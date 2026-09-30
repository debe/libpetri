"""Cross-language verifier conformance: loader, reference replay and checker.

The corpus contract is ``spec/verification-fixtures/conformance/README.md``: nets as
JSON (``nets/<id>.json``), verdicts written by the Lean reference
(``expected/<id>.json``). This module turns a net file into a real ``libpetri`` net,
initial marking and properties, runs the verifier under the four route setups of
``rust/libpetri-verification/tests/route_agreement.rs`` and holds every verdict
against the README conformance rule. The replay of a counterexample uses the
reference firing rule stated here from the spec, sharing no code with the library.

The four setups run twice, as in ``rust/libpetri-verification/tests/conformance.rs``.
The atomic pass (``assume_atomic_firing=True``) reads every firing as one step, as the
reference does, and is held to all four rules. The default pass leaves the in-flight
split of VER-004 on, as a caller gets it, and is held to rules 1, 3 and 4 only: the
split adds the executor's runs with an action in flight, which the atomic reference
does not have, so a violation where the reference proves is counted there, not a
finding. A default-pass trace of a split net names ``complete:<t>`` steps the
reference cannot fire, so it is counted, with whether the verifier's own abstract
replay confirmed it, instead of replayed.

Not a test module (no ``test_`` prefix): ``test_conformance.py`` imports it.
"""

from __future__ import annotations

import json
import math
import os
import re
from collections import Counter
from dataclasses import dataclass, field
from itertools import product
from pathlib import Path
from typing import Any

import libpetri as lp

LANG = "python"

# ======================================================================
# Corpus location
# ======================================================================


def locate_corpus() -> Path | None:
    """``LIBPETRI_CONFORMANCE_DIR`` when set, else the first
    ``spec/verification-fixtures/conformance`` upward from this file."""
    env = os.environ.get("LIBPETRI_CONFORMANCE_DIR")
    if env:
        return Path(env)
    here = Path(__file__).resolve().parent
    for d in [here, *here.parents]:
        candidate = d / "spec" / "verification-fixtures" / "conformance"
        if candidate.is_dir():
            return candidate
    return None


@dataclass
class Corpus:
    root: Path
    cases: list[tuple[Path, Path]]  # (net file, expected file)
    missing_expected: list[str]


def load_corpus(root: Path | None) -> tuple[Corpus | None, str]:
    """The (net, expected) pairs under ``root``, or ``None`` with the reason to skip."""
    if root is None:
        return None, "conformance corpus directory not found"
    nets_dir = root / "nets"
    nets = sorted(nets_dir.glob("*.json")) if nets_dir.is_dir() else []
    if not nets:
        return None, f"conformance corpus absent: no nets under {nets_dir}"
    cases, missing = [], []
    for net_file in nets:
        exp = root / "expected" / net_file.name
        if exp.is_file():
            cases.append((net_file, exp))
        else:
            missing.append(net_file.stem)
    if not cases:
        return None, (
            f"conformance expected verdicts absent: none of the {len(nets)} nets under "
            f"{nets_dir} has an expected/<id>.json (run the Lean reference first)"
        )
    return Corpus(root, cases, missing), ""


# ======================================================================
# Net model (the schema, parsed) and loader into libpetri
# ======================================================================


@dataclass
class ConfNet:
    id: str
    declared: list[str]
    marking: dict[str, int]
    transitions: list[dict[str, Any]]
    properties: list[dict[str, Any]]
    raw: dict[str, Any] = field(repr=False, default_factory=dict)

    @property
    def transition_names(self) -> set[str]:
        return {t["name"] for t in self.transitions}


def parse_net(doc: dict[str, Any]) -> ConfNet:
    transitions = []
    for t in doc.get("transitions", []):
        for inp in t.get("inputs", []):
            kind = inp["kind"]
            if kind not in ("one", "exactly", "all", "atLeast"):
                raise ValueError(f"{doc['id']}/{t['name']}: unknown input kind {kind!r}")
            if kind in ("exactly", "atLeast") and int(inp.get("n", 0)) < 1:
                raise ValueError(f"{doc['id']}/{t['name']}: {kind} needs n >= 1")
        transitions.append(t)
    for p in doc.get("properties", []):
        if p["type"] not in PROPERTY_TYPES:
            raise ValueError(f"{doc['id']}: unknown property type {p['type']!r}")
    return ConfNet(
        id=doc["id"],
        declared=list(doc.get("places", [])),
        marking={k: int(v) for k, v in (doc.get("marking") or {}).items()},
        transitions=transitions,
        properties=list(doc.get("properties", [])),
        raw=doc,
    )


def read_net(path: Path) -> ConfNet:
    return parse_net(json.loads(path.read_text()))


def _input_spec(inp: dict[str, Any], place: Any) -> Any:
    kind = inp["kind"]
    if kind == "one":
        return lp.one(place)
    if kind == "exactly":
        return lp.exactly(int(inp["n"]), place)
    if kind == "all":
        return lp.all_tokens(place)
    if kind == "atLeast":
        return lp.at_least(int(inp["n"]), place)
    raise ValueError(f"unknown input kind {kind!r}")


def _output_spec(o: dict[str, Any], place: Any) -> Any:
    kind = o["type"]
    if kind == "place":
        return lp.out(place(o["place"]))
    if kind == "and":
        return lp.and_(*[_output_spec(c, place) for c in o["children"]])
    if kind == "xor":
        return lp.xor(*[_output_spec(c, place) for c in o["children"]])
    if kind == "timeout":
        return lp.timeout(int(o["afterMs"]), _output_spec(o["child"], place))
    if kind == "forward":
        return lp.forward_input(place(o["from"]), place(o["to"]))
    raise ValueError(f"unknown output type {kind!r}")


REAPABLE_KINDS = ("deadline", "window")


def _timing(tm: dict[str, Any]) -> Any:
    """The schema's `timing` object ([TIME-002]..[TIME-006])."""
    kind = tm["kind"]
    if kind in ("immediate", "unconstrained"):
        return lp.immediate()
    if kind == "deadline":
        return lp.deadline(int(tm["latestMs"]))
    if kind == "delayed":
        return lp.delayed(int(tm["earliestMs"]))
    if kind == "window":
        return lp.window(int(tm["earliestMs"]), int(tm["latestMs"]))
    if kind == "exact":
        return lp.exact(int(tm["earliestMs"]))
    raise ValueError(f"unknown timing kind {kind!r}")


def reapable(t: dict[str, Any]) -> bool:
    """[TIME-013]: `deadline` or `window` timing."""
    tm = t.get("timing")
    return tm is not None and tm["kind"] in REAPABLE_KINDS


def build_net(net: ConfNet) -> Any:
    """The net through libpetri's real builders, with the structure-only ``fork``
    action on every transition (the verifier never runs it)."""
    places: dict[str, Any] = {}

    def place(name: str) -> Any:
        if name not in places:
            places[name] = lp.Place(name)
        return places[name]

    builder = lp.Net(net.id)
    for t in net.transitions:
        tb = lp.Transition(t["name"])
        for inp in t.get("inputs", []):
            tb = tb.input(_input_spec(inp, place(inp["place"])))
        for p in t.get("inhibitors") or []:
            tb = tb.inhibitor(lp.inhibitor(place(p)))
        for p in t.get("reads") or []:
            tb = tb.read(lp.read(place(p)))
        for p in t.get("resets") or []:
            tb = tb.reset(lp.reset(place(p)))
        if t.get("output") is not None:
            tb = tb.output(_output_spec(t["output"], place))
        if t.get("priority") is not None:
            tb = tb.priority(int(t["priority"]))
        if t.get("timing") is not None:
            tb = tb.timing(_timing(t["timing"]))
        builder = builder.transition(tb.action(lp.fork).build())
    # Declared places, touched by an arc or not. Marking-only names stay undeclared:
    # they are inert places of the verified net (CORE-072).
    for name in net.declared:
        builder = builder.place(place(name))
    return builder.build()


PROPERTY_TYPES = (
    "deadlock-free",
    "terminates-at-sink",
    "place-bound",
    "mutual-exclusion",
    "unreachable",
    "quiescent-count",
)


def build_property(prop: dict[str, Any]) -> tuple[Any, list[str]]:
    """(libpetri property, sink places)."""
    kind = prop["type"]
    if kind == "deadlock-free":
        return lp.deadlock_free(), list(prop.get("sinks", []))
    if kind == "terminates-at-sink":
        return lp.terminates_at_sink(), list(prop.get("sinks", []))
    if kind == "place-bound":
        return lp.place_bound(prop["place"], int(prop["bound"])), []
    if kind == "mutual-exclusion":
        # Pairwise over any list (VER-002); the Rust API behind Python takes a list.
        return lp.mutual_exclusion(list(prop["places"])), []
    if kind == "unreachable":
        return lp.unreachable(list(prop["places"])), []
    if kind == "quiescent-count":
        mx = prop.get("max")
        return lp.quiescent_count(
            list(prop["places"]), int(prop["min"]), math.inf if mx is None else int(mx)
        ), []
    raise ValueError(f"unknown property type {kind!r}")


# ======================================================================
# Reference firing rule (README / VER-002 / IO-001..016), independent of libpetri
# ======================================================================

Marking = tuple[tuple[str, int], ...]  # sorted, zero counts dropped


def _freeze(m: dict[str, int]) -> Marking:
    return tuple(sorted((k, v) for k, v in m.items() if v > 0))


def _required(inp: dict[str, Any]) -> int:
    kind = inp["kind"]
    return int(inp["n"]) if kind in ("exactly", "atLeast") else 1


def enabled(t: dict[str, Any], m: dict[str, int]) -> bool:
    return (
        all(m.get(i["place"], 0) >= _required(i) for i in t.get("inputs", []))
        and all(m.get(p, 0) >= 1 for p in t.get("reads") or [])
        and all(m.get(p, 0) == 0 for p in t.get("inhibitors") or [])
    )


def _alternatives(o: dict[str, Any] | None) -> list[list[tuple[str, str, str | None]]]:
    """Each alternative is a list of leaves: ("place", p, None) or ("forward", to, from)."""
    if o is None:
        return [[]]
    kind = o["type"]
    if kind == "place":
        return [[("place", o["place"], None)]]
    if kind == "forward":
        return [[("forward", o["to"], o["from"])]]
    if kind == "timeout":
        return _alternatives(o["child"])
    if kind == "xor":
        return [alt for c in o["children"] for alt in _alternatives(c)]
    if kind == "and":
        acc: list[list[tuple[str, str, str | None]]] = [[]]
        for c in o["children"]:
            acc = [a + b for a, b in product(acc, _alternatives(c))]
        return acc
    raise ValueError(f"unknown output type {kind!r}")


def _timeouts(o: dict[str, Any] | None) -> list[dict[str, Any]]:
    """Every ``timeout`` node of the tree, outermost first."""
    if o is None:
        return []
    kind = o["type"]
    if kind == "timeout":
        return [o, *_timeouts(o["child"])]
    if kind in ("and", "xor"):
        return [n for c in o["children"] for n in _timeouts(c)]
    return []


def fire(t: dict[str, Any], m: dict[str, int]) -> list[dict[str, int]]:
    """The markings one firing can produce (IO-013 AC5, IO-014 AC6, IO-015, IO-016):
    (a) the action completes and writes one claim of the output tree, one token per
    claimed place (a forward claims ``to`` with ONE token); plus (b) for each timeout
    node, its budget expires and the marking receives that timeout child's claims only,
    where a forward deposits one token per token consumed from ``from``."""
    base = dict(m)
    consumed: dict[str, int] = {}
    for inp in t.get("inputs", []):
        p = inp["place"]
        n = m.get(p, 0) if inp["kind"] in ("all", "atLeast") else _required(inp)
        base[p] = base.get(p, 0) - n
        consumed[p] = n
    for p in t.get("resets") or []:
        base[p] = 0
    out = []

    def deposit(alt: list[tuple[str, str, str | None]], faithful: bool) -> None:
        nxt = dict(base)
        for kind, to, frm in alt:
            k = consumed.get(frm, 0) if frm is not None and faithful else 1
            nxt[to] = nxt.get(to, 0) + k
        out.append(nxt)

    for alt in _alternatives(t.get("output")):
        deposit(alt, faithful=False)
    for node in _timeouts(t.get("output")):
        for alt in _alternatives(node["child"]):
            deposit(alt, faithful=True)
    return out


def quiescent(net: ConfNet, m: dict[str, int]) -> bool:
    """Reap-quiescent ([VER-002], [TIME-013]): every enabled transition is reapable."""
    return not any(enabled(t, m) and not reapable(t) for t in net.transitions)


def bad(net: ConfNet, prop: dict[str, Any], m: dict[str, int]) -> bool:
    c = lambda p: m.get(p, 0)  # noqa: E731
    kind = prop["type"]
    if kind == "place-bound":
        return c(prop["place"]) > int(prop["bound"])
    if kind == "mutual-exclusion":
        # Pairwise (VER-002): two entries of the list marked at once.
        return sum(1 for p in prop["places"] if c(p) >= 1) >= 2
    if kind == "unreachable":
        return all(c(p) >= 1 for p in prop["places"])
    if kind == "deadlock-free":
        sinks = set(prop.get("sinks", []))
        return quiescent(net, m) and any(v > 0 and p not in sinks for p, v in m.items())
    if kind == "terminates-at-sink":
        return quiescent(net, m) and not any(c(s) > 0 for s in prop.get("sinks", []))
    if kind == "quiescent-count":
        if not quiescent(net, m):
            return False
        total = sum(c(p) for p in dict.fromkeys(prop["places"]))
        mx = prop.get("max")
        return total < int(prop["min"]) or (mx is not None and total > int(mx))
    raise ValueError(f"unknown property type {kind!r}")


_BRANCH = re.compile(r"^(.*)_b\d+$")


def strip_branch(net: ConfNet, name: str) -> str:
    """``t_b3`` -> ``t`` when ``t`` is a transition of the net and ``t_b3`` is not."""
    names = net.transition_names
    if name in names:
        return name
    mt = _BRANCH.match(name)
    if mt and mt.group(1) in names:
        return mt.group(1)
    return name


def replay(net: ConfNet, prop: dict[str, Any], trace: list[str]) -> str | None:
    """``None`` when the trace replays to a bad state under the reference rule, else why not."""
    by_name = {t["name"]: t for t in net.transitions}
    states: dict[Marking, dict[str, int]] = {_freeze(net.marking): dict(net.marking)}
    for step, raw in enumerate(trace):
        name = strip_branch(net, raw)
        t = by_name.get(name)
        if t is None:
            return f"step {step}: unknown transition {raw!r}"
        nxt: dict[Marking, dict[str, int]] = {}
        for s in states.values():
            if enabled(t, s):
                for n in fire(t, s):
                    nxt.setdefault(_freeze(n), n)
        if not nxt:
            return f"step {step}: {raw!r} not enabled in any of {sorted(states)}"
        states = nxt
    if any(bad(net, prop, s) for s in states.values()):
        return None
    return f"final state(s) {sorted(states)} do not violate {prop['id']} ({prop['type']})"


# ======================================================================
# The conformance rule, as a pure function
# ======================================================================


@dataclass
class Finding:
    kind: str
    net: str
    property: str
    route: str
    detail: str

    def __str__(self) -> str:
        return f"{self.kind} [{self.net} / {self.property} / {self.route}]: {self.detail}"


def check(
    net: ConfNet,
    prop: dict[str, Any],
    route: str,
    verdict: str,
    trace: list[str] | None,
    ref: dict[str, Any] | None,
    *,
    split_pass: bool = False,
    split_net: bool = False,
) -> list[Finding]:
    """The README conformance rule for one (net, property, route). ``ref`` is the
    property's entry in the expected file; ``None`` counts as reference unknown.

    ``trace`` is ``None`` for an UNTRACED violation (README clarification 6): no firing
    sequence and not the initial marking alone. It has nothing to replay, so it fails
    rule 3 (UNTRACED VIOLATED), and against a reference proof it is WRONG VIOLATED
    (rule 2), as in ``rust/libpetri-verification/tests/conformance.rs``.

    ``split_pass`` holds a default-pass verdict (the in-flight split on) to rules 1, 3
    and 4 only; ``split_net`` says the report split a transition (``In-flight actions
    (VER-004):``), whose trace the atomic reference rule cannot replay."""
    ref_verdict = (ref or {}).get("verdict", "unknown")
    findings: list[Finding] = []

    def f(kind: str, detail: str) -> None:
        findings.append(Finding(kind, net.id, prop["id"], route, detail))

    if split_pass:
        if verdict == "proven" and ref_verdict == "violated":
            f("WRONG PROVEN", f"reference violates via {(ref or {}).get('trace')}")
        elif verdict == "violated" and trace is None:
            f(
                "UNTRACED VIOLATED",
                "no firing sequence to replay; an initial-marking violation must report "
                "the empty trace",
            )
        elif verdict == "violated" and not split_net:
            why = replay(net, prop, trace)
            if why is not None:
                f("REPLAY FAILS", f"trace {trace}: {why}")
        elif verdict not in ("proven", "violated", "unknown"):
            f("BAD VERDICT", f"unrecognised verdict {verdict!r}")
        return findings

    if verdict == "proven" and ref_verdict == "violated":
        f("WRONG PROVEN", f"reference violates via {(ref or {}).get('trace')}")
    elif verdict == "violated" and trace is None:
        if ref_verdict == "proven":
            f("WRONG VIOLATED", "reference proves it; the violation carries no trace")
        else:
            f(
                "UNTRACED VIOLATED",
                "no firing sequence to replay; an initial-marking violation must report "
                "the empty trace",
            )
    elif verdict == "violated" and trace is not None:
        why = replay(net, prop, trace)
        if ref_verdict == "proven":
            if why is None:
                f(
                    "FALSIFIES THE REFERENCE",
                    f"trace {trace} replays under the reference rule, yet the reference proves it",
                )
            else:
                f("WRONG VIOLATED", f"reference proves it; trace {trace}: {why}")
        elif why is not None:
            f("REPLAY FAILS", f"trace {trace}: {why}")
    elif verdict not in ("proven", "unknown"):
        f("BAD VERDICT", f"unrecognised verdict {verdict!r}")
    return findings


def stale_findings(
    net: ConfNet, prop: dict[str, Any], refs: dict[str, dict[str, Any]]
) -> list[Finding]:
    """A property with no entry in its expected file: once per property, not per route
    (the expected set predates the net; rust ``conformance.rs`` does the same)."""
    if prop["id"] in refs:
        return []
    return [
        Finding(
            "STALE", net.id, prop["id"], "-",
            f"{net.id}/{prop['id']}: no reference verdict (expected/ is stale)",
        )
    ]


def missing_expected_findings(corpus: Corpus) -> list[Finding]:
    """A corpus net with no ``expected/<id>.json`` once ``expected/`` has any file."""
    return [
        Finding("STALE", nid, "-", "-", f"{nid}: no expected/{nid}.json (expected/ is stale)")
        for nid in corpus.missing_expected
    ]


# ======================================================================
# Route setups (route_agreement.rs CONFIGS) and the runner
# ======================================================================


@dataclass(frozen=True)
class RouteSetup:
    name: str
    enum_budget: int
    linear_bound: bool
    phases: bool
    needs_z3: bool
    # The atomic pass (all four rules) or the default, split pass (rules 1, 3, 4).
    atomic: bool = True


ROUTES = (
    RouteSetup("enum", 5_000, True, True, False),
    RouteSetup("smt+lb", 0, True, True, True),
    RouteSetup("smt-lb", 0, False, True, True),
    RouteSetup("ic3", 0, False, False, True),
)

# The same four with the in-flight split of VER-004 on, as a caller gets it.
SPLIT_ROUTES = tuple(
    RouteSetup(f"{r.name}/split", r.enum_budget, r.linear_bound, r.phases, r.needs_z3, atomic=False)
    for r in ROUTES
)

ALL_ROUTES = ROUTES + SPLIT_ROUTES

SPLIT_MARK = "In-flight actions (VER-004):"


def run_route(built: Any, net: ConfNet, prop: dict[str, Any], setup: RouteSetup) -> Any:
    property_, sinks = build_property(prop)
    return lp.verify(
        built,
        property_,
        initial_marking=dict(net.marking),
        sink_places=sinks or None,
        enumeration_max_classes=setup.enum_budget,
        linear_bound=setup.linear_bound,
        state_equation_phase=setup.phases,
        firing_bound=setup.phases,
        certificate_check=True,
        counterexample_replay=True,
        timeout_ms=4_000,
        total_budget_ms=12_000,
        # The Lean reference fires atomically and does not model the in-flight split of
        # VER-004: the atomic pass compares on that reading, the default pass on the split.
        assume_atomic_firing=setup.atomic,
    )


@dataclass
class Stats:
    verdicts: dict[str, Counter] = field(default_factory=dict)
    unknown_reasons: dict[str, Counter] = field(default_factory=dict)
    skipped_routes: list[str] = field(default_factory=list)
    untraced: dict[str, list[str]] = field(default_factory=dict)
    # Default pass: a violation where the reference proves (a run with an action in
    # flight, allowed there), per route; traces of split nets, and of those the ones the
    # verifier's abstract replay did not confirm.
    split_only: Counter = field(default_factory=Counter)
    split_traces: int = 0
    split_unconfirmed: int = 0

    def count(self, route: str, verdict: str, reason: str | None) -> None:
        self.verdicts.setdefault(route, Counter())[verdict] += 1
        if verdict == "unknown":
            key = (reason or "?").splitlines()[0][:120]
            self.unknown_reasons.setdefault(route, Counter())[key] += 1

    def merge(self, other: Stats) -> None:
        for r, c in other.verdicts.items():
            self.verdicts.setdefault(r, Counter()).update(c)
        for r, c in other.unknown_reasons.items():
            self.unknown_reasons.setdefault(r, Counter()).update(c)
        for r, lst in other.untraced.items():
            self.untraced.setdefault(r, []).extend(lst)
        for r in other.skipped_routes:
            if r not in self.skipped_routes:
                self.skipped_routes.append(r)
        self.split_only.update(other.split_only)
        self.split_traces += other.split_traces
        self.split_unconfirmed += other.split_unconfirmed

    def render(self) -> str:
        lines = [f"conformance ({LANG}) per route: proven / violated / unknown"]
        for setup in ALL_ROUTES:
            c = self.verdicts.get(setup.name)
            if c is None:
                lines.append(f"  {setup.name:13} skipped")
                continue
            split_only = (
                "" if setup.atomic
                else f"  violated-where-reference-proved {self.split_only[setup.name]}"
            )
            lines.append(
                f"  {setup.name:13} {c['proven']:5} / {c['violated']:5} / {c['unknown']:5}"
                f"  (violated without a trace: {len(self.untraced.get(setup.name, []))})"
                + split_only
            )
            for d in self.untraced.get(setup.name, [])[:5]:
                lines.append(f"      untraced: {d}")
            for reason, n in self.unknown_reasons.get(setup.name, Counter()).most_common(5):
                lines.append(f"      unknown x{n}: {reason}")
        lines.append(
            f"  default-pass traces of split nets {self.split_traces} (unconfirmed by the "
            f"abstract replay {self.split_unconfirmed}), not replayed by the reference"
        )
        return "\n".join(lines)


def run_net(
    net_file: Path, expected_file: Path, z3: bool, dump_dir: Path | None = None
) -> tuple[list[Finding], Stats]:
    """Every property of one net under every route setup, atomic and split (the SMT
    setups only with z3)."""
    net = read_net(net_file)
    expected = json.loads(expected_file.read_text())
    if expected.get("id") != net.id:
        raise ValueError(f"{expected_file}: id {expected.get('id')!r} != net id {net.id!r}")
    refs = {r["property"]: r for r in expected.get("results", [])}
    built = build_net(net)
    stats = Stats()
    findings: list[Finding] = []
    dumped: list[dict[str, Any]] = []
    seen: set[tuple[str, tuple[str, ...]]] = set()
    for prop in net.properties:
        findings += stale_findings(net, prop, refs)
        for setup in ALL_ROUTES:
            if setup.needs_z3 and not z3:
                if setup.name not in stats.skipped_routes:
                    stats.skipped_routes.append(setup.name)
                continue
            r = run_route(built, net, prop, setup)
            stats.count(setup.name, r.verdict, r.reason)
            names = list(r.counterexample_transitions)
            # Traced iff it names a step, or its one marking is the initial marking itself.
            traced = bool(names) or len(r.counterexample_trace) == 1
            trace = names if traced else None
            split_net = not setup.atomic and SPLIT_MARK in r.report
            if r.verdict == "violated" and not traced:
                stats.untraced.setdefault(setup.name, []).append(
                    f"{net.id}/{prop['id']}: violated with {len(r.counterexample_trace)} "
                    "marking(s) and no firing sequence"
                )
            ref = refs.get(prop["id"])
            findings += check(
                net, prop, setup.name, r.verdict, trace, ref,
                split_pass=not setup.atomic, split_net=split_net,
            )
            if r.verdict == "violated" and not setup.atomic:
                if (ref or {}).get("verdict") == "proven":
                    stats.split_only[setup.name] += 1
                if traced and split_net:
                    stats.split_traces += 1
                    if r.counterexample_confirmed is False:
                        stats.split_unconfirmed += 1
                    continue
            if r.verdict == "violated" and traced:
                stripped = tuple(strip_branch(net, n) for n in names)
                if (prop["id"], stripped) not in seen:
                    seen.add((prop["id"], stripped))
                    dumped.append({"property": prop["id"], "trace": list(stripped)})
    if dump_dir is not None and dumped:
        dump_dir.mkdir(parents=True, exist_ok=True)
        (dump_dir / f"{net.id}.traces.json").write_text(json.dumps(dumped, indent=2) + "\n")
    return findings, stats


def require_corpus() -> bool:
    """``LIBPETRI_CONFORMANCE_REQUIRE=1`` (set by ``scripts/conformance-replay.py``):
    an absent corpus or expected set fails instead of skipping."""
    return os.environ.get("LIBPETRI_CONFORMANCE_REQUIRE", "") not in ("", "0")


def dump_dir_from_env() -> Path | None:
    d = os.environ.get("LIBPETRI_CONFORMANCE_DUMP")
    return Path(d) if d else None
