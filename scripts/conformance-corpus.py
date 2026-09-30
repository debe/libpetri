#!/usr/bin/env python3
"""Conformance corpus generator (spec/verification-fixtures/conformance/README.md).

Writes the nets every language's verifier is checked against, deterministically
from a seed, and — with ``--update`` — their expected verdicts from the verified
Lean reference (``lake exe reference``). Expected files are never written any
other way.

    scripts/conformance-corpus.py              regenerate nets/ and corpus.json
    scripts/conformance-corpus.py --update     ... then run the Lean reference into expected/
    scripts/conformance-corpus.py --check      fail if nets/, corpus.json or expected/ are stale
                                               (expected/ is re-derived by the Lean binary)
    scripts/conformance-corpus.py --stats      print the corpus composition and exit

Options: ``--seed 0x5EED`` (base seed), ``--count N`` (generated nets, default 287),
``--cap N`` (passed to ``lake exe reference``), ``--reference CMD`` (the reference
command, default ``lake exe reference`` run inside lean/).

Corpus: ``gen-NNNNNN`` nets drawn with the shape distribution of
rust/libpetri-verification/tests/route_agreement.rs's generator (the same
splitmix64 stream, so ``gen-000007`` is route_agreement's net for seed
0x5EED + 7), each with 3-6 properties over all six property types; the in-scope
nets of spec/verification-fixtures/fixtures.json hand-ported from their
normative netDescription (``fixture-*``); and the two historical wrong-Proven
repros (``bug-*``) and the reaping witnesses (``reap-*``).

About 20% of the generated nets carry transition timing (``TIMED_PERCENT``),
drawn from a separate stream so every untimed net is byte-identical to the
corpus before timing existed. At least one transition of a timed net is
reapable ([TIME-013]: ``deadline`` or ``window``), so its quiescence properties
read reap-quiescence ([VER-002]).

The explorer below exists only to pick place bounds and quiescent counts near the
reachable values, so both verdicts occur. It is NOT the reference: verdicts come
from the Lean binary alone.
"""

from __future__ import annotations

import argparse
import json
import shlex
import shutil
import subprocess
import sys
import tempfile
from collections import deque
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
CORPUS = REPO / "spec" / "verification-fixtures" / "conformance"
NETS = CORPUS / "nets"
EXPECTED = CORPUS / "expected"
INDEX = CORPUS / "corpus.json"
LEAN = REPO / "lean"

DEFAULT_SEED = 0x5EED
DEFAULT_COUNT = 287
TIMEOUT_MS = 50
# Share of generated nets with transition timing, and the timing stream's salt.
TIMED_PERCENT = 20
TIMING_SALT = 0x71A1_4EA9
REAPABLE_KINDS = ("deadline", "window")
PROPERTY_TYPES = [
    "deadlock-free",
    "terminates-at-sink",
    "place-bound",
    "mutual-exclusion",
    "unreachable",
    "quiescent-count",
]

# Caps of the bound-picking explorer (the same as route_agreement's reference).
MAX_STATES = 20_000
MAX_TOKENS = 24

M64 = (1 << 64) - 1


# ======================================================================
# splitmix64, bit-identical to route_agreement.rs's Rng
# ======================================================================


class Rng:
    def __init__(self, seed: int) -> None:
        self.s = (seed ^ 0x9E3779B97F4A7C15) & M64

    def next(self) -> int:
        self.s = (self.s + 0x9E3779B97F4A7C15) & M64
        z = self.s
        z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & M64
        z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & M64
        return z ^ (z >> 31)

    def below(self, n: int) -> int:
        return self.next() % n

    def range(self, lo: int, hi_incl: int) -> int:
        return lo + self.below(hi_incl - lo + 1)

    def chance(self, percent: int) -> bool:
        return self.below(100) < percent

    def pick(self, items):
        return items[self.below(len(items))]

    def distinct(self, n: int, k: int) -> list[int]:
        pool = list(range(n))
        for i in range(k):
            j = i + self.below(n - i)
            pool[i], pool[j] = pool[j], pool[i]
        return pool[:k]


# ======================================================================
# Net model: cards are ("one",) ("exactly", n) ("all",) ("atLeast", n);
# outputs are ("place", p) ("and", [..]) ("xor", [..]) ("timeout", child)
# ("forward", from, to), with places as indices into `names`.
# ======================================================================


def required(card) -> int:
    return {"one": 1, "all": 1}.get(card[0]) or card[1]


def gen_card(rng: Rng):
    r = rng.below(100)
    if r <= 44:
        return ("one",)
    if r <= 69:
        return ("exactly", rng.range(2, 3))
    if r <= 84:
        return ("all",)
    return ("atLeast", rng.range(1, 2))


def gen_normal(rng: Rng, n: int):
    if n >= 2 and rng.chance(35):
        v = rng.distinct(n, 2)
        return ("and", [("place", v[0]), ("place", v[1])])
    return ("place", rng.below(n))


def gen_timeout_child(rng: Rng, n: int, inputs):
    fixed = [p for p, c in inputs if c[0] in ("one", "exactly")]
    if fixed and rng.chance(80):
        frm = rng.pick(fixed)
    else:
        frm = inputs[rng.below(len(inputs))][0]
    to = rng.below(n)
    fw = ("forward", frm, to)
    if n >= 2 and rng.chance(25):
        z = rng.below(n)
        if z == to:
            z = (z + 1) % n
        return ("and", [fw, ("place", z)])
    return fw


def gen_out(rng: Rng, n: int, inputs):
    r = rng.below(100)
    if r <= 7:
        return None
    if r <= 35:
        return ("place", rng.below(n))
    if r <= 50:
        if n < 2:
            return ("place", 0)
        v = rng.distinct(n, 2)
        return ("and", [("place", v[0]), ("place", v[1])])
    if r <= 64:
        a = gen_normal(rng, n)
        b = ("place", rng.below(n))
        return ("xor", [a, b])
    if r <= 89 and inputs:
        normal = gen_normal(rng, n)
        return ("xor", [normal, ("timeout", gen_timeout_child(rng, n, inputs))])
    if inputs:
        return ("timeout", gen_timeout_child(rng, n, inputs))
    return ("place", rng.below(n))


def duplicate_in_branch(o) -> bool:
    """[IO-011]: some branch names a place twice (And children cross-multiply)."""

    def leaves(o) -> tuple[set, bool]:
        kind = o[0]
        if kind == "place":
            return {o[1]}, False
        if kind == "forward":
            return {o[2]}, False
        if kind == "timeout":
            return leaves(o[1])
        acc: set = set()
        for c in o[1]:
            ls, dup = leaves(c)
            if dup or (kind == "and" and acc & ls):
                return acc | ls, True
            acc |= ls
        return acc, False

    return leaves(o)[1]


def gen_net(seed: int) -> dict:
    """route_agreement.rs `gen_net`, call for call."""
    rng = Rng(seed)
    n = rng.range(2, 6)
    names = [f"p{i}" for i in range(n)]
    declared_extra = None
    if rng.chance(20):
        names.append("q0")
        declared_extra = len(names) - 1
    undeclared = None
    if rng.chance(30):
        names.append("s0")
        undeclared = len(names) - 1
    t_count = rng.range(1, 6)
    transitions = []
    for ti in range(t_count):
        r = rng.below(100)
        k_in = 0 if r <= 4 else (1 if r <= 69 else min(2, n))
        inputs = [(p, gen_card(rng)) for p in rng.distinct(n, k_in)]
        in_set = {p for p, _ in inputs}
        reads = []
        if rng.chance(15):
            cands = [p for p in range(n) if p not in in_set]
            if cands:
                reads.append(rng.pick(cands))
        inhibitors = []
        if rng.chance(70 if k_in == 0 else 20):
            inhibitors.append(rng.below(n))
        resets = []
        if rng.chance(12):
            resets.append(rng.below(n))
        out = gen_out(rng, n, inputs)
        if out is not None and duplicate_in_branch(out):
            out = ("place", rng.below(n))
        transitions.append(
            dict(name=f"t{ti}", inputs=inputs, reads=reads, inhibitors=inhibitors, resets=resets, out=out)
        )
    initial = [0] * len(names)
    for i in range(n):
        r = rng.below(100)
        initial[i] = 0 if r <= 49 else 1 if r <= 79 else 2 if r <= 94 else 3
    for t in transitions:
        for p, c in t["inputs"]:
            if c[0] in ("exactly", "atLeast") and rng.chance(50):
                initial[p] = max(initial[p], required(c))
    if declared_extra is not None and rng.chance(50):
        initial[declared_extra] = rng.range(1, 2)
    if undeclared is not None:
        initial[undeclared] = rng.range(1, 2)
    declared = names[:n] + ([names[declared_extra]] if declared_extra is not None else [])
    return dict(names=names, declared=declared, transitions=transitions, initial=initial)


def gen_timing(seed: int, net: dict) -> None:
    """Draw transition timing into `net` for ~TIMED_PERCENT of seeds, from its own stream.

    Untimed nets are left without a `timing` key. A timed net has a timing on every transition
    and at least one reapable one ([TIME-013]).
    """
    rng = Rng((seed * 0xD1342543DE82EF95 + TIMING_SALT) & M64)
    if not rng.chance(TIMED_PERCENT):
        return
    ts = net["transitions"]
    for t in ts:
        r = rng.below(100)
        if r <= 29:
            t["timing"] = {"kind": "deadline", "latestMs": rng.pick([5, 10, 50])}
        elif r <= 54:
            e = rng.pick([0, 1, 3])
            t["timing"] = {"kind": "window", "earliestMs": e, "latestMs": e + rng.pick([2, 5, 20])}
        elif r <= 69:
            t["timing"] = {"kind": "delayed", "earliestMs": rng.pick([1, 5])}
        elif r <= 79:
            t["timing"] = {"kind": "exact", "earliestMs": rng.pick([2, 5])}
        else:
            t["timing"] = {"kind": "immediate"}
    if not any(t["timing"]["kind"] in REAPABLE_KINDS for t in ts):
        ts[rng.below(len(ts))]["timing"] = {"kind": "deadline", "latestMs": 10}


def reapable(t: dict) -> bool:
    tm = t.get("timing")
    return tm is not None and tm["kind"] in REAPABLE_KINDS


# ======================================================================
# Bound-picking explorer (untimed, priority-blind, IO-014 forwards).
# Not the reference; it only steers the generator.
# ======================================================================


def alternatives(o) -> list[list]:
    """What a completing action can write ([IO-015]): a forward claims its `to`."""
    kind = o[0]
    if kind == "place":
        return [[("place", o[1])]]
    if kind == "forward":
        return [[("place", o[2])]]
    if kind == "timeout":
        return alternatives(o[1])
    if kind == "xor":
        return [a for c in o[1] for a in alternatives(c)]
    acc: list[list] = [[]]
    for c in o[1]:
        acc = [a + b for a in acc for b in alternatives(c)]
    return acc


def timeout_leaves(o):
    """The leaves an expired timeout deposits ([IO-013] AC5), forwards kept as forwards."""

    def leaves(o, acc):
        if o[0] in ("place", "forward"):
            acc.append(o)
        elif o[0] == "and":
            for c in o[1]:
                leaves(c, acc)
        else:
            raise ValueError("xor/timeout under a timeout")

    if o[0] == "timeout":
        acc: list = []
        leaves(o[1], acc)
        return acc
    if o[0] in ("and", "xor"):
        for c in o[1]:
            found = timeout_leaves(c)
            if found is not None:
                return found
    return None


class Explorer:
    def __init__(self, net: dict) -> None:
        self.net = net
        self.ts = []
        for t in net["transitions"]:
            out = t["out"]
            outcomes = alternatives(out) if out is not None else [[]]
            to = timeout_leaves(out) if out is not None else None
            if to is not None:
                outcomes = outcomes + [to]
            self.ts.append((t, outcomes))

    @staticmethod
    def enabled(t, m) -> bool:
        return (
            all(m[p] >= required(c) for p, c in t["inputs"])
            and all(m[p] >= 1 for p in t["reads"])
            and all(m[p] == 0 for p in t["inhibitors"])
        )

    def successors(self, m):
        for t, outcomes in self.ts:
            if not self.enabled(t, m):
                continue
            base = list(m)
            consumed = {}
            for p, c in t["inputs"]:
                k = m[p] if c[0] in ("all", "atLeast") else required(c)
                base[p] -= k
                consumed[p] = k
            for p in t["resets"]:
                base[p] = 0
            for alt in outcomes:
                nxt = list(base)
                for leaf in alt:
                    if leaf[0] == "place":
                        nxt[leaf[1]] += 1
                    else:
                        nxt[leaf[2]] += consumed.get(leaf[1], 0)
                yield t["name"], tuple(nxt)

    def quiescent(self, m) -> bool:
        """Reap-quiescent ([VER-002], [TIME-013]): every enabled transition is reapable."""
        return not any(self.enabled(t, m) and not reapable(t) for t, _ in self.ts)

    def explore(self):
        m0 = tuple(self.net["initial"])
        seen = {m0}
        states = [m0]
        queue = deque([m0])
        complete = True
        while queue:
            m = queue.popleft()
            for _, nxt in self.successors(m):
                if nxt in seen:
                    continue
                if max(nxt) > MAX_TOKENS or len(states) >= MAX_STATES:
                    complete = False
                    continue
                seen.add(nxt)
                states.append(nxt)
                queue.append(nxt)
        return states, complete


def bad(prop: dict, idx: dict, ex: Explorer, m) -> bool:
    def count(p):
        return m[idx[p]] if p in idx else 0

    ty = prop["type"]
    if ty == "place-bound":
        return count(prop["place"]) > prop["bound"]
    if ty == "mutual-exclusion":
        return sum(1 for p in prop["places"] if count(p) >= 1) >= 2
    if ty == "unreachable":
        return all(count(p) >= 1 for p in prop["places"])
    if not ex.quiescent(m):
        return False
    if ty == "deadlock-free":
        sinks = {idx[s] for s in prop["sinks"] if s in idx}
        return any(k > 0 and i not in sinks for i, k in enumerate(m))
    if ty == "terminates-at-sink":
        return not any(count(s) > 0 for s in prop["sinks"])
    if ty == "quiescent-count":
        total = sum(count(p) for p in set(prop["places"]))
        return total < prop["min"] or ("max" in prop and total > prop["max"])
    raise ValueError(ty)


# ======================================================================
# Properties: 3-6 per net over all six types, tuned near reachable values
# ======================================================================


def forward_targets(o, acc):
    if o is None:
        return
    if o[0] == "forward":
        acc.append(o[2])
    elif o[0] == "timeout":
        forward_targets(o[1], acc)
    elif o[0] in ("and", "xor"):
        for c in o[1]:
            forward_targets(c, acc)


def gen_props(seed: int, net: dict) -> list[dict]:
    rng = Rng((seed * 0x2545F4914F6CDD1D + 0xC0FFEE) & M64)
    names = net["names"]
    u = len(names)
    ex = Explorer(net)
    states, complete = ex.explore()

    def some(lo, hi):
        return [names[i] for i in rng.distinct(u, rng.range(lo, min(hi, u)))]

    k = rng.range(3, 6)
    kinds = sorted(rng.distinct(len(PROPERTY_TYPES), k))
    props = []
    for kind in kinds:
        ty = PROPERTY_TYPES[kind]
        pid = f"prop{len(props)}"
        if ty == "deadlock-free":
            props.append({"id": pid, "type": ty, "sinks": [] if rng.chance(40) else some(1, 2)})
        elif ty == "terminates-at-sink":
            props.append({"id": pid, "type": ty, "sinks": [] if rng.chance(10) else some(1, 2)})
        elif ty == "place-bound":
            fw: list = []
            for t in net["transitions"]:
                forward_targets(t["out"], fw)
            place = rng.pick(fw) if fw and rng.chance(40) else rng.below(u)
            if complete:
                reach = max(m[place] for m in states)
                bound = max(0, reach - rng.below(2))
            else:
                bound = rng.range(0, 2)
            props.append({"id": pid, "type": ty, "place": names[place], "bound": bound})
        elif ty == "mutual-exclusion":
            # Exactly two places, which every language can express (Java and TypeScript take
            # two); the named net bug-mutex-pairwise exercises longer pairwise lists.
            props.append({"id": pid, "type": ty, "places": [names[i] for i in rng.distinct(u, 2)]})
        elif ty == "unreachable":
            props.append({"id": pid, "type": ty, "places": some(1, 2)})
        else:
            places = some(1, 3)
            prop = {"id": pid, "type": ty, "places": places}
            idx = {n: i for i, n in enumerate(names)}
            totals = sorted({sum(m[idx[p]] for p in places) for m in states if ex.quiescent(m)})
            if complete and totals:
                lo = max(0, totals[0] + rng.pick([-1, 0, 0, 1]))
                hi = totals[-1] + rng.pick([-1, 0, 0, 1])
            else:
                lo = rng.range(0, 2)
                hi = lo + rng.range(0, 2)
            prop["min"] = lo
            if not rng.chance(30):
                prop["max"] = max(lo, hi)
            props.append(prop)
    return props


# ======================================================================
# JSON rendering (schema of the README)
# ======================================================================


def out_json(o, names):
    if o is None:
        return None
    kind = o[0]
    if kind == "place":
        return {"type": "place", "place": names[o[1]]}
    if kind in ("and", "xor"):
        return {"type": kind, "children": [out_json(c, names) for c in o[1]]}
    if kind == "timeout":
        return {"type": "timeout", "afterMs": TIMEOUT_MS, "child": out_json(o[1], names)}
    return {"type": "forward", "from": names[o[1]], "to": names[o[2]]}


def input_json(p, c, names):
    arc = {"place": names[p], "kind": c[0]}
    if c[0] in ("exactly", "atLeast"):
        arc["n"] = c[1]
    return arc


def net_json(net_id: str, net: dict, props: list[dict]) -> dict:
    names = net["names"]
    return {
        "id": net_id,
        "places": list(net["declared"]),
        "marking": {names[i]: k for i, k in enumerate(net["initial"]) if k > 0},
        "transitions": [
            {
                "name": t["name"],
                "inputs": [input_json(p, c, names) for p, c in t["inputs"]],
                "inhibitors": [names[p] for p in t["inhibitors"]],
                "reads": [names[p] for p in t["reads"]],
                "resets": [names[p] for p in t["resets"]],
                "output": out_json(t["out"], names),
                "priority": 0,
                **({"timing": t["timing"]} if "timing" in t else {}),
            }
            for t in net["transitions"]
        ],
        "properties": props,
    }


# ======================================================================
# Named nets: fixtures.json (netDescription is normative) and the two repros
# ======================================================================


def P(p):
    return {"type": "place", "place": p}


def AND(*cs):
    return {"type": "and", "children": list(cs)}


def XOR(*cs):
    return {"type": "xor", "children": list(cs)}


def T(name, inputs, output, inhibitors=(), reads=(), resets=(), timing=None):
    t = {
        "name": name,
        "inputs": [
            {"place": p, "kind": "one"} if isinstance(p, str) else dict(p) for p in inputs
        ],
        "inhibitors": list(inhibitors),
        "reads": list(reads),
        "resets": list(resets),
        "output": output,
        "priority": 0,
    }
    if timing is not None:
        t["timing"] = timing
    return t


def props(*ps):
    return [{"id": f"prop{i}", **p} for i, p in enumerate(ps)]


def named_nets() -> list[tuple[str, str, dict]]:
    """(id, origin, net). `origin` names the fixture ids / regression the net ports."""
    nets = []

    def add(net_id, origin, places, marking, transitions, properties):
        nets.append((net_id, origin, {
            "id": net_id, "places": places, "marking": marking,
            "transitions": transitions, "properties": properties,
        }))

    add("fixture-circular-chain",
        "fixtures.json circularChain: circular-chain-deadlock-free, circular-chain-state-equation-deadlock-free",
        ["p0", "p1", "p2"], {"p0": 1},
        [T("t01", ["p0"], P("p1")), T("t12", ["p1"], P("p2")), T("t20", ["p2"], P("p0"))],
        props({"type": "deadlock-free", "sinks": []},
              {"type": "terminates-at-sink", "sinks": ["p2"]},
              {"type": "place-bound", "place": "p0", "bound": 1},
              {"type": "mutual-exclusion", "places": ["p0", "p1"]},
              {"type": "quiescent-count", "places": ["p0"], "min": 1, "max": 1}))
    add("fixture-dead-end-chain",
        "fixtures.json deadEndChain: dead-end-chain-deadlocks (sinkPlacesWhen siblings are out of the v1 schema)",
        ["p0", "p1", "p2"], {"p0": 1},
        [T("t01", ["p0"], P("p1")), T("t12", ["p1"], P("p2"))],
        props({"type": "deadlock-free", "sinks": []},
              {"type": "terminates-at-sink", "sinks": ["p2"]},
              {"type": "place-bound", "place": "p2", "bound": 0},
              {"type": "unreachable", "places": ["p0", "p2"]},
              {"type": "deadlock-free", "sinks": ["p2"]}))
    add("fixture-mutex-locked",
        "fixtures.json mutexLocked: mutex-with-lock-proven",
        ["idle1", "idle2", "lock", "crit1", "crit2"], {"idle1": 1, "idle2": 1, "lock": 1},
        [T("enter1", ["idle1", "lock"], P("crit1")),
         T("exit1", ["crit1"], AND(P("idle1"), P("lock"))),
         T("enter2", ["idle2", "lock"], P("crit2")),
         T("exit2", ["crit2"], AND(P("idle2"), P("lock")))],
        props({"type": "mutual-exclusion", "places": ["crit1", "crit2"]},
              {"type": "deadlock-free", "sinks": []},
              {"type": "place-bound", "place": "lock", "bound": 1},
              {"type": "unreachable", "places": ["crit1", "lock"]}))
    add("fixture-mutex-unlocked",
        "fixtures.json mutexUnlocked: mutex-without-lock-violated",
        ["idle1", "idle2", "crit1", "crit2"], {"idle1": 1, "idle2": 1},
        [T("enter1", ["idle1"], P("crit1")),
         T("exit1", ["crit1"], P("idle1")),
         T("enter2", ["idle2"], P("crit2")),
         T("exit2", ["crit2"], P("idle2"))],
        props({"type": "mutual-exclusion", "places": ["crit1", "crit2"]},
              {"type": "deadlock-free", "sinks": []},
              {"type": "place-bound", "place": "crit1", "bound": 1}))
    add("fixture-conserved-pair",
        "fixtures.json conservedPair: conserved-bound-proven, conserved-bound-violated, conserved-bound-state-equation-proven",
        ["p0", "p1"], {"p0": 3},
        [T("t", ["p0"], P("p1"))],
        props({"type": "place-bound", "place": "p1", "bound": 3},
              {"type": "place-bound", "place": "p1", "bound": 2},
              {"type": "deadlock-free", "sinks": ["p1"]},
              {"type": "terminates-at-sink", "sinks": ["p1"]},
              {"type": "quiescent-count", "places": ["p1"], "min": 3, "max": 3}))
    add("fixture-inhibitor-frozen",
        "fixtures.json inhibitorFrozen: inhibitor-frozen-unreachable-proven",
        ["p0", "blocker", "p1"], {"p0": 1, "blocker": 1},
        [T("t", ["p0"], P("p1"), inhibitors=["blocker"])],
        props({"type": "unreachable", "places": ["p1"]},
              {"type": "deadlock-free", "sinks": []},
              {"type": "place-bound", "place": "p0", "bound": 1}))
    add("fixture-h1-consume-all",
        "fixtures.json h1ConsumeAll: h1-consume-all-bound-violated",
        ["p0", "p1"], {"p0": 2},
        [T("t", [{"place": "p0", "kind": "all"}], P("p1"))],
        props({"type": "place-bound", "place": "p1", "bound": 0},
              {"type": "place-bound", "place": "p1", "bound": 1},
              {"type": "deadlock-free", "sinks": ["p1"]},
              {"type": "unreachable", "places": ["p0", "p1"]}))
    add("fixture-at-least-drain",
        "fixtures.json atLeastDrain: atleast-drain-bound-proven",
        ["p0", "p1"], {"p0": 3},
        [T("t", [{"place": "p0", "kind": "atLeast", "n": 2}], P("p1"))],
        props({"type": "place-bound", "place": "p1", "bound": 1},
              {"type": "quiescent-count", "places": ["p0"], "min": 0, "max": 0},
              {"type": "deadlock-free", "sinks": ["p1"]}))
    add("fixture-sink-partial-terminal",
        "fixtures.json sinkPartialTerminal: sink-partial-terminal-violated, sink-partial-terminal-reaches-sink-proven",
        ["p0", "done", "stuck"], {"p0": 1},
        [T("t", ["p0"], AND(P("done"), P("stuck")))],
        props({"type": "deadlock-free", "sinks": ["done"]},
              {"type": "terminates-at-sink", "sinks": ["done"]},
              {"type": "mutual-exclusion", "places": ["done", "stuck"]}))
    add("fixture-sink-drained-terminal",
        "fixtures.json sinkDrainedTerminal: sink-drained-terminal-proven, sink-drained-terminal-reaches-sink-violated",
        ["p0", "done"], {"p0": 1},
        [T("t", ["p0"], None)],
        props({"type": "deadlock-free", "sinks": ["done"]},
              {"type": "terminates-at-sink", "sinks": ["done"]},
              {"type": "place-bound", "place": "done", "bound": 0}))
    add("fixture-fork-in-flight",
        "fixtures.json terminalForkInFlight, WITHOUT its net-declared terminal (EXEC-042 is out of v1 scope)",
        ["start", "a", "b", "done", "result"], {"start": 1},
        [T("fork", ["start"], AND(P("a"), P("b"))),
         T("finish", ["a"], P("done")),
         T("work", ["b"], P("result"))],
        props({"type": "deadlock-free", "sinks": ["done"]},
              {"type": "terminates-at-sink", "sinks": ["done"]},
              {"type": "quiescent-count", "places": ["done", "result"], "min": 2, "max": 2},
              {"type": "unreachable", "places": ["a", "result"]}))
    add("bug-stray-token",
        "route_agreement.rs regression_stray_token_on_undeclared_place (fixed in e058472)",
        ["c", "d"], {"a": 1},
        [T("t", ["c"], P("d"))],
        props({"type": "deadlock-free", "sinks": ["d"]},
              {"type": "place-bound", "place": "a", "bound": 0},
              {"type": "terminates-at-sink", "sinks": ["d"]}))
    add("bug-forward-deposit",
        "route_agreement.rs regression_forward_input_deposits_every_consumed_token (R1)",
        ["a", "b", "c"], {"a": 2},
        [T("t", [{"place": "a", "kind": "exactly", "n": 2}],
           XOR(P("c"), {"type": "timeout", "afterMs": TIMEOUT_MS,
                        "child": {"type": "forward", "from": "a", "to": "b"}}))],
        props({"type": "place-bound", "place": "b", "bound": 1},
              {"type": "place-bound", "place": "b", "bound": 2},
              {"type": "deadlock-free", "sinks": ["b", "c"]}))
    add("bug-drained-forward",
        "smt_verifier.rs a_forward_of_a_drained_input_is_decided_by_the_graph_and_refused_by_the_linear_routes",
        ["a", "b", "c"], {"a": 2},
        [T("t", [{"place": "a", "kind": "all"}],
           XOR(P("c"), {"type": "timeout", "afterMs": TIMEOUT_MS,
                        "child": {"type": "forward", "from": "a", "to": "b"}}))],
        props({"type": "place-bound", "place": "b", "bound": 1},
              {"type": "place-bound", "place": "b", "bound": 2},
              {"type": "deadlock-free", "sinks": ["b", "c"]}))
    # Pairwise mutual exclusion over three places (VER-002 AC10). Java and TypeScript take
    # exactly two places and skip the longer lists; Rust and Python check them.
    add("bug-mutex-pairwise",
        "smt_verifier.rs a_three_place_mutual_exclusion_is_pairwise_on_every_route",
        ["s", "a", "b", "c", "s2", "x", "y", "z"], {"s": 1, "s2": 1},
        [T("t", ["s"], AND(P("a"), P("b"))),
         T("t1", ["s2"], P("x")),
         T("t2", ["x"], P("y")),
         T("t3", ["y"], P("z"))],
        props({"type": "mutual-exclusion", "places": ["c", "a", "b"]},
              {"type": "mutual-exclusion", "places": ["x", "y", "z"]},
              {"type": "mutual-exclusion", "places": ["z", "z"]},
              {"type": "mutual-exclusion", "places": ["a", "c"]}))
    # Deadline reaping ([TIME-013], [VER-002] reap-quiescence): ReapingVsUntimed.lean's witness,
    # the same net with an immediate sibling that shadows the reap, and a reapable self-loop.
    window35 = {"kind": "window", "earliestMs": 3, "latestMs": 5}
    add("reap-witness",
        "lean/Libpetri/Novel/ReapingVsUntimed.lean reaping_refutes_ver004_ac3; ReapAware.lean witness_caught",
        ["p0", "p1"], {"p0": 1},
        [T("t", ["p0"], P("p1"), timing=window35)],
        props({"type": "deadlock-free", "sinks": ["p1"]},
              {"type": "terminates-at-sink", "sinks": ["p1"]},
              {"type": "quiescent-count", "places": ["p1"], "min": 1, "max": 1},
              {"type": "place-bound", "place": "p1", "bound": 1}))
    add("reap-shadowed",
        "VER-002 AC12: an immediate transition on the same input shadows the reap",
        ["p0", "p1"], {"p0": 1},
        [T("t", ["p0"], P("p1"), timing=window35),
         T("u", ["p0"], P("p1"), timing={"kind": "immediate"})],
        props({"type": "deadlock-free", "sinks": ["p1"]},
              {"type": "terminates-at-sink", "sinks": ["p1"]}))
    add("reap-self-loop",
        "VER-002 AC13: a reapable self-loop is not proven deadlock-free structurally",
        ["p0"], {"p0": 1},
        [T("t", ["p0"], P("p0"), timing={"kind": "deadline", "latestMs": 10})],
        props({"type": "deadlock-free", "sinks": []},
              {"type": "place-bound", "place": "p0", "bound": 1}))
    return nets


# ======================================================================
# Corpus assembly, writing, checking
# ======================================================================


def build_corpus(seed: int, count: int) -> tuple[dict[str, dict], dict]:
    nets: dict[str, dict] = {}
    origins: dict[str, str] = {}
    for net_id, origin, net in named_nets():
        nets[net_id] = net
        origins[net_id] = origin
    for i in range(count):
        s = (seed + i) & M64
        net_id = f"gen-{i:06d}"
        spec = gen_net(s)
        gen_timing(s, spec)
        nets[net_id] = net_json(net_id, spec, gen_props(s, spec))
        origins[net_id] = f"generated, seed {s:#x}"
    index = {
        "version": 1,
        "generator": "scripts/conformance-corpus.py",
        "seed": f"{seed:#x}",
        "generated": count,
        "reference": None,
        "ids": list(nets),
        "origins": origins,
    }
    return nets, index


def dumps(doc) -> str:
    return json.dumps(doc, indent=2, ensure_ascii=False) + "\n"


def dumps_net(net: dict) -> str:
    """One transition / property per line: small files, line-per-change diffs."""

    def one(x) -> str:
        return json.dumps(x, ensure_ascii=False)

    lines = ["{"]
    keys = list(net)
    for k, key in enumerate(keys):
        sep = "," if k < len(keys) - 1 else ""
        value = net[key]
        if key in ("transitions", "properties") and value:
            rows = [f"    {one(v)}" for v in value]
            lines.append(f'  "{key}": [\n' + ",\n".join(rows) + f"\n  ]{sep}")
        else:
            lines.append(f'  "{key}": {one(value)}{sep}')
    lines.append("}")
    return "\n".join(lines) + "\n"


def write_dir(directory: Path, files: dict[str, str]) -> None:
    directory.mkdir(parents=True, exist_ok=True)
    for stale in directory.glob("*.json"):
        if stale.name not in files:
            stale.unlink()
    for name, text in files.items():
        path = directory / name
        if not path.exists() or path.read_text() != text:
            path.write_text(text)


def run_reference(reference: list[str], nets_dir: Path, out_dir: Path, cap: int | None) -> None:
    cmd = reference + [str(nets_dir), str(out_dir)]
    if cap is not None:
        cmd += ["--cap", str(cap)]
    print("conformance-corpus: " + " ".join(shlex.quote(c) for c in cmd), file=sys.stderr)
    proc = subprocess.run(cmd, cwd=LEAN)
    if proc.returncode != 0:
        sys.exit(f"conformance-corpus: the reference failed (exit {proc.returncode})")


def reference_version(expected_dir: Path) -> str | None:
    versions = {json.loads(p.read_text()).get("reference") for p in expected_dir.glob("*.json")}
    if len(versions) > 1:
        sys.exit(f"conformance-corpus: expected/ mixes reference versions {sorted(map(str, versions))}")
    return next(iter(versions), None)


def without_reference(text: str):
    doc = json.loads(text)
    doc.pop("reference", None)
    return doc


def stats(nets: dict[str, dict]) -> str:
    card = {"one": 0, "exactly": 0, "all": 0, "atLeast": 0}
    arcs = {"inhibitors": 0, "reads": 0, "resets": 0}
    outs = {"none": 0, "and": 0, "xor": 0, "timeout": 0, "forward": 0}
    types = {t: 0 for t in PROPERTY_TYPES}
    verdicts = {"violated": 0, "holds": 0, "undecided": 0}
    per_type = {t: {"violated": 0, "holds": 0, "undecided": 0} for t in PROPERTY_TYPES}
    undeclared = arcless = incomplete = 0
    timing = {"untimed nets": 0, "timed nets": 0}
    for net in nets.values():
        kinds = [t["timing"]["kind"] for t in net["transitions"] if "timing" in t]
        timing["timed nets" if kinds else "untimed nets"] += 1
        for k in kinds:
            timing[k] = timing.get(k, 0) + 1
        declared = set(net["places"])
        used = set()
        for t in net["transitions"]:
            for a in t["inputs"]:
                card[a["kind"]] += 1
                used.add(a["place"])
            for k in arcs:
                arcs[k] += len(t[k])
                used.update(t[k])
            s = json.dumps(t["output"])
            if t["output"] is None:
                outs["none"] += 1
            for k in ("and", "xor", "timeout", "forward"):
                outs[k] += f'"type": "{k}"' in s
            for part in s.split('"place": "')[1:] + s.split('"to": "')[1:]:
                used.add(part.split('"')[0])
        undeclared += any(p not in declared and p not in used for p in net["marking"])
        arcless += any(p not in used for p in declared)
        # Re-derive the explorer's view for the composition line only.
        names = sorted(declared | used | set(net["marking"]))
        idx = {n: i for i, n in enumerate(names)}
        spec = {
            "names": names,
            "initial": [net["marking"].get(n, 0) for n in names],
            "transitions": [
                {
                    "name": t["name"],
                    "inputs": [(idx[a["place"]], (a["kind"], a.get("n"))) for a in t["inputs"]],
                    "inhibitors": [idx[p] for p in t["inhibitors"]],
                    "reads": [idx[p] for p in t["reads"]],
                    "resets": [idx[p] for p in t["resets"]],
                    "out": _from_json(t["output"], idx),
                    **({"timing": t["timing"]} if "timing" in t else {}),
                }
                for t in net["transitions"]
            ],
        }
        ex = Explorer(spec)
        states, complete = ex.explore()
        incomplete += not complete
        for prop in net["properties"]:
            types[prop["type"]] += 1
            if any(bad(prop, idx, ex, m) for m in states):
                v = "violated"
            else:
                v = "holds" if complete else "undecided"
            verdicts[v] += 1
            per_type[prop["type"]][v] += 1
    lines = [
        f"nets {len(nets)}, properties {sum(types.values())}",
        f"inputs {card}, arcs {arcs}",
        f"transitions by output {outs}",
        f"timing {timing}",
        f"nets with a marked undeclared inert place {undeclared}, with a declared or marked arc-less place {arcless}",
        f"explorer (NOT the reference): incomplete nets {incomplete}, verdicts {verdicts}",
    ]
    lines += [f"  {t:18} {per_type[t]}" for t in PROPERTY_TYPES]
    return "\n".join(lines)


def _from_json(o, idx):
    if o is None:
        return None
    ty = o["type"]
    if ty == "place":
        return ("place", idx[o["place"]])
    if ty in ("and", "xor"):
        return (ty, [_from_json(c, idx) for c in o["children"]])
    if ty == "timeout":
        return ("timeout", _from_json(o["child"], idx))
    return ("forward", idx[o["from"]], idx[o["to"]])


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    mode = ap.add_mutually_exclusive_group()
    mode.add_argument("--update", action="store_true", help="also regenerate expected/ with the Lean reference")
    mode.add_argument("--check", action="store_true", help="fail when nets/, corpus.json or expected/ are stale")
    mode.add_argument("--stats", action="store_true", help="print the corpus composition")
    ap.add_argument("--seed", type=lambda s: int(s, 0), default=DEFAULT_SEED)
    ap.add_argument("--count", type=int, default=DEFAULT_COUNT)
    ap.add_argument("--cap", type=int, default=None, help="state cap passed to the reference")
    ap.add_argument("--reference", default="lake exe reference",
                    help="reference command, run inside lean/ (default: %(default)s)")
    args = ap.parse_args(argv)

    nets, index = build_corpus(args.seed, args.count)
    net_files = {f"{i}.json": dumps_net(n) for i, n in nets.items()}
    reference = shlex.split(args.reference)

    if args.stats:
        print(stats(nets))
        return 0

    if args.check:
        problems = []
        on_disk = {p.name for p in NETS.glob("*.json")}
        for name, text in net_files.items():
            if name not in on_disk:
                problems.append(f"nets/{name} missing")
            elif (NETS / name).read_text() != text:
                problems.append(f"nets/{name} differs from the generator")
        problems += [f"nets/{n} is not in the corpus" for n in sorted(on_disk - set(net_files))]
        if not INDEX.exists() or without_reference(INDEX.read_text()) != without_reference(dumps(index)):
            problems.append("corpus.json differs from the generator")
        with tempfile.TemporaryDirectory() as tmp:
            fresh = Path(tmp) / "expected"
            fresh.mkdir()
            run_reference(reference, NETS, fresh, args.cap)
            want = {p.name: p.read_text() for p in fresh.glob("*.json")}
            have = {p.name: p.read_text() for p in EXPECTED.glob("*.json")} if EXPECTED.exists() else {}
            for name in sorted(set(want) | set(have)):
                if name not in have:
                    problems.append(f"expected/{name} missing")
                elif name not in want:
                    problems.append(f"expected/{name} is not produced by the reference")
                elif without_reference(have[name]) != without_reference(want[name]):
                    problems.append(f"expected/{name} differs from the reference's output")
            fresh_version = reference_version(fresh)
            if have and reference_version(EXPECTED) != fresh_version:
                print(f"conformance-corpus: note: checked-in reference version "
                      f"{reference_version(EXPECTED)} != {fresh_version} (verdicts identical)", file=sys.stderr)
        for p in problems[:50]:
            print("  " + p, file=sys.stderr)
        if problems:
            print(f"conformance-corpus: STALE ({len(problems)} problem(s)); run "
                  "scripts/conformance-corpus.py --update", file=sys.stderr)
            return 1
        print(f"conformance-corpus: {len(nets)} nets and their expected verdicts are current")
        return 0

    write_dir(NETS, net_files)
    if args.update:
        with tempfile.TemporaryDirectory() as tmp:
            fresh = Path(tmp) / "expected"
            fresh.mkdir()
            run_reference(reference, NETS, fresh, args.cap)
            produced = {p.name for p in fresh.glob("*.json")}
            missing = sorted(set(net_files) - produced)
            if missing:
                sys.exit(f"conformance-corpus: the reference wrote no verdicts for {missing[:10]}")
            if EXPECTED.exists():
                shutil.rmtree(EXPECTED)
            shutil.copytree(fresh, EXPECTED)
    if EXPECTED.exists():
        index["reference"] = reference_version(EXPECTED)
    INDEX.write_text(dumps(index))
    print(f"conformance-corpus: wrote {len(nets)} nets"
          + (" and their expected verdicts" if args.update else "")
          + f" to {CORPUS.relative_to(REPO)}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
