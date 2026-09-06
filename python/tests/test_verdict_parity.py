"""Cross-language verdict-parity fixture runner.

Runs every fixture in ``spec/verification-fixtures/fixtures.json`` — the shared
expectations all four language implementations assert against — through the
Python binding with BOTH independent validation layers on: certificate checking
(a ``proven`` re-verified as an inductive invariant in a second solver run) and
counterexample replay (a ``violated`` re-executed against the abstract
semantics).

The nets are built here with the public Python API per each fixture's normative
``netDescription``; the reference builders are
``java/src/test/java/org/libpetri/smt/fixtures/VerificationNets.java``,
``typescript/tests/fixtures/verification-nets.ts`` and
``rust/libpetri-verification/tests/common/nets.rs``.

A verdict disagreeing with a fixture's ``expected`` is a parity FINDING to
investigate and report — never a reason to adjust the fixture. Every fixture
runs before the assertion fires, so one finding does not mask another.
"""

from __future__ import annotations

import json
import pathlib

import libpetri as lp
import pytest

FIXTURES = (
    pathlib.Path(__file__).resolve().parents[2]
    / "spec"
    / "verification-fixtures"
    / "fixtures.json"
)

# The line every implementation prints when the ν name-aware state-class-graph
# verifier (NU-050 Route B) — not the SMT / Route A encoders — decided the query.
# Fixtures marked ``"route": "B"`` assert it BEFORE their verdict, so a silent
# fall-back to Route A fails loudly instead of passing vacuously.
ROUTE_B_MARKER = "ν-net Route B: name-aware state-class graph (NU-050)"


def _net(name: str):
    """Builds the named fixture net, its initial marking and env configuration."""
    if name == "circularChain":
        # p0(1) -> p1 -> p2 -> p0: the token circulates forever.
        p0, p1, p2 = lp.Place("p0"), lp.Place("p1"), lp.Place("p2")
        net = (
            lp.Net("circularChain")
            .transition(lp.Transition("t01").input(lp.one(p0)).output(lp.out(p1)).action(lp.fork).build())
            .transition(lp.Transition("t12").input(lp.one(p1)).output(lp.out(p2)).action(lp.fork).build())
            .transition(lp.Transition("t20").input(lp.one(p2)).output(lp.out(p0)).action(lp.fork).build())
            .build()
        )
        return net, {"p0": 1}, {}

    if name == "deadEndChain":
        # p0(1) -> p1 -> p2, and nothing consumes p2: a genuine dead marking
        # (p2 is a normal place, NOT a declared sink).
        p0, p1, p2 = lp.Place("p0"), lp.Place("p1"), lp.Place("p2")
        net = (
            lp.Net("deadEndChain")
            .transition(lp.Transition("t01").input(lp.one(p0)).output(lp.out(p1)).action(lp.fork).build())
            .transition(lp.Transition("t12").input(lp.one(p1)).output(lp.out(p2)).action(lp.fork).build())
            .build()
        )
        return net, {"p0": 1}, {}

    if name == "mutexLocked":
        # Binary semaphore: enter_i consumes idle_i + lock, exit_i returns both.
        idle1, idle2 = lp.Place("idle1"), lp.Place("idle2")
        lock = lp.Place("lock")
        crit1, crit2 = lp.Place("crit1"), lp.Place("crit2")
        net = (
            lp.Net("mutexLocked")
            .transition(
                lp.Transition("enter1").input(lp.one(idle1)).input(lp.one(lock))
                .output(lp.out(crit1)).action(lp.fork).build()
            )
            .transition(
                lp.Transition("exit1").input(lp.one(crit1))
                .output(lp.and_(lp.out(idle1), lp.out(lock))).action(lp.fork).build()
            )
            .transition(
                lp.Transition("enter2").input(lp.one(idle2)).input(lp.one(lock))
                .output(lp.out(crit2)).action(lp.fork).build()
            )
            .transition(
                lp.Transition("exit2").input(lp.one(crit2))
                .output(lp.and_(lp.out(idle2), lp.out(lock))).action(lp.fork).build()
            )
            .build()
        )
        return net, {"idle1": 1, "idle2": 1, "lock": 1}, {}

    if name == "mutexUnlocked":
        # Same shape but no lock place at all: both criticals reachable at once.
        idle1, idle2 = lp.Place("idle1"), lp.Place("idle2")
        crit1, crit2 = lp.Place("crit1"), lp.Place("crit2")
        net = (
            lp.Net("mutexUnlocked")
            .transition(lp.Transition("enter1").input(lp.one(idle1)).output(lp.out(crit1)).action(lp.fork).build())
            .transition(lp.Transition("exit1").input(lp.one(crit1)).output(lp.out(idle1)).action(lp.fork).build())
            .transition(lp.Transition("enter2").input(lp.one(idle2)).output(lp.out(crit2)).action(lp.fork).build())
            .transition(lp.Transition("exit2").input(lp.one(crit2)).output(lp.out(idle2)).action(lp.fork).build())
            .build()
        )
        return net, {"idle1": 1, "idle2": 1}, {}

    if name == "conservedPair":
        # p0(3) -> p1 with conservation p0 + p1 = 3: the bound-3 proof needs the
        # P-invariant strengthening (exercises the R'-candidate certificate check).
        p0, p1 = lp.Place("p0"), lp.Place("p1")
        net = (
            lp.Net("conservedPair")
            .transition(lp.Transition("t").input(lp.one(p0)).output(lp.out(p1)).action(lp.fork).build())
            .build()
        )
        return net, {"p0": 3}, {}

    if name == "envSingleFeed":
        # Environment place e in always-available injection mode (VER-006).
        e, p1 = lp.Place("e"), lp.Place("p1")
        net = (
            lp.Net("envSingleFeed")
            .transition(lp.Transition("t").input(lp.one(e)).output(lp.out(p1)).action(lp.fork).build())
            .build()
        )
        return net, {}, {"environment_places": ["e"], "environment_mode": lp.always_available()}

    if name == "inhibitorFrozen":
        # Nothing ever drains blocker(1), so t stays frozen and p1 stays empty.
        p0, blocker, p1 = lp.Place("p0"), lp.Place("blocker"), lp.Place("p1")
        net = (
            lp.Net("inhibitorFrozen")
            .transition(
                lp.Transition("t").input(lp.one(p0)).inhibitor(lp.inhibitor(blocker))
                .output(lp.out(p1)).action(lp.fork).build()
            )
            .build()
        )
        return net, {"p0": 1, "blocker": 1}, {}

    if name == "h1ConsumeAll":
        # The Strengthening.lean H1 witness: t: all(p0) -> p1 with p0(2).
        p0, p1 = lp.Place("p0"), lp.Place("p1")
        net = (
            lp.Net("h1ConsumeAll")
            .transition(lp.Transition("t").input(lp.all_tokens(p0)).output(lp.out(p1)).action(lp.fork).build())
            .build()
        )
        return net, {"p0": 2}, {}

    if name == "atLeastDrain":
        # t: at_least(2)(p0) -> p1 with p0(3): the drain empties p0 on the first
        # firing, so t fires at most once and p1 <= 1.
        p0, p1 = lp.Place("p0"), lp.Place("p1")
        net = (
            lp.Net("atLeastDrain")
            .transition(lp.Transition("t").input(lp.at_least(2, p0)).output(lp.out(p1)).action(lp.fork).build())
            .build()
        )
        return net, {"p0": 3}, {}

    if name == "sinkPartialTerminal":
        # p0(1) -> done + stuck. The only quiescent marking holds a token in the
        # declared sink `done` AND one in the non-sink `stuck`.
        p0, done, stuck = lp.Place("p0"), lp.Place("done"), lp.Place("stuck")
        net = (
            lp.Net("sinkPartialTerminal")
            .transition(
                lp.Transition("t").input(lp.one(p0))
                .output(lp.and_(lp.out(done), lp.out(stuck))).action(lp.fork).build()
            )
            .build()
        )
        return net, {"p0": 1}, {}

    if name == "sinkDrainedTerminal":
        # t: one(p0) with NO output spec — a sink transition (CORE-042). `done`
        # touches no arc, so it is declared explicitly on the builder; after t
        # fires the net holds no tokens anywhere.
        p0, done = lp.Place("p0"), lp.Place("done")
        net = (
            lp.Net("sinkDrainedTerminal")
            .place(done)
            .transition(lp.Transition("t").input(lp.one(p0)).build())
            .build()
        )
        return net, {"p0": 1}, {}

    # === Route B fixtures (``"route": "B"`` in fixtures.json) ===
    #
    # ν nets in the BASE mint->matched-join fragment, so the name-aware
    # state-class-graph verifier (NU-050 Route B) decides them and the SMT /
    # Route A encoders never see them. They pin the two markings on which Route
    # B's deadlock predicate — quiescent AND NOT(every marked place is a declared
    # sink) — disagrees with VER-002's, which Route A implements verbatim. The
    # disagreement is recorded deliberately; see each fixture's netDescription.

    if name == "nuMixedTerminal":
        # `fork` co-mints ONE fresh name into branchA+branchB; `join` correlates
        # them by name equality into done+stuck. The only quiescent marking is
        # {done:1, stuck:1} — a token in the declared sink AND one in the
        # non-sink `stuck`. Route B: violated. Route A on the same shape (see
        # `sinkPartialTerminal`): proven. Non-vacuity guard: a failed ν
        # correlation would also quiesce (at {branchA:1, branchB:1}, neither a
        # sink) and also read violated here — `nuDrainedTerminal` below, built on
        # the identical correlation, is what turns violated if that ever happens.
        source = lp.Place("source")
        branch_a, branch_b = lp.Place("branchA"), lp.Place("branchB")
        done, stuck = lp.Place("done"), lp.Place("stuck")
        net = (
            lp.Net("nuMixedTerminal")
            .transition(
                lp.Transition("fork").input(lp.one(source))
                .output(lp.and_(branch_a, branch_b)).action(lp.fork).build()
            )
            .transition(
                lp.Transition("join").input(lp.one(branch_a)).input(lp.one(branch_b))
                .match_spec(lp.match_spec([(branch_a, lambda m: m), (branch_b, lambda m: m)]))
                .output(lp.and_(lp.out(done), lp.out(stuck))).action(lp.fork).build()
            )
            .build()
        )
        return net, {"source": 1}, {}

    if name == "nuDrainedTerminal":
        # Same mint->join shape, but `join` has NO output spec — a sink
        # transition (CORE-042 / CORE-043 AC4) — so the only quiescent marking is
        # the EMPTY one. The declared sink `done` touches no arc and is therefore
        # declared explicitly on the builder, so the declaration resolves against
        # the flattened net (the same requirement its Route A sibling carries).
        # Route B: proven — vacuously as to the predicate (nothing is marked
        # outside the sinks) but NOT as to the net: the empty marking is reachable
        # only because the ν join really correlates the co-minted pair and drains
        # it; a correlation failure would quiesce at {branchA:1, branchB:1} and
        # turn this fixture violated. Route A on the same shape (see
        # `sinkDrainedTerminal`): violated.
        source = lp.Place("source")
        branch_a, branch_b = lp.Place("branchA"), lp.Place("branchB")
        done = lp.Place("done")
        net = (
            lp.Net("nuDrainedTerminal")
            .place(done)
            .transition(
                lp.Transition("fork").input(lp.one(source))
                .output(lp.and_(branch_a, branch_b)).action(lp.fork).build()
            )
            .transition(
                lp.Transition("join").input(lp.one(branch_a)).input(lp.one(branch_b))
                .match_spec(lp.match_spec([(branch_a, lambda m: m), (branch_b, lambda m: m)]))
                .build()
            )
            .build()
        )
        return net, {"source": 1}, {}

    if name == "nuScatterGather":
        # ν scatter-gather on Route A's exact name-coloured encoding (NU-053): a
        # declared budget puts the reachability-safety query on the coloured
        # encoder. fork consumes source+budget and co-mints one fresh name into
        # branchA+branchB (plus a pending token); join correlates the branches and
        # returns the budget token. Conservation budget + pending = 2 bounds
        # budget by 2.
        source, budget, pending = lp.Place("source"), lp.Place("budget"), lp.Place("pending")
        a, b, merged = lp.Place("branchA"), lp.Place("branchB"), lp.Place("merged")
        net = (
            lp.Net("nuScatterGather")
            .transition(
                lp.Transition("fork").input(lp.one(source)).input(lp.one(budget))
                .output(lp.and_(a, b, pending)).action(lp.fork).build()
            )
            .transition(
                lp.Transition("join").input(lp.one(a)).input(lp.one(b)).input(lp.one(pending))
                .match_spec(lp.match_spec([(a, lambda m: m), (b, lambda m: m)]))
                .output(lp.and_(merged, budget)).action(lp.fork).build()
            )
            .build()
        )
        return net, {"source": 3, "budget": 2}, {}

    raise AssertionError(
        f"unknown fixture net {name!r} — add its builder here "
        "(the shared fixtures.json gained a net this implementation does not build yet)"
    )


def _property(spec):
    kind = spec["type"]
    if kind == "deadlock-free":
        return lp.deadlock_free()
    if kind == "terminates-at-sink":
        return lp.terminates_at_sink()
    if kind == "mutual-exclusion":
        return lp.mutual_exclusion(spec["places"])
    if kind == "place-bound":
        return lp.place_bound(spec["place"], spec["bound"])
    if kind == "unreachable":
        # The shared schema's `unreachable` carries a singular `place`.
        return lp.unreachable([spec["place"]])
    raise AssertionError(f"unknown fixture property type {kind!r}")


def test_verdict_parity_fixtures():
    if not (lp.HAS_Z3 and lp.z3_available()):
        # tests/test_z3_gate.py turns this skip into a failure on a CI runner.
        pytest.skip(
            "VERDICT PARITY NOT RUN: the wheel was built without the z3 feature or no "
            "usable z3 executable resolves, so the shared fixtures were not checked "
            "against the Python binding at all"
        )

    doc = json.loads(FIXTURES.read_text())
    fixtures = doc["fixtures"]
    assert fixtures, "fixtures.json lists no fixtures"

    findings = []
    for fixture in fixtures:
        fid = fixture["id"]
        expected = fixture["expected"]
        net, marking, env = _net(fixture["net"])
        result = lp.verify(
            net,
            _property(fixture["property"]),
            initial_marking=marking,
            # Optional shared-schema fields: expected terminal places (VER-002) and
            # ν budget places (NU-040, Route A's coloured encoding).
            sink_places=fixture.get("sinkPlaces") or None,
            budget_places=fixture.get("budgetPlaces") or None,
            semiflow_invariants=bool(fixture.get("semiflowInvariants", False)),
            # Both independent validation layers explicitly ON — the point of
            # the parity suite (they are also the defaults).
            certificate_check=True,
            counterexample_replay=True,
            timeout_ms=30_000,
            **env,
        )
        route_b = fixture.get("route") == "B"
        print(
            f"[parity] {fid}: expected={expected} got={result.verdict} "
            f"route={fixture.get('route', 'A')} "
            f"replay_confirmed={result.counterexample_confirmed} elapsed={result.elapsed_ms}ms"
        )
        # The route marker is checked FIRST: a `route: "B"` fixture that silently
        # fell back to Route A would pin nothing, so name that failure directly
        # rather than letting it surface as a confusing verdict mismatch.
        if route_b and ROUTE_B_MARKER not in result.report:
            findings.append(
                f'ROUTE FINDING [{fid}]: fixture declares route "B" but the report does not '
                "name the ν name-aware state-class graph — the query fell back to Route A, so "
                "the Route B deadlock predicate was never exercised\n"
                f"--- verifier report ---\n{result.report}"
            )
            continue
        if result.verdict != expected:
            findings.append(
                f"PARITY FINDING [{fid}]: expected {expected!r}, got {result.verdict!r}\n"
                f"--- verifier report ---\n{result.report}"
            )
            continue
        needle = fixture.get("expectReportContains")
        if needle is not None and needle not in result.report:
            findings.append(
                f"PARITY FINDING [{fid}]: verdict {result.verdict!r} matches but the report "
                f"is missing the required substring {needle!r}\n"
                f"--- verifier report ---\n{result.report}"
            )
            continue
        # Route B is exempt: its counterexample is a path of the name-partition
        # graph, not of the flat abstract semantics, so it reports
        # counterexample_confirmed = None by construction.
        if expected == "violated" and not route_b and result.counterexample_confirmed is not True:
            findings.append(
                f"REPLAY REGRESSION [{fid}]: verdict is violated as expected, but the "
                f"counterexample no longer replays (confirmed="
                f"{result.counterexample_confirmed})\n"
                f"--- verifier report ---\n{result.report}"
            )

    assert not findings, f"\n{len(findings)} parity finding(s):\n\n" + "\n\n".join(findings)
