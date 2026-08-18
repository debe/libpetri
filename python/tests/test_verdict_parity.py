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

    raise AssertionError(
        f"unknown fixture net {name!r} — add its builder here "
        "(the shared fixtures.json gained a net this implementation does not build yet)"
    )


def _property(spec):
    kind = spec["type"]
    if kind == "deadlock-free":
        return lp.deadlock_free()
    if kind == "mutual-exclusion":
        return lp.mutual_exclusion(spec["places"])
    if kind == "place-bound":
        return lp.place_bound(spec["place"], spec["bound"])
    if kind == "unreachable":
        # The shared schema's `unreachable` carries a singular `place`.
        return lp.unreachable([spec["place"]])
    raise AssertionError(f"unknown fixture property type {kind!r}")


def test_verdict_parity_fixtures():
    if not lp.HAS_Z3:
        pytest.skip(
            "VERDICT PARITY NOT RUN: the wheel was built without the z3 feature, so the "
            "shared fixtures were not checked against the Python binding at all"
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
            # Optional shared-schema field: expected terminal places (VER-002).
            sink_places=fixture.get("sinkPlaces") or None,
            # Both independent validation layers explicitly ON — the point of
            # the parity suite (they are also the defaults).
            certificate_check=True,
            counterexample_replay=True,
            timeout_ms=30_000,
            **env,
        )
        print(
            f"[parity] {fid}: expected={expected} got={result.verdict} "
            f"replay_confirmed={result.counterexample_confirmed} elapsed={result.elapsed_ms}ms"
        )
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
        if expected == "violated" and result.counterexample_confirmed is not True:
            findings.append(
                f"REPLAY REGRESSION [{fid}]: verdict is violated as expected, but the "
                f"counterexample no longer replays (confirmed="
                f"{result.counterexample_confirmed})\n"
                f"--- verifier report ---\n{result.report}"
            )

    assert not findings, f"\n{len(findings)} parity finding(s):\n\n" + "\n\n".join(findings)
