"""VER-006: SMT verification environment-injection soundness.

Regression for the bug where ``verify`` vacuously reported safety bounds as
``proven`` on nets with environment places (env columns could only be consumed,
never produced, so the reachable set froze at the initial marking). The core fix
lives in the Rust verifier; here we exercise it through the Python binding and the
newly exposed ``environment_mode`` selector.

Gated on ``lp.HAS_Z3`` — the SMT path requires the wheel built with the ``z3``
feature (pyproject's maturin config enables ``full`` which includes it).
"""

import libpetri as lp
import pytest

pytestmark = pytest.mark.skipif(not lp.HAS_Z3, reason="z3 feature not enabled")


def _env_source_net():
    """env IN -> T -> OUT."""
    in_p = lp.Place("IN")
    out = lp.Place("OUT")
    net = (
        lp.Net("env-source")
        .transition(
            lp.Transition("T").input(lp.one(in_p)).output(lp.out(out)).action(lp.fork).build()
        )
        .build()
    )
    return in_p, out, net


@pytest.mark.parametrize("k", [0, 1, 5])
def test_always_available_injects_place_bound_violated(k):
    # AlwaysAvailable lets IN be injected without bound, so OUT grows without
    # bound: place_bound(OUT, k) is violated for every finite k.
    _in, out, net = _env_source_net()
    result = lp.verify(
        net,
        lp.place_bound(out, k),
        environment_places=["IN"],
        environment_mode=lp.always_available(),
        timeout_ms=15_000,
    )
    assert result.verdict == "violated", result.report


def test_bounded_gates_by_multiplicity():
    # T2 needs EXACTLY 2 tokens from env IN per firing. bounded(1) starves it
    # (OUT stays 0 -> proven); always_available feeds it (OUT unbounded -> violated).
    # Also exercises the env-aware P-invariant: the closed-net law IN + 2*OUT = 0
    # must be discarded so OUT is not vacuously pinned.
    def build():
        in_p = lp.Place("IN")
        out = lp.Place("OUT")
        return out, (
            lp.Net("env-mult")
            .transition(
                lp.Transition("T2")
                .input(lp.exactly(2, in_p))
                .output(lp.out(out))
                .action(lp.fork)
                .build()
            )
            .build()
        )

    out, net = build()
    bounded1 = lp.verify(
        net,
        lp.place_bound(out, 0),
        environment_places=["IN"],
        environment_mode=lp.bounded(1),
        timeout_ms=15_000,
    )
    assert bounded1.verdict == "proven", bounded1.report

    out, net = build()
    always = lp.verify(
        net,
        lp.place_bound(out, 0),
        environment_places=["IN"],
        environment_mode=lp.always_available(),
        timeout_ms=15_000,
    )
    assert always.verdict == "violated", always.report


def test_ignore_mode_with_env_places_downgrades_to_unknown():
    # Ignore mode does not model injection; a "proven" here would be vacuous.
    # The default (no environment_mode) is also Ignore, so both must be unknown.
    _in, out, net = _env_source_net()

    explicit = lp.verify(
        net,
        lp.place_bound(out, 1),
        environment_places=["IN"],
        environment_mode=lp.ignore(),
        timeout_ms=15_000,
    )
    assert explicit.verdict == "unknown", explicit.report

    default = lp.verify(
        net,
        lp.place_bound(out, 1),
        environment_places=["IN"],
        timeout_ms=15_000,
    )
    assert default.verdict == "unknown", default.report


def test_control_closed_net_place_bound_stays_sound():
    # The defect is env-specific: closed-net place_bound must stay sound.
    a = lp.Place("A")
    b = lp.Place("B")
    net = (
        lp.Net("closed-cycle")
        .transition(lp.Transition("AtoB").input(lp.one(a)).output(lp.out(b)).action(lp.fork).build())
        .transition(lp.Transition("BtoA").input(lp.one(b)).output(lp.out(a)).action(lp.fork).build())
        .build()
    )

    # Note: verify() defaults the initial marking to empty; place_bound on an
    # all-empty closed net is trivially proven, which is still a sound result.
    safe = lp.verify(net, lp.place_bound(b, 1), timeout_ms=15_000)
    assert safe.verdict == "proven", safe.report


def _conserved_pair():
    """p0(3) -> p1: conservation p0 + p1 = 3, so place_bound(p1, 3) is proven."""
    p0 = lp.Place("p0")
    p1 = lp.Place("p1")
    net = (
        lp.Net("conservedPair")
        .transition(lp.Transition("t").input(lp.one(p0)).output(lp.out(p1)).action(lp.fork).build())
        .build()
    )
    return p0, p1, net


def test_certificate_check_kwarg_toggles_the_second_solver_run():
    # Default on: the proof is re-verified against the unstrengthened step
    # relation and the report says so. Off: the check is skipped, and says why.
    _p0, p1, net = _conserved_pair()
    on = lp.verify(net, lp.place_bound(p1, 3), initial_marking={"p0": 3}, timeout_ms=15_000)
    assert on.verdict == "proven", on.report
    assert "  Certificate check: PASSED (init, consecution, safety)" in on.report

    off = lp.verify(
        net,
        lp.place_bound(p1, 3),
        initial_marking={"p0": 3},
        certificate_check=False,
        timeout_ms=15_000,
    )
    assert off.verdict == "proven", off.report
    assert "  Certificate check: not applicable (disabled)" in off.report


def _semiflow_loop():
    """VER-007 test derivation: a budgeted work loop with one reset arc on a side
    place. Open: one(Budget), reset(Stamp) -> and(Work, Stamp); Step: one(Work) ->
    Done; Close: one(Done) -> and(Budget, Sink). The semiflow enumeration finds
    Budget + Work + Done = 1 with zero weight on the reset place."""
    budget, work, done = lp.Place("Budget"), lp.Place("Work"), lp.Place("Done")
    stamp, sink = lp.Place("Stamp"), lp.Place("Sink")
    net = (
        lp.Net("loop")
        .transition(
            lp.Transition("Open")
            .input(lp.one(budget))
            .reset(lp.reset(stamp))
            .output(lp.and_(lp.out(work), lp.out(stamp)))
            .action(lp.fork)
            .build()
        )
        .transition(
            lp.Transition("Step").input(lp.one(work)).output(lp.out(done)).action(lp.fork).build()
        )
        .transition(
            lp.Transition("Close")
            .input(lp.one(done))
            .output(lp.and_(lp.out(budget), lp.out(sink)))
            .action(lp.fork)
            .build()
        )
        .build()
    )
    return work, sink, net


def test_semiflow_invariants_kwarg_adds_the_report_line():
    # VER-007 AC2/AC3: off by default (no report line); on, the minimal laws reach
    # the encoder, the report says how many, and the loop's bound is proven.
    work, _sink, net = _semiflow_loop()
    off = lp.verify(net, lp.place_bound(work, 1), initial_marking={"Budget": 1}, timeout_ms=30_000)
    assert "Semiflows encoded as invariants" not in off.report, off.report

    on = lp.verify(
        net,
        lp.place_bound(work, 1),
        initial_marking={"Budget": 1},
        semiflow_invariants=True,
        timeout_ms=30_000,
    )
    assert on.verdict == "proven", on.report
    assert "  Semiflows encoded as invariants: " in on.report, on.report
    assert any(
        line.startswith("  I") and "Budget" in line and "Work" in line and "Done" in line
        and line.endswith("= 1")
        for line in on.report.splitlines()
    ), on.report


def test_semiflow_invariants_never_hide_a_counterexample():
    # VER-007 AC5: Sink gains one token per loop iteration, so bound 1 is violated.
    _work, sink, net = _semiflow_loop()
    result = lp.verify(
        net,
        lp.place_bound(sink, 1),
        initial_marking={"Budget": 1},
        semiflow_invariants=True,
        timeout_ms=30_000,
    )
    assert result.verdict == "violated", result.report


def test_counterexample_confirmed_is_a_tri_state():
    _p0, p1, net = _conserved_pair()

    # Violated with a replayed chain -> True.
    violated = lp.verify(net, lp.place_bound(p1, 2), initial_marking={"p0": 3}, timeout_ms=15_000)
    assert violated.verdict == "violated", violated.report
    assert violated.counterexample_confirmed is True
    assert violated.counterexample_trace, "a confirmed replay carries the trace"

    # Proven -> the replay never applied.
    proven = lp.verify(net, lp.place_bound(p1, 3), initial_marking={"p0": 3}, timeout_ms=15_000)
    assert proven.verdict == "proven", proven.report
    assert proven.counterexample_confirmed is None

    # Replay disabled -> also "did not apply", and no trace is produced.
    off = lp.verify(
        net,
        lp.place_bound(p1, 2),
        initial_marking={"p0": 3},
        counterexample_replay=False,
        timeout_ms=15_000,
    )
    assert off.verdict == "violated", off.report
    assert off.counterexample_confirmed is None
    assert off.counterexample_trace == []


def _wide_fanout_net(width):
    """One source place drained by `width` competing transitions, one sink each.

    The abstract counterexample replay searches breadth-first, so with S=4 it
    must admit every 3-token distribution over the `width` sinks before it can
    reach the 4-firing violation of ``place_bound(P00, 3)``. At width 48 that
    is C(50, 3) = 19_600 states, comfortably past the replay's 10_000-node
    budget.
    """
    source = lp.Place("S")
    sinks = [lp.Place(f"P{i:02d}") for i in range(width)]
    net = lp.Net("fanout")
    for i, sink in enumerate(sinks):
        net = net.transition(
            lp.Transition(f"t{i:02d}")
            .input(lp.one(source))
            .output(lp.out(sink))
            .action(lp.fork)
            .build()
        )
    return sinks[0], net.build()


def test_counterexample_confirmed_is_false_when_the_replay_exhausts_its_budget():
    # The False arm of the tri-state, mirroring the Rust budget-exhaustion
    # tests through the bindings. False means the replay APPLIED and did not
    # confirm -- here because its search budget ran out, which is an absence
    # of evidence, so the violated verdict stands. That is exactly what
    # separates False from None: None means the replay never ran at all.
    first_sink, net = _wide_fanout_net(48)
    result = lp.verify(
        net, lp.place_bound(first_sink, 3), initial_marking={"S": 4}, timeout_ms=30_000
    )
    assert result.verdict == "violated", result.report
    assert result.counterexample_confirmed is False, result.report
    assert "search node budget" in result.report, result.report


def test_unresolved_property_place_is_refused():
    # A property over a place the net never declares would encode to `false`,
    # which proves anything. Every implementation refuses with the same reason.
    if not lp.z3_available():
        pytest.skip("no usable z3 executable")
    p0 = lp.Place("p0")
    p1 = lp.Place("p1")
    net = (
        lp.Net("tiny")
        .transition(lp.Transition("t").input(lp.one(p0)).output(lp.out(p1)).action(lp.fork).build())
        .build()
    )
    result = lp.verify(net, lp.unreachable([lp.Place("Ghost")]), initial_marking={p0: 1})
    assert result.verdict == "unknown", result.report
    assert "does not resolve in the net ('Ghost')" in result.report
