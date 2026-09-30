"""Deadline reaping in the verifier's quiescence (VER-002, VER-004, TIME-013).

A ``deadline`` / ``window`` transition a late executor reaps keeps its input tokens
and is not re-enabled until one of its input places changes, so the executor can
rest at a marking the untimed net still enables. Lean:
``Libpetri/Novel/ReapingVsUntimed.lean``, ``reaping_refutes_ver004_ac3``, whose
witness is ``_witness()`` below. Mirrors ``rust/libpetri-verification/tests/reaping.rs``.
"""

from __future__ import annotations

import libpetri as lp
import pytest

pytestmark = [
    pytest.mark.skipif(not lp.HAS_Z3, reason="z3 feature not enabled"),
    pytest.mark.skipif(not lp.z3_available(), reason="no usable z3 executable"),
]


def _arc(name: str, src: lp.Place, dst: lp.Place, timing=None):
    t = lp.Transition(name).input(lp.one(src)).output(lp.out(dst))
    if timing is not None:
        t = t.timing(timing)
    return t.action(lp.fork).build()


def _witness():
    p0, p1 = lp.Place("p0"), lp.Place("p1")
    return lp.Net("reaping-witness").transition(_arc("t", p0, p1, lp.window(3, 5))).build()


def _verify(net, prop, **kw):
    return lp.verify(
        net,
        prop,
        initial_marking={"p0": 1},
        sink_places=["p1"],
        timeout_ms=30_000,
        **kw,
    )


def test_the_witness_rests_at_its_initial_marking():
    result = _verify(_witness(), lp.deadlock_free())
    assert result.verdict == "violated", result.report
    # The initial marking itself violates: the empty trace (VER-003 AC8).
    assert result.counterexample_transitions == [], result.report
    assert result.counterexample_trace and dict(result.counterexample_trace[0]) == {"p0": 1}, result.report
    assert "Reaping (TIME-013): t can be reaped" in result.report


def test_assume_no_reaping_restores_the_strict_verdict():
    result = _verify(_witness(), lp.deadlock_free(), assume_no_reaping=True)
    assert result.verdict == "proven", result.report
    assert "ASSUMPTION: no transition is reaped (the assume-no-reaping option)" in result.report


def test_the_fixpoint_query_alone_finds_the_reaped_rest():
    result = _verify(
        _witness(),
        lp.deadlock_free(),
        state_equation_phase=False,
        firing_bound=False,
    )
    assert result.verdict == "violated", result.report
    assert result.counterexample_transitions == [], result.report


def test_a_shadowed_reapable_transition_changes_nothing():
    p0, p1 = lp.Place("p0"), lp.Place("p1")
    net = (
        lp.Net("shadowed")
        .transition(_arc("t", p0, p1, lp.window(3, 5)))
        .transition(_arc("u", p0, p1))
        .build()
    )
    result = _verify(net, lp.deadlock_free())
    assert result.verdict == "proven", result.report


def test_the_quiescence_clause_skips_the_reapable_transition():
    def horn(no_reaping: bool) -> str:
        return lp.encode_smt_scripts(
            _witness(),
            lp.deadlock_free(),
            initial_marking={"p0": 1},
            sink_places=["p1"],
            assume_no_reaping=no_reaping,
        )["horn"]

    assert "(< m0 1)" in horn(True)
    assert "(< m0 1)" not in horn(False)


def test_open_net_reads_a_reaped_relay_as_resting():
    q, out = lp.Place("q"), lp.Place("out")
    net = lp.Net("reaped-relay").transition(_arc("relay", q, out, lp.window(3, 5))).build()
    contract = lp.OpenNetContract.builder().arrive(1, "q").expect("out", 1, "out").build()
    result = lp.verify_open_net(net, contract)
    assert result.verdict == "violated", result.report
    strict = lp.verify_open_net(net, contract, assume_no_reaping=True)
    assert strict.verdict == "proven", strict.report


# ==================== lateness on Route B (TIME-006, TIME-013) ====================


def _late_race(early):
    """``t1: p -> a`` at ``early``, ``t2: p -> b`` at ``delayed(10)``, beside a
    same-mint join so the query runs on Route B. On time ``t1`` always wins; a late
    executor reaps a deadline / window ``t1`` or fires an exact one after ``t2``.
    Lean: ``TimedScg/Retrodict.reaping_escapes_timed_graph``."""
    p, a, b = lp.Place("p"), lp.Place("a"), lp.Place("b")
    source = lp.Place("source")
    ba, bb, merged = lp.Place("branchA"), lp.Place("branchB"), lp.Place("merged")
    fork_t = lp.Transition("fork").input(lp.one(source)).output(lp.and_(ba, bb)).action(lp.fork).build()
    join_t = (
        lp.Transition("join")
        .input(lp.one(ba))
        .input(lp.one(bb))
        .match_spec(lp.match_spec([(ba, lambda m: m), (bb, lambda m: m)]))
        .output(lp.out(merged))
        .action(lp.fork)
        .build()
    )
    return (
        lp.Net("late-race")
        .transition(_arc("t1", p, a, early))
        .transition(_arc("t2", p, b, lp.delayed(10)))
        .transition(fork_t)
        .transition(join_t)
        .build()
    )


def _verify_late_race(early, assume_no_reaping):
    return lp.verify(
        _late_race(early),
        lp.unreachable(["b"]),
        initial_marking={"p": 1, "source": 1},
        mint_transitions=["fork"],
        assume_no_reaping=assume_no_reaping,
        timeout_ms=30_000,
    )


@pytest.mark.parametrize("early", [lp.deadline(5), lp.window(3, 5), lp.exact(5)])
def test_route_b_marking_properties_see_a_late_executor(early):
    late = _verify_late_race(early, False)
    assert late.route == "nu-scg", late.report
    assert late.verdict == "violated", late.report
    assert late.counterexample_transitions[-1] == "t2", late.report
    assert "latest bound of t1 was lifted" in late.report
    on_time = _verify_late_race(early, True)
    assert on_time.verdict == "proven", on_time.report
    assert "on-time executor" in on_time.report


def test_the_timed_check_names_its_assumptions():
    p, a, b = lp.Place("p"), lp.Place("a"), lp.Place("b")
    net = (
        lp.Net("race")
        .transition(_arc("t1", p, a, lp.window(3, 5)))
        .transition(_arc("t2", p, b, lp.delayed(10)))
        .build()
    )
    result = lp.verify(
        net,
        lp.unreachable(["b"]),
        initial_marking={"p": 1},
        timed_counterexample_check=True,
        timeout_ms=30_000,
    )
    assert result.verdict == "violated", result.report
    assert "assumes an on-time executor with atomic firings" in result.report


_MAX_DURATION_MS = 365 * 100 * 24 * 60 * 60 * 1000


@pytest.mark.parametrize(
    "make",
    [
        lambda: lp.delayed(_MAX_DURATION_MS + 1),
        lambda: lp.window(_MAX_DURATION_MS + 1, _MAX_DURATION_MS + 2),
        lambda: lp.exact(_MAX_DURATION_MS + 1),
    ],
)
def test_an_earliest_bound_past_the_open_end_is_rejected(make):
    # [after, MAX_DURATION_MS] would be empty (TIME-001); construction raises
    # ValueError, as for the other invalid bounds.
    with pytest.raises(ValueError, match="at most MAX_DURATION_MS"):
        make()


@pytest.mark.parametrize(
    "make, message",
    [
        (lambda: lp.window(5, 3), r"Latest \(3\) must be >= earliest \(5\)"),
        (lambda: lp.deadline(0), "Deadline must be positive: 0"),
        (lambda: lp.timeout(0, lp.Place("late")), "Timeout must be positive: 0"),
    ],
)
def test_an_invalid_bound_raises_value_error(make, message):
    # The Rust factories assert their arguments; the binding turns the panic into a
    # ValueError (it used to surface as pyo3's PanicException, a BaseException).
    with pytest.raises(ValueError, match=message):
        make()
