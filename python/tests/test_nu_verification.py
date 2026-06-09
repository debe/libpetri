"""NU-040 / NU-050: ν-net SMT verification (sound carve-out, Stage 6a).

The untimed encoder over-approximates ν-join name equality. That is sound for
reachability-safety bounds (a ``proven`` holds for the real net) — so the
bounded-budget decidability lever is checkable today — but not for quiescence
properties, and not for unbounded fresh names. The carve-out logic lives in the
Rust verifier; here we exercise it through the Python binding.

Gated on ``lp.HAS_Z3`` — the SMT path requires the wheel built with the ``z3``
feature.
"""

import libpetri as lp
import pytest

pytestmark = pytest.mark.skipif(not lp.HAS_Z3, reason="z3 feature not enabled")


def _nu_scatter_gather_net():
    """Structural scatter-gather. ``fork`` consumes a ``budget`` token and stamps
    a ``pending`` token plus both branches; ``join`` correlates the branches by
    name, consumes ``pending``, and returns the ``budget`` token. The conservation
    laws ``budget + pending = k`` and ``branchA = branchB = pending`` hold
    regardless of names, so the over-approximation can prove the bounds."""
    source = lp.Place("source")
    budget = lp.Place("budget")
    pending = lp.Place("pending")
    a = lp.Place("branchA")
    b = lp.Place("branchB")
    merged = lp.Place("merged")

    fork_t = (
        lp.Transition("fork")
        .input(lp.one(source))
        .input(lp.one(budget))
        .output(lp.and_(a, b, pending))
        .action(lp.fork)
        .build()
    )
    join_t = (
        lp.Transition("join")
        .input(lp.one(a))
        .input(lp.one(b))
        .input(lp.one(pending))
        .match_spec(lp.match_spec([(a, lambda m: m), (b, lambda m: m)]))
        .output(lp.and_(merged, budget))
        .action(lp.fork)
        .build()
    )
    net = (
        lp.Net("nu_scatter_gather_verify")
        .transition(fork_t)
        .transition(join_t)
        .build()
    )
    return net, source, budget, pending


def test_branch_budget_bound_proven_with_declared_budget():
    # NU-040 #1: the live correlation pool is bounded by conservation.
    net, source, budget, _pending = _nu_scatter_gather_net()
    result = lp.verify(
        net,
        lp.branch_place_bound(budget, 2),
        initial_marking={source: 3, budget: 2},
        budget_places=[budget],
        timeout_ms=15_000,
    )
    assert result.verdict == "proven", result.report


def test_pending_bound_proven_exact():
    # NU-040 #2 (bound half): at most k live groups. The scatter-gather is in the
    # name-coloured fragment (Stage 6b / NU-050 #1), so the bound is decided
    # exactly rather than via the name-blind over-approximation.
    net, source, budget, pending = _nu_scatter_gather_net()
    result = lp.verify(
        net,
        lp.branch_place_bound(pending, 2),
        initial_marking={source: 3, budget: 2},
        budget_places=[budget],
        timeout_ms=15_000,
    )
    assert result.verdict == "proven", result.report
    assert "name-coloured" in result.report


def test_unbounded_without_declared_budget_is_unknown():
    # NU-050 #2: an undeclared-budget ν-net is treated as unbounded -> unknown,
    # even for a bound the over-approximation could prove.
    net, source, budget, _pending = _nu_scatter_gather_net()
    result = lp.verify(
        net,
        lp.branch_place_bound(budget, 2),
        initial_marking={source: 3, budget: 2},
        timeout_ms=15_000,
    )
    assert result.verdict == "unknown", result.report
    assert "budget" in result.reason and "unbounded" in result.reason


def test_joined_or_dead_lettered_unknown_on_nu_net():
    # Quiescence-based on a ν-net -> unknown (deferred to the exact ν-analysis).
    net, source, budget, pending = _nu_scatter_gather_net()
    result = lp.verify(
        net,
        lp.joined_or_dead_lettered(pending),
        initial_marking={source: 3, budget: 2},
        budget_places=[budget],
        timeout_ms=15_000,
    )
    assert result.verdict == "unknown", result.report


def test_deadlock_free_unknown_on_nu_net():
    # DeadlockFree is also quiescence-based, and the structural shortcut is gated
    # off for ν-nets -> unknown.
    net, source, budget, _pending = _nu_scatter_gather_net()
    result = lp.verify(
        net,
        lp.deadlock_free(),
        initial_marking={source: 3, budget: 2},
        budget_places=[budget],
        timeout_ms=15_000,
    )
    assert result.verdict == "unknown", result.report


def test_joined_or_dead_lettered_proven_on_non_nu_net():
    # On a net WITHOUT ν-matching the encoding is exact for quiescence. `pending`
    # always drains before quiescence -> proven.
    start = lp.Place("start")
    pending = lp.Place("pending")
    done = lp.Place("done")
    net = (
        lp.Net("pending_drains")
        .transition(lp.Transition("gen").input(lp.one(start)).output(lp.out(pending)).action(lp.fork).build())
        .transition(lp.Transition("fin").input(lp.one(pending)).output(lp.out(done)).action(lp.fork).build())
        .build()
    )
    result = lp.verify(
        net,
        lp.joined_or_dead_lettered(pending),
        initial_marking={start: 1},
        timeout_ms=15_000,
    )
    assert result.verdict == "proven", result.report


def test_joined_or_dead_lettered_violated_on_non_nu_net():
    # A stranded `pending` token: `leak` produces into `pending` but nothing
    # consumes it -> the quiescent marking still holds pending -> violated.
    start = lp.Place("start")
    pending = lp.Place("pending")
    net = (
        lp.Net("pending_strands")
        .transition(lp.Transition("leak").input(lp.one(start)).output(lp.out(pending)).action(lp.fork).build())
        .build()
    )
    result = lp.verify(
        net,
        lp.joined_or_dead_lettered(pending),
        initial_marking={start: 1},
        timeout_ms=15_000,
    )
    assert result.verdict == "violated", result.report
