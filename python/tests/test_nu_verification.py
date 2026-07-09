"""NU-040 / NU-050: ν-net verification through the Python binding.

Covers the bounded name-coloured SMT carve-out (NU-050 #1, Route A) and the exact
name-aware state-class-graph name-partition quotient (NU-050, Route B): the latter
decides ν-join correlation exactly beyond the bounded fragment — budget-less
structurally-bounded nets, name×time, and quiescence — returning ``unknown`` only
when the live correlation pool is not structurally bounded (graph truncation). The
analysis logic lives in the Rust verifier; here we exercise it through Python.

Gated on ``lp.HAS_Z3`` — the binding's ``verify_net`` is built behind the ``z3``
feature (Route B itself is solver-free, but the Python entry point is gated with
the rest of the SMT surface).
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


def test_structurally_bounded_without_declared_budget_decided_by_route_b():
    # NU-050 Route B: without a DECLARED budget the SMT/Route-A path returns
    # unknown, but the name-aware SCG name-partition quotient discovers the
    # structural bound (the budget token caps live groups) and proves the bound
    # exactly — the beyond-bounded win.
    net, source, budget, _pending = _nu_scatter_gather_net()
    result = lp.verify(
        net,
        lp.branch_place_bound(budget, 2),
        initial_marking={source: 3, budget: 2},
    )
    assert result.verdict == "proven", result.report
    assert "Route B" in result.report


def test_joined_or_dead_lettered_proven_by_route_b():
    # NU-050 Route B: quiescence on a ν-net is decided exactly by the name-aware
    # SCG. Same-mint siblings always join, so no quiescent state strands `pending`
    # -> proven (the SMT path returned unknown here).
    net, source, budget, pending = _nu_scatter_gather_net()
    result = lp.verify(
        net,
        lp.joined_or_dead_lettered(pending),
        initial_marking={source: 3, budget: 2},
    )
    assert result.verdict == "proven", result.report
    assert "Route B" in result.report


def test_deadlock_free_violated_by_route_b():
    # NU-050 Route B: DeadlockFree is now exact. The net quiesces when `source` is
    # exhausted (budget returned, no group in flight) — a genuine deadlock with no
    # declared sinks -> violated (was unknown).
    net, source, budget, _pending = _nu_scatter_gather_net()
    result = lp.verify(
        net,
        lp.deadlock_free(),
        initial_marking={source: 3, budget: 2},
    )
    assert result.verdict == "violated", result.report
    assert "Route B" in result.report


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


# === NU-050 Route B: exact name-aware SCG name-partition quotient ===


def _nu_distinct_mints_net():
    """Two independent mints feed one join: ``forkA`` mints into ``branchA``,
    ``forkB`` a *different* name into ``branchB``. Their names can never be equal,
    so the join can never correlate them and ``merged`` is unreachable — with NO
    budget place (the beyond-bounded win Route A cannot do)."""
    source_a = lp.Place("sourceA")
    source_b = lp.Place("sourceB")
    a = lp.Place("branchA")
    b = lp.Place("branchB")
    merged = lp.Place("merged")
    fork_a = lp.Transition("forkA").input(lp.one(source_a)).output(lp.out(a)).action(lp.fork).build()
    fork_b = lp.Transition("forkB").input(lp.one(source_b)).output(lp.out(b)).action(lp.fork).build()
    join = (
        lp.Transition("join")
        .input(lp.one(a))
        .input(lp.one(b))
        .match_spec(lp.match_spec([(a, lambda m: m), (b, lambda m: m)]))
        .output(lp.out(merged))
        .action(lp.fork)
        .build()
    )
    net = lp.Net("nu_distinct_mints").transition(fork_a).transition(fork_b).transition(join).build()
    return net, source_a, source_b


def test_distinct_mints_merged_unreachable_proven_no_budget():
    net, source_a, source_b = _nu_distinct_mints_net()
    result = lp.verify(
        net,
        lp.unreachable(["merged"]),
        initial_marking={source_a: 1, source_b: 1},
    )
    assert result.verdict == "proven", result.report
    assert "name-partition quotient" in result.report
    assert "Route B" in result.report


def test_same_mint_merged_reachable_violated():
    # The same-mint scatter-gather stamps both branches with one name, so the join
    # CAN fire and `merged` IS reachable -> Unreachable(merged) violated.
    net, source, _budget, _pending = _nu_scatter_gather_net()
    result = lp.verify(
        net,
        lp.unreachable(["merged"]),
        initial_marking={source: 3, "budget": 2},
    )
    assert result.verdict == "violated", result.report


def test_unbounded_mint_truncates_to_unknown():
    # A self-refilling fork mints a fresh name every firing with no join able to
    # consume it -> the name-aware graph grows without bound -> truncation ->
    # unknown (NU-050 #2 generalised). nu_max_classes bounds the search.
    source = lp.Place("source")
    a = lp.Place("branchA")
    b = lp.Place("branchB")
    merged = lp.Place("merged")
    fork = (
        lp.Transition("fork")
        .input(lp.one(source))
        .output(lp.and_(source, a))
        .action(lp.fork)
        .build()
    )
    join = (
        lp.Transition("join")
        .input(lp.one(a))
        .input(lp.one(b))
        .match_spec(lp.match_spec([(a, lambda m: m), (b, lambda m: m)]))
        .output(lp.out(merged))
        .action(lp.fork)
        .build()
    )
    net = lp.Net("nu_unbounded_mint").transition(fork).transition(join).build()
    result = lp.verify(
        net,
        lp.unreachable(["merged"]),
        initial_marking={source: 1},
        nu_max_classes=40,
    )
    assert result.verdict == "unknown", result.report
    assert "truncated" in result.reason


# === NU-051: EXTENDED coloured-consumer fragment (drain/relay + carrier co-mint) ===
# The name-aware SCG decides DeadlockFree exactly, so these route through Route B
# without ever touching the z3 binary. They are still gated on HAS_Z3 (the module
# marker) because the verify_net entry point is built behind the z3 feature.


def _comint_carrier_drain_net(with_drain):
    """A ``fork`` co-mints one fresh name into ``branchA``, ``branchB``, and the
    declared carrier ``stray``; the ``join`` correlates the branches into
    ``merged`` (a sink), leaving ``stray``; the optional ``drain`` dead-letters
    the leftover ``stray`` into ``deadletter`` (a sink). Without the drain,
    ``stray`` is stranded at quiescence, a genuine stall."""
    source = lp.Place("source")
    a = lp.Place("branchA")
    b = lp.Place("branchB")
    stray = lp.Place("stray")
    merged = lp.Place("merged")
    dl = lp.Place("deadletter")

    fork_t = (
        lp.Transition("fork")
        .input(lp.one(source))
        .output(lp.and_(a, b, stray))
        .action(lp.fork)
        .build()
    )
    join_t = (
        lp.Transition("join")
        .input(lp.one(a))
        .input(lp.one(b))
        .match_spec(lp.match_spec([(a, lambda s: s), (b, lambda s: s)]))
        .output(lp.out(merged))
        .action(lp.fork)
        .build()
    )
    net = lp.Net("comint_carrier_drain").transition(fork_t).transition(join_t)
    if with_drain:
        drain_t = (
            lp.Transition("drain")
            .input(lp.one(stray))
            .output(lp.out(dl))
            .action(lp.fork)
            .build()
        )
        net = net.transition(drain_t)
    return net.build()


def test_extended_deadlock_free_proven_with_drain_via_route_b():
    # With the drain, the only quiescent marking is {merged, deadletter}, both
    # declared sinks -> no stall -> proven. Decided by Route B EXTENDED.
    net = _comint_carrier_drain_net(with_drain=True)
    result = lp.verify(
        net,
        lp.deadlock_free(),
        initial_marking={"source": 1},
        sink_places=["merged", "deadletter"],
        fragment_mode="extended",
        carrier_places=["stray"],
    )
    assert result.verdict == "proven", result.report
    # The verdict must come from Route B (name-partition quotient), not a
    # silently name-blind SMT fall-back.
    assert "Route B" in result.report, result.report


def test_extended_deadlock_free_violated_without_drain_via_route_b():
    # Remove the drain: after the join, `stray` is stranded at quiescence
    # ({merged, stray}, and `stray` is not a sink) -> a genuine stall -> violated.
    net = _comint_carrier_drain_net(with_drain=False)
    result = lp.verify(
        net,
        lp.deadlock_free(),
        initial_marking={"source": 1},
        sink_places=["merged", "deadletter"],
        fragment_mode="extended",
        carrier_places=["stray"],
    )
    assert result.verdict == "violated", result.report
    assert "Route B" in result.report, result.report


def test_extended_unknown_on_unknown_carrier_place():
    # A mistyped carrier name must surface as unknown naming the place, never a
    # silent fall-back to a confident (possibly false) verdict.
    net = _comint_carrier_drain_net(with_drain=True)
    result = lp.verify(
        net,
        lp.deadlock_free(),
        initial_marking={"source": 1},
        sink_places=["merged", "deadletter"],
        fragment_mode="extended",
        carrier_places=["nonExistent"],
    )
    assert result.verdict == "unknown", result.report
    assert "nonExistent" in (result.reason or ""), result.report
