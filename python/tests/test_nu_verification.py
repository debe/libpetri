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

# ``lp.HAS_Z3`` is the compile feature; the Route A coloured quiescence path
# (NU-053) shells out to the ``z3`` executable, which is separate
# (``lp.z3_available()``, VER-013). Skip the binary-driven nu053_* tests when it
# is absent so they cleanly SKIP (not fail), matching the Rust/Java clean-skip.
_HAS_Z3_BINARY = lp.z3_available()
_needs_z3_binary = pytest.mark.skipif(
    not _HAS_Z3_BINARY, reason="no usable z3 executable (Route A coloured encoder)"
)


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


def test_zero_budget_quiescence_decided_by_zero_slot_plan():
    # NU-053 AC6: a mid-phase marking with no budget token (the covering semiflow's
    # initial sum is zero) is decided exactly by the zero-slot coloured plan instead of
    # being downgraded to unknown. Route B is forced to truncate (nu_max_classes=1) so
    # the deferral to Route A is exercised. No sink: the initial marking is quiescent
    # with `source` tokens stranded.
    net, source, budget, _pending = _nu_scatter_gather_net()
    violated = lp.verify(
        net,
        lp.deadlock_free(),
        initial_marking={source: 3, budget: 0},
        budget_places=[budget],
        nu_max_classes=1,
        timeout_ms=15_000,
    )
    assert "exact within budget k=0" in violated.report, violated.report
    assert violated.verdict == "violated", violated.report
    # Declaring `source` a sink makes that marking a legitimate end state.
    proven = lp.verify(
        net,
        lp.deadlock_free(),
        initial_marking={source: 3, budget: 0},
        budget_places=[budget],
        sink_places=[source],
        nu_max_classes=1,
        timeout_ms=15_000,
    )
    assert "exact within budget k=0" in proven.report, proven.report
    assert proven.verdict == "proven", proven.report


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


def test_extended_leaky_carrier_never_falsely_proven():
    # [NU-053] S2 regression: the fork co-mints one colour into branchA, branchB AND the
    # carrier `stray`, but the join only re-collects branchA, branchB. Without the drain,
    # `stray` is a genuine stall, so the verifier must never answer `proven`. The
    # colour-flow gate rejects the leaky coloured plan (a mint fan-out no single join
    # re-collects), so the query stays sound rather than certifying a false PROVEN.
    net = _comint_carrier_drain_net(with_drain=False)
    result = lp.verify(
        net,
        lp.deadlock_free(),
        initial_marking={"source": 1},
        sink_places=["merged", "deadletter"],
        fragment_mode="extended",
        carrier_places=["stray"],
    )
    assert result.verdict != "proven", result.report


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


# === NU-052: conflict-only priority (priority_semantics="none"/"conflict") ===
# Mirrors the Rust nu_scg_verifier priority tests. A ν-join and a timed
# dead-letter-drain conflict on a coloured place; the priority-blind graph
# (NONE, the default) reports a spurious stall the eager, priority-ordered
# executor can never produce, while CONFLICT prunes exactly that interleaving.


def _nu_priority_conflict_net(co_mint_both=True, with_drain=True):
    """Marvin guard-join vs. timed dead-letter-drain conflict, minimal.

    ``MINT`` co-mints one fresh name into ``COL_A`` (and ``COL_B`` when
    ``co_mint_both``); an immediate, default-priority ν-``JOIN`` correlates the
    branches into ``OUT``; a delayed, lower-priority (-10) ``DRAIN_A``
    dead-letters ``COL_A`` into ``DEADLETTER``. ``DRAIN_A`` and ``JOIN`` conflict
    on the consumed ``COL_A``."""
    seed = lp.Place("SEED")
    a = lp.Place("COL_A")
    b = lp.Place("COL_B")
    out = lp.Place("OUT")
    dl = lp.Place("DEADLETTER")

    mint = (
        lp.Transition("MINT")
        .input(lp.one(seed))
        .output(lp.and_(a, b) if co_mint_both else lp.out(a))
        .action(lp.fork)
        .build()
    )
    join = (  # immediate, default priority 0
        lp.Transition("JOIN")
        .input(lp.one(a))
        .input(lp.one(b))
        .match_spec(lp.match_spec([(a, lambda s: s), (b, lambda s: s)]))
        .output(lp.out(out))
        .action(lp.fork)
        .build()
    )
    net = lp.Net("nu_priority_conflict").transition(mint).transition(join)
    if with_drain:
        drain = (  # delayed, lower priority, conflicts on COL_A
            lp.Transition("DRAIN_A")
            .input(lp.one(a))
            .timing(lp.delayed(5_000))
            .priority(-10)
            .output(lp.out(dl))
            .action(lp.fork)
            .build()
        )
        net = net.transition(drain)
    return net.build()


def _verify_priority(net, priority_semantics):
    # EXTENDED DeadlockFree with OUT and DEADLETTER as sinks.
    return lp.verify(
        net,
        lp.deadlock_free(),
        initial_marking={"SEED": 1},
        sink_places=["OUT", "DEADLETTER"],
        fragment_mode="extended",
        priority_semantics=priority_semantics,
    )


def test_priority_none_default_reports_spurious_stall():
    # Default priority_semantics (== "none"): the priority/timing-blind graph
    # explores DRAIN_A stealing the matched COL_A, stranding COL_B -> spurious
    # stall -> violated.
    result = lp.verify(
        _nu_priority_conflict_net(),
        lp.deadlock_free(),
        initial_marking={"SEED": 1},
        sink_places=["OUT", "DEADLETTER"],
        fragment_mode="extended",
    )
    assert result.verdict == "violated", result.report
    assert "Route B" in result.report, result.report


def test_priority_none_explicit_reports_spurious_stall():
    result = _verify_priority(_nu_priority_conflict_net(), "none")
    assert result.verdict == "violated", result.report
    assert "Route B" in result.report, result.report


def test_priority_conflict_proves_no_stall():
    # CONFLICT: the immediate, higher-priority JOIN pre-empts the delayed drain,
    # so COL_A is never stolen from a live join -> the only quiescent marking is
    # {OUT}, a declared sink -> proven.
    result = _verify_priority(_nu_priority_conflict_net(), "conflict")
    assert result.verdict == "proven", result.report
    assert "Route B" in result.report, result.report


def test_priority_conflict_int_form_proves_no_stall():
    # The int form (1 == "conflict") threads through identically.
    result = _verify_priority(_nu_priority_conflict_net(), 1)
    assert result.verdict == "proven", result.report


def test_priority_conflict_still_finds_genuine_stall():
    # A real orphan: MINT mints only COL_A (no COL_B) and there is no drain, so
    # JOIN can never fire and COL_A strands. CONFLICT must NOT hide it — JOIN is
    # name-disabled, so nothing is pruned -> violated.
    net = _nu_priority_conflict_net(co_mint_both=False, with_drain=False)
    result = _verify_priority(net, "conflict")
    assert result.verdict == "violated", result.report


def test_priority_conflict_lets_drain_clear_a_real_orphan():
    # A real orphan that IS drainable: MINT mints only COL_A (no COL_B) and a
    # lower-priority DRAIN_A exists. JOIN is name-disabled (never gets COL_B's
    # name), so willFire(JOIN) is false and CONFLICT must NOT prune the drain —
    # it dead-letters COL_A into the DEADLETTER sink, so the net is deadlock-free.
    # This pins the over-prune guard from the safe direction (NU-052 case 4);
    # mirrors Rust conflict_priority_lets_drain_clear_a_real_orphan.
    net = _nu_priority_conflict_net(co_mint_both=False, with_drain=True)
    result = _verify_priority(net, "conflict")
    assert result.verdict == "proven", result.report


def test_priority_semantics_rejects_bad_value():
    with pytest.raises(ValueError):
        _verify_priority(_nu_priority_conflict_net(), "bogus")


# === NU-053: Route A coloured quiescence (EXTENDED + deadlock encoding) ===
# Mirrors the Rust nu053_* tests in smt_verifier.rs. When the name-aware SCG
# (Route B) is truncated (nu_max_classes=1), the bounded quiescence proof defers
# to the Route A coloured IC3/PDR encoder — which decides ν deadlock-freedom
# scalably. These exercise the real z3 binary (the coloured SMT path).


def _nu053_no_stall_net():
    """Single-turn co-mint→join net. ``fork`` consumes ``source`` + ``budget`` and
    co-mints one fresh name into join inputs ``a`` and ``b``; ``join`` correlates
    them by name into ``merged`` and refunds ``budget``. The only quiescent marking
    holds just the sinks {merged, budget}, so the net is deadlock-free."""
    source = lp.Place("source")
    budget = lp.Place("budget")
    a = lp.Place("a")
    b = lp.Place("b")
    merged = lp.Place("merged")

    fork_t = (
        lp.Transition("fork")
        .input(lp.one(source))
        .input(lp.one(budget))
        .output(lp.and_(a, b))
        .action(lp.fork)
        .build()
    )
    join_t = (
        lp.Transition("join")
        .input(lp.one(a))
        .input(lp.one(b))
        .match_spec(lp.match_spec([(a, lambda s: s), (b, lambda s: s)]))
        .output(lp.and_(merged, budget))
        .action(lp.fork)
        .build()
    )
    return lp.Net("nu053_no_stall").transition(fork_t).transition(join_t).build()


def _nu053_steal_net():
    """The no-stall net plus an EXTENDED ``drain`` that steals ``a`` into a
    dead-letter, stranding ``b``. An unprioritised schedule can reach a quiescent
    marking where the non-sink ``b`` still holds a token, so it is NOT
    deadlock-free."""
    source = lp.Place("source")
    budget = lp.Place("budget")
    a = lp.Place("a")
    b = lp.Place("b")
    merged = lp.Place("merged")
    dl = lp.Place("deadletter")

    fork_t = (
        lp.Transition("fork")
        .input(lp.one(source))
        .input(lp.one(budget))
        .output(lp.and_(a, b))
        .action(lp.fork)
        .build()
    )
    join_t = (
        lp.Transition("join")
        .input(lp.one(a))
        .input(lp.one(b))
        .match_spec(lp.match_spec([(a, lambda s: s), (b, lambda s: s)]))
        .output(lp.and_(merged, budget))
        .action(lp.fork)
        .build()
    )
    drain_t = (
        lp.Transition("drain")
        .input(lp.one(a))
        .output(lp.out(dl))
        .action(lp.fork)
        .build()
    )
    return (
        lp.Net("nu053_steal")
        .transition(fork_t)
        .transition(join_t)
        .transition(drain_t)
        .build()
    )


_NU053_SEED = {"source": 1, "budget": 1}


@_needs_z3_binary
def test_nu053_route_a_proves_deadlock_free_when_route_b_truncates():
    # nu_max_classes=1 forces Route B to truncate, so the bounded quiescence proof
    # defers to the Route A coloured IC3/PDR encoder ([NU-053]). The single-turn
    # co-mint→join net quiesces only at {merged, budget}, both declared sinks ->
    # proven.
    result = lp.verify(
        _nu053_no_stall_net(),
        lp.deadlock_free(),
        initial_marking=_NU053_SEED,
        sink_places=["merged", "budget"],
        budget_places=["budget"],
        nu_max_classes=1,
        timeout_ms=15_000,
    )
    assert result.verdict == "proven", result.report
    # The proof must defer to the Route A coloured encoder, not a name-blind
    # fall-back: the deferral note names Route A and NU-053, and the coloured
    # IC3/PDR method drives it.
    assert "Route A" in result.report, result.report
    assert "NU-053" in result.report, result.report
    assert result.method == "IC3/PDR", result.report


@_needs_z3_binary
def test_nu053_route_a_detects_stranding_deadlock():
    # The EXTENDED drain can steal `a` and strand `b` under an unprioritised
    # schedule — a genuine reachable deadlock the coloured encoding must catch.
    # Sinks are {merged, budget} only: under VER-002 a quiescent marking is
    # excused as soon as ANY declared sink holds a token, so declaring
    # `deadletter` a sink would excuse the stranded-`b` marking (which also
    # holds the dead-lettered token) and hide the stall.
    result = lp.verify(
        _nu053_steal_net(),
        lp.deadlock_free(),
        initial_marking=_NU053_SEED,
        sink_places=["merged", "budget"],
        budget_places=["budget"],
        fragment_mode="extended",
        nu_max_classes=1,
        timeout_ms=15_000,
    )
    assert result.verdict == "violated", result.report
    # Reached via the Route A coloured encoder (Route B truncated at k=1).
    assert "Route A" in result.report, result.report
    assert "NU-053" in result.report, result.report


@_needs_z3_binary
def test_nu053_route_a_agrees_with_route_b_on_no_stall():
    # Differential: Route B (exact SCG, default class bound) and Route A (forced via
    # a tiny class bound) must agree that the co-mint→join net is deadlock-free.
    def _run(max_classes):
        return lp.verify(
            _nu053_no_stall_net(),
            lp.deadlock_free(),
            initial_marking=_NU053_SEED,
            sink_places=["merged", "budget"],
            budget_places=["budget"],
            nu_max_classes=max_classes,
            timeout_ms=15_000,
        )

    route_b = _run(100_000)
    route_a = _run(1)
    assert route_b.verdict == "proven", route_b.report
    assert "Route B" in route_b.report, route_b.report
    assert route_a.verdict == "proven", route_a.report
    assert "Route A" in route_a.report, route_a.report
