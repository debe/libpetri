"""ν-net fork/join correlation by ID (spec NU-010, NU-020).

Mirrors Rust ``backend_suite_tests::nu_*``, Java
``AbstractNetExecutorEngineTest.nu*``, and TypeScript
``tests/runtime/nu-net.test.ts``.
"""

from __future__ import annotations

import libpetri as lp


def _correlate_on_cid(a: lp.Place, b: lp.Place) -> lp.MatchSpec:
    return lp.match_spec([(a, lambda m: m["cid"]), (b, lambda m: m["cid"])])


def test_join_matches_by_name_not_fifo() -> None:
    a = lp.Place("branchA")
    b = lp.Place("branchB")
    merged = lp.Place("merged")

    def join_action(ctx: lp.TransitionContext) -> None:
        ma = ctx.input("branchA")
        mb = ctx.input("branchB")
        ctx.output("merged", f"{ma['cid']}+{mb['cid']}")

    net = (
        lp.Net("nu_join")
        .transition(
            lp.Transition("join")
            .input(lp.one(a))
            .input(lp.one(b))
            .match_spec(_correlate_on_cid(a, b))
            .output(lp.out(merged))
            .action(join_action)
            .build()
        )
        .build()
    )

    # Reversed arrival order: a FIFO join would pair X with Y; the name match
    # must instead pair X-X and Y-Y.
    result = lp.run_sync(
        net,
        initial={
            a: [{"cid": "X"}, {"cid": "Y"}],
            b: [{"cid": "Y"}, {"cid": "X"}],
        },
    )

    vals = sorted(result.tokens(merged))
    assert vals == ["X+X", "Y+Y"]
    for v in vals:
        left, right = v.split("+")
        assert left == right  # correlated, not FIFO-paired


def test_join_blocks_without_matching_name() -> None:
    a = lp.Place("branchA")
    b = lp.Place("branchB")
    merged = lp.Place("merged")

    def join_action(ctx: lp.TransitionContext) -> None:
        ctx.output("merged", f"{ctx.input('branchA')['cid']}+{ctx.input('branchB')['cid']}")

    net = (
        lp.Net("nu_block")
        .transition(
            lp.Transition("join")
            .input(lp.one(a))
            .input(lp.one(b))
            .match_spec(_correlate_on_cid(a, b))
            .output(lp.out(merged))
            .action(join_action)
            .build()
        )
        .build()
    )

    result = lp.run_sync(net, initial={a: [{"cid": "X"}], b: [{"cid": "Y"}]})
    assert result.count(merged) == 0
    assert result.count(a) == 1
    assert result.count(b) == 1


def test_fork_mints_unique_ids_then_join_merges() -> None:
    source = lp.Place("source")
    a = lp.Place("branchA")
    b = lp.Place("branchB")
    merged = lp.Place("merged")

    def fork_action(ctx: lp.TransitionContext) -> None:
        cid = ctx.fresh_name()
        ctx.output("branchA", {"cid": cid})
        ctx.output("branchB", {"cid": cid})

    def join_action(ctx: lp.TransitionContext) -> None:
        ma = ctx.input("branchA")
        mb = ctx.input("branchB")
        assert ma["cid"] == mb["cid"], f"join saw mismatched ids: {ma['cid']} vs {mb['cid']}"
        ctx.output("merged", ma["cid"])

    net = (
        lp.Net("nu_scatter_gather")
        .transition(
            lp.Transition("fork")
            .input(lp.one(source))
            .output(lp.and_(a, b))
            .action(fork_action)
            .build()
        )
        .transition(
            lp.Transition("join")
            .input(lp.one(a))
            .input(lp.one(b))
            .match_spec(_correlate_on_cid(a, b))
            .output(lp.out(merged))
            .action(join_action)
            .build()
        )
        .build()
    )

    result = lp.run_sync(net, initial={source: [0, 0, 0]})
    vals = result.tokens(merged)
    assert len(vals) == 3
    assert len(set(vals)) == 3  # fresh_name mints a unique id per fork firing


def test_budget_bounds_concurrency() -> None:
    """NU-040: a bounded ``budget`` place caps live fork groups (the
    decidability lever); the budget token returned by each join lets all work
    still complete -- serialized at k = 1."""
    source = lp.Place("source")
    budget = lp.Place("budget")
    a = lp.Place("branchA")
    b = lp.Place("branchB")
    merged = lp.Place("merged")

    def fork_action(ctx: lp.TransitionContext) -> None:
        cid = ctx.fresh_name()
        ctx.output("branchA", {"cid": cid})
        ctx.output("branchB", {"cid": cid})

    def join_action(ctx: lp.TransitionContext) -> None:
        ma = ctx.input("branchA")
        mb = ctx.input("branchB")
        assert ma["cid"] == mb["cid"]
        ctx.output("merged", ma["cid"])
        ctx.output("budget", 0)

    net = (
        lp.Net("nu_budget")
        .transition(
            lp.Transition("fork")
            .input(lp.one(source))
            .input(lp.one(budget))
            .output(lp.and_(a, b))
            .action(fork_action)
            .build()
        )
        .transition(
            lp.Transition("join")
            .input(lp.one(a))
            .input(lp.one(b))
            .match_spec(_correlate_on_cid(a, b))
            .output(lp.and_(merged, budget))
            .action(join_action)
            .build()
        )
        .build()
    )

    result = lp.run_sync(net, initial={source: [0, 0, 0], budget: [0]})
    assert result.count(merged) == 3  # all complete despite k=1 budget
    assert result.count(budget) == 1  # budget token returned
    assert result.count(source) == 0
