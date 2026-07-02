"""NU-030 / NU-060: a ν-net join's match must survive modular composition.

Python reaches the Rust rewriter through ``Net.compose`` (port composition).
Before the fix the Rust rewriter dropped ``match_spec`` on the
rename/substitute rebuild, so a ν-net join inside a composed subnet silently
reverted to a plain FIFO AND join — pairing tokens by arrival order instead of
by correlation id (serving stale, cross-group results).

Mirrors the Rust ``nu_match_composition::port_composition_preserves_nu_match``
integration test and the Java/TS channel-merge regressions.
"""

from __future__ import annotations

import libpetri as lp


def test_compose_preserves_nu_match_by_name_not_fifo() -> None:
    a = lp.Place("a")
    b = lp.Place("b")
    merged = lp.Place("merged")

    def join_action(ctx: lp.TransitionContext) -> None:
        # Read via the host-bound names so the test isolates the match survival
        # (MOD-031 local-name resolution is covered in test_subnet_local_names).
        ma = ctx.input("host_a")
        mb = ctx.input("host_b")
        ctx.output("host_merged", f"{ma['cid']}+{mb['cid']}")

    subnet = (
        lp.SubnetDef("MatchedJoin")
        .transition(
            lp.Transition("join")
            .input(lp.one(a))
            .input(lp.one(b))
            .match_spec(lp.match_spec([(a, lambda m: m["cid"]), (b, lambda m: m["cid"])]))
            .output(lp.out(merged))
            .action(join_action)
            .build()
        )
        .input_port("in_a", a)
        .input_port("in_b", b)
        .output_port("out_merged", merged)
        .build()
    )

    host_a = lp.Place("host_a")
    host_b = lp.Place("host_b")
    host_merged = lp.Place("host_merged")

    net = (
        lp.NetBuilder("Host")
        .place(host_a)
        .place(host_b)
        .place(host_merged)
        .compose(
            "j",
            subnet,
            {"in_a": host_a, "in_b": host_b, "out_merged": host_merged},
        )
        .build()
    )

    # Interleaved arrival: a FIFO join would cross-pair (X+Y / Y+X); the
    # surviving ν-match yields the correlated X+X / Y+Y.
    result = lp.run_sync(
        net,
        initial={
            host_a: [{"cid": "X"}, {"cid": "Y"}],
            host_b: [{"cid": "Y"}, {"cid": "X"}],
        },
    )

    vals = sorted(result.tokens(host_merged))
    assert vals == ["X+X", "Y+Y"], f"composed join must correlate by name, got {vals}"
    for v in vals:
        left, right = v.split("+")
        assert left == right  # correlated, not FIFO-paired


def test_bind_actions_after_instantiate_preserves_nu_match_by_name_not_fifo() -> None:
    """NU-030: a ν-net join whose action is bound AFTER instantiate (via
    ``Instance.bind_actions``) must keep correlating by name, not FIFO.

    ``bind_actions`` rebuilds each transition to attach its action; if that
    rebuild dropped ``match_spec`` the join would revert to a plain FIFO AND
    join — pairing tokens by arrival order across generations instead of by
    correlation id. Mirrors the Java ``bindActions_matchedJoin_correlatesByName``
    and TypeScript ``bound matched join still correlates by name`` regressions.
    Python reaches the Rust ``rebuild_with_action`` through the runtime.
    """
    a = lp.Place("a")
    b = lp.Place("b")
    merged = lp.Place("merged")

    def join_action(ctx: lp.TransitionContext) -> None:
        # author-local names, preserved across instantiate + bind (MOD-031)
        ma = ctx.input("a")
        mb = ctx.input("b")
        ctx.output("merged", f"{ma['cid']}+{mb['cid']}")

    # Structure-only join carrying a match; the action is bound post-instantiate.
    subnet = (
        lp.SubnetDef("MatchedJoin")
        .transition(
            lp.Transition("join")
            .input(lp.one(a))
            .input(lp.one(b))
            .match_spec(lp.match_spec([(a, lambda m: m["cid"]), (b, lambda m: m["cid"])]))
            .output(lp.out(merged))
            .build()
        )
        .input_port("in_a", a)
        .input_port("in_b", b)
        .output_port("out_merged", merged)
        .build()
    )

    host_a = lp.Place("host_a")
    host_b = lp.Place("host_b")
    host_merged = lp.Place("host_merged")

    instance = subnet.instantiate("j").bind_actions({"join": join_action})
    net = (
        lp.NetBuilder("Host")
        .place(host_a)
        .place(host_b)
        .place(host_merged)
        .compose_instance(
            instance,
            {"in_a": host_a, "in_b": host_b, "out_merged": host_merged},
        )
        .build()
    )

    # Interleaved arrival: a FIFO join would cross-pair (X+Y / Y+X); the
    # surviving ν-match yields the correlated X+X / Y+Y.
    result = lp.run_sync(
        net,
        initial={
            host_a: [{"cid": "X"}, {"cid": "Y"}],
            host_b: [{"cid": "Y"}, {"cid": "X"}],
        },
    )

    vals = sorted(result.tokens(host_merged))
    assert vals == ["X+X", "Y+Y"], f"bound join must correlate by name, got {vals}"
    for v in vals:
        left, right = v.split("+")
        assert left == right  # correlated, not FIFO-paired
