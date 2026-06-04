"""MOD-031: action callbacks resolve author-local place names after compose.

These are the Python conformance tests for **MOD-031** (Action Place
Resolution under Composition, ``spec/11-modular-composition.md``). The Rust
core builds the per-transition declared→actual correspondence
(``Transition::local_name_map``) and the pyo3 action adapter applies it, so a
SubnetDef whose Python action calls ``ctx.input("local")`` keeps working after
its arcs are rewritten by instantiation / port binding.

Before 2.8.0, such an action broke after composition because the runtime
exposed the host-bound place name (``ctx.input("host_in")``) instead of the
local one the action's source code hard-coded. 2.8.0 attaches the local→composed
map to each substituted transition and falls back through it on lookups, so both
the *local* and the *host* names work.
"""

from __future__ import annotations

import pytest

import libpetri as lp


def test_compose_with_action_using_local_names() -> None:
    """The canonical V1 case: a subnet declares ``LOCAL_IN`` / ``LOCAL_OUT``
    as port places; its action calls ``ctx.input("LOCAL_IN")``,
    ``ctx.output("LOCAL_OUT", ...)``. After binding to host places, the
    action runs unchanged."""

    local_in = lp.Place("LOCAL_IN")
    local_out = lp.Place("LOCAL_OUT")

    def transform(ctx: lp.TransitionContext) -> None:
        msg = ctx.input("LOCAL_IN")  # author-local name
        ctx.output("LOCAL_OUT", {**msg, "tag": "processed"})

    subnet = (
        lp.SubnetDef("Transformer")
        .transition(
            lp.Transition("transform")
            .input(lp.one(local_in))
            .output(lp.out(local_out))
            .action(transform)
            .build()
        )
        .input_port("inbox", local_in)
        .output_port("outbox", local_out)
        .build()
    )

    host_in = lp.Place("host_in")
    host_out = lp.Place("host_out")

    net = (
        lp.NetBuilder("Host")
        .place(host_in)
        .place(host_out)
        .compose(
            "inst1",
            subnet,
            {"inbox": host_in, "outbox": host_out},
        )
        .build()
    )

    result = lp.run_sync(net, initial={host_in: [{"v": 1}]})
    assert result.count(host_out) == 1
    assert result.first(host_out) == {"v": 1, "tag": "processed"}


def test_host_name_still_works_after_compose() -> None:
    """The host name is also a valid lookup key — actions written with
    knowledge of the host wiring still work."""

    local_in = lp.Place("L_IN")
    local_out = lp.Place("L_OUT")

    def transform(ctx: lp.TransitionContext) -> None:
        # Use the *host* name directly. This is what users wrote pre-2.8
        # when they flattened manually.
        msg = ctx.input("host_in")
        ctx.output("host_out", msg)

    subnet = (
        lp.SubnetDef("Pass")
        .transition(
            lp.Transition("t")
            .input(lp.one(local_in))
            .output(lp.out(local_out))
            .action(transform)
            .build()
        )
        .input_port("in", local_in)
        .output_port("out", local_out)
        .build()
    )

    host_in = lp.Place("host_in")
    host_out = lp.Place("host_out")
    net = (
        lp.NetBuilder("Host")
        .place(host_in)
        .place(host_out)
        .compose("a", subnet, {"in": host_in, "out": host_out})
        .build()
    )

    result = lp.run_sync(net, initial={host_in: [{"v": 42}]})
    assert result.first(host_out) == {"v": 42}


def test_two_instances_get_independent_remaps() -> None:
    """Composing the same subnet twice with different port bindings
    must not cross-contaminate the local→host maps."""

    local_in = lp.Place("L_IN")
    local_out = lp.Place("L_OUT")

    def emit(ctx: lp.TransitionContext) -> None:
        msg = ctx.input("L_IN")
        ctx.output("L_OUT", {**msg, "id": ctx.transition_name})

    subnet = (
        lp.SubnetDef("Emitter")
        .transition(
            lp.Transition("emit")
            .input(lp.one(local_in))
            .output(lp.out(local_out))
            .action(emit)
            .build()
        )
        .input_port("in", local_in)
        .output_port("out", local_out)
        .build()
    )

    in_a = lp.Place("in_a")
    in_b = lp.Place("in_b")
    out_a = lp.Place("out_a")
    out_b = lp.Place("out_b")

    net = (
        lp.NetBuilder("TwoEmitters")
        .place(in_a)
        .place(in_b)
        .place(out_a)
        .place(out_b)
        .compose("a", subnet, {"in": in_a, "out": out_a})
        .compose("b", subnet, {"in": in_b, "out": out_b})
        .build()
    )

    result = lp.run_sync(net, initial={in_a: [{"v": 1}], in_b: [{"v": 2}]})
    assert result.count(out_a) == 1
    assert result.count(out_b) == 1
    assert result.first(out_a) == {"v": 1, "id": "a/emit"}
    assert result.first(out_b) == {"v": 2, "id": "b/emit"}


def test_internal_subnet_place_resolves_via_prefix() -> None:
    """Internal subnet places (not bound as ports) get a ``prefix/name``
    name after compose. The action's hard-coded internal-name lookup
    should also fall back through the local-name map."""

    port_in = lp.Place("PORT_IN")
    internal = lp.Place("INTERNAL")
    port_out = lp.Place("PORT_OUT")

    def stage1(ctx: lp.TransitionContext) -> None:
        msg = ctx.input("PORT_IN")
        ctx.output("INTERNAL", msg)

    def stage2(ctx: lp.TransitionContext) -> None:
        # Author-local name for an internal (non-port) place.
        msg = ctx.input("INTERNAL")
        ctx.output("PORT_OUT", {**msg, "stage2": True})

    subnet = (
        lp.SubnetDef("TwoStage")
        .place(internal)
        .transition(
            lp.Transition("s1")
            .input(lp.one(port_in))
            .output(lp.out(internal))
            .action(stage1)
            .build()
        )
        .transition(
            lp.Transition("s2")
            .input(lp.one(internal))
            .output(lp.out(port_out))
            .action(stage2)
            .build()
        )
        .input_port("inbox", port_in)
        .output_port("outbox", port_out)
        .build()
    )

    host_in = lp.Place("host_in")
    host_out = lp.Place("host_out")
    net = (
        lp.NetBuilder("Host")
        .place(host_in)
        .place(host_out)
        .compose("two", subnet, {"inbox": host_in, "outbox": host_out})
        .build()
    )

    result = lp.run_sync(net, initial={host_in: [{"v": 1}]})
    assert result.count(host_out) == 1
    assert result.first(host_out) == {"v": 1, "stage2": True}


def test_compose_xor_branch_selection_by_local_name() -> None:
    """MOD-031 AC#2: an action selects an ``xor`` output branch by its
    author-local declared name. After port binding, the token lands on exactly
    the bound ``a`` place, the unselected branch stays empty, and the
    exactly-one-production validator passes."""

    in_decl = lp.Place("IN_DECL")
    a_decl = lp.Place("A_DECL")
    b_decl = lp.Place("B_DECL")

    def branch(ctx: lp.TransitionContext) -> None:
        msg = ctx.input("IN_DECL")  # author-local name
        ctx.output("A_DECL", {**msg, "via": "a"})  # pick the 'a' branch

    subnet = (
        lp.SubnetDef("Router")
        .transition(
            lp.Transition("route")
            .input(lp.one(in_decl))
            .output(lp.xor(lp.out(a_decl), lp.out(b_decl)))
            .action(branch)
            .build()
        )
        .input_port("in", in_decl)
        .output_port("a", a_decl)
        .output_port("b", b_decl)
        .build()
    )

    host_in = lp.Place("host_in")
    host_a = lp.Place("host_a")
    host_b = lp.Place("host_b")
    net = (
        lp.NetBuilder("Host")
        .place(host_in)
        .place(host_a)
        .place(host_b)
        .compose("r", subnet, {"in": host_in, "a": host_a, "b": host_b})
        .build()
    )

    result = lp.run_sync(net, initial={host_in: [{"v": 1}]})
    assert result.count(host_a) == 1
    assert result.count(host_b) == 0
    assert result.first(host_a) == {"v": 1, "via": "a"}


def test_unknown_place_still_raises_after_compose() -> None:
    """The fallback only resolves the local→host map; lookups for truly
    unknown places still raise ``ValueError``."""

    local_in = lp.Place("L_IN")
    local_out = lp.Place("L_OUT")

    captured: dict[str, str] = {}

    def bad(ctx: lp.TransitionContext) -> None:
        try:
            ctx.input("never_declared")
        except ValueError as exc:
            captured["err"] = str(exc)
        msg = ctx.input("L_IN")
        ctx.output("L_OUT", msg)

    subnet = (
        lp.SubnetDef("Bad")
        .transition(
            lp.Transition("t")
            .input(lp.one(local_in))
            .output(lp.out(local_out))
            .action(bad)
            .build()
        )
        .input_port("in", local_in)
        .output_port("out", local_out)
        .build()
    )

    host_in = lp.Place("host_in")
    host_out = lp.Place("host_out")
    net = (
        lp.NetBuilder("Host")
        .place(host_in)
        .place(host_out)
        .compose("x", subnet, {"in": host_in, "out": host_out})
        .build()
    )
    lp.run_sync(net, initial={host_in: [{"v": 1}]})
    assert "never_declared" in captured["err"]
