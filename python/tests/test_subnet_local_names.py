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


def test_bind_actions_after_instantiate_preserves_local_names() -> None:
    """MOD-031 ∩ CORE-042: a *structure-only* subnet whose action is bound
    AFTER instantiate (via ``Instance.bind_actions``) keeps resolving its
    author-local place names after composition.

    The instantiate-time declared→actual correspondence must survive the action
    swap — before the fix, ``bind_actions`` dropped it and ``ctx.input("LOCAL_IN")``
    failed once the arcs were rewritten to the host places."""

    local_in = lp.Place("LOCAL_IN")
    local_out = lp.Place("LOCAL_OUT")

    def transform(ctx: lp.TransitionContext) -> None:
        msg = ctx.input("LOCAL_IN")  # author-local name, not the host name
        ctx.output("LOCAL_OUT", {**msg, "tag": "processed"})

    # Structure-only def — no action baked into the transition (CORE-042).
    subnet = (
        lp.SubnetDef("Transformer")
        .transition(
            lp.Transition("transform")
            .input(lp.one(local_in))
            .output(lp.out(local_out))
            .build()
        )
        .input_port("inbox", local_in)
        .output_port("outbox", local_out)
        .build()
    )

    host_in = lp.Place("host_in")
    host_out = lp.Place("host_out")

    # Bind the action AFTER instantiate, then compose the bound instance.
    instance = subnet.instantiate("inst1").bind_actions({"transform": transform})
    net = (
        lp.NetBuilder("Host")
        .place(host_in)
        .place(host_out)
        .compose_instance(instance, {"inbox": host_in, "outbox": host_out})
        .build()
    )

    result = lp.run_sync(net, initial={host_in: [{"v": 1}]})
    assert result.count(host_out) == 1
    assert result.first(host_out) == {"v": 1, "tag": "processed"}


def test_bind_actions_is_non_mutating() -> None:
    """``bind_actions`` returns a derived instance; the receiver is unchanged
    and remains independently composable (MOD-030 AC#8)."""

    local_in = lp.Place("LOCAL_IN")
    local_out = lp.Place("LOCAL_OUT")

    def tag_a(ctx: lp.TransitionContext) -> None:
        ctx.output("LOCAL_OUT", {**ctx.input("LOCAL_IN"), "by": "a"})

    def tag_b(ctx: lp.TransitionContext) -> None:
        ctx.output("LOCAL_OUT", {**ctx.input("LOCAL_IN"), "by": "b"})

    subnet = (
        lp.SubnetDef("Tagger")
        .transition(
            lp.Transition("tag")
            .input(lp.one(local_in))
            .output(lp.out(local_out))
            .build()
        )
        .input_port("inbox", local_in)
        .output_port("outbox", local_out)
        .build()
    )

    base = subnet.instantiate("inst")
    bound_a = base.bind_actions({"tag": tag_a})
    bound_b = base.bind_actions({"tag": tag_b})

    a_in, a_out = lp.Place("a_in"), lp.Place("a_out")
    b_in, b_out = lp.Place("b_in"), lp.Place("b_out")

    net_a = (
        lp.NetBuilder("A")
        .place(a_in)
        .place(a_out)
        .compose_instance(bound_a, {"inbox": a_in, "outbox": a_out})
        .build()
    )
    net_b = (
        lp.NetBuilder("B")
        .place(b_in)
        .place(b_out)
        .compose_instance(bound_b, {"inbox": b_in, "outbox": b_out})
        .build()
    )

    res_a = lp.run_sync(net_a, initial={a_in: [{"v": 1}]})
    res_b = lp.run_sync(net_b, initial={b_in: [{"v": 1}]})
    assert res_a.first(a_out) == {"v": 1, "by": "a"}
    assert res_b.first(b_out) == {"v": 1, "by": "b"}


def test_identity_round_trip_entry_still_resolves_all_declared_names() -> None:
    """MOD-031 AC#8: a declared place bound to a host place of its **own
    declared name** produces an *identity* entry (``x -> x``) in the
    correspondence, mixed with non-identity entries for the prefixed internal
    places. Every hardcoded declared name must still resolve.

    Identity entries used to be filtered out to keep the map minimal. They are
    now retained, because the chained rewrite pass carries the map forward
    without walking arcs, so the map is the only carrier of the author-original
    key set and a dropped key is unrecoverable at the next pass.

    Asserted on the executor run rather than on the map's shape: the failure
    mode is consume-then-throw — the transition enables, its inputs are
    consumed, and only then does the action fail its declared-place check, so
    the tokens are lost rather than the net failing to build (EXEC-031).

    This is the two-pass half — instantiate, then port-bind. The third pass,
    which renames the identity-bound place afterwards and is where the entry
    actually becomes load-bearing, is
    ``test_identity_round_trip_survives_a_later_renaming_pass`` below.
    """

    x = lp.Place("x")  # port place
    y = lp.Place("y")  # internal -> becomes inst/y
    z = lp.Place("z")  # internal sink -> becomes inst/z

    def join(ctx: lp.TransitionContext) -> None:
        # Every name here is the author-declared one. After compose, `x` is
        # the identity entry and `y` / `z` are prefixed.
        left = ctx.input("x")
        right = ctx.input("y")
        ctx.output("z", {**left, **right})

    subnet = (
        lp.SubnetDef("Step")
        .place(y)
        .place(z)
        .transition(
            lp.Transition("call")
            .input(lp.one(x))
            .input(lp.one(y))
            .output(lp.out(z))
            .action(join)
            .build()
        )
        .input_port("in", x)
        .build()
    )

    # The host place carries the subnet's own declared name -> identity entry.
    host_x = lp.Place("x")
    net = (
        lp.NetBuilder("Host")
        .place(host_x)
        .compose("inst", subnet, {"in": host_x})
        .build()
    )

    result = lp.run_sync(
        net,
        initial={host_x: [{"l": 1}], lp.Place("inst/y"): [{"r": 2}]},
    )

    sink = lp.Place("inst/z")
    assert result.count(sink) == 1, "action must resolve every declared name and produce"
    assert result.first(sink) == {"l": 1, "r": 2}
    assert result.count(host_x) == 0, "input consumed"
    assert result.count(lp.Place("inst/y")) == 0, "input consumed"


def test_all_identity_correspondence_still_resolves() -> None:
    """MOD-031 AC#9: when *every* declared place round-trips to its own name
    the correspondence carries no information and may be dropped wholesale.
    The action's declared names are then the actual names, so the binding's
    literal-first lookup resolves them without consulting a map at all."""

    x = lp.Place("x")
    z = lp.Place("z")

    def pass_through(ctx: lp.TransitionContext) -> None:
        ctx.output("z", {**ctx.input("x"), "seen": True})

    subnet = (
        lp.SubnetDef("Step")
        .transition(
            lp.Transition("call")
            .input(lp.one(x))
            .output(lp.out(z))
            .action(pass_through)
            .build()
        )
        .input_port("in", x)
        .output_port("out", z)
        .build()
    )

    # Both ports bind to host places carrying the author's own names.
    host_x = lp.Place("x")
    host_z = lp.Place("z")
    net = (
        lp.NetBuilder("Host")
        .place(host_x)
        .place(host_z)
        .compose("inst", subnet, {"in": host_x, "out": host_z})
        .build()
    )

    result = lp.run_sync(net, initial={host_x: [{"v": 1}]})
    assert result.count(host_z) == 1
    assert result.first(host_z) == {"v": 1, "seen": True}


def test_identity_round_trip_survives_a_later_renaming_pass() -> None:
    """MOD-031 AC#8, the full three-pass shape.

    Pass 1 instantiates under ``inst``; pass 2 binds the port to a host place
    carrying the subnet's **own declared name**, so ``x``'s correspondence
    round-trips to ``x``; pass 3 retrofits that host as a subnet via
    ``SubnetDef.from_net`` and composes it under ``outer``, which finally
    renames ``x``.

    A correspondence that dropped the identity entry at pass 2 has nothing to
    carry into pass 3 — the chained rewrite deliberately does not walk arcs —
    so ``ctx.input("x")`` resolves to a place that no longer exists. The
    transition still *enables* and its inputs are still consumed, so the
    symptom is lost tokens rather than a build error (EXEC-031); this asserts
    on the run, not on the map's shape.

    The mixed case is what makes it reachable: ``y`` and ``z`` stay
    non-identity, so the map survives pass 2 as a real map. An all-identity
    map is dropped whole and the next pass self-heals off the arcs (AC#9).
    """

    x = lp.Place("x")
    y = lp.Place("y")
    z = lp.Place("z")

    def join(ctx: lp.TransitionContext) -> None:
        left = ctx.input("x")  # author-declared names throughout
        right = ctx.input("y")
        ctx.output("z", {**left, **right})

    subnet = (
        lp.SubnetDef("Step")
        .place(y)
        .place(z)
        .transition(
            lp.Transition("call")
            .input(lp.one(x))
            .input(lp.one(y))
            .output(lp.out(z))
            .action(join)
            .build()
        )
        .input_port("in", x)
        .build()
    )

    # Passes 1 + 2: the host place carries the declared name -> identity entry.
    host_x = lp.Place("x")
    host = (
        lp.NetBuilder("Host")
        .place(host_x)
        .compose("inst", subnet, {"in": host_x})
        .build()
    )
    assert {p.name for p in host.places} >= {"x", "inst/y", "inst/z"}

    # Pass 3: retrofit and compose under a second prefix, renaming `x`.
    retrofit = lp.SubnetDef.from_net(
        host, lp.Interface().input_port("in", host_x).build()
    )
    top = lp.NetBuilder("Top").compose("outer", retrofit, {}).build()

    result = lp.run_sync(
        top,
        initial={lp.Place("outer/x"): [{"l": 1}], lp.Place("outer/inst/y"): [{"r": 2}]},
    )

    sink = lp.Place("outer/inst/z")
    assert result.count(sink) == 1, (
        "the action must resolve both declared places after the later rename; "
        "a dropped identity entry loses `x` and the firing throws after consuming"
    )
    assert result.first(sink) == {"l": 1, "r": 2}
    assert result.count(lp.Place("outer/x")) == 0, "input consumed"


def test_nested_instantiation_resolves_doubly_prefixed() -> None:
    """MOD-013 + MOD-031 AC#3: a declared place resolves through *nested*
    instantiation to the doubly-prefixed composed place.

    Compose ``Inner`` into a body net under ``inner``, retrofit that body as
    subnet ``S``, then compose ``S`` under ``outer``. The inner action's
    hardcoded ``xDecl`` must reach ``outer/inner/xDecl`` and its ``reqDecl``
    must reach the host place, through two prefixing passes.
    """

    req = lp.Place("reqDecl")
    x = lp.Place("xDecl")

    def emit(ctx: lp.TransitionContext) -> None:
        msg = ctx.input("reqDecl")  # bound out to the host, two passes up
        ctx.output("xDecl", {**msg, "emitted": True})  # internal, doubly prefixed

    inner = (
        lp.SubnetDef("Inner")
        .place(x)
        .transition(
            lp.Transition("emit")
            .input(lp.one(req))
            .output(lp.out(x))
            .action(emit)
            .build()
        )
        .input_port("in", req)
        .build()
    )

    s_in = lp.Place("sIn")
    body = (
        lp.NetBuilder("Sbody")
        .place(s_in)
        .compose("inner", inner, {"in": s_in})
        .build()
    )

    s_def = lp.SubnetDef.from_net(
        body, lp.Interface().input_port("sin", s_in).build()
    )

    host_req = lp.Place("hostReq")
    host = (
        lp.NetBuilder("Host")
        .place(host_req)
        .compose("outer", s_def, {"sin": host_req})
        .build()
    )

    names = {p.name for p in host.places}
    assert "outer/inner/xDecl" in names, f"doubly-prefixed internal place: {names}"
    assert "hostReq" in names

    result = lp.run_sync(host, initial={host_req: [{"v": 7}]})
    assert result.count(lp.Place("outer/inner/xDecl")) == 1
    assert result.first(lp.Place("outer/inner/xDecl")) == {"v": 7, "emitted": True}
