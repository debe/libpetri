"""ν-net join relay (spec NU-054): the declaration and its build-time
rejections (AC1), the runtime check that every token a join writes into a
relay target carries the matched name (AC2), composition remapping the targets
like the keys, and the analysis reading a relaying join as a relay under
EXTENDED (AC3, AC5).

Mirrors Rust ``libpetri-runtime/src/nu_relay_tests.rs`` and
``libpetri-verification/tests/nu_join_relay.rs``, TypeScript
``tests/runtime/nu-join-relay.test.ts`` / ``tests/verification/nu-join-relay.test.ts``
and Java ``MatchSpecRelayTest`` / ``JoinRelayTest``.
"""

from __future__ import annotations

import pytest

import libpetri as lp


def _cid(m):
    return m["cid"]


A = lp.Place("A")
B = lp.Place("B")
C = lp.Place("C")


def _relay_join(action, output=None, relay_key=_cid, name="j"):
    """A join on A, B relaying to C; ``action`` decides what lands in C."""
    return (
        lp.Transition(name)
        .input(lp.one(A))
        .input(lp.one(B))
        .match_spec(lp.match_spec([(A, _cid), (B, _cid)], relay_to=[(C, relay_key)]))
        .output(output if output is not None else lp.out(C))
        .action(action)
        .build()
    )


def _run(transition, *, options=None, extra=None):
    net = lp.Net("relay").transition(transition).build()
    initial = {A: [{"cid": "x"}], B: [{"cid": "x"}]}
    initial.update(extra or {})
    store = lp.InMemoryEventStore()
    marking = lp.run_sync(net, initial=initial, options=options, event_store=store)
    failures = [e.payload()["error"] for e in store.events() if e.type == "TransitionFailed"]
    return marking, failures


OTHER_NAME = "'j': relay target 'C' received a token with name 'y', but the join matched name 'x' (NU-054)"
NO_NAME = "'j': relay target 'C' received a token with no name, but the join matched name 'x' (NU-054)"


# === AC1: declaration ===


def test_relay_targets_are_kept_apart_from_the_keys() -> None:
    spec = lp.match_spec([(A, _cid), (B, _cid)], relay_to=[(C, _cid)])
    assert repr(spec) == "MatchSpec(places=[\"A\", \"B\"], relay_to=[\"C\"])"


def test_a_relay_target_does_not_count_towards_the_two_correlated_inputs() -> None:
    with pytest.raises(ValueError, match="at least 2 input places, got 1"):
        lp.match_spec([(A, _cid)], relay_to=[(C, _cid)])


def test_rejects_a_relay_target_that_is_not_an_output() -> None:
    other = lp.Place("other")
    with pytest.raises(lp.StructureError) as excinfo:
        (
            lp.Transition("j")
            .input(lp.one(A))
            .input(lp.one(B))
            .match_spec(lp.match_spec([(A, _cid), (B, _cid)], relay_to=[(other, _cid)]))
            .output(lp.out(C))
            .build()
        )
    assert "Transition 'j': relay target 'other' is not an output of the transition (NU-054)" in str(
        excinfo.value
    )


def test_rejects_a_relay_target_declared_twice() -> None:
    with pytest.raises(lp.StructureError) as excinfo:
        (
            lp.Transition("j")
            .input(lp.one(A))
            .input(lp.one(B))
            .match_spec(lp.match_spec([(A, _cid), (B, _cid)], relay_to=[(C, _cid), (C, _cid)]))
            .output(lp.out(C))
            .build()
        )
    assert "Transition 'j': relay target 'C' is declared twice (NU-054)" in str(excinfo.value)


def test_accepts_a_self_loop_target() -> None:
    (
        lp.Transition("j")
        .input(lp.one(A))
        .input(lp.one(B))
        .match_spec(lp.match_spec([(A, _cid), (B, _cid)], relay_to=[(A, _cid)]))
        .output(lp.and_(A, C))
        .build()
    )


def _relaying_subnet() -> lp.BuiltSubnetDef:
    """A join relaying its matched name onto ``out1`` or ``out2`` (an XOR), both
    exposed as output ports."""
    in_a, in_b = lp.Place("inA"), lp.Place("inB")
    out1, out2 = lp.Place("out1"), lp.Place("out2")
    join = (
        lp.Transition("j")
        .input(lp.one(in_a))
        .input(lp.one(in_b))
        .match_spec(
            lp.match_spec([(in_a, _cid), (in_b, _cid)], relay_to=[(out1, _cid), (out2, _cid)])
        )
        .output(lp.xor(out1, out2))
        .action(lambda ctx: ctx.output("out1", {"cid": ctx.input("inA")["cid"]}))
        .build()
    )
    return (
        lp.SubnetDef("sub")
        .transition(join)
        .input_port("a", in_a)
        .input_port("b", in_b)
        .output_port("out1", out1)
        .output_port("out2", out2)
        .build()
    )


def test_composition_remaps_relay_targets_like_keys() -> None:
    host_a, host_b = lp.Place("hostA"), lp.Place("hostB")
    host_o1, host_o2 = lp.Place("hostO1"), lp.Place("hostO2")
    net = (
        lp.NetBuilder("host")
        .compose("s", _relaying_subnet(), {"a": host_a, "b": host_b, "out1": host_o1, "out2": host_o2})
        .build()
    )
    # The relay check runs on the remapped target: a conforming firing lands in hostO1.
    store = lp.InMemoryEventStore()
    marking = lp.run_sync(
        net, initial={host_a: [{"cid": "x"}], host_b: [{"cid": "x"}]}, event_store=store
    )
    assert [e for e in store.events() if e.type == "TransitionFailed"] == []
    assert marking.count(host_o1) == 1


def test_binding_two_relay_targets_onto_one_place_is_rejected() -> None:
    host_a, host_b, host_o = lp.Place("hostA"), lp.Place("hostB"), lp.Place("hostO")
    with pytest.raises(lp.StructureError, match=r"relay target 'hostO' is declared twice \(NU-054\)"):
        lp.NetBuilder("host").compose(
            "s", _relaying_subnet(), {"a": host_a, "b": host_b, "out1": host_o, "out2": host_o}
        )


# === AC2: runtime check ===


def test_a_conforming_action_fires_normally() -> None:
    def action(ctx):
        ctx.output("C", {"cid": ctx.input("A")["cid"]})

    marking, failures = _run(_relay_join(action))
    assert failures == []
    assert marking.count(C) == 1


def test_a_token_of_another_name_fails_the_firing() -> None:
    def action(ctx):
        ctx.output("C", {"cid": "y"})

    marking, failures = _run(_relay_join(action))
    assert failures == [OTHER_NAME]
    assert marking.count(C) == 0


def test_a_projection_that_yields_no_name_fails_the_firing() -> None:
    def action(ctx):
        ctx.output("C", {"other": 1})

    # The projection raises KeyError: no name, as for a match key.
    _, failures = _run(_relay_join(action))
    assert failures == [NO_NAME]


def test_a_none_value_has_no_name_and_the_projection_is_not_called() -> None:
    calls: list[object] = []

    def key(v):
        calls.append(v)
        return "x"

    def action(ctx):
        ctx.output("C", None)

    _, failures = _run(_relay_join(action, relay_key=key))
    assert failures == [NO_NAME]
    assert None not in calls


def test_every_token_in_the_target_is_checked() -> None:
    log = lp.Place("log")

    def action(ctx):
        ctx.output("C", {"cid": "x"})
        ctx.output("C", {"cid": "z"})
        ctx.output("log", "done")

    _, failures = _run(_relay_join(action, output=lp.and_(C, log)))
    assert len(failures) == 1 and "name 'z'" in failures[0]


def test_a_place_that_is_not_a_relay_target_is_not_checked() -> None:
    log = lp.Place("log")

    def action(ctx):
        ctx.output("C", {"cid": "x"})
        ctx.output("log", "anything")

    _, failures = _run(_relay_join(action, output=lp.and_(C, log)))
    assert failures == []


def test_skipped_exactly_where_output_validation_is() -> None:
    def action(ctx):
        ctx.output("C", {"cid": "y"})

    marking, failures = _run(
        _relay_join(action), options=lp.ExecutorOptions(skip_output_validation=True)
    )
    assert failures == []
    assert marking.count(C) == 1


@pytest.mark.asyncio
async def test_a_flushed_batch_is_checked_when_it_is_published() -> None:
    # The refused batch raises from ``flush()``; an action that swallows it still
    # fails the firing with the relay error.
    raised = []

    async def action(ctx):
        ctx.output("C", {"cid": "y"})
        try:
            ctx.flush()
        except RuntimeError as e:
            raised.append(str(e))
        ctx.output("C", {"cid": "x"})

    net = lp.Net("relay").transition(_relay_join(action)).build()
    store = lp.InMemoryEventStore()
    marking = await lp.run_async(
        net, initial={A: [{"cid": "x"}], B: [{"cid": "x"}]}, event_store=store
    )
    failures = [e.payload()["error"] for e in store.events() if e.type == "TransitionFailed"]
    assert failures == [OTHER_NAME]
    assert raised == [OTHER_NAME]
    assert marking.count(C) == 0


# === analysis: EXTENDED reads the join as a relay (AC3, AC5) ===


def _join_chain(relay: bool) -> lp.BuiltNet:
    s, a, b, c, d, done = (lp.Place(n) for n in ("S", "A", "B", "C", "D", "done"))
    ident = lambda v: v  # noqa: E731
    return (
        lp.Net("join-chain")
        .transition(lp.Transition("fork").input(lp.one(s)).output(lp.and_(a, b, d)).action(lp.fork).build())
        .transition(
            lp.Transition("j1")
            .input(lp.one(a))
            .input(lp.one(b))
            .match_spec(lp.match_spec([(a, ident), (b, ident)], relay_to=[(c, ident)] if relay else None))
            .output(lp.out(c))
            .action(lp.fork)
            .build()
        )
        .transition(
            lp.Transition("j2")
            .input(lp.one(c))
            .input(lp.one(d))
            .match_spec(lp.match_spec([(c, ident), (d, ident)]))
            .output(lp.out(done))
            .action(lp.fork)
            .build()
        )
        .build()
    )


def _chain_with_timeout(child) -> lp.BuiltNet:
    """The join chain with j1's relay into C written by the action, or by the
    executor on timeout (``child``). j1 also consumes the uncoloured Z, so a
    forward of a non-key input can be stated."""
    s, a, b, c, d, z, done = (lp.Place(n) for n in ("S", "A", "B", "C", "D", "Z", "done"))
    ident = lambda v: v  # noqa: E731
    return (
        lp.Net("chain-timeout")
        .transition(lp.Transition("fork").input(lp.one(s)).output(lp.and_(a, b, d)).action(lp.fork).build())
        .transition(
            lp.Transition("j1")
            .input(lp.one(a))
            .input(lp.one(b))
            .input(lp.one(z))
            .match_spec(lp.match_spec([(a, ident), (b, ident)], relay_to=[(c, ident)]))
            .output(lp.xor(lp.out(c), lp.timeout(10, child(a, z, c))))
            .action(lp.fork)
            .build()
        )
        .transition(
            lp.Transition("j2")
            .input(lp.one(c))
            .input(lp.one(d))
            .match_spec(lp.match_spec([(c, ident), (d, ident)]))
            .output(lp.out(done))
            .action(lp.fork)
            .build()
        )
        .build()
    )


def _chain_timeout_deadlock(net):
    return lp.verify(
        net,
        lp.deadlock_free(),
        initial_marking={"S": 1, "Z": 1},
        sink_places=["done"],
        budget_places=["S"],
        fragment_mode="extended",
        enumeration_max_classes=0,
        timeout_ms=2_000,
    )


@pytest.mark.parametrize(
    "child",
    [lambda a, z, c: lp.out(c), lambda a, z, c: lp.forward_input(z, c)],
    ids=["unit-token", "non-key-forward"],
)
def test_a_join_timeout_writing_a_relay_target_without_a_key_is_declined(child) -> None:
    # The executor checks every relay deposit, timeout branches included: a unit
    # token or another input's name fails the firing, which deposits nothing, so D
    # is stranded. The name layer would relay the name instead: a wrong proven.
    r = _chain_timeout_deadlock(_chain_with_timeout(child))
    assert r.verdict != "proven", r.report
    assert "Route B (EXTENDED) declined" in r.report, r.report
    assert "ν-encoding: name-coloured" not in r.report, r.report


def test_a_join_timeout_forwarding_a_key_into_a_relay_target_stays_in_the_fragment() -> None:
    r = _chain_timeout_deadlock(_chain_with_timeout(lambda a, z, c: lp.forward_input(a, c)))
    assert r.verdict == "proven", r.report
    assert "Route B" in r.report and "declined" not in r.report, r.report


def test_extended_decides_the_join_chain_through_route_b() -> None:
    reach = lp.verify(
        _join_chain(True),
        lp.unreachable(["done"]),
        initial_marking={"S": 1},
        fragment_mode="extended",
        mint_transitions=["fork"],
    )
    assert reach.verdict == "violated", reach.report
    assert reach.counterexample_transitions == ["fork", "j1", "j2"]
    dlf = lp.verify(
        _join_chain(True),
        lp.deadlock_free(),
        initial_marking={"S": 1},
        sink_places=["done"],
        fragment_mode="extended",
        mint_transitions=["fork"],
    )
    assert dlf.verdict == "proven", dlf.report
    assert "Route B" in dlf.report, dlf.report


def test_without_the_declaration_extended_declines() -> None:
    r = lp.verify(
        _join_chain(False),
        lp.deadlock_free(),
        initial_marking={"S": 1},
        sink_places=["done"],
        fragment_mode="extended",
    )
    assert r.verdict == "unknown", r.report
    assert "does not declare as a relay target" in r.report, r.report


def test_base_ignores_the_declaration_and_says_so() -> None:
    kwargs = dict(initial_marking={"S": 1}, sink_places=["done"])
    with_relay = lp.verify(_join_chain(True), lp.deadlock_free(), **kwargs)
    without = lp.verify(_join_chain(False), lp.deadlock_free(), **kwargs)
    assert with_relay.verdict == without.verdict
    assert (
        "NOTE: ν relay declarations ignored under BASE fragment mode (NU-054): 'j1' -> 'C'; "
        "select fragment_mode(FragmentMode::Extended) to analyse the joins as relays."
    ) in with_relay.report
    assert "NU-054" not in without.report
