"""Composition guards and the subnet accessor through the Python binding.

Mirrors the Rust `petri_net::tests` of the same requirements:

- MOD-020: binding two ports of one instance to the same host place, so that one
  transition would consume from it through two input arcs, is rejected at compose;
- MOD-027: an arc naming a port place that compose bound to a host place is
  rejected at build, whether it was added before or after the compose;
- IO-011: a place named twice in one AND output branch is rejected at transition
  build, and compose rejects binding two output ports of one AND branch to one
  host place (the output side of MOD-020), both as ``StructureError``;
- MOD-040: ``Net.subnet_of`` walks a name's ``/``-prefixes up to one that carries a
  transition, after ``Net.subnet_membership``, the direct-composition metadata it
  reads first (MOD-026).
"""

from __future__ import annotations

import pytest

import libpetri as lp


def _join() -> lp.BuiltSubnetDef:
    a, b, out = lp.Place("a"), lp.Place("b"), lp.Place("out")
    join = (
        lp.Transition("join")
        .input(lp.one(a))
        .input(lp.one(b))
        .output(lp.out(out))
        .action(lp.fork)
        .build()
    )
    return (
        lp.SubnetDef("Join")
        .transition(join)
        .input_port("a", a)
        .input_port("b", b)
        .output_port("out", out)
        .build()
    )


def test_two_ports_bound_to_one_host_place_are_rejected_at_compose() -> None:
    x = lp.Place("X")
    with pytest.raises(
        lp.StructureError,
        match=r"ports 'a' and 'b' of instance 's' are both bound to host place 'X'; "
        r"transition 's/join' would consume from 'X' through two input arcs\. Bind them "
        r"to distinct places or use one port\.",
    ):
        lp.NetBuilder("Host").compose("s", _join(), {"a": x, "b": x})


IO011 = (
    r"output spec of transition 't' names place 'C' twice in one AND branch; outputs are "
    r"sets \(IO-015\)"
)


@pytest.mark.parametrize(
    "output",
    [
        lambda a, b, c: lp.and_(c, c),
        lambda a, b, c: lp.and_(c, lp.and_(b, c)),
        lambda a, b, c: lp.xor(a, lp.and_(c, c)),
    ],
    ids=["and", "nested-and", "and-under-xor"],
)
def test_a_place_twice_in_one_and_branch_is_rejected_at_build(output) -> None:
    a, b, c = lp.Place("A"), lp.Place("B"), lp.Place("C")
    builder = lp.Transition("t").input(lp.one(a)).output(output(a, b, c))
    with pytest.raises(lp.StructureError, match=IO011):
        builder.build()


def test_a_place_in_two_xor_branches_builds() -> None:
    a, c = lp.Place("A"), lp.Place("C")
    lp.Transition("t").input(lp.one(a)).output(lp.xor(c, c)).build()


def test_two_output_ports_of_one_and_branch_bound_to_one_host_place_are_rejected() -> None:
    a, o1, o2 = lp.Place("a"), lp.Place("o1"), lp.Place("o2")
    fan = (
        lp.SubnetDef("Fan")
        .transition(lp.Transition("t").input(lp.one(a)).output(lp.and_(o1, o2)).action(lp.fork).build())
        .input_port("a", a)
        .output_port("o1", o1)
        .output_port("o2", o2)
        .build()
    )
    x = lp.Place("X")
    with pytest.raises(
        lp.StructureError,
        match=r"ports 'o1' and 'o2' of instance 's' are both bound to host place 'X'; "
        r"transition 's/t' would produce into 'X' twice in one AND branch\.",
    ):
        lp.NetBuilder("Host").compose("s", fan, {"a": lp.Place("A"), "o1": x, "o2": x})


def _answer() -> lp.BuiltSubnetDef:
    p_in, p_out = lp.Place("IN"), lp.Place("OUT")
    answer = (
        lp.Transition("answer").input(lp.one(p_in)).output(lp.out(p_out)).action(lp.fork).build()
    )
    return (
        lp.SubnetDef("Answer")
        .transition(answer)
        .input_port("in", p_in)
        .output_port("out", p_out)
        .build()
    )


def _hub_kill(target: lp.Place) -> lp.BuiltTransition:
    return lp.Transition("hub_kill").input(lp.one(lp.Place("KILL"))).reset(lp.reset(target)).build()


MOD027 = (
    r"place 'answer/IN' is port 'in' of instance 'answer', bound to host place 'A_IN' at "
    r"compose; reference 'A_IN' instead"
)


def test_an_arc_on_a_bound_port_place_is_rejected_at_build_in_either_order() -> None:
    a_in = lp.Place("A_IN")
    stale = lp.Place("answer/IN")

    after = lp.NetBuilder("Host").compose("answer", _answer(), {"in": a_in}).transition(
        _hub_kill(stale)
    )
    with pytest.raises(lp.StructureError, match=MOD027):
        after.build()

    before = lp.NetBuilder("Host").transition(_hub_kill(stale)).compose(
        "answer", _answer(), {"in": a_in}
    )
    with pytest.raises(lp.StructureError, match=MOD027):
        before.build()


def test_referencing_the_host_place_builds() -> None:
    a_in = lp.Place("A_IN")
    net = (
        lp.NetBuilder("Host")
        .compose("answer", _answer(), {"in": a_in})
        .transition(_hub_kill(a_in))
        .build()
    )
    assert len(net.transitions) == 2


def test_subnet_of_is_the_auto_cluster_rule() -> None:
    a_in = lp.Place("A_IN")
    net = (
        lp.NetBuilder("Host")
        .compose("answer", _answer(), {"in": a_in})
        .transition(_hub_kill(a_in))
        .build()
    )
    # Instance composition records no membership (MOD-026 rule 4) ...
    assert net.subnet_membership == {}
    # ... so subnet_of answers from the name.
    assert net.subnet_of("answer/answer") == "answer"
    assert net.subnet_of("answer/OUT") == "answer"
    assert net.subnet_of("A_IN") is None
    assert net.subnet_of("hub_kill") is None
    # Not a node of the net: the bound port place is gone.
    assert net.subnet_of("answer/IN") is None
    assert net.subnet_of("nowhere/x") is None


def test_subnet_of_walks_up_to_a_prefix_that_carries_a_transition() -> None:
    def t(name: str, src: str, dst: str) -> lp.Transition:
        return lp.Transition(name).input(lp.one(lp.Place(src))).output(lp.out(lp.Place(dst))).build()

    net = (
        lp.NetBuilder("Host")
        .transition(t("s1/t", "s1/in", "s1/obs/TURN"))
        .transition(t("outer/inner/t", "outer/inner/p", "x/y"))
        .build()
    )
    # `s1/obs` carries no transition, so the place belongs to `s1`.
    assert net.subnet_of("s1/obs/TURN") == "s1"
    assert net.subnet_of("s1/t") == "s1"
    assert net.subnet_of("outer/inner/p") == "outer/inner"
    assert net.subnet_of("x/y") is None
