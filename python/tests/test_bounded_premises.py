"""VER-006 AC3: the ``bounded(k)`` premises.

Every route models a bounded environment place as a source holding at most k. That is the
executor only when no transition deposits into an environment place and the initial marking
holds at most k on each one. Outside those premises ``verify`` answers unknown, naming the
place, on every route.
"""

import libpetri as lp
import pytest

pytestmark = [
    pytest.mark.skipif(not lp.HAS_Z3, reason="z3 feature not enabled"),
    pytest.mark.skipif(not lp.z3_available(), reason="no usable z3 executable"),
]

A, B, C, D, E, OUT, SOURCE = (lp.Place(n) for n in ("a", "b", "c", "d", "E", "out", "source"))


def _arc(name, inp, to):
    return lp.Transition(name).input(inp).output(lp.out(to)).action(lp.fork).build()


def _net(name, *transitions, join=False):
    builder = lp.Net(name)
    for t in transitions:
        builder = builder.transition(t)
    if join:
        branch_a, branch_b, merged = lp.Place("branchA"), lp.Place("branchB"), lp.Place("merged")
        builder = builder.transition(
            lp.Transition("fork").input(lp.one(SOURCE)).output(lp.and_(branch_a, branch_b)).action(lp.fork).build()
        ).transition(
            lp.Transition("join")
            .input(lp.one(branch_a))
            .input(lp.one(branch_b))
            .match_spec(lp.match_spec([(branch_a, lambda m: m), (branch_b, lambda m: m)]))
            .output(lp.out(merged))
            .action(lp.fork)
            .build()
        )
    return builder.build()


def _verify(net, marking, prop, budget=50_000, join=False):
    kw = {"mint_transitions": ["fork"]} if join else {}
    return lp.verify(
        net,
        prop,
        initial_marking=marking,
        environment_places=["E"],
        environment_mode=lp.bounded(1),
        enumeration_max_classes=budget,
        timeout_ms=15_000,
        **kw,
    )


def _assert_refused(result, cause):
    assert result.verdict == "unknown", result.report
    assert result.reason.startswith(
        f"environment place 'E' is outside the Bounded(1) premises (VER-006 AC3): {cause}. "
    ), result.reason


@pytest.mark.parametrize("budget", [0, 50_000])
def test_an_initial_marking_above_k_is_refused(budget):
    net = _net("capA", _arc("t", lp.one(A), B), lp.Transition("u").input(lp.one(E)).input(lp.one(D)).output(lp.out(C)).action(lp.fork).build())
    result = _verify(net, {"a": 1, "E": 2}, lp.place_bound("b", 0), budget)
    _assert_refused(result, "the initial marking holds 2 tokens there, more than 1")


def test_a_deposit_into_an_environment_place_is_refused():
    net = _net("capB", _arc("t", lp.one(A), E))
    _assert_refused(_verify(net, {"a": 2}, lp.place_bound("E", 1)), "transition 't' deposits into it")


def test_a_deposit_by_a_split_transition_is_refused_naming_it():
    """``u`` tests ``E`` with an inhibitor, so ``t`` is split (VER-004) and the deposit into
    ``E`` is made by ``complete:t``. The reason names the caller's transition ``t``."""
    watch = lp.Transition("u").input(lp.one(lp.Place("q"))).inhibitor(lp.inhibitor(E)).output(lp.out(lp.Place("r"))).action(lp.fork).build()
    net = _net("capSplit", _arc("t", lp.one(A), E), watch)
    result = _verify(net, {"a": 2, "q": 1}, lp.place_bound("E", 1))
    _assert_refused(result, "transition 't' deposits into it")
    assert "complete:" not in result.reason, result.reason


@pytest.mark.parametrize("join", [True, False])
def test_a_demand_above_k_met_by_deposits_is_refused_on_every_route(join):
    net = _net("supplied", _arc("t0", lp.one(A), E), _arc("t1", lp.exactly(2, E), OUT), join=join)
    result = _verify(net, {"a": 2, "source": 1}, lp.place_bound("out", 0), join=join)
    _assert_refused(result, "transition 't0' deposits into it")


def test_a_spurious_deadlock_from_an_initial_marking_above_k_is_refused():
    net = _net("quiescent", _arc("tQ1", lp.exactly(2, E), OUT), _arc("tQ2", lp.one(OUT), OUT))
    result = _verify(net, {"E": 2}, lp.deadlock_free())
    _assert_refused(result, "the initial marking holds 2 tokens there, more than 1")


def test_within_the_premises_the_verdict_stands():
    net = _net("within", _arc("t", lp.one(A), B), _arc("u", lp.one(E), OUT))
    marking = {"a": 1, "E": 1}
    assert _verify(net, marking, lp.place_bound("b", 0), 0).verdict == "violated"
    proven = _verify(net, marking, lp.place_bound("b", 1), 0)
    assert proven.verdict == "proven", proven.report
    assert proven.route != "unavailable"
