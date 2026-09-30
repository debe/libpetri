"""IO-014 / VER-001 AC4-AC5: when a transition's timeout fires, a forward_input puts one
token in its target per token the firing consumed. Every analysis used to put one, so
``exactly(2, a) -> xor(c, timeout(50, forward_input(a, b)))`` proved ``place_bound(b, 1)``
while the executor ends at b = 2. Rides on the Rust verifier."""

import libpetri as lp
import pytest

pytestmark = pytest.mark.skipif(not lp.HAS_Z3, reason="z3 feature not enabled")


def _net(input_of):
    a, b, c = lp.Place("a"), lp.Place("b"), lp.Place("c")
    t = (
        lp.Transition("t")
        .input(input_of(a))
        .output(lp.xor(lp.out(c), lp.timeout(50, lp.forward_input(a, b))))
        .action(lp.fork)
        .build()
    )
    return lp.Net("forward").transition(t).build()


# (enumeration budget, linear bound, VER-018 phase and VER-019 bound, route); the third
# arm leaves the CHC fixpoint query alone to decide.
@pytest.mark.parametrize(
    "budget,linear_bound,phases,route",
    [
        (0, True, True, "smt"),
        (0, False, True, "smt"),
        (0, False, False, "smt"),
        (50_000, True, True, "enumeration"),
    ],
)
def test_a_forward_of_two_tokens_violates_a_bound_of_one(budget, linear_bound, phases, route):
    result = lp.verify(
        _net(lambda a: lp.exactly(2, a)),
        lp.place_bound("b", 1),
        initial_marking={"a": 2},
        enumeration_max_classes=budget,
        linear_bound=linear_bound,
        state_equation_phase=phases,
        firing_bound=phases,
        timeout_ms=15_000,
    )
    assert result.verdict == "violated", result.report
    assert result.route == route, result.report
    assert len(result.counterexample_transitions) == 1, result.report
    last = result.counterexample_trace[-1]
    assert (last.get("a", 0), last.get("b", 0)) == (0, 2), result.report


@pytest.mark.parametrize("input_of", [lp.all_tokens, lambda a: lp.at_least(1, a)])
def test_a_forward_of_a_drained_input_is_refused_by_the_linear_routes(input_of):
    # Enumeration off: only the linear routes are left, and each refuses (VER-003 AC5).
    result = lp.verify(
        _net(input_of),
        lp.place_bound("b", 1),
        initial_marking={"a": 2},
        enumeration_max_classes=0,
        timeout_ms=15_000,
    )
    assert result.verdict == "unknown", result.report
    assert "forwards its All/AtLeast input 'a' to 'b'" in result.report
    assert "refusing to certify on the linear routes" in result.report


@pytest.mark.parametrize("input_of", [lp.all_tokens, lambda a: lp.at_least(1, a)])
def test_a_forward_of_a_drained_input_is_decided_by_the_enumeration(input_of):
    # The enumeration (VER-017) counts the drained batch as the executor does: b reaches
    # 2 (the timeout forwards both drained tokens), never 3.
    def verify(bound):
        return lp.verify(
            _net(input_of),
            lp.place_bound("b", bound),
            initial_marking={"a": 2},
            enumeration_max_classes=50_000,
            timeout_ms=15_000,
        )

    violated = verify(1)
    assert violated.verdict == "violated", violated.report
    assert violated.route == "enumeration", violated.report
    last = violated.counterexample_trace[-1]
    assert (last.get("a", 0), last.get("b", 0)) == (0, 2), violated.report
    proven = verify(2)
    assert proven.verdict == "proven", proven.report
    assert proven.route == "enumeration", proven.report


# VER-002: a mutual exclusion over three places is pairwise on every route.
@pytest.mark.parametrize(
    "budget,linear_bound,phases",
    [(50_000, True, True), (0, True, True), (0, False, True), (0, False, False)],
)
def test_a_three_place_mutual_exclusion_is_pairwise(budget, linear_bound, phases):
    s, a, b, c = lp.Place("s"), lp.Place("a"), lp.Place("b"), lp.Place("c")
    fork_net = (
        lp.Net("fork")
        .transition(lp.Transition("t").input(lp.one(s)).output(lp.and_(lp.out(a), lp.out(b))).action(lp.fork).build())
        .place(c)
        .build()
    )

    def verify(net, places):
        return lp.verify(
            net,
            lp.mutual_exclusion(places),
            initial_marking={"s": 1},
            enumeration_max_classes=budget,
            linear_bound=linear_bound,
            state_equation_phase=phases,
            firing_bound=phases,
            timeout_ms=15_000,
        )

    violated = verify(fork_net, ["c", "a", "b"])
    assert violated.verdict == "violated", violated.report
    assert list(violated.counterexample_transitions) == ["t"], violated.report
    chain = (
        lp.Net("chain")
        .transition(lp.Transition("t1").input(lp.one(s)).output(lp.out(a)).action(lp.fork).build())
        .transition(lp.Transition("t2").input(lp.one(a)).output(lp.out(b)).action(lp.fork).build())
        .transition(lp.Transition("t3").input(lp.one(b)).output(lp.out(c)).action(lp.fork).build())
        .build()
    )
    proven = verify(chain, ["a", "b", "c"])
    assert proven.verdict == "proven", proven.report


def test_an_initial_violation_on_the_fixpoint_query_is_the_empty_trace():
    # One marking (M0), no transition — with the replay on or off.
    p, q = lp.Place("p"), lp.Place("q")
    net = lp.Net("initial").transition(
        lp.Transition("t").input(lp.one(p)).output(lp.out(q)).action(lp.fork).build()
    ).build()
    for replay in (True, False):
        result = lp.verify(
            net,
            lp.place_bound("p", 0),
            initial_marking={"p": 1},
            enumeration_max_classes=0,
            linear_bound=False,
            state_equation_phase=False,
            firing_bound=False,
            counterexample_replay=replay,
            timeout_ms=15_000,
        )
        assert result.verdict == "violated", result.report
        assert result.route == "smt", result.report
        assert len(result.counterexample_trace) == 1, result.report
        assert list(result.counterexample_transitions) == [], result.report
        assert "the initial marking violates the property" in result.report
