"""VER-006 ``arrivals(k)``: at most ``k`` tokens injected into each environment
place over the whole run, as a net rewrite before any route."""

import libpetri as lp
import pytest

pytestmark = pytest.mark.skipif(not lp.HAS_Z3, reason="z3 feature not enabled")


def _env_source():
    """``env IN -> T -> OUT``."""
    inp = lp.Place("IN")
    out = lp.Place("OUT")
    return (
        lp.Net("env-source")
        .transition(lp.Transition("T").input(lp.one(inp)).output(lp.out(out)).action(lp.fork).build())
        .build()
    )


def _verify(mode, prop, **kw):
    return lp.verify(_env_source(), prop, environment_places=["IN"], environment_mode=mode, **kw)


def test_arrivals_bounds_the_total_injected():
    proven = _verify(lp.arrivals(2), lp.place_bound("OUT", 2))
    assert proven.verdict == "proven", proven.report
    assert proven.route == "enumeration"
    assert (
        "Environment: arrivals(2) — net closed before any route: env:arrive?[0]:IN from "
        "env:optional[0] (at most 2) (VER-006)"
    ) in proven.report
    violated = _verify(lp.arrivals(2), lp.place_bound("OUT", 1))
    assert violated.verdict == "violated"
    assert violated.counterexample_transitions.count("env:arrive?[0]:IN") == 2
    assert violated.counterexample_transitions.count("T") == 2
    assert repr(lp.arrivals(2)) == "EnvironmentAnalysisMode.arrivals(2)"


@pytest.mark.skipif(not lp.z3_available(), reason="no usable z3 executable")
def test_bounded_does_not_bound_the_total():
    result = _verify(lp.bounded(2), lp.place_bound("OUT", 2), timeout_ms=15_000)
    assert result.verdict == "violated", result.report


def test_arrivals_is_at_most_k_at_quiescence_too():
    result = _verify(lp.arrivals(2), lp.quiescent_count(["OUT"], 2, 2))
    assert result.verdict == "violated", result.report
    assert "env:decline[0]" in result.counterexample_transitions


def test_arrivals_min_max_is_exact_accounting_at_quiescence():
    """``arrivals(k, k)``: every arrival is mandatory, so the net rests with exactly ``k``."""
    result = _verify(lp.arrivals(2, 2), lp.quiescent_count(["OUT"], 2, 2))
    assert result.verdict == "proven", result.report
    assert (
        "Environment: arrivals(2..2) — net closed before any route: env:arrive[0]:IN from "
        "env:arrivals[0] (exactly 2) (VER-006)"
    ) in result.report
    partial = _verify(lp.arrivals(1, 2), lp.quiescent_count(["OUT"], 2, 2))
    assert partial.verdict == "violated", partial.report
    assert "env:decline[0]" in partial.counterexample_transitions
    assert repr(lp.arrivals(2, 3)) == "EnvironmentAnalysisMode.arrivals(2, 3)"
    assert repr(lp.arrivals(min_tokens=2, max_tokens=3)) == "EnvironmentAnalysisMode.arrivals(2, 3)"
    assert repr(lp.arrivals(0, 3)) == "EnvironmentAnalysisMode.arrivals(3)"
    assert repr(lp.arrivals(max_tokens=3)) == "EnvironmentAnalysisMode.arrivals(3)"


@pytest.mark.parametrize("args", [(3, 2), (-1, 2), (-1,)])
def test_arrivals_rejects_bad_bounds(args):
    with pytest.raises(ValueError):
        lp.arrivals(*args)


def test_an_arrival_into_a_match_key_is_declined_by_name():
    """VER-006 AC10: the injection transition feeding a match key is not a mint."""
    inp = lp.Place("IN")
    slot = lp.Place("slot")
    a = lp.Place("A")
    b = lp.Place("B")
    accepted = lp.Place("accepted")
    net = (
        lp.Net("keyed")
        .transition(lp.Transition("fork").input(lp.one(slot)).output(lp.and_(a, b)).action(lp.fork).build())
        .transition(
            lp.Transition("join")
            .input(lp.one(a))
            .input(lp.one(b))
            .input(lp.one(inp))
            .match_spec(lp.match_spec([(a, lambda m: m), (b, lambda m: m), (inp, lambda m: m)]))
            .output(lp.out(accepted))
            .action(lp.fork)
            .build()
        )
        .build()
    )
    result = lp.verify(
        net,
        lp.unreachable([accepted]),
        initial_marking={slot: 1},
        environment_places=[inp],
        environment_mode=lp.arrivals(1),
    )
    assert result.verdict == "unknown", result.report
    assert result.route == "nu-scg"
    assert "environment place 'IN' carries ν-names" in result.reason
    assert "fed by arrivals(k)" in result.reason
