"""CORE-072 / VER-001: a place the initial marking marks and the net does not
declare is an inert place of the verified net. Every route sees its token, so the
verdict does not depend on the class budget, a bound counts it, and a property may
name it (VER-003 AC5). Rides on the Rust verifier."""

import libpetri as lp
import pytest

pytestmark = pytest.mark.skipif(not lp.HAS_Z3, reason="z3 feature not enabled")


def _net(terminal=False):
    """``t: c -> d``; ``a`` is in no arc."""
    c, d = lp.Place("c"), lp.Place("d")
    builder = lp.Net("stray").transition(
        lp.Transition("t").input(lp.one(c)).output(lp.out(d)).action(lp.fork).build()
    )
    if terminal:
        builder = builder.terminal(d)
    return builder.build()


@pytest.mark.parametrize("budget", [0, 1, 50_000])
def test_a_stray_token_strands_the_net_at_every_budget(budget):
    result = lp.verify(
        _net(),
        lp.deadlock_free(),
        initial_marking={"a": 1},
        sink_places=["d"],
        enumeration_max_classes=budget,
        timeout_ms=15_000,
    )
    assert result.verdict == "violated", result.report


@pytest.mark.parametrize("budget", [0, 50_000])
def test_a_bound_counts_the_stray_token(budget):
    result = lp.verify(
        _net(),
        lp.place_bound("a", 0),
        initial_marking={"a": 1},
        enumeration_max_classes=budget,
        timeout_ms=15_000,
    )
    assert result.verdict == "violated", result.report


@pytest.mark.parametrize("budget", [0, 50_000])
def test_without_a_stray_token_the_net_is_unchanged(budget):
    result = lp.verify(
        _net(),
        lp.deadlock_free(),
        initial_marking={"c": 1},
        sink_places=["d"],
        enumeration_max_classes=budget,
        timeout_ms=15_000,
    )
    assert result.verdict == "proven", result.report


@pytest.mark.parametrize("budget", [0, 50_000])
def test_a_terminal_excuses_the_stray_token(budget):
    result = lp.verify(
        _net(terminal=True),
        lp.deadlock_free(),
        initial_marking={"c": 1, "a": 1},
        enumeration_max_classes=budget,
        timeout_ms=15_000,
    )
    assert result.verdict == "proven", result.report
