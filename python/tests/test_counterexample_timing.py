"""VER-003 ``counterexample_timing``, the VER-023 timed counterexample check and
the VER-013 total budget, through the Python binding. Mirrors the Rust
`smt_verifier::tests` of the same names on the lab's watchdog net
(`research/net-metrics/lab/TimedNets.java` ``watchdogs(n, false)``).
"""

from __future__ import annotations

import pytest

import libpetri as lp

pytestmark = pytest.mark.skipif(not lp.HAS_Z3, reason="z3 feature not enabled")


def _watchdogs(n: int, watchdog_ms: int):
    b = lp.Net(f"watchdog-timing-{n}")
    m0 = {}
    for i in range(n):
        req, calling = lp.Place(f"REQ_{i}"), lp.Place(f"CALLING_{i}")
        resp, timeout = lp.Place(f"RESP_{i}"), lp.Place(f"TIMEOUT_{i}")
        b = (
            b.transition(
                lp.Transition(f"start_{i}").input(lp.one(req)).output(lp.out(calling))
                .action(lp.fork).build()
            )
            .transition(
                lp.Transition(f"answer_{i}").input(lp.one(calling)).output(lp.out(resp))
                .timing(lp.window(0, 2)).action(lp.fork).build()
            )
            .transition(
                lp.Transition(f"watchdog_{i}").input(lp.one(calling)).output(lp.out(timeout))
                .timing(lp.delayed(watchdog_ms)).action(lp.fork).build()
            )
        )
        m0[req] = 1
    return b.build(), m0


NO_TIMEOUT = lp.unreachable(["TIMEOUT_0"])


def test_the_default_is_the_untimed_abstraction() -> None:
    net, m0 = _watchdogs(2, 5)
    result = lp.verify(net, NO_TIMEOUT, initial_marking=m0)
    assert result.verdict == "violated"
    assert result.counterexample_timing == "untimed-abstraction"


def test_the_timed_check_finds_the_watchdog_spurious() -> None:
    net, m0 = _watchdogs(2, 5)
    result = lp.verify(net, NO_TIMEOUT, initial_marking=m0, timed_counterexample_check=True)
    assert result.verdict == "violated", "the check never changes a verdict"
    assert result.counterexample_timing == "spurious-under-timing"
    assert "closed with 10 classes" in result.report


def test_a_timing_real_violation_is_confirmed() -> None:
    net, m0 = _watchdogs(1, 1)
    result = lp.verify(net, NO_TIMEOUT, initial_marking=m0, timed_counterexample_check=True)
    assert result.counterexample_timing == "timed-confirmed"
    assert result.counterexample_transitions == ["start_0", "watchdog_0"]
    assert result.counterexample_confirmed is True


def test_non_violated_verdicts_carry_no_timing() -> None:
    net, m0 = _watchdogs(1, 5)
    result = lp.verify(net, lp.place_bound("RESP_0", 1), initial_marking=m0)
    assert result.verdict == "proven"
    assert result.counterexample_timing is None


def test_a_spent_total_budget_is_unknown_naming_the_step() -> None:
    net, m0 = _watchdogs(1, 5)
    result = lp.verify(net, NO_TIMEOUT, initial_marking=m0, total_budget_ms=0)
    assert result.verdict == "unknown"
    assert result.reason == (
        "total verification budget of 0 ms exhausted during net preparation"
    )
    assert result.counterexample_timing is None
