"""CORE-037: a read, inhibitor or reset arc on a place nothing fills is warned
about — never rejected — by the executor (a ``WARN`` ``LogMessage`` when the
executor is constructed, recorded only where events are) and by the verifier (a
``WARNING:`` report line). Both come from the Rust runtime and verifier.
"""

from __future__ import annotations

import pytest

import libpetri as lp

MESSAGE = (
    "reset arc of 'hub_kill' on 'answer/IN': no transition produces into or consumes "
    "from it and it starts empty; the arc has no effect."
)


def _net() -> tuple[lp.Place, lp.Place, lp.BuiltNet]:
    kill, ghost = lp.Place("KILL"), lp.Place("answer/IN")
    net = (
        lp.Net("dead")
        .transition(
            lp.Transition("hub_kill").input(lp.one(kill)).reset(lp.reset(ghost)).build()
        )
        .build()
    )
    return kill, ghost, net


def test_the_executor_warns_once_per_dead_arc() -> None:
    kill, _ghost, net = _net()
    store = lp.InMemoryEventStore()
    result = lp.run_sync(net, initial={kill: [{}]}, event_store=store)
    warnings = [ev.payload() for ev in store.events(types={"LogMessage"})]
    assert warnings == [
        {**warnings[0], "transition_name": "hub_kill", "level": "WARN", "message": MESSAGE}
    ]
    assert result.count(kill) == 0, "the run is not rejected"


def test_a_seeded_place_is_not_warned_about() -> None:
    kill, ghost, net = _net()
    store = lp.InMemoryEventStore()
    lp.run_sync(net, initial={kill: [{}], ghost: [{}]}, event_store=store)
    assert store.events(types={"LogMessage"}) == []


@pytest.mark.skipif(not lp.HAS_Z3, reason="z3 feature not enabled")
def test_the_verifier_report_carries_the_warning() -> None:
    kill, _ghost, net = _net()
    result = lp.verify(net, lp.deadlock_free(), initial_marking={kill: 1})
    assert result.report.startswith(f"WARNING: {MESSAGE}\n"), result.report
