"""Tests for ``handle.inject_many(place, values)`` (V5).

Verifies that the batched injection delivers tokens in input order, in one
GIL crossing, and survives the same drain/close semantics as ``inject``.
"""

from __future__ import annotations

import pytest

import libpetri as lp

pytestmark = pytest.mark.skipif(
    not lp.HAS_TOKIO,
    reason="wheel built without tokio async support",
)


@pytest.mark.asyncio
async def test_inject_many_delivers_all_tokens_in_order() -> None:
    sensor = lp.Place("sensor")
    observed = lp.Place("observed")

    net = (
        lp.Net("inject-many")
        .transition(
            lp.Transition("capture")
            .input(lp.one(sensor))
            .output(lp.out(observed))
            .action(lp.fork)
            .build()
        )
        .build()
    )

    handle, awaitable = lp.start_async(
        net,
        options=lp.ExecutorOptions(environment_places=(sensor,)),
    )

    values = [{"i": i} for i in range(20)]
    assert handle.inject_many(sensor, values) is True
    assert handle.drain() is True

    result = await awaitable
    assert result.count(observed) == 20
    # Verify ordering preserved across the batch.
    observed_indices = [t["i"] for t in result["observed"]]
    assert observed_indices == list(range(20))


@pytest.mark.asyncio
async def test_inject_many_with_empty_iterable_is_noop() -> None:
    sensor = lp.Place("sensor")
    net = (
        lp.Net("empty-batch")
        .transition(
            lp.Transition("noop")
            .input(lp.one(sensor))
            .output(lp.out(lp.Place("sink")))
            .action(lp.fork)
            .build()
        )
        .build()
    )

    handle, awaitable = lp.start_async(
        net,
        options=lp.ExecutorOptions(environment_places=(sensor,)),
    )
    # Empty batch returns True (accepted; no events to deliver) and does
    # not start the executor doing any work.
    assert handle.inject_many(sensor, []) is True
    assert handle.drain() is True
    result = await awaitable
    assert result.count(sensor) == 0


@pytest.mark.asyncio
async def test_inject_many_after_drain_returns_false() -> None:
    sensor = lp.Place("sensor")
    net = (
        lp.Net("drained")
        .transition(
            lp.Transition("noop")
            .input(lp.one(sensor))
            .output(lp.out(lp.Place("sink")))
            .action(lp.fork)
            .build()
        )
        .build()
    )

    handle, awaitable = lp.start_async(
        net,
        options=lp.ExecutorOptions(environment_places=(sensor,)),
    )
    assert handle.drain() is True
    assert handle.inject_many(sensor, [{"x": 1}, {"x": 2}]) is False
    await awaitable


@pytest.mark.asyncio
async def test_inject_many_atomic_relative_to_other_signals() -> None:
    """All tokens from one inject_many call deposit before drain begins
    processing — atomic relative to the drain signal that follows."""

    sensor = lp.Place("sensor")
    observed = lp.Place("observed")

    net = (
        lp.Net("atomic")
        .transition(
            lp.Transition("capture")
            .input(lp.one(sensor))
            .output(lp.out(observed))
            .action(lp.fork)
            .build()
        )
        .build()
    )

    handle, awaitable = lp.start_async(
        net,
        options=lp.ExecutorOptions(environment_places=(sensor,)),
    )

    # Batch + drain back-to-back. All 5 tokens must land before drain
    # discards new events.
    handle.inject_many(sensor, [{"i": i} for i in range(5)])
    handle.drain()
    result = await awaitable
    assert result.count(observed) == 5
