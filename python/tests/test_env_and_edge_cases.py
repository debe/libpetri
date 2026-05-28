"""Environment-place injection and edge cases (empty nets, large markings).

Mirrors Java `EnvironmentPlaceTests` / `ConcurrentInjectionTests` and Rust
async signal handling in `precompiled_executor.rs`.
"""

from __future__ import annotations

import asyncio

import pytest

import libpetri as lp


def test_empty_net_with_no_initial_marking_returns_empty() -> None:
    net = lp.Net("empty").build()

    result = lp.run_sync(net)

    assert len(result) == 0


def test_single_place_no_transitions_keeps_initial_tokens() -> None:
    only = lp.Place("only")
    net = lp.Net("static").place(only).build()

    result = lp.run_sync(net, initial={only: [{"id": 1}, {"id": 2}]})

    assert result.count(only) == 2


def test_large_initial_marking_processed_through_one_transition() -> None:
    queued = lp.Place("queued")
    done = lp.Place("done")

    net = (
        lp.Net("large")
        .transition(
            lp.Transition("forward")
            .input(lp.one(queued))
            .output(lp.out(done))
            .action(lp.fork)
            .build()
        )
        .build()
    )

    token_count = 200
    initial = [{"i": i} for i in range(token_count)]

    result = lp.run_sync(net, initial={queued: initial})

    assert result.count(done) == token_count
    assert result.count(queued) == 0


# ---------- environment place injection --------------------------------


@pytest.mark.skipif(
    not lp.HAS_TOKIO,
    reason="env-place injection requires the async runtime",
)
@pytest.mark.asyncio
async def test_env_place_injection_wakes_sleeping_executor() -> None:
    sensor = lp.Place("sensor")
    captured = lp.Place("captured")

    net = (
        lp.Net("env-wake")
        .transition(
            lp.Transition("capture")
            .input(lp.one(sensor))
            .output(lp.out(captured))
            .action(lp.fork)
            .build()
        )
        .build()
    )

    handle, awaitable = lp.start_async(
        net,
        options=lp.ExecutorOptions(environment_places=(sensor,)),
    )

    # Executor starts idle; injection should wake it.
    await asyncio.sleep(0.02)
    assert handle.inject(sensor, {"reading": 99}) is True
    assert handle.drain() is True

    result = await awaitable

    assert result.count(captured) == 1
    assert result.first(captured)["reading"] == 99


@pytest.mark.skipif(
    not lp.HAS_TOKIO,
    reason="env-place injection requires the async runtime",
)
@pytest.mark.asyncio
async def test_multiple_injections_on_env_place_all_processed() -> None:
    sensor = lp.Place("sensor")
    captured = lp.Place("captured")

    net = (
        lp.Net("env-multi")
        .transition(
            lp.Transition("capture")
            .input(lp.one(sensor))
            .output(lp.out(captured))
            .action(lp.fork)
            .build()
        )
        .build()
    )

    handle, awaitable = lp.start_async(
        net,
        options=lp.ExecutorOptions(environment_places=(sensor,)),
    )

    for i in range(5):
        assert handle.inject(sensor, {"i": i}) is True
    handle.drain()

    result = await awaitable

    assert result.count(captured) == 5
