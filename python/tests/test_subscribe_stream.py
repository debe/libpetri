"""Smoke test for ``store.subscribe_stream(...)`` (V4 streaming mode).

Unlike ``subscribe(batch_size=1)`` — which yields ``list[NetEvent]`` of
length 1 per ``__anext__`` — ``subscribe_stream`` yields a single
``NetEvent``. Same channel-capacity semantics, same filter.
"""

from __future__ import annotations

import asyncio

import pytest

import libpetri as lp

pytestmark = pytest.mark.skipif(
    not lp.HAS_TOKIO,
    reason="wheel built without tokio async support",
)


@pytest.mark.asyncio
async def test_subscribe_stream_yields_single_events() -> None:
    trigger = lp.Place("trigger")
    out = lp.Place("out")

    def emit_three(ctx: lp.TransitionContext) -> None:
        _ = ctx.input("trigger")
        for i in range(3):
            ctx.output("out", i)

    net = (
        lp.Net("stream")
        .transition(
            lp.Transition("emit")
            .input(lp.one(trigger))
            .output(lp.out(out))
            .action(emit_three)
            .build()
        )
        .build()
    )

    store = lp.InMemoryEventStore()
    sub = store.subscribe_stream(
        types={"TokenAdded"},
        places={"out"},
        channel_capacity=64,
    )

    events: list = []

    async def drain() -> None:
        async for event in sub:
            events.append(event)
            if len(events) == 3:
                sub.close()
                return

    drain_task = asyncio.create_task(drain())
    await lp.run_async(net, initial={trigger: [{"go": True}]}, event_store=store)
    await drain_task

    assert len(events) == 3
    # Each item is a single NetEvent (not a list-of-one).
    assert all(isinstance(e, lp.NetEvent) for e in events)
    assert all(e.type == "TokenAdded" for e in events)
    assert all(e.place_name == "out" for e in events)


@pytest.mark.asyncio
async def test_subscribe_stream_close_stops_iteration() -> None:
    store = lp.InMemoryEventStore()
    sub = store.subscribe_stream(types={"TokenAdded"}, channel_capacity=8)
    sub.close()
    # After close, async iteration ends immediately on first __anext__.
    async for _ev in sub:
        pytest.fail("stream should be closed")


def test_subscribe_stream_rejects_zero_channel_capacity() -> None:
    store = lp.InMemoryEventStore()
    with pytest.raises(ValueError, match="channel_capacity"):
        store.subscribe_stream(channel_capacity=0)
