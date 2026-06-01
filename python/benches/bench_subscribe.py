"""Subscribe path throughput at unary mode (batch_size=1, batch_timeout_ms=0).

V4 target: ≥ 50k events/sec sustained at unary settings. Token-streaming
consumers (LLM chunk delivery, byte-stream injection) need per-event
delivery and can't tolerate batch-mode latency. This benchmark drives N
events through the subscribe path and reports sustained throughput.

Compare unary vs batched modes to quantify the GIL-acquire savings of
batching.
"""

from __future__ import annotations

import asyncio
import pytest

import libpetri as lp

pytestmark = pytest.mark.skipif(
    not lp.HAS_TOKIO,
    reason="wheel built without tokio async support",
)


def _build_streamer_net(n: int) -> tuple[lp.BuiltNet, lp.Place]:
    """Net with one transition that emits N tokens to `out` from a single
    firing. The subscriber drains them as `TokenAdded` events.
    """
    trigger = lp.Place("trigger")
    out = lp.Place("out")

    def emit_n(ctx: lp.TransitionContext) -> None:
        _ = ctx.input("trigger")
        for i in range(n):
            ctx.output("out", i)

    net = (
        lp.Net("streamer")
        .transition(
            lp.Transition("emit")
            .input(lp.one(trigger))
            .output(lp.out(out))
            .action(emit_n)
            .build()
        )
        .build()
    )
    return net, trigger


def bench_subscribe_stream_throughput(benchmark_async) -> None:
    """Streaming-mode subscription: one NetEvent per yield, no list wrapper.

    Compare against `bench_subscribe_throughput[unary]` to quantify the
    PyList-of-one savings. Same N, same filter.
    """
    n = 10_000
    net, trigger = _build_streamer_net(n)
    compiled = lp.compile(net)

    async def run_once() -> None:
        store = lp.InMemoryEventStore()
        sub = store.subscribe_stream(
            types={"TokenAdded"},
            places={"out"},
            channel_capacity=n + 1024,
        )

        async def drain_sub() -> int:
            count = 0
            async for _event in sub:
                count += 1
                if count >= n:
                    sub.close()
                    return count
            return count

        drain_task = asyncio.create_task(drain_sub())
        await compiled.run_async(
            initial={trigger: [{"go": True}]},
            event_store=store,
        )
        delivered = await drain_task
        assert delivered == n

    benchmark_async(run_once)


@pytest.mark.parametrize(
    "batch_size,batch_timeout_ms",
    [(1, 0), (16, 0), (64, 0), (256, 0)],
    ids=["unary", "batch16", "batch64", "batch256"],
)
def bench_subscribe_throughput(
    benchmark_async,
    batch_size: int,
    batch_timeout_ms: int,
) -> None:
    """Drives N=10_000 events through subscribe at the given batch
    settings. Mean wall time → events/sec."""
    n = 10_000
    net, trigger = _build_streamer_net(n)
    compiled = lp.compile(net)

    async def run_once() -> None:
        store = lp.InMemoryEventStore()
        sub = store.subscribe(
            types={"TokenAdded"},
            places={"out"},
            batch_size=batch_size,
            batch_timeout_ms=batch_timeout_ms,
            channel_capacity=n + 1024,
        )

        async def drain_sub() -> int:
            count = 0
            async for batch in sub:
                count += len(batch)
                if count >= n:
                    sub.close()
                    return count
            return count

        drain_task = asyncio.create_task(drain_sub())
        await compiled.run_async(
            initial={trigger: [{"go": True}]},
            event_store=store,
        )
        delivered = await drain_task
        assert delivered == n, f"delivered={delivered} expected={n}"

    benchmark_async(run_once)
