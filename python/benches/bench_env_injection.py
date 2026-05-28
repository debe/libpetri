"""Environment-place injection throughput.

Real production users hit this path on every sensor event / inbound webhook /
message-queue arrival: a long-lived async-executing net with one or more
environment places, where Python code injects tokens via
`ExecutorHandle.inject(place, value)`.

The benchmark measures the per-token cost end-to-end:
  Python -> ExecutorHandle::inject -> Rust mpsc send -> executor wakeup ->
  transition fire (with lp.fork action) -> token in sink.

Throughput = N / total_time. Lower is better per-token; higher is better as
events/second.
"""

from __future__ import annotations

import pytest

import libpetri as lp

pytestmark = pytest.mark.skipif(
    not lp.HAS_TOKIO,
    reason="wheel built without tokio async support",
)


def _build_injection_net() -> tuple[lp.BuiltNet, lp.Place, lp.Place]:
    sensor = lp.Place("sensor")
    sink = lp.Place("sink")
    net = (
        lp.Net("env_injection")
        .transition(
            lp.Transition("absorb")
            .input(lp.one(sensor))
            .output(lp.out(sink))
            .action(lp.fork)
            .build()
        )
        .build()
    )
    return net, sensor, sink


@pytest.mark.parametrize("n", [100, 1000, 10000])
def bench_inject_throughput(benchmark_async, n) -> None:
    net, sensor, _sink = _build_injection_net()
    compiled = lp.compile(net)

    async def run_once() -> None:
        handle, awaitable = compiled.start_async(
            options=lp.ExecutorOptions(environment_places=(sensor,)),
        )
        for i in range(n):
            handle.inject(sensor, {"event_id": i})
        handle.drain()
        await awaitable

    benchmark_async(run_once)
