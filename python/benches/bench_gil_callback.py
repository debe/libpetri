"""Three-way callback overhead comparison on the same linear chain workload.

Goal: isolate the cost of re-entering Python on every transition fire.

The Rust-side built-in `lp.fork` action runs without the GIL during a chain
firing. A Python sync callback re-acquires the GIL (`Python::attach`) on every
fire and clones token references across the boundary. A Python async callback
additionally schedules a coroutine on the asyncio event loop through
`pyo3_async_runtimes::into_future_with_locals`.

For each chain length N we report:
- `bench_chain_fork[n]`        — `lp.fork` (Rust built-in, no GIL re-entry)
- `bench_chain_sync_callback[n]` — Python sync function as action
- `bench_chain_async_callback[n]` — Python async function as action

Read the numbers as:
- (sync_callback / fork) - 1  ≈ GIL re-acquire + Py token clone per fire
- (async_callback / sync) - 1 ≈ asyncio scheduling + future-into-py overhead per fire
"""

from __future__ import annotations

import asyncio
from collections.abc import Callable

import pytest

import libpetri as lp


def _build_chain(n: int, action) -> tuple[lp.BuiltNet, lp.Place, lp.Place]:
    """Build a linear chain of N transitions with a configurable action.

    `action` is either a callable (sync `def` or `async def`) or `lp.fork`.
    """
    places = [lp.Place(f"p{i}") for i in range(n + 1)]
    builder = lp.Net("gil_chain")
    for i in range(n):
        prev_name = f"p{i}"
        next_name = f"p{i + 1}"

        # Sync and async callbacks need a fresh closure binding for each
        # transition so they emit to the right output place name.
        if callable(action) and not isinstance(action, lp.BuiltinAction):
            if asyncio.iscoroutinefunction(action):
                cb = _make_async_passthrough(prev_name, next_name)
            else:
                cb = _make_sync_passthrough(prev_name, next_name)
        else:
            cb = action

        builder = builder.transition(
            lp.Transition(f"t{i}")
            .input(lp.one(places[i]))
            .output(lp.out(places[i + 1]))
            .action(cb)
            .build()
        )
    return builder.build(), places[0], places[n]


def _make_sync_passthrough(in_name: str, out_name: str) -> Callable:
    def passthrough(ctx) -> None:
        value = ctx.input(in_name)
        ctx.output(out_name, value)

    return passthrough


def _make_async_passthrough(in_name: str, out_name: str) -> Callable:
    async def passthrough(ctx) -> None:
        value = ctx.input(in_name)
        ctx.output(out_name, value)

    return passthrough


# Smaller N range than bench_executor.py — callbacks are slow enough that the
# 200/500 sizes blow past the 1 s per-bench budget.
N_VALUES = [5, 10, 20, 50, 100]


@pytest.mark.parametrize("n", N_VALUES)
def bench_chain_fork(benchmark, n) -> None:
    net, start, _end = _build_chain(n, lp.fork)
    compiled = lp.compile(net)
    benchmark(lambda: compiled.run_sync(initial={start: [{"id": 1}]}))


@pytest.mark.parametrize("n", N_VALUES)
def bench_chain_sync_callback(benchmark, n) -> None:
    # Pass a non-builtin sentinel — _build_chain rewrites per-transition closures.
    def sentinel(ctx):  # never invoked; per-transition closures replace this
        raise RuntimeError("sentinel called")

    net, start, _end = _build_chain(n, sentinel)
    compiled = lp.compile(net)
    benchmark(lambda: compiled.run_sync(initial={start: [{"id": 1}]}))


@pytest.mark.parametrize("n", N_VALUES)
def bench_chain_async_callback(benchmark_async, n) -> None:
    async def sentinel(ctx):  # likewise never invoked
        raise RuntimeError("sentinel called")

    net, start, _end = _build_chain(n, sentinel)
    compiled = lp.compile(net)
    benchmark_async(lambda: compiled.run_async(initial={start: [{"id": 1}]}))
