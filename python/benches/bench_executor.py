"""Executor scenarios mirroring `rust/benches/benches/executor.rs`.

All scenarios here use `lp.fork` as the action, so the benchmark crosses the
FFI boundary (Python -> Rust executor) but does *not* re-enter Python during
execution. The Phase 3 GIL-bridge benches add the same scenarios with Python
sync/async callbacks to isolate the GIL cost.

Match Rust IDs (modulo the `precompiled_*` / `owned_*` prefix the Rust side
uses). E.g. `test_sync_linear_chain[100]` lines up with Rust
`owned_sync_linear_chain/100`.
"""

from __future__ import annotations

import pytest

import libpetri as lp


def test_single_passthrough(benchmark) -> None:
    p1 = lp.Place("p1")
    p2 = lp.Place("p2")
    net = (
        lp.Net("single")
        .transition(
            lp.Transition("t1")
            .input(lp.one(p1))
            .output(lp.out(p2))
            .action(lp.fork)
            .build()
        )
        .build()
    )
    compiled = lp.compile(net)
    benchmark(lambda: compiled.run_sync(initial={p1: [42]}))


@pytest.mark.parametrize("n", [5, 10, 20, 50, 100, 200, 500])
def test_sync_linear_chain(benchmark, linear_chain_net, n) -> None:
    net, start, _end = linear_chain_net(n)
    compiled = lp.compile(net)
    benchmark(lambda: compiled.run_sync(initial={start: [1]}))


@pytest.mark.parametrize("fan", [5, 10, 20])
def test_parallel_fan_out(benchmark, fan_out_net, fan) -> None:
    net, start, _end = fan_out_net(fan)
    compiled = lp.compile(net)
    benchmark(lambda: compiled.run_sync(initial={start: [1] * fan}))


@pytest.mark.parametrize("n", [5, 10, 20, 50, 100, 200, 500])
def test_async_linear_chain(benchmark_async, linear_chain_net, n) -> None:
    net, start, _end = linear_chain_net(n)
    compiled = lp.compile(net)
    benchmark_async(lambda: compiled.run_async(initial={start: [1]}))


@pytest.mark.parametrize("fan", [5, 10, 20])
def test_async_fan_out(benchmark_async, fan_out_net, fan) -> None:
    net, start, _end = fan_out_net(fan)
    compiled = lp.compile(net)
    benchmark_async(lambda: compiled.run_async(initial={start: [1] * fan}))


def test_complex_workflow_8t_13p(benchmark, complex_workflow_net) -> None:
    net, start, _response = complex_workflow_net
    compiled = lp.compile(net)
    # guard_state read arc needs a token to allow the guard_check transition.
    benchmark(
        lambda: compiled.run_sync(
            initial={start: [1], "guard_state": [{"safe": True}]},
        )
    )
