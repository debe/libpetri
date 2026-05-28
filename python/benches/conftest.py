"""Shared fixtures for the libpetri Python benchmark suite.

Mirrors the helpers in `rust/benches/benches/executor.rs` (build_linear_chain,
build_fan_out, build_complex_workflow). All fixtures return built nets paired
with the relevant places, so bench files can populate initial markings
without re-deriving place handles.
"""

from __future__ import annotations

import asyncio
from collections.abc import Callable

import pytest

import libpetri as lp


def _build_linear_chain(n: int) -> tuple[lp.BuiltNet, lp.Place, lp.Place]:
    """Linear chain of N fork transitions, mirroring Rust `build_linear_chain`."""
    places = [lp.Place(f"p{i}") for i in range(n + 1)]
    builder = lp.Net("chain")
    for i in range(n):
        builder = builder.transition(
            lp.Transition(f"t{i}")
            .input(lp.one(places[i]))
            .output(lp.out(places[i + 1]))
            .action(lp.fork)
            .build()
        )
    return builder.build(), places[0], places[n]


def _build_fan_out(fan: int) -> tuple[lp.BuiltNet, lp.Place, lp.Place]:
    """Fan-out -> fan-in topology, mirroring Rust `build_fan_out`."""
    start = lp.Place("start")
    end = lp.Place("end")
    mids = [lp.Place(f"mid{i}") for i in range(fan)]

    builder = lp.Net("fan_out")
    for i, m in enumerate(mids):
        builder = builder.transition(
            lp.Transition(f"fan_out_{i}")
            .input(lp.one(start))
            .output(lp.out(m))
            .action(lp.fork)
            .build()
        )
    for i, m in enumerate(mids):
        builder = builder.transition(
            lp.Transition(f"fan_in_{i}")
            .input(lp.one(m))
            .output(lp.out(end))
            .action(lp.fork)
            .build()
        )
    return builder.build(), start, end


def _build_complex_workflow() -> tuple[lp.BuiltNet, lp.Place, lp.Place]:
    """8-transition / 13-place workflow with XOR, inhibitors, priorities, read arcs.

    Structurally mirrors the Rust `build_complex_workflow` benchmark target.
    Uses ``fork`` for actions to keep the Python side free of callback overhead.
    """
    input_p = lp.Place("input")
    intent_in = lp.Place("input_intent")
    topic_in = lp.Place("input_topic")
    search_in = lp.Place("input_search")
    guard_state = lp.Place("guard_state")
    guard_safe = lp.Place("guard_safe")
    guard_violation = lp.Place("guard_violation")
    intent_done = lp.Place("intent_done")
    topic_done = lp.Place("topic_done")
    search_done = lp.Place("search_done")
    output_guard_in = lp.Place("output_guard_in")
    output_guard_done = lp.Place("output_guard_done")
    response = lp.Place("response")

    fork_trans = (
        lp.Transition("fork")
        .input(lp.one(input_p))
        .output(
            lp.and_(
                lp.out(intent_in),
                lp.out(topic_in),
                lp.out(search_in),
                lp.out(output_guard_in),
            )
        )
        .action(lp.fork)
        .build()
    )
    guard_trans = (
        lp.Transition("guard_check")
        .input(lp.one(input_p))
        .read(lp.read(guard_state))
        .inhibitor(lp.inhibitor(guard_violation))
        .output(lp.out(guard_safe))
        .action(lp.fork)
        .build()
    )
    handle_violation = (
        lp.Transition("handle_violation")
        .input(lp.one(input_p))
        .input(lp.one(guard_violation))
        .inhibitor(lp.inhibitor(guard_safe))
        .output(lp.out(response))
        .priority(-5)
        .action(lp.fork)
        .build()
    )
    intent_trans = (
        lp.Transition("intent")
        .input(lp.one(intent_in))
        .output(lp.out(intent_done))
        .action(lp.fork)
        .build()
    )
    topic_trans = (
        lp.Transition("topic")
        .input(lp.one(topic_in))
        .output(lp.out(topic_done))
        .action(lp.fork)
        .build()
    )
    search_trans = (
        lp.Transition("search")
        .input(lp.one(search_in))
        .output(lp.out(search_done))
        .action(lp.fork)
        .build()
    )
    output_guard_trans = (
        lp.Transition("output_guard")
        .input(lp.one(output_guard_in))
        .read(lp.read(guard_safe))
        .output(lp.out(output_guard_done))
        .action(lp.fork)
        .build()
    )
    compose_trans = (
        lp.Transition("compose")
        .input(lp.one(intent_done))
        .input(lp.one(topic_done))
        .input(lp.one(search_done))
        .output(lp.out(response))
        .priority(10)
        .action(lp.fork)
        .build()
    )

    net = (
        lp.Net("complex_workflow")
        .transition(fork_trans)
        .transition(guard_trans)
        .transition(handle_violation)
        .transition(intent_trans)
        .transition(topic_trans)
        .transition(search_trans)
        .transition(output_guard_trans)
        .transition(compose_trans)
        .build()
    )
    return net, input_p, response


@pytest.fixture
def linear_chain_net() -> Callable[[int], tuple[lp.BuiltNet, lp.Place, lp.Place]]:
    return _build_linear_chain


@pytest.fixture
def fan_out_net() -> Callable[[int], tuple[lp.BuiltNet, lp.Place, lp.Place]]:
    return _build_fan_out


@pytest.fixture
def complex_workflow_net() -> tuple[lp.BuiltNet, lp.Place, lp.Place]:
    return _build_complex_workflow()


@pytest.fixture
def benchmark_async(benchmark):
    """Bench wrapper that drives an async coroutine factory on a dedicated event loop.

    pytest-benchmark itself only times synchronous callables, and pytest-asyncio's
    `asyncio_mode = "auto"` interferes with benchmark fixtures. This helper isolates
    a private event loop, runs the coroutine via `run_until_complete` inside the
    benchmark callable, and tears down at the end so the loop isn't shared across
    parametrized cases.
    """
    loop = asyncio.new_event_loop()

    def _run(coro_factory: Callable[[], object]) -> object:
        return benchmark(lambda: loop.run_until_complete(coro_factory()))

    try:
        yield _run
    finally:
        loop.close()
