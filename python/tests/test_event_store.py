"""EventStore + NetEvent — Tier A (post-hoc), Tier B (live), Tier C (aggregates).

Per the libpetri-py 2.7.0 plan: the event store implementation lives in Rust;
Python crosses the GIL only for filtered/batched reads. These tests cover the
three tiers and the langgraph-style streaming pattern.
"""

from __future__ import annotations

import asyncio

import pytest

import libpetri as lp

requires_tokio = pytest.mark.skipif(
    not lp.HAS_TOKIO, reason="async event-store path requires tokio"
)


def _build_chain() -> tuple[lp.Place, lp.Place, lp.BuiltNet]:
    p_in = lp.Place("p_in")
    p_out = lp.Place("p_out")
    net = (
        lp.Net("chain")
        .transition(
            lp.Transition("t1")
            .input(lp.one(p_in))
            .output(lp.out(p_out))
            .action(lp.fork)
            .build()
        )
        .build()
    )
    return p_in, p_out, net


# ---------------------------------------------------------------------------
# Tier A — post-hoc reads
# ---------------------------------------------------------------------------


def test_event_store_records_run() -> None:
    p_in, p_out, net = _build_chain()
    store = lp.InMemoryEventStore()
    assert len(store) == 0

    lp.run_sync(net, initial={p_in: ["v"]}, event_store=store)

    # Recorded *something*. We don't pin the exact 13-variant set because
    # event emission ordering is an implementation detail — the spec only
    # mandates which events fire, not their interleaving.
    assert len(store) > 0


def test_event_store_filters_by_type() -> None:
    p_in, _p_out, net = _build_chain()
    store = lp.InMemoryEventStore()
    lp.run_sync(net, initial={p_in: ["v"]}, event_store=store)

    started = store.events(types={"TransitionStarted"})
    completed = store.events(types={"TransitionCompleted"})

    assert all(ev.type == "TransitionStarted" for ev in started)
    assert all(ev.type == "TransitionCompleted" for ev in completed)
    assert len(started) >= 1 and len(completed) >= 1


def test_event_store_filters_by_transition() -> None:
    p_in, _p_out, net = _build_chain()
    store = lp.InMemoryEventStore()
    lp.run_sync(net, initial={p_in: ["v"]}, event_store=store)

    t1_events = store.events(transitions={"t1"})
    assert len(t1_events) >= 2  # at least started + completed
    assert all(ev.transition_name == "t1" for ev in t1_events)

    # No transition named "nope" — empty list.
    assert store.events(transitions={"nope"}) == []


def test_event_store_filters_by_place_for_token_events() -> None:
    p_in, _p_out, net = _build_chain()
    store = lp.InMemoryEventStore()
    lp.run_sync(net, initial={p_in: ["v"]}, event_store=store)

    p_out_token_events = store.events(
        types={"TokenAdded", "TokenRemoved"}, places={"p_out"}
    )
    # At least one TokenAdded into p_out from the firing.
    assert any(ev.type == "TokenAdded" for ev in p_out_token_events)
    assert all(ev.place_name == "p_out" for ev in p_out_token_events)


def test_event_store_limit_and_offset() -> None:
    p_in, _p_out, net = _build_chain()
    store = lp.InMemoryEventStore()
    lp.run_sync(net, initial={p_in: ["v"]}, event_store=store)

    all_events = store.events()
    if len(all_events) < 3:
        pytest.skip("net produced too few events for slicing test")

    first_two = store.events(limit=2)
    skip_one = store.events(offset=1, limit=2)

    assert len(first_two) == 2
    assert len(skip_one) == 2
    assert first_two[1].timestamp == skip_one[0].timestamp


def test_event_payload_lazy_dict() -> None:
    p_in, _p_out, net = _build_chain()
    store = lp.InMemoryEventStore()
    lp.run_sync(net, initial={p_in: ["v"]}, event_store=store)

    [started] = store.events(types={"TransitionStarted"})
    payload = started.payload()
    assert payload["transition_name"] == "t1"
    assert isinstance(payload["timestamp"], int)


def test_event_store_count_matches_filtered_events_len() -> None:
    p_in, _p_out, net = _build_chain()
    store = lp.InMemoryEventStore()
    lp.run_sync(net, initial={p_in: ["v"]}, event_store=store)

    assert store.count() == len(store)
    assert store.count(types={"TransitionStarted"}) == len(
        store.events(types={"TransitionStarted"})
    )


# ---------------------------------------------------------------------------
# Tier C — Rust-side aggregates
# ---------------------------------------------------------------------------


def test_counters_histogram() -> None:
    p_in, _p_out, net = _build_chain()
    store = lp.InMemoryEventStore()
    lp.run_sync(net, initial={p_in: ["v"]}, event_store=store)

    counters = store.counters()
    assert counters.get("TransitionStarted", 0) >= 1
    assert counters.get("TransitionCompleted", 0) >= 1
    assert sum(counters.values()) == len(store)


def test_failures_filters_failure_variants() -> None:
    p_in, _p_out, net = _build_chain()
    store = lp.InMemoryEventStore()
    lp.run_sync(net, initial={p_in: ["v"]}, event_store=store)

    # Happy-path chain produces no failures.
    assert store.failures() == []


# ---------------------------------------------------------------------------
# Tier B — live subscriptions
# ---------------------------------------------------------------------------


@requires_tokio
@pytest.mark.asyncio
async def test_subscribe_batched_delivery_for_async_run() -> None:
    p_env = lp.Place("p_env")
    p_done = lp.Place("p_done")
    net = (
        lp.Net("env-stream")
        .transition(
            lp.Transition("forward")
            .input(lp.one(p_env))
            .output(lp.out(p_done))
            .action(lp.fork)
            .build()
        )
        .build()
    )
    options = lp.ExecutorOptions(environment_places=(p_env,))
    store = lp.InMemoryEventStore()

    handle, awaitable = lp.start_async(net, options=options, event_store=store)
    sub = store.subscribe(
        types={"TransitionCompleted"},
        batch_size=4,
        batch_timeout_ms=50,
    )

    async def producer():
        for i in range(8):
            handle.inject(p_env, f"chunk-{i}")
            await asyncio.sleep(0.001)
        await asyncio.sleep(0.02)  # let last events drain through filter
        handle.drain()

    async def consumer():
        received = []
        async for batch in sub:
            received.extend(batch)
            if len(received) >= 8:
                break
        return received

    producer_task = asyncio.create_task(producer())
    received = await asyncio.wait_for(consumer(), timeout=2.0)
    await producer_task
    await awaitable

    assert len(received) == 8
    assert all(ev.type == "TransitionCompleted" for ev in received)


@requires_tokio
@pytest.mark.asyncio
async def test_subscribe_unary_mode_delivers_per_event() -> None:
    """`batch_size=1, batch_timeout_ms=0` — the langgraph stream_mode='messages' shape."""
    p_env = lp.Place("p_env")
    p_done = lp.Place("p_done")
    net = (
        lp.Net("unary-stream")
        .transition(
            lp.Transition("tok")
            .input(lp.one(p_env))
            .output(lp.out(p_done))
            .action(lp.fork)
            .build()
        )
        .build()
    )
    options = lp.ExecutorOptions(environment_places=(p_env,))
    store = lp.InMemoryEventStore()

    handle, awaitable = lp.start_async(net, options=options, event_store=store)
    sub = store.subscribe(
        types={"TokenAdded"},
        places={"p_done"},
        batch_size=1,
        batch_timeout_ms=0,
    )

    async def produce():
        for i in range(3):
            handle.inject(p_env, f"t{i}")
            await asyncio.sleep(0.005)
        await asyncio.sleep(0.02)
        handle.drain()

    async def consume():
        batches = []
        async for batch in sub:
            batches.append(batch)
            if len(batches) >= 3:
                break
        return batches

    prod_task = asyncio.create_task(produce())
    batches = await asyncio.wait_for(consume(), timeout=2.0)
    await prod_task
    await awaitable

    # Each batch has exactly one event under unary mode.
    assert all(len(batch) == 1 for batch in batches)
    assert len(batches) == 3


@requires_tokio
@pytest.mark.asyncio
async def test_subscribe_filter_by_transition_excludes_others() -> None:
    p_env = lp.Place("p_env")
    p_mid = lp.Place("p_mid")
    p_done = lp.Place("p_done")
    net = (
        lp.Net("two-stage")
        .transition(
            lp.Transition("stage_a")
            .input(lp.one(p_env))
            .output(lp.out(p_mid))
            .action(lp.fork)
            .build()
        )
        .transition(
            lp.Transition("stage_b")
            .input(lp.one(p_mid))
            .output(lp.out(p_done))
            .action(lp.fork)
            .build()
        )
        .build()
    )
    options = lp.ExecutorOptions(environment_places=(p_env,))
    store = lp.InMemoryEventStore()
    handle, awaitable = lp.start_async(net, options=options, event_store=store)
    sub = store.subscribe(
        types={"TransitionCompleted"},
        transitions={"stage_b"},
        batch_size=1,
        batch_timeout_ms=0,
    )

    async def produce():
        handle.inject(p_env, "in")
        await asyncio.sleep(0.05)
        handle.drain()

    async def consume():
        async for batch in sub:
            return batch
        return []

    prod_task = asyncio.create_task(produce())
    batch = await asyncio.wait_for(consume(), timeout=2.0)
    await prod_task
    await awaitable

    assert len(batch) == 1
    assert batch[0].transition_name == "stage_b"


@requires_tokio
def test_subscribe_rejects_batch_size_zero() -> None:
    store = lp.InMemoryEventStore()
    with pytest.raises(ValueError):
        store.subscribe(batch_size=0)


def test_event_store_clone_handles_share_storage() -> None:
    """Two references to the same handle see the same events."""
    p_in, _p_out, net = _build_chain()
    store_a = lp.InMemoryEventStore()
    lp.run_sync(net, initial={p_in: ["v"]}, event_store=store_a)
    # The store is reference-shared via Arc on the Rust side; passing the
    # same handle to a second run accumulates events.
    lp.run_sync(net, initial={p_in: ["w"]}, event_store=store_a)
    counters = store_a.counters()
    assert counters.get("ExecutionStarted", 0) == 2


# ---------------------------------------------------------------------------
# Tier B — subscription lifecycle edge cases
# ---------------------------------------------------------------------------


@requires_tokio
@pytest.mark.asyncio
async def test_subscribe_after_completion_is_forward_only() -> None:
    """A subscription created after the run is forward-only — no replay.

    Past events are not re-delivered, so the first batch never arrives and a
    bounded wait times out. (A replaying subscription would return instantly.)
    """
    p_in, _p_out, net = _build_chain()
    store = lp.InMemoryEventStore()
    lp.run_sync(net, initial={p_in: ["v"]}, event_store=store)
    assert len(store) > 0

    sub = store.subscribe(batch_size=1, batch_timeout_ms=0)

    async def first_batch():
        async for batch in sub:
            return batch
        return None

    with pytest.raises(asyncio.TimeoutError):
        await asyncio.wait_for(first_batch(), timeout=0.1)
    sub.close()


@requires_tokio
@pytest.mark.asyncio
async def test_subscription_close_before_iteration_stops_cleanly() -> None:
    """close() before iterating makes the async-for terminate immediately."""
    store = lp.InMemoryEventStore()
    sub = store.subscribe(batch_size=1, batch_timeout_ms=0)
    sub.close()

    collected = []

    async def consume():
        async for batch in sub:
            collected.extend(batch)
        return "stopped"

    assert await asyncio.wait_for(consume(), timeout=2.0) == "stopped"
    assert collected == []
