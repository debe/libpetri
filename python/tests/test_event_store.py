"""EventStore + NetEvent — Tier A (post-hoc), Tier B (live), Tier C (aggregates).

Per the libpetri-py 2.7.0 plan: the event store implementation lives in Rust;
Python crosses the GIL only for filtered/batched reads. These tests cover the
three tiers and the langgraph-style streaming pattern.
"""

from __future__ import annotations

import asyncio
import logging
import time

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


def test_counters_histogram_is_ordered_independently_of_the_process() -> None:
    """`counters()` lands in a Python dict — an ordered medium — so the event
    types come back in ascending order, not in the order a per-process seeded
    hash map happens to yield. ``list(...)``: dict equality ignores order."""
    p_in, p_out = lp.Place("p_in"), lp.Place("p_out")
    net = (
        lp.Net("hist")
        .transition(
            lp.Transition("t").input(lp.one(p_in)).output(lp.out(p_out)).action(lp.fork).build()
        )
        .build()
    )
    store = lp.InMemoryEventStore()
    lp.run_sync(net, initial={p_in: ["v"]}, event_store=store)

    kinds = list(store.counters())
    assert len(kinds) >= 5, f"too few event types to order: {kinds}"
    assert kinds == sorted(kinds)


# ---------------------------------------------------------------------------
# Event stores written in Python, and token capture
# ---------------------------------------------------------------------------


class RecordingStore:
    """A Python event store: records every event it is handed."""

    def __init__(self, *, captures_tokens=None, delay_s: float = 0.0) -> None:
        self.events: list[lp.NetEvent] = []
        self.delay_s = delay_s
        if captures_tokens is not None:
            self.captures_tokens = captures_tokens

    def append(self, event: lp.NetEvent) -> None:
        if self.delay_s:
            time.sleep(self.delay_s)
        self.events.append(event)


def _shape(events) -> list[tuple[str, str | None, str | None]]:
    return [(e.type, e.transition_name, e.place_name) for e in events]


def _async_chain() -> tuple[lp.Place, lp.Place, lp.BuiltNet]:
    p_env = lp.Place("p_env")
    p_done = lp.Place("p_done")
    net = (
        lp.Net("env-chain")
        .transition(
            lp.Transition("forward")
            .input(lp.one(p_env))
            .output(lp.out(p_done))
            .action(lp.fork)
            .build()
        )
        .build()
    )
    return p_env, p_done, net


def test_python_store_receives_the_in_memory_events_in_order() -> None:
    p_in, _p_out, net = _build_chain()
    reference = lp.InMemoryEventStore()
    lp.run_sync(net, initial={p_in: ["v"]}, event_store=reference)
    store = RecordingStore()
    lp.run_sync(net, initial={p_in: ["v"]}, event_store=store)

    assert isinstance(store, lp.EventStoreProtocol)
    assert len(store.events) == len(reference) > 0
    assert _shape(store.events) == _shape(reference.events())
    assert store.events[-1].type == "ExecutionCompleted"


@requires_tokio
async def test_python_store_receives_the_in_memory_events_in_order_async() -> None:
    p_in, _p_out, net = _build_chain()
    reference = lp.InMemoryEventStore()
    await lp.run_async(net, initial={p_in: ["v"]}, event_store=reference)
    store = RecordingStore()
    await lp.run_async(net, initial={p_in: ["v"]}, event_store=store)

    assert len(store.events) == len(reference) > 0
    assert _shape(store.events) == _shape(reference.events())


def test_python_store_chain_ends_in_in_memory_store() -> None:
    class Counting:
        def __init__(self, inner) -> None:
            self.inner = inner
            self.seen = 0

        def append(self, event) -> None:
            self.seen += 1
            self.inner.append(event)

    p_in, _p_out, net = _build_chain()
    inner = lp.InMemoryEventStore()
    outer = Counting(inner)
    lp.run_sync(net, initial={p_in: ["v"]}, event_store=outer)

    reference = lp.InMemoryEventStore()
    lp.run_sync(net, initial={p_in: ["v"]}, event_store=reference)
    assert outer.seen == len(inner) == len(reference)
    assert _shape(inner.events()) == _shape(reference.events())
    assert inner.counters() == reference.counters()


def test_python_store_disabled_receives_nothing() -> None:
    class Disabled(RecordingStore):
        def is_enabled(self) -> bool:
            return False

    p_in, p_out, net = _build_chain()
    store = Disabled()
    result = lp.run_sync(net, initial={p_in: ["v"]}, event_store=store)
    assert result.tokens(p_out) == ("v",)
    assert store.events == []


def test_event_store_without_append_is_a_type_error() -> None:
    p_in, _p_out, net = _build_chain()
    with pytest.raises(TypeError, match="append"):
        lp.run_sync(net, initial={p_in: ["v"]}, event_store=object())

    class NotCallable:
        append = 3

    with pytest.raises(TypeError, match="append"):
        lp.run_sync(net, initial={p_in: ["v"]}, event_store=NotCallable())


def test_capture_tokens_rejects_a_bare_string() -> None:
    with pytest.raises(TypeError):
        lp.InMemoryEventStore(capture_tokens="p_in")


class Raising(RecordingStore):
    def append(self, event) -> None:
        if event.type == "TransitionStarted":
            raise RuntimeError("store failed")
        super().append(event)


def test_raising_python_store_is_logged_and_not_fatal_sync(caplog) -> None:
    p_in, p_out, net = _build_chain()
    store = Raising()
    with caplog.at_level(logging.ERROR, logger="libpetri"):
        result = lp.run_sync(net, initial={p_in: ["v"]}, event_store=store)

    assert result.tokens(p_out) == ("v",)
    assert "TransitionStarted" not in {e.type for e in store.events}
    assert store.events[-1].type == "ExecutionCompleted"
    [record] = [r for r in caplog.records if r.name == "libpetri"]
    assert record.exc_info is not None
    assert isinstance(record.exc_info[1], RuntimeError)


@requires_tokio
async def test_raising_python_store_is_exposed_on_the_handle() -> None:
    p_in, p_out, net = _build_chain()
    store = Raising()
    handle, awaitable = lp.start_async(net, initial={p_in: ["v"]}, event_store=store)
    result = await awaitable

    assert result.tokens(p_out) == ("v",)
    err = handle.event_store_error
    assert isinstance(err, RuntimeError)
    assert str(err) == "store failed"
    # Delivery went on after the failure.
    assert store.events[-1].type == "ExecutionCompleted"


@requires_tokio
async def test_event_store_error_is_none_without_failures() -> None:
    p_in, _p_out, net = _build_chain()
    handle, awaitable = lp.start_async(
        net, initial={p_in: ["v"]}, event_store=RecordingStore()
    )
    await awaitable
    assert handle.event_store_error is None


@requires_tokio
async def test_every_event_is_delivered_before_the_run_resolves() -> None:
    """A slow store must still hold every event once `await run` returns:
    the run waits for the drainer before resolving."""
    p_in, _p_out, net = _build_chain()
    reference = lp.InMemoryEventStore()
    await lp.run_async(net, initial={p_in: ["v"]}, event_store=reference)

    store = RecordingStore(delay_s=0.02)
    await lp.run_async(net, initial={p_in: ["v"]}, event_store=store)
    assert len(store.events) == len(reference)
    assert store.events[-1].type == "ExecutionCompleted"


def test_in_memory_capture_tokens_true_carries_the_same_object() -> None:
    p_in, _p_out, net = _build_chain()
    token = object()
    store = lp.InMemoryEventStore(capture_tokens=True)
    lp.run_sync(net, initial={p_in: [token]}, event_store=store)

    token_events = store.events(types={"TokenAdded", "TokenRemoved"})
    assert token_events
    for event in token_events:
        assert event.token is token
        assert event.payload()["token"] is token


def test_in_memory_without_capture_has_no_token() -> None:
    p_in, _p_out, net = _build_chain()
    store = lp.InMemoryEventStore()
    lp.run_sync(net, initial={p_in: [object()]}, event_store=store)

    token_events = store.events(types={"TokenAdded", "TokenRemoved"})
    assert token_events
    for event in token_events:
        assert event.token is None
        assert "token" not in event.payload()
    [started] = store.events(types={"TransitionStarted"})
    assert started.token is None


def test_in_memory_capture_tokens_by_place() -> None:
    p_in, p_out, net = _build_chain()
    token = object()
    store = lp.InMemoryEventStore(capture_tokens=[p_out])
    lp.run_sync(net, initial={p_in: [token]}, event_store=store)

    out_events = store.events(types={"TokenAdded"}, places={"p_out"})
    in_events = store.events(types={"TokenAdded", "TokenRemoved"}, places={"p_in"})
    assert out_events and in_events
    assert all(e.token is token for e in out_events)
    assert all(e.token is None for e in in_events)


def test_python_store_captures_tokens() -> None:
    p_in, p_out, net = _build_chain()
    token = object()
    store = RecordingStore(captures_tokens=True)
    lp.run_sync(net, initial={p_in: [token]}, event_store=store)
    token_events = [e for e in store.events if e.type in {"TokenAdded", "TokenRemoved"}]
    assert token_events
    assert all(e.token is token for e in token_events)

    by_place = RecordingStore(captures_tokens=["p_out"])
    lp.run_sync(net, initial={p_in: [token]}, event_store=by_place)
    token_events = [e for e in by_place.events if e.type in {"TokenAdded", "TokenRemoved"}]
    assert {e.place_name for e in token_events} == {"p_in", "p_out"}
    for event in token_events:
        expected = token if event.place_name == "p_out" else None
        assert event.token is expected


def test_outer_python_store_decides_token_capture() -> None:
    """The InMemoryEventStore at the end of a chain stores what it is given:
    its own `capture_tokens` does not apply to appended events."""

    class Outer:
        captures_tokens = False

        def __init__(self, inner) -> None:
            self.inner = inner

        def append(self, event) -> None:
            self.inner.append(event)

    p_in, _p_out, net = _build_chain()
    inner = lp.InMemoryEventStore(capture_tokens=True)
    lp.run_sync(net, initial={p_in: [object()]}, event_store=Outer(inner))
    token_events = inner.events(types={"TokenAdded", "TokenRemoved"})
    assert token_events
    assert all(e.token is None for e in token_events)


@requires_tokio
async def test_injected_token_is_captured_async() -> None:
    p_env, _p_done, net = _async_chain()
    token = {"id": 7}
    store = RecordingStore(captures_tokens=True)
    handle, awaitable = lp.start_async(
        net,
        options=lp.ExecutorOptions(environment_places=(p_env,)),
        event_store=store,
    )
    handle.inject(p_env, token)
    handle.drain()
    await awaitable

    added = [e for e in store.events if e.type == "TokenAdded"]
    assert {e.place_name for e in added} == {"p_env", "p_done"}
    assert all(e.token is token for e in added)


@pytest.mark.skipif(not lp.HAS_ARCHIVE, reason="wheel built without `archive` feature")
def test_archive_accepts_captured_python_tokens(tmp_path) -> None:
    p_in, _p_out, net = _build_chain()
    store = lp.InMemoryEventStore(capture_tokens=True)
    lp.run_sync(net, initial={p_in: [{"k": 1}]}, event_store=store)

    path = tmp_path / "captured.lpa"
    lp.SessionArchiveWriter.write_from_store(
        path, session_id="captured", net=net, store=store
    )
    archive = lp.SessionArchiveReader.read(path)
    assert archive.event_count == len(store)
    assert _shape(archive.events()) == _shape(store.events())
