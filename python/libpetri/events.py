"""Event store and live subscription API.

The Rust-side in-memory event store is exposed through `InMemoryEventStore`.
The implementation lives entirely in Rust — Python sees an opaque handle and
crosses the GIL only for filtered/batched reads, never per event.

Three tiers, all wired through the same handle:

- **Tier A** (post-hoc reads): `store.events(...)` / `store.count(...)`
  materialize filtered batches lazily after a run completes.
- **Tier B** (live subscriptions): `async for batch in store.subscribe(...)`
  yields batches of events through a bounded Rust-side channel; filter
  predicates evaluate in Rust. Pass `batch_size=1, batch_timeout_ms=0` for
  per-event unary delivery (token-stream-style latency).
- **Tier C** (Rust aggregates): `store.counters()` / `store.failures()`
  compute over the stored events without crossing the GIL per event.

A store can also be written in Python: pass any object with an
``append(event)`` method as ``event_store=`` (see `EventStoreProtocol`).
Stores can wrap each other, and a chain can end in an `InMemoryEventStore`
through its own ``append``.

Token values ride on ``TokenAdded`` / ``TokenRemoved`` events as
``NetEvent.token`` when the outermost store asks for them:
``InMemoryEventStore(capture_tokens=True)`` (or a list of place names), or a
``captures_tokens`` attribute on a Python store.
"""

from __future__ import annotations

from typing import Protocol, runtime_checkable

from . import _libpetri as _ext

InMemoryEventStore = _ext.InMemoryEventStore
NetEvent = _ext.NetEvent
if _ext.HAS_TOKIO:
    EventSubscription = _ext.EventSubscription
    EventStream = _ext.EventStream


@runtime_checkable
class EventStoreProtocol(Protocol):
    """What ``event_store=`` accepts besides an `InMemoryEventStore`.

    Only ``append`` is required. Two optional members are read once, when a
    run starts, as an attribute or a zero-argument method:

    - ``is_enabled``: when false, the run records no events at all.
      Defaults to true.
    - ``captures_tokens``: ``True`` to receive token values on
      ``TokenAdded`` / ``TokenRemoved`` (as ``event.token``), or a list of
      place names to receive them for those places only. Defaults to false.

    ``append`` is called on a libpetri thread, never on the executor's own
    thread, with the events of one run in order. An exception it raises is
    logged to the ``libpetri`` logger and does not stop the run or the
    delivery of later events. On an async run the first one is kept as
    ``ExecutorHandle.event_store_error``; a sync run only logs it. Every event has been delivered by
    the time ``run_sync`` returns or the run's awaitable resolves.
    """

    def append(self, event: NetEvent) -> None: ...


__all__ = ["EventStoreProtocol", "InMemoryEventStore", "NetEvent"]
if _ext.HAS_TOKIO:
    __all__.extend(["EventStream", "EventSubscription"])
