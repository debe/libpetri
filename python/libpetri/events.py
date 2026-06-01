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
"""

from __future__ import annotations

from . import _libpetri as _ext

InMemoryEventStore = _ext.InMemoryEventStore
NetEvent = _ext.NetEvent
if _ext.HAS_TOKIO:
    EventSubscription = _ext.EventSubscription


__all__ = ["InMemoryEventStore", "NetEvent"]
if _ext.HAS_TOKIO:
    __all__.append("EventSubscription")
