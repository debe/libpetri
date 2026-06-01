"""Type stubs for libpetri.events.

Re-exports the raw PyO3 classes from `._libpetri` — the wrapper module is a
thin re-export, so the stubs delegate to the single source of truth in
`_libpetri.pyi`.
"""

from __future__ import annotations

from ._libpetri import (
    EventSubscription as EventSubscription,
    InMemoryEventStore as InMemoryEventStore,
    NetEvent as NetEvent,
)
