//! Event store wrapper that delegates to both a primary store and a debug store.

use std::sync::Arc;

use libpetri_event::event_store::EventStore;
use libpetri_event::net_event::NetEvent;

use crate::debug_event_store::DebugEventStore;

/// An `EventStore` that delegates to both a primary `E: EventStore` (owned)
/// and a shared `Arc<DebugEventStore>` for the debug protocol.
///
/// The primary store is accessed via `&mut self` (normal `EventStore` contract).
/// The debug store uses interior mutability (Mutex) so it can be shared with
/// the protocol handler.
pub struct DebugAwareEventStore<E: EventStore> {
    primary: E,
    debug_store: Arc<DebugEventStore>,
}

impl<E: EventStore> DebugAwareEventStore<E> {
    /// Creates a new `DebugAwareEventStore`.
    pub fn new(primary: E, debug_store: Arc<DebugEventStore>) -> Self {
        Self {
            primary,
            debug_store,
        }
    }

    /// Returns a reference to the primary event store.
    pub fn primary(&self) -> &E {
        &self.primary
    }

    /// Returns a mutable reference to the primary event store.
    pub fn primary_mut(&mut self) -> &mut E {
        &mut self.primary
    }

    /// Returns a clone of the `Arc<DebugEventStore>`.
    pub fn debug_store(&self) -> Arc<DebugEventStore> {
        Arc::clone(&self.debug_store)
    }
}

impl<E: EventStore> EventStore for DebugAwareEventStore<E> {
    const ENABLED: bool = true;

    /// Opt in so executors attach token payloads to `TokenAdded` / `TokenRemoved`
    /// events — the archive writer and live debug UI both depend on them.
    const CAPTURES_TOKENS: bool = true;

    fn append(&mut self, event: NetEvent) {
        // Always forward to debug store (swallow failures)
        self.debug_store.append(event.clone());
        // Forward to primary if enabled
        if E::ENABLED {
            self.primary.append(event);
        }
    }

    fn events(&self) -> &[NetEvent] {
        if E::ENABLED {
            self.primary.events()
        } else {
            &[]
        }
    }

    fn size(&self) -> usize {
        if E::ENABLED { self.primary.size() } else { 0 }
    }

    fn is_empty(&self) -> bool {
        if E::ENABLED {
            self.primary.is_empty()
        } else {
            true
        }
    }
}

impl<E: EventStore> Default for DebugAwareEventStore<E> {
    fn default() -> Self {
        Self {
            primary: E::default(),
            debug_store: Arc::new(DebugEventStore::new("default".into())),
        }
    }
}

impl<E: EventStore> std::fmt::Debug for DebugAwareEventStore<E>
where
    E: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DebugAwareEventStore")
            .field("primary", &self.primary)
            .field("debug_store", &self.debug_store)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use libpetri_event::event_store::{InMemoryEventStore, NoopEventStore};
    use std::sync::Arc as StdArc;

    fn exec_started(ts: u64) -> NetEvent {
        NetEvent::ExecutionStarted {
            net_name: StdArc::from("test"),
            timestamp: ts,
        }
    }

    #[test]
    fn delegates_to_both_stores() {
        let debug_store = Arc::new(DebugEventStore::new("s1".into()));
        let mut store =
            DebugAwareEventStore::new(InMemoryEventStore::new(), Arc::clone(&debug_store));

        store.append(exec_started(100));

        assert_eq!(store.size(), 1);
        assert_eq!(store.events().len(), 1);
        assert_eq!(debug_store.size(), 1);
    }

    #[test]
    fn delegates_to_debug_even_with_noop_primary() {
        let debug_store = Arc::new(DebugEventStore::new("s1".into()));
        let mut store = DebugAwareEventStore::new(NoopEventStore, Arc::clone(&debug_store));

        store.append(exec_started(100));

        // Primary is noop, so size/events return empty
        assert_eq!(store.size(), 0);
        assert!(store.is_empty());
        // But debug store got the event
        assert_eq!(debug_store.size(), 1);
    }

    #[test]
    fn enabled_is_always_true() {
        assert!(DebugAwareEventStore::<NoopEventStore>::ENABLED);
        assert!(DebugAwareEventStore::<InMemoryEventStore>::ENABLED);
    }

    #[test]
    fn debug_store_accessible() {
        let debug_store = Arc::new(DebugEventStore::new("s1".into()));
        let store = DebugAwareEventStore::new(InMemoryEventStore::new(), Arc::clone(&debug_store));
        assert_eq!(store.debug_store().session_id(), "s1");
    }
}
