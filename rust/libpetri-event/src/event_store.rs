use crate::net_event::NetEvent;

/// Trait for event storage during Petri net execution.
///
/// Two const flags govern zero-cost opt-in behaviour. The compiler
/// monomorphizes the executor against the concrete store type and eliminates
/// any branch guarded by a const whose value is known at compile time.
///
/// - [`ENABLED`](Self::ENABLED) — when `false`, the executor skips every
///   `append()` call (including argument construction) entirely. Used by
///   `NoopEventStore` in production hot paths.
/// - [`CAPTURES_TOKENS`](Self::CAPTURES_TOKENS) — when `true`, the executor
///   attaches the live token payload to `TokenAdded` / `TokenRemoved` events
///   via [`NetEvent::token_added_with`](crate::net_event::NetEvent::token_added_with).
///   Opt-in because cloning the payload costs one `Arc` bump per token
///   event and a heap allocation for the erased payload wrapper — acceptable
///   under debug inspection, wasteful otherwise.
pub trait EventStore: Default + Send {
    const ENABLED: bool;

    /// Whether this store wants token payloads attached to `TokenAdded` /
    /// `TokenRemoved` events. Defaults to `false` so existing implementations
    /// opt in explicitly (debug-aware stores in `libpetri-debug`).
    const CAPTURES_TOKENS: bool = false;

    fn append(&mut self, event: NetEvent);
    fn events(&self) -> &[NetEvent];
    fn size(&self) -> usize;
    fn is_empty(&self) -> bool;
}

/// No-op event store for production use.
///
/// All methods are no-ops; the compiler eliminates recording branches
/// via the `ENABLED = false` constant.
#[derive(Debug, Default)]
pub struct NoopEventStore;

impl EventStore for NoopEventStore {
    const ENABLED: bool = false;

    #[inline(always)]
    fn append(&mut self, _event: NetEvent) {}

    #[inline(always)]
    fn events(&self) -> &[NetEvent] {
        &[]
    }

    #[inline(always)]
    fn size(&self) -> usize {
        0
    }

    #[inline(always)]
    fn is_empty(&self) -> bool {
        true
    }
}

/// In-memory event store for debugging and testing.
#[derive(Debug, Default)]
pub struct InMemoryEventStore {
    events: Vec<NetEvent>,
}

impl InMemoryEventStore {
    pub fn new() -> Self {
        Self { events: Vec::new() }
    }

    /// Filter events by predicate.
    pub fn filter(&self, predicate: impl Fn(&NetEvent) -> bool) -> Vec<&NetEvent> {
        self.events.iter().filter(|e| predicate(e)).collect()
    }

    /// Get events for a specific transition.
    pub fn transition_events(&self, name: &str) -> Vec<&NetEvent> {
        self.filter(|e| e.transition_name() == Some(name))
    }

    /// Get all failure events.
    pub fn failures(&self) -> Vec<&NetEvent> {
        self.filter(|e| e.is_failure())
    }
}

impl EventStore for InMemoryEventStore {
    const ENABLED: bool = true;

    fn append(&mut self, event: NetEvent) {
        self.events.push(event);
    }

    fn events(&self) -> &[NetEvent] {
        &self.events
    }

    fn size(&self) -> usize {
        self.events.len()
    }

    fn is_empty(&self) -> bool {
        self.events.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    #[test]
    fn noop_store_is_always_empty() {
        let mut store = NoopEventStore;
        store.append(NetEvent::ExecutionStarted {
            net_name: Arc::from("test"),
            timestamp: 0,
        });
        assert!(store.is_empty());
        assert_eq!(store.size(), 0);
        assert!(store.events().is_empty());
    }

    #[test]
    fn in_memory_store_records_events() {
        let mut store = InMemoryEventStore::new();
        store.append(NetEvent::ExecutionStarted {
            net_name: Arc::from("test"),
            timestamp: 0,
        });
        store.append(NetEvent::TransitionStarted {
            transition_name: Arc::from("t1"),
            timestamp: 1,
        });
        assert_eq!(store.size(), 2);
        assert!(!store.is_empty());
    }

    #[test]
    fn in_memory_store_transition_events() {
        let mut store = InMemoryEventStore::new();
        store.append(NetEvent::TransitionStarted {
            transition_name: Arc::from("t1"),
            timestamp: 1,
        });
        store.append(NetEvent::TransitionCompleted {
            transition_name: Arc::from("t1"),
            timestamp: 2,
        });
        store.append(NetEvent::TransitionStarted {
            transition_name: Arc::from("t2"),
            timestamp: 3,
        });
        assert_eq!(store.transition_events("t1").len(), 2);
        assert_eq!(store.transition_events("t2").len(), 1);
    }

    #[test]
    fn enabled_constants() {
        const { assert!(!NoopEventStore::ENABLED) };
        const { assert!(InMemoryEventStore::ENABLED) };
    }

    #[test]
    fn capture_tokens_defaults_off() {
        // NoopEventStore opts out of token capture (monomorphization elides the
        // Arc::new payload on hot paths). InMemoryEventStore is a testing store and
        // inherits the default — debug-aware stores override CAPTURES_TOKENS = true.
        const { assert!(!NoopEventStore::CAPTURES_TOKENS) };
        const { assert!(!InMemoryEventStore::CAPTURES_TOKENS) };
    }
}
