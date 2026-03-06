use crate::net_event::NetEvent;

/// Trait for event storage during Petri net execution.
///
/// The `ENABLED` constant allows zero-cost elimination of event recording
/// when using `NoopEventStore` — the compiler eliminates all branches
/// guarded by `if E::ENABLED`.
pub trait EventStore: Default + Send {
    const ENABLED: bool;

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
}
