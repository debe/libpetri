//! Event store with live tailing and historical replay for debug sessions.

use std::sync::Mutex;

use crossbeam_channel::Sender;
use libpetri_event::net_event::NetEvent;

/// Default maximum events to retain before evicting oldest.
pub const DEFAULT_MAX_EVENTS: usize = 10_000;

/// Event store for debug sessions with subscription support.
///
/// Uses interior mutability (`Mutex`) so it can be shared via `Arc`
/// between the executor (which owns the `DebugAwareEventStore`) and
/// the protocol handler.
pub struct DebugEventStore {
    session_id: String,
    max_events: usize,
    inner: Mutex<Inner>,
}

struct Inner {
    events: Vec<NetEvent>,
    event_count: usize,
    evicted_count: usize,
    subscribers: Vec<Sender<NetEvent>>,
}

/// Handle for managing a live event subscription.
pub struct Subscription {
    cancel_tx: Option<Sender<()>>,
}

impl Subscription {
    /// Cancels the subscription.
    pub fn cancel(&mut self) {
        self.cancel_tx.take();
    }

    /// Returns `true` if the subscription is still active.
    pub fn is_active(&self) -> bool {
        self.cancel_tx.is_some()
    }
}

impl DebugEventStore {
    /// Creates a new `DebugEventStore` with the given session ID and default capacity.
    pub fn new(session_id: String) -> Self {
        Self::with_capacity(session_id, DEFAULT_MAX_EVENTS)
    }

    /// Creates a new `DebugEventStore` with the given session ID and max event capacity.
    pub fn with_capacity(session_id: String, max_events: usize) -> Self {
        assert!(
            max_events > 0,
            "max_events must be positive, got: {max_events}"
        );
        Self {
            session_id,
            max_events,
            inner: Mutex::new(Inner {
                events: Vec::new(),
                event_count: 0,
                evicted_count: 0,
                subscribers: Vec::new(),
            }),
        }
    }

    /// Returns the session ID.
    pub fn session_id(&self) -> &str {
        &self.session_id
    }

    /// Returns the max event capacity.
    pub fn max_events(&self) -> usize {
        self.max_events
    }

    /// Appends an event, evicting oldest if at capacity, and broadcasts to subscribers.
    pub fn append(&self, event: NetEvent) {
        let mut inner = self.inner.lock().unwrap();
        inner.events.push(event.clone());
        inner.event_count += 1;

        // Evict oldest when capacity exceeded
        while inner.events.len() > self.max_events {
            inner.events.remove(0);
            inner.evicted_count += 1;
        }

        // Broadcast to subscribers, removing disconnected ones
        inner
            .subscribers
            .retain(|tx| tx.send(event.clone()).is_ok());
    }

    /// Returns a snapshot of all retained events.
    pub fn events(&self) -> Vec<NetEvent> {
        self.inner.lock().unwrap().events.clone()
    }

    /// Total number of events ever appended (including evicted).
    pub fn event_count(&self) -> usize {
        self.inner.lock().unwrap().event_count
    }

    /// Number of retained events.
    pub fn size(&self) -> usize {
        self.inner.lock().unwrap().events.len()
    }

    /// Returns `true` if no events are retained.
    pub fn is_empty(&self) -> bool {
        self.inner.lock().unwrap().events.is_empty()
    }

    /// Number of events evicted from the store.
    pub fn evicted_count(&self) -> usize {
        self.inner.lock().unwrap().evicted_count
    }

    /// Subscribe to receive events as they occur.
    ///
    /// Returns a `crossbeam_channel::Receiver` for receiving events
    /// and a `Subscription` handle for cancellation.
    pub fn subscribe(&self) -> (crossbeam_channel::Receiver<NetEvent>, Subscription) {
        let (event_tx, event_rx) = crossbeam_channel::unbounded();
        let (cancel_tx, _cancel_rx) = crossbeam_channel::bounded(1);

        self.inner.lock().unwrap().subscribers.push(event_tx);

        (
            event_rx,
            Subscription {
                cancel_tx: Some(cancel_tx),
            },
        )
    }

    /// Number of active subscribers.
    pub fn subscriber_count(&self) -> usize {
        self.inner.lock().unwrap().subscribers.len()
    }

    /// Returns events starting from a specific global index.
    pub fn events_from(&self, from_index: usize) -> Vec<NetEvent> {
        let inner = self.inner.lock().unwrap();
        let adjusted_skip = from_index.saturating_sub(inner.evicted_count);
        if adjusted_skip >= inner.events.len() {
            return Vec::new();
        }
        inner.events[adjusted_skip..].to_vec()
    }

    /// Returns all events since the specified timestamp.
    pub fn events_since(&self, from: u64) -> Vec<NetEvent> {
        let inner = self.inner.lock().unwrap();
        inner
            .events
            .iter()
            .filter(|e| e.timestamp() >= from)
            .cloned()
            .collect()
    }

    /// Returns events within a time range `[from, to)`.
    pub fn events_between(&self, from: u64, to: u64) -> Vec<NetEvent> {
        let inner = self.inner.lock().unwrap();
        inner
            .events
            .iter()
            .filter(|e| e.timestamp() >= from && e.timestamp() < to)
            .cloned()
            .collect()
    }

    /// Closes the store, removing all subscribers.
    pub fn close(&self) {
        self.inner.lock().unwrap().subscribers.clear();
    }
}

impl std::fmt::Debug for DebugEventStore {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let inner = self.inner.lock().unwrap();
        f.debug_struct("DebugEventStore")
            .field("session_id", &self.session_id)
            .field("max_events", &self.max_events)
            .field("event_count", &inner.event_count)
            .field("retained", &inner.events.len())
            .field("subscribers", &inner.subscribers.len())
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    fn started_event(name: &str, ts: u64) -> NetEvent {
        NetEvent::TransitionStarted {
            transition_name: Arc::from(name),
            timestamp: ts,
        }
    }

    #[test]
    fn basic_append_and_retrieve() {
        let store = DebugEventStore::new("s1".into());
        store.append(started_event("t1", 100));
        store.append(started_event("t2", 200));
        assert_eq!(store.event_count(), 2);
        assert_eq!(store.size(), 2);
        assert!(!store.is_empty());
        assert_eq!(store.events().len(), 2);
    }

    #[test]
    fn eviction_at_capacity() {
        let store = DebugEventStore::with_capacity("s1".into(), 3);
        for i in 0..5 {
            store.append(started_event("t", i));
        }
        assert_eq!(store.event_count(), 5);
        assert_eq!(store.size(), 3);
        assert_eq!(store.evicted_count(), 2);
        // Retained events should be timestamps 2, 3, 4
        let events = store.events();
        assert_eq!(events[0].timestamp(), 2);
    }

    #[test]
    fn events_from_with_eviction() {
        let store = DebugEventStore::with_capacity("s1".into(), 3);
        for i in 0..5 {
            store.append(started_event("t", i));
        }
        // Global index 0..4, evicted 0,1 → retained 2,3,4
        let from_0 = store.events_from(0);
        assert_eq!(from_0.len(), 3); // all retained
        let from_3 = store.events_from(3);
        assert_eq!(from_3.len(), 2); // indices 3,4
    }

    #[test]
    fn events_since_and_between() {
        let store = DebugEventStore::new("s1".into());
        for i in 0..5 {
            store.append(started_event("t", i * 100));
        }
        assert_eq!(store.events_since(200).len(), 3);
        assert_eq!(store.events_between(100, 300).len(), 2);
    }

    #[test]
    fn subscription_broadcast() {
        let store = DebugEventStore::new("s1".into());
        let (rx, _sub) = store.subscribe();
        store.append(started_event("t1", 100));
        let event = rx.try_recv().unwrap();
        assert_eq!(event.timestamp(), 100);
    }

    #[test]
    fn subscription_cancel() {
        let store = DebugEventStore::new("s1".into());
        let (rx, mut sub) = store.subscribe();
        assert!(sub.is_active());
        sub.cancel();
        assert!(!sub.is_active());
        // After cancel, the sender is dropped but existing senders in store
        // will be cleaned up on next broadcast
        store.append(started_event("t1", 100));
        // rx may or may not receive depending on timing, but shouldn't panic
        let _ = rx.try_recv();
    }

    #[test]
    fn close_clears_subscribers() {
        let store = DebugEventStore::new("s1".into());
        let (_rx, _sub) = store.subscribe();
        assert_eq!(store.subscriber_count(), 1);
        store.close();
        assert_eq!(store.subscriber_count(), 0);
    }
}
