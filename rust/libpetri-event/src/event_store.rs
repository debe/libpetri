use std::collections::BTreeMap;

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

    /// Get the events of one type, named as [`NetEvent::event_type`] names
    /// it (`"TransitionCompleted"`, `"TokenAdded"`, …) (\[EVT-030\]).
    pub fn events_of_type(&self, event_type: &str) -> Vec<&NetEvent> {
        self.filter(|e| e.event_type() == event_type)
    }

    /// Get the token events (`TokenAdded` / `TokenRemoved`) of one place
    /// (\[EVT-030\]).
    pub fn place_events(&self, place_name: &str) -> Vec<&NetEvent> {
        self.filter(|e| e.place_name() == Some(place_name))
    }

    /// Runs `query` over the stored events: the matching events in append
    /// order, with the query's offset and limit applied to the filtered
    /// result (\[EVT-030\]).
    pub fn query(&self, query: &EventQuery) -> Vec<&NetEvent> {
        query.apply(&self.events)
    }

    /// Number of events whose type is one of `types` (\[EVT-030\]). Use
    /// [`size`](EventStore::size) to count every event.
    pub fn count_of_types(&self, types: &[&str]) -> usize {
        self.events
            .iter()
            .filter(|e| types.contains(&e.event_type()))
            .count()
    }

    /// Histogram of the stored events by [`NetEvent::event_type`]: each
    /// type that occurs, once, with its number of events (\[EVT-030\]). A
    /// `BTreeMap`, so the types iterate in ascending order on every run.
    pub fn counters(&self) -> BTreeMap<&'static str, usize> {
        let mut counts = BTreeMap::new();
        for event in &self.events {
            *counts.entry(event.event_type()).or_insert(0) += 1;
        }
        counts
    }
}

/// A query over the events of an event store (\[EVT-030\]).
///
/// Every filter that is set must match: a type filter matches the events of
/// the given [`NetEvent::event_type`] names, a transition filter the events
/// that carry one of the given transition names, and a place filter the
/// token events of one of the given places. An event that carries no
/// transition (or place) name matches no transition (or place) filter, and a
/// filter set to an empty list matches nothing. The offset and limit page
/// the filtered result, not the store: skip `offset` matching events, then
/// return at most `limit` of the rest (all of them without a limit).
///
/// The semantics are those of the Python binding's
/// `InMemoryEventStore.events(types=, transitions=, places=, limit=, offset=)`.
///
/// ```
/// use libpetri_event::event_store::EventQuery;
///
/// let page = EventQuery::new()
///     .types(["TokenAdded", "TokenRemoved"])
///     .places(["queue"])
///     .offset(10)
///     .limit(10);
/// # let _ = page;
/// ```
#[derive(Debug, Clone, Default)]
pub struct EventQuery {
    types: Option<Vec<String>>,
    transitions: Option<Vec<String>>,
    places: Option<Vec<String>>,
    offset: usize,
    limit: Option<usize>,
}

impl EventQuery {
    /// A query that matches every event.
    pub fn new() -> Self {
        Self::default()
    }

    /// Keeps only the events of the given types.
    pub fn types<I, S>(mut self, types: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        self.types = Some(types.into_iter().map(Into::into).collect());
        self
    }

    /// Keeps only the events that carry one of the given transition names.
    pub fn transitions<I, S>(mut self, transitions: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        self.transitions = Some(transitions.into_iter().map(Into::into).collect());
        self
    }

    /// Keeps only the token events of the given places.
    pub fn places<I, S>(mut self, places: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        self.places = Some(places.into_iter().map(Into::into).collect());
        self
    }

    /// Skips the first `offset` matching events.
    pub fn offset(mut self, offset: usize) -> Self {
        self.offset = offset;
        self
    }

    /// Returns at most `limit` matching events after the offset.
    pub fn limit(mut self, limit: usize) -> Self {
        self.limit = Some(limit);
        self
    }

    /// True when `event` passes every filter of this query. Offset and
    /// limit play no part.
    pub fn matches(&self, event: &NetEvent) -> bool {
        if let Some(types) = &self.types
            && !types.iter().any(|t| t == event.event_type())
        {
            return false;
        }
        if let Some(transitions) = &self.transitions {
            let Some(name) = event.transition_name() else {
                return false;
            };
            if !transitions.iter().any(|t| t == name) {
                return false;
            }
        }
        if let Some(places) = &self.places {
            let Some(name) = event.place_name() else {
                return false;
            };
            if !places.iter().any(|p| p == name) {
                return false;
            }
        }
        true
    }

    /// Runs this query over `events`: the matching events in order, paged
    /// by the offset and limit.
    pub fn apply<'a>(&self, events: &'a [NetEvent]) -> Vec<&'a NetEvent> {
        events
            .iter()
            .filter(|e| self.matches(e))
            .skip(self.offset)
            .take(self.limit.unwrap_or(usize::MAX))
            .collect()
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

    /// A store with token events on two places, transition events, a
    /// failure and execution events that carry no transition name, in a
    /// known order.
    fn mixed_store() -> InMemoryEventStore {
        let mut store = InMemoryEventStore::new();
        let events = vec![
            NetEvent::ExecutionStarted { net_name: Arc::from("net"), timestamp: 0 },
            NetEvent::token_added(Arc::from("a"), 1),
            NetEvent::TransitionStarted { transition_name: Arc::from("t1"), timestamp: 2 },
            NetEvent::token_removed(Arc::from("a"), 3),
            NetEvent::token_added(Arc::from("b"), 4),
            NetEvent::TransitionCompleted { transition_name: Arc::from("t1"), timestamp: 5 },
            NetEvent::token_added(Arc::from("a"), 6),
            NetEvent::TransitionFailed {
                transition_name: Arc::from("t2"),
                error: "boom".into(),
                timestamp: 7,
            },
            NetEvent::token_added(Arc::from("a"), 8),
            NetEvent::ExecutionCompleted { net_name: Arc::from("net"), timestamp: 9 },
        ];
        for event in events {
            store.append(event);
        }
        store
    }

    fn timestamps(events: &[&NetEvent]) -> Vec<u64> {
        events.iter().map(|e| e.timestamp()).collect()
    }

    /// \[EVT-030\] AC1: a filter by type returns only the events of that type.
    #[test]
    fn evt030_events_of_type() {
        let store = mixed_store();
        assert_eq!(timestamps(&store.events_of_type("TransitionCompleted")), vec![5]);
        assert_eq!(timestamps(&store.events_of_type("TokenAdded")), vec![1, 4, 6, 8]);
        assert!(store.events_of_type("ActionTimedOut").is_empty());
        let query = EventQuery::new().types(["TokenRemoved", "TransitionFailed"]);
        assert_eq!(timestamps(&store.query(&query)), vec![3, 7]);
    }

    /// \[EVT-030\] AC2: an event with no transition name matches no
    /// transition filter, and leaves the events the filter returns unchanged.
    #[test]
    fn evt030_transition_filter_skips_nameless_events() {
        let store = mixed_store();
        let query = EventQuery::new().transitions(["t1", "t2"]);
        assert_eq!(timestamps(&store.query(&query)), vec![2, 5, 7]);
        assert_eq!(
            timestamps(&store.query(&EventQuery::new().transitions(["t1"]))),
            timestamps(&store.transition_events("t1")),
        );
    }

    /// \[EVT-030\] AC3: a place filter returns only the token events of the
    /// named places, and offset / limit page the filtered result.
    #[test]
    fn evt030_place_filter_and_pagination() {
        let store = mixed_store();
        assert_eq!(timestamps(&store.place_events("a")), vec![1, 3, 6, 8]);
        assert_eq!(timestamps(&store.place_events("b")), vec![4]);
        let both = EventQuery::new().places(["a", "b"]);
        assert_eq!(timestamps(&store.query(&both)), vec![1, 3, 4, 6, 8]);

        // The page is taken over the filtered result, not over the store.
        let page = both.clone().offset(1).limit(2);
        assert_eq!(timestamps(&store.query(&page)), vec![3, 4]);
        // No limit: everything after the offset.
        assert_eq!(timestamps(&store.query(&both.clone().offset(3))), vec![6, 8]);
        // An offset past the end, and a zero limit, return nothing.
        assert!(store.query(&both.clone().offset(9)).is_empty());
        assert!(store.query(&both.limit(0)).is_empty());

        // Every filter must match.
        let added_to_a = EventQuery::new().types(["TokenAdded"]).places(["a"]);
        assert_eq!(timestamps(&store.query(&added_to_a)), vec![1, 6, 8]);
        // A filter set to no names matches nothing.
        assert!(store.query(&EventQuery::new().places(Vec::<String>::new())).is_empty());
        // The empty query, without offset and limit, is `events()`.
        assert_eq!(store.query(&EventQuery::new()).len(), store.size());
    }

    /// \[EVT-030\] AC4: `failures()` returns the failure events.
    #[test]
    fn evt030_failures() {
        let store = mixed_store();
        assert_eq!(timestamps(&store.failures()), vec![7]);
    }

    /// \[EVT-030\] AC5: `counters()` names each type that occurs once, with
    /// its count, and its values sum to the total; a count by type counts the
    /// events of the given types.
    #[test]
    fn evt030_counters_and_count() {
        let store = mixed_store();
        let counters = store.counters();
        let expected: Vec<(&str, usize)> = vec![
            ("ExecutionCompleted", 1),
            ("ExecutionStarted", 1),
            ("TokenAdded", 4),
            ("TokenRemoved", 1),
            ("TransitionCompleted", 1),
            ("TransitionFailed", 1),
            ("TransitionStarted", 1),
        ];
        assert_eq!(counters.into_iter().collect::<Vec<_>>(), expected);
        assert_eq!(store.counters().values().sum::<usize>(), store.size());
        assert_eq!(store.count_of_types(&["TokenAdded", "TokenRemoved"]), 5);
        assert_eq!(store.count_of_types(&[]), 0);
        assert!(InMemoryEventStore::new().counters().is_empty());
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
