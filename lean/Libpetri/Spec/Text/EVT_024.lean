import Libpetri.Spec.Text

requirement_text EVT_024
  id "EVT-024"
  title "DebugEventStore"
  priority SHOULD
  kind F
  body r#"An event store with live tailing support for debug UIs. Supports:
- Subscriptions (consumers notified of new events)
- Capacity management (eviction of old events)
- Session tracking

A debug event store has a capacity: a positive number of events, 10,000 unless the caller gives another. A debug event store is open until its `close()` is called.

⟦s1|*When* events have been appended to a debug event store one after the other, a call of `events()` *shall* return the newest of them, as many as the store's capacity allows, in the order they were appended.⟧

⟦s2|*When* an event is appended to an open debug event store, the append *shall* complete without waiting for any subscriber to receive the event.⟧

⟦s3|Each subscriber of a debug event store *shall* receive only events appended to the store, each at most once and, for appends that do not overlap in time, in the order they were appended.⟧ ⟦s4|A subscriber may receive an event after the append that added it has returned.⟧

⟦s5|*While* a debug event store is open, a caller *shall* be able to add a further subscriber, whatever subscribers the store already has.⟧

⟦s6|*While* a debug event store is open, each subscriber that has not cancelled its subscription *shall* still be able to receive every event appended since it subscribed, whatever the other subscribers have received.⟧

**Acceptance Criteria:**
1. While the store is open, each subscriber that has not cancelled can receive the events appended since it subscribed, each at most once and, for appends that do not overlap in time, in the order they were appended.
2. Old events are evicted when capacity is exceeded.
3. Multiple subscribers can be active simultaneously.

**Implementation notes:**
- Java: Full implementation with virtual-thread broadcast
- TypeScript: Full implementation with microtask broadcast
- Rust: Implemented (`libpetri-debug::DebugEventStore`, crossbeam-channel subscriptions)

**Test derivation:** Subscribe to debug store; append event; verify subscriber receives it."#
