import Libpetri.Spec.Text

requirement_text EVT_021
  id "EVT-021"
  title "InMemoryEventStore"
  priority MUST
  kind F
  body r#"A thread-safe in-memory event store that retains all events in the order they were appended.

⟦s1|A new in-memory event store *shall* return no event from `events()`.⟧

⟦s2|*When* an event is appended to the in-memory event store, a call of `events()` made right after the append *shall* return the events that a call made right before the append returns, with that event added at the end.⟧

⟦s3|*Where* the in-memory event store provides `clear()`, a call of `events()` made right after `clear()` *shall* return no event.⟧

⟦s4|The in-memory event store *shall* report itself as enabled, so that an executor appends every event it emits to it (see [EVT-020]): `isEnabled()` returns true in Java and TypeScript, the store type's `ENABLED` constant is true in Rust, and the Python binding's store is written through a Rust store whose `ENABLED` constant is true.⟧

⟦s5|A call of `events()` changes nothing that a later call of `events()` returns, so the sentences above speak of what a call returns after the appends and clears made so far.⟧

**Acceptance Criteria:**
1. Events are stored in insertion order.
2. Thread-safe append (concurrent callers do not lose events).
3. events() returns the events appended since the last clear() (every appended event where the store has no clear()), in the order they were appended; what a returned list shows after later operations, whether it is a copy or a live view, is not specified.
4. Where the store provides clear() (TypeScript; in Java only on the package-private InMemoryEventStore class, which EventStore.inMemory() returns as the EventStore interface), clear() empties it for test reuse.

**Test derivation:** Append 100 events; verify events() returns 100 in order."#
