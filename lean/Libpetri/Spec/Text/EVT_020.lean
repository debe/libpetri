import Libpetri.Spec.Text

requirement_text EVT_020
  id "EVT-020"
  title "EventStore Interface"
  priority MUST
  kind F
  body r#"The event store provides:
- `append(event)` — thread-safe event addition
- `events()` — a subsequence of the appended events, in append order
- `isEnabled()` — whether event capture is active

⟦s1|The list `events()` returns *shall* be a subsequence of the events appended to the store: only appended events, in the order they were appended, each append at most once.⟧ ⟦s2|A store that keeps token payloads only for some places (the Python binding's `capture_tokens` filter) is compared with the appended events after the same payloads are removed from them.⟧ ⟦s3|Which appended events the list leaves out, and whether it is a copy or a live view of the store, is up to each store ([EVT-021], [EVT-022], [EVT-024]).⟧

Events reach a store through the executor, which appends them only while the store reports itself as enabled (`isEnabled()` returns true; in Rust, the store type's `ENABLED` constant is true).

**Acceptance Criteria:**
1. append() is safe to call from any thread.
2. events() returns a subsequence of the appended events, in append order; whether that list is a copy or a live view is not specified.
3. isEnabled() controls whether the executor appends events to the store.

**Test derivation:** Append events from multiple threads; verify events() returns only appended events, each at most once, in the order the appends took effect (on the in-memory store, all of them, [EVT-021])."#
