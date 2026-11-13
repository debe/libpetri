import Libpetri.Spec.Text

requirement_text EVT_022
  id "EVT-022"
  title "NoopEventStore"
  priority MUST
  kind F
  body r#"A zero-cost event store that discards all events. When used, the executor skips event object creation entirely.

⟦s1|The noop event store *shall* return no event from `events()`, whatever was appended to it, and the list it returns *shall* stay empty whatever is appended to it later.⟧

⟦s2|*When* an event is appended to the noop event store, the store *shall* discard it.⟧

⟦s3|The noop event store *shall* report itself as not enabled (`isEnabled()` returns false; in Rust, the store type's `ENABLED` constant is false).⟧

**Acceptance Criteria:**
1. append() is a no-op.
2. events() returns empty.
3. isEnabled() returns false.
4. The executor does not allocate event objects when the noop store is used.

**Test derivation:** Run net with noop store; verify no events captured; verify no allocation overhead (benchmark)."#
