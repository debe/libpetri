import Libpetri.Spec.Text

requirement_text EVT_023
  id "EVT-023"
  title "LoggingEventStore"
  priority SHOULD
  kind F
  body r#"An event store decorator that logs events to the platform's logging framework at appropriate levels before delegating to a wrapped store.

⟦s1|*When* an event is appended to the logging event store, the store *shall* log the event once, at the level of the event's kind, *shall* then pass the event once to the wrapped store, and *shall* log no other record and pass no other event, whatever store it wraps.⟧

⟦s2|The logging event store *shall* make the logging call of an event whenever the logging framework has the call's level enabled, and *may* skip the call when the framework has that level disabled.⟧

⟦s3|The logging event store *shall* log TransitionFailed, TransitionTimedOut and ActionTimedOut events at WARN level.⟧

⟦s4|The logging event store *shall* log ExecutionStarted and ExecutionCompleted events at INFO level.⟧

⟦s5|The logging event store *shall* log TransitionEnabled, TransitionClockRestarted, TransitionStarted and TransitionCompleted events at DEBUG level.⟧

⟦s6|The logging event store *shall* log TokenAdded, TokenRemoved, MarkingSnapshot and LogMessage events at TRACE level.⟧

⟦s7|The logging event store *shall* return from `events()` what the wrapped store returns.⟧

⟦s8|The logging event store *shall* report itself as enabled, whatever the wrapped store reports (`isEnabled()` returns true).⟧

**Acceptance Criteria:**
1. Failure events (TransitionFailed, TransitionTimedOut, ActionTimedOut) logged at WARN level.
2. Lifecycle events (ExecutionStarted, ExecutionCompleted) logged at INFO level.
3. The other transition events (TransitionEnabled, TransitionClockRestarted, TransitionStarted, TransitionCompleted) logged at DEBUG level.
4. Token events (TokenAdded, TokenRemoved), MarkingSnapshot and LogMessage logged at TRACE level.
5. Delegates to wrapped store after logging; `events()` returns the wrapped store's events.
6. Reports itself as enabled whatever store it wraps.

**Implementation notes:**
- Java: Full implementation with `java.lang.System.Logger`
- TypeScript: Not implemented
- Rust: Not implemented
- Python: Not implemented

**Test derivation:** Run net with logging store; verify log output at correct levels."#
