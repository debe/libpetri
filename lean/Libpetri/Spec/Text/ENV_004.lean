import Libpetri.Spec.Text

requirement_text ENV_004
  id "ENV-004"
  title "inject() Completion Semantics"
  priority MUST
  kind B
  body r#"⟦s1|In Java and TypeScript the inject operation returns a future/promise that completes with true when the token has been added to the marking.⟧ ⟦s2|In Rust and Python the return value indicates whether the injection was accepted; in Java and TypeScript the future's value indicates whether the token was injected.⟧

⟦s3|In Java and TypeScript the future is the admission signal of the accepted event.⟧ ⟦s4|The orchestrator completes it with true in the external-events step ([EXEC-001] step 2), when it adds the token to the marking.⟧ ⟦s5|It completes it with false when it discards the event because the executor is closed or stopped ([ENV-013], [ENV-015]), or when the run ends with the event still queued ([EXEC-041], [EXEC-042]).⟧ ⟦s6|A drain does not discard the events accepted before it: the orchestrator still injects them ([ENV-011]), unless close() is called or the run ends first.⟧ ⟦s7|Each accepted event has an admission signal of its own: an injection into a place whose earlier event is still queued neither replaces that event nor merges with it ([ENV-003]).⟧ Rust and Python have no admission signal, and no later answer reports a discard ([ENV-006]).

⟦s8|*When* the executor accepts an injection request, it *shall* queue the event as a new event, apart from every event already queued.⟧

⟦s9|*When* the executor completes the admission signal of an accepted event with true, it *shall*, in the same step, add the event's token at the tail of its place's queue and change no other part of the marking.⟧

⟦s10|*If* the executor completes the admission signal of an accepted event with false, *then* it *shall* leave the marking unchanged in that step.⟧

⟦s11|*If* a step leaves the executor open or draining and does not end the run, *then* the executor *shall not* complete the admission signal of an accepted event with false in that step.⟧

⟦s12|The executor *shall* complete the admission signal of an accepted event at most once.⟧

**Acceptance Criteria:**
1. Future completes with true/success when token is in marking.
2. Future completes with false/error if inject() is called while the executor is draining, closed or finished ([ENV-006]), or if the event is still queued when the executor closes or the run ends; an event queued before a drain is not completed with false while the executor drains, unless the run ends or close() is called.
3. The future completes at most once.

**Depends on:** [ENV-003], [ENV-013]
**Test derivation:** Inject token; await future; verify token in marking after future resolves."#
