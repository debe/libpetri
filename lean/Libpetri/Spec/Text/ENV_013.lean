import Libpetri.Spec.Text

requirement_text ENV_013
  id "ENV-013"
  title "Immediate Close"
  priority MUST
  kind B
  body r#"⟦s1|The executor provides a `close()` method for immediate shutdown.⟧ After `close()` is called:
1. New `inject()` calls are rejected (return error/false).
2. Queued external events are not injected. Where `inject()` reports when its event is injected (Java, TypeScript), every event still queued at the close is discarded after it, never injected, and completed with false (at the latest when the loop ends). Rust and Python answer `inject()` when the event is queued, and the close travels the signal channel behind the events sent before it, so those events are injected before the executor takes the close.
3. In-flight actions are allowed to complete, unless a terminal place is marked ([EXEC-042]).
4. The executor terminates after in-flight actions complete, unless a terminal place is marked first ([EXEC-042]).

⟦s2|In Java and TypeScript the executor takes the close when `close()` sets its closed flag, except that a call that lands while the loop is injecting queued events in the external-events step ([EXEC-001] step 2) is taken when that injection ends: the events it injects come before the close, and the events still queued after it are discarded.⟧

⟦s3|Calling `close()` after `drain()` escalates from graceful to immediate shutdown.⟧

⟦s4|A close does not stop the firing pass.⟧ ⟦s5|While an action is in flight, a closed executor keeps running its cycles and may start ready transitions, whose actions are then in flight too; it terminates at the first termination test ([EXEC-040]) that finds no action in flight.⟧ ⟦s6|A close alone therefore does not bound a run whose firings overlap; an immediate termination ([ENV-015]) does.⟧ ⟦s7|A run budget ([ENV-016]) bounds only the caller's wait.⟧ In Java and TypeScript an awaited `inject()` of an event still queued at the close is answered when the loop ends.

⟦s8|*When* the executor takes a close, it *shall* enter the closed mode and *shall* leave every part of its state other than its mode and whether its loop waits ([CONC-010]) as it was: the marking, the clock of every transition, the clock reading of the cycle, the actions in flight, the queued outcomes, publications and external events, the supply of identities, the phase of its loop and the rest of a firing pass.⟧

⟦s9|*While* the executor is closed, it *shall* reject every `inject()` call, and a rejected call *shall* change nothing.⟧

⟦s10|The executor *shall* enter the closed mode only when it takes a close, and *shall* leave it only for an immediate termination ([ENV-015]).⟧

⟦s11|*While* the executor is closed, it *shall not* inject a queued external event.⟧

⟦s12|*When* a closed executor ends its run, it *shall* leave no external event queued.⟧

⟦s13|*While* the executor is closed and no terminal place is marked, it *shall* end its run only when no action is in flight, or on a cancellation it observes in its wait ([EXEC-041]).⟧

⟦s14|*While* the executor is closed, no terminal place is marked and no action is in flight, it *shall* take no step at a termination test ([EXEC-040]) other than ending its run.⟧

⟦s15|*While* the executor is closed, it *shall* remove an action from the actions in flight only by settling its outcome.⟧

⟦s16|*While* the executor is closed, it *shall* end step 1b of a cycle ([EXEC-001]) only when no publication is queued.⟧

**Acceptance Criteria:**
1. `close()` signals immediate shutdown.
2. No queued event is injected after the close; where `inject()` reports injection, each event still queued is completed with false (not processed).
3. In-flight actions complete before termination.
4. `inject()` returns error/false after close.

**Depends on:** [ENV-010], [ENV-004], [EXEC-040]
**Test derivation:** Executor with in-flight action; call close(); verify action completes; verify queued events discarded; verify executor terminates."#
