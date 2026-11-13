import Libpetri.Spec.Text

requirement_text ENV_011
  id "ENV-011"
  title "Graceful Drain"
  priority MUST
  kind B
  body r#"⟦s1|The executor provides a `drain()` method that signals graceful shutdown.⟧ ⟦s2|After `drain()` is called:⟧
1. ⟦s3|New `inject()` calls are rejected (return error/false).⟧
2. ⟦s4|Already-queued external events are processed normally.⟧
3. ⟦s5|In-flight actions are allowed to complete.⟧
4. ⟦s6|The executor terminates when quiescent (no armed transitions, no in-flight, no pending events).⟧

⟦s7|Items 2 to 4 hold while no terminal place is marked: a marked terminal place stops the executor at once, abandoning the actions in flight and ending the run with the queued external events unapplied ([EXEC-042]).⟧

⟦s8|For executors without environment places, a drain does not change when the executor terminates, since the executor already terminates at quiescence.⟧

⟦s9|*When* an open executor is drained, it *shall* enter the draining mode and *shall* leave the rest of its state as it was, apart from waking its wait ([CONC-010]): its marking, its queued external events and its firings in flight stay as they were.⟧

⟦s10|*If* an executor that is not open (draining, closed or stopped) is drained, *then* the drain *shall* change nothing.⟧

⟦s11|*While* the executor is draining, *when* an injection is requested, the executor *shall* reject it (error or false) and *shall* change nothing.⟧

⟦s12|*While* the executor is draining, it *shall not* discard a queued external event.⟧

⟦s13|*While* the executor is draining, it *shall* take every step of its cycle as it takes it while open, with the same effect: it *shall* inject the queued external events, let the actions in flight complete, settle their outcomes and start ready transitions as an open executor does; only the answers to requests and snapshot requests ([ENV-014]), and the wait and the termination test of an executor with environment places at quiescence, differ.⟧ ⟦s14|A close or an immediate termination of a draining executor is governed by [ENV-013] and [ENV-015].⟧

⟦s15|*While* the executor is draining and no terminal place is marked, it *shall not* terminate except at the termination test of a cycle ([EXEC-001]) that finds it quiescent: no transition armed, no firing in flight, and no completion, publication or external event queued.⟧

⟦s16|*While* the executor is draining and no terminal place is marked, *when* the termination test of a cycle finds it quiescent, the executor *shall* terminate.⟧

⟦s17|*While* the executor is draining and quiescent, *when* it enters or ends its wait, it *shall* change nothing but the wait, and ending the wait *shall* take it to the first step of the next cycle.⟧

⟦s18|*While* the executor is draining and quiescent and no terminal place is marked, it *shall* end its wait at once, without waiting for an arrival or a timer ([CONC-010]).⟧

**Acceptance Criteria:**
1. `drain()` method is available on the executor.
2. After `drain()`, `inject()` returns error/false.
3. Already-queued events are processed before termination.
4. In-flight actions complete before termination.
5. Executor terminates when quiescent after drain.

**Depends on:** [ENV-010], [EXEC-001], [EXEC-040], [EXEC-042], [CONC-010]
**Test derivation:** Executor with env places; inject tokens; call drain(); verify queued events processed; verify new inject rejected; verify termination at quiescence."#
