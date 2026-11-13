import Libpetri.Spec.Text

requirement_text ENV_003
  id "ENV-003"
  title "inject() Thread Safety"
  priority MUST
  kind B
  body r#"⟦s1|The inject operation is safe to call from any thread, task, or coroutine — not just the orchestrator thread.⟧ ⟦s2|It enqueues the token for processing on the next orchestrator cycle.⟧

⟦s3|*When* the executor accepts an `inject()` call, it *shall* append the event to the tail of its queue of accepted events, as a new entry under a fresh ticket that identifies the call, and *shall not* change the marking or any other part of its state, except that it moves its ticket supply on and wakes the orchestrator if it is waiting ([ENV-005]).⟧

⟦s4|*When* the orchestrator injects an accepted event, it *shall* take the oldest entry of the queue, *shall* remove that entry from the queue, *shall* add its token at the tail of its place (glossary: Queue order) and *shall not* change any other place.⟧

⟦s5|The executor *shall not* change its queue of accepted events in any other way than appending a newly accepted event, injecting the oldest entry, discarding entries once it is closed ([ENV-013]) or terminated immediately ([ENV-015]), and emptying the queue when the run ends ([EXEC-041]), so that it injects accepted events in the order it accepted them.⟧

⟦s6|*When* the executor discards queued events or the run ends, the executor *shall* only remove entries from its queue of accepted events and *shall* keep the remaining entries in the order it accepted them.⟧

⟦s7|The executor *shall not* move its ticket supply back, so that no two accepted calls share a ticket.⟧

⟦s8|*When* the executor accepts an `inject()` call, the orchestrator *shall* inject its token before the run finishes, unless after accepting it the executor is closed ([ENV-013]), is terminated immediately ([ENV-015]), stops because a terminal place is marked ([EXEC-042]) or ends its run on a cancellation it observes in its wait ([EXEC-041]).⟧

⟦s9|*While* the orchestrator is in the external-events step of a cycle ([EXEC-001] step 2), no terminal place is marked, the executor is neither closed ([ENV-013]) nor terminated immediately ([ENV-015]) and its queue of accepted events is not empty, the orchestrator *shall* inject the oldest entry.⟧

**Acceptance Criteria:**
1. inject() can be called from a different thread than the orchestrator.
2. Multiple concurrent inject() calls do not cause data races.
3. Injected tokens are eventually processed by the orchestrator, unless the executor is closed, terminated immediately, stops because a terminal place is marked or ends its run on a cancellation it observes in its wait before it processes them.

**Depends on:** [ENV-002], [ENV-013], [ENV-015], [CONC-010], [EXEC-001], [EXEC-041], [EXEC-042]
**Test derivation:** Spawn 10 threads; each injects a token; verify all 10 tokens processed."#
