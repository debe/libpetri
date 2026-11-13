import Libpetri.Spec.Text

requirement_text CONC_001
  id "CONC-001"
  title "Orchestrator Thread Ownership"
  priority MUST
  kind B
  body r#"⟦s1|All marking state (token queues, enablement flags, enabled-at timestamps) is owned and mutated exclusively by a single logical orchestrator thread.⟧ No locking or synchronization is needed for marking access.

⟦s2|A step that the orchestrator does not take (an action writing, flushing a batch ([IO-015]) or returning, the budget of an action expiring, a caller requesting an injection or draining, closing or terminating the executor, or the firing clock advancing) *shall not* change the clock status of a transition (its enablement flag, its enabled-at timestamp, its restart flag or its reaped mark) or the orchestrator's current cycle (its phase, its clock reading, the transitions its firing pass has still to try, whether the pass has started one, and the tokens the pass has deposited).⟧

⟦s3|A step that neither starts a firing nor deposits the outcome of a firing, a flushed batch or an injected event *shall not* change the token queues.⟧

⟦s4|The orchestrator *shall not* deposit the produced tokens of a firing before the firing's action has returned, deposit its timeout outcome before its budget has expired, or settle it without a deposit before either has happened.⟧

⟦s5|The orchestrator *shall not* deposit a flushed batch of a firing before the firing's action has flushed a batch.⟧

⟦s6|The orchestrator *shall not* inject an event before a caller's request to inject it has been accepted.⟧

**Acceptance Criteria:**
1. Marking has no locks, mutexes, or atomic operations.
2. Only the orchestrator thread writes the marking; a thread other than the orchestrator reads it only as [ENV-014] allows.
3. Action completion results are communicated back via a thread-safe mechanism, then applied on the orchestrator thread.

**Test derivation:** Inspect marking implementation for absence of synchronization primitives."#
