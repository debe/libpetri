import Libpetri.Spec.Text

requirement_text CONC_010
  id "CONC-010"
  title "Orchestrator Wake-Up"
  priority MUST
  kind B
  body r#"⟦s1|When the orchestrator is idle (no transitions ready, waiting for work), it must be woken by each of these causes:⟧
1. ⟦s2|**Action completion:** an action returns, or its timeout expires ([EXEC-022]), and its outcome is queued for the orchestrator.⟧
2. ⟦s3|**External event injection:** `inject()` accepts a token for an environment place ([ENV-003]).⟧
3. ⟦s4|**Timer expiry:** the timer the wait set for a timing boundary of an armed transition runs out.⟧
4. ⟦s5|**Lifecycle:** the executor is drained ([ENV-011]), closed ([ENV-013]) or terminated immediately ([ENV-015]).⟧
5. ⟦s6|**Publication:** an action's flush queues a batch of outputs before the action returns ([IO-015]), in an implementation with mid-action publication.⟧ ⟦s7|A flush that the join-relay check rejects ([NU-054]) queues nothing and is no wake cause; the firing then ends with an error when its action returns.⟧

The wait may also end for no reason, such as a spurious wake-up or a periodic re-check behind the direct wake-up ([TIME-015]). A snapshot request ([ENV-014]) may be answered from the wait without ending it. The wake-up mechanism is implementation-specific (semaphore, notify, promise resolution, channel select) but must be responsive: a wake-up does not depend on a poll interval.

A drain, a close or an immediate termination that comes after the cycle's termination test and before the block is not lost either: the runtimes keep the signal until the wait reads it (Rust's signal channel, Java's semaphore permit, TypeScript's latched wake-up), and the wait then ends at once. The rules below do not state this case yet, so it is tested, not proven.

⟦s8|A timing boundary of an armed transition is its earliest bound, while its elapsed time has not reached it, and, for a reapable transition, the reading at which it becomes expired ([TIME-013]).⟧ ⟦s9|The orchestrator judges Ready, Expired and the timing boundaries for its wait at the firing-clock reading its deadline step took in the current cycle ([EXEC-001] step 4), which is not earlier than the reading of its enablement update ([TIME-010]).⟧ [TIME-010] rules out judging them at a later reading of the same cycle, although that would only park less often and set an earlier timer.

⟦s10|*While* the outcome of an action, a flushed publication or an accepted injection is queued and not yet processed, the executor *shall not* block in its wait ([EXEC-001] step 6).⟧

⟦s11|*While* a transition is Ready or Expired at the reading of the cycle's deadline step, the executor *shall not* block in its wait.⟧

⟦s12|*When* an action's outcome is queued, an action's flush queues a publication, `inject()` accepts a token, or the executor is drained, closed or terminated immediately, the executor *shall* end any block of its wait at once and be ready to leave the wait for the start of its loop ([EXEC-001] step 1) without waiting for a timer.⟧

⟦s13|*When* the executor blocks in its wait while an armed transition has a timing boundary ahead, it *shall* set a timer no longer than the time from the reading of the cycle's deadline step to the nearest such boundary, plus the timer resolution.⟧

⟦s14|*When* an action returns or its timeout expires, the executor *shall* queue the action's outcome for the orchestrator.⟧

⟦s15|So no queued work waits for a timer or a poll, and a wait with a timing boundary ahead carries a timer that runs out no later than that boundary, within timer resolution, counted from the reading of the cycle's deadline step.⟧ Ending the wait when that timer runs out is the work of the host timer ([TIME-015]).

**Acceptance Criteria:**
1. Injecting a token into an environment place wakes the orchestrator immediately.
2. Action completion wakes the orchestrator.
3. A wait with a timing boundary of an armed transition ahead sets a timer of at most the time to that boundary plus the timer resolution, counted from the reading of the cycle's deadline step, so that, if the transition is still armed, the cycle the timer starts finds it ready ([TIME-010]) or reaps it ([TIME-013]) without another cause.
4. A drain, a close or an immediate termination ends a block of the wait at once.

**Test derivation:** Inject token while orchestrator is idle; measure latency to processing."#
