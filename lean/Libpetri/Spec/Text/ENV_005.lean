import Libpetri.Spec.Text

requirement_text ENV_005
  id "ENV-005"
  title "inject() Wake-Up"
  priority MUST
  kind T
  body r#"⟦s1|Injecting a token wakes the orchestrator from idle immediately.⟧ ⟦s2|The orchestrator does not need to wait for a timer or poll.⟧

**Acceptance Criteria:**
1. Orchestrator is idle (no ready transitions).
2. External inject() call wakes orchestrator.
3. Token is processed promptly (within one cycle).

⟦s3|An injection is queued from the moment inject() accepts it ([ENV-003]) until it leaves the queue: the executor puts its token into the marking, or, once the executor is closed or stopped or the run has ended, discards it ([ENV-013], [ENV-015], [EXEC-042]).⟧

Once the executor is closed, an event that Java or TypeScript still holds in its queue counts as discarded from the first external-events step or wait after the close, though its inject() is answered only when the loop ends ([ENV-013], [ENV-004]).

⟦s4|An injection that inject() accepts after the external-events step of a cycle has last read the queue counts as accepted after that step ends, and is left to the next cycle.⟧

⟦s5|*While* an accepted injection is queued, the executor *shall not* block in its wait ([EXEC-001] step 6, [CONC-010]), neither at the end of a cycle nor again after it has answered something during the wait, such as a marking snapshot.⟧

⟦s6|*When* inject() accepts a token, the executor *shall* end any block of its wait at once, without waiting for a timer.⟧

⟦s7|*While* an accepted injection is queued and the executor is in its wait with no terminal place marked, the executor *shall* be able to leave the wait at once, by waking up or by taking a queued injection from the queue, without waiting for a timer.⟧

⟦s8|*While* an accepted injection is queued, the executor *shall not* end the external-events step of a cycle and *shall not* start the enablement update of a cycle ([EXEC-001] steps 2 and 3).⟧

⟦s9|Read with the definition of queued above, this means that a token accepted while the executor waits has left the queue before the enablement update of the cycle the wake-up starts, and is in the marking by then unless the run has closed, stopped or ended first; the earlier sentences mean that no timer or polling is needed to find it.⟧

⟦s10|The requirement on the external-events step covers every injection queued during that step, not only those queued when it begins ([EXEC-001] step 2), so the step has no limit on how many injections it takes.⟧

⟦s11|The words immediately, promptly and at once mean that nothing in the executor waits between the acceptance and the injection; the latency itself is tested, not proven.⟧

⟦s12|Under a host clock an implementation may leave the wait to the host ([TIME-015]); the wait these sentences speak of is then the host's, and [TIME-015] requires its readiness predicate to observe the queued injection.⟧

**Depends on:** [CONC-010], [ENV-003], [ENV-013], [ENV-015], [EXEC-001], [EXEC-042], [TIME-015]
**Test derivation:** Start executor with environment places; wait for quiescence; inject token; verify processing within milliseconds."#
