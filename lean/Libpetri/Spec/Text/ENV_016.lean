import Libpetri.Spec.Text

requirement_text ENV_016
  id "ENV-016"
  title "Observable Termination"
  priority MAY
  kind B
  body r#"⟦s1|An implementation MAY provide `awaitTermination(timeout)`, which blocks until the orchestrator loop
has finished its termination bookkeeping (pending `inject()` futures completed, `ExecutionCompleted`
emitted), returning whether termination was observed within the timeout.⟧ ⟦s2|It returns promptly when the
loop was never started, and it MUST NOT itself be defeated by a failure in that bookkeeping (for
example a throwing event store).⟧

⟦s3|*Where* an implementation provides `awaitTermination`, *when* it is called on an executor whose loop was never started, the implementation *shall* answer true at once, without waiting for the timeout.⟧

⟦s4|*Where* an implementation provides `awaitTermination`, *when* it is called on an executor whose loop has started, the implementation *shall* wait until the loop has finished its termination bookkeeping or the timeout has expired, whichever comes first.⟧

⟦s5|*Where* an implementation provides `awaitTermination`, *when* its wait ends while the loop is still running, the implementation *shall* answer false.⟧

⟦s6|*Where* an implementation provides `awaitTermination`, the implementation *shall not* answer true for a run before the loop has taken the step that ends the run and, in that step, answered every accepted `inject()` still pending.⟧

⟦s7|*Where* an implementation provides `awaitTermination`, the implementation *shall not* answer true for a run while the emission of `ExecutionCompleted` ([EVT-003]) for that run is still to come.⟧

⟦s8|*Where* an implementation provides `awaitTermination`, *when* its wait ends after the loop has finished, the implementation *shall* answer true, even if a part of the termination bookkeeping failed, such as an event store that throws when the termination events are appended.⟧

⟦s9|*Where* an implementation provides `awaitTermination`, a failure in the termination bookkeeping *shall not* keep the call from returning its answer.⟧

⟦s10|These sentences on `awaitTermination` concern the first run of an executor; whether an executor may be run again, and what `awaitTermination` answers then, is not specified.⟧

⟦s11|Independently, run-with-timeout (`run(timeout)`, whose timeout is the caller's run budget named in
[EXEC-041]; its expiry fails the caller's wait and does not by itself end the run) MAY expose a
policy for what happens to the loop when the caller's timeout expires: *abandon* (leave the loop
running; the historical default, rarely desirable) or *close* (stop it per [ENV-013]).⟧ ⟦s12|The expiry
of the caller's timeout MUST NOT complete the loop's own result: an abandoned loop can still report
its real final marking.⟧

⟦s13|*Where* an implementation exposes this policy, *when* the caller's timeout expires while the loop is running, the implementation *shall* act on the expiry under the policy the caller chose.⟧

⟦s14|*When* the caller's timeout expires under *abandon*, the implementation *shall* leave the executor as it was, including its marking, its lifecycle mode, its queues, its firings in flight and the position of its loop, and a running loop *shall* go on running.⟧

⟦s15|*When* the caller's timeout expires under *close* while the executor is open or draining, the implementation *shall* close the executor as a call of `close()` does ([ENV-013]), even while its loop is running.⟧

⟦s16|*When* the caller's timeout expires under *close* after the executor is already closed or stopped, the implementation *shall* leave the executor as it was.⟧

⟦s17|*When* the caller's timeout expires while the loop is running, the implementation *shall not* end the run and *shall not* change the marking.⟧

**Acceptance Criteria:**
1. `awaitTermination` returns false while the loop is still running, true once it has stopped.
2. `awaitTermination` returns promptly (true) if the loop was never started.
3. ⟦s18|Under a *close* policy the executor is closed on timeout and the loop then stops as [ENV-013]
   says, once its in-flight actions complete; under *abandon* it keeps running.⟧

**Depends on:** [ENV-013], [EXEC-041]
**Status:** Proposed
**Test derivation:** Run a net whose action is still in flight when a short timeout expires, under
each policy; verify that under *close* the executor is closed and the loop stops once the action
completes, that under *abandon* the loop stays live and reports the action's output in its final
marking, and that `awaitTermination` reports the transition."#
