import Libpetri.Spec.Text

requirement_text EXEC_040
  id "EXEC-040"
  title "Standard Quiescence"
  priority MUST
  kind B
  body r#"⟦s1|When no environment places are registered and the net has no terminal places ([EXEC-042]), the executor terminates when ALL of the following hold at the termination test of a cycle, which follows the cycle's enablement update and deadline step ([EXEC-001]):⟧
1. ⟦s2|No transition is armed ([TIME-010]).⟧ ⟦s3|A reaped transition that is still enabled holds no clock and does not keep the executor running ([TIME-013]).⟧
2. ⟦s4|No transitions are in-flight (executing actions).⟧ ⟦s5|A firing counts as in flight until its completion and its queued publications are processed.⟧
3. ⟦s6|No external events are pending.⟧

⟦s7|The final marking is returned.⟧

⟦s8|The test is made there and nowhere else: straight after a deposit, before the next enablement update, a transition the deposit enabled is not yet armed ([TIME-010]), so the three conditions can hold while the net still has work to do.⟧

⟦s9|*While* no terminal place is marked ([EXEC-042]), *when* the termination test of a cycle finds that no transition is armed, no firing is in flight and no completion, publication or external event is queued, an executor without environment places *shall* terminate and *shall* return the marking as it is.⟧

⟦s10|An executor without environment places *shall not* terminate as quiescent ([EXEC-041]) anywhere in a cycle except at its termination test.⟧

⟦s11|*When* an executor without environment places takes a step other than an enablement update or a deadline step, it *shall not* terminate as quiescent until it has run an enablement update.⟧

⟦s12|*If* a transition is armed, a firing is in flight, or a completion, publication or external event is queued, *then* an executor without environment places *shall not* terminate as quiescent.⟧

**Acceptance Criteria:**
1. Simple chain A→B→C: executor runs to completion; returns marking with token in C.
2. Parallel branches: waits for all in-flight actions before terminating.

**Test derivation:** Linear chain of 5 transitions; verify executor returns marking with token at end."#
