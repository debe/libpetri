import Libpetri.Spec.Text

requirement_text EXEC_030
  id "EXEC-030"
  title "Action Failure"
  priority MUST
  kind B
  body r#"⟦s1|If an action throws an exception or returns an error, the executor:⟧
1. ⟦s2|Emits a TransitionFailed event with error details.⟧
2. ⟦s3|Does NOT restore consumed input tokens (no rollback).⟧
3. ⟦s4|The transition is no longer in-flight.⟧
4. ⟦s5|Execution continues with remaining transitions.⟧

⟦s6|A firing fails when its action throws an exception or returns an error, or when output validation or the join-relay check of [NU-054] rejects its outcome ([EXEC-021]).⟧

⟦s7|*If* a firing fails, *then* the executor *shall* emit a TransitionFailed event ([EVT-008]) and *shall not* change the marking: it *shall not* restore the tokens the firing consumed and *shall not* deposit any token its action produced at completion.⟧

⟦s8|*If* a firing fails, *then* the executor *shall* remove that firing from the firings in flight and its outcome from the queued outcomes, and *shall* leave every other firing in flight as it was and the other queued outcomes as they were, in the order they arrived.⟧

⟦s9|*Where* an executor starts a transition again while an earlier firing of it is in flight ([CONC-002]), *if* one of those firings fails, *then* the executor *shall* leave the other firings of that transition in flight.⟧

⟦s10|*If* a firing fails, *then* the executor *shall not* end the run and *shall not* change its lifecycle mode, and a failure inside a firing pass *shall* leave the pass to go on with its remaining transitions.⟧

⟦s11|*If* a firing fails, *then* the executor *shall* leave the clock of every transition as it was, so that the next enablement update ([EXEC-001] step 3) evaluates the transition of the failed firing as it evaluates any other transition.⟧

⟦s12|A fault of the host runtime itself is not an action failure: in Java, a `VirtualMachineError` or a `LinkageError` thrown inside a firing ends the run with that error, which [EXEC-041] requires the caller to be able to tell apart from quiescence.⟧

**Acceptance Criteria:**
1. Failing action → TransitionFailed event with error message and type.
2. Consumed tokens are lost (not returned to input places).
3. Other transitions continue to fire.

**Depends on:** [EVT-008], [CONC-002], [NU-054]
**Test derivation:** Action throws; verify failure event; verify consumed tokens not restored; verify net continues."#
