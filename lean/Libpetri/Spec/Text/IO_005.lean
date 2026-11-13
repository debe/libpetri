import Libpetri.Spec.Text

requirement_text IO_005
  id "IO-005"
  title "Input AND-Join Semantics"
  priority MUST
  kind B
  body r#"All inputs on a transition are AND-joined: every input arc is a precondition, and all of them must hold in the same marking.

⟦s1|*While* any input place of a transition holds fewer tokens than the required count of its input arc, the transition *shall not* fire.⟧

⟦s2|*While* every input place of a transition that has no match specification ([NU-020]) holds at least the required count of its input arc, the input arcs *shall not* affect whether the transition can fire.⟧

**Acceptance Criteria:**
1. Transition with 3 inputs enables only when all 3 places have sufficient tokens.
2. If any one input is unsatisfied, the transition is disabled.

**Test derivation:** Transition with 3 inputs; satisfy 2 of 3; verify disabled. Satisfy all 3; verify enabled."#
