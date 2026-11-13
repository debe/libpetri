import Libpetri.Spec.Text

requirement_text CORE_033
  id "CORE-033"
  title "Read Arc Multi-Reader"
  priority MUST
  kind B
  body r#"Multiple transitions can have read arcs to the same place. ⟦s1|*While* a place is marked, a read arc to that place *shall not* stop its transition from firing, so all transitions with read arcs to the place can be enabled simultaneously.⟧ ⟦s2|*When* a transition with a read arc to a marked place fires, and the transition has no input arc and no reset arc to that place, the read arc of any transition to that place *shall not* stop that transition from firing afterwards (no conflict), since read arcs do not consume tokens.⟧

**Acceptance Criteria:**
1. Two transitions with read arcs to the same place are both enabled when the place has tokens.
2. Both can fire without conflict.

**Depends on:** [CORE-032]
**Test derivation:** Two transitions read from the same place; verify both can fire."#
