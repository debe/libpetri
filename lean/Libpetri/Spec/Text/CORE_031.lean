import Libpetri.Spec.Text

requirement_text CORE_031
  id "CORE-031"
  title "Inhibitor Arc"
  priority MUST
  kind B
  body r#"An inhibitor arc connects a place to a transition as a **negative precondition**.

⟦s1|*While* an inhibitor place of a transition is marked, the transition *shall not* fire.⟧

⟦s2|*While* an inhibitor place of a transition is unmarked, the inhibitor arc *shall not* affect whether the transition can fire.⟧

The inhibitor arc does not consume tokens.

**Acceptance Criteria:**
1. Inhibitor place empty → transition enablement unaffected by inhibitor.
2. Inhibitor place has tokens → transition disabled.
3. Firing a transition consumes nothing through its inhibitor arcs; another transition's input arc on the same place consumes as [CORE-030] says.

**Test derivation:** Create transition with inhibitor; verify disabled when inhibitor place has tokens, enabled when empty."#
