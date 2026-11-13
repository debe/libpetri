import Libpetri.Spec.Text

requirement_text CORE_054
  id "CORE-054"
  title "Produce Action"
  priority SHOULD
  kind F
  body r#"A built-in action that produces a fixed value to a specified output place.

⟦s1|*When* the built-in produce action of a place and a value runs on a transition whose output spec names that place, the action *shall* complete with exactly one output token, which carries that value and goes to that place, and with no output token in any other place.⟧

⟦s2|*If* the built-in produce action of a place and a value runs on a transition whose output spec does not name that place, *then* the action *shall* fail.⟧

**Acceptance Criteria:**
1. The specified place receives a token with the fixed value.

**Test derivation:** Produce action with value "hello" to place P; verify P receives "hello"."#
