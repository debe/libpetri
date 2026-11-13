import Libpetri.Spec.Text

requirement_text CORE_021
  id "CORE-021"
  title "Transition Identity"
  priority MUST
  kind F
  body r#"Each transition instance, the result of one build call, has a unique identity. Two transitions built by separate build calls are never equal, even if they share the same name. A copy of a built transition (a Rust clone) is the same instance and is equal to it.

⟦s1|*When* two transitions are built by separate build calls, the two built transitions *shall not* be equal, even if they share the same name or were given the same definition.⟧

⟦s2|Every built transition *shall* be equal to itself.⟧

**Acceptance Criteria:**
1. Two transitions built with the same name are not equal (identity-based, not name-based).
2. A transition is equal to itself.

**Test derivation:** Build two transitions with name "Process"; verify they are not equal."#
