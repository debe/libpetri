import Libpetri.Spec.Text

requirement_text IO_010
  id "IO-010"
  title "Output Place (Leaf)"
  priority MUST
  kind B
  body r#"⟦s1|`Place(place)` is a leaf node of an output spec that names a single output place.⟧

⟦s2|*When* a transition whose output spec is `Place(place)` fires, it *shall* deposit one or more tokens in `place`.⟧

⟦s3|*When* a transition whose output spec is `Place(place)` fires, it *shall not* deposit a token in any other place.⟧

⟦s4|*When* a transition whose output spec is `Place(place)` fires, the marking the firing leaves *shall* hold in `place` the tokens the firing deposited there, in addition to the tokens `place` kept through the firing.⟧

⟦s5|This requirement applies to an executor with output validation enabled, which is the default ([CONC-026]).⟧

**Acceptance Criteria:**
1. Output spec declares a single place.
2. Produced tokens appear in the place.

**Test derivation:** Transition with Place output; action produces token; verify it appears."#
