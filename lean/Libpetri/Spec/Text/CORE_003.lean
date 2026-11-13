import Libpetri.Spec.Text

requirement_text CORE_003
  id "CORE-003"
  title "Place Type Safety"
  priority MUST
  kind A
  body r#"⟦s1|A place has a declared token type, and a token is compatible with a place when its value is of that type.⟧ ⟦s2|A token without a value, the unit token ([CORE-012]), is compatible with every place.⟧ ⟦s3|The engine does not check the type of a token it deposits or a host adds: the net's author and the host keep an action's outputs, a forwarded token ([IO-014]) and an injected token compatible with their places.⟧ An implementation that keeps a run-time token type for each place (Java) rejects an initial marking that puts a token with an incompatible value in a place. Where an API call takes a typed place handle (Java, TypeScript and Rust), the compiler rejects a token of another type at that call; this requirement does not rely on it.

⟦s4|*When* a transition fires from a marking in which every token is compatible with its place, nothing else changes the marking between the firing's consumption and its deposit, and every token the firing deposits is compatible with the place it is deposited to, every token a place holds after the firing *shall* be compatible with that place.⟧

⟦s5|*When* a transition fires from a marking in which every token is compatible with its place, every token its action receives from one of its input places or read places *shall* be compatible with that place.⟧

⟦s6|*When* a transition can fire from a marking and deposit tokens to a list of places, it *shall* also be able to fire from that marking, delivering the same tokens to its action, and deposit to the same places, in the same order, any tokens compatible with them, except that a relay target of a match specification takes only tokens carrying the matched name ([NU-054]).⟧

**Acceptance Criteria:**
1. ⟦s7|A firing whose action outputs a token with a compatible value to a place succeeds.⟧
2. In an implementation that keeps a run-time token type for each place, an initial marking that puts a token with an incompatible value in a place is rejected.

**Test derivation:** Create a place of type Integer and a transition that outputs to it; fire it with an action that outputs an integer token (succeeds). In Java, build an executor whose initial marking puts a string token in that place (rejected with an `IllegalArgumentException`)."#
