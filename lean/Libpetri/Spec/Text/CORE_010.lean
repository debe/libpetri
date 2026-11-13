import Libpetri.Spec.Text

requirement_text CORE_010
  id "CORE-010"
  title "Token Immutability"
  priority MUST
  kind B
  body r#"⟦s1|A token is an immutable value object consisting of a typed payload value and a creation timestamp.⟧ ⟦s2|Once created, neither the value nor the timestamp can be modified.⟧

⟦s3|*When* a transition fires and nothing else changes the marking between the firing's consumption and its deposit, every token a place holds after the firing *shall* be a token the place held before the firing, with the same value and creation timestamp, or a token the action emitted to that place, and the firing *shall* not duplicate any of these tokens.⟧

⟦s4|*When* a transition fires and nothing else changes the marking between the firing's consumption and its deposit, every token that a place without a reset arc of the transition held before the firing *shall* still be in that place after the firing, with the same value and creation timestamp, unless the action received it from that place as a consumed input.⟧

⟦s5|*When* a transition fires, every token its action receives from one of its input places or read places *shall* be a token that place held before the firing, with the same value and creation timestamp, and the action *shall* not receive a consumed token more often than its input place held it.⟧

**Acceptance Criteria:**
1. Token value is accessible after creation and matches the original.
2. Token timestamp is accessible after creation.
3. No API exists to mutate token fields after creation.

**Test derivation:** Create a token with value 42; verify value() returns 42 and timestamp is non-null."#
