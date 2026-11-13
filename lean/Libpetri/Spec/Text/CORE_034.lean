import Libpetri.Spec.Text

requirement_text CORE_034
  id "CORE-034"
  title "Reset Arc"
  priority MUST
  kind B
  body r#"A reset arc connects a place to a transition.

⟦s1|*When* a transition fires, each of its reset places *shall* lose every token it held before the firing and end the firing holding exactly the tokens the firing deposited there.⟧

⟦s2|A reset arc *shall not* affect whether its transition can fire, whether the reset place is marked or not.⟧

⟦s3|A reset arc *shall not* change what its transition can deposit: from every marking, the transition and the same transition without its reset arcs *shall* be able to make exactly the same deposits, so a reset arc neither adds a deposit nor removes one.⟧

⟦s4|A reset arc *shall not* change the token count of any place other than its own.⟧

**Acceptance Criteria:**
1. Transition with reset arc fires even if the reset place is empty.
2. If the reset place has tokens, all are removed on firing.
3. Reset arc does not contribute to enablement (no token requirement).
4. From the same marking, a transition with a reset arc and the same transition without it
   make the same deposits, compared per place ([CORE-036]): a reset arc on one of its output
   places neither adds an outcome nor removes one.

**Test derivation:** Fire transition with reset arc on place with 3 tokens; verify all tokens removed. Fire again with empty place; verify no error. Give `t: a → xor(b, c)` a reset arc on `b`; from a marking with 2 tokens in `b`, verify the firings of `t` deposit `{b}` or `{c}`, exactly as `t` without the reset arc does, and that `b` ends holding the deposited token alone."#
