import Libpetri.Spec.Text

requirement_text IO_003
  id "IO-003"
  title "Input All"
  priority MUST
  kind B
  body r#"`All(place)` is an input arc that drains its place: its required count is 1 and its consumption count is every token the place holds.

- `requiredCount()` returns 1
- `consumptionCount(available)` returns `available`

⟦s1|*While* the place of an `All` input arc of a transition is unmarked, the transition *shall not* fire.⟧

⟦s2|*While* the place of an `All` input arc of a transition is marked and is not a correlated input of the transition's match specification ([NU-020]), the `All` input arc *shall not* affect whether the transition can fire.⟧

⟦s3|*When* a transition fires, it *shall* consume every token from the place of each of its `All` input arcs that is not a correlated input of its match specification ([NU-020]).⟧

⟦s4|*When* a transition fires, the place of each of its `All` input arcs that is neither an output place of the transition nor a correlated input of its match specification *shall* end the firing empty.⟧

On a correlated input of a match specification, an `All` input arc consumes every token of the chosen name and leaves the tokens of other names in the place ([NU-020]).

**Acceptance Criteria:**
1. Transition enables when place has >= 1 token.
2. All tokens consumed on firing (place empty after).
3. Place with 0 tokens → transition not enabled.

**Depends on:** [CORE-030]
**Test derivation:** All on place with 5 tokens; verify all 5 consumed, place empty."#
