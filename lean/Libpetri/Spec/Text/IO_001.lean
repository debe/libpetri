import Libpetri.Spec.Text

requirement_text IO_001
  id "IO-001"
  title "Input One"
  priority MUST
  kind B
  body r#"⟦s1|`One(place)` is an input arc whose required count and consumption count are both 1.⟧

⟦s2|*While* the input place of a `One` input arc is unmarked, the transition *shall not* fire.⟧

⟦s3|*While* the input place of a `One` input arc is marked and is not a correlated input of the transition's match specification ([NU-020]), the arc *shall not* affect whether the transition can fire.⟧

⟦s4|*When* a transition with a `One` input arc fires, it *shall* consume exactly 1 token from the input place.⟧

⟦s5|*When* a transition with a `One` input arc fires, and the input place is neither a reset place nor an output place of the transition, the input place *shall* end the firing holding exactly 1 fewer token than it held before the firing.⟧

- `requiredCount()` returns 1
- `consumptionCount(available)` returns 1

**Acceptance Criteria:**
1. Transition enables when place has >= 1 token.
2. Exactly 1 token consumed on firing (the oldest).
3. Remaining tokens stay in place.

**Depends on:** [CORE-030]
**Test derivation:** Place with 3 tokens; fire transition with One; verify 1 consumed, 2 remain."#
