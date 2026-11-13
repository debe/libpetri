import Libpetri.Spec.Text

requirement_text IO_004
  id "IO-004"
  title "Input AtLeast"
  priority MUST
  kind B
  body r#"`AtLeast(place, minimum)` — waits for at least `minimum` tokens, then drains all when enabled.

- `requiredCount()` returns `minimum`
- `consumptionCount(available)` returns `available` (consumes all when available >= minimum)

⟦s1|*While* the input place of an `AtLeast(place, minimum)` input arc holds fewer than `minimum` tokens, the transition *shall not* fire.⟧

⟦s2|*While* the input place of an `AtLeast(place, minimum)` input arc holds at least `minimum` tokens and is not a correlated input of the transition's match specification ([NU-020]), the input arc *shall not* affect whether the transition can fire.⟧

⟦s3|*When* a transition with an `AtLeast(place, minimum)` input arc fires, it *shall* consume every token the input place holds, unless the input place is a correlated input of its match specification ([NU-020]).⟧

⟦s4|*When* a transition with an `AtLeast(place, minimum)` input arc fires, and the input place is neither an output place nor a correlated input of the match specification of the transition, the input place *shall* end the firing empty.⟧

On a correlated input of a match specification, an `AtLeast(place, minimum)` input arc requires and consumes the tokens of the chosen name only ([NU-020]).

**Acceptance Criteria:**
1. ⟦s5|Construction with minimum < 1 is rejected (error or panic), also when building a
   transition from a spec written out without the constructor, as for [IO-002].⟧
2. Transition enables when place has >= minimum tokens.
3. All tokens consumed on firing (not just minimum).
4. Place with minimum-1 tokens → transition not enabled.

**Depends on:** [CORE-030]
**Test derivation:** AtLeast(3) on place with 7 tokens; verify all 7 consumed. Verify disabled with 2 tokens."#
