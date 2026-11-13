import Libpetri.Spec.Text

requirement_text IO_002
  id "IO-002"
  title "Input Exactly"
  priority MUST
  kind B
  body r#"⟦s1|`Exactly(place, n)` is an input arc whose required count and consumption count are both N, where N >= 1.⟧

⟦s2|*While* the input place of an `Exactly(n)` input arc holds fewer than N tokens, the transition *shall not* fire.⟧

⟦s3|*When* a transition with an `Exactly(n)` input arc fires, it *shall* consume exactly N tokens from the input place.⟧

⟦s4|*When* a transition with an `Exactly(n)` input arc fires, and the input place is neither a reset place nor an output place of the transition, the input place *shall* end the firing holding exactly N fewer tokens than it held before the firing.⟧

- `requiredCount()` returns N
- `consumptionCount(available)` returns N (when available >= N)

**Acceptance Criteria:**
1. ⟦s5|Construction with N < 1 is rejected (error or panic). Where the language lets the spec be
   written out without the constructor (a public enum variant, an object literal), building
   the transition rejects it.⟧
2. Transition enables only when place has >= N tokens.
3. Exactly N tokens consumed on firing (the N oldest, FIFO).
4. Place with N-1 tokens → transition not enabled.

**Depends on:** [CORE-030]
**Test derivation:** Exactly(5) on place with 7 tokens; verify 5 consumed, 2 remain. Verify disabled with 4 tokens."#
