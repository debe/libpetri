import Libpetri.Spec.Text

requirement_text EXEC_010
  id "EXEC-010"
  title "FIFO Token Consumption"
  priority MUST
  kind B
  body r#"⟦s1|When a transition fires, it consumes tokens from the oldest-first (FIFO) end of each input place's queue.⟧ ⟦s2|The number of tokens consumed is determined by the input cardinality's `consumptionCount(available)`.⟧

⟦s3|*When* a transition fires, it *shall* consume from each of its input places that is not a correlated input of its match specification ([NU-020]) the oldest tokens the place holds, as many as the consumption count of the input arc.⟧

⟦s4|*When* a transition fires, its action *shall* receive the tokens consumed from each input place that is not a correlated input of its match specification in queue order, the oldest first.⟧

⟦s5|*When* a transition fires, its action *shall* receive consumed tokens only from the input places of the transition.⟧

⟦s6|A correlated input of a ν-net match specification is the one exception to oldest-first consumption: it takes the matched tokens of the chosen name, oldest first among the tokens of that name, so it can pass over an older token of another name ([NU-020]).⟧ ⟦s7|Its non-correlated inputs consume as above.⟧

⟦s8|*When* a transition starts in a firing pass, it *shall* remove from each of its input places that is neither a reset place nor a correlated input of its match specification the oldest tokens the place holds, as many as the consumption count of the input arc counted on the pass-visible marking ([EXEC-003]).⟧

⟦s9|*When* a transition starts in a firing pass, its action *shall* receive from each of its input places that is not a correlated input of its match specification the oldest tokens the place holds, as many as that consumption count, in queue order.⟧

**Acceptance Criteria:**
1. Tokens added in order A, B, C; One consumes A.
2. Exactly(2) consumes A, B.
3. All consumes A, B, C.

**Depends on:** [CORE-013], [IO-007], [NU-020]
**Test derivation:** Add tokens with identifiable values; fire transition; verify consumed tokens match FIFO order."#
