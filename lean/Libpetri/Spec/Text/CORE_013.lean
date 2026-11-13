import Libpetri.Spec.Text

requirement_text CORE_013
  id "CORE-013"
  title "Token FIFO Ordering"
  priority MUST
  kind B
  body r#"⟦s1|Tokens within a place are stored in FIFO (first-in, first-out) order.⟧ ⟦s2|The oldest token is consumed first when a transition fires, except on a correlated input of a match specification ([NU-020]).⟧

⟦s3|*When* a transition fires and nothing else changes the marking between the firing's consumption and its deposit, each place that is neither one of its input places nor one of its reset places ([CORE-034]) *shall* end the firing holding its whole queue from before the firing, in queue order, followed by the tokens the firing deposited there, in the order the action produced them ([EXEC-020]).⟧

⟦s4|*When* a transition fires and nothing else changes the marking between the firing's consumption and its deposit, its action *shall* receive from each input place that is not a correlated input of its match specification ([NU-020]) the first tokens of the place's queue before the firing, in queue order; unless the place is also one of its reset places, the place *shall* end the firing holding the rest of that queue, in queue order, followed by the tokens the firing deposited there, in the order the action produced them ([EXEC-010], [EXEC-020]).⟧

**Acceptance Criteria:**
1. Adding tokens A, B, C in order, then consuming one, yields A.
2. Consuming again yields B.

**Depends on:** [CORE-001]
**Test derivation:** Add three tokens to a place; remove them one at a time; verify FIFO order."#
