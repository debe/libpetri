import Libpetri.Spec.Text

requirement_text CORE_070
  id "CORE-070"
  title "Marking State"
  priority MUST
  kind F
  body r#"⟦s1|A marking represents the current distribution of tokens across all places.⟧ ⟦s2|Internally, each place maps to a FIFO queue of tokens.⟧

⟦s3|A marking *shall* hold a queue of tokens for each place of its net, oldest token first, and the token count of a place *shall* be the length of its queue.⟧

⟦s4|An empty marking *shall* hold no token in any place.⟧

⟦s5|*When* a token is added to a place, the marking *shall* append it at the tail of that place's queue and leave the queue of every other place unchanged.⟧

⟦s6|*When* the first token of a marked place is removed, the marking *shall* return the head of that place's queue and keep the rest of that queue in order, leaving the queue of every other place unchanged.⟧

⟦s7|*If* the first token of a place that is not marked is removed, *then* the marking *shall* return no token and change no queue.⟧

⟦s8|*When* a token is added to or removed from a marking, the resulting marking *shall* still hold a queue for each place of its net.⟧

**Acceptance Criteria:**
1. Empty marking has zero tokens in all places.
2. Tokens can be added and removed from specific places.
3. Token count per place is queryable.

**Test derivation:** Create empty marking; add 3 tokens to place P; verify count is 3; remove one; verify count is 2."#
