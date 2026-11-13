import Libpetri.Spec.Text

requirement_text NU_060
  id "NU-060"
  title "Match-Arc Composition"
  priority SHOULD
  kind F
  body r#"⟦s1|A correlated input behaves, under channel composition ([MOD-021]), as the input
arc it layers on: its arc dedup/conflict rules are unchanged.⟧ ⟦s2|A merge MUST NOT
silently drop a match, and no implementation fuses two matches into one: when both
merged sides carry a match, whatever places the two matches correlate, the merge
MUST be rejected with an error naming the caller-side transition.⟧

⟦s3|*When* at most one side of a channel merge carries a match, the channel merge *shall* reject with the same error when the same merge of the two transitions without their matches rejects, and otherwise *shall* give the merged transition of that merge with that side's match unchanged, or with no match when neither side carries one.⟧

⟦s4|*If* both sides of a channel merge carry a match, *then* the channel merge *shall* be rejected with an error that names the caller-side transition.⟧

A correlated input is therefore merged by the canonical input-arc merge table like any
other input arc: a correlated `one()` and the other side's `one()` on the same place give
one `exactly(2)` arc that the surviving match still correlates. The other side's token on
that place is then a token of the chosen name, not the oldest token. Which error a merge reports
when it also breaks a rule of [MOD-021] is not specified.

**Acceptance Criteria:**
1. Composing a transition that carries a match with a side that carries none
   preserves the match on the flat net (it is not dropped).
2. A merge of two transitions that both carry a match is rejected with an error
   naming the caller-side transition, whatever places the two matches correlate.

**Depends on:** [MOD-021], [NU-020], [NU-054]
**Test derivation:** Channel-merge a matched transition with a passthrough side;
verify the composed transition still correlates. Channel-merge two matched transitions
whose matches key different places; verify the merge is rejected naming the caller-side
transition."#
