import Libpetri.Spec.Text

requirement_text CONC_007
  id "CONC-007"
  title "Compiled Net Representation"
  priority MUST
  kind F
  body r#"The bitmap executor compiles the net into an integer-indexed representation where places and transitions are assigned stable numeric IDs (0-based). This enables array-based access instead of hash map lookups.

Precomputed data includes:
- Per-transition: needs-mask, inhibitor-mask, consumption places (the IDs of its input and reset places)
- Per-place: list of affected transition IDs (reverse index)
- Per-transition: cardinality check (needed for a transition with an input that requires more than one token)
- Per-transition: match presence flag (whether the transition carries a ν-match specification, [NU-020])

Stable means that the IDs stay fixed for the life of the compiled net. The order in which places are numbered is not specified; transitions are numbered in declaration order.

⟦s1|The compiled net *shall* number the places of the net from 0 to P-1, where P is the number of places of the net, so that each place has exactly one ID and each ID names exactly one place.⟧

⟦s2|The compiled net *shall* give each transition its declaration position as its ID, numbering the transitions from 0 in the order the net declares them.⟧

⟦s3|The needs-mask of a transition *shall* hold exactly the IDs of its input and read places, and its inhibitor-mask exactly the IDs of its inhibitor places.⟧

⟦s4|The consumption places of a transition *shall* be exactly the IDs of its input and reset places.⟧

⟦s5|The reverse index *shall* map the ID of each place to exactly the IDs of the transitions that have an input, read, inhibitor or reset arc on that place.⟧

⟦s6|*If* a transition has no cardinality check, *then* each of its inputs *shall* require at most one token.⟧

⟦s7|Each entry of a cardinality check *shall* be the ID of an input place of the transition with the required count of that input, and each input that requires more than one token *shall* have an entry.⟧

⟦s8|The compiled net *shall* set the match presence flag of a transition exactly when the transition carries a match specification ([NU-020]).⟧

**Acceptance Criteria:**
1. Places and transitions have stable numeric IDs.
2. All masks are precomputed at compilation time, not at each enablement check.

**Test derivation:** Compile a net; verify masks match expected bit patterns."#
