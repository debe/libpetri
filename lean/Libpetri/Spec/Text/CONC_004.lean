import Libpetri.Spec.Text

requirement_text CONC_004
  id "CONC-004"
  title "Bitmap-Based Enablement Check"
  priority MUST
  kind F
  body r#"The primary executor uses precomputed bitmasks for O(1) enablement checking per transition (proportional to the number of machine words needed to represent all places).

Each transition has precomputed masks:
- **needs-mask**: bits set for all input + read places (all must have tokens)
- **inhibitor-mask**: bits set for all inhibitor places (none may have tokens)

Enablement check: `(marking & needs-mask) == needs-mask AND (marking & inhibitor-mask) == 0`

⟦s1|The presence check of a transition *shall* pass on a bitmap exactly when every bit of its needs-mask is set in the bitmap and no bit of its inhibitor-mask is set.⟧

**Acceptance Criteria:**
1. Enablement is checked via bitwise operations, not by iterating over arcs.
2. A transition with 3 inputs and 2 reads requires only 1-2 bitwise operations.
3. The check is O(W) where W = ceil(numPlaces / word_size).

**Test derivation:** Net with 100 places; verify enablement check performance is constant per transition."#
