import Libpetri.Spec.Text

requirement_text VER_011
  id "VER-011"
  title "DBM Zone Representation"
  priority MAY
  kind F
  body r#"Timing constraints within a state class are represented as a Difference Bound Matrix (DBM), encoding constraints of the form `θᵢ - θⱼ ≤ cᵢⱼ` where θᵢ is the firing time of transition i: the time from entering the class until it fires.

⟦s1|*When* the zone library creates a zone from one lower and one upper bound per clock, the zone *shall* hold exactly the firing times that lie between the bounds of each clock.⟧

⟦s2|Canonicalising a zone *shall not* change the firing times it holds.⟧

⟦s3|*When* a zone holds some firing times, its canonical matrix *shall* be closed: no bound exceeds the sum of the two bounds of a detour through any clock of the matrix, the reference clock included.⟧

⟦s4|The zone library *shall* report a zone empty only when it holds no firing times.⟧

⟦s5|*If* every finite bound of a zone is a whole number of milliseconds and every clock, the reference clock included, has a finite lower bound, *then* the zone library *shall* report the zone empty exactly when it holds no firing times.⟧

⟦s6|*When* a transition fires from a zone, the successor zone, with the persistent clocks first in the order given and the newly enabled clocks after them, *shall* hold every firing time the firing rule allows: the fired clock is not later than any other clock, each persistent clock keeps the time it had left after the fired clock, and each newly enabled clock lies between its static bounds.⟧

⟦s7|*When* the clocks of a zone that holds some firing times are permuted, the zone library *shall* keep the reference clock first, move every other bound of the matrix with its two clocks, and write zero as the bound of the reference clock against itself.⟧

⟦s8|*If* two zones each hold some firing times and every finite bound of both is a whole number of milliseconds, *then* their dedup keys *shall* be equal exactly when their matrices are equal entry by entry, the bounds between two clocks included.⟧

**Acceptance Criteria:**
1. DBM encodes lower and upper bounds for each transition clock.
2. Zone emptiness is detectable (unsatisfiable constraints).
3. Successor DBM is computed correctly after transition firing.
4. The zone exposes a dedup key over its full canonical matrix (every `θᵢ - θⱼ` bound, not
   only the diagonal projections), and a permutation of its clocks that reorders the matrix
   with them; equality is positional over the canonical order ([VER-010] AC1). The key renders
   each finite bound to the millisecond, so on zones that hold some firing times it is exact
   when every finite bound is a whole number of milliseconds.

**Depends on:** [VER-010]

**Implementation notes:**
- Java: Full implementation
- TypeScript: Full implementation
- Rust: Full implementation (`libpetri-verification` `dbm`)

**Test derivation:** Create DBM for 3 timed transitions; fire one; verify successor zone constraints."#
