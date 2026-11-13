import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.Glossary
import Libpetri.Spec.Req.IO_016
import Libpetri.Spec.Text.IO_017

set_option linter.missingDocs true

/-!
# IO-017: allPlaces flattening (`spec/02-input-output-specs.md`)

IO-017 is a pure-function requirement (kind F): it fixes `allPlaces`, the function that collects
every place an output spec names, whatever its `And`/`Xor`/`Timeout` structure. The statement is
a predicate over a *place-set function* `A : Out N → Finset N`: an output spec goes in, a set of
places comes out. The witness is the glossary's `outPlaces` (the function `OutputArc` is defined
through) read as a set.

The five lines fix the function exactly (`IO_017_unique`). Two consequences are derived, not
stated: every place-set function that satisfies IO-017 returns the union of the output branches
of every branch enumeration that satisfies [IO-016] (`IO_017_union_of_branches`), and it names
exactly the output arcs of the glossary (`IO_017_outputArc`).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## The model: a place-set function -/

/-- A place-set function: the set of places each output spec names. It reads the output spec
alone. -/
abbrev AllPlaces (N : Type) := Out N → Finset N

/-- The reference place-set function: the glossary's `outPlaces` (every place an output spec
names, a `ForwardInput` contributing its `to`), read as a set. -/
def refAllPlaces {N : Type} [DecidableEq N] : AllPlaces N :=
  fun o => (outPlaces o).toFinset

/- The reference place-set function is the witness model of IO-017's `holds` theorem. -/
#spec_witness refAllPlaces

/-! ## IO-017: allPlaces Flattening -/

requirement IO_017
  id "IO-017"
  title "allPlaces Flattening"
  kind F
  scope "all output specs"
  source verbatim "spec/02-input-output-specs.md"
  covers IO_017.s1, IO_017.s2, IO_017.s3, IO_017.s4, IO_017.s5
  reading "Place(p) gives exactly the set {p};"
          "ForwardInput(from, to) gives exactly the set {to};"
          "And(l, r) gives exactly the union of the sets of l and r;"
          "Xor(l, r) gives exactly the union of the sets of l and r;"
          "Timeout(c) gives exactly the set of c."
  assumes "A place-set function is a function from an output spec alone to a finite set of places (`Finset`), so it is static by its type and has no order and no repetition: the text and every runtime return a set (Rust `HashSet<PlaceRef>`, Java `Set<Place<?>>`, TypeScript `Set<Place<any>>`). The lines compare sets with equality, so they fix the function exactly (`IO_017_unique`)."
          "The lines say \"be\" and \"holding only\": the set equals the places the text names, so it is complete (every place, every `Xor` alternative, every `Timeout` child) and exact (nothing else). The markdown's prose (\"collect all leaf places\") and test derivation (\"complete set\") state completeness only; the block reads collecting the leaf places as returning them and nothing else, which is what all three runtimes do (Rust `rust/libpetri-core/src/output.rs` `collect_places`, Java `Arc.java` `allPlaces`, TypeScript `out.ts` `collectPlaces`). The containment reading is strictly weaker (`IO_017_mutant_superset_killed`), and a `Place` leaf that also names another place is forbidden (`IO_017_forbids_placeExtra`)."
          "The statement is generic in the place type `N` and its equality, so the set is a set under the implementation's own place identity, which CORE-002 fixes as the name or the name and the token type (line 3, ruling D82 (a)); the glossary entry Same set of places means that identity. Rust's set compares `PlaceRef` by name and Java's set compares `Place` records by name and token type (MOD-024), so both meet the lines under their identity. TypeScript's identity is the name (CORE-002 line 2), and `allPlaces` and `collectPlaces` (`typescript/src/core/out.ts`) collect into a map from name to place, keeping the first object met for each name, so two separate place objects of one name are one member: `Xor(And(A, B), And(A', C))` with `A` and `A'` two `place('A')` objects builds (TypeScript's IO-011 and IO-012 checks compare names) and gives three members, A, B and C, the union the third and fourth lines give. A set of place objects keyed by reference would give four members for those three places (the behaviour RD-03 in spec/runtime-defects.md recorded of TypeScript), which the lines reject under name identity."
          "An n-ary `And` or `Xor` is read as right-nested binary nodes, as `Reference.Out` writes it and IO-016 does. Union is associative, so the nesting does not change the set. An `And` with one child (the runtimes allow it; an `Xor` needs two) is that child, which the n-ary union also gives."
          "The second line strengthens AC2 (`ForwardInput(from, to)` contributes `to`), which does not say that `from` is left out: it reads AC2 as contributing `to` and nothing else. It says \"only `to`\" rather than \"not `from`\" because `from` and `to` may be one place, and then the set holds it. The reading follows the text: the prose collects the places the spec writes to, `from` is an input place (IO-014), and all three runtimes add only `to` (Rust `rust/libpetri-core/src/output.rs` `collect_places`, Java `Arc.java` `allPlaces`, TypeScript `out.ts` `collectPlaces`). The glossary entries Forward (\"In an output branch it claims `to`\") and Output arc (a place the output spec names) say the same, so a forward makes `to`, not `from`, an output arc."
          "The function is defined on every output spec, ones that fail a build-time check included: the `Timeout` and `ForwardInput` lines fix it whether or not the spec has one `Timeout` node and its forwards inside that node's child (IO-013, IO-014), since the build checks and the glossary read it before a spec is known to build."
          "AC1 (`Xor(And(P1, P2), Timeout(5s, P3))` gives {P1, P2, P3}) follows from lines 1, 3, 4 and 5; the timeout's duration does not matter, since `Reference.Out` carries none and the fifth line reads only the child. AC2 is the second line. The non-vacuity theorem checks both on the reference function, and the test derivation (a nested spec gives the complete set) is AC1."
          "The relation to IO-016 is derived, not stated: the set is the union of the output branches of the branch enumeration (`IO_017_union_of_branches`, for every pair of functions that satisfy IO-016 and IO-017). So is the relation to the glossary's output arcs (`IO_017_outputArc`)."
          "The block fixes the function only. That the output specification offers it as a method is an API fact of each runtime and is not encoded. That executors and analyses read output places through it (CORE-035, CORE-062, CORE-072, VER-001) is the subject of those requirements."
  signoff "2026-11-13 3aee03ced6332910 ai"
  statement : ∀ {N : Type} [DecidableEq N], AllPlaces N → Prop :=
    fun A =>
      (∀ p, A (.place p) = {p}) ∧
      (∀ s d, A (.forward s d) = {d}) ∧
      (∀ l r, A (.and l r) = A l ∪ A r) ∧
      (∀ l r, A (.xor l r) = A l ∪ A r) ∧
      (∀ c, A (.timeout c) = A c)

/- The pinned readable form of IO-017: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.IO_017 : {N : Type} → [DecidableEq N] → AllPlaces N → Prop :=
fun {N} [DecidableEq N] A =>
  (∀ (p : N), A (Out.place p) = {p}) ∧
    (∀ (s d : N), A (Out.forward s d) = {d}) ∧
      (∀ (l r : Out N), A (l.and r) = A l ∪ A r) ∧
        (∀ (l r : Out N), A (l.xor r) = A l ∪ A r) ∧ ∀ (c : Out N), A c.timeout = A c
-/
#guard_msgs in #print IO_017

/-- The reference place-set function satisfies IO-017: `outPlaces` is `[p]` on a place, `[to]`
on a forward, append on `And` and `Xor` and the child's on `Timeout`; read as sets, append is
union. -/
@[evidence holds IO_017]
theorem IO_017_reference {N : Type} [DecidableEq N] : IO_017 (refAllPlaces (N := N)) := by
  refine ⟨fun p => ?_, fun s d => ?_, fun l r => ?_, fun l r => ?_, fun c => rfl⟩ <;>
    simp [refAllPlaces, outPlaces, List.toFinset_append]

/-- IO-017 fixes the function exactly: every place-set function that satisfies it is the
reference one on every output spec, `ForwardInput` included. So any bug that adds or drops a
place on some spec violates IO-017. -/
theorem IO_017_unique {N : Type} [DecidableEq N] (A : AllPlaces N) (h : IO_017 A) :
    A = refAllPlaces := by
  have hr := IO_017_reference (N := N)
  funext o
  induction o with
  | place p => rw [h.1, hr.1]
  | forward s d => rw [h.2.1, hr.2.1]
  | and l r ihl ihr => rw [h.2.2.1, hr.2.2.1, ihl, ihr]
  | xor l r ihl ihr => rw [h.2.2.2.1, hr.2.2.2.1, ihl, ihr]
  | timeout c ih => rw [h.2.2.2.2, hr.2.2.2.2, ih]

/-! ### Derived: the union of the output branches, and the output arcs -/

/-- The set is the union of the output branches: for every place-set function that satisfies
IO-017 and every branch enumeration that satisfies [IO-016], a place is in the set exactly when
some enumerated output branch holds it. -/
theorem IO_017_union_of_branches {N : Type} [DecidableEq N] (A : AllPlaces N) (E : BranchEnum N)
    (hA : IO_017 A) (hE : IO_016 E) (o : Out N) (p : N) :
    p ∈ A o ↔ ∃ b ∈ E o, p ∈ b := by
  rw [IO_017_unique A hA, IO_016_unique E hE]
  simp only [refAllPlaces, refBranchSets, List.mem_toFinset, List.mem_map]
  constructor
  · intro hp
    obtain ⟨b, hb, hpb⟩ := branch_of_outPlaces o p hp
    exact ⟨b.toFinset, ⟨b, hb, rfl⟩, by simpa using hpb⟩
  · rintro ⟨_, ⟨b, hb, rfl⟩, hpb⟩
    exact outPlaces_of_branch o b hb p (by simpa using hpb)

/-- Every place-set function that satisfies IO-017 names exactly the glossary's output arcs:
`p` is an output arc of `t` iff `t` has an output spec whose set holds `p`. -/
theorem IO_017_outputArc {N : Type} [DecidableEq N] (A : AllPlaces N) (hA : IO_017 A)
    (t : Trans N) (p : N) : OutputArc t p ↔ ∃ o, t.out = some o ∧ p ∈ A o := by
  rw [IO_017_unique A hA]
  simp [OutputArc, refAllPlaces]

/-! ### Examples: wrong place-set functions, one per line, and one with both forward places -/

/-- A place-set function that is the reference one except that a `Place` node gives the empty
set: a leaf that names nothing. -/
def io017_placeEmpty {N : Type} [DecidableEq N] : AllPlaces N
  | .place _ => ∅
  | .forward _ dst => {dst}
  | .and l r => io017_placeEmpty l ∪ io017_placeEmpty r
  | .xor l r => io017_placeEmpty l ∪ io017_placeEmpty r
  | .timeout c => io017_placeEmpty c

/-- A place-set function that is the reference one except that `ForwardInput(from, to)` gives
`from`, the source place, instead of `to`. -/
def io017_forwardSrc {N : Type} [DecidableEq N] : AllPlaces N
  | .place p => {p}
  | .forward src _ => {src}
  | .and l r => io017_forwardSrc l ∪ io017_forwardSrc r
  | .xor l r => io017_forwardSrc l ∪ io017_forwardSrc r
  | .timeout c => io017_forwardSrc c

/-- A place-set function that is the reference one except that `ForwardInput(from, to)` gives
both of its places: it reads a forward's leaf as naming `from` too. -/
def io017_forwardBoth {N : Type} [DecidableEq N] : AllPlaces N
  | .place p => {p}
  | .forward src dst => {src, dst}
  | .and l r => io017_forwardBoth l ∪ io017_forwardBoth r
  | .xor l r => io017_forwardBoth l ∪ io017_forwardBoth r
  | .timeout c => io017_forwardBoth c

/-- A place-set function that is the reference one except that `And` gives the intersection of
its children's sets: only the places every child names. -/
def io017_andInter {N : Type} [DecidableEq N] : AllPlaces N
  | .place p => {p}
  | .forward _ dst => {dst}
  | .and l r => io017_andInter l ∩ io017_andInter r
  | .xor l r => io017_andInter l ∪ io017_andInter r
  | .timeout c => io017_andInter c

/-- A place-set function that is the reference one except that `Xor` gives only its first
child's set: it reads an `Xor` as the one alternative listed first. -/
def io017_xorFirst {N : Type} [DecidableEq N] : AllPlaces N
  | .place p => {p}
  | .forward _ dst => {dst}
  | .and l r => io017_xorFirst l ∪ io017_xorFirst r
  | .xor l _ => io017_xorFirst l
  | .timeout c => io017_xorFirst c

/-- A place-set function that is the reference one except that a `Timeout` node gives the empty
set: it skips the timeout child's places. -/
def io017_timeoutNone {N : Type} [DecidableEq N] : AllPlaces N
  | .place p => {p}
  | .forward _ dst => {dst}
  | .and l r => io017_timeoutNone l ∪ io017_timeoutNone r
  | .xor l r => io017_timeoutNone l ∪ io017_timeoutNone r
  | .timeout _ => ∅

/-- ✗ Reading a forward as naming both of its places violates IO-017 (second line):
`ForwardInput(0, 1)` gives {0, 1} instead of {1}. -/
@[evidence forbids IO_017]
theorem IO_017_forbids_forwardBoth : ¬ IO_017 (io017_forwardBoth (N := Nat)) := by
  intro h
  exact absurd (h.2.1 0 1) (by decide)

/-- A place-set function on numbered places that is the reference one except that a `Place` leaf
also names place 0: it reads "the set holding that place" as a set that contains it. -/
def io017_placeExtra : AllPlaces Nat
  | .place p => {p, 0}
  | .forward _ dst => {dst}
  | .and l r => io017_placeExtra l ∪ io017_placeExtra r
  | .xor l r => io017_placeExtra l ∪ io017_placeExtra r
  | .timeout c => io017_placeExtra c

/-- ✗ A `Place` leaf that also names another place violates IO-017 (first line): `Place(1)` gives
{1, 0} instead of {1}. The set holds only that place. -/
@[evidence forbids IO_017]
theorem IO_017_forbids_placeExtra : ¬ IO_017 io017_placeExtra := by
  intro h
  exact absurd (h.1 1) (by decide)

/-- A place-set function that is the reference one except that `ForwardInput(from, to)` gives
`to` with `from` taken out: it reads the second line as "`to` and not `from`". -/
def io017_forwardNotSrc {N : Type} [DecidableEq N] : AllPlaces N
  | .place p => {p}
  | .forward src dst => {dst} \ {src}
  | .and l r => io017_forwardNotSrc l ∪ io017_forwardNotSrc r
  | .xor l r => io017_forwardNotSrc l ∪ io017_forwardNotSrc r
  | .timeout c => io017_forwardNotSrc c

/-- ✗ Taking `from` out of a forward's set violates IO-017 (second line) when `from` is `to`:
`ForwardInput(0, 0)` gives the empty set instead of {0}. This is why the line says "only `to`"
and not "`to` and not `from`". -/
@[evidence forbids IO_017]
theorem IO_017_forbids_forwardNotSrc : ¬ IO_017 (io017_forwardNotSrc (N := Nat)) := by
  intro h
  exact absurd (h.2.1 0 0) (by decide)

/-- ✗ Reading an `Xor` as its first alternative violates IO-017 (fourth line): `Xor(0, 1)` gives
{0} instead of {0, 1}. -/
@[evidence forbids IO_017]
theorem IO_017_forbids_xorFirst : ¬ IO_017 (io017_xorFirst (N := Nat)) := by
  intro h
  exact absurd (h.2.2.2.1 (.place 0) (.place 1)) (by decide)

/-- Mutant reading of IO-017 that drops the first line: a `Place` leaf may give anything. -/
def IO_017_mutant_dropPlace {N : Type} [DecidableEq N] (A : AllPlaces N) : Prop :=
  (∀ s d, A (.forward s d) = {d}) ∧
  (∀ l r, A (.and l r) = A l ∪ A r) ∧
  (∀ l r, A (.xor l r) = A l ∪ A r) ∧
  (∀ c, A (.timeout c) = A c)

/-- The empty-leaf function kills the first mutant: every other node follows the text, but
`Place(0)` gives the empty set, not {0}. -/
@[evidence mutant IO_017]
theorem IO_017_mutant_dropPlace_killed :
    IO_017_mutant_dropPlace (io017_placeEmpty (N := Nat)) ∧
      ¬ IO_017 (io017_placeEmpty (N := Nat)) :=
  ⟨⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩,
    fun h => absurd (h.1 0) (by decide)⟩

/-- Mutant reading of IO-017 that drops the second line: a `ForwardInput` leaf may give
anything. -/
def IO_017_mutant_dropForward {N : Type} [DecidableEq N] (A : AllPlaces N) : Prop :=
  (∀ p, A (.place p) = {p}) ∧
  (∀ l r, A (.and l r) = A l ∪ A r) ∧
  (∀ l r, A (.xor l r) = A l ∪ A r) ∧
  (∀ c, A (.timeout c) = A c)

/-- The source-place function kills the second mutant: every other node follows the text, but
`ForwardInput(0, 1)` gives {0}, not {1}. -/
@[evidence mutant IO_017]
theorem IO_017_mutant_dropForward_killed :
    IO_017_mutant_dropForward (io017_forwardSrc (N := Nat)) ∧
      ¬ IO_017 (io017_forwardSrc (N := Nat)) :=
  ⟨⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩,
    fun h => absurd (h.2.1 0 1) (by decide)⟩

/-- Mutant reading of IO-017 that drops the third line: `And` may give anything. -/
def IO_017_mutant_dropAnd {N : Type} [DecidableEq N] (A : AllPlaces N) : Prop :=
  (∀ p, A (.place p) = {p}) ∧
  (∀ s d, A (.forward s d) = {d}) ∧
  (∀ l r, A (.xor l r) = A l ∪ A r) ∧
  (∀ c, A (.timeout c) = A c)

/-- The intersection function kills the third mutant: every other node follows the text, but
`And(0, 1)` gives the empty set, not {0, 1}. -/
@[evidence mutant IO_017]
theorem IO_017_mutant_dropAnd_killed :
    IO_017_mutant_dropAnd (io017_andInter (N := Nat)) ∧ ¬ IO_017 (io017_andInter (N := Nat)) :=
  ⟨⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩,
    fun h => absurd (h.2.2.1 (.place 0) (.place 1)) (by decide)⟩

/-- Mutant reading of IO-017 that drops the fourth line: `Xor` may give anything. -/
def IO_017_mutant_dropXor {N : Type} [DecidableEq N] (A : AllPlaces N) : Prop :=
  (∀ p, A (.place p) = {p}) ∧
  (∀ s d, A (.forward s d) = {d}) ∧
  (∀ l r, A (.and l r) = A l ∪ A r) ∧
  (∀ c, A (.timeout c) = A c)

/-- The first-alternative function kills the fourth mutant: every other node follows the text,
but `Xor(0, 1)` gives {0}, not {0, 1}. -/
@[evidence mutant IO_017]
theorem IO_017_mutant_dropXor_killed :
    IO_017_mutant_dropXor (io017_xorFirst (N := Nat)) ∧ ¬ IO_017 (io017_xorFirst (N := Nat)) :=
  ⟨⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩, IO_017_forbids_xorFirst⟩

/-- Mutant reading of IO-017 that drops the fifth line: `Timeout` may give anything. -/
def IO_017_mutant_dropTimeout {N : Type} [DecidableEq N] (A : AllPlaces N) : Prop :=
  (∀ p, A (.place p) = {p}) ∧
  (∀ s d, A (.forward s d) = {d}) ∧
  (∀ l r, A (.and l r) = A l ∪ A r) ∧
  (∀ l r, A (.xor l r) = A l ∪ A r)

/-- The empty-`Timeout` function kills the fifth mutant: every other node follows the text, but
`Timeout(Place(0))` gives the empty set, not its child's {0}. -/
@[evidence mutant IO_017]
theorem IO_017_mutant_dropTimeout_killed :
    IO_017_mutant_dropTimeout (io017_timeoutNone (N := Nat)) ∧
      ¬ IO_017 (io017_timeoutNone (N := Nat)) :=
  ⟨⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩,
    fun h => absurd (h.2.2.2.2 (.place 0)) (by decide)⟩

/-- Mutant reading of IO-017 that weakens every line to "contains": the function must name every
place the text names, but may name more. -/
def IO_017_mutant_superset {N : Type} [DecidableEq N] (A : AllPlaces N) : Prop :=
  (∀ p, {p} ⊆ A (.place p)) ∧
  (∀ s d, {d} ⊆ A (.forward s d)) ∧
  (∀ l r, A l ∪ A r ⊆ A (.and l r)) ∧
  (∀ l r, A l ∪ A r ⊆ A (.xor l r)) ∧
  (∀ c, A c ⊆ A (.timeout c))

/-- The both-places function kills the superset mutant: it names every place the text names,
and also `from` of a forward, which the second line excludes. -/
@[evidence mutant IO_017]
theorem IO_017_mutant_superset_killed :
    IO_017_mutant_superset (io017_forwardBoth (N := Nat)) ∧
      ¬ IO_017 (io017_forwardBoth (N := Nat)) :=
  ⟨⟨fun _ => subset_refl _, fun _ _ => by simp [io017_forwardBoth],
      fun _ _ => subset_refl _, fun _ _ => subset_refl _, fun _ => subset_refl _⟩,
    IO_017_forbids_forwardBoth⟩

/-! ### Non-vacuity: the acceptance criteria on the reference -/

/-- The transition of the example: no inputs, output spec
`Xor(And(Place(1), Place(2)), Timeout(Place(3)))`. -/
def io017_t : Trans Nat :=
  { core := { name := "t", inputs := [], inhibitors := [], reads := [], resets := [] },
    out := some (.xor (.and (.place 1) (.place 2)) (.timeout (.place 3))) }

/-- Every line of IO-017 is exercised by the reference function on the acceptance criteria:
AC1 `Xor(And(P1, P2), Timeout(P3))` gives {P1, P2, P3}; AC2 `ForwardInput(4, 5)` gives {5}, also
inside a `Timeout` child next to a place. And the AC1 spec on a transition makes 1, 2 and 3 its
output arcs and nothing else (4 is not). -/
@[evidence nonvacuous IO_017]
theorem IO_017_nonvacuous :
    refAllPlaces (.xor (.and (.place 1) (.place 2)) (.timeout (.place 3))) =
        ({1, 2, 3} : Finset Nat) ∧
      refAllPlaces (.forward 4 5) = ({5} : Finset Nat) ∧
      refAllPlaces (.xor (.place 1) (.timeout (.and (.place 2) (.forward 4 5)))) =
        ({1, 2, 5} : Finset Nat) ∧
      (∀ p, OutputArc io017_t p ↔ p ∈ ({1, 2, 3} : Finset Nat)) := by
  refine ⟨by decide, by decide, by decide, fun p => ?_⟩
  rw [IO_017_outputArc refAllPlaces IO_017_reference]
  simp only [io017_t, Option.some.injEq, exists_eq_left']
  rw [show refAllPlaces (.xor (.and (.place 1) (.place 2)) (.timeout (.place 3))) =
      ({1, 2, 3} : Finset Nat) by decide]

end Libpetri.Spec
