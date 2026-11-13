import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.Glossary
import Libpetri.Spec.Text.IO_016

set_option linter.missingDocs true

/-!
# IO-016: Branch enumeration (`spec/02-input-output-specs.md`)

IO-016 is a pure-function requirement (kind F): it fixes the *branch enumeration*, the function
that lists the output branches of an output spec for structural analysis. The statement is a
predicate over a *branch enumeration* `E : Out N → List (Finset N)`: an output spec goes in, a
list of output branches comes out, each branch a set of places ("A branch is a **set** of
places"). The witness is the reference enumeration, `Out.branches` (the branches the reference
firing's action outcome deposits) with each branch read as a set.

The enumeration lists one output branch per assignment ([IO-015]), so `Xor(P, P)` lists `{P}`
twice. On a spec that builds the output branches are pairwise distinct sets ([IO-012]): the
build-time check of [IO-012] is the statement that the reference enumeration, read as sets, has
no repeated entry. The glossary's `WellFormedOut` states the build-time checks of an output spec, and
`IO_016_nodup_of_wf` derives the distinctness for every enumeration that satisfies IO-016.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## The model: a branch enumeration -/

/-- A branch enumeration: the output branches of each output spec, as a list (one entry per
alternative, so a branch may occur twice) of sets of places. It reads the output spec alone,
which is what "static" means. -/
abbrev BranchEnum (N : Type) := Out N → List (Finset N)

/-- The Cartesian product of two branch lists ([IO-016], `And`): one branch for each choice of
one branch of each list, holding the union of the two. Local term of this block. -/
def branchCross {N : Type} [DecidableEq N] (xs ys : List (Finset N)) : List (Finset N) :=
  xs.flatMap fun x => ys.map fun y => x ∪ y

/-- The reference branch enumeration: `Out.branches`, the branches the reference firing
semantics lets an action deposit (`Reference.deposit`, `.action i`), each read as the set of
places it claims. -/
def refBranchSets {N : Type} [DecidableEq N] : BranchEnum N :=
  fun o => o.branches.map List.toFinset

/- The reference enumeration is the witness model of IO-016's `holds` theorem. -/
#spec_witness refBranchSets

/-! ## IO-016: Branch Enumeration -/

requirement IO_016
  id "IO-016"
  title "Branch Enumeration"
  kind F
  scope "all output specs"
  source verbatim "spec/02-input-output-specs.md"
  covers IO_016.s1, IO_016.s2, IO_016.s3, IO_016.s4, IO_016.s5
  reading "Place(p) enumerates exactly the one branch {p};"
          "ForwardInput(from, to) enumerates exactly the one branch {to};"
          "And(l, r) enumerates, for each branch x of l in order and, within it, each branch y of r in order, the branch x ∪ y, and nothing else;"
          "Xor(l, r) enumerates the branches of l, in order, then the branches of r, in order, each as often as it occurs there, and nothing else;"
          "Timeout(c) enumerates exactly the branches of c, in order."
  assumes "A branch enumeration is a function from an output spec alone to a list of output branches, so it is static by its type. A branch is a set of places (`Finset`), as the text says (\"a set of places: it says which places receive a token when the branch is taken, not how many\"). The list keeps multiplicity (`Xor(P, P)` has two branches) and its order: the lines compare lists with equality, so the enumeration is fixed exactly (`IO_016_unique`). The order is normative because the analyses expand a transition into its branches \"in the order above\" and name the virtual transitions `<t>_b<i>` in enumeration order ([VER-001]), which the byte-identical SMT scripts carry ([VER-013])."
          "An n-ary `And` or `Xor` is read as right-nested binary nodes, as `Reference.Out` writes it. List append and the lexicographic Cartesian product are associative and union is associative, so the nesting changes neither the branches nor their order: the n-ary product with the first child slowest is the right-nested product of binary ones."
          "A branch read as a set loses a repeated claim: `And(P, P)` enumerates {P}, while the reference `Out.branches` lists [P, P]. IO-011 rejects such a spec when it is built, so on every buildable spec the two agree (`IO_016_card_of_wf`: each set has as many places as the list it reads)."
          "The list has one entry per assignment (IO-015), counted by position, so on a spec that builds no two entries are the same set: IO-012 rejects at build time any spec with two distinct assignments claiming one set, and its check enumerates per IO-016 and compares the entries as sets in index order (the numbering of VER-001's `<t>_b<i>`). The paragraph saying so is a consequence of IO-012's build check, not a further constraint on the enumeration; it is derived, not stated (`IO_016_nodup_of_wf`). The enumeration itself is defined on every spec, ambiguous ones included, because the build check is computed from it."
          "A spec that builds holds at most one `Timeout` node, and a `ForwardInput` only inside that node's child (IO-013, IO-014). The `Timeout` and `ForwardInput` lines still fix the enumeration on every spec: the enumeration is a total function on output specs, and the build checks read it before a spec is known to build."
          "AC1 (`And(P1, P2)` → {P1, P2}) follows from lines 1 and 3; AC2 (`Xor(P1, P2)` → {P1}, {P2}) from lines 1 and 4; AC3 (`Xor(And(P1, P2), P3)` → {P1, P2}, {P3}) from lines 1, 3 and 4. The non-vacuity theorem checks all three on the reference enumeration."
          "AC4 (the executor's WARN log-message event when a validated firing deposits more than one token in a place its matched branch names, at most once per transition per execution) is an [EVT-013] event of a running executor, and is skipped with the rest of validation by the CONC-026 option. Neither the branch enumeration nor the firing relation has an event store or an execution, and the reference executor does not emit this warning (Reference/Events.lean), so no block states AC4: it is Q-tested, with the test derivation's three cases (two tokens to the one place the spec names, fired three times: every token lands and one warning is emitted; `And(A, B)` with three tokens to A and two to B: one warning naming `(A: 3, B: 2)`; one token per named place: no event) in every runtime, the Rust, Java and TypeScript suites on both backends: Rust `backend_suite_tests` (the libpetri-runtime backend suite) `multiplicity_warns_once_per_transition`, `multiplicity_names_every_repeated_place` and `multiplicity_silent_for_one_token_per_place`; Java `java/src/test/java/org/libpetri/runtime/BackendDivergenceRegressionTest.java` `multiplicity_warnsOncePerTransitionWhenAnActionWritesTwoTokensToAPlaceNamedOnce`, `multiplicity_warnsThroughACompositeSpecNamingEveryRepeatedPlace` and `multiplicity_staysSilentWhenEveryNamedPlaceReceivesExactlyOneToken`; TypeScript `typescript/tests/runtime/executor-shared-semantics.test.ts` (describe 'branch multiplicity diagnostic', three cases); Python `python/tests/test_output_validation.py` `test_multiplicity_warns_once_per_transition`, `test_multiplicity_names_every_repeated_place` and `test_multiplicity_is_silent_for_one_token_per_named_place`. AC4's logger `libpetri.runtime` is omitted where the log-message event carries no logger field, as for the diagnostics of CORE-037 and CORE-072 AC4: EVT-013 gives the event a logger name in Java and TypeScript only, and Rust's `NetEvent::LogMessage` has no logger field (`rust/libpetri-event/src/net_event.rs`), so Rust and Python carry the level, the transition name and the message, and Java (`BitmapNetExecutor.java` and `PrecompiledNetExecutor.java` `warnMultiplicity`) and TypeScript (`bitmap-net-executor.ts` `warnMultiplicity`) carry the logger as well."
          "The statement is generic in the place type `N` and its equality, so a branch is a set under the implementation's own place identity (CORE-002: the name, or the name and the token type; glossary: Same set of places). Rust's branches are sets of `PlaceRef`, compared by name (`rust/libpetri-core/src/output.rs` `enumerate_branches`), and Java's are sets of `Place` records, compared by name and token type (MOD-024; `Arc.java` `enumerateBranches`), so both meet the lines under their identity. TypeScript's identity is the name (CORE-002 line 2, ruling D82 (a)), and `enumerateBranches` (`typescript/src/core/out.ts`, its `crossProduct`) keeps one place object per name in a branch, the first met, so `And(place('A'), place('A'))` with two separate objects gives one branch holding one place, as the third line says. A branch built as a JS `Set` of place objects keyed by reference would hold two members there (the behaviour RD-03 in spec/runtime-defects.md recorded of TypeScript), which the third line rejects under name identity. On a spec that builds the two agree anyway: TypeScript's IO-011 check (`duplicateInBranch`) and IO-012 check (`ambiguousBranches`) compare place names, so no branch of a buildable spec holds two objects of one name, and the analyses key a branch's deposits by name (`typescript/src/verification/analysis/branch-outcomes.ts` `outcomes`)."
          "A branch fixes which places receive tokens, not how many: with output validation enabled, a firing that ends with its action deposits one or more tokens in each place of one output branch and none in any other (glossary: Output branch, IO-015, CORE-036). The paragraph on what the analyses deposit (one token per place of a branch: VER-010, VER-001, NU-051) describes those analyses, not the enumeration, and is their subject. The reference firing semantics deposits one token per claim of a branch, the case the analyses model; the non-vacuity theorem shows one such firing."
          "The paragraph on the timeout outcome says that it is not an output branch (glossary: Timeout outcome), which the `Timeout` line respects by enumerating the child's branches only; the `ForwardInput` line is the branch an action writes, `to` claimed once (glossary: Forward, IO-015), not the timeout outcome's per-consumed-token deposit (IO-014). How the analyses append the timeout outcome after the branches, when it differs place by place from every branch (deposits compared per place, CORE-036), is VER-001's subject."
          "The block fixes the enumeration function only. That executors and analyses use it (the executor's validation, the SCG virtual transitions, the flattener) is the subject of IO-015, VER-001 and VER-010."
  signoff "2026-11-13 9f5864d92dfe9b93 ai"
  statement : ∀ {N : Type} [DecidableEq N], BranchEnum N → Prop :=
    fun E =>
      (∀ p, E (.place p) = [{p}]) ∧
      (∀ s d, E (.forward s d) = [{d}]) ∧
      (∀ l r, E (.and l r) = branchCross (E l) (E r)) ∧
      (∀ l r, E (.xor l r) = E l ++ E r) ∧
      (∀ c, E (.timeout c) = E c)

/- The pinned readable form of IO-016: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.IO_016 : {N : Type} → [DecidableEq N] → BranchEnum N → Prop :=
fun {N} [DecidableEq N] E =>
  (∀ (p : N), E (Out.place p) = [{p}]) ∧
    (∀ (s d : N), E (Out.forward s d) = [{d}]) ∧
      (∀ (l r : Out N), E (l.and r) = branchCross (E l) (E r)) ∧
        (∀ (l r : Out N), E (l.xor r) = E l ++ E r) ∧ ∀ (c : Out N), E c.timeout = E c
-/
#guard_msgs in #print IO_016

/-- Reading each branch as a set commutes with the Cartesian product: the set of `x ++ y` is the
union of the sets of `x` and `y`. -/
theorem map_toFinset_cross {N : Type} [DecidableEq N] (xs ys : List (List N)) :
    (cross xs ys).map List.toFinset =
      branchCross (xs.map List.toFinset) (ys.map List.toFinset) := by
  simp [cross, branchCross, List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def,
    List.toFinset_append]

/-- The reference enumeration satisfies IO-016: `Out.branches` is `[[p]]` on a place, `[[to]]`
on a forward, `cross` (concatenation of one branch per child, left child slowest) on `And`,
append on `Xor` and the child's on `Timeout`; read as sets, concatenation is union
(`map_toFinset_cross`). Each line holds with equality, in the reference order. -/
@[evidence holds IO_016]
theorem IO_016_reference {N : Type} [DecidableEq N] : IO_016 (refBranchSets (N := N)) := by
  refine ⟨fun p => ?_, fun s d => ?_, fun l r => ?_, fun l r => ?_, fun c => rfl⟩
  · simp [refBranchSets, Out.branches]
  · simp [refBranchSets, Out.branches]
  · simp only [refBranchSets, Out.branches]; exact map_toFinset_cross _ _
  · simp [refBranchSets, Out.branches]

/-- IO-016 fixes the enumeration exactly: every enumeration that satisfies it is the reference
one, on every output spec (`ForwardInput` included) and in the same order. So any enumeration
bug that changes a branch, the number of branches or their order violates IO-016. -/
theorem IO_016_unique {N : Type} [DecidableEq N] (E : BranchEnum N) (h : IO_016 E) :
    E = refBranchSets := by
  have hr := IO_016_reference (N := N)
  funext o
  induction o with
  | place p => rw [h.1, hr.1]
  | forward s d => rw [h.2.1, hr.2.1]
  | and l r ihl ihr => rw [h.2.2.1, hr.2.2.1, ihl, ihr]
  | xor l r ihl ihr => rw [h.2.2.2.1, hr.2.2.2.1, ihl, ihr]
  | timeout c ih => rw [h.2.2.2.2, hr.2.2.2.2, ih]

/-! ### Examples: wrong enumerations, one per line, and one in the wrong order -/

/-- An enumeration that is the reference one except that a `Place` node enumerates the one
empty branch: a leaf that claims nothing. -/
def io016_placeEmpty {N : Type} [DecidableEq N] : BranchEnum N
  | .place _ => [∅]
  | .forward _ dst => [{dst}]
  | .and l r => branchCross (io016_placeEmpty l) (io016_placeEmpty r)
  | .xor l r => io016_placeEmpty l ++ io016_placeEmpty r
  | .timeout c => io016_placeEmpty c

/-- An enumeration that is the reference one except that `ForwardInput(from, to)` enumerates
`from`, the source place, instead of `to`. -/
def io016_forwardSrc {N : Type} [DecidableEq N] : BranchEnum N
  | .place p => [{p}]
  | .forward src _ => [{src}]
  | .and l r => branchCross (io016_forwardSrc l) (io016_forwardSrc r)
  | .xor l r => io016_forwardSrc l ++ io016_forwardSrc r
  | .timeout c => io016_forwardSrc c

/-- An enumeration that is the reference one except that `ForwardInput` enumerates no branch:
it drops the forward from the analysis, and with it every `And` branch that contains it. -/
def io016_forwardNone {N : Type} [DecidableEq N] : BranchEnum N
  | .place p => [{p}]
  | .forward _ _ => []
  | .and l r => branchCross (io016_forwardNone l) (io016_forwardNone r)
  | .xor l r => io016_forwardNone l ++ io016_forwardNone r
  | .timeout c => io016_forwardNone c

/-- An enumeration that is the reference one except that `And` is read like `Xor`: the union of
the children's branches instead of their Cartesian product. -/
def io016_andAsXor {N : Type} [DecidableEq N] : BranchEnum N
  | .place p => [{p}]
  | .forward _ dst => [{dst}]
  | .and l r => io016_andAsXor l ++ io016_andAsXor r
  | .xor l r => io016_andAsXor l ++ io016_andAsXor r
  | .timeout c => io016_andAsXor c

/-- An enumeration that is the reference one except that `Xor` is read like `And`: the
Cartesian product of the children's branches instead of their union. -/
def io016_xorAsAnd {N : Type} [DecidableEq N] : BranchEnum N
  | .place p => [{p}]
  | .forward _ dst => [{dst}]
  | .and l r => branchCross (io016_xorAsAnd l) (io016_xorAsAnd r)
  | .xor l r => branchCross (io016_xorAsAnd l) (io016_xorAsAnd r)
  | .timeout c => io016_xorAsAnd c

/-- An enumeration that is the reference one except that a `Timeout` node enumerates no branch:
it treats the timeout as the only way a `Timeout` subtree ends. -/
def io016_timeoutNone {N : Type} [DecidableEq N] : BranchEnum N
  | .place p => [{p}]
  | .forward _ dst => [{dst}]
  | .and l r => branchCross (io016_timeoutNone l) (io016_timeoutNone r)
  | .xor l r => io016_timeoutNone l ++ io016_timeoutNone r
  | .timeout _ => []

/-- An enumeration that is the reference one except that `Xor` lists the second child's
branches first: the same branches, in the wrong order. -/
def io016_xorReversed {N : Type} [DecidableEq N] : BranchEnum N
  | .place p => [{p}]
  | .forward _ dst => [{dst}]
  | .and l r => branchCross (io016_xorReversed l) (io016_xorReversed r)
  | .xor l r => io016_xorReversed r ++ io016_xorReversed l
  | .timeout c => io016_xorReversed c

/-- ✗ Reading `And` like `Xor` violates IO-016 (third line): `And(0, 1)` enumerates the two
branches {0}, {1} instead of the one branch {0, 1}. -/
@[evidence forbids IO_016]
theorem IO_016_forbids_andAsXor : ¬ IO_016 (io016_andAsXor (N := Nat)) := by
  intro h
  exact absurd (h.2.2.1 (.place 0) (.place 1)) (by decide)

/-- ✗ Dropping a forward from the enumeration violates IO-016 (second line):
`ForwardInput(0, 1)` enumerates no branch instead of {1}. -/
@[evidence forbids IO_016]
theorem IO_016_forbids_forwardNone : ¬ IO_016 (io016_forwardNone (N := Nat)) := by
  intro h
  exact absurd (h.2.1 0 1) (by decide)

/-- Mutant reading of IO-016 that drops the first line: a `Place` leaf may enumerate anything. -/
def IO_016_mutant_dropPlace {N : Type} [DecidableEq N] (E : BranchEnum N) : Prop :=
  (∀ s d, E (.forward s d) = [{d}]) ∧
  (∀ l r, E (.and l r) = branchCross (E l) (E r)) ∧
  (∀ l r, E (.xor l r) = E l ++ E r) ∧
  (∀ c, E (.timeout c) = E c)

/-- The empty-leaf enumeration kills the first mutant: every other node follows the text, but
`Place(0)` enumerates {∅}, not {{0}}. -/
@[evidence mutant IO_016]
theorem IO_016_mutant_dropPlace_killed :
    IO_016_mutant_dropPlace (io016_placeEmpty (N := Nat)) ∧ ¬ IO_016 (io016_placeEmpty (N := Nat)) :=
  ⟨⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩,
    fun h => absurd (h.1 0) (by decide)⟩

/-- Mutant reading of IO-016 that drops the second line: a `ForwardInput` leaf may enumerate
anything. -/
def IO_016_mutant_dropForward {N : Type} [DecidableEq N] (E : BranchEnum N) : Prop :=
  (∀ p, E (.place p) = [{p}]) ∧
  (∀ l r, E (.and l r) = branchCross (E l) (E r)) ∧
  (∀ l r, E (.xor l r) = E l ++ E r) ∧
  (∀ c, E (.timeout c) = E c)

/-- The source-place enumeration kills the second mutant: every other node follows the text,
but `ForwardInput(0, 1)` enumerates {0}, not {1}. -/
@[evidence mutant IO_016]
theorem IO_016_mutant_dropForward_killed :
    IO_016_mutant_dropForward (io016_forwardSrc (N := Nat)) ∧
      ¬ IO_016 (io016_forwardSrc (N := Nat)) :=
  ⟨⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩,
    fun h => absurd (h.2.1 0 1) (by decide)⟩

/-- Mutant reading of IO-016 that drops the third line: `And` may enumerate anything. -/
def IO_016_mutant_dropAnd {N : Type} [DecidableEq N] (E : BranchEnum N) : Prop :=
  (∀ p, E (.place p) = [{p}]) ∧
  (∀ s d, E (.forward s d) = [{d}]) ∧
  (∀ l r, E (.xor l r) = E l ++ E r) ∧
  (∀ c, E (.timeout c) = E c)

/-- The `And`-as-`Xor` enumeration kills the third mutant: every other node follows the text,
but `And(0, 1)` enumerates two branches, not one. -/
@[evidence mutant IO_016]
theorem IO_016_mutant_dropAnd_killed :
    IO_016_mutant_dropAnd (io016_andAsXor (N := Nat)) ∧ ¬ IO_016 (io016_andAsXor (N := Nat)) :=
  ⟨⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩, IO_016_forbids_andAsXor⟩

/-- Mutant reading of IO-016 that drops the fourth line: `Xor` may enumerate anything. -/
def IO_016_mutant_dropXor {N : Type} [DecidableEq N] (E : BranchEnum N) : Prop :=
  (∀ p, E (.place p) = [{p}]) ∧
  (∀ s d, E (.forward s d) = [{d}]) ∧
  (∀ l r, E (.and l r) = branchCross (E l) (E r)) ∧
  (∀ c, E (.timeout c) = E c)

/-- The `Xor`-as-`And` enumeration kills the fourth mutant: every other node follows the text,
but `Xor(0, 1)` enumerates the one branch {0, 1}, not the two branches {0}, {1}. -/
@[evidence mutant IO_016]
theorem IO_016_mutant_dropXor_killed :
    IO_016_mutant_dropXor (io016_xorAsAnd (N := Nat)) ∧ ¬ IO_016 (io016_xorAsAnd (N := Nat)) :=
  ⟨⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩,
    fun h => absurd (h.2.2.2.1 (.place 0) (.place 1)) (by decide)⟩

/-- Mutant reading of IO-016 that drops the fifth line: `Timeout` may enumerate anything. -/
def IO_016_mutant_dropTimeout {N : Type} [DecidableEq N] (E : BranchEnum N) : Prop :=
  (∀ p, E (.place p) = [{p}]) ∧
  (∀ s d, E (.forward s d) = [{d}]) ∧
  (∀ l r, E (.and l r) = branchCross (E l) (E r)) ∧
  (∀ l r, E (.xor l r) = E l ++ E r)

/-- The no-branch-`Timeout` enumeration kills the fifth mutant: every other node follows the
text, but `Timeout(Place(0))` enumerates no branch, not its child's {0}. -/
@[evidence mutant IO_016]
theorem IO_016_mutant_dropTimeout_killed :
    IO_016_mutant_dropTimeout (io016_timeoutNone (N := Nat)) ∧
      ¬ IO_016 (io016_timeoutNone (N := Nat)) :=
  ⟨⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩,
    fun h => absurd (h.2.2.2.2 (.place 0)) (by decide)⟩

/-- Mutant reading of IO-016 that drops the order: every line compares only up to permutation
(`List.Perm`), so the right branches in any order conform. -/
def IO_016_mutant_unordered {N : Type} [DecidableEq N] (E : BranchEnum N) : Prop :=
  (∀ p, (E (.place p)).Perm [{p}]) ∧
  (∀ s d, (E (.forward s d)).Perm [{d}]) ∧
  (∀ l r, (E (.and l r)).Perm (branchCross (E l) (E r))) ∧
  (∀ l r, (E (.xor l r)).Perm (E l ++ E r)) ∧
  (∀ c, (E (.timeout c)).Perm (E c))

/-- The reversed-`Xor` enumeration kills the order mutant: its branches are the right ones up to
order, but `Xor(0, 1)` lists {1} before {0}, so the virtual transitions `<t>_b<i>` of
[VER-001] would be numbered the other way round. -/
@[evidence mutant IO_016]
theorem IO_016_mutant_unordered_killed :
    IO_016_mutant_unordered (io016_xorReversed (N := Nat)) ∧
      ¬ IO_016 (io016_xorReversed (N := Nat)) :=
  ⟨⟨fun _ => List.Perm.refl _, fun _ _ => List.Perm.refl _, fun _ _ => List.Perm.refl _,
      fun _ _ => List.perm_append_comm, fun _ => List.Perm.refl _⟩,
    fun h => absurd (h.2.2.2.1 (.place 0) (.place 1)) (by decide)⟩

/-! ### Non-vacuity: the acceptance criteria on the reference, and a reference firing -/

/-- The transition of the example: no inputs, output spec `And(Place(0), Place(1))`. -/
def io016_t : Trans Nat :=
  { core := { name := "t", inputs := [], inhibitors := [], reads := [], resets := [] },
    out := some (.and (.place 0) (.place 1)) }

/-- The empty marking of the example. -/
def io016_m : Nat → Nat := fun _ => 0

/-- The marking after the example's firing: one token in places 0 and 1. -/
def io016_m' : Nat → Nat := fun n => if n = 0 ∨ n = 1 then 1 else 0

/-- Every line of IO-016 is exercised by the reference enumeration on the acceptance criteria:
AC1 `And(P1, P2)` → {P1, P2}; AC2 `Xor(P1, P2)` → {P1}, {P2}; AC3 `Xor(And(P1, P2), P3)` →
{P1, P2}, {P3}; `Timeout(Xor(P1, P2))` → {P1}, {P2}; `Xor(P1, Timeout(ForwardInput(P1, P2)))`
→ {P1}, {P2}, the forward inside a `Timeout` child as [IO-014] requires. And a reference firing
of a transition with output spec `And(0, 1)` deposits its one branch, one token in each of 0
and 1. -/
@[evidence nonvacuous IO_016]
theorem IO_016_nonvacuous :
    refBranchSets (.and (.place 1) (.place 2)) = [({1, 2} : Finset Nat)] ∧
      refBranchSets (.xor (.place 1) (.place 2)) = [({1} : Finset Nat), {2}] ∧
      refBranchSets (.xor (.and (.place 1) (.place 2)) (.place 3)) =
        [({1, 2} : Finset Nat), {3}] ∧
      refBranchSets (.timeout (.xor (.place 1) (.place 2))) = [({1} : Finset Nat), {2}] ∧
      refBranchSets (.xor (.place 1) (.timeout (.forward 1 2))) = [({1} : Finset Nat), {2}] ∧
      RefFire io016_t io016_m [0, 1] io016_m' := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ⟨.action 0, rfl⟩, ?_⟩
  funext n
  by_cases h0 : n = 0
  · subst h0; rfl
  · by_cases h1 : n = 1
    · subst h1; rfl
    · simp [io016_m', h0, h1, Ne.symm h0, Ne.symm h1, fireNC, depProd, nconsumed, nspecAt,
        io016_t, io016_m]

/-! ### Specs that build: distinct output branches ([IO-011]–[IO-014] build checks) -/

/-- On a spec that builds, every enumeration that satisfies IO-016 lists pairwise distinct
sets: no two entries name the same places ([IO-012]). -/
theorem IO_016_nodup_of_wf {N : Type} [DecidableEq N] (E : BranchEnum N) (h : IO_016 E)
    {ins : List N} (o : Out N) (hwf : WellFormedOut ins o) : (E o).Nodup := by
  rw [IO_016_unique E h]
  refine List.pairwise_map.2 (hwf.2.2.2.2.2.imp fun {a b} hab heq => hab fun q => ?_)
  simpa using congrArg (q ∈ ·) heq

/-- On a spec that builds, reading a branch as a set loses no claim: each enumerated set has as
many places as the reference branch it reads ([IO-011]). -/
theorem IO_016_card_of_wf {N : Type} [DecidableEq N] (E : BranchEnum N) (h : IO_016 E)
    {ins : List N} (o : Out N) (hwf : WellFormedOut ins o) : (E o).map Finset.card = o.branches.map List.length := by
  rw [IO_016_unique E h]
  simp only [refBranchSets, List.map_map]
  apply List.map_congr_left
  intro b hb
  exact List.toFinset_card_of_nodup (by by_contra hn; exact hwf.1 ⟨b, hb, hn⟩)

/-- The rejected and accepted specs of [IO-012] AC5, [IO-013] AC7 and [IO-014] AC7 under
`WellFormedOut` with input place `a` (places as numbers: A = 0, B = 1, C = 2, a = 4, c = 5, e = 6; P is 0 except in
`Xor(And(P, A), And(P, B))`, where it is 3, and Q = 3). The
branch numbering of the reference enumeration is the one the [IO-012] message reports:
`Xor(And(A, Xor(B, C)), And(A, B))` lists {A, B}, {A, C}, {A, B}, so branches 0 and 2 clash. -/
example :
    -- [IO-012] AC5, rejected
    ¬ WellFormedOut [4] (Out.xor (.place 0) (.place 0) : Out Nat) ∧
    ¬ WellFormedOut [4] (Out.xor (.and (.place 0) (.place 1)) (.and (.place 1) (.place 0)) : Out Nat) ∧
    ¬ WellFormedOut [4] (Out.xor (.place 0) (.xor (.place 0) (.place 1)) : Out Nat) ∧
    ¬ WellFormedOut [4] (Out.and (.place 3) (.xor (.place 0) (.place 0)) : Out Nat) ∧
    ¬ WellFormedOut [4] (Out.xor (.and (.place 0) (.xor (.place 1) (.place 2)))
      (.and (.place 0) (.place 1)) : Out Nat) ∧
    ¬ WellFormedOut [4] (Out.xor (.place 0) (.timeout (.place 0)) : Out Nat) ∧
    ¬ WellFormedOut [4] (Out.xor (.place 1) (.timeout (.forward 4 1)) : Out Nat) ∧
    -- [IO-012] AC5, accepted
    WellFormedOut [4] (Out.xor (.and (.place 0) (.and (.place 1) (.place 2)))
      (.and (.place 0) (.place 1)) : Out Nat) ∧
    WellFormedOut [4] (Out.xor (.and (.place 3) (.place 0)) (.and (.place 3) (.place 1)) : Out Nat) ∧
    WellFormedOut [4] (Out.xor (.place 0) (.timeout (.place 1)) : Out Nat) ∧
    -- [IO-013] AC7
    ¬ WellFormedOut [4] (Out.timeout (.timeout (.place 0)) : Out Nat) ∧
    ¬ WellFormedOut [4] (Out.xor (.timeout (.place 0)) (.timeout (.place 1)) : Out Nat) ∧
    ¬ WellFormedOut [4] (Out.and (.timeout (.place 0)) (.xor (.place 1) (.timeout (.place 2))) : Out Nat) ∧
    WellFormedOut [4] (Out.timeout (.and (.place 0) (.place 1)) : Out Nat) ∧
    -- [IO-014] AC7
    ¬ WellFormedOut [4] (Out.forward 4 1 : Out Nat) ∧
    ¬ WellFormedOut [4] (Out.xor (.place 5) (.forward 4 1) : Out Nat) ∧
    ¬ WellFormedOut [4] (Out.and (.place 5) (.xor (.place 6) (.forward 4 1)) : Out Nat) ∧
    WellFormedOut [4] (Out.timeout (.forward 4 1) : Out Nat) ∧
    WellFormedOut [4] (Out.xor (.place 5) (.timeout (.and (.place 6) (.forward 4 1))) : Out Nat) ∧
    -- the numbering the [IO-012] message reports
    refBranchSets (Out.xor (.and (.place 0) (.xor (.place 1) (.place 2)))
      (.and (.place 0) (.place 1)) : Out Nat) = [{0, 1}, {0, 2}, {0, 1}] := by
  decide

end Libpetri.Spec
