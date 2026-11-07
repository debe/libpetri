import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.Glossary

set_option linter.missingDocs true

/-!
# IO-015: Output validation (`spec/02-input-output-specs.md`)

IO-015 is a pure-function requirement (kind F): it fixes the verdict of output validation, the
check an executor runs on what a completed action produced, as a function of the declared output
spec and the produced set. The statement is a predicate over an *output validator*: a function
from an output spec and a deposit to a verdict. The witness is the reference validator, which
counts the assignments of the spec (the output branches `Out.branches` lists, one per assignment)
whose claim is the produced set, and succeeds when there is exactly one.

The reference firing semantics (`Reference.Fires`) has no validation step: it lets a firing
deposit any output branch. The block therefore states the verdict, not a property of firings.

The verdict function is total over output specs, the ambiguous ones included. Building a
transition rejects an output spec whose distinct assignments claim one set ([IO-012]), so on a
spec that builds (`WellFormedOut`) the third clause never applies (theorem `IO_015_wf_noAmbiguous`)
and validation succeeds exactly when some assignment claims the produced set (theorem
`IO_015_wf_iff`). Deposits are compared per place ([CORE-036]): two deposits with the same count
in every place get the same verdict, whatever their order (theorem `IO_015_perPlace`).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

variable {N : Type}

/-! ## The model: an output validator -/

/-- An output validator ([IO-015]): the verdict of validating the deposit `d` of a completed
action against the declared output spec `o`. `true` is success, `false` a violation. The
produced set is the places of `d` (glossary: Produced set). -/
abbrev OutputValidator (N : Type) := Out N → List N → Bool

/-- A claim `b` *equals* the produced set of the deposit `d`: the same places, whatever the
counts. -/
def ClaimsExactly (b d : List N) : Prop := ∀ q, q ∈ b ↔ Produced d q

/-- **Assignment** (local term of [IO-015], not yet in the glossary): "An *assignment* selects
exactly one child at each `Xor` node it reaches". `Out.branches o` lists one claim per
assignment of `o` (a `Place` claims its place, a `ForwardInput` its `to`, an `And` the union of
its children's claims, an `Xor` and a `Timeout` their selected child's claim), so assignment `i`
of `o` is index `i` of that list. `ExactAssignment o d i`: assignment `i` of `o` claims a set
equal to the produced set of `d`. -/
def ExactAssignment (o : Out N) (d : List N) (i : Nat) : Prop :=
  ∃ b, o.branches[i]? = some b ∧ ClaimsExactly b d

/-- The reference validator: the number of assignments whose claim equals the produced set is
exactly one. -/
def ioRefValidate [DecidableEq N] : OutputValidator N :=
  fun o d => o.branches.countP (sameSetB · d) == 1

/- The reference validator is the witness model of IO-015's `holds` theorem. -/
#spec_witness ioRefValidate

/-! ## IO-015: Output Validation -/

requirement IO_015
  id "IO-015"
  title "Output Validation"
  kind F
  scope "every declared output spec"
  source verbatim "spec/02-input-output-specs.md"
  quote "An *assignment* selects exactly one child at each `Xor` node it reaches; nodes beneath an unselected `Xor` child are never evaluated."
        "*If* exactly one assignment claims a set *equal* to the produced set, *then* validation *shall* succeed."
        "*If* no assignment claims a set equal to the produced set, *then* validation *shall* fail, because nothing explains what was written."
        "*If* two or more assignments claim a set equal to the produced set, *then* validation *shall* fail, because the write is genuinely ambiguous."
        "For a transition that builds, no two assignments claim the same set ([IO-012]), so on a firing this third case does not arise."
        "The comparison is over **sets of places**: a spec names places, not counts, so an action that deposits several tokens into one claimed place conforms."
  reading "For every declared output spec o and every deposit d, with assignment i of o claiming the i-th entry of Out.branches o:"
          "if some assignment i claims exactly the produced set of d and every assignment that does is i, validation of d against o succeeds;"
          "if no assignment claims exactly the produced set of d, validation fails;"
          "if two different assignments i ≠ j both claim exactly the produced set of d, validation fails."
  assumes "A validator is the verdict function of one implementation: its inputs are the declared output spec and the tokens the completed action produced, as a deposit (a list of places with repetition); its output is success (true) or violation (false). The produced set is the places of the deposit (glossary: Produced set)."
          "When an action completes, an executor with output validation enabled, which is the default ([CONC-026]), shall validate its produced set against the transition's output spec. This sentence is the trigger and is not encoded: the block fixes the verdict of the check, not when it runs. An executor with the CONC-026 skip enabled runs no check, so the verdict constrains nothing there (CONC-026's subject). A completion that fails validation deposits no outcome and is not a firing (glossary: Fire); a transition with no output spec has nothing to validate; the timeout outcome (IO-013) does not complete the action and is not validated."
          "Assignments are counted, not their claims: two assignments that claim the same set are two (Xor(A, A) with A produced has two exact assignments and fails). Out.branches enumerates one claim per assignment, in the claim rules of the bullet list; n-ary And and Xor are read as right-nested binary nodes, which changes neither the number of assignments, their claims nor their IO-016 order."
          "The verdict function is total: the three clauses range over every output spec, those IO-012 rejects at build included. The sentence 'For a transition that builds, no two assignments claim the same set' is a consequence, not a clause: the glossary's WellFormedOut is the build-time constraint on an output spec, and on a spec satisfying it no two different assignments are exact for any deposit (theorem IO_015_wf_noAmbiguous), so under IO-015 the verdict is success exactly when some assignment is exact (theorem IO_015_wf_iff). The theorems use only its IO-012 conjunct, pairwise distinct branch sets."
          "The set-of-places sentence is a consequence, not a clause: the three clauses fix the verdict from the number of exact assignments (theorem IO_015_determines), and that number reads only the produced set (theorem IO_015_setOnly). Deposits are compared per place (CORE-036): two deposits with the same count in every place, in any order, get the same verdict (theorem IO_015_perPlace)."
          "AC1 (conforming output → success) is the first clause, 'conforming' read as 'exactly one exact assignment'."
          "AC2 (non-conforming output → failure event emitted) and AC3 (consumed input tokens are not restored on failure) are executor behaviour on a failed completion ('Validation failure is treated as a transition failure', EVT-007); the failure is not a firing of the reference semantics, which has no failed completion, so neither is encoded here."
          "AC4 (zero exact assignments → violation; two or more → violation) is the second and third clauses."
          "AC5 (Xor(And(A, B, C), And(A, B)) with A, B, C produced → success) is checked for every validator satisfying IO-015 (theorem IO_015_ac5)."
          "AC6 (output spec declared, action produces nothing → validation failure on every firing) is checked for every validator satisfying IO-015 and every output spec (theorem IO_015_ac6): every claim names at least one place, so none equals the empty produced set. That the built-in passthrough is rejected before execution is CORE-043's subject."
          "AC7 (mid-action publication) fixes which tokens make up the deposit the validator sees (published places count) and that published tokens stay in the marking on a violation; both are executor behaviour outside the verdict function and are not encoded. With the published places in the deposit, the AC7 verdicts (And(A, B) with A, B produced → success; with A only → violation) are checked on the reference validator."
          "AC8 (And is unordered) is not a separate clause: a claim is compared as a set, and permuting the children of an And permutes the assignments and the order of places within a claim. It is checked for the AC8 pair And(A, Xor(D, E)) / And(Xor(D, E), A) on every produced set drawn from A, D, E and one foreign place, the empty one included (theorem IO_015_ac8)."
          "AC9 (Xor(And(A, C), B) with B and C produced → violation) is checked for every validator satisfying IO-015 (theorem IO_015_ac9)."
          "AC10 (Xor(And(A, Xor(D, E)), A) with only A produced → success) is checked for every validator satisfying IO-015 (theorem IO_015_ac10)."
  signoff "pending"
  statement : ∀ {N : Type}, OutputValidator N → Prop :=
    fun V =>
      (∀ o d i, ExactAssignment o d i → (∀ j, ExactAssignment o d j → j = i) → V o d = true) ∧
      (∀ o d, (∀ i, ¬ ExactAssignment o d i) → V o d = false) ∧
      (∀ o d i j, i ≠ j → ExactAssignment o d i → ExactAssignment o d j → V o d = false)

/- The pinned readable form of IO-015: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.IO_015 : {N : Type} → OutputValidator N → Prop :=
fun {N} V =>
  (∀ (o : Out N) (d : List N) (i : ℕ),
      ExactAssignment o d i → (∀ (j : ℕ), ExactAssignment o d j → j = i) → V o d = true) ∧
    (∀ (o : Out N) (d : List N), (∀ (i : ℕ), ¬ExactAssignment o d i) → V o d = false) ∧
      ∀ (o : Out N) (d : List N) (i j : ℕ), i ≠ j → ExactAssignment o d i → ExactAssignment o d j → V o d = false
-/
#guard_msgs in #print IO_015

/-! ### Counting lemmas -/

/-- `sameSetB` decides `ClaimsExactly`. -/
theorem sameSetB_iff_claims [DecidableEq N] (b d : List N) : sameSetB b d = true ↔ ClaimsExactly b d := by
  simp only [sameSetB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, ClaimsExactly,
    Produced]
  exact ⟨fun ⟨h1, h2⟩ q => ⟨h1 q, h2 q⟩, fun h => ⟨fun q => (h q).1, fun q => (h q).2⟩⟩

/-- `ExactAssignment`, read through `sameSetB`. -/
theorem exactAssignment_iff [DecidableEq N] (o : Out N) (d : List N) (i : Nat) :
    ExactAssignment o d i ↔ ∃ b, o.branches[i]? = some b ∧ sameSetB b d = true := by
  simp only [ExactAssignment, sameSetB_iff_claims]

/-- Two different positions of `l` satisfying `p` make `countP p l` at least two. -/
theorem two_le_countP {α : Type} (p : α → Bool) :
    ∀ (l : List α) (i j : Nat) (a b : α), i ≠ j → l[i]? = some a → l[j]? = some b →
      p a = true → p b = true → 2 ≤ l.countP p
  | [], i, _, _, _, _, hi, _, _, _ => by simp at hi
  | x :: t, 0, 0, _, _, hij, _, _, _, _ => absurd rfl hij
  | x :: t, 0, j + 1, a, b, _, hi, hj, ha, hb => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    have : 0 < t.countP p := List.countP_pos_iff.2 ⟨b, List.mem_of_getElem? hj, hb⟩
    rw [List.countP_cons, if_pos ha]; omega
  | x :: t, i + 1, 0, a, b, _, hi, hj, ha, hb => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
    subst hj
    have : 0 < t.countP p := List.countP_pos_iff.2 ⟨a, List.mem_of_getElem? hi, ha⟩
    rw [List.countP_cons, if_pos hb]; omega
  | x :: t, i + 1, j + 1, a, b, hij, hi, hj, ha, hb => by
    have := two_le_countP p t i j a b (fun h => hij (by rw [h])) hi hj ha hb
    rw [List.countP_cons]; omega

/-- A `countP` of at least two has two different positions satisfying `p`. -/
theorem exists_two_of_two_le_countP {α : Type} (p : α → Bool) :
    ∀ l : List α, 2 ≤ l.countP p →
      ∃ (i j : Nat) (a b : α), i ≠ j ∧ l[i]? = some a ∧ l[j]? = some b ∧ p a = true ∧ p b = true
  | [], h => by simp at h
  | x :: t, h => by
    rw [List.countP_cons] at h
    by_cases hx : p x = true
    · have : 0 < t.countP p := by rw [if_pos hx] at h; omega
      obtain ⟨b, hb, hpb⟩ := List.countP_pos_iff.1 this
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hb
      exact ⟨0, k + 1, x, b, by omega, rfl, hk, hx, hpb⟩
    · have : 2 ≤ t.countP p := by rw [if_neg hx] at h; omega
      obtain ⟨i, j, a, b, hij, hi, hj, ha, hb⟩ := exists_two_of_two_le_countP p t this
      exact ⟨i + 1, j + 1, a, b, by omega, hi, hj, ha, hb⟩

/-- The number of exact assignments, as the reference validator counts them. -/
abbrev exactCount [DecidableEq N] (o : Out N) (d : List N) : Nat :=
  o.branches.countP (sameSetB · d)

/-- No exact assignment exactly when the count is zero. -/
theorem noExact_iff [DecidableEq N] (o : Out N) (d : List N) :
    (∀ i, ¬ ExactAssignment o d i) ↔ exactCount o d = 0 := by
  rw [List.countP_eq_zero]
  constructor
  · intro h b hb hs
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hb
    exact h i ((exactAssignment_iff o d i).2 ⟨b, hi, hs⟩)
  · intro h i hi
    obtain ⟨b, hb, hs⟩ := (exactAssignment_iff o d i).1 hi
    exact h b (List.mem_of_getElem? hb) hs

/-- Two different exact assignments exactly when the count is at least two. -/
theorem twoExact_iff [DecidableEq N] (o : Out N) (d : List N) :
    (∃ i j, i ≠ j ∧ ExactAssignment o d i ∧ ExactAssignment o d j) ↔ 2 ≤ exactCount o d := by
  constructor
  · rintro ⟨i, j, hij, hi, hj⟩
    obtain ⟨a, ha, hsa⟩ := (exactAssignment_iff o d i).1 hi
    obtain ⟨b, hb, hsb⟩ := (exactAssignment_iff o d j).1 hj
    exact two_le_countP _ _ i j a b hij ha hb hsa hsb
  · intro h
    obtain ⟨i, j, a, b, hij, ha, hb, hsa, hsb⟩ := exists_two_of_two_le_countP _ _ h
    exact ⟨i, j, hij, (exactAssignment_iff o d i).2 ⟨a, ha, hsa⟩,
      (exactAssignment_iff o d j).2 ⟨b, hb, hsb⟩⟩

/-- Exactly one exact assignment exactly when the count is one. -/
theorem oneExact_iff [DecidableEq N] (o : Out N) (d : List N) :
    (∃ i, ExactAssignment o d i ∧ ∀ j, ExactAssignment o d j → j = i) ↔ exactCount o d = 1 := by
  constructor
  · rintro ⟨i, hi, hu⟩
    have h0 : exactCount o d ≠ 0 := fun h => (noExact_iff o d).2 h i hi
    have h2 : ¬ 2 ≤ exactCount o d := fun h => by
      obtain ⟨j, k, hjk, hj, hk⟩ := (twoExact_iff o d).2 h
      exact hjk ((hu j hj).trans (hu k hk).symm)
    omega
  · intro h
    have h0 : ¬ ∀ i, ¬ ExactAssignment o d i := fun h' => by
      rw [noExact_iff] at h'; omega
    obtain ⟨i, hi⟩ := Classical.not_forall_not.1 h0
    refine ⟨i, hi, fun j hj => Classical.byContradiction fun hji => ?_⟩
    have := (twoExact_iff o d).1 ⟨j, i, hji, hj, hi⟩
    omega

/-! ### The reference validator satisfies IO-015, and IO-015 determines the verdict -/

/-- The reference validator satisfies IO-015: one exact assignment is a count of one, none a
count of zero, two different ones a count of at least two. -/
@[evidence holds IO_015]
theorem IO_015_reference {N : Type} [DecidableEq N] : IO_015 (ioRefValidate (N := N)) := by
  refine ⟨fun o d i hi hu => ?_, fun o d h => ?_, fun o d i j hij hi hj => ?_⟩
  · have := (oneExact_iff o d).1 ⟨i, hi, hu⟩
    simp only [ioRefValidate, exactCount] at this ⊢
    simp [this]
  · have := (noExact_iff o d).1 h
    simp only [ioRefValidate, exactCount] at this ⊢
    simp [this]
  · have := (twoExact_iff o d).1 ⟨i, j, hij, hi, hj⟩
    simp only [ioRefValidate, exactCount] at this ⊢
    simp only [beq_eq_false_iff_ne, ne_eq]; omega

/-- IO-015 determines the verdict: every validator satisfying it agrees with the reference
validator on every output spec and every deposit. -/
theorem IO_015_determines [DecidableEq N] {V : OutputValidator N} (h : IO_015 V) (o : Out N)
    (d : List N) : V o d = ioRefValidate o d := by
  have hr := IO_015_reference (N := N)
  by_cases h0 : exactCount o d = 0
  · have hn := (noExact_iff o d).2 h0
    rw [h.2.1 o d hn, hr.2.1 o d hn]
  · by_cases h1 : exactCount o d = 1
    · obtain ⟨i, hi, hu⟩ := (oneExact_iff o d).2 h1
      rw [h.1 o d i hi hu, hr.1 o d i hi hu]
    · obtain ⟨i, j, hij, hi, hj⟩ := (twoExact_iff o d).2 (by omega)
      rw [h.2.2 o d i j hij hi hj, hr.2.2 o d i j hij hi hj]

/-- The comparison is over sets of places: under IO-015 two deposits with the same places get
the same verdict, whatever the counts. -/
theorem IO_015_setOnly [DecidableEq N] {V : OutputValidator N} (h : IO_015 V) (o : Out N)
    (d d' : List N) (hd : ∀ q, q ∈ d ↔ q ∈ d') : V o d = V o d' := by
  have hs : ∀ b, sameSetB b d = sameSetB b d' := fun b => by
    rw [Bool.eq_iff_iff, sameSetB_iff_claims, sameSetB_iff_claims]
    simp only [ClaimsExactly, Produced, hd]
  rw [IO_015_determines h, IO_015_determines h]
  simp only [ioRefValidate, hs]

/-- Deposits are compared per place ([CORE-036]): under IO-015 two deposits that put the same
number of tokens in every place get the same verdict, whatever their order. -/
theorem IO_015_perPlace [DecidableEq N] {V : OutputValidator N} (h : IO_015 V) (o : Out N)
    (d d' : List N) (hd : ∀ q, Deposits d q = Deposits d' q) : V o d = V o d' := by
  refine IO_015_setOnly h o d d' fun q => ?_
  have := hd q
  simp only [Deposits, depProd] at this
  rw [← List.count_pos_iff, ← List.count_pos_iff, this]

/-! ### On a spec that builds, the third clause never applies -/

/-- `sameSetB` is symmetric. -/
theorem sameSetB_comm [DecidableEq N] (a b : List N) : sameSetB a b = sameSetB b a := by
  simp only [sameSetB, Bool.and_comm]

/-- Two different indices of the branches of a spec that builds name different sets. -/
theorem IO_015_distinct_ne [DecidableEq N] {o : Out N}
    (h : o.branches.Pairwise (fun a b => ¬ SameSet a b)) {i j : Nat}
    {a b : List N} (hij : i ≠ j) (ha : o.branches[i]? = some a) (hb : o.branches[j]? = some b) :
    sameSetB a b = false := by
  rw [List.pairwise_iff_getElem] at h
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 ha
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 hb
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · exact Bool.eq_false_iff.2 fun hs => h i j hi hj hlt ((sameSetB_iff _ _).1 hs)
  · rw [sameSetB_comm]
    exact Bool.eq_false_iff.2 fun hs => h j i hj hi hlt ((sameSetB_iff _ _).1 hs)

/-- Two claims both equal to the produced set of `d` are the same set. -/
theorem sameSetB_of_exact [DecidableEq N] {a b d : List N} (ha : ClaimsExactly a d)
    (hb : ClaimsExactly b d) : sameSetB a b = true := by
  simp only [sameSetB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  exact ⟨fun q hq => (hb q).2 ((ha q).1 hq), fun q hq => (ha q).2 ((hb q).1 hq)⟩

/-- On a spec that builds, no deposit has two different exact assignments: the third clause of
IO-015 never applies ("For a transition that builds, no two assignments claim the same set"). -/
theorem IO_015_wf_noAmbiguous [DecidableEq N] {ins : List N} {o : Out N} (hw : WellFormedOut ins o) (d : List N)
    {i j : Nat} (hij : i ≠ j) (hi : ExactAssignment o d i) (hj : ExactAssignment o d j) : False := by
  obtain ⟨a, ha, hea⟩ := hi
  obtain ⟨b, hb, heb⟩ := hj
  have := IO_015_distinct_ne hw.2.2.2.2.2 hij ha hb
  rw [sameSetB_of_exact hea heb] at this
  exact Bool.noConfusion this

/-- On a spec that builds, IO-015's verdict is success exactly when some assignment claims the
produced set. -/
theorem IO_015_wf_iff [DecidableEq N] {V : OutputValidator N} (h : IO_015 V) {ins : List N}
    {o : Out N} (hw : WellFormedOut ins o) (d : List N) : V o d = true ↔ ∃ i, ExactAssignment o d i := by
  constructor
  · intro hv
    refine Classical.byContradiction fun hn => ?_
    rw [h.2.1 o d (fun i hi => hn ⟨i, hi⟩)] at hv
    exact Bool.noConfusion hv
  · rintro ⟨i, hi⟩
    exact h.1 o d i hi fun j hj =>
      Classical.byContradiction fun hji => IO_015_wf_noAmbiguous hw d hji hj hi

/-- The build-time constraint rejects exactly the IO-012, IO-013 and IO-014 examples it should
and accepts the IO-015 ACs (A, B, C, D, E, P = 0, 1, 2, 3, 4, 5; `a` = 6): `Xor(P, P)`,
`Xor(And(A, B), And(B, A))`, `Xor(P, Timeout(P))`, `Timeout(Timeout(P))` and a bare
`ForwardInput(a, B)` do not build; the AC5, AC9 and AC10 specs and `Xor(A, Timeout(B))` do. -/
example :
    ¬ WellFormedOut [6] (.xor (.place 5) (.place 5) : Out Nat) ∧
    ¬ WellFormedOut [6] (.xor (.and (.place 0) (.place 1)) (.and (.place 1) (.place 0)) : Out Nat) ∧
    ¬ WellFormedOut [6] (.xor (.place 5) (.timeout (.place 5)) : Out Nat) ∧
    ¬ WellFormedOut [6] (.timeout (.timeout (.place 5)) : Out Nat) ∧
    ¬ WellFormedOut [6] (.forward 6 1 : Out Nat) ∧
    WellFormedOut [6] (.xor (.and (.place 0) (.and (.place 1) (.place 2))) (.and (.place 0) (.place 1))
      : Out Nat) ∧
    WellFormedOut [6] (.xor (.and (.place 0) (.place 2)) (.place 1) : Out Nat) ∧
    WellFormedOut [6] (.xor (.and (.place 0) (.xor (.place 3) (.place 4))) (.place 0) : Out Nat) ∧
    WellFormedOut [6] (.xor (.place 0) (.timeout (.place 1)) : Out Nat) := by
  decide

/-- Every claim names at least one place. -/
theorem branches_ne_nil_mem : ∀ (o : Out N), ∀ b ∈ o.branches, b ≠ []
  | .place p, b, hb => by simp [Out.branches] at hb; simp [hb]
  | .forward _ dst, b, hb => by simp [Out.branches] at hb; simp [hb]
  | .and l r, b, hb => by
    simp only [Out.branches, cross, List.mem_flatMap, List.mem_map] at hb
    obtain ⟨x, hx, y, -, rfl⟩ := hb
    simp [branches_ne_nil_mem l x hx]
  | .xor l r, b, hb => by
    simp only [Out.branches, List.mem_append] at hb
    exact hb.elim (branches_ne_nil_mem l b) (branches_ne_nil_mem r b)
  | .timeout c, b, hb => branches_ne_nil_mem c b hb

/-! ### The acceptance criteria, for every validator satisfying IO-015 -/

/-- AC6: an action that produces nothing fails validation against every declared output spec. -/
theorem IO_015_ac6 [DecidableEq N] {V : OutputValidator N} (h : IO_015 V) (o : Out N) :
    V o [] = false := by
  refine h.2.1 o [] fun i ⟨b, hb, hs⟩ => ?_
  obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil b (branches_ne_nil_mem o b (List.mem_of_getElem? hb))
  exact absurd ((hs q).1 hq) (by simp [Produced])

/-- AC5: `Xor(And(A, B, C), And(A, B))` with A, B, C produced succeeds (A, B, C = 0, 1, 2). -/
theorem IO_015_ac5 {V : OutputValidator Nat} (h : IO_015 V) :
    V (.xor (.and (.place 0) (.and (.place 1) (.place 2))) (.and (.place 0) (.place 1)))
      [0, 1, 2] = true := by
  rw [IO_015_determines h]; decide

/-- AC9: `Xor(And(A, C), B)` with B and C produced is a violation (A, B, C = 0, 1, 2). -/
theorem IO_015_ac9 {V : OutputValidator Nat} (h : IO_015 V) :
    V (.xor (.and (.place 0) (.place 2)) (.place 1)) [1, 2] = false := by
  rw [IO_015_determines h]; decide

/-- AC10: `Xor(And(A, Xor(D, E)), A)` with only A produced succeeds (A, D, E = 0, 3, 4). -/
theorem IO_015_ac10 {V : OutputValidator Nat} (h : IO_015 V) :
    V (.xor (.and (.place 0) (.xor (.place 3) (.place 4))) (.place 0)) [0] = true := by
  rw [IO_015_determines h]; decide

/-- AC8: `And(A, Xor(D, E))` and `And(Xor(D, E), A)` get the same verdict on every produced set
drawn from A, D, E and the foreign place 5, the empty one included (A, D, E = 0, 3, 4). -/
theorem IO_015_ac8 {V : OutputValidator Nat} (h : IO_015 V) :
    ∀ d ∈ [0, 3, 4, 5].sublists,
      V (.and (.place 0) (.xor (.place 3) (.place 4))) d =
        V (.and (.xor (.place 3) (.place 4)) (.place 0)) d := by
  intro d hd
  rw [IO_015_determines h, IO_015_determines h]
  revert d; decide

/-- AC7 on the reference validator, with the published places in the deposit: `And(A, B)` with
A published and B written succeeds; with A published and B never written it is a violation
(A, B = 0, 1). -/
example : ioRefValidate (.and (.place 0) (.place 1)) [0, 1] = true ∧
    ioRefValidate (.and (.place 0) (.place 1)) [0] = false := by decide

/-- Several tokens into one claimed place conform. -/
example : ioRefValidate (.place 0) [0, 0, 0] = true := by decide

/-! ### Examples: wrong validators -/

/-- A validator that accepts when some assignment's claim is covered by the produced set: a
token written outside the selected branch is deposited silently. -/
def io015_coverValidator [DecidableEq N] : OutputValidator N :=
  fun o d => o.branches.any (fun b => b.all (fun q => decide (q ∈ d)))

/-- ✗ Accepting a write outside the selected branch violates IO-015 (second clause): with
`Xor(And(A, C), B)` and B, C produced (A, B, C = 0, 1, 2) no assignment is exact, yet the
covering validator accepts. -/
@[evidence forbids IO_015]
theorem IO_015_forbids_cover : ¬ IO_015 (io015_coverValidator (N := Nat)) := by
  intro h
  have := h.2.1 (.xor (.and (.place 0) (.place 2)) (.place 1)) [1, 2]
    ((noExact_iff _ _).2 (by decide))
  exact absurd this (by decide)

/-- A validator by the number of exact assignments: `ok n` is the verdict when `n` assignments
claim exactly the produced set. -/
def io015_byCount [DecidableEq N] (ok : Nat → Bool) : OutputValidator N :=
  fun o d => ok (exactCount o d)

/-- A validator that rejects every output. -/
abbrev io015_rejectAll [DecidableEq N] : OutputValidator N := io015_byCount fun _ => false

/-- A validator that accepts at most one exact assignment, zero included. -/
abbrev io015_atMostOne [DecidableEq N] : OutputValidator N := io015_byCount fun n => n ≤ 1

/-- A validator that accepts some exact assignment, without the ambiguity check. -/
abbrev io015_someExact [DecidableEq N] : OutputValidator N := io015_byCount fun n => 1 ≤ n

/-- ✗ Accepting an ambiguous write violates IO-015 (third clause): `Xor(A, A)` with A produced
(A = 0) has two exact assignments, yet the validator without the ambiguity check accepts. -/
@[evidence forbids IO_015]
theorem IO_015_forbids_someExact : ¬ IO_015 (io015_someExact (N := Nat)) := by
  intro h
  obtain ⟨i, j, hij, hi, hj⟩ := (twoExact_iff (.xor (.place 0) (.place 0)) [0]).2 (by decide)
  exact absurd (h.2.2 _ _ i j hij hi hj) (by decide)

/-- ✗ Rejecting everything violates IO-015 (first clause): `Place(A)` with A produced
(A = 0) has exactly one exact assignment. -/
@[evidence forbids IO_015]
theorem IO_015_forbids_rejectAll : ¬ IO_015 (io015_rejectAll (N := Nat)) := by
  intro h
  obtain ⟨i, hi, hu⟩ := (oneExact_iff (.place 0) [0]).2 (by decide)
  exact absurd (h.1 _ _ i hi hu) (by decide)

/-- ✗ Accepting an unexplained write violates IO-015 (second clause): `Place(A)` with nothing
produced (A = 0) has no exact assignment, yet the at-most-one validator accepts. -/
@[evidence forbids IO_015]
theorem IO_015_forbids_atMostOne : ¬ IO_015 (io015_atMostOne (N := Nat)) := by
  intro h
  exact absurd (h.2.1 (.place 0) [] ((noExact_iff _ _).2 (by decide))) (by decide)

/-! ### Mutants: one clause dropped at a time -/

/-- Mutant reading of IO-015 that drops the first clause: unexplained and ambiguous writes fail,
but nothing is required to succeed. -/
def IO_015_mutant_dropSucceed {N : Type} (V : OutputValidator N) : Prop :=
  (∀ o d, (∀ i, ¬ ExactAssignment o d i) → V o d = false) ∧
    (∀ o d i j, i ≠ j → ExactAssignment o d i → ExactAssignment o d j → V o d = false)

/-- The rejecting validator kills the first mutant. -/
@[evidence mutant IO_015]
theorem IO_015_mutant_dropSucceed_killed :
    IO_015_mutant_dropSucceed (io015_rejectAll (N := Nat)) ∧
      ¬ IO_015 (io015_rejectAll (N := Nat)) :=
  ⟨⟨fun _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩, IO_015_forbids_rejectAll⟩

/-- Mutant reading of IO-015 that drops the second clause: a write no assignment explains may
succeed. -/
def IO_015_mutant_dropNone {N : Type} (V : OutputValidator N) : Prop :=
  (∀ o d i, ExactAssignment o d i → (∀ j, ExactAssignment o d j → j = i) → V o d = true) ∧
    (∀ o d i j, i ≠ j → ExactAssignment o d i → ExactAssignment o d j → V o d = false)

/-- The at-most-one validator kills the second mutant: it accepts one exact assignment and
rejects two, but also accepts none. -/
@[evidence mutant IO_015]
theorem IO_015_mutant_dropNone_killed :
    IO_015_mutant_dropNone (io015_atMostOne (N := Nat)) ∧
      ¬ IO_015 (io015_atMostOne (N := Nat)) := by
  refine ⟨⟨fun o d i hi hu => ?_, fun o d i j hij hi hj => ?_⟩, IO_015_forbids_atMostOne⟩
  · have := (oneExact_iff o d).1 ⟨i, hi, hu⟩
    simp [io015_byCount, this]
  · have := (twoExact_iff o d).1 ⟨i, j, hij, hi, hj⟩
    simp only [io015_byCount, decide_eq_false_iff_not]; omega

/-- Mutant reading of IO-015 that drops the third clause: an ambiguous write may succeed. -/
def IO_015_mutant_dropAmbiguous {N : Type} (V : OutputValidator N) : Prop :=
  (∀ o d i, ExactAssignment o d i → (∀ j, ExactAssignment o d j → j = i) → V o d = true) ∧
    (∀ o d, (∀ i, ¬ ExactAssignment o d i) → V o d = false)

/-- The some-exact validator kills the third mutant: it accepts one exact assignment and rejects
none, but also accepts two. -/
@[evidence mutant IO_015]
theorem IO_015_mutant_dropAmbiguous_killed :
    IO_015_mutant_dropAmbiguous (io015_someExact (N := Nat)) ∧
      ¬ IO_015 (io015_someExact (N := Nat)) := by
  refine ⟨⟨fun o d i hi hu => ?_, fun o d h => ?_⟩, IO_015_forbids_someExact⟩
  · have := (oneExact_iff o d).1 ⟨i, hi, hu⟩
    simp [io015_byCount, this]
  · have := (noExact_iff o d).1 h
    simp [io015_byCount, this]

/-- All three clauses are exercised by the reference validator: AC5 has exactly one exact
assignment and succeeds; AC9 has none and fails; `Xor(A, A)` with A produced has two and
fails. `Xor(A, A)` does not build and the AC5 spec does, so the build-time constraint of
`IO_015_wf_noAmbiguous` is neither empty nor everything. -/
@[evidence nonvacuous IO_015]
theorem IO_015_nonvacuous :
    exactCount (.xor (.and (.place 0) (.and (.place 1) (.place 2))) (.and (.place 0) (.place 1)))
        [0, 1, 2] = 1 ∧
      ioRefValidate (.xor (.and (.place 0) (.and (.place 1) (.place 2)))
        (.and (.place 0) (.place 1))) [0, 1, 2] = true ∧
      exactCount (.xor (.and (.place 0) (.place 2)) (.place 1)) [1, 2] = 0 ∧
      ioRefValidate (.xor (.and (.place 0) (.place 2)) (.place 1)) [1, 2] = false ∧
      exactCount (.xor (.place 0) (.place 0)) [0] = 2 ∧
      ioRefValidate (.xor (.place 0) (.place 0)) [0] = false ∧
      ¬ WellFormedOut [6] (.xor (.place 0) (.place 0) : Out Nat) ∧
      WellFormedOut [6] (.xor (.and (.place 0) (.and (.place 1) (.place 2)))
        (.and (.place 0) (.place 1)) : Out Nat) := by
  decide

end Libpetri.Spec
