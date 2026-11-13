import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryBuild
import Libpetri.Spec.Req.CORE_020
import Libpetri.Spec.Text.CORE_021

set_option linter.missingDocs true

/-!
# CORE-021: Transition identity (`spec/01-core-model.md`)

CORE-021 is a pure-function requirement (kind F) over an abstract transition builder
`B : TBuilder N A` (`Reference/Build.lean`): the `k`-th build call on an input either fails or
returns an instance, and `B.same` is the implementation's equality of transitions. The statement
says that two separate build calls never return equal transitions, whatever they were given, and
that a built transition is equal to itself. It says nothing about the fields a built transition
carries (CORE-020).

The witness is the reference transition builder `refTransBuild`, whose instances are a call
number and a definition and whose equality compares call numbers. Wrong builders are killed: one
that compares definitions (two builds of "Process" are equal), one that compares names (the
mutant reading identity by name), and one whose equality is never true (the mutant reading the
body sentence "Two transition instances are never equal" literally, so that even a transition and
itself are unequal).

Which build calls succeed is CORE-020's (its last line). Line 1 compares only calls that both
succeed, so CORE-021 alone is met by a builder that refuses a second build of a name and then
compares names (`CORE_021_allows_registry`); CORE-020 rejects that builder, and every builder that
meets both requirements returns two unequal transitions for two calls on one buildable input
(`core021_with_020`).

Ruling D10 identifies the transitions of a net by name, under one shared assumption that their
names are pairwise distinct (ruling D23, `NetNamesDistinct`). The two do not compete:
`CORE_021_allows_sameName` builds a net holding two unequal transitions named "Process"
(CORE-020 lets no builder refuse a buildable input for its name), and that net lies outside the assumption; one firing labelled "Process"
then reaches two different markings.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## CORE-021: Transition Identity -/

requirement CORE_021
  id "CORE-021"
  title "Transition Identity"
  kind F
  scope "all transition builders"
  source verbatim "spec/01-core-model.md"
  covers CORE_021.s1, CORE_021.s2
  reading "For every transition builder B:"
          "if call k on input i returns x and call k' on input i' returns y, with k and k' two different calls, then x and y are not the same transition (B.same), whatever i and i' are; in particular when they have the same name, and when i and i' are the same input;"
          "if call k on input i returns x, then x is the same transition as x."
  assumes "A transition builder (TBuilder) is the build call of one implementation: the k-th call on an input either fails or returns an instance. A transition instance is what one build call returns (AC1 says 'built'), and the call number k names that call. B.same is the implementation's equality of transitions: Rust's PartialEq and Hash on the TransitionId a global counter hands out per build (TransitionId::next and the PartialEq and Hash impls of Transition, rust/libpetri-core/src/transition.rs), Java's Object.equals, which Transition does not override (java/src/main/java/org/libpetri/core/Transition.java), and TypeScript's === on the built object (class Transition in typescript/src/core/transition.ts)."
          "Which calls succeed is CORE-020's (its last line: a call succeeds exactly when its input builds and its timing is valid, whatever calls came before). Line 1 compares only calls that both succeed, so CORE-021 alone is met vacuously by a builder that fails every call, and by a name-registry builder that refuses a second build of a name even when its equality compares names (CORE_021_allows_registry). CORE-020 rejects both, and every builder meeting CORE-020 and CORE-021 returns two unequal transitions with one name for any two calls on one buildable input (core021_with_020), so the two together rule out identity by name; that is what AC1 and the test derivation need, since both build 'Process' twice."
          "Copying a built transition is not a build call, and the markdown body says a copy is the same instance and equal to it. A Rust clone copies the TransitionId and is equal to its original (#[derive(Clone)] on Transition in rust/libpetri-core/src/transition.rs); every Rust rebuild (renaming, composition, binding) goes through build() and takes a fresh id, and Java (Transition.Builder.build) and TypeScript (TransitionBuilder.build in transition.ts) each have one construction site. TBuilder has no copy operation, so the statement does not check copies: a Clone that drew a fresh TransitionId would give the same builder as the reference and meet CORE-021, and its effect would show in CORE-040 (one transition added twice would count as two). What a net holds when one instance is added to it twice (Java and TypeScript keep a set, Rust keeps a list) is CORE-040's, which assumes the added transitions are pairwise distinct."
          "The Python binding's equality is Rust's: PetriNet.transitions returns a fresh wrapper of a clone on every access, and the Transition wrapper's __eq__ and __hash__ compare and hash the wrapped transition, so its TransitionId (rust/libpetri-py/src/model.rs, PyTransition __eq__ and __hash__). Two wrappers of one built transition are equal, so a transition read back from a net is equal to itself (net.transitions[0] == net.transitions[0], AC2; python/tests/test_smoke.py test_core_021_ac2_transition_read_back_equals_itself), and two builds are unequal. A wrapper compared by Python object identity, under which a transition read back from a net is unequal to itself (the behaviour RD-07 in spec/runtime-defects.md recorded of the binding), would violate line 2."
          "Ruling D10 identifies the transitions of a net by name (TIME-010 to TIME-015, binding by name in CORE-042, events, export ids, composition channels), under one shared assumption that the transitions of a net have pairwise distinct names (ruling D23 (a); NamesDistinct in Spec/GlossaryTime.lean, NetNamesDistinct in Spec/GlossaryBuild.lean). CORE-021 is about the equality of transition objects and does not contradict it: CORE-020 lets no builder refuse a buildable input for its name, so a net holding two unequal transitions of one name builds (CORE_021_allows_sameName), and such a net is outside every name-keyed requirement. CORE-020's name bullet ('identifies the transition, see [TIME-010]') is that ruling."
          "Only reflexivity is stated (AC2). That the equality is also symmetric and transitive, and that equal transitions hash alike, holds in every runtime and is not stated. Two results of one call number are not compared: a call is one call."
          "AC1 (two transitions built with the same name are not equal) is line 1 on two inputs of one name; CORE_021_nonvacuous builds one input named Process twice and gets two unequal transitions with equal definitions, which is also the test derivation. AC2 is line 2. A builder whose equality compares definitions (CORE_021_forbids_structural) violates line 1; one that compares names meets the name reading of line 1 and violates CORE-021 (CORE_021_mutant_byName_killed); one whose equality is never true meets the literal reading of the body sentence and violates line 2 (CORE_021_mutant_neverEqual_killed). A builder whose id counter wraps (here modulo 4) violates line 1 on calls 0 and 4 of one input (CORE_021_forbids_wrap); one that memoizes its instance per input keeps two different inputs of one name apart, so it passes the AC1 test written with two builders, and violates line 1 on calls 0 and 1 of one input (CORE_021_forbids_memo)."
  signoff "2026-11-13 7792de31f8f3f5f3 ai"
  statement : ∀ {N A : Type}, TBuilder N A → Prop :=
    fun B =>
      (∀ k k' i i' x y, k ≠ k' → B.build k i = .ok x → B.build k' i' = .ok y → ¬ B.same x y) ∧
      (∀ k i x, B.build k i = .ok x → B.same x x)

/- The pinned readable form of CORE-021: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CORE_021 : {N A : Type} → TBuilder N A → Prop :=
fun {N A} B =>
  (∀ (k k' : ℕ) (i i' : TransIn N A) (x y : B.I),
      k ≠ k' → B.build k i = Except.ok x → B.build k' i' = Except.ok y → ¬B.same x y) ∧
    ∀ (k : ℕ) (i : TransIn N A) (x : B.I), B.build k i = Except.ok x → B.same x x
-/
#guard_msgs in #print CORE_021

/-! ### The two lines, named (for the mutants) -/

section Lines

variable {N A : Type}

/-- Line 1 of CORE-021. -/
def core021_line1 (B : TBuilder N A) : Prop :=
  ∀ k k' i i' x y, k ≠ k' → B.build k i = .ok x → B.build k' i' = .ok y → ¬ B.same x y

/-- Line 2 of CORE-021. -/
def core021_line2 (B : TBuilder N A) : Prop :=
  ∀ k i x, B.build k i = .ok x → B.same x x

/-- CORE-021 is its two lines. -/
theorem core021_iff (B : TBuilder N A) : CORE_021 B ↔ core021_line1 B ∧ core021_line2 B :=
  Iff.rfl

end Lines

/-! ### The reference -/

section Reference

variable {N A : Type} [DecidableEq N] [ToString N]

/-- A successful build call of the reference transition builder returns an instance carrying its
call number. -/
theorem core021_ref_call {k : Nat} {i : TransIn N A} {x : (refTransBuild (N := N) (A := A)).I}
    (h : (refTransBuild (N := N) (A := A)).build k i = .ok x) : x.1.1 = k := by
  rw [refTransBuild_def h]

/-- ✓ The reference transition builder satisfies CORE-021: an instance carries the number of the
call that returned it, and two instances are the same exactly when their call numbers are
equal. -/
@[evidence holds CORE_021]
theorem CORE_021_reference : CORE_021 (refTransBuild (N := N) (A := A)) := by
  refine ⟨fun k k' i i' x y hk hx hy hs => ?_, fun k i x _ => rfl⟩
  have e : x.1.1 = y.1.1 := hs
  rw [core021_ref_call hx, core021_ref_call hy] at e
  exact hk e

end Reference

/-! ### Examples -/

/-- The example input: a transition named "Process" with one input arc on place 0 and the output
place 1. -/
def core021_exIn : TransIn Nat Unit :=
  { core := ⟨"Process", [⟨0, .one⟩], [], [], []⟩, out := some (.place 1) }

/-- A second input of the same name: one input arc on place 2 and the output place 3. -/
def core021_exIn₂ : TransIn Nat Unit :=
  { core := ⟨"Process", [⟨2, .one⟩], [], [], []⟩, out := some (.place 3) }

/-- Every call on the example input builds. -/
theorem core021_ex_builds (k : Nat) :
    ∃ x, (refTransBuild (N := Nat) (A := Unit)).build k core021_exIn = .ok x :=
  refTransBuild_succeeds.2 ⟨(refBuild_eq_none_iff _).1 (by decide), fun _ h => nomatch h⟩

/-- Every call on the second example input builds. -/
theorem core021_ex₂_builds (k : Nat) :
    ∃ x, (refTransBuild (N := Nat) (A := Unit)).build k core021_exIn₂ = .ok x :=
  refTransBuild_succeeds.2 ⟨(refBuild_eq_none_iff _).1 (by decide), fun _ h => nomatch h⟩

/-- ✓ Both lines of CORE-021 are exercised by the reference: calls 0 and 1 on the one input named
"Process" both build, their definitions are equal (so the two transitions share the name and
everything else), and the two transitions are not the same (line 1, AC1, the test derivation);
the first is the same as itself (line 2, AC2). -/
@[evidence nonvacuous CORE_021]
theorem CORE_021_nonvacuous :
    ∃ x y, (refTransBuild (N := Nat) (A := Unit)).build 0 core021_exIn = .ok x ∧
      (refTransBuild (N := Nat) (A := Unit)).build 1 core021_exIn = .ok y ∧
      ((refTransBuild (N := Nat) (A := Unit)).defOf x).core.name = "Process" ∧
      (refTransBuild (N := Nat) (A := Unit)).defOf x =
        (refTransBuild (N := Nat) (A := Unit)).defOf y ∧
      ¬ (refTransBuild (N := Nat) (A := Unit)).same x y ∧
      (refTransBuild (N := Nat) (A := Unit)).same x x := by
  obtain ⟨x, hx⟩ := core021_ex_builds 0
  obtain ⟨y, hy⟩ := core021_ex_builds 1
  have dx := refTransBuild_def hx
  have dy := refTransBuild_def hy
  refine ⟨x, y, hx, hy, ?_, ?_, ?_, rfl⟩
  · show x.1.2.core.name = _
    rw [dx]; rfl
  · show x.1.2 = y.1.2
    rw [dx, dy]
  · intro h
    have e : x.1.1 = y.1.1 := h
    rw [dx, dy] at e
    exact absurd e (by decide)

/-! ### Wrong builders -/

section Wrong

variable {N A : Type} [DecidableEq N] [ToString N]

/-- A builder whose equality compares definitions (structural equality, or a builder that hands
back one interned instance per definition), and is the reference otherwise. -/
def core021_structBuild : TBuilder N A :=
  { refTransBuild with same := fun x y => x.1.2 = y.1.2 }

/-- A builder whose equality compares names (identity by name), and is the reference
otherwise. -/
def core021_nameBuild : TBuilder N A :=
  { refTransBuild with same := fun x y => x.1.2.core.name = y.1.2.core.name }

/-- A builder whose equality is never true, and is the reference otherwise. -/
def core021_neverBuild : TBuilder N A :=
  { refTransBuild with same := fun _ _ => False }

end Wrong

/-- ✗ A builder whose equality compares definitions violates CORE-021 (line 1): calls 0 and 1 on
the one input named "Process" return equal transitions. -/
@[evidence forbids CORE_021]
theorem CORE_021_forbids_structural :
    ¬ CORE_021 (core021_structBuild (N := Nat) (A := Unit)) := by
  intro h
  obtain ⟨x, hx⟩ := core021_ex_builds 0
  obtain ⟨y, hy⟩ := core021_ex_builds 1
  refine h.1 0 1 core021_exIn core021_exIn x y (by decide) hx hy ?_
  show x.1.2 = y.1.2
  rw [refTransBuild_def hx, refTransBuild_def hy]

/-- A builder whose id counter wraps (a narrowed counter, here modulo 4), so calls `k` and `k + 4`
hand out the same id; equality compares ids. -/
def core021_wrapBuild : TBuilder Nat Unit where
  I := Nat × TransDef Nat Unit
  build := fun k i => .ok (k % 4, i.resolve)
  defOf := fun x => x.2
  same := fun x y => x.1 = y.1

/-- ✗ A wrapping id counter violates CORE-021 (line 1): calls 0 and 4 on the input named
"Process" return equal transitions, although line 2 holds. -/
@[evidence forbids CORE_021]
theorem CORE_021_forbids_wrap : ¬ CORE_021 core021_wrapBuild := fun h =>
  h.1 0 4 core021_exIn core021_exIn _ _ (by decide) rfl rfl rfl

/-- A builder that memoizes its instance per input (`this.built ??= new Transition(...)`), so the
instance is the input and equality compares inputs. -/
def core021_memoBuild : TBuilder Nat Unit where
  I := TransIn Nat Unit × Nat
  build := fun k i => .ok (i, k)
  defOf := fun x => x.1.resolve
  same := fun x y => x.1 = y.1

/-- The memoizing builder keeps the two different inputs named "Process" apart (the AC1 test
written with two builders passes on it). -/
theorem core021_memo_apart : ∀ x y, core021_memoBuild.build 0 core021_exIn = .ok x →
    core021_memoBuild.build 1 core021_exIn₂ = .ok y → ¬ core021_memoBuild.same x y := by
  intro x y hx hy hs
  cases hx; cases hy
  have e : core021_exIn.out = core021_exIn₂.out := congrArg TransIn.out hs
  simp [core021_exIn, core021_exIn₂] at e

/-- ✗ The memoizing builder violates CORE-021 (line 1 with one input): calls 0 and 1 on the one
input named "Process" return equal transitions. -/
@[evidence forbids CORE_021]
theorem CORE_021_forbids_memo : ¬ CORE_021 core021_memoBuild := fun h =>
  h.1 0 1 core021_exIn core021_exIn _ _ (by decide) rfl rfl rfl

/-! ### Mutant: line 1 read as identity by name -/

section MutantName

variable {N A : Type}

/-- Mutant reading of line 1, identity by name (ruling D10 read as the equality of transitions):
two transitions of different names are never equal. Line 2 is as in CORE-021. -/
def CORE_021_mutant_byName (B : TBuilder N A) : Prop :=
  (∀ k k' i i' x y, B.build k i = .ok x → B.build k' i' = .ok y →
    (B.defOf x).core.name ≠ (B.defOf y).core.name → ¬ B.same x y) ∧
  core021_line2 B

end MutantName

/-- The name builder kills the mutant: its equality holds exactly when the names agree, so it
meets the name reading, but calls 0 and 1 on the one input named "Process" return equal
transitions (line 1). -/
@[evidence mutant CORE_021]
theorem CORE_021_mutant_byName_killed :
    CORE_021_mutant_byName (core021_nameBuild (N := Nat) (A := Unit)) ∧
      ¬ CORE_021 (core021_nameBuild (N := Nat) (A := Unit)) := by
  refine ⟨⟨fun k k' i i' x y _ _ hn hs => hn hs, fun k i x _ => rfl⟩, fun h => ?_⟩
  obtain ⟨x, hx⟩ := core021_ex_builds 0
  obtain ⟨y, hy⟩ := core021_ex_builds 1
  refine h.1 0 1 core021_exIn core021_exIn x y (by decide) hx hy ?_
  show x.1.2.core.name = y.1.2.core.name
  rw [refTransBuild_def hx, refTransBuild_def hy]

/-! ### Mutant: the body sentence read literally (no transition equals any transition) -/

section MutantNever

variable {N A : Type}

/-- Mutant reading of line 2, the body sentence "Two transition instances are never equal" read
without AC2: no built transition is equal to any built transition, itself included. Line 1
follows from it. -/
def CORE_021_mutant_neverEqual (B : TBuilder N A) : Prop :=
  ∀ k k' i i' x y, B.build k i = .ok x → B.build k' i' = .ok y → ¬ B.same x y

end MutantNever

/-- The never-equal builder kills the mutant: no two of its transitions are equal, so it meets the
literal reading, but the transition call 0 returns on the example is not equal to itself
(line 2). -/
@[evidence mutant CORE_021]
theorem CORE_021_mutant_neverEqual_killed :
    CORE_021_mutant_neverEqual (core021_neverBuild (N := Nat) (A := Unit)) ∧
      ¬ CORE_021 (core021_neverBuild (N := Nat) (A := Unit)) := by
  refine ⟨fun _ _ _ _ _ _ _ _ hs => hs, fun h => ?_⟩
  obtain ⟨x, hx⟩ := core021_ex_builds 0
  exact h.2 0 core021_exIn x hx

/-! ### Which calls succeed: CORE-020 -/

/-- A builder that refuses a second build of a name (a global name registry) and compares names.
The model is stateless: call `k` on an input succeeds only when `k` is the call number the registry
reserves for the input's name (its length), and is the reference otherwise. So any two successful
calls with one name are one call. -/
def core021_registryBuild : TBuilder Nat Unit :=
  { refTransBuild (N := Nat) (A := Unit) with
    build := fun k i =>
      if k = i.core.name.length then (refTransBuild (N := Nat) (A := Unit)).build k i
      else .error "transition name already registered"
    same := fun x y => x.1.2.core.name = y.1.2.core.name }

/-- A successful call of the registry builder is the reserved call and keeps the input's name. -/
theorem core021_registry_build {k : Nat} {i : TransIn Nat Unit}
    {x : core021_registryBuild.I} (h : core021_registryBuild.build k i = .ok x) :
    k = i.core.name.length ∧ x.1.2.core.name = i.core.name := by
  by_cases hk : k = i.core.name.length
  · have h' : (refTransBuild (N := Nat) (A := Unit)).build k i = .ok x := by
      have : core021_registryBuild.build k i = (refTransBuild (N := Nat) (A := Unit)).build k i :=
        if_pos hk
      rw [← this]; exact h
    refine ⟨hk, ?_⟩
    rw [refTransBuild_def h']; rfl
  · have : core021_registryBuild.build k i = .error "transition name already registered" :=
      if_neg hk
    rw [this] at h; cases h

/-- ✓ CORE-021 alone allows the name-registry builder, whose equality is identity by name, and
CORE-020 rejects it: call 0 on the input named "Process" must build and does not. Line 1 bites on
two builds of one name only together with CORE-020's success line. -/
@[evidence allows CORE_021]
theorem CORE_021_allows_registry :
    CORE_021 core021_registryBuild ∧
      (∀ x y : core021_registryBuild.I,
        x.1.2.core.name = y.1.2.core.name → core021_registryBuild.same x y) ∧
      ¬ CORE_020 core021_registryBuild := by
  refine ⟨⟨fun k k' i i' x y hk hx hy hs => ?_, fun _ _ _ _ => rfl⟩, fun _ _ h => h, fun h => ?_⟩
  · obtain ⟨ek, nx⟩ := core021_registry_build hx
    obtain ⟨ek', ny⟩ := core021_registry_build hy
    have hs' : x.1.2.core.name = y.1.2.core.name := hs
    rw [nx, ny] at hs'
    exact hk (by rw [ek, ek', hs'])
  · have hr := ((CORE_020_reference (N := Nat) (A := Unit)).2.2.2 0 core021_exIn).1
      (core021_ex_builds 0)
    obtain ⟨x, hx⟩ := (h.2.2.2 0 core021_exIn).2 hr
    exact absurd (core021_registry_build hx).1 (by decide)

/-- CORE-020 and CORE-021 together rule out identity by name: for every builder meeting both, two
different calls on one input that builds with valid timing both succeed, return transitions of one
name, and the two are not equal. -/
theorem core021_with_020 {N A : Type} [DecidableEq N] (B : TBuilder N A)
    (h20 : CORE_020 B) (h21 : CORE_021 B) {i : TransIn N A}
    (hb : Builds i.toTrans ∧ ∀ tm, i.timing = some tm → tm.Valid) {k k' : Nat} (hk : k ≠ k') :
    ∃ x y, B.build k i = .ok x ∧ B.build k' i = .ok y ∧
      (B.defOf x).core.name = (B.defOf y).core.name ∧ ¬ B.same x y := by
  obtain ⟨x, hx⟩ := (h20.2.2.2 k i).2 hb
  obtain ⟨y, hy⟩ := (h20.2.2.2 k' i).2 hb
  refine ⟨x, y, hx, hy, ?_, h21.1 k k' i i x y hk hx hy⟩
  rw [(h20.1 k i x hx).1, (h20.1 k' i y hy).1]

/-! ### Two transitions of one name in one net -/

/-- The marking with one token on place 0 and one on place 2. -/
def core021_m0 : Nat → Nat := fun p => if p = 0 ∨ p = 2 then 1 else 0

/-- ✓ CORE-021 allows a net with two unequal transitions of one name, which lies outside the
D10 assumption: the reference builder satisfies CORE-021 and builds "Process" twice (calls 0 and
1, different arcs), the two transitions are not equal, the reference net builder accepts both,
the built net fails `NetNamesDistinct`, and from the marking with tokens on places 0 and 2 a step
labelled "Process" reaches two different markings (one deposits on place 1, the other on place
3). So the name labels a step only under the D10 assumption. -/
@[evidence allows CORE_021]
theorem CORE_021_allows_sameName :
    CORE_021 (refTransBuild (N := Nat) (A := Unit)) ∧
    ∃ x y, (refTransBuild (N := Nat) (A := Unit)).build 0 core021_exIn = .ok x ∧
      (refTransBuild (N := Nat) (A := Unit)).build 1 core021_exIn₂ = .ok y ∧
      ¬ (refTransBuild (N := Nat) (A := Unit)).same x y ∧
      ∃ b, refNetBuild (⟨[], [x, y], []⟩ : NetIn (refTransBuild (N := Nat) (A := Unit))) = .ok b ∧
        ¬ NetNamesDistinct b ∧
        ∃ m₁ m₂, LStep b.toNet "Process" core021_m0 m₁ ∧ LStep b.toNet "Process" core021_m0 m₂ ∧
          m₁ 1 ≠ m₂ 1 := by
  obtain ⟨x, hx⟩ := core021_ex_builds 0
  obtain ⟨y, hy⟩ := core021_ex₂_builds 1
  have dx := refTransBuild_def hx
  have dy := refTransBuild_def hy
  refine ⟨CORE_021_reference, x, y, hx, hy, ?_, _,
    refNetBuild_of_terminals_nil (B := refTransBuild (N := Nat) (A := Unit)) rfl, ?_, ?_⟩
  · intro h
    have e : x.1.1 = y.1.1 := h
    rw [dx, dy] at e
    exact absurd e (by decide)
  · intro hn
    have ht : (NetIn.collect (⟨[], [x, y], []⟩ :
        NetIn (refTransBuild (N := Nat) (A := Unit)))).trans =
        [core021_exIn.resolve, core021_exIn₂.resolve] := by
      show [x.1.2, y.1.2] = _
      rw [dx, dy]
    unfold NetNamesDistinct at hn
    rw [ht] at hn
    exact absurd hn (by decide)
  · have ht : (NetIn.collect (⟨[], [x, y], []⟩ :
        NetIn (refTransBuild (N := Nat) (A := Unit)))).toNet.transitions =
        [core021_exIn.resolve.toTrans, core021_exIn₂.resolve.toTrans] := by
      show [x.1.2.toTrans, y.1.2.toTrans] = _
      rw [dx, dy]
    refine ⟨fireNC core021_m0 core021_exIn.core (depProd [1]),
      fireNC core021_m0 core021_exIn₂.core (depProd [3]), ?_, ?_, by decide⟩
    · refine ⟨core021_exIn.resolve.toTrans, ?_, rfl, [1], ?_, ⟨.action 0, rfl⟩, rfl⟩
      · rw [ht]; exact List.mem_cons_self
      · decide
    · refine ⟨core021_exIn₂.resolve.toTrans, ?_, rfl, [3], ?_, ⟨.action 0, rfl⟩, rfl⟩
      · rw [ht]; exact List.mem_cons_of_mem _ List.mem_cons_self
      · decide

end Libpetri.Spec
