import Libpetri.Spec.Consistency
import Libpetri.Spec.Text.IO_015
import Libpetri.Spec.Text.CONC_026

set_option linter.missingDocs true

/-!
# Scoped blocks: the validation skip and the validated write

Two blocks sit beside the CORE and IO blocks and are checked against witnesses that are not the
reference semantics, because each describes an executor that differs from it in one way:

* `CONC_026`: an executor with CONC-026's output-validation skip enabled deposits whatever the
  action wrote into the transition's output places, whatever its output spec, single leaves
  included. IO-010, IO-011, IO-012 and the per-firing check of IO-015 are requirements on an
  executor with output validation enabled, so they and CONC-026 constrain different executors:
  `CONC_026_scoped` shows that each holds of its own executor and that the skip only adds
  firings to the validating executor's, and `CONC_026_core036` that CORE-036's firing lines
  other than the outcome line keep holding with the skip.
* `IO_015_firing`: an executor that validates deposits every write validation accepts, several
  tokens in one claimed place included. CORE-036 compares deposits per place and asks only that
  the deposited places be the places of one output branch, so both blocks hold of that executor
  (`CORE_036_IO_015_firing_consistent`).

Each block quotes the markdown verbatim and is checked like any other block (a witness, a
negative example, a non-vacuity theorem). Their witnesses are **not** the reference semantics:
each docstring says in which one way it differs.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## Shared examples -/

/-- The marking of the examples in which every place is empty. -/
def clashEmpty : Nat → Nat := fun _ => 0

/-- An arc-less transition with output spec `o`: it is enabled at every marking. -/
def clashT (o : Out Nat) : Trans Nat :=
  { core := { name := "t", inputs := [], inhibitors := [], reads := [], resets := [] },
    out := some o }

/-- The output spec `And(Place(0), Place(1))`. -/
def clashAnd01 : Out Nat := .and (.place 0) (.place 1)

/-- An arc-less transition is enabled at the empty marking. -/
theorem clashT_enabled (o : Out Nat) : Enabled (clashT o) clashEmpty := by
  simp [Enabled, enabledNA, clashT]

/-- Every reference deposit of `And(Place(0), Place(1))` is `[0, 1]`. -/
theorem deposit_clashAnd01 (k : Nat → Nat) (ch : Novel.ForwardDeposit.Choice) (d : List Nat)
    (h : deposit k (some clashAnd01) ch = some d) : d = [0, 1] := by
  cases ch with
  | action i =>
    cases i with
    | zero => simpa [deposit, clashAnd01, Out.branches, cross] using h.symm
    | succ i => simp [deposit, clashAnd01, Out.branches, cross] at h
  | timedOut j => simp [deposit, clashAnd01, Out.findTimeout] at h

/-! ## CONC-026: the validation skip -/

/-- The deposits of the skip-validation executor: any write into the transition's output
places. -/
def skipDep {N : Type} [DecidableEq N] (t : Trans N) (_m : N → Nat) (d : List N) : Prop :=
  ∀ p, Produced d p → OutputArc t p

/-- **Not the reference semantics.** An executor with CONC-026's option enabled: a transition
fires from every marking at which it is enabled and deposits any write into its output places,
with the reference effect, whether or not the write is an output branch. Like the reference
firing relation it ranges over every transition; which transitions build is the builder's
(`refBuild`), not the firing relation's. Every reference firing is one of these firings
(`CONC_026_scoped`). -/
def refFireSkipValidation {N : Type} [DecidableEq N] : FireRel N :=
  core036_model Enabled skipDep (·.core)

/- The skip-validation firings are the witness model of CONC-026's `holds` theorem only. -/
#spec_witness refFireSkipValidation

requirement CONC_026
  id "CONC-026"
  title "Optional output validation skip (option enabled)"
  kind N
  scope "an executor that offers the option, with the option enabled"
  source verbatim "spec/05-concurrency.md"
  covers CONC_026.s1, CONC_026.s2, CONC_026.s3, CONC_026.s4, CONC_026.s5, CONC_026.s6, CONC_026.s7
  reading "For every transition t that builds, whatever its output spec (an And, an Xor, or a single Place or ForwardInput leaf), every marking m at which t is enabled and every deposit d that writes only output places of t:"
          "some firing of t from m deposits d."
          "Every firing of every transition deposits only in output places of the transition."
  assumes "The model is the firing relation F of one executor that has the option and has it enabled, each firing read as one step from a marking to a marking (glossary: Fire, Deposit); timing and priority play no part. The action may write any tokens into the transition's output places, so 'deposit the tokens an action wrote without validating them' is read as: every such write is the deposit of some firing (the first two lines). Deposits are compared per place (CORE-036), so several tokens in one place are one more such write."
          "'The skip covers the whole spec, its Place and ForwardInput leaves included' is why the first line ranges over every output spec: a transition whose output spec is Place(P) also fires with a write that misses P (CONC_026_forbids_leafValidated)."
          "'It also covers the join-relay check of [NU-054] and the multiplicity warning of [IO-016] AC4, both of which run as part of validation.': a correlation name and a diagnostic are below the token-count granularity of the firing semantics; not encoded."
          "The paragraph naming IO-010, IO-011, IO-012, the per-firing check of IO-015 and the last two firing lines of CORE-036 is a scope: those blocks describe an executor with output validation enabled (their scope strings say so), and this block describes the executor with the option enabled. Theorem CONC_026_scoped shows both hold at once, each of its own executor, and that every firing of the validating executor is a firing of the skipping one."
          "'The option skips nothing else' and 'A write to a place the transition does not declare as an output still fails ([CORE-063])' are the third line: a write outside the output places is not the deposit of any firing. 'Skips nothing else' also keeps CORE-036's firing lines other than the outcome line for the skip executor (the token requirements of input, read and inhibitor arcs, that an enabled transition can fire, and the effect on every place): theorem CONC_026_core036 shows that CORE-036's lines 1 to 7 and this block hold together of the witness."
          "'A firing that ends with the timeout outcome deposits what [IO-013] and [IO-014] say.' is those blocks' subject, over the relation of timed-out firings; it is not restated here. A timeout deposit writes only output places, so the first line covers it."
          "'The build-time checks of [IO-011], [IO-012], [IO-013] and [IO-014] run when the transition is built, before any executor exists, and no executor option reaches them' is about the builder, not the firing relation, and no line of this block encodes it. In the model the builder is a function of the transition alone (Build in IO_011 to IO_014, witness refBuild): it takes no executor and no option, so no option reaches it, and its checks are the build lines of IO_011 to IO_014, which hold of refBuild (CONC_026_scoped states IO_011 and IO_012 over refBuild beside this block). A firing relation ranges over every transition, as CORE-036's does; the first line asks firings only of a transition that builds (glossary: Builds), the transitions an executor holds, and the block says nothing of firings of a transition that does not build."
          "The first sentence's MAY (whether an executor offers the option at all), 'for known-correct nets' and the performance sentence are not encoded: the block describes an executor that offers the option, with it enabled. The implementation notes are not normative."
          "AC1 (the option is opt-in, validation is on by default) is about the builder's default, not about the firing relation; not encoded."
          "AC2 (when enabled, output tokens are deposited without validation) is the first two lines."
          "AC3 (when disabled, validation behaves identically to the bitmap executor) is the plain firing relation's subject (IO-010 to IO-015); not encoded here."
          "AC4 (Place(P) writing nothing, And(A, B) writing only A, both deposited) is the first two lines; CONC_026_nonvacuous fires both under the witness."
          "AC5 (no NU-054 diagnostic, no IO-016 AC4 warning) is below the token-count granularity; not encoded."
          "AC6: 'a write to an undeclared place still fails' is the third line; 'building a transition whose output spec [IO-012] rejects still fails' is the builder's, IO_012's build line over refBuild, as the build-time paragraph above says."
  signoff "2026-11-13 fe6b6d06d66e8eb7 ai"
  statement : ∀ {N : Type} [DecidableEq N], FireRel N → Prop :=
    fun F =>
      (∀ t, Builds t → ∀ m, Enabled t m → ∀ d, (∀ p, Produced d p → OutputArc t p) →
        ∃ m', F t m d m') ∧
      (∀ t d, on (fun m m' => F t m d m'), shall (fun _ _ => ∀ p, Produced d p → OutputArc t p))

/-- ✓ CONC-026 holds of the skip-validation firings (`refFireSkipValidation`). -/
@[evidence holds CONC_026]
theorem CONC_026_skip {N : Type} [DecidableEq N] :
    CONC_026 (refFireSkipValidation (N := N)) :=
  ⟨fun _ _ _ hm _ hd => ⟨_, hm, hd, rfl⟩, fun _ _ _ _ h => h.2.1⟩

/-- The write `[0]` of the `And(Place(0), Place(1))` transition names only output places. -/
theorem clashAnd01_write0_outputs : ∀ p, Produced [0] p → OutputArc (clashT clashAnd01) p := by
  intro p hp
  have : p = 0 := List.mem_singleton.mp hp
  subst this
  exact ⟨_, rfl, by simp [clashAnd01, outPlaces]⟩

/-- The empty write names only output places. -/
theorem clash_writeNothing_outputs (o : Out Nat) : ∀ p, Produced [] p → OutputArc (clashT o) p :=
  fun _ h => absurd h (List.not_mem_nil)

/-- The arc-less `And(Place(0), Place(1))` and `Place(0)` transitions build. -/
theorem clashT_builds : Builds (clashT clashAnd01) ∧ Builds (clashT (.place 0)) := by decide

/-- ✗ The reference semantics, which validates, is not an executor with the option enabled: the
`And(Place(0), Place(1))` transition never deposits the partial write `[0]`. -/
@[evidence forbids CONC_026]
theorem CONC_026_forbids_reference : ¬ CONC_026 (RefFire (N := Nat)) := by
  intro h
  obtain ⟨_, -, ⟨ch, hch⟩, -⟩ :=
    h.1 (clashT clashAnd01) clashT_builds.1 clashEmpty (clashT_enabled _) [0]
      clashAnd01_write0_outputs
  exact absurd (deposit_clashAnd01 _ ch _ hch) (by simp)

/-- The output spec of `t` is an `And` or an `Xor` node. -/
def AndXorSpec {N : Type} (t : Trans N) : Prop :=
  ∃ l r, OutputSpec t = some (.and l r) ∨ OutputSpec t = some (.xor l r)

/-- An executor that skips validation of `And` and `Xor` specs only and still validates a
single leaf: the reference firings, plus, for an `And` or `Xor` spec, every write into the
output places. -/
def clashSkipAndXorFire : FireRel Nat :=
  fun t m d m' => RefFire t m d m' ∨
    (AndXorSpec t ∧ Enabled t m ∧ (∀ p, Produced d p → OutputArc t p) ∧
      m' = fireNC m t.core (depProd d))

/-- ✗ An executor that still validates a single leaf violates CONC-026: the `Place(0)`
transition never completes with the empty write, which the skip deposits ("its `Place` and
`ForwardInput` leaves included", AC4). -/
@[evidence forbids CONC_026]
theorem CONC_026_forbids_leafValidated : ¬ CONC_026 clashSkipAndXorFire := by
  intro h
  obtain ⟨_, hf⟩ :=
    h.1 (clashT (.place 0)) clashT_builds.2 clashEmpty (clashT_enabled _) []
      (clash_writeNothing_outputs _)
  rcases hf with ⟨-, ⟨ch, hch⟩, -⟩ | ⟨⟨l, r, hlr⟩, -⟩
  · exact absurd (deposit_place_leaf _ 0 ch _ hch) (by simp)
  · simp [OutputSpec, clashT] at hlr

/-- An executor that also deposits writes into places the transition does not declare. -/
def clashUndeclaredFire : FireRel Nat :=
  fun t m d m' => Enabled t m ∧ m' = fireNC m t.core (depProd d)

/-- ✗ An executor that deposits a write to an undeclared place violates CONC-026 (AC6): the
`And(Place(0), Place(1))` transition deposits `[2]`. -/
@[evidence forbids CONC_026]
theorem CONC_026_forbids_undeclared : ¬ CONC_026 clashUndeclaredFire := by
  intro h
  have := h.2 (clashT clashAnd01) [2] clashEmpty _ ⟨clashT_enabled _, rfl⟩ 2
    (by simp [Produced])
  obtain ⟨o, ho, hp⟩ := this
  simp [clashT, clashAnd01] at ho
  subst ho
  simp [outPlaces] at hp

/-- Mutant reading of CONC-026 without its first line: the option need not deposit anything the
validating executor would not. -/
def CONC_026_mutant_dropDeposits {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t d, on (fun m m' => F t m d m'), shall (fun _ _ => ∀ p, Produced d p → OutputArc t p)

/-- The reference firings kill the first mutant: they deposit only output places, but they
validate. -/
@[evidence mutant CONC_026]
theorem CONC_026_mutant_dropDeposits_killed :
    CONC_026_mutant_dropDeposits (RefFire (N := Nat)) ∧ ¬ CONC_026 (RefFire (N := Nat)) :=
  ⟨fun _ _ _ _ h => refFire_outputs h, CONC_026_forbids_reference⟩

/-- Mutant reading of CONC-026 without its third line: the option also skips the output-place
check. -/
def CONC_026_mutant_dropUndeclared {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t, Builds t → ∀ m, Enabled t m → ∀ d, (∀ p, Produced d p → OutputArc t p) →
    ∃ m', F t m d m'

/-- The undeclared-write executor kills the second mutant. -/
@[evidence mutant CONC_026]
theorem CONC_026_mutant_dropUndeclared_killed :
    CONC_026_mutant_dropUndeclared clashUndeclaredFire ∧ ¬ CONC_026 clashUndeclaredFire :=
  ⟨fun _ _ _ hm _ _ => ⟨_, hm, rfl⟩, CONC_026_forbids_undeclared⟩

/-- CONC-026 is exercised (AC4): under the skip-validation firings the `And(Place(0), Place(1))`
transition fires from the empty marking with the partial write `[0]`, and the `Place(0)`
transition with the empty write; neither write is an output branch. -/
@[evidence nonvacuous CONC_026]
theorem CONC_026_nonvacuous :
    (∃ m', refFireSkipValidation (clashT clashAnd01) clashEmpty [0] m') ∧
      ¬ OutputBranch (clashT clashAnd01) [0] ∧
      (∃ m', refFireSkipValidation (clashT (.place 0)) clashEmpty [] m') ∧
      ¬ OutputBranch (clashT (.place 0)) [] :=
  ⟨⟨_, clashT_enabled _, clashAnd01_write0_outputs, rfl⟩,
   by simp [OutputBranch, clashT, clashAnd01, Out.branches, cross],
   ⟨_, clashT_enabled _, clash_writeNothing_outputs _, rfl⟩,
   by simp [OutputBranch, clashT, Out.branches]⟩

/-- ✓ The validating blocks and the skip hold together, each of its own executor: IO-010,
IO-011 and IO-012 hold of the reference firings (output validation enabled) and the reference
builder, CONC-026 of the skip-validation firings, and every reference firing is a
skip-validation firing, so enabling the option only adds firings. -/
@[evidence consistent IO_010 IO_011 IO_012 CONC_026]
theorem CONC_026_scoped {N : Type} [DecidableEq N] [ToString N] :
    IO_010 (RefFire (N := N)) ∧ IO_011 refBuild (RefFire (N := N)) ∧
      IO_012 (IO_012_check (N := N)) refBuild (RefFire (N := N)) ∧
      CONC_026 (refFireSkipValidation (N := N)) ∧
      ∀ (t : Trans N) m d m', RefFire t m d m' → refFireSkipValidation t m d m' :=
  ⟨IO_010_reference, IO_011_reference, IO_012_reference, CONC_026_skip,
    fun _ _ _ _ h => ⟨h.1, refFire_outputs h, h.2.2⟩⟩

/-- ✓ The option skips nothing else: CORE-036's lines 1 to 7 (the token requirements of input,
read and inhibitor arcs, that an enabled transition can fire, and the effect of a firing on
input, other and reset places) hold of the skip-validation firings together with CONC-026. Only
CORE-036's outcome line, which CONC-026 sets aside while the option is enabled, is not asked. -/
theorem CONC_026_core036 {N : Type} [DecidableEq N] :
    (∀ t : Trans N,
      core036_c1 refFireSkipValidation t ∧ core036_c2 refFireSkipValidation t ∧
      core036_c3 refFireSkipValidation t ∧ core036_c4 refFireSkipValidation t ∧
      core036_c5 refFireSkipValidation t ∧ core036_c6 refFireSkipValidation t ∧
      core036_c7 refFireSkipValidation t) ∧
    CONC_026 (refFireSkipValidation (N := N)) :=
  ⟨fun t => ⟨core036_c1_of (fun t m h => ((core036_enabled_iff t m).1 h).1) t,
    core036_c2_of (fun t m h => ((core036_enabled_iff t m).1 h).2.2) t,
    core036_c3_of (fun t m h => ((core036_enabled_iff t m).1 h).2.1) t,
    core036_c4_of (fun _ _ h => h) (fun _ _ => ⟨[], fun _ h => absurd h List.not_mem_nil⟩) t,
    core036_c5_of core036_ref_c5 t, core036_c6_of core036_ref_c6 t,
    core036_c7_of (fun _ _ h => h) t⟩, CONC_026_skip⟩

/-! ## IO-015 and CORE-036: a validated write is deposited -/

/-- The deposits of the validated-write executor: a reference deposit, or any write in the
places the output spec names that the reference validator accepts (`ioRefValidate`: exactly one
assignment claims its produced set). A token in a place the spec never names is CORE-072's
subject, not this executor's. -/
def validatedDep {N : Type} [DecidableEq N] (t : Trans N) (m : N → Nat) (d : List N) : Prop :=
  core036_refDep t m d ∨
    ∃ o, OutputSpec t = some o ∧ ioRefValidate o d = true ∧ ∀ q ∈ d, q ∈ outPlaces o

/-- **Not the reference semantics.** The reference firings, plus every write the reference
validator accepts, deposited as written with the reference effect. It is the executor IO-015
describes, which deposits several tokens in one claimed place when the action writes them. -/
def refFireValidated {N : Type} [DecidableEq N] : FireRel N :=
  core036_model Enabled validatedDep (·.core)

/- The validated-write firings are the witness model of `IO_015_firing`'s `holds` theorem and of
the consistency of CORE-036 with it. -/
#spec_witness refFireValidated

requirement IO_015_firing
  id "IO-015"
  title "Output validation: a validated write is deposited"
  kind B
  scope "executors with output validation enabled (the default, CONC-026)"
  source verbatim "spec/02-input-output-specs.md"
  covers IO_015.s4, IO_015.s8
  reading "For every transition t that builds, with output spec o, every marking m at which t is enabled and every deposit d such that exactly one assignment of o claims exactly the produced set of d:"
          "some firing of t from m deposits d."
  assumes "The firing-level reading of the IO-015 sentences quoted: the block IO_015 fixes the validator's verdict; this one ties the verdict to firings. An action may write any tokens (glossary: Deposit), a completion that passes validation deposits what the action wrote, and one that fails is not a firing (glossary: Fire). So every write that validation accepts is the deposit of some firing. 'Conforms' is read as 'passes validation and is deposited', as IO-016 AC4 says of such a write ('the tokens are deposited regardless')."
          "Timing and priority play no part: whether the action completes within a Timeout budget is nondeterministic (IO-013), so a validated write is always one way a firing can end."
          "The block asks firings only of a transition that builds (glossary: Builds): a transition the build-time checks reject (CORE-022, IO-011 to IO-014) is held by no executor, since every runtime rejects its definition when the net is built, so no firing of it is asked. The firing relation itself ranges over every transition, as CORE-036's does: the witness refFireValidated fires unbuilt transitions too, and a validating executor that holds only transitions that build satisfies the block as well (IO_015_firing_builtOnly)."
          "CORE-036 compares deposits per place and asks only that the places a firing deposits in be the places of one output branch, each receiving one or more tokens, so it allows such a deposit: both blocks hold of the validated-write executor (theorem CORE_036_IO_015_firing_consistent)."
  signoff "2026-11-13 2218d01fbc44b335 ai"
  statement : ∀ {N : Type} [DecidableEq N], FireRel N → Prop :=
    fun F => ∀ t, Builds t → ∀ o, OutputSpec t = some o → ∀ m, Enabled t m → ∀ d,
      (∃ i, ExactAssignment o d i ∧ ∀ j, ExactAssignment o d j → j = i) → ∃ m', F t m d m'

/-- ✓ `IO_015_firing` holds of the validated-write firings (`refFireValidated`): a write with
exactly one exact assignment lies in the places the output spec names and passes the reference
validator (`ioRefValidate_of_exact`). -/
@[evidence holds IO_015_firing]
theorem IO_015_firing_validated {N : Type} [DecidableEq N] :
    IO_015_firing (refFireValidated (N := N)) :=
  fun _ _ o ht _ hm _ ⟨_, hi, hu⟩ =>
    ⟨_, hm, Or.inr ⟨o, ht, ioRefValidate_of_exact hi hu⟩, rfl⟩

/-- `IO_015_firing` also holds of a validating executor that holds only transitions that build:
the block asks nothing of a transition that does not build. -/
theorem IO_015_firing_builtOnly {N : Type} [DecidableEq N] :
    IO_015_firing (fun (t : Trans N) m d m' => Builds t ∧ refFireValidated t m d m') :=
  fun t hb o ht m hm d hu => by
    obtain ⟨m', hf⟩ := IO_015_firing_validated t hb o ht m hm d hu
    exact ⟨m', hb, hf⟩

/-- The write `[0, 0]` (two tokens in place `0`) has exactly one exact assignment of
`Place(0)`: assignment `0`, claiming `{0}`. -/
theorem place0_twice_unique :
    ∃ i, ExactAssignment (Out.place 0) [0, 0] i ∧
      ∀ j, ExactAssignment (Out.place 0) [0, 0] j → j = i := by
  refine ⟨0, ⟨[0], rfl, fun q => by simp [Produced]⟩, fun j ⟨b, hb, _⟩ => ?_⟩
  cases j with
  | zero => rfl
  | succ j => simp [Out.branches] at hb

/-- ✗ The reference semantics deposits exactly one token per claimed place, so the leaf
`Place(0)` never deposits the validated write `[0, 0]`. -/
@[evidence forbids IO_015_firing]
theorem IO_015_firing_forbids_reference : ¬ IO_015_firing (RefFire (N := Nat)) := by
  intro h
  obtain ⟨_, -, ⟨ch, hch⟩, -⟩ :=
    h (clashT (.place 0)) clashT_builds.2 (.place 0) rfl clashEmpty (clashT_enabled _) [0, 0]
      place0_twice_unique
  exact absurd (deposit_place_leaf _ 0 ch _ hch) (by simp)

/-- `IO_015_firing` is exercised: the reference validator accepts `[0, 0]` for `Place(0)`, the
validated-write firings fire it from the empty marking, and it is not an output branch. -/
@[evidence nonvacuous IO_015_firing]
theorem IO_015_firing_nonvacuous :
    ioRefValidate (Out.place 0) [0, 0] = true ∧
      (∃ m', refFireValidated (clashT (.place 0)) clashEmpty [0, 0] m') ∧
      ¬ OutputBranch (clashT (.place 0)) [0, 0] :=
  ⟨by decide, ⟨_, clashT_enabled _, Or.inr ⟨_, rfl, by decide⟩, rfl⟩,
   by simp [OutputBranch, clashT, Out.branches]⟩

/-- A write the reference validator accepts marks exactly the places of one output branch. -/
theorem validated_outcome {N : Type} [DecidableEq N] {t : Trans N} {o : Out N} {d : List N}
    (ho : OutputSpec t = some o) (hv : ioRefValidate o d = true)
    (hd : ∀ q ∈ d, q ∈ outPlaces o) :
    ∃ b, OutputBranch t b ∧ OnPlacesOf d b := by
  have hc : o.branches.countP (sameSetB · d) = 1 := by
    rw [ioRefValidate_of_named hd] at hv
    simpa using hv
  obtain ⟨b, hb, hs⟩ := List.countP_pos_iff.1 (by omega : 0 < o.branches.countP (sameSetB · d))
  refine ⟨b, ?_, fun p => ((sameSetB_iff b d).1 hs p).symm⟩
  have ho' : t.out = some o := ho
  simp only [OutputBranch, ho']
  exact hb

/-- The validated-write firings satisfy CORE-036's outcome line. -/
theorem validatedDep_outcome {N : Type} [DecidableEq N] (t : Trans N) (m : N → Nat)
    (d : List N) (h : validatedDep t m d) : core036_outcome t (Consumes t m) d := by
  rcases h with h | ⟨o, ho, hv, hd⟩
  · exact core036_ref_c8 t m d h
  · exact .inl (validated_outcome ho hv hd)

/-- ✓ CORE-036 and `IO_015_firing` hold together: the validated-write firings satisfy both. They
are the reference firings with more deposits, and every extra deposit marks exactly the places
of one output branch, which is what CORE-036's outcome line asks of a firing that ends with its
action. -/
@[evidence consistent CORE_036 IO_015_firing]
theorem CORE_036_IO_015_firing_consistent {N : Type} [DecidableEq N] :
    CORE_036 (refFireValidated (N := N)) ∧ IO_015_firing (refFireValidated (N := N)) := by
  refine ⟨fun t => ⟨core036_c1_of (fun t m h => ((core036_enabled_iff t m).1 h).1) t,
    core036_c2_of (fun t m h => ((core036_enabled_iff t m).1 h).2.2) t,
    core036_c3_of (fun t m h => ((core036_enabled_iff t m).1 h).2.1) t,
    core036_c4_of (fun _ _ h => h) (fun t m => ?_) t,
    core036_c5_of core036_ref_c5 t, core036_c6_of core036_ref_c6 t,
    core036_c7_of (fun _ _ h => h) t, core036_c8_of validatedDep_outcome t⟩,
    IO_015_firing_validated⟩
  obtain ⟨d, hd⟩ := core036_ref_dep t m
  exact ⟨d, .inl hd⟩

end Libpetri.Spec
