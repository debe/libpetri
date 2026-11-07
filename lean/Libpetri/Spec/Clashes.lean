import Libpetri.Spec.Consistency

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
  firings to the validating executor's.
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

/-- **Not the reference semantics.** An executor with CONC-026's option enabled: a transition
that builds fires from every marking at which it is enabled and deposits any write into its
output places, with the reference effect, whether or not the write is an output branch. A
transition that does not build is not held by any executor and never fires. Every reference
firing of a transition that builds is one of these firings (`CONC_026_scoped`). -/
def refFireSkipValidation {N : Type} [DecidableEq N] : FireRel N :=
  fun t m d m' => Builds t ∧ Enabled t m ∧ (∀ p, Produced d p → OutputArc t p) ∧
    m' = fireNC m t.core (depProd d)

/- The skip-validation firings are the witness model of CONC-026's `holds` theorem only. -/
#spec_witness refFireSkipValidation

requirement CONC_026
  id "CONC-026"
  title "Optional output validation skip (option enabled)"
  kind N
  scope "an executor that offers the option, with the option enabled"
  source verbatim "spec/05-concurrency.md"
  quote "*While* the option is enabled, the executor *shall* deposit the tokens an action wrote without validating them against the transition's output spec."
        "The skip covers the whole spec, its `Place` and `ForwardInput` leaves included: a transition whose output spec is a single leaf is not checked for a write to that place either."
        "While the option is enabled they do not apply: a firing that ends with its action deposits the action's write whether or not it equals an output branch."
        "The option skips nothing else."
        "A write to a place the transition does not declare as an output still fails ([CORE-063])."
        "The build-time checks of [IO-011], [IO-012], [IO-013] and [IO-014] run when the transition is built, before any executor exists, and no executor option reaches them."
        "When enabled, output tokens are deposited without validation."
  reading "For every transition t that builds, whatever its output spec (an And, an Xor, or a single Place or ForwardInput leaf), every marking m at which t is enabled and every deposit d that writes only output places of t:"
          "some firing of t from m deposits d."
          "Every firing of every transition deposits only in output places of the transition."
          "A transition that does not build never fires."
  assumes "The model is the firing relation F of one executor that has the option and has it enabled, each firing read as one step from a marking to a marking (glossary: Fire, Deposit); timing and priority play no part. The action may write any tokens into the transition's output places, so 'deposit the tokens an action wrote without validating them' is read as: every such write is the deposit of some firing (the first two lines). Deposits are compared per place (CORE-036), so several tokens in one place are one more such write."
          "'The skip covers the whole spec, its Place and ForwardInput leaves included' is why the first line ranges over every output spec: a transition whose output spec is Place(P) also fires with a write that misses P (CONC_026_forbids_leafValidated)."
          "'It also covers the join-relay check of [NU-054] and the multiplicity warning of [IO-016] AC4, both of which run as part of validation.': a correlation name and a diagnostic are below the token-count granularity of the firing semantics; not encoded."
          "The paragraph naming IO-010, IO-011, IO-012, the per-firing check of IO-015 and the last two firing lines of CORE-036 is a scope: those blocks describe an executor with output validation enabled (their scope strings say so), and this block describes the executor with the option enabled. Theorem CONC_026_scoped shows both hold at once, each of its own executor, and that every firing of the validating executor on a transition that builds is a firing of the skipping one."
          "'The option skips nothing else' and 'A write to a place the transition does not declare as an output still fails ([CORE-063])' are the third line: a write outside the output places is not the deposit of any firing."
          "'A firing that ends with the timeout outcome deposits what [IO-013] and [IO-014] say.' is those blocks' subject, over the relation of timed-out firings; it is not restated here. A timeout deposit writes only output places, so the first line covers it."
          "'The build-time checks ... no executor option reaches them' is the fourth line: a transition that does not build (glossary: Builds) is not a transition any executor holds, so it never fires, the option enabled or not."
          "The first sentence's MAY (whether an executor offers the option at all), 'for known-correct nets' and the performance sentence are not encoded: the block describes an executor that offers the option, with it enabled. The implementation notes are not normative."
          "AC1 (the option is opt-in, validation is on by default) is about the builder's default, not about the firing relation; not encoded."
          "AC2 (when enabled, output tokens are deposited without validation) is the first two lines."
          "AC3 (when disabled, validation behaves identically to the bitmap executor) is the plain firing relation's subject (IO-010 to IO-015); not encoded here."
          "AC4 (Place(P) writing nothing, And(A, B) writing only A, both deposited) is the first two lines; CONC_026_nonvacuous fires both under the witness."
          "AC5 (no NU-054 diagnostic, no IO-016 AC4 warning) is below the token-count granularity; not encoded."
          "AC6 (a write to an undeclared place still fails, and building a transition that IO-012 rejects still fails) is the third and fourth lines."
  signoff "pending"
  statement : ∀ {N : Type} [DecidableEq N], FireRel N → Prop :=
    fun F =>
      (∀ t, Builds t → ∀ m, Enabled t m → ∀ d, (∀ p, Produced d p → OutputArc t p) →
        ∃ m', F t m d m') ∧
      (∀ t d, on (fun m m' => F t m d m'), shall (fun _ _ => ∀ p, Produced d p → OutputArc t p)) ∧
      (∀ t, ¬ Builds t → ∀ m d m', ¬ F t m d m')

/-- ✓ CONC-026 holds of the skip-validation firings (`refFireSkipValidation`). -/
@[evidence holds CONC_026]
theorem CONC_026_skip {N : Type} [DecidableEq N] :
    CONC_026 (refFireSkipValidation (N := N)) :=
  ⟨fun _ hb _ hm _ hd => ⟨_, hb, hm, hd, rfl⟩, fun _ _ _ _ h => h.2.2.1,
    fun _ hb _ _ _ h => hb h.1⟩

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
  fun t m d m' => Builds t ∧ (RefFire t m d m' ∨
    (AndXorSpec t ∧ Enabled t m ∧ (∀ p, Produced d p → OutputArc t p) ∧
      m' = fireNC m t.core (depProd d)))

/-- ✗ An executor that still validates a single leaf violates CONC-026: the `Place(0)`
transition never completes with the empty write, which the skip deposits ("its `Place` and
`ForwardInput` leaves included", AC4). -/
@[evidence forbids CONC_026]
theorem CONC_026_forbids_leafValidated : ¬ CONC_026 clashSkipAndXorFire := by
  intro h
  obtain ⟨_, -, hf⟩ :=
    h.1 (clashT (.place 0)) clashT_builds.2 clashEmpty (clashT_enabled _) []
      (clash_writeNothing_outputs _)
  rcases hf with ⟨-, ⟨ch, hch⟩, -⟩ | ⟨⟨l, r, hlr⟩, -⟩
  · exact absurd (deposit_place_leaf _ 0 ch _ hch) (by simp)
  · simp [OutputSpec, clashT] at hlr

/-- An executor that also deposits writes into places the transition does not declare. -/
def clashUndeclaredFire : FireRel Nat :=
  fun t m d m' => Builds t ∧ Enabled t m ∧ m' = fireNC m t.core (depProd d)

/-- An executor that also fires transitions that do not build. -/
def clashUnbuiltFire : FireRel Nat :=
  fun t m d m' => Enabled t m ∧ (∀ p, Produced d p → OutputArc t p) ∧
    m' = fireNC m t.core (depProd d)

/-- The arc-less `Xor(Place(0), Place(0))` transition does not build ([IO-012]). -/
theorem clashT_dup_not_builds : ¬ Builds (clashT (.xor (.place 0) (.place 0))) := by decide

/-- ✗ An executor that deposits a write to an undeclared place violates CONC-026 (AC6): the
`And(Place(0), Place(1))` transition deposits `[2]`. -/
@[evidence forbids CONC_026]
theorem CONC_026_forbids_undeclared : ¬ CONC_026 clashUndeclaredFire := by
  intro h
  have := h.2.1 (clashT clashAnd01) [2] clashEmpty _ ⟨clashT_builds.1, clashT_enabled _, rfl⟩ 2
    (by simp [Produced])
  obtain ⟨o, ho, hp⟩ := this
  simp [clashT, clashAnd01] at ho
  subst ho
  simp [outPlaces] at hp

/-- ✗ An executor that fires a transition that does not build violates CONC-026 (AC6): the
`Xor(Place(0), Place(0))` transition, which [IO-012] rejects, fires. -/
@[evidence forbids CONC_026]
theorem CONC_026_forbids_unbuilt : ¬ CONC_026 clashUnbuiltFire := fun h =>
  h.2.2 _ clashT_dup_not_builds clashEmpty [] _
    ⟨clashT_enabled _, clash_writeNothing_outputs _, rfl⟩

/-- Mutant reading of CONC-026 without its first line: the option need not deposit anything the
validating executor would not. -/
def CONC_026_mutant_dropDeposits {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  (∀ t d, on (fun m m' => F t m d m'), shall (fun _ _ => ∀ p, Produced d p → OutputArc t p)) ∧
  (∀ t, ¬ Builds t → ∀ m d m', ¬ F t m d m')

/-- The reference firings of transitions that build kill the first mutant: they deposit only
output places and never fire a transition that does not build, but they validate. -/
@[evidence mutant CONC_026]
theorem CONC_026_mutant_dropDeposits_killed :
    CONC_026_mutant_dropDeposits (fun (t : Trans Nat) m d m' => Builds t ∧ RefFire t m d m') ∧
      ¬ CONC_026 (fun (t : Trans Nat) m d m' => Builds t ∧ RefFire t m d m') := by
  refine ⟨⟨fun _ _ _ _ h => refFire_outputs h.2, fun _ hb _ _ _ h => hb h.1⟩, fun h => ?_⟩
  obtain ⟨_, -, -, ⟨ch, hch⟩, -⟩ :=
    h.1 (clashT clashAnd01) clashT_builds.1 clashEmpty (clashT_enabled _) [0]
      clashAnd01_write0_outputs
  exact absurd (deposit_clashAnd01 _ ch _ hch) (by simp)

/-- Mutant reading of CONC-026 without its third line: the option also skips the output-place
check. -/
def CONC_026_mutant_dropUndeclared {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  (∀ t, Builds t → ∀ m, Enabled t m → ∀ d, (∀ p, Produced d p → OutputArc t p) →
    ∃ m', F t m d m') ∧
  (∀ t, ¬ Builds t → ∀ m d m', ¬ F t m d m')

/-- The undeclared-write executor kills the second mutant. -/
@[evidence mutant CONC_026]
theorem CONC_026_mutant_dropUndeclared_killed :
    CONC_026_mutant_dropUndeclared clashUndeclaredFire ∧ ¬ CONC_026 clashUndeclaredFire :=
  ⟨⟨fun _ hb _ hm _ _ => ⟨_, hb, hm, rfl⟩, fun _ hb _ _ _ h => hb h.1⟩,
    CONC_026_forbids_undeclared⟩

/-- Mutant reading of CONC-026 without its fourth line: the option also reaches the build-time
checks. -/
def CONC_026_mutant_dropBuild {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  (∀ t, Builds t → ∀ m, Enabled t m → ∀ d, (∀ p, Produced d p → OutputArc t p) →
    ∃ m', F t m d m') ∧
  (∀ t d, on (fun m m' => F t m d m'), shall (fun _ _ => ∀ p, Produced d p → OutputArc t p))

/-- The executor that fires unbuilt transitions kills the third mutant. -/
@[evidence mutant CONC_026]
theorem CONC_026_mutant_dropBuild_killed :
    CONC_026_mutant_dropBuild clashUnbuiltFire ∧ ¬ CONC_026 clashUnbuiltFire :=
  ⟨⟨fun _ _ _ hm _ hd => ⟨_, hm, hd, rfl⟩, fun _ _ _ _ h => h.2.1⟩, CONC_026_forbids_unbuilt⟩

/-- CONC-026 is exercised (AC4): under the skip-validation firings the `And(Place(0), Place(1))`
transition fires from the empty marking with the partial write `[0]`, and the `Place(0)`
transition with the empty write; neither write is an output branch. -/
@[evidence nonvacuous CONC_026]
theorem CONC_026_nonvacuous :
    (∃ m', refFireSkipValidation (clashT clashAnd01) clashEmpty [0] m') ∧
      ¬ OutputBranch (clashT clashAnd01) [0] ∧
      (∃ m', refFireSkipValidation (clashT (.place 0)) clashEmpty [] m') ∧
      ¬ OutputBranch (clashT (.place 0)) [] :=
  ⟨⟨_, clashT_builds.1, clashT_enabled _, clashAnd01_write0_outputs, rfl⟩,
   by simp [OutputBranch, clashT, clashAnd01, Out.branches, cross],
   ⟨_, clashT_builds.2, clashT_enabled _, clash_writeNothing_outputs _, rfl⟩,
   by simp [OutputBranch, clashT, Out.branches]⟩

/-- ✓ The validating blocks and the skip hold together, each of its own executor: IO-010,
IO-011 and IO-012 hold of the reference firings (output validation enabled), CONC-026 of the
skip-validation firings, and every reference firing of a transition that builds is a
skip-validation firing, so enabling the option only adds firings. -/
@[evidence consistent IO_010 IO_011 IO_012 CONC_026]
theorem CONC_026_scoped {N : Type} [DecidableEq N] [ToString N] :
    IO_010 (RefFire (N := N)) ∧ IO_011 refBuild (RefFire (N := N)) ∧
      IO_012 (IO_012_check (N := N)) refBuild (RefFire (N := N)) ∧
      CONC_026 (refFireSkipValidation (N := N)) ∧
      ∀ (t : Trans N) m d m', Builds t → RefFire t m d m' → refFireSkipValidation t m d m' :=
  ⟨IO_010_reference, IO_011_reference, IO_012_reference, CONC_026_skip,
    fun _ _ _ _ hb h => ⟨hb, h.1, refFire_outputs h, h.2.2⟩⟩

/-! ## IO-015 and CORE-036: a validated write is deposited -/

/-- The deposits of the validated-write executor: a reference deposit, or any write the
reference validator accepts (`ioRefValidate`: exactly one assignment claims its produced set). -/
def validatedDep {N : Type} [DecidableEq N] (t : Trans N) (m : N → Nat) (d : List N) : Prop :=
  core036_refDep t m d ∨ ∃ o, OutputSpec t = some o ∧ ioRefValidate o d = true

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
  quote "*If* exactly one assignment claims a set *equal* to the produced set, *then* validation *shall* succeed."
        "The comparison is over **sets of places**: a spec names places, not counts, so an action that deposits several tokens into one claimed place conforms."
  reading "For every transition t with output spec o, every marking m at which t is enabled and every deposit d such that exactly one assignment of o claims exactly the produced set of d:"
          "some firing of t from m deposits d."
  assumes "The firing-level reading of the IO-015 sentences quoted: the block IO_015 fixes the validator's verdict; this one ties the verdict to firings. An action may write any tokens (glossary: Deposit), a completion that passes validation deposits what the action wrote, and one that fails is not a firing (glossary: Fire). So every write that validation accepts is the deposit of some firing. 'Conforms' is read as 'passes validation and is deposited', as IO-016 AC4 says of such a write ('the tokens are deposited regardless')."
          "Timing and priority play no part: whether the action completes within a Timeout budget is nondeterministic (IO-013), so a validated write is always one way a firing can end."
          "CORE-036 compares deposits per place and asks only that the places a firing deposits in be the places of one output branch, each receiving one or more tokens, so it allows such a deposit: both blocks hold of the validated-write executor (theorem CORE_036_IO_015_firing_consistent)."
  signoff "pending"
  statement : ∀ {N : Type} [DecidableEq N], FireRel N → Prop :=
    fun F => ∀ t o, OutputSpec t = some o → ∀ m, Enabled t m → ∀ d,
      (∃ i, ExactAssignment o d i ∧ ∀ j, ExactAssignment o d j → j = i) → ∃ m', F t m d m'

/-- ✓ `IO_015_firing` holds of the validated-write firings (`refFireValidated`): a write with
exactly one exact assignment passes the reference validator (`IO_015_reference`). -/
@[evidence holds IO_015_firing]
theorem IO_015_firing_validated {N : Type} [DecidableEq N] :
    IO_015_firing (refFireValidated (N := N)) :=
  fun _ o ht _ hm d ⟨i, hi, hu⟩ =>
    ⟨_, hm, Or.inr ⟨o, ht, (IO_015_reference (N := N)).1 o d i hi hu⟩, rfl⟩

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
    h (clashT (.place 0)) (.place 0) rfl clashEmpty (clashT_enabled _) [0, 0] place0_twice_unique
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
    (ho : OutputSpec t = some o) (hv : ioRefValidate o d = true) :
    ∃ b, OutputBranch t b ∧ OnPlacesOf d b := by
  have hc : o.branches.countP (sameSetB · d) = 1 := by
    simpa [ioRefValidate] using hv
  obtain ⟨b, hb, hs⟩ := List.countP_pos_iff.1 (by omega : 0 < o.branches.countP (sameSetB · d))
  refine ⟨b, ?_, fun p => ((sameSetB_iff b d).1 hs p).symm⟩
  have ho' : t.out = some o := ho
  simp only [OutputBranch, ho']
  exact hb

/-- The validated-write firings satisfy CORE-036's outcome line. -/
theorem validatedDep_outcome {N : Type} [DecidableEq N] (t : Trans N) (m : N → Nat)
    (d : List N) (h : validatedDep t m d) : core036_outcome t (Consumes t m) d := by
  rcases h with h | ⟨o, ho, hv⟩
  · exact core036_ref_c8 t m d h
  · exact .inl (validated_outcome ho hv)

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
