import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryBuild

set_option linter.missingDocs true

/-!
# CORE-020: Transition definition (`spec/01-core-model.md`)

CORE-020 is a pure-function requirement (kind F) over an abstract transition builder
`B : TBuilder N A` (`Reference/Build.lean`): the `k`-th build call on an input `i` (`TransIn`:
name and arcs, an output specification if any, and optionally a timing, a priority and an action)
either fails or returns an instance whose definition (`TransDef`) has every field resolved. The
statement says what the definition carries and when a build call succeeds; it says nothing about
identity (CORE-021) or about what an action does (CORE-050, W3).

The witness is the reference transition builder `refTransBuild`: `refBuild`'s arc and
output-spec checks, then TIME-001's reference factory on a timing written out without a factory.
Wrong builders are killed: one that drops a given priority, one that keeps only the first input
arc, one that drops a repeated read arc, and one per line that satisfies a plausible wrong reading of that line (arc lists compared
without order, a timing kept only up to its interval, any fixed default priority, and the first
draft's line 4, which ignores the timing and contradicts TIME-001).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Novel.TimedScg (Timing maxDurationMs)

/-! ## CORE-020: Transition Definition -/

requirement CORE_020
  id "CORE-020"
  title "Transition Definition"
  kind F
  scope "all transition builders"
  source verbatim "spec/01-core-model.md"
  quote "*When* a transition is built, the built transition *shall* carry the name and the output specification it was given, if any, and each of its input, inhibitor, read and reset arc lists exactly as given, in the order given and with its repetitions."
        "*When* a transition is built with a timing, a priority or an action, the built transition *shall* carry that timing, priority or action."
        "*When* a transition is built without a priority, the built transition *shall* have priority 0."
        "Building a transition that has no match specification ([NU-020]) *shall* succeed exactly when its arcs and output specification pass the build-time checks and the timing it is given, if any, is valid ([TIME-001])."
  reading "For every transition builder B, every call number k and every input i:"
          "if call k on i returns an instance x, the definition of x has i's name and its input, inhibitor, read and reset arc lists exactly as i has them (as lists: order and repetitions kept), and i's output specification (or none, as i);"
          "if call k on i returns x, a timing, a priority or an action given in i is the one the definition of x carries;"
          "if call k on i returns x and i gives no priority, the definition of x has priority 0;"
          "call k on i returns an instance exactly when i's arcs and output specification build (Builds in Spec/Glossary.lean: the build-time checks of spec/glossary.md without the timing check) and a timing given in i is valid (Timing.Valid, TIME-001's validity table), whatever k is."
  assumes "A transition builder (TBuilder) is the build call of one implementation: the k-th call on an input either fails with a message (a panic or an exception, read as `.error msg`) or returns an instance, which carries a definition (defOf; TransDef: name and arcs, output specification, timing, priority, action) and an identity (same). An input (TransIn) is what the host hands the builder; a field it leaves out is absent. The call number plays no part in this block; identity is CORE-021's."
          "An action is read as its identity tag (Act): the built-in passthrough action or another action named by an opaque id. What an action does is CORE-050's and the action model's (W3). The default action, passthrough when none is given, is CORE-051's line and is not restated here."
          "The default timing, Immediate when none is given, is TIME-001's last line (TimingContract.defaultTiming) and is not restated here. In the joint model the transition builder's default is tied to it by TimingAgree (Spec/GlossaryBuild.lean, Spec/ConsistencyStructure.lean)."
          "Line 4 reads 'valid' as TIME-001's validity table (Timing.Valid). A timing given in the input is a timing written out without a factory (a Rust enum variant, a TypeScript object literal, a Java record constructor): a factory fails before the build call is reached (TIME-001 lines 4 to 11), so a build call only sees an invalid timing written out directly. Line 4 is TIME-001's line 12 (building with an invalid timing written out fails) seen from the transition builder. The first draft of line 4 ('succeeds exactly when the arcs and output specification build') has no model together with TIME-001 and TimingAgree (core020_arcsOnly_conflicts_TIME_001); it is the mutant CORE_020_mutant_arcsOnly, killed by the builder that skips the timing check. The glossary's build-time checks (spec/glossary.md) include TIME-001's timing check, while Builds in Spec/Glossary.lean holds the arc and output-spec checks only; the sentence names the two halves separately, so both readings give the same line."
          "Only success and failure are stated, not the message of a failing call. The messages of the output-spec checks and of the input-and-read check are those of the IO and EXEC-012 blocks, stated over the builder's build check (projBuild in Spec/GlossaryBuild.lean; projBuild_ref ties the reference to refBuild), and the timing message is TIME-001's line 12. The messages of the input-arc check (CORE-030) and of the input-count checks (IO-002, IO-004) are stated by no block: the reference builder fails them with stand-ins (\"CORE-030\", msgCount), and CORE-030's assumes records its message as Q-tested in the three runtimes. The order of the checks (Rust: input checks, then the timing check, then the output-spec checks, TransitionBuilder::build in rust/libpetri-core/src/transition.rs) is not stated."
          "The body's field list is the definition's fields: name and arcs (core), the output specification (out, optional: a transition with no output specification has none, so 'an output specification' is read as 'at most one'), the timing, the priority (an integer; 'higher fires first' is EXEC-002's) and the action. The name is a field like any other here; the bullet's 'identifies the transition' is ruling D10 (transitions are identified by name, with the shared unique-names assumption of ruling D23), which this block does not restate. The match specification of a transition with a match specification (NU-020) is not a field of the definition: the ν-net model's definition extends TransDef with it (W9). Line 4 is scoped to a transition that has no match specification: NU-020's build checks (a match key named twice, a key that is not an input place) and NU-054's relay-target checks reject transitions whose arcs, output specification and timing pass (the NU-020 and NU-054 checks of TransitionBuilder::build, rust/libpetri-core/src/transition.rs), so the unscoped sentence would contradict NU-020. An input (TransIn) carries no match specification, so the Lean line 4 is the scoped sentence."
          "Line 1 compares arc lists as lists. Other blocks read their order and repetitions: EXEC-012's message names the first read arc in declaration order, IO-011 walks the output specification, and a read arc declared twice delivers twice (refQFire_reads). All three runtimes keep arcs as ordered lists with their repetitions (the fields of the Transition struct in rust/libpetri-core/src/transition.rs, the Transition constructor in java/src/main/java/org/libpetri/core/Transition.java, the fields of the Transition class in typescript/src/core/transition.ts). A builder that keeps only the first input arc (CORE_020_forbids_firstInput), stores the read arcs as a set and so drops a repeated read arc (CORE_020_forbids_dedupReads) or reverses the input arcs (CORE_020_mutant_arcOrderFree_killed, a reading that compares arcs without their order) violates line 1."
          "Line 2: a builder that drops a given priority (CORE_020_forbids_dropPrio) violates it, and so does one that stores a given Window(e, maximum) as Delayed(e), which has the same interval and no deadline (CORE_020_mutant_sameInterval_killed), as TIME-001's line 4 forbids for the factory."
          "Line 3 is the sentence ruling D32 (a) adds; every builder already defaults the priority to 0 (TransitionBuilder::new in rust/libpetri-core/src/transition.rs, the priority field of Transition.Builder in java/src/main/java/org/libpetri/core/Transition.java, the _priority field of TransitionBuilder in typescript/src/core/transition.ts). A builder whose default is another fixed value (-1 in CORE_020_mutant_someDefault_killed) violates it."
          "The block does not bind the language surface (ruling D99 (a)): TypeScript accepts any number as a priority where the model has integers, Java's sixth timing variant Unconstrained is not modelled (TIME-001), and the Python binding exposes only the name of a built transition. These are API shape, tested and not proven."
          "AC1 (a transition can be constructed with all the above fields via a builder pattern) is lines 1, 2 and 4 on one definition: every field the host gives is carried and a call on an input that builds succeeds (CORE_020_nonvacuous builds a transition with two input arcs, an output place, the timing Window(2, 5), priority 5 and an action). The builder pattern as an API shape is a Q-kind test (ruling D99 (a))."
          "AC2 (all fields are accessible after construction) is lines 1 and 2: the definition an instance carries exposes every field; that each language has an accessor per field is API shape (ruling D99 (a)). The test derivation ('verify all fields match') is lines 1 and 2 on CORE_020_nonvacuous's example."
  signoff "2026-11-13 bd4977fa5a0efd72 ai"
  statement : ∀ {N A : Type} [DecidableEq N], TBuilder N A → Prop :=
    fun B =>
      (∀ k i x, B.build k i = .ok x →
        (B.defOf x).core = i.core ∧ (B.defOf x).out = i.out) ∧
      (∀ k i x, B.build k i = .ok x →
        (∀ tm, i.timing = some tm → (B.defOf x).timing = tm) ∧
        (∀ pr, i.priority = some pr → (B.defOf x).priority = pr) ∧
        (∀ a, i.action = some a → (B.defOf x).action = a)) ∧
      (∀ k i x, B.build k i = .ok x → i.priority = none → (B.defOf x).priority = 0) ∧
      (∀ k i, (∃ x, B.build k i = .ok x) ↔
        Builds i.toTrans ∧ ∀ tm, i.timing = some tm → tm.Valid)

/- The pinned readable form of CORE-020: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CORE_020 : {N A : Type} → [DecidableEq N] → TBuilder N A → Prop :=
fun {N A} [DecidableEq N] B =>
  (∀ (k : ℕ) (i : TransIn N A) (x : B.I),
      B.build k i = Except.ok x → (B.defOf x).core = i.core ∧ (B.defOf x).out = i.out) ∧
    (∀ (k : ℕ) (i : TransIn N A) (x : B.I),
        B.build k i = Except.ok x →
          (∀ (tm : Timing), i.timing = some tm → (B.defOf x).timing = tm) ∧
            (∀ (pr : ℤ), i.priority = some pr → (B.defOf x).priority = pr) ∧
              ∀ (a : Act A), i.action = some a → (B.defOf x).action = a) ∧
      (∀ (k : ℕ) (i : TransIn N A) (x : B.I),
          B.build k i = Except.ok x → i.priority = none → (B.defOf x).priority = 0) ∧
        ∀ (k : ℕ) (i : TransIn N A),
          (∃ x, B.build k i = Except.ok x) ↔ Builds i.toTrans ∧ ∀ (tm : Timing), i.timing = some tm → tm.Valid
-/
#guard_msgs in #print CORE_020

/-! ### The four lines, named (for the mutants) -/

section Lines

variable {N A : Type} [DecidableEq N]

/-- Line 1 of CORE-020. -/
def core020_line1 (B : TBuilder N A) : Prop :=
  ∀ k i x, B.build k i = .ok x → (B.defOf x).core = i.core ∧ (B.defOf x).out = i.out

/-- Line 2 of CORE-020. -/
def core020_line2 (B : TBuilder N A) : Prop :=
  ∀ k i x, B.build k i = .ok x →
    (∀ tm, i.timing = some tm → (B.defOf x).timing = tm) ∧
    (∀ pr, i.priority = some pr → (B.defOf x).priority = pr) ∧
    (∀ a, i.action = some a → (B.defOf x).action = a)

/-- Line 3 of CORE-020. -/
def core020_line3 (B : TBuilder N A) : Prop :=
  ∀ k i x, B.build k i = .ok x → i.priority = none → (B.defOf x).priority = 0

/-- Line 4 of CORE-020. -/
def core020_line4 (B : TBuilder N A) : Prop :=
  ∀ k i, (∃ x, B.build k i = .ok x) ↔ Builds i.toTrans ∧ ∀ tm, i.timing = some tm → tm.Valid

/-- CORE-020 is its four lines. -/
theorem core020_iff (B : TBuilder N A) :
    CORE_020 B ↔ core020_line1 B ∧ core020_line2 B ∧ core020_line3 B ∧ core020_line4 B :=
  Iff.rfl

end Lines

/-! ### The reference -/

section Reference

variable {N A : Type} [DecidableEq N] [ToString N]

/-- Lines 1 to 3 hold of every builder that builds as the reference does and resolves the
definition as the reference does. -/
theorem core020_ref_lines {k : Nat} {i : TransIn N A} {x : (refTransBuild (N := N) (A := A)).I}
    (h : (refTransBuild (N := N) (A := A)).build k i = .ok x) :
    (refTransBuild (N := N) (A := A)).defOf x = i.resolve := by
  show x.1.2 = i.resolve
  rw [refTransBuild_def h]

/-- ✓ The reference transition builder satisfies CORE-020: it resolves the definition from the
input (given fields kept, priority 0 by default) and succeeds exactly when `refBuild` accepts the
arcs and output specification and TIME-001's reference factory accepts a given timing. -/
@[evidence holds CORE_020]
theorem CORE_020_reference : CORE_020 (refTransBuild (N := N) (A := A)) := by
  refine ⟨fun k i x h => ?_, fun k i x h => ?_, fun k i x h hp => ?_,
    fun k i => refTransBuild_succeeds⟩
  · rw [core020_ref_lines h]; exact ⟨rfl, rfl⟩
  · rw [core020_ref_lines h]
    refine ⟨fun tm ht => ?_, fun pr hp => ?_, fun a ha => ?_⟩
    · show i.timing.getD _ = tm
      rw [ht]; rfl
    · show i.priority.getD _ = pr
      rw [hp]; rfl
    · show i.action.getD _ = a
      rw [ha]; rfl
  · rw [core020_ref_lines h]
    show i.priority.getD _ = 0
    rw [hp]; rfl

end Reference

/-! ### Examples -/

/-- The example input: inputs on places 0 and 1, output `Place 2`, the timing Window(2, 5),
priority 5 and an action. -/
def core020_exIn : TransIn Nat Unit :=
  { core := ⟨"t", [⟨0, .one⟩, ⟨1, .one⟩], [], [], []⟩, out := some (.place 2),
    timing := some (.window 2 5), priority := some 5, action := some (.other ()) }

/-- The example input with no priority. -/
def core020_exNoPrio : TransIn Nat Unit := { core020_exIn with priority := none }

/-- The example input with the valid timing Window(0, maximum), which has no finite latest bound
short of the maximum. -/
def core020_exWinMax : TransIn Nat Unit := { core020_exIn with timing := some (.window 0 maxDurationMs) }

/-- The example input with the invalid timing Window(5, 2), written out without a factory. -/
def core020_exBad : TransIn Nat Unit := { core020_exIn with timing := some (.window 5 2) }

/-- The example's arcs and output specification build. -/
theorem core020_ex_builds : Builds core020_exIn.toTrans := (refBuild_eq_none_iff _).1 (by decide)

/-- The reference builds each valid example. -/
theorem core020_ref_builds (i : TransIn Nat Unit) (hc : i.core = core020_exIn.core)
    (ho : i.out = core020_exIn.out) (ht : ∀ tm, i.timing = some tm → tm.Valid) :
    ∃ x, (refTransBuild (N := Nat) (A := Unit)).build 0 i = .ok x := by
  refine refTransBuild_succeeds.2 ⟨?_, ht⟩
  have : i.toTrans = core020_exIn.toTrans := by
    simp only [TransIn.toTrans, hc, ho]
  rw [this]; exact core020_ex_builds

/-- ✓ Every line of CORE-020 is exercised by the reference: the example builds, and its
definition keeps the two input arcs in order, the output place, the timing Window(2, 5),
priority 5 and the action (lines 1 and 2, AC1, AC2); without a priority it has priority 0
(line 3); with the invalid timing Window(5, 2) written out directly the build call fails
(line 4). -/
@[evidence nonvacuous CORE_020]
theorem CORE_020_nonvacuous :
    (∃ x, (refTransBuild (N := Nat) (A := Unit)).build 0 core020_exIn = .ok x ∧
      ((refTransBuild (N := Nat) (A := Unit)).defOf x).core.inputs.map (·.place) = [0, 1] ∧
      ((refTransBuild (N := Nat) (A := Unit)).defOf x).out.map outPlaces = some [2] ∧
      ((refTransBuild (N := Nat) (A := Unit)).defOf x).timing = .window 2 5 ∧
      ((refTransBuild (N := Nat) (A := Unit)).defOf x).priority = 5 ∧
      ((refTransBuild (N := Nat) (A := Unit)).defOf x).action = .other ()) ∧
    (∃ x, (refTransBuild (N := Nat) (A := Unit)).build 0 core020_exNoPrio = .ok x ∧
      ((refTransBuild (N := Nat) (A := Unit)).defOf x).priority = 0) ∧
    (¬ ∃ x, (refTransBuild (N := Nat) (A := Unit)).build 0 core020_exBad = .ok x) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := core020_ref_builds core020_exIn rfl rfl (by
      intro tm ht; cases ht; decide)
    refine ⟨x, hx, ?_⟩
    rw [core020_ref_lines hx]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨x, hx⟩ := core020_ref_builds core020_exNoPrio rfl rfl (by
      intro tm ht; cases ht; decide)
    refine ⟨x, hx, ?_⟩
    rw [core020_ref_lines hx]
    rfl
  · intro h
    have := (refTransBuild_succeeds.1 h).2 (.window 5 2) rfl
    exact absurd this (by decide)

/-! ### Wrong builders -/

section Wrong

variable {N A : Type} [DecidableEq N] [ToString N]

/-- A builder that drops the priority it was given (always 0), and is the reference otherwise. -/
def core020_dropPrioBuild : TBuilder N A :=
  { refTransBuild with defOf := fun x => { x.1.2 with priority := 0 } }

/-- A builder that keeps only the first input arc (a truncating builder), and is the reference
otherwise. -/
def core020_firstInputBuild : TBuilder N A :=
  { refTransBuild with
    defOf := fun x => { x.1.2 with core := { x.1.2.core with inputs := x.1.2.core.inputs.take 1 } } }

/-- A builder that stores the read arcs as a set, so a read arc declared twice comes back once
(the runtimes' cached read-place sets, used as the arc list), and is the reference otherwise. -/
def core020_dedupReadsBuild : TBuilder N A :=
  { refTransBuild with
    defOf := fun x => { x.1.2 with core := { x.1.2.core with reads := x.1.2.core.reads.dedup } } }

end Wrong

/-- The example input with a read arc on place 3 declared twice. -/
def core020_exDupRead : TransIn Nat Unit :=
  { core020_exIn with core := { core020_exIn.core with reads := [3, 3] } }

/-- The example with the repeated read arc builds: [EXEC-012] rejects only a read on an input
place, and no check rejects a read arc declared twice. -/
theorem core020_exDupRead_builds : Builds core020_exDupRead.toTrans :=
  (refBuild_eq_none_iff _).1 (by decide)

/-- ✗ A builder that drops a given priority violates CORE-020 (line 2): the example's priority 5
becomes 0. -/
@[evidence forbids CORE_020]
theorem CORE_020_forbids_dropPrio : ¬ CORE_020 (core020_dropPrioBuild (N := Nat) (A := Unit)) := by
  intro h
  obtain ⟨x, hx⟩ := core020_ref_builds core020_exIn rfl rfl (by intro tm ht; cases ht; decide)
  have := (h.2.1 0 core020_exIn x hx).2.1 5 rfl
  exact absurd this (by simp [core020_dropPrioBuild])

/-- ✗ A builder that keeps only the first input arc violates CORE-020 (line 1): the example's two
input arcs become one. -/
@[evidence forbids CORE_020]
theorem CORE_020_forbids_firstInput :
    ¬ CORE_020 (core020_firstInputBuild (N := Nat) (A := Unit)) := by
  intro h
  obtain ⟨x, hx⟩ := core020_ref_builds core020_exIn rfl rfl (by intro tm ht; cases ht; decide)
  have h1 := congrArg (·.inputs.length) (h.1 0 core020_exIn x hx).1
  have hd := core020_ref_lines hx
  simp only [core020_firstInputBuild] at h1
  have : x.1.2 = core020_exIn.resolve := hd
  rw [this] at h1
  exact absurd h1 (by decide)

/-- ✗ A builder that drops a repeated read arc violates CORE-020 (line 1, the repetitions half):
the read arcs 3, 3 come back as 3. -/
@[evidence forbids CORE_020]
theorem CORE_020_forbids_dedupReads :
    ¬ CORE_020 (core020_dedupReadsBuild (N := Nat) (A := Unit)) := by
  intro h
  obtain ⟨x, hx⟩ := (refTransBuild_succeeds (k := 0) (i := core020_exDupRead)).2
    ⟨core020_exDupRead_builds, fun tm ht => by cases ht; decide⟩
  have h1 := congrArg (·.reads) (h.1 0 core020_exDupRead x hx).1
  have : x.1.2 = core020_exDupRead.resolve := core020_ref_lines hx
  simp only [core020_dedupReadsBuild] at h1
  rw [this] at h1
  exact absurd h1 (by decide)

/-! ### Mutant: line 1 without the order of the arcs -/

section MutantOrder

variable {N A : Type} [DecidableEq N]

/-- Mutant reading of line 1: the definition has the given name and output specification, and
each arc list holds the given arcs with their repetitions, in any order (a sorting or reordering
builder passes). Lines 2 to 4 are as in CORE-020. -/
def CORE_020_mutant_arcOrderFree (B : TBuilder N A) : Prop :=
  (∀ k i x, B.build k i = .ok x →
    (B.defOf x).core.name = i.core.name ∧ (B.defOf x).core.inputs.Perm i.core.inputs ∧
    (B.defOf x).core.inhibitors.Perm i.core.inhibitors ∧
    (B.defOf x).core.reads.Perm i.core.reads ∧ (B.defOf x).core.resets.Perm i.core.resets ∧
    (B.defOf x).out = i.out) ∧
  core020_line2 B ∧ core020_line3 B ∧ core020_line4 B

end MutantOrder

/-- A builder that stores the input arcs in reverse order, and is the reference otherwise. -/
def core020_reverseBuild {N A : Type} [DecidableEq N] [ToString N] : TBuilder N A :=
  { refTransBuild with
    defOf := fun x => { x.1.2 with core := { x.1.2.core with inputs := x.1.2.core.inputs.reverse } } }

/-- The reversing builder kills the mutant: it keeps every arc with its repetitions, so it meets
the order-free reading, but the example's input arcs 0, 1 come back as 1, 0 (line 1). -/
@[evidence mutant CORE_020]
theorem CORE_020_mutant_arcOrderFree_killed :
    CORE_020_mutant_arcOrderFree (core020_reverseBuild (N := Nat) (A := Unit)) ∧
      ¬ CORE_020 (core020_reverseBuild (N := Nat) (A := Unit)) := by
  obtain ⟨-, h2, h3, h4⟩ := CORE_020_reference (N := Nat) (A := Unit)
  refine ⟨⟨fun k i x hx => ?_, fun k i x hx => ?_, fun k i x hx => ?_, h4⟩, fun h => ?_⟩
  · have hd : x.1.2 = i.resolve := core020_ref_lines hx
    show x.1.2.core.name = _ ∧ x.1.2.core.inputs.reverse.Perm _ ∧ x.1.2.core.inhibitors.Perm _ ∧
      x.1.2.core.reads.Perm _ ∧ x.1.2.core.resets.Perm _ ∧ x.1.2.out = _
    rw [hd]
    exact ⟨rfl, List.reverse_perm _, List.Perm.refl _, List.Perm.refl _, List.Perm.refl _, rfl⟩
  · exact h2 k i x hx
  · exact h3 k i x hx
  · obtain ⟨x, hx⟩ := core020_ref_builds core020_exIn rfl rfl (by intro tm ht; cases ht; decide)
    have h1 := congrArg (·.inputs.map (·.place)) (h.1 0 core020_exIn x hx).1
    have : x.1.2 = core020_exIn.resolve := core020_ref_lines hx
    simp only [core020_reverseBuild] at h1
    rw [this] at h1
    exact absurd h1 (by decide)

/-! ### Mutant: line 2 with a timing kept up to its interval -/

/-- A timing with a `Window` whose latest bound is the maximum duration written as the `Delayed`
with the same earliest bound: the same interval, no deadline. -/
def core020_normTiming : Timing → Timing
  | .window e l => if l = maxDurationMs then .delayed e else .window e l
  | tm => tm

theorem core020_normTiming_earliest (tm : Timing) :
    (core020_normTiming tm).earliest = tm.earliest := by
  cases tm with
  | window e l =>
    simp only [core020_normTiming]
    split <;> rfl
  | _ => rfl

theorem core020_normTiming_latest (tm : Timing) :
    (core020_normTiming tm).latest = tm.latest := by
  cases tm with
  | window e l =>
    simp only [core020_normTiming]
    split
    · rename_i h; subst h; rfl
    · rfl
  | _ => rfl

section MutantInterval

variable {N A : Type} [DecidableEq N]

/-- Mutant reading of line 2: a given timing is kept up to its interval (the definition's
timing has the given earliest and latest bounds); a given priority and action are kept. Lines 1, 3
and 4 are as in CORE-020. -/
def CORE_020_mutant_sameInterval (B : TBuilder N A) : Prop :=
  core020_line1 B ∧
  (∀ k i x, B.build k i = .ok x →
    (∀ tm, i.timing = some tm →
      (B.defOf x).timing.earliest = tm.earliest ∧ (B.defOf x).timing.latest = tm.latest) ∧
    (∀ pr, i.priority = some pr → (B.defOf x).priority = pr) ∧
    (∀ a, i.action = some a → (B.defOf x).action = a)) ∧
  core020_line3 B ∧ core020_line4 B

end MutantInterval

/-- A builder that normalises a given `Window(e, maximum)` to `Delayed(e)`, and is the reference
otherwise. -/
def core020_normaliseBuild {N A : Type} [DecidableEq N] [ToString N] : TBuilder N A :=
  { refTransBuild with defOf := fun x => { x.1.2 with timing := core020_normTiming x.1.2.timing } }

/-- The normalising builder kills the mutant: `Delayed(e)` has the interval of `Window(e,
maximum)`, so it meets the interval reading, but the example's valid `Window(0, maximum)` comes
back as `Delayed(0)`, which has no deadline (line 2). -/
@[evidence mutant CORE_020]
theorem CORE_020_mutant_sameInterval_killed :
    CORE_020_mutant_sameInterval (core020_normaliseBuild (N := Nat) (A := Unit)) ∧
      ¬ CORE_020 (core020_normaliseBuild (N := Nat) (A := Unit)) := by
  obtain ⟨h1, h2, h3, h4⟩ := CORE_020_reference (N := Nat) (A := Unit)
  refine ⟨⟨fun k i x hx => h1 k i x hx, fun k i x hx => ?_, fun k i x hx => h3 k i x hx, h4⟩,
    fun h => ?_⟩
  · obtain ⟨ht, hp, ha⟩ := h2 k i x hx
    refine ⟨fun tm htm => ?_, hp, ha⟩
    have e : x.1.2.timing = tm := ht tm htm
    show (core020_normTiming x.1.2.timing).earliest = _ ∧ (core020_normTiming x.1.2.timing).latest = _
    rw [e, core020_normTiming_earliest, core020_normTiming_latest]
    exact ⟨rfl, rfl⟩
  · obtain ⟨x, hx⟩ := core020_ref_builds core020_exWinMax rfl rfl (by
      intro tm ht; cases ht; decide)
    have ht := (h.2.1 0 core020_exWinMax x hx).1 _ rfl
    have : x.1.2 = core020_exWinMax.resolve := core020_ref_lines hx
    simp only [core020_normaliseBuild] at ht
    rw [this] at ht
    exact absurd ht (by decide)

/-! ### Mutant: line 3 with any fixed default priority -/

section MutantDefault

variable {N A : Type} [DecidableEq N]

/-- Mutant reading of line 3: a transition built without a priority has one fixed default
priority, whichever it is. Lines 1, 2 and 4 are as in CORE-020. -/
def CORE_020_mutant_someDefault (B : TBuilder N A) : Prop :=
  core020_line1 B ∧ core020_line2 B ∧
  (∃ c : Int, ∀ k i x, B.build k i = .ok x → i.priority = none → (B.defOf x).priority = c) ∧
  core020_line4 B

end MutantDefault

/-- A builder whose default priority is -1: it remembers whether a priority was given, and is the
reference otherwise. -/
def core020_lowDefaultBuild {N A : Type} [DecidableEq N] [ToString N] : TBuilder N A where
  I := (refTransBuild (N := N) (A := A)).I × Option Int
  build k i := ((refTransBuild (N := N) (A := A)).build k i).map (·, i.priority)
  defOf x := { x.1.1.2 with priority := x.2.getD (-1) }
  same x y := x.1.1.1 = y.1.1.1

/-- A build call of the low-default builder returns the reference's instance and the given
priority. -/
theorem core020_lowDefault_ok {k : Nat} {i : TransIn Nat Unit}
    {x : (core020_lowDefaultBuild (N := Nat) (A := Unit)).I}
    (h : (core020_lowDefaultBuild (N := Nat) (A := Unit)).build k i = .ok x) :
    (refTransBuild (N := Nat) (A := Unit)).build k i = .ok x.1 ∧ x.2 = i.priority := by
  simp only [core020_lowDefaultBuild] at h
  cases hb : (refTransBuild (N := Nat) (A := Unit)).build k i with
  | error e => rw [hb] at h; cases h
  | ok y => rw [hb] at h; cases h; exact ⟨rfl, rfl⟩

/-- The low-default builder kills the mutant: its default is the fixed value -1, so it meets the
fixed-default reading, but the example built without a priority has priority -1, not 0
(line 3). -/
@[evidence mutant CORE_020]
theorem CORE_020_mutant_someDefault_killed :
    CORE_020_mutant_someDefault (core020_lowDefaultBuild (N := Nat) (A := Unit)) ∧
      ¬ CORE_020 (core020_lowDefaultBuild (N := Nat) (A := Unit)) := by
  obtain ⟨h1, h2, -, h4⟩ := CORE_020_reference (N := Nat) (A := Unit)
  refine ⟨⟨fun k i x hx => ?_, fun k i x hx => ?_, ⟨-1, fun k i x hx hp => ?_⟩, fun k i => ?_⟩,
    fun h => ?_⟩
  · exact h1 k i x.1 (core020_lowDefault_ok hx).1
  · obtain ⟨hr, he⟩ := core020_lowDefault_ok hx
    obtain ⟨ht, -, ha⟩ := h2 k i x.1 hr
    refine ⟨ht, fun pr hp => ?_, ha⟩
    show x.2.getD (-1) = pr
    rw [he, hp]; rfl
  · show x.2.getD (-1) = -1
    rw [(core020_lowDefault_ok hx).2, hp]; rfl
  · rw [← h4 k i]
    constructor
    · rintro ⟨x, hx⟩; exact ⟨x.1, (core020_lowDefault_ok hx).1⟩
    · rintro ⟨y, hy⟩
      exact ⟨(y, i.priority), by simp only [core020_lowDefaultBuild, hy]; rfl⟩
  · obtain ⟨y, hy⟩ := core020_ref_builds core020_exNoPrio rfl rfl (by
      intro tm ht; cases ht; decide)
    have hx : (core020_lowDefaultBuild (N := Nat) (A := Unit)).build 0 core020_exNoPrio =
        .ok (y, none) := by
      simp only [core020_lowDefaultBuild, hy]; rfl
    have h3 : ((none : Option Int).getD (-1)) = 0 := h.2.2.1 0 core020_exNoPrio _ hx rfl
    exact absurd h3 (by decide)

/-! ### Mutant: line 4 without the timing (the first draft) -/

section MutantArcsOnly

variable {N A : Type} [DecidableEq N]

/-- Mutant reading of line 4, the first draft of the block: a build call succeeds exactly when
the arcs and output specification build, whatever timing is given. Lines 1 to 3 are as in
CORE-020. -/
def CORE_020_mutant_arcsOnly (B : TBuilder N A) : Prop :=
  core020_line1 B ∧ core020_line2 B ∧ core020_line3 B ∧
  ∀ k i, (∃ x, B.build k i = .ok x) ↔ Builds i.toTrans

end MutantArcsOnly

/-- A builder that does not check a timing written out without a factory: `refBuild`'s checks
only (the Rust builder before [TIME-001] AC5). -/
def core020_uncheckedBuild {N A : Type} [DecidableEq N] [ToString N] : TBuilder N A where
  I := Nat × TransDef N A
  build k i := match refBuild i.toTrans with
    | some e => .error e
    | none => .ok (k, i.resolve)
  defOf x := x.2
  same x y := x.1 = y.1

/-- A build call of the unchecked builder returns the resolved definition exactly when the arcs
and output specification build. -/
theorem core020_unchecked_ok {N A : Type} [DecidableEq N] [ToString N] {k : Nat}
    {i : TransIn N A} {x : (core020_uncheckedBuild (N := N) (A := A)).I} :
    (core020_uncheckedBuild (N := N) (A := A)).build k i = .ok x ↔
      Builds i.toTrans ∧ x = (k, i.resolve) := by
  rw [← refBuild_eq_none_iff]
  show (match refBuild i.toTrans with
    | some e => Except.error e
    | none => Except.ok (k, i.resolve)) = Except.ok x ↔ _
  cases refBuild i.toTrans with
  | some e => exact ⟨(fun h => nomatch h), (fun ⟨h, _⟩ => nomatch h)⟩
  | none =>
    exact ⟨fun h => ⟨rfl, (Except.ok.inj h).symm⟩, fun ⟨_, h⟩ => h ▸ rfl⟩

/-- The unchecked builder kills the mutant: it meets the first draft, but the example with the
invalid timing Window(5, 2) written out directly builds (line 4). -/
@[evidence mutant CORE_020]
theorem CORE_020_mutant_arcsOnly_killed :
    CORE_020_mutant_arcsOnly (core020_uncheckedBuild (N := Nat) (A := Unit)) ∧
      ¬ CORE_020 (core020_uncheckedBuild (N := Nat) (A := Unit)) := by
  refine ⟨⟨fun k i x hx => ?_, fun k i x hx => ?_, fun k i x hx hp => ?_, fun k i => ?_⟩,
    fun h => ?_⟩
  · obtain ⟨-, rfl⟩ := core020_unchecked_ok.1 hx; exact ⟨rfl, rfl⟩
  · obtain ⟨-, rfl⟩ := core020_unchecked_ok.1 hx
    refine ⟨fun tm ht => ?_, fun pr hp => ?_, fun a ha => ?_⟩
    · show i.timing.getD _ = tm
      rw [ht]; rfl
    · show i.priority.getD _ = pr
      rw [hp]; rfl
    · show i.action.getD _ = a
      rw [ha]; rfl
  · obtain ⟨-, rfl⟩ := core020_unchecked_ok.1 hx
    show i.priority.getD _ = 0
    rw [hp]; rfl
  · exact ⟨fun ⟨x, hx⟩ => (core020_unchecked_ok.1 hx).1,
      fun hb => ⟨(k, i.resolve), core020_unchecked_ok.2 ⟨hb, rfl⟩⟩⟩
  · have hb : Builds core020_exBad.toTrans := core020_ex_builds
    have := ((h.2.2.2 0 core020_exBad).1 ⟨(0, core020_exBad.resolve),
      core020_unchecked_ok.2 ⟨hb, rfl⟩⟩).2 (.window 5 2) rfl
    exact absurd this (by decide)

/-- The first draft of line 4 contradicts TIME-001 in every joint model that ties the two
transition builders together: no builder satisfies the first draft, agrees with a timing contract
on timings and satisfies TIME-001 with it, since TIME-001's builder rejects Window(5, 2) and the
first draft builds it (skeptic correction S1 of the core-structure design). -/
theorem core020_arcsOnly_conflicts_TIME_001 (TB : TBuilder Nat Unit) (Q : TimingContract)
    (h20 : CORE_020_mutant_arcsOnly TB) (h1 : TIME_001 Q) (hag : TimingAgree TB Q) : False := by
  have hb : Builds core020_exBad.toTrans := core020_ex_builds
  obtain ⟨x, hx⟩ := (h20.2.2.2 0 core020_exBad).2 hb
  obtain ⟨v, hv⟩ := (hag.1 0 core020_exBad (.window 5 2) hb rfl).1 ⟨x, hx⟩
  have hbuild := h1.2.2.2.2.2.2.2.2.2.2.2.1 (.window 5 2)
  have hfac := h1.2.2.2.2.2.2.2.2.1 5 2 (by decide) (by decide)
  rw [hbuild, hfac] at hv
  cases hv

end Libpetri.Spec
