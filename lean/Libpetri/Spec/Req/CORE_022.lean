import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.Glossary

set_option linter.missingDocs true

/-!
# CORE-022: Transition enablement (`spec/01-core-model.md`)

A predicate over an abstract firing relation `F : FireRel N`. The evidence theorems check it
against the reference semantics (`Reference.Fires`, as `RefFire`), against concrete firing
relations that each drop one condition, and against a mutant reading per clause.

CORE-022 concerns transitions that build. `Builds` is the build-time check of a transition
(the input-arc check of [CORE-030], the input-count checks of [IO-002] and [IO-004], the
input-and-read check of [EXEC-012] and the output-spec checks of [IO-011]–[IO-014]); the block
quantifies over the transitions that pass it.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

requirement CORE_022
  id "CORE-022"
  title "Transition enablement"
  kind B
  scope "all executors"
  source verbatim "spec/01-core-model.md"
  quote "A transition is **enabled** in a marking when every input place holds at least its required count (see [IO-001]–[IO-004]), every read place is marked and no inhibitor place is marked."
        "*While* an input place of a transition holds fewer tokens than its required count, the transition *shall not* fire."
        "*While* a read place of a transition is unmarked, the transition *shall not* fire."
        "*While* an inhibitor place of a transition is marked, the transition *shall not* fire."
        "*While* a transition that has no match specification ([NU-020]) is enabled, the transition *shall* be able to fire."
        "This requirement concerns transitions that build. A definition that building the transition rejects ([CORE-030], [IO-002], [IO-004], [EXEC-012], [IO-011]–[IO-014]) is not a transition of any net and is never enabled anywhere; in particular an output spec whose alternatives no write can tell apart ([IO-012]) never reaches a marking."
  reading "For every transition t that builds (Builds t: at most one input arc per place, every input arc requiring at least one token, no place with both an input arc and a read arc, no place twice in one output branch, at most one Timeout node, no Xor node inside the Timeout child, no ForwardInput outside a Timeout child, every forward's from an input place, no two output branches claiming the same set of places):"
          "t does not fire from a marking in which the place of some input arc of t holds fewer tokens than that arc's required count;"
          "t does not fire from a marking in which some read place of t is unmarked;"
          "t does not fire from a marking in which some inhibitor place of t is marked;"
          "from every marking m in which t is enabled, t fires to some marking m'."
  assumes "A firing is read as one step from a marking to a marking (glossary: Fire); timing and priority play no part. 'Enabled' is the glossary term (`Enabled`, readable form `enabled_iff`); 'can fire' / 'able to fire' is read as 'some firing exists'. The last line says a firing exists, not that an executor performs it now: when an enabled transition actually fires is the subject of the timing and scheduling requirements (TIME-*, EXEC-*)."
          "Enablement is a function of the current marking alone: the three 'shall not' lines forbid a firing from every marking in which a condition fails, whatever happened before. This is how 'when any condition ceases to hold, the transition becomes disabled' of the previous wording is read."
          "The input condition ranges over every input arc of t, not only the first one per place. Under CORE-030 a transition has at most one input arc per place, so the two readings coincide on every transition that can be built."
          "The 'able to fire' line needs every transition to have at least one way to end (an output branch, or the empty deposit when it has no output spec); the reference semantics has one for every output spec (`Reference.exists_deposit`)."
          "Transitions with a ν match specification (NU-020) add a correlation condition on top of these three, as the section says after the definition, and the 'able to fire' sentence is scoped to a transition that has no match specification (ruling D30). The transitions of the model (Reference.Trans) carry no match specification, so the last line quantifies over every transition that builds. The three 'shall not' sentences need no exclusion: a correlated input requires at least its required count of tokens of one name, so at least its required count of tokens. How the correlation condition decides a firing is NU-020's, not encoded here."
          "The inhibitor line restates the first clause of CORE-031 because CORE-022 lists it as one of its conditions; it is kept so that this block stands on its own."
          "Inside a firing pass, the marking a transition fires from in the sense of these lines is the pass-visible marking, not the live one (EXEC-003 AC4, ruling D75 (a)): the input counts, the read places and the inhibitor places are all judged on it, so a token a synchronous action deposited earlier in the same pass neither enables a transition nor, in an inhibitor place, blocks one. Rust (recheck_can_fire on the pass snapshot, rust/libpetri-runtime/src/bitmap_backend.rs:708-713, inhibitors tested on that snapshot, compiled_net.rs:355-361) and Java (canEnable on fireScanBitmap) start such a transition, as EXEC_003_nonvacuous's fifth part shows on the reference executor (T4); TypeScript settles every firing in step 1, so its passes have no same-pass deposit. EXEC_003_start_inhibitors states the start half over the executor: a start happens only with every inhibitor place empty in the pass-visible marking. The bridge from a reference start to this one-step firing relation is recorded with the integrator."
          "'Transitions that build' is read as the build-time checks themselves (`Builds`): the input-arc check of CORE-030, the input-count checks of IO-002 and IO-004 (no Exactly(0), no AtLeast(0)), the input-and-read check of EXEC-012 (ruling D15) and the output-spec checks of IO-011 (a place twice in one branch), IO-013 (more than one Timeout node), IO-014 (a ForwardInput outside a Timeout child; a forward from a non-input place) and IO-012 (two output branches claiming the same set of places). A transition that fails one constrains nothing here: no executor ever holds it, so it neither fires nor is required to. Branch sets are compared as sets (`SameSet`), so Xor(And(A, B, C), And(A, B)) and Xor(And(P, A), And(P, B)) build and are covered, while Xor(P, P) and Xor(And(A, B), And(B, A)) are not."
          "The reference `Out` is binary; n-ary And / Xor are read as right-nested, which keeps the IO-016 enumeration order, so the IO-012 branch indices and the build verdict are those of the n-ary spec."
          "AC1 (satisfied inputs, reads present, inhibitors empty, enabled) is the last line."
          "AC2 (missing input tokens, disabled) is the second line."
          "AC3 (missing read tokens, disabled) is the third line."
          "AC4 (inhibitor place has tokens, disabled) is the fourth line."
  signoff "2026-11-13 7385a628838a890d ai"
  statement : ∀ {N : Type} [DecidableEq N], FireRel N → Prop :=
    fun F => ∀ t, Builds t →
      (while (fun m => ∃ s ∈ t.core.inputs, m s.place < requiredCount s.card), never Fire F t) ∧
      (while (fun m => ∃ p, ReadArc t p ∧ ¬ Marked m p), never Fire F t) ∧
      (while (fun m => ∃ p, InhibitorArc t p ∧ Marked m p), never Fire F t) ∧
      (∀ m, Enabled t m → ∃ m', Fire F t m m')

/- The pinned readable form of CORE-022: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CORE_022 : {N : Type} → [DecidableEq N] → FireRel N → Prop :=
fun {N} [DecidableEq N] F =>
  ∀ (t : Reference.Trans N),
    Builds t →
      (while fun m => ∃ s ∈ t.core.inputs, m s.place < requiredCount s.card, never Fire F t) ∧
        (while fun m => ∃ p, ReadArc t p ∧ ¬Marked m p, never Fire F t) ∧
          (while fun m => ∃ p, InhibitorArc t p ∧ Marked m p, never Fire F t) ∧
            ∀ (m : CountMarking N), Enabled t m → ∃ m', Fire F t m m'
-/
#guard_msgs in #print CORE_022

/-- The reference semantics satisfies CORE-022: a reference firing starts with `Seam.enabledNA`,
whose readable form (`enabled_iff`) is the three conditions, so a failed condition rules out
every firing; and an enabled transition always has a deposit to end with
(`Reference.exists_deposit`), so it fires. The reference fires every transition, those that do
not build included, so the scoping to transitions that build is not needed here. -/
@[evidence holds CORE_022]
theorem CORE_022_reference {N : Type} [DecidableEq N] : CORE_022 (RefFire (N := N)) := by
  intro t _
  refine ⟨?_, ?_, ?_, fun m hen => ?_⟩
  · rintro m m' ⟨d, hen, -, -⟩ ⟨s, hs, hlt⟩
    have := ((enabled_iff t m).1 hen).1 s hs
    omega
  · rintro m m' ⟨d, hen, -, -⟩ ⟨p, hp, hn⟩
    exact hn (((enabled_iff t m).1 hen).2.2 p hp)
  · rintro m m' ⟨d, hen, -, -⟩ ⟨p, hp, hm⟩
    exact ((enabled_iff t m).1 hen).2.1 p hp hm
  · obtain ⟨ch, d, hd⟩ := exists_deposit (nconsumed m t.core) t.out
    exact ⟨_, d, hen, ⟨ch, hd⟩, rfl⟩

/-- **Not the reference semantics.** The reference firings of the transitions that build, and
no firing at all of a definition the build rejects: the executors' reading, since a rejected
definition never reaches a net. -/
def CORE_022_refFireBuilt {N : Type} [DecidableEq N] : FireRel N :=
  fun t m d m' => Builds t ∧ RefFire t m d m'

/- The reference restricted to transitions that build is the witness model of CORE-022's
second `holds` theorem. -/
#spec_witness CORE_022_refFireBuilt

/-- ✓ CORE-022 holds of the reference restricted to transitions that build
(`CORE_022_refFireBuilt`): the "shall not" lines are the reference's, and a transition that
builds keeps every reference firing. This is the relation that also satisfies IO-012, whose
`Xor(Place(0), Place(0))` transition (`core022_dup`) does not build. -/
@[evidence holds CORE_022]
theorem CORE_022_builtOnly {N : Type} [DecidableEq N] :
    CORE_022 (CORE_022_refFireBuilt (N := N)) := by
  intro t hwf
  obtain ⟨h1, h2, h3, h4⟩ := CORE_022_reference (N := N) t hwf
  refine ⟨fun m m' hf hc => h1 m m' ?_ hc, fun m m' hf hc => h2 m m' ?_ hc,
    fun m m' hf hc => h3 m m' ?_ hc, fun m hen => ?_⟩
  · obtain ⟨d, -, hd⟩ := hf; exact ⟨d, hd⟩
  · obtain ⟨d, -, hd⟩ := hf; exact ⟨d, hd⟩
  · obtain ⟨d, -, hd⟩ := hf; exact ⟨d, hd⟩
  · obtain ⟨m', d, hd⟩ := h4 m hen
    exact ⟨m', d, hwf, hd⟩

/-! ### Examples over a three-place net -/

/-- The one transition of the examples: an input arc `One` on place `0`, a read arc on place
`1`, an inhibitor arc on place `2`, no output spec. -/
def core022_t : Trans Nat :=
  { core :=
      { name := "t"
        inputs := [{ place := 0, card := .one }]
        inhibitors := [2]
        reads := [1]
        resets := [] }
    out := none }

/-- `core022_t` builds: one input arc, no output spec. -/
theorem core022_t_wf : Builds core022_t := by decide

/-- The marking in which `core022_t` is enabled: one token in `0`, one in `1`, none in `2`. -/
def core022_enabled : Nat → Nat := fun n => [1, 1, 0].getD n 0

/-- `core022_enabled` with the input place emptied (AC2). -/
def core022_noInput : Nat → Nat := fun n => [0, 1, 0].getD n 0

/-- `core022_enabled` with the read place emptied (AC3). -/
def core022_noRead : Nat → Nat := fun n => [1, 0, 0].getD n 0

/-- `core022_enabled` with the inhibitor place marked (AC4). -/
def core022_inhibited : Nat → Nat := fun n => [1, 1, 1].getD n 0

/-- The empty marking. -/
def core022_empty : Nat → Nat := fun _ => 0

/-- An arc-less transition named `name` with output spec `o`. -/
def core022_arcless (name : String) (o : Out Nat) : Trans Nat :=
  { core := { name := name, inputs := [], inhibitors := [], reads := [], resets := [] }
    out := some o }

/-- `Xor(Place(0), Place(0))`: two distinct assignments claim `{0}`, so it does not build
([IO-012] AC5). -/
def core022_dup : Trans Nat := core022_arcless "dup" (.xor (.place 0) (.place 0))

/-- `Xor(And(0, 1, 2), And(0, 1))`: one claim strictly contains the other, and it builds
([IO-012] AC5). -/
def core022_overlap : Trans Nat :=
  core022_arcless "overlap" (.xor (.and (.place 0) (.and (.place 1) (.place 2)))
    (.and (.place 0) (.place 1)))

/-- `core022_dup` does not build: its two output branches both claim `{0}`. -/
theorem core022_dup_not_wf : ¬ Builds core022_dup := by decide

/-- `core022_overlap` builds: its branches `[0, 1, 2]` and `[0, 1]` are different sets. -/
theorem core022_overlap_wf : Builds core022_overlap := by decide

/-- A firing relation that lets a transition fire, changing nothing, exactly when `P` holds of
it and the marking. Each counterexample below is one choice of `P`. -/
def core022_gated (P : Trans Nat → (Nat → Nat) → Prop) : FireRel Nat :=
  fun t m d m' => P t m ∧ d = [] ∧ m' = m

/-- Fires when the read and inhibitor conditions hold, ignoring the input arcs. -/
def core022_ignoresInputs : FireRel Nat :=
  core022_gated fun t m => (∀ p ∈ t.core.reads, Marked m p) ∧
    (∀ p ∈ t.core.inhibitors, ¬ Marked m p)

/-- Fires when the input and inhibitor conditions hold, ignoring the read arcs. -/
def core022_ignoresReads : FireRel Nat :=
  core022_gated fun t m => (∀ s ∈ t.core.inputs, requiredCount s.card ≤ m s.place) ∧
    (∀ p ∈ t.core.inhibitors, ¬ Marked m p)

/-- Fires when the input and read conditions hold, ignoring the inhibitor arcs. -/
def core022_ignoresInhibitors : FireRel Nat :=
  core022_gated fun t m => (∀ s ∈ t.core.inputs, requiredCount s.card ≤ m s.place) ∧
    (∀ p ∈ t.core.reads, Marked m p)

/-- Never fires at all. -/
def core022_neverFire : FireRel Nat := core022_gated fun _ _ => False

/-- ✗ Ignoring input arcs violates CORE-022 (second line): `core022_t` fires from
`core022_noInput`, whose input place is empty. -/
@[evidence forbids CORE_022]
theorem CORE_022_forbids_ignoresInputs : ¬ CORE_022 core022_ignoresInputs := by
  intro h
  exact (h core022_t core022_t_wf).1 core022_noInput core022_noInput
    ⟨[], ⟨by decide, by decide⟩, rfl, rfl⟩ (by decide)

/-- ✗ Ignoring read arcs violates CORE-022 (third line): `core022_t` fires from
`core022_noRead`, whose read place is empty. -/
@[evidence forbids CORE_022]
theorem CORE_022_forbids_ignoresReads : ¬ CORE_022 core022_ignoresReads := by
  intro h
  exact (h core022_t core022_t_wf).2.1 core022_noRead core022_noRead
    ⟨[], ⟨by decide, by decide⟩, rfl, rfl⟩ ⟨1, by decide, by decide⟩

/-- ✗ Ignoring inhibitor arcs violates CORE-022 (fourth line): `core022_t` fires from
`core022_inhibited`, whose inhibitor place is marked. -/
@[evidence forbids CORE_022]
theorem CORE_022_forbids_ignoresInhibitors : ¬ CORE_022 core022_ignoresInhibitors := by
  intro h
  exact (h core022_t core022_t_wf).2.2.1 core022_inhibited core022_inhibited
    ⟨[], ⟨by decide, by decide⟩, rfl, rfl⟩ ⟨2, by decide, by decide⟩

/-- ✗ A firing relation that never fires violates CORE-022 (last line): `core022_t` is enabled
at `core022_enabled` but does not fire. -/
@[evidence forbids CORE_022]
theorem CORE_022_forbids_neverFire : ¬ CORE_022 core022_neverFire := by
  intro h
  obtain ⟨_, _, hf, -⟩ := (h core022_t core022_t_wf).2.2.2 core022_enabled (by decide)
  exact hf

/-- A build check stricter than the spec's: besides `Builds`, no output branch's claim
contains another's. This is the misreading of [IO-012] that takes overlapping alternatives for
ambiguous ones, rejecting `Xor(And(A, B, C), And(A, B))`, which [IO-012] AC5 says builds. -/
def CORE_022_strictWf {N : Type} [DecidableEq N] (t : Trans N) : Prop :=
  Builds t ∧ ∀ o, t.out = some o → o.branches.Pairwise (fun a b => ¬ a ⊆ b ∧ ¬ b ⊆ a)

/-- The reference firings of the transitions that pass the stricter check `CORE_022_strictWf`:
an executor that refuses to build an overlapping `Xor`. -/
def core022_refFireStrict : FireRel Nat :=
  fun t m d m' => CORE_022_strictWf t ∧ RefFire t m d m'

/-- ✗ Rejecting a spec the build accepts violates CORE-022 (last line, scoping):
`core022_overlap` builds and is enabled at the empty marking, but an executor that refuses
overlapping alternatives never fires it. -/
@[evidence forbids CORE_022]
theorem CORE_022_forbids_strictBuild : ¬ CORE_022 core022_refFireStrict := by
  intro h
  obtain ⟨_, _, ⟨-, hs⟩, -⟩ :=
    (h core022_overlap core022_overlap_wf).2.2.2 core022_empty (by decide)
  have := hs _ rfl
  simp [Out.branches, cross] at this

/-! ### One mutant per clause: each drops one line, and one counterexample tells it apart -/

/-- Mutant reading of CORE-022 without the input line. -/
def CORE_022_mutant_dropInputs {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t, Builds t →
    (while (fun m => ∃ p, ReadArc t p ∧ ¬ Marked m p), never Fire F t) ∧
    (while (fun m => ∃ p, InhibitorArc t p ∧ Marked m p), never Fire F t) ∧
    (∀ m, Enabled t m → ∃ m', Fire F t m m')

/-- Mutant reading of CORE-022 without the read line. -/
def CORE_022_mutant_dropReads {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t, Builds t →
    (while (fun m => ∃ s ∈ t.core.inputs, m s.place < requiredCount s.card), never Fire F t) ∧
    (while (fun m => ∃ p, InhibitorArc t p ∧ Marked m p), never Fire F t) ∧
    (∀ m, Enabled t m → ∃ m', Fire F t m m')

/-- Mutant reading of CORE-022 without the inhibitor line. -/
def CORE_022_mutant_dropInhibitors {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t, Builds t →
    (while (fun m => ∃ s ∈ t.core.inputs, m s.place < requiredCount s.card), never Fire F t) ∧
    (while (fun m => ∃ p, ReadArc t p ∧ ¬ Marked m p), never Fire F t) ∧
    (∀ m, Enabled t m → ∃ m', Fire F t m m')

/-- Mutant reading of CORE-022 without the last line: the conditions are necessary but no
longer sufficient. -/
def CORE_022_mutant_dropFires {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t, Builds t →
    (while (fun m => ∃ s ∈ t.core.inputs, m s.place < requiredCount s.card), never Fire F t) ∧
    (while (fun m => ∃ p, ReadArc t p ∧ ¬ Marked m p), never Fire F t) ∧
    (while (fun m => ∃ p, InhibitorArc t p ∧ Marked m p), never Fire F t)

/-- Mutant reading of the scoping paragraph: "transitions that build" read through the stricter
check `CORE_022_strictWf`, so an overlapping `Xor` that builds is exempt from the last line. -/
def CORE_022_mutant_strictBuild {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t, CORE_022_strictWf t →
    (while (fun m => ∃ s ∈ t.core.inputs, m s.place < requiredCount s.card), never Fire F t) ∧
    (while (fun m => ∃ p, ReadArc t p ∧ ¬ Marked m p), never Fire F t) ∧
    (while (fun m => ∃ p, InhibitorArc t p ∧ Marked m p), never Fire F t) ∧
    (∀ m, Enabled t m → ∃ m', Fire F t m m')

/-- Ignoring input arcs kills the first mutant: it keeps the read, inhibitor and "able to fire"
lines, but not the input line. -/
@[evidence mutant CORE_022]
theorem CORE_022_mutant_dropInputs_killed :
    CORE_022_mutant_dropInputs core022_ignoresInputs ∧ ¬ CORE_022 core022_ignoresInputs := by
  refine ⟨fun t _ => ⟨?_, ?_, fun m hen => ?_⟩, CORE_022_forbids_ignoresInputs⟩
  · rintro m m' ⟨d, ⟨hr, -⟩, -, -⟩ ⟨p, hp, hn⟩
    exact hn (hr p hp)
  · rintro m m' ⟨d, ⟨-, hi⟩, -, -⟩ ⟨p, hp, hm⟩
    exact hi p hp hm
  · have he := (enabled_iff t m).1 hen
    exact ⟨m, [], ⟨he.2.2, he.2.1⟩, rfl, rfl⟩

/-- Ignoring read arcs kills the second mutant: it keeps the input, inhibitor and "able to fire"
lines, but not the read line. -/
@[evidence mutant CORE_022]
theorem CORE_022_mutant_dropReads_killed :
    CORE_022_mutant_dropReads core022_ignoresReads ∧ ¬ CORE_022 core022_ignoresReads := by
  refine ⟨fun t _ => ⟨?_, ?_, fun m hen => ?_⟩, CORE_022_forbids_ignoresReads⟩
  · rintro m m' ⟨d, ⟨hi, -⟩, -, -⟩ ⟨s, hs, hlt⟩
    have := hi s hs
    omega
  · rintro m m' ⟨d, ⟨-, hh⟩, -, -⟩ ⟨p, hp, hm⟩
    exact hh p hp hm
  · have he := (enabled_iff t m).1 hen
    exact ⟨m, [], ⟨he.1, he.2.1⟩, rfl, rfl⟩

/-- Ignoring inhibitor arcs kills the third mutant: it keeps the input, read and "able to fire"
lines, but not the inhibitor line. -/
@[evidence mutant CORE_022]
theorem CORE_022_mutant_dropInhibitors_killed :
    CORE_022_mutant_dropInhibitors core022_ignoresInhibitors ∧
      ¬ CORE_022 core022_ignoresInhibitors := by
  refine ⟨fun t _ => ⟨?_, ?_, fun m hen => ?_⟩, CORE_022_forbids_ignoresInhibitors⟩
  · rintro m m' ⟨d, ⟨hi, -⟩, -, -⟩ ⟨s, hs, hlt⟩
    have := hi s hs
    omega
  · rintro m m' ⟨d, ⟨-, hr⟩, -, -⟩ ⟨p, hp, hn⟩
    exact hn (hr p hp)
  · have he := (enabled_iff t m).1 hen
    exact ⟨m, [], ⟨he.1, he.2.2⟩, rfl, rfl⟩

/-- The firing relation that never fires kills the fourth mutant: it keeps every "shall not"
line, since it forbids every firing, but an enabled transition does not fire. -/
@[evidence mutant CORE_022]
theorem CORE_022_mutant_dropFires_killed :
    CORE_022_mutant_dropFires core022_neverFire ∧ ¬ CORE_022 core022_neverFire := by
  refine ⟨fun t _ => ⟨?_, ?_, ?_⟩, CORE_022_forbids_neverFire⟩ <;>
    rintro m m' ⟨d, hf, -⟩ <;> exact hf.elim

/-- An executor that also refuses overlapping alternatives kills the scoping mutant: it
satisfies every line for the transitions that pass the stricter check, but `core022_overlap`
builds and never fires. -/
@[evidence mutant CORE_022]
theorem CORE_022_mutant_strictBuild_killed :
    CORE_022_mutant_strictBuild core022_refFireStrict ∧ ¬ CORE_022 core022_refFireStrict := by
  refine ⟨fun t hs => ?_, CORE_022_forbids_strictBuild⟩
  obtain ⟨h1, h2, h3, h4⟩ := CORE_022_reference (N := Nat) t hs.1
  refine ⟨fun m m' hf hc => h1 m m' ?_ hc, fun m m' hf hc => h2 m m' ?_ hc,
    fun m m' hf hc => h3 m m' ?_ hc, fun m hen => ?_⟩
  · obtain ⟨d, -, hd⟩ := hf; exact ⟨d, hd⟩
  · obtain ⟨d, -, hd⟩ := hf; exact ⟨d, hd⟩
  · obtain ⟨d, -, hd⟩ := hf; exact ⟨d, hd⟩
  · obtain ⟨m', d, hd⟩ := h4 m hen
    exact ⟨m', d, hs, hd⟩

/-- Every line of CORE-022 is exercised by the reference semantics, toggling one condition at a
time as the test derivation says: `core022_t` builds, fires from `core022_enabled` (last line),
and does not fire with its input place emptied (second line), its read place emptied (third
line) or its inhibitor place marked (fourth line); each of those markings fails exactly its own
condition. -/
@[evidence nonvacuous CORE_022]
theorem CORE_022_nonvacuous :
    Builds core022_t ∧
      Enabled core022_t core022_enabled ∧
      (∃ m', Fire RefFire core022_t core022_enabled m') ∧
      (∀ m', ¬ Fire RefFire core022_t core022_noInput m') ∧
      (∀ m', ¬ Fire RefFire core022_t core022_noRead m') ∧
      (∀ m', ¬ Fire RefFire core022_t core022_inhibited m') ∧
      (∃ s ∈ core022_t.core.inputs, core022_noInput s.place < requiredCount s.card) ∧
      ¬ Marked core022_noRead 1 ∧ Marked core022_inhibited 2 := by
  refine ⟨core022_t_wf, by decide, ⟨_, [], by decide, ⟨.action 0, rfl⟩, rfl⟩, ?_, ?_, ?_,
    by decide, by decide, by decide⟩ <;>
  · rintro m' ⟨d, hen, -⟩
    exact absurd hen (by decide)

/-- The scoping paragraph separates its two sides on the reference: `Xor(Place(0), Place(0))`
(`core022_dup`) is enabled at the empty marking and has a reference firing, yet does not build,
so CORE-022 does not reach it and the built-only executor never fires it; the overlapping
`Xor(And(0, 1, 2), And(0, 1))` (`core022_overlap`) builds, is enabled at the empty marking and
fires in both. -/
@[evidence nonvacuous CORE_022]
theorem CORE_022_nonvacuous_scope :
    ¬ Builds core022_dup ∧ Enabled core022_dup core022_empty ∧
      (∃ m', Fire RefFire core022_dup core022_empty m') ∧
      (∀ m', ¬ Fire CORE_022_refFireBuilt core022_dup core022_empty m') ∧
      Builds core022_overlap ∧ Enabled core022_overlap core022_empty ∧
      (∃ m', Fire CORE_022_refFireBuilt core022_overlap core022_empty m') := by
  refine ⟨core022_dup_not_wf, by decide, ⟨_, [0], by decide, ⟨.action 0, rfl⟩, rfl⟩,
    fun m' ⟨_, hwf, _⟩ => core022_dup_not_wf hwf, core022_overlap_wf, by decide,
    ⟨_, [0, 1], core022_overlap_wf, by decide, ⟨.action 1, rfl⟩, rfl⟩⟩

end Libpetri.Spec
