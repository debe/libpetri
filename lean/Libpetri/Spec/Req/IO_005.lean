import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.Glossary

set_option linter.missingDocs true

/-!
# IO-005: Input AND-join semantics (`spec/02-input-output-specs.md`)

The requirement is a predicate over an abstract firing relation `F : FireRel N`. The evidence
theorems check it against the reference semantics (`Reference.Fires`, as `RefFire`), against
concrete firing relations that break it (an OR-join, and input arcs that block whatever the
marking), and against one mutant reading per clause.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-- `t` with every input arc removed, and nothing else changed (local to IO-005, not a glossary
term): the transition the input arcs would leave behind if, once satisfied, they gated nothing
further. -/
def withoutInputs {N : Type} (t : Trans N) : Trans N :=
  { t with core := { t.core with inputs := [] } }

/-! ## IO-005: Input AND-join semantics -/

requirement IO_005
  id "IO-005"
  title "Input AND-Join Semantics"
  kind B
  scope "all executors"
  source verbatim "spec/02-input-output-specs.md"
  quote "*While* any input place of a transition holds fewer tokens than the required count of its input arc, the transition *shall not* fire."
        "*While* every input place of a transition that has no match specification ([NU-020]) holds at least the required count of its input arc, the input arcs *shall not* affect whether the transition can fire."
  reading "For every transition t:"
          "for every input arc s of t, t does not fire from a marking in which the input place of s holds fewer tokens than the required count of s;"
          "from a marking m in which every input place of t holds at least the required count of its input arc, t can fire from m exactly when t without its input arcs can fire from m."
  assumes "A firing is read as one step from a marking to a marking (glossary: Fire); timing and priority play no part. 'Can fire' and 'enabled' are both read as 'some firing exists' (to some marking): the input arcs change what a firing consumes, so the second line compares whether t fires, not where it leads."
          "Correlated inputs (ruling D30, extending D16): the second quoted shall sentence is scoped to a transition that has no match specification; a transition with one also needs a name of which every correlated input holds at least its required count of tokens (NU-020). The transitions of the model (Reference.Trans) carry no match specification, so the second line quantifies over every transition. The first quoted shall sentence needs no exclusion: a correlated input that holds fewer tokens than its required count holds fewer tokens of any one name."
          "The opening sentence ('All inputs on a transition are AND-joined: every input arc is a precondition, and all of them must hold in the same marking.') is the two lines together: line 1 makes each input arc a precondition (t does not fire while any one of them is unsatisfied), and both lines fix the single marking m the firing starts from, so 'all of them must hold in the same marking' is read as 'every input arc is satisfied in m'."
          "Input arcs are read from the transition's list of input arcs, every one of them. A transition with two input arcs on one place, which [CORE-030] rejects at build, is gated by both."
          "AC1 (a transition with 3 inputs enables only when all 3 places have sufficient tokens) is the first line, for any number of input arcs, 3 included; the test derivation's 'satisfy all 3; verify enabled' is the second line together with a transition that, without its input arcs, can fire (no read or inhibitor arc blocks it)."
          "AC2 (any one input unsatisfied disables the transition) is the first line."
          "How many tokens an input arc requires (requiredCount) is IO-001 to IO-004 and IO-007, not this block: the statement takes requiredCount as given."
  signoff "2026-11-13 566c1a17d5cf3f37 ai"
  statement : ∀ {N : Type} [DecidableEq N], FireRel N → Prop :=
    fun F => ∀ t : Trans _,
      (∀ s ∈ t.core.inputs,
        while (fun m => TokenCount m s.place < requiredCount s.card), never Fire F t) ∧
      (∀ m, (∀ s ∈ t.core.inputs, requiredCount s.card ≤ TokenCount m s.place) →
        ((∃ m', Fire F t m m') ↔ ∃ m', Fire F (withoutInputs t) m m'))

/- The pinned readable form of IO-005: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.IO_005 : {N : Type} → [DecidableEq N] → FireRel N → Prop :=
fun {N} [DecidableEq N] F =>
  ∀ (t : Reference.Trans N),
    (∀ s ∈ t.core.inputs, while fun m => TokenCount m s.place < requiredCount s.card, never Fire F t) ∧
      ∀ (m : CountMarking N),
        (∀ s ∈ t.core.inputs, requiredCount s.card ≤ TokenCount m s.place) →
          ((∃ m', Fire F t m m') ↔ ∃ m', Fire F (withoutInputs t) m m')
-/
#guard_msgs in #print IO_005

/-! ### Lemmas about the reference semantics -/

/-- Every output spec offers at least one output branch. -/
theorem io005_branches_ne_nil {N : Type} : ∀ o : Out N, o.branches ≠ []
  | .place _ => by simp [Out.branches]
  | .forward _ _ => by simp [Out.branches]
  | .and l r => by
    obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil (io005_branches_ne_nil l)
    obtain ⟨y, ys, hy⟩ := List.exists_cons_of_ne_nil (io005_branches_ne_nil r)
    simp [Out.branches, cross, hx, hy]
  | .xor l r => by simp [Out.branches, io005_branches_ne_nil l]
  | .timeout c => by simpa [Out.branches] using io005_branches_ne_nil c

/-- Under the reference semantics a transition can fire from `m` exactly when it is enabled at
`m`: an enabled transition can always end with its action writing the first output branch. -/
theorem io005_refFire_exists_iff {N : Type} [DecidableEq N] (t : Trans N) (m : CountMarking N) :
    (∃ m', Fire RefFire t m m') ↔ Enabled t m := by
  constructor
  · rintro ⟨m', d, hen, -, -⟩
    exact hen
  · intro hen
    cases ho : t.out with
    | none =>
      exact ⟨_, [], hen, ⟨.action 0, by simp [ho, deposit]⟩, rfl⟩
    | some o =>
      obtain ⟨b, bs, hb⟩ := List.exists_cons_of_ne_nil (io005_branches_ne_nil o)
      exact ⟨_, b, hen, ⟨.action 0, by simp [ho, deposit, hb]⟩, rfl⟩

/-- With every input arc satisfied, `t` and `t` without its input arcs are enabled at the same
markings. -/
theorem io005_enabled_withoutInputs {N : Type} (t : Trans N) (m : CountMarking N)
    (h : ∀ s ∈ t.core.inputs, requiredCount s.card ≤ m s.place) :
    Enabled (withoutInputs t) m ↔ Enabled t m := by
  rw [enabled_iff, enabled_iff]
  simp only [withoutInputs, List.not_mem_nil, false_implies, implies_true, true_and]
  exact ⟨fun h' => ⟨h, h'⟩, fun h' => h'.2⟩

/-- The reference semantics satisfies IO-005: `Seam.enabledNA` requires every input arc's
required count, so an unsatisfied input arc disables the transition; with every input arc
satisfied the remaining conditions (read and inhibitor arcs) are those of the transition without
its input arcs, and an enabled transition can always fire. -/
@[evidence holds IO_005]
theorem IO_005_reference {N : Type} [DecidableEq N] : IO_005 (RefFire (N := N)) := by
  intro t
  refine ⟨fun s hs => ?_, fun m hm => ?_⟩
  · rintro m m' ⟨d, hen, -, -⟩ hlt
    have := ((enabled_iff t m).1 hen).1 s hs
    simp only [TokenCount] at hlt
    omega
  · rw [io005_refFire_exists_iff, io005_refFire_exists_iff]
    exact (io005_enabled_withoutInputs t m hm).symm

/-! ### Examples -/

/-- The transition of AC1: three input arcs, `One` on place `0`, `Exactly(2)` on place `1`,
`All` on place `2`; no other arcs and no output spec. -/
def io005_t : Trans Nat :=
  { core := { name := "t",
              inputs := [⟨0, .one⟩, ⟨1, .exactly 2⟩, ⟨2, .all⟩],
              inhibitors := [], reads := [], resets := [] },
    out := none }

/-- Two of the three input arcs of `io005_t` satisfied: places `0` and `1` hold their required
counts, place `2` is empty. -/
def io005_twoOfThree : Nat → Nat := fun n => if n = 0 then 1 else if n = 1 then 2 else 0

/-- All three input arcs of `io005_t` satisfied. -/
def io005_all : Nat → Nat := fun n => if n = 0 then 1 else if n = 1 then 2 else 1

/-- The marking a reference firing of `t` from `m` leaves when it deposits nothing. -/
def io005_after (t : Trans Nat) (m : Nat → Nat) : Nat → Nat := fireNC m t.core (depProd [])

/-- An OR-join: a transition fires, without regard to its input arcs, as soon as one of its
input arcs is satisfied (or it has none). -/
def io005_orJoinFire : FireRel Nat := fun t m d m' =>
  (t.core.inputs = [] ∨ ∃ s ∈ t.core.inputs, requiredCount s.card ≤ m s.place) ∧
    RefFire (withoutInputs t) m d m'

/-- ✗ An OR-join violates IO-005 (first clause): `io005_t` fires with two of its three input
arcs satisfied. -/
@[evidence forbids IO_005]
theorem IO_005_forbids_orJoin : ¬ IO_005 io005_orJoinFire := by
  intro h
  have hfire : Fire io005_orJoinFire io005_t io005_twoOfThree
      (io005_after (withoutInputs io005_t) io005_twoOfThree) :=
    ⟨[], .inr ⟨⟨0, .one⟩, List.mem_cons_self .., by decide⟩, by decide, ⟨.action 0, rfl⟩, rfl⟩
  exact (h io005_t).1 ⟨2, .all⟩
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) _ _ hfire (by decide)

/-- Input arcs that block whatever the marking: a reference firing of a transition that has no
input arcs, and no firing at all of one that has. -/
def io005_inputsAlwaysBlockFire : FireRel Nat :=
  fun t m d m' => t.core.inputs = [] ∧ RefFire t m d m'

/-- ✗ Input arcs that block their transition although all of them are satisfied violate IO-005
(second clause): `io005_t` cannot fire from `io005_all`, but without its input arcs it can. -/
@[evidence forbids IO_005]
theorem IO_005_forbids_inputsAlwaysBlock : ¬ IO_005 io005_inputsAlwaysBlockFire := by
  intro h
  have hfire : Fire io005_inputsAlwaysBlockFire (withoutInputs io005_t) io005_all
      (io005_after (withoutInputs io005_t) io005_all) :=
    ⟨[], rfl, by decide, ⟨.action 0, rfl⟩, rfl⟩
  obtain ⟨m', d, hne, -⟩ := ((h io005_t).2 io005_all (by decide)).2 ⟨_, hfire⟩
  exact absurd hne (by decide)

/-- Mutant reading of IO-005 that drops the first clause: with every input arc satisfied the
input arcs gate nothing further, but an unsatisfied input arc need not disable the transition. -/
def IO_005_mutant_dropUnsatisfied {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t : Trans N, ∀ m, (∀ s ∈ t.core.inputs, requiredCount s.card ≤ TokenCount m s.place) →
    ((∃ m', Fire F t m m') ↔ ∃ m', Fire F (withoutInputs t) m m')

/-- The OR-join kills the first mutant: it satisfies the mutant (with every input arc satisfied,
the OR-join's condition holds and the firing is that of the transition without its input arcs)
but not IO-005. -/
@[evidence mutant IO_005]
theorem IO_005_mutant_dropUnsatisfied_killed :
    IO_005_mutant_dropUnsatisfied io005_orJoinFire ∧ ¬ IO_005 io005_orJoinFire := by
  refine ⟨fun t m hm => ?_, IO_005_forbids_orJoin⟩
  have hc : t.core.inputs = [] ∨ ∃ s ∈ t.core.inputs, requiredCount s.card ≤ m s.place := by
    cases hi : t.core.inputs with
    | nil => exact .inl rfl
    | cons s _ => exact .inr ⟨s, by simp, hm s (by simp [hi])⟩
  constructor
  · rintro ⟨m', d, -, hf⟩
    exact ⟨m', d, .inl rfl, hf⟩
  · rintro ⟨m', d, -, hf⟩
    exact ⟨m', d, hc, hf⟩

/-- Mutant reading of IO-005 that drops the second clause: an unsatisfied input arc disables the
transition, but satisfied input arcs may still stop it from firing. -/
def IO_005_mutant_dropSatisfied {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t : Trans N, ∀ s ∈ t.core.inputs,
    while (fun m => TokenCount m s.place < requiredCount s.card), never Fire F t

/-- The always-blocking input arcs kill the second mutant: they satisfy the mutant (a transition
with an input arc never fires) but not IO-005. -/
@[evidence mutant IO_005]
theorem IO_005_mutant_dropSatisfied_killed :
    IO_005_mutant_dropSatisfied io005_inputsAlwaysBlockFire ∧
      ¬ IO_005 io005_inputsAlwaysBlockFire := by
  refine ⟨?_, IO_005_forbids_inputsAlwaysBlock⟩
  rintro t s hs m m' ⟨d, hne, -⟩ -
  simp [hne] at hs

/-- Both clauses of IO-005 are exercised by the reference semantics on AC1's transition: with
two of its three input arcs satisfied `io005_t` does not fire (first clause, place `2` short of
its required count), although without its input arcs it does; with all three satisfied it
fires, as it does without its input arcs (second clause). -/
@[evidence nonvacuous IO_005]
theorem IO_005_nonvacuous :
    io005_twoOfThree 2 < requiredCount (Card.all) ∧
      (∀ m', ¬ Fire RefFire io005_t io005_twoOfThree m') ∧
      Fire RefFire (withoutInputs io005_t) io005_twoOfThree
        (io005_after (withoutInputs io005_t) io005_twoOfThree) ∧
      (∀ s ∈ io005_t.core.inputs, requiredCount s.card ≤ io005_all s.place) ∧
      Fire RefFire io005_t io005_all (io005_after io005_t io005_all) ∧
      Fire RefFire (withoutInputs io005_t) io005_all
        (io005_after (withoutInputs io005_t) io005_all) := by
  refine ⟨by decide, ?_, ⟨[], by decide, ⟨.action 0, rfl⟩, rfl⟩, by decide,
    ⟨[], by decide, ⟨.action 0, rfl⟩, rfl⟩, ⟨[], by decide, ⟨.action 0, rfl⟩, rfl⟩⟩
  rintro m' ⟨d, hen, -⟩
  exact absurd hen (by decide)

end Libpetri.Spec
