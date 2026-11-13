import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.Glossary
import Libpetri.Spec.Text.CORE_033

set_option linter.missingDocs true

/-!
# CORE-033: Read arc multi-reader (`spec/01-core-model.md`)

A predicate over an abstract firing relation `F : FireRel N`, checked against the reference
semantics (`RefFire`), against concrete firing relations that break it, against one mutant
reading per clause, and against two read-arc bugs that it allows because they are CORE-032's
subject.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-- `t` with every read arc on `p` removed, and nothing else changed: the transition that a read
arc on `p` which played no part in whether `t` can fire would leave behind. (Local to CORE-033,
so that this module does not import CORE-032's; the same definition as CORE-032's `withoutRead`
and the read-arc counterpart of the glossary's `withoutInhibitor`: a glossary candidate.) -/
def core033_withoutRead {N : Type} [DecidableEq N] (t : Trans N) (p : N) : Trans N :=
  { t with core := { t.core with reads := t.core.reads.filter (· ≠ p) } }

/-! ## CORE-033: Read arc multi-reader -/

requirement CORE_033
  id "CORE-033"
  title "Read arc multi-reader"
  kind B
  scope "all executors"
  source verbatim "spec/01-core-model.md"
  covers CORE_033.s1, CORE_033.s2
  reading "For every transition t and every read place p of t, at every marking m in which p is marked:"
          "if t without its read arcs on p can fire from m, then t can fire from m;"
          "for every two transitions t₁, t₂ with read arcs on p, where t₁ has no input arc and no reset arc on p:"
          "after every firing of t₁ from a marking m in which p is marked to m', if t₂ without its read arcs on p can fire from m', then t₂ can fire from m'."
  assumes "A firing is read as one step from a marking to a marking (glossary: Fire); timing and priority play no part. 'Can fire' and 'enabled' are both read as 'some firing exists', to any target marking."
          "AC1 (two readers both enabled when the place has tokens) is the first two lines: whether a firing relation lets t fire from m depends on t and m alone, so 'both enabled' is each enabled, and each reader's read arc on a marked p adds no condition. The text does not claim a reader fires with its other arcs unsatisfied, hence the comparison with the reader without its read arcs on p."
          "AC2 (both can fire without conflict) is read in the untimed interleaving: firing one reader does not take away, through p, the other reader's ability to fire (last two lines). Conflicts through other places (t₁ consuming an input of t₂, or depositing into an inhibitor place of t₂) are not this block's subject."
          "The restriction to a t₁ with no input arc and no reset arc on p is an interpretation choice: such a t₁ removes tokens from p (CORE-030, CORE-034; EXEC-012 allows a read arc and a reset arc on one place), so it can disable the other reader; the text's reason 'read arcs do not consume tokens' covers the read arcs only."
          "t₁ and t₂ may be the same transition: a reader firing twice in a row is covered too. In the untimed step model this is no stronger than the case of two transitions with the same arcs."
          "The read token's value reaching the action (CORE-032 AC3, EXEC-012) is below the count granularity and not this block's subject."
          "Both clauses assume p is marked: a reader firing from an empty read place is CORE-032 AC1 (its first clause), not this block's subject. A firing relation that ignores read arcs satisfies this block (CORE_033_allows_ignoresRead)."
          "Clause 2 asks only that p stay marked for the other reader, which is what 'no conflict' needs. That a read leaves the count of p unchanged (apart from deposits) is CORE-032 AC2 (its third clause); the 'since read arcs do not consume tokens' of this text is that requirement's reason, not a second acceptance criterion here. A read that takes one token whenever two or more are present satisfies this block (CORE_033_allows_readTakesSurplus)."
          "Each firing is one atomic step, so a read token held or reserved while the reader's action runs (taken at the start and put back at completion, or a per-place lock on read places), which would keep two readers from being in flight together, cannot be expressed here. In-flight concurrency of readers needs a start/complete step model (CONC, EXEC); a take-and-put read that reorders the FIFO queue is below count granularity (EXEC-012)."
  signoff "2026-11-13 a864c7bea1b325a9 ai"
  statement : ∀ {N : Type} [DecidableEq N], FireRel N → Prop :=
    fun F =>
      (∀ t p, ReadArc t p → ∀ m, Marked m p →
        (∃ m', Fire F (core033_withoutRead t p) m m') → ∃ m', Fire F t m m') ∧
      (∀ t₁ t₂ p, ReadArc t₁ p → ReadArc t₂ p → (∀ c, ¬ InputArc t₁ p c) → ¬ ResetArc t₁ p →
        on Fire F t₁, shall (fun m m' => Marked m p →
          (∃ m'', Fire F (core033_withoutRead t₂ p) m' m'') → ∃ m'', Fire F t₂ m' m''))

/- The pinned readable form of CORE-033: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CORE_033 : {N : Type} → [DecidableEq N] → FireRel N → Prop :=
fun {N} [DecidableEq N] F =>
  (∀ (t : Reference.Trans N) (p : N),
      ReadArc t p →
        ∀ (m : CountMarking N), Marked m p → (∃ m', Fire F (core033_withoutRead t p) m m') → ∃ m', Fire F t m m') ∧
    ∀ (t₁ t₂ : Reference.Trans N) (p : N),
      ReadArc t₁ p →
        ReadArc t₂ p →
          (∀ (c : Card), ¬InputArc t₁ p c) →
            ¬ResetArc t₁ p →
              on Fire F t₁, shall fun m m' =>
                Marked m p → (∃ m'', Fire F (core033_withoutRead t₂ p) m' m'') → ∃ m'', Fire F t₂ m' m''
-/
#guard_msgs in #print CORE_033

/-- Under the reference semantics, a read arc on a marked place adds no condition: if `t`
without its read arcs on `p` fires from `m` to `m'`, then `t` fires from `m` to `m'` with the
same deposit (the read arcs play no part in `Seam.nconsumed` or `Seam.fireNC`). -/
theorem core033_ref_fire_of_withoutRead {N : Type} [DecidableEq N] {t : Trans N} {p : N}
    {m m' : N → Nat} (hp : Marked m p) (h : Fire RefFire (core033_withoutRead t p) m m') :
    Fire RefFire t m m' := by
  obtain ⟨d, hen, hd, hm'⟩ := h
  have hen' : Enabled t m := by
    obtain ⟨hi, hh, hr⟩ := (enabled_iff _ m).1 hen
    refine (enabled_iff t m).2 ⟨hi, hh, fun q hq => ?_⟩
    by_cases e : q = p
    · exact e ▸ hp
    · exact hr q (List.mem_filter.2 ⟨hq, by simpa using e⟩)
  exact ⟨d, hen', hd, hm'⟩

/-- The reference semantics satisfies CORE-033: a read arc on a marked place adds no condition
(`core033_ref_fire_of_withoutRead`), and a firing of a reader with no input arc and no reset
arc on `p` consumes nothing from `p` and does not reset it (`refFire_apply`), so `p` stays
marked for the other reader. -/
@[evidence holds CORE_033]
theorem CORE_033_reference {N : Type} [DecidableEq N] : CORE_033 (RefFire (N := N)) := by
  refine ⟨fun t p _ m hp ⟨m', h⟩ => ⟨m', core033_ref_fire_of_withoutRead hp h⟩, ?_⟩
  intro t₁ t₂ p _ _ hin hres m m' ⟨d, h⟩ hp ⟨m'', h2⟩
  have hc : Consumes t₁ m p = 0 := by
    rw [consumes_eq]
    cases hs : nspecAt t₁.core p with
    | none => rfl
    | some s => exact absurd ⟨s, hs, rfl⟩ (hin s.card)
  have hp' : Marked m' p := by
    have := refFire_apply h p
    simp only [hres, if_false, hc, Nat.sub_zero] at this
    simp only [Marked] at hp ⊢
    omega
  exact ⟨m'', core033_ref_fire_of_withoutRead hp' h2⟩

/-! ### Examples over a one-place net -/

/-- The first reader of the examples: one read arc on place `0`, no other arc, no output
spec. -/
def core033_t₁ : Trans Nat :=
  { core := { name := "t1", inputs := [], inhibitors := [], reads := [0], resets := [] },
    out := none }

/-- The second reader of the examples: like `core033_t₁`, under another name. -/
def core033_t₂ : Trans Nat :=
  { core := { name := "t2", inputs := [], inhibitors := [], reads := [0], resets := [] },
    out := none }

/-- The marking of the examples in which every place holds one token. -/
def core033_one : Nat → Nat := fun _ => 1

/-- `t` with each read arc turned into a `One` input arc on the same place: a read that
consumes. -/
def core033_readsAsInputs {N : Type} (t : Trans N) : Trans N :=
  { t with core := { t.core with
      inputs := t.core.inputs ++ t.core.reads.map (fun q => ⟨q, .one⟩), reads := [] } }

/-- A firing relation in which a read arc consumes one token, as a `One` input arc would. -/
def core033_readConsumesFire : FireRel Nat := fun t => RefFire (core033_readsAsInputs t)

/-- The marking after `core033_t₁` fires under `core033_readConsumesFire` from
`core033_one`. -/
def core033_drained : Nat → Nat :=
  fireNC core033_one (core033_readsAsInputs core033_t₁).core (depProd [])

/-- The reader `core033_t₁` has no input arc on place `0`. -/
theorem core033_t₁_noInput : ∀ c, ¬ InputArc core033_t₁ 0 c := by
  rintro c ⟨s, hs, -⟩
  simp [nspecAt, core033_t₁] at hs

/-- ✗ A read that consumes violates CORE-033 (second clause): `core033_t₁` fires from
`core033_one` and drains place `0`, after which `core033_t₂` cannot fire although it can
without its read arc. -/
@[evidence forbids CORE_033]
theorem CORE_033_forbids_readConsumes : ¬ CORE_033 core033_readConsumesFire := by
  intro h
  have hfire : Fire core033_readConsumesFire core033_t₁ core033_one core033_drained :=
    ⟨[], by decide, ⟨.action 0, rfl⟩, rfl⟩
  have hfree : ∃ m'', Fire core033_readConsumesFire (core033_withoutRead core033_t₂ 0)
      core033_drained m'' :=
    ⟨_, [], by decide, ⟨.action 0, rfl⟩, rfl⟩
  obtain ⟨_, _, hen, -⟩ := h.2 core033_t₁ core033_t₂ 0 (by decide) (by decide)
    core033_t₁_noInput (by decide) _ _ hfire (by decide) hfree
  exact absurd hen (by decide)

/-- A firing relation in which a read arc blocks its transition whatever the marking: a
reference firing of a transition that has no read arcs, and no firing at all of one that
has. -/
def core033_readAlwaysBlocksFire : FireRel Nat :=
  fun t m d m' => t.core.reads = [] ∧ RefFire t m d m'

/-- ✗ A read arc that blocks its transition while its place is marked violates CORE-033 (first
clause): `core033_t₁` cannot fire from `core033_one`, but without its read arc it can. -/
@[evidence forbids CORE_033]
theorem CORE_033_forbids_readAlwaysBlocks : ¬ CORE_033 core033_readAlwaysBlocksFire := by
  intro h
  obtain ⟨_, _, hne, -⟩ := h.1 core033_t₁ 0 (by decide) core033_one (by decide)
    ⟨_, [], by decide, by decide, ⟨.action 0, rfl⟩, rfl⟩
  exact absurd hne (by decide)

/-- Mutant reading of CORE-033 that drops the first clause: a reader keeps the place marked for
the others, but a read arc on a marked place may still stop its own transition. -/
def CORE_033_mutant_dropEnabled {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t₁ t₂ p, ReadArc t₁ p → ReadArc t₂ p → (∀ c, ¬ InputArc t₁ p c) → ¬ ResetArc t₁ p →
    on Fire F t₁, shall (fun m m' => Marked m p →
      (∃ m'', Fire F (core033_withoutRead t₂ p) m' m'') → ∃ m'', Fire F t₂ m' m'')

/-- The always-blocking firing kills the first mutant: it satisfies the mutant (a transition
with a read arc never fires, so no reader's firing takes anything away) but not CORE-033
(`core033_t₁` does not fire from `core033_one`). -/
@[evidence mutant CORE_033]
theorem CORE_033_mutant_dropEnabled_killed :
    CORE_033_mutant_dropEnabled core033_readAlwaysBlocksFire ∧
      ¬ CORE_033 core033_readAlwaysBlocksFire := by
  refine ⟨?_, CORE_033_forbids_readAlwaysBlocks⟩
  rintro t₁ t₂ p hp - - - m m' ⟨d, hne, -⟩
  have hp' : p ∈ t₁.core.reads := hp
  simp [hne] at hp'

/-- Mutant reading of CORE-033 that drops the second clause: a read arc on a marked place adds
no condition, but firing one reader may take the place away from the others. -/
def CORE_033_mutant_dropNoConflict {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t p, ReadArc t p → ∀ m, Marked m p →
    (∃ m', Fire F (core033_withoutRead t p) m m') → ∃ m', Fire F t m m'

/-- The consuming read kills the second mutant: it satisfies the mutant (a `One` input on a
marked place adds no condition) but not CORE-033 (`core033_t₁` drains place `0` and blocks
`core033_t₂`). -/
@[evidence mutant CORE_033]
theorem CORE_033_mutant_dropNoConflict_killed :
    CORE_033_mutant_dropNoConflict core033_readConsumesFire ∧
      ¬ CORE_033 core033_readConsumesFire := by
  refine ⟨?_, CORE_033_forbids_readConsumes⟩
  rintro t p - m hp ⟨_, d, hen, -, -⟩
  have hen' : Enabled (core033_readsAsInputs t) m := by
    obtain ⟨hi, hh, -⟩ := (enabled_iff _ m).1 hen
    refine (enabled_iff _ m).2 ⟨fun s hs => ?_, hh, by simp [core033_readsAsInputs]⟩
    simp only [core033_readsAsInputs, List.mem_append, List.mem_map] at hs
    rcases hs with hs | ⟨q, hq, rfl⟩
    · exact hi s (by simp [core033_readsAsInputs, core033_withoutRead, hs])
    · by_cases e : q = p
      · subst e
        simpa [requiredCount, Card.required, Marked, Nat.one_le_iff_ne_zero] using hp
      · exact hi ⟨q, .one⟩ (by
          simp [core033_readsAsInputs, core033_withoutRead, List.mem_filter, hq, e])
  obtain ⟨ch, d', hd'⟩ := exists_deposit (nconsumed m (core033_readsAsInputs t).core)
    (core033_readsAsInputs t).out
  exact ⟨_, d', hen', ⟨ch, hd'⟩, rfl⟩

/-! ### Read-arc bugs this block allows (CORE-032's subject) -/

/-- A firing relation that ignores read arcs: a reference firing of the transition with its read
arcs removed. -/
def core033_ignoresReadFire : FireRel Nat :=
  fun t => RefFire { t with core := { t.core with reads := [] } }

/-- The marking of the examples in which every place is empty. -/
def core033_empty : Nat → Nat := fun _ => 0

/-- ✓ CORE-033 allows a firing relation that ignores read arcs, under which `core033_t₁` fires
from the empty marking: both clauses assume the read place is marked, so a reader firing from
an empty read place is outside this block. CORE-032's first clause rejects it (CORE-032's
`CORE_032_forbids_ignoresRead`, for the same relation). -/
@[evidence allows CORE_033]
theorem CORE_033_allows_ignoresRead :
    CORE_033 core033_ignoresReadFire ∧
      Fire core033_ignoresReadFire core033_t₁ core033_empty core033_empty := by
  refine ⟨⟨fun t p _ m _ ⟨m', d, h⟩ => ⟨m', d, h⟩, ?_⟩,
    ⟨[], by decide, ⟨.action 0, rfl⟩, by
      funext n; simp [fireNC, depProd, nconsumed, nspecAt, core033_t₁, core033_empty]⟩⟩
  intro t₁ t₂ p _ _ _ _ m m' _ _ ⟨m'', d, h⟩
  exact ⟨m'', d, h⟩

/-- A firing relation in which a read takes one token from each read place that holds two or
more after the reference firing, and leaves the last one. -/
def core033_readTakesSurplusFire : FireRel Nat := fun t m d m' => ∃ m₀, RefFire t m d m₀ ∧
  m' = fun q => if q ∈ t.core.reads ∧ 2 ≤ m₀ q then m₀ q - 1 else m₀ q

/-- The marking of the examples in which every place holds two tokens. -/
def core033_two : Nat → Nat := fun _ => 2

/-- ✓ CORE-033 allows a read that takes surplus tokens: the read place never becomes empty, so
no reader blocks another ('no conflict' holds), yet `core033_t₁` fires from `core033_two`,
deposits nothing and leaves one token in place `0`. CORE-032's third clause (the count after a
firing is the count before plus the deposits) rejects it. -/
@[evidence allows CORE_033]
theorem CORE_033_allows_readTakesSurplus :
    CORE_033 core033_readTakesSurplusFire ∧
      core033_readTakesSurplusFire core033_t₁ core033_two []
        (fun n => if n = 0 then 1 else 2) := by
  refine ⟨⟨fun t p _ m hp ⟨m', d, m₀, h, _⟩ => ?_, ?_⟩, ?_⟩
  · obtain ⟨d', h'⟩ := core033_ref_fire_of_withoutRead hp ⟨d, h⟩
    exact ⟨_, d', m₀, h', rfl⟩
  · intro t₁ t₂ p _ _ hin hres m m' ⟨d, m₀, h, hm'⟩ hp ⟨m'', d₂, m₁, h₂, _⟩
    have hc : Consumes t₁ m p = 0 := by
      rw [consumes_eq]
      cases hs : nspecAt t₁.core p with
      | none => rfl
      | some s => exact absurd ⟨s, hs, rfl⟩ (hin s.card)
    have hp₀ : Marked m₀ p := by
      have := refFire_apply h p
      simp only [hres, if_false, hc, Nat.sub_zero] at this
      simp only [Marked] at hp ⊢
      omega
    have hp' : Marked m' p := by
      subst hm'
      simp only [Marked] at hp₀ ⊢
      split <;> omega
    obtain ⟨d₃, h₃⟩ := core033_ref_fire_of_withoutRead hp' ⟨d₂, h₂⟩
    exact ⟨_, d₃, m₁, h₃, rfl⟩
  · refine ⟨core033_two, ⟨by decide, ⟨.action 0, rfl⟩, by
      funext n; simp [fireNC, depProd, nconsumed, nspecAt, core033_t₁, core033_two]⟩, ?_⟩
    funext n
    by_cases e : n = 0
    · subst e; simp [core033_t₁, core033_two]
    · simp [core033_t₁, core033_two, e]

/-- Both clauses of CORE-033 are exercised by the reference semantics: `core033_t₁` and
`core033_t₂` both read place `0`, which `core033_one` marks; `core033_t₁` without its read arc
fires from `core033_one`, and so does `core033_t₁` (first clause); `core033_t₁` fires from
`core033_one` back to `core033_one`, from which `core033_t₂` without its read arc and
`core033_t₂` both fire (second clause). -/
@[evidence nonvacuous CORE_033]
theorem CORE_033_nonvacuous :
    ReadArc core033_t₁ 0 ∧ ReadArc core033_t₂ 0 ∧ Marked core033_one 0 ∧
      Fire RefFire (core033_withoutRead core033_t₁ 0) core033_one core033_one ∧
      Fire RefFire core033_t₁ core033_one core033_one ∧
      Fire RefFire (core033_withoutRead core033_t₂ 0) core033_one core033_one ∧
      Fire RefFire core033_t₂ core033_one core033_one := by
  refine ⟨by decide, by decide, by decide, ⟨[], by decide, ⟨.action 0, rfl⟩, ?_⟩,
    ⟨[], by decide, ⟨.action 0, rfl⟩, ?_⟩, ⟨[], by decide, ⟨.action 0, rfl⟩, ?_⟩,
    ⟨[], by decide, ⟨.action 0, rfl⟩, ?_⟩⟩ <;>
  · funext n
    simp [fireNC, depProd, nconsumed, nspecAt, core033_withoutRead, core033_t₁, core033_t₂,
      core033_one]

end Libpetri.Spec
