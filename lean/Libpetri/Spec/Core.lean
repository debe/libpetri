import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.Glossary
import Libpetri.Spec.Text.CORE_031

set_option linter.missingDocs true

/-!
# Core model: arc requirements (`spec/01-core-model.md`)

Each requirement is a predicate over an abstract firing relation `F : FireRel N`. The evidence
theorems check it against the reference semantics (`Reference.Fires`, as `RefFire`), against a
concrete firing relation that breaks it, and against a mutant reading of the text.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## CORE-031: Inhibitor arc -/

requirement CORE_031
  id "CORE-031"
  title "Inhibitor arc"
  kind B
  scope "all executors"
  source verbatim "spec/01-core-model.md"
  covers CORE_031.s1, CORE_031.s2
  reading "For every transition t and every inhibitor place p of t:"
          "t does not fire from a marking in which p is marked;"
          "from a marking m in which p is unmarked, t fires to m' exactly when t without its inhibitor arcs on p fires from m to m'."
  assumes "A firing is read as one step from a marking to a marking (glossary: Fire); timing and priority play no part. 'Can fire' and 'enabled' are both read as 'some firing exists'."
          "AC1 (inhibitor place empty, enablement unaffected) is the second line: with p unmarked, removing the inhibitor arcs on p changes neither whether t fires nor where it leads."
          "AC2 (inhibitor place marked, transition disabled) is the first line."
          "AC3, first half (a firing consumes nothing through its inhibitor arcs): by the second line a firing of t from a marking with p unmarked is a firing of t without its arcs on p, so those arcs add nothing to what it consumes or produces; by the first line t does not fire when p is marked. AC3, second half: what a firing of another transition consumes through an input arc on p is CORE-030's subject, not this block's."
          "Inside a firing pass, the marking a transition fires from in the sense of these lines is the pass-visible marking, not the live one (EXEC-003 AC4, ruling D75 (a)): 'p is marked' is judged on it, so a token a synchronous action deposited into p earlier in the same pass does not block t, and t may fire later in that pass. Rust (recheck_can_fire in rust/libpetri-runtime/src/bitmap_backend.rs on the pass snapshot, inhibitors tested on that snapshot by can_enable_bitmap in compiled_net.rs) and Java (canEnable on fireScanBitmap) start such a transition, as EXEC_003_nonvacuous's fifth part shows on the reference executor (T4); TypeScript settles every firing in step 1, so its passes have no same-pass deposit. EXEC_003_start_inhibitors states the start half over the executor: a start happens only with every inhibitor place empty in the pass-visible marking. The bridge from a reference start to this one-step firing relation is recorded with the integrator."
  signoff "2026-11-13 13bd1b82094c56b6 ai"
  statement : ∀ {N : Type} [DecidableEq N], FireRel N → Prop :=
    fun F => ∀ t p, InhibitorArc t p →
      (while (fun m => Marked m p), never Fire F t) ∧
      (∀ m m', ¬ Marked m p → (Fire F t m m' ↔ Fire F (withoutInhibitor t p) m m'))

/- The pinned readable form of CORE-031: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CORE_031 : {N : Type} → [DecidableEq N] → FireRel N → Prop :=
fun {N} [DecidableEq N] F =>
  ∀ (t : Reference.Trans N) (p : N),
    InhibitorArc t p →
      (while fun m => Marked m p, never Fire F t) ∧
        ∀ (m : CountMarking N) (m' : N → ℕ), ¬Marked m p → (Fire F t m m' ↔ Fire F (withoutInhibitor t p) m m')
-/
#guard_msgs in #print CORE_031

/-- With `p` unmarked, `t` and `t` without its inhibitor arcs on `p` are enabled at the same
markings: the dropped arcs all test `p`. -/
theorem enabledNA_withoutInhibitor {N : Type} [DecidableEq N] (t : Trans N) (p : N)
    (m : N → Nat) (hp : m p = 0) :
    enabledNA m (withoutInhibitor t p).core = enabledNA m t.core := by
  have : (t.core.inhibitors.filter (· ≠ p)).all (fun q => m q == 0) =
      t.core.inhibitors.all (fun q => m q == 0) := by
    rw [Bool.eq_iff_iff]
    simp only [List.all_eq_true, List.mem_filter, ne_eq, decide_not, Bool.not_eq_eq_eq_not,
      Bool.not_true, decide_eq_false_iff_not, beq_iff_eq]
    refine ⟨fun h q hq => ?_, fun h q hq => h q hq.1⟩
    by_cases e : q = p
    · exact e ▸ hp
    · exact h q ⟨hq, e⟩
  simp only [enabledNA, withoutInhibitor, this]

/-- The reference semantics satisfies CORE-031: `Seam.enabledNA` requires every inhibitor place
to be empty, so `t` does not fire while `p` is marked; and the firing effect (`Seam.nconsumed`,
`Seam.fireNC`) and the deposits read inputs, resets and the output spec only, so with `p`
unmarked removing the inhibitor arcs on `p` changes nothing. -/
@[evidence holds CORE_031]
theorem CORE_031_reference {N : Type} [DecidableEq N] : CORE_031 (RefFire (N := N)) := by
  intro t p hp
  refine ⟨?_, fun m m' hm => ?_⟩
  · rintro m m' ⟨d, hen, -, -⟩ hm
    exact ((enabled_iff t m).1 hen).2.1 p hp hm
  · have h0 : m p = 0 := by simpa [Marked] using hm
    have he := enabledNA_withoutInhibitor t p m h0
    constructor
    · rintro ⟨d, hen, hd, hm'⟩
      exact ⟨d, he.trans hen, hd, hm'⟩
    · rintro ⟨d, hen, hd, hm'⟩
      exact ⟨d, he.symm.trans hen, hd, hm'⟩

/-! ### Examples over a one-place net -/

/-- The one transition of the examples: no inputs, one inhibitor arc on place `0`, no output
spec. -/
def core031_t : Trans Nat :=
  { core := { name := "t", inputs := [], inhibitors := [0], reads := [], resets := [] },
    out := none }

/-- The marking of the examples in which place `0` holds one token. -/
def core031_marked : Nat → Nat := fun _ => 1

/-- The marking of the examples in which every place is empty. -/
def core031_empty : Nat → Nat := fun _ => 0

/-- A firing relation that ignores inhibitor arcs: a reference firing of the transition with its
inhibitor arcs removed. -/
def core031_ignoresInhibitorFire : FireRel Nat :=
  fun t => RefFire { t with core := { t.core with inhibitors := [] } }

/-- ✗ Ignoring the inhibitor arc violates CORE-031 (first clause): `core031_t` fires while
place `0` is marked. -/
@[evidence forbids CORE_031]
theorem CORE_031_forbids_ignoresInhibitor : ¬ CORE_031 core031_ignoresInhibitorFire := by
  intro h
  have hfire : Fire core031_ignoresInhibitorFire core031_t core031_marked core031_marked :=
    ⟨[], by decide, ⟨.action 0, rfl⟩, by funext n; simp [fireNC, depProd, nconsumed, nspecAt,
      core031_t]⟩
  exact (h core031_t 0 (by decide)).1 _ _ hfire (by decide)

/-- A firing relation in which an inhibitor arc blocks its transition whatever the marking: a
reference firing of a transition that has no inhibitor arcs, and no firing at all of one that
has. -/
def core031_inhibitorAlwaysBlocksFire : FireRel Nat :=
  fun t m d m' => t.core.inhibitors = [] ∧ RefFire t m d m'

/-- ✗ An inhibitor arc that blocks its transition while its place is empty violates CORE-031
(second clause): `core031_t` cannot fire from the empty marking, but without its inhibitor arc
it can. -/
@[evidence forbids CORE_031]
theorem CORE_031_forbids_inhibitorAlwaysBlocks :
    ¬ CORE_031 core031_inhibitorAlwaysBlocksFire := by
  intro h
  have hfire : Fire core031_inhibitorAlwaysBlocksFire (withoutInhibitor core031_t 0)
      core031_empty core031_empty :=
    ⟨[], by decide, by decide, ⟨.action 0, rfl⟩, by funext n; simp [fireNC, depProd, nconsumed,
      nspecAt, withoutInhibitor, core031_t, core031_empty]⟩
  obtain ⟨d, hne, -⟩ := ((h core031_t 0 (by decide)).2 core031_empty core031_empty
    (by decide)).2 hfire
  exact absurd hne (by decide)

/-- Mutant reading of CORE-031 that drops the first clause: with the inhibitor place unmarked
the arc changes nothing, but a marked inhibitor place does not stop the transition. -/
def CORE_031_mutant_dropMarked {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t p, InhibitorArc t p →
    ∀ m m', ¬ Marked m p → (Fire F t m m' ↔ Fire F (withoutInhibitor t p) m m')

/-- The firing that changes nothing: every transition may fire from every marking, depositing
nothing and leaving the marking as it is. -/
def core031_idleFire : FireRel Nat := fun _ m d m' => d = [] ∧ m' = m

/-- The idle firing kills the first mutant: it satisfies the mutant (whether a transition fires
does not depend on its arcs at all) but not CORE-031 (`core031_t` fires while its inhibitor
place is marked). -/
@[evidence mutant CORE_031]
theorem CORE_031_mutant_dropMarked_killed :
    CORE_031_mutant_dropMarked core031_idleFire ∧ ¬ CORE_031 core031_idleFire := by
  refine ⟨?_, fun h => ?_⟩
  · intro t p _ m m' _
    exact Iff.rfl
  · exact (h core031_t 0 (by decide)).1 core031_marked core031_marked
      ⟨[], rfl, rfl⟩ (by decide)

/-- Mutant reading of CORE-031 that drops the second clause: a marked inhibitor place stops the
transition, but an unmarked one may still change whether, and where, it fires. -/
def CORE_031_mutant_dropUnmarked {N : Type} (F : FireRel N) : Prop :=
  ∀ t p, InhibitorArc t p → (while (fun m => Marked m p), never Fire F t)

/-- The always-blocking firing kills the second mutant: it satisfies the mutant (a transition
with an inhibitor arc never fires) but not CORE-031 (`core031_t` does not fire from the empty
marking although it fires there without its inhibitor arc). -/
@[evidence mutant CORE_031]
theorem CORE_031_mutant_dropUnmarked_killed :
    CORE_031_mutant_dropUnmarked core031_inhibitorAlwaysBlocksFire ∧
      ¬ CORE_031 core031_inhibitorAlwaysBlocksFire := by
  refine ⟨?_, CORE_031_forbids_inhibitorAlwaysBlocks⟩
  rintro t p hp m m' ⟨d, hne, -⟩ -
  have hp' : p ∈ t.core.inhibitors := hp
  simp [hne] at hp'

/-- Both clauses of CORE-031 are exercised by the reference semantics: `core031_t` has an
inhibitor arc; it fires from the empty marking, as it does without its inhibitor arc (second
clause, with the place unmarked); and it does not fire from the marking in which its inhibitor
place is marked, although without its inhibitor arc it does (first clause). -/
@[evidence nonvacuous CORE_031]
theorem CORE_031_nonvacuous :
    InhibitorArc core031_t 0 ∧
      Fire RefFire core031_t core031_empty core031_empty ∧
      Fire RefFire (withoutInhibitor core031_t 0) core031_empty core031_empty ∧
      ¬ Fire RefFire core031_t core031_marked core031_marked ∧
      Fire RefFire (withoutInhibitor core031_t 0) core031_marked core031_marked := by
  refine ⟨by decide, ⟨[], by decide, ⟨.action 0, rfl⟩, ?_⟩, ⟨[], by decide, ⟨.action 0, rfl⟩, ?_⟩,
    ?_, ⟨[], by decide, ⟨.action 0, rfl⟩, ?_⟩⟩
  · funext n; simp [fireNC, depProd, nconsumed, nspecAt, core031_t, core031_empty]
  · funext n; simp [fireNC, depProd, nconsumed, nspecAt, withoutInhibitor, core031_t,
      core031_empty]
  · rintro ⟨d, hen, -⟩
    exact absurd hen (by decide)
  · funext n; simp [fireNC, depProd, nconsumed, nspecAt, withoutInhibitor, core031_t,
      core031_marked]

end Libpetri.Spec
