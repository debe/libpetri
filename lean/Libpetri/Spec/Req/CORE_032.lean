import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.Glossary
import Libpetri.Spec.Text.CORE_032

set_option linter.missingDocs true

/-!
# CORE-032: Read arc (`spec/01-core-model.md`)

A predicate over an abstract firing relation `F : FireRel N`, checked against the reference
semantics (`Reference.Fires`, as `RefFire`), against concrete firing relations that break it,
and against one mutant reading per clause.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-- `t` with every read arc on `p` removed, and nothing else changed: the transition a read arc
on `p` that never gated would leave behind. (Local to CORE-032; the read-arc counterpart of the
glossary's `withoutInhibitor`.) -/
def withoutRead [DecidableEq N] (t : Trans N) (p : N) : Trans N :=
  { t with core := { t.core with reads := t.core.reads.filter (· ≠ p) } }

/-! ## CORE-032: Read arc -/

requirement CORE_032
  id "CORE-032"
  title "Read Arc"
  kind B
  scope "all executors"
  source verbatim "spec/01-core-model.md"
  covers CORE_032.s1, CORE_032.s2, CORE_032.s3
  reading "For every transition t and every read place p of t:"
          "t does not fire from a marking in which p is unmarked;"
          "from a marking m in which p is marked, t fires to m' exactly when t without its read arcs on p fires from m to m';"
          "if t has no input arc and no reset arc on p, every firing of t from m that deposits d and leaves m' has m'(p) = m(p) + (tokens d puts in p)."
  assumes "A firing is read as one step from a marking to a marking (glossary: Fire); timing and priority play no part. 'Can fire' and 'enabled' are both read as 'some firing exists'."
          "AC1 (read place must have tokens for enablement) is the second line."
          "AC2 (token remains in place after firing) is the fourth line, for a read place the transition neither consumes from nor resets. A place that is also an input place or a reset place of the same transition loses tokens through those arcs ([CORE-030], [CORE-034], [EXEC-013] AC4); the third line says the read arc adds nothing to that loss."
          "AC3 (action receives the read token value) is not encoded: the firing relation works on token counts and has no action or token values. Which token is read is [EXEC-012]'s subject, the context access [CORE-061]'s."
          "'Marked' is read as 'holds at least one token' (glossary: Marked), the spec's 'at least one token for enablement'."
          "AC2's 'token remains' is encoded at count level only. A firing that takes the read token out of p and puts it, or another token, back in the same step leaves the same counts and satisfies this statement, but moves the token to the FIFO tail and changes its timestamp. Token identity, FIFO position and timestamp are below the count granularity of the firing relation, as for CORE-030 AC2; they belong to [EXEC-012] ('both A and B remain after firing', the oldest is peeked), and no count-level block can catch the bug."
  signoff "2026-11-13 7fd3f8d88a4203c9 ai"
  statement : ∀ {N : Type} [DecidableEq N], FireRel N → Prop :=
    fun F => ∀ t p, ReadArc t p →
      (while (fun m => ¬ Marked m p), never Fire F t) ∧
      (∀ m m', Marked m p → (Fire F t m m' ↔ Fire F (withoutRead t p) m m')) ∧
      ((∀ c, ¬ InputArc t p c) → ¬ ResetArc t p →
        ∀ m d m', F t m d m' → m' p = m p + Deposits d p)

/- The pinned readable form of CORE-032: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CORE_032 : {N : Type} → [DecidableEq N] → FireRel N → Prop :=
fun {N} [DecidableEq N] F =>
  ∀ (t : Reference.Trans N) (p : N),
    ReadArc t p →
      (while fun m => ¬Marked m p, never Fire F t) ∧
        (∀ (m : CountMarking N) (m' : N → ℕ), Marked m p → (Fire F t m m' ↔ Fire F (withoutRead t p) m m')) ∧
          ((∀ (c : Card), ¬InputArc t p c) →
            ¬ResetArc t p → ∀ (m : N → ℕ) (d : List N) (m' : N → ℕ), F t m d m' → m' p = m p + Deposits d p)
-/
#guard_msgs in #print CORE_032

/-- With `p` marked, `t` and `t` without its read arcs on `p` are enabled at the same markings:
the dropped arcs all test `p`. -/
theorem enabledNA_withoutRead {N : Type} [DecidableEq N] (t : Trans N) (p : N)
    (m : N → Nat) (hp : m p ≠ 0) :
    enabledNA m (withoutRead t p).core = enabledNA m t.core := by
  have : (t.core.reads.filter (· ≠ p)).all (fun q => 1 ≤ m q) =
      t.core.reads.all (fun q => 1 ≤ m q) := by
    rw [Bool.eq_iff_iff]
    simp only [List.all_eq_true, List.mem_filter, ne_eq, decide_not, Bool.not_eq_eq_eq_not,
      Bool.not_true, decide_eq_false_iff_not, decide_eq_true_eq]
    refine ⟨fun h q hq => ?_, fun h q hq => h q hq.1⟩
    by_cases e : q = p
    · subst e; omega
    · exact h q ⟨hq, e⟩
  simp only [enabledNA, withoutRead, this]

/-- With `p` marked, a reference firing of `t` is a reference firing of `t` without its read
arcs on `p`, with the same deposit: reads gate enablement only. -/
theorem refFire_withoutRead {N : Type} [DecidableEq N] (t : Trans N) (p : N) (m : N → Nat)
    (hp : m p ≠ 0) (d : List N) (m' : N → Nat) :
    RefFire t m d m' ↔ RefFire (withoutRead t p) m d m' := by
  have he := enabledNA_withoutRead t p m hp
  constructor
  · rintro ⟨hen, hd, hm'⟩
    exact ⟨he.trans hen, hd, hm'⟩
  · rintro ⟨hen, hd, hm'⟩
    exact ⟨he.symm.trans hen, hd, hm'⟩

/-- The reference semantics satisfies CORE-032: `Seam.enabledNA` requires every read place to
hold a token, so `t` does not fire while `p` is unmarked; the consumption (`Seam.nconsumed`),
the deposits and the effect (`Seam.fireNC`) never read the read arcs, so with `p` marked removing
them changes nothing; and with no input arc and no reset arc on `p`, `Seam.fireNC` leaves
`m p - 0 + Deposits d p` there. -/
@[evidence holds CORE_032]
theorem CORE_032_reference {N : Type} [DecidableEq N] : CORE_032 (RefFire (N := N)) := by
  intro t p hp
  refine ⟨?_, fun m m' hm => ?_, fun hin hres m d m' h => ?_⟩
  · rintro m m' ⟨d, hen, -, -⟩ hm
    exact hm (((enabled_iff t m).1 hen).2.2 p hp)
  · exact ⟨fun ⟨d, h⟩ => ⟨d, (refFire_withoutRead t p m hm d m').1 h⟩,
      fun ⟨d, h⟩ => ⟨d, (refFire_withoutRead t p m hm d m').2 h⟩⟩
  · have hc : Consumes t m p = 0 := by
      rw [consumes_eq]
      cases hs : nspecAt t.core p with
      | none => rfl
      | some s => exact absurd ⟨s, hs, rfl⟩ (hin s.card)
    rw [refFire_apply h p, if_neg hres, hc, Nat.sub_zero]

/-! ### Examples over a one-place net -/

/-- The one transition of the examples: no inputs, one read arc on place `0`, no output spec. -/
def core032_t : Trans Nat :=
  { core := { name := "t", inputs := [], inhibitors := [], reads := [0], resets := [] },
    out := none }

/-- The marking of the examples in which every place holds one token. -/
def core032_marked : Nat → Nat := fun _ => 1

/-- The marking of the examples in which every place is empty. -/
def core032_empty : Nat → Nat := fun _ => 0

/-- A firing relation that ignores read arcs: a reference firing of the transition with its read
arcs removed. -/
def core032_ignoresReadFire : FireRel Nat :=
  fun t => RefFire { t with core := { t.core with reads := [] } }

/-- ✗ Ignoring the read arc violates CORE-032 (first clause): `core032_t` fires from the empty
marking. -/
@[evidence forbids CORE_032]
theorem CORE_032_forbids_ignoresRead : ¬ CORE_032 core032_ignoresReadFire := by
  intro h
  have hfire : Fire core032_ignoresReadFire core032_t core032_empty core032_empty :=
    ⟨[], by decide, ⟨.action 0, rfl⟩, by funext n; simp [fireNC, depProd, nconsumed, nspecAt,
      core032_t, core032_empty]⟩
  exact (h core032_t 0 (by decide)).1 _ _ hfire (by decide)

/-- A firing relation that treats a read arc as an input arc `One`: a reference firing of the
transition with each read place added as a `One` input. -/
def core032_readConsumesFire : FireRel Nat :=
  fun t => RefFire { t with core := { t.core with
    inputs := t.core.inputs ++ t.core.reads.map fun p => { place := p, card := .one } } }

/-- ✗ Consuming the read token violates CORE-032 (third clause): `core032_t` fires from the
marking with one token in every place and leaves place `0` empty, depositing nothing. -/
@[evidence forbids CORE_032]
theorem CORE_032_forbids_readConsumes : ¬ CORE_032 core032_readConsumesFire := by
  intro h
  have hfire : core032_readConsumesFire core032_t core032_marked []
      (fun n => if n = 0 then 0 else 1) :=
    ⟨by decide, ⟨.action 0, rfl⟩, by
      funext n
      by_cases e : n = 0
      · subst e; simp [fireNC, depProd, nconsumed, nspecAt, core032_t, core032_marked,
          Card.consumesAll, Card.required]
      · simp [fireNC, depProd, nconsumed, nspecAt, core032_t, core032_marked, e, Ne.symm e]⟩
  have := (h core032_t 0 (by decide)).2.2 (fun c ⟨s, hs, _⟩ => by simp [nspecAt, core032_t] at hs)
    (by decide) _ _ _ hfire
  exact absurd this (by decide)

/-- A firing relation in which a read arc blocks its transition whatever the marking: a reference
firing of a transition that has no read arcs, and no firing at all of one that has. -/
def core032_readAlwaysBlocksFire : FireRel Nat :=
  fun t m d m' => t.core.reads = [] ∧ RefFire t m d m'

/-- ✗ A read arc that blocks its transition while its place is marked violates CORE-032 (second
clause): `core032_t` cannot fire from the marked marking, but without its read arc it can. -/
@[evidence forbids CORE_032]
theorem CORE_032_forbids_readAlwaysBlocks : ¬ CORE_032 core032_readAlwaysBlocksFire := by
  intro h
  have hfire : Fire core032_readAlwaysBlocksFire (withoutRead core032_t 0)
      core032_marked core032_marked :=
    ⟨[], by decide, by decide, ⟨.action 0, rfl⟩, by funext n; simp [fireNC, depProd, nconsumed,
      nspecAt, withoutRead, core032_t, core032_marked]⟩
  obtain ⟨d, hne, -⟩ := ((h core032_t 0 (by decide)).2.1 core032_marked core032_marked
    (by decide)).2 hfire
  exact absurd hne (by decide)

/-! A firing relation that peeks the read places after input consumption is not a mutant here:
ruling D15 rejects an input arc and a read arc on one place when the transition is built
([EXEC-012]), so on every transition that builds no read place loses a token to consumption and
that relation agrees with the reference. -/

/-- The transition with a read arc and a reset arc on place `0`, nothing else. -/
def core032_tRes : Trans Nat :=
  { core := { name := "t", inputs := [], inhibitors := [], reads := [0], resets := [0] },
    out := none }

/-- A firing relation that skips the reset of a place the transition also reads: a reference
firing of the transition with those reset arcs removed. -/
def core032_skipReadResetFire : FireRel Nat :=
  fun t => RefFire { t with core := { t.core with
    resets := t.core.resets.filter (· ∉ t.core.reads) } }

/-- ✗ Skipping the reset of a read place violates CORE-032 (second clause): with one token in
place `0`, `core032_tRes` without its read arc fires and drains place `0`, but no firing of
`core032_tRes` leaves place `0` empty. -/
@[evidence forbids CORE_032]
theorem CORE_032_forbids_skipReadReset : ¬ CORE_032 core032_skipReadResetFire := by
  intro h
  have hfire : Fire core032_skipReadResetFire (withoutRead core032_tRes 0) core032_marked
      (fun n => if n = 0 then 0 else 1) :=
    ⟨[], by decide, ⟨.action 0, rfl⟩, by
      funext n
      by_cases e : n = 0
      · subst e; simp [fireNC, depProd, withoutRead, core032_tRes]
      · simp [fireNC, depProd, nconsumed, nspecAt, withoutRead, core032_tRes, core032_marked,
          e]⟩
  obtain ⟨d, hr⟩ := ((h core032_tRes 0 (by decide)).2.1 core032_marked _ (by decide)).2 hfire
  have := refFire_apply hr 0
  rw [consumes_eq] at this
  simp [ResetArc, nspecAt, core032_tRes, core032_marked] at this
  omega

/-! ### One mutant per clause -/

/-- Mutant reading of CORE-032 that drops the first clause: an unmarked read place does not stop
the transition. -/
def CORE_032_mutant_dropUnmarked {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t p, ReadArc t p →
    (∀ m m', Marked m p → (Fire F t m m' ↔ Fire F (withoutRead t p) m m')) ∧
    ((∀ c, ¬ InputArc t p c) → ¬ ResetArc t p →
      ∀ m d m', F t m d m' → m' p = m p + Deposits d p)

/-- The firing that changes nothing: every transition may fire from every marking, depositing
nothing and leaving the marking as it is. -/
def core032_idleFire : FireRel Nat := fun _ m d m' => d = [] ∧ m' = m

/-- The idle firing kills the first mutant: it satisfies the mutant (whether a transition fires
does not depend on its arcs, and no firing changes a token count) but not CORE-032
(`core032_t` fires while its read place is unmarked). -/
@[evidence mutant CORE_032]
theorem CORE_032_mutant_dropUnmarked_killed :
    CORE_032_mutant_dropUnmarked core032_idleFire ∧ ¬ CORE_032 core032_idleFire := by
  refine ⟨fun t p _ => ⟨fun m m' _ => Iff.rfl, fun _ _ m d m' ⟨hd, hm⟩ => ?_⟩, fun h => ?_⟩
  · subst hd hm; simp [Deposits, depProd]
  · exact (h core032_t 0 (by decide)).1 core032_empty core032_empty ⟨[], rfl, rfl⟩ (by decide)

/-- Mutant reading of CORE-032 that drops the second clause: a marked read place may still
change whether, and where, the transition fires. -/
def CORE_032_mutant_dropMarked {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t p, ReadArc t p →
    (while (fun m => ¬ Marked m p), never Fire F t) ∧
    ((∀ c, ¬ InputArc t p c) → ¬ ResetArc t p →
      ∀ m d m', F t m d m' → m' p = m p + Deposits d p)

/-- The always-blocking firing kills the second mutant: it satisfies the mutant (a transition
with a read arc never fires) but not CORE-032 (`core032_t` does not fire from the marked marking
although it fires there without its read arc). -/
@[evidence mutant CORE_032]
theorem CORE_032_mutant_dropMarked_killed :
    CORE_032_mutant_dropMarked core032_readAlwaysBlocksFire ∧
      ¬ CORE_032 core032_readAlwaysBlocksFire := by
  refine ⟨fun t p hp => ⟨?_, fun _ _ m d m' ⟨hne, _⟩ => ?_⟩, CORE_032_forbids_readAlwaysBlocks⟩
  · rintro m m' ⟨d, hne, -⟩ -
    have hp' : p ∈ t.core.reads := hp
    simp [hne] at hp'
  · have hp' : p ∈ t.core.reads := hp
    simp [hne] at hp'

/-- Mutant reading of CORE-032 that drops the third clause: the read arc gates enablement, but a
firing may still take the read token. -/
def CORE_032_mutant_dropConserve {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t p, ReadArc t p →
    (while (fun m => ¬ Marked m p), never Fire F t) ∧
    (∀ m m', Marked m p → (Fire F t m m' ↔ Fire F (withoutRead t p) m m'))

/-- A firing relation that empties the whole marking: a reference firing of the transition, then
every place cleared. Read arcs gate it exactly as in the reference, so it is blind to the first
two clauses. -/
def core032_clearsAllFire : FireRel Nat :=
  fun t m d m' => (∃ m'', RefFire t m d m'') ∧ m' = fun _ => 0

/-- The clearing firing kills the third mutant: it satisfies the mutant (it fires exactly when
the reference does, and the reference satisfies the first two clauses) but not CORE-032
(`core032_t` fires from the marked marking and leaves place `0` empty, depositing nothing). -/
@[evidence mutant CORE_032]
theorem CORE_032_mutant_dropConserve_killed :
    CORE_032_mutant_dropConserve core032_clearsAllFire ∧ ¬ CORE_032 core032_clearsAllFire := by
  refine ⟨fun t p hp => ⟨?_, fun m m' hm => ?_⟩, fun h => ?_⟩
  · rintro m m' ⟨d, ⟨m'', hr⟩, -⟩ hm
    exact (CORE_032_reference t p hp).1 m m'' ⟨d, hr⟩ hm
  · constructor
    · rintro ⟨d, ⟨m'', hr⟩, rfl⟩
      exact ⟨d, ⟨m'', (refFire_withoutRead t p m hm d m'').1 hr⟩, rfl⟩
    · rintro ⟨d, ⟨m'', hr⟩, rfl⟩
      exact ⟨d, ⟨m'', (refFire_withoutRead t p m hm d m'').2 hr⟩, rfl⟩
  · have hr : RefFire core032_t core032_marked [] core032_marked :=
      ⟨by decide, ⟨.action 0, rfl⟩, by funext n; simp [fireNC, depProd, nconsumed, nspecAt,
        core032_t, core032_marked]⟩
    have := (h core032_t 0 (by decide)).2.2
      (fun c ⟨s, hs, _⟩ => by simp [nspecAt, core032_t] at hs) (by decide)
      core032_marked [] (fun _ => 0) ⟨⟨_, hr⟩, rfl⟩
    exact absurd this (by decide)

/-- All three clauses of CORE-032 are exercised by the reference semantics: `core032_t` has a
read arc on place `0` and no input or reset arc there; it does not fire from the empty marking,
although without its read arc it does (first clause); it fires from the marked marking, as it
does without its read arc (second clause); and that firing deposits nothing and leaves place
`0` holding its one token (third clause). -/
@[evidence nonvacuous CORE_032]
theorem CORE_032_nonvacuous :
    ReadArc core032_t 0 ∧ (∀ c, ¬ InputArc core032_t 0 c) ∧ ¬ ResetArc core032_t 0 ∧
      ¬ Fire RefFire core032_t core032_empty core032_empty ∧
      Fire RefFire (withoutRead core032_t 0) core032_empty core032_empty ∧
      RefFire core032_t core032_marked [] core032_marked ∧
      Fire RefFire (withoutRead core032_t 0) core032_marked core032_marked ∧
      core032_marked 0 = core032_marked 0 + Deposits [] 0 := by
  refine ⟨by decide, fun c ⟨s, hs, _⟩ => by simp [nspecAt, core032_t] at hs, by decide, ?_,
    ⟨[], by decide, ⟨.action 0, rfl⟩, ?_⟩, ⟨by decide, ⟨.action 0, rfl⟩, ?_⟩,
    ⟨[], by decide, ⟨.action 0, rfl⟩, ?_⟩, by decide⟩
  · rintro ⟨d, hen, -⟩
    exact absurd hen (by decide)
  · funext n; simp [fireNC, depProd, nconsumed, nspecAt, withoutRead, core032_t, core032_empty]
  · funext n; simp [fireNC, depProd, nconsumed, nspecAt, core032_t, core032_marked]
  · funext n; simp [fireNC, depProd, nconsumed, nspecAt, withoutRead, core032_t,
      core032_marked]

end Libpetri.Spec
