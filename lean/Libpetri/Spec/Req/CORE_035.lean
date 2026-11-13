import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.Glossary
import Libpetri.Spec.Text.CORE_035

set_option linter.missingDocs true

/-!
# CORE-035: Output arc (`spec/01-core-model.md`)

The requirement is a predicate over an abstract firing relation `F : FireRel N`. The evidence
theorems check it against the reference semantics (`Reference.Fires`, as `RefFire`), against
concrete firing relations that break it, and against a mutant reading per clause.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## CORE-035: Output arc -/

requirement CORE_035
  id "CORE-035"
  title "Output arc"
  kind B
  scope "all executors"
  source verbatim "spec/01-core-model.md"
  covers CORE_035.s1, CORE_035.s2, CORE_035.s3
  reading "For every transition t and every deposit d:"
          "every firing of t that deposits d puts tokens only in places that t's output spec names;"
          "every firing of t that deposits d leaves a marking in which every place holds at least as many tokens as d put there;"
          "every firing of t that deposits d, from m to m', leaves every place p with no input arc and no reset arc of t holding m p plus what d put in p, no more and no less."
  assumes "A firing is read as one step from a marking to a marking that deposits the tokens of one outcome (glossary: Fire, Deposit); timing and priority play no part. 'When the transition's action completes' is read as 'when the firing deposits', for every outcome: the timeout outcome ([IO-013]) also deposits only in places the output spec names (a Timeout child, a ForwardInput's `to`)."
          "An output place is a place the transition's output spec names (glossary: Output arc), every Xor branch, Timeout child and ForwardInput `to` included. A transition with no output spec has no output place, so its firings deposit nothing."
          "Which output places one firing deposits in, and how many tokens, is the subject of [IO-010]–[IO-016] ('according to its output spec'), not of this block: a firing relation that never deposits satisfies CORE-035 and is ruled out by [IO-016]."
          "The second line says only that the deposited tokens are in the resulting marking; the exact count of an input place is [CORE-030]'s and of a reset place [CORE-034]'s. A reset place that is also an output place ends holding exactly what was deposited, which satisfies the line."
          "The third line is the marking side of 'only in its output places': on every place [CORE-030] and [CORE-034] do not cover (a pure output place, a read-only or inhibitor-only place, a place with no arc), the firing adds exactly its deposit. A place the firing does not deposit in is therefore unchanged, and an output place keeps its earlier tokens (no overwrite, no double or deduplicated deposit). On read places this coincides with [CORE-032]'s third clause."
          "AC1 (after the transition fires, produced tokens appear in the output place) is the second line, with the first saying the place is an output place."
          "AC2 (output tokens carry the current timestamp): not encoded. The firing relation works on token counts and carries no token timestamps; timestamps are [CORE-011] and the timed semantics' subject."
  signoff "2026-11-13 1af909a444b9b0bb ai"
  statement : ∀ {N : Type} [DecidableEq N], FireRel N → Prop :=
    fun F => ∀ t d,
      (on (fun m m' => F t m d m'), shall (fun _ _ => ∀ p, Produced d p → OutputArc t p)) ∧
      (on (fun m m' => F t m d m'), shall (fun _ m' => ∀ p, Deposits d p ≤ m' p)) ∧
      (on (fun m m' => F t m d m'), shall
        (fun m m' => ∀ p, (∀ c, ¬ InputArc t p c) → ¬ ResetArc t p → m' p = m p + Deposits d p))

/- The pinned readable form of CORE-035: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CORE_035 : {N : Type} → [DecidableEq N] → FireRel N → Prop :=
fun {N} [DecidableEq N] F =>
  ∀ (t : Reference.Trans N) (d : List N),
    (on fun m m' => F t m d m', shall fun x x_1 => ∀ (p : N), Produced d p → OutputArc t p) ∧
      (on fun m m' => F t m d m', shall fun x m' => ∀ (p : N), Deposits d p ≤ m' p) ∧
        on fun m m' => F t m d m', shall fun m m' =>
          ∀ (p : N), (∀ (c : Card), ¬InputArc t p c) → ¬ResetArc t p → m' p = m p + Deposits d p
-/
#guard_msgs in #print CORE_035

/-! ### Every place an outcome deposits in is named by the output spec -/

/-- A reference firing leaves every place holding at least what it deposited there: a reset
place holds exactly the deposit, every other place the remainder after consumption plus the
deposit. -/
theorem core035_ref_appear {N : Type} [DecidableEq N] {t : Trans N} {m m' : N → Nat}
    {d : List N} (h : RefFire t m d m') : ∀ p, Deposits d p ≤ m' p := by
  intro p
  rw [refFire_apply h p]
  split <;> omega

/-- A reference firing adds exactly its deposit to a place with no input arc and no reset arc:
nothing is consumed there and the old count is kept. -/
theorem core035_ref_frame {N : Type} [DecidableEq N] {t : Trans N} {m m' : N → Nat}
    {d : List N} (h : RefFire t m d m') :
    ∀ p, (∀ c, ¬ InputArc t p c) → ¬ ResetArc t p → m' p = m p + Deposits d p := by
  intro p hin hr
  rw [refFire_apply h p, if_neg hr]
  have : Consumes t m p = 0 := by
    rw [consumes_eq]
    cases hs : nspecAt t.core p with
    | none => rfl
    | some s => exact absurd ⟨s, hs, rfl⟩ (hin s.card)
  omega

/-- The reference semantics satisfies CORE-035: `Reference.deposit` takes its tokens from an
output branch (`Out.branches`) or from the first `Timeout` child (`Out.timeoutDeposits`), both
of which name only places of the output spec; and `Seam.fireNC` adds the deposit's counts to
every place (after consumption, or in place of the old count on a reset place), so a place
with no input or reset arc gains exactly the deposit. -/
@[evidence holds CORE_035]
theorem CORE_035_reference {N : Type} [DecidableEq N] : CORE_035 (RefFire (N := N)) :=
  fun _ _ => ⟨fun _ _ h => refFire_outputs h, fun _ _ h => core035_ref_appear h,
    fun _ _ h => core035_ref_frame h⟩

/-! ### Examples over a small net -/

/-- The producing transition of the examples: no arcs in, output spec `Place 0`. -/
def core035_t : Trans Nat :=
  { core := { name := "t", inputs := [], inhibitors := [], reads := [], resets := [] },
    out := some (.place 0) }

/-- A transition of the examples with no output spec and no arcs. -/
def core035_silent : Trans Nat :=
  { core := { name := "s", inputs := [], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- The marking of the examples in which every place is empty. -/
def core035_empty : Nat → Nat := fun _ => 0

/-- The marking in which place `0` holds one token and every other place none. -/
def core035_one : Nat → Nat := fun p => if p = 0 then 1 else 0

/-- A firing relation that deposits a token in place `0` whatever the transition's output spec
says, and adds the deposit to the marking. -/
def core035_strayFire : FireRel Nat :=
  fun _ m d m' => d = [0] ∧ m' = fun p => m p + Deposits d p

/-- ✗ Depositing outside the output spec violates CORE-035 (first clause): `core035_silent`
has no output spec, yet under `core035_strayFire` it deposits a token in place `0`. -/
@[evidence forbids CORE_035]
theorem CORE_035_forbids_stray : ¬ CORE_035 core035_strayFire := by
  intro h
  obtain ⟨o, ho, -⟩ := (h core035_silent [0]).1 core035_empty core035_one ⟨rfl, by
    funext p; cases p <;> simp [core035_empty, core035_one, Deposits, depProd]⟩
    0 (by simp [Produced])
  exact absurd ho (by simp [core035_silent])

/-- A firing relation that takes a reference firing's deposit but drops its tokens: the
marking is left as it was. -/
def core035_lostFire : FireRel Nat :=
  fun t m d m' => (∃ m'', RefFire t m d m'') ∧ m' = m

/-- The reference firing of `core035_t` from the empty marking: it deposits one token in place
`0`. -/
theorem core035_t_fires : RefFire core035_t core035_empty [0] core035_one :=
  ⟨by decide, ⟨.action 0, rfl⟩, by
    funext n; cases n <;> simp [fireNC, depProd, nconsumed, nspecAt, core035_t, core035_empty,
      core035_one]⟩

/-- The marking in which place `0` holds two tokens and every other place none. -/
def core035_two : Nat → Nat := fun p => if p = 0 then 2 else 0

/-- The reference firing of `core035_t` from `core035_one`: the token already in place `0` is
kept and the deposit is added to it. -/
theorem core035_t_fires_one : RefFire core035_t core035_one [0] core035_two :=
  ⟨by decide, ⟨.action 0, rfl⟩, by
    funext n; cases n <;> simp [fireNC, depProd, nconsumed, nspecAt, core035_t, core035_one,
      core035_two]⟩

/-- `core035_t` has no input arc on any place. -/
theorem core035_t_noInput (p : Nat) : ∀ c, ¬ InputArc core035_t p c := by
  rintro c ⟨s, hs, -⟩
  simp [nspecAt, core035_t] at hs

/-- `core035_t` has no reset arc on any place. -/
theorem core035_t_noReset (p : Nat) : ¬ ResetArc core035_t p := by
  simp [core035_t, ResetArc]

/-- ✗ Losing the deposited tokens violates CORE-035 (second clause): `core035_t` deposits a
token in place `0`, but under `core035_lostFire` the marking it leaves is still empty. -/
@[evidence forbids CORE_035]
theorem CORE_035_forbids_lost : ¬ CORE_035 core035_lostFire := by
  intro h
  have := (h core035_t [0]).2.1 core035_empty core035_empty ⟨⟨_, core035_t_fires⟩, rfl⟩ 0
  exact absurd this (by decide)

/-- A transition with a reset arc on place `0` and output spec `Place 0`. -/
def core035_r : Trans Nat :=
  { core := { name := "r", inputs := [], inhibitors := [], reads := [], resets := [0] },
    out := some (.place 0) }

/-- The reference firing of `core035_r` from the empty marking: place `0` ends holding the
deposited token. -/
theorem core035_r_fires : RefFire core035_r core035_empty [0] core035_one :=
  ⟨by decide, ⟨.action 0, rfl⟩, by
    funext n; cases n <;> simp [fireNC, depProd, nconsumed, nspecAt, core035_r, core035_empty,
      core035_one]⟩

/-- A firing relation that applies the reset arcs after the deposit: the reference firing,
then every reset place emptied. -/
def core035_resetAfterFire : FireRel Nat :=
  fun t m d m' => ∃ m'', RefFire t m d m'' ∧ m' = fun p => if p ∈ t.core.resets then 0 else m'' p

/-- ✗ Resetting after depositing violates CORE-035 (second clause): `core035_r` deposits a token
in its reset place `0`, which `core035_resetAfterFire` then empties. -/
@[evidence forbids CORE_035]
theorem CORE_035_forbids_resetAfter : ¬ CORE_035 core035_resetAfterFire := by
  intro h
  have := (h core035_r [0]).2.1 core035_empty _ ⟨_, core035_r_fires, rfl⟩ 0
  exact absurd this (by simp [core035_r, Deposits, depProd])

/-- A firing relation that writes an output place like a reset: a place the deposit names is
set to the deposit, its earlier tokens dropped. -/
def core035_overwriteFire : FireRel Nat :=
  fun t m d m' => ∃ m'', RefFire t m d m'' ∧
    m' = fun p => if 0 < Deposits d p then Deposits d p else m'' p

/-- ✗ Overwriting an output place violates CORE-035 (third clause): `core035_t` fires from
`core035_one`, and place `0` ends with one token instead of two. -/
@[evidence forbids CORE_035]
theorem CORE_035_forbids_overwrite : ¬ CORE_035 core035_overwriteFire := by
  intro h
  have := (h core035_t [0]).2.2 core035_one _ ⟨_, core035_t_fires_one, rfl⟩ 0
    (core035_t_noInput 0) (core035_t_noReset 0)
  simp [core035_one, Deposits, depProd] at this

/-- A firing relation that also puts a token in place `7`, which no arc names, while reporting
the reference deposit. -/
def core035_phantomFire : FireRel Nat :=
  fun t m d m' => ∃ m'', RefFire t m d m'' ∧ m' = fun p => m'' p + if p = 7 then 1 else 0

/-- ✗ A phantom write violates CORE-035 (third clause): `core035_t` deposits only in place `0`,
yet place `7` gains a token. -/
@[evidence forbids CORE_035]
theorem CORE_035_forbids_phantom : ¬ CORE_035 core035_phantomFire := by
  intro h
  have := (h core035_t [0]).2.2 core035_empty _ ⟨_, core035_t_fires, rfl⟩ 7
    (core035_t_noInput 7) (core035_t_noReset 7)
  simp [core035_empty, core035_one, Deposits, depProd] at this

/-- A firing relation that adds the deposit to the marking twice while reporting it once. -/
def core035_doubleFire : FireRel Nat :=
  fun t m d m' => ∃ m'', RefFire t m d m'' ∧ m' = fun p => m'' p + Deposits d p

/-- ✗ A double deposit violates CORE-035 (third clause): `core035_t` fires from the empty
marking and place `0` ends with two tokens for a deposit of one. -/
@[evidence forbids CORE_035]
theorem CORE_035_forbids_double : ¬ CORE_035 core035_doubleFire := by
  intro h
  have := (h core035_t [0]).2.2 core035_empty _ ⟨_, core035_t_fires, rfl⟩ 0
    (core035_t_noInput 0) (core035_t_noReset 0)
  simp [core035_empty, core035_one, Deposits, depProd] at this

/-- A firing relation with a set-like token store: a deposit is skipped where the place
already holds as many tokens as it deposits. -/
def core035_dedupFire : FireRel Nat :=
  fun t m d m' => ∃ m'', RefFire t m d m'' ∧
    m' = fun p => max (m'' p - Deposits d p) (Deposits d p)

/-- ✗ A deduplicating store violates CORE-035 (third clause): `core035_t` fires from
`core035_one`, and place `0` keeps one token instead of two. -/
@[evidence forbids CORE_035]
theorem CORE_035_forbids_dedup : ¬ CORE_035 core035_dedupFire := by
  intro h
  have := (h core035_t [0]).2.2 core035_one _ ⟨_, core035_t_fires_one, rfl⟩ 0
    (core035_t_noInput 0) (core035_t_noReset 0)
  simp [core035_one, core035_two, Deposits, depProd] at this

/-- Mutant reading of CORE-035 that drops the first clause: deposited tokens appear in the
marking and untouched places gain exactly the deposit, but the deposit may name any place. -/
def CORE_035_mutant_dropOutputs {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t d,
    (on (fun m m' => F t m d m'), shall (fun _ m' => ∀ p, Deposits d p ≤ m' p)) ∧
    (on (fun m m' => F t m d m'), shall
      (fun m m' => ∀ p, (∀ c, ¬ InputArc t p c) → ¬ ResetArc t p → m' p = m p + Deposits d p))

/-- The stray firing kills the first mutant: it satisfies the mutant (it adds its deposit to
the marking) but not CORE-035 (it deposits outside the output spec). -/
@[evidence mutant CORE_035]
theorem CORE_035_mutant_dropOutputs_killed :
    CORE_035_mutant_dropOutputs core035_strayFire ∧ ¬ CORE_035 core035_strayFire := by
  refine ⟨fun t d => ⟨?_, ?_⟩, CORE_035_forbids_stray⟩
  · rintro m m' ⟨-, rfl⟩ p
    exact Nat.le_add_left _ _
  · rintro m m' ⟨-, rfl⟩ p - -
    rfl

/-- Mutant reading of CORE-035 that drops the second clause: tokens go only to output places
and untouched places gain exactly the deposit, but an input or reset place need not hold it. -/
def CORE_035_mutant_dropAppear {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t d,
    (on (fun m m' => F t m d m'), shall (fun _ _ => ∀ p, Produced d p → OutputArc t p)) ∧
    (on (fun m m' => F t m d m'), shall
      (fun m m' => ∀ p, (∀ c, ¬ InputArc t p c) → ¬ ResetArc t p → m' p = m p + Deposits d p))

/-- The reset-after firing kills the second mutant: off the reset places it is the reference
firing, so it satisfies the mutant, but it empties a reset place the deposit filled. -/
@[evidence mutant CORE_035]
theorem CORE_035_mutant_dropAppear_killed :
    CORE_035_mutant_dropAppear core035_resetAfterFire ∧ ¬ CORE_035 core035_resetAfterFire := by
  refine ⟨fun t d => ⟨?_, ?_⟩, CORE_035_forbids_resetAfter⟩
  · rintro m m' ⟨m'', hf, -⟩
    exact refFire_outputs hf
  · rintro m m' ⟨m'', hf, rfl⟩ p hin hr
    have hp : p ∉ t.core.resets := hr
    simp only [if_neg hp]
    exact core035_ref_frame hf p hin hr

/-- Mutant reading of CORE-035 that drops the third clause: tokens go only to output places and
the deposit is in the marking, but other places may change too. -/
def CORE_035_mutant_dropFrame {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t d,
    (on (fun m m' => F t m d m'), shall (fun _ _ => ∀ p, Produced d p → OutputArc t p)) ∧
    (on (fun m m' => F t m d m'), shall (fun _ m' => ∀ p, Deposits d p ≤ m' p))

/-- The double firing kills the third mutant: its deposits are reference deposits and the
marking holds them, but it adds each deposit twice. -/
@[evidence mutant CORE_035]
theorem CORE_035_mutant_dropFrame_killed :
    CORE_035_mutant_dropFrame core035_doubleFire ∧ ¬ CORE_035 core035_doubleFire := by
  refine ⟨fun t d => ⟨?_, ?_⟩, CORE_035_forbids_double⟩
  · rintro m m' ⟨m'', hf, -⟩
    exact refFire_outputs hf
  · rintro m m' ⟨m'', hf, rfl⟩ p
    exact Nat.le_add_left _ _

/-- All three clauses of CORE-035 are exercised by the reference semantics: `core035_t` fires
from the empty marking depositing a token in place `0`, which is an output place of `core035_t`
(first clause) and holds that token afterwards (second clause); fired again from `core035_one`,
place `0`, which has no input or reset arc, ends with its old token plus the new one (third
clause). -/
@[evidence nonvacuous CORE_035]
theorem CORE_035_nonvacuous :
    RefFire core035_t core035_empty [0] core035_one ∧ Produced [0] 0 ∧
      OutputArc core035_t 0 ∧ Deposits [0] 0 = 1 ∧ core035_one 0 = 1 ∧
      RefFire core035_t core035_one [0] core035_two ∧ core035_two 0 = core035_one 0 + 1 :=
  ⟨core035_t_fires, by simp [Produced], ⟨.place 0, rfl, by simp [outPlaces]⟩, by decide,
    by decide, core035_t_fires_one, by decide⟩

end Libpetri.Spec
