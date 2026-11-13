import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.Glossary
import Libpetri.Spec.Text.IO_001

set_option linter.missingDocs true

/-!
# IO-001: Input One (`spec/02-input-output-specs.md`)

The requirement is a predicate over an abstract firing relation `F : FireRel N`. The evidence
theorems check it against the reference semantics (`Reference.Fires`, as `RefFire`), against
four concrete firing relations that each break one clause (or one part of the third), and
against one mutant reading per clause and part.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## Local term: a transition without its input arc on a place -/

/-- `t` with the input arc on `p` removed (the arc `InputArc` names: the first input arc on `p`,
as the reference reads it), and nothing else changed. For a transition that [CORE-030] accepts
it is the only input arc on `p`. Local to IO-001: the glossary has no such term. -/
def io001_withoutInput {N : Type} [DecidableEq N] (t : Trans N) (p : N) : Trans N :=
  { t with core := { t.core with inputs := t.core.inputs.eraseP (fun s => decide (s.place = p)) } }

/-! ## IO-001: Input One -/

requirement IO_001
  id "IO-001"
  title "Input One"
  kind B
  scope "all executors"
  source verbatim "spec/02-input-output-specs.md"
  covers IO_001.s1, IO_001.s2, IO_001.s3, IO_001.s4, IO_001.s5
  reading "For every transition t and place p such that the input arc of t on p is One:"
          "t does not fire from a marking in which p is unmarked;"
          "from a marking in which p is marked, t can fire exactly when t without its input arc on p can fire;"
          "unless p is also a reset place of t, every firing of t from m that deposits d and leaves m' has m'(p) + 1 = m(p) + d(p): p loses exactly 1 token, besides what the firing deposits there; and if p is not an output place of t either, m'(p) + 1 = m(p): p loses exactly 1 token, whatever deposit the firing reports."
  assumes "A firing is read as one step from a marking to a marking with its deposit (glossary: Fire); timing and priority play no part. 'Can fire' and 'enables' are both read as 'some firing exists'."
          "Correlated inputs (ruling D30, extending D16): the third quoted sentence excludes a correlated input of a ν-net match specification (NU-020), on which the arc also requires a token of the chosen name. The transitions of the model (Reference.Trans) carry no match specification, so every input place is one that is not a correlated input, and the second line quantifies over every `One` input arc. How a correlated input counts and consumes is NU-020's, not encoded here."
          "The first quoted sentence and the bullets (`requiredCount()` returns 1, `consumptionCount(available)` returns 1) are IO-007's contract for `One`. Here it is observed through firing: the required count is the second and third lines, the consumption count the fourth. The bullet values themselves are `io001_counts`."
          "AC1 (enables when the place has >= 1 token) is the second line (not with 0 tokens) and the third line (with >= 1 token the arc does not stand in the way; whether the other arcs allow the firing is theirs to say, IO-005 and CORE-022)."
          "AC2 (exactly 1 token consumed on firing) is the fourth line for the count. Which token is consumed (the oldest) is below the count granularity of the firing semantics and is the glossary's reading of Consume (CORE-030); it is not encoded here."
          "AC3 (remaining tokens stay in the place) is the fourth line: p holds m(p) - 1 tokens plus the firing's deposit there afterwards."
          "Consumption is observed through the marking: p loses 1 and gains what the firing deposits there (p may also be an output place). A place that is both the input place and a reset place of t ends holding what the firing deposited there (CORE-034), so the consumed token is not visible in the marking; the fourth line excludes that case."
          "The deposit a firing reports is not trusted for the count: on a place that t's output spec does not name (glossary: Output arc) no firing of t can deposit ([CORE-035]), so there the consumed token shows in the marking alone, as exactly 1 token fewer. Without this a firing that consumes nothing but reports a deposit of 1 in the input place would pass the count."
          "The input arc of t on p is the first input arc on p (glossary: Input arc), and t without its input arc on p drops that arc only; CORE-030 rejects a second input arc on p at build."
  signoff "2026-11-13 749a74beaedb4a3d ai"
  statement : ∀ {N : Type} [DecidableEq N], FireRel N → Prop :=
    fun F => ∀ t p, InputArc t p .one →
      (while (fun m => ¬ Marked m p), never Fire F t) ∧
      (∀ m, Marked m p →
        ((∃ m', Fire F t m m') ↔ (∃ m', Fire F (io001_withoutInput t p) m m'))) ∧
      (¬ ResetArc t p → ∀ m d m', F t m d m' →
        m' p + 1 = m p + Deposits d p ∧ (¬ OutputArc t p → m' p + 1 = m p))

/- The pinned readable form of IO-001: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.IO_001 : {N : Type} → [DecidableEq N] → FireRel N → Prop :=
fun {N} [DecidableEq N] F =>
  ∀ (t : Reference.Trans N) (p : N),
    InputArc t p Card.one →
      (while fun m => ¬Marked m p, never Fire F t) ∧
        (∀ (m : CountMarking N), Marked m p → ((∃ m', Fire F t m m') ↔ ∃ m', Fire F (io001_withoutInput t p) m m')) ∧
          (¬ResetArc t p →
            ∀ (m : N → ℕ) (d : List N) (m' : N → ℕ),
              F t m d m' → m' p + 1 = m p + Deposits d p ∧ (¬OutputArc t p → m' p + 1 = m p))
-/
#guard_msgs in #print IO_001

/-- The bullets of IO-001: the glossary's required count and consumption count of `One` are both
1, whatever the place holds. -/
theorem io001_counts : requiredCount .one = 1 ∧ ∀ a, consumptionCount .one a = 1 :=
  ⟨rfl, fun _ => rfl⟩

/-! ## Lemmas over the reference definitions -/

/-- Removing the first element satisfying `q` splits an `all` check into that element and the
rest. -/
theorem io001_all_eraseP {α : Type} (q f : α → Bool) :
    ∀ (l : List α) (s : α), l.find? q = some s →
      (l.all f = true ↔ f s = true ∧ (l.eraseP q).all f = true)
  | [], _, h => by simp at h
  | a :: l, s, h => by
    by_cases hq : q a = true
    · simp only [List.find?_cons, hq] at h
      cases h
      simp [hq]
    · have hq' : q a = false := by simpa using hq
      simp only [List.find?_cons, hq'] at h
      have ih := io001_all_eraseP q f l s h
      simp only [List.all_cons, List.eraseP_cons, hq', Bool.and_eq_true, cond_false] at ih ⊢
      constructor
      · rintro ⟨ha, hl⟩; exact ⟨(ih.1 hl).1, ha, (ih.1 hl).2⟩
      · rintro ⟨hs, ha, hl⟩; exact ⟨ha, ih.2 ⟨hs, hl⟩⟩

/-- The input arc `InputArc` names is one of the transition's input arcs, on `p`. -/
theorem io001_inputArc_mem {N : Type} [DecidableEq N] {t : Trans N} {p : N} {c : Card}
    (h : InputArc t p c) : ∃ s, s ∈ t.core.inputs ∧ s.place = p ∧ s.card = c ∧
      t.core.inputs.find? (fun s => decide (s.place = p)) = some s := by
  obtain ⟨s, hs, hc⟩ := h
  have hmem := List.mem_of_find?_eq_some hs
  have hp := List.find?_some hs
  exact ⟨s, hmem, by simpa using hp, hc, hs⟩

/-- An enabled transition has at least one token in the place of a `One` input arc. -/
theorem io001_enabled_marked {N : Type} [DecidableEq N] {t : Trans N} {p : N}
    {m : CountMarking N} (h : InputArc t p .one) (he : Enabled t m) : Marked m p := by
  obtain ⟨s, hmem, hp, hc, -⟩ := io001_inputArc_mem h
  have := ((enabled_iff t m).1 he).1 s hmem
  simp only [hc, hp, requiredCount, Card.required] at this
  simp [Marked]; omega

/-- With the place of its `One` input arc marked, a transition is enabled exactly when it is
enabled without that arc. -/
theorem io001_enabled_without {N : Type} [DecidableEq N] {t : Trans N} {p : N}
    {m : CountMarking N} (h : InputArc t p .one) (hm : Marked m p) :
    Enabled t m ↔ Enabled (io001_withoutInput t p) m := by
  obtain ⟨s, -, hp, hc, hf⟩ := io001_inputArc_mem h
  have key := io001_all_eraseP (fun s => decide (s.place = p))
    (fun s => decide (s.card.required ≤ m s.place)) t.core.inputs s hf
  have hs : decide (s.card.required ≤ m s.place) = true := by
    simp only [hc, hp, Card.required, decide_eq_true_eq]
    simp [Marked] at hm; omega
  simp only [Enabled, enabledNA, io001_withoutInput, Bool.and_eq_true]
  rw [key]
  simp [hs]

/-- Some reference firing exists exactly when the transition is enabled: every output spec offers
some deposit (`exists_deposit`). -/
theorem io001_refFire_exists_iff {N : Type} [DecidableEq N] (t : Trans N) (m : CountMarking N) :
    (∃ m', Fire RefFire t m m') ↔ Enabled t m := by
  constructor
  · rintro ⟨m', d, he, -⟩; exact he
  · intro he
    obtain ⟨ch, d, hd⟩ := exists_deposit (nconsumed m t.core) t.out
    exact ⟨_, d, he, ⟨ch, hd⟩, rfl⟩

/-- A reference firing of `t` consumes 1 token from the place of its `One` input arc. -/
theorem io001_consumes_one {N : Type} [DecidableEq N] {t : Trans N} {p : N}
    (h : InputArc t p .one) (m : CountMarking N) : Consumes t m p = 1 := by
  obtain ⟨s, hs, hc⟩ := h
  rw [consumes_eq, hs]
  simp [consumptionCount, hc, Card.consumesAll, Card.required]

/-- The reference semantics satisfies IO-001: `Seam.enabledNA` requires the `One` place to hold
`Card.required .one = 1` token, so `t` does not fire with it unmarked, and with it marked the
arc's conjunct of `enabledNA` holds, so dropping the arc changes no enablement (and every output
spec offers a deposit); `Seam.nconsumed` takes 1 from it, and `Seam.fireNC` of a non-reset place
is "minus consumed, plus deposited", where the deposit is empty outside the output spec's
places. -/
@[evidence holds IO_001]
theorem IO_001_reference {N : Type} [DecidableEq N] : IO_001 (RefFire (N := N)) := by
  intro t p hp
  refine ⟨?_, fun m hm => ?_, fun hr m d m' hf => ?_⟩
  · rintro m m' ⟨d, he, -, -⟩ hm
    exact hm (io001_enabled_marked hp he)
  · rw [io001_refFire_exists_iff, io001_refFire_exists_iff]
    exact io001_enabled_without hp hm
  · have hmk := io001_enabled_marked hp hf.1
    have happ := refFire_apply hf p
    rw [if_neg hr, io001_consumes_one hp] at happ
    simp [Marked] at hmk
    refine ⟨by omega, fun ho => ?_⟩
    have h0 : Deposits d p = 0 :=
      List.count_eq_zero_of_not_mem (fun h => ho (refFire_outputs hf p h))
    omega

/-! ### Examples over a one-place net -/

/-- The one transition of the examples: one `One` input arc on place `0`, no other arcs, no
output spec. -/
def io001_t : Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- The marking of the test derivation: place `0` holds 3 tokens, every other place none. -/
def io001_three : Nat → Nat := fun n => if n = 0 then 3 else 0

/-- The marking after one firing from `io001_three`: place `0` holds 2 tokens. -/
def io001_two : Nat → Nat := fun n => if n = 0 then 2 else 0

/-- The marking in which place `0` holds one token, every other place none. -/
def io001_one : Nat → Nat := fun n => if n = 0 then 1 else 0

/-- The marking in which every place is empty. -/
def io001_empty : Nat → Nat := fun _ => 0

/-- `io001_t` has a `One` input arc on place `0`. -/
theorem io001_t_arc : InputArc io001_t 0 .one := ⟨_, rfl, rfl⟩

/-- A second transition: one `One` input arc on place `0` and an output spec that puts a token
back in place `0`. -/
def io001_t2 : Trans Nat :=
  { core := { name := "t2", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 0) }

/-- `io001_t2` has a `One` input arc on place `0`. -/
theorem io001_t2_arc : InputArc io001_t2 0 .one := ⟨_, rfl, rfl⟩

/-- `io001_t` has no output place. -/
theorem io001_t_noOut (p : Nat) : ¬ OutputArc io001_t p := by
  rintro ⟨o, h, -⟩; simp [io001_t] at h

/-- Whether the output spec of `t` names `q`: `OutputArc` as a `Bool`. -/
def io001_isOut (t : Trans Nat) (q : Nat) : Bool :=
  match t.out with
  | some o => decide (q ∈ outPlaces o)
  | none => false

/-- `io001_isOut` decides `OutputArc`. -/
theorem io001_isOut_iff (t : Trans Nat) (q : Nat) : io001_isOut t q = true ↔ OutputArc t q := by
  obtain ⟨c, o, r⟩ := t
  cases o <;> simp [io001_isOut, OutputArc]

/-- A firing relation in which a `One` arc whose place is also an output place does not guard:
a transition fires whenever its input places outside the output spec are marked; it takes one
token from each of those, leaves its other input places as they are, and reports a deposit of
one token in each of those others (so they lose one token and gain one back). -/
def io001_outputBypassFire : FireRel Nat :=
  fun t m d m' =>
    (∀ s ∈ t.core.inputs, io001_isOut t s.place = false → Marked m s.place) ∧
    d = ((t.core.inputs.map NInSpec.place).filter (io001_isOut t)).dedup ∧
    m' = fun q => if q ∈ t.core.inputs.map NInSpec.place ∧ io001_isOut t q = false
      then m q - 1 else m q

/-- A ghost-deposit firing relation: an enabled transition fires, consumes nothing, leaves the
marking as it is and reports a deposit of one token in each of its input places, whether or not
its output spec names them. -/
def io001_ghostFire : FireRel Nat :=
  fun t m d m' => Enabled t m ∧ d = (t.core.inputs.map NInSpec.place).dedup ∧ m' = m

/-- A firing relation in which a `One` arc needs 2 tokens: a reference firing, allowed only when
every `One` input place holds at least 2 tokens. -/
def io001_needsTwoFire : FireRel Nat :=
  fun t m d m' => RefFire t m d m' ∧ ∀ s ∈ t.core.inputs, s.card = .one → 2 ≤ m s.place

/-- A firing relation that consumes nothing: an enabled transition fires, deposits nothing and
leaves the marking as it is. -/
def io001_idleFire : FireRel Nat := fun t m d m' => Enabled t m ∧ d = [] ∧ m' = m

/-- ✗ A `One` arc that does not guard its transition violates IO-001 (first clause): `io001_t2`
fires from the empty marking, its place `0` being an output place. -/
@[evidence forbids IO_001]
theorem IO_001_forbids_outputBypass : ¬ IO_001 io001_outputBypassFire := by
  intro h
  refine (h io001_t2 0 io001_t2_arc).1 io001_empty _ ⟨_, ?_, rfl, rfl⟩ (by decide)
  intro s hs hno
  simp [io001_t2] at hs
  subst hs
  exact absurd hno (by decide)

/-- ✗ A firing that consumes nothing but reports a deposit in its input place violates IO-001
(third clause, its second part): `io001_t` has no output place, fires from the marking with one
token in place `0` and leaves that token there. -/
@[evidence forbids IO_001]
theorem IO_001_forbids_ghost : ¬ IO_001 io001_ghostFire := by
  intro h
  have := ((h io001_t 0 io001_t_arc).2.2 (by decide) io001_one [0] io001_one
    ⟨by decide, by decide, rfl⟩).2 (io001_t_noOut 0)
  exact absurd this (by decide)

/-- ✗ A `One` arc that needs 2 tokens violates IO-001 (second clause): with place `0` holding
one token, `io001_t` cannot fire, but without its input arc it can. -/
@[evidence forbids IO_001]
theorem IO_001_forbids_needsTwo : ¬ IO_001 io001_needsTwoFire := by
  intro h
  have hw : ∃ m', Fire io001_needsTwoFire (io001_withoutInput io001_t 0) io001_one m' :=
    ⟨io001_one, [], ⟨by decide, ⟨.action 0, rfl⟩, by
      funext n; simp [fireNC, depProd, nconsumed, nspecAt, io001_withoutInput, io001_t,
        io001_one]⟩, by simp [io001_withoutInput, io001_t]⟩
  obtain ⟨m', d, -, h2⟩ := ((h io001_t 0 io001_t_arc).2.1 io001_one (by decide)).2 hw
  exact absurd (h2 ⟨0, .one⟩ (by simp [io001_t]) rfl) (by decide)

/-- ✗ A firing that consumes nothing violates IO-001 (third clause): `io001_t` fires from the
marking with one token in place `0` and leaves that token there. -/
@[evidence forbids IO_001]
theorem IO_001_forbids_idle : ¬ IO_001 io001_idleFire := by
  intro h
  have := ((h io001_t 0 io001_t_arc).2.2 (by decide) io001_one [] io001_one
    ⟨by decide, rfl, rfl⟩).1
  exact absurd this (by decide)

/-! ### Mutants: each drops one clause, and a relation tells it apart from IO-001 -/

/-- Mutant reading of IO-001 that drops the first clause: the arc may let its transition fire
from a marking in which its place is unmarked. -/
def IO_001_mutant_dropUnmarked {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t p, InputArc t p .one →
    (∀ m, Marked m p →
      ((∃ m', Fire F t m m') ↔ (∃ m', Fire F (io001_withoutInput t p) m m'))) ∧
    (¬ ResetArc t p → ∀ m d m', F t m d m' →
      m' p + 1 = m p + Deposits d p ∧ (¬ OutputArc t p → m' p + 1 = m p))

/-- The output-bypass firing kills the first mutant: a transition fires exactly when its input
places outside the output spec are marked, which a marked `One` place does not change, so the
second clause holds; an input place outside the output spec loses one token and one in it loses
one and gets it back, so the third does; but `io001_t2` fires from the empty marking. -/
@[evidence mutant IO_001]
theorem IO_001_mutant_dropUnmarked_killed :
    IO_001_mutant_dropUnmarked io001_outputBypassFire ∧ ¬ IO_001 io001_outputBypassFire := by
  refine ⟨fun t p hp => ⟨fun m hm => ?_, fun _ m d m' ⟨hc, hd, hm'⟩ => ?_⟩,
    IO_001_forbids_outputBypass⟩
  · have hout : ∀ q, io001_isOut (io001_withoutInput t p) q = io001_isOut t q := fun _ => rfl
    constructor
    · rintro ⟨-, -, hc, -, -⟩
      exact ⟨_, _, fun s hs hno => hc s (List.mem_of_mem_eraseP hs) (by rw [← hout]; exact hno),
        rfl, rfl⟩
    · rintro ⟨-, -, hc, -, -⟩
      refine ⟨_, _, fun s hs hno => ?_, rfl, rfl⟩
      by_cases hsp : s.place = p
      · rw [hsp]; exact hm
      · exact hc s ((List.mem_eraseP_of_neg (by simpa using hsp)).2 hs)
          (by rw [hout]; exact hno)
  · obtain ⟨s, hmem, hsp, -, -⟩ := io001_inputArc_mem hp
    have hin : p ∈ t.core.inputs.map NInSpec.place := List.mem_map.2 ⟨s, hmem, hsp⟩
    subst hd hm'
    cases ho : io001_isOut t p
    · have hmk : Marked m p := hsp ▸ hc s hmem (by rw [hsp]; exact ho)
      have h0 : Deposits ((t.core.inputs.map NInSpec.place).filter (io001_isOut t)).dedup p = 0 :=
        List.count_eq_zero_of_not_mem (by simp [ho])
      simp only [Marked] at hmk
      simp only [hin, ho, and_self, if_true, h0]
      omega
    · have h1 : Deposits ((t.core.inputs.map NInSpec.place).filter (io001_isOut t)).dedup p = 1 :=
        List.count_eq_one_of_mem (List.nodup_dedup _)
          (List.mem_dedup.2 (List.mem_filter.2 ⟨hin, ho⟩))
      simp only [ho, Bool.true_eq_false, and_false, if_false, h1]
      exact ⟨trivial, fun hno => absurd ((io001_isOut_iff t p).1 ho) hno⟩

/-- Mutant reading of IO-001 that drops the second clause: a marked place need not let the
transition fire. -/
def IO_001_mutant_dropMarked {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t p, InputArc t p .one →
    (while (fun m => ¬ Marked m p), never Fire F t) ∧
    (¬ ResetArc t p → ∀ m d m', F t m d m' →
      m' p + 1 = m p + Deposits d p ∧ (¬ OutputArc t p → m' p + 1 = m p))

/-- The needs-two firing kills the second mutant: it is a reference firing restricted further,
so it never fires with the place unmarked and consumes 1 token; but with one token in place `0`
`io001_t` cannot fire, although without its input arc it can. -/
@[evidence mutant IO_001]
theorem IO_001_mutant_dropMarked_killed :
    IO_001_mutant_dropMarked io001_needsTwoFire ∧ ¬ IO_001 io001_needsTwoFire := by
  refine ⟨fun t p hp => ⟨?_, fun hr m d m' hf => ?_⟩, IO_001_forbids_needsTwo⟩
  · rintro m m' ⟨d, hf, -⟩
    exact (IO_001_reference t p hp).1 m m' ⟨d, hf⟩
  · exact (IO_001_reference t p hp).2.2 hr m d m' hf.1

/-- Mutant reading of IO-001 that drops the third clause: a firing may take any number of tokens
from the place. -/
def IO_001_mutant_dropConsume {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t p, InputArc t p .one →
    (while (fun m => ¬ Marked m p), never Fire F t) ∧
    (∀ m, Marked m p →
      ((∃ m', Fire F t m m') ↔ (∃ m', Fire F (io001_withoutInput t p) m m')))

/-- The idle firing kills the third mutant: it fires exactly where the reference does, so the
first two clauses hold; but it leaves the token of `io001_t`'s input place where it is. -/
@[evidence mutant IO_001]
theorem IO_001_mutant_dropConsume_killed :
    IO_001_mutant_dropConsume io001_idleFire ∧ ¬ IO_001 io001_idleFire := by
  have hex : ∀ t m, (∃ m', Fire io001_idleFire t m m') ↔ Enabled t m := fun t m =>
    ⟨fun ⟨_, _, he, _⟩ => he, fun he => ⟨m, [], he, rfl, rfl⟩⟩
  refine ⟨fun t p hp => ⟨?_, fun m hm => ?_⟩, IO_001_forbids_idle⟩
  · rintro m m' ⟨d, he, -⟩
    exact fun hm => hm (io001_enabled_marked hp he)
  · rw [hex, hex]
    exact io001_enabled_without hp hm

/-- Mutant reading of IO-001 that drops the second part of the third clause: the count trusts
the deposit the firing reports, also in a place outside the output spec. -/
def IO_001_mutant_trustDeposit {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t p, InputArc t p .one →
    (while (fun m => ¬ Marked m p), never Fire F t) ∧
    (∀ m, Marked m p →
      ((∃ m', Fire F t m m') ↔ (∃ m', Fire F (io001_withoutInput t p) m m'))) ∧
    (¬ ResetArc t p → ∀ m d m', F t m d m' → m' p + 1 = m p + Deposits d p)

/-- The ghost-deposit firing kills the fourth mutant: it fires exactly where the reference does,
so the first two clauses hold, and the deposit of one token it reports in the input place makes
up for the token it does not take; but `io001_t` has no output place, and its input place keeps
its token. -/
@[evidence mutant IO_001]
theorem IO_001_mutant_trustDeposit_killed :
    IO_001_mutant_trustDeposit io001_ghostFire ∧ ¬ IO_001 io001_ghostFire := by
  have hex : ∀ t m, (∃ m', Fire io001_ghostFire t m m') ↔ Enabled t m := fun t m =>
    ⟨fun ⟨_, _, he, _⟩ => he, fun he => ⟨m, _, he, rfl, rfl⟩⟩
  refine ⟨fun t p hp => ⟨?_, fun m hm => ?_, fun _ m d m' ⟨_, hd, hm'⟩ => ?_⟩,
    IO_001_forbids_ghost⟩
  · rintro m m' ⟨d, he, -⟩
    exact fun hm => hm (io001_enabled_marked hp he)
  · rw [hex, hex]
    exact io001_enabled_without hp hm
  · obtain ⟨s, hmem, hsp, -, -⟩ := io001_inputArc_mem hp
    have hin : p ∈ (t.core.inputs.map NInSpec.place).dedup :=
      List.mem_dedup.2 (List.mem_map.2 ⟨s, hmem, hsp⟩)
    have hc : Deposits d p = 1 := by
      rw [hd]; exact List.count_eq_one_of_mem (List.nodup_dedup _) hin
    rw [hc, hm']

/-- All three clauses of IO-001 are exercised by the reference semantics, on the test
derivation's marking: `io001_t` has a `One` arc on place `0`; it does not fire from the empty
marking (first clause); with one token in place `0` it fires, as it does without its input arc
(second clause); and from 3 tokens it fires to 2 (third clause: 1 consumed, 2 remain). -/
@[evidence nonvacuous IO_001]
theorem IO_001_nonvacuous :
    InputArc io001_t 0 .one ∧
      ¬ (∃ m', Fire RefFire io001_t io001_empty m') ∧
      Fire RefFire io001_t io001_one io001_empty ∧
      Fire RefFire (io001_withoutInput io001_t 0) io001_one io001_one ∧
      RefFire io001_t io001_three [] io001_two := by
  refine ⟨io001_t_arc, ?_, ⟨[], by decide, ⟨.action 0, rfl⟩, ?_⟩,
    ⟨[], by decide, ⟨.action 0, rfl⟩, ?_⟩, ⟨by decide, ⟨.action 0, rfl⟩, ?_⟩⟩
  · rintro ⟨m', d, hen, -⟩
    exact absurd hen (by decide)
  · funext n
    by_cases h : n = 0
    · subst h; simp [fireNC, depProd, nconsumed, nspecAt, io001_t, io001_one, io001_empty,
        Card.consumesAll, Card.required]
    · simp [fireNC, depProd, nconsumed, nspecAt, io001_t, io001_one, io001_empty, h, Ne.symm h]
  · funext n; simp [fireNC, depProd, nconsumed, nspecAt, io001_withoutInput, io001_t, io001_one]
  · funext n
    by_cases h : n = 0
    · subst h; simp [fireNC, depProd, nconsumed, nspecAt, io001_t, io001_three, io001_two,
        Card.consumesAll, Card.required]
    · simp [fireNC, depProd, nconsumed, nspecAt, io001_t, io001_three, io001_two, h, Ne.symm h]

end Libpetri.Spec
