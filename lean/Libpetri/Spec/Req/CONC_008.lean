import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryEnable
import Libpetri.Spec.Req.CONC_004
import Libpetri.Spec.GlossaryNu

set_option linter.missingDocs true

/-!
# CONC-008: Multi-phase enablement (`spec/05-concurrency.md`)

CONC-008 is a pure function of a transition and a marking: the enablement check of a transition
that builds and has no match specification is the presence check on the presence bitmap of the
marking (phase 1, CONC-004), followed, for a transition with an `Exactly(n)`, `All` or
`AtLeast(m)` input, by the cardinality check (phase 2), and it passes exactly when the transition
is enabled. The requirement is a predicate over the abstract check `C : EnableCheck N` of CONC-004
(glossary `GlossaryEnable.lean`), for the transitions that build (glossary `Builds`), as CORE-022
is. The evidence theorems check it against the reference check `refEnableCheck` (CONC-004's
file), against the checks the runtimes compute, which skip phase 2 where phase 1 already decides
(allowed), a check that evaluates phase 2 first (allowed), a phase 2 that adds up duplicate input
arcs (allowed, since such a transition does not build), the check that stops after phase 1, a
check that runs phase 2 alone, a phase 2 that asks for exactly `n` tokens, a whole check whose
needs-mask drops the read places, and a check that sends a transition with only `One` inputs to
phase 2. `conc004_008_pins_check` shows that CONC-004 and CONC-008 together fix the whole check
of every transition that builds.

Phase 3, the ν-match check (AC3), is the second block of this file, `CONC_008_nu`, over an
abstract check `C : NuEnableCheck N V Nm` on transitions that may carry a match specification
(glossary `GlossaryNu.lean`) and queue markings: its base is the count-level check above, applied
to the transition without its match and the token counts; for a transition with a match the
whole check is that base and then the ν-match check, which passes exactly when some name is
eligible ([NU-020]); without a match it is the base alone, with no per-token phase. The evidence
checks it against the reference `refNuEnableCheck`, a check without phase 3, a ν-match check that
ignores the required counts, a guard on token values and a base that stops after phase 1.
`conc008_nu_pins_check` shows that CONC-004 and the two blocks together fix the whole check.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-- Every input arc of `t` has cardinality `One` (vacuously true of a transition with no input
arc). Its negation is "`t` has an `Exactly(n)`, `All` or `AtLeast(m)` input", the transitions
CONC-008's phase 2 is for. (Local to CONC-008.) -/
def OnlyOneInputs {N : Type} (t : Trans N) : Prop := ∀ s ∈ t.core.inputs, s.card = Card.one

instance {N : Type} (t : Trans N) : Decidable (OnlyOneInputs t) := by
  unfold OnlyOneInputs; infer_instance

/-! ## CONC-008: Multi-phase enablement -/

requirement CONC_008
  id "CONC-008"
  title "Multi-Phase Enablement"
  kind F
  scope "all executors, transitions that build and have no match specification"
  source verbatim "spec/05-concurrency.md"
  quote "*When* a transition that builds has no match specification and has an `Exactly(n)`, `All` or `AtLeast(m)` input, and its presence check passes on the presence bitmap of the marking, its cardinality check *shall* pass exactly when every input place holds at least its required count."
        "*When* a transition that builds has no match specification and has an `Exactly(n)`, `All` or `AtLeast(m)` input, its enablement check *shall* pass exactly when the presence check passes on the presence bitmap of the marking and the cardinality check passes."
        "*When* a transition that builds has no match specification and no `Exactly(n)`, `All` or `AtLeast(m)` input, its enablement check *shall* pass exactly when the presence check passes on the presence bitmap of the marking."
        "*When* a transition that builds has no match specification, its enablement check *shall* pass exactly when the transition is enabled ([CORE-022])."
  reading "For every transition t that builds (Builds t: distinct input places, every input arc requiring at least one token, no place with both an input arc and a read arc, a well-formed output spec; no transition has a match specification here) and every count marking m:"
          "if t has an input that is not `One` and the presence check of t passes on the presence bitmap of m, the cardinality check of t passes on m exactly when every input place of t holds at least its required count;"
          "if t has an input that is not `One`, the enablement check of t on m passes exactly when the presence check of t passes on the presence bitmap of m and the cardinality check of t passes on m;"
          "if t has no input that is not `One` (a transition with no input arc included), the enablement check of t on m passes exactly when the presence check of t passes on the presence bitmap of m;"
          "the enablement check of t on m passes exactly when t is enabled in m."
  assumes "A marking is read as its token counts (CountMarking) and its presence bitmap as one bit per place, set exactly when the place is marked (glossary: Presence bitmap). The check is the abstract EnableCheck of CONC-004: its presence phase on a bitmap, its cardinality phase on counts, and the whole check on a marking."
          "'The presence check' in the quoted sentences is the glossary term that CONC-004 pins, so the sentences mean this block and CONC-004 together; the presence phase is constrained there, not here. Read alone, this block accepts a presence phase that ignores the input bits of a transition with an input that is not `One`, since its cardinality phase covers those places (conc008_dropInputs_ok); CONC-004 kills that check (CONC_004_forbids_dropInputs). The two blocks hold together of one check (CONC_004_008_consistent), and together they fix the whole check of every transition that builds to the reference check (conc004_008_pins_check)."
          "Every line speaks of transitions that build (glossary: Builds), as CORE-022 does: a definition that building rejects is held by no executor, so no check is asked of it. Two build checks matter here. IO-002 and IO-004 reject an `Exactly(0)` or `AtLeast(0)` input, which is enabled on an empty place but fails the presence check: without them the fourth line contradicts the second line together with CONC-004 (conc008_unscoped_conflict). CORE-030 rejects two input arcs on one place, which have no coherent consumption semantics: a cardinality phase that adds up the required counts of all arcs on one place answers what the reference answers on every transition that builds, and the block allows it (CONC_008_allows_sumDup)."
          "Phase 3 and AC3 (a transition with a match specification needs the ν-match check, which scans its correlated inputs for a shared name, [NU-020]) are the second block of this file, CONC_008_nu: the count-level transition has no match specification, so every quoted sentence here is stated for transitions without one. The lines for a transition with one, and the body item 'This is the only per-token phase; there is no value-predicate phase (guards were removed, [IO-006])', are that block's. At the count level no check sees token values, so a value-predicate phase cannot be expressed; the fourth line already forbids any extra phase that rejects an enabled transition."
          "A transition with no `Exactly(n)`, `All` or `AtLeast(m)` input, including one with no input arc at all (a read-only, inhibitor-only or source transition), is checked by phase 1 alone (third line, AC1). 'Fully checked in Phase 1' is read as 'the answer of the check is the answer of phase 1': computing phase 2 anyway is not forbidden, and its cardinality phase is not constrained. Rust and TypeScript skip phase 2 for it (they build no cardinality check unless some input is not `One`); Java also skips it for an `Exactly(1)` input (it builds one only for a required count above 1, `All` or `AtLeast`); the reference runs phase 2 for every transition, where it passes whenever phase 1 does. All three satisfy the block (CONC_008_reference, CONC_008_allows_skipOneOnly, CONC_008_allows_skipJava). For a transition with an input that is not `One`, phase 2 checks every input place, `One` inputs included, as the runtimes do."
          "'Phases 2 and 3 are only reached if Phase 1 passes, minimizing work for most transitions' is not encoded as an order of evaluation. The second line is an equation of Boolean values, whose answer does not depend on the order its parts are evaluated in, so a check that evaluates phase 2 first, or always, satisfies it (CONC_008_allows_cardFirst). What the sentence implies for the answer is encoded: the whole check passes only if phase 1 does (second and third lines), and where phase 1 fails phase 2 is not constrained (the first line is stated only at a marking where phase 1 passes; there a skipped phase 2 passes trivially, and that is the right answer because every input place is marked). The order and the saving of work are quality properties. Phase 1's 'O(W) bitwise check' and 'fast reject for most transitions' are CONC-004's and PERF-002's quality properties."
          "Which marking the phases read is not this ID's subject: in the enablement update the presence phase reads the bitmap snapshot and the cardinality phase the live counts, taken at the same instant; in the recheck of a firing pass (EXEC-003) the cardinality phase discounts same-pass deposits. This block is the function of one marking; the pass recheck is EXEC-003's."
          "The body names the mask test of CONC-004 the 'Enablement check' and this ID makes it phase 1 (clash conc-a#10). The reading in which CONC-004's formula is the whole enablement check is the mutant CONC_008_mutant_maskOnly, killed by AC2."
          "With CONC-004 in force, the fourth line follows from the first three; it is kept because this block alone needs it: it makes phase 1 on the presence bitmap agree with enablement for a transition with only `One` inputs, and CONC_008_forbids_cardOnly uses it."
          "AC1 (a transition with only One inputs and no match specification is fully checked in phase 1) is the third line (CONC_008_mutant_noPhase1Only_killed, CONC_008_nonvacuous)."
          "AC2 (a transition with an Exactly(5) input needs phase 2 to verify the token count) is the first and second lines: with three tokens the presence check passes, the cardinality check fails and so does the enablement check (CONC_008_mutant_maskOnly_killed, CONC_008_nonvacuous). CONC_008_nonvacuous also runs an `All` input and an `AtLeast(3)` input through both phases."
          "AC3 is not encoded here: it is the block CONC_008_nu (see above)."
          "The test derivation's 'correct enablement' is the fourth line; its 'minimal re-evaluation' is CONC-005's subject."
  signoff "2026-11-13 2ed06600a6fb11e9 ai"
  statement : ∀ {N : Type} [DecidableEq N], EnableCheck N → Prop :=
    fun C => ∀ t, Builds t → ∀ m,
      (¬ OnlyOneInputs t → C.presence t (presenceOf m) = true →
        (C.cardinality t m = true ↔ CardinalityOk t m)) ∧
      (¬ OnlyOneInputs t →
        C.check t m = (C.presence t (presenceOf m) && C.cardinality t m)) ∧
      (OnlyOneInputs t → C.check t m = C.presence t (presenceOf m)) ∧
      (C.check t m = true ↔ Enabled t m)

/- The pinned readable form of CONC-008: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CONC_008 : {N : Type} → [DecidableEq N] → EnableCheck N → Prop :=
fun {N} [DecidableEq N] C =>
  ∀ (t : Reference.Trans N),
    Builds t →
      ∀ (m : CountMarking N),
        (¬OnlyOneInputs t → C.presence t (presenceOf m) = true → (C.cardinality t m = true ↔ CardinalityOk t m)) ∧
          (¬OnlyOneInputs t → C.check t m = (C.presence t (presenceOf m) && C.cardinality t m)) ∧
            (OnlyOneInputs t → C.check t m = C.presence t (presenceOf m)) ∧ (C.check t m = true ↔ Enabled t m)
-/
#guard_msgs in #print CONC_008

/-! ### The reference -/

section Reference

variable {N : Type}

/-- The cardinality phase of the reference check is the glossary's cardinality check. -/
theorem refEnableCheck_cardinality (t : Trans N) (m : CountMarking N) :
    (refEnableCheck (N := N)).cardinality t m = true ↔ CardinalityOk t m := by
  simp [refEnableCheck, CardinalityOk]

/-- The reference check is its presence phase on the presence bitmap, and then its cardinality
phase. -/
theorem refEnableCheck_check (t : Trans N) (m : CountMarking N) :
    (refEnableCheck (N := N)).check t m =
      ((refEnableCheck (N := N)).presence t (presenceOf m) &&
        (refEnableCheck (N := N)).cardinality t m) := rfl

/-- For a transition whose inputs each require exactly one token, the presence check on the
presence bitmap of a marking passes exactly when the transition is enabled. -/
theorem refEnableCheck_presence_enabled {t : Trans N}
    (hone : ∀ s ∈ t.core.inputs, requiredCount s.card = 1) (m : CountMarking N) :
    (refEnableCheck (N := N)).presence t (presenceOf m) = true ↔ Enabled t m := by
  rw [refEnableCheck_presence, maskCheck_presenceOf, enabled_iff]
  constructor
  · rintro ⟨hi, hr, hh⟩
    refine ⟨fun s hs => ?_, hh, hr⟩
    have h2 := hi s hs
    simp only [Marked] at h2
    rw [hone s hs]
    omega
  · rintro ⟨hc, hh, hr⟩
    refine ⟨fun s hs => ?_, hr, hh⟩
    have h2 := hc s hs
    rw [hone s hs] at h2
    simp only [Marked]
    omega

/-- For a transition whose inputs each require at least one token, the reference check passes
exactly when the transition is enabled. -/
theorem refEnableCheck_enabled {t : Trans N} (hpos : InputCountsPositive t) (m : CountMarking N) :
    (refEnableCheck (N := N)).check t m = true ↔ Enabled t m := by
  rw [refEnableCheck_check, Bool.and_eq_true, refEnableCheck_presence,
    refEnableCheck_cardinality, maskCheck_presenceOf, enabled_iff, CardinalityOk]
  constructor
  · rintro ⟨⟨-, hr, hh⟩, hc⟩
    exact ⟨hc, hh, hr⟩
  · rintro ⟨hc, hh, hr⟩
    refine ⟨⟨fun s hs => ?_, hr, hh⟩, hc⟩
    have h1 := hpos s hs
    have h2 := hc s hs
    simp only [Marked]
    omega

/-- Every input of a transition with only `One` inputs requires exactly one token. -/
theorem onlyOneInputs_req {t : Trans N} (hone : OnlyOneInputs t) :
    ∀ s ∈ t.core.inputs, requiredCount s.card = 1 :=
  fun s hs => by simp [requiredCount, hone s hs, Card.required]

/-- The cardinality check passes on a marking at which the presence check passes, for a
transition whose inputs each require at most one token. -/
theorem cardinalityOk_of_presence {t : Trans N} (hle : ∀ s ∈ t.core.inputs, requiredCount s.card ≤ 1)
    {m : CountMarking N} (hp : (refEnableCheck (N := N)).presence t (presenceOf m) = true) :
    CardinalityOk t m := by
  rw [refEnableCheck_presence, maskCheck_presenceOf] at hp
  intro s hs
  have h1 := hle s hs
  have h2 := hp.1 s hs
  simp only [Marked] at h2
  omega

/-- A transition that builds has every input requiring at least one token ([IO-002],
[IO-004]). -/
theorem Builds.pos [DecidableEq N] {t : Trans N} (hb : Builds t) : InputCountsPositive t :=
  hb.1.2.1

/-- A transition that builds has distinct input places ([CORE-030]). -/
theorem Builds.distinct [DecidableEq N] {t : Trans N} (hb : Builds t) : (inPlaces t).Nodup :=
  hb.1.1

end Reference

/-- ✓ The reference check satisfies CONC-008: its whole check is its presence phase on the
presence bitmap and then its cardinality phase (`refEnableCheck_check`), the cardinality phase
is the glossary's (`refEnableCheck_cardinality`), and together they decide enablement for every
transition whose inputs each require a token (`refEnableCheck_enabled`), as every transition
that builds does; for a transition with only `One` inputs the cardinality phase passes whenever
the presence phase does. -/
@[evidence holds CONC_008]
theorem CONC_008_reference {N : Type} [DecidableEq N] : CONC_008 (refEnableCheck (N := N)) := by
  intro t hb m
  refine ⟨fun _ _ => refEnableCheck_cardinality t m, fun _ => refEnableCheck_check t m,
    fun hone => ?_, refEnableCheck_enabled hb.pos m⟩
  have h2 := refEnableCheck_presence_enabled (onlyOneInputs_req hone) m
  have h1 := refEnableCheck_enabled hb.pos m
  cases hc : (refEnableCheck (N := N)).check t m <;>
    cases hp : (refEnableCheck (N := N)).presence t (presenceOf m) <;> simp_all

/-- ✓ CONC-004 and CONC-008 hold together of one check: the reference check satisfies both. -/
@[evidence consistent CONC_004 CONC_008]
theorem CONC_004_008_consistent {N : Type} [DecidableEq N] :
    ∃ C : EnableCheck N, CONC_004 C ∧ CONC_008 C :=
  ⟨refEnableCheck, CONC_004_reference, CONC_008_reference⟩

/-- CONC-004 and CONC-008 together fix the whole check: on every transition that builds, a check
that satisfies both answers what the reference check answers, at every marking. Only the
cardinality phase keeps some freedom, where the whole check never consults it. -/
theorem conc004_008_pins_check {N : Type} [DecidableEq N] (C : EnableCheck N) (h4 : CONC_004 C)
    (h8 : CONC_008 C) (t : Trans N) (hb : Builds t) (m : CountMarking N) :
    C.check t m = refEnableCheck.check t m := by
  have hp : C.presence t (presenceOf m) = refEnableCheck.presence t (presenceOf m) := by
    rw [Bool.eq_iff_iff, h4, refEnableCheck_presence]
  by_cases hone : OnlyOneInputs t
  · rw [(h8 t hb m).2.2.1 hone, hp]
    exact ((CONC_008_reference t hb m).2.2.1 hone).symm
  · rw [(h8 t hb m).2.1 hone, refEnableCheck_check, hp]
    cases hr : refEnableCheck.presence t (presenceOf m)
    · rfl
    · simp only [Bool.true_and]
      rw [Bool.eq_iff_iff, (h8 t hb m).1 hone (hp.trans hr), refEnableCheck_cardinality]

/-- CONC-008 passes from one check to another that agrees with it on every transition that
builds. -/
theorem conc008_congr {N : Type} [DecidableEq N] {C C' : EnableCheck N}
    (h : ∀ t, Builds t → C.presence t = C'.presence t ∧ C.cardinality t = C'.cardinality t ∧
      C.check t = C'.check t)
    (h' : CONC_008 C') : CONC_008 C := by
  intro t hb m
  obtain ⟨hp, hc, hk⟩ := h t hb
  rw [hp, hc, hk]
  exact h' t hb m

/-! ### Allowed: phase 2 skipped where phase 1 decides -/

/-- The reference check with phase 2 skipped (passing trivially) for every transition `skip`
picks: the shape of the runtimes' check, which builds a cardinality check only for some
transitions. -/
def conc008_skipWith {N : Type} (skip : Trans N → Bool) : EnableCheck N where
  presence := refEnableCheck.presence
  cardinality t m := skip t || refEnableCheck.cardinality t m
  check t m := refEnableCheck.presence t (presenceOf m) && (skip t || refEnableCheck.cardinality t m)

/-- CONC-008 holds of a check that skips phase 2 for transitions whose inputs each require at
most one token, provided it skips it for every transition with only `One` inputs. -/
theorem conc008_skipWith_ok {N : Type} [DecidableEq N] (skip : Trans N → Bool)
    (hle : ∀ t, skip t = true → ∀ s ∈ t.core.inputs, requiredCount s.card ≤ 1)
    (hone : ∀ t, OnlyOneInputs t → skip t = true) : CONC_008 (conc008_skipWith skip) := by
  intro t hb m
  refine ⟨fun _ hp => ?_, fun _ => rfl, fun h => ?_, ?_⟩
  · cases hs : skip t
    · simp only [conc008_skipWith, hs, Bool.false_or]
      exact refEnableCheck_cardinality t m
    · simp only [conc008_skipWith, hs, Bool.true_or, true_iff]
      exact cardinalityOk_of_presence (hle t hs) hp
  · simp only [conc008_skipWith, hone t h, Bool.true_or, Bool.and_true]
  · cases hs : skip t
    · simp only [conc008_skipWith, hs, Bool.false_or]
      exact refEnableCheck_enabled hb.pos m
    · simp only [conc008_skipWith, hs, Bool.true_or, Bool.and_true]
      exact refEnableCheck_presence_enabled
        (fun s h => Nat.le_antisymm (hle t hs s h) (hb.pos s h)) m

/-- Rust's and TypeScript's choice: phase 2 is built only for a transition with an input that is
not `One` (`compiled_net.rs` and `compiled-net.ts`, `needsCardinality`). -/
def conc008_skipOneOnly {N : Type} (t : Trans N) : Bool := decide (OnlyOneInputs t)

/-- Java's choice: phase 2 is built only for a transition with an input whose required count is
above 1, or that is `All` or `AtLeast` (`CompiledNet.java`, `needsCardinality`). -/
def conc008_skipJava {N : Type} (t : Trans N) : Bool :=
  t.core.inputs.all fun s => match s.card with
    | .one => true
    | .exactly n => decide (n ≤ 1)
    | _ => false

/-- CONC-008 allows a check that skips phase 2 for a transition with only `One` inputs, as Rust
and TypeScript do (AC1, 'fully checked in Phase 1'). -/
@[evidence allows CONC_008]
theorem CONC_008_allows_skipOneOnly : CONC_008 (conc008_skipWith (conc008_skipOneOnly (N := Nat))) :=
  conc008_skipWith_ok _
    (fun t h s hs => by
      simp only [conc008_skipOneOnly, decide_eq_true_eq] at h
      simp [requiredCount, h s hs, Card.required])
    (fun t h => by simpa [conc008_skipOneOnly] using h)

/-- CONC-008 allows a check that also skips phase 2 for an `Exactly(1)` input, as Java does: the
first line asks for the cardinality answer only where phase 1 passed, and there every input
place is marked. -/
@[evidence allows CONC_008]
theorem CONC_008_allows_skipJava : CONC_008 (conc008_skipWith (conc008_skipJava (N := Nat))) := by
  refine conc008_skipWith_ok _ (fun t h s hs => ?_) (fun t h => ?_)
  · simp only [conc008_skipJava, List.all_eq_true] at h
    have := h s hs
    revert this
    cases s.card <;> simp [requiredCount, Card.required]
  · simp only [conc008_skipJava, List.all_eq_true]
    intro s hs
    simp [h s hs]

/-! ### Allowed: phase 2 evaluated first -/

/-- The reference check with its two phases evaluated in the other order: phase 2 first, then
phase 1, both always. -/
def conc008_cardFirst {N : Type} : EnableCheck N :=
  { refEnableCheck with
    check := fun t m => refEnableCheck.cardinality t m && refEnableCheck.presence t (presenceOf m) }

/-- CONC-008 allows a check that evaluates phase 2 before phase 1: the second line is an equation
of Boolean values, so 'Phases 2 and 3 are only reached if Phase 1 passes' fixes no order of
evaluation and no saving of work, only the answer. -/
@[evidence allows CONC_008]
theorem CONC_008_allows_cardFirst : CONC_008 (conc008_cardFirst (N := Nat)) :=
  conc008_congr (C' := refEnableCheck) (fun _ _ => ⟨rfl, rfl, by
    funext m
    simp only [conc008_cardFirst, Bool.and_comm]
    rfl⟩) CONC_008_reference

/-! ### Allowed: a phase 2 that adds up duplicate input arcs -/

/-- A cardinality phase that asks each input place for the sum of the required counts of all
input arcs on it. It differs from the reference only on a transition with two input arcs on one
place, which CORE-030 rejects at build. -/
def conc008_sumCard (t : Trans Nat) (m : CountMarking Nat) : Bool :=
  t.core.inputs.all fun s =>
    decide (((t.core.inputs.filter fun s' => s'.place == s.place).map
      (fun s' => requiredCount s'.card)).sum ≤ m s.place)

/-- The reference check with the summing cardinality phase `conc008_sumCard`. -/
def conc008_sumDup : EnableCheck Nat :=
  { refEnableCheck with
    cardinality := conc008_sumCard
    check := fun t m => refEnableCheck.presence t (presenceOf m) && conc008_sumCard t m }

/-- On a list of input arcs on distinct places, the arcs on the place of one of them are that
one alone. -/
theorem conc008_filter_single (l : List (NInSpec Nat)) (hd : (l.map (·.place)).Nodup) :
    ∀ s ∈ l, (l.filter fun s' => s'.place == s.place) = [s] := by
  induction l with
  | nil => intro s hs; simp at hs
  | cons a l ih =>
    intro s hs
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hd
    rcases List.mem_cons.mp hs with rfl | hl
    · have : (l.filter fun s' => s'.place == s.place) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx
        simp only [beq_iff_eq]
        intro he; exact hd.1 ⟨x, hx, he⟩
      simp [this]
    · have hne : (a.place == s.place) = false := by
        simp only [beq_eq_false_iff_ne]
        intro he; exact hd.1 ⟨s, hl, he.symm⟩
      simp [hne, ih hd.2 s hl]

/-- On a transition with distinct input places the summing phase 2 is the reference one. -/
theorem conc008_sumCard_distinct (t : Trans Nat) (hd : (inPlaces t).Nodup) (m : CountMarking Nat) :
    conc008_sumCard t m = refEnableCheck.cardinality t m := by
  have hf := conc008_filter_single t.core.inputs hd
  rw [Bool.eq_iff_iff]
  simp only [conc008_sumCard, refEnableCheck, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h s hs; have := h s hs; rw [hf s hs] at this; simpa using this
  · intro h s hs; rw [hf s hs]; simpa using h s hs

/-- CONC-008 allows a cardinality phase that adds up the required counts of the input arcs on
one place: on every transition that builds (distinct input places, CORE-030) it is the
reference phase. A transition with two input arcs on one place, where the two disagree, does not
build, so the block asks nothing of it. -/
@[evidence allows CONC_008]
theorem CONC_008_allows_sumDup : CONC_008 conc008_sumDup :=
  conc008_congr (C' := refEnableCheck) (fun t hb => by
    have hc : conc008_sumCard t = refEnableCheck.cardinality t :=
      funext (conc008_sumCard_distinct t hb.distinct)
    exact ⟨rfl, hc, by funext m; simp only [conc008_sumDup, refEnableCheck_check, hc]⟩)
    CONC_008_reference

/-! ### Examples -/

/-- The AC2 transition: an `Exactly(5)` input on place `0`, no other arc. -/
def conc008_tFive : Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .exactly 5⟩], inhibitors := [], reads := [],
              resets := [] },
    out := none }

/-- The AC1 transition: `One` inputs on `0` and `1`, an inhibitor arc on `2`. -/
def conc008_tOne : Trans Nat :=
  { core := { name := "u", inputs := [⟨0, .one⟩, ⟨1, .one⟩], inhibitors := [2], reads := [],
              resets := [] },
    out := none }

/-- A transition with an `All` input on `0` and an `AtLeast(3)` input on `1`. -/
def conc008_tMix : Trans Nat :=
  { core := { name := "x", inputs := [⟨0, .all⟩, ⟨1, .atLeast 3⟩], inhibitors := [], reads := [],
              resets := [] },
    out := none }

/-- A transition with an `Exactly(0)` input on `0`, which IO-002 rejects at build. -/
def conc008_tZero : Trans Nat :=
  { core := { name := "z", inputs := [⟨0, .exactly 0⟩], inhibitors := [], reads := [],
              resets := [] },
    out := none }

/-- The marking in which place `0` holds `k` tokens and every other place is empty. -/
def conc008_at0 (k : Nat) : CountMarking Nat := fun p => if p = 0 then k else 0

/-- The marking in which places `0`, `1` and `2` hold one token each. -/
def conc008_all3 : CountMarking Nat := fun p => if p < 3 then 1 else 0

/-- The marking in which place `0` holds one token, place `1` holds `k` tokens and every other
place is empty. -/
def conc008_mix (k : Nat) : CountMarking Nat := fun p => if p = 0 then 1 else if p = 1 then k else 0

/-! ### Conflict without the build checks -/

/-- Without the build checks the fourth line contradicts the second line together with CONC-004:
`conc008_tZero` (`Exactly(0)` on place `0`) is enabled on the empty marking, so its check must
pass, so by the second line its presence phase passes on the empty bitmap, which CONC-004 forbids
(the input bit of place `0` is clear). This is why every line speaks of transitions that build,
and why the spec sentences say so. -/
theorem conc008_unscoped_conflict :
    ¬ ∃ C : EnableCheck Nat, CONC_004 C ∧
      (∀ t m, ¬ OnlyOneInputs t → C.check t m = (C.presence t (presenceOf m) && C.cardinality t m)) ∧
      (∀ t m, C.check t m = true ↔ Enabled t m) := by
  rintro ⟨C, h4, h2, hen⟩
  have hc := (hen conc008_tZero (fun _ => 0)).2 (by decide)
  rw [h2 conc008_tZero _ (by decide), Bool.and_eq_true] at hc
  have := ((h4 conc008_tZero _).1 hc.1).1 0 (.inl (by simp [inPlaces, conc008_tZero]))
  revert this
  decide

/-! ### Mutant: the presence check as the whole enablement check -/

/-- The check that stops after phase 1: CONC-004's mask test taken as the whole check. -/
def conc008_maskOnly {N : Type} : EnableCheck N :=
  { refEnableCheck with check := fun t m => refEnableCheck.presence t (presenceOf m) }

/-- Mutant reading of CONC-008 in which CONC-004's 'Enablement check' formula is the whole
enablement check, for every transition (clash conc-a#10). -/
def CONC_008_mutant_maskOnly {N : Type} (C : EnableCheck N) : Prop :=
  ∀ t m, C.check t m = C.presence t (presenceOf m)

/-- The check that stops after phase 1 kills the mutant: it satisfies the mutant reading, but
not CONC-008. `conc008_tFive` with three tokens in place `0` passes it, but its cardinality
check fails (AC2). -/
@[evidence mutant CONC_008]
theorem CONC_008_mutant_maskOnly_killed :
    CONC_008_mutant_maskOnly (conc008_maskOnly (N := Nat)) ∧
      ¬ CONC_008 (conc008_maskOnly (N := Nat)) := by
  refine ⟨fun _ _ => rfl, fun h => ?_⟩
  have := (h conc008_tFive (by decide) (conc008_at0 3)).2.1 (by decide)
  revert this
  decide

/-! ### Violation: phase 2 alone -/

/-- A check that runs the cardinality phase only and ignores read and inhibitor places. -/
def conc008_cardOnly {N : Type} : EnableCheck N :=
  { refEnableCheck with check := fun t m => refEnableCheck.cardinality t m }

/-- ✗ A check that runs phase 2 alone violates CONC-008: `conc008_tOne` passes it on the
marking with places `0`, `1` and `2` marked, although its inhibitor place `2` is marked, so it
is not enabled (fourth line). -/
@[evidence forbids CONC_008]
theorem CONC_008_forbids_cardOnly : ¬ CONC_008 (conc008_cardOnly (N := Nat)) := by
  intro h
  have := (h conc008_tOne (by decide) conc008_all3).2.2.2.1 (by decide)
  revert this
  decide

/-! ### Violation: phase 2 asks for exactly `n` tokens -/

/-- A check whose cardinality phase reads `Exactly(n)` as "the place holds exactly `n`
tokens". -/
def conc008_exactEq {N : Type} : EnableCheck N :=
  { refEnableCheck with
    cardinality := fun t m => t.core.inputs.all fun s =>
      match s.card with
      | .exactly n => decide (m s.place = n)
      | c => decide (requiredCount c ≤ m s.place) }

/-- ✗ A phase 2 that asks for exactly `n` tokens violates CONC-008: `conc008_tFive` with six
tokens in place `0` fails it, although the place holds at least its required count (first
line). -/
@[evidence forbids CONC_008]
theorem CONC_008_forbids_exactEq : ¬ CONC_008 (conc008_exactEq (N := Nat)) := by
  intro h
  have := ((h conc008_tFive (by decide) (conc008_at0 6)).1 (by decide) (by decide)).2 fun s hs => by
    simp only [conc008_tFive, List.mem_singleton] at hs
    subst hs
    decide
  revert this
  decide

/-! ### Violation: the whole check runs a needs-mask without the read places -/

/-- A check whose presence phase is the reference one, but whose whole check tests a second
needs-mask that leaves out the read places: a sparse mask out of step with the full-width one.
CONC-004 alone accepts it (`conc008_driftedMask_conc004`). -/
def conc008_driftedMask {N : Type} : EnableCheck N :=
  { refEnableCheck with
    check := fun t m => ((inPlaces t).all (presenceOf m) &&
        t.core.inhibitors.all (!presenceOf m ·)) && refEnableCheck.cardinality t m }

/-- CONC-004 accepts the drifted check: it constrains the presence phase only. -/
theorem conc008_driftedMask_conc004 {N : Type} : CONC_004 (conc008_driftedMask (N := N)) :=
  refEnableCheck_presence

/-- ✗ A whole check that drops the read places from its needs-mask violates CONC-008: the read
transition `conc004_tRead` passes it on the empty marking, although its presence phase fails
there (third line). CONC-004 alone does not tell it apart (`conc008_driftedMask_conc004`). -/
@[evidence forbids CONC_008]
theorem CONC_008_forbids_driftedMask : ¬ CONC_008 (conc008_driftedMask (N := Nat)) := fun h => by
  have := (h conc004_tRead (by decide) (fun _ => 0)).2.2.1 (by decide)
  revert this
  decide

/-! ### Violation of CONC-004 that CONC-008 alone accepts: phase 1 without the input bits -/

/-- A presence phase that tests the input bits only for a transition with only `One` inputs; for
any other transition it tests the read and inhibitor bits alone, leaving the inputs to phase 2. -/
def conc008_dropPresence {N : Type} (t : Trans N) (bits : N → Bool) : Bool :=
  if OnlyOneInputs t then refEnableCheck.presence t bits
  else t.core.reads.all bits && t.core.inhibitors.all (!bits ·)

/-- The check with the presence phase `conc008_dropPresence` and the reference phase 2, skipped
for a transition with only `One` inputs. -/
def conc008_dropInputs {N : Type} : EnableCheck N where
  presence := conc008_dropPresence
  cardinality := refEnableCheck.cardinality
  check t m := conc008_dropPresence t (presenceOf m) &&
    (decide (OnlyOneInputs t) || refEnableCheck.cardinality t m)

/-- CONC-008 alone accepts the check whose phase 1 ignores the input bits of a transition with an
input that is not `One`: its phase 2 covers those places. -/
theorem conc008_dropInputs_ok {N : Type} [DecidableEq N] : CONC_008 (conc008_dropInputs (N := N)) := by
  intro t hb m
  by_cases hone : OnlyOneInputs t
  · have hpe := refEnableCheck_presence_enabled (onlyOneInputs_req hone) m
    refine ⟨fun h => absurd hone h, fun h => absurd hone h, fun _ => ?_, ?_⟩
    · simp [conc008_dropInputs, hone]
    · simp only [conc008_dropInputs, conc008_dropPresence, if_pos hone, decide_eq_true hone,
        Bool.true_or, Bool.and_true]
      exact hpe
  · refine ⟨fun _ _ => refEnableCheck_cardinality t m, fun _ => ?_, fun h => absurd h hone, ?_⟩
    · simp [conc008_dropInputs, hone]
    · simp only [conc008_dropInputs, conc008_dropPresence, if_neg hone, decide_eq_false hone,
        Bool.false_or, Bool.and_eq_true, refEnableCheck_cardinality, enabled_iff, CardinalityOk,
        List.all_eq_true, Bool.not_eq_true', presenceOf, decide_eq_true_eq,
        decide_eq_false_iff_not]
      constructor
      · rintro ⟨⟨hr, hh⟩, hc⟩
        exact ⟨hc, hh, hr⟩
      · rintro ⟨hc, hh, hr⟩
        exact ⟨⟨hr, hh⟩, hc⟩

/-- ✗ The check whose phase 1 ignores the input bits violates CONC-004: `conc008_tFive` passes
its presence phase on the empty bitmap, although the input bit of place `0` is clear. CONC-008
alone accepts it (`conc008_dropInputs_ok`). -/
@[evidence forbids CONC_004]
theorem CONC_004_forbids_dropInputs : ¬ CONC_004 (conc008_dropInputs (N := Nat)) := fun h => by
  have := ((h conc008_tFive (fun _ => false)).1 (by decide)).1 0
    (.inl (by simp [inPlaces, conc008_tFive]))
  revert this
  decide

/-! ### Mutant: a transition with only `One` inputs checked in phase 2 -/

/-- A check that sends a transition with only `One` inputs straight to phase 2, which decides
its enablement there; its phase 1 passes it unconditionally. -/
def conc008_onePhase2 {N : Type} : EnableCheck N where
  presence t bits := if OnlyOneInputs t then true else refEnableCheck.presence t bits
  cardinality t m := if OnlyOneInputs t then decide (Enabled t m)
    else refEnableCheck.cardinality t m
  check := refEnableCheck.check

/-- Mutant reading of CONC-008 without AC1: lines 1, 2 and 4 only, so a transition with only
`One` inputs may be decided in phase 2. -/
def CONC_008_mutant_noPhase1Only {N : Type} [DecidableEq N] (C : EnableCheck N) : Prop :=
  ∀ t, Builds t → ∀ m,
    (¬ OnlyOneInputs t → C.presence t (presenceOf m) = true →
        (C.cardinality t m = true ↔ CardinalityOk t m)) ∧
    (¬ OnlyOneInputs t →
      C.check t m = (C.presence t (presenceOf m) && C.cardinality t m)) ∧
    (C.check t m = true ↔ Enabled t m)

/-- The check that decides `One`-only transitions in phase 2 kills the mutant: it satisfies the
mutant reading, but not CONC-008. `conc008_tOne` on the empty marking passes its phase 1,
although its whole check fails (AC1). -/
@[evidence mutant CONC_008]
theorem CONC_008_mutant_noPhase1Only_killed :
    CONC_008_mutant_noPhase1Only (conc008_onePhase2 (N := Nat)) ∧
      ¬ CONC_008 (conc008_onePhase2 (N := Nat)) := by
  refine ⟨fun t hb m => ⟨fun h _ => ?_, fun h => ?_, ?_⟩, fun h => ?_⟩
  · simp only [conc008_onePhase2, if_neg h]
    exact refEnableCheck_cardinality t m
  · simp only [conc008_onePhase2, if_neg h]
    rfl
  · exact refEnableCheck_enabled hb.pos m
  · have := (h conc008_tOne (by decide) (fun _ => 0)).2.2.1 (by decide)
    revert this
    decide

/-! ### Every line exercised (count level) -/

/-- Every line of CONC-008 is exercised by the reference on transitions that build. AC2:
`conc008_tFive` (`Exactly(5)` on place `0`) with three tokens passes the presence check, fails
the cardinality check and the enablement check, and is not enabled; with five tokens all three
pass and it is enabled. `All` and `AtLeast(3)`: `conc008_tMix` with one token in `0` and two in
`1` passes the presence check but not the cardinality check, and with three in `1` passes both
and is enabled. AC1: `conc008_tOne` (`One` on `0` and `1`, inhibitor on `2`) is enabled and
passes the check on the marking with `0` and `1` marked, and fails both the presence check and
the check when `2` is marked too. The build premise matters: `conc008_tZero` (`Exactly(0)`) does
not build, is enabled on the empty marking and fails the presence check there. -/
@[evidence nonvacuous CONC_008]
theorem CONC_008_nonvacuous :
    Builds conc008_tFive ∧ Builds conc008_tOne ∧ Builds conc008_tMix ∧
      (refEnableCheck (N := Nat)).presence conc008_tFive (presenceOf (conc008_at0 3)) = true ∧
      (refEnableCheck (N := Nat)).cardinality conc008_tFive (conc008_at0 3) = false ∧
      (refEnableCheck (N := Nat)).check conc008_tFive (conc008_at0 3) = false ∧
      ¬ Enabled conc008_tFive (conc008_at0 3) ∧
      (refEnableCheck (N := Nat)).cardinality conc008_tFive (conc008_at0 5) = true ∧
      (refEnableCheck (N := Nat)).check conc008_tFive (conc008_at0 5) = true ∧
      Enabled conc008_tFive (conc008_at0 5) ∧
      (refEnableCheck (N := Nat)).presence conc008_tMix (presenceOf (conc008_mix 2)) = true ∧
      (refEnableCheck (N := Nat)).cardinality conc008_tMix (conc008_mix 2) = false ∧
      ¬ Enabled conc008_tMix (conc008_mix 2) ∧
      (refEnableCheck (N := Nat)).check conc008_tMix (conc008_mix 3) = true ∧
      Enabled conc008_tMix (conc008_mix 3) ∧
      (refEnableCheck (N := Nat)).check conc008_tOne (fun p => if p < 2 then 1 else 0) = true ∧
      Enabled conc008_tOne (fun p => if p < 2 then 1 else 0) ∧
      (refEnableCheck (N := Nat)).presence conc008_tOne (presenceOf conc008_all3) = false ∧
      (refEnableCheck (N := Nat)).check conc008_tOne conc008_all3 = false ∧
      ¬ OnlyOneInputs conc008_tFive ∧ ¬ OnlyOneInputs conc008_tMix ∧ OnlyOneInputs conc008_tOne ∧
      ¬ Builds conc008_tZero ∧ Enabled conc008_tZero (fun _ => 0) ∧
      (refEnableCheck (N := Nat)).presence conc008_tZero (presenceOf (fun _ => 0)) = false := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

/-! ## CONC-008, phase 3: the ν-match check -/

/-- The enablement check of an executor on transitions that may carry a match specification,
over queue markings of stamped tokens (local to CONC-008). `base` is the count-level check of
CONC-004 and CONC-008 (phases 1 and 2), applied to the transition without its match and to the
token counts of the marking; `nuMatch` is phase 3, the ν-match check, which reads the tokens;
`check` is the whole check. -/
structure NuEnableCheck (N V Nm : Type) where
  /-- Phases 1 and 2: the count-level check of CONC-004 and CONC-008. -/
  base : EnableCheck N
  /-- Phase 3: the ν-match check of a transition on a queue marking. -/
  nuMatch : NuTrans N (KeyFn V Nm) → QMarking N (Stamped V) → Bool
  /-- The whole enablement check of a transition on a queue marking. -/
  check : NuTrans N (KeyFn V Nm) → QMarking N (Stamped V) → Bool

section NuRef

variable {N V Nm : Type} [DecidableEq N] [LinearOrder Nm]

/-- The reference ν-match check: for a transition with a match specification, the selection of
NU-022 returns a name on the selection input read off the marking, as every runtime asks
(`find_match_binding(..).is_none()`, `MatchEngine.findBinding(..) == null`,
`findBinding(..) === null`); it passes trivially for a transition without one. -/
def refNuMatch (t : NuTrans N (KeyFn V Nm)) (M : QMarking N (Stamped V)) : Bool :=
  match t.mspec with
  | none => true
  | some ms => (refSelect (matchIn ms t M)).isSome

/-- The reference enablement check on ν transitions: the reference count-level check of the
transition without its match on the token counts, then the reference ν-match check. -/
def refNuEnableCheck : NuEnableCheck N V Nm where
  base := refEnableCheck
  nuMatch := refNuMatch
  check t M := refEnableCheck.check t.base (qCount M) && refNuMatch t M

end NuRef

#spec_witness refNuEnableCheck

requirement CONC_008_nu
  id "CONC-008"
  title "Multi-Phase Enablement (ν-match check)"
  kind F
  scope "all executors, transitions that build, with and without a match specification"
  source verbatim "spec/05-concurrency.md"
  quote "*When* a transition that builds has a match specification and phases 1 and 2 pass on the token counts of the marking, its ν-match check *shall* pass exactly when the match specification keys at least one place and there is a name of which every correlated input holds at least its required count of tokens of that name ([NU-020])."
        "*When* a transition that builds has a match specification, its enablement check *shall* pass exactly when phases 1 and 2 pass on the token counts of the marking and its ν-match check passes."
        "*When* a transition that builds has no match specification, its enablement check *shall* pass exactly when phases 1 and 2 pass on the token counts of the marking."
        "*When* a transition that builds has a match specification, its enablement check *shall* pass exactly when the transition without its match specification is enabled on the token counts of the marking ([CORE-022]), the match specification keys at least one place and there is a name of which every correlated input holds at least its required count of tokens of that name."
  reading "For every transition t that builds with or without its match (NuBuilds t) and every queue marking M of stamped tokens:"
          "if t has match specification ms and the count-level check of t without its match passes on the token counts of M, the ν-match check of t on M passes exactly when some name n is eligible on the selection input read off M (the match has a key, and every correlated input holds at least one token of n and at least its required count of them);"
          "if t has match specification ms, the whole check of t on M is the count-level check of t without its match on the token counts of M, and then the ν-match check of t on M;"
          "if t has no match specification, the whole check of t on M is the count-level check of t on the token counts of M;"
          "if t has match specification ms, the whole check of t on M passes exactly when t without its match is enabled on the token counts of M and some name is eligible on the selection input read off M."
  assumes "The model is a NuEnableCheck: base, the count-level check of CONC-004 and the first CONC-008 block (phases 1 and 2), applied to the transition without its match (t.base) and to the token counts of the marking (qCount); nuMatch, the ν-match check (phase 3), on a ν transition (glossary NuTrans) and a queue marking of stamped tokens; and check, the whole check. 'Phases 1 and 2 pass on the token counts of the marking' is base.check of the transition without its match (t.base) on the token counts (qCount M), which CONC-004 and CONC-008 constrain; for a transition with a match these are the phases of the transition without it, since a match specification adds no arc. This block does not constrain base, so its sentences mean this block and those two together: then the whole check of every transition that builds is the reference check (conc008_nu_pins_check), and it passes exactly when the transition is ν-enabled (conc008_nu_enabled, glossary NuEnabled). The three blocks hold together of one check (CONC_004_008_nu_consistent)."
          "The scan of phase 3 counts the required count, as every runtime computes it: Rust find_match_binding (rust/libpetri-runtime/src/bitmap_backend.rs:381-405, and the precompiled backend), Java MatchEngine.findBinding and requiredFor, and TypeScript findBinding and requiredFor (typescript/src/runtime/match-engine.ts:112-140) keep a name only when every correlated input holds at least the required count of its tokens, the count of an Exactly(n) or the minimum of an AtLeast(m) input, and 1 for One and All (glossary reqAt). The reading that asks only for a name with one token in every correlated input is killed (CONC_008_nu_forbids_sharedOnly). 'Tokens of that name' are the tokens of the correlated input whose key gives that name. The Lean name test (eligible) also asks for at least one token of the name in every correlated input; on a transition that builds this adds nothing, since every correlated input is an input place and every input arc requires at least one token (IO-002, IO-004), so the sentences leave it out (conc008_eligible_iff)."
          "Ruling D37 (a): a token whose key yields no name has no name on that input and is not counted (matchIn keeps only the tokens with a name). 'The match specification keys at least one place' is the first conjunct of eligible: a match without keys has no eligible name, so its ν-match check fails, as in the runtimes (rust/libpetri-runtime/src/match_engine.rs:33-34, select_match_name returns no name for no correlated inputs); a check that passes it is killed (CONC_008_nu_forbids_vacuous). The minimum of two keys is a check of the match builder only (ruling D37 (a), NU_020_build), not a build-time check of the transition: Rust MatchSpec::from_keys (rust/libpetri-core/src/match_spec.rs:82) leaves it to the caller and the transition build checks only a duplicate key (rust/libpetri-core/src/transition.rs:514), so a transition that builds (NuBuilds) may carry a match with fewer than two keys, and the sentences say 'keys at least one place'. Which name the firing then joins on is NU-020's and NU-022's subject, not this block's: the check asks only whether some name is eligible. The reference reads that off NU-022's selection, which returns a name exactly when one is eligible (refSelect_isSome_iff), as the runtimes do; the incremental matcher they read on the fast path (cache.best()) answers what the rebuild answers by NU-022's AC2."
          "'Phases 2 and 3 are only reached if Phase 1 passes' is not encoded as an order of evaluation, as in the first CONC-008 block: the second line is an equation of Boolean values. What it implies for the answer is encoded: the first line constrains the ν-match check only where phases 1 and 2 pass, which is where all three runtimes run it (bitmap_backend.rs:329-371, BitmapNetExecutor.java canEnable, bitmap-net-executor.ts canEnable, and the precompiled executors); where they fail, the ν-match check is not constrained and the whole check fails."
          "'This is the only per-token phase; there is no value-predicate phase (guards were removed, [IO-006])' is the type of base, which reads token counts only (EnableCheck on a count marking), together with the second and third lines: a transition without a match is decided by phases 1 and 2 on the token counts, and a transition with one by those phases and the ν-match check, with no further phase. A check that adds a guard on token values is killed (CONC_008_nu_forbids_guard)."
          "Which marking the phases read is not this ID's subject: a join whose correlated input took a deposit in the same firing pass is deferred to the next pass in every runtime (EXEC-003 AC4), which is RefExec's with the ν kernel. This block is the function of one marking. That an enabled matched transition fires is an offer, not a line: it is the conjunct NuCovers of the ν consistency theorem."
          "With CONC-004 and the first CONC-008 block in force, the fourth line follows from the first two (conc008_nu_enabled); it is kept because this block alone leaves base free and needs it: a check whose base stops after phase 1 meets the first three lines and is killed by the fourth (CONC_008_nu_forbids_maskBase)."
          "AC3 (a transition with a match specification requires phase 3 to scan tokens for a name of which every correlated input holds at least its required count of tokens of that name) is the first two lines: on a marking where both correlated inputs are marked but share no name, phases 1 and 2 pass, the ν-match check fails and so does the whole check (CONC_008_nu_nonvacuous); the check without phase 3 is killed (CONC_008_nu_mutant_noPhase3_killed). AC1 and AC2 are the first CONC-008 block's."
          "The test derivation's 'correct enablement' is the fourth line for a transition with a match and the first block's fourth line for one without; its 'minimal re-evaluation' is CONC-005's subject."
  signoff "2026-11-13 e74f39afa3b38f90 ai"
  statement : ∀ {N V Nm : Type} [DecidableEq N] [LinearOrder Nm], NuEnableCheck N V Nm → Prop :=
    fun C => ∀ t, NuBuilds t → ∀ M,
      (∀ ms, t.mspec = some ms → C.base.check t.base (qCount M) = true →
        (C.nuMatch t M = true ↔ ∃ n, eligible (matchIn ms t M) n = true)) ∧
      (∀ ms, t.mspec = some ms →
        C.check t M = (C.base.check t.base (qCount M) && C.nuMatch t M)) ∧
      (t.mspec = none → C.check t M = C.base.check t.base (qCount M)) ∧
      (∀ ms, t.mspec = some ms →
        (C.check t M = true ↔
          Enabled t.base (qCount M) ∧ ∃ n, eligible (matchIn ms t M) n = true))

/- The pinned readable form of CONC_008_nu: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CONC_008_nu : {N V Nm : Type} → [DecidableEq N] → [LinearOrder Nm] → NuEnableCheck N V Nm → Prop :=
fun {N V Nm} [DecidableEq N] [LinearOrder Nm] C =>
  ∀ (t : NuTrans N (KeyFn V Nm)),
    NuBuilds t →
      ∀ (M : QMarking N (Stamped V)),
        (∀ (ms : MatchSpec N (KeyFn V Nm)),
            t.mspec = some ms →
              C.base.check t.base (qCount M) = true →
                (C.nuMatch t M = true ↔ ∃ n, eligible (matchIn ms t M) n = true)) ∧
          (∀ (ms : MatchSpec N (KeyFn V Nm)),
              t.mspec = some ms → C.check t M = (C.base.check t.base (qCount M) && C.nuMatch t M)) ∧
            (t.mspec = none → C.check t M = C.base.check t.base (qCount M)) ∧
              ∀ (ms : MatchSpec N (KeyFn V Nm)),
                t.mspec = some ms →
                  (C.check t M = true ↔ Enabled t.base (qCount M) ∧ ∃ n, eligible (matchIn ms t M) n = true)
-/
#guard_msgs in #print CONC_008_nu

/-! ### The reference -/

section NuRefFacts

variable {N V Nm : Type} [DecidableEq N] [LinearOrder Nm]

/-- The selection of NU-022 returns a name exactly when some name is eligible. -/
theorem refSelect_isSome_iff (I : MatchIn Nm) :
    (refSelect I).isSome = true ↔ ∃ n, eligible I n = true := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 h
    exact ⟨n, ((refSelect_spec I).1 n hn).1⟩
  · exact (refSelect_spec I).2

/-- The reference ν-match check of a transition with a match passes exactly when some name is
eligible. -/
theorem refNuMatch_iff {t : NuTrans N (KeyFn V Nm)} {ms : MatchSpec N (KeyFn V Nm)}
    (hm : t.mspec = some ms) (M : QMarking N (Stamped V)) :
    refNuMatch t M = true ↔ ∃ n, eligible (matchIn ms t M) n = true := by
  simp only [refNuMatch, hm]
  exact refSelect_isSome_iff _

/-- The reference ν-match check passes on a transition without a match. -/
theorem refNuMatch_none {t : NuTrans N (KeyFn V Nm)} (hm : t.mspec = none)
    (M : QMarking N (Stamped V)) : refNuMatch t M = true := by
  simp [refNuMatch, hm]

/-- The reference check on ν transitions passes exactly when the transition is ν-enabled
(glossary NuEnabled), for every transition whose base builds. -/
theorem refNuEnableCheck_enabled {t : NuTrans N (KeyFn V Nm)} (hb : Builds t.base)
    (M : QMarking N (Stamped V)) :
    (refNuEnableCheck (N := N) (V := V) (Nm := Nm)).check t M = true ↔ NuEnabled t M := by
  simp only [refNuEnableCheck, Bool.and_eq_true, refEnableCheck_enabled hb.pos, NuEnabled]
  cases hm : t.mspec with
  | none => simp [refNuMatch_none hm]
  | some ms =>
    rw [refNuMatch_iff hm]
    simp

end NuRefFacts

/-- ✓ The reference check satisfies the ν-match lines: its ν-match check asks NU-022's
selection for a name, which it returns exactly when some name is eligible
(`refSelect_isSome_iff`); its whole check is the reference count-level check of the transition
without its match, then the ν-match check, which passes trivially without a match; and the count
check decides enablement on the token counts (`refEnableCheck_enabled`). -/
@[evidence holds CONC_008_nu]
theorem CONC_008_nu_reference {N V Nm : Type} [DecidableEq N] [LinearOrder Nm] :
    CONC_008_nu (refNuEnableCheck (N := N) (V := V) (Nm := Nm)) := by
  intro t hb M
  refine ⟨fun ms hm _ => refNuMatch_iff hm M, fun ms hm => rfl, fun hm => ?_, fun ms hm => ?_⟩
  · show (refEnableCheck.check t.base (qCount M) && refNuMatch t M) = _
    rw [refNuMatch_none hm, Bool.and_true]
    rfl
  · show (refEnableCheck.check t.base (qCount M) && refNuMatch t M) = true ↔ _
    rw [Bool.and_eq_true, refEnableCheck_enabled hb.1.pos, refNuMatch_iff hm]

/-- ✓ CONC-004, the count-level CONC-008 block and the ν-match block hold together of one check:
the reference check satisfies all three. -/
@[evidence consistent CONC_004 CONC_008 CONC_008_nu]
theorem CONC_004_008_nu_consistent {N V Nm : Type} [DecidableEq N] [LinearOrder Nm] :
    ∃ C : NuEnableCheck N V Nm, CONC_004 C.base ∧ CONC_008 C.base ∧ CONC_008_nu C :=
  ⟨refNuEnableCheck, CONC_004_reference, CONC_008_reference, CONC_008_nu_reference⟩

/-- CONC-004 and the two CONC-008 blocks together fix the whole check of every ν transition that
builds: a check that satisfies all three answers what the reference check answers, at every
queue marking. -/
theorem conc008_nu_pins_check {N V Nm : Type} [DecidableEq N] [LinearOrder Nm]
    (C : NuEnableCheck N V Nm) (h4 : CONC_004 C.base) (h8 : CONC_008 C.base)
    (hnu : CONC_008_nu C) (t : NuTrans N (KeyFn V Nm)) (hb : NuBuilds t)
    (M : QMarking N (Stamped V)) : C.check t M = refNuEnableCheck.check t M := by
  have hbase := conc004_008_pins_check C.base h4 h8 t.base hb.1 (qCount M)
  show C.check t M = (refEnableCheck.check t.base (qCount M) && refNuMatch t M)
  cases hm : t.mspec with
  | none => rw [(hnu t hb M).2.2.1 hm, hbase, refNuMatch_none hm, Bool.and_true]
  | some ms =>
    rw [(hnu t hb M).2.1 ms hm, hbase]
    cases hr : refEnableCheck.check t.base (qCount M)
    · rfl
    · simp only [Bool.true_and]
      rw [Bool.eq_iff_iff, (hnu t hb M).1 ms hm (hbase.trans hr), refNuMatch_iff hm]

/-- With the count-level CONC-008 block on its base, a check that meets the ν-match lines passes
exactly when the transition is ν-enabled (glossary NuEnabled): enabled on its token counts and,
with a match, some name eligible. This is the enablement NU-020 asks of every matched firing. -/
@[evidence cites "NU-020" "enablement of a matched transition: the usual cardinality, bitmap and inhibitor checks, and a name present in every correlated input with at least that input's required count"]
theorem conc008_nu_enabled {N V Nm : Type} [DecidableEq N] [LinearOrder Nm]
    (C : NuEnableCheck N V Nm) (h8 : CONC_008 C.base) (hnu : CONC_008_nu C)
    (t : NuTrans N (KeyFn V Nm)) (hb : NuBuilds t) (M : QMarking N (Stamped V)) :
    C.check t M = true ↔ NuEnabled t M := by
  have hen := (h8 t.base hb.1 (qCount M)).2.2.2
  cases hm : t.mspec with
  | none =>
    rw [(hnu t hb M).2.2.1 hm, hen]
    simp [NuEnabled, hm]
  | some ms =>
    rw [(hnu t hb M).2.2.2 ms hm]
    simp [NuEnabled, hm]

/-- On a transition that builds, a name is eligible exactly when the match keys at least one place
and every correlated input holds at least its required count of tokens of the name: the
'at least one token' of `eligible` follows, because every correlated input is an input place and
every input arc requires at least one token ([IO-002], [IO-004]). -/
theorem conc008_eligible_iff {N V Nm : Type} [DecidableEq N] [DecidableEq Nm]
    {t : NuTrans N (KeyFn V Nm)} {ms : MatchSpec N (KeyFn V Nm)} (hb : NuBuilds t)
    (hm : t.mspec = some ms) (M : QMarking N (Stamped V)) (n : Nm) :
    eligible (matchIn ms t M) n = true ↔
      ms.keys ≠ [] ∧ ∀ k ∈ (matchIn ms t M).keys, k.2 ≤ (stamps k.1 n).length := by
  have hreq : ∀ k ∈ (matchIn ms t M).keys, 1 ≤ k.2 := by
    intro k hk
    simp only [matchIn, List.mem_map] at hk
    obtain ⟨k', hk', rfl⟩ := hk
    have hin : k'.1 ∈ inPlaces t.base :=
      (hb.2 ms hm).2.1 k'.1 (List.mem_map_of_mem (f := Prod.fst) hk')
    show 1 ≤ reqAt t.base k'.1
    unfold reqAt
    cases h : nspecAt t.base.core k'.1 with
    | none => exact le_refl 1
    | some s => exact hb.1.1.2.1 s (List.mem_of_find?_eq_some h)
  have hne : (matchIn ms t M).keys.isEmpty = false ↔ ms.keys ≠ [] := by
    simp [matchIn]
  unfold eligible
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, decide_eq_true_eq, hne]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun k hk => (h2 k hk).2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun k hk => ⟨le_trans (hreq k hk) (h2 k hk), h2 k hk⟩⟩

/-! ### Examples over values and names in `Nat` -/

/-- A token with value (and name) `v`, created at `s`. -/
def conc008_tok (v : Nat) (s : Int) : Stamped Nat := ⟨v, s⟩

/-- The key of the examples: a token's name is its value. -/
def conc008_key : KeyFn Nat Nat := some

/-- A match that keys places `0` and `1`. -/
def conc008_ms : MatchSpec Nat (KeyFn Nat Nat) := { keys := [(0, conc008_key), (1, conc008_key)] }

/-- A join of places `0` and `1` with the given cards, correlated by `conc008_ms`. -/
def conc008_join (c0 c1 : Card) : NuTrans Nat (KeyFn Nat Nat) :=
  { base := { core := { name := "join", inputs := [⟨0, c0⟩, ⟨1, c1⟩], inhibitors := [],
                        reads := [], resets := [] }, out := none }
    mspec := some conc008_ms }

/-- A join of places `0` and `1` (`One` each) with a further input `Exactly(5)` on place `2`,
which the match does not key. -/
def conc008_joinFive : NuTrans Nat (KeyFn Nat Nat) :=
  { base := { core := { name := "join5", inputs := [⟨0, .one⟩, ⟨1, .one⟩, ⟨2, .exactly 5⟩],
                        inhibitors := [], reads := [], resets := [] }, out := none }
    mspec := some conc008_ms }

/-- A transition without a match: one `One` input on place `0`. -/
def conc008_plain : NuTrans Nat (KeyFn Nat Nat) :=
  { base := { core := { name := "plain", inputs := [⟨0, .one⟩], inhibitors := [], reads := [],
                        resets := [] }, out := none } }

/-- Both branches hold the name `1` (X): place `0` holds X@0, place `1` holds X@1. -/
def conc008_both : QMarking Nat (Stamped Nat) := fun p =>
  if p = 0 then [conc008_tok 1 0] else if p = 1 then [conc008_tok 1 1] else []

/-- Both branches are marked but share no name: place `0` holds X@0, place `1` holds Y@0
(X = 1, Y = 2). -/
def conc008_apart : QMarking Nat (Stamped Nat) := fun p =>
  if p = 0 then [conc008_tok 1 0] else if p = 1 then [conc008_tok 2 0] else []

/-- Place `0` holds X@0 and Y@1, place `1` holds X@2: X is in both, but only once in place `0`. -/
def conc008_once : QMarking Nat (Stamped Nat) := fun p =>
  if p = 0 then [conc008_tok 1 0, conc008_tok 2 1] else if p = 1 then [conc008_tok 1 2] else []

/-- `conc008_both` with three tokens on place `2`. -/
def conc008_three : QMarking Nat (Stamped Nat) := fun p =>
  if p = 2 then [conc008_tok 7 0, conc008_tok 7 1, conc008_tok 7 2] else conc008_both p

/-- Place `0` holds one token whose value is `0`. -/
def conc008_zero : QMarking Nat (Stamped Nat) := fun p => if p = 0 then [conc008_tok 0 0] else []

/-! ### Mutant: the check without phase 3 -/

/-- A check that never runs phase 3: the whole check of every transition is the count-level check
on the token counts, with or without a match. -/
def conc008_noPhase3 {N V Nm : Type} [DecidableEq N] [LinearOrder Nm] : NuEnableCheck N V Nm :=
  { refNuEnableCheck with check := fun t M => refEnableCheck.check t.base (qCount M) }

/-- Mutant reading of the ν-match lines in which the count-level CONC-008 block is the whole
check of every transition, a match specification adding no phase. -/
def CONC_008_nu_mutant_noPhase3 {N V Nm : Type} [DecidableEq N] [LinearOrder Nm]
    (C : NuEnableCheck N V Nm) : Prop :=
  ∀ t, NuBuilds t → ∀ M, C.check t M = C.base.check t.base (qCount M)

/-- The check without phase 3 kills the mutant: it satisfies the mutant reading, but not the
ν-match lines (AC3). The join of places `0` and `1` on a marking where place `0` holds X and
place `1` holds Y passes phases 1 and 2, so it passes this check, but the two places share no
name, so the ν-match check fails and the whole check must fail (second line). -/
@[evidence mutant CONC_008_nu]
theorem CONC_008_nu_mutant_noPhase3_killed :
    CONC_008_nu_mutant_noPhase3 (conc008_noPhase3 (N := Nat) (V := Nat) (Nm := Nat)) ∧
      ¬ CONC_008_nu (conc008_noPhase3 (N := Nat) (V := Nat) (Nm := Nat)) := by
  refine ⟨fun _ _ _ => rfl, fun h => ?_⟩
  have := (h (conc008_join .one .one) (by decide) conc008_apart).2.1 conc008_ms rfl
  revert this
  decide

/-! ### Violation: a name shared by all correlated inputs, without the required count -/

/-- A ν-match check that asks only for a name with one token in every correlated input,
ignoring the required counts. -/
def conc008_sharedName (t : NuTrans Nat (KeyFn Nat Nat)) (M : QMarking Nat (Stamped Nat)) : Bool :=
  match t.mspec with
  | none => true
  | some ms =>
    let I := matchIn ms t M
    ((I.keys.head?.map Prod.fst).getD []).any fun x =>
      I.keys.all fun k => decide (1 ≤ (stamps k.1 x.1).length)

/-- The reference check with the ν-match check `conc008_sharedName`. -/
def conc008_sharedOnly : NuEnableCheck Nat Nat Nat where
  base := refEnableCheck
  nuMatch := conc008_sharedName
  check t M := refEnableCheck.check t.base (qCount M) && conc008_sharedName t M

/-- ✗ A ν-match check that reads 'a name shared by all of them' without the required counts
violates the first line. Take a join whose input on place `0` is `Exactly(2)`, with X and Y in
place `0` and X in place `1`: phases 1 and 2 pass (two tokens and one), X is in both places, but
place `0` holds only one X, so no name is eligible and the ν-match check must fail. -/
@[evidence forbids CONC_008_nu]
theorem CONC_008_nu_forbids_sharedOnly : ¬ CONC_008_nu conc008_sharedOnly := fun h => by
  have hx := ((h (conc008_join (.exactly 2) .one) (by decide) conc008_once).1 conc008_ms rfl
    (by decide)).1 (by decide)
  have hnone : refSelect (matchIn conc008_ms (conc008_join (.exactly 2) .one) conc008_once) =
      none := by decide
  have := (refSelect_isSome_iff _).2 hx
  rw [hnone] at this
  exact absurd this (by decide)

/-! ### Violation: a value-predicate phase -/

/-- A check that adds a guard on token values for a transition without a match: the token at the
head of place `0` must not have value `0`. -/
def conc008_guard : NuEnableCheck Nat Nat Nat :=
  { refNuEnableCheck with
    check := fun t M => refNuEnableCheck.check t M &&
      (t.mspec.isSome || (M 0).all fun x => x.val != 0) }

/-- ✗ A guard on token values violates the third line: the plain transition with one `One` input
on place `0` passes phases 1 and 2 when place `0` holds one token, but the guard rejects it
because the token's value is `0`; without a match, phases 1 and 2 decide the check. -/
@[evidence forbids CONC_008_nu]
theorem CONC_008_nu_forbids_guard : ¬ CONC_008_nu conc008_guard := fun h => by
  have := (h conc008_plain (by decide) conc008_zero).2.2.1 rfl
  revert this
  decide

/-! ### Violation: a base that stops after phase 1 -/

/-- A check whose base is the count-level check that stops after phase 1 (`conc008_maskOnly`),
followed by the reference ν-match check. -/
def conc008_maskBase : NuEnableCheck Nat Nat Nat where
  base := conc008_maskOnly
  nuMatch := refNuMatch
  check t M := conc008_maskOnly.check t.base (qCount M) && refNuMatch t M

/-- ✗ A base that stops after phase 1 violates the fourth line: the join of places `0` and `1`
with a further `Exactly(5)` input on place `2` passes this check when X is in both branches and
place `2` holds three tokens, although it is not enabled on its counts. It meets the first three
lines, which speak of whatever base the check has; the count-level CONC-008 block also forbids
that base (`CONC_008_mutant_maskOnly_killed`). -/
@[evidence forbids CONC_008_nu]
theorem CONC_008_nu_forbids_maskBase : ¬ CONC_008_nu conc008_maskBase := fun h => by
  have := ((h conc008_joinFive (by decide) conc008_three).2.2.2 conc008_ms rfl).1 (by decide)
  exact absurd this.1 (by decide)

/-! ### Violation: a match without keys passes -/

/-- A match that keys no place. -/
def conc008_msNone : MatchSpec Nat (KeyFn Nat Nat) := { keys := [] }

/-- A transition with one `One` input on place `0` and a match that keys no place. It builds:
the transition build checks a duplicate key and keys on non-input places, not the minimum of
two keys, which is the match builder's ([NU-020]). -/
def conc008_noKeys : NuTrans Nat (KeyFn Nat Nat) :=
  { base := { core := { name := "nokeys", inputs := [⟨0, .one⟩], inhibitors := [], reads := [],
                        resets := [] }, out := none }
    mspec := some conc008_msNone }

/-- A ν-match check that passes every match without keys, and otherwise asks the reference. -/
def conc008_emptyPass (t : NuTrans Nat (KeyFn Nat Nat)) (M : QMarking Nat (Stamped Nat)) : Bool :=
  match t.mspec with
  | none => true
  | some ms => ms.keys.isEmpty || refNuMatch t M

/-- The reference check with the ν-match check `conc008_emptyPass`. -/
def conc008_vacuous : NuEnableCheck Nat Nat Nat where
  base := refEnableCheck
  nuMatch := conc008_emptyPass
  check t M := refEnableCheck.check t.base (qCount M) && conc008_emptyPass t M

/-- ✗ A ν-match check that passes a match without keys violates the first line. Take a
transition with one input on place `0` and a match that keys no place, with one token in place
`0`: phases 1 and 2 pass and this check passes too, because 'every correlated input holds enough
tokens of the name' is true when there is no correlated input. But the match keys no place, so no
name is eligible and the ν-match check must fail. -/
@[evidence forbids CONC_008_nu]
theorem CONC_008_nu_forbids_vacuous : ¬ CONC_008_nu conc008_vacuous := fun h => by
  obtain ⟨n, hn⟩ := ((h conc008_noKeys (by decide) conc008_zero).1 conc008_msNone rfl
    (by decide)).1 (by decide)
  revert hn
  simp [eligible, matchIn, conc008_msNone]

/-! ### Every line exercised -/

/-- ✓ Worked example (AC3). Take a join of places `0` and `1`, and names X and Y. With X in both
places, phases 1 and 2 pass, the ν-match check passes and the whole check passes. With X in place
`0` and Y in place `1`, phases 1 and 2 still pass, but no name is in both, so the ν-match check
fails and so does the whole check. With an `Exactly(2)` input on place `0` holding X and Y, and X
in place `1`, X is in both places but not twice in place `0`, so the ν-match check fails. A join
with a further `Exactly(5)` input holding three tokens passes the ν-match check but not phase 2.
A transition without a match is decided by phases 1 and 2 alone. -/
@[evidence nonvacuous CONC_008_nu]
theorem CONC_008_nu_nonvacuous :
    NuBuilds (conc008_join .one .one) ∧ NuBuilds (conc008_join (.exactly 2) .one) ∧
      NuBuilds conc008_joinFive ∧ NuBuilds conc008_plain ∧
      (refNuEnableCheck (N := Nat) (V := Nat) (Nm := Nat)).base.check
        (conc008_join .one .one).base (qCount conc008_both) = true ∧
      (refNuEnableCheck (N := Nat) (V := Nat) (Nm := Nat)).nuMatch
        (conc008_join .one .one) conc008_both = true ∧
      (refNuEnableCheck (N := Nat) (V := Nat) (Nm := Nat)).check
        (conc008_join .one .one) conc008_both = true ∧
      eligible (matchIn conc008_ms (conc008_join .one .one) conc008_both) 1 = true ∧
      (refNuEnableCheck (N := Nat) (V := Nat) (Nm := Nat)).base.check
        (conc008_join .one .one).base (qCount conc008_apart) = true ∧
      (refNuEnableCheck (N := Nat) (V := Nat) (Nm := Nat)).nuMatch
        (conc008_join .one .one) conc008_apart = false ∧
      (refNuEnableCheck (N := Nat) (V := Nat) (Nm := Nat)).check
        (conc008_join .one .one) conc008_apart = false ∧
      (refNuEnableCheck (N := Nat) (V := Nat) (Nm := Nat)).base.check
        (conc008_join (.exactly 2) .one).base (qCount conc008_once) = true ∧
      (refNuEnableCheck (N := Nat) (V := Nat) (Nm := Nat)).nuMatch
        (conc008_join (.exactly 2) .one) conc008_once = false ∧
      (refNuEnableCheck (N := Nat) (V := Nat) (Nm := Nat)).nuMatch
        conc008_joinFive conc008_three = true ∧
      (refNuEnableCheck (N := Nat) (V := Nat) (Nm := Nat)).base.check
        conc008_joinFive.base (qCount conc008_three) = false ∧
      (refNuEnableCheck (N := Nat) (V := Nat) (Nm := Nat)).check
        conc008_joinFive conc008_three = false ∧
      (refNuEnableCheck (N := Nat) (V := Nat) (Nm := Nat)).check conc008_plain conc008_zero =
        true ∧
      (refNuEnableCheck (N := Nat) (V := Nat) (Nm := Nat)).check conc008_plain (fun _ => []) =
        false := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

end Libpetri.Spec
