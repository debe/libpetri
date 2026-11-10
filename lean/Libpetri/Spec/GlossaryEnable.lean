import Libpetri.Spec.Glossary

set_option linter.missingDocs true

/-!
# Glossary: the enablement check

The terms the enablement-check requirements use ([CONC-004], [CONC-008], and the sparse masks of
[PERF-042]), as Lean definitions at the count level of `Glossary.lean`. Each docstring quotes
its entry in section "Enablement check" of `spec/glossary.md`.

A bitmap is read here as one bit per place, `N → Bool`, and a mask as the set of places whose bit
is set. Word layout, place indices and the cost of the check are below this level: they are the
business of [CONC-004]'s complexity criteria and of [PERF-042]'s word layer.

An enablement-check requirement is a predicate over an abstract check `C : EnableCheck N`, so that
it can be checked against a reference check and against a mutant. This module defines the
interface only; the reference check is defined beside the requirement blocks that state it.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

variable {N : Type}

/-! ## Masks and bitmaps -/

/-- **Glossary: Needs-mask.** "The bitmap of a transition with a bit set for each of its input
places and read places: all of them must be marked [CONC-004]." -/
def NeedsMask (t : Trans N) (p : N) : Prop := p ∈ inPlaces t ∨ ReadArc t p

/-- **Glossary: Inhibitor-mask.** "The bitmap of a transition with a bit set for each of its
inhibitor places: none of them may be marked [CONC-004]." -/
abbrev InhibitorMask (t : Trans N) (p : N) : Prop := InhibitorArc t p

/-- **Glossary: Presence bitmap.** "The bitmap of a marking with one bit per place, set exactly
when the place is marked [CONC-004]." -/
def presenceOf (m : CountMarking N) : N → Bool := fun p => decide (Marked m p)

/-! ## The phases of the check -/

/-- **Glossary: Presence check.** "Phase 1 of the enablement check. It passes on a bitmap when
every bit of the transition's needs-mask is set and no bit of its inhibitor-mask is set:
`(marking & needs-mask) == needs-mask AND (marking & inhibitor-mask) == 0` [CONC-004],
[CONC-008]. Reset arcs and output arcs play no part."

`MaskCheck t bits`: the presence check of `t` passes on the bitmap `bits`. -/
def MaskCheck (t : Trans N) (bits : N → Bool) : Prop :=
  (∀ p, NeedsMask t p → bits p = true) ∧ (∀ p, InhibitorMask t p → bits p = false)

/-- **Glossary: Cardinality check.** "Phase 2 of the enablement check. It passes when every input
place holds at least its required count [CONC-008], [IO-007]."

`CardinalityOk t m`: the cardinality check of `t` passes on the marking `m`. -/
def CardinalityOk (t : Trans N) (m : CountMarking N) : Prop :=
  ∀ s ∈ t.core.inputs, requiredCount s.card ≤ m s.place

/-- **Glossary: Enablement check.** "The check an executor runs to decide whether a transition is
enabled: the presence check on the presence bitmap of the marking, then the cardinality check,
then, for a transition with a match specification, the ν-match check [CONC-008], [NU-020]."

The interface of a check for transitions without a match specification: its presence phase on a
bitmap, its cardinality phase on token counts, and the whole check on a marking. The ν-match
phase is not part of it. -/
structure EnableCheck (N : Type) where
  /-- Phase 1, the presence check, on a bitmap. -/
  presence : Trans N → (N → Bool) → Bool
  /-- Phase 2, the cardinality check, on token counts. -/
  cardinality : Trans N → CountMarking N → Bool
  /-- The whole check, on a marking. -/
  check : Trans N → CountMarking N → Bool

/-! ## Bridge lemmas -/

/-- A bit of the presence bitmap is set exactly when the place is marked. -/
theorem presenceOf_iff (m : CountMarking N) (p : N) : presenceOf m p = true ↔ Marked m p := by
  simp [presenceOf]

/-- The presence check on the presence bitmap of a marking, read on the marking: every input and
read place is marked and no inhibitor place is. -/
theorem maskCheck_presenceOf (t : Trans N) (m : CountMarking N) :
    MaskCheck t (presenceOf m) ↔
      (∀ s ∈ t.core.inputs, Marked m s.place) ∧ (∀ p ∈ t.core.reads, Marked m p) ∧
        (∀ p ∈ t.core.inhibitors, ¬ Marked m p) := by
  simp only [MaskCheck, NeedsMask, presenceOf, decide_eq_true_eq, decide_eq_false_iff_not,
    inPlaces, List.mem_map]
  constructor
  · rintro ⟨hn, hh⟩
    exact ⟨fun s hs => hn _ (.inl ⟨s, hs, rfl⟩), fun p hp => hn p (.inr hp), hh⟩
  · rintro ⟨hi, hr, hh⟩
    refine ⟨fun p hp => ?_, hh⟩
    rcases hp with ⟨s, hs, rfl⟩ | hp
    · exact hi s hs
    · exact hr p hp

end Libpetri.Spec
