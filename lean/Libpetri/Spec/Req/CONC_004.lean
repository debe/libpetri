import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryEnable

set_option linter.missingDocs true

/-!
# CONC-004: Bitmap-based enablement check (`spec/05-concurrency.md`)

CONC-004 is a pure function of a transition and a bitmap: the presence check (glossary, section
"Enablement check") passes exactly when every bit of the transition's needs-mask is set and no
bit of its inhibitor-mask is set. The requirement is a predicate over an abstract check
`C : EnableCheck N` (glossary `GlossaryEnable.lean`), of which it constrains the presence phase
only. The evidence theorems check it against the reference check `refEnableCheck`, defined here
and shared with CONC-008, against a needs-mask without the read places, a needs-mask that also
holds the reset places, and an inhibitor test that blocks only when every inhibitor place is
marked.

The cost of the check (O(W), a few word operations, no iteration over arcs) is a quality
property, PERF-002's and PERF-042's subject; this block states what the check returns.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## The reference check -/

/-- The reference enablement check (CONC-004, CONC-008), for transitions without a match
specification. Phase 1, the presence check, reads the bitmap only: every input place and every
read place has its bit set, and no inhibitor place has. Phase 2, the cardinality check, reads the
token counts: every input place holds at least its required count. The whole check is phase 1 on
the presence bitmap of the marking, and then phase 2. -/
def refEnableCheck {N : Type} : EnableCheck N where
  presence t bits :=
    (inPlaces t).all bits && t.core.reads.all bits && t.core.inhibitors.all (!bits ·)
  cardinality t m := t.core.inputs.all fun s => decide (requiredCount s.card ≤ m s.place)
  check t m :=
    ((inPlaces t).all (presenceOf m) && t.core.reads.all (presenceOf m) &&
        t.core.inhibitors.all (!presenceOf m ·)) &&
      t.core.inputs.all fun s => decide (requiredCount s.card ≤ m s.place)

#spec_witness refEnableCheck

/-! ## CONC-004: Bitmap-based enablement check -/

requirement CONC_004
  id "CONC-004"
  title "Bitmap-Based Enablement Check"
  kind F
  scope "all executors (the mask test of the bitmap executor; the precompiled executor's sparse form is PERF-042)"
  source verbatim "spec/05-concurrency.md"
  quote "The presence check of a transition *shall* pass on a bitmap exactly when every bit of its needs-mask is set in the bitmap and no bit of its inhibitor-mask is set."
  reading "For every transition t and every bitmap (one bit per place), the presence check of t passes exactly when every input place and every read place of t has its bit set and no inhibitor place of t has its bit set."
  assumes "A bitmap is read as one bit per place (N → Bool) and a mask as the set of places whose bit is set; the needs-mask is the input places and the read places, the inhibitor-mask the inhibitor places (glossary: Needs-mask, Inhibitor-mask, Presence check). Place numbering, word layout and when the masks are computed are CONC-007's and PERF-042's subject. The presence check is a function of the transition and the bitmap only (the type of EnableCheck.presence): it reads no token count, which is what 'bitmap-based' adds to the glossary's Enabled."
          "The line ranges over every bitmap, not only the presence bitmap of a marking, and says nothing about what a bit means. The parentheses '(all must have tokens)' and '(none may have tokens)' and the operand 'marking' of the formula, which tie a bit to a marked place, are carried by CONC-008, whose lines apply the presence check to the presence bitmap of the marking (glossary: Presence bitmap). Which bitmap the executor passes (the live presence bitmap, or the snapshot of a firing pass, EXEC-003) is not this ID's subject."
          "This line constrains the presence phase of the check, not the decision the executor makes with it: read alone, it accepts a check whose presence phase is the formula but whose whole check runs a second needs-mask without the read places (a sparse mask out of step with the full-width one). CONC-008 ties the whole check to the presence phase and kills that check (CONC_008_forbids_driftedMask); the two blocks together fix the whole check of every transition that builds (conc004_008_pins_check)."
          "Reset arcs and output arcs set no bit of either mask: a reset arc never gates its transition (CORE-034, second line). The mutant that puts the reset places in the needs-mask is killed (CONC_004_forbids_withResets)."
          "The inhibitor test fails when any inhibitor place has its bit set, not only when all of them have (`(marking & inhibitor-mask) == 0`); the reading that blocks only when every inhibitor place is marked is killed (CONC_004_forbids_inhAll)."
          "The body calls the mask test the 'Enablement check'; CONC-008 makes it phase 1 of the enablement check, followed by the cardinality check and the ν-match check (clash conc-a#10). This block reads the formula as the presence check, the glossary's name for phase 1, and the inserted sentence says so; no existing sentence is reworded. The reading in which the mask test is the whole enablement check is CONC-008's mutant CONC_008_mutant_maskOnly, killed there by AC2."
          "'The primary executor' is read as every executor (scope): the bitmap executor's mask test is this line, and the precompiled executor's sparse mask test answers what the full-width test answers (PERF-042)."
          "'uses precomputed bitmasks' and 'Each transition has precomputed masks' say how and when the masks are held, not what the check returns, and are not encoded: the line fixes the content of the masks as a function of the transition, and when they are computed is CONC-007's and PERF-042's subject. The reference check refEnableCheck walks the arc lists; it is a witness of what the check returns, not of how it is computed."
          "Kind F: the formula line is the one functional sentence of the body; the acceptance criteria and the test derivation are all cost criteria, listed below as not encoded."
          "The body sentence on the cost ('O(1) enablement checking per transition (proportional to the number of machine words needed to represent all places)') is a quality property and is not encoded: the parenthesis reads 'O(1)' as O(W), constant for a fixed place count (clash conc-a#4, D20). It is PERF-002's subject; CONC_004_reference cites PERF-002 for what the O(W) check returns."
          "AC1 (enablement checked by bitwise operations, not by iterating over arcs) is a quality property of how the check is computed and is not encoded; what the bitwise check returns is the line. The word check of PERF-042 is the bitwise form, and that block proves it answers what the full-width check answers."
          "AC2 (a transition with 3 inputs and 2 reads needs only 1-2 bitwise operations) is a quality property and is not encoded; the operation count holds for one word (W = 1, clash conc-a#4). The answer of the check for such a transition is the line at CONC_004_nonvacuous, whose transition has 3 input places, 2 read places and 1 inhibitor place."
          "AC3 (the check is O(W), W = ceil(numPlaces / word_size)) is a quality property, PERF-002's subject, and is not encoded."
          "The test derivation (constant check time per transition on a 100-place net) is a performance test, PERF-002's, and is not encoded."
  signoff "pending"
  statement : ∀ {N : Type}, EnableCheck N → Prop :=
    fun C => ∀ t bits, C.presence t bits = true ↔ MaskCheck t bits

/- The pinned readable form of CONC-004: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CONC_004 : {N : Type} → EnableCheck N → Prop :=
fun {N} C => ∀ (t : Reference.Trans N) (bits : N → Bool), C.presence t bits = true ↔ MaskCheck t bits
-/
#guard_msgs in #print CONC_004

/-! ### The reference -/

/-- The presence phase of the reference check is the glossary's presence check. -/
theorem refEnableCheck_presence {N : Type} (t : Trans N) (bits : N → Bool) :
    (refEnableCheck (N := N)).presence t bits = true ↔ MaskCheck t bits := by
  simp only [refEnableCheck, MaskCheck, NeedsMask, Bool.and_eq_true, List.all_eq_true,
    Bool.not_eq_true']
  constructor
  · rintro ⟨⟨hi, hr⟩, hh⟩
    exact ⟨fun p hp => hp.elim (hi p) (hr p), hh⟩
  · rintro ⟨hn, hh⟩
    exact ⟨⟨fun p hp => hn p (.inl hp), fun p hp => hn p (.inr hp)⟩, hh⟩

/-- ✓ The reference check satisfies CONC-004: its presence phase tests every input and read
bit and every inhibitor bit, and nothing else (`refEnableCheck_presence`). -/
@[evidence holds CONC_004, evidence cites "PERF-002" "what the O(W) enablement check returns: the presence check of a transition passes on a bitmap exactly when every needs-mask bit is set and no inhibitor-mask bit is set"]
theorem CONC_004_reference {N : Type} : CONC_004 (refEnableCheck (N := N)) :=
  refEnableCheck_presence

/-! ### Examples -/

/-- The AC2 transition of the examples: `One` inputs on `0`, `1`, `2`, read arcs on `3` and
`4`, an inhibitor arc on `5` and a reset arc on `6`. -/
def conc004_t : Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .one⟩, ⟨1, .one⟩, ⟨2, .one⟩], inhibitors := [5],
              reads := [3, 4], resets := [6] },
    out := none }

/-- The bitmap of the examples with bits `0` to `4` set and every other bit clear. -/
def conc004_bits : Nat → Bool := fun p => decide (p < 5)

/-- A transition with one read arc, on `0`, and no other arc. -/
def conc004_tRead : Trans Nat :=
  { core := { name := "r", inputs := [], inhibitors := [], reads := [0], resets := [] },
    out := none }

/-- A transition with one reset arc, on `0`, and no other arc. -/
def conc004_tReset : Trans Nat :=
  { core := { name := "z", inputs := [], inhibitors := [], reads := [], resets := [0] },
    out := none }

/-- A transition with inhibitor arcs on `0` and `1` and no other arc. -/
def conc004_tInh2 : Trans Nat :=
  { core := { name := "i", inputs := [], inhibitors := [0, 1], reads := [], resets := [] },
    out := none }

/-! ### Mutant: a needs-mask without the read places -/

/-- A check whose needs-mask holds the input places only. -/
def conc004_noReads {N : Type} : EnableCheck N :=
  { refEnableCheck with
    presence := fun t bits => (inPlaces t).all bits && t.core.inhibitors.all (!bits ·) }

/-- Mutant reading of CONC-004 in which the needs-mask holds the input places only: a read
place gates nothing. -/
def CONC_004_mutant_noReads {N : Type} (C : EnableCheck N) : Prop :=
  ∀ t bits, C.presence t bits = true ↔
    (∀ p ∈ inPlaces t, bits p = true) ∧ (∀ p, InhibitorMask t p → bits p = false)

/-- The check without the read places kills the mutant: it satisfies the mutant reading, but
not CONC-004. `conc004_tRead` passes it on the empty bitmap, although its read place `0` has no
bit set. -/
@[evidence mutant CONC_004]
theorem CONC_004_mutant_noReads_killed :
    CONC_004_mutant_noReads (conc004_noReads (N := Nat)) ∧ ¬ CONC_004 (conc004_noReads (N := Nat)) := by
  refine ⟨fun t bits => ?_, fun h => ?_⟩
  · simp only [conc004_noReads, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
      InhibitorMask, InhibitorArc]
  · have := (h conc004_tRead (fun _ => false)).1 (by decide)
    exact absurd (this.1 0 (.inr (by simp [ReadArc, conc004_tRead]))) (by decide)

/-! ### Violation: a needs-mask that also holds the reset places -/

/-- A check whose needs-mask also holds the reset places. -/
def conc004_withResets {N : Type} : EnableCheck N :=
  { refEnableCheck with
    presence := fun t bits => refEnableCheck.presence t bits && t.core.resets.all bits }

/-- ✗ A needs-mask with the reset places violates CONC-004: `conc004_tReset` fails it on the
empty bitmap, although it has no input, read or inhibitor place (a reset never gates,
CORE-034). -/
@[evidence forbids CONC_004]
theorem CONC_004_forbids_withResets : ¬ CONC_004 (conc004_withResets (N := Nat)) := fun h => by
  have := (h conc004_tReset (fun _ => false)).2
    ⟨fun p hp => by simp [NeedsMask, inPlaces, ReadArc, conc004_tReset] at hp, fun _ _ => rfl⟩
  revert this
  decide

/-! ### Violation: an inhibitor test that blocks only when every inhibitor place is marked -/

/-- A check whose inhibitor test fails only when every inhibitor place has its bit set. -/
def conc004_inhAll {N : Type} : EnableCheck N :=
  { refEnableCheck with
    presence := fun t bits => (inPlaces t).all bits && t.core.reads.all bits &&
      !(t.core.inhibitors.all bits && !t.core.inhibitors.isEmpty) }

/-- ✗ An inhibitor test on all inhibitor places together violates CONC-004: `conc004_tInh2`
passes it with bit `0` set and bit `1` clear, although its inhibitor place `0` is marked. -/
@[evidence forbids CONC_004]
theorem CONC_004_forbids_inhAll : ¬ CONC_004 (conc004_inhAll (N := Nat)) := fun h => by
  have := (h conc004_tInh2 (fun p => decide (p = 0))).1 (by decide)
  exact absurd (this.2 0 (by simp [InhibitorMask, InhibitorArc, conc004_tInh2])) (by decide)

/-! ### Every part of the line exercised -/

/-- The line of CONC-004 is exercised by the reference on the AC2 transition `conc004_t` (three
inputs, two reads, one inhibitor, one reset): it passes on the bitmap with bits `0` to `4` set
and the reset bit `6` clear; it fails when the read bit `4` is cleared, when the input bit `0` is
cleared, and when the inhibitor bit `5` is set. -/
@[evidence nonvacuous CONC_004]
theorem CONC_004_nonvacuous :
    (refEnableCheck (N := Nat)).presence conc004_t conc004_bits = true ∧
      (refEnableCheck (N := Nat)).presence conc004_t
        (fun p => conc004_bits p && p != 4) = false ∧
      (refEnableCheck (N := Nat)).presence conc004_t
        (fun p => conc004_bits p && p != 0) = false ∧
      (refEnableCheck (N := Nat)).presence conc004_t
        (fun p => conc004_bits p || p == 5) = false ∧
      MaskCheck conc004_t conc004_bits := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  exact (refEnableCheck_presence _ _).1 (by decide)

end Libpetri.Spec
