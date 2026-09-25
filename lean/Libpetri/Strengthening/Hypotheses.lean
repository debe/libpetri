/-
# The strengthening hypotheses and per-step conservation

H1 (`ZeroOnNonlinear`) and the per-firing conservation lemma `dot_fireA`,
split out of `Strengthening.lean`, which proves strengthening sound from them.
-/
import Libpetri.InvariantSum

namespace Libpetri

/-!
## The hypotheses the proof forces

The abstract fire relation (`fireA`, modelling `firing_conditions`,
`smt_encoder.rs:372-396`) has exactly two non-linear arms: a reset place and a
consume-all place both get `m'_i = post[i]` (`smt_encoder.rs:376-381`), erasing
however many tokens the
place actually held. A weighted sum survives such an arm only where the
weight is zero — that is H1, and `consume_all_hypothesis_is_necessary` is the
counterexample that put it into the shipped gate. H2 is the incidence-column
condition the C2 gate always checked. H3 — env-freedom — is carried by the
reachability relation itself; its env-aware replacement H3′ appears with
`invariant_strengthening_sound_inj`.
-/

/-- **H1 (linearity).** Below the truncation bound, `y` vanishes on every
place where `fireA` is non-linear: reset places and consume-all places
(`Card.consumesAll`, i.e. `In::All` / `In::AtLeast` — `flatten`,
`net_flattener.rs:53-55`).
Only places below `n` matter: the emitted sum never reads past `place_count`. -/
def ZeroOnNonlinear (y : Weight) (t : Transition) (n : Nat) : Prop :=
  ∀ p, p < n → t.resets.contains p = true ∨ consumeAllAt t p = true → y p = 0

/-- Abstract enablement bounds the linear arm's `Nat` subtraction:
`pre[p] ≤ m p`, so `m p - pre[p] + post[p]` computes the exact integer
`m p − pre[p] + post[p]`. -/
theorem pre_le_of_enabledA {m : AMarking} {t : Transition}
    (hEn : enabledA m t = true) (p : PlaceId) : pre t p ≤ m p := by
  unfold pre
  cases hs : specAt t p with
  | none => exact Nat.zero_le _
  | some s =>
    obtain ⟨hmem, hplace⟩ := specAt_sound hs
    unfold enabledA at hEn
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hEn
    exact hplace ▸ hEn.1.1 s hmem

/-- One place's contribution to `y·M` across one abstract firing: with H1 at
`p` and enablement, the change is exactly `y p · (post[p] − pre[p])` — the
place's incidence-column entry. -/
theorem fire_term (y : Weight) {m : AMarking} {t : Transition} (br : List PlaceId)
    {n : Nat} (h1 : ZeroOnNonlinear y t n) (hEn : enabledA m t = true)
    (p : PlaceId) (hp : p < n) :
    y p * (fireA m t br p : Int)
      = y p * (m p : Int) + y p * ((post br p : Int) - (pre t p : Int)) := by
  by_cases hR : t.resets.contains p = true
  · rw [h1 p hp (Or.inl hR)]
    omega
  · by_cases hCA : consumeAllAt t p = true
    · rw [h1 p hp (Or.inr hCA)]
      omega
    · have hfa : fireA m t br p = m p - pre t p + post br p := by
        unfold fireA
        rw [if_neg hR, if_neg hCA]
      have hle : pre t p ≤ m p := pre_le_of_enabledA hEn p
      have hcast : ((m p - pre t p + post br p : Nat) : Int)
          = (m p : Int) + ((post br p : Int) - (pre t p : Int)) := by omega
      rw [hfa, hcast, Int.mul_add]

/-- Per-step conservation: one abstract firing preserves `y·M` when `y` is
(H1) zero on the firing's non-linear places and (H2) annihilates its
incidence column. [VER-005] AC2, with the hypothesis the shipped pipeline is
missing made explicit. -/
theorem dot_fireA (y : Weight) {m : AMarking} {t : Transition} {br : List PlaceId}
    {n : Nat} (h1 : ZeroOnNonlinear y t n) (h2 : dotInc y (t, br) n = 0)
    (hEn : enabledA m t = true) :
    dot y (fireA m t br) n = dot y m n := by
  have hsplit : dot y (fireA m t br) n = dot y m n + dotInc y (t, br) n := by
    rw [dot_eq_isum, dot_eq_isum, isum_congr fun p hp => fire_term y br h1 hEn p hp]
    exact isum_add _ _ n
  rw [hsplit, h2]
  omega

end Libpetri
