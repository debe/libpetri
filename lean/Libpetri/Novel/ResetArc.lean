import Libpetri.Basic

/-!
# Reset arcs ([CORE-034])

[CORE-034]: a reset arc removes **all** tokens from its place when the transition fires, and
it does **not** contribute to enablement.
AC1: the transition fires even if the reset place is empty.
AC2: if the reset place has tokens, all of them are removed on firing.
AC3: the reset arc imposes no token requirement.

The Rust behaviour:
* Enablement. `CompiledNet::new` (`rust/libpetri-runtime/src/compiled_net.rs:192-197`) puts a
  reset place in the reverse index and the `drained` set only. It never sets a bit in
  `needs_masks` or `inhibitor_masks`, and `can_enable_bitmap` (`compiled_net.rs:356`) and
  `can_enable` (`rust/libpetri-runtime/src/bitmap_backend.rs:328`) read nothing else of it.
  `enabledC` / `enabledA` (`Basic.lean`) model this: neither reads `Transition.resets`.
* Firing. `consume_for_firing` (`bitmap_backend.rs:834-852`) calls `marking.remove_all` on
  every reset place, and does so whatever the place holds, including nothing. `alphaFireC`
  (concrete, token-count image) and `fireA` (the CHC fire relation, `smt_encoder.rs:372-396`)
  give a reset place exactly the tokens the firing itself produces there.

Results:
* `enabledC_resets` / `enabledA_resets` (AC3): enablement does not depend on the reset list.
  Adding, removing or changing reset arcs never changes whether a transition is enabled.
* `enabledC_congr_off` / `enabledA_congr_off` (AC1, AC3): a place that is only a reset place
  of `t` (not an input, inhibitor or read place) cannot influence `t`'s enablement. The
  transition is enabled with that place empty exactly when it is enabled with any content
  there.
* `alphaFireC_reset` / `fireA_reset` (AC2): after the firing a reset place holds exactly the
  tokens produced into it. How many it held before is erased, so with no output to it the
  place is empty.
* `reset_arc_semantics`: AC1–AC3 together for the concrete model.
* `alphaFireC_reset_eq_fireA`: at a reset place the concrete image and the CHC relation agree
  under `UnitOutput`.

Out of scope:
* The EXEC-003 AC5 refinement. A reset later in a pass drains `drainable(place, live)`, so
  tokens a same-pass synchronous action deposited survive. The model drains the whole live
  queue, which is the `take == live` fast path of every deposit-free pass.
* Timing, events (`emit_removed`) and token identity. Only counts are modelled, as in
  `Basic.lean`.
-/

namespace Libpetri.Novel.ResetArc

open Libpetri

/-! ## Enablement ignores reset arcs (AC3) -/

/-- Concrete enablement is independent of the reset list. -/
theorem enabledC_resets (m : CMarking) (t : Transition) (r : List PlaceId) :
    enabledC m { t with resets := r } = enabledC m t := rfl

/-- Abstract (CHC) enablement is independent of the reset list. -/
theorem enabledA_resets (m : AMarking) (t : Transition) (r : List PlaceId) :
    enabledA m { t with resets := r } = enabledA m t := rfl

theorem all_congr_mem {α : Type} {f g : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.all f = l.all g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.all_cons]
    rw [h a List.mem_cons_self, all_congr_mem fun x hx => h x (List.mem_cons_of_mem a hx)]

/-- `p` is only (possibly) a reset place of `t`: no input, inhibitor or read arc touches it. -/
def OnlyReset (t : Transition) (p : PlaceId) : Prop :=
  (∀ s ∈ t.inputs, s.place ≠ p) ∧ p ∉ t.inhibitors ∧ p ∉ t.reads

/-- **A reset place imposes no token requirement** (concrete). If `m` and `m'` agree off `p`
and `p` is only a reset place of `t`, then `t` is enabled under `m` iff under `m'`. Take
`m' p = []` for AC1. -/
theorem enabledC_congr_off {m m' : CMarking} {t : Transition} {p : PlaceId}
    (hp : OnlyReset t p) (hm : ∀ q, q ≠ p → m q = m' q) :
    enabledC m t = enabledC m' t := by
  obtain ⟨hin, hinh, hrd⟩ := hp
  unfold enabledC
  have e1 : t.inputs.all (fun s => decide (s.card.required ≤ matchCount m s))
      = t.inputs.all (fun s => decide (s.card.required ≤ matchCount m' s)) :=
    all_congr_mem fun s hs => by
      unfold matchCount
      rw [hm s.place (hin s hs)]
  have e2 : t.inhibitors.all (fun q => (m q).length == 0)
      = t.inhibitors.all (fun q => (m' q).length == 0) :=
    all_congr_mem fun q hq => by
      rw [hm q fun h => hinh (h ▸ hq)]
  have e3 : t.reads.all (fun q => decide (1 ≤ (m q).length))
      = t.reads.all (fun q => decide (1 ≤ (m' q).length)) :=
    all_congr_mem fun q hq => by
      rw [hm q fun h => hrd (h ▸ hq)]
  rw [e1, e2, e3]

/-- **A reset place imposes no token requirement** (abstract, the CHC guard). -/
theorem enabledA_congr_off {m m' : AMarking} {t : Transition} {p : PlaceId}
    (hp : OnlyReset t p) (hm : ∀ q, q ≠ p → m q = m' q) :
    enabledA m t = enabledA m' t := by
  obtain ⟨hin, hinh, hrd⟩ := hp
  unfold enabledA
  have e1 : t.inputs.all (fun s => decide (s.card.required ≤ m s.place))
      = t.inputs.all (fun s => decide (s.card.required ≤ m' s.place)) :=
    all_congr_mem fun s hs => by rw [hm s.place (hin s hs)]
  have e2 : t.inhibitors.all (fun q => m q == 0) = t.inhibitors.all (fun q => m' q == 0) :=
    all_congr_mem fun q hq => by rw [hm q fun h => hinh (h ▸ hq)]
  have e3 : t.reads.all (fun q => decide (1 ≤ m q)) = t.reads.all (fun q => decide (1 ≤ m' q)) :=
    all_congr_mem fun q hq => by rw [hm q fun h => hrd (h ▸ hq)]
  rw [e1, e2, e3]

/-- The marking `m` with place `p` emptied. -/
def emptyAt (m : CMarking) (p : PlaceId) : CMarking :=
  fun q => if q = p then [] else m q

/-- **AC1.** A transition whose place `p` is only a reset place is enabled with `p` empty
exactly when it is enabled with `p` holding anything. -/
theorem enabledC_emptyAt {m : CMarking} {t : Transition} {p : PlaceId} (hp : OnlyReset t p) :
    enabledC (emptyAt m p) t = enabledC m t :=
  enabledC_congr_off hp fun q hq => by simp only [emptyAt, if_neg hq]

/-! ## Firing drains the reset place (AC2) -/

/-- **AC2** (concrete, token-count image). After firing, a reset place holds exactly what the
firing produced into it, independent of how many tokens it held. -/
theorem alphaFireC_reset (m : CMarking) (t : Transition) (prod : PlaceId → Nat) {p : PlaceId}
    (hr : t.resets.contains p = true) : alphaFireC m t prod p = prod p := by
  simp only [alphaFireC, hr, if_true]

/-- **AC2** with nothing produced into the reset place: it ends empty, whatever it held. -/
theorem alphaFireC_reset_empty (m : CMarking) (t : Transition) (prod : PlaceId → Nat)
    {p : PlaceId} (hr : t.resets.contains p = true) (hprod : prod p = 0) :
    alphaFireC m t prod p = 0 := by
  rw [alphaFireC_reset m t prod hr, hprod]

/-- **AC2** (abstract, `firing_conditions`): `m'_p = post[p]` on a reset place. -/
theorem fireA_reset (m : AMarking) (t : Transition) (br : List PlaceId) {p : PlaceId}
    (hr : t.resets.contains p = true) : fireA m t br p = post br p := by
  simp only [fireA, hr, if_true]

/-- **AC2** in the CHC relation with the reset place off the output branch: `m'_p = 0`. -/
theorem fireA_reset_empty (m : AMarking) (t : Transition) (br : List PlaceId) {p : PlaceId}
    (hr : t.resets.contains p = true) (hbr : br.contains p = false) :
    fireA m t br p = 0 := by
  rw [fireA_reset m t br hr]
  simp only [post, hbr, Bool.false_eq_true, if_false]

/-- At a reset place the concrete image and the CHC relation agree when the action writes one
token per branch place (`UnitOutput`). -/
theorem alphaFireC_reset_eq_fireA (c : CMarking) (t : Transition) {prod : PlaceId → Nat}
    {br : List PlaceId} (hu : UnitOutput prod br) {p : PlaceId}
    (hr : t.resets.contains p = true) :
    alphaFireC c t prod p = fireA (alpha c) t br p := by
  rw [alphaFireC_reset c t prod hr, fireA_reset _ t br hr, hu p]

/-! ## CORE-034, all three criteria -/

/-- **[CORE-034]** for the concrete model. Let `p` be a reset place of `t` that no input,
inhibitor or read arc touches. Then:
1. (AC1) `t` is enabled with `p` empty iff it is enabled with `p`'s actual content;
2. (AC2) after the firing `p` holds exactly the produced tokens, so none of the old ones
   survive, and with no output to `p` it is empty;
3. (AC3) enablement is the same with every reset arc removed. -/
theorem reset_arc_semantics {m : CMarking} {t : Transition} {p : PlaceId}
    (hr : t.resets.contains p = true) (hp : OnlyReset t p) :
    enabledC (emptyAt m p) t = enabledC m t
    ∧ (∀ prod : PlaceId → Nat, alphaFireC m t prod p = prod p
        ∧ (prod p = 0 → alphaFireC m t prod p = 0))
    ∧ enabledC m { t with resets := [] } = enabledC m t :=
  ⟨enabledC_emptyAt hp,
    fun prod => ⟨alphaFireC_reset m t prod hr, alphaFireC_reset_empty m t prod hr⟩,
    enabledC_resets m t []⟩

end Libpetri.Novel.ResetArc
