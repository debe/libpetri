/-
# Match cache: WF / frame / nplaces plumbing

The `ring_remove_matching` facts and the whole-mutation WF, frame and
`nplaces` lemmas of `MatchCache.lean`, split out of it.
-/
import Libpetri.MatchCache.Model

namespace Libpetri

/-- `WF` survives `ring_remove_matching` (both halves of RB6). -/
theorem removeMatching_snd_wf {s : Pool} (hwf : Pool.WF s) {r : PlaceId}
    (hr : r < s.nplaces) (pred : Colour → Bool) :
    Pool.WF (s.removeMatching r pred).2 := by
  cases hres : (s.removeMatching r pred).1 with
  | none => rw [(Pool.removeMatching_none hwf hr hres).1]; exact hwf
  | some c =>
    obtain ⟨_, _, _, _, _, _, _, hwf'⟩ := Pool.removeMatching_some hwf hr hres
    exact hwf'

theorem removeMatching_snd_nplaces (s : Pool) (r : PlaceId)
    (pred : Colour → Bool) :
    (s.removeMatching r pred).2.nplaces = s.nplaces := by
  unfold Pool.removeMatching
  cases s.findMatch r pred with
  | none => rfl
  | some i =>
    dsimp only
    by_cases hside : i ≤ s.cnt r - 1 - i
    · rw [if_pos hside, Pool.headSlideAt_nplaces]
    · rw [if_neg hside, Pool.tailSlideAt_nplaces]

/-- Frame: `ring_remove_matching` at another place leaves this projection
untouched (RB6's other-place clause / identity on no match). -/
theorem removeMatching_snd_proj_other {s : Pool} (hwf : Pool.WF s)
    {r : PlaceId} (hr : r < s.nplaces) {p : PlaceId} (hp : p < s.nplaces)
    (hne : p ≠ r) (pred : Colour → Bool) :
    (s.removeMatching r pred).2.proj p = s.proj p := by
  cases hres : (s.removeMatching r pred).1 with
  | none => rw [(Pool.removeMatching_none hwf hr hres).1]
  | some c =>
    obtain ⟨_, _, _, _, _, _, hframe, _⟩ := Pool.removeMatching_some hwf hr hres
    exact hframe p hp hne

/-! ## WF / frame / nplaces plumbing for whole mutations -/

theorem matchedRemoveIter_wf {p : PlaceId} (pred : Colour → Bool) :
    ∀ (k : Nat) {s : Pool}, Pool.WF s → p < s.nplaces →
      Pool.WF (matchedRemoveIter s p pred k) := by
  intro k
  induction k with
  | zero => intro s hwf _; exact hwf
  | succ k ih =>
    intro s hwf hp
    simp only [matchedRemoveIter]
    exact ih (removeMatching_snd_wf hwf hp pred)
      (by rw [removeMatching_snd_nplaces]; exact hp)

theorem matchedRemoveIter_nplaces (r : PlaceId) (pred : Colour → Bool) :
    ∀ (k : Nat) (s : Pool),
      (matchedRemoveIter s r pred k).nplaces = s.nplaces := by
  intro k
  induction k with
  | zero => intro s; rfl
  | succ k ih =>
    intro s
    simp only [matchedRemoveIter]
    rw [ih, removeMatching_snd_nplaces]

theorem matchedRemoveIter_proj_other {r p : PlaceId} (hne : p ≠ r)
    (pred : Colour → Bool) :
    ∀ (k : Nat) {s : Pool}, Pool.WF s → r < s.nplaces → p < s.nplaces →
      (matchedRemoveIter s r pred k).proj p = s.proj p := by
  intro k
  induction k with
  | zero => intro s _ _ _; rfl
  | succ k ih =>
    intro s hwf hr hp
    simp only [matchedRemoveIter]
    rw [ih (removeMatching_snd_wf hwf hr pred)
        (by rw [removeMatching_snd_nplaces]; exact hr)
        (by rw [removeMatching_snd_nplaces]; exact hp),
      removeMatching_snd_proj_other hwf hr hp hne pred]

theorem drainIter_wf (r : PlaceId) :
    ∀ (k : Nat) {s : Pool}, Pool.WF s → r < s.nplaces → k ≤ s.cnt r →
      Pool.WF (drainIter s r k) := by
  intro k
  induction k with
  | zero => intro s hwf _ _; exact hwf
  | succ k ih =>
    intro s hwf hr hk
    simp only [drainIter]
    have hcnt : 0 < s.cnt r := by omega
    exact ih (Pool.removeFirst_wf hwf hr hcnt)
      (by rw [Pool.removeFirst_nplaces]; exact hr)
      (by rw [Pool.removeFirst_cnt_self]; omega)

theorem drainIter_nplaces (r : PlaceId) :
    ∀ (k : Nat) (s : Pool), (drainIter s r k).nplaces = s.nplaces := by
  intro k
  induction k with
  | zero => intro s; rfl
  | succ k ih =>
    intro s
    simp only [drainIter]
    rw [ih, Pool.removeFirst_nplaces]

theorem drainIter_proj_other {r p : PlaceId} (hne : p ≠ r) :
    ∀ (k : Nat) {s : Pool}, Pool.WF s → r < s.nplaces → p < s.nplaces →
      k ≤ s.cnt r → (drainIter s r k).proj p = s.proj p := by
  intro k
  induction k with
  | zero => intro s _ _ _ _; rfl
  | succ k ih =>
    intro s hwf hr hp hk
    simp only [drainIter]
    have hcnt : 0 < s.cnt r := by omega
    rw [ih (Pool.removeFirst_wf hwf hr hcnt)
        (by rw [Pool.removeFirst_nplaces]; exact hr)
        (by rw [Pool.removeFirst_nplaces]; exact hp)
        (by rw [Pool.removeFirst_cnt_self]; omega),
      Pool.removeFirst_proj_other hwf hr hp hne]

/-- Every modeled mutation preserves RB1–RB3. -/
theorem applyMutPool_wf {r : PlaceId} {s : Pool} (hwf : Pool.WF s)
    (hr : r < s.nplaces) (op : Mut) : Pool.WF (applyMutPool r s op) := by
  cases op with
  | add c => exact Pool.addLast_wf hwf hr c
  | matchedConsume pred m ringK cacheK =>
    exact matchedRemoveIter_wf pred ringK hwf hr
  | consumeFirst =>
    simp only [applyMutPool]
    by_cases hc : 0 < s.cnt r
    · rw [if_pos hc]; exact Pool.removeFirst_wf hwf hr hc
    · rw [if_neg hc]; exact hwf
  | reset => exact drainIter_wf r (s.cnt r) hwf hr (Nat.le_refl _)

theorem applyMutPool_nplaces (r : PlaceId) (s : Pool) (op : Mut) :
    (applyMutPool r s op).nplaces = s.nplaces := by
  cases op with
  | add c => exact addLast_nplaces s r c
  | matchedConsume pred m ringK cacheK =>
    exact matchedRemoveIter_nplaces r pred ringK s
  | consumeFirst =>
    simp only [applyMutPool]
    by_cases hc : 0 < s.cnt r
    · rw [if_pos hc, Pool.removeFirst_nplaces]
    · rw [if_neg hc]
  | reset => exact drainIter_nplaces r (s.cnt r) s

/-- Frame: any mutation addressed to another place leaves this place's
projection untouched — assembled from `Ring.lean`'s `*_proj_other` family. -/
theorem applyMutPool_proj_other {r p : PlaceId} {s : Pool} (hwf : Pool.WF s)
    (hr : r < s.nplaces) (hp : p < s.nplaces) (hne : p ≠ r) (op : Mut) :
    (applyMutPool r s op).proj p = s.proj p := by
  cases op with
  | add c => exact Pool.addLast_proj_other hwf hr hp hne c
  | matchedConsume pred m ringK cacheK =>
    exact matchedRemoveIter_proj_other hne pred ringK hwf hr hp
  | consumeFirst =>
    simp only [applyMutPool]
    by_cases hc : 0 < s.cnt r
    · rw [if_pos hc]; exact Pool.removeFirst_proj_other hwf hr hp hne
    · rw [if_neg hc]
  | reset => exact drainIter_proj_other hne (s.cnt r) hwf hr hp (Nat.le_refl _)

end Libpetri
