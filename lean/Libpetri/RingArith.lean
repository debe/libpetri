/-
# Ring arithmetic: the modular index algebra of the flat token pool

`precompiled_backend.rs` addresses the *i*-th oldest token of place `pid` at

    token_pool[place_offset[pid] + (ring_head[pid] + i) % ring_capacity[pid]]

Everything the pool proofs need about that expression is the handful of facts
about `(head + i) % cap` collected here. No Mathlib: `omega` cannot discharge
goals with a *variable* modulus, so these are proved from core
`Nat.mod_add_mod` / `Nat.mod_eq_of_lt` by hand — they are the entire modular
toolkit, and every later file stays mod-free by rewriting with them.
-/

namespace Libpetri

/-- The ring-relative slot of logical position `i`: `(head + i) % cap`. -/
def ringPos (head i cap : Nat) : Nat := (head + i) % cap

/-- The inverse of `ringPos`: recover the logical position from a
ring-relative slot `v`. The shipped code never computes this (it always walks
positions forward); the proofs use it to define slides pointwise and to get
slot injectivity for free. -/
def ringPosInv (head v cap : Nat) : Nat := (v + cap - head) % cap

theorem ringPos_lt (head i : Nat) {cap : Nat} (hcap : 0 < cap) :
    ringPos head i cap < cap := Nat.mod_lt _ hcap

/-- `ringPosInv` really is a left inverse on positions `i < cap`. -/
theorem ringPosInv_ringPos {head i cap : Nat} (hh : head < cap) (hi : i < cap) :
    ringPosInv head (ringPos head i cap) cap = i := by
  unfold ringPos ringPosInv
  rw [show (head + i) % cap + cap - head = (head + i) % cap + (cap - head) by omega,
    Nat.mod_add_mod,
    show head + i + (cap - head) = i + cap by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt hi]

/-- Distinct logical positions occupy distinct slots (RB2's backbone). -/
theorem ringPos_injective {head cap : Nat} (hh : head < cap) {i j : Nat}
    (hi : i < cap) (hj : j < cap)
    (h : ringPos head i cap = ringPos head j cap) : i = j :=
  calc i = ringPosInv head (ringPos head i cap) cap :=
        (ringPosInv_ringPos hh hi).symm
    _ = ringPosInv head (ringPos head j cap) cap := by rw [h]
    _ = j := ringPosInv_ringPos hh hj

/-- Advancing the head reindexes every position by one: position `i` under the
new head `(head + 1) % cap` is position `i + 1` under the old head. This is
why `ring_remove_first` (`precompiled_backend.rs` — head-advance, count
decrement) projects to `List.tail`. -/
theorem ringPos_succ_head {head i cap : Nat} :
    ringPos ((head + 1) % cap) i cap = ringPos head (i + 1) cap := by
  unfold ringPos
  rw [Nat.mod_add_mod, show head + 1 + i = head + (i + 1) by omega]

/-- Incrementing the tail: `(tail + 1) % cap` for `tail = ringPos head cnt cap`
is the slot of position `cnt + 1` — the append slot of `ring_add_last`. -/
theorem ringPos_succ (head cnt cap : Nat) :
    (ringPos head cnt cap + 1) % cap = ringPos head (cnt + 1) cap := by
  unfold ringPos
  rw [Nat.mod_add_mod, Nat.add_assoc]

/-- Decrementing the tail: the branchy `if tail == 0 { cap - 1 } else
{ tail - 1 }` of `ring_remove_matching`'s tail-slide is `(tail + cap - 1) %
cap` in disguise. -/
theorem pred_ring {cap t : Nat} (hcap : 0 < cap) (ht : t < cap) :
    (if t = 0 then cap - 1 else t - 1) = (t + cap - 1) % cap := by
  split
  · next h =>
    subst h
    rw [show 0 + cap - 1 = cap - 1 by omega, Nat.mod_eq_of_lt (by omega)]
  · next h =>
    rw [show t + cap - 1 = (t - 1) + cap by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- Retracting the tail by one lands on the slot of position `cnt - 1`. -/
theorem ringPos_pred {head cnt cap : Nat} (hcap : 0 < cap) (hcnt : 0 < cnt) :
    (ringPos head cnt cap + cap - 1) % cap = ringPos head (cnt - 1) cap := by
  unfold ringPos
  rw [show (head + cnt) % cap + cap - 1 = (head + cnt) % cap + (cap - 1) by omega,
    Nat.mod_add_mod,
    show head + cnt + (cap - 1) = (head + (cnt - 1)) + cap by omega,
    Nat.add_mod_right]

end Libpetri
