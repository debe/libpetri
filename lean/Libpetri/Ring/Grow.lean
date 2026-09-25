/-
# The flat token pool: `grow_ring_static` and `ring_add_last`

`growRing`, `pushLast` and `addLast` with their WF and projection lemmas
(RB5), split out of `Ring.lean`.
-/
import Libpetri.Ring.Core

namespace Libpetri

namespace Pool

/-! ## `grow_ring_static` (`precompiled_backend.rs:1405-1432`)

Appends a fresh `2 * cap` block at the end of the pool, `take()`s the `cnt`
live tokens into it linearly (`head = 0`, `tail = cnt`), and re-points the
place at the new block. The old block is leaked — RB3 keeps it outside every
current block, so its (now stale) contents are unconstrained garbage. -/

def growRing (s : Pool) (p : PlaceId) : Pool where
  pool := fun idx =>
    if s.len ≤ idx then
      if idx < s.len + s.cnt p then s.pool (s.slot p (idx - s.len)) else none
    else if s.offset p ≤ idx ∧ idx < s.offset p + s.cap p ∧
            ringPosInv (s.head p) (idx - s.offset p) (s.cap p) < s.cnt p then
      none
    else s.pool idx
  len := s.len + 2 * s.cap p
  offset := fun q => if q = p then s.len else s.offset q
  head := fun q => if q = p then 0 else s.head q
  tail := fun q => if q = p then s.cnt q else s.tail q
  cnt := s.cnt
  cap := fun q => if q = p then 2 * s.cap p else s.cap q
  nplaces := s.nplaces

@[simp] theorem growRing_cnt (s : Pool) (p : PlaceId) :
    (s.growRing p).cnt = s.cnt := rfl
@[simp] theorem growRing_nplaces (s : Pool) (p : PlaceId) :
    (s.growRing p).nplaces = s.nplaces := rfl
@[simp] theorem growRing_len (s : Pool) (p : PlaceId) :
    (s.growRing p).len = s.len + 2 * s.cap p := rfl
@[simp] theorem growRing_cap_self (s : Pool) (p : PlaceId) :
    (s.growRing p).cap p = 2 * s.cap p := by simp [growRing]
theorem growRing_cap_other (s : Pool) {p q : PlaceId} (hne : q ≠ p) :
    (s.growRing p).cap q = s.cap q := by simp [growRing, hne]
@[simp] theorem growRing_offset_self (s : Pool) (p : PlaceId) :
    (s.growRing p).offset p = s.len := by simp [growRing]
theorem growRing_offset_other (s : Pool) {p q : PlaceId} (hne : q ≠ p) :
    (s.growRing p).offset q = s.offset q := by simp [growRing, hne]
@[simp] theorem growRing_head_self (s : Pool) (p : PlaceId) :
    (s.growRing p).head p = 0 := by simp [growRing]
theorem growRing_head_other (s : Pool) {p q : PlaceId} (hne : q ≠ p) :
    (s.growRing p).head q = s.head q := by simp [growRing, hne]
@[simp] theorem growRing_tail_self (s : Pool) (p : PlaceId) :
    (s.growRing p).tail p = s.cnt p := by simp [growRing]
theorem growRing_tail_other (s : Pool) {p q : PlaceId} (hne : q ≠ p) :
    (s.growRing p).tail q = s.tail q := by simp [growRing, hne]

/-- Positions of the grown place live at `len + i` in the new block. -/
theorem growRing_slot_self (s : Pool) {p : PlaceId} {i : Nat}
    (hi : i < 2 * s.cap p) : (s.growRing p).slot p i = s.len + i := by
  unfold slot ringPos
  rw [growRing_offset_self, growRing_head_self, growRing_cap_self,
    Nat.zero_add, Nat.mod_eq_of_lt hi]

theorem growRing_slot_other (s : Pool) {p q : PlaceId} (hne : q ≠ p) (i : Nat) :
    (s.growRing p).slot q i = s.slot q i := by
  unfold slot
  rw [growRing_offset_other s hne, growRing_head_other s hne,
    growRing_cap_other s hne]

/-- Reading the copied live token `i < cnt p` out of the new block. -/
theorem growRing_pool_new (s : Pool) {p : PlaceId} {i : Nat} (hi : i < s.cnt p) :
    (s.growRing p).pool (s.len + i) = s.pool (s.slot p i) := by
  show (if s.len ≤ s.len + i then
      if s.len + i < s.len + s.cnt p then s.pool (s.slot p (s.len + i - s.len))
      else none
    else _) = _
  rw [if_pos (by omega), if_pos (by omega), Nat.add_sub_cancel_left]

/-- Reading a fresh free slot of the new block. -/
theorem growRing_pool_new_free (s : Pool) {p : PlaceId} {i : Nat}
    (hlo : s.cnt p ≤ i) (_hhi : i < 2 * s.cap p) :
    (s.growRing p).pool (s.len + i) = none := by
  show (if s.len ≤ s.len + i then
      if s.len + i < s.len + s.cnt p then s.pool (s.slot p (s.len + i - s.len))
      else none
    else _) = _
  rw [if_pos (by omega), if_neg (by omega)]

/-- Reading any slot below the old length that is not a live slot of `p`'s
old block: unchanged. -/
theorem growRing_pool_stale (s : Pool) {p : PlaceId} {idx : Nat}
    (hlen : idx < s.len)
    (hnot : ¬(s.offset p ≤ idx ∧ idx < s.offset p + s.cap p ∧
      ringPosInv (s.head p) (idx - s.offset p) (s.cap p) < s.cnt p)) :
    (s.growRing p).pool idx = s.pool idx := by
  show (if s.len ≤ idx then _ else
    if s.offset p ≤ idx ∧ idx < s.offset p + s.cap p ∧
        ringPosInv (s.head p) (idx - s.offset p) (s.cap p) < s.cnt p then
      none
    else s.pool idx) = _
  rw [if_neg (by omega), if_neg hnot]

theorem growRing_wf {s : Pool} (hwf : WF s) {p : PlaceId} (hp : p < s.nplaces) :
    WF (s.growRing p) := by
  have hcap := hwf.cap_pos p hp
  have hle := hwf.cnt_le p hp
  have hh := hwf.head_lt p hp
  constructor
  · intro q hq
    rw [growRing_nplaces] at hq
    by_cases hne : q = p
    · subst hne
      rw [growRing_cap_self]
      have := hwf.cap_pos q hq
      omega
    · rw [growRing_cap_other s hne]
      exact hwf.cap_pos q hq
  · intro q hq
    rw [growRing_nplaces] at hq
    rw [growRing_cnt]
    by_cases hne : q = p
    · subst hne
      rw [growRing_cap_self]
      have := hwf.cnt_le q hq
      omega
    · rw [growRing_cap_other s hne]
      exact hwf.cnt_le q hq
  · intro q hq
    rw [growRing_nplaces] at hq
    by_cases hne : q = p
    · subst hne
      rw [growRing_head_self, growRing_cap_self]
      have := hwf.cap_pos q hq
      omega
    · rw [growRing_head_other s hne, growRing_cap_other s hne]
      exact hwf.head_lt q hq
  · intro q hq
    rw [growRing_nplaces] at hq
    rw [growRing_cnt]
    by_cases hne : q = p
    · subst hne
      rw [growRing_tail_self, growRing_head_self, growRing_cap_self]
      unfold ringPos
      have h1 : s.cnt q < 2 * s.cap q := by
        have := hwf.cnt_le q hq; omega
      rw [Nat.zero_add, Nat.mod_eq_of_lt h1]
    · rw [growRing_tail_other s hne, growRing_head_other s hne,
        growRing_cap_other s hne]
      exact hwf.tail_eq q hq
  · intro q hq
    rw [growRing_nplaces] at hq
    rw [growRing_len]
    by_cases hne : q = p
    · subst hne
      rw [growRing_offset_self, growRing_cap_self]
      omega
    · rw [growRing_offset_other s hne, growRing_cap_other s hne]
      have := hwf.in_bounds q hq
      omega
  · intro q hq i hi
    rw [growRing_nplaces] at hq
    rw [growRing_cnt] at hi
    by_cases hne : q = p
    · subst hne
      rw [growRing_slot_self s (by omega), growRing_pool_new s hi]
      exact hwf.occupied q hq i hi
    · rw [growRing_slot_other s hne, growRing_pool_stale s
        (by
          have h1 := slot_lt_block (hwf.cap_pos q hq) (s := s) (p := q) i
          have h2 := hwf.in_bounds q hq
          omega)
        (by
          intro ⟨ha, hb, _⟩
          have h1 := slot_lt_block (hwf.cap_pos q hq) (s := s) (p := q) i
          have h2 := offset_le_slot s q i
          rcases hwf.disjoint p q hp hq (fun h => hne h.symm) with h | h <;> omega)]
      exact hwf.occupied q hq i hi
  · intro q hq i hlo hhi
    rw [growRing_nplaces] at hq
    rw [growRing_cnt] at hlo
    by_cases hne : q = p
    · subst hne
      rw [growRing_cap_self] at hhi
      rw [growRing_slot_self s hhi]
      exact growRing_pool_new_free s hlo hhi
    · rw [growRing_cap_other s hne] at hhi
      rw [growRing_slot_other s hne, growRing_pool_stale s
        (by
          have h1 := slot_lt_block (hwf.cap_pos q hq) (s := s) (p := q) i
          have h2 := hwf.in_bounds q hq
          omega)
        (by
          intro ⟨ha, hb, _⟩
          have h1 := slot_lt_block (hwf.cap_pos q hq) (s := s) (p := q) i
          have h2 := offset_le_slot s q i
          rcases hwf.disjoint p q hp hq (fun h => hne h.symm) with h | h <;> omega)]
      exact hwf.free q hq i hlo hhi
  · intro q r hq hr hqr
    rw [growRing_nplaces] at hq hr
    by_cases hqp : q = p
    · subst hqp
      rw [growRing_offset_self, growRing_offset_other s (fun h => hqr h.symm),
        growRing_cap_other s (fun h => hqr h.symm)]
      have := hwf.in_bounds r hr
      omega
    · by_cases hrp : r = p
      · subst hrp
        rw [growRing_offset_self, growRing_offset_other s hqp,
          growRing_cap_other s hqp]
        have := hwf.in_bounds q hq
        omega
      · rw [growRing_offset_other s hqp, growRing_offset_other s hrp,
          growRing_cap_other s hqp, growRing_cap_other s hrp]
        exact hwf.disjoint q r hq hr hqr

/-- RB5, grow half: relocating the ring block preserves the projection. -/
theorem growRing_proj_self {s : Pool} (hwf : WF s) {p : PlaceId}
    (hp : p < s.nplaces) : (s.growRing p).proj p = s.proj p := by
  have hle := hwf.cnt_le p hp
  have hcap := hwf.cap_pos p hp
  unfold proj
  rw [growRing_cnt]
  apply projFrom_eq_of
  intro i hi
  rw [Nat.zero_add, growRing_slot_self s (by omega), growRing_pool_new s hi]

theorem growRing_proj_other {s : Pool} (hwf : WF s) {p q : PlaceId}
    (hp : p < s.nplaces) (hq : q < s.nplaces) (hne : q ≠ p) :
    (s.growRing p).proj q = s.proj q := by
  unfold proj
  rw [growRing_cnt]
  apply projFrom_eq_of
  intro i hi
  rw [Nat.zero_add, growRing_slot_other s hne, growRing_pool_stale s
    (by
      have h1 := slot_lt_block (hwf.cap_pos q hq) (s := s) (p := q) i
      have h2 := hwf.in_bounds q hq
      omega)
    (by
      intro ⟨ha, hb, _⟩
      have h1 := slot_lt_block (hwf.cap_pos q hq) (s := s) (p := q) i
      have h2 := offset_le_slot s q i
      rcases hwf.disjoint p q hp hq (fun h => hne h.symm) with h | h <;> omega)]

/-! ## `ring_add_last` (`precompiled_backend.rs:406-423`)

Write at the tail slot, bump the tail, increment the count — growing first
when the ring is full. `pushLast` is the write half; `addLast` is the shipped
composition. -/

def pushLast (s : Pool) (p : PlaceId) (c : Colour) : Pool :=
  { s with
    pool := fun idx => if idx = s.offset p + s.tail p then some c else s.pool idx
    tail := fun q => if q = p then (s.tail q + 1) % s.cap q else s.tail q
    cnt  := fun q => if q = p then s.cnt q + 1 else s.cnt q }

def addLast (s : Pool) (p : PlaceId) (c : Colour) : Pool :=
  if s.cnt p = s.cap p then (s.growRing p).pushLast p c else s.pushLast p c

@[simp] theorem pushLast_pool (s : Pool) (p : PlaceId) (c : Colour) (idx : Nat) :
    (s.pushLast p c).pool idx
      = if idx = s.offset p + s.tail p then some c else s.pool idx := rfl
@[simp] theorem pushLast_cap (s : Pool) (p : PlaceId) (c : Colour) :
    (s.pushLast p c).cap = s.cap := rfl
@[simp] theorem pushLast_offset (s : Pool) (p : PlaceId) (c : Colour) :
    (s.pushLast p c).offset = s.offset := rfl
@[simp] theorem pushLast_head (s : Pool) (p : PlaceId) (c : Colour) :
    (s.pushLast p c).head = s.head := rfl
@[simp] theorem pushLast_len (s : Pool) (p : PlaceId) (c : Colour) :
    (s.pushLast p c).len = s.len := rfl
@[simp] theorem pushLast_nplaces (s : Pool) (p : PlaceId) (c : Colour) :
    (s.pushLast p c).nplaces = s.nplaces := rfl
@[simp] theorem pushLast_slot (s : Pool) (p : PlaceId) (c : Colour)
    (q : PlaceId) (i : Nat) : (s.pushLast p c).slot q i = s.slot q i := rfl
@[simp] theorem pushLast_cnt_self (s : Pool) (p : PlaceId) (c : Colour) :
    (s.pushLast p c).cnt p = s.cnt p + 1 := by simp [pushLast]
theorem pushLast_cnt_other (s : Pool) {p q : PlaceId} (c : Colour) (hne : q ≠ p) :
    (s.pushLast p c).cnt q = s.cnt q := by simp [pushLast, hne]
@[simp] theorem pushLast_tail_self (s : Pool) (p : PlaceId) (c : Colour) :
    (s.pushLast p c).tail p = (s.tail p + 1) % s.cap p := by simp [pushLast]
theorem pushLast_tail_other (s : Pool) {p q : PlaceId} (c : Colour) (hne : q ≠ p) :
    (s.pushLast p c).tail q = s.tail q := by simp [pushLast, hne]

/-- The write slot `offset + tail` is position `cnt` (RB1's `tail_eq`). -/
theorem write_slot_eq {s : Pool} (hwf : WF s) {p : PlaceId} (hp : p < s.nplaces) :
    s.offset p + s.tail p = s.slot p (s.cnt p) := by
  unfold slot
  rw [hwf.tail_eq p hp]

theorem pushLast_wf {s : Pool} (hwf : WF s) {p : PlaceId} (hp : p < s.nplaces)
    (hlt : s.cnt p < s.cap p) (c : Colour) : WF (s.pushLast p c) := by
  have hh := hwf.head_lt p hp
  have hcap := hwf.cap_pos p hp
  have hws := write_slot_eq hwf hp
  constructor
  · intro q hq
    rw [pushLast_nplaces] at hq
    rw [pushLast_cap]
    exact hwf.cap_pos q hq
  · intro q hq
    rw [pushLast_nplaces] at hq
    rw [pushLast_cap]
    by_cases hne : q = p
    · subst hne
      rw [pushLast_cnt_self]
      omega
    · rw [pushLast_cnt_other s c hne]
      exact hwf.cnt_le q hq
  · intro q hq
    rw [pushLast_nplaces] at hq
    rw [pushLast_cap, pushLast_head]
    exact hwf.head_lt q hq
  · intro q hq
    rw [pushLast_nplaces] at hq
    rw [pushLast_cap, pushLast_head]
    by_cases hne : q = p
    · subst hne
      rw [pushLast_tail_self, pushLast_cnt_self, hwf.tail_eq q hq, ringPos_succ]
    · rw [pushLast_tail_other s c hne, pushLast_cnt_other s c hne]
      exact hwf.tail_eq q hq
  · intro q hq
    rw [pushLast_nplaces] at hq
    rw [pushLast_cap, pushLast_offset, pushLast_len]
    exact hwf.in_bounds q hq
  · intro q hq i hi
    rw [pushLast_nplaces] at hq
    rw [pushLast_slot, pushLast_pool]
    by_cases hne : q = p
    · subst hne
      rw [pushLast_cnt_self] at hi
      by_cases hicnt : i = s.cnt q
      · rw [if_pos (by rw [hws, hicnt])]
        rfl
      · rw [if_neg (by
          rw [hws]
          exact fun h => hicnt (slot_injective hh (by omega) (by omega) h))]
        exact hwf.occupied q hq i (by omega)
    · rw [pushLast_cnt_other s c hne] at hi
      rw [if_neg (by
        rw [hws]
        exact Ne.symm (slot_ne_of_place_ne hwf hp hq (fun h => hne h.symm)
          (s.cnt p) i))]
      exact hwf.occupied q hq i hi
  · intro q hq i hlo hhi
    rw [pushLast_nplaces] at hq
    rw [pushLast_slot, pushLast_pool]
    rw [pushLast_cap] at hhi
    by_cases hne : q = p
    · subst hne
      rw [pushLast_cnt_self] at hlo
      rw [if_neg (by
        rw [hws]
        exact fun h => by
          have := slot_injective hh (i := i) (j := s.cnt q) (by omega) (by omega) h
          omega)]
      exact hwf.free q hq i (by omega) hhi
    · rw [pushLast_cnt_other s c hne] at hlo
      rw [if_neg (by
        rw [hws]
        exact Ne.symm (slot_ne_of_place_ne hwf hp hq (fun h => hne h.symm)
          (s.cnt p) i))]
      exact hwf.free q hq i hlo hhi
  · intro q r hq hr hqr
    rw [pushLast_nplaces] at hq hr
    rw [pushLast_offset, pushLast_cap]
    exact hwf.disjoint q r hq hr hqr

/-- Appending writes exactly one element at the FIFO tail. -/
theorem pushLast_proj_self {s : Pool} (hwf : WF s) {p : PlaceId}
    (hp : p < s.nplaces) (hlt : s.cnt p < s.cap p) (c : Colour) :
    (s.pushLast p c).proj p = s.proj p ++ [c] := by
  have hh := hwf.head_lt p hp
  have hws := write_slot_eq hwf hp
  unfold proj
  rw [pushLast_cnt_self, projFrom_append _ p 0 (s.cnt p) 1]
  congr 1
  · apply projFrom_eq_of
    intro i hi
    rw [pushLast_slot, pushLast_pool, if_neg (by
      rw [hws]
      exact fun h => by
        have := slot_injective hh (i := 0 + i) (j := s.cnt p) (by omega) (by omega) h
        omega)]
  · show ((s.pushLast p c).pool ((s.pushLast p c).slot p (0 + s.cnt p))).toList
        ++ [] = [c]
    rw [List.append_nil, pushLast_slot, pushLast_pool, Nat.zero_add,
      if_pos hws.symm]
    rfl

theorem pushLast_proj_other {s : Pool} (hwf : WF s) {p q : PlaceId}
    (hp : p < s.nplaces) (hq : q < s.nplaces) (hne : q ≠ p) (c : Colour) :
    (s.pushLast p c).proj q = s.proj q := by
  have hws := write_slot_eq hwf hp
  unfold proj
  rw [pushLast_cnt_other s c hne]
  apply projFrom_eq_of
  intro i hi
  rw [pushLast_slot, pushLast_pool, if_neg (by
    rw [hws]
    exact Ne.symm (slot_ne_of_place_ne hwf hp hq (fun h => hne h.symm)
      (s.cnt p) (0 + i)))]

theorem addLast_wf {s : Pool} (hwf : WF s) {p : PlaceId} (hp : p < s.nplaces)
    (c : Colour) : WF (s.addLast p c) := by
  unfold addLast
  by_cases hfull : s.cnt p = s.cap p
  · rw [if_pos hfull]
    have hg := growRing_wf hwf hp
    apply pushLast_wf hg (by simpa using hp)
    rw [growRing_cnt, growRing_cap_self]
    have := hwf.cap_pos p hp
    have := hwf.cnt_le p hp
    omega
  · rw [if_neg hfull]
    exact pushLast_wf hwf hp (by
      have := hwf.cnt_le p hp
      omega) c

/-- RB5: `ring_add_last` appends at the FIFO tail — through the grow path
too, so growth never reorders or loses tokens. -/
theorem addLast_proj_self {s : Pool} (hwf : WF s) {p : PlaceId}
    (hp : p < s.nplaces) (c : Colour) :
    (s.addLast p c).proj p = s.proj p ++ [c] := by
  unfold addLast
  by_cases hfull : s.cnt p = s.cap p
  · rw [if_pos hfull]
    have hg := growRing_wf hwf hp
    rw [pushLast_proj_self hg (by simpa using hp)
      (by
        rw [growRing_cnt, growRing_cap_self]
        have := hwf.cap_pos p hp
        have := hwf.cnt_le p hp
        omega) c,
      growRing_proj_self hwf hp]
  · rw [if_neg hfull]
    exact pushLast_proj_self hwf hp (by
      have := hwf.cnt_le p hp
      omega) c

theorem addLast_proj_other {s : Pool} (hwf : WF s) {p q : PlaceId}
    (hp : p < s.nplaces) (hq : q < s.nplaces) (hne : q ≠ p) (c : Colour) :
    (s.addLast p c).proj q = s.proj q := by
  unfold addLast
  by_cases hfull : s.cnt p = s.cap p
  · rw [if_pos hfull]
    have hg := growRing_wf hwf hp
    rw [pushLast_proj_other hg (by simpa using hp) (by simpa using hq) hne c,
      growRing_proj_other hwf hp hq hne]
  · rw [if_neg hfull]
    exact pushLast_proj_other hwf hp hq hne c

end Pool

end Libpetri
