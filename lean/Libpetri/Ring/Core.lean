/-
# The flat token pool: state, invariants, projection, `ring_remove_first`

`Pool`, `Pool.WF` (RB1–RB3), slot geometry, the refinement map `proj` (RB4),
`removeFirst` and `peekFirst`, split out of `Ring.lean`.
-/
import Libpetri.Basic
import Libpetri.RingArith

namespace Libpetri

/-- The flat pool state. Field-for-field:
`pool` = `token_pool`, `len` = `token_pool.len()`, `offset` = `place_offset`,
`head` = `ring_head`, `tail` = `ring_tail`, `cnt` = `token_counts`,
`cap` = `ring_capacity`; `nplaces` bounds the meaningful place ids. -/
structure Pool where
  pool    : Nat → Option Colour
  len     : Nat
  offset  : PlaceId → Nat
  head    : PlaceId → Nat
  tail    : PlaceId → Nat
  cnt     : PlaceId → Nat
  cap     : PlaceId → Nat
  nplaces : Nat

namespace Pool

/-- Absolute pool index of the `i`-th oldest token of place `p`. -/
def slot (s : Pool) (p : PlaceId) (i : Nat) : Nat :=
  s.offset p + ringPos (s.head p) i (s.cap p)

/-- RB1–RB3: ring well-formedness, occupancy, and block disjointness.

* `cap_pos … in_bounds` — RB1: each ring is a genuine circular buffer whose
  cached `tail` equals `(head + cnt) % cap` and whose block fits in the pool.
* `occupied` / `free` — RB2: live positions hold `Some`, free positions of the
  *current* block hold `None`. This is what makes `ring_remove_first`'s
  `.take().unwrap()` (`precompiled_backend.rs:399`) total. Slots outside every
  current block (blocks leaked by `grow_ring_static`) are unconstrained.
* `disjoint` — RB3: current blocks of distinct places never overlap, so one
  place's writes cannot corrupt another's ring. -/
structure WF (s : Pool) : Prop where
  cap_pos   : ∀ p, p < s.nplaces → 0 < s.cap p
  cnt_le    : ∀ p, p < s.nplaces → s.cnt p ≤ s.cap p
  head_lt   : ∀ p, p < s.nplaces → s.head p < s.cap p
  tail_eq   : ∀ p, p < s.nplaces → s.tail p = ringPos (s.head p) (s.cnt p) (s.cap p)
  in_bounds : ∀ p, p < s.nplaces → s.offset p + s.cap p ≤ s.len
  occupied  : ∀ p, p < s.nplaces → ∀ i, i < s.cnt p → (s.pool (s.slot p i)).isSome
  free      : ∀ p, p < s.nplaces → ∀ i, s.cnt p ≤ i → i < s.cap p →
                s.pool (s.slot p i) = none
  disjoint  : ∀ p q, p < s.nplaces → q < s.nplaces → p ≠ q →
                s.offset p + s.cap p ≤ s.offset q ∨ s.offset q + s.cap q ≤ s.offset p

/-! ## Slot geometry -/

theorem slot_lt_block {s : Pool} {p : PlaceId} (hcap : 0 < s.cap p) (i : Nat) :
    s.slot p i < s.offset p + s.cap p :=
  Nat.add_lt_add_left (ringPos_lt _ _ hcap) _

theorem offset_le_slot (s : Pool) (p : PlaceId) (i : Nat) :
    s.offset p ≤ s.slot p i :=
  Nat.le_add_right _ _

theorem slot_injective {s : Pool} {p : PlaceId} (hh : s.head p < s.cap p)
    {i j : Nat} (hi : i < s.cap p) (hj : j < s.cap p)
    (h : s.slot p i = s.slot p j) : i = j :=
  ringPos_injective hh hi hj (Nat.add_left_cancel h)

/-- Recovering a slot's logical position (left inverse of `slot`). -/
theorem posInv_slot {s : Pool} {p : PlaceId} (hh : s.head p < s.cap p)
    {i : Nat} (hi : i < s.cap p) :
    ringPosInv (s.head p) (s.slot p i - s.offset p) (s.cap p) = i := by
  unfold slot
  rw [Nat.add_sub_cancel_left]
  exact ringPosInv_ringPos hh hi

/-- Slots of distinct places are distinct (RB3 consequence). -/
theorem slot_ne_of_place_ne {s : Pool} (hwf : WF s) {p q : PlaceId}
    (hp : p < s.nplaces) (hq : q < s.nplaces) (hne : p ≠ q) (i j : Nat) :
    s.slot p i ≠ s.slot q j := by
  have hcp := hwf.cap_pos p hp
  have hcq := hwf.cap_pos q hq
  have h1 := slot_lt_block hcp i
  have h2 := slot_lt_block hcq j
  have h3 := offset_le_slot s p i
  have h4 := offset_le_slot s q j
  rcases hwf.disjoint p q hp hq hne with h | h <;> omega

/-- Position `cap` wraps back to position `0`. -/
theorem slot_cap_eq_slot_zero {s : Pool} {p : PlaceId} (hh : s.head p < s.cap p) :
    s.slot p (s.cap p) = s.slot p 0 := by
  unfold slot ringPos
  rw [Nat.add_mod_right, Nat.add_zero, Nat.mod_eq_of_lt hh]

/-! ## The refinement map (RB4)

`projFrom p start n` reads positions `start, …, start + n - 1`; `proj p` is
the whole FIFO queue and is exactly what `materialize_marking`
(`precompiled_backend.rs`) emits for place `p`. -/

def projFrom (s : Pool) (p : PlaceId) (start : Nat) : Nat → List Colour
  | 0 => []
  | n + 1 => (s.pool (s.slot p start)).toList ++ s.projFrom p (start + 1) n

/-- RB4: the abstraction of one place's ring to its `CMarking` FIFO list. -/
def proj (s : Pool) (p : PlaceId) : List Colour :=
  s.projFrom p 0 (s.cnt p)

/-- Two (pool, place) views project identically when they agree slot-wise
under a position shift. The workhorse congruence for every operation proof. -/
theorem projFrom_eq_of {s t : Pool} {p q : PlaceId} {a b n : Nat}
    (h : ∀ i, i < n → t.pool (t.slot q (b + i)) = s.pool (s.slot p (a + i))) :
    t.projFrom q b n = s.projFrom p a n := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    simp only [projFrom]
    have h0 := h 0 (Nat.succ_pos n)
    simp only [Nat.add_zero] at h0
    rw [h0, ih (fun i hi => by
      have := h (i + 1) (by omega)
      rw [show b + (i + 1) = b + 1 + i by omega, show a + (i + 1) = a + 1 + i by omega] at this
      exact this)]

theorem projFrom_append (s : Pool) (p : PlaceId) (start m n : Nat) :
    s.projFrom p start (m + n) = s.projFrom p start m ++ s.projFrom p (start + m) n := by
  induction m generalizing start with
  | zero => simp [projFrom]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega]
    simp only [projFrom]
    rw [ih (start + 1), List.append_assoc,
      show start + 1 + m = start + (m + 1) by omega]

/-- One occupied cell projects as a singleton. -/
theorem toList_of_isSome {o : Option Colour} (h : o.isSome) :
    ∃ c, o = some c ∧ o.toList = [c] := by
  cases o with
  | none => simp at h
  | some c => exact ⟨c, rfl, rfl⟩

theorem projFrom_length {s : Pool} {p : PlaceId} {start n : Nat}
    (h : ∀ i, i < n → (s.pool (s.slot p (start + i))).isSome) :
    (s.projFrom p start n).length = n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    have h0 := h 0 (Nat.succ_pos n)
    simp only [Nat.add_zero] at h0
    obtain ⟨c, hc, hcl⟩ := toList_of_isSome h0
    simp only [projFrom, List.length_append, hcl]
    rw [ih (fun i hi => by
      have := h (i + 1) (by omega)
      rw [show start + (i + 1) = start + 1 + i by omega] at this
      exact this)]
    simp only [List.length_cons, List.length_nil]
    omega

theorem proj_length {s : Pool} (hwf : WF s) {p : PlaceId} (hp : p < s.nplaces) :
    (s.proj p).length = s.cnt p :=
  projFrom_length (fun i hi => by
    have := hwf.occupied p hp i hi
    simpa using this)

/-! ## `ring_remove_first` (`precompiled_backend.rs:396-403`)

`take()` the head slot (the returned token is `first`), advance the head,
decrement the count. -/

/-- The token `ring_remove_first` returns: the head slot's content. -/
def first (s : Pool) (p : PlaceId) : Option Colour := s.pool (s.slot p 0)

def removeFirst (s : Pool) (p : PlaceId) : Pool :=
  { s with
    pool := fun idx => if idx = s.slot p 0 then none else s.pool idx
    head := fun q => if q = p then (s.head q + 1) % s.cap q else s.head q
    cnt  := fun q => if q = p then s.cnt q - 1 else s.cnt q }

@[simp] theorem removeFirst_pool (s : Pool) (p : PlaceId) (idx : Nat) :
    (s.removeFirst p).pool idx = if idx = s.slot p 0 then none else s.pool idx := rfl
@[simp] theorem removeFirst_cap (s : Pool) (p : PlaceId) :
    (s.removeFirst p).cap = s.cap := rfl
@[simp] theorem removeFirst_offset (s : Pool) (p : PlaceId) :
    (s.removeFirst p).offset = s.offset := rfl
@[simp] theorem removeFirst_tail (s : Pool) (p : PlaceId) :
    (s.removeFirst p).tail = s.tail := rfl
@[simp] theorem removeFirst_len (s : Pool) (p : PlaceId) :
    (s.removeFirst p).len = s.len := rfl
@[simp] theorem removeFirst_nplaces (s : Pool) (p : PlaceId) :
    (s.removeFirst p).nplaces = s.nplaces := rfl
@[simp] theorem removeFirst_cnt_self (s : Pool) (p : PlaceId) :
    (s.removeFirst p).cnt p = s.cnt p - 1 := by simp [removeFirst]
theorem removeFirst_cnt_other (s : Pool) {p q : PlaceId} (hne : q ≠ p) :
    (s.removeFirst p).cnt q = s.cnt q := by simp [removeFirst, hne]
@[simp] theorem removeFirst_head_self (s : Pool) (p : PlaceId) :
    (s.removeFirst p).head p = (s.head p + 1) % s.cap p := by simp [removeFirst]
theorem removeFirst_head_other (s : Pool) {p q : PlaceId} (hne : q ≠ p) :
    (s.removeFirst p).head q = s.head q := by simp [removeFirst, hne]

/-- After the head advance, position `i` addresses the slot that held
position `i + 1`. -/
theorem removeFirst_slot (s : Pool) (p : PlaceId) (i : Nat) :
    (s.removeFirst p).slot p i = s.slot p (i + 1) := by
  unfold slot
  rw [removeFirst_offset, removeFirst_cap, removeFirst_head_self, ringPos_succ_head]

theorem removeFirst_slot_other (s : Pool) {p q : PlaceId} (hne : q ≠ p) (i : Nat) :
    (s.removeFirst p).slot q i = s.slot q i := by
  unfold slot
  rw [removeFirst_offset, removeFirst_cap, removeFirst_head_other s hne]

/-- Totality of the `.unwrap()` at `precompiled_backend.rs:399`: under RB2 a
non-empty ring's head slot is `Some`. -/
theorem first_isSome {s : Pool} (hwf : WF s) {p : PlaceId} (hp : p < s.nplaces)
    (hcnt : 0 < s.cnt p) : (s.first p).isSome :=
  hwf.occupied p hp 0 hcnt

/-- `first` is the head of the projected FIFO queue. -/
theorem first_eq_head {s : Pool} (hwf : WF s) {p : PlaceId} (hp : p < s.nplaces)
    (hcnt : 0 < s.cnt p) : s.first p = (s.proj p).head? := by
  unfold proj first
  obtain ⟨n, hn⟩ : ∃ n, s.cnt p = n + 1 := ⟨s.cnt p - 1, by omega⟩
  rw [hn]
  simp only [projFrom]
  obtain ⟨c, hc, _⟩ := toList_of_isSome (hwf.occupied p hp 0 hcnt)
  rw [hc]
  simp

theorem removeFirst_wf {s : Pool} (hwf : WF s) {p : PlaceId} (hp : p < s.nplaces)
    (hcnt : 0 < s.cnt p) : WF (s.removeFirst p) := by
  have hh := hwf.head_lt p hp
  have hcap := hwf.cap_pos p hp
  have hle := hwf.cnt_le p hp
  constructor
  · intro q hq
    rw [removeFirst_nplaces] at hq
    rw [removeFirst_cap]
    exact hwf.cap_pos q hq
  · intro q hq
    rw [removeFirst_nplaces] at hq
    rw [removeFirst_cap]
    by_cases hne : q = p
    · subst hne
      rw [removeFirst_cnt_self]
      exact Nat.le_trans (Nat.sub_le _ _) (hwf.cnt_le q hq)
    · rw [removeFirst_cnt_other s hne]
      exact hwf.cnt_le q hq
  · intro q hq
    rw [removeFirst_nplaces] at hq
    rw [removeFirst_cap]
    by_cases hne : q = p
    · subst hne
      rw [removeFirst_head_self]
      exact Nat.mod_lt _ (hwf.cap_pos q hq)
    · rw [removeFirst_head_other s hne]
      exact hwf.head_lt q hq
  · intro q hq
    rw [removeFirst_nplaces] at hq
    rw [removeFirst_tail, removeFirst_cap]
    by_cases hne : q = p
    · subst hne
      rw [removeFirst_head_self, removeFirst_cnt_self, ringPos_succ_head,
        show s.cnt q - 1 + 1 = s.cnt q by omega]
      exact hwf.tail_eq q hq
    · rw [removeFirst_head_other s hne, removeFirst_cnt_other s hne]
      exact hwf.tail_eq q hq
  · intro q hq
    rw [removeFirst_nplaces] at hq
    rw [removeFirst_offset, removeFirst_cap, removeFirst_len]
    exact hwf.in_bounds q hq
  · intro q hq i hi
    rw [removeFirst_nplaces] at hq
    by_cases hne : q = p
    · subst hne
      rw [removeFirst_cnt_self] at hi
      rw [removeFirst_slot, removeFirst_pool, if_neg (fun h => by
        have := slot_injective hh (i := i + 1) (j := 0) (by omega) (by omega) h
        omega)]
      exact hwf.occupied q hq (i + 1) (by omega)
    · rw [removeFirst_cnt_other s hne] at hi
      rw [removeFirst_slot_other s hne, removeFirst_pool,
        if_neg (Ne.symm (slot_ne_of_place_ne hwf hp hq (Ne.symm hne) 0 i))]
      exact hwf.occupied q hq i hi
  · intro q hq i hlo hhi
    rw [removeFirst_nplaces] at hq
    by_cases hne : q = p
    · subst hne
      rw [removeFirst_cnt_self] at hlo
      rw [removeFirst_cap] at hhi
      rw [removeFirst_slot, removeFirst_pool]
      by_cases hwrap : i + 1 = s.cap q
      · rw [if_pos (by rw [hwrap]; exact slot_cap_eq_slot_zero hh)]
      · rw [if_neg (fun h => by
          have := slot_injective hh (i := i + 1) (j := 0) (by omega) (by omega) h
          omega)]
        exact hwf.free q hq (i + 1) (by omega) (by omega)
    · rw [removeFirst_cnt_other s hne] at hlo
      rw [removeFirst_cap] at hhi
      rw [removeFirst_slot_other s hne, removeFirst_pool,
        if_neg (Ne.symm (slot_ne_of_place_ne hwf hp hq (Ne.symm hne) 0 i))]
      exact hwf.free q hq i hlo hhi
  · intro q r hq hr hne
    rw [removeFirst_nplaces] at hq hr
    rw [removeFirst_offset, removeFirst_cap]
    exact hwf.disjoint q r hq hr hne

/-- Effect on the removed place: the projection drops its head (FIFO pop). -/
theorem removeFirst_proj_self {s : Pool} (hwf : WF s) {p : PlaceId}
    (hp : p < s.nplaces) (hcnt : 0 < s.cnt p) :
    (s.removeFirst p).proj p = (s.proj p).tail := by
  have hh := hwf.head_lt p hp
  have hle := hwf.cnt_le p hp
  unfold proj
  obtain ⟨n, hn⟩ : ∃ n, s.cnt p = n + 1 := ⟨s.cnt p - 1, by omega⟩
  rw [removeFirst_cnt_self, hn, Nat.add_sub_cancel]
  simp only [projFrom]
  obtain ⟨c, hc, hcl⟩ := toList_of_isSome (hwf.occupied p hp 0 hcnt)
  rw [hcl, List.singleton_append, List.tail_cons]
  apply projFrom_eq_of
  intro i hi
  rw [Nat.zero_add, removeFirst_slot, removeFirst_pool, if_neg (fun h => by
    have := slot_injective hh (i := i + 1) (j := 0) (by omega) (by omega) h
    omega), show (1 : Nat) + i = i + 1 by omega]

/-- Frame: other places' projections are untouched. -/
theorem removeFirst_proj_other {s : Pool} (hwf : WF s) {p q : PlaceId}
    (hp : p < s.nplaces) (hq : q < s.nplaces) (hne : q ≠ p) :
    (s.removeFirst p).proj q = s.proj q := by
  unfold proj
  rw [removeFirst_cnt_other s hne]
  apply projFrom_eq_of
  intro i hi
  rw [removeFirst_slot_other s hne, removeFirst_pool,
    if_neg (Ne.symm (slot_ne_of_place_ne hwf hp hq (Ne.symm hne) 0 (0 + i)))]

/-! ## `ring_peek_first` (`precompiled_backend.rs:426-431`) -/

def peekFirst (s : Pool) (p : PlaceId) : Option Colour :=
  if s.cnt p = 0 then none else s.pool (s.slot p 0)

/-- FR3's storage half: peeking is exactly `head?` of the projection and, by
definition, mutates nothing. -/
theorem peekFirst_eq_head {s : Pool} (hwf : WF s) {p : PlaceId} (hp : p < s.nplaces) :
    s.peekFirst p = (s.proj p).head? := by
  unfold peekFirst
  by_cases hcnt : s.cnt p = 0
  · rw [if_pos hcnt]
    unfold proj
    rw [hcnt]
    rfl
  · rw [if_neg hcnt]
    exact first_eq_head hwf hp (by omega)

/-! ## `ring_remove_matching`'s scan (definitions; the lemmas and the
compactions are in `Ring/Match.lean`). Kept in this module so the scan's
structural match shares the matcher it had when `Ring.lean` was one file. -/

/-- Position `i` holds a token satisfying `pred`. -/
def matchesAt (s : Pool) (p : PlaceId) (pred : Colour → Bool) (i : Nat) : Bool :=
  match s.pool (s.slot p i) with
  | some c => pred c
  | none => false

/-- The forward scan of `ring_remove_matching`'s `for i in 0..count`. -/
def findMatchFrom (s : Pool) (p : PlaceId) (pred : Colour → Bool)
    (start : Nat) : Nat → Option Nat
  | 0 => none
  | n + 1 =>
    if s.matchesAt p pred start then some start
    else s.findMatchFrom p pred (start + 1) n

def findMatch (s : Pool) (p : PlaceId) (pred : Colour → Bool) : Option Nat :=
  s.findMatchFrom p pred 0 (s.cnt p)

end Pool

end Libpetri
