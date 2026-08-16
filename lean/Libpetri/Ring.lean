/-
# The flat token pool of `PrecompiledBackend`, at full fidelity

Models the ring-buffer token storage of
`rust/libpetri-runtime/src/precompiled_backend.rs`: one flat pool
(`token_pool: Vec<Option<ErasedToken>>`) holding every place's ring as a block
at `place_offset[pid]`, with per-place `ring_head` / `ring_tail` /
`ring_capacity` / `token_counts`. The *i*-th oldest token of place `p` lives at

    token_pool[place_offset[p] + (ring_head[p] + i) % ring_capacity[p]]

Colours stand in for `ErasedToken` (as everywhere in this development — only
guard-observable equality matters), and the pool is a total function
`Nat → Option Colour` (a flat array *is* its index function; `len` carries the
`Vec` length for the bounds invariant RB1).

The invariant bundle `Pool.WF` is RB1–RB3 of the plan; `Pool.proj` is the
refinement map RB4 onto `CMarking` (`Basic.lean`), and the operation lemmas
are RB5 (`addLast`/grow preserve FIFO) and the frame/effect specs each later
file builds on. `ring_remove_matching` (RB6) lives here too, with both
compaction directions.
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
  `.take().unwrap()` (`precompiled_backend.rs:307`) total. Slots outside every
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

/-! ## `ring_remove_first` (`precompiled_backend.rs:304-311`)

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

/-- Totality of the `.unwrap()` at `precompiled_backend.rs:307`: under RB2 a
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

/-! ## `ring_peek_first` (`precompiled_backend.rs:333-339`) -/

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

/-! ## `grow_ring_static` (`precompiled_backend.rs:1174-1201`)

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

/-! ## `ring_add_last` (`precompiled_backend.rs:313-331`)

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

/-! ## `ring_remove_matching` (`precompiled_backend.rs:367-419`)

The ν-net matched consume: scan positions from the head for the first token
satisfying `pred`, `take()` it, then close the gap from whichever end is
nearer — slide the preceding tokens forward and advance the head
(`headSlideAt`, chosen when `i ≤ cnt - 1 - i`), or slide the trailing tokens
back and retract the tail (`tailSlideAt`). RB6: exactly the first match is
removed and the survivors keep their order, whichever direction compacts. -/

/-- Position `i` holds a token satisfying `pred`. -/
def matchesAt (s : Pool) (p : PlaceId) (pred : Colour → Bool) (i : Nat) : Bool :=
  match s.pool (s.slot p i) with
  | some c => pred c
  | none => false

theorem matchesAt_true {s : Pool} {p : PlaceId} {pred : Colour → Bool} {i : Nat}
    (h : s.matchesAt p pred i = true) :
    ∃ c, s.pool (s.slot p i) = some c ∧ pred c = true := by
  unfold matchesAt at h
  cases hp : s.pool (s.slot p i) with
  | none => rw [hp] at h; simp at h
  | some c => rw [hp] at h; exact ⟨c, rfl, h⟩

/-- The forward scan of `ring_remove_matching`'s `for i in 0..count`. -/
def findMatchFrom (s : Pool) (p : PlaceId) (pred : Colour → Bool)
    (start : Nat) : Nat → Option Nat
  | 0 => none
  | n + 1 =>
    if s.matchesAt p pred start then some start
    else s.findMatchFrom p pred (start + 1) n

def findMatch (s : Pool) (p : PlaceId) (pred : Colour → Bool) : Option Nat :=
  s.findMatchFrom p pred 0 (s.cnt p)

theorem findMatchFrom_some {s : Pool} {p : PlaceId} {pred : Colour → Bool}
    {start n i : Nat} (h : s.findMatchFrom p pred start n = some i) :
    start ≤ i ∧ i < start + n ∧ s.matchesAt p pred i = true ∧
      ∀ j, start ≤ j → j < i → s.matchesAt p pred j = false := by
  induction n generalizing start with
  | zero => exact absurd h (by simp [findMatchFrom])
  | succ n ih =>
    unfold findMatchFrom at h
    by_cases hm : s.matchesAt p pred start = true
    · rw [if_pos hm] at h
      cases h
      exact ⟨Nat.le_refl _, by omega, hm, fun j h1 h2 => by omega⟩
    · rw [if_neg hm] at h
      obtain ⟨h1, h2, h3, h4⟩ := ih h
      refine ⟨by omega, by omega, h3, fun j hj1 hj2 => ?_⟩
      by_cases hjs : j = start
      · subst hjs
        cases hb : s.matchesAt p pred j with
        | false => rfl
        | true => exact absurd hb hm
      · exact h4 j (by omega) hj2

theorem findMatchFrom_none {s : Pool} {p : PlaceId} {pred : Colour → Bool}
    {start n : Nat} (h : s.findMatchFrom p pred start n = none) :
    ∀ j, start ≤ j → j < start + n → s.matchesAt p pred j = false := by
  induction n generalizing start with
  | zero => intro j h1 h2; omega
  | succ n ih =>
    unfold findMatchFrom at h
    by_cases hm : s.matchesAt p pred start = true
    · rw [if_pos hm] at h; cases h
    · rw [if_neg hm] at h
      intro j h1 h2
      by_cases hjs : j = start
      · subst hjs
        cases hb : s.matchesAt p pred j with
        | false => rfl
        | true => exact absurd hb hm
      · exact ih h j (by omega) (by omega)

/-- Every projected token comes from a live slot. -/
theorem mem_projFrom {s : Pool} {p : PlaceId} {start n : Nat} {c : Colour}
    (h : c ∈ s.projFrom p start n) :
    ∃ j, j < n ∧ s.pool (s.slot p (start + j)) = some c := by
  induction n generalizing start with
  | zero => exact absurd h (by simp [projFrom])
  | succ n ih =>
    unfold projFrom at h
    rcases List.mem_append.mp h with h | h
    · refine ⟨0, Nat.succ_pos n, ?_⟩
      rw [Nat.add_zero]
      cases hp : s.pool (s.slot p start) with
      | none => rw [hp] at h; simp at h
      | some c' => rw [hp] at h; simp at h; rw [h]
    · obtain ⟨j, hj, hc⟩ := ih h
      exact ⟨j + 1, by omega, by rw [show start + (j + 1) = start + 1 + j by omega]; exact hc⟩

/-- Decompose the projection around a live position `i`. -/
theorem proj_split {s : Pool} (_hwf : WF s) {p : PlaceId} (_hp : p < s.nplaces)
    {i : Nat} (hi : i < s.cnt p) {c : Colour}
    (hc : s.pool (s.slot p i) = some c) :
    s.proj p = s.projFrom p 0 i ++ c :: s.projFrom p (i + 1) (s.cnt p - 1 - i) := by
  unfold proj
  obtain ⟨k, hk⟩ : ∃ k, s.cnt p - 1 - i = k := ⟨_, rfl⟩
  rw [hk, show s.cnt p = i + (1 + k) by omega, projFrom_append s p 0 i,
    Nat.zero_add, projFrom_append s p i 1]
  congr 1
  simp only [projFrom, hc, Option.toList, List.append_nil, List.cons_append,
    List.nil_append]

/-! ### The head-side compaction (`precompiled_backend.rs:391-399`) -/

def headSlideAt (s : Pool) (p : PlaceId) (i : Nat) : Pool :=
  { s with
    pool := fun idx =>
      if s.offset p ≤ idx ∧ idx < s.offset p + s.cap p then
        let k := ringPosInv (s.head p) (idx - s.offset p) (s.cap p)
        if k = 0 then none
        else if k ≤ i then s.pool (s.slot p (k - 1))
        else s.pool idx
      else s.pool idx
    head := fun q => if q = p then (s.head q + 1) % s.cap q else s.head q
    cnt  := fun q => if q = p then s.cnt q - 1 else s.cnt q }

@[simp] theorem headSlideAt_cap (s : Pool) (p : PlaceId) (i : Nat) :
    (s.headSlideAt p i).cap = s.cap := rfl
@[simp] theorem headSlideAt_offset (s : Pool) (p : PlaceId) (i : Nat) :
    (s.headSlideAt p i).offset = s.offset := rfl
@[simp] theorem headSlideAt_tail (s : Pool) (p : PlaceId) (i : Nat) :
    (s.headSlideAt p i).tail = s.tail := rfl
@[simp] theorem headSlideAt_len (s : Pool) (p : PlaceId) (i : Nat) :
    (s.headSlideAt p i).len = s.len := rfl
@[simp] theorem headSlideAt_nplaces (s : Pool) (p : PlaceId) (i : Nat) :
    (s.headSlideAt p i).nplaces = s.nplaces := rfl
@[simp] theorem headSlideAt_cnt_self (s : Pool) (p : PlaceId) (i : Nat) :
    (s.headSlideAt p i).cnt p = s.cnt p - 1 := by simp [headSlideAt]
theorem headSlideAt_cnt_other (s : Pool) {p q : PlaceId} (i : Nat) (hne : q ≠ p) :
    (s.headSlideAt p i).cnt q = s.cnt q := by simp [headSlideAt, hne]
@[simp] theorem headSlideAt_head_self (s : Pool) (p : PlaceId) (i : Nat) :
    (s.headSlideAt p i).head p = (s.head p + 1) % s.cap p := by simp [headSlideAt]
theorem headSlideAt_head_other (s : Pool) {p q : PlaceId} (i : Nat) (hne : q ≠ p) :
    (s.headSlideAt p i).head q = s.head q := by simp [headSlideAt, hne]

theorem headSlideAt_slot (s : Pool) (p : PlaceId) (i j : Nat) :
    (s.headSlideAt p i).slot p j = s.slot p (j + 1) := by
  unfold slot
  rw [headSlideAt_offset, headSlideAt_cap, headSlideAt_head_self, ringPos_succ_head]

theorem headSlideAt_slot_other (s : Pool) {p q : PlaceId} (i : Nat) (hne : q ≠ p)
    (j : Nat) : (s.headSlideAt p i).slot q j = s.slot q j := by
  unfold slot
  rw [headSlideAt_offset, headSlideAt_cap, headSlideAt_head_other s i hne]

/-- Evaluate the slide at a slot of `p` by its logical position. -/
theorem headSlideAt_pool_at {s : Pool} (hwf : WF s) {p : PlaceId}
    (hp : p < s.nplaces) (i : Nat) {j : Nat} (hj : j < s.cap p) :
    (s.headSlideAt p i).pool (s.slot p j)
      = if j = 0 then none
        else if j ≤ i then s.pool (s.slot p (j - 1))
        else s.pool (s.slot p j) := by
  have hcap := hwf.cap_pos p hp
  have hh := hwf.head_lt p hp
  show (if s.offset p ≤ s.slot p j ∧ s.slot p j < s.offset p + s.cap p then _
    else _) = _
  rw [if_pos ⟨offset_le_slot s p j, slot_lt_block hcap j⟩]
  simp only [posInv_slot hh hj]

theorem headSlideAt_pool_other {s : Pool} (hwf : WF s) {p q : PlaceId}
    (hp : p < s.nplaces) (hq : q < s.nplaces) (hne : q ≠ p) (i j : Nat) :
    (s.headSlideAt p i).pool (s.slot q j) = s.pool (s.slot q j) := by
  have hcq := hwf.cap_pos q hq
  show (if s.offset p ≤ s.slot q j ∧ s.slot q j < s.offset p + s.cap p then _
    else _) = _
  rw [if_neg (by
    have h1 := slot_lt_block hcq j
    have h2 := offset_le_slot s q j
    rcases hwf.disjoint p q hp hq (fun h => hne h.symm) with h | h <;> omega)]

theorem headSlideAt_wf {s : Pool} (hwf : WF s) {p : PlaceId} (hp : p < s.nplaces)
    {i : Nat} (hi : i < s.cnt p) : WF (s.headSlideAt p i) := by
  have hh := hwf.head_lt p hp
  have hcap := hwf.cap_pos p hp
  have hle := hwf.cnt_le p hp
  constructor
  · intro q hq
    rw [headSlideAt_nplaces] at hq
    rw [headSlideAt_cap]
    exact hwf.cap_pos q hq
  · intro q hq
    rw [headSlideAt_nplaces] at hq
    rw [headSlideAt_cap]
    by_cases hne : q = p
    · subst hne
      rw [headSlideAt_cnt_self]
      have := hwf.cnt_le q hq
      omega
    · rw [headSlideAt_cnt_other s i hne]
      exact hwf.cnt_le q hq
  · intro q hq
    rw [headSlideAt_nplaces] at hq
    rw [headSlideAt_cap]
    by_cases hne : q = p
    · subst hne
      rw [headSlideAt_head_self]
      exact Nat.mod_lt _ (hwf.cap_pos q hq)
    · rw [headSlideAt_head_other s i hne]
      exact hwf.head_lt q hq
  · intro q hq
    rw [headSlideAt_nplaces] at hq
    rw [headSlideAt_tail, headSlideAt_cap]
    by_cases hne : q = p
    · subst hne
      rw [headSlideAt_head_self, headSlideAt_cnt_self, ringPos_succ_head,
        show s.cnt q - 1 + 1 = s.cnt q by omega]
      exact hwf.tail_eq q hq
    · rw [headSlideAt_head_other s i hne, headSlideAt_cnt_other s i hne]
      exact hwf.tail_eq q hq
  · intro q hq
    rw [headSlideAt_nplaces] at hq
    rw [headSlideAt_offset, headSlideAt_cap, headSlideAt_len]
    exact hwf.in_bounds q hq
  · intro q hq m hm
    rw [headSlideAt_nplaces] at hq
    by_cases hne : q = p
    · subst hne
      rw [headSlideAt_cnt_self] at hm
      rw [headSlideAt_slot, headSlideAt_pool_at hwf hq i (by omega),
        if_neg (by omega)]
      by_cases hmi : m + 1 ≤ i
      · rw [if_pos hmi, Nat.add_sub_cancel]
        exact hwf.occupied q hq m (by omega)
      · rw [if_neg hmi]
        exact hwf.occupied q hq (m + 1) (by omega)
    · rw [headSlideAt_cnt_other s i hne] at hm
      rw [headSlideAt_slot_other s i hne,
        headSlideAt_pool_other hwf hp hq hne i m]
      exact hwf.occupied q hq m hm
  · intro q hq m hlo hhi
    rw [headSlideAt_nplaces] at hq
    by_cases hne : q = p
    · subst hne
      rw [headSlideAt_cnt_self] at hlo
      rw [headSlideAt_cap] at hhi
      rw [headSlideAt_slot]
      by_cases hwrap : m + 1 = s.cap q
      · rw [hwrap, slot_cap_eq_slot_zero hh,
          headSlideAt_pool_at hwf hq i (by omega), if_pos rfl]
      · rw [headSlideAt_pool_at hwf hq i (by omega), if_neg (by omega),
          if_neg (by omega)]
        exact hwf.free q hq (m + 1) (by omega) (by omega)
    · rw [headSlideAt_cnt_other s i hne] at hlo
      rw [headSlideAt_cap] at hhi
      rw [headSlideAt_slot_other s i hne,
        headSlideAt_pool_other hwf hp hq hne i m]
      exact hwf.free q hq m hlo hhi
  · intro q r hq hr hqr
    rw [headSlideAt_nplaces] at hq hr
    rw [headSlideAt_offset, headSlideAt_cap]
    exact hwf.disjoint q r hq hr hqr

theorem headSlideAt_proj_self {s : Pool} (hwf : WF s) {p : PlaceId}
    (hp : p < s.nplaces) {i : Nat} (hi : i < s.cnt p) :
    (s.headSlideAt p i).proj p
      = s.projFrom p 0 i ++ s.projFrom p (i + 1) (s.cnt p - 1 - i) := by
  have hh := hwf.head_lt p hp
  have hle := hwf.cnt_le p hp
  unfold proj
  obtain ⟨k, hk⟩ : ∃ k, s.cnt p - 1 - i = k := ⟨_, rfl⟩
  rw [headSlideAt_cnt_self, hk, show s.cnt p - 1 = i + k by omega,
    projFrom_append _ p 0 i, Nat.zero_add]
  congr 1
  · apply projFrom_eq_of
    intro m hm
    rw [headSlideAt_slot, headSlideAt_pool_at hwf hp i (by omega),
      if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel]
  · apply projFrom_eq_of
    intro m hm
    rw [headSlideAt_slot, headSlideAt_pool_at hwf hp i (by omega),
      if_neg (by omega), if_neg (by omega),
      show i + m + 1 = i + 1 + m by omega]

theorem headSlideAt_proj_other {s : Pool} (hwf : WF s) {p q : PlaceId}
    (hp : p < s.nplaces) (hq : q < s.nplaces) (hne : q ≠ p) (i : Nat) :
    (s.headSlideAt p i).proj q = s.proj q := by
  unfold proj
  rw [headSlideAt_cnt_other s i hne]
  apply projFrom_eq_of
  intro m hm
  rw [headSlideAt_slot_other s i hne,
    headSlideAt_pool_other hwf hp hq hne i (0 + m)]

/-! ### The tail-side compaction (`precompiled_backend.rs:400-413`) -/

def tailSlideAt (s : Pool) (p : PlaceId) (i : Nat) : Pool :=
  { s with
    pool := fun idx =>
      if s.offset p ≤ idx ∧ idx < s.offset p + s.cap p then
        let k := ringPosInv (s.head p) (idx - s.offset p) (s.cap p)
        if i ≤ k ∧ k < s.cnt p - 1 then s.pool (s.slot p (k + 1))
        else if k = s.cnt p - 1 then none
        else s.pool idx
      else s.pool idx
    tail := fun q =>
      if q = p then (if s.tail q = 0 then s.cap q - 1 else s.tail q - 1)
      else s.tail q
    cnt  := fun q => if q = p then s.cnt q - 1 else s.cnt q }

@[simp] theorem tailSlideAt_cap (s : Pool) (p : PlaceId) (i : Nat) :
    (s.tailSlideAt p i).cap = s.cap := rfl
@[simp] theorem tailSlideAt_offset (s : Pool) (p : PlaceId) (i : Nat) :
    (s.tailSlideAt p i).offset = s.offset := rfl
@[simp] theorem tailSlideAt_head (s : Pool) (p : PlaceId) (i : Nat) :
    (s.tailSlideAt p i).head = s.head := rfl
@[simp] theorem tailSlideAt_len (s : Pool) (p : PlaceId) (i : Nat) :
    (s.tailSlideAt p i).len = s.len := rfl
@[simp] theorem tailSlideAt_nplaces (s : Pool) (p : PlaceId) (i : Nat) :
    (s.tailSlideAt p i).nplaces = s.nplaces := rfl
@[simp] theorem tailSlideAt_slot (s : Pool) (p : PlaceId) (i : Nat)
    (q : PlaceId) (j : Nat) : (s.tailSlideAt p i).slot q j = s.slot q j := rfl
@[simp] theorem tailSlideAt_cnt_self (s : Pool) (p : PlaceId) (i : Nat) :
    (s.tailSlideAt p i).cnt p = s.cnt p - 1 := by simp [tailSlideAt]
theorem tailSlideAt_cnt_other (s : Pool) {p q : PlaceId} (i : Nat) (hne : q ≠ p) :
    (s.tailSlideAt p i).cnt q = s.cnt q := by simp [tailSlideAt, hne]
@[simp] theorem tailSlideAt_tail_self (s : Pool) (p : PlaceId) (i : Nat) :
    (s.tailSlideAt p i).tail p
      = (if s.tail p = 0 then s.cap p - 1 else s.tail p - 1) := by
  simp [tailSlideAt]
theorem tailSlideAt_tail_other (s : Pool) {p q : PlaceId} (i : Nat) (hne : q ≠ p) :
    (s.tailSlideAt p i).tail q = s.tail q := by simp [tailSlideAt, hne]

theorem tailSlideAt_pool_at {s : Pool} (hwf : WF s) {p : PlaceId}
    (hp : p < s.nplaces) (i : Nat) {j : Nat} (hj : j < s.cap p) :
    (s.tailSlideAt p i).pool (s.slot p j)
      = if i ≤ j ∧ j < s.cnt p - 1 then s.pool (s.slot p (j + 1))
        else if j = s.cnt p - 1 then none
        else s.pool (s.slot p j) := by
  have hcap := hwf.cap_pos p hp
  have hh := hwf.head_lt p hp
  show (if s.offset p ≤ s.slot p j ∧ s.slot p j < s.offset p + s.cap p then _
    else _) = _
  rw [if_pos ⟨offset_le_slot s p j, slot_lt_block hcap j⟩]
  simp only [posInv_slot hh hj]

theorem tailSlideAt_pool_other {s : Pool} (hwf : WF s) {p q : PlaceId}
    (hp : p < s.nplaces) (hq : q < s.nplaces) (hne : q ≠ p) (i j : Nat) :
    (s.tailSlideAt p i).pool (s.slot q j) = s.pool (s.slot q j) := by
  have hcq := hwf.cap_pos q hq
  show (if s.offset p ≤ s.slot q j ∧ s.slot q j < s.offset p + s.cap p then _
    else _) = _
  rw [if_neg (by
    have h1 := slot_lt_block hcq j
    have h2 := offset_le_slot s q j
    rcases hwf.disjoint p q hp hq (fun h => hne h.symm) with h | h <;> omega)]

theorem tailSlideAt_wf {s : Pool} (hwf : WF s) {p : PlaceId} (hp : p < s.nplaces)
    {i : Nat} (hi : i < s.cnt p) : WF (s.tailSlideAt p i) := by
  have hh := hwf.head_lt p hp
  have hcap := hwf.cap_pos p hp
  have hle := hwf.cnt_le p hp
  have htl : s.tail p < s.cap p := by
    rw [hwf.tail_eq p hp]
    exact ringPos_lt _ _ hcap
  constructor
  · intro q hq
    rw [tailSlideAt_nplaces] at hq
    rw [tailSlideAt_cap]
    exact hwf.cap_pos q hq
  · intro q hq
    rw [tailSlideAt_nplaces] at hq
    rw [tailSlideAt_cap]
    by_cases hne : q = p
    · subst hne
      rw [tailSlideAt_cnt_self]
      have := hwf.cnt_le q hq
      omega
    · rw [tailSlideAt_cnt_other s i hne]
      exact hwf.cnt_le q hq
  · intro q hq
    rw [tailSlideAt_nplaces] at hq
    rw [tailSlideAt_cap, tailSlideAt_head]
    exact hwf.head_lt q hq
  · intro q hq
    rw [tailSlideAt_nplaces] at hq
    rw [tailSlideAt_cap, tailSlideAt_head]
    by_cases hne : q = p
    · subst hne
      rw [tailSlideAt_tail_self, tailSlideAt_cnt_self,
        pred_ring (hwf.cap_pos q hq) htl, hwf.tail_eq q hq,
        ringPos_pred (hwf.cap_pos q hq) (by omega)]
    · rw [tailSlideAt_tail_other s i hne, tailSlideAt_cnt_other s i hne]
      exact hwf.tail_eq q hq
  · intro q hq
    rw [tailSlideAt_nplaces] at hq
    rw [tailSlideAt_offset, tailSlideAt_cap, tailSlideAt_len]
    exact hwf.in_bounds q hq
  · intro q hq m hm
    rw [tailSlideAt_nplaces] at hq
    rw [tailSlideAt_slot]
    by_cases hne : q = p
    · subst hne
      rw [tailSlideAt_cnt_self] at hm
      rw [tailSlideAt_pool_at hwf hq i (by omega)]
      by_cases hmi : i ≤ m ∧ m < s.cnt q - 1
      · rw [if_pos hmi]
        exact hwf.occupied q hq (m + 1) (by omega)
      · rw [if_neg hmi, if_neg (by omega)]
        exact hwf.occupied q hq m (by omega)
    · rw [tailSlideAt_cnt_other s i hne] at hm
      rw [tailSlideAt_pool_other hwf hp hq hne i m]
      exact hwf.occupied q hq m hm
  · intro q hq m hlo hhi
    rw [tailSlideAt_nplaces] at hq
    rw [tailSlideAt_slot]
    by_cases hne : q = p
    · subst hne
      rw [tailSlideAt_cnt_self] at hlo
      rw [tailSlideAt_cap] at hhi
      rw [tailSlideAt_pool_at hwf hq i (by omega)]
      by_cases hend : m = s.cnt q - 1
      · rw [if_neg (by omega), if_pos hend]
      · rw [if_neg (by omega), if_neg hend]
        exact hwf.free q hq m (by omega) hhi
    · rw [tailSlideAt_cnt_other s i hne] at hlo
      rw [tailSlideAt_cap] at hhi
      rw [tailSlideAt_pool_other hwf hp hq hne i m]
      exact hwf.free q hq m hlo hhi
  · intro q r hq hr hqr
    rw [tailSlideAt_nplaces] at hq hr
    rw [tailSlideAt_offset, tailSlideAt_cap]
    exact hwf.disjoint q r hq hr hqr

theorem tailSlideAt_proj_self {s : Pool} (hwf : WF s) {p : PlaceId}
    (hp : p < s.nplaces) {i : Nat} (hi : i < s.cnt p) :
    (s.tailSlideAt p i).proj p
      = s.projFrom p 0 i ++ s.projFrom p (i + 1) (s.cnt p - 1 - i) := by
  have hh := hwf.head_lt p hp
  have hle := hwf.cnt_le p hp
  unfold proj
  obtain ⟨k, hk⟩ : ∃ k, s.cnt p - 1 - i = k := ⟨_, rfl⟩
  rw [tailSlideAt_cnt_self, hk, show s.cnt p - 1 = i + k by omega,
    projFrom_append _ p 0 i, Nat.zero_add]
  congr 1
  · apply projFrom_eq_of
    intro m hm
    rw [tailSlideAt_slot, tailSlideAt_pool_at hwf hp i (by omega),
      if_neg (by omega), if_neg (by omega)]
  · apply projFrom_eq_of
    intro m hm
    rw [tailSlideAt_slot, tailSlideAt_pool_at hwf hp i (by omega),
      if_pos (by omega), show i + m + 1 = i + 1 + m by omega]

theorem tailSlideAt_proj_other {s : Pool} (hwf : WF s) {p q : PlaceId}
    (hp : p < s.nplaces) (hq : q < s.nplaces) (hne : q ≠ p) (i : Nat) :
    (s.tailSlideAt p i).proj q = s.proj q := by
  unfold proj
  rw [tailSlideAt_cnt_other s i hne]
  apply projFrom_eq_of
  intro m hm
  rw [tailSlideAt_slot, tailSlideAt_pool_other hwf hp hq hne i (0 + m)]

/-! ### The composed operation -/

def removeMatching (s : Pool) (p : PlaceId) (pred : Colour → Bool) :
    Option Colour × Pool :=
  match s.findMatch p pred with
  | none => (none, s)
  | some i =>
    (s.pool (s.slot p i),
     if i ≤ s.cnt p - 1 - i then s.headSlideAt p i else s.tailSlideAt p i)

/-- RB6, no-match half: nothing satisfies `pred`, nothing changes. -/
theorem removeMatching_none {s : Pool} (_hwf : WF s) {p : PlaceId}
    (_hp : p < s.nplaces) {pred : Colour → Bool}
    (h : (s.removeMatching p pred).1 = none) :
    (s.removeMatching p pred).2 = s ∧ ∀ c ∈ s.proj p, pred c = false := by
  unfold removeMatching at h ⊢
  cases hf : s.findMatch p pred with
  | some i =>
    rw [hf] at h
    change s.pool (s.slot p i) = none at h
    obtain ⟨_, h2, h3, _⟩ := findMatchFrom_some hf
    obtain ⟨c, hc, _⟩ := matchesAt_true h3
    rw [hc] at h
    cases h
  | none =>
    refine ⟨rfl, fun c hc => ?_⟩
    obtain ⟨j, hj, hjc⟩ := mem_projFrom hc
    have := findMatchFrom_none hf j (by omega) (by omega)
    unfold matchesAt at this
    rw [Nat.zero_add] at hjc
    rw [hjc] at this
    exact this

/-- **RB6**, match half: `ring_remove_matching` removes *exactly the first*
token satisfying `pred` — the projection splits as `pre ++ c :: post` with
every `pre` element failing the predicate, and the survivor list is
`pre ++ post` in order. Both compaction directions land on the same list, and
the result is well-formed. Other places are untouched. -/
theorem removeMatching_some {s : Pool} (hwf : WF s) {p : PlaceId}
    (hp : p < s.nplaces) {pred : Colour → Bool} {c : Colour}
    (h : (s.removeMatching p pred).1 = some c) :
    pred c = true ∧
    ∃ pre post,
      s.proj p = pre ++ c :: post ∧
      (∀ c' ∈ pre, pred c' = false) ∧
      (s.removeMatching p pred).2.proj p = pre ++ post ∧
      (∀ q, q < s.nplaces → q ≠ p → (s.removeMatching p pred).2.proj q = s.proj q) ∧
      WF (s.removeMatching p pred).2 := by
  unfold removeMatching at h ⊢
  cases hf : s.findMatch p pred with
  | none =>
    rw [hf] at h
    change (none : Option Colour) = some c at h
    cases h
  | some i =>
    rw [hf] at h
    change s.pool (s.slot p i) = some c at h
    obtain ⟨_, hlt, hm, hearlier⟩ := findMatchFrom_some hf
    rw [Nat.zero_add] at hlt
    obtain ⟨c', hc', hpred⟩ := matchesAt_true hm
    have hcc : c' = c := by
      rw [hc'] at h
      exact Option.some.inj h
    subst hcc
    refine ⟨hpred, s.projFrom p 0 i, s.projFrom p (i + 1) (s.cnt p - 1 - i),
      proj_split hwf hp hlt hc', ?_, ?_, ?_, ?_⟩
    · intro c'' hc''
      obtain ⟨j, hj, hjc⟩ := mem_projFrom hc''
      have := hearlier j (by omega) (by omega)
      unfold matchesAt at this
      rw [Nat.zero_add] at hjc
      rw [hjc] at this
      exact this
    · show (if i ≤ s.cnt p - 1 - i then s.headSlideAt p i else s.tailSlideAt p i).proj p
          = s.projFrom p 0 i ++ s.projFrom p (i + 1) (s.cnt p - 1 - i)
      by_cases hside : i ≤ s.cnt p - 1 - i
      · rw [if_pos hside]
        exact headSlideAt_proj_self hwf hp hlt
      · rw [if_neg hside]
        exact tailSlideAt_proj_self hwf hp hlt
    · intro q hq hne
      show (if i ≤ s.cnt p - 1 - i then s.headSlideAt p i else s.tailSlideAt p i).proj q
          = s.proj q
      by_cases hside : i ≤ s.cnt p - 1 - i
      · rw [if_pos hside]
        exact headSlideAt_proj_other hwf hp hq hne i
      · rw [if_neg hside]
        exact tailSlideAt_proj_other hwf hp hq hne i
    · show WF (if i ≤ s.cnt p - 1 - i then s.headSlideAt p i else s.tailSlideAt p i)
      by_cases hside : i ≤ s.cnt p - 1 - i
      · rw [if_pos hside]
        exact headSlideAt_wf hwf hp hlt
      · rw [if_neg hside]
        exact tailSlideAt_wf hwf hp hlt

end Pool

end Libpetri
