/-
# The flat token pool: `ring_remove_matching`'s scan and compactions

The match scan and both compaction directions (`headSlideAt`, `tailSlideAt`),
split out of `Ring.lean`, which composes them into `removeMatching` (RB6).
-/
import Libpetri.Ring.Grow

namespace Libpetri

namespace Pool

/-! ## `ring_remove_matching` (`precompiled_backend.rs:438-490`)

The ν-net matched consume: scan positions from the head for the first token
satisfying `pred`, `take()` it, then close the gap from whichever end is
nearer — slide the preceding tokens forward and advance the head
(`headSlideAt`, chosen when `i ≤ cnt - 1 - i`), or slide the trailing tokens
back and retract the tail (`tailSlideAt`). RB6: exactly the first match is
removed and the survivors keep their order, whichever direction compacts. -/

theorem matchesAt_true {s : Pool} {p : PlaceId} {pred : Colour → Bool} {i : Nat}
    (h : s.matchesAt p pred i = true) :
    ∃ c, s.pool (s.slot p i) = some c ∧ pred c = true := by
  unfold matchesAt at h
  cases hp : s.pool (s.slot p i) with
  | none => rw [hp] at h; simp at h
  | some c => rw [hp] at h; exact ⟨c, rfl, h⟩

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

/-! ### The head-side compaction (`ring_remove_matching`'s nearer-the-head
branch, `precompiled_backend.rs:462-470`) -/

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

/-! ### The tail-side compaction (`ring_remove_matching`'s nearer-the-tail
branch, `precompiled_backend.rs:471-484`) -/

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

end Pool

end Libpetri
