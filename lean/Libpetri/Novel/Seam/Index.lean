import Libpetri.Soundness
import Mathlib.Data.List.Dedup

/-!
# The name → index seam: place index, named markings, the encoded seed ([VER-001], [CORE-072])

`Basic.lean` takes `PlaceId := Nat` and every theorem downstream starts from an abstract seed
`a0 = alpha m0`. Both are idealisations of one seam the shipped verifier crosses before any CHC
rule is written:

* `net_flattener.rs` `flatten` builds the index from the **declared** places of the net it is
  handed (`net.places()`, sorted and deduplicated) — a finite list of names, not all of `Nat`;
* `smt_encoder.rs` `encode_net` seeds `Reachable` with `initial_marking.count(&flat.places[i])`
  for `i` in `0..place_count` — the caller's named `MarkingState` **restricted** to the index.

A token the caller put on a place outside that list has no variable, so the seed cannot carry
it. With `PlaceId := Nat` that was inexpressible, which is why the stray-token `Proven` got past
this development. This module models the seam: `PlaceIndex` (a duplicate-free name list),
`NMarking` (a finitely supported named marking, `marking_state.rs` `MarkingState`), `encodeM0`
(the seed as encoded) and `Covers` (every marked name has an index) — the premise under which
the restriction loses nothing.

The flattener sorts the names; only the order of the index follows from that, and no result here
depends on the order, so `flatIndex` leaves both the order and the numbering to `List.dedup`,
which keeps the **last** occurrence of each name. The model's index is therefore not the Rust's
sorted one, and a statement about a particular index number (`Retrodict.lean`) is about the
model's. Every theorem is stated for an arbitrary `PlaceIndex`.
-/

namespace Libpetri.Novel.Seam

open Libpetri

variable {N : Type} [DecidableEq N]

/-- The flat net's place list: `FlatNet::places` with `place_index` its inverse
(`net_flattener.rs` `flatten`). Position in `names` is the flat index. -/
structure PlaceIndex (N : Type) where
  names : List N
  nodup : names.Nodup

namespace PlaceIndex

/-- `FlatNet::place_count`. -/
def size (ix : PlaceIndex N) : Nat := ix.names.length

/-- `place_index[name]` for a name in the index (the position of the name). -/
def idx (ix : PlaceIndex N) (n : N) : Nat := ix.names.idxOf n

/-- `flat.place_index.get(name)`: `none` for a name the index does not hold. -/
def lookup (ix : PlaceIndex N) (n : N) : Option Nat :=
  if n ∈ ix.names then some (ix.idx n) else none

/-- `flat.places[i]`, `none` past `place_count`. -/
def name? (ix : PlaceIndex N) (i : Nat) : Option N := ix.names[i]?

variable (ix : PlaceIndex N)

theorem idx_lt {n : N} (h : n ∈ ix.names) : ix.idx n < ix.size :=
  List.idxOf_lt_length_iff.mpr h

theorem name?_idx {n : N} (h : n ∈ ix.names) : ix.name? (ix.idx n) = some n := by
  unfold name?
  rw [List.getElem?_eq_getElem (ix.idx_lt h)]
  exact congrArg some (List.getElem_idxOf _)

theorem idx_of_name? {i : Nat} {n : N} (h : ix.name? i = some n) : ix.idx n = i := by
  unfold name? at h
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp h
  exact ix.nodup.idxOf_getElem i hi

omit [DecidableEq N] in
theorem mem_of_name? {i : Nat} {n : N} (h : ix.name? i = some n) : n ∈ ix.names :=
  List.mem_of_getElem? h

omit [DecidableEq N] in
theorem name?_eq_none_iff {i : Nat} : ix.name? i = none ↔ ix.size ≤ i :=
  List.getElem?_eq_none_iff

/-- Two names with the same index are the same name, provided one of them is in the index. -/
theorem idx_inj {n n' : N} (h : n ∈ ix.names) : ix.idx n = ix.idx n' ↔ n = n' :=
  List.idxOf_inj h

theorem lookup_eq_some {n : N} {i : Nat} : ix.lookup n = some i ↔ n ∈ ix.names ∧ ix.idx n = i := by
  unfold lookup
  split <;> simp_all

theorem lookup_eq_none {n : N} : ix.lookup n = none ↔ n ∉ ix.names := by
  unfold lookup
  split <;> simp_all

end PlaceIndex

/-- `net_flattener.rs` `flatten`'s index over a declared place list: every declared name once.
(`flatten` also sorts; see the module note.) -/
def flatIndex (declared : List N) : PlaceIndex N := ⟨declared.dedup, List.nodup_dedup _⟩

@[simp] theorem mem_flatIndex {declared : List N} {n : N} :
    n ∈ (flatIndex declared).names ↔ n ∈ declared :=
  List.mem_dedup

/-- A named marking: `marking_state.rs` `MarkingState`, token counts by place name with non-zero
counts only and each name once. Finitely supported by construction. -/
structure NMarking (N : Type) where
  entries : List (N × Nat)
  nodup : (entries.map Prod.fst).Nodup
  pos : ∀ e ∈ entries, 0 < e.2

namespace NMarking

/-- `MarkingState::count`: the count of a name, `0` for a name the marking does not hold. -/
def count (m : NMarking N) (n : N) : Nat :=
  match m.entries.find? (fun e => decide (e.1 = n)) with
  | some e => e.2
  | none => 0

/-- `MarkingState::places`: the marked names. -/
def places (m : NMarking N) : List N := m.entries.map Prod.fst

theorem count_ne_zero_iff (m : NMarking N) (n : N) : m.count n ≠ 0 ↔ n ∈ m.places := by
  unfold count places
  constructor
  · intro h
    cases hf : m.entries.find? (fun e => decide (e.1 = n)) with
    | none => rw [hf] at h; exact absurd rfl h
    | some e =>
      have hmem := List.mem_of_find?_eq_some hf
      have he : e.1 = n := by simpa using List.find?_some hf
      exact List.mem_map.mpr ⟨e, hmem, he⟩
  · intro h
    obtain ⟨e, hmem, he⟩ := List.mem_map.mp h
    cases hf : m.entries.find? (fun e => decide (e.1 = n)) with
    | none =>
      exact absurd (by simpa using he) (List.find?_eq_none.mp hf e hmem)
    | some e' =>
      simp only
      exact Nat.pos_iff_ne_zero.mp (m.pos e' (List.mem_of_find?_eq_some hf))

end NMarking

/-- **The seed as encoded**: `encode_net`'s init rule writes `initial_marking.count(&flat.places[i])`
for each `i < place_count` and nothing else (`smt_encoder.rs` `encode_net`). Indices past
`place_count` have no variable; they read `0`, which every flat transition leaves alone. -/
def encodeM0 (ix : PlaceIndex N) (m0 : NMarking N) : AMarking :=
  fun i => if h : i < ix.size then m0.count (ix.names[i]'h) else 0

/-- The restriction of a named count function to the index: what `encodeM0` does to the seed, and
what the encoding can see of any named marking. -/
def restrict (ix : PlaceIndex N) (m : N → Nat) : AMarking :=
  fun i => match ix.name? i with
    | some n => m n
    | none => 0

/-- Read an indexed marking back by name; names without an index read `0`. -/
def lift (ix : PlaceIndex N) (a : AMarking) : N → Nat :=
  fun n => if n ∈ ix.names then a (ix.idx n) else 0

/-- **Covers**: every name the marking marks has an index. The seam loses nothing exactly under
this premise. -/
def Covers (ix : PlaceIndex N) (m : N → Nat) : Prop :=
  ∀ n, m n ≠ 0 → n ∈ ix.names

theorem encodeM0_eq_restrict (ix : PlaceIndex N) (m0 : NMarking N) :
    encodeM0 ix m0 = restrict ix m0.count := by
  funext i
  unfold encodeM0 restrict PlaceIndex.name?
  by_cases h : i < ix.size
  · rw [dif_pos h, List.getElem?_eq_getElem h]
  · rw [dif_neg h, List.getElem?_eq_none (Nat.le_of_not_lt h)]

theorem restrict_idx (ix : PlaceIndex N) (m : N → Nat) {n : N} (h : n ∈ ix.names) :
    restrict ix m (ix.idx n) = m n := by
  unfold restrict
  rw [ix.name?_idx h]

omit [DecidableEq N] in
theorem restrict_of_size_le (ix : PlaceIndex N) (m : N → Nat) {i : Nat} (h : ix.size ≤ i) :
    restrict ix m i = 0 := by
  unfold restrict
  rw [ix.name?_eq_none_iff.mpr h]

omit [DecidableEq N] in
theorem covers_zero {ix : PlaceIndex N} {m : N → Nat} (h : Covers ix m) {n : N}
    (hn : n ∉ ix.names) : m n = 0 :=
  Classical.byContradiction fun h' => hn (h n h')

/-- Under `Covers`, the restriction is lossless: reading it back by name gives the marking. -/
theorem lift_restrict {ix : PlaceIndex N} {m : N → Nat} (h : Covers ix m) :
    lift ix (restrict ix m) = m := by
  funext n
  unfold lift
  by_cases hn : n ∈ ix.names
  · rw [if_pos hn, restrict_idx ix m hn]
  · rw [if_neg hn, covers_zero h hn]

theorem restrict_lift (ix : PlaceIndex N) {a : AMarking} (h : ∀ i, ix.size ≤ i → a i = 0) :
    restrict ix (lift ix a) = a := by
  funext i
  unfold restrict
  cases hi : ix.name? i with
  | none => exact (h i (ix.name?_eq_none_iff.mp hi)).symm
  | some n =>
    simp only [lift, if_pos (ix.mem_of_name? hi), ix.idx_of_name? hi]

/-- The restriction is injective on covered markings. -/
theorem restrict_injective {ix : PlaceIndex N} {m m' : N → Nat} (h : Covers ix m)
    (h' : Covers ix m') (he : restrict ix m = restrict ix m') : m = m' := by
  rw [← lift_restrict h, ← lift_restrict h', he]

end Libpetri.Novel.Seam
