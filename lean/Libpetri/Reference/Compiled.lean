import Libpetri.Reference.Build
import Libpetri.Spec.GlossaryEnable
import Libpetri.Spec.GlossaryTime

set_option linter.missingDocs true

/-!
# RefCompiled: the compiled net ([CONC-007], [PERF-030])

The integer-indexed form of a net that the bitmap executor works on: a place index, a transition
index, per transition a needs-mask, an inhibitor-mask, the consumption places, a cardinality check
and a match flag, and per place the reverse index of affected transitions. It is a pure function
of the net; it fires nothing and reads no marking.

The interface `CompiledNet N` is raw on purpose (an ID lookup, an ID-to-place map, functions for
the masks, lists for the reverse index and the consumption places): a requirement block states
its lines as a predicate over an abstract compile function `Net N → CompiledNet N`, and a wrong
compiler (two places with one ID, transitions numbered by name, a reverse index without the
inhibitor places) is a term of the same type.

Design decisions (ruling D55, recommendation (a), accepted):

* **Place IDs.** The place index is `Novel.Seam.PlaceIndex` over the net's places: its declared
  places and every place an arc or the output specification of a transition names
  (`netPlaceList`), each once. Position in the index is the ID, so the IDs are `0 … P-1` and the
  index is a bijection between the places and that range (`refCompileWith_placeAt_iff`). The order is
  not normative: Rust sorts the names, Java and TypeScript number by first use, and the model
  leaves the order to `List.dedup`. "Stable" means fixed for the life of the compiled net: the
  IDs are a function of the compiled net and of nothing else, which the type gives.
* **Transition IDs** are declaration positions: the transition with ID `j` is the `j`-th
  transition of the net (`refCompileWith_trans`), as the EXEC-002 block numbers them.
* **Masks.** Two full-width masks per transition, needs (input and read places) and inhibitor
  (inhibitor places), equal to the glossary's `NeedsMask` and `InhibitorMask` under the index
  (`refCompileWith_needs_iff`, `refCompileWith_inhibitor_iff`). There is no reset-mask: Rust and
  TypeScript keep the consumption places (input and reset places) as a list, and the reset-mask
  Java builds is read by no executor. The consumption places are `consumption`.
* **Reverse index.** Place ID `i` maps to the IDs of the transitions that have the place as an
  arc place (input, read, inhibitor or reset arc; glossary: Arc place, ruling D6). A transition
  that only deposits into the place is not in it. The list is duplicate-free and in ascending ID
  order; only membership is normative (Rust iterates a hash set).
* **Cardinality check.** Rust's and TypeScript's choice: a transition gets one exactly when some
  input is not `One`, and it lists every input's place ID and required count. Java also skips an
  `Exactly(1)` input; both choices meet CONC-008 (`CONC_008_allows_skipJava`).
* **Match flag.** `Reference.Trans` has no match specification (the ν model wraps it, W9), so the
  compiler takes the flag as a function `hm : Trans N → Bool` (`refCompileWith`); the reference
  without ν, `refCompileNet`, sets no flag.
* **Words.** The word layer of [PERF-030]: `ceilDiv P ws` words per full-width mask, a mask packed
  into words by `packBits` (bit `b` of word `k` is mask bit `k * ws + b`), and the words of the
  bitmap layout (presence bitmap, two masks per transition, dirty set) summing to
  `(1 + 2 * T) * ceilDiv P ws + ceilDiv T ws` for every compiled net (`maskWords_length`,
  `layoutWords_eq`).

The presence check on the compiled masks, over the indexed presence bitmap, passes exactly when
the glossary presence check `MaskCheck` passes on the named bitmap (`refCompileWith_presence_iff`);
this ties the compiled net to [CONC-004]'s formula. The reverse index is the "affected
transitions" of [CONC-005] (`refCompileWith_mem_affected`). On a net built by the reference net
builder, the places of the index are exactly the places of the built net
(`netPlaceList_built`, `refCompileWith_placeCount_built`).

The compile-time refusals (the CORE-043 passthrough check, the duplicate-input backstop of
CORE-030) are not part of this function; they are the net builder's and CORE-043's.
-/

namespace Libpetri.Reference

open Libpetri Libpetri.Novel.Seam Libpetri.Spec

variable {N : Type}

/-! ## The interface -/

/-- A compiled net ([CONC-007]): place IDs, transition IDs and the data precomputed per transition
and per place. Transition IDs index `trans`; place IDs are what `placeId` returns. -/
structure CompiledNet (N : Type) where
  /-- The number of place IDs, `P`. -/
  placeCount  : Nat
  /-- The place index: the ID of a place, `none` for a name the compiled net does not hold. -/
  placeId     : N → Option Nat
  /-- The place with an ID, `none` for a number that is no ID. -/
  placeAt     : Nat → Option N
  /-- The transitions by ID: the transition with ID `j` is `trans[j]`. -/
  trans       : List (Trans N)
  /-- The needs-mask: bit `i` of transition `j`'s mask. -/
  needs       : Nat → Nat → Bool
  /-- The inhibitor-mask: bit `i` of transition `j`'s mask. -/
  inhibitor   : Nat → Nat → Bool
  /-- The consumption place IDs of transition `j`: its input and reset places. -/
  consumption : Nat → List Nat
  /-- The reverse index: the IDs of the transitions affected by place `i`. -/
  affected    : Nat → List Nat
  /-- The cardinality check of transition `j`: its input place IDs with their required counts, or
  `none` when the transition needs none. -/
  card        : Nat → Option (List (Nat × Nat))
  /-- The match presence flag of transition `j` ([NU-020]). -/
  hasMatch    : Nat → Bool

/-- The number of transition IDs, `T`. -/
def CompiledNet.transCount (c : CompiledNet N) : Nat := c.trans.length

/-- The indexed presence bitmap of a bitmap over places: bit `i` is the bit of the place with ID
`i`, clear for a number that is no ID. -/
def CompiledNet.indexBits (c : CompiledNet N) (bits : N → Bool) : Nat → Bool :=
  fun i => match c.placeAt i with
    | some p => bits p
    | none => false

/-- The presence check on the compiled masks of transition `j`, over an indexed bitmap: every
needs bit below `P` is set in the bitmap and no inhibitor bit below `P` is. -/
def CompiledNet.presence (c : CompiledNet N) (j : Nat) (ib : Nat → Bool) : Bool :=
  (List.range c.placeCount).all fun i => (!c.needs j i || ib i) && (!c.inhibitor j i || !ib i)

/-! ## The reference compiler -/

/-- The places of a net: its declared places, then every place an arc or the output
specification of a transition names, in transition order, with repetitions. -/
def netPlaceList (n : Net N) : List N :=
  n.places ++ n.transitions.flatMap fun t => arcPlaces t ++ (t.out.map outPlaces).getD []

/-- A transition all of whose inputs are `One` (Rust's and TypeScript's test for "needs no
cardinality check"). -/
def onlyOneInputs (t : Trans N) : Bool := t.core.inputs.all fun s => s.card == .one

section Ref

variable [DecidableEq N]

/-- The reference place index: every place of the net once (`flatIndex`, which keeps the order
`List.dedup` leaves; the order is not normative). -/
def refPlaceIndex (n : Net N) : PlaceIndex N := flatIndex (netPlaceList n)

/-- **The reference compiler**, with the match flag given by `hm`. -/
def refCompileWith (hm : Trans N → Bool) (n : Net N) : CompiledNet N where
  placeCount := (refPlaceIndex n).size
  placeId := (refPlaceIndex n).lookup
  placeAt := (refPlaceIndex n).name?
  trans := n.transitions
  needs j i := match n.transitions[j]?, (refPlaceIndex n).name? i with
    | some t, some p => decide (p ∈ inPlaces t ∨ p ∈ t.core.reads)
    | _, _ => false
  inhibitor j i := match n.transitions[j]?, (refPlaceIndex n).name? i with
    | some t, some p => decide (p ∈ t.core.inhibitors)
    | _, _ => false
  consumption j := match n.transitions[j]? with
    | some t => ((inPlaces t ++ t.core.resets).map (refPlaceIndex n).idx).dedup
    | none => []
  affected i := match (refPlaceIndex n).name? i with
    | some p => (List.range n.transitions.length).filter fun j =>
        match n.transitions[j]? with
        | some t => decide (p ∈ arcPlaces t)
        | none => false
    | none => []
  card j := match n.transitions[j]? with
    | some t => if onlyOneInputs t then none
        else some (t.core.inputs.map fun s => ((refPlaceIndex n).idx s.place, requiredCount s.card))
    | none => none
  hasMatch j := (n.transitions[j]?.map hm).getD false

/-- **The reference compiler without ν**: no transition carries a match specification. -/
def refCompileNet (n : Net N) : CompiledNet N := refCompileWith (fun _ => false) n

/- The reference compilers are the witness models of the compiled-net blocks. -/
#spec_witness refCompileWith
#spec_witness refCompileNet

/-! ## The places of a net -/

omit [DecidableEq N] in
/-- A place of the net is a declared place, an arc place or an output place of a transition. -/
theorem mem_netPlaceList {n : Net N} {p : N} :
    p ∈ netPlaceList n ↔
      p ∈ n.places ∨ ∃ t ∈ n.transitions, ArcPlace t p ∨ OutputArc t p := by
  simp only [netPlaceList, List.mem_append, List.mem_flatMap, arcPlace_iff, OutputArc]
  apply or_congr Iff.rfl
  apply exists_congr; intro t
  apply and_congr Iff.rfl
  apply or_congr Iff.rfl
  cases t.out <;> simp

omit [DecidableEq N] in
/-- Every arc place of a transition of the net is a place of the net. -/
theorem mem_netPlaceList_of_arc {n : Net N} {t : Trans N} (ht : t ∈ n.transitions) {p : N}
    (hp : ArcPlace t p) : p ∈ netPlaceList n :=
  mem_netPlaceList.2 (.inr ⟨t, ht, .inl hp⟩)

/-! ## Place IDs: a bijection onto `0 … P-1` -/

section Index

variable {hm : Trans N → Bool} {n : Net N}

@[simp] theorem refCompileWith_placeCount : (refCompileWith hm n).placeCount = (refPlaceIndex n).size :=
  rfl

theorem mem_refPlaceIndex {p : N} : p ∈ (refPlaceIndex n).names ↔ p ∈ netPlaceList n :=
  mem_flatIndex

/-- The place with ID `i` is `p` exactly when `p` is a place of the net and its index is `i`. -/
theorem refCompileWith_placeAt_iff {i : Nat} {p : N} :
    (refCompileWith hm n).placeAt i = some p ↔
      p ∈ netPlaceList n ∧ (refPlaceIndex n).idx p = i := by
  show (refPlaceIndex n).name? i = some p ↔ _
  rw [← mem_refPlaceIndex]
  constructor
  · intro h
    exact ⟨(refPlaceIndex n).mem_of_name? h, (refPlaceIndex n).idx_of_name? h⟩
  · rintro ⟨hm, rfl⟩
    exact (refPlaceIndex n).name?_idx hm

/-- The ID lookup and the ID-to-place map are inverse: a place has ID `i` exactly when `i` is
below `P` and `i` names the place. -/
theorem refCompileWith_placeId_iff {p : N} {i : Nat} :
    (refCompileWith hm n).placeId p = some i ↔
      i < (refCompileWith hm n).placeCount ∧ (refCompileWith hm n).placeAt i = some p := by
  show (refPlaceIndex n).lookup p = some i ↔ _ ∧ (refPlaceIndex n).name? i = some p
  rw [PlaceIndex.lookup_eq_some]
  constructor
  · rintro ⟨hm, rfl⟩
    exact ⟨(refPlaceIndex n).idx_lt hm, (refPlaceIndex n).name?_idx hm⟩
  · rintro ⟨-, h⟩
    exact ⟨(refPlaceIndex n).mem_of_name? h, (refPlaceIndex n).idx_of_name? h⟩

/-- A number names a place exactly when it is below `P`. -/
theorem refCompileWith_placeAt_isSome {i : Nat} :
    ((refCompileWith hm n).placeAt i).isSome ↔ i < (refCompileWith hm n).placeCount := by
  show ((refPlaceIndex n).name? i).isSome ↔ i < (refPlaceIndex n).size
  constructor
  · intro h
    refine Nat.lt_of_not_le fun hc => ?_
    rw [(refPlaceIndex n).name?_eq_none_iff.2 hc] at h
    cases h
  · intro h
    cases hc : (refPlaceIndex n).name? i with
    | none => exact absurd ((refPlaceIndex n).name?_eq_none_iff.1 hc) (Nat.not_le_of_lt h)
    | some _ => rfl

/-- A name has an ID exactly when it is a place of the net. -/
theorem refCompileWith_placeId_isSome {p : N} :
    ((refCompileWith hm n).placeId p).isSome ↔ p ∈ netPlaceList n := by
  show ((refPlaceIndex n).lookup p).isSome ↔ _
  rw [← mem_refPlaceIndex]
  unfold PlaceIndex.lookup
  split <;> simp_all

/-- A place of the net has ID `idx p`. -/
theorem refCompileWith_placeId_of_mem {p : N} (h : p ∈ netPlaceList n) :
    (refCompileWith hm n).placeId p = some ((refPlaceIndex n).idx p) :=
  (PlaceIndex.lookup_eq_some _).2 ⟨mem_refPlaceIndex.2 h, rfl⟩

/-- A place of the net is the place with its ID. -/
theorem refCompileWith_placeAt_idx {p : N} (h : p ∈ netPlaceList n) :
    (refCompileWith hm n).placeAt ((refPlaceIndex n).idx p) = some p :=
  refCompileWith_placeAt_iff.2 ⟨h, rfl⟩

/-- Two places with one ID are one place. -/
theorem refCompileWith_placeId_inj {p q : N} {i : Nat} (hp : (refCompileWith hm n).placeId p = some i)
    (hq : (refCompileWith hm n).placeId q = some i) : p = q := by
  have h1 := (refCompileWith_placeId_iff.1 hp).2
  have h2 := (refCompileWith_placeId_iff.1 hq).2
  rw [h1] at h2
  exact Option.some.inj h2

/-! ## Transition IDs: declaration positions -/

/-- The transition with ID `j` is the `j`-th transition of the net. -/
@[simp] theorem refCompileWith_trans : (refCompileWith hm n).trans = n.transitions := rfl

/-- The number of transition IDs is the number of transitions of the net. -/
@[simp] theorem refCompileWith_transCount :
    (refCompileWith hm n).transCount = n.transitions.length := rfl

end Index

/-! ## The masks -/

section Masks

variable {hm : Trans N → Bool} {n : Net N}

/-- Bit `i` of the needs-mask of the transition with ID `j` is set exactly when `i` names an input
or read place of that transition. -/
theorem refCompileWith_needs_iff {j i : Nat} :
    (refCompileWith hm n).needs j i = true ↔
      ∃ t p, n.transitions[j]? = some t ∧ (refCompileWith hm n).placeAt i = some p ∧
        NeedsMask t p := by
  show (match n.transitions[j]?, (refPlaceIndex n).name? i with
    | some t, some p => decide (p ∈ inPlaces t ∨ p ∈ t.core.reads)
    | _, _ => false) = true ↔ ∃ t p, _ ∧ (refPlaceIndex n).name? i = some p ∧ _
  cases n.transitions[j]? <;> cases (refPlaceIndex n).name? i <;> simp [NeedsMask, ReadArc]

/-- Bit `i` of the inhibitor-mask of the transition with ID `j` is set exactly when `i` names an
inhibitor place of that transition. -/
theorem refCompileWith_inhibitor_iff {j i : Nat} :
    (refCompileWith hm n).inhibitor j i = true ↔
      ∃ t p, n.transitions[j]? = some t ∧ (refCompileWith hm n).placeAt i = some p ∧
        InhibitorMask t p := by
  show (match n.transitions[j]?, (refPlaceIndex n).name? i with
    | some t, some p => decide (p ∈ t.core.inhibitors)
    | _, _ => false) = true ↔ ∃ t p, _ ∧ (refPlaceIndex n).name? i = some p ∧ _
  cases n.transitions[j]? <;> cases (refPlaceIndex n).name? i <;> simp [InhibitorMask, InhibitorArc]

/-- The needs-mask by place: for the transition `t` with ID `j` and a place with ID `i`, the bit
is set exactly when the place is in `t`'s needs-mask. -/
theorem refCompileWith_needs_at {j i : Nat} {t : Trans N} {p : N} (ht : n.transitions[j]? = some t)
    (hp : (refCompileWith hm n).placeAt i = some p) :
    (refCompileWith hm n).needs j i = true ↔ NeedsMask t p := by
  rw [refCompileWith_needs_iff]
  constructor
  · rintro ⟨t', p', ht', hp', h⟩
    rw [ht] at ht'; rw [hp] at hp'
    cases ht'; cases hp'; exact h
  · intro h; exact ⟨t, p, ht, hp, h⟩

/-- The inhibitor-mask by place. -/
theorem refCompileWith_inhibitor_at {j i : Nat} {t : Trans N} {p : N} (ht : n.transitions[j]? = some t)
    (hp : (refCompileWith hm n).placeAt i = some p) :
    (refCompileWith hm n).inhibitor j i = true ↔ InhibitorMask t p := by
  rw [refCompileWith_inhibitor_iff]
  constructor
  · rintro ⟨t', p', ht', hp', h⟩
    rw [ht] at ht'; rw [hp] at hp'
    cases ht'; cases hp'; exact h
  · intro h; exact ⟨t, p, ht, hp, h⟩

/-- A number that is no transition ID, or no place ID, sets no mask bit. -/
theorem refCompileWith_needs_outside {j i : Nat}
    (h : n.transitions.length ≤ j ∨ (refCompileWith hm n).placeCount ≤ i) :
    (refCompileWith hm n).needs j i = false ∧ (refCompileWith hm n).inhibitor j i = false := by
  have hn : n.transitions[j]? = none ∨ (refPlaceIndex n).name? i = none := by
    rcases h with h | h
    · exact .inl (List.getElem?_eq_none h)
    · exact .inr ((refPlaceIndex n).name?_eq_none_iff.2 h)
  show (match n.transitions[j]?, (refPlaceIndex n).name? i with
    | some t, some p => decide (p ∈ inPlaces t ∨ p ∈ t.core.reads)
    | _, _ => false) = false ∧ (match n.transitions[j]?, (refPlaceIndex n).name? i with
    | some t, some p => decide (p ∈ t.core.inhibitors)
    | _, _ => false) = false
  rcases hn with h | h
  · rw [h]; simp
  · rw [h]; cases n.transitions[j]? <;> simp

/-! ## The presence check on the compiled masks -/

/-- **Link to [CONC-004].** For the transition `t` with ID `j`, the presence check on its compiled
masks over the indexed bitmap passes exactly when the glossary presence check of `t` passes on the
named bitmap. -/
theorem refCompileWith_presence_iff {j : Nat} {t : Trans N} (ht : n.transitions[j]? = some t)
    (bits : N → Bool) :
    (refCompileWith hm n).presence j ((refCompileWith hm n).indexBits bits) = true ↔
      MaskCheck t bits := by
  have htm : t ∈ n.transitions := List.mem_of_getElem? ht
  have hnp : ∀ p, NeedsMask t p → p ∈ netPlaceList n := fun p hp =>
    mem_netPlaceList_of_arc htm (hp.elim (fun h => .inl h) (fun h => .inr (.inl h)))
  have hip : ∀ p, InhibitorMask t p → p ∈ netPlaceList n := fun p hp =>
    mem_netPlaceList_of_arc htm (.inr (.inr (.inl hp)))
  simp only [CompiledNet.presence, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · intro h
    refine ⟨fun p hp => ?_, fun p hp => ?_⟩
    · have hpa := refCompileWith_placeAt_idx (hm := hm) (hnp p hp)
      have hlt := (refCompileWith_placeAt_isSome (hm := hm)).1 (by rw [hpa]; rfl)
      have hb := (h _ hlt).1
      have hn := (refCompileWith_needs_at ht hpa).2 hp
      rw [hn] at hb
      simpa [CompiledNet.indexBits, hpa] using hb
    · have hpa := refCompileWith_placeAt_idx (hm := hm) (hip p hp)
      have hlt := (refCompileWith_placeAt_isSome (hm := hm)).1 (by rw [hpa]; rfl)
      have hb := (h _ hlt).2
      have hn := (refCompileWith_inhibitor_at ht hpa).2 hp
      rw [hn] at hb
      simpa [CompiledNet.indexBits, hpa] using hb
  · rintro ⟨hn, hh⟩ i hi
    obtain ⟨p, hpa⟩ := Option.isSome_iff_exists.1 ((refCompileWith_placeAt_isSome (hm := hm)).2 hi)
    have hib : (refCompileWith hm n).indexBits bits i = bits p := by
      simp [CompiledNet.indexBits, hpa]
    rw [hib]
    constructor
    · by_cases hq : NeedsMask t p
      · exact .inr (hn p hq)
      · left
        cases hc : (refCompileWith hm n).needs j i
        · rfl
        · exact absurd ((refCompileWith_needs_at ht hpa).1 hc) hq
    · by_cases hq : InhibitorMask t p
      · exact .inr (hh p hq)
      · left
        cases hc : (refCompileWith hm n).inhibitor j i
        · rfl
        · exact absurd ((refCompileWith_inhibitor_at ht hpa).1 hc) hq

end Masks

/-! ## Consumption places, the reverse index, the cardinality check, the match flag -/

section Data

variable {hm : Trans N → Bool} {n : Net N}

/-- Place ID `i` is a consumption place of the transition with ID `j` exactly when it names an
input or reset place of that transition. -/
theorem refCompileWith_mem_consumption {j i : Nat} :
    i ∈ (refCompileWith hm n).consumption j ↔
      ∃ t p, n.transitions[j]? = some t ∧ (refCompileWith hm n).placeAt i = some p ∧
        (p ∈ inPlaces t ∨ ResetArc t p) := by
  show i ∈ (match n.transitions[j]? with
    | some t => ((inPlaces t ++ t.core.resets).map (refPlaceIndex n).idx).dedup
    | none => []) ↔ _
  cases ht : n.transitions[j]? with
  | none => simp
  | some t =>
    have htm : t ∈ n.transitions := List.mem_of_getElem? ht
    show i ∈ ((inPlaces t ++ t.core.resets).map (refPlaceIndex n).idx).dedup ↔ _
    rw [List.mem_dedup, List.mem_map]
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hp' := List.mem_append.1 hp
      refine ⟨t, p, rfl, refCompileWith_placeAt_idx (mem_netPlaceList_of_arc htm ?_), hp'⟩
      rcases hp' with hp' | hp'
      · exact .inl hp'
      · exact .inr (.inr (.inr hp'))
    · rintro ⟨t', p, ht', hpa, hp⟩
      cases ht'
      obtain ⟨-, rfl⟩ := refCompileWith_placeAt_iff.1 hpa
      exact ⟨p, List.mem_append.2 hp, rfl⟩

/-- The consumption places of a transition are listed once each. -/
theorem refCompileWith_consumption_nodup (j : Nat) : ((refCompileWith hm n).consumption j).Nodup := by
  show (match n.transitions[j]? with
    | some t => ((inPlaces t ++ t.core.resets).map (refPlaceIndex n).idx).dedup
    | none => []).Nodup
  cases n.transitions[j]? with
  | none => exact List.nodup_nil
  | some t => exact List.nodup_dedup _

/-- **The reverse index** ([CONC-005]'s affected transitions): transition ID `j` is affected by
place ID `i` exactly when `i` names an arc place of the transition with ID `j`. -/
theorem refCompileWith_mem_affected {i j : Nat} :
    j ∈ (refCompileWith hm n).affected i ↔
      ∃ t p, n.transitions[j]? = some t ∧ (refCompileWith hm n).placeAt i = some p ∧
        ArcPlace t p := by
  show j ∈ (match (refPlaceIndex n).name? i with
    | some p => (List.range n.transitions.length).filter fun j =>
        match n.transitions[j]? with
        | some t => decide (p ∈ arcPlaces t)
        | none => false
    | none => []) ↔ ∃ t p, _ ∧ (refPlaceIndex n).name? i = some p ∧ _
  cases hp : (refPlaceIndex n).name? i with
  | none => simp
  | some p =>
    rw [List.mem_filter, List.mem_range]
    constructor
    · rintro ⟨-, h⟩
      cases ht : n.transitions[j]? with
      | none => rw [ht] at h; cases h
      | some t =>
        rw [ht] at h
        exact ⟨t, p, rfl, rfl, (arcPlace_iff t p).2 (of_decide_eq_true h)⟩
    · rintro ⟨t, p', ht, hp', h⟩
      cases hp'
      refine ⟨(List.getElem?_eq_some_iff.1 ht).1, ?_⟩
      rw [ht]; exact decide_eq_true ((arcPlace_iff t p).1 h)

/-- The reverse index lists each affected transition once. -/
theorem refCompileWith_affected_nodup (i : Nat) : ((refCompileWith hm n).affected i).Nodup := by
  show (match (refPlaceIndex n).name? i with
    | some p => (List.range n.transitions.length).filter fun j =>
        match n.transitions[j]? with
        | some t => decide (p ∈ arcPlaces t)
        | none => false
    | none => []).Nodup
  cases (refPlaceIndex n).name? i with
  | none => exact List.nodup_nil
  | some p => exact (List.nodup_range).filter _

/-- The reverse index by place: for a place `p` of the net and the transition `t` with ID `j`,
`j` is affected by `p`'s ID exactly when `p` is an arc place of `t`. -/
theorem refCompileWith_affected_at {j : Nat} {t : Trans N} {p : N} (ht : n.transitions[j]? = some t)
    (hp : p ∈ netPlaceList n) :
    j ∈ (refCompileWith hm n).affected ((refPlaceIndex n).idx p) ↔ ArcPlace t p := by
  rw [refCompileWith_mem_affected]
  constructor
  · rintro ⟨t', p', ht', hp', h⟩
    rw [ht] at ht'; rw [refCompileWith_placeAt_idx hp] at hp'
    cases ht'; cases hp'; exact h
  · intro h; exact ⟨t, p, ht, refCompileWith_placeAt_idx hp, h⟩

omit [DecidableEq N] in
/-- `onlyOneInputs` is the test "every input is `One`". -/
theorem onlyOneInputs_iff (t : Trans N) :
    onlyOneInputs t = true ↔ ∀ s ∈ t.core.inputs, s.card = .one := by
  simp [onlyOneInputs]

/-- The cardinality check of the transition `t` with ID `j`: none when every input is `One`,
otherwise every input's place ID with its required count, in input order. -/
theorem refCompileWith_card {j : Nat} {t : Trans N} (ht : n.transitions[j]? = some t) :
    (refCompileWith hm n).card j =
      if onlyOneInputs t then none
      else some (t.core.inputs.map fun (s : NInSpec N) => ((refPlaceIndex n).idx s.place, requiredCount s.card)) := by
  show (match n.transitions[j]? with
    | some t => if onlyOneInputs t then none
        else some (t.core.inputs.map fun (s : NInSpec N) => ((refPlaceIndex n).idx s.place, requiredCount s.card))
    | none => none) = _
  rw [ht]

/-- A transition with a cardinality check has an input that is not `One`; a transition without
one has only `One` inputs. -/
theorem refCompileWith_card_none_iff {j : Nat} {t : Trans N} (ht : n.transitions[j]? = some t) :
    (refCompileWith hm n).card j = none ↔ ∀ s ∈ t.core.inputs, s.card = .one := by
  rw [refCompileWith_card ht, ← onlyOneInputs_iff]
  cases onlyOneInputs t <;> simp

/-- Every entry of a cardinality check is the ID of an input place with its required count. -/
theorem refCompileWith_card_entry {j : Nat} {t : Trans N} (ht : n.transitions[j]? = some t)
    {l : List (Nat × Nat)} (hl : (refCompileWith hm n).card j = some l) {e : Nat × Nat}
    (he : e ∈ l) :
    ∃ s ∈ t.core.inputs, (refCompileWith hm n).placeId s.place = some e.1 ∧
      e.2 = requiredCount s.card := by
  rw [refCompileWith_card ht] at hl
  split at hl
  · cases hl
  · cases hl
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 he
    have hm' : s.place ∈ netPlaceList n :=
      mem_netPlaceList_of_arc (List.mem_of_getElem? ht) (.inl (List.mem_map_of_mem hs))
    exact ⟨s, hs, refCompileWith_placeId_of_mem hm', rfl⟩

/-- The match flag of the transition `t` with ID `j` is `hm t`. -/
theorem refCompileWith_hasMatch {j : Nat} {t : Trans N} (ht : n.transitions[j]? = some t) :
    (refCompileWith hm n).hasMatch j = hm t := by
  show (n.transitions[j]?.map hm).getD false = _
  rw [ht]; rfl

/-- The reference compiler without ν sets no match flag. -/
theorem refCompileNet_hasMatch (j : Nat) : (refCompileNet n).hasMatch j = false := by
  show (n.transitions[j]?.map (fun _ => false)).getD false = false
  cases n.transitions[j]? <;> rfl

end Data

/-! ## Built nets -/

/-- On a net built by the reference net builder, the places of the net (`netPlaceList` of its
untimed view) are exactly the places of the built net: the builder already collects every place
an arc or output specification names. -/
theorem netPlaceList_built {A : Type} {B : TBuilder N A} {inp : NetIn B} {b : BuiltNet N A}
    (h : refNetBuild inp = .ok b) (p : N) : p ∈ netPlaceList b.toNet ↔ p ∈ b.places := by
  have hb : b.places = (inp.places ++ inp.terminals ++
      (inp.trans.map B.defOf).flatMap TransDef.namedPlaces).dedup ∧
      b.trans = inp.trans.map B.defOf := by
    unfold refNetBuild at h
    split at h
    · cases h
    · cases h; exact ⟨rfl, rfl⟩
  rw [mem_netPlaceList]
  constructor
  · rintro (hp | ⟨t, ht, hp⟩)
    · exact hp
    · simp only [BuiltNet.toNet, List.mem_map] at ht
      obtain ⟨d, hd, rfl⟩ := ht
      rw [hb.1, List.mem_dedup]
      refine List.mem_append_right _ (List.mem_flatMap.2 ⟨d, hb.2 ▸ hd, ?_⟩)
      simp only [TransDef.namedPlaces, List.mem_append]
      rcases hp with hp | ⟨o, ho, hp⟩
      · rcases hp with hp | hp | hp | hp
        · exact .inl (.inl (.inl (.inl hp)))
        · exact .inl (.inl (.inr hp))
        · exact .inl (.inl (.inl (.inr hp)))
        · exact .inl (.inr hp)
      · right
        simp only [TransDef.toTrans] at ho
        rw [ho]; exact hp
  · intro hp; exact .inl hp

/-- On a net built by the reference net builder, the number of place IDs is the number of places
of the built net. -/
theorem refCompileWith_placeCount_built {A : Type} {B : TBuilder N A} {inp : NetIn B}
    {b : BuiltNet N A} (h : refNetBuild inp = .ok b) (hm : Trans N → Bool) :
    (refCompileWith hm b.toNet).placeCount = b.places.length := by
  have hnd : b.places.Nodup := by
    unfold refNetBuild at h
    split at h
    · cases h
    · cases h; exact List.nodup_dedup _
  show (netPlaceList b.toNet).dedup.length = _
  apply List.Perm.length_eq
  rw [List.perm_ext_iff_of_nodup (List.nodup_dedup _) hnd]
  intro p
  rw [List.mem_dedup, netPlaceList_built h]

end Ref

/-! ## Words ([PERF-030]) -/

/-- `⌈a / b⌉` for `b > 0`. -/
def ceilDiv (a b : Nat) : Nat := (a + b - 1) / b

/-- Bits `base … base + n - 1` of a bitmap packed into one number, bit `b` of the number being
bit `base + b` of the bitmap. -/
def packWord (bits : Nat → Bool) : Nat → Nat → Nat
  | _, 0 => 0
  | base, n + 1 => (if bits base then 1 else 0) + 2 * packWord bits (base + 1) n

/-- A bitmap over IDs packed into `W` words of `ws` bits: bit `b` of word `k` is bit
`k * ws + b`. -/
def packBits (ws W : Nat) (bits : Nat → Bool) : List Nat :=
  (List.range W).map fun k => packWord bits (k * ws) ws

/-- Bit `i` of a packed word is bit `base + i` of the bitmap for `i < n`, and clear above. -/
theorem testBit_packWord (bits : Nat → Bool) :
    ∀ (n base i : Nat), (packWord bits base n).testBit i = (decide (i < n) && bits (base + i))
  | 0, _, _ => by simp [packWord]
  | n + 1, base, 0 => by
    rw [packWord, Nat.testBit_zero]
    cases bits base <;> simp
  | n + 1, base, i + 1 => by
    have h2 : ((if bits base then 1 else 0) + 2 * packWord bits (base + 1) n) / 2 =
        packWord bits (base + 1) n := by
      cases bits base <;> simp; omega
    rw [packWord, Nat.testBit_add_one, h2, testBit_packWord bits n (base + 1) i]
    simp [Nat.add_assoc, Nat.add_comm 1 i]

/-- A packed word fits in its `n` bits. -/
theorem packWord_lt (bits : Nat → Bool) : ∀ (n base : Nat), packWord bits base n < 2 ^ n
  | 0, _ => by simp [packWord]
  | n + 1, base => by
    have ih := packWord_lt bits n (base + 1)
    rw [packWord, Nat.pow_succ]
    cases bits base <;> simp <;> omega

/-- A packed bitmap has `W` words. -/
@[simp] theorem packBits_length (ws W : Nat) (bits : Nat → Bool) :
    (packBits ws W bits).length = W := by
  simp [packBits]

/-- Every bit below `W * ws` is where `packBits` puts it: bit `i % ws` of word `i / ws`. -/
theorem packBits_testBit {ws W : Nat} (bits : Nat → Bool) {i : Nat} (hws : 0 < ws)
    (hi : i < W * ws) :
    ((packBits ws W bits).getD (i / ws) 0).testBit (i % ws) = bits i := by
  have hk : i / ws < W := (Nat.div_lt_iff_lt_mul hws).2 hi
  simp only [packBits, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
    Option.map_some, Option.getD_some]
  rw [testBit_packWord, Nat.div_add_mod' i ws]
  simp [Nat.mod_lt i hws]

/-- The number of full-width masks per transition the reference compiler keeps: the needs-mask
and the inhibitor-mask (ruling D55 (a): no reset-mask). -/
def refMaskCount : Nat := 2

/-- The words of a compiled net's full-width masks at word size `ws`: per transition, its
needs-mask and its inhibitor-mask, each packed into `⌈P / ws⌉` words. -/
def CompiledNet.maskWords (ws : Nat) (c : CompiledNet N) : List (List Nat) :=
  (List.range c.transCount).flatMap fun j =>
    [packBits ws (ceilDiv c.placeCount ws) (c.needs j),
     packBits ws (ceilDiv c.placeCount ws) (c.inhibitor j)]

/-- The words of the bitmap layout of a compiled net at word size `ws`: the presence bitmap
(`⌈P / ws⌉` words), the masks, and the dirty set (`⌈T / ws⌉` words). -/
def CompiledNet.layoutWords (ws : Nat) (c : CompiledNet N) : Nat :=
  ceilDiv c.placeCount ws + ((c.maskWords ws).map List.length).sum + ceilDiv c.transCount ws

/-- The masks of a compiled net take `2 * T * ⌈P / ws⌉` words. -/
theorem maskWords_length (ws : Nat) (c : CompiledNet N) :
    ((c.maskWords ws).map List.length).sum =
      refMaskCount * c.transCount * ceilDiv c.placeCount ws := by
  unfold CompiledNet.maskWords refMaskCount
  generalize c.transCount = T
  induction T with
  | zero => simp
  | succ T ih =>
    rw [List.range_succ, List.flatMap_append, List.map_append, List.sum_append, ih]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil,
      packBits_length, List.sum_cons, List.sum_nil]
    ring

/-- **The word count PERF-030 bounds**, for the reference layout: the bitmap layout of a compiled
net takes `(1 + 2 * T) * ⌈P / ws⌉ + ⌈T / ws⌉` words. -/
theorem layoutWords_eq (ws : Nat) (c : CompiledNet N) :
    c.layoutWords ws =
      (1 + refMaskCount * c.transCount) * ceilDiv c.placeCount ws + ceilDiv c.transCount ws := by
  unfold CompiledNet.layoutWords
  rw [maskWords_length]
  ring

end Libpetri.Reference
