import Libpetri.Novel.Seam.Net
import Libpetri.Novel.Seam.Excuses
import Libpetri.Novel.Pairwise
import Libpetri.Strengthening

/-!
# The error rule's `Bad` against the named property ([VER-002], [VER-003], [VER-014])

`encode_property_violation` (`smt_encoder.rs`) writes `Bad(M)` over the flat variables `m_i`,
`i < place_count`. The property the caller asked about is a statement about the **named**
marking. This module models the arms of `Bad` as encoded and proves each equivalent to its named
reading on the restriction of a marking the index covers:

| arm | encoded | named | theorem |
|---|---|---|---|
| `DeadlockFree` | `deadlockBad` | `NDeadlock` | `deadlockBad_iff` |
| `PlaceBound`, `BranchPlaceBound` | `placeBoundBad` | `k < m n` | `placeBoundBad_iff` |
| `MutualExclusion` (pairwise) | `pairMarkedBad` | two entries marked | `pairMarkedBad_iff` |
| `Unreachable` | `allMarkedBad` | every place marked | `allMarkedBad_iff` |
| `QuiescentCount` | `countBad` | `NCountViolated` | `countBad_iff` |

Not modelled: `TerminatesAtSink` and `JoinedOrDeadLettered` (quiescence conjoined with a sink /
`pending` clause, the same shape as the arms above), the environment-injection relaxation of
`encode_quiescent` (the model is env-free: `env_inject = []`), and the [EXEC-042] terminal
rewrite, which runs after the inert-place rewrite: it adds inhibitor arcs
(`inhibit_on_terminals`) and makes every terminal a sink and a conditional-sink marker for every
place (`with_net_terminals`); `TerminalRewrite.lean` models it on flat nets.

`DeadlockFree`'s `Bad` quantifies over flat indices, so a token on a name without an index can
never strand. That is the stray-token `Proven`; `Covers` is what excludes it, and
`Retrodict.lean` in this directory shows the pre-fix instance.
-/

namespace Libpetri.Novel.Seam

open Libpetri

variable {N : Type} [DecidableEq N]

/-! ## Quiescence as encoded -/

/-- The disable reasons `encode_quiescent` collects for one flat transition, over `p` places
with no injectable environment place: `(< m_i pre_i)` per `i < p` with `pre_i > 0`, `(> m_q 0)`
per inhibitor, `(< m_q 1)` per read arc. -/
def disableReasons (p : Nat) (t : Transition) : List (AMarking → Bool) :=
  ((List.range p).filter (fun i => 0 < pre t i)).map (fun i a => decide (a i < pre t i))
    ++ t.inhibitors.map (fun q a => decide (0 < a q))
    ++ t.reads.map (fun q a => decide (a q < 1))

/-- `smt_encoder.rs` `encode_quiescent` (no environment): `None` when some transition has no
disable reason (it is enabled in every marking), else the conjunction over transitions of the
disjunction of its reasons. -/
def encodeQuiescent (p : Nat) (flat : FlatNet) : Option (AMarking → Bool) :=
  if flat.any (fun ft => (disableReasons p ft.1).isEmpty) then none
  else some (fun a => flat.all (fun ft => (disableReasons p ft.1).any (fun r => r a)))

/-- The quiescence conjunct as a predicate, `false` for `None`. -/
def quiescentBad (p : Nat) (flat : FlatNet) (a : AMarking) : Bool :=
  match encodeQuiescent p flat with
  | none => false
  | some q => q a

/-- Inputs below `p` and at most one input arc per place: what every flat transition of a
flattened named net satisfies. -/
def FlatOK (p : Nat) (t : Transition) : Prop :=
  (∀ s ∈ t.inputs, s.place < p) ∧ InputsDistinctPlaces t

theorem pre_pos_spec {t : Transition} {i : Nat} (h : 0 < pre t i) :
    ∃ s ∈ t.inputs, s.place = i ∧ pre t i = s.card.required := by
  unfold pre at h ⊢
  cases hs : specAt t i with
  | none => rw [hs] at h; exact absurd h (Nat.lt_irrefl 0)
  | some s =>
    obtain ⟨hm, hp⟩ := specAt_sound hs
    exact ⟨s, hm, hp, rfl⟩

/-- A transition's disable reasons hold exactly when it is disabled. -/
theorem reasons_any {p : Nat} {t : Transition} (hok : FlatOK p t) (a : AMarking) :
    (disableReasons p t).any (fun r => r a) = !enabledA a t := by
  apply Bool.eq_iff_iff.mpr
  have hA : ((((List.range p).filter (fun i => 0 < pre t i)).map
        (fun i (a : AMarking) => decide (a i < pre t i))).any (fun r => r a)) = true ↔
      ∃ s ∈ t.inputs, a s.place < s.card.required := by
    simp only [List.any_map, List.any_eq_true, List.mem_filter, List.mem_range,
      Function.comp, decide_eq_true_eq]
    constructor
    · rintro ⟨i, ⟨-, hpos⟩, hlt⟩
      obtain ⟨s, hs, rfl, hpre⟩ := pre_pos_spec hpos
      exact ⟨s, hs, hpre ▸ hlt⟩
    · rintro ⟨s, hs, hlt⟩
      have hpre : pre t s.place = s.card.required := by
        unfold pre; rw [hok.2 s hs]
      exact ⟨s.place, ⟨hok.1 s hs, by omega⟩, by omega⟩
  have hB : (t.inhibitors.map (fun q (a : AMarking) => decide (0 < a q))).any (fun r => r a)
      = true ↔ ∃ q ∈ t.inhibitors, 0 < a q := by
    simp [List.any_map, Function.comp]
  have hC : (t.reads.map (fun q (a : AMarking) => decide (a q < 1))).any (fun r => r a)
      = true ↔ ∃ q ∈ t.reads, a q < 1 := by
    simp [List.any_map, Function.comp]
  have hE : enabledA a t = true ↔ (∀ s ∈ t.inputs, s.card.required ≤ a s.place) ∧
      (∀ q ∈ t.inhibitors, a q = 0) ∧ (∀ q ∈ t.reads, 1 ≤ a q) := by
    simp [enabledA, List.all_eq_true, and_assoc]
  have hN : ((!enabledA a t) = true) ↔ ¬ (enabledA a t = true) := by simp
  rw [disableReasons, List.any_append, List.any_append, Bool.or_eq_true, Bool.or_eq_true, hA, hB,
    hC, hN, hE]
  constructor
  · rintro ((⟨s, hs, h⟩ | ⟨q, hq, h⟩) | ⟨q, hq, h⟩) ⟨h1, h2, h3⟩
    · have := h1 s hs; omega
    · have := h2 q hq; omega
    · have := h3 q hq; omega
  · intro hn
    by_contra hc
    apply hn
    refine ⟨fun s hs => ?_, fun q hq => ?_, fun q hq => ?_⟩
    · by_contra h'; exact hc (Or.inl (Or.inl ⟨s, hs, by omega⟩))
    · by_contra h'; exact hc (Or.inl (Or.inr ⟨q, hq, by omega⟩))
    · by_contra h'; exact hc (Or.inr ⟨q, hq, by omega⟩)

/-- **`encode_quiescent` is exact**: the quiescence conjunct holds iff no flat transition is
enabled, including the `None` case (some transition is always enabled). -/
theorem quiescentBad_iff {p : Nat} {flat : FlatNet} (hok : ∀ ft ∈ flat, FlatOK p ft.1)
    (a : AMarking) :
    quiescentBad p flat a = true ↔ ∀ ft ∈ flat, enabledA a ft.1 = false := by
  unfold quiescentBad encodeQuiescent
  by_cases hany : flat.any (fun ft => (disableReasons p ft.1).isEmpty) = true
  · rw [if_pos hany]
    simp only [Bool.false_eq_true, false_iff, not_forall]
    obtain ⟨ft, hft, he⟩ := List.any_eq_true.mp hany
    refine ⟨ft, hft, ?_⟩
    have := reasons_any (hok ft hft) a
    rw [List.isEmpty_iff.mp he] at this
    simp at this
    simp [this]
  · rw [if_neg hany]
    simp only [List.all_eq_true]
    refine forall_congr' fun ft => forall_congr' fun hft => ?_
    rw [reasons_any (hok ft hft) a]
    simp

theorem flatOK_flatNet {ix : PlaceIndex N} {net : NNet N} (hA : ArcsIn ix net)
    (hD : InputsDistinct net) : ∀ ft ∈ flatNet ix net, FlatOK ix.size ft.1 := by
  intro ft' hft'
  refine ⟨?_, ((wellFormed_flatNet hA hD) ft' hft').1⟩
  obtain ⟨ft, hft, rfl⟩ := List.mem_map.mp hft'
  intro s' hs'
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
  exact ix.idx_lt ((hA.tin hft).inputs s hs)

/-- The encoded quiescence of the restriction is the named quiescence. -/
theorem quiescentBad_restrict {ix : PlaceIndex N} {net : NNet N} (hA : ArcsIn ix net)
    (hD : InputsDistinct net) (m : N → Nat) :
    quiescentBad ix.size (flatNet ix net) (restrict ix m) = true ↔ NQuiescent net m := by
  rw [quiescentBad_iff (flatOK_flatNet hA hD)]
  unfold NQuiescent flatNet
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  refine forall_congr' fun ft => forall_congr' fun hft => ?_
  rw [flatFT, enabledA_restrict ix (hA.tin hft)]

/-! ## `DeadlockFree` -/

/-- `stranded_conditions` over the excuses: one disjunct per indexed place whose entry is
`Some ms`: `(>= m_i 1)` and `(= m_k 0)` for every `k ∈ ms`. -/
def strandedDisjuncts (ix : PlaceIndex N) (e : Excuses) : List (AMarking → Bool) :=
  (List.range ix.size).filterMap fun i =>
    (e i).map fun ms a => decide (1 ≤ a i) && ms.all (fun k => a k == 0)

/-- **`DeadlockFree`'s `Bad`, as encoded** (`encode_property_violation`): `false` when no
marking is quiescent or no place can strand, else quiescent and some disjunct. -/
def deadlockBad (flat : FlatNet) (ix : PlaceIndex N) (sinks : List N)
    (cond : List (CondSinks N)) (a : AMarking) : Bool :=
  match encodeQuiescent ix.size flat with
  | none => false
  | some q =>
    let s := strandedDisjuncts ix (strandingExcuses ix sinks cond)
    if s.isEmpty then false else q a && s.any (fun d => d a)

/-- Where a token may rest in `m` (`rest_set.rs` `resting_names`): a declared sink, a marker, or
a place of a declaration whose marker `m` marks. -/
def Resting (sinks : List N) (cond : List (CondSinks N)) (m : N → Nat) (n : N) : Prop :=
  n ∈ sinks ∨ IsMarker cond n ∨ ∃ c ∈ cond, m c.marker ≠ 0 ∧ n ∈ c.places

/-- **The named deadlock** ([VER-002] `DeadlockFree` violated): no transition enabled and some
marked place, of any name, where resting is not permitted (`rest_set.rs` `strands_token`). -/
def NDeadlock (net : NNet N) (sinks : List N) (cond : List (CondSinks N)) (m : N → Nat) : Prop :=
  NQuiescent net m ∧ ∃ n, m n ≠ 0 ∧ ¬ Resting sinks cond m n

theorem deadlockBad_eq (flat : FlatNet) (ix : PlaceIndex N) (sinks : List N)
    (cond : List (CondSinks N)) (a : AMarking) :
    deadlockBad flat ix sinks cond a = true ↔
      quiescentBad ix.size flat a = true ∧
      ∃ i < ix.size, ∃ ms, strandingExcuses ix sinks cond i = some ms ∧ 1 ≤ a i ∧
        ∀ k ∈ ms, a k = 0 := by
  have hs : (strandedDisjuncts ix (strandingExcuses ix sinks cond)).any (fun d => d a) = true ↔
      ∃ i < ix.size, ∃ ms, strandingExcuses ix sinks cond i = some ms ∧ 1 ≤ a i ∧
        ∀ k ∈ ms, a k = 0 := by
    simp only [strandedDisjuncts, List.any_eq_true, List.mem_filterMap, List.mem_range]
    constructor
    · rintro ⟨d, ⟨i, hi, hd⟩, hda⟩
      cases he : strandingExcuses ix sinks cond i with
      | none => rw [he] at hd; simp at hd
      | some ms =>
        rw [he] at hd
        simp only [Option.map_some, Option.some.injEq] at hd
        subst hd
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hda
        exact ⟨i, hi, ms, he, hda.1, hda.2⟩
    · rintro ⟨i, hi, ms, he, h1, h2⟩
      refine ⟨_, ⟨i, hi, by rw [he]; rfl⟩, ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq]
      exact ⟨h1, h2⟩
  unfold deadlockBad quiescentBad
  cases encodeQuiescent ix.size flat with
  | none => simp
  | some q =>
    simp only
    by_cases hemp : (strandedDisjuncts ix (strandingExcuses ix sinks cond)).isEmpty = true
    · rw [if_pos hemp]
      have hnil := List.isEmpty_iff.mp hemp
      rw [hnil] at hs
      simp only [Bool.false_eq_true, false_iff, not_and]
      intro _ hex
      exact absurd (hs.mpr hex) (by simp)
    · rw [if_neg hemp, Bool.and_eq_true, hs]

/-- **`DeadlockFree`'s `Bad` is exact on covered markings.** On the restriction of a named
marking the index covers, the encoded violation holds iff the named marking is a deadlock that
strands a token. -/
theorem deadlockBad_iff {ix : PlaceIndex N} {net : NNet N} (hA : ArcsIn ix net)
    (hD : InputsDistinct net) (sinks : List N) (cond : List (CondSinks N)) {m : N → Nat}
    (h : Covers ix m) :
    deadlockBad (flatNet ix net) ix sinks cond (restrict ix m) = true ↔
      NDeadlock net sinks cond m := by
  have spec := strandingExcuses_spec ix sinks cond
  rw [deadlockBad_eq, quiescentBad_restrict hA hD]
  unfold NDeadlock
  refine and_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨i, hi, ms, he, h1, h2⟩
    have hname : ix.name? i = some ix.names[i] := List.getElem?_eq_getElem hi
    set n := ix.names[i]
    have hri : restrict ix m i = m n := by simp [restrict, hname]
    refine ⟨n, by rw [hri] at h1; omega, ?_⟩
    rintro (hs | hm | ⟨c, hc, hmk, hn⟩)
    · exact absurd ((spec.none_iff i n hname).mpr (Or.inl hs)) (by rw [he]; simp)
    · exact absurd ((spec.none_iff i n hname).mpr (Or.inr hm)) (by rw [he]; simp)
    · have hcm : c.marker ∈ ix.names := h c.marker hmk
      have hk : ix.idx c.marker ∈ ms :=
        (spec.mem_iff i n ms hname he _).mpr ⟨c, hc, hcm, rfl, hn⟩
      have := h2 _ hk
      rw [restrict_idx ix m hcm] at this
      exact hmk this
  · rintro ⟨n, hn, hnr⟩
    have hmem : n ∈ ix.names := h n hn
    have hname := ix.name?_idx hmem
    refine ⟨ix.idx n, ix.idx_lt hmem, ?_⟩
    cases he : strandingExcuses ix sinks cond (ix.idx n) with
    | none =>
      exfalso
      rcases (spec.none_iff _ n hname).mp he with hs | hm
      · exact hnr (Or.inl hs)
      · exact hnr (Or.inr (Or.inl hm))
    | some ms =>
      refine ⟨ms, rfl, by rw [restrict_idx ix m hmem]; omega, fun k hk => ?_⟩
      obtain ⟨c, hc, hcm, rfl, hnc⟩ := (spec.mem_iff _ n ms hname he k).mp hk
      rw [restrict_idx ix m hcm]
      by_contra hne
      exact hnr (Or.inr (Or.inr ⟨c, hc, hne, hnc⟩))

/-! ## `PlaceBound`, `BranchPlaceBound` -/

/-- `(> m_p bound)` for a resolving place, `false` otherwise. -/
def placeBoundBad (ix : PlaceIndex N) (n : N) (k : Nat) (a : AMarking) : Bool :=
  match ix.lookup n with
  | some i => decide (k < a i)
  | none => false

/-- **Exact on covered markings**, with no resolution premise: an unresolved place is unmarked in
a covered marking, so its bound holds, and the `false` fallback says so. -/
theorem placeBoundBad_iff {ix : PlaceIndex N} {m : N → Nat} (h : Covers ix m) (n : N) (k : Nat) :
    placeBoundBad ix n k (restrict ix m) = true ↔ k < m n := by
  cases hl : ix.lookup n with
  | none => simp [placeBoundBad, hl, covers_zero h (ix.lookup_eq_none.mp hl)]
  | some i =>
    obtain ⟨hmem, rfl⟩ := ix.lookup_eq_some.mp hl
    simp [placeBoundBad, hl, restrict_idx ix m hmem]

/-! ## `MutualExclusion` (pairwise, [VER-002])

`encode_property_violation`'s `MutualExclusion` arm resolves the listed names (`filter_map` over
`flat.place_index`, keeping duplicates and list order) and hands one `(>= m_i 1)` term per entry
to `pairwise_marked`: `false` below two entries, `(and a b)` for two, and the disjunction of the
pairs' conjunctions, positions `i < j` in lexicographic order, beyond. Its Boolean meaning is
`Pairwise.pairsOf` of the resolved list, each pair "both marked". Before the pairwise rule the
arm was `allMarkedBad` below, which reads a list of three or more as "every place marked", while
the graph routes read "two marked" — the two routes disagreed.

No resolution premise: a name without an index is unmarked on a covered marking, so dropping it
changes neither side's count of marked entries. -/

/-- `pairwise_marked` over the resolving places (`smt_encoder.rs`). -/
def pairMarkedBad (ix : PlaceIndex N) (places : List N) (a : AMarking) : Bool :=
  (Pairwise.pairsOf (places.filterMap ix.lookup)).any
    (fun p => decide (1 ≤ a p.1) && decide (1 ≤ a p.2))

/-- **[VER-002] `MutualExclusion` violated**, by name: two entries of the list (at different
positions) marked at once. A name listed twice pairs with itself. -/
def NTwoMarked (places : List N) (m : N → Nat) : Prop :=
  2 ≤ (places.filter (fun n => decide (1 ≤ m n))).length

/-- Resolving the names loses no marked entry of a covered marking. -/
theorem filterMap_marked_length {ix : PlaceIndex N} {m : N → Nat} (h : Covers ix m) :
    ∀ places : List N,
      ((places.filterMap ix.lookup).filter (fun i => decide (1 ≤ restrict ix m i))).length =
        (places.filter (fun n => decide (1 ≤ m n))).length
  | [] => rfl
  | n :: ns => by
    have ih := filterMap_marked_length h ns
    cases hl : ix.lookup n with
    | none =>
      have h0 : m n = 0 := covers_zero h (ix.lookup_eq_none.mp hl)
      simp [hl, h0, ih]
    | some i =>
      obtain ⟨hmem, rfl⟩ := ix.lookup_eq_some.mp hl
      have hr := restrict_idx ix m hmem
      by_cases hm : 1 ≤ m n
      · simp [hl, hr, hm, ih]
      · simp [hl, hr, hm, ih]

/-- **Exact on covered markings**, with no resolution premise and for a list of any length
(duplicates included): the encoded pairwise disjunction holds iff two entries are marked. -/
theorem pairMarkedBad_iff {ix : PlaceIndex N} {m : N → Nat} (h : Covers ix m) (places : List N) :
    pairMarkedBad ix places (restrict ix m) = true ↔ NTwoMarked places m := by
  unfold pairMarkedBad NTwoMarked
  rw [← filterMap_marked_length h places]
  exact Pairwise.any_pairsOf_iff (fun i => decide (1 ≤ restrict ix m i)) _

/-- Two places: `MutualExclusion(p, q)` is violated iff both are marked — [VER-002]'s two-place
form, and the reference's (`Reference/Semantics.lean` `mutualExclusion`). -/
theorem pairMarkedBad_pair {ix : PlaceIndex N} {m : N → Nat} (h : Covers ix m) (p q : N) :
    pairMarkedBad ix [p, q] (restrict ix m) = true ↔ 1 ≤ m p ∧ 1 ≤ m q := by
  rw [pairMarkedBad_iff h, NTwoMarked]
  by_cases hp : 1 ≤ m p <;> by_cases hq : 1 ≤ m q <;> simp [hp, hq]

/-- Fewer than two entries: never violated. -/
theorem pairMarkedBad_short {ix : PlaceIndex N} {m : N → Nat} (h : Covers ix m) {places : List N}
    (hl : places.length < 2) : pairMarkedBad ix places (restrict ix m) = false := by
  have : ¬ NTwoMarked places m := by
    unfold NTwoMarked
    have := List.length_filter_le (fun n => decide (1 ≤ m n)) places
    omega
  cases hb : pairMarkedBad ix places (restrict ix m) with
  | false => rfl
  | true => exact absurd ((pairMarkedBad_iff h places).mp hb) this

/-! ## `Unreachable` -/

/-- `(and (>= m_p 1) …)` over the resolving places, `false` when none resolves. -/
def allMarkedBad (ix : PlaceIndex N) (places : List N) (a : AMarking) : Bool :=
  if (places.filterMap ix.lookup).isEmpty then false
  else (places.filterMap ix.lookup).all (fun i => decide (1 ≤ a i))

/-- Sound direction: a covered marking that marks every (of a non-empty list of) places is
caught. -/
theorem allMarkedBad_of {ix : PlaceIndex N} {m : N → Nat} (h : Covers ix m) {places : List N}
    (hne : places ≠ []) (hall : ∀ n ∈ places, 1 ≤ m n) :
    allMarkedBad ix places (restrict ix m) = true := by
  have hres : ∀ n ∈ places, n ∈ ix.names := fun n hn => h n (by have := hall n hn; omega)
  unfold allMarkedBad
  obtain ⟨n0, hn0⟩ := List.exists_mem_of_ne_nil places hne
  have hne' : ¬ (places.filterMap ix.lookup).isEmpty = true := by
    rw [List.isEmpty_iff]
    intro hnil
    have : ix.idx n0 ∈ places.filterMap ix.lookup :=
      List.mem_filterMap.mpr ⟨n0, hn0, ix.lookup_eq_some.mpr ⟨hres n0 hn0, rfl⟩⟩
    rw [hnil] at this
    exact List.not_mem_nil this
  rw [if_neg hne']
  simp only [List.all_eq_true, List.mem_filterMap, decide_eq_true_eq]
  rintro i ⟨n, hn, hl⟩
  obtain ⟨hmem, rfl⟩ := ix.lookup_eq_some.mp hl
  rw [restrict_idx ix m hmem]
  exact hall n hn

/-- **Exact on covered markings** when every named place resolves (what
`unresolved_property_place_in_net` enforces before any route runs: it refuses a property any of
whose `property_place_names` — here the `Unreachable` place list — the net does not declare)
and the list is non-empty. -/
theorem allMarkedBad_iff {ix : PlaceIndex N} {m : N → Nat} (h : Covers ix m) {places : List N}
    (hres : ∀ n ∈ places, n ∈ ix.names) (hne : places ≠ []) :
    allMarkedBad ix places (restrict ix m) = true ↔ ∀ n ∈ places, 1 ≤ m n := by
  refine ⟨fun hb n hn => ?_, allMarkedBad_of h hne⟩
  unfold allMarkedBad at hb
  split at hb
  · exact absurd hb (by simp)
  · have hi : ix.idx n ∈ places.filterMap ix.lookup :=
      List.mem_filterMap.mpr ⟨n, hn, ix.lookup_eq_some.mpr ⟨hres n hn, rfl⟩⟩
    have := List.all_eq_true.mp hb _ hi
    rw [restrict_idx ix m (hres n hn)] at this
    simpa using this

/-! ## `QuiescentCount` -/

-- Keep core's `Zero ℕ` for `List.sum`, as `Strengthening.lean` elaborates `quiescentCountBad`.
attribute [local instance high] Zero.ofOfNat0

/-- `smt_encoder.rs` `index_ordered`: the resolving indices, deduplicated (the ascending sort is
omitted: only the sum and `all` read the list). -/
def indexOrdered (ix : PlaceIndex N) (names : List N) : List Nat :=
  (names.filterMap ix.lookup).dedup

/-- The `QuiescentCount` arm as encoded: `Strengthening.lean`'s `quiescentCountBad` (the model
of `count_violation_condition`, conjoined with quiescence) with `encode_quiescent` and
`index_ordered` plugged in. -/
def countBad (flat : FlatNet) (ix : PlaceIndex N) (places waivers : List N) (min : Nat)
    (max : Option Nat) (a : AMarking) : Bool :=
  quiescentCountBad (encodeQuiescent ix.size flat) (indexOrdered ix places)
    (indexOrdered ix waivers) min max a

/-- The named count over a place set (each name once). -/
def ncount (places : List N) (m : N → Nat) : Nat := (places.dedup.map m).sum

/-- **[VER-002] `QuiescentCount` violated**, by name. -/
def NCountViolated (net : NNet N) (places waivers : List N) (min : Nat) (max : Option Nat)
    (m : N → Nat) : Prop :=
  NQuiescent net m ∧
    ((ncount places m < min ∧ ∀ w ∈ waivers, m w = 0) ∨ ∃ k, max = some k ∧ k < ncount places m)

omit [DecidableEq N] in
theorem sum_filter_of_zero {f : N → Nat} {p : N → Bool} :
    ∀ {l : List N}, (∀ x ∈ l, p x = false → f x = 0) → ((l.filter p).map f).sum = (l.map f).sum
  | [], _ => rfl
  | x :: xs, h => by
    have ih := sum_filter_of_zero (fun y hy => h y (List.mem_cons_of_mem x hy))
    cases hp : p x with
    | true => simp [hp, ih]
    | false => simp [hp, ih, h x List.mem_cons_self hp]

theorem indexOrdered_sum {ix : PlaceIndex N} {m : N → Nat} (h : Covers ix m) (places : List N) :
    ((indexOrdered ix places).map (restrict ix m)).sum = ncount places m := by
  let L2 := (places.dedup.filter (fun n => decide (n ∈ ix.names))).map ix.idx
  have hnd2 : L2.Nodup := by
    refine List.Nodup.map_on (fun x hx y _ hxy => ?_) ((List.nodup_dedup _).filter _)
    exact (ix.idx_inj (by simpa using (List.mem_filter.mp hx).2)).mp hxy
  have hperm : (indexOrdered ix places).Perm L2 := by
    refine (List.perm_ext_iff_of_nodup (List.nodup_dedup _) hnd2).mpr fun k => ?_
    simp only [List.mem_dedup, List.mem_filterMap, L2, List.mem_map,
      List.mem_filter, decide_eq_true_eq, ix.lookup_eq_some]
    constructor
    · rintro ⟨n, hn, hm, rfl⟩; exact ⟨n, ⟨hn, hm⟩, rfl⟩
    · rintro ⟨n, ⟨hn, hm⟩, rfl⟩; exact ⟨n, hn, hm, rfl⟩
  rw [(hperm.map _).sum_nat, List.map_map, ncount]
  have hcomp : ∀ n ∈ places.dedup.filter (fun n => decide (n ∈ ix.names)),
      (restrict ix m ∘ ix.idx) n = m n := fun n hn =>
    restrict_idx ix m (by simpa using (List.mem_filter.mp hn).2)
  rw [List.map_congr_left hcomp]
  exact sum_filter_of_zero fun n _ hp => covers_zero h (by simpa using hp)

theorem indexOrdered_waivers {ix : PlaceIndex N} {m : N → Nat} (h : Covers ix m)
    (waivers : List N) :
    ((indexOrdered ix waivers).all fun w => restrict ix m w == 0) = true ↔
      ∀ w ∈ waivers, m w = 0 := by
  simp only [List.all_eq_true, indexOrdered, List.mem_dedup, List.mem_filterMap, beq_iff_eq,
    ix.lookup_eq_some]
  constructor
  · intro hall w hw
    by_cases hmem : w ∈ ix.names
    · have := hall _ ⟨w, hw, hmem, rfl⟩
      rwa [restrict_idx ix m hmem] at this
    · exact covers_zero h hmem
  · rintro hall _ ⟨w, hw, hmem, rfl⟩
    rw [restrict_idx ix m hmem]
    exact hall w hw

/-- **`QuiescentCount`'s `Bad` is exact on covered markings.** No resolution premise: an
unresolved counted place or waiver is unmarked in a covered marking. -/
theorem countBad_iff {ix : PlaceIndex N} {net : NNet N} (hA : ArcsIn ix net)
    (hD : InputsDistinct net) (places waivers : List N) (min : Nat) (max : Option Nat)
    {m : N → Nat} (h : Covers ix m) :
    countBad (flatNet ix net) ix places waivers min max (restrict ix m) = true ↔
      NCountViolated net places waivers min max m := by
  unfold countBad NCountViolated
  rw [quiescent_count_clause_exact, indexOrdered_sum h]
  have hq : (∃ q, encodeQuiescent ix.size (flatNet ix net) = some q ∧ q (restrict ix m) = true)
      ↔ NQuiescent net m := by
    rw [← quiescentBad_restrict hA hD m, quiescentBad]
    cases encodeQuiescent ix.size (flatNet ix net) <;> simp
  have hw : (∀ w ∈ indexOrdered ix waivers, restrict ix m w = 0) ↔ ∀ w ∈ waivers, m w = 0 := by
    rw [← indexOrdered_waivers h]
    simp
  rw [hq, hw]

end Libpetri.Novel.Seam
