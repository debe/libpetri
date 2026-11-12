import Libpetri.Novel.TimedScg
import Libpetri.Spec.Verifier.Graph
import Mathlib.Data.List.Sort

set_option linter.missingDocs true
set_option autoImplicit false

/-!
# The timed class-key layer of the verifier (RefVerifier L3)

`Novel/TimedScg` models one step of the timed state-class graph (`compute_successor`), the timed
semantics `TStep`, and proves that every timed run stays in classes the graph reaches. It leaves
three things open, which this file supplies: the names of the transitions and the canonical
clock order as a concrete function (the model has an abstract order `co`, premise 5 of
`Succ.lean`), the class key the graph deduplicates by (premise 7), and the graph as a build at an
explorer of `Novel.RouteB.Decide`, so the graph layer (`Spec/Verifier/Graph.lean`: edges, the
shortest witness, closed and truncated, the cache) applies to the timed graph as it does to the
enumeration route.

* **Names and the canonical order** (`codePoints`, `nameOf`, `coByName`): a clock list in name
  order, compared by Unicode code point, is left alone; otherwise its positions are sorted by
  name with a stable sort, as `canonical_order` does. `coByName_wf` discharges premise 5;
  `reorder_sorted` and `reorder_perm`: the reordered clocks are the same clocks, in name order;
  `reorder_eq_of_perm`: with distinct names, the order the transitions became enabled in is
  forgotten.
* **The class key** (`classKey`): the marking, the clock names in clock order, and every bound of
  the firing domain, the bounds between two clocks included (`StateClass::canonical_key`). The
  explorer keys by `idxKey` (clock indices in place of names), which is the same test on a net
  with unique names (`idxKey_eq_iff_classKey`).
* **Equal zones have equal canonical matrices** (`canon_unique`, `corner_eq_iff_zone`): two
  firing domains that are closed, zero on the diagonal and have a finite reference row agree on
  every bound when they hold the same firing times. The proof shows each bound is tight: a
  valuation of the zone meets it (`canon_witness`, `canon_tight`). Every class the graph reaches
  has such a domain (`graph_canon`), when the emptiness check is exact (`ExactEps`: `eps = 0`, or
  the Rust `EPSILON = 1e-9` on whole-millisecond bounds).
* **One marking, one clock list** (`graph_cs_eq`): two classes of the graph with the same marking
  list the same clocks in the same order. With the uniqueness above, `classKey_eq_iff`: two
  classes have one key exactly when they have one marking and one zone. `stored_one_class`: a
  build stores such classes once.
* **The explorer** (`scgE`, `succL`): the successors of a class with their labels, the fired
  transition's name and the index of the outcome row (`StateClassEdge`). The successor reads only
  the marking, the clocks and the corner of the domain (`succWith_congr`), so the explorer is
  key-equivariant (`scgE_equivariant`), and its reachability is the graph's (`scgE_reach_iff`).
* **Coverage** (`timed_run_stored`, `timed_safety_closed`, `scgGraph_covers`): a closed graph
  built with key dedup holds every state of every timed run. This is `Run.timed_markings_discovered`
  with premise 7 discharged: the build dedups by key, not by equality of classes.

Out of scope here: the exact half of the successor (every class is realised by a timed run,
ruling D67), the bridge from the reference executor's on-time and late steps to `TStep` (premise
9 of `Succ.lean`, the J7 and J8 bridges), environment places and match transitions (premise 8),
and the string form of the key.
-/

namespace Libpetri.Spec.Verifier.Scg

open Libpetri Libpetri.Novel.TimedScg Libpetri.Novel.ForwardDeposit Libpetri.Novel.RouteB
open Libpetri.Novel.Dbm (Bound)

/-! ## Transition names and the canonical clock order -/

/-- The code points of a name. -/
def codePoints (s : String) : List Nat := s.toList.map Char.toNat

theorem codePoints_inj : Function.Injective codePoints := by
  intro a b h
  have hc : Function.Injective Char.toNat := fun x y hxy => by
    rw [← Char.ofNat_toNat x, ← Char.ofNat_toNat y, hxy]
  exact String.toList_inj.mp (List.map_injective_iff.mpr hc h)

/-- The name of transition `i` of a timed net (`""` outside the net). -/
def nameOf (N : TNet) (i : Nat) : String := (trOf N i).name

/-- The sort key of transition `i`: the code points of its name. -/
def nameKey (N : TNet) (i : Nat) : List Nat := codePoints (nameOf N i)

/-- Transition names are unique (premise 1 of `Succ.lean`). -/
def NamesUnique (N : TNet) : Prop :=
  ∀ i j, i < N.length → j < N.length → nameOf N i = nameOf N j → i = j

/-- On a net with unique names, the sort key tells transitions apart. -/
theorem nameKey_inj {N : TNet} (hN : NamesUnique N) {i j : Nat} (hi : i < N.length)
    (hj : j < N.length) (h : nameKey N i = nameKey N j) : i = j :=
  hN i j hi hj (codePoints_inj h)

/-- One name not after another, by code point. -/
def nameLe (N : TNet) (a b : Nat) : Bool := decide (nameKey N a ≤ nameKey N b)

/-- `names.windows(2).all(|w| w[0] <= w[1])`: every two neighbours in order. -/
def inOrder (N : TNet) : List Nat → Bool
  | a :: b :: t => nameLe N a b && inOrder N (b :: t)
  | _ => true

theorem pairwise_of_inOrder {N : TNet} :
    ∀ {l : List Nat}, inOrder N l = true → l.Pairwise (fun a b => nameKey N a ≤ nameKey N b)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: t, h => by
    simp only [inOrder, Bool.and_eq_true, nameLe, decide_eq_true_eq] at h
    have ih := pairwise_of_inOrder h.2
    refine List.Pairwise.cons (fun c hc => ?_) ih
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h.1
    · exact le_trans h.1 (List.rel_of_pairwise_cons ih hc)

/-- The order the canonical clock order sorts positions by: position `a` of the clock list `l`
not after position `b` when its transition's name is not after the other's. -/
def posLe (N : TNet) (l : List Nat) (a b : Nat) : Prop := nameKey N (l.getD a 0) ≤ nameKey N (l.getD b 0)

instance (N : TNet) (l : List Nat) : DecidableRel (posLe N l) := fun a b => by
  unfold posLe; infer_instance

/-- **The canonical clock order** (`canonical_order`, `state_class_graph.rs`): `none` when the
clocks are already in name order, otherwise the positions sorted by name with a stable sort, so
equal names keep their incoming order. The Rust sorts with the stable `sort_by`, the model with a
stable insertion sort: both give the one stable sorted order. -/
def coByName (N : TNet) (l : List Nat) : Option (List Nat) :=
  if inOrder N l then none
  else some ((List.range l.length).insertionSort (posLe N l))

/-- `coByName` returns a permutation of the positions (premise 5 of `Succ.lean`). -/
theorem coByName_wf (N : TNet) : CoWF (coByName N) := by
  intro l ord h
  unfold coByName at h
  split_ifs at h
  cases h
  exact ⟨by simp, fun x hx => by simpa using hx, fun i hi => by simpa using hi⟩

theorem map_getD_range (l : List Nat) : (List.range l.length).map (fun i => l.getD i 0) = l := by
  apply List.ext_getElem (by simp)
  intro i _ h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- The clocks in canonical order, unfolded. -/
theorem reorder_byName (N : TNet) (l : List Nat) :
    reorder (coByName N) l = if inOrder N l then l
      else ((List.range l.length).insertionSort (posLe N l)).map fun i => l.getD i 0 := by
  unfold reorder coByName
  split_ifs <;> rfl

/-- Reordering keeps the clocks: it is a permutation of them. -/
theorem reorder_perm (N : TNet) (l : List Nat) : (reorder (coByName N) l).Perm l := by
  rw [reorder_byName]
  split_ifs
  · exact List.Perm.refl _
  · have := (List.perm_insertionSort (posLe N l) (List.range l.length)).map (fun i => l.getD i 0)
    rwa [map_getD_range] at this

/-- **The reordered clocks are in name order.** -/
theorem reorder_sorted (N : TNet) (l : List Nat) :
    (reorder (coByName N) l).Pairwise (fun a b => nameKey N a ≤ nameKey N b) := by
  rw [reorder_byName]
  split_ifs with h
  · exact pairwise_of_inOrder h
  · rw [List.pairwise_map]
    haveI : Std.Total (posLe N l) := ⟨fun a b => le_total _ _⟩
    haveI : IsTrans Nat (posLe N l) := ⟨fun a b c h1 h2 => le_trans h1 h2⟩
    exact List.pairwise_insertionSort (posLe N l) (List.range l.length)

/-- Two lists sorted by a key that tells their members apart, and permutations of each other,
are equal. -/
theorem eq_of_perm_sorted {κ : Nat → List Nat} {l₁ l₂ : List Nat} (hp : l₁.Perm l₂)
    (h₁ : l₁.Pairwise (fun a b => κ a ≤ κ b)) (h₂ : l₂.Pairwise (fun a b => κ a ≤ κ b))
    (hinj : ∀ a ∈ l₁, ∀ b ∈ l₁, κ a = κ b → a = b) : l₁ = l₂ :=
  List.Perm.eq_of_pairwise
    (fun a b ha hb hab hba => hinj a ha b (hp.symm.subset hb) (le_antisymm hab hba)) h₁ h₂ hp

/-- **The canonical order forgets the enabling order**: two orders of the same clocks with
distinct names give one clock list. -/
theorem reorder_eq_of_perm (N : TNet) {l₁ l₂ : List Nat} (hp : l₁.Perm l₂)
    (hn : (l₁.map (nameKey N)).Nodup) : reorder (coByName N) l₁ = reorder (coByName N) l₂ := by
  refine eq_of_perm_sorted ((reorder_perm N l₁).trans (hp.trans (reorder_perm N l₂).symm))
    (reorder_sorted N l₁) (reorder_sorted N l₂) fun a ha b hb hab => ?_
  exact List.inj_on_of_nodup_map hn ((reorder_perm N l₁).subset ha)
    ((reorder_perm N l₁).subset hb) hab

/-! ## The class key -/

/-- The `d × d` corner of a positional matrix, row by row: the matrix a key renders. -/
def corner (d : Nat) (D : NMat) : List (List Bound) :=
  (List.range d).map fun i => (List.range d).map fun j => D i j

/-- Two matrices agree on their `d × d` corner. -/
def Agree (d : Nat) (D D' : NMat) : Prop := ∀ i j, i < d → j < d → D i j = D' i j

theorem corner_eq_iff {d : Nat} {D D' : NMat} : corner d D = corner d D' ↔ Agree d D D' := by
  constructor
  · intro h i j hi hj
    have h1 := congrArg (fun c => (c[i]?).bind fun r => r[j]?) h
    simpa [corner, hi, hj] using h1
  · intro h
    unfold corner
    refine List.map_congr_left fun i hi => List.map_congr_left fun j hj => ?_
    exact h i j (List.mem_range.mp hi) (List.mem_range.mp hj)

/-- A zone reads only its corner. -/
theorem satN_agree {d : Nat} {D D' : NMat} (h : Agree d D D') (θ : Nat → ℚ) :
    SatN d D θ ↔ SatN d D' θ := by
  unfold SatN
  constructor
  · intro hs i j hi hj; rw [← h i j hi hj]; exact hs i j hi hj
  · intro hs i j hi hj; rw [h i j hi hj]; exact hs i j hi hj

/-- **The class key** (`StateClass::canonical_key`): the marking, the clock names in clock
order, and every bound of the firing domain, the bounds between two clocks included. -/
structure ClassKey where
  /-- The marking (`MarkingState::canonical_key`). -/
  m : AMarking
  /-- The clock names, in clock order (`Dbm::clock_names`). -/
  names : List String
  /-- The full firing domain, row by row (`Dbm::data`). -/
  zone : List (List Bound)

/-- The key of a class. -/
def classKey (N : TNet) (C : Cls) : ClassKey :=
  ⟨C.m, C.cs.map (nameOf N), corner (C.cs.length + 1) C.D⟩

/-- The key the model's explorer dedups by: the clock indices in place of their names. On a net
with unique names it is the class key (`idxKey_eq_iff`). -/
structure IdxKey where
  /-- The marking. -/
  m : AMarking
  /-- The clocks, as transition indices in clock order. -/
  cs : List Nat
  /-- The full firing domain, row by row. -/
  zone : List (List Bound)

/-- The index key of a class. -/
def idxKey (C : Cls) : IdxKey := ⟨C.m, C.cs, corner (C.cs.length + 1) C.D⟩

theorem idxKey_eq_iff {C C' : Cls} :
    idxKey C = idxKey C' ↔ C.m = C'.m ∧ C.cs = C'.cs ∧ Agree (C.cs.length + 1) C.D C'.D := by
  unfold idxKey
  constructor
  · intro h
    simp only [IdxKey.mk.injEq] at h
    obtain ⟨hm, hcs, hz⟩ := h
    refine ⟨hm, hcs, corner_eq_iff.mp ?_⟩
    rw [hz, hcs]
  · rintro ⟨hm, hcs, hz⟩
    simp only [IdxKey.mk.injEq]
    refine ⟨hm, hcs, ?_⟩
    rw [corner_eq_iff.mpr hz, hcs]

/-! ## Canonical zones: equal zones have equal matrices -/

/-- A canonical firing domain of dimension `d`: closed (no bound exceeds a two-step detour),
zero on the diagonal, and a finite reference row (every clock has a finite lower bound). -/
structure CanonZone (d : Nat) (D : NMat) : Prop where
  /-- The reference clock is there. -/
  pos : 0 < d
  /-- Closed. -/
  closed : ∀ i j k, i < d → j < d → k < d → D i j ≤ D i k + D k j
  /-- Zero on the diagonal. -/
  diag : ∀ i, i < d → D i i = 0
  /-- A finite reference row. -/
  ref : ∀ i, i < d → D 0 i ≠ ⊤

/-- A finite bound as a rational (`0` for `⊤`, never read). -/
def fin (x : Bound) : ℚ := match x with | some q => q | none => 0

theorem coe_fin {x : Bound} (h : x ≠ ⊤) : ((fin x : ℚ) : Bound) = x := by
  cases x using WithTop.recTopCoe with
  | top => exact absurd rfl h
  | coe q => rfl

theorem fin_coe (q : ℚ) : fin (q : Bound) = q := rfl

section Tight

variable {d : Nat} {D : NMat}

/-- **The witness valuation of a canonical zone.** For a clock `i` and a shift `K` large enough
that `K` plus `i`'s reference bound is not negative, the valuation `θ k = -min (D i k) (K + r k)`
(`r` the reference row) lies in the zone and puts every clock `j` exactly
`min (D i j) (K + r j)` behind `i`. -/
theorem canon_witness (hD : CanonZone d D) {i : Nat} (hi : i < d) (K : ℚ)
    (hK : 0 ≤ K + fin (D 0 i)) :
    ∃ θ : Nat → ℚ, SatN d D θ ∧ ∀ j, j < d →
      ((θ i - θ j : ℚ) : Bound) = min (D i j) ((K + fin (D 0 j) : ℚ) : Bound) := by
  let e : Nat → Bound := fun k => min (D i k) ((K + fin (D 0 k) : ℚ) : Bound)
  have he : ∀ k, e k ≠ ⊤ := fun k => ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ _)
  let θ : Nat → ℚ := fun k => -fin (e k)
  have hθ : ∀ a b, ((θ a - θ b : ℚ) : Bound) = ((fin (e b) - fin (e a) : ℚ) : Bound) := by
    intro a b; congr 1; simp only [θ]; ring
  -- the step bound
  have hstep : ∀ a b, a < d → b < d → e b ≤ e a + D a b := by
    intro a b ha hb
    have h1 : D i b ≤ D i a + D a b := hD.closed i b a hi hb ha
    have h2 : ((K + fin (D 0 b) : ℚ) : Bound) ≤ ((K + fin (D 0 a) : ℚ) : Bound) + D a b := by
      have hc := hD.closed 0 b a (hD.pos) hb ha
      rw [← coe_fin (hD.ref b hb), ← coe_fin (hD.ref a ha)] at hc
      rw [WithTop.coe_add, WithTop.coe_add, add_assoc]
      exact add_le_add (le_refl _) hc
    calc e b ≤ min (D i a + D a b) (((K + fin (D 0 a) : ℚ) : Bound) + D a b) :=
          min_le_min h1 h2
      _ = e a + D a b := (min_add_add_right _ _ _)
  refine ⟨θ, fun a b ha hb => ?_, fun j _ => ?_⟩
  · rw [hθ]
    have hs := hstep a b ha hb
    cases hab : D a b using WithTop.recTopCoe with
    | top => exact le_top
    | coe c =>
      rw [hab, ← coe_fin (he b), ← coe_fin (he a), ← WithTop.coe_add, WithTop.coe_le_coe] at hs
      rw [WithTop.coe_le_coe]
      linarith
  · have hei : e i = 0 := by
      simp only [e, hD.diag i hi]
      exact min_eq_left (by exact_mod_cast hK)
    rw [hθ, hei, show fin (0 : Bound) = 0 from rfl, sub_zero, coe_fin (he j)]

/-- **A canonical zone's bounds are tight**: a bound every valuation of the zone respects is at
least the matrix entry. -/
theorem canon_tight (hD : CanonZone d D) {i j : Nat} (hi : i < d) (hj : j < d) {x : Bound}
    (h : ∀ θ, SatN d D θ → ((θ i - θ j : ℚ) : Bound) ≤ x) : D i j ≤ x := by
  cases x using WithTop.recTopCoe with
  | top => exact le_top
  | coe c =>
    cases hij : D i j using WithTop.recTopCoe with
    | top =>
      obtain ⟨θ, hs, hθ⟩ := canon_witness hD hi (max (-fin (D 0 i)) (c - fin (D 0 j) + 1))
        (by have := le_max_left (-fin (D 0 i)) (c - fin (D 0 j) + 1); linarith)
      have h1 := h θ hs
      rw [hθ j hj, hij, min_eq_right le_top, WithTop.coe_le_coe] at h1
      have := le_max_right (-fin (D 0 i)) (c - fin (D 0 j) + 1)
      linarith
    | coe c' =>
      obtain ⟨θ, hs, hθ⟩ := canon_witness hD hi (max (-fin (D 0 i)) (c' - fin (D 0 j)))
        (by have := le_max_left (-fin (D 0 i)) (c' - fin (D 0 j)); linarith)
      have h1 := h θ hs
      have hm : min ((c' : ℚ) : Bound) ((max (-fin (D 0 i)) (c' - fin (D 0 j)) + fin (D 0 j) : ℚ) :
          Bound) = (c' : Bound) := by
        refine min_eq_left (WithTop.coe_le_coe.mpr ?_)
        have := le_max_right (-fin (D 0 i)) (c' - fin (D 0 j))
        linarith
      rw [hθ j hj, hij, hm] at h1
      exact h1

end Tight

/-- **Equal zones have equal canonical matrices**: two canonical firing domains that hold the
same firing times agree on every bound. -/
theorem canon_unique {d : Nat} {D D' : NMat} (hD : CanonZone d D) (hD' : CanonZone d D')
    (h : ∀ θ, SatN d D θ ↔ SatN d D' θ) : Agree d D D' := by
  intro i j hi hj
  exact le_antisymm (canon_tight hD hi hj fun θ hθ => (h θ).mp hθ i j hi hj)
    (canon_tight hD' hi hj fun θ hθ => (h θ).mpr hθ i j hi hj)

/-- **On canonical zones the corner is the zone**: equal corners exactly when equal zones. -/
theorem corner_eq_iff_zone {d : Nat} {D D' : NMat} (hD : CanonZone d D) (hD' : CanonZone d D') :
    corner d D = corner d D' ↔ ∀ θ, SatN d D θ ↔ SatN d D' θ := by
  rw [corner_eq_iff]
  exact ⟨fun h => satN_agree h, canon_unique hD hD'⟩


/-! ## The successor reads only the corner of a class -/

section Congr

variable {d n k : Nat} {D D' : NMat}

theorem toFin_agree (h : Agree d D D') : toFin d D = toFin d D' := by
  funext i j
  exact h i j i.isLt j.isLt

theorem canonN_agree (h : Agree d D D') : Agree d (canonN d D) (canonN d D') := by
  intro i j hi hj
  have e : toFin d (canonN d D) = toFin d (canonN d D') := by
    rw [toFin_canonN, toFin_canonN, toFin_agree h]
  exact congrArg (fun M => M ⟨i, hi⟩ ⟨j, hj⟩) e

theorem flaggedN_agree {eps : ℚ} (h : Agree d D D') : FlaggedN eps d D ↔ FlaggedN eps d D' := by
  unfold FlaggedN
  rw [toFin_agree h]

theorem constrainPre_agree (h : Agree (n + 1) D D') :
    Agree (n + 1) (constrainPre n k D) (constrainPre n k D') := by
  intro i j hi hj
  simp only [constrainPre, h i j hi hj]

theorem fireMat_congr {C C' : NMat} {ps : List Nat} {lb : List ℚ} {ub : List Bound}
    (hk : k < n) (hps : ∀ x ∈ ps, x < n) (h : Agree (n + 1) C C') :
    fireMat C k ps lb ub = fireMat C' k ps lb ub := by
  have hg : ∀ p, p < ps.length → ps.getD p 0 < n := fun p hp => by
    apply hps
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some]
    exact List.getElem_mem hp
  funext a b
  unfold fireMat
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9
  all_goals first
    | rfl
    | (rw [h _ _ (by omega) (by have := hg (b - 1) (by omega); omega)])
    | (rw [h _ _ (by have := hg (a - 1) (by omega); omega) (by omega)])
    | (rw [h _ _ (by have := hg (a - 1) (by omega); omega)
          (by have := hg (b - 1) (by omega); omega)])

theorem zoneStep_congr {eps : ℚ} {ps : List Nat} {lb : List ℚ} {ub : List Bound}
    (hk : k < n) (hps : ∀ x ∈ ps, x < n) (h : Agree (n + 1) D D') :
    zoneStep eps n k D ps lb ub = zoneStep eps n k D' ps lb ub := by
  have h1 : Agree (n + 1) (constrainPre n k D) (constrainPre n k D') := constrainPre_agree h
  have hf : fireMat (canonN (n + 1) (constrainPre n k D)) k ps lb ub =
      fireMat (canonN (n + 1) (constrainPre n k D')) k ps lb ub :=
    fireMat_congr hk hps (canonN_agree h1)
  unfold zoneStep
  by_cases hA : FlaggedN eps (n + 1) (constrainPre n k D)
  · rw [if_pos hA, if_pos ((flaggedN_agree h1).mp hA)]
  · rw [if_neg hA, if_neg (fun h' => hA ((flaggedN_agree h1).mpr h')), hf]

end Congr

/-- **The successor of a class reads only its marking, its clocks and the corner of its
domain**: two classes with one index key have the same successors. -/
theorem succWith_congr {surv : Nat → AMarking → AMarking → Nat → Bool} {N : TNet}
    {co : List Nat → Option (List Nat)} {eps : ℚ} {C C' : Cls} (h : idxKey C = idxKey C')
    (k : Nat) (d : Deposit) : succWith surv N co eps C k d = succWith surv N co eps C' k d := by
  obtain ⟨hm, hcs, hz⟩ := idxKey_eq_iff.mp h
  obtain ⟨m, cs, D⟩ := C
  obtain ⟨m', cs', D'⟩ := C'
  simp only at hm hcs hz
  subst hm hcs
  unfold succWith
  simp only
  cases hk : cs[k]? with
  | none => rfl
  | some f =>
    simp only
    have hkn : k < cs.length := (List.getElem?_eq_some_iff.mp hk).1
    rw [zoneStep_congr hkn (fun x hx => persPos_lt (C := ⟨m, cs, D⟩) x hx) hz]
    rfl

/-! ## The explorer of the timed class graph -/

/-- An edge label (`StateClassEdge`): the fired transition's name and the index of the outcome
row it took (`branch_index`). -/
abbrev Label := String × Nat

/-- The labelled successors of a class, in the order of `succList` (clocks in class order, rows
in `outcomes` order, dropped successors left out). -/
def succL (N : TNet) (co : List Nat → Option (List Nat)) (eps : ℚ) (C : Cls) :
    List (Label × Cls) :=
  (List.range C.cs.length).flatMap fun k =>
    (rowsOf N (C.cs.getD k 0)).zipIdx.filterMap fun p =>
      (succ N co eps C k p.1).map fun C' => ((nameOf N (C.cs.getD k 0), p.2), C')

/-- A labelled successor is a successor, and every successor carries a label. -/
theorem mem_succL {N : TNet} {co : List Nat → Option (List Nat)} {eps : ℚ} {C C' : Cls} :
    (∃ l, (l, C') ∈ succL N co eps C) ↔ C' ∈ succList N co eps C := by
  simp only [succL, succList, succListWith, List.mem_flatMap, List.mem_range, List.mem_filterMap,
    Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨l, k, hk, p, hp, C'', hs, -, rfl⟩
    exact ⟨k, hk, p.1, List.mem_iff_getElem?.mpr ⟨_, List.mem_zipIdx_iff_getElem?.mp hp⟩, hs⟩
  · rintro ⟨k, hk, d, hd, hs⟩
    obtain ⟨r, hr⟩ := List.mem_iff_getElem?.mp hd
    exact ⟨_, k, hk, (d, r), List.mem_zipIdx_iff_getElem?.mpr hr, C', hs, rfl, rfl⟩

/-- The labelled successors depend on the index key only. -/
theorem succL_congr {N : TNet} {co : List Nat → Option (List Nat)} {eps : ℚ} {C C' : Cls}
    (h : idxKey C = idxKey C') : succL N co eps C = succL N co eps C' := by
  have hcs : C.cs = C'.cs := (idxKey_eq_iff.mp h).2.1
  have hs : ∀ k d, succ N co eps C k d = succ N co eps C' k d := succWith_congr h
  unfold succL
  rw [hcs]
  refine List.flatMap_congr fun k _ => ?_
  refine List.filterMap_congr fun p _ => ?_
  rw [hs]

/-- **The explorer of the timed state-class graph** (`state_class_graph.rs::build_core`):
classes are deduplicated by their index key (marking, clocks, full firing domain), the
successors of a class are `succList` with their labels, and no counter is read. -/
def scgE (N : TNet) (co : List Nat → Option (List Nat)) (eps : ℚ) : Explorer Cls IdxKey Label where
  key := idxKey
  bound := fun _ => 0
  succ := fun _ C => succL N co eps C

/-- **The class-key explorer is key-equivariant**: two classes with one key have the same
labelled successors. -/
theorem scgE_equivariant (N : TNet) (co : List Nat → Option (List Nat)) (eps : ℚ) :
    (scgE N co eps).Equivariant := by
  refine ⟨fun a b c c' h _ _ => ?_⟩
  change List.Perm ((succL N co eps a).map _) ((succL N co eps b).map _)
  rw [succL_congr h]

/-- Reachability in the explorer is reachability along the graph's edges (`Run.lean`). -/
theorem scgE_reach_iff {N : TNet} {co : List Nat → Option (List Nat)} {eps : ℚ} {C0 C : Cls} :
    Explorer.Reach (scgE N co eps) C0 C ↔ Relation.ReflTransGen (Edge N co eps) C0 C := by
  unfold Explorer.Reach
  have e : ∀ a s, Explorer.StepRel (scgE N co eps) a s ↔ Edge N co eps a s := by
    intro a s
    unfold Explorer.StepRel Edge
    rw [← mem_succL]
    constructor
    · rintro ⟨c, l, -, hl⟩; exact ⟨l, hl⟩
    · rintro ⟨l, hl⟩; exact ⟨0, l, le_rfl, hl⟩
  constructor
  · exact fun h => Relation.ReflTransGen.mono (fun a s => (e a s).mp) C0 C h
  · exact fun h => Relation.ReflTransGen.mono (fun a s => (e a s).mpr) C0 C h


/-! ## The shape of a successor -/

/-- What `succ` builds: the fired clock `f`, the persistent positions `ps`, the newly enabled
clocks `newly`, the fired zone `Y`, and the class `finish` makes of them. -/
theorem succ_shape {N : TNet} {co : List Nat → Option (List Nat)} {eps : ℚ} {C C' : Cls}
    {k : Nat} {d : Deposit} (h : succ N co eps C k d = some C') :
    ∃ f ps newly Y, C.cs[k]? = some f ∧
      ps = persPos (survives N) C f (fireAD C.m (trOf N f) d) (inter C.m (trOf N f)) ∧
      newly = (enabledIds N (fireAD C.m (trOf N f) d)).filter
        (fun j => !(ps.map fun i => C.cs.getD i 0).contains j) ∧
      zoneStep eps C.cs.length k C.D ps (newly.map (eftOf N)) (newly.map (lftOf N)) = some Y ∧
      C'.m = fireAD C.m (trOf N f) d ∧
      C'.cs = reorder co ((ps.map fun i => C.cs.getD i 0) ++ newly) ∧
      C'.D = canonN (((ps.map fun i => C.cs.getD i 0) ++ newly).length + 1)
        (ltpPre (((ps.map fun i => C.cs.getD i 0) ++ newly).length + 1)
          (reorderMat co ((ps.map fun i => C.cs.getD i 0) ++ newly) Y)) := by
  unfold succ succWith at h
  cases hk : C.cs[k]? with
  | none => rw [hk] at h; exact absurd h (by simp)
  | some f =>
    rw [hk] at h
    simp only at h
    obtain ⟨Y, hz, hfin⟩ := Option.bind_eq_some_iff.mp h
    unfold finish at hfin
    split_ifs at hfin
    cases hfin
    exact ⟨f, _, _, Y, rfl, rfl, rfl, hz, rfl, rfl, rfl⟩

theorem zoneStep_eq {eps : ℚ} {n k : Nat} {D : NMat} {ps : List Nat} {lb : List ℚ}
    {ub : List Bound} {Y : NMat} (h : zoneStep eps n k D ps lb ub = some Y) :
    Y = canonN (ps.length + lb.length + 1) (fireMat (canonN (n + 1) (constrainPre n k D)) k ps lb ub) := by
  unfold zoneStep at h
  split_ifs at h
  cases h
  rfl

/-! ## Every class of the graph has a canonical domain -/

section Diag

/-- Every diagonal entry of the `d × d` corner is at most `0`. -/
def DiagLe (d : Nat) (D : NMat) : Prop := ∀ i, i < d → D i i ≤ 0

variable {d n k : Nat} {D : NMat}

theorem diagLe_canonN (h : DiagLe d D) : DiagLe d (canonN d D) :=
  fun i hi => (canonN_le D hi hi).trans (h i hi)

theorem diagLe_ltpPre (h : DiagLe d D) : DiagLe d (ltpPre d D) := by
  intro i hi
  unfold ltpPre
  split_ifs with h1
  · omega
  · exact h i hi

theorem diagLe_constrainPre (h : DiagLe (n + 1) D) : DiagLe (n + 1) (constrainPre n k D) := by
  intro i hi
  unfold constrainPre
  split_ifs with h1
  · omega
  · exact h i hi

theorem diagLe_createPre {lb : List ℚ} {ub : List Bound} : DiagLe (n + 1) (createPre n lb ub) := by
  intro i _
  simp [createPre]

theorem diagLe_fireMat {C : NMat} {ps : List Nat} {lb : List ℚ} {ub : List Bound}
    (hps : ∀ x ∈ ps, x < n) (hC : DiagLe (n + 1) C) :
    DiagLe (ps.length + lb.length + 1) (fireMat C k ps lb ub) := by
  have hg : ∀ p, p < ps.length → ps.getD p 0 < n := fun p hp => by
    apply hps
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some]
    exact List.getElem_mem hp
  intro a _
  unfold fireMat
  split_ifs
  all_goals first
    | exact le_rfl
    | (exact hC _ (by have := hg (a - 1) (by omega); omega))
    | omega

theorem diagLe_reorderMat {co : List Nat → Option (List Nat)} (hco : CoWF co) {all : List Nat}
    {Y : NMat} (h : DiagLe (all.length + 1) Y) : DiagLe (all.length + 1) (reorderMat co all Y) := by
  unfold reorderMat
  cases hc : co all with
  | none => exact h
  | some ord =>
    obtain ⟨hlen, hlt, -⟩ := hco all ord hc
    intro a ha
    simp only [permMat]
    split_ifs with h0
    · exact le_rfl
    · refine h _ ?_
      unfold pm
      split_ifs with ha0
      · omega
      · have : a - 1 < ord.length := by omega
        have := hlt _ (getD_mem (a - 1) this)
        omega

end Diag

variable {N : TNet} {co : List Nat → Option (List Nat)} {eps : ℚ}

theorem init_diag {m0 : AMarking} {C0 : Cls} (h0 : initCls N co eps m0 = some C0) :
    DiagLe (C0.cs.length + 1) C0.D := by
  obtain ⟨-, -, hD⟩ := initCls_eq h0
  rw [hD]
  exact diagLe_canonN (diagLe_ltpPre (diagLe_canonN diagLe_createPre))

theorem succ_diag (hco : CoWF co) {C C' : Cls} {k : Nat} {d : Deposit}
    (hC : DiagLe (C.cs.length + 1) C.D) (h : succ N co eps C k d = some C') :
    DiagLe (C'.cs.length + 1) C'.D := by
  obtain ⟨f, ps, newly, Y, hk, hps, -, hz, -, hcs, hD⟩ := succ_shape h
  have hpsl : ∀ x ∈ ps, x < C.cs.length := by rw [hps]; exact fun x hx => persPos_lt x hx
  have hY := zoneStep_eq hz
  have hYd : DiagLe ((ps.map fun i => C.cs.getD i 0) ++ newly).length.succ Y := by
    have e : ((ps.map fun i => C.cs.getD i 0) ++ newly).length.succ =
        ps.length + (newly.map (eftOf N)).length + 1 := by simp
    rw [e, hY]
    exact diagLe_canonN (diagLe_fireMat hpsl (diagLe_canonN (diagLe_constrainPre hC)))
  rw [hcs, reorder_length hco, hD]
  exact diagLe_canonN (diagLe_ltpPre (diagLe_reorderMat hco hYd))

/-- Every class the graph reaches has a diagonal at most `0`. -/
theorem graph_diag (hco : CoWF co) {m0 : AMarking} {C0 : Cls}
    (h0 : initCls N co eps m0 = some C0) {C : Cls}
    (h : Relation.ReflTransGen (Edge N co eps) C0 C) : DiagLe (C.cs.length + 1) C.D := by
  induction h with
  | refl => exact init_diag h0
  | tail _ hstep ih =>
    simp only [Edge, succList, succListWith, List.mem_flatMap, List.mem_filterMap] at hstep
    obtain ⟨k, -, d, -, hs⟩ := hstep
    exact succ_diag hco ih hs

/-- The emptiness check of the graph is exact: `eps = 0`, or every bound of the net on a grid
of step `g` above `eps` (the Rust `EPSILON = 1e-9` on whole-millisecond bounds,
`Timing.netGrid_of_timings`). -/
def ExactEps (N : TNet) (eps : ℚ) : Prop :=
  eps = 0 ∨ ∃ g : ℚ, 0 < g ∧ NetGrid g N ∧ 0 ≤ eps ∧ eps < g

theorem ExactEps.nonneg {eps : ℚ} (h : ExactEps N eps) : 0 ≤ eps := by
  rcases h with rfl | ⟨_, _, _, h, _⟩
  · exact le_rfl
  · exact h

/-- **Every class of the graph has a canonical domain**: closed, zero on the diagonal, with a
finite reference row. -/
theorem graph_canon (hT : TimingWF N) (hco : CoWF co) (hx : ExactEps N eps) {m0 : AMarking}
    {C0 : Cls} (h0 : initCls N co eps m0 = some C0) {C : Cls}
    (h : Relation.ReflTransGen (Edge N co eps) C0 C) : CanonZone (C.cs.length + 1) C.D := by
  obtain ⟨-, Y, hD, hnf, hY00⟩ := graph_classes_ok hT hco hx.nonneg h0 h
  have hdiag := graph_diag hco h0 h
  set d := C.cs.length + 1 with hd
  have hnf0 : ¬ FlaggedN 0 d (ltpPre d Y) := by
    rcases hx with rfl | ⟨g, hg, hN, -, hepsg⟩
    · exact hnf
    · intro h0'
      have hgrid : GridM g (canonN d (ltpPre d Y)) := by rw [← hD]; exact graph_grid hN h0 h
      exact hnf (flagged_of_flagged_zero hg hepsg hgrid h0')
  obtain ⟨θ, hθ⟩ := nonempty_of_not_flagged (by omega) hY00 hnf0
  rw [← hD] at hθ
  refine ⟨by omega, ?_, fun i hi => ?_, fun i hi => ?_⟩
  · -- closed: canonicalisation of a satisfiable matrix
    have hs : Novel.Dbm.Sat (toFin d (ltpPre d Y)) (fun i => θ i) := by
      rw [hD] at hθ
      exact satN_iff.mp (satN_canonN.mp hθ)
    have hnn : Novel.Dbm.NoNegCycle (toFin d (ltpPre d Y)) := fun x l => by
      by_contra hlt
      exact Novel.Dbm.flagged_empty le_rfl (Novel.Dbm.flagged_of_neg (not_le.mp hlt)) ⟨_, hs⟩
    have hc := Novel.Dbm.closed_canon hnn
    rw [← toFin_canonN, ← hD] at hc
    intro i j k hi hj hk
    exact hc ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩
  · refine le_antisymm (hdiag i hi) ?_
    have := hθ i i hi hi
    rwa [sub_self] at this
  · rw [hD]
    refine ne_top_of_le_ne_top ?_ (canonN_le _ (by omega) hi)
    unfold ltpPre
    split_ifs with h1
    · exact WithTop.zero_ne_top
    · have : i = 0 := by omega
      subst this
      exact hY00

/-! ## The clocks of a class are in name order -/

/-- A clock list without repeats, in name order. -/
def ClocksOrdered (N : TNet) (cs : List Nat) : Prop :=
  cs.Nodup ∧ cs.Pairwise (fun a b => nameKey N a ≤ nameKey N b)

theorem ordered_reorder {l : List Nat} (hn : l.Nodup) : ClocksOrdered N (reorder (coByName N) l) :=
  ⟨(reorder_perm N l).nodup_iff.mpr hn, reorder_sorted N l⟩

theorem enabledIds_nodup (a : AMarking) : (enabledIds N a).Nodup :=
  List.nodup_range.filter _

theorem init_ordered {m0 : AMarking} {C0 : Cls} (h0 : initCls N (coByName N) eps m0 = some C0) :
    ClocksOrdered N C0.cs := by
  obtain ⟨-, hcs, -⟩ := initCls_eq h0
  rw [hcs]
  exact ordered_reorder (enabledIds_nodup m0)

theorem succ_ordered {C C' : Cls} {k : Nat} {d : Deposit} (hC : C.cs.Nodup)
    (h : succ N (coByName N) eps C k d = some C') : ClocksOrdered N C'.cs := by
  obtain ⟨f, ps, newly, Y, -, hps, hnew, -, -, hcs, -⟩ := succ_shape h
  rw [hcs]
  refine ordered_reorder (List.nodup_append.mpr ⟨?_, ?_, ?_⟩)
  · have hsub : (ps.map fun i => C.cs.getD i 0).Sublist C.cs := by
      have := (List.filter_sublist (l := List.range C.cs.length)
        (p := fun i => survives N f (fireAD C.m (trOf N f) d) (inter C.m (trOf N f))
          (C.cs.getD i 0))).map (fun i => C.cs.getD i 0)
      rw [map_getD_range] at this
      rw [hps]
      exact this
    exact hC.sublist hsub
  · rw [hnew]
    exact (enabledIds_nodup _).filter _
  · intro a ha b hb hab
    subst hab
    rw [hnew, List.mem_filter, Bool.not_eq_true', contains_false_iff] at hb
    exact hb.2 ha

/-- Every class the graph reaches has its clocks in name order, without repeats. -/
theorem graph_ordered {m0 : AMarking} {C0 : Cls} (h0 : initCls N (coByName N) eps m0 = some C0)
    {C : Cls} (h : Relation.ReflTransGen (Edge N (coByName N) eps) C0 C) : ClocksOrdered N C.cs := by
  induction h with
  | refl => exact init_ordered h0
  | tail _ hstep ih =>
    simp only [Edge, succList, succListWith, List.mem_flatMap, List.mem_filterMap] at hstep
    obtain ⟨k, -, d, -, hs⟩ := hstep
    exact succ_ordered ih.1 hs

/-- **One marking, one clock list**: two classes of the graph with the same marking have the
same clocks in the same order, whatever order their transitions became enabled in. -/
theorem graph_cs_eq (hT : TimingWF N) (hN : NamesUnique N) (heps : 0 ≤ eps) {m0 : AMarking}
    {C0 : Cls} (h0 : initCls N (coByName N) eps m0 = some C0) {C C' : Cls}
    (hC : Relation.ReflTransGen (Edge N (coByName N) eps) C0 C)
    (hC' : Relation.ReflTransGen (Edge N (coByName N) eps) C0 C') (hm : C.m = C'.m) :
    C.cs = C'.cs := by
  have hw := (graph_classes_ok hT (coByName_wf N) heps h0 hC).1
  have hw' := (graph_classes_ok hT (coByName_wf N) heps h0 hC').1
  obtain ⟨hn, hs⟩ := graph_ordered h0 hC
  obtain ⟨hn', hs'⟩ := graph_ordered h0 hC'
  have hp : C.cs.Perm C'.cs := (List.perm_ext_iff_of_nodup hn hn').mpr fun c => by
    rw [hw.mem, hw'.mem, hm]
  refine eq_of_perm_sorted hp hs hs' fun a ha b hb hab => ?_
  exact nameKey_inj hN (en_lt ((hw.mem a).mp ha)) (en_lt ((hw.mem b).mp hb)) hab

/-! ## The class key identifies a class by its marking and its zone -/

/-- **The class key of the graph** ([VER-010] AC1): two classes the graph reaches have one key
exactly when they have one marking and one zone (the same firing times). The clock order
plays no part: the canonical order makes it a function of the marking. -/
theorem classKey_eq_iff (hT : TimingWF N) (hN : NamesUnique N) (hx : ExactEps N eps)
    {m0 : AMarking} {C0 : Cls} (h0 : initCls N (coByName N) eps m0 = some C0) {C C' : Cls}
    (hC : Relation.ReflTransGen (Edge N (coByName N) eps) C0 C)
    (hC' : Relation.ReflTransGen (Edge N (coByName N) eps) C0 C') :
    classKey N C = classKey N C' ↔
      C.m = C'.m ∧ ∀ θ, SatN (C.cs.length + 1) C.D θ ↔ SatN (C'.cs.length + 1) C'.D θ := by
  constructor
  · intro h
    simp only [classKey, ClassKey.mk.injEq] at h
    obtain ⟨hm, -, hz⟩ := h
    have hcs := graph_cs_eq hT hN hx.nonneg h0 hC hC' hm
    refine ⟨hm, fun θ => ?_⟩
    rw [hcs] at hz ⊢
    exact satN_agree (corner_eq_iff.mp hz) θ
  · rintro ⟨hm, hz⟩
    have hcs := graph_cs_eq hT hN hx.nonneg h0 hC hC' hm
    have hc := graph_canon hT (coByName_wf N) hx h0 hC
    have hc' := graph_canon hT (coByName_wf N) hx h0 hC'
    rw [hcs] at hz hc
    simp only [classKey, ClassKey.mk.injEq]
    refine ⟨hm, by rw [hcs], ?_⟩
    rw [hcs]
    exact corner_eq_iff.mpr (canon_unique hc hc' hz)

/-- Two clock lists of transitions of a net with unique names that carry the same names are
equal. -/
theorem map_nameOf_inj (hN : NamesUnique N) :
    ∀ {l₁ l₂ : List Nat}, (∀ c ∈ l₁, c < N.length) → (∀ c ∈ l₂, c < N.length) →
      l₁.map (nameOf N) = l₂.map (nameOf N) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: t, b :: u, h₁, h₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [hN a b (h₁ a List.mem_cons_self) (h₂ b List.mem_cons_self) h.1,
      map_nameOf_inj hN (fun c hc => h₁ c (List.mem_cons_of_mem a hc))
        (fun c hc => h₂ c (List.mem_cons_of_mem b hc)) h.2]

/-- **The explorer dedups as the Rust does**: on a net with unique names, two classes whose
clocks are transitions of the net have one index key exactly when they have one class key. -/
theorem idxKey_eq_iff_classKey (hN : NamesUnique N) {C C' : Cls}
    (hC : ∀ c ∈ C.cs, c < N.length) (hC' : ∀ c ∈ C'.cs, c < N.length) :
    idxKey C = idxKey C' ↔ classKey N C = classKey N C' := by
  simp only [idxKey, classKey, IdxKey.mk.injEq, ClassKey.mk.injEq]
  constructor
  · rintro ⟨hm, hcs, hz⟩
    exact ⟨hm, by rw [hcs], hz⟩
  · rintro ⟨hm, hn, hz⟩
    exact ⟨hm, map_nameOf_inj hN hC hC' hn, hz⟩

/-! ## The built graph covers every timed run -/

section Build

variable {n : Nat} {cut : Nat → Bool} {bad : Cls → Bool} {stopAt : Bool} {fuel : Nat}

/-- Every class a build stores is a class of the graph. -/
theorem scg_stored_graph {C0 T : Cls}
    (hT : T ∈ (Decide.build (scgE N co eps) n cut bad stopAt fuel C0).cls) :
    Relation.ReflTransGen (Edge N co eps) C0 T :=
  scgE_reach_iff.mp (Decide.build_reach _ hT)

/-- **A closed graph built with key dedup holds every timed run** ([VER-010] AC2, [VER-023]
`SPURIOUS_UNDER_TIMING`): every state of a run of the timed semantics lies in a stored class. The
build dedups by the class key, not by equality of classes, so this discharges premise 7 of
`Succ.lean` for the model. -/
theorem timed_run_stored (hT : TimingWF N) (hco : CoWF co) (heps : 0 ≤ eps) {m0 : AMarking}
    {C0 : Cls} (h0 : initCls N co eps m0 = some C0)
    (hcomp : (Decide.build (scgE N co eps) n cut bad stopAt fuel C0).complete = true)
    {s : TState} (hs : TReach N m0 s) :
    ∃ T ∈ (Decide.build (scgE N co eps) n cut bad stopAt fuel C0).cls, InCls N s T ∧ ClsWF N T := by
  obtain ⟨C, hreach, hin, -, -⟩ := timed_run_sound hT hco heps h0 hs
  obtain ⟨-, hclosed, -, hall⟩ := Decide.build_spec (scgE N co eps) n cut bad stopAt fuel C0
  obtain ⟨T, hT', hkT⟩ := Decide.complete_twin (scgE_equivariant N co eps)
    (Decide.x0_mem_build (E := scgE N co eps) n cut bad stopAt fuel C0) hclosed (hall hcomp) C
    (scgE_reach_iff.mpr hreach)
  obtain ⟨hm, hcs, hz⟩ := idxKey_eq_iff.mp hkT
  refine ⟨T, hT', ⟨hin.1.trans hm.symm, fun ϑ hbox => ?_⟩,
    (graph_classes_ok hT hco heps h0 (scg_stored_graph hT')).1⟩
  rw [hcs] at hbox hz ⊢
  exact (satN_agree hz _).mpr (hin.2 ϑ hbox)

/-- **A marking no stored class of a closed graph has is reached by no timed run.** -/
theorem timed_safety_closed (hT : TimingWF N) (hco : CoWF co) (heps : 0 ≤ eps) {m0 : AMarking}
    {C0 : Cls} (h0 : initCls N co eps m0 = some C0)
    (hcomp : (Decide.build (scgE N co eps) n cut bad stopAt fuel C0).complete = true)
    (badM : AMarking → Prop)
    (hgood : ∀ T ∈ (Decide.build (scgE N co eps) n cut bad stopAt fuel C0).cls, ¬ badM T.m)
    {s : TState} (hs : TReach N m0 s) : ¬ badM s.m := by
  obtain ⟨T, hT', hin, -⟩ := timed_run_stored hT hco heps h0 hcomp hs
  rw [hin.1]
  exact hgood T hT'

open Classical in
/-- **One marking and one zone, one stored class** ([VER-010] AC1): two classes a build stores
with the same marking and the same firing times are the same class of the built graph. -/
theorem stored_one_class (hT : TimingWF N) (hN : NamesUnique N) (hx : ExactEps N eps)
    {m0 : AMarking} {C0 : Cls} (h0 : initCls N (coByName N) eps m0 = some C0) {i j : Nat}
    {A B : Cls}
    (hA : (Decide.build (scgE N (coByName N) eps) n cut bad stopAt fuel C0).cls[i]? = some A)
    (hB : (Decide.build (scgE N (coByName N) eps) n cut bad stopAt fuel C0).cls[j]? = some B)
    (hm : A.m = B.m) (hz : ∀ θ, SatN (A.cs.length + 1) A.D θ ↔ SatN (B.cs.length + 1) B.D θ) :
    i = j := by
  have hAg := scg_stored_graph (List.mem_of_getElem? hA)
  have hBg := scg_stored_graph (List.mem_of_getElem? hB)
  have hkey : classKey N A = classKey N B := (classKey_eq_iff hT hN hx h0 hAg hBg).mpr ⟨hm, hz⟩
  have hw := (graph_classes_ok hT (coByName_wf N) hx.nonneg h0 hAg).1
  have hw' := (graph_classes_ok hT (coByName_wf N) hx.nonneg h0 hBg).1
  have hidx : idxKey A = idxKey B :=
    (idxKey_eq_iff_classKey hN (fun c hc => en_lt ((hw.mem c).mp hc))
      (fun c hc => en_lt ((hw'.mem c).mp hc))).mpr hkey
  exact (Graph.build_par (E := scgE N (coByName N) eps) n cut bad stopAt fuel C0).2.1 i j A B hA hB hidx

end Build


/-! ## The timed graph route -/

/-- **The timed state-class graph of a net** (`StateClassGraph::build_with_options`, timed): the
initial class in canonical order, then the build loop at the class-key explorer with the class
budget `maxClasses`, the stop oracle `cut` and `fuel`, no early stop. `none` when the initial zone
is flagged empty (never under `TimingWF`, `init_sound`). -/
noncomputable def scgGraph (N : TNet) (eps : ℚ) (maxClasses : Nat) (cut : Nat → Bool) (fuel : Nat)
    (m0 : AMarking) : Option (Decide.Out Cls) :=
  (initCls N (coByName N) eps m0).map
    (Decide.build (scgE N (coByName N) eps) maxClasses cut (fun _ => false) false fuel)

/-- A well-timed net always has a graph. -/
theorem scgGraph_some (hT : TimingWF N) {eps : ℚ} (heps : 0 ≤ eps) (maxClasses : Nat)
    (cut : Nat → Bool) (fuel : Nat) (m0 : AMarking) :
    ∃ o, scgGraph N eps maxClasses cut fuel m0 = some o := by
  obtain ⟨C0, h0, -, -⟩ := init_sound hT (coByName_wf N) heps m0
  exact ⟨Decide.build (scgE N (coByName N) eps) maxClasses cut (fun _ => false) false fuel C0,
    by simp only [scgGraph, h0, Option.map_some]⟩

/-- **A closed timed graph holds every state of every timed run.** -/
theorem scgGraph_covers (hT : TimingWF N) {eps : ℚ} (heps : 0 ≤ eps) {maxClasses : Nat}
    {cut : Nat → Bool} {fuel : Nat} {m0 : AMarking} {o : Decide.Out Cls}
    (ho : scgGraph N eps maxClasses cut fuel m0 = some o) (hcomp : o.complete = true)
    {s : TState} (hs : TReach N m0 s) : ∃ T ∈ o.cls, InCls N s T ∧ ClsWF N T := by
  obtain ⟨C0, h0, rfl⟩ := Option.map_eq_some_iff.mp ho
  exact timed_run_stored hT (coByName_wf N) heps h0 hcomp hs

#spec_witness coByName
#spec_witness classKey
#spec_witness scgE
#spec_witness scgGraph

/-! ## Worked examples -/

section Examples

/-- A transition with no arcs and the given name. -/
def exTr (s : String) : Transition :=
  { name := s, inputs := [], inhibitors := [], reads := [], resets := [] }

/-- Three transitions named `b`, `a` and `Z`, at positions 0, 1 and 2. -/
def exNet : TNet := [⟨exTr "b", [], 0, ⊤⟩, ⟨exTr "a", [], 0, ⊤⟩, ⟨exTr "Z", [], 0, ⊤⟩]

/-- The clocks `b, a, Z` are put in the order `Z, a, b`: an upper-case `Z` (code point 90) comes
before a lower-case `a` (97), as code points order them and no locale does. Clocks already in
that order are left alone (`none`). -/
theorem ex_order :
    coByName exNet [0, 1, 2] = some [2, 1, 0] ∧ reorder (coByName exNet) [0, 1, 2] = [2, 1, 0] ∧
      coByName exNet [2, 1, 0] = none := by
  decide

/-- Whatever order the three transitions became enabled in, the class lists their clocks as
`Z, a, b`. -/
theorem ex_order_forgets :
    reorder (coByName exNet) [1, 0, 2] = [2, 1, 0] ∧ reorder (coByName exNet) [0, 2, 1] = [2, 1, 0] ∧
      reorder (coByName exNet) [2, 0, 1] = [2, 1, 0] := by
  decide

/-- Two transitions whose names are the private-use character U+E000 and the mathematical bold
capital A, U+1D400. By code point U+E000 comes first; by UTF-16 code units it would come second
(U+1D400 is the surrogate pair D835 DC00, below E000). -/
def exNetCp : TNet :=
  [⟨exTr (String.singleton (Char.ofNat 0x1D400)), [], 0, ⊤⟩,
   ⟨exTr (String.singleton (Char.ofNat 0xE000)), [], 0, ⊤⟩]

/-- The clock of U+E000 goes first. -/
theorem ex_order_codePoint : reorder (coByName exNetCp) [0, 1] = [1, 0] := by
  decide

/-- Two transitions share the name `a`. -/
def exNetDup : TNet := [⟨exTr "b", [], 0, ⊤⟩, ⟨exTr "a", [], 0, ⊤⟩, ⟨exTr "a", [], 0, ⊤⟩]

/-- With a repeated name the order is no longer a function of the clock set: the sort is
stable, so the two `a` clocks keep the order they came in, and two enabling orders give two
clock lists. This is why unique names (premise 1) are a premise of `reorder_eq_of_perm` and of
`classKey_eq_iff`. -/
theorem ex_order_dupNames :
    reorder (coByName exNetDup) [0, 1, 2] = [1, 2, 0] ∧
      reorder (coByName exNetDup) [0, 2, 1] = [2, 1, 0] := by
  decide

/-- One clock that fires between `0` and `1` time units from now: `θ 0 - θ 1 ≤ 0` and
`θ 1 - θ 0 ≤ 1`, zero on the diagonal. -/
def exZone : NMat := fun a b => if a = 1 ∧ b = 0 then ((1 : ℚ) : Bound) else 0

/-- The same bounds, with `1` in place of `0` on the clock's diagonal. -/
def exZoneDiag : NMat := fun a b => if a = 1 ∧ (b = 0 ∨ b = 1) then ((1 : ℚ) : Bound) else 0

/-- `exZone` is canonical. -/
theorem exZone_canon : CanonZone 2 exZone :=
  ⟨by omega, fun i j k hi hj hk => by
    interval_cases i <;> interval_cases j <;> interval_cases k <;> norm_num [exZone],
   fun i hi => by interval_cases i <;> simp [exZone], fun i hi => by interval_cases i <;> simp [exZone]⟩

/-- **A positive diagonal entry splits one zone into two matrices.** `exZone` and `exZoneDiag` hold
the same firing times (a diagonal bound `θ 1 - θ 1 ≤ 1` excludes nothing), are both closed, and
differ in one entry. So the uniqueness of the canonical matrix needs the zero diagonal, which
every class of the graph has (`graph_canon`). -/
theorem ex_diag_needed :
    (∀ θ, SatN 2 exZone θ ↔ SatN 2 exZoneDiag θ) ∧ corner 2 exZone ≠ corner 2 exZoneDiag := by
  refine ⟨fun θ => ⟨fun h i j hi hj => ?_, fun h i j hi hj => ?_⟩, by
    unfold exZone exZoneDiag; decide⟩
  · have := h i j hi hj
    interval_cases i <;> interval_cases j <;> simp_all [exZone, exZoneDiag]
  · have := h i j hi hj
    interval_cases i <;> interval_cases j <;> simp_all [exZone, exZoneDiag]

end Examples

end Libpetri.Spec.Verifier.Scg
