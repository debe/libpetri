import Libpetri.Novel.Seam.Index
import Libpetri.Novel.ForwardDeposit
import Mathlib.Logic.Relation

/-!
# Named nets, the flattener, and the inert-place rewrite ([CORE-072], [VER-001], [VER-017])

The executor and the enumeration route work on the net **by name**: `Marking` and `MarkingState`
are keyed by place name, and a place no arc touches keeps its tokens ([CORE-072], inert). The
CHC routes work on the flat net, whose places are numbered by the index `flatten` builds. This
module models both sides and the map between them.

* `NNet`: a named net after outcome expansion: the declared place list and one
  `(transition, deposit)` pair per flat transition, arcs by name. A deposit is a list of names
  **with repetition**: `ft.2.count n` tokens land in `n`. That is one row of
  `branch_outcomes::outcomes`: an action branch deposits one token per place ([IO-016]), and a
  timeout forward from a `One` / `Exactly(k)` input deposits `k` in its target ([IO-014]), so a
  row may carry `post[to] = k ≥ 2`. Outcome enumeration itself is not the seam and is taken as
  given; `ForwardDeposit.lean` models it (`fixedRows`).
* `StepNC` / `ReachNC`: the executor on named markings at token-count granularity. Input guards are
  gone ([IO-006]), so colours never gate a firing. The firing deposits the counts of its row
  (`StepNC.deposit`); `ForwardDeposit.stepCD_stepCR` is that fact for rows built by `fixedRows`,
  whichever way the firing ends. A name no arc touches is a frame place: `fireNC_outside`.
* `StepNARel` / `ReachNA`: the same step on named count markings: the untimed successor the
  enumeration route (`verify_via_state_class_graph`, which builds its graph from the named
  `MarkingState` itself) computes.
* `flatNet ix net`: `net_flattener.rs` `flatten` over the index `ix`, arcs resolved by
  `place_index`, the post vector of a row its deposit counts (`post[pid] += n`).
* `inertNet`: `smt_verifier.rs` `inert_places_net`: the net plus one arc-less place for every
  place the initial marking marks that the net does not declare.

Results: a named firing is a flat firing of the restriction (`stepNC_pull`, `fireAD_restrict`),
so named reachability restricts to concrete row steps (`reachNC_pull`) and, by
`ForwardDeposit.rows_reachability_simulated`, to `ReachAD` over the flat rows — **with or
without** `Covers`; the restriction is simply lossy without it. No multiplicity premise: the
frame and restriction arguments never read how many tokens a row deposits, so rows with
`post[to] = k ≥ 2` are covered, and on a duplicate-free row `fireAD` is `fireA`
(`ForwardDeposit.fireAD_eq_fireA`). The inert net has the same semantics as the net and its
index covers the initial marking (`inert_covers`). Under `Covers` the two routes read the same
seed (`routes_same_seed`) and reach the same markings (`routes_agree`).
-/

namespace Libpetri.Novel.Seam

open Libpetri

variable {N : Type} [DecidableEq N]

/-! ## Named nets -/

/-- An input arc by place name (`libpetri-core` `In`; no guard, [IO-006]). -/
structure NInSpec (N : Type) where
  place : N
  card  : Card

/-- A transition with arcs by place name. -/
structure NTransition (N : Type) where
  name       : String
  inputs     : List (NInSpec N)
  inhibitors : List N
  reads      : List N
  resets     : List N

/-- One outcome of a transition (`branch_outcomes::outcomes`): the names it deposits into, with
repetition — `ft.2.count n` tokens land in `n`. -/
abbrev NFlatTransition (N : Type) := NTransition N × List N

/-- A named net: `PetriNet::places()` and its transitions, branch-expanded. -/
structure NNet (N : Type) where
  places      : List N
  transitions : List (NFlatTransition N)

/-- Every name an arc or the deposit of `ft` mentions. -/
def arcNames (ft : NFlatTransition N) : List N :=
  ft.1.inputs.map NInSpec.place ++ ft.1.inhibitors ++ ft.1.reads ++ ft.1.resets ++ ft.2

/-- Every arc resolves in the index: `flatten`'s `place_index[..]` lookups do not panic. -/
def ArcsIn (ix : PlaceIndex N) (net : NNet N) : Prop :=
  ∀ ft ∈ net.transitions, ∀ n ∈ arcNames ft, n ∈ ix.names

/-- Every arc names a declared place: the `PetriNet` builder declares the places of every arc,
so this holds of every built net. -/
def ArcsDeclared (net : NNet N) : Prop :=
  ∀ ft ∈ net.transitions, ∀ n ∈ arcNames ft, n ∈ net.places

/-- At most one input arc per place per transition: `Basic.lean`'s `InputsDistinctPlaces`, by name. -/
def InputsDistinct (net : NNet N) : Prop :=
  ∀ ft ∈ net.transitions, (ft.1.inputs.map NInSpec.place).Nodup

/-- `ArcsIn`, unpacked for one flat transition. -/
structure TIn (ix : PlaceIndex N) (ft : NFlatTransition N) : Prop where
  inputs     : ∀ s ∈ ft.1.inputs, s.place ∈ ix.names
  inhibitors : ∀ n ∈ ft.1.inhibitors, n ∈ ix.names
  reads      : ∀ n ∈ ft.1.reads, n ∈ ix.names
  resets     : ∀ n ∈ ft.1.resets, n ∈ ix.names
  branch     : ∀ n ∈ ft.2, n ∈ ix.names

omit [DecidableEq N] in
theorem ArcsIn.tin {ix : PlaceIndex N} {net : NNet N} (h : ArcsIn ix net) {ft : NFlatTransition N}
    (hft : ft ∈ net.transitions) : TIn ix ft := by
  have h' := h ft hft
  simp only [arcNames, List.mem_append, List.mem_map] at h'
  exact ⟨fun s hs => h' _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨s, hs, rfl⟩)))),
    fun n hn => h' n (Or.inl (Or.inl (Or.inl (Or.inr hn)))),
    fun n hn => h' n (Or.inl (Or.inl (Or.inr hn))),
    fun n hn => h' n (Or.inl (Or.inr hn)),
    fun n hn => h' n (Or.inr hn)⟩

/-! ## Named semantics -/

/-- The input arc on `n`, if any (first match, as `specAt`). -/
def nspecAt (t : NTransition N) (n : N) : Option (NInSpec N) :=
  t.inputs.find? (fun s => decide (s.place = n))

/-- Enablement on named counts (`can_enable` minus timing and ν; no guards). -/
def enabledNA (m : N → Nat) (t : NTransition N) : Bool :=
  t.inputs.all (fun s => s.card.required ≤ m s.place)
    && t.inhibitors.all (fun p => m p == 0)
    && t.reads.all (fun p => 1 ≤ m p)

/-- Tokens a firing removes from `n`: `consume_for_firing`, guard-free. -/
def nconsumed (m : N → Nat) (t : NTransition N) (n : N) : Nat :=
  match nspecAt t n with
  | none => 0
  | some s => if s.card.consumesAll then m n else s.card.required

/-- The named successor counts for an action writing `prod n` tokens to `n` (`alphaFireC` by name). -/
def fireNC (m : N → Nat) (t : NTransition N) (prod : N → Nat) : N → Nat :=
  fun n => if n ∈ t.resets then prod n else m n - nconsumed m t n + prod n

/-- The tokens a row deposits in each name: its count in the deposit (`post[pid] += n`). -/
def depProd (br : List N) : N → Nat := fun n => br.count n

/-- The untimed successor of a named count marking. -/
def fireNA (m : N → Nat) (t : NTransition N) (br : List N) : N → Nat :=
  fireNC m t (depProd br)

/-- A concrete marking by name: `marking.rs`, `HashMap<Arc<str>, VecDeque<ErasedToken>>`. -/
abbrev NCMarking (N : Type) := N → List Colour

/-- Token counts by name. -/
def alphaN (M : NCMarking N) : N → Nat := fun n => (M n).length

/-- One executor firing on named markings at count granularity: enabled, the firing deposits the
counts of its row, and the counts move as `fireNC` says. The named counterpart of
`ForwardDeposit.StepCR`. `deposit` is the premise about the executor's output: an action writes
one token per place of its branch ([IO-016]), and a timeout deposits its child with each forward
repeated once per consumed token ([IO-014]); for rows built by `fixedRows` that is
`ForwardDeposit.deposit_mem_fixedRows`. -/
structure StepNC (M : NCMarking N) (ft : NFlatTransition N) (prod : N → Nat)
    (M' : NCMarking N) : Prop where
  enabled : enabledNA (alphaN M) ft.1 = true
  deposit : prod = depProd ft.2
  effect  : alphaN M' = fireNC (alphaN M) ft.1 prod

def StepNCRel (net : NNet N) (M M' : NCMarking N) : Prop :=
  ∃ ft ∈ net.transitions, ∃ prod, StepNC M ft prod M'

/-- The executor's reachable named markings. -/
def ReachNC (net : NNet N) (M0 : NCMarking N) : NCMarking N → Prop :=
  Relation.ReflTransGen (StepNCRel net) M0

/-- One untimed successor on named count markings (the enumeration's `compute_successor`, by
name). -/
def StepNARel (net : NNet N) (m m' : N → Nat) : Prop :=
  ∃ ft ∈ net.transitions, enabledNA m ft.1 = true ∧ m' = fireNA m ft.1 ft.2

def ReachNA (net : NNet N) (m0 : N → Nat) : (N → Nat) → Prop :=
  Relation.ReflTransGen (StepNARel net) m0

/-- The quiescence both routes read: no transition enabled. -/
def NQuiescent (net : NNet N) (m : N → Nat) : Prop :=
  ∀ ft ∈ net.transitions, enabledNA m ft.1 = false

/-! ## The flattener -/

/-- An input arc resolved through `place_index`. -/
def flatSpec (ix : PlaceIndex N) (s : NInSpec N) : InSpec :=
  { place := ix.idx s.place, card := s.card, guard := none }

/-- A transition resolved through `place_index` (`flatten`'s per-transition loop). -/
def toFlatT (ix : PlaceIndex N) (t : NTransition N) : Transition :=
  { name := t.name
  , inputs := t.inputs.map (flatSpec ix)
  , inhibitors := t.inhibitors.map ix.idx
  , reads := t.reads.map ix.idx
  , resets := t.resets.map ix.idx }

def flatFT (ix : PlaceIndex N) (ft : NFlatTransition N) : FlatTransition :=
  (toFlatT ix ft.1, ft.2.map ix.idx)

/-- `flatten`: the flat net over index `ix`. -/
def flatNet (ix : PlaceIndex N) (net : NNet N) : FlatNet :=
  net.transitions.map (flatFT ix)

/-- A concrete marking read through the index: what the flat side can see of `M`. -/
def pullC (ix : PlaceIndex N) (M : NCMarking N) : CMarking :=
  fun i => match ix.name? i with
    | some n => M n
    | none => []

/-! ## Helper lemmas -/

omit [DecidableEq N] in
theorem find?_congr_mem {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = q x) → l.find? p = l.find? q
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.find?_cons, h x List.mem_cons_self]
    rw [find?_congr_mem (fun y hy => h y (List.mem_cons_of_mem x hy))]

omit [DecidableEq N] in
theorem all_congr_mem {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = q x) → l.all p = l.all q
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.all_cons, h x List.mem_cons_self]
    rw [all_congr_mem (fun y hy => h y (List.mem_cons_of_mem x hy))]

theorem find?_of_nodup {α β : Type} [DecidableEq β] {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {x : α}, x ∈ l →
      l.find? (fun y => decide (f y = f x)) = some x
  | [], _, _, hx => absurd hx List.not_mem_nil
  | y :: ys, hnd, x, hx => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hx with rfl | hx'
    · simp
    · have hne : f y ≠ f x := fun he => hnd.1 (he ▸ List.mem_map_of_mem hx')
      simp only [List.find?_cons, hne, decide_false]
      exact find?_of_nodup hnd.2 hx'

theorem nspecAt_place {t : NTransition N} {n : N} {s : NInSpec N} (h : nspecAt t n = some s) :
    s ∈ t.inputs ∧ s.place = n :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem nspecAt_none_of_not_mem {ix : PlaceIndex N} {t : NTransition N} {n : N}
    (hin : ∀ s ∈ t.inputs, s.place ∈ ix.names) (hn : n ∉ ix.names) : nspecAt t n = none := by
  unfold nspecAt
  rw [List.find?_eq_none]
  intro s hs he
  have : s.place = n := by simpa using he
  exact hn (this ▸ hin s hs)

section AtIndex

variable (ix : PlaceIndex N)

theorem contains_idx_some (l : List N) {i : Nat} {n : N}
    (hi : ix.name? i = some n) : (l.map ix.idx).contains i = decide (n ∈ l) := by
  have hidx := ix.idx_of_name? hi
  have hn := ix.mem_of_name? hi
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem, List.mem_map, decide_eq_true_eq]
  constructor
  · rintro ⟨n', hn', he⟩
    rw [← hidx, eq_comm, ix.idx_inj hn] at he
    exact he ▸ hn'
  · intro h
    exact ⟨n, h, hidx⟩

theorem contains_idx_none {l : List N} (hl : ∀ n ∈ l, n ∈ ix.names) {i : Nat}
    (hi : ix.name? i = none) : (l.map ix.idx).contains i = false := by
  have hsz := ix.name?_eq_none_iff.mp hi
  apply Bool.eq_false_iff.mpr
  simp only [ne_eq, List.contains_iff_mem, List.mem_map, not_exists, not_and]
  intro n hn he
  have := ix.idx_lt (hl n hn)
  omega

theorem specAt_some {t : NTransition N} (hin : ∀ s ∈ t.inputs, s.place ∈ ix.names) {i : Nat}
    {n : N} (hi : ix.name? i = some n) :
    specAt (toFlatT ix t) i = (nspecAt t n).map (flatSpec ix) := by
  unfold specAt nspecAt toFlatT
  simp only
  rw [List.find?_map]
  congr 1
  apply find?_congr_mem
  intro s hs
  have hidx := ix.idx_of_name? hi
  simp only [Function.comp, flatSpec]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  rw [← hidx, ix.idx_inj (hin s hs)]

theorem specAt_none {t : NTransition N} (hin : ∀ s ∈ t.inputs, s.place ∈ ix.names) {i : Nat}
    (hi : ix.name? i = none) : specAt (toFlatT ix t) i = none := by
  have hsz := ix.name?_eq_none_iff.mp hi
  unfold specAt toFlatT
  simp only
  rw [List.find?_eq_none]
  intro s' hs' he
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
  have := ix.idx_lt (hin s hs)
  have he' : ix.idx s.place = i := by simpa [flatSpec] using he
  omega

/-- The flat post of a row at an indexed place is the named deposit count: `idx` is injective on
the index, so no two names of the row collapse onto one flat place. -/
theorem count_some {br : List N} (hbr : ∀ n ∈ br, n ∈ ix.names) {i : Nat} {n : N}
    (hi : ix.name? i = some n) : (br.map ix.idx).count i = depProd br n := by
  unfold depProd
  induction br with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.count_cons]
    rw [ih (fun n h => hbr n (List.mem_cons_of_mem x h))]
    by_cases hxn : x = n
    · subst hxn
      simp [ix.idx_of_name? hi]
    · have hne : ix.idx x ≠ i := by
        rw [← ix.idx_of_name? hi]
        exact fun h => hxn ((ix.idx_inj (hbr x List.mem_cons_self)).mp h)
      simp [hne, hxn]

theorem count_none {br : List N} (hbr : ∀ n ∈ br, n ∈ ix.names) {i : Nat}
    (hi : ix.name? i = none) : (br.map ix.idx).count i = 0 := by
  apply List.count_eq_zero.mpr
  simpa using contains_idx_none ix hbr hi

end AtIndex

/-! ## A named firing is a flat firing of the restriction -/

theorem enabledA_restrict (ix : PlaceIndex N) {ft : NFlatTransition N} (hT : TIn ix ft)
    (m : N → Nat) : enabledA (restrict ix m) (toFlatT ix ft.1) = enabledNA m ft.1 := by
  have e1 : (ft.1.inputs.map (flatSpec ix)).all
      (fun s => decide (s.card.required ≤ restrict ix m s.place))
      = ft.1.inputs.all (fun s => decide (s.card.required ≤ m s.place)) := by
    rw [List.all_map]
    exact all_congr_mem fun s hs => by
      simp [Function.comp, flatSpec, restrict_idx ix m (hT.inputs s hs)]
  have e2 : (ft.1.inhibitors.map ix.idx).all (fun p => restrict ix m p == 0)
      = ft.1.inhibitors.all (fun p => m p == 0) := by
    rw [List.all_map]
    exact all_congr_mem fun p hp => by
      simp only [Function.comp, restrict_idx ix m (hT.inhibitors p hp)]
  have e3 : (ft.1.reads.map ix.idx).all (fun p => decide (1 ≤ restrict ix m p))
      = ft.1.reads.all (fun p => decide (1 ≤ m p)) := by
    rw [List.all_map]
    exact all_congr_mem fun p hp => by
      simp only [Function.comp, restrict_idx ix m (hT.reads p hp)]
  simp only [enabledA, enabledNA, toFlatT, e1, e2, e3]

/-- **The flat firing of the restriction is the restriction of the named firing**, for a row of
any multiplicity: `fireAD` (the CHC rule with integer posts) on the flat side. -/
theorem fireAD_restrict (ix : PlaceIndex N) {ft : NFlatTransition N} (hT : TIn ix ft)
    (m : N → Nat) :
    ForwardDeposit.fireAD (restrict ix m) (toFlatT ix ft.1) (ft.2.map ix.idx)
      = restrict ix (fireNA m ft.1 ft.2) := by
  funext i
  cases hi : ix.name? i with
  | none =>
    have hr : (toFlatT ix ft.1).resets.contains i = false := contains_idx_none ix hT.resets hi
    unfold ForwardDeposit.fireAD consumeAllAt pre
    rw [hr, specAt_none ix hT.inputs hi, count_none ix hT.branch hi]
    simp [restrict, hi]
  | some n =>
    have hr : (toFlatT ix ft.1).resets.contains i = decide (n ∈ ft.1.resets) :=
      contains_idx_some ix ft.1.resets hi
    have hrn : restrict ix (fireNA m ft.1 ft.2) i = fireNA m ft.1 ft.2 n := by simp [restrict, hi]
    have hrm : restrict ix m i = m n := by simp [restrict, hi]
    rw [hrn]
    unfold ForwardDeposit.fireAD consumeAllAt pre fireNA fireNC nconsumed
    rw [hr, specAt_some ix hT.inputs hi, count_some ix hT.branch hi, hrm]
    by_cases hres : n ∈ ft.1.resets
    · simp [hres]
    · simp only [hres, decide_false, Bool.false_eq_true, if_false]
      cases hs : nspecAt ft.1 n with
      | none => simp
      | some s =>
        simp only [Option.map_some, flatSpec]
        by_cases hca : s.card.consumesAll = true
        · simp [hca]
        · simp [hca]

omit [DecidableEq N] in
theorem alpha_pullC (ix : PlaceIndex N) (M : NCMarking N) :
    alpha (pullC ix M) = restrict ix (alphaN M) := by
  funext i
  unfold alpha pullC restrict alphaN
  cases ix.name? i <;> rfl

/-- `enabledC` of a guard-free transition is `enabledA` of the counts. -/
theorem enabledC_guardFree {m : CMarking} {t : Transition}
    (hg : ∀ s ∈ t.inputs, s.guard = none) : enabledC m t = enabledA (alpha m) t := by
  unfold enabledC enabledA
  rw [all_congr_mem (l := t.inputs) (q := fun s => decide (s.card.required ≤ alpha m s.place))]
  · rfl
  · intro s hs
    simp [matchCount, hg s hs, alpha]

theorem alphaFireC_pull (ix : PlaceIndex N) {ft : NFlatTransition N} (hT : TIn ix ft)
    (M : NCMarking N) (prod : N → Nat) :
    alphaFireC (pullC ix M) (toFlatT ix ft.1) (restrict ix prod)
      = restrict ix (fireNC (alphaN M) ft.1 prod) := by
  funext i
  cases hi : ix.name? i with
  | none =>
    have hr : (toFlatT ix ft.1).resets.contains i = false := contains_idx_none ix hT.resets hi
    unfold alphaFireC consumedAt
    rw [hr, specAt_none ix hT.inputs hi]
    simp [restrict, pullC, hi]
  | some n =>
    have hr : (toFlatT ix ft.1).resets.contains i = decide (n ∈ ft.1.resets) :=
      contains_idx_some ix ft.1.resets hi
    unfold alphaFireC consumedAt
    rw [hr, specAt_some ix hT.inputs hi]
    simp only [restrict, pullC, hi, fireNC, nconsumed, alphaN]
    by_cases hres : n ∈ ft.1.resets
    · simp [hres]
    · simp only [hres, decide_false, Bool.false_eq_true, if_false]
      cases hs : nspecAt ft.1 n with
      | none => simp
      | some s =>
        obtain ⟨hsm, hsp⟩ := nspecAt_place hs
        have hpl : pullC ix M (ix.idx s.place) = M n := by
          simp only [pullC]
          rw [ix.name?_idx (hT.inputs s hsm), hsp]
        simp [Option.map_some, consumeCount, flatSpec, matchCount, hpl]

/-- The restricted deposit is the flat row's post vector. -/
theorem restrict_depProd (ix : PlaceIndex N) {br : List N} (hbr : ∀ n ∈ br, n ∈ ix.names) :
    restrict ix (depProd br) = fun i => (br.map ix.idx).count i := by
  funext i
  cases hi : ix.name? i with
  | none => rw [count_none ix hbr hi]; simp [restrict, hi]
  | some n => rw [count_some ix hbr hi]; simp [restrict, hi]

/-- **A named executor firing is a flat row step of the pulled-back marking**: enabled, and it
deposits the counts of the flat row (`ForwardDeposit.StepCR`'s body). -/
theorem stepNC_pull (ix : PlaceIndex N) {ft : NFlatTransition N} (hT : TIn ix ft)
    {M M' : NCMarking N} {prod : N → Nat} (hs : StepNC M ft prod M') :
    enabledC (pullC ix M) (flatFT ix ft).1 = true ∧
      alpha (pullC ix M') =
        alphaFireC (pullC ix M) (flatFT ix ft).1 (fun i => (flatFT ix ft).2.count i) := by
  refine ⟨?_, ?_⟩
  · show enabledC (pullC ix M) (toFlatT ix ft.1) = true
    rw [enabledC_guardFree (fun s hs => by
      obtain ⟨s0, -, rfl⟩ := List.mem_map.mp hs; rfl), alpha_pullC, enabledA_restrict ix hT]
    exact hs.enabled
  · show alpha (pullC ix M') =
      alphaFireC (pullC ix M) (toFlatT ix ft.1) (fun i => (ft.2.map ix.idx).count i)
    rw [← restrict_depProd ix hT.branch, ← hs.deposit, alphaFireC_pull ix hT, alpha_pullC,
      hs.effect]

/-- The flat net of a named net satisfies `proposition_one`'s side conditions: guards are gone,
and distinct input names resolve to distinct indices. -/
theorem wellFormed_flatNet {ix : PlaceIndex N} {net : NNet N} (hA : ArcsIn ix net)
    (hD : InputsDistinct net) : WellFormed (flatNet ix net) := by
  intro ft' hft'
  obtain ⟨ft, hft, rfl⟩ := List.mem_map.mp hft'
  have hT := hA.tin hft
  refine ⟨fun s' hs' => ?_, fun s' hs' _ => ?_⟩
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
    show specAt (toFlatT ix ft.1) (ix.idx s.place) = some (flatSpec ix s)
    rw [specAt_some ix hT.inputs (ix.name?_idx (hT.inputs s hs))]
    unfold nspecAt
    rw [find?_of_nodup (f := NInSpec.place) (hD ft hft) hs]
    rfl
  · obtain ⟨s, -, rfl⟩ := List.mem_map.mp hs'
    rfl

/-- Every consume-all arc of a flat net is unguarded: `flatSpec` writes no guard. -/
theorem guardFree_flatNet (ix : PlaceIndex N) (net : NNet N) :
    ∀ tr ∈ flatNet ix net, GuardFreeConsumeAll tr.1 := by
  intro tr htr s hs _
  obtain ⟨ft, -, rfl⟩ := List.mem_map.mp htr
  obtain ⟨s0, -, rfl⟩ := List.mem_map.mp hs
  rfl

/-- **Named reachability restricts to concrete flat row steps.** No `Covers` premise: the flat
side always sees the restriction; without `Covers` it just cannot see the rest. -/
theorem reachNC_pull {ix : PlaceIndex N} {net : NNet N} (hA : ArcsIn ix net)
    {M0 M : NCMarking N} (h : ReachNC net M0 M) :
    Relation.ReflTransGen (ForwardDeposit.StepCR (flatNet ix net)) (pullC ix M0) (pullC ix M) := by
  refine Relation.ReflTransGen.lift (pullC ix) (fun M M' hs => ?_) M0 M h
  obtain ⟨ft, hft, prod, hstep⟩ := hs
  exact ⟨flatFT ix ft, List.mem_map_of_mem hft, stepNC_pull ix (hA.tin hft) hstep⟩

/-- **Named reachability restricts to `ReachAD`** over the flat rows, through
`ForwardDeposit.rows_reachability_simulated` (Proposition 1 with integer posts): no
`UnitOutput`, no `InputsDistinct`. -/
theorem reachNC_reachAD {ix : PlaceIndex N} {net : NNet N} (hA : ArcsIn ix net)
    {M0 M : NCMarking N} (h : ReachNC net M0 M) :
    ForwardDeposit.ReachAD (flatNet ix net) (restrict ix (alphaN M0)) (restrict ix (alphaN M)) := by
  rw [← alpha_pullC, ← alpha_pullC]
  exact ForwardDeposit.rows_reachability_simulated (guardFree_flatNet ix net) (reachNC_pull hA h)

/-- The enumeration's named successor restricts to a CHC successor. -/
theorem reachNA_restrict {ix : PlaceIndex N} {net : NNet N} (hA : ArcsIn ix net)
    {m0 m : N → Nat} (h : ReachNA net m0 m) :
    ForwardDeposit.ReachAD (flatNet ix net) (restrict ix m0) (restrict ix m) := by
  refine Relation.ReflTransGen.lift (restrict ix) (fun m m' hs => ?_) m0 m h
  obtain ⟨ft, hft, hen, rfl⟩ := hs
  have hT := hA.tin hft
  exact ⟨flatFT ix ft, List.mem_map_of_mem hft, by rw [flatFT, enabledA_restrict ix hT]; exact hen,
    (fireAD_restrict ix hT m).symm⟩

/-! ## Covers is preserved by firing -/

/-- A name outside the index is a frame place: no firing changes it. -/
theorem fireNC_outside {ix : PlaceIndex N} {ft : NFlatTransition N} (hT : TIn ix ft)
    (m : N → Nat) {n : N} (hn : n ∉ ix.names) : fireNA m ft.1 ft.2 n = m n := by
  have hres : n ∉ ft.1.resets := fun h => hn (hT.resets n h)
  have hbr : n ∉ ft.2 := fun h => hn (hT.branch n h)
  simp [fireNA, fireNC, nconsumed, depProd, hres, List.count_eq_zero_of_not_mem hbr,
    nspecAt_none_of_not_mem hT.inputs hn]

theorem covers_fireNA {ix : PlaceIndex N} {ft : NFlatTransition N} (hT : TIn ix ft)
    {m : N → Nat} (h : Covers ix m) : Covers ix (fireNA m ft.1 ft.2) := by
  intro n hne
  by_contra hn
  rw [fireNC_outside hT m hn] at hne
  exact hne (covers_zero h hn)

theorem covers_reachNA {ix : PlaceIndex N} {net : NNet N} (hA : ArcsIn ix net)
    {m0 m : N → Nat} (h0 : Covers ix m0) (h : ReachNA net m0 m) : Covers ix m := by
  induction h with
  | refl => exact h0
  | tail _ hs ih =>
    obtain ⟨ft, hft, -, rfl⟩ := hs
    exact covers_fireNA (hA.tin hft) ih

theorem covers_reachNC {ix : PlaceIndex N} {net : NNet N} (hA : ArcsIn ix net)
    {M0 M : NCMarking N} (h0 : Covers ix (alphaN M0)) (h : ReachNC net M0 M) :
    Covers ix (alphaN M) := by
  induction h with
  | refl => exact h0
  | tail _ hs ih =>
    obtain ⟨ft, hft, prod, hstep⟩ := hs
    rw [hstep.effect, hstep.deposit]
    exact covers_fireNA (hA.tin hft) ih

/-! ## The inert-place rewrite -/

/-- The places `m0` marks that `net` does not declare, in the marking's order
(`inert_places_net`'s filter over `marking.places()`). -/
def inertPlaces (net : NNet N) (m0 : NMarking N) : List N :=
  m0.places.filter (fun n => n ∉ net.places)

/-- `smt_verifier.rs` `inert_places_net`: the net plus an arc-less place per inert place,
appended after the declared places **in the net's place list**. `flatten` re-sorts that list, so
in the flat index an inert place sits wherever its name sorts, not after the declared places;
no result here depends on the position. (The Rust returns `None` when there is none, and the
verifier then keeps the net itself; `inertNet_of_nil` is that case.) -/
def inertNet (net : NNet N) (m0 : NMarking N) : NNet N :=
  { places := net.places ++ inertPlaces net m0, transitions := net.transitions }

theorem inertNet_of_nil {net : NNet N} {m0 : NMarking N} (h : inertPlaces net m0 = []) :
    inertNet net m0 = net := by
  simp [inertNet, h]

/-- The rewrite adds no arc, so the executor and the enumeration see the same net. -/
theorem inertNet_transitions (net : NNet N) (m0 : NMarking N) :
    (inertNet net m0).transitions = net.transitions := rfl

theorem arcsDeclared_inert {net : NNet N} (h : ArcsDeclared net) (m0 : NMarking N) :
    ArcsDeclared (inertNet net m0) :=
  fun ft hft n hn => List.mem_append_left _ (h ft hft n hn)

theorem arcsIn_flatIndex {net : NNet N} (h : ArcsDeclared net) :
    ArcsIn (flatIndex net.places) net :=
  fun ft hft n hn => mem_flatIndex.mpr (h ft hft n hn)

/-- **The inert net's index covers the initial marking.** -/
theorem inert_covers (net : NNet N) (m0 : NMarking N) :
    Covers (flatIndex (inertNet net m0).places) m0.count := by
  intro n hn
  have hp := (m0.count_ne_zero_iff n).mp hn
  rw [mem_flatIndex]
  by_cases hd : n ∈ net.places
  · exact List.mem_append_left _ hd
  · exact List.mem_append_right _ (List.mem_filter.mpr ⟨hp, by simpa using hd⟩)

/-! ## The two routes read one seed ([VER-017] vs the CHC routes) -/

/-- **Same seed.** The enumeration route starts from the named `MarkingState` `m0`, the CHC routes
from `encodeM0 ix m0`. Under `Covers` the encoded seed is the restriction of `m0` and reads back
as `m0` exactly: the two routes start from the same marking. -/
theorem routes_same_seed {ix : PlaceIndex N} {m0 : NMarking N} (h : Covers ix m0.count) :
    encodeM0 ix m0 = restrict ix m0.count ∧ lift ix (encodeM0 ix m0) = m0.count :=
  ⟨encodeM0_eq_restrict ix m0, by rw [encodeM0_eq_restrict]; exact lift_restrict h⟩

/-- **The routes reach the same markings.** Under `Covers` of the seed, a marking is CHC-reachable
from the encoded seed iff it is the restriction of a named marking the enumeration reaches from
`m0`, and that named marking is determined by it (`restrict_injective`). -/
theorem routes_agree {ix : PlaceIndex N} {net : NNet N} (hA : ArcsIn ix net)
    {m0 : NMarking N} (h : Covers ix m0.count) (a : AMarking) :
    ForwardDeposit.ReachAD (flatNet ix net) (encodeM0 ix m0) a ↔
      ∃ m, ReachNA net m0.count m ∧ Covers ix m ∧ a = restrict ix m := by
  rw [encodeM0_eq_restrict]
  constructor
  · intro hr
    induction hr with
    | refl => exact ⟨m0.count, Relation.ReflTransGen.refl, h, rfl⟩
    | tail _ hs ih =>
      obtain ⟨m, hm, hc, rfl⟩ := ih
      obtain ⟨ft', hft', hen, rfl⟩ := hs
      obtain ⟨ft, hft, rfl⟩ := List.mem_map.mp hft'
      have hT := hA.tin hft
      rw [flatFT, enabledA_restrict ix hT] at hen
      exact ⟨fireNA m ft.1 ft.2, Relation.ReflTransGen.tail hm ⟨ft, hft, hen, rfl⟩,
        covers_fireNA hT hc, fireAD_restrict ix hT m⟩
  · rintro ⟨m, hm, -, rfl⟩
    exact reachNA_restrict hA hm

/-- **The routes decide the same verdict.** Given an encoded `Bad` that reads a named `Sem` on
covered markings, "no CHC-reachable marking is `Bad`" iff "no marking the enumeration reaches is
`Sem`". -/
theorem routes_agree_verdict {ix : PlaceIndex N} {net : NNet N} (hA : ArcsIn ix net)
    {m0 : NMarking N} (h : Covers ix m0.count) {Bad : AMarking → Prop} {Sem : (N → Nat) → Prop}
    (hBad : ∀ m, Covers ix m → (Bad (restrict ix m) ↔ Sem m)) :
    (∀ a, ForwardDeposit.ReachAD (flatNet ix net) (encodeM0 ix m0) a → ¬ Bad a) ↔
      (∀ m, ReachNA net m0.count m → ¬ Sem m) := by
  constructor
  · intro hp m hm hs
    have hc := covers_reachNA hA h hm
    exact hp _ ((routes_agree hA h _).mpr ⟨m, hm, hc, rfl⟩) ((hBad m hc).mpr hs)
  · intro hp a ha hb
    obtain ⟨m, hm, hc, rfl⟩ := (routes_agree hA h a).mp ha
    exact hp m hm ((hBad m hc).mp hb)

end Libpetri.Novel.Seam
