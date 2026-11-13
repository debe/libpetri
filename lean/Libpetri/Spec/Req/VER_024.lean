import Libpetri.Novel.Stubborn
import Libpetri.Spec.Req.VER_006
import Libpetri.Spec.Verifier.Graph
import Mathlib.Data.Prod.Lex

set_option linter.missingDocs true
set_option autoImplicit false

/-!
# VER-024: Stubborn-Set Reduction of the Enumeration Route (`spec/07-verification.md`)

On a quiescence property the enumeration route of [VER-017] expands, at each class, only the
enabled transitions of one stubborn set, each with all of its outcomes. Three blocks:

* `VER_024` (B), over a selection function `Sel : SelFn` (the transitions to expand at a
  marking): the selection picks only enabled transitions; every dead marking reachable in the net
  is reachable through the reduced steps; a marking has no reduced successor exactly when no
  transition is enabled. A reduced step fires every outcome of a selected transition
  (`StepSel`), so "with all of its outcomes" is the step itself.
* `VER_024_select` (F), over the same `Sel`: the choice the spec pins, so that every
  implementation builds the same reduced graph. The selection is the set of enabled members of
  the least set `S(s)` closed under rules S-D1 and S-D2 (`ClosedT`), for the enabled seed `s`
  whose closure has the fewest enabled members, the code-point-smallest seed name breaking ties.
  Rule S-D2 reads the first unsatisfied condition over the input and read places in place order,
  then over the inhibitor places in place order (`conds`, `firstUnsat`). The selection lists its
  picks in ascending order of name, the order in which the route expands them.
* `VER_024_route` (F), over the decision `U : ReduceFn` and the cache key `key : CacheKeyFn`: the
  route reduces exactly on a quiescence property, with the option on and no drained forward, and
  the cache key of [VER-017] carries that bit in its `reduced` field.

The witnesses are `refSel` (the closure of `Novel/Stubborn.lean` lifted to transitions, with the
pinned blocker and the pinned seed choice, sorted by name), `refReduce` and `refKey`. The proofs of the B lines
go through the row-level theory of `Novel/Stubborn.lean` (`stubborn_preserves_dead`,
`reducedQuiescent_iff_dead`) with one bridge lemma (`closedT_stubborn`): the rows of a
transition-level closed set with an enabled seed are a row-level stubborn set.

Labels: the spec's (D1) and (D2) are written S-D1 and S-D2 here, so that they do not read as the
migration rulings D1 and D2.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Novel.ForwardDeposit

namespace Ver024

/-! ## The net the graph is built on, transition by transition -/

/-- One transition of the net the graph is built on, with the deposit of each of its outcomes
(every outcome of every branch, [VER-021]). -/
abbrev TEntry : Type := Transition × List Deposit

/-- The net the graph is built on: its transitions in order, each with all of its outcomes. -/
abbrev SNet : Type := List TEntry

/-- A row of `Novel/Stubborn.lean`: one transition with one of its outcomes. -/
abbrev SRow : Type := Novel.Stubborn.Row

/-- The rows of the net: one per outcome of each transition, in order. -/
def rowsOf (net : SNet) : List SRow := net.flatMap fun e => e.2.map fun d => (e.1, d)

/-- The rows of the transitions at the given indices: every outcome of each. -/
def rowsAt (net : SNet) (idx : List Nat) : List SRow :=
  idx.flatMap fun i => match net[i]? with
    | some e => e.2.map fun d => (e.1, d)
    | none => []

/-- Transition `i` exists and is enabled at `a`. -/
def enAt (net : SNet) (a : AMarking) (i : Nat) : Bool :=
  match net[i]? with
  | some e => enabledA a e.1
  | none => false

/-- The name of transition `i` (empty when there is none). -/
def nameAt (net : SNet) (i : Nat) : String :=
  match net[i]? with
  | some e => e.1.name
  | none => ""

/-- Every transition has at least one outcome, as every row expansion of [VER-001] gives. -/
def Outcomes (net : SNet) : Prop := ∀ e ∈ net, e.2 ≠ []

/-- No transition is enabled at `a`: a dead marking. -/
def DeadT (net : SNet) (a : AMarking) : Prop := ∀ e ∈ net, enabledA a e.1 = false

instance (net : SNet) : Decidable (Outcomes net) :=
  inferInstanceAs (Decidable (∀ e ∈ net, e.2 ≠ []))

instance (net : SNet) (a : AMarking) : Decidable (DeadT net a) :=
  inferInstanceAs (Decidable (∀ e ∈ net, enabledA a e.1 = false))

/-- **A selection**: the indices of the transitions the reduced enumeration expands at a
marking. -/
abbrev SelFn : Type := SNet → AMarking → List Nat

/-- **The reduced step**: fire an enabled transition the selection picks, with any of its
outcomes. -/
def StepSel (Sel : SelFn) (net : SNet) (a b : AMarking) : Prop :=
  StepAD (rowsAt net (Sel net a)) a b

theorem mem_rowsOf {net : SNet} {r : SRow} :
    r ∈ rowsOf net ↔ ∃ e ∈ net, ∃ d ∈ e.2, r = (e.1, d) := by
  simp only [rowsOf, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨e, he, d, hd, rfl⟩; exact ⟨e, he, d, hd, rfl⟩
  · rintro ⟨e, he, d, hd, rfl⟩; exact ⟨e, he, d, hd, rfl⟩

theorem mem_rowsAt {net : SNet} {idx : List Nat} {r : SRow} :
    r ∈ rowsAt net idx ↔ ∃ i ∈ idx, ∃ e, net[i]? = some e ∧ ∃ d ∈ e.2, r = (e.1, d) := by
  simp only [rowsAt, List.mem_flatMap]
  constructor
  · rintro ⟨i, hi, hr⟩
    cases he : net[i]? with
    | none => rw [he] at hr; exact absurd hr List.not_mem_nil
    | some e =>
      rw [he] at hr
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hr
      exact ⟨i, hi, e, he, d, hd, rfl⟩
  · rintro ⟨i, hi, e, he, d, hd, rfl⟩
    exact ⟨i, hi, by rw [he]; exact List.mem_map.mpr ⟨d, hd, rfl⟩⟩

theorem rowsAt_sub {net : SNet} {idx : List Nat} {r : SRow} (h : r ∈ rowsAt net idx) :
    r ∈ rowsOf net := by
  obtain ⟨i, -, e, he, d, hd, rfl⟩ := mem_rowsAt.mp h
  exact mem_rowsOf.mpr ⟨e, List.mem_of_getElem? he, d, hd, rfl⟩

theorem enAt_iff {net : SNet} {a : AMarking} {i : Nat} :
    enAt net a i = true ↔ ∃ e, net[i]? = some e ∧ enabledA a e.1 = true := by
  unfold enAt
  cases h : net[i]? with
  | none => simp
  | some e => simp

/-- Under `Outcomes`, the row-level dead markings are the transition-level ones. -/
theorem dead_iff {net : SNet} (hO : Outcomes net) (a : AMarking) :
    Novel.Stubborn.Dead (rowsOf net) a ↔ DeadT net a := by
  constructor
  · intro h e he
    obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ (hO e he)
    exact h (e.1, d) (mem_rowsOf.mpr ⟨e, he, d, hd, rfl⟩)
  · intro h r hr
    obtain ⟨e, he, d, -, rfl⟩ := mem_rowsOf.mp hr
    exact h e he

/-! ## Footprints, transition by transition -/

/-- `tests(t)`: its input, read and inhibitor places. -/
def testsT (e : TEntry) : List PlaceId := Novel.Stubborn.inPlaces e.1 ++ e.1.reads ++ e.1.inhibitors

/-- `writes(t)`: its input and reset places and every place an outcome deposits into. -/
def writesT (e : TEntry) : List PlaceId := Novel.Stubborn.inPlaces e.1 ++ e.1.resets ++ e.2.flatten

/-- `overwrites(t)`: its reset places and its consume-all inputs (`all`, `atLeast`). -/
def overwritesT (e : TEntry) : List PlaceId :=
  e.1.resets ++ (Novel.Stubborn.inPlaces e.1).filter (fun p => consumeAllAt e.1 p)

/-- **Dependency**: one writes what the other tests, or one overwrites what the other writes. -/
def dependentT (e f : TEntry) : Bool :=
  Novel.Stubborn.meets (writesT e) (testsT f) || Novel.Stubborn.meets (writesT f) (testsT e) ||
    Novel.Stubborn.meets (overwritesT e) (writesT f) ||
    Novel.Stubborn.meets (overwritesT f) (writesT e)

/-- `t` can increase `p`: an outcome deposits into `p`. -/
def increasesT (e : TEntry) (p : PlaceId) : Bool := e.2.any fun d => d.contains p

/-- `t` can decrease `p`: `p` is among its input or reset places. -/
def decreasesT (e : TEntry) (p : PlaceId) : Bool :=
  (Novel.Stubborn.inPlaces e.1).contains p || e.1.resets.contains p

/-! ## Enabling conditions in the pinned order -/

/-- One enabling condition: a place that needs `k` tokens (an input, or a read with `k = 1`), or
an inhibitor place that must be empty. -/
inductive Cond where
  /-- An input or read place `p` that needs `k` tokens. -/
  | need (p : PlaceId) (k : Nat)
  /-- An inhibitor place `p`. -/
  | inhib (p : PlaceId)
  deriving DecidableEq

/-- The place of a condition. -/
def Cond.place : Cond → PlaceId
  | .need p _ => p
  | .inhib p => p

/-- The condition does not hold at `a`. -/
def Cond.unsat (a : AMarking) : Cond → Bool
  | .need p k => decide (a p < k)
  | .inhib p => decide (0 < a p)

/-- **The conditions of a transition in the pinned order**: its input and read places in place
order (place ids follow the code-point order of the names), then its inhibitor places in place
order. -/
def conds (t : Transition) : List Cond :=
  ((t.inputs.map fun s => Cond.need s.place s.card.required) ++
      t.reads.map fun p => Cond.need p 1).insertionSort (fun x y => x.place ≤ y.place) ++
    (t.inhibitors.insertionSort (· ≤ ·)).map Cond.inhib

/-- **The first unsatisfied condition** of a transition at `a`, in the pinned order. -/
def firstUnsat (a : AMarking) (t : Transition) : Option Cond := (conds t).find? (·.unsat a)

/-- A transition can satisfy a condition: it can increase the place of an input or read
condition, or decrease the place of an inhibitor condition. -/
def fixes (e : TEntry) : Cond → Bool
  | .need p _ => increasesT e p
  | .inhib p => decreasesT e p

theorem mem_conds {t : Transition} {c : Cond} :
    c ∈ conds t ↔ (∃ s ∈ t.inputs, c = .need s.place s.card.required) ∨
      (∃ p ∈ t.reads, c = .need p 1) ∨ (∃ p ∈ t.inhibitors, c = .inhib p) := by
  simp only [conds, List.mem_append, (List.perm_insertionSort _ _).mem_iff, List.mem_map]
  constructor
  · rintro ((⟨s, hs, rfl⟩ | ⟨p, hp, rfl⟩) | ⟨p, hp, rfl⟩)
    · exact Or.inl ⟨s, hs, rfl⟩
    · exact Or.inr (Or.inl ⟨p, hp, rfl⟩)
    · exact Or.inr (Or.inr ⟨p, hp, rfl⟩)
  · rintro (⟨s, hs, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
    · exact Or.inl (Or.inl ⟨s, hs, rfl⟩)
    · exact Or.inl (Or.inr ⟨p, hp, rfl⟩)
    · exact Or.inr ⟨p, hp, rfl⟩

/-- A disabled transition has a first unsatisfied condition. -/
theorem firstUnsat_isSome {a : AMarking} {t : Transition} (h : enabledA a t = false) :
    ∃ c, firstUnsat a t = some c := by
  cases hf : firstUnsat a t with
  | some c => exact ⟨c, rfl⟩
  | none =>
    exfalso
    unfold firstUnsat at hf
    rw [List.find?_eq_none] at hf
    have : enabledA a t = true := by
      simp only [enabledA, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq]
      refine ⟨⟨fun s hs => ?_, fun p hp => ?_⟩, fun p hp => ?_⟩
      · have := hf _ (mem_conds.mpr (Or.inl ⟨s, hs, rfl⟩))
        simp only [Cond.unsat, decide_eq_true_eq] at this
        omega
      · have := hf _ (mem_conds.mpr (Or.inr (Or.inr ⟨p, hp, rfl⟩)))
        simp only [Cond.unsat, decide_eq_true_eq] at this
        omega
      · have := hf _ (mem_conds.mpr (Or.inr (Or.inl ⟨p, hp, rfl⟩)))
        simp only [Cond.unsat, decide_eq_true_eq] at this
        omega
    rw [this] at h
    exact absurd h (by simp)

/-! ## The closure S(s), declaratively -/

/-- **`S` is closed at `a`** (the two rules of the spec): for every transition `t` in `S`,
S-D1: if `t` is enabled, every transition dependent with it is in `S`; S-D2: if `t` is disabled,
every transition that can satisfy its first unsatisfied condition is in `S`. -/
def ClosedT (net : SNet) (a : AMarking) (S : Nat → Prop) : Prop :=
  ∀ i e, net[i]? = some e → S i →
    (enabledA a e.1 = true → ∀ j f, net[j]? = some f → dependentT e f = true → S j) ∧
    (enabledA a e.1 = false → ∀ c, firstUnsat a e.1 = some c →
      ∀ j f, net[j]? = some f → fixes f c = true → S j)

/-- **`i ∈ S(s)`**: `i` is in every closed set that contains `s`; `S(s)` is the least such set. -/
def InClosure (net : SNet) (a : AMarking) (s i : Nat) : Prop :=
  ∀ S : Nat → Prop, S s → ClosedT net a S → S i

open Classical in
/-- The number of enabled transitions in `S(s)`. -/
noncomputable def enabledCount (net : SNet) (a : AMarking) (s : Nat) : Nat :=
  ((List.range net.length).filter fun i => enAt net a i && decide (InClosure net a s i)).length

/-! ## The closure the route computes -/

/-- The indices of the transitions satisfying `f`, in net order. -/
def idxWhere (net : SNet) (f : TEntry → Bool) : List Nat :=
  (List.range net.length).filter fun j => (net[j]?.map f).getD false

theorem mem_idxWhere {net : SNet} {f : TEntry → Bool} {j : Nat} :
    j ∈ idxWhere net f ↔ ∃ e, net[j]? = some e ∧ f e = true := by
  simp only [idxWhere, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hj, h⟩
    refine ⟨net[j], List.getElem?_eq_getElem hj, ?_⟩
    rw [List.getElem?_eq_getElem hj] at h
    simpa using h
  · rintro ⟨e, he, hf⟩
    obtain ⟨hj, -⟩ := List.getElem?_eq_some_iff.mp he
    exact ⟨hj, by rw [he]; simpa using hf⟩

theorem lt_of_mem_idxWhere {net : SNet} {f : TEntry → Bool} {j : Nat}
    (h : j ∈ idxWhere net f) : j < net.length := by
  obtain ⟨e, he, -⟩ := mem_idxWhere.mp h
  exact (List.getElem?_eq_some_iff.mp he).1

/-- What a member requires, by the two rules. -/
abbrev ReqFn : Type := SNet → AMarking → Nat → List Nat

/-- **What member `i` requires** (the pinned rules): S-D1, every transition dependent with it
when it is enabled; S-D2, every transition that can satisfy its first unsatisfied condition when
it is disabled. -/
def reqT : ReqFn := fun net a i =>
  match net[i]? with
  | none => []
  | some e =>
    if enabledA a e.1 = true then idxWhere net (dependentT e)
    else
      match firstUnsat a e.1 with
      | some c => idxWhere net fun f => fixes f c
      | none => []

/-- Iterate rounds of a requirement function until nothing new is required. -/
def closureIter (req : ReqFn) (net : SNet) (a : AMarking) : Nat → List Nat → List Nat
  | 0, idx => idx
  | n + 1, idx =>
    if (idx.flatMap (req net a)).all (fun j => decide (j ∈ idx)) then idx
    else closureIter req net a n (idx ++ (idx.flatMap (req net a)).filter fun j => decide (j ∉ idx))

/-- The closure of seed `s` under a requirement function, as indices; `net.length + 1` rounds. -/
def closureWith (req : ReqFn) (net : SNet) (a : AMarking) (s : Nat) : List Nat :=
  closureIter req net a (net.length + 1) [s]

/-- A requirement function names only transitions of the net. -/
def ReqIn (req : ReqFn) : Prop := ∀ net a i, ∀ j ∈ req net a i, j < net.length

theorem reqT_in : ReqIn reqT := by
  intro net a i j h
  unfold reqT at h
  split at h
  · exact absurd h List.not_mem_nil
  · split at h
    · exact lt_of_mem_idxWhere h
    · split at h
      · exact lt_of_mem_idxWhere h
      · exact absurd h List.not_mem_nil

theorem closureIter_sup {req : ReqFn} {net : SNet} {a : AMarking} :
    ∀ (n : Nat) (idx : List Nat), ∀ i ∈ idx, i ∈ closureIter req net a n idx
  | 0, _, _, h => h
  | n + 1, idx, i, h => by
    simp only [closureIter]
    split
    · exact h
    · exact closureIter_sup n _ i (List.mem_append_left _ h)

/-- With more rounds than missing indices, the iteration stops at a set that requires nothing
outside itself. -/
theorem closureIter_closed {req : ReqFn} (hreq : ReqIn req) {net : SNet} {a : AMarking} :
    ∀ (n : Nat) (idx : List Nat), (∀ i ∈ idx, i < net.length) →
      (Finset.range net.length \ idx.toFinset).card < n →
      ∀ i ∈ closureIter req net a n idx, ∀ j ∈ req net a i, j ∈ closureIter req net a n idx
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, idx, hlt, hcard => by
    simp only [closureIter]
    split
    · rename_i hall
      rw [List.all_eq_true] at hall
      intro i hi j hj
      have := hall j (List.mem_flatMap.mpr ⟨i, hi, hj⟩)
      simpa using this
    · rename_i hall
      simp only [List.all_eq_true, not_forall, decide_eq_true_eq] at hall
      obtain ⟨j, hj, hjn⟩ := hall
      obtain ⟨i, hi, hji⟩ := List.mem_flatMap.mp hj
      have hgrow_sup : ∀ x ∈ idx,
          x ∈ idx ++ (idx.flatMap (req net a)).filter fun j => decide (j ∉ idx) :=
        fun x hx => List.mem_append_left _ hx
      have hj_grow : j ∈ idx ++ (idx.flatMap (req net a)).filter fun j => decide (j ∉ idx) :=
        List.mem_append_right _ (List.mem_filter.mpr ⟨hj, by simpa using hjn⟩)
      have hlt' : ∀ x ∈ idx ++ (idx.flatMap (req net a)).filter (fun j => decide (j ∉ idx)),
          x < net.length := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hlt x hx
        · obtain ⟨k, -, hk⟩ := List.mem_flatMap.mp (List.mem_filter.mp hx).1
          exact hreq net a k x hk
      apply closureIter_closed hreq n _ hlt'
      have hsub : Finset.range net.length \
            (idx ++ (idx.flatMap (req net a)).filter fun j => decide (j ∉ idx)).toFinset ⊆
          Finset.range net.length \ idx.toFinset := by
        intro x hx
        simp only [Finset.mem_sdiff, List.mem_toFinset] at hx ⊢
        exact ⟨hx.1, fun h => hx.2 (hgrow_sup x h)⟩
      have hss : Finset.range net.length \
            (idx ++ (idx.flatMap (req net a)).filter fun j => decide (j ∉ idx)).toFinset ⊂
          Finset.range net.length \ idx.toFinset := by
        rw [Finset.ssubset_iff_of_subset hsub]
        refine ⟨j, ?_, ?_⟩
        · simp only [Finset.mem_sdiff, List.mem_toFinset, Finset.mem_range]
          exact ⟨hreq net a i j hji, hjn⟩
        · simp only [Finset.mem_sdiff, List.mem_toFinset, not_and, not_not]
          exact fun _ => hj_grow
      have := Finset.card_lt_card hss
      omega

/-- The closure of a transition of the net requires nothing outside itself. -/
theorem closureWith_closed {req : ReqFn} (hreq : ReqIn req) {net : SNet} {a : AMarking} {s : Nat}
    (hs : s < net.length) :
    ∀ i ∈ closureWith req net a s, ∀ j ∈ req net a i, j ∈ closureWith req net a s := by
  apply closureIter_closed hreq _ [s] (fun i hi => by rw [List.mem_singleton.mp hi]; exact hs)
  have := Finset.card_le_card (Finset.sdiff_subset (s := Finset.range net.length)
    (t := [s].toFinset))
  rw [Finset.card_range] at this
  omega

/-- Every member of the iteration lies in every set that contains the start and requires nothing
outside itself. -/
theorem closureIter_least {req : ReqFn} {net : SNet} {a : AMarking} {S : Nat → Prop}
    (hS : ∀ i, S i → ∀ j ∈ req net a i, S j) :
    ∀ (n : Nat) (idx : List Nat), (∀ i ∈ idx, S i) → ∀ i ∈ closureIter req net a n idx, S i
  | 0, _, h => h
  | n + 1, idx, h => by
    simp only [closureIter]
    split
    · exact h
    · apply closureIter_least hS n
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact h x hx
      · obtain ⟨k, hk, hxk⟩ := List.mem_flatMap.mp (List.mem_filter.mp hx).1
        exact hS k (h k hk) x hxk

/-- A closed set in the declarative sense requires nothing outside itself under `reqT`. -/
theorem closedT_req {net : SNet} {a : AMarking} {S : Nat → Prop} (hS : ClosedT net a S) :
    ∀ i, S i → ∀ j ∈ reqT net a i, S j := by
  intro i hi j hj
  unfold reqT at hj
  cases he : net[i]? with
  | none => rw [he] at hj; exact absurd hj List.not_mem_nil
  | some e =>
    rw [he] at hj
    simp only at hj
    by_cases hen : enabledA a e.1 = true
    · rw [if_pos hen] at hj
      obtain ⟨f, hf, hdep⟩ := mem_idxWhere.mp hj
      exact (hS i e he hi).1 hen j f hf hdep
    · rw [if_neg hen] at hj
      have hdis : enabledA a e.1 = false := by simpa using hen
      cases hc : firstUnsat a e.1 with
      | none => rw [hc] at hj; exact absurd hj List.not_mem_nil
      | some c =>
        rw [hc] at hj
        obtain ⟨f, hf, hfix⟩ := mem_idxWhere.mp hj
        exact (hS i e he hi).2 hdis c hc j f hf hfix

/-- A set that requires nothing outside itself under `reqT` is closed in the declarative sense. -/
theorem req_closedT {net : SNet} {a : AMarking} {S : Nat → Prop}
    (hS : ∀ i, S i → ∀ j ∈ reqT net a i, S j) : ClosedT net a S := by
  intro i e he hi
  refine ⟨fun hen j f hf hdep => hS i hi j ?_, fun hdis c hc j f hf hfix => hS i hi j ?_⟩
  · simp only [reqT, he, hen, if_true]
    exact mem_idxWhere.mpr ⟨f, hf, hdep⟩
  · simp only [reqT, he, hdis, hc]
    exact mem_idxWhere.mpr ⟨f, hf, hfix⟩

/-- **The computed closure is `S(s)`**: for a transition `s` of the net, `i` is in the closure
`reqT` computes iff it is in every closed set containing `s`. -/
theorem inClosure_iff {net : SNet} {a : AMarking} {s i : Nat} (hs : s < net.length) :
    InClosure net a s i ↔ i ∈ closureWith reqT net a s := by
  constructor
  · intro h
    exact h (· ∈ closureWith reqT net a s)
      (closureIter_sup _ [s] s (List.mem_singleton_self _))
      (req_closedT (closureWith_closed reqT_in hs))
  · intro h S hs0 hcl
    exact closureIter_least (closedT_req hcl) _ [s] (by simpa using hs0) i h

/-! ## The reference selection -/

/-- The number of enabled transitions in the closure of `s` under `req`. -/
def countWith (req : ReqFn) (net : SNet) (a : AMarking) (s : Nat) : Nat :=
  ((List.range net.length).filter fun i => enAt net a i && (closureWith req net a s).contains i).length

/-- The seed order: fewest enabled members first, then the smaller name. -/
def seedKey (req : ReqFn) (net : SNet) (a : AMarking) (s : Nat) : Lex (Nat × String) :=
  toLex (countWith req net a s, nameAt net s)

/-- The enabled transitions, in net order. -/
def enabledIdx (net : SNet) (a : AMarking) : List Nat := (List.range net.length).filter (enAt net a)

/-- The seed: the enabled transition whose closure has the fewest enabled members, the smallest
name breaking ties (the first in net order on a full tie, which distinct names rule out). -/
def bestSeed (req : ReqFn) (net : SNet) (a : AMarking) : Option Nat :=
  (enabledIdx net a).argmin (seedKey req net a)

/-- The indices of a list sorted by transition name, ascending (code-point order of `String`). -/
def byName (net : SNet) (l : List Nat) : List Nat :=
  l.insertionSort fun i j => nameAt net i ≤ nameAt net j

/-- **A selection from a requirement function**: the enabled members of the closure of the best
seed, in ascending order of name (the canonical clock order of a class, [VER-010] AC1, which the
breadth-first build iterates). -/
def selWith (req : ReqFn) : SelFn := fun net a =>
  match bestSeed req net a with
  | none => []
  | some s => byName net
      ((List.range net.length).filter fun i => enAt net a i && (closureWith req net a s).contains i)

/-- **The reference selection** of [VER-024]: the pinned rules, the pinned seed choice. -/
def refSel : SelFn := selWith reqT

#spec_witness refSel

/-! ## The bridge to the row-level theory -/

/-- A row's dependency implies its transitions' dependency: the row footprints lie inside the
transition footprints. -/
theorem dependentT_of_rows {e f : TEntry} {d d' : Deposit} (hd : d ∈ e.2) (hd' : d' ∈ f.2)
    (h : Novel.Stubborn.Dependent (e.1, d) (f.1, d')) : dependentT e f = true := by
  have hw : ∀ (g : TEntry) (x : Deposit), x ∈ g.2 → ∀ p,
      p ∈ Novel.Stubborn.writes (g.1, x) → p ∈ writesT g := by
    intro g x hx p hp
    simp only [Novel.Stubborn.writes, writesT, List.mem_append, List.mem_flatten] at hp ⊢
    rcases hp with hp | hp
    · exact Or.inl hp
    · exact Or.inr ⟨x, hx, hp⟩
  have ht : ∀ (g : TEntry) (x : Deposit) p, p ∈ Novel.Stubborn.tests (g.1, x) → p ∈ testsT g :=
    fun _ _ _ hp => hp
  have ho : ∀ (g : TEntry) (x : Deposit) p,
      p ∈ Novel.Stubborn.overwrites (g.1, x) → p ∈ overwritesT g := fun _ _ _ hp => hp
  simp only [dependentT, Bool.or_eq_true, Novel.Stubborn.meets_iff]
  rcases Novel.Stubborn.dependent_iff.mp h with ⟨p, h1, h2⟩ | ⟨p, h1, h2⟩ | ⟨p, h1, h2⟩ |
      ⟨p, h1, h2⟩
  · exact Or.inl (Or.inl (Or.inl ⟨p, hw e d hd p h1, ht f d' p h2⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨p, hw f d' hd' p h1, ht e d p h2⟩))
  · exact Or.inl (Or.inr ⟨p, ho e d p h1, hw f d' hd' p h2⟩)
  · exact Or.inr ⟨p, ho f d' p h1, hw e d hd p h2⟩

/-- The first unsatisfied condition is a condition of the transition that does not hold. -/
theorem firstUnsat_sound {a : AMarking} {t : Transition} {c : Cond}
    (h : firstUnsat a t = some c) : c ∈ conds t ∧ c.unsat a = true :=
  ⟨List.mem_of_find?_eq_some h, List.find?_some h⟩

/-- **The bridge**: the rows of a set of transitions that requires nothing outside itself under
the pinned rules and holds an enabled seed with an outcome form a row-level stubborn set. -/
theorem closedT_stubborn {net : SNet} {a : AMarking} {idx : List Nat}
    (hcl : ∀ i ∈ idx, ∀ j ∈ reqT net a i, j ∈ idx) {s : Nat} {e0 : TEntry} {d0 : Deposit}
    (hs : s ∈ idx) (he0 : net[s]? = some e0) (hen0 : enabledA a e0.1 = true) (hd0 : d0 ∈ e0.2) :
    Novel.Stubborn.IsStubborn (rowsOf net) (rowsAt net idx) a := by
  refine ⟨⟨(e0.1, d0), mem_rowsAt.mpr ⟨s, hs, e0, he0, d0, hd0, rfl⟩, hen0⟩, ?_, ?_⟩
  · intro r hr hen u hu hdep
    obtain ⟨i, hi, e, he, d, hd, rfl⟩ := mem_rowsAt.mp hr
    obtain ⟨f, hf, d', hd', rfl⟩ := mem_rowsOf.mp hu
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hf
    refine mem_rowsAt.mpr ⟨j, hcl i hi j ?_, f, hj, d', hd', rfl⟩
    simp only [reqT, he, hen, if_true]
    exact mem_idxWhere.mpr ⟨f, hj, dependentT_of_rows hd hd' hdep⟩
  · intro r hr hdis
    obtain ⟨i, hi, e, he, d, hd, rfl⟩ := mem_rowsAt.mp hr
    obtain ⟨c, hc⟩ := firstUnsat_isSome hdis
    obtain ⟨hcm, hcu⟩ := firstUnsat_sound hc
    -- every row of a transition that can satisfy `c` is in the set
    have hfix : ∀ u ∈ rowsOf net, (∀ f d', d' ∈ f.2 → u = (f.1, d') → fixes f c = true) →
        u ∈ rowsAt net idx := by
      intro u hu hf
      obtain ⟨f, hfm, d', hd', rfl⟩ := mem_rowsOf.mp hu
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hfm
      refine mem_rowsAt.mpr ⟨j, hcl i hi j ?_, f, hj, d', hd', rfl⟩
      simp only [reqT, he, hdis, hc, Bool.false_eq_true, if_false]
      exact mem_idxWhere.mpr ⟨f, hj, hf f d' hd' rfl⟩
    have hinc : ∀ p k, c = .need p k → ∀ u ∈ rowsOf net,
        Novel.Stubborn.increases u p = true → u ∈ rowsAt net idx := by
      intro p k hcp u hu hinc
      refine hfix u hu fun f d' hd' hu' => ?_
      subst hcp hu'
      simp only [fixes, increasesT, List.any_eq_true]
      exact ⟨d', hd', hinc⟩
    have hdec : ∀ p, c = .inhib p → ∀ u ∈ rowsOf net,
        Novel.Stubborn.decreases u p = true → u ∈ rowsAt net idx := by
      intro p hcp u hu hdec
      refine hfix u hu fun f d' hd' hu' => ?_
      subst hcp hu'
      exact hdec
    rcases mem_conds.mp hcm with ⟨sp, hsp, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · simp only [Cond.unsat, decide_eq_true_eq] at hcu
      exact Or.inl ⟨sp, hsp, hcu, hinc _ _ rfl⟩
    · simp only [Cond.unsat, decide_eq_true_eq] at hcu
      exact Or.inr (Or.inl ⟨p, hp, by omega, hinc _ _ rfl⟩)
    · simp only [Cond.unsat, decide_eq_true_eq] at hcu
      exact Or.inr (Or.inr ⟨p, hp, hcu, hdec _ rfl⟩)

/-! ## The reference selection is a stubborn family -/

theorem mem_enabledIdx {net : SNet} {a : AMarking} {i : Nat} :
    i ∈ enabledIdx net a ↔ enAt net a i = true := by
  simp only [enabledIdx, List.mem_filter, List.mem_range, and_iff_right_iff_imp]
  intro h
  obtain ⟨e, he, -⟩ := enAt_iff.mp h
  exact (List.getElem?_eq_some_iff.mp he).1

theorem lt_of_enAt {net : SNet} {a : AMarking} {i : Nat} (h : enAt net a i = true) :
    i < net.length := by
  obtain ⟨e, he, -⟩ := enAt_iff.mp h
  exact (List.getElem?_eq_some_iff.mp he).1

/-- Some transition is enabled exactly when the seed exists. -/
theorem bestSeed_some {req : ReqFn} {net : SNet} {a : AMarking} (h : ∃ i, enAt net a i = true) :
    ∃ s, bestSeed req net a = some s ∧ enAt net a s = true := by
  obtain ⟨i, hi⟩ := h
  cases hb : bestSeed req net a with
  | none =>
    unfold bestSeed at hb
    rw [List.argmin_eq_none] at hb
    have := mem_enabledIdx.mpr hi
    rw [hb] at this
    exact absurd this List.not_mem_nil
  | some s => exact ⟨s, rfl, mem_enabledIdx.mp (List.argmin_mem hb)⟩

theorem mem_selWith {req : ReqFn} {net : SNet} {a : AMarking} {s i : Nat}
    (hb : bestSeed req net a = some s) :
    i ∈ selWith req net a ↔ enAt net a i = true ∧ i ∈ closureWith req net a s := by
  simp only [selWith, hb, byName, (List.perm_insertionSort _ _).mem_iff, List.mem_filter,
    List.mem_range, Bool.and_eq_true, List.contains_iff_mem]
  constructor
  · exact fun ⟨_, h⟩ => h
  · exact fun h => ⟨lt_of_enAt h.1, h⟩

theorem selWith_none {req : ReqFn} {net : SNet} {a : AMarking}
    (hb : bestSeed req net a = none) : selWith req net a = [] := by
  simp [selWith, hb]

/-- With distinct names, two transitions of the net with the same name are the same. -/
theorem nameAt_inj {net : SNet} (hn : (net.map fun e => e.1.name).Nodup) {i j : Nat}
    (hi : i < net.length) (hj : j < net.length) (h : nameAt net i = nameAt net j) : i = j := by
  have hg : (net.map fun e => e.1.name)[i]'(by simpa using hi) =
      (net.map fun e => e.1.name)[j]'(by simpa using hj) := by
    simpa [nameAt, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] using h
  exact (List.Nodup.getElem_inj_iff hn).mp hg

/-- **Sorting by name gives strictly ascending names** on a list of distinct transitions of a net
with distinct names. -/
theorem byName_sorted {net : SNet} (hn : (net.map fun e => e.1.name).Nodup) {l : List Nat}
    (hl : ∀ i ∈ l, i < net.length) (hnd : l.Nodup) :
    (byName net l).Pairwise fun i j => nameAt net i < nameAt net j := by
  haveI : Std.Total fun i j : Nat => nameAt net i ≤ nameAt net j := ⟨fun _ _ => le_total _ _⟩
  haveI : IsTrans Nat fun i j : Nat => nameAt net i ≤ nameAt net j := ⟨fun _ _ _ => le_trans⟩
  have hperm := List.perm_insertionSort (fun i j : Nat => nameAt net i ≤ nameAt net j) l
  have hs := List.pairwise_insertionSort (fun i j : Nat => nameAt net i ≤ nameAt net j) l
  have hnd' : (byName net l).Nodup := hperm.nodup_iff.mpr hnd
  refine (hs.and hnd').imp_of_mem fun hi hj ⟨hle, hne⟩ => lt_of_le_of_ne hle fun heq => hne ?_
  exact nameAt_inj hn (hl _ (hperm.mem_iff.mp hi)) (hl _ (hperm.mem_iff.mp hj)) heq

/-- A selection from a requirement function lists its picks in strictly ascending order of
name, on a net with distinct names. -/
theorem selWith_sorted {req : ReqFn} {net : SNet} {a : AMarking}
    (hn : (net.map fun e => e.1.name).Nodup) :
    (selWith req net a).Pairwise fun i j => nameAt net i < nameAt net j := by
  unfold selWith
  split
  · exact List.Pairwise.nil
  · exact byName_sorted hn (fun i hi => List.mem_range.mp (List.mem_filter.mp hi).1)
      (List.nodup_range.filter _)

theorem selWith_enabled {req : ReqFn} {net : SNet} {a : AMarking} {i : Nat}
    (h : i ∈ selWith req net a) : enAt net a i = true := by
  cases hb : bestSeed req net a with
  | none => rw [selWith_none hb] at h; exact absurd h List.not_mem_nil
  | some s => exact ((mem_selWith hb).mp h).1

/-- The rows the reference expands at `a` with a seed: every row of the closure. -/
def refStub (net : SNet) (a : AMarking) : List SRow :=
  match bestSeed reqT net a with
  | none => []
  | some s => rowsAt net (closureWith reqT net a s)

/-- Firing an enabled row of the selected (enabled) transitions is firing an enabled row of the
whole closure: the disabled members fire nothing. -/
theorem stepSel_ref_iff (net : SNet) (a b : AMarking) :
    StepSel refSel net a b ↔ StepAD (refStub net a) a b := by
  unfold StepSel refSel refStub
  cases hb : bestSeed reqT net a with
  | none => rw [selWith_none hb]; simp [StepAD, rowsAt]
  | some s =>
    simp only
    constructor
    · rintro ⟨r, hr, hen, rfl⟩
      obtain ⟨i, hi, e, he, d, hd, rfl⟩ := mem_rowsAt.mp hr
      exact ⟨_, mem_rowsAt.mpr ⟨i, ((mem_selWith hb).mp hi).2, e, he, d, hd, rfl⟩, hen, rfl⟩
    · rintro ⟨r, hr, hen, rfl⟩
      obtain ⟨i, hi, e, he, d, hd, rfl⟩ := mem_rowsAt.mp hr
      have hi' : i ∈ selWith reqT net a :=
        (mem_selWith hb).mpr ⟨enAt_iff.mpr ⟨e, he, hen⟩, hi⟩
      exact ⟨_, mem_rowsAt.mpr ⟨i, hi', e, he, d, hd, rfl⟩, hen, rfl⟩

/-- **The reference is a stubborn family** on every net whose transitions have outcomes. -/
theorem refStub_family {net : SNet} (hO : Outcomes net) :
    Novel.Stubborn.StubbornFamily (rowsOf net) (refStub net) := by
  refine ⟨fun a r hr => ?_, fun a hex => ?_⟩
  · unfold refStub at hr
    split at hr
    · exact absurd hr List.not_mem_nil
    · exact rowsAt_sub hr
  · obtain ⟨r, hr, hen⟩ := hex
    obtain ⟨e, hem, d, -, rfl⟩ := mem_rowsOf.mp hr
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hem
    obtain ⟨s, hb, hs⟩ := bestSeed_some (req := reqT) ⟨j, enAt_iff.mpr ⟨e, hj, hen⟩⟩
    obtain ⟨e0, he0, hen0⟩ := enAt_iff.mp hs
    obtain ⟨d0, hd0⟩ := List.exists_mem_of_ne_nil _ (hO e0 (List.mem_of_getElem? he0))
    simp only [refStub, hb]
    exact closedT_stubborn (closureWith_closed reqT_in (lt_of_enAt hs))
      (closureIter_sup _ [s] s (List.mem_singleton_self _)) he0 hen0 hd0

end Ver024

open Ver024

/-! ## VER-024 (B): what the reduced graph keeps -/

requirement VER_024
  id "VER-024"
  title "Stubborn-Set Reduction of the Enumeration Route"
  kind B
  scope "the enumeration route of VER-017 on a quiescence property, all implementations (SHOULD; the shall sentences bind an implementation that offers the reduction)"
  source verbatim "spec/07-verification.md"
  quote "*When* the route expands a class, it *shall* expand only enabled transitions, each with all of its outcomes."
        "*While* the reduction applies, every dead marking reachable from the initial marking *shall* be reachable by a run that fires, at each class, one of the transitions the route expands there."
        "*While* the reduction applies, a class *shall* have no reduced successor exactly when no transition is enabled at its marking."
  reading "For every net and marking, every transition the selection Sel picks is a transition of the net enabled at the marking."
          "For every net whose transitions each have at least one outcome, and all markings a0 and d: if d is reachable from a0 in the net (ReachAD over every outcome of every transition) and no transition is enabled at d, then d is reachable from a0 by reduced steps (StepSel: fire an enabled transition Sel picks at the current marking, with any of its outcomes)."
          "For every net whose transitions each have at least one outcome, and every marking a: a has no reduced successor iff no transition is enabled at a."
  assumes "The model is the untimed atomic abstraction of the net the graph is built on (VER-004), as rows of Novel/Stubborn.lean: a transition with all of its outcomes (TEntry), each outcome a deposit list, firing by fireAD and enabling by enabledA. The net is the one after the inert places of VER-001, the in-flight split of VER-004 and the terminal rewrites of EXEC-042; those rewrites are their own requirements. The conditions under which the reduction applies are VER_024_route below; ν-joins, environment places, timing and drained forwards (IO-014) are outside the model, as the first and third of those conditions exclude them. A drained forward's deposit depends on the marking, which a deposit list cannot express."
          "With all of its outcomes is the reduced step itself, not a line: StepSel fires a selected transition with each of its outcomes (rowsAt), so a selection names transitions, never single outcomes, and no selection can break that half of the first quoted sentence. The row-level closure of Novel/Stubborn.lean can hold one outcome of an input-less transition without the other (rowLevel_drops_an_outcome in the ver-c check); the transition-level selection here cannot."
          "Line 2 starts from any marking a0, which covers the initial marking of the second quoted sentence. A run that fires, at each class, one of the transitions the route expands there is a run of StepSel."
          "Classes are markings: the class key of an untimed graph is its marking (VER-017). The lines are stated on the reduced step relation, so they hold for the graph at every class budget. On a closed reduced graph the quiescent classes are exactly the reachable dead markings, so a property read off the quiescent classes is decided exactly (VER_024_exact, from the statement alone). That a violated is a real firing sequence, shortest in the reduced graph, and that a truncated reduced graph is read as in VER-017, are VER-017's lines over the reduced successor function; reduced steps are steps of the net, whatever the selection (VER_024_steps_sound)."
          "Ruling D22 (a): VER-024 is SHOULD, and its shall sentences bind an implementation that offers the reduction. Transition names are unique (rulings D10 and D23); place ids follow the code-point order of place names (the flattener's order, VER-013); no place carries both an input and a read arc of one transition (ruling D15, EXEC-012)."
          "AC1 (verdict with and without the reduction equal on the conformance corpus, every violated trace replays) is the corpus test, kind Q; lines 2 and 3 are the reason it holds (VER_024_exact)."
          "AC2 (k independent cycles of length n: at most 1 + k·n classes reduced, 1 + n^k full, the same verdict) is a corpus test over every k and n, kind Q; it is not proven for all k and n. VER_024_ac2 is one worked instance (k = 2, n = 3: 4 classes reduced, 10 full), and VER_024_nonvacuous the chain variant of the test derivation."
          "AC3 (a safety property builds the full graph) and AC4 (partialOrderReduction(false) gives the graph of VER-017) are VER_024_route, line 1."
          "AC5 (the same class count in every implementation) is VER_024_select: the selection, with its order, is a function of the net and the marking (VER_024_select_unique_list), so the reduced graph is."
          "AC6 (the report line Stubborn-set reduction (VER-024): on) is report text, kind Q. The default (on) is a quoted sentence of VER_024_route, kind N (ver024_defaultOn); the option names of the Implementation notes are kind N."
  signoff "2026-11-13 48e64fd98bd49532 ai"
  statement : SelFn → Prop :=
    fun Sel =>
      (∀ net a, ∀ i ∈ Sel net a, enAt net a i = true) ∧
      (∀ net, Outcomes net → ∀ a0 d, ReachAD (rowsOf net) a0 d → DeadT net d →
        Relation.ReflTransGen (StepSel Sel net) a0 d) ∧
      (∀ net, Outcomes net → ∀ a, (∀ b, ¬ StepSel Sel net a b) ↔ DeadT net a)

/- The pinned readable form of VER-024: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.VER_024 : SelFn → Prop :=
fun Sel =>
  (∀ (net : SNet) (a : AMarking), ∀ i ∈ Sel net a, enAt net a i = true) ∧
    (∀ (net : SNet),
        Outcomes net →
          ∀ (a0 d : AMarking), ReachAD (rowsOf net) a0 d → DeadT net d → Relation.ReflTransGen (StepSel Sel net) a0 d) ∧
      ∀ (net : SNet), Outcomes net → ∀ (a : AMarking), (∀ (b : AMarking), ¬StepSel Sel net a b) ↔ DeadT net a
-/
#guard_msgs in #print VER_024

/-- ✓ **The reference selection keeps every dead marking.** Example: on a net that forks one
token into two independent subnets, `refSel` expands one subnet at a time, yet every marking
where nothing is enabled is still reached: the transitions it picks form a stubborn set
(`refStub_family`, through the bridge `closedT_stubborn`), and a stubborn family keeps every
reachable dead marking (`stubborn_preserves_dead`) and stops exactly at the dead ones
(`reducedQuiescent_iff_dead`). -/
@[evidence holds VER_024]
theorem VER_024_reference : VER_024 refSel := by
  refine ⟨fun net a i hi => selWith_enabled hi, fun net hO a0 d hr hd => ?_, fun net hO a => ?_⟩
  · have h := Novel.Stubborn.stubborn_preserves_dead (refStub_family hO) hr ((dead_iff hO d).mpr hd)
    exact Relation.ReflTransGen.lift id (fun x y hxy => (stepSel_ref_iff net x y).mpr hxy) a0 d h
  · rw [← dead_iff hO, ← Novel.Stubborn.reducedQuiescent_iff_dead (refStub_family hO)]
    simp only [Novel.Stubborn.StepRed, stepSel_ref_iff]

/-- **Reduced steps are steps of the net**, whatever the selection: a reduced step fires an
enabled row of the net. Example: a violated trace read off a reduced graph is a firing sequence
of the net. -/
theorem VER_024_steps_sound {Sel : SelFn} {net : SNet} {a0 a : AMarking}
    (hr : Relation.ReflTransGen (StepSel Sel net) a0 a) : ReachAD (rowsOf net) a0 a :=
  Relation.ReflTransGen.lift id (fun _ _ ⟨r, hr, hen, he⟩ => ⟨r, rowsAt_sub hr, hen, he⟩) a0 a hr

namespace Ver024

/-- The reduced successors of a selection, as the breadth-first build of [VER-017] reads them. -/
def succSel (Sel : SelFn) (net : SNet) (a : AMarking) : List AMarking :=
  Novel.Enumeration.succRows (rowsAt net (Sel net a)) a

end Ver024

/-- **A closed reduced graph decides a quiescence property exactly**, from the statement alone.
Example: `deadlockFree` asks whether any reachable marking enables nothing; when the reduced
build closes, its classes without a successor are exactly those markings, so `Proven` on the
reduced graph means what `Proven` on the full graph means. -/
theorem VER_024_exact {Sel : SelFn} (h : VER_024 Sel) {net : SNet} (hO : Outcomes net)
    [DecidableEq AMarking] {maxClasses fuel : Nat} {a0 : AMarking}
    (hc : (Novel.Enumeration.build (succSel Sel net) maxClasses fuel a0).2 = true) (a : AMarking) :
    (a ∈ (Novel.Enumeration.build (succSel Sel net) maxClasses fuel a0).1 ∧
        succSel Sel net a = []) ↔ (ReachAD (rowsOf net) a0 a ∧ DeadT net a) := by
  have hreach : ∀ x y, Novel.Enumeration.Reach (succSel Sel net) x y ↔
      Relation.ReflTransGen (StepSel Sel net) x y := by
    intro x y
    unfold Novel.Enumeration.Reach
    have : (fun x y => y ∈ succSel Sel net x) = StepSel Sel net := by
      funext x y
      exact propext (Novel.Enumeration.succRows_iff_step _ x y)
    rw [this]
  have hnil : ∀ x, succSel Sel net x = [] ↔ ∀ y, ¬ StepSel Sel net x y := by
    intro x
    rw [List.eq_nil_iff_forall_not_mem]
    exact forall_congr' fun y => not_congr (Novel.Enumeration.succRows_iff_step _ x y)
  rw [hnil, h.2.2 net hO a]
  constructor
  · rintro ⟨ha, hd⟩
    exact ⟨VER_024_steps_sound ((hreach a0 a).mp (Novel.Enumeration.build_reach a ha)), hd⟩
  · rintro ⟨hr, hd⟩
    exact ⟨(Novel.Enumeration.run_complete_iff_reach hc a).mpr
      ((hreach a0 a).mpr (h.2.1 net hO a0 a hr hd)), hd⟩

namespace Ver024

/-! ## Small nets, written as vectors of counts -/

/-- The marking with the counts of a list, zero on every later place. -/
def mkM (l : List Nat) : AMarking := fun p => l.getD p 0

/-- The counts of the first `n` places. -/
def window (n : Nat) (a : AMarking) : List Nat := (List.range n).map a

/-- Every place a transition of the net tests or writes lies below `n`. -/
def PlacesBelow (net : SNet) (n : Nat) : Bool :=
  net.all fun e => (testsT e ++ writesT e).all (· < n)

theorem window_mkM {l : List Nat} {n : Nat} (hl : l.length = n) : window n (mkM l) = l := by
  subst hl
  apply List.ext_getElem (by simp [window])
  intro i h1 h2
  simp [window, mkM, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- Firing a transition of the net on a vector marking gives the vector marking of its window. -/
theorem fire_mkM {net : SNet} {n : Nat} (hP : PlacesBelow net n = true) {l : List Nat}
    (hl : l.length = n) {e : TEntry} (he : e ∈ net) {d : Deposit} (hd : d ∈ e.2) :
    fireAD (mkM l) e.1 d = mkM (window n (fireAD (mkM l) e.1 d)) := by
  funext p
  by_cases hp : p < n
  · simp [mkM, window, List.getD_eq_getElem?_getD, hp]
  · have hw : p ∉ Novel.Stubborn.writes (e.1, d) := by
      intro hm
      have h1 := List.all_eq_true.mp hP e he
      have h2 := List.all_eq_true.mp h1 p (by
        simp only [writesT, Novel.Stubborn.writes, List.mem_append, List.mem_flatten] at hm ⊢
        rcases hm with hm | hm
        · exact Or.inr (Or.inl hm)
        · exact Or.inr (Or.inr ⟨d, hd, hm⟩))
      exact hp (by simpa using h2)
    rw [Novel.Stubborn.fire_unwritten hw]
    simp [mkM, window, List.getD_eq_getElem?_getD, hp, hl]

/-- **Reduced reachability on a window**: if a finite set `W` of vectors holds the start and is
closed under the reduced steps, every marking the reduced steps reach is a vector of `W`. -/
theorem reach_window {Sel : SelFn} {net : SNet} {n : Nat} (hP : PlacesBelow net n = true)
    (W : List (List Nat)) (hW : ∀ l ∈ W, l.length = n)
    (hcl : ∀ l ∈ W, ∀ r ∈ rowsAt net (Sel net (mkM l)), enabledA (mkM l) r.1 = true →
      window n (fireAD (mkM l) r.1 r.2) ∈ W)
    {l0 : List Nat} (h0 : l0 ∈ W) {b : AMarking}
    (h : Relation.ReflTransGen (StepSel Sel net) (mkM l0) b) : ∃ l ∈ W, b = mkM l := by
  induction h with
  | refl => exact ⟨l0, h0, rfl⟩
  | tail _ hs ih =>
    obtain ⟨l, hl, rfl⟩ := ih
    obtain ⟨r, hr, hen, rfl⟩ := hs
    obtain ⟨i, -, e, he, d, hd, rfl⟩ := mem_rowsAt.mp hr
    exact ⟨_, hcl l hl _ hr hen, fire_mkM hP (hW l hl) (List.mem_of_getElem? he) hd⟩

/-- One full step on vector markings, checked on the window. -/
theorem stepAD_mkM {net : SNet} {n : Nat} (hP : PlacesBelow net n = true) {l l' : List Nat}
    (hl : l.length = n) {i : Nat} {e : TEntry} (he : net[i]? = some e) {d : Deposit} (hd : d ∈ e.2)
    (hen : enabledA (mkM l) e.1 = true) (hw : window n (fireAD (mkM l) e.1 d) = l') :
    StepAD (rowsOf net) (mkM l) (mkM l') :=
  ⟨(e.1, d), mem_rowsOf.mpr ⟨e, List.mem_of_getElem? he, d, hd, rfl⟩, hen, by
    rw [← hw]; exact (fire_mkM hP hl (List.mem_of_getElem? he) hd).symm⟩

/-- One reduced step on vector markings, checked on the window. -/
theorem stepSel_mkM {Sel : SelFn} {net : SNet} {n : Nat} (hP : PlacesBelow net n = true)
    {l l' : List Nat} (hl : l.length = n) {i : Nat} (hi : i ∈ Sel net (mkM l)) {e : TEntry}
    (he : net[i]? = some e) {d : Deposit} (hd : d ∈ e.2) (hen : enabledA (mkM l) e.1 = true)
    (hw : window n (fireAD (mkM l) e.1 d) = l') : StepSel Sel net (mkM l) (mkM l') :=
  ⟨(e.1, d), mem_rowsAt.mpr ⟨i, hi, e, he, d, hd, rfl⟩, hen, by
    rw [← hw]; exact (fire_mkM hP hl (List.mem_of_getElem? he) hd).symm⟩

/-- A vector outside `W` is not the marking of a vector in `W`. -/
theorem mkM_not_mem {W : List (List Nat)} {n : Nat} (hW : ∀ l ∈ W, l.length = n)
    {ld : List Nat} (hld : ld.length = n) (hout : ld ∉ W) : ¬ ∃ l ∈ W, mkM ld = mkM l := by
  rintro ⟨l, hl, heq⟩
  have := congrArg (window n) heq
  rw [window_mkM hld, window_mkM (hW l hl)] at this
  exact hout (this ▸ hl)

/-- A transition with plain one-token inputs and outputs. -/
def ver024T (name : String) (ins : List PlaceId) : Transition :=
  { name, inputs := ins.map fun p => ⟨p, .one, none⟩, inhibitors := [], reads := [], resets := [] }

end Ver024

/-! ### Worked examples -/

/-- The chain variant of the test derivation with `k = 2` chains of length 1: `fork` puts a token
on places 1 and 3, `a` moves it from 1 to 2, `b` from 3 to 4. -/
def ver024Chain : SNet :=
  [(ver024T "fork" [0], [[1, 3]]), (ver024T "a" [1], [[2]]), (ver024T "b" [3], [[4]])]

/-- ✓ **The reduction is real and keeps the dead marking.** Example: after `fork`, both `a` and
`b` are enabled, but each closure holds one enabled transition, and the name `a` wins the tie,
so the reference expands only `a` there. The marking with tokens on 2 and 4, where nothing is
enabled, is still reached by the reduced steps: `fork`, then `a`, then `b`. -/
@[evidence nonvacuous VER_024]
theorem VER_024_nonvacuous :
    Outcomes ver024Chain ∧ ReachAD (rowsOf ver024Chain) (mkM [1, 0, 0, 0, 0]) (mkM [0, 0, 1, 0, 1]) ∧
      DeadT ver024Chain (mkM [0, 0, 1, 0, 1]) ∧
      refSel ver024Chain (mkM [0, 1, 0, 1, 0]) = [1] ∧
      Relation.ReflTransGen (StepSel refSel ver024Chain) (mkM [1, 0, 0, 0, 0]) (mkM [0, 0, 1, 0, 1]) := by
  have hP : PlacesBelow ver024Chain 5 = true := by decide
  refine ⟨by decide, ?_, by decide, by decide, ?_⟩
  · exact Relation.ReflTransGen.head
      (stepAD_mkM hP (l' := [0, 1, 0, 1, 0]) rfl (i := 0) rfl (d := [1, 3]) (by decide) (by decide)
        (by decide))
      (Relation.ReflTransGen.head
        (stepAD_mkM hP (l' := [0, 0, 1, 1, 0]) rfl (i := 1) rfl (d := [2]) (by decide) (by decide)
          (by decide))
        (Relation.ReflTransGen.single
          (stepAD_mkM hP rfl (i := 2) rfl (d := [4]) (by decide) (by decide) (by decide))))
  · exact Relation.ReflTransGen.head
      (stepSel_mkM hP (l' := [0, 1, 0, 1, 0]) rfl (i := 0) (by decide) rfl (d := [1, 3]) (by decide)
        (by decide) (by decide))
      (Relation.ReflTransGen.head
        (stepSel_mkM hP (l' := [0, 0, 1, 1, 0]) rfl (i := 1) (by decide) rfl (d := [2]) (by decide)
          (by decide) (by decide))
        (Relation.ReflTransGen.single
          (stepSel_mkM hP rfl (i := 2) (by decide) rfl (d := [4]) (by decide) (by decide)
            (by decide))))

namespace Ver024

/-- The selection that expands every enabled transition: the full graph of [VER-017]. -/
def fullSel : SelFn := fun net a => enabledIdx net a

/-- The breadth-first build of [VER-017] over a selection, on markings written as vectors of the
first `n` places. -/
def buildV (Sel : SelFn) (net : SNet) (n budget : Nat) (l0 : List Nat) : List (List Nat) × Bool :=
  Novel.Enumeration.build (fun l => (succSel Sel net (mkM l)).map (window n)) budget budget l0

end Ver024

/-- AC2's net with `k = 2` cycles of length `n = 3`: `fork` puts a token on places 1 and 4; `a0`,
`a1`, `a2` move one around 1, 2, 3, and `b0`, `b1`, `b2` the other around 4, 5, 6. -/
def ver024Cycles : SNet :=
  [(ver024T "fork" [0], [[1, 4]]),
   (ver024T "a0" [1], [[2]]), (ver024T "a1" [2], [[3]]), (ver024T "a2" [3], [[1]]),
   (ver024T "b0" [4], [[5]]), (ver024T "b1" [5], [[6]]), (ver024T "b2" [6], [[4]])]

/-- **AC2 on two cycles of length 3.** Example: the full build closes with `1 + 3^2 = 10`
classes; the reduced build closes with `1 + 3 = 4`, within AC2's bound `1 + 2·3 = 7`, because the
tie-break keeps advancing the first cycle. No class of either graph is without a successor, so
`deadlockFree` is proven on both: the same verdict. -/
theorem VER_024_ac2 :
    (buildV fullSel ver024Cycles 7 100 [1, 0, 0, 0, 0, 0, 0]).1.length = 10 ∧
      (buildV fullSel ver024Cycles 7 100 [1, 0, 0, 0, 0, 0, 0]).2 = true ∧
      (buildV refSel ver024Cycles 7 100 [1, 0, 0, 0, 0, 0, 0]).1.length = 4 ∧
      (buildV refSel ver024Cycles 7 100 [1, 0, 0, 0, 0, 0, 0]).2 = true ∧
      (buildV refSel ver024Cycles 7 100 [1, 0, 0, 0, 0, 0, 0]).1.all
        (fun l => !(succSel refSel ver024Cycles (mkM l)).isEmpty) = true ∧
      (buildV fullSel ver024Cycles 7 100 [1, 0, 0, 0, 0, 0, 0]).1.all
        (fun l => !(succSel fullSel ver024Cycles (mkM l)).isEmpty) = true := by
  decide

/-! ### Wrong selections -/

/-- Mutant: expand nothing. -/
def ver024_nothing : SelFn := fun _ _ => []

/-- One transition with no arcs and one outcome that deposits nothing: enabled everywhere. -/
def ver024Free : SNet := [(ver024T "t" [], [[]])]

/-- ✗ **A class with an enabled transition has a successor** (line 3). Example: `t` has no arcs,
so it is enabled at the empty marking; a selection that expands nothing leaves that class
without a successor, and the route would report a deadlock that does not exist. -/
@[evidence forbids VER_024]
theorem VER_024_forbids_nothing : ¬ VER_024 ver024_nothing := by
  intro h
  have hd := ((h.2.2 ver024Free (by decide) (mkM [])).mp (fun b ⟨r, hr, _⟩ => by
    simp [ver024_nothing, rowsAt] at hr))
  revert hd
  decide

/-- Mutant: the reference selection plus every disabled transition. -/
def ver024_withDisabled : SelFn := fun net a =>
  refSel net a ++ (List.range net.length).filter fun i => !enAt net a i

/-- One transition that needs a token on place 0. -/
def ver024Blocked : SNet := [(ver024T "t" [0], [[]])]

/-- ✗ **Only enabled transitions are picked** (line 1). Example: with place 0 empty, `t` is
disabled; a selection that also lists it names a transition the route cannot expand. Its steps
are the reference's, so only line 1 tells it apart. -/
@[evidence forbids VER_024]
theorem VER_024_forbids_withDisabled : ¬ VER_024 ver024_withDisabled := by
  intro h
  have := h.1 ver024Blocked (mkM [0]) 0 (by decide)
  revert this
  decide

/-- Mutant: expand only the first enabled transition, with no closure. -/
def ver024_seedOnly : SelFn := fun net a => (enabledIdx net a).take 1

/-- A conflict: `a` and `b` both take the token on place 0, to place 1 or to place 2. -/
def ver024Conflict : SNet := [(ver024T "a" [0], [[1]]), (ver024T "b" [0], [[2]])]

/-- ✗ **Expanding only the seed loses a dead marking** (line 2). Example: `a` and `b` compete for
one token. Expanding `a` alone reaches only the dead marking with a token on place 1; the dead
marking with a token on place 2, which `b` reaches, is lost. S-D1 puts `b` into the set, since
the two share their input place. -/
@[evidence forbids VER_024]
theorem VER_024_forbids_seedOnly : ¬ VER_024 ver024_seedOnly := by
  intro h
  have hP : PlacesBelow ver024Conflict 3 = true := by decide
  have hr : ReachAD (rowsOf ver024Conflict) (mkM [1, 0, 0]) (mkM [0, 0, 1]) :=
    Relation.ReflTransGen.single
      (stepAD_mkM hP rfl (i := 1) rfl (d := [2]) (by decide) (by decide) (by decide))
  have hR := h.2.1 ver024Conflict (by decide) _ _ hr (by decide)
  obtain ⟨l, hl, heq⟩ := reach_window hP [[1, 0, 0], [0, 1, 0]] (by decide) (by decide)
    (by decide) hR
  exact mkM_not_mem (W := [[1, 0, 0], [0, 1, 0]]) (n := 3) (by decide) rfl (by decide) ⟨l, hl, heq⟩

namespace Ver024

/-- The rules without S-D2: a disabled member requires nothing. -/
def reqNoD2 : ReqFn := fun net a i =>
  match net[i]? with
  | none => []
  | some e => if enabledA a e.1 = true then idxWhere net (dependentT e) else []

end Ver024

/-- Mutant: the pinned choice over closures without S-D2. -/
def ver024_noD2 : SelFn := selWith reqNoD2

/-- `s` takes place 0 to 3; `t` needs places 0 and 2 and puts a token on 4; `u` takes place 1
to 2, which enables `t`. -/
def ver024Enabler : SNet :=
  [(ver024T "s" [0], [[3]]), (ver024T "t" [0, 2], [[4]]), (ver024T "u" [1], [[2]])]

/-- ✗ **Without S-D2 a dead marking is lost** (line 2). Example: from tokens on 0 and 1, `t` is
disabled but shares place 0 with `s`. Without S-D2 the closures of `s` and of `u` each hold one
enabled transition, the name `s` wins, and `s` fires first, which disables `t` for good. The dead
marking with one token on place 4 (`u`, then `t`) is lost. S-D2 puts `u`, which can increase
`t`'s missing place 2, into the set of `s`. -/
@[evidence forbids VER_024]
theorem VER_024_forbids_noD2 : ¬ VER_024 ver024_noD2 := by
  intro h
  have hP : PlacesBelow ver024Enabler 5 = true := by decide
  have hr : ReachAD (rowsOf ver024Enabler) (mkM [1, 1, 0, 0, 0]) (mkM [0, 0, 0, 0, 1]) :=
    Relation.ReflTransGen.head
      (stepAD_mkM hP (l' := [1, 0, 1, 0, 0]) rfl (i := 2) rfl (d := [2]) (by decide) (by decide)
        (by decide))
      (Relation.ReflTransGen.single
        (stepAD_mkM hP rfl (i := 1) rfl (d := [4]) (by decide) (by decide) (by decide)))
  have hR := h.2.1 ver024Enabler (by decide) _ _ hr (by decide)
  obtain ⟨l, hl, heq⟩ := reach_window hP [[1, 1, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 1, 1, 0]]
    (by decide) (by decide) (by decide) hR
  exact mkM_not_mem (W := [[1, 1, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 1, 1, 0]]) (n := 5)
    (by decide) rfl (by decide) ⟨l, hl, heq⟩

namespace Ver024

/-- Dependency without the two overwrite clauses. -/
def dependentNoOw (e f : TEntry) : Bool :=
  Novel.Stubborn.meets (writesT e) (testsT f) || Novel.Stubborn.meets (writesT f) (testsT e)

/-- The rules with that dependency. -/
def reqNoOw : ReqFn := fun net a i =>
  match net[i]? with
  | none => []
  | some e =>
    if enabledA a e.1 = true then idxWhere net (dependentNoOw e)
    else
      match firstUnsat a e.1 with
      | some c => idxWhere net fun f => fixes f c
      | none => []

end Ver024

/-- Mutant: the pinned choice over closures whose dependency ignores overwrites. -/
def ver024_noOverwrites : SelFn := selWith reqNoOw

/-- A reset race: `t` takes place 0 and clears place 2; `u` takes place 1 and puts a token on
place 2. -/
def ver024Race : SNet :=
  [({ name := "t", inputs := [⟨0, .one, none⟩], inhibitors := [], reads := [], resets := [2] },
      [[]]),
   (ver024T "u" [1], [[2]])]

/-- ✗ **Without the overwrite clauses a dead marking is lost** (line 2). Example: `t` clears place
2 and `u` fills it; neither tests a place the other writes, so a dependency without the overwrite
clauses calls them independent. The name `t` wins the tie and `t` fires first, so the run ends
with one token on place 2; the dead marking with place 2 empty (`u`, then `t`) is lost. -/
@[evidence forbids VER_024]
theorem VER_024_forbids_noOverwrites : ¬ VER_024 ver024_noOverwrites := by
  intro h
  have hP : PlacesBelow ver024Race 3 = true := by decide
  have hr : ReachAD (rowsOf ver024Race) (mkM [1, 1, 0]) (mkM [0, 0, 0]) :=
    Relation.ReflTransGen.head
      (stepAD_mkM hP (l' := [1, 0, 1]) rfl (i := 1) rfl (d := [2]) (by decide) (by decide)
        (by decide))
      (Relation.ReflTransGen.single
        (stepAD_mkM hP rfl (i := 0) rfl (d := []) (by decide) (by decide) (by decide)))
  have hR := h.2.1 ver024Race (by decide) _ _ hr (by decide)
  obtain ⟨l, hl, heq⟩ := reach_window hP [[1, 1, 0], [0, 1, 0], [0, 0, 1]]
    (by decide) (by decide) (by decide) hR
  exact mkM_not_mem (W := [[1, 1, 0], [0, 1, 0], [0, 0, 1]]) (n := 3) (by decide) rfl (by decide)
    ⟨l, hl, heq⟩

/-! ## VER-024 (F): the pinned choice -/

requirement VER_024_select
  id "VER-024"
  title "Stubborn-Set Reduction: the pinned stubborn set"
  kind F
  scope "the stubborn set the enumeration route expands at each class, all implementations"
  source verbatim "spec/07-verification.md"
  quote "*While* the reduction applies, *when* the route expands a class whose marking `M` enables a transition, it *shall* expand exactly the enabled transitions of `S(s)` for the enabled seed `s` whose closure has the fewest enabled transitions, the code-point-smallest seed name breaking ties."
        "*When* a transition `t` of `S(s)` is disabled at `M`, the closure *shall* read its first unsatisfied condition over its input and read places in code-point order of place name, then over its inhibitor places in code-point order."
        "*While* the reduction applies, the route *shall* expand the transitions it selects at a class in ascending code-point order of transition name."
  reading "For every net whose transition names are distinct and every marking: every transition Sel picks is enabled."
          "If some transition is enabled, there is an enabled seed s0 such that: Sel picks exactly the enabled transitions i in S(s0) (InClosure: i is in every set that contains s0 and is closed under S-D1 and S-D2, with S-D2 reading the first unsatisfied condition in the pinned order, firstUnsat over conds);"
          "no enabled seed has fewer enabled transitions in its closure than s0 (enabledCount);"
          "every enabled seed with as many enabled transitions in its closure as s0 has a name no smaller than s0's (String order, which is code-point order)."
          "Sel lists the transitions it picks in strictly ascending order of name, the order in which the route expands them."
  assumes "The closure is stated as the spec defines it, the least set containing the seed and closed under the two rules (InClosure over ClosedT); refSel computes it by rounds from the seed (closureWith reqT), and inClosure_iff shows the two agree. Dependency, the increasers and the decreasers are those of the Footprints paragraph over all outcomes of a transition (testsT, writesT, overwritesT, dependentT, increasesT, decreasesT). S-D1 for t = u adds nothing, as t is already in the set, so the closedness rule does not exclude it."
          "The order of conditions is a function (conds): input and read places together, sorted by place id, then inhibitor places sorted by place id. Place ids follow the code-point order of place names (the flattener's order, VER-013), so the sort is the code-point order of the spec; that link from names to ids is an assumption about the flattener, not a line, and the runtimes sort by name directly. No place carries both an input and a read of one transition (ruling D15), so the merged order has no tie; two input specs on one place are excluded by the builders. The runtimes build the same list (stubborn_sets.rs:66-88, StubbornSets.java:59-78, stubborn-sets.ts:59-76). Three wrong orders are killed: Novel/Stubborn.lean's firstBlocker order, inputs then reads (VER_024_select_forbids_inputsFirst); the merged list in descending place order (VER_024_select_forbids_descending); inhibitors before inputs and reads (VER_024_select_forbids_inhibitorsFirst)."
          "Transition names are distinct (rulings D10 and D23), a premise of every line: with two equal names the tie-break does not single out one seed, and the runtimes index transitions by name. The runtimes' early cut (a closure stops counting once it reaches the best count so far) and their stop at a count of 1 change no choice, so they are not in the model."
          "Line 5 is the expansion order. A class keeps its enabled transitions in the canonical clock order of VER-010 AC1, ascending by name in code-point order; the breadth-first build iterates that list and the selection only filters it (state_class_graph.rs:193, StateClassGraph.java:580, state-class-graph.ts:166). With lines 2 to 4 it fixes the list of transitions a class expands, so with the order of each transition's outcomes (the net's, VER-021) it fixes the reduced graph, the order in which its classes are found, and which classes a truncated build expands (AC5; the order mutant is killed by VER_024_select_forbids_netOrder)."
  signoff "2026-11-13 2b7d225579be0e67 ai"
  statement : SelFn → Prop :=
    fun Sel =>
      ∀ net a, (net.map fun e => e.1.name).Nodup →
        (∀ i ∈ Sel net a, enAt net a i = true) ∧
        ((∃ s, enAt net a s = true) → ∃ s0, enAt net a s0 = true ∧
          (∀ i, i ∈ Sel net a ↔ enAt net a i = true ∧ InClosure net a s0 i) ∧
          (∀ s, enAt net a s = true → enabledCount net a s0 ≤ enabledCount net a s) ∧
          (∀ s, enAt net a s = true → enabledCount net a s = enabledCount net a s0 →
            nameAt net s0 ≤ nameAt net s)) ∧
        (Sel net a).Pairwise fun i j => nameAt net i < nameAt net j

/- The pinned readable form of VER-024's choice block. -/
/--
info: def Libpetri.Spec.VER_024_select : SelFn → Prop :=
fun Sel =>
  ∀ (net : SNet) (a : AMarking),
    (List.map (fun e => e.1.name) net).Nodup →
      (∀ i ∈ Sel net a, enAt net a i = true) ∧
        ((∃ s, enAt net a s = true) →
            ∃ s0,
              enAt net a s0 = true ∧
                (∀ (i : ℕ), i ∈ Sel net a ↔ enAt net a i = true ∧ InClosure net a s0 i) ∧
                  (∀ (s : ℕ), enAt net a s = true → enabledCount net a s0 ≤ enabledCount net a s) ∧
                    ∀ (s : ℕ),
                      enAt net a s = true →
                        enabledCount net a s = enabledCount net a s0 → nameAt net s0 ≤ nameAt net s) ∧
          List.Pairwise (fun i j => nameAt net i < nameAt net j) (Sel net a)
-/
#guard_msgs in #print VER_024_select

namespace Ver024

/-- The declarative count is the computed one. -/
theorem enabledCount_eq {net : SNet} {a : AMarking} {s : Nat} (hs : s < net.length) :
    enabledCount net a s = countWith reqT net a s := by
  classical
  unfold enabledCount countWith
  congr 1
  apply List.filter_congr
  intro i _
  simp only [inClosure_iff hs]
  cases enAt net a i <;> simp

end Ver024

/-- ✓ **The reference makes the pinned choice.** Example: after `fork` in the chain net, the
closures of `a` and of `b` each hold one enabled transition; `refSel` takes the seed `a`, the
smaller name, and expands `a` alone. It takes the seed with the least key (count of enabled
members, then name) over the enabled transitions (`List.argmin`), and its closure is the least
closed set (`inClosure_iff`). -/
@[evidence holds VER_024_select]
theorem VER_024_select_reference : VER_024_select refSel := by
  intro net a hn
  refine ⟨fun i hi => selWith_enabled hi, fun hex => ?_, selWith_sorted hn⟩
  obtain ⟨s0, hb, hs0⟩ := bestSeed_some (req := reqT) hex
  have hlt0 := lt_of_enAt hs0
  have hkey : ∀ s, enAt net a s = true → seedKey reqT net a s0 ≤ seedKey reqT net a s := by
    intro s hs
    have := (List.argmin_eq_some_iff.mp hb).2.1 s (mem_enabledIdx.mpr hs)
    exact this
  refine ⟨s0, hs0, fun i => ?_, fun s hs => ?_, fun s hs heq => ?_⟩
  · rw [show refSel = selWith reqT from rfl, mem_selWith hb]
    constructor
    · rintro ⟨hi, hc⟩; exact ⟨hi, (inClosure_iff hlt0).mpr hc⟩
    · rintro ⟨hi, hc⟩; exact ⟨hi, (inClosure_iff hlt0).mp hc⟩
  · have := hkey s hs
    rw [enabledCount_eq hlt0, enabledCount_eq (lt_of_enAt hs)]
    simp only [seedKey, Prod.Lex.toLex_le_toLex] at this
    omega
  · have := hkey s hs
    rw [enabledCount_eq hlt0, enabledCount_eq (lt_of_enAt hs)] at heq
    simp only [seedKey, Prod.Lex.toLex_le_toLex] at this
    rcases this with h | ⟨_, h⟩
    · omega
    · exact h

/-- **The choice is unique**, from the statement alone: two selections that both make the pinned
choice pick the same transitions on every net with distinct names. Example: there is one seed
with the fewest enabled members and the smallest name, so one stubborn set. -/
theorem VER_024_select_unique {Sel Sel' : SelFn} (h : VER_024_select Sel)
    (h' : VER_024_select Sel') {net : SNet} (hn : (net.map fun e => e.1.name).Nodup)
    (a : AMarking) (i : Nat) : i ∈ Sel net a ↔ i ∈ Sel' net a := by
  by_cases hex : ∃ s, enAt net a s = true
  · obtain ⟨s0, hs0, hm0, hc0, ht0⟩ := (h net a hn).2.1 hex
    obtain ⟨s1, hs1, hm1, hc1, ht1⟩ := (h' net a hn).2.1 hex
    have hcnt : enabledCount net a s1 = enabledCount net a s0 :=
      le_antisymm (hc1 s0 hs0) (hc0 s1 hs1)
    have hname : nameAt net s0 = nameAt net s1 :=
      le_antisymm (ht0 s1 hs1 hcnt) (ht1 s0 hs0 hcnt.symm)
    have heq : s0 = s1 := nameAt_inj hn (lt_of_enAt hs0) (lt_of_enAt hs1) hname
    subst heq
    rw [hm0, hm1]
  · have hn0 : ∀ j ∈ Sel net a, False := fun j hj => hex ⟨j, (h net a hn).1 j hj⟩
    have hn1 : ∀ j ∈ Sel' net a, False := fun j hj => hex ⟨j, (h' net a hn).1 j hj⟩
    exact ⟨fun hi => (hn0 i hi).elim, fun hi => (hn1 i hi).elim⟩

/-- **The choice is unique, order included**, from the statement alone: two selections that both
make the pinned choice give the same list on every net with distinct names. Example: one stubborn
set, expanded in ascending order of name, so one reduced graph, found in one order, and one class
count in every implementation (AC5). -/
theorem VER_024_select_unique_list {Sel Sel' : SelFn} (h : VER_024_select Sel) (h' : VER_024_select Sel')
    {net : SNet} (hn : (net.map fun e => e.1.name).Nodup) (a : AMarking) :
    Sel net a = Sel' net a := by
  have hs := (h net a hn).2.2
  have hs' := (h' net a hn).2.2
  have hnd : ∀ {l : List Nat}, l.Pairwise (fun i j => nameAt net i < nameAt net j) → l.Nodup :=
    fun hl => hl.imp fun hlt heq => by subst heq; exact lt_irrefl _ hlt
  refine List.Perm.eq_of_pairwise (fun i j _ _ hij hji => absurd (lt_trans hij hji) (lt_irrefl _))
    hs hs' ?_
  exact (List.perm_ext_iff_of_nodup (hnd hs) (hnd hs')).mpr
    (VER_024_select_unique h h' hn a)

/-! ### Wrong choices -/

namespace Ver024

/-- The conditions in list order: inputs, then reads, then inhibitors (the order of
`Novel/Stubborn.lean`'s `firstBlocker`). -/
def firstUnsatInputsFirst (a : AMarking) (t : Transition) : Option Cond :=
  ((t.inputs.map fun s => Cond.need s.place s.card.required) ++ t.reads.map (fun p => Cond.need p 1) ++
    t.inhibitors.map Cond.inhib).find? (·.unsat a)

/-- The rules with that order. -/
def reqInputsFirst : ReqFn := fun net a i =>
  match net[i]? with
  | none => []
  | some e =>
    if enabledA a e.1 = true then idxWhere net (dependentT e)
    else
      match firstUnsatInputsFirst a e.1 with
      | some c => idxWhere net fun f => fixes f c
      | none => []

end Ver024

/-- Mutant: the pinned seed choice over closures that read inputs before reads. -/
def ver024_inputsFirst : SelFn := selWith reqInputsFirst

/-- `t` needs a token on place 1 and reads places 0 and 2; `s` takes place 2 to 3; `u0` fills
place 0 and `u1` fills place 1. -/
def ver024Order : SNet :=
  [(ver024T "s" [2], [[3]]),
   ({ name := "t", inputs := [⟨1, .one, none⟩], inhibitors := [], reads := [0, 2], resets := [] },
      [[]]),
   (ver024T "u0" [4], [[0]]), (ver024T "u1" [5], [[1]])]

/-- ✗ **The first unsatisfied condition merges inputs and reads by place** (line 2, S-D2's order).
Example: `t` lacks its read place 0 and its input place 1. In place order the first is place 0,
so S-D2 puts `u0` into a closure holding `t`, and the closure of `u0` holds one enabled
transition: the route expands `u0`. Reading inputs before reads blames place 1 instead and
expands `u1`, a different reduced graph. -/
@[evidence forbids VER_024_select]
theorem VER_024_select_forbids_inputsFirst : ¬ VER_024_select ver024_inputsFirst := by
  intro h
  have := VER_024_select_unique_list h VER_024_select_reference (net := ver024Order) (by decide)
    (mkM [0, 0, 1, 0, 1, 1])
  revert this
  decide

namespace Ver024

/-- The rules with a given order of conditions in S-D2. -/
def reqOrder (order : Transition → List Cond) : ReqFn := fun net a i =>
  match net[i]? with
  | none => []
  | some e =>
    if enabledA a e.1 = true then idxWhere net (dependentT e)
    else
      match (order e.1).find? (·.unsat a) with
      | some c => idxWhere net fun f => fixes f c
      | none => []

/-- Inputs and reads merged in descending place order, then inhibitors. -/
def condsDescending (t : Transition) : List Cond :=
  ((t.inputs.map fun s => Cond.need s.place s.card.required) ++
      t.reads.map fun p => Cond.need p 1).insertionSort (fun x y => y.place ≤ x.place) ++
    (t.inhibitors.insertionSort (· ≤ ·)).map Cond.inhib

/-- Inhibitors first, then inputs and reads merged in place order. -/
def condsInhibitorsFirst (t : Transition) : List Cond :=
  (t.inhibitors.insertionSort (· ≤ ·)).map Cond.inhib ++
    ((t.inputs.map fun s => Cond.need s.place s.card.required) ++
      t.reads.map fun p => Cond.need p 1).insertionSort (fun x y => x.place ≤ y.place)

end Ver024

/-- Mutant: the pinned seed choice over closures that read the merged conditions from the
largest place down. -/
def ver024_descending : SelFn := selWith (reqOrder condsDescending)

/-- ✗ **The merged conditions are read in ascending place order** (line 2, S-D2's order).
Example: on the net of the previous example `t` lacks its places 0 and 1 and has place 2. Read
from the largest place down, the first missing place is 1, so the closure of `u1` holds one
enabled transition and the route would expand `u1` instead of `u0`. -/
@[evidence forbids VER_024_select]
theorem VER_024_select_forbids_descending : ¬ VER_024_select ver024_descending := by
  intro h
  have := VER_024_select_unique_list h VER_024_select_reference (net := ver024Order) (by decide)
    (mkM [0, 0, 1, 0, 1, 1])
  revert this
  decide

/-- Mutant: the pinned seed choice over closures that read inhibitors before inputs and reads. -/
def ver024_inhibitorsFirst : SelFn := selWith (reqOrder condsInhibitorsFirst)

/-- `s` takes place 2 to place 1; `t` needs place 1 and is inhibited by place 0; `d` takes place
0 to place 3. -/
def ver024Inhib : SNet :=
  [(ver024T "s" [2], [[1]]),
   ({ name := "t", inputs := [⟨1, .one, none⟩], inhibitors := [0], reads := [], resets := [] },
      [[]]),
   (ver024T "d" [0], [[3]])]

/-- ✗ **Inputs and reads come before inhibitors** (line 2, S-D2's order). Example: with tokens on
places 0 and 2, `t` lacks its input place 1 and its inhibitor place 0 is marked. Read in the
pinned order, the first unsatisfied condition is place 1, which `s` fills, so the closure of `s`
holds `s` and `t` and one enabled transition: the route expands `s`. Read inhibitors first, it is
place 0, which `d` empties, so the closure of `d` wins instead and the route would expand `d`. -/
@[evidence forbids VER_024_select]
theorem VER_024_select_forbids_inhibitorsFirst : ¬ VER_024_select ver024_inhibitorsFirst := by
  intro h
  have := VER_024_select_unique_list h VER_024_select_reference (net := ver024Inhib) (by decide)
    (mkM [1, 0, 1, 0])
  revert this
  decide

/-- Mutant: the pinned set, listed in net order instead of name order. -/
def ver024_netOrder : SelFn := fun net a =>
  match bestSeed reqT net a with
  | none => []
  | some s => (List.range net.length).filter fun i => enAt net a i && (closureWith reqT net a s).contains i

/-- `b` and `a` compete for the token on place 0; `b` leads on to `c`, which needs place 1. -/
def ver024Compete : SNet :=
  [(ver024T "b" [0], [[1]]), (ver024T "a" [0], [[2]]), (ver024T "c" [1], [[3]])]

/-- ✗ **The route expands the picked transitions in order of name** (line 5). Example: `b` and
`a` compete for one token, so both are expanded at the first class. In net order the route would
fire `b` first and find its successor first; in name order it fires `a` first, so the two builds
find their classes in a different order (`VER_024_select_netOrder_graph`). -/
@[evidence forbids VER_024_select]
theorem VER_024_select_forbids_netOrder : ¬ VER_024_select ver024_netOrder := by
  intro h
  have := (h ver024Compete (mkM [1, 0, 0, 0]) (by decide)).2.2
  revert this
  decide

/-- **The order changes the graph a budget sees.** Example: with a budget of 4 classes, the build
in name order finds the dead class `a` reaches second, the build in net order finds it third. -/
theorem VER_024_select_netOrder_graph :
    (buildV refSel ver024Compete 4 4 [1, 0, 0, 0]).1 =
        [[1, 0, 0, 0], [0, 0, 1, 0], [0, 1, 0, 0], [0, 0, 0, 1]] ∧
      (buildV ver024_netOrder ver024Compete 4 4 [1, 0, 0, 0]).1 =
        [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]] := by
  decide

/-- Mutant: the first enabled seed in net order among those with the fewest enabled members. -/
def ver024_byIndex : SelFn := fun net a =>
  match (enabledIdx net a).argmin (countWith reqT net a) with
  | none => []
  | some s => (List.range net.length).filter fun i => enAt net a i && (closureWith reqT net a s).contains i

/-- Two independent transitions, `b` first in net order, `a` second. -/
def ver024Tie : SNet := [(ver024T "b" [0], [[2]]), (ver024T "a" [1], [[3]])]

/-- ✗ **The smallest name breaks a tie, not the net order** (line 4). Example: `b` and `a` are
independent and each closure holds one enabled transition; the route expands `a`, the smaller
name, although `b` comes first in the net. -/
@[evidence forbids VER_024_select]
theorem VER_024_select_forbids_byIndex : ¬ VER_024_select ver024_byIndex := by
  intro h
  have := VER_024_select_unique_list h VER_024_select_reference (net := ver024Tie) (by decide)
    (mkM [1, 1, 0, 0])
  revert this
  decide

/-- Mutant: the seed whose closure has the most enabled members. -/
def ver024_most : SelFn := fun net a =>
  match (enabledIdx net a).argmax (countWith reqT net a) with
  | none => []
  | some s => (List.range net.length).filter fun i => enAt net a i && (closureWith reqT net a s).contains i

/-- A conflict between `a` and `b` beside an independent `c`. -/
def ver024Mixed : SNet :=
  [(ver024T "a" [0], [[1]]), (ver024T "b" [0], [[2]]), (ver024T "c" [3], [[4]])]

/-- ✗ **The fewest enabled members win** (line 3). Example: the closures of `a` and `b` hold both
of them, the closure of `c` holds `c` alone; the route expands `c` only, where a choice of the
largest closure expands `a` and `b`. -/
@[evidence forbids VER_024_select]
theorem VER_024_select_forbids_most : ¬ VER_024_select ver024_most := by
  intro h
  have := VER_024_select_unique_list h VER_024_select_reference (net := ver024Mixed) (by decide)
    (mkM [1, 0, 0, 1, 0])
  revert this
  decide

/-- ✗ **The whole closure is expanded, not the seed alone** (line 2). Example: `a` and `b`
compete for one token, so S-D1 puts both into one closure and the route expands both; expanding
the seed `a` alone is a different, and unsound, reduced graph (`VER_024_forbids_seedOnly`). -/
@[evidence forbids VER_024_select]
theorem VER_024_select_forbids_seedOnly : ¬ VER_024_select ver024_seedOnly := by
  intro h
  have := VER_024_select_unique_list h VER_024_select_reference (net := ver024Conflict) (by decide)
    (mkM [1, 0, 0])
  revert this
  decide

/-- ✗ **Only enabled transitions are picked** (line 1). Example: `t` waits for a token on place 0;
a selection that lists it as well breaks the line. -/
@[evidence forbids VER_024_select]
theorem VER_024_select_forbids_withDisabled : ¬ VER_024_select ver024_withDisabled := by
  intro h
  have := (h ver024Blocked (mkM [0]) (by decide)).1 0 (by decide)
  revert this
  decide

/-- ✓ **The choice block is not vacuous.** Example: on the net of `VER_024_select_forbids_inputsFirst`
every transition name is distinct, three transitions are enabled, and the reference picks `u0`
alone, the seed whose closure (`u0` and the disabled `t`) holds one enabled transition. On the
net of `VER_024_select_forbids_netOrder` it picks two, `b` (first in the net) and `a`, and lists
`a` first, as the order line asks. -/
@[evidence nonvacuous VER_024_select]
theorem VER_024_select_nonvacuous :
    (ver024Order.map fun e => e.1.name).Nodup ∧
      enabledIdx ver024Order (mkM [0, 0, 1, 0, 1, 1]) = [0, 2, 3] ∧
      closureWith reqT ver024Order (mkM [0, 0, 1, 0, 1, 1]) 2 = [2, 1] ∧
      refSel ver024Order (mkM [0, 0, 1, 0, 1, 1]) = [2] ∧
      (ver024Compete.map fun e => e.1.name).Nodup ∧
      refSel ver024Compete (mkM [1, 0, 0, 0]) = [1, 0] := by
  decide

/-! ## VER-024 (F): when the route reduces, and the cache key -/

namespace Ver024

/-- **The reduction decision**: from the property, whether the option is on, and whether the net
has a drained forward ([IO-014]), whether the route builds the reduced graph. -/
abbrev ReduceFn (K : Type) : Type := VerProp K → Bool → Bool → Bool

/-- **The cache key a query uses**: from the net, the in-flight split, the initial marking, the
property, the option and the drained-forward flag, the key of [VER-017]'s cache. -/
abbrev CacheKeyFn (N M K : Type) : Type :=
  N → List String → M → VerProp K → Bool → Bool → Verifier.Graph.CacheKey N M

end Ver024

requirement VER_024_route
  id "VER-024"
  title "Stubborn-Set Reduction: when it applies, and the cache key"
  kind F
  scope "the enumeration route of VER-017 and its state-space cache, all implementations"
  source verbatim "spec/07-verification.md"
  quote "*While* the enumeration route of [VER-017] runs on a quiescence property (`deadlockFree`, `terminatesAtSink`, `joinedOrDeadLettered` or `quiescentCount`), on a net without a drained forward ([IO-014]), with the reduction enabled, the route *shall* build the reduced graph."
        "*If* the property is not a quiescence property, the net has a drained forward or the reduction is disabled, *then* the route *shall* build the full graph of [VER-017]."
        "Every implementation *shall* turn the reduction on by default."
        "The cache of [VER-017] *shall* key a reduced graph apart from the full graph of the same net and initial marking, so that a safety query, and a quiescence query with the reduction off, never read a reduced entry."
  reading "For every property, option value and drained-forward flag: U builds the reduced graph iff the property is a quiescence property (DeadlockFree, TerminatesAtSink or QuiescentCount), the option is on and the net has no drained forward."
          "For every net, in-flight split, initial marking, property, option value and drained-forward flag, the reduced field of the cache key is the bit U gives."
  assumes "Condition 1 (the enumeration route runs: no ν-join, no environment place, untimed, a positive class budget) is VER-017's applicability; the decision U is read only when the route runs."
          "JoinedOrDeadLettered (NU-055) is not a VerProp of VER-002, so line 1 does not range over it. The runtimes count it as a quiescence property and reduce for it (stubborn_enumeration, smt_verifier.rs:593-602), and the route meets it on a net without ν-joins (smt_verifier.rs:7265-7343 runs it on such nets with the route turned off explicitly). It reads only the classes without successors, so the reduced graph decides it as it decides the three others (VER_024_exact). That the first two quoted sentences hold for it is a corpus test, kind Q."
          "The third quoted sentence (on by default) is configuration, kind N: the constant ver024_defaultOn, pinned below. All four runtimes default to on (smt_verifier.rs:253, SmtVerifier.java:189, smt-verifier.ts:166, Python verify(..., partial_order_reduction=True)); that they default alike is checked by the verdict-parity fixtures. The option names are kind N (Implementation notes)."
          "The cache is VER-017's sequential state machine (Verifier.Graph.cacheQuery): a query reads and writes only the entry of its own key (cacheQuery_frame). With the reduced bit in the key, a safety query and a quiescence query with the reduction off use keys whose bit is false, so they never read or write an entry whose bit is true (VER_024_route_apart, from the statement alone). Line 2 pins only the reduced field: which other fields the key has (the net or its structural fingerprint, the split, the initial marking) and the reuse rules are VER-017's cache block."
          "AC3 (a safety property builds the full graph whatever the setting) and AC4 (with partialOrderReduction(false), VER-017's graph, witness and class count) are line 1 with the property or the option set; that the full graph is VER-017's is VER-017's subject."
  signoff "2026-11-13 60a35bb2a87a4c8b ai"
  statement : ∀ {K N M : Type}, ReduceFn K → CacheKeyFn N M K → Prop :=
    fun U key =>
      (∀ φ opt dr, U φ opt dr = true ↔ quiescenceProp φ = true ∧ opt = true ∧ dr = false) ∧
      (∀ net split m0 φ opt dr, (key net split m0 φ opt dr).reduced = U φ opt dr)

/- The pinned readable form of VER-024's route block. -/
/--
info: def Libpetri.Spec.VER_024_route : {K N M : Type} → ReduceFn K → CacheKeyFn N M K → Prop :=
fun {K N M} U key =>
  (∀ (φ : VerProp K) (opt dr : Bool), U φ opt dr = true ↔ quiescenceProp φ = true ∧ opt = true ∧ dr = false) ∧
    ∀ (net : N) (split : List String) (m0 : M) (φ : VerProp K) (opt dr : Bool),
      (key net split m0 φ opt dr).reduced = U φ opt dr
-/
#guard_msgs in #print VER_024_route

namespace Ver024

/-- The reference decision, as `stubborn_enumeration` (`smt_verifier.rs:593-602`). -/
def refReduce {K : Type} : ReduceFn K := fun φ opt dr => quiescenceProp φ && opt && !dr

/-- The key with the bit a decision gives. -/
def keyWith {N M K : Type} (U : ReduceFn K) : CacheKeyFn N M K := fun net split m0 φ opt dr =>
  { net := net, split := split, m0 := m0, reduced := U φ opt dr }

/-- The reference key. -/
def refKey {N M K : Type} : CacheKeyFn N M K := keyWith refReduce

end Ver024

#spec_witness refReduce
#spec_witness refKey

/-- ✓ **The reference decides and keys as the spec says.** Example: `deadlockFree` with the option
on, on a net without a drained forward, gets the reduced graph and a key with the reduced bit set;
`placeBound` never does. -/
@[evidence holds VER_024_route]
theorem VER_024_route_reference {N M K : Type} :
    VER_024_route (refReduce (K := K)) (refKey (N := N) (M := M)) := by
  refine ⟨fun φ opt dr => ?_, fun _ _ _ _ _ _ => rfl⟩
  simp [refReduce, and_assoc]

/-- **A safety query never touches a reduced entry**, from the statement alone. Example:
`placeBound` on a net whose `deadlockFree` query left a reduced graph in the cache uses a key
whose reduced bit is false, so the query's lookup and store leave the reduced entry as it was. -/
theorem VER_024_route_apart {K N M S : Type} [DecidableEq N] [DecidableEq M] {U : ReduceFn K}
    {key : CacheKeyFn N M K} (h : VER_024_route U key) (c : Verifier.Graph.Cache (Verifier.Graph.CacheKey N M) S)
    (net : N) (split : List String) (m0 : M) {φ φ' : VerProp K} {opt opt' dr dr' : Bool}
    (hoff : U φ opt dr = false) (hred : U φ' opt' dr' = true) (budget : Nat)
    (build : Option (Novel.RouteB.Decide.Out S)) :
    key net split m0 φ opt dr ≠ key net split m0 φ' opt' dr' ∧
      (Verifier.Graph.cacheQuery c (key net split m0 φ opt dr) budget build).2
        (key net split m0 φ' opt' dr') = c (key net split m0 φ' opt' dr') := by
  have hne : key net split m0 φ opt dr ≠ key net split m0 φ' opt' dr' := by
    intro he
    have := congrArg Verifier.Graph.CacheKey.reduced he
    rw [h.2, h.2, hoff, hred] at this
    exact Bool.false_ne_true this
  exact ⟨hne, Verifier.Graph.cacheQuery_frame c (Ne.symm hne) budget build⟩

/-- Mutant: reduce whatever the property. -/
def ver024_reduceAll {K : Type} : ReduceFn K := fun _ opt dr => opt && !dr

/-- ✗ **A safety property keeps the full graph** (line 1, AC3). Example: `PlaceBound(p, 2)` may be
violated at a marking where transitions are still enabled; reducing for it would drop that
marking. -/
@[evidence forbids VER_024_route]
theorem VER_024_route_forbids_reduceAll : ¬ VER_024_route (ver024_reduceAll (K := Nat))
    (keyWith (N := Nat) (M := Nat) ver024_reduceAll) := by
  intro h
  have := ((h.1 (.placeBound 0 2) true false).mp rfl).1
  exact absurd this (by decide)

/-- Mutant: reduce whatever the drained forwards. -/
def ver024_ignoreDrained {K : Type} : ReduceFn K := fun φ opt _ => quiescenceProp φ && opt

/-- ✗ **A drained forward keeps the full graph** (line 1, condition 3). Example: `deadlockFree` on
a net with a drained forward, whose marking-dependent deposit is outside the model the reduction
is proven on. -/
@[evidence forbids VER_024_route]
theorem VER_024_route_forbids_ignoreDrained : ¬ VER_024_route (ver024_ignoreDrained (K := Nat))
    (keyWith (N := Nat) (M := Nat) ver024_ignoreDrained) := by
  intro h
  have := ((h.1 (.deadlockFree [] []) true true).mp rfl).2.2
  exact absurd this (by decide)

/-- Mutant: reduce whatever the option. -/
def ver024_ignoreOption {K : Type} : ReduceFn K := fun φ _ dr => quiescenceProp φ && !dr

/-- ✗ **`partialOrderReduction(false)` turns the reduction off** (line 1, AC4). Example:
`deadlockFree` with the option off builds VER-017's full graph. -/
@[evidence forbids VER_024_route]
theorem VER_024_route_forbids_ignoreOption : ¬ VER_024_route (ver024_ignoreOption (K := Nat))
    (keyWith (N := Nat) (M := Nat) ver024_ignoreOption) := by
  intro h
  have := ((h.1 (.deadlockFree [] []) false false).mp rfl).2.1
  exact absurd this (by decide)

/-- Mutant: a key without the reduced bit. -/
def ver024_keyNoBit {N M K : Type} : CacheKeyFn N M K := fun net split m0 _ _ _ =>
  { net := net, split := split, m0 := m0, reduced := false }

/-- ✗ **The key carries the reduced bit** (line 2). Example: without it, `deadlockFree` stores its
reduced graph under the same key a `placeBound` query of the same net and marking reads, and the
safety query would answer from a graph that dropped markings. -/
@[evidence forbids VER_024_route]
theorem VER_024_route_forbids_keyNoBit :
    ¬ VER_024_route (refReduce (K := Nat)) (ver024_keyNoBit (N := Nat) (M := Nat)) := by
  intro h
  have := h.2 0 [] 0 (.deadlockFree [] []) true false
  exact absurd this (by decide)

/-- ✓ **The route block is not vacuous.** Example: `deadlockFree` with the option on and no drained
forward is reduced and keyed with the bit set, while `placeBound` on the same net and marking is
not, so the two keys differ. -/
@[evidence nonvacuous VER_024_route]
theorem VER_024_route_nonvacuous :
    refReduce (K := Nat) (.deadlockFree [] []) true false = true ∧
      refReduce (K := Nat) (.placeBound 0 2) true false = false ∧
      refKey (N := Nat) (M := Nat) (K := Nat) 0 [] 0 (.deadlockFree [] []) true false ≠
        refKey 0 [] 0 (.placeBound 0 2) true false := by
  decide

/-! ## The three blocks together -/

/-! ### The default -/

namespace Ver024

/-- The reduction is on by default (the third quoted sentence of `VER_024_route`, kind N). -/
def ver024_defaultOn : Bool := true

end Ver024

#guard ver024_defaultOn == true

/-- ✓ **The three VER-024 blocks hold together** of one selection, one decision and one key: the
reference selection keeps every dead marking and is the pinned choice, and the reference decision
and key are the spec's. -/
@[evidence consistent VER_024 VER_024_select VER_024_route]
theorem VER_024_joint :
    ∃ (Sel : SelFn) (U : ReduceFn Nat) (key : CacheKeyFn Nat Nat Nat),
      VER_024 Sel ∧ VER_024_select Sel ∧ VER_024_route U key :=
  ⟨refSel, refReduce, refKey, VER_024_reference, VER_024_select_reference, VER_024_route_reference⟩

end Libpetri.Spec
