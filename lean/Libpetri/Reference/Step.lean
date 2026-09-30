import Libpetri.Reference.Marking
import Libpetri.Reference.Semantics

/-!
# The executable successor function

`succ net m` lists, for every transition enabled at `m` and every way its firing can end, the
transition's name and the successor marking. It evaluates the spec's own definitions
(`enabledNA`, `nconsumed`, `fireNC`) on the counts `get m`; what it adds is representation:
deposits as `(place, count)` bags (`outcomesB`, equal to the spec's `outcomes` count for count:
`outcomesB_counts`), and canonical markings: `fire` writes the spec's successor count into every
place the firing touches (inputs, resets, deposit), and every other place keeps its count.

**`mem_succ_iff`** (headline (a)): on canonical markings, `(l, m') ∈ succ net m` iff `m'` is
reached from `m` in one step of `LStep` labelled `l`. Together with `succ_canon` it says the
successor list is exactly the one-step image, as canonical markings.
-/

namespace Libpetri.Reference

open Libpetri Libpetri.Novel.Seam

variable {K : Type} [LinearOrder K]

/-- Every deposit a firing can end with ([IO-013]–[IO-016]), as the spec writes it: lists of
places with repetition. -/
def outcomes (consumed : K → Nat) : Option (Out K) → List (List K)
  | none => [[]]
  | some o => o.branches ++
      (match o.findTimeout with
       | none => []
       | some c => c.timeoutDeposits consumed)

/-! ### The same outcomes as `(place, count)` bags

A forward of a drained batch deposits as many tokens as the firing consumed, so a deposit list can
be as long as a place's count. The executable writes each deposit as a bag of `(place, count)`
pairs instead, in the same order; `outcomesB_counts` proves the two lists of outcomes have the
same token counts, outcome by outcome. -/

/-- A deposit as `(place, count)` pairs. -/
abbrev Bag (K : Type) := List (K × Nat)

/-- Tokens a bag deposits in `p`. -/
def bagCount : Bag K → K → Nat
  | [], _ => 0
  | (k, n) :: rest, p => (if k = p then n else 0) + bagCount rest p

def crossB (xs ys : List (Bag K)) : List (Bag K) := xs.flatMap fun x => ys.map fun y => x ++ y

def branchesB : Out K → List (Bag K)
  | .place p => [[(p, 1)]]
  | .forward _ dst => [[(dst, 1)]]
  | .and l r => crossB (branchesB l) (branchesB r)
  | .xor l r => branchesB l ++ branchesB r
  | .timeout c => branchesB c

def timeoutBags (consumed : K → Nat) : Out K → List (Bag K)
  | .place p => [[(p, 1)]]
  | .forward src dst => [[(dst, consumed src)]]
  | .and l r => crossB (timeoutBags consumed l) (timeoutBags consumed r)
  | .xor l r => timeoutBags consumed l ++ timeoutBags consumed r
  | .timeout c => timeoutBags consumed c

/-- `outcomes`, as bags. -/
def outcomesB (consumed : K → Nat) : Option (Out K) → List (Bag K)
  | none => [[]]
  | some o => branchesB o ++
      (match o.findTimeout with
       | none => []
       | some c => timeoutBags consumed c)

/-- The places a firing of `t` with deposit `b` can change. -/
def touched (t : NTransition K) (b : Bag K) : List K :=
  t.inputs.map NInSpec.place ++ t.resets ++ b.map Prod.fst

/-- The successor marking: each touched place gets the spec's count `fireNC`. -/
def fire (m : Marking K) (t : NTransition K) (b : Bag K) : Marking K :=
  (touched t b).foldl (fun acc p => set acc p (fireNC (get m) t (bagCount b) p)) m

/-- **The executable successor function**: every enabled transition, every outcome. -/
def succ (net : Net K) (m : Marking K) : List (String × Marking K) :=
  net.transitions.flatMap fun t =>
    if enabledNA (get m) t.core then
      (outcomesB (nconsumed (get m) t.core) t.out).map fun b => (t.core.name, fire m t.core b)
    else []

/-! ## Correctness -/

omit [LinearOrder K] in
theorem mem_outcomes {c : K → Nat} {o : Option (Out K)} {d : List K} :
    d ∈ outcomes c o ↔ ∃ ch, deposit c o ch = some d := by
  cases o with
  | none =>
    simp only [outcomes, List.mem_singleton]
    constructor
    · rintro rfl; exact ⟨.action 0, rfl⟩
    · rintro ⟨ch, h⟩
      match ch, h with
      | .action 0, h => simpa [deposit] using h.symm
      | .action (_ + 1), h => simp [deposit] at h
      | .timedOut _, h => simp [deposit] at h
  | some o =>
    simp only [outcomes, List.mem_append]
    constructor
    · rintro (h | h)
      · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
        exact ⟨.action i, hi⟩
      · cases hc : o.findTimeout with
        | none => rw [hc] at h; exact absurd h List.not_mem_nil
        | some c' =>
          rw [hc] at h
          obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp h
          exact ⟨.timedOut j, by simp [deposit, hc, hj]⟩
    · rintro ⟨ch, h⟩
      cases ch with
      | action i => exact Or.inl (List.mem_of_getElem? h)
      | timedOut j =>
        right
        simp only [deposit] at h
        cases hc : o.findTimeout with
        | none => rw [hc] at h; simp at h
        | some c' =>
          rw [hc] at h
          simp only [Option.bind_some] at h
          exact List.mem_of_getElem? h

theorem bagCount_append (x y : Bag K) : bagCount (x ++ y) = bagCount x + bagCount y := by
  funext p
  induction x with
  | nil => simp [bagCount]
  | cons e x ih =>
    obtain ⟨k, n⟩ := e
    simp only [List.cons_append, bagCount, Pi.add_apply] at ih ⊢
    rw [ih]; omega

omit [LinearOrder K] in
theorem depProd_append [DecidableEq K] (x y : List K) :
    depProd (x ++ y) = depProd x + depProd y := by
  funext p
  simp [depProd, List.count_append]

/-- Crossing preserves "same counts, outcome by outcome". -/
theorem crossB_counts {xs ys : List (Bag K)} {xs' ys' : List (List K)}
    (hx : xs.map bagCount = xs'.map depProd) (hy : ys.map bagCount = ys'.map depProd) :
    (crossB xs ys).map bagCount = (cross xs' ys').map depProd := by
  induction xs generalizing xs' with
  | nil =>
    cases xs' with
    | nil => rfl
    | cons _ _ => simp at hx
  | cons x xs ih =>
    cases xs' with
    | nil => simp at hx
    | cons x' xs' =>
      simp only [List.map_cons, List.cons.injEq] at hx
      obtain ⟨hh, ht⟩ := hx
      simp only [crossB, cross, List.flatMap_cons, List.map_append, List.map_map] at ih ⊢
      rw [ih ht]
      congr 1
      have e1 : (bagCount ∘ fun y => x ++ y) = (fun f => bagCount x + f) ∘ bagCount := by
        funext y; simp [bagCount_append]
      have e2 : (depProd ∘ fun y => x' ++ y) = (fun f => depProd x' + f) ∘ depProd := by
        funext y; simp [depProd_append]
      rw [e1, e2, ← List.map_map, ← List.map_map, hy, hh]

theorem branchesB_counts : ∀ o : Out K, (branchesB o).map bagCount = o.branches.map depProd
  | .place p => by
    simp only [branchesB, Out.branches, List.map_cons, List.map_nil, List.cons.injEq, and_true]
    funext q; simp [bagCount, depProd, List.count_singleton]
  | .forward _ dst => by
    simp only [branchesB, Out.branches, List.map_cons, List.map_nil, List.cons.injEq, and_true]
    funext q; simp [bagCount, depProd, List.count_singleton]
  | .and l r => crossB_counts (branchesB_counts l) (branchesB_counts r)
  | .xor l r => by
    simp [branchesB, Out.branches, branchesB_counts l, branchesB_counts r]
  | .timeout c => branchesB_counts c

theorem timeoutBags_counts (c : K → Nat) :
    ∀ o : Out K, (timeoutBags c o).map bagCount = (o.timeoutDeposits c).map depProd
  | .place p => by
    simp only [timeoutBags, Out.timeoutDeposits, List.map_cons, List.map_nil, List.cons.injEq,
      and_true]
    funext q; simp [bagCount, depProd, List.count_singleton]
  | .forward src dst => by
    simp only [timeoutBags, Out.timeoutDeposits, List.map_cons, List.map_nil, List.cons.injEq,
      and_true]
    funext q; simp [bagCount, depProd, List.count_replicate]
  | .and l r => crossB_counts (timeoutBags_counts c l) (timeoutBags_counts c r)
  | .xor l r => by
    simp [timeoutBags, Out.timeoutDeposits, timeoutBags_counts c l, timeoutBags_counts c r]
  | .timeout o => timeoutBags_counts c o

/-- **The executable outcomes are the spec's**, outcome by outcome, as token counts. -/
theorem outcomesB_counts (c : K → Nat) (o : Option (Out K)) :
    (outcomesB c o).map bagCount = (outcomes c o).map depProd := by
  cases o with
  | none =>
    simp only [outcomesB, outcomes, List.map_cons, List.map_nil, List.cons.injEq, and_true]
    funext q; simp [bagCount, depProd]
  | some o =>
    simp only [outcomesB, outcomes, List.map_append, branchesB_counts]
    congr 1
    cases o.findTimeout with
    | none => rfl
    | some c' => exact timeoutBags_counts c c'

theorem bagCount_outcome {c : K → Nat} {o : Option (Out K)} {b : Bag K} (hb : b ∈ outcomesB c o) :
    ∃ d ∈ outcomes c o, depProd d = bagCount b := by
  have : bagCount b ∈ (outcomes c o).map depProd := by
    rw [← outcomesB_counts]; exact List.mem_map_of_mem hb
  exact List.mem_map.mp this

theorem outcome_bagCount {c : K → Nat} {o : Option (Out K)} {d : List K} (hd : d ∈ outcomes c o) :
    ∃ b ∈ outcomesB c o, bagCount b = depProd d := by
  have : depProd d ∈ (outcomesB c o).map bagCount := by
    rw [outcomesB_counts]; exact List.mem_map_of_mem hd
  exact List.mem_map.mp this

theorem bagCount_eq_zero {b : Bag K} {q : K} (h : q ∉ b.map Prod.fst) : bagCount b q = 0 := by
  induction b with
  | nil => rfl
  | cons e b ih =>
    obtain ⟨k, n⟩ := e
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp [bagCount, Ne.symm h.1, ih h.2]

/-- A place the firing does not touch keeps its count. -/
theorem fireNC_untouched {m : K → Nat} {t : NTransition K} {b : Bag K} {q : K}
    (hq : q ∉ touched t b) : fireNC m t (bagCount b) q = m q := by
  simp only [touched, List.mem_append, not_or] at hq
  obtain ⟨⟨hin, hres⟩, hd⟩ := hq
  have hspec : nspecAt t q = none := by
    unfold nspecAt
    rw [List.find?_eq_none]
    intro s hs he
    have : s.place = q := by simpa using he
    exact hin (List.mem_map.mpr ⟨s, hs, this⟩)
  simp [fireNC, hres, nconsumed, hspec, bagCount_eq_zero hd]

/-- **`fire` computes the spec's successor counts**, canonically. -/
theorem fire_spec {m : Marking K} (hc : Canon m) (t : NTransition K) (b : Bag K) :
    Canon (fire m t b) ∧ ∀ q, get (fire m t b) q = fireNC (get m) t (bagCount b) q := by
  obtain ⟨hc', hg⟩ := foldl_set (touched t b) (fireNC (get m) t (bagCount b)) hc
  refine ⟨hc', fun q => ?_⟩
  unfold fire
  rw [hg q]
  split
  · rfl
  · rename_i hq
    exact (fireNC_untouched hq).symm

/-- Every successor is canonical and one labelled step away. -/
theorem mem_succ {net : Net K} {m : Marking K} (hc : Canon m) {l : String} {m' : Marking K}
    (h : (l, m') ∈ succ net m) : Canon m' ∧ LStep net l (get m) (get m') := by
  obtain ⟨t, ht, hmem⟩ := List.mem_flatMap.mp h
  split at hmem
  · rename_i hen
    obtain ⟨b, hb, he⟩ := List.mem_map.mp hmem
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨hc', hg⟩ := fire_spec hc t.core b
    obtain ⟨d, hd, hdb⟩ := bagCount_outcome hb
    exact ⟨hc', t, ht, rfl, d, hen, mem_outcomes.mp hd, by rw [hdb]; exact funext hg⟩
  · exact absurd hmem List.not_mem_nil

/-- Every labelled step has a successor in the list. -/
theorem succ_complete {net : Net K} {m : Marking K} (hc : Canon m) {l : String} {f : K → Nat}
    (h : LStep net l (get m) f) : ∃ m', (l, m') ∈ succ net m ∧ get m' = f := by
  obtain ⟨t, ht, rfl, d, hen, hdep, rfl⟩ := h
  obtain ⟨b, hb, hbd⟩ := outcome_bagCount (mem_outcomes.mpr hdep)
  refine ⟨fire m t.core b, List.mem_flatMap.mpr ⟨t, ht, ?_⟩, ?_⟩
  · rw [if_pos hen]
    exact List.mem_map.mpr ⟨b, hb, rfl⟩
  · rw [← hbd]; exact funext (fire_spec hc t.core b).2

/-- **Headline (a).** On canonical markings, the executable successor list is exactly the
one-step relation of the spec semantics, label by label. -/
theorem mem_succ_iff {net : Net K} {m m' : Marking K} (hc : Canon m) (hc' : Canon m')
    (l : String) : (l, m') ∈ succ net m ↔ LStep net l (get m) (get m') := by
  refine ⟨fun h => (mem_succ hc h).2, fun h => ?_⟩
  obtain ⟨m'', hm, hg⟩ := succ_complete hc h
  have := ext (mem_succ hc hm).1 hc' (fun q => congrFun hg q)
  exact this ▸ hm

/-- The successors of a canonical marking are canonical. -/
theorem succ_canon {net : Net K} {m : Marking K} (hc : Canon m) :
    ∀ e ∈ succ net m, Canon e.2 := fun e he => (mem_succ hc (l := e.1) he).1

/-- A marking has no successor iff it is quiescent. -/
theorem succ_eq_nil_iff {net : Net K} {m : Marking K} (hc : Canon m) :
    succ net m = [] ↔ Quiescent net (get m) := by
  rw [quiescent_iff_no_step]
  constructor
  · rintro h f ⟨l, hs⟩
    obtain ⟨m', hm, _⟩ := succ_complete hc hs
    rw [h] at hm
    exact List.not_mem_nil hm
  · intro h
    cases hs : succ net m with
    | nil => rfl
    | cons e es =>
      have := mem_succ hc (l := e.1) (m' := e.2) (by rw [hs]; exact List.mem_cons_self)
      exact absurd ⟨e.1, this.2⟩ (h _)

end Libpetri.Reference
