import Libpetri.Novel.Commoner
import Libpetri.Novel.ReapingVsUntimed
import Libpetri.Novel.ReapAware

/-!
# The siphon search and trap contraction behind the structural `Proven` ([VER-020])

`Commoner.lean` proves Commoner's theorem and leaves the loops out of scope. This module models
the loops of `rust/libpetri-verification/src/structural_check.rs` and proves they decide what
the theorem needs:

* `structural_check` (`structural_check.rs:36`) as `structuralCheck`;
* `find_minimal_siphons` (`:66`) as `findMinimalSiphons`, with the start-place loop `searchZ`
  and the minimality filter `minimalOf`;
* `grow_siphon` (`:96`) as `growZ`;
* `find_maximal_trap_in` (`:149`) as `maximalTrapIn`, with one `while changed` round as `pass`.

## The Rust as data

`FlatNet` (`net_flattener.rs`) is modelled by `Soundness.FlatNet`, a list of flat transitions
in `flat.transitions` order, and `place_count` by `n`. A place set is `Vec<bool>` of length
`n`, here `PSet := PlaceId → Bool` of which only indices below `n` are ever read. A siphon
handed to `find_maximal_trap_in` is a `Vec<usize>` of indices, here `List PlaceId`.

## Premises about the Rust (stated, not proved)

* **P1 `pre`.** `ft.pre[p] > 0` iff `Consumes ft.1 p` (as `consumesB`). `flatten` writes
  `pre[p] = Σ required_count` over the input arcs on `p` (`flatten_with_reapable`,
  `net_flattener.rs:120-127`), so the
  sum is positive iff one arc requires a token. No `InputsDistinctPlaces` is needed.
* **P2 `post`.** `ft.post[p] > 0` iff `ft.2.contains p` (as `outputsB`): every place of an
  outcome deposits at least one token (`branch_outcomes::outcomes`, `ForwardDeposit.lean`).
* **P3 indices.** Every `pre`/`post` vector has length `n`: loops over `pre.iter().enumerate()`
  are loops over `List.range n`.
* **P4 marking.** `initial.count(&flat.places[p])` is `a0 p` for `p < n`, the marking the
  `Commoner`/`Seam` semantics starts from (`Seam.SeedsFrom`, `encodeM0`).
* **P5 stop.** `crate::total_budget::cut()` is an arbitrary oracle. `grow_siphon` polls it once
  per node after the node counter is incremented, and the counter is strictly increasing, so
  any run of the Rust is a run of the model for some `cut : Nat → Bool` indexed by that
  counter. Every theorem below is stated for all `cut`.
* **P6 call site.** `verify_net` (`smt_verifier.rs`, the `structural_candidate` conjunction;
  `verify_net` is pinned to this module) calls `structural_check` only for `DeadlockFree`, with
  no ν-matching (`!has_match`), **no flat transition marked reapable**
  (`!flat.transitions.iter().any(|t| t.reapable)`: no `Deadline` / `Window` transition, or
  `assume_no_reaping`), `commoner_applies`, no sink or conditional-sink places and no
  environment places, and returns `Proven` exactly on `NoPotentialDeadlock`. The theorems take
  `commoner_applies` as `Ordinary`, the reapable gate as `∀ ft ∈ net, reapable ft.1 = false`
  (`structural_proven_sound_timed`), and read the answer as the `DeadlockFree` verdict with no
  sinks (`structural_proven_no_dlf_violation`); the other conjuncts are assumed. The
  nonempty-net guard is *not* among them: it sits in `structural_check`, which is pinned, and
  the model derives it from the answer (`structuralCheck_ne_nil`).

## Fuel

The Rust recursion and the `while changed` loop have no fuel. The model's `growZ` and
`contractZ` take fuel and an arbitrary fallback `z` for fuel exhaustion; `growZ_fuel_irrelevant`
and `contractZ_fuel_irrelevant` show the fallback is never returned at the fuel the model uses
(`n` for the search, one more than the siphon's length for the contraction), so the model
computes what the Rust computes. The headline theorems are proved for every `z`.

## Results

* `findMinimalSiphons_complete`: when the search returns (neither the node budget nor the stop
  hit), every nonempty siphon below `n` contains a returned siphon.
* `findMinimalSiphons_sound`: every returned set is a nonempty siphon below `n` and minimal:
  a nonempty siphon inside it is all of it. With completeness, the result is exactly the set of
  minimal siphons.
* `maximalTrapIn_spec`: the contraction returns a trap inside the siphon that contains every
  trap inside the siphon.
* `structural_check_sound`: `noPotentialDeadlock` implies `Commoner.CommonerCond`.
* `structuralCheck_ne_nil`: `noPotentialDeadlock` implies the flat net has a transition, by the
  guard `flat.transitions.is_empty()` in `structural_check`. `structuralCheck_eq_unguarded`: on
  any other net the guard changes nothing.
* `structural_proven_sound`: with `commoner_applies` (`Ordinary`) and the dense index
  (`InputsBelow`), the early `Proven` of `verify_net` is sound **for the untimed net**: no
  `ReachA`-reachable marking is dead. `structural_proven_no_dlf_violation` restates it as the
  `DeadlockFree` property the verifier decides (`ReapingVsUntimed.dlfBad`, no sinks). Both rest
  on P6.
* `structural_proven_is_untimed_only`: the check's answer is about the untimed net, as [VER-004]
  AC3 is for quiescence properties (`ReapingVsUntimed.reaping_refutes_ver004_ac3`, R16). The
  self-loop `t: a → a` with `window(3, 5)` from `{a:1}` gets `noPotentialDeadlock`, and a timed
  run that wakes past the deadline reaps `t` and stops `Quiescent` with the token stranded on
  `a`. The Rust used to return `Proven { method: "structural" }` for it; the reapable gate of P6
  now keeps it off the structural route (`reapGate_refuses_witness`), and the reap-aware
  encoders decide it.
* **`structural_proven_sound_timed`**: behind the reapable gate the structural `Proven` holds for
  every timed run of either backend (`ReapAware`'s executor model): with no reapable row a
  rest is a dead marking (`ReapAware.reap_quiescent_iff_quiescent`), and no reachable marking
  is dead, so no run rests at all.
* Retrodiction `empty_net_structural_proven_dead`: before the guard, a net with no transitions
  and one marked place got `noPotentialDeadlock` while its initial marking is dead and strands a
  token, so `verify_net` returned an unsound `Proven` (with the [VER-017] enumeration off,
  `enumeration_max_classes(0)`). The same net shows `Commoner.commoner` needs `net ≠ []`. The
  last conjunct is the fix: the guarded check answers `inconclusive`.
* Retrodictions of f52c482: `pre_fix_padding_proves_dead_net` (the pre-fix Rust search added
  every input of a producer and missed the empty minimal siphon `{a, b}`) and
  `pre_fix_unmarked_trap_proves_dead_net` (the pre-fix Rust accepted a nonempty but unmarked
  trap). The last conjunct of each is the fix: the shipped check answers `potentialDeadlock`.
-/

namespace Libpetri.Novel.SiphonSearch

open Libpetri Libpetri.Novel.Commoner

/-! ## Place sets as `Vec<bool>` -/

/-- `Vec<bool>` of length `n`: only indices below `n` are read. -/
abbrev PSet := PlaceId → Bool

/-- The empty set, `vec![false; n]`. -/
def emptyS : PSet := fun _ => false

/-- `siphon[start_pid] = true` on `vec![false; n]`. -/
def single (p : PlaceId) : PSet := fun q => q == p

/-- `next[pid] = true` on a clone. -/
def ins (S : PSet) (p : PlaceId) : PSet := fun q => q == p || S q

/-- `trap[pid] = false`. -/
def remove (T : PSet) (p : PlaceId) : PSet := fun q => q != p && T q

/-- `is_subset(a, b)` over the `n` entries. -/
def subsetB (n : Nat) (a b : PSet) : Bool := (List.range n).all fun p => !a p || b p

/-- `(0..n).filter(|&p| s[p]).collect()`. -/
def toList (n : Nat) (S : PSet) : List PlaceId := (List.range n).filter S

/-- `for &pid in siphon { trap[pid] = true }` on `vec![false; n]`. -/
def ofList (l : List PlaceId) : PSet := fun q => l.contains q

/-- The number of members below `n` (proof device only). -/
def card (n : Nat) (S : PSet) : Nat := (List.range n).countP S

/-! ## The flat transition's vectors (premises P1, P2) -/

/-- `ft.pre[p] > 0`. -/
def consumesB (ft : FlatTransition) (p : PlaceId) : Bool :=
  ft.1.inputs.any fun s => s.place == p && decide (0 < s.card.required)

/-- `ft.post[p] > 0`. -/
def outputsB (ft : FlatTransition) (p : PlaceId) : Bool := ft.2.contains p

/-- `outputs_to_siphon` (`structural_check.rs:113-117`). -/
def outputsInto (n : Nat) (S : PSet) (ft : FlatTransition) : Bool :=
  (List.range n).any fun p => outputsB ft p && S p

/-- `has_input_in_siphon` (`structural_check.rs:118-122`). -/
def consumesFrom (n : Nat) (S : PSet) (ft : FlatTransition) : Bool :=
  (List.range n).any fun p => consumesB ft p && S p

/-- The predicate of the `find` at `structural_check.rs:112`. -/
def violates (n : Nat) (S : PSet) (ft : FlatTransition) : Bool :=
  outputsInto n S ft && !consumesFrom n S ft

/-- `for (pid, &count) in ft.pre.iter().enumerate() { if count > 0 { .. } }`. -/
def inputsOf (n : Nat) (ft : FlatTransition) : List PlaceId := (List.range n).filter (consumesB ft)

/-! ## `grow_siphon` and `find_minimal_siphons` -/

/-- The mutable state `(found, nodes)`. -/
abbrev St := List PSet × Nat

/-- A loop whose body returns `false` (here `none`) to abort: `if !f(..) { return false; }`. -/
def seqM {α : Type} (g : α → St → Option St) : List α → St → Option St
  | [], st => some st
  | x :: xs, st =>
    match g x st with
    | none => none
    | some st' => seqM g xs st'

/-- `grow_siphon` (`structural_check.rs:96`), with fuel `f` and fuel fallback `z`. `none` is
the Rust's `false`: the node budget was exceeded or the stop fired. -/
def growZ (net : FlatNet) (n budget : Nat) (cut : Nat → Bool) (z : Option St) :
    Nat → PSet → St → Option St
  | 0, _, _ => z
  | f + 1, S, st =>
    if budget < st.2 + 1 || cut (st.2 + 1) then none
    else if st.1.any (fun F => subsetB n F S) then some (st.1, st.2 + 1)
    else
      match net.find? (violates n S) with
      | none => some (st.1 ++ [S], st.2 + 1)
      | some ft =>
        seqM (fun p => growZ net n budget cut z f (ins S p)) (inputsOf n ft) (st.1, st.2 + 1)

/-- The start-place loop of `find_minimal_siphons` (`structural_check.rs:69-75`), at fuel `n`. -/
def searchZ (net : FlatNet) (n budget : Nat) (cut : Nat → Bool) (z : Option St) : Option St :=
  seqM (fun p => growZ net n budget cut z n (single p)) (List.range n) ([], 0)

/-- The minimality filter of `find_minimal_siphons` (`structural_check.rs:78-88`): keep entry
`i` unless another *index* `j ≠ i` holds a subset of it. -/
def minimalOf (n : Nat) (found : List PSet) : List PSet :=
  (List.range found.length).filterMap fun i =>
    if (List.range found.length).any
        (fun j => j != i && subsetB n (found[j]?.getD emptyS) (found[i]?.getD emptyS))
    then none else some (found[i]?.getD emptyS)

/-- `find_minimal_siphons` (`structural_check.rs:66`). -/
def findMinimalSiphons (net : FlatNet) (n budget : Nat) (cut : Nat → Bool) :
    Option (List (List PlaceId)) :=
  (searchZ net n budget cut none).map fun st => (minimalOf n st.1).map (toList n)

/-! ## `find_maximal_trap_in` -/

/-- The inner `for ft in &flat.transitions` loop (`structural_check.rs:166-180`): every
transition consuming from `pid` produces into the current trap. -/
def okAt (net : FlatNet) (n : Nat) (T : PSet) (pid : PlaceId) : Bool :=
  net.all fun ft => !consumesB ft pid || (List.range n).any fun p => outputsB ft p && T p

/-- One iteration of `for &pid in siphon` (`structural_check.rs:159-186`), updating in place. -/
def passStep (net : FlatNet) (n : Nat) (st : PSet × Bool) (pid : PlaceId) : PSet × Bool :=
  if !st.1 pid then st
  else if okAt net n st.1 pid then st
  else (remove st.1 pid, true)

/-- One round of `while changed` (`changed = false; for &pid in siphon { .. }`). -/
def pass (net : FlatNet) (n : Nat) (sip : List PlaceId) (T : PSet) : PSet × Bool :=
  sip.foldl (passStep net n) (T, false)

/-- The `while changed` loop, with fuel `f` and fallback `z`. -/
def contractZ (net : FlatNet) (n : Nat) (sip : List PlaceId) (z : PSet) : Nat → PSet → PSet
  | 0, _ => z
  | f + 1, T =>
    if (pass net n sip T).2 then contractZ net n sip z f (pass net n sip T).1
    else (pass net n sip T).1

/-- `find_maximal_trap_in` (`structural_check.rs:149`). -/
def maximalTrapIn (net : FlatNet) (n : Nat) (sip : List PlaceId) : List PlaceId :=
  toList n (contractZ net n sip emptyS (sip.length + 1) (ofList sip))

/-! ## `structural_check` -/

/-- `StructuralCheckResult` (`structural_check.rs:6`). -/
inductive Verdict where
  | noPotentialDeadlock
  | potentialDeadlock
  | inconclusive
  deriving DecidableEq, Repr

/-- `SIPHON_SEARCH_BUDGET` (`structural_check.rs:19`). -/
def siphonSearchBudget : Nat := 10000

/-- The siphon/trap verdict once the cut-offs are passed: `Inconclusive` when the search was cut,
else `NoPotentialDeadlock` iff every returned siphon's maximal trap holds a token
(`structural_check.rs:41-55`). -/
def siphonVerdict (net : FlatNet) (n budget : Nat) (cut : Nat → Bool) (a0 : AMarking) :
    Verdict :=
  match findMinimalSiphons net n budget cut with
  | none => .inconclusive
  | some sips =>
    if sips.all (fun sip => (maximalTrapIn net n sip).any fun p => decide (0 < a0 p))
    then .noPotentialDeadlock else .potentialDeadlock

/-- `structural_check` (`structural_check.rs:36`) with node budget `budget` (the Rust passes
`siphonSearchBudget`) and stop oracle `cut` (P5). The guard
`flat.place_count > 50 || flat.transitions.is_empty()` answers `Inconclusive`; the second
disjunct is the fix for `empty_net_structural_proven_dead`. -/
def structuralCheck (net : FlatNet) (n budget : Nat) (cut : Nat → Bool) (a0 : AMarking) :
    Verdict :=
  if 50 < n || net.isEmpty then .inconclusive else siphonVerdict net n budget cut a0

/-- The check before the empty-net guard: only the 50-place cut-off. -/
def structuralCheckUnguarded (net : FlatNet) (n budget : Nat) (cut : Nat → Bool)
    (a0 : AMarking) : Verdict :=
  if 50 < n then .inconclusive else siphonVerdict net n budget cut a0

/-! ## Basic lemmas -/

theorem consumesB_iff {ft : FlatTransition} {p : PlaceId} :
    consumesB ft p = true ↔ Consumes ft.1 p := by
  unfold consumesB Consumes
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]

theorem subsetB_iff {n : Nat} {a b : PSet} :
    subsetB n a b = true ↔ ∀ p < n, a p = true → b p = true := by
  unfold subsetB
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true']
  refine forall_congr' fun p => imp_congr_right fun _ => ?_
  cases a p <;> simp

theorem subsetB_refl (n : Nat) (a : PSet) : subsetB n a a = true :=
  subsetB_iff.mpr fun _ _ h => h

theorem subsetB_trans {n : Nat} {a b c : PSet} (h1 : subsetB n a b = true)
    (h2 : subsetB n b c = true) : subsetB n a c = true :=
  subsetB_iff.mpr fun p hp ha => subsetB_iff.mp h2 p hp (subsetB_iff.mp h1 p hp ha)

theorem mem_toList {n : Nat} {S : PSet} {p : PlaceId} : p ∈ toList n S ↔ p < n ∧ S p = true := by
  simp [toList]

theorem countP_lt {α : Type} {l : List α} {a b : α → Bool}
    (h : ∀ x ∈ l, a x = true → b x = true) (hx : ∃ x ∈ l, b x = true ∧ a x = false) :
    l.countP a < l.countP b := by
  induction l with
  | nil => obtain ⟨x, hx, _⟩ := hx; cases hx
  | cons y ys ih =>
    simp only [List.countP_cons]
    have hys : ∀ x ∈ ys, a x = true → b x = true := fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hmono := List.countP_mono_left hys
    obtain ⟨x, hxm, hbx, hax⟩ := hx
    rcases List.mem_cons.mp hxm with rfl | hxs
    · rw [hax, hbx]; simp; omega
    · have := ih hys ⟨x, hxs, hbx, hax⟩
      have hy := h y List.mem_cons_self
      cases hay : a y <;> cases hby : b y <;> simp_all <;> omega

theorem card_le (n : Nat) (S : PSet) : card n S ≤ n := by
  have := @List.countP_le_length _ S (List.range n)
  simpa [card] using this

theorem card_pos {n : Nat} {S : PSet} {p : PlaceId} (hp : p < n) (hS : S p = true) :
    0 < card n S :=
  List.countP_pos_iff.mpr ⟨p, List.mem_range.mpr hp, hS⟩

theorem card_ins {n : Nat} {S : PSet} {p : PlaceId} (hp : p < n) (hS : S p = false) :
    card n S + 1 ≤ card n (ins S p) := by
  refine countP_lt (fun q _ h => by simp [ins, h]) ⟨p, List.mem_range.mpr hp, by simp [ins], hS⟩

/-! ## The minimality filter -/

theorem mem_minimalOf {n : Nat} {found : List PSet} {K : PSet} :
    K ∈ minimalOf n found ↔ ∃ i, ∃ hi : i < found.length, found[i] = K ∧
      ∀ j, ∀ hj : j < found.length, j ≠ i → subsetB n found[j] found[i] = false := by
  unfold minimalOf
  simp only [List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨i, hi, hK⟩
    rw [List.getElem?_eq_getElem hi, Option.getD_some] at hK
    split at hK
    · cases hK
    · rename_i hno
      cases hK
      refine ⟨i, hi, rfl, fun j hj hji => ?_⟩
      simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq,
        not_exists, not_and] at hno
      have := hno j hj hji
      rw [List.getElem?_eq_getElem hj, Option.getD_some] at this
      simpa using this
  · rintro ⟨i, hi, rfl, hmin⟩
    refine ⟨i, hi, ?_⟩
    rw [List.getElem?_eq_getElem hi, Option.getD_some, if_neg]
    simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq,
      not_exists, not_and]
    intro j hj hji
    rw [List.getElem?_eq_getElem hj, Option.getD_some]
    simp [hmin j hj hji]

/-- The search's `found` list never holds an entry that contains an earlier one. -/
abbrev Antichain (n : Nat) (found : List PSet) : Prop :=
  found.Pairwise fun a b => subsetB n a b = false

/-- Every entry of an antichain contains a kept (minimal) entry. -/
theorem exists_minimal_below {n : Nat} {found : List PSet} (hac : Antichain n found)
    {F : PSet} (hF : F ∈ found) : ∃ K ∈ minimalOf n found, subsetB n K F = true := by
  have hpw := List.pairwise_iff_getElem.mp hac
  suffices h : ∀ c, ∀ i (hi : i < found.length), card n found[i] ≤ c →
      ∃ K ∈ minimalOf n found, subsetB n K found[i] = true by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hF
    exact h _ i hi (Nat.le_refl _)
  intro c
  induction c using Nat.strongRecOn with
  | _ c ih =>
    intro i hi hc
    by_cases hkept : ∀ j, ∀ hj : j < found.length, j ≠ i → subsetB n found[j] found[i] = false
    · exact ⟨found[i], mem_minimalOf.mpr ⟨i, hi, rfl, hkept⟩, subsetB_refl n _⟩
    · have hex : ∃ j, ∃ hj : j < found.length, j ≠ i ∧ subsetB n found[j] found[i] = true := by
        refine Classical.byContradiction fun hno => hkept fun j hj hji => ?_
        cases hs : subsetB n found[j] found[i]
        · rfl
        · exact absurd ⟨j, hj, hji, hs⟩ hno
      obtain ⟨j, hj, hji, hsub⟩ := hex
      -- `j` comes after `i` (else the antichain is violated) and is strictly smaller.
      have hij : i < j := by
        rcases Nat.lt_or_gt_of_ne hji with hlt | hgt
        · have := hpw j i hj hi hlt
          rw [hsub] at this; cases this
        · exact hgt
      have hnot := hpw i j hi hj hij
      have hlt : card n found[j] < card n found[i] := by
        unfold card
        refine countP_lt (fun x hx h => subsetB_iff.mp hsub x (List.mem_range.mp hx) h) ?_
        refine Classical.byContradiction fun hno => ?_
        simp only [not_exists, not_and, Bool.not_eq_false] at hno
        have : subsetB n found[i] found[j] = true :=
          subsetB_iff.mpr fun p hp hip => hno p (List.mem_range.mpr hp) hip
        rw [hnot] at this; cases this
      obtain ⟨K, hK, hKj⟩ := ih (card n found[j]) (by omega) j hj (Nat.le_refl _)
      exact ⟨K, hK, subsetB_trans hKj hsub⟩

/-! ## The search loop -/

theorem seqM_induct {α : Type} {g : α → St → Option St} {Q : St → Prop} :
    ∀ {xs : List α} {st st' : St},
    (∀ x ∈ xs, ∀ s1 s2, Q s1 → g x s1 = some s2 → Q s2) → Q st → seqM g xs st = some st' →
      Q st'
  | [], st, st', _, hq, h => by cases h; exact hq
  | x :: xs, st, st', hg, hq, h => by
    unfold seqM at h
    cases hx : g x st with
    | none => rw [hx] at h; cases h
    | some s =>
      rw [hx] at h
      exact seqM_induct (fun y hy => hg y (List.mem_cons_of_mem _ hy))
        (hg x List.mem_cons_self _ _ hq hx) h

theorem seqM_hit {α : Type} {g : α → St → Option St} {Q W : St → Prop} :
    ∀ {xs : List α} {st st' : St},
    (∀ x ∈ xs, ∀ s1 s2, Q s1 → g x s1 = some s2 → Q s2 ∧ (W s1 → W s2)) →
    (∃ x ∈ xs, ∀ s1 s2, Q s1 → g x s1 = some s2 → W s2) →
    Q st → seqM g xs st = some st' → W st'
  | [], _, _, _, hx, _, _ => by obtain ⟨_, hx, _⟩ := hx; cases hx
  | x :: xs, st, st', hg, hx, hq, h => by
    unfold seqM at h
    cases hgx : g x st with
    | none => rw [hgx] at h; cases h
    | some s =>
      rw [hgx] at h
      have hs := hg x List.mem_cons_self _ _ hq hgx
      obtain ⟨y, hy, hw⟩ := hx
      rcases List.mem_cons.mp hy with rfl | hy'
      · have hws := hw _ _ hq hgx
        exact seqM_induct (Q := fun s => Q s ∧ W s)
          (fun y hy s1 s2 h12 heq =>
            let r := hg y (List.mem_cons_of_mem _ hy) s1 s2 h12.1 heq
            ⟨r.1, r.2 h12.2⟩) ⟨hs.1, hws⟩ h |>.2
      · exact seqM_hit (fun z hz => hg z (List.mem_cons_of_mem _ hz)) ⟨y, hy', hw⟩ hs.1 h

theorem seqM_congr {α : Type} {g1 g2 : α → St → Option St} :
    ∀ {xs : List α} {st : St}, (∀ x ∈ xs, ∀ s, g1 x s = g2 x s) → seqM g1 xs st = seqM g2 xs st
  | [], _, _ => rfl
  | x :: xs, st, h => by
    unfold seqM
    rw [h x List.mem_cons_self st]
    cases g2 x st with
    | none => rfl
    | some s => exact seqM_congr fun y hy => h y (List.mem_cons_of_mem _ hy)

/-- A pushed set: nonempty below `n` and closed (no violating transition). -/
def Good (net : FlatNet) (n : Nat) (F : PSet) : Prop :=
  (∃ p < n, F p = true) ∧ ∀ ft ∈ net, violates n F ft = false

/-- The invariant of `found`. -/
def Inv (net : FlatNet) (n : Nat) (found : List PSet) : Prop :=
  Antichain n found ∧ ∀ F ∈ found, Good net n F

theorem violating_input {net : FlatNet} {n : Nat} {S : PSet} {ft : FlatTransition}
    (h : net.find? (violates n S) = some ft) {p : PlaceId} (hp : p ∈ inputsOf n ft) :
    p < n ∧ S p = false := by
  have hv := List.find?_some h
  simp only [inputsOf, List.mem_filter, List.mem_range] at hp
  refine ⟨hp.1, ?_⟩
  unfold violates consumesFrom at hv
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false, List.mem_range,
    Bool.and_eq_true, not_and, Bool.not_eq_true] at hv
  cases hS : S p
  · rfl
  · exact absurd hS (by simpa using hv.2 p hp.1 hp.2)

/-- **The fuel fallback of `grow_siphon` is never returned** while `n < f + card n S`: each
recursive call adds a place below `n` not yet in the set. So the model is the Rust recursion. -/
theorem growZ_fuel_irrelevant {net : FlatNet} {n budget : Nat} {cut : Nat → Bool}
    (z1 z2 : Option St) :
    ∀ f S st, n < f + card n S →
      growZ net n budget cut z1 f S st = growZ net n budget cut z2 f S st
  | 0, S, _, h => absurd h (by have := card_le n S; omega)
  | f + 1, S, st, h => by
    unfold growZ
    split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · rename_i ft hft
          refine seqM_congr fun p hp s => ?_
          obtain ⟨hpn, hSp⟩ := violating_input hft hp
          exact growZ_fuel_irrelevant z1 z2 f (ins S p) s (by have := card_ins hpn hSp; omega)

/-- **The node of `grow_siphon`, specified.** From a nonempty set `C` and a `found` satisfying
`Inv`, a returning call (a) only appends to `found`, (b) keeps `Inv`, and (c) leaves in `found` a
subset of every siphon below `n` that contains `C`. -/
theorem growZ_spec {net : FlatNet} {n budget : Nat} {cut : Nat → Bool} (z : Option St) :
    ∀ f C st st', n < f + card n C → (∃ p < n, C p = true) → Inv net n st.1 →
      growZ net n budget cut z f C st = some st' →
      (∃ ext, st'.1 = st.1 ++ ext) ∧ Inv net n st'.1 ∧
      ∀ S : PlaceId → Prop, (∀ p, S p → p < n) → Siphon net S →
        (∀ p < n, C p = true → S p) → ∃ F ∈ st'.1, ∀ p < n, F p = true → S p
  | 0, C, _, _, h, _, _, _ => absurd h (by have := card_le n C; omega)
  | f + 1, C, st, st', hfuel, hne, hinv, h => by
    unfold growZ at h
    split at h
    · cases h
    · rename_i hnb
      split at h
      · -- pruned: some found set lies inside `C`
        rename_i hprune
        cases h
        refine ⟨⟨[], by simp⟩, hinv, fun S _ _ hCS => ?_⟩
        obtain ⟨F, hF, hsub⟩ := List.any_eq_true.mp hprune
        exact ⟨F, hF, fun p hp hFp => hCS p hp (subsetB_iff.mp hsub p hp hFp)⟩
      · rename_i hprune
        split at h
        · -- closed: `C` is a siphon and is pushed
          rename_i hnone
          cases h
          refine ⟨⟨[C], rfl⟩, ⟨?_, ?_⟩, fun S _ _ hCS => ⟨C, by simp, hCS⟩⟩
          · refine List.pairwise_append.mpr ⟨hinv.1, List.pairwise_singleton _ _, ?_⟩
            intro a ha b hb
            rw [List.mem_singleton] at hb
            subst hb
            simp only [Bool.not_eq_true, List.any_eq_false] at hprune
            simpa using hprune a ha
          · intro F hF
            rcases List.mem_append.mp hF with hF | hF
            · exact hinv.2 F hF
            · rw [List.mem_singleton] at hF
              subst hF
              refine ⟨hne, fun ft hft => ?_⟩
              have := List.find?_eq_none.mp hnone ft hft
              simpa using this
        · -- a violating producer: branch on each of its inputs
          rename_i ft hft
          let Q : St → Prop := fun s => (∃ ext, s.1 = st.1 ++ ext) ∧ Inv net n s.1
          have hQ : ∀ p ∈ inputsOf n ft, ∀ s1 s2 : St, Q s1 →
              growZ net n budget cut z f (ins C p) s1 = some s2 →
              Q s2 ∧ ∀ F ∈ s1.1, F ∈ s2.1 := by
            intro p hp s1 s2 hq1 heq
            obtain ⟨hpn, hCp⟩ := violating_input hft hp
            obtain ⟨⟨e2, he2⟩, hinv2, _⟩ := growZ_spec z f (ins C p) s1 s2
              (by have := card_ins hpn hCp; omega) ⟨p, hpn, by simp [ins]⟩ hq1.2 heq
            obtain ⟨e1, he1⟩ := hq1.1
            refine ⟨⟨⟨e1 ++ e2, by rw [he2, he1, List.append_assoc]⟩, hinv2⟩, fun F hF => ?_⟩
            rw [he2]; exact List.mem_append_left _ hF
          have hQ0 : Q (st.1, st.2 + 1) := ⟨⟨[], by simp⟩, hinv⟩
          have hfin := seqM_induct (fun p hp s1 s2 hq heq => (hQ p hp s1 s2 hq heq).1) hQ0 h
          refine ⟨hfin.1, hfin.2, fun S hSb hSiph hCS => ?_⟩
          have hmem := List.mem_of_find?_eq_some hft
          have hv := List.find?_some hft
          simp only [violates, outputsInto, Bool.and_eq_true, List.any_eq_true, List.mem_range]
            at hv
          obtain ⟨⟨p, hpn, hout⟩, _⟩ := hv
          obtain ⟨hop, hCp⟩ := hout
          obtain ⟨q, hSq, hcq⟩ := hSiph ft hmem ⟨p, hCS p hpn hCp, hop⟩
          have hqn := hSb q hSq
          have hqin : q ∈ inputsOf n ft := by
            simp only [inputsOf, List.mem_filter, List.mem_range]
            exact ⟨hqn, consumesB_iff.mpr hcq⟩
          obtain ⟨_, hCq⟩ := violating_input hft hqin
          refine seqM_hit (Q := Q) (W := fun s => ∃ F ∈ s.1, ∀ p < n, F p = true → S p)
            (fun p hp s1 s2 hq heq => ?_) ⟨q, hqin, fun s1 s2 hq heq => ?_⟩ hQ0 h
          · obtain ⟨hq2, hsub⟩ := hQ p hp s1 s2 hq heq
            exact ⟨hq2, fun ⟨F, hF, hFS⟩ => ⟨F, hsub F hF, hFS⟩⟩
          · obtain ⟨_, _, hc⟩ := growZ_spec z f (ins C q) s1 s2
              (by have := card_ins hqn hCq; omega) ⟨q, hqn, by simp [ins]⟩ hq.2 heq
            refine hc S hSb hSiph fun r hr hins => ?_
            simp only [ins, Bool.or_eq_true, beq_iff_eq] at hins
            rcases hins with rfl | hCr
            · exact hSq
            · exact hCS r hr hCr

/-- **The start-place loop, specified.** A returning search leaves an antichain of nonempty
siphons below `n`, and every nonempty siphon below `n` contains one of them. -/
theorem searchZ_spec {net : FlatNet} {n budget : Nat} {cut : Nat → Bool} (z : Option St)
    {st' : St} (h : searchZ net n budget cut z = some st') :
    Inv net n st'.1 ∧
    ∀ S : PlaceId → Prop, (∀ p, S p → p < n) → (∃ p, S p) → Siphon net S →
      ∃ F ∈ st'.1, ∀ p < n, F p = true → S p := by
  have hstep : ∀ p ∈ List.range n, ∀ s1 s2 : St, Inv net n s1.1 →
      growZ net n budget cut z n (single p) s1 = some s2 →
      Inv net n s2.1 ∧ ∀ F ∈ s1.1, F ∈ s2.1 := by
    intro p hp s1 s2 hq heq
    have hpn := List.mem_range.mp hp
    obtain ⟨⟨e, he⟩, hinv, _⟩ := growZ_spec z n (single p) s1 s2
      (by have := card_pos (S := single p) hpn (by simp [single]); omega)
      ⟨p, hpn, by simp [single]⟩ hq heq
    exact ⟨hinv, fun F hF => by rw [he]; exact List.mem_append_left _ hF⟩
  have hQ0 : Inv net n ([] : List PSet) := ⟨List.Pairwise.nil, fun _ h => by cases h⟩
  refine ⟨seqM_induct (Q := fun s => Inv net n s.1)
    (fun p hp s1 s2 hq heq => (hstep p hp s1 s2 hq heq).1) hQ0 h, ?_⟩
  intro S hSb ⟨p, hSp⟩ hSiph
  have hpn := hSb p hSp
  refine seqM_hit (Q := fun s => Inv net n s.1)
    (W := fun s => ∃ F ∈ s.1, ∀ q < n, F q = true → S q)
    (fun x hx s1 s2 hq heq => ?_) ⟨p, List.mem_range.mpr hpn, fun s1 s2 hq heq => ?_⟩ hQ0 h
  · obtain ⟨hq2, hsub⟩ := hstep x hx s1 s2 hq heq
    exact ⟨hq2, fun ⟨F, hF, hFS⟩ => ⟨F, hsub F hF, hFS⟩⟩
  · obtain ⟨_, _, hc⟩ := growZ_spec z n (single p) s1 s2
      (by have := card_pos (S := single p) hpn (by simp [single]); omega)
      ⟨p, hpn, by simp [single]⟩ hq heq
    refine hc S hSb hSiph fun r _ hr => ?_
    simp only [single, beq_iff_eq] at hr
    subst hr
    exact hSp

/-- **The search is the Rust search**: its result does not depend on the fuel fallback. -/
theorem searchZ_fuel_irrelevant {net : FlatNet} {n budget : Nat} {cut : Nat → Bool}
    (z1 z2 : Option St) : searchZ net n budget cut z1 = searchZ net n budget cut z2 :=
  seqM_congr fun p hp s => growZ_fuel_irrelevant z1 z2 n (single p) s
    (by have := card_pos (S := single p) (List.mem_range.mp hp) (by simp [single]); omega)

theorem findMinimalSiphons_some {net : FlatNet} {n budget : Nat} {cut : Nat → Bool}
    {sips : List (List PlaceId)} (h : findMinimalSiphons net n budget cut = some sips) :
    ∃ st', searchZ net n budget cut none = some st' ∧
      sips = (minimalOf n st'.1).map (toList n) := by
  unfold findMinimalSiphons at h
  cases hs : searchZ net n budget cut none with
  | none => rw [hs] at h; cases h
  | some st' => rw [hs] at h; cases h; exact ⟨st', rfl, rfl⟩

/-- **`find_minimal_siphons` is complete when its budget is not hit** ([VER-020]). If the search
returns (neither the 10 000-node budget nor the [VER-013] stop cut it), every nonempty siphon
below `n` contains a returned siphon. Committing to one input per producer, or to all of them,
is not complete (`pre_fix_padding_proves_dead_net`). -/
theorem findMinimalSiphons_complete {net : FlatNet} {n budget : Nat} {cut : Nat → Bool}
    {sips : List (List PlaceId)} (h : findMinimalSiphons net n budget cut = some sips)
    (S : PlaceId → Prop) (hSb : ∀ p, S p → p < n) (hne : ∃ p, S p) (hS : Siphon net S) :
    ∃ K ∈ sips, ∀ p ∈ K, S p := by
  obtain ⟨st', hst, rfl⟩ := findMinimalSiphons_some h
  obtain ⟨hinv, hcomp⟩ := searchZ_spec none hst
  obtain ⟨F, hF, hFS⟩ := hcomp S hSb hne hS
  obtain ⟨K, hK, hKF⟩ := exists_minimal_below hinv.1 hF
  refine ⟨toList n K, List.mem_map_of_mem hK, fun p hp => ?_⟩
  obtain ⟨hpn, hKp⟩ := mem_toList.mp hp
  exact hFS p hpn (subsetB_iff.mp hKF p hpn hKp)

/-- **`find_minimal_siphons` returns minimal siphons only.** Each returned list is a nonempty
siphon below `n`, and a nonempty siphon inside it is all of it. With
`findMinimalSiphons_complete`, the result is exactly the set of minimal siphons. -/
theorem findMinimalSiphons_sound {net : FlatNet} {n budget : Nat} {cut : Nat → Bool}
    {sips : List (List PlaceId)} (h : findMinimalSiphons net n budget cut = some sips)
    {K : List PlaceId} (hK : K ∈ sips) :
    (∃ p, p ∈ K) ∧ (∀ p ∈ K, p < n) ∧ Siphon net (· ∈ K) ∧
    ∀ S : PlaceId → Prop, (∃ p, S p) → Siphon net S → (∀ p, S p → p ∈ K) → ∀ p ∈ K, S p := by
  obtain ⟨st', hst, rfl⟩ := findMinimalSiphons_some h
  obtain ⟨hinv, hcomp⟩ := searchZ_spec none hst
  obtain ⟨K', hK', rfl⟩ := List.mem_map.mp hK
  obtain ⟨i, hi, hKi, hkept⟩ := mem_minimalOf.mp hK'
  have hgood := hinv.2 K' (hKi ▸ List.getElem_mem hi)
  refine ⟨?_, fun p hp => (mem_toList.mp hp).1, ?_, ?_⟩
  · obtain ⟨p, hpn, hp⟩ := hgood.1
    exact ⟨p, mem_toList.mpr ⟨hpn, hp⟩⟩
  · intro ft hft ⟨p, hp, hout⟩
    obtain ⟨hpn, hKp⟩ := mem_toList.mp hp
    have hv := hgood.2 ft hft
    have hinto : outputsInto n K' ft = true :=
      List.any_eq_true.mpr ⟨p, List.mem_range.mpr hpn, Bool.and_eq_true_iff.mpr ⟨hout, hKp⟩⟩
    simp only [violates, hinto, Bool.true_and, Bool.not_eq_false'] at hv
    obtain ⟨q, hq, hcq⟩ := List.any_eq_true.mp hv
    obtain ⟨hcq, hKq⟩ := Bool.and_eq_true_iff.mp hcq
    exact ⟨q, mem_toList.mpr ⟨List.mem_range.mp hq, hKq⟩, consumesB_iff.mp hcq⟩
  · intro S hne hS hSK
    have hSb : ∀ p, S p → p < n := fun p hp => (mem_toList.mp (hSK p hp)).1
    obtain ⟨F, hF, hFS⟩ := hcomp S hSb hne hS
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hF
    have hji : j = i := by
      refine Classical.byContradiction fun hne' => ?_
      have hsub : subsetB n st'.1[j] st'.1[i] = true := subsetB_iff.mpr fun p hp hFp => by
        have := hSK p (hFS p hp hFp)
        rw [hKi]; exact (mem_toList.mp this).2
      rw [hkept j hj hne'] at hsub
      cases hsub
    subst hji
    intro p hp
    obtain ⟨hpn, hKp⟩ := mem_toList.mp hp
    rw [← hKi] at hKp
    exact hFS p hpn hKp

/-! ## The trap contraction -/

theorem okAt_false {net : FlatNet} {n : Nat} {T : PSet} {pid : PlaceId}
    (h : okAt net n T pid = false) :
    ∃ ft ∈ net, consumesB ft pid = true ∧ ∀ q < n, outputsB ft q = true → T q = false := by
  unfold okAt at h
  simp only [List.all_eq_false, Bool.or_eq_true, Bool.not_eq_true', not_or,
    Bool.not_eq_true, List.any_eq_false, List.mem_range, Bool.and_eq_true, not_and] at h
  obtain ⟨ft, hft, hc, hno⟩ := h
  refine ⟨ft, hft, by simpa using hc, fun q hq hout => ?_⟩
  simpa using hno q hq hout

/-- One `for &pid in siphon` round only removes places; a round that reports `changed`
removed one of `M`'s places, so the count over `M` dropped. -/
theorem fold_spec {net : FlatNet} {n : Nat} {M : List PlaceId} :
    ∀ (l : List PlaceId) (st : PSet × Bool), (∀ x ∈ l, x ∈ M) →
      (∀ q, (l.foldl (passStep net n) st).1 q = true → st.1 q = true) ∧
      ((l.foldl (passStep net n) st).2 = true →
        st.2 = true ∨ M.countP (l.foldl (passStep net n) st).1 < M.countP st.1)
  | [], st, _ => ⟨fun _ h => h, fun h => Or.inl h⟩
  | x :: xs, st, hM => by
    simp only [List.foldl_cons]
    have ih := fold_spec (net := net) (n := n) (M := M) xs (passStep net n st x)
      fun y hy => hM y (List.mem_cons_of_mem _ hy)
    by_cases hx : st.1 x = true
    · by_cases hok : okAt net n st.1 x = true
      · have hps : passStep net n st x = st := by simp [passStep, hx, hok]
        rw [hps] at ih ⊢
        exact ih
      · have hps : passStep net n st x = (remove st.1 x, true) := by simp [passStep, hx, hok]
        rw [hps] at ih ⊢
        refine ⟨fun q hq => ?_, fun _ => Or.inr ?_⟩
        · have := ih.1 q hq
          simp only [remove, Bool.and_eq_true] at this
          exact this.2
        · have hle := List.countP_mono_left (l := M) (fun q _ hq => ih.1 q hq)
          have hlt : M.countP (remove st.1 x) < M.countP st.1 := by
            refine countP_lt (fun q _ hq => ?_) ⟨x, hM x List.mem_cons_self, hx, by simp [remove]⟩
            simp only [remove, Bool.and_eq_true] at hq; exact hq.2
          exact Nat.lt_of_le_of_lt hle hlt
    · have hps : passStep net n st x = st := by simp [passStep, hx]
      rw [hps] at ih ⊢
      exact ih

theorem fold_true {net : FlatNet} {n : Nat} :
    ∀ (l : List PlaceId) (st : PSet × Bool), st.2 = true →
      (l.foldl (passStep net n) st).2 = true
  | [], _, h => h
  | x :: xs, st, h => by
    simp only [List.foldl_cons]
    refine fold_true xs _ ?_
    unfold passStep
    split
    · exact h
    · split
      · exact h
      · rfl

/-- A round that reports no change changed nothing, and every place of the round satisfies the
trap test. -/
theorem fold_false {net : FlatNet} {n : Nat} :
    ∀ (l : List PlaceId) (st : PSet × Bool), (l.foldl (passStep net n) st).2 = false →
      st.2 = false ∧ (l.foldl (passStep net n) st).1 = st.1 ∧
      ∀ pid ∈ l, st.1 pid = true → okAt net n st.1 pid = true
  | [], st, h => ⟨h, rfl, fun _ h => by cases h⟩
  | x :: xs, st, h => by
    simp only [List.foldl_cons] at h ⊢
    have ih := fold_false (net := net) (n := n) xs _ h
    by_cases hx : st.1 x = true
    · by_cases hok : okAt net n st.1 x = true
      · have hps : passStep net n st x = st := by simp [passStep, hx, hok]
        rw [hps] at ih ⊢
        refine ⟨ih.1, ih.2.1, fun pid hpid hT => ?_⟩
        rcases List.mem_cons.mp hpid with rfl | hpid
        · exact hok
        · exact ih.2.2 pid hpid hT
      · have hps : passStep net n st x = (remove st.1 x, true) := by simp [passStep, hx, hok]
        rw [hps] at ih
        exact absurd ih.1 (by simp)
    · have hps : passStep net n st x = st := by simp [passStep, hx]
      rw [hps] at ih ⊢
      refine ⟨ih.1, ih.2.1, fun pid hpid hT => ?_⟩
      rcases List.mem_cons.mp hpid with rfl | hpid
      · exact absurd hT hx
      · exact ih.2.2 pid hpid hT

/-- A round never removes a place of a trap `U` that the current set contains: removal needs a
consumer of the place that produces nowhere into the set, and a consumer of a `U` place produces
into `U`. -/
theorem fold_keep {net : FlatNet} {n : Nat} {U : PlaceId → Prop} (hU : Trap net U)
    (hUn : ∀ q, U q → q < n) :
    ∀ (l : List PlaceId) (st : PSet × Bool), (∀ q, U q → st.1 q = true) →
      ∀ q, U q → (l.foldl (passStep net n) st).1 q = true
  | [], _, h => h
  | x :: xs, st, h => by
    simp only [List.foldl_cons]
    refine fold_keep hU hUn xs _ ?_
    unfold passStep
    split
    · exact h
    · split
      · exact h
      · rename_i hok
        have hnx : ¬ U x := by
          intro hUx
          obtain ⟨ft, hft, hc, hno⟩ := okAt_false (Bool.eq_false_iff.mpr hok)
          obtain ⟨q, hUq, hout⟩ := hU ft hft ⟨x, hUx, consumesB_iff.mp hc⟩
          have := hno q (hUn q hUq) hout
          rw [h q hUq] at this
          cases this
        intro q hq
        have hqx : q ≠ x := fun e => hnx (e ▸ hq)
        simp [remove, hqx, h q hq]

/-- **The `while changed` loop, specified**, at any fuel above the count of the current set over
the siphon: the result lies inside the start set, passes the trap test at each of the siphon's
places it keeps, and keeps every trap below `n` the start set contains. -/
theorem contractZ_spec {net : FlatNet} {n : Nat} {sip : List PlaceId} (z : PSet) :
    ∀ f T, sip.countP T < f →
      (∀ q, contractZ net n sip z f T q = true → T q = true) ∧
      (∀ pid ∈ sip, contractZ net n sip z f T pid = true →
        okAt net n (contractZ net n sip z f T) pid = true) ∧
      (∀ U : PlaceId → Prop, Trap net U → (∀ q, U q → q < n) → (∀ q, U q → T q = true) →
        ∀ q, U q → contractZ net n sip z f T q = true)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, T, h => by
    unfold contractZ
    cases hp : (pass net n sip T).2 with
    | true =>
      simp only [if_true]
      obtain ⟨hsub, hmeas⟩ := fold_spec (net := net) (n := n) (M := sip) sip (T, false)
        (fun _ h => h)
      have hlt : sip.countP (pass net n sip T).1 < sip.countP T := by
        rcases hmeas hp with h' | h'
        · cases h'
        · exact h'
      obtain ⟨ih1, ih2, ih3⟩ := contractZ_spec (net := net) (n := n) (sip := sip) z f (pass net n sip T).1 (by omega)
      refine ⟨fun q hq => hsub q (ih1 q hq), ih2, fun U hU hUn hUT => ?_⟩
      exact ih3 U hU hUn (fold_keep hU hUn sip (T, false) hUT)
    | false =>
      simp only [Bool.false_eq_true, if_false]
      obtain ⟨_, heq, hok⟩ := fold_false (net := net) (n := n) sip (T, false) hp
      unfold pass
      rw [heq]
      exact ⟨fun _ h => h, hok, fun _ _ _ hUT => hUT⟩

/-- **The fuel fallback of the contraction is never returned**: each changed round strictly
lowers the count over the siphon, so `sip.length + 1` rounds suffice. -/
theorem contractZ_fuel_irrelevant {net : FlatNet} {n : Nat} {sip : List PlaceId} (z1 z2 : PSet) :
    ∀ f T, sip.countP T < f → contractZ net n sip z1 f T = contractZ net n sip z2 f T
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, T, h => by
    unfold contractZ
    cases hp : (pass net n sip T).2 with
    | true =>
      simp only [if_true]
      obtain ⟨_, hmeas⟩ := fold_spec (net := net) (n := n) (M := sip) sip (T, false)
        (fun _ h => h)
      have hlt : sip.countP (pass net n sip T).1 < sip.countP T := by
        rcases hmeas hp with h' | h'
        · cases h'
        · exact h'
      exact contractZ_fuel_irrelevant (net := net) (n := n) (sip := sip) z1 z2 f _ (by omega)
    | false => rfl

/-- **The contraction is the Rust loop**: `maximalTrapIn` does not depend on the fallback. -/
theorem maximalTrapIn_fuel_irrelevant (net : FlatNet) (n : Nat) (sip : List PlaceId) (z : PSet) :
    toList n (contractZ net n sip z (sip.length + 1) (ofList sip)) = maximalTrapIn net n sip := by
  unfold maximalTrapIn
  rw [contractZ_fuel_irrelevant z emptyS _ _ (Nat.lt_succ_of_le List.countP_le_length)]

/-- **`find_maximal_trap_in` returns the maximal trap inside the siphon** ([VER-020]): the
result lies inside `sip`, is a trap, and contains every trap that lies inside `sip`. -/
theorem maximalTrapIn_spec {net : FlatNet} {n : Nat} {sip : List PlaceId}
    (hsip : ∀ p ∈ sip, p < n) :
    (∀ p ∈ maximalTrapIn net n sip, p ∈ sip) ∧
    Trap net (· ∈ maximalTrapIn net n sip) ∧
    ∀ U : PlaceId → Prop, Trap net U → (∀ p, U p → p ∈ sip) →
      ∀ p, U p → p ∈ maximalTrapIn net n sip := by
  have hfuel : sip.countP (ofList sip) < sip.length + 1 :=
    Nat.lt_succ_of_le List.countP_le_length
  obtain ⟨hsub, hok, hkeep⟩ := contractZ_spec (net := net) (n := n) emptyS _ (ofList sip) hfuel
  unfold maximalTrapIn
  generalize contractZ net n sip emptyS (sip.length + 1) (ofList sip) = R at hsub hok hkeep
  have hin : ∀ p, R p = true → p ∈ sip := fun p hp => by
    have := hsub p hp
    simpa [ofList] using this
  refine ⟨fun p hp => hin p (mem_toList.mp hp).2, ?_, ?_⟩
  · intro ft hft ⟨p, hp, hc⟩
    obtain ⟨_, hRp⟩ := mem_toList.mp hp
    have hokp := hok p (hin p hRp) hRp
    unfold okAt at hokp
    have := List.all_eq_true.mp hokp ft hft
    simp only [consumesB_iff.mpr hc, Bool.not_true, Bool.false_or, List.any_eq_true,
      List.mem_range, Bool.and_eq_true] at this
    obtain ⟨q, hqn, hout, hRq⟩ := this
    exact ⟨q, mem_toList.mpr ⟨hqn, hRq⟩, hout⟩
  · intro U hU hUs p hp
    have hUn : ∀ q, U q → q < n := fun q hq => hsip q (hUs q hq)
    exact mem_toList.mpr ⟨hUn p hp,
      hkeep U hU hUn (fun q hq => by simpa [ofList] using hUs q hq) p hp⟩

/-! ## `structural_check` -/

/-- The siphon/trap verdict decides Commoner's condition. -/
theorem siphonVerdict_sound {net : FlatNet} {n budget : Nat} {cut : Nat → Bool}
    {a0 : AMarking} (h : siphonVerdict net n budget cut a0 = .noPotentialDeadlock) :
    CommonerCond net n a0 := by
  unfold siphonVerdict at h
  split at h
  · cases h
  · rename_i sips hsips
    split at h
    · rename_i hall
      intro S hSb hne hS
      obtain ⟨K, hK, hKS⟩ := findMinimalSiphons_complete hsips S hSb hne hS
      obtain ⟨_, hKn, _, _⟩ := findMinimalSiphons_sound hsips hK
      obtain ⟨hTK, hT, _⟩ := maximalTrapIn_spec (net := net) hKn
      have hm := List.all_eq_true.mp hall K hK
      obtain ⟨p, hp, hpos⟩ := List.any_eq_true.mp hm
      exact ⟨(· ∈ maximalTrapIn net n K), fun q hq => hKS q (hTK q hq), hT, p, hp,
        of_decide_eq_true hpos⟩
    · cases h

/-- A `NoPotentialDeadlock` answer passed the guard: the flat net has a transition. -/
theorem structuralCheck_ne_nil {net : FlatNet} {n budget : Nat} {cut : Nat → Bool}
    {a0 : AMarking} (h : structuralCheck net n budget cut a0 = .noPotentialDeadlock) :
    net ≠ [] := by
  intro he
  subst he
  simp [structuralCheck] at h

/-- On a net with a transition the guard changes nothing: the fix only refuses the empty net. -/
theorem structuralCheck_eq_unguarded {net : FlatNet} (hne : net ≠ []) (n budget : Nat)
    (cut : Nat → Bool) (a0 : AMarking) :
    structuralCheck net n budget cut a0 = structuralCheckUnguarded net n budget cut a0 := by
  have : net.isEmpty = false := by cases net with
    | nil => exact absurd rfl hne
    | cons _ _ => rfl
  simp [structuralCheck, structuralCheckUnguarded, this]

/-- **`structural_check` decides Commoner's condition** ([VER-020]). A `NoPotentialDeadlock`
answer, for any node budget and any stop, means every nonempty siphon below `n` contains a
trap that is marked under the initial marking: `Commoner.CommonerCond`. -/
theorem structural_check_sound {net : FlatNet} {n budget : Nat} {cut : Nat → Bool}
    {a0 : AMarking} (h : structuralCheck net n budget cut a0 = .noPotentialDeadlock) :
    CommonerCond net n a0 := by
  unfold structuralCheck at h
  split at h
  · cases h
  · exact siphonVerdict_sound h

/-- **The early structural `Proven` is sound for the untimed net.** The premises are the guard
`commoner_applies` (`Ordinary`) and the flattener's dense index (`InputsBelow`, P3); the flat
net's nonemptiness is no longer a premise, it follows from the answer
(`structuralCheck_ne_nil`, the guard in `structural_check`). The conclusion is about the
untimed relation `ReachA`, the [VER-004] contract: it says nothing about a timed execution
under [TIME-013] reaping (`structural_proven_is_untimed_only`). It also relies on the
conditions `verify_net` checks beside `commoner_applies` (premise P6), which nothing here
models. -/
theorem structural_proven_sound {net : FlatNet} {n budget : Nat} {cut : Nat → Bool}
    {a0 : AMarking} (hord : Ordinary net) (hbelow : InputsBelow net n)
    (h : structuralCheck net n budget cut a0 = .noPotentialDeadlock)
    {a : AMarking} (hr : ReachA net a0 a) : ¬ Dead net a :=
  commoner (structuralCheck_ne_nil h) hord hbelow (structural_check_sound h) hr

/-- **The `Proven` answers the property the verifier decides.** `Dead` is
`ReapingVsUntimed.QuiescentA`, so no untimed-reachable marking is a `DeadlockFree` violation
(`dlfBad`, `encode_property_violation`'s arm: quiescent with a token off the sinks), for the
sink-free nets the structural route admits (P6). -/
theorem structural_proven_no_dlf_violation {net : FlatNet} {n budget : Nat} {cut : Nat → Bool}
    {a0 : AMarking} (hord : Ordinary net) (hbelow : InputsBelow net n)
    (h : structuralCheck net n budget cut a0 = .noPotentialDeadlock) :
    ProvenFor (ReachA net a0) (ReapingVsUntimed.dlfBad net [] n) :=
  fun _ hr hbad => structural_proven_sound hord hbelow h hr hbad.1

/-! ## Retrodiction: a net with no transitions -/

/-- `{a:1}` on a one-place net. -/
def aOne : AMarking := fun p => if p = 0 then 1 else 0

/-- **Retrodiction: before the guard, the check proved a dead net deadlock-free when it had no
transitions.** The flat net is empty, `commoner_applies` holds vacuously, and the one place is a
siphon whose maximal trap is itself and is marked, so the unguarded check answered
`NoPotentialDeadlock` and `verify_net` returned `Proven` by method `structural`. Yet the
initial marking is dead and strands a token: the [VER-002] `DeadlockFree` violation (`dlfBad`
with no sinks); the [VER-017] enumeration answers `Violated` on the same net. The reviewer
reproduced it against the Rust with `PetriNet::builder("empty").place(a)` and
`enumeration_max_classes(0)` (the Rust regression test `a_net_without_transitions_is_not_proven_structurally`). The last conjunct is the
fix: the guarded check answers `Inconclusive` and the net falls through to a route that decides
it. The `hne` premise of `Commoner.commoner` is necessary for the same reason. -/
theorem empty_net_structural_proven_dead :
    structuralCheckUnguarded [] 1 siphonSearchBudget (fun _ => false) aOne = .noPotentialDeadlock
    ∧ Ordinary [] ∧ InputsBelow [] 1 ∧ CommonerCond [] 1 aOne ∧ Dead [] aOne
    ∧ ReapingVsUntimed.dlfBad [] [] 1 aOne
    ∧ structuralCheck [] 1 siphonSearchBudget (fun _ => false) aOne = .inconclusive := by
  have hu : structuralCheckUnguarded [] 1 siphonSearchBudget (fun _ => false) aOne =
      .noPotentialDeadlock := by decide
  have hcond : CommonerCond [] 1 aOne := by
    unfold structuralCheckUnguarded at hu
    split at hu
    · cases hu
    · exact siphonVerdict_sound hu
  have hdead : Dead ([] : FlatNet) aOne := fun _ h => by cases h
  have hbad : ReapingVsUntimed.dlfBad [] [] 1 aOne :=
    And.intro hdead ⟨0, by decide, by simp, by decide⟩
  have hg : structuralCheck [] 1 siphonSearchBudget (fun _ => false) aOne = .inconclusive := by
    decide
  have hord : Ordinary ([] : FlatNet) := fun _ h => by cases h
  have hbelow : InputsBelow ([] : FlatNet) 1 := fun _ h => by cases h
  exact ⟨hu, hord, hbelow, hcond, hdead, hbad, hg⟩

/-! ## The structural `Proven` is untimed only ([VER-004] AC3, [TIME-013])

`ReapingVsUntimed.execCycle` runs its one-transition net `netR`. `execCycleT` is the same cell
over any one flat transition `ft`, and is `execCycle` at `ft = (tR, [1])` (`execCycleT_tR`). -/

/-- `ReapingVsUntimed.execCycle` over the flat transition `ft`. -/
def execCycleT (ft : FlatTransition) (enforce : Nat → Nat → Cell → Cell) (tm : Timing)
    (now : Nat) (a : AMarking) (s : Cell) : ReapingVsUntimed.Outcome :=
  let s1 := updateCell now { s with tokens := enabledA a ft.1 }
  let s2 := enforce tm.latest now s1
  if s2.enabled = false then .halted a s2
  else if fires tm.earliest now s2 && enabledA a ft.1 then
    .running (fireA a ft.1 ft.2)
      { s2 with tokens := enabledA (fireA a ft.1 ft.2) ft.1, dirty := true }
  else .running a s2

/-- `ReapingVsUntimed.execRun` over the flat transition `ft`. -/
def execRunT (ft : FlatTransition) (enforce : Nat → Nat → Cell → Cell) (tm : Timing) :
    AMarking → Cell → List Nat → ReapingVsUntimed.Outcome
  | a, s, [] => .running a s
  | a, s, now :: rest =>
    match execCycleT ft enforce tm now a s with
    | .halted a' s' => .halted a' s'
    | .running a' s' => execRunT ft enforce tm a' s' rest

theorem execCycleT_tR : execCycleT (ReapingVsUntimed.tR, [1]) = ReapingVsUntimed.execCycle :=
  rfl

/-- `t: a → a`, `One` input. In the timed run it carries `wTiming = window(3, 5)`. -/
def tSelf : Transition :=
  { name := "t", inputs := [⟨0, .one, none⟩], inhibitors := [], reads := [], resets := [] }
def netSelf : FlatNet := [(tSelf, [0])]

/-- **The structural `Proven` does not hold for timed executions with reaping.** On the ordinary
self-loop `t: a → a` from `{a:1}`, with no sinks:
1. the shipped check answers `NoPotentialDeadlock`, and the untimed net is never dead, so the
   untimed `Proven` is correct (`structural_proven_sound`);
2. with `window(3, 5)` on `t` and cycles `[0, 10]` (an executor blocked past the deadline,
   tolerance 0 as in `ReapingVsUntimed`), both backends enable `t` at 0, reap it at 10 and
   stop `Quiescent` at `{a:1}`;
3. that marking strands a token on `a`, which is no sink: a `DeadlockFree` violation of the
   timed execution.
`verify_net` skips the [VER-017] enumeration on a timed net (`scg_verifier::is_untimed`), and
the structural candidate had no timing gate, so this net got `Proven { method: "structural" }`
from the Rust at its default settings. The structural route shared R16. The shipped candidate
now requires that no flat transition is marked reapable (P6), which `t` is, so the net goes to
the reap-aware encoders (`reapGate_refuses_witness`; behind the gate,
`structural_proven_sound_timed`). -/
theorem structural_proven_is_untimed_only :
    structuralCheck netSelf 1 siphonSearchBudget (fun _ => false) aOne = .noPotentialDeadlock
    ∧ (∀ a, ReachA netSelf aOne a → ¬ Dead netSelf a)
    ∧ (∀ rest : List Nat,
        execRunT (tSelf, [0]) enforceBB wTiming aOne wInit (0 :: 10 :: rest) =
          .halted aOne ReapingVsUntimed.reapedBB
        ∧ execRunT (tSelf, [0]) enforcePB wTiming aOne wInit (0 :: 10 :: rest) =
          .halted aOne ReapingVsUntimed.reapedPB)
    ∧ ReapingVsUntimed.Strands [] 1 aOne := by
  have hc : structuralCheck netSelf 1 siphonSearchBudget (fun _ => false) aOne =
      .noPotentialDeadlock := by decide
  have hord : Ordinary netSelf := by
    intro ft hmem
    simp only [netSelf, List.mem_singleton] at hmem
    subst hmem
    refine ⟨rfl, rfl, rfl, fun s hs => ?_⟩
    simp only [tSelf, List.mem_singleton] at hs
    subst hs; decide
  have hbelow : InputsBelow netSelf 1 := by
    intro ft hmem s hs
    simp only [netSelf, List.mem_singleton] at hmem
    subst hmem
    simp only [tSelf, List.mem_singleton] at hs
    subst hs; decide
  exact ⟨hc, fun _ hr => structural_proven_sound hord hbelow hc hr, fun _ => ⟨rfl, rfl⟩,
    ⟨0, by decide, by simp, by decide⟩⟩

/-! ## Agreement with the Rust unit tests (`structural_check.rs` `mod tests`) -/

/-- `ring(true)` of the Rust tests, places sorted `g h x y`:
`t1: x + g → y + g`, `t2: y + h → x + h`. -/
def tR1 : Transition :=
  { name := "t1", inputs := [⟨2, .one, none⟩, ⟨0, .one, none⟩], inhibitors := [], reads := [],
    resets := [] }
def tR2 : Transition :=
  { name := "t2", inputs := [⟨3, .one, none⟩, ⟨1, .one, none⟩], inhibitors := [], reads := [],
    resets := [] }
def netRing : FlatNet := [(tR1, [3, 0]), (tR2, [2, 1])]

/-- `a_siphon_behind_a_second_input_is_found`: `{x, y}` is found; `{g:1, h:1}` is a potential
deadlock and adding `x` makes it live. -/
example : ([2, 3] : List PlaceId) ∈
    ((findMinimalSiphons netRing 4 siphonSearchBudget fun _ => false).getD []) := by decide
example : structuralCheck netRing 4 siphonSearchBudget (fun _ => false)
    (fun p => if p = 0 ∨ p = 1 then 1 else 0) = .potentialDeadlock := by decide
example : structuralCheck netRing 4 siphonSearchBudget (fun _ => false)
    (fun p => if p = 0 ∨ p = 1 ∨ p = 2 then 1 else 0) = .noPotentialDeadlock := by decide

/-- `an_exhausted_search_is_inconclusive`. -/
example : findMinimalSiphons netRing 4 1 (fun _ => false) = none := by decide

/-- `a_stopped_verification_gives_up_the_siphon_search`: a stop that fires makes the check
`Inconclusive`, and without it the marked cycle is live. -/
example : structuralCheck netCyc 2 siphonSearchBudget (fun _ => true)
    (fun p => if p = 0 then 1 else 0) = .inconclusive := by decide
example : structuralCheck netCyc 2 siphonSearchBudget (fun _ => false)
    (fun p => if p = 0 then 1 else 0) = .noPotentialDeadlock := by decide

/-! ## Retrodiction: the pre-fix search of f52c482 -/

/-- One sweep of the pre-f52c482 `while changed` expansion: for each transition that outputs
into the current set, add **every** input not yet in it. -/
def preFixSweep (net : FlatNet) (n : Nat) (S : PSet) : PSet × Bool :=
  net.foldl (fun st ft =>
    if outputsInto n st.1 ft then
      (inputsOf n ft).foldl (fun st pid => if !st.1 pid then (ins st.1 pid, true) else st) st
    else st) (S, false)

def preFixExpand (net : FlatNet) (n : Nat) : Nat → PSet → PSet
  | 0, S => S
  | f + 1, S => if (preFixSweep net n S).2 then preFixExpand net n f (preFixSweep net n S).1
      else (preFixSweep net n S).1

/-- The pre-fix `find_minimal_siphons`: one expansion per start place, skipped when it contains
an earlier one. -/
def preFixFind (net : FlatNet) (n : Nat) : List (List PlaceId) :=
  (List.range n).foldl (fun sips start =>
    let sp := toList n (preFixExpand net n (n + 1) (single start))
    if sips.any (fun ex => ex.all fun p => sp.contains p) then sips else sips ++ [sp]) []

/-- The pre-fix `structural_check`: each found siphon's maximal trap only had to be nonempty. -/
def preFixCheck (net : FlatNet) (n : Nat) : Verdict :=
  if 50 < n then .inconclusive
  else if (preFixFind net n).all (fun sip => !(maximalTrapIn net n sip).isEmpty)
  then .noPotentialDeadlock else .potentialDeadlock

/-- The pre-fix search with the post-fix marked-trap test: isolates the search defect. -/
def preFixSearchMarked (net : FlatNet) (n : Nat) (a0 : AMarking) : Verdict :=
  if (preFixFind net n).all (fun sip => (maximalTrapIn net n sip).any fun p => decide (0 < a0 p))
  then .noPotentialDeadlock else .potentialDeadlock

/-- `t1: a + c → b + c` (places `a b c` = `0 1 2`). -/
def tP1 : Transition :=
  { name := "t1", inputs := [⟨0, .one, none⟩, ⟨2, .one, none⟩], inhibitors := [], reads := [],
    resets := [] }
/-- `t2: b → a`. -/
def tP2 : Transition :=
  { name := "t2", inputs := [⟨1, .one, none⟩], inhibitors := [], reads := [], resets := [] }
def netPad : FlatNet := [(tP1, [1, 2]), (tP2, [0])]
def a0Pad : AMarking := fun p => if p = 2 then 1 else 0

theorem ordinary_netPad : Ordinary netPad := by
  intro ft hmem
  simp only [netPad, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · refine ⟨rfl, rfl, rfl, fun s hs => ?_⟩
    simp only [tP1, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> decide
  · refine ⟨rfl, rfl, rfl, fun s hs => ?_⟩
    simp only [tP2, List.mem_singleton] at hs
    subst hs; decide

theorem dead_netPad : Dead netPad a0Pad := by
  intro ft hmem
  simp only [netPad, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl <;> decide

/-- **Retrodiction of f52c482, the search defect** (`a_siphon_is_not_padded_with_every_input`).
Growing by every input of a producer only reaches `{a, b, c}`, whose maximal trap is marked
through `c`, and misses the empty minimal siphon `{a, b}`. The pre-fix Rust answered
`NoPotentialDeadlock` (and so `Proven`) on an ordinary net dead at `{c:1}`, and it still would
with the marked-trap test added; the shipped search finds `{a, b}`. -/
theorem pre_fix_padding_proves_dead_net :
    preFixCheck netPad 3 = .noPotentialDeadlock ∧
    preFixSearchMarked netPad 3 a0Pad = .noPotentialDeadlock ∧
    Ordinary netPad ∧ Dead netPad a0Pad ∧
    ([0, 1] : List PlaceId) ∈ (findMinimalSiphons netPad 3 siphonSearchBudget fun _ => false).getD []
    ∧ structuralCheck netPad 3 siphonSearchBudget (fun _ => false) a0Pad = .potentialDeadlock :=
  ⟨by decide, by decide, ordinary_netPad, dead_netPad, by decide, by decide⟩

/-- **Retrodiction of f52c482, the unchecked trap marking** (`an_unmarked_trap_does_not_count`).
On the ordinary cycle `a ⇄ b` with no token the maximal trap `{a, b}` is nonempty, so the pre-fix
Rust answered `NoPotentialDeadlock`; the net is dead. The shipped check requires a token. -/
theorem pre_fix_unmarked_trap_proves_dead_net :
    preFixCheck netCyc 2 = .noPotentialDeadlock ∧ Ordinary netCyc ∧ Dead netCyc (fun _ => 0) ∧
    structuralCheck netCyc 2 siphonSearchBudget (fun _ => false) (fun _ => 0) =
      .potentialDeadlock :=
  ⟨by decide, marked_trap_is_necessary.1, marked_trap_is_necessary.2.2, by decide⟩

/-! ## The reapable gate of the structural candidate -/

/-- `!flat.transitions.iter().any(|t| t.reapable)`: the conjunct of `verify_net`'s structural
candidate that keeps a net with a reapable row off the structural route. -/
def reapGate (rp : Transition → Bool) (net : FlatNet) : Bool := net.all fun ft => !rp ft.1

/-- **The gate refuses the witness** of `structural_proven_is_untimed_only`: its one row is the
`window(3, 5)` transition, which `flatten_with_reapable` marks reapable. -/
theorem reapGate_refuses_witness : reapGate (fun t => t.name == "t") netSelf = false := by
  decide

/-- **Behind the reapable gate the structural `Proven` holds for timed runs.** With no row
reapable, no run of either backend (any schedule, `ReapAware.RestsAt`) comes to rest: a rest
would be a reachable dead marking. -/
theorem structural_proven_sound_timed {net : FlatNet} {n budget : Nat} {cut : Nat → Bool}
    {a0 : AMarking} (hord : Ordinary net) (hbelow : InputsBelow net n)
    (h : structuralCheck net n budget cut a0 = .noPotentialDeadlock)
    {tm : Transition → ReapAware.TTiming}
    (hgate : reapGate (ReapAware.reapable tm) net = true)
    {enforce : Nat → Nat → Cell → Cell} {a : AMarking}
    (hrest : ReapAware.RestsAt enforce tm net a0 a) : False := by
  obtain ⟨hr, hq⟩ := ReapAware.rest_sound hrest
  have hnr : ∀ ft ∈ net, ReapAware.reapable tm ft.1 = false := fun ft hft => by
    unfold reapGate at hgate
    rw [List.all_eq_true] at hgate
    simpa using hgate ft hft
  have hdead := (ReapAware.reap_quiescent_iff_quiescent hnr a).mp hq
  exact structural_proven_sound hord hbelow h hr hdead

end Libpetri.Novel.SiphonSearch
