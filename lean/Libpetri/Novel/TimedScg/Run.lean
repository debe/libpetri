import Libpetri.Novel.TimedScg.Succ
import Libpetri.Novel.Enumeration

/-!
# Timed runs stay in the graph, and the persistence rule ([VER-010], [VER-023], [TIME-012])

* `timed_run_sound`: every state of a timed run (`TReach`) lies in a class reachable from the
  initial class along `succList`, by induction over the run with `delay_sound` and
  `successor_sound`.
* `timed_markings_discovered`: composed with `Enumeration.run_complete_iff_reach`, a **closed**
  graph (`complete = true`) holds a class for every marking a timed run visits. A property
  whose bad predicate holds of no discovered class therefore holds of every timed run: the
  claim `SPURIOUS_UNDER_TIMING` makes ([VER-023]), in the Time Petri net semantics `TStep`, for an
  executor that is never late (`Late.lean` for one that is). The `TIMED_CONFIRMED` direction
  (a violating class is realised by a run) is not proven.
* The persistence rule. `graph_persistent_iff`: the clocks `compute_successor` keeps are the
  clocks `TStep` keeps. This holds by construction, since `TStep`'s `persists` is built from the
  graph's own `survives` test; it says nothing about the executor's [TIME-012] implementation
  (premise 9 of `Succ.lean`). `persistence_rule` unfolds that rule; `fired_never_persists`,
  `inhibitor_never_restarts`, `reset_restarts` and `surplus_keeps` are the bullets of
  [TIME-012] (the fired transition restarts; removing tokens never disables through an
  inhibitor; a reset drains a place, so everything that consumes or reads it restarts; a place
  that still satisfies the transition in the intermediate marking keeps its clock).
-/

namespace Libpetri.Novel.TimedScg

open Libpetri Libpetri.Novel.ForwardDeposit
open Libpetri.Novel.Dbm (Bound)

variable {N : TNet} {co : List Nat → Option (List Nat)} {eps : ℚ}

/-- The graph's edge relation. -/
def Edge (N : TNet) (co : List Nat → Option (List Nat)) (eps : ℚ) (C C' : Cls) : Prop :=
  C' ∈ succList N co eps C

theorem succ_mem_succList {C C' : Cls} {k : Nat} {d : Deposit} (hk : k < C.cs.length)
    (hd : d ∈ rowsOf N (C.cs.getD k 0)) (h : succ N co eps C k d = some C') :
    C' ∈ succList N co eps C := by
  simp only [succList, succListWith, List.mem_flatMap, List.mem_range, List.mem_filterMap]
  exact ⟨k, hk, d, hd, h⟩

theorem urgent_s0 (hT : TimingWF N) (m0 : AMarking) : Urgent N (s0 m0) :=
  fun i _ => lft_nonneg hT i

/-- **Timed runs stay in the graph.** Every state of a timed run lies in a well-formed class
the graph reaches from its initial class. -/
theorem timed_run_sound (hT : TimingWF N) (hco : CoWF co) (heps : 0 ≤ eps) {m0 : AMarking}
    {C0 : Cls} (h0 : initCls N co eps m0 = some C0) {s : TState} (hs : TReach N m0 s) :
    ∃ C, Relation.ReflTransGen (Edge N co eps) C0 C ∧ InCls N s C ∧ ClsWF N C ∧ Urgent N s := by
  induction hs with
  | refl =>
    obtain ⟨C, hC, hin, hwf⟩ := init_sound hT hco heps m0
    rw [h0] at hC
    cases hC
    exact ⟨C0, Relation.ReflTransGen.refl, hin, hwf, urgent_s0 hT m0⟩
  | tail _ hstep ih =>
    obtain ⟨C, hreach, hin, hwf, hu⟩ := ih
    cases hstep with
    | delay δ hδ hurg =>
      exact ⟨C, hreach, delay_sound hwf hin hδ, hwf, hurg⟩
    | fire f d hen hready hd =>
      have hfC : f ∈ C.cs := (hwf.mem f).mpr (hin.1 ▸ hen)
      obtain ⟨k, hk, hkf⟩ := List.getElem_of_mem hfC
      have hk' : C.cs[k]? = some f := by rw [List.getElem?_eq_getElem hk, hkf]
      obtain ⟨C', hsucc, hin', hwf', hu'⟩ :=
        successor_sound hT hco heps hwf hin hu hen hready hk'
      have hgd : C.cs.getD k 0 = f := by
        simp only [List.getD_eq_getElem?_getD, hk', Option.getD_some]
      exact ⟨C', Relation.ReflTransGen.tail hreach
        (succ_mem_succList hk (by rw [hgd]; exact hd) hsucc), hin', hwf', hu'⟩

open Classical in
/-- **A closed timed graph holds every marking a timed run visits** ([VER-023]
`SPURIOUS_UNDER_TIMING`, [VER-010] AC1), under the class-identity premise (dedup by `Cls`
equality, `Enumeration.build`). -/
theorem timed_markings_discovered (hT : TimingWF N) (hco : CoWF co) (heps : 0 ≤ eps)
    {m0 : AMarking} {C0 : Cls} (h0 : initCls N co eps m0 = some C0) {maxClasses fuel : Nat}
    (hclosed : (Enumeration.build (succList N co eps) maxClasses fuel C0).2 = true)
    {s : TState} (hs : TReach N m0 s) :
    ∃ C ∈ (Enumeration.build (succList N co eps) maxClasses fuel C0).1, C.m = s.m ∧ InCls N s C := by
  obtain ⟨C, hreach, hin, -, -⟩ := timed_run_sound hT hco heps h0 hs
  exact ⟨C, (Enumeration.run_complete_iff_reach hclosed C).mpr hreach, hin.1.symm, hin⟩

open Classical in
/-- Corollary: a bad predicate of the marking that no discovered class of a closed graph
satisfies holds of no timed run. -/
theorem timed_safety_of_closed (hT : TimingWF N) (hco : CoWF co) (heps : 0 ≤ eps)
    {m0 : AMarking} {C0 : Cls} (h0 : initCls N co eps m0 = some C0) {maxClasses fuel : Nat}
    (hclosed : (Enumeration.build (succList N co eps) maxClasses fuel C0).2 = true)
    (bad : AMarking → Prop)
    (hgood : ∀ C ∈ (Enumeration.build (succList N co eps) maxClasses fuel C0).1, ¬ bad C.m)
    {s : TState} (hs : TReach N m0 s) : ¬ bad s.m := by
  obtain ⟨C, hC, hm, -⟩ := timed_markings_discovered hT hco heps h0 hclosed hs
  rw [← hm]
  exact hgood C hC

/-! ## The persistence rule ([TIME-012], [VER-010] AC4) -/

/-- **The persistence rule.** A transition keeps its clock across the firing of `f` with row
`d` iff it was enabled before, is not `f`, and is enabled both in the successor and in the
intermediate marking `M - Pre(f)` (inputs consumed, resets drained, nothing deposited). -/
theorem persistence_rule (m : AMarking) (f : Nat) (d : Deposit) (i : Nat) :
    persists N m f d i = true ↔
      en N m i = true ∧ i ≠ f ∧ en N (fireAD m (trOf N f) d) i = true ∧
        en N (inter m (trOf N f)) i = true := by
  simp only [persists, survives, Bool.and_eq_true, bne_iff_ne, ne_eq]
  tauto

/-- **The graph keeps exactly the semantics' clocks.** In a well-formed class, the clock list of
`compute_successor`'s persistent part is the set of transitions `persists` keeps. By
construction (`persists` uses `survives`); not a statement about the executor. -/
theorem graph_persistent_iff {C : Cls} (hC : ClsWF N C) {f : Nat} {d : Deposit} (c : Nat) :
    c ∈ (persPos (survives N) C f (fireAD C.m (trOf N f) d) (inter C.m (trOf N f))).map
        (fun i => C.cs.getD i 0) ↔ persists N C.m f d c = true := by
  rw [mem_pers_iff]
  simp only [persists, Bool.and_eq_true]
  exact and_congr_left' (hC.mem c)

/-- The fired transition always restarts. -/
theorem fired_never_persists (m : AMarking) (f : Nat) (d : Deposit) : persists N m f d f = false := by
  simp [persists, survives]

/-- Removing tokens never disables through an inhibitor: a transition enabled before whose
inputs and reads still hold in the intermediate marking is enabled there. -/
theorem inhibitor_never_restarts {m : AMarking} {t : Transition} {c : Nat}
    (hen : en N m c = true)
    (hin : ∀ s ∈ (trOf N c).inputs, s.card.required ≤ inter m t s.place)
    (hrd : ∀ p ∈ (trOf N c).reads, 1 ≤ inter m t p) : en N (inter m t) c = true := by
  have hc := en_lt hen
  rw [en_eq hc] at hen ⊢
  unfold enabledA at hen ⊢
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at hen ⊢
  refine ⟨⟨hin, fun p hp => ?_⟩, hrd⟩
  have h0 := hen.1.2 p hp
  have := inter_le m t p
  omega

/-- A reset arc drains its place, so a transition that consumes (with a positive requirement) or
reads from a place the fired transition resets restarts ([TIME-012] AC3). -/
theorem reset_restarts {m : AMarking} {f : Nat} {d : Deposit} {c p : Nat}
    (hreset : (trOf N f).resets.contains p = true)
    (huse : (∃ s ∈ (trOf N c).inputs, s.place = p ∧ 1 ≤ s.card.required) ∨ p ∈ (trOf N c).reads) :
    persists N m f d c = false := by
  cases hp : persists N m f d c
  · rfl
  exfalso
  obtain ⟨-, -, -, hmid⟩ := (persistence_rule m f d c).mp hp
  have hc := en_lt hmid
  rw [en_eq hc] at hmid
  unfold enabledA at hmid
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hmid
  have hz : inter m (trOf N f) p = 0 := by unfold inter; rw [if_pos hreset]
  rcases huse with ⟨s, hs, rfl, hreq⟩ | hrd
  · have := hmid.1.1 s hs
    omega
  · have := hmid.2 p hrd
    omega

/-- Surplus tokens keep the clock ([TIME-012] AC4): enabled before, in the intermediate
marking and after, and not the fired transition. -/
theorem surplus_keeps {m : AMarking} {f : Nat} {d : Deposit} {c : Nat} (hen : en N m c = true)
    (hne : c ≠ f) (hmid : en N (inter m (trOf N f)) c = true)
    (hafter : en N (fireAD m (trOf N f) d) c = true) : persists N m f d c = true :=
  (persistence_rule m f d c).mpr ⟨hen, hne, hafter, hmid⟩

end Libpetri.Novel.TimedScg
