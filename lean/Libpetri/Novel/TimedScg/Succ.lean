import Libpetri.Novel.TimedScg.Zone
import Libpetri.Novel.ForwardDeposit
import Mathlib.Logic.Relation
import Mathlib.Order.Interval.Finset.Nat

/-!
# The timed state-class successor ([VER-010], [VER-011], [TIME-011], [TIME-012])

Model of `state_class_graph.rs::compute_successor` on the timed path (`untimed = false`), of
`initial_state_class`, and of the loop of `build_core` (behind `build_with_options`) that lists a class's successors
(`state_class_graph.rs:186-247`), with no environment places (`env_places = []`, `Ignore`).

## The model

* A timed net `TNet` is a list of `TTrans`: the structural core of `Basic.lean` (`Transition`),
  its outcome rows (`branch_outcomes::outcomes`, the rows `expand_transition` enumerates; one
  `ForwardDeposit.Deposit` each), and its static interval `[eft, lft]` in seconds. The
  intervals are data here; `Timing.lean` says which ones the Rust produces:
  `clock_timing(t).earliest() / 1000` and `latest() / 1000`, where `latest()` is the **finite**
  `MAX_DURATION_MS` for `immediate` and `delayed` (never `f64::INFINITY`), so `lft` is never `⊤`
  in the faithful instantiation (`Timing.lftT_ne_top`). `⊤` is allowed by the model and used by
  `Late.relax`. A transition is its index in the list.
* A marking is an `AMarking`; enablement is `Basic.enabledA` (`is_enabled`,
  `state_class_graph.rs:435-457`); firing a row is `ForwardDeposit.fireAD`; the intermediate
  marking `inter` is `consume_marking` (`state_class_graph.rs:662-692`): inputs taken by
  `consumptionCount`, reset places drained, nothing deposited. `fireAD_eq_inter_add`: the
  successor marking is the intermediate one plus the deposit, which is `produce_marking` for a
  constant row.
* A class `Cls` is the marking, the clock list `cs` (`enabled_transitions`) and the positional
  firing domain `D` of dimension `cs.length + 1` (`Dbm.data`, `Zone.lean`).
* `succWith surv` is `compute_successor` with the survival test `surv` as a parameter:
  `survives` (`c ≠ f`, enabled after, enabled in the intermediate marking: the current rule,
  in `compute_successor_gated`, `state_class_graph.rs:519-547`) and `survivesOld` (no
  intermediate test: the rule before 6.0.0, see `Retrodict.lean`). `succ := succWith survives`.
  `compute_successor` is `compute_successor_gated` with both gates `|_| true`, and that is the
  only form modelled here. Route B's name layer passes `name_enabled` as the gates (a ν-join
  holds a clock only while one name is in every correlated input, [NU-020]); that gated form
  filters both the persistent and the newly enabled clocks by the gate and is not modelled.
* `TStep` is the Time Petri net semantics the graph is meant to over-approximate (Merlin,
  strong urgency, the clock rule of [TIME-011] / [TIME-012]): a state is a marking and one clock
  per transition (`ν`, the time since it was last newly enabled); time may pass while no enabled
  transition overruns its `lft`; an enabled transition fires once its clock reaches `eft`; after
  a firing, a transition keeps its clock iff it was enabled before, is not the fired one, and is
  enabled in the intermediate and in the successor marking (`persists`); every other clock is
  reset to `0`. `persists` is built from the same `survives` test the graph uses, so the
  semantics' clock rule is the graph's **by construction**; that it is also the executor's is
  premise 9, not a theorem.

## Results

* `successor_sound`: a state in a class that fires `f` with row `d` (after any delay) lands in
  the successor class `succ C k d`, which is therefore **not dropped** (`some`), and the
  successor is a well-formed class again. `delay_sound`: letting time pass keeps a state in its
  class; this means something only for a delay `TStep.delay` allows (no enabled clock past its
  `lft`, `Urgent`): past a clock's `lft` the box of possible times-to-fire is empty and
  `InCls` holds vacuously. `init_sound`: the initial state is in the initial class.
* `Run.timed_run_sound`: every state of every timed run lies in a class the graph reaches from
  the initial class, and `Run.timed_markings_discovered` composes it with
  `Enumeration.run_complete_iff_reach`: on a closed graph every marking a timed run visits is the
  marking of a discovered class. This is the `SPURIOUS_UNDER_TIMING` half of [VER-023]. The
  `TIMED_CONFIRMED` half (every class and path is realised by a timed run) is **not** proven.
* `mem_pers_iff` / `Run.graph_persistent_iff` / `Run.persistence_rule`: the clocks the graph
  keeps are the clocks `persists` keeps (true by construction, see above), and
  `fired_never_persists`, `inhibitor_never_restarts`, `reset_restarts`, `surplus_keeps` are the
  bullets of [TIME-012] for that rule.
* `Progress.succ_exists` / `Progress.reachable_quiescent_iff_dead`: a class with a solution and
  an enabled transition has a successor whatever the intervals ([VER-023], "a class with an
  enabled transition has a successor"), so "no successor" means "nothing enabled"; every class
  the graph stores has a solution at `eps = 0` (`Progress.nonempty_of_not_flagged`), and at the
  Rust `EPSILON = 1e-9` on a millisecond-grid net (`Progress.faithful_quiescent_iff_dead`).
* `Late.late_run_sound` / `Late.late_quiescence_sound`: what bounds an executor that falls
  behind and reaps deadlines (see there).

## Premises assumed about the Rust (not proven)

1. **Names.** Transition names are unique, so a name lookup (`find(|t| t.name() == name)`) is
   the transition with that index, and `c ≠ fired_name` is `c ≠ f`.
2. **One input arc per place** (`Basic.InputsDistinctPlaces`): `consume_marking` sets each input
   place from the original count, so two specs on one place would not sum.
3. **Constant rows.** Every row of `outcomes` is a constant deposit (`ForwardDeposit.FixedForwards`;
   a forward of a drained batch, which `produce_marking` computes from the marking, is out of
   scope), and every transition of the net has at least one row (`outcomes` of a transition
   with no output spec is one empty row); needed only for the quiescence theorems.
4. **Exact arithmetic.** Bounds are rationals; `f64` rounding is not modelled. The emptiness flag
   uses `eps ≥ 0` (Rust `EPSILON = 1e-9`); soundness holds for every such `eps`. Quiescence is
   proven at `eps = 0`, and at every `eps` below the grid step of a grid net (`Grid.lean`), which
   covers `1e-9` for every net built from `Timing`s.
5. **Canonical order.** `canonical_order` returns a permutation of the clock positions or `None`
   for the identity (`CoWF`); which permutation is irrelevant to every result here.
6. **Well-formed timing** (`TimingWF`): `0 ≤ eft ≤ lft` for every transition. It holds for
   every net built from Rust `Timing`s the shipped constructors accept
   (`Timing.timingWF_of_valid_timings`): `delayed`, `window` and `exact` reject an earliest bound
   above `MAX_DURATION_MS`. Before that check a `delayed(after > MAX_DURATION_MS)` broke it and
   escaped the graph (`Retrodict.delayed_past_max_escapes`).
7. **Class identity.** The graph dedups by `canonical_key` (marking key, clock names, the full
   matrix rendered). `timed_markings_discovered` reads that as equality of `Cls`, which holds
   when the key renders exact rationals injectively (entries outside `dim × dim` are never read
   by the key, and every class this file builds has `0` / `⊤` there).
8. **No environment places** and no ν-match transitions (the timed check runs only then, [VER-023]
   conditions 2 and 3).
9. **The executor's clock rule is `persists`.** [TIME-012] as the executor implements it is
   spread over `update_bitmap_after_consumption` (the restart walk runs only for a place left
   below `CompiledNet::restart_threshold`, which is `0`, so no walk, for a place with one
   undrained requirer), `flag_clock_restarts` (judged by `can_enable` on the **live** marking,
   same-pass sync deposits included) and `update_enablement` (a flagged restart applies only if
   the transition is still enabled at the next update). No file of `TimedScg/` models that
   chain, so a correspondence to `TStep` is assumed, not proven. `MAX_DURATION_MS` read as `⊤`
   for an unbounded timing is likewise assumed (`Timing.lean`).

## Divergences from the executor

The theorems are about `TStep`. These executor behaviours fall outside it, so a closed timed
graph (`SPURIOUS_UNDER_TIMING`, [VER-023]; Route B's `TIMED_EXACT`) does not bound them:

* **Lateness and deadline reaping ([TIME-013]).** `TStep` blocks time at `lft`; the executor
  cannot stop time. A late executor fires a `Deadline` / `Window` transition anywhere in
  `(lft, lft + tolerance]`, reaps it past `lft + tolerance`, fires an `exact()` transition after
  its `lft` (enforced softly, never reaped, [TIME-006]), and fires an `immediate` / `delayed` one
  whenever. Witness `Retrodict.reaping_escapes_timed_graph` (Lean) and the Rust test
  `untimed_exploration_reaches_a_marking_the_timing_excludes`. `Late.lean` models the late
  executor (`LateStep`, tolerance and soft `exact` included) and proves that the graph of the
  net with its upper bounds dropped covers it, and where it may rest. Route B builds that
  relaxed graph (`reaping::relax_late`) unless the caller assumes an on-time executor.
* **Action duration.** The graph deposits a firing's outputs at the instant it fires; an action
  that takes time deposits later, so a transition inhibited by an output can fire in between.
  Witness `Retrodict.action_duration_escapes` (Lean only; no Rust test). [VER-010] AC4 names only
  the overlapping-actions half; one asynchronous action is enough.
* **`delayed(after > MAX_DURATION_MS)`** (fixed). Premise 6 failed
  (`Retrodict.delayed_past_max_escapes`); the constructors now reject it (`Retrodict.lean` §5).
* **Name-disabled ν-joins (Route B, fixed).** `name_state_class_graph.rs` used
  `compute_successor` for its base layer, whose clock list is the count-enabled set: a join whose
  inputs shared no name kept a clock and its deadline, which the executor does not have. It now
  calls `compute_successor_gated` with `name_enabled` as the gates. The Lean witness
  `Retrodict.name_disabled_join_escapes` (model level, plain graph, a `blocked` predicate)
  describes the old behaviour (`Retrodict.lean` §3).
-/

namespace Libpetri.Novel.TimedScg

open Libpetri Libpetri.Novel.ForwardDeposit
open Libpetri.Novel.Dbm (Bound)

/-! ## List helpers -/

section Lists

variable {α : Type}

theorem getD_mem {l : List α} {i : Nat} (x : α) (h : i < l.length) : l.getD i x ∈ l := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

theorem getD_irrel {l : List α} {i : Nat} (x y : α) (h : i < l.length) : l.getD i x = l.getD i y := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem getD_map {β : Type} {l : List α} {i : Nat} (g : α → β) (x : α) (y : β)
    (h : i < l.length) : (l.map g).getD i y = g (l.getD i x) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h,
    Option.map_some, Option.getD_some]

theorem getD_append_left {l₁ l₂ : List α} {i : Nat} (x : α) (h : i < l₁.length) :
    (l₁ ++ l₂).getD i x = l₁.getD i x := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right {l₁ l₂ : List α} {i : Nat} (x : α) (h : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i x = l₂.getD (i - l₁.length) x := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem contains_false_iff {l : List Nat} {c : Nat} : l.contains c = false ↔ c ∉ l := by
  rw [← Bool.not_eq_true, List.contains_iff_mem]

theorem mem_iff_getD {l : List α} {c : α} (x : α) : c ∈ l ↔ ∃ i, i < l.length ∧ l.getD i x = c := by
  constructor
  · intro h
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
    exact ⟨i, hi, by simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some]⟩
  · rintro ⟨i, hi, rfl⟩
    exact getD_mem x hi

end Lists

/-! ## Timed nets -/

/-- A timed transition: the structural core, its outcome rows, and its static interval. -/
structure TTrans where
  tr   : Transition
  rows : List Deposit
  eft  : ℚ
  lft  : Bound

abbrev TNet := List TTrans

/-- The empty transition, for an index outside the net. -/
def noTr : Transition := { name := "", inputs := [], inhibitors := [], reads := [], resets := [] }

def trOf (N : TNet) (i : Nat) : Transition := match N[i]? with | some x => x.tr | none => noTr
def rowsOf (N : TNet) (i : Nat) : List Deposit := match N[i]? with | some x => x.rows | none => []
def eftOf (N : TNet) (i : Nat) : ℚ := match N[i]? with | some x => x.eft | none => 0
def lftOf (N : TNet) (i : Nat) : Bound := match N[i]? with | some x => x.lft | none => ⊤

/-- `is_enabled` (no environment places). An index outside the net is never enabled. -/
def en (N : TNet) (a : AMarking) (i : Nat) : Bool :=
  match N[i]? with | some x => enabledA a x.tr | none => false

/-- `find_enabled_transitions`: the enabled transitions in net order. -/
def enabledIds (N : TNet) (a : AMarking) : List Nat := (List.range N.length).filter (en N a)

theorem en_lt {N : TNet} {a : AMarking} {i : Nat} (h : en N a i = true) : i < N.length := by
  unfold en at h
  cases hi : N[i]? with
  | none => rw [hi] at h; exact absurd h (by simp)
  | some x => exact (List.getElem?_eq_some_iff.mp hi).1

theorem en_eq {N : TNet} {a : AMarking} {i : Nat} (h : i < N.length) :
    en N a i = enabledA a (trOf N i) := by
  simp only [en, trOf, List.getElem?_eq_getElem h]

theorem mem_enabledIds {N : TNet} {a : AMarking} {i : Nat} : i ∈ enabledIds N a ↔ en N a i = true := by
  simp only [enabledIds, List.mem_filter, List.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨en_lt h, h⟩⟩

/-- `0 ≤ eft ≤ lft` for every transition (premise 6). -/
def TimingWF (N : TNet) : Prop := ∀ i, 0 ≤ eftOf N i ∧ ((eftOf N i : ℚ) : Bound) ≤ lftOf N i

theorem lft_nonneg {N : TNet} (h : TimingWF N) (i : Nat) : ((0 : ℚ) : Bound) ≤ lftOf N i :=
  (WithTop.coe_le_coe.mpr (h i).1).trans (h i).2

/-! ## The intermediate marking -/

/-- `consume_marking`: inputs taken (`consumptionCount`: all of a consume-all place, `pre`
otherwise), reset places drained, nothing deposited. -/
def inter (a : AMarking) (t : Transition) : AMarking := fun p =>
  if t.resets.contains p then 0 else if consumeAllAt t p then 0 else a p - pre t p

/-- The successor marking is the intermediate marking plus the deposit (`produce_marking`). -/
theorem fireAD_eq_inter_add (a : AMarking) (t : Transition) (d : Deposit) (p : PlaceId) :
    fireAD a t d p = inter a t p + d.count p := by
  unfold fireAD inter
  split_ifs <;> omega

theorem inter_le (a : AMarking) (t : Transition) (p : PlaceId) : inter a t p ≤ a p := by
  unfold inter
  split_ifs <;> omega

/-! ## Classes and the successor -/

/-- A state class: marking, clock list (`enabled_transitions`), positional firing domain. -/
structure Cls where
  m  : AMarking
  cs : List Nat
  D  : NMat

/-- The survival test of the current rule (`state_class_graph.rs:490-514`, since 6.0.0): not
the fired transition, enabled after, enabled in the intermediate marking. -/
def survives (N : TNet) (f : Nat) (a' mid : AMarking) (c : Nat) : Bool :=
  c != f && en N a' c && en N mid c

/-- The clock positions that keep their clock: `persistent_indices`, in clock order. -/
def persPos (surv : Nat → AMarking → AMarking → Nat → Bool) (C : Cls) (f : Nat) (a' mid : AMarking) :
    List Nat :=
  (List.range C.cs.length).filter fun i => surv f a' mid (C.cs.getD i 0)

/-- The zone half of the successor: `fire_transition` (steps 1–5 and its final
`canonicalize`). `none` when a `canonicalize` raises the empty flag. -/
def zoneStep (eps : ℚ) (n k : Nat) (D : NMat) (ps : List Nat) (lb : List ℚ) (ub : List Bound) :
    Option NMat :=
  if FlaggedN eps (n + 1) (constrainPre n k D) then none
  else if FlaggedN eps (ps.length + lb.length + 1)
      (fireMat (canonN (n + 1) (constrainPre n k D)) k ps lb ub) then none
  else some (canonN (ps.length + lb.length + 1)
    (fireMat (canonN (n + 1) (constrainPre n k D)) k ps lb ub))

/-- `canonical_order` applied to the clock list: `None` keeps it. -/
def reorder (co : List Nat → Option (List Nat)) (all : List Nat) : List Nat :=
  match co all with | none => all | some ord => ord.map fun i => all.getD i 0

/-- `permuted` applied to the zone with the same order. -/
def reorderMat (co : List Nat → Option (List Nat)) (all : List Nat) (Y : NMat) : NMat :=
  match co all with | none => Y | some ord => permMat ord Y

/-- The tail of `compute_successor`: canonical order, `let_time_pass`, the `is_empty` drop. -/
def finish (eps : ℚ) (co : List Nat → Option (List Nat)) (a' : AMarking) (all : List Nat)
    (Y : NMat) : Option Cls :=
  if FlaggedN eps (all.length + 1) (ltpPre (all.length + 1) (reorderMat co all Y)) then none
  else some ⟨a', reorder co all, canonN (all.length + 1) (ltpPre (all.length + 1) (reorderMat co all Y))⟩

/-- **`compute_successor`** for the clock at position `k` and the row `d`, with survival test
`surv`. -/
def succWith (surv : Nat → AMarking → AMarking → Nat → Bool) (N : TNet)
    (co : List Nat → Option (List Nat)) (eps : ℚ) (C : Cls) (k : Nat) (d : Deposit) :
    Option Cls :=
  match C.cs[k]? with
  | none => none
  | some f =>
    let a' := fireAD C.m (trOf N f) d
    let mid := inter C.m (trOf N f)
    let ps := persPos surv C f a' mid
    let pers := ps.map fun i => C.cs.getD i 0
    let newly := (enabledIds N a').filter fun j => !pers.contains j
    (zoneStep eps C.cs.length k C.D ps (newly.map (eftOf N)) (newly.map (lftOf N))).bind
      (finish eps co a' (pers ++ newly))

/-- The current successor. -/
def succ (N : TNet) := succWith (survives N) N

/-- The successors of a class in the Rust order: clocks in class order, rows in `outcomes`
order (`state_class_graph.rs:186-247`), dropped ones left out. -/
def succListWith (surv : Nat → AMarking → AMarking → Nat → Bool) (N : TNet)
    (co : List Nat → Option (List Nat)) (eps : ℚ) (C : Cls) : List Cls :=
  (List.range C.cs.length).flatMap fun k =>
    (rowsOf N (C.cs.getD k 0)).filterMap (succWith surv N co eps C k)

def succList (N : TNet) := succListWith (survives N) N

/-- `initial_state_class`: canonical order, `create`, `let_time_pass`. `none` when a
`canonicalize` flags the zone empty. The Rust keeps such a class, with no successors, so its
graph closes after one class; under `TimingWF` it never happens (`init_sound`), but the Rust
does not guarantee `TimingWF`: `delayed(after > MAX_DURATION_MS)` breaks it
(`Retrodict.netBig_initCls_none`). -/
def initCls (N : TNet) (co : List Nat → Option (List Nat)) (eps : ℚ) (m0 : AMarking) :
    Option Cls :=
  let cs0 := reorder co (enabledIds N m0)
  let B := createPre cs0.length (cs0.map (eftOf N)) (cs0.map (lftOf N))
  if FlaggedN eps (cs0.length + 1) B then none
  else if FlaggedN eps (cs0.length + 1) (ltpPre (cs0.length + 1) (canonN (cs0.length + 1) B))
    then none
  else some ⟨m0, cs0, canonN (cs0.length + 1) (ltpPre (cs0.length + 1) (canonN (cs0.length + 1) B))⟩

/-- `canonical_order` returns a permutation of the positions (premise 5). -/
def CoWF (co : List Nat → Option (List Nat)) : Prop :=
  ∀ l ord, co l = some ord →
    ord.length = l.length ∧ (∀ x ∈ ord, x < l.length) ∧ ∀ i, i < l.length → i ∈ ord

theorem reorder_length {co : List Nat → Option (List Nat)} (hco : CoWF co) (l : List Nat) :
    (reorder co l).length = l.length := by
  unfold reorder
  cases h : co l with
  | none => rfl
  | some ord => simp only [List.length_map]; exact (hco l ord h).1

theorem mem_reorder {co : List Nat → Option (List Nat)} (hco : CoWF co) (l : List Nat) (c : Nat) :
    c ∈ reorder co l ↔ c ∈ l := by
  unfold reorder
  cases h : co l with
  | none => rfl
  | some ord =>
    obtain ⟨-, hlt, hall⟩ := hco l ord h
    simp only [List.mem_map]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact getD_mem 0 (hlt i hi)
    · intro hc
      obtain ⟨i, hi, rfl⟩ := (mem_iff_getD 0).mp hc
      exact ⟨i, hall i hi, rfl⟩

/-! ## The timed semantics -/

/-- A timed state: a marking and a clock per transition. -/
structure TState where
  m : AMarking
  ν : Nat → ℚ

/-- The clock rule of [TIME-011] / [TIME-012]: `i` keeps its clock across the firing of `f`
with row `d` iff it was enabled, is not `f`, and is enabled in the intermediate and in the
successor marking. Defined from the graph's own `survives`; that the executor follows it is
premise 9. -/
def persists (N : TNet) (m : AMarking) (f : Nat) (d : Deposit) (i : Nat) : Bool :=
  en N m i && survives N f (fireAD m (trOf N f) d) (inter m (trOf N f)) i

/-- One step of the Time Petri net semantics (strong urgency). -/
inductive TStep (N : TNet) : TState → TState → Prop
  | delay (s : TState) (δ : ℚ) (hδ : 0 ≤ δ)
      (hurg : ∀ i, en N s.m i = true → ((s.ν i + δ : ℚ) : Bound) ≤ lftOf N i) :
      TStep N s ⟨s.m, fun i => s.ν i + δ⟩
  | fire (s : TState) (f : Nat) (d : Deposit) (hen : en N s.m f = true)
      (hready : eftOf N f ≤ s.ν f) (hd : d ∈ rowsOf N f) :
      TStep N s ⟨fireAD s.m (trOf N f) d, fun i => if persists N s.m f d i then s.ν i else 0⟩

/-- The initial state: every clock at `0`. -/
def s0 (m0 : AMarking) : TState := ⟨m0, fun _ => 0⟩

/-- The states of the timed runs from `m0`. -/
def TReach (N : TNet) (m0 : AMarking) : TState → Prop := Relation.ReflTransGen (TStep N) (s0 m0)

/-- No enabled clock has overrun its latest firing time. -/
def Urgent (N : TNet) (s : TState) : Prop :=
  ∀ i, en N s.m i = true → ((s.ν i : ℚ) : Bound) ≤ lftOf N i

/-- `x` is a possible time-to-fire of `c` in clock state `ν`. -/
def BoxAt (N : TNet) (ν : Nat → ℚ) (c : Nat) (x : ℚ) : Prop :=
  0 ≤ x ∧ eftOf N c ≤ x + ν c ∧ ((x + ν c : ℚ) : Bound) ≤ lftOf N c

/-- A named valuation laid out along a clock list, the reference at `0`. -/
def posOf (cs : List Nat) (ϑ : Nat → ℚ) : Nat → ℚ := fun a => if a = 0 then 0 else ϑ (cs.getD (a - 1) 0)

/-- **Class membership.** The state's marking is the class marking, and every combination of
possible times-to-fire of the enabled transitions is a point of the class's zone. -/
def InCls (N : TNet) (s : TState) (C : Cls) : Prop :=
  s.m = C.m ∧ ∀ ϑ : Nat → ℚ, (∀ c ∈ C.cs, BoxAt N s.ν c (ϑ c)) →
    SatN (C.cs.length + 1) C.D (posOf C.cs ϑ)

/-- A well-formed class: its clocks are the enabled transitions, and its zone is a
let-time-pass zone whose reference entry is finite. -/
structure ClsWF (N : TNet) (C : Cls) : Prop where
  mem  : ∀ c, c ∈ C.cs ↔ en N C.m c = true
  down : ∃ Y : NMat, C.D = canonN (C.cs.length + 1) (ltpPre (C.cs.length + 1) Y) ∧ Y 0 0 ≠ ⊤

/-! ## Basic facts -/

theorem posOf_zero (cs : List Nat) (ϑ : Nat → ℚ) : posOf cs ϑ 0 = 0 := rfl

theorem posOf_succ (cs : List Nat) (ϑ : Nat → ℚ) (i : Nat) : posOf cs ϑ (i + 1) = ϑ (cs.getD i 0) := by
  simp [posOf]

theorem box_nonempty {N : TNet} (hT : TimingWF N) {ν : Nat → ℚ} {c : Nat}
    (hc : ((ν c : ℚ) : Bound) ≤ lftOf N c) : BoxAt N ν c (max 0 (eftOf N c - ν c)) := by
  refine ⟨le_max_left _ _, ?_, ?_⟩
  · have := le_max_right 0 (eftOf N c - ν c)
    linarith
  · rcases le_total 0 (eftOf N c - ν c) with h | h
    · rw [max_eq_right h, sub_add_cancel]
      exact (hT c).2
    · rw [max_eq_left h, zero_add]
      exact hc

theorem box_nonneg {N : TNet} {ν : Nat → ℚ} {c : Nat} {x : ℚ} (h : BoxAt N ν c x) : 0 ≤ x := h.1

/-- The valuation laid out along a class's clocks is never behind the reference. -/
theorem posOf_pos {N : TNet} {ν : Nat → ℚ} {cs : List Nat} {ϑ : Nat → ℚ}
    (h : ∀ c ∈ cs, BoxAt N ν c (ϑ c)) : ∀ j, 1 ≤ j → j < cs.length + 1 → posOf cs ϑ 0 ≤ posOf cs ϑ j := by
  intro j hj1 hjd
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [posOf_zero, posOf_succ]
  exact (h _ (getD_mem 0 (by omega))).1

/-! ## Delay -/

/-- **Letting time pass keeps a state in its class.** Meaningful together with `Urgent` after
the delay, which `TStep.delay` supplies (`hurg`) and this statement does not require: once a
clock is past its `lft`, `BoxAt` is empty for it and `InCls` holds vacuously. -/
theorem delay_sound {N : TNet} {C : Cls} (hC : ClsWF N C) {s : TState} (hs : InCls N s C)
    {δ : ℚ} (hδ : 0 ≤ δ) : InCls N ⟨s.m, fun i => s.ν i + δ⟩ C := by
  refine ⟨hs.1, fun ϑ'' hbox => ?_⟩
  obtain ⟨Y, hD, -⟩ := hC.down
  let ϑ : Nat → ℚ := fun c => ϑ'' c + δ
  have hbox' : ∀ c ∈ C.cs, BoxAt N s.ν c (ϑ c) := by
    intro c hc
    obtain ⟨h0, h1, h2⟩ := hbox c hc
    refine ⟨by simp only [ϑ]; linarith, by simp only [ϑ]; linarith, ?_⟩
    have e : ϑ c + s.ν c = ϑ'' c + (s.ν c + δ) := by simp only [ϑ]; ring
    rw [e]; exact h2
  have hsat := hs.2 ϑ hbox'
  rw [hD, satN_canonN] at hsat ⊢
  have e : posOf C.cs ϑ'' = shift (posOf C.cs ϑ) δ := by
    funext a
    by_cases ha : a = 0
    · simp [shift, posOf, ha]
    · simp [shift, posOf, ha, ϑ]
  rw [e]
  refine sat_ltpPre_shift hsat hδ fun j hj1 hjd => ?_
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [posOf_zero, posOf_succ]
  have := (hbox _ (getD_mem 0 (by omega : i < C.cs.length))).1
  simp only [ϑ]
  linarith

/-! ## Initial class -/

theorem initCls_eq {N : TNet} {co : List Nat → Option (List Nat)} {eps : ℚ} {m0 : AMarking}
    {C : Cls} (h : initCls N co eps m0 = some C) :
    C.m = m0 ∧ C.cs = reorder co (enabledIds N m0) ∧
      C.D = canonN (C.cs.length + 1) (ltpPre (C.cs.length + 1) (canonN (C.cs.length + 1)
        (createPre C.cs.length (C.cs.map (eftOf N)) (C.cs.map (lftOf N))))) := by
  unfold initCls at h
  simp only at h
  split_ifs at h
  cases h
  exact ⟨rfl, rfl, rfl⟩

/-- The initial box lies in the created zone. -/
theorem init_box_sat {N : TNet} {cs : List Nat} {ϑ : Nat → ℚ}
    (h : ∀ c ∈ cs, BoxAt N (fun _ => 0) c (ϑ c)) :
    SatN (cs.length + 1) (createPre cs.length (cs.map (eftOf N)) (cs.map (lftOf N))) (posOf cs ϑ) := by
  refine sat_createPre (posOf_zero _ _) (fun i hi => ?_) (fun i hi => ?_)
  · rw [getD_map (eftOf N) 0 0 hi, posOf_succ]
    have := (h _ (getD_mem 0 hi)).2.1
    simpa using this
  · rw [getD_map (lftOf N) 0 ⊤ hi, posOf_succ]
    have := (h _ (getD_mem 0 hi)).2.2
    simpa using this

/-- **The initial state is in the initial class**, which exists under `TimingWF` (premise 6). -/
theorem init_sound {N : TNet} (hT : TimingWF N) {co : List Nat → Option (List Nat)}
    (hco : CoWF co) {eps : ℚ} (heps : 0 ≤ eps) (m0 : AMarking) :
    ∃ C, initCls N co eps m0 = some C ∧ InCls N (s0 m0) C ∧ ClsWF N C := by
  set cs0 := reorder co (enabledIds N m0) with hcs0
  set B := createPre cs0.length (cs0.map (eftOf N)) (cs0.map (lftOf N)) with hB
  have hsatB : ∀ ϑ : Nat → ℚ, (∀ c ∈ cs0, BoxAt N (fun _ => 0) c (ϑ c)) →
      SatN (cs0.length + 1) (ltpPre (cs0.length + 1) (canonN (cs0.length + 1) B)) (posOf cs0 ϑ) :=
    fun ϑ hϑ => sat_ltpPre (satN_canonN.mpr (init_box_sat hϑ)) (posOf_pos hϑ)
  have hbox0 : ∀ c ∈ cs0, BoxAt N (fun _ => 0) c (eftOf N c) := fun c _ =>
    ⟨(hT c).1, by simp, by simpa using (hT c).2⟩
  have hnf1 : ¬ FlaggedN eps (cs0.length + 1) B := not_flagged_of_sat heps (init_box_sat hbox0)
  have hnf2 := not_flagged_of_sat heps (hsatB _ hbox0)
  refine ⟨⟨m0, cs0, canonN (cs0.length + 1) (ltpPre (cs0.length + 1) (canonN (cs0.length + 1) B))⟩,
    ?_, ⟨rfl, fun ϑ hϑ => satN_canonN.mpr (hsatB ϑ hϑ)⟩, ⟨?_, ?_⟩⟩
  · unfold initCls
    simp only [← hcs0, ← hB, if_neg hnf1, if_neg hnf2]
  · intro c
    show c ∈ reorder co (enabledIds N m0) ↔ _
    rw [mem_reorder hco, mem_enabledIds]
  · refine ⟨_, rfl, ne_top_of_le_ne_top (b := B 0 0) ?_ (canonN_le B (by omega) (by omega))⟩
    simp [hB, createPre]

/-! ## Firing -/

theorem mem_pers_iff {surv : Nat → AMarking → AMarking → Nat → Bool} {C : Cls} {f : Nat}
    {a' mid : AMarking} {c : Nat} :
    c ∈ (persPos surv C f a' mid).map (fun i => C.cs.getD i 0) ↔
      c ∈ C.cs ∧ surv f a' mid c = true := by
  simp only [persPos, List.mem_map, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨i, ⟨hi, hs⟩, rfl⟩
    exact ⟨getD_mem 0 hi, hs⟩
  · rintro ⟨hc, hs⟩
    obtain ⟨i, hi, rfl⟩ := (mem_iff_getD 0).mp hc
    exact ⟨i, ⟨hi, hs⟩, rfl⟩

theorem persPos_lt {surv : Nat → AMarking → AMarking → Nat → Bool} {C : Cls} {f : Nat}
    {a' mid : AMarking} : ∀ x ∈ persPos surv C f a' mid, x < C.cs.length := by
  intro x hx
  simp only [persPos, List.mem_filter, List.mem_range] at hx
  exact hx.1

/-- The tail of the successor keeps every valuation the fired zone keeps. -/
theorem finish_sound {N : TNet} {co : List Nat → Option (List Nat)} (hco : CoWF co) {eps : ℚ}
    (heps : 0 ≤ eps) {a' : AMarking} {all : List Nat} {Y : NMat} {ν' : Nat → ℚ}
    (hY : ∀ ϑ' : Nat → ℚ, (∀ c ∈ all, BoxAt N ν' c (ϑ' c)) → SatN (all.length + 1) Y (posOf all ϑ'))
    (hne : ∃ ϑ' : Nat → ℚ, ∀ c ∈ all, BoxAt N ν' c (ϑ' c)) (hY00 : Y 0 0 ≠ ⊤) :
    ∃ C', finish eps co a' all Y = some C' ∧ C'.m = a' ∧ (∀ c, c ∈ C'.cs ↔ c ∈ all) ∧
      (∀ ϑ' : Nat → ℚ, (∀ c ∈ C'.cs, BoxAt N ν' c (ϑ' c)) →
        SatN (C'.cs.length + 1) C'.D (posOf C'.cs ϑ')) ∧
      ∃ Y' : NMat, C'.D = canonN (C'.cs.length + 1) (ltpPre (C'.cs.length + 1) Y') ∧ Y' 0 0 ≠ ⊤ := by
  -- the reordered zone keeps the valuations laid out along the reordered clocks
  have hR : ∀ ϑ' : Nat → ℚ, (∀ c ∈ all, BoxAt N ν' c (ϑ' c)) →
      SatN (all.length + 1) (ltpPre (all.length + 1) (reorderMat co all Y))
        (posOf (reorder co all) ϑ') := by
    intro ϑ' hϑ
    have hpos : ∀ j, 1 ≤ j → j < all.length + 1 →
        posOf (reorder co all) ϑ' 0 ≤ posOf (reorder co all) ϑ' j := by
      have := posOf_pos (cs := reorder co all) (ϑ := ϑ') (N := N) (ν := ν')
        (fun c hc => hϑ c ((mem_reorder hco all c).mp hc))
      rwa [reorder_length hco] at this
    refine sat_ltpPre ?_ hpos
    unfold reorder reorderMat
    cases h : co all with
    | none => dsimp only; exact hY ϑ' hϑ
    | some ord =>
      obtain ⟨hlen, hlt, -⟩ := hco all ord h
      refine sat_permMat (hY ϑ' hϑ) (fun a ha => ?_) (fun a ha => ?_)
      · unfold pm
        split_ifs with h0
        · omega
        · have : a - 1 < ord.length := by omega
          have := hlt _ (getD_mem (a - 1) this)
          omega
      · dsimp only
        by_cases h0 : a = 0
        · subst h0
          simp [pm, posOf]
        · have hi : a - 1 < ord.length := by omega
          have e1 : posOf (ord.map (fun i => all.getD i 0)) ϑ' a =
              ϑ' (all.getD (ord.getD (a - 1) 0) 0) := by
            simp only [posOf, h0, if_false]
            rw [getD_map _ 0 0 hi]
          have e2 : pm ord a = ord.getD (a - 1) (a - 1) + 1 := by simp [pm, h0]
          rw [e1, e2, posOf_succ, getD_irrel (a - 1) 0 hi]
  obtain ⟨ϑ₀, hϑ₀⟩ := hne
  have hnf := not_flagged_of_sat heps (hR ϑ₀ hϑ₀)
  refine ⟨_, by unfold finish; rw [if_neg hnf], rfl, fun c => mem_reorder hco all c, ?_, ?_⟩
  · intro ϑ' hϑ
    show SatN ((reorder co all).length + 1) _ _
    rw [reorder_length hco, satN_canonN]
    exact hR ϑ' fun c hc => hϑ c ((mem_reorder hco all c).mpr hc)
  · refine ⟨reorderMat co all Y, by simp only [reorder_length hco], ?_⟩
    unfold reorderMat
    cases co all with
    | none => exact hY00
    | some ord => simp [permMat]

/-- **Successor soundness** ([VER-010] AC2, AC4). A state of class `C` in which the transition
`f` at clock position `k` is ready fires it with the row `d`; the successor class
`succ C k d` exists (the Rust keeps it: no `canonicalize` flags it), contains the state the
firing leads to, and is well-formed; and the new state is urgent-consistent again. -/
theorem successor_sound {N : TNet} (hT : TimingWF N) {co : List Nat → Option (List Nat)}
    (hco : CoWF co) {eps : ℚ} (heps : 0 ≤ eps) {C : Cls} (hC : ClsWF N C) {s : TState}
    (hs : InCls N s C) (hu : Urgent N s) {f : Nat} {d : Deposit} (hen : en N s.m f = true)
    (hready : eftOf N f ≤ s.ν f) {k : Nat} (hk : C.cs[k]? = some f) :
    ∃ C', succ N co eps C k d = some C' ∧
      InCls N ⟨fireAD s.m (trOf N f) d, fun i => if persists N s.m f d i then s.ν i else 0⟩ C' ∧
      ClsWF N C' ∧
      Urgent N ⟨fireAD s.m (trOf N f) d, fun i => if persists N s.m f d i then s.ν i else 0⟩ := by
  obtain ⟨m, ν⟩ := s
  obtain ⟨mC, cs, D⟩ := C
  obtain ⟨hm, hin⟩ := hs
  simp only at hm hin hen hready hk hu ⊢
  subst hm
  have hmem := hC.mem
  simp only at hmem
  have hkn : k < cs.length := (List.getElem?_eq_some_iff.mp hk).1
  have hfk : cs.getD k 0 = f := by
    simp only [List.getD_eq_getElem?_getD, hk, Option.getD_some]
  -- the plan
  set t := trOf N f with ht
  set a' := fireAD m t d with ha'
  set mid := inter m t with hmid
  set C : Cls := ⟨m, cs, D⟩ with hCdef
  set ps := persPos (survives N) C f a' mid with hps
  set pers := ps.map (fun i => cs.getD i 0) with hpers
  set newly := (enabledIds N a').filter (fun j => !pers.contains j) with hnewly
  set lb := newly.map (eftOf N) with hlb
  set ub := newly.map (lftOf N) with hub
  set all := pers ++ newly with hall
  set ν' : Nat → ℚ := fun i => if persists N m f d i then ν i else 0 with hν'
  have hpersL : pers.length = ps.length := List.length_map _
  have hlbL : lb.length = newly.length := List.length_map _
  have hallL : all.length = ps.length + lb.length := by
    simp only [hall, List.length_append, hpersL, hlbL]
  -- the graph's persistent clocks are the semantics' ones
  have hpers_iff : ∀ c, c ∈ pers ↔ persists N m f d c = true := by
    intro c
    refine Iff.trans (mem_pers_iff (surv := survives N) (C := C) (f := f) (a' := a') (mid := mid))
      ?_
    simp only [persists, Bool.and_eq_true]
    rw [hCdef]
    exact and_congr_left' (hmem c)
  have hsurv : ∀ c ∈ pers, c ≠ f ∧ en N a' c = true := by
    intro c hc
    have := ((hpers_iff c).mp hc)
    simp only [persists, survives, Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    exact ⟨this.2.1.1, this.2.1.2⟩
  have hall_iff : ∀ c, c ∈ all ↔ en N a' c = true := by
    intro c
    simp only [hall, List.mem_append, hnewly, List.mem_filter, mem_enabledIds, Bool.not_eq_true',
      contains_false_iff]
    constructor
    · rintro (h | ⟨h, -⟩)
      · exact (hsurv c h).2
      · exact h
    · intro h
      by_cases hc : c ∈ pers
      · exact Or.inl hc
      · exact Or.inr ⟨h, hc⟩
  have hν'_pers : ∀ c ∈ pers, ν' c = ν c := fun c hc => by
    simp only [hν', (hpers_iff c).mp hc, if_true]
  have hν'_new : ∀ c, c ∉ pers → ν' c = 0 := fun c hc => by
    have : persists N m f d c = false := by
      cases h : persists N m f d c
      · rfl
      · exact absurd ((hpers_iff c).mpr h) hc
    simp only [hν', this]
    rfl
  -- the new state is urgent-consistent
  have hu' : Urgent N ⟨a', ν'⟩ := by
    intro i hi
    show ((ν' i : ℚ) : Bound) ≤ _
    by_cases hp : i ∈ pers
    · rw [hν'_pers i hp]
      have := (hpers_iff i).mp hp
      simp only [persists, Bool.and_eq_true] at this
      exact hu i this.1
    · simp only [hν'_new i hp]
      exact lft_nonneg hT i
  -- the old valuation a new one is read from
  let oldV : (Nat → ℚ) → Nat → ℚ := fun ϑ' c =>
    if c = f then 0 else if c ∈ pers then ϑ' c else max 0 (eftOf N c - ν c)
  have holdBox : ∀ ϑ' : Nat → ℚ, (∀ c ∈ all, BoxAt N ν' c (ϑ' c)) →
      ∀ c ∈ cs, BoxAt N ν c (oldV ϑ' c) := by
    intro ϑ' hϑ c hc
    simp only [oldV]
    split_ifs with h1 h2
    · subst h1
      refine ⟨le_refl _, by linarith, ?_⟩
      rw [zero_add]
      exact hu c hen
    · have hb := hϑ c (by rw [hall]; exact List.mem_append_left _ h2)
      obtain ⟨hb0, hb1, hb2⟩ := hb
      rw [hν'_pers c h2] at hb1 hb2
      exact ⟨hb0, hb1, hb2⟩
    · exact box_nonempty hT (hu c ((hmem c).mp hc))
  set n := cs.length with hn
  set K := constrainPre n k D with hK
  set X := fireMat (canonN (n + 1) K) k ps lb ub with hX
  have hKsat : ∀ ϑ' : Nat → ℚ, (∀ c ∈ all, BoxAt N ν' c (ϑ' c)) →
      SatN (n + 1) K (posOf cs (oldV ϑ')) := by
    intro ϑ' hϑ
    have hb := holdBox ϑ' hϑ
    have hsat := hin (oldV ϑ') hb
    refine sat_constrainPre hsat fun i hi => ?_
    rw [posOf_succ, posOf_succ, hfk]
    have : oldV ϑ' f = 0 := by simp [oldV]
    rw [this]
    exact (hb _ (getD_mem 0 hi)).1
  have hXsat : ∀ ϑ' : Nat → ℚ, (∀ c ∈ all, BoxAt N ν' c (ϑ' c)) →
      SatN (ps.length + lb.length + 1) X (posOf all ϑ') := by
    intro ϑ' hϑ
    have hbox_all := hϑ
    refine sat_fireMat (satN_canonN.mpr (hKsat ϑ' hϑ)) hkn (fun x hx => persPos_lt x hx)
      (by rw [posOf_succ, hfk]; simp [oldV]) rfl (fun p hp => ?_) (fun p hp => ?_)
      (fun j hj => ?_) (fun j hj => ?_)
    · have hpp : p < pers.length := by rw [hpersL]; exact hp
      rw [posOf_succ, posOf_succ, getD_append_left 0 hpp]
      have e : pers.getD p 0 = cs.getD (ps.getD p 0) 0 := getD_map _ 0 0 hp
      have hmemp : pers.getD p 0 ∈ pers := getD_mem 0 hpp
      rw [← e]
      simp only [oldV, (hsurv _ hmemp).1, hmemp, if_false, if_true]
    · have hpp : p < pers.length := by rw [hpersL]; exact hp
      rw [posOf_succ]
      exact (hbox_all _ (getD_mem 0 (by rw [hall, List.length_append]; omega))).1
    · have hjn : j < newly.length := by rw [← hlbL]; exact hj
      have hc : newly.getD j 0 ∈ newly := getD_mem 0 hjn
      have hnp : newly.getD j 0 ∉ pers := by
        have := (List.mem_filter.mp hc).2
        rw [Bool.not_eq_true', contains_false_iff] at this
        exact this
      rw [getD_map (eftOf N) 0 0 hjn, show ps.length + j + 1 = (pers.length + j) + 1 by omega,
        posOf_succ, getD_append_right 0 (by omega), show pers.length + j - pers.length = j by omega]
      have hb := hbox_all _ (by rw [hall]; exact List.mem_append_right _ hc)
      have := hb.2.1
      rw [hν'_new _ hnp, add_zero] at this
      simpa [hlb] using this
    · have hjn : j < newly.length := by rw [← hlbL]; exact hj
      have hc : newly.getD j 0 ∈ newly := getD_mem 0 hjn
      have hnp : newly.getD j 0 ∉ pers := by
        have := (List.mem_filter.mp hc).2
        rw [Bool.not_eq_true', contains_false_iff] at this
        exact this
      rw [getD_map (lftOf N) 0 ⊤ hjn, show ps.length + j + 1 = (pers.length + j) + 1 by omega,
        posOf_succ, getD_append_right 0 (by omega), show pers.length + j - pers.length = j by omega]
      have hb := hbox_all _ (by rw [hall]; exact List.mem_append_right _ hc)
      have := hb.2.2
      rw [hν'_new _ hnp, add_zero] at this
      simpa [hub] using this
  -- a witness valuation
  have hne : ∃ ϑ' : Nat → ℚ, ∀ c ∈ all, BoxAt N ν' c (ϑ' c) :=
    ⟨fun c => max 0 (eftOf N c - ν' c), fun c hc => box_nonempty hT (hu' c ((hall_iff c).mp hc))⟩
  obtain ⟨ϑ₀, hϑ₀⟩ := hne
  have hnfK : ¬ FlaggedN eps (n + 1) K := not_flagged_of_sat heps (hKsat ϑ₀ hϑ₀)
  have hnfX : ¬ FlaggedN eps (ps.length + lb.length + 1) X := not_flagged_of_sat heps (hXsat ϑ₀ hϑ₀)
  have hzone : zoneStep eps n k D ps lb ub = some (canonN (ps.length + lb.length + 1) X) := by
    unfold zoneStep
    rw [← hK, if_neg hnfK, ← hX, if_neg hnfX]
  set Y := canonN (ps.length + lb.length + 1) X with hY
  have hYsat : ∀ ϑ' : Nat → ℚ, (∀ c ∈ all, BoxAt N ν' c (ϑ' c)) →
      SatN (all.length + 1) Y (posOf all ϑ') := by
    intro ϑ' hϑ
    rw [hallL, hY, satN_canonN]
    exact hXsat ϑ' hϑ
  have hY00 : Y 0 0 ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := X 0 0) ?_ (canonN_le X (by omega) (by omega))
    simp [hX, fireMat]
  obtain ⟨C', hfin, hm', hmem', hsat', hdown'⟩ :=
    finish_sound (a' := a') hco heps hYsat ⟨ϑ₀, hϑ₀⟩ hY00
  refine ⟨C', ?_, ⟨hm'.symm, hsat'⟩, ⟨fun c => by rw [hmem', hall_iff, hm'], hdown'⟩, hu'⟩
  show succWith (survives N) N co eps C k d = some C'
  unfold succWith
  simp only [hCdef, hk]
  rw [← ht, ← ha', ← hmid, ← hCdef, ← hps, ← hpers, ← hnewly, ← hlb, ← hub, hzone,
    Option.bind_some, ← hall]
  exact hfin


end Libpetri.Novel.TimedScg
