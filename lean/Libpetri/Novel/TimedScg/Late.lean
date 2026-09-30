import Libpetri.Novel.TimedScg.Progress

/-!
# Verification that accounts for deadline reaping ([TIME-013], [TIME-006], [VER-023], [VER-004])

The theorems of `Succ.lean` / `Run.lean` are about `TStep`, the Time Petri net semantics with
strong urgency: time never passes an enabled transition's `lft`. The executor cannot stop time.
When it falls behind (a blocking synchronous action, a suspended process, an injected clock that
jumps: [TIME-015]) a closed timed graph no longer bounds what it does
(`Retrodict.reaping_escapes_timed_graph`). This file gives the executor that falls behind a
model and says which graph does bound it.

## The late executor `LateStep`

* **Time always passes** (`delay`, any `δ ≥ 0`, no urgency).
* **Reaping** (`enforce_deadlines`, `bitmap_backend.rs` / `precompiled_backend.rs`): after a
  delay, a `reapable` transition that is enabled and whose clock is **strictly** past
  `lft + tol` is marked `dead` (`elapsed > latest + deadline_tolerance_ms`). The tolerance is a
  parameter, so a `Deadline` / `Window` transition may fire in `(lft, lft + tol]`. For the
  faithful instantiation `reapable i = (tms i).reapable` (`Timing.reapable`): an `exact()`
  transition is never reaped ([TIME-006], it fires late at its first opportunity), and neither
  are `immediate` / `delayed` ones. A non-reapable transition may fire at any time after `eft`.
* **Firing** (`fire`): enabled, not dead, `eft ≤ clock`, a row of `outcomes`. The clocks follow
  `persists` (premise 9 of `Succ.lean`: the executor's [TIME-012] rule). A dead transition that
  keeps its clock stays dead (`TimedCycle` `bb_reaped_stays_disabled`); one that loses its clock
  loses the mark.
* **Revival** (`revive`, at any time): a dead transition gets a fresh clock and loses the mark.
  This covers the one way the executor re-enables a reaped transition whose tokens are still
  there: a token change on one of its places marks it dirty, and `update_enablement` makes one
  that `can_enable` accepts with its bit clear newly enabled (`TimedCycle.lean`'s
  `reaped_rearms_on_touch`, the [TIME-013] ruling). Before the ruling the precompiled backend
  also marked a reaped transition dirty at once, so its next update re-enabled it. Allowing a
  revival at any time over-approximates both.

Out of scope, as for `TStep`: priorities (they only remove runs), action duration
(`Retrodict.action_duration_escapes`), environment places, ν-joins.

## Results

* `on_time_is_late`: every `TStep` run is a `LateStep` run with nothing reaped (`tol ≥ 0`).
* `late_sim` / `late_run_sound`: every `LateStep` run is covered by the timed graph of
  **`relax N`**, the net with every upper bound dropped (`lft := ⊤`) and the lower bounds kept.
  So `SPURIOUS_UNDER_TIMING` with reaping accounted for is the closed graph of `relax N`
  (`late_safety_of_closed`), not the graph of `N`. The clocks of the executor stay at or below
  the covering `TStep` clocks (a revival only restarts a clock).
* `late_quiescence_sound`: where a late executor comes to rest (every enabled transition reaped:
  `LateQuiescent`, the `enabled_count() == 0` break of `run_sync` / `run_async`), the covering
  class's clocks are **all reapable**. A reaping-aware quiescence check must therefore treat
  every class of the relaxed graph whose clocks are all reapable as a place the executor may
  stop (`late_quiescent_safety_of_closed`), not only the classes with no clock. On the timed
  graph of `N` such a class still has a successor
  (`Progress.reachable_quiescent_iff_dead`), which is exactly what [VER-004] AC3 and
  [VER-023]'s quiescence reading miss (`ReapingVsUntimed.reaping_refutes_ver004_ac3`).

* `relaxLate_fromTimings`, `capped_run_in_rust_graph`: the Rust side. `reaping::relax_late`
  (called by Route B's `verify_via_name_scg_reaping` for every property, on the late set
  `SmtVerifier::late_set` gives it) lifts the latest bound of every `deadline`, `window` and
  `exact` transition (`Timing.relaxLate`), which is `relaxMax N`: `relax N` with the graph's
  finite stand-in `MAX_DURATION_MS` for `⊤`. A late run whose covering clocks stay below 100
  years is in that graph.

The relaxed graph is sound, not exact: it forgets that a reaped transition cannot fire until
its clock restarts. A remark, not stated as a theorem here: since nothing bounds time in
`relax N`, every untimed firing sequence can be timed by waiting for each transition's `eft`,
so the relaxed graph's markings are those of the untimed abstraction, and for marking
properties timing then excludes nothing a late executor could reach. What the relaxed graph
adds is the quiescence side: its all-reapable classes are where the executor may strand
tokens.
-/

namespace Libpetri.Novel.TimedScg

open Libpetri Libpetri.Novel.ForwardDeposit
open Libpetri.Novel.Dbm (Bound)

/-! ## Dropping the upper bounds -/

/-- The net with every upper bound dropped. -/
def relax (N : TNet) : TNet := N.map fun x => { x with lft := ⊤ }

variable {N : TNet}

theorem relax_getElem? (i : Nat) :
    (relax N)[i]? = (N[i]?).map (fun x => { x with lft := ⊤ }) := by
  simp [relax, List.getElem?_map]

theorem relax_length : (relax N).length = N.length := List.length_map _

theorem en_relax (a : AMarking) (i : Nat) : en (relax N) a i = en N a i := by
  unfold en
  rw [relax_getElem?]
  cases N[i]? <;> rfl

theorem trOf_relax (i : Nat) : trOf (relax N) i = trOf N i := by
  unfold trOf
  rw [relax_getElem?]
  cases N[i]? <;> rfl

theorem rowsOf_relax (i : Nat) : rowsOf (relax N) i = rowsOf N i := by
  unfold rowsOf
  rw [relax_getElem?]
  cases N[i]? <;> rfl

theorem eftOf_relax (i : Nat) : eftOf (relax N) i = eftOf N i := by
  unfold eftOf
  rw [relax_getElem?]
  cases N[i]? <;> rfl

theorem lftOf_relax (i : Nat) : lftOf (relax N) i = ⊤ := by
  unfold lftOf
  rw [relax_getElem?]
  cases N[i]? <;> rfl

theorem persists_relax (m : AMarking) (f : Nat) (d : Deposit) (i : Nat) :
    persists (relax N) m f d i = persists N m f d i := by
  simp only [persists, survives, en_relax, trOf_relax]

/-- The relaxed net meets premise 6 as soon as no earliest time is negative, which every
faithful net does (`delayed(after > MAX_DURATION_MS)` included). -/
theorem timingWF_relax (hE : ∀ i, 0 ≤ eftOf N i) : TimingWF (relax N) := fun i => by
  rw [eftOf_relax, lftOf_relax]
  exact ⟨hE i, le_top⟩

/-! ## The late executor -/

/-- An executor state: marking, clocks, and the reaped mark of [TIME-013]. -/
structure RState where
  m : AMarking
  ν : Nat → ℚ
  dead : Nat → Bool

/-- **A late executor with deadline reaping.** -/
inductive LateStep (N : TNet) (reapable : Nat → Bool) (tol : ℚ) : RState → RState → Prop
  | delay (s : RState) (δ : ℚ) (hδ : 0 ≤ δ) :
      LateStep N reapable tol s ⟨s.m, fun i => s.ν i + δ, fun i =>
        s.dead i || (en N s.m i && reapable i &&
          decide (lftOf N i + ((tol : ℚ) : Bound) < ((s.ν i + δ : ℚ) : Bound)))⟩
  | fire (s : RState) (f : Nat) (d : Deposit) (hen : en N s.m f = true)
      (hlive : s.dead f = false) (hready : eftOf N f ≤ s.ν f) (hd : d ∈ rowsOf N f) :
      LateStep N reapable tol s ⟨fireAD s.m (trOf N f) d,
        fun i => if persists N s.m f d i then s.ν i else 0,
        fun i => s.dead i && persists N s.m f d i⟩
  | revive (s : RState) (r : Nat) (hr : s.dead r = true) :
      LateStep N reapable tol s ⟨s.m, fun i => if i = r then 0 else s.ν i,
        fun i => if i = r then false else s.dead i⟩

/-- The states of the late executor's runs from `m0`. -/
def LateReach (N : TNet) (reapable : Nat → Bool) (tol : ℚ) (m0 : AMarking) : RState → Prop :=
  Relation.ReflTransGen (LateStep N reapable tol) ⟨m0, fun _ => 0, fun _ => false⟩

/-- The executor rests: every enabled transition has been reaped. -/
def LateQuiescent (N : TNet) (s : RState) : Prop := ∀ i, en N s.m i = true → s.dead i = true

variable {reapable : Nat → Bool} {tol : ℚ} {m0 : AMarking}

/-- **An on-time run is a late run** in which nothing is reaped. -/
theorem on_time_is_late (htol : 0 ≤ tol) {s : TState} (hs : TReach N m0 s) :
    LateReach N reapable tol m0 ⟨s.m, s.ν, fun _ => false⟩ := by
  induction hs with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    rename_i t _ _
    cases hstep with
    | delay δ hδ hurg =>
      have h := LateStep.delay (N := N) (reapable := reapable) (tol := tol)
        ⟨t.m, t.ν, fun _ => false⟩ δ hδ
      have e : (fun i => (false || (en N t.m i && reapable i &&
          decide (lftOf N i + ((tol : ℚ) : Bound) < ((t.ν i + δ : ℚ) : Bound))))) =
          fun _ => false := by
        funext i
        cases hi : en N t.m i
        · simp
        · have h1 := hurg i hi
          have h2 : lftOf N i ≤ lftOf N i + ((tol : ℚ) : Bound) :=
            le_add_of_nonneg_right (WithTop.coe_le_coe.mpr htol)
          have : ¬ (lftOf N i + ((tol : ℚ) : Bound) < ((t.ν i + δ : ℚ) : Bound)) :=
            not_lt.mpr (h1.trans h2)
          rw [decide_eq_false this]
          simp
      simp only at h
      rw [e] at h
      exact Relation.ReflTransGen.tail ih h
    | fire f d hen hready hd =>
      have h := LateStep.fire (N := N) (reapable := reapable) (tol := tol)
        ⟨t.m, t.ν, fun _ => false⟩ f d hen rfl hready hd
      simp only [Bool.false_and] at h
      exact Relation.ReflTransGen.tail ih h

/-- **The simulation.** Every late state is matched by a `TStep` state of the relaxed net with
the same marking and clocks at least as large. -/
theorem late_sim {s : RState} (hr : LateReach N reapable tol m0 s) :
    ∃ t : TState, TReach (relax N) m0 t ∧ t.m = s.m ∧ (∀ i, s.ν i ≤ t.ν i) ∧ ∀ i, 0 ≤ s.ν i := by
  induction hr with
  | refl => exact ⟨s0 m0, Relation.ReflTransGen.refl, rfl, fun _ => le_refl _, fun _ => le_refl _⟩
  | @tail b _ _ hstep ih =>
    obtain ⟨t, ht, htm, hle, hnn⟩ := ih
    cases hstep with
    | delay δ hδ =>
      refine ⟨⟨t.m, fun i => t.ν i + δ⟩, Relation.ReflTransGen.tail ht
        (TStep.delay t δ hδ fun i _ => by rw [lftOf_relax]; exact le_top), htm,
        fun i => by simp only; linarith [hle i], fun i => by simp only; linarith [hnn i]⟩
    | fire f d hen hlive hready hd =>
      have hen' : en (relax N) t.m f = true := by rw [en_relax, htm]; exact hen
      have hready' : eftOf (relax N) f ≤ t.ν f := by rw [eftOf_relax]; exact hready.trans (hle f)
      have hd' : d ∈ rowsOf (relax N) f := by rw [rowsOf_relax]; exact hd
      refine ⟨_, Relation.ReflTransGen.tail ht (TStep.fire t f d hen' hready' hd'), ?_, ?_, ?_⟩
      · simp only [trOf_relax, htm]
      · intro i
        simp only [persists_relax, htm]
        split_ifs
        · exact hle i
        · exact le_refl _
      · intro i
        simp only
        split_ifs
        · exact hnn i
        · exact le_refl _
    | revive r hr =>
      refine ⟨t, ht, htm, fun i => ?_, fun i => ?_⟩
      · simp only
        split_ifs
        · exact (hnn i).trans (hle i)
        · exact hle i
      · simp only
        split_ifs
        · exact le_refl _
        · exact hnn i

/-- **Late runs stay in the relaxed graph.** Every state of a late executor's run has the
marking of a well-formed class the timed graph of `relax N` reaches. -/
theorem late_run_sound (hE : ∀ i, 0 ≤ eftOf N i) {co : List Nat → Option (List Nat)}
    (hco : CoWF co) {eps : ℚ} (heps : 0 ≤ eps) {C0 : Cls}
    (h0 : initCls (relax N) co eps m0 = some C0) {s : RState} (hr : LateReach N reapable tol m0 s) :
    ∃ C, Relation.ReflTransGen (Edge (relax N) co eps) C0 C ∧ C.m = s.m ∧ ClsWF (relax N) C := by
  obtain ⟨t, ht, htm, -, -⟩ := late_sim hr
  obtain ⟨C, hreach, hin, hwf, -⟩ := timed_run_sound (timingWF_relax hE) hco heps h0 ht
  exact ⟨C, hreach, hin.1.symm.trans htm, hwf⟩

open Classical in
/-- **Reaping-aware `SPURIOUS_UNDER_TIMING`.** A bad predicate of the marking that no class of
the **closed relaxed** graph satisfies holds of no late executor's run. -/
theorem late_safety_of_closed (hE : ∀ i, 0 ≤ eftOf N i) {co : List Nat → Option (List Nat)}
    (hco : CoWF co) {eps : ℚ} (heps : 0 ≤ eps) {C0 : Cls}
    (h0 : initCls (relax N) co eps m0 = some C0) {maxClasses fuel : Nat}
    (hclosed : (Enumeration.build (succList (relax N) co eps) maxClasses fuel C0).2 = true)
    (bad : AMarking → Prop)
    (hgood : ∀ C ∈ (Enumeration.build (succList (relax N) co eps) maxClasses fuel C0).1, ¬ bad C.m)
    {s : RState} (hr : LateReach N reapable tol m0 s) : ¬ bad s.m := by
  obtain ⟨C, hreach, hm, -⟩ := late_run_sound hE hco heps h0 hr
  rw [← hm]
  exact hgood C ((Enumeration.run_complete_iff_reach hclosed C).mpr hreach)

/-! ## Where a late executor rests -/

/-- Only reapable transitions are ever marked dead. -/
theorem dead_reapable {s : RState} (hr : LateReach N reapable tol m0 s) :
    ∀ i, s.dead i = true → reapable i = true := by
  induction hr with
  | refl => intro i h; exact absurd h (by simp)
  | tail _ hstep ih =>
    cases hstep with
    | delay δ hδ =>
      intro i h
      simp only [Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with h | ⟨⟨-, h⟩, -⟩
      · exact ih i h
      · exact h
    | fire f d hen hlive hready hd =>
      intro i h
      simp only [Bool.and_eq_true] at h
      exact ih i h.1
    | revive r hr =>
      intro i h
      simp only at h
      split_ifs at h
      exact ih i h

/-- **Where a late executor rests, every clock of the covering class is reapable.** -/
theorem late_quiescence_sound (hE : ∀ i, 0 ≤ eftOf N i) {co : List Nat → Option (List Nat)}
    (hco : CoWF co) {eps : ℚ} (heps : 0 ≤ eps) {C0 : Cls}
    (h0 : initCls (relax N) co eps m0 = some C0) {s : RState} (hr : LateReach N reapable tol m0 s)
    (hq : LateQuiescent N s) :
    ∃ C, Relation.ReflTransGen (Edge (relax N) co eps) C0 C ∧ C.m = s.m ∧
      ∀ c ∈ C.cs, reapable c = true := by
  obtain ⟨C, hreach, hm, hwf⟩ := late_run_sound hE hco heps h0 hr
  refine ⟨C, hreach, hm, fun c hc => ?_⟩
  have hen := (hwf.mem c).mp hc
  rw [en_relax, hm] at hen
  exact dead_reapable hr c (hq c hen)

open Classical in
/-- **Reaping-aware quiescence.** A bad predicate of a resting marking that no class of the
closed relaxed graph with all its clocks reapable satisfies holds wherever a late executor
rests. -/
theorem late_quiescent_safety_of_closed (hE : ∀ i, 0 ≤ eftOf N i)
    {co : List Nat → Option (List Nat)} (hco : CoWF co) {eps : ℚ} (heps : 0 ≤ eps) {C0 : Cls}
    (h0 : initCls (relax N) co eps m0 = some C0) {maxClasses fuel : Nat}
    (hclosed : (Enumeration.build (succList (relax N) co eps) maxClasses fuel C0).2 = true)
    (qbad : AMarking → Prop)
    (hgood : ∀ C ∈ (Enumeration.build (succList (relax N) co eps) maxClasses fuel C0).1,
      (∀ c ∈ C.cs, reapable c = true) → ¬ qbad C.m)
    {s : RState} (hr : LateReach N reapable tol m0 s) (hq : LateQuiescent N s) : ¬ qbad s.m := by
  obtain ⟨C, hreach, hm, hall⟩ := late_quiescence_sound hE hco heps h0 hr hq
  rw [← hm]
  exact hgood C ((Enumeration.run_complete_iff_reach hclosed C).mpr hreach) hall


/-! ## The Rust relaxation `relax_late`

`reaping::relax_late` (`reaping.rs`) is what Route B builds its graph on
(`nu_scg_verifier.rs::verify_via_name_scg_reaping`, for every property, with `late` the set
`SmtVerifier::late_set` hands it: `reaping::late_transitions` of the net, the transitions whose
timing `has_latest_bound`, or nothing under `assume_no_reaping`). On a transition of `late` with
a latest bound it replaces `deadline(by)` by `immediate()`, `window(e, l)` by `delayed(e)` and
`exact(a)` by `delayed(a)`, `immediate()` when the earliest bound is `0`
(`Timing.relaxLate`). It rebuilds each lifted transition with `with_timing`, which keeps every
arc, the priority, the action, the match spec and the name map, so the relaxation changes the
timing alone, as `relaxLate` does. The graph reads every unbounded timing's latest bound as the
finite `MAX_DURATION_MS` (`Timing.lean`), so with every late transition lifted the Rust graph is the
graph of `relaxMax N`, every `lft` set to that stand-in (`relaxLate_fromTimings`), not the
graph of `relax N`, every `lft` set to `⊤`. The two agree once the stand-in is read as `⊤`
(`relax_relaxMax`), which is the reading `Timing.lean` leaves unproven. What is proved about the
gap: a run of `relax N` whose enabled clocks stay within `MAX_DURATION_MS` (100 years) is a run
of `relaxMax N` (`capped_step`, `capped_run`), so it lies in the graph the Rust builds
(`capped_run_in_rust_graph`). Every transition outside `late` keeps its timing
(`Timing.relaxLate_false`), and a net timed only with `immediate` and `delayed` has nothing to
lift (`Timing.relaxLate_of_no_deadline`), which is why `relax_late` returns `None` for it.
-/

namespace Timing

/-- `relax_late` on one transition's timing; `lifted` is whether the transition is in `late`. -/
def relaxLate (lifted : Bool) (tm : Timing) : Timing :=
  if lifted && tm.hasDeadline then
    if tm.earliest = 0 then .immediate else .delayed tm.earliest
  else tm

theorem relaxLate_false (tm : Timing) : relaxLate false tm = tm := by
  simp [relaxLate]

theorem relaxLate_of_no_deadline {tm : Timing} (h : tm.hasDeadline = false) (b : Bool) :
    relaxLate b tm = tm := by
  simp [relaxLate, h]

/-- The earliest bound is kept. -/
theorem relaxLate_earliest (b : Bool) (tm : Timing) : (relaxLate b tm).earliest = tm.earliest := by
  unfold relaxLate
  split_ifs with h1 h2
  · exact h2.symm
  · rfl
  · rfl

/-- Every lifted timing has the graph's unbounded latest bound. -/
theorem relaxLate_latest (tm : Timing) : (relaxLate true tm).latest = maxDurationMs := by
  unfold relaxLate
  cases tm <;> simp [hasDeadline, latest] <;> split_ifs <;> rfl

/-- A lifted timing has no latest bound left: the executor neither reaps it nor fires it late. -/
theorem relaxLate_hasDeadline (tm : Timing) : (relaxLate true tm).hasDeadline = false := by
  unfold relaxLate
  cases tm <;> simp [hasDeadline] <;> split_ifs <;> rfl

theorem relaxLate_reapable (tm : Timing) : (relaxLate true tm).reapable = false := by
  cases h : (relaxLate true tm).reapable
  · rfl
  · have := reapable_hasDeadline h
    rw [relaxLate_hasDeadline] at this
    exact absurd this (by simp)

/-- A timing the shipped constructors accept stays one: its earliest bound is at most
`MAX_DURATION_MS`, which the R6 check guarantees. -/
theorem relaxLate_valid {tm : Timing} (h : tm.Valid) (b : Bool) : (relaxLate b tm).Valid := by
  have he := h.earliest_le
  unfold relaxLate
  split_ifs with h1 h2
  · trivial
  · exact he
  · exact h

end Timing

/-- The graph's reading of an unbounded latest bound: `MAX_DURATION_MS`, in seconds. -/
def maxLft : Bound := lftT .immediate

/-- Every latest bound set to the stand-in `MAX_DURATION_MS`: the net `relax_late` hands the
graph when every transition with a latest bound is lifted. -/
def relaxMax (N : TNet) : TNet := N.map fun x => { x with lft := maxLft }

theorem relaxMax_getElem? (i : Nat) :
    (relaxMax N)[i]? = (N[i]?).map (fun x => { x with lft := maxLft }) := by
  simp [relaxMax, List.getElem?_map]

theorem en_relaxMax (a : AMarking) (i : Nat) : en (relaxMax N) a i = en N a i := by
  unfold en
  rw [relaxMax_getElem?]
  cases N[i]? <;> rfl

theorem trOf_relaxMax (i : Nat) : trOf (relaxMax N) i = trOf N i := by
  unfold trOf
  rw [relaxMax_getElem?]
  cases N[i]? <;> rfl

theorem rowsOf_relaxMax (i : Nat) : rowsOf (relaxMax N) i = rowsOf N i := by
  unfold rowsOf
  rw [relaxMax_getElem?]
  cases N[i]? <;> rfl

theorem eftOf_relaxMax (i : Nat) : eftOf (relaxMax N) i = eftOf N i := by
  unfold eftOf
  rw [relaxMax_getElem?]
  cases N[i]? <;> rfl

theorem lftOf_relaxMax {i : Nat} (hi : i < N.length) : lftOf (relaxMax N) i = maxLft := by
  unfold lftOf
  rw [relaxMax_getElem?, List.getElem?_eq_getElem hi]
  rfl

theorem persists_relaxMax (m : AMarking) (f : Nat) (d : Deposit) (i : Nat) :
    persists (relaxMax N) m f d i = persists N m f d i := by
  simp only [persists, survives, en_relaxMax, trOf_relaxMax]

/-- Read as `⊤`, the stand-in gives `relax` back. -/
theorem relax_relaxMax : relax (relaxMax N) = relax N := by
  simp [relax, relaxMax, List.map_map, Function.comp_def]

/-- **`relax_late` builds `relaxMax`.** If `N` is the graph's reading of the timings `tms`,
`relaxMax N` is the graph's reading of the timings `relax_late` produces with every transition
lifted. -/
theorem relaxLate_fromTimings {tms : Nat → Timing} (hN : FromTimings N tms) :
    FromTimings (relaxMax N) (fun i => (tms i).relaxLate true) := by
  intro i hi
  rw [relaxMax, List.length_map] at hi
  refine ⟨?_, ?_⟩
  · rw [eftOf_relaxMax, (hN i hi).1]
    unfold eftT
    rw [Timing.relaxLate_earliest]
  · rw [lftOf_relaxMax hi]
    unfold maxLft lftT
    rw [Timing.relaxLate_latest]
    rfl

/-- The relaxed net meets premise 6 when every earliest bound lies in `[0, MAX_DURATION_MS]`,
which every shipped timing's does (`Timing.Valid.earliest_le`). -/
theorem timingWF_relaxMax (hE : ∀ i, 0 ≤ eftOf N i)
    (hle : ∀ i, i < N.length → ((eftOf N i : ℚ) : Bound) ≤ maxLft) : TimingWF (relaxMax N) := by
  intro i
  refine ⟨by rw [eftOf_relaxMax]; exact hE i, ?_⟩
  by_cases hi : i < N.length
  · rw [eftOf_relaxMax, lftOf_relaxMax hi]
    exact hle i hi
  · have e2 : lftOf (relaxMax N) i = ⊤ := by
      simp [lftOf, relaxMax, List.getElem?_eq_none (by simpa using hi : N.length ≤ i)]
    rw [e2]
    exact le_top

/-- Every enabled clock is within the stand-in `MAX_DURATION_MS`. -/
def Capped (N : TNet) (s : TState) : Prop :=
  ∀ i, en N s.m i = true → ((s.ν i : ℚ) : Bound) ≤ maxLft

/-- **A capped step of `relax N` is a step of `relaxMax N`.** -/
theorem capped_step {s s' : TState} (h : TStep (relax N) s s') (hcap : Capped N s') :
    TStep (relaxMax N) s s' := by
  cases h with
  | delay δ hδ _ =>
    refine TStep.delay s δ hδ fun i hi => ?_
    rw [en_relaxMax] at hi
    rw [lftOf_relaxMax (en_lt hi)]
    exact hcap i hi
  | fire f d hen hready hd =>
    have hen' : en (relaxMax N) s.m f = true := by rw [en_relaxMax, ← en_relax]; exact hen
    have hready' : eftOf (relaxMax N) f ≤ s.ν f := by
      rw [eftOf_relaxMax, ← eftOf_relax (N := N)]; exact hready
    have hd' : d ∈ rowsOf (relaxMax N) f := by
      rw [rowsOf_relaxMax, ← rowsOf_relax (N := N)]; exact hd
    have := TStep.fire s f d hen' hready' hd'
    simp only [trOf_relaxMax, persists_relaxMax] at this
    simp only [trOf_relax, persists_relax]
    exact this

/-- **A run of `relax N` that stays capped is a run of `relaxMax N`.** -/
theorem capped_run {s : TState}
    (h : Relation.ReflTransGen (fun a b => TStep (relax N) a b ∧ Capped N b) (s0 m0) s) :
    TReach (relaxMax N) m0 s := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih => exact Relation.ReflTransGen.tail ih (capped_step hab.1 hab.2)

/-- **A capped run lies in the graph the Rust builds.** Every state of a run of `relax N` whose
enabled clocks stay within `MAX_DURATION_MS` is in a class the timed graph of `relaxMax N` (the
net `relax_late` returns) reaches. -/
theorem capped_run_in_rust_graph (hE : ∀ i, 0 ≤ eftOf N i)
    (hle : ∀ i, i < N.length → ((eftOf N i : ℚ) : Bound) ≤ maxLft)
    {co : List Nat → Option (List Nat)} (hco : CoWF co) {eps : ℚ} (heps : 0 ≤ eps) {C0 : Cls}
    (h0 : initCls (relaxMax N) co eps m0 = some C0) {s : TState}
    (h : Relation.ReflTransGen (fun a b => TStep (relax N) a b ∧ Capped N b) (s0 m0) s) :
    ∃ C, Relation.ReflTransGen (Edge (relaxMax N) co eps) C0 C ∧ C.m = s.m := by
  obtain ⟨C, hreach, hin, -, -⟩ :=
    timed_run_sound (timingWF_relaxMax hE hle) hco heps h0 (capped_run h)
  exact ⟨C, hreach, hin.1.symm⟩

end Libpetri.Novel.TimedScg
