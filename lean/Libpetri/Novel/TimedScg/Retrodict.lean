import Libpetri.Novel.TimedScg.Late
import Mathlib.Tactic.IntervalCases

/-!
# Runs the timed graph misses

Each section is a witness: a run of the executor, or of an earlier graph, that the timed graph of
`Succ.lean` does not contain, with the Rust behaviour it stands for.

## 1. The pre-6.0.0 clock-persistence / reset-restart bug ([TIME-012], [VER-010] AC4)

Before 6.0.0 (the CHANGELOG entry "Timing: clock restarts follow the intermediate marking" is
in the Java 6.0.0 / TypeScript 6.0.0 / Rust 6.0.0 / Python 5.0.0 release; for Rust,
`rust/v5.1.0:state_class_graph.rs` has no intermediate marking and `rust/v6.0.0` has it) the
state-class graph kept a clock whenever its transition was enabled before and after a firing:
the survival test was `survivesOld`, with no look at the intermediate marking `M - Pre(t)`, so
neither a consume-and-return refresh nor a reset-and-refill restarted anything. `succOld` is
`compute_successor` with that test; everything else is today's code.

Witness (`netRT`, the Rust test `conserved_input_refresh_gives_a_fresh_interval` with a
deadline instead of a delay, so that the kept clock *excludes* a run rather than admitting an
extra one):

* `CloseSession` (index 0): `timer → done`, `window(0, 150)`;
* `Refresh` (index 1): `act + timer → timer`, `exact(100)`;
* `M₀ = {act, timer}`.

(Units: seconds here, `window(0, 150_000)` / `exact(100_000)` in milliseconds, `netRT_faithful`.)
At `t = 100` `Refresh` fires; it takes the only timer token and puts one back, so `CloseSession`
is disabled in the intermediate marking and its clock restarts ([TIME-012] AC1): it may now
fire as late as `t = 250`. The old rule keeps the clock, so its successor class bounds
`CloseSession`'s time-to-fire by `150 - 100 = 50`.

* `rt_rules_differ` (by `decide`): the old test keeps `CloseSession`'s clock, `persists` does not.
* `old_rule_loses_run`: the timed run `delay 100; fire Refresh` reaches a state (clock of
  `CloseSession` at `0`, so time-to-fire `100` possible) that lies in **no** successor the old rule
  computes from the initial class, while today's `succ` has one containing it
  (`successor_sound`). Under the old rule the graph therefore under-approximates: a violation
  reachable only after `CloseSession` fires later than `t = 150` (e.g. a watchdog `delayed(160)`
  inhibited by `done`) is missed, and a closed graph reports `SPURIOUS_UNDER_TIMING` ([VER-023])
  for a property the net violates.

## 2. Deadline reaping escapes the timed graph ([TIME-013] against [VER-023])

`Late.LateStep` is the executor that falls behind. Witness (`netRP`, the Rust test
`untimed_exploration_reaches_a_marking_the_timing_excludes`): `t1 : p → a`, `deadline(5)`;
`t2 : p → b`, `delayed(10)`; `M₀ = {p}`.

* `reaping_escapes_timed_graph`: a late executor reaches `b` (wake at `t = 10`, `t2` fires),
  while every class the timed graph reaches has `b = 0`, and so does every state of every `TStep`
  run. So `SPURIOUS_UNDER_TIMING` for `unreachable(b)` is a claim about the Time Petri net
  semantics, not about an executor that reaps. This is also the retrodiction of Route B before
  the lateness fix: it built the strong-semantics graph of `netRP` for a marking property and
  answered `Proven`.
* `reaping_witness_in_relaxed_graph`: the graph of `Late.relax netRP` does reach `b`, as
  `Late.late_run_sound` says it must. Route B now builds this graph for every property
  (`reaping::relax_late`, called from `verify_via_name_scg_reaping`; `Late.lean`, "The Rust
  relaxation"), and the ν version of this net is `Violated` there.
* `late_rest_witness`: the `window(3, 5)` transition of `TimedCycle.lean` alone: a late executor
  rests at `{p}` with the transition reaped, while the class of the timed graph at `{p}` has a
  successor. The relaxed graph's class at `{p}` has only reapable clocks, which is what
  `Late.late_quiescence_sound` flags.

## 3. A name-disabled ν-join bounds time in Route B's graph ([NU-020], [NU-050])

`name_disabled_join_escapes` is stated over the plain `Edge` graph of a net **without** ν: a
`blocked` predicate stands in for "count-enabled but never name-enabled". It does not model
`name_state_class_graph.rs::build_until`, its name layer, or the [NU-052] prune; it shows only
that a clock the executor does not have excludes a run it makes. Route B no longer has this
behaviour: `build_until` now computes the base successor through `compute_successor_gated` with
`name_enabled` as the gate, so a join whose inputs share no name holds no clock (see the
section).

## 4. Action duration ([VER-010] AC4)

`action_duration_escapes`: an on-time executor whose action takes time deposits after the
firing, so a transition inhibited by that output can fire in between; the graph and `TStep`
deposit at the firing instant and never see it.

## 5. `delayed(after > MAX_DURATION_MS)` ([TIME-003], premise 6)

`delayed_past_max_escapes`: `delayed(MAX_DURATION_MS + 1)` was accepted by the Rust constructor
before the R6 fix, its graph interval is `[MAX + 0.001, MAX]` (`Timing.lean`), premise 6 fails,
the model's `initCls` flags the zone empty, `TStep` time-locks, and the executor, which never
forces a `delayed` transition, fires it. The shipped `delayed` asserts `after <= MAX_DURATION_MS`
and panics on this net (`netBig_rejected`), and `TransitionBuilder::build` re-runs that check on
a `Timing::Delayed` written out without the constructor ([TIME-001] AC5, `Timing.lean`), so it
is a retrodiction now.
-/

namespace Libpetri.Novel.TimedScg

open Libpetri Libpetri.Novel.ForwardDeposit
open Libpetri.Novel.Dbm (Bound)

/-! ## Unfolding the successor -/

theorem succWith_marking {surv : Nat → AMarking → AMarking → Nat → Bool} {N : TNet}
    {co : List Nat → Option (List Nat)} {eps : ℚ} {C C' : Cls} {k : Nat} {d : Deposit}
    (h : succWith surv N co eps C k d = some C') :
    ∃ f, C.cs[k]? = some f ∧ C'.m = fireAD C.m (trOf N f) d := by
  unfold succWith at h
  cases hk : C.cs[k]? with
  | none => rw [hk] at h; exact absurd h (by simp)
  | some f =>
    rw [hk] at h
    simp only at h
    obtain ⟨Y, -, hfin⟩ := Option.bind_eq_some_iff.mp h
    unfold finish at hfin
    split_ifs at hfin
    cases hfin
    exact ⟨f, rfl, rfl⟩

/-- With the identity order, the successor's clocks are persistent-then-newly-enabled, and a
persistent clock's upper bound is at most the old difference bound `θ_o - θ_f`. -/
theorem succWith_none_spec {surv : Nat → AMarking → AMarking → Nat → Bool}
    (hsurv : ∀ f a' mid c, surv f a' mid c = true → c ≠ f) {N : TNet} {eps : ℚ} {C C' : Cls}
    {k f : Nat} {d : Deposit} (hk : C.cs[k]? = some f) {ps : List Nat}
    (hps : ps = persPos surv C f (fireAD C.m (trOf N f) d) (inter C.m (trOf N f)))
    (h : succWith surv N (fun _ => none) eps C k d = some C') :
    C'.cs = ps.map (fun i => C.cs.getD i 0) ++
        (enabledIds N (fireAD C.m (trOf N f) d)).filter
          (fun j => !(ps.map fun i => C.cs.getD i 0).contains j) ∧
      ∀ p, p < ps.length → C'.D (p + 1) 0 ≤ C.D (ps.getD p 0 + 1) (k + 1) := by
  have hkn : k < C.cs.length := (List.getElem?_eq_some_iff.mp hk).1
  have hfk : C.cs.getD k 0 = f := by simp only [List.getD_eq_getElem?_getD, hk, Option.getD_some]
  unfold succWith at h
  rw [hk] at h
  simp only at h
  rw [← hps] at h
  obtain ⟨Y, hz, hfin⟩ := Option.bind_eq_some_iff.mp h
  unfold finish reorder reorderMat at hfin
  simp only at hfin
  split_ifs at hfin
  cases hfin
  refine ⟨rfl, fun p hp => ?_⟩
  set newly := (enabledIds N (fireAD C.m (trOf N f) d)).filter
    (fun j => !(ps.map fun i => C.cs.getD i 0).contains j)
  set lb := newly.map (eftOf N)
  set ub := newly.map (lftOf N)
  have hdim : p + 1 < (ps.map (fun i => C.cs.getD i 0) ++ newly).length + 1 := by
    simp only [List.length_append, List.length_map]; omega
  refine (canonN_le _ hdim (by omega)).trans ?_
  simp only [ltpPre, show p + 1 ≠ 0 by omega, false_and, if_false]
  unfold zoneStep at hz
  split_ifs at hz
  cases hz
  have hdimX : p + 1 < ps.length + lb.length + 1 := by omega
  refine (canonN_le _ hdimX (by omega)).trans ?_
  have hpo : ps.getD p 0 < C.cs.length := by
    rw [hps] at hp ⊢
    exact persPos_lt _ (getD_mem 0 hp)
  have hallS : ∀ x ∈ ps, surv f (fireAD C.m (trOf N f) d) (inter C.m (trOf N f)) (C.cs.getD x 0) = true := by
    rw [hps]
    intro x hx
    simp only [persPos, List.mem_filter, List.mem_range] at hx
    exact hx.2
  have hne : ps.getD p 0 ≠ k := by
    intro heq
    have := hsurv _ _ _ _ (hallS _ (getD_mem 0 hp))
    rw [heq, hfk] at this
    exact this rfl
  simp only [fireMat, show p + 1 ≠ 0 by omega, if_false, show p + 1 ≤ ps.length by omega,
    if_true, Nat.add_sub_cancel]
  refine (canonN_le _ (by omega) (by omega)).trans ?_
  simp only [constrainPre, show ¬ (ps.getD p 0 + 1 = k + 1) by omega, false_and, if_false]
  exact le_refl _

/-! ## 1. The pre-6.0.0 rule -/

/-- The pre-6.0.0 survival test (Rust ≤ 5.x): not the fired transition, enabled after. No
intermediate marking. -/
def survivesOld (N : TNet) (f : Nat) (a' _mid : AMarking) (c : Nat) : Bool :=
  c != f && en N a' c

section Refresh

/-- Places: `act = 0`, `timer = 1`, `done = 2`. -/
def netRT : TNet :=
  [ { tr := { name := "CloseSession", inputs := [⟨1, .one, none⟩], inhibitors := [], reads := [],
              resets := [] },
      rows := [[2]], eft := 0, lft := ((150 : ℚ) : Bound) },
    { tr := { name := "Refresh", inputs := [⟨0, .one, none⟩, ⟨1, .one, none⟩], inhibitors := [],
              reads := [], resets := [] },
      rows := [[1]], eft := 100, lft := ((100 : ℚ) : Bound) } ]

def m0RT : AMarking := fun p => if p = 0 then 1 else if p = 1 then 1 else 0

/-- After `delay 100; fire Refresh`: the timer is back, `CloseSession`'s clock restarted. -/
def s2RT : TState :=
  ⟨fireAD m0RT (trOf netRT 1) [1], fun i => if persists netRT m0RT 1 [1] i then 100 else 0⟩

/-- **The two rules differ on the refresh** (by `decide`): the old test keeps `CloseSession`'s
clock across `Refresh`, the intermediate-marking rule restarts it. -/
theorem rt_rules_differ :
    survivesOld netRT 1 (fireAD m0RT (trOf netRT 1) [1]) (inter m0RT (trOf netRT 1)) 0 = true ∧
      persists netRT m0RT 1 [1] 0 = false ∧ en netRT m0RT 0 = true ∧
      en netRT (fireAD m0RT (trOf netRT 1) [1]) 0 = true := by
  decide

theorem netRT_wf : TimingWF netRT := by
  intro i
  match i with
  | 0 => exact ⟨le_refl _, by simp [eftOf, lftOf, netRT]⟩
  | 1 => exact ⟨by simp [eftOf, netRT], le_refl _⟩
  | i + 2 => exact ⟨le_refl _, by simp [eftOf, lftOf, netRT]⟩

theorem co_none_wf : CoWF (fun _ => none) := fun _ _ h => by simp at h

theorem en_netRT_lt {a : AMarking} {i : Nat} (h : en netRT a i = true) : i = 0 ∨ i = 1 := by
  have := en_lt h
  simp only [netRT, List.length_cons, List.length_nil] at this
  omega

/-- The run `delay 100; fire Refresh` is a timed run. -/
theorem s2RT_reach : TReach netRT m0RT s2RT := by
  have h1 : TStep netRT (s0 m0RT) ⟨m0RT, fun _ => 100⟩ := by
    have := TStep.delay (N := netRT) (s0 m0RT) 100 (by norm_num) (fun i hi => by
      rcases en_netRT_lt hi with rfl | rfl
      · simp only [s0, lftOf, netRT]
        exact WithTop.coe_le_coe.mpr (by norm_num)
      · simp only [s0, lftOf, netRT]
        exact WithTop.coe_le_coe.mpr (by norm_num))
    simpa [s0] using this
  have h2 : TStep netRT ⟨m0RT, fun _ => 100⟩ s2RT :=
    TStep.fire _ 1 [1] (by decide) (by simp [eftOf, netRT]) (by simp [rowsOf, netRT])
  exact Relation.ReflTransGen.tail (Relation.ReflTransGen.tail Relation.ReflTransGen.refl h1) h2

/-- The initial class of the witness, with the identity order (the names are sorted). -/
theorem initRT_spec {eps : ℚ} {C0 : Cls} (h0 : initCls netRT (fun _ => none) eps m0RT = some C0) :
    C0.m = m0RT ∧ C0.cs = [0, 1] ∧ C0.D 1 2 ≤ ((50 : ℚ) : Bound) := by
  obtain ⟨hm, hcs, hD⟩ := initCls_eq h0
  have hcs' : C0.cs = [0, 1] := by rw [hcs]; decide
  refine ⟨hm, hcs', ?_⟩
  rw [hD, hcs']
  refine (canonN_le _ (by simp) (by simp)).trans ?_
  simp only [ltpPre, show (1 : Nat) ≠ 0 by omega, false_and, if_false]
  refine (canonN_le_walk _ (k := 0) (by simp) (by simp) (by simp)).trans ?_
  have hB10 : createPre [0, 1].length ([0, 1].map (eftOf netRT)) ([0, 1].map (lftOf netRT)) 1 0 =
      ((150 : ℚ) : Bound) := by
    simp [createPre, lftOf, netRT]
  have hB02 : createPre [0, 1].length ([0, 1].map (eftOf netRT)) ([0, 1].map (lftOf netRT)) 0 2 =
      ((-100 : ℚ) : Bound) := by
    simp [createPre, eftOf, netRT]
  rw [hB10, hB02, ← WithTop.coe_add, WithTop.coe_le_coe]
  norm_num

/-- **The pre-6.0.0 rule loses a timed run.** The run `delay 100; fire Refresh` reaches `s2RT`; no
successor of the initial class under the old rule contains it, while today's graph has one. -/
theorem old_rule_loses_run {eps : ℚ} (heps : 0 ≤ eps) {C0 : Cls}
    (h0 : initCls netRT (fun _ => none) eps m0RT = some C0) :
    TReach netRT m0RT s2RT ∧
      (∀ C' ∈ succListWith (survivesOld netRT) netRT (fun _ => none) eps C0,
        ¬ InCls netRT s2RT C') ∧
      ∃ C' ∈ succList netRT (fun _ => none) eps C0, InCls netRT s2RT C' := by
  obtain ⟨hm0, hcs0, hD12⟩ := initRT_spec h0
  refine ⟨s2RT_reach, ?_, ?_⟩
  · intro C' hC' hin
    simp only [succListWith, List.mem_flatMap, List.mem_range, List.mem_filterMap] at hC'
    obtain ⟨k, hk, d, hd, hs⟩ := hC'
    rw [hcs0] at hk hd
    simp only [List.length_cons, List.length_nil] at hk
    obtain ⟨f, hkf, hmC'⟩ := succWith_marking hs
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · -- firing `CloseSession` empties the timer; `s2RT` holds it
      rw [hcs0] at hkf
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hkf
      subst hkf
      simp only [List.getD_cons_zero, rowsOf, netRT, List.getElem?_cons_zero,
        List.mem_singleton] at hd
      subst hd
      have := congrFun (hin.1.trans hmC') 1
      rw [hm0] at this
      revert this
      decide
    · rw [hcs0] at hkf
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hkf
      subst hkf
      simp only [List.getD_cons_succ, List.getD_cons_zero, rowsOf, netRT, List.getElem?_cons_succ,
        List.getElem?_cons_zero, List.mem_singleton] at hd
      subst hd
      have hk1 : C0.cs[1]? = some 1 := by rw [hcs0]; rfl
      have hps : persPos (survivesOld netRT) C0 1 (fireAD C0.m (trOf netRT 1) [1])
          (inter C0.m (trOf netRT 1)) = [0] := by
        unfold persPos
        rw [hcs0, hm0]
        decide
      obtain ⟨hcs', hbound⟩ := succWith_none_spec (fun f a' mid c h => by
        simp only [survivesOld, Bool.and_eq_true, bne_iff_ne] at h; exact h.1) hk1 hps.symm hs
      have hcs'' : C'.cs = [0] := by
        rw [hcs', hcs0, hm0]
        decide
      have hb := hbound 0 (by simp)
      simp only [List.getD_cons_zero, zero_add] at hb
      -- the state's time-to-fire `100` for `CloseSession`
      have hsat := hin.2 (fun _ => 100) (by
        intro c hc
        rw [hcs''] at hc
        simp only [List.mem_singleton] at hc
        subst hc
        have hp0 : persists netRT m0RT 1 [1] 0 = false := by decide
        have hν : s2RT.ν 0 = 0 := by simp only [s2RT, hp0]; rfl
        refine ⟨by norm_num, ?_, ?_⟩
        · rw [hν]; simp [eftOf, netRT]
        · rw [hν]
          simp only [lftOf, netRT, List.getElem?_cons_zero]
          exact WithTop.coe_le_coe.mpr (by norm_num))
      have h10 := hsat 1 0 (by rw [hcs'']; simp) (by simp)
      simp only [posOf, if_false, if_true, sub_zero, show (1 : Nat) ≠ 0 by omega] at h10
      have := (h10.trans hb).trans hD12
      rw [WithTop.coe_le_coe] at this
      norm_num at this
  · -- today's rule: the delayed initial state fires `Refresh` into a successor containing `s2RT`
    obtain ⟨C, hC, hin, hwf⟩ := init_sound netRT_wf co_none_wf heps m0RT
    rw [h0] at hC
    cases hC
    have hurg : ∀ i, en netRT m0RT i = true → (((0 : ℚ) + 100 : ℚ) : Bound) ≤ lftOf netRT i := by
      intro i hi
      rcases en_netRT_lt hi with rfl | rfl
      · simp only [lftOf, netRT]
        exact WithTop.coe_le_coe.mpr (by norm_num)
      · simp only [lftOf, netRT]
        exact WithTop.coe_le_coe.mpr (by norm_num)
    have hin1 := delay_sound hwf hin (δ := 100) (by norm_num)
    have hu1 : Urgent netRT ⟨(s0 m0RT).m, fun i => (s0 m0RT).ν i + 100⟩ := hurg
    have hk1 : C0.cs[1]? = some 1 := by rw [hcs0]; rfl
    obtain ⟨C', hs, hin', -, -⟩ := successor_sound netRT_wf co_none_wf heps hwf hin1 hu1
      (f := 1) (d := [1]) (by decide) (by simp [s0, eftOf, netRT]) hk1
    refine ⟨C', succ_mem_succList (by rw [hcs0]; simp) (by rw [hcs0]; simp [rowsOf, netRT]) hs, ?_⟩
    have e : s2RT = ⟨fireAD (s0 m0RT).m (trOf netRT 1) [1], fun i =>
        if persists netRT (s0 m0RT).m 1 [1] i then (s0 m0RT).ν i + 100 else 0⟩ := by
      simp only [s2RT, s0, zero_add]
    rw [e]
    exact hin'

/-- `netRT` is the graph's reading of `window(0, 150_000)` and `exact(100_000)`. -/
def tmsRT : Nat → Timing
  | 0 => .window 0 150000
  | _ => .exact 100000

theorem netRT_faithful : FromTimings netRT tmsRT := by
  intro i hi
  simp only [netRT, List.length_cons, List.length_nil] at hi
  interval_cases i
  · refine ⟨?_, ?_⟩
    · simp only [eftOf, netRT, List.getElem?_cons_zero, eftT, tmsRT, Timing.earliest]; norm_num
    · simp only [lftOf, netRT, List.getElem?_cons_zero, lftT, tmsRT, Timing.latest]
      congr 1; norm_num
  · refine ⟨?_, ?_⟩
    · simp only [eftOf, netRT, List.getElem?_cons_succ, List.getElem?_cons_zero, eftT, tmsRT,
        Timing.earliest]; norm_num
    · simp only [lftOf, netRT, List.getElem?_cons_succ, List.getElem?_cons_zero, lftT, tmsRT,
        Timing.latest]
      congr 1; norm_num

end Refresh

/-! ## 2. Deadline reaping -/

section Reaping

/-- Places: `p = 0`, `a = 1`, `b = 2`. `t1 : p → a`, `deadline(5)`; `t2 : p → b`,
`delayed(10)`, whose graph interval is `[10, MAX_DURATION_MS / 1000]` (`netRP_faithful`). -/
def netRP : TNet :=
  [ { tr := { name := "t1", inputs := [⟨0, .one, none⟩], inhibitors := [], reads := [], resets := [] },
      rows := [[1]], eft := 0, lft := ((5 : ℚ) : Bound) },
    { tr := { name := "t2", inputs := [⟨0, .one, none⟩], inhibitors := [], reads := [], resets := [] },
      rows := [[2]], eft := 10, lft := ((3153600000 : ℚ) : Bound) } ]

/-- The Rust timings of `netRP`, in milliseconds. -/
def tmsRP : Nat → Timing
  | 0 => .deadline 5000
  | _ => .delayed 10000

theorem netRP_faithful : FromTimings netRP tmsRP := by
  intro i hi
  simp only [netRP, List.length_cons, List.length_nil] at hi
  interval_cases i
  · refine ⟨?_, ?_⟩
    · simp only [eftOf, netRP, List.getElem?_cons_zero, eftT, tmsRP, Timing.earliest]; norm_num
    · simp only [lftOf, netRP, List.getElem?_cons_zero, lftT, tmsRP, Timing.latest]
      congr 1; norm_num
  · refine ⟨?_, ?_⟩
    · simp only [eftOf, netRP, List.getElem?_cons_succ, List.getElem?_cons_zero, eftT, tmsRP,
        Timing.earliest]; norm_num
    · simp only [lftOf, netRP, List.getElem?_cons_succ, List.getElem?_cons_zero, lftT, tmsRP,
        Timing.latest]
      congr 1; norm_num [maxDurationMs]

/-- `t1` has a hard deadline ([TIME-013]); `t2` is `delayed`, never reaped. -/
def reapRP : Nat → Bool := fun i => (tmsRP i).reapable

def m0RP : AMarking := fun q => if q = 0 then 1 else 0

theorem netRP_wf : TimingWF netRP := by
  intro i
  match i with
  | 0 => exact ⟨le_refl _, by simp [eftOf, lftOf, netRP]⟩
  | 1 => exact ⟨by simp [eftOf, netRP], by
      simp only [eftOf, lftOf, netRP, List.getElem?_cons_succ, List.getElem?_cons_zero]
      exact WithTop.coe_le_coe.mpr (by norm_num)⟩
  | i + 2 => exact ⟨le_refl _, by simp [eftOf, lftOf, netRP]⟩

theorem netRP_rows : ∀ i, i < netRP.length → rowsOf netRP i ≠ [] := by
  intro i hi
  simp only [netRP, List.length_cons, List.length_nil] at hi
  interval_cases i <;> simp [rowsOf, netRP]

/-- **The premises of the faithful quiescence theorem are met** by `netRP` (so
`Progress.faithful_quiescent_iff_dead` is not vacuous). -/
theorem netRP_premises :
    FromTimings netRP tmsRP ∧ (∀ i, i < netRP.length → (tmsRP i).Valid) ∧
      (∀ i, i < netRP.length → ∀ a, tmsRP i = .delayed a → a ≤ maxDurationMs) ∧
      (∀ i, i < netRP.length → rowsOf netRP i ≠ []) := by
  refine ⟨netRP_faithful, fun i hi => ?_, fun i hi a ha => ?_, netRP_rows⟩
  · simp only [netRP, List.length_cons, List.length_nil] at hi
    interval_cases i <;> simp [tmsRP, Timing.Valid, maxDurationMs]
  · simp only [netRP, List.length_cons, List.length_nil] at hi
    interval_cases i
    · simp [tmsRP] at ha
    · simp only [tmsRP, Timing.delayed.injEq] at ha
      subst ha
      norm_num [maxDurationMs]

theorem en_netRP_lt {a : AMarking} {i : Nat} (h : en netRP a i = true) : i = 0 ∨ i = 1 := by
  have := en_lt h
  simp only [netRP, List.length_cons, List.length_nil] at this
  omega

/-- A late executor marks `b`: it wakes at `t = 10` and `t2` fires. Whether `t1` was reaped on
the way does not matter. -/
theorem late_executor_marks_b (tol : ℚ) :
    ∃ s, LateReach netRP reapRP tol m0RP s ∧ s.m 2 = 1 := by
  refine ⟨_, Relation.ReflTransGen.tail (Relation.ReflTransGen.single
    (LateStep.delay (N := netRP) (reapable := reapRP) (tol := tol)
      ⟨m0RP, fun _ => 0, fun _ => false⟩ 10 (by norm_num)))
    (LateStep.fire _ 1 [2] ?_ ?_ ?_ ?_), ?_⟩
  · show en netRP m0RP 1 = true
    decide
  · simp [reapRP, tmsRP, Timing.reapable]
  · simp [eftOf, netRP]
  · simp [rowsOf, netRP]
  · show fireAD m0RP (trOf netRP 1) [2] 2 = 1
    decide

/-- The initial class of the reaping witness: `t2` can never fire first, since
`θ_t1 - θ_t2 ≤ 5 - 10`. -/
theorem initRP_spec {eps : ℚ} {C0 : Cls} (h0 : initCls netRP (fun _ => none) eps m0RP = some C0) :
    C0.m = m0RP ∧ C0.cs = [0, 1] ∧ C0.D 1 2 ≤ ((-5 : ℚ) : Bound) := by
  obtain ⟨hm, hcs, hD⟩ := initCls_eq h0
  have hcs' : C0.cs = [0, 1] := by rw [hcs]; decide
  refine ⟨hm, hcs', ?_⟩
  rw [hD, hcs']
  refine (canonN_le _ (by simp) (by simp)).trans ?_
  simp only [ltpPre, show (1 : Nat) ≠ 0 by omega, false_and, if_false]
  refine (canonN_le_walk _ (k := 0) (by simp) (by simp) (by simp)).trans ?_
  have hB10 : createPre [0, 1].length ([0, 1].map (eftOf netRP)) ([0, 1].map (lftOf netRP)) 1 0 =
      ((5 : ℚ) : Bound) := by
    simp [createPre, lftOf, netRP]
  have hB02 : createPre [0, 1].length ([0, 1].map (eftOf netRP)) ([0, 1].map (lftOf netRP)) 0 2 =
      ((-10 : ℚ) : Bound) := by
    simp [createPre, eftOf, netRP]
  rw [hB10, hB02, ← WithTop.coe_add, WithTop.coe_le_coe]
  norm_num

/-- Firing `t2` first is flagged empty, so the graph has no such edge. -/
theorem succRP_t2_none {eps : ℚ} (heps : eps < 5) {C0 : Cls}
    (h0 : initCls netRP (fun _ => none) eps m0RP = some C0) (d : Deposit) :
    succ netRP (fun _ => none) eps C0 1 d = none := by
  obtain ⟨-, hcs0, hD12⟩ := initRP_spec h0
  have hflag : FlaggedN eps (C0.cs.length + 1) (constrainPre C0.cs.length 1 C0.D) := by
    rw [hcs0]
    refine flaggedN_of_cycle (a := 1) (k := 2) (by simp) (by simp) ?_
    have h12 : constrainPre [0, 1].length 1 C0.D 1 2 = C0.D 1 2 := by
      simp [constrainPre]
    have h21 : constrainPre [0, 1].length 1 C0.D 2 1 ≤ ((0 : ℚ) : Bound) := by
      simp only [constrainPre, List.length_cons, List.length_nil]
      rw [if_pos (by decide)]
      exact min_le_right _ _
    rw [h12]
    calc C0.D 1 2 + constrainPre [0, 1].length 1 C0.D 2 1
        ≤ ((-5 : ℚ) : Bound) + ((0 : ℚ) : Bound) := add_le_add hD12 h21
      _ = ((-5 : ℚ) : Bound) := by rw [← WithTop.coe_add]; norm_num
      _ < ((-eps : ℚ) : Bound) := WithTop.coe_lt_coe.mpr (by linarith)
  have hk : C0.cs[1]? = some 1 := by rw [hcs0]; rfl
  unfold succ succWith
  rw [hk]
  simp only
  unfold zoneStep
  rw [if_pos hflag]
  rfl

/-- Every class the timed graph reaches has `b = 0`: from the initial class only `t1` fires, and
its successor enables nothing. -/
theorem graphRP_never_marks_b {eps : ℚ} (heps : eps < 5) {C0 : Cls}
    (h0 : initCls netRP (fun _ => none) eps m0RP = some C0) {C : Cls}
    (h : Relation.ReflTransGen (Edge netRP (fun _ => none) eps) C0 C) : C.m 2 = 0 := by
  obtain ⟨hm0, hcs0, -⟩ := initRP_spec h0
  have key : ∀ C, Relation.ReflTransGen (Edge netRP (fun _ => none) eps) C0 C →
      C.m 2 = 0 ∧ (C = C0 ∨ C.cs = []) := by
    intro C h
    induction h with
    | refl => exact ⟨by rw [hm0]; rfl, Or.inl rfl⟩
    | tail _ hstep ih =>
      obtain ⟨-, hor⟩ := ih
      simp only [Edge, succList, succListWith, List.mem_flatMap, List.mem_range,
        List.mem_filterMap] at hstep
      obtain ⟨k, hk, d, hd, hs⟩ := hstep
      rcases hor with rfl | hnil
      · rw [hcs0] at hk hd
        simp only [List.length_cons, List.length_nil] at hk
        rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
        · obtain ⟨f, hkf, hmC⟩ := succWith_marking hs
          rw [hcs0] at hkf
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hkf
          subst hkf
          simp only [List.getD_cons_zero, rowsOf, netRP, List.getElem?_cons_zero,
            List.mem_singleton] at hd
          subst hd
          have hwf := (succ_wf co_none_wf hs).1
          refine ⟨by rw [hmC, hm0]; decide, Or.inr ?_⟩
          refine List.eq_nil_iff_forall_not_mem.mpr fun c hc => ?_
          have hen := (hwf.mem c).mp hc
          rw [hmC, hm0] at hen
          rcases en_netRP_lt hen with rfl | rfl <;> revert hen <;> decide
        · have hn := succRP_t2_none heps h0 d
          unfold succ at hn
          rw [hn] at hs
          exact absurd hs (by simp)
      · rw [hnil] at hk
        exact absurd hk (by simp)
  exact (key C h).1

/-- **Deadline reaping escapes the timed graph** ([TIME-013] against [VER-023]). A late
executor marks `b`; no class of the timed graph does, and no run of the Time Petri net
semantics does. A closed timed graph reporting `unreachable(b)` as `SPURIOUS_UNDER_TIMING`
speaks about the semantics without lateness. It is also what Route B answered before the
lateness fix, which built this graph for marking properties. -/
theorem reaping_escapes_timed_graph (tol : ℚ) {eps : ℚ} (heps0 : 0 ≤ eps) (heps : eps < 5) :
    (∃ s, LateReach netRP reapRP tol m0RP s ∧ s.m 2 = 1) ∧
      (∃ C0, initCls netRP (fun _ => none) eps m0RP = some C0 ∧
        ∀ C, Relation.ReflTransGen (Edge netRP (fun _ => none) eps) C0 C → C.m 2 = 0) ∧
      ∀ s, TReach netRP m0RP s → s.m 2 = 0 := by
  obtain ⟨C0, h0, -, -⟩ := init_sound netRP_wf co_none_wf heps0 m0RP
  refine ⟨late_executor_marks_b tol, ⟨C0, h0, fun C h => graphRP_never_marks_b heps h0 h⟩,
    fun s hs => ?_⟩
  obtain ⟨C, hC, hin, -, -⟩ := timed_run_sound netRP_wf co_none_wf heps0 h0 hs
  rw [hin.1]
  exact graphRP_never_marks_b heps h0 hC

/-- **The relaxed graph catches it**: the timed graph of `relax netRP` reaches a class marking
`b` (`Late.late_run_sound` applied to the late run). -/
theorem reaping_witness_in_relaxed_graph (tol : ℚ) {eps : ℚ} (heps : 0 ≤ eps) :
    ∃ C0, initCls (relax netRP) (fun _ => none) eps m0RP = some C0 ∧
      ∃ C, Relation.ReflTransGen (Edge (relax netRP) (fun _ => none) eps) C0 C ∧ C.m 2 = 1 := by
  have hE : ∀ i, 0 ≤ eftOf netRP i := fun i => (netRP_wf i).1
  obtain ⟨C0, h0, -, -⟩ := init_sound (timingWF_relax hE) co_none_wf heps m0RP
  obtain ⟨s, hs, hb⟩ := late_executor_marks_b tol
  obtain ⟨C, hC, hm, -⟩ := late_run_sound hE co_none_wf heps h0 hs
  exact ⟨C0, h0, C, hC, by rw [hm]; exact hb⟩

/-! ### Where a late executor rests -/

/-- `TimedCycle.lean`'s witness as a net: `t : p → q`, `window(3, 5)`, `M₀ = {p}`. -/
def netQ : TNet :=
  [ { tr := { name := "t", inputs := [⟨0, .one, none⟩], inhibitors := [], reads := [], resets := [] },
      rows := [[1]], eft := 3, lft := ((5 : ℚ) : Bound) } ]

def m0Q : AMarking := fun q => if q = 0 then 1 else 0

/-- `t` is a `window`, so it is reaped. -/
def tmsQ : Nat → Timing
  | 0 => .window 3000 5000
  | _ => .immediate

def reapQ : Nat → Bool := fun i => (tmsQ i).reapable

theorem netQ_wf : TimingWF netQ := by
  intro i
  match i with
  | 0 => exact ⟨by simp only [eftOf, netQ, List.getElem?_cons_zero]; norm_num, by
      simp only [eftOf, lftOf, netQ, List.getElem?_cons_zero]
      exact WithTop.coe_le_coe.mpr (by norm_num)⟩
  | i + 1 => exact ⟨le_refl _, by simp [eftOf, lftOf, netQ]⟩

theorem en_netQ_lt {a : AMarking} {i : Nat} (h : en netQ a i = true) : i = 0 := by
  have := en_lt h
  simp only [netQ, List.length_cons, List.length_nil] at this
  omega

/-- **A late executor rests where the timed graph moves on.** With a tolerance below `2`
seconds, a wake at `t = 10` reaps `t`: the executor rests at `{p}` (`LateQuiescent`). Every
class of the timed graph at `{p}` has a successor, so the graph's quiescence reading misses the
rest; the relaxed graph has a class at `{p}` whose clocks are all reapable, which is what
`Late.late_quiescence_sound` flags. -/
theorem late_rest_witness (tol : ℚ) (htol : tol < 5) :
    (∃ s, LateReach netQ reapQ tol m0Q s ∧ LateQuiescent netQ s ∧ s.m = m0Q) ∧
      (∀ C0, initCls netQ (fun _ => none) 0 m0Q = some C0 → ∀ C,
        Relation.ReflTransGen (Edge netQ (fun _ => none) 0) C0 C → C.m = m0Q →
          succList netQ (fun _ => none) 0 C ≠ []) ∧
      ∃ C0, initCls (relax netQ) (fun _ => none) 0 m0Q = some C0 ∧
        ∃ C, Relation.ReflTransGen (Edge (relax netQ) (fun _ => none) 0) C0 C ∧ C.m = m0Q ∧
          ∀ c ∈ C.cs, reapQ c = true := by
  have h1 := LateStep.delay (N := netQ) (reapable := reapQ) (tol := tol)
    ⟨m0Q, fun _ => 0, fun _ => false⟩ 10 (by norm_num)
  have hlt : lftOf netQ 0 + ((tol : ℚ) : Bound) < (((0 : ℚ) + 10 : ℚ) : Bound) := by
    simp only [lftOf, netQ, List.getElem?_cons_zero]
    rw [← WithTop.coe_add, WithTop.coe_lt_coe]
    linarith
  have hrest : ∃ s, LateReach netQ reapQ tol m0Q s ∧ LateQuiescent netQ s ∧ s.m = m0Q := by
    refine ⟨_, Relation.ReflTransGen.single h1, fun i hi => ?_, rfl⟩
    have hi0 := en_netQ_lt hi
    subst hi0
    have hen : en netQ m0Q 0 = true := by decide
    have hdec : decide (lftOf netQ 0 + ((tol : ℚ) : Bound) < (((0 : ℚ) + 10 : ℚ) : Bound)) = true :=
      decide_eq_true hlt
    simp only [hen, Bool.false_or, Bool.true_and, hdec, Bool.and_true]
    rfl
  refine ⟨hrest, fun C0 h0 C hC hm hnil => ?_, ?_⟩
  · have hrows : ∀ i, i < netQ.length → rowsOf netQ i ≠ [] := by
      intro i hi
      simp only [netQ, List.length_cons, List.length_nil] at hi
      interval_cases i
      simp [rowsOf, netQ]
    have := (reachable_quiescent_iff_dead netQ_wf co_none_wf hrows h0 hC).mp hnil 0
    rw [hm] at this
    revert this
    decide
  · have hE : ∀ i, 0 ≤ eftOf netQ i := fun i => (netQ_wf i).1
    obtain ⟨C0, h0, -, -⟩ := init_sound (timingWF_relax hE) co_none_wf le_rfl m0Q
    obtain ⟨s, hs, hq, hm⟩ := hrest
    obtain ⟨C, hC, hmC, hall⟩ := late_quiescence_sound hE co_none_wf le_rfl h0 hs hq
    exact ⟨C0, h0, C, hC, hmC.trans hm, hall⟩

/-! ## 3. A count-enabled, name-disabled ν-join bounds time in the graph but not in the executor

Route B's name-aware graph (`name_state_class_graph.rs::build_until`) reuses `compute_successor`
for its base layer: the clock list is the **count**-enabled set (`find_enabled_transitions`), so
a ν-join whose inputs hold tokens but share no name carries a clock and its `lft` bounds every
other firing, although the executor never enables it ([NU-020]: a join is enabled only on a
shared name) and it has no clock there.

**What is modelled.** `BlockedStep` is the Time Petri net semantics in which some count-enabled
transitions are never enabled (`blocked`): they neither fire nor bound time. The theorem is
stated over the plain `Edge` graph of a net **without** ν, with `blocked` standing in for "never
name-enabled". It does not model `build_until`'s name layer, its name-keyed dedup, or the
[NU-052] prune, so it shows that a clock the executor does not have excludes an executor run
from the count-based graph; it does not show that Route B's verdict is wrong.

`name_disabled_join_escapes` reuses the reaping witness with `t1` read as that join (never
name-enabled): the executor marks `b` at `t = 10` without being late, while every class of the
count-based graph has `b = 0`.

**Rust status: fixed (2026-09-29).** `build_until` now computes each name step's base successor
with `compute_successor_gated`, whose gates are `name_enabled` on the intermediate and the new
name layers: a join whose correlated inputs share no name holds no clock, its clock restarts
when a firing takes its bound name out of an input, and starts fresh when its inputs first share
a name. On the net below the strict (`assume_no_reaping`) verdict for `unreachable(BAD)` is now
`Violated`. The rest of this paragraph is the pre-fix reproduction. A scratch crate outside the
repository (against the working tree) builds `forkA : sourceA → branchA`, `forkB : sourceB → branchB`
(`deadline(1)`, their actions write the names `"a"` and `"b"`); `join : branchA + branchB →
merged`, `window(0, 5)`, matching both inputs on the string; `watchdog : W → BAD`,
`delayed(10)`; `M₀ = {sourceA, sourceB, W}`. `SmtVerifier` on `unreachable(BAD)` returns
`Proven { method: "ν name-partition SCG (NU-050, Route B)" }` with 4 name-partition classes,
while `BitmapNetExecutor::run_sync` on the same net ends with `BAD = 1`, `merged = 0`. With
the join `immediate()` Route B returns `Violated`, `TIMED_EXACT`. The finding is not in
`research/net-metrics/review/lean-gaps/FOLLOWUPS.md`. The model here still has no name layer, so
the fix itself is described, not proved: the gated successor is `compute_successor` with the
clock set filtered by `name_enabled` (`Succ.lean`, the note on `compute_successor_gated`). -/

/-- The semantics with some count-enabled transitions never enabled. -/
inductive BlockedStep (N : TNet) (blocked : Nat → Bool) : TState → TState → Prop
  | delay (s : TState) (δ : ℚ) (hδ : 0 ≤ δ)
      (hurg : ∀ i, en N s.m i = true → blocked i = false →
        ((s.ν i + δ : ℚ) : Bound) ≤ lftOf N i) :
      BlockedStep N blocked s ⟨s.m, fun i => s.ν i + δ⟩
  | fire (s : TState) (f : Nat) (d : Deposit) (hen : en N s.m f = true)
      (hnb : blocked f = false) (hready : eftOf N f ≤ s.ν f) (hd : d ∈ rowsOf N f) :
      BlockedStep N blocked s
        ⟨fireAD s.m (trOf N f) d, fun i => if persists N s.m f d i then s.ν i else 0⟩

/-- **A name-disabled join's deadline excludes a run the executor makes** (model level: the
count-based graph of a net without ν, see the section comment). -/
theorem name_disabled_join_escapes {eps : ℚ} (heps0 : 0 ≤ eps) (heps : eps < 5) :
    (∃ s, Relation.ReflTransGen (BlockedStep netRP fun i => i == 0) (s0 m0RP) s ∧ s.m 2 = 1) ∧
      ∃ C0, initCls netRP (fun _ => none) eps m0RP = some C0 ∧
        ∀ C, Relation.ReflTransGen (Edge netRP (fun _ => none) eps) C0 C → C.m 2 = 0 := by
  obtain ⟨C0, h0, -, -⟩ := init_sound netRP_wf co_none_wf heps0 m0RP
  refine ⟨?_, C0, h0, fun C h => graphRP_never_marks_b heps h0 h⟩
  have h1 : BlockedStep netRP (fun i => i == 0) (s0 m0RP) ⟨m0RP, fun _ => 10⟩ := by
    have := BlockedStep.delay (N := netRP) (blocked := fun i => i == 0) (s0 m0RP) 10
      (by norm_num) (fun i hi hnb => by
        rcases en_netRP_lt hi with rfl | rfl
        · exact absurd hnb (by decide)
        · simp only [lftOf, netRP, s0, List.getElem?_cons_succ, List.getElem?_cons_zero]
          exact WithTop.coe_le_coe.mpr (by norm_num))
    simpa [s0] using this
  have h2 := BlockedStep.fire (N := netRP) (blocked := fun i => i == 0) ⟨m0RP, fun _ => 10⟩ 1 [2]
    (by decide) (by decide) (by simp [eftOf, netRP]) (by simp [rowsOf, netRP])
  refine ⟨_, Relation.ReflTransGen.tail (Relation.ReflTransGen.single h1) h2, ?_⟩
  decide

end Reaping

/-! ## 4. Action duration

The graph deposits a firing's outputs at the instant it fires. An action that takes time
deposits later: consume at the start, deposit at completion, other firings in between
(`run_async`; `flag_clock_restarts`'s doc: "An asynchronous action's outputs are not there yet").
`DurStep` is an **on-time** executor (strong urgency, as `TStep`) with action durations `dur`:
`start` consumes and keeps the clocks of the transitions enabled before and in the intermediate
marking; `complete` deposits a pending row (any of them, once its remaining time is `0`) and
keeps the clocks of the transitions enabled before and after.

Witness (`netAD`): `t0 : p → a`, `deadline(5)`, whose action takes 20 s; `t1 : q → b`,
`delayed(10)`, inhibited by `a`; `M₀ = {p, q}`. On time, `t0` fires at `0`; in `TStep` and in the
graph `a` is marked at once and `t1` never fires. With the duration, `a` arrives at `20` and
`t1` fires at `10`. [VER-010] AC4 names only overlapping actions; one asynchronous action is
enough. -/

section Duration

/-- An executor state with the rows of the actions in flight and their remaining time. -/
structure DState where
  m : AMarking
  ν : Nat → ℚ
  pend : List (Deposit × ℚ)

/-- **An on-time executor whose actions take time.** -/
inductive DurStep (N : TNet) (dur : Nat → ℚ) : DState → DState → Prop
  | delay (s : DState) (δ : ℚ) (hδ : 0 ≤ δ)
      (hurg : ∀ i, en N s.m i = true → ((s.ν i + δ : ℚ) : Bound) ≤ lftOf N i)
      (hpend : ∀ x ∈ s.pend, δ ≤ x.2) :
      DurStep N dur s ⟨s.m, fun i => s.ν i + δ, s.pend.map fun x => (x.1, x.2 - δ)⟩
  | start (s : DState) (f : Nat) (d : Deposit) (hen : en N s.m f = true)
      (hready : eftOf N f ≤ s.ν f) (hd : d ∈ rowsOf N f) :
      DurStep N dur s ⟨inter s.m (trOf N f),
        fun i => if en N s.m i && i != f && en N (inter s.m (trOf N f)) i then s.ν i else 0,
        s.pend ++ [(d, dur f)]⟩
  | complete (s : DState) (j : Nat) (d : Deposit) (r : ℚ) (hj : s.pend[j]? = some (d, r))
      (hr : r ≤ 0) :
      DurStep N dur s ⟨fun p => s.m p + d.count p,
        fun i => if en N s.m i && en N (fun p => s.m p + d.count p) i then s.ν i else 0,
        s.pend.eraseIdx j⟩

/-- Places `p = 0`, `q = 1`, `a = 2`, `b = 3`. -/
def netAD : TNet :=
  [ { tr := { name := "t0", inputs := [⟨0, .one, none⟩], inhibitors := [], reads := [], resets := [] },
      rows := [[2]], eft := 0, lft := ((5 : ℚ) : Bound) },
    { tr := { name := "t1", inputs := [⟨1, .one, none⟩], inhibitors := [2], reads := [],
              resets := [] },
      rows := [[3]], eft := 10, lft := ((3153600000 : ℚ) : Bound) } ]

def m0AD : AMarking := fun q => if q = 0 then 1 else if q = 1 then 1 else 0

/-- `t0`'s action takes 20 s, `t1`'s none. -/
def durAD : Nat → ℚ := fun i => if i = 0 then 20 else 0

theorem netAD_faithful : FromTimings netAD tmsRP := by
  intro i hi
  simp only [netAD, List.length_cons, List.length_nil] at hi
  interval_cases i
  · refine ⟨?_, ?_⟩
    · simp only [eftOf, netAD, List.getElem?_cons_zero, eftT, tmsRP, Timing.earliest]; norm_num
    · simp only [lftOf, netAD, List.getElem?_cons_zero, lftT, tmsRP, Timing.latest]
      congr 1; norm_num
  · refine ⟨?_, ?_⟩
    · simp only [eftOf, netAD, List.getElem?_cons_succ, List.getElem?_cons_zero, eftT, tmsRP,
        Timing.earliest]; norm_num
    · simp only [lftOf, netAD, List.getElem?_cons_succ, List.getElem?_cons_zero, lftT, tmsRP,
        Timing.latest]
      congr 1; norm_num [maxDurationMs]

theorem netAD_wf : TimingWF netAD := by
  intro i
  match i with
  | 0 => exact ⟨le_refl _, by simp [eftOf, lftOf, netAD]⟩
  | 1 => exact ⟨by simp [eftOf, netAD], by
      simp only [eftOf, lftOf, netAD, List.getElem?_cons_succ, List.getElem?_cons_zero]
      exact WithTop.coe_le_coe.mpr (by norm_num)⟩
  | i + 2 => exact ⟨le_refl _, by simp [eftOf, lftOf, netAD]⟩

theorem en_netAD_lt {a : AMarking} {i : Nat} (h : en netAD a i = true) : i = 0 ∨ i = 1 := by
  have := en_lt h
  simp only [netAD, List.length_cons, List.length_nil] at this
  omega

/-- The on-time executor with `t0`'s 20 s action marks `b`. -/
theorem duration_marks_b :
    ∃ s, Relation.ReflTransGen (DurStep netAD durAD) ⟨m0AD, fun _ => 0, []⟩ s ∧ s.m 3 = 1 := by
  refine ⟨_, ((((Relation.ReflTransGen.single
      (DurStep.start (N := netAD) (dur := durAD) ⟨m0AD, fun _ => 0, []⟩ 0 [2] ?_ ?_ ?_)).tail
      (DurStep.delay _ 10 (by norm_num) ?_ ?_)).tail
      (DurStep.start _ 1 [3] ?_ ?_ ?_)).tail
      (DurStep.complete _ 1 [3] 0 ?_ le_rfl)), ?_⟩
  · decide
  · simp [eftOf, netAD]
  · simp [rowsOf, netAD]
  · intro i hi
    rcases en_netAD_lt hi with rfl | rfl
    · exact absurd hi (by decide)
    · simp only [ite_self, zero_add, lftOf, netAD, List.getElem?_cons_succ,
        List.getElem?_cons_zero]
      exact WithTop.coe_le_coe.mpr (by norm_num)
  · norm_num [durAD]
  · decide
  · simp only [ite_self, zero_add, eftOf, netAD, List.getElem?_cons_succ, List.getElem?_cons_zero]
    norm_num
  · simp [rowsOf, netAD]
  · simp [durAD]
  · decide

theorem initAD_spec {eps : ℚ} {C0 : Cls} (h0 : initCls netAD (fun _ => none) eps m0AD = some C0) :
    C0.m = m0AD ∧ C0.cs = [0, 1] ∧ C0.D 1 2 ≤ ((-5 : ℚ) : Bound) := by
  obtain ⟨hm, hcs, hD⟩ := initCls_eq h0
  have hcs' : C0.cs = [0, 1] := by rw [hcs]; decide
  refine ⟨hm, hcs', ?_⟩
  rw [hD, hcs']
  refine (canonN_le _ (by simp) (by simp)).trans ?_
  simp only [ltpPre, show (1 : Nat) ≠ 0 by omega, false_and, if_false]
  refine (canonN_le_walk _ (k := 0) (by simp) (by simp) (by simp)).trans ?_
  have hB10 : createPre [0, 1].length ([0, 1].map (eftOf netAD)) ([0, 1].map (lftOf netAD)) 1 0 =
      ((5 : ℚ) : Bound) := by
    simp [createPre, lftOf, netAD]
  have hB02 : createPre [0, 1].length ([0, 1].map (eftOf netAD)) ([0, 1].map (lftOf netAD)) 0 2 =
      ((-10 : ℚ) : Bound) := by
    simp [createPre, eftOf, netAD]
  rw [hB10, hB02, ← WithTop.coe_add, WithTop.coe_le_coe]
  norm_num

theorem succAD_t1_none {eps : ℚ} (heps : eps < 5) {C0 : Cls}
    (h0 : initCls netAD (fun _ => none) eps m0AD = some C0) (d : Deposit) :
    succ netAD (fun _ => none) eps C0 1 d = none := by
  obtain ⟨-, hcs0, hD12⟩ := initAD_spec h0
  have hflag : FlaggedN eps (C0.cs.length + 1) (constrainPre C0.cs.length 1 C0.D) := by
    rw [hcs0]
    refine flaggedN_of_cycle (a := 1) (k := 2) (by simp) (by simp) ?_
    have h12 : constrainPre [0, 1].length 1 C0.D 1 2 = C0.D 1 2 := by
      simp [constrainPre]
    have h21 : constrainPre [0, 1].length 1 C0.D 2 1 ≤ ((0 : ℚ) : Bound) := by
      simp only [constrainPre, List.length_cons, List.length_nil]
      rw [if_pos (by decide)]
      exact min_le_right _ _
    rw [h12]
    calc C0.D 1 2 + constrainPre [0, 1].length 1 C0.D 2 1
        ≤ ((-5 : ℚ) : Bound) + ((0 : ℚ) : Bound) := add_le_add hD12 h21
      _ = ((-5 : ℚ) : Bound) := by rw [← WithTop.coe_add]; norm_num
      _ < ((-eps : ℚ) : Bound) := WithTop.coe_lt_coe.mpr (by linarith)
  have hk : C0.cs[1]? = some 1 := by rw [hcs0]; rfl
  unfold succ succWith
  rw [hk]
  simp only
  unfold zoneStep
  rw [if_pos hflag]
  rfl

theorem graphAD_never_marks_b {eps : ℚ} (heps : eps < 5) {C0 : Cls}
    (h0 : initCls netAD (fun _ => none) eps m0AD = some C0) {C : Cls}
    (h : Relation.ReflTransGen (Edge netAD (fun _ => none) eps) C0 C) : C.m 3 = 0 := by
  obtain ⟨hm0, hcs0, -⟩ := initAD_spec h0
  have key : ∀ C, Relation.ReflTransGen (Edge netAD (fun _ => none) eps) C0 C →
      C.m 3 = 0 ∧ (C = C0 ∨ C.cs = []) := by
    intro C h
    induction h with
    | refl => exact ⟨by rw [hm0]; rfl, Or.inl rfl⟩
    | tail _ hstep ih =>
      obtain ⟨-, hor⟩ := ih
      simp only [Edge, succList, succListWith, List.mem_flatMap, List.mem_range,
        List.mem_filterMap] at hstep
      obtain ⟨k, hk, d, hd, hs⟩ := hstep
      rcases hor with rfl | hnil
      · rw [hcs0] at hk hd
        simp only [List.length_cons, List.length_nil] at hk
        rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
        · obtain ⟨f, hkf, hmC⟩ := succWith_marking hs
          rw [hcs0] at hkf
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hkf
          subst hkf
          simp only [List.getD_cons_zero, rowsOf, netAD, List.getElem?_cons_zero,
            List.mem_singleton] at hd
          subst hd
          have hwf := (succ_wf co_none_wf hs).1
          refine ⟨by rw [hmC, hm0]; decide, Or.inr ?_⟩
          refine List.eq_nil_iff_forall_not_mem.mpr fun c hc => ?_
          have hen := (hwf.mem c).mp hc
          rw [hmC, hm0] at hen
          rcases en_netAD_lt hen with rfl | rfl <;> revert hen <;> decide
        · have hn := succAD_t1_none heps h0 d
          unfold succ at hn
          rw [hn] at hs
          exact absurd hs (by simp)
      · rw [hnil] at hk
        exact absurd hk (by simp)
  exact (key C h).1

/-- **Action duration escapes the timed graph.** An on-time executor whose `t0` action takes
20 s marks `b`; no class of the timed graph does, and no `TStep` run does. -/
theorem action_duration_escapes {eps : ℚ} (heps0 : 0 ≤ eps) (heps : eps < 5) :
    (∃ s, Relation.ReflTransGen (DurStep netAD durAD) ⟨m0AD, fun _ => 0, []⟩ s ∧ s.m 3 = 1) ∧
      (∃ C0, initCls netAD (fun _ => none) eps m0AD = some C0 ∧
        ∀ C, Relation.ReflTransGen (Edge netAD (fun _ => none) eps) C0 C → C.m 3 = 0) ∧
      ∀ s, TReach netAD m0AD s → s.m 3 = 0 := by
  obtain ⟨C0, h0, -, -⟩ := init_sound netAD_wf co_none_wf heps0 m0AD
  refine ⟨duration_marks_b, ⟨C0, h0, fun C h => graphAD_never_marks_b heps h0 h⟩, fun s hs => ?_⟩
  obtain ⟨C, hC, hin, -, -⟩ := timed_run_sound netAD_wf co_none_wf heps0 h0 hs
  rw [hin.1]
  exact graphAD_never_marks_b heps h0 hC

end Duration

/-! ## 5. `delayed(after > MAX_DURATION_MS)`

Before the R6 fix `delayed(after_ms)` checked nothing. The shipped `delayed` (`timing.rs:47-53`)
asserts `after_ms <= MAX_DURATION_MS`, so the net below can no longer be built
(`netBig_rejected`); what follows is the pre-fix behaviour. `latest()` is `MAX_DURATION_MS`, so
`delayed(MAX_DURATION_MS + 1)` has the graph interval `[MAX + 0.001, MAX]` seconds. In the Rust,
`Dbm::create` flags that zone empty; `initial_state_class` keeps the class anyway, its successors
are all empty and dropped (`build_with_options`, `successor.is_empty()`), and the graph closes
after one class. The executor never forces a `delayed` transition (`has_deadline` is false) and
fires it once `earliest ≤ elapsed` (`collect_ready_general`).

Observed on the working tree (2026-09-28, scratch crate, not committed): `t : p → b`,
`delayed(MAX_DURATION_MS + 1)`, `M₀ = {p}`. The timed graph has 1 class, `complete = true`,
0 edges. With the timed check on, `unreachable(b)` is `Violated` / `SPURIOUS_UNDER_TIMING`, and
`deadlockFree` is `Violated` / `TIMED_CONFIRMED` with the one-state trace `{p:1}`: a timed
deadlock the net does not have, which [VER-023] forbids. -/

section PastMax

/-- `t : p → b`, `delayed(MAX_DURATION_MS + 1)`, in the graph's reading. Places `p = 0`,
`b = 1`. -/
def netBig : TNet :=
  [ mkT { name := "t", inputs := [⟨0, .one, none⟩], inhibitors := [], reads := [], resets := [] }
      [[1]] (.delayed (maxDurationMs + 1)) ]

def m0B : AMarking := fun q => if q = 0 then 1 else 0

theorem netBig_faithful : FromTimings netBig fun _ => .delayed (maxDurationMs + 1) := by
  intro i hi
  simp only [netBig, List.length_cons, List.length_nil] at hi
  interval_cases i
  simp [eftOf, lftOf, netBig, mkT]

theorem eft_netBig : eftOf netBig 0 = 3153600000001 / 1000 := by
  simp [eftOf, netBig, mkT, eftT, Timing.earliest, maxDurationMs]

theorem lft_netBig : lftOf netBig 0 = ((3153600000 : ℚ) : Bound) := by
  simp only [lftOf, netBig, mkT, lftT, Timing.latest, maxDurationMs, List.getElem?_cons_zero]
  congr 1
  norm_num

/-- Premise 6 fails. -/
theorem netBig_not_wf : ¬ TimingWF netBig := by
  intro h
  have := (h 0).2
  rw [eft_netBig, lft_netBig, WithTop.coe_le_coe] at this
  norm_num at this

/-- The model flags the initial zone empty at every `eps < 1/1000`, the Rust `1e-9` included. -/
theorem netBig_initCls_none {eps : ℚ} (heps : eps < 1 / 1000) :
    initCls netBig (fun _ => none) eps m0B = none := by
  have hcs : reorder (fun _ => none) (enabledIds netBig m0B) = [0] := by decide
  unfold initCls
  simp only [hcs]
  rw [if_pos]
  refine flaggedN_of_cycle (a := 0) (k := 1) (by simp) (by simp) ?_
  have e01 : createPre [0].length ([0].map (eftOf netBig)) ([0].map (lftOf netBig)) 0 1 =
      ((-(3153600000001 / 1000 : ℚ) : ℚ) : Bound) := by
    simp [createPre, eft_netBig]
  have e10 : createPre [0].length ([0].map (eftOf netBig)) ([0].map (lftOf netBig)) 1 0 =
      ((3153600000 : ℚ) : Bound) := by
    simp [createPre, lft_netBig]
  rw [e01, e10, ← WithTop.coe_add, WithTop.coe_lt_coe]
  linarith

/-- `TStep` time-locks: the clock can never reach `eft`, so `b` is never marked. -/
theorem netBig_time_locks {s : TState} (hs : TReach netBig m0B s) :
    s.m = m0B ∧ ((s.ν 0 : ℚ) : Bound) ≤ lftOf netBig 0 := by
  induction hs with
  | refl =>
    refine ⟨rfl, ?_⟩
    show (((0 : ℚ) : ℚ) : Bound) ≤ _
    rw [lft_netBig]
    exact WithTop.coe_le_coe.mpr (by norm_num)
  | tail _ hstep ih =>
    obtain ⟨hm, hν⟩ := ih
    cases hstep with
    | delay δ hδ hurg => exact ⟨hm, hurg 0 (by rw [hm]; decide)⟩
    | fire f d hen hready hd =>
      exfalso
      have hf : f = 0 := by
        have := en_lt hen
        simp only [netBig, List.length_cons, List.length_nil] at this
        omega
      subst hf
      rw [lft_netBig, WithTop.coe_le_coe] at hν
      rw [eft_netBig] at hready
      linarith

/-- **The shipped constructor rejects `netBig`'s timing** (`delayed` panics, R6 fix). -/
theorem netBig_rejected : ¬ (Timing.delayed (maxDurationMs + 1)).Valid := by
  simp [Timing.Valid]

/-- **`delayed(MAX_DURATION_MS + 1)` escapes the graph** (before the R6 fix). Premise 6 fails; the model's initial
class is flagged empty (the Rust keeps it, with no successors); every `TStep` run keeps `b = 0`;
the executor, which reads a `delayed` transition's upper bound as `⊤` (`relax`: nothing forces
it), marks `b` on time; and the relaxed graph has a class marking `b`. -/
theorem delayed_past_max_escapes {eps : ℚ} (heps0 : 0 ≤ eps) (heps : eps < 1 / 1000) :
    ¬ TimingWF netBig ∧ initCls netBig (fun _ => none) eps m0B = none ∧
      (∀ s, TReach netBig m0B s → s.m 1 = 0) ∧
      (∃ s, TReach (relax netBig) m0B s ∧ s.m 1 = 1) ∧
      ∃ C0, initCls (relax netBig) (fun _ => none) eps m0B = some C0 ∧
        ∃ C, Relation.ReflTransGen (Edge (relax netBig) (fun _ => none) eps) C0 C ∧ C.m 1 = 1 := by
  have hE : ∀ i, 0 ≤ eftOf netBig i := by
    intro i
    match i with
    | 0 => rw [eft_netBig]; norm_num
    | i + 1 => simp [eftOf, netBig]
  have hrun : ∃ s, TReach (relax netBig) m0B s ∧ s.m 1 = 1 := by
    refine ⟨_, Relation.ReflTransGen.tail (Relation.ReflTransGen.single
      (TStep.delay (N := relax netBig) (s0 m0B) (eftOf netBig 0) (hE 0)
        (fun i _ => by rw [lftOf_relax]; exact le_top)))
      (TStep.fire _ 0 [1] ?_ ?_ ?_), ?_⟩
    · show en (relax netBig) m0B 0 = true
      rw [en_relax]
      decide
    · show eftOf (relax netBig) 0 ≤ 0 + eftOf netBig 0
      rw [eftOf_relax, zero_add]
    · rw [rowsOf_relax]; simp [rowsOf, netBig, mkT]
    · show fireAD m0B (trOf (relax netBig) 0) [1] 1 = 1
      rw [trOf_relax]
      decide
  refine ⟨netBig_not_wf, netBig_initCls_none heps, fun s hs => by
    rw [(netBig_time_locks hs).1]; rfl, hrun, ?_⟩
  obtain ⟨C0, h0, -, -⟩ := init_sound (timingWF_relax hE) co_none_wf heps0 m0B
  obtain ⟨s, hs, hb⟩ := hrun
  obtain ⟨C, hC, hin, -, -⟩ := timed_run_sound (timingWF_relax hE) co_none_wf heps0 h0 hs
  exact ⟨C0, h0, C, hC, by rw [← hin.1]; exact hb⟩

end PastMax

end Libpetri.Novel.TimedScg
