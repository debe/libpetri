import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryTime
import Libpetri.Spec.Req.TIME_010
import Libpetri.Spec.Text.TIME_005

set_option linter.missingDocs true

/-!
# TIME-005: Window timing (`spec/03-timing.md`)

The requirement is a predicate over an abstract timed step relation `R : TRel N` (glossary
`GlossaryTime.lean`), for every transition whose timing is `Window(earliest, latest)`. The
evidence theorems check it against the timed reference step (`RefTStep`), against a relation
that fires without looking at the clock, and against mutant readings: an executor that reaps a
window already at its bound plus the tolerance instead of strictly past it, one that ignores the
tolerance, one that enforces a window softly, as `Exact` is, and never reaps it, and two that
drop or restart the clock of `u` when a transition of another name fires and leaves `u` enabled
throughout (a reap or a restart hidden in a firing).

The lemmas of the section `Lines` are stated for any policy (`RefTStepW P`), so that every
mutant reuses them and needs only its counterexample.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Novel.TimedScg (Timing maxDurationMs)

/-! ## TIME-005: Window timing -/

requirement TIME_005
  id "TIME-005"
  title "Window Timing"
  kind T
  scope "all executors"
  source verbatim "spec/03-timing.md"
  covers TIME_005.s1, TIME_005.s2, TIME_005.s3
  reading "For every timed net X, every transition u and all bounds e and l such that u's timing is Window(e, l):"
          "no firing of u starts from a state in which u is armed and its elapsed time is below e (this restates [TIME-010] line 4 for this timing);"
          "from every state in which u, the net's transition of its name, is armed and its elapsed time is at least e and at most l plus the tolerance, every reference firing of u is a step, to the marking that firing gives;"
          "no firing of u starts from a state in which u is armed and its elapsed time is greater than l plus the tolerance;"
          "from every state in which u, the net's transition of its name, is armed and its elapsed time is greater than l plus the tolerance, a reap of u is a step (the 'shall reap' is encoded as the reap being available; that it is taken is deferred, see below);"
          "a reap of u starts from a state in which u is armed and its elapsed time is greater than l plus the tolerance, and leaves u reaped: enabled and not armed;"
          "when u is the net's transition of its name, its clock is framed (ClockFrame): when the net's names are distinct, no step but a reap of u disarms u while it stays enabled, a firing of u itself included, and a delay, the reap of a transition of another name, and a firing of a transition of another name that leaves u enabled in its intermediate marking and after it keep u's stamp."
  assumes "A step relates two states of the executor (glossary: TSt), each holding a marking, the reading of the firing clock and a stamp per transition name; a step is a delay of the clock, a firing or a reap (TRel). Firings are atomic. Armed, Elapsed time, Deadline tolerance, Expired, Ready and Reaped are the glossary terms (GlossaryTime.lean); bounds are in milliseconds."
          "Expired is read with ruling D4: the bound is latest plus the deadline tolerance, and the test is strict, as MUST. A Window transition that is armed is expired exactly when its elapsed time is greater than l plus the tolerance (Window is reapable), which is how lines 2 to 5 spell 'until it is expired' and 'exceeds'."
          "Line 2 reads 'its timing shall not stop it from being ready until it is expired' on the step relation: a Window transition that is armed, past e and not expired is ready (glossary: Ready), and a ready transition can take every reference firing it has, as Covers says for all transitions. Choosing among several ready transitions (priority, FIFO) is [EXEC-002] and [TIME-014]; the atomic step relation of Phase 1 has no such choice."
          "Lines 3 to 5 are the 'If ... then shall reap' sentence: past the bound u does not fire (line 3), a reap of it is a step (line 4), and a reap of u happens only strictly past the bound and leaves it reaped (line 5). The 'shall' of the sentence is encoded only as the reap being offered (line 4 is existential): a relation that lets the clock run on past the bound without reaping satisfies the block, because the atomic relation of Phase 1 lets a delay pass any bound (the executor may be late). That the reap is taken is the cycle loop's obligation ([EXEC-001], Phase 2), as below. Ignoring the tolerance (bound l instead of l plus the tolerance) is the mutant TIME_005_mutant_noTol_killed, a non-strict bound TIME_005_mutant_reapAt_killed. Rust and Java (one reading per cycle, shared by the deadline step and the firing pass: cycle_now, cycleNanos) and TypeScript (the deadline step and the pass share cycleNowMs) conform to line 3. A firing pass that takes a clock reading of its own, later than the deadline step's, and checks only the earliest bound there breaks it: a Window transition whose elapsed time passes l plus the tolerance between the two readings is not reaped and fires. That is the behaviour RD-16 in spec/runtime-defects.md recorded for Java's fireReadyGeneral."
          "Line 6 is the frame ClockFrame shared with TIME-003, TIME-004 and TIME-006 (GlossaryTime.lean); it keeps u's clock to the reap step and to the firings that disable u. Its first part, StaysArmed, says no step but a reap of u leaves u enabled and unarmed, a firing of u itself included: a firing of u that leaves u enabled re-arms it (TIME_005_forbids_selfDrop). Its other parts keep u's stamp across a delay, a reap of another name and a firing of another name that leaves u enabled throughout; the last is [TIME-012] line 2 specialised to u: without it a firing of an unrelated transition could drop u's clock, a reap hidden in a firing that disarms u before it expires (TIME_005_mutant_dropClean_killed), or restart it, so that a continuously enabled window escapes its bound (TIME_005_mutant_restart_killed). A firing that disables u in its intermediate marking or after it drops or restarts u's clock as [TIME-011] and [TIME-012] say, and which stamp a firing of u itself leaves (a fresh one) is [TIME-012] line 4; this block fixes neither. That a delay advances the clock by its length is [TIME-015] line 2. A reap labelled with a transition other than u that carries u's name is not constrained by line 5: it is excluded by [TIME-013] line 1 (only a transition of the net is reaped) together with NamesDistinct (ruling D10)."
          "AC2 (a transition still armed past latest plus the deadline tolerance does not fire after that bound; if it is still armed on the first cycle whose elapsed time is strictly greater than the bound, it is reaped in that cycle) is lines 2 to 5 and is not quoted: fireable up to the bound, not fireable past it (the first sentence), the reap offered in every state strictly past it and allowed in no other (the second sentence on the step relation). Both sentences speak of a transition still armed, so a competitor that disables u before its bound falsifies neither ([TIME-011] drops its clock). That the reap happens in the first such cycle is a property of the cycle loop ([EXEC-001] step 4), which the atomic step relation of Phase 1 does not have, and is deferred to Phase 2 (RefExec). Line 4 is the reap of u being available; TIME-013's last line states the same for every expired transition. Which event a reap emits is [TIME-013] and [EVT-009]."
          "AC1 (cannot fire before earliest) is line 1. AC3 (latest below earliest is rejected) and AC4 (earliest or latest above the maximum duration is rejected) are construction rules over Timing.Valid, the F reading of [TIME-001] AC4 with ruling D11: time005_construction states that Window(e, l) is valid exactly when e and l are at most the maximum duration and e is at most l, and time005_construction_examples checks the boundary cases."
          "The interval bullets (earliest bound e, latest bound l, hasDeadline true) are the Timing accessors (time005_interval); Window is reapable, unlike Exact ([TIME-006])."
          "The test derivation (Window(1s, 5s): not ready at 0.5s, ready at 2s, expired at 6s) is the nonvacuous example TIME_005_nonvacuous, in milliseconds with the default tolerance of 5 ms, which also checks both sides of the bound 5005, and fires an unrelated transition at T=500 that keeps u's stamp (line 6)."
  signoff "2026-11-13 4d99c46f6b5f098d ai"
  statement : ∀ {N : Type} [DecidableEq N], TRel N → Prop :=
    fun R => ∀ (X : TimedNet _) u e l, TimingOf X u = .window e l →
      (while (fun s => Armed s u ∧ Elapsed s u < e),
          never (fun s s' => ∃ d, R X s (.fire u d) s')) ∧
      (∀ s d m', InNet X u → Armed s u → e ≤ Elapsed s u → Elapsed s u ≤ l + Tolerance X →
          RefFire u s.m d m' → ∃ s', R X s (.fire u d) s' ∧ s'.m = m') ∧
      (while (fun s => Armed s u ∧ l + Tolerance X < Elapsed s u),
          never (fun s s' => ∃ d, R X s (.fire u d) s')) ∧
      (∀ s, InNet X u → Armed s u → l + Tolerance X < Elapsed s u →
          ∃ s', R X s (.reap u) s') ∧
      (on (fun s s' => R X s (.reap u) s'),
          shall (fun s s' => Armed s u ∧ l + Tolerance X < Elapsed s u ∧ Reaped s' u)) ∧
      (InNet X u → ClockFrame R X u)

/--
info: def Libpetri.Spec.TIME_005 : {N : Type} → [DecidableEq N] → TRel N → Prop :=
fun {N} [DecidableEq N] R =>
  ∀ (X : TimedNet N) (u : Reference.Trans N) (e l : ℕ),
    TimingOf X u = Timing.window e l →
      (while fun s => Armed s u ∧ Elapsed s u < e, never fun s s' => ∃ d, R X s (TLbl.fire u d) s') ∧
        (∀ (s : TSt N) (d : List N) (m' : N → ℕ),
            InNet X u →
              Armed s u →
                e ≤ Elapsed s u →
                  Elapsed s u ≤ l + Tolerance X → RefFire u s.m d m' → ∃ s', R X s (TLbl.fire u d) s' ∧ s'.m = m') ∧
          (while fun s => Armed s u ∧ l + Tolerance X < Elapsed s u, never fun s s' => ∃ d, R X s (TLbl.fire u d) s') ∧
            (∀ (s : TSt N), InNet X u → Armed s u → l + Tolerance X < Elapsed s u → ∃ s', R X s (TLbl.reap u) s') ∧
              (on fun s s' => R X s (TLbl.reap u) s', shall fun s s' =>
                  Armed s u ∧ l + Tolerance X < Elapsed s u ∧ Reaped s' u) ∧
                (InNet X u → ClockFrame R X u)
-/
#guard_msgs in #print TIME_005

/-! ### The lines, for any policy -/

section Lines

variable {N : Type} [DecidableEq N]

/-- Inversion of a reap step, under any policy: the reaped transition is in the net, the
policy calls it expired, and the step drops the stamp of its name and nothing else. -/
theorem time005_reap_inv {P : Policy N} {X : TimedNet N} {s s' : TSt N} {t : Trans N}
    (h : RefTStepW P X s (.reap t) s') :
    t ∈ X.net.transitions ∧ P.expired X s t = true ∧
      s' = { s with stamp := fun n => if n = t.core.name then none else s.stamp n } := by
  match h with
  | .reap _ _ _ ht hx => exact ⟨ht, hx, rfl⟩

/-- A reap, under any policy, leaves the reaped transition reaped if it was armed: the marking
stays, so it is still enabled, and its stamp is gone. -/
theorem time005_reap_reaped {P : Policy N} {X : TimedNet N} {s s' : TSt N} {u : Trans N}
    (h : RefTStepW P X s (.reap u) s') (ha : Armed s u) : Reaped s' u := by
  rw [(time005_reap_inv h).2.2]
  exact ⟨ha.1, fun h' => by simpa using h'.2⟩

/-- A transition of the net that is armed, past the policy's gate and not expired for it takes
every reference firing it has, under any policy. -/
theorem time005_fires {P : Policy N} {X : TimedNet N} {s : TSt N} {u : Trans N} {d : List N}
    {m' : N → Nat} (hu : InNet X u) (ha : Armed s u) (hg : P.gate X s u = true)
    (hx : P.expired X s u = false) (hf : RefFire u s.m d m') :
    ∃ s', RefTStepW P X s (.fire u d) s' ∧ s'.m = m' :=
  ⟨_, RefTStepW.fire X s u d m' (inNet_mem hu) hf ((armed_iff s u).1 ha) hg hx, rfl⟩

/-- The spec's gate is open for a transition whose earliest bound is at most its elapsed
time. -/
theorem time005_gate_open {X : TimedNet N} {s : TSt N} {t : Trans N}
    (h : (TimingOf X t).earliest ≤ Elapsed s t) : (refPolicy (N := N)).gate X s t = true := by
  simpa [refPolicy, elapsed_eq] using h

omit [DecidableEq N] in
/-- The spec's expiry test on a `Window(e, l)` transition: armed and elapsed time greater than
`l` plus the tolerance. -/
theorem time005_tExpired_window {X : TimedNet N} {s : TSt N} {u : Trans N} {e l : Nat}
    (hT : TimingOf X u = .window e l) :
    tExpired X s u = true ↔ Armed s u ∧ l + Tolerance X < Elapsed s u := by
  rw [← expired_iff]
  simp [Expired, Reapable, hT, Timing.reapable, Timing.latest]

/-- The delay and reap parts of the clock frame, for any policy. -/
theorem time005_keeps {P : Policy N} {X : TimedNet N} {u : Trans N} :
    (∀ δ, on (fun s s' => RefTStepW P X s (.delay δ) s'),
        shall (fun s s' => s'.stamp u.core.name = s.stamp u.core.name)) ∧
      (∀ t, t.core.name ≠ u.core.name → on (fun s s' => RefTStepW P X s (.reap t) s'),
        shall (fun s s' => s'.stamp u.core.name = s.stamp u.core.name)) :=
  ⟨fun _ _ _ h => frame_delay h _, fun _ hn _ _ h => frame_reapOther h (Ne.symm hn)⟩

/-- Line 1 for any policy with the spec's gate. -/
theorem time005_gate {P : Policy N} (hg : P.gate = refPolicy.gate) {X : TimedNet N}
    {u : Trans N} {e l : Nat} (hT : TimingOf X u = .window e l) :
    while (fun s => Armed s u ∧ Elapsed s u < e),
      never (fun s s' => ∃ d, RefTStepW P X s (.fire u d) s') := by
  intro s s' ⟨d, h⟩ ⟨_, hlt⟩
  have := time010_gate hg h
  rw [hT] at this
  exact absurd this (by simp [Timing.earliest]; omega)

/-- Lines 1 to 5 for any policy with the spec's gate and expiry test. -/
theorem time005_lines15 {P : Policy N} (hg : P.gate = refPolicy.gate)
    (hx : P.expired = refPolicy.expired) {X : TimedNet N} {u : Trans N} {e l : Nat}
    (hT : TimingOf X u = .window e l) :
    (while (fun s => Armed s u ∧ Elapsed s u < e),
        never (fun s s' => ∃ d, RefTStepW P X s (.fire u d) s')) ∧
      (∀ s d m', InNet X u → Armed s u → e ≤ Elapsed s u → Elapsed s u ≤ l + Tolerance X →
        RefFire u s.m d m' → ∃ s', RefTStepW P X s (.fire u d) s' ∧ s'.m = m') ∧
      (while (fun s => Armed s u ∧ l + Tolerance X < Elapsed s u),
        never (fun s s' => ∃ d, RefTStepW P X s (.fire u d) s')) ∧
      (∀ s, InNet X u → Armed s u → l + Tolerance X < Elapsed s u →
        ∃ s', RefTStepW P X s (.reap u) s') ∧
      (on (fun s s' => RefTStepW P X s (.reap u) s'),
        shall (fun s s' => Armed s u ∧ l + Tolerance X < Elapsed s u ∧ Reaped s' u)) := by
  have hx' : ∀ s, P.expired X s u = tExpired X s u := fun s => by rw [hx]; rfl
  refine ⟨time005_gate hg hT, fun s d m' hu ha hle hle' hf => ?_, fun s s' ⟨d, h⟩ hxs => ?_,
    fun s hu ha hlt => ?_, fun s s' h => ?_⟩
  · refine time005_fires hu ha (by rw [hg]; exact time005_gate_open (by rw [hT]; exact hle)) ?_ hf
    rw [hx']
    cases hxs : tExpired X s u
    · rfl
    · exact absurd ((time005_tExpired_window hT).1 hxs).2 (by omega)
  · have hf := (refTStepW_fire_inv h).2.2.2.2.1
    rw [hx', (time005_tExpired_window hT).2 hxs] at hf
    exact Bool.noConfusion hf
  · exact ⟨_, RefTStepW.reap X s u (inNet_mem hu)
      (by rw [hx']; exact (time005_tExpired_window hT).2 ⟨ha, hlt⟩)⟩
  · have hxs := (time005_reap_inv h).2.1
    rw [hx'] at hxs
    obtain ⟨ha, hlt⟩ := (time005_tExpired_window hT).1 hxs
    exact ⟨ha, hlt, time005_reap_reaped h ha⟩

end Lines

/-- The timed reference step satisfies TIME-005: a firing of a `Window(e, l)` transition passes
the spec's gate, so its elapsed time is at least `e` (line 1), and is not expired, so its
elapsed time is at most `l` plus the tolerance (line 3); an armed transition between the two
bounds takes every reference firing it has (line 2); past the upper bound it is expired, so a
reap is a step (line 4), and a reap needs it expired and drops its stamp only (line 5); the
reference step meets the clock frame of every transition of the net (line 6,
`clockFrame_refTStep`). -/
@[evidence holds TIME_005]
theorem TIME_005_reference {N : Type} [DecidableEq N] : TIME_005 (RefTStep (N := N)) := by
  intro X u e l hT
  obtain ⟨h1, h2, h3, h4, h5⟩ := time005_lines15 (P := refPolicy) rfl rfl hT
  exact ⟨h1, h2, h3, h4, h5, fun hu => clockFrame_refTStep hu⟩

/-! ### The timing itself -/

/-- The interval bullets of TIME-005: `Window(e, l)` has earliest bound `e`, latest bound `l`,
a deadline, and is reapable. -/
@[evidence cites "TIME-005" "earliest() = earliest, latest() = latest, hasDeadline() = true; Window is reapable"]
theorem time005_interval (e l : Nat) :
    (Timing.window e l).earliest = e ∧ (Timing.window e l).latest = l ∧
      (Timing.window e l).hasDeadline = true ∧ (Timing.window e l).reapable = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The construction rule of TIME-005 ([TIME-001] AC4, ruling D11): `Window(e, l)` is valid
exactly when `e ≤ MAX`, `e ≤ l` and `l ≤ MAX`. -/
@[evidence cites "TIME-005" "AC3 and AC4: construction with latest < earliest, or earliest or latest above the maximum duration, is rejected"]
theorem time005_construction (e l : Nat) :
    (Timing.window e l).Valid ↔ e ≤ maxDurationMs ∧ e ≤ l ∧ l ≤ maxDurationMs :=
  Iff.rfl

/-- AC3 and AC4 on their boundary cases: `Window(5000, 1000)` (latest below earliest),
`Window(0, MAX + 1)` and `Window(MAX + 1, MAX + 1)` are rejected; `Window(1000, 5000)`,
`Window(MAX, MAX)` and `Window(1000, 1000)` are accepted. -/
@[evidence cites "TIME-005" "AC3 and AC4 boundary cases of the window construction"]
theorem time005_construction_examples :
    ¬ (Timing.window 5000 1000).Valid ∧ ¬ (Timing.window 0 (maxDurationMs + 1)).Valid ∧
      ¬ (Timing.window (maxDurationMs + 1) (maxDurationMs + 1)).Valid ∧
      (Timing.window 1000 5000).Valid ∧ (Timing.window maxDurationMs maxDurationMs).Valid ∧
      (Timing.window 1000 1000).Valid := by
  simp only [time005_construction]
  decide

/-! ### Examples -/

/-- The `Window` transition of the examples: one input arc on place `0`, no output spec. -/
def time005_u : Trans Nat :=
  { core := { name := "u", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- A transition with no arcs, of another name, so that a reap of another transition can be
exercised. -/
def time005_v : Trans Nat :=
  { core := { name := "v", inputs := [], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- The timing of the examples: `u` is `Window(1000, 5000)` (1 s to 5 s), every other
transition `Deadline(1000)`. -/
def time005_timing (t : Trans Nat) : Timing :=
  if t.core.name = "u" then .window 1000 5000 else .deadline 1000

/-- The timed net of the examples, with the default tolerance of 5 ms. -/
def time005_X : TimedNet Nat :=
  { net := { places := [0], transitions := [time005_u, time005_v] },
    timing := time005_timing, tol := 5 }

theorem time005_u_in : InNet time005_X time005_u := rfl

/-- The initial marking: one token in place `0`. -/
def time005_m0 : Nat → Nat := fun p => if p = 0 then 1 else 0

/-- The initial state at `T = 0`: both transitions are enabled, so both are stamped `0`. -/
def time005_s0 : TSt Nat := TSt.init time005_X time005_m0 0

/-- The initial state with the clock at `n`. -/
def time005_at (n : Nat) : TSt Nat := { time005_s0 with now := n }

/-- The marking after `u` fires from the initial marking. -/
def time005_m1 : Nat → Nat := fireNC time005_m0 time005_u.core (depProd [])

/-- `u` has a reference firing from the initial marking. -/
theorem time005_u_refFire : RefFire time005_u time005_m0 [] time005_m1 :=
  ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩

/-- A relation that fires every reference firing and ignores the clock (`time010_untimed`)
violates TIME-005 (line 1): at `T = 0` it fires `u`, armed with elapsed time `0`, below its
earliest bound of 1000 ms. -/
@[evidence forbids TIME_005]
theorem TIME_005_forbids_untimed : ¬ TIME_005 time010_untimed := by
  intro h
  have hfire : time010_untimed time005_X time005_s0 (.fire time005_u [])
      { m := time005_m1, now := 0, stamp := time005_s0.stamp } :=
    ⟨time005_u_refFire, rfl, rfl⟩
  exact (h time005_X time005_u 1000 5000 rfl).1 _ _ ⟨_, hfire⟩ (by decide)

/-! ### Mutant: reaped at the bound, not strictly past it -/

/-- The policy that calls a reapable armed transition expired when its elapsed time is at least
its latest bound plus the tolerance, and decides everything else as the spec does. -/
def time005_reapAtPolicy : Policy Nat :=
  { refPolicy with expired := fun X s t =>
      (X.timing t).reapable && s.armed t && decide ((X.timing t).latest + X.tol ≤ s.elapsed t) }

/-- Mutant reading of TIME-005 with a non-strict bound: a window is expired when its elapsed
time is at least `l` plus the tolerance (lines 2 to 5). The other lines are as in TIME-005. -/
def TIME_005_mutant_reapAt {N : Type} [DecidableEq N] (R : TRel N) : Prop :=
  ∀ (X : TimedNet N) u e l, TimingOf X u = .window e l →
    (while (fun s => Armed s u ∧ Elapsed s u < e),
        never (fun s s' => ∃ d, R X s (.fire u d) s')) ∧
    (∀ s d m', InNet X u → Armed s u → e ≤ Elapsed s u → Elapsed s u < l + Tolerance X →
        RefFire u s.m d m' → ∃ s', R X s (.fire u d) s' ∧ s'.m = m') ∧
    (while (fun s => Armed s u ∧ l + Tolerance X ≤ Elapsed s u),
        never (fun s s' => ∃ d, R X s (.fire u d) s')) ∧
    (∀ s, InNet X u → Armed s u → l + Tolerance X ≤ Elapsed s u →
        ∃ s', R X s (.reap u) s') ∧
    (on (fun s s' => R X s (.reap u) s'),
        shall (fun s s' => Armed s u ∧ l + Tolerance X ≤ Elapsed s u ∧ Reaped s' u)) ∧
    (InNet X u → ClockFrame R X u)

/-- The mutant's expiry test on a `Window(e, l)` transition. -/
theorem time005_reapAt_window {X : TimedNet Nat} {s : TSt Nat} {u : Trans Nat} {e l : Nat}
    (hT : TimingOf X u = .window e l) :
    time005_reapAtPolicy.expired X s u = true ↔ Armed s u ∧ l + Tolerance X ≤ Elapsed s u := by
  have hT' : X.timing u = .window e l := hT
  simp [time005_reapAtPolicy, hT', Timing.reapable, Timing.latest, armed_iff, elapsed_eq]

/-- The step that reaps at the bound kills the mutant: it satisfies the mutant reading, but not
TIME-005, since at `T = 5005`, with elapsed time exactly `5000 + 5`, it reaps `u` (AC2:
"strictly greater than that bound"). -/
@[evidence mutant TIME_005]
theorem TIME_005_mutant_reapAt_killed :
    TIME_005_mutant_reapAt (RefTStepW time005_reapAtPolicy) ∧
      ¬ TIME_005 (RefTStepW time005_reapAtPolicy) := by
  refine ⟨fun X u e l hT => ⟨time005_gate (P := time005_reapAtPolicy) rfl hT, fun s d m' hu ha hle hlt hf => ?_,
    fun s s' ⟨d, h⟩ hx => ?_, fun s hu ha hle => ?_, fun s s' h => ?_, fun hu => clockFrame_of (P := time005_reapAtPolicy) rfl rfl hu⟩,
    fun h => ?_⟩
  · refine time005_fires hu ha (time005_gate_open (by rw [hT]; exact hle)) ?_ hf
    cases hx : time005_reapAtPolicy.expired X s u
    · rfl
    · exact absurd ((time005_reapAt_window hT).1 hx).2 (by omega)
  · have hf := (refTStepW_fire_inv h).2.2.2.2.1
    rw [(time005_reapAt_window hT).2 hx] at hf
    exact Bool.noConfusion hf
  · exact ⟨_, RefTStepW.reap X s u (inNet_mem hu) ((time005_reapAt_window hT).2 ⟨ha, hle⟩)⟩
  · obtain ⟨ha, hle⟩ := (time005_reapAt_window hT).1 (time005_reap_inv h).2.1
    exact ⟨ha, hle, time005_reap_reaped h ha⟩
  · have hs := RefTStepW.reap (P := time005_reapAtPolicy) time005_X (time005_at 5005) time005_u
      (inNet_mem time005_u_in) (by decide)
    obtain ⟨-, hlt, -⟩ := (h time005_X time005_u 1000 5000 rfl).2.2.2.2.1 _ _ hs
    revert hlt
    decide

/-! ### Mutant: the tolerance ignored -/

/-- The policy that calls a reapable armed transition expired when its elapsed time is greater
than its latest bound, without the tolerance, and decides everything else as the spec does. -/
def time005_noTolPolicy : Policy Nat :=
  { refPolicy with expired := fun X s t =>
      (X.timing t).reapable && s.armed t && decide ((X.timing t).latest < s.elapsed t) }

/-- Mutant reading of TIME-005 without the tolerance: a window is expired when its elapsed time
is greater than `l` (lines 2 to 5). The other lines are as in TIME-005. -/
def TIME_005_mutant_noTol {N : Type} [DecidableEq N] (R : TRel N) : Prop :=
  ∀ (X : TimedNet N) u e l, TimingOf X u = .window e l →
    (while (fun s => Armed s u ∧ Elapsed s u < e),
        never (fun s s' => ∃ d, R X s (.fire u d) s')) ∧
    (∀ s d m', InNet X u → Armed s u → e ≤ Elapsed s u → Elapsed s u ≤ l →
        RefFire u s.m d m' → ∃ s', R X s (.fire u d) s' ∧ s'.m = m') ∧
    (while (fun s => Armed s u ∧ l < Elapsed s u),
        never (fun s s' => ∃ d, R X s (.fire u d) s')) ∧
    (∀ s, InNet X u → Armed s u → l < Elapsed s u → ∃ s', R X s (.reap u) s') ∧
    (on (fun s s' => R X s (.reap u) s'),
        shall (fun s s' => Armed s u ∧ l < Elapsed s u ∧ Reaped s' u)) ∧
    (InNet X u → ClockFrame R X u)

/-- The mutant's expiry test on a `Window(e, l)` transition. -/
theorem time005_noTol_window {X : TimedNet Nat} {s : TSt Nat} {u : Trans Nat} {e l : Nat}
    (hT : TimingOf X u = .window e l) :
    time005_noTolPolicy.expired X s u = true ↔ Armed s u ∧ l < Elapsed s u := by
  have hT' : X.timing u = .window e l := hT
  simp [time005_noTolPolicy, hT', Timing.reapable, Timing.latest, armed_iff, elapsed_eq]

/-- The step that ignores the tolerance kills the mutant: it satisfies the mutant reading, but
not TIME-005, since at `T = 5003`, with elapsed time `5003`, past `5000` but within the tolerance
of 5 ms, `u` cannot fire (sentence 2: ready until it is expired, expired only past latest plus
the deadline tolerance). -/
@[evidence mutant TIME_005]
theorem TIME_005_mutant_noTol_killed :
    TIME_005_mutant_noTol (RefTStepW time005_noTolPolicy) ∧
      ¬ TIME_005 (RefTStepW time005_noTolPolicy) := by
  refine ⟨fun X u e l hT => ⟨time005_gate (P := time005_noTolPolicy) rfl hT,
    fun s d m' hu ha hle hlt hf => ?_, fun s s' ⟨d, h⟩ hx => ?_, fun s hu ha hle => ?_,
    fun s s' h => ?_, fun hu => clockFrame_of (P := time005_noTolPolicy) rfl rfl hu⟩, fun h => ?_⟩
  · refine time005_fires hu ha (time005_gate_open (by rw [hT]; exact hle)) ?_ hf
    cases hx : time005_noTolPolicy.expired X s u
    · rfl
    · exact absurd ((time005_noTol_window hT).1 hx).2 (by omega)
  · have hf := (refTStepW_fire_inv h).2.2.2.2.1
    rw [(time005_noTol_window hT).2 hx] at hf
    exact Bool.noConfusion hf
  · exact ⟨_, RefTStepW.reap X s u (inNet_mem hu) ((time005_noTol_window hT).2 ⟨ha, hle⟩)⟩
  · obtain ⟨ha, hle⟩ := (time005_noTol_window hT).1 (time005_reap_inv h).2.1
    exact ⟨ha, hle, time005_reap_reaped h ha⟩
  · obtain ⟨s', hs, -⟩ := (h time005_X time005_u 1000 5000 rfl).2.1 (time005_at 5003) [] _
      time005_u_in (by decide) (by decide) (by decide) time005_u_refFire
    have hx := (refTStepW_fire_inv hs).2.2.2.2.1
    revert hx
    decide

/-! ### Mutant: a window enforced softly, never reaped -/

/-- The expiry test that never calls a `Window` transition expired (it enforces a window softly,
as `Exact` is), and is the spec's on every other timing. -/
def time005_softExpired (X : TimedNet Nat) (s : TSt Nat) (t : Trans Nat) : Bool :=
  match X.timing t with
  | .window _ _ => false
  | _ => tExpired X s t

/-- The policy with the soft expiry test, and the spec's other decisions. -/
def time005_softPolicy : Policy Nat := { refPolicy with expired := time005_softExpired }

/-- Mutant reading of TIME-005 in which a window is soft: a `Window(e, l)` transition is
gated at `e` and then ready however late, and is never reaped. The other lines are as in
TIME-005. -/
def TIME_005_mutant_soft {N : Type} [DecidableEq N] (R : TRel N) : Prop :=
  ∀ (X : TimedNet N) u e l, TimingOf X u = .window e l →
    (while (fun s => Armed s u ∧ Elapsed s u < e),
        never (fun s s' => ∃ d, R X s (.fire u d) s')) ∧
    (∀ s d m', InNet X u → Armed s u → e ≤ Elapsed s u → RefFire u s.m d m' →
        ∃ s', R X s (.fire u d) s' ∧ s'.m = m') ∧
    (∀ s s', ¬ R X s (.reap u) s') ∧
    (InNet X u → ClockFrame R X u)

/-- The soft step kills the mutant: it satisfies the mutant reading, but not TIME-005, since
at `T = 6000` the window `u` is past `5000 + 5` and no reap of it is a step (test derivation:
"at 6s → expired"). -/
@[evidence mutant TIME_005]
theorem TIME_005_mutant_soft_killed :
    TIME_005_mutant_soft (RefTStepW time005_softPolicy) ∧
      ¬ TIME_005 (RefTStepW time005_softPolicy) := by
  have hsoft : ∀ (X : TimedNet Nat) s u e l, TimingOf X u = .window e l →
      time005_softPolicy.expired X s u = false := fun X s u e l hT => by
    have hT' : X.timing u = .window e l := hT
    simp [time005_softPolicy, time005_softExpired, hT']
  refine ⟨fun X u e l hT => ⟨time005_gate (P := time005_softPolicy) rfl hT,
    fun s d m' hu ha hle hf => ?_, fun s s' h => ?_, fun hu => clockFrame_of (P := time005_softPolicy) rfl rfl hu⟩, fun h => ?_⟩
  · exact time005_fires hu ha (time005_gate_open (by rw [hT]; exact hle))
      (hsoft X s u e l hT) hf
  · have hx := (time005_reap_inv h).2.1
    rw [hsoft X s u e l hT] at hx
    exact Bool.noConfusion hx
  · obtain ⟨s', hs⟩ := (h time005_X time005_u 1000 5000 rfl).2.2.2.1 (time005_at 6000)
      time005_u_in (by decide) (by decide)
    have hx := (time005_reap_inv hs).2.1
    rw [hsoft time005_X _ time005_u 1000 5000 rfl] at hx
    exact Bool.noConfusion hx

/-! ### Mutants: a reap or a restart hidden in another transition's firing -/

/-- Mutant reading of TIME-005 with line 6 cut down: `u`'s clock is framed across delays and
reaps of other names only, and a firing may do anything to it (no `StaysArmed`, no firing part
of the clock frame). -/
def TIME_005_mutant_noKeep {N : Type} [DecidableEq N] (R : TRel N) : Prop :=
  ∀ (X : TimedNet N) u e l, TimingOf X u = .window e l →
    (while (fun s => Armed s u ∧ Elapsed s u < e),
        never (fun s s' => ∃ d, R X s (.fire u d) s')) ∧
    (∀ s d m', InNet X u → Armed s u → e ≤ Elapsed s u → Elapsed s u ≤ l + Tolerance X →
        RefFire u s.m d m' → ∃ s', R X s (.fire u d) s' ∧ s'.m = m') ∧
    (while (fun s => Armed s u ∧ l + Tolerance X < Elapsed s u),
        never (fun s s' => ∃ d, R X s (.fire u d) s')) ∧
    (∀ s, InNet X u → Armed s u → l + Tolerance X < Elapsed s u →
        ∃ s', R X s (.reap u) s') ∧
    (on (fun s s' => R X s (.reap u) s'),
        shall (fun s s' => Armed s u ∧ l + Tolerance X < Elapsed s u ∧ Reaped s' u)) ∧
    (∀ δ, on (fun s s' => R X s (.delay δ) s'),
        shall (fun s s' => s'.stamp u.core.name = s.stamp u.core.name)) ∧
    (∀ t, t.core.name ≠ u.core.name → on (fun s s' => R X s (.reap t) s'),
        shall (fun s s' => s'.stamp u.core.name = s.stamp u.core.name))

/-- Every policy with the spec's gate and expiry test satisfies the mutant reading, whatever it
does to the stamps across a firing. -/
theorem time005_noKeep_of {P : Policy Nat} (hg : P.gate = refPolicy.gate)
    (hx : P.expired = refPolicy.expired) : TIME_005_mutant_noKeep (RefTStepW P) := by
  intro X u e l hT
  obtain ⟨h1, h2, h3, h4, h5⟩ := time005_lines15 hg hx hT
  exact ⟨h1, h2, h3, h4, h5, time005_keeps⟩

/-- The clean-set drop: a firing keeps or re-arms only the clocks of the transitions whose arc
places it writes (the dirty set of the runtimes); every other armed transition loses its clock,
though it stays enabled. -/
def time005_dropCleanPolicy : Policy Nat :=
  { refPolicy with
    keep := fun X s t d m' u => refPolicy.keep X s t d m' u && writesArc t d u
    rearm := fun _ _ t d m' u => enabledNA m' u.core && writesArc t d u }

/-- The restart on every firing: no armed transition keeps its stamp across a firing; each one
enabled after it is armed again with the current reading. -/
def time005_restartPolicy : Policy Nat := { refPolicy with keep := fun _ _ _ _ _ _ => false }

/-- The marking after `v`, which has no arcs, fires from the initial marking. -/
def time005_mv : Nat → Nat := fireNC time005_m0 time005_v.core (depProd [])

/-- `v` has a reference firing from the initial marking. -/
theorem time005_v_refFire : RefFire time005_v time005_m0 [] time005_mv :=
  ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩

/-- The clean-set drop kills the mutant: it satisfies the mutant reading, but not TIME-005
(line 6). At `T = 500` the unrelated `v` fires; the window `u` stays enabled in the intermediate
marking and after it, yet loses its clock long before it expires: a reap hidden in a firing. -/
@[evidence mutant TIME_005]
theorem TIME_005_mutant_dropClean_killed :
    TIME_005_mutant_noKeep (RefTStepW time005_dropCleanPolicy) ∧
      ¬ TIME_005 (RefTStepW time005_dropCleanPolicy) := by
  refine ⟨time005_noKeep_of rfl rfl, fun h => ?_⟩
  have hs := RefTStepW.fire (P := time005_dropCleanPolicy) time005_X (time005_at 500) time005_v
    [] time005_mv (by simp [time005_X]) time005_v_refFire (by decide) (by decide) (by decide)
  have := ((h time005_X time005_u 1000 5000 rfl).2.2.2.2.2 time005_u_in).2.2.2 time005_v []
    (by decide) _ _ hs (by decide) (by decide) (by decide)
  revert this
  decide

/-- The restart on every firing kills the mutant: it satisfies the mutant reading, but not
TIME-005 (line 6). At `T = 500` the unrelated `v` fires and the window `u`, enabled throughout,
is restamped `500` instead of keeping `0`, so a continuously enabled window is pushed past its
bound by every firing of a busy net and escapes the reap. -/
@[evidence mutant TIME_005]
theorem TIME_005_mutant_restart_killed :
    TIME_005_mutant_noKeep (RefTStepW time005_restartPolicy) ∧
      ¬ TIME_005 (RefTStepW time005_restartPolicy) := by
  refine ⟨time005_noKeep_of rfl rfl, fun h => ?_⟩
  have hs := RefTStepW.fire (P := time005_restartPolicy) time005_X (time005_at 500) time005_v
    [] time005_mv (by simp [time005_X]) time005_v_refFire (by decide) (by decide) (by decide)
  have := ((h time005_X time005_u 1000 5000 rfl).2.2.2.2.2 time005_u_in).2.2.2 time005_v []
    (by decide) _ _ hs (by decide) (by decide) (by decide)
  revert this
  decide

/-! ### A reap hidden in the transition's own firing -/

theorem time005_namesDistinct : NamesDistinct time005_X := by unfold NamesDistinct; decide

/-- ✗ An executor whose firing of `u` itself leaves `u` enabled but unarmed violates TIME-005
(line 6, `StaysArmed`): with two tokens in `u`'s input place at `T = 2000`, inside the window,
`u` fires and stays enabled, and the self-drop policy gives it no clock, a reap before the
window's bound hidden in its own firing. -/
@[evidence forbids TIME_005]
theorem TIME_005_forbids_selfDrop : ¬ TIME_005 (RefTStepW (selfDropPolicy (N := Nat))) := fun h =>
  selfDrop_not_staysArmed
    (s := { m := fun p => if p = 0 then 2 else 0, now := 2000,
            stamp := fun n => if n = "u" then some 0 else none })
    (d := []) time005_u_in time005_namesDistinct (by decide)
    ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩ (by decide) (by decide) (by decide)
    ((h time005_X time005_u 1000 5000 rfl).2.2.2.2.2 time005_u_in).1

/-! ### Every line exercised -/

/-- The state after `u` is reaped at `T = 5006`. -/
def time005_reaped : TSt Nat :=
  { time005_at 5006 with
    stamp := fun n => if n = "u" then none else (time005_at 5006).stamp n }

/-- Every line of TIME-005 is exercised by the reference step, on the test derivation in
milliseconds with a tolerance of 5 ms. `u` is `Window(1000, 5000)` and armed at `T = 0`. At
`T = 500` it cannot fire (line 1); at `T = 2000` it can (line 2), and still at `T = 5005`, its
bound plus the tolerance, where no reap of it is a step (line 5). At `T = 5006` it cannot fire
(line 3), a reap of it is a step (line 4) and leaves it reaped (line 5); at `T = 6000` it is
expired. The delays keep its stamp `0` (line 6). At `T = 2000` the deadline transition `v` is
expired and reaped, and `u` keeps its stamp (line 6). At `T = 500` `v` fires instead; `u`, armed,
is enabled in the intermediate marking and after the firing, and keeps its stamp `0` (line 6). -/
@[evidence nonvacuous TIME_005]
theorem TIME_005_nonvacuous :
    RefTStep time005_X time005_s0 (.delay 500) (time005_at 500) ∧
      Armed (time005_at 500) time005_u ∧ Elapsed (time005_at 500) time005_u = 500 ∧
      (∀ d s', ¬ RefTStep time005_X (time005_at 500) (.fire time005_u d) s') ∧
      RefTStep time005_X time005_s0 (.delay 2000) (time005_at 2000) ∧
      (time005_at 2000).stamp "u" = time005_s0.stamp "u" ∧
      (∃ s', RefTStep time005_X (time005_at 2000) (.fire time005_u []) s') ∧
      (∃ s', RefTStep time005_X (time005_at 5005) (.fire time005_u []) s') ∧
      (∀ s', ¬ RefTStep time005_X (time005_at 5005) (.reap time005_u) s') ∧
      (∀ d s', ¬ RefTStep time005_X (time005_at 5006) (.fire time005_u d) s') ∧
      RefTStep time005_X (time005_at 5006) (.reap time005_u) time005_reaped ∧
      Reaped time005_reaped time005_u ∧
      Expired time005_X (time005_at 6000) time005_u ∧
      Expired time005_X (time005_at 2000) time005_v ∧
      (∃ s', RefTStep time005_X (time005_at 2000) (.reap time005_v) s' ∧
        s'.stamp "u" = some 0) ∧
      (∃ s', RefTStep time005_X (time005_at 500) (.fire time005_v []) s' ∧
        Armed (time005_at 500) time005_u ∧ Enabled time005_u (Mid time005_v time005_m0) ∧
        Enabled time005_u s'.m ∧ s'.stamp "u" = some 0) := by
  refine ⟨RefTStepW.delay _ _ 500, by decide, by decide, fun d s' h => ?_,
    RefTStepW.delay _ _ 2000, rfl,
    ⟨_, RefTStepW.fire _ _ _ _ _ (inNet_mem time005_u_in) time005_u_refFire (by decide)
      (by decide) (by decide)⟩,
    ⟨_, RefTStepW.fire _ _ _ _ _ (inNet_mem time005_u_in) time005_u_refFire (by decide)
      (by decide) (by decide)⟩,
    fun s' h => ?_, fun d s' h => ?_,
    RefTStepW.reap _ _ _ (inNet_mem time005_u_in) (by decide), by decide, by decide, by decide,
    ⟨_, RefTStepW.reap _ _ _ (by simp [time005_X]) (by decide), by decide⟩,
    ⟨_, RefTStepW.fire _ _ _ _ _ (by simp [time005_X]) time005_v_refFire (by decide) (by decide)
      (by decide), by decide, by decide, by decide, by decide⟩⟩
  · have := time010_gate rfl h
    revert this
    decide
  · have := (time005_reap_inv h).2.1
    revert this
    decide
  · have := (refTStepW_fire_inv h).2.2.2.2.1
    revert this
    decide

end Libpetri.Spec
