import Libpetri.Strengthening
import Libpetri.TimedCycle

/-!
# Deadline reaping against the untimed verdict ([VER-004] AC3, [TIME-013])

[VER-004] AC3: "A Proven verdict on the untimed net implies the property holds for all timed
executions", on the rationale that "timing only restricts behavior". [TIME-013]: a
`Deadline` / `Window` transition past `latest + tolerance` is disabled (reaped) and
`TransitionTimedOut` is emitted; its tokens stay where they are.

**Outcome: AC3 is false for the quiescence properties and true for the marking properties.**

* Reaping never changes the marking, and every timed firing is an enabled untimed firing, so
  every marking a timed run visits is untimed-reachable (`timed_markings_reachable`,
  `timed_marking_run_reachable`). A `Proven` for a predicate of the marking alone —
  `PlaceBound`, `BranchPlaceBound`, `MutualExclusion`, `Unreachable` — therefore holds for
  every timed execution (`marking_properties_transfer`).
* The quiescence properties (`DeadlockFree`, `TerminatesAtSink`, `QuiescentCount`,
  `JoinedOrDeadLettered`) are not predicates of the marking alone. The untimed `Bad` reads
  quiescence as "no transition enabled at this marking" (`encode_quiescent`); the executor
  comes to rest when its enabled *bits* are clear. A reap clears a bit while the tokens stay,
  and both loops then terminate: `run_sync` (`executor_core/executor.rs:411`, the
  `enabled_count() == 0` break right after `enforce_deadlines`) and `run_async` (`:1090`, the
  same test with nothing in flight). Neither shipped backend marks a reaped transition dirty
  (the [TIME-013] ruling, `TimedCycle.lean`), so **both backends** stop, reason `Quiescent`,
  with the token stranded. The break comes before the next update phase, so the precompiled
  path before the ruling, whose extra `mark_transition_dirty` on a reap re-enabled the
  transition one cycle later (`enforcePB`), stopped there too.

The witness `reaping_refutes_ver004_ac3` is `TimedCycle.lean`'s `window(3,5)` transition as a
whole net: `p₀ —t→ p₁`, `M₀ = {p₀}`, sink `{p₁}`, cycles at `[0, 10]` (the executor blocked
past the deadline, TIME-013's own test derivation; under [TIME-015] any clock that jumps).
`TimedCycle.lean` folds the tolerance into `latest`, so `latest = 5` is the reap threshold of an
executor built with `deadline_tolerance_ms(0)`: at the default tolerance of 5 ms the threshold
is 10, the wake at 10 does not reap (`elapsed > latest + tolerance` is strict), and the same
witness needs a wake past 10.
Untimed `DeadlockFree` is `Proven`; the timed run ends `Quiescent` at `{p₀}` with `p₀` not a
sink — a `DeadlockFree` violation the untimed verdict cannot see, because at `{p₀}` the untimed
net still enables `t`.

The timed model (`execCycle`) reuses `TimedCycle.lean`'s cell: update enablement, enforce
deadlines, the loop's termination test, then the ready/fire decision. `tokens` is refreshed
from the live marking (`can_enable`), and a firing requires `enabledA` (`recheck_can_fire`).
One transition, no environment places, nothing in flight: the loop's termination test is
exactly "the enabled bit is clear". The post-fire cell is simplified (dirty set, tokens
refreshed); the witness never fires, and the reachability half does not read it.

Proposed wording for [VER-004] (spec/ not edited here), see the report.

**Resolution (2026-09-28).** Every language now reads quiescence as *reap-quiescence* (every
enabled transition is reapable, [VER-002]). `ReapAware.lean` proves that reading sound for every
timed run of either backend (`rest_sound`, `reap_aware_ac3`) and shows this module's witness is
caught (`witness_caught`): `{p₀}` is reap-quiescent, so the reap-aware `DeadlockFree` is
`Violated` there. The theorems here still describe the strict reading.
-/

namespace Libpetri.Novel.ReapingVsUntimed

open Libpetri

/-! ## Generic half: timed runs visit only untimed-reachable markings -/

/-- A timed executor at marking granularity: control state `σ` (enabled bits, clocks, dirty
bits) moves freely, the marking moves only by an enabled untimed firing. Reaping, clock
restarts and dirty marking are control moves. This covers **atomic** firings only — consume and
deposit in one move, as `run_sync` does with sync actions. An async action consumes at start and
deposits at completion, with other firings and injections in between; that in-flight marking is
not a `StepARel` successor, and `MarkingFaithful` says nothing about it. [VER-004] now verifies
the in-flight split net instead (`in_flight::split_in_flight`), and `InFlight.lean` proves the
bridge: the split net covers every interleaving (`split_covers_executor`), and where no output
is tested non-monotonically an atomic run matches it (`atomic_covers_executor`). -/
def MarkingFaithful (net : FlatNet) {σ : Type} (step : AMarking × σ → AMarking × σ → Prop) :
    Prop :=
  ∀ a s a' s', step (a, s) (a', s') → a' = a ∨ StepARel net a a'

/-- Every marking a faithful timed run visits is untimed-reachable. -/
theorem timed_markings_reachable {net : FlatNet} {σ : Type}
    {step : AMarking × σ → AMarking × σ → Prop} (hf : MarkingFaithful net step)
    {a0 : AMarking} {s0 : σ} {x : AMarking × σ}
    (h : Relation.ReflTransGen step (a0, s0) x) : ReachA net a0 x.1 := by
  induction h with
  | refl => exact ReachA.init
  | tail _ hs ih =>
    rename_i y z _
    obtain ⟨a, s⟩ := y
    obtain ⟨a', s'⟩ := z
    rcases hf a s a' s' hs with rfl | hst
    · exact ih
    · exact Relation.ReflTransGen.tail ih hst

/-- **AC3 for marking properties**: an untimed `Proven` for any predicate of the marking holds
at every state of every faithful timed run. -/
theorem marking_properties_transfer {net : FlatNet} {σ : Type}
    {step : AMarking × σ → AMarking × σ → Prop} (hf : MarkingFaithful net step)
    {a0 : AMarking} {s0 : σ} {Bad : AMarking → Prop}
    (hp : ProvenFor (ReachA net a0) Bad) {x : AMarking × σ}
    (h : Relation.ReflTransGen step (a0, s0) x) : ¬ Bad x.1 :=
  hp _ (timed_markings_reachable hf h)

/-! ## The witness net -/

/-- `p₀ —t→ p₁`, `One` input. In the timed run it carries `wTiming = window(3, 5)`. -/
def tR : Transition :=
  { name := "t"
  , inputs := [{ place := 0, card := .one, guard := none }]
  , inhibitors := [], reads := [], resets := [] }

def netR : FlatNet := [(tR, [1])]

def a0R : AMarking := fun p => if p = 0 then 1 else 0

/-- Declared sinks: `{p₁}`. -/
def sinksR : List PlaceId := [1]

/-- No flat transition enabled: `encode_quiescent` on an env-free net. -/
def QuiescentA (net : FlatNet) (a : AMarking) : Prop :=
  ∀ ft ∈ net, enabledA a ft.1 = false

/-- A token rests on a flat place that is not a declared sink: `stranded_conditions` with no
conditional sinks. -/
def Strands (sinks : List PlaceId) (n : Nat) (a : AMarking) : Prop :=
  ∃ q, q < n ∧ q ∉ sinks ∧ 1 ≤ a q

/-- The `DeadlockFree` violation `encode_property_violation` emits ([VER-002]). -/
def dlfBad (net : FlatNet) (sinks : List PlaceId) (n : Nat) (a : AMarking) : Prop :=
  QuiescentA net a ∧ Strands sinks n a

/-- The untimed reachable set of `netR` is `{p₀}` then `{p₁}` (on the flat places). -/
theorem reachR_inv {a : AMarking} (h : ReachA netR a0R a) :
    (a 0 = 1 ∧ a 1 = 0) ∨ (a 0 = 0 ∧ a 1 = 1) := by
  induction h with
  | init => left; decide
  | @step a1 ft _ hmem hen ih =>
    have : ft = (tR, [1]) := by simpa [netR] using hmem
    subst this
    have hen0 : 1 ≤ a1 0 := by
      simp [enabledA, tR] at hen; exact hen
    have e0 : fireA a1 tR [1] 0 = a1 0 - 1 + 0 := rfl
    have e1 : fireA a1 tR [1] 1 = a1 1 - 0 + 1 := rfl
    show (fireA a1 tR [1] 0 = 1 ∧ fireA a1 tR [1] 1 = 0)
      ∨ (fireA a1 tR [1] 0 = 0 ∧ fireA a1 tR [1] 1 = 1)
    rw [e0, e1]
    omega

/-- **Untimed `DeadlockFree` is `Proven`** on `netR` from `{p₀}` with sink `{p₁}`. -/
theorem untimed_dlf_proven : ProvenFor (ReachA netR a0R) (dlfBad netR sinksR 2) := by
  rintro a h ⟨hq, q, hq2, hqs, hqa⟩
  have hdis : enabledA a tR = false := hq (tR, [1]) (by simp [netR])
  have h0 : a 0 = 0 := by
    cases h' : a 0 with
    | zero => rfl
    | succ k => simp [enabledA, tR, h', Card.required] at hdis
  have : q = 0 := by
    have : q ≠ 1 := fun h => hqs (by simp [sinksR, h])
    omega
  subst this
  omega

/-! ## The timed executor on the witness net -/

/-- A loop outcome: still running, or terminated at a marking. -/
inductive Outcome where
  | running (a : AMarking) (s : Cell)
  | halted (a : AMarking) (s : Cell)

def Outcome.marking : Outcome → AMarking
  | .running a _ => a
  | .halted a _ => a

/-- One executor cycle on `netR` (`run_sync`, `executor_core/executor.rs:386`; `run_async`
Phase 3/4 and the termination checks, `:1063-1095`): update enablement from the live marking,
enforce deadlines, stop when nothing is enabled (`:411` / `:1090`; no environment place,
nothing in flight), otherwise fire `t` if the window is open and `recheck_can_fire` passes. -/
def execCycle (enforce : Nat → Nat → Cell → Cell) (tm : Timing) (now : Nat) (a : AMarking)
    (s : Cell) : Outcome :=
  let s1 := updateCell now { s with tokens := enabledA a tR }
  let s2 := enforce tm.latest now s1
  if s2.enabled = false then .halted a s2
  else if fires tm.earliest now s2 && enabledA a tR then
    .running (fireA a tR [1]) { s2 with tokens := enabledA (fireA a tR [1]) tR, dirty := true }
  else .running a s2

/-- A run over the cycle timestamps; a halt is final. -/
def execRun (enforce : Nat → Nat → Cell → Cell) (tm : Timing) :
    AMarking → Cell → List Nat → Outcome
  | a, s, [] => .running a s
  | a, s, now :: rest =>
    match execCycle enforce tm now a s with
    | .halted a' s' => .halted a' s'
    | .running a' s' => execRun enforce tm a' s' rest

/-- One cycle moves the marking only by an enabled firing of `netR`. -/
theorem execCycle_faithful (enforce : Nat → Nat → Cell → Cell) (tm : Timing) (now : Nat)
    (a : AMarking) (s : Cell) :
    (execCycle enforce tm now a s).marking = a
      ∨ StepARel netR a (execCycle enforce tm now a s).marking := by
  unfold execCycle
  simp only
  split
  · left; rfl
  · split
    · rename_i h
      right
      simp only [Bool.and_eq_true] at h
      exact ⟨(tR, [1]), by simp [netR], h.2, rfl⟩
    · left; rfl

/-- **Reachability half on the witness**: every marking any timed run of `netR` ends at,
over every schedule and both enforcement paths, is untimed-reachable. -/
theorem timed_marking_run_reachable (enforce : Nat → Nat → Cell → Cell) (tm : Timing) :
    ∀ (nows : List Nat) (a : AMarking) (s : Cell), ReachA netR a0R a →
      ReachA netR a0R (execRun enforce tm a s nows).marking
  | [], _, _, h => h
  | now :: rest, a, s, h => by
    have hc : ReachA netR a0R (execCycle enforce tm now a s).marking := by
      rcases execCycle_faithful enforce tm now a s with he | hst
      · rw [he]; exact h
      · exact Relation.ReflTransGen.tail h hst
    unfold execRun
    split
    · rename_i a' s' heq
      rw [heq] at hc; exact hc
    · rename_i a' s' heq
      rw [heq] at hc
      exact timed_marking_run_reachable enforce tm rest a' s' hc

/-- The cell after the reap: `reapedBB` in both shipped backends' runs, `reapedPB` in the run of
the precompiled path before the [TIME-013] ruling (additionally dirty). -/
def reapedBB : Cell := { tokens := true, enabled := false, clock := none, dirty := false }
def reapedPB : Cell := { tokens := true, enabled := false, clock := none, dirty := true }

/-- **VER-004 AC3 fails for `DeadlockFree`.**
1. The untimed verifier's `Proven` is correct for the untimed net.
2. Both backends' timed runs of the same net, cycles `[0, 10]` then anything, terminate at
   cycle 10 — enable at 0, reap at 10, `enabled_count() == 0`, loop exit — at the initial
   marking `{p₀}`, whatever the schedule continues with.
3. That final marking strands a token on `p₀`, not a sink: the run ends `Quiescent`, a
   `DeadlockFree` violation of the timed execution.
4. At that marking the untimed net enables `t`, so it is not untimed-quiescent: the untimed
   `Bad` is false there, which is exactly why (1) cannot see (3). -/
theorem reaping_refutes_ver004_ac3 :
    ProvenFor (ReachA netR a0R) (dlfBad netR sinksR 2)
    ∧ (∀ rest : List Nat,
        execRun enforceBB wTiming a0R wInit (0 :: 10 :: rest) = .halted a0R reapedBB
        ∧ execRun enforcePB wTiming a0R wInit (0 :: 10 :: rest) = .halted a0R reapedPB)
    ∧ Strands sinksR 2 a0R
    ∧ enabledA a0R tR = true
    ∧ ¬ dlfBad netR sinksR 2 a0R :=
  ⟨untimed_dlf_proven, fun _ => ⟨rfl, rfl⟩, ⟨0, by decide, by decide, by decide⟩, by decide,
    untimed_dlf_proven a0R ReachA.init⟩

/-- Without the reap the same net quiesces legitimately: on a schedule that reaches the window
before the deadline (`[0, 3]`), the transition fires and the run moves to `{p₁}`, which strands
nothing. The stranding is the reap's, not the net's. -/
theorem on_time_run_fires :
    (execRun enforceBB wTiming a0R wInit [0, 3]).marking 0 = 0
    ∧ (execRun enforceBB wTiming a0R wInit [0, 3]).marking 1 = 1 := by
  constructor <;> rfl

end Libpetri.Novel.ReapingVsUntimed
