import Libpetri.Novel.FiringBound.Phase
import Libpetri.Novel.ReapingVsUntimed

/-!
# The firing-bound phase under deadline reaping ([TIME-013], R16)

The ranking bounds every faithful timed run, and a `Proven` of a marking predicate transfers;
a `Proven` of `DeadlockFree` does not (`firing_bound_proves_reaped_net`). "Faithful" covers
**atomic** executors only (`run_sync` with sync actions): an async action consumes at start and
deposits at completion, and that in-flight marking is not a row firing. The premise is
discharged for `ReapingVsUntimed`'s executor model of the witness net (`execStep_faithfulRows`,
through `markingFaithfulRows_of_markingFaithful`), where both results are instantiated
(`ranking_bounds_timed_netR`, `phase_proven_timed_marking_netR`). Without reaping the rest state
is untimed-quiescent and the untimed `Proven` is the timed one (`noReap_timedDeadlockFree`).

`firing_bound_proves_reaped_net` is a retrodiction of the phase before the reaping fix, which
read the strict quiescence. The shipped phase closes R16 by reap-quiescence instead: its script
(`encode_property_violation` through the reap-aware `encode_quiescent`) and its replay
(`abstract_replay::violation_predicate`, whose `quiescent` skips `ft.reapable`) run over the flat
net `SmtVerifier::flatten` builds with `reapable_set()`, which is `ReapAware.lean`'s reading
(`rest_sound`, `reap_aware_ac3`). `gateReaping`, a gate on the phase's verdict that also closes
R16 on the witness (`gated_witness_steps_aside`, `gated_dlf_timed_sound_netR`), is an alternative
that was not taken and models no Rust code. See `Libpetri/Novel/FiringBound.lean`.
-/

namespace Libpetri.Novel.FiringBound

open Libpetri
open Libpetri.Novel.ForwardDeposit
open Libpetri.Novel.LinearBound

/-! ## Deadline reaping ([TIME-013], R16) -/

/-- A timed executor at marking granularity over deposit rows: its control state (enabled bits,
clocks, dirty bits) moves freely, its marking only by an enabled row firing. Reaping and clock
moves change no token (`ReapingVsUntimed.MarkingFaithful`, over rows;
`markingFaithfulRows_of_markingFaithful` converts). **Atomic firings only**: consume and deposit
in one move, as `run_sync` does with sync actions. `run_async` with an action in flight holds a
marking with the inputs consumed and the outputs not yet deposited, which is no row firing's
result; this premise is false for it, and nothing here covers it. -/
def MarkingFaithfulRows (rows : List Row) {σ : Type} (step : AMarking × σ → AMarking × σ → Prop) :
    Prop :=
  ∀ a s a' s', step (a, s) (a', s') → a' = a ∨ StepAD rows a a'

/-- A timed run, counting the moves that change the marking. -/
inductive TimedRun {σ : Type} (step : AMarking × σ → AMarking × σ → Prop) :
    Nat → AMarking × σ → AMarking × σ → Prop
  | refl (x) : TimedRun step 0 x x
  | same {k x y z} : TimedRun step k x y → step y z → z.1 = y.1 → TimedRun step k x z
  | moves {k x y z} : TimedRun step k x y → step y z → z.1 ≠ y.1 → TimedRun step (k + 1) x z

/-- **The firing bound holds for atomic timed executions**: a faithful timed run changes the
marking at most `K = r·M0` times, however it reaps; with a ranking every firing changes the
marking, so this is at most `K` firings. Instantiated on the executor model of the witness net
by `ranking_bounds_timed_netR`. -/
theorem ranking_bounds_timed {rows : List Row} {n : Nat} {r : Weight} {σ : Type}
    {step : AMarking × σ → AMarking × σ → Prop} (hf : MarkingFaithfulRows rows step)
    (hr : IsRanking n rows r) {k : Nat} {x y : AMarking × σ} (h : TimedRun step k x y) :
    (k : Int) + dot r y.1 n ≤ dot r x.1 n := by
  induction h with
  | refl => simp
  | same _ _ hz ih => rw [hz]; exact ih
  | @moves k x y z _ hs hne ih =>
    obtain ⟨a, s⟩ := y
    obtain ⟨a', s'⟩ := z
    rcases hf a s a' s' hs with heq | ⟨tr, hmem, hen, hfire⟩
    · exact absurd heq hne
    · have := ranking_step hr hmem hen
      simp only at hfire ih ⊢
      rw [hfire]
      push_cast
      omega

/-- Every marking a faithful timed run visits is `ReachAD`-reachable. -/
theorem timed_reachAD {rows : List Row} {σ : Type} {step : AMarking × σ → AMarking × σ → Prop}
    (hf : MarkingFaithfulRows rows step) {a0 : AMarking} {s0 : σ} {x : AMarking × σ}
    (h : Relation.ReflTransGen step (a0, s0) x) : ReachAD rows a0 x.1 := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih =>
    rename_i y z _
    obtain ⟨a, s⟩ := y
    obtain ⟨a', s'⟩ := z
    rcases hf a s a' s' hs with rfl | hst
    · exact ih
    · exact Relation.ReflTransGen.tail ih hst

/-- **A bounded-model-check `Proven` of a marking predicate holds under reaping**: at every state
of every faithful (atomic) timed run. The quiescence properties are not marking predicates of
the executor's rest state, and there it fails (`firing_bound_proves_reaped_net`). -/
theorem bmc_proven_marking_timed {rows : List Row} {σ : Type}
    {step : AMarking × σ → AMarking × σ → Prop} (hf : MarkingFaithfulRows rows step)
    {a0 : AMarking} {bad : AMarking → Prop} (hp : ProvenFor (ReachAD rows a0) bad)
    {s0 : σ} {x : AMarking × σ} (h : Relation.ReflTransGen step (a0, s0) x) : ¬ bad x.1 :=
  hp _ (timed_reachAD hf h)

section ReapedWitness

open Libpetri.Novel.ReapingVsUntimed
open Libpetri.Novel.Enumeration

/-- The ranking of the `window(3, 5)` net `p₀ —t→ p₁`: weight 1 on `p₀`. -/
def rR : Weight := fun p => if p = 0 then 1 else 0

theorem netR_wellFormed : WellFormedRows 2 netR := by
  intro tr htr
  simp only [netR, List.mem_singleton] at htr
  subst htr
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro s hs; simp [tR] at hs; subst hs; decide
  · intro p hp; simp [tR] at hp
  · intro p hp; simp at hp; rw [hp]; decide
  · intro p hp; simp [tR] at hp
  · intro p hp; simp [tR] at hp
  · intro s hs; simp [tR] at hs; subst hs; rfl

theorem reaped_ranking : checkRankingExact 2 netR a0R rR = some 1 := by
  simp only [checkRankingExact, netR, canFire, tR, List.all_nil,
    List.all_cons, List.all_nil, Bool.and_true]
  rw [if_pos (by decide)]
  simp [dot, dotProduct, rR, a0R]

theorem reachAD_netR_iff (a : AMarking) : ReachAD netR a0R a ↔ ReachA netR a0R a := by
  have hnd : ∀ ft ∈ netR, ft.2.Nodup := by
    intro ft hft; simp only [netR, List.mem_singleton] at hft; subst hft; simp
  rw [← reach_succRows_iff, ← succNet_eq_succRows hnd, reach_succNet_iff]

/-- **Witness (R16 in the firing-bound phase).** On `ReapingVsUntimed`'s net with sink `{p₁}`:
1. the exact check accepts the ranking `p₀` with bound `K = 1`;
2. for any integer violation agreeing with `DeadlockFree`'s (P5), the depth-1 script has no
   model, so z3 answers `unsat` and the depth loop (`min(1, 8, 512) = 1 ≥ K`) answers
   `Proven` (method `bounded-model-check`);
3. both executors' timed runs over cycles `[0, 10]` halt at `{p₀}` after the reap, stranding the
   token on a non-sink place — a `DeadlockFree` violation of the timed execution.

This is a retrodiction: it describes `firing_bound_decision` as shipped on 2026-09-28, before
the reaping fix, when the script read the strict quiescence. The shipped phase reads
reap-quiescence and answers `Violated` here (`ReapAware.witness_caught`; the Rust integration
test `the_firing_bound_reads_the_reaped_rest`). The gate `gateReaping`, an
alternative that was not taken, answers `.stop` here (`gated_witness_steps_aside`).
-/
theorem firing_bound_proves_reaped_net :
    checkRankingExact 2 netR a0R rR = some 1
    ∧ (∀ badI : (PlaceId → Int) → Prop, BadAgrees badI (dlfBad netR sinksR 2) →
        ¬ BmcSat netR 2 a0R badI 1)
    ∧ phaseDepths 1 512 (fun _ => some false) = .proven
    ∧ (∀ rest : List Nat,
        execRun enforceBB wTiming a0R wInit (0 :: 10 :: rest) = .halted a0R reapedBB
        ∧ execRun enforcePB wTiming a0R wInit (0 :: 10 :: rest) = .halted a0R reapedPB)
    ∧ Strands sinksR 2 a0R := by
  refine ⟨reaped_ranking, fun badI hBad hsat => ?_, rfl,
    (reaping_refutes_ver004_ac3).2.1, (reaping_refutes_ver004_ac3).2.2.1⟩
  obtain ⟨a, hreach, hbad⟩ :=
    (bmc_exact_at_bound netR_wellFormed hBad reaped_ranking (by decide)).mp hsat
  exact untimed_dlf_proven a ((reachAD_netR_iff a).mp hreach) hbad

end ReapedWitness

/-! ## The bridge from `ReapingVsUntimed.MarkingFaithful`

`ReapingVsUntimed` states faithfulness over `StepARel` (flat transitions, `fireA`); the
firing-bound phase works over deposit rows (`StepAD`, `fireAD`). On duplicate-free rows, which
every action branch is ([IO-011]), the two steps are the same (`fireAD_eq_fireA`), so every
executor model `ReapingVsUntimed` proves faithful is one `ranking_bounds_timed` and
`bmc_proven_marking_timed` apply to. -/

/-- `MarkingFaithful` over a flat net with duplicate-free branches is `MarkingFaithfulRows`. -/
theorem markingFaithfulRows_of_markingFaithful {net : FlatNet} (hnd : ∀ ft ∈ net, ft.2.Nodup)
    {σ : Type} {step : AMarking × σ → AMarking × σ → Prop}
    (hf : ReapingVsUntimed.MarkingFaithful net step) : MarkingFaithfulRows net step := by
  intro a s a' s' hs
  rcases hf a s a' s' hs with h | ⟨ft, hm, he, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨ft, hm, he, (fireAD_eq_fireA (hnd ft hm) a ft.1).symm⟩

/-- **The phase's `Proven` of a marking predicate holds under reaping**: with the phase's own
hypotheses, the `Proven` holds at every state of every faithful (atomic) timed run. This is
`phase_proven_sound` composed with `bmc_proven_marking_timed`. -/
theorem phase_proven_timed_marking {rows : List Row} {n : Nat} {a0 : AMarking} {r : Weight}
    {K : Int} {badI : (PlaceId → Int) → Prop} {bad : AMarking → Prop} {maxDepth : Nat}
    {ask : Nat → Option Bool} {σ : Type} {step : AMarking × σ → AMarking × σ → Prop}
    (hf : MarkingFaithfulRows rows step)
    (hWF : WellFormedRows n rows) (hBad : BadAgrees badI bad)
    (hK : checkRankingExact n rows a0 r = some K)
    (hAsk : ∀ d, ask d = some false → ¬ BmcSat rows n a0 badI d)
    (h : phaseDepths K.toNat maxDepth ask = .proven)
    {s0 : σ} {x : AMarking × σ} (hx : Relation.ReflTransGen step (a0, s0) x) : ¬ bad x.1 :=
  bmc_proven_marking_timed hf (phase_proven_sound hWF hBad hK hAsk h) hx

section ExecutorInstance

open Libpetri.Novel.ReapingVsUntimed

/-- The cell an executor cycle leaves, running or halted. -/
def outcomeCell : Outcome → Cell
  | .running _ s => s
  | .halted _ s => s

/-- One cycle of `ReapingVsUntimed`'s executor model of `netR` (`execCycle`: update, enforce
deadlines, the termination test, fire), at some timestamp, as a step on (marking, cell). A halt
is a state the relation may step on from, which only adds states, so every claim over this
relation covers the real runs. The shipped enforcement path (`enforceBB`, both backends), the
pre-ruling precompiled one (`enforcePB`) and every timing are instances. -/
def execStep (enforce : Nat → Nat → Cell → Cell) (tm : Timing) (x y : AMarking × Cell) : Prop :=
  ∃ now, (execCycle enforce tm now x.1 x.2).marking = y.1
    ∧ outcomeCell (execCycle enforce tm now x.1 x.2) = y.2

theorem execStep_faithful (enforce : Nat → Nat → Cell → Cell) (tm : Timing) :
    MarkingFaithful netR (execStep enforce tm) := by
  rintro a s a' s' ⟨now, h1, _⟩
  simp only at h1
  rw [← h1]
  exact execCycle_faithful enforce tm now a s

/-- **`MarkingFaithfulRows` is discharged for the executor model of `netR`.** -/
theorem execStep_faithfulRows (enforce : Nat → Nat → Cell → Cell) (tm : Timing) :
    MarkingFaithfulRows netR (execStep enforce tm) :=
  markingFaithfulRows_of_markingFaithful
    (by intro ft hft; simp only [netR, List.mem_singleton] at hft; subst hft; simp)
    (execStep_faithful enforce tm)

/-- Every run over a schedule is a path of `execStep`. -/
theorem execRun_path (enforce : Nat → Nat → Cell → Cell) (tm : Timing) :
    ∀ (nows : List Nat) (a : AMarking) (s : Cell),
      Relation.ReflTransGen (execStep enforce tm) (a, s)
        ((execRun enforce tm a s nows).marking, outcomeCell (execRun enforce tm a s nows))
  | [], _, _ => Relation.ReflTransGen.refl
  | now :: rest, a, s => by
    have hst : execStep enforce tm (a, s)
        ((execCycle enforce tm now a s).marking, outcomeCell (execCycle enforce tm now a s)) :=
      ⟨now, rfl, rfl⟩
    unfold execRun
    split
    · rename_i a' s' heq
      rw [heq] at hst
      exact Relation.ReflTransGen.single hst
    · rename_i a' s' heq
      rw [heq] at hst
      exact Relation.ReflTransGen.head hst (execRun_path enforce tm rest a' s')

/-- **The firing bound on the executor model** (instance of `ranking_bounds_timed`): every
timed run of `netR` from `{p₀}`, under either enforcement path and any timing and schedule,
changes its marking at most `K = 1` time, reaps included. -/
theorem ranking_bounds_timed_netR (enforce : Nat → Nat → Cell → Cell) (tm : Timing) {k : Nat}
    {x y : AMarking × Cell} (h : TimedRun (execStep enforce tm) k x y) (hx : x.1 = a0R) :
    k ≤ 1 := by
  obtain ⟨hr, hK⟩ := checkRankingExact_sound reaped_ranking
  have hb := ranking_bounds_timed (execStep_faithfulRows enforce tm) hr h
  have hy := dot_nonneg hr.1 y.1
  rw [hx, ← hK] at hb
  omega

/-- **A phase `Proven` of a marking predicate holds on the executor model** (instance of
`phase_proven_timed_marking`): at the marking every run of `netR` ends at, under either
enforcement path, any timing and any schedule. -/
theorem phase_proven_timed_marking_netR {r : Weight} {K : Int}
    {badI : (PlaceId → Int) → Prop} {bad : AMarking → Prop} {maxDepth : Nat}
    {ask : Nat → Option Bool} (hBad : BadAgrees badI bad)
    (hK : checkRankingExact 2 netR a0R r = some K)
    (hAsk : ∀ d, ask d = some false → ¬ BmcSat netR 2 a0R badI d)
    (h : phaseDepths K.toNat maxDepth ask = .proven)
    (enforce : Nat → Nat → Cell → Cell) (tm : Timing) (s0 : Cell) (nows : List Nat) :
    ¬ bad (execRun enforce tm a0R s0 nows).marking :=
  phase_proven_timed_marking (execStep_faithfulRows enforce tm) netR_wellFormed hBad hK hAsk h
    (execRun_path enforce tm nows a0R s0)

/-! ## Without reaping the rest state is untimed-quiescent

The stranding of `firing_bound_proves_reaped_net` is the reap's: an executor whose deadline
enforcement never changes a cell (`NoReap`, what `enforce_deadlines` is on a net with no
`Deadline` / `Window` transition: its loop skips every other timing) halts only at a marking
where the untimed net enables nothing. There the untimed `DeadlockFree` violation is exactly
the timed one, so the untimed `Proven` holds of the timed rest state. -/

/-- Deadline enforcement that never changes a cell. -/
def NoReap (enforce : Nat → Nat → Cell → Cell) : Prop := ∀ l now s, enforce l now s = s

/-- The enabled bit agrees with the live marking unless the cell is dirty (the dirty-set
invariant both backends keep: every token mutation marks the transition dirty). -/
def Synced (a : AMarking) (s : Cell) : Prop := s.dirty = true ∨ s.enabled = enabledA a tR

/-- After the update phase a synced cell's enabled bit is the live marking's enablement, and
the cell is clean. -/
theorem update_synced {a : AMarking} {s : Cell} (hs : Synced a s) (now : Nat) :
    (updateCell now { s with tokens := enabledA a tR }).enabled = enabledA a tR
    ∧ (updateCell now { s with tokens := enabledA a tR }).dirty = false := by
  obtain ⟨tk, en, cl, dt⟩ := s
  unfold Synced at hs
  simp only at hs
  cases dt <;> cases en <;> cases he : enabledA a tR <;> simp_all [updateCell]

/-- Without reaping, a cycle from a synced cell halts only at an untimed-quiescent marking, and
a running cycle leaves a synced cell. -/
theorem cycle_noReap {enforce : Nat → Nat → Cell → Cell} (hnr : NoReap enforce) (tm : Timing)
    (now : Nat) {a : AMarking} {s : Cell} (hs : Synced a s) :
    (∀ a' s', execCycle enforce tm now a s = .halted a' s' → a' = a ∧ enabledA a tR = false)
    ∧ (∀ a' s', execCycle enforce tm now a s = .running a' s' → Synced a' s') := by
  obtain ⟨hen, _⟩ := update_synced hs now
  unfold execCycle
  dsimp only
  rw [hnr]
  constructor
  · intro a' s' h
    split at h
    · rename_i hc
      cases h
      exact ⟨rfl, by rw [← hen]; exact hc⟩
    · split at h <;> cases h
  · intro a' s' h
    split at h
    · cases h
    · split at h
      · cases h; left; rfl
      · cases h; right; exact hen

/-- Without reaping, a run from a synced cell halts only at an untimed-quiescent marking. -/
theorem noReap_halt_quiescent {enforce : Nat → Nat → Cell → Cell} (hnr : NoReap enforce)
    (tm : Timing) :
    ∀ (nows : List Nat) (a : AMarking) (s : Cell), Synced a s →
      ∀ a' s', execRun enforce tm a s nows = .halted a' s' → QuiescentA netR a'
  | [], _, _, _, _, _, h => by simp [execRun] at h
  | now :: rest, a, s, hs, a', s', h => by
    obtain ⟨hhalt, hrun⟩ := cycle_noReap hnr tm now hs
    unfold execRun at h
    split at h
    · rename_i b c heq
      cases h
      obtain ⟨rfl, hq⟩ := hhalt _ _ heq
      intro ft hft
      simp only [netR, List.mem_singleton] at hft
      subst hft
      exact hq
    · rename_i b c heq
      exact noReap_halt_quiescent hnr tm rest b c (hrun _ _ heq) a' s' h

/-- The timed `DeadlockFree` of the executor model with sinks `sinks`: every run of `netR` from
`{p₀}` and the initial cell that halts comes to rest with no token on a non-sink place. -/
def TimedDeadlockFree (sinks : List PlaceId) (enforce : Nat → Nat → Cell → Cell) (tm : Timing) :
    Prop :=
  ∀ nows a' s', execRun enforce tm a0R wInit nows = .halted a' s' → ¬ Strands sinks 2 a'

/-- **Without reaping, the untimed `Proven` is the timed one**: an untimed `DeadlockFree`
`Proven` of `netR` gives `TimedDeadlockFree` for every enforcement that never reaps, any timing
and any schedule. -/
theorem noReap_timedDeadlockFree {sinks : List PlaceId}
    (hp : ProvenFor (ReachA netR a0R) (dlfBad netR sinks 2))
    {enforce : Nat → Nat → Cell → Cell} (hnr : NoReap enforce)
    (tm : Timing) : TimedDeadlockFree sinks enforce tm := by
  intro nows a' s' h hstr
  have hq := noReap_halt_quiescent hnr tm nows a0R wInit (Or.inl rfl) a' s' h
  have hreach := timed_marking_run_reachable enforce tm nows a0R wInit ReachA.init
  rw [h] at hreach
  exact hp a' hreach ⟨hq, hstr⟩

/-- With reaping it fails: `enforceBB` / `enforcePB` at `window(3, 5)` over `[0, 10]`, although
the untimed `DeadlockFree` is `Proven` (`untimed_dlf_proven`). -/
theorem reaping_not_timedDeadlockFree :
    ¬ TimedDeadlockFree sinksR enforceBB wTiming ∧ ¬ TimedDeadlockFree sinksR enforcePB wTiming := by
  obtain ⟨_, hrun, hstr, _⟩ := reaping_refutes_ver004_ac3
  exact ⟨fun h => h [0, 10] _ _ (hrun []).1 hstr, fun h => h [0, 10] _ _ (hrun []).2 hstr⟩

/-! ## A reaping gate on the phase's verdict (an alternative that was not taken)

One form the "verification accounts for deadline reaping" fix could have taken at the
firing-bound phase: a `Proven` of a quiescence property (`DeadlockFree`, `TerminatesAtSink`,
`QuiescentCount`, `JoinedOrDeadLettered`) on a net with a `Deadline` / `Window` transition steps
aside; marking properties and nets with nothing to reap keep the phase's verdict. `gateReaping`
models that filter on the depth loop's outcome. It is not a model of shipped code: the fix that
landed reads reap-quiescence in the phase's script and replay instead (`ReapAware.lean`), and
`firing_bound_decision` has no such gate. -/

/-- The two property classes of [VER-002] under reaping. -/
inductive PropClass where
  | marking
  | quiescence
  deriving DecidableEq, Repr

/-- The gate: `hasReapable` is "some transition has `Deadline` or `Window` timing". -/
def gateReaping : PropClass → Bool → DepthOutcome → DepthOutcome
  | .quiescence, true, .proven => .stop
  | _, _, o => o

theorem gateReaping_marking (b : Bool) (o : DepthOutcome) : gateReaping .marking b o = o := by
  cases b <;> cases o <;> rfl

theorem gateReaping_unreapable (c : PropClass) (o : DepthOutcome) :
    gateReaping c false o = o := by
  cases c <;> cases o <;> rfl

/-- A gated `Proven` is the phase's `Proven`, and for a quiescence property the net has nothing
to reap. -/
theorem gateReaping_proven {c : PropClass} {b : Bool} {o : DepthOutcome}
    (h : gateReaping c b o = .proven) : o = .proven ∧ (c = .quiescence → b = false) := by
  cases c <;> cases b <;> cases o <;> simp_all [gateReaping]

/-- **The gate closes R16 on the witness**: the gated phase does not answer `Proven` for
`DeadlockFree` on the `window(3, 5)` net. -/
theorem gated_witness_steps_aside :
    gateReaping .quiescence true (phaseDepths 1 512 (fun _ => some false)) = .stop := rfl

/-- **The gated `Proven` for `DeadlockFree` holds of the timed executor model of `netR`.**
Premise (P8): an executor on a net with no `Deadline` / `Window` transition never reaps
(`hasReapable = false → NoReap enforce`). Then a gated `Proven` gives `TimedDeadlockFree`, for
any timing and schedule; with a reapable transition the gate never answers `Proven`. -/
theorem gated_dlf_timed_sound_netR {sinks : List PlaceId} {r : Weight} {K : Int}
    {badI : (PlaceId → Int) → Prop} {maxDepth : Nat} {ask : Nat → Option Bool}
    {hasReapable : Bool} {enforce : Nat → Nat → Cell → Cell} (tm : Timing)
    (hP8 : hasReapable = false → NoReap enforce)
    (hBad : BadAgrees badI (dlfBad netR sinks 2))
    (hK : checkRankingExact 2 netR a0R r = some K)
    (hAsk : ∀ d, ask d = some false → ¬ BmcSat netR 2 a0R badI d)
    (h : gateReaping .quiescence hasReapable (phaseDepths K.toNat maxDepth ask) = .proven) :
    TimedDeadlockFree sinks enforce tm := by
  obtain ⟨hph, hb⟩ := gateReaping_proven h
  have hp := phase_proven_sound netR_wellFormed hBad hK hAsk hph
  exact noReap_timedDeadlockFree (fun a ha => hp a ((reachAD_netR_iff a).mpr ha))
    (hP8 (hb rfl)) tm

end ExecutorInstance

end Libpetri.Novel.FiringBound
