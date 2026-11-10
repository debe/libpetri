import Libpetri.Novel.FiringBound.Bmc
import Libpetri.Novel.EnvSemantics.Step
import Libpetri.StateEquation

/-!
# The bounded witness phase ([VER-025])

Model of the witness phase the ports implement (contract `tasks/ver025-contract.md`): in
`bounded_run.rs`, `run_witness_phase` and the private `witness_phase` it wraps, the trim
`trim_run` with its `violating_prefix`, and `StepRelation`, the one place a step is taken; in
`smt_verifier.rs`, the call site in the flat branch of `verify_net`, its gate
`witness_phase_applies` and its handover `witness_decision`. One bounded-run query at depth `D`
over firings and injection steps (`BmcModelEnv`, `Bmc.lean`), the decode at `stepCount = T + J`
(`decodeModel`), the replay (`replayRun`), the solver-free trim (`trim`: the cut to the violating
prefix, then passes from the last step to the first), the outcome (`witnessPhase`), and the
pipeline around it (`pipeline`). See `Libpetri/Novel/FiringBound.lean`.

Results:
* `replayRun_sound`: a run `replay_run` accepts is a run of `StepEnv` from `M0` whose last
  marking violates, every index a step index in `[0, T + J)`.
* `trim_sound`, `trim_sublist`, `trim_first`, `trim_irredundant`, `trim_initial`: the trim keeps
  a replaying run replaying, only drops steps, ends at the first violating marking it reaches,
  ends at a run no single step of which can be dropped, and is the empty run when `M0` violates.
  It makes no claim that the run is a shortest one.
* `witnessPhase_violated_sound`: a `violated` outcome is the trim of a `sat` model's decoded run
  that replays, a replayed, irredundant run of at most `D` steps from `M0` that ends at the first
  violating marking it reaches, and the empty run when `M0` violates.
* `witnessPhase_noRun_exact`: `noRun` comes only from `unsat`, and, with the solver's `unsat`
  truthful (P4), no run of at most `D` steps reaches a violation (`bmcEnv_complete`). That is the
  report line "no run of at most D steps reaches a violation", and nothing more: it is not a
  proof of the property.
* `witnessPhase_sat_violated`: a truthful `sat` whose model defines its selectors always ends
  `violated`; the replay never turns such a model away.
* `pipeline_some_eq`, `witnessPhase_never_proven` / `pipeline_eq_fixpoint`: unless the phase
  answered `violated`, the pipeline's verdict is the fixpoint route's at the total budget minus
  the time the phase spent, so the phase never produces `Proven` and changes no verdict except
  through the budget it spends.
* `witnessPhase_depth0`: at `D = 0` the phase is skipped and the pipeline is the one without it.
* `stepEnv_injsOf` / `reachEnv_injsOf`: at the injection list the verifier builds
  (`env_injection`: every environment place, one mode), `StepEnv` is `EnvSemantics.StepAE`, the
  open system the CHC rules of `encode_net` describe without their strengthening conjuncts.
* `witness_horn_derivation`: on duplicate-free rows ([IO-011]) and with gate-validated laws
  (H1, H2, H3′), every marking a replayed witness reaches is reachable in the **strengthened**
  CHC system as well: P-invariant equalities, state-equation rows and firing counters
  ([VER-016]), post-caps and the `Bounded(k)` guard included (`ReachHorn`). A replayed witness is
  a derivation of `Error` in the system the fixpoint query solves.

Premises: P1, P2, P5 and P7 as in `FiringBound.lean`; P4 for the `unsat` reading only (as the
hypothesis `hTruth`); for the converse of the encoding, P9 (`InjsDistinct`) and a seed within the
caps, which `bounded_premise_violation` checks before any route ([VER-006] AC3,
`EnvSemantics/Premise.lean`).

Not modelled: the SMT-LIB text (P4), the reply's text (a model is the selector values it defines,
`Witness.Answer.sat`; a reply with an `(error …)` line is the answer `failure`), the transport and
its budget clamp (an outcome `inconclusive` stands for each), the budget arithmetic
`max(1, floor(timeoutMs / 8))` (`elapsed` is any number), the report text, and the ν guard and the
counterexample-timing step that the result passes through afterwards ([VER-023]). Nor the stop
`trim_run` polls before every candidate ([VER-013]: total budget and cancellation, both abstract
here): a stop ends the phase without a run (`WitnessOutcome::Stopped`), which `witness_decision`
hands over like `noRun`, and the pipeline's next step ends the query `Unknown` with the stop's
reason. A stop inside the query comes back as the transport's failure (`Inconclusive`), and
`witness_decision` then cuts the total budget and prints the stop's reason in the status line in
place of the transport's, so a stop in the query and a stop in the trim read alike. The model's
`trim` is the run `trim_run` returns when no stop occurs.
-/

namespace Libpetri.Novel.FiringBound

open Libpetri
open Libpetri.Novel.ForwardDeposit
open Libpetri.Novel.EnvSemantics (InjMode StepAE ReachAE injA)

/-! ## `replay_run` -/

/-- **`replay_run`** with injection steps (contract section 5): every step accepted
(`replayEnv`), then the property at the last marking (`is_bad`, as
`abstract_replay::violation_predicate` builds it). -/
def replayRun (rows : List Row) (injs : List Inj) (isBad : AMarking → Bool) (a0 : AMarking)
    (ts : List Nat) : Option AMarking :=
  (replayEnv rows injs a0 ts).bind fun a => if isBad a = true then some a else none

/-- `replay_run(…).is_some()`: the run replays to a violation. -/
def replays (rows : List Row) (injs : List Inj) (isBad : AMarking → Bool) (a0 : AMarking)
    (ts : List Nat) : Bool :=
  (replayRun rows injs isBad a0 ts).isSome

theorem replays_iff {rows : List Row} {injs : List Inj} {isBad : AMarking → Bool}
    {a0 : AMarking} {ts : List Nat} :
    replays rows injs isBad a0 ts = true ↔
      ∃ a, replayEnv rows injs a0 ts = some a ∧ isBad a = true := by
  unfold replays replayRun
  cases h : replayEnv rows injs a0 ts with
  | none => simp
  | some a =>
    simp only [Option.bind_some]
    by_cases hb : isBad a = true
    · simp [hb]
    · simp [hb]

/-- **A run `replay_run` accepts is a run of `StepEnv` from `M0` to a violating marking**, and
every index it takes is a step index in `[0, T + J)`. -/
@[evidence cites "VER-025" "a run replay_run accepts is a run of StepEnv from M0 to a violating marking, every index a step index in [0, T + J)"]
theorem replayRun_sound {rows : List Row} {injs : List Inj} {isBad : AMarking → Bool}
    {a0 : AMarking} {ts : List Nat} (h : replays rows injs isBad a0 ts = true) :
    ∃ a, replayEnv rows injs a0 ts = some a ∧ isBad a = true ∧ ReachEnv rows injs a0 a ∧
      ∀ t ∈ ts, t < rows.length + injs.length := by
  obtain ⟨a, hrep, hbad⟩ := replays_iff.mp h
  exact ⟨a, hrep, hbad, replayEnv_sound hrep, replayEnv_lt hrep⟩

/-! ## The trim (contract section 6)

`ok` is any acceptance test on runs; the phase uses `replays`. `violatingPrefix ok r` is the
shortest prefix of `r` that `ok` accepts (the empty prefix is `M0`). The trim first cuts the run
to its violating prefix. One pass then walks the indices from the last down to `0`, each time
replacing the run by the violating prefix of the run without the step at that index, when there
is one; the loop repeats passes until one changes nothing. A replacement always shortens the
run, so "changes nothing" and "keeps the length" agree. -/

/-- **`violatingPrefix`**: the shortest prefix of `run` that `ok` accepts, the empty one
included; `none` when no prefix is accepted. With `ok = replays …` it is `violating_prefix`
(`bounded_run.rs`): the run cut at the first violating marking it reaches, the violation tested
before each step and after the last; a step after that marking need not be enabled. The Rust
answers `None` at a step `StepRelation::step` refuses before any violating marking, which is
this answer too: no prefix through a refused step replays. -/
def violatingPrefix (ok : List Nat → Bool) (run : List Nat) : Option (List Nat) :=
  ((List.range (run.length + 1)).find? fun i => ok (run.take i)).map run.take

/-- What `violatingPrefix` returns: an accepted prefix of the run, none of whose own proper
prefixes is accepted. -/
theorem violatingPrefix_spec {ok : List Nat → Bool} {run c : List Nat}
    (h : violatingPrefix ok run = some c) :
    ok c = true ∧ c <+: run ∧ ∀ j, j < c.length → ok (c.take j) = false := by
  unfold violatingPrefix at h
  cases hf : (List.range (run.length + 1)).find? (fun i => ok (run.take i)) with
  | none => rw [hf] at h; cases h
  | some i =>
    rw [hf, Option.map_some] at h
    cases h
    obtain ⟨hi, -, hlt⟩ := List.find?_range_eq_some.mp hf
    refine ⟨hi, List.take_prefix _ _, fun j hj => ?_⟩
    have hj' : j < i := lt_of_lt_of_le hj (List.length_take_le _ _)
    rw [List.take_take, Nat.min_eq_left hj'.le]
    simpa using hlt j hj'

/-- `none` means no prefix at all is accepted, the whole run included. -/
theorem violatingPrefix_none {ok : List Nat → Bool} {run : List Nat}
    (h : violatingPrefix ok run = none) : ∀ j, j ≤ run.length → ok (run.take j) = false := by
  intro j hj
  unfold violatingPrefix at h
  rw [Option.map_eq_none_iff, List.find?_eq_none] at h
  simpa using h j (List.mem_range.mpr (Nat.lt_succ_of_le hj))

/-- An accepted run has a violating prefix. -/
theorem violatingPrefix_isSome {ok : List Nat → Bool} {run : List Nat} (h : ok run = true) :
    ∃ c, violatingPrefix ok run = some c := by
  cases hv : violatingPrefix ok run with
  | some c => exact ⟨c, rfl⟩
  | none =>
    have := violatingPrefix_none hv run.length (le_refl _)
    rw [List.take_length] at this
    rw [h] at this; cases this

/-- The step of a pass at index `k`: the violating prefix of the run without step `k`, when
`k` is an index of the run and that prefix exists; the run itself otherwise. `trim_run`'s
`candidate.remove(k)`; there `k` is always an index of the run, since a replacement at `k`
keeps more than `k` steps. -/
def trimStep (ok : List Nat → Bool) (k : Nat) (run : List Nat) : List Nat :=
  if k < run.length then (violatingPrefix ok (run.eraseIdx k)).getD run else run

/-- The pass from index `k - 1` down to `0` over the current run. -/
def passFrom (ok : List Nat → Bool) : Nat → List Nat → List Nat
  | 0, run => run
  | k + 1, run => passFrom ok k (trimStep ok k run)

/-- One pass, from the last index of the run down to `0`. -/
def trimPass (ok : List Nat → Bool) (run : List Nat) : List Nat :=
  passFrom ok run.length run

/-- Passes until one changes nothing. A pass that changes something shortens the run, so
`fuel = |run| + 1` passes always reach one that changes nothing (`trimLoop_fixed`). -/
def trimLoop (ok : List Nat → Bool) : Nat → List Nat → List Nat
  | 0, run => run
  | fuel + 1, run =>
    if (trimPass ok run).length = run.length then run else trimLoop ok fuel (trimPass ok run)

/-- **The trim** of contract section 6, total: the cut to the violating prefix, then the passes.
A run without a violating prefix (which the phase never trims) is passed on uncut.

`trim_run` (`bounded_run.rs`) loops passes until one keeps the length, with no fuel; a pass that
changes the run shortens it, so `|run| + 1` passes suffice here (`trimLoop_fixed`). It also polls
the verification's stop ([VER-013]) before every candidate and answers `None` on a stop; that
poll is not modelled (budget and cancellation are abstract). A stop ends the phase
(`WitnessOutcome::Stopped`), and `trim` is the run `trim_run` returns when no stop occurs. -/
def trim (ok : List Nat → Bool) (run : List Nat) : List Nat :=
  trimLoop ok (run.length + 1) ((violatingPrefix ok run).getD run)

/-- The invariant the trim keeps: the run is accepted and no proper prefix of it is (it ends at
the first violating marking it reaches). -/
def FirstOk (ok : List Nat → Bool) (run : List Nat) : Prop :=
  ok run = true ∧ ∀ j, j < run.length → ok (run.take j) = false

theorem firstOk_of_violatingPrefix {ok : List Nat → Bool} {run c : List Nat}
    (h : violatingPrefix ok run = some c) : FirstOk ok c :=
  ⟨(violatingPrefix_spec h).1, (violatingPrefix_spec h).2.2⟩

theorem trimStep_sublist (ok : List Nat → Bool) (k : Nat) (run : List Nat) :
    (trimStep ok k run).Sublist run := by
  unfold trimStep
  split
  · cases hv : violatingPrefix ok (run.eraseIdx k) with
    | none => exact List.Sublist.refl run
    | some c =>
      exact (violatingPrefix_spec hv).2.1.sublist.trans (List.eraseIdx_sublist run k)
  · exact List.Sublist.refl run

theorem trimStep_firstOk (ok : List Nat → Bool) (k : Nat) {run : List Nat}
    (h : FirstOk ok run) : FirstOk ok (trimStep ok k run) := by
  unfold trimStep
  split
  · cases hv : violatingPrefix ok (run.eraseIdx k) with
    | none => exact h
    | some c => exact firstOk_of_violatingPrefix hv
  · exact h

/-- A step that keeps the length changes nothing, and found no violating prefix at `k`. -/
theorem trimStep_keeps (ok : List Nat → Bool) (k : Nat) (run : List Nat)
    (hlen : (trimStep ok k run).length = run.length) :
    trimStep ok k run = run ∧ (k < run.length → violatingPrefix ok (run.eraseIdx k) = none) := by
  unfold trimStep at hlen ⊢
  by_cases hk : k < run.length
  · rw [if_pos hk] at hlen ⊢
    cases hv : violatingPrefix ok (run.eraseIdx k) with
    | none => exact ⟨rfl, fun _ => rfl⟩
    | some c =>
      exfalso
      rw [hv, Option.getD_some] at hlen
      have hle := (violatingPrefix_spec hv).2.1.sublist.length_le
      rw [List.length_eraseIdx, if_pos hk] at hle
      omega
  · rw [if_neg hk]; exact ⟨rfl, fun h => absurd h hk⟩

theorem passFrom_sublist (ok : List Nat → Bool) :
    ∀ k run, (passFrom ok k run).Sublist run
  | 0, run => List.Sublist.refl run
  | k + 1, run => (passFrom_sublist ok k _).trans (trimStep_sublist ok k run)

theorem passFrom_firstOk (ok : List Nat → Bool) :
    ∀ k run, FirstOk ok run → FirstOk ok (passFrom ok k run)
  | 0, _, h => h
  | k + 1, _, h => passFrom_firstOk ok k _ (trimStep_firstOk ok k h)

/-- A pass that keeps the length has tried every index below `k` and found no violating prefix
of the run without it. -/
theorem passFrom_keeps (ok : List Nat → Bool) :
    ∀ k run, (passFrom ok k run).length = run.length →
      ∀ i, i < k → i < run.length → violatingPrefix ok (run.eraseIdx i) = none
  | 0, _, _, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | k + 1, run, hlen, i, hi, hil => by
    simp only [passFrom] at hlen
    have h1 := (passFrom_sublist ok k (trimStep ok k run)).length_le
    have h2 := (trimStep_sublist ok k run).length_le
    obtain ⟨heq, hnone⟩ := trimStep_keeps ok k run (by omega)
    rw [heq] at hlen
    by_cases hik : i < k
    · exact passFrom_keeps ok k run hlen i hik hil
    · have hik' : i = k := by omega
      subst hik'
      exact hnone hil

theorem trimLoop_sublist (ok : List Nat → Bool) :
    ∀ fuel run, (trimLoop ok fuel run).Sublist run
  | 0, run => List.Sublist.refl run
  | fuel + 1, run => by
    simp only [trimLoop]
    split
    · exact List.Sublist.refl run
    · exact (trimLoop_sublist ok fuel _).trans (passFrom_sublist ok _ run)

theorem trimLoop_firstOk (ok : List Nat → Bool) :
    ∀ fuel run, FirstOk ok run → FirstOk ok (trimLoop ok fuel run)
  | 0, _, h => h
  | fuel + 1, run, h => by
    simp only [trimLoop]
    split
    · exact h
    · exact trimLoop_firstOk ok fuel _ (passFrom_firstOk ok _ run h)

/-- With more fuel than steps the loop ends at a run that a pass leaves alone. -/
theorem trimLoop_fixed (ok : List Nat → Bool) :
    ∀ fuel run, run.length < fuel →
      (trimPass ok (trimLoop ok fuel run)).length = (trimLoop ok fuel run).length
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, run, h => by
    simp only [trimLoop]
    split
    · rename_i heq; exact heq
    · rename_i hne
      have hle := (passFrom_sublist ok run.length run).length_le
      exact trimLoop_fixed ok fuel _ (by unfold trimPass at hne ⊢; omega)

/-- **The trim only drops steps**: its output is a sublist of its input. -/
@[evidence cites "VER-025" "the trim only drops steps: the trimmed run is a sublist of the decoded run"]
theorem trim_sublist (ok : List Nat → Bool) (run : List Nat) : (trim ok run).Sublist run := by
  unfold trim
  refine (trimLoop_sublist ok _ _).trans ?_
  cases hv : violatingPrefix ok run with
  | none => exact List.Sublist.refl run
  | some c => exact (violatingPrefix_spec hv).2.1.sublist

/-- The trim of an accepted run keeps the invariant: accepted, no proper prefix accepted. -/
theorem trim_firstOk (ok : List Nat → Bool) {run : List Nat} (h : ok run = true) :
    FirstOk ok (trim ok run) := by
  obtain ⟨c, hc⟩ := violatingPrefix_isSome h
  unfold trim
  rw [hc, Option.getD_some]
  exact trimLoop_firstOk ok _ c (firstOk_of_violatingPrefix hc)

/-- **The trim keeps a replaying run replaying.** -/
@[evidence cites "VER-025" "the trim keeps a replaying run replaying"]
theorem trim_sound (ok : List Nat → Bool) {run : List Nat} (h : ok run = true) :
    ok (trim ok run) = true :=
  (trim_firstOk ok h).1

/-- **The trimmed run ends at the first violating marking it reaches**: no proper prefix of it
is accepted. -/
@[evidence cites "VER-025" "the trimmed run ends at the first violating marking it reaches: no proper prefix of it replays to a violation"]
theorem trim_first (ok : List Nat → Bool) {run : List Nat} (h : ok run = true) :
    ∀ j, j < (trim ok run).length → ok ((trim ok run).take j) = false :=
  (trim_firstOk ok h).2

/-- **When `M0` violates, the trimmed run is empty**, whatever run was trimmed. -/
@[evidence cites "VER-025" "when M0 violates the trimmed run is the empty one, whatever model the solver returned"]
theorem trim_initial (ok : List Nat → Bool) {run : List Nat} (h : ok run = true)
    (h0 : ok [] = true) : trim ok run = [] := by
  cases ht : trim ok run with
  | nil => rfl
  | cons x xs =>
    have := trim_first ok h 0 (by rw [ht]; exact Nat.zero_lt_succ _)
    rw [List.take_zero, h0] at this
    cases this

/-- **No step of the trimmed run can be dropped**: without any single step, no prefix of the rest
is accepted. -/
theorem trim_irredundant_prefix (ok : List Nat → Bool) (run : List Nat) :
    ∀ k, k < (trim ok run).length → violatingPrefix ok ((trim ok run).eraseIdx k) = none := by
  intro k hk
  have hfix := trimLoop_fixed ok (run.length + 1) ((violatingPrefix ok run).getD run) (by
    cases hv : violatingPrefix ok run with
    | none => exact Nat.lt_succ_self _
    | some c =>
      have := (violatingPrefix_spec hv).2.1.sublist.length_le
      rw [Option.getD_some]; omega)
  exact passFrom_keeps ok _ _ hfix k hk hk

/-- **The trimmed run is irredundant**: no single step of it can be dropped with the rest still
accepted. Irredundant, not shortest: a shorter run that is not a sublist may exist. -/
@[evidence cites "VER-025" "the trimmed run is irredundant: dropping any single step leaves a run no prefix of which replays to a violation; not claimed shortest"]
theorem trim_irredundant (ok : List Nat → Bool) (run : List Nat) :
    ∀ k, k < (trim ok run).length → ok ((trim ok run).eraseIdx k) = false := by
  intro k hk
  have := violatingPrefix_none (trim_irredundant_prefix ok run k hk) _ (le_refl _)
  rwa [List.take_length] at this

/-! ## The phase: `run_witness_phase` -/

/-- What the solver gave for the depth-`D` script: `sat` with the model's selectors (`none` for a
selector the model does not define), `unsat`, `unknown`, a transport failure, or the phase's
budget spent before an answer. -/
inductive Witness.Answer where
  | sat (s : Nat → Option Int)
  | unsat
  | unknown
  | failure
  | budgetSpent

/-- A model that defines every selector, with the values `s`. -/
def Witness.defined (s : Nat → Int) : Nat → Option Int := fun i => some (s i)

/-- **`decode_bounded_run` on a model**: no run (`none`) when the depth is positive and the model
defines none of the selectors `s0 … s(D−1)`; otherwise the run `decodeRust` reads, with a selector
the model is silent on read as idle (the value `T`, which `decodeSel T` maps to idle). -/
def decodeModel (T : Nat) (s : Nat → Option Int) (D : Nat) : Option (List Nat) :=
  if D = 0 ∨ (List.range D).any (fun i => (s i).isSome) then
    some (decodeRust T (fun i => (s i).getD (T : Int)) D)
  else none

/-- A model that defines its selectors decodes to the run `decodeRust` reads from them. -/
theorem decodeModel_defined (T : Nat) (s : Nat → Int) (D : Nat) :
    decodeModel T (Witness.defined s) D = some (decodeRust T s D) := by
  unfold decodeModel Witness.defined
  rw [if_pos]
  · rfl
  · rcases Nat.eq_zero_or_pos D with h | h
    · exact Or.inl h
    · exact Or.inr (List.any_eq_true.mpr ⟨0, List.mem_range.mpr h, rfl⟩)

theorem decodeModel_length_le {T : Nat} {s : Nat → Option Int} {D : Nat} {run : List Nat}
    (h : decodeModel T s D = some run) : run.length ≤ D := by
  unfold decodeModel at h
  split at h
  · cases h; rw [decodeRust_eq_decode]; exact decode_length_le _ _ _
  · cases h

/-- Why the phase is inconclusive (contract section 8). A reply with an `(error …)` line is a
failed query (`transport`). -/
inductive Witness.Reason where
  | transport
  | budget
  | unknown
  | noReplay
  | nameAlignment
  deriving DecidableEq, Repr

/-- The phase's outcome, `WitnessOutcome` (`bounded_run.rs`; not `parikh_search`'s type of the
same name) without its `Stopped` case (see `trim`). There is no `proven` constructor: the phase
never proves anything. -/
inductive Witness.Outcome where
  /-- `a run of <n> steps reaches a violation (replayed; depth <D>)`. -/
  | violated (run : List Nat)
  /-- `no run of at most <D> steps reaches a violation (not a proof)`. -/
  | noRun
  /-- `inconclusive (<reason>)`. -/
  | inconclusive (reason : Witness.Reason)
  deriving DecidableEq, Repr

/-- **`run_witness_phase` and its gates** (contract sections 3, 5, 6, 8). `none` is a skipped
phase: `D = 0`, or the section 3 gate closed (`enter = false`: the net has match transitions
and either the property is not reachability-safety or no budget place is declared); together
they are `witness_phase_applies` (`smt_verifier.rs`), which `verify_net` asks on the flat
encoding only. A name-alignment property is refused, `witness_phase`'s first check. Otherwise
the solver's answer decides: `sat` is decoded at `T + J`, replayed (`replay_run`), and, when the
whole decoded run replays, trimmed (`trim_run`). A model that defines no selector yields no run,
as one whose run does not replay. -/
def witnessPhase (D : Nat) (enter nameAlignment : Bool) (rows : List Row) (injs : List Inj)
    (a0 : AMarking) (isBad : AMarking → Bool) (ans : Witness.Answer) :
    Option Witness.Outcome :=
  if D = 0 ∨ enter = false then none
  else if nameAlignment = true then some (.inconclusive .nameAlignment)
  else
    some <| match ans with
    | .sat s =>
      match decodeModel (rows.length + injs.length) s D with
      | none => .inconclusive .noReplay
      | some run =>
        if replays rows injs isBad a0 run = true then
          .violated (trim (replays rows injs isBad a0) run)
        else .inconclusive .noReplay
    | .unsat => .noRun
    | .unknown => .inconclusive .unknown
    | .failure => .inconclusive .transport
    | .budgetSpent => .inconclusive .budget

/-- A verdict of the pipeline. -/
inductive Witness.Verdict where
  | proven
  | violated (run : List Nat)
  | unknown
  deriving DecidableEq, Repr

/-- **The pipeline around the phase** (`verify_net`'s call site and `witness_decision`,
`smt_verifier.rs`): a `violated` outcome is the result; anything else hands over to the fixpoint
route (`fixpoint`, a function of the total budget left). A phase that ran spent `elapsed` of the
budget; a skipped one spent nothing. -/
def pipeline (phase : Option Witness.Outcome) (elapsed budget : Nat)
    (fixpoint : Nat → Witness.Verdict) : Witness.Verdict :=
  match phase with
  | some (.violated r) => .violated r
  | some _ => fixpoint (budget - elapsed)
  | none => fixpoint budget

/-- **A phase that ran and ended without a run costs exactly its time**: the verdict is the
fixpoint route's at the total budget minus the time the phase spent. -/
@[evidence cites "VER-025" "a phase that ran and ended without a run hands the fixpoint route the total budget minus the time it spent, and changes nothing else"]
theorem pipeline_some_eq {o : Witness.Outcome} {elapsed budget : Nat}
    {fixpoint : Nat → Witness.Verdict} (h : ∀ r, o ≠ .violated r) :
    pipeline (some o) elapsed budget fixpoint = fixpoint (budget - elapsed) := by
  unfold pipeline
  match o, h with
  | .violated r, h => exact absurd rfl (h r)
  | .noRun, _ => rfl
  | .inconclusive _, _ => rfl

/-- **The phase changes no verdict except through the budget it spends**: unless it answered
`violated`, the pipeline's verdict is the fixpoint route's at the budget left. -/
@[evidence cites "VER-025" "a phase that ends without a run changes no verdict except through the budget it spends: the verdict is the fixpoint route at the budget left"]
theorem pipeline_eq_fixpoint {phase : Option Witness.Outcome} {elapsed budget : Nat}
    {fixpoint : Nat → Witness.Verdict} (h : ∀ r, phase ≠ some (.violated r)) :
    ∃ left, left ≤ budget ∧ pipeline phase elapsed budget fixpoint = fixpoint left := by
  match phase, h with
  | none, _ => exact ⟨budget, le_refl _, rfl⟩
  | some o, h =>
    exact ⟨budget - elapsed, Nat.sub_le _ _,
      pipeline_some_eq fun r hr => h r (by rw [hr])⟩

/-- **The phase never reports `Proven`**: a `Proven` of the pipeline is the fixpoint route's,
at the budget left after the phase. -/
@[evidence cites "VER-025" "the phase never reports Proven: a Proven of the pipeline is the fixpoint route at the budget left"]
theorem witnessPhase_never_proven {D : Nat} {enter nameAlignment : Bool} {rows : List Row}
    {injs : List Inj} {a0 : AMarking} {isBad : AMarking → Bool} {ans : Witness.Answer}
    {elapsed budget : Nat} {fixpoint : Nat → Witness.Verdict}
    (h : pipeline (witnessPhase D enter nameAlignment rows injs a0 isBad ans) elapsed budget
      fixpoint = .proven) :
    ∃ left, left ≤ budget ∧ fixpoint left = .proven := by
  revert h
  unfold pipeline
  split
  · intro h; exact absurd h (by simp)
  · intro h; exact ⟨budget - elapsed, Nat.sub_le _ _, h⟩
  · intro h; exact ⟨budget, le_refl _, h⟩

/-- **`D = 0` disables the phase**: it is skipped, and the pipeline is the one without it. -/
@[evidence cites "VER-025" "with the witness depth 0 the phase does not run and the verdict is that of the pipeline without the phase"]
theorem witnessPhase_depth0 (enter nameAlignment : Bool) (rows : List Row) (injs : List Inj)
    (a0 : AMarking) (isBad : AMarking → Bool) (ans : Witness.Answer) (elapsed budget : Nat)
    (fixpoint : Nat → Witness.Verdict) :
    witnessPhase 0 enter nameAlignment rows injs a0 isBad ans = none ∧
      pipeline (witnessPhase 0 enter nameAlignment rows injs a0 isBad ans) elapsed budget
        fixpoint = fixpoint budget := by
  have h : witnessPhase 0 enter nameAlignment rows injs a0 isBad ans = none := by
    simp [witnessPhase]
  exact ⟨h, by rw [h]; rfl⟩

/-- **A `violated` outcome is a replayed witness**: the run is the trim of the run decoded from a
`sat` answer, which replays; it is a run of `StepEnv` from `M0` of at most `D` steps, each a step
index in `[0, T + J)`, that ends at the first violating marking it reaches, and no single step of
it can be dropped. When `M0` violates, it is the empty run. -/
@[evidence cites "VER-025" "a reported run is the trim of a sat model's decoded run, has at most D steps, replays from M0 to a violating marking under the exact step relation, ends at the first violating marking it reaches, is irredundant, and is empty when M0 violates"]
theorem witnessPhase_violated_sound {D : Nat} {enter nameAlignment : Bool} {rows : List Row}
    {injs : List Inj} {a0 : AMarking} {isBad : AMarking → Bool} {ans : Witness.Answer}
    {r : List Nat}
    (h : witnessPhase D enter nameAlignment rows injs a0 isBad ans = some (.violated r)) :
    (∃ s run, ans = .sat s ∧ decodeModel (rows.length + injs.length) s D = some run ∧
      replays rows injs isBad a0 run = true ∧ r = trim (replays rows injs isBad a0) run ∧
      r.Sublist run) ∧
      r.length ≤ D ∧
      (∃ a, replayEnv rows injs a0 r = some a ∧ isBad a = true ∧ ReachEnv rows injs a0 a) ∧
      (∀ t ∈ r, t < rows.length + injs.length) ∧
      (∀ j, j < r.length → replays rows injs isBad a0 (r.take j) = false) ∧
      (∀ k, k < r.length → replays rows injs isBad a0 (r.eraseIdx k) = false) ∧
      (replays rows injs isBad a0 [] = true → r = []) := by
  unfold witnessPhase at h
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  cases ans with
  | sat s =>
    simp only at h
    split at h
    · exact absurd h (by simp)
    rename_i run hdec
    split at h
    · rename_i hrep
      have hr := (Option.some.inj h)
      cases hr
      have hsub := trim_sublist (replays rows injs isBad a0) run
      obtain ⟨a, hrep', hbad, hreach, hlt⟩ := replayRun_sound (trim_sound _ hrep)
      exact ⟨⟨s, run, rfl, hdec, hrep, rfl, hsub⟩,
        le_trans hsub.length_le (decodeModel_length_le hdec), ⟨a, hrep', hbad, hreach⟩, hlt,
        trim_first _ hrep, trim_irredundant _ _, trim_initial _ hrep⟩
    · exact absurd h (by simp)
  | unsat => exact absurd h (by simp)
  | unknown => exact absurd h (by simp)
  | failure => exact absurd h (by simp)
  | budgetSpent => exact absurd h (by simp)

/-- **`noRun` is exact up to the solver**: the phase answers `noRun` only on `unsat`, and when
that `unsat` is truthful (P4), no run of at most `D` steps (firings and injections) reaches a
violating marking. It says nothing about longer runs, so it is not a proof. -/
@[evidence cites "VER-025" "'no run' comes only from unsat, and with a truthful unsat (P4) no run of at most D steps, firings and injections, reaches a violation; nothing about longer runs, so not a proof"]
theorem witnessPhase_noRun_exact {D : Nat} {enter nameAlignment : Bool} {rows : List Row}
    {injs : List Inj} {n : Nat} {a0 : AMarking} {isBad : AMarking → Bool}
    {badI : (PlaceId → Int) → Prop} {ans : Witness.Answer}
    (hWF : WellFormedRows n rows) (hIn : InjsIn n injs) (hD : InjsDistinct injs)
    (hBad : BadAgrees badI (fun a => isBad a = true)) (hcap0 : capsOk injs a0 = true)
    (hTruth : ans = .unsat → ¬ BmcSatEnv rows injs n a0 badI D)
    (h : witnessPhase D enter nameAlignment rows injs a0 isBad ans = some .noRun) :
    ans = .unsat ∧
      ¬ ∃ ts a, ts.length ≤ D ∧ replayEnv rows injs a0 ts = some a ∧ isBad a = true := by
  have hu : ans = .unsat := by
    unfold witnessPhase at h
    split at h
    · exact absurd h (by simp)
    split at h
    · exact absurd h (by simp)
    cases ans with
    | sat s =>
      simp only at h
      split at h
      · exact absurd h (by simp)
      split at h <;> exact absurd h (by simp)
    | unsat => rfl
    | unknown => exact absurd h (by simp)
    | failure => exact absurd h (by simp)
    | budgetSpent => exact absurd h (by simp)
  refine ⟨hu, fun hrun => hTruth hu ?_⟩
  exact (bmcEnv_complete D hWF hIn hD hBad hcap0).mpr hrun

/-- **A truthful `sat` is never turned away**: when the answer defines the selectors of a model of
the depth-`D` script, the phase (entered, not a name-alignment property) answers `violated`. A
`sat` whose model defines no selector is not a model of the script in this sense; the phase
reads no run from it and is inconclusive. -/
@[evidence cites "VER-025" "a sat answer that defines the selectors of a model of the depth-D script always ends in a reported run"]
theorem witnessPhase_sat_violated {D : Nat} {rows : List Row} {injs : List Inj} {n : Nat}
    {a0 : AMarking} {isBad : AMarking → Bool} {badI : (PlaceId → Int) → Prop} {s : Nat → Int}
    {M : Nat → PlaceId → Int} (hD0 : D ≠ 0)
    (hWF : WellFormedRows n rows) (hIn : InjsIn n injs)
    (hBad : BadAgrees badI (fun a => isBad a = true))
    (hm : BmcModelEnv rows injs n a0 badI D s M) :
    ∃ r, witnessPhase D true false rows injs a0 isBad (.sat (Witness.defined s)) =
      some (.violated r) := by
  obtain ⟨a, hrep, hbad⟩ := bmcEnv_sat_replays hWF hIn hBad hm
  have hok : replays rows injs isBad a0 (decodeRust (rows.length + injs.length) s D) = true :=
    replays_iff.mpr ⟨a, hrep, hbad⟩
  refine ⟨trim (replays rows injs isBad a0) (decodeRust (rows.length + injs.length) s D), ?_⟩
  simp [witnessPhase, hD0, hok, decodeModel_defined]

/-! ## The relation is the CHC rules' open system -/

/-- The bound `env_injection` gives each environment place: `None` for `AlwaysAvailable`,
`Some(k)` for `Bounded(k)`. -/
def modeBound : InjMode → Option Nat
  | .always => none
  | .bounded k => some k

/-- The injection list of the verifier: every environment place, with the mode's bound. -/
def injsOf (envs : List PlaceId) (mode : InjMode) : List Inj :=
  envs.map fun e => (e, modeBound mode)

theorem injAt_eq_injA (a : AMarking) (p : PlaceId) : injAt a p = injA a p := rfl

/-- **`StepEnv` is `StepAE`** at the verifier's injection list: the witness phase searches the
open system the CHC rules of `encode_net` describe (transition rules with the post-cap,
injection rules with the `Bounded(k)` guard), without their strengthening conjuncts. -/
@[evidence cites "VER-025" "the phase's step relation at the verifier's injection list is EnvSemantics.StepAE, the transition and injection rules of the HORN encoding without their strengthening conjuncts"]
theorem stepEnv_injsOf (rows : List Row) (envs : List PlaceId) (mode : InjMode) :
    StepEnv rows (injsOf envs mode) = StepAE rows envs mode := by
  funext a a'
  apply propext
  have hcap : ∀ b, capsOk (injsOf envs mode) b = mode.capped envs b := by
    intro b
    unfold capsOk injsOf
    rw [List.all_map]
    cases mode with
    | always => simp [InjMode.capped, capOk, modeBound]
    | bounded k => simp [InjMode.capped, capOk, modeBound, Function.comp_def]
  have hadm : ∀ e b, injOk (e, modeBound mode) b = mode.admits (b e) := by
    intro e b
    cases mode <;> rfl
  unfold StepEnv StepAE
  rw [hcap]
  constructor
  · rintro (h | ⟨jj, hmem, hok, rfl⟩)
    · exact Or.inl h
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmem
      exact Or.inr ⟨e, he, by rw [← hadm]; exact hok, rfl⟩
  · rintro (h | ⟨e, he, hok, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨(e, modeBound mode), List.mem_map.mpr ⟨e, he, rfl⟩,
        by rw [hadm]; exact hok, rfl⟩

theorem reachEnv_injsOf (rows : List Row) (envs : List PlaceId) (mode : InjMode)
    (a0 : AMarking) : ReachEnv rows (injsOf envs mode) a0 = ReachAE rows envs mode a0 := by
  unfold ReachEnv ReachAE
  rw [stepEnv_injsOf]

/-! ## A replayed witness is a derivation of the strengthened CHC system -/

/-- **One rule of the shipped CHC system with every conjunct** (`encode_net` with the state
equation, [VER-016]; under `Bounded(k)`, [VER-006]): a transition rule fires flat transition `k`
(`firing_conditions`), bumps its counter, and its successor satisfies every law of `ys`
(`invariant_conditions`), the state-equation row of every non-injected place below `w`
(`state_equation_conditions`) and the post-cap (`env_bound_conditions`); an injection rule
is allowed by the guard, adds one token and copies the counters (`encode_injection_rule`). Without
the state equation the rows and counters are dropped, which only removes conjuncts. -/
def StepHorn (net : FlatNet) (envs : List PlaceId) (mode : InjMode) (ys : List Weight) (w : Nat)
    (a0 : AMarking) (s s' : AMarking × Counters) : Prop :=
  (∃ k ft, net[k]? = some ft ∧ enabledA s.1 ft.1 = true ∧
      mode.capped envs (fireA s.1 ft.1 ft.2) = true ∧
      (∀ y ∈ ys, dot y (fireA s.1 ft.1 ft.2) w = dot y a0 w) ∧
      (∀ p, p < w → p ∉ envs → Libpetri.Row net a0 (fireA s.1 ft.1 ft.2) (bump s.2 k) p) ∧
      s' = (fireA s.1 ft.1 ft.2, bump s.2 k))
  ∨ ∃ p ∈ envs, mode.admits (s.1 p) = true ∧ s' = (injA s.1 p, s.2)

/-- `Reachable` of the strengthened CHC system, from `(M0, 0)`. -/
def ReachHorn (net : FlatNet) (envs : List PlaceId) (mode : InjMode) (ys : List Weight) (w : Nat)
    (a0 : AMarking) (a : AMarking) (n : Counters) : Prop :=
  Relation.ReflTransGen (StepHorn net envs mode ys w a0) (a0, fun _ => 0) (a, n)

/-- **Every marking of the unstrengthened open system is reachable in the strengthened one**, on
duplicate-free rows ([IO-011]) and with every law gate-validated (H1, H2, H3′): conjoining the
P-invariants and the state-equation rows to the bounded rules removes no marking. -/
theorem reachAE_horn {net : FlatNet} {envs : List PlaceId} {mode : InjMode} {ys : List Weight}
    {w : Nat} {a0 a : AMarking} (hnd : ∀ ft ∈ net, ft.2.Nodup)
    (hv : ∀ y ∈ ys, ValidLawInj net envs w y) (h : ReachAE net envs mode a0 a) :
    ∃ n, ReachHorn net envs mode ys w a0 a n := by
  suffices ∃ n, ReachCnt net envs a0 a n ∧ ReachHorn net envs mode ys w a0 a n by
    obtain ⟨n, -, hh⟩ := this; exact ⟨n, hh⟩
  induction h with
  | refl => exact ⟨_, ReachCnt.init, Relation.ReflTransGen.refl⟩
  | @tail b c _ hs ih =>
    obtain ⟨n, hc, hh⟩ := ih
    rcases hs with ⟨⟨ft, hmem, hen, rfl⟩, hcap⟩ | ⟨p, hp, hadm, rfl⟩
    · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hmem
      have hfa := fireAD_eq_fireA (hnd ft hmem) b ft.1
      rw [hfa] at hcap ⊢
      have hc' := ReachCnt.step hc hk hen
      refine ⟨_, hc', Relation.ReflTransGen.tail hh (Or.inl ⟨k, ft, hk, hen, hcap, ?_, ?_, rfl⟩)⟩
      · intro y hy
        exact invariant_strengthening_sound_inj (hv y hy).h1 (hv y hy).h2 (hv y hy).h3
          (counters_erase hc')
      · exact fun p _ hp => rows_hold hc' p hp
    · exact ⟨_, ReachCnt.inject hc hp,
        Relation.ReflTransGen.tail hh (Or.inr ⟨p, hp, hadm, rfl⟩)⟩

/-- **A replayed witness is a derivation of the strengthened CHC system**: every marking the
replay reaches, the violating last one included, is `Reachable` in the rule system the fixpoint
query solves, P-invariants, state-equation rows, counters, post-caps and the `Bounded(k)` guard
included. So the phase's `Violated` never contradicts a derivation of that system. -/
@[evidence cites "VER-025" "the phase adds Violated verdicts and never removes one: every marking a replayed witness reaches is reachable in the strengthened CHC system the fixpoint query solves (P-invariants, state-equation rows, post-caps, Bounded(k) guard), on duplicate-free rows with gate-validated laws"]
theorem witness_horn_derivation {net : FlatNet} {envs : List PlaceId} {mode : InjMode}
    {ys : List Weight} {w : Nat} {a0 a : AMarking} {ts : List Nat}
    (hnd : ∀ ft ∈ net, ft.2.Nodup) (hv : ∀ y ∈ ys, ValidLawInj net envs w y)
    (h : replayEnv net (injsOf envs mode) a0 ts = some a) :
    ∃ n, ReachHorn net envs mode ys w a0 a n := by
  have hr := replayEnv_sound h
  rw [reachEnv_injsOf] at hr
  exact reachAE_horn hnd hv hr

end Libpetri.Novel.FiringBound
