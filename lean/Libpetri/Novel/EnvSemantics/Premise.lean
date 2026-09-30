import Libpetri.Novel.EnvSemantics.Supplied

/-!
# The `Bounded(k)` premises, checked ([VER-006] AC3)

`Step.lean`, `Quiescence.lean` and `Supplied.lean` prove the `Bounded(k)` results under two
premises: no row deposits into an environment place (`NoEnvDeposit`) and the initial marking
holds at most `k` on each (`EnvCappedC`). Each witness there breaks one of them and gets a wrong
verdict. The verifier now checks both before any route runs:
`environment.rs::bounded_premise_violation`, called by `smt_verifier.rs::verify_net` under
`Bounded(k)` with registered environment places, returns the first environment place (in
code-point order) that the initial marking holds above `k`, then the first one some transition's
output spec names (`output_places`, timeout and forward outputs included), and `verify_net`
answers `Unknown` on route `Unavailable` with that reason. On the [VER-004] split net the
depositor is a completion step `complete:t`; the reason names `t`
(`in_flight::source_transition`), which changes only the message.

* `boundedPremiseOK` is the check (`none` from the Rust is `true`); `boundedPremiseOK_iff`: it
  holds exactly when both premises do. The flat rows carry every outcome of every transition, so
  a place some output spec names is a place some row deposits into.
* `bounded_checked_sound`, `bounded_checked_supplied_sound`,
  `bounded_checked_quiescence_sound`: once the check passes, Proposition 1 with injection, the
  supplied successor and the relaxed quiescence transfer hold with no premise left about the
  environment beyond the ones `route_b_env_observation` checks.
* The five witnesses fail the check (`*_refused`), so `verify_net` no longer reaches any of
  them (`witnesses_guardFree`: each also meets the structural side premise, so it breaks exactly
  the premise it names): `bounded_initial_overflow_wrong_proven`, `bounded_producer_overflow_wrong_proven`,
  `supplied_bounded_deposit_wrong_proven`, `supplied_bounded_initial_wrong_proven` and
  `quiescence_bounded_initial_spurious` stay true of the encodings, and are retrodictions of
  the verifier.

The check is sufficient, not exact: it refuses every deposit into an environment place, even
one that could never push it above `k`, and answers `Unknown` there (spec [VER-006] AC3).
-/

namespace Libpetri.Novel.EnvSemantics

open Libpetri Libpetri.Novel.ForwardDeposit Libpetri.Novel.Seam

/-- `bounded_premise_violation(net, m0, envs, Bounded(k)) == None`. -/
def boundedPremiseOK (k : Nat) (envs : List PlaceId) (rows : Rows) (m0 : CMarking) : Bool :=
  envs.all (fun e => decide ((m0 e).length ≤ k)) &&
    envs.all (fun e => rows.all fun tr => tr.2.count e == 0)

/-- **The check is the two premises.** -/
theorem boundedPremiseOK_iff {k : Nat} {envs : List PlaceId} {rows : Rows} {m0 : CMarking} :
    boundedPremiseOK k envs rows m0 = true ↔ EnvCappedC k envs m0 ∧ NoEnvDeposit rows envs := by
  unfold boundedPremiseOK EnvCappedC NoEnvDeposit
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, fun tr htr e he => h2 e he tr htr⟩,
    fun ⟨h1, h2⟩ => ⟨h1, fun e he tr htr => h2 tr htr e he⟩⟩

theorem boundedPremiseOK_capped {k : Nat} {envs : List PlaceId} {rows : Rows} {m0 : CMarking}
    (h : boundedPremiseOK k envs rows m0 = true) :
    (InjMode.bounded k).capped envs (alpha m0) = true :=
  capped_bounded_iff.mpr fun e he => (boundedPremiseOK_iff.mp h).1 e he

/-- **Proposition 1 with injection, `Bounded(k)`, behind the check.** -/
theorem bounded_checked_sound {rows : Rows} {envs : List PlaceId} {k : Nat}
    (hG : ∀ tr ∈ rows, GuardFreeConsumeAll tr.1) {m0 m : CMarking}
    (hok : boundedPremiseOK k envs rows m0 = true) (h : ReachCE rows envs (.bounded k) m0 m) :
    ReachAE rows envs (.bounded k) (alpha m0) (alpha m) ∧ EnvCappedC k envs m :=
  proposition_one_inj_bounded hG (boundedPremiseOK_iff.mp hok).2 (boundedPremiseOK_iff.mp hok).1 h

/-- **The supplied successor covers the executor behind the check.** The remaining premise,
no inhibitor on an environment place, is the one `route_b_env_observation` checks. -/
theorem bounded_checked_supplied_sound {rows : Rows} {envs : List PlaceId} {k : Nat}
    (hG : ∀ tr ∈ rows, GuardFreeConsumeAll tr.1) (hInh : NoEnvInhibitor rows envs)
    {m0 m : CMarking} (hok : boundedPremiseOK k envs rows m0 = true)
    (h : ReachCE rows envs (.bounded k) m0 m) :
    ∃ b, ReachSup rows envs (.bounded k) (alpha m0) b ∧ OffEnvEq envs (alpha m) b :=
  supplied_executor_sound hG hInh (Or.inr (boundedPremiseOK_iff.mp hok).2)
    (boundedPremiseOK_capped hok) h

/-- **Relaxed quiescence catches every untimed executor deadlock behind the check.** -/
theorem bounded_checked_quiescence_sound {np N : Nat} {rows : Rows} {envs : List PlaceId}
    {k : Nat} (hG : ∀ tr ∈ rows, GuardFreeConsumeAll tr.1) (hok' : ∀ ft ∈ rows, FlatOK np ft.1)
    (hN : DemandBelow N rows) (hN1 : 1 ≤ N) {m0 m : CMarking}
    (hok : boundedPremiseOK k envs rows m0 = true) {P : AMarking → Prop} (hP : InjStable envs P)
    (hm : ReachCE rows envs (.bounded k) m0 m) (hstuck : OpenStuck rows envs (.bounded k) (alpha m))
    (hPm : P (alpha m)) :
    ∃ b, ReachAE rows envs (.bounded k) (alpha m0) b ∧
      quiescentE np rows envs (.bounded k) b = true ∧ P b ∧ OffEnvEq envs (alpha m) b :=
  relaxed_quiescence_sound_executor hG (Or.inr (boundedPremiseOK_iff.mp hok).2) hok' hN hN1
    (boundedPremiseOK_capped hok) hP hm hstuck hPm

/-! ## The witnesses are refused -/

theorem bounded_initial_overflow_refused : boundedPremiseOK 1 [2] rowsAB m0Over = false := by
  decide

theorem bounded_producer_overflow_refused : boundedPremiseOK 1 [1] rowsAE m0Prod = false := by
  decide

theorem supplied_bounded_deposit_refused : boundedPremiseOK 1 [1] rowsGate m0Gate = false := by
  decide

theorem supplied_bounded_initial_refused :
    boundedPremiseOK 1 [1] rowsGateNoDep m0GateOver = false := by
  decide

theorem quiescence_bounded_initial_refused : boundedPremiseOK 1 [0] rowsQ m0Q = false := by
  decide

/-- **The witnesses meet the structural side premise too**: every row is guard-free on its
consume-all arcs (`GuardFreeConsumeAll`, which `proposition_one_inj_bounded` and
`supplied_executor_sound` also take), so each witness breaks exactly the premise it names. -/
theorem witnesses_guardFree :
    (∀ tr ∈ rowsAB, GuardFreeConsumeAll tr.1) ∧ (∀ tr ∈ rowsAE, GuardFreeConsumeAll tr.1) ∧
      (∀ tr ∈ rowsGate, GuardFreeConsumeAll tr.1) ∧
      (∀ tr ∈ rowsGateNoDep, GuardFreeConsumeAll tr.1) ∧
      (∀ tr ∈ rowsQ, GuardFreeConsumeAll tr.1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro tr htr s hs hc <;>
    simp [rowsAB, rowsAE, rowsGate, rowsGateNoDep, rowsQ, tAB, tAE, tToEnv, tTwoEnv, tQ1, tQ2]
      at htr <;> rcases htr with rfl | rfl <;> simp_all [Card.consumesAll]

end Libpetri.Novel.EnvSemantics
