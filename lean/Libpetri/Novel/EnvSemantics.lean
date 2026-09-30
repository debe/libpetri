import Libpetri.Novel.EnvSemantics.Step
import Libpetri.Novel.EnvSemantics.Quiescence
import Libpetri.Novel.EnvSemantics.Supplied
import Libpetri.Novel.EnvSemantics.Arrivals
import Libpetri.Novel.EnvSemantics.Premise

/-!
# Environment semantics across routes ([VER-006], [VER-022]; gap R5)

Root of the `Novel/EnvSemantics/` modules. The gap analysis
(`research/net-metrics/review/lean-gaps/ANALYSIS.md`, row 6 and R5) found the environment covered
on the abstract side only (`Retrodict.lean`, `AlwaysAvailable`), with no concrete simulation, no
`Bounded(k)` guard, no meaning for the relaxed quiescence check and nothing for `Arrivals`.

* `Step.lean` — the encoded open system (`StepAE`: injection rule, `Bounded(k)` guard and the
  transition rules' post-cap) and the executor with an environment (`StepCE`, `StepCDE`).
  `proposition_one_inj` (concrete ⊆ abstract, `AlwaysAvailable`), `proposition_one_inj_bounded`
  (under `NoEnvDeposit` and a capped `M0`), `bounded_demand_gate` ([VER-006] AC3), the two
  premises' necessity against the shipped post-cap (`bounded_initial_overflow_wrong_proven`,
  `bounded_producer_overflow_wrong_proven`), and `retrodict_98b9297`.
* `Quiescence.lean` — `encode_quiescent` with injection (`quiescentE`) means **stuck under every
  injection future** in the encoded open system: `relaxed_quiescence_sound`,
  `relaxed_violation_real`, `relaxed_quiescence_exact`, `relaxed_quiescence_sound_executor`
  (untimed executor deadlocks are caught), `quiescence_vacuity_sound` (the AC6 note), and the
  relaxation of `98b9297` (`retrodict_98b9297_relaxation`).
* `Supplied.lean` — the state-class graphs' and Route B's supplied-environment successor agrees
  with the injected encoding off the environment places and in quiescence under four premises:
  no inhibitor on an environment place and an environment-blind property (checked by
  `route_b_env_observation`), a capped seed and, for `Bounded(k)`, `NoEnvDeposit` (both checked
  by `verify_net`, `Premise.lean`)
  (`supplied_safety_exact`, `supplied_quiescence_exact`, `supplied_enumeration_sound` against
  the executor, `sup_enumeration_exact` for the worklist). The unchecked two are needed on
  every route, each shown by a witness that breaks it alone:
  `supplied_bounded_deposit_wrong_proven` (`NoEnvDeposit`), `supplied_bounded_initial_wrong_proven`
  (the capped seed; both a wrong `Proven`) and `quiescence_bounded_initial_spurious` (the capped
  seed; a spurious deadlock). All three were live until the check below.
  Retrodictions of `89aaeec` (`routeB_env_count_frozen`, `routeB_env_inhibitor_unsound`,
  `scg_env_read_prefix_unsound`).
* `Premise.lean`: `environment.rs::bounded_premise_violation`, which `verify_net` runs before
  any route under `Bounded(k)`, is exactly the two premises (`boundedPremiseOK_iff`); behind it
  the three transfers hold (`bounded_checked_sound`, `bounded_checked_supplied_sound`,
  `bounded_checked_quiescence_sound`), and every `Bounded(k)` witness above is refused
  (`*_refused`).
* `Arrivals.lean` — the `Arrivals(min, max)` closure is exact for safety and quiescence
  (`arrivals_closure_reach`, `arrivals_closure_quiescent`), and a closed enumeration's `Proven`
  holds for the executor under the environment (`arrivals_enumeration_sound`).

Scope: untimed throughout, and every row read as not reapable. Deadline reaping ([TIME-013]) can
bring the executor to rest at a marking the untimed relation still enables
(`ReapingVsUntimed.lean`); the shipped `encode_quiescent` skips reapable rows for that reason,
and `ReapAware.lean` proves that reading sound. The quiescence results here are the reapable-free
case and say nothing about such a rest. Name → index resolution (`resolve_env_injection`) is out of
scope too.
-/
