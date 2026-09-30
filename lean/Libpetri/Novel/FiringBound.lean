import Libpetri.Novel.FiringBound.Ranking
import Libpetri.Novel.FiringBound.Bmc
import Libpetri.Novel.FiringBound.Phase
import Libpetri.Novel.FiringBound.Reaping

/-!
# The firing bound and the bounded model check ([VER-019])

Root of `Novel/FiringBound/`: `Ranking.lean` (`can_fire`, the ranking, replayed runs),
`Bmc.lean` (the bounded-run constraint system and its exactness), `Phase.lean` (the depth loop,
the verdicts, agreement with [VER-017]) and `Reaping.lean` (timed runs and the R16 witness).

Model of the firing-bound phase, `rust/libpetri-verification/src/bounded_run.rs`, over the
deposit rows of `ForwardDeposit.lean` (`StepAD`, `ReachAD`, `fireAD`): one row per flat
transition `flatten` writes, its deposit the row's `post` vector.

The Rust:
* `can_fire(ft)`: no inhibited place is one the transition needs — `pre[p] ≤ 0` and `p` not
  read, for every inhibitor `p`. `canFire`.
* `check_ranking_exact`: weights `r ≥ 0` with `r·(post − pre) ≤ −1` on every row `can_fire`
  keeps, in checked `i128` (an overflow fails the check), and the bound `K = r·M0`.
  `checkRankingExact`, over unbounded `Int`, so it accepts every weighting the checked
  arithmetic accepts, with the same `K`.
* `encode_bounded_run(depth = d)`: a selector `s_i ∈ [0, T]` per step (`T` idles), an idle step
  followed only by idle steps, the exact guard of the selected row
  (`guard_conditions`: `m ≥ pre[p]` where `pre[p] > 0`, `m = 0` on inhibitors, `m ≥ 1` on reads),
  each place's successor an `ite` chain over the rows that touch it (`clears` or a nonzero
  column), newest-first, and the violation at the last marking. `BmcModel` is that constraint
  system, read over integer assignments as the solver reads it; the variables `m{i}_{p}` exist
  for `p < n` only, and `mAt` reads a place past the net at its initial count.
* `decode_bounded_run`: the selectors read in order up to the first one outside `[0, T)`
  (`map_while`). `decodeRust`, proved equal to the recursive `decode`.
* `replay_run`: every firing enabled (`enabled_a`), then `fire_a`, and the property checked at
  the last marking. `replay`.
* `run_firing_bound_phase`: the ranking, then depths `min(k, 8)`, doubling, capped by `k` and
  `max_depth`; `unsat` at a depth `≥ k` is `Proven`, `sat` is replayed. `depthLoop`.

Results:
* `canFire_filter_sound`: a row `can_fire` filters out is enabled at no marking at all, so at no
  reachable one; `reachAD_filter_canFire`: dropping those rows changes no reachable set. This is
  why the ranking constraint may skip them while the bounded run encodes every row.
* `ranking_bounds_runs`: a ranking the exact check accepts (`IsRanking`) bounds every replayable
  run: `|run| + r·M ≤ r·M0`, so no run has more than `K = r·M0` firings. `ranking_bounds_steps`
  is the same over counted steps, and `ranking_bounds_concrete` carries it to the executor's
  concrete steps through Proposition 1 over rows (`stepCR_simulated`): the bound is a claim
  about every concrete run, not only abstract ones.
* `bmc_complete`: for every depth `d`, the constraint system has a model **iff** some run of at
  most `d` firings reaches a violating marking; the model's decoded selectors replay to that
  marking (`bmc_model_replays`, `bmc_sat_replays` through `decodeRust`), which is why a `sat`
  survives `replay_run`. The idle-only-at-the-end constraint is not needed for soundness (an idle
  step mid-run only shortens the run); it is what makes the `map_while` decode read the whole
  run, so it is load-bearing for the `Violated` path, not the `Proven` one. With the ranking,
  `bmc_exact_at_bound`: at `d ≥ K` a model exists iff some reachable marking violates.
* `phase_proven_sound` / `phase_violated_sound`: the depth loop answers `Proven` only after
  `unsat` at a depth `≥ k`, and then no `ReachAD`-reachable marking violates; a replayed
  `Violated` run is really reachable. `phase_proven_concrete`: the `Proven` holds of every
  concrete **untimed** run of the fixed rows, timeout outcomes included.
  `phase_postfix_deadlock_sound` carries a `DeadlockFree` `Proven` through the name → index seam
  (`Seam.postfix_deadlock_sound`, seed `encodeM0` = the phase's `initial` vector) to every
  marking the **untimed** executor reaches on the caller's net. Neither covers the timed
  executor's rest state under deadline reaping by itself; R16 below says how the shipped phase
  does.
* `bmc_agrees_with_enumeration`: on a net where both answer, the bounded model check at the
  firing bound and the closed enumeration ([VER-017]) give the same verdict.

Deadline reaping ([TIME-013], R16), **atomic (sync) executors only**:
* `ranking_bounds_timed`: every timed execution whose marking moves only by atomic abstract
  firings (`MarkingFaithfulRows` — reaping and clock moves change no token, and each firing
  consumes and deposits in one move) changes its marking at most `K` times, and with a ranking
  every firing changes it; the bound transfers. `run_async` with an action in flight holds a
  consumed-but-not-deposited marking, which the premise excludes; nothing here covers it.
* `bmc_proven_marking_timed` / `phase_proven_timed_marking`: a `Proven` for a predicate of the
  marking holds at every state of such an execution.
* The premise is discharged for `ReapingVsUntimed`'s executor model of the witness net, both
  enforcement paths, any timing and schedule: `markingFaithfulRows_of_markingFaithful` (the
  bridge from `MarkingFaithful` over duplicate-free branches), `execStep_faithfulRows`, and the
  instances `ranking_bounds_timed_netR` (at most one marking change) and
  `phase_proven_timed_marking_netR`. It is not discharged for a multi-transition executor model,
  since none exists yet.
* `firing_bound_proves_reaped_net` (witness, **a retrodiction of the pre-fix phase**): on
  `ReapingVsUntimed`'s `window(3, 5)` net the phase finds the ranking `p₀`, `K = 1`, and its
  bounded model check at depth 1 under the strict quiescence has no model, so the phase as it
  stood before the reaping fix answered `Proven` for `DeadlockFree`, while both executors' timed
  runs halt at `{p₀}` with the token stranded. Checked against the Rust on 2026-09-28, before
  the fix: `SmtVerifier` with `state_equation_phase(false)` on that net reported
  `Bound: 1 firings (p0 drops on every firing)`, `Depths: 1 none`,
  `PROVEN (bounded model check)`; with the state-equation phase on, [VER-018] answered the same
  `Proven` first.
* **How the shipped phase closes R16: reap-quiescence.** The phase runs over the flat net that
  `SmtVerifier::flatten` builds with `reapable_set()` (`flatten_with_reapable`), so every
  `Deadline` / `Window` row carries `ft.reapable` unless the caller sets `assume_no_reaping`.
  Its bounded-run script (`bounded_run::encode_bounded_run`) states the violation with
  `smt_encoder::encode_property_violation`, whose quiescence clause comes from the reap-aware
  `encode_quiescent` (a reapable row adds no clause), and its replay reads
  `abstract_replay::violation_predicate`, whose `quiescent` skips `ft.reapable` too. That is
  `ReapAware.lean`'s reading: `rest_sound` puts every timed rest at an untimed-reachable,
  reap-quiescent marking, and `reap_aware_ac3` turns a `Proven` over the untimed reachable set
  into a claim about every timed rest. On the witness the reap-aware `DeadlockFree` violation
  holds at `{p₀}` itself (`ReapAware.witness_caught`), so the phase now answers `Violated` with
  an empty trace (the Rust integration test `the_firing_bound_reads_the_reaped_rest`; with
  `assume_no_reaping` it answers `Proven`, the on-time reading of `noReap_timedDeadlockFree`).
  `bmc_complete` and `phase_proven_sound` hold for any violation `bad` that agrees with the
  script (P5). For the shipped script that `bad` is the reap-aware one
  (`ReapAware.quiescentBad_filter_iff`, `ReapAware.deadlockBad_filter_eq`: the encoded clause
  over the rows without the reapable ones is reap-quiescence), so a `Proven` says no
  untimed-reachable marking is reap-quiescent and violating, and `reap_aware_ac3` carries that
  to every timed rest. The ranking and the depth loop do not change.
  `phase_postfix_deadlock_sound` is still stated for the strict `DeadlockFree` clause, which is
  the script only under `assume_no_reaping` or on a net with nothing to reap.
* `noReap_timedDeadlockFree`: on the executor model, an enforcement that never reaps halts only
  at an untimed-quiescent marking, so an untimed `DeadlockFree` `Proven` is the timed one; the
  stranding is the reap's (`reaping_not_timedDeadlockFree`).
* `gateReaping` (**an alternative that was not taken**): step aside on a quiescence `Proven`
  when the net has a `Deadline` / `Window` transition. It closes the witness
  (`gated_witness_steps_aside`) and, under P8, its `Proven` is sound for the timed executor
  model (`gated_dlf_timed_sound_netR`). The shipped fix reads reap-quiescence instead, which
  keeps a `Proven` where the gate would give up and answers `Violated` on the witness where the
  gate would stop. `gateReaping` models no Rust code.

Premises about the Rust, stated where used:
* **P1 distinct input places** (`InputsDistinctPlaces`, rejected at transition build,
  [CORE-030] AC3): `pre t p` is the flattener's summed `base_pre[p]`, and `consumeAllAt` its
  `consume_all` list.
* **P2 dense index** (`RowIn`): every place a row reads or writes is below `place_count`
  (`place_index` is the dense index of `flatten`).
* **P3 exact arithmetic**: `check_ranking_exact` returns `Some` only when its checked `i128`
  arithmetic did not overflow, where it equals `Int` arithmetic.
* **P4 the SMT-LIB text denotes `BmcModel`** (the string rendering of `encode_bounded_run` is not
  modelled) and z3's `unsat` is correct for `QF_LIA`.
* **P5 the violation**: `encode_property_violation` over the last marking (integers) agrees with
  `violation_predicate` over naturals (`BadAgrees`) — the seam's per-arm `_iff` (R3), assumed.
* **P6 no environment injection**: the call site gates on the declared injection list, so
  `env_inject = []` and the post-caps are empty; injections are not modelled here.
* **P7 `enabled_a` / `fire_a` are `enabledA` / `fireAD`** on the flat vectors: `enabled_a` is
  the same guard as `guard_conditions` (`guardI_iff_enabledA` under P1, P2), `fire_a` the same
  arms as `fireAD`.
* **P8 no reapable transition, no reap** (`gated_dlf_timed_sound_netR` only): on a net with no
  `Deadline` / `Window` transition, `enforce_deadlines` changes no cell (its loop skips every
  other timing, and `Exact` is enforced softly, [TIME-006]).

Not modelled: `encode_ranking_query` and `decode_ranking` (whatever the solver returns, only the
exact re-check is trusted), the `Unbounded` path (`encode_repeatable_vector_query`, which makes no
claim), the budget and the `LARGEST_BOUND` cap (both only step aside), and the report text.
-/

