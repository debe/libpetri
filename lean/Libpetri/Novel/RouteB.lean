import Libpetri.Novel.RouteB.Name
import Libpetri.Novel.RouteB.Graph
import Libpetri.Novel.RouteB.Exec
import Libpetri.Novel.RouteB.Sim
import Libpetri.Novel.RouteB.Decide
import Libpetri.Novel.RouteB.Sound
import Libpetri.Novel.RouteB.Classify
import Libpetri.Novel.RouteB.Retrodict
import Libpetri.Novel.RouteB.Aligned

/-!
# Route B: the ν name-partition state-class graph ([NU-050], [NU-051], [NU-052], [NU-054], [VER-012])

Gap R2 of `research/net-metrics/review/lean-gaps/ANALYSIS.md`. Root of the `Novel/RouteB/`
modules, which model `rust/libpetri-verification/src/name_state_class_graph.rs`
(`build_until`, `name_successors`, `distinct_signatures`, `enabling_symbols`,
`priority_dominated`, `will_fire`, `shares_consumed_input`, `consumed_demand`), `name_marking.rs`
(`add`, `remove`, `count_of`, `symbols_in`), `name_fragment.rs` (`classify`, `declared_mints`),
`branch_outcomes.rs` (`Outcome`, `Deposit`, including `Deposit::Drained`), `nu_scg_verifier.rs`
(`verify_via_name_scg`, `verify_via_name_scg_reaping`, `decide`, `NameClasses::new` and
`NameClasses::is_quiescent` with its `fires_unreapable` branch), `reaping.rs` (`relax_late`, in
`TimedScg/Late.lean`), `graph_decision.rs`
(`decide_over_classes`), the runtime's `select_match_name` / `find_match_binding` (`Selectable`),
`smt_verifier.rs::route_b_env_observation`, and the one `if` of `verify_net` that downgrades a
Route B `Proven` under [VER-006] `Ignore` (`routeBFinal`; `verify_net` itself is not modelled).

| module | content | headline |
|---|---|---|
| `Name` | name layer, role steps, orbit dedup | `dedup_perm`, `mint_key` |
| `Graph` | branch outcomes (`Row`), one expansion, the prune, the explorer | **`routeB_equivariant`** (discharges `Interning.Equivariant`), `routeB_interned_keys_eq` |
| `Exec` | untimed base, executor name effect, `InFragment`, contracts, projection premise | `exec_names_step`, `keyIndex_eq_nameLayer` |
| `Sim` | untimed, env-free executor ν step | **`name_step_simulates_exec`**, `exec_reach_simulated`, `exec_quiescent_succ_nil`, `nu_reach_reachAN` |
| `Decide` | build loop (FIFO, early stop, truncation, stop), verdict, reap-aware `is_quiescent` | **`truncated_never_proven`**, **`prefix_safety_sound`**, **`prefix_quiescence_sound`**, `complete_proven_*`, `quiescentAt_noReap`, `rests_transfer` |
| `Sound` | composition, untimed and env-free, reaping included | `routeB_untimed_safety_sound_keyInv`, `routeB_untimed_quiescence_sound_keyInv`, **`routeB_untimed_safety_sound`**, **`routeB_untimed_quiescence_sound`** |
| `Aligned` | name alignment over a list of places, one name across all (`NameAligned`, `QuiescentNameAligned`) | `aligned_key_inv`, `aligned_view_iff`, `alignedAll_congr_mem`, `alignedAll_key_inv`, `alignedAll_view_iff`, `alignedAll_uncoloured`, **`routeB_untimed_nameAligned_sound`**, **`routeB_untimed_quiescentNameAligned_sound`** |
| `Classify` | `classify` (pre-fix `classifyT`, shipped `classifyS`), the bridge to `InFragment`, the off-key rule, the builders' checks, three closed issues, key order | **`classifyT_inFragment`**, **`classifyS_inFragment`**, **`offKey_rule_is_necessary`** (`4d7a9d9`), `classifyS_mint`, `classifyS_consume`, `classifyS_join`, `builderOK_posKeys`, `dupKey_breaks_simulation` / `dupKey_refused`, `copyingMint_breaks_simulation` / `copyingMint_refused`, `zeroKey_breaks_quiescence` / `zeroKey_refused`, `joinEnab_perm_of_pos`, `zeroKey_order_matters` |
| `Retrodict` | the other past fixes | `willFire_guard_is_necessary_routeB` (`c23cd9e`), `ver006_binds_routeB` (`662ec39`), `env_count_frozen` / `env_count_witness` (`89aaeec`), `envObservation_none_*` |

**Premises about the Rust.** Stated as hypotheses unless marked otherwise. Items 1, 4, 5 and 8
are built into the definitions (`keyOf`, `NuStepC`), item 6 is how the model is written, and
items 3 and 7 are discharged by the transition builder (`Classify.BuilderOK`):
1. The base intern key determines everything the successor step reads of a class's base
   (marking, zone with its clock order, `ready_earliest`): the key of a class is modelled as the
   base itself (`Graph.lean`). `intern_base` keys all three; `zone_key` lists the clock names in
   the canonical order `compute_successor` lays them out in. (Built into `keyOf`.)
2. `coloured_order` is duplicate-free (a `BTreeSet`), every input arc is unguarded ([IO-006]), the
   coloured places start empty (otherwise `verify_via_name_scg` returns `None`, or `Unknown` for
   name alignment ([NU-055]); never `Proven`).
3. `InFragment`, derived from `classify`'s answer by `classifyT_inFragment` given two join
   conditions `classify` does not check: distinct keys (`dupKey_breaks_simulation` shows it is
   needed) and at most one input spec per key place (`hone`). Both are discharged:
   `MatchSpecBuilder::build` and `TransitionBuilder::build` panic on a place keyed twice
   ([NU-020]), `TransitionBuilder::build` on two input arcs on one place ([CORE-030] AC3), and
   every transition passes through it (`classifyS_inFragment`, `dupKey_refused`).
4. Action contracts (`Contract`; built into `NuStepC`, not a hypothesis): a `Mint` writes one
   fresh name into all its coloured outputs; a `Consume` writes only a name it consumed
   ([NU-051]). The shipped `classify` reads a writer as a `Mint` only when the net declares it
   ([NU-010]: `SmtVerifier::mint_transitions`, or consuming a declared budget place,
   `declared_mints`) and its timeout writes no coloured place, keeps a `Consume` only when
   each coloured timeout write forwards its consumed input, and keeps a `Join` only when each
   coloured timeout write forwards one of its match keys (`classifyS_mint`,
   `classifyS_consume`, `classifyS_join`). A join's coloured writes are relay targets, and the
   executor fails a firing whose relay deposit carries no name or another one ([NU-054]); a
   forward of a key carries the matched name (given item 8). So the executor's own timeout
   writes never rely on a contract, and an undeclared copying `fork()` is refused
   (`copyingMint_refused`). What a declared mint's or a
   consumer's action writes is still not checked at run time; the report names both contracts.
   The theorems describe only runs whose actions keep them.
5. Under `Conflict`, the executor never fires a transition `priority_dominated` calls dominated
   (the [NU-052] soundness argument; `Priority.lean`). Built into `NuStepC` (its last conjunct),
   not a hypothesis: the theorems describe only runs that respect it. A late executor that reaps
   a deadline transition breaks it, which is why `verify_via_name_scg_reaping` falls back to
   `PrioritySemantics::None` whenever the reapable set is non-empty, for every property (unless
   the caller sets `assume_no_reaping`, which empties that set).
   An action in flight breaks it too: a pruner `H` whose feeder is still running, or which is
   running itself, cannot pre-empt `L` on the executor. So `SmtVerifier::with_in_flight` splits
   every pruner and every depositor into a pruner's input or read places
   (`in_flight::conflict_demand`), `priority_dominated` skips a pruner whose `inflight:` place is
   marked (`BaseLayer.idle`, `Priority.lean`'s `inFlight_guard_is_necessary`), and when one of
   those transitions cannot be split (a ν-join pruner, or the mint feeding it) the verifier
   turns `Conflict` off for that verification. That the premise then holds on the split net is
   argued in `in_flight.rs` and has no proof here: `InFlight.lean` has no priorities, and the
   theorems here are for `untimedBase`, an atomic net with no `inflight:` place.
6. A modelling fact, not an assumption about the Rust's behaviour: every add / remove
   `name_successors` issues targets a coloured place (so an uncoloured one is a no-op in the
   model), and a coloured fixed deposit is one token (the `Deposit::Tokens(1)` rule, which
   `classify` enforces; `classifyT` rule 2). A drained forward (`Deposit::Drained`) is modelled
   (`Row.resolve`, resolved at the marking fired in as `produce_marking` does); `classify` keeps
   it out of coloured places.
7. For quiescence only: every join key consumes at least one token (`PosKeys`;
   `zeroKey_breaks_quiescence`: `classify` admits `In::Exactly { count: 0 }`). Discharged:
   `TransitionBuilder::build` panics on an input that requires zero tokens
   (`builderOK_posKeys`, `zeroKey_refused`). The model keeps
   `coloured_in` in key order, the Rust sorts it by place name, and `enabling_symbols` seeds from
   its head, so the order matters for a zero-count key (`zeroKey_order_matters`) and drops out
   under `PosKeys` (`joinEnab_perm_of_pos`).
8. **One global total name projection** (`Exec.ProjCoherent`; built into `NuStepC`, not a
   hypothesis). The model reads every coloured token through one `nameOf : Colour → ℕ`; the
   runtime has one partial `KeyFn` per match key of each join and per relay target, and
   `find_match_binding` skips a token its key projects to `None`. The theorems describe the
   executor only when every key and relay projection that reads a coloured place agrees with
   `nameOf` there and never returns `None`. `classify` checks neither; [NU-050] states it as a
   contract on the net, which is what this item cites.

**Deadline reaping** ([TIME-013], [VER-002], [VER-004]). `is_quiescent` is modelled with its
`fires_unreapable` branch: an expanded class rests when every successor is a firing of a
reapable transition (`Decide.quiescentAt reap`; with nothing reapable, no successor at all,
`quiescentAt_noReap`). `routeB_untimed_quiescence_sound` takes the reapable set and concludes
for every executor marking where only reapable transitions can fire (`ExecRests`), which is
`ExecQuiescent` when the set is empty. The rest of `verify_via_name_scg_reaping` is modelled
elsewhere or not needed here:

* It builds the graph on `reaping::relax_late`'s net for **every** property, marking properties
  included, with `late` the set the caller passes (`SmtVerifier::late_set`: every `deadline`,
  `window` and `exact` transition of the net, none under `assume_no_reaping`), a superset of the
  reapable set (`exact` is late, never reapable). The relaxation is `TimedScg/Late.lean`'s
  (`Timing.relaxLate`, `relaxLate_fromTimings`, with the finite `MAX_DURATION_MS` for `⊤`), and
  `late_run_sound` is the premise the Rust relies on: a late executor's runs lie in the relaxed
  graph. On the untimed instance the end-to-end theorems are about, nothing has a latest bound,
  so the relaxation is a no-op there. The Lean witness of what the unrelaxed graph misses is
  `TimedScg/Retrodict.reaping_escapes_timed_graph`, now the retrodiction of Route B before the
  fix.
* The reapable set it reads rest by goes to quiescence properties only (`rests_on`; `Decide.Prop'`).
* The fallback from `Conflict` to `None`, which the theorems do not need because they take the
  [NU-052] premise (item 5) as part of the step, and which the Rust needs because a late
  executor does not keep that premise.

That a late executor really comes to rest only at `ExecRests` markings is [TIME-013]'s runtime
statement, not proved here.

**Scope.** The executor side is untimed, environment-free and atomic (`untimedBase`, `NuStepC`: a
firing consumes and deposits in one step, so an action takes no time): the
end-to-end theorems are about that instance, not the shipped Route B, which always builds the
timed DBM graph and whose `Conflict` prune reads `ready_earliest`. The step and the equivariance
theorem are for an abstract base, so they cover the timed class too, but no timed executor
simulation is proved (gap R6). The shipped base successor is computed per name step with
name-gated clocks (`compute_successor_gated`, `Graph.lean`, `nameEnabled_comp`); the abstract
base step of the model does not take the gate. Environment places are modelled only as far as the two [VER-006]
retrodictions and rule 4's read set need (gap R5). `Proven` is proved sound; `Violated` is proved
sound for the graph (a reachable class), not for the executor — a consumer fires on any resident
symbol in the graph and on the FIFO head at run time, so the graph over-approximates.

**Actions in flight.** The verifier runs Route B on the [VER-004] split net (`InFlight.lean`),
which covers an action in flight; a ν-join cannot be split, so a net that tests a join's output
non-monotonically is refused. Under `assume_no_reaping` Route B keeps every latest bound and
reads each firing as one instant step, so its verdict describes an on-time executor whose
actions take no time: an action that runs while a bound passes lets other transitions fire first.
The report says so (`reaping::no_reaping_route_b_note`, and the closed-graph note
`NOTE_ON_TIME` in place of the "sound AND complete" one when a latest bound is kept); nothing
here models it.
-/
