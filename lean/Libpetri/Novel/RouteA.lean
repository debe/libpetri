import Libpetri.Novel.RouteA.Model
import Libpetri.Novel.RouteA.Simulate
import Libpetri.Novel.RouteA.Plan
import Libpetri.Novel.RouteA.Retrodict
import Libpetri.Novel.RouteA.Reaping
import Libpetri.Novel.RouteA.Shipped

/-!
# Route A, the name-coloured encoding, for every colour-slot bound ([NU-050], [NU-053])

Root of the `Novel/RouteA/` modules, which close gap R4 of the Lean coverage analysis
(`Semiflow.lean`'s `vacuous_colour_layer` covered `k = 0` only):

* `Model.lean`: the plan, the CHC relation `encode_coloured` emitted before the self-loop fix
  (the old `Class::Consume` write order, `sConsume`), its strict quiescence predicate, and the ν
  semantics it must over-approximate, with every premise about the runtime named (P1 to P6).
* `Simulate.lean`: `colour_slots_suffice` (a covering semiflow bound caps the live names by
  `k`), `coloured_simulates` (every ν-reachable marking maps, injectively on its live names,
  into a reachable state of the `k`-slot encoding), and the two verdict transfers
  `routeA_safety_sound` / `routeA_quiescence_sound`.
* `Plan.lean`: `build_plan` / `colour_slot_bound` modelled, with the classification gates as
  parameters (`classifyRowG`): the shipped gates (`buildPlan`, `shippedGate`: a `Mint` row must
  be a declared mint whose timeout writes no coloured place, a `Consume` row must forward its
  input in every coloured timeout write, `shipped_mint`, `shipped_consume`) and the ones before
  the NU-010 fix (`buildPlanBudget`, `budgetGate`: one budget token made a mint). The Rust also
  refuses a `Join` row whose source writes a coloured place on timeout other than by forwarding
  one of its match keys ([NU-054]: the executor fails that firing). `shippedGate` does not model
  that refusal. It only refuses more, so every plan the shipped `build_plan` returns is one
  `buildPlan` returns, and the results about accepted plans carry over.
  `buildPlanG_premisesS`: a plan either returns discharges every plan premise but
  `ConsumeNoSelfLoop`.
* `Retrodict.lean`: the `667e67d` budget-count `k` and the `f52c482` injection `Proven`s
  reproduced, and two wrong `Proven`s that were live until the NU-010 and self-loop fixes: a
  coloured output with no coloured input classified as a mint because it consumed a budget
  token, shown on a timeout forward into a match key (`forward_mint_false_proven`; the shipped
  `build_plan` refuses that net, `forward_mint_refused`), and a self-loop coloured consumer
  whose rule the old write order made unsatisfiable under any conjoined law that weights its
  input, the default semiflow basis included (`self_loop_consume_false_proven`,
  `selfLoop_false_proven_any_basis`).
* `Reaping.lean`: deadline reaping ([TIME-013], [VER-002]). `routeA_quiescence_sound` reads
  the strict predicate and misses the markings where the executor rests after a reap. A
  transition is reapable when its timing is `Deadline` or `Window` (`reaping::is_reapable`;
  `Exact` is never reaped, [TIME-006]). The shipped `encode_coloured_quiescent` skips the rows
  of reapable transitions (`ft.reapable`), which is `DeadERs`, equal to the reaping-aware
  `DeadER` (`deadERs_iff`) and to the strict `DeadE` under `assume_no_reaping`
  (`deadERs_nil`). It is sound for every ν-reachable marking a timed run of either backend
  rests at (`routeA_quiescence_sound_reaping`, `routeA_reap_aware_sound`, the latter over
  `Novel/ReapAware.lean`'s executor model). The witness `ReapW.reaping_breaks_routeA_quiescence`
  is a plan `build_plan` returns (`C = [a, b]`, `k = 1`): the strict query is `Proven`, the
  executor rests at a marking that strands a token, and the shipped query is not `Proven`.
* `Shipped.lean`: the shipped `Class::Consume` arm nets a self-loop to zero, which is the join
  rule on the one input (`Cls.shipped`). The ν semantics is unchanged (`reachNu_shipped`), and
  the shipped encoding meets every premise from the plan premises alone (`premises_shipped`), so
  `routeA_safety_sound_shipped` / `routeA_quiescence_sound_shipped` need no `ConsumeNoSelfLoop`.
  On the self-loop witness every premise now holds (`selfLoop_premises_shipped`).

What is proved is **soundness** (inclusion of the ν-reachable markings, under the premises),
not exactness. The report used to say "exact within budget k"; it now says "colour-slot bound
k" and names the mint and relay contracts the verdict assumes.

**How the premises enter.** P1–P4 and P6 (`Model.lean`) are built into `NuStep`, `NameEffect`
and `ReachNu`, not hypotheses: P1 and P3 are unenforced action contracts, and where they fail
the theorems describe a relation that is not the executor's. P5 (no guard on an input arc,
[IO-006]) is a hypothesis: `GuardFreeConsumeAll` through `Premises.guardFree`, and `Unguarded`
for the quiescence transfers. The other `Premises` fields are hypotheses too; `ConsumeNoSelfLoop`
is one only for the old encoder (`Shipped.lean`). P1 and P3 now rest on declarations: a row is
a `Mint` only for a declared mint ([NU-010]) whose timeout writes no coloured place, and the
report states both contracts ("Mint contract (NU-010) assumed for ...", "Relay contract (NU-051)
assumed for ...").
-/
