import Libpetri.Novel.RouteB.Sim
import Libpetri.Novel.RouteB.Decide

/-!
# Route B end to end, untimed and environment-free: a `Proven` from a closed graph holds for the executor

Composition of the three layers, for the **untimed, environment-free instance** `routeB
untimedBase` (`readyLe` always true, no environment place, no injection). The shipped Rust
always builds the timed DBM graph, and its `Conflict` prune reads `ready_earliest`; no timed
executor simulation is proved (gap R6), so these theorems are about the untimed instance, not the
shipped Route B on a timed net. The step and `routeB_equivariant` are proved for an abstract
base and so cover the timed class too; what is missing is the timed executor side.

* `Decide.complete_proven_safety` / `complete_proven_quiescence` — a complete build's `Proven`
  holds of every state the plain exploration reaches (up to key), using `routeB_equivariant`;
* `exec_reach_simulated` — every executor-reachable marking's view is reached, up to key;
* `exec_rests_succ_reap`: every successor of the class of a marking where the executor can
  fire only reapable transitions ([TIME-013]) is a reapable firing; with nothing reapable,
  `exec_quiescent_succ_nil` (an executor-quiescent marking's class has no successor).

The property reads the base marking only (`bad S = badA S.b`), as every arm of
`decide_over_classes` does (`marking_violates`, `strands_token`, sinks, `pending`, counts).

Premises stated as hypotheses: `coloured_order` duplicate-free; every transition in the fragment
for its role (`InFragment`, which `Classify.classifyT_inFragment` derives from `classify`'s
answer plus two join conditions: distinct keys and one input spec per key place, both enforced
by `TransitionBuilder::build`, [NU-020] and [CORE-030] AC3, `Classify.classifyS_inFragment`);
unguarded input arcs; the coloured places initially empty (`verify_via_name_scg` returns `None`
otherwise); for quiescence, every join key consuming at least one token (`PosKeys`, enforced by
`TransitionBuilder::build`, `Classify.builderOK_posKeys`).

Premises **built into the step relation** `NuStepC`, not hypotheses: contract-abiding actions
(`Contract`: a `Mint` writes a fresh name, a `Consume` only a name it consumed), under
`Conflict` the [NU-052] priority premise (the executor never fires a transition the prune calls
dominated), and one global total name projection `nameOf` (`Exec.ProjCoherent`). The runtime reads each key and each relay target through its own
partial `KeyFn`; the theorems describe the executor only when all those projections agree with
one total `nameOf` on every token they read. Drained forwards (`Deposit::Drained`) are modelled
(`Row.resolve`), not assumed away.

`Classify.lean` shows the off-key rule, the distinct-keys condition and the `Mint` contract are
each necessary for the step, and `PosKeys` for quiescence.
-/

namespace Libpetri.Novel.RouteB

open Libpetri
open Libpetri.Novel.CanonicalKey
open Libpetri.Novel.ForwardDeposit

section Sound

variable {co : List PlaceId} {nameOf : Colour → ℕ} {net : List NuTrans} {role : NuTrans → Role}
  {conflict : Bool}

theorem keyOf_b {S S' : NState co AMarking} (h : keyOf S = keyOf S') : S.b = S'.b :=
  (Prod.mk.inj h).1

/-- **Route B's safety `Proven` holds for the untimed, environment-free executor.** A complete
build of the untimed instance from the initial class whose verdict for `bad` (reading the count
marking) is `Proven`: no marking an untimed, injection-free executor run (`NuStepC`) reaches is
bad. Not a statement about the shipped timed graph (gap R6). -/
theorem routeB_untimed_safety_sound (hco : co.Nodup) (hfr : ∀ T ∈ net, InFragment co T (role T))
    (hG : ∀ T ∈ net, GuardFree T.base) {badA : AMarking → Bool} {maxClasses : ℕ}
    {cut : ℕ → Bool} {stopBad : NState co AMarking → Bool} {stopAt : Bool} {fuel : ℕ}
    {m0 : CMarking} (hempty : ∀ i : Fin co.length, m0 co[i.1] = [])
    (hP : Decide.verdict (routeB untimedBase net role conflict)
      (Decide.build (routeB untimedBase net role conflict) maxClasses cut stopBad stopAt fuel
        (initState co (alpha m0)))
      (.safety fun S => badA S.b) = .proven)
    {m : CMarking} (hR : Relation.ReflTransGen (NuStepC co nameOf net role conflict) m0 m) :
    badA (alpha m) = false := by
  obtain ⟨S, hS, hk⟩ := exec_reach_simulated hco hfr hG (init_key hempty) hR
  have := Decide.complete_proven_safety (routeB_equivariant (co := co)) (bad := fun S => badA S.b)
    (fun a b h => by rw [keyOf_b h]) hP S hS
  rw [keyOf_b hk] at this
  exact this

/-- **Route B's quiescence `Proven` holds for the untimed, environment-free executor**, deadline
reaping included ([TIME-013], [VER-002]). A complete build of the untimed instance whose verdict
for the quiescence predicate `bad` over the reapable set `reap` is `Proven`: no marking an
untimed, injection-free executor run reaches and rests at (`ExecRests reap`: every transition it
can fire is reapable) is bad (`DeadlockFree`, `TerminatesAtSink`, `JoinedOrDeadLettered`,
`QuiescentCount`). With `reap` constantly false, `ExecRests` is `ExecQuiescent`
(`execRests_noReap`) and this is the plain `verify_via_name_scg` reading. Needs `PosKeys` beyond
the safety premises. -/
theorem routeB_untimed_quiescence_sound (hco : co.Nodup)
    (hfr : ∀ T ∈ net, InFragment co T (role T)) (hpos : ∀ T ∈ net, PosKeys (role T))
    (hG : ∀ T ∈ net, GuardFree T.base) {badA : AMarking → Bool} {reap : String → Bool}
    {maxClasses : ℕ} {cut : ℕ → Bool} {stopBad : NState co AMarking → Bool} {stopAt : Bool}
    {fuel : ℕ} {m0 : CMarking} (hempty : ∀ i : Fin co.length, m0 co[i.1] = [])
    (hP : Decide.verdict (routeB untimedBase net role conflict)
      (Decide.build (routeB untimedBase net role conflict) maxClasses cut stopBad stopAt fuel
        (initState co (alpha m0)))
      (.quiescence (fun S => badA S.b) reap) = .proven)
    {m : CMarking} (hR : Relation.ReflTransGen (NuStepC co nameOf net role conflict) m0 m)
    (hq : ExecRests (co := co) (nameOf := nameOf) (net := net) reap m) :
    badA (alpha m) = false := by
  obtain ⟨S, hS, hk⟩ := exec_reach_simulated hco hfr hG (init_key hempty) hR
  have hrest := exec_rests_succ_reap (role := role) (conflict := conflict) hfr hpos hG hk hq S.bound
  have := Decide.complete_proven_quiescence (routeB_equivariant (co := co))
    (bad := fun S => badA S.b) (fun a b h => by rw [keyOf_b h]) hP S hS
    ⟨S.bound, Nat.le_refl _, hrest⟩
  rw [keyOf_b hk] at this
  exact this

end Sound

end Libpetri.Novel.RouteB
