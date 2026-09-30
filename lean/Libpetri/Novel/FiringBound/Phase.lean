import Libpetri.Novel.FiringBound.Bmc
import Libpetri.Novel.Enumeration
import Libpetri.Novel.Seam

/-!
# The firing-bound phase's verdicts ([VER-019])

`run_firing_bound_phase`'s depth loop (`depthLoop`), the soundness of its `Proven` over the
abstract and the concrete semantics, through the name → index seam to the caller's net
(`phase_postfix_deadlock_sound`), and agreement with the enumeration route ([VER-017]). See
`Libpetri/Novel/FiringBound.lean`.
-/

namespace Libpetri.Novel.FiringBound

open Libpetri
open Libpetri.Novel.ForwardDeposit
open Libpetri.Novel.LinearBound

/-! ## The phase: `run_firing_bound_phase` -/

/-- What the depth loop ends with: `unsat` at a depth reaching the bound, a `sat` depth (then
decoded and replayed), or stepping aside (an unknown reply, the depth limit, an exhausted
budget). -/
inductive DepthOutcome where
  | proven
  | sat (d : Nat)
  | stop
  deriving DecidableEq, Repr

/-- The depth loop of `run_firing_bound_phase`. `ask d` is the solver's reply to the depth-`d`
script: `some true` = `sat`, `some false` = `unsat`, `none` = no verdict. `unsat` at a depth
`≥ k` is `Proven`, checked before the depth limit; otherwise the next depth is
`min(2·depth, k, max_depth)`. The Rust loop needs no fuel (the depth grows until it reaches `k`
or the limit); running out of fuel here is stepping aside, which only loses answers. -/
def depthLoop (k maxDepth : Nat) (ask : Nat → Option Bool) : Nat → Nat → DepthOutcome
  | 0, _ => .stop
  | fuel + 1, depth =>
    match ask depth with
    | none => .stop
    | some true => .sat depth
    | some false =>
      if k ≤ depth then .proven
      else if maxDepth ≤ depth then .stop
      else depthLoop k maxDepth ask fuel (min (min (2 * depth) k) maxDepth)

/-- The loop from its first depth, `min(k, 8, max_depth)`. -/
def phaseDepths (k maxDepth : Nat) (ask : Nat → Option Bool) : DepthOutcome :=
  depthLoop k maxDepth ask (k + 1) (min (min k 8) maxDepth)

/-- `Proven` only after `unsat` at a depth that reaches the bound. -/
theorem depthLoop_proven {k maxDepth : Nat} {ask : Nat → Option Bool} :
    ∀ {fuel depth : Nat}, depthLoop k maxDepth ask fuel depth = .proven →
      ∃ d, k ≤ d ∧ ask d = some false
  | 0, _, h => by simp [depthLoop] at h
  | fuel + 1, depth, h => by
    unfold depthLoop at h
    cases hq : ask depth with
    | none => rw [hq] at h; simp only at h; cases h
    | some b =>
      rw [hq] at h
      cases b with
      | true => simp only at h; cases h
      | false =>
        simp only at h
        split at h
        · rename_i hk; exact ⟨depth, hk, hq⟩
        · split at h
          · cases h
          · exact depthLoop_proven h

/-- A `sat` depth is one the solver answered `sat`. -/
theorem depthLoop_sat {k maxDepth : Nat} {ask : Nat → Option Bool} :
    ∀ {fuel depth d : Nat}, depthLoop k maxDepth ask fuel depth = .sat d → ask d = some true
  | 0, _, _, h => by simp [depthLoop] at h
  | fuel + 1, depth, d, h => by
    unfold depthLoop at h
    cases hq : ask depth with
    | none => rw [hq] at h; exact absurd h (by simp)
    | some b =>
      rw [hq] at h
      cases b with
      | true =>
        simp only [DepthOutcome.sat.injEq] at h
        subst h; exact hq
      | false =>
        simp only at h
        split at h
        · exact absurd h (by simp)
        · split at h
          · exact absurd h (by simp)
          · exact depthLoop_sat h

/-- **The phase's `Proven` is sound** (headline). With a ranking the exact check accepts
(bound `K`), and z3's `unsat` correct (P4), a loop that answers `Proven` has shown that no
`ReachAD`-reachable marking violates. -/
theorem phase_proven_sound {rows : List Row} {n : Nat} {a0 : AMarking} {r : Weight} {K : Int}
    {badI : (PlaceId → Int) → Prop} {bad : AMarking → Prop} {maxDepth : Nat}
    {ask : Nat → Option Bool}
    (hWF : WellFormedRows n rows) (hBad : BadAgrees badI bad)
    (hK : checkRankingExact n rows a0 r = some K)
    (hAsk : ∀ d, ask d = some false → ¬ BmcSat rows n a0 badI d)
    (h : phaseDepths K.toNat maxDepth ask = .proven) :
    ProvenFor (ReachAD rows a0) bad := by
  obtain ⟨d, hkd, hq⟩ := depthLoop_proven h
  have hKd : K ≤ d := by
    have := Int.self_le_toNat K
    omega
  intro a hreach hbad
  exact hAsk d hq ((bmc_exact_at_bound hWF hBad hK hKd).mpr ⟨a, hreach, hbad⟩)

/-- **A replayed `Violated` is reachable**: the run `replay_run` accepts ends at a
`ReachAD`-reachable marking that violates. -/
theorem phase_violated_sound {rows : List Row} {a0 a : AMarking} {bad : AMarking → Prop}
    {ts : List Nat} (hrep : replay rows a0 ts = some a) (hbad : bad a) :
    ∃ b, ReachAD rows a0 b ∧ bad b :=
  ⟨a, replay_sound hrep, hbad⟩

/-- **The phase's `Proven` holds of the untimed executor**, timeout outcomes included: over the
fixed rows of a net whose consume-all arcs are unguarded and whose forwards draw from `One` /
`Exactly` inputs, no marking a concrete run reaches violates under `alpha`. `StepCD` is the
untimed atomic step relation: it has no clocks and no deadline reaping ([TIME-013]). The
conclusion is about the markings the executor visits, so it covers the marking properties of a
timed run too (`Reaping.bmc_proven_marking_timed`). It does **not** say the timed executor's rest
state satisfies a quiescence property: after a reap the executor can rest at a marking where the
untimed net still enables a transition, and a `DeadlockFree` `Proven` for the strict
quiescence clause is then wrong about the timed run (R16, the pre-fix phase in
`Reaping.firing_bound_proves_reaped_net`). The shipped phase's script and replay read
reap-quiescence instead, and `ReapAware.reap_aware_ac3` carries that `Proven` to every timed
rest; see `FiringBound.lean`. -/
theorem phase_proven_concrete {net : SpecNet} {n : Nat} {m0 : CMarking} {r : Weight} {K : Int}
    {badI : (PlaceId → Int) → Prop} {bad : AMarking → Prop} {maxDepth : Nat}
    {ask : Nat → Option Bool}
    (hSpec : ∀ x ∈ net, GuardFreeConsumeAll x.1 ∧ FixedForwards x.1 x.2)
    (hWF : WellFormedRows n (flatRows net)) (hBad : BadAgrees badI bad)
    (hK : checkRankingExact n (flatRows net) (alpha m0) r = some K)
    (hAsk : ∀ d, ask d = some false → ¬ BmcSat (flatRows net) n (alpha m0) badI d)
    (h : phaseDepths K.toNat maxDepth ask = .proven)
    {m : CMarking} (hR : Relation.ReflTransGen (StepCD net) m0 m) : ¬ bad (alpha m) :=
  phase_proven_sound hWF hBad hK hAsk h _ (forward_reachability_simulated hSpec hR)

/-- `ReachAD` is its own inductive invariant. -/
theorem reachAD_inductive (rows : List Row) (a0 : AMarking) :
    Libpetri.Novel.Seam.InductiveInv rows a0 (ReachAD rows a0) :=
  ⟨Relation.ReflTransGen.refl, fun _ _ ha hs => Relation.ReflTransGen.tail ha hs⟩

open Libpetri.Novel.Seam in
/-- **Through the seam, for `DeadlockFree`.** The verifier flattens `inertNet net m0` and seeds
the phase with `initial[i] = initial_marking.count(flat.places[i])`, which is `encodeM0`. A
firing-bound `Proven` there, for the integer violation `encode_property_violation` writes (P5
against `deadlockBad`), holds of every marking the **untimed** executor reaches on the caller's
net: no marking reachable under `ReachNC` (untimed, no deadline reaping) is an untimed deadlock.
The reachable set is its own inductive invariant, so this is `Seam.postfix_deadlock_sound` with
the phase in place of the CHC fixpoint.

This is not a claim that the timed executor never comes to rest stranded. Under [TIME-013] a
reaped `Deadline` / `Window` transition leaves its tokens in place and the executor can stop
`Quiescent` at a marking the untimed net still moves from; `Reaping.firing_bound_proves_reaped_net`
is a caller net on which every premise here holds and the timed run rests with a token on a
non-sink place (R16) for the phase before the reaping fix. Here `deadlockBad` is over the whole
flat net, which is the shipped script's clause only when no row is reapable (under
`assume_no_reaping`, or on a net with no `Deadline` / `Window` transition). Otherwise the shipped
script drops the reapable rows from the quiescence clause (`ReapAware.deadlockBad_filter_eq`),
and `ReapAware.reap_aware_ac3` is the timed statement. -/
theorem phase_postfix_deadlock_sound {N : Type} [DecidableEq N] {net : NNet N}
    {m0 : NMarking N} {M0 M : NCMarking N} {sinks : List N} {cond : List (CondSinks N)}
    {n : Nat} {r : Weight} {K : Int} {badI : (PlaceId → Int) → Prop} {maxDepth : Nat}
    {ask : Nat → Option Bool}
    (hDecl : ArcsDeclared net) (hD : InputsDistinct net) (hSeed : SeedsFrom M0 m0)
    (hWF : WellFormedRows n
      (flatNet (flatIndex (inertNet net m0).places) (inertNet net m0)))
    (hBad : BadAgrees badI fun a =>
      deadlockBad (flatNet (flatIndex (inertNet net m0).places) (inertNet net m0))
        (flatIndex (inertNet net m0).places) sinks cond a = true)
    (hK : checkRankingExact n (flatNet (flatIndex (inertNet net m0).places) (inertNet net m0))
      (encodeM0 (flatIndex (inertNet net m0).places) m0) r = some K)
    (hAsk : ∀ d, ask d = some false →
      ¬ BmcSat (flatNet (flatIndex (inertNet net m0).places) (inertNet net m0)) n
        (encodeM0 (flatIndex (inertNet net m0).places) m0) badI d)
    (h : phaseDepths K.toNat maxDepth ask = .proven)
    (hR : ReachNC net M0 M) : ¬ NDeadlock net sinks cond (alphaN M) :=
  postfix_deadlock_sound hDecl hD hSeed (reachAD_inductive _ _)
    (fun a ha => phase_proven_sound hWF hBad hK hAsk h a ha) hR

/-! ## Agreement with the enumeration route ([VER-017]) -/

open Libpetri.Novel.Enumeration in
/-- **Route agreement**: when the enumeration closes and a ranking exists, the enumeration's
`Proven` and the bounded model check's `unsat` at the firing bound are the same statement. -/
theorem bmc_agrees_with_enumeration [DecidableEq AMarking] {rows : List Row} {n : Nat}
    {a0 : AMarking} {r : Weight} {K : Int} {badI : (PlaceId → Int) → Prop}
    {badB : AMarking → Bool} {maxClasses fuel d : Nat}
    (hWF : WellFormedRows n rows) (hBad : BadAgrees badI fun a => badB a = true)
    (hK : checkRankingExact n rows a0 r = some K) (hd : K ≤ d)
    (hclosed : (build (succRows rows) maxClasses fuel a0).2 = true) :
    proven badB (build (succRows rows) maxClasses fuel a0).1 = true ↔
      ¬ BmcSat rows n a0 badI d := by
  rw [(rows_enumeration_exact hclosed badB).2.1, bmc_exact_at_bound hWF hBad hK hd]
  constructor
  · rintro hall ⟨a, hreach, hbad⟩
    rw [hall a hreach] at hbad
    exact absurd hbad (by decide)
  · intro hno a hreach
    cases hb : badB a with
    | false => rfl
    | true => exact absurd ⟨a, hreach, hb⟩ hno

end Libpetri.Novel.FiringBound
