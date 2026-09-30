import Libpetri.Novel.Seam.Bad

/-!
# A CHC `Proven` is a statement about the caller's marking ([VER-001], [VER-004])

The flat-route chain had three unproved links (`research/net-metrics/review/lean-gaps`): the seed
(`encode_net` writes `encodeM0 (flatten net) m0`, not `alpha m0`), the violation predicate (`Bad`
ranges over flat indices), and the step from an inductive invariant of the CHC system to the
property of the executor's reachable markings. `chc_proven_sound` closes all three for the
untimed, env-free fragment, reusing Proposition 1 with integer posts
(`ForwardDeposit.rows_reachability_simulated`) for the firing rule:

  named executor run ─(`reachNC_pull`)→ flat row steps ─(`rows_reachability_simulated`)→
    `ReachAD` from `encodeM0` ─(inductive invariant)→ `¬ Bad`
    ─(`Bad` ↔ named property, under `Covers`)→ property holds.

The CHC transition rules are modelled with the post vector `flatten` writes, a row's deposit
counts (`StepAD`), so every row of `branch_outcomes::outcomes` is covered, including a timeout
forward from an `exactly(k)` input with `post[to] = k ≥ 2`. The executor's side of that is
`StepNC.deposit`: each firing deposits one row's counts, which `ForwardDeposit.stepCD_stepCR`
proves of rows built by `fixedRows` when every forward draws from a `One` / `Exactly` input.
`spec_proven_sound` states that composition at the flat level. A forward of a drained batch has
no row and is refused before any route (`branch_outcomes::drained_forward`).

`Covers ix m0` is the one premise about the seam. It is what the inert-place rewrite provides
(`postfix_proven_sound`) and what the pre-fix pipeline lacked (`Retrodict.lean`,
`covers_is_necessary`). `verify_closed` (`smt_verifier.rs`) runs every route inside
`with_inert_places`, so the net every route reads is `inertNet`; the [EXEC-042] terminal rewrite
it applies next is `TerminalRewrite.lean`'s and is not composed here.
-/

namespace Libpetri.Novel.Seam

open Libpetri

variable {N : Type} [DecidableEq N]

/-- The executor starts from the caller's marking: its counts are the `MarkingState`'s. -/
def SeedsFrom (M0 : NCMarking N) (m0 : NMarking N) : Prop := alphaN M0 = m0.count

/-- An inductive invariant of the CHC system: contains the init rule's seed and is closed under
the transition rules. A `sat` answer from Spacer (reported `Proven` by `process_z3_result`) is an
interpretation of `Reachable` with exactly these two properties that also refutes the error
rule's body. -/
structure InductiveInv (flat : FlatNet) (a0 : AMarking) (Inv : AMarking → Prop) : Prop where
  init : Inv a0
  step : ∀ a b, Inv a → ForwardDeposit.StepAD flat a b → Inv b

theorem InductiveInv.reach {flat : FlatNet} {a0 : AMarking} {Inv : AMarking → Prop}
    (h : InductiveInv flat a0 Inv) {a : AMarking} (hr : ForwardDeposit.ReachAD flat a0 a) :
    Inv a := by
  induction hr with
  | refl => exact h.init
  | tail _ hs ih => exact h.step _ _ ih hs

/-- **End-to-end soundness of a CHC `Proven`.**

Premises: the net's arcs resolve in the index (`ArcsIn`; true of `flatten`), the executor starts
from `m0`, the index
**covers** `m0`, the CHC system over the flat net seeded with `encodeM0 ix m0` has an inductive
invariant that refutes `Bad`, and `Bad` catches the named violation `Sem` on every covered
marking. Conclusion: no marking the executor reaches from `M0` violates `Sem`. Rows of any
multiplicity are covered (see the module note).

The `Bad` premise is discharged per property by `deadlockBad_iff`, `placeBoundBad_iff`,
`pairMarkedBad_iff` (the pairwise `MutualExclusion`), `allMarkedBad_of` (`Unreachable`) and
`countBad_iff`. -/
theorem chc_proven_sound {net : NNet N} {ix : PlaceIndex N} {m0 : NMarking N}
    {M0 M : NCMarking N}
    (hA : ArcsIn ix net) (hSeed : SeedsFrom M0 m0)
    (hCov : Covers ix m0.count)
    {Inv : AMarking → Prop} (hInv : InductiveInv (flatNet ix net) (encodeM0 ix m0) Inv)
    {Bad : AMarking → Prop} {Sem : (N → Nat) → Prop}
    (hBad : ∀ m, Covers ix m → Sem m → Bad (restrict ix m))
    (hSafe : ∀ a, Inv a → ¬ Bad a)
    (hR : ReachNC net M0 M) : ¬ Sem (alphaN M) := by
  have hc0 : Covers ix (alphaN M0) := by rw [hSeed]; exact hCov
  have hcM := covers_reachNC hA hc0 hR
  have hRA := reachNC_reachAD hA hR
  rw [hSeed, ← encodeM0_eq_restrict] at hRA
  exact fun hs => hSafe _ (hInv.reach hRA) (hBad _ hcM hs)

/-- `chc_proven_sound` for `DeadlockFree` with declared and conditional sinks. -/
theorem deadlock_proven_sound {net : NNet N} {ix : PlaceIndex N} {m0 : NMarking N}
    {M0 M : NCMarking N} {sinks : List N} {cond : List (CondSinks N)}
    (hA : ArcsIn ix net) (hD : InputsDistinct net) (hSeed : SeedsFrom M0 m0)
    (hCov : Covers ix m0.count)
    {Inv : AMarking → Prop} (hInv : InductiveInv (flatNet ix net) (encodeM0 ix m0) Inv)
    (hSafe : ∀ a, Inv a → ¬ deadlockBad (flatNet ix net) ix sinks cond a = true)
    (hR : ReachNC net M0 M) : ¬ NDeadlock net sinks cond (alphaN M) :=
  chc_proven_sound hA hSeed hCov hInv
    (fun _ hc hs => (deadlockBad_iff hA hD sinks cond hc).mpr hs) hSafe hR

/-- **The post-fix pipeline is sound with no seam premise.** The verifier flattens
`inertNet net m0` (`with_inert_places`), whose index covers `m0` by construction
(`inert_covers`), and whose transitions are the net's, so the executor's runs are the same. Every
`Proven` it certifies (for any property arm whose `Bad` catches its named violation on covered
markings) holds of every marking the executor reaches on the original net — forward rows with
`post[to] = k ≥ 2` included, since the flat semantics is `StepAD`. The premise on the executor
is `StepNC`'s: each firing deposits one row's counts. -/
theorem postfix_proven_sound {net : NNet N} {m0 : NMarking N} {M0 M : NCMarking N}
    (hDecl : ArcsDeclared net) (hSeed : SeedsFrom M0 m0)
    {Inv : AMarking → Prop}
    (hInv : InductiveInv (flatNet (flatIndex (inertNet net m0).places) (inertNet net m0))
      (encodeM0 (flatIndex (inertNet net m0).places) m0) Inv)
    {Bad : AMarking → Prop} {Sem : (N → Nat) → Prop}
    (hBad : ∀ m, Covers (flatIndex (inertNet net m0).places) m → Sem m →
      Bad (restrict (flatIndex (inertNet net m0).places) m))
    (hSafe : ∀ a, Inv a → ¬ Bad a)
    (hR : ReachNC net M0 M) : ¬ Sem (alphaN M) :=
  chc_proven_sound (arcsIn_flatIndex (arcsDeclared_inert hDecl m0)) hSeed
    (inert_covers net m0) hInv hBad hSafe hR

/-- The post-fix `DeadlockFree` instance. -/
theorem postfix_deadlock_sound {net : NNet N} {m0 : NMarking N} {M0 M : NCMarking N}
    {sinks : List N} {cond : List (CondSinks N)}
    (hDecl : ArcsDeclared net) (hD : InputsDistinct net) (hSeed : SeedsFrom M0 m0)
    {Inv : AMarking → Prop}
    (hInv : InductiveInv (flatNet (flatIndex (inertNet net m0).places) (inertNet net m0))
      (encodeM0 (flatIndex (inertNet net m0).places) m0) Inv)
    (hSafe : ∀ a, Inv a → ¬ deadlockBad (flatNet (flatIndex (inertNet net m0).places)
      (inertNet net m0)) (flatIndex (inertNet net m0).places) sinks cond a = true)
    (hR : ReachNC net M0 M) : ¬ NDeadlock net sinks cond (alphaN M) :=
  deadlock_proven_sound (net := inertNet net m0)
    (arcsIn_flatIndex (arcsDeclared_inert hDecl m0)) hD hSeed (inert_covers net m0) hInv hSafe hR

/-- **Forward rows at the flat level, end to end.** For a flat net of transitions with output
specs whose every forward draws from a `One` / `Exactly` input, an inductive invariant of the CHC
system over the fixed rows (`flatRows`, integer posts) that refutes `Bad` holds on the α-image
of every concrete run, whichever way each firing ends: action branch or timeout. The composition
of `ForwardDeposit.forward_reachability_simulated` with the invariant argument above. -/
theorem spec_proven_sound {net : ForwardDeposit.SpecNet} {m0 m : CMarking}
    (hWF : ∀ x ∈ net, GuardFreeConsumeAll x.1 ∧ ForwardDeposit.FixedForwards x.1 x.2)
    {Inv : AMarking → Prop} (hInv : InductiveInv (ForwardDeposit.flatRows net) (alpha m0) Inv)
    {Bad : AMarking → Prop} (hSafe : ∀ a, Inv a → ¬ Bad a)
    (hR : Relation.ReflTransGen (ForwardDeposit.StepCD net) m0 m) : ¬ Bad (alpha m) :=
  hSafe _ (hInv.reach (ForwardDeposit.forward_reachability_simulated hWF hR))

end Libpetri.Novel.Seam
