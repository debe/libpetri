import Libpetri.Spec.ConsistencyQueue
import Libpetri.Spec.GlossaryBuild
import Libpetri.Spec.Req.CORE_020
import Libpetri.Spec.Req.CORE_037

set_option linter.missingDocs true

/-!
# Consistency of the structure requirements with the CORE, IO, TIME and queue requirements (skeleton)

The target of this module is one theorem, `spec_consistent_structure`, that extends
`spec_consistent_queue` by the structure blocks of waves W2 and W3 ([CORE-002], [CORE-020],
[CORE-021], [CORE-040]–[CORE-043], [CORE-050]–[CORE-054], [CORE-060]–[CORE-063], [CORE-073]) on
one joint model. Conjoining blocks over independent parameters proves nothing on its own, so what
counts is the agreement conjuncts that tie each new parameter to a witness the existing blocks
already use:

* **Builder.** `projBuild TB = Build`: the transition builder `TB` of CORE-020 and CORE-021 has
  the build check `Build` of the IO blocks and of EXEC-012 (witness `refTransBuild`,
  `projBuild_ref`).
* **Timing.** `TimingAgree TB Q`: `TB` accepts a given timing exactly when TIME-001's contract
  `Q` builds it, and gives a transition built without a timing `Q`'s default
  (`refTransBuild_timingAgree`). Without it the joint model holds two unconnected transition
  builders; with it the first draft of CORE-020's line 4 has no model
  (`core020_arcsOnly_conflicts_TIME_001`), and a transition built without a timing is
  `Immediate` (`timingAgree_default`), which CORE-020 alone leaves to TIME-001.
* **Action** (W3, open). The default action (passthrough, [CORE-051]) has no agreement conjunct
  yet: until CORE-051's block joins, CORE-020 and this sketch accept a builder whose default
  action is another action.
* **Net view** (W2 fan-out). Every block that runs a net runs `b.toNet` or `b.toTimed tol` of a
  built net: `toTrans_reapable` gives `TimedNet`'s coherence by construction,
  `netNamesDistinct_iff` lifts ruling D10 to built nets, `toTimed_timing` gives each transition its
  own timing, and `built_timing_valid` keeps every timing the timed step reads valid.
* **Actions, context, initial state, snapshot** (W3). The action firing is a queue firing of the
  same `QF`, the initialiser is `TSt.init`, the snapshot's count projection is
  `Reference.Marking`'s canonical form.

This file is the skeleton of wave W2's tracer bullet. `joint_core_structure_sketch` fixes the
shape on the conjuncts CORE-020 shares with existing blocks: the build check of the IO blocks and
EXEC-012, and TIME-001's contract. The full theorem conjoins `spec_consistent_queue`'s body in
place of the five IO and EXEC lines repeated here. Wave W1 adds CORE-037's dead-arc report and
message on their reference witnesses as their own conjunct; the build-time B line that ties the
report to the net builder is wave W11's (CORE-037 B).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-- ✓ CORE-020 holds together with the build lines of the IO blocks, EXEC-012's build line and
TIME-001, on one builder: the reference transition builder, whose build check is the reference
builder `refBuild` that the IO and EXEC-012 blocks are stated over, and which agrees with
TIME-001's reference contract on timings. CORE-037 holds of the reference dead-arc report and
message. The skeleton of `spec_consistent_structure`. -/
@[evidence consistent CORE_020 TIME_001 IO_011 IO_012 IO_013 IO_014 EXEC_012 CORE_037]
theorem joint_core_structure_sketch {N A Tk : Type} [DecidableEq N] [ToString N] :
    (∃ (Build : Trans N → Option String) (F T : FireRel N) (Q : TimingContract)
      (QF : QFireRel N Tk) (TB : TBuilder N A),
      IO_011 Build F ∧ IO_012 IO_012_check Build F ∧ IO_013 Build F T ∧ IO_014 Build T ∧
      EXEC_012 Build QF ∧ TIME_001 Q ∧ CORE_020 TB ∧
      projBuild TB = Build ∧ TimingAgree TB Q) ∧
    (∃ (Rep : DeadArcReport String) (Msg : DeadArc String → String), CORE_037 Rep Msg) :=
  ⟨⟨refBuild, RefFire, refTimeoutOutcomeFire, refTimingQ, RefQFire, refTransBuild,
    IO_011_reference, IO_012_reference, IO_013_reference,
    refTimeoutOutcomeFire_eq_refTimedOutFire (N := N) ▸ IO_014_reference, EXEC_012_reference,
    TIME_001_reference, CORE_020_reference, projBuild_ref, refTransBuild_timingAgree⟩,
    ⟨_, _, CORE_037_reference⟩⟩

end Libpetri.Spec
