import Libpetri.Spec.Consistency
import Libpetri.Spec.Req.VER_001
import Libpetri.Spec.Req.VER_002
import Libpetri.Spec.Req.VER_005
import Libpetri.Spec.Req.VER_007
import Libpetri.Spec.Req.VER_011
import Libpetri.Spec.Req.VER_014
import Libpetri.Spec.Req.VER_015
import Libpetri.Spec.Req.VER_016
import Libpetri.Spec.Req.VER_019
import Libpetri.Spec.Req.VER_020
import Libpetri.Spec.Req.VER_025
import Libpetri.Spec.Req.NU_053

set_option linter.missingDocs true

/-!
# Consistency of the CORE requirements with the VER requirements (skeleton)

The target of this module is one theorem, `spec_consistent_ver`, that picks one witness for every
variable the CORE, IO, TIME and VER blocks share and shows that every block holds of it: the
reference firing relation `RefFire` for the CORE and IO blocks and as the yardstick of the
verifier's reachability claims, the reference timed step `RefTStep` for the TIME blocks and the
verifier's timed claims, one violation reading for VER-002, VER-003 and VER-014, and the phase
witnesses of VER-015 to VER-025. Each VER block of a wave adds its conjunct here, instantiated
by the same witness its own holds theorem uses.

This file is the skeleton of wave W1. `joint_core_ver_sketch` fixes the shape: the CORE firing
relation and the rest set of VER-014 are existentials of one statement, instantiated by the
reference witnesses, and the bounded witness phase of VER-025, whose model is over flat nets and
shares no variable with the others yet, is a separate conjunct. `VER_014_violates_agree` is the
first agreement lemma: with no conditional declaration the rest-set violations of VER-014, at the
reap-aware quiescence of the reference, are the conformance reference's `Violates`, which
decides the verdicts of the conformance corpus.

Wave W1 adds VER-002 on VER-014's rest set (one `S` for both, the agreement
`VER_002_deadlock_agree`), VER-001 over the same name type, the `QuiescentCount` constructor of
VER-002 (`VER_002_count`) over the same name type, and one conjunct for each of VER-005,
VER-007, VER-011, VER-015, VER-016, VER-019, VER-020 and NU-053, instantiated by the witness of
its own holds theorem. Those eight share no variable with the others yet: each is stated over its
own abstract function (an invariant finder, a semiflow encoder, a zone library, the bound phase,
the counter rules, the firing-bound phase, the siphon search, the colour-slot bound over the flat
rows), and the agreement conjuncts that tie them to one verifier pipeline are the W10 lines. NU-053
is here rather than in the ν sketch of wave W9 because its models are over flat rows. VER-003 (one `F` for CORE-022 and the
verifier's verdicts) is the next shared conjunct.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-- With no conditional declaration, VER-014's reference violations at the reference's reap-aware
quiescence are the conformance reference's `Violates` for `DeadlockFree` and `TerminatesAtSink`.
-/
theorem VER_014_violates_agree {N : Type} [DecidableEq N] (net : Reference.Net N)
    (sinks : List N) (m : N → Nat) :
    (Violates net (.deadlockFree sinks) m ↔
      refRestViol (ReapQuiescent net) .deadlockFree sinks [] m) ∧
    (Violates net (.terminatesAtSink sinks) m ↔
      refRestViol (ReapQuiescent net) .terminatesAtSink sinks [] m) :=
  VER_014_reference_violates net sinks [] m

/-- ✓ The CORE firing requirement CORE-022 and the VER requirements of waves W0 and W1 hold
together: the reference firing relation; one rest set for VER-014 and VER-002 with the reference
violations; the reference verified net and expansion of VER-001; the bounded witness phase of
VER-025 with its pipeline; and the reference P-invariant finder, semiflow encoder, zone library,
bound phase, counter rules, firing-bound phase and siphon search; the reference `QuiescentCount`
constructor; and the reference colour-slot bound of NU-053. The skeleton of
`spec_consistent_ver`. -/
@[evidence consistent CORE_022 VER_001 VER_002 VER_002_count VER_005 VER_007 VER_011 VER_014
  VER_015 VER_016 VER_019 VER_020 VER_025 NU_053]
theorem joint_core_ver_sketch {N : Type} [DecidableEq N] :
    (∃ (F : FireRel N) (S : StrandRel N) (V : RestViolRel N) (D : SafetyViolRel N)
        (VN : VerifiedNetFn N) (X : ExpandFn N),
      CORE_022 F ∧ VER_014 S V ∧ VER_002 S D ∧ VER_001 VN X) ∧
    (∃ B : CountBuild N, VER_002_count B) ∧
    (∃ (S : ScriptRel) (W : PhaseFn) (P : PipelineFn), VER_025 S W P) ∧
    (∃ I : InvFn, VER_005 I) ∧ (∃ E : SemiflowEnc, VER_007 E) ∧ (∃ Z : ZoneLib, VER_011 Z) ∧
    (∃ (C : LinCheckRel) (Dm : LinDemandFn) (Ph : LinPhaseRel), VER_015 C Dm Ph) ∧
    (∃ (I : CntInit) (R : CntRuleRel), VER_016 I R) ∧
    (∃ (C : FBRankingCheck) (Dl : FBDepthLoop) (P : FBPhaseFn), VER_019 C Dl P) ∧
    (∃ (Se : Ver020Search) (T : Ver020Trap) (C : Ver020Check), VER_020 Se T C) ∧
    (∃ (B : ColourSlotBound) (R : SlotReCheck) (Cr : ConsumerRule) (V : ColouredViolation),
      NU_053 B R Cr V) :=
  ⟨⟨RefFire, refStrand, refRestViol, refSafetyViol, refVerifiedNet, refVirtual,
      CORE_022_reference, VER_014_reference, VER_002_reference, VER_001_reference⟩,
    ⟨_, VER_002_count_reference⟩,
    ⟨ver025_script, Novel.FiringBound.witnessPhase, Novel.FiringBound.pipeline,
      VER_025_reference⟩,
    ⟨_, VER_005_reference⟩, ⟨_, VER_007_reference⟩, ⟨_, VER_011_reference⟩,
    ⟨_, _, _, VER_015_reference⟩, ⟨_, _, VER_016_reference⟩, ⟨_, _, _, VER_019_reference⟩,
    ⟨_, _, _, VER_020_reference⟩, ⟨_, _, _, _, NU_053_reference⟩⟩

end Libpetri.Spec
