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
import Libpetri.Spec.Req.VER_003
import Libpetri.Spec.Req.VER_004
import Libpetri.Spec.Req.VER_006
import Libpetri.Spec.Req.VER_010
import Libpetri.Spec.Req.VER_012
import Libpetri.Spec.Req.VER_013
import Libpetri.Spec.Req.VER_017
import Libpetri.Spec.Req.VER_018
import Libpetri.Spec.Req.VER_021
import Libpetri.Spec.Req.VER_022
import Libpetri.Spec.Req.VER_023
import Libpetri.Spec.Req.VER_024
import Libpetri.Spec.Req.NU_010_ac6
import Libpetri.Spec.Req.NU_051_carrier
import Libpetri.Spec.Req.NU_052_split
import Libpetri.Spec.Req.NU_053_dispatch
import Libpetri.Spec.Req.NU_055_steps

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
is here rather than in the ν sketch of wave W9 because its models are over flat rows.

Wave W10 adds the verifier pipeline. The first conjunct now also carries the verdict contract of
VER-003 and the environment verdicts of VER-006 on the same firing relation `F`, the same safety
violations `D` and a verified-net function `abs` that builds exactly VER-001's verified net `VN`
(one `abs` for VER-003 and for VER-006 under `Ignore`); the timed abstraction of VER-004 on the
same `F`; and the XOR analysis of VER-021 on VER-001's expansion `X`. The name type now needs an
order and a hash, as the reference verifier does. VER-022's open-net verifier is a conjunct of its
own over `String` names, with the reference firing relation and VER-014's rest set at that type.
The other W10 blocks (the in-flight split, the state-class graph and its key, Route B, the
enumeration and its cache, the order lines of the pipeline, the timed check, the reduction, and
the ν pipeline lines of NU-010, NU-051, NU-052, NU-053 and NU-055) are one conjunct each,
instantiated by the witness of their own holds theorems, with the offers of VER-015's order,
VER-020, VER-022, NU-051's carriers and NU-053's dispatch (`Ver015OrderCovers`,
`Ver020GuardCovers`, `Ver022Covers`, `Nu051CarrierCovers`, `Nu053DispatchCovers`) next to their
blocks. The order lines share one step list: the bound dispatch of VER-015 and the ν dispatch of
NU-053 carry the same step names as the list VER-018's and VER-019's order lines read, the
runtimes' `rtStepNames`, so one pipeline meets every order line at once. The four blocks of
VER-013 (name order, timeouts and clamp, reply classification, and the pipeline under a solver
and a stop) are one conjunct, over the runner `runPipeline` every order line runs on.
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

/-- ✓ The CORE firing requirement CORE-022 and the VER requirements hold together. Example: the
reference firing relation; one rest set for VER-014 and VER-002 with the reference violations;
the reference verified net and expansion of VER-001, the verified-net function that builds that
net, and the reference verifier over it (VER-003), the reference environment verifier (VER-006),
the reference timed step (VER-004) and the reference XOR analysis on that expansion (VER-021);
the bounded witness phase of VER-025 with its pipeline; the reference P-invariant finder,
semiflow encoder, zone library, bound phase, counter rules, firing-bound phase and siphon search;
the reference `QuiescentCount` constructor; the reference colour-slot bound of NU-053; and the
witnesses of the W10 pipeline blocks. The skeleton of `spec_consistent_ver`. -/
@[evidence consistent CORE_022 VER_001 VER_002 VER_002_count VER_003 VER_004_timed VER_004_split
  VER_005 VER_006 VER_006_premise VER_006_quiescent VER_006_arrivals VER_006_verdict VER_007
  VER_010 VER_010_persist VER_010_key VER_011 VER_012 VER_012_build VER_013_order VER_013_args
  VER_013_classify VER_013_stop VER_014 VER_015
  VER_015_order VER_016 VER_017 VER_017_cache VER_018 VER_018_order VER_019 VER_019_order VER_020
  VER_020_guard VER_021 VER_022_meets VER_022_closure VER_022 VER_023 VER_023_graph VER_024
  VER_024_select VER_024_route VER_025 NU_010_unknownMint NU_051_colours NU_051_carrier
  NU_052_split NU_053 NU_053_dispatch NU_055_refusal]
theorem joint_core_ver_sketch {N : Type} [LinearOrder N] [Hashable N] :
    (∃ (F : FireRel N) (S : StrandRel N) (V : RestViolRel N) (D : SafetyViolRel N)
        (VN : VerifiedNetFn N) (X : ExpandFn N) (abs : Verifier.Abs N)
        (Dec : Verifier.Decider N) (envAbs : EnvMode → List N → Verifier.Abs N)
        (Denv : EnvDecider N) (R : TRel N) (A : XorAnalysis N),
      CORE_022 F ∧ VER_014 S V ∧ VER_002 S D ∧ VER_001 VN X ∧
      (∀ o Y φ m0, abs o Y φ m0 = .ok ⟨{ Y with net := VN Y.net m0 }, φ, m0⟩) ∧
      VER_003 F D abs Dec ∧ VER_006_verdict F D abs Denv ∧ (∀ envs, envAbs .ignore envs = abs) ∧
      (∀ mode envs, VER_003 F D (envAbs mode envs) (Denv mode envs)) ∧
      VER_004_timed R F ∧ VER_021 X A) ∧
    (∃ B : CountBuild N, VER_002_count B) ∧
    (∃ (S : ScriptRel) (W : PhaseFn) (P : PipelineFn), VER_025 S W P) ∧
    (∃ I : InvFn, VER_005 I) ∧ (∃ E : SemiflowEnc, VER_007 E) ∧ (∃ Z : ZoneLib, VER_011 Z) ∧
    (∃ (C : LinCheckRel) (Dm : LinDemandFn) (Ph : LinPhaseRel), VER_015 C Dm Ph) ∧
    (∃ (I : CntInit) (R : CntRuleRel), VER_016 I R) ∧
    (∃ (C : FBRankingCheck) (Dl : FBDepthLoop) (P : FBPhaseFn), VER_019 C Dl P) ∧
    (∃ (Se : Ver020Search) (T : Ver020Trap) (C : Ver020Check) (R : StructRouteFn N),
      VER_020 Se T C ∧ VER_020_guard R ∧ Ver020GuardCovers R) ∧
    (∃ (B : ColourSlotBound) (R : SlotReCheck) (Cr : ConsumerRule) (V : ColouredViolation),
      NU_053 B R Cr V) ∧
    (∃ (Sp : SplitFn N) (P : SplitPlanFn N), VER_004_split Sp P) ∧
    (∃ Rc : OpenReach, VER_006 Rc) ∧ (∃ Pc : PremiseCheck, VER_006_premise Pc) ∧
    (∃ Q : OpenQuiescent, VER_006_quiescent Q) ∧ (∃ Ac : ArrClosure, VER_006_arrivals Ac) ∧
    (∃ (co : Novel.TimedScg.TNet → List Nat → Option (List Nat)) (surv : SurvTest)
        (same : Novel.TimedScg.TNet → Novel.TimedScg.Cls → Novel.TimedScg.Cls → Prop) (St : ScgStep),
      VER_010_key co same ∧ VER_010_persist surv ∧ VER_010 St) ∧
    (∃ (G : NameGraph) (B : RBBuild), VER_012 G ∧ VER_012_build B) ∧
    (∃ (lt : Ver013.NameLt) (B : Ver013.Budgets) (Cl : Ver013.Clamp) (C : Ver013.Classify)
        (RP : Ver013.Runner (Verifier.Query N)) (Fin : Ver013.Finisher),
      VER_013_order lt ∧ VER_013_args B Cl ∧ VER_013_classify C ∧ VER_013_stop RP Fin) ∧
    (∃ (Bd : BoundDispatch) (Nd : NuDispatch) (names : List String) (seG fbG : FBGate)
        (W : FBWrap),
      VER_015_order Bd ∧ Ver015OrderCovers Bd ∧ NU_053_dispatch Nd ∧ Nu053DispatchCovers Nd ∧
      VER_018_order names seG ∧ VER_019_order names seG fbG W ∧
      Bd.map Verifier.GStep.name = names ∧ Nd.map Verifier.GStep.name = names) ∧
    (∃ (G : EnumGateFn N) (Rt : Verifier.Graph.GraphRoute N N String)
        (Dd : EnumDispatchFn String), VER_017 G Rt Dd) ∧
    (∃ (Lk : CacheLookupFn N) (Cq : CacheQueryFn N N N) (Rd : CacheReadFn N String),
      VER_017_cache Lk Cq Rd) ∧
    (∃ (S : SESearch) (T : SETrapFn) (Xc : SEIndCheck) (P : SEPhaseFn) (W : SEWrap),
      VER_018 S T Xc P W) ∧
    (∃ (F : FireRel String) (S : StrandRel String) (Vr : RestViolRel String)
        (M : OpenNet.MeetsRel String) (Cl : OpenNet.CloseFn) (Ov : OpenNet.OpenVerifier),
      CORE_022 F ∧ VER_014 S Vr ∧ VER_022_meets M S ∧ VER_022_closure Cl ∧
      VER_022 F Cl M S Ov ∧ Ver022Covers F Cl M Ov) ∧
    (∃ (G : TimedGateFn N) (Oc : TimedOutcomeFn N N) (An : TimedAnnotFn N) (Sc : TimedSuccFn),
      VER_023 G Oc An ∧ VER_023_graph Sc) ∧
    (∃ (Sel : Ver024.SelFn) (U : Ver024.ReduceFn N) (key : Ver024.CacheKeyFn N N N),
      VER_024 Sel ∧ VER_024_select Sel ∧ VER_024_route U key) ∧
    (∃ Mn : MintCall → MintAnswer, NU_010_unknownMint Mn) ∧
    (∃ (Cs : ColourSet) (Cp : CarrierPipeline N),
      NU_051_colours Cs ∧ NU_051_carrier Cp ∧ Nu051CarrierCovers Cp) ∧
    (∃ (M : NuSetupFn N) (B : InFlightBase), NU_052_split M B) ∧
    (∃ Ag : AlignGateFn, NU_055_refusal Ag) :=
  ⟨⟨RefFire, refStrand, refRestViol, refSafetyViol, refVerifiedNet, refVirtual, inertAbs,
      Verifier.refVerify inertAbs, ver006EnvAbs, refEnvVerify, RefTStep, refXor,
      CORE_022_reference, VER_014_reference, VER_002_reference, VER_001_reference,
      fun _ _ _ _ => rfl, VER_003_reference inertAbs, VER_006_verdict_reference,
      ver006EnvAbs_ignore, ver006_ver003, VER_004_timed_reference, VER_021_reference⟩,
    ⟨_, VER_002_count_reference⟩,
    ⟨ver025_script, Novel.FiringBound.witnessPhase, Novel.FiringBound.pipeline,
      VER_025_reference⟩,
    ⟨_, VER_005_reference⟩, ⟨_, VER_007_reference⟩, ⟨_, VER_011_reference⟩,
    ⟨_, _, _, VER_015_reference⟩, ⟨_, _, VER_016_reference⟩, ⟨_, _, _, VER_019_reference⟩,
    ⟨_, _, _, _, VER_020_reference, VER_020_guard_reference, refStructRoute_covers⟩,
    ⟨_, _, _, _, NU_053_reference⟩,
    ⟨_, _, VER_004_split_reference⟩,
    ⟨_, VER_006_reference⟩, ⟨_, VER_006_premise_reference⟩, ⟨_, VER_006_quiescent_reference⟩,
    ⟨_, VER_006_arrivals_reference⟩,
    ⟨_, _, _, _, VER_010_key_reference, VER_010_persist_reference, VER_010_reference⟩,
    ⟨_, _, VER_012_reference, VER_012_build_reference⟩,
    VER_013_joint,
    ⟨_, _, _, _, _, _, VER_015_order_reference, ver015OrderCovers_reference,
      NU_053_dispatch_reference, nu053DispatchCovers_reference, VER_018_order_reference,
      VER_019_order_reference, refBoundDispatch_names, refNuDispatch_names⟩,
    ⟨_, _, _, VER_017_reference⟩,
    ⟨_, _, _, VER_017_cache_reference⟩,
    ⟨_, _, _, _, _, VER_018_reference⟩,
    ⟨RefFire, refStrand, refRestViol, OpenNet.refMeets, OpenNet.refClose, OpenNet.refOpenVerify,
      CORE_022_reference, VER_014_reference, VER_022_meets_reference, VER_022_closure_reference,
      VER_022_reference, ver022_ref_covers⟩,
    ⟨_, _, _, _, VER_023_reference, VER_023_graph_reference⟩,
    ⟨_, _, _, VER_024_reference, VER_024_select_reference, VER_024_route_reference⟩,
    ⟨_, NU_010_unknownMint_reference⟩,
    ⟨_, _, NU_051_colours_reference, NU_051_carrier_reference, nu051c_ref_covers⟩,
    ⟨_, _, NU_052_split_reference⟩,
    ⟨_, NU_055_refusal_reference⟩⟩

end Libpetri.Spec
