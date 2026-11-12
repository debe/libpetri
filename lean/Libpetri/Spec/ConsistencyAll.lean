import Libpetri.Spec.ConsistencyQueue
import Libpetri.Spec.ConsistencyStructure
import Libpetri.Spec.ConsistencyCompose
import Libpetri.Spec.ConsistencyNu
import Libpetri.Spec.ConsistencyVer
import Libpetri.Spec.ConsistencyExport
import Libpetri.Spec.ConsistencyEvents
import Libpetri.Spec.Req.VER_004_exec
import Libpetri.Spec.Req.EVT_032_B
import Libpetri.Spec.Req.NU_054_fail
import Libpetri.Spec.Req.MOD_040_b
import Libpetri.Spec.Req.MOD_051
import Libpetri.Spec.Req.CORE_037_B
import Libpetri.Spec.Req.CORE_011_B
import Libpetri.Spec.Req.TIME_012_nu
import Libpetri.Spec.Req.NU_050_timed

set_option linter.missingDocs true

/-!
# One model for the whole specification

`spec_consistent_all` is the single consistency theorem of the migration (wave W11). It joins the
area theorems (`spec_consistent_queue`, `joint_core_structure_sketch`, `spec_consistent_compose`,
`joint_nu_sketch`, `joint_core_ver_sketch`, `spec_consistent_exec_sketch`, `joint_events_sketch`
and `joint_export_sketch`) into one statement whose shared witnesses are existentials of that one
statement, not of each area theorem. Each area keeps its private parameters inside its area
predicate (`QueueSpec`, `StructureSpec`, `ComposeSpec`, `NuSpec`, `VerSpec`, `ExportSpec`,
`StoreSpec`, and `ExecSpec` and `EventsSpec` from `ConsistencyEvents.lean`); what the areas share
is a parameter of `AllSpec`, read by every area that names it:

* **One build check** `Build`: the IO and EXEC-012 build lines of the queue area, the transition
  builder of the structure area (`projBuild TB = Build`), the composition functions and the build
  script, and the ν builder (`NuBuildExtends`).
* **One firing relation** `F` and **one timed-out firing relation** `Tm`: the CORE and IO blocks
  of the queue, structure, composition and ν areas, and the yardstick of the verifier's
  reachability claims.
* **One timing contract** `Q` (TIME-001, the queue and structure areas) and **one timed step**
  `R` (the TIME blocks, the composition's clock lines, VER-004's timed abstraction, and the
  executor's atomic agreement `AtomicAgrees`).
* **One queue firing** `QF`: the queue blocks, the structure blocks (CORE-050's action firing is
  stated over it), the ν blocks (`NuRestrictsTo`) and the executor (`QueueAgrees`). The token
  type is `Stamped V`, the tokens the ν blocks stamp, so the ν area and the executor share it.
* **One output validator** `Vd`: IO-015 in the queue area, and the executor's settlement
  (`ValidatedBy E Vd`) in the executor area.
* **One ready order** `O`: EXEC-002 and CONC-023 in the queue area, and the pass order of the
  executor, `PassOrder O`: the transitions a pass offers, in the order it offers them, are `O`'s
  order of the timed view at the cycle reading. So EXEC-002's order is the order EXEC-002's cycle
  companion, TIME-014 and CONC-002 read.
* **One transition builder** `TB` (structure and composition), **one binding pair** `Bind`,
  `BindMap` (CORE-042 and MOD-051's binding block), **one verification entry check** `Ve`
  (CORE-043, and the check MOD-051's `verify` runs), **one instantiation** `Inst`, **one build
  script** `S` and **one set of correspondence operations** `Co` (the composition area, MOD-031's
  context block and MOD-051), **one environment verifier** `Denv` (VER-006, VER-003 under every
  environment mode, CORE-037's verifier block and MOD-051), and **one exporter** `Ex` (the EXP
  blocks and MOD-040's block (b)).
* **One executor** `E` with its expiry handling `X`, and **one executor with events** `W` that
  steps as it (`W.erase = E`), with its action log and await answer: the W5 and W7 blocks, the
  replay agreement of EVT-032 (block B) on `W`, and NU-054's fail block on `E`.
* **One snapshot** `Snap`: CORE-073's snapshot function in the structure area, and, over string
  place names, the payload of every marking snapshot the executor with events reports
  (`W = evt014With (fun C M => Snap (evt014_restrictFin C.X.net.places M))`), so EVT-014's
  snapshot is CORE-073's, not a second form.

The theorem has three parts, one per place type a block is stated at:

1. **Every place type with a linear order, a hash and a printer** (the verifier needs the first
   two, the build messages the third): `AllSpec` with the reference witnesses, for every naming
   model, token-type reader, verification facility and place printer.
2. **String place names**: the same, with the naming model `strNaming` (so the naming binder of
   part 1 is not vacuous), and the blocks stated only over strings: EVT-014, CORE-037's events
   and verifier blocks (each over a wrapper of the shared executor and verifier that adds the
   dead-arc warnings), MOD-051's `verify` with its coverage, and the snapshot link above. The
   shared executor with events `W` and the shared verifier `Denv` are the ones that do not report
   dead arcs; the ones that do are the wrappers (`core037bExec W` and `core037bVerify Denv` in the
   witness), and of the event blocks only EVT-013 is shown to carry over to the wrapper
   (`core037b_evt013`).
3. **Flat place identities** (`PlaceId`, where the verifier's in-flight split lives): the queue,
   verifier and executor areas with the L5 agreement conjunct `CountAgrees E` and block B of
   VER-004 on the shared executor and the shared split `Sp` of `VER_004_split`
   (`VER_004_exec_of`).

The area projections (`queueSpec_sound`, `structureSpec_sound`, `composeSpec_sound`,
`nuSpec_sound`, `verSpec_sound`, `exportSpec_sound`, and `execSpec_sketch` in
`ConsistencyEvents.lean`) check by repacking that every area predicate gives its area theorem's
statement, so an area theorem that gains a conjunct the area predicate lacks fails the build here.

Not joined (each is a conjunct over its own relation, instantiated by the witness of its holds
theorem): TIME-012's ν clause (`TIME_012_nu`, over the timed ν step), NU-050's timed line
(`NU_050_timed` with its coverage, over Route B's timed semantics) and CORE-011's epoch slice
(`CORE_011_B`, over tokens with a factory stamp). No agreement conjunct yet ties these three
relations to the shared executor or the shared ν firing. In particular CORE-011 block B's line 3
holds of its witness by the guard the epoch slice adds (`core011b_expireOk`), not by anything the
shared executor `E` does, so `E` is not constrained by it here. TIME-012's ν clause and NU-050's
timed lines share one relation type (`RBTRel` abbreviates `NuTRel`) but not one witness. The
NU-054 failure block has no link that the shared configuration's relay check is `relayVerdict`. Also open: the link that a built
configuration has a sound `timeoutOut` (EXEC-022's premise `exec022_OutcomeSound`), and a context
link between MOD-031's resolved context and CORE-060's context `Cx`.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Novel.TimedScg (Timing)

/-! ## The area predicates -/

section Areas

/-- The queue area: the body of `spec_consistent_queue` with the build check, the firing
relations, the timing contract, the ready order, the timed step, the queue firing and the output
validator as parameters. -/
def QueueSpec {N Tk : Type} [DecidableEq N] [ToString N] (Build : Trans N → Option String)
    (F Tm : FireRel N) (Q : TimingContract) (O : ReadyOrder) (R : TRel N) (QF : QFireRel N Tk)
    (Vd : OutputValidator N) : Prop :=
  ∃ (C : TimingCompile) (I : Init N) (Ops : MarkingOps N Tk) (EC : EnableCheck N),
    (CORE_022 F ∧ CORE_030 F ∧ CORE_031 F ∧ CORE_032 F ∧ CORE_033 F ∧ CORE_034 F ∧
      CORE_035 F ∧ CORE_036 F ∧ IO_001 F ∧ IO_002 F ∧ IO_003 F ∧ IO_004 F ∧ IO_005 F ∧
      IO_010 F ∧ IO_011 Build F ∧ IO_012 IO_012_check Build F ∧ IO_013 Build F Tm ∧
      IO_014 Build Tm) ∧
    ((∃ K, IO_007 K) ∧ IO_015 Vd ∧
      (∃ (E : BranchEnum N) (A : AllPlaces N), IO_016 E ∧ IO_017 A)) ∧
    (TIME_001 Q ∧ Q.earliest = Novel.TimedScg.Timing.earliest ∧
      Q.latest = Novel.TimedScg.Timing.latest ∧ CONC_024 Q C) ∧
    (EXEC_002 O ∧ CONC_023 O) ∧
    ProjectsTo R F ∧ FramesMarking R ∧ time012_FramesClock R ∧ Covers R ∧
    CoversReap R ∧ CoversDelay R ∧ TIME_002 R ∧ TIME_003 R ∧ TIME_004 R ∧ TIME_005 R ∧
    TIME_006 R ∧ TIME_010 R ∧ TIME_011 R ∧ TIME_012 R ∧ TIME_013 R ∧ TIME_015 R ∧
    CONC_005 R ∧
    QProjectsTo QF F ∧ QCovers QF F ∧
    EXEC_010 QF ∧ EXEC_012 Build QF ∧ EXEC_013 QF ∧ EXEC_020 QF ∧
    CORE_010 QF ∧ CORE_013 QF ∧ CORE_072 I R QF ∧ CORE_070 Ops ∧
    (∀ (Ty V : Type) (ty : N → Ty) (val : Tk → Option V) (HasType : Ty → V → Prop),
      CORE_003 ty val HasType QF) ∧
    CONC_004 EC ∧ CONC_008 EC ∧
    (∃ (S : MarkingOps PlaceId Colour) (X : Materialiser S) (P : ConsumeProgram S),
      CORE_070 S ∧ CONC_022 S ∧ CONC_025 S X ∧ CONC_021 S P)

/-- The structure area: the body of `joint_core_structure_sketch` with the build check, the
firing relations, the timing contract, the queue firing, the transition builder, the binding
pair, the verification entry check and the snapshot function as parameters. -/
def StructureSpec {N A Tk Val : Type} [DecidableEq N] [ToString N] (val : Tk → Val)
    (Build : Trans N → Option String) (F Tm : FireRel N) (Q : TimingContract)
    (QF : QFireRel N Tk) (TB : TBuilder N A)
    (Bind BindMap : BuiltNet N A → (String → Option (Act A)) → BuiltNet N A)
    (Ve : BuiltNet N A → Option String) (Snap : FinQ String Tk → QSnap String Tk) : Prop :=
  ∃ (NB : NetBuilder TB) (BA : BuilderApi TB) (C : BuiltNet N A → Option String)
    (Cmp : (Trans N → Bool) → Reference.Net N → CompiledNet N) (L : Nat → BitmapLayout N)
    (M : PlaceKeyed N Tk) (Rep : DeadArcReport String) (Msg : DeadArc String → String)
    (AF : ActFireRel N Tk) (I : A → ActionRel N Tk) (interp : Act A → ActionRel N Tk)
    (isPT : Act A → Bool) (pt : Nat → Act A) (Fork : ActionFn N Tk)
    (Tf : TransformFn N Tk Val → ActionRel N Tk) (produce : N → Val → ActionRel N Tk)
    (Cx : Ctx N Tk Val) (K : TokenFactory Val) (Restore : QSnap String Tk → QMarking String Tk)
    (Seed : Option (QSnap String Tk) → QSnap String Tk → Except String (QMarking String Tk))
    (Rs : TimedNet String → QSnap String Tk → Nat → TSt String),
    IO_011 Build F ∧ IO_012 IO_012_check Build F ∧ IO_013 Build F Tm ∧ IO_014 Build Tm ∧
    EXEC_012 Build QF ∧ TIME_001 Q ∧ CORE_020 TB ∧ CORE_021 TB ∧ CORE_040 TB NB ∧
    CORE_041 TB NB BA ∧ EXEC_042_build TB NB ∧ CORE_042 Bind BindMap ∧ CORE_043 C Ve ∧
    CONC_007 Cmp ∧
    (∀ ws, PERF_030 ws (L ws)) ∧ CORE_002 M ∧ CORE_037 Rep Msg ∧
    projBuild TB = Build ∧ TimingAgree TB Q ∧
    (∀ inp b, NB inp = .ok b → b.FromBuilder TB) ∧
    (∀ b r, b.FromBuilder TB → (Bind b r).FromBuilder TB ∧ (BindMap b r).FromBuilder TB) ∧
    (∀ ws n, (List.range n.transitions.length).flatMap ((L ws).masks n) =
      (Cmp (fun _ => false) n).maskWords ws) ∧
    EXEC_010 QF ∧ QProjectsTo QF F ∧ QCovers QF F ∧ CORE_050 QF AF ∧
    EndsByActionOrTimeout QF AF Tm ∧ CORE_051 interp isPT TB pt ∧ CORE_052 val Fork ∧
    CORE_053 val Tf ∧ CORE_054 val produce ∧ CORE_060 val Cx ∧ CORE_061 val Cx ∧
    CORE_062 val Cx ∧ CORE_063 val Cx ∧ CORE_011 K ∧ CORE_073 Snap Restore Seed ∧
    CORE_073_T Restore Rs ∧
    (∀ f, (∀ t δ w v, f t δ (.ok (w, v)) → Built Cx t (w.map fun x => (x.1, val x.2))) →
      ThroughCtx Cx val (Tf f)) ∧
    ThroughCtx Cx val (ActionFn.rel Fork) ∧
    (∀ (d : TransDef N A) Mq δ e Mq',
      TagFire AF I d Mq δ e Mq' ↔ AF (interp d.action) d.toTrans Mq δ e Mq') ∧
    (∀ p v, produce p v = core054_ctxProduce Cx val p v) ∧
    (∀ X s now0, Rs X s now0 = TSt.init X (qCount (Restore s)) now0)

/-- The composition area: the body of `spec_consistent_compose` with the build check, the firing
relations, the timed step, the transition builder, the instantiation, the build script and the
correspondence operations as parameters. -/
def ComposeSpec {N A T Rr : Type} [DecidableEq N] [ToString N] [DecidableEq T] [ToString T]
    (Nm : Naming N) (tyOf : N → T) (Fv : BuiltNet N A → Rr) (Build : Trans N → Option String)
    (F Tm : FireRel N) (TR : TRel N) (TB : TBuilder N A) (Inst : InstFn N A) (S : ScriptFn N A)
    (Co : CorrOps N A) : Prop :=
  ∃ (NB : NetBuilder (defsTB N A)) (SB : SubnetMake N A)
    (sq : Act A → Act A → Act A) (cm : CorrMergeFn N A) (Mg : MergeFn N A)
    (C : ComposeFn N A) (Au : AutoFn N A) (D : DirectFn N A)
    (Rb : RebindFn N A) (Fz : FuseFn N A) (FN : FromNetFn N A) (Bi : InstBindFn N A)
    (PA : PortAsFn N A T) (G : ComposedNet N A → Rr)
    (tbl : Card → Card → Option Card) (res : List (String × String) → String → Option String)
    (acc : SubnetAccess) (vw : Mod041.SubnetView),
    (CORE_022 F ∧ CORE_030 F ∧ CORE_031 F ∧ CORE_032 F ∧ CORE_033 F ∧ CORE_034 F ∧
      CORE_035 F ∧ CORE_036 F ∧ IO_001 F ∧ IO_002 F ∧ IO_003 F ∧ IO_004 F ∧ IO_005 F ∧
      IO_010 F ∧ IO_011 Build F ∧ IO_012 IO_012_check Build F ∧ IO_013 Build F Tm ∧
      IO_014 Build Tm ∧ CORE_020 TB) ∧
    (MOD_001 NB SB ∧ MOD_003 NB SB ∧ MOD_004 Nm SB Inst ∧ MOD_005 NB SB ∧ MOD_006 NB SB) ∧
    (MOD_010 Nm Inst ∧ MOD_011 Nm Inst ∧ MOD_011_typed tyOf PA ∧ MOD_013 Nm Inst ∧
      MOD_014 FN ∧ MOD_030 Bi ∧ MOD_031 Co) ∧
    (MOD_020 tyOf Build Mg C ∧ MOD_021_table tbl ∧ MOD_021 Build sq cm timingStr Mg ∧
      MOD_022 tyOf Build C ∧ MOD_024 Nm Build C Au ∧ MOD_025 Nm tyOf D) ∧
    (MOD_012 Nm S F ∧ MOD_012_clock Nm S TR ∧ MOD_023 Nm Build S ∧ MOD_026_resolve res ∧
      MOD_026 Nm S Rb ∧ MOD_027 Nm tyOf Build S ∧ MOD_050 Fv G ∧ MOD_061 Build Fz) ∧
    (MOD_040 acc ∧ MOD_041 vw) ∧
    projBuild TB = Build ∧ InstFiresAsBody Nm Inst F ∧
    (CORE_040 (defsTB N A) NB ∧
      ∀ ops : List (BOp (defsTB N A)),
        (∀ x, BOp.trans x ∈ ops → Build ((defsTB N A).defOf x).toTrans = none) →
        BuiltAgree ((S (ops.map Op.ofBOp)).map (·.toBuiltNet)) (NB (NetIn.ofOps ops))) ∧
    ScriptRuns Build C Au D S ∧
    (cm = Co.merge ∧
      ∀ (Sd : SubnetDef N A) p I, Inst Sd p = .ok I →
        I.defs = Sd.defs.map (Co.pass (Nm.pre p) (preS p))) ∧
    (∀ I m I', Bi I m = .ok I' →
      I'.defs = I.defs.map fun d => Co.rebind d ((instLook I.pfx m d.core.name).getD d.action)) ∧
    (ProjectsTo TR F ∧ FramesMarking TR ∧ time012_FramesClock TR)

/-- The ν area: the body of `joint_nu_sketch` with the build check, the firing relation and the
queue firing as parameters. -/
def NuSpec {N V : Type} [DecidableEq N] [ToString N] (Build : Trans N → Option String)
    (F : FireRel N) (QF : QFireRel N (Stamped V)) : Prop :=
  ∃ (MB : List (N × KeyFn V String) → Option String)
    (NB : NuTrans N (KeyFn V String) → Option String) (NF : NuFireRel N V String)
    (S : MatchSelect String) (I : NameImpl) (NC : NuEnableCheck N V String) (Mi : MintSys)
    (Vs : ScopeCheck) (D : Nat → String → Prop) (Cl : Classifier),
    CORE_022 F ∧ IO_011 Build F ∧ EXEC_010 QF ∧ EXEC_012 Build QF ∧
    QProjectsTo QF F ∧ QCovers QF F ∧
    NU_020_build MB NB ∧ NU_020_enable NF ∧ NU_020_take NF ∧ NU_020_frame NF ∧ NU_022 S ∧
    NU_001 I ∧ NU_001_rename NF ∧ NU_021 NF ∧ NU_054_build NB ∧ NU_054_check NF ∧
    CONC_004 NC.base ∧ CONC_008 NC.base ∧ CONC_008_nu NC ∧
    NU_010_unique Mi ∧ NU_010_replay Mi ∧ NU_011_format Mi Vs ∧ NU_011_lineage Mi Vs ∧
    NU_011_default D ∧ NU_051 Cl ∧ NU_010_classify Cl ∧ NU_054_verifier Cl ∧
    NuRestrictsTo NF QF ∧ NuBuildExtends NB Build ∧ NuSelectsBy NF S ∧ NuCovers NF ∧
    (∀ a b : String, I.lt (I.ofValue a) (I.ofValue b) ↔ a < b) ∧
    NuChecksFirings NF NC ∧ MintTotal Mi ∧ DefaultUnfixed D ∧ (∀ k s, D k s → Vs s = true)

/-- The verifier area: the body of `joint_core_ver_sketch` with the firing relation, the timed
step, the environment verifier and the in-flight split (with its plan) as parameters. -/
def VerSpec {N : Type} [LinearOrder N] [Hashable N] (F : FireRel N) (R : TRel N)
    (Denv : EnvDecider N) (Sp : SplitFn N) (Pl : SplitPlanFn N) : Prop :=
  (∃ (S : StrandRel N) (V : RestViolRel N) (D : SafetyViolRel N)
      (VN : VerifiedNetFn N) (X : ExpandFn N) (abs : Verifier.Abs N)
      (Dec : Verifier.Decider N) (envAbs : EnvMode → List N → Verifier.Abs N)
      (A : XorAnalysis N),
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
  VER_004_split Sp Pl ∧
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
  (∃ Ag : AlignGateFn, NU_055_refusal Ag)

/-- The export area: the body of `joint_export_sketch` with the exporter as a parameter. -/
def ExportSpec (Ex : Exporter) : Prop :=
  ∃ (Em : Emitter) (L : Card → Option String) (TL : TransLabeller) (C : PlaceClassifier String),
    ExportAgrees Ex Em L TL C ∧
    EXP_001 Ex ∧ EXP_002 Ex ∧ EXP_003 Ex ∧ EXP_004 Ex ∧ EXP_005 Em ∧ EXP_006 L ∧
    EXP_007_label TL ∧ EXP_007_config Ex ∧ EXP_008 C ∧ EXP_012 Em ∧ EXP_013 Ex ∧
    EXP_014 Ex ∧ EXP_016 Ex ∧ EXP_017 Ex ∧ EXP_018 Ex ∧
    ∀ (t : String) (R : List String) (o : OutTree) (o' : Out String), o.toOut = some o' →
      (Em t R o).edges.filterMap XEdge.placeTarget = outPlaces o'

/-- The store part of the event area: the store-tier conjuncts of `joint_events_sketch` over the
executor events `NetEvent N T`, with place names by `pn`. -/
def StoreSpec {N T : Type} [DecidableEq N] [DecidableEq T] (pn : N → String) : Prop :=
  (∃ (Smem : StoreObs (NetEvent N T)) (H : QueryHelpers (NetEvent N T))
      (L : LogDecorator (NetEvent N T)),
    EVT_020 Smem ∧ EVT_021 Smem ∧ EVT_030 (NetEvent.toShape pn) H ∧
    EVT_023 NetEvent.kind L ∧ EVT_020 (L.over Smem)) ∧
  (∃ Snoop : StoreObs (NetEvent N T), EVT_020 Snoop ∧ EVT_022 Snoop) ∧
  (∃ Sdbg : StoreObs (NetEvent N T), EVT_020 Sdbg ∧ EVT_024 10000 Sdbg) ∧
  (∃ Udbg : SubSem (NetEvent N T), EVT_024_B Udbg) ∧
  (∃ Upy : SubSem (NetEvent N T), EVT_031 Upy) ∧
  (∃ C : ArchiveCodec String (NetEvent N T), EVT_025 C) ∧
  (∃ call : CacheCall N (NetEvent N T), EVT_032 NetEvent.replayView call)

/-- **One ready order**: the transitions a pass of the executor offers, in the order it offers
them (`readyOrder`, read by EXEC-002's cycle companion, TIME-014 and CONC-002), are the order `O`
gives the timed view at the cycle reading, mapped back to the declared transitions. -/
def PassOrder {N T : Type} [DecidableEq N] (O : ReadyOrder) : Prop :=
  ∀ (C : Cfg N T) (s : XSt N T),
    readyOrder C s =
      (O (ReadyIn.ofTSt C.X C.prio (viewAt s s.cyc) C.X.net.transitions)).filterMap
        (C.X.net.transitions[·]?)

end Areas

/-! ## The area projections

Each area predicate gives its area theorem's statement, by repacking. If an area theorem gains a
conjunct its area predicate lacks, the projection no longer type-checks. -/

section Projections

/-- The queue area gives `spec_consistent_queue`. -/
theorem queueSpec_sound {N Tk : Type} [DecidableEq N] [ToString N]
    (h : ∃ (Build : Trans N → Option String) (F Tm : FireRel N) (Q : TimingContract)
      (O : ReadyOrder) (R : TRel N) (QF : QFireRel N Tk) (Vd : OutputValidator N),
      QueueSpec Build F Tm Q O R QF Vd) :
    type_of% (@spec_consistent_queue N Tk _ _) := by
  obtain ⟨Build, F, Tm, Q, O, R, QF, Vd, C, I, Ops, EC, h1, ⟨hK, hV, hE⟩, rest⟩ := h
  exact ⟨Build, F, Tm, Q, C, O, R, QF, I, Ops, EC, h1, ⟨hK, ⟨Vd, hV⟩, hE⟩, rest⟩

/-- The structure area gives `joint_core_structure_sketch`. -/
theorem structureSpec_sound {N A Tk Val : Type} [DecidableEq N] [ToString N] (val : Tk → Val)
    (h : ∃ (Build : Trans N → Option String) (F Tm : FireRel N) (Q : TimingContract)
      (QF : QFireRel N Tk) (TB : TBuilder N A)
      (Bind BindMap : BuiltNet N A → (String → Option (Act A)) → BuiltNet N A)
      (Ve : BuiltNet N A → Option String) (Snap : FinQ String Tk → QSnap String Tk),
      StructureSpec val Build F Tm Q QF TB Bind BindMap Ve Snap) :
    type_of% (@joint_core_structure_sketch N A Tk Val _ _ val) := by
  obtain ⟨Build, F, Tm, Q, QF, TB, Bind, BindMap, Ve, Snap, NB, BA, C, Cmp, L, M, Rep, Msg, AF,
    I, interp, isPT, pt, Fork, Tf, produce, Cx, K, Restore, Seed, Rs, hb⟩ := h
  exact ⟨Build, F, Tm, Q, QF, TB, NB, BA, Bind, BindMap, C, Ve, Cmp, L, M, Rep, Msg, AF, I,
    interp, isPT, pt, Fork, Tf, produce, Cx, K, Snap, Restore, Seed, Rs, hb⟩

/-- The composition area gives `spec_consistent_compose`. -/
theorem composeSpec_sound {N A T Rr : Type} [DecidableEq N] [ToString N] [DecidableEq T]
    [ToString T] (Nm : Naming N) (tyOf : N → T) (Fv : BuiltNet N A → Rr)
    (h : ∃ (Build : Trans N → Option String) (F Tm : FireRel N) (TR : TRel N)
      (TB : TBuilder N A) (Inst : InstFn N A) (S : ScriptFn N A) (Co : CorrOps N A),
      ComposeSpec Nm tyOf Fv Build F Tm TR TB Inst S Co) :
    type_of% (@spec_consistent_compose N A T Rr _ _ _ _ Nm tyOf Fv) := by
  obtain ⟨Build, F, Tm, TR, TB, Inst, S, Co, NB, SB, sq, cm, Mg, C, Au, D, Rb, Fz, FN, Bi, PA, G,
    tbl, res, acc, vw, hb⟩ := h
  exact ⟨Build, F, Tm, TR, TB, NB, SB, Inst, sq, cm, Mg, C, Au, D, S, Rb, Fz, FN, Bi, Co, PA, G,
    tbl, res, acc, vw, hb⟩

/-- The ν area gives `joint_nu_sketch`. -/
theorem nuSpec_sound {N V : Type} [DecidableEq N] [ToString N]
    (h : ∃ (Build : Trans N → Option String) (F : FireRel N) (QF : QFireRel N (Stamped V)),
      NuSpec Build F QF) :
    type_of% (@joint_nu_sketch N V _ _) := by
  obtain ⟨Build, F, QF, MB, NB, NF, S, I, NC, Mi, Vs, D, Cl, hb⟩ := h
  exact ⟨Build, F, QF, MB, NB, NF, S, I, NC, Mi, Vs, D, Cl, hb⟩

/-- The verifier area gives `joint_core_ver_sketch`. -/
theorem verSpec_sound {N : Type} [LinearOrder N] [Hashable N]
    (h : ∃ (F : FireRel N) (R : TRel N) (Denv : EnvDecider N) (Sp : SplitFn N)
      (Pl : SplitPlanFn N), VerSpec F R Denv Sp Pl) :
    type_of% (@joint_core_ver_sketch N _ _) := by
  obtain ⟨F, R, Denv, Sp, Pl, ⟨S, V, D, VN, X, abs, Dec, envAbs, A, h1⟩, h2, h3, h4, h5, h6, h7,
    h8, h9, h10, h11, hsp, rest⟩ := h
  exact ⟨⟨F, S, V, D, VN, X, abs, Dec, envAbs, Denv, R, A, h1⟩, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11, ⟨Sp, Pl, hsp⟩, rest⟩

/-- The export area gives `joint_export_sketch`. -/
theorem exportSpec_sound (h : ∃ Ex : Exporter, ExportSpec Ex) : type_of% joint_export_sketch := by
  obtain ⟨Ex, Em, L, TL, C, hb⟩ := h
  exact ⟨Ex, Em, L, TL, C, hb⟩

end Projections

/-! ## The reference witnesses of each area -/

section Witnesses

/-- The reference witnesses meet the queue area, with the reference validator `ioRefValidate`
(the executor's). -/
theorem queueSpec_ref {N Tk : Type} [DecidableEq N] [ToString N] :
    QueueSpec (Tk := Tk) refBuild RefFire refTimeoutOutcomeFire refTimingQ refReadyOrder RefTStep
      RefQFire (ioRefValidate (N := N)) :=
  ⟨refTimingCompile, TSt.init, refQOps, refEnableCheck,
    ⟨CORE_022_reference, CORE_030_reference, CORE_031_reference, CORE_032_reference,
      CORE_033_reference, CORE_034_reference, CORE_035_reference, CORE_036_reference,
      IO_001_reference, IO_002_reference, IO_003_reference, IO_004_reference, IO_005_reference,
      IO_010_reference, IO_011_reference, IO_012_reference, IO_013_reference,
      refTimeoutOutcomeFire_eq_refTimedOutFire (N := N) ▸ IO_014_reference⟩,
    ⟨⟨_, IO_007_reference⟩, IO_015_reference,
      ⟨_, _, IO_016_reference (N := N), IO_017_reference (N := N)⟩⟩,
    ⟨TIME_001_reference, rfl, rfl, CONC_024_reference⟩, ⟨EXEC_002_reference, CONC_023_reference⟩,
    refTStep_projectsTo, refTStep_framesMarking, TIME_012_reference_framesClock,
    refTStep_covers, refTStep_coversReap, refTStep_coversDelay, TIME_002_reference,
    TIME_003_reference, TIME_004_reference, TIME_005_reference, TIME_006_reference,
    TIME_010_reference, TIME_011_reference, TIME_012_reference, TIME_013_reference,
    TIME_015_reference, CONC_005_reference, refQFire_projectsTo, refQFire_covers,
    EXEC_010_reference, EXEC_012_reference, EXEC_013_reference, EXEC_020_reference,
    CORE_010_reference, CORE_013_reference, CORE_072_reference, CORE_070_reference,
    fun _ _ ty val HasType => CORE_003_reference ty val HasType,
    CONC_004_reference, CONC_008_reference,
    ⟨core070_ringMarking, ringMarkingMaterialiser, refConsume, CORE_070_ringStore,
      CONC_022_ringMarking, CONC_025_ringMarking, CONC_021_ringMarking⟩⟩

/-- The reference witnesses meet the structure area, with the reference snapshot `refSnapshot`
of CORE-073 and the reference verification entry check. -/
theorem structureSpec_ref {N A Tk Val : Type} [DecidableEq N] [ToString N] (val : Tk → Val) :
    StructureSpec (N := N) (A := A) val refBuild RefFire refTimeoutOutcomeFire refTimingQ RefQFire
      refTransBuild refBind refBindMapKeep refVerifyEntry
      (refSnapshot : FinQ String Tk → QSnap String Tk) :=
  ⟨refNetBuild, copyBuilder refTransBuild, refCompile, refCompileWith, refBitmapLayout,
    refPlacesByName, refDeadArcs, refDeadArcMsg,
    refActionFire, refAnyAction, Act.interp refAnyAction, Act.isPassthrough,
    refRetrievePassthrough, refFork, refTransform val, refProduce val, refCtx val,
    refTokenFactory, refRestore, refSeed, refResume,
    IO_011_reference, IO_012_reference, IO_013_reference,
    refTimeoutOutcomeFire_eq_refTimedOutFire (N := N) ▸ IO_014_reference, EXEC_012_reference,
    TIME_001_reference, CORE_020_reference, CORE_021_reference, CORE_040_reference _,
    CORE_041_reference _, EXEC_042_build_reference _, CORE_042_reference_keep, CORE_043_reference,
    CONC_007_reference,
    PERF_030_reference, CORE_002_byName, CORE_037_reference, projBuild_ref,
    refTransBuild_timingAgree, fun _ _ h => refNetBuild_fromBuilder h,
    fun _ r h => ⟨refBind_fromBuilder h r, refBind_fromBuilder h (mapKeep r)⟩,
    refBitmapLayout_maskWords, EXEC_010_reference, refQFire_projectsTo, refQFire_covers,
    CORE_050_reference, core050_endsBy CORE_050_reference refQFire_projectsTo, CORE_051_reference,
    CORE_052_reference val, CORE_053_reference val, CORE_054_reference val,
    CORE_060_reference val, CORE_061_reference val, CORE_062_reference val,
    CORE_063_reference val, CORE_011_reference, CORE_073_reference, CORE_073_T_reference,
    fun _ hw => refTransform_throughCtx val (CORE_062_reference val).1 hw,
    refFork_throughCtx val (CORE_062_reference val).1,
    fun _ _ _ _ _ => Iff.rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- The reference channel merge of the composition area. -/
abbrev refMergeAll (N A : Type) [DecidableEq N] [ToString N] : MergeFn N A :=
  refMerge refBuild (seqAct fun a _ => a) (refCorrOps (A := A)).merge

/-- The reference witnesses meet the composition area: the reference instantiation, the reference
build script over the reference merge, and the reference correspondence operations. -/
theorem composeSpec_ref {N A T Rr : Type} [DecidableEq N] [ToString N] [DecidableEq T]
    [ToString T] (Nm : Naming N) (tyOf : N → T) (Fv : BuiltNet N A → Rr) :
    ComposeSpec Nm tyOf Fv refBuild RefFire refTimeoutOutcomeFire RefTStep refTransBuild
      (refInst Nm) (buildScript Nm tyOf refBuild (refMergeAll N A)) refCorrOps :=
  ⟨refNetBuild, refSubnetBuild refNetBuild, seqAct fun a _ => a, refCorrOps.merge,
    refMergeAll N A,
    refCompose tyOf refBuild (refMergeAll N A), refAuto Nm tyOf refBuild (refMergeAll N A),
    refDirect Nm tyOf, composedRebind, refFuse refBuild, refFromNet, refBindInst,
    refPortAs tyOf, refPassThrough Fv, mergeCard, memberOf, refSubnetAccess,
    Mod041.refView,
    ⟨CORE_022_reference, CORE_030_reference, CORE_031_reference, CORE_032_reference,
      CORE_033_reference, CORE_034_reference, CORE_035_reference, CORE_036_reference,
      IO_001_reference, IO_002_reference, IO_003_reference, IO_004_reference, IO_005_reference,
      IO_010_reference, IO_011_reference, IO_012_reference, IO_013_reference,
      refTimeoutOutcomeFire_eq_refTimedOutFire (N := N) ▸ IO_014_reference,
      CORE_020_reference⟩,
    ⟨MOD_001_reference refNetBuild, MOD_003_reference refNetBuild, MOD_004_reference Nm,
      MOD_005_reference refNetBuild, MOD_006_reference refNetBuild⟩,
    ⟨MOD_010_reference Nm, MOD_011_reference Nm, MOD_011_typed_reference tyOf,
      MOD_013_reference Nm, MOD_014_reference, MOD_030_reference, MOD_031_reference⟩,
    ⟨MOD_020_reference tyOf refBuild _, MOD_021_table_reference,
      MOD_021_reference refBuild _ _, mod022_reference_anyMerge tyOf refBuild _,
      mod024_ref Nm tyOf refBuild _, MOD_025_reference Nm tyOf⟩,
    ⟨mod012_buildScript Nm tyOf refBuild (refMerge_local _ _),
      mod012_clock_buildScript Nm tyOf refBuild (refMerge_local _ _),
      mod023_buildScript Nm tyOf refBuild _ (refMerge_builds _ _), MOD_026_resolve_reference,
      mod026_buildScript Nm tyOf refBuild _, mod027_ref Nm tyOf refBuild _,
      MOD_050_reference Fv, MOD_061_reference refBuild⟩,
    ⟨MOD_040_reference, MOD_041_reference⟩,
    projBuild_ref, refInst_firesAsBody Nm,
    ⟨CORE_040_reference _, fun ops hB => buildScript_core ops hB⟩,
    scriptRuns_ref Nm tyOf refBuild _,
    ⟨rfl, fun _ _ _ hI => (refInst_ok hI).2.2.2.2.1⟩,
    fun _ _ _ h => by cases h; rfl,
    ⟨refTStep_projectsTo, refTStep_framesMarking, TIME_012_reference_framesClock⟩⟩

/-- The reference witnesses meet the ν area. -/
theorem nuSpec_ref {N V : Type} [DecidableEq N] [ToString N] :
    NuSpec (V := V) refBuild (RefFire (N := N)) RefQFire :=
  ⟨refMatchBuild, refNuBuild, RefNuFire, refSelect, refNameImpl,
    refNuEnableCheck, refMintSys, refValidScope, refDefaultDraw, refClassify,
    CORE_022_reference, IO_011_reference, EXEC_010_reference, EXEC_012_reference,
    refQFire_projectsTo, refQFire_covers,
    NU_020_build_reference, NU_020_enable_reference, NU_020_take_reference,
    NU_020_frame_reference, NU_022_reference, NU_001_reference, NU_001_rename_reference,
    NU_021_reference, NU_054_build_reference, NU_054_check_reference,
    CONC_004_reference, CONC_008_reference, CONC_008_nu_reference,
    NU_010_unique_reference, NU_010_replay_reference, NU_011_format_reference,
    NU_011_lineage_reference, NU_011_default_reference, NU_051_reference,
    NU_010_classify_reference, NU_054_verifier_reference,
    refNuFire_restrictsTo, refNuBuild_extends, refNuFire_selectsBy, refNuFire_covers,
    refNameImpl_lt_iff, refNuFire_checks, refMintSys_total, refDefaultDraw_unfixed,
    fun _ _ hd => nu011_default_draw_accepted NU_011_default_reference hd⟩

/-- The reference witnesses meet the verifier area, with the reference environment verifier and
the reference split. -/
theorem verSpec_ref {N : Type} [LinearOrder N] [Hashable N] :
    VerSpec (RefFire (N := N)) RefTStep refEnvVerify (Verifier.Split.refSplit (K := N))
      refSplitPlan :=
  ⟨⟨refStrand, refRestViol, refSafetyViol, refVerifiedNet, refVirtual, inertAbs,
      Verifier.refVerify inertAbs, ver006EnvAbs, refXor,
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
    VER_004_split_reference,
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

/-- The reference witnesses meet the export area, with the clustered reference exporter. -/
theorem exportSpec_ref : ExportSpec refExport :=
  ⟨refEmit, refCardLabel, refTransLabel, refPlaceCategory,
    refExportWith_agrees refClusterStage,
    EXP_001_any _, EXP_002_any _, EXP_003_any _, EXP_004_any _, EXP_005_reference,
    EXP_006_reference, EXP_007_label_reference, EXP_007_config_any _, EXP_008_reference,
    EXP_012_reference, EXP_013_any _, EXP_014_any _, EXP_016_reference, EXP_017_reference,
    EXP_018_any _, refEmit_leafTargets⟩

/-- The reference stores, queries, logging decorator, subscriptions, archive and replay call meet
the store part over the executor events. -/
theorem storeSpec_ref {N T : Type} [DecidableEq N] [DecidableEq T] (pn : N → String) :
    StoreSpec (N := N) (T := T) pn :=
  joint_events_store_sketch (D := String) (NetEvent.toShape pn) NetEvent.replayView

/-- The reference executor's pass order is the reference order of EXEC-002: `readyOrder` is
defined from `refReadyOrder`. -/
theorem passOrder_ref {N T : Type} [DecidableEq N] : PassOrder (N := N) (T := T) refReadyOrder :=
  fun _ _ => rfl

end Witnesses

/-! ## The joint predicate -/

/-- **Every area on one model.** The area predicates over the shared parameters, the executor
and event areas over the one executor `E` and the one executor with events `W` that steps as it,
the pass-order link, and the cross-model blocks of wave W11 that read a shared parameter:
EVT-032's replay agreement on `W`, NU-054's fail block on `E`, MOD-040's block (b) on the
exporter `Ex`, MOD-051's binding block on the binding pair of CORE-042, and MOD-031's context
block on the correspondence operations `Co`. Three W11 lines over relations of their own close
it (TIME-012's ν clause, NU-050's timed line with its coverage, CORE-011's epoch slice). -/
def AllSpec {N V A Val Ty Rr : Type} [LinearOrder N] [Hashable N] [ToString N] [DecidableEq V]
    [DecidableEq Ty] [ToString Ty]
    (val : Stamped V → Val) (Nm : Naming N) (tyOf : N → Ty) (Fv : BuiltNet N A → Rr)
    (pn : N → String)
    (Build : Trans N → Option String) (F Tm : FireRel N) (Q : TimingContract) (O : ReadyOrder)
    (R : TRel N) (QF : QFireRel N (Stamped V)) (Vd : OutputValidator N) (TB : TBuilder N A)
    (Bind BindMap : BuiltNet N A → (String → Option (Act A)) → BuiltNet N A)
    (Ve : BuiltNet N A → Option String)
    (Snap : FinQ String (Stamped V) → QSnap String (Stamped V))
    (Inst : InstFn N A) (S : ScriptFn N A) (Co : CorrOps N A) (Denv : EnvDecider N)
    (Sp : SplitFn N) (Pl : SplitPlanFn N) (Ex : Exporter)
    (E : XRel N (Stamped V)) (X : ExpiryRel N (Stamped V)) (W : EvExec N (Stamped V))
    (Al : ActionLogRel N (Stamped V)) (Aw : AwaitRel N (Stamped V)) : Prop :=
  QueueSpec Build F Tm Q O R QF Vd ∧
  StructureSpec val Build F Tm Q QF TB Bind BindMap Ve Snap ∧
  ComposeSpec Nm tyOf Fv Build F Tm R TB Inst S Co ∧
  NuSpec Build F QF ∧
  VerSpec F R Denv Sp Pl ∧
  ExecSpec Vd E X QF R ∧ PassOrder (N := N) (T := Stamped V) O ∧
  W.erase = E ∧ EventsSpec W Al Aw ∧ StoreSpec (T := Stamped V) pn ∧
  ExportSpec Ex ∧
  EVT_032_B W ∧ NU_054_fail E ∧ MOD_040_b Ex ∧
  (∃ DB DBM, MOD_051_bind Bind BindMap DB DBM) ∧ (∃ RC, MOD_031_ctx val Co RC) ∧
  (∃ RT : NuTRel N V String, TIME_012_nu RT) ∧
  (∃ RB : RBTRel N V String, NU_050_timed RB ∧ RBTCovers RB) ∧
  (∃ EE : EpochRel N V, CORE_011_B EE)

/-- The reference witnesses meet the joint predicate, for every value projection, naming model,
token-type reader, verification facility and place printer. -/
theorem allSpec_ref {N V A Val Ty Rr : Type} [LinearOrder N] [Hashable N] [ToString N]
    [DecidableEq V] [DecidableEq Ty] [ToString Ty]
    (val : Stamped V → Val) (Nm : Naming N) (tyOf : N → Ty) (Fv : BuiltNet N A → Rr)
    (pn : N → String) :
    AllSpec val Nm tyOf Fv pn refBuild RefFire refTimeoutOutcomeFire refTimingQ refReadyOrder
      RefTStep RefQFire ioRefValidate refTransBuild refBind refBindMapKeep refVerifyEntry
      refSnapshot (refInst Nm) (buildScript Nm tyOf refBuild (refMergeAll N A)) refCorrOps
      refEnvVerify (Verifier.Split.refSplit (K := N)) refSplitPlan refExport RefExec refExpiry
      (refEvExec polJT) refALog refAwait :=
  ⟨queueSpec_ref, structureSpec_ref val, composeSpec_ref Nm tyOf Fv, nuSpec_ref, verSpec_ref,
    execSpec_ref, passOrder_ref, refEvExec_erase polJT, eventsSpec_ref, storeSpec_ref pn,
    exportSpec_ref,
    EVT_032_B_reference, NU_054_fail_reference, MOD_040_b_reference,
    ⟨_, _, MOD_051_bind_reference_keep⟩, ⟨_, MOD_031_ctx_reference val⟩,
    ⟨_, TIME_012_nu_reference⟩, ⟨_, NU_050_timed_reference, NU_050_timed_covers_reference⟩,
    ⟨_, CORE_011_B_reference⟩⟩

/-! ## The theorem -/

/-- ✓ **The whole specification has one model.** One build check, one firing relation, one timing
contract, one ready order, one timed step, one queue firing, one output validator, one transition
builder, one snapshot, one composition, one environment verifier, one split, one exporter, one
executor and one executor with events that steps as it meet every area at once: the CORE, IO,
TIME, queue, structure, composition, ν, verifier, executor, event and export blocks, and the
cross-model lines of wave W11. Over string place names the same witnesses also meet EVT-014, and
every marking snapshot the executor reports is CORE-073's snapshot `Snap` of the declared places;
CORE-037's warnings wrap the one executor and the one environment verifier, and MOD-051's
`verify` runs the one instantiation, build script, entry check and environment verifier. Over flat
place identities the one executor's runs are runs of the verifier's in-flight model by their
counts (`CountAgrees`), so the split the verifier checks covers them (VER-004, block B).

For example, a net built by the one builder, run by the one executor, fires each transition as
the one firing relation does; a pass starts its ready transitions in the order EXEC-002 gives;
the snapshot at the start of a run with places `b`, `c`, `a` lists `a` then `b` as CORE-073 does;
and the verifier's split of that net reaches every marking the run rests at. -/
@[evidence consistent CORE_022 CORE_030 CORE_031 CORE_032 CORE_033 CORE_034 CORE_035 CORE_036
  IO_001 IO_002 IO_003 IO_004 IO_005 IO_007 IO_010 IO_011 IO_012 IO_013 IO_014 IO_015 IO_016
  IO_017 TIME_001 TIME_002 TIME_003 TIME_004 TIME_005 TIME_006 TIME_010 TIME_011 TIME_012
  TIME_013 TIME_015 EXEC_002 EXEC_010 EXEC_012 EXEC_013 EXEC_020 CONC_005 CONC_023 CONC_024
  CORE_010 CORE_013 CORE_070 CORE_072 CONC_004 CONC_008 CONC_022 CONC_025 CORE_003 CONC_021
  CORE_020 CORE_002 CORE_021 CORE_040 CORE_041 CORE_042 CORE_043 CONC_007 PERF_030 CORE_037
  CORE_011 CORE_050 CORE_051 CORE_052 CORE_053 CORE_054 CORE_060 CORE_061 CORE_062 CORE_063
  CORE_073 CORE_073_T EXEC_042_build
  MOD_001 MOD_003 MOD_004 MOD_005 MOD_006 MOD_010 MOD_011 MOD_011_typed MOD_012 MOD_012_clock
  MOD_013 MOD_014 MOD_020 MOD_021_table MOD_021 MOD_022 MOD_023 MOD_024 MOD_025
  MOD_026_resolve MOD_026 MOD_027 MOD_030 MOD_031 MOD_040 MOD_041 MOD_050 MOD_061
  NU_020_build NU_020_enable NU_020_take NU_020_frame NU_022 NU_001 NU_001_rename NU_021
  NU_054_build NU_054_check CONC_008_nu NU_010_unique NU_010_replay NU_011_format NU_011_lineage
  NU_011_default NU_010_classify NU_054_verifier NU_051
  VER_001 VER_002 VER_002_count VER_003 VER_004_timed VER_004_split VER_005 VER_006
  VER_006_premise VER_006_quiescent VER_006_arrivals VER_006_verdict VER_007 VER_010
  VER_010_persist VER_010_key VER_011 VER_012 VER_012_build VER_013_order VER_013_args
  VER_013_classify VER_013_stop VER_014 VER_015 VER_015_order VER_016 VER_017 VER_017_cache
  VER_018 VER_018_order VER_019 VER_019_order VER_020 VER_020_guard VER_021 VER_022_meets
  VER_022_closure VER_022 VER_023 VER_023_graph VER_024 VER_024_select VER_024_route VER_025
  NU_010_unknownMint NU_051_colours NU_051_carrier NU_052_split NU_053 NU_053_dispatch
  NU_055_refusal
  EXEC_021 EXEC_001 EXEC_003 EXEC_022 EXEC_030 EXEC_031 EXEC_040 EXEC_041 EXEC_042 TIME_014
  CONC_001 CONC_002 CONC_003 CONC_010 ENV_002 ENV_003 ENV_004 ENV_005 ENV_006 ENV_010 ENV_011
  ENV_013 ENV_014 ENV_015 ENV_016 EXEC_002_cycle EXEC_010_cycle EXEC_013_cycle EXEC_020_cycle
  TIME_010_cycle TIME_012_cycle TIME_013_cycle TIME_015_cycle CONC_005_cycle
  EVT_002 EVT_003 EVT_004 EVT_005 EVT_006 EVT_006_payload EVT_007 EVT_007_payload EVT_008
  EVT_009 EVT_009_payload EVT_010 EVT_011 EVT_011_payload EVT_012 EVT_012_payload EVT_013
  EVT_014 ENV_016_await EVT_020 EVT_021 EVT_022 EVT_023 EVT_024 EVT_024_B EVT_025 EVT_030
  EVT_031 EVT_032
  EXP_001 EXP_002 EXP_003 EXP_004 EXP_005 EXP_006 EXP_007_label EXP_007_config EXP_008 EXP_012
  EXP_013 EXP_014 EXP_016 EXP_017 EXP_018
  EVT_032_B NU_054_fail MOD_040_b MOD_051_bind MOD_031_ctx TIME_012_nu NU_050_timed CORE_011_B
  CORE_037_events CORE_037_verifier MOD_051 VER_004_exec]
theorem spec_consistent_all {N V A Val Ty Rr : Type} [LinearOrder N] [Hashable N] [ToString N]
    [DecidableEq V] [DecidableEq Ty] [ToString Ty]
    (val : Stamped V → Val) (Nm : Naming N) (tyOf : N → Ty) (Fv : BuiltNet N A → Rr)
    (pn : N → String) :
    (∃ (Build : Trans N → Option String) (F Tm : FireRel N) (Q : TimingContract)
        (O : ReadyOrder) (R : TRel N) (QF : QFireRel N (Stamped V)) (Vd : OutputValidator N)
        (TB : TBuilder N A)
        (Bind BindMap : BuiltNet N A → (String → Option (Act A)) → BuiltNet N A)
        (Ve : BuiltNet N A → Option String)
        (Snap : FinQ String (Stamped V) → QSnap String (Stamped V))
        (Inst : InstFn N A) (S : ScriptFn N A) (Co : CorrOps N A) (Denv : EnvDecider N)
        (Sp : SplitFn N) (Pl : SplitPlanFn N) (Ex : Exporter)
        (E : XRel N (Stamped V)) (X : ExpiryRel N (Stamped V)) (W : EvExec N (Stamped V))
        (Al : ActionLogRel N (Stamped V)) (Aw : AwaitRel N (Stamped V)),
      AllSpec val Nm tyOf Fv pn Build F Tm Q O R QF Vd TB Bind BindMap Ve Snap Inst S Co Denv
        Sp Pl Ex E X W Al Aw) ∧
    (∀ (tyS : String → Ty) (FvS : BuiltNet String A → Rr),
      ∃ (Build : Trans String → Option String) (F Tm : FireRel String) (Q : TimingContract)
        (O : ReadyOrder) (R : TRel String) (QF : QFireRel String (Stamped V))
        (Vd : OutputValidator String) (TB : TBuilder String A)
        (Bind BindMap : BuiltNet String A → (String → Option (Act A)) → BuiltNet String A)
        (Ve : BuiltNet String A → Option String)
        (Snap : FinQ String (Stamped V) → QSnap String (Stamped V))
        (Inst : InstFn String A) (S : ScriptFn String A) (Co : CorrOps String A)
        (Denv : EnvDecider String) (Sp : SplitFn String) (Pl : SplitPlanFn String)
        (Ex : Exporter) (E : XRel String (Stamped V)) (X : ExpiryRel String (Stamped V))
        (W : EvExec String (Stamped V)) (Al : ActionLogRel String (Stamped V))
        (Aw : AwaitRel String (Stamped V)),
      AllSpec val strNaming tyS FvS id Build F Tm Q O R QF Vd TB Bind BindMap Ve Snap Inst S Co
          Denv Sp Pl Ex E X W Al Aw ∧
        EVT_014 W ∧ W = evt014With (fun C M => Snap (evt014_restrictFin C.X.net.places M)) ∧
        (∃ W', CORE_037_events W' W) ∧ (∃ D', CORE_037_verifier D' Denv) ∧
        (∃ SV, MOD_051 Inst S Ve Denv SV ∧ Mod051Covers Inst S Ve SV)) ∧
    (∃ (Build : Trans PlaceId → Option String) (F Tm : FireRel PlaceId) (Q : TimingContract)
        (O : ReadyOrder) (R : TRel PlaceId) (QF : QFireRel PlaceId (Stamped V))
        (Vd : OutputValidator PlaceId) (Denv : EnvDecider PlaceId) (Sp : SplitFn PlaceId)
        (Pl : SplitPlanFn PlaceId) (E : XRel PlaceId (Stamped V))
        (X : ExpiryRel PlaceId (Stamped V)) (W : EvExec PlaceId (Stamped V))
        (Al : ActionLogRel PlaceId (Stamped V)) (Aw : AwaitRel PlaceId (Stamped V)),
      QueueSpec Build F Tm Q O R QF Vd ∧ VerSpec F R Denv Sp Pl ∧ ExecSpec Vd E X QF R ∧
        PassOrder (N := PlaceId) (T := Stamped V) O ∧ W.erase = E ∧ EventsSpec W Al Aw ∧
        NU_054_fail E ∧
        CountAgrees E ∧ VER_004_exec E Sp) := by
  refine ⟨⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      allSpec_ref val Nm tyOf Fv pn⟩, fun tyS FvS => ?_, ?_⟩
  · refine ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      allSpec_ref val strNaming tyS FvS id, EVT_014_reference, ?_,
      ⟨_, CORE_037_events_referenceJT⟩, ⟨_, CORE_037_verifier_reference⟩,
      ⟨_, MOD_051_reference _ _ _ _, mod051_ref_covers _ _ _ _⟩⟩
    rw [← evt014With_snapOf]
    congr 1
    funext C M
    exact evt014_snapOf_eq C M
  · exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, queueSpec_ref, verSpec_ref, execSpec_ref,
      passOrder_ref, refEvExec_erase polJT, eventsSpec_ref, NU_054_fail_reference,
      countAgrees_ref, VER_004_exec_of countAgrees_ref (VER_004_split_reference (K := PlaceId))⟩

end Libpetri.Spec
