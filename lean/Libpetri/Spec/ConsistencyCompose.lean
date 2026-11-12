import Libpetri.Spec.Consistency
import Libpetri.Spec.GlossaryBuild
import Libpetri.Spec.GlossaryCompose
import Libpetri.Spec.Req.CORE_020
import Libpetri.Spec.Req.CORE_040
import Libpetri.Spec.Req.TIME_012
import Libpetri.Spec.Req.MOD_001
import Libpetri.Spec.Req.MOD_003
import Libpetri.Spec.Req.MOD_004
import Libpetri.Spec.Req.MOD_005
import Libpetri.Spec.Req.MOD_006
import Libpetri.Spec.Req.MOD_010
import Libpetri.Spec.Req.MOD_011
import Libpetri.Spec.Req.MOD_012
import Libpetri.Spec.Req.MOD_013
import Libpetri.Spec.Req.MOD_014
import Libpetri.Spec.Req.MOD_020
import Libpetri.Spec.Req.MOD_021
import Libpetri.Spec.Req.MOD_022
import Libpetri.Spec.Req.MOD_023
import Libpetri.Spec.Req.MOD_024
import Libpetri.Spec.Req.MOD_025
import Libpetri.Spec.Req.MOD_026
import Libpetri.Spec.Req.MOD_027
import Libpetri.Spec.Req.MOD_030
import Libpetri.Spec.Req.MOD_031
import Libpetri.Spec.Req.MOD_040
import Libpetri.Spec.Req.MOD_041
import Libpetri.Spec.Req.MOD_050
import Libpetri.Spec.Req.MOD_061

set_option linter.missingDocs true

/-!
# Consistency of the composition requirements with the CORE and IO requirements

`spec_consistent_compose` puts every composition block of wave W8 ([MOD-001] to [MOD-061]) on one
joint model together with the CORE and IO firing blocks and CORE-020. The tracer
`joint_compose_sketch` joined MOD-010 alone. Conjoining blocks over independent parameters proves
nothing on its own; what counts is the parameters the blocks share and the agreement conjuncts
that tie each new parameter to a witness the existing blocks already use.

Shared parameters (one value each, read by every block that names it):

* the build check `Build` of the IO blocks is the build check of the composition functions
  (MOD-020, MOD-021, MOD-022, MOD-023, MOD-024, MOD-027) and of fusion (MOD-061);
* the firing relation `F` of the CORE and IO blocks is the one MOD-012's isolation line is
  stated over;
* one net builder `NB` and one subnet builder `SB` for MOD-001, MOD-003, MOD-004, MOD-005 and
  MOD-006; one instantiation function `Inst` for MOD-004, MOD-010, MOD-011 and MOD-013;
* one channel merge `Mg` for MOD-020 (the merge a channel binding runs) and MOD-021 (the merge
  rules); one composition function `C` for MOD-020, MOD-022 and MOD-024; one build script `S`
  for MOD-012, MOD-023, MOD-026 and MOD-027; one token-type reader `tyOf` for MOD-011 (typed),
  MOD-020, MOD-022, MOD-025 and MOD-027; one set of correspondence operations `Co` for MOD-031,
  whose merge is MOD-021's correspondence merge `cm`.

Agreement conjuncts tie the parameters that no block shares:

* **Builder.** `projBuild TB = Build`: CORE-020's transition builder `TB` has the build check
  `Build` of the IO blocks (witness `refTransBuild`, `projBuild_ref`). The composition model
  rewrites RefNetBuild's `TransDef` (`CDef` extends it), so a renamed definition is a definition
  `TB` could have built; that every definition of a built net passes `Build` is MOD-023's line 1.
* **Net builder.** `CORE_040 (defsTB N A) NB`, and on a script of `place`, `trans` and
  `terminal` calls whose transitions pass `Build`, the build script `S` agrees with `NB` up to
  the order of places (`buildScript_core`): composition adds calls to the one net builder, not a
  second builder state.
* **Script.** `ScriptRuns Build C Au D S`: `S` is a fold of one call function over a new builder,
  followed by a `build()` step, and that call function runs `C` for an explicit compose, `Au` for
  an auto-compose and `D` for a direct composition of a built body, and fails a transition `Build`
  rejects with `Build`'s message (`step_compose`, `step_composeAuto`, `step_composeDirect`,
  `step_trans_error`). So the blocks over `S` and the blocks over `C`, `Au` and `D` speak of one
  composition.
* **Correspondence.** `cm = Co.merge`: MOD-021's correspondence merge is MOD-031's; and every
  instance `Inst` returns holds the body's definitions, each through one pass `Co.pass` of
  MOD-031 (`refInst_ok`: `refInst` maps every definition with `CDef.map`, `refCorrOps.pass`).
* **Binding.** Every derived instance the per-instance binding `Bi` of MOD-030 returns holds the
  instance's definitions, each bound through MOD-031's `Co.rebind` with the action the overrides
  give its name, its own action otherwise. The binding `Rb` of a composed net (MOD-026) acts on
  built nets, not on instances: it is tied to the build script by MOD-026's own statement, which
  takes both.
* **Time.** `ProjectsTo TR F`, `FramesMarking TR` and `time012_FramesClock TR`: a firing step of
  MOD-012's timed relation `TR` is a firing of `F`, only a firing changes the marking, and a
  firing leaves the clocks alone; the TIME blocks themselves are joined at the reference timed
  relation by `spec_consistent_coreIO_time` (ConsistencyTime), with these three conjuncts.
* **Firing.** `InstFiresAsBody Nm Inst F`: every transition of an instance fires under the firing
  relation `F` of the CORE and IO blocks exactly as the body transition it renames, at the marking
  pulled back through the rename, and leaves every place outside the rename's image as it was.
  At the reference it is a consequence of MOD-010 (`mod010_firesAsBody`, through `fires_mapT`),
  so the conjunct costs the reference nothing and constrains every other joint model: the
  instantiation function and the firing relation must agree.

MOD-040's helper and MOD-041's `instancePrefix` field need no conjunct: both blocks state them
with the export glossary's `instancePrefix`, so every pair of models agrees on every node
(`mod041_nodePrefix_eq_helper`). Not tied (open): the accessor `acc` of MOD-040 and the view `vw`
of MOD-041 are functions of any net's names, so no conjunct relates them to the composed net the
script builds; and the verification facility `Fv` of MOD-050 is a free parameter.

The joint theorems hold for every naming model `Nm`; `joint_compose_sketch_str` instantiates it
at place identity by name (`strNaming`), so the naming binder is not vacuous (a type such as
`Unit` has no naming model, since two valid prefixes must rename its one place apart).
`compose_join_frame` shows what the firing conjunct buys in every joint model: a firing of a
transition of an instance leaves every place the instance's rename does not reach unchanged, the
first half of MOD-012's isolation.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-- ✓ MOD-010 holds together with the CORE and IO firing blocks and CORE-020 on one model, for
every naming model `Nm`. The firing relation `F` is the reference firing relation, the build check
`Build` is the reference builder `refBuild`, the transition builder `TB` is the reference
transition builder (whose build check is `refBuild`), and the instantiation function is the
reference instantiation `refInst Nm`. Two agreement conjuncts tie the parameters together:
`TB`'s build check is `Build`, and every transition of an instance fires under `F` as the body
transition it renames (`InstFiresAsBody`, a consequence of MOD-010 at the reference firing
relation). The skeleton of `spec_consistent_compose`. -/
@[evidence consistent CORE_022 CORE_030 CORE_031 CORE_032 CORE_033 CORE_034 CORE_035 CORE_036
  IO_001 IO_002 IO_003 IO_004 IO_005 IO_010 IO_011 IO_012 IO_013 IO_014 CORE_020 MOD_010]
theorem joint_compose_sketch {N A : Type} [DecidableEq N] [ToString N] (Nm : Naming N) :
    ∃ (Build : Trans N → Option String) (F T : FireRel N) (TB : TBuilder N A)
      (Inst : InstFn N A),
      CORE_022 F ∧ CORE_030 F ∧ CORE_031 F ∧ CORE_032 F ∧ CORE_033 F ∧ CORE_034 F ∧
      CORE_035 F ∧ CORE_036 F ∧ IO_001 F ∧ IO_002 F ∧ IO_003 F ∧ IO_004 F ∧ IO_005 F ∧
      IO_010 F ∧ IO_011 Build F ∧ IO_012 IO_012_check Build F ∧ IO_013 Build F T ∧
      IO_014 Build T ∧ CORE_020 TB ∧ MOD_010 Nm Inst ∧
      projBuild TB = Build ∧ InstFiresAsBody Nm Inst F :=
  ⟨refBuild, RefFire, refTimeoutOutcomeFire, refTransBuild, refInst Nm,
    CORE_022_reference, CORE_030_reference, CORE_031_reference, CORE_032_reference,
    CORE_033_reference, CORE_034_reference, CORE_035_reference, CORE_036_reference,
    IO_001_reference, IO_002_reference, IO_003_reference, IO_004_reference, IO_005_reference,
    IO_010_reference, IO_011_reference, IO_012_reference, IO_013_reference,
    refTimeoutOutcomeFire_eq_refTimedOutFire (N := N) ▸ IO_014_reference,
    CORE_020_reference, MOD_010_reference Nm, projBuild_ref, refInst_firesAsBody Nm⟩

/-- The joint model at place identity by name (TypeScript, Rust, Python): the naming binder of
`joint_compose_sketch` has a value, `strNaming`. -/
theorem joint_compose_sketch_str {A : Type} :
    ∃ (Build : Trans String → Option String) (F T : FireRel String) (TB : TBuilder String A)
      (Inst : InstFn String A),
      CORE_022 F ∧ CORE_030 F ∧ CORE_031 F ∧ CORE_032 F ∧ CORE_033 F ∧ CORE_034 F ∧
      CORE_035 F ∧ CORE_036 F ∧ IO_001 F ∧ IO_002 F ∧ IO_003 F ∧ IO_004 F ∧ IO_005 F ∧
      IO_010 F ∧ IO_011 Build F ∧ IO_012 IO_012_check Build F ∧ IO_013 Build F T ∧
      IO_014 Build T ∧ CORE_020 TB ∧ MOD_010 strNaming Inst ∧
      projBuild TB = Build ∧ InstFiresAsBody strNaming Inst F :=
  joint_compose_sketch strNaming

/-- **The firing conjunct at work**: in every joint model, a firing under `F` of a transition of
an instance leaves every place outside the image of the instance's rename unchanged. A transition
of instance `a` cannot write a place of instance `b`, whose places all lie outside `a`'s image
(`mod010_disjoint`): the first half of [MOD-012]'s isolation, before composition binds ports. -/
theorem compose_join_frame {N A : Type} {Nm : Naming N} {Inst : InstFn N A} {F : FireRel N}
    (hF : InstFiresAsBody Nm Inst F) {S : SubnetDef N A} {p : String} {I : Instance N A}
    (hI : Inst S p = .ok I) {d : CDef N A} (hd : d ∈ I.defs) {m : N → Nat} {dep : List N}
    {m' : N → Nat} (hfire : F d.toTrans m dep m') {y : N} (hy : ∀ x, Nm.pre p x ≠ y) :
    m' y = m y := by
  obtain ⟨d₀, -, h⟩ := hF S p I hI d hd
  obtain ⟨-, -, -, hout⟩ := (h m dep m').1 hfire
  exact hout y hy

/-- **The build script runs the composition functions**: `S` folds one call function over a new
builder and then runs a `build()` step, and that call function is `C` on an explicit compose call,
`Au` on an auto-compose call, `D` on a direct composition of a body whose definitions pass `Build`,
and fails a hand-added transition `Build` rejects with `Build`'s message. -/
def ScriptRuns {N A : Type} (Build : Trans N → Option String) (C : ComposeFn N A)
    (Au : AutoFn N A) (D : DirectFn N A) (S : ScriptFn N A) : Prop :=
  ∃ (St : Bld N A → Op N A → Except String (Bld N A))
    (Fi : Bld N A → Except String (ComposedNet N A)),
    (∀ ops, S ops = match ops.foldlM St Bld.empty with
      | .error m => .error m
      | .ok b => Fi b) ∧
    (∀ b I ports chans, St b (.compose I ports chans) = C b I ports chans) ∧
    (∀ b I cs, St b (.composeAuto I cs) = Au b I cs) ∧
    (∀ b (Sd : SubnetDef N A), (∀ d ∈ Sd.defs, Build d.toTrans = none) →
      St b (.composeDirect Sd) = D b Sd) ∧
    (∀ b (d : CDef N A) m, Build d.toTrans = some m → St b (.trans d) = .error m)

/-- The reference build script runs the reference composition functions. -/
theorem scriptRuns_ref {N A T : Type} [DecidableEq N] [ToString N] [DecidableEq T] [ToString T]
    (Nm : Naming N) (tyOf : N → T) (Build : Trans N → Option String) (Mg : MergeFn N A) :
    ScriptRuns Build (refCompose tyOf Build Mg) (refAuto Nm tyOf Build Mg) (refDirect Nm tyOf)
      (buildScript Nm tyOf Build Mg) :=
  ⟨scriptStep Nm tyOf Build Mg, finish Nm Build, fun _ => rfl, fun _ _ _ _ => step_compose _ _ _,
    fun _ _ _ => step_composeAuto _ _, fun _ _ h => step_composeDirect h,
    fun _ _ _ h => step_trans_error h⟩

/-- ✓ **Every composition block holds together with the CORE and IO firing blocks and CORE-020 on
one model**, for every naming model `Nm`, every token-type reader `tyOf` and every verification
facility `Fv`. The firing relation is the reference one, the build check is `refBuild`, the net
and subnet builders are the reference ones, instantiation is `refInst Nm`, and the channel merge
is `refMerge` with MOD-031's correspondence merge: when both sides of a channel carry an action
it keeps the caller's (the generic action type has no sequencing), and it merges the two
correspondences key by key. Composition, the automatic binding, direct composition and the build
script all run that one merge and that one build check, and the agreement conjuncts say so. So a
subnet instantiated under `p1`, bound to the caller and built, is read by every block in the same
way: the same renamed places, the same transitions, the same build check, the same
correspondences and the same firings. -/
@[evidence consistent CORE_022 CORE_030 CORE_031 CORE_032 CORE_033 CORE_034 CORE_035 CORE_036
  IO_001 IO_002 IO_003 IO_004 IO_005 IO_010 IO_011 IO_012 IO_013 IO_014 CORE_020
  MOD_001 MOD_003 MOD_004 MOD_005 MOD_006 MOD_010 MOD_011 MOD_011_typed MOD_012 MOD_012_clock
  MOD_013 MOD_014 MOD_020 MOD_021_table MOD_021 MOD_022 MOD_023 MOD_024 MOD_025
  MOD_026_resolve MOD_026 MOD_027 MOD_030 MOD_031 MOD_040 MOD_041 MOD_050 MOD_061]
theorem spec_consistent_compose {N A T R : Type} [DecidableEq N] [ToString N] [DecidableEq T]
    [ToString T] (Nm : Naming N) (tyOf : N → T) (Fv : BuiltNet N A → R) :
    ∃ (Build : Trans N → Option String) (F Tm : FireRel N) (TR : TRel N) (TB : TBuilder N A)
      (NB : NetBuilder (defsTB N A)) (SB : SubnetMake N A) (Inst : InstFn N A)
      (sq : Act A → Act A → Act A) (cm : CorrMergeFn N A) (Mg : MergeFn N A)
      (C : ComposeFn N A) (Au : AutoFn N A) (D : DirectFn N A) (S : ScriptFn N A)
      (Rb : RebindFn N A) (Fz : FuseFn N A) (FN : FromNetFn N A) (Bi : InstBindFn N A)
      (Co : CorrOps N A) (PA : PortAsFn N A T) (G : ComposedNet N A → R)
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
      (ProjectsTo TR F ∧ FramesMarking TR ∧ time012_FramesClock TR) := by
  let Mg : MergeFn N A := refMerge refBuild (seqAct fun a _ => a) (refCorrOps (A := A)).merge
  exact ⟨refBuild, RefFire, refTimeoutOutcomeFire, RefTStep, refTransBuild, refNetBuild,
    refSubnetBuild refNetBuild, refInst Nm, seqAct fun a _ => a, refCorrOps.merge, Mg,
    refCompose tyOf refBuild Mg, refAuto Nm tyOf refBuild Mg, refDirect Nm tyOf,
    buildScript Nm tyOf refBuild Mg, composedRebind, refFuse refBuild, refFromNet, refBindInst,
    refCorrOps, refPortAs tyOf, refPassThrough Fv, mergeCard, memberOf, refSubnetAccess,
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
    ⟨MOD_020_reference tyOf refBuild Mg, MOD_021_table_reference,
      MOD_021_reference refBuild _ _, mod022_reference_anyMerge tyOf refBuild Mg,
      mod024_ref Nm tyOf refBuild Mg, MOD_025_reference Nm tyOf⟩,
    ⟨mod012_buildScript Nm tyOf refBuild (refMerge_local _ _),
      mod012_clock_buildScript Nm tyOf refBuild (refMerge_local _ _),
      mod023_buildScript Nm tyOf refBuild Mg (refMerge_builds _ _), MOD_026_resolve_reference,
      mod026_buildScript Nm tyOf refBuild Mg, mod027_ref Nm tyOf refBuild Mg,
      MOD_050_reference Fv, MOD_061_reference refBuild⟩,
    ⟨MOD_040_reference, MOD_041_reference⟩,
    projBuild_ref, refInst_firesAsBody Nm,
    ⟨CORE_040_reference _, fun ops hB => buildScript_core ops hB⟩,
    scriptRuns_ref Nm tyOf refBuild Mg,
    ⟨rfl, fun _ _ _ hI => (refInst_ok hI).2.2.2.2.1⟩,
    fun _ _ _ h => by cases h; rfl,
    ⟨refTStep_projectsTo, refTStep_framesMarking, TIME_012_reference_framesClock⟩⟩

end Libpetri.Spec
