import Libpetri.Spec.ConsistencyQueue
import Libpetri.Spec.GlossaryBuild
import Libpetri.Spec.Req.CORE_002
import Libpetri.Spec.Req.CORE_020
import Libpetri.Spec.Req.CORE_021
import Libpetri.Spec.Req.CORE_037
import Libpetri.Spec.Req.CORE_040
import Libpetri.Spec.Req.CORE_041
import Libpetri.Spec.Req.EXEC_042
import Libpetri.Spec.Req.CORE_042
import Libpetri.Spec.Req.CORE_043
import Libpetri.Spec.Req.CONC_007
import Libpetri.Spec.Req.PERF_030
import Libpetri.Spec.Req.EXEC_010
import Libpetri.Spec.Req.CORE_011
import Libpetri.Spec.Req.CORE_050
import Libpetri.Spec.Req.CORE_051
import Libpetri.Spec.Req.CORE_052
import Libpetri.Spec.Req.CORE_053
import Libpetri.Spec.Req.CORE_054
import Libpetri.Spec.Req.CORE_060
import Libpetri.Spec.Req.CORE_061
import Libpetri.Spec.Req.CORE_062
import Libpetri.Spec.Req.CORE_063
import Libpetri.Spec.Req.CORE_073
import Libpetri.Reference.Link

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
* **Action tag** (W3). CORE-051 is stated over the same builder `TB`, so a transition built
  without an action carries the passthrough tag; and the action CORE-051's tags name is the
  action the action firing `AF` of CORE-050 reads for a built transition: for every definition
  `d`, the firings of `d` that end with its tag's action under the table `I` (`TagFire`) are the
  `AF` firings under `interp d.action`. With it, `structure_default_tag_nil` holds: a transition
  `TB` builds without an action deposits nothing when a firing ends with its action.
* **Net view** (W2 fan-out). Every block that runs a net runs `b.toNet` or `b.toTimed tol` of a
  built net: `toTrans_reapable` gives `TimedNet`'s coherence by construction,
  `netNamesDistinct_iff` lifts ruling D10 to built nets, `toTimed_timing` gives each transition its
  own timing, and `built_timing_valid` keeps every timing the timed step reads valid.
* **Actions, context, initial state, snapshot** (W3). The action firing `AF` of CORE-050 is
  stated over the same queue firing `QF` (the reference `refActionFire` is a restriction of
  `RefQFire`), and CORE-053's transform and CORE-054's produce action are read through the same
  `AF` (`core053_firing_copies`, `core054_emits`). The context blocks CORE-060 to CORE-063 hold of
  one context `Cx`, and CORE-054's produce action writes through that context
  (`core054_ctxProduce Cx`). The snapshot blocks are stated at `N := String`: the resume of
  CORE-073 (T) is the queue theorem's initialiser `TSt.init` on the restored counts, and the
  snapshot's count projection is `Reference.Marking`'s canonical form (`structure_snapshot_counts`).
  CORE-011's token factory has no parameter in common with the others; its executor line is the
  block `CORE_011_B` (`CORE_011_B.lean`), stated on the executor model `RefExec`.

* **Net builder, binding, compiled net** (W2). CORE-040's net builder and CORE-041's builder
  state machine are built over `TB`; every net the net builder builds, bound in either form,
  holds only definitions of `TB` (`refNetBuild_fromBuilder`, `refBind_fromBuilder`); PERF-030's
  layout keeps CONC-007's mask words (`refBitmapLayout_maskWords`).

`joint_core_structure_sketch` holds the conjuncts of waves W1, W2 and W3 on one model: the build
check of the IO blocks and EXEC-012, TIME-001's contract, the W2 and W3 blocks with their
agreement conjuncts, and CORE-037's dead-arc report and message on their reference witnesses. It
holds for every value projection `val` of the queue tokens, which the value-level W3 blocks
share. The full theorem conjoins `spec_consistent_queue`'s body in place of the six IO and EXEC
lines repeated here. The B blocks that tie the dead-arc report to the executor's boot events and
the verifier's report lines are `CORE_037_events` and `CORE_037_verifier` (`CORE_037_B.lean`).
`core040_core041_joint_kills_blind` shows what the shared net builder buys: CORE-041 alone
accepts a builder state machine whose handle shows the empty net, and with CORE-040 over the
same net builder it does not. `core001_place` is CORE-001's citation (a term definition with no
statement of its own). `BuiltNet.toNNet_eq_link` bridges the two arc views of a built net, so a
block stated over `Link.toNNet` of a built net can use the net builder's `toNNet` theorems.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-- ✓ The structure blocks of waves W2 and W3 hold together with the build lines of the IO
blocks, EXEC-010, EXEC-012's build line, TIME-001 and CORE-037, on one model, for every value
projection `val` of the queue tokens. The transition builder `TB` is the reference transition
builder, whose build check is the reference builder `refBuild` that the IO and EXEC-012 blocks are
stated over, and which agrees with TIME-001's reference contract on timings. CORE-021 is stated
over the same `TB`; CORE-040's net builder `NB` and CORE-041's builder state machine `BA` are
built over it (`refNetBuild`, `copyBuilder`), so CORE-041's handle shows CORE-040's built net.
EXEC-042's build block (wave W5) is stated over the same `TB` and `NB`: the net builder rejects a
terminal place that a transition consumes or reads.
Three agreement conjuncts tie the W2 parameters to each other:

* every net `NB` builds holds only definitions of `TB` (`refNetBuild_fromBuilder`), and both
  binding forms keep that (`refBind_fromBuilder`): a net holds only builder outputs, also after
  binding (tracer decision W2);
* the full-width masks of PERF-030's layout at every word size are the mask words of CONC-007's
  compiled net (`refBitmapLayout_maskWords`), so PERF-030 bounds the masks CONC-007 fixes.

The W3 blocks join on the shared parameters: CORE-050's action firing `AF` is stated over the
queue firing `QF` (witness `refActionFire`, a restriction of `RefQFire`), CORE-051 over the
builder `TB`, CORE-052 to CORE-054 and CORE-060 to CORE-063 over `val`, and CORE-053 and CORE-054
are read at the firing through `AF`. `QF` counts to the firing relation `F` of the IO lines and
lifts every firing of it (`QProjectsTo`, `QCovers`, the queue theorem's count guards), which is
what makes CORE-050's cover line exclude the empty `AF`, and every firing of `QF` ends with the
completion of an action or with the timeout outcome `T` of IO-013 (`EndsByActionOrTimeout`,
witness `core050_endsBy`). The transform and the fork write through the context `Cx`: the
transform `Tf f` does whenever the writes of `f` are built through `Cx`
(`refTransform_throughCtx`), the fork always (`refFork_throughCtx`), so `ctx_deposits_outputs`
reaches them as it reaches the produce action. Three agreement conjuncts tie the W3 parameters:

* the action tag: the firings of a built definition `d` that end with its tag's action under the
  table `I` (`TagFire`) are the `AF` firings under the action CORE-051's `interp` names for
  `d.action`, so CORE-051's passthrough line speaks of the actions `AF` reads
  (`structure_default_tag_nil`);
* CORE-054's produce action writes through the context `Cx` of CORE-060 to CORE-063
  (`core054_ctxProduce`);
* the resume of CORE-073 (T) is the queue theorem's initialiser `TSt.init` (CORE-072's witness)
  on the restored counts.

The snapshot blocks are stated at `N := String`, the place names of CORE-073. The compile check
`C` and its verification entry `V` (CORE-043), the place model `M` (CORE-002) and CORE-011's token
factory `K` have no link to the other parameters yet. `V` is linked to no verifier: CORE-043's
witness `refVerifyEntry` is the compile check itself, since the verifier pipeline model
(`Verifier/Pipeline.lean`) does not model an entry check. The place model joins the net builder's
place type in wave W8 (MOD-024), and CORE-011's executor line is the block `CORE_011_B`
(`CORE_011_B.lean`). CORE-037 holds of the reference dead-arc report and message. The skeleton of `spec_consistent_structure`. -/
@[evidence consistent CORE_020 TIME_001 IO_011 IO_012 IO_013 IO_014 EXEC_012 CORE_037
  CORE_002 CORE_021 CORE_040 CORE_041 CORE_042 CORE_043 CONC_007 PERF_030
  EXEC_010 CORE_011 CORE_050 CORE_051 CORE_052 CORE_053 CORE_054 CORE_060 CORE_061 CORE_062
  CORE_063 CORE_073 CORE_073_T EXEC_042_build]
theorem joint_core_structure_sketch {N A Tk Val : Type} [DecidableEq N] [ToString N]
    (val : Tk → Val) :
    ∃ (Build : Trans N → Option String) (F T : FireRel N) (Q : TimingContract)
      (QF : QFireRel N Tk) (TB : TBuilder N A) (NB : NetBuilder TB) (BA : BuilderApi TB)
      (Bind BindMap : BuiltNet N A → (String → Option (Act A)) → BuiltNet N A)
      (C V : BuiltNet N A → Option String)
      (Cmp : (Trans N → Bool) → Reference.Net N → CompiledNet N) (L : Nat → BitmapLayout N)
      (M : PlaceKeyed N Tk) (Rep : DeadArcReport String) (Msg : DeadArc String → String)
      (AF : ActFireRel N Tk) (I : A → ActionRel N Tk) (interp : Act A → ActionRel N Tk)
      (isPT : Act A → Bool) (pt : Nat → Act A) (Fork : ActionFn N Tk)
      (Tf : TransformFn N Tk Val → ActionRel N Tk) (produce : N → Val → ActionRel N Tk)
      (Cx : Ctx N Tk Val) (K : TokenFactory Val)
      (Snap : FinQ String Tk → QSnap String Tk) (Restore : QSnap String Tk → QMarking String Tk)
      (Seed : Option (QSnap String Tk) → QSnap String Tk → Except String (QMarking String Tk))
      (Rs : TimedNet String → QSnap String Tk → Nat → TSt String),
      IO_011 Build F ∧ IO_012 IO_012_check Build F ∧ IO_013 Build F T ∧ IO_014 Build T ∧
      EXEC_012 Build QF ∧ TIME_001 Q ∧ CORE_020 TB ∧ CORE_021 TB ∧ CORE_040 TB NB ∧
      CORE_041 TB NB BA ∧ EXEC_042_build TB NB ∧ CORE_042 Bind BindMap ∧ CORE_043 C V ∧
      CONC_007 Cmp ∧
      (∀ ws, PERF_030 ws (L ws)) ∧ CORE_002 M ∧ CORE_037 Rep Msg ∧
      projBuild TB = Build ∧ TimingAgree TB Q ∧
      (∀ inp b, NB inp = .ok b → b.FromBuilder TB) ∧
      (∀ b r, b.FromBuilder TB → (Bind b r).FromBuilder TB ∧ (BindMap b r).FromBuilder TB) ∧
      (∀ ws n, (List.range n.transitions.length).flatMap ((L ws).masks n) =
        (Cmp (fun _ => false) n).maskWords ws) ∧
      EXEC_010 QF ∧ QProjectsTo QF F ∧ QCovers QF F ∧ CORE_050 QF AF ∧
      EndsByActionOrTimeout QF AF T ∧ CORE_051 interp isPT TB pt ∧ CORE_052 val Fork ∧
      CORE_053 val Tf ∧ CORE_054 val produce ∧ CORE_060 val Cx ∧ CORE_061 val Cx ∧
      CORE_062 val Cx ∧ CORE_063 val Cx ∧ CORE_011 K ∧ CORE_073 Snap Restore Seed ∧
      CORE_073_T Restore Rs ∧
      (∀ f, (∀ t δ w v, f t δ (.ok (w, v)) → Built Cx t (w.map fun x => (x.1, val x.2))) →
        ThroughCtx Cx val (Tf f)) ∧
      ThroughCtx Cx val (ActionFn.rel Fork) ∧
      (∀ (d : TransDef N A) Mq δ e Mq',
        TagFire AF I d Mq δ e Mq' ↔ AF (interp d.action) d.toTrans Mq δ e Mq') ∧
      (∀ p v, produce p v = core054_ctxProduce Cx val p v) ∧
      (∀ X s now0, Rs X s now0 = TSt.init X (qCount (Restore s)) now0) :=
  ⟨refBuild, RefFire, refTimeoutOutcomeFire, refTimingQ, RefQFire, refTransBuild, refNetBuild,
    copyBuilder refTransBuild, refBind, refBindMapKeep, refCompile, refVerifyEntry,
    refCompileWith, refBitmapLayout, refPlacesByName, refDeadArcs, refDeadArcMsg,
    refActionFire, refAnyAction, Act.interp refAnyAction, Act.isPassthrough,
    refRetrievePassthrough, refFork, refTransform val, refProduce val, refCtx val,
    refTokenFactory, refSnapshot, refRestore, refSeed, refResume,
    IO_011_reference, IO_012_reference, IO_013_reference,
    refTimeoutOutcomeFire_eq_refTimedOutFire (N := N) ▸ IO_014_reference, EXEC_012_reference,
    TIME_001_reference, CORE_020_reference, CORE_021_reference, CORE_040_reference _,
    CORE_041_reference _, EXEC_042_build_reference _, CORE_042_reference_keep, CORE_043_reference, CONC_007_reference,
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

/-- **The action-tag conjunct at work**: on a joint model of CORE-050, CORE-051 and the
action-tag conjunct of `joint_core_structure_sketch`, a transition the builder `TB` builds
without an action deposits nothing when a firing ends with the action its tag names. CORE-051's
line 3 gives the definition the passthrough tag, the tag conjunct turns the tag firing into an
`AF` firing under CORE-051's `interp`, and CORE-051's line 1 with CORE-050's line 2 empties the
emission (`core051_default_fire_nil`). -/
theorem structure_default_tag_nil {N A Tk : Type} [DecidableEq N] {QF : QFireRel N Tk}
    {AF : ActFireRel N Tk} {I : A → ActionRel N Tk} {interp : Act A → ActionRel N Tk}
    {isPT : Act A → Bool} {TB : TBuilder N A} {pt : Nat → Act A} (h50 : CORE_050 QF AF)
    (h51 : CORE_051 interp isPT TB pt)
    (htag : ∀ (d : TransDef N A) Mq δ e Mq',
      TagFire AF I d Mq δ e Mq' ↔ AF (interp d.action) d.toTrans Mq δ e Mq')
    {k : Nat} {i : TransIn N A} {x : TB.I} (hb : TB.build k i = .ok x) (hn : i.action = none)
    {Mq Mq' : QueueMarking N Tk} {δ : Delivered N Tk} {e : List (N × Tk)}
    (hf : TagFire AF I (TB.defOf x) Mq δ e Mq') : e = [] :=
  core051_default_fire_nil h50 h51 hb hn ((htag _ _ _ _ _).1 hf)

/-- **The snapshot's count projection** on a joint model of CORE-073: for every snapshot
function and restore that meet CORE-073, the count projection of every snapshot is a canonical
count marking (`Reference.Marking`'s form, as the conformance corpus uses it) holding the counts
of the snapshotted marking. Lines 1 and 2 with `core073_restore_eq` give it; the reference case is
`count_snapshot`. -/
theorem structure_snapshot_counts {T : Type} {Snap : FinQ String T → QSnap String T}
    {Restore : QSnap String T → QMarking String T}
    {Seed : Option (QSnap String T) → QSnap String T → Except String (QMarking String T)}
    (h : CORE_073 Snap Restore Seed) (F : FinQ String T) :
    Canon (snapCounts (Snap F)) ∧ ∀ k, get (snapCounts (Snap F)) k = qCount F.M k := by
  refine ⟨canon_snapCounts (h.2.1 F), fun k => ?_⟩
  rw [get_snapCounts, ← core073_restore_eq h (h.2.1 F).keysNodup, h.1 F]
  rfl

/-- CORE-040 and CORE-041 over one net builder kill the blind builder state machine, whose handle
shows the empty net whatever was added: CORE-041 alone accepts it beside a net builder that
drops declared places, and CORE-040's lines 2 and 4 make the builder accept a declared place and
keep it, so the blind handle no longer shows the built net. -/
theorem core040_core041_joint_kills_blind {N A : Type} [DecidableEq N] {B : TBuilder N A}
    (NB : NetBuilder B) (p : N) (h40 : CORE_040 B NB) : ¬ CORE_041 B NB (core041_blindBuilder B) := by
  obtain ⟨b, hb⟩ := h40.2.2.2 (NetIn.ofOps [.place p]) rfl
  exact core041_blind_killed_declared NB p
    ⟨b, hb, h40.2.1 _ b hb p (Or.inl (by simp [NetIn.ofOps, NetIn.addOp, NetIn.empty]))⟩

/-- CORE-001's place has a string name and a token type, which the place model `PlaceKeyed`
records (`name`, `ty`; the glossary's `PlaceName`), and both can be read back from a place
object (AC1, the test derivation). The place identities that exist, by name and by name and token
type, are the two models of the CORE-002 block. -/
@[evidence cites "CORE-001" "Each place has a string name and an associated token value type."]
theorem core001_place {Nm Ty : Type} (n : Nm) (t : Ty) :
    (refPlacesByName (Nm := Nm) (Ty := Ty)).name (n, t) = (n : PlaceName Nm) ∧
      (refPlacesByName (Nm := Nm) (Ty := Ty)).ty (n, t) = t ∧
      CORE_002 (refPlacesByName (Nm := Nm) (Ty := Ty)) ∧
      CORE_002 (refPlacesByNameType (Nm := Nm) (Ty := Ty)) :=
  ⟨rfl, rfl, CORE_002_byName, CORE_002_byNameType⟩

/-- The arc view of a built net (`BuiltNet.toNNet`, Spec/GlossaryBuild.lean) is the arc view of its
untimed net (`Link.toNNet b.toNet`), so a block stated over `Link.toNNet` of a built net (such as
VER-001's `inert_covers`) can use `refNetBuild_arcsDeclared_toNNet` without restating it. -/
theorem _root_.Libpetri.Reference.BuiltNet.toNNet_eq_link {N A : Type} (b : BuiltNet N A) :
    b.toNNet = Link.toNNet b.toNet := by
  simp only [BuiltNet.toNNet, Link.toNNet, BuiltNet.toNet, List.map_map]
  rfl

end Libpetri.Spec
