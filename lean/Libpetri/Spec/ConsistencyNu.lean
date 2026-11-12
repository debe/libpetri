import Mathlib.Data.String.Basic
import Libpetri.Spec.GlossaryQueue
import Libpetri.Reference.Nu
import Libpetri.Spec.Req.CORE_022
import Libpetri.Spec.Req.IO_011
import Libpetri.Spec.Req.EXEC_010
import Libpetri.Spec.Req.EXEC_012
import Libpetri.Spec.Req.NU_001
import Libpetri.Spec.Req.NU_020
import Libpetri.Spec.Req.NU_022
import Libpetri.Spec.Req.NU_010
import Libpetri.Spec.Req.NU_011
import Libpetri.Spec.Req.NU_021
import Libpetri.Spec.Req.NU_054
import Libpetri.Spec.Req.CONC_008

set_option linter.missingDocs true

/-!
# Consistency of the ν requirements with the CORE, IO and queue requirements (skeleton)

The target of this module is one theorem, `spec_consistent_nu`, that extends
`spec_consistent_queue` (`Spec/ConsistencyQueue.lean`) by the ν blocks of wave W9 on one joint
model. Wave W9's tracer leaves it as `joint_nu_sketch`, which joins NU-020's four blocks, NU-022
and NU-001 to the builder, the firing relation and the queue firing of the CORE, IO and EXEC
blocks. Conjoining blocks over independent parameters proves nothing on its own; what counts are
the agreement conjuncts that tie each ν parameter to a witness the existing blocks use:

* **Without a match, a ν firing is a queue firing** (`NuRestrictsTo NF QF`). `QF` counts to the
  firing relation `F` of the CORE and IO blocks and lifts every firing of it (`QProjectsTo`,
  `QCovers`), so every count and queue block speaks of the match-free ν firings. `Reference.Trans`
  carries no match, so CORE-022 and IO-001 to IO-005 stay stated over match-free transitions
  (ruling D30 (a)); this conjunct is how they reach `NF`.
* **The ν builder extends the plain builder** (`NuBuildExtends NB Build`): on a transition without
  a match, and on one the plain builder `Build` of IO-011 and EXEC-012 rejects, the ν builder
  answers what `Build` answers. So the match checks run after every other build-time check.
* **The chosen name is the selection's answer** (`NuSelectsBy NF S`), with NU-022 over the same
  `S`. NU-022 has one model per name order (`NU_022_iff_ref`), so this fixes every matched
  firing's choice.
* **The name order is NU-001's**: the ν blocks are stated at the name type `String` with its
  linear order, and the name implementation `I` of NU-001 orders the names of any two strings
  as that order does (`I.lt (I.ofValue a) (I.ofValue b) ↔ a < b`), so the tie-break of the
  selection is NU-001's name order. The reference names `refNameImpl` meet it
  (`refNameImpl_lt_iff`).
* **Every enabled matched transition fires** (`NuCovers NF`, the anti-vacuity conjunct, stated
  under the `Selected` name, nu.md skeptic S8): the ν blocks are safety lines, and the relation
  that never fires satisfies all of them (`nu_coverage_excludes_empty`).
* **The enablement check passes on every firing** (`NuChecksFirings NF NC`): the check `NC` of
  CONC-004 and both CONC-008 blocks passes for every transition that builds whenever `NF` fires
  it, so the ν-match phase of CONC-008 is the enablement NU-020 asks of the firing.
* **Every call to the minter is answered** (`MintTotal Mi`, the coverage conjunct of NU-010 and
  NU-011): the mint lines speak of runs only, and a minter with no mint step meets all of them.
* **The default scope is drawn, not fixed** (`DefaultUnfixed D`, the coverage conjunct of
  NU-011's default scope, with NU_011_default over the same draw `D`), and every drawn default is
  an accepted scope (`∀ k s, D k s → Vs s = true`), so NU-011's format and lineage lines cover the
  names minted under a default scope.
* **One classifier** (`Cl`) carries NU-051's fragment lines (the consume role among them),
  NU-010's declared-mint lines and NU-054's verifier lines, so the consume-role admission and the
  no-role and mint lines constrain one function.

The witnesses, one per role: the reference builder `refBuild`, the reference firing `RefFire`, the
reference queue firing `RefQFire`, the reference match and ν builders `refMatchBuild` and
`refNuBuild`, the reference ν firing `RefNuFire`, the reference selection `refSelect`, the
reference names `refNameImpl`, the reference enablement check `refNuEnableCheck`, the reference
minter `refMintSys` with its scope check `refValidScope`, the reference default draw
`refDefaultDraw`, and the shipped classifier `refClassify`. The agreement conjuncts are proved by
`refQFire_projectsTo`, `refQFire_covers`, `refNuFire_restrictsTo`, `refNuBuild_extends`,
`refNuFire_selectsBy`, `refNameImpl_lt_iff`, `refNuFire_covers`, `refNuFire_checks`,
`refMintSys_total`, `refDefaultDraw_unfixed` and `nu011_default_draw_accepted`.

The fan-out blocks over the same ν firing relation `NF` (NU-021's equivariance, NU-001's rename
line, NU-054's relay check) and the same ν builder `NB` (NU-054's relay build checks) join here.

What waits for later waves: the full `spec_consistent_nu` conjoins `spec_consistent_queue`'s body in
place of the six CORE, IO and EXEC lines repeated here. NU-040's lines are predicates on nets and
markings (the joined-or-dead-lettered property, the declared mints), NU-050's lines are over the
verifier routes, and NU-030 and NU-060 are over the composition rewrite and merge
(`NU_060_with_MOD_021`); they join the verifier and composition theorems of waves W10 and W11.
The timed ν lines (TIME-012's ν join, NU-050's timed line) join RefExec's consistency theorem, on
the firing kernel instantiated with `RefNuFire`.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-- NU-001's reference name order is the linear order on `String` the ν blocks are stated with,
so the selection's tie-break orders names as NU-001 does. -/
theorem refNameImpl_lt_iff (a b : String) :
    refNameImpl.lt (refNameImpl.ofValue a) (refNameImpl.ofValue b) ↔ a < b := Iff.rfl

/-- **The coverage conjunct excludes the empty relation.** The ν firing relation that never fires
satisfies NU-020's enablement, take and frame blocks (each line speaks of firings only), but not
`NuCovers`: on AC1's marking the join is enabled on its counts, X is its selected name, and the
empty emission is offered, so a covering relation must fire there. -/
theorem nu_coverage_excludes_empty :
    NU_020_enable (fun _ _ _ _ _ _ => False : NuFireRel Nat Nat Nat) ∧
      NU_020_take (fun _ _ _ _ _ _ => False : NuFireRel Nat Nat Nat) ∧
      NU_020_frame (fun _ _ _ _ _ _ => False : NuFireRel Nat Nat Nat) ∧
      ¬ NuCovers (fun _ _ _ _ _ _ => False : NuFireRel Nat Nat Nat) := by
  refine ⟨⟨fun _ _ _ _ _ _ _ _ h => h.elim, fun _ _ _ _ _ _ _ _ h => h.elim,
      fun _ _ _ _ _ _ _ _ h => h.elim⟩,
    ⟨fun _ _ _ _ _ _ _ _ h => h.elim, fun _ _ _ _ _ _ _ _ h => h.elim⟩,
    ⟨fun _ _ _ _ _ _ _ _ h => h.elim, fun _ _ _ _ _ _ _ _ h => h.elim,
      fun _ _ _ _ _ _ _ _ h => h.elim, fun _ _ _ _ _ _ _ _ h => h.elim,
      fun _ _ _ _ _ _ _ _ h => h.elim⟩, fun h => ?_⟩
  obtain ⟨_, _, hf⟩ := h (nu020_join .one .one) nu020_ms rfl nu020_ac1 1
    (refSelect_eq_some_iff.1 (by decide)) (by decide) [] ⟨.action 0, rfl⟩
    (fun r hr => by simp [nu020_ms] at hr)
  exact hf

/-- **The enablement check passes on every firing**: for every transition that builds, whenever
`NF` fires it, the whole enablement check `NC` passes on the marking it fired from. -/
def NuChecksFirings {N V Nm : Type} [DecidableEq N] (NF : NuFireRel N V Nm)
    (NC : NuEnableCheck N V Nm) : Prop :=
  ∀ t : NuTrans N (KeyFn V Nm), NuBuilds t → ∀ M c δ e M', NF t M c δ e M' → NC.check t M = true

/-- The reference enablement check passes on every reference ν firing: a firing is ν-enabled
(`refNuFire_nuEnabled`), and on a transition that builds the reference check passes exactly when
it is ν-enabled (`refNuEnableCheck_enabled`). -/
theorem refNuFire_checks {N V Nm : Type} [DecidableEq N] [LinearOrder Nm] :
    NuChecksFirings (RefNuFire (N := N) (V := V) (Nm := Nm)) refNuEnableCheck :=
  fun _ hb _ _ _ _ _ hf => (refNuEnableCheck_enabled hb.1 _).2 (refNuFire_nuEnabled hf)

/-- ✓ Worked example of one model for the ν requirements. On AC1's marking (branch A holds X, Y
and branch B holds Y, X) the reference join is enabled on its counts and on names, the enablement
check passes, the selection picks X (both names have a token at time 0, and X comes first in the
name order), and the firing takes X from both branches; an action of the fork that calls
`freshName()` is answered `fork#s:0` under the scope `s`; and the shipped classifier gives that
fork the mint role when it is declared. One builder, one firing relation, one selection, one
minter, one default draw and one classifier meet NU-020's four blocks, NU-022, NU-001 (both
blocks), NU-021, NU-054's three blocks, CONC-008's ν-match block, NU-010's and NU-011's lines and
NU-051's fragment lines, together with CORE-022, IO-011, EXEC-010, EXEC-012, CONC-004 and CONC-008,
for every place type and token value type, with names in `String`; the agreement conjuncts tie
each ν parameter to the one the other blocks use (the module docstring lists them). The skeleton
of `spec_consistent_nu`. -/
@[evidence consistent CORE_022 IO_011 EXEC_010 EXEC_012 NU_020_build NU_020_enable NU_020_take
  NU_020_frame NU_022 NU_001 NU_001_rename NU_021 NU_054_build NU_054_check CONC_004 CONC_008
  CONC_008_nu NU_010_unique NU_010_replay NU_011_format NU_011_lineage NU_011_default
  NU_010_classify NU_054_verifier NU_051]
theorem joint_nu_sketch {N V : Type} [DecidableEq N] [ToString N] :
    ∃ (Build : Trans N → Option String) (F : FireRel N) (QF : QFireRel N (Stamped V))
      (MB : List (N × KeyFn V String) → Option String)
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
      NuChecksFirings NF NC ∧ MintTotal Mi ∧ DefaultUnfixed D ∧ (∀ k s, D k s → Vs s = true) :=
  ⟨refBuild, RefFire, RefQFire, refMatchBuild, refNuBuild, RefNuFire, refSelect, refNameImpl,
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

end Libpetri.Spec
