import Libpetri.Spec.ConsistencyTime
import Libpetri.Spec.GlossaryQueue
import Libpetri.Spec.Req.EXEC_010
import Libpetri.Spec.Req.EXEC_012
import Libpetri.Spec.Req.EXEC_013
import Libpetri.Spec.Req.EXEC_020
import Libpetri.Spec.Req.CORE_010
import Libpetri.Spec.Req.CORE_013
import Libpetri.Spec.Req.CORE_070
import Libpetri.Spec.Req.CORE_072
import Libpetri.Spec.Req.IO_017
import Libpetri.Spec.Req.CONC_004
import Libpetri.Spec.Req.CONC_008
import Libpetri.Spec.Req.CONC_022
import Libpetri.Spec.Req.CONC_025
import Libpetri.Spec.Req.CONC_021
import Libpetri.Spec.Req.CORE_003

set_option linter.missingDocs true

/-!
# Consistency of the queue requirements with the CORE, IO and TIME requirements

`spec_consistent_queue` extends `spec_consistent_coreIO_time` by the token-order requirements
([EXEC-010], [EXEC-012], [EXEC-013], [EXEC-020]) on one joint model. The builder `Build`, the
firing relation `F`, the timing contract, the ready order and the timed step relation are those
of `spec_consistent_coreIO_time`; a queue firing relation `Q` (glossary `QFireRel`) satisfies
the four queue blocks, and it is tied to the same `F`: every queue firing, counted, is a firing
of `F` (`QProjectsTo Q F`), and every firing of `F` lifts to a queue firing from every queue
marking with its counts (`QCovers Q F`). EXEC-012's build lines are stated over the same `Build`
as IO-011 to IO-014: the reference builder `refBuild`, which runs the [EXEC-012] input-and-read
check of ruling D15 after the input-arc checks and before the output-spec checks.

The witnesses are `refBuild`, `RefFire`, `refTimeoutOutcomeFire`, `refTimingQ`,
`refReadyOrder`, `RefTStep` and the reference queue firing `RefQFire`, whose count projection is
`RefFire` (`count_QFire`).

Like most `on … shall` lines, the four queue blocks hold of the relation that takes no step.
The coverage conjunct `QCovers Q F` rules that out (`exec020_empty_not_covers`).

The blocks of wave W0 over these models join on the same witnesses. [CORE-010] and [CORE-013]
are stated over the same queue firing relation `QF`. [CORE-072] is stated over an initialiser
`I` (witness `TSt.init`), the same timed step relation `R` and the same `QF`. [CORE-070] is
stated over marking operations `Ops` on the queue marking (witness `refQOps`, whose state is
the queue marking `RefQFire` steps, read by `view` as it is). [CONC-004] and [CONC-008] are
stated over one enablement check `EC` (witness `refEnableCheck`), whose answer CONC-008 ties to
the glossary's `Enabled`, the predicate the CORE blocks state `F` over. [IO-017]'s place-set
function sits with IO-016's branch enumeration: both read the output spec alone. [CONC-022] and
[CONC-025] are stated over one token store of the precompiled backend and its materialiser,
and CORE-070 over the same store as well (witnesses `core070_ringMarking`, the ring pool
`refRingStore` with its removal guarded by the count as every caller of `ring_remove_first`
guards it, and `ringMarkingMaterialiser`): one store satisfies the marking interface of CORE-070
and the token storage of CONC-022 (`CORE_070_ringStore`, `CONC_022_ringMarking`), and the
materialised marking is its queue view, which is what CONC-025 says. The ring store is a
separate state from the queue marking `QF` steps, as the output-port interfaces are; tying the
materialiser's steps to `QF` is the executor model's (RefExec, W5).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Novel.TimedScg (Timing)

/-- CONC-022 holds of the ring pool with its removal guarded by the count
(`core070_ringMarking`, the store CORE-070's `CORE_070_ringStore` is about): the store differs
from `refRingStore` only on a removal at an unmarked place, which CONC-022's removal line does not
constrain, and on a marked place the guard picks `refRingStore`'s removal. So one store satisfies
both CORE-070 and CONC-022. -/
theorem CONC_022_ringMarking : CONC_022 core070_ringMarking := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := CONC_022_reference
  refine ⟨h1, h2, fun s p hok hm => ?_, h4, h5⟩
  have hc : s.cnt p ≠ 0 := by
    intro h0
    apply hm
    show (s.proj p).length = 0
    rw [Pool.proj_length hok.1 hok.2, h0]
  have he : core070_ringMarking.removeFirst s p = refRingStore.removeFirst s p := by
    simp [core070_ringMarking, hc]
  rw [he]
  exact h3 s p hok hm

/-- The reference materialiser over the guarded ring store `core070_ringMarking`: the same
precompiled backend state, start states, steps and store as `refMaterialiser`, materialising with
`Pool.proj`. -/
def ringMarkingMaterialiser : Materialiser core070_ringMarking where
  σ := PBState
  init st := Pool.WF st.ring
  step st st' := ∃ net emit, st' = pcCycle net emit st ∨
    ∃ tid, pcRecheck net st tid = true ∧ st' = pcFire net emit st tid
  store st := st.ring
  mat st := st.ring.proj

/-- CONC-025 holds of the materialiser over the guarded ring store, as of `refMaterialiser`: it
materialises by reading the store. -/
theorem CONC_025_ringMarking : CONC_025 core070_ringMarking ringMarkingMaterialiser :=
  fun _ _ _ _ _ _ => rfl

/-- ✓ The CORE and IO requirement blocks, TIME-001, EXEC-002, the TIME blocks and the queue
blocks EXEC-010, EXEC-012, EXEC-013 and EXEC-020 hold together on one model: the model of
`spec_consistent_coreIO_time`, with one builder for the IO build lines and EXEC-012's, and a
queue firing relation whose firings, counted, are the firings of the same firing relation `F`,
and which lifts every firing of `F`. The witnesses are the reference builder, the reference
firing relation, the reference timing contract, the reference ready order, the timed reference
step and the reference queue firing. The same queue firing relation satisfies CORE-010, CORE-013
and, with the reference initialiser and the same step relation, CORE-072; the same queue firing relation keeps
every typing of CORE-003; the queue marking's operations satisfy CORE-070; one enablement check
satisfies CONC-004 and CONC-008; and the ring pool, with its removal guarded by the count, its
materialiser and its consume program satisfy CORE-070, CONC-022, CONC-025 and CONC-021
together. -/
@[evidence consistent CORE_022 CORE_030 CORE_031 CORE_032 CORE_033 CORE_034 CORE_035 CORE_036
  IO_001 IO_002 IO_003 IO_004 IO_005 IO_007 IO_010 IO_011 IO_012 IO_013 IO_014 IO_015 IO_016
  TIME_001 TIME_002 TIME_003 TIME_004 TIME_005 TIME_006 TIME_010 TIME_011 TIME_012 TIME_013
  TIME_015 EXEC_002 EXEC_010 EXEC_012 EXEC_013 EXEC_020 CONC_005 CONC_023 CONC_024 CORE_010
  CORE_013 CORE_070 CORE_072 IO_017 CONC_004 CONC_008 CONC_022 CONC_025 CORE_003 CONC_021]
theorem spec_consistent_queue {N Tk : Type} [DecidableEq N] [ToString N] :
    ∃ (Build : Trans N → Option String) (F T : FireRel N) (Q : TimingContract)
      (C : TimingCompile) (O : ReadyOrder) (R : TRel N) (QF : QFireRel N Tk) (I : Init N)
      (Ops : MarkingOps N Tk) (EC : EnableCheck N),
      (CORE_022 F ∧ CORE_030 F ∧ CORE_031 F ∧ CORE_032 F ∧ CORE_033 F ∧ CORE_034 F ∧
        CORE_035 F ∧ CORE_036 F ∧ IO_001 F ∧ IO_002 F ∧ IO_003 F ∧ IO_004 F ∧ IO_005 F ∧
        IO_010 F ∧ IO_011 Build F ∧ IO_012 IO_012_check Build F ∧ IO_013 Build F T ∧
        IO_014 Build T) ∧
      ((∃ K, IO_007 K) ∧ (∃ V : OutputValidator N, IO_015 V) ∧
        (∃ (E : BranchEnum N) (A : AllPlaces N), IO_016 E ∧ IO_017 A)) ∧
      (TIME_001 Q ∧ Q.earliest = Timing.earliest ∧ Q.latest = Timing.latest ∧ CONC_024 Q C) ∧
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
        CORE_070 S ∧ CONC_022 S ∧ CONC_025 S X ∧ CONC_021 S P) :=
  ⟨refBuild, RefFire, refTimeoutOutcomeFire, refTimingQ, refTimingCompile, refReadyOrder,
    RefTStep, RefQFire, TSt.init, refQOps, refEnableCheck,
    ⟨CORE_022_reference, CORE_030_reference, CORE_031_reference, CORE_032_reference,
      CORE_033_reference, CORE_034_reference, CORE_035_reference, CORE_036_reference,
      IO_001_reference, IO_002_reference, IO_003_reference, IO_004_reference, IO_005_reference,
      IO_010_reference, IO_011_reference, IO_012_reference, IO_013_reference,
      refTimeoutOutcomeFire_eq_refTimedOutFire (N := N) ▸ IO_014_reference⟩,
    ⟨⟨_, IO_007_reference⟩, ⟨_, IO_015_reference (N := N)⟩,
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

end Libpetri.Spec
