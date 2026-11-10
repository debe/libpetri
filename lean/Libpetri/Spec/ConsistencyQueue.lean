import Libpetri.Spec.ConsistencyTime
import Libpetri.Spec.GlossaryQueue
import Libpetri.Spec.Req.EXEC_010
import Libpetri.Spec.Req.EXEC_012
import Libpetri.Spec.Req.EXEC_013
import Libpetri.Spec.Req.EXEC_020

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
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Novel.TimedScg (Timing)

/-- ✓ The CORE and IO requirement blocks, TIME-001, EXEC-002, the TIME blocks and the queue
blocks EXEC-010, EXEC-012, EXEC-013 and EXEC-020 hold together on one model: the model of
`spec_consistent_coreIO_time`, with one builder for the IO build lines and EXEC-012's, and a
queue firing relation whose firings, counted, are the firings of the same firing relation `F`,
and which lifts every firing of `F`. The witnesses are the reference builder, the reference
firing relation, the reference timing contract, the reference ready order, the timed reference
step and the reference queue firing. -/
@[evidence consistent CORE_022 CORE_030 CORE_031 CORE_032 CORE_033 CORE_034 CORE_035 CORE_036
  IO_001 IO_002 IO_003 IO_004 IO_005 IO_007 IO_010 IO_011 IO_012 IO_013 IO_014 IO_015 IO_016
  TIME_001 TIME_002 TIME_003 TIME_004 TIME_005 TIME_006 TIME_010 TIME_011 TIME_012 TIME_013
  TIME_015 EXEC_002 EXEC_010 EXEC_012 EXEC_013 EXEC_020]
theorem spec_consistent_queue {N Tk : Type} [DecidableEq N] [ToString N] :
    ∃ (Build : Trans N → Option String) (F T : FireRel N) (Q : TimingContract) (O : ReadyOrder)
      (R : TRel N) (QF : QFireRel N Tk),
      (CORE_022 F ∧ CORE_030 F ∧ CORE_031 F ∧ CORE_032 F ∧ CORE_033 F ∧ CORE_034 F ∧
        CORE_035 F ∧ CORE_036 F ∧ IO_001 F ∧ IO_002 F ∧ IO_003 F ∧ IO_004 F ∧ IO_005 F ∧
        IO_010 F ∧ IO_011 Build F ∧ IO_012 IO_012_check Build F ∧ IO_013 Build F T ∧
        IO_014 Build T) ∧
      ((∃ K, IO_007 K) ∧ (∃ V : OutputValidator N, IO_015 V) ∧ (∃ E : BranchEnum N, IO_016 E)) ∧
      (TIME_001 Q ∧ Q.earliest = Timing.earliest ∧ Q.latest = Timing.latest) ∧
      EXEC_002 O ∧
      ProjectsTo R F ∧ FramesMarking R ∧ time012_FramesClock R ∧ Covers R ∧
      CoversReap R ∧ CoversDelay R ∧ TIME_002 R ∧ TIME_003 R ∧ TIME_004 R ∧ TIME_005 R ∧
      TIME_006 R ∧ TIME_010 R ∧ TIME_011 R ∧ TIME_012 R ∧ TIME_013 R ∧ TIME_015 R ∧
      QProjectsTo QF F ∧ QCovers QF F ∧
      EXEC_010 QF ∧ EXEC_012 Build QF ∧ EXEC_013 QF ∧ EXEC_020 QF :=
  ⟨refBuild, RefFire, refTimeoutOutcomeFire, refTimingQ, refReadyOrder, RefTStep, RefQFire,
    ⟨CORE_022_reference, CORE_030_reference, CORE_031_reference, CORE_032_reference,
      CORE_033_reference, CORE_034_reference, CORE_035_reference, CORE_036_reference,
      IO_001_reference, IO_002_reference, IO_003_reference, IO_004_reference, IO_005_reference,
      IO_010_reference, IO_011_reference, IO_012_reference, IO_013_reference,
      refTimeoutOutcomeFire_eq_refTimedOutFire (N := N) ▸ IO_014_reference⟩,
    ⟨⟨_, IO_007_reference⟩, ⟨_, IO_015_reference (N := N)⟩, ⟨_, IO_016_reference (N := N)⟩⟩,
    ⟨TIME_001_reference, rfl, rfl⟩, EXEC_002_reference,
    refTStep_projectsTo, refTStep_framesMarking, TIME_012_reference_framesClock,
    refTStep_covers, refTStep_coversReap, refTStep_coversDelay, TIME_002_reference,
    TIME_003_reference, TIME_004_reference, TIME_005_reference, TIME_006_reference,
    TIME_010_reference, TIME_011_reference, TIME_012_reference, TIME_013_reference,
    TIME_015_reference, refQFire_projectsTo, refQFire_covers,
    EXEC_010_reference, EXEC_012_reference, EXEC_013_reference, EXEC_020_reference⟩

end Libpetri.Spec
