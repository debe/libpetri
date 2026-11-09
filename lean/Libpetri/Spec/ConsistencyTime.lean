import Libpetri.Spec.Consistency
import Libpetri.Spec.GlossaryTime
import Libpetri.Spec.Req.TIME_001
import Libpetri.Spec.Req.TIME_002
import Libpetri.Spec.Req.TIME_003
import Libpetri.Spec.Req.TIME_004
import Libpetri.Spec.Req.TIME_005
import Libpetri.Spec.Req.TIME_006
import Libpetri.Spec.Req.TIME_010
import Libpetri.Spec.Req.TIME_011
import Libpetri.Spec.Req.TIME_012
import Libpetri.Spec.Req.TIME_013
import Libpetri.Spec.Req.TIME_015
import Libpetri.Spec.Req.EXEC_002

set_option linter.missingDocs true

/-!
# Consistency of the CORE + IO firing requirements with the TIME requirements

`spec_consistent_coreIO_time` extends `spec_consistent_coreIO` to one joint model. A single
untimed firing relation `F` satisfies the CORE and IO blocks (the witnesses of
`spec_consistent_coreIO`); a single timed step relation `R` satisfies the TIME blocks over `TRel`
(TIME-002 to TIME-006, TIME-010 to TIME-013 and TIME-015), and its firings are firings of that
same `F` (`ProjectsTo R F`), nothing else changes the marking (`FramesMarking R`) and a firing
leaves the clock reading as it is (`time012_FramesClock R`). The timing contract `Q` of TIME-001
is tied to the timings the TIME blocks read: its `earliest` and `latest` are the accessors of
`Timing` that `TimingOf`, `refPolicy` and the blocks use. The ready order `O` of EXEC-002 is
quantified over every pass input, so in particular over every input `ReadyIn.ofTSt X prio s ts`
read off a state of `R`; nothing more ties it to `R`, since the atomic step relation has no pass
and no choice among ready transitions (that is the Phase 2 cycle relation). The output-port
interfaces of IO-007, IO-015 and IO-016 are separate models, as in `spec_consistent_coreIO`. The
witness for `R` is the timed reference step `RefTStep`.

The clock frame is not a sentence of any TIME section. Without it a firing fused with a hidden
delay satisfies TIME-012 (`TIME_012_gap_fireAdvancesClock`), so it is conjoined here, next to
`FramesMarking`.

Most `on … shall` and `while …, never` lines of a TIME block also hold of the relation that takes
no step at all (`TIME_010_empty`), so a conjunction of such lines alone could be satisfied by
doing nothing. The coverage conjuncts rule that out: `Covers R` (every ready transition can take
every reference firing it has), `CoversReap R` (every expired transition can be reaped) and
`CoversDelay R` (the clock can always advance). `time_coverage_excludes_empty` shows that the
empty relation fails the whole timed conjunction. TIME-003, TIME-005 and TIME-013 also fail it
on their own, by their reap-availability lines.

The candidate readings of TIME-014's second bullet (`ClashesTime.lean`) are not conjoined:
ruling D9 is open, and one of them conflicts with EXEC-002 by design.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Novel.TimedScg (Timing)

/-- ✓ The CORE and IO requirement blocks, TIME-001, EXEC-002 and the TIME blocks over the timed
step relation hold together on one model: one firing relation `F` for the CORE and IO blocks,
whose firings are the firings of the timed step relation `R` of the TIME blocks; a timing
contract whose bounds are the `Timing` accessors the TIME blocks read; and a ready order for
every pass input. The witnesses are the reference firing relation, the reference timing
contract, the reference ready order and the timed reference step, whose firings take no time on
the firing clock, whose delays and reaps leave the marking as it is, and which covers every
ready firing, every expired reap and every delay. -/
@[evidence consistent CORE_022 CORE_030 CORE_031 CORE_032 CORE_033 CORE_034 CORE_035 CORE_036
  IO_001 IO_002 IO_003 IO_004 IO_005 IO_007 IO_010 IO_011 IO_012 IO_013 IO_014 IO_015 IO_016
  TIME_001 TIME_002 TIME_003 TIME_004 TIME_005 TIME_006 TIME_010 TIME_011 TIME_012 TIME_013
  TIME_015 EXEC_002]
theorem spec_consistent_coreIO_time {N : Type} [DecidableEq N] [ToString N] :
    ∃ (Build : Trans N → Option String) (F T : FireRel N) (Q : TimingContract) (O : ReadyOrder)
      (R : TRel N),
      (CORE_022 F ∧ CORE_030 F ∧ CORE_031 F ∧ CORE_032 F ∧ CORE_033 F ∧ CORE_034 F ∧
        CORE_035 F ∧ CORE_036 F ∧ IO_001 F ∧ IO_002 F ∧ IO_003 F ∧ IO_004 F ∧ IO_005 F ∧
        IO_010 F ∧ IO_011 Build F ∧ IO_012 IO_012_check Build F ∧ IO_013 Build F T ∧
        IO_014 Build T) ∧
      ((∃ K, IO_007 K) ∧ (∃ V : OutputValidator N, IO_015 V) ∧ (∃ E : BranchEnum N, IO_016 E)) ∧
      (TIME_001 Q ∧ Q.earliest = Timing.earliest ∧ Q.latest = Timing.latest) ∧
      EXEC_002 O ∧
      ProjectsTo R F ∧ FramesMarking R ∧ time012_FramesClock R ∧ Covers R ∧
      CoversReap R ∧ CoversDelay R ∧ TIME_002 R ∧ TIME_003 R ∧ TIME_004 R ∧ TIME_005 R ∧
      TIME_006 R ∧ TIME_010 R ∧ TIME_011 R ∧ TIME_012 R ∧ TIME_013 R ∧ TIME_015 R :=
  ⟨refBuild, RefFire, refTimeoutOutcomeFire, refTimingQ, refReadyOrder, RefTStep,
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
    TIME_015_reference⟩

/-- The relation that takes no step. -/
def timeEmptyRel : TRel Nat := fun _ _ _ _ => False

/-- The relation that takes no step satisfies TIME-010, as it satisfies every `on … shall` and
`while …, never` line. -/
theorem TIME_010_empty : TIME_010 timeEmptyRel :=
  fun _ => ⟨fun _ _ _ _ _ h => h.elim, fun _ _ _ _ h => h.elim, fun _ _ _ _ _ _ h => h.elim,
    fun _ _ _ ⟨_, h⟩ => h.elim, fun _ _ _ ⟨_, h⟩ => h.elim⟩

/-- The coverage conjuncts of `spec_consistent_coreIO_time` exclude the relation that takes no
step: in AC1's net of TIME-010 the source is ready at `T = 10` and has a reference firing, which
the empty relation does not cover. -/
theorem time_coverage_excludes_empty :
    ¬ (ProjectsTo timeEmptyRel RefFire ∧ FramesMarking timeEmptyRel ∧
      time012_FramesClock timeEmptyRel ∧ Covers timeEmptyRel ∧ CoversReap timeEmptyRel ∧
      CoversDelay timeEmptyRel ∧ TIME_002 timeEmptyRel ∧ TIME_003 timeEmptyRel ∧
      TIME_004 timeEmptyRel ∧ TIME_005 timeEmptyRel ∧ TIME_006 timeEmptyRel ∧
      TIME_010 timeEmptyRel ∧ TIME_011 timeEmptyRel ∧ TIME_012 timeEmptyRel ∧
      TIME_013 timeEmptyRel ∧ TIME_015 timeEmptyRel) := by
  rintro ⟨-, -, -, hc, -⟩
  obtain ⟨_, h, -⟩ := hc time010_X time010_s0 time010_src [0] time010_m1
    (by simp [time010_X]) (by decide) ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
  exact h

end Libpetri.Spec
