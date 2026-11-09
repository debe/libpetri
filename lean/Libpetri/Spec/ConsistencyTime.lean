import Libpetri.Spec.Consistency
import Libpetri.Spec.GlossaryTime
import Libpetri.Spec.Req.TIME_010

set_option linter.missingDocs true

/-!
# Consistency of the CORE + IO firing requirements with the TIME requirements

`spec_consistent_coreIO_time` extends `spec_consistent_coreIO`: the CORE and IO blocks hold
together (the same witnesses as there), and one timed step relation `R` satisfies the TIME
blocks while its firings are reference firings (`ProjectsTo R RefFire`) and nothing else changes
the marking (`FramesMarking R`). The witness is the timed reference step `RefTStep`.

Every `on … shall` and `while …, never` line of a TIME block also holds of the relation that
takes no step at all, so a conjunction of TIME blocks alone could be satisfied by doing nothing.
The coverage conjuncts rule that out: `Covers R` (every ready transition can take every reference
firing it has), `CoversReap R` (every expired transition can be reaped) and `CoversDelay R` (the
clock can always advance). `time_coverage_excludes_empty` shows that the empty relation fails
them.

This is the Wave 0 skeleton: TIME-010 is the only TIME block so far. The other TIME blocks join
the conjunction as they are written.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-- ✓ The CORE and IO requirement blocks and TIME-010 hold together: the CORE/IO witnesses of
`spec_consistent_coreIO`, and the timed reference step, whose firings are reference firings,
whose delays and reaps leave the marking as it is, and which covers every ready firing, every
expired reap and every delay. -/
@[evidence consistent CORE_022 CORE_030 CORE_031 CORE_032 CORE_033 CORE_034 CORE_035 CORE_036
  IO_001 IO_002 IO_003 IO_004 IO_005 IO_007 IO_010 IO_011 IO_012 IO_013 IO_014 IO_015 IO_016
  TIME_010]
theorem spec_consistent_coreIO_time {N : Type} [DecidableEq N] [ToString N] :
    ((∃ (Build : Trans N → Option String) (F T : FireRel N),
      CORE_022 F ∧ CORE_030 F ∧ CORE_031 F ∧ CORE_032 F ∧ CORE_033 F ∧ CORE_034 F ∧
      CORE_035 F ∧ CORE_036 F ∧ IO_001 F ∧ IO_002 F ∧ IO_003 F ∧ IO_004 F ∧ IO_005 F ∧
      IO_010 F ∧ IO_011 Build F ∧ IO_012 IO_012_check Build F ∧ IO_013 Build F T ∧ IO_014 Build T) ∧
    (∃ K, IO_007 K) ∧ (∃ V : OutputValidator N, IO_015 V) ∧ (∃ E : BranchEnum N, IO_016 E)) ∧
    ∃ R : TRel N, ProjectsTo R RefFire ∧ FramesMarking R ∧ Covers R ∧ CoversReap R ∧
      CoversDelay R ∧ TIME_010 R :=
  ⟨spec_consistent_coreIO, RefTStep, refTStep_projectsTo, refTStep_framesMarking,
    refTStep_covers, refTStep_coversReap, refTStep_coversDelay, TIME_010_reference⟩

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
    ¬ (ProjectsTo timeEmptyRel RefFire ∧ FramesMarking timeEmptyRel ∧ Covers timeEmptyRel ∧
      CoversReap timeEmptyRel ∧ CoversDelay timeEmptyRel ∧ TIME_010 timeEmptyRel) := by
  rintro ⟨-, -, hc, -⟩
  obtain ⟨_, h, -⟩ := hc time010_X time010_s0 time010_src [0] time010_m1
    (by simp [time010_X]) (by decide) ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
  exact h

end Libpetri.Spec
