import Libpetri.Spec.Core
import Libpetri.Spec.Req.CORE_022
import Libpetri.Spec.Req.CORE_030
import Libpetri.Spec.Req.CORE_032
import Libpetri.Spec.Req.CORE_033
import Libpetri.Spec.Req.CORE_034
import Libpetri.Spec.Req.CORE_035
import Libpetri.Spec.Req.CORE_036
import Libpetri.Spec.Req.IO_001
import Libpetri.Spec.Req.IO_002
import Libpetri.Spec.Req.IO_003
import Libpetri.Spec.Req.IO_004
import Libpetri.Spec.Req.IO_005
import Libpetri.Spec.Req.IO_007
import Libpetri.Spec.Req.IO_010
import Libpetri.Spec.Req.IO_011
import Libpetri.Spec.Req.IO_012
import Libpetri.Spec.Req.IO_013
import Libpetri.Spec.Req.IO_014
import Libpetri.Spec.Req.IO_015
import Libpetri.Spec.Req.IO_016

set_option linter.missingDocs true

/-!
# Consistency of the CORE + IO firing requirements

`spec_consistent_coreIO` shows that the CORE and IO requirement blocks can all hold together:
one builder (the reference builder `refBuild`, which runs the build-time checks of CORE-030 and
the Output Composition preamble), one firing relation `F` (the reference semantics, `RefFire`)
and one relation `T` of firings that end with the timeout outcome (`refTimeoutOutcomeFire`)
satisfy every behaviour block at once, and the reference ambiguity check, contract, validator
and branch enumeration satisfy IO-012's build line and the three function blocks (IO-007,
IO-015, IO-016).

IO-012 is among them: its firing lines speak of transitions whose output spec passes its build
check, and CORE-022's last line speaks of transitions that build (glossary: Builds), so an
output spec such as `Xor(Place(0), Place(0))`, whose two assignments claim one set, is rejected
when the transition is built and is never asked to fire.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-- IO-013's reference timed-out firings and IO-014's are the same relation. -/
theorem refTimeoutOutcomeFire_eq_refTimedOutFire {N : Type} [DecidableEq N] :
    refTimeoutOutcomeFire (N := N) = refTimedOutFire := rfl

/-- ✓ The CORE and IO requirement blocks hold together: the reference builder, the reference
firing relation and its timed-out firings satisfy every behaviour block, and the reference
ambiguity check, consumption contract, output validator and branch enumeration satisfy IO-012,
IO-007, IO-015 and IO-016. -/
@[evidence consistent CORE_022 CORE_030 CORE_031 CORE_032 CORE_033 CORE_034 CORE_035 CORE_036
  IO_001 IO_002 IO_003 IO_004 IO_005 IO_007 IO_010 IO_011 IO_012 IO_013 IO_014 IO_015 IO_016]
theorem spec_consistent_coreIO {N : Type} [DecidableEq N] [ToString N] :
    (∃ (Build : Trans N → Option String) (F T : FireRel N),
      CORE_022 F ∧ CORE_030 F ∧ CORE_031 F ∧ CORE_032 F ∧ CORE_033 F ∧ CORE_034 F ∧
      CORE_035 F ∧ CORE_036 F ∧ IO_001 F ∧ IO_002 F ∧ IO_003 F ∧ IO_004 F ∧ IO_005 F ∧
      IO_010 F ∧ IO_011 Build F ∧ IO_012 IO_012_check Build F ∧ IO_013 Build F T ∧ IO_014 Build T) ∧
    (∃ K, IO_007 K) ∧ (∃ V : OutputValidator N, IO_015 V) ∧ (∃ E : BranchEnum N, IO_016 E) :=
  ⟨⟨refBuild, RefFire, refTimeoutOutcomeFire,
      CORE_022_reference, CORE_030_reference, CORE_031_reference, CORE_032_reference,
      CORE_033_reference, CORE_034_reference, CORE_035_reference, CORE_036_reference,
      IO_001_reference, IO_002_reference, IO_003_reference, IO_004_reference, IO_005_reference,
      IO_010_reference, IO_011_reference, IO_012_reference, IO_013_reference,
      refTimeoutOutcomeFire_eq_refTimedOutFire (N := N) ▸ IO_014_reference⟩,
    ⟨_, IO_007_reference⟩, ⟨_, IO_015_reference (N := N)⟩, ⟨_, IO_016_reference (N := N)⟩⟩

end Libpetri.Spec
