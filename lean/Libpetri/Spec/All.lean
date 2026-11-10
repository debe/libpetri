import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.Glossary
import Libpetri.Spec.GlossaryTime
import Libpetri.Spec.GlossaryQueue
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
import Libpetri.Spec.Req.EXEC_002
import Libpetri.Spec.Req.EXEC_010
import Libpetri.Spec.Req.EXEC_012
import Libpetri.Spec.Req.EXEC_013
import Libpetri.Spec.Req.EXEC_020
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
import Libpetri.Spec.Req.VER_025
import Libpetri.Spec.Consistency
import Libpetri.Spec.ConsistencyTime
import Libpetri.Spec.ConsistencyQueue
import Libpetri.Spec.Clashes
import Libpetri.Spec.ClashesTime

/-!
# All requirement modules

Imports every module of `Libpetri.Spec`, so that `spec-tools/Report.lean` and
`spec-tools/Audit.lean` see every requirement block and every evidence theorem.
-/
