import Libpetri
import Libpetri.Reference
import Libpetri.Spec.All
/-! Regenerates `lean/report/requirements.{md,json}`. Run from `lean/`:
`lake env lean spec-tools/Report.lean`. CI runs it and fails when the committed report differs.
`Libpetri` and `Libpetri.Reference` are imported so that `@[evidence]` tags outside
`Libpetri.Spec` reach the report. The namespaces are opened so that statements print with the
EARS notations and short names. -/
open Libpetri Libpetri.Reference Libpetri.Spec
#write_requirements_report "report"
