import Libpetri
import Libpetri.Basic
import Libpetri.Compile
import Libpetri.Conservation
import Libpetri.Conservation.Pop
import Libpetri.Enablement
import Libpetri.Interning
import Libpetri.InvariantSum
import Libpetri.MatchCache
import Libpetri.MatchCache.Eligibility
import Libpetri.MatchCache.Model
import Libpetri.MatchCache.Plumbing
import Libpetri.Novel.CanonicalKey
import Libpetri.Novel.Certificate
import Libpetri.Novel.Commoner
import Libpetri.Novel.Dbm
import Libpetri.Novel.Enumeration
import Libpetri.Novel.EnvSemantics
import Libpetri.Novel.EnvSemantics.Arrivals
import Libpetri.Novel.EnvSemantics.Premise
import Libpetri.Novel.EnvSemantics.Quiescence
import Libpetri.Novel.EnvSemantics.Step
import Libpetri.Novel.EnvSemantics.Supplied
import Libpetri.Novel.Farkas
import Libpetri.Novel.FiringBound
import Libpetri.Novel.FiringBound.Bmc
import Libpetri.Novel.FiringBound.Phase
import Libpetri.Novel.FiringBound.Ranking
import Libpetri.Novel.FiringBound.Reaping
import Libpetri.Novel.FiringBound.Witness
import Libpetri.Novel.ForwardDeposit
import Libpetri.Novel.InFlight
import Libpetri.Novel.LinearBound
import Libpetri.Novel.Pairwise
import Libpetri.Novel.ReapAware
import Libpetri.Novel.ReapingVsUntimed
import Libpetri.Novel.ResetArc
import Libpetri.Novel.RouteA
import Libpetri.Novel.RouteA.Model
import Libpetri.Novel.RouteA.Plan
import Libpetri.Novel.RouteA.Reaping
import Libpetri.Novel.RouteA.Retrodict
import Libpetri.Novel.RouteA.Shipped
import Libpetri.Novel.RouteA.Simulate
import Libpetri.Novel.RouteA.SlotBound
import Libpetri.Novel.RouteB
import Libpetri.Novel.RouteB.Aligned
import Libpetri.Novel.RouteB.Classify
import Libpetri.Novel.RouteB.Decide
import Libpetri.Novel.RouteB.Exec
import Libpetri.Novel.RouteB.Graph
import Libpetri.Novel.RouteB.Name
import Libpetri.Novel.RouteB.Retrodict
import Libpetri.Novel.RouteB.Sim
import Libpetri.Novel.RouteB.Sound
import Libpetri.Novel.Seam
import Libpetri.Novel.Seam.Bad
import Libpetri.Novel.Seam.Excuses
import Libpetri.Novel.Seam.Index
import Libpetri.Novel.Seam.Net
import Libpetri.Novel.Seam.Retrodict
import Libpetri.Novel.Seam.Sound
import Libpetri.Novel.SiphonSearch
import Libpetri.Novel.Stubborn
import Libpetri.Novel.TerminalRewrite
import Libpetri.Novel.TimedScg
import Libpetri.Novel.TimedScg.Grid
import Libpetri.Novel.TimedScg.Late
import Libpetri.Novel.TimedScg.Progress
import Libpetri.Novel.TimedScg.Retrodict
import Libpetri.Novel.TimedScg.Run
import Libpetri.Novel.TimedScg.Succ
import Libpetri.Novel.TimedScg.Timing
import Libpetri.Novel.TimedScg.Zone
import Libpetri.Novel.TransferRows
import Libpetri.Priority
import Libpetri.Reference
import Libpetri.Reference.Decide
import Libpetri.Reference.Link
import Libpetri.Reference.Load
import Libpetri.Reference.Main
import Libpetri.Reference.Marking
import Libpetri.Reference.Queue
import Libpetri.Reference.Search
import Libpetri.Reference.Semantics
import Libpetri.Reference.Sha256
import Libpetri.Reference.Step
import Libpetri.Reference.Timed
import Libpetri.Refinement
import Libpetri.Refinement.Correspondence
import Libpetri.Refinement.Model
import Libpetri.Retrodict
import Libpetri.RetrodictExec
import Libpetri.Ring
import Libpetri.Ring.Core
import Libpetri.Ring.Grow
import Libpetri.Ring.Match
import Libpetri.RingArith
import Libpetri.Sched
import Libpetri.Semiflow
import Libpetri.Soundness
import Libpetri.Spec.All
import Libpetri.Spec.Clashes
import Libpetri.Spec.ClashesTime
import Libpetri.Spec.Consistency
import Libpetri.Spec.ConsistencyQueue
import Libpetri.Spec.ConsistencyTime
import Libpetri.Spec.Core
import Libpetri.Spec.Ears
import Libpetri.Spec.Glossary
import Libpetri.Spec.GlossaryQueue
import Libpetri.Spec.GlossaryTime
import Libpetri.Spec.Registry
import Libpetri.Spec.Req.CORE_022
import Libpetri.Spec.Req.CORE_030
import Libpetri.Spec.Req.CORE_032
import Libpetri.Spec.Req.CORE_033
import Libpetri.Spec.Req.CORE_034
import Libpetri.Spec.Req.CORE_035
import Libpetri.Spec.Req.CORE_036
import Libpetri.Spec.Req.EXEC_002
import Libpetri.Spec.Req.EXEC_010
import Libpetri.Spec.Req.EXEC_012
import Libpetri.Spec.Req.EXEC_013
import Libpetri.Spec.Req.EXEC_020
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
import Libpetri.StateEquation
import Libpetri.Strengthening
import Libpetri.Strengthening.Hypotheses
import Libpetri.TimedCycle
/-! Regenerates `lean/report/requirements.{md,json}` and `lean/report/proof-coverage.json`. Run
from `lean/`: `lake env lean spec-tools/Report.lean`. CI runs it and fails when a committed
report differs. The report only sees the `@[evidence]` tags of the modules imported here, so
every module of `lean/Libpetri.lean` and `lean/Libpetri/` is imported directly, the same list as
`spec-tools/Audit.lean` (the reference executable's `Main`, `Load` and `Sha256` are reached by no
other import). `scripts/lean-module-coverage-check.py` fails CI when a module is missing here.
The namespaces are opened so that statements print with the EARS notations and short names. -/

namespace SpecTools
open Lean Elab Command Libpetri.Spec

/-- The source file of a module, relative to `lean/`: `Libpetri.Novel.Dbm` becomes
`Libpetri/Novel/Dbm.lean`. -/
def moduleFile (m : Name) : String :=
  "/".intercalate (m.components.map toString) ++ ".lean"

/-- The last component of a theorem's user-facing name (a private theorem shows the name it
was declared with), as `scripts/spec-coverage-matrix.py` and `lake exe proofgraph` match it. -/
def shortName (thm : Name) : String :=
  match (privateToUserName? thm).getD thm with
  | .str _ s => s
  | n => n.toString

/-- The note at the top of `proof-coverage.json`. -/
def coverageComment : String :=
  "GENERATED from the @[evidence cites \"ID\" \"fragment\"] attributes on the theorems under \
  lean/Libpetri/ by lean/spec-tools/Report.lean (run from lean/: lake env lean \
  spec-tools/Report.lean); do not edit, CI regenerates it and fails on a difference. Maps Lean \
  theorems to the spec requirements they support. Consumed by scripts/spec-coverage-matrix.py, \
  which validates every id against the active registry in spec/00-index.md, by lake exe \
  proofgraph, and by scripts/proof-graph.py --coverage, which fails unless every listed theorem \
  is a graph node carrying the id. Each `fragment` scopes the claim honestly: a listed id means the theorem supports \
  THAT fragment of the requirement, nothing more. See lean/README.md for the development's \
  overall scope and out-of-scope list."

/-- `#write_proof_coverage "file"` writes the `@[evidence cites]` citations as
`{"$comment", "theorems": [{name, module, specIds: [{id, fragment}]}]}`: one entry per theorem,
its IDs in attribute order, the entries sorted by module file, then short name. Two theorems of
one module with the same short name are an error, since the consumers key on that pair. -/
elab "#write_proof_coverage " file:str : command => do
  let cs := (evExt.getState (← getEnv)).filter (·.role == "cites")
  -- group by theorem, keeping the order the attributes were applied in
  let mut thms : Array Name := #[]
  let mut ids : Std.HashMap Name (Array Evidence) := {}
  for c in cs do
    unless ids.contains c.thm do thms := thms.push c.thm
    ids := ids.insert c.thm ((ids.getD c.thm #[]).push c)
  let key (t : Name) : String × String :=
    (moduleFile (ids.getD t #[])[0]!.module, shortName t)
  let sorted := thms.qsort fun a b =>
    (key a).1 < (key b).1 || ((key a).1 == (key b).1 && (key a).2 < (key b).2)
  for i in [1:sorted.size] do
    if key sorted[i - 1]! == key sorted[i]! then
      throwError "#write_proof_coverage: {sorted[i - 1]!} and {sorted[i]!} share the short name \
        {(key sorted[i]!).2} in {(key sorted[i]!).1}; the coverage consumers cannot tell them \
        apart"
  -- laid out by hand (two-space indent, keys in schema order) so that diffs stay readable
  let str (x : String) : String := (Json.str x).compress
  let entries := sorted.map fun t =>
    let (module, name) := key t
    let specs := (ids.getD t #[]).map fun c =>
      s!"        \{\n          \"id\": {str c.id},\n          \"fragment\": {str c.fragment}\n        }"
    s!"    \{\n      \"name\": {str name},\n      \"module\": {str module},\n      \
      \"specIds\": [\n{",\n".intercalate specs.toList}\n      ]\n    }"
  let body := if entries.isEmpty then "[]" else
    "[\n" ++ ",\n".intercalate entries.toList ++ "\n  ]"
  let path : System.FilePath := file.getString
  if let some dir := path.parent then IO.FS.createDirAll dir
  IO.FS.writeFile path
    s!"\{\n  \"$comment\": {str coverageComment},\n  \"theorems\": {body}\n}\n"
  logInfo m!"wrote {entries.size} theorems and {cs.size} citations to {path}"

end SpecTools

open Libpetri Libpetri.Reference Libpetri.Spec
#write_requirements_report "report"
#write_proof_coverage "report/proof-coverage.json"
