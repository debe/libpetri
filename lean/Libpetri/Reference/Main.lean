import Libpetri.Reference
import Libpetri.Reference.Load
import Libpetri.Reference.Sha256
import Libpetri.Reference.Situation

/-!
# `lake exe reference`

```
lake exe reference <netsDir> <expectedDir> [--cap N]
lake exe reference --replay <net.json> <traces.json>
lake exe reference situations <situationsDir> <expectedDir>
```

The first form explores every `<netsDir>/*.json` once (default cap 100 000 markings) and writes
`<expectedDir>/<id>.json` with a verdict per property (schema:
`spec/verification-fixtures/conformance/README.md`). The second replays each
`{"property", "trace"}` entry of `traces.json` under the reference firing rule and prints, per
entry, whether some firing sequence carries those labels (`enabled`) and whether one of them ends
in a marking violating the property (`violates`); it exits 1 if any entry fails either.
The third replays the steps of every `<situationsDir>/*.json` whose `replay` is not `false`
(`Situation.lean`, schema: `spec/situations/README.md`) and writes
`<expectedDir>/<slug>.json`, the slug being the file's name without `.json`; it exits 1 when a
situation's net or steps do not load.
-/

open Lean Libpetri.Reference Libpetri.Reference.Load

namespace Libpetri.Reference.Cli

def jstr (s : String) : String := (Json.str s).compress

def jarr (xs : List String) : String := "[" ++ ", ".intercalate xs ++ "]"

def renderVerdict (pid : String) : Verdict → String
  | .proven => s!"\{ \"property\": {jstr pid}, \"verdict\": \"proven\" }"
  | .violated tr =>
    s!"\{ \"property\": {jstr pid}, \"verdict\": \"violated\", \"trace\": {jarr (tr.map jstr)} }"
  | .unknown r =>
    s!"\{ \"property\": {jstr pid}, \"verdict\": \"unknown\", \"reason\": {jstr r} }"

def render (id version : String) (classes : Nat) (complete : Bool)
    (results : List (String × Verdict)) : String :=
  let rs := results.map fun (pid, v) => "    " ++ renderVerdict pid v
  s!"\{ \"id\": {jstr id}, \"reference\": {jstr version}, \"classes\": {classes}, " ++
    s!"\"complete\": {complete},\n  \"results\": [\n" ++ ",\n".intercalate rs ++ "\n  ] }\n"

/-- The directory holding the reference's sources: `lean/Libpetri/Reference`, found from the
binary's path (`lean/.lake/build/bin/reference`). -/
def sourceDir : IO System.FilePath := do
  let app ← IO.appPath
  let leanDir := (app.parent >>= (·.parent) >>= (·.parent) >>= (·.parent)).getD "."
  return leanDir / "Libpetri" / "Reference"

/-- The SHA-256 of the concatenated sources of `lean/Libpetri/Reference/*.lean` in path order
(README "Clarifications", 3), or `dev` when they cannot be read. -/
def referenceVersion : IO String := do
  try
    let dir ← sourceDir
    let files := ((← dir.readDir).filter (·.path.extension == some "lean")).map (·.path)
    let files := files.qsort (fun a b => a.toString < b.toString)
    if files.isEmpty then return "dev"
    let mut bytes := ByteArray.empty
    for f in files do
      bytes := bytes ++ (← IO.FS.readBinFile f)
    return Sha256.hex bytes
  catch _ => return "dev"

/-- The standard SHA-256 test vectors. -/
def selfTest : IO UInt32 := do
  let cases := [("", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
    ("abc", "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
    ("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
      "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1")]
  let mut ok := true
  for (m, h) in cases do
    let got := Sha256.hex m.toUTF8
    if got != h then
      IO.eprintln s!"sha256 {m.quote}: {got} != {h}"
      ok := false
  IO.println (if ok then "self-test ok" else "self-test FAILED")
  return if ok then 0 else 1

def readJson (path : System.FilePath) : IO Json := do
  let txt ← IO.FS.readFile path
  match Json.parse txt with
  | .ok j => pure j
  | .error e => throw (IO.userError s!"{path}: {e}")

def runNet (cap : Nat) (version : String) (outDir path : System.FilePath) : IO Unit := do
  let ld := load (path.fileStem.getD "net") (← readJson path)
  match ld.refusal with
  | some r =>
    let results := ld.properties.map fun (pid, _) => (pid, Verdict.unknown r)
    IO.FS.writeFile (outDir / s!"{ld.id}.json") (render ld.id version 0 false results)
    IO.eprintln s!"{ld.id}: refused ({r})"
  | none =>
    let t0 ← IO.monoNanosNow
    let r ← IO.lazyPure fun _ => exploreNet ld.net cap ld.m0
    let classes := r.1.size
    let t1 ← IO.monoNanosNow
    let results := ld.properties.map fun (pid, p) =>
      match p with
      | .ok φ => (pid, verdict ld.net φ ld.m0 cap r)
      | .error e => (pid, Verdict.unknown e)
    IO.FS.writeFile (outDir / s!"{ld.id}.json") (render ld.id version classes r.2 results)
    let ms := (t1 - t0).toFloat / 1.0e6
    let rate := if t1 > t0 then classes.toFloat / ((t1 - t0).toFloat / 1.0e9) else 0
    IO.eprintln s!"{ld.id}: {classes} classes, complete={r.2}, {ms} ms, {rate.floor} classes/s"

def referenceMode (netsDir outDir : System.FilePath) (cap : Nat) : IO UInt32 := do
  let version ← referenceVersion
  IO.FS.createDirAll outDir
  let entries ← netsDir.readDir
  let files := (entries.filter (·.path.extension == some "json")).map (·.path)
  let files := files.qsort (fun a b => a.toString < b.toString)
  for f in files do
    runNet cap version outDir f
  return 0

/-- The index of the first label no firing sequence can take, if any. -/
def firstFailure (net : Net String) (m0 : Marking String) (tr : List String) : Option Nat :=
  let rec go : List String → List (Marking String) → Nat → Option Nat
    | [], _, _ => none
    | l :: ls, ms, i =>
      let ms' := stepLabel net l ms
      if ms'.isEmpty then some i else go ls ms' (i + 1)
  go tr [m0] 0

def replayMode (netPath tracesPath : System.FilePath) : IO UInt32 := do
  let ld := load (netPath.fileStem.getD "net") (← readJson netPath)
  let traces ← match (← readJson tracesPath).getArr? with
    | .ok a => pure a.toList
    | .error e => throw (IO.userError s!"{tracesPath}: {e}")
  let mut out : List String := []
  let mut allOk := true
  for t in traces do
    let pid := (t.getObjVal? "property" >>= Json.getStr?).toOption.getD ""
    let tr : List String := match t.getObjVal? "trace" >>= Json.getArr? with
      | .ok a => a.toList.filterMap fun x => x.getStr?.toOption
      | .error _ => []
    let err : Option String :=
      match ld.refusal with
      | some r => some r
      | none => match ld.properties.find? (·.1 == pid) with
        | none => some s!"no property '{pid}'"
        | some (_, .error e) => some e
        | some (_, .ok _) => none
    match err, ld.properties.find? (·.1 == pid) with
    | none, some (_, .ok φ) =>
      let enabled := !(replay ld.net tr [ld.m0]).isEmpty
      let violates := replayViolates ld.net φ ld.m0 tr
      let ok := enabled && violates
      allOk := allOk && ok
      let failed := match firstFailure ld.net ld.m0 tr with
        | some i => s!", \"failedStep\": {i}"
        | none => ""
      out := out ++ [s!"  \{ \"property\": {jstr pid}, \"enabled\": {enabled}, " ++
        s!"\"violates\": {violates}, \"ok\": {ok}{failed} }"]
    | _, _ =>
      allOk := false
      out := out ++ [s!"  \{ \"property\": {jstr pid}, \"ok\": false, " ++
        s!"\"error\": {jstr (err.getD "unknown")} }"]
  IO.println ("[\n" ++ ",\n".intercalate out ++ "\n]")
  return if allOk then 0 else 1

/-! ### Situations (`spec/situations/README.md`) -/

/-- The keys a situation adds to the corpus net schema; they are removed before the net is
loaded. -/
def situationKeys : List String := ["steps", "title", "text", "group", "cites", "replay"]

/-- One step: `{"fire": t, "branch": k?, "timeout": b?, "text": s?, "expect": e?}`. `branch`
defaults to 0; `"timeout": true` selects the timeout outcome ([IO-013]) instead of an action
branch. `text` and `expect` (what the author says the step does, checked by the spec site against
this replay) are accepted and ignored. -/
def parseStep (j : Json) : Load.Err SitStep := do
  Load.onlyKeys j ["fire", "branch", "timeout", "text", "expect"] "step"
  let fire ← Load.str (← Load.field j "fire") "step fire"
  let k ← match Load.optField j "branch" with
    | some b => Load.nat b "step branch"
    | none => pure 0
  let timeout ← match Load.optField j "timeout" with
    | some b => match b.getBool? with
      | .ok v => pure v
      | .error _ => Load.fail "invalid: step timeout must be a boolean"
    | none => pure false
  if let some x := Load.optField j "text" then
    discard <| Load.str x "step text"
  return { fire, choice := if timeout then .timedOut k else .action k }

/-- The text of a count marking: places in canonical (sorted) order, zero counts left out. -/
def renderMarking (m : Marking String) : String :=
  "{" ++ ", ".intercalate (m.map fun (p, n) => s!"{jstr p}: {n}") ++ "}"

/-- How an arc's cardinality is written in the corpus schema. -/
def cardJson : Card → String
  | .one => "\"kind\": \"one\""
  | .exactly n => s!"\"kind\": \"exactly\", \"n\": {n}"
  | .all => "\"kind\": \"all\""
  | .atLeast n => s!"\"kind\": \"atLeast\", \"n\": {n}"

/-- An arc's cardinality in prose, named as [IO-001]–[IO-004] name it. -/
def cardText : Card → String
  | .one => "One"
  | .exactly n => s!"Exactly({n})"
  | .all => "All"
  | .atLeast n => s!"AtLeast({n})"

/-- `n token` or `n tokens`. -/
def tokens (n : Nat) : String := if n == 1 then "1 token" else s!"{n} tokens"

/-- A reason as JSON. -/
def reasonJson : Blocked String → String
  | .unknownTransition => "{\"kind\": \"unknownTransition\"}"
  | .inputShort p c need held =>
    s!"\{\"kind\": \"inputShort\", \"place\": {jstr p}, \"arc\": \{{cardJson c}}, " ++
      s!"\"need\": {need}, \"have\": {held}}"
  | .inhibitorMarked p n =>
    s!"\{\"kind\": \"inhibitorMarked\", \"place\": {jstr p}, \"count\": {n}}"
  | .readEmpty p => s!"\{\"kind\": \"readEmpty\", \"place\": {jstr p}}"
  | .noSuchBranch (.action i) => s!"\{\"kind\": \"noSuchBranch\", \"branch\": {i}}"
  | .noSuchBranch (.timedOut j) =>
    s!"\{\"kind\": \"noSuchBranch\", \"timeout\": true, \"branch\": {j}}"

/-- A reason in one plain sentence. -/
def reasonText (t : String) : Blocked String → String
  | .unknownTransition => s!"the net has no transition '{t}'"
  | .inputShort p c need held =>
    s!"'{t}' is not enabled: input place '{p}' holds {tokens held}, its {cardText c} arc \
      needs {need}"
  | .inhibitorMarked p n => s!"'{t}' is not enabled: inhibitor place '{p}' holds {tokens n}"
  | .readEmpty p => s!"'{t}' is not enabled: read place '{p}' is empty"
  | .noSuchBranch (.action i) => s!"'{t}' is enabled but its output spec has no branch {i}"
  | .noSuchBranch (.timedOut 0) => s!"'{t}' is enabled but its output spec has no timeout"
  | .noSuchBranch (.timedOut j) =>
    s!"'{t}' is enabled but its output spec has no timeout outcome {j}"

/-- The step's own fields: the transition and the chosen outcome. -/
def stepHead (i : Nat) (s : SitStep) : String :=
  let ch := match s.choice with
    | .action k => s!"\"branch\": {k}"
    | .timedOut k => s!"\"timeout\": true, \"branch\": {k}"
  s!"\"index\": {i}, \"fire\": {jstr s.fire}, {ch}"

/-- The expected file of a situation (`spec/situations/README.md`, "Expected file"). -/
def renderSituation (slug version : String) (m0 : Marking String) (steps : List SitStep)
    (os : List (StepResult String)) : String :=
  let rows := (steps.zip os).zipIdx.map fun ((s, o), i) =>
    match o with
    | .fired m => s!"    \{ {stepHead i s}, \"fired\": true, \"marking\": {renderMarking m} }"
    | .blocked r =>
      s!"    \{ {stepHead i s}, \"blocked\": true, \"reason\": {reasonJson r}, " ++
        s!"\"requirement\": {jstr r.requirement}, \"message\": {jstr (reasonText s.fire r)} }"
  let body := if rows.isEmpty then "[]" else "[\n" ++ ",\n".intercalate rows ++ "\n  ]"
  s!"\{\n  \"slug\": {jstr slug},\n  \"reference\": {jstr version},\n" ++
    s!"  \"initial\": {renderMarking m0},\n  \"complete\": {allFired os && os.length == steps.length},\n" ++
    s!"  \"steps\": {body}\n}\n"

/-- Replay one situation file into `outDir`; an error when it does not load. -/
def runSituation (version : String) (outDir path : System.FilePath) : IO Unit := do
  let slug := path.fileStem.getD "situation"
  let j ← readJson path
  if let .ok (Json.bool false) := j.getObjVal? "replay" then
    IO.eprintln s!"{slug}: replay false, skipped"
    return
  let obj ← match j.getObj? with
    | .ok o => pure o
    | .error _ => throw (IO.userError s!"{path}: a situation must be an object")
  let netJson := Json.mkObj <| obj.toList.filter fun (k, _) => !situationKeys.contains k
  let ld := load slug netJson
  if let some r := ld.refusal then
    throw (IO.userError s!"{path}: the net does not load: {r}")
  let stepsJ ← match Load.optField j "steps" with
    | some a => match Load.arr a "steps" with
      | .ok xs => pure xs
      | .error e => throw (IO.userError s!"{path}: {e}")
    | none => throw (IO.userError s!"{path}: missing 'steps'")
  let steps ← match stepsJ.mapM parseStep with
    | .ok xs => pure xs
    | .error e => throw (IO.userError s!"{path}: {e}")
  let os := replaySituation ld.net ld.m0 steps
  IO.FS.writeFile (outDir / s!"{slug}.json") (renderSituation slug version ld.m0 steps os)
  let fired := (os.filter fun | .fired _ => true | _ => false).length
  IO.eprintln s!"{slug}: {fired} of {steps.length} steps fired"

def situationsMode (inDir outDir : System.FilePath) : IO UInt32 := do
  let version ← referenceVersion
  IO.FS.createDirAll outDir
  let entries ← inDir.readDir
  let files := (entries.filter (·.path.extension == some "json")).map (·.path)
  let files := files.qsort (fun a b => a.toString < b.toString)
  let mut ok := true
  for f in files do
    try runSituation version outDir f
    catch e =>
      IO.eprintln s!"error: {e}"
      ok := false
  return if ok then 0 else 1

def usage : String :=
  "usage: reference <netsDir> <expectedDir> [--cap N]\n" ++
  "       reference --replay <net.json> <traces.json>\n" ++
  "       reference situations <situationsDir> <expectedDir>"

end Libpetri.Reference.Cli

open Libpetri.Reference.Cli in
def main (args : List String) : IO UInt32 := do
  match args with
  | ["--replay", net, traces] => replayMode net traces
  | ["situations", dir, out] => situationsMode dir out
  | ["--self-test"] => selfTest
  | ["--version"] =>
    IO.println (← referenceVersion)
    return 0
  | [nets, out] => referenceMode nets out 100000
  | [nets, out, "--cap", n] | ["--cap", n, nets, out] =>
    match n.toNat? with
    | some c =>
      if c = 0 then
        IO.eprintln usage
        return 2
      else referenceMode nets out c
    | none =>
      IO.eprintln usage
      return 2
  | _ =>
    IO.eprintln usage
    return 2
