import Libpetri.Reference
import Libpetri.Reference.Load
import Libpetri.Reference.Sha256

/-!
# `lake exe reference`

```
lake exe reference <netsDir> <expectedDir> [--cap N]
lake exe reference --replay <net.json> <traces.json>
```

The first form explores every `<netsDir>/*.json` once (default cap 100 000 markings) and writes
`<expectedDir>/<id>.json` with a verdict per property (schema:
`spec/verification-fixtures/conformance/README.md`). The second replays each
`{"property", "trace"}` entry of `traces.json` under the reference firing rule and prints, per
entry, whether some firing sequence carries those labels (`enabled`) and whether one of them ends
in a marking violating the property (`violates`); it exits 1 if any entry fails either.
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

def usage : String :=
  "usage: reference <netsDir> <expectedDir> [--cap N]\n" ++
  "       reference --replay <net.json> <traces.json>"

end Libpetri.Reference.Cli

open Libpetri.Reference.Cli in
def main (args : List String) : IO UInt32 := do
  match args with
  | ["--replay", net, traces] => replayMode net traces
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
