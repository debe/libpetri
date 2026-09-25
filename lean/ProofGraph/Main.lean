/-
# `lake exe proofgraph` — the Libpetri proof-dependency graph

Imports `Libpetri`, walks the compiled environment and writes
`graph/proof-graph.json` (schema `libpetri-proofgraph/1`, see
`graph/README.md`). Every edge comes from `Expr.getUsedConstants` on an
elaborated type or value; nothing is annotated by hand.

    lake exe proofgraph [--root <module>] [--prefix <namespace>]
      [--lock <names.txt|baseline.lock.json>] [--coverage <proof-coverage.json>]
      [--out <file> | OUT] [--check <expected.json>]

Run from `lean/`. `--root` and `--prefix` default to `Libpetri`; `OUT` to
`graph/proof-graph.json`, `--lock` to `graph/locked-theorems.txt`,
`--coverage` to `proof-coverage.json`.
-/
import Lean

open Lean

namespace ProofGraph

/-- The user-facing name: private declarations are shown under the name they
were declared with. -/
def userName (n : Name) : Name := (privateToUserName? n).getD n

/-- Last-component names the compiler or the structure/inductive machinery
generates. -/
def auxLast : List String :=
  ["rec", "recOn", "casesOn", "brecOn", "binductionOn", "below", "ibelow",
   "noConfusion", "noConfusionType", "ctorIdx", "toCtorIdx", "ctorElim",
   "ctorElimType", "injEq", "inj", "sizeOf_spec", "eq_def", "splitter"]

/-- `eq_<digits>`: an equation lemma. -/
def isEqnName (s : String) : Bool :=
  s.startsWith "eq_" && !(s.drop 3).isEmpty && (s.drop 3).all Char.isDigit

/-- `<prefix>_<digits>` for the compiler's numbered auxiliaries
(`match_1`, `proof_2`, …). -/
def isNumbered (pre s : String) : Bool :=
  s.startsWith pre && !(s.drop pre.length).isEmpty && (s.drop pre.length).all Char.isDigit

/-- Is `n` (a constant under `Libpetri`) an auxiliary to contract? The exact
filter is listed in `graph/README.md`. -/
def isAux (env : Environment) (n : Name) : Bool :=
  let u := userName n
  let last := match u with
    | .str _ s => s
    | _ => ""
  let comps := u.components.map (·.toString)
  u.isInternal || isAuxRecursor env n || isNoConfusion env n ||
    Meta.isMatcherCore env n || auxLast.contains last ||
    comps.any (fun s => isEqnName s || isNumbered "match_" s || isNumbered "proof_" s) ||
    (match env.find? n with
     | some (.recInfo _) => true
     | _ => false)

/-- Under the node namespace `root` (after stripping the private prefix). -/
def inRoot (root n : Name) : Bool := root.isPrefixOf (userName n) && userName n != root

def kindOf (env : Environment) (n : Name) : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => if Meta.isInstanceCore env n then "instance" else "def"
  | .inductInfo _ => if isStructure env n then "structure" else "inductive"
  | .ctorInfo _ => "ctor"
  | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom"
  | _ => "other"

/-- Constants used by a declaration's type and value. -/
def used (ci : ConstantInfo) : Array Name :=
  let t := ci.type.getUsedConstants
  match ci.value? (allowOpaque := true) with
  | some v => t ++ v.getUsedConstants
  | none => t

/-- No cycle reached (the low-link of a finished or non-auxiliary constant). -/
def noLow : Nat := 1000000000

/-- What a used constant contributes: node ends and external leaves.
Auxiliaries are expanded through their own uses. `stack` maps the auxiliaries
on the current path to their depth; re-entering one cuts the cycle and reports
its depth as the low-link. A result is memoised only when its low-link is not
above its own depth, i.e. the exploration did not cut into an auxiliary still
open below it on the path. A result cut short by such a cycle is partial and
is not stored; the auxiliary that closes the cycle (the one on the path whose
depth equals the low-link) collects the whole cycle and is stored. So every
memo entry is the complete contribution. -/
partial def resolve (env : Environment) (root b : Name) (stack : NameMap Nat) (depth : Nat) :
    StateM (NameMap (NameSet × NameSet)) (NameSet × NameSet × Nat) := do
  if !inRoot root b then return ({}, ({} : NameSet).insert b, noLow)
  if !isAux env b then return (({} : NameSet).insert (userName b), {}, noLow)
  if let some (ns, es) := (← get).find? b then return (ns, es, noLow)
  if let some d := stack.find? b then return ({}, {}, d)
  let some ci := env.find? b | return ({}, {}, noLow)
  let mut nodes : NameSet := {}
  let mut ext : NameSet := {}
  let mut low := noLow
  for c in used ci do
    let (ns, es, l) ← resolve env root c (stack.insert b depth) (depth + 1)
    nodes := ns.foldl (·.insert ·) nodes
    ext := es.foldl (·.insert ·) ext
    low := min low l
  if low ≥ depth then modify (·.insert b (nodes, ext))
  return (nodes, ext, low)

def moduleFile (m : Name) : String :=
  "/".intercalate (m.components.map (·.toString)) ++ ".lean"

def sortStrs (xs : Array String) : Array String :=
  xs.qsort (· < ·)

def strArr (xs : Array String) : Json :=
  Json.arr (sortStrs xs |>.map Json.str)

/-- Short theorem name + module file → spec IDs, from `proof-coverage.json`. -/
def readCoverage (path : System.FilePath) : IO (Std.HashMap (String × String) (Array String)) := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let ths ← IO.ofExcept (j.getObjValAs? (Array Json) "theorems")
  let mut m : Std.HashMap (String × String) (Array String) := {}
  for t in ths do
    let name ← IO.ofExcept (t.getObjValAs? String "name")
    let modl ← IO.ofExcept (t.getObjValAs? String "module")
    let ids ← IO.ofExcept (t.getObjValAs? (Array Json) "specIds")
    let ids ← ids.mapM fun i => IO.ofExcept (i.getObjValAs? String "id")
    m := m.insert (name, modl) ((m.getD (name, modl) #[]) ++ ids)
  return m

/-- A locked name as the node list shows it: `_private.<module>.0.<name>`
becomes `<name>`. -/
def lockUserName (s : String) : String :=
  if s.startsWith "_private." then
    match s.splitOn ".0." with
    | _ :: rest@(_ :: _) => ".0.".intercalate rest
    | _ => s
  else s

/-- The single lock source: the names the gate's statement lock covers.
A `.json` path is the gate's `baseline.lock.json` itself (the keys of every
top-level map whose entries carry a `typeHash`); any other path is a list of
names, one per line (`graph/locked-theorems.txt`, the default). -/
def readLock (path : System.FilePath) : IO (Std.HashSet String) := do
  let text ← IO.FS.readFile path
  let mut s : Std.HashSet String := {}
  if path.extension == some "json" then
    let j ← IO.ofExcept (Json.parse text)
    let some top := (j.getObj?).toOption | throw (IO.userError "lock: not an object")
    for ⟨_, v⟩ in top.toArray do
      if let some o := v.getObj?.toOption then
        for ⟨k, e⟩ in o.toArray do
          if (e.getObjVal? "typeHash").toOption.isSome then
            s := s.insert (lockUserName k)
  else
    for line in text.splitOn "\n" do
      let l := line.trimAscii.toString
      if !l.isEmpty then s := s.insert (lockUserName l)
  return s

structure Args where
  /-- The module imported (`--root`). -/
  root : String := "Libpetri"
  /-- The namespace whose declarations become nodes (`--prefix`). -/
  nsPrefix : String := "Libpetri"
  lock : String := "graph/locked-theorems.txt"
  coverage : String := "proof-coverage.json"
  out : String := "graph/proof-graph.json"
  /-- Test mode (`--check`): compare the output with this file instead of
  writing it. -/
  check : Option String := none

/-- `--check`: the first line where `actual` and `expected` differ, if any. -/
def firstDiff (expected actual : String) : Option (Nat × String × String) :=
  let e := expected.splitOn "\n"
  let a := actual.splitOn "\n"
  let n := max e.length a.length
  (List.range n).findSome? fun i =>
    let x := e.getD i "<missing>"
    let y := a.getD i "<missing>"
    if x == y then none else some (i + 1, x, y)

def parseArgs : List String → Args → Except String Args
  | [], a => .ok a
  | "--root" :: p :: rest, a => parseArgs rest { a with root := p }
  | "--prefix" :: p :: rest, a => parseArgs rest { a with nsPrefix := p }
  | "--lock" :: p :: rest, a => parseArgs rest { a with lock := p }
  | "--coverage" :: p :: rest, a => parseArgs rest { a with coverage := p }
  | "--out" :: p :: rest, a => parseArgs rest { a with out := p }
  | "--check" :: p :: rest, a => parseArgs rest { a with check := some p }
  | p :: rest, a =>
    if p.startsWith "--" then .error s!"unknown option {p}" else parseArgs rest { a with out := p }

end ProofGraph

open ProofGraph in
unsafe def main (argv : List String) : IO UInt32 := do
  let args ← IO.ofExcept (parseArgs argv {})
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let root := args.nsPrefix.toName
  let env ← importModules #[{ module := args.root.toName }] {} (loadExts := true)
  let coverage ← readCoverage args.coverage
  let locked ← readLock args.lock
  -- the node set, keyed by the user-facing name
  let names : Array Name := env.constants.fold (init := #[]) fun acc n _ =>
    if inRoot root n && !isAux env n then acc.push n else acc
  let ctx : Core.Context := { fileName := "<proofgraph>", fileMap := default }
  let (out, _) ← (do
    let mut memo : NameMap (NameSet × NameSet) := {}
    let mut rows : Array (String × Json) := #[]
    let mut edges : Array (String × String) := #[]
    for n in names do
      let some ci := env.find? n | continue
      let u := userName n
      let mut deps : NameSet := {}
      let mut ext : NameSet := {}
      for c in used ci do
        let ((ns, es, _), memo') := (resolve env root c {} 0).run memo
        memo := memo'
        deps := ns.foldl (·.insert ·) deps
        ext := es.foldl (·.insert ·) ext
      for d in deps do
        if d != u then edges := edges.push (u.toString, d.toString)
      let axs ← collectAxioms n
      let modl := match env.getModuleIdxFor? n with
        | some i => env.header.moduleNames[i.toNat]!
        | none => .anonymous
      let file := moduleFile modl
      let line := match ← findDeclarationRanges? n with
        | some r => r.range.pos.line
        | none => 0
      let short := match u with
        | .str _ s => s
        | _ => u.toString
      let specs := (coverage.getD (short, file) #[]).toList.eraseDups.toArray
      let node := Json.mkObj
        [("name", Json.str u.toString), ("kind", Json.str (kindOf env n ci)),
         ("module", Json.str modl.toString), ("file", Json.str file),
         ("line", toJson line), ("specs", strArr specs),
         ("locked", Json.bool (locked.contains u.toString)),
         ("axioms", strArr (axs.map (·.toString)).toList.eraseDups.toArray),
         ("external", strArr (ext.toArray.map (·.toString)))]
      rows := rows.push (u.toString, node)
    return (rows, edges) : CoreM _).toIO ctx { env }
  let (rows, edges) := out
  let rows := rows.qsort (fun a b => a.1 < b.1)
  let sorted := edges.qsort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2))
  let edges := (sorted.foldl (init := #[]) fun acc e =>
    if acc.back? == some e then acc else acc.push e).toList
  let nodeLines := rows.toList.map fun (_, j) => "    " ++ j.compress
  let edgeLines := edges.map fun (a, b) => "    " ++ (Json.arr #[Json.str a, Json.str b]).compress
  let text := "{\n  \"schema\": \"libpetri-proofgraph/1\",\n  \"nodes\": [\n" ++
    ",\n".intercalate nodeLines ++ "\n  ],\n  \"edges\": [\n" ++
    ",\n".intercalate edgeLines ++ "\n  ]\n}\n"
  if let some expPath := args.check then
    let expected ← IO.FS.readFile expPath
    match firstDiff expected text with
    | none =>
      IO.println s!"proofgraph --check: PASS ({rows.size} nodes, {edges.length} edges match {expPath})"
      return 0
    | some (i, x, y) =>
      IO.println s!"proofgraph --check: FAIL at line {i} of {expPath}\n  expected: {x}\n  actual:   {y}"
      return 1
  IO.FS.writeFile args.out text
  IO.println s!"proofgraph: {rows.size} nodes, {edges.length} edges -> {args.out}"
  return 0
