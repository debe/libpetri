import Libpetri.Spec.Text
import Libpetri.Spec.Ledger
/-!
# Generating `spec/*.md`

This module is tooling, not specification. It renders the chapters declared with `spec_chapter`
(`Libpetri.Spec.Text`) and computes their generated blocks (`table KIND`):

* the index's `files` (the Spec Files table: one row per chapter with a `scope`, its prefix and
  its count of active requirements, and the total), `tombstones` (the removed requirements),
  `crossref` (the cross-reference index: per prefix, every requirement's ID, title, priority and
  the IDs of its `**Depends on:**` line) and `priorities` (the priority distribution);
* the ledger's `unbuilt` and `defects` entries, `defectTable` (one row per defect: its ID, the
  spec IDs of its Requirements item, its runtimes and its status) and `divergences`
  (`Libpetri.Spec.Ledger`).

No count, title, priority or dependency is written twice: each is read from the requirement text
or the ledger entry that states it.

`#render_spec "dir"` checks the whole program, then writes every chapter into `dir`:

* every requirement text is listed by exactly one chapter;
* every ID of a `**Depends on:**` line is a requirement text;
* no two chapters define one glossary term, and no two modules declare one ledger entry;
* every `RD-NN` and `UB-NN` that a Lean source under `Libpetri/` names is a ledger entry (the
  ledger chapter itself, which names withdrawn numbers, excepted);
* every glossary reference in a Lean source under `Libpetri/` (`Glossary: *Place*
  (spec/glossary.md)`) names a glossary term.

The last two read the sources, so `#render_spec` runs from `lean/` (`spec-tools/Render.lean`).
-/
set_option linter.missingDocs true

open Lean Elab Command

namespace Libpetri.Spec.Generate

open Libpetri.Spec.Text Libpetri.Spec.Ledger

/-- The prefix of a spec ID: `CORE` for `CORE-031`. -/
def idPrefix (id : String) : String := (id.splitOn "-").headD ""

/-- The number of a spec or ledger ID: `31` for `CORE-031`. -/
def idNum (id : String) : Nat := ((id.splitOn "-").getD 1 "").toNat!

/-- Is the requirement text a tombstone? -/
def removed (e : TextEntry) : Bool := e.status == "Removed"

/-- The title of a chapter: its first chunk starts with `# NN — Title`. -/
def chapterTitle (c : Chapter) : Option String := do
  let .md s := (← c.items[0]?) | none
  let line := (s.splitOn "\n").headD ""
  let rest ← (if line.startsWith "# " then some (line.drop 2).toString else none)
  match rest.splitOn " — " with
  | _ :: t :: more => some (" — ".intercalate (t :: more))
  | _ => none

/-- A chapter of the Spec Files table: the chapter, its prefix, its title and its active
requirement texts. -/
structure Indexed where
  /-- The chapter. -/
  chapter : Chapter
  /-- The prefix its requirements share. -/
  pre : String
  /-- Its title, from its `# NN — Title` heading. -/
  title : String
  /-- Its requirement texts, tombstones included, in chapter order. -/
  texts : Array TextEntry

/-- The chapters with a `scope`, by file name: each with one prefix and a title. -/
def indexedChapters (env : Environment) (chapters : Array Chapter) : Except String (Array Indexed) :=
  chapters.filter (!·.scope.isEmpty) |>.mapM fun c => do
    let texts := c.texts env
    let pres := texts.foldl (fun (acc : Array String) e =>
      if acc.contains (idPrefix e.id) then acc else acc.push (idPrefix e.id)) #[]
    let #[pre] := pres
      | throw s!"{c.file} has a scope, so its requirements share one prefix; they have {pres}"
    let some title := chapterTitle c
      | throw s!"{c.file} has a scope, so its first chunk starts with its `# NN — Title` heading"
    return { chapter := c, pre, title, texts }

/-- `s` padded with spaces to `n` characters. -/
def pad (s : String) (n : Nat) : String := s ++ "".pushn ' ' (n - s.length)

/-- A tombstone's title without its strike-through and `(Removed)`. -/
def plainTitle (t : String) : String :=
  let t := if t.endsWith " (Removed)" then (t.dropEnd 10).toString else t
  t.replace "~~" ""

/-! ## The index -/

/-- The Spec Files table. -/
def filesTable (ix : Array Indexed) : String :=
  let rows := ix.map fun i =>
    s!"| [{i.chapter.file}]({i.chapter.file}) | {i.pre} | {i.chapter.scope} | \
      {(i.texts.filter (!removed ·)).size} |"
  let total := ix.foldl (fun n i => n + (i.texts.filter (!removed ·)).size) 0
  "| File | Prefix | Scope | Req Count |\n|------|--------|-------|-----------|\n" ++
    "\n".intercalate rows.toList ++ s!"\n| **Total** | | | **{total}** |\n"

/-- The tombstones, in chapter order. -/
def tombstones (ix : Array Indexed) : Array TextEntry :=
  ix.foldl (fun acc i => acc ++ i.texts.filter (removed ·)) #[]

/-- A list in prose: `a`, `a and b`, `a, b and c`. -/
def andList (xs : List String) : String :=
  match xs.reverse with
  | [] => ""
  | [x] => x
  | x :: rest => ", ".intercalate rest.reverse ++ " and " ++ x

/-- The note on the removed requirements. -/
def tombstoneNote (ix : Array Indexed) : String :=
  let ts := (tombstones ix).toList
  if ts.isEmpty then "> No requirement has been removed. Counts above are active requirements \
    only.\n" else
  "> " ++ andList (ts.map fun e => s!"**{e.id}** ({plainTitle e.title})") ++
    s!" {if ts.length == 1 then "was" else "were"} removed (see " ++
    ", ".intercalate (ts.map (s!"[{·.id}]")) ++ "); " ++
    (if ts.length == 1 then "it is retained as a struck-through tombstone" else
      "each is retained as a struck-through tombstone") ++
    " for traceability and **excluded** from the active count. Counts above are active \
    requirements only.\n"

/-- The cross-reference index: per prefix, alphabetically, a table of every requirement by number. -/
def crossref (ix : Array Indexed) : String :=
  let byPre := ix.qsort (·.pre < ·.pre)
  let part (i : Indexed) : String :=
    let rows := (i.texts.qsort (idNum ·.id < idNum ·.id)).map fun e =>
      if removed e then s!"| ~~{e.id}~~ | {e.title} | — | — |" else
        let deps := dependsOn e.plain
        s!"| {e.id} | {e.title} | {e.priority} | \
          {if deps.isEmpty then "—" else ", ".intercalate deps.toList} |"
    s!"### {i.pre} — {i.title}\n| ID | Title | Priority | Depends On |\n\
      |----|-------|----------|------------|\n" ++ "\n".intercalate rows.toList ++ "\n"
  "\n".intercalate (byPre.map part).toList

/-- The priority distribution of the active requirements. -/
def priorityTable (ix : Array Indexed) : String :=
  let active := ix.foldl (fun acc i => acc ++ i.texts.filter (!removed ·)) #[]
  let n (p : String) := (active.filter (·.priority == p)).size
  let ts := tombstones ix
  let row (p d : String) := s!"| {pad p 8} | {pad (toString (n p)) 5} | {d} |"
  "| Priority | Count | Description |\n|----------|-------|-------------|\n" ++
    row "MUST" "Core contract; all implementations must conform" ++ "\n" ++
    row "SHOULD" "Recommended; implementations should include unless technically infeasible" ++
    "\n" ++ row "MAY" "Optional; implementations may include" ++ "\n" ++
    s!"| **Total** | **{active.size}** | Matches the active-requirement total above\
      {if ts.isEmpty then "" else
        s!"; tombstones ({", ".intercalate (ts.toList.map (·.id))}) excluded"} |\n"

/-! ## The ledger -/

/-- An item's text with the lines that continue it indented by two spaces. -/
def indent (s : String) : String := s.replace "\n" "\n  "

/-- A ledger item, `- **Label:** text`. -/
def item (label text : String) : String := s!"- **{label}:** {indent text}\n"

/-- The text of an evidence item, its `⟪name⟫` markers shown as code spans. -/
def shown (s : String) : String :=
  match parseNames s with
  | .ok (t, _) => t
  | .error _ => s

/-- The markdown of a defect entry. -/
def renderDefect (d : Defect) : String :=
  s!"### {d.id}. {d.title}\n\n" ++ item "Requirements" d.requirements ++
    item "Runtimes" d.runtimes ++ item "Defect" d.defect ++
    item "Lean evidence" (shown d.evidence) ++
    (if d.fix.isEmpty then "" else item "Fix" d.fix) ++ item "Status" (d.status ++ ".")

/-- The markdown of an unbuilt entry. -/
def renderUnbuilt (u : Unbuilt) : String :=
  s!"### {u.id}. {u.title}\n\n" ++ item "Requirements" u.requirements ++
    item "Runtimes" u.runtimes ++ item "Missing" u.missing ++ item "Status" (u.status ++ ".")

/-- The defects, by number. -/
def defects (env : Environment) : Array Defect :=
  (defectExt.getState env).qsort (·.num < ·.num)

/-- The ledger's summary table: per defect its ID, the spec IDs its Requirements item names, its
runtimes and its status. -/
def defectTable (env : Environment) : String :=
  let rows := (defects env).map fun d =>
    s!"| {d.id} | {", ".intercalate (specIdsIn d.requirements).toList} | \
      {", ".intercalate ((parseRuntimes d.runtimes).getD #[]).toList} | {d.status} |"
  "| ID | Requirements | Runtimes | Status |\n|---|---|---|---|\n" ++
    "\n".intercalate rows.toList ++ "\n"

/-- The divergence table, in declaration order. -/
def divergenceTable (env : Environment) : String :=
  let rows := (divergenceExt.getState env).map fun d =>
    s!"| {d.aspect} | {d.spec} | {d.java} | {d.typescript} | {d.rust} |"
  "| Aspect | Spec | Java | TypeScript | Rust |\n|---|---|---|---|---|\n" ++
    "\n".intercalate rows.toList ++ "\n"

/-! ## Chapters -/

/-- The markdown of a generated block. -/
def block (env : Environment) (ix : Array Indexed) : String → String
  | "files" => filesTable ix
  | "tombstones" => tombstoneNote ix
  | "crossref" => crossref ix
  | "priorities" => priorityTable ix
  | "unbuilt" =>
    "\n".intercalate ((unbuiltExt.getState env).qsort (·.num < ·.num) |>.map renderUnbuilt).toList
  | "defectTable" => defectTable env
  | "defects" => "\n".intercalate ((defects env).map renderDefect).toList
  | "divergences" => divergenceTable env
  | _ => ""

/-- Does the chapter hold a generated block of one of `kinds`? -/
def hasBlock (c : Chapter) (kinds : List String) : Bool :=
  c.items.any fun | .table k => kinds.contains k | _ => false

/-- The first line of a generated file. -/
def banner (c : Chapter) : String :=
  let src := moduleSource c.module
  let tail := "by lean/spec-tools/Render.lean. Do not edit: edit the Lean source, then run \
    `lake env lean spec-tools/Render.lean` from lean/. -->"
  if c.items.any (fun | .req _ => true | _ => false) then
    s!"<!-- Generated from {src} and the requirement texts it lists, {tail}"
  else if hasBlock c ["unbuilt", "defectTable", "defects", "divergences"] then
    s!"<!-- Generated from {src} and the ledger entries of lean/Libpetri/Spec/Ledger/, {tail}"
  else if hasBlock c ["files", "tombstones", "crossref", "priorities"] then
    s!"<!-- Generated from {src}, the chapters and the requirement texts, {tail}"
  else
    s!"<!-- Generated from {src}, {tail}"

/-- The markdown of a chapter, banner first. -/
def renderChapter (env : Environment) (ix : Array Indexed) (c : Chapter) : String :=
  let item : Item → String
    | .md s => s ++ "\n"
    | .req k => match findText? env k with
      | some e => e.render
      | none => ""
    | .term t b => s!"### {t}\n\n{b}\n"
    | .table k => block env ix k
  banner c ++ "\n" ++ "\n".intercalate (c.items.toList.map item)

/-! ## Whole-program checks -/

/-- The `KEY-NN` mentions of `s` (`RD-12`, `UB-01`): the prefix, a `-` and digits, not inside a
word. -/
def mentions (pre : String) (s : String) : Array String := Id.run do
  let mut out : Array String := #[]
  let parts := (s.splitOn (pre ++ "-")).toArray
  for i in [1:parts.size] do
    let before := parts[i - 1]!
    let ok := before.isEmpty || !wordChar (before.back)
    let digits := (parts[i]!.takeWhile Char.isDigit).toString
    let after := (parts[i]!.drop digits.length).toString
    if ok && !digits.isEmpty && (after.isEmpty || !wordChar after.front) then
      let m := s!"{pre}-{digits}"
      unless out.contains m do out := out.push m
  return out

/-- The glossary references of `s`: the term of every `Glossary: *Place* (spec/glossary.md)`, the
term's lines joined. A term in asterisks that the file name does not follow is not a reference. -/
def glossaryRefs (s : String) : Array String :=
  ((s.splitOn "Glossary: *").drop 1).toArray.filterMap fun p =>
    match p.splitOn "*" with
    | t :: rest =>
      if ("*".intercalate rest).trimAsciiStart.toString.startsWith "(spec/glossary.md)" then
        some (joinLines t) else none
    | [] => none

/-- The `.lean` files under `dir`, sorted. -/
def leanFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let fs ← dir.walkDir
  return (fs.filter (·.extension == some "lean")).qsort (·.toString < ·.toString)

/-- `#render_spec "dir"` checks the whole program (the module docstring) and writes every chapter
into `dir` (`dir/<file>`). -/
syntax (name := renderSpecCmd) "#render_spec " str : command

@[command_elab renderSpecCmd, inherit_doc renderSpecCmd]
def elabRenderSpec : CommandElab := fun stx => do
  let env ← getEnv
  let chapters := (chapterExt.getState env).qsort (·.file < ·.file)
  let texts := textExt.getState env
  let mut bad : Array String := #[]
  for e in texts do
    let n := (chapters.filter fun c => c.items.any fun | .req k => k == e.key | _ => false).size
    if n != 1 then
      bad := bad.push s!"the text {e.key} ({moduleSource e.module}) is listed by {n} chapters, \
        not 1"
    for d in dependsOn e.plain do
      if (findText? env (Name.mkSimple (d.replace "-" "_"))).isNone then
        bad := bad.push s!"{e.id} ({moduleSource e.module}) depends on [{d}], which is not a \
          requirement text"
  let mut terms : Array String := #[]
  for c in chapters do
    for (t, _) in c.terms do
      if terms.contains t then bad := bad.push s!"the glossary term {t} is defined twice"
      terms := terms.push t
  let ds := defectExt.getState env
  let us := unbuiltExt.getState env
  for d in ds do
    if (ds.filter (·.id == d.id)).size > 1 then
      bad := bad.push s!"{d.id} is declared twice ({moduleSource d.module})"
  for u in us do
    if (us.filter (·.id == u.id)).size > 1 then
      bad := bad.push s!"{u.id} is declared twice ({moduleSource u.module})"
  -- the Lean sources: ledger mentions and glossary references
  let ledgerSrc := chapters.filterMap fun c =>
    if hasBlock c ["defects"] then some (moduleSource c.module) else none
  let dir : System.FilePath := "Libpetri"
  unless ← dir.isDir do
    throwError "#render_spec: there is no Libpetri/ here; run it from lean/"
  for f in ← leanFiles dir do
    let src ← IO.FS.readFile f
    let rel := "lean/" ++ f.toString
    unless ledgerSrc.contains rel do
      for m in mentions "RD" src do
        unless ds.any (·.id == m) do
          bad := bad.push s!"{rel} cites {m}, which is not a defect of the runtime ledger"
      for m in mentions "UB" src do
        unless us.any (·.id == m) do
          bad := bad.push s!"{rel} cites {m}, which is not an unbuilt entry of the runtime ledger"
    for t in glossaryRefs src do
      unless terms.contains t do
        bad := bad.push s!"{rel} refers to the glossary term *{t}*, which spec/glossary.md does \
          not define"
  let mut ix : Array Indexed := #[]
  match indexedChapters env chapters with
  | .ok r => ix := r
  | .error msg => bad := bad.push msg
  unless bad.isEmpty do
    throwError m!"#render_spec:\n{"\n".intercalate bad.toList}"
  let out : System.FilePath := (stx[1].isStrLit?).getD ""
  IO.FS.createDirAll out
  for c in chapters do
    IO.FS.writeFile (out / c.file) (renderChapter env ix c)
  logInfo m!"rendered {chapters.size} chapters ({texts.size} requirement texts, {terms.size} \
    glossary terms, {ds.size} defects, {us.size} unbuilt entries) into {out}"

end Libpetri.Spec.Generate
