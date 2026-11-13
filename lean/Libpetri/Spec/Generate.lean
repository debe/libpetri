import Libpetri.Spec.Text
import Libpetri.Spec.Ledger
import Libpetri.Spec.Registry
import Libpetri.Spec.Markdown
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

Two more commands read the rendered chapters back (`Libpetri.Spec.Markdown`):
`#write_spec_json "file"` writes the spec as data for the consumers outside Lean
(`spec-tools/Report.lean` writes `lean/report/spec.json`), and `#audit_spec` checks the
requirement blocks against the text (`spec-tools/Audit.lean`). The index's Depends On column
reads each text's `**Depends on:**` lines with the same reader.
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

/-- The fields of a requirement text (`Markdown.fields`), read from its own rendered markdown
without the heading: the lines its section of the chapter holds. -/
def textFields (e : TextEntry) : Except String Markdown.Fields :=
  let ls := Markdown.scan (Markdown.lines e.render)
  Markdown.fields (ls.extract 1 ls.size)

/-- The IDs of a requirement text's `**Depends on:**` lines, in order, each once (`textFields`);
none when the fields do not read, which `#render_spec` reports. -/
def dependsOn (e : TextEntry) : Array String :=
  match textFields e with
  | .ok f => f.dependsOn
  | .error _ => #[]

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
        let deps := dependsOn e
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
    match textFields e with
    | .error msg => bad := bad.push s!"{e.id} ({moduleSource e.module}): {msg}"
    | .ok f =>
      for d in f.dependsOn do
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

/-! ## Reading the chapters back

`spec/*.md` is rendered from Lean, and some facts are only visible in the rendered chapter: which
`##` section a requirement sits in, the line of its heading, the paragraphs its body falls into,
which of its sentences are normative. `Libpetri.Spec.Markdown` reads the rendered chapters, and
everything below uses what it reads: `#write_spec_json` writes it for the consumers outside Lean,
`#audit_spec` checks the requirement blocks against it. -/

open Libpetri.Spec.Markdown

/-- A requirement section of a rendered chapter: from its `#### ID:` heading to the next heading
of level 1 to 4. -/
structure Section where
  /-- The ID of its heading. -/
  id : String
  /-- The chapter file. -/
  file : String
  /-- The line of the heading, from 1. -/
  line : Nat
  /-- The scanned lines after the heading. -/
  body : Array Line
  /-- The same lines as the units see them (`Markdown.stripped`). -/
  plain : Array String
  /-- The title of the `##` heading it sits under. -/
  group : Option String
  deriving Inhabited

/-- A rendered chapter, read back. -/
structure Scanned where
  /-- The chapter. -/
  chapter : Chapter
  /-- The text of its first `#` heading, without its number. -/
  title : Option String
  /-- Its requirement sections, in order. -/
  sections : Array Section
  /-- Its scanned lines. -/
  lines : Array Line

/-- `t` without a leading two-digit number, a dash and the whitespace around it: `01 — Core Model`
is `Core Model`. -/
def dropNumber (t : String) : String := Id.run do
  let a := t.toList.toArray
  unless a.size ≥ 2 && a[0]!.isDigit && a[1]!.isDigit do return t
  let mut i := 2
  while i < a.size && isWs a[i]! do i := i + 1
  unless i < a.size && (a[i]! == '—' || a[i]! == '–' || a[i]! == '-') do return t
  i := i + 1
  while i < a.size && isWs a[i]! do i := i + 1
  return sub a i a.size

/-- Read a rendered chapter back: its title, its `##` headings and its requirement sections. -/
def scanChapter (env : Environment) (ix : Array Indexed) (c : Chapter) : Scanned := Id.run do
  let sc := scan (Markdown.lines (renderChapter env ix c))
  let st := sc.map stripped
  let mut title : Option String := none
  let mut h2 : Array (Nat × String) := #[]
  for i in [0:st.size] do
    match headingLevel? st[i]! with
    | some 1 => if title.isNone then title := some (dropNumber (headingBody st[i]!))
    | some 2 => h2 := h2.push (i, headingBody st[i]!)
    | _ => pure ()
  let mut secs : Array Section := #[]
  for i in [0:st.size] do
    unless isSectionBreak st[i]! do continue
    let some id := canonId? st[i]! | continue
    let mut j := i + 1
    while j < st.size && !isSectionBreak st[j]! do j := j + 1
    secs := secs.push {
      id, file := c.file, line := i + 1, body := sc.extract (i + 1) j,
      plain := st.extract (i + 1) j, group := (h2.filter (·.1 < i)).back?.map (·.2) }
  return { chapter := c, title, sections := secs, lines := sc }

/-- Is the file a numbered chapter, `NN-name.md` (`a`–`z`, digits and `-`), other than the
index? -/
def isNumbered (f : String) : Bool :=
  match f.toList with
  | d1 :: d2 :: '-' :: rest =>
    d1.isDigit && d2.isDigit && !f.startsWith "00-" && f.endsWith ".md" &&
      (rest.take (rest.length - 3)).all fun c => ('a' ≤ c && c ≤ 'z') || c.isDigit || c == '-'
  | _ => false

/-- The chapters, by file name, the index's generated blocks and every chapter read back. -/
def readChapters (env : Environment) : Except String (Array Indexed × Array Scanned) := do
  let chapters := (chapterExt.getState env).qsort (·.file < ·.file)
  let ix ← indexedChapters env chapters
  return (ix, chapters.map (scanChapter env ix))

/-- A requirement's title as the site shows it: without strike-through and `(Removed)`. -/
def bareTitle (t : String) : String :=
  let t := trimEnd t
  let t := if t.endsWith "(Removed)" then trimEnd (t.dropEnd 9).toString else t
  trim (t.replace "~~" "")

/-- One requirement of a numbered chapter, read back. -/
structure ReadReq where
  /-- Its text. -/
  text : TextEntry
  /-- Its section. -/
  sec : Section
  /-- The fields of its section. -/
  fields : Fields
  /-- `active`, `proposed` or `removed`. -/
  status : String
  /-- The spec IDs its section cites outside its Depends on lines, sorted, its own ID left out.
  An `[ID]` whose prefix is no chapter's (`[RV-08]`, a bibliography entry) is not one. -/
  mentions : Array String

/-- Read the requirements of the numbered chapters back, in chapter order. Fails on a section
without a requirement text, on a section whose fields do not parse and on a status line that
disagrees with the text's status. -/
def readReqs (env : Environment) (ix : Array Indexed) (scans : Array Scanned) :
    Except String (Array ReadReq) := do
  let prefixes := ix.map (·.pre)
  let mut out : Array ReadReq := #[]
  for s in scans do
    unless isNumbered s.chapter.file do continue
    for sec in s.sections do
      let some e := findText? env (Name.mkSimple (sec.id.replace "-" "_"))
        | throw s!"spec/{sec.file}: the heading of {sec.id} at line {sec.line} is no \
            requirement text's"
      let f ← match fields sec.body with
        | .ok f => pure f
        | .error msg => throw s!"{sec.id} ({moduleSource e.module}): {msg}"
      let status := f.status.getD "active"
      if (status == "removed") != removed e then
        throw s!"{sec.id} ({moduleSource e.module}): its status line says {status}, its text's \
          status is {repr e.status}"
      let cited := (f.cited.flatMap bracketRefs).foldl
        (fun acc i => if acc.contains i then acc else acc.push i) #[]
      let mentions := (cited.filter fun i => prefixes.contains (idPrefix i) && i != sec.id &&
        !f.dependsOn.contains i).qsort (· < ·)
      out := out.push { text := e, sec, fields := f, status, mentions }
  return out

/-- A glossary term, read back. -/
structure ReadTerm where
  /-- The term, as its `### Term` heading shows it. -/
  term : String
  /-- The `#` or `##` heading it sits under. -/
  group : String
  /-- Its text, its chunks joined (`joinMarkdown`) and separated by a blank line. -/
  text : String

/-- The glossary terms of a chapter read back: every `###` heading opens a term, which runs to
the next heading; a `#` or `##` heading is the group of the terms under it. Fails on a term
before any group and a term without text. -/
def readTerms (s : Scanned) : Except String (Array ReadTerm) := do
  let mut out : Array ReadTerm := #[]
  let mut group : Option String := none
  let mut open_ : Option (String × String × Nat) := none
  let ls := s.lines
  let close (o : Option (String × String × Nat)) (stop : Nat) (out : Array ReadTerm) :
      Except String (Array ReadTerm) := do
    let some (term, g, start) := o | return out
    let text := "\n\n".intercalate ((chunks (ls.extract start stop) false).map joinMarkdown).toList
    if text.isEmpty then throw s!"spec/{s.chapter.file}: the glossary term {term} has no text"
    return out.push { term, group := g, text }
  for i in [0:ls.size] do
    let l := ls[i]!
    if l.fence then continue
    let some level := headingLevel? l.text | continue
    out ← close open_ i out
    open_ := none
    let title := headingText l.text
    if level ≤ 2 then group := some title
    else if level == 3 then
      let some g := group
        | throw s!"spec/{s.chapter.file}: the term {title} comes before any group heading"
      open_ := some (title, g, i + 1)
  close open_ ls.size out

/-- The lines of a ledger item as the generated file shows them after its `- **Label:**`: the
first line without its leading whitespace, then the lines that continue it (indented by two
spaces), up to the first that is neither fenced nor indented text. -/
def itemLines (text : String) : Array Line := Id.run do
  let ls := Markdown.lines text
  let some first := ls[0]? | return #[]
  let sc := scan (#["- **Item:** " ++ first] ++ (ls.extract 1 ls.size).map ("  " ++ ·))
  let mut out : Array Line := #[{ text := trimStart first, fence := false }]
  for l in sc.extract 1 sc.size do
    if l.fence || (indentOf l.text ≥ 1 && !(trim l.text).isEmpty) then out := out.push l
    else break
  return out

/-- The markdown of a ledger item, joined (`joinMarkdown`). -/
def itemText (text : String) : String := joinMarkdown (itemLines text)

/-- A ledger status as JSON: `{"state": "open"}`, or `{"state": "fixed", "version": v}` with
`v` null while the fix is unreleased. -/
def statusJson (s : String) : Json :=
  if s == "open" then Json.mkObj [("state", "open")]
  else if s == "fixed, unreleased" then Json.mkObj [("state", "fixed"), ("version", Json.null)]
  else Json.mkObj [("state", "fixed"), ("version", Json.str (s.drop 9).toString)]

/-- An optional string as JSON: the string, or null. -/
def optJson : Option String → Json
  | some s => Json.str s
  | none => Json.null

/-- An empty string as null. -/
def nonEmpty (s : String) : Option String := if s.isEmpty then none else some s

/-- Does a ledger item start with the word *none* (any case)? A Lean evidence item that does
names no evidence: the names it gives are context. -/
def startsWithNone (s : String) : Bool :=
  let t := (trim s).toLower
  t.startsWith "none" && !((t.toList.drop 4).head?.any isWord)

/-- The note at the top of `spec.json`. -/
def specJsonComment : String :=
  "GENERATED from the spec text in lean/Libpetri/Spec/Text/ and the runtime ledger in \
  lean/Libpetri/Spec/Ledger/ by lean/spec-tools/Report.lean (#write_spec_json, \
  Libpetri/Spec/Generate.lean); do not edit, CI regenerates it and fails on a difference. It is \
  the spec as data, read by the spec site and scripts/spec-coverage-matrix.py, so that no tool \
  parses spec/*.md. chapters: the numbered chapters with their ## sections. requirements: every \
  requirement of a numbered chapter, in chapter order, with its markdown body, its labelled \
  normative spans (what `covers ID.label` names, lines joined) and its body read back: \
  paragraphs (shall, prose or code), acceptance criteria, notes, depends-on, the IDs it \
  mentions otherwise, and test derivation. glossary: the terms. defects, unbuilt, divergences: \
  the runtime ledger; a defect's evidence is the Lean names of its evidence item, none when the \
  item starts with none."

/-- `spec.json` (the module docstring of `spec-tools/Report.lean` and `specJsonComment`). -/
def specJson (env : Environment) : Except String Json := do
  let (ix, scans) ← readChapters env
  let reqs ← readReqs env ix scans
  let chapters := scans.filter (isNumbered ·.chapter.file) |>.map fun s =>
    let ids := s.sections.map (·.id)
    let pres := ids.foldl (fun (acc : Array String) i =>
      if acc.contains (idPrefix i) then acc else acc.push (idPrefix i)) #[]
    -- consecutive sections under one `##` heading form one group
    let groups := s.sections.foldl (fun (acc : Array (Option String × Array String)) sec =>
      match acc.back? with
      | some (g, xs) => if g == sec.group then acc.pop.push (g, xs.push sec.id)
          else acc.push (sec.group, #[sec.id])
      | none => acc.push (sec.group, #[sec.id])) #[]
    Json.mkObj [
      ("file", s.chapter.file), ("number", (s.chapter.file.take 2).toString),
      ("title", optJson s.title), ("scope", s.chapter.scope), ("prefixes", toJson pres),
      ("sections", Json.arr <| groups.map fun (g, xs) => Json.mkObj [
        ("title", Json.str (g.getD (s.title.getD ""))), ("ids", toJson xs)])]
  let reqJson := reqs.map fun r =>
    let e := r.text
    let f := r.fields
    Json.mkObj [
      ("id", e.id), ("title", bareTitle e.title), ("priority", optJson (nonEmpty e.priority)),
      ("kind", optJson (nonEmpty e.kind)), ("status", r.status), ("file", r.sec.file),
      ("line", toJson r.sec.line), ("section", optJson r.sec.group), ("source", moduleSource e.module),
      ("body", e.plain),
      ("spans", Json.arr <| e.spans.map fun sp =>
        Json.mkObj [("label", sp.label), ("text", joinLines sp.text)]),
      ("paragraphs", Json.arr <| f.body.map fun p => Json.mkObj [("kind", p.kind), ("text", p.text)]),
      ("acceptance", toJson f.acceptance),
      ("notes", Json.arr <| f.notes.map fun (l, t) => Json.mkObj [("label", l), ("text", t)]),
      ("dependsOn", toJson f.dependsOn), ("mentions", toJson r.mentions),
      ("testDerivation", optJson f.testDerivation)]
  let mut terms : Array Json := #[]
  for s in scans do
    unless s.chapter.items.any (fun | .term .. => true | _ => false) do continue
    for t in ← readTerms s do
      terms := terms.push <| Json.mkObj [("term", t.term), ("group", t.group), ("text", t.text),
        ("refs", toJson (bracketRefs t.text))]
  let ds := (defects env).map fun d =>
    let (shown, names) := (parseNames d.evidence).toOption.getD (d.evidence, #[])
    let names := if startsWithNone shown then #[] else
      names.foldl (fun acc n => if acc.contains n then acc else acc.push n) #[]
    Json.mkObj [
      ("id", d.id), ("title", d.title), ("requirements", toJson (specIdsIn d.requirements)),
      ("runtimes", toJson ((parseRuntimes d.runtimes).getD #[])), ("text", itemText d.defect),
      ("evidence", toJson names), ("evidenceText", itemText shown),
      ("fix", optJson (if d.fix.isEmpty then none else some (itemText d.fix))),
      ("status", statusJson d.status)]
  let us := (unbuiltExt.getState env).qsort (·.num < ·.num) |>.map fun u =>
    Json.mkObj [
      ("id", u.id), ("title", u.title), ("requirements", toJson (specIdsIn u.requirements)),
      ("runtimes", toJson ((parseRuntimes u.runtimes).getD #[])), ("missing", itemText u.missing),
      ("status", u.status)]
  let dvs := (divergenceExt.getState env).map fun d =>
    Json.mkObj [("aspect", d.aspect), ("spec", d.spec), ("java", d.java),
      ("typescript", d.typescript), ("rust", d.rust)]
  return Json.mkObj [
    ("$comment", specJsonComment), ("chapters", Json.arr chapters),
    ("requirements", Json.arr reqJson), ("glossary", Json.arr terms), ("defects", Json.arr ds),
    ("unbuilt", Json.arr us), ("divergences", Json.arr dvs)]

/-- `#write_spec_json "file"` writes `spec.json` (`specJson`). -/
syntax (name := writeSpecJsonCmd) "#write_spec_json " str : command

@[command_elab writeSpecJsonCmd, inherit_doc writeSpecJsonCmd]
def elabWriteSpecJson : CommandElab := fun stx => do
  let path : System.FilePath := (stx[1].isStrLit?).getD ""
  match specJson (← getEnv) with
  | .error msg => throwError m!"#write_spec_json: {msg}"
  | .ok j =>
    if let some dir := path.parent then IO.FS.createDirAll dir
    IO.FS.writeFile path (j.pretty ++ "\n")
    logInfo m!"wrote {path}"

/-! ## The spec audit -/

/-- The IDs whose requirement blocks may take `source proposed`: wording that the spec text does
not hold yet. Empty: every block names spans of its requirement text. -/
def proposedIds : List String := []

/-- The kinds a requirement stated in Lean has: behaviour, pure function, timing. A requirement
of one of these kinds needs a requirement block; Q, A and N need none. -/
def statedKinds : List String := ["B", "F", "T"]

/-- The words of a `sourceRef`, split at whitespace, `/`, `,`, `;`, `#`, `(` and `)`. -/
def refWords (s : String) : List String := Id.run do
  let mut out : Array String := #[]
  let mut cur : Array Char := #[]
  for c in s.toList do
    if isWs c || "/,;#()".toList.contains c then
      unless cur.isEmpty do out := out.push (String.ofList cur.toList)
      cur := #[]
    else
      cur := cur.push c
  unless cur.isEmpty do out := out.push (String.ofList cur.toList)
  return out.toList

/-- `s`, cut to 120 characters. -/
def short (s : String) : String :=
  if s.length ≤ 120 then s else (s.take 117).toString ++ "..."

/-- `#audit_spec` checks the requirement blocks and the citations against the spec text, as the
generated chapters show it, and fails with one line per finding, each starting `SPEC <rule>`:

* `duplicate-heading`: two `#### ID:` headings for one ID in the generated chapters;
* `no-blocks`: there is no requirement block at all;
* `id-inactive`: a block's ID is a removed requirement or no requirement text;
* `no-heading`: a verbatim block's ID has no `#### ID:` heading in the generated chapters;
* `source-file`: a verbatim block's `sourceRef` does not name the chapter its text is in;
* `span-not-sentence`: a span a verbatim block covers is not a whole sentence, run of
  consecutive sentences or list bullet of the generated section (say, it sits in an HTML
  comment, a code block or a strike-through, or ends inside a sentence);
* `proposed-not-allowed`: a `source proposed` block whose ID is not in `proposedIds`;
* `evidence-missing`: a block without evidence, a kind-B block without `holds` or
  `nonvacuous` evidence, or a block with neither `forbids` nor `mutant` evidence;
* `uncovered`: for an ID with a verbatim block, a sentence of its section with the word
  *shall* that no block covers and no `assumes` line of the ID contains, or a numbered
  acceptance criterion `ACn` that no block covers whole and no `assumes` line names as `ACn`;
* `citation-inactive`: an `@[evidence cites]` names a removed requirement or no requirement;
* `kind-missing`, `kind-mismatch`: an active requirement's section has no `**Kind:**` line,
  more than one, or one that is not a kind; or its kind is no block's kind while it has blocks;
  or its kind is B, F or T and it has no block;
* `unknown-id`: a numbered chapter's requirement cites (Depends on or `[ID]` elsewhere) an ID
  that is no requirement text.

The sections, sentences and units are read by `Libpetri.Spec.Markdown` from the rendered
chapters. -/
syntax (name := auditSpecCmd) "#audit_spec" : command

@[command_elab auditSpecCmd, inherit_doc auditSpecCmd]
def elabAuditSpec : CommandElab := fun _ => do
  let env ← getEnv
  let texts := textExt.getState env
  let blocks := reqExt.getState env
  let evs := evExt.getState env
  let (ix, scans) ← match readChapters env with
    | .ok r => pure r
    | .error msg => throwError m!"#audit_spec: {msg}"
  let mut bad : Array String := #[]
  -- the sections, first heading first
  let mut secs : Array Section := #[]
  for s in scans do
    for sec in s.sections do
      match secs.find? (·.id == sec.id) with
      | some prev => bad := bad.push s!"SPEC duplicate-heading {sec.id}: '#### {sec.id}:' at \
          spec/{prev.file}:{prev.line} and spec/{sec.file}:{sec.line}"
      | none => secs := secs.push sec
  let isActive (id : String) : Bool := texts.any fun e => e.id == id && !removed e
  let isRemoved (id : String) : Bool := texts.any fun e => e.id == id && removed e
  let unitsOf (id : String) : Option (Section × Array TextUnit) :=
    (secs.find? (·.id == id)).map fun sec => (sec, units sec.plain)
  if blocks.isEmpty then bad := bad.push "SPEC no-blocks: there is no requirement block"
  -- per block; coverage per ID with a verbatim block
  let mut covered : Array (String × Array (Nat × Nat)) := #[]
  let mut assumed : Array (String × Array String) := #[]
  let mut spans : Nat := 0
  for b in blocks do
    let name := b.decl.toString
    if isRemoved b.id then
      bad := bad.push s!"SPEC id-inactive {name}: {b.id} is a removed requirement"
    else if !isActive b.id then
      bad := bad.push s!"SPEC id-inactive {name}: {b.id} is no requirement text"
    if b.source == "verbatim" then
      let mut cov := ((covered.find? (·.1 == b.id)).map (·.2)).getD #[]
      covered := covered.filter (·.1 != b.id)
      let ass := ((assumed.find? (·.1 == b.id)).map (·.2)).getD #[]
      assumed := (assumed.filter (·.1 != b.id)).push (b.id, ass ++ b.assumes.map norm)
      if b.quotes.isEmpty then
        bad := bad.push s!"SPEC span-not-sentence {name}: a verbatim block that covers nothing"
      match unitsOf b.id with
      | none =>
        bad := bad.push s!"SPEC no-heading {name}: no '#### {b.id}:' heading in the generated \
          spec/*.md"
      | some (sec, us) =>
        unless (refWords b.sourceRef).contains sec.file do
          bad := bad.push s!"SPEC source-file {name}: sourceRef {repr b.sourceRef} does not \
            name {sec.file}, where {b.id} is"
        for q in b.quotes do
          let hits := if (norm q).isEmpty then #[] else matchQuote (norm q) us
          if hits.isEmpty then
            bad := bad.push s!"SPEC span-not-sentence {name}: the covered text is not a whole \
              sentence, run of sentences or bullet of the '#### {b.id}:' section of \
              spec/{sec.file} (is it in a comment, a code block or a strike-through, or cut \
              inside a sentence?): {repr (short q)}"
          else
            spans := spans + 1
            cov := cov ++ hits
      covered := covered.push (b.id, cov)
    else if b.source == "proposed" then
      unless proposedIds.contains b.id do
        bad := bad.push s!"SPEC proposed-not-allowed {name}: source proposed, but {b.id} is not \
          in Libpetri.Spec.Generate.proposedIds"
    let roles := (evs.filter fun v => v.req == b.decl && v.role != "cites").map (·.role)
    if roles.isEmpty then
      bad := bad.push s!"SPEC evidence-missing {name}: no evidence theorem (tag one with \
        @[evidence ROLE {name}])"
    if b.kind == "B" then
      for role in ["holds", "nonvacuous"] do
        unless roles.contains role do
          bad := bad.push s!"SPEC evidence-missing {name}: a kind-B block without a '{role}' \
            evidence theorem"
    unless roles.contains "forbids" || roles.contains "mutant" do
      bad := bad.push s!"SPEC evidence-missing {name}: no 'forbids' or 'mutant' evidence \
        theorem (every requirement needs a negative example)"
  -- the normative text of every ID with a verbatim block
  for (id, cov) in covered.qsort (·.1 < ·.1) do
    let some (sec, us) := unitsOf id | continue
    let ass := ((assumed.find? (·.1 == id)).map (·.2)).getD #[]
    let acs := ass.flatMap acMentions
    for ui in [0:us.size] do
      let u := us[ui]!
      if let some n := u.ac then
        if acs.contains n || (List.range u.sents.size).all (fun si => cov.contains (ui, si)) then continue
        bad := bad.push s!"SPEC uncovered {id}: acceptance criterion AC{n} in spec/{sec.file} \
          is neither covered whole by a block nor named as 'AC{n}' in an assumes line: \
          {repr (short (" ".intercalate u.sents.toList))}"
        continue
      for si in [0:u.sents.size] do
        let st := u.sents[si]!
        if !hasShall st || cov.contains (ui, si) || ass.any (fun a => (a.splitOn st).length > 1) then
          continue
        bad := bad.push s!"SPEC uncovered {id}: a 'shall' sentence in spec/{sec.file} is \
          covered by no block and stated in no assumes line: {repr (short st)}"
  -- citations
  let cites := evs.filter (·.role == "cites")
  for c in cites do
    if isRemoved c.id then
      bad := bad.push s!"SPEC citation-inactive {c.thm} ({c.module}): cites {c.id}, a removed \
        requirement"
    else if !isActive c.id then
      bad := bad.push s!"SPEC citation-inactive {c.thm} ({c.module}): cites {c.id}, which is \
        no requirement text"
  -- the Kind line of every active requirement
  let activeIds := (texts.filter (!removed ·)).map (·.id) |>.qsort (· < ·)
  for id in activeIds do
    let some sec := secs.find? (·.id == id) | continue
    let where_ := s!"spec/{sec.file}:{sec.line}"
    let ks := kindLines sec.plain
    let owned := (blocks.filter (·.id == id)).map (·.kind)
    match ks with
    | #[] => bad := bad.push s!"SPEC kind-missing {id}: the section at {where_} has no \
        '**Kind:**' line"
    | #[k] =>
      if !kinds.contains k then
        bad := bad.push s!"SPEC kind-mismatch {id}: '**Kind:** {k}' at {where_} is not one of \
          {kinds}"
      else if !owned.isEmpty && !owned.contains k then
        bad := bad.push s!"SPEC kind-mismatch {id}: the text says Kind {k}, but no block of {id} \
          has kind {k} (blocks: {", ".intercalate owned.toList})"
      else if owned.isEmpty && statedKinds.contains k then
        bad := bad.push s!"SPEC kind-mismatch {id}: the text says Kind {k}, a stated kind, but \
          {id} has no requirement block (Q, A and N need none)"
    | _ => bad := bad.push s!"SPEC kind-mismatch {id}: the section at {where_} has {ks.size} \
        '**Kind:**' lines ({", ".intercalate ks.toList}); expected one"
  -- the IDs the numbered chapters cite
  match readReqs env ix scans with
  | .error msg => bad := bad.push s!"SPEC unreadable: {msg}"
  | .ok reqs =>
    for r in reqs do
      for id in r.fields.dependsOn ++ r.mentions do
        unless (findText? env (Name.mkSimple (id.replace "-" "_"))).isSome do
          bad := bad.push s!"SPEC unknown-id {r.text.id} ({moduleSource r.text.module}): cites \
            [{id}], which is no requirement text"
  unless bad.isEmpty do
    throwError m!"spec audit failed, {bad.size} finding(s):\n{"\n".intercalate bad.toList}"
  logInfo m!"spec ok: {blocks.size} requirement blocks, {spans} covered spans under their IDs, \
    {cites.size} citations of active requirements"

end Libpetri.Spec.Generate
