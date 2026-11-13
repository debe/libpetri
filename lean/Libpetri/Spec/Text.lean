import Lean
/-!
# The spec text

This module is tooling, not specification. It holds the text of the spec (`spec/*.md` is generated
from it) and gives the spec modules two commands:

* `requirement_text`, the text of one requirement: its ID, title, priority, kind, status and its
  body, the requirement's raw markdown. Normative spans of the body are marked `⟦s1|…⟧`, so that
  a `requirement` block can name them (`covers PERF_030.s1`) instead of copying them;
* `spec_chapter`, one generated markdown file: an ordered list of raw markdown chunks
  (`md r#"…"#`), requirement texts (`req PERF_001`), glossary terms (`term "Place" r#"…"#`) and
  generated blocks (`table files`), with an optional `scope` that the index lists it with.

`#render_spec "dir"` (`Libpetri.Spec.Generate`) writes every chapter into `dir`.

A chapter renders as its items joined by a blank line: a chunk is its text and a line break; a
requirement is its `#### ID: Title` heading, a blank line, its `**Priority:**`, `**Kind:**` and
`**Status:**` lines (those it has), a blank line, then its body with the markers removed and a
line break; a term is its `### Term` heading, a blank line, its text and a line break; a
generated block is what `Libpetri.Spec.Generate` computes for it. The first line of every
generated file is a banner naming the Lean source.

It imports only Lean core, so that a text module builds fast and light.
-/
set_option linter.missingDocs true

open Lean Elab Command

namespace Libpetri.Spec

/-! ## Shared with the `requirement` command (`Libpetri.Spec.Registry`) -/

/-- Is the string blank, i.e. without a single ASCII letter or digit? Trimming is not enough: it
keeps invisible characters such as a zero-width space or a word joiner, so a field holding only
those would pass for text. Every field checked with this is English prose or an identifier. -/
def blank (s : String) : Bool := !s.any Char.isAlphanum

/-- Does `s` match `^[A-Z]+-[0-9]{3}$`, the shape of a spec ID such as `VER-002`? -/
def isSpecId (s : String) : Bool :=
  match s.splitOn "-" with
  | [pre, num] =>
    !pre.isEmpty && pre.all (fun c => 'A' ≤ c && c ≤ 'Z') &&
      num.length == 3 && num.all Char.isDigit
  | _ => false

/-- The kind tags: B behaviour, F pure function, T timing, Q quality (test-only),
A assumption, N configuration. -/
def kinds : List String := ["B", "F", "T", "Q", "A", "N"]

namespace Text

/-- One labelled normative span of a requirement body, `⟦label|text⟧`. -/
structure Span where
  /-- The label, e.g. `s1`: a letter, then letters, digits or `_`. -/
  label : String
  /-- The raw markdown between `⟦label|` and `⟧`. -/
  text : String
  deriving Inhabited, Repr

/-- The text of one requirement, as written in a text module. -/
structure TextEntry where
  /-- The name the text is declared with, e.g. `PERF_030` for `PERF-030`. -/
  key : Name
  /-- Spec ID, e.g. `PERF-030`. -/
  id : String
  /-- The title, as the heading shows it. -/
  title : String
  /-- `MUST`, `SHOULD` or `MAY`; empty for a requirement without a priority line. -/
  priority : String
  /-- Kind tag (B, F, T, Q, A, N); empty for a requirement without a kind line. -/
  kind : String
  /-- Status, e.g. `Removed` for a tombstone; empty for a requirement without a status line. -/
  status : String
  /-- The body with its span markers. -/
  body : String
  /-- The body with the markers removed: the markdown the chapter shows. -/
  plain : String
  /-- The labelled spans of the body, in order. -/
  spans : Array Span
  /-- The module the text is declared in. -/
  module : Name
  deriving Inhabited

/-- One item of a chapter. -/
inductive Item where
  /-- A raw markdown chunk. -/
  | md (text : String)
  /-- The text of a requirement, by its key. -/
  | req (key : Name)
  /-- A glossary term: its name, as the `### Term` heading shows it, and its text. -/
  | term (title body : String)
  /-- A block computed from the other declarations (`tableKinds`), e.g. `files`. -/
  | table (kind : String)
  deriving Inhabited

/-- One generated markdown file. -/
structure Chapter where
  /-- The file name under `spec/`, e.g. `10-performance.md`. -/
  file : String
  /-- What the index's Spec Files table says the chapter covers; empty for a chapter that the
  table does not list (the index, the glossary, the ledger). -/
  scope : String
  /-- The items, in order. -/
  items : Array Item
  /-- The module the chapter is declared in. -/
  module : Name
  deriving Inhabited

/-- Persistent store of all requirement texts, imported modules included. -/
initialize textExt : SimplePersistentEnvExtension TextEntry (Array TextEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun as => as.foldl (· ++ ·) #[]
  }

/-- Persistent store of all chapters, imported modules included. -/
initialize chapterExt : SimplePersistentEnvExtension Chapter (Array Chapter) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun as => as.foldl (· ++ ·) #[]
  }

/-- The priorities a requirement may have. -/
def priorities : List String := ["MUST", "SHOULD", "MAY"]

/-- Is `s` a valid span label: a letter, then letters, digits or `_`? -/
def isLabel (s : String) : Bool :=
  match s.toList with
  | c :: cs => c.isAlpha && cs.all fun c => c.isAlphanum || c == '_'
  | [] => false

/-- Split a body into its plain text and its spans. Fails on a `⟧` that closes nothing, a `⟦`
inside a span (spans do not nest), a span left open, a label that is not `isLabel`, a label used
twice, and a span without a letter or digit. -/
def parseMarkers (body : String) : Except String (String × Array Span) := Id.run do
  let mut plain := ""
  let mut spans : Array Span := #[]
  -- 0: outside a span, 1: reading a label, 2: inside a span
  let mut state : Nat := 0
  let mut label := ""
  let mut cur := ""
  for c in body.toList do
    if state == 0 then
      if c == '⟦' then
        state := 1
        label := ""
      else if c == '⟧' then
        return .error "a ⟧ closes no span"
      else
        plain := plain.push c
    else if state == 1 then
      if c == '|' then
        unless isLabel label do
          return .error s!"the span label {repr label} is not a letter followed by letters, \
            digits or _"
        if spans.any (·.label == label) then
          return .error s!"the span label {label} is used twice"
        state := 2
        cur := ""
      else if c == '⟦' || c == '⟧' || c == '\n' then
        return .error s!"a span label must be followed by |, after ⟦{label}"
      else
        label := label.push c
    else
      if c == '⟧' then
        unless cur.any Char.isAlphanum do
          return .error s!"the span {label} holds no letter or digit"
        spans := spans.push { label, text := cur }
        state := 0
      else if c == '⟦' then
        return .error s!"a span opens inside the span {label}; spans do not nest"
      else
        cur := cur.push c
        plain := plain.push c
  if state != 0 then
    return .error s!"the span {label} is not closed with ⟧"
  return .ok (plain, spans)

/-- Join the lines of a span: every whitespace run (space, tab, line break) that holds a line
break becomes one space, a run without one stays as it is (so the spacing inside a code span
survives), and whitespace at both ends is dropped. A `covers` reference resolves to its span read
like this, so a quote keeps its statement hash wherever the markdown wraps it. -/
def joinLines (s : String) : String := Id.run do
  let mut out := ""
  let mut run := ""
  for c in s.toList do
    if c.isWhitespace then
      run := run.push c
    else
      unless out.isEmpty do
        out := out ++ (if run.contains '\n' then " " else run)
      run := ""
      out := out.push c
  return out

/-- The kinds of generated block a chapter may hold (`table KIND`): the index's `files` (Spec Files
table), `tombstones` (the removed requirements), `crossref` (the cross-reference index) and
`priorities` (the priority distribution); the ledger's `unbuilt` and `defects` entries,
`defectTable` (its summary table) and `divergences` (its divergence table). -/
def tableKinds : List String :=
  ["files", "tombstones", "crossref", "priorities", "unbuilt", "defectTable", "defects",
    "divergences"]

/-- The requirement text declared as `key`, if any module of the environment declares it. -/
def findText? (env : Environment) (key : Name) : Option TextEntry :=
  (textExt.getState env).find? (·.key == key)

/-- Resolve a reference `KEY.label` (e.g. `PERF_030.s1`) to its text entry and the span's text,
its lines joined (`joinLines`). -/
def resolveSpan (env : Environment) (ref : Name) : Except String (TextEntry × String) := do
  let key := ref.getPrefix
  let label := ref.components.getLast?.map toString |>.getD ""
  if key.isAnonymous then
    throw s!"{ref} is not a span reference; write the text's name and the span label, e.g. \
      PERF_030.s1"
  let some e := findText? env key
    | throw s!"there is no requirement text {key}; is the text module imported (e.g. \
        import Libpetri.Spec.Text.{key})?"
  let some sp := e.spans.find? (·.label == label)
    | let labels := ", ".intercalate (e.spans.toList.map (·.label))
      throw s!"the text of {e.id} has no span labelled {label} (its spans: \
        {if labels.isEmpty then "none" else labels})"
  return (e, joinLines sp.text)

/-- The `requirement_text` command: the text of one requirement.

```
requirement_text PERF_030
  id "PERF-030"
  title "Bitmap Memory Efficiency"
  priority MUST                -- MUST, SHOULD or MAY
  kind F                       -- B, F, T, Q, A or N
  status Removed               -- optional; a tombstone has a status and no priority or kind
  body r#"The bitmap executor uses compact representations: …

⟦s1|For a net with P places and T transitions, the bitmap executor *shall* …⟧"#
```

The name is the ID with `-` replaced by `_`. The body is the requirement's markdown after its
heading and its priority, kind and status lines, up to the end of its section, verbatim; a raw
string (`r#"…"#`, more `#` when the text holds `"#`) takes it without escapes. A normative span
is marked `⟦label|…⟧`: the chapter shows the body without the markers, and a `requirement`
block names the span with `covers PERF_030.s1`. The command checks the markers (balanced, not
nested, labels unique) and the fields, and records the text. Keywords after the first are
non-reserved. -/
syntax (name := requirementTextCmd) "requirement_text " ident &"id" str &"title" str
  (&"priority" ident)? (&"kind" ident)? (&"status" ident)? &"body" str : command

@[command_elab requirementTextCmd, inherit_doc requirementTextCmd]
def elabRequirementText : CommandElab := fun stx => do
  let n := stx[1]
  let key := n.getId
  let str (s : Syntax) : String := (s.isStrLit?).getD ""
  let opt (s : Syntax) : String := if s.getNumArgs == 2 then s[1].getId.toString else ""
  let id := str stx[3]
  let title := str stx[5]
  let priority := opt stx[6]
  let kind := opt stx[7]
  let status := opt stx[8]
  let body := str stx[10]
  let fail {α : Type} (msg : String) : CommandElabM α :=
    throwErrorAt n m!"requirement_text {key}: {msg}"
  unless isSpecId id do fail s!"id {repr id} is not a spec ID (expected e.g. PERF-030)"
  unless key.toString == id.replace "-" "_" do
    fail s!"the name must be the ID with - replaced by _, i.e. {id.replace "-" "_"}"
  if blank title then fail "empty title"
  unless priority.isEmpty || priorities.contains priority do
    fail s!"priority must be one of {priorities}, not {priority}"
  unless kind.isEmpty || kinds.contains kind do
    fail s!"kind must be one of {kinds}, not {kind}"
  if status.isEmpty && (priority.isEmpty || kind.isEmpty) then
    fail "give a priority and a kind, or a status (a tombstone)"
  if blank body then fail "empty body"
  if (findText? (← getEnv) key).isSome then fail "the text is declared twice"
  let (plain, spans) ← match parseMarkers body with
    | .ok r => pure r
    | .error msg => fail msg
  modifyEnv (textExt.addEntry · {
    key, id, title, priority, kind, status, body, plain, spans,
    module := (← getEnv).mainModule })

/-- A raw markdown chunk of a chapter. -/
syntax chapterMd := &"md" str

/-- A requirement text of a chapter, by its name. -/
syntax chapterReq := &"req" ident

/-- A glossary term of a chapter: its name, then its text. -/
syntax chapterTerm := &"term" str str

/-- A generated block of a chapter, by its kind (`tableKinds`). -/
syntax chapterTable := &"table" ident

/-- The `spec_chapter` command: one generated markdown file under `spec/`.

```
spec_chapter "10-performance.md"
  scope "Scaling, benchmarks, memory efficiency, flat-array executor performance"
  md r#"# 10 — Performance

…

## Scaling Requirements"#
  req PERF_001
  md r#"---"#
  req PERF_002
```

The items render in order, separated by a blank line: a chunk as its text, a requirement as its
heading, its priority, kind and status lines and its body (see the module docstring), a term
(`term "Place" r#"A named container …"#`) as its `### Place` heading and its text, and a
generated block (`table crossref`) as `Libpetri.Spec.Generate` computes it. A chunk holds no
leading or trailing line break of its own unless the markdown has more than one blank line there.
Every requirement text it names must be imported. A chapter with a `scope` is a row of the
index's Spec Files table: its requirements share one prefix, and its first chunk starts with its
`# NN — Title` heading, which names the prefix's section of the cross-reference index. -/
syntax (name := specChapterCmd) "spec_chapter " str (&"scope" str)?
  (chapterMd <|> chapterReq <|> chapterTerm <|> chapterTable)* : command

@[command_elab specChapterCmd, inherit_doc specChapterCmd]
def elabSpecChapter : CommandElab := fun stx => do
  let file := (stx[1].isStrLit?).getD ""
  let scope := if stx[2].getNumArgs == 2 then (stx[2][1].isStrLit?).getD "" else ""
  let fail {α : Type} (msg : String) : CommandElabM α :=
    throwErrorAt stx[1] m!"spec_chapter {repr file}: {msg}"
  unless file.endsWith ".md" && !file.contains '/' && !blank file do
    fail "the file must be a markdown file name under spec/, e.g. 10-performance.md"
  if stx[2].getNumArgs == 2 && blank scope then fail "empty scope"
  let env ← getEnv
  if (chapterExt.getState env).any (·.file == file) then fail "the chapter is declared twice"
  let mut items : Array Item := #[]
  let mut seen : Array Name := #[]
  let mut terms : Array String := #[]
  for it in stx[3].getArgs do
    if it.getKind == ``chapterMd then
      items := items.push (.md ((it[1].isStrLit?).getD ""))
    else if it.getKind == ``chapterTerm then
      let title := (it[1].isStrLit?).getD ""
      let body := (it[2].isStrLit?).getD ""
      if blank title || title.contains '\n' || title.contains '*' then
        throwErrorAt it[1] m!"spec_chapter {repr file}: a term's name is one line of text"
      if blank body then
        throwErrorAt it[2] m!"spec_chapter {repr file}: the term {title} has no text"
      if terms.contains title then
        throwErrorAt it[1] m!"spec_chapter {repr file}: the term {title} is listed twice"
      terms := terms.push title
      items := items.push (.term title body)
    else if it.getKind == ``chapterTable then
      let kind := it[1].getId.toString
      unless tableKinds.contains kind do
        throwErrorAt it[1] m!"spec_chapter {repr file}: no generated block {kind}; the kinds \
          are {tableKinds}"
      if items.any (fun | .table k => k == kind | _ => false) then
        throwErrorAt it[1] m!"spec_chapter {repr file}: the block {kind} is listed twice"
      items := items.push (.table kind)
    else
      let key := it[1].getId
      if (findText? env key).isNone then
        throwErrorAt it[1] m!"spec_chapter {repr file}: there is no requirement text {key}; \
          import its text module (e.g. Libpetri.Spec.Text.{key})"
      if seen.contains key then
        throwErrorAt it[1] m!"spec_chapter {repr file}: {key} is listed twice"
      seen := seen.push key
      items := items.push (.req key)
  if items.isEmpty then fail "the chapter has no items"
  modifyEnv (chapterExt.addEntry · { file, scope, items, module := env.mainModule })

/-! ## Rendering -/

/-- The markdown of a requirement text: heading, blank line, its priority, kind and status lines,
blank line, body without markers, line break. -/
def TextEntry.render (e : TextEntry) : String :=
  let field (k v : String) : String := if v.isEmpty then "" else s!"**{k}:** {v}\n"
  s!"#### {e.id}: {e.title}\n\n" ++ field "Priority" e.priority ++ field "Kind" e.kind ++
    field "Status" e.status ++ "\n" ++ e.plain ++ "\n"

/-- The source file of a module, relative to the repository root. -/
def moduleSource (m : Name) : String :=
  "lean/" ++ "/".intercalate (m.components.map toString) ++ ".lean"

/-- The requirement texts a chapter lists, in order. -/
def Chapter.texts (env : Environment) (c : Chapter) : Array TextEntry :=
  c.items.filterMap fun | .req k => findText? env k | _ => none

/-- The glossary terms of a chapter, in order, as (name, text). -/
def Chapter.terms (c : Chapter) : Array (String × String) :=
  c.items.filterMap fun | .term t b => some (t, b) | _ => none

end Text

end Libpetri.Spec
