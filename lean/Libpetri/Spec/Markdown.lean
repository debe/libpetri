import Lean
/-!
# Reading the generated markdown

This module is tooling, not specification. It is the one reader of the markdown the spec text
renders to (`Libpetri.Spec.Generate` renders `spec/*.md` from `Libpetri.Spec.Text`). Two consumers
use it, both in `Libpetri.Spec.Generate`:

* `#write_spec_json` (run by `spec-tools/Report.lean`), which writes `lean/report/spec.json`: every
  requirement with its body cut into paragraphs, acceptance criteria, notes, depends-on and test
  derivation, the glossary terms and the ledger entries. The spec site and the coverage matrix
  read that file instead of parsing markdown.
* `#audit_spec` (run by `spec-tools/Audit.lean`), whose "uncovered" rule needs the normative
  sentences of a requirement: its body cut into units (paragraphs, list bullets, table rows) and
  each unit into sentences.

The rules follow plain CommonMark where they need it and are simple elsewhere:

* **Scan.** A fenced code block opens at a line of at least three backticks or tildes indented at
  most three spaces (a backtick fence whose info string holds a backtick is not one) and closes at
  a line of at least as many of the same character; an unclosed fence runs to the end. HTML
  comments outside fences are removed, across lines. `strip` also blanks fence lines and drops
  `~~strikethrough~~`.
* **Units** (`units`, for the audit): a blank line or a thematic break (`---`) ends a unit; a list
  bullet, a heading and a table row each start one; a line indented four spaces or more outside a
  paragraph or list is indented code and dropped. A unit's text has its emphasis markers (`*`,
  `_`) removed and its whitespace collapsed (`norm`). A unit is cut into sentences after `.`, `!`
  or `?` (optionally followed by a quote, parenthesis or bracket) where a space and an upper-case
  letter, digit, quote or bracket follow. A numbered bullet of the list after an `Acceptance
  Criteria:` paragraph is acceptance criterion `AC<n>`.
* **Chunks** (`chunks`, for the JSON): a blank line or a thematic break ends a chunk outside a
  fence, and a `**Label:**` line starts one. A chunk is joined back into one markdown string
  (`joinMarkdown`): wrapped prose lines are joined with a space, list items, table rows and fenced
  code keep their own lines. `fields` sorts the chunks of a requirement section into its priority,
  kind and status lines, its `**Depends on:**` IDs, its body paragraphs (`shall` when they hold
  the word *shall*, `code` for fenced code, `prose` otherwise), its acceptance criteria, its test
  derivation and its other labelled notes.

Whitespace is ASCII (space, tab, line feed, carriage return, form feed, vertical tab) and a word
character for `\b` is an ASCII letter, digit or `_`.
-/
set_option linter.missingDocs true

namespace Libpetri.Spec.Markdown

/-! ## Characters and strings -/

/-- Whitespace: ASCII space, tab, line feed, carriage return, form feed and vertical tab. -/
def isWs (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c' || c == '\x0b'

/-- A word character of `\b`: an ASCII letter, digit or `_`. -/
def isWord (c : Char) : Bool := c.isAlphanum || c == '_'

/-- An upper-case ASCII letter. -/
def isUpper (c : Char) : Bool := 'A' ≤ c && c ≤ 'Z'

/-- The characters `i` (inclusive) to `j` (exclusive) of `a`, as a string. -/
def sub (a : Array Char) (i j : Nat) : String := String.ofList (a.extract i j).toList

/-- Does `pat` occur in `a` at `i`? -/
def startsAt (a : Array Char) (i : Nat) (pat : String) : Bool :=
  let p := pat.toList
  i + p.length ≤ a.size && (p.zipIdx.all fun (c, k) => a[i + k]! == c)

/-- `s` without whitespace at either end. -/
def trim (s : String) : String := Id.run do
  let a := s.toList.toArray
  let mut i := 0
  while i < a.size && isWs a[i]! do i := i + 1
  let mut j := a.size
  while j > i && isWs a[j - 1]! do j := j - 1
  return sub a i j

/-- `s` without whitespace at its start. -/
def trimStart (s : String) : String := String.ofList (s.toList.dropWhile isWs)

/-- `s` without whitespace at its end. -/
def trimEnd (s : String) : String := String.ofList (s.toList.reverse.dropWhile isWs).reverse

/-- The whitespace characters `s` starts with. -/
def indentOf (s : String) : Nat := (s.toList.takeWhile isWs).length

/-- The spaces `s` starts with. -/
def leadingSpaces (s : String) : Nat := (s.toList.takeWhile (· == ' ')).length

/-- `s` without its first `n` characters. -/
def dropN (s : String) (n : Nat) : String := String.ofList (s.toList.drop n)

/-- The lines of `s`, split at line feeds; a final line feed ends the last line and does not
start an empty one. -/
def lines (s : String) : Array String :=
  if s.isEmpty then #[] else
    let parts := (s.splitOn "\n").toArray
    if s.endsWith "\n" then parts.pop else parts

/-- `s` with every whitespace run made one space and none at either end. -/
def collapse (s : String) : String := Id.run do
  let mut out : Array Char := #[]
  let mut gap := false
  for c in s.toList do
    if isWs c then
      gap := true
    else
      if gap && !out.isEmpty then out := out.push ' '
      gap := false
      out := out.push c
  return String.ofList out.toList

/-- `s` without emphasis markers (`*`, `_`), its whitespace collapsed. -/
def norm (s : String) : String := collapse (String.ofList (s.toList.filter fun c => c != '*' && c != '_'))

/-- Does the word `w` (lower case) occur in `s`, any case, between word boundaries? -/
def hasWord (w : String) (s : String) : Bool := Id.run do
  let a := s.toList.toArray.map Char.toLower
  let n := w.length
  for i in [0:a.size] do
    if startsAt a i w && (i == 0 || !isWord a[i - 1]!) && (i + n == a.size || !isWord a[i + n]!) then
      return true
  return false

/-- Does `s` hold the word *shall*, any case? -/
def hasShall (s : String) : Bool := hasWord "shall" s

/-- The IDs written `[ID]` in `s`, `ID` an upper-case prefix, `-` and digits, in order of first
mention, each once. -/
def bracketRefs (s : String) : Array String := Id.run do
  let a := s.toList.toArray
  let mut out : Array String := #[]
  let mut i := 0
  while i < a.size do
    if a[i]! == '[' then
      let mut j := i + 1
      while j < a.size && isUpper a[j]! do j := j + 1
      if j > i + 1 && j < a.size && a[j]! == '-' then
        let mut k := j + 1
        while k < a.size && a[k]!.isDigit do k := k + 1
        if k > j + 1 && k < a.size && a[k]! == ']' then
          let id := sub a (i + 1) k
          unless out.contains id do out := out.push id
          i := k + 1
          continue
    i := i + 1
  return out

/-! ## Line shapes -/

/-- The level of an ATX heading line (at most three spaces, one to six `#`, then whitespace or
the end), if it is one. -/
def headingLevel? (line : String) : Option Nat := Id.run do
  let a := line.toList.toArray
  let i := leadingSpaces line
  if i > 3 then return none
  let mut j := i
  while j < a.size && a[j]! == '#' do j := j + 1
  if 1 ≤ j - i && j - i ≤ 6 && (j == a.size || isWs a[j]!) then return some (j - i)
  return none

/-- Is the line a heading of level 1 to 4, the lines a requirement section ends at? -/
def isSectionBreak (line : String) : Bool := (headingLevel? line).any (· ≤ 4)

/-- The ID of a canonical requirement heading `#### ID:` (ID an upper-case prefix, `-` and
digits), if the line is one. -/
def canonId? (line : String) : Option String := Id.run do
  unless line.startsWith "#### " do return none
  let a := line.toList.toArray
  let mut j := 5
  while j < a.size && isUpper a[j]! do j := j + 1
  if j == 5 || j ≥ a.size || a[j]! != '-' then return none
  let mut k := j + 1
  while k < a.size && a[k]!.isDigit do k := k + 1
  if k == j + 1 || k ≥ a.size || a[k]! != ':' then return none
  return some (sub a 5 k)

/-- Is the line a thematic break: at most three spaces, then at least three of one of `-`, `*`,
`_`, with only whitespace between and after them? -/
def isThematic (line : String) : Bool := Id.run do
  let a := line.toList.toArray
  let i := leadingSpaces line
  if i > 3 || i ≥ a.size then return false
  let c := a[i]!
  unless c == '-' || c == '*' || c == '_' do return false
  let mut n := 0
  for k in [i:a.size] do
    if a[k]! == c then n := n + 1
    else if !isWs a[k]! then return false
  return n ≥ 3

/-- A list marker at the start of a line. -/
structure ListMatch where
  /-- The number of an ordered marker (`3.` or `3)`); `none` for `-`, `*` or `+`. -/
  num : Option Nat
  /-- The line after the marker and the whitespace that follows it. -/
  rest : String
  /-- The characters up to `rest`: indentation, marker and whitespace. -/
  len : Nat

/-- The list marker the line starts with, after any whitespace: one to nine digits and `.` or
`)`, or one of `-`, `*`, `+`; followed by whitespace or the end of the line. -/
def listMatch? (line : String) : Option ListMatch := Id.run do
  let a := line.toList.toArray
  let i := indentOf line
  if i ≥ a.size then return none
  let mut e := i
  let mut num : Option Nat := none
  if a[i]!.isDigit then
    let mut j := i
    while j < a.size && a[j]!.isDigit do j := j + 1
    if j - i > 9 || j ≥ a.size || !(a[j]! == '.' || a[j]! == ')') then return none
    num := some (sub a i j).toNat!
    e := j + 1
  else if a[i]! == '-' || a[i]! == '*' || a[i]! == '+' then
    e := i + 1
  else
    return none
  if e == a.size then return some { num, rest := "", len := e }
  unless isWs a[e]! do return none
  let mut r := e
  while r < a.size && isWs a[r]! do r := r + 1
  return some { num, rest := sub a r a.size, len := r }

/-- The fence a line opens (its character and length), if it opens one. -/
def fenceOpen? (line : String) : Option (Char × Nat) := Id.run do
  let a := line.toList.toArray
  let i := leadingSpaces line
  if i > 3 || i ≥ a.size then return none
  let c := a[i]!
  unless c == '`' || c == '~' do return none
  let mut j := i
  while j < a.size && a[j]! == c do j := j + 1
  if j - i < 3 then return none
  if c == '`' && (a.extract j a.size).contains '`' then return none
  return some (c, j - i)

/-- Does the line close a fence of `n` characters `c`? -/
def closesFence (c : Char) (n : Nat) (line : String) : Bool := Id.run do
  let a := line.toList.toArray
  let i := leadingSpaces line
  if i > 3 then return false
  let mut j := i
  while j < a.size && a[j]! == c do j := j + 1
  return j - i ≥ n && (a.extract j a.size).all isWs

/-- Does the line start a fence (at most three spaces, then three backticks or tildes)? -/
def isFenceLine (line : String) : Bool := Id.run do
  let a := line.toList.toArray
  let i := leadingSpaces line
  if i > 3 then return false
  return startsAt a i "```" || startsAt a i "~~~"

/-- A `**Label:** rest` line: the label and the rest after the whitespace that follows it. The
label holds no `*`. -/
def label? (line : String) : Option (String × String) := Id.run do
  unless line.startsWith "**" do return none
  let a := line.toList.toArray
  let mut k := 2
  while k < a.size && a[k]! != '*' do k := k + 1
  if k < 4 || k + 1 ≥ a.size || a[k - 1]! != ':' || a[k + 1]! != '*' then return none
  let mut r := k + 2
  while r < a.size && isWs a[r]! do r := r + 1
  return some (sub a 2 (k - 1), sub a r a.size)

/-! ## Scan -/

/-- One line after the scan. -/
structure Line where
  /-- The line without its HTML comments; the raw line inside a fence. -/
  text : String
  /-- Is it a fence's opening line, one of its lines or its closing line? -/
  fence : Bool
  deriving Inhabited

/-- Remove the HTML comments of a line; `inC` says whether a comment is open when it starts.
Returns the text kept and whether a comment is open at its end. -/
def dropComments (line : String) (inC : Bool) : String × Bool := Id.run do
  let a := line.toList.toArray
  let mut kept : Array Char := #[]
  let mut i := 0
  let mut open_ := inC
  while i < a.size do
    if open_ then
      if startsAt a i "-->" then
        open_ := false
        i := i + 3
      else
        i := i + 1
    else if startsAt a i "<!--" then
      open_ := true
      i := i + 4
    else
      kept := kept.push a[i]!
      i := i + 1
  return (String.ofList kept.toList, open_)

/-- The scan of a file's lines (the module docstring), one entry per line, and whether a comment
or a fence is still open at the end. -/
def scanOpen (ls : Array String) : Array Line × Bool := Id.run do
  let mut out : Array Line := #[]
  let mut inC := false
  let mut fence : Option (Char × Nat) := none
  for line in ls do
    if let some (c, n) := fence then
      if closesFence c n line then fence := none
      out := out.push { text := line, fence := true }
      continue
    if !inC then
      if let some f := fenceOpen? line then
        fence := some f
        out := out.push { text := line, fence := true }
        continue
    let (kept, c) := dropComments line inC
    inC := c
    out := out.push { text := kept, fence := false }
  return (out, inC || fence.isSome)

/-- The scan of a file's lines. -/
def scan (ls : Array String) : Array Line := (scanOpen ls).1

/-- `s` without its `~~strikethrough~~` spans. -/
def dropStrike (s : String) : String := Id.run do
  let a := s.toList.toArray
  let mut out : Array Char := #[]
  let mut p := 0
  while p < a.size do
    if startsAt a p "~~" then
      let mut q := p + 2
      let mut found := false
      while !found && q + 1 < a.size do
        if startsAt a q "~~" then found := true else q := q + 1
      if found then
        p := q + 2
        continue
    out := out.push a[p]!
    p := p + 1
  return String.ofList out.toList

/-- A scanned line as the units and headings see it: blank inside a fence, without
strike-through. -/
def stripped (l : Line) : String := if l.fence then "" else dropStrike l.text

/-- The text of a heading line: trimmed, without its leading `#` run and the whitespace after it. -/
def headingBody (line : String) : String :=
  trim (String.ofList ((trim line).toList.dropWhile (· == '#')))

/-- `headingBody` without a closing sequence (whitespace, then `#`s, at the end). -/
def headingText (line : String) : String :=
  let t := headingBody line
  let r := t.toList.reverse
  let hashes := r.takeWhile (· == '#')
  let after := r.drop hashes.length
  if !hashes.isEmpty && after.head?.any isWs then
    trim (String.ofList (after.dropWhile isWs).reverse)
  else t

/-! ## Units and sentences (the audit's uncovered rule) -/

/-- Split normalised text into sentences: at a space after `.`, `!` or `?` (or after one of them
and a quote, parenthesis or bracket) before an upper-case letter, digit, quote, backtick,
parenthesis or bracket. -/
def sentences (t : String) : Array String := Id.run do
  let a := t.toList.toArray
  let stop (c : Char) : Bool := c == '.' || c == '!' || c == '?'
  let close (c : Char) : Bool := c == '"' || c == '\'' || c == ')' || c == ']'
  let next (c : Char) : Bool := isUpper c || c.isDigit || "\"'`([".toList.contains c
  let mut out : Array String := #[]
  let mut start := 0
  let mut i := 0
  while i < a.size do
    if isWs a[i]! && i > 0 then
      let mut j := i
      while j < a.size && isWs a[j]! do j := j + 1
      let p := a[i - 1]!
      let before := stop p || (close p && i ≥ 2 && stop a[i - 2]!)
      if before && j < a.size && next a[j]! then
        out := out.push (sub a start i)
        start := j
      i := j
    else
      i := i + 1
  out := out.push (sub a start a.size)
  return out.filter (!·.isEmpty)

/-- A paragraph, list bullet or table row of a section body, as normalised sentences. -/
structure TextUnit where
  /-- Its sentences, normalised (`norm`). -/
  sents : Array String
  /-- The number of a top-level Acceptance Criteria bullet. -/
  ac : Option Nat
  deriving Inhabited

/-- Is the normalised text an `Acceptance Criteria` heading paragraph? -/
def isAcHead (t : String) : Bool :=
  let l := t.toLower
  l == "acceptance criteria" || l == "acceptance criteria:"

/-- Cut the stripped lines of a section body into units (the module docstring). -/
def units (body : Array String) : Array TextUnit := Id.run do
  -- raw units: kind (0 item, 1 paragraph, 2 other), lines, number, indentation
  let mut raw : Array (Nat × Array String × Option Nat × Nat) := #[]
  let mut cur : Option (Nat × Array String × Option Nat × Nat) := none
  let mut inList := false
  for line in body do
    if (trim line).isEmpty then
      if let some u := cur then raw := raw.push u
      cur := none
      continue
    let indent := leadingSpaces line
    if indent ≥ 4 && cur.isNone && !inList then continue
    if isThematic line then
      if let some u := cur then raw := raw.push u
      cur := none
      inList := false
      continue
    if let some m := listMatch? line then
      if indent < 4 || inList then
        if let some u := cur then raw := raw.push u
        cur := some (0, #[m.rest], m.num, indent)
        inList := true
        continue
    if (headingLevel? line).isSome || (trimStart line).startsWith "|" then
      if let some u := cur then raw := raw.push u
      cur := none
      raw := raw.push (2, #[String.ofList ((trim line).toList.dropWhile (· == '#'))], none, indent)
      inList := false
      continue
    if let some (k, ls, n, ind) := cur then
      cur := some (k, ls.push (trim line), n, ind)
      continue
    if !(inList && indent ≥ 2) then inList := false
    cur := some (1, #[trim line], none, indent)
  if let some u := cur then raw := raw.push u
  let mut out : Array TextUnit := #[]
  let mut acIndent : Option Nat := none
  let mut inAc := false
  for (kind, ls, num, indent) in raw do
    let text := norm (" ".intercalate ls.toList)
    if text.isEmpty then continue
    let mut ac : Option Nat := none
    if kind == 1 && isAcHead text then
      inAc := true
      acIndent := none
    else if kind == 0 && inAc then
      if num.isSome && (acIndent.isNone || acIndent == some indent) then
        acIndent := some indent
        ac := num
    else if inAc && !(kind == 1 && acIndent.isSome && indent > acIndent.getD 0) then
      inAc := false
    out := out.push { sents := sentences text, ac }
  return out

/-- The positions (unit, sentence) of every run of whole consecutive sentences of one unit
equal to the normalised text `q`. -/
def matchQuote (q : String) (us : Array TextUnit) : Array (Nat × Nat) := Id.run do
  let mut hits : Array (Nat × Nat) := #[]
  for ui in [0:us.size] do
    let ss := us[ui]!.sents
    for a in [0:ss.size] do
      let mut run := ""
      for b in [a:ss.size] do
        run := if b == a then ss[b]! else run ++ " " ++ ss[b]!
        if run.length > q.length then break
        if run == q then
          for k in [a:b + 1] do hits := hits.push (ui, k)
          break
  return hits

/-- The numbers `n` of the mentions `AC<n>` or `AC <n>` (between word boundaries) in `s`. -/
def acMentions (s : String) : Array Nat := Id.run do
  let a := s.toList.toArray
  let mut out : Array Nat := #[]
  for i in [0:a.size] do
    if startsAt a i "AC" && (i == 0 || !isWord a[i - 1]!) then
      let mut j := i + 2
      if j < a.size && isWs a[j]! then j := j + 1
      let mut k := j
      while k < a.size && a[k]!.isDigit do k := k + 1
      if k > j && (k == a.size || !isWord a[k]!) then out := out.push (sub a j k).toNat!
  return out

/-- The values of the `**Kind:**` lines (at most three spaces before them) of stripped lines,
trimmed. -/
def kindLines (body : Array String) : Array String :=
  body.filterMap fun line =>
    let i := leadingSpaces line
    if i ≤ 3 && (dropN line i).startsWith "**Kind:**" then some (trim (dropN line (i + 9)))
    else none

/-! ## Chunks and fields (the JSON) -/

/-- A run of scanned lines without a blank line between them (a fence may hold blank lines). -/
abbrev Chunk := Array Line

/-- Cut scanned lines into chunks at blank lines and thematic breaks outside fences; with
`labels`, a `**Label:**` line starts a chunk. -/
def chunks (ls : Array Line) (labels : Bool) : Array Chunk := Id.run do
  let mut out : Array Chunk := #[]
  let mut cur : Option Chunk := none
  for l in ls do
    if l.fence then
      cur := some ((cur.getD #[]).push l)
      continue
    if (trim l.text).isEmpty || isThematic l.text then
      if let some c := cur then out := out.push c
      cur := none
      continue
    if labels && (label? l.text).isSome then
      if let some c := cur then out := out.push c
      cur := none
    cur := some ((cur.getD #[]).push l)
  if let some c := cur then out := out.push c
  return out

/-- Is the trimmed text a list item (a list marker at its start)? -/
def isItem (t : String) : Bool := (listMatch? t).isSome && indentOf t == 0

/-- Join the lines of a chunk into one markdown string: wrapped prose lines are joined with a
space; list items, table rows and fence lines keep their own lines; a list right after prose gets
a blank line first; the common indentation of the prose lines is removed. -/
def joinMarkdown (ls : Array Line) : String := Id.run do
  let prose := ls.filter fun l => !l.fence && !(trim l.text).isEmpty
  let base := match prose.toList.map (indentOf ·.text) with
    | [] => 0
    | x :: xs => xs.foldl min x
  let dedent (t : String) : String := dropN t (min base (indentOf t))
  let mut out : Array String := #[]
  let mut lastWasFence := false
  let mut inList := false
  for l in ls do
    if l.fence then
      out := out.push (trimEnd (dedent l.text))
      lastWasFence := true
      continue
    let t := trim l.text
    let item := isItem t
    if item && !inList && !out.isEmpty && !lastWasFence then out := out.push ""
    let startsLine := out.isEmpty || lastWasFence || item || t.startsWith "|"
    if startsLine then out := out.push (trimEnd (dedent l.text))
    else out := out.set! (out.size - 1) (out[out.size - 1]! ++ " " ++ t)
    if item then inList := true
    lastWasFence := false
  return "\n".intercalate out.toList

/-- Cut list lines into items, each without its marker and joined (`joinMarkdown`); a marker
left of the current item's content column opens an item, one further right is a nested list.
Fails on a line before the first marker. -/
def listItems (ls : Array Line) : Except String (Array String) := do
  let mut items : Array (Array Line) := #[]
  let mut column := 0
  for l in ls do
    let marker := if l.fence then none else listMatch? l.text
    if let some m := marker then
      if indentOf l.text < (if items.isEmpty then 4 else column) then
        column := m.len
        items := items.push #[{ text := dropN l.text column, fence := false }]
        continue
    if items.isEmpty then throw "text before the first list item"
    items := items.modify (items.size - 1)
      (·.push { text := dropN l.text (min column (indentOf l.text)), fence := l.fence })
  return items.map joinMarkdown

/-- Cut a chunk where fenced code starts or ends. -/
def splitFences (c : Chunk) : Array Chunk := Id.run do
  let mut out : Array Chunk := #[]
  let mut start := 0
  for i in [1:c.size] do
    if c[i]!.fence != c[i - 1]!.fence then
      out := out.push (c.extract start i)
      start := i
  out := out.push (c.extract start c.size)
  return out

/-- Cut a chunk where a list starts right after prose lines, so the paragraph and the list are
two chunks. -/
def splitProseAndList (c : Chunk) : Array Chunk := Id.run do
  let mut at_ : Option Nat := none
  for i in [1:c.size] do
    let l := c[i]!
    if at_.isNone && !l.fence && isItem (trim l.text) && indentOf l.text ≤ 3 then at_ := some i
  match at_ with
  | none => #[c]
  | some k =>
    if (c.extract 0 k).any (fun l => l.fence || isItem (trim l.text)) then #[c]
    else #[c.extract 0 k, c.extract k c.size]

/-- A body paragraph: its kind (`shall`, `prose` or `code`) and its markdown. -/
structure Paragraph where
  /-- `shall`, `prose` or `code`. -/
  kind : String
  /-- The markdown; for `code`, the lines between the fences. -/
  text : String

/-- The paragraph of a body chunk: fenced code keeps its lines without the fences; other text is
`shall` when it holds the word *shall*, else `prose`. -/
def paragraph (c : Chunk) : Paragraph :=
  if c[0]?.any (·.fence) then
    let ls := c.map (trimEnd ·.text)
    let closed := ls.size > 1 && isFenceLine ls[ls.size - 1]!
    { kind := "code", text := "\n".intercalate (ls.extract 1 (if closed then ls.size - 1 else ls.size)).toList }
  else
    let t := joinMarkdown c
    { kind := if hasShall t then "shall" else "prose", text := t }

/-- The fields of a requirement section. -/
structure Fields where
  /-- The value of the `**Priority:**` line. -/
  priority : Option String := none
  /-- The value of the `**Kind:**` line. -/
  kind : Option String := none
  /-- `removed` or `proposed`, from the `**Status:**` line. -/
  status : Option String := none
  /-- The IDs of the `**Depends on:**` lines, in order, each once. -/
  dependsOn : Array String := #[]
  /-- The body paragraphs, in order. -/
  body : Array Paragraph := #[]
  /-- The acceptance criteria, without their numbers. -/
  acceptance : Array String := #[]
  /-- The other labelled notes: label and markdown. -/
  notes : Array (String × String) := #[]
  /-- The test derivation. -/
  testDerivation : Option String := none
  /-- The text of every chunk but the Depends on lines, for the IDs it mentions. -/
  cited : Array String := #[]

/-- Sort the chunks of a requirement section (the lines after its heading) into its fields (the
module docstring). After an acceptance criteria label a list chunk continues the list and an
indented chunk continues the last criterion; after a test derivation every unlabelled chunk
continues it; after another label an unlabelled chunk without *shall* continues the note. Fails
on a second priority, kind, status or test derivation line, an unknown priority, kind or status,
a Depends on line without an `[ID]`, and text before an acceptance criteria list. -/
def fields (ls : Array Line) : Except String Fields := do
  let mut f : Fields := {}
  -- 0 body, 1 metadata, 2 acceptance criteria, 3 test derivation, 4 note
  let mut field := 0
  for c in chunks ls true do
    let first := c[0]!
    let lab := if first.fence then none else label? first.text
    match lab with
    | none =>
      let text := joinMarkdown c
      f := { f with cited := f.cited.push text }
      if field == 2 then
        if !first.fence && (listMatch? first.text).isSome && indentOf first.text < 2 then
          f := { f with acceptance := f.acceptance ++ (← listItems c) }
          continue
        if indentOf first.text ≥ 2 && !f.acceptance.isEmpty then
          let n := f.acceptance.size - 1
          f := { f with acceptance := f.acceptance.set! n (f.acceptance[n]! ++ "\n\n" ++ text) }
          continue
      else if field == 3 then
        f := { f with testDerivation := some (f.testDerivation.getD "" ++ "\n\n" ++ text) }
        continue
      else if field == 4 && !hasShall text then
        let n := f.notes.size - 1
        let (l, t) := f.notes[n]!
        f := { f with notes := f.notes.set! n (l, t ++ "\n\n" ++ text) }
        continue
      f := { f with body := f.body ++ ((splitFences c).flatMap splitProseAndList).map paragraph }
      field := 0
    | some (name, rest0) =>
      let name := trim name
      let rest := (#[({ text := rest0, fence := false } : Line)] ++ c.extract 1 c.size).toList.zipIdx.filterMap
        fun (l, i) => if i > 0 || !(trim l.text).isEmpty then some l else none
      let rest := rest.toArray
      let value := joinMarkdown rest
      let key := name.toLower
      if key == "priority" then
        if f.priority.isSome then throw "second **Priority:** line"
        unless ["MUST", "SHOULD", "MAY"].contains value do
          throw s!"priority {repr value} is not one of MUST, SHOULD, MAY"
        f := { f with priority := some value }
        field := 1
      else if key == "kind" then
        if f.kind.isSome then throw "second **Kind:** line"
        unless ["A", "B", "F", "T", "Q", "N"].contains value do
          throw s!"kind {repr value} is not one of A, B, F, T, Q, N"
        f := { f with kind := some value }
        field := 1
      else if key == "status" then
        if f.status.isSome then throw "second **Status:** line"
        let v := value.toLower
        if v == "removed" || v == "removed." then f := { f with status := some "removed" }
        else if v == "proposed" || v == "proposed." then f := { f with status := some "proposed" }
        else throw s!"status {repr value} is neither Removed nor Proposed"
        field := 1
      else if key == "depends on" then
        let ids := bracketRefs value
        if ids.isEmpty then throw "**Depends on:** names no [ID]"
        let deps := ids.foldl (fun acc i => if acc.contains i then acc else acc.push i) f.dependsOn
        f := { f with dependsOn := deps }
        field := 1
      else if key.startsWith "acceptance criteria" then
        let items ← match listItems rest with
          | .ok xs => pure xs
          | .error _ => throw "text before the first acceptance criterion"
        f := { f with cited := f.cited.push value, acceptance := f.acceptance ++ items }
        field := 2
      else if key == "test derivation" then
        if f.testDerivation.isSome then throw "second **Test derivation:** line"
        f := { f with cited := f.cited.push value, testDerivation := some value }
        field := 3
      else
        f := { f with cited := f.cited.push value, notes := f.notes.push (name, value) }
        field := 4
  return f

/-! ## Examples

Each `#guard` runs at build time; a reader that drifts from these fails the build. -/

#guard stripped <$> scan #["a <!-- x", "y --> b", "```", "# no", "```", "~~gone~~ kept"] ==
  #["a ", " b", "", "", "", " kept"]
#guard (scan #["~~~", "x", "~~~~"]).map (·.fence) == #[true, true, true]
#guard (units #["A *first* one. Second one.", "", "Acceptance Criteria:", "1. One.", "2. Two.", "",
    "After."]).map (fun u => (u.sents, u.ac)) ==
  #[(#["A first one.", "Second one."], none), (#["Acceptance Criteria:"], none), (#["One."], some 1),
    (#["Two."], some 2), (#["After."], none)]
#guard matchQuote (norm "Two. Three.") (units #["One. Two. Three."]) == #[(0, 1), (0, 2)]
#guard matchQuote (norm "Tw") (units #["One. Two. Three."]) == #[]
#guard sentences "Ends with \"quote.\" Next" == #["Ends with \"quote.\"", "Next"]
#guard hasShall "it *shall* hold" && !hasShall "marshall" && hasShall "Shall."
#guard acMentions "covers AC2 and AC 3, not ACME4" == #[2, 3]
#guard joinMarkdown (scan #["Para line one", "line two:", "- item a", "  wrapped a", "```", "code", "```"]) ==
  "Para line one line two:\n\n- item a wrapped a\n```\ncode\n```"
#guard (chunks (scan #["**A:** x", "**B:** y", "z", "", "w"]) true).map (·.map (·.text)) ==
  #[#["**A:** x"], #["**B:** y", "z"], #["w"]]
#guard bracketRefs "[CORE-002], [RV-08] and [CORE-002] [x]" == #["CORE-002", "RV-08"]

/-- A requirement section for the examples of `fields`. -/
private def exampleSection : String := r#"**Priority:** MUST
**Kind:** B

A place holds tokens. Each place has a name. It can:
1. hold tokens,
2. be named.

*When* a transition fires, it *shall* consume from each input place.

```
#### NOT-001: inside a fence
```

**Note:** Names follow [MOD-010] and [CORE-009]
for subnets.

More of the note.

**Acceptance Criteria:**
1. A place can be created.
2. The name is kept,
   across a restart.
   - nested detail

3. After a blank line the list goes on.

Context after the list cites [CORE-002].

**Depends on:** [CORE-002],
[CORE-003]
**Test derivation:** Create a place.

A second paragraph of the derivation.
"#

#guard match fields (scan (lines exampleSection)) with
  | .ok f =>
    f.priority == some "MUST" && f.kind == some "B" && f.status == none &&
    f.body.map (fun p => (p.kind, p.text)) == #[
      ("prose", "A place holds tokens. Each place has a name. It can:"),
      ("prose", "1. hold tokens,\n2. be named."),
      ("shall", "*When* a transition fires, it *shall* consume from each input place."),
      ("code", "#### NOT-001: inside a fence"),
      ("prose", "Context after the list cites [CORE-002].")] &&
    f.notes == #[("Note", "Names follow [MOD-010] and [CORE-009] for subnets.\n\nMore of the note.")] &&
    f.acceptance == #["A place can be created.", "The name is kept, across a restart.\n\n- nested detail",
      "After a blank line the list goes on."] &&
    f.dependsOn == #["CORE-002", "CORE-003"] &&
    f.testDerivation == some "Create a place.\n\nA second paragraph of the derivation."
  | .error _ => false

#guard match fields (scan (lines "**Priority:** MAY\n\nIt *shall* do it.\n\n**Status:** Proposed\n**Implementation status:** Java only.\n\nIt *shall* be visible.\n")) with
  | .ok f => f.status == some "proposed" && f.notes == #[("Implementation status", "Java only.")] &&
    f.body.map (·.kind) == #["shall", "shall"]
  | .error _ => false

#guard (fields (scan #["**Priority:** OFTEN"])).toOption.isNone
#guard (fields (scan #["**Kind:** B", "**Kind:** F"])).toOption.isNone

end Libpetri.Spec.Markdown
