import Libpetri.Spec.Text
/-!
# The runtime ledger

This module is tooling, not specification. It holds the runtime ledger (`spec/runtime-defects.md`
is generated from it, by `Libpetri.Spec.Generate`) as typed declarations, one command per kind of
entry:

* `runtime_defect RD_NN`, a place where a runtime breaks or broke a requirement the spec keeps:
  the requirements it breaks, the runtimes, the defect, the Lean evidence, the fix and the status;
* `unbuilt_requirement UB_NN`, a `**Status:** Proposed` requirement that a runtime it targets has
  not built;
* `ledger_divergence`, one row of the divergence table: an implementation-defined difference that
  the spec allows.

What the commands check, at elaboration:

* every spec ID an entry names is the ID of a requirement text, so the module that declares an
  entry imports the text modules of the requirements it names (`Libpetri.Spec.Text.EXEC_021`);
  an unbuilt entry names `Proposed` requirements only;
* every Lean name of a defect's evidence, written `⟪name⟫`, is a declaration, so the module
  imports the modules that declare them; a name is matched by its last components, so
  `⟪ExportNet.ClusterKeysWellFormed⟫` finds `Libpetri.Spec.ExportNet.ClusterKeysWellFormed`;
* the runtimes are Java, TypeScript, Rust and Python (`all` for the four), and the status is
  `open`, `fixed, unreleased` or `fixed in <version>`.

An entry's items are markdown. A line break inside an item is written as is: the generated file
indents the lines that continue an item by two spaces. `⟪name⟫` renders as `` `name` ``.

It imports only `Libpetri.Spec.Text`, so that it builds light; an entry module imports what its
entry names.
-/
set_option linter.missingDocs true

open Lean Elab Command

namespace Libpetri.Spec.Ledger

open Libpetri.Spec.Text

/-- One `runtime_defect` entry. -/
structure Defect where
  /-- The name it is declared with, e.g. `RD_01`. -/
  key : Name
  /-- `RD-01`. -/
  id : String
  /-- The number, `1` for `RD-01`. -/
  num : Nat
  /-- The title, as the `### RD-01. Title` heading shows it. -/
  title : String
  /-- The Requirements item: the requirements it breaks, with the reading of each. -/
  requirements : String
  /-- The Runtimes item. -/
  runtimes : String
  /-- The Defect item. -/
  defect : String
  /-- The Lean evidence item, its Lean names marked `⟪name⟫`. -/
  evidence : String
  /-- The Fix item; empty for an entry without one. -/
  fix : String
  /-- `open`, `fixed, unreleased` or `fixed in <version>`. -/
  status : String
  /-- The module the entry is declared in. -/
  module : Name
  deriving Inhabited

/-- One `unbuilt_requirement` entry. -/
structure Unbuilt where
  /-- The name it is declared with, e.g. `UB_01`. -/
  key : Name
  /-- `UB-01`. -/
  id : String
  /-- The number, `1` for `UB-01`. -/
  num : Nat
  /-- The title. -/
  title : String
  /-- The Requirements item. -/
  requirements : String
  /-- The Runtimes item. -/
  runtimes : String
  /-- The Missing item: what the runtimes lack. -/
  missing : String
  /-- The status. -/
  status : String
  /-- The module the entry is declared in. -/
  module : Name
  deriving Inhabited

/-- One row of the divergence table. -/
structure Divergence where
  /-- The aspect the implementations differ in. -/
  aspect : String
  /-- What the spec says. -/
  spec : String
  /-- What Java does. -/
  java : String
  /-- What TypeScript does. -/
  typescript : String
  /-- What Rust does (and Python, unless the cell says otherwise). -/
  rust : String
  /-- The module the row is declared in. -/
  module : Name
  deriving Inhabited

/-- Persistent store of the defect entries. -/
initialize defectExt : SimplePersistentEnvExtension Defect (Array Defect) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun as => as.foldl (· ++ ·) #[]
  }

/-- Persistent store of the unbuilt entries. -/
initialize unbuiltExt : SimplePersistentEnvExtension Unbuilt (Array Unbuilt) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun as => as.foldl (· ++ ·) #[]
  }

/-- Persistent store of the divergence rows, in declaration order. -/
initialize divergenceExt : SimplePersistentEnvExtension Divergence (Array Divergence) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun as => as.foldl (· ++ ·) #[]
  }

/-! ## Reading the items -/

/-- Is `c` a letter, a digit or `_`? -/
def wordChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- The spec IDs `s` names, bracketed or not (`[A-Z]{2,6}-[0-9]{3}` between word boundaries), in
order, each once. -/
def specIdsIn (s : String) : Array String := Id.run do
  let cs := s.toList.toArray
  let mut out : Array String := #[]
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    if 'A' ≤ c && c ≤ 'Z' && (i == 0 || !wordChar cs[i - 1]!) then
      let mut j := i
      while j < cs.size && 'A' ≤ cs[j]! && cs[j]! ≤ 'Z' do j := j + 1
      let n := j - i
      if 2 ≤ n && n ≤ 6 && j + 4 ≤ cs.size && cs[j]! == '-' &&
          cs[j + 1]!.isDigit && cs[j + 2]!.isDigit && cs[j + 3]!.isDigit &&
          (j + 4 == cs.size || !wordChar cs[j + 4]!) then
        let id := String.ofList (cs.extract i (j + 4)).toList
        unless out.contains id do out := out.push id
        i := j + 4
      else
        i := j
    else
      i := i + 1
  return out

/-- The runtimes, in the order the ledger names them. -/
def runtimeNames : List String := ["Java", "TypeScript", "Rust", "Python"]

/-- The runtimes a Runtimes item names, in the item's order; `all` names the four, as `Rust, Java,
TypeScript, Python`. The item is cut at every comma and every word `and`, and each part is named by
its first word (`Python through Rust` is Python, `Java (both executors)` is Java), as the spec
site reads it. `none` when a part names no runtime. -/
def parseRuntimes (text : String) : Option (Array String) := Id.run do
  let plain := (if text.endsWith "." then (text.dropEnd 1).toString else text).trimAscii.toString
  if plain.toLower == "all" then return some #["Rust", "Java", "TypeScript", "Python"]
  let mut groups : Array (List String) := #[]
  for part in plain.splitOn "," do
    let mut cur : List String := []
    for w in ((part.replace "\n" " ").splitOn " ").filter (· ≠ "") do
      if w == "and" then
        groups := groups.push cur.reverse
        cur := []
      else
        cur := w :: cur
    groups := groups.push cur.reverse
  let mut out : Array String := #[]
  for g in groups do
    let some w := g.head? | continue
    let some r := runtimeNames.find? (·.toLower == w.toLower) | return none
    unless out.contains r do out := out.push r
  return if out.isEmpty then none else some out

/-- Is `s` a ledger status: `open`, `fixed, unreleased` or `fixed in <version>`? -/
def validStatus (s : String) : Bool :=
  s == "open" || s == "fixed, unreleased" ||
    (s.startsWith "fixed in " && let v := (s.drop 9).toString
      !v.isEmpty && !v.contains ' ' && v.any Char.isDigit)

/-- Split a text with `⟪name⟫` markers into the text shown (each marker becomes a code span) and
the names, in order. Fails on an unbalanced or nested marker or an empty name. -/
def parseNames (s : String) : Except String (String × Array String) := Id.run do
  let mut shown := ""
  let mut names : Array String := #[]
  let mut cur : Option String := none
  for c in s.toList do
    match cur with
    | none =>
      if c == '⟪' then cur := some "" else
      if c == '⟫' then return .error "a ⟫ closes no ⟪" else shown := shown.push c
    | some n =>
      if c == '⟫' then
        if n.isEmpty || n.any (fun c => c.isWhitespace || c == '`') then
          return .error s!"⟪{n}⟫ is not a Lean name"
        names := names.push n
        shown := shown ++ "`" ++ n ++ "`"
        cur := none
      else if c == '⟪' then return .error "a ⟪ opens inside a ⟪"
      else cur := some (n.push c)
  if cur.isSome then return .error "a ⟪ is not closed with ⟫"
  return .ok (shown, names)

/-- Is the dotted name `n` the user-facing name of `c`, or its last components? -/
def nameSuffix (n c : Name) : Bool :=
  let u := (privateToUserName? c).getD c
  let a := n.components
  let b := u.components
  a.length ≤ b.length && b.drop (b.length - a.length) == a

/-- The names of `names` that no declaration of `env` has as its name or last components. -/
def unresolved (env : Environment) (names : Array String) : Array String :=
  let wanted := names.map String.toName
  let found := env.constants.fold (init := (#[] : Array Name)) fun acc c _ =>
    match wanted.find? (fun n => !acc.contains n && nameSuffix n c) with
    | some n => acc.push n
    | none => acc
  names.filter fun n => !found.contains n.toName

/-- Check that every spec ID in `texts` is a requirement text of `env`; with `proposed`, that it
is a `Proposed` one (its status, or a `**Status:** Proposed` line of its body). Returns the IDs, in order. -/
def checkIds (env : Environment) (texts : List String) (proposed : Bool := false) :
    Except String (Array String) := do
  let mut ids : Array String := #[]
  for t in texts do
    for id in specIdsIn t do
      unless ids.contains id do ids := ids.push id
  for id in ids do
    let key := Name.mkSimple (id.replace "-" "_")
    let some e := findText? env key
      | throw s!"{id} is not a requirement text; is its text module imported (import \
          Libpetri.Spec.Text.{key})?"
    if proposed && e.status != "Proposed" && !(e.plain.splitOn "\n").contains "**Status:** Proposed" then
      throw s!"{id} is not a Proposed requirement (its status is {repr e.status})"
  return ids

/-- The ID and number of a ledger key: `RD_01` is `RD-01`, number 1. -/
def keyId (pre : String) (key : Name) : Option (String × Nat) :=
  match key.toString.splitOn "_" with
  | [p, num] => if p == pre && 2 ≤ num.length && num.all Char.isDigit then
      some (s!"{pre}-{num}", num.toNat!) else none
  | _ => none

/-! ## The commands -/

/-- The `runtime_defect` command: one defect entry of the runtime ledger.

```
runtime_defect RD_01
  title "The timeout outcome is validated against the output spec"
  requirements r#"EXEC-021, EXEC-022, IO-013 (ruling D24 (a)), CORE-036."#
  runtimes r#"Java, TypeScript."#
  defect r#"both validate the timeout outcome against the whole output spec, …"#
  evidence r#"⟪EXEC_021_forbids_validateTimeout⟫ (EXEC_021.lean)."#
  fix r#"both executors of each runtime skip the output-spec validation …"#   -- optional
  status "fixed, unreleased"   -- open, fixed, unreleased, or fixed in <version>
```

The name is the ID with `-` replaced by `_`. The items are markdown, written as the ledger shows
them after the item's label. The command checks the requirements (each a requirement text), the
runtimes, the evidence names (each a declaration) and the status, and records the entry. -/
syntax (name := runtimeDefectCmd) "runtime_defect " ident &"title" str &"requirements" str
  &"runtimes" str &"defect" str &"evidence" str (&"fix" str)? &"status" str : command

@[command_elab runtimeDefectCmd, inherit_doc runtimeDefectCmd]
def elabRuntimeDefect : CommandElab := fun stx => do
  let n := stx[1]
  let key := n.getId
  let str (s : Syntax) : String := (s.isStrLit?).getD ""
  let fail {α : Type} (msg : String) : CommandElabM α :=
    throwErrorAt n m!"runtime_defect {key}: {msg}"
  let some (id, num) := keyId "RD" key | fail "the name must be RD_ and a number, e.g. RD_01"
  let title := str stx[3]
  let requirements := str stx[5]
  let runtimes := str stx[7]
  let defect := str stx[9]
  let evidence := str stx[11]
  let fix := if stx[12].getNumArgs == 2 then str stx[12][1] else ""
  let status := str stx[14]
  for (k, v) in [("title", title), ("requirements", requirements), ("runtimes", runtimes),
      ("defect", defect), ("evidence", evidence)] do
    if blank v then fail s!"empty {k}"
  if stx[12].getNumArgs == 2 && blank fix then fail "empty fix"
  if title.contains '\n' then fail "the title is one line"
  let env ← getEnv
  if (defectExt.getState env).any (·.key == key) then fail "the entry is declared twice"
  match checkIds env [requirements] with
  | .error msg => fail msg
  | .ok ids => if ids.isEmpty then fail "the requirements name no spec ID"
  if (parseRuntimes runtimes).isNone then
    fail s!"unknown runtime in {repr runtimes}; name Java, TypeScript, Rust, Python or all"
  unless validStatus status do
    fail s!"the status {repr status} is not open, fixed, unreleased or fixed in <version>"
  let names ← match parseNames evidence with
    | .ok (_, ns) => pure ns
    | .error msg => fail s!"evidence: {msg}"
  let missing := unresolved env names
  unless missing.isEmpty do
    fail s!"no declaration is named {missing.toList}; import the module that declares it"
  modifyEnv (defectExt.addEntry · {
    key, id, num, title, requirements, runtimes, defect, evidence, fix, status,
    module := env.mainModule })

/-- The `unbuilt_requirement` command: one unbuilt entry of the runtime ledger.

```
unbuilt_requirement UB_01
  title "Immediate termination"
  requirements r#"ENV-015."#
  runtimes r#"Rust, TypeScript, Python."#
  missing r#"`terminateNow()`. Java has it on both executors."#
  status "open"
```

Every requirement it names must be a `Proposed` requirement text. -/
syntax (name := unbuiltCmd) "unbuilt_requirement " ident &"title" str &"requirements" str
  &"runtimes" str &"missing" str &"status" str : command

@[command_elab unbuiltCmd, inherit_doc unbuiltCmd]
def elabUnbuilt : CommandElab := fun stx => do
  let n := stx[1]
  let key := n.getId
  let str (s : Syntax) : String := (s.isStrLit?).getD ""
  let fail {α : Type} (msg : String) : CommandElabM α :=
    throwErrorAt n m!"unbuilt_requirement {key}: {msg}"
  let some (id, num) := keyId "UB" key | fail "the name must be UB_ and a number, e.g. UB_01"
  let title := str stx[3]
  let requirements := str stx[5]
  let runtimes := str stx[7]
  let missing := str stx[9]
  let status := str stx[11]
  for (k, v) in [("title", title), ("requirements", requirements), ("runtimes", runtimes),
      ("missing", missing)] do
    if blank v then fail s!"empty {k}"
  let env ← getEnv
  if (unbuiltExt.getState env).any (·.key == key) then fail "the entry is declared twice"
  match checkIds env [requirements] (proposed := true) with
  | .error msg => fail msg
  | .ok ids => if ids.isEmpty then fail "the requirements name no spec ID"
  if (parseRuntimes runtimes).isNone then
    fail s!"unknown runtime in {repr runtimes}; name Java, TypeScript, Rust, Python or all"
  unless validStatus status do
    fail s!"the status {repr status} is not open, fixed, unreleased or fixed in <version>"
  modifyEnv (unbuiltExt.addEntry · {
    key, id, num, title, requirements, runtimes, missing, status, module := env.mainModule })

/-- The `ledger_divergence` command: one row of the divergence table, in table order.

```
ledger_divergence "Place equality ([MOD-024])" spec "implementation's own"
  java "structural on name and token type" typescript "name only" rust "name only"
```

Every spec ID a cell names must be a requirement text. -/
syntax (name := divergenceCmd) "ledger_divergence " str &"spec" str &"java" str
  &"typescript" str &"rust" str : command

@[command_elab divergenceCmd, inherit_doc divergenceCmd]
def elabDivergence : CommandElab := fun stx => do
  let str (s : Syntax) : String := (s.isStrLit?).getD ""
  let cells := [str stx[1], str stx[3], str stx[5], str stx[7], str stx[9]]
  let fail {α : Type} (msg : String) : CommandElabM α :=
    throwErrorAt stx[1] m!"ledger_divergence {repr (str stx[1])}: {msg}"
  if cells.any blank then fail "an empty cell"
  if cells.any (fun c => c.contains '\n' || c.contains '|') then
    fail "a cell is one line without |"
  let env ← getEnv
  if (divergenceExt.getState env).any (·.aspect == str stx[1]) then
    fail "the row is declared twice"
  if let .error msg := checkIds env cells then fail msg
  modifyEnv (divergenceExt.addEntry · {
    aspect := str stx[1], spec := str stx[3], java := str stx[5], typescript := str stx[7],
    rust := str stx[9], module := env.mainModule })

end Libpetri.Spec.Ledger
