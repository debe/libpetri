import Lean
/-!
# The requirement registry

This module is tooling, not specification. It gives the spec modules five things:

* the `requirement` command, the one block every requirement is declared with. It defines the
  Lean statement (a predicate, never an axiom), writes a structured docstring (shown on hover),
  checks that the block is complete, hashes it (the sign-off names the hash) and records it in a
  persistent registry;
* `#spec_witness NAME`, which registers a definition (the reference firing relation) as a
  *witness model*: the model a `holds` theorem must check a requirement against;
* the `@[evidence role REQ…]` attribute, which links a theorem (a witness, a violation, a
  non-vacuity proof, a conflict …) to the requirements it is evidence for, and checks that the
  theorem's statement has the shape its role promises and assumes nothing;
* the citation form `@[evidence cites "VER-002" "fragment"]`, which links a theorem to the
  fragment of a spec ID it proves, whether or not the ID has a requirement block (the citations
  become `lean/report/proof-coverage.json`);
* `#write_requirements_report "dir"`, which renders the registry as `requirements.md` and
  `requirements.json`, and `#audit_axioms`, which fails on any axiom outside the standard three.

It imports only Lean core so that any module can use `@[evidence]`. It lives in its own module
because `initialize` declarations only run in importing modules.
-/
set_option linter.missingDocs true

open Lean Elab Command Meta

namespace Libpetri.Spec

/-- One requirement block, as written in a spec module. -/
structure Entry where
  /-- The Lean definition that states the requirement. -/
  decl : Name
  /-- Spec ID, e.g. `CORE-031`. Several blocks may share an ID (as written / proposed). -/
  id : String
  /-- Short title. -/
  title : String
  /-- Kind tag: B behaviour, F pure function, T timing, Q quality, A assumption, N config. -/
  kind : String
  /-- What the requirement applies to, e.g. `all executors`. -/
  scope : String
  /-- `verbatim` (quote is in `spec/*.md` under the ID's heading) or `proposed`. -/
  source : String
  /-- Where a proposed text comes from, or the spec file of a verbatim one. -/
  sourceRef : String
  /-- The natural-language text, one string per quoted sentence or bullet. -/
  quotes : Array String
  /-- Plain-language reading of the formula, one string per formula line. -/
  reading : Array String
  /-- Assumptions the formula relies on. -/
  assumes : Array String
  /-- Sign-off status: `pending`, or `<YYYY-MM-DD> <hash>` naming the statement hash. -/
  signoff : String
  /-- The statement hash (`statementHash`), 16 hex digits. -/
  hash : String
  /-- The module the block is declared in. -/
  module : Name
  deriving Inhabited

/-- One evidence link. For a requirement role, theorem `thm` is evidence of kind `role` for the
requirement block `req`. For the citation role `cites`, `req` is anonymous and the theorem is
linked to the spec ID `id` through the spec text `fragment`. -/
structure Evidence where
  /-- The requirement's Lean definition; anonymous for a citation. -/
  req : Name
  /-- What the theorem shows: `holds`, `violated`, `forbids`, `nonvacuous`, …, or `cites`. -/
  role : String
  /-- The theorem. -/
  thm : Name
  /-- The module the theorem is declared in. -/
  module : Name
  /-- The cited spec ID; empty unless `role = "cites"`. -/
  id : String := ""
  /-- The cited spec fragment; empty unless `role = "cites"`. -/
  fragment : String := ""
  deriving Inhabited

/-- Persistent store of all requirement blocks, imported modules included. -/
initialize reqExt : SimplePersistentEnvExtension Entry (Array Entry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun as => as.foldl (· ++ ·) #[]
  }

/-- Persistent store of all evidence links, citations included. -/
initialize evExt : SimplePersistentEnvExtension Evidence (Array Evidence) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun as => as.foldl (· ++ ·) #[]
  }

/-- Persistent store of the witness models registered with `#spec_witness`. -/
initialize witExt : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    addEntryFn := NameSet.insert
    addImportedFn := fun as => as.foldl (fun s a => a.foldl NameSet.insert s) {}
  }

/-- The evidence roles a theorem may carry for a requirement block. -/
def roles : List String :=
  ["holds", "violated", "allows", "forbids", "undecided", "mutant", "nonvacuous", "conflict",
   "ambiguity", "total", "consistent"]

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

/-! ## Witness models -/

/-- `#spec_witness NAME` registers the definition `NAME` (for example `RefFire`, the reference
firing relation) as a witness model. A `holds` theorem must apply its requirement to a witness
model, so that "the requirement holds" always means "holds of the reference semantics", never
"holds of some model the theorem picked". -/
syntax (name := specWitnessCmd) "#spec_witness " ident : command

@[command_elab specWitnessCmd, inherit_doc specWitnessCmd]
def elabSpecWitness : CommandElab := fun stx => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let env ← getEnv
  unless (env.find? n).any (· matches .defnInfo _) do
    throwError "#spec_witness: {n} is not a definition; a witness model is a definition (such as \
      a firing relation), not a theorem, axiom, opaque constant or constructor"
  if (reqExt.getState env).any (·.decl == n) then
    throwError "#spec_witness: {n} is a requirement block, not a model"
  modifyEnv (witExt.addEntry · n)

/-! ## Role-shape check -/

/-- The expected statement shape of a role, for the error message. -/
def shapeHint : String → String
  | "holds" => "`∀ {N : Type} [DecidableEq N] …, REQ W` with exactly one named requirement \
      REQ, its type arguments the theorem's own type variables and its model argument a \
      registered witness model W"
  | "forbids" | "violated" => "`¬ REQ x` with exactly one named requirement REQ"
  | "mutant" => "`M x ∧ ¬ REQ x` with exactly one named requirement REQ and a constant M ≠ REQ"
  | "nonvacuous" => "a statement other than `True` that mentions a registered witness model"
  | "conflict" => "`¬ ∃ x, R₁ x ∧ … ∧ Rₙ x` with exactly the named requirements as conjuncts"
  | "ambiguity" => "`A x ∧ ¬ B x` or `¬ A x ∧ B x` with A, B the two named requirements"
  | _ => "a statement other than `True`"

/-- Instance classes an evidence theorem may assume over its type variables. Every type has an
instance of each, so assuming one never narrows the claim (`Inhabited` is absent for that
reason). -/
def freeClasses : List Name := [``DecidableEq, ``BEq, ``Hashable, ``Repr, ``ToString, ``Ord]

/-- `freeClasses`, for an error message. -/
def classList : String := ", ".intercalate (freeClasses.map toString)

/-- The error every failed shape check raises. -/
def shapeError {α : Type} (role : String) (thm : Name) (type : Expr) (why : MessageData) :
    MetaM α :=
  throwError "@[evidence {role}] on {thm}: {why}; expected shape {shapeHint role}, got\
    {indentExpr type}"

/-- The head constant of `e`, if `e` is an application of a constant. -/
def headConst? (e : Expr) : Option Name := e.consumeMData.getAppFn.consumeMData.constName?

/-- The conjuncts of a right- or left-nested `∧`. -/
partial def conjuncts (e : Expr) : Array Expr :=
  match e.consumeMData.and? with
  | some (a, b) => conjuncts a ++ conjuncts b
  | none => #[e.consumeMData]

/-- The free variables that occur as a direct argument of an application of one of `names`
anywhere in `e`: the model parameters a statement passes straight to a requirement. -/
partial def reqArgFVars (names : Array Name) (e : Expr) : Array Expr :=
  go e #[]
where
  /-- Accumulate. -/
  go (e : Expr) (acc : Array Expr) : Array Expr :=
    let acc := match headConst? e with
      | some c =>
        if names.contains c then
          acc ++ (e.getAppArgs.map (·.consumeMData)).filter (·.isFVar)
        else acc
      | none => acc
    match e with
    | .app f a => go a (go f acc)
    | .lam _ t b _ | .forallE _ t b _ => go b (go t acc)
    | .letE _ t v b _ => go b (go v (go t acc))
    | .mdata _ b | .proj _ _ b => go b acc
    | _ => acc

/-- Split the arguments of an application of requirement `req` into its type arguments (binders
whose type is a sort) and its model arguments (the explicit and implicit non-type, non-instance
binders). `none` if the application does not have exactly the requirement's arity. -/
def splitArgs (req : Name) (app : Expr) : MetaM (Option (Array Expr × Array Expr)) := do
  let args := app.consumeMData.getAppArgs.map (·.consumeMData)
  let ci ← getConstInfo req
  forallTelescopeReducing ci.type fun xs _ => do
    if xs.size != args.size then return none
    let mut ts := #[]
    let mut ms := #[]
    for x in xs, a in args do
      let d ← x.fvarId!.getDecl
      if (← whnf d.type).isSort then ts := ts.push a
      else if d.binderInfo.isInstImplicit then pure ()
      else ms := ms.push a
    return some (ts, ms)

/-- Pretty-print `e` on one line, for an error message. -/
def ppS (e : Expr) : MetaM String := return (← ppExpr e).pretty 100000

/-- Is `e`, unfolded to weak head normal form, the proposition `True`? -/
def isTrueProp (e : Expr) : MetaM Bool := return (← whnf e).consumeMData.isConstOf ``True

/-- Check the binders `xs` a theorem's statement starts with. A binder whose type is a
proposition (a hypothesis) is always rejected, since evidence must assume nothing. Type
binders are accepted, and so are binders of a `freeClasses` instance over type binders. Any
other (data) binder is accepted when `dataOk = some ok` and the binder is in `ok`, or, when
`dataOk = none`, unless its type is closed and has no `Nonempty` instance (`(e : Empty)`). -/
def checkBinders (fail : MessageData → MetaM Unit) (xs : Array Expr)
    (dataOk : Option (Array Expr)) : MetaM Unit := do
  for x in xs do
    let ty := (← instantiateMVars (← x.fvarId!.getDecl).type).consumeMData
    if ← isProp ty then
      fail m!"the hypothesis ({← ppS x} : {← ppS ty}) is not allowed: evidence assumes \
        nothing"
    else if (← whnf ty).isSort then
      pure ()
    else if freeClasses.contains (ty.getAppFn.constName?.getD .anonymous) then
      unless ty.getAppArgs.all (fun a => xs.contains a.consumeMData) do
        fail m!"the instance binder ({← ppS x} : {← ppS ty}) is not over type variables of \
          the theorem"
    else
      match dataOk with
      | some ok =>
        unless ok.contains x do
          fail m!"the binder ({← ppS x} : {← ppS ty}) is not allowed: a theorem of this role \
            binds only type variables, instances of {classList} over them, and model \
            parameters passed directly to a named requirement"
      | none =>
        if !ty.hasFVar then
          let ne := mkApp (mkConst ``Nonempty [← getLevel ty]) ty
          if (← synthInstance? ne).isNone then
            fail m!"the binder ({← ppS x} : {← ppS ty}) ranges over a type with no Nonempty \
              instance, so the statement may hold vacuously"

/-- Check that `thm` is a theorem whose statement has the shape its role promises and that it
assumes nothing. The leading `∀` binders are stripped (without unfolding) and checked with
`checkBinders`; the rest is the body.

* `holds`: exactly one named requirement `REQ`; the body is `REQ args`. Every type argument is
  a distinct type variable of the theorem (not `Empty`, not `Nat`), and every model argument is
  a registered witness model (`#spec_witness`) or a variable the theorem binds, at least one
  being a witness. No data binders other than such variables.
* `forbids` / `violated`: exactly one named requirement; the body is `¬ REQ args`.
* `mutant`: exactly one named requirement; the body is `M args' ∧ ¬ REQ args` for a constant
  `M ≠ REQ` whose trailing arguments are the model arguments of `REQ`, and `M args'` does not
  unfold to `True`.
* `nonvacuous`: no data binders; the body is not `True` and mentions a witness model.
* `conflict`: the body is `¬ ∃ x, C₁ ∧ … ∧ Cₙ`, every `Cᵢ` an application of a named
  requirement with `x` as a direct argument, every named requirement among them.
* `ambiguity`: exactly two named requirements `A ≠ B`; the body is `A args ∧ ¬ B args'` or
  `¬ A args ∧ B args'` with equal model arguments.
* `total`, `consistent`, `allows`, `undecided`: the body is not `True`; data binders must range
  over a type that is not closed or has a `Nonempty` instance. -/
def checkShape (thm : Name) (role : String) (names : Array Name) : MetaM Unit := do
  let ci ← getConstInfo thm
  let fail {α : Type} (why : MessageData) : MetaM α := shapeError role thm ci.type why
  let failU (why : MessageData) : MetaM Unit := fail why
  let one : MetaM Name := do
    unless names.size == 1 do
      fail m!"{role} evidence names exactly one requirement, not {names.size}"
    return names[0]!
  let ws := witExt.getState (← getEnv)
  let regd := if ws.isEmpty then "none" else ", ".intercalate (ws.toList.map toString)
  let isWitness (e : Expr) : Bool := (headConst? e).any ws.contains
  let split (req : Name) (app : Expr) : MetaM (Array Expr × Array Expr) := do
    let some r ← splitArgs req app
      | fail m!"{req} is not applied to exactly its arguments in {← ppS app}"
    return r
  forallTelescope ci.type fun xs body => do
    let body := (← instantiateMVars body).consumeMData
    match role with
    | "holds" =>
      let req ← one
      checkBinders failU xs (some (reqArgFVars names body))
      unless headConst? body == some req do
        fail m!"the statement is not an application of {req}"
      let (ts, ms) ← split req body
      let mut seen : Array Expr := #[]
      for t in ts do
        unless t.isFVar && xs.contains t do
          fail m!"the type argument {← ppS t} of {req} is not a type variable of the \
            theorem; holds evidence must hold at every type, not at one"
        if seen.contains t then
          fail m!"the type variable {← ppS t} is passed to {req} twice; holds evidence must \
            hold at every choice of types, not at equal ones"
        seen := seen.push t
      for m in ms do
        unless isWitness m || (m.isFVar && xs.contains m) do
          fail m!"the model argument {← ppS m} of {req} is not a registered witness model \
            (registered: {regd}); register the model with #spec_witness"
      unless ms.isEmpty || ms.any isWitness do
        fail m!"no model argument of {req} is a registered witness model (registered: \
          {regd}); register the model with #spec_witness"
    | "forbids" | "violated" =>
      let req ← one
      checkBinders failU xs (some (reqArgFVars names body))
      let some inner := body.not? | fail "the statement is not a negation"
      unless headConst? inner == some req do
        fail m!"the negated statement is not an application of {req}"
      let _ ← split req inner
    | "mutant" =>
      let req ← one
      checkBinders failU xs (some (reqArgFVars names body))
      let some (mut_, neg) := body.and? | fail "the statement is not a conjunction"
      let some inner := neg.consumeMData.not? | fail "the second conjunct is not a negation"
      unless headConst? inner == some req do
        fail m!"the second conjunct is not the negation of an application of {req}"
      let (_, ms) ← split req inner
      let mut_ := mut_.consumeMData
      match headConst? mut_ with
      | none => fail "the first conjunct is not an application of a constant"
      | some m =>
        if m == req then fail m!"the mutant is {req} itself"
      let margs := mut_.getAppArgs.map (·.consumeMData)
      unless ms.size ≤ margs.size && margs.extract (margs.size - ms.size) margs.size == ms do
        fail m!"the mutant {← ppS mut_} is not applied to the model {req} is applied to"
      if ← isTrueProp mut_ then fail m!"the mutant {← ppS mut_} unfolds to True"
    | "nonvacuous" =>
      checkBinders failU xs (some #[])
      if ← isTrueProp body then fail "the statement is True"
      unless (body.find? fun e => isWitness e).isSome do
        fail m!"the statement mentions no registered witness model (registered: {regd})"
    | "conflict" =>
      checkBinders failU xs (some (reqArgFVars names body))
      let some inner := body.not? | fail "the statement is not a negation"
      let inner := inner.consumeMData
      unless inner.isAppOfArity ``Exists 2 do fail "the negated statement is not `∃ x, …`"
      withLocalDeclD `x inner.appFn!.appArg! fun x => do
        let cs := conjuncts (mkApp inner.appArg! x).headBeta
        for c in cs do
          unless (headConst? c).any names.contains do
            fail m!"the conjunct {← ppS c} is not an application of a named requirement"
          unless c.getAppArgs.any (·.consumeMData == x) do
            fail m!"the conjunct {← ppS c} is not applied to the bound variable"
        for r in names do
          unless cs.any (headConst? · == some r) do
            fail m!"no conjunct is an application of {r}"
    | "ambiguity" =>
      unless names.size == 2 do
        fail m!"ambiguity evidence names exactly two requirements, not {names.size}"
      checkBinders failU xs (some (reqArgFVars names body))
      let some (a, b) := body.and? | fail "the statement is not a conjunction"
      let (pos, neg) ← match a.consumeMData.not?, b.consumeMData.not? with
        | none, some nb => pure (a.consumeMData, nb.consumeMData)
        | some na, none => pure (b.consumeMData, na.consumeMData)
        | _, _ => fail "exactly one conjunct must be a negation"
      let (some p, some n) := (headConst? pos, headConst? neg)
        | fail "a conjunct is not an application of a constant"
      unless names.contains p && names.contains n && p != n do
        fail "the conjuncts are not applications of the two named requirements, one each"
      let (_, pm) ← split p pos
      let (_, nm) ← split n neg
      unless pm == nm do fail m!"{p} and {n} are not applied to the same model"
    | _ =>
      checkBinders failU xs none
      if ← isTrueProp body then fail "the statement is True"

/-! ## The `evidence` attribute -/

/-- Syntax: `@[evidence holds CORE_031]` or `@[evidence cites "VER-002" "fragment"]`. -/
syntax (name := evidenceAttr) "evidence " ident (ppSpace ident)* (ppSpace str)* : attr

initialize registerBuiltinAttribute {
  name := `evidenceAttr
  descr := "links a theorem to the requirements (or spec IDs) it is evidence for"
  add := fun thm stx kind => do
    let `(attr| evidence $role:ident $reqs:ident* $strs:str*) := stx
      | throwError "usage: @[evidence role REQ…] or @[evidence cites \"ID-000\" \"fragment\"]"
    let role := role.getId.toString
    unless kind == .global do
      throwError "@[evidence {role}] on {thm}: the attribute must be global, not local or scoped"
    unless (← getConstInfo thm).isTheorem do
      throwError "@[evidence {role}] on {thm}: {thm} is not a theorem; only a theorem can be \
        evidence"
    -- The report records the module that declares the theorem, and only sees Libpetri modules.
    if ((← getEnv).getModuleIdxFor? thm).isSome then
      throwError "@[evidence {role}] on {thm}: {thm} is declared in another module; tag it where \
        it is declared"
    let module := (← getEnv).mainModule
    unless (`Libpetri).isPrefixOf module do
      throwError "@[evidence {role}] on {thm}: {module} is not a Libpetri module; \
        spec-tools/Report.lean only reads the tags of lean/Libpetri.lean and lean/Libpetri/"
    if role == "cites" then
      unless reqs.isEmpty && strs.size == 2 do
        throwError "usage: @[evidence cites \"ID-000\" \"fragment\"] (exactly one ID and one fragment)"
      let id := strs[0]!.getString
      let fragment := strs[1]!.getString
      unless isSpecId id do
        throwError "cites: {repr id} is not a spec ID (expected ^[A-Z]+-\\d\{3}$, e.g. VER-002)"
      if blank fragment then throwError "cites {id}: the fragment is blank (no letter or digit)"
      modifyEnv (evExt.addEntry · { req := .anonymous, role, thm, module, id, fragment })
      return
    unless roles.contains role do
      throwError s!"unknown evidence role {role}; use one of {", ".intercalate roles} or cites"
    unless strs.isEmpty do
      throwError "@[evidence {role} …] takes requirement names, not strings"
    if reqs.isEmpty then throwError "@[evidence {role}] names no requirement"
    let mut names : Array Name := #[]
    for r in reqs do
      let req ← realizeGlobalConstNoOverload r
      unless (reqExt.getState (← getEnv)).any (·.decl == req) do
        throwError "{req} is not a requirement block"
      if names.contains req then throwError "@[evidence {role}] names {req} twice"
      names := names.push req
    let _ ← (checkShape thm role names).run'
    for req in names do
      modifyEnv (evExt.addEntry · { req, role, thm, module })
}

/-! ## The `requirement` command -/

/-- The kind tags: B behaviour, F pure function, T timing, Q quality (test-only),
A assumption, N configuration. -/
def kinds : List String := ["B", "F", "T", "Q", "A", "N"]

/-- `n` as 16 lower-case hex digits. -/
def hex16 (n : UInt64) : String :=
  let digits := Nat.toDigits 16 n.toNat
  String.ofList (List.replicate (16 - digits.length) '0' ++ digits)

/-- The statement hash of a block: a 64-bit hash, as 16 hex digits, of its Lean statement
printed with `pp.all` (so that it does not depend on open namespaces or notations), its quotes,
its reading and its assumptions. A sign-off names it, so any change to the block's meaning
invalidates the sign-off. -/
def statementHash (stmt : String) (quotes reading assumes : Array String) : String :=
  let part (tag : String) (xs : Array String) : String :=
    s!"{tag}\x1f{xs.size}\x1f" ++ "\x1e".intercalate xs.toList
  hex16 <| hash <| "\x1d".intercalate
    [s!"statement\x1f{stmt}", part "quotes" quotes, part "reading" reading,
     part "assumes" assumes]

/-- Does `s` have the shape `YYYY-MM-DD`? -/
def isDate (s : String) : Bool :=
  match s.splitOn "-" with
  | [y, m, d] => y.length == 4 && m.length == 2 && d.length == 2 &&
      (y ++ m ++ d).all Char.isDigit
  | _ => false

/-- Markdown docstring generated from a block, shown on hover. -/
def Entry.docstring (e : Entry) : String :=
  let quotes := e.quotes.foldl (fun acc q => acc ++ s!"> {q}\n>\n") ""
  let reading := (e.reading.toList.zipIdx.map fun (l, i) => s!"{i + 1}. {l}") |> "\n".intercalate
  let assumes := if e.assumes.isEmpty then "none" else
    "\n" ++ ("\n".intercalate (e.assumes.toList.map (s!"* {·}")))
  s!"**{e.id}: {e.title}**\n\n\
    Kind {e.kind} · Scope {e.scope} · Source {e.source} ({e.sourceRef}) · Sign-off {e.signoff}\n\n\
    **Quote:**\n\n{quotes}\n**Reading:**\n\n{reading}\n\n**Assumptions:** {assumes}\n"

/-- The `requirement` command: the one block every requirement is declared with.

```
requirement CORE_031
  id "CORE-031" title "…" kind B scope "all executors"
  source verbatim "spec/01-core-model.md"     -- or: source proposed "<where from>"
  quote "…" "…"                               -- one string per quoted sentence
  reading "…" "…"                             -- one string per formula line
  assumes "…"                                 -- zero or more
  signoff "pending"                           -- or: signoff "2026-11-06 <statement hash>"
  statement : FireRel N → Prop := …
```

It validates the block (an empty id, title, scope, quote, reading line, assumption or sign-off,
an unknown kind or source is a build error), defines `NAME` with a generated docstring, computes
the statement hash (`statementHash`) and registers the block. A sign-off other than `pending`
must be a date and the current statement hash; a sign-off naming another hash is a build error,
so a block cannot change meaning under an old sign-off. All keywords after the first are
non-reserved (`&"…"`), so `id`, `title`, … stay usable as ordinary identifiers. -/
elab (name := requirementCmd) "requirement " n:ident
    &"id" id:str &"title" title:str &"kind" kind:ident &"scope" scope:str
    &"source" source:ident ref:str &"quote" qs:str+ &"reading" rs:str+
    (&"assumes")? as:str* &"signoff" so:str &"statement" " : " ty:term " := " val:term : command => do
  let decl := (← getCurrNamespace) ++ n.getId
  let e : Entry := {
    decl, id := id.getString, title := title.getString, kind := kind.getId.toString,
    scope := scope.getString, source := source.getId.toString, sourceRef := ref.getString,
    quotes := qs.map (·.getString), reading := rs.map (·.getString),
    assumes := as.map (·.getString), signoff := so.getString, hash := "",
    module := (← getEnv).mainModule }
  let fail (msg : String) : CommandElabM Unit := throwErrorAt n m!"requirement {decl}: {msg}"
  if blank e.id then fail "empty id"
  unless isSpecId e.id do fail s!"id {e.id} is not a spec ID (expected e.g. CORE-031)"
  if blank e.title then fail "empty title"
  unless kinds.contains e.kind do fail s!"kind must be one of {kinds}, not {e.kind}"
  if blank e.scope then fail "empty scope"
  unless e.source == "verbatim" || e.source == "proposed" do
    fail s!"source must be verbatim or proposed, not {e.source}"
  if blank e.sourceRef then fail "say where the text comes from"
  if e.quotes.any blank then fail "a quote is empty"
  if e.reading.any blank then fail "a reading line is empty"
  if e.assumes.any blank then fail "an assumption is empty"
  if blank e.signoff then fail "empty signoff"
  let docStx : TSyntax ``Parser.Command.docComment :=
    ⟨mkNode ``Parser.Command.docComment #[mkAtom "/--", mkAtom (e.docstring ++ " -/")]⟩
  elabCommand (← `($docStx:docComment def $n : $ty := $val))
  let some ci := (← getEnv).find? decl | fail "the statement did not elaborate"; return
  let stmt ← liftTermElabM <| withOptions (fun o => o.setBool `pp.all true) do
    return s!"{← ppExpr ci.type} := {← ppExpr (ci.value?.getD ci.type)}"
  let h := statementHash stmt e.quotes e.reading e.assumes
  unless e.signoff == "pending" do
    match e.signoff.splitOn " " with
    | [date, given] =>
      unless isDate date do
        fail s!"signoff must be \"pending\" or \"<YYYY-MM-DD> <statement hash>\", not \
          {repr e.signoff}; the statement hash is {h}"
      unless given == h do
        fail s!"signoff hash {given} does not match the statement hash {h}; the block changed \
          after sign-off: re-read it and sign off again with \"<YYYY-MM-DD> {h}\""
    | _ =>
      fail s!"signoff must be \"pending\" or \"<YYYY-MM-DD> <statement hash>\", not \
        {repr e.signoff}; the statement hash is {h}"
  modifyEnv (reqExt.addEntry · { e with hash := h })

/-! ## Report -/

/-- Escape text for an HTML context inside Markdown: only `&` and `<` need it, so arrows,
comparisons and quotes stay readable in the raw Markdown. -/
def html (s : String) : String :=
  s.replace "&" "&amp;" |>.replace "<" "&lt;"

/-- Escape a Markdown table cell (the cell may hold `<br>`). -/
def mdCell (s : String) : String := (html s).replace "|" "\\|" |>.replace "\n" "<br>"

/-- Pretty-print a constant: a definition shows its body, a theorem its statement. Proofs and
deep terms are printed in full (`pp.proofs`, `pp.deepTerms`, a raised `pp.maxSteps`), and
`fun x ↦ …` uses the Unicode arrow. -/
def statementOf (n : Name) : CommandElabM String := do
  let some ci := (← getEnv).find? n | return "?"
  let e := if ci.isTheorem then ci.type else ci.value?.getD ci.type
  liftTermElabM <| withOptions (fun o => o.setBool `pp.proofs true |>.setBool `pp.deepTerms true
      |>.set `pp.maxSteps (1000000 : Nat) |>.setBool `pp.unicode.fun true) do
    let f ← ppExpr e
    return f.pretty 90

/-- First paragraph of a docstring, on one line. -/
def docOf (n : Name) : CommandElabM String := do
  let d := (← findDocString? (← getEnv) n).getD ""
  return (((d.splitOn "\n\n").headD "").trimAscii.toString).replace "\n" " "

/-- The whole docstring, trimmed, its line breaks kept; empty when there is none. -/
def fullDocOf (n : Name) : CommandElabM String := do
  return ((← findDocString? (← getEnv) n).getD "").trimAscii.toString

/-- Display order of evidence roles. -/
def roleRank (r : String) : Nat := roles.idxOf r

/-- Symbol shown in front of an evidence line. -/
def roleMark : String → String
  | "holds" | "allows" | "consistent" | "total" | "nonvacuous" => "✓"
  | "violated" | "forbids" | "conflict" | "mutant" => "✗"
  | _ => "?"

/-- One rendered evidence line. -/
structure EvRow where
  /-- The role. -/
  role : String
  /-- The theorem. -/
  thm : Name
  /-- The theorem's module. -/
  module : Name
  /-- First paragraph of the theorem's docstring. -/
  doc : String
  /-- The theorem's whole docstring (`fullDocOf`), for the JSON report. -/
  fullDoc : String
  /-- The theorem's pretty-printed statement. -/
  stmt : String

/-- Everything the report needs about one block, rendered once. -/
structure Row where
  /-- The block. -/
  e : Entry
  /-- Its pretty-printed statement. -/
  stmt : String
  /-- Its evidence. -/
  ev : Array EvRow

/-- Collect the rows, sorted by ID, then source (verbatim first), then declaration name. -/
def rows : CommandElabM (Array Row) := do
  let env ← getEnv
  let entries := (reqExt.getState env).qsort fun a b =>
    a.id < b.id || (a.id == b.id && (a.source > b.source ||
      (a.source == b.source && a.decl.toString < b.decl.toString)))
  let evs := evExt.getState env
  entries.mapM fun e => do
    let mine := (evs.filter (·.req == e.decl)).qsort fun a b =>
      roleRank a.role < roleRank b.role ||
        (a.role == b.role && a.thm.toString < b.thm.toString)
    let ev ← mine.mapM fun v => return {
      role := v.role, thm := v.thm, module := v.module,
      doc := ← docOf v.thm, fullDoc := ← fullDocOf v.thm, stmt := ← statementOf v.thm : EvRow }
    return { e, stmt := ← statementOf e.decl, ev }

/-- The citations, sorted by ID, then theorem, then fragment. -/
def citations : CommandElabM (Array Evidence) := do
  let cs := (evExt.getState (← getEnv)).filter (·.role == "cites")
  return cs.qsort fun a b =>
    a.id < b.id || (a.id == b.id && (a.thm.toString < b.thm.toString ||
      (a.thm == b.thm && a.fragment < b.fragment)))

/-- Anchor of a block in the Markdown report. -/
def anchor (e : Entry) : String := e.decl.toString.replace "." "-"

/-- How to read the report, printed at the top of `requirements.md`. -/
def legend : String :=
  "## How to read this report\n\n\
  Each requirement block shows the spec text (quoted verbatim from `spec/*.md`, or proposed), \
  a plain reading of the formula line by line, and the Lean statement. A requirement is a \
  predicate, never an axiom: it is checked against a firing semantics, not assumed.\n\n\
  **Names in the Lean statements**\n\n\
  | Name | Meaning |\n|---|---|\n\
  | `N` | the type of place names; a statement holds for every `N` |\n\
  | `F` | the firing semantics under test (`F : FireRel N`); `F t m d m'` says that transition `t` fires from marking `m`, deposits `d` and leaves marking `m'` |\n\
  | `RefFire` | the reference firing semantics (`Reference.Fires`), the registered witness model |\n\
  | `Trans N`, `Reference.Trans N` | transitions over places named by `N` |\n\
  | `m`, `m'` | markings: token counts by place (`N → Nat`) |\n\
  | `t`, `p` | a transition, a place |\n\
  | `fun x ↦ e` | the function that maps `x` to `e` |\n\n\
  **EARS keywords** (Easy Approach to Requirements Syntax; defined in `Libpetri/Spec/Ears.lean`)\n\n\
  | Notation | Reads as |\n|---|---|\n\
  | `while P, never R` | no `R` step starts in a state where `P` holds |\n\
  | `on R, shall Q` | every `R` step from `s` to `s'` satisfies `Q s s'` |\n\
  | `when T, shall R` | in a trace, every `T` is followed (at it or later) by an `R` |\n\
  | `after T, never B` | in a trace, once a `T` has happened no later event is a `B` |\n\
  | `until G, never B` | in a trace, no `B` happens before the first `G` |\n\
  | `at-most-once P` | in a trace, at most one event is a `P` |\n\
  | `occurs P` | in a trace, some event is a `P` |\n\n\
  **Evidence roles** (each is a theorem; its shape is checked when it is tagged)\n\n\
  | Role | The theorem shows |\n|---|---|\n\
  | ✓ holds | the requirement holds of the witness model (`RefFire`), at every type `N` |\n\
  | ✓ nonvacuous | the requirement's premises can be met: the witness model has a case it applies to |\n\
  | ✓ allows | the requirement permits a behaviour |\n\
  | ✓ total | some outcome exists in every case the requirement covers |\n\
  | ✓ consistent | the named requirements can all hold together |\n\
  | ✗ forbids | a concrete firing semantics breaks the requirement (`¬ REQ x`) |\n\
  | ✗ violated | the requirement is broken by the model named in the theorem |\n\
  | ✗ mutant | a plausible wrong reading `M` is told apart from the requirement: `M x ∧ ¬ REQ x` |\n\
  | ✗ conflict | the named requirements cannot all hold together: `¬ ∃ x, R₁ x ∧ … ∧ Rₙ x` |\n\
  | ? ambiguity | two readings of the text disagree on one model: `A x ∧ ¬ B x` |\n\
  | ? undecided | an open question the spec does not settle |\n\n\
  **Kind**: B behaviour, F pure function, T timing, Q quality (tested, not proven), \
  A assumption, N configuration. **Source**: `verbatim` (the quote is in `spec/*.md` under the \
  ID's heading) or `proposed` (new text, not yet in the spec). **Sign-off**: `pending`, or the \
  date and statement hash a reviewer signed; the build fails when the hash no longer matches \
  the block.\n\n"

/-- The Markdown report. -/
def renderMd (rs : Array Row) (cs : Array Evidence) : String := Id.run do
  let mut out := "# libpetri requirements: natural language next to Lean\n\n\
    Generated by `#write_requirements_report` from the `requirement` blocks and `@[evidence]` \
    attributes under `lean/Libpetri/`. Do not edit; CI regenerates it and fails on a \
    difference.\n\n" ++ legend ++
    "## Requirements\n\n\
    | ID | Title | Kind | Scope | Source | Evidence | Sign-off |\n|---|---|---|---|---|---|---|\n"
  for r in rs do
    let ev := ", ".intercalate <| roles.filterMap fun role =>
      match (r.ev.filter (·.role == role)).size with
      | 0 => none
      | 1 => some s!"{roleMark role} {role}"
      | n => some s!"{roleMark role} {role} ×{n}"
    out := out ++ s!"| [{r.e.id}](#{anchor r.e}) | {mdCell r.e.title} | {r.e.kind} | \
      {mdCell r.e.scope} | {r.e.source} | {ev} | {mdCell r.e.signoff} |\n"
  for r in rs do
    out := out ++ s!"\n---\n\n<a id=\"{anchor r.e}\"></a>\n## {r.e.id}: {r.e.title}\n\n\
      `{r.e.decl}` · Kind **{r.e.kind}** · Scope {r.e.scope} · Source **{r.e.source}** \
      ({r.e.sourceRef}) · Sign-off **{r.e.signoff}** · Statement hash `{r.e.hash}`\n\n\
      | Natural language | Plain reading | Lean statement |\n|---|---|---|\n"
    let q := "<br><br>".intercalate (r.e.quotes.toList.map mdCell)
    let rd := "<br>".intercalate (r.e.reading.toList.zipIdx.map fun (l, i) => s!"{i + 1}. {mdCell l}")
    out := out ++ s!"| {q} | {rd} | <pre>{mdCell r.stmt}</pre> |\n\n"
    unless r.e.assumes.isEmpty do
      out := out ++ "**Assumptions**\n\n" ++
        String.join (r.e.assumes.toList.map (s!"- {·}\n")) ++ "\n"
    out := out ++ "**Evidence**\n\n"
    if r.ev.isEmpty then out := out ++ "- none\n"
    for v in r.ev do
      out := out ++ s!"- {roleMark v.role} **{v.role}** `{v.thm}` ({v.module}): {v.doc}\n  \
        <pre>{mdCell v.stmt}</pre>\n"
  unless cs.isEmpty do
    out := out ++ "\n---\n\n## Citations\n\nTheorems linked to the fragment of a spec ID they \
      prove (`@[evidence cites \"ID\" \"fragment\"]`), whether or not the ID has a requirement \
      block.\n\n\
      | ID | Fragment | Theorem | Module |\n|---|---|---|---|\n"
    for c in cs do
      out := out ++ s!"| {c.id} | {mdCell c.fragment} | `{c.thm}` | {c.module} |\n"
  return out

/-- The `("doc", d)` field of an evidence or citation entry, left out when `d` is empty. -/
def docField (d : String) : List (String × Json) :=
  if d.isEmpty then [] else [("doc", Json.str d)]

/-- Machine-readable form, read by the CI gates and the spec site:
`{"title", "requirements": [block with "hash" and "evidence"], "citations": [...]}`. Every
evidence entry and citation carries its theorem's whole docstring as `"doc"` (`fullDocOf`),
left out when the theorem has none; `cs` pairs each citation with that docstring. -/
def renderJson (rs : Array Row) (cs : Array (Evidence × String)) : Json :=
  Json.mkObj [
    ("title", "libpetri requirements"),
    ("requirements", Json.arr <| rs.map fun r => Json.mkObj [
      ("decl", r.e.decl.toString), ("module", r.e.module.toString), ("id", r.e.id),
      ("title", r.e.title), ("kind", r.e.kind), ("scope", r.e.scope), ("source", r.e.source),
      ("sourceRef", r.e.sourceRef), ("quotes", toJson r.e.quotes),
      ("reading", toJson r.e.reading), ("assumes", toJson r.e.assumes),
      ("signoff", r.e.signoff), ("hash", r.e.hash), ("statement", r.stmt),
      ("evidence", Json.arr <| r.ev.map fun v =>
        Json.mkObj ([("role", Json.str v.role), ("theorem", Json.str v.thm.toString),
          ("module", Json.str v.module.toString)] ++ docField v.fullDoc))]),
    ("citations", Json.arr <| cs.map fun (c, d) => Json.mkObj ([
      ("role", Json.str "cites"), ("id", Json.str c.id), ("fragment", Json.str c.fragment),
      ("theorem", Json.str c.thm.toString), ("module", Json.str c.module.toString)] ++
      docField d))]

/-- `#write_requirements_report "dir"` writes `requirements.md` and `requirements.json` into
`dir`. -/
elab "#write_requirements_report " dir:str : command => do
  let rs ← rows
  let cs ← citations
  let dir : System.FilePath := dir.getString
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "requirements.md") (renderMd rs cs)
  let cds ← cs.mapM fun c => return (c, ← fullDocOf c.thm)
  IO.FS.writeFile (dir / "requirements.json") ((renderJson rs cds).pretty ++ "\n")
  logInfo m!"wrote {rs.size} requirement blocks and {cs.size} citations to {dir}"

/-! ## Axiom audit run by CI -/

/-- Is `n` declared in a module under `pre` (e.g. `Libpetri` or `Libpetri.Spec`)? A constant of
the current file counts when the file's own module name is under `pre`. -/
def declaredUnder (env : Environment) (pre : Name) (n : Name) : Bool :=
  let mod := match env.getModuleIdxFor? n with
    | some i => env.header.moduleNames[i.toNat]!
    | none => env.mainModule
  pre.isPrefixOf mod

/-- `#audit_axioms` enumerates every constant declared in a module under `Libpetri` (private
ones included; `#audit_axioms Libpetri.Spec` restricts to a module prefix) and fails if any is
an axiom or depends on an axiom outside `propext`, `Quot.sound`, `Classical.choice`. -/
syntax (name := auditAxiomsCmd) "#audit_axioms" (ppSpace ident)? : command

@[command_elab auditAxiomsCmd, inherit_doc auditAxiomsCmd]
def elabAuditAxioms : CommandElab := fun stx => do
  let pre : Name := match stx[1].getOptional? with
    | some p => p.getId
    | none => `Libpetri
  unless (`Libpetri).isPrefixOf pre do
    throwError "#audit_axioms: the prefix {pre} is not under Libpetri"
  let env ← getEnv
  let allowed := [``propext, ``Quot.sound, ``Classical.choice]
  let mut thms : Nat := 0
  let mut checked : Nat := 0
  let mut bad : Array MessageData := #[]
  for (n, ci) in env.constants.toList do
    unless declaredUnder env pre n do continue
    if ci matches .axiomInfo _ then bad := bad.push m!"{n} is an axiom"
    if ci.isTheorem then thms := thms + 1
    checked := checked + 1
    let axs ← liftCoreM (collectAxioms n)
    for a in axs do
      unless allowed.contains a do bad := bad.push m!"{n} depends on {a}"
  if checked == 0 then
    throwError "#audit_axioms: no constants declared under {pre}; is it imported?"
  if bad.isEmpty then
    logInfo m!"axioms ok: {checked} constants ({thms} theorems) in {pre}.*, \
      only propext / Quot.sound / Classical.choice"
  else
    throwError m!"axiom audit failed:\n{MessageData.joinSep bad.toList "\n"}"

end Libpetri.Spec
