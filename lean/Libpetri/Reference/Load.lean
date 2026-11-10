import Lean.Data.Json
import Libpetri.Reference.Decide

/-!
# Reading a corpus net (`spec/verification-fixtures/conformance/README.md`)

Not verified: this is the front end that turns a net file into `Net String`, a canonical initial
marking and the properties. It refuses, rather than guesses:

* **invalid** nets, as the builders would reject them: two input arcs on one place ([CORE-030]),
  `exactly` / `atLeast` with `n < 1` ([IO-002], [IO-004]), an input arc and a read arc on one
  place ([EXEC-012], ruling D15, with the builders' message after `invalid: `, checked after the
  input-arc checks and before the timing and output-spec checks), an `and` without children or a `xor`
  with fewer than two ([IO-011], [IO-012]), a timeout with `afterMs ≤ 0` ([IO-013]), two
  transitions with one name, and the build-time output-spec checks, in the builders' order with
  the first failure reported ([IO-011]–[IO-014]): a branch naming a place twice ([IO-011]), more
  than one `timeout` node, nested or not ([IO-013] AC7), an `xor` inside the child of the
  `timeout` ([IO-013] AC8), a `forward` outside the child of a `timeout` ([IO-014] AC7), a
  `forward` whose `from` is not an input place ([IO-014] AC3), and two output branches claiming
  one set of places ([IO-012] AC5). All six carry the builders' messages, after `invalid: `;
* invalid **timing** ([TIME-001]–[TIME-006]): an unknown `kind`, a missing or extra bound, a
  `deadline` of 0 ([TIME-003]), a `window` with `earliestMs > latestMs` ([TIME-005]), or a
  `deadline` or `window` latest bound or an earliest bound above the maximum duration
  ([TIME-001] AC4);
* nets **outside v1**: any key the schema does not define (environment places, terminals,
  ν / match specs, …).

Timing is read only for reapability ([TIME-013]): `deadline` and `window` are reapable,
`immediate`, `unconstrained`, `delayed` and `exact` are not.

A refused net gets `unknown` for every property, with the reason.
-/

namespace Libpetri.Reference.Load

open Lean Libpetri Libpetri.Novel.Seam Libpetri.Reference

abbrev Err := Except String

def fail {α : Type} (msg : String) : Err α := .error msg

def field (j : Json) (k : String) : Err Json :=
  match j.getObjVal? k with
  | .ok v => .ok v
  | .error _ => fail s!"invalid: missing '{k}'"

def optField (j : Json) (k : String) : Option Json :=
  match j.getObjVal? k with
  | .ok Json.null => none
  | .ok v => some v
  | .error _ => none

def str (j : Json) (what : String) : Err String :=
  match j.getStr? with
  | .ok s => .ok s
  | .error _ => fail s!"invalid: {what} must be a string"

def nat (j : Json) (what : String) : Err Nat :=
  match j.getNat? with
  | .ok n => .ok n
  | .error _ => fail s!"invalid: {what} must be a non-negative integer"

def arr (j : Json) (what : String) : Err (List Json) :=
  match j.getArr? with
  | .ok a => .ok a.toList
  | .error _ => fail s!"invalid: {what} must be an array"

def strs (j : Json) (what : String) : Err (List String) := do
  (← arr j what).mapM (str · what)

/-- Refuse keys the schema does not define. -/
def onlyKeys (j : Json) (allowed : List String) (where_ : String) : Err Unit := do
  let o ← match j.getObj? with
    | .ok o => pure o
    | .error _ => fail s!"invalid: {where_} must be an object"
  for (k, _) in o.toList do
    unless allowed.contains k do
      fail s!"out-of-scope: key '{k}' in {where_}"

/-- Right-nested binary node over `n ≥ 1` children. -/
def nest (mk : Out String → Out String → Out String) : List (Out String) → Err (Out String)
  | [] => fail "invalid: empty and/xor"
  | [x] => pure x
  | x :: xs => do pure (mk x (← nest mk xs))

partial def parseOut (j : Json) : Err (Out String) := do
  let ty ← str (← field j "type") "output type"
  match ty with
  | "place" =>
    onlyKeys j ["type", "place"] "output"
    return .place (← str (← field j "place") "output place")
  | "and" =>
    onlyKeys j ["type", "children"] "output"
    let cs ← (← arr (← field j "children") "and children").mapM parseOut
    if cs.isEmpty then fail "invalid: and needs at least one child (IO-011)"
    nest .and cs
  | "xor" =>
    onlyKeys j ["type", "children"] "output"
    let cs ← (← arr (← field j "children") "xor children").mapM parseOut
    if cs.length < 2 then fail "invalid: xor needs at least two children (IO-012)"
    nest .xor cs
  | "timeout" =>
    onlyKeys j ["type", "afterMs", "child"] "output"
    let ms ← nat (← field j "afterMs") "afterMs"
    if ms == 0 then fail "invalid: timeout afterMs must be positive (IO-013)"
    return .timeout (← parseOut (← field j "child"))
  | "forward" =>
    onlyKeys j ["type", "from", "to"] "output"
    return .forward (← str (← field j "from") "forward from") (← str (← field j "to") "forward to")
  | other => fail s!"out-of-scope: output type '{other}'"

def timeoutCount : Out String → Nat
  | .timeout c => 1 + timeoutCount c
  | .and l r => timeoutCount l + timeoutCount r
  | .xor l r => timeoutCount l + timeoutCount r
  | _ => 0

/-- [IO-011]'s walk, on the output spec as written (n-ary `and` / `xor`), as the builders run it
(spec/02-input-output-specs.md, IO-011 "Which place the message names"): `.inl p` reports `p`,
`.inr ps` names the places `ps`, each once, in the order the walk met them. Run on JSON that
`parseOut` accepted, so every key it reads is there. `Spec.firstDup` is the same walk over the
right-nested binary `Out`. -/
partial def dupWalk (j : Json) : String ⊕ List String :=
  let get (k : String) : Json := (j.getObjVal? k).toOption.getD Json.null
  let s (k : String) : String := ((get k).getStr?).toOption.getD ""
  let kids : List Json := (((get "children").getArr?).toOption.map (·.toList)).getD []
  match s "type" with
  | "place" => .inr [s "place"]
  | "forward" => .inr [s "to"]
  | "timeout" => dupWalk (get "child")
  | "xor" => kids.foldl (init := .inr []) fun acc c =>
      match acc with
      | .inl p => .inl p
      | .inr ps =>
        match dupWalk c with
        | .inl p => .inl p
        | .inr cs => .inr (ps ++ cs.filter (fun q => !ps.contains q))
  | "and" => kids.foldl (init := .inr []) fun acc c =>
      match acc with
      | .inl p => .inl p
      | .inr own =>
        match dupWalk c with
        | .inl p => .inl p
        | .inr cs =>
          match cs.find? own.contains with
          | some p => .inl p
          | none => .inr (own ++ cs)
  | _ => .inr []

/-- Whether an `Xor` node lies anywhere in `o`. -/
def hasXor : Out String → Bool
  | .xor _ _ => true
  | .and l r => hasXor l || hasXor r
  | .timeout c => hasXor c
  | _ => false

/-- Whether the child of a `timeout` holds an `xor` node at any depth ([IO-013] AC8). -/
def xorInTimeout : Out String → Bool
  | .timeout c => hasXor c
  | .and l r => xorInTimeout l || xorInTimeout r
  | .xor l r => xorInTimeout l || xorInTimeout r
  | _ => false

def forwardSources : Out String → List String
  | .forward s _ => [s]
  | .and l r => forwardSources l ++ forwardSources r
  | .xor l r => forwardSources l ++ forwardSources r
  | .timeout c => forwardSources c
  | .place _ => []

/-- The first `forward` outside the child of a `timeout`, in pre-order ([IO-014] AC7). A
`timeout`'s subtree is not searched: every forward there is allowed. -/
def bareForward : Out String → Option (String × String)
  | .forward s d => some (s, d)
  | .and l r => (bareForward l).or (bareForward r)
  | .xor l r => (bareForward l).or (bareForward r)
  | .timeout _ => none
  | .place _ => none

/-- The first pair `(i, j)`, `i < j`, of output branches that claim one set of places
([IO-012] AC5): the smallest `j` whose set equals an earlier branch's, and the smallest such `i`.
Branches are `Out.branches`, numbered as [IO-016] / [VER-001] number them (right-nested binary
nodes enumerate as the n-ary ones). Run after the [IO-011] check, so no branch repeats a place
and two branches claim one set iff they have one length and one holds the other. -/
def ambiguousPair (bs : List (List String)) : Option (Nat × Nat) :=
  let same (x y : List String) : Bool := x.length == y.length && x.all (y.contains ·)
  let idx := bs.zipIdx
  idx.findSome? fun (bj, j) =>
    (idx.take j).findSome? fun (bi, i) => if same bi bj then some (i, j) else none

def parseInput (j : Json) : Err (NInSpec String) := do
  onlyKeys j ["place", "kind", "n"] "input"
  let p ← str (← field j "place") "input place"
  let kind ← str (← field j "kind") "input kind"
  let card ← match kind with
    | "one" => pure Card.one
    | "all" => pure Card.all
    | "exactly" => do
      let n ← nat (← field j "n") "exactly n"
      if n < 1 then fail "invalid: exactly(n) needs n ≥ 1 (IO-002)"
      pure (Card.exactly n)
    | "atLeast" => do
      let n ← nat (← field j "n") "atLeast n"
      if n < 1 then fail "invalid: atLeast(n) needs n ≥ 1 (IO-004)"
      pure (Card.atLeast n)
    | other => fail s!"invalid: input kind '{other}'"
  return { place := p, card := card }

/-- The maximum duration in milliseconds ([TIME-001]): `MAX_DURATION_MS`, the value of
`Novel.TimedScg.maxDurationMs`, written out here so the reference executable does not import the
timed state-class graph. -/
def maxDurationMs : Nat := 3153600000000

/-- `invalid` unless the bound `v` named `what` is at most the maximum duration ([TIME-001]
AC4). -/
def atMostMax (name kind what : String) (v : Nat) : Err Unit :=
  if v > maxDurationMs then
    fail s!"invalid: {kind} timing of '{name}' has {what} above the maximum duration (TIME-001)"
  else pure ()

/-- A transition's timing ([TIME-001]–[TIME-006]), read to its reapability ([TIME-013]):
`{"kind": k, "earliestMs": e, "latestMs": l}` with the bounds `k` takes —
`immediate` / `unconstrained` none, `deadline` `latestMs`, `delayed` `earliestMs`,
`window` both (`e ≤ l ≤ MAX_DURATION_MS`), `exact` `earliestMs` (and `latestMs` equal to it, if given). The v0
forms `"immediate"` and `{"type": "immediate"}` are still accepted. -/
def parseTiming (name : String) (j : Json) : Err Bool := do
  if j == Json.str "immediate" then return false
  if let .ok (Json.str "immediate") := j.getObjVal? "type" then
    onlyKeys j ["type"] "timing"
    return false
  let kind ← str (← field j "kind") "timing kind"
  let e? ← match optField j "earliestMs" with
    | some v => some <$> nat v "earliestMs"
    | none => pure none
  let l? ← match optField j "latestMs" with
    | some v => some <$> nat v "latestMs"
    | none => pure none
  let need (b : Option Nat) (k : String) : Err Nat :=
    match b with
    | some v => pure v
    | none => fail s!"invalid: {kind} timing of '{name}' needs '{k}'"
  match kind with
  | "immediate" | "unconstrained" =>
    onlyKeys j ["kind"] "timing"
    return false
  | "deadline" =>
    onlyKeys j ["kind", "latestMs"] "timing"
    let l ← need l? "latestMs"
    if l == 0 then fail s!"invalid: deadline of '{name}' must be positive (TIME-003)"
    atMostMax name kind "latestMs" l
    return true
  | "delayed" =>
    onlyKeys j ["kind", "earliestMs"] "timing"
    let e ← need e? "earliestMs"
    atMostMax name kind "earliestMs" e
    return false
  | "window" =>
    onlyKeys j ["kind", "earliestMs", "latestMs"] "timing"
    let e ← need e? "earliestMs"
    let l ← need l? "latestMs"
    atMostMax name kind "earliestMs" e
    if l < e then fail s!"invalid: window of '{name}' has earliestMs > latestMs (TIME-005)"
    atMostMax name kind "latestMs" l
    return true
  | "exact" =>
    onlyKeys j ["kind", "earliestMs", "latestMs"] "timing"
    let e ← need e? "earliestMs"
    if let some l := l? then
      if l != e then fail s!"invalid: exact timing of '{name}' needs latestMs = earliestMs"
    atMostMax name kind "earliestMs" e
    return false
  | other => fail s!"invalid: timing kind '{other}' of '{name}'"

def parseTrans (j : Json) : Err (Trans String) := do
  onlyKeys j ["name", "inputs", "inhibitors", "reads", "resets", "output", "priority", "timing"]
    "transition"
  let name ← str (← field j "name") "transition name"
  let inputs ← match optField j "inputs" with
    | some a => do (← arr a "inputs").mapM parseInput
    | none => pure []
  let list (k : String) : Err (List String) :=
    match optField j k with
    | some a => strs a k
    | none => pure []
  let inh ← list "inhibitors"
  let rds ← list "reads"
  let rst ← list "resets"
  let out ← match optField j "output" with
    | some o => some <$> parseOut o
    | none => pure none
  if let some p := optField j "priority" then
    unless (p.getInt?.toOption.isSome) do fail "invalid: priority must be an integer"
  let places := inputs.map NInSpec.place
  if !places.Nodup then
    fail s!"invalid: '{name}' declares two input arcs on one place (CORE-030)"
  -- EXEC-012 (ruling D15): after the input-arc checks, before the timing and output-spec checks;
  -- the first read arc, in declaration order, whose place is an input place is named.
  if let some p := rds.find? (fun r => places.contains r) then
    fail s!"invalid: Transition '{name}' declares an input arc and a read arc on place '{p}'. \
      A read of a place the same firing consumes from has no coherent semantics and is rejected \
      (EXEC-012). Remove the read arc: the input arc already hands the consumed tokens to the \
      action."
  let reapable ← match optField j "timing" with
    | some tm => parseTiming name tm
    | none => pure false
  -- The build-time output-spec checks, in the builders' order; the first failure wins.
  if let some o := out then
    if let some oj := optField j "output" then
      if let .inl p := dupWalk oj then
        fail s!"invalid: output spec of transition '{name}' names place '{p}' twice in one AND \
          branch; outputs are sets (IO-015) — a weighted output is not supported, add a second \
          place or a follow-up transition"
    let n := timeoutCount o
    if n > 1 then
      fail s!"invalid: output spec of transition '{name}' has {n} Timeout nodes; an output spec \
        has at most one, nested or not (IO-013)"
    if xorInTimeout o then
      fail s!"invalid: output spec of transition '{name}' has a Xor node inside the child of its \
        Timeout node; the timeout outcome deposits one fixed set of places (IO-013)"
    if let some (s, d) := bareForward o then
      fail s!"invalid: output spec of transition '{name}' uses ForwardInput('{s}', '{d}') \
        outside the child of a Timeout node; a forward deposits only on the timeout outcome \
        (IO-014)"
    for s in forwardSources o do
      unless places.contains s do
        fail s!"invalid: Transition '{name}': ForwardInput references non-input place '{s}'"
    let bs := o.branches
    if let some (i, j) := ambiguousPair bs then
      let ps := ", ".intercalate (bs.getD i [])
      fail s!"invalid: output spec of transition '{name}' is ambiguous: output branches {i} and \
        {j} both claim \{{ps}}; no write can tell them apart (IO-012)"
  return { core := { name := name, inputs := inputs, inhibitors := inh, reads := rds,
                     resets := rst }, out := out, reapable := reapable }

def parseProperty (j : Json) : Err (Property String) := do
  let ty ← str (← field j "type") "property type"
  let places (k : String) : Err (List String) := do
    return (← strs (← field j k) k).eraseDups
  let sinks : Err (List String) :=
    match optField j "sinks" with
    | some a => strs a "sinks"
    | none => pure []
  match ty with
  | "deadlock-free" =>
    onlyKeys j ["id", "type", "sinks"] "property"
    return .deadlockFree (← sinks)
  | "terminates-at-sink" =>
    onlyKeys j ["id", "type", "sinks"] "property"
    return .terminatesAtSink (← sinks)
  | "place-bound" =>
    onlyKeys j ["id", "type", "place", "bound"] "property"
    return .placeBound (← str (← field j "place") "place") (← nat (← field j "bound") "bound")
  | "mutual-exclusion" =>
    onlyKeys j ["id", "type", "places"] "property"
    let ps ← strs (← field j "places") "places"
    if ps.length < 2 then
      fail "out-of-scope: mutual-exclusion takes at least two places"
    return .mutualExclusion ps
  | "unreachable" =>
    onlyKeys j ["id", "type", "places"] "property"
    return .unreachable (← places "places")
  | "quiescent-count" =>
    onlyKeys j ["id", "type", "places", "min", "max"] "property"
    let lo ← nat (← field j "min") "min"
    let hi ← match optField j "max" with
      | some m => some <$> nat m "max"
      | none => pure none
    if let some h := hi then
      if h < lo then fail "invalid: quiescent-count max < min (VER-002)"
    return .quiescentCount (← places "places") lo hi
  | other => fail s!"out-of-scope: property type '{other}'"

/-- A loaded corpus file. -/
structure Loaded where
  id         : String
  net        : Net String
  m0         : Marking String
  /-- `(property id, property or refusal)`. -/
  properties : List (String × Err (Property String))
  /-- Why the whole net is refused, if it is. -/
  refusal    : Option String

def parseNet (j : Json) : Err (Net String × Marking String) := do
  onlyKeys j ["id", "places", "marking", "transitions", "properties"] "net"
  let places ← match optField j "places" with
    | some a => strs a "places"
    | none => pure []
  let ts ← match optField j "transitions" with
    | some a => do (← arr a "transitions").mapM parseTrans
    | none => pure []
  let names := ts.map (·.core.name)
  if !names.Nodup then fail "invalid: two transitions share a name"
  let entries ← match optField j "marking" with
    | some m => do
      let o ← match m.getObj? with
        | .ok o => pure o
        | .error _ => fail "invalid: marking must be an object"
      o.toList.mapM fun (k, v) => do return (k, ← nat v s!"marking of '{k}'")
    | none => pure []
  return ({ places := places, transitions := ts }, ofList entries)

def load (fallbackId : String) (j : Json) : Loaded :=
  let id := (j.getObjVal? "id" >>= Json.getStr?).toOption.getD fallbackId
  let props : List (String × Err (Property String)) :=
    match j.getObjVal? "properties" >>= Json.getArr? with
    | .ok a => a.toList.zipIdx.map fun (p, i) =>
        ((p.getObjVal? "id" >>= Json.getStr?).toOption.getD s!"#{i}", parseProperty p)
    | .error _ => []
  match parseNet j with
  | .ok (net, m0) => { id, net, m0, properties := props, refusal := none }
  | .error e => { id, net := { places := [], transitions := [] }, m0 := [], properties := props,
                  refusal := some e }

/-! ### The build-check refusals on fixed specs

No corpus net fails an output-spec check, so these pin the loader's walk and check order to
the builders' messages. `buildError o` is the refusal of a transition `t` with one input `i` and
output `o` (JSON), or `none` when it loads. -/

private def buildError (o : String) : Option String :=
  match Json.parse s!"\{\"name\": \"t\", \"inputs\": [\{\"kind\": \"one\", \"place\": \"i\"}], \"output\": {o}}" with
  | .error e => some s!"json: {e}"
  | .ok j => match parseTrans j with
    | .error e => some e
    | .ok _ => none

private def p (n : String) : String := s!"\{\"type\": \"place\", \"place\": \"{n}\"}"
private def and_ (cs : List String) : String := s!"\{\"type\": \"and\", \"children\": [{", ".intercalate cs}]}"
private def xor_ (cs : List String) : String := s!"\{\"type\": \"xor\", \"children\": [{", ".intercalate cs}]}"
private def tmo (c : String) : String := s!"\{\"type\": \"timeout\", \"afterMs\": 5, \"child\": {c}}"
private def fwd (a b : String) : String := s!"\{\"type\": \"forward\", \"from\": \"{a}\", \"to\": \"{b}\"}"

private def dupMsg (q : String) : String :=
  s!"invalid: output spec of transition 't' names place '{q}' twice in one AND branch; outputs \
    are sets (IO-015) — a weighted output is not supported, add a second place or a follow-up \
    transition"

private def xorMsg : String :=
  "invalid: output spec of transition 't' has a Xor node inside the child of its Timeout node; \
    the timeout outcome deposits one fixed set of places (IO-013)"

-- IO-011: the walk names the place the builders name.
#guard buildError (and_ [xor_ [p "A", p "B"], xor_ [p "B", p "A"]]) == some (dupMsg "B")
#guard buildError (and_ [xor_ [p "A", p "B"], and_ [p "C", xor_ [p "B", p "A"]]]) == some (dupMsg "B")
#guard buildError (xor_ [and_ [p "P", p "P"], and_ [p "Q", p "Q"]]) == some (dupMsg "P")
#guard buildError (and_ [p "A", xor_ [p "B", and_ [p "C", p "A"]]]) == some (dupMsg "A")
-- A nested And is walked before its siblings are compared, as the builders do.
#guard buildError (and_ [p "A", and_ [p "B", p "A", p "B"]]) == some (dupMsg "B")
#guard buildError (and_ [p "A", p "B", p "A", p "B"]) == some (dupMsg "A")
#guard buildError (xor_ [and_ [p "P", p "A"], and_ [p "P", p "B"]]) == none
-- IO-013: an Xor anywhere in the Timeout child, after the count check, before IO-014 and IO-012.
#guard buildError (tmo (xor_ [p "A", p "B"])) == some xorMsg
#guard buildError (xor_ [p "C", tmo (and_ [p "A", xor_ [p "B", p "D"]])]) == some xorMsg
#guard buildError (tmo (xor_ [p "A", p "A"])) == some xorMsg
#guard buildError (tmo (xor_ [fwd "x" "A", p "B"])) == some xorMsg
#guard buildError (xor_ [tmo (p "A"), tmo (xor_ [p "B", p "C"])]) ==
  some "invalid: output spec of transition 't' has 2 Timeout nodes; an output spec has at most one, nested or not (IO-013)"
#guard buildError (xor_ [p "A", tmo (p "B")]) == none
#guard buildError (tmo (and_ [p "A", fwd "i" "B"])) == none

/-! ### The input-and-read refusal ([EXEC-012], ruling D15)

`transError t` is the refusal of the transition `t` (JSON), or `none` when it loads. The check
runs after the input-arc checks and before the timing and output-spec checks, and names the first
read arc, in declaration order, whose place is an input place. -/

private def transError (t : String) : Option String :=
  match Json.parse t with
  | .error e => some s!"json: {e}"
  | .ok j => match parseTrans j with
    | .error e => some e
    | .ok _ => none

private def inp (k pl : String) : String := s!"\{\"kind\": \"{k}\", \"place\": \"{pl}\"}"
private def inpN (k pl : String) (n : Nat) : String :=
  s!"\{\"kind\": \"{k}\", \"place\": \"{pl}\", \"n\": {n}}"
private def strList (xs : List String) : String := "[" ++ ", ".intercalate (xs.map (s!"\"{·}\"")) ++ "]"
private def tr (ins : List String) (rds rst : List String) (extra : String := "") : String :=
  s!"\{\"name\": \"t\", \"inputs\": [{", ".intercalate ins}], \"reads\": {strList rds}, \"resets\": {strList rst}{extra}}"

private def irMsg (pl : String) : String :=
  s!"invalid: Transition 't' declares an input arc and a read arc on place '{pl}'. A read of a place the same firing consumes from has no coherent semantics and is rejected (EXEC-012). Remove the read arc: the input arc already hands the consumed tokens to the action."

-- AC2: one(), all(), exactly(2), atLeast(1) with a read on the same place.
#guard transError (tr [inp "one" "p"] ["p"] []) == some (irMsg "p")
#guard transError (tr [inp "all" "p"] ["p"] []) == some (irMsg "p")
#guard transError (tr [inpN "exactly" "p" 2] ["p"] []) == some (irMsg "p")
#guard transError (tr [inpN "atLeast" "p" 1] ["p"] []) == some (irMsg "p")
-- AC3: reads declared b then a name b; two inputs on p and a read on p give CORE-030's message.
#guard transError (tr [inp "one" "a", inp "one" "b"] ["b", "a"] []) == some (irMsg "b")
#guard transError (tr [inp "one" "p", inp "one" "p"] ["p"] []) ==
  some "invalid: 't' declares two input arcs on one place (CORE-030)"
-- After the count checks: exactly(0) with a read on the same place gives IO-002's message.
#guard transError (tr [inpN "exactly" "p" 0] ["p"] []) == some "invalid: exactly(n) needs n ≥ 1 (IO-002)"
-- Before the timing and output-spec checks.
#guard transError (tr [inp "one" "p"] ["p"] [] ", \"timing\": {\"kind\": \"deadline\", \"latestMs\": 0}") ==
  some (irMsg "p")
#guard transError (tr [inp "one" "p"] ["p"] [] s!", \"output\": {and_ [p "A", p "A"]}") ==
  some (irMsg "p")
-- AC4: input a with read b, and a read and a reset on one place, both load.
#guard transError (tr [inp "one" "a"] ["b"] []) == none
#guard transError (tr [] ["p"] ["p"]) == none

/-! ### The timing refusals at the maximum duration

`timingError t` is the refusal of the timing `t` (JSON) of a transition `t`, or `none` when it
loads. A `window` checks its earliest bound, then `earliestMs <= latestMs`, then its latest bound
against the maximum duration, in the builders' order ([TIME-001] AC4, [TIME-005]). -/

private def timingError (t : String) : Option String :=
  match Json.parse t with
  | .error e => some s!"json: {e}"
  | .ok j => match parseTiming "t" j with
    | .error e => some e
    | .ok _ => none

private def window (e l : Nat) : String :=
  s!"\{\"kind\": \"window\", \"earliestMs\": {e}, \"latestMs\": {l}}"

private def maxMsg (kind what : String) : String :=
  s!"invalid: {kind} timing of 't' has {what} above the maximum duration (TIME-001)"

#guard timingError (window 0 maxDurationMs) == none
#guard timingError (window maxDurationMs maxDurationMs) == none
#guard timingError (window 0 (maxDurationMs + 1)) == some (maxMsg "window" "latestMs")
#guard timingError (window maxDurationMs (maxDurationMs + 1)) == some (maxMsg "window" "latestMs")
#guard timingError (window (maxDurationMs + 1) (maxDurationMs + 2)) ==
  some (maxMsg "window" "earliestMs")
#guard timingError (window 5 3) ==
  some "invalid: window of 't' has earliestMs > latestMs (TIME-005)"
#guard timingError s!"\{\"kind\": \"deadline\", \"latestMs\": {maxDurationMs}}" == none
#guard timingError s!"\{\"kind\": \"deadline\", \"latestMs\": {maxDurationMs + 1}}" ==
  some (maxMsg "deadline" "latestMs")

end Libpetri.Reference.Load
