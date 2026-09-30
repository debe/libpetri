import Lean.Data.Json
import Libpetri.Reference.Decide

/-!
# Reading a corpus net (`spec/verification-fixtures/conformance/README.md`)

Not verified: this is the front end that turns a net file into `Net String`, a canonical initial
marking and the properties. It refuses, rather than guesses:

* **invalid** nets, as the builders would reject them: two input arcs on one place ([CORE-030]),
  `exactly` / `atLeast` with `n < 1` ([IO-002], [IO-004]), a `forward` whose `from` is not an
  input place ([IO-014] AC1), an `and` without children or a `xor` with fewer than two
  ([IO-011], [IO-012]), a timeout with `afterMs ≤ 0` ([IO-013]), a branch naming a place twice
  ([IO-011]), two transitions with one name;
* invalid **timing** ([TIME-001]–[TIME-006]): an unknown `kind`, a missing or extra bound, a
  `deadline` of 0 ([TIME-003]), or a `window` with `earliestMs > latestMs` ([TIME-005]);
* nets **outside v1**: any key the schema does not define (environment places, terminals,
  ν / match specs, …), and a spec with more than one `timeout` node.

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

def forwardSources : Out String → List String
  | .forward s _ => [s]
  | .and l r => forwardSources l ++ forwardSources r
  | .xor l r => forwardSources l ++ forwardSources r
  | .timeout c => forwardSources c
  | .place _ => []

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

/-- A transition's timing ([TIME-001]–[TIME-006]), read to its reapability ([TIME-013]):
`{"kind": k, "earliestMs": e, "latestMs": l}` with the bounds `k` takes —
`immediate` / `unconstrained` none, `deadline` `latestMs`, `delayed` `earliestMs`,
`window` both (`e ≤ l`), `exact` `earliestMs` (and `latestMs` equal to it, if given). The v0
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
    return true
  | "delayed" =>
    onlyKeys j ["kind", "earliestMs"] "timing"
    let _ ← need e? "earliestMs"
    return false
  | "window" =>
    onlyKeys j ["kind", "earliestMs", "latestMs"] "timing"
    let e ← need e? "earliestMs"
    let l ← need l? "latestMs"
    if l < e then fail s!"invalid: window of '{name}' has earliestMs > latestMs (TIME-005)"
    return true
  | "exact" =>
    onlyKeys j ["kind", "earliestMs", "latestMs"] "timing"
    let e ← need e? "earliestMs"
    if let some l := l? then
      if l != e then fail s!"invalid: exact timing of '{name}' needs latestMs = earliestMs"
    return false
  | other => fail s!"invalid: timing kind '{other}' of '{name}'"

def parseTrans (j : Json) : Err (Trans String) := do
  onlyKeys j ["name", "inputs", "inhibitors", "reads", "resets", "output", "priority", "timing"]
    "transition"
  let name ← str (← field j "name") "transition name"
  let reapable ← match optField j "timing" with
    | some tm => parseTiming name tm
    | none => pure false
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
  if let some o := out then
    if timeoutCount o > 1 then fail s!"out-of-scope: '{name}' has more than one timeout"
    for s in forwardSources o do
      unless places.contains s do
        fail s!"invalid: '{name}' forwards from '{s}', which is not an input place (IO-014)"
    for b in o.branches do
      unless b.Nodup do
        fail s!"invalid: an output branch of '{name}' names a place twice (IO-011)"
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

end Libpetri.Reference.Load
