import Libpetri.Spec.Registry

set_option linter.missingDocs true

/-!
# NU-055: the refusal order (`spec/12-nu-nets.md`)

One block, `NU_055_refusal` (kind F): which refusal a name-alignment call meets first, and what
its reason names. It is a predicate over an abstract gate `R : AlignGateFn` that answers, for a
call, either a refusal (the verdict `Unknown` with that reason) or that Route B builds the graph.
Witness: `refAlignGate`, the seven steps of the refusal order tried in turn.

The call is read through the facts the refusal order looks at (`AlignCall`): the places of `S`
in the caller's order, the declared and marked places, the coloured set the classifier computes,
whether the net is in the fragment of the mode when every transition counts as a mint, the
transitions that would have to be declared mints, the injection mode and the environment places,
the inhibitor arcs and consumers of each place, and the four flags of step 1. Places and
transitions are their names (`String`, "Its places compare by name"); `<` on `String` is the
code-point order of the spec, so "the first in code-point order" is `cpFirst`.

Each of the eight lines says: when the steps before it do not apply and its own step does, the
gate refuses with that step's reason; the last line says that when no step applies, the gate
builds. Together they fix the gate (`NU_055_refusal_eq_ref`). Consequences, not lines: a call the
gate lets through has every place of `S` declared or marked and coloured, and no coloured place
marked, which are the premises `hps` and `hempty` of `NU_055_sound`
(`NU_055_refusal_build_premises`); so an absent or uncoloured place of `S` is never decided
(`NU_055_refusal_uncoloured_refused`), and neither is `QuiescentNameAligned` with a declared
environment place under modelled injection (`NU_055_refusal_envQuiescent_refused`).

Wrong gates, one per line: no absent-place check (line 1), the uncoloured check before the
fragment decline (line 2), the arrival refusal after the marked place (line 3), the environment
refusal before the undeclared mints and the mints in some order other than the net's (line 4), the marked place before the environment refusal
(line 5), the uncoloured place in code-point order or not checked at all (line 6), the marked place in the order the
marking lists it (line 7), and a gate that never builds (line 8). Mutant readings: line 4 in
the classifier's order, line 6 in code-point order, line 7 in marking order.
-/

namespace Libpetri.Spec

/-! ## The call, as the refusal order reads it -/

/-- How a call models its environment places ([VER-006]), as the refusal order reads it. -/
inductive AlignInj where
  /-- `Ignore`, or no environment place registered: nothing is modelled. -/
  | ignore
  /-- `AlwaysAvailable` or `Bounded(k)`: Route B keeps each environment place as an
  inexhaustible input. -/
  | modelled
  /-- `Arrivals(k)` or `Arrivals(min, max)`: the net is closed and has no environment place left;
  `fed` lists the places an arrival feeds, in the order the environment places were registered
  (none under `Arrivals(0)`). -/
  | arrivals (fed : List String)
  deriving DecidableEq

/-- A call to verify `NameAligned(S)` or `QuiescentNameAligned(S)`, read through the facts the
refusal order looks at. Places and transitions are their names. -/
structure AlignCall where
  /-- `QuiescentNameAligned(S)` (`true`) or `NameAligned(S)` (`false`). -/
  quiescent : Bool
  /-- The places of `S`, in the order the caller gives, a repeat already dropped. -/
  S : List String
  /-- The call was cancelled, or had its total budget spent, before it started ([VER-013]). -/
  stopped : Bool
  /-- The places the net declares. -/
  declared : List String
  /-- The places the initial marking marks, in the order the marking lists them. -/
  marked : List String
  /-- A `Bounded(k)` environment outside its premises ([VER-006] AC3). -/
  boundedOutside : Bool
  /-- The in-flight refusal of [VER-004] applies. -/
  inFlight : Bool
  /-- The fragment mode is BASE (`true`) or EXTENDED (`false`). -/
  base : Bool
  /-- The net is inside the fragment of the mode when every transition counts as a mint. -/
  fragAll : Bool
  /-- The transitions of the net, in declaration order (the order they were added to the
  builder). -/
  transitions : List String
  /-- The transitions that write a coloured place without consuming one and are not declared
  mints, as the classifier finds them with every transition counted as a mint ([NU-010]), in
  whatever order it holds them: step 4 reads only which transitions they are. -/
  undeclared : List String
  /-- The coloured set the classifier computes for the call: match keys, and under EXTENDED the
  declared carriers and relay targets. -/
  coloured : List String
  /-- The injection mode. -/
  inj : AlignInj
  /-- The registered environment places. -/
  env : List String
  /-- The transitions with an inhibitor arc on a place. -/
  inhib : String → List String
  /-- The number of transitions that consume a place. -/
  consumers : String → Nat
  /-- Conflict priority ([NU-052]) is in effect for the call. -/
  conflict : Bool

/-- The reason of a refusal: what the `Unknown` names. -/
inductive AlignRefusal where
  /-- Cancelled or out of total budget before the call started ([VER-013]). -/
  | stopped
  /-- A place of `S` the net does not declare and the initial marking does not mark. -/
  | absent (p : String)
  /-- A `Bounded(k)` environment outside its premises ([VER-006] AC3). -/
  | boundedPremise
  /-- The in-flight refusal of [VER-004]. -/
  | inFlight
  /-- The net is outside the fragment of the mode (`underBase`: the mode is BASE). Under
  EXTENDED this is the "EXTENDED declined" note; under BASE the decline names EXTENDED. -/
  | outsideFragment (underBase : Bool)
  /-- An arrival into the coloured place `p` ([VER-006] AC10). -/
  | arrival (p : String)
  /-- The transitions that would have to be declared mints ([NU-010]), in declaration order. -/
  | undeclaredMints (ts : List String)
  /-- The environment place `p` is coloured. -/
  | envColoured (p : String)
  /-- The environment place `p` is tested by an inhibitor arc of transition `t`. -/
  | envInhibitor (p t : String)
  /-- The environment place `p` is consumed by two or more transitions under conflict priority. -/
  | envShared (p : String)
  /-- The environment place `p` is registered and the property reads quiescence. -/
  | envQuiescent (p : String)
  /-- The environment place `p` is a place of `S`. -/
  | envRead (p : String)
  /-- The place `p` of `S` is not coloured; under BASE the reason also names EXTENDED. -/
  | uncoloured (p : String) (namesExtended : Bool)
  /-- The coloured place `p` holds a token in the initial marking. -/
  | markedColoured (p : String)
  deriving DecidableEq

/-- What the gate answers for a call: a refusal, the verdict `Unknown` with its reason, or that
Route B builds the graph and reads the verdict off it. -/
inductive AlignGate where
  /-- The call is refused: `Unknown` with the reason `r`. -/
  | refuse (r : AlignRefusal)
  /-- No refusal applies: Route B builds the graph. -/
  | build
  deriving DecidableEq

/-- A gate: what it answers for each call. -/
abbrev AlignGateFn := AlignCall → AlignGate

/-! ## The steps -/

/-- The first name of a list in code-point order (`<` on `String`), or none for an empty list. -/
def cpFirst (l : List String) : Option String :=
  l.foldl (fun acc a => match acc with
    | none => some a
    | some b => if a < b then some a else some b) none

/-- The first place of `S`, in the order of `S`, that the net does not declare and the initial
marking does not mark. -/
def absentFirst (c : AlignCall) : Option String :=
  c.S.find? (fun p => !(decide (p ∈ c.declared)) && !(decide (p ∈ c.marked)))

/-- Step 1: the refusals that precede every route, in their order: the stop, the first absent
place of `S`, a `Bounded(k)` environment outside its premises, the in-flight refusal. -/
def step1 (c : AlignCall) : Option AlignRefusal :=
  if c.stopped then some .stopped
  else match absentFirst c with
    | some p => some (.absent p)
    | none =>
      if c.boundedOutside then some .boundedPremise
      else if c.inFlight then some .inFlight else none

/-- Step 2: the net is outside the fragment of the mode even when every transition counts as a
mint; the decline carries the mode, and names EXTENDED under BASE. -/
def step2 (c : AlignCall) : Option AlignRefusal :=
  if c.fragAll then none else some (.outsideFragment c.base)

/-- Step 3: under `Arrivals(k)` or `Arrivals(min, max)`, the first place an arrival feeds, in
registration order, that is coloured. -/
def step3 (c : AlignCall) : Option AlignRefusal :=
  match c.inj with
  | .arrivals fed => (fed.find? (fun p => decide (p ∈ c.coloured))).map .arrival
  | _ => none

/-- The transitions that would have to be declared mints, in declaration order. -/
def undeclaredInOrder (c : AlignCall) : List String :=
  c.transitions.filter (fun t => decide (t ∈ c.undeclared))

/-- Step 4: transitions write a coloured place without consuming one and are not declared
mints; the decline names them in declaration order. -/
def step4 (c : AlignCall) : Option AlignRefusal :=
  match undeclaredInOrder c with
  | [] => none
  | ts => some (.undeclaredMints ts)

/-- The registered environment places the net declares. -/
def envDeclared (c : AlignCall) : List String :=
  c.env.filter (fun p => decide (p ∈ c.declared))

/-- The four rules of step 5, in their order, each over the declared environment places `E` in
code-point order: a coloured one; one an inhibitor arc tests (with the first such transition in
code-point order); where conflict priority is in effect, one two or more transitions consume;
then, for `QuiescentNameAligned`, the first of them, and for `NameAligned`, the first that is in
`S` (code-point order, not the order of `S`). -/
def envRule (c : AlignCall) (E : List String) : Option AlignRefusal :=
  match cpFirst (E.filter (fun p => decide (p ∈ c.coloured))) with
  | some p => some (.envColoured p)
  | none =>
    match cpFirst (E.filter (fun p => !(c.inhib p).isEmpty)) with
    | some p => some (.envInhibitor p ((cpFirst (c.inhib p)).getD ""))
    | none =>
      match (if c.conflict then cpFirst (E.filter (fun p => decide (2 ≤ c.consumers p)))
             else none) with
      | some p => some (.envShared p)
      | none =>
        if c.quiescent then (cpFirst E).map .envQuiescent
        else (cpFirst (E.filter (fun p => decide (p ∈ c.S)))).map .envRead

/-- Step 5: under `AlwaysAvailable` or `Bounded(k)`, an environment place Route B cannot
model. -/
def step5 (c : AlignCall) : Option AlignRefusal :=
  match c.inj with
  | .modelled => envRule c (envDeclared c)
  | _ => none

/-- Step 6: the first place of `S`, in the order of `S`, that is not coloured. -/
def step6 (c : AlignCall) : Option AlignRefusal :=
  (c.S.find? (fun p => !(decide (p ∈ c.coloured)))).map (fun p => .uncoloured p c.base)

/-- Step 7: the first coloured place the initial marking marks, in code-point order. -/
def step7 (c : AlignCall) : Option AlignRefusal :=
  (cpFirst (c.coloured.filter (fun p => decide (p ∈ c.marked)))).map .markedColoured

/-- The gate that tries a list of steps in turn: the first refusal found, or `build`. -/
def gateOf (steps : List (AlignCall → Option AlignRefusal)) : AlignGateFn := fun c =>
  match steps.findSome? (fun s => s c) with
  | some r => .refuse r
  | none => .build

/-- The shipped gate: steps 1 to 7 in their order (Rust `verify_net` up to
`name_alignment_refusal`, Java `SmtVerifier.verify`, TypeScript `SmtVerifier.verify`).
Registered as a witness model. -/
def refAlignGate : AlignGateFn := gateOf [step1, step2, step3, step4, step5, step6, step7]

#spec_witness refAlignGate

/-! ## NU-055 (F): the refusal order -/

requirement NU_055_refusal
  id "NU-055"
  title "Name Alignment: the refusal order"
  kind F
  scope "every verifier that offers NameAligned or QuiescentNameAligned (MAY); the refusals before Route B builds the graph"
  source verbatim "spec/12-nu-nets.md"
  quote "A call can meet several of these refusals at once."
        "Its verdict is `Unknown` with the reason of the first that applies, in this order, so every implementation names the same place:"
        "The refusals that precede every route for every property, in this order: a call cancelled or out of total budget before it starts ([VER-013]); a place of `S` that the net does not declare and the initial marking does not mark ([VER-003] AC5), naming the first such place of `S`; a `Bounded(k)` environment outside its premises ([VER-006] AC3); the in-flight refusal of [VER-004]."
        "The net is outside the fragment of the mode even when every transition counts as a mint: the fragment decline of the mode, under EXTENDED the note of **EXTENDED** above, under BASE a decline that names EXTENDED."
        "Under `Arrivals(k)` or `Arrivals(min, max)`, an arrival into a coloured place ([VER-006] AC10), naming the first such place in the order the environment places were registered."
        "The net is outside the fragment only because a transition writes a coloured place without consuming one and is not a declared mint: the decline names those transitions in declaration order ([NU-010])."
        "Under `AlwaysAvailable` or `Bounded(k)`, an environment place Route B cannot model ([VER-006] AC8). The rules run in this order, each over the environment places the net declares in code-point order of names: one that is coloured; one that an inhibitor arc tests (naming the first such transition in code-point order); where conflict priority is in effect ([NU-052]), one that two or more transitions consume; then, for `QuiescentNameAligned`, the first of them (**Modelled injection** above), and for `NameAligned`, the first that is in `S`."
        "The first place of `S`, in the order of `S`, that is not coloured. Under BASE the reason also names EXTENDED."
        "A coloured place the initial marking marks: the first in code-point order of place names."
        "Steps 3 and 5 apply whether or not the coloured places start empty."
        "Every place of `S` MUST be a coloured place of the fragment Route B classified for the call: match keys ([NU-020]), declared carriers ([NU-051]) and relay targets ([NU-054])."
        "A place that is uncoloured, or absent from the net (the net does not declare it and the initial marking does not mark it), MUST fail loudly: the verdict is `Unknown`, never `Proven`, and where no earlier refusal of the refusal order below applies, its reason names a place of `S`: the first absent place of `S`, otherwise the first uncoloured one."
        "The coloured places MUST start empty (the `hempty` premise of the Lean theorems)."
        "A call whose initial marking holds a token in a coloured place (a restored marking, [CORE-073], [NU-011]) is `Unknown`, and where no earlier refusal of the refusal order below applies, its reason names the place, the first in code-point order of place names when several are marked; since nothing else decides the property, there is no fallback."
        "Under **BASE** the coloured set is the match keys alone ([NU-051], [NU-054]), so a property place that is a carrier or a relay target is uncoloured there."
        "Such a call is refused at step 2 or at step 6 of the refusal order below unless an earlier step refuses it, and the reason of either step MUST name EXTENDED."
        "In addition, under these modes `QuiescentNameAligned` with a registered environment place that the net declares is `Unknown`, and where no earlier refusal of the refusal order below applies, nor an earlier rule of its step 5, the reason names the first such place in code-point order and points to `Arrivals` ([VER-006]); the vacuity reading of [VER-006] AC6 does not apply to it."
        "*If* a name-alignment call meets a refusal of step 1 of the refusal order, *then* the verifier *shall* answer `Unknown` with the reason of the first refusal of step 1 that applies, in the order step 1 lists them, naming for an absent place the first place of `S` that the net does not declare and the initial marking does not mark."
        "*If* no refusal of step 1 applies and the net is outside the fragment of the mode even when every transition counts as a mint, *then* the verifier *shall* answer `Unknown` with the fragment decline of the mode, whose reason names EXTENDED under BASE."
        "*If* no refusal of steps 1 and 2 applies and, under `Arrivals(k)` or `Arrivals(min, max)`, an arrival feeds a coloured place, *then* the verifier *shall* answer `Unknown` naming the first such place in the order the environment places were registered."
        "*If* no refusal of steps 1 to 3 applies and transitions write a coloured place without consuming one and are not declared mints, *then* the verifier *shall* answer `Unknown` naming those transitions in declaration order."
        "*If* no refusal of steps 1 to 4 applies and, under `AlwaysAvailable` or `Bounded(k)`, a rule of step 5 applies, *then* the verifier *shall* answer `Unknown` naming the first environment place, in code-point order, that the first applicable rule finds, and for an inhibitor arc also the first transition in code-point order that tests it."
        "*If* no refusal of steps 1 to 5 applies and a place of `S` is not coloured, *then* the verifier *shall* answer `Unknown` naming the first such place in the order of `S`, and under BASE the reason *shall* also name EXTENDED."
        "*If* no refusal of steps 1 to 6 applies and the initial marking marks a coloured place, *then* the verifier *shall* answer `Unknown` naming the first marked coloured place in code-point order of place names."
        "*If* no step of the refusal order applies, *then* the verifier *shall not* refuse the call with a refusal of that order: unless the call is the caller's error of a declared mint or carrier that is not in the net, or a later poll sees a stop ([VER-013]), Route B builds the graph, and the verdict is the one it reads off that graph."
  reading "For every call c, with step1 to step7 the seven steps of the refusal order read on c (each the reason of its first refusal that applies, or none):"
          "if step 1 gives the reason r, R refuses c with r;"
          "if step 1 gives none and step 2 gives r, R refuses c with r;"
          "if steps 1 and 2 give none and step 3 gives r, R refuses c with r;"
          "if steps 1 to 3 give none and step 4 gives r, R refuses c with r;"
          "if steps 1 to 4 give none and step 5 gives r, R refuses c with r;"
          "if steps 1 to 5 give none and step 6 gives r, R refuses c with r;"
          "if steps 1 to 6 give none and step 7 gives r, R refuses c with r;"
          "if steps 1 to 7 all give none, R builds the graph."
  assumes "The model is a gate R : AlignCall → AlignGate. A call (AlignCall) is read through the facts the refusal order looks at: the places of S in the caller's order (a repeat already dropped, NU_055's assumes), the places the net declares and the places the initial marking marks, the stop, the Bounded(k) and in-flight flags, the fragment mode, whether the net is inside the fragment of the mode when every transition counts as a mint, the transitions of the net in declaration order and those of them that would have to be declared mints, the coloured set the classifier computes, the injection mode with the arrival places in registration order, the registered environment places, and per place the transitions with an inhibitor arc on it and the number of transitions that consume it. Places and transitions are their names (String), as 'Its places compare by name' says; < on String compares code points, so 'the first in code-point order' is cpFirst. A refusal .refuse r is the verdict Unknown with the reason r; .build is the call reaching the graph. The calls are those without the caller's error of a declared mint or carrier that is not in the net: 'A declared mint or carrier that is not in the net is the caller's error and is reported as [NU-010] and [NU-051] say, outside this order.' puts that error outside the order, and the runtimes place it differently (Rust checks an unknown declared mint after the absent place of step 1 and before the Bounded(k) premises), so no line speaks of such a call. The route a refusal reports is not modelled: the runtimes report Unavailable for step 1 and Route B for steps 2 to 7 (Rust verify_net and route_b_declined)."
          "The step functions step1 to step7 are vocabulary: each is the bullet of the refusal order it is named after, read on the call, and returns the reason of its first refusal that applies. The lines fix the gate on every call (NU_055_refusal_eq_ref): the refusal order is a function of the call, so the block states which refusal comes first and what it names, not how a verifier computes it. Why each refusal exists (VER-003 AC5, VER-006 AC3, AC8 and AC10, VER-004, NU-010, NU-051) is those requirements'; whether a call meets one (the classifier's fragment and coloured set, the Bounded(k) premises, the in-flight split) is a fact of the call here."
          "Line 1 is step 1, its four refusals in the order the bullet lists them, the absent place being the first place of S that the net does not declare and the initial marking does not mark, which is VER-003's unresolved check on S (Verifier/Result.lean Unresolved). 'Cancelled or out of total budget before it starts' is a stop the first poll sees; a stop that a later poll sees, on entering Route B, is VER-013's and names the step it was charged to. A gate without the absent check lets an absent place reach step 6, where it is named as uncoloured (NU_055_refusal_forbids_noAbsent)."
          "Line 2 is step 2, and lines 2 and 6 together are the EXTENDED paragraph's 'Such a call is refused at step 2 or at step 6 of the refusal order below unless an earlier step refuses it, and the reason of either step MUST name EXTENDED.' (clash nu-c#7, the body SHOULD made MUST as AC3 has it, ruling D20, and scoped to the refusal order: under BASE a carrier or relay target of S is uncoloured, so a call that steps 1 and 2 let through and steps 3 to 5 do not refuse meets step 6, whose reason carries the mode as step 2's does; a stop, a coloured arrival, undeclared mints or an environment place come first and name no mode), and 'A net outside the EXTENDED fragment gets the \"EXTENDED declined\" note of [NU-051] and the verdict `Unknown`.': the decline carries the mode (underBase), and names EXTENDED under BASE; under EXTENDED it is the note of the EXTENDED paragraph, which the mode alone tells apart. That the note never says the property was verified by another route is its text (N): every reason here is a refusal, and no route other than Route B is consulted. A gate that checks the places of S before the fragment names list on AC3's BASE call (NU_055_refusal_forbids_uncolouredFirst)."
          "Line 3 is step 3, for Arrivals(k) and Arrivals(min, max) alike (VER-006 names both; the runtimes read either through their arrivals injection), and 'Under `Arrivals` the net has no environment places left ([VER-006]); the decline of [VER-006] AC10 for an arrival into a coloured place still applies.' The place named is the first coloured one in the order the environment places were registered, as all three runtimes name it (Rust coloured_arrival_reason, Java colouredArrivalReason, TypeScript colouredArrivalReason over the arrival's injected list). The runtimes read the arrival places on the coloured set of the classifier run with every transition counted a mint; declaring mints changes no coloured place, so that set is the call's coloured set."
          "Line 4 is step 4: the fragment would hold if the listed transitions were declared mints, and the decline names them in declaration order, the order the net holds its transitions (CORE-040), as all three runtimes list them (Rust undeclared_mints_for, Java NameFragment.undeclaredMints, TypeScript undeclaredMints: the classifier's mints in net order, less the declared ones). Which transitions they are is a fact of the call (undeclared, in any order); their order is read off the net (undeclaredInOrder). A gate that lists them in the order the classifier holds them names sendA, sendB on a net that declares sendB first (NU_055_refusal_forbids_mintsAnyOrder). The caller's error of a declared mint or carrier missing from the net is not a line: that check is NU-010's and NU-051's, and the first assumes says why no line speaks of it."
          "Line 5 is step 5 with its four rules, the Modelled injection paragraph's 'In addition, under these modes QuiescentNameAligned with a registered environment place that the net declares is Unknown, and where no earlier refusal ... applies, nor an earlier rule of its step 5, the reason names the first such place in code-point order ...' (its fourth rule; that such a call is never built is NU_055_refusal_envQuiescent_refused). Under Ignore no environment place is modelled and nothing is refused for one; a registered place the net does not declare is not read (envDeclared) and 'Under `AlwaysAvailable` or `Bounded(k)` ([VER-006]) the decline rule of [NU-050] and [VER-006] AC8 applies to both properties.' (its first three rules and the NameAligned half of the fourth). Conflict priority is the call's priority after NU-052's rule that turns it off when a pruner cannot be split, as all three runtimes read it (effective priority). The rest of that paragraph explains why (the graph never consumes an environment place, the worked example would truncate); it is not a line."
          "'Steps 3 and 5 apply whether or not the coloured places start empty.' is the order of lines 3, 5 and 7: a marked coloured place is the last refusal. The other properties take a different path in the runtimes (a marked coloured place makes Route B decline and the flat pipeline decide them); a gate that keeps that path for name alignment names the marked place first (NU_055_refusal_forbids_markedBeforeEnv, NU_055_refusal_forbids_arrivalLast)."
          "Line 6 is step 6, the step-6 half of the EXTENDED sentence (see line 2), 'Every place of S MUST be a coloured place of the fragment Route B classified for the call' and the coloured-only paragraph's 'MUST fail loudly' sentence, reworded under ruling NC-7 (a) and D20 (clash nu-c#9): the reason names a place of S only where no earlier refusal applies; 'absent' is step 1's 'not declared and not marked'. The sentence's 'never Proven' is NU_055_refusal_uncoloured_refused: a call with an absent or uncoloured place of S is refused, so the graph is never built for it. That such a place would make the predicate hold vacuously is NU_055's assumes (alignedAll_uncoloured)."
          "Line 7 is step 7, 'The coloured places MUST start empty' and the sentence on a restored marking, which like the MUST fail loudly sentence names the place only where no earlier refusal applies (AC8: with box marked, QuiescentNameAligned(box, ready) names ready); that such a call is Unknown whatever comes first is NU_055_refusal_build_premises (no call with a marked coloured place is built). The place named is the first marked coloured place in code-point order, whatever the order of S or of the marking. 'There is no fallback' is the Route B only rule: no other route decides a name-alignment property, which is a pipeline rule and not a line of this block."
          "Line 8 is the closing EARS sentence: no refusal of this order fires on a call none of the steps refuse. .build is the gate letting the call through to Route B, not a promise that the graph is finished: a stop that a later poll sees ends the call there, which is VER-013's and NU_055_truncation's (a cancelled build does not close), and the caller's error of a missing mint or carrier is outside the calls this block reads. 'The `Ignore` downgrade of a `Proven` ([VER-006]) and a truncation `Unknown` are not refusals: they follow a graph that was built.' is this line read with NU_055_truncation: they are verdicts read off the graph, after the gate built it. The gate's build is where NU_055_sound's premises hps (every place of S coloured) and hempty (the coloured places start empty) come from (NU_055_refusal_build_premises)."
          "Left out: 'Route B only' (no other route decides, no NU-053 fallback, the script encoders return none) and the routing rule that sends a name-alignment property to Route B before a budget place; they are dispatch rules of the verifier pipeline, not refusals. The reason texts, the report lines and the Property: description are N."
          "AC2 (an uncoloured place, the first in S, and an absent place, Unknown naming it, never Proven) is lines 1 and 6: NU_055_refusal_nonvacuous names ready on QuiescentNameAligned(box, ready) and on (box, ready, clr), and nope on (box, nope). AC3 (under BASE, Unknown naming EXTENDED) is line 2 on the BASE call of the worked example (nu055r_base); the report note naming the ignored relay declarations is NU-054's (AC5). AC2's absent place is anchored to the worked example (box, nope), like its uncoloured one. AC6 (typed registered under AlwaysAvailable, Unknown naming typed; a marked coloured place, Unknown, naming it where no earlier refusal applies: box on (box, list) with box marked) is lines 5 and 7. AC8 (the refusal order on the worked example) is lines 5, 6 and 7, all three of its calls in NU_055_refusal_nonvacuous. AC6's 'on the buggy variant' and AC8's report wording are fixture tests (Q); the gate reads the same facts on both variants."
  signoff "pending"
  statement : AlignGateFn → Prop :=
    fun R => ∀ c : AlignCall,
      (∀ r, step1 c = some r → R c = .refuse r) ∧
      (step1 c = none → ∀ r, step2 c = some r → R c = .refuse r) ∧
      (step1 c = none → step2 c = none → ∀ r, step3 c = some r → R c = .refuse r) ∧
      (step1 c = none → step2 c = none → step3 c = none →
        ∀ r, step4 c = some r → R c = .refuse r) ∧
      (step1 c = none → step2 c = none → step3 c = none → step4 c = none →
        ∀ r, step5 c = some r → R c = .refuse r) ∧
      (step1 c = none → step2 c = none → step3 c = none → step4 c = none → step5 c = none →
        ∀ r, step6 c = some r → R c = .refuse r) ∧
      (step1 c = none → step2 c = none → step3 c = none → step4 c = none → step5 c = none →
        step6 c = none → ∀ r, step7 c = some r → R c = .refuse r) ∧
      (step1 c = none → step2 c = none → step3 c = none → step4 c = none → step5 c = none →
        step6 c = none → step7 c = none → R c = .build)

/- The pinned readable form of NU_055_refusal: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.NU_055_refusal : AlignGateFn → Prop :=
fun R =>
  ∀ (c : AlignCall),
    (∀ (r : AlignRefusal), step1 c = some r → R c = AlignGate.refuse r) ∧
      (step1 c = none → ∀ (r : AlignRefusal), step2 c = some r → R c = AlignGate.refuse r) ∧
        (step1 c = none → step2 c = none → ∀ (r : AlignRefusal), step3 c = some r → R c = AlignGate.refuse r) ∧
          (step1 c = none →
              step2 c = none → step3 c = none → ∀ (r : AlignRefusal), step4 c = some r → R c = AlignGate.refuse r) ∧
            (step1 c = none →
                step2 c = none →
                  step3 c = none → step4 c = none → ∀ (r : AlignRefusal), step5 c = some r → R c = AlignGate.refuse r) ∧
              (step1 c = none →
                  step2 c = none →
                    step3 c = none →
                      step4 c = none →
                        step5 c = none → ∀ (r : AlignRefusal), step6 c = some r → R c = AlignGate.refuse r) ∧
                (step1 c = none →
                    step2 c = none →
                      step3 c = none →
                        step4 c = none →
                          step5 c = none →
                            step6 c = none → ∀ (r : AlignRefusal), step7 c = some r → R c = AlignGate.refuse r) ∧
                  (step1 c = none →
                    step2 c = none →
                      step3 c = none →
                        step4 c = none → step5 c = none → step6 c = none → step7 c = none → R c = AlignGate.build)
-/
#guard_msgs in #print NU_055_refusal

/-! ### The reference -/

/-- Any gate that tries seven steps in turn meets the eight lines read on those seven steps. -/
theorem gateOf_lines (s1 s2 s3 s4 s5 s6 s7 : AlignCall → Option AlignRefusal) (c : AlignCall) :
    (∀ r, s1 c = some r → gateOf [s1, s2, s3, s4, s5, s6, s7] c = .refuse r) ∧
    (s1 c = none → ∀ r, s2 c = some r → gateOf [s1, s2, s3, s4, s5, s6, s7] c = .refuse r) ∧
    (s1 c = none → s2 c = none → ∀ r, s3 c = some r →
      gateOf [s1, s2, s3, s4, s5, s6, s7] c = .refuse r) ∧
    (s1 c = none → s2 c = none → s3 c = none → ∀ r, s4 c = some r →
      gateOf [s1, s2, s3, s4, s5, s6, s7] c = .refuse r) ∧
    (s1 c = none → s2 c = none → s3 c = none → s4 c = none → ∀ r, s5 c = some r →
      gateOf [s1, s2, s3, s4, s5, s6, s7] c = .refuse r) ∧
    (s1 c = none → s2 c = none → s3 c = none → s4 c = none → s5 c = none → ∀ r, s6 c = some r →
      gateOf [s1, s2, s3, s4, s5, s6, s7] c = .refuse r) ∧
    (s1 c = none → s2 c = none → s3 c = none → s4 c = none → s5 c = none → s6 c = none →
      ∀ r, s7 c = some r → gateOf [s1, s2, s3, s4, s5, s6, s7] c = .refuse r) ∧
    (s1 c = none → s2 c = none → s3 c = none → s4 c = none → s5 c = none → s6 c = none →
      s7 c = none → gateOf [s1, s2, s3, s4, s5, s6, s7] c = .build) := by
  refine ⟨fun r h1 => ?_, fun h1 r h2 => ?_, fun h1 h2 r h3 => ?_, fun h1 h2 h3 r h4 => ?_,
    fun h1 h2 h3 h4 r h5 => ?_, fun h1 h2 h3 h4 h5 r h6 => ?_,
    fun h1 h2 h3 h4 h5 h6 r h7 => ?_, fun h1 h2 h3 h4 h5 h6 h7 => ?_⟩ <;>
    simp_all [gateOf]

/-- The shipped gate meets the refusal order: it tries steps 1 to 7 in turn and refuses with the
first reason it finds, or builds the graph when none applies. -/
@[evidence holds NU_055_refusal]
theorem NU_055_refusal_reference : NU_055_refusal refAlignGate := fun c =>
  gateOf_lines step1 step2 step3 step4 step5 step6 step7 c

/-! ### Consequences of the lines -/

/-- The lines fix the gate: a gate that meets them answers every call as the shipped one does. -/
theorem NU_055_refusal_eq_ref {R : AlignGateFn} (h : NU_055_refusal R) (c : AlignCall) :
    R c = refAlignGate c := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := h c
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩ := NU_055_refusal_reference c
  cases h1 : step1 c with
  | some r => rw [l1 r h1, r1 r h1]
  | none =>
  cases h2 : step2 c with
  | some r => rw [l2 h1 r h2, r2 h1 r h2]
  | none =>
  cases h3 : step3 c with
  | some r => rw [l3 h1 h2 r h3, r3 h1 h2 r h3]
  | none =>
  cases h4 : step4 c with
  | some r => rw [l4 h1 h2 h3 r h4, r4 h1 h2 h3 r h4]
  | none =>
  cases h5 : step5 c with
  | some r => rw [l5 h1 h2 h3 h4 r h5, r5 h1 h2 h3 h4 r h5]
  | none =>
  cases h6 : step6 c with
  | some r => rw [l6 h1 h2 h3 h4 h5 r h6, r6 h1 h2 h3 h4 h5 r h6]
  | none =>
  cases h7 : step7 c with
  | some r => rw [l7 h1 h2 h3 h4 h5 h6 r h7, r7 h1 h2 h3 h4 h5 h6 r h7]
  | none => rw [l8 h1 h2 h3 h4 h5 h6 h7, r8 h1 h2 h3 h4 h5 h6 h7]

/-- A fold that starts from a name ends at a name. -/
theorem nu055r_foldl_some (l : List String) (b : String) :
    ∃ x, l.foldl (fun acc a => match acc with
      | none => some a
      | some b => if a < b then some a else some b) (some b) = some x := by
  induction l generalizing b with
  | nil => exact ⟨b, rfl⟩
  | cons a t ih =>
    simp only [List.foldl_cons]
    split
    · exact ih a
    · exact ih b

/-- `cpFirst` finds no name exactly on the empty list. -/
theorem cpFirst_eq_none {l : List String} : cpFirst l = none ↔ l = [] := by
  constructor
  · intro h
    cases l with
    | nil => rfl
    | cons a t =>
      obtain ⟨x, hx⟩ := nu055r_foldl_some t a
      simp only [cpFirst, List.foldl_cons] at h
      rw [hx] at h
      cases h
  · rintro rfl; rfl

/-- When every step gives none, the gate a meeting `R` gives is `build`, and conversely. -/
theorem nu055r_build_iff {R : AlignGateFn} (h : NU_055_refusal R) (c : AlignCall) :
    R c = .build ↔ step1 c = none ∧ step2 c = none ∧ step3 c = none ∧ step4 c = none ∧
      step5 c = none ∧ step6 c = none ∧ step7 c = none := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := h c
  constructor
  · intro hb
    have n1 : step1 c = none := by
      cases h1 : step1 c with
      | none => rfl
      | some r => rw [l1 r h1] at hb; cases hb
    have n2 : step2 c = none := by
      cases h2 : step2 c with
      | none => rfl
      | some r => rw [l2 n1 r h2] at hb; cases hb
    have n3 : step3 c = none := by
      cases h3 : step3 c with
      | none => rfl
      | some r => rw [l3 n1 n2 r h3] at hb; cases hb
    have n4 : step4 c = none := by
      cases h4 : step4 c with
      | none => rfl
      | some r => rw [l4 n1 n2 n3 r h4] at hb; cases hb
    have n5 : step5 c = none := by
      cases h5 : step5 c with
      | none => rfl
      | some r => rw [l5 n1 n2 n3 n4 r h5] at hb; cases hb
    have n6 : step6 c = none := by
      cases h6 : step6 c with
      | none => rfl
      | some r => rw [l6 n1 n2 n3 n4 n5 r h6] at hb; cases hb
    have n7 : step7 c = none := by
      cases h7 : step7 c with
      | none => rfl
      | some r => rw [l7 n1 n2 n3 n4 n5 n6 r h7] at hb; cases hb
    exact ⟨n1, n2, n3, n4, n5, n6, n7⟩
  · rintro ⟨n1, n2, n3, n4, n5, n6, n7⟩
    exact l8 n1 n2 n3 n4 n5 n6 n7

/-- What the gate's build guarantees: a call that a gate meeting the lines lets through to the
graph was not stopped, every place of `S` is declared or marked and coloured, and no coloured
place is marked. These are the premises `hps` (every place of `S` coloured) and `hempty` (the
coloured places start empty) of `NU_055_sound`: the refusal order is what enforces them. -/
theorem NU_055_refusal_build_premises {R : AlignGateFn} (h : NU_055_refusal R) {c : AlignCall}
    (hb : R c = .build) :
    c.stopped = false ∧ (∀ p ∈ c.S, p ∈ c.declared ∨ p ∈ c.marked) ∧
      (∀ p ∈ c.S, p ∈ c.coloured) ∧ (∀ p ∈ c.coloured, p ∉ c.marked) := by
  obtain ⟨n1, -, -, -, -, n6, n7⟩ := (nu055r_build_iff h c).mp hb
  have hs : c.stopped = false := by
    cases hc : c.stopped
    · rfl
    · simp [step1, hc] at n1
  have ha : absentFirst c = none := by
    cases hc : absentFirst c with
    | none => rfl
    | some p => simp [step1, hs, hc] at n1
  refine ⟨hs, fun p hp => ?_, fun p hp => ?_, fun p hp hm => ?_⟩
  · have := List.find?_eq_none.mp ha p hp
    by_cases hd : p ∈ c.declared
    · exact .inl hd
    · exact .inr (by simpa [hd] using this)
  · have h6 : c.S.find? (fun p => !(decide (p ∈ c.coloured))) = none := by
      simpa [step6] using n6
    have := List.find?_eq_none.mp h6 p hp
    simpa using this
  · have h7 : cpFirst (c.coloured.filter (fun p => decide (p ∈ c.marked))) = none := by
      simpa [step7] using n7
    have hnil := cpFirst_eq_none.mp h7
    have : p ∈ c.coloured.filter (fun p => decide (p ∈ c.marked)) :=
      List.mem_filter.mpr ⟨hp, by simpa using hm⟩
    rw [hnil] at this
    cases this

/-- "MUST fail loudly ... never `Proven`": a call naming in `S` a place that is absent from the
net or not coloured is refused by every gate that meets the lines, so the graph that could prove
it is never built. -/
theorem NU_055_refusal_uncoloured_refused {R : AlignGateFn} (h : NU_055_refusal R)
    {c : AlignCall} {p : String} (hp : p ∈ c.S)
    (hbad : (p ∉ c.declared ∧ p ∉ c.marked) ∨ p ∉ c.coloured) : R c ≠ .build := by
  intro hb
  obtain ⟨-, hdecl, hcol, -⟩ := NU_055_refusal_build_premises h hb
  rcases hbad with ⟨hd, hm⟩ | hc
  · rcases hdecl p hp with h' | h'
    · exact hd h'
    · exact hm h'
  · exact hc (hcol p hp)

/-- The Modelled injection rule: under `AlwaysAvailable` or `Bounded(k)`, a call to verify
`QuiescentNameAligned` with a registered environment place that the net declares is refused by
every gate that meets the lines, whichever refusal comes first, so its graph is never built. -/
theorem NU_055_refusal_envQuiescent_refused {R : AlignGateFn} (h : NU_055_refusal R)
    {c : AlignCall} (hq : c.quiescent = true) (hi : c.inj = .modelled)
    (hE : envDeclared c ≠ []) : R c ≠ .build := by
  intro hb
  obtain ⟨-, -, -, -, n5, -, -⟩ := (nu055r_build_iff h c).mp hb
  have h5 : envRule c (envDeclared c) = none := by
    simpa [step5, hi] using n5
  apply hE
  unfold envRule at h5
  split at h5
  · cases h5
  · split at h5
    · cases h5
    · split at h5
      · cases h5
      · simp only [hq, if_true, Option.map_eq_none_iff] at h5
        exact cpFirst_eq_none.mp h5

/-! ### Examples: the search-as-you-type net of the worked example -/

/-- The places of the worked example. -/
def nu055r_places : List String :=
  ["typed", "idle", "armedA", "armedB", "clr", "ready", "listEmpty", "slot", "box", "inflightA",
    "inflightB", "reply", "staged", "list"]

/-- The transitions of the worked example, in the order its table declares them. -/
def nu055r_trans : List String :=
  ["first", "retire", "sendA", "sendB", "fetchA", "fetchB", "apply", "clearNone", "clear", "show"]

/-- The coloured set of the worked example under EXTENDED. -/
def nu055r_coloured : List String :=
  ["box", "inflightA", "inflightB", "list", "reply", "staged"]

/-- A call on the worked example under EXTENDED, with `sendA` and `sendB` declared mints and
`inflightA`, `inflightB`, `list` declared carriers: the property (`q` for the quiescent form), the
list `S`, and the places the initial marking marks. `first` and `retire` consume `typed`; no
environment place is registered. -/
def nu055r_call (q : Bool) (S marked : List String) : AlignCall where
  quiescent := q
  S := S
  stopped := false
  declared := nu055r_places
  marked := marked
  boundedOutside := false
  inFlight := false
  base := false
  fragAll := true
  transitions := nu055r_trans
  undeclared := []
  coloured := nu055r_coloured
  inj := .ignore
  env := []
  inhib := fun _ => []
  consumers := fun p => if p = "typed" then 2 else 1
  conflict := false

/-- The initial marking of the worked example: `typed`, `idle`, `listEmpty`, `slot`. -/
def nu055r_m0 : List String := ["typed", "idle", "listEmpty", "slot"]

/-- AC6 and AC8: `typed` registered as an environment place under `AlwaysAvailable`, and not in
the initial marking. -/
def nu055r_env (q : Bool) (S marked : List String) : AlignCall :=
  { nu055r_call q S marked with inj := .modelled, env := ["typed"] }

/-- AC3: the same net under BASE. The coloured set is the match keys `reply` and `box`, and the
net is outside the BASE fragment even with every transition counted a mint. -/
def nu055r_base : AlignCall :=
  { nu055r_call true ["box", "list"] nu055r_m0 with
    base := true, fragAll := false, coloured := ["box", "reply"] }

/-! ### Violation: no absent-place check (line 1) -/

/-- Step 1 without its absent-place check. -/
def nu055r_step1NoAbsent (c : AlignCall) : Option AlignRefusal :=
  if c.stopped then some .stopped
  else if c.boundedOutside then some .boundedPremise
  else if c.inFlight then some .inFlight else none

/-- A gate that never checks for an absent place. -/
def nu055r_noAbsent : AlignGateFn :=
  gateOf [nu055r_step1NoAbsent, step2, step3, step4, step5, step6, step7]

/-- ✗ A gate without the absent-place check violates line 1: `QuiescentNameAligned(box, nope)`
on the worked example names `nope` as an uncoloured place, where the order asks for the absent
place `nope` of step 1. -/
@[evidence forbids NU_055_refusal]
theorem NU_055_refusal_forbids_noAbsent : ¬ NU_055_refusal nu055r_noAbsent := by
  intro h
  have := (h (nu055r_call true ["box", "nope"] nu055r_m0)).1 (.absent "nope") (by decide)
  revert this
  decide

/-! ### Violation: the places of `S` checked before the fragment (line 2) -/

/-- A gate that checks the places of `S` before the fragment decline. -/
def nu055r_uncolouredFirst : AlignGateFn :=
  gateOf [step1, step6, step2, step3, step4, step5, step7]

/-- ✗ Checking the places of `S` before the fragment violates line 2 (AC3): under BASE,
`QuiescentNameAligned(box, list)` on the worked example is the fragment decline naming EXTENDED;
the gate names `list` as uncoloured instead. -/
@[evidence forbids NU_055_refusal]
theorem NU_055_refusal_forbids_uncolouredFirst : ¬ NU_055_refusal nu055r_uncolouredFirst := by
  intro h
  have := (h nu055r_base).2.1 (by decide) (.outsideFragment true) (by decide)
  revert this
  decide

/-! ### Violation: the arrival refusal after the marked place (line 3) -/

/-- A gate that keeps the arrival refusal for last, after the marked coloured place. -/
def nu055r_arrivalLast : AlignGateFn :=
  gateOf [step1, step2, step4, step5, step6, step7, step3]

/-- The worked example with `typed` and `reply` registered as environment places under
`Arrivals(k)`, the replies arriving from outside, and `box` marked. -/
def nu055r_arrivalCall : AlignCall :=
  { nu055r_call true ["box", "list"] ("box" :: nu055r_m0) with
    inj := .arrivals ["typed", "reply"] }

/-- ✗ Keeping the arrival refusal behind the marked place violates line 3: with the arrivals
feeding `typed` and `reply` and `box` marked, the order names `reply`, the first coloured place
an arrival feeds; the gate names the marked `box`. -/
@[evidence forbids NU_055_refusal]
theorem NU_055_refusal_forbids_arrivalLast : ¬ NU_055_refusal nu055r_arrivalLast := by
  intro h
  have := (h nu055r_arrivalCall).2.2.1 (by decide) (by decide) (.arrival "reply") (by decide)
  revert this
  decide

/-! ### Violation: the environment refusal before the undeclared mints (line 4) -/

/-- A gate that runs step 5 before step 4. -/
def nu055r_envBeforeMints : AlignGateFn :=
  gateOf [step1, step2, step3, step5, step4, step6, step7]

/-- AC6's call with `sendA` and `sendB` not declared as mints. -/
def nu055r_mintCall : AlignCall :=
  { nu055r_env true ["box", "list"] nu055r_m0 with undeclared := ["sendA", "sendB"] }

/-- ✗ Running the environment rule before the mint decline violates line 4: with `typed`
registered and `sendA`, `sendB` undeclared, the order names the two transitions; the gate names
`typed`. -/
@[evidence forbids NU_055_refusal]
theorem NU_055_refusal_forbids_envBeforeMints : ¬ NU_055_refusal nu055r_envBeforeMints := by
  intro h
  have := (h nu055r_mintCall).2.2.2.1 (by decide) (by decide) (by decide)
    (.undeclaredMints ["sendA", "sendB"]) (by decide)
  revert this
  decide

/-! ### Violation: the undeclared mints in some other order (line 4) -/

/-- Step 4 naming the undeclared mints in whatever order the classifier holds them, not in
declaration order. -/
def nu055r_step4any (c : AlignCall) : Option AlignRefusal :=
  if c.undeclared.isEmpty then none else some (.undeclaredMints c.undeclared)

/-- A gate that names the undeclared mints in the order the classifier holds them. -/
def nu055r_mintsAnyOrder : AlignGateFn :=
  gateOf [step1, step2, step3, nu055r_step4any, step5, step6, step7]

/-- The call of `nu055r_mintCall` on a net that declares `sendB` before `sendA`; the classifier
holds them as `sendA`, `sendB`. -/
def nu055r_mintCallBA : AlignCall :=
  { nu055r_mintCall with
    transitions := ["first", "retire", "sendB", "sendA", "fetchA", "fetchB", "apply", "clearNone",
      "clear", "show"] }

/-- ✗ Naming the undeclared mints in any order but the net's violates line 4: on a net that
declares `sendB` before `sendA`, the order names `sendB`, `sendA`; the gate names `sendA`, `sendB`,
the order its classifier happened to hold them in. -/
@[evidence forbids NU_055_refusal]
theorem NU_055_refusal_forbids_mintsAnyOrder : ¬ NU_055_refusal nu055r_mintsAnyOrder := by
  intro h
  have := (h nu055r_mintCallBA).2.2.2.1 (by decide) (by decide) (by decide)
    (.undeclaredMints ["sendB", "sendA"]) (by decide)
  revert this
  decide

/-! ### Violation: the marked place before the environment refusal (line 5) -/

/-- A gate that checks the marked coloured place before the environment places, as the runtimes
do for the other properties, where a marked coloured place sends the call to the flat
pipeline. -/
def nu055r_markedBeforeEnv : AlignGateFn :=
  gateOf [step1, step2, step3, step4, step7, step5, step6]

/-- ✗ The marked place before the environment refusal violates line 5 (AC8, third call): with
`typed` registered under `AlwaysAvailable` and `box` marked, `QuiescentNameAligned(box, list)`
names `typed`; the gate names `box`. -/
@[evidence forbids NU_055_refusal]
theorem NU_055_refusal_forbids_markedBeforeEnv : ¬ NU_055_refusal nu055r_markedBeforeEnv := by
  intro h
  have := (h (nu055r_env true ["box", "list"] ("box" :: nu055r_m0))).2.2.2.2.1 (by decide)
    (by decide) (by decide) (by decide) (.envQuiescent "typed") (by decide)
  revert this
  decide

/-! ### Violation: the uncoloured place in code-point order (line 6) -/

/-- Step 6 read in code-point order instead of the order of `S`. -/
def nu055r_step6cp (c : AlignCall) : Option AlignRefusal :=
  (cpFirst (c.S.filter (fun p => !(decide (p ∈ c.coloured))))).map (fun p => .uncoloured p c.base)

/-- A gate that names the uncoloured place of `S` first in code-point order. -/
def nu055r_uncolouredCp : AlignGateFn :=
  gateOf [step1, step2, step3, step4, step5, nu055r_step6cp, step7]

/-- ✗ Code-point order for the uncoloured place violates line 6 (AC2):
`QuiescentNameAligned(box, ready, clr)` names `ready`, the first uncoloured place in the order of
`S`; the gate names `clr`. -/
@[evidence forbids NU_055_refusal]
theorem NU_055_refusal_forbids_uncolouredCp : ¬ NU_055_refusal nu055r_uncolouredCp := by
  intro h
  have := (h (nu055r_call true ["box", "ready", "clr"] nu055r_m0)).2.2.2.2.2.1 (by decide)
    (by decide) (by decide) (by decide) (by decide) (.uncoloured "ready" false) (by decide)
  revert this
  decide

/-- A gate without step 6: an uncoloured place of `S` reaches the graph, where the predicate
holds on it vacuously. -/
def nu055r_noUncoloured : AlignGateFn :=
  gateOf [step1, step2, step3, step4, step5, step7]

/-- ✗ A gate that lets an uncoloured place through violates line 6 (AC2): on
`QuiescentNameAligned(box, ready)` it builds the graph, which would prove the property while
`ready` carries no name; the order refuses naming `ready`. -/
@[evidence forbids NU_055_refusal]
theorem NU_055_refusal_forbids_noUncoloured : ¬ NU_055_refusal nu055r_noUncoloured := by
  intro h
  have := (h (nu055r_call true ["box", "ready"] nu055r_m0)).2.2.2.2.2.1 (by decide)
    (by decide) (by decide) (by decide) (by decide) (.uncoloured "ready" false) (by decide)
  revert this
  decide

/-- A gate that checks the marked coloured place before the places of `S`. -/
def nu055r_markedFirst : AlignGateFn :=
  gateOf [step1, step2, step3, step4, step5, step7, step6]

/-- ✗ The marked place before the uncoloured one violates line 6 (AC8, first call): with `box`
marked, `QuiescentNameAligned(box, ready)` names the uncoloured `ready`; the gate names `box`. -/
@[evidence forbids NU_055_refusal]
theorem NU_055_refusal_forbids_markedFirst : ¬ NU_055_refusal nu055r_markedFirst := by
  intro h
  have := (h (nu055r_call true ["box", "ready"] ("box" :: nu055r_m0))).2.2.2.2.2.1 (by decide)
    (by decide) (by decide) (by decide) (by decide) (.uncoloured "ready" false) (by decide)
  revert this
  decide

/-! ### Violation: the marked place in the order of the marking (line 7) -/

/-- Step 7 read in the order the initial marking lists its places. -/
def nu055r_step7mk (c : AlignCall) : Option AlignRefusal :=
  (c.marked.find? (fun p => decide (p ∈ c.coloured))).map .markedColoured

/-- A gate that names the marked coloured place in the order of the marking. -/
def nu055r_markedInOrder : AlignGateFn :=
  gateOf [step1, step2, step3, step4, step5, step6, nu055r_step7mk]

/-- ✗ The order of the marking violates line 7 (AC8, second call): with `list` and `inflightB`
marked, in that order, `QuiescentNameAligned(list, box)` names `inflightB`, the first in
code-point order; the gate names `list`. -/
@[evidence forbids NU_055_refusal]
theorem NU_055_refusal_forbids_markedInOrder : ¬ NU_055_refusal nu055r_markedInOrder := by
  intro h
  have := (h (nu055r_call true ["list", "box"] (nu055r_m0 ++ ["list", "inflightB"]))).2.2.2.2.2.2.1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (.markedColoured "inflightB") (by decide)
  revert this
  decide

/-! ### Violation: a gate that never builds (line 8) -/

/-- A gate that refuses every call. -/
def nu055r_neverBuild : AlignGateFn := fun _ => .refuse .inFlight

/-- ✗ Refusing every call violates line 8: `QuiescentNameAligned(box, list)` on the worked example
meets no refusal, and the graph must be built (AC1 decides it `Proven`). -/
@[evidence forbids NU_055_refusal]
theorem NU_055_refusal_forbids_neverBuild : ¬ NU_055_refusal nu055r_neverBuild := by
  intro h
  have := (h (nu055r_call true ["box", "list"] nu055r_m0)).2.2.2.2.2.2.2 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  revert this
  decide

/-! ### Mutants -/

/-- Mutant reading of the refusal order whose line 6 names the uncoloured place of `S` first in
code-point order. -/
def NU_055_refusal_mutant_uncolouredCp (R : AlignGateFn) : Prop :=
  ∀ c : AlignCall,
    (∀ r, step1 c = some r → R c = .refuse r) ∧
    (step1 c = none → ∀ r, step2 c = some r → R c = .refuse r) ∧
    (step1 c = none → step2 c = none → ∀ r, step3 c = some r → R c = .refuse r) ∧
    (step1 c = none → step2 c = none → step3 c = none →
      ∀ r, step4 c = some r → R c = .refuse r) ∧
    (step1 c = none → step2 c = none → step3 c = none → step4 c = none →
      ∀ r, step5 c = some r → R c = .refuse r) ∧
    (step1 c = none → step2 c = none → step3 c = none → step4 c = none → step5 c = none →
      ∀ r, nu055r_step6cp c = some r → R c = .refuse r) ∧
    (step1 c = none → step2 c = none → step3 c = none → step4 c = none → step5 c = none →
      nu055r_step6cp c = none → ∀ r, step7 c = some r → R c = .refuse r) ∧
    (step1 c = none → step2 c = none → step3 c = none → step4 c = none → step5 c = none →
      nu055r_step6cp c = none → step7 c = none → R c = .build)

/-- The code-point gate kills the mutant reading of line 6: it is that reading, so it meets it,
and the refusal order rejects it on `QuiescentNameAligned(box, ready, clr)`
(`NU_055_refusal_forbids_uncolouredCp`). -/
@[evidence mutant NU_055_refusal]
theorem NU_055_refusal_mutant_uncolouredCp_killed :
    NU_055_refusal_mutant_uncolouredCp nu055r_uncolouredCp ∧
      ¬ NU_055_refusal nu055r_uncolouredCp :=
  ⟨fun c => gateOf_lines step1 step2 step3 step4 step5 nu055r_step6cp step7 c,
    NU_055_refusal_forbids_uncolouredCp⟩

/-- Mutant reading of the refusal order whose line 7 names the marked coloured place first in the
order the initial marking lists it. -/
def NU_055_refusal_mutant_markedInOrder (R : AlignGateFn) : Prop :=
  ∀ c : AlignCall,
    (∀ r, step1 c = some r → R c = .refuse r) ∧
    (step1 c = none → ∀ r, step2 c = some r → R c = .refuse r) ∧
    (step1 c = none → step2 c = none → ∀ r, step3 c = some r → R c = .refuse r) ∧
    (step1 c = none → step2 c = none → step3 c = none →
      ∀ r, step4 c = some r → R c = .refuse r) ∧
    (step1 c = none → step2 c = none → step3 c = none → step4 c = none →
      ∀ r, step5 c = some r → R c = .refuse r) ∧
    (step1 c = none → step2 c = none → step3 c = none → step4 c = none → step5 c = none →
      ∀ r, step6 c = some r → R c = .refuse r) ∧
    (step1 c = none → step2 c = none → step3 c = none → step4 c = none → step5 c = none →
      step6 c = none → ∀ r, nu055r_step7mk c = some r → R c = .refuse r) ∧
    (step1 c = none → step2 c = none → step3 c = none → step4 c = none → step5 c = none →
      step6 c = none → nu055r_step7mk c = none → R c = .build)

/-- The marking-order gate kills the mutant reading of line 7: it is that reading, so it meets
it, and the refusal order rejects it on `QuiescentNameAligned(list, box)` with `list` and
`inflightB` marked (`NU_055_refusal_forbids_markedInOrder`). -/
@[evidence mutant NU_055_refusal]
theorem NU_055_refusal_mutant_markedInOrder_killed :
    NU_055_refusal_mutant_markedInOrder nu055r_markedInOrder ∧
      ¬ NU_055_refusal nu055r_markedInOrder :=
  ⟨fun c => gateOf_lines step1 step2 step3 step4 step5 step6 nu055r_step7mk c,
    NU_055_refusal_forbids_markedInOrder⟩

/-- Mutant reading of the refusal order whose line 4 names the undeclared mints in the order the
classifier holds them, not in declaration order. -/
def NU_055_refusal_mutant_mintsAnyOrder (R : AlignGateFn) : Prop :=
  ∀ c : AlignCall,
    (∀ r, step1 c = some r → R c = .refuse r) ∧
    (step1 c = none → ∀ r, step2 c = some r → R c = .refuse r) ∧
    (step1 c = none → step2 c = none → ∀ r, step3 c = some r → R c = .refuse r) ∧
    (step1 c = none → step2 c = none → step3 c = none →
      ∀ r, nu055r_step4any c = some r → R c = .refuse r) ∧
    (step1 c = none → step2 c = none → step3 c = none → nu055r_step4any c = none →
      ∀ r, step5 c = some r → R c = .refuse r) ∧
    (step1 c = none → step2 c = none → step3 c = none → nu055r_step4any c = none →
      step5 c = none → ∀ r, step6 c = some r → R c = .refuse r) ∧
    (step1 c = none → step2 c = none → step3 c = none → nu055r_step4any c = none →
      step5 c = none → step6 c = none → ∀ r, step7 c = some r → R c = .refuse r) ∧
    (step1 c = none → step2 c = none → step3 c = none → nu055r_step4any c = none →
      step5 c = none → step6 c = none → step7 c = none → R c = .build)

/-- The any-order gate kills the mutant reading of line 4: it is that reading, so it meets it, and
the refusal order rejects it on a net that declares `sendB` before `sendA`
(`NU_055_refusal_forbids_mintsAnyOrder`). -/
@[evidence mutant NU_055_refusal]
theorem NU_055_refusal_mutant_mintsAnyOrder_killed :
    NU_055_refusal_mutant_mintsAnyOrder nu055r_mintsAnyOrder ∧
      ¬ NU_055_refusal nu055r_mintsAnyOrder :=
  ⟨fun c => gateOf_lines step1 step2 step3 nu055r_step4any step5 step6 step7 c,
    NU_055_refusal_forbids_mintsAnyOrder⟩

/-! ### Every line exercised -/

/-- Every line of the refusal order is exercised by the shipped gate on the worked example.
Line 1: a call cancelled before it starts is refused for that, even with the absent place `nope`
in `S`; without the stop, `nope` is named. Line 2: under BASE the decline names EXTENDED (AC3).
Line 3: arrivals into `typed` and `reply` name `reply`, the first coloured one. Line 4: with
`sendA` and `sendB` undeclared, the decline names both, in the order the net declares them. Line 5: with `typed` registered under
`AlwaysAvailable`, `QuiescentNameAligned(box, list)` names `typed` (AC6), also with `box` marked
(AC8); `NameAligned(box, list)` does not, as `typed` is not in `S`, and the graph is built; under
conflict priority `typed`, which `first` and `retire` consume, is named as shared; an inhibitor
arc on `typed` in `zeta` and `alpha` names `alpha`. Line 6: `ready` is named on `(box, ready)` and
on `(box, ready, clr)` (AC2), also with `box` marked (AC8). Line 7: with `box` marked, `box` is
named (AC6); with `list` and `inflightB` marked, `inflightB` (AC8). Line 8: with nothing to
refuse, `QuiescentNameAligned(box, list)` reaches the graph. -/
@[evidence nonvacuous NU_055_refusal]
theorem NU_055_refusal_nonvacuous :
    refAlignGate { nu055r_call true ["box", "nope"] nu055r_m0 with stopped := true } =
        .refuse .stopped ∧
      refAlignGate (nu055r_call true ["box", "nope"] nu055r_m0) = .refuse (.absent "nope") ∧
      refAlignGate nu055r_base = .refuse (.outsideFragment true) ∧
      refAlignGate nu055r_arrivalCall = .refuse (.arrival "reply") ∧
      refAlignGate nu055r_mintCall = .refuse (.undeclaredMints ["sendA", "sendB"]) ∧
      refAlignGate nu055r_mintCallBA = .refuse (.undeclaredMints ["sendB", "sendA"]) ∧
      refAlignGate (nu055r_env true ["box", "list"] nu055r_m0) = .refuse (.envQuiescent "typed") ∧
      refAlignGate (nu055r_env true ["box", "list"] ("box" :: nu055r_m0)) =
        .refuse (.envQuiescent "typed") ∧
      refAlignGate (nu055r_env false ["box", "list"] nu055r_m0) = .build ∧
      refAlignGate { nu055r_env true ["box", "list"] nu055r_m0 with conflict := true } =
        .refuse (.envShared "typed") ∧
      refAlignGate { nu055r_env true ["box", "list"] nu055r_m0 with
        inhib := fun p => if p = "typed" then ["zeta", "alpha"] else [] } =
        .refuse (.envInhibitor "typed" "alpha") ∧
      refAlignGate (nu055r_call true ["box", "ready"] nu055r_m0) =
        .refuse (.uncoloured "ready" false) ∧
      refAlignGate (nu055r_call true ["box", "ready", "clr"] nu055r_m0) =
        .refuse (.uncoloured "ready" false) ∧
      refAlignGate (nu055r_call true ["box", "ready"] ("box" :: nu055r_m0)) =
        .refuse (.uncoloured "ready" false) ∧
      refAlignGate (nu055r_call true ["box", "list"] ("box" :: nu055r_m0)) =
        .refuse (.markedColoured "box") ∧
      refAlignGate (nu055r_call true ["list", "box"] (nu055r_m0 ++ ["list", "inflightB"])) =
        .refuse (.markedColoured "inflightB") ∧
      refAlignGate (nu055r_call true ["box", "list"] nu055r_m0) = .build := by
  decide

end Libpetri.Spec
