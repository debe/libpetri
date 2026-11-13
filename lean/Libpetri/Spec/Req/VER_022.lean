import Libpetri.Spec.Verifier.Result
import Libpetri.Spec.Req.VER_014
import Libpetri.Spec.Req.CORE_022
import Mathlib.Data.List.Sort
import Libpetri.Spec.Text.VER_022

set_option linter.missingDocs true
set_option autoImplicit false

/-!
# VER-022: Open-Net Verification Against a Contract (`spec/07-verification.md`)

A subnet is verified on its own: its ports are played by the environment a **contract**
describes, the subnet is closed with that environment, and the closed net is judged against what
the contract guarantees. Three blocks, one per layer:

* `VER_022_meets` (F): when a quiescent marking **meets** the contract. Over a reading
  `M : MeetsRel N` and the rest-set reading `S : StrandRel N` of [VER-014]: every clause's
  upper bound holds, every lower bound holds unless a terminal marker is marked, and no marked
  place is stranded under `S` with the clause, rest and environment places as sinks and each
  terminal as a conditional sink.
* `VER_022_closure` (F): the **closure**. Over a closure function `Cl : CloseFn`: a name the
  closure adds that the subnet already uses is refused, fresh names are not; the closed net's
  transitions are the subnet's, then the environment transitions unchanged, then each arrival
  group's sources' transitions under the fixed names, a source of count 0 left out with its
  transitions; its initial marking is the contract's with the sources filled; its environment
  places are the places only environment transitions touch.
* `VER_022` (B): the **verdict**. Over a firing relation `F`, the closure `Cl`, the meets reading
  `M`, the rest set `S` and a verifier `V : OpenVerifier`: a refused closure is a refused
  verification; `Proven` means every reachable quiescent marking of the closed net meets the
  contract (quiescence reap-aware unless `assumeNoReaping`) and, where termination is required,
  no run fires forever; every confirmed witness of a `Violated` is a firing sequence of the closed
  net to a marking that breaks its part (a lasso for termination); every clause part names a
  clause of the contract; a termination part only when termination is required; an unconfirmed
  witness comes from the SMT route and names no stranded place; an `Unknown` has a reason; a
  closed net with match transitions is never decided by the graph route.

The existence halves (an accepted closure gets a result; a contract that holds on a graph that
closes within the class budget is `Proven`, and a broken one there is `Violated`) are the coverage
condition `Ver022Covers`, never a
line of a block (the convention of `GlossaryExec.lean`), which the reference meets
(`ver022_ref_covers`) and `VER_022_joint` carries.

The witnesses are `refMeets`, `refClose` and `refOpenVerify`, a list-based enumeration of the
closed net (`Reference.succ`), which `decide` evaluates, so the [VER-022] AC11 relay is checked
end to end (`VER_022_nonvacuous`). The SMT route is not modelled: the reference reports
`Unknown` where Rust would ask the SMT pipeline.
-/

namespace Libpetri.Spec.OpenNet

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## The contract -/

/-- An arrival group: between `min` and `max` tokens in total, each onto one of `places`. -/
structure Group (N : Type) where
  /-- The tokens the group must deliver. -/
  min : Nat
  /-- The tokens the group may deliver at most. -/
  max : Nat
  /-- The places a token of the group may land on. -/
  places : List N

/-- A named count clause: at every quiescent marking the tokens across `places` number between
`min` and `max` (`none`: no upper bound). -/
structure Clause (N : Type) where
  /-- The clause's name. -/
  name : String
  /-- The places counted. -/
  places : List N
  /-- The lower bound. -/
  min : Nat
  /-- The upper bound, if any. -/
  max : Option Nat

/-- A designed terminal: while `marker` holds a token, clause lower bounds are waived and the
places `excused` may hold tokens. -/
structure Terminal (N : Type) where
  /-- The marker place. -/
  marker : N
  /-- The places the marked terminal excuses. -/
  excused : List N

/-- An open-net contract ([VER-022]). -/
structure Contract (N : Type) where
  /-- The tokens the subnet holds before anything arrives. -/
  init : List (N × Nat) := []
  /-- The arrival groups, in order. -/
  groups : List (Group N) := []
  /-- The count clauses, in order. -/
  clauses : List (Clause N) := []
  /-- The rest places. -/
  rest : List N := []
  /-- The designed terminals. -/
  terminals : List (Terminal N) := []
  /-- The environment transitions. -/
  env : List (Reference.Trans N) := []
  /-- Whether every run must come to rest (the default) or the contract waives it. -/
  terminate : Bool := true

section Meets

variable {N : Type} [DecidableEq N]

/-! ## Meeting the contract -/

/-- The tokens across a clause's places, each place counted once (`tokens_across`). -/
def clauseSum (c : Clause N) (m : N → Nat) : Nat := (c.places.dedup.map m).sum

/-- A clause holds at `m`: the upper bound always, the lower bound while no terminal marker is
marked. -/
def ClauseHolds (C : Contract N) (c : Clause N) (m : N → Nat) : Prop :=
  (∀ h, c.max = some h → clauseSum c m ≤ h) ∧
    ((∀ τ ∈ C.terminals, m τ.marker = 0) → c.min ≤ clauseSum c m)

/-- The rest set's sinks: the clause places, the rest places and the environment places. -/
def restSinks (C : Contract N) (envs : List N) : List N :=
  C.clauses.flatMap Clause.places ++ C.rest ++ envs

/-- The rest set's conditional sinks: one declaration per designed terminal. -/
def restCond (C : Contract N) : List (CondSinks N) :=
  C.terminals.map fun τ => ⟨τ.marker, τ.excused⟩

/-- A reading of "the quiescent marking `m` meets the contract `C`", given the closed net's
environment places `envs`. -/
abbrev MeetsRel (N : Type) : Type := Contract N → List N → (N → Nat) → Prop

/-- The reference reading (`predicate.rs` `quiescence_findings` is empty): every clause holds,
and no marked place is stranded under the [VER-014] rest set of the contract. -/
def refMeets : MeetsRel N := fun C envs m =>
  (∀ c ∈ C.clauses, ClauseHolds C c m) ∧
    ∀ p, m p ≠ 0 → ¬ refStrand (restSinks C envs) (restCond C) m p

end Meets

#spec_witness refMeets

/-! ## The closure -/

/-- The places an output spec names. -/
def outNames : Out String → List String
  | .place p => [p]
  | .and l r => outNames l ++ outNames r
  | .xor l r => outNames l ++ outNames r
  | .timeout c => outNames c
  | .forward s d => [s, d]

/-- Every place a transition's arcs or output spec name. -/
def transPlaces (t : Reference.Trans String) : List String :=
  t.core.inputs.map NInSpec.place ++ t.core.inhibitors ++ t.core.reads ++ t.core.resets ++
    (match t.out with
     | none => []
     | some o => outNames o)

/-- The subnet's places: the declared ones and every place an arc or output spec names (the
`PetriNet` builder declares those). -/
def netPlaceNames (net : Reference.Net String) : List String :=
  net.places ++ net.transitions.flatMap transPlaces

/-- The subnet's names: its places and its transitions' names. -/
def netNames (net : Reference.Net String) : List String :=
  netPlaceNames net ++ net.transitions.map fun t => t.core.name

/-- `l` without repeats, first occurrence kept. -/
def nub : List String → List String
  | [] => []
  | x :: xs => x :: (nub xs).filter (· ≠ x)

/-- The closed net's environment places: the places an environment transition touches that the
subnet does not, in first-mention order. -/
def envPlacesOf (net : Reference.Net String) (C : Contract String) : List String :=
  nub ((C.env.flatMap transPlaces).filter fun p => p ∉ netPlaceNames net)

/-- The mandatory source of group `i`. -/
def manSrc (i : Nat) : String := s!"env:arrivals[{i}]"
/-- The optional source of group `i`. -/
def optSrc (i : Nat) : String := s!"env:optional[{i}]"
/-- The mandatory arrival of group `i` onto `p`. -/
def arrName (i : Nat) (p : String) : String := s!"env:arrive[{i}]:{p}"
/-- The optional arrival of group `i` onto `p`. -/
def optName (i : Nat) (p : String) : String := s!"env:arrive?[{i}]:{p}"
/-- The decline of group `i`. -/
def declName (i : Nat) : String := s!"env:decline[{i}]"

/-- A transition moving one token from `src` onto `dst` (`none`: discarding it). Immediate, so
never reapable. -/
def moveT (name src : String) (dst : Option String) : Reference.Trans String :=
  { core := { name, inputs := [⟨src, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := dst.map Out.place }

/-- Group `i`'s transitions, in the order `close_open_net` adds them; a source whose count is 0
is left out with its transitions. -/
def groupTrans (i : Nat) (g : Group String) : List (Reference.Trans String) :=
  (if 0 < g.min then g.places.map fun p => moveT (arrName i p) (manSrc i) (some p) else []) ++
    (if g.min < g.max then
      g.places.map (fun p => moveT (optName i p) (optSrc i) (some p)) ++
        [moveT (declName i) (optSrc i) none]
    else [])

/-- Group `i`'s sources with their counts. -/
def groupSources (i : Nat) (g : Group String) : List (String × Nat) :=
  (if 0 < g.min then [(manSrc i, g.min)] else []) ++
    (if g.min < g.max then [(optSrc i, g.max - g.min)] else [])

/-- Group `i`'s names, in the order the closure claims them. -/
def groupNames (i : Nat) (g : Group String) : List String :=
  (if 0 < g.min then manSrc i :: g.places.map (arrName i) else []) ++
    (if g.min < g.max then optSrc i :: (g.places.map (optName i) ++ [declName i]) else [])

/-- Every group's transitions, from index `i` on. -/
def transFrom : Nat → List (Group String) → List (Reference.Trans String)
  | _, [] => []
  | i, g :: gs => groupTrans i g ++ transFrom (i + 1) gs

/-- Every group's sources, from index `i` on. -/
def sourcesFrom : Nat → List (Group String) → List (String × Nat)
  | _, [] => []
  | i, g :: gs => groupSources i g ++ sourcesFrom (i + 1) gs

/-- Every group's names, from index `i` on. -/
def namesFrom : Nat → List (Group String) → List String
  | _, [] => []
  | i, g :: gs => groupNames i g ++ namesFrom (i + 1) gs

/-- The closure's transitions. -/
def closureTrans (C : Contract String) : List (Reference.Trans String) := transFrom 0 C.groups
/-- The closure's sources. -/
def closureSources (C : Contract String) : List (String × Nat) := sourcesFrom 0 C.groups
/-- The closure's names. -/
def closureNames (C : Contract String) : List String := namesFrom 0 C.groups

/-- The environment transitions' names. -/
def envNames (C : Contract String) : List String := C.env.map fun t => t.core.name

/-- Every place the contract names. -/
def contractNamed (C : Contract String) : List String :=
  C.init.map Prod.fst ++ C.groups.flatMap Group.places ++ C.clauses.flatMap Clause.places ++
    C.rest ++ C.terminals.flatMap fun τ => τ.marker :: τ.excused

/-- The contract places neither the subnet nor an environment transition declares. -/
def undeclaredOf (net : Reference.Net String) (C : Contract String) : List String :=
  nub ((contractNamed C).filter fun p => p ∉ netPlaceNames net ∧ p ∉ envPlacesOf net C)

/-- `fresh` of `close_open_net`, run over its calls in order: an entry `(true, n)` claims `n`
and fails when it is taken; an entry `(false, n)` takes `n` unchecked (an environment place). -/
def freshFails : List String → List (Bool × String) → Bool
  | _, [] => false
  | taken, (b, n) :: rest => (b && decide (n ∈ taken)) || freshFails (taken ++ [n]) rest

/-- The closure's claims, in `close_open_net`'s order. -/
def claims (net : Reference.Net String) (C : Contract String) : List (Bool × String) :=
  (envNames C).map (true, ·) ++ (envPlacesOf net C).map (false, ·) ++
    (closureNames C).map (true, ·)

/-- The closed net and what the port trace and the judge read from the closure. -/
structure Closed where
  /-- The closed net. -/
  net : Reference.Net String
  /-- Its initial marking. -/
  m0 : Marking String
  /-- The environment's transitions by name: the contract's, then the closure's. -/
  envSteps : List String
  /-- The environment places. -/
  envPlaces : List String

/-- A closure function: the closed net, or the reason it is refused. -/
abbrev CloseFn : Type := Reference.Net String → Contract String → Except String Closed

/-- The closed net, names unchecked. -/
def closeNet (net : Reference.Net String) (C : Contract String) : Closed :=
  { net := { places := net.places ++ undeclaredOf net C,
             transitions := net.transitions ++ C.env ++ closureTrans C },
    m0 := ofList (C.init ++ closureSources C),
    envSteps := envNames C ++ (closureTrans C).map fun t => t.core.name,
    envPlaces := envPlacesOf net C }

/-- **The reference closure** (`close_open_net`): refused at the first claim of a taken name. -/
def refClose : CloseFn := fun net C =>
  if freshFails (netNames net) (claims net C) then
    .error "VER-022: closing the net would add a name the net already declares"
  else .ok (closeNet net C)

#spec_witness refClose

/-! ## The verifier -/

/-- An open net: the subnet, and whether its closed net declares match (ν-join) transitions,
which the named reference semantics does not model. -/
structure OpenSubnet where
  /-- The subnet. -/
  net : Reference.Net String
  /-- Whether the closed net declares a match transition, in the subnet or in an environment
  transition of the contract: `Reference.Trans` carries no match specification, so this flag
  stands for one. -/
  hasMatch : Bool := false

/-- The options `verify_open_net` reads here. -/
structure OOptions where
  /-- The class budget of the graph route; `0` skips the graph. -/
  maxClasses : Nat := 50000
  /-- Whether the SMT route is asked when the graph does not close. -/
  smt : Bool := true
  /-- Read quiescence strictly ([TIME-013]). -/
  assumeNoReaping : Bool := false

/-- A broken part of the contract. -/
inductive Part where
  /-- The clause of this name. -/
  | clause (name : String)
  /-- These places hold stranded tokens (empty: an unconfirmed SMT stranding). -/
  | stranded (places : List String)
  /-- A run that never comes to rest. -/
  | termination
  deriving DecidableEq, Repr

/-- A witness: the part, the firing sequence from the initial marking (environment steps
included), the marking it ends in, where a termination lasso's cycle starts, and whether the
sequence is a confirmed firing sequence. -/
structure Witness where
  /-- The broken part. -/
  part : Part
  /-- The firing sequence. -/
  trace : List String
  /-- The marking at its end (for a lasso: where the cycle starts and ends). -/
  endM : Marking String
  /-- For a lasso, the index into `trace` where the cycle starts. -/
  cycleStart : Option Nat := none
  /-- Whether `trace` replays as an ordered firing sequence. -/
  confirmed : Bool := true
  deriving DecidableEq, Repr

/-- The verdict. -/
inductive OVerdict where
  /-- Every reachable quiescent marking meets the contract. -/
  | proven
  /-- The broken parts found. -/
  | violated (ws : List Witness)
  /-- Undecided, and why. -/
  | unknown (reason : String)
  deriving DecidableEq, Repr

/-- The deciding route. -/
inductive ORoute where
  /-- The state-class graph. -/
  | enumeration
  /-- The SMT pipeline. -/
  | smt
  deriving DecidableEq, Repr

/-- The result. -/
structure OResult where
  /-- The verdict. -/
  verdict : OVerdict
  /-- The deciding route. -/
  route : ORoute
  deriving DecidableEq, Repr

/-- An open-net verifier: the result, or the reason the verification is refused. -/
abbrev OpenVerifier : Type := OOptions → OpenSubnet → Contract String → Except String OResult

/-- Quiescence as [VER-002] reads it: every enabled transition is reapable, and under
`assumeNoReaping` none may be enabled. -/
def Quiet (o : OOptions) (net : Reference.Net String) (m : String → Nat) : Prop :=
  ∀ t ∈ net.transitions, enabledNA m t.core = true → t.reapable = true ∧ o.assumeNoReaping = false

end Libpetri.Spec.OpenNet

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam Libpetri.Spec.OpenNet

/-! ## VER-022 (F): meeting the contract -/

requirement VER_022_meets
  id "VER-022"
  title "Open-Net Verification Against a Contract: meeting the contract"
  kind F
  scope "the open-net verifier, both routes, all implementations (MAY; the shall sentences bind an implementation that offers open-net verification)"
  source verbatim "spec/07-verification.md"
  covers VER_022.s3, VER_022.s4, VER_022.s1, VER_022.s5
  reading "For every reading M of meeting the contract and every rest-set reading S of VER-014, all contracts C, environment places envs and markings m:"
          "M holds of C, envs and m exactly when every clause's count (each place counted once) is at most its upper bound, every clause's count is at least its lower bound unless some terminal marker is marked, and no marked place is stranded under S with the clause, rest and environment places as sinks and each terminal as a conditional sink."
  assumes "A marking is a count marking by place name; the clause count is the sum over the clause's places, each counted once (`tokens_across`), and an absent upper bound is none. Line 1 holds the rest set as the parameter S, the variable VER-014's statement fixes, so 'implementations MUST decide it through that same predicate' is the line itself: the two blocks hold together of one S (VER_022_joint), and with VER-014's first line the stranding half is the plain list of the quoted definition (VER_022_meets_plain: every token lies on a clause, rest or environment place, a terminal marker, or an excused place of a marked terminal). 'Every other place is internal to the subnet and must be empty' is that list read the other way."
          "The contract's parts (initial marking, arrival groups, named count clauses, rest places, designed terminals, environment transitions, termination flag) are the fields of OpenNet.Contract; the per-language builders and their argument checks (min <= max, a group or clause naming at least one place, distinct clause and environment transition names) are kind N. The environment places envs are the closed net's, which VER_022_closure fixes."
          "AC2 (a clause whose upper bound is exceeded is violated whether or not a terminal is marked; a lower bound is waived while one is) is line 1: a judge that waives the upper bound under a marked terminal is killed (VER_022_meets_forbids_waiveUpper), and so is one that keeps the lower bound under a marked terminal (VER_022_meets_forbids_lowerAlways)."
          "AC3 (a token on a place the contract does not name is reported as stranded, and the report names the place whenever its witness is confirmed, always on the graph route) is line 1 for the judgement: a judge that ignores stranded tokens is killed (VER_022_meets_forbids_ignoreStrand). That a confirmed violation names the place is VER_022's stranded-part line, and that an unconfirmed one names none is its unconfirmed-witness line; that a closed graph with a stranded token is reported Violated at all is the third part of Ver022Covers (VER_022_covers_hideViolated); the report text is kind Q."
          "AC8, second and third sentences (a token left on an environment place is never reported stranded; a place environment transitions share with the subnet is judged like any other) is line 1 with envs the closed net's environment places, which VER_022_closure defines as the places only environment transitions touch: a judge that leaves the environment places out of the sinks is killed (VER_022_meets_forbids_envNotSink)."
  signoff "2026-11-13 4e9af8b142080c49 ai"
  statement : ∀ {N : Type} [DecidableEq N], MeetsRel N → StrandRel N → Prop :=
    fun M S => ∀ C envs m, M C envs m ↔
      (∀ c ∈ C.clauses, ∀ h, c.max = some h → clauseSum c m ≤ h) ∧
      ((∀ τ ∈ C.terminals, m τ.marker = 0) → ∀ c ∈ C.clauses, c.min ≤ clauseSum c m) ∧
      (∀ p, m p ≠ 0 → ¬ S (restSinks C envs) (restCond C) m p)

/- The pinned readable form of VER_022_meets: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.VER_022_meets : {N : Type} → [DecidableEq N] → MeetsRel N → StrandRel N → Prop :=
fun {N} [DecidableEq N] M S =>
  ∀ (C : Contract N) (envs : List N) (m : N → ℕ),
    M C envs m ↔
      (∀ c ∈ C.clauses, ∀ (h : ℕ), c.max = some h → clauseSum c m ≤ h) ∧
        ((∀ τ ∈ C.terminals, m τ.marker = 0) → ∀ c ∈ C.clauses, c.min ≤ clauseSum c m) ∧
          ∀ (p : N), m p ≠ 0 → ¬S (restSinks C envs) (restCond C) m p
-/
#guard_msgs in #print VER_022_meets

/-- ✓ **The reference judge.** Example: a contract with the clause `out = exactly 1` and no
terminal; the marking holding one token on `out` meets it, and the marking holding one token on
`q` breaks the clause and strands `q`. -/
@[evidence holds VER_022_meets]
theorem VER_022_meets_reference {N : Type} [DecidableEq N] :
    VER_022_meets (N := N) refMeets refStrand := by
  intro C envs m
  simp only [refMeets, ClauseHolds]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun c hc => (h1 c hc).1, fun hm c hc => (h1 c hc).2 hm, h2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun c hc => ⟨h1 c hc, fun hm => h2 hm c hc⟩, h3⟩


/-! ## VER-022 (F): the closure -/

requirement VER_022_closure
  id "VER-022"
  title "Open-Net Verification Against a Contract: the closure"
  kind F
  scope "the open-net verifier before either route, all implementations (MAY; the shall sentences bind an implementation that offers open-net verification)"
  source verbatim "spec/07-verification.md"
  covers VER_022.s6, VER_022.s7, VER_022.s8, VER_022.s9, VER_022.s10, VER_022.s11, VER_022.s12,
        VER_022.s13, VER_022.s14
  reading "For every closure function Cl, every subnet net and every contract C:"
          "if the name of an environment transition or a name the closure adds (env:arrivals[i], env:arrive[i]:p, env:optional[i], env:arrive?[i]:p, env:decline[i], for the sources it builds) is a place or transition name of the subnet, Cl refuses;"
          "if those names are pairwise distinct, and none is a name of the subnet or an environment place, Cl does not refuse;"
          "and whenever Cl returns a closed net X:"
          "X's transitions are the subnet's, then the environment transitions, then each group's in order, numbered from 0: per target place, in the group's order, an immediate move of one token from env:arrivals[i] when min > 0, per target place an immediate move of one token from env:optional[i] and the immediate decline when min < max, each with no other arc;"
          "X's initial marking is the contract's initial marking with min on env:arrivals[i] and max - min on env:optional[i] for each source built;"
          "every place of the subnet and every place the contract names is a place of X;"
          "a place is an environment place of X exactly when some environment transition touches it and the subnet does not;"
          "the environment steps of X are the environment transitions' names, then the closure's."
  assumes "The subnet is a Reference.Net over place names (strings); its places are the declared ones and every place an arc or output spec names, as the PetriNet builder declares them. Names are the fixed strings of the spec (`env:arrivals[i]`, `env:optional[i]`, `env:arrive[i]:<place>`, `env:arrive?[i]:<place>`, `env:decline[i]`); the line 'The closure's names (...) and the environment transitions' names MUST NOT collide with the subnet's, and a collision is refused.' is lines 1 and 2. Rust, Java and TypeScript also refuse a closure name equal to an earlier claimed name or to an environment place and accept an environment place equal to an environment transition's name (one `taken` set of places and transitions); line 2's premise covers the first two, the third is kind N. The refusal is a panic (Rust) or an exception (Java, TypeScript), modelled as an error value; its message is kind N."
          "The arrival and decline transitions are moveT: one `one` input arc from the source, the target place as output (none for the decline), no other arc, immediate (never reapable; a closure with reapable arrivals is killed, VER_022_closure_forbids_reapable), as Rust, Java and TypeScript build them (closure.rs arrival_transition, OpenNetClosure.inject, closure.ts: an input arc `one`, an output place, default timing). The initial marking is ofList (C.init ++ sources): a place given twice keeps its last count, as the runtimes' marking builders set rather than add (Rust MarkingStateBuilder::tokens), and an init entry on a source name is overridden by the source; both are kind N. 'The sources are ordinary places, not the environment places of [VER-006], which never run dry and would make every quiescence property hold vacuously.' is line 3 with the reading of VER-022's verdict block, which reads quiescence on the closed net as an ordinary net: a closure that leaves the groups to an injection mode instead of sources is killed (VER_022_closure_forbids_envMode). 'A run is therefore quiescent only once every required arrival has happened and every optional one has been delivered or declined.' follows from line 3 (VER_022_quiescent_sources: at a marking where only reapable transitions are enabled both sources of each group are empty). A source of count 0 is left out with its transitions (ruling D20, VD-5 (4); VER-006: 'exactly as the [VER-022] closure omits it'): a closure that builds both sources always is killed (VER_022_closure_forbids_bothSources)."
          "'Their actions never run, so one that declares outputs gets a placeholder action instead of a [CORE-043] refusal.' is about actions, which the untimed net model does not carry (kind N). The closed net's name `<net>+environment`, the carried terminal places of EXEC-042 and the order of the closed net's declared places are kind N; the terminal rewrite and the in-flight split that run after the closure are EXEC-042's and VER-004's. 'Contract places no arc touches join as places of their own and are listed in the report, so a clause over a place nothing writes counts zero there: a finding, never a refusal.' is line 6 for joining (a closure that leaves them out is killed, VER_022_closure_forbids_noUndeclared) and line 2 for never refusing; that a clause over such a place counts zero is VER_022_meets' clause sum at a marking that leaves the place at 0. That the report lists them (Rust ClosedNet.undeclared in closure.rs, rendered by the open-net report module of libpetri-verification as 'Not declared by the net: ...'; Java opennet/Report.java, TypeScript open-net/report.ts) is report text, kind Q."
          "AC5 (an arrival group that must deliver n tokens reaches quiescence only after all n; one that may deliver at most n also reaches quiescence after fewer) is lines 3 and 4: the mandatory source holds n and every quiescent marking has it empty (VER_022_quiescent_sources), the optional source holds n and may be emptied by declines; a closure without the mandatory source, or with the sources left to injection, is killed (VER_022_closure_forbids_envMode, VER_022_closure_forbids_noSeed), and VER_022_nonvacuous checks both readings end to end (two mandatory arrivals onto q with the clause q = exactly 2 are Proven, two optional ones Violated)."
          "AC8, first sentence (an environment transition's firings are marked as environment steps in the port trace) is line 7: the environment steps are the environment transitions' names, then the closure's; the port trace marks a firing whose name is among them (contract_violation), and its rendering is kind Q. The second and third sentences are VER_022_meets'."
  signoff "2026-11-13 8ea929bede855106 ai"
  statement : CloseFn → Prop :=
    fun Cl => ∀ net C,
      ((∃ n ∈ envNames C ++ closureNames C, n ∈ netNames net) → ∃ e, Cl net C = .error e) ∧
      ((envNames C ++ closureNames C).Nodup →
        (∀ n ∈ envNames C ++ closureNames C, n ∉ netNames net ∧ n ∉ envPlacesOf net C) →
        ∃ X, Cl net C = .ok X) ∧
      ∀ X, Cl net C = .ok X →
        X.net.transitions = net.transitions ++ C.env ++ closureTrans C ∧
        X.m0 = ofList (C.init ++ closureSources C) ∧
        (∀ p ∈ netPlaceNames net ++ contractNamed C, p ∈ netPlaceNames X.net) ∧
        (∀ p, p ∈ X.envPlaces ↔ (∃ t ∈ C.env, p ∈ transPlaces t) ∧ p ∉ netPlaceNames net) ∧
        X.envSteps = envNames C ++ (closureTrans C).map fun t => t.core.name

/- The pinned readable form of VER_022_closure: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.VER_022_closure : CloseFn → Prop :=
fun Cl =>
  ∀ (net : Reference.Net String) (C : Contract String),
    ((∃ n ∈ envNames C ++ closureNames C, n ∈ netNames net) → ∃ e, Cl net C = Except.error e) ∧
      ((envNames C ++ closureNames C).Nodup →
          (∀ n ∈ envNames C ++ closureNames C, n ∉ netNames net ∧ n ∉ envPlacesOf net C) →
            ∃ X, Cl net C = Except.ok X) ∧
        ∀ (X : Closed),
          Cl net C = Except.ok X →
            X.net.transitions = net.transitions ++ C.env ++ closureTrans C ∧
              X.m0 = ofList (C.init ++ closureSources C) ∧
                (∀ p ∈ netPlaceNames net ++ contractNamed C, p ∈ netPlaceNames X.net) ∧
                  (∀ (p : String), p ∈ X.envPlaces ↔ (∃ t ∈ C.env, p ∈ transPlaces t) ∧ p ∉ netPlaceNames net) ∧
                    X.envSteps = envNames C ++ List.map (fun t => t.core.name) (closureTrans C)
-/
#guard_msgs in #print VER_022_closure

namespace OpenNet

theorem mem_nub {x : String} : ∀ {l : List String}, x ∈ nub l ↔ x ∈ l
  | [] => by simp [nub]
  | y :: ys => by
    simp only [nub, List.mem_cons, List.mem_filter, decide_eq_true_eq]
    rw [mem_nub]
    by_cases h : x = y
    · simp [h]
    · simp [h]

theorem freshFails_append : ∀ (taken : List String) (xs ys : List (Bool × String)),
    freshFails taken (xs ++ ys) =
      (freshFails taken xs || freshFails (taken ++ xs.map Prod.snd) ys)
  | taken, [], ys => by simp [freshFails]
  | taken, (b, n) :: xs, ys => by
    simp only [List.cons_append, freshFails, List.map_cons]
    rw [freshFails_append (taken ++ [n]) xs ys]
    simp only [List.append_assoc, List.singleton_append, Bool.or_assoc]

theorem freshFails_checked : ∀ (taken ns : List String),
    freshFails taken (ns.map (true, ·)) = false ↔ ns.Nodup ∧ ∀ n ∈ ns, n ∉ taken
  | taken, [] => by simp [freshFails]
  | taken, n :: ns => by
    simp only [List.map_cons, freshFails, Bool.true_and, Bool.or_eq_false_iff,
      decide_eq_false_iff_not]
    rw [freshFails_checked (taken ++ [n]) ns]
    simp only [List.nodup_cons, List.mem_cons, forall_eq_or_imp, List.mem_append]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨fun h => ?_, h2⟩, h1, fun x hx => fun h => h3 x hx (Or.inl h)⟩
      exact h3 n h (Or.inr (Or.inl rfl))
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      refine ⟨h3, h2, fun x hx h => ?_⟩
      rcases h with h | rfl | h
      · exact h4 x hx h
      · exact h1 hx
      · exact absurd h List.not_mem_nil

theorem freshFails_unchecked : ∀ (taken ns : List String),
    freshFails taken (ns.map (false, ·)) = false
  | taken, [] => by simp [freshFails]
  | taken, n :: ns => by
    simp only [List.map_cons, freshFails, Bool.false_and, Bool.false_or]
    exact freshFails_unchecked _ ns

/-- When the reference closure refuses: exactly at a claim of a taken name. -/
theorem freshFails_claims (net : Reference.Net String) (C : Contract String) :
    freshFails (netNames net) (claims net C) = false ↔
      ((envNames C).Nodup ∧ ∀ n ∈ envNames C, n ∉ netNames net) ∧
      ((closureNames C).Nodup ∧ ∀ n ∈ closureNames C,
        n ∉ netNames net ++ envNames C ++ envPlacesOf net C) := by
  unfold claims
  rw [freshFails_append, freshFails_append, Bool.or_eq_false_iff, Bool.or_eq_false_iff,
    freshFails_checked, freshFails_unchecked, freshFails_checked]
  simp only [List.map_append, List.map_map, Function.comp_def, List.map_id', and_true,
    List.append_assoc]

theorem closeNet_ok {net : Reference.Net String} {C : Contract String} {X : Closed}
    (h : refClose net C = .ok X) : X = closeNet net C := by
  unfold refClose at h
  split at h
  · exact absurd h (by simp)
  · exact (Except.ok.inj h).symm

end OpenNet

/-- ✓ **The reference closure.** Example: the relay `q → relay → out` with one mandatory arrival
on `q` closes to the relay, then `env:arrive[0]:q` taking a token from `env:arrivals[0]`, which
starts with one token; no optional source is built, since `max − min` is 0. -/
@[evidence holds VER_022_closure]
theorem VER_022_closure_reference : VER_022_closure refClose := by
  intro net C
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨n, hn, hnet⟩
    have hT : freshFails (netNames net) (claims net C) = true := by
      by_contra hf
      rw [Bool.not_eq_true, freshFails_claims] at hf
      rcases List.mem_append.mp hn with h | h
      · exact hf.1.2 n h hnet
      · exact hf.2.2 n h (List.mem_append_left _ (List.mem_append_left _ hnet))
    exact ⟨_, by unfold refClose; rw [if_pos hT]⟩
  · intro hnd hfresh
    have hF : freshFails (netNames net) (claims net C) = false := by
      rw [freshFails_claims]
      obtain ⟨hA, hD, hAD⟩ := List.nodup_append.mp hnd
      refine ⟨⟨hA, fun n hn => (hfresh n (List.mem_append_left _ hn)).1⟩, hD,
        fun n hn hmem => ?_⟩
      have hf := hfresh n (List.mem_append_right _ hn)
      rcases List.mem_append.mp hmem with h | h
      · rcases List.mem_append.mp h with h | h
        · exact hf.1 h
        · exact hAD n h n hn rfl
      · exact hf.2 h
    exact ⟨_, by unfold refClose; rw [if_neg (by simp [hF])]⟩
  · intro X hX
    obtain rfl := closeNet_ok hX
    refine ⟨rfl, rfl, ?_, ?_, rfl⟩
    · intro p hp
      simp only [closeNet, netPlaceNames, List.mem_append, List.mem_flatMap] at hp ⊢
      by_cases hn : p ∈ netPlaceNames net
      · simp only [netPlaceNames, List.mem_append, List.mem_flatMap] at hn
        rcases hn with h | ⟨t, ht, hpt⟩
        · exact Or.inl (Or.inl h)
        · exact Or.inr ⟨t, Or.inl (Or.inl ht), hpt⟩
      · rcases hp with h | h
        · exact absurd (by simpa [netPlaceNames] using h) hn
        · by_cases he : p ∈ envPlacesOf net C
          · simp only [envPlacesOf, mem_nub, List.mem_filter, List.mem_flatMap] at he
            obtain ⟨⟨t, ht, hpt⟩, -⟩ := he
            exact Or.inr ⟨t, Or.inl (Or.inr ht), hpt⟩
          · refine Or.inl (Or.inr ?_)
            simp only [undeclaredOf, mem_nub, List.mem_filter, decide_eq_true_eq]
            exact ⟨h, hn, he⟩
    · intro p
      simp only [closeNet, envPlacesOf, mem_nub, List.mem_filter, List.mem_flatMap,
        decide_eq_true_eq]


/-! ## The reference verifier -/

namespace OpenNet

/-- `Canon`, as a Boolean check. -/
def canonB (m : Marking String) : Bool :=
  decide ((m.map Prod.fst).Pairwise (· < ·)) && m.all fun e => e.2 != 0

theorem canonB_canon {m : Marking String} (h : canonB m = true) : Canon m := by
  simp only [canonB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, bne_iff_ne,
    ne_eq] at h
  exact ⟨h.1, h.2⟩

/-- `Quiet`, on a canonical marking. -/
def quietB (o : OOptions) (net : Reference.Net String) (y : Marking String) : Bool :=
  net.transitions.all fun t => !enabledNA (get y) t.core || (t.reapable && !o.assumeNoReaping)

theorem quietB_iff {o : OOptions} {net : Reference.Net String} {y : Marking String} :
    quietB o net y = true ↔ Quiet o net (get y) := by
  simp only [quietB, Quiet, List.all_eq_true]
  refine forall_congr' fun t => forall_congr' fun _ => ?_
  cases enabledNA (get y) t.core <;> cases t.reapable <;> cases o.assumeNoReaping <;> simp

/-- `ClauseHolds`, on a canonical marking. -/
def clauseHoldsB (C : Contract String) (c : Clause String) (y : Marking String) : Bool :=
  (match c.max with
   | none => true
   | some h => decide (clauseSum c (get y) ≤ h)) &&
    (!(C.terminals.all fun τ => decide (get y τ.marker = 0)) ||
      decide (c.min ≤ clauseSum c (get y)))

theorem clauseHoldsB_iff {C : Contract String} {c : Clause String} {y : Marking String} :
    clauseHoldsB C c y = true ↔ ClauseHolds C c (get y) := by
  unfold clauseHoldsB ClauseHolds
  rw [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    imp_iff_not_or]
  refine and_congr ?_ (or_congr ?_ Iff.rfl)
  · cases c.max <;> simp
  · simp [List.all_eq_false]

/-- `refStrand` at the contract's rest set, on a canonical marking. -/
def strandB (C : Contract String) (envs : List String) (y : Marking String) (p : String) : Bool :=
  !(decide (p ∈ restSinks C envs) || (restCond C).any (fun c => decide (c.marker = p)) ||
    (restCond C).any (fun c => decide (get y c.marker ≠ 0) && decide (p ∈ c.places)))

theorem strandB_iff {C : Contract String} {envs : List String} {y : Marking String}
    {p : String} :
    strandB C envs y p = true ↔ refStrand (restSinks C envs) (restCond C) (get y) p := by
  simp [strandB, refStrand, Resting, IsMarker, and_assoc]

/-- `refMeets`, on a canonical marking. -/
def meetsB (C : Contract String) (envs : List String) (y : Marking String) : Bool :=
  C.clauses.all (clauseHoldsB C · y) && y.all fun e => !strandB C envs y e.1

theorem meetsB_iff {C : Contract String} {envs : List String} {y : Marking String}
    (hc : Canon y) : meetsB C envs y = true ↔ refMeets C envs (get y) := by
  simp only [meetsB, refMeets, Bool.and_eq_true, List.all_eq_true, clauseHoldsB_iff,
    Bool.not_eq_true']
  refine and_congr Iff.rfl ⟨fun h p hp hs => ?_, fun h e he => ?_⟩
  · have := h _ (mem_of_get_ne_zero hp)
    rw [strandB_iff.mpr hs] at this
    exact Bool.noConfusion this
  · cases hb : strandB C envs y e.1 with
    | false => rfl
    | true =>
      have hne : get y e.1 ≠ 0 := by rw [get_of_mem hc he]; exact hc.2 e he
      exact absurd (strandB_iff.mp hb) (h e.1 hne)

/-! ### The graph: a list-based enumeration of the closed net -/

/-- A discovered marking with the firing sequence that first reached it. -/
abbrev Node : Type := Marking String × List String

/-- Add a successor `s` of `e` unless its marking is already known. -/
def addSucc (vis : List Node) (e : Node) (acc : List Node) (s : String × Marking String) :
    List Node :=
  if (vis ++ acc).any (fun x => decide (x.1 = s.2)) then acc else acc ++ [(s.2, e.2 ++ [s.1])]

/-- The next breadth-first layer. -/
def newSuccs (net : Reference.Net String) (vis fr : List Node) : List Node :=
  fr.foldl (fun acc e => (succ net e.1).foldl (addSucc vis e) acc) []

/-- Breadth-first exploration: stop when the frontier is empty or `cap` markings are known. -/
def explore (net : Reference.Net String) (cap : Nat) : Nat → List Node → List Node → List Node
  | 0, vis, _ => vis
  | k + 1, vis, fr =>
    if fr.isEmpty || decide (cap ≤ vis.length) then vis
    else explore net cap k (vis ++ newSuccs net vis fr) (newSuccs net vis fr)

/-- The markings the graph route discovers within the class budget `cap`, each with a shortest
firing sequence. -/
def visited (net : Reference.Net String) (m0 : Marking String) (cap : Nat) : List Node :=
  explore net cap cap [(m0, [])] [(m0, [])]

/-- The discovered markings are closed under successors: the graph closed. -/
def closedB (net : Reference.Net String) (vis : List Node) : Bool :=
  vis.all fun e => (succ net e.1).all fun s => decide (s.2 ∈ vis.map Prod.fst)

theorem closed_complete {net : Reference.Net String} {vis : List Node} {m0 : Marking String}
    (hcl : closedB net vis = true) (hcan : ∀ e ∈ vis, Canon e.1) (h0 : m0 ∈ vis.map Prod.fst)
    {f : String → Nat} (hr : Reach net (get m0) f) : ∃ y ∈ vis.map Prod.fst, get y = f := by
  induction hr with
  | refl => exact ⟨m0, h0, rfl⟩
  | tail _ hs ih =>
    obtain ⟨y, hy, hyf⟩ := ih
    obtain ⟨l, hl⟩ := hs
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
    rw [← hyf] at hl
    obtain ⟨m', hm, hg⟩ := succ_complete (hcan e he) hl
    have := (List.all_eq_true.mp ((List.all_eq_true.mp hcl) e he)) (l, m') hm
    exact ⟨m', of_decide_eq_true this, hg⟩

/-! ### Witnesses -/

/-- The replay check of a witness: `tr` leads from `m0` to `y` ([VER-003]). -/
def confirmB (net : Reference.Net String) (m0 y : Marking String) (tr : List String) : Bool :=
  canonB m0 && canonB y && decide (y ∈ replay net tr [m0])

theorem confirmB_run {net : Reference.Net String} {m0 y : Marking String} {tr : List String}
    (h : confirmB net m0 y tr = true) : Run net tr (get m0) (get y) := by
  simp only [confirmB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h0, hy⟩, hm⟩ := h
  have h1 : ∀ m ∈ [m0], Canon m := by simpa using canonB_canon h0
  obtain ⟨m, hm', hr⟩ := (mem_replay_iff tr [m0] h1 (canonB_canon hy)).mp hm
  rw [List.mem_singleton.mp hm'] at hr
  exact hr

/-- The shallowest quiescent marking that breaks clause `c`, as a witness. -/
def clauseWit (o : OOptions) (X : Closed) (C : Contract String) (vis : List Node)
    (c : Clause String) : List Witness :=
  match vis.find? (fun e => quietB o X.net e.1 && !clauseHoldsB C c e.1) with
  | none => []
  | some e =>
    if confirmB X.net X.m0 e.1 e.2 then [{ part := .clause c.name, trace := e.2, endM := e.1 }]
    else []

/-- The places some discovered quiescent marking strands, in code-point order. -/
def strandCands (o : OOptions) (X : Closed) (C : Contract String) (vis : List Node) :
    List String :=
  List.insertionSort (fun a b : String => a ≤ b)
    (nub ((vis.filter fun e => quietB o X.net e.1).flatMap fun e =>
      (e.1.map Prod.fst).filter (strandB C X.envPlaces e.1)))

/-- The shallowest quiescent marking that strands `p`, as a witness. -/
def strandWit (o : OOptions) (X : Closed) (C : Contract String) (vis : List Node) (p : String) :
    List Witness :=
  match vis.find? (fun e => quietB o X.net e.1 && decide (get e.1 p ≠ 0) &&
      strandB C X.envPlaces e.1 p) with
  | none => []
  | some e =>
    if confirmB X.net X.m0 e.1 e.2 then [{ part := .stranded [p], trace := e.2, endM := e.1 }]
    else []

/-! ### Termination: layers of runs and lassos -/

/-- A marking reached by a run, with the run's labels and its markings in order. -/
abbrev PNode : Type := Marking String × List String × List (Marking String)

/-- Keep `x` unless its marking is already in the layer. -/
def ddAdd (acc : List PNode) (x : PNode) : List PNode :=
  if acc.any (fun a => decide (a.1 = x.1)) then acc else acc ++ [x]

/-- The runs one step longer, one per marking. -/
def nextT (net : Reference.Net String) (L : List PNode) : List PNode :=
  (L.flatMap fun e => (succ net e.1).map fun s => (s.2, e.2.1 ++ [s.1], e.2.2 ++ [s.2])).foldl
    ddAdd []

/-- The markings `k` firings from `m0`, each with a run reaching it. -/
def tlayer (net : Reference.Net String) (m0 : Marking String) : Nat → List PNode
  | 0 => [(m0, [], [m0])]
  | k + 1 => nextT net (tlayer net m0 k)

/-- The first pair `i < j` of equal entries. -/
def firstRepeat (ms : List (Marking String)) : Option (Nat × Nat) :=
  (List.range ms.length).findSome? fun j =>
    ((List.range j).find? fun i => decide (ms[i]? = ms[j]?)).map (·, j)

/-- A lasso read off a run that revisits a marking, kept only when its stem and cycle replay. -/
def lassoOf (net : Reference.Net String) (m0 : Marking String) (e : PNode) : Option Witness :=
  match firstRepeat e.2.2 with
  | none => none
  | some (i, j) =>
    match e.2.2[i]? with
    | none => none
    | some z =>
      if canonB m0 && canonB z && !((e.2.1.drop i).take (j - i)).isEmpty &&
          decide (z ∈ replay net (e.2.1.take i) [m0]) &&
          decide (z ∈ replay net ((e.2.1.drop i).take (j - i)) [z]) then
        some { part := .termination, trace := e.2.1.take i ++ (e.2.1.drop i).take (j - i),
               endM := z, cycleStart := some (e.2.1.take i).length }
      else none

/-- A termination witness from the runs of length `D`. -/
def termWit (net : Reference.Net String) (m0 : Marking String) (D : Nat) : List Witness :=
  ((tlayer net m0 D).findSome? (lassoOf net m0)).toList

theorem ddAdd_sup {acc : List PNode} {x y : PNode} (h : x ∈ acc) : x ∈ ddAdd acc y := by
  unfold ddAdd; split
  · exact h
  · exact List.mem_append_left _ h

theorem ddAdd_self (acc : List PNode) (x : PNode) : ∃ x' ∈ ddAdd acc x, x'.1 = x.1 := by
  unfold ddAdd; split
  · rename_i h
    obtain ⟨a, ha, he⟩ := List.any_eq_true.mp h
    exact ⟨a, ha, of_decide_eq_true he⟩
  · exact ⟨x, List.mem_append_right _ (List.mem_singleton_self x), rfl⟩

theorem mem_ddFold : ∀ (L acc : List PNode) (x : PNode), x ∈ L ∨ x ∈ acc →
    ∃ x' ∈ L.foldl ddAdd acc, x'.1 = x.1
  | [], acc, x, h => by
    simp only [List.not_mem_nil, false_or] at h
    exact ⟨x, h, rfl⟩
  | y :: ys, acc, x, h => by
    simp only [List.foldl_cons]
    rcases h with h | hacc
    · rcases List.mem_cons.mp h with rfl | hy
      · obtain ⟨x', hx', he⟩ := ddAdd_self acc x
        obtain ⟨x'', hx'', he'⟩ := mem_ddFold ys _ x' (Or.inr hx')
        exact ⟨x'', hx'', he'.trans he⟩
      · exact mem_ddFold ys _ x (Or.inl hy)
    · exact mem_ddFold ys _ x (Or.inr (ddAdd_sup hacc))

/-- Every run of `k` firings from `m0` ends at a marking of layer `k`. -/
theorem tlayer_run {net : Reference.Net String} {m0 : Marking String} (hc : Canon m0)
    {f : Nat → String → Nat} (h0 : f 0 = get m0)
    (hs : ∀ n, ∃ l, LStep net l (f n) (f (n + 1))) :
    ∀ k, ∃ e ∈ tlayer net m0 k, Canon e.1 ∧ get e.1 = f k
  | 0 => ⟨(m0, [], [m0]), by simp [tlayer], hc, h0.symm⟩
  | k + 1 => by
    obtain ⟨e, he, hce, hge⟩ := tlayer_run hc h0 hs k
    obtain ⟨l, hl⟩ := hs k
    rw [← hge] at hl
    obtain ⟨m', hm', hg'⟩ := succ_complete hce hl
    have hx : ((m', e.2.1 ++ [l], e.2.2 ++ [m']) : PNode) ∈ (tlayer net m0 k).flatMap fun e =>
        (succ net e.1).map fun s => (s.2, e.2.1 ++ [s.1], e.2.2 ++ [s.2]) :=
      List.mem_flatMap.mpr ⟨e, he, List.mem_map.mpr ⟨(l, m'), hm', rfl⟩⟩
    obtain ⟨x', hx', hx1⟩ := mem_ddFold _ [] _ (Or.inl hx)
    refine ⟨x', hx', ?_, ?_⟩
    · rw [hx1]; exact (mem_succ hce hm').1
    · rw [hx1]; exact hg'

/-- An empty layer: no run fires forever. -/
theorem tlayer_nil_terminates {net : Reference.Net String} {m0 : Marking String} (hc : Canon m0)
    {D : Nat} (hD : tlayer net m0 D = []) :
    ¬ ∃ f : Nat → String → Nat, f 0 = get m0 ∧ ∀ n, ∃ l, LStep net l (f n) (f (n + 1)) := by
  rintro ⟨f, h0, hs⟩
  obtain ⟨e, he, -⟩ := tlayer_run hc h0 hs D
  rw [hD] at he
  exact List.not_mem_nil he

theorem lassoOf_sound {net : Reference.Net String} {m0 : Marking String} {e : PNode}
    {w : Witness} (h : lassoOf net m0 e = some w) :
    w.part = .termination ∧ w.confirmed = true ∧
      ∃ k, w.cycleStart = some k ∧ k < w.trace.length ∧
        Run net (w.trace.take k) (get m0) (get w.endM) ∧
        Run net (w.trace.drop k) (get w.endM) (get w.endM) := by
  unfold lassoOf at h
  split at h
  · exact absurd h (by simp)
  · rename_i i j _
    split at h
    · exact absurd h (by simp)
    · rename_i z _
      split at h
      · rename_i hck
        obtain rfl := (Option.some.inj h).symm
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hck
        obtain ⟨⟨⟨⟨h0, hz⟩, hne⟩, hstem⟩, hcyc⟩ := hck
        have c0 : ∀ m ∈ [m0], Canon m := by simpa using canonB_canon h0
        have cz : ∀ m ∈ [z], Canon m := by simpa using canonB_canon hz
        obtain ⟨a, ha, hra⟩ := (mem_replay_iff _ [m0] c0 (canonB_canon hz)).mp hstem
        obtain ⟨b, hb, hrb⟩ := (mem_replay_iff _ [z] cz (canonB_canon hz)).mp hcyc
        rw [List.mem_singleton.mp ha] at hra
        rw [List.mem_singleton.mp hb] at hrb
        refine ⟨rfl, rfl, _, rfl, ?_, ?_, ?_⟩
        · rw [List.length_append]
          have : ((e.2.1.drop i).take (j - i)).length ≠ 0 := by
            intro h0'
            rw [List.length_eq_zero_iff] at h0'
            rw [h0'] at hne
            exact Bool.noConfusion hne
          omega
        · rw [List.take_left' rfl]; exact hra
        · rw [List.drop_left' rfl]; exact hrb
      · exact absurd h (by simp)

theorem termWit_sound {net : Reference.Net String} {m0 : Marking String} {D : Nat} {w : Witness}
    (h : w ∈ termWit net m0 D) :
    w.part = .termination ∧ w.confirmed = true ∧
      ∃ k, w.cycleStart = some k ∧ k < w.trace.length ∧
        Run net (w.trace.take k) (get m0) (get w.endM) ∧
        Run net (w.trace.drop k) (get w.endM) (get w.endM) := by
  unfold termWit at h
  cases hf : (tlayer net m0 D).findSome? (lassoOf net m0) with
  | none => rw [hf] at h; exact absurd h (by simp)
  | some w' =>
    rw [hf] at h
    obtain rfl := List.mem_singleton.mp (by simpa using h)
    obtain ⟨e, -, he⟩ := List.exists_of_findSome?_eq_some hf
    exact lassoOf_sound he

/-! ### The verdict -/

/-- Why the graph did not decide, with the SMT route off or leaving every part undecided
(the reference has no solver). -/
def undecided (o : OOptions) : OResult :=
  if o.smt then
    ⟨.unknown "the state-class graph did not close within the class budget; left undecided by the SMT route: stranding, the clauses and termination", .smt⟩
  else
    ⟨.unknown "the state-class graph did not close within the class budget, and the SMT route is disabled", .enumeration⟩

/-- The graph skipped on a net with match transitions. -/
def skipMatch (o : OOptions) : OResult :=
  if o.smt then
    ⟨.unknown "the state-class graph was skipped: the closed net declares match (ν-join) transitions, which the graph does not model; left undecided by the SMT route: stranding, the clauses and termination", .smt⟩
  else
    ⟨.unknown "the state-class graph was skipped: the closed net declares match (ν-join) transitions, which the graph does not model, and the SMT route is disabled", .enumeration⟩

/-- The graph skipped at class budget 0. -/
def skipBudget (o : OOptions) : OResult :=
  if o.smt then
    ⟨.unknown "the state-class graph was skipped; left undecided by the SMT route: stranding, the clauses and termination", .smt⟩
  else
    ⟨.unknown "the state-class graph was skipped, and the SMT route is disabled", .enumeration⟩

/-- Every violation the graph route finds: clauses in contract order, then stranded places in
code-point order, then termination. -/
def graphWits (o : OOptions) (C : Contract String) (X : Closed) (vis : List Node) :
    List Witness :=
  C.clauses.flatMap (clauseWit o X C vis) ++ (strandCands o X C vis).flatMap (strandWit o X C vis)
    ++ (if C.terminate && !(tlayer X.net X.m0 vis.length).isEmpty then
          termWit X.net X.m0 vis.length
        else [])

/-- The graph closed, every discovered quiescent marking meets the contract and, where
termination is required, no run is as long as the graph has markings. -/
def provenB (o : OOptions) (C : Contract String) (X : Closed) (vis : List Node) : Bool :=
  closedB X.net vis && decide (X.m0 ∈ vis.map Prod.fst) && vis.all (fun e => canonB e.1) &&
    canonB X.m0 && vis.all (fun e => !quietB o X.net e.1 || meetsB C X.envPlaces e.1) &&
    (!C.terminate || (tlayer X.net X.m0 vis.length).isEmpty)

/-- The graph route on the closed net. -/
def graphJudge (o : OOptions) (C : Contract String) (X : Closed) : OResult :=
  if (graphWits o C X (visited X.net X.m0 o.maxClasses)).isEmpty then
    if provenB o C X (visited X.net X.m0 o.maxClasses) then ⟨.proven, .enumeration⟩
    else undecided o
  else ⟨.violated (graphWits o C X (visited X.net X.m0 o.maxClasses)), .enumeration⟩

/-- The verdict on a closed net. -/
def refJudge (o : OOptions) (N : OpenSubnet) (C : Contract String) (X : Closed) : OResult :=
  if N.hasMatch then skipMatch o
  else if o.maxClasses = 0 then skipBudget o
  else graphJudge o C X

/-- **The reference open-net verifier** (`verify_open_net` without the SMT pipeline). -/
def refOpenVerify : OpenVerifier := fun o N C =>
  match refClose N.net C with
  | .error e => .error e
  | .ok X => .ok (refJudge o N C X)

end OpenNet

#spec_witness refOpenVerify

/-! ## VER-022 (B): the verdict -/

requirement VER_022
  id "VER-022"
  title "Open-Net Verification Against a Contract"
  kind B
  scope "the open-net verifier, both routes, all implementations (MAY; the shall sentences bind an implementation that offers open-net verification)"
  source verbatim "spec/07-verification.md"
  covers VER_022.s15, VER_022.s16, VER_022.s2, VER_022.s17, VER_022.s18, VER_022.s19, VER_022.s20,
        VER_022.s21, VER_022.s22, VER_022.s23, VER_022.s24, VER_022.s25, VER_022.s26
  reading "For every firing relation F, closure Cl, meets reading M, rest-set reading S and verifier V, all options o, open subnets N and contracts C:"
          "if Cl refuses N's net under C, V refuses the verification;"
          "and whenever V returns a result r and Cl returns the closed net X:"
          "if r is Proven, every marking reachable in X under F from its initial marking that is quiescent under o (every enabled transition reapable, and none enabled under assumeNoReaping) meets C under M, with X's environment places;"
          "if r is Proven and C requires termination, no infinite sequence of steps of X under F starts at its initial marking;"
          "if r is Violated, its list is not empty; every clause part, confirmed or not, names a clause of C; and each confirmed witness is a firing sequence of X under F from its initial marking: for a clause, to a quiescent marking at which that clause fails; for stranded places (at least one), to a quiescent marking at which each is marked and stranded under S; for termination, a stem to a marking and a cycle from it back to it, split at the reported cycle start, which lies inside the sequence;"
          "a termination part appears only when C requires termination, and an unconfirmed witness comes from the SMT route (r's route is smt) and, if a stranding, names no place;"
          "if r is Unknown, its reason is not empty;"
          "if N declares a match transition and r is Proven or Violated, r's route is the SMT route."
  assumes "The subnet is a Reference.Net over place names, untimed but for whether a transition is reapable (deadline or window timing), which quiescence reads; the closed net X is the value of the closure Cl, the variable VER_022_closure fixes, and M and S are the variables of VER_022_meets and VER-014 (VER_022_joint). Firing sequences and reachability are those of the firing relation F (RunF F, ReachF F); at F = RefFire they are Reference.Run and Reference.Reach, the untimed claim of VER-004, in which each firing is atomic. In the runtimes the verified net is X after the in-flight split of VER-004 (environment transitions staying atomic, their arcs counting as tests) and the terminal rewrite of EXEC-042 (each terminal place of the net inhibits every transition and joins the contract as a designed terminal excusing every place); the block is stated for a subnet with no terminal place and no transition to split, or under assumeAtomicFiring, and those rewrites are VER-004's and EXEC-042's. The sentence on the in-flight split ('The in-flight split of [VER-004] applies to the closed net before the terminal rewrite of [EXEC-042]: the environment transitions stay atomic and their arcs count as tests, and a closed net the split refuses, or one that a declared mint transition ([NU-010]) is not in, is `Unknown` before either route runs.') places these steps and is not a line of this block: the split and the terminal rewrite are VER-004's and EXEC-042's, the mint check is NU-010's, and Rust, Java and TypeScript run all three before either route (verify_open_net in verify_open_net.rs, OpenNetVerifier.java, verify-open-net.ts), answering Unknown on a refused split or a declared mint transition the net does not hold. The mint half is NU_010_unknownMint, whose entry points include open-net verification. The split half is stated by no block: VER_004_split states the split and when it refuses, and VER_003's line 4 makes a refusal Unknown for a decider over closed nets, but the line that a closed net the split refuses is Unknown here needs the closure Cl followed by that split, a cross-model line no block has; the runtime sites above are its evidence. That such an Unknown has a reason is line 6."
          "Both routes decide the untimed claim of VER-004: the graph is built untimed and the SMT route makes every transition immediate after naming the reapable ones. The reference has the graph route only, a list-based enumeration of X (Reference.succ) whose Proven needs the discovered markings closed under successors, and it returns Unknown where the runtimes ask the SMT pipeline, whose phases are oracle-backed (VER-003, VER-015 to VER-020). 'only the absence of violations needs the graph to close' is line 2: a verifier that proves the contract from a truncated graph is killed (VER_022_forbids_eager). That a class with no enabled transition is quiescent whether or not it was expanded, and that a cycle among explored edges is a real cycle, is line 4 read on a witness of a graph that did not close. The SMT route's queries (DeadlockFree with the clause, rest and environment places as sinks and each terminal as a conditional sink; QuiescentCount per clause with every terminal marker as a waiver; the ranking of VER-019 for termination, which bounds every run by r·M0 firings) are VER-002, VER-014 and VER-019 on X; 'Without a ranking termination is undecided, and the report names the firings the marking equation lets repeat.' is report text, kind Q."
          "Termination is read as the absence of an infinite firing sequence from the initial marking; on a finite closed graph that is the absence of a reachable cycle, which the graph route reads. The reference proves termination only when no firing sequence is as long as the number of discovered markings, and reports a lasso only when its stem and cycle replay; that a reachable cycle is always reported when termination is required is the exactness of a closed graph, not a line. 'A cycle of reapable transitions ([TIME-013]) counts too, since a run need not reap them.' is line 3: termination is read on the runs of F, which fire a reapable transition like any other, so reapability counts only where quiescence is read (lines 2 and 4); the graph route of every runtime reports any reachable cycle (graph_route.rs find_cycle), and VER_022_nonvacuous's spin is such a run. 'Violated lists every broken part the deciding route found' is the listing's completeness (kind Q); line 4 asks that what is listed holds. A witness's markings along the sequence are kind Q: the model keeps the end marking (endM) and, for a lasso, the cycle start. 'On the SMT route it is the deciding query's counterexample, which need not be shortest; one that does not replay as an ordered firing sequence ([VER-003]) is marked unconfirmed and names no stranded place.' and the EARS sentence on unconfirmed witnesses are line 5: an unconfirmed witness comes from the SMT route (killed: VER_022_forbids_graphUnconfirmed) and names no stranded place (VER_022_forbids_unconfirmedNamed), and line 4 has every clause part name a clause of the contract, confirmed or not (VER_022_forbids_cry). Its sequence and end marking are the solver's model, which the replay of VER-003 could not order, so no line asks them to be a run, quiescent or breaking: Rust keeps the counterexample's transitions and markings as they come (smt_route.rs read_violation). 'On the graph route a witness is a shortest one, and a termination witness is a lasso that marks where its cycle starts.' is line 4 for the lasso and its cycle start; that a graph witness is a shortest one is VER-017's shortest-trace line on the same graph (the reference's breadth-first exploration records a shortest sequence per marking), not a line here; the per-route attribution of a stranding (one part per place on the graph route, one part naming every stranded place on the SMT route) is kind N."
          "AC1 (a subnet that meets its contract is Proven; with an edge that receives neither of its two places it is Violated, naming that edge's clause, with a port trace ending in the quiescent marking) has an existence half and a safety half. That a subnet meeting its contract is Proven is coverage, never a line (the convention of GlossaryExec.lean): the quoted EARS sentence on an accepted closure is the clause Ver022Covers, whose first part asks a result for every accepted closure, whose second asks Proven when the closed net declares no match transition, its graph closes within a class budget above 0, every reachable quiescent marking meets the contract and, where termination is required, no run fires forever, and whose third asks Violated under the same first three conditions when some reachable quiescent marking does not meet the contract or, where termination is required, some run fires forever. A graph closing within the class budget is read as GraphCloses: the breadth-first enumeration of the closed net's markings, stopped at the budget, is closed under successors; how a runtime counts classes against the budget is kind N. The reference meets Ver022Covers (ver022_ref_covers, carried by VER_022_joint); an always-Unknown verifier, an always-refusing one and one that answers Unknown wherever the reference answers Violated meet every line and fail it (VER_022_covers_unknown, VER_022_covers_refuse, VER_022_covers_hideViolated). The prose 'When the graph closes within the class budget the verdict is exact' is that clause: its second part for Proven, its third part for Violated (a closed graph with a broken contract is reported Violated rather than Unknown), which VER_022_nonvacuous shows on the relay. AC1's Violated answer on the edge that receives neither place is that third part; which clause the witness names and its port trace are the safety half. The safety half is lines 2 and 4: the witness is a firing sequence to the quiescent marking that breaks the clause, environment steps included, and a verifier that drops them is killed (VER_022_forbids_noEnvSteps). The port trace is read off the witness with the environment steps of VER_022_closure and the token changes on contract places (contract_violation); its rendering is kind Q."
          "AC4 (a reachable cycle is a termination violation with a lasso witness when termination is required, and no violation when it is waived) is lines 3, 4 and 5: VER_022_nonvacuous checks spin : p → p (a lasso whose cycle starts at once, and Proven under the waiver); a verifier that skips termination and one that reports it under the waiver are killed (VER_022_forbids_noTermination, VER_022_forbids_alwaysTerminate). That a reachable cycle on a closed graph is reported Violated rather than Unknown is the third part of Ver022Covers, which the reference meets by the pigeonhole (a run as long as the graph has markings revisits one, lassoOf_some)."
          "AC6 (a timed subnet gets the verdict of the untimed, reap-aware claim of VER-004: its class count equals that of the same subnet with every transition immediate, and its verdict equals that subnet's when no transition is reapable or under assumeNoReaping; on the SMT route a ν-net whose timing keeps a transition from firing is judged as if it could) is the model itself: a transition carries no timing but its reapable flag, so the verdict is that of the all-immediate subnet exactly when no flag is set or the option clears them (ruling D20, VD-5 (5)). Class counts are kind Q; the ν half is the SMT route's (VER-012, NU-053), outside the model."
          "AC7 (when the graph does not close the SMT route decides; the result is Unknown, naming the reason, when that route is disabled or leaves a part undecided) is line 6 for the reason: a verifier that gives none is killed (VER_022_forbids_blank). That the SMT route decides is the SMT route's, which the model does not have; that a result comes at all is the first part of Ver022Covers. '`Unknown`: says which parts no route decided, and why.' is that line for the why; that the reason names the class budget, the skipped graph and the undecided parts is kind Q; the reference, having no solver, is Unknown wherever the graph does not decide, as VER_022_nonvacuous shows."
          "AC9 (a closed net with match transitions is not decided by the graph; two independently minted names reaching a join that requires them equal strand both inputs: Violated on the SMT route, never Proven by enumeration, and Unknown naming the skipped graph when the SMT route is disabled) is lines 7 and 6: the reference skips the graph on such a net and returns Unknown naming it (VER_022_nonvacuous); a verifier that runs the graph anyway is killed (VER_022_forbids_matchBlind). 'The graph route MUST NOT run' is read on the result, the only thing a verifier shows: a Proven or Violated never comes from the graph route. Reference.Net carries no match specification, so the flag hasMatch stands for the declaration, whether a transition of the subnet or an environment transition of the contract carries it, as the runtimes test the closed net (verify_open_net in verify_open_net.rs); this reading is kind N; the name-blind graph's two errors and the SMT route's Violated are the ν routes' (VER-012, NU-050, NU-053)."
          "AC10 (places whose locale, UTF-16 and code-point orders differ are listed in code-point order, in the violations of either route and in the quiescent marking the report prints) and the Report order paragraph are kind Q, VER-013's name order: the reference lists stranded parts in code-point order (the order of Lean strings), as VER_022_nonvacuous shows for Zeit and apfel, but the order is not a line."
          "AC11 (the relay q → relay → out with relay at window(3, 5), one arrival on q and the clause out = exactly 1, is Violated on both routes because a late executor reaps the relay and rests with the token on q; with assumeNoReaping it is Proven on both and the report says so) is line 2 with VER_022_nonvacuous: the reference returns both verdicts on the graph route (both are also what Ver022Covers asks, since the relay's graph closes: Violated by its third part, which VER_022_covers_hideViolated checks on the relay, Proven by its second), and a verifier that reads quiescence strictly whatever the option says is killed (VER_022_forbids_plainQuiet). The SMT half is the SMT route's; the report sentence is kind Q. 'The reapable transitions are named on the closed net before the SMT route makes every transition immediate()' is the order of the SMT route (kind N): here reapability is a field of the transition and never changes. 'The option assumeNoReaping restores the plain reading, and the report of a closed net with a reapable transition says which reading the verdict used.' is line 2 for the reading and kind Q for the report."
          "The intro paragraph (a subnet verified in isolation, its ports played by the environment; the composition argument stays with the caller; unlike MOD-051 the contract is judged whole) is the scope of the three blocks. The Cost paragraphs (class counts by arity and by budget, the two SHOULDs on describing cost and budget-blindness, the SMT route's cost), the per-language Implementation notes, the report's byte identity with TypeScript and the CONC-002 restart note of a witness (ruling D8 (b)) are kind Q or N. Ruling D22 (a): VER-022 is MAY, and its shall sentences bind an implementation that offers open-net verification."
  signoff "2026-11-13 29eddd26f288fb70 ai"
  statement : FireRel String → CloseFn → MeetsRel String → StrandRel String → OpenVerifier →
      Prop :=
    fun F Cl M S V => ∀ o N C,
      ((∃ e, Cl N.net C = .error e) → ∃ e, V o N C = .error e) ∧
      ∀ r X, V o N C = .ok r → Cl N.net C = .ok X →
        (r.verdict = .proven → ∀ m, ReachF F X.net (get X.m0) m → Quiet o X.net m →
          M C X.envPlaces m) ∧
        (r.verdict = .proven → C.terminate = true →
          ¬ ∃ f : Nat → String → Nat, f 0 = get X.m0 ∧
            ∀ n, ∃ l, LStepF F X.net l (f n) (f (n + 1))) ∧
        (∀ ws, r.verdict = .violated ws → ws ≠ [] ∧ ∀ w ∈ ws,
          (∀ n, w.part = .clause n → ∃ c ∈ C.clauses, c.name = n ∧ (w.confirmed = true →
            RunF F X.net w.trace (get X.m0) (get w.endM) ∧
              Quiet o X.net (get w.endM) ∧ ¬ ClauseHolds C c (get w.endM))) ∧
          (∀ ps, w.part = .stranded ps → w.confirmed = true →
            ps ≠ [] ∧ RunF F X.net w.trace (get X.m0) (get w.endM) ∧
              Quiet o X.net (get w.endM) ∧
              ∀ p ∈ ps, get w.endM p ≠ 0 ∧
                S (restSinks C X.envPlaces) (restCond C) (get w.endM) p) ∧
          (w.part = .termination → C.terminate = true ∧
            (w.confirmed = true → ∃ k, w.cycleStart = some k ∧ k < w.trace.length ∧
              RunF F X.net (w.trace.take k) (get X.m0) (get w.endM) ∧
              RunF F X.net (w.trace.drop k) (get w.endM) (get w.endM))) ∧
          (w.confirmed = false → r.route = .smt ∧ ∀ ps, w.part = .stranded ps → ps = [])) ∧
        (∀ s, r.verdict = .unknown s → s ≠ "") ∧
        (N.hasMatch = true → r.verdict = .proven ∨ (∃ ws, r.verdict = .violated ws) →
          r.route = .smt)

/- The pinned readable form of VER_022: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.VER_022 : FireRel String → CloseFn → MeetsRel String → StrandRel String → OpenVerifier → Prop :=
fun F Cl M S V =>
  ∀ (o : OOptions) (N : OpenSubnet) (C : Contract String),
    ((∃ e, Cl N.net C = Except.error e) → ∃ e, V o N C = Except.error e) ∧
      ∀ (r : OResult) (X : Closed),
        V o N C = Except.ok r →
          Cl N.net C = Except.ok X →
            (r.verdict = OVerdict.proven →
                ∀ (m : String → ℕ), ReachF F X.net (Reference.get X.m0) m → Quiet o X.net m → M C X.envPlaces m) ∧
              (r.verdict = OVerdict.proven →
                  C.terminate = true →
                    ¬∃ f, f 0 = Reference.get X.m0 ∧ ∀ (n : ℕ), ∃ l, LStepF F X.net l (f n) (f (n + 1))) ∧
                (∀ (ws : List Witness),
                    r.verdict = OVerdict.violated ws →
                      ws ≠ [] ∧
                        ∀ w ∈ ws,
                          (∀ (n : String),
                              w.part = Part.clause n →
                                ∃ c ∈ C.clauses,
                                  c.name = n ∧
                                    (w.confirmed = true →
                                      RunF F X.net w.trace (Reference.get X.m0) (Reference.get w.endM) ∧
                                        Quiet o X.net (Reference.get w.endM) ∧
                                          ¬ClauseHolds C c (Reference.get w.endM))) ∧
                            (∀ (ps : List String),
                                w.part = Part.stranded ps →
                                  w.confirmed = true →
                                    ps ≠ [] ∧
                                      RunF F X.net w.trace (Reference.get X.m0) (Reference.get w.endM) ∧
                                        Quiet o X.net (Reference.get w.endM) ∧
                                          ∀ p ∈ ps,
                                            Reference.get w.endM p ≠ 0 ∧
                                              S (restSinks C X.envPlaces) (restCond C) (Reference.get w.endM) p) ∧
                              (w.part = Part.termination →
                                  C.terminate = true ∧
                                    (w.confirmed = true →
                                      ∃ k,
                                        w.cycleStart = some k ∧
                                          k < w.trace.length ∧
                                            RunF F X.net (List.take k w.trace) (Reference.get X.m0)
                                                (Reference.get w.endM) ∧
                                              RunF F X.net (List.drop k w.trace) (Reference.get w.endM)
                                                (Reference.get w.endM))) ∧
                                (w.confirmed = false →
                                  r.route = ORoute.smt ∧ ∀ (ps : List String), w.part = Part.stranded ps → ps = [])) ∧
                  (∀ (s : String), r.verdict = OVerdict.unknown s → s ≠ "") ∧
                    (N.hasMatch = true →
                      (r.verdict = OVerdict.proven ∨ ∃ ws, r.verdict = OVerdict.violated ws) → r.route = ORoute.smt)
-/
#guard_msgs in #print VER_022

/-- The graph closes within the class budget: the breadth-first enumeration of the closed net's
markings, stopped at `o.maxClasses` markings, is closed under successors. -/
def OpenNet.GraphCloses (o : OOptions) (X : Closed) : Prop :=
  closedB X.net (visited X.net X.m0 o.maxClasses) = true

/-- **The coverage VER-022 asks of a verifier**, never a line of the block (the convention of
`GlossaryExec.lean`: blocks state safety, offers are coverage). (1) Whenever the closure `Cl`
accepts the subnet, `V` returns a result rather than refusing. (2) On a closed net with no match
transition whose graph closes within a class budget above 0, where every reachable quiescent
marking meets the contract under `M` and, if termination is required, no run fires forever, that
result is `Proven`. (3) On such a closed net where some reachable quiescent marking does not meet
the contract under `M` or, if termination is required, some run fires forever, that result is
`Violated`. -/
def Ver022Covers (F : FireRel String) (Cl : CloseFn) (M : MeetsRel String) (V : OpenVerifier) :
    Prop :=
  ∀ o N C X, Cl N.net C = .ok X →
    (∃ r, V o N C = .ok r) ∧
    (N.hasMatch = false → 0 < o.maxClasses → OpenNet.GraphCloses o X →
      (∀ m, ReachF F X.net (get X.m0) m → Quiet o X.net m → M C X.envPlaces m) →
      (C.terminate = true → ¬ ∃ f : Nat → String → Nat, f 0 = get X.m0 ∧
        ∀ n, ∃ l, LStepF F X.net l (f n) (f (n + 1))) →
      ∃ r, V o N C = .ok r ∧ r.verdict = .proven) ∧
    (N.hasMatch = false → 0 < o.maxClasses → OpenNet.GraphCloses o X →
      ((∃ m, ReachF F X.net (get X.m0) m ∧ Quiet o X.net m ∧ ¬ M C X.envPlaces m) ∨
        (C.terminate = true ∧ ∃ f : Nat → String → Nat, f 0 = get X.m0 ∧
          ∀ n, ∃ l, LStepF F X.net l (f n) (f (n + 1)))) →
      ∃ r ws, V o N C = .ok r ∧ r.verdict = .violated ws)


namespace OpenNet

theorem clauseWit_sound {o : OOptions} {X : Closed} {C : Contract String} {vis : List Node}
    {c : Clause String} {w : Witness} (h : w ∈ clauseWit o X C vis c) :
    w.part = .clause c.name ∧ w.confirmed = true ∧ w.cycleStart = none ∧
      Run X.net w.trace (get X.m0) (get w.endM) ∧ Quiet o X.net (get w.endM) ∧
      ¬ ClauseHolds C c (get w.endM) := by
  unfold clauseWit at h
  split at h
  · exact absurd h List.not_mem_nil
  · rename_i e he
    split at h
    · rename_i hc
      obtain rfl := List.mem_singleton.mp h
      have hp := List.find?_some he
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
      refine ⟨rfl, rfl, rfl, confirmB_run hc, quietB_iff.mp hp.1, fun hh => ?_⟩
      rw [clauseHoldsB_iff.mpr hh] at hp
      exact Bool.noConfusion hp.2
    · exact absurd h List.not_mem_nil

theorem strandWit_sound {o : OOptions} {X : Closed} {C : Contract String} {vis : List Node}
    {p : String} {w : Witness} (h : w ∈ strandWit o X C vis p) :
    w.part = .stranded [p] ∧ w.confirmed = true ∧ w.cycleStart = none ∧
      Run X.net w.trace (get X.m0) (get w.endM) ∧ Quiet o X.net (get w.endM) ∧
      get w.endM p ≠ 0 ∧ refStrand (restSinks C X.envPlaces) (restCond C) (get w.endM) p := by
  unfold strandWit at h
  split at h
  · exact absurd h List.not_mem_nil
  · rename_i e he
    split at h
    · rename_i hc
      obtain rfl := List.mem_singleton.mp h
      have hp := List.find?_some he
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
      exact ⟨rfl, rfl, rfl, confirmB_run hc, quietB_iff.mp hp.1.1, hp.1.2, strandB_iff.mp hp.2⟩
    · exact absurd h List.not_mem_nil

/-- Every witness the graph route reports holds up. -/
theorem graphWits_sound {o : OOptions} {C : Contract String} {X : Closed} {vis : List Node}
    {w : Witness} (h : w ∈ graphWits o C X vis) :
    (∀ n, w.part = .clause n → w.confirmed = true →
      ∃ c ∈ C.clauses, c.name = n ∧ Run X.net w.trace (get X.m0) (get w.endM) ∧
        Quiet o X.net (get w.endM) ∧ ¬ ClauseHolds C c (get w.endM)) ∧
    (∀ ps, w.part = .stranded ps → w.confirmed = true →
      ps ≠ [] ∧ Run X.net w.trace (get X.m0) (get w.endM) ∧ Quiet o X.net (get w.endM) ∧
        ∀ p ∈ ps, get w.endM p ≠ 0 ∧ refStrand (restSinks C X.envPlaces) (restCond C) (get w.endM) p) ∧
    (∀ ps, w.part = .stranded ps → w.confirmed = false → ps = []) ∧
    (w.part = .termination → C.terminate = true ∧
      (w.confirmed = true → ∃ k, w.cycleStart = some k ∧ k < w.trace.length ∧
        Run X.net (w.trace.take k) (get X.m0) (get w.endM) ∧
        Run X.net (w.trace.drop k) (get w.endM) (get w.endM))) := by
  unfold graphWits at h
  rcases List.mem_append.mp h with h | h
  · rcases List.mem_append.mp h with h | h
    · obtain ⟨c, hc, hw⟩ := List.mem_flatMap.mp h
      obtain ⟨hpt, hcf, -, hr, hq, hb⟩ := clauseWit_sound hw
      refine ⟨fun n hn _ => ?_, fun ps hps => ?_, fun ps hps => ?_, fun ht => ?_⟩
      · rw [hpt] at hn
        obtain rfl := Part.clause.inj hn
        exact ⟨c, hc, rfl, hr, hq, hb⟩
      · rw [hpt] at hps; exact Part.noConfusion hps
      · rw [hpt] at hps; exact Part.noConfusion hps
      · rw [hpt] at ht; exact Part.noConfusion ht
    · obtain ⟨p, -, hw⟩ := List.mem_flatMap.mp h
      obtain ⟨hpt, hcf, -, hr, hq, hm, hs⟩ := strandWit_sound hw
      refine ⟨fun n hn => ?_, fun ps hps _ => ?_, fun ps _ hcf' => ?_, fun ht => ?_⟩
      · rw [hpt] at hn; exact Part.noConfusion hn
      · rw [hpt] at hps
        obtain rfl := Part.stranded.inj hps
        refine ⟨List.cons_ne_nil _ _, hr, hq, fun q hq' => ?_⟩
        rw [List.mem_singleton.mp hq']
        exact ⟨hm, hs⟩
      · rw [hcf] at hcf'; exact Bool.noConfusion hcf'
      · rw [hpt] at ht; exact Part.noConfusion ht
  · split at h
    · rename_i hterm
      obtain ⟨hpt, hcf, hl⟩ := termWit_sound h
      simp only [Bool.and_eq_true] at hterm
      refine ⟨fun n hn => ?_, fun ps hps => ?_, fun ps hps => ?_, fun _ => ⟨hterm.1, fun _ => hl⟩⟩
      · rw [hpt] at hn; exact Part.noConfusion hn
      · rw [hpt] at hps; exact Part.noConfusion hps
      · rw [hpt] at hps; exact Part.noConfusion hps
    · exact absurd h List.not_mem_nil

/-- A `Proven` of the graph route: every reachable quiescent marking meets the contract and, if
termination is required, no run fires forever. -/
theorem provenB_sound {o : OOptions} {C : Contract String} {X : Closed} {vis : List Node}
    (h : provenB o C X vis = true) :
    (∀ m, Reach X.net (get X.m0) m → Quiet o X.net m → refMeets C X.envPlaces m) ∧
    (C.terminate = true → ¬ ∃ f : Nat → String → Nat, f 0 = get X.m0 ∧
      ∀ n, ∃ l, LStep X.net l (f n) (f (n + 1))) := by
  simp only [provenB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨⟨hcl, h0⟩, hcan⟩, hc0⟩, hmeet⟩, hterm⟩ := h
  have hcan' : ∀ e ∈ vis, Canon e.1 := fun e he => canonB_canon (hcan e he)
  refine ⟨fun m hr hq => ?_, fun ht => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := closed_complete hcl hcan' h0 hr
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
    rcases hmeet e he with hq' | hm
    · exact absurd (quietB_iff.mpr hq) (by rw [hq']; exact Bool.false_ne_true)
    · exact (meetsB_iff (hcan' e he)).mp hm
  · rcases hterm with hf | hl
    · rw [ht] at hf; exact Bool.noConfusion hf
    · exact tlayer_nil_terminates (canonB_canon hc0) hl

theorem undecided_facts {o : OOptions} {R : OResult}
    (hR : R = skipMatch o ∨ R = skipBudget o ∨ R = undecided o) (s : String) :
    R.verdict ≠ .proven ∧ (∀ ws, R.verdict ≠ .violated ws) ∧
      (R.verdict = .unknown s → s ≠ "") := by
  rcases hR with rfl | rfl | rfl <;> simp only [skipMatch, skipBudget, undecided] <;> split <;>
    refine ⟨by simp, by simp, ?_⟩ <;> intro h <;> simp only [OVerdict.unknown.injEq] at h <;>
    subst h <;> simp

theorem graphJudge_route {o : OOptions} {C : Contract String} {X : Closed} :
    (graphJudge o C X).verdict = .proven ∨ (∃ ws, (graphJudge o C X).verdict = .violated ws) →
      (graphJudge o C X).route = .enumeration := by
  unfold graphJudge undecided
  split
  · split
    · intro; rfl
    · split <;> simp
  · intro; rfl

/-! ### Coverage: the graph route proves a contract that holds on a closed graph -/

/-- The position a loop of `i < j` visits at step `n`: up to `j`, then back to `i`. -/
def loopIdx (i j : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => if loopIdx i j n + 1 = j then i else loopIdx i j n + 1

/-- A sequence whose first `j` steps hold and that is back at its `i`-th value at `j` runs
forever. -/
theorem forever_of_loop {α : Type} (R : α → α → Prop) (g : Nat → α) {i j : Nat} (hij : i < j)
    (hstep : ∀ k < j, R (g k) (g (k + 1))) (heq : g j = g i) :
    ∃ f : Nat → α, f 0 = g 0 ∧ ∀ n, R (f n) (f (n + 1)) := by
  have hlt : ∀ n, loopIdx i j n < j := by
    intro n
    induction n with
    | zero => show 0 < j; omega
    | succ n ih => simp only [loopIdx]; split <;> omega
  refine ⟨fun n => g (loopIdx i j n), rfl, fun n => ?_⟩
  have h := hstep (loopIdx i j n) (hlt n)
  show R (g (loopIdx i j n)) (g (if loopIdx i j n + 1 = j then i else loopIdx i j n + 1))
  by_cases he : loopIdx i j n + 1 = j
  · rw [if_pos he]; rw [he, heq] at h; exact h
  · rw [if_neg he]; exact h

/-- A firing sequence, read as the markings it passes through. -/
theorem run_fun {net : Reference.Net String} : ∀ {tr : List String} {a b : String → Nat},
    Run net tr a b → ∃ g : Nat → String → Nat, g 0 = a ∧ g tr.length = b ∧
      ∀ k < tr.length, ∃ l, LStep net l (g k) (g (k + 1))
  | [], a, b, h => by
    cases h
    exact ⟨fun _ => a, rfl, rfl, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | l :: ls, a, b, h => by
    cases h with
    | cons hs hr =>
      obtain ⟨g, h0, hl, hst⟩ := run_fun hr
      refine ⟨fun k => if k = 0 then a else g (k - 1), by simp, by simp [hl], fun k hk => ?_⟩
      cases k with
      | zero => exact ⟨l, by simpa [h0] using hs⟩
      | succ k =>
        obtain ⟨l', h'⟩ := hst k (by simp at hk; omega)
        exact ⟨l', by simpa using h'⟩

/-- A lasso is a run that fires forever: the stem, then the cycle again and again. -/
theorem lasso_forever {net : Reference.Net String} {s c : List String} {a z : String → Nat}
    (hs : Run net s a z) (hc : Run net c z z) (hne : c ≠ []) :
    ∃ f : Nat → String → Nat, f 0 = a ∧ ∀ n, ∃ l, LStep net l (f n) (f (n + 1)) := by
  obtain ⟨g1, h10, h1l, h1s⟩ := run_fun hs
  obtain ⟨g2, h20, h2l, h2s⟩ := run_fun hc
  have hq : 0 < c.length := List.length_pos_iff.mpr hne
  let g : Nat → String → Nat := fun k => if k ≤ s.length then g1 k else g2 (k - s.length)
  have hstep : ∀ k < s.length + c.length, ∃ l, LStep net l (g k) (g (k + 1)) := by
    intro k hk
    by_cases hk1 : k + 1 ≤ s.length
    · simp only [g, if_pos hk1, if_pos (show k ≤ s.length by omega)]
      exact h1s k (by omega)
    · simp only [g, if_neg hk1]
      by_cases hk2 : k = s.length
      · subst hk2
        simp only [le_refl, if_true, h1l, ← h20, show s.length + 1 - s.length = 0 + 1 by omega]
        exact h2s 0 hq
      · simp only [if_neg (show ¬ k ≤ s.length by omega),
          show k + 1 - s.length = (k - s.length) + 1 by omega]
        exact h2s _ (by omega)
  have heq : g (s.length + c.length) = g s.length := by
    simp only [g, if_neg (show ¬ s.length + c.length ≤ s.length by omega), le_refl, if_true,
      Nat.add_sub_cancel_left, h2l, h1l]
  obtain ⟨f, hf0, hf⟩ := forever_of_loop (fun x y => ∃ l, LStep net l x y) g
    (by omega : s.length < s.length + c.length) hstep heq
  exact ⟨f, by rw [hf0]; simp [g, h10], hf⟩

/-! ### The termination layers are runs -/

theorem mem_ddFold_sub : ∀ (L acc : List PNode) (x : PNode), x ∈ L.foldl ddAdd acc →
    x ∈ L ∨ x ∈ acc
  | [], acc, x, h => Or.inr h
  | y :: ys, acc, x, h => by
    simp only [List.foldl_cons] at h
    rcases mem_ddFold_sub ys _ x h with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · unfold ddAdd at h
      split at h
      · exact Or.inr h
      · rcases List.mem_append.mp h with h | h
        · exact Or.inr h
        · exact Or.inl (by rw [List.mem_singleton.mp h]; exact List.mem_cons_self)

/-- Every marking of layer `k` ends a path of `k` successor steps from `m0`. -/
theorem tlayer_path {net : Reference.Net String} {m0 : Marking String} (hc : Canon m0) :
    ∀ k, ∀ e ∈ tlayer net m0 k, ∃ g : Nat → Marking String, g 0 = m0 ∧ g k = e.1 ∧
      (∀ i ≤ k, Canon (g i)) ∧ ∀ i < k, ∃ l, (l, g (i + 1)) ∈ succ net (g i)
  | 0, e, he => by
    simp only [tlayer, List.mem_singleton] at he
    subst he
    exact ⟨fun _ => m0, rfl, rfl, fun _ _ => hc, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | k + 1, e, he => by
    simp only [tlayer, nextT] at he
    rcases mem_ddFold_sub _ [] e he with h | h
    · obtain ⟨e', he', hm⟩ := List.mem_flatMap.mp h
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hm
      obtain ⟨g, h0, hk, hcan, hst⟩ := tlayer_path hc k e' he'
      refine ⟨fun i => if i ≤ k then g i else s.2, by simp [h0], by simp, fun i hi => ?_,
        fun i hi => ?_⟩
      · have hce : Canon e'.1 := hk ▸ hcan k le_rfl
        by_cases h : i ≤ k
        · simp only [if_pos h]; exact hcan i h
        · simp only [if_neg h]
          exact (mem_succ hce (l := s.1) (m' := s.2) hs).1
      · by_cases h : i + 1 ≤ k
        · simp only [if_pos h, if_pos (show i ≤ k by omega)]; exact hst i (by omega)
        · obtain rfl : i = k := by omega
          simp only [le_refl, if_true, Nat.not_succ_le_self, if_false, hk]
          exact ⟨s.1, hs⟩
    · exact absurd h List.not_mem_nil

/-! ### The discovered markings are reachable -/

theorem addSucc_sub {vis : List Node} {e : Node} :
    ∀ (ss : List (String × Marking String)) (acc : List Node) (x : Node),
      x ∈ ss.foldl (addSucc vis e) acc → x ∈ acc ∨ ∃ s ∈ ss, x.1 = s.2
  | [], acc, x, h => Or.inl h
  | s :: ss, acc, x, h => by
    simp only [List.foldl_cons] at h
    rcases addSucc_sub ss _ x h with h | ⟨s', hs', he⟩
    · unfold addSucc at h
      split at h
      · exact Or.inl h
      · rcases List.mem_append.mp h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨s, List.mem_cons_self, by rw [List.mem_singleton.mp h]⟩
    · exact Or.inr ⟨s', List.mem_cons_of_mem _ hs', he⟩

theorem newSuccs_fold_sub {net : Reference.Net String} {vis : List Node} :
    ∀ (fr acc : List Node) (x : Node),
      x ∈ fr.foldl (fun acc e => (succ net e.1).foldl (addSucc vis e) acc) acc →
        x ∈ acc ∨ ∃ e ∈ fr, ∃ s ∈ succ net e.1, x.1 = s.2
  | [], acc, x, h => Or.inl h
  | e :: fr, acc, x, h => by
    simp only [List.foldl_cons] at h
    rcases newSuccs_fold_sub fr _ x h with h | ⟨e', he', hs⟩
    · rcases addSucc_sub _ acc x h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨e, List.mem_cons_self, h⟩
    · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', hs⟩

/-- What the breadth-first exploration keeps: canonical markings reachable from `m0`. -/
def Found (net : Reference.Net String) (m0 : Marking String) (x : Node) : Prop :=
  Canon x.1 ∧ Reach net (get m0) (get x.1)

theorem explore_found {net : Reference.Net String} {m0 : Marking String} {cap : Nat} :
    ∀ (k : Nat) (vis fr : List Node), (∀ x ∈ vis, Found net m0 x) → (∀ x ∈ fr, Found net m0 x) →
      ∀ x ∈ explore net cap k vis fr, Found net m0 x
  | 0, vis, _, hv, _ => by simpa [explore] using hv
  | k + 1, vis, fr, hv, hf => by
    have hn : ∀ x ∈ newSuccs net vis fr, Found net m0 x := by
      intro x hx
      rcases newSuccs_fold_sub fr [] x hx with h | ⟨e, he, s, hs, hxs⟩
      · exact absurd h List.not_mem_nil
      · obtain ⟨hce, hre⟩ := hf e he
        obtain ⟨hc', hl⟩ := mem_succ hce (l := s.1) hs
        exact ⟨hxs ▸ hc', hxs ▸ Relation.ReflTransGen.tail hre ⟨_, hl⟩⟩
    simp only [explore]
    split
    · exact hv
    · exact explore_found k _ _ (fun x hx => by
        rcases List.mem_append.mp hx with h | h
        · exact hv x h
        · exact hn x h) hn

theorem explore_sup {net : Reference.Net String} {cap : Nat} :
    ∀ (k : Nat) (vis fr : List Node), ∀ x ∈ vis, x ∈ explore net cap k vis fr
  | 0, _, _, _, h => by simpa [explore] using h
  | k + 1, vis, fr, x, h => by
    simp only [explore]
    split
    · exact h
    · exact explore_sup k _ _ x (List.mem_append_left _ h)

theorem visited_found {net : Reference.Net String} {m0 : Marking String} {cap : Nat}
    (hc : Canon m0) : ∀ x ∈ visited net m0 cap, Found net m0 x := by
  have h : ∀ x ∈ ([(m0, [])] : List Node), Found net m0 x := by
    intro x hx
    rw [List.mem_singleton.mp hx]
    exact ⟨hc, Relation.ReflTransGen.refl⟩
  exact explore_found cap _ _ h h

theorem visited_init {net : Reference.Net String} {m0 : Marking String} {cap : Nat} :
    m0 ∈ (visited net m0 cap).map Prod.fst :=
  List.mem_map.mpr ⟨(m0, []), explore_sup cap _ _ _ List.mem_cons_self, rfl⟩

theorem canonB_of_canon {m : Marking String} (h : Canon m) : canonB m = true := by
  simp only [canonB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, bne_iff_ne, ne_eq]
  exact ⟨h.1, fun e he => h.2 e he⟩

/-- **The pigeonhole**: on a closed graph with no infinite run, no run is as long as the graph
has markings. -/
theorem tlayer_closed_nil {net : Reference.Net String} {m0 : Marking String} {vis : List Node}
    (hc : Canon m0) (hcl : closedB net vis = true) (hcan : ∀ e ∈ vis, Canon e.1)
    (h0 : m0 ∈ vis.map Prod.fst)
    (hterm : ¬ ∃ f : Nat → String → Nat, f 0 = get m0 ∧ ∀ n, ∃ l, LStep net l (f n) (f (n + 1))) :
    tlayer net m0 vis.length = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro e he
  obtain ⟨g, hg0, -, hgc, hgs⟩ := tlayer_path hc _ e he
  have hreach : ∀ i ≤ vis.length, Reach net (get m0) (get (g i)) := by
    intro i
    induction i with
    | zero => intro _; rw [hg0]; exact Relation.ReflTransGen.refl
    | succ i ih =>
      intro hi
      obtain ⟨l, hl⟩ := hgs i (by omega)
      exact Relation.ReflTransGen.tail (ih (by omega)) ⟨l, (mem_succ (hgc i (by omega)) hl).2⟩
  have hin : ∀ i ≤ vis.length, g i ∈ vis.map Prod.fst := by
    intro i hi
    obtain ⟨y, hy, hyg⟩ := closed_complete hcl hcan h0 (hreach i hi)
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    have := ext (hcan x hx) (hgc i hi) (fun q => congrFun hyg q)
    rw [← this]; exact List.mem_map_of_mem hx
  have hnd : ¬ ((List.range (vis.length + 1)).map g).Nodup := by
    intro hnd
    have hsub : (List.range (vis.length + 1)).map g ⊆ vis.map Prod.fst := by
      intro y hy
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
      exact hin i (by rw [List.mem_range] at hi; omega)
    have := (hnd.subperm hsub).length_le
    simp at this
  have hinj : ¬ ∀ x ∈ List.range (vis.length + 1), ∀ y ∈ List.range (vis.length + 1),
      g x = g y → x = y := fun h => hnd (List.Nodup.map_on h List.nodup_range)
  push Not at hinj
  obtain ⟨a, ha, b, hb, hab, hne⟩ := hinj
  rw [List.mem_range] at ha hb
  have key : ∀ {i j : Nat}, i < j → j ≤ vis.length → g i = g j → False := by
    intro i j hij hj heq
    obtain ⟨f, hf0, hf⟩ := forever_of_loop (fun x y => ∃ l, LStep net l x y)
      (fun k => get (g k)) hij (fun k hk => by
        obtain ⟨l, hl⟩ := hgs k (by omega)
        exact ⟨l, (mem_succ (hgc k (by omega)) hl).2⟩) (by simp only [heq])
    exact hterm ⟨f, by rw [hf0, hg0], hf⟩
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact key h (by omega) hab
  · exact key h (by omega) hab.symm

/-! ### The graph route proves a contract that holds on a closed graph -/

theorem graphWits_confirmed {o : OOptions} {C : Contract String} {X : Closed} {vis : List Node}
    {w : Witness} (h : w ∈ graphWits o C X vis) : w.confirmed = true := by
  unfold graphWits at h
  rcases List.mem_append.mp h with h | h
  · rcases List.mem_append.mp h with h | h
    · obtain ⟨c, -, hw⟩ := List.mem_flatMap.mp h
      exact (clauseWit_sound hw).2.1
    · obtain ⟨p, -, hw⟩ := List.mem_flatMap.mp h
      exact (strandWit_sound hw).2.1
  · split at h
    · exact (termWit_sound h).2.1
    · exact absurd h List.not_mem_nil

theorem graphJudge_proven {o : OOptions} {C : Contract String} {X : Closed} (hc0 : Canon X.m0)
    (hcl : closedB X.net (visited X.net X.m0 o.maxClasses) = true)
    (hmeet : ∀ m, Reach X.net (get X.m0) m → Quiet o X.net m → refMeets C X.envPlaces m)
    (hterm : C.terminate = true → ¬ ∃ f : Nat → String → Nat, f 0 = get X.m0 ∧
      ∀ n, ∃ l, LStep X.net l (f n) (f (n + 1))) :
    graphJudge o C X = ⟨.proven, .enumeration⟩ := by
  have hfound := visited_found (net := X.net) (cap := o.maxClasses) hc0
  have hE : (graphWits o C X (visited X.net X.m0 o.maxClasses)).isEmpty = true := by
    rw [List.isEmpty_iff, List.eq_nil_iff_forall_not_mem]
    intro w hw
    have hcf := graphWits_confirmed hw
    obtain ⟨h1, h2, -, h4⟩ := graphWits_sound hw
    cases hp : w.part with
    | clause n =>
      obtain ⟨c, hc, -, hr, hq, hb⟩ := h1 n hp hcf
      exact hb ((hmeet _ (Reference.run_reach hr) hq).1 c hc)
    | stranded ps =>
      obtain ⟨hne, hr, hq, hps⟩ := h2 ps hp hcf
      obtain ⟨p, hp'⟩ := List.exists_mem_of_ne_nil _ hne
      obtain ⟨hm, hs⟩ := hps p hp'
      exact (hmeet _ (Reference.run_reach hr) hq).2 p hm hs
    | termination =>
      obtain ⟨ht, hl⟩ := h4 hp
      obtain ⟨k, -, hk, hr1, hr2⟩ := hl hcf
      refine hterm ht (lasso_forever hr1 hr2 ?_)
      intro hnil
      rw [List.drop_eq_nil_iff] at hnil
      omega
  have hP : provenB o C X (visited X.net X.m0 o.maxClasses) = true := by
    simp only [provenB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
      Bool.not_eq_true', List.isEmpty_iff]
    refine ⟨⟨⟨⟨⟨hcl, visited_init⟩, fun e he => canonB_of_canon (hfound e he).1⟩,
      canonB_of_canon hc0⟩, fun e he => ?_⟩, ?_⟩
    · cases hq : quietB o X.net e.1 with
      | false => exact Or.inl rfl
      | true =>
        exact Or.inr ((meetsB_iff (hfound e he).1).mpr
          (hmeet _ (hfound e he).2 (quietB_iff.mp hq)))
    · cases ht : C.terminate with
      | false => exact Or.inl rfl
      | true =>
        exact Or.inr (tlayer_closed_nil hc0 hcl (fun e he => (hfound e he).1) visited_init
          (hterm ht))
  unfold graphJudge
  rw [if_pos hE, if_pos hP]

/-! ### The graph route reports a violation that a closed graph holds -/

/-- A firing sequence and one more step. -/
theorem vrun_snoc {net : Reference.Net String} : ∀ {tr : List String} {l : String}
    {a b c : String → Nat}, Run net tr a b → LStep net l b c → Run net (tr ++ [l]) a c
  | [], _, _, _, _, h, hs => by cases h; exact Run.cons hs (Run.nil _)
  | _ :: _, _, _, _, _, h, hs => by
    cases h with
    | cons h1 hr => exact Run.cons h1 (vrun_snoc hr hs)

theorem addSucc_trace {vis : List Node} {e : Node} :
    ∀ (ss : List (String × Marking String)) (acc : List Node) (x : Node),
      x ∈ ss.foldl (addSucc vis e) acc → x ∈ acc ∨ ∃ s ∈ ss, x = (s.2, e.2 ++ [s.1])
  | [], acc, x, h => Or.inl h
  | s :: ss, acc, x, h => by
    simp only [List.foldl_cons] at h
    rcases addSucc_trace ss _ x h with h | ⟨s', hs', he⟩
    · unfold addSucc at h
      split at h
      · exact Or.inl h
      · rcases List.mem_append.mp h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨s, List.mem_cons_self, List.mem_singleton.mp h⟩
    · exact Or.inr ⟨s', List.mem_cons_of_mem _ hs', he⟩

theorem newSuccs_fold_trace {net : Reference.Net String} {vis : List Node} :
    ∀ (fr acc : List Node) (x : Node),
      x ∈ fr.foldl (fun acc e => (succ net e.1).foldl (addSucc vis e) acc) acc →
        x ∈ acc ∨ ∃ e ∈ fr, ∃ s ∈ succ net e.1, x = (s.2, e.2 ++ [s.1])
  | [], acc, x, h => Or.inl h
  | e :: fr, acc, x, h => by
    simp only [List.foldl_cons] at h
    rcases newSuccs_fold_trace fr _ x h with h | ⟨e', he', hs⟩
    · rcases addSucc_trace _ acc x h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨e, List.mem_cons_self, h⟩
    · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', hs⟩

/-- What the breadth-first exploration keeps, with its trace: a canonical marking and a firing
sequence from `m0` to it. -/
def FoundT (net : Reference.Net String) (m0 : Marking String) (x : Node) : Prop :=
  Canon x.1 ∧ Run net x.2 (get m0) (get x.1)

theorem explore_foundT {net : Reference.Net String} {m0 : Marking String} {cap : Nat} :
    ∀ (k : Nat) (vis fr : List Node), (∀ x ∈ vis, FoundT net m0 x) →
      (∀ x ∈ fr, FoundT net m0 x) → ∀ x ∈ explore net cap k vis fr, FoundT net m0 x
  | 0, vis, _, hv, _ => by simpa [explore] using hv
  | k + 1, vis, fr, hv, hf => by
    have hn : ∀ x ∈ newSuccs net vis fr, FoundT net m0 x := by
      intro x hx
      rcases newSuccs_fold_trace fr [] x hx with h | ⟨e, he, s, hs, rfl⟩
      · exact absurd h List.not_mem_nil
      · obtain ⟨hce, hre⟩ := hf e he
        obtain ⟨hc', hl⟩ := mem_succ hce (l := s.1) (m' := s.2) hs
        exact ⟨hc', vrun_snoc hre hl⟩
    simp only [explore]
    split
    · exact hv
    · exact explore_foundT k _ _ (fun x hx => by
        rcases List.mem_append.mp hx with h | h
        · exact hv x h
        · exact hn x h) hn

theorem visited_foundT {net : Reference.Net String} {m0 : Marking String} {cap : Nat}
    (hc : Canon m0) : ∀ x ∈ visited net m0 cap, FoundT net m0 x := by
  have h : ∀ x ∈ ([(m0, [])] : List Node), FoundT net m0 x := by
    intro x hx
    rw [List.mem_singleton.mp hx]
    exact ⟨hc, Run.nil _⟩
  exact explore_foundT cap _ _ h h

/-- A discovered marking's trace replays. -/
theorem confirmB_of_foundT {net : Reference.Net String} {m0 : Marking String} {x : Node}
    (hc : Canon m0) (h : FoundT net m0 x) : confirmB net m0 x.1 x.2 = true := by
  obtain ⟨hcx, hr⟩ := h
  simp only [confirmB, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨canonB_of_canon hc, canonB_of_canon hcx⟩,
    (mem_replay_iff x.2 [m0] (by simpa using hc) hcx).mpr ⟨m0, List.mem_singleton_self _, hr⟩⟩

/-- On a closed graph, a reachable quiescent marking that does not meet the contract gives the
graph route a witness. -/
theorem graphWits_meets {o : OOptions} {C : Contract String} {X : Closed} {vis : List Node}
    (hc0 : Canon X.m0) (hcl : closedB X.net vis = true) (hft : ∀ x ∈ vis, FoundT X.net X.m0 x)
    (h0 : X.m0 ∈ vis.map Prod.fst) {m : String → Nat} (hr : Reach X.net (get X.m0) m)
    (hq : Quiet o X.net m) (hb : ¬ refMeets C X.envPlaces m) : graphWits o C X vis ≠ [] := by
  obtain ⟨y, hy, rfl⟩ := closed_complete hcl (fun e he => (hft e he).1) h0 hr
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
  have hqe : quietB o X.net e.1 = true := quietB_iff.mpr hq
  intro hnil
  unfold graphWits at hnil
  rw [List.append_eq_nil_iff, List.append_eq_nil_iff] at hnil
  obtain ⟨⟨h1, h2⟩, -⟩ := hnil
  rcases not_and_or.mp hb with hb | hb
  · obtain ⟨c, hc, hnc⟩ : ∃ c ∈ C.clauses, ¬ ClauseHolds C c (get e.1) := by
      by_contra hno
      exact hb fun c hc => by_contra fun h => hno ⟨c, hc, h⟩
    have hw : clauseWit o X C vis c ≠ [] := by
      unfold clauseWit
      split
      · rename_i hf
        have := List.find?_eq_none.mp hf e he
        have hcb : clauseHoldsB C c e.1 = false :=
          Bool.eq_false_iff.mpr fun h => hnc (clauseHoldsB_iff.mp h)
        simp [hqe, hcb] at this
      · rename_i e' hf
        rw [if_pos (confirmB_of_foundT hc0 (hft e' (List.mem_of_find?_eq_some hf)))]
        simp
    exact hw (List.flatMap_eq_nil_iff.mp h1 c hc)
  · obtain ⟨p, hp, hs⟩ : ∃ p, get e.1 p ≠ 0 ∧
        refStrand (restSinks C X.envPlaces) (restCond C) (get e.1) p := by
      by_contra hno
      exact hb fun p hp hs => hno ⟨p, hp, hs⟩
    have hpc : p ∈ strandCands o X C vis := by
      unfold strandCands
      rw [List.mem_insertionSort, mem_nub]
      exact List.mem_flatMap.mpr ⟨e, List.mem_filter.mpr ⟨he, hqe⟩,
        List.mem_filter.mpr ⟨List.mem_map.mpr ⟨_, mem_of_get_ne_zero hp, rfl⟩,
          strandB_iff.mpr hs⟩⟩
    have hw : strandWit o X C vis p ≠ [] := by
      unfold strandWit
      split
      · rename_i hf
        have := List.find?_eq_none.mp hf e he
        simp [hqe, hp, strandB_iff.mpr hs] at this
      · rename_i e' hf
        rw [if_pos (confirmB_of_foundT hc0 (hft e' (List.mem_of_find?_eq_some hf)))]
        simp
    exact hw (List.flatMap_eq_nil_iff.mp h2 p hpc)

/-- A run of layer `k`: its labels and markings line up, and every stretch of it is a firing
sequence. -/
def Chain (net : Reference.Net String) (m0 : Marking String) (k : Nat) (e : PNode) : Prop :=
  e.2.1.length = k ∧ e.2.2.length = k + 1 ∧ e.2.2[0]? = some m0 ∧ e.2.2[k]? = some e.1 ∧
    (∀ (i : Nat) (x : Marking String), e.2.2[i]? = some x → Canon x) ∧
    ∀ (a b : Nat) (x y : Marking String), a ≤ b → e.2.2[a]? = some x → e.2.2[b]? = some y →
      Run net ((e.2.1.drop a).take (b - a)) (get x) (get y)

theorem tlayer_chain {net : Reference.Net String} {m0 : Marking String} (hc : Canon m0) :
    ∀ k, ∀ e ∈ tlayer net m0 k, Chain net m0 k e
  | 0, e, he => by
    simp only [tlayer, List.mem_singleton] at he
    subst he
    refine ⟨rfl, rfl, rfl, rfl, fun i x hx => ?_, fun a b x y _ hx hy => ?_⟩
    · cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        exact hx ▸ hc
      | succ i => simp at hx
    · cases a with
      | succ a => simp at hx
      | zero =>
        cases b with
        | succ b => simp at hy
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hy
          subst hx hy
          exact Run.nil _
  | k + 1, e, he => by
    simp only [tlayer, nextT] at he
    rcases mem_ddFold_sub _ [] e he with h | h
    · obtain ⟨e', he', hm⟩ := List.mem_flatMap.mp h
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hm
      obtain ⟨hl1, hl2, h0, hk, hcan, hrun⟩ := tlayer_chain hc k e' he'
      have hce : Canon e'.1 := hcan k e'.1 hk
      obtain ⟨hcs, hst⟩ := mem_succ hce (l := s.1) (m' := s.2) hs
      have hget : ∀ i x, (e'.2.2 ++ [s.2])[i]? = some x →
          (i < k + 1 ∧ e'.2.2[i]? = some x) ∨ (i = k + 1 ∧ x = s.2) := by
        intro i x hx
        rw [List.getElem?_append, hl2] at hx
        split at hx
        · exact Or.inl ⟨by assumption, hx⟩
        · rename_i hi
          obtain ⟨n, hn⟩ : ∃ n, i - (k + 1) = n := ⟨_, rfl⟩
          rw [hn] at hx
          cases n with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
            exact Or.inr ⟨by omega, hx.symm⟩
          | succ n => simp at hx
      unfold Chain
      dsimp only
      refine ⟨by simp [hl1], by simp [hl2], ?_, ?_, fun i x hx => ?_, fun a b x y hab hx hy => ?_⟩
      · rw [List.getElem?_append, hl2, if_pos (by omega)]; exact h0
      · rw [List.getElem?_append, hl2, if_neg (by omega)]; simp
      · rcases hget i x hx with ⟨-, h⟩ | ⟨-, rfl⟩
        · exact hcan i x h
        · exact hcs
      · rcases hget b y hy with ⟨hb, hy'⟩ | ⟨rfl, rfl⟩
        · have hx' : e'.2.2[a]? = some x := by
            rcases hget a x hx with ⟨-, h⟩ | ⟨ha, -⟩
            · exact h
            · omega
          rw [List.drop_append_of_le_length (by omega),
            List.take_append_of_le_length (by rw [List.length_drop, hl1]; omega)]
          exact hrun a b x y hab hx' hy'
        · rcases hget a x hx with ⟨ha, hx'⟩ | ⟨rfl, rfl⟩
          · have hlen : (e'.2.1.drop a ++ [s.1]).length ≤ k + 1 - a := by
              simp only [List.length_append, List.length_drop, hl1, List.length_singleton]
              omega
            rw [List.drop_append_of_le_length (by omega), List.take_of_length_le hlen]
            have := hrun a k x e'.1 (by omega) hx' hk
            rw [List.take_of_length_le (by rw [List.length_drop, hl1])] at this
            exact vrun_snoc this hst
          · simp only [Nat.sub_self, List.take_zero]
            exact Run.nil _
    · exact absurd h List.not_mem_nil

/-- **The pigeonhole, the other way**: on a closed graph, a run as long as the graph has markings
revisits one, and its lasso replays. -/
theorem lassoOf_some {net : Reference.Net String} {m0 : Marking String} {vis : List Node}
    (hc : Canon m0) (hcl : closedB net vis = true) (hcan : ∀ e ∈ vis, Canon e.1)
    (h0 : m0 ∈ vis.map Prod.fst) {e : PNode} (he : e ∈ tlayer net m0 vis.length) :
    ∃ w, lassoOf net m0 e = some w := by
  obtain ⟨hl1, hl2, h0', -, hcanE, hrun⟩ := tlayer_chain hc _ e he
  have hsub : e.2.2 ⊆ vis.map Prod.fst := by
    intro x hx
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
    have hr : Reach net (get m0) (get x) :=
      Reference.run_reach (hrun 0 i m0 x (Nat.zero_le _) h0' hi)
    obtain ⟨y, hy, hyg⟩ := closed_complete hcl hcan h0 hr
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    have := ext (hcan z hz) (hcanE i x hi) (fun q => congrFun hyg q)
    rw [← this]; exact List.mem_map_of_mem hz
  have hnd : ¬ e.2.2.Nodup := fun hnd => by
    have := (hnd.subperm hsub).length_le
    simp only [List.length_map, hl2] at this
    omega
  have hfr : ∃ i j, firstRepeat e.2.2 = some (i, j) := by
    cases hf : firstRepeat e.2.2 with
    | some p => exact ⟨p.1, p.2, rfl⟩
    | none =>
      exfalso
      apply hnd
      rw [List.nodup_iff_getElem?_ne_getElem?]
      intro i j hij hj heq
      unfold firstRepeat at hf
      have := List.findSome?_eq_none_iff.mp hf j (List.mem_range.mpr hj)
      rw [Option.map_eq_none_iff, List.find?_eq_none] at this
      exact this i (List.mem_range.mpr hij) (decide_eq_true heq)
  obtain ⟨i, j, hij⟩ := hfr
  have hsound : i < j ∧ j < e.2.2.length ∧ e.2.2[i]? = e.2.2[j]? := by
    have hij' := hij
    unfold firstRepeat at hij'
    obtain ⟨j', hj', hm⟩ := List.exists_of_findSome?_eq_some hij'
    obtain ⟨i', hi', hp⟩ := Option.map_eq_some_iff.mp hm
    have hp' : i' = i ∧ j' = j := by simpa using hp
    obtain ⟨hi1, hj1⟩ := hp'
    subst hi1 hj1
    have hpi := List.find?_some hi'
    simp only [decide_eq_true_eq] at hpi
    exact ⟨List.mem_range.mp (List.mem_of_find?_eq_some hi'), List.mem_range.mp hj', hpi⟩
  obtain ⟨hlt, hjl, heq⟩ := hsound
  cases hz : e.2.2[i]? with
  | none => rw [List.getElem?_eq_none_iff] at hz; omega
  | some z =>
    have hzj : e.2.2[j]? = some z := heq ▸ hz
    have hstem := hrun 0 i m0 z (Nat.zero_le _) h0' hz
    simp only [List.drop_zero, Nat.sub_zero] at hstem
    have hcyc := hrun i j z z hlt.le hz hzj
    have hcz := hcanE i z hz
    have hcond : (canonB m0 && canonB z && !((e.2.1.drop i).take (j - i)).isEmpty &&
        decide (z ∈ replay net (e.2.1.take i) [m0]) &&
        decide (z ∈ replay net ((e.2.1.drop i).take (j - i)) [z])) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
      refine ⟨⟨⟨⟨canonB_of_canon hc, canonB_of_canon hcz⟩, ?_⟩,
        (mem_replay_iff _ [m0] (by simpa using hc) hcz).mpr ⟨m0, List.mem_singleton_self _, hstem⟩⟩,
        (mem_replay_iff _ [z] (by simpa using hcz) hcz).mpr ⟨z, List.mem_singleton_self _, hcyc⟩⟩
      cases hL : (e.2.1.drop i).take (j - i) with
      | nil =>
        have := congrArg List.length hL
        simp only [List.length_take, List.length_drop, hl1, List.length_nil] at this
        omega
      | cons _ _ => rfl
    simp only [lassoOf, hij, hz]
    rw [if_pos hcond]
    exact ⟨_, rfl⟩

/-- On a closed graph, a run that fires forever gives the graph route a termination witness. -/
theorem graphWits_term {o : OOptions} {C : Contract String} {X : Closed} {vis : List Node}
    (hc0 : Canon X.m0) (hcl : closedB X.net vis = true) (hcan : ∀ e ∈ vis, Canon e.1)
    (h0 : X.m0 ∈ vis.map Prod.fst) (ht : C.terminate = true)
    (hf : ∃ f : Nat → String → Nat, f 0 = get X.m0 ∧ ∀ n, ∃ l, LStep X.net l (f n) (f (n + 1))) :
    graphWits o C X vis ≠ [] := by
  obtain ⟨f, hf0, hs⟩ := hf
  obtain ⟨e, he, -⟩ := tlayer_run hc0 hf0 hs vis.length
  obtain ⟨w, hw⟩ := lassoOf_some hc0 hcl hcan h0 he
  have hne : (tlayer X.net X.m0 vis.length).isEmpty = false := by
    cases hL : tlayer X.net X.m0 vis.length with
    | nil => rw [hL] at he; exact absurd he List.not_mem_nil
    | cons _ _ => rfl
  have hT : termWit X.net X.m0 vis.length ≠ [] := by
    unfold termWit
    cases hF : (tlayer X.net X.m0 vis.length).findSome? (lassoOf X.net X.m0) with
    | none =>
      rw [List.findSome?_eq_none_iff] at hF
      rw [hF e he] at hw
      exact absurd hw (by simp)
    | some w' => simp
  intro hnil
  unfold graphWits at hnil
  have h3 := (List.append_eq_nil_iff.mp hnil).2
  simp only [ht, hne, Bool.not_false, Bool.and_self, ↓reduceIte] at h3
  exact hT h3

/-- The graph route reports `Violated` on a closed graph where a reachable quiescent marking
breaks the contract or, if termination is required, a run fires forever. -/
theorem graphJudge_violated {o : OOptions} {C : Contract String} {X : Closed} (hc0 : Canon X.m0)
    (hcl : closedB X.net (visited X.net X.m0 o.maxClasses) = true)
    (hv : (∃ m, Reach X.net (get X.m0) m ∧ Quiet o X.net m ∧ ¬ refMeets C X.envPlaces m) ∨
      (C.terminate = true ∧ ∃ f : Nat → String → Nat, f 0 = get X.m0 ∧
        ∀ n, ∃ l, LStep X.net l (f n) (f (n + 1)))) :
    ∃ ws, graphJudge o C X = ⟨.violated ws, .enumeration⟩ := by
  have hft := visited_foundT (net := X.net) (cap := o.maxClasses) hc0
  have hne : graphWits o C X (visited X.net X.m0 o.maxClasses) ≠ [] := by
    rcases hv with ⟨m, hr, hq, hb⟩ | ⟨ht, hf⟩
    · exact graphWits_meets hc0 hcl hft visited_init hr hq hb
    · exact graphWits_term hc0 hcl (fun e he => (hft e he).1) visited_init ht hf
  refine ⟨graphWits o C X (visited X.net X.m0 o.maxClasses), ?_⟩
  unfold graphJudge
  rw [if_neg (by rw [List.isEmpty_iff]; exact hne)]

end OpenNet

/-- ✓ **The reference verifier.** Example: the relay `q → relay → out` with `relay` at
`window(3, 5)`, one arrival on `q` and the clause `out = exactly 1` is `Violated`: once the token
has arrived on `q`, the only enabled transition is the reapable relay, so a late executor rests
there with `out` empty. The witness is the run `env:arrive[0]:q`. -/
@[evidence holds VER_022]
theorem VER_022_reference : VER_022 RefFire refClose refMeets refStrand refOpenVerify := by
  intro o N C
  refine ⟨fun ⟨e, he⟩ => ⟨e, by simp [refOpenVerify, he]⟩, ?_⟩
  intro r X hV hX
  have hJ : refJudge o N C X = r := by simpa [refOpenVerify, hX] using hV
  subst hJ
  have hdec : ∀ (R : OResult), (R = skipMatch o ∨ R = skipBudget o ∨ R = undecided o) →
      ∀ s, R.verdict ≠ .proven ∧ (∀ ws, R.verdict ≠ .violated ws) ∧
        (R.verdict = .unknown s → s ≠ "") := fun R hR s => undecided_facts hR s
  by_cases hm : N.hasMatch = true
  · have hR : refJudge o N C X = skipMatch o := by simp [refJudge, hm]
    rw [hR]
    obtain ⟨-, -, -⟩ := hdec (skipMatch o) (Or.inl rfl) ""
    refine ⟨fun hp => absurd hp (hdec _ (Or.inl rfl) "").1,
      fun hp => absurd hp (hdec _ (Or.inl rfl) "").1,
      fun ws hw => absurd hw ((hdec _ (Or.inl rfl) "").2.1 ws),
      fun s hs => (hdec _ (Or.inl rfl) s).2.2 hs, ?_⟩
    rintro - (hp | ⟨ws, hw⟩)
    · exact absurd hp (hdec _ (Or.inl rfl) "").1
    · exact absurd hw ((hdec _ (Or.inl rfl) "").2.1 ws)
  · by_cases hb : o.maxClasses = 0
    · have hR : refJudge o N C X = skipBudget o := by simp [refJudge, hm, hb]
      rw [hR]
      have H := hdec (skipBudget o) (Or.inr (Or.inl rfl))
      refine ⟨fun hp => absurd hp (H "").1, fun hp => absurd hp (H "").1,
        fun ws hw => absurd hw ((H "").2.1 ws), fun s hs => (H s).2.2 hs, ?_⟩
      rintro hm' -
      exact absurd hm' hm
    · have hR : refJudge o N C X = graphJudge o C X := by simp [refJudge, hm, hb]
      rw [hR]
      refine ⟨fun hp m hr hq => ?_, fun hp ht => ?_, fun ws hw => ?_, fun s hs => ?_,
        fun hm' => absurd hm' hm⟩
      · unfold graphJudge at hp
        split at hp
        · split at hp
          · rename_i hpv
            exact (provenB_sound hpv).1 m ((reachF_ref _ _ _).mp hr) hq
          · exact absurd hp (hdec _ (Or.inr (Or.inr rfl)) "").1
        · exact absurd hp (by simp)
      · unfold graphJudge at hp
        split at hp
        · split at hp
          · rename_i hpv
            rintro ⟨f, h0, hs⟩
            exact (provenB_sound hpv).2 ht ⟨f, h0, hs⟩
          · exact absurd hp (hdec _ (Or.inr (Or.inr rfl)) "").1
        · exact absurd hp (by simp)
      · unfold graphJudge at hw
        split at hw
        · split at hw
          · exact absurd hw (by simp)
          · exact absurd hw ((hdec _ (Or.inr (Or.inr rfl)) "").2.1 ws)
        · rename_i hne
          obtain rfl := (OVerdict.violated.inj hw)
          refine ⟨fun h0 => hne (by simp [h0]), fun w hw' => ?_⟩
          obtain ⟨h1, h2, -, h4⟩ := graphWits_sound hw'
          have hcf := graphWits_confirmed hw'
          refine ⟨fun n hn => ?_, fun ps hps hc => ?_, fun ht => ?_,
            fun hc => absurd (hcf.symm.trans hc) Bool.noConfusion⟩
          · obtain ⟨c, hc', hn', hr, hq, hb'⟩ := h1 n hn hcf
            exact ⟨c, hc', hn', fun _ => ⟨runF_ref.mpr hr, hq, hb'⟩⟩
          · obtain ⟨hne', hr, hq, hp⟩ := h2 ps hps hc
            exact ⟨hne', runF_ref.mpr hr, hq, hp⟩
          · obtain ⟨ht', hl⟩ := h4 ht
            refine ⟨ht', fun hc => ?_⟩
            obtain ⟨k, hk, hlt, hr1, hr2⟩ := hl hc
            exact ⟨k, hk, hlt, runF_ref.mpr hr1, runF_ref.mpr hr2⟩
      · unfold graphJudge at hs
        split at hs
        · split at hs
          · exact absurd hs (by simp)
          · exact (hdec _ (Or.inr (Or.inr rfl)) s).2.2 hs
        · exact absurd hs (by simp)




/-- The reference meets the coverage of VER-022: it never refuses an accepted closure, and on a
closed net with no match transition whose graph closes within the budget it proves a contract
that holds (`graphJudge_proven`) and reports one that is broken (`graphJudge_violated`). -/
theorem ver022_ref_covers : Ver022Covers RefFire refClose refMeets refOpenVerify := by
  intro o N C X hX
  obtain rfl := closeNet_ok hX
  have hV : refOpenVerify o N C = .ok (refJudge o N C (closeNet N.net C)) := by
    simp [refOpenVerify, hX]
  have hR : N.hasMatch = false → 0 < o.maxClasses →
      refJudge o N C (closeNet N.net C) = graphJudge o C (closeNet N.net C) := fun hm hb => by
    simp [refJudge, hm, Nat.pos_iff_ne_zero.mp hb]
  refine ⟨⟨_, hV⟩, fun hm hb hcl hmeet hterm => ?_, fun hm hb hcl hv => ?_⟩
  · refine ⟨_, hV, ?_⟩
    rw [hR hm hb, graphJudge_proven (canon_ofList _) hcl (fun m hr hq => hmeet m hr hq) hterm]
  · obtain ⟨ws, hws⟩ := graphJudge_violated (canon_ofList _) hcl hv
    exact ⟨_, ws, hV, by rw [hR hm hb, hws]⟩

/-! ## Examples -/

namespace OpenNet

theorem clausesB_iff {C : Contract String} {y : Marking String} :
    C.clauses.all (clauseHoldsB C · y) = true ↔ ∀ c ∈ C.clauses, ClauseHolds C c (get y) := by
  simp only [List.all_eq_true, clauseHoldsB_iff]

theorem strandFree_iff {C : Contract String} {envs : List String} {y : Marking String}
    (hc : Canon y) :
    (y.all fun e => !strandB C envs y e.1) = true ↔
      ∀ p, get y p ≠ 0 → ¬ refStrand (restSinks C envs) (restCond C) (get y) p := by
  simp only [List.all_eq_true, Bool.not_eq_true']
  refine ⟨fun h p hp hs => ?_, fun h e he => ?_⟩
  · have := h _ (mem_of_get_ne_zero hp)
    rw [strandB_iff.mpr hs] at this
    exact Bool.noConfusion this
  · cases hb : strandB C envs y e.1 with
    | false => rfl
    | true =>
      have hne : get y e.1 ≠ 0 := by rw [get_of_mem hc he]; exact hc.2 e he
      exact absurd (strandB_iff.mp hb) (h e.1 hne)

theorem ok_of_toOption {e : Except String OResult} {r : OResult} (h : e.toOption = some r) :
    e = .ok r := by
  cases e with
  | error _ => exact absurd h (by simp [Except.toOption])
  | ok a => simp only [Except.toOption, Option.some.injEq] at h; rw [h]

/-- The relay of [VER-022] AC11: `q → relay → out`, `relay` at `window(3, 5)` (reapable). -/
def relayT : Reference.Trans String :=
  { core := { name := "relay", inputs := [⟨"q", .one⟩], inhibitors := [], reads := [],
              resets := [] },
    out := some (.place "out"), reapable := true }

/-- The relay subnet. -/
def relayNet : Reference.Net String := { places := ["q", "out"], transitions := [relayT] }

/-- One arrival on `q` and the clause `out = exactly 1`. -/
def relayC : Contract String :=
  { groups := [⟨1, 1, ["q"]⟩], clauses := [⟨"out", ["out"], 1, some 1⟩] }

/-- The same arrival declared optional: `arriveAtMost(1, q)` written as `(0, 2)`. -/
def relayOpt : Contract String :=
  { groups := [⟨0, 2, ["q"]⟩], clauses := [⟨"out", ["out"], 1, some 1⟩] }

/-- A contract whose environment transition reuses the subnet's name `relay`. -/
def clashC : Contract String := { groups := [⟨1, 1, ["q"]⟩], env := [relayT] }

/-- The relay's closed net. -/
def relayX : Closed := closeNet relayNet relayC

/-- The token arrived on `q`. -/
def relayQ : Marking String := [("q", 1)]

theorem relay_close : refClose relayNet relayC = .ok relayX := by
  unfold refClose; rw [if_neg (by decide)]; rfl

theorem relay_reach : ReachF RefFire relayX.net (get relayX.m0) (get relayQ) := by
  have hc : Canon relayX.m0 := canonB_canon (by decide)
  have hm : ("env:arrive[0]:q", relayQ) ∈ succ relayX.net relayX.m0 := by decide
  exact Relation.ReflTransGen.single ⟨_, (mem_succ hc hm).2⟩

theorem relay_quiet (o : OOptions) (ho : o.assumeNoReaping = false) :
    Quiet o relayX.net (get relayQ) := by
  apply quietB_iff.mp
  simp only [quietB, ho]
  decide

theorem relay_breaks : ¬ refMeets relayC relayX.envPlaces (get relayQ) := by
  rw [← meetsB_iff (canonB_canon (by decide))]; decide

/-- `spin : p → p`, a transition that fires forever. -/
def spinT : Reference.Trans String :=
  { core := { name := "spin", inputs := [⟨"p", .one⟩], inhibitors := [], reads := [],
              resets := [] },
    out := some (.place "p") }

/-- The spinning subnet. -/
def spinNet : Reference.Net String := { places := ["p"], transitions := [spinT] }

/-- One token on `p`, which may rest there; termination required. -/
def spinC : Contract String := { init := [("p", 1)], rest := ["p"] }

/-- The spinning closed net. -/
def spinX : Closed := closeNet spinNet spinC

theorem spin_close (C : Contract String) (hC : C = spinC ∨ C = { spinC with terminate := false }) :
    refClose spinNet C = .ok spinX := by
  rcases hC with rfl | rfl <;> (unfold refClose; rw [if_neg (by decide)]; rfl)

theorem spin_forever : ∃ f : Nat → String → Nat, f 0 = get spinX.m0 ∧
    ∀ n, ∃ l, LStepF RefFire spinX.net l (f n) (f (n + 1)) := by
  have hc : Canon spinX.m0 := canonB_canon (by decide)
  have hm : ("spin", spinX.m0) ∈ succ spinX.net spinX.m0 := by decide
  exact ⟨fun _ => get spinX.m0, rfl, fun _ => ⟨_, (mem_succ hc hm).2⟩⟩

/-- A subnet with no transition. -/
def idleNet : Reference.Net String := { places := ["q"], transitions := [] }

/-- An arrival group `(lo, hi)` onto `q` and the clause `q = exactly 2`. -/
def arrC (lo hi : Nat) : Contract String :=
  { groups := [⟨lo, hi, ["q"]⟩], clauses := [⟨"q", ["q"], 2, some 2⟩] }

/-- Two tokens on places the contract does not name, `apfel` and `Zeit`. -/
def orderC : Contract String := { init := [("apfel", 1), ("Zeit", 1)] }

end OpenNet

/-! ### Meeting the contract -/

/-- A clause `out ≤ 1` and the terminal `halt`. -/
def ver022Halt : Contract String :=
  { clauses := [⟨"out", ["out"], 0, some 1⟩], terminals := [⟨"halt", []⟩] }

/-- A clause `out = exactly 1` and the terminal `halt`. -/
def ver022Halt1 : Contract String :=
  { clauses := [⟨"out", ["out"], 1, some 1⟩], terminals := [⟨"halt", []⟩] }

/-- A clause `out ≥ 0`. -/
def ver022Open : Contract String := { clauses := [⟨"out", ["out"], 0, none⟩] }

/-- ✓ **Meeting the contract, by example.** With the clause `out ≥ 0`, one token on `out` meets
the contract and one token on `q` does not (it is stranded). With `out = exactly 1` and the
terminal `halt`, a marking holding only the marked `halt` meets it: the lower bound is waived.
With `out ≤ 1` and `halt` marked, two tokens on `out` do not: the upper bound is not waived. -/
@[evidence nonvacuous VER_022_meets]
theorem VER_022_meets_nonvacuous :
    refMeets ver022Open [] (get [("out", 1)]) ∧ ¬ refMeets ver022Open [] (get [("q", 1)]) ∧
    refMeets ver022Halt1 [] (get [("halt", 1)]) ∧
    ¬ refMeets ver022Halt [] (get [("halt", 1), ("out", 2)]) := by
  refine ⟨(meetsB_iff (canonB_canon (by decide))).mp (by decide), ?_,
    (meetsB_iff (canonB_canon (by decide))).mp (by decide), ?_⟩ <;>
  · rw [← meetsB_iff (canonB_canon (by decide))]; decide

/-- Mutant: a marked terminal waives the upper bounds too. -/
def meetsWaiveUpper : MeetsRel String := fun C envs m =>
  (∀ c ∈ C.clauses, (∀ τ ∈ C.terminals, m τ.marker = 0) → ClauseHolds C c m) ∧
    ∀ p, m p ≠ 0 → ¬ refStrand (restSinks C envs) (restCond C) m p

/-- ✗ **An upper bound holds under a terminal too** (AC2). Example: the clause `out ≤ 1` with
the terminal `halt` marked and two tokens on `out` breaks the contract; a judge that waives the
whole clause under the terminal accepts it. -/
@[evidence forbids VER_022_meets]
theorem VER_022_meets_forbids_waiveUpper : ¬ VER_022_meets meetsWaiveUpper refStrand := by
  intro h
  have hc : Canon ([("halt", 1), ("out", 2)] : Marking String) := canonB_canon (by decide)
  have hiff := (h ver022Halt [] (get [("halt", 1), ("out", 2)])).trans
    (VER_022_meets_reference ver022Halt [] (get [("halt", 1), ("out", 2)])).symm
  have hR : ¬ refMeets ver022Halt [] (get [("halt", 1), ("out", 2)]) := by
    rw [← meetsB_iff hc]; decide
  refine hR (hiff.mp ⟨fun c _ hz => ?_, (strandFree_iff hc).mp (by decide)⟩)
  exact absurd (hz ⟨"halt", []⟩ (by simp [ver022Halt])) (by decide)

/-- Mutant: the lower bounds hold under a marked terminal too. -/
def meetsLowerAlways : MeetsRel String := fun C envs m =>
  (∀ c ∈ C.clauses, (∀ h, c.max = some h → clauseSum c m ≤ h) ∧ c.min ≤ clauseSum c m) ∧
    ∀ p, m p ≠ 0 → ¬ refStrand (restSinks C envs) (restCond C) m p

/-- ✗ **A lower bound is waived while a terminal is marked** (AC2). Example: the clause
`out = exactly 1` with the terminal `halt` marked and `out` empty meets the contract; a judge
that keeps the lower bound rejects it. -/
@[evidence forbids VER_022_meets]
theorem VER_022_meets_forbids_lowerAlways : ¬ VER_022_meets meetsLowerAlways refStrand := by
  intro h
  have hc : Canon ([("halt", 1)] : Marking String) := canonB_canon (by decide)
  have hiff := (h ver022Halt1 [] (get [("halt", 1)])).trans
    (VER_022_meets_reference ver022Halt1 [] (get [("halt", 1)])).symm
  have hR : refMeets ver022Halt1 [] (get [("halt", 1)]) := (meetsB_iff hc).mp (by decide)
  have := ((hiff.mpr hR).1 ⟨"out", ["out"], 1, some 1⟩ (by simp [ver022Halt1])).2
  exact absurd this (by decide)

/-- Mutant: stranded tokens are ignored. -/
def meetsIgnoreStrand : MeetsRel String := fun C _ m => ∀ c ∈ C.clauses, ClauseHolds C c m

/-- ✗ **A token on a place the contract does not name is stranded** (AC3). Example: with the
clause `out ≥ 0`, one token on `q` breaks the contract; a judge that reads the clauses only
accepts it. -/
@[evidence forbids VER_022_meets]
theorem VER_022_meets_forbids_ignoreStrand : ¬ VER_022_meets meetsIgnoreStrand refStrand := by
  intro h
  have hc : Canon ([("q", 1)] : Marking String) := canonB_canon (by decide)
  have hiff := (h ver022Open [] (get [("q", 1)])).trans
    (VER_022_meets_reference ver022Open [] (get [("q", 1)])).symm
  have hR : ¬ refMeets ver022Open [] (get [("q", 1)]) := by rw [← meetsB_iff hc]; decide
  exact hR (hiff.mp (clausesB_iff.mp (by decide)))

/-- Mutant: the environment places are not sinks. -/
def meetsEnvNotSink : MeetsRel String := fun C _ m => refMeets C [] m

/-- ✗ **A token on an environment place is never stranded** (AC8). Example: with `e` an
environment place, one token on `e` meets the contract; a judge that leaves the environment
places out of the rest set reports `e` stranded. -/
@[evidence forbids VER_022_meets]
theorem VER_022_meets_forbids_envNotSink : ¬ VER_022_meets meetsEnvNotSink refStrand := by
  intro h
  have hc : Canon ([("e", 1)] : Marking String) := canonB_canon (by decide)
  have hiff := (h ver022Open ["e"] (get [("e", 1)])).trans
    (VER_022_meets_reference ver022Open ["e"] (get [("e", 1)])).symm
  have hR : refMeets ver022Open ["e"] (get [("e", 1)]) := (meetsB_iff hc).mp (by decide)
  have hM : meetsEnvNotSink ver022Open ["e"] (get [("e", 1)]) := hiff.mpr hR
  exact (by rw [← meetsB_iff hc]; decide : ¬ refMeets ver022Open [] (get [("e", 1)])) hM

/-- With the rest set of [VER-014], meeting the contract is the plain list of the quoted
definition. Example: under the clause `out ≥ 0` and the terminal `halt` excusing `w`, a token on
`w` meets the contract exactly while `halt` is marked. -/
@[evidence cites "VER-022" "A quiescent marking **meets** the contract when every clause holds, lower bounds only while no terminal marker is marked, and every token lies on a clause place, a rest place, an environment place, a terminal marker, or an excused place of a marked terminal."]
theorem VER_022_meets_plain {N : Type} [DecidableEq N] {M : MeetsRel N} {S : StrandRel N}
    {V : RestViolRel N} (h14 : VER_014 S V) (h : VER_022_meets M S) (C : Contract N)
    (envs : List N) (m : N → Nat) :
    M C envs m ↔ (∀ c ∈ C.clauses, ClauseHolds C c m) ∧
      ∀ p, m p ≠ 0 → p ∈ C.clauses.flatMap Clause.places ∨ p ∈ C.rest ∨ p ∈ envs ∨
        (∃ τ ∈ C.terminals, τ.marker = p) ∨ ∃ τ ∈ C.terminals, m τ.marker ≠ 0 ∧ p ∈ τ.excused := by
  rw [h C envs m]
  have hs : ∀ p, ¬ S (restSinks C envs) (restCond C) m p ↔
      p ∈ C.clauses.flatMap Clause.places ∨ p ∈ C.rest ∨ p ∈ envs ∨
        (∃ τ ∈ C.terminals, τ.marker = p) ∨ ∃ τ ∈ C.terminals, m τ.marker ≠ 0 ∧ p ∈ τ.excused := by
    intro p
    rw [h14.1]
    simp only [restSinks, restCond, List.mem_append, List.mem_map, List.mem_flatMap,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, not_and, not_forall, exists_prop,
      or_assoc]
    by_cases hA : (∃ a ∈ C.clauses, p ∈ a.places) ∨ p ∈ C.rest ∨ p ∈ envs
    · refine iff_of_true (fun h' => absurd hA h') ?_
      rcases hA with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (Or.inl h'))
    · constructor
      · intro h2
        by_cases h3 : ∃ τ ∈ C.terminals, τ.marker = p
        · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
        · obtain ⟨τ, hτ, hp, hm⟩ := h2 hA (fun a ha he => h3 ⟨a, ha, he⟩)
          exact Or.inr (Or.inr (Or.inr (Or.inr ⟨τ, hτ, hm, hp⟩)))
      · rintro (h' | h' | h' | ⟨τ, hτ, he⟩ | ⟨τ, hτ, hm, hp⟩) _ h3
        · exact absurd (Or.inl h') hA
        · exact absurd (Or.inr (Or.inl h')) hA
        · exact absurd (Or.inr (Or.inr h')) hA
        · exact absurd he (h3 τ hτ)
        · exact ⟨τ, hτ, hp, hm⟩
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun c hc => ⟨h1 c hc, fun hm => h2 hm c hc⟩, fun p hp => (hs p).mp (h3 p hp)⟩
  · rintro ⟨h1, h3⟩
    exact ⟨fun c hc => (h1 c hc).1, fun hm c hc => (h1 c hc).2 hm,
      fun p hp => (hs p).mpr (h3 p hp)⟩


/-! ### The closure -/

namespace OpenNet

theorem groupTrans_sub : ∀ (gs : List (Group String)) (k i : Nat) (g : Group String),
    gs[i]? = some g → ∀ t ∈ groupTrans (k + i) g, t ∈ transFrom k gs
  | [], _, _, _, h => by simp at h
  | g' :: gs, k, 0, g, h => by
    intro t ht
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact List.mem_append_left _ (by simpa using ht)
  | g' :: gs, k, i + 1, g, h => by
    intro t ht
    simp only [List.getElem?_cons_succ] at h
    have := groupTrans_sub gs (k + 1) i g h t (by rwa [show k + 1 + i = k + (i + 1) by omega])
    exact List.mem_append_right _ this

/-- Both sources always built, whatever their count (the closure paragraph read before ruling
D20, VD-5 (4)). -/
def groupTransBoth (i : Nat) (g : Group String) : List (Reference.Trans String) :=
  g.places.map (fun p => moveT (arrName i p) (manSrc i) (some p)) ++
    g.places.map (fun p => moveT (optName i p) (optSrc i) (some p)) ++
    [moveT (declName i) (optSrc i) none]

/-- `groupTransBoth` over every group. -/
def transFromBoth : Nat → List (Group String) → List (Reference.Trans String)
  | _, [] => []
  | i, g :: gs => groupTransBoth i g ++ transFromBoth (i + 1) gs

end OpenNet

/-- ✓ **The closure, by example.** The relay with one mandatory arrival on `q` closes to `relay`
and `env:arrive[0]:q`, starting from one token on `env:arrivals[0]`; the same arrival declared
optional (`0` to `2`) closes to `relay`, `env:arrive?[0]:q` and `env:decline[0]`, starting from
two tokens on `env:optional[0]`; an environment transition named `relay`, like the subnet's own,
is refused. -/
@[evidence nonvacuous VER_022_closure]
theorem VER_022_closure_nonvacuous :
    ((refClose relayNet relayC).toOption.map fun X =>
        (X.net.transitions.map fun t => t.core.name, X.m0, X.envSteps)) =
      some (["relay", "env:arrive[0]:q"], [("env:arrivals[0]", 1)], ["env:arrive[0]:q"]) ∧
    ((refClose relayNet relayOpt).toOption.map fun X =>
        (X.net.transitions.map fun t => t.core.name, X.m0)) =
      some (["relay", "env:arrive?[0]:q", "env:decline[0]"], [("env:optional[0]", 2)]) ∧
    (refClose relayNet clashC).toOption = none := by
  decide

/-- Mutant: a collision is not refused. -/
def closeNoRefuse : CloseFn := fun net C => .ok (closeNet net C)

/-- ✗ **A collision is refused.** Example: an environment transition named `relay`, the name of
a transition of the subnet, must be refused; a closure that builds the net anyway is not. -/
@[evidence forbids VER_022_closure]
theorem VER_022_closure_forbids_noRefuse : ¬ VER_022_closure closeNoRefuse := by
  intro h
  obtain ⟨e, he⟩ := (h relayNet clashC).1 ⟨"relay", by decide, by decide⟩
  exact absurd he (by simp [closeNoRefuse])

/-- Mutant: both sources of every group are built, also when a count is 0. -/
def closeBoth : CloseFn := fun net C =>
  (refClose net C).map fun X =>
    { X with net := ⟨X.net.places, net.transitions ++ C.env ++ transFromBoth 0 C.groups⟩ }

/-- ✗ **A source of count 0 is left out with its transitions** (ruling D20, VD-5 (4)).
Example: one mandatory arrival on `q` has no optional source; a closure that builds both sources
adds `env:arrive?[0]:q` and `env:decline[0]`, so the closed net has four transitions, not two. -/
@[evidence forbids VER_022_closure]
theorem VER_022_closure_forbids_bothSources : ¬ VER_022_closure closeBoth := by
  intro h
  have hX : closeBoth relayNet relayC = .ok { relayX with net :=
      ⟨relayX.net.places, relayNet.transitions ++ relayC.env ++ transFromBoth 0 relayC.groups⟩ } := by
    simp only [closeBoth, relay_close]; rfl
  have := congrArg List.length ((h relayNet relayC).2.2 _ hX).1
  exact absurd this (by decide)

/-- Mutant: the arrival and decline transitions are reapable, as if they carried a deadline. -/
def closeReapable : CloseFn := fun net C =>
  (refClose net C).map fun X =>
    { X with net := ⟨X.net.places, net.transitions ++ C.env ++
        (closureTrans C).map fun t => { t with reapable := true }⟩ }

/-- ✗ **The arrivals are immediate.** Example: the relay's one arrival on `q` is the transition
`env:arrive[0]:q`, which is never reaped; a closure that makes it reapable lets a run rest before
the token arrives, so every quiescence property could hold for the wrong reason. -/
@[evidence forbids VER_022_closure]
theorem VER_022_closure_forbids_reapable : ¬ VER_022_closure closeReapable := by
  intro h
  have hX : closeReapable relayNet relayC = .ok { relayX with net :=
      ⟨relayX.net.places, relayNet.transitions ++ relayC.env ++
        (closureTrans relayC).map fun t => { t with reapable := true }⟩ } := by
    simp only [closeReapable, relay_close]; rfl
  have := congrArg (List.map Reference.Trans.reapable) ((h relayNet relayC).2.2 _ hX).1
  exact absurd this (by decide)

/-- Mutant: the groups are left to an environment mode, as the environment places of [VER-006]:
no sources, no arrival transitions. -/
def closeEnvMode : CloseFn := fun net C =>
  (refClose net C).map fun X =>
    { X with net := ⟨X.net.places, net.transitions ++ C.env⟩, m0 := ofList C.init }

/-- ✗ **The sources are ordinary places** (AC5). Example: one mandatory arrival on `q` becomes
the source `env:arrivals[0]` and the transition `env:arrive[0]:q`; a closure that leaves the
arrival to an environment mode has neither, so a run of its net could rest before the arrival. -/
@[evidence forbids VER_022_closure]
theorem VER_022_closure_forbids_envMode : ¬ VER_022_closure closeEnvMode := by
  intro h
  have hX : closeEnvMode relayNet relayC = .ok { relayX with
      net := ⟨relayX.net.places, relayNet.transitions ++ relayC.env⟩,
      m0 := ofList relayC.init } := by
    simp only [closeEnvMode, relay_close]; rfl
  have := congrArg List.length ((h relayNet relayC).2.2 _ hX).1
  exact absurd this (by decide)

/-- Mutant: the sources start empty. -/
def closeNoSeed : CloseFn := fun net C => (refClose net C).map fun X => { X with m0 := ofList C.init }

/-- ✗ **The mandatory source holds `min` tokens** (AC5). Example: one mandatory arrival on `q`
puts one token on `env:arrivals[0]`; a closure that starts it empty never delivers it. -/
@[evidence forbids VER_022_closure]
theorem VER_022_closure_forbids_noSeed : ¬ VER_022_closure closeNoSeed := by
  intro h
  have hX : closeNoSeed relayNet relayC = .ok { relayX with m0 := ofList relayC.init } := by
    simp only [closeNoSeed, relay_close]; rfl
  exact absurd ((h relayNet relayC).2.2 _ hX).2.1 (by decide)

/-- Mutant: every closure is refused. -/
def closeAlwaysRefuse : CloseFn := fun _ _ => .error "refused"

/-- ✗ **Fresh names are not refused.** Example: the relay with one arrival on `q` claims only
`env:arrivals[0]` and `env:arrive[0]:q`, which the subnet does not use; a closure that refuses
it anyway refuses a valid contract. -/
@[evidence forbids VER_022_closure]
theorem VER_022_closure_forbids_alwaysRefuse : ¬ VER_022_closure closeAlwaysRefuse := by
  intro h
  obtain ⟨X, hX⟩ := (h relayNet relayC).2.1 (by decide) (by decide)
  exact absurd hX (by simp [closeAlwaysRefuse])

/-- `answer : req → q`, an environment transition answering on the subnet's place `q`. -/
def ver022Answer : Reference.Trans String :=
  { core := { name := "answer", inputs := [⟨"req", .one⟩], inhibitors := [], reads := [],
              resets := [] },
    out := some (.place "q") }

/-- The relay's contract with the environment transition `answer` and the rest place `r`. -/
def ver022EnvC : Contract String :=
  { groups := [⟨1, 1, ["q"]⟩], rest := ["r"], env := [ver022Answer] }

/-- Mutant: contract places no arc touches are left out of the closed net. -/
def closeNoUndeclared : CloseFn := fun net C =>
  (refClose net C).map fun X => { X with net := ⟨net.places, X.net.transitions⟩ }

/-- ✗ **Contract places no arc touches join the closed net.** Example: the rest place `r`,
which nothing touches, is a place of the closed net; a closure that keeps only the subnet's
declared places drops it. -/
@[evidence forbids VER_022_closure]
theorem VER_022_closure_forbids_noUndeclared : ¬ VER_022_closure closeNoUndeclared := by
  intro h
  have hX : closeNoUndeclared relayNet ver022EnvC =
      .ok { closeNet relayNet ver022EnvC with
        net := ⟨relayNet.places, (closeNet relayNet ver022EnvC).net.transitions⟩ } := by
    simp only [closeNoUndeclared, refClose]; rw [if_neg (by decide)]; rfl
  have := ((h relayNet ver022EnvC).2.2 _ hX).2.2.1 "r" (by decide)
  exact absurd this (by decide)

/-- Mutant: every place an environment transition touches is an environment place, the
subnet's ports included. -/
def closeAllEnvPlaces : CloseFn := fun net C =>
  (refClose net C).map fun X => { X with envPlaces := nub (C.env.flatMap transPlaces) }

/-- ✗ **A port is no environment place** (AC8). Example: `answer : req → q` touches `req`,
the environment's own place, and `q`, a place of the subnet; only `req` is an environment place.
A closure that also counts `q` would let a token rest on the port. -/
@[evidence forbids VER_022_closure]
theorem VER_022_closure_forbids_allEnvPlaces : ¬ VER_022_closure closeAllEnvPlaces := by
  intro h
  have hX : closeAllEnvPlaces relayNet ver022EnvC =
      .ok { closeNet relayNet ver022EnvC with envPlaces := nub (ver022EnvC.env.flatMap transPlaces) } := by
    simp only [closeAllEnvPlaces, refClose]; rw [if_neg (by decide)]; rfl
  have := (((h relayNet ver022EnvC).2.2 _ hX).2.2.2.1 "q").mp (by decide)
  exact this.2 (by decide)

/-- Mutant: the contract's own environment transitions are not marked as environment steps. -/
def closeNoEnvSteps : CloseFn := fun net C =>
  (refClose net C).map fun X => { X with envSteps := (closureTrans C).map fun t => t.core.name }

/-- ✗ **An environment transition's firings are environment steps** (AC8). Example: `answer`
is fired by the environment; a closure that marks only the arrivals leaves its firings out of
the port trace's environment steps. -/
@[evidence forbids VER_022_closure]
theorem VER_022_closure_forbids_noEnvSteps : ¬ VER_022_closure closeNoEnvSteps := by
  intro h
  have hX : closeNoEnvSteps relayNet ver022EnvC =
      .ok { closeNet relayNet ver022EnvC with
        envSteps := (closureTrans ver022EnvC).map fun t => t.core.name } := by
    simp only [closeNoEnvSteps, refClose]; rw [if_neg (by decide)]; rfl
  exact absurd ((h relayNet ver022EnvC).2.2 _ hX).2.2.2.2 (by decide)

/-- A run is quiescent only once every required arrival has happened and every optional one has
been delivered or declined. Example: with one mandatory arrival on `q`, a marking that still
holds the token on `env:arrivals[0]` enables `env:arrive[0]:q`, which is never reaped, so it is
not quiescent. -/
@[evidence cites "VER-022" "A run is therefore quiescent only once every required arrival has happened and every optional one has been delivered or declined."]
theorem VER_022_quiescent_sources {Cl : CloseFn} (h : VER_022_closure Cl)
    {net : Reference.Net String} {C : Contract String} {X : Closed} (hX : Cl net C = .ok X)
    {m : String → Nat}
    (hq : ∀ t ∈ X.net.transitions, enabledNA m t.core = true → t.reapable = true)
    {i : Nat} {g : OpenNet.Group String} (hg : C.groups[i]? = some g) :
    (0 < g.min → g.places ≠ [] → m (manSrc i) = 0) ∧ (g.min < g.max → m (optSrc i) = 0) := by
  have hT := ((h net C).2.2 X hX).1
  have hsub : ∀ t ∈ groupTrans i g, t ∈ X.net.transitions := fun t ht => by
    rw [hT]
    exact List.mem_append_right _ (groupTrans_sub C.groups 0 i g hg t (by simpa using ht))
  have key : ∀ name src dst, moveT name src dst ∈ X.net.transitions → m src = 0 := by
    intro name src dst hmem
    by_contra hne
    have hen : enabledNA m (moveT name src dst).core = true := by
      simp [moveT, enabledNA, Card.required]
      omega
    have := hq _ hmem hen
    simp [moveT] at this
  constructor
  · intro hmin hp
    obtain ⟨p, hp'⟩ := List.exists_mem_of_ne_nil _ hp
    refine key (arrName i p) (manSrc i) (some p) (hsub _ ?_)
    simp only [groupTrans, hmin, if_true, List.mem_append, List.mem_map]
    exact Or.inl ⟨p, hp', rfl⟩
  · intro hlt
    refine key (declName i) (optSrc i) none (hsub _ ?_)
    simp [groupTrans, hlt]


/-! ### The verdict -/

set_option maxRecDepth 4000 in
/-- ✓ **The verdict, by example.** The [VER-022] AC11 relay (one arrival on `q`, the clause
`out = exactly 1`, `relay` at `window(3, 5)`) is `Violated` on the graph route: after the run
`env:arrive[0]:q` only the reapable relay is enabled, so the marking with the token on `q` is
quiescent, breaks the clause and strands `q`. Under `assumeNoReaping` it is `Proven`. With a
match transition and the SMT route off it is `Unknown`, naming the skipped graph. `spin : p → p`
is a `termination` violation with the lasso `spin` starting at once, and `Proven` when the
contract waives termination. One mandatory arrival pair onto `q` with the clause `q = exactly 2`
is `Proven`; the same pair declared optional is `Violated`, by a run that delivers one token and
declines the other (AC5). Tokens stranded on `apfel` and `Zeit` are listed `Zeit` first, in
code-point order (AC10). -/
@[evidence nonvacuous VER_022]
theorem VER_022_nonvacuous :
    (refOpenVerify {} ⟨relayNet, false⟩ relayC).toOption =
      some ⟨.violated [{ part := .clause "out", trace := ["env:arrive[0]:q"], endM := [("q", 1)] },
        { part := .stranded ["q"], trace := ["env:arrive[0]:q"], endM := [("q", 1)] }],
        .enumeration⟩ ∧
    (refOpenVerify { assumeNoReaping := true } ⟨relayNet, false⟩ relayC).toOption =
      some ⟨.proven, .enumeration⟩ ∧
    (refOpenVerify { smt := false } ⟨relayNet, true⟩ relayC).toOption =
      some ⟨.unknown "the state-class graph was skipped: the closed net declares match (ν-join) transitions, which the graph does not model, and the SMT route is disabled", .enumeration⟩ ∧
    (refOpenVerify {} ⟨spinNet, false⟩ spinC).toOption =
      some ⟨.violated [{ part := .termination, trace := ["spin"], endM := [("p", 1)], cycleStart := some 0 }],
        .enumeration⟩ ∧
    (refOpenVerify {} ⟨spinNet, false⟩ { spinC with terminate := false }).toOption =
      some ⟨.proven, .enumeration⟩ ∧
    (refOpenVerify {} ⟨idleNet, false⟩ (arrC 2 2)).toOption = some ⟨.proven, .enumeration⟩ ∧
    (refOpenVerify {} ⟨idleNet, false⟩ (arrC 0 2)).toOption =
      some ⟨.violated [{ part := .clause "q", trace := ["env:arrive?[0]:q", "env:decline[0]"], endM := [("q", 1)] }],
        .enumeration⟩ ∧
    ((refOpenVerify {} ⟨idleNet, false⟩ orderC).toOption.map fun r =>
      match r.verdict with
      | .violated ws => ws.map Witness.part
      | _ => []) = some [.stranded ["Zeit"], .stranded ["apfel"]] :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Mutant: quiescence read strictly whatever the option says (AC11). -/
def verifyPlain : OpenVerifier := fun o N C => refOpenVerify { o with assumeNoReaping := true } N C

/-- ✗ **Quiescence is reap-aware unless `assumeNoReaping`** (AC11). Example: on the relay, a
verifier that reads quiescence strictly proves the contract, although a late executor reaps the
relay and rests with the token on `q`, where the clause `out = exactly 1` fails. -/
@[evidence forbids VER_022]
theorem VER_022_forbids_plainQuiet : ¬ VER_022 RefFire refClose refMeets refStrand verifyPlain := by
  intro h
  have hV : verifyPlain {} ⟨relayNet, false⟩ relayC = .ok ⟨.proven, .enumeration⟩ :=
    ok_of_toOption (by decide)
  exact relay_breaks (((h {} ⟨relayNet, false⟩ relayC).2 _ _ hV relay_close).1 rfl _
    relay_reach (relay_quiet {} rfl))

/-- Mutant: the graph route also runs on a net with match transitions. -/
def verifyMatchBlind : OpenVerifier := fun o N C => refOpenVerify o { N with hasMatch := false } C

/-- ✗ **The graph never decides a net with match transitions** (AC9). Example: the relay
declared with a match transition must not be decided by the graph; a verifier that ignores the
declaration reports the graph's `Violated`. -/
@[evidence forbids VER_022]
theorem VER_022_forbids_matchBlind :
    ¬ VER_022 RefFire refClose refMeets refStrand verifyMatchBlind := by
  intro h
  have hV : verifyMatchBlind {} ⟨relayNet, true⟩ relayC =
      .ok ⟨.violated [{ part := .clause "out", trace := ["env:arrive[0]:q"], endM := [("q", 1)] },
        { part := .stranded ["q"], trace := ["env:arrive[0]:q"], endM := [("q", 1)] }],
        .enumeration⟩ :=
    ok_of_toOption (by decide)
  have := ((h {} ⟨relayNet, true⟩ relayC).2 _ _ hV relay_close).2.2.2.2 rfl (Or.inr ⟨_, rfl⟩)
  exact ORoute.noConfusion this

/-- Mutant: `Proven` whenever the explored classes show no violation, closed or not. -/
def verifyEager : OpenVerifier := fun o N C =>
  match refClose N.net C with
  | .error e => .error e
  | .ok X => .ok (
    if N.hasMatch then skipMatch o
    else if o.maxClasses = 0 then skipBudget o
    else if (graphWits o C X (visited X.net X.m0 o.maxClasses)).isEmpty then ⟨.proven, .enumeration⟩
    else ⟨.violated (graphWits o C X (visited X.net X.m0 o.maxClasses)), .enumeration⟩)

/-- ✗ **Only the absence of violations needs the graph to close.** Example: on the relay with a
class budget of 1 the graph holds only the initial marking, which is not quiescent; a verifier
that proves the contract from that prefix misses the reachable rest with the token on `q`. -/
@[evidence forbids VER_022]
theorem VER_022_forbids_eager : ¬ VER_022 RefFire refClose refMeets refStrand verifyEager := by
  intro h
  have hV : verifyEager { maxClasses := 1 } ⟨relayNet, false⟩ relayC =
      .ok ⟨.proven, .enumeration⟩ :=
    ok_of_toOption (by decide)
  exact relay_breaks (((h { maxClasses := 1 } ⟨relayNet, false⟩ relayC).2 _ _ hV
    relay_close).1 rfl _ relay_reach (relay_quiet _ rfl))

/-- Mutant: termination is never checked. -/
def verifyNoTermination : OpenVerifier := fun o N C =>
  refOpenVerify o N { C with terminate := false }

/-- ✗ **`Proven` means every run comes to rest, where termination is required** (AC4).
Example: `spin : p → p` fires forever; a verifier that skips the termination check proves the
contract. -/
@[evidence forbids VER_022]
theorem VER_022_forbids_noTermination :
    ¬ VER_022 RefFire refClose refMeets refStrand verifyNoTermination := by
  intro h
  have hV : verifyNoTermination {} ⟨spinNet, false⟩ spinC = .ok ⟨.proven, .enumeration⟩ :=
    ok_of_toOption (by decide)
  exact ((h {} ⟨spinNet, false⟩ spinC).2 _ _ hV (spin_close _ (Or.inl rfl))).2.1 rfl rfl
    spin_forever

/-- Mutant: termination is checked even when the contract waives it. -/
def verifyAlwaysTerminate : OpenVerifier := fun o N C =>
  refOpenVerify o N { C with terminate := true }

/-- ✗ **A cycle is no violation when termination is waived** (AC4). Example: `spin : p → p`
under a contract that waives termination meets it; a verifier that still reports the lasso
`spin` breaks the waiver. -/
@[evidence forbids VER_022]
theorem VER_022_forbids_alwaysTerminate :
    ¬ VER_022 RefFire refClose refMeets refStrand verifyAlwaysTerminate := by
  intro h
  have hV : verifyAlwaysTerminate {} ⟨spinNet, false⟩ { spinC with terminate := false } =
      .ok ⟨.violated [{ part := .termination, trace := ["spin"], endM := [("p", 1)], cycleStart := some 0 }],
        .enumeration⟩ :=
    ok_of_toOption (by decide)
  have := (((h {} ⟨spinNet, false⟩ { spinC with terminate := false }).2 _ _ hV
    (spin_close _ (Or.inr rfl))).2.2.1 _ rfl).2 _ List.mem_cons_self
  exact Bool.noConfusion (this.2.2.1 rfl).1

/-- Mutant: a refused closure is reported as `Unknown`. -/
def verifySwallow : OpenVerifier := fun o N C =>
  match refClose N.net C with
  | .error _ => .ok ⟨.unknown "the closure was refused", .enumeration⟩
  | .ok X => .ok (refJudge o N C X)

/-- ✗ **A refused closure is a refused verification.** Example: an environment transition named
`relay`, like the subnet's own, makes the closure refuse; a verifier that answers `Unknown`
instead hides the collision. -/
@[evidence forbids VER_022]
theorem VER_022_forbids_swallow : ¬ VER_022 RefFire refClose refMeets refStrand verifySwallow := by
  intro h
  have hc : refClose relayNet clashC =
      .error "VER-022: closing the net would add a name the net already declares" := by
    unfold refClose; rw [if_pos (by decide)]
  obtain ⟨e, he⟩ := (h {} ⟨relayNet, false⟩ clashC).1 ⟨_, hc⟩
  simp [verifySwallow, hc] at he

/-- Mutant: environment steps (the closure's and the contract's transitions) are dropped from the
witnesses' firing sequences. -/
def verifyNoEnvSteps : OpenVerifier := fun o N C =>
  (refOpenVerify o N C).map fun r =>
    match r.verdict with
    | .violated ws => { r with verdict := .violated (ws.map fun w =>
        { w with trace := w.trace.filter fun l => !decide (l ∈ (closeNet N.net C).envSteps) }) }
    | _ => r

/-- ✗ **A witness carries the firing sequence, environment steps included** (AC1). Example: on
the relay the clause violation is reached by the arrival `env:arrive[0]:q`; a witness without
that step is not a firing sequence from the initial marking, which holds no token on `q`. -/
@[evidence forbids VER_022]
theorem VER_022_forbids_noEnvSteps :
    ¬ VER_022 RefFire refClose refMeets refStrand verifyNoEnvSteps := by
  intro h
  have hV : verifyNoEnvSteps {} ⟨relayNet, false⟩ relayC =
      .ok ⟨.violated [{ part := .clause "out", trace := [], endM := [("q", 1)] },
        { part := .stranded ["q"], trace := [], endM := [("q", 1)] }], .enumeration⟩ :=
    ok_of_toOption (by decide)
  have := (((h {} ⟨relayNet, false⟩ relayC).2 _ _ hV relay_close).2.2.1 _ rfl).2 _
    List.mem_cons_self
  obtain ⟨c, -, -, hc⟩ := this.1 "out" rfl
  obtain ⟨hr, -⟩ := hc rfl
  have hq := congrFun (hr : get relayX.m0 = get [("q", 1)]) "q"
  exact absurd hq (by decide)

/-- Mutant: every witness is marked unconfirmed, as the SMT route's, and keeps its stranded
places. -/
def verifyUnconfirmed : OpenVerifier := fun o N C =>
  (refOpenVerify o N C).map fun r =>
    match r.verdict with
    | .violated ws => { verdict := .violated (ws.map fun w => { w with confirmed := false }),
                        route := .smt }
    | _ => r

/-- ✗ **An unconfirmed witness names no stranded place.** Example: on the relay, an SMT
stranding witness whose sequence does not replay can not say which place holds the stranded
token, so it must not name `q`. -/
@[evidence forbids VER_022]
theorem VER_022_forbids_unconfirmedNamed :
    ¬ VER_022 RefFire refClose refMeets refStrand verifyUnconfirmed := by
  intro h
  have hV : verifyUnconfirmed {} ⟨relayNet, false⟩ relayC =
      .ok ⟨.violated [{ part := .clause "out", trace := ["env:arrive[0]:q"], endM := [("q", 1)], confirmed := false },
        { part := .stranded ["q"], trace := ["env:arrive[0]:q"], endM := [("q", 1)], confirmed := false }],
        .smt⟩ :=
    ok_of_toOption (by decide)
  have := (((h {} ⟨relayNet, false⟩ relayC).2 _ _ hV relay_close).2.2.1 _ rfl).2 _
    (List.mem_cons_of_mem _ List.mem_cons_self)
  exact List.cons_ne_nil _ _ ((this.2.2.2 rfl).2 ["q"] rfl)

/-- Mutant: a violation is reported with an empty list of parts. -/
def verifyNoParts : OpenVerifier := fun o N C =>
  (refOpenVerify o N C).map fun r =>
    match r.verdict with
    | .violated _ => { r with verdict := .violated [] }
    | _ => r

/-- ✗ **A `Violated` lists a broken part.** Example: the relay breaks its clause and strands
`q`; a verifier that reports `Violated` with no part says nothing a caller can act on. -/
@[evidence forbids VER_022]
theorem VER_022_forbids_noParts : ¬ VER_022 RefFire refClose refMeets refStrand verifyNoParts := by
  intro h
  have hV : verifyNoParts {} ⟨relayNet, false⟩ relayC = .ok ⟨.violated [], .enumeration⟩ :=
    ok_of_toOption (by decide)
  exact (((h {} ⟨relayNet, false⟩ relayC).2 _ _ hV relay_close).2.2.1 _ rfl).1 rfl

/-- Mutant: a lasso's cycle start is one step late. -/
def verifyLateCycle : OpenVerifier := fun o N C =>
  (refOpenVerify o N C).map fun r =>
    match r.verdict with
    | .violated ws => { r with verdict := .violated (ws.map fun w =>
        { w with cycleStart := w.cycleStart.map (· + 1) }) }
    | _ => r

/-- ✗ **A termination witness marks where its cycle starts** (AC4). Example: `spin : p → p`
repeats from the first step, so the cycle starts at index 0 of `spin`; a witness that marks it
at index 1 leaves no cycle to repeat. -/
@[evidence forbids VER_022]
theorem VER_022_forbids_lateCycle :
    ¬ VER_022 RefFire refClose refMeets refStrand verifyLateCycle := by
  intro h
  have hV : verifyLateCycle {} ⟨spinNet, false⟩ spinC =
      .ok ⟨.violated [{ part := .termination, trace := ["spin"], endM := [("p", 1)], cycleStart := some 1 }],
        .enumeration⟩ :=
    ok_of_toOption (by decide)
  have := (((h {} ⟨spinNet, false⟩ spinC).2 _ _ hV (spin_close _ (Or.inl rfl))).2.2.1 _ rfl).2 _
    List.mem_cons_self
  obtain ⟨k, hk, hlt, -⟩ := (this.2.2.1 rfl).2 rfl
  obtain rfl := (Option.some.inj hk).symm
  exact absurd hlt (by decide)

/-- Mutant: an `Unknown` without a reason. -/
def verifyBlank : OpenVerifier := fun o N C =>
  (refOpenVerify o N C).map fun r =>
    match r.verdict with
    | .unknown _ => { r with verdict := .unknown "" }
    | _ => r

/-- ✗ **An `Unknown` says why** (AC7). Example: the relay with a match transition and the SMT
route off is `Unknown`; a verifier that gives no reason hides that the graph was skipped. -/
@[evidence forbids VER_022]
theorem VER_022_forbids_blank : ¬ VER_022 RefFire refClose refMeets refStrand verifyBlank := by
  intro h
  have hV : verifyBlank { smt := false } ⟨relayNet, true⟩ relayC =
      .ok ⟨.unknown "", .enumeration⟩ :=
    ok_of_toOption (by decide)
  exact ((h { smt := false } ⟨relayNet, true⟩ relayC).2 _ _ hV relay_close).2.2.2.1 "" rfl rfl

/-- Mutant: the graph route marks its witnesses unconfirmed and names no stranded place. -/
def verifyGraphUnconfirmed : OpenVerifier := fun o N C =>
  (refOpenVerify o N C).map fun r =>
    match r.verdict with
    | .violated ws => { r with verdict := .violated (ws.map fun w =>
        { w with confirmed := false,
                 part := match w.part with
                   | .stranded _ => .stranded []
                   | p => p }) }
    | _ => r

/-- ✗ **Only the SMT route marks a witness unconfirmed.** Example: on the relay the graph
route finds the run `env:arrive[0]:q`, a real firing sequence; a verifier that marks it
unconfirmed there would let any graph witness go unchecked. -/
@[evidence forbids VER_022]
theorem VER_022_forbids_graphUnconfirmed :
    ¬ VER_022 RefFire refClose refMeets refStrand verifyGraphUnconfirmed := by
  intro h
  have hV : verifyGraphUnconfirmed {} ⟨relayNet, false⟩ relayC =
      .ok ⟨.violated [{ part := .clause "out", trace := ["env:arrive[0]:q"], endM := [("q", 1)], confirmed := false },
        { part := .stranded [], trace := ["env:arrive[0]:q"], endM := [("q", 1)], confirmed := false }],
        .enumeration⟩ :=
    ok_of_toOption (by decide)
  have := (((h {} ⟨relayNet, false⟩ relayC).2 _ _ hV relay_close).2.2.1 _ rfl).2 _
    List.mem_cons_self
  exact ORoute.noConfusion (this.2.2.2 rfl).1

/-- A witness for a clause the contract does not have, unconfirmed. -/
def cryW : Witness :=
  { part := .clause "no such clause", trace := [], endM := [], confirmed := false }

/-- Mutant: every accepted closure is `Violated` on the SMT route, by an unconfirmed witness
for a clause the contract need not have. -/
def verifyCry : OpenVerifier := fun _ N C =>
  match refClose N.net C with
  | .error e => .error e
  | .ok _ => .ok ⟨.violated [cryW], .smt⟩

/-- ✗ **A clause part names a clause of the contract, confirmed or not.** Example: the relay's
contract has the one clause `out`; a verifier that reports an unconfirmed violation of a clause
named `no such clause` points the caller at nothing. -/
@[evidence forbids VER_022]
theorem VER_022_forbids_cry : ¬ VER_022 RefFire refClose refMeets refStrand verifyCry := by
  intro h
  have hV : verifyCry {} ⟨relayNet, false⟩ relayC = .ok ⟨.violated [cryW], .smt⟩ := by
    simp [verifyCry, relay_close]
  have := (((h {} ⟨relayNet, false⟩ relayC).2 _ _ hV relay_close).2.2.1 _ rfl).2 _
    List.mem_cons_self
  obtain ⟨c, hc, hn, -⟩ := this.1 "no such clause" rfl
  simp only [relayC, List.mem_singleton] at hc
  subst hc
  exact absurd hn (by decide)

/-- Mutant: every accepted closure is left `Unknown`. -/
def verifyUnknown : OpenVerifier := fun _ N C =>
  match refClose N.net C with
  | .error e => .error e
  | .ok _ => .ok ⟨.unknown "undecided", .smt⟩

/-- Mutant: every verification is refused. -/
def verifyRefuse : OpenVerifier := fun _ _ _ => .error "refused"

/-- A verifier that only ever answers `Unknown` or refuses breaks no line of the block. -/
theorem ver022_of_silent {V : OpenVerifier}
    (h1 : ∀ o N C, (∃ e, refClose N.net C = .error e) → ∃ e, V o N C = .error e)
    (h2 : ∀ o N C r, V o N C = .ok r → r = ⟨.unknown "undecided", .smt⟩) :
    VER_022 RefFire refClose refMeets refStrand V := by
  intro o N C
  refine ⟨h1 o N C, fun r X hV _ => ?_⟩
  obtain rfl := h2 o N C r hV
  refine ⟨fun h => ?_, fun h => ?_, fun ws h => ?_, fun s h => ?_, fun _ h => ?_⟩
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · simp only [OVerdict.unknown.injEq] at h; subst h; decide
  · rcases h with h | ⟨_, h⟩ <;> exact absurd h (by simp)

/-- The idle subnet with two mandatory arrivals onto `q` and the clause `q = exactly 2` closes,
and the reference proves it on a graph that closes: every hypothesis of the coverage's second
part holds there. -/
theorem idle_covered :
    refClose idleNet (arrC 2 2) = .ok (closeNet idleNet (arrC 2 2)) ∧
    GraphCloses {} (closeNet idleNet (arrC 2 2)) ∧
    (∀ m, ReachF RefFire (closeNet idleNet (arrC 2 2)).net (get (closeNet idleNet (arrC 2 2)).m0) m →
      Quiet {} (closeNet idleNet (arrC 2 2)).net m →
      refMeets (arrC 2 2) (closeNet idleNet (arrC 2 2)).envPlaces m) ∧
    ¬ ∃ f : Nat → String → Nat, f 0 = get (closeNet idleNet (arrC 2 2)).m0 ∧
      ∀ n, ∃ l, LStepF RefFire (closeNet idleNet (arrC 2 2)).net l (f n) (f (n + 1)) := by
  have hP : provenB {} (arrC 2 2) (closeNet idleNet (arrC 2 2))
      (visited (closeNet idleNet (arrC 2 2)).net (closeNet idleNet (arrC 2 2)).m0
        (({} : OOptions).maxClasses)) = true := by decide
  refine ⟨by unfold refClose; rw [if_neg (by decide)], by unfold GraphCloses; decide,
    fun m hr hq => (provenB_sound hP).1 m ((reachF_ref _ _ _).mp hr) hq, ?_⟩
  exact (provenB_sound hP).2 rfl

/-- The answer is coverage, not a line: a verifier that leaves every accepted closure `Unknown`
meets every line of VER-022 (it claims nothing it could get wrong) and fails `Ver022Covers`.
Example: two mandatory arrivals onto `q` with the clause `q = exactly 2` close to a net whose
whole graph is three markings, all meeting the contract; the coverage asks `Proven` there. -/
@[evidence cites "VER-022" "when the verifier accepts the closure and the graph closes within the class budget on a contract that holds, the verifier shall return Proven: a verifier that leaves every accepted closure Unknown meets every line of the block and fails its coverage Ver022Covers"]
theorem VER_022_covers_unknown :
    VER_022 RefFire refClose refMeets refStrand verifyUnknown ∧
      ¬ Ver022Covers RefFire refClose refMeets verifyUnknown := by
  refine ⟨ver022_of_silent (fun o N C ⟨e, he⟩ => ⟨e, by simp [verifyUnknown, he]⟩)
    (fun o N C r hV => ?_), fun h => ?_⟩
  · unfold verifyUnknown at hV
    split at hV
    · exact absurd hV (by simp)
    · exact (Except.ok.inj hV).symm
  · obtain ⟨hX, hcl, hmeet, hterm⟩ := idle_covered
    obtain ⟨r, hr, hp⟩ := (h {} ⟨idleNet, false⟩ (arrC 2 2) _ hX).2.1 rfl (by decide) hcl hmeet
      (fun _ => hterm)
    simp only [verifyUnknown, hX, Except.ok.injEq] at hr
    subst hr
    exact absurd hp (by simp)

/-- The answer is coverage, not a line: a verifier that refuses every verification meets every
line of VER-022 and fails the first part of `Ver022Covers`. Example: the relay with one arrival on
`q` closes without a collision, so a verifier must answer it rather than refuse. -/
@[evidence cites "VER-022" "when the verifier accepts the closure, it shall return a result: a verifier that refuses every verification meets every line of the block and fails its coverage Ver022Covers"]
theorem VER_022_covers_refuse :
    VER_022 RefFire refClose refMeets refStrand verifyRefuse ∧
      ¬ Ver022Covers RefFire refClose refMeets verifyRefuse := by
  refine ⟨ver022_of_silent (fun _ _ _ _ => ⟨_, rfl⟩) (fun _ _ _ r hV => ?_), fun h => ?_⟩
  · exact absurd hV (by simp [verifyRefuse])
  · obtain ⟨r, hr⟩ := (h {} ⟨relayNet, false⟩ relayC _ relay_close).1
    exact absurd hr (by simp [verifyRefuse])

/-- Mutant: the reference, with every `Violated` answer replaced by an `Unknown` (AC1, AC3, AC4,
AC11: the violations a closed graph shows are never reported). -/
def verifyHideViolated : OpenVerifier := fun o N C =>
  (refOpenVerify o N C).map fun r =>
    match r.verdict with
    | .violated _ => ⟨.unknown "a violation was found and not reported", .smt⟩
    | _ => r

/-- The answer is coverage, not a line: a verifier that answers `Unknown` wherever the reference
answers `Violated` meets every line of VER-022 (its `Proven` answers are the reference's) and
fails the third part of `Ver022Covers`. Example: the relay with one arrival on `q` and the clause
`out = exactly 1` closes, its graph closes, and the quiescent marking with the token on `q` breaks
the clause, so a verifier must answer `Violated` there. -/
@[evidence cites "VER-022" "When the graph closes within the class budget the verdict is exact: a verifier that leaves every violation of a closed graph Unknown meets every line of the block and fails its coverage Ver022Covers"]
theorem VER_022_covers_hideViolated :
    VER_022 RefFire refClose refMeets refStrand verifyHideViolated ∧
      ¬ Ver022Covers RefFire refClose refMeets verifyHideViolated := by
  refine ⟨fun o N C => ?_, fun h => ?_⟩
  · obtain ⟨h1, h2⟩ := VER_022_reference o N C
    refine ⟨fun he => ?_, fun r X hV hX => ?_⟩
    · obtain ⟨e, he'⟩ := h1 he
      exact ⟨e, by simp [verifyHideViolated, he', Except.map]⟩
    · cases hr0 : refOpenVerify o N C with
      | error e => simp [verifyHideViolated, hr0, Except.map] at hV
      | ok r0 =>
        simp only [verifyHideViolated, hr0, Except.map, Except.ok.injEq] at hV
        cases hv : r0.verdict with
        | violated ws =>
          rw [hv] at hV
          subst hV
          refine ⟨fun h => absurd h (by simp), fun h => absurd h (by simp),
            fun ws h => absurd h (by simp), fun s h => ?_, fun _ h => ?_⟩
          · simp only [OVerdict.unknown.injEq] at h; subst h; decide
          · rcases h with h | ⟨_, h⟩ <;> exact absurd h (by simp)
        | proven => rw [hv] at hV; subst hV; exact h2 r0 X hr0 hX
        | unknown s => rw [hv] at hV; subst hV; exact h2 r0 X hr0 hX
  · have hrel := ok_of_toOption VER_022_nonvacuous.1
    have hcl : GraphCloses {} relayX := by unfold GraphCloses; decide
    obtain ⟨r, ws, hr, hw⟩ := (h {} ⟨relayNet, false⟩ relayC _ relay_close).2.2 rfl (by decide) hcl
      (Or.inl ⟨get relayQ, relay_reach, relay_quiet {} rfl, relay_breaks⟩)
    simp only [verifyHideViolated, hrel, Except.map, Except.ok.injEq] at hr
    subst hr
    exact absurd hw (by simp)

/-- ✓ **One model for all blocks.** The reference firing relation, the [VER-014] rest set, the
reference judge, the reference closure and the reference verifier satisfy CORE-022, VER-014 and
the three VER-022 blocks at once, and the verifier meets the coverage `Ver022Covers` too: the
judge reads the same rest set VER-014 fixes. -/
@[evidence consistent CORE_022 VER_014 VER_022_meets VER_022_closure VER_022]
theorem VER_022_joint :
    ∃ (F : FireRel String) (S : StrandRel String) (Vr : RestViolRel String)
      (M : MeetsRel String) (Cl : CloseFn) (V : OpenVerifier),
      CORE_022 F ∧ VER_014 S Vr ∧ VER_022_meets M S ∧ VER_022_closure Cl ∧ VER_022 F Cl M S V ∧
        Ver022Covers F Cl M V :=
  ⟨RefFire, refStrand, refRestViol, refMeets, refClose, refOpenVerify, CORE_022_reference,
    VER_014_reference, VER_022_meets_reference, VER_022_closure_reference, VER_022_reference,
    ver022_ref_covers⟩

end Libpetri.Spec
