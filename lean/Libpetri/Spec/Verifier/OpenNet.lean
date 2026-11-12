import Libpetri.Spec.Verifier.Split

set_option linter.missingDocs true
set_option autoImplicit false

/-!
# Open nets against a contract (RefVerifier L6, [VER-022])

A subnet is verified in isolation, its ports played by the environment, against a contract that
says what the environment does and what the subnet guarantees. This file is the reference for
`rust/libpetri-verification/src/open_net/` (`closure.rs`, `predicate.rs`, `graph_route.rs`).

* **The contract** (`Contract`): the initial marking, the arrival groups (`Group`: between `min`
  and `max` tokens in total, each onto one of its places), the named count clauses (`Clause`),
  the rest places, the designed terminals (`Terminal`: a marker and its excused places), the
  environment transitions (`EnvTrans`, with their timing) and whether termination is required.
* **The closure** (`close`, `close_open_net`): the closed net is the subnet's places and the
  contract places no arc touches (`undeclared`), then the subnet's transitions, the environment
  transitions, and per arrival group `i`: when `min > 0` a source place `env:arrivals[i]` holding
  `min` and one transition `env:arrive[i]:<p>` per target; when `max > min` a source place
  `env:optional[i]` holding `max - min`, one transition `env:arrive?[i]:<p>` per target and one
  transition `env:decline[i]` with no output. An empty source is omitted. A name the subnet
  already uses is refused (`firstClash`). An **environment place** is a place only environment
  transitions touch (`envPlacesOf`).
* **Meeting the contract** (`Meets`): every clause holds (`ClauseBroken`: above `max`, or below
  `min` while no terminal marker is marked), and no token is stranded (`Stranded`), where the
  rest set is [VER-014]'s `refStrand` with the clause, rest and environment places as sinks and
  each terminal as a conditional sink (`restSinks`, `restCond`). `meets_iff_parts` shows this is
  exactly the SMT route's two queries on a quiescent marking: VER-002's `DeadlockFree` over that
  rest set and one `QuiescentCount` per clause with the markers as waivers.
* **The claim** (`ContractHolds`): every reachable quiescent marking of the closed net (VER-002's
  quiescence, reap-aware unless `assumeNoReaping`) meets the contract, and, where termination is
  required, every firing sequence is bounded (`Terminates`).
* **The cycle lemma** (`terminates_iff_no_lasso`): on a net whose reachable markings lie in a
  finite list, every run comes to rest exactly when no reachable marking lies on a cycle
  (`Lasso`). `terminates_of_ranking`: a ranking that every step lowers bounds every run by its
  initial value ([VER-019]).
* **The graph route** (`judge`): the reference exploration of the closed net, judged class by
  class: every explored marking that is quiescent is checked against the contract, and, when the
  exploration completed, termination is decided by whether a firing sequence as long as the
  number of explored markings exists (`layers`). `judge_proven_sound`: a `Proven` is
  `ContractHolds`. `judge_violated_sound`: each reported clause and stranded place is broken at
  a reachable quiescent marking, and a reported termination part is a reachable cycle.
  `judge_unknown_reason`: an `Unknown` names its reason. `graphApplies` is the route's guard: it
  never runs on a closed net with match transitions.

## Not modelled here (deferred)

* The SMT route as a solver (its queries are VER-002 properties; `meets_iff_parts` is the
  agreement), the port trace and the witnesses' marking lists (report shape), the report order
  of [VER-013] (names are reported in exploration and contract order here), the cost section.
* The in-flight split of the closed net (`verify_open_net` splits it with the environment steps
  atomic): `Split.refSplit` with `SplitCfg.envTrans := envStepNames`. Its in-flight places need
  no excuse at a rest: `Split.quiescent_no_inflight`.
* The graph route reads the untimed graph (every clock `immediate()`); the judge explores the
  untimed net, which is that graph's marking set, and reads the timing only for reapability.
* A truncated graph's termination: the judge reports a termination part only on a completed
  exploration (the runtimes also report a cycle among explored edges).
-/

namespace Libpetri.Spec.Verifier.OpenNet

open Libpetri Libpetri.Novel.Seam Libpetri.Spec.Verifier.Split

variable {K : Type}

/-! ## The contract -/

/-- An arrival group: between `min` and `max` tokens in total, each onto one of `places`. -/
structure Group (K : Type) where
  /-- The tokens that must arrive. -/
  min : Nat
  /-- The tokens that may arrive. -/
  max : Nat
  /-- The target places. -/
  places : List K

/-- A named count clause: at every quiescent marking the tokens across `places` number between
`min` and `max` (`none`: unbounded). -/
structure Clause (K : Type) where
  /-- The clause's name. -/
  name : String
  /-- The counted places. -/
  places : List K
  /-- The lower bound. -/
  min : Nat
  /-- The upper bound, if any. -/
  max : Option Nat

/-- A designed terminal: while `marker` holds a token, clause lower bounds are waived and the
`excused` places may hold tokens. -/
structure Terminal (K : Type) where
  /-- The marker place. -/
  marker : K
  /-- The excused places. -/
  excused : List K

/-- An environment transition, with its timing. -/
structure EnvTrans (K : Type) where
  /-- The transition. -/
  trans : Reference.Trans K
  /-- Its timing. -/
  timing : Novel.TimedScg.Timing := .immediate

/-- **The contract** ([VER-022]). -/
structure Contract (K : Type) where
  /-- The subnet's initial tokens. -/
  init : List (K × Nat) := []
  /-- The arrival groups. -/
  groups : List (Group K) := []
  /-- The count clauses. -/
  clauses : List (Clause K) := []
  /-- The rest places. -/
  rest : List K := []
  /-- The designed terminals. -/
  terminals : List (Terminal K) := []
  /-- The environment transitions. -/
  env : List (EnvTrans K) := []
  /-- Whether every run must come to rest (`true` unless waived). -/
  termination : Bool := true

/-! ## Names -/

/-- How places are named: a place from a generated name, and a place's name. -/
structure OpenNames (K : Type) where
  /-- The place a generated name stands for. -/
  place : String → K
  /-- A place's name. -/
  render : K → String

/-- `env:arrivals[i]`, the source of group `i`'s required tokens. -/
def srcName (i : Nat) : String := "env:arrivals[" ++ toString i ++ "]"
/-- `env:optional[i]`, the source of group `i`'s optional tokens. -/
def optName (i : Nat) : String := "env:optional[" ++ toString i ++ "]"
/-- `env:arrive[i]:<p>`. -/
def arriveName (i : Nat) (p : String) : String := "env:arrive[" ++ toString i ++ "]:" ++ p
/-- `env:arrive?[i]:<p>`. -/
def arriveOptName (i : Nat) (p : String) : String := "env:arrive?[" ++ toString i ++ "]:" ++ p
/-- `env:decline[i]`. -/
def declineName (i : Nat) : String := "env:decline[" ++ toString i ++ "]"

/-- What an environment step is, for the port trace. -/
inductive StepKind where
  /-- An arrival of group `group` onto `place`. -/
  | arrival (group : Nat) (place : String)
  /-- A decline of group `group`. -/
  | decline (group : Nat)
  /-- An environment transition of the contract. -/
  | environment
  deriving DecidableEq, Repr

/-! ## The closure -/

/-- An arrival transition: `one(src) → p`. -/
def arrivalT (nm : String) (src p : K) : Reference.Trans K :=
  { core := ⟨nm, [⟨src, .one⟩], [], [], []⟩, out := some (.place p) }

/-- A decline transition: `one(src)`, no output. -/
def declineT (nm : String) (src : K) : Reference.Trans K :=
  { core := ⟨nm, [⟨src, .one⟩], [], [], []⟩, out := none }

/-- The transitions of group `i`. -/
def groupTrans (nm : OpenNames K) (i : Nat) (g : Group K) : List (Reference.Trans K) :=
  (if 0 < g.min then
    g.places.map fun p => arrivalT (arriveName i (nm.render p)) (nm.place (srcName i)) p
   else []) ++
  (if g.min < g.max then
    g.places.map (fun p => arrivalT (arriveOptName i (nm.render p)) (nm.place (optName i)) p) ++
      [declineT (declineName i) (nm.place (optName i))]
   else [])

/-- The source tokens of group `i`; an empty source is omitted. -/
def groupInit (nm : OpenNames K) (i : Nat) (g : Group K) : List (K × Nat) :=
  (if 0 < g.min then [(nm.place (srcName i), g.min)] else []) ++
  (if g.min < g.max then [(nm.place (optName i), g.max - g.min)] else [])

/-- The names group `i` adds, in the order the closure adds them. -/
def groupNames (nm : OpenNames K) (i : Nat) (g : Group K) : List String :=
  (if 0 < g.min then srcName i :: g.places.map (fun p => arriveName i (nm.render p)) else []) ++
  (if g.min < g.max then
    optName i :: g.places.map (fun p => arriveOptName i (nm.render p)) ++ [declineName i]
   else [])

/-- The environment steps group `i` adds, with their kind. -/
def groupKinds (nm : OpenNames K) (i : Nat) (g : Group K) : List (String × StepKind) :=
  (if 0 < g.min then
    g.places.map (fun p => (arriveName i (nm.render p), .arrival i (nm.render p))) else []) ++
  (if g.min < g.max then
    g.places.map (fun p => (arriveOptName i (nm.render p), .arrival i (nm.render p))) ++
      [(declineName i, .decline i)]
   else [])

/-- Every group's contribution, groups numbered from `i`. -/
def allGroups {α : Type} (f : Nat → Group K → List α) : Nat → List (Group K) → List α
  | _, [] => []
  | i, g :: gs => f i g ++ allGroups f (i + 1) gs

/-- Append the entries of `l` not yet in `acc`, in order. -/
def uniqAppend [DecidableEq K] (acc l : List K) : List K :=
  l.foldl (fun a p => if p ∈ a then a else a ++ [p]) acc

/-- The first name of `l` already taken, `taken` growing with each name (Rust's `fresh`). -/
def firstClash : List String → List String → Option String
  | _, [] => none
  | taken, x :: xs => if x ∈ taken then some x else firstClash (x :: taken) xs

/-- `firstClash` finds nothing exactly when the names are new and pairwise distinct. -/
theorem firstClash_none_iff : ∀ (taken l : List String),
    firstClash taken l = none ↔ l.Nodup ∧ ∀ x ∈ l, x ∉ taken
  | _, [] => by simp [firstClash]
  | taken, x :: xs => by
    unfold firstClash
    split
    · rename_i hx; simp only [reduceCtorEq, false_iff, not_and, not_forall]
      intro _; exact ⟨x, List.mem_cons_self, fun h => h hx⟩
    · rename_i hx
      rw [firstClash_none_iff (x :: taken) xs]
      simp only [List.nodup_cons, List.mem_cons, forall_eq_or_imp, not_or]
      constructor
      · rintro ⟨hn, hall⟩
        exact ⟨⟨fun h => (hall x h).1 rfl, hn⟩, hx, fun y hy => (hall y hy).2⟩
      · rintro ⟨⟨hxs, hn⟩, _, hall⟩
        exact ⟨hn, fun y hy => ⟨fun h => hxs (h ▸ hy), hall y hy⟩⟩

/-- The closed net and what the report reads from it. -/
structure Closed (K : Type) where
  /-- The closed timed net. -/
  net : Reference.TimedNet K
  /-- The initial marking: the contract's initial tokens and the sources. -/
  init : List (K × Nat)
  /-- The environment steps by name, with their kind. -/
  envSteps : List (String × StepKind)
  /-- The environment places: places only environment transitions touch. -/
  envPlaces : List K
  /-- The contract places no arc touches. -/
  undeclared : List K

/-- The count a list of `(place, tokens)` entries gives a place (entries summed). -/
def initCount [DecidableEq K] (l : List (K × Nat)) : K → Nat := fun p =>
  ((l.filter fun e => decide (e.1 = p)).map Prod.snd).sum

section Dec

variable [DecidableEq K]

/-- **The environment places**: places environment transitions touch that the subnet does not. -/
def envPlacesOf (c : Contract K) (net : Reference.Net K) : List K :=
  uniqAppend [] ((c.env.flatMap fun e => transPlaces e.trans).filter fun p => p ∉ allPlaces net)

/-- The places a contract names (`OpenNetContract::places`), then the excused places. -/
def contractPlaces (c : Contract K) : List K :=
  c.init.map Prod.fst ++ c.groups.flatMap (·.places) ++ c.clauses.flatMap (·.places) ++ c.rest ++
    c.terminals.map (·.marker) ++ c.env.flatMap (fun e => transPlaces e.trans) ++
    c.terminals.flatMap (·.excused)

/-- **The contract places no arc touches**: they join the closed net as places of their own. -/
def undeclaredOf (c : Contract K) (net : Reference.Net K) : List K :=
  uniqAppend [] ((contractPlaces c).filter fun p => p ∉ allPlaces net ∧ p ∉ envPlacesOf c net)

/-- The closed net's timing, by name: a subnet transition keeps its timing, an environment
transition has the contract's, an arrival or decline is `immediate`. -/
def closedTiming (X : Reference.TimedNet K) (c : Contract K) (u : Reference.Trans K) :
    Novel.TimedScg.Timing :=
  match X.net.transitions.find? (fun t => t.core.name == u.core.name) with
  | some t => X.timing t
  | none => match c.env.find? (fun e => e.trans.core.name == u.core.name) with
    | some e => e.timing
    | none => .immediate

/-- **The closure** (`close_open_net`), or the name that collides. -/
def close (nm : OpenNames K) (X : Reference.TimedNet K) (c : Contract K) : Except String (Closed K) :=
  let taken0 := (allPlaces X.net).map nm.render ++ X.net.transitions.map (·.core.name)
  let envNames := c.env.map (·.trans.core.name)
  let envPl := envPlacesOf c X.net
  let gen := allGroups (groupNames nm) 0 c.groups
  match firstClash taken0 envNames, firstClash (envNames.reverse ++ taken0 ++ envPl.map nm.render) gen with
  | some n, _ | none, some n =>
    .error ("VER-022: closing the net would add '" ++ n ++ "', which the net already declares")
  | none, none =>
    .ok { net := { net := { places := X.net.places ++ undeclaredOf c X.net,
                            transitions := X.net.transitions ++ c.env.map (·.trans) ++
                              allGroups (groupTrans nm) 0 c.groups },
                   timing := closedTiming X c,
                   tol := X.tol },
          init := c.init ++ allGroups (groupInit nm) 0 c.groups,
          envSteps := envNames.map (fun n => (n, .environment)) ++
            allGroups (groupKinds nm) 0 c.groups,
          envPlaces := envPl,
          undeclared := undeclaredOf c X.net }

/-- The names of every environment step of a closed net: the steps the in-flight split keeps
atomic (`SplitCfg.envTrans`). -/
def envStepNames (cl : Closed K) : List String := cl.envSteps.map Prod.fst

/-- **A collision is refused**: the closure succeeds exactly when no environment transition's
name and no generated name is already taken, the names taken so far growing as Rust's `fresh`
adds them. -/
theorem close_ok_iff (nm : OpenNames K) (X : Reference.TimedNet K) (c : Contract K) :
    (∃ cl, close nm X c = .ok cl) ↔
      firstClash ((allPlaces X.net).map nm.render ++ X.net.transitions.map (·.core.name))
          (c.env.map (·.trans.core.name)) = none ∧
      firstClash ((c.env.map (·.trans.core.name)).reverse ++
          ((allPlaces X.net).map nm.render ++ X.net.transitions.map (·.core.name)) ++
          (envPlacesOf c X.net).map nm.render)
        (allGroups (groupNames nm) 0 c.groups) = none := by
  unfold close
  simp only
  split <;> simp_all [List.append_assoc]

/-- The closure's refusal, read as names: it succeeds exactly when the environment transitions'
names and the generated names are pairwise distinct and new. -/
theorem close_ok_iff_nodup (nm : OpenNames K) (X : Reference.TimedNet K) (c : Contract K) :
    (∃ cl, close nm X c = .ok cl) ↔
      ((c.env.map (·.trans.core.name)).Nodup ∧
        ∀ x ∈ c.env.map (·.trans.core.name),
          x ∉ (allPlaces X.net).map nm.render ++ X.net.transitions.map (·.core.name)) ∧
      ((allGroups (groupNames nm) 0 c.groups).Nodup ∧
        ∀ x ∈ allGroups (groupNames nm) 0 c.groups,
          x ∉ (c.env.map (·.trans.core.name)).reverse ++
            ((allPlaces X.net).map nm.render ++ X.net.transitions.map (·.core.name)) ++
            (envPlacesOf c X.net).map nm.render) := by
  rw [close_ok_iff, firstClash_none_iff, firstClash_none_iff]

end Dec

/-! ## Meeting the contract -/

/-- The places where a token may always rest: the clause places, the rest places and the
environment places (the sinks of the [VER-014] rest set). -/
def restSinks (c : Contract K) (envPl : List K) : List K :=
  c.clauses.flatMap (·.places) ++ c.rest ++ envPl

/-- Each terminal as a conditional sink ([VER-014]). -/
def restCond (c : Contract K) : List (CondSinks K) :=
  c.terminals.map fun t => ⟨t.marker, t.excused⟩

/-- The terminal markers, the waivers of every clause's lower bound. -/
def markers (c : Contract K) : List K := c.terminals.map (·.marker)

/-- **A clause is broken** at `m` (`count_violation`): above its upper bound, or below its lower
bound while no terminal marker is marked. -/
def ClauseBroken [DecidableEq K] (c : Contract K) (m : K → Nat) (cl : Clause K) : Prop :=
  (∃ h, cl.max = some h ∧ h < ncount cl.places m) ∨
    (ncount cl.places m < cl.min ∧ ∀ v ∈ markers c, m v = 0)

/-- **A stranded token** on `p`: `p` is marked and the [VER-014] rest set does not let a token
rest there. -/
def Stranded [DecidableEq K] (c : Contract K) (envPl : List K) (m : K → Nat) (p : K) : Prop :=
  m p ≠ 0 ∧ refStrand (restSinks c envPl) (restCond c) m p

/-- **A quiescent marking meets the contract** ([VER-022]): every clause holds and no token is
stranded. -/
def Meets [DecidableEq K] (c : Contract K) (envPl : List K) (m : K → Nat) : Prop :=
  (∀ cl ∈ c.clauses, ¬ ClauseBroken c m cl) ∧ ∀ p, ¬ Stranded c envPl m p

/-- The stranding query of the SMT route: `DeadlockFree` over the rest set. -/
def strandProp (c : Contract K) (envPl : List K) : VerProp K :=
  .deadlockFree (restSinks c envPl) (restCond c)

/-- The query of one clause: `QuiescentCount` with every terminal marker as a waiver. -/
def clauseProp (c : Contract K) (cl : Clause K) : VerProp K :=
  .quiescentCount cl.places cl.min cl.max (markers c)

/-- **The SMT route's queries decide the same predicate** ([VER-022]): at a quiescent marking,
the contract is not met exactly when VER-002's reference violation holds for the stranding query
or for some clause's query. -/
theorem meets_iff_parts [DecidableEq K] (c : Contract K) (envPl : List K) {noReap : Bool}
    {Y : Reference.TimedNet K} {m : K → Nat} (hq : VerQuiescent noReap Y m) :
    ¬ Meets c envPl m ↔
      refSafetyViol noReap Y (strandProp c envPl) m ∨
        ∃ cl ∈ c.clauses, refSafetyViol noReap Y (clauseProp c cl) m := by
  simp only [Meets, refSafetyViol, strandProp, clauseProp, refRestViol, ClauseBroken, Stranded,
    refStrand]
  constructor
  · intro h
    by_cases hs : ∃ p, m p ≠ 0 ∧ ¬ Resting (restSinks c envPl) (restCond c) m p
    · exact Or.inl ⟨hq, hs⟩
    · refine Or.inr ?_
      by_contra hc
      apply h
      refine ⟨fun cl hcl hb => hc ⟨cl, hcl, hq, ?_⟩, fun p hp => hs ⟨p, hp⟩⟩
      rcases hb with hb | hb
      · exact Or.inr hb
      · exact Or.inl hb
  · rintro (⟨_, p, hp⟩ | ⟨cl, hcl, _, hb⟩) ⟨hcls, hst⟩
    · exact hst p hp
    · apply hcls cl hcl
      rcases hb with hb | hb
      · exact Or.inr hb
      · exact Or.inl hb

/-- An environment place never strands a token ([VER-022] AC8). -/
theorem envPlace_not_stranded [DecidableEq K] (c : Contract K) {envPl : List K} {p : K}
    (hp : p ∈ envPl) (m : K → Nat) : ¬ Stranded c envPl m p := fun h =>
  h.2 (Or.inl (by simp [restSinks, hp]))

/-- An upper bound holds under a terminal too ([VER-022] AC2): above `max` the clause is broken
whatever the markers hold. -/
theorem clause_upper_broken [DecidableEq K] (c : Contract K) {cl : Clause K} {m : K → Nat} {h : Nat}
    (hmax : cl.max = some h) (hgt : h < ncount cl.places m) : ClauseBroken c m cl :=
  Or.inl ⟨h, hmax, hgt⟩

/-- A lower bound is waived while a terminal marker is marked ([VER-022] AC2). -/
theorem clause_lower_waived [DecidableEq K] (c : Contract K) {cl : Clause K} {m : K → Nat}
    (hmax : ∀ h, cl.max = some h → ncount cl.places m ≤ h) {v : K} (hv : v ∈ markers c)
    (hm : m v ≠ 0) : ¬ ClauseBroken c m cl := by
  rintro (⟨h, hh, hlt⟩ | ⟨_, hall⟩)
  · exact absurd (hmax h hh) (Nat.not_le.mpr hlt)
  · exact hm (hall v hv)

/-! ## Termination and the cycle lemma -/

section Cycle

variable [DecidableEq K]

/-- **Every run comes to rest**: the firing sequences from `m0` are bounded in length. -/
def Terminates (net : Reference.Net K) (m0 : K → Nat) : Prop :=
  ∃ B, ∀ tr m, Reference.Run net tr m0 m → tr.length ≤ B

/-- **A lasso**: a reachable marking on a cycle of at least one firing. -/
def Lasso (net : Reference.Net K) (m0 : K → Nat) : Prop :=
  ∃ m, Reference.Reach net m0 m ∧ ∃ tr, tr ≠ [] ∧ Reference.Run net tr m m

/-- A cycle run `k` times. -/
theorem run_repeat {net : Reference.Net K} {tr : List String} {m : K → Nat}
    (h : Reference.Run net tr m m) : ∀ k, Reference.Run net (List.replicate k tr).flatten m m
  | 0 => Reference.Run.nil m
  | k + 1 => by
    rw [List.replicate_succ, List.flatten_cons]
    exact run_append h (run_repeat h k)

/-- **A lasso is a run that never comes to rest.** -/
theorem lasso_not_terminates {net : Reference.Net K} {m0 : K → Nat} (h : Lasso net m0) :
    ¬ Terminates net m0 := by
  rintro ⟨B, hB⟩
  obtain ⟨m, hr, tr, hne, hc⟩ := h
  obtain ⟨pre, hpre⟩ := reach_run hr
  have hrun := run_append hpre (run_repeat hc (B + 1))
  have := hB _ _ hrun
  have hlen : B + 1 ≤ ((List.replicate (B + 1) tr).flatten).length := by
    rw [List.length_flatten]
    have h1 : 1 ≤ tr.length := List.length_pos_iff.mpr hne
    simp only [List.map_replicate, List.sum_replicate, smul_eq_mul]
    exact Nat.le_mul_of_pos_right _ h1
  rw [List.length_append] at this
  omega

/-- Along a firing sequence from a reachable marking, either some reachable marking lies on a
cycle, or the sequence visits `length + 1` distinct reachable markings. -/
theorem run_lasso_or_distinct {net : Reference.Net K} {m0 : K → Nat} :
    ∀ {tr : List String} {a b : K → Nat}, Reference.Run net tr a b → Reference.Reach net m0 a →
      Lasso net m0 ∨ ∃ W : List (K → Nat), W.length = tr.length + 1 ∧ W.Nodup ∧
        ∀ w ∈ W, Reference.Reach net m0 w ∧ ∃ tr', Reference.Run net tr' a w
  | [], a, _, _, ha => Or.inr ⟨[a], rfl, List.nodup_singleton a,
      fun w hw => by
        rw [List.mem_singleton.mp hw]
        exact ⟨ha, [], Reference.Run.nil _⟩⟩
  | l :: ls, a, b, h, ha => by
    cases h with
    | cons hs hr =>
      rename_i a1
      have ha1 : Reference.Reach net m0 a1 := Relation.ReflTransGen.tail ha ⟨l, hs⟩
      rcases run_lasso_or_distinct hr ha1 with hl | ⟨W, hlen, hnd, hW⟩
      · exact Or.inl hl
      · by_cases hmem : a ∈ W
        · obtain ⟨_, tr', hr'⟩ := hW a hmem
          exact Or.inl ⟨a, ha, l :: tr', List.cons_ne_nil _ _, Reference.Run.cons hs hr'⟩
        · refine Or.inr ⟨a :: W, by simp [hlen], List.nodup_cons.mpr ⟨hmem, hnd⟩, ?_⟩
          intro w hw
          rcases List.mem_cons.mp hw with rfl | hw
          · exact ⟨ha, [], Reference.Run.nil _⟩
          · obtain ⟨hw1, tr', hr'⟩ := hW w hw
            exact ⟨hw1, l :: tr', Reference.Run.cons hs hr'⟩

/-- **A long run closes a cycle**: when every reachable marking lies in `S`, a firing sequence
of at least `S.length` firings passes a reachable marking twice. -/
theorem long_run_lasso {net : Reference.Net K} {m0 : K → Nat} (S : List (K → Nat))
    (hS : ∀ f, Reference.Reach net m0 f → f ∈ S) {tr : List String} {m : K → Nat}
    (h : Reference.Run net tr m0 m) (hl : S.length ≤ tr.length) : Lasso net m0 := by
  rcases run_lasso_or_distinct h Relation.ReflTransGen.refl with hL | ⟨W, hlen, hnd, hW⟩
  · exact hL
  · exfalso
    have hsub : W ⊆ S := fun w hw => hS w (hW w hw).1
    have := (hnd.subperm hsub).length_le
    omega

/-- **The cycle lemma** ([VER-022] graph route): on a net whose reachable markings lie in the
finite list `S`, every run comes to rest exactly when no reachable marking lies on a cycle. -/
theorem terminates_iff_no_lasso {net : Reference.Net K} {m0 : K → Nat} (S : List (K → Nat))
    (hS : ∀ f, Reference.Reach net m0 f → f ∈ S) : Terminates net m0 ↔ ¬ Lasso net m0 := by
  refine ⟨fun ht hl => lasso_not_terminates hl ht, fun hl => ⟨S.length, fun tr m h => ?_⟩⟩
  by_contra hlt
  exact hl (long_run_lasso S hS h (by omega))

/-- **A ranking bounds every run** ([VER-019]): when every step lowers `r`, no firing sequence is
longer than `r m0`. -/
theorem terminates_of_ranking {net : Reference.Net K} {m0 : K → Nat} (r : (K → Nat) → Nat)
    (hr : ∀ m m', Reference.Reach net m0 m → Reference.Step net m m' → r m' < r m) :
    Terminates net m0 := by
  refine ⟨r m0, fun tr m h => ?_⟩
  suffices key : ∀ {tr : List String} {a b : K → Nat}, Reference.Run net tr a b →
      Reference.Reach net m0 a → tr.length + r b ≤ r a by
    have := key h Relation.ReflTransGen.refl
    omega
  intro tr
  induction tr with
  | nil => intro a b h _; cases h; simp
  | cons l ls ih =>
    intro a b h ha
    cases h with
    | cons hs hrest =>
      rename_i a1
      have hlt := hr _ _ ha ⟨l, hs⟩
      have := ih hrest (Relation.ReflTransGen.tail ha ⟨l, hs⟩)
      simp only [List.length_cons]
      omega

/-- A firing sequence at least `n` long has a prefix of exactly `n` firings. -/
theorem run_prefix {net : Reference.Net K} : ∀ {tr : List String} {a b : K → Nat} (n : Nat),
    Reference.Run net tr a b → n ≤ tr.length → ∃ c, Reference.Run net (tr.take n) a c
  | _, a, _, 0, _, _ => ⟨a, by simpa using Reference.Run.nil a⟩
  | [], _, _, _ + 1, _, hn => by simp at hn
  | _ :: _, _, _, n + 1, h, hn => by
    cases h with
    | cons hs hr =>
      obtain ⟨c, hc⟩ := run_prefix n hr (by simpa using hn)
      exact ⟨c, by simpa using Reference.Run.cons hs hc⟩

end Cycle

/-! ## The claim -/

/-- **The contract holds** ([VER-022] `Proven`): every reachable marking of the closed net that
is quiescent as [VER-002] reads it (reap-aware, or plain under `assumeNoReaping`) meets the
contract and, where termination is required, every run comes to rest. -/
def ContractHolds [DecidableEq K] (noReap : Bool) (Y : Reference.TimedNet K) (m0 : K → Nat)
    (c : Contract K) (envPl : List K) : Prop :=
  (∀ m, Reference.Reach Y.net m0 m → VerQuiescent noReap Y m → Meets c envPl m) ∧
    (c.termination = true → Terminates Y.net m0)

/-- A broken part of the contract. -/
inductive Part (K : Type) where
  /-- A clause, by name. -/
  | clause (name : String)
  /-- A stranded place. -/
  | stranded (p : K)
  /-- Some run never comes to rest. -/
  | termination
  deriving DecidableEq, Repr

/-- The open-net verdict: `Proven`, `Violated` with its broken parts, or `Unknown` with its
reasons. -/
inductive OpenVerdict (K : Type) where
  /-- Every part holds. -/
  | proven
  /-- The broken parts. -/
  | violated (parts : List (Part K))
  /-- Why no route decided. -/
  | unknown (reasons : List String)
  deriving DecidableEq, Repr

/-- **The graph route's guard** ([VER-022], [VER-017] condition 1): it never runs on a closed net
that declares match transitions. -/
def graphApplies (hasMatch : Bool) : Bool := !hasMatch

/-- The graph route steps aside on a net with match transitions. -/
theorem graphApplies_match : graphApplies true = false := rfl

/-! ## The graph route, on the reference exploration -/

section Judge

variable [LinearOrder K]

open Reference in
/-- Where a token may rest, on a canonical marking. -/
def restingB (c : Contract K) (envPl : List K) (m : Marking K) (p : K) : Bool :=
  decide (p ∈ restSinks c envPl) || (restCond c).any (fun cs => decide (cs.marker = p)) ||
    (restCond c).any (fun cs => decide (get m cs.marker ≠ 0) && decide (p ∈ cs.places))

open Reference in
/-- Whether a clause is broken, on a canonical marking. -/
def clauseBrokenB (c : Contract K) (m : Marking K) (cl : Clause K) : Bool :=
  cl.max.any (fun h => decide (h < ncount cl.places (get m))) ||
    (decide (ncount cl.places (get m) < cl.min) && (markers c).all (fun v => get m v == 0))

open Reference in
/-- **The broken parts at one marking**: the broken clauses in contract order, then the
stranded places in the marking's order. -/
def partsAt (c : Contract K) (envPl : List K) (m : Marking K) : List (Part K) :=
  (c.clauses.filter (clauseBrokenB c m)).map (fun cl => .clause cl.name) ++
    (m.filter (fun e => !restingB c envPl m e.1)).map (fun e => .stranded e.1)

open Reference in
/-- `restingB` decides the [VER-014] rest set. -/
theorem restingB_iff (c : Contract K) (envPl : List K) (m : Marking K) (p : K) :
    restingB c envPl m p = true ↔ Resting (restSinks c envPl) (restCond c) (get m) p := by
  unfold restingB Resting IsMarker
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true, ne_eq,
    or_assoc]

open Reference in
/-- `clauseBrokenB` decides `ClauseBroken`. -/
theorem clauseBrokenB_iff (c : Contract K) (m : Marking K) (cl : Clause K) :
    clauseBrokenB c m cl = true ↔ ClauseBroken c (get m) cl := by
  unfold clauseBrokenB ClauseBroken
  cases cl.max <;> simp

open Reference in
/-- A clause part is reported exactly for a broken clause. -/
theorem clause_mem_partsAt (c : Contract K) (envPl : List K) (m : Marking K) (n : String) :
    Part.clause n ∈ partsAt c envPl m ↔ ∃ cl ∈ c.clauses, cl.name = n ∧ ClauseBroken c (get m) cl := by
  simp only [partsAt, List.mem_append, List.mem_map, List.mem_filter, reduceCtorEq, and_false,
    exists_false, or_false, clauseBrokenB_iff, Part.clause.injEq]
  constructor
  · rintro ⟨cl, ⟨h1, h2⟩, h3⟩; exact ⟨cl, h1, h3, h2⟩
  · rintro ⟨cl, h1, h3, h2⟩; exact ⟨cl, ⟨h1, h2⟩, h3⟩

open Reference in
/-- A stranded part is reported exactly for a stranded place, on a canonical marking. -/
theorem stranded_mem_partsAt (c : Contract K) (envPl : List K) {m : Marking K} (hc : Canon m)
    (p : K) : Part.stranded p ∈ partsAt c envPl m ↔ Stranded c envPl (get m) p := by
  simp only [partsAt, List.mem_append, List.mem_map, List.mem_filter, reduceCtorEq, and_false,
    exists_false, false_or, Part.stranded.injEq, Bool.not_eq_true', Stranded, refStrand]
  constructor
  · rintro ⟨e, ⟨he, hr⟩, rfl⟩
    refine ⟨?_, fun h => by rw [(restingB_iff c envPl m e.1).mpr h] at hr; exact absurd hr (by simp)⟩
    rw [get_of_mem hc (show (e.1, e.2) ∈ m from he)]
    exact hc.2 e he
  · rintro ⟨hp, hr⟩
    refine ⟨(p, get m p), ⟨mem_of_get_ne_zero hp, ?_⟩, rfl⟩
    cases hb : restingB c envPl m p with
    | false => rfl
    | true => exact absurd ((restingB_iff c envPl m p).mp hb) hr

open Reference in
/-- No part at a marking is meeting the contract there. -/
theorem partsAt_nil_iff (c : Contract K) (envPl : List K) {m : Marking K} (hc : Canon m) :
    partsAt c envPl m = [] ↔ Meets c envPl (get m) := by
  constructor
  · intro h
    refine ⟨fun cl hcl hb => ?_, fun p hp => ?_⟩
    · have := (clause_mem_partsAt c envPl m cl.name).mpr ⟨cl, hcl, rfl, hb⟩
      rw [h] at this; exact absurd this List.not_mem_nil
    · have := (stranded_mem_partsAt c envPl hc p).mpr hp
      rw [h] at this; exact absurd this List.not_mem_nil
  · intro ⟨hcl, hst⟩
    rw [List.eq_nil_iff_forall_not_mem]
    intro x hx
    cases x with
    | clause n =>
      obtain ⟨cl, h1, _, h3⟩ := (clause_mem_partsAt c envPl m n).mp hx
      exact hcl cl h1 h3
    | stranded p => exact hst p ((stranded_mem_partsAt c envPl hc p).mp hx)
    | termination => simp [partsAt] at hx

open Reference in
/-- One layer of the exploration: every successor of a marking of `ms`, each once. -/
def layer (net : Reference.Net K) (ms : List (Marking K)) : List (Marking K) :=
  (ms.flatMap fun m => (succ net m).map Prod.snd).foldl addNew []

open Reference in
/-- The markings exactly `n` firings away from one of `ms`. -/
def layers (net : Reference.Net K) : Nat → List (Marking K) → List (Marking K)
  | 0, ms => ms
  | n + 1, ms => layers net n (layer net ms)

open Reference in
theorem mem_layer {net : Reference.Net K} {ms : List (Marking K)} {y : Marking K} :
    y ∈ layer net ms ↔ ∃ m ∈ ms, ∃ l, (l, y) ∈ succ net m := by
  unfold layer
  rw [mem_foldl_addNew]
  simp only [List.mem_flatMap, List.mem_map, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨m, hm, e, he, rfl⟩; exact ⟨m, hm, e.1, he⟩
  · rintro ⟨m, hm, l, hl⟩; exact ⟨m, hm, (l, y), hl, rfl⟩

open Reference in
/-- Every marking of a layer is canonical. -/
theorem layers_canon {net : Reference.Net K} : ∀ (n : Nat) (ms : List (Marking K)), (∀ m ∈ ms, Canon m) →
    ∀ y ∈ layers net n ms, Canon y
  | 0, _, h => h
  | n + 1, ms, h => by
    apply layers_canon n
    intro y hy
    obtain ⟨m, hm, l, hs⟩ := mem_layer.mp hy
    exact (mem_succ (h m hm) hs).1

open Reference in
/-- **The layers are exact**: a canonical marking is `n` firings from one of `ms` iff it is in
the `n`-th layer. -/
theorem mem_layers {net : Reference.Net K} : ∀ (n : Nat) (ms : List (Marking K)), (∀ m ∈ ms, Canon m) →
    ∀ {y : Marking K}, Canon y →
      (y ∈ layers net n ms ↔ ∃ m ∈ ms, ∃ tr, tr.length = n ∧ Run net tr (get m) (get y))
  | 0, ms, hms, y, hy => by
    simp only [layers]
    constructor
    · intro h; exact ⟨y, h, [], rfl, Run.nil _⟩
    · rintro ⟨m, hm, tr, hl, hr⟩
      obtain rfl := List.length_eq_zero_iff.mp hl
      have := ext (hms m hm) hy (fun q => congrFun (run_nil_eq hr) q)
      exact this ▸ hm
  | n + 1, ms, hms, y, hy => by
    have hms' : ∀ m ∈ layer net ms, Canon m := fun m hm => by
      obtain ⟨m', hm', l, hs⟩ := mem_layer.mp hm
      exact (mem_succ (hms m' hm') hs).1
    simp only [layers]
    rw [mem_layers n _ hms' hy]
    constructor
    · rintro ⟨m1, hm1, tr, hl, hr⟩
      obtain ⟨m, hm, l, hs⟩ := mem_layer.mp hm1
      exact ⟨m, hm, l :: tr, by simp [hl], Run.cons (mem_succ (hms m hm) hs).2 hr⟩
    · rintro ⟨m, hm, tr, hl, hr⟩
      cases tr with
      | nil => simp at hl
      | cons l ls =>
        obtain ⟨a1, hs, hr'⟩ := run_cons_inv hr
        obtain ⟨m1, hm1, hg⟩ := succ_complete (hms m hm) hs
        exact ⟨m1, mem_layer.mpr ⟨m, hm, l, hm1⟩, ls, by simpa using hl, hg ▸ hr'⟩

open Reference in
/-- The `n`-th layer from `m0` is empty iff no firing sequence of `n` firings starts there. -/
theorem layers_nil_iff {net : Reference.Net K} {m0 : Marking K} (hc : Canon m0) (n : Nat) :
    layers net n [m0] = [] ↔ ¬ ∃ tr f, tr.length = n ∧ Run net tr (get m0) f := by
  have h1 : ∀ m ∈ [m0], Canon m := by simpa using hc
  constructor
  · rintro h ⟨tr, f, hl, hr⟩
    obtain ⟨y, hcy, rfl⟩ := run_canon hc hr
    have := (mem_layers n [m0] h1 hcy).mpr ⟨m0, by simp, tr, hl, hr⟩
    rw [h] at this; exact absurd this List.not_mem_nil
  · intro h
    rw [List.eq_nil_iff_forall_not_mem]
    intro y hy
    have hcy : Canon y := layers_canon n [m0] h1 y hy
    obtain ⟨m, hm, tr, hl, hr⟩ := (mem_layers n [m0] h1 hcy).mp hy
    rw [List.mem_singleton.mp hm] at hr
    exact h ⟨tr, _, hl, hr⟩

/-- A broken part is real: a clause or a stranded place broken at a reachable quiescent marking,
or, for termination, a reachable cycle. -/
def PartReal (noReap : Bool) (Y : Reference.TimedNet K) (m0 : K → Nat) (c : Contract K)
    (envPl : List K) : Part K → Prop
  | .clause n => ∃ f, Reference.Reach Y.net m0 f ∧ VerQuiescent noReap Y f ∧
      ∃ cl ∈ c.clauses, cl.name = n ∧ ClauseBroken c f cl
  | .stranded p => ∃ f, Reference.Reach Y.net m0 f ∧ VerQuiescent noReap Y f ∧
      Stranded c envPl f p
  | .termination => Lasso Y.net m0

/-- The reason an unclosed graph gives. -/
def notClosedReason : String := "the state-class graph did not close within the class budget"

open Reference in
/-- The broken parts at the explored quiescent markings of an exploration `r`. -/
def brokenParts [Hashable K] (noReap : Bool) (Y : Reference.TimedNet K) (c : Contract K)
    (envPl : List K) (r : Search.Seen (Marking K) × Bool) : List (Part K) :=
  (r.1.keys.filter (quiescentB (refNet noReap Y))).flatMap (partsAt c envPl)

open Reference in
/-- Whether termination is required and broken: the exploration completed and a firing sequence
as long as the number of explored markings exists. -/
def termBroken [Hashable K] (noReap : Bool) (Y : Reference.TimedNet K) (c : Contract K)
    (m0 : Marking K) (r : Search.Seen (Marking K) × Bool) : Bool :=
  c.termination && r.2 && !(layers (refNet noReap Y) r.1.keys.length [m0]).isEmpty

/-- The termination part, when broken. -/
def termParts (b : Bool) : List (Part K) := if b then [.termination] else []

open Reference in
/-- **The graph route** ([VER-022] route 1), on the reference exploration of the closed net `Y`
from `m0` with at most `cap` markings: every explored marking that is quiescent (reap-aware, or
plain under `noReap`) is judged against the contract; when the exploration completed, a firing
sequence as long as the number of explored markings is a run that never comes to rest. No broken
part and a completed exploration: `Proven`; no broken part on an unclosed graph: `Unknown`;
otherwise `Violated` with every broken part found. -/
def judge [Hashable K] (noReap : Bool) (Y : Reference.TimedNet K) (c : Contract K)
    (envPl : List K) (m0 : Marking K) (cap : Nat) : OpenVerdict K :=
  let r := exploreNet (refNet noReap Y) cap m0
  let all := brokenParts noReap Y c envPl r ++ termParts (termBroken noReap Y c m0 r)
  if all.isEmpty then (if r.2 then .proven else .unknown [notClosedReason])
  else .violated all

#spec_witness judge

/-- A firing sequence and a lasso read the same on the relabelled net. -/
theorem lasso_refNet {noReap : Bool} {Y : Reference.TimedNet K} {m0 : K → Nat} :
    Lasso (refNet noReap Y) m0 ↔ Lasso Y.net m0 := by
  unfold Lasso
  simp only [refNet_reach, refNet_run]

/-- Termination reads the same on the relabelled net. -/
theorem terminates_refNet {noReap : Bool} {Y : Reference.TimedNet K} {m0 : K → Nat} :
    Terminates (refNet noReap Y) m0 ↔ Terminates Y.net m0 := by
  unfold Terminates
  simp only [refNet_run]

open Reference in
/-- **A `Proven` holds** ([VER-022] `Proven`): the graph route proves the contract only when
every reachable quiescent marking meets it and, where termination is required, every run comes
to rest. -/
theorem judge_proven_sound [Hashable K] {noReap : Bool} {Y : Reference.TimedNet K}
    {c : Contract K} {envPl : List K} {m0 : Marking K} {cap : Nat} (hc : Canon m0)
    (h : judge noReap Y c envPl m0 cap = .proven) :
    ContractHolds noReap Y (get m0) c envPl := by
  unfold judge at h
  simp only at h
  split at h
  · rename_i hall
    split at h
    · rename_i hcomp
      rw [List.isEmpty_iff, List.append_eq_nil_iff] at hall
      obtain ⟨hparts, hterm⟩ := hall
      have hex := explored_eq_reachable (net := refNet noReap Y) hc hcomp
      refine ⟨fun f hf hq => ?_, fun ht => ?_⟩
      · obtain ⟨y, hy, rfl⟩ := (hex.2 f).mpr (refNet_reach.mpr hf)
        have hcy := hex.1 y hy
        have hqy : quiescentB (refNet noReap Y) y = true :=
          (quiescentB_iff _ y).mpr (refNet_quiescent.mpr hq)
        have hmem : y ∈ (exploreNet (refNet noReap Y) cap m0).1.keys.filter
            (quiescentB (refNet noReap Y)) :=
          List.mem_filter.mpr ⟨Std.HashMap.mem_keys.mpr hy, hqy⟩
        have : partsAt c envPl y = [] := by
          rw [List.eq_nil_iff_forall_not_mem]
          intro x hx
          have : x ∈ brokenParts noReap Y c envPl (exploreNet (refNet noReap Y) cap m0) :=
            List.mem_flatMap.mpr ⟨y, hmem, hx⟩
          rw [hparts] at this
          exact absurd this List.not_mem_nil
        exact (partsAt_nil_iff c envPl hcy).mp this
      · rw [← terminates_refNet (noReap := noReap)]
        have hb : termBroken noReap Y c m0 (exploreNet (refNet noReap Y) cap m0) = false := by
          cases hb : termBroken noReap Y c m0 (exploreNet (refNet noReap Y) cap m0) with
          | false => rfl
          | true => rw [hb] at hterm; simp [termParts] at hterm
        have hl : layers (refNet noReap Y) (exploreNet (refNet noReap Y) cap m0).1.keys.length
            [m0] = [] := by
          simp only [termBroken, ht, hcomp, Bool.true_and, Bool.not_eq_false',
            List.isEmpty_iff] at hb
          exact hb
        have hno := (layers_nil_iff hc _).mp hl
        refine ⟨(exploreNet (refNet noReap Y) cap m0).1.keys.length, fun tr f hr => ?_⟩
        by_contra hlt
        obtain ⟨g, hg⟩ := run_prefix (exploreNet (refNet noReap Y) cap m0).1.keys.length hr
          (by omega)
        exact hno ⟨_, g, by rw [List.length_take]; omega, hg⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

open Reference in
/-- **Every reported part is broken** ([VER-022] `Violated`): each clause and each stranded place
the graph route reports is broken at a reachable quiescent marking, and a reported termination
part is a reachable cycle. -/
theorem judge_violated_sound [Hashable K] {noReap : Bool} {Y : Reference.TimedNet K}
    {c : Contract K} {envPl : List K} {m0 : Marking K} {cap : Nat} (hc : Canon m0)
    {parts : List (Part K)} (h : judge noReap Y c envPl m0 cap = .violated parts) :
    parts ≠ [] ∧ ∀ x ∈ parts, PartReal noReap Y (get m0) c envPl x := by
  unfold judge at h
  simp only at h
  split at h
  · split at h <;> simp at h
  · rename_i hall
    simp only [OpenVerdict.violated.injEq] at h
    subst h
    refine ⟨fun h => by simp [h] at hall, fun x hx => ?_⟩
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨y, hy, hxy⟩ := List.mem_flatMap.mp hx
      obtain ⟨hyk, hqy⟩ := List.mem_filter.mp hy
      have hym := Std.HashMap.mem_keys.mp hyk
      obtain ⟨hcy, hry⟩ := explored_sound hc hym
      have hq : VerQuiescent noReap Y (get y) :=
        refNet_quiescent.mp ((quiescentB_iff _ y).mp hqy)
      have hr : Reference.Reach Y.net (get m0) (get y) := refNet_reach.mp hry
      cases x with
      | clause n =>
        obtain ⟨cl, h1, h2, h3⟩ := (clause_mem_partsAt c envPl y n).mp hxy
        exact ⟨get y, hr, hq, cl, h1, h2, h3⟩
      | stranded p => exact ⟨get y, hr, hq, (stranded_mem_partsAt c envPl hcy p).mp hxy⟩
      | termination => simp [partsAt] at hxy
    · cases hb : termBroken noReap Y c m0 (exploreNet (refNet noReap Y) cap m0) with
      | false => rw [hb] at hx; simp [termParts] at hx
      | true =>
        rw [hb] at hx
        simp only [termParts, if_true, List.mem_singleton] at hx
        subst hx
        simp only [termBroken, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hb
        obtain ⟨⟨_, hcomp⟩, hne⟩ := hb
        have hno : ¬ ¬ ∃ tr f, tr.length =
            (exploreNet (refNet noReap Y) cap m0).1.keys.length ∧
              Run (refNet noReap Y) tr (get m0) f := fun hn => hne ((layers_nil_iff hc _).mpr hn)
        obtain ⟨tr, f, hl, hrun⟩ := Classical.not_not.mp hno
        have hex := explored_eq_reachable (net := refNet noReap Y) hc hcomp
        apply lasso_refNet.mp
        refine long_run_lasso ((exploreNet (refNet noReap Y) cap m0).1.keys.map get)
          (fun g hg => ?_) hrun (by simp [hl])
        obtain ⟨z, hz, rfl⟩ := (hex.2 g).mpr hg
        exact List.mem_map.mpr ⟨z, Std.HashMap.mem_keys.mpr hz, rfl⟩

/-- **An `Unknown` names its reason.** -/
theorem judge_unknown_reason [Hashable K] {noReap : Bool} {Y : Reference.TimedNet K}
    {c : Contract K} {envPl : List K} {m0 : Reference.Marking K} {cap : Nat}
    {reasons : List String} (h : judge noReap Y c envPl m0 cap = .unknown reasons) :
    reasons ≠ [] ∧ ∀ w ∈ reasons, w ≠ "" := by
  unfold judge at h
  simp only at h
  split at h
  · split at h
    · simp at h
    · simp only [OpenVerdict.unknown.injEq] at h
      subst h
      simp [notClosedReason]
  · simp at h

end Judge

/-! ## Worked examples ([VER-022] AC2, AC3, AC5, AC8, AC11) -/

/-- Place names of the examples. -/
def exRender : Nat → String
  | 0 => "q" | 1 => "out" | 5 => "budget" | 6 => "halt" | 7 => "stray" | 8 => "tool"
  | 100 => "env:arrivals[0]" | 101 => "env:optional[0]" | _ => "x"

/-- The places the closure names: the sources of group 0. -/
def exPlace (s : String) : Nat :=
  if s = srcName 0 then 100 else if s = optName 0 then 101 else 999

/-- The naming of the examples. -/
def exNm : OpenNames Nat := { place := exPlace, render := exRender }

/-- The relay `q → relay → out`. -/
def exRelay : Reference.Trans Nat :=
  { core := ⟨"relay", [⟨0, .one⟩], [], [], []⟩, out := some (.place 1) }

/-- The subnet: the relay at `window(3, 5)`. -/
def exX : Reference.TimedNet Nat :=
  { net := { places := [0, 1], transitions := [exRelay] }, timing := fun _ => .window 3 5,
    tol := 0 }

/-- The AC11 contract: one arrival on `q`, the clause `out = exactly 1`. -/
def exC : Contract Nat :=
  { groups := [⟨1, 1, [0]⟩], clauses := [⟨"out", [1], 1, some 1⟩] }

/-- The closed net's transition names and initial marking. -/
def closedShape (r : Except String (Closed Nat)) : Option (List String × List (Nat × Nat)) :=
  match r with
  | .ok cl => some (cl.net.net.transitions.map (·.core.name), cl.init)
  | .error _ => none

/-- The closure's refusal, if any. -/
def closeError (r : Except String (Closed Nat)) : Option String :=
  match r with
  | .ok _ => none
  | .error e => some e

/-- **The closure of a required arrival.** Example: one token must arrive on `q`; the closure adds
the source `env:arrivals[0]` holding one token and the transition `env:arrive[0]:q`, and no
optional source, since nothing more may arrive. -/
theorem ex_close_required :
    closedShape (close exNm exX exC) = some (["relay", "env:arrive[0]:q"], [(100, 1)]) := by
  decide

/-- **The closure of an optional arrival** ([VER-022] AC5). Example: at most one token may arrive
on `q`; the closure adds the source `env:optional[0]` holding one token, the arrival
`env:arrive?[0]:q` and the decline `env:decline[0]`, and no required source. -/
theorem ex_close_optional :
    closedShape (close exNm exX { exC with groups := [⟨0, 1, [0]⟩] }) =
      some (["relay", "env:arrive?[0]:q", "env:decline[0]"], [(101, 1)]) := by
  decide

set_option maxRecDepth 20000 in
/-- **A collision is refused.** Example: a subnet transition already named `env:arrive[0]:q`
makes the closure refuse, naming it. -/
theorem ex_close_collision :
    closeError (close exNm
        { exX with net := { exX.net with transitions := [{ exRelay with
            core := { exRelay.core with name := "env:arrive[0]:q" } }] } } exC) =
      some "VER-022: closing the net would add 'env:arrive[0]:q', which the net already declares" := by
  decide

/-- A contract with a budget clause, a terminal `halt` and the environment place `tool`. -/
def exC2 : Contract Nat :=
  { clauses := [⟨"budget", [5], 2, some 2⟩], terminals := [⟨6, []⟩] }

/-- **Upper bounds hold under a terminal, lower bounds are waived** ([VER-022] AC2). Example: one
token on `budget` breaks the clause `budget = 2`; with `halt` marked it does not; three tokens
on `budget` break it with or without `halt`. -/
theorem ex_parts_clause :
    partsAt exC2 [] [(5, 1)] = [.clause "budget"] ∧
    partsAt exC2 [] [(5, 1), (6, 1)] = [] ∧
    partsAt exC2 [] [(5, 3)] = [.clause "budget"] ∧
    partsAt exC2 [] [(5, 3), (6, 1)] = [.clause "budget"] := by
  decide

/-- **A stray token is stranded and named** ([VER-022] AC3); **an environment place never
strands** (AC8). Example: a token on `stray`, a place the contract does not name, is reported;
a token on `tool`, an environment place, is not. -/
theorem ex_parts_stranded :
    partsAt exC2 [8] [(5, 2), (7, 1)] = [.stranded 7] ∧
    partsAt exC2 [8] [(5, 2), (8, 1)] = [] := by
  decide

/-- The arrival transition of the AC11 closure. -/
def exArrive : Reference.Trans Nat := arrivalT "env:arrive[0]:q" 100 0

/-- The AC11 closed net: the relay and the arrival, timed as the closure times them. -/
def exY : Reference.TimedNet Nat :=
  { net := { places := [0, 1], transitions := [exRelay, exArrive] },
    timing := closedTiming exX exC, tol := 0 }

/-- The closure builds `exY`. -/
theorem ex_close_net :
    closedShape (close exNm exX exC) =
      some (exY.net.transitions.map (·.core.name), [(100, 1)]) := by
  decide

/-- The source token `{env:arrivals[0]: 1}`. -/
def exM0 : Nat → Nat := fun p => if p = 100 then 1 else 0

/-- The token arrived on `q`. -/
def exMq : Nat → Nat := fun p => if p = 0 then 1 else 0

/-- The token relayed to `out`. -/
def exMout : Nat → Nat := fun p => if p = 1 then 1 else 0

/-- The relay is reapable in the closed net; the arrival is not. -/
theorem ex_reapable : Reapable exY exRelay ∧ ¬ Reapable exY exArrive := by
  decide

/-- **AC11, the late executor's rest.** Example: after the arrival, the token waits on `q`; the
relay at `window(3, 5)` is reapable, so a late executor reaps it and rests there. Read
reap-aware, that marking is quiescent, and the clause `out = exactly 1` is broken. -/
theorem ex_ac11_violated :
    Reference.Reach exY.net exM0 exMq ∧ VerQuiescent false exY exMq ∧
      ClauseBroken exC exMq ⟨"out", [1], 1, some 1⟩ := by
  refine ⟨Relation.ReflTransGen.single ⟨"env:arrive[0]:q", exArrive, by simp [exY], rfl, [0],
    by decide, ⟨.action 0, rfl⟩, ?_⟩, ?_, ?_⟩
  · funext p
    by_cases h : p = 0
    · subst h; decide
    · by_cases h' : p = 100
      · subst h'; decide
      · simp [exMq, exM0, fireNC, exArrive, arrivalT, nconsumed, nspecAt, depProd, h, h',
          Ne.symm h', Ne.symm h]
  · intro t ht hen
    simp only [exY, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨rfl, ex_reapable.1⟩
    · exact absurd hen (by decide)
  · exact Or.inr ⟨by decide, by simp [markers, exC]⟩

/-- The reap-aware reading does not hold on the AC11 net: the contract is violated. -/
theorem ex_ac11_not_holds : ¬ ContractHolds false exY exM0 exC [] := by
  rintro ⟨h, _⟩
  obtain ⟨hr, hq, hb⟩ := ex_ac11_violated
  exact (h _ hr hq).1 _ (by simp [exC]) hb

/-- The markings the AC11 closed net reaches: the source token, the token on `q`, the token on
`out`. -/
theorem ex_reach (m : Nat → Nat) (h : Reference.Reach exY.net exM0 m) :
    m = exM0 ∨ m = exMq ∨ m = exMout := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hs ih =>
    rename_i a b _
    obtain ⟨l, t, ht, _, d, hen, ⟨ch, hd⟩, rfl⟩ := hs
    simp only [exY, List.mem_cons, List.not_mem_nil, or_false] at ht
    have hd' : d = (match t.out with | some (.place p) => [p] | _ => []) := by
      rcases ht with rfl | rfl
      · rcases ch with (_ | i) | j
        · simpa [Reference.deposit, exRelay, Reference.Out.branches] using hd.symm
        · simp [Reference.deposit, exRelay, Reference.Out.branches] at hd
        · simp [Reference.deposit, exRelay, Reference.Out.findTimeout] at hd
      · rcases ch with (_ | i) | j
        · simpa [Reference.deposit, exArrive, arrivalT, Reference.Out.branches] using hd.symm
        · simp [Reference.deposit, exArrive, arrivalT, Reference.Out.branches] at hd
        · simp [Reference.deposit, exArrive, arrivalT, Reference.Out.findTimeout] at hd
    subst hd'
    rcases ih with rfl | rfl | rfl <;> rcases ht with rfl | rfl
    · exact absurd hen (by decide)
    · refine Or.inr (Or.inl (funext fun p => ?_))
      by_cases h0 : p = 0
      · subst h0; decide
      · by_cases h1 : p = 100
        · subst h1; decide
        · simp [exMq, exM0, fireNC, exArrive, arrivalT, nconsumed, nspecAt, depProd, h0, h1,
            Ne.symm h1, Ne.symm h0]
    · refine Or.inr (Or.inr (funext fun p => ?_))
      by_cases h0 : p = 0
      · subst h0; decide
      · by_cases h1 : p = 1
        · subst h1; decide
        · simp [exMq, exMout, fireNC, exRelay, nconsumed, nspecAt, depProd, h0, h1, Ne.symm h0,
            Ne.symm h1]
    · exact absurd hen (by decide)
    · exact absurd hen (by decide)
    · exact absurd hen (by decide)

/-- **AC11 under `assumeNoReaping`.** Example: read plainly, the only reachable rest is the
token on `out`, where the clause holds and nothing strands; every run is at most two firings
long. The contract holds. -/
theorem ex_ac11_noReap : ContractHolds true exY exM0 exC [] := by
  refine ⟨fun m hm hq => ?_, fun _ => ?_⟩
  · rcases ex_reach m hm with rfl | rfl | rfl
    · exact absurd (hq exArrive (by simp [exY]) (by decide)).1 (by decide)
    · exact absurd (hq exRelay (by simp [exY]) (by decide)).1 (by decide)
    · refine ⟨fun cl hcl hb => ?_, fun p hp => ?_⟩
      · simp only [exC, List.mem_cons, List.not_mem_nil, or_false] at hcl
        subst hcl
        have hn : ncount [1] exMout = 1 := by decide
        rcases hb with ⟨h, hh, hlt⟩ | ⟨hlt, _⟩
        · simp only [Option.some.injEq] at hh
          subst hh
          rw [hn] at hlt
          omega
        · rw [hn] at hlt
          exact absurd hlt (by decide)
      · obtain ⟨hp1, hp2⟩ := hp
        by_cases h1 : p = 1
        · subst h1
          exact hp2 (Or.inl (by simp [restSinks, exC]))
        · exact hp1 (by simp [exMout, h1])
  · refine terminates_of_ranking (fun m => 2 * m 100 + m 0) (fun a b ha hs => ?_)
    obtain ⟨l, t, ht, _, d, hen, ⟨ch, hd⟩, rfl⟩ := hs
    simp only [exY, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ex_reach a ha with rfl | rfl | rfl <;> rcases ht with rfl | rfl
    · exact absurd hen (by decide)
    · have hd' : d = [0] := by
        rcases ch with (_ | i) | j
        · simpa [Reference.deposit, exArrive, arrivalT, Reference.Out.branches] using hd.symm
        · simp [Reference.deposit, exArrive, arrivalT, Reference.Out.branches] at hd
        · simp [Reference.deposit, exArrive, arrivalT, Reference.Out.findTimeout] at hd
      subst hd'; decide
    · have hd' : d = [1] := by
        rcases ch with (_ | i) | j
        · simpa [Reference.deposit, exRelay, Reference.Out.branches] using hd.symm
        · simp [Reference.deposit, exRelay, Reference.Out.branches] at hd
        · simp [Reference.deposit, exRelay, Reference.Out.findTimeout] at hd
      subst hd'; decide
    · exact absurd hen (by decide)
    · exact absurd hen (by decide)
    · exact absurd hen (by decide)

end Libpetri.Spec.Verifier.OpenNet
