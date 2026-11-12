import Libpetri.Spec.Req.VER_002
import Libpetri.Reference.Decide

set_option linter.missingDocs true
set_option autoImplicit false

/-!
# The verifier's result layer (RefVerifier L1)

The thin layer every verifier block reads ([VER-003]): the result record, the verified query,
the verified-net function, a decider, the phases of a dispatch and the one contract a phase
keeps. It adds no second verifier: the phases of the reference dispatch are the conformance
reference's own enumeration (`Reference.verdict` over `exploreNet`), read through VER-002's
violation predicate.

* **The yardstick** (`LStepF`, `RunF`, `ReachF`): firing sequences and reachability of a named
  net under an abstract firing relation `F : FireRel K`, the relation the CORE and IO blocks
  constrain. At `F = RefFire` they are `Reference.Run` and `Reference.Reach` (`runF_ref`,
  `reachF_ref`), so one consistency theorem can pick one `F` for CORE, IO and VER.
* **The record** (`Result`): the verdict (`Proven` with its method, `Violated`, `Unknown` with
  its reason), the deciding route, the trace, `counterexampleConfirmed`,
  `counterexampleTiming`, the reported P-invariants and free notes.
* **The query** (`Query`): the verified timed net, the property (VER-002's `VerProp`) and the
  initial marking (`NMarking`, the shipped `MarkingState`). `Abs` is the verified-net function
  (VER-001 inert places, VER-006 Arrivals closure, VER-004 in-flight split, EXEC-042 terminal
  rewrite), or the reason it cannot be built; `Decider` is a verifier entry point.
* **The dispatch** (`firstDecided`): the first phase that decides wins. `PhaseSound V P` is the
  contract of one phase against a violation reading `V` (VER-002's `SafetyViolRel`): a `Proven`
  names a method and holds on every reachable marking, a confirmed `Violated` carries a firing
  sequence to a violating marking, an `Unknown` has a reason. `firstDecided_sound` shows the
  contract composes.
* **The reference** (`refVerify`): refuse an unresolved property place (the places and waivers a
  property names, never its sinks: `propPlaces`), build the verified query, dispatch over
  `refSteps` (initial marking, dead initial marking, the reference enumeration), and pack the
  result: the route, the timing label (`UNTIMED_NET` exactly on an untimed net) and the
  invariants of the places no transition touches (`inertInvariants`, VER-001's "its own trivial
  P-invariant"). The reference decides only properties `Reference.Property` can express
  (`toRef`: no conditional sink declaration and no waiver); on the others every phase steps
  aside, which is sound.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Novel.Seam

/-! ## The yardstick, parametric in the firing relation -/

/-- A step of `net` under the firing relation `F`, labelled with the fired transition's name. -/
def LStepF {K : Type} (F : FireRel K) (net : Reference.Net K) (l : String) (m m' : K → Nat) :
    Prop :=
  ∃ t ∈ net.transitions, t.core.name = l ∧ ∃ d, F t m d m'

/-- A firing sequence of `net` under `F`: the labels in order, from the first marking to the
last. -/
def RunF {K : Type} (F : FireRel K) (net : Reference.Net K) :
    List String → (K → Nat) → (K → Nat) → Prop
  | [], m, m' => m = m'
  | l :: ls, m, m' => ∃ m1, LStepF F net l m m1 ∧ RunF F net ls m1 m'

/-- The markings reachable in `net` from `m0` under `F`. -/
def ReachF {K : Type} (F : FireRel K) (net : Reference.Net K) (m0 : K → Nat) :
    (K → Nat) → Prop :=
  Relation.ReflTransGen (fun m m' => ∃ l, LStepF F net l m m') m0

/-- At the reference firing relation, `ReachF` is `Reference.Reach`. -/
theorem reachF_ref {K : Type} [DecidableEq K] (net : Reference.Net K) (m0 f : K → Nat) :
    ReachF RefFire net m0 f ↔ Reference.Reach net m0 f := Iff.rfl

/-- An empty firing sequence stays where it started. -/
theorem run_nil_eq' {K : Type} [DecidableEq K] {net : Reference.Net K} {a b : K → Nat}
    (h : Reference.Run net [] a b) : a = b := by
  cases h; rfl

/-- A non-empty firing sequence is a first step and the rest. -/
theorem run_cons_inv' {K : Type} [DecidableEq K] {net : Reference.Net K} {l : String}
    {ls : List String} {a b : K → Nat} (h : Reference.Run net (l :: ls) a b) :
    ∃ m1, Reference.LStep net l a m1 ∧ Reference.Run net ls m1 b := by
  cases h with
  | cons hs hr => exact ⟨_, hs, hr⟩

/-- At the reference firing relation, `RunF` is `Reference.Run`. -/
theorem runF_ref {K : Type} [DecidableEq K] {net : Reference.Net K} :
    ∀ {tr : List String} {a b : K → Nat}, RunF RefFire net tr a b ↔ Reference.Run net tr a b
  | [], a, b => ⟨fun h => h ▸ Reference.Run.nil a, fun h => run_nil_eq' h⟩
  | l :: ls, a, b => by
    constructor
    · rintro ⟨m1, hs, hr⟩
      exact Reference.Run.cons hs (runF_ref.mp hr)
    · intro h
      obtain ⟨m1, hs, hr⟩ := run_cons_inv' h
      exact ⟨m1, hs, runF_ref.mpr hr⟩

namespace Verifier

/-! ## The result record -/

/-- The verdict ([VER-003]): `Proven` with its proof method, `Violated`, or `Unknown` with its
reason. -/
inductive Verdict where
  /-- Proven, with the proof method. -/
  | proven (method : String)
  /-- Violated. -/
  | violated
  /-- Unknown, with the reason. -/
  | unknown (reason : String)
  deriving DecidableEq, Repr

/-- The route that decided ([VER-003] Route): the SMT pipeline, the bounded enumeration
([VER-017]), the ν name-partition graph ([VER-012]), a structural proof, or `Unavailable` when
no route decided (the runtimes' `VerificationRoute`). -/
inductive Route where
  /-- The SMT pipeline. -/
  | smt
  /-- The bounded enumeration. -/
  | enumeration
  /-- The ν name-partition graph (Route B). -/
  | nuScg
  /-- A structural proof. -/
  | structural
  /-- No route decided. -/
  | unavailable
  deriving DecidableEq, Repr

/-- `counterexampleTiming` ([VER-003], [VER-023]). -/
inductive CexTiming where
  /-- Every transition is `immediate`. -/
  | untimedNet
  /-- A trace of the untimed abstraction, unchecked under timing. -/
  | untimedAbstraction
  /-- Route B decided on a timed net. -/
  | timedExact
  /-- The timed check reached a violating class. -/
  | timedConfirmed
  /-- The timed check closed its graph without a violating class. -/
  | spuriousUnderTiming
  /-- The timed check was truncated or stopped. -/
  | timedUndecided
  deriving DecidableEq, Repr

/-- A reported P-invariant ([VER-005]): weights by place name and the constant. -/
structure PInv (K : Type) where
  /-- The weights, by place name. -/
  weights : List (K × Int)
  /-- The constant. -/
  const : Int
  deriving DecidableEq, Repr

/-- The weighted token sum of a marking. -/
def PInv.dot {K : Type} (i : PInv K) (m : K → Nat) : Int :=
  (i.weights.map fun e => e.2 * (m e.1 : Int)).sum

/-- **The result record** ([VER-003]). -/
structure Result (K : Type) where
  /-- The verdict. -/
  verdict : Verdict
  /-- The deciding route. -/
  route : Route := .unavailable
  /-- The counterexample's transition labels. -/
  trace : List String := []
  /-- `counterexampleConfirmed`: `none` where no replay applies. -/
  confirmed : Option Bool := none
  /-- `counterexampleTiming`. -/
  timing : Option CexTiming := none
  /-- The reported P-invariants. -/
  invariants : List (PInv K) := []
  /-- Free notes (report text). -/
  notes : List String := []
  deriving Repr

/-- The options a verifier block reads. Later blocks add the fields they read; a field the
statement of a signed block does not name can be added without changing its hash. -/
structure Options where
  /-- The class budget of the graph routes ([VER-017]): 50 000 by default in every runtime. -/
  maxClasses : Nat := 50000
  /-- `assumeNoReaping` ([VER-002]). -/
  assumeNoReaping : Bool := false
  /-- `assumeAtomicFiring` ([VER-004]). -/
  assumeAtomicFiring : Bool := false
  /-- The timed counterexample check ([VER-023]). -/
  timedCheck : Bool := false

/-- **The verified query**: the verified timed net, the property and the initial marking every
route reads. -/
structure Query (K : Type) where
  /-- The verified net. -/
  net : Reference.TimedNet K
  /-- The property, after any rewrite the verified-net function makes. -/
  prop : VerProp K
  /-- The initial marking. -/
  m0 : NMarking K

/-- The initial marking of a query, as counts by place name. -/
def Query.init {K : Type} [DecidableEq K] (q : Query K) : K → Nat := q.m0.count

/-- **The verified-net function**: from the options, the user's net, the property and the initial
marking, the verified query, or the reason it cannot be built. -/
abbrev Abs (K : Type) : Type :=
  Options → Reference.TimedNet K → VerProp K → NMarking K → Except String (Query K)

/-- **A decider**: a verifier entry point, from the options, the user's net, the property and
the initial marking to a result. -/
abbrev Decider (K : Type) : Type :=
  Options → Reference.TimedNet K → VerProp K → NMarking K → Result K

/-! ## Unresolved places and untimed nets -/

/-- **The places a property names** (`property_place_names`, `smt_verifier.rs:3947-3964`; Java
`propertyPlaces`, TypeScript `propertyPlaces`): the places of `MutualExclusion`, `PlaceBound`
and `Unreachable`, the places and the waivers of `QuiescentCount`. The sinks of `DeadlockFree`
and `TerminatesAtSink` and the conditional declarations are not read: an unresolved sink or
marker is never marked and excuses nothing. -/
def propPlaces {K : Type} : VerProp K → List K
  | .deadlockFree _ _ | .terminatesAtSink _ => []
  | .mutualExclusion ps | .unreachable ps => ps
  | .placeBound p _ => [p]
  | .quiescentCount ps _ _ w => ps ++ w

/-- **Unresolved** ([VER-003] AC5): the property names a place the net does not declare and the
initial marking does not mark. -/
def Unresolved {K : Type} (X : Reference.TimedNet K) (φ : VerProp K) (m0 : NMarking K) : Prop :=
  ∃ p ∈ propPlaces φ, p ∉ X.net.places ∧ p ∉ m0.places

instance {K : Type} [DecidableEq K] (X : Reference.TimedNet K) (φ : VerProp K) (m0 : NMarking K) :
    Decidable (Unresolved X φ m0) := by
  unfold Unresolved; infer_instance

/-- **Untimed** ([VER-003] `UNTIMED_NET`): every transition is `immediate`. -/
def Untimed {K : Type} (X : Reference.TimedNet K) : Prop :=
  ∀ t ∈ X.net.transitions, TimingOf X t = .immediate

instance {K : Type} (X : Reference.TimedNet K) : Decidable (Untimed X) := by
  unfold Untimed; infer_instance

/-! ## Phases and the dispatch -/

/-- What one phase returns: a decision, or a note that it steps aside. -/
inductive PhaseOut where
  /-- The phase decided: the verdict, the trace and `counterexampleConfirmed`. -/
  | decided (v : Verdict) (trace : List String) (confirmed : Option Bool)
  /-- The phase steps aside. -/
  | aside (note : String)

/-- A phase reads the options and the verified query. -/
abbrev Phase (K : Type) : Type := Options → Query K → PhaseOut

/-- A named step of a dispatch, with the route it reports. -/
structure Step (K : Type) where
  /-- The step's name. -/
  name : String
  /-- The route a decision of the step reports. -/
  route : Route
  /-- The phase. -/
  run : Phase K

variable {K : Type}

/-- **The dispatch**: the first step whose phase decides wins. -/
def firstDecided : List (Step K) → Options → Query K → Option (Route × PhaseOut)
  | [], _, _ => none
  | s :: ss, o, q =>
    match s.run o q with
    | .aside _ => firstDecided ss o q
    | out => some (s.route, out)

/-- A dispatch reports the route of one of its steps, the decision of that step, never an aside.
-/
theorem firstDecided_step : ∀ {steps : List (Step K)} {o : Options} {q : Query K} {r : Route}
    {out : PhaseOut}, firstDecided steps o q = some (r, out) →
      ∃ s ∈ steps, s.route = r ∧ s.run o q = out ∧ ∀ n, out ≠ .aside n
  | [], _, _, _, _, h => by simp [firstDecided] at h
  | s :: ss, o, q, r, out, h => by
    unfold firstDecided at h
    split at h
    · obtain ⟨s', hs', h1, h2, h3⟩ := firstDecided_step h
      exact ⟨s', List.mem_cons_of_mem _ hs', h1, h2, h3⟩
    · rename_i hne
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨s, List.mem_cons_self, rfl, rfl, fun n hn => hne n hn⟩

/-- A dispatch whose first step decides returns that decision. -/
theorem firstDecided_head {s : Step K} {ss : List (Step K)} {o : Options} {q : Query K}
    {v : Verdict} {tr : List String} {c : Option Bool} (h : s.run o q = .decided v tr c) :
    firstDecided (s :: ss) o q = some (s.route, .decided v tr c) := by
  simp [firstDecided, h]

/-- A dispatch whose steps all step aside decides nothing. -/
theorem firstDecided_none : ∀ {steps : List (Step K)} {o : Options} {q : Query K},
    (∀ s ∈ steps, ∃ n, s.run o q = .aside n) → firstDecided steps o q = none
  | [], _, _, _ => rfl
  | s :: ss, o, q, h => by
    obtain ⟨n, hn⟩ := h s List.mem_cons_self
    simp only [firstDecided, hn]
    exact firstDecided_none fun s' hs' => h s' (List.mem_cons_of_mem _ hs')

/-- **The phase contract** against the violation reading `V`: a `Proven` names a method and no
reachable marking of the verified net violates the property; a confirmed `Violated` carries a
firing sequence from the initial marking to a violating marking; an `Unknown` has a reason. -/
def PhaseSound [DecidableEq K] (V : SafetyViolRel K) (P : Phase K) : Prop :=
  ∀ o q,
    (∀ meth tr c, P o q = .decided (.proven meth) tr c →
      meth ≠ "" ∧ ∀ f, Reference.Reach q.net.net q.init f → ¬ V o.assumeNoReaping q.net q.prop f) ∧
    (∀ tr, P o q = .decided .violated tr (some true) →
      ∃ f, Reference.Run q.net.net tr q.init f ∧ V o.assumeNoReaping q.net q.prop f) ∧
    (∀ why tr c, P o q = .decided (.unknown why) tr c → why ≠ "")

/-- **The contract composes**: a dispatch over sound phases decides soundly. -/
theorem firstDecided_sound [DecidableEq K] {V : SafetyViolRel K} {steps : List (Step K)}
    (hs : ∀ s ∈ steps, PhaseSound V s.run) {o : Options} {q : Query K} {r : Route}
    {out : PhaseOut} (h : firstDecided steps o q = some (r, out)) :
    (∀ meth tr c, out = .decided (.proven meth) tr c →
      meth ≠ "" ∧ ∀ f, Reference.Reach q.net.net q.init f → ¬ V o.assumeNoReaping q.net q.prop f) ∧
    (∀ tr, out = .decided .violated tr (some true) →
      ∃ f, Reference.Run q.net.net tr q.init f ∧ V o.assumeNoReaping q.net q.prop f) ∧
    (∀ why tr c, out = .decided (.unknown why) tr c → why ≠ "") := by
  obtain ⟨s, hm, -, rfl, -⟩ := firstDecided_step h
  exact hs s hm o q

/-! ## The reference phases

The reference decides with the conformance reference (`Reference.verdict`), whose property type
has no conditional sink declaration and no waiver, and whose quiescence reads each transition's
`reapable` flag. `refNet` sets the flags from the timing (and clears them under
`assumeNoReaping`), and `toRef` translates the properties the reference can express. -/

/-- The verified net as the conformance reference reads it: each transition's `reapable` flag
is its timing's ([TIME-013]: `Deadline` or `Window`), and no transition is reapable under
`assumeNoReaping`. Firing does not read the flag. -/
def refNet (noReap : Bool) (X : Reference.TimedNet K) : Reference.Net K :=
  { places := X.net.places,
    transitions := X.net.transitions.map fun t =>
      { t with reapable := !noReap && (X.timing t).reapable } }

section Dec

variable [DecidableEq K]

/-- The properties the conformance reference expresses: no conditional declaration, no waiver;
a `QuiescentCount` place listed twice is counted once (`dedup`). -/
def toRef : VerProp K → Option (Reference.Property K)
  | .deadlockFree sinks [] => some (.deadlockFree sinks)
  | .deadlockFree _ (_ :: _) => none
  | .terminatesAtSink sinks => some (.terminatesAtSink sinks)
  | .mutualExclusion ps => some (.mutualExclusion ps)
  | .placeBound p k => some (.placeBound p k)
  | .unreachable ps => some (.unreachable ps)
  | .quiescentCount ps lo hi [] => some (.quiescentCount ps.dedup lo hi)
  | .quiescentCount _ _ _ (_ :: _) => none


/-- Relabelling the `reapable` flags changes no step. -/
theorem refNet_lstep {noReap : Bool} {X : Reference.TimedNet K} {l : String} {m m' : K → Nat} :
    Reference.LStep (refNet noReap X) l m m' ↔ Reference.LStep X.net l m m' := by
  constructor
  · rintro ⟨t', ht', hn, d, hf⟩
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
    exact ⟨t, ht, hn, d, hf⟩
  · rintro ⟨t, ht, hn, d, hf⟩
    exact ⟨_, List.mem_map.mpr ⟨t, ht, rfl⟩, hn, d, hf⟩

/-- Relabelling the `reapable` flags changes no firing sequence. -/
theorem refNet_run {noReap : Bool} {X : Reference.TimedNet K} :
    ∀ {tr : List String} {a b : K → Nat},
      Reference.Run (refNet noReap X) tr a b ↔ Reference.Run X.net tr a b
  | [], a, b => by
    constructor <;> intro h <;> (obtain rfl := run_nil_eq' h; exact Reference.Run.nil _)
  | l :: ls, a, b => by
    constructor
    · intro h
      obtain ⟨m1, hs, hr⟩ := run_cons_inv' h
      exact Reference.Run.cons (refNet_lstep.mp hs) (refNet_run.mp hr)
    · intro h
      obtain ⟨m1, hs, hr⟩ := run_cons_inv' h
      exact Reference.Run.cons (refNet_lstep.mpr hs) (refNet_run.mpr hr)

/-- Relabelling the `reapable` flags changes no reachable marking. -/
theorem refNet_reach {noReap : Bool} {X : Reference.TimedNet K} {m0 f : K → Nat} :
    Reference.Reach (refNet noReap X) m0 f ↔ Reference.Reach X.net m0 f := by
  have : Reference.Step (refNet noReap X) = Reference.Step X.net := by
    funext m m'
    exact propext (exists_congr fun _ => refNet_lstep)
  unfold Reference.Reach
  rw [this]

omit [DecidableEq K] in
/-- The reference's reap-aware quiescence on `refNet` is VER-002's `VerQuiescent`. -/
theorem refNet_quiescent {noReap : Bool} {X : Reference.TimedNet K} {m : K → Nat} :
    Reference.ReapQuiescent (refNet noReap X) m ↔ VerQuiescent noReap X m := by
  unfold Reference.ReapQuiescent VerQuiescent refNet
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  refine forall_congr' fun t => forall_congr' fun _ => ?_
  simp only [Enabled, Reapable, TimingOf, Bool.and_eq_true, Bool.not_eq_true']

/-- **The translation is exact**: on a property the reference expresses, its `Violates` on
`refNet` is VER-002's reference violation. -/
theorem toRef_violates {noReap : Bool} {X : Reference.TimedNet K} {φ : VerProp K}
    {ψ : Reference.Property K} (h : toRef φ = some ψ) (m : K → Nat) :
    Reference.Violates (refNet noReap X) ψ m ↔ refSafetyViol noReap X φ m := by
  have hq := refNet_quiescent (noReap := noReap) (X := X) (m := m)
  cases φ with
  | deadlockFree sinks cond =>
    cases cond with
    | nil =>
      obtain rfl := (Option.some.inj h).symm
      simp only [Reference.Violates, refSafetyViol, refRestViol, ver002_resting_nil, hq]
    | cons _ _ => simp [toRef] at h
  | terminatesAtSink sinks =>
    obtain rfl := (Option.some.inj h).symm
    simp only [Reference.Violates, refSafetyViol, refRestViol, hq]
  | mutualExclusion ps =>
    obtain rfl := (Option.some.inj h).symm
    simp only [Reference.Violates, refSafetyViol, NTwoMarked]
    have : (fun p => m p != 0) = (fun n => decide (1 ≤ m n)) := by
      funext n; cases m n <;> simp
    rw [this]
  | placeBound p k =>
    obtain rfl := (Option.some.inj h).symm
    exact Iff.rfl
  | unreachable ps =>
    obtain rfl := (Option.some.inj h).symm
    exact Iff.rfl
  | quiescentCount ps lo hi w =>
    cases w with
    | nil =>
      obtain rfl := (Option.some.inj h).symm
      simp only [Reference.Violates, refSafetyViol, ncount, hq]
      simp
    | cons _ _ => simp [toRef] at h

end Dec

/-- The places an output spec names. -/
def outPlaces : Reference.Out K → List K
  | .place p => [p]
  | .and l r => outPlaces l ++ outPlaces r
  | .xor l r => outPlaces l ++ outPlaces r
  | .timeout c => outPlaces c
  | .forward _ dst => [dst]

theorem mem_outPlaces_branches : ∀ (o : Reference.Out K) (b : List K), b ∈ o.branches →
    ∀ x ∈ b, x ∈ outPlaces o
  | .place p, b, hb, x, hx => by
    simp only [Reference.Out.branches, List.mem_singleton] at hb; subst hb; simpa [outPlaces] using hx
  | .forward _ dst, b, hb, x, hx => by
    simp only [Reference.Out.branches, List.mem_singleton] at hb; subst hb; simpa [outPlaces] using hx
  | .and l r, b, hb, x, hx => by
    simp only [Reference.Out.branches, Reference.cross, List.mem_flatMap, List.mem_map] at hb
    obtain ⟨a, ha, c, hc, rfl⟩ := hb
    simp only [outPlaces, List.mem_append] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl (mem_outPlaces_branches l a ha x hx)
    · exact Or.inr (mem_outPlaces_branches r c hc x hx)
  | .xor l r, b, hb, x, hx => by
    simp only [Reference.Out.branches, List.mem_append] at hb
    simp only [outPlaces, List.mem_append]
    rcases hb with hb | hb
    · exact Or.inl (mem_outPlaces_branches l b hb x hx)
    · exact Or.inr (mem_outPlaces_branches r b hb x hx)
  | .timeout c, b, hb, x, hx => by
    simp only [Reference.Out.branches] at hb
    simpa [outPlaces] using mem_outPlaces_branches c b hb x hx

theorem mem_outPlaces_timeout (cn : K → Nat) : ∀ (o : Reference.Out K) (b : List K),
    b ∈ o.timeoutDeposits cn → ∀ x ∈ b, x ∈ outPlaces o
  | .place p, b, hb, x, hx => by
    simp only [Reference.Out.timeoutDeposits, List.mem_singleton] at hb
    subst hb; simpa [outPlaces] using hx
  | .forward _ dst, b, hb, x, hx => by
    simp only [Reference.Out.timeoutDeposits, List.mem_singleton] at hb
    subst hb; simp only [outPlaces, List.mem_singleton]; exact List.eq_of_mem_replicate hx
  | .and l r, b, hb, x, hx => by
    simp only [Reference.Out.timeoutDeposits, Reference.cross, List.mem_flatMap,
      List.mem_map] at hb
    obtain ⟨a, ha, c, hc, rfl⟩ := hb
    simp only [outPlaces, List.mem_append] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl (mem_outPlaces_timeout cn l a ha x hx)
    · exact Or.inr (mem_outPlaces_timeout cn r c hc x hx)
  | .xor l r, b, hb, x, hx => by
    simp only [Reference.Out.timeoutDeposits, List.mem_append] at hb
    simp only [outPlaces, List.mem_append]
    rcases hb with hb | hb
    · exact Or.inl (mem_outPlaces_timeout cn l b hb x hx)
    · exact Or.inr (mem_outPlaces_timeout cn r b hb x hx)
  | .timeout c, b, hb, x, hx => by
    simp only [Reference.Out.timeoutDeposits] at hb
    simpa [outPlaces] using mem_outPlaces_timeout cn c b hb x hx

theorem outPlaces_findTimeout : ∀ {o c : Reference.Out K}, o.findTimeout = some c →
    ∀ x ∈ outPlaces c, x ∈ outPlaces o
  | .place _, _, h, _, _ => by simp [Reference.Out.findTimeout] at h
  | .forward _ _, _, h, _, _ => by simp [Reference.Out.findTimeout] at h
  | .timeout c', c, h, x, hx => by
    simp only [Reference.Out.findTimeout, Option.some.injEq] at h
    subst h; simpa [outPlaces] using hx
  | .and l r, c, h, x, hx => by
    simp only [Reference.Out.findTimeout] at h
    simp only [outPlaces, List.mem_append]
    cases hl : l.findTimeout with
    | some c' =>
      rw [hl, Option.some_or, Option.some.injEq] at h
      subst h; exact Or.inl (outPlaces_findTimeout hl x hx)
    | none =>
      rw [hl, Option.none_or] at h
      exact Or.inr (outPlaces_findTimeout h x hx)
  | .xor l r, c, h, x, hx => by
    simp only [Reference.Out.findTimeout] at h
    simp only [outPlaces, List.mem_append]
    cases hl : l.findTimeout with
    | some c' =>
      rw [hl, Option.some_or, Option.some.injEq] at h
      subst h; exact Or.inl (outPlaces_findTimeout hl x hx)
    | none =>
      rw [hl, Option.none_or] at h
      exact Or.inr (outPlaces_findTimeout h x hx)

section Lin

variable [LinearOrder K]

/-- The reference reads an initial marking as the canonical list of its entries; its counts are
the marking's. -/
theorem get_ofList_count (m0 : NMarking K) :
    Reference.get (Reference.ofList m0.entries) = m0.count := by
  suffices h : ∀ (l : List (K × Nat)) (acc : Reference.Marking K), Reference.Canon acc →
      (l.map Prod.fst).Nodup → ∀ q,
        Reference.get (l.foldl (fun m e => Reference.set m e.1 e.2) acc) q =
          match l.find? (fun e => decide (e.1 = q)) with
          | some e => e.2
          | none => Reference.get acc q by
    funext q
    rw [Reference.ofList, h m0.entries [] Reference.canon_nil m0.nodup q, NMarking.count]
    cases m0.entries.find? (fun e => decide (e.1 = q)) <;> rfl
  intro l
  induction l with
  | nil => intro acc _ _ q; rfl
  | cons e es ih =>
    intro acc hc hnd q
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.foldl_cons]
    rw [ih _ (Reference.canon_set hc e.1 e.2) hnd.2 q]
    by_cases hq : e.1 = q
    · subst hq
      have hnone : es.find? (fun e' => decide (e'.1 = e.1)) = none := by
        rw [List.find?_eq_none]
        intro x hx hxe
        exact hnd.1 (List.mem_map.mpr ⟨x, hx, of_decide_eq_true hxe⟩)
      rw [hnone, List.find?_cons_of_pos (by simp), Reference.get_set hc]
      simp
    · rw [List.find?_cons_of_neg (by simpa using hq)]
      cases es.find? (fun e' => decide (e'.1 = q)) with
      | some _ => rfl
      | none =>
        rw [Reference.get_set hc]
        simp [Ne.symm hq]

/-- Phase 0, **the initial marking**: a violating initial marking is `Violated` with the empty
trace, confirmed. -/
def initialPhase : Phase K := fun o q =>
  match toRef q.prop with
  | none => .aside "the reference decides no conditional sink declaration and no waiver"
  | some ψ =>
    if Reference.violatesB (refNet o.assumeNoReaping q.net) ψ (Reference.ofList q.m0.entries)
    then .decided .violated [] (some true)
    else .aside "the initial marking does not violate the property"

/-- Phase 1, **the dead initial marking**: when the initial marking enables no transition it is
the only reachable marking, so a property it does not violate is `Proven`. The enumeration
route's one-class graph, without the hash map. -/
def deadPhase : Phase K := fun o q =>
  match toRef q.prop with
  | none => .aside "the reference decides no conditional sink declaration and no waiver"
  | some ψ =>
    if q.net.net.transitions.all (fun t => !enabledNA q.init t.core) &&
        !Reference.violatesB (refNet o.assumeNoReaping q.net) ψ (Reference.ofList q.m0.entries)
    then .decided (.proven "enumeration") [] none
    else .aside "the initial marking enables a transition or violates the property"

/-- Phase 2, **the reference enumeration**: `Reference.verdict` over `exploreNet` at the class
budget. -/
def enumPhase [Hashable K] : Phase K := fun o q =>
  match toRef q.prop with
  | none => .aside "the reference decides no conditional sink declaration and no waiver"
  | some ψ =>
    match Reference.verdict (refNet o.assumeNoReaping q.net) ψ (Reference.ofList q.m0.entries)
        o.maxClasses
        (Reference.exploreNet (refNet o.assumeNoReaping q.net) o.maxClasses
          (Reference.ofList q.m0.entries)) with
    | .proven => .decided (.proven "enumeration") [] none
    | .violated tr => .decided .violated tr (some true)
    | .unknown why => .aside why

/-- The reference's `violatesB` at the initial marking is VER-002's violation there. -/
theorem violatesB_init {o : Options} {q : Query K} {ψ : Reference.Property K}
    (h : toRef q.prop = some ψ) :
    Reference.violatesB (refNet o.assumeNoReaping q.net) ψ (Reference.ofList q.m0.entries) = true ↔
      refSafetyViol o.assumeNoReaping q.net q.prop q.init := by
  rw [Reference.violatesB_iff _ _ (Reference.canon_ofList _), get_ofList_count,
    toRef_violates h]
  rfl

/-- From a marking that enables no transition, nothing else is reachable. -/
theorem reach_dead {net : Reference.Net K} {m0 f : K → Nat}
    (hd : ∀ t ∈ net.transitions, enabledNA m0 t.core = false) (h : Reference.Reach net m0 f) :
    f = m0 := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    subst ih
    obtain ⟨_, t, ht, -, d, hf, -⟩ := hs
    rw [hd t ht] at hf
    exact absurd hf Bool.false_ne_true

theorem initialPhase_sound : PhaseSound refSafetyViol (initialPhase (K := K)) := by
  intro o q
  refine ⟨?_, ?_, ?_⟩
  · intro meth tr c h
    unfold initialPhase at h
    split at h
    · simp at h
    · split at h <;> simp at h
  · intro tr h
    unfold initialPhase at h
    split at h
    · simp at h
    · rename_i ψ hψ
      split at h
      · rename_i hv
        simp only [PhaseOut.decided.injEq, true_and] at h
        obtain ⟨rfl, -⟩ := h
        exact ⟨_, Reference.Run.nil _, (violatesB_init hψ).mp hv⟩
      · simp at h
  · intro why tr c h
    unfold initialPhase at h
    split at h
    · simp at h
    · split at h <;> simp at h

theorem deadPhase_sound : PhaseSound refSafetyViol (deadPhase (K := K)) := by
  intro o q
  refine ⟨?_, ?_, ?_⟩
  · intro meth tr c h
    unfold deadPhase at h
    split at h
    · simp at h
    · rename_i ψ hψ
      split at h
      · rename_i hc
        simp only [PhaseOut.decided.injEq, Verdict.proven.injEq] at h
        obtain ⟨rfl, -, -⟩ := h
        simp only [Bool.and_eq_true, List.all_eq_true,
          Bool.not_eq_eq_eq_not, Bool.not_true] at hc
        refine ⟨by decide, fun f hf hv => ?_⟩
        obtain rfl := reach_dead hc.1 hf
        have := (violatesB_init (o := o) hψ).mpr hv
        rw [hc.2] at this
        exact Bool.false_ne_true this
      · simp at h
  · intro tr h
    unfold deadPhase at h
    split at h
    · simp at h
    · split at h <;> simp at h
  · intro why tr c h
    unfold deadPhase at h
    split at h
    · simp at h
    · split at h <;> simp at h

theorem enumPhase_sound [Hashable K] :
    PhaseSound refSafetyViol (enumPhase (K := K)) := by
  intro o q
  have hc := Reference.canon_ofList q.m0.entries
  refine ⟨?_, ?_, ?_⟩
  · intro meth tr c h
    unfold enumPhase at h
    split at h
    · simp at h
    · rename_i ψ hψ
      split at h
      · rename_i hp
        simp only [PhaseOut.decided.injEq, Verdict.proven.injEq] at h
        obtain ⟨rfl, -, -⟩ := h
        refine ⟨by decide, fun f hf hv => ?_⟩
        have hr : Reference.Reach (refNet o.assumeNoReaping q.net)
            (Reference.get (Reference.ofList q.m0.entries)) f := by
          rw [get_ofList_count]; exact refNet_reach.mpr hf
        exact ((Reference.verdict_proven_iff hc ψ).mp hp).2 f hr ((toRef_violates hψ f).mpr hv)
      · simp at h
      · simp at h
  · intro tr h
    unfold enumPhase at h
    split at h
    · simp at h
    · rename_i ψ hψ
      split at h
      · simp at h
      · rename_i tr' hv
        simp only [PhaseOut.decided.injEq, true_and] at h
        obtain ⟨rfl, -⟩ := h
        obtain ⟨f, hr, hvf⟩ := Reference.verdict_violated_run hc hv
        rw [get_ofList_count] at hr
        exact ⟨f, refNet_run.mp hr, (toRef_violates hψ f).mp hvf⟩
      · simp at h
  · intro why tr c h
    unfold enumPhase at h
    split at h
    · simp at h
    · split at h <;> simp at h

/-- **The reference dispatch**: the initial marking, the dead initial marking, the enumeration.
Every step reports the enumeration route, which checks the initial class first. -/
def refSteps [Hashable K] : List (Step K) :=
  [⟨"initial marking", .enumeration, initialPhase⟩,
   ⟨"dead initial marking", .enumeration, deadPhase⟩,
   ⟨"enumeration", .enumeration, enumPhase⟩]

theorem refSteps_sound [Hashable K] :
    ∀ s ∈ refSteps (K := K), PhaseSound refSafetyViol s.run := by
  intro s hs
  simp only [refSteps, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact initialPhase_sound
  · exact deadPhase_sound
  · exact enumPhase_sound

/-- Every step of the reference dispatch reports the enumeration route. -/
theorem refSteps_route [Hashable K] {o : Options} {q : Query K} {r : Route}
    {out : PhaseOut} (h : firstDecided refSteps o q = some (r, out)) : r = .enumeration := by
  obtain ⟨s, hs, rfl, -⟩ := firstDecided_step h
  simp only [refSteps, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl <;> rfl

/-- **An initial violation is decided at once**: when the initial marking violates the
property, the reference dispatch either decides nothing or decides `Violated` with the empty
trace, confirmed. -/
theorem refSteps_initial [Hashable K] {o : Options} {q : Query K}
    (h : refSafetyViol o.assumeNoReaping q.net q.prop q.init) :
    firstDecided refSteps o q = none ∨
      firstDecided refSteps o q = some (.enumeration, .decided .violated [] (some true)) := by
  cases hψ : toRef q.prop with
  | none =>
    left
    apply firstDecided_none
    intro s hs
    simp only [refSteps, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> simp [initialPhase, deadPhase, enumPhase, hψ]
  | some ψ =>
    right
    have hv := (violatesB_init (o := o) hψ).mpr h
    exact firstDecided_head (by simp [initialPhase, hψ, hv])

/-! ## The invariants of the untouched places -/

/-- No transition of `net` touches the place `p`: no input, reset or output names it. -/
def untouchedB (net : Reference.Net K) (p : K) : Bool :=
  net.transitions.all fun t =>
    t.core.inputs.all (fun s => decide (s.place ≠ p)) && !decide (p ∈ t.core.resets) &&
      match t.out with
      | none => true
      | some o => !decide (p ∈ outPlaces o)

/-- **The invariants the reference reports**: weight 1 on each declared place no transition
touches, its constant the initial count. VER-001's inert places are such places. -/
def inertInvariants (q : Query K) : List (PInv K) :=
  (q.net.net.places.filter (untouchedB q.net.net)).map fun p => ⟨[(p, 1)], (q.init p : Int)⟩

omit [LinearOrder K] in
/-- A deposit names only places of the output spec. -/
theorem mem_deposit {cn : K → Nat} {out : Option (Reference.Out K)}
    {ch : Novel.ForwardDeposit.Choice} {d : List K} (h : Reference.deposit cn out ch = some d)
    {x : K} (hx : x ∈ d) : ∃ o, out = some o ∧ x ∈ outPlaces o := by
  cases out with
  | none =>
    cases ch with
    | action i =>
      cases i with
      | zero => simp only [Reference.deposit, Option.some.injEq] at h; subst h; simp at hx
      | succ _ => simp [Reference.deposit] at h
    | timedOut _ => simp [Reference.deposit] at h
  | some o =>
    refine ⟨o, rfl, ?_⟩
    cases ch with
    | action i =>
      simp only [Reference.deposit] at h
      exact mem_outPlaces_branches o d (List.mem_of_getElem? h) x hx
    | timedOut j =>
      simp only [Reference.deposit] at h
      cases hc : o.findTimeout with
      | none => rw [hc] at h; simp at h
      | some c =>
        rw [hc, Option.bind_some] at h
        exact outPlaces_findTimeout hc x
          (mem_outPlaces_timeout cn c d (List.mem_of_getElem? h) x hx)

/-- A firing leaves an untouched place as it was. -/
theorem fires_untouched {net : Reference.Net K} {p : K} (hp : untouchedB net p = true)
    {t : Reference.Trans K} (ht : t ∈ net.transitions) {m m' : K → Nat} {d : List K}
    (hf : Reference.Fires t m d m') : m' p = m p := by
  obtain ⟨-, ⟨ch, hd⟩, rfl⟩ := hf
  have hu := List.all_eq_true.mp hp t ht
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not] at hu
  obtain ⟨⟨hin, hres⟩, hout⟩ := hu
  have hcount : d.count p = 0 := by
    rw [List.count_eq_zero]
    intro hx
    obtain ⟨o, ho, hxo⟩ := mem_deposit hd hx
    rw [ho] at hout
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hout
    exact hout hxo
  have hns : nspecAt t.core p = none := by
    unfold nspecAt
    rw [List.find?_eq_none]
    intro s hs
    simpa using hin s hs
  simp only [fireNC, depProd, hres, if_false, nconsumed, hns, hcount]
  omega

/-- The reported invariants are conserved on every reachable marking. -/
theorem inertInvariants_conserved (q : Query K) :
    ∀ i ∈ inertInvariants q, ∀ f, ReachF RefFire q.net.net q.init f → i.dot f = i.const := by
  intro i hi f hf
  simp only [inertInvariants, List.mem_map, List.mem_filter] at hi
  obtain ⟨p, ⟨-, hp⟩, rfl⟩ := hi
  have : f p = q.init p := by
    induction hf with
    | refl => rfl
    | tail _ hs ih =>
      obtain ⟨_, t, ht, -, d, hfi⟩ := hs
      rw [fires_untouched hp ht hfi, ih]
  simp [PInv.dot, this]

/-! ## The reference decider -/

/-- **The reference dispatch and packing**, after the unresolved-place check: build the verified
query; dispatch over `refSteps`; report the deciding route, the trace, the confirmation, the
timing label (`UNTIMED_NET` on an untimed net, `UNTIMED_ABSTRACTION` otherwise: the timed check
of [VER-023] is not modelled) and the invariants of the untouched places. -/
def refDispatch [Hashable K] (abs : Abs K) : Decider K := fun o X φ m0 =>
  match abs o X φ m0 with
  | .error why =>
    { verdict := .unknown "the verified net cannot be built", notes := [why] }
  | .ok q =>
    match firstDecided refSteps o q with
    | some (route, .decided v tr c) =>
      { verdict := v, route, trace := tr, confirmed := c,
        timing := if v = .violated then
          some (if Untimed X then .untimedNet else .untimedAbstraction) else none,
        invariants := inertInvariants q }
    | _ => { verdict := .unknown "no route decided", invariants := inertInvariants q }

/-- **The reference decider**, for any verified-net function `abs`: refuse an unresolved
property place before any route runs, then `refDispatch`. -/
def refVerify [Hashable K] (abs : Abs K) : Decider K := fun o X φ m0 =>
  if Unresolved X φ m0 then
    { verdict := .unknown
        "the property names a place that the net does not declare and the initial marking does not mark" }
  else refDispatch abs o X φ m0

#spec_witness refVerify

end Lin

end Verifier

end Libpetri.Spec
