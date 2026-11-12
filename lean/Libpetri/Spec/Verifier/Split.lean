import Libpetri.Spec.Verifier.Result

set_option linter.missingDocs true
set_option autoImplicit false

/-!
# The in-flight split on named nets (RefVerifier L4, [VER-004])

Every route reads a firing as one atomic step. The executor does not: it consumes a firing's
inputs when the action starts and deposits the outputs when the action completes, and other
transitions fire in between ([EXEC-001], [CONC-002], [EXEC-003] AC5). [VER-004] makes the
verified net model that gap for every transition whose output some transition tests
non-monotonically. This file is the named-net function that does it, `refSplit`, the reference
for `in_flight.rs` `split_in_flight_for` (Java `InFlightSplit`, TypeScript `in-flight.ts`).

**Which transitions split** (`splits`, `in_flight_transitions_for`): in net order, every
transition that is not itself a completion step and not an environment step, and that either is
forced by the demand or has an output place in the tested set. The tested set is
`nonMonotone` (every terminal place, and every place some transition tests with an inhibitor, a
reset or a draining input `all` / `atLeast`), plus the places the demand adds
(`SplitCfg.tested`: `quiescent_count_demand`'s counted and waiver places, `conflict_demand`'s
pruner inputs and reads). `SplitCfg.forced` is `conflict_demand`'s pruners.

**The shape** (`halves`): a split `t` becomes
* `startHalf t`: `t` with every arc, its timing and its name, whose only output is the place
  `inflight:<t>`;
* `endHalf t`, named `complete:<t>`: the one input `one(inflight:<t>)`, `t`'s output spec with
  every `forwardInput(from, to)` leaf read as the place `to` (`completionOut`), immediate and not
  reapable.
The completion step follows `t` at once in the transition list, and the in-flight places follow
the net's own places in the order of the split transitions (`splitNet`).

**The refusals** (`refusal`, `refusal_cause`): a split transition that is a ν-join, that writes a
coloured place (a match key, a relay target or a declared carrier), whose `Timeout` forwards an
input that is not `one` (`multiFwd`), or whose added names the net already uses. The first
refusal in net order makes `refSplit` an error, so every route answers `Unknown` ([VER-003]
line 4). Under `assumeAtomicFiring`, and when nothing needs the split, the net is returned
unchanged ([VER-004] AC5: the same net, so the same scripts).

## Results

* `refSplit_atomic`, `refSplit_nil`, `refSplit_ok`, `refSplit_error_iff`, `mem_splits`: the
  function, read clause by clause.
* `branches_completionOut`, `findTimeout_completionOut`, `timeoutDeposits_completionOut`: the
  completion step deposits what the transition deposits. A forward from a `one` input deposits
  one token either way; that is why a forward from any other input is refused.
* **`run_splitNet`** (the split only adds runs): every firing sequence of the net, from a marking
  that holds nothing on the in-flight places, is a firing sequence of the split net with each
  split label `t` followed at once by `complete:<t>` (`expandLabels`), ending in the same
  marking. `reach_splitNet` is the reachability form. So a safety `Proven` on the split net is
  a `Proven` on the atomic net, and a `Violated` the split net finds may be one only the
  executor's gap allows: that is the point of the split.
* **`quiescent_no_inflight`**: a marking of the split net that rests, read as [VER-002] reads
  quiescence (reap-aware or plain), holds no token on an in-flight place. A marked in-flight
  place never rests: its completion step is enabled, immediate and not reapable.
* Worked examples (`ex*`, by `decide` through `refVerify`): the AC4 inhibitor net, `Violated`
  with the split and `Proven` under `assumeAtomicFiring`; the refusals of AC6.

## Not modelled here (deferred)

* The executor side (block B): that every RefExec run with actions in flight is covered by the
  split net (`InFlight.split_covers_executor`, `split_rest_sound` lifted from flat rows) needs
  RefExec and is wave W11. Block A (every `RefTStep` marking is `Reference.Reach`-reachable,
  every rest reap-quiescent) is `Bridges.refReach_reach` and `Bridges.ref_rest_reapable`.
* The terminal rewrite of [EXEC-042] after the split (`Novel/TerminalRewrite.lean`, flat).
  `Reference.Net` carries no terminal list; `SplitCfg.terminals` only feeds the tested set.
* Priorities and match specs: `Reference.Trans` has neither. The ν-join test reads
  `SplitCfg.joins`, the coloured test `SplitCfg.coloured`; the conflict-priority switch-off
  (a refused pruner turns pruning off instead of refusing) is the caller's.
* Report text: the split note, the atomic-assumption note, the CONC-002 restart note (kind Q).
  The refusal text is modelled with Rust's heads; the coloured place is named as it is found in
  output order, where Rust names the first in sorted order.
-/

namespace Libpetri.Spec.Verifier.Split

open Libpetri Libpetri.Novel.Seam

variable {K : Type}

/-! ## Names and configuration -/

/-- The completion step's name, `complete:<t>` (`completion_transition`). -/
def completeName (t : String) : String := "complete:" ++ t

/-- What the split reads besides the net (`split_in_flight_for`'s arguments and the net's
terminal places). -/
structure SplitCfg (K : Type) where
  /-- The place `inflight:<t>` of transition `t` (`in_flight_place`). -/
  inflight  : String → K
  /-- A place's name, for the name-clash test and the refusal text. -/
  render    : K → String
  /-- The terminal places ([EXEC-042]); each counts as a non-monotone test. -/
  terminals : List K := []
  /-- The coloured places: declared carriers, match keys and relay targets. -/
  coloured  : List K := []
  /-- The ν-join transitions (those with a match spec). -/
  joins     : List String := []
  /-- The environment steps, which stay atomic (arrivals of [VER-006], the contract
  environment of [VER-022]). -/
  envTrans  : List String := []
  /-- `SplitDemand.tested`: places whose depositors split. -/
  tested    : List K := []
  /-- `SplitDemand.forced`: transitions split whatever their outputs. -/
  forced    : List String := []

/-! ## Output specs -/

/-- The forward sources of an output spec. -/
def fwdSrcs : Reference.Out K → List K
  | .place _ => []
  | .and l r => fwdSrcs l ++ fwdSrcs r
  | .xor l r => fwdSrcs l ++ fwdSrcs r
  | .timeout c => fwdSrcs c
  | .forward s _ => [s]

/-- **The completion step's output spec** (`completion_output`): a `forwardInput(from, to)`
leaf becomes the place `to`. -/
def completionOut : Reference.Out K → Reference.Out K
  | .place p => .place p
  | .and l r => .and (completionOut l) (completionOut r)
  | .xor l r => .xor (completionOut l) (completionOut r)
  | .timeout c => .timeout (completionOut c)
  | .forward _ d => .place d

/-- The completion step writes the same branches. -/
theorem branches_completionOut : ∀ o : Reference.Out K,
    (completionOut o).branches = o.branches
  | .place _ => rfl
  | .forward _ _ => rfl
  | .and l r => by
    simp only [completionOut, Reference.Out.branches, branches_completionOut l,
      branches_completionOut r]
  | .xor l r => by
    simp only [completionOut, Reference.Out.branches, branches_completionOut l,
      branches_completionOut r]
  | .timeout c => by simp only [completionOut, Reference.Out.branches, branches_completionOut c]

/-- The completion step's `Timeout` node is the transition's, rewritten. -/
theorem findTimeout_completionOut : ∀ o : Reference.Out K,
    (completionOut o).findTimeout = o.findTimeout.map completionOut
  | .place _ => rfl
  | .forward _ _ => rfl
  | .timeout _ => rfl
  | .and l r => by
    simp only [completionOut, Reference.Out.findTimeout, findTimeout_completionOut l,
      findTimeout_completionOut r]
    cases l.findTimeout <;> rfl
  | .xor l r => by
    simp only [completionOut, Reference.Out.findTimeout, findTimeout_completionOut l,
      findTimeout_completionOut r]
    cases l.findTimeout <;> rfl

/-- The completion step deposits on a timeout what the transition does, when every forward
source was consumed once. -/
theorem timeoutDeposits_completionOut (c c' : K → Nat) : ∀ o : Reference.Out K,
    (∀ s ∈ fwdSrcs o, c s = 1) →
      (completionOut o).timeoutDeposits c' = o.timeoutDeposits c
  | .place _, _ => rfl
  | .forward s _, h => by
    have : c s = 1 := h s (by simp [fwdSrcs])
    simp [completionOut, Reference.Out.timeoutDeposits, this]
  | .and l r, h => by
    simp only [completionOut, Reference.Out.timeoutDeposits]
    rw [timeoutDeposits_completionOut c c' l (fun s hs => h s (by simp [fwdSrcs, hs])),
      timeoutDeposits_completionOut c c' r (fun s hs => h s (by simp [fwdSrcs, hs]))]
  | .xor l r, h => by
    simp only [completionOut, Reference.Out.timeoutDeposits]
    rw [timeoutDeposits_completionOut c c' l (fun s hs => h s (by simp [fwdSrcs, hs])),
      timeoutDeposits_completionOut c c' r (fun s hs => h s (by simp [fwdSrcs, hs]))]
  | .timeout ch, h => by
    simp only [completionOut, Reference.Out.timeoutDeposits]
    exact timeoutDeposits_completionOut c c' ch (fun s hs => h s (by simpa [fwdSrcs] using hs))

/-- The forward sources of a `Timeout` child are forward sources of the spec. -/
theorem fwdSrcs_findTimeout : ∀ {o ch : Reference.Out K}, o.findTimeout = some ch →
    ∀ s ∈ fwdSrcs ch, s ∈ fwdSrcs o
  | .place _, _, h, _, _ => by simp [Reference.Out.findTimeout] at h
  | .forward _ _, _, h, _, _ => by simp [Reference.Out.findTimeout] at h
  | .timeout _, _, h, s, hs => by
    simp only [Reference.Out.findTimeout, Option.some.injEq] at h
    subst h; simpa [fwdSrcs] using hs
  | .and l r, ch, h, s, hs => by
    simp only [Reference.Out.findTimeout] at h
    cases hl : l.findTimeout with
    | some c =>
      rw [hl, Option.some_or, Option.some.injEq] at h; subst h
      simp [fwdSrcs, fwdSrcs_findTimeout hl s hs]
    | none =>
      rw [hl, Option.none_or] at h
      simp [fwdSrcs, fwdSrcs_findTimeout h s hs]
  | .xor l r, ch, h, s, hs => by
    simp only [Reference.Out.findTimeout] at h
    cases hl : l.findTimeout with
    | some c =>
      rw [hl, Option.some_or, Option.some.injEq] at h; subst h
      simp [fwdSrcs, fwdSrcs_findTimeout hl s hs]
    | none =>
      rw [hl, Option.none_or] at h
      simp [fwdSrcs, fwdSrcs_findTimeout h s hs]

/-! ## Which transitions split -/

/-- The output places of a transition (none without an output spec). -/
def outs (t : Reference.Trans K) : List K :=
  match t.out with
  | none => []
  | some o => outPlaces o

/-- The places a transition drains (`all`, `atLeast` inputs). -/
def drainPlaces (t : Reference.Trans K) : List K :=
  (t.core.inputs.filter (fun s => s.card.consumesAll)).map (·.place)

/-- **The non-monotone places** (`non_monotone_places`): every terminal, and every place some
transition tests with an inhibitor, a reset or a draining input. -/
def nonMonotone (cfg : SplitCfg K) (net : Reference.Net K) : List K :=
  cfg.terminals ++ net.transitions.flatMap fun t =>
    t.core.inhibitors ++ t.core.resets ++ drainPlaces t

/-- Every place of a transition: its arc places and its output places. -/
def transPlaces (t : Reference.Trans K) : List K :=
  t.core.inputs.map (·.place) ++ t.core.inhibitors ++ t.core.reads ++ t.core.resets ++ outs t

/-- Every place of a net: the declared ones and every place an arc or an output spec names. -/
def allPlaces (net : Reference.Net K) : List K :=
  net.places ++ net.transitions.flatMap transPlaces

/-- Every name a net uses: its places, rendered, and its transitions (one name space, as in
Rust's `names` set). -/
def usedNames (cfg : SplitCfg K) (net : Reference.Net K) : List String :=
  (allPlaces net).map cfg.render ++ net.transitions.map (·.core.name)

section Dec

variable [DecidableEq K]

/-- **A completion step** (`is_completion`): named `complete:<x>`, with the one input
`one(inflight:<x>)` and no read or reset arc. It is never split again. -/
def isCompletion (cfg : SplitCfg K) (t : Reference.Trans K) : Bool :=
  "complete:".toList.isPrefixOf t.core.name.toList &&
    (match t.core.inputs with
     | [s] => s.card == .one &&
         decide (s.place = cfg.inflight (String.ofList (t.core.name.toList.drop 9)))
     | _ => false) &&
    t.core.reads.isEmpty && t.core.resets.isEmpty

/-- Whether `t` splits (`in_flight_transitions_for`'s filter). -/
def splitB (cfg : SplitCfg K) (net : Reference.Net K) (t : Reference.Trans K) : Bool :=
  !isCompletion cfg t && !decide (t.core.name ∈ cfg.envTrans) &&
    (decide (t.core.name ∈ cfg.forced) ||
      (outs t).any fun p => decide (p ∈ nonMonotone cfg net) || decide (p ∈ cfg.tested))

/-- **The split transitions**, in net order (`in_flight_transitions_for`). -/
def splits (cfg : SplitCfg K) (net : Reference.Net K) : List String :=
  (net.transitions.filter (splitB cfg net)).map (·.core.name)

/-- **Which transitions split**, clause by clause. -/
theorem mem_splits (cfg : SplitCfg K) (net : Reference.Net K) (n : String) :
    n ∈ splits cfg net ↔ ∃ t ∈ net.transitions, t.core.name = n ∧
      isCompletion cfg t = false ∧ t.core.name ∉ cfg.envTrans ∧
      (t.core.name ∈ cfg.forced ∨ ∃ p ∈ outs t, p ∈ nonMonotone cfg net ∨ p ∈ cfg.tested) := by
  simp only [splits, List.mem_map, List.mem_filter, splitB, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true]
  constructor
  · rintro ⟨t, ⟨ht, ⟨hc, he⟩, hs⟩, rfl⟩
    exact ⟨t, ht, rfl, hc, he, hs⟩
  · rintro ⟨t, ht, rfl, hc, he, hs⟩
    exact ⟨t, ⟨ht, ⟨hc, he⟩, hs⟩, rfl⟩

/-- The first forward under a `Timeout` whose source input is not `one` (`multi_token_forward`;
a source that is no input counts as single, as in Rust, and the builder rejects it anyway,
[IO-014] AC3). -/
def multiFwdIn (t : Reference.Trans K) : Bool → Reference.Out K → Option (K × K)
  | _, .place _ => none
  | u, .forward s d =>
    let single := match nspecAt t.core s with
      | none => true
      | some sp => sp.card == .one
    if u && !single then some (s, d) else none
  | _, .timeout c => multiFwdIn t true c
  | u, .and l r => (multiFwdIn t u l).or (multiFwdIn t u r)
  | u, .xor l r => (multiFwdIn t u l).or (multiFwdIn t u r)

/-- `multi_token_forward` of a transition's output spec. -/
def multiFwd (t : Reference.Trans K) : Option (K × K) :=
  t.out.bind (multiFwdIn t false)

/-- **Why `t` cannot be split** (`refusal_cause`), if it cannot: a ν-join, a coloured writer, a
multi-token timeout forward, or a name the split would add that the net already uses. -/
def refusal (cfg : SplitCfg K) (net : Reference.Net K) (t : Reference.Trans K) :
    Option String :=
  let n := t.core.name
  if n ∈ cfg.joins then
    some "it is a ν-join, whose outputs carry the matched name (NU-020, NU-054)"
  else match (outs t).find? (fun p => decide (p ∈ cfg.coloured)) with
  | some p => some ("it writes the coloured place '" ++ cfg.render p ++
      "', whose tokens carry a ν name")
  | none => match multiFwd t with
    | some (s, d) => some ("its timeout forwards input '" ++ cfg.render s ++ "' to '" ++
        cfg.render d ++ "', one token per token consumed (IO-014), " ++
        "a count its completion step cannot see")
    | none =>
      if cfg.render (cfg.inflight n) ∈ usedNames cfg net then
        some ("the net already uses the name '" ++ cfg.render (cfg.inflight n) ++
          "' the split would add")
      else if completeName n ∈ usedNames cfg net then
        some ("the net already uses the name '" ++ completeName n ++ "' the split would add")
      else none

/-- The opening of a refusal (`refusal_head`, or `demand_refusal_head` when only the demand
splits `t`). -/
def refusalHead (cfg : SplitCfg K) (net : Reference.Net K) (n : String) : String :=
  if n ∈ splits { cfg with tested := [], forced := [] } net then
    "transition '" ++ n ++ "' must be verified as two steps, since its action runs between " ++
      "consuming and depositing and another transition tests one of its outputs with an " ++
      "inhibitor, reset or drain (VER-004), but"
  else
    "transition '" ++ n ++ "' must be verified as two steps, since a terminal place can stop " ++
      "the net while its action runs and the property's lower bound counts a place it " ++
      "deposits into (VER-004, EXEC-042), but"

/-- The first refusal among the split transitions, in net order (`first_unsplittable`). -/
def firstRefusal (cfg : SplitCfg K) (net : Reference.Net K) (sp : List String) :
    Option String :=
  (net.transitions.filter (fun t => decide (t.core.name ∈ sp))).findSome? fun t =>
    (refusal cfg net t).map fun c => refusalHead cfg net t.core.name ++ " " ++ c

end Dec

/-! ## The split net -/

/-- The start half of a split `t` (`halves`): every arc, its name and reapability, and the one
output `inflight:<t>`. -/
def startHalf (cfg : SplitCfg K) (t : Reference.Trans K) : Reference.Trans K :=
  { t with out := some (.place (cfg.inflight t.core.name)) }

/-- The completion step `complete:<t>`: the one input `one(inflight:<t>)`, `t`'s output spec
through `completionOut`, not reapable. -/
def endHalf (cfg : SplitCfg K) (t : Reference.Trans K) : Reference.Trans K :=
  { core := { name := completeName t.core.name,
              inputs := [⟨cfg.inflight t.core.name, .one⟩],
              inhibitors := [], reads := [], resets := [] },
    out := t.out.map completionOut,
    reapable := false }

/-- What one transition becomes. -/
def halves (cfg : SplitCfg K) (sp : List String) (t : Reference.Trans K) :
    List (Reference.Trans K) :=
  if t.core.name ∈ sp then [startHalf cfg t, endHalf cfg t] else [t]

/-- **The split net**: each split transition followed by its completion step; the in-flight
places after the net's own places, in the order of the split transitions. -/
def splitNet (cfg : SplitCfg K) (sp : List String) (net : Reference.Net K) : Reference.Net K :=
  { places := net.places ++
      (net.transitions.filter (fun t => decide (t.core.name ∈ sp))).map
        (fun t => cfg.inflight t.core.name),
    transitions := net.transitions.flatMap (halves cfg sp) }

/-- The split net's timing, by name: a transition of the net keeps its timing (the start half
keeps its transition's); a completion step, whose name the net does not use, is `immediate`. -/
def splitTiming (X : Reference.TimedNet K) (u : Reference.Trans K) : Novel.TimedScg.Timing :=
  match X.net.transitions.find? (fun t => t.core.name == u.core.name) with
  | some t => X.timing t
  | none => .immediate

/-- The split timed net. -/
def splitTimed (cfg : SplitCfg K) (sp : List String) (X : Reference.TimedNet K) :
    Reference.TimedNet K :=
  { net := splitNet cfg sp X.net, timing := splitTiming X, tol := X.tol }

/-- **The in-flight split** (`split_in_flight_for` with `with_in_flight`'s opt-out): under
`assumeAtomicFiring`, or when nothing needs the split, the net unchanged with no split list;
the first refusal as an error; otherwise the split net and the split transitions. -/
def refSplit [DecidableEq K] (cfg : SplitCfg K) (o : Options) (X : Reference.TimedNet K) :
    Except String (Reference.TimedNet K × List String) :=
  if o.assumeAtomicFiring then .ok (X, [])
  else
    let sp := splits cfg X.net
    if sp = [] then .ok (X, [])
    else match firstRefusal cfg X.net sp with
      | some r => .error r
      | none => .ok (splitTimed cfg sp X, sp)

/-- `refSplit` as a verified-net function: the split timed net with the property and the
initial marking unchanged, or the refusal. -/
def splitAbs [DecidableEq K] (cfg : SplitCfg K) : Abs K := fun o X φ m0 =>
  match refSplit cfg o X with
  | .ok (Y, _) => .ok ⟨Y, φ, m0⟩
  | .error e => .error e

#spec_witness refSplit

/-! ## `refSplit`, clause by clause -/

section Clauses

variable [DecidableEq K]

/-- **Opt-out** ([VER-004] AC6): under `assumeAtomicFiring` the net is verified unchanged. -/
theorem refSplit_atomic (cfg : SplitCfg K) {o : Options} (X : Reference.TimedNet K)
    (h : o.assumeAtomicFiring = true) : refSplit cfg o X = .ok (X, []) := by
  simp [refSplit, h]

/-- **Nothing to split, nothing changes** ([VER-004] AC5): the verified net is the net itself. -/
theorem refSplit_nil (cfg : SplitCfg K) (o : Options) (X : Reference.TimedNet K)
    (h : splits cfg X.net = []) : refSplit cfg o X = .ok (X, []) := by
  unfold refSplit
  split <;> simp [h]

/-- What a successful split returns: the net unchanged with no split list, or the split net of
exactly the transitions `splits` names, none of them refused. -/
theorem refSplit_ok {cfg : SplitCfg K} {o : Options} {X Y : Reference.TimedNet K}
    {sp : List String} (h : refSplit cfg o X = .ok (Y, sp)) :
    (sp = [] ∧ Y = X) ∨
      (o.assumeAtomicFiring = false ∧ sp = splits cfg X.net ∧ sp ≠ [] ∧
        firstRefusal cfg X.net sp = none ∧ Y = splitTimed cfg sp X) := by
  unfold refSplit at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact Or.inl ⟨h.2.symm, h.1.symm⟩
  · rename_i hat
    simp only at h
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact Or.inl ⟨h.2.symm, h.1.symm⟩
    · rename_i hne
      split at h
      · simp at h
      · rename_i hr
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Or.inr ⟨by simpa using hat, rfl, hne, hr, rfl⟩

/-- **The refusal** ([VER-004] AC6): with the opt-out off, the split is refused exactly when some
transition that splits cannot be split. -/
theorem refSplit_error_iff (cfg : SplitCfg K) {o : Options} (X : Reference.TimedNet K)
    (hat : o.assumeAtomicFiring = false) :
    (∃ e, refSplit cfg o X = .error e) ↔
      ∃ t ∈ X.net.transitions, t.core.name ∈ splits cfg X.net ∧ refusal cfg X.net t ≠ none := by
  have key : (firstRefusal cfg X.net (splits cfg X.net)).isSome ↔
      ∃ t ∈ X.net.transitions, t.core.name ∈ splits cfg X.net ∧
        refusal cfg X.net t ≠ none := by
    unfold firstRefusal
    rw [List.findSome?_isSome_iff]
    simp only [List.mem_filter, decide_eq_true_eq, Option.isSome_map]
    constructor
    · rintro ⟨t, ⟨ht, hs⟩, hr⟩; exact ⟨t, ht, hs, Option.isSome_iff_ne_none.mp hr⟩
    · rintro ⟨t, ht, hs, hr⟩; exact ⟨t, ⟨ht, hs⟩, Option.isSome_iff_ne_none.mpr hr⟩
  rw [← key]
  unfold refSplit
  simp only [hat, Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i hnil
    simp only [reduceCtorEq, exists_false, false_iff]
    simp [firstRefusal, hnil]
  · split
    · rename_i r hr; simp [hr]
    · rename_i hr; simp [hr]

/-- A refusal-free transition adds names the net does not use. -/
theorem refusal_none_fresh {cfg : SplitCfg K} {net : Reference.Net K} {t : Reference.Trans K}
    (h : refusal cfg net t = none) :
    cfg.render (cfg.inflight t.core.name) ∉ usedNames cfg net ∧
      completeName t.core.name ∉ usedNames cfg net ∧ multiFwd t = none := by
  unfold refusal at h
  simp only at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i hm
        split at h
        · simp at h
        · rename_i h1
          split at h
          · simp at h
          · rename_i h2
            exact ⟨h1, h2, hm⟩

/-- A refusal-free split list: every split transition passes the refusal test. -/
theorem firstRefusal_none {cfg : SplitCfg K} {net : Reference.Net K} {sp : List String}
    (h : firstRefusal cfg net sp = none) {t : Reference.Trans K} (ht : t ∈ net.transitions)
    (hn : t.core.name ∈ sp) : refusal cfg net t = none := by
  unfold firstRefusal at h
  rw [List.findSome?_eq_none_iff] at h
  have := h t (List.mem_filter.mpr ⟨ht, by simpa using hn⟩)
  simpa using this

end Clauses

/-! ## Firing sequences: append and reachability -/

section Runs

variable [DecidableEq K]

/-- Two firing sequences, one after the other. -/
theorem run_append {net : Reference.Net K} : ∀ {tr1 tr2 : List String} {a b c : K → Nat},
    Reference.Run net tr1 a b → Reference.Run net tr2 b c → Reference.Run net (tr1 ++ tr2) a c
  | [], _, _, _, _, h1, h2 => by cases h1; exact h2
  | _ :: _, _, _, _, _, h1, h2 => by
    cases h1 with
    | cons hs hr => exact Reference.Run.cons hs (run_append hr h2)

/-- A firing sequence and one more step. -/
theorem run_snoc {net : Reference.Net K} {tr : List String} {l : String} {a b c : K → Nat}
    (h : Reference.Run net tr a b) (hs : Reference.LStep net l b c) :
    Reference.Run net (tr ++ [l]) a c :=
  run_append h (Reference.Run.cons hs (Reference.Run.nil c))

/-- A reachable marking is the end of some firing sequence. -/
theorem reach_run {net : Reference.Net K} {a b : K → Nat} (h : Reference.Reach net a b) :
    ∃ tr, Reference.Run net tr a b := by
  induction h with
  | refl => exact ⟨[], Reference.Run.nil _⟩
  | tail _ hs ih =>
    obtain ⟨tr, hr⟩ := ih
    obtain ⟨l, hl⟩ := hs
    exact ⟨_, run_snoc hr hl⟩

/-- The end of a firing sequence is reachable. -/
theorem run_reach {net : Reference.Net K} : ∀ {tr : List String} {a b : K → Nat},
    Reference.Run net tr a b → Reference.Reach net a b
  | [], _, _, h => by cases h; exact Relation.ReflTransGen.refl
  | _ :: _, _, _, h => by
    cases h with
    | cons hs hr => exact Relation.ReflTransGen.head ⟨_, hs⟩ (run_reach hr)

end Runs

/-! ## The split only adds runs -/

section Sem

variable [LinearOrder K]

/-- The labels of a firing sequence of the net as the split net fires them: each split label
`t` followed at once by `complete:<t>`. -/
def expandLabels (sp : List String) (tr : List String) : List String :=
  tr.flatMap fun l => if l ∈ sp then [l, completeName l] else [l]

/-- No in-flight place of a split transition is an arc or output place of the net. -/
def Fresh (cfg : SplitCfg K) (sp : List String) (net : Reference.Net K) : Prop :=
  ∀ t ∈ net.transitions, t.core.name ∈ sp → cfg.inflight t.core.name ∉ allPlaces net

/-- Every forward a split transition's `Timeout` makes is from a `one` input ([IO-014] AC3 and
the refusal of AC6). -/
def OneFwd (sp : List String) (net : Reference.Net K) : Prop :=
  ∀ t ∈ net.transitions, t.core.name ∈ sp → ∀ o, t.out = some o → ∀ ch, o.findTimeout = some ch →
    ∀ s ∈ fwdSrcs ch, ∃ spec, nspecAt t.core s = some spec ∧ spec.card = .one

/-- Nothing in flight: every in-flight place of a split transition is empty. -/
def Idle (cfg : SplitCfg K) (sp : List String) (net : Reference.Net K) (m : K → Nat) : Prop :=
  ∀ t ∈ net.transitions, t.core.name ∈ sp → m (cfg.inflight t.core.name) = 0

/-- A place a transition does not name keeps its count when the transition fires. -/
theorem fires_frame {t : Reference.Trans K} {m m' : K → Nat} {d : List K} {q : K}
    (hq : q ∉ transPlaces t) (h : Reference.Fires t m d m') : m' q = m q := by
  obtain ⟨_, ⟨ch, hd⟩, rfl⟩ := h
  have hres : q ∉ t.core.resets := fun hr => hq (by simp [transPlaces, hr])
  have hin : nspecAt t.core q = none := by
    unfold nspecAt
    rw [List.find?_eq_none]
    intro s hs hsq
    exact hq (by
      have : s.place = q := by simpa using hsq
      simp only [transPlaces, List.mem_append, List.mem_map]
      exact Or.inl (Or.inl (Or.inl (Or.inl ⟨s, hs, this⟩))))
  have hd0 : d.count q = 0 := by
    rw [List.count_eq_zero]
    intro hx
    obtain ⟨o, ho, hx⟩ := mem_deposit hd hx
    exact hq (by simp [transPlaces, outs, ho, hx])
  simp [fireNC, hres, nconsumed, hin, depProd, hd0]

/-- A place no transition names keeps its count along every firing sequence. -/
theorem run_frame {net : Reference.Net K} {q : K} (hq : q ∉ allPlaces net) :
    ∀ {tr : List String} {a b : K → Nat}, Reference.Run net tr a b → b q = a q
  | [], _, _, h => by cases h; rfl
  | _ :: _, _, _, h => by
    cases h with
    | cons hs hr =>
      obtain ⟨t, ht, _, d, hf⟩ := hs
      rw [run_frame hq hr]
      exact fires_frame (fun h => hq (by
        simp only [allPlaces, List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨t, ht, h⟩)) hf

omit [LinearOrder K] in
/-- A transition of the net is in the split net, as itself or as its two halves. -/
theorem mem_splitNet_of {cfg : SplitCfg K} {sp : List String} {net : Reference.Net K}
    {t : Reference.Trans K} (ht : t ∈ net.transitions) :
    (t.core.name ∉ sp → t ∈ (splitNet cfg sp net).transitions) ∧
      (t.core.name ∈ sp → startHalf cfg t ∈ (splitNet cfg sp net).transitions ∧
        endHalf cfg t ∈ (splitNet cfg sp net).transitions) := by
  refine ⟨fun hn => List.mem_flatMap.mpr ⟨t, ht, by simp [halves, hn]⟩,
    fun hn => ⟨List.mem_flatMap.mpr ⟨t, ht, by simp [halves, hn]⟩,
      List.mem_flatMap.mpr ⟨t, ht, by simp [halves, hn]⟩⟩⟩

/-- **One split firing is a start and its completion.** A firing of a split transition `t` from a
marking with `inflight:<t>` empty is, in the split net, the start of `t` followed by
`complete:<t>`, ending in the same marking. -/
theorem fires_split {cfg : SplitCfg K} {t : Reference.Trans K} {m m' : K → Nat} {d : List K}
    (hp : cfg.inflight t.core.name ∉ transPlaces t) (h0 : m (cfg.inflight t.core.name) = 0)
    (hone : ∀ o, t.out = some o → ∀ ch, o.findTimeout = some ch →
      ∀ s ∈ fwdSrcs ch, ∃ spec, nspecAt t.core s = some spec ∧ spec.card = .one)
    (h : Reference.Fires t m d m') :
    ∃ mA, Reference.Fires (startHalf cfg t) m [cfg.inflight t.core.name] mA ∧
      Reference.Fires (endHalf cfg t) mA d m' := by
  obtain ⟨hen, ⟨ch, hd⟩, rfl⟩ := h
  unfold startHalf endHalf
  generalize cfg.inflight t.core.name = p at hp h0 ⊢
  have hpres : p ∉ t.core.resets := fun hr => hp (by simp [transPlaces, hr])
  have hpin : nspecAt t.core p = none := by
    unfold nspecAt
    rw [List.find?_eq_none]
    intro s hs hsq
    exact hp (by
      have : s.place = p := by simpa using hsq
      simp only [transPlaces, List.mem_append, List.mem_map]
      exact Or.inl (Or.inl (Or.inl (Or.inl ⟨s, hs, this⟩))))
  have hdp : d.count p = 0 := by
    rw [List.count_eq_zero]
    intro hx
    obtain ⟨o, ho, hx⟩ := mem_deposit hd hx
    exact hp (by simp [transPlaces, outs, ho, hx])
  have hA : fireNC m t.core (depProd [p]) p = 1 := by
    simp [fireNC, hpres, nconsumed, hpin, depProd, h0]
  refine ⟨fireNC m t.core (depProd [p]), ⟨hen, ⟨.action 0, rfl⟩, rfl⟩, ?_, ?_, ?_⟩
  · -- the completion step is enabled: its in-flight place holds one token
    simp [enabledNA, hA, Card.required]
  · -- it deposits what the firing deposited
    cases hout : t.out with
    | none =>
      rw [hout] at hd
      refine ⟨ch, ?_⟩
      have hfree : ∀ c c' : K → Nat, Reference.deposit c none ch = Reference.deposit c' none ch := by
        intro c c'
        cases ch with
        | action i => cases i <;> rfl
        | timedOut _ => rfl
      exact (hfree _ _).trans hd
    | some o =>
      rw [hout] at hd
      cases ch with
      | action i =>
        refine ⟨.action i, ?_⟩
        simpa [Reference.deposit, branches_completionOut] using hd
      | timedOut j =>
        refine ⟨.timedOut j, ?_⟩
        simp only [Reference.deposit, Option.map_some] at hd ⊢
        rw [findTimeout_completionOut]
        cases hft : o.findTimeout with
        | none => rw [hft] at hd; simp at hd
        | some c =>
          rw [hft] at hd
          simp only [Option.map_some, Option.bind_some] at hd ⊢
          rw [timeoutDeposits_completionOut (nconsumed m t.core) _ c (fun s hs => by
            obtain ⟨spec, hsp, hc⟩ := hone o hout c hft s hs
            simp [nconsumed, hsp, hc, Card.consumesAll, Card.required])]
          exact hd
  · -- and ends where the firing ended
    funext q
    by_cases hq : q = p
    · subst hq
      simp [fireNC, hpres, nconsumed, depProd, h0, hdp, nspecAt, Card.consumesAll,
        Card.required]
    · have hnq : ∀ nm : String,
          nspecAt (⟨nm, [⟨p, .one⟩], [], [], []⟩ : NTransition K) q = none := by
        intro nm
        simp [nspecAt, List.find?, Ne.symm hq]
      have hcq : List.count q [p] = 0 := by simp [Ne.symm hq]
      by_cases hr : q ∈ t.core.resets
      · simp [fireNC, hr, depProd, hcq, nconsumed, hnq]
      · simp [fireNC, hr, depProd, hcq, nconsumed, hnq]

/-- **The split only adds runs.** Every firing sequence of the net, from a marking with nothing
in flight, is a firing sequence of the split net with each split label followed at once by its
completion step, ending in the same marking. -/
theorem run_splitNet {cfg : SplitCfg K} {sp : List String} {net : Reference.Net K}
    (hfresh : Fresh cfg sp net) (hone : OneFwd sp net) :
    ∀ {tr : List String} {a b : K → Nat}, Idle cfg sp net a → Reference.Run net tr a b →
      Reference.Run (splitNet cfg sp net) (expandLabels sp tr) a b
  | [], _, _, _, h => by cases h; exact Reference.Run.nil _
  | l :: ls, a, b, hidle, h => by
    cases h with
    | cons hs hr =>
      rename_i a1
      obtain ⟨t, ht, rfl, d, hf⟩ := hs
      have hidle1 : Idle cfg sp net a1 := fun u hu hn => by
        rw [fires_frame (fun h => hfresh u hu hn (by
          simp only [allPlaces, List.mem_append, List.mem_flatMap]
          exact Or.inr ⟨t, ht, h⟩)) hf]
        exact hidle u hu hn
      have ih := run_splitNet hfresh hone hidle1 hr
      by_cases hn : t.core.name ∈ sp
      · have hp : cfg.inflight t.core.name ∉ transPlaces t := fun h => hfresh t ht hn (by
          simp only [allPlaces, List.mem_append, List.mem_flatMap]
          exact Or.inr ⟨t, ht, h⟩)
        obtain ⟨mA, h1, h2⟩ := fires_split hp (hidle t ht hn) (hone t ht hn) hf
        have hm := (mem_splitNet_of (cfg := cfg) (sp := sp) ht).2 hn
        have e : expandLabels sp (t.core.name :: ls) =
            t.core.name :: completeName t.core.name :: expandLabels sp ls := by
          simp [expandLabels, hn]
        rw [e]
        exact Reference.Run.cons ⟨_, hm.1, rfl, _, h1⟩
          (Reference.Run.cons ⟨_, hm.2, rfl, _, h2⟩ ih)
      · have hm := (mem_splitNet_of (cfg := cfg) (sp := sp) ht).1 hn
        have e : expandLabels sp (t.core.name :: ls) = t.core.name :: expandLabels sp ls := by
          simp [expandLabels, hn]
        rw [e]
        exact Reference.Run.cons ⟨t, hm, rfl, d, hf⟩ ih

/-- **Reachability form**: every marking the net reaches from a marking with nothing in flight,
the split net reaches too. -/
theorem reach_splitNet {cfg : SplitCfg K} {sp : List String} {net : Reference.Net K}
    (hfresh : Fresh cfg sp net) (hone : OneFwd sp net) {a b : K → Nat}
    (hidle : Idle cfg sp net a) (h : Reference.Reach net a b) :
    Reference.Reach (splitNet cfg sp net) a b := by
  obtain ⟨tr, hr⟩ := reach_run h
  exact run_reach (run_splitNet hfresh hone hidle hr)

/-- The forwards of a refusal-free `Timeout` are single. -/
theorem multiFwdIn_true_none {t : Reference.Trans K} : ∀ {c : Reference.Out K},
    multiFwdIn t true c = none → ∀ s ∈ fwdSrcs c,
      nspecAt t.core s = none ∨ ∃ spec, nspecAt t.core s = some spec ∧ spec.card = .one
  | .place _, _, _, hs => by simp [fwdSrcs] at hs
  | .forward s' d, h, s, hs => by
    simp only [fwdSrcs, List.mem_singleton] at hs
    subst hs
    simp only [multiFwdIn, Bool.true_and] at h
    cases hn : nspecAt t.core s with
    | none => exact Or.inl rfl
    | some spec =>
      rw [hn] at h
      refine Or.inr ⟨spec, rfl, ?_⟩
      by_cases hc : spec.card = .one
      · exact hc
      · simp [hc] at h
  | .timeout c, h, s, hs => multiFwdIn_true_none (by simpa [multiFwdIn] using h) s
      (by simpa [fwdSrcs] using hs)
  | .and l r, h, s, hs => by
    simp only [multiFwdIn, Option.or_eq_none_iff] at h
    simp only [fwdSrcs, List.mem_append] at hs
    rcases hs with hs | hs
    · exact multiFwdIn_true_none h.1 s hs
    · exact multiFwdIn_true_none h.2 s hs
  | .xor l r, h, s, hs => by
    simp only [multiFwdIn, Option.or_eq_none_iff] at h
    simp only [fwdSrcs, List.mem_append] at hs
    rcases hs with hs | hs
    · exact multiFwdIn_true_none h.1 s hs
    · exact multiFwdIn_true_none h.2 s hs

/-- A refusal-free spec has a refusal-free `Timeout` child. -/
theorem multiFwdIn_findTimeout {t : Reference.Trans K} : ∀ {u : Bool} {o ch : Reference.Out K},
    multiFwdIn t u o = none → o.findTimeout = some ch → multiFwdIn t true ch = none
  | _, .place _, _, _, h => by simp [Reference.Out.findTimeout] at h
  | _, .forward _ _, _, _, h => by simp [Reference.Out.findTimeout] at h
  | _, .timeout c, ch, hm, h => by
    simp only [Reference.Out.findTimeout, Option.some.injEq] at h
    subst h; simpa [multiFwdIn] using hm
  | _, .and l r, ch, hm, h => by
    simp only [multiFwdIn, Option.or_eq_none_iff] at hm
    simp only [Reference.Out.findTimeout] at h
    cases hl : l.findTimeout with
    | some c =>
      rw [hl, Option.some_or, Option.some.injEq] at h; subst h
      exact multiFwdIn_findTimeout hm.1 hl
    | none =>
      rw [hl, Option.none_or] at h
      exact multiFwdIn_findTimeout hm.2 h
  | _, .xor l r, ch, hm, h => by
    simp only [multiFwdIn, Option.or_eq_none_iff] at hm
    simp only [Reference.Out.findTimeout] at h
    cases hl : l.findTimeout with
    | some c =>
      rw [hl, Option.some_or, Option.some.injEq] at h; subst h
      exact multiFwdIn_findTimeout hm.1 hl
    | none =>
      rw [hl, Option.none_or] at h
      exact multiFwdIn_findTimeout hm.2 h

/-- The builder's check ([IO-014] AC3): every forward source is an input place. -/
def FwdFromInputs (net : Reference.Net K) : Prop :=
  ∀ t ∈ net.transitions, ∀ o, t.out = some o → ∀ s ∈ fwdSrcs o, ∃ i ∈ t.core.inputs, i.place = s

/-- **A successful split runs every firing sequence of the net** ([VER-004]): when `refSplit`
returns the split net, every firing sequence of the net from a marking with nothing in flight is
one of the split net, labels expanded. The premise is the builder's ([IO-014] AC3). -/
theorem refSplit_run {cfg : SplitCfg K} {o : Options} {X Y : Reference.TimedNet K}
    {sp : List String} (h : refSplit cfg o X = .ok (Y, sp)) (hb : FwdFromInputs X.net)
    {tr : List String} {a b : K → Nat} (hidle : Idle cfg sp X.net a)
    (hr : Reference.Run X.net tr a b) : Reference.Run Y.net (expandLabels sp tr) a b := by
  rcases refSplit_ok h with ⟨rfl, rfl⟩ | ⟨_, _, _, hnone, rfl⟩
  · simpa [expandLabels] using hr
  · have hfr : ∀ t ∈ X.net.transitions, t.core.name ∈ sp → refusal cfg X.net t = none :=
      fun t ht hn => firstRefusal_none hnone ht hn
    refine run_splitNet (fun t ht hn hm => ?_) (fun t ht hn oo ho ch hch s hs => ?_) hidle hr
    · exact (refusal_none_fresh (hfr t ht hn)).1
        (List.mem_append_left _ (List.mem_map_of_mem hm))
    · have hm := (refusal_none_fresh (hfr t ht hn)).2.2
      simp only [multiFwd, ho, Option.bind_some] at hm
      rcases multiFwdIn_true_none (multiFwdIn_findTimeout hm hch) s hs with hn' | hs'
      · obtain ⟨i, hi, hip⟩ := hb t ht oo ho s (fwdSrcs_findTimeout hch s hs)
        have : (nspecAt t.core s).isSome := by
          unfold nspecAt
          rw [List.find?_isSome]
          exact ⟨i, hi, by simp [hip]⟩
        rw [hn'] at this
        exact absurd this (by simp)
      · exact hs'

/-! ## A marked in-flight place never rests -/

/-- **A marked in-flight place never rests** ([VER-004]): on the split net, a marking that is
quiescent as [VER-002] reads it (reap-aware, or plain under `assumeNoReaping`) holds no token on
the in-flight place of a split transition, since that place enables its completion step, which
is immediate and not reapable. -/
theorem quiescent_no_inflight {cfg : SplitCfg K} {o : Options} {X Y : Reference.TimedNet K}
    {sp : List String} (h : refSplit cfg o X = .ok (Y, sp)) {t : Reference.Trans K}
    (ht : t ∈ X.net.transitions) (hn : t.core.name ∈ sp) {noReap : Bool} {m : K → Nat}
    (hq : VerQuiescent noReap Y m) : m (cfg.inflight t.core.name) = 0 := by
  rcases refSplit_ok h with ⟨rfl, _⟩ | ⟨_, _, _, hnone, rfl⟩
  · exact absurd hn List.not_mem_nil
  · have hfresh := refusal_none_fresh (firstRefusal_none hnone ht hn)
    have hmem := ((mem_splitNet_of (cfg := cfg) (sp := sp) ht).2 hn).2
    by_contra hne
    have hen : Enabled (endHalf cfg t) m := by
      show enabledNA m (endHalf cfg t).core = true
      simp [endHalf, enabledNA, Card.required]
      omega
    have hr := (hq _ hmem hen).2
    have hfind : X.net.transitions.find?
        (fun u => u.core.name == (endHalf cfg t).core.name) = none := by
      rw [List.find?_eq_none]
      intro u hu heq
      apply hfresh.2.1
      simp only [beq_iff_eq] at heq
      exact List.mem_append_right _ (List.mem_map.mpr ⟨u, hu, by simpa [endHalf] using heq⟩)
    simp [Reapable, TimingOf, splitTimed, splitTiming, hfind,
      Novel.TimedScg.Timing.reapable] at hr

end Sem

/-! ## Worked examples ([VER-004] AC4, AC5, AC6) -/

/-- The refusal of a verified-net function's result, if it refused. -/
def errorOf {α : Type} : Except String α → Option String
  | .error e => some e
  | .ok _ => none

/-- Place names of the examples: `p`, `q`, `go`, `r`, and the in-flight place of `t`. -/
def exRender : Nat → String
  | 0 => "p" | 1 => "q" | 2 => "go" | 3 => "r" | 10 => "inflight:t" | _ => "x"

/-- The split configuration of the examples: `inflight:t` is place 10. -/
def exCfg : SplitCfg Nat := { inflight := fun _ => 10, render := exRender }

/-- `t: one(p) + one(go) → p`, whose action is asynchronous. -/
def exT : Reference.Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .one⟩, ⟨2, .one⟩], inhibitors := [], reads := [],
              resets := [] },
    out := some (.place 0) }

/-- `u: one(q) + inhibitor(p) → r`. -/
def exU : Reference.Trans Nat :=
  { core := { name := "u", inputs := [⟨1, .one⟩], inhibitors := [0], reads := [], resets := [] },
    out := some (.place 3) }

/-- The AC4 net, untimed. -/
def exX : Reference.TimedNet Nat :=
  { net := { places := [0, 1, 2, 3], transitions := [exT, exU] },
    timing := fun _ => .immediate, tol := 0 }

/-- The initial marking `{p, q, go}`. -/
def exM0 : NMarking Nat := ⟨[(0, 1), (1, 1), (2, 1)], by decide, by decide⟩

/-- **Which transition splits.** Example: in the AC4 net `u` inhibits `p`, an output of `t`, so
`t` splits and `u` does not. -/
theorem ex_splits : splits exCfg exX.net = ["t"] := by decide

/-- **The split.** Example: on the AC4 net the split succeeds and splits `t` alone. -/
theorem ex_refSplit : refSplit exCfg {} exX = .ok (splitTimed exCfg ["t"] exX, ["t"]) := rfl

/-- **The opt-out.** Example: under `assumeAtomicFiring` the AC4 net is verified as it is. -/
theorem ex_atomic : refSplit exCfg { assumeAtomicFiring := true } exX = .ok (exX, []) := rfl

/-- **The split net reaches `r`** ([VER-004] AC4). Example: from `{p, q, go}` the split net starts
`t` (the token leaves `p` for `inflight:t`) and then fires `u`, whose inhibitor on `p` no longer
blocks it: `r` is marked, as on the executor while `t`'s action runs. -/
theorem ex_split_reaches :
    ∃ f, Reference.Run (splitTimed exCfg ["t"] exX).net ["t", "u"] exM0.count f ∧ f 3 ≠ 0 :=
  ⟨_, Reference.Run.cons
    ⟨startHalf exCfg exT,
      ((mem_splitNet_of (show exT ∈ exX.net.transitions by simp [exX])).2 (by decide)).1, rfl,
      [10], by decide, ⟨.action 0, rfl⟩, rfl⟩
    (Reference.Run.cons
      ⟨exU, (mem_splitNet_of (show exU ∈ exX.net.transitions by simp [exX])).1 (by decide), rfl,
        [3], by decide, ⟨.action 0, rfl⟩, rfl⟩
      (Reference.Run.nil _)), by decide⟩

/-- **The atomic net never reaches `r`.** Example: read atomically, `t` puts its token back in
`p` in the same step, so `p` is never empty and `u` never fires. An atomic verifier proves
`Unreachable(r)`; the executor marks `r`. This is why the split is needed. -/
theorem ex_atomic_never : ∀ f, Reference.Reach exX.net exM0.count f → f 3 = 0 := by
  suffices h : ∀ f, Reference.Reach exX.net exM0.count f → 1 ≤ f 0 ∧ f 3 = 0 from
    fun f hf => (h f hf).2
  intro f hf
  induction hf with
  | refl => decide
  | tail _ hs ih =>
    obtain ⟨l, t, ht, _, d, hen, ⟨ch, hd⟩, rfl⟩ := hs
    simp only [exX, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · have hd' : d = [0] := by
        rcases ch with (_ | i) | j
        · simpa [Reference.deposit, exT, Reference.Out.branches] using hd.symm
        · simp [Reference.deposit, exT, Reference.Out.branches] at hd
        · simp [Reference.deposit, exT, Reference.Out.findTimeout] at hd
      subst hd'
      simp [fireNC, exT, nconsumed, nspecAt, depProd, Card.consumesAll, Card.required]
      omega
    · simp [enabledNA, exU] at hen
      omega

/-- **A terminal counts as a test.** Example: with `r` a terminal place, `u`, which deposits into
`r`, splits too. -/
theorem ex_terminal_splits : splits { exCfg with terminals := [3] } exX.net = ["t", "u"] := by
  decide

set_option maxRecDepth 20000 in
/-- **A ν-join is refused** ([VER-004] AC6). Example: when `t` is a ν-join the split is refused
and the reason names `t`. -/
theorem ex_refuse_join :
    errorOf (refSplit { exCfg with joins := ["t"] } {} exX) =
      some ("transition 't' must be verified as two steps, since its action runs between " ++
        "consuming and depositing and another transition tests one of its outputs with an " ++
        "inhibitor, reset or drain (VER-004), but it is a ν-join, whose outputs carry the " ++
        "matched name (NU-020, NU-054)") := by decide

set_option maxRecDepth 20000 in
/-- **A refused split is `Unknown`** ([VER-003] line 4). Example: the reference verifier, given
the refusal, answers `Unknown` before any route runs, and its report carries the reason. -/
theorem ex_refuse_unknown :
    (refVerify (splitAbs { exCfg with joins := ["t"] }) {} exX (.unreachable [3]) exM0).verdict =
      .unknown "the verified net cannot be built" ∧
    (refVerify (splitAbs { exCfg with joins := ["t"] }) {} exX (.unreachable [3]) exM0).notes =
      ["transition 't' must be verified as two steps, since its action runs between " ++
        "consuming and depositing and another transition tests one of its outputs with an " ++
        "inhibitor, reset or drain (VER-004), but it is a ν-join, whose outputs carry the " ++
        "matched name (NU-020, NU-054)"] := by decide

/-- `t` with a timeout that forwards its drained input `p` back to `p`. -/
def exTDrain : Reference.Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .all⟩, ⟨2, .one⟩], inhibitors := [], reads := [],
              resets := [] },
    out := some (.xor (.place 0) (.timeout (.forward 0 0))) }

set_option maxRecDepth 20000 in
/-- **A multi-token timeout forward is refused** ([VER-004] AC6). Example: `t` drains `p` and its
timeout forwards every drained token back to `p`; its completion step cannot see how many it
took, so the split is refused, naming `t`, `p` and the forward. -/
theorem ex_refuse_forward :
    errorOf (refSplit exCfg {} { exX with net := { exX.net with transitions := [exTDrain, exU] } }) =
      some ("transition 't' must be verified as two steps, since its action runs between " ++
        "consuming and depositing and another transition tests one of its outputs with an " ++
        "inhibitor, reset or drain (VER-004), but its timeout forwards input 'p' to 'p', one " ++
        "token per token consumed (IO-014), a count its completion step cannot see") := by decide

set_option maxRecDepth 20000 in
/-- **A name clash is refused** ([VER-004]). Example: when the net already declares the place
`inflight:t`, the split would add a name the net uses, and is refused. -/
theorem ex_refuse_clash :
    errorOf (refSplit exCfg {} { exX with net := { exX.net with places := [0, 1, 2, 3, 10] } }) =
      some ("transition 't' must be verified as two steps, since its action runs between " ++
        "consuming and depositing and another transition tests one of its outputs with an " ++
        "inhibitor, reset or drain (VER-004), but the net already uses the name " ++
        "'inflight:t' the split would add") := by decide

end Libpetri.Spec.Verifier.Split
