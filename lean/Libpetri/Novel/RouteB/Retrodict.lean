import Libpetri.Novel.RouteB.Classify
import Libpetri.Novel.RouteB.Sound

/-!
# Route B retrodictions: the past wrong verdicts as Lean witnesses

The four fixes the gap analysis lists against Route B, each reproduced on the model of the code
before the fix and shown gone on the shipped one. `4d7a9d9` (off-key join) is in `Classify.lean`
(`offKey_rule_is_necessary`), with the three issues found while modelling, all closed since
(`dupKey_refused`, `copyingMint_refused`, `zeroKey_refused`).

* **`c23cd9e` — [NU-052] prune without `will_fire`** (`willFire_guard_is_necessary_routeB`). A
  priority-10 join `J : A, B` whose keys hold two different names, and a priority-0 drain
  `D : A` competing for `A`'s single token. The pre-fix `priority_dominated` prunes `D` (the join
  is base-enabled), so the class has **no successor** — a spurious stall, and every state after
  the drain is lost. The executor fires `D` (a concrete `NuStepC`, whose premises all hold), and
  on the shipped step `name_step_simulates_exec` finds the edge. `Priority.lean` has the
  count-level version; this one runs through the Route B successor function itself.
* **`662ec39` — [VER-006] did not bind Route B** (`ver006_binds_routeB`). Under `Ignore` the graph
  treats an environment place as an ordinary empty one: on `T : E → P` (with an idle ν-join so
  the net takes Route B) every reachable class has `P = 0`, so `placeBound(P, 0)` is `Proven`,
  while one injection into `E` lets the executor reach `P = 1` (over the net's own rows,
  `nuRows`). The pre-fix dispatcher returned that `Proven`; `routeBFinal` downgrades every
  `Proven` under `Ignore`. `routeBFinal` models one `if` of `smt_verifier.rs::verify_net` (the
  Route B arm's [VER-006] downgrade), nothing else of it; `verify_net` as a whole is deliberately
  not pinned (`fidelity.toml`), and this module does not ask for it to be.
* **`89aaeec` — Route B read a frozen environment count** (`env_count_frozen`,
  `env_count_witness`). Under `AlwaysAvailable` the graph never consumes an environment place and
  injects nothing, so its count stays at the initial value (`env_count_frozen`, for any net none
  of whose branch outcomes deposits into it, drained forwards included). A property reading it is
  decided on that value: `placeBound(E, 0)` holds in every class, while one injection makes
  `E = 1`. `envObservation` (`route_b_env_observation`, rules 1–4 over the declared environment
  places) declines it.

`envObservation` models rule 4's read set from the property's shape (`observed`): a safety
property's places, nothing for a vacuous quiescence property, for `DeadlockFree` the environment
places that are not sinks plus every conditional sink's marker, for `TerminatesAtSink` the sinks,
else the property's places. The place lists themselves (`property_place_names`, the sink set,
the markers) are inputs. What a Route B answer then assumes, per property:
`envObservation_none_reach` (a safety property reads no declared environment place),
`envObservation_none_deadlockFree` (every declared environment place is a sink and no marker),
`envObservation_none_terminatesAtSink` (no declared environment place is a sink).

Not claimed: that the environment rules 1–4 suffice for a sound verdict under injection. That is
[VER-006] across routes (gap R5); here only the frozen-count mechanism, the witnesses and the
read set.
-/

namespace Libpetri.Novel.RouteB

open Libpetri
open Libpetri.Novel.CanonicalKey
open Libpetri.Novel.ForwardDeposit
open Libpetri.Novel.TransferRows (consumedA)

/-! ## `c23cd9e`: the `will_fire` guard -/

section WillFire

variable {β : Type} (co : List PlaceId) (base : BaseLayer β) (net : List NuTrans)
  (role : NuTrans → Role)

/-- `priority_dominated` before `c23cd9e`: no `will_fire` conjunct. -/
def dominatedPre (S : NState co β) (L : NuTrans) : Bool :=
  (net.filter fun H => base.enabled S.b H.base).any fun H =>
    (H.base.name != L.base.name) && decide (L.base.priority < H.base.priority)
      && base.readyLe S.b H.base L.base && base.compete S.b H.base L.base

/-- The expansion before `c23cd9e` (`Conflict` semantics). -/
def succPre (c : ℕ) (S : NState co β) : List (String × NState co β) :=
  (net.filter fun T => base.enabled S.b T.base).flatMap fun T =>
    if dominatedPre co base net S T then [] else
      T.rows.flatMap fun d =>
        match base.fire S.b T.base d with
        | none => []
        | some b' => (nameSuccs co (role T) S.m d.places S.bound c).attach.map fun M' =>
            (T.base.name, ⟨b', M'.1, max S.bound (c + 1), nameSuccs_supp S.supp M'.1 M'.2⟩)

end WillFire

namespace WF

/-- Coloured `A = 0`, `B = 1`; the drain's dead letter `DL = 2`; the join's output `OUT = 3`. -/
def co : List PlaceId := [0, 1]

/-- The join, priority 10. -/
def tJ : NuTrans where
  base := { name := "J", inputs := [inOne 0, inOne 1], inhibitors := [], reads := [], resets := [],
            priority := 10 }
  rows := [⟨[3], []⟩]
  keys := some [0, 1]
  relays := []

/-- The orphan drain, priority 0 (EXTENDED consume role, drain branch). -/
def tD : NuTrans where
  base := { name := "D", inputs := [inOne 0], inhibitors := [], reads := [], resets := [],
            priority := 0 }
  rows := [⟨[2], []⟩]
  keys := none
  relays := []

def net : List NuTrans := [tJ, tD]

def role (T : NuTrans) : Role :=
  if T.base.name = "J" then .join [(0, 1), (1, 1)] [] else .consume 0

/-- Name `0` in `A`, name `1` in `B`: the join is base-enabled but name-disabled. -/
def m : CMarking := fun p => if p = 0 then [0] else if p = 1 then [1] else []

/-- After the drain. -/
def m' : CMarking := fun p => if p = 1 then [1] else if p = 2 then [0] else []

theorem inFragment : ∀ T ∈ net, InFragment co T (role T) := by
  intro T hT
  simp only [net, List.mem_cons, List.mem_nil_iff, or_false] at hT
  rcases hT with rfl | rfl
  · refine ⟨⟨by decide, by decide, by decide⟩, [0, 1], rfl, fun p => by simp, by decide,
      ?_, by decide, by decide, by decide⟩
    intro pr hpr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl
    · exact ⟨by decide, inOne 0, rfl, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨by decide, inOne 1, rfl, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨⟨by decide, by decide, by decide⟩, rfl, inOne 0, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

theorem guardFree : ∀ T ∈ net, GuardFree T.base := by
  intro T hT
  simp only [net, List.mem_cons, List.mem_nil_iff, or_false] at hT
  rcases hT with rfl | rfl <;> intro s hs <;>
    simp only [tJ, tD, List.mem_cons, List.mem_nil_iff, or_false] at hs <;>
    rcases hs with rfl | rfl <;> rfl

/-- **The executor fires the drain** — a `NuStepC`, every premise met. -/
theorem drain_step : NuStepC co id net role true m m' := by
  refine ⟨tD, by simp [net], ⟨[2], []⟩, by simp [tD], by decide, ?_, ?_, fun _ => by decide⟩
  · funext p
    rcases p with _ | _ | _ | p <;>
      simp [alpha, alphaFireC, m, m', consumedAt, specAt, tD, inOne, consumeCount,
        Card.consumesAll, Card.required, Row.resolve]
  · refine ⟨0, [[0]], fun _ => [], fun h => by simp [tD] at h, ?_, ?_, ?_,
      fun h => by simp [tD] at h, ?_, ?_⟩
    · exact List.Forall₂.cons (by simp [SpecTakes, isKey, tD, inOne, Card.consumesAll,
        Card.required]) List.Forall₂.nil
    · intro i u
      rcases (show u = 0 ∨ u = 1 ∨ 2 ≤ u by omega) with rfl | rfl | hu
      · fin_cases i <;> simp [rmvList, nameLayer, m, inOne, tD, co]
      · fin_cases i <;> simp [rmvList, nameLayer, m, inOne, tD, co]
      · have h0 : (0 : ℕ) ≠ u := by omega
        have h1 : (1 : ℕ) ≠ u := by omega
        fin_cases i <;> simp [rmvList, nameLayer, m, inOne, tD, co, h0, h1]
    · intro i; fin_cases i <;> decide
    · show ∀ i, ∀ w ∈ ([] : List ℕ), _
      intro _ _ hw; exact absurd hw List.not_mem_nil
    · funext u i
      rcases (show u = 0 ∨ u = 1 ∨ 2 ≤ u by omega) with rfl | rfl | hu
      · fin_cases i <;> simp [rmvList, nameLayer, m, m', inOne, tD, co]
      · fin_cases i <;> simp [rmvList, nameLayer, m, m', inOne, tD, co]
      · have h0 : (0 : ℕ) ≠ u := by omega
        have h1 : (1 : ℕ) ≠ u := by omega
        fin_cases i <;> simp [rmvList, nameLayer, m, m', inOne, tD, co, h0, h1]

/-- The pre-fix prune removes the drain, and the join has no name successor: no successor. -/
theorem pre_fix_stalls :
    (succPre co untimedBase net role (view co id m).bound (view co id m)).isEmpty = true := by
  decide

/-- **Retrodiction of `c23cd9e`.** From the class of `m`, the pre-fix step has no successor while
the executor fires the drain; the shipped step has the drain's edge, landing on the executor's
successor key. -/
theorem willFire_guard_is_necessary_routeB :
    NuStepC co id net role true m m' ∧
    succPre co untimedBase net role (view co id m).bound (view co id m) = [] ∧
    ∃ l S', (l, S') ∈ succ untimedBase net role true (view co id m).bound (view co id m) ∧
      keyOf S' = keyOf (view co id m') :=
  ⟨drain_step, List.isEmpty_iff.mp pre_fix_stalls,
    name_step_simulates_exec (by decide) inFragment guardFree rfl drain_step⟩

end WF

/-! ## `662ec39`: [VER-006] binds Route B -/

/-- The dispatcher's Route B arm. Before `662ec39` (`fixed = false`) it returned Route B's verdict
as is; since, a `Proven` under `Ignore` with environment places is downgraded to `Unknown`. -/
def routeBFinal (fixed ignores : Bool) (v : Decide.Verdict) : Decide.Verdict :=
  if fixed && ignores && v == .proven then .unknown else v

theorem routeBFinal_never_proven (v : Decide.Verdict) : routeBFinal true true v ≠ .proven := by
  unfold routeBFinal
  by_cases h : v = .proven
  · subst h; decide
  · have : (v == .proven) = false := by simpa using h
    simp [this, h]

namespace Ignore

/-- `E = 2` (an environment place), `P = 3`; coloured `A = 0`, `B = 1` for an idle ν-join. -/
def co : List PlaceId := [0, 1]

def tT : NuTrans where
  base := { name := "T", inputs := [inOne 2], inhibitors := [], reads := [], resets := [] }
  rows := [⟨[3], []⟩]
  keys := none
  relays := []

def tJ : NuTrans where
  base := { name := "J", inputs := [inOne 0, inOne 1], inhibitors := [], reads := [], resets := [] }
  rows := [⟨[4], []⟩]
  keys := some [0, 1]
  relays := []

def net : List NuTrans := [tT, tJ]

def role (T : NuTrans) : Role := if T.base.name = "J" then .join [(0, 1), (1, 1)] [] else .ordinary

def zero : AMarking := fun _ => 0

theorem succ_zero (c : ℕ) (S : NState co AMarking) (hS : S.b = zero) :
    succ untimedBase net role true c S = [] := by
  unfold succ
  have : net.filter (fun T => untimedBase.enabled S.b T.base) = [] := by rw [hS]; decide
  rw [this]
  rfl

/-- Under `Ignore` the graph never leaves the empty marking: every class has `P = 0`. -/
theorem graph_P_zero {S : NState co AMarking}
    (h : Explorer.Reach (routeB untimedBase net role true) (initState co zero) S) : S.b 3 = 0 := by
  suffices S.b = zero by rw [this]; rfl
  induction h with
  | init => rfl
  | @step a c l s _ _ hmem ih =>
    have : succ untimedBase net role true c a = [] := succ_zero c a ih
    change (l, s) ∈ succ untimedBase net role true c a at hmem
    rw [this] at hmem
    exact absurd hmem List.not_mem_nil

/-- With injection into `E` the executor's count marking reaches `P = 1`, over the net's own
rows (`nuRows net`: `T` deposits into `P`, the join into `OUT`). -/
theorem injection_reaches_P :
    ∃ a, ReachADInj (nuRows net) [2] zero a ∧ a 3 = 1 := by
  let a1 : AMarking := fun q => if q == 2 then zero q + 1 else zero q
  refine ⟨fireAD a1 tT.base [3], ?_, by decide⟩
  refine Relation.ReflTransGen.tail (Relation.ReflTransGen.single (Or.inr ⟨2, by simp, rfl⟩)) ?_
  exact Or.inl ⟨(tT.base, [3]), by simp [net, nuRows, tT, tJ], by decide, rfl⟩

/-- **Retrodiction of `662ec39`.** Under `Ignore` the graph proves `placeBound(P, 0)`; one
injection violates it; before the fix the dispatcher returned the `Proven`, since it cannot. -/
theorem ver006_binds_routeB :
    (∀ S, Explorer.Reach (routeB untimedBase net role true) (initState co zero) S → S.b 3 = 0) ∧
    (∃ a, ReachADInj (nuRows net) [2] zero a ∧ a 3 = 1) ∧
    routeBFinal false true .proven = .proven ∧
    routeBFinal true true .proven = .unknown :=
  ⟨fun _ h => graph_P_zero h, injection_reaches_P, rfl, rfl⟩

end Ignore

/-! ## `89aaeec`: an environment count is frozen in the graph -/

section Env

/-- The untimed base under `AlwaysAvailable` ([VER-006]): an input arc on an environment place is
always satisfied and consumes nothing, nothing is injected, and an environment place gains only
what a firing deposits. -/
def envBase (envs : List PlaceId) : BaseLayer AMarking where
  enabled a t :=
    (t.inputs.all fun s => envs.contains s.place || decide (s.card.required ≤ a s.place))
      && t.inhibitors.all (fun p => a p == 0)
      && t.reads.all (fun p => envs.contains p || decide (1 ≤ a p))
  fire a t r := some fun p =>
    if envs.contains p then a p + (r.resolve (consumedA a t)).count p
    else fireAD a t (r.resolve (consumedA a t)) p
  readyLe _ _ _ := true
  compete := sharesConsumed
  idle _ _ := true

theorem resolve_count_off {r : Row} {p : PlaceId} (h : p ∉ r.places) (k : PlaceId → ℕ) :
    (r.resolve k).count p = 0 := by
  refine List.count_eq_zero_of_not_mem fun hm => h ?_
  unfold Row.resolve at hm
  unfold Row.places
  rcases List.mem_append.mp hm with hm | hm
  · exact List.mem_append_left _ hm
  · obtain ⟨x, hx, hpx⟩ := List.mem_flatMap.mp hm
    rw [List.eq_of_mem_replicate hpx]
    exact List.mem_append_right _ (List.mem_map_of_mem hx)

/-- **The environment count is frozen.** When no branch outcome deposits into an environment
place (fixed or drained), every class the graph reaches holds the initial count there: a
verdict reading it reads a constant. -/
theorem env_count_frozen {co : List PlaceId} {envs : List PlaceId} {net : List NuTrans}
    {role : NuTrans → Role} {conflict : Bool}
    (hno : ∀ T ∈ net, ∀ r ∈ T.rows, ∀ p ∈ envs, p ∉ r.places) {S0 S : NState co AMarking}
    (h : Explorer.Reach (routeB (envBase envs) net role conflict) S0 S) :
    ∀ p ∈ envs, S.b p = S0.b p := by
  induction h with
  | init => exact fun _ _ => rfl
  | @step a c l s _ _ hmem ih =>
    intro p hp
    obtain ⟨T, hT, -, d, hd, hf⟩ := mem_succ_base (base := envBase envs) hmem
    have hf' : (fun p => if envs.contains p then a.b p + (d.resolve (consumedA a.b T.base)).count p
        else fireAD a.b T.base (d.resolve (consumedA a.b T.base)) p) = s.b := Option.some.inj hf
    rw [← hf']
    show (if envs.contains p then a.b p + (d.resolve (consumedA a.b T.base)).count p
      else fireAD a.b T.base (d.resolve (consumedA a.b T.base)) p) = S0.b p
    rw [if_pos (List.contains_iff_mem.mpr hp), resolve_count_off (hno T hT d hd p hp),
      Nat.add_zero]
    exact ih p hp

/-- The property as rule 4 of `route_b_env_observation` reads it: a reachability-safety property
(`is_reachability_safety`: `PlaceBound`, `BranchPlaceBound`, `MutualExclusion`, `Unreachable`,
`NameAligned`) with its `property_place_names`; `DeadlockFree`; `TerminatesAtSink`; any other
quiescence property (`JoinedOrDeadLettered`, `QuiescentCount`, `QuiescentNameAligned`) with its
`property_place_names`. The place lists are inputs: `property_place_names` is modelled in
`Seam/Bad.lean`, not here. Rule 4 also refuses `QuiescentNameAligned` on any registered
environment place ([NU-055] AC6); that only refuses more, so it needs no case here. -/
inductive PropShape where
  | reach (places : List PlaceId)
  | deadlockFree
  | terminatesAtSink
  | quiescence (places : List PlaceId)

/-- Rule 4's `observed` set: a safety property's places; nothing for a vacuous quiescence
property (`quiescence_vacuous`); for `DeadlockFree` the environment places that are not sinks
plus every conditional sink's marker; for `TerminatesAtSink` the sinks; else the property's
places. -/
def observed : PropShape → Bool → List PlaceId → List PlaceId → List PlaceId → List PlaceId
  | .reach ps, _, _, _, _ => ps
  | _, true, _, _, _ => []
  | .deadlockFree, false, env, sinks, markers => env.filter (fun p => !sinks.contains p) ++ markers
  | .terminatesAtSink, false, _, sinks, _ => sinks
  | .quiescence ps, false, _, _, _ => ps

/-- `route_b_env_observation`, rules 1–4, as a first culprit over the declared environment
places (`env`: `env_places` filtered by the net's places): a coloured one, one an inhibitor
tests, one shared by two consumers under `Conflict`, one the property observes. The Rust
reports a reason string and scans transitions in name order; only whether some culprit exists
matters here. -/
def envObservation (declared : PlaceId → Bool) (envs : List PlaceId) (coloured : PlaceId → Bool)
    (net : List NuTrans) (conflict : Bool) (prop : PropShape) (vacuous : Bool)
    (sinks markers : List PlaceId) : Option PlaceId :=
  let env := envs.filter declared
  (env.find? coloured).orElse fun _ =>
  (env.find? fun p => net.any fun T => T.base.inhibitors.contains p).orElse fun _ =>
  (if conflict then env.find? fun p =>
      decide (2 ≤ (net.filter fun T => T.base.inputs.any fun s => s.place == p).length)
    else none).orElse fun _ =>
  env.find? fun p => (observed prop vacuous env sinks markers).contains p

theorem orElse_none {α : Type} {a : Option α} {b : Unit → Option α} (h : a.orElse b = none) :
    b () = none := by
  cases a with
  | none => exact h
  | some _ => cases h

/-- When Route B answers, the property observes no declared environment place. -/
theorem envObservation_none_reads {declared : PlaceId → Bool} {envs : List PlaceId}
    {coloured : PlaceId → Bool} {net : List NuTrans} {conflict : Bool} {prop : PropShape}
    {vacuous : Bool} {sinks markers : List PlaceId}
    (h : envObservation declared envs coloured net conflict prop vacuous sinks markers = none) :
    ∀ p ∈ envs, declared p = true →
      p ∉ observed prop vacuous (envs.filter declared) sinks markers := by
  intro p hp hd hr
  unfold envObservation at h
  have h4 := orElse_none (orElse_none (orElse_none h))
  have := List.find?_eq_none.mp h4 p (List.mem_filter.mpr ⟨hp, hd⟩)
  exact this (List.contains_iff_mem.mpr hr)

/-- What a Route B answer under `AlwaysAvailable` assumes, per property: a safety property reads
no declared environment place. -/
theorem envObservation_none_reach {declared : PlaceId → Bool} {envs : List PlaceId}
    {coloured : PlaceId → Bool} {net : List NuTrans} {conflict : Bool} {ps : List PlaceId}
    {vacuous : Bool} {sinks markers : List PlaceId}
    (h : envObservation declared envs coloured net conflict (.reach ps) vacuous sinks markers = none) :
    ∀ p ∈ envs, declared p = true → p ∉ ps :=
  fun p hp hd => envObservation_none_reads h p hp hd

/-- A non-vacuous `DeadlockFree` answer: every declared environment place is a sink, and none is
a conditional sink's marker. -/
theorem envObservation_none_deadlockFree {declared : PlaceId → Bool} {envs : List PlaceId}
    {coloured : PlaceId → Bool} {net : List NuTrans} {conflict : Bool}
    {sinks markers : List PlaceId}
    (h : envObservation declared envs coloured net conflict .deadlockFree false sinks markers = none) :
    ∀ p ∈ envs, declared p = true → p ∈ sinks ∧ p ∉ markers := by
  intro p hp hd
  have hn := envObservation_none_reads h p hp hd
  simp only [observed, List.mem_append, List.mem_filter, Bool.not_eq_true',
    not_or, not_and] at hn
  refine ⟨?_, hn.2⟩
  by_contra hs
  exact absurd (by simpa [List.contains_iff_mem] using hs) (hn.1 ⟨hp, hd⟩)

/-- A non-vacuous `TerminatesAtSink` answer: no declared environment place is a sink. -/
theorem envObservation_none_terminatesAtSink {declared : PlaceId → Bool} {envs : List PlaceId}
    {coloured : PlaceId → Bool} {net : List NuTrans} {conflict : Bool}
    {sinks markers : List PlaceId}
    (h : envObservation declared envs coloured net conflict .terminatesAtSink false sinks markers =
      none) :
    ∀ p ∈ envs, declared p = true → p ∉ sinks :=
  fun p hp hd => envObservation_none_reads h p hp hd

namespace EnvW

/-- `E = 2` an environment place, `P = 3`; coloured `A = 0`, `B = 1` for an idle ν-join; the net
`T : E → P`. -/
def co : List PlaceId := [0, 1]
def net : List NuTrans := [Ignore.tT, Ignore.tJ]

/-- **Retrodiction of `89aaeec`.** Under `AlwaysAvailable` every class has `E = 0`, so
`placeBound(E, 0)` is read off a constant and comes back `Proven`; one injection makes `E = 1`
(over the net's own rows); rule 4 declines the property (it reads `E`). -/
theorem env_count_witness :
    (∀ S, Explorer.Reach (routeB (envBase [2]) net Ignore.role false) (initState co Ignore.zero) S →
      S.b 2 = 0) ∧
    (∃ a, ReachADInj (nuRows net) [2] Ignore.zero a ∧ a 2 = 1) ∧
    envObservation (fun _ => true) [2] (fun p => co.contains p) net false (.reach [2]) false [] [] =
      some 2 := by
  refine ⟨fun S h => ?_, ⟨fun q => if q == 2 then Ignore.zero q + 1 else Ignore.zero q,
    Relation.ReflTransGen.single (Or.inr ⟨2, by simp, rfl⟩), by decide⟩, by decide⟩
  have := env_count_frozen (co := co) (envs := [2]) (net := net) (role := Ignore.role)
    (conflict := false) (by decide) h 2 (by simp)
  rw [this]
  rfl

end EnvW

end Env

end Libpetri.Novel.RouteB
