import Libpetri.Novel.RouteA.Retrodict
import Libpetri.Novel.ReapAware

/-!
# Route A quiescence under deadline reaping ([TIME-013], [VER-002], [VER-004])

`routeA_quiescence_sound` (`Simulate.lean`) transfers a quiescence `Proven` to every ν-reachable
marking at which **no row is enabled** (`NuDead`). That is the untimed reading of quiescence.
The executor comes to rest at a different set of markings: a **reapable** transition past its
latest bound is reaped, its enabled bit is cleared while its tokens stay, and the loop stops
once no bit is set (`Novel/ReapingVsUntimed.lean`, `Novel/ReapAware.lean`). Reapable is
`reaping::is_reapable`: the timing is `Deadline` or `Window`. `Exact` is never reaped (its
bound is enforced softly, [TIME-006]), and neither are `Immediate` and `Delayed`
(`Novel/TimedScg/Timing.lean`, `Timing.reapable`; `Novel/ReapAware.lean`, `reapable`).

Until the fix of 2026-09-28 the Route A quiescence predicate read no timing and inherited the
untimed reading. The shipped `encode_coloured_quiescent` (`name_coloured_encoder.rs`) now
skips every flat row whose `ft.reapable` is set, as the flat `encode_quiescent` does. This
module models that and proves it sound for the executor's rest markings.

* `NuRest rp rows m`: where the timed executor may rest, every row is ν-disabled at `m` or
  reapable (`rp`).
* `DeadER E rp e`: the reaping-aware quiescence predicate, each row reapable or disabled as in
  `DeadE`. `DeadE` implies it (`deadE_reaping`); with no reapable row the two coincide
  (`deadER_none`).
* `DeadERs E R e`: the shipped predicate, the `DeadE` conjunction over the rows that
  `flatten_with_reapable` did not mark, a row being marked when its source transition's name is
  in the set `R` (`SmtVerifier::reapable_set`: `reaping::reapable_transitions` of the net, or
  empty under `assume_no_reaping`). `deadERs_iff`: it is `DeadER` for that marking;
  `deadERs_nil`: under `assume_no_reaping` it is the strict `DeadE`.
* `routeA_quiescence_sound_reaping`: a `Proven` of the reaping-aware query holds of every
  ν-reachable rest marking.
* **`routeA_reap_aware_sound`**: the shipped query against the executor. If the reap-aware
  query is `Proven`, `R` marks exactly the rows whose timing is reapable, and a timed run of
  either backend over the flat rows (`ReapAware.RestsAt`, any schedule) rests at `α(m)` for a
  ν-reachable `m`, then the property's clause `Q` fails at `α(m)`. The rest marking is
  reap-quiescent by `ReapAware.rest_sound`; `nuRest_of_reapQuiescent` lifts that to `NuRest`.
  That the marking behind a rest is ν-reachable is P6 (`Model.lean`), a premise here.
* **`ReapW.reaping_breaks_routeA_quiescence`**: the witness, a plan `build_plan` returns. The
  net is `ReapingVsUntimed.lean`'s `p₀ —t→ p₁` with `t = window(3, 5)`, beside a ν-join
  `join : a, b → done` keyed on `a` and `b`. `buildPlan` accepts it with `C = [a, b]` and
  `k = 0` from the simplex's own answer (`planW`), and every `Premises` field holds. The strict
  query (the one `assume_no_reaping` asks) is `Proven`, while both backends' timed runs rest at
  `{p₀}`, which strands a token. The shipped reap-aware query is violated at the seed, so it is
  not `Proven`.
-/

namespace Libpetri.Novel.RouteA

open Libpetri
open Libpetri.Novel.ForwardDeposit
open Libpetri.Novel.LinearBound

/-! ## Reaping-aware quiescence -/

/-- The reaping-aware `encode_coloured_quiescent`: every row belongs to a reapable transition
(the executor may have cleared its bit) or is disabled for an uncoloured reason or for every
colour. -/
def DeadER (E : Enc) (rp : CRow → Prop) (e : EState) : Prop :=
  ∀ r ∈ E.rows, rp r ∨ uDisabled E.C e r.t ∨ colDisabled E.C E.k r.cls e.s

/-- Where the timed executor may come to rest: every row is reapable or ν-disabled. With a
reapable row enabled the executor still stops once the reap clears its bit
(`Novel/ReapAware.lean`, `rest_sound`). -/
def NuRest (rp : CRow → Prop) (rows : List CRow) (m : CMarking) : Prop :=
  ∀ r ∈ rows, rp r ∨ ¬ NuEnabled m r

/-- A ν-dead marking is a rest marking, whatever is reapable. -/
theorem nuDead_rest {rows : List CRow} {m : CMarking} (rp : CRow → Prop) (h : NuDead rows m) :
    NuRest rp rows m :=
  fun r hr => Or.inr (h r hr)

/-- With nothing reapable, rest is ν-deadness. -/
theorem nuRest_none {rows : List CRow} {m : CMarking} :
    NuRest (fun _ => False) rows m ↔ NuDead rows m :=
  ⟨fun h r hr => (h r hr).resolve_left id, nuDead_rest _⟩

/-- The untimed quiescence predicate implies the reaping-aware one: the reaping-aware query is
the stronger claim when `Proven`. -/
theorem deadE_reaping {E : Enc} {e : EState} (rp : CRow → Prop) (h : DeadE E e) :
    DeadER E rp e :=
  fun r hr => Or.inr (h r hr)

/-- With nothing reapable (an untimed net), the two predicates coincide. -/
theorem deadER_none {E : Enc} {e : EState} : DeadER E (fun _ => False) e ↔ DeadE E e :=
  ⟨fun h r hr => (h r hr).resolve_left id, deadE_reaping _⟩

/-! ## The shipped predicate -/

/-- `flatten_with_reapable`'s mark on a flat row: the name of its source transition is in `R`,
the set `SmtVerifier::reapable_set` hands the encoders (`reaping::reapable_transitions` of the
net, the transitions whose timing is `Deadline` or `Window`; empty under `assume_no_reaping`).
Each flat row's `reapable` flag is computed from its source transition (a transition with more
than one outcome has rows named `{t}_b{i}`, but `flatten_with_reapable` reads `reapable(t)`). -/
def reapT (R : List String) (t : Transition) : Bool := R.contains t.name

/-- `encode_coloured_quiescent` as shipped: the loop `continue`s on a row with `ft.reapable`,
and every other row contributes its disabled condition to the conjunction. (`None`, "never
quiescent", is the empty disjunction of a kept row, as in `DeadE`.) -/
def DeadERs (E : Enc) (R : List String) (e : EState) : Prop :=
  ∀ r ∈ E.rows.filter (fun r => !reapT R r.t), uDisabled E.C e r.t ∨ colDisabled E.C E.k r.cls e.s

/-- **The shipped predicate is `DeadER`** for the rows `flatten_with_reapable` marks. -/
theorem deadERs_iff {E : Enc} {R : List String} {e : EState} :
    DeadERs E R e ↔ DeadER E (fun r => reapT R r.t = true) e := by
  constructor
  · intro h r hr
    by_cases hrp : reapT R r.t = true
    · exact Or.inl hrp
    · exact Or.inr (h r (List.mem_filter.mpr ⟨hr, by simpa using hrp⟩))
  · intro h r hr
    obtain ⟨hr, hn⟩ := List.mem_filter.mp hr
    exact (h r hr).resolve_left (by simpa using hn)

/-- **Under `assume_no_reaping`** (`R` empty) the shipped predicate is the strict `DeadE`. -/
theorem deadERs_nil {E : Enc} {e : EState} : DeadERs E [] e ↔ DeadE E e := by
  rw [deadERs_iff]
  have : (fun r : CRow => reapT [] r.t = true) = fun _ => False := by
    funext r
    simp [reapT]
  rw [this]
  exact deadER_none

/-! ## Soundness -/

/-- **A rest marking is represented by a state `DeadER` holds of.** Row by row: a reapable row
is reapable in both; a ν-disabled row is disabled in the encoding by `dead_transfer` on that
row alone. -/
theorem dead_transfer_reaping {E : Enc} {rp : CRow → Prop} {m : CMarking} {e : EState}
    {σ : Name → Nat} (hok : ∀ r ∈ E.rows, ClassOK E.C r) (hu : ∀ r ∈ E.rows, Unguarded r.t)
    (hd : ∀ r ∈ E.rows, InputsDistinctPlaces r.t) (hsim : Sim E.C E.k m e σ)
    (hrest : NuRest rp E.rows m) : DeadER E rp e := by
  intro r hr
  rcases hrest r hr with h | h
  · exact Or.inl h
  · right
    have hsing : ∀ r' ∈ [r], r' = r := fun r' h' => List.mem_singleton.mp h'
    exact dead_transfer (E := { E with rows := [r] })
      (fun r' h' => hsing r' h' ▸ hok r hr) (fun r' h' => hsing r' h' ▸ hu r hr)
      (fun r' h' => hsing r' h' ▸ hd r hr) hsim
      (fun r' h' => hsing r' h' ▸ h) r (List.mem_singleton.mpr rfl)

/-- **Quiescence under reaping.** A `Proven` of the reaping-aware query (no reachable encoding
state satisfies `DeadER` with a bad aggregate) holds of every ν-reachable marking at which the
timed executor may rest. -/
theorem routeA_quiescence_sound_reaping {E : Enc} {m0 : CMarking} (P : Premises E m0)
    (hu : ∀ r ∈ E.rows, Unguarded r.t) (hd : ∀ r ∈ E.rows, InputsDistinctPlaces r.t)
    {rp : CRow → Prop} {Q : AMarking → Prop}
    (hproven : ∀ e, ReachE E e → ¬ (DeadER E rp e ∧ Q (agg E.C E.k e))) :
    ∀ m, ReachNu E.C E.rows m0 m → ¬ (NuRest rp E.rows m ∧ Q (alpha m)) := by
  intro m h ⟨hrest, hq⟩
  obtain ⟨e, σ, he, hsim⟩ := coloured_simulates P h
  exact hproven e he ⟨dead_transfer_reaping P.classOK hu hd hsim hrest, (agg_of_sim hsim) ▸ hq⟩

/-- **A reap-quiescent count marking is a ν rest marking.** If every flat row that `α(m)`
enables is reapable (`ReapAware.ReapQuiescentA`, what `rest_sound` gives of every rest), then
every row is reapable or ν-disabled at `m`: a ν-enabled row is count-enabled at `α(m)`. -/
theorem nuRest_of_reapQuiescent {rows : List CRow} {m : CMarking} {rpT : Transition → Bool}
    (hG : ∀ r ∈ rows, GuardFreeConsumeAll r.t)
    (h : ReapAware.ReapQuiescentA rpT (rows.map CRow.flat) (alpha m)) :
    NuRest (fun r => rpT r.t = true) rows m := by
  intro r hr
  by_cases hrp : rpT r.t = true
  · exact Or.inl hrp
  · right
    intro hen
    exact hrp (h r.flat (List.mem_map.mpr ⟨r, hr, rfl⟩)
      (prop1_step_deposit m r.t r.d (hG r hr) hen.1).1)

/-- **The shipped reap-aware Route A query is sound for the executor.** A `Proven` of
`encode_coloured_quiescent` with the rows of `R` skipped (`DeadERs`), where `R` marks exactly
the rows whose timing is reapable (`hR`), rules out `Q` at every marking a timed run of the flat
rows rests at, on either backend and under any schedule (`ReapAware.RestsAt`), provided the
marking is `α(m)` for a ν-reachable `m` (P6). -/
theorem routeA_reap_aware_sound {E : Enc} {m0 : CMarking} (P : Premises E m0)
    (hu : ∀ r ∈ E.rows, Unguarded r.t) (hd : ∀ r ∈ E.rows, InputsDistinctPlaces r.t)
    {R : List String} {Q : AMarking → Prop}
    (hproven : ∀ e, ReachE E e → ¬ (DeadERs E R e ∧ Q (agg E.C E.k e)))
    {enforce : Nat → Nat → Cell → Cell} {tm : Transition → ReapAware.TTiming}
    (hR : ∀ r ∈ E.rows, reapT R r.t = ReapAware.reapable tm r.t)
    {m : CMarking} (hm : ReachNu E.C E.rows m0 m)
    (hrest : ReapAware.RestsAt enforce tm (E.rows.map CRow.flat) (alpha m0) (alpha m)) :
    ¬ Q (alpha m) := by
  intro hq
  have hrq := (ReapAware.rest_sound hrest).2
  have hrq' : ReapAware.ReapQuiescentA (reapT R) (E.rows.map CRow.flat) (alpha m) := by
    intro ft hft hen
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hft
    show reapT R r.t = true
    rw [hR r hr]
    exact hrq r.flat hft hen
  refine routeA_quiescence_sound_reaping P hu hd (rp := fun r => reapT R r.t = true)
    (fun e he h => hproven e he ⟨deadERs_iff.mpr h.1, h.2⟩) m hm
    ⟨nuRest_of_reapQuiescent P.guardFree hrq', hq⟩

/-! ## The witness: the strict Route A query misses a reap -/

namespace ReapW

open Libpetri.Novel.RouteA.Retro
open Libpetri.Novel.ReapingVsUntimed

/-! Places: `0 = p₀`, `1 = p₁` (the sink), `2 = a`, `3 = b` (the join's keys), `4 = done`. -/

/-- `ReapingVsUntimed.lean`'s witness transition is an `mkT` row. -/
theorem tR_eq : tR = mkT "t" [0] := rfl

/-- The ν-join `join : a, b → done`, matched on its keys `a` and `b`, timing `immediate`. -/
def tJ : Transition := mkT "join" [2, 3]

/-- The row of `t : p₀ → p₁` (timing `window(3, 5)`), untouched by colour. -/
def rW : CRow := ⟨tR, [1], .untouched⟩
/-- The join's row. -/
def rJ : CRow := ⟨tJ, [4], .join [2, 3] []⟩
def rowsW : List CRow := [rW, rJ]

/-- The coloured places: the join's keys. -/
def CW : List PlaceId := [2, 3]

/-- The rows as `build_plan` receives them: only the join has a `match_spec`. -/
def srcW : List SrcRow := [⟨tR, [1], none, false, []⟩, ⟨tJ, [4], some ⟨[2, 3], []⟩, false, []⟩]

/-- The weighting the simplex returns on this net: `a + b`, denominator one. Nothing produces into
a key, so the slot-bound program's optimum is `0` (the old semiflow bound was `0` too, from the
laws `a + done` and `b + done`). -/
def yW : Weight := fun p => if p = 2 ∨ p = 3 then 1 else 0
/-- The simplex's answer: denominator `1`, weighting `yW`. -/
def ansW : Option (Nat × Weight) := some (1, yW)

/-- The ν initial marking: one token (any payload) on `p₀`. -/
def m0W : CMarking := mk [[0]]

theorem alpha_m0W : alpha m0W = a0R := by
  funext p
  rcases p with _ | p
  · rfl
  · simp [alpha, m0W, mk, a0R]

/-- **`build_plan` accepts the net** with the keys coloured and `k = 0`: the checker accepts the
simplex's answer, and `k = 0` is refused only when every place is coloured. -/
theorem planW : buildPlan 5 CW false (alpha m0W) ansW srcW = some (0, rowsW) := by
  rfl

/-- The Route A encoding of that plan, with no conjoined invariant. -/
def encW : Enc := ⟨CW, 0, 5, rowsW, [], alpha m0W⟩

theorem unguarded_mkT (name : String) (ins : List PlaceId) : Unguarded (mkT name ins) := by
  intro s hs
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hs
  rfl

theorem distinct_mkT (name : String) (ins : List PlaceId) :
    InputsDistinctPlaces (mkT name ins) := by
  intro s hs
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hs
  simp [specAt_mkT, inp1, hq]

/-- **Every premise of `routeA_quiescence_sound` holds of the witness**, through
`buildPlan_premises` from the plan `build_plan` returns. No fact about the simplex is needed:
the checker vouched for the bound. -/
theorem premisesW : Premises encW m0W := by
  refine buildPlan_premises planW (by decide) (by decide) ?_ (by simp) ?_
  · intro s hs
    simp only [srcW, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact guardFree_mkT "t" [0]
    · exact guardFree_mkT "join" [2, 3]
  · intro r hr
    simp only [rowsW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> trivial

theorem unguardedW : ∀ r ∈ encW.rows, Unguarded r.t := by
  intro r hr
  simp only [encW, rowsW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact unguarded_mkT "t" [0]
  · exact unguarded_mkT "join" [2, 3]

theorem distinctW : ∀ r ∈ encW.rows, InputsDistinctPlaces r.t := by
  intro r hr
  simp only [encW, rowsW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact distinct_mkT "t" [0]
  · exact distinct_mkT "join" [2, 3]

/-- Every reachable encoding state has every colour column and `done` empty: at `k = 0` the join
has no colour to fire under, and nothing produces into a key. -/
theorem reach_invW : ∀ e, ReachE encW e → (∀ p c, e.s p c = 0) ∧ e.u 4 = 0 := by
  intro e h
  induction h with
  | refl => exact ⟨fun _ _ => rfl, by simp [e0, encW, CW, alpha, m0W, mk]⟩
  | @tail e1 e2 _ hs ih =>
    obtain ⟨hs0, hu4⟩ := ih
    obtain ⟨r, hr, hE⟩ := hs
    simp only [encW, rowsW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have hs' : e2.s = e1.s := hE.s
      refine ⟨fun p c => by rw [hs']; exact hs0 p c, ?_⟩
      rw [hE.u]
      exact (uFire_off_row (r := rW) tR_eq (by decide) (by decide)).trans hu4
    · exfalso
      obtain ⟨c, _, hkeys, _⟩ := hE.s
      have h2 := hkeys 2 (by simp)
      rw [hs0 2 c] at h2
      omega

/-- The `DeadlockFree` clause the property conjoins: a token off the sink `{p₁}`. -/
def QW : AMarking → Prop := Strands sinksR 5

/-- **The strict Route A query is `Proven`**: no encoding state is `DeadE` and strands a token.
`t` is disabled only with `p₀` empty, and nothing else ever holds a token. -/
theorem untimed_routeA_proven :
    ∀ e, ReachE encW e → ¬ (DeadE encW e ∧ QW (agg encW.C encW.k e)) := by
  rintro e he ⟨hdead, q, hq5, hqs, hqa⟩
  obtain ⟨hs0, hu4⟩ := reach_invW e he
  have hq0 : q = 0 := by
    have hq1 : q ≠ 1 := fun h => hqs (by simp [sinksR, h])
    have hcase : q = 0 ∨ q = 2 ∨ q = 3 ∨ q = 4 := by omega
    rcases hcase with rfl | rfl | rfl | rfl
    · rfl
    · simp [agg, encW, CW, hs0] at hqa
    · simp [agg, encW, CW, hs0] at hqa
    · simp [agg, encW, CW, hu4] at hqa
  subst hq0
  have hqa' : 1 ≤ e.u 0 := by simpa [agg, encW, CW] using hqa
  rcases hdead rW (by simp [encW, rowsW]) with hdis | hcol
  · rcases hdis with ⟨p, _, hp⟩ | ⟨p, hp, _⟩ | ⟨p, hp, _⟩
    · rw [show rW.t = mkT "t" [0] from rfl, pre_mkT] at hp
      by_cases h0 : p = 0
      · subst h0; simp at hp; omega
      · simp [h0] at hp
    · simp [rW, tR] at hp
    · simp [rW, tR] at hp
  · exact hcol

/-- The set `reaping::reapable_transitions` returns for the witness: `t` (a window). -/
def RW : List String := ["t"]

/-- **The shipped reap-aware query is violated at the seed**: the row of `t` is skipped, the
join is disabled for every colour (at `k = 0` there is none), and `{p₀}` strands a token. -/
theorem reapAware_query_violated :
    ReachE encW (e0 encW) ∧ DeadERs encW RW (e0 encW) ∧ QW (agg encW.C encW.k (e0 encW)) := by
  refine ⟨Relation.ReflTransGen.refl, fun r hr => ?_, ?_⟩
  · have hf : encW.rows.filter (fun r => !reapT RW r.t) = [rJ] := rfl
    rw [hf, List.mem_singleton] at hr
    subst hr
    exact Or.inr fun c _ => ⟨2, by simp, rfl⟩
  · exact ⟨0, by decide, by decide, by simp [agg, e0, encW, CW, alpha, m0W, mk]⟩

/-- The witness timing as `Novel/ReapAware.lean` reads it: `t = window(3, 5)` (tolerance folded
in), the join `immediate`. -/
def tmW : Transition → ReapAware.TTiming :=
  fun t => if t.name = "t" then { earliest := 3, latest := some 5 } else
    { earliest := 0, latest := none }

/-- `RW` marks exactly the rows whose timing is reapable. -/
theorem RW_faithful : ∀ r ∈ encW.rows, reapT RW r.t = ReapAware.reapable tmW r.t := by
  intro r hr
  simp only [encW, rowsW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> decide

/-- The flat rows the executor runs. -/
def netW : FlatNet := rowsW.map CRow.flat

theorem netW_eq : netW = [(tR, [1]), (tJ, [4])] := rfl

/-- **Both backends' runs `[0, 10]` rest at `{p₀}`**: cycle 0 enables `t` and fires nothing
(its window opens at 3), the join is never enabled, and cycle 10 reaps `t`, so no bit is set. -/
theorem restsW (enforce : Nat → Nat → Cell → Cell)
    (h0 : (ReapAware.enf enforce tmW 0 ⟨a0R, ReapAware.initCells⟩ tR).enabled = true)
    (h10 : ∀ ft ∈ netW, (ReapAware.enf enforce tmW 10
      ⟨a0R, fun t => { ReapAware.enf enforce tmW 0 ⟨a0R, ReapAware.initCells⟩ t with
        dirty := false }⟩ ft.1).enabled = false) :
    ReapAware.RestsAt enforce tmW netW a0R a0R := by
  refine ⟨⟨a0R, fun t => { ReapAware.enf enforce tmW 0 ⟨a0R, ReapAware.initCells⟩ t with
      dirty := false }⟩, 10, ?_, ?_, rfl⟩
  · refine Relation.ReflTransGen.single ⟨0, ?_, Relation.ReflTransGen.refl,
      fun _ h => Or.inl h, fun _ _ _ hne => absurd rfl hne⟩
    intro hh
    have := hh (tR, [1]) (by simp [netW_eq])
    rw [h0] at this
    exact Bool.noConfusion this
  · exact h10

theorem restsW_BB : ReapAware.RestsAt enforceBB tmW netW a0R a0R := by
  refine restsW enforceBB (by decide) fun ft hft => ?_
  rw [netW_eq, List.mem_cons, List.mem_singleton] at hft
  rcases hft with rfl | rfl <;> decide

theorem restsW_PB : ReapAware.RestsAt enforcePB tmW netW a0R a0R := by
  refine restsW enforcePB (by decide) fun ft hft => ?_
  rw [netW_eq, List.mem_cons, List.mem_singleton] at hft
  rcases hft with rfl | rfl <;> decide

/-- **Reaping breaks the strict Route A quiescence verdict, and the shipped reap-aware query
sees it.**
1. `build_plan` returns a plan with `C = [a, b]` and `k = 0`, and every premise of
   `routeA_quiescence_sound` holds.
2. The strict `DeadlockFree` query (`DeadE`, what `assume_no_reaping` asks, `deadERs_nil`) is
   `Proven`.
3. Both backends' timed runs of the flat rows, cycles `[0, 10]`, rest at `α(m₀) = {p₀}`.
4. `m₀` is ν-reachable, a rest marking (`t` reapable) that strands a token, and not ν-dead (`t`
   is enabled), which is why the strict transfer does not reach it.
5. The shipped reap-aware query (`DeadERs` with `RW = ["t"]`, which marks exactly the reapable
   rows) is violated at the seed, so it is not `Proven`: `routeA_reap_aware_sound` could not
   have been applied, as it must not be. -/
theorem reaping_breaks_routeA_quiescence :
    buildPlan 5 CW false (alpha m0W) ansW srcW = some (0, rowsW) ∧ Premises encW m0W ∧
      (∀ e, ReachE encW e → ¬ (DeadERs encW [] e ∧ QW (agg encW.C encW.k e))) ∧
      ReapAware.RestsAt enforceBB tmW netW (alpha m0W) (alpha m0W) ∧
      ReapAware.RestsAt enforcePB tmW netW (alpha m0W) (alpha m0W) ∧
      ReachNu encW.C encW.rows m0W m0W ∧
      NuRest (fun r => reapT RW r.t = true) encW.rows m0W ∧ QW (alpha m0W) ∧
      ¬ NuDead encW.rows m0W ∧
      (∀ r ∈ encW.rows, reapT RW r.t = ReapAware.reapable tmW r.t) ∧
      ¬ (∀ e, ReachE encW e → ¬ (DeadERs encW RW e ∧ QW (agg encW.C encW.k e))) := by
  refine ⟨planW, premisesW, fun e he h => untimed_routeA_proven e he ⟨deadERs_nil.mp h.1, h.2⟩,
    alpha_m0W ▸ restsW_BB, alpha_m0W ▸ restsW_PB, Relation.ReflTransGen.refl, ?_, ?_, ?_,
    RW_faithful, fun hp => hp _ reapAware_query_violated.1 reapAware_query_violated.2⟩
  · intro r hr
    simp only [encW, rowsW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Or.inl (by decide)
    · exact Or.inr fun hen => absurd hen.1 (by decide)
  · rw [alpha_m0W]
    exact ⟨0, by decide, by decide, by decide⟩
  · intro hdead
    exact hdead rW (by simp [encW, rowsW]) ⟨by decide, trivial⟩

end ReapW

end Libpetri.Novel.RouteA
