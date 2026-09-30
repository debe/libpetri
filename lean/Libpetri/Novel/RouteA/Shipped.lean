import Libpetri.Novel.RouteA.Reaping

/-!
# Route A as shipped: the self-loop consumer, and the premises it no longer needs

`Model.lean` models the `Class::Consume` rule of `encode_coloured` in its old write order
(`sConsume`): the input's decrement was pushed first and each coloured output's increment after
it, and `encode_rule` keeps the last write per column, so a consumer that relays into its own
input wrote `m_inp_c + 1`. That was a live wrong `Proven` (`Retrodict.lean`,
`self_loop_consume_false_proven`), and the simulation theorem carried `ConsumeNoSelfLoop` as a
premise nothing checked.

The shipped `Class::Consume` arm now nets a self-loop to zero, as the `Class::Join` arm nets a
key that is also a relay target: the input column keeps its `>= 1` guard and gets no update when
it is also an output, and every other output gets `+ 1`. That is exactly `sJoin [inp] outs`, the
join rule on the one key `inp` with relay targets `outs`, under the join's colour guard
`∀ p ∈ [inp], 1 ≤ s p c`. So the shipped encoder encodes a row of class `consume inp outs` as the
model encodes a row of class `join [inp] outs` (`Cls.shipped`, `Enc.shipped`), and:

* `nuStep_shipped`: the ν semantics of the two classes is the same step (a consumer takes some
  `v` resident in `inp` and appends it to each output; a one-key join takes a `v` present in its
  key and appends it to each relay target), so `ReachNu` does not change (`reachNu_shipped`);
* `noSelfLoop_shipped`: every shipped class meets `ConsumeNoSelfLoop` (there is no consumer
  class left);
* **`premises_shipped`**: `PremisesS` (`Plan.lean`: what `build_plan` returns and the verifier
  establishes, `buildPlanG_premisesS`) gives the full `Premises` of the shipped encoding;
* **`routeA_safety_sound_shipped`**, **`routeA_quiescence_sound_shipped`**: a `Proven` of the
  shipped encoding holds of every ν-reachable marking, with no self-loop premise. A ν-dead
  marking is ν-dead for the shipped classes (`nuDead_shipped`).
* **`selfLoop_premises_shipped`**: on `Retrodict.lean`'s self-loop witness, where the old encoding
  proved a false bound, every premise of the shipped encoding holds, so the shipped encoding
  covers the run that reaches `done`.

The encoder's `debug_assert` against a second write to one column (`encode_rule`) is what makes
the netting necessary; it is not modelled.
-/

namespace Libpetri.Novel.RouteA

open Libpetri
open Libpetri.Novel.ForwardDeposit
open Libpetri.Novel.LinearBound

/-- The class the shipped `encode_coloured` encodes a row by. -/
def Cls.shipped : Cls → Cls
  | .consume inp outs => .join [inp] outs
  | c => c

/-- A row with its shipped class. -/
def CRow.shipped (r : CRow) : CRow := ⟨r.t, r.d, r.cls.shipped⟩

/-- The encoding the shipped `encode_coloured` emits for `E`. -/
def Enc.shipped (E : Enc) : Enc := { E with rows := E.rows.map CRow.shipped }

@[simp] theorem CRow.shipped_t (r : CRow) : r.shipped.t = r.t := rfl
@[simp] theorem CRow.shipped_d (r : CRow) : r.shipped.d = r.d := rfl
@[simp] theorem CRow.shipped_flat (r : CRow) : r.shipped.flat = r.flat := rfl

/-- The shipped consumer rule is the join rule on its one input. -/
theorem colourStep_consume_shipped {C : List PlaceId} {k : Nat} {inp : PlaceId}
    {outs : List PlaceId} {s s' : PlaceId → Nat → Nat} :
    ColourStep C k (Cls.consume inp outs).shipped s s' ↔
      ∃ c, c < k ∧ 1 ≤ s inp c ∧ s' = sJoin [inp] outs c s := by
  simp [Cls.shipped, ColourStep]

/-- **No self-loop premise is left**: the shipped encoder has no consumer class. -/
theorem noSelfLoop_shipped (r : CRow) : ConsumeNoSelfLoop r.shipped.cls := by
  obtain ⟨t, d, cls⟩ := r
  cases cls <;> trivial

theorem classShape_shipped {C : List PlaceId} {r : CRow} (h : ClassShape C r) :
    ClassShape C r.shipped := by
  obtain ⟨t, d, cls⟩ := r
  cases cls with
  | consume inp outs =>
    obtain ⟨hin, hout, hp⟩ := h
    refine ⟨List.cons_ne_nil _ _, fun p hp' => ?_, hout, fun p hpC => ?_⟩
    · rw [List.mem_singleton.mp hp']; exact hin
    · have := hp p hpC
      simpa [List.mem_singleton] using this
  | _ => exact h

theorem classOK_shipped {C : List PlaceId} {r : CRow} (h : ClassOK C r) :
    ClassOK C r.shipped :=
  ⟨h.arcs, classShape_shipped h.shape⟩

/-- **The ν step does not change**: a consumer of `inp` and a join keyed on `inp` alone take the
same names and deposit them in the same places. -/
theorem nameEffect_shipped {C : List PlaceId} {cls : Cls} {m m' : CMarking} :
    NameEffect C cls.shipped m m' ↔ NameEffect C cls m m' := by
  cases cls with
  | consume inp outs =>
    simp only [Cls.shipped, NameEffect, List.mem_singleton, forall_eq]
  | _ => rfl

theorem nuStep_shipped {C : List PlaceId} {r : CRow} {m m' : CMarking} :
    NuStep C r.shipped m m' ↔ NuStep C r m m' := by
  constructor
  · intro h
    exact ⟨h.enabled, h.counts, nameEffect_shipped.mp h.names⟩
  · intro h
    exact ⟨h.enabled, h.counts, nameEffect_shipped.mpr h.names⟩

theorem reachNu_shipped {C : List PlaceId} {rows : List CRow} {m0 m : CMarking} :
    ReachNu C (rows.map CRow.shipped) m0 m ↔ ReachNu C rows m0 m := by
  have key : ∀ a b, (∃ r ∈ rows.map CRow.shipped, NuStep C r a b) ↔
      (∃ r ∈ rows, NuStep C r a b) := fun a b => by
    constructor
    · rintro ⟨r', hr', hs⟩
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr'
      exact ⟨r, hr, nuStep_shipped.mp hs⟩
    · rintro ⟨r, hr, hs⟩
      exact ⟨r.shipped, List.mem_map.mpr ⟨r, hr, rfl⟩, nuStep_shipped.mpr hs⟩
  unfold ReachNu
  have : (fun a b => ∃ r ∈ rows.map CRow.shipped, NuStep C r a b) =
      (fun a b => ∃ r ∈ rows, NuStep C r a b) := by
    funext a b
    exact propext (key a b)
  rw [this]

/-- A shipped row enabled in the ν semantics is enabled as the row it came from. -/
theorem nuEnabled_of_shipped {m : CMarking} {r : CRow} (h : NuEnabled m r.shipped) :
    NuEnabled m r := by
  obtain ⟨t, d, cls⟩ := r
  cases cls with
  | consume inp outs => exact ⟨h.1, trivial⟩
  | _ => exact h

/-- A ν-dead marking is ν-dead for the shipped classes. -/
theorem nuDead_shipped {rows : List CRow} {m : CMarking} (h : NuDead rows m) :
    NuDead (rows.map CRow.shipped) m := by
  intro r' hr' hen
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr'
  exact h r hr (nuEnabled_of_shipped hen)

/-- **The shipped encoding meets every premise of `coloured_simulates`** as soon as the plan
premises hold, with no self-loop condition. -/
theorem premises_shipped {E : Enc} {m0 : CMarking} (P : PremisesS E m0) :
    Premises E.shipped m0 := by
  obtain ⟨y, hpos, hcov, hdec, hk⟩ := P.cover
  refine ⟨P.nodup, P.below, fun r hr => ?_, fun r hr => ?_, fun r hr => ?_, P.seed, P.empty,
    ⟨y, hpos, hcov, fun r hr => ?_, hk⟩, fun y' hy' r hr => ?_⟩
  all_goals
    obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr
  · exact classOK_shipped (P.classOK r0 hr0)
  · exact P.guardFree r0 hr0
  · exact noSelfLoop_shipped r0
  · rw [CRow.shipped_flat]; exact hdec r0 hr0
  · rw [CRow.shipped_t, CRow.shipped_flat]; exact P.laws y' hy' r0 hr0

/-- **Reachability safety, as shipped.** A `Proven` of the shipped name-coloured query holds of
every ν-reachable marking. No self-loop premise. -/
theorem routeA_safety_sound_shipped {E : Enc} {m0 : CMarking} (P : PremisesS E m0)
    {Bad : AMarking → Prop} (hproven : ∀ e, ReachE E.shipped e → ¬ Bad (agg E.C E.k e)) :
    ∀ m, ReachNu E.C E.rows m0 m → ¬ Bad (alpha m) := by
  intro m h
  exact routeA_safety_sound (premises_shipped P) hproven m (reachNu_shipped.mpr h)

/-- **Quiescence, untimed, as shipped.** No self-loop premise. -/
theorem routeA_quiescence_sound_shipped {E : Enc} {m0 : CMarking} (P : PremisesS E m0)
    (hu : ∀ r ∈ E.rows, Unguarded r.t) (hd : ∀ r ∈ E.rows, InputsDistinctPlaces r.t)
    {Q : AMarking → Prop}
    (hproven : ∀ e, ReachE E.shipped e → ¬ (DeadE E.shipped e ∧ Q (agg E.C E.k e))) :
    ∀ m, ReachNu E.C E.rows m0 m → ¬ (NuDead E.rows m ∧ Q (alpha m)) := by
  intro m h ⟨hdead, hq⟩
  have hu' : ∀ r ∈ E.shipped.rows, Unguarded r.t := fun r hr => by
    obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr
    exact hu r0 hr0
  have hd' : ∀ r ∈ E.shipped.rows, InputsDistinctPlaces r.t := fun r hr => by
    obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr
    exact hd r0 hr0
  exact routeA_quiescence_sound (premises_shipped P) hu' hd' hproven m (reachNu_shipped.mpr h)
    ⟨nuDead_shipped hdead, hq⟩

/-! ## The self-loop witness, shipped -/

/-- **On the self-loop witness every premise of the shipped encoding holds**, so its `Proven`
would be sound (`routeA_safety_sound_shipped`); the old encoding proved a bound the ν run
breaks (`Retrodict.self_loop_consume_false_proven`) because its self-loop rule never fired. -/
theorem selfLoop_premises_shipped : Premises (Enc.shipped Retro.encS) Retro.m0S :=
  premises_shipped Retro.selfLoop_premisesS

end Libpetri.Novel.RouteA
