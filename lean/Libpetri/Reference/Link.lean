import Libpetri.Reference.Decide
import Libpetri.Novel.Enumeration

/-!
# The reference firing rule is the development's

`Semantics.lean` states the firing rule once, generically in the place-name type. This module
ties it to the models the rest of the development already proves things about:

* **`ForwardDeposit.StepCD`** (flat place ids, coloured markings, the outcome rule of
  [IO-013]–[IO-016] including forwards of a drained batch): at `N = PlaceId`, a reference step
  between count markings is exactly the α-image of a `StepCD` step (`step_alpha_iff`), for nets
  whose every transition declares an output spec (`StepCD` has no empty spec). Composed with
  `Step.lean`: **`mem_succ_iff_stepCD`**, the executable successor list is the α-image of
  `StepCD`.
* **`Seam.StepNC`** (named executor step on a row): a reference firing is a `StepNC` of the row
  it deposits (`fires_iff_stepNC`, `step_iff_stepNC`).
* **`Seam.NDeadlock`** ([VER-002] `DeadlockFree`, no conditional sinks): `deadlock_iff_NDeadlock`,
  over the net without its reapable transitions (`liveNet`, [TIME-013]).
* **`Novel.Enumeration.rows_enumeration_exact`** ([VER-017]): when every forward draws from a
  `One` / `Exactly` input, a reference step is a `StepAD` step over `ForwardDeposit.flatRows`
  (`step_iff_stepAD`), so the reachable sets agree (`reach_iff_reachAD`) and a completed
  reference exploration discovers exactly the markings a closed enumeration of the fixed rows
  does (**`explore_agrees_enumeration`**). Forwards from `All` / `AtLeast` inputs, which the
  rows cannot express (`drained_forward_has_no_row`), are covered by the first bullet.
-/

namespace Libpetri.Reference.Link

open Libpetri Libpetri.Novel.Seam Libpetri.Novel.ForwardDeposit Libpetri.Reference

/-! ## Named: `StepNC` and `NDeadlock` -/

section Named

variable {N : Type} [DecidableEq N]

/-- **A reference firing is a named executor step** (`Seam.StepNC`) of the row it deposits,
that row being one of the firing's outcomes. -/
theorem fires_iff_stepNC (t : Trans N) (d : List N) (M M' : NCMarking N) :
    Fires t (alphaN M) d (alphaN M') ↔
      (∃ ch, deposit (nconsumed (alphaN M) t.core) t.out ch = some d) ∧
        StepNC M (t.core, d) (depProd d) M' := by
  constructor
  · rintro ⟨hen, hdep, heff⟩
    exact ⟨hdep, ⟨hen, rfl, heff⟩⟩
  · rintro ⟨hdep, ⟨hen, _, heff⟩⟩
    exact ⟨hen, hdep, heff⟩

theorem step_iff_stepNC (net : Net N) (M M' : NCMarking N) :
    Step net (alphaN M) (alphaN M') ↔
      ∃ t ∈ net.transitions, ∃ d, (∃ ch, deposit (nconsumed (alphaN M) t.core) t.out ch = some d)
        ∧ StepNC M (t.core, d) (depProd d) M' := by
  constructor
  · rintro ⟨_, t, ht, _, d, hf⟩
    exact ⟨t, ht, d, (fires_iff_stepNC t d M M').mp hf⟩
  · rintro ⟨t, ht, d, h⟩
    exact ⟨t.core.name, t, ht, rfl, d, (fires_iff_stepNC t d M M').mpr h⟩

/-- The net's transitions as `Seam` rows (quiescence reads only the arcs). -/
def toNNet (net : Net N) : NNet N :=
  { places := net.places, transitions := net.transitions.map fun t => (t.core, []) }

omit [DecidableEq N] in
theorem quiescent_iff_NQuiescent (net : Net N) (m : N → Nat) :
    Quiescent net m ↔ NQuiescent (toNNet net) m := by
  simp [Quiescent, NQuiescent, toNNet]

/-- The net without its reapable transitions: what `encode_quiescent` reads ([TIME-013]). -/
def liveNet (net : Net N) : Net N :=
  { places := net.places, transitions := net.transitions.filter fun t => !t.reapable }

omit [DecidableEq N] in
/-- Reap-quiescence is quiescence of the net without its reapable transitions. -/
theorem reapQuiescent_iff_live (net : Net N) (m : N → Nat) :
    ReapQuiescent net m ↔ Quiescent (liveNet net) m := by
  unfold ReapQuiescent Quiescent liveNet
  constructor
  · intro h t ht
    obtain ⟨hmem, hnr⟩ := List.mem_filter.mp ht
    cases hen : enabledNA m t.core with
    | false => rfl
    | true => simp [h t hmem hen] at hnr
  · intro h t ht hen
    by_contra hr
    have := h t (List.mem_filter.mpr ⟨ht, by simpa using hr⟩)
    rw [hen] at this
    exact Bool.noConfusion this

omit [DecidableEq N] in
/-- **`DeadlockFree`'s violation is `Seam.NDeadlock`** of the net without its reapable
transitions, with no conditional sinks. -/
theorem deadlock_iff_NDeadlock (net : Net N) (sinks : List N) (m : N → Nat) :
    Violates net (.deadlockFree sinks) m ↔ NDeadlock (toNNet (liveNet net)) sinks [] m := by
  simp only [Violates, NDeadlock, Resting, IsMarker, reapQuiescent_iff_live,
    quiescent_iff_NQuiescent]
  simp

end Named

/-! ## Flat place ids: `StepCD` -/

/-- An input arc at flat ids (no guard, [IO-006]). -/
def toInSpec (s : NInSpec PlaceId) : InSpec := { place := s.place, card := s.card, guard := none }

def toTransition (t : NTransition PlaceId) : Transition :=
  { name := t.name, inputs := t.inputs.map toInSpec, inhibitors := t.inhibitors,
    reads := t.reads, resets := t.resets }

def toOutSpec : Out PlaceId → OutSpec
  | .place p => .place p
  | .and l r => .and (toOutSpec l) (toOutSpec r)
  | .xor l r => .xor (toOutSpec l) (toOutSpec r)
  | .timeout c => .timeout (toOutSpec c)
  | .forward s d => .forward s d

/-- The transitions with an output spec, as `Novel.ForwardDeposit.SpecNet`. -/
def toSpecNet (net : Net PlaceId) : SpecNet :=
  net.transitions.filterMap fun t => t.out.map fun o => (toTransition t.core, toOutSpec o)

/-- Every transition declares an output spec. -/
def HasOutputs (net : Net PlaceId) : Prop := ∀ t ∈ net.transitions, t.out.isSome

theorem branches_toOutSpec : ∀ o : Out PlaceId,
    Novel.ForwardDeposit.branches (toOutSpec o) = o.branches
  | .place _ => rfl
  | .forward _ _ => rfl
  | .and l r => by
    simp [toOutSpec, Novel.ForwardDeposit.branches, Out.branches, Novel.ForwardDeposit.cross, cross,
      branches_toOutSpec l, branches_toOutSpec r]
  | .xor l r => by
    simp [toOutSpec, Novel.ForwardDeposit.branches, Out.branches, branches_toOutSpec l,
      branches_toOutSpec r]
  | .timeout c => by simp [toOutSpec, Novel.ForwardDeposit.branches, Out.branches, branches_toOutSpec c]

theorem timeoutDeposits_toOutSpec (c : PlaceId → Nat) : ∀ o : Out PlaceId,
    Novel.ForwardDeposit.timeoutDeposits c (toOutSpec o) = o.timeoutDeposits c
  | .place _ => rfl
  | .forward _ _ => rfl
  | .and l r => by
    simp [toOutSpec, Novel.ForwardDeposit.timeoutDeposits, Out.timeoutDeposits, Novel.ForwardDeposit.cross,
      cross, timeoutDeposits_toOutSpec c l, timeoutDeposits_toOutSpec c r]
  | .xor l r => by
    simp [toOutSpec, Novel.ForwardDeposit.timeoutDeposits, Out.timeoutDeposits,
      timeoutDeposits_toOutSpec c l, timeoutDeposits_toOutSpec c r]
  | .timeout o => by
    simp [toOutSpec, Novel.ForwardDeposit.timeoutDeposits, Out.timeoutDeposits,
      timeoutDeposits_toOutSpec c o]

theorem findTimeout_toOutSpec : ∀ o : Out PlaceId,
    Novel.ForwardDeposit.findTimeout (toOutSpec o) = o.findTimeout.map toOutSpec
  | .place _ => rfl
  | .forward _ _ => rfl
  | .timeout _ => rfl
  | .and l r => by
    simp only [toOutSpec, Novel.ForwardDeposit.findTimeout, Out.findTimeout, findTimeout_toOutSpec l,
      findTimeout_toOutSpec r]
    cases l.findTimeout <;> rfl
  | .xor l r => by
    simp only [toOutSpec, Novel.ForwardDeposit.findTimeout, Out.findTimeout, findTimeout_toOutSpec l,
      findTimeout_toOutSpec r]
    cases l.findTimeout <;> rfl

theorem deposit_toOutSpec (c : PlaceId → Nat) (o : Out PlaceId) (ch : Choice) :
    Novel.ForwardDeposit.deposit c (toOutSpec o) ch = Reference.deposit c (some o) ch := by
  cases ch with
  | action i => simp [Novel.ForwardDeposit.deposit, Reference.deposit, branches_toOutSpec]
  | timedOut j =>
    simp only [Novel.ForwardDeposit.deposit, Reference.deposit, findTimeout_toOutSpec]
    cases o.findTimeout <;> simp [timeoutDeposits_toOutSpec]

theorem enabledC_toTransition (m : CMarking) (t : NTransition PlaceId) :
    enabledC m (toTransition t) = enabledNA (alpha m) t := by
  simp only [enabledC, enabledNA, toTransition, List.all_map, Function.comp_def, matchCount,
    toInSpec, alpha]
  rfl

theorem specAt_toTransition (t : NTransition PlaceId) (n : PlaceId) :
    specAt (toTransition t) n = (nspecAt t n).map toInSpec := by
  unfold specAt nspecAt toTransition
  rw [List.find?_map]
  congr 1

theorem consumedAt_toTransition (m : CMarking) (t : NTransition PlaceId) (n : PlaceId) :
    consumedAt m (toTransition t) n = nconsumed (alpha m) t n := by
  unfold consumedAt nconsumed
  rw [specAt_toTransition]
  cases hs : nspecAt t n with
  | none => rfl
  | some s =>
    have hp := (nspecAt_place hs).2
    simp [consumeCount, matchCount, toInSpec, alpha, hp]

theorem alphaFireC_toTransition (m : CMarking) (t : NTransition PlaceId) (d : List PlaceId) :
    alphaFireC m (toTransition t) (fun p => d.count p) = fireNC (alpha m) t (depProd d) := by
  funext p
  simp only [alphaFireC, fireNC, consumedAt_toTransition, depProd]
  simp [toTransition, alpha]

/-- Some coloured marking has the given counts. -/
def lift (a : AMarking) : CMarking := fun p => List.replicate (a p) 0

theorem alpha_lift (a : AMarking) : alpha (lift a) = a := by
  funext p; simp [alpha, lift]

theorem mem_toSpecNet {net : Net PlaceId} {tr0 : Transition × OutSpec} :
    tr0 ∈ toSpecNet net ↔ ∃ t ∈ net.transitions, ∃ o, t.out = some o ∧
      tr0 = (toTransition t.core, toOutSpec o) := by
  unfold toSpecNet
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨t, ht, h⟩
    cases ho : t.out with
    | none => rw [ho] at h; simp at h
    | some o =>
      rw [ho] at h
      exact ⟨t, ht, o, ho, (Option.some.inj h).symm⟩
  · rintro ⟨t, ht, o, ho, rfl⟩
    exact ⟨t, ht, by rw [ho]; rfl⟩

/-- **The reference step is `StepCD`'s α-image** at flat place ids, on nets whose transitions
all declare an output spec: forwards of a drained batch included. -/
theorem step_alpha_iff {net : Net PlaceId} (hout : HasOutputs net) (m m' : CMarking) :
    StepCD (toSpecNet net) m m' ↔ Step net (alpha m) (alpha m') := by
  have hcons : nconsumed (alpha m) = fun t => consumedAt m (toTransition t) := by
    funext t n; exact (consumedAt_toTransition m t n).symm
  constructor
  · rintro ⟨tr0, hto, hen, ch, d, hdep, heff⟩
    obtain ⟨t, ht, o, ho, rfl⟩ := mem_toSpecNet.mp hto
    refine ⟨t.core.name, t, ht, rfl, d, ?_, ⟨ch, ?_⟩, ?_⟩
    · rwa [enabledC_toTransition] at hen
    · rw [ho, ← deposit_toOutSpec]
      have : nconsumed (alpha m) t.core = consumedAt m (toTransition t.core) := by
        rw [hcons]
      rw [this]; exact hdep
    · rw [heff, alphaFireC_toTransition]
  · rintro ⟨_, t, ht, _, d, hen, ⟨ch, hdep⟩, heff⟩
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp (hout t ht)
    refine ⟨(toTransition t.core, toOutSpec o), mem_toSpecNet.mpr ⟨t, ht, o, ho, rfl⟩, ?_, ch, d,
      ?_, ?_⟩
    · rwa [enabledC_toTransition]
    · rw [deposit_toOutSpec, ← ho]
      have : consumedAt m (toTransition t.core) = nconsumed (alpha m) t.core := by
        rw [hcons]
      rw [this]; exact hdep
    · rw [heff, alphaFireC_toTransition]

/-- **Headline (a) against `StepCD`.** At flat place ids, the executable successor list is
exactly the α-image of `Novel.ForwardDeposit.StepCD`: `m'` is listed iff some coloured markings with
the counts of `m` and `m'` are one `StepCD` step apart. -/
theorem mem_succ_iff_stepCD {net : Net PlaceId} (hout : HasOutputs net) {m m' : Marking PlaceId}
    (hc : Canon m) (hc' : Canon m') :
    (∃ l, (l, m') ∈ succ net m) ↔
      ∃ M M', alpha M = get m ∧ alpha M' = get m' ∧ StepCD (toSpecNet net) M M' := by
  constructor
  · rintro ⟨l, h⟩
    refine ⟨lift (get m), lift (get m'), alpha_lift _, alpha_lift _, ?_⟩
    rw [step_alpha_iff hout, alpha_lift, alpha_lift]
    exact ⟨l, (mem_succ_iff hc hc' l).mp h⟩
  · rintro ⟨M, M', hM, hM', hs⟩
    rw [step_alpha_iff hout, hM, hM'] at hs
    obtain ⟨l, hl⟩ := hs
    exact ⟨l, (mem_succ_iff hc hc' l).mpr hl⟩

/-! ## Fixed forwards: `ReachAD` and the VER-017 enumeration -/

/-- Every forward draws from a `One` / `Exactly` input (or none): `Novel.ForwardDeposit.FixedForwards`. -/
def FixedForwardsNet (net : Net PlaceId) : Prop :=
  ∀ tr0 ∈ toSpecNet net, FixedForwards tr0.1 tr0.2

theorem guardFree_toTransition (t : NTransition PlaceId) : GuardFreeConsumeAll (toTransition t) := by
  intro s hs _
  obtain ⟨s', _, rfl⟩ := List.mem_map.mp hs
  rfl

theorem guardNone_toTransition (t : NTransition PlaceId) :
    ∀ s ∈ (toTransition t).inputs, s.guard = none := by
  intro s hs
  obtain ⟨s', _, rfl⟩ := List.mem_map.mp hs
  rfl

/-- **With fixed forwards, a reference step is a step of the fixed rows** (`StepAD` over
`flatRows`), the relation `rows_enumeration_exact` explores. -/
theorem step_iff_stepAD {net : Net PlaceId} (hout : HasOutputs net) (hfix : FixedForwardsNet net)
    (a a' : AMarking) : Step net a a' ↔ StepAD (flatRows (toSpecNet net)) a a' := by
  have hG : ∀ tr ∈ flatRows (toSpecNet net), GuardFreeConsumeAll tr.1 := by
    intro tr htr
    obtain ⟨tr0, hto, htr'⟩ := List.mem_flatMap.mp htr
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp htr'
    obtain ⟨t, _, _, _, rfl⟩ := mem_toSpecNet.mp hto
    exact guardFree_toTransition t.core
  constructor
  · intro h
    rw [← alpha_lift a, ← alpha_lift a', ← step_alpha_iff hout] at h
    have := stepCR_simulated hG (stepCD_stepCR hfix h)
    rwa [alpha_lift, alpha_lift] at this
  · rintro ⟨tr, htr, hen, heff⟩
    obtain ⟨tr0, hto, htr'⟩ := List.mem_flatMap.mp htr
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp htr'
    obtain ⟨t, ht, o, ho, rfl⟩ := mem_toSpecNet.mp hto
    obtain ⟨ch, hch⟩ := fixedRows_mem_deposit (m := lift a) (hfix _ hto) hr
    have henC : enabledC (lift a) (toTransition t.core) = true := by
      rw [enabledC_guardFree (guardNone_toTransition t.core), alpha_lift]; exact hen
    obtain ⟨_, hfire⟩ := prop1_step_deposit (lift a) (toTransition t.core) r
      (guardFree_toTransition t.core) henC
    rw [← alpha_lift a, ← alpha_lift a', ← step_alpha_iff hout]
    refine ⟨_, hto, henC, ch, r, hch, ?_⟩
    rw [hfire, alpha_lift, alpha_lift]
    exact heff

theorem reach_iff_reachAD {net : Net PlaceId} (hout : HasOutputs net)
    (hfix : FixedForwardsNet net) (a0 a : AMarking) :
    Reach net a0 a ↔ ReachAD (flatRows (toSpecNet net)) a0 a := by
  have : Step net = StepAD (flatRows (toSpecNet net)) := by
    funext x y; exact propext (step_iff_stepAD hout hfix x y)
  unfold Reach ReachAD
  rw [this]

/-- **The reference agrees with the [VER-017] enumeration model**: on a net with fixed forwards,
when both the reference exploration and `Novel.Enumeration.build` over the fixed rows complete, they
discover the same markings. -/
theorem explore_agrees_enumeration [Hashable PlaceId] [DecidableEq AMarking]
    {net : Net PlaceId} (hout : HasOutputs net) (hfix : FixedForwardsNet net)
    {cap maxClasses fuel : Nat} {m0 : Marking PlaceId} (hc : Canon m0)
    (h : (exploreNet net cap m0).2 = true)
    (h' : (Novel.Enumeration.build (Novel.Enumeration.succRows (flatRows (toSpecNet net))) maxClasses fuel
      (get m0)).2 = true) (a : AMarking) :
    (∃ y, y ∈ (exploreNet net cap m0).1 ∧ get y = a) ↔
      a ∈ (Novel.Enumeration.build (Novel.Enumeration.succRows (flatRows (toSpecNet net))) maxClasses fuel
        (get m0)).1 := by
  rw [(explored_eq_reachable hc h).2 a, reach_iff_reachAD hout hfix,
    ((Novel.Enumeration.rows_enumeration_exact h' (fun _ => false)).1 a)]

end Libpetri.Reference.Link
