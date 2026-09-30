import Libpetri.Novel.EnvSemantics.Quiescence
import Libpetri.Novel.Enumeration

/-!
# The supplied-environment successor of the state-class graphs ([VER-006] AC3, AC8, `89aaeec`)

The state-class graphs (`state_class_graph.rs`, and through `compute_successor` the base layer
of Route B's name-partition graph, `name_state_class_graph.rs`) do not inject. Under
`AlwaysAvailable` / `Bounded(k)` they treat an environment place as an **inexhaustible input**:
`check_place_enabled` answers an input or read arc on one with "supplied" (always, or
`required ≤ k`) whatever it holds, `consume_marking` skips it, a reset still clears it and
`produce_marking` still deposits into it. Inhibitors read its count. That is `enabledSup` /
`fireSup` (`is_enabled` / `find_enabled_transitions` for the first, `compute_successor`
composing `consume_marking` and `produce_marking` for the second); `ReachSup` is the reachable
set of the untimed graph. `succSup` is the successor list, and `sup_enumeration_exact`
instantiates `Enumeration.lean`'s worklist with it: a closed graph's classes are exactly
`ReachSup`, and its verdict decides `ReachSup` exactly. That the Rust `compute_successor` on an
untimed class yields `succSup` as a set is the same assumed premise as `Enumeration.lean`'s
(**Successors**), with the environment gate added.

Its count on an environment place is therefore not the environment's. `89aaeec` made Route B
decline (`route_b_env_observation`) when a verdict would read it: the property reads an
environment place, or an inhibitor tests one (a coloured place or conflict pruning on a shared
environment input are outside this untimed, colourless model).

**What the agreement with the injected encoding needs: four premises.** The two exclusions
Route B checks (no inhibitor on an environment place, `NoEnvInhibitor`; a property that reads no
environment place, `EnvBlind`), and two it does not: a seed capped at `k` on every environment
place, and, under `Bounded(k)`, no transition depositing into an environment place
(`NoEnvDeposit`). No route checks the last two. Without them the executor can hold more than
`k` on an environment place and fire a transition that takes more than `k`, which
`check_place_enabled`'s `required ≤ k` never enables: the graph routes and Route B then return a
wrong `Proven`, and `encode_quiescent`'s `permanently_disabled` a spurious deadlock.

* `reachAE_to_sup`, `sup_to_reachAE`: with no inhibitor on an environment place, the supplied
  graph and the injected encoding reach the same markings **off the environment places**
  (`OffEnvEq`). Under `Bounded(k)` the second direction needs `NoEnvDeposit` (the encoding's
  post-cap, `Step.lean`), and both a capped seed.
* `enabledSup_iff_noReason` / `deadSup_iff_quiescentE`: a class with no enabled transition is
  exactly a marking satisfying `encode_quiescent`'s relaxed conjunct, so the graph routes and the
  CHC route mean the same thing by quiescence.
* `supplied_safety_exact`, `supplied_quiescence_exact` (**Route B under injection**): under the
  four premises, for a property that reads no environment place, the supplied graph's verdict is
  the injected encoding's, and its quiescence is stuck-under-every-injection-future.
* `supplied_executor_sound` / `supplied_enumeration_sound` (**against the executor**): under the
  same premises every untimed executor run's α-image is a `ReachSup` marking off the environment
  places, so a closed supplied graph's `Proven` of an environment-blind property holds for the
  executor.
* **The two premises the routes do not check are needed** (they were live on the Rust until
  `verify_net` started checking them, `Premise.lean`). Each
  witness breaks exactly one premise and states that the other three hold:
  `supplied_bounded_deposit_wrong_proven` (`t0 : one(a) → E`, `t1 : exactly(2, E) → out`,
  `Bounded(1)`, `a = 2`, `E = 0`: the executor reaches `out = 1`, the graph keeps `out = 0`, so
  `PlaceBound(out, 0)` is `Proven`, and `route_b_env_observation` passes the net; only
  `NoEnvDeposit` fails), `supplied_bounded_initial_wrong_proven` (`t1` alone from `E = 2`; only
  the capped seed fails), and `quiescence_bounded_initial_spurious` (`E = 2` with a self-loop
  that keeps the executor live: the relaxed conjunct and the graph both report a deadlock at
  `M0`, the executor never has one; only the capped seed fails).
* Retrodictions of `89aaeec`: `routeB_env_count_frozen` (the property reads the frozen count:
  `PlaceBound(IN, 0)` holds on every class while injection reaches `IN = 1`),
  `routeB_env_inhibitor_unsound` (an inhibitor on an environment place: the graph has no
  quiescent class stranding a token, the injected system has one), and
  `scg_env_read_prefix_unsound` (before `89aaeec` the Rust graph checked a read arc on an
  environment place against its frozen count, so a transition gated on it never fired).

Scope: untimed, as `Quiescence.lean` ("Scope"). The rows here carry no reapable mark, which is
the reapable-free case of `encode_quiescent` and of the graph routes' rest test; the reap-aware
reading is `ReapAware.lean` (and `ReapingVsUntimed.lean` for why it is needed).
-/

namespace Libpetri.Novel.EnvSemantics

open Libpetri Libpetri.Novel.ForwardDeposit Libpetri.Novel.Seam

/-- `check_place_enabled` (`state_class_graph.rs`): an environment place supplies `need` unless
the mode's cap is below it; any other place must hold `need`. -/
def envOK (envs : List PlaceId) (mode : InjMode) (a : AMarking) (p : PlaceId) (need : Nat) :
    Bool :=
  if envs.contains p then !mode.unsupplied need else decide (need ≤ a p)

theorem envOK_true {envs : List PlaceId} {mode : InjMode} {a : AMarking} {p : PlaceId}
    {need : Nat} :
    envOK envs mode a p need = true ↔
      (p ∈ envs → mode.unsupplied need = false) ∧ (p ∉ envs → need ≤ a p) := by
  by_cases h : p ∈ envs <;> simp [envOK, h]

/-- `is_enabled` (`state_class_graph.rs`, untimed): inputs and reads through
`check_place_enabled`, inhibitors on the count. -/
def enabledSup (envs : List PlaceId) (mode : InjMode) (a : AMarking) (t : Transition) : Bool :=
  t.inputs.all (fun s => envOK envs mode a s.place s.card.required)
    && t.inhibitors.all (fun q => a q == 0)
    && t.reads.all (fun q => envOK envs mode a q 1)

/-- `consume_marking` + `produce_marking`: an environment place is not consumed (a reset still
clears it) and receives its deposit; every other place fires as `fireAD`. -/
def fireSup (envs : List PlaceId) (a : AMarking) (t : Transition) (d : Deposit) : AMarking :=
  fun q => if envs.contains q && !t.resets.contains q then a q + d.count q else fireAD a t d q

def StepSup (rows : Rows) (envs : List PlaceId) (mode : InjMode) (a a' : AMarking) : Prop :=
  ∃ tr ∈ rows, enabledSup envs mode a tr.1 = true ∧ a' = fireSup envs a tr.1 tr.2

def ReachSup (rows : Rows) (envs : List PlaceId) (mode : InjMode) (a0 : AMarking) :
    AMarking → Prop :=
  Relation.ReflTransGen (StepSup rows envs mode) a0

/-- No inhibitor arc tests an environment place (`route_b_env_observation` rule 2). -/
def NoEnvInhibitor (rows : Rows) (envs : List PlaceId) : Prop :=
  ∀ tr ∈ rows, ∀ q ∈ tr.1.inhibitors, q ∉ envs

/-- A predicate that reads no environment place (`route_b_env_observation` rule 4). -/
def EnvBlind (envs : List PlaceId) (P : AMarking → Prop) : Prop :=
  ∀ a b, OffEnvEq envs a b → (P a ↔ P b)

theorem EnvBlind.injStable {envs : List PlaceId} {P : AMarking → Prop} (h : EnvBlind envs P) :
    InjStable envs P := by
  intro a p hp ha
  refine (h a (injA a p) ?_).mp ha
  intro q hq
  have : q ≠ p := fun e => hq (e ▸ hp)
  simp [injA, this]

theorem fireAD_congr {a b : AMarking} {q : PlaceId} (h : a q = b q) (t : Transition)
    (d : Deposit) : fireAD a t d q = fireAD b t d q := by
  simp [fireAD, h]

theorem offEnv_fire {envs : List PlaceId} {a b : AMarking} (h : OffEnvEq envs a b)
    (t : Transition) (d : Deposit) : OffEnvEq envs (fireAD a t d) (fireSup envs b t d) := by
  intro q hq
  have hc : envs.contains q = false := by simpa using hq
  simp only [fireSup, hc, Bool.false_and, Bool.false_eq_true, if_false]
  exact fireAD_congr (h q hq) t d

/-! ## The two reachable sets agree off the environment places -/

theorem enabledSup_of_enabledA {envs : List PlaceId} {mode : InjMode} {a b : AMarking}
    {t : Transition} (hcap : mode.capped envs a = true) (hEq : OffEnvEq envs a b)
    (hInh : ∀ q ∈ t.inhibitors, q ∉ envs) (hen : enabledA a t = true) :
    enabledSup envs mode b t = true := by
  unfold enabledA at hen
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at hen
  obtain ⟨⟨hIn, hH⟩, hR⟩ := hen
  unfold enabledSup
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, envOK_true]
  refine ⟨⟨fun s hs => ⟨fun he => ?_, fun he => ?_⟩, fun q hq => ?_⟩,
    fun q hq => ⟨fun he => ?_, fun he => ?_⟩⟩
  · cases mode with
    | always => rfl
    | bounded k =>
      have := (capped_bounded_iff.mp hcap) s.place he
      have := hIn s hs
      simp [InjMode.unsupplied]; omega
  · rw [← hEq _ he]; exact hIn s hs
  · rw [← hEq _ (hInh q hq)]; exact hH q hq
  · cases mode with
    | always => rfl
    | bounded k =>
      have := (capped_bounded_iff.mp hcap) q he
      have := hR q hq
      simp [InjMode.unsupplied]; omega
  · rw [← hEq _ he]; exact hR q hq

theorem enabledA_of_enabledSup {N : Nat} {envs : List PlaceId} {mode : InjMode}
    {a b : AMarking} {t : Transition} (hsat : Saturated mode N envs a) (hEq : OffEnvEq envs a b)
    (hN : ∀ s ∈ t.inputs, s.card.required ≤ N) (hN1 : 1 ≤ N)
    (hInh : ∀ q ∈ t.inhibitors, q ∉ envs) (hen : enabledSup envs mode b t = true) :
    enabledA a t = true := by
  unfold enabledSup at hen
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, envOK_true] at hen
  obtain ⟨⟨hIn, hH⟩, hR⟩ := hen
  unfold enabledA
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨fun s hs => ?_, fun q hq => ?_⟩, fun q hq => ?_⟩
  · by_cases he : s.place ∈ envs
    · have hu := (hIn s hs).1 he
      have hs' := hsat s.place he
      cases mode with
      | always => have := hN s hs; simp only at hs'; omega
      | bounded k => simp [InjMode.unsupplied] at hu; simp only at hs'; omega
    · rw [hEq _ he]; exact (hIn s hs).2 he
  · rw [hEq _ (hInh q hq)]; exact hH q hq
  · by_cases he : q ∈ envs
    · have hu := (hR q hq).1 he
      have hs' := hsat q he
      cases mode with
      | always => simp only at hs'; omega
      | bounded k => simp [InjMode.unsupplied] at hu; simp only at hs'; omega
    · rw [hEq _ he]; exact (hR q hq).2 he

/-- **Every injected-encoding marking is a supplied-graph marking off the environment.** -/
theorem reachAE_to_sup {rows : Rows} {envs : List PlaceId} {mode : InjMode} {a0 a : AMarking}
    (hInh : NoEnvInhibitor rows envs) (hcap0 : mode.capped envs a0 = true)
    (h : ReachAE rows envs mode a0 a) :
    ∃ b, ReachSup rows envs mode a0 b ∧ OffEnvEq envs a b := by
  induction h with
  | refl => exact ⟨a0, Relation.ReflTransGen.refl, fun _ _ => rfl⟩
  | @tail a1 a2 hr hs ih =>
    obtain ⟨b, hb, hEq⟩ := ih
    rcases hs with ⟨⟨tr, hmem, hen, rfl⟩, _⟩ | ⟨p, hp, _, rfl⟩
    · refine ⟨fireSup envs b tr.1 tr.2, hb.tail ⟨tr, hmem, ?_, rfl⟩, offEnv_fire hEq tr.1 tr.2⟩
      exact enabledSup_of_enabledA (reachAE_capped hcap0 hr) hEq (hInh tr hmem) hen
    · refine ⟨b, hb, fun q hq => ?_⟩
      have : q ≠ p := fun e => hq (e ▸ hp)
      rw [← hEq q hq]
      simp [injA, this]

/-- **Every supplied-graph marking is an injected-encoding marking off the environment**, the
environment first filling each place to the demand (or to `k`). Under `Bounded(k)` the
encoding's post-cap needs `NoEnvDeposit`. -/
theorem sup_to_reachAE {N : Nat} {rows : Rows} {envs : List PlaceId} {mode : InjMode}
    {a0 b : AMarking} (hInh : NoEnvInhibitor rows envs) (hN : DemandBelow N rows) (hN1 : 1 ≤ N)
    (hcap0 : mode.capped envs a0 = true) (hDep : mode = .always ∨ NoEnvDeposit rows envs)
    (h : ReachSup rows envs mode a0 b) :
    ∃ a, ReachAE rows envs mode a0 a ∧ OffEnvEq envs a b ∧ mode.capped envs a = true := by
  induction h with
  | refl => exact ⟨a0, Relation.ReflTransGen.refl, fun _ _ => rfl, hcap0⟩
  | @tail b1 b2 _ hs ih =>
    obtain ⟨a, ha, hEq, hcap⟩ := ih
    obtain ⟨tr, hmem, hen, rfl⟩ := hs
    obtain ⟨s, hR, hS, hO, hcs⟩ := exists_saturation N hcap
    have hEq' : OffEnvEq envs s b1 := fun q hq => (hO q hq).symm.trans (hEq q hq)
    have henA := enabledA_of_enabledSup hS hEq' (hN tr hmem) hN1 (hInh tr hmem) hen
    have hcap' : mode.capped envs (fireAD s tr.1 tr.2) = true := by
      cases mode with
      | always => rfl
      | bounded k =>
        have hD : NoEnvDeposit rows envs := by
          rcases hDep with h | h
          · exact absurd h (by simp)
          · exact h
        rw [capped_bounded_iff] at hcs ⊢
        intro e he
        have := fireAD_le_of_count_zero s tr.1 tr.2 (hD tr hmem e he)
        have := hcs e he
        omega
    exact ⟨fireAD s tr.1 tr.2,
      (ha.trans (injReach_reachAE hR)).tail (Or.inl ⟨⟨tr, hmem, henA, rfl⟩, hcap'⟩),
      offEnv_fire hEq' tr.1 tr.2, hcap'⟩

/-- **Route B / the state-class graph under injection decide an environment-blind safety
property as the injected encoding does**, under the four premises: no inhibitor tests an
environment place and the property is environment-blind (both checked by
`route_b_env_observation`), a capped seed and, for `Bounded(k)`, `NoEnvDeposit` (neither
checked). -/
theorem supplied_safety_exact {N : Nat} {rows : Rows} {envs : List PlaceId} {mode : InjMode}
    {a0 : AMarking} (hInh : NoEnvInhibitor rows envs) (hN : DemandBelow N rows) (hN1 : 1 ≤ N)
    (hcap0 : mode.capped envs a0 = true) (hDep : mode = .always ∨ NoEnvDeposit rows envs)
    {P : AMarking → Prop} (hP : EnvBlind envs P) :
    (∃ a, ReachAE rows envs mode a0 a ∧ P a) ↔ ∃ b, ReachSup rows envs mode a0 b ∧ P b := by
  constructor
  · rintro ⟨a, ha, hPa⟩
    obtain ⟨b, hb, hEq⟩ := reachAE_to_sup hInh hcap0 ha
    exact ⟨b, hb, (hP a b hEq).mp hPa⟩
  · rintro ⟨b, hb, hPb⟩
    obtain ⟨a, ha, hEq, _⟩ := sup_to_reachAE hInh hN hN1 hcap0 hDep hb
    exact ⟨a, ha, (hP a b hEq).mpr hPb⟩

/-! ## Quiescence: a class with no successor is a relaxed-quiescent marking -/

/-- No transition enabled in the supplied graph: `is_quiescent` of a class. -/
def DeadSup (rows : Rows) (envs : List PlaceId) (mode : InjMode) (b : AMarking) : Prop :=
  ∀ tr ∈ rows, enabledSup envs mode b tr.1 = false

/-- **Supplied enablement is the absence of every relaxed disable reason**, read on any marking
that agrees off the environment places. -/
theorem enabledSup_iff_noReason {np : Nat} {envs : List PlaceId} {mode : InjMode}
    {t : Transition} {a b : AMarking} (hok : FlatOK np t) (hInh : ∀ q ∈ t.inhibitors, q ∉ envs)
    (hEq : OffEnvEq envs a b) :
    enabledSup envs mode b t = true ↔
      permDisabled np envs mode t = false ∧ ∀ r ∈ disableReasonsE np envs t, r a = false := by
  unfold enabledSup
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, envOK_true]
  constructor
  · rintro ⟨⟨hIn, hH⟩, hR⟩
    constructor
    · cases hp : permDisabled np envs mode t with
      | false => rfl
      | true =>
        exfalso
        simp only [permDisabled, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
          decide_eq_true_eq, List.mem_range, List.contains_iff_mem] at hp
        rcases hp with ⟨i, _, ⟨hpos, he⟩, hun⟩ | ⟨q, hqr, he, hun⟩
        · obtain ⟨s, hs, rfl, hpre⟩ := pre_pos_spec hpos
          have := (hIn s hs).1 he
          rw [hpre] at hun
          rw [this] at hun; exact absurd hun (by simp)
        · have := (hR q hqr).1 he
          rw [this] at hun; exact absurd hun (by simp)
    · intro r hr
      simp only [disableReasonsE, List.mem_append, List.mem_map, List.mem_filter,
        List.mem_range] at hr
      rcases hr with ((⟨i, ⟨_, hpos⟩, rfl⟩ | ⟨q, hq, rfl⟩) | ⟨q, ⟨hq, hne⟩, rfl⟩)
      · simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hpos
        obtain ⟨s, hs, rfl, hpre⟩ := pre_pos_spec hpos.1
        have hne : s.place ∉ envs := by simpa using hpos.2
        have := (hIn s hs).2 hne
        show decide (a s.place < pre t s.place) = false
        rw [hEq _ hne, hpre]
        simp; omega
      · have := hH q hq
        show decide (0 < a q) = false
        rw [hEq _ (hInh q hq)]
        simp [this]
      · have hne' : q ∉ envs := by simpa using hne
        have := (hR q hq).2 hne'
        show decide (a q < 1) = false
        rw [hEq _ hne']
        simp; omega
  · rintro ⟨hperm, hr⟩
    have hpI : ∀ i < np, 0 < pre t i → i ∈ envs → mode.unsupplied (pre t i) = false := by
      intro i hi hpos he
      cases h : mode.unsupplied (pre t i)
      · rfl
      · exfalso
        have : permDisabled np envs mode t = true := by
          simp only [permDisabled, Bool.or_eq_true]
          left
          exact List.any_eq_true.mpr ⟨i, List.mem_range.mpr hi, by simp [hpos, he, h]⟩
        rw [hperm] at this; exact absurd this (by simp)
    have hpR : ∀ q ∈ t.reads, q ∈ envs → mode.unsupplied 1 = false := by
      intro q hq he
      cases h : mode.unsupplied 1
      · rfl
      · exfalso
        have : permDisabled np envs mode t = true := by
          simp only [permDisabled, Bool.or_eq_true]
          right
          exact List.any_eq_true.mpr ⟨q, hq, by simp [he, h]⟩
        rw [hperm] at this; exact absurd this (by simp)
    refine ⟨⟨fun s hs => ⟨fun he => ?_, fun he => ?_⟩, fun q hq => ?_⟩,
      fun q hq => ⟨hpR q hq, fun he => ?_⟩⟩
    · have hpre := pre_eq_required hok.2 hs
      by_cases h0 : s.card.required = 0
      · rw [h0]; cases mode <;> simp [InjMode.unsupplied]
      · have := hpI s.place (hok.1 s hs) (by omega) he
        rwa [hpre] at this
    · have hpre := pre_eq_required hok.2 hs
      by_cases h0 : s.card.required = 0
      · omega
      · have := hr (fun a => decide (a s.place < pre t s.place)) (by
          simp only [disableReasonsE, List.mem_append, List.mem_map, List.mem_filter,
            List.mem_range]
          exact Or.inl (Or.inl ⟨s.place, ⟨hok.1 s hs, by simp [he]; omega⟩, rfl⟩))
        rw [← hEq _ he]
        simp at this; omega
    · have := hr (fun a => decide (0 < a q)) (by
        simp only [disableReasonsE, List.mem_append, List.mem_map]
        exact Or.inl (Or.inr ⟨q, hq, rfl⟩))
      rw [← hEq _ (hInh q hq)]
      simp at this; omega
    · have := hr (fun a => decide (a q < 1)) (by
        simp only [disableReasonsE, List.mem_append, List.mem_map, List.mem_filter]
        exact Or.inr ⟨q, ⟨hq, by simp [he]⟩, rfl⟩)
      rw [← hEq _ he]
      simp at this; omega

/-- **A class with no successor is exactly a relaxed-quiescent marking** (`is_quiescent` of the
graph routes is `encode_quiescent` of the CHC route), on markings agreeing off the environment
places, when no inhibitor tests an environment place. -/
theorem deadSup_iff_quiescentE {np : Nat} {rows : Rows} {envs : List PlaceId} {mode : InjMode}
    {a b : AMarking} (hok : ∀ ft ∈ rows, FlatOK np ft.1) (hInh : NoEnvInhibitor rows envs)
    (hEq : OffEnvEq envs a b) :
    DeadSup rows envs mode b ↔ quiescentE np rows envs mode a = true := by
  rw [quiescentE_iff]
  constructor
  · intro hd
    constructor
    · intro h
      obtain ⟨ft, hft, hx⟩ := List.any_eq_true.mp h
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff] at hx
      have := (enabledSup_iff_noReason (hok ft hft) (hInh ft hft) hEq).mpr
        ⟨hx.1, by rw [hx.2]; simp⟩
      rw [hd ft hft] at this
      exact absurd this (by simp)
    · intro ft hft
      by_contra hc
      simp only [not_or, Bool.not_eq_true, List.any_eq_false] at hc
      have := (enabledSup_iff_noReason (hok ft hft) (hInh ft hft) hEq).mpr
        ⟨hc.1, fun r hr => by simpa using hc.2 r hr⟩
      rw [hd ft hft] at this
      exact absurd this (by simp)
  · rintro ⟨_, hall⟩ ft hft
    cases hen : enabledSup envs mode b ft.1 with
    | false => rfl
    | true =>
      obtain ⟨hp, hr⟩ := (enabledSup_iff_noReason (hok ft hft) (hInh ft hft) hEq).mp hen
      rcases hall ft hft with h | h
      · rw [hp] at h; exact absurd h (by simp)
      · obtain ⟨r, hmem, hra⟩ := List.any_eq_true.mp h
        rw [hr r hmem] at hra; exact absurd hra (by simp)

/-- **Route B / the state-class graph under injection decide an environment-blind quiescence
property exactly**: some graph class has no successor and satisfies `P` iff some reachable
marking of the open system satisfying `P` is stuck under every injection future. Same four
premises as `supplied_safety_exact`, two of them unchecked in Rust. -/
theorem supplied_quiescence_exact {np N : Nat} {rows : Rows} {envs : List PlaceId}
    {mode : InjMode} {a0 : AMarking} (hok : ∀ ft ∈ rows, FlatOK np ft.1)
    (hInh : NoEnvInhibitor rows envs) (hN : DemandBelow N rows) (hN1 : 1 ≤ N)
    (hcap0 : mode.capped envs a0 = true) (hDep : mode = .always ∨ NoEnvDeposit rows envs)
    {P : AMarking → Prop} (hP : EnvBlind envs P) :
    (∃ b, ReachSup rows envs mode a0 b ∧ DeadSup rows envs mode b ∧ P b) ↔
      ∃ a, ReachAE rows envs mode a0 a ∧ OpenStuck rows envs mode a ∧ P a := by
  rw [relaxed_quiescence_exact hok hN hN1 hcap0 hP.injStable]
  constructor
  · rintro ⟨b, hb, hd, hPb⟩
    obtain ⟨a, ha, hEq, _⟩ := sup_to_reachAE hInh hN hN1 hcap0 hDep hb
    exact ⟨a, ha, (deadSup_iff_quiescentE hok hInh hEq).mp hd, (hP a b hEq).mpr hPb⟩
  · rintro ⟨a, ha, hq, hPa⟩
    obtain ⟨b, hb, hEq⟩ := reachAE_to_sup hInh hcap0 ha
    exact ⟨b, hb, (deadSup_iff_quiescentE hok hInh hEq).mpr hq, (hP a b hEq).mp hPa⟩

/-! ## Against the executor -/

/-- **Every untimed executor run is a supplied-graph run off the environment places**, under
`AlwaysAvailable`, or under `Bounded(k)` given `NoEnvDeposit` and a capped `M0`; no inhibitor
may test an environment place. -/
theorem supplied_executor_sound {rows : Rows} {envs : List PlaceId} {mode : InjMode}
    (hG : ∀ tr ∈ rows, GuardFreeConsumeAll tr.1) (hInh : NoEnvInhibitor rows envs)
    (hDep : mode = .always ∨ NoEnvDeposit rows envs) {m0 m : CMarking}
    (hcap0 : mode.capped envs (alpha m0) = true) (h : ReachCE rows envs mode m0 m) :
    ∃ b, ReachSup rows envs mode (alpha m0) b ∧ OffEnvEq envs (alpha m) b :=
  reachAE_to_sup hInh hcap0 (proposition_one_inj_mode hG hDep hcap0 h).1

/-! ## The enumeration over the supplied successor -/

/-- The supplied graph's successors of a marking: one per supplied-enabled row, in row order
(`find_enabled_transitions`, then `compute_successor` per outcome). -/
def succSup (rows : Rows) (envs : List PlaceId) (mode : InjMode) (a : AMarking) :
    List AMarking :=
  rows.filterMap fun tr =>
    if enabledSup envs mode a tr.1 = true then some (fireSup envs a tr.1 tr.2) else none

theorem succSup_iff_step (rows : Rows) (envs : List PlaceId) (mode : InjMode) (a b : AMarking) :
    b ∈ succSup rows envs mode a ↔ StepSup rows envs mode a b := by
  unfold succSup StepSup
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨tr, hmem, htr⟩
    split at htr
    · rename_i hen
      exact ⟨tr, hmem, hen, (Option.some.inj htr).symm⟩
    · exact absurd htr (by simp)
  · rintro ⟨tr, hmem, hen, rfl⟩
    exact ⟨tr, hmem, by rw [if_pos hen]⟩

theorem reach_succSup_iff (rows : Rows) (envs : List PlaceId) (mode : InjMode)
    (a0 a : AMarking) :
    Enumeration.Reach (succSup rows envs mode) a0 a ↔ ReachSup rows envs mode a0 a := by
  unfold Enumeration.Reach ReachSup
  have : (fun x y => y ∈ succSup rows envs mode x) = StepSup rows envs mode := by
    funext x y
    exact propext (succSup_iff_step rows envs mode x y)
  rw [this]

/-- A class has no successor iff no row is supplied-enabled there. -/
theorem quiescentSup_iff_dead (rows : Rows) (envs : List PlaceId) (mode : InjMode)
    (a : AMarking) : succSup rows envs mode a = [] ↔ DeadSup rows envs mode a := by
  unfold succSup DeadSup
  rw [List.filterMap_eq_nil_iff]
  constructor
  · intro h tr hmem
    have := h tr hmem
    cases hen : enabledSup envs mode a tr.1 with
    | false => rfl
    | true => simp [hen] at this
  · intro h tr hmem
    simp [h tr hmem]

/-- **[VER-017]'s worklist over the supplied successor is exact.** If the enumeration closes, its
classes are exactly the `ReachSup`-reachable markings, a bad predicate read off them is decided
exactly for `ReachSup`, and a class without successor is a `DeadSup` marking. -/
theorem sup_enumeration_exact {rows : Rows} {envs : List PlaceId} {mode : InjMode}
    {maxClasses fuel : Nat} {a0 : AMarking} [DecidableEq AMarking]
    (h : (Enumeration.build (succSup rows envs mode) maxClasses fuel a0).2 = true)
    (bad : AMarking → Bool) :
    (∀ a, a ∈ (Enumeration.build (succSup rows envs mode) maxClasses fuel a0).1 ↔
      ReachSup rows envs mode a0 a) ∧
    (Enumeration.proven bad (Enumeration.build (succSup rows envs mode) maxClasses fuel a0).1 =
        true ↔ ∀ a, ReachSup rows envs mode a0 a → bad a = false) ∧
    ((∃ a ∈ (Enumeration.build (succSup rows envs mode) maxClasses fuel a0).1,
        succSup rows envs mode a = []) ↔
      ∃ a, ReachSup rows envs mode a0 a ∧ DeadSup rows envs mode a) := by
  have hmem : ∀ a, a ∈ (Enumeration.build (succSup rows envs mode) maxClasses fuel a0).1 ↔
      ReachSup rows envs mode a0 a :=
    fun a => (Enumeration.run_complete_iff_reach h a).trans (reach_succSup_iff rows envs mode a0 a)
  refine ⟨hmem, ?_, ?_⟩
  · rw [(Enumeration.decided_exact bad h).1]
    exact forall_congr' fun a => by rw [reach_succSup_iff]
  · constructor
    · rintro ⟨a, ha, hq⟩
      exact ⟨a, (hmem a).mp ha, (quiescentSup_iff_dead rows envs mode a).mp hq⟩
    · rintro ⟨a, ha, hd⟩
      exact ⟨a, (hmem a).mpr ha, (quiescentSup_iff_dead rows envs mode a).mpr hd⟩

/-- **A closed supplied graph's `Proven` holds for the executor.** Under `AlwaysAvailable`, or
`Bounded(k)` with `NoEnvDeposit` and a capped `M0`, with no inhibitor on an environment place and
a bad predicate that reads no environment place, no untimed executor run reaches a bad
marking. -/
theorem supplied_enumeration_sound {rows : Rows} {envs : List PlaceId} {mode : InjMode}
    {maxClasses fuel : Nat} [DecidableEq AMarking] {m0 m : CMarking}
    (hG : ∀ tr ∈ rows, GuardFreeConsumeAll tr.1) (hInh : NoEnvInhibitor rows envs)
    (hDep : mode = .always ∨ NoEnvDeposit rows envs)
    (hcap0 : mode.capped envs (alpha m0) = true)
    (hB : (Enumeration.build (succSup rows envs mode) maxClasses fuel (alpha m0)).2 = true)
    (bad : AMarking → Bool) (hbad : ∀ x y, OffEnvEq envs x y → bad x = bad y)
    (hp : Enumeration.proven bad
      (Enumeration.build (succSup rows envs mode) maxClasses fuel (alpha m0)).1 = true)
    (h : ReachCE rows envs mode m0 m) : bad (alpha m) = false := by
  obtain ⟨b, hb, hEq⟩ := supplied_executor_sound hG hInh hDep hcap0 h
  rw [hbad _ _ hEq]
  exact ((sup_enumeration_exact hB bad).2.1.mp hp) b hb

/-! ## Retrodictions of `89aaeec` -/

section Retro89

/-- **The property reads the frozen count.** On `env IN → consume → out` under
`AlwaysAvailable`, every supplied-graph marking has `IN = 0`, so `PlaceBound(IN, 0)` would be
`Proven`, while one injection reaches `IN = 1`. `route_b_env_observation` rule 4 now declines
(the [VER-006] AC8 example `PlaceBound(IN, 0)` is `Unknown`). -/
theorem routeB_env_count_frozen :
    (∀ b, ReachSup netEnv [envPlace] .always m0A b → b envPlace = 0) ∧
    ∃ a, ReachAE netEnv [envPlace] .always m0A a ∧ a envPlace = 1 := by
  refine ⟨fun b h => ?_, injA m0A envPlace,
    Relation.ReflTransGen.single (Or.inr ⟨envPlace, by simp, rfl, rfl⟩), by decide⟩
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    obtain ⟨tr, hmem, _, rfl⟩ := hs
    simp only [netEnv, List.mem_singleton] at hmem
    subst hmem
    have ih' : _ = 0 := ih
    simp only [envPlace] at ih' ⊢
    simp [fireSup, tConsume, outPlace, ih']

/-- `tI : one(a) ⊣ inhibitor(IN) → b`, `tU : exactly(2, IN) → c`; `a = 0`, `b = 1`, `IN = 2`,
`c = 3`, under `Bounded(1)`. -/
def tInh : Transition :=
  { name := "tI"
  , inputs := [{ place := 0, card := .one, guard := none }]
  , inhibitors := [2], reads := [], resets := [] }

def tTwo : Transition :=
  { name := "tU"
  , inputs := [{ place := 2, card := .exactly 2, guard := none }]
  , inhibitors := [], reads := [], resets := [] }

def rowsInh : Rows := [(tInh, [1]), (tTwo, [3])]

def a0Inh : AMarking := fun p => if p == 0 then 1 else 0

/-- The supplied graph never raises `IN` and never holds two tokens on `a`. -/
theorem inh_invariant {b : AMarking} (h : ReachSup rowsInh [2] (.bounded 1) a0Inh b) :
    b 2 = 0 ∧ b 0 ≤ 1 := by
  induction h with
  | refl => exact ⟨rfl, by decide⟩
  | tail _ hs ih =>
    obtain ⟨tr, hmem, hen, rfl⟩ := hs
    simp only [rowsInh, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · constructor
      · simp [fireSup, tInh, ih.1]
      · simp [fireSup, fireAD, tInh, pre, specAt, consumeAllAt, Card.consumesAll,
          Card.required]
        omega
    · exact absurd hen (by simp [enabledSup, tTwo, envOK, InjMode.unsupplied, Card.required])

/-- **An inhibitor tests the environment place.** In the injected system, one arrival on `IN`
blocks `tI` forever (`tU` needs two, above the cap), stranding the token on `a` in a marking
stuck under every injection future. The supplied graph keeps `IN` at 0, fires `tI`, and has no
class with no successor that still marks `a`: `DeadlockFree` with `b` a sink would be `Proven`.
`route_b_env_observation` rule 2 now declines. -/
theorem routeB_env_inhibitor_unsound :
    (∃ a, ReachAE rowsInh [2] (.bounded 1) a0Inh a ∧
      quiescentE 4 rowsInh [2] (.bounded 1) a = true ∧ a 0 = 1) ∧
    ∀ b, ReachSup rowsInh [2] (.bounded 1) a0Inh b → DeadSup rowsInh [2] (.bounded 1) b →
      b 0 = 0 := by
  refine ⟨⟨injA a0Inh 2, Relation.ReflTransGen.single
    (show StepAE rowsInh [2] (.bounded 1) a0Inh (injA a0Inh 2) from
      Or.inr ⟨2, by simp, by decide, rfl⟩), by decide, by decide⟩, ?_⟩
  intro b h hd
  have inv := inh_invariant h
  by_contra hb
  have h1 : b 0 = 1 := by omega
  have := hd (tInh, [1]) (by simp [rowsInh])
  simp [enabledSup, tInh, envOK, h1, inv.1, Card.required] at this

/-- The graph's read gate before `89aaeec`: a read arc on an environment place checked against
its count (`marking.count(arc) < 1`), which the graph never raises. -/
def enabledSupOld (envs : List PlaceId) (mode : InjMode) (a : AMarking) (t : Transition) : Bool :=
  t.inputs.all (fun s => envOK envs mode a s.place s.card.required)
    && t.inhibitors.all (fun q => a q == 0)
    && t.reads.all (fun q => decide (1 ≤ a q))

def StepSupOld (rows : Rows) (envs : List PlaceId) (mode : InjMode) (a a' : AMarking) : Prop :=
  ∃ tr ∈ rows, enabledSupOld envs mode a tr.1 = true ∧ a' = fireSup envs a tr.1 tr.2

/-- `t : read(env), one(ready) → out`; `env = 0`, `ready = 1`, `out = 2`. -/
def tRead : Transition :=
  { name := "t1"
  , inputs := [{ place := 1, card := .one, guard := none }]
  , inhibitors := [], reads := [0], resets := [] }

def rowsRead : Rows := [(tRead, [2])]

def a0Read : AMarking := fun p => if p == 1 then 1 else 0

/-- **Retrodiction of the read gate.** Before `89aaeec` the Rust graph never fired a transition
reading an environment place under `AlwaysAvailable` (`out` stays 0 in every class, a vacuous
`PlaceBound(out, 0)`); the injected system reaches `out = 1`, and the fixed gate
(`enabledSup`) fires it, as `reachAE_to_sup` requires. -/
theorem scg_env_read_prefix_unsound :
    (∀ b, Relation.ReflTransGen (StepSupOld rowsRead [0] .always) a0Read b → b 2 = 0) ∧
    (∃ a, ReachAE rowsRead [0] .always a0Read a ∧ a 2 = 1) ∧
    StepSup rowsRead [0] .always a0Read (fireSup [0] a0Read tRead [2]) := by
  refine ⟨fun b h => ?_, ⟨fireAD (injA a0Read 0) tRead [2], ?_, by decide⟩,
    ⟨(tRead, [2]), by simp [rowsRead], by decide, rfl⟩⟩
  · have : b = a0Read := by
      induction h with
      | refl => rfl
      | tail _ hs ih =>
        subst ih
        obtain ⟨tr, hmem, hen, _⟩ := hs
        simp only [rowsRead, List.mem_singleton] at hmem
        subst hmem
        exact absurd hen (by decide)
    subst this; decide
  · exact (Relation.ReflTransGen.single
      (show StepAE rowsRead [0] .always a0Read (injA a0Read 0) from
        Or.inr ⟨0, by simp, rfl, rfl⟩)).tail
      (Or.inl ⟨⟨(tRead, [2]), by simp [rowsRead], by decide, rfl⟩, rfl⟩)

end Retro89

/-! ## The `Bounded(k)` premises on the graph routes (checked by `verify_net` since, `Premise.lean`) -/

section BoundedGate

/-- On a transition whose inputs carry no guard, concrete enablement is abstract enablement of
the α-image. -/
theorem enabledC_eq_enabledA_alpha {m : CMarking} {t : Transition}
    (hg : ∀ s ∈ t.inputs, s.guard = none) : enabledC m t = enabledA (alpha m) t := by
  unfold enabledC enabledA
  have e1 : t.inputs.all (fun s => decide (s.card.required ≤ matchCount m s)) =
      t.inputs.all (fun s => decide (s.card.required ≤ alpha m s.place)) :=
    all_congr_mem fun s hs => by simp [matchCount, hg s hs, alpha]
  rw [e1]
  rfl

/-- `t0 : one(a) → E` and `t1 : exactly(2, E) → out`; `a = 0`, `E = 1`, `out = 2`. -/
def tToEnv : Transition :=
  { name := "t0"
  , inputs := [{ place := 0, card := .one, guard := none }]
  , inhibitors := [], reads := [], resets := [] }

def tTwoEnv : Transition :=
  { name := "t1"
  , inputs := [{ place := 1, card := .exactly 2, guard := none }]
  , inhibitors := [], reads := [], resets := [] }

def rowsGate : Rows := [(tToEnv, [1]), (tTwoEnv, [2])]

/-- `t1` alone: no row deposits into `E`. -/
def rowsGateNoDep : Rows := [(tTwoEnv, [2])]

/-- `PlaceBound(out, 0)` reads no environment place. -/
theorem gate_property_envBlind : EnvBlind [1] (fun b => b 2 = 0) := by
  intro a b h
  show a 2 = 0 ↔ b 2 = 0
  rw [h 2 (by decide)]

/-- The supplied graph never fires `t1` under `Bounded(1)` (`required = 2 > 1`), so `out` stays
where it started. Holds for any subset of `rowsGate`. -/
theorem gate_sup_out_zero {rows : Rows} (hrows : ∀ tr ∈ rows, tr ∈ rowsGate) {b0 b : AMarking}
    (h0 : b0 2 = 0) (h : ReachSup rows [1] (.bounded 1) b0 b) : b 2 = 0 := by
  induction h with
  | refl => exact h0
  | tail _ hs ih =>
    obtain ⟨tr, hmem, hen, rfl⟩ := hs
    have hmem := hrows tr hmem
    simp only [rowsGate, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · simp [fireSup, fireAD, tToEnv, consumeAllAt, pre, specAt, ih]
    · exact absurd hen (by simp [enabledSup, tTwoEnv, envOK, InjMode.unsupplied, Card.required])

def m0Gate : CMarking := fun p => if p == 0 then [0, 0] else []
def m1Gate : CMarking := fun p => if p == 0 then [0] else if p == 1 then [0] else []
def m2Gate : CMarking := fun p => if p == 1 then [0, 0] else []
def m3Gate : CMarking := fun p => if p == 2 then [0] else []

theorem gate_step01 : StepCR rowsGate m0Gate m1Gate := by
  refine ⟨(tToEnv, [1]), by simp [rowsGate], by decide, ?_⟩
  funext p
  simp only [alpha, alphaFireC, m0Gate, m1Gate, consumedAt, specAt, tToEnv]
  rcases p with _ | _ | _ | p <;> simp [consumeCount, Card.consumesAll, Card.required]

theorem gate_step12 : StepCR rowsGate m1Gate m2Gate := by
  refine ⟨(tToEnv, [1]), by simp [rowsGate], by decide, ?_⟩
  funext p
  simp only [alpha, alphaFireC, m1Gate, m2Gate, consumedAt, specAt, tToEnv]
  rcases p with _ | _ | _ | p <;> simp [consumeCount, Card.consumesAll, Card.required]

theorem gate_step23 : StepCR rowsGate m2Gate m3Gate := by
  refine ⟨(tTwoEnv, [2]), by simp [rowsGate], by decide, ?_⟩
  funext p
  simp only [alpha, alphaFireC, m2Gate, m3Gate, consumedAt, specAt, tTwoEnv]
  rcases p with _ | _ | _ | p <;> simp [consumeCount, Card.consumesAll, Card.required]

/-- **Live: a deposit into the environment place breaks the graph routes under `Bounded(k)`.**
The executor fires `t0` twice (two tokens on `E`, no injection) and then `t1`, reaching
`out = 1`; the supplied graph (state-class graph, Route B's base layer) never enables `t1`
because `check_place_enabled` answers `2 ≤ 1` whatever `E` holds, so every class has `out = 0`
and `PlaceBound(out, 0)` is `Proven`. `route_b_env_observation` passes the net: the property
does not read `E` and no inhibitor tests it. Only `NoEnvDeposit` fails: the seed is capped
(`E = 0`). -/
theorem supplied_bounded_deposit_wrong_proven :
    (∃ m, ReachCE rowsGate [1] (.bounded 1) m0Gate m ∧ (m 2).length = 1) ∧
    NoEnvInhibitor rowsGate [1] ∧ EnvBlind [1] (fun b => b 2 = 0) ∧
    EnvCappedC 1 [1] m0Gate ∧ ¬ NoEnvDeposit rowsGate [1] ∧
    ∀ b, ReachSup rowsGate [1] (.bounded 1) (alpha m0Gate) b → b 2 = 0 := by
  refine ⟨⟨m3Gate, ?_, by decide⟩, ?_, gate_property_envBlind, ?_, ?_,
    fun b h => gate_sup_out_zero (fun _ h => h) (by decide) h⟩
  · exact ((Relation.ReflTransGen.single
      (show StepCE rowsGate [1] (.bounded 1) m0Gate m1Gate from Or.inl gate_step01)).tail
      (show StepCE rowsGate [1] (.bounded 1) m1Gate m2Gate from Or.inl gate_step12)).tail
      (show StepCE rowsGate [1] (.bounded 1) m2Gate m3Gate from Or.inl gate_step23)
  · intro tr htr q hq
    simp only [rowsGate, List.mem_cons, List.not_mem_nil, or_false] at htr
    rcases htr with rfl | rfl <;> simp [tToEnv, tTwoEnv] at hq
  · intro e he
    simp only [List.mem_singleton] at he
    subst he
    decide
  · intro h
    exact absurd (h (tToEnv, [1]) (by simp [rowsGate]) 1 (by simp)) (by decide)

/-- `M0 = {E: 2}`, above `Bounded(1)`'s cap. -/
def m0GateOver : CMarking := fun p => if p == 1 then [0, 0] else []

theorem gate_stepOver : StepCR rowsGateNoDep m0GateOver m3Gate := by
  refine ⟨(tTwoEnv, [2]), by simp [rowsGateNoDep], by decide, ?_⟩
  funext p
  simp only [alpha, alphaFireC, m0GateOver, m3Gate, consumedAt, specAt, tTwoEnv]
  rcases p with _ | _ | _ | p <;> simp [consumeCount, Card.consumesAll, Card.required]

/-- **Live: an initial marking above `k` breaks the graph routes under `Bounded(k)`.** On `t1`
alone (`rowsGateNoDep`, no row deposits into `E`) from `E = 2`, the executor fires `t1` at once
and reaches `out = 1`; the supplied graph never enables it, so `PlaceBound(out, 0)` is `Proven`.
Only the capped seed fails: `NoEnvDeposit`, `NoEnvInhibitor` and the property's environment
blindness all hold. -/
theorem supplied_bounded_initial_wrong_proven :
    (∃ m, ReachCE rowsGateNoDep [1] (.bounded 1) m0GateOver m ∧ (m 2).length = 1) ∧
    NoEnvInhibitor rowsGateNoDep [1] ∧ EnvBlind [1] (fun b => b 2 = 0) ∧
    NoEnvDeposit rowsGateNoDep [1] ∧ ¬ EnvCappedC 1 [1] m0GateOver ∧
    ∀ b, ReachSup rowsGateNoDep [1] (.bounded 1) (alpha m0GateOver) b → b 2 = 0 := by
  have hsub : ∀ tr ∈ rowsGateNoDep, tr ∈ rowsGate := by
    intro tr htr
    simp only [rowsGateNoDep, List.mem_singleton] at htr
    subst htr
    simp [rowsGate]
  refine ⟨⟨m3Gate, Relation.ReflTransGen.single
      (show StepCE rowsGateNoDep [1] (.bounded 1) m0GateOver m3Gate from Or.inl gate_stepOver),
    by decide⟩, ?_, gate_property_envBlind, ?_, ?_,
    fun b h => gate_sup_out_zero hsub (by decide) h⟩
  · intro tr htr q hq
    simp only [rowsGateNoDep, List.mem_singleton] at htr
    subst htr
    simp [tTwoEnv] at hq
  · intro tr htr e he
    simp only [rowsGateNoDep, List.mem_singleton] at htr he
    subst htr he
    decide
  · intro h
    exact absurd (h 1 (by simp)) (by decide)

/-- `tQ1 : exactly(2, E) → out` and the self-loop `tQ2 : one(out) → out`; `E = 0`, `out = 1`. -/
def tQ1 : Transition :=
  { name := "tQ1"
  , inputs := [{ place := 0, card := .exactly 2, guard := none }]
  , inhibitors := [], reads := [], resets := [] }

def tQ2 : Transition :=
  { name := "tQ2"
  , inputs := [{ place := 1, card := .one, guard := none }]
  , inhibitors := [], reads := [], resets := [] }

def rowsQ : Rows := [(tQ1, [1]), (tQ2, [1])]

/-- `M0 = {E: 2}`. -/
def m0Q : CMarking := fun p => if p == 0 then [0, 0] else []

theorem rowsQ_guardFree : ∀ tr ∈ rowsQ, GuardFreeConsumeAll tr.1 := by
  intro tr htr s hs hca
  simp only [rowsQ, List.mem_cons, List.not_mem_nil, or_false] at htr
  rcases htr with rfl | rfl <;>
  · simp only [tQ1, tQ2, List.mem_singleton] at hs
    subst hs
    exact absurd hca (by decide)

/-- The executor under `Bounded(1)` from `E = 2` always holds two on `E` or one on `out`. -/
theorem q_exec_invariant {m : CMarking} (h : ReachCE rowsQ [0] (.bounded 1) m0Q m) :
    2 ≤ alpha m 0 ∨ 1 ≤ alpha m 1 := by
  induction h with
  | refl => left; decide
  | tail _ hs ih =>
    rename_i m1 m2 _
    rcases hs with hs | ⟨p, hp, _, c, rfl⟩
    · obtain ⟨tr, hmem, hen, heq⟩ := stepCR_simulated rowsQ_guardFree hs
      simp only [rowsQ, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rw [heq]
      rcases hmem with rfl | rfl
      · right
        simp [fireAD, tQ1, consumeAllAt, pre, specAt]
      · right
        simp [fireAD, tQ2, consumeAllAt, pre, specAt, Card.consumesAll, Card.required]
    · simp only [List.mem_singleton] at hp
      subst hp
      rw [alpha_injC]
      simp only [injA]
      simp; omega

/-- **Live: an initial marking above `k` makes `encode_quiescent` report a deadlock the executor
never has.** Under `Bounded(1)` from `E = 2`, `permanently_disabled` marks `tQ1` disabled for
good (`2 > 1`), so the relaxed conjunct holds at `α(M0)` (reachable, `DeadlockFree` comes back
`Violated`), and the supplied graph also has no successor there. The executor fires `tQ1` and
then loops on `tQ2` forever: no marking it reaches is dead. Only the capped seed fails: no
row deposits into `E` and no inhibitor tests it. -/
theorem quiescence_bounded_initial_spurious :
    NoEnvInhibitor rowsQ [0] ∧ NoEnvDeposit rowsQ [0] ∧ ¬ EnvCappedC 1 [0] m0Q ∧
    quiescentE 2 rowsQ [0] (.bounded 1) (alpha m0Q) = true ∧
    DeadSup rowsQ [0] (.bounded 1) (alpha m0Q) ∧
    ∀ m, ReachCE rowsQ [0] (.bounded 1) m0Q m → ∃ tr ∈ rowsQ, enabledC m tr.1 = true := by
  refine ⟨?_, ?_, fun h => absurd (h 0 (by simp)) (by decide), by decide, ?_, fun m h => ?_⟩
  · intro tr htr q hq
    simp only [rowsQ, List.mem_cons, List.not_mem_nil, or_false] at htr
    rcases htr with rfl | rfl <;> simp [tQ1, tQ2] at hq
  · intro tr htr e he
    simp only [List.mem_singleton] at he
    subst he
    simp only [rowsQ, List.mem_cons, List.not_mem_nil, or_false] at htr
    rcases htr with rfl | rfl <;> decide
  · intro tr htr
    simp only [rowsQ, List.mem_cons, List.not_mem_nil, or_false] at htr
    rcases htr with rfl | rfl <;> decide
  · rcases q_exec_invariant h with h0 | h1
    · refine ⟨(tQ1, [1]), by simp [rowsQ], ?_⟩
      rw [enabledC_eq_enabledA_alpha (by simp [tQ1])]
      simp [enabledA, tQ1, Card.required]; omega
    · refine ⟨(tQ2, [1]), by simp [rowsQ], ?_⟩
      rw [enabledC_eq_enabledA_alpha (by simp [tQ2])]
      simp [enabledA, tQ2, Card.required]; omega

end BoundedGate

end Libpetri.Novel.EnvSemantics
