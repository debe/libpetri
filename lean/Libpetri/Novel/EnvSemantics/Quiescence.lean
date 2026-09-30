import Libpetri.Novel.EnvSemantics.Step
import Libpetri.Novel.Seam.Bad

/-!
# Relaxed quiescence under injection ([VER-006] AC6, `98b9297`)

`encode_quiescent` (`smt_encoder.rs`) writes the quiescence conjunct of every quiescence
property (`DeadlockFree`, `TerminatesAtSink`, `QuiescentCount`, `JoinedOrDeadLettered`). With
injectable environment places it is **relaxed**: an input or read arc on an environment place is
not a reason a transition is disabled, because injection can satisfy it — unless a `Bounded(k)`
cap is below the demand (`pre > k` for an input, `k < 1` for a read), in which case the
transition is `permanently_disabled` and contributes `true`. A transition with no reason left is
enabled in every marking, the whole conjunct is `None`, and every quiescence property is
unviolatable (the AC6 vacuity note, `quiescence_unreachable`). `Seam/Bad.lean` models the
env-free case (`encodeQuiescent`); `encodeQuiescentE_nil` shows it is the `envs = []` instance of
the model here.

What does the relaxed conjunct mean? It is **not** "no transition is enabled at this marking"
(an inhibitor on an environment place reads the current count, and a marking waiting for an
arrival is not quiescent). Its meaning is **stuck under every injection future** (`OpenStuck`):

* `quiescentE_openStuck` (completeness): a marking satisfying it, capped (`Bounded(k)`), is dead,
  and so is every marking injection can take it to. So a relaxed violation is a deadlock **of the
  encoded open system** (`ReachAE`) that the environment cannot lift (`relaxed_violation_real`).
  `ReachAE` over-approximates the executor (`proposition_one_inj*`), so the marking need not be
  one the executor reaches; "real" means real in the encoding.
* `relaxed_quiescence_sound`: a reachable marking that is stuck under every injection future
  has a **saturation** (every environment place filled to its demand, or to `k`), reachable by
  injections alone, agreeing off the environment places, and satisfying the relaxed conjunct.
  So quiescence properties whose other conjuncts survive injection (`InjStable`, e.g. anything
  that reads no environment place) lose no violation of `ReachAE`.
* `relaxed_quiescence_exact`: the two combined as an equivalence over reachable markings.
* `relaxed_quiescence_sound_executor`: composed with Proposition 1 with injection, an **untimed**
  executor run (`ReachCE`) that reaches a marking stuck under every injection future is caught,
  under `AlwaysAvailable`, or under `Bounded(k)` given `NoEnvDeposit` and a capped `M0` (the two
  premises no route checks and `verify_net` checks first, `Premise.lean`,
  `bounded_checked_quiescence_sound`; `Supplied.lean` shows what goes wrong without them).
* `quiescence_vacuity_sound`: when the conjunct is `None`, no marking is stuck under injection:
  the AC6 note is true.

**Scope: untimed, no reapable row.** Every result here is about the untimed open system.
Quiescence is "no transition enabled at this marking under any injection future". The shipped
`encode_quiescent` (`smt_encoder.rs`) skips every flat row marked `ft.reapable` (a `Deadline` or
`Window` transition, unless `assume_no_reaping`), so a reapable row adds no clause; the timed
executor comes to rest when [TIME-013] reaping has cleared such a transition's enabled bit, and
the skip is what lets the check see that rest. `encodeQuiescentE` below has no skip: it is
`encode_quiescent` on rows none of which is reapable, which is every row of an untimed net and
of a net under `assume_no_reaping`. The reap-aware reading, and its soundness for the executor's
rest markings, is `ReapAware.lean` (`quiescentBad_filter_iff`, `rest_sound`, `reap_aware_ac3`);
`ReapingVsUntimed.reaping_refutes_ver004_ac3` is the env-free witness of why it is needed.
Combining the reap-aware skip with injection is not proved here.

Retrodiction (`retrodict_98b9297_relaxation`, by `decide`): before `98b9297` relaxed the check,
the env-free conjunct held at the empty marking of `env → consume → out`, reporting a deadlock on
a net merely waiting for input; the relaxed conjunct is `None` there.

Premises: `FlatOK` (inputs below the place count, one input arc per place, as `Seam/Bad.lean`),
a demand bound `N` on every input arc (`DemandBelow`), and a capped seed under `Bounded(k)`.
-/

namespace Libpetri.Novel.EnvSemantics

open Libpetri Libpetri.Novel.ForwardDeposit Libpetri.Novel.Seam

/-- Whether the mode can never supply `need` tokens in one firing: `Bounded(k)` with
`k < need`. -/
def InjMode.unsupplied : InjMode → Nat → Bool
  | .always, _ => false
  | .bounded k, need => decide (k < need)

/-- `permanently_disabled` of `encode_quiescent`: some input on an injectable place demands more
than the cap (`matches!(bound, Some(k) if pre > k)`), or some read on one has `k < 1`. -/
def permDisabled (np : Nat) (envs : List PlaceId) (mode : InjMode) (t : Transition) : Bool :=
  ((List.range np).any fun i => decide (0 < pre t i) && envs.contains i && mode.unsupplied (pre t i))
    || t.reads.any fun q => envs.contains q && mode.unsupplied 1

/-- The disable reasons `encode_quiescent` collects with injection: `(< m_i pre_i)` per
non-environment input place, `(> m_q 0)` per inhibitor (environment or not), `(< m_q 1)` per
non-environment read place. -/
def disableReasonsE (np : Nat) (envs : List PlaceId) (t : Transition) : List (AMarking → Bool) :=
  ((List.range np).filter (fun i => decide (0 < pre t i) && !envs.contains i)).map
      (fun i a => decide (a i < pre t i))
    ++ t.inhibitors.map (fun q a => decide (0 < a q))
    ++ (t.reads.filter (fun q => !envs.contains q)).map (fun q a => decide (a q < 1))

/-- **`encode_quiescent` with injection.** `None` when some transition is neither permanently
disabled nor has any reason left (enabled, via injection, in every marking); else per transition
`true` if permanently disabled, the disjunction of its reasons otherwise. -/
def encodeQuiescentE (np : Nat) (flat : Rows) (envs : List PlaceId) (mode : InjMode) :
    Option (AMarking → Bool) :=
  if flat.any (fun ft => !permDisabled np envs mode ft.1 && (disableReasonsE np envs ft.1).isEmpty)
  then none
  else some fun a =>
    flat.all fun ft => permDisabled np envs mode ft.1 || (disableReasonsE np envs ft.1).any (· a)

/-- The relaxed quiescence conjunct as a predicate, `false` for `None`. -/
def quiescentE (np : Nat) (flat : Rows) (envs : List PlaceId) (mode : InjMode)
    (a : AMarking) : Bool :=
  match encodeQuiescentE np flat envs mode with
  | none => false
  | some q => q a

/-- **The env-free conjunct is the `envs = []` instance.** -/
theorem encodeQuiescentE_nil (np : Nat) (flat : Rows) (mode : InjMode) :
    encodeQuiescentE np flat [] mode = encodeQuiescent np flat := by
  have hp : ∀ t, permDisabled np [] mode t = false := by
    intro t; simp [permDisabled]
  have hr : ∀ t, disableReasonsE np [] t = disableReasons np t := by
    intro t; simp [disableReasonsE, disableReasons]
  have e1 : flat.any (fun ft => !permDisabled np [] mode ft.1 &&
      (disableReasonsE np [] ft.1).isEmpty) = flat.any (fun ft => (disableReasons np ft.1).isEmpty) := by
    congr 1; funext ft; simp [hp, hr]
  unfold encodeQuiescentE encodeQuiescent
  rw [e1]
  split <;> simp [hp, hr]

/-- The conjunct, unfolded: not `None`, and every transition permanently disabled or with a
reason that holds. -/
theorem quiescentE_iff {np : Nat} {flat : Rows} {envs : List PlaceId} {mode : InjMode}
    {a : AMarking} :
    quiescentE np flat envs mode a = true ↔
      ¬ (flat.any (fun ft => !permDisabled np envs mode ft.1 &&
          (disableReasonsE np envs ft.1).isEmpty) = true) ∧
      ∀ ft ∈ flat, permDisabled np envs mode ft.1 = true ∨
        (disableReasonsE np envs ft.1).any (· a) = true := by
  unfold quiescentE encodeQuiescentE
  by_cases hc : flat.any (fun ft => !permDisabled np envs mode ft.1 &&
      (disableReasonsE np envs ft.1).isEmpty) = true
  · rw [if_pos hc]; simp [hc]
  · rw [if_neg hc]; simp [hc, List.all_eq_true]

/-! ## What the conjunct means -/

/-- No row is enabled. -/
def Dead (rows : Rows) (a : AMarking) : Prop := ∀ tr ∈ rows, enabledA a tr.1 = false

/-- One admitted injection. -/
def InjStep (envs : List PlaceId) (mode : InjMode) (a a' : AMarking) : Prop :=
  ∃ p ∈ envs, mode.admits (a p) = true ∧ a' = injA a p

/-- What the environment alone can do from a marking. -/
def InjReach (envs : List PlaceId) (mode : InjMode) : AMarking → AMarking → Prop :=
  Relation.ReflTransGen (InjStep envs mode)

/-- **Stuck under every injection future**: dead now and after any admitted injections. -/
def OpenStuck (rows : Rows) (envs : List PlaceId) (mode : InjMode) (a : AMarking) : Prop :=
  ∀ b, InjReach envs mode a b → Dead rows b

/-- Every environment place filled to at least `N` (`AlwaysAvailable`) or `k` (`Bounded(k)`). -/
def Saturated (mode : InjMode) (N : Nat) (envs : List PlaceId) (b : AMarking) : Prop :=
  ∀ e ∈ envs, match mode with
    | .always => N ≤ b e
    | .bounded k => k ≤ b e

/-- Every input arc demands at most `N` tokens. -/
def DemandBelow (N : Nat) (rows : Rows) : Prop := ∀ tr ∈ rows, ∀ s ∈ tr.1.inputs, s.card.required ≤ N

/-- Agreement off the environment places. -/
def OffEnvEq (envs : List PlaceId) (a b : AMarking) : Prop := ∀ q, q ∉ envs → a q = b q

theorem injReach_reachAE {rows : Rows} {envs : List PlaceId} {mode : InjMode} {a b : AMarking}
    (h : InjReach envs mode a b) : Relation.ReflTransGen (StepAE rows envs mode) a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail (Or.inr hs)

theorem injReach_capped {envs : List PlaceId} {mode : InjMode} {a b : AMarking}
    (h0 : mode.capped envs a = true) (h : InjReach envs mode a b) : mode.capped envs b = true := by
  induction h with
  | refl => exact h0
  | tail _ hs ih =>
    obtain ⟨p, _, hadm, rfl⟩ := hs
    exact capped_injA ih hadm

theorem injReach_offEnv {envs : List PlaceId} {mode : InjMode} {a b : AMarking}
    (h : InjReach envs mode a b) : OffEnvEq envs a b := by
  induction h with
  | refl => intro q _; rfl
  | tail _ hs ih =>
    obtain ⟨p, hp, _, rfl⟩ := hs
    intro q hq
    have hqp : q ≠ p := fun h => hq (h ▸ hp)
    rw [ih q hq]
    simp [injA, hqp]

/-! ## Saturation is reachable by injections -/

/-- `j` injections into `e`. -/
def injN (a : AMarking) (e : PlaceId) (j : Nat) : AMarking :=
  fun q => if q == e then a q + j else a q

theorem injN_zero (a : AMarking) (e : PlaceId) : injN a e 0 = a := by
  funext q; simp [injN]

theorem injN_succ (a : AMarking) (e : PlaceId) (j : Nat) :
    injN a e (j + 1) = injA (injN a e j) e := by
  funext q
  by_cases h : q = e
  · subst h; simp [injN, injA]; omega
  · simp [injN, injA, h]

theorem injN_reach {envs : List PlaceId} {mode : InjMode} {a : AMarking} {e : PlaceId}
    (he : e ∈ envs) : ∀ j, (∀ i < j, mode.admits (a e + i) = true) →
      InjReach envs mode a (injN a e j)
  | 0, _ => by rw [injN_zero]; exact Relation.ReflTransGen.refl
  | j + 1, h => by
    rw [injN_succ]
    refine (injN_reach he j fun i hi => h i (by omega)).tail ⟨e, he, ?_, rfl⟩
    have : injN a e j e = a e + j := by simp [injN]
    rw [this]
    exact h j (by omega)

/-- **A saturation exists, reachable by injections alone**, agreeing off the environment places
and still capped. -/
theorem exists_saturation {envs : List PlaceId} {mode : InjMode} (N : Nat) {a : AMarking}
    (hc : mode.capped envs a = true) :
    ∃ b, InjReach envs mode a b ∧ Saturated mode N envs b ∧ OffEnvEq envs a b ∧
      mode.capped envs b = true := by
  suffices H : ∀ l : List PlaceId, (∀ e ∈ l, e ∈ envs) →
      ∃ b, InjReach envs mode a b ∧ Saturated mode N l b ∧ (∀ q, q ∉ l → a q = b q) ∧
        mode.capped envs b = true by
    obtain ⟨b, h1, h2, _, h4⟩ := H envs (fun _ h => h)
    exact ⟨b, h1, h2, injReach_offEnv h1, h4⟩
  intro l
  induction l with
  | nil => exact fun _ => ⟨a, Relation.ReflTransGen.refl, fun _ h => absurd h (by simp),
      fun _ _ => rfl, hc⟩
  | cons e l ih =>
    intro hl
    obtain ⟨b, hR, hS, hO, hC⟩ := ih (fun x hx => hl x (List.mem_cons_of_mem e hx))
    have he : e ∈ envs := hl e List.mem_cons_self
    let j := match mode with
      | .always => N
      | .bounded k => k - b e
    have hadm : ∀ i < j, mode.admits (b e + i) = true := by
      intro i hi
      cases mode with
      | always => rfl
      | bounded k =>
        have := (capped_bounded_iff.mp hC) e he
        simp only [InjMode.admits, decide_eq_true_eq]
        simp only [j] at hi
        omega
    have hR' := injN_reach (a := b) he j hadm
    refine ⟨injN b e j, hR.trans hR', ?_, ?_, injReach_capped hC hR'⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · cases mode with
        | always => simp [injN, j]
        | bounded k =>
          have := (capped_bounded_iff.mp hC) x he
          simp [injN, j]; omega
      · have := hS x hx
        cases mode with
        | always =>
          simp only at this ⊢
          unfold injN; split <;> omega
        | bounded k =>
          simp only at this ⊢
          unfold injN; split <;> omega
    · intro q hq
      have hqe : q ≠ e := fun h => hq (h ▸ List.mem_cons_self)
      rw [hO q (fun h => hq (List.mem_cons_of_mem e h))]
      simp [injN, hqe]

/-! ## Soundness: a stuck saturation satisfies the conjunct -/

theorem pre_eq_required {t : Transition} (hD : InputsDistinctPlaces t) {s : InSpec}
    (hs : s ∈ t.inputs) : pre t s.place = s.card.required := by
  unfold pre; rw [hD s hs]

/-- **No reason and not permanently disabled means enabled at a saturation.** -/
theorem enabled_of_no_reason {np N : Nat} {envs : List PlaceId} {mode : InjMode} {t : Transition}
    {b : AMarking} (hok : FlatOK np t) (hsat : Saturated mode N envs b)
    (hN : ∀ s ∈ t.inputs, s.card.required ≤ N) (hN1 : 1 ≤ N)
    (hperm : permDisabled np envs mode t = false)
    (hr : ∀ r ∈ disableReasonsE np envs t, r b = false) : enabledA b t = true := by
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
  have hrI : ∀ i < np, 0 < pre t i → i ∉ envs → pre t i ≤ b i := by
    intro i hi hpos hne
    have := hr (fun a => decide (a i < pre t i)) (by
      simp only [disableReasonsE, List.mem_append, List.mem_map, List.mem_filter, List.mem_range]
      exact Or.inl (Or.inl ⟨i, ⟨hi, by simp [hpos, hne]⟩, rfl⟩))
    simp at this; omega
  have hrH : ∀ q ∈ t.inhibitors, b q = 0 := by
    intro q hq
    have := hr (fun a => decide (0 < a q)) (by
      simp only [disableReasonsE, List.mem_append, List.mem_map]
      exact Or.inl (Or.inr ⟨q, hq, rfl⟩))
    simp at this; omega
  have hrD : ∀ q ∈ t.reads, q ∉ envs → 1 ≤ b q := by
    intro q hq hne
    have := hr (fun a => decide (a q < 1)) (by
      simp only [disableReasonsE, List.mem_append, List.mem_map, List.mem_filter]
      exact Or.inr ⟨q, ⟨hq, by simp [hne]⟩, rfl⟩)
    simp at this; omega
  unfold enabledA
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨fun s hs => ?_, hrH⟩, fun q hq => ?_⟩
  · have hpre := pre_eq_required hok.2 hs
    have hlt := hok.1 s hs
    by_cases h0 : s.card.required = 0
    · omega
    by_cases he : s.place ∈ envs
    · have hns := hpI s.place hlt (by omega) he
      have hsat' := hsat s.place he
      rw [hpre] at hns
      cases mode with
      | always => have := hN s hs; simp only at hsat'; omega
      | bounded k =>
        simp only [InjMode.unsupplied, decide_eq_false_iff_not] at hns
        simp only at hsat'
        omega
    · have := hrI s.place hlt (by omega) he
      omega
  · by_cases he : q ∈ envs
    · have hns := hpR q hq he
      have hsat' := hsat q he
      cases mode with
      | always => simp only at hsat'; omega
      | bounded k =>
        simp only [InjMode.unsupplied, decide_eq_false_iff_not] at hns
        simp only at hsat'
        omega
    · exact hrD q hq he

/-- **Relaxed quiescence holds at a dead saturation.** -/
theorem quiescentE_of_dead {np N : Nat} {flat : Rows} {envs : List PlaceId} {mode : InjMode}
    {b : AMarking} (hok : ∀ ft ∈ flat, FlatOK np ft.1) (hN : DemandBelow N flat) (hN1 : 1 ≤ N)
    (hsat : Saturated mode N envs b) (hdead : Dead flat b) :
    quiescentE np flat envs mode b = true := by
  rw [quiescentE_iff]
  constructor
  · intro h
    obtain ⟨ft, hft, hx⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff] at hx
    have := enabled_of_no_reason (hok ft hft) hsat (hN ft hft) hN1 hx.1
      (by rw [hx.2]; simp)
    rw [hdead ft hft] at this
    exact absurd this (by simp)
  · intro ft hft
    by_contra hc
    simp only [not_or, Bool.not_eq_true, List.any_eq_false] at hc
    have := enabled_of_no_reason (hok ft hft) hsat (hN ft hft) hN1 hc.1
      (fun r hr => by simpa using hc.2 r hr)
    rw [hdead ft hft] at this
    exact absurd this (by simp)

/-! ## Completeness: the conjunct means stuck under injection -/

/-- **A relaxed-quiescent capped marking is dead.** -/
theorem dead_of_quiescentE {np : Nat} {flat : Rows} {envs : List PlaceId} {mode : InjMode}
    {b : AMarking} (hcap : mode.capped envs b = true)
    (hq : quiescentE np flat envs mode b = true) : Dead flat b := by
  have hQ := (quiescentE_iff.mp hq).2
  intro ft hft
  cases hen : enabledA b ft.1 with
  | false => rfl
  | true =>
    exfalso
    unfold enabledA at hen
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at hen
    obtain ⟨⟨hIn, hInh⟩, hRd⟩ := hen
    rcases hQ ft hft with hp | hr
    · simp only [permDisabled, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
        decide_eq_true_eq, List.mem_range, List.contains_iff_mem] at hp
      rcases hp with ⟨i, _, ⟨hpos, he⟩, hun⟩ | ⟨q, hqr, he, hun⟩
      · obtain ⟨s, hs, rfl, hpre⟩ := pre_pos_spec hpos
        cases mode with
        | always => simp [InjMode.unsupplied] at hun
        | bounded k =>
          have := (capped_bounded_iff.mp hcap) s.place he
          have := hIn s hs
          simp only [InjMode.unsupplied, decide_eq_true_eq] at hun
          omega
      · cases mode with
        | always => simp [InjMode.unsupplied] at hun
        | bounded k =>
          have := (capped_bounded_iff.mp hcap) q he
          have := hRd q hqr
          simp only [InjMode.unsupplied, decide_eq_true_eq] at hun
          omega
    · obtain ⟨r, hr, hra⟩ := List.any_eq_true.mp hr
      simp only [disableReasonsE, List.mem_append, List.mem_map, List.mem_filter,
        List.mem_range] at hr
      rcases hr with ((⟨i, ⟨_, hpos⟩, rfl⟩ | ⟨q, hq, rfl⟩) | ⟨q, ⟨hq, _⟩, rfl⟩)
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hpos
        obtain ⟨s, hs, rfl, hpre⟩ := pre_pos_spec hpos.1
        have := hIn s hs
        simp only [decide_eq_true_eq] at hra
        omega
      · have := hInh q hq
        simp only [decide_eq_true_eq] at hra
        omega
      · have := hRd q hq
        simp only [decide_eq_true_eq] at hra
        omega

/-- The conjunct survives an injection: permanent disablement does not read the marking, a
non-environment reason is untouched, and an inhibitor reason only grows. -/
theorem quiescentE_injA {np : Nat} {flat : Rows} {envs : List PlaceId} {mode : InjMode}
    {b : AMarking} {p : PlaceId} (hp : p ∈ envs) (hq : quiescentE np flat envs mode b = true) :
    quiescentE np flat envs mode (injA b p) = true := by
  obtain ⟨hnone, hq⟩ := quiescentE_iff.mp hq
  refine quiescentE_iff.mpr ⟨hnone, ?_⟩
  intro ft hft
  rcases hq ft hft with h | h
  · exact Or.inl h
  · right
    obtain ⟨r, hr, hra⟩ := List.any_eq_true.mp h
    refine List.any_eq_true.mpr ⟨r, hr, ?_⟩
    simp only [disableReasonsE, List.mem_append, List.mem_map, List.mem_filter,
      List.mem_range] at hr
    rcases hr with ((⟨i, ⟨_, hpos⟩, rfl⟩ | ⟨q, _, rfl⟩) | ⟨q, ⟨_, hne⟩, rfl⟩)
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hpos
      have hip : i ≠ p := fun h => by
        have : p ∉ envs := by
          rw [← h]; simpa using hpos.2
        exact this hp
      simpa [injA, hip] using hra
    · simp only [decide_eq_true_eq] at hra ⊢
      unfold injA; split <;> omega
    · simp only [Bool.not_eq_true'] at hne
      have hqp : q ≠ p := fun h => by
        have : p ∉ envs := by rw [← h]; simpa using hne
        exact this hp
      simpa [injA, hqp] using hra

/-- **Completeness.** A capped marking satisfying the relaxed conjunct is stuck under every
injection future. -/
theorem quiescentE_openStuck {np : Nat} {flat : Rows} {envs : List PlaceId} {mode : InjMode}
    {a : AMarking} (hcap : mode.capped envs a = true)
    (hq : quiescentE np flat envs mode a = true) : OpenStuck flat envs mode a := by
  intro b hb
  have hQ : quiescentE np flat envs mode b = true ∧ mode.capped envs b = true := by
    induction hb with
    | refl => exact ⟨hq, hcap⟩
    | tail _ hs ih =>
      obtain ⟨p, hp, hadm, rfl⟩ := hs
      exact ⟨quiescentE_injA hp ih.1, capped_injA ih.2 hadm⟩
  exact dead_of_quiescentE hQ.2 hQ.1

/-- **A relaxed violation is real**: the reachable marking is dead, and stays dead whatever the
environment injects. -/
theorem relaxed_violation_real {np : Nat} {rows : Rows} {envs : List PlaceId} {mode : InjMode}
    {a0 a : AMarking} (hcap0 : mode.capped envs a0 = true)
    (ha : ReachAE rows envs mode a0 a) (hq : quiescentE np rows envs mode a = true) :
    Dead rows a ∧ OpenStuck rows envs mode a := by
  have hcap := reachAE_capped hcap0 ha
  exact ⟨dead_of_quiescentE hcap hq, quiescentE_openStuck hcap hq⟩

/-- A predicate injection cannot falsify: anything that reads no environment place, or only
grows with one (a stranded-token disjunct over non-sink places). -/
def InjStable (envs : List PlaceId) (P : AMarking → Prop) : Prop :=
  ∀ a p, p ∈ envs → P a → P (injA a p)

theorem InjStable.reach {envs : List PlaceId} {mode : InjMode} {P : AMarking → Prop}
    (hP : InjStable envs P) {a b : AMarking} (h : InjReach envs mode a b) (ha : P a) : P b := by
  induction h with
  | refl => exact ha
  | tail _ hs ih =>
    obtain ⟨p, hp, _, rfl⟩ := hs
    exact hP _ p hp ih

/-- **`relaxed_quiescence_sound`.** A reachable marking stuck under every injection future, with
an injection-stable side condition `P`, has a reachable relaxed-quiescent witness that agrees
with it off the environment places: the error rule `quiescent ∧ P` is reachable, so the encoded
quiescence property cannot be `Proven`. -/
theorem relaxed_quiescence_sound {np N : Nat} {rows : Rows} {envs : List PlaceId}
    {mode : InjMode} {a0 a : AMarking} (hok : ∀ ft ∈ rows, FlatOK np ft.1)
    (hN : DemandBelow N rows) (hN1 : 1 ≤ N) (hcap0 : mode.capped envs a0 = true)
    {P : AMarking → Prop} (hP : InjStable envs P)
    (ha : ReachAE rows envs mode a0 a) (hstuck : OpenStuck rows envs mode a) (hPa : P a) :
    ∃ b, ReachAE rows envs mode a0 b ∧ quiescentE np rows envs mode b = true ∧ P b ∧
      OffEnvEq envs a b := by
  obtain ⟨b, hR, hS, hO, _⟩ := exists_saturation N (reachAE_capped hcap0 ha)
  exact ⟨b, ha.trans (injReach_reachAE hR), quiescentE_of_dead hok hN hN1 hS (hstuck b hR),
    hP.reach hR hPa, hO⟩

/-- **Relaxed quiescence is exact over reachable markings.** For an injection-stable `P`, the
encoded error `quiescentE ∧ P` is reachable iff some reachable marking satisfying `P` is stuck
under every injection future. -/
theorem relaxed_quiescence_exact {np N : Nat} {rows : Rows} {envs : List PlaceId}
    {mode : InjMode} {a0 : AMarking} (hok : ∀ ft ∈ rows, FlatOK np ft.1)
    (hN : DemandBelow N rows) (hN1 : 1 ≤ N) (hcap0 : mode.capped envs a0 = true)
    {P : AMarking → Prop} (hP : InjStable envs P) :
    (∃ a, ReachAE rows envs mode a0 a ∧ OpenStuck rows envs mode a ∧ P a) ↔
      ∃ a, ReachAE rows envs mode a0 a ∧ quiescentE np rows envs mode a = true ∧ P a := by
  constructor
  · rintro ⟨a, ha, hs, hPa⟩
    obtain ⟨b, hb, hq, hPb, _⟩ := relaxed_quiescence_sound hok hN hN1 hcap0 hP ha hs hPa
    exact ⟨b, hb, hq, hPb⟩
  · rintro ⟨a, ha, hq, hPa⟩
    exact ⟨a, ha, (relaxed_violation_real hcap0 ha hq).2, hPa⟩

/-- **No untimed executor deadlock is lost.** An executor run under the environment the mode
describes (`ReachCE`, untimed) that reaches a marking whose α-image is stuck under every
injection future, with an injection-stable side condition `P`, is matched by a reachable
encoded marking satisfying the relaxed conjunct and `P`. Under `Bounded(k)` this needs the two
premises of `proposition_one_inj_bounded` (`NoEnvDeposit`, a capped `M0`). Deadlocks produced by
deadline reaping are outside it (module doc, "Scope"). -/
theorem relaxed_quiescence_sound_executor {np N : Nat} {rows : Rows} {envs : List PlaceId}
    {mode : InjMode} (hG : ∀ tr ∈ rows, GuardFreeConsumeAll tr.1)
    (hDep : mode = .always ∨ NoEnvDeposit rows envs) (hok : ∀ ft ∈ rows, FlatOK np ft.1)
    (hN : DemandBelow N rows) (hN1 : 1 ≤ N) {m0 m : CMarking}
    (hcap0 : mode.capped envs (alpha m0) = true) {P : AMarking → Prop} (hP : InjStable envs P)
    (hm : ReachCE rows envs mode m0 m) (hstuck : OpenStuck rows envs mode (alpha m))
    (hPm : P (alpha m)) :
    ∃ b, ReachAE rows envs mode (alpha m0) b ∧ quiescentE np rows envs mode b = true ∧ P b ∧
      OffEnvEq envs (alpha m) b :=
  relaxed_quiescence_sound hok hN hN1 hcap0 hP (proposition_one_inj_mode hG hDep hcap0 hm).1
    hstuck hPm

/-- **The AC6 vacuity note is true.** When the conjunct is `None`, no capped marking is stuck
under injection: the environment can always enable some transition, and every quiescence
property holds vacuously. -/
theorem quiescence_vacuity_sound {np N : Nat} {flat : Rows} {envs : List PlaceId}
    {mode : InjMode} (hok : ∀ ft ∈ flat, FlatOK np ft.1) (hN : DemandBelow N flat) (hN1 : 1 ≤ N)
    (hnone : encodeQuiescentE np flat envs mode = none) {a : AMarking}
    (hcap : mode.capped envs a = true) : ¬ OpenStuck flat envs mode a := by
  intro hstuck
  obtain ⟨b, hR, hS, _, _⟩ := exists_saturation N hcap
  unfold encodeQuiescentE at hnone
  split at hnone
  · rename_i hany
    obtain ⟨ft, hft, hx⟩ := List.any_eq_true.mp hany
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff] at hx
    have := enabled_of_no_reason (hok ft hft) hS (hN ft hft) hN1 hx.1 (by rw [hx.2]; simp)
    rw [hstuck b hR ft hft] at this
    exact absurd this (by simp)
  · exact absurd hnone (by simp)

/-! ## Retrodiction: the relaxation of `98b9297` -/

/-- **Retrodiction.** On `env → consume → out` under `AlwaysAvailable`, the env-free quiescence
conjunct (what the encoder wrote before `98b9297` relaxed it) holds at the empty marking, so a net
merely waiting for its input was reported deadlocked; with injection the conjunct is `None` (the
AC6 vacuity), and the empty marking is not stuck under injection. -/
theorem retrodict_98b9297_relaxation :
    quiescentBad 2 netEnv m0A = true ∧
    encodeQuiescentE 2 netEnv [envPlace] .always = none ∧
    ¬ OpenStuck netEnv [envPlace] .always m0A := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  have hR : InjReach [envPlace] .always m0A (injA m0A envPlace) :=
    Relation.ReflTransGen.single ⟨envPlace, by simp, rfl, rfl⟩
  have := h _ hR (tConsume, [outPlace]) (by simp [netEnv])
  exact absurd this (by decide)

end Libpetri.Novel.EnvSemantics
