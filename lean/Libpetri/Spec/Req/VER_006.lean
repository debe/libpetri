import Libpetri.Spec.Req.VER_003
import Libpetri.Novel.EnvSemantics
import Libpetri.Reference.Link
import Libpetri.Novel.RouteB.Retrodict
import Libpetri.Spec.Text.VER_006

set_option linter.missingDocs true
set_option autoImplicit false

/-!
# VER-006: Environment Analysis Mode (`spec/07-verification.md`)

How the verifier treats the environment places of a net: modelled injection (`AlwaysAvailable`,
`Bounded(k)`), a net rewrite (`Arrivals(min, max)`), or nothing (`Ignore`). Five blocks:

* `VER_006` (B): the reachable set of the verified open system. Under `AlwaysAvailable` every
  marking the executor reaches with injection is in it; under `Bounded(k)` the same holds behind
  the two premises, and the set never holds more than `k` on an environment place.
* `VER_006_premise` (F): the `Bounded(k)` premise check is exactly the two premises.
* `VER_006_quiescent` (F): quiescence under modelled injection, in the reasons form the encoders
  write (ruling D49 (a)): an input or read arc on an environment place is no reason a
  transition is disabled, unless `Bounded(k)` is below the demand.
* `VER_006_arrivals` (F): `Arrivals(min, max)` is the closed net, exactly for safety and for
  quiescence.
* `VER_006_verdict` (B): the verdict lines over an environment-aware decider: `Ignore` with a
  registered environment place never returns `Proven`; a failed `Bounded(k)` premise is
  `Unknown` and runs no route; a confirmed `Violated` under `Ignore` replays in the verified
  net without injection; the AC6 vacuity note appears only when no marking can rest, and with
  every decided verdict when injection is modelled.

The first four are over the flat open-system model of `Novel/EnvSemantics` (place ids, untimed,
every row read as not reapable). The fifth is over the verdict record of `Spec/Verifier/Result`
(VER-003), at place names; its witness `refEnvVerify` decides through `refVerify` without
injection and proves only the vacuous quiescence properties under modelled injection.
`VER_006_verdict_joint` shows the fifth block and VER-003 hold together of one firing relation,
one violation reading and one decider, for every mode (`ver006_ver003`). `envPremiseOK_eq_premise`
ties the two premise checks: the one the fifth block reads by name equals, on a net at flat place
ids, every check meeting `VER_006_premise` on the net's flat rows. `VER_006_routeB_env` cites AC8 from
the Route B model of `Novel/RouteB/Retrodict.lean`: the frozen environment count, the four cases
of the decline, and the witness.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Novel.ForwardDeposit Libpetri.Novel.EnvSemantics Libpetri.Novel.Seam

/-! ## VER-006 (B): the reachable set of the verified open system -/

/-- The verifier's reachable set of the open system: from the flat rows, the registered
environment places, the injection mode and the initial marking, the markings it treats as
reachable. -/
abbrev OpenReach : Type := Rows → List PlaceId → InjMode → AMarking → AMarking → Prop

/-- The reference: the encoded open system `ReachAE` (each row step capped under `Bounded(k)`,
plus one injection rule per environment place). -/
def refOpenReach : OpenReach := fun rows envs mode a0 a => ReachAE rows envs mode a0 a

#spec_witness refOpenReach

requirement VER_006
  id "VER-006"
  title "Environment Analysis Mode"
  kind B
  scope "the SMT verifier and every route it dispatches to, AlwaysAvailable and Bounded(k), all implementations (SHOULD; the shall sentences bind an implementation that offers environment analysis)"
  source verbatim "spec/07-verification.md"
  covers VER_006.s1, VER_006.s2, VER_006.s3, VER_006.s4, VER_006.s5, VER_006.s6
  reading "For every reachable-set function R of the open system, all flat nets given as rows, environment places envs, caps k and markings:"
          "under AlwaysAvailable, when no consume-all arc carries a guard, every marking the executor reaches with injection (ReachCE, the counts of its coloured marking) is in R from the initial counts;"
          "under Bounded(k), when no consume-all arc carries a guard and the premise check passes (boundedPremiseOK: at most k on each environment place initially, no row deposits into one), the same holds;"
          "under Bounded(k), from an initial marking with at most k on each environment place, every marking in R holds at most k on each environment place."
  assumes "The model is the flat open system of Novel/EnvSemantics: place ids, the flat rows of the verified net (one deposit row per way a firing can end), untimed, every row read as not reapable, counts only. The executor side is ReachCE (StepCE: a row fires on the coloured marking, or one token is injected into an environment place, always under AlwaysAvailable and while fewer than k are resident under Bounded(k)); its counts are alpha. Lines 1 and 2 carry the hypothesis of Proposition 1 that no consume-all arc has a guard (GuardFreeConsumeAll). It holds of every net the spec allows, since IO-006 removed input guards: the flat Transition type keeps the guard field of the older model, and the rows of every reference net carry none (guardFree_toTransition, Reference/Link.lean). The reachable set may be larger than the executor's: the lines are inclusions, which is what a Proven needs; that a Violated replays is VER-003's line 5 on the verified net, whose injection steps the runtimes label inject(p) (abstract_replay.rs)."
          "The third quoted sentence (no conservation law of the closed net on an injected place) is line 1 read on the strengthened set: the conjuncts the encoders add to every rule (P-invariants of VER-005 and VER-007, the counters of VER-016) are part of R, so a law that cuts off a marking the executor reaches breaks line 1. A closed-net law applied to an injected place is killed (VER_006_forbids_closedLaw: env IN → T → OUT conserves IN + OUT without injection, and injection breaks it). That the shipped conjuncts remove no reachable marking is Strengthening.lean, StateEquation.lean and Novel/Certificate.lean, with VER-007's gate H3' (zero weight on an injected place) and VER-005's injector columns (incidence_matrix.rs) as the clauses that keep it true with injection; VER-005 cites this block for the sentence."
          "AC2 (AlwaysAvailable: for env IN → T → OUT, PlaceBound(OUT, k) is Violated for every k) is VER_006_ac2: OUT holds more than k in the reference reachable set, for every k (VER_006_nonvacuous at k = 2); a set without injection is killed (VER_006_forbids_frozen), and so is a Bounded(k) set without the injection rule (VER_006_forbids_boundedFrozen). The Violated verdicts that AC2 and the Bounded(k) half of AC9 name are completeness claims, not lines: the lines are inclusions, which rule out a wrong Proven, and VER-003 allows Unknown on every input (the reference decider refEnvVerify answers Unknown there). They are checked by the runtimes' tests (the env IN → T → OUT regression of smt_verifier.rs), since the conformance corpus covers closed nets only; VER_006_ac2 shows that the violating marking is in the reference reachable set. AC3's first sentence (Bounded(k) limits the state space: a transition requiring more than k tokens from an environment place per firing is never enabled) is the third line, read through VER_006_demand_gate, which derives it for every R meeting the block; a cap read as AlwaysAvailable is killed (VER_006_forbids_uncapped). AC3's premises are VER_006_premise and line 2 of VER_006_verdict; its Route B and state-class wording ('the state-class graphs enable an environment input exactly when it demands at most k whatever the place holds') is Novel/EnvSemantics/Supplied.lean (supplied_safety_exact). No block states it for the shipped graphs: the VER-012 blocks (VER_012, VER_012_build) and the VER-010 blocks say nothing of environment places."
          "AC1 (each mode is selectable via the verifier configuration) is kind N, an offer of configuration: the mode type EnvMode carries the four modes (VER_006_verdict), and no line states the offer. The default mode (AlwaysAvailable for the SMT verifier, Ignore for the state-class graph API, which refuses Arrivals) is kind N (ruling D49 (a), VB3). AC4 to AC6 are VER_006_verdict's; AC9 and AC11 are VER_006_arrivals'; AC10 and the ν paragraph are accounted in VER_006_arrivals' assumes. AC7: line 3 of NU_053_dispatch (no colour-slot bound when injection is modelled on the flat net or an arrival feeds a coloured place) is the part that the name-coloured encoding does not answer there; that the query then takes the flat encoding, the report line and the witness (env source → fork (mint) → join → merged, Unreachable(merged) Violated) are kind Q (Rust smt_verifier.rs nu_route_a_declines_under_environment_injection, Java SmtVerifierTest.nuRouteA_declinesUnderEnvironmentInjection, TypeScript smt-verifier.test.ts 'Route A declines under environment injection (VER-006)'). AC8 is cited (VER_006_routeB_env, over the Route B model of Novel/RouteB/Retrodict.lean): the graph's base under AlwaysAvailable consumes and injects nothing on an environment place, so when no row deposits into an environment place, every class it reaches holds the initial count there (env_count_frozen); the decline route_b_env_observation (rules 1 to 4) names a place exactly in AC8's four cases, the property reading one (a quiescence property reads nothing when no marking can rest), an inhibitor arc testing one, a coloured one, and one two transitions consume under conflict priority (ver006_envObservation_ne_none_iff); and PlaceBound(E, 0) on T : E → P beside an idle ν-join is read off the frozen count and declined (env_count_witness). The model has no Bounded(k) base and no verdict record, so the rest of AC8 is kind Q: that a decline is the call's Unknown naming the place, under AlwaysAvailable and Bounded(k), that a verdict nothing declines stands, with the AC6 note on a quiescence verdict, and the witness net (PlaceBound(IN, 0) Unknown, Unreachable(accepted) Violated). Tests: Rust smt_verifier.rs ver006_route_b_declines_a_property_reading_an_env_place (both modes), ver006_route_b_declines_an_inhibitor_on_an_env_place, ver006_route_b_declines_a_coloured_env_place, ver006_route_b_still_answers_when_no_env_count_is_read, ver006_route_b_quiescence_vacuity_note_and_decline; Java SmtVerifierTest ver006ac8_routeB_propertyReadingEnvironmentPlace_isUnknown, _inhibitorOnEnvironmentPlace_isUnknown, _colouredEnvironmentPlace_isUnknown, _verdictsNotObservingTheEnvironment_stand, _vacuousQuiescence_carriesTheAc6Note; TypeScript smt-verifier.test.ts 'SmtVerifier Route B under environment injection (VER-006)' (five cases). In the conflict case every runtime reads whether conflict priority applies, not the selected mode, so on a net with a reapable transition the verdict stands as under NONE: Rust smt_verifier.rs nu_052_env_decline_only_where_conflict_priority_applies, Java SmtVerifierTest envDeclineReadsWhetherConflictPriorityApplies_NU052_VER006_AC8, TypeScript smt-verifier.test.ts 'NU-052 / VER-006 AC8: the env decline applies only where conflict priority is in effect', Python test_nu_verification.py test_nu_052_env_decline_only_where_conflict_priority_applies. Reading the selected mode there, which declines where AC8 lets the verdict stand, is the behaviour RD-39 recorded (spec/runtime-defects.md). Steps 3 and 5 of NU_055_refusal (an arrival that feeds a coloured place; an environment place Route B cannot model, under AlwaysAvailable or Bounded(k)) are AC10 and AC8 for the name-alignment properties."
  signoff "2026-11-13 78e7cf929f6d5e80 ai"
  statement : OpenReach → Prop :=
    fun R =>
      (∀ rows envs m0 m, (∀ tr ∈ rows, GuardFreeConsumeAll tr.1) →
        ReachCE rows envs .always m0 m → R rows envs .always (alpha m0) (alpha m)) ∧
      (∀ rows envs k m0 m, (∀ tr ∈ rows, GuardFreeConsumeAll tr.1) →
        boundedPremiseOK k envs rows m0 = true →
        ReachCE rows envs (.bounded k) m0 m → R rows envs (.bounded k) (alpha m0) (alpha m)) ∧
      (∀ rows envs k a0 a, (∀ e ∈ envs, a0 e ≤ k) →
        R rows envs (.bounded k) a0 a → ∀ e ∈ envs, a e ≤ k)

/- The pinned readable form of VER-006: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.VER_006 : OpenReach → Prop :=
fun R =>
  (∀ (rows : Rows) (envs : List PlaceId) (m0 m : CMarking),
      (∀ tr ∈ rows, GuardFreeConsumeAll tr.1) →
        ReachCE rows envs InjMode.always m0 m → R rows envs InjMode.always (alpha m0) (alpha m)) ∧
    (∀ (rows : Rows) (envs : List PlaceId) (k : ℕ) (m0 m : CMarking),
        (∀ tr ∈ rows, GuardFreeConsumeAll tr.1) →
          boundedPremiseOK k envs rows m0 = true →
            ReachCE rows envs (InjMode.bounded k) m0 m → R rows envs (InjMode.bounded k) (alpha m0) (alpha m)) ∧
      ∀ (rows : Rows) (envs : List PlaceId) (k : ℕ) (a0 a : AMarking),
        (∀ e ∈ envs, a0 e ≤ k) → R rows envs (InjMode.bounded k) a0 a → ∀ e ∈ envs, a e ≤ k
-/
#guard_msgs in #print VER_006

/-- ✓ **The encoded open system meets the block.** Example: on `env IN → T → OUT`, the executor
injects one token into `IN` and fires `T`; the encoding has the injection rule, so it reaches
`OUT = 1` too, and under `Bounded(1)` it never holds two tokens on `IN`. -/
@[evidence holds VER_006]
theorem VER_006_reference : VER_006 refOpenReach :=
  ⟨fun _ _ _ _ hG h => proposition_one_inj hG h,
   fun _ _ _ _ _ hG hok h => (bounded_checked_sound hG hok h).1,
   fun _ _ _ _ _ h0 h => reachAE_bounded_le h0 h⟩

/-- `env IN → T → OUT` after `n` arrivals each consumed by `T`: `OUT = n`, nothing else. -/
def ver006Out (n : Nat) : AMarking := fun q => if q = outPlace then n else 0

/-- One more arrival and one more firing of `T` in the encoded system. -/
theorem ver006_out_succ (n : Nat) :
    ReachAE netEnv [envPlace] .always (ver006Out n) (ver006Out (n + 1)) := by
  have h1 : StepAE netEnv [envPlace] .always (ver006Out n) (injA (ver006Out n) envPlace) :=
    Or.inr ⟨envPlace, by simp, rfl, rfl⟩
  have h2 : StepAE netEnv [envPlace] .always (injA (ver006Out n) envPlace) (ver006Out (n + 1)) := by
    refine Or.inl ⟨⟨(tConsume, [outPlace]), by simp [netEnv],
      by simp [enabledA, injA, ver006Out, tConsume, envPlace, outPlace, Card.required], ?_⟩, rfl⟩
    funext q
    simp only [fireAD, ver006Out, injA, tConsume, envPlace, outPlace, consumeAllAt, specAt, pre]
    rcases q with _ | _ | q <;> simp [Card.consumesAll, Card.required]
  exact (Relation.ReflTransGen.single h1).tail h2

/-- **AC2: `AlwaysAvailable` reaches an unbounded `OUT`.** Example: on `env IN → T → OUT` from
the empty marking, `k + 1` arrivals each followed by a firing of `T` put `k + 1` tokens on
`OUT`, so `PlaceBound(OUT, k)` is violated in the reference reachable set, whatever `k`. -/
@[evidence cites "VER-006" "AC2"]
theorem VER_006_ac2 :
    ∀ k : Nat, ∃ a, refOpenReach netEnv [envPlace] .always m0A a ∧ k < a outPlace := by
  intro k
  refine ⟨ver006Out (k + 1), ?_, by simp [ver006Out]⟩
  have : ∀ n, ReachAE netEnv [envPlace] .always m0A (ver006Out n) := by
    intro n
    induction n with
    | zero =>
      have : ver006Out 0 = m0A := by funext q; simp [ver006Out, m0A]
      rw [this]
      exact Relation.ReflTransGen.refl
    | succ n ih => exact ih.trans (ver006_out_succ n)
  exact this (k + 1)

/-- ✓ **AC2 at `k = 2`.** Example: on `env IN → T → OUT` from the empty marking, three arrivals,
each consumed by `T`, put three tokens on `OUT`: `PlaceBound(OUT, 2)` is violated in the
reference reachable set. -/
@[evidence nonvacuous VER_006]
theorem VER_006_nonvacuous :
    ∃ a, refOpenReach netEnv [envPlace] .always m0A a ∧ 2 < a outPlace :=
  VER_006_ac2 2

/-- ✓ **AC3, first sentence, from the block.** For every reachable-set function meeting VER-006,
under `Bounded(k)` from a capped initial marking no marking in the set enables a row that takes
more than `k` tokens from an environment place. Example: under `Bounded(1)`, a transition
`exactly(2, E) → out` is never enabled. -/
theorem VER_006_demand_gate {R : OpenReach} (h : VER_006 R) {rows : Rows} {envs : List PlaceId}
    {k : Nat} {a0 a : AMarking} (h0 : ∀ e ∈ envs, a0 e ≤ k) (ha : R rows envs (.bounded k) a0 a)
    {tr : Transition × Deposit} {s : InSpec} (hs : s ∈ tr.1.inputs) (he : s.place ∈ envs)
    (hk : k < s.card.required) : enabledA a tr.1 = false := by
  have hle := h.2.2 rows envs k a0 a h0 ha s.place he
  cases hen : enabledA a tr.1 with
  | false => rfl
  | true =>
    simp only [enabledA, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hen
    have := hen.1.1 s hs
    omega

/-- Mutant: no injection rule (the encoding before `98b9297`): the environment is frozen. -/
def ver006Frozen : OpenReach := fun rows _ _ a0 a => ReachAD rows a0 a

theorem ver006_frozen_stays {a : AMarking} (h : ReachAD netEnv m0A a) : a = m0A := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    subst ih
    obtain ⟨tr, hmem, hen, _⟩ := hs
    have : tr = (tConsume, [outPlace]) := by simpa [netEnv] using hmem
    subst this
    exact absurd hen (by decide)

/-- ✗ **A frozen environment is not modelled injection** (line 1). Example: on
`env IN → T → OUT` the executor injects one token and fires `T`, reaching `OUT = 1`; without
an injection rule the encoding reaches only the empty marking, so it would prove
`PlaceBound(OUT, 0)`. -/
@[evidence forbids VER_006]
theorem VER_006_forbids_frozen : ¬ VER_006 ver006Frozen := by
  intro h
  obtain ⟨_, m, hrun, hlen, _⟩ := retrodict_98b9297
  have hG : ∀ tr ∈ netEnv, GuardFreeConsumeAll tr.1 := by
    intro tr htr s hs hca
    simp only [netEnv, List.mem_singleton] at htr
    subst htr
    simp only [tConsume, List.mem_singleton] at hs
    subst hs
    exact absurd hca (by decide)
  have hR : ReachAD netEnv (alpha (fun _ => [])) (alpha m) := h.1 netEnv [envPlace] _ m hG hrun
  have hm0 : alpha (fun _ => []) = m0A := by funext p; simp [alpha, m0A]
  rw [hm0] at hR
  have := congrFun (ver006_frozen_stays hR) outPlace
  simp only [alpha] at this
  rw [hlen] at this
  exact absurd this (by decide)

/-- Mutant: `Bounded(k)` read as `AlwaysAvailable` (no cap). -/
def ver006Uncapped : OpenReach := fun rows envs _ a0 a => ReachAE rows envs .always a0 a

/-- ✗ **The cap is part of the mode** (line 3). Example: with one environment place and
`Bounded(0)`, an uncapped encoding injects one token, a marking the cap forbids. -/
@[evidence forbids VER_006]
theorem VER_006_forbids_uncapped : ¬ VER_006 ver006Uncapped := by
  intro h
  have hstep : ReachAE [] [0] .always (fun _ => 0) (injA (fun _ => 0) 0) :=
    Relation.ReflTransGen.single (Or.inr ⟨0, by simp, rfl, rfl⟩)
  have := h.2.2 [] [0] 0 (fun _ => 0) _ (by simp) hstep 0 (by simp)
  simp [injA] at this

/-- Mutant: the `Bounded(k)` reachable set without injection (the cap kept, the injection rule
dropped). -/
def ver006BoundedFrozen : OpenReach := fun rows envs mode a0 a =>
  match mode with
  | .always => ReachAE rows envs .always a0 a
  | .bounded _ => ReachAD rows a0 a

/-- ✗ **Bounded(k) injects too** (line 2). Example: on `env IN → T → OUT` under `Bounded(1)` the
premises hold (nothing deposits into `IN`, which starts empty), and the executor injects one
token and fires `T`; a `Bounded(k)` encoding without the injection rule never reaches
`OUT = 1`. -/
@[evidence forbids VER_006]
theorem VER_006_forbids_boundedFrozen : ¬ VER_006 ver006BoundedFrozen := by
  intro h
  have hG : ∀ tr ∈ netEnv, GuardFreeConsumeAll tr.1 := by
    intro tr htr s hs hca
    simp only [netEnv, List.mem_singleton] at htr
    subst htr
    simp only [tConsume, List.mem_singleton] at hs
    subst hs
    exact absurd hca (by decide)
  have hrun : ReachCE netEnv [envPlace] (.bounded 1) (fun _ => []) mOut :=
    (Relation.ReflTransGen.single
      (show StepCE netEnv [envPlace] (.bounded 1) (fun _ => []) mInj from
        Or.inr ⟨envPlace, by simp, by decide, 0, rfl⟩)).tail
      (show StepCE netEnv [envPlace] (.bounded 1) mInj mOut from Or.inl retro_fire)
  have hR : ReachAD netEnv (alpha (fun _ => [])) (alpha mOut) :=
    h.2.1 netEnv [envPlace] 1 _ mOut hG (by decide) hrun
  have hm0 : alpha (fun _ => []) = m0A := by funext p; simp [alpha, m0A]
  rw [hm0] at hR
  have := congrFun (ver006_frozen_stays hR) outPlace
  revert this
  decide

/-- Mutant: the closed-net law `IN + OUT = const` of `env IN → T → OUT` conjoined to every
marking, the injected place `IN` included (a strengthening without the gate H3'). -/
def ver006ClosedLaw : OpenReach := fun rows envs mode a0 a =>
  ReachAE rows envs mode a0 a ∧ a envPlace + a outPlace = a0 envPlace + a0 outPlace

/-- ✗ **No closed-net law on an injected place** (line 1, the third quoted sentence). Example:
without injection `env IN → T → OUT` keeps `IN + OUT` constant, 0 from the empty marking. The
executor injects one token into `IN` and fires `T`, reaching `OUT = 1`; a reachable set cut down
by the closed-net law misses that marking and would prove `PlaceBound(OUT, 0)`. -/
@[evidence forbids VER_006]
theorem VER_006_forbids_closedLaw : ¬ VER_006 ver006ClosedLaw := by
  intro h
  obtain ⟨_, m, hrun, hlen, _⟩ := retrodict_98b9297
  have hG : ∀ tr ∈ netEnv, GuardFreeConsumeAll tr.1 := by
    intro tr htr s hs hca
    simp only [netEnv, List.mem_singleton] at htr
    subst htr
    simp only [tConsume, List.mem_singleton] at hs
    subst hs
    exact absurd hca (by decide)
  have := (h.1 netEnv [envPlace] _ m hG hrun).2
  simp only [alpha, List.length_nil] at this
  omega

/-! ## AC8: Route B under modelled injection -/

theorem ver006_orElse_ne_none {α : Type} (a : Option α) (b : Unit → Option α) :
    a.orElse b ≠ none ↔ a ≠ none ∨ b () ≠ none := by
  cases a <;> simp [Option.orElse]

theorem ver006_find_ne_none {l : List PlaceId} {q : PlaceId → Bool} :
    l.find? q ≠ none ↔ ∃ p ∈ l, q p = true := by
  rw [Ne, List.find?_eq_none]
  simp

/-- Route B's environment decline (`route_b_env_observation`, rules 1 to 4, modelled as
`Novel.RouteB.envObservation`) names a place exactly when some declared environment place is
coloured, is tested by an inhibitor arc, is consumed by two transitions under conflict priority,
or is read by the property (`observed`: nothing for a quiescence property when no marking can
rest). These are the four triggers of AC8. -/
theorem ver006_envObservation_ne_none_iff {declared : PlaceId → Bool} {envs : List PlaceId}
    {coloured : PlaceId → Bool} {net : List Novel.RouteB.NuTrans} {conflict : Bool}
    {prop : Novel.RouteB.PropShape} {vacuous : Bool} {sinks markers : List PlaceId} :
    Novel.RouteB.envObservation declared envs coloured net conflict prop vacuous sinks markers ≠
        none ↔
      ∃ p ∈ envs, declared p = true ∧
        (coloured p = true ∨
          (net.any fun T => T.base.inhibitors.contains p) = true ∨
          (conflict = true ∧
            2 ≤ (net.filter fun T => T.base.inputs.any fun s => s.place == p).length) ∨
          p ∈ Novel.RouteB.observed prop vacuous (envs.filter declared) sinks markers) := by
  generalize hob : Novel.RouteB.observed prop vacuous (envs.filter declared) sinks markers = ob
  unfold Novel.RouteB.envObservation
  simp only [hob]
  rw [ver006_orElse_ne_none, ver006_orElse_ne_none, ver006_orElse_ne_none,
    ver006_find_ne_none, ver006_find_ne_none, ver006_find_ne_none]
  have h3 : ((if conflict = true then (envs.filter declared).find? fun p =>
        decide (2 ≤ (net.filter fun T => T.base.inputs.any fun s => s.place == p).length)
      else none) ≠ none) ↔
      ∃ p ∈ envs.filter declared, conflict = true ∧
        2 ≤ (net.filter fun T => T.base.inputs.any fun s => s.place == p).length := by
    cases conflict
    · simp
    · simp only [if_true, ver006_find_ne_none, decide_eq_true_eq, true_and]
  rw [h3]
  simp only [List.mem_filter, List.contains_iff_mem]
  constructor
  · rintro (⟨p, ⟨hp, hd⟩, h⟩ | ⟨p, ⟨hp, hd⟩, h⟩ | ⟨p, ⟨hp, hd⟩, h⟩ | ⟨p, ⟨hp, hd⟩, h⟩)
    · exact ⟨p, hp, hd, Or.inl h⟩
    · exact ⟨p, hp, hd, Or.inr (Or.inl h)⟩
    · exact ⟨p, hp, hd, Or.inr (Or.inr (Or.inl h))⟩
    · exact ⟨p, hp, hd, Or.inr (Or.inr (Or.inr (by simpa using h)))⟩
  · rintro ⟨p, hp, hd, h | h | h | h⟩
    · exact Or.inl ⟨p, ⟨hp, hd⟩, h⟩
    · exact Or.inr (Or.inl ⟨p, ⟨hp, hd⟩, h⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨p, ⟨hp, hd⟩, h⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨p, ⟨hp, hd⟩, by simpa using h⟩))

/-- **AC8: Route B under modelled injection.** Three facts of the Route B model
(`Novel/RouteB/Retrodict.lean`). First, the graph's base under `AlwaysAvailable` (`envBase`:
an input arc on an environment place is always met and consumes nothing, nothing is injected)
keeps an environment place at its initial count in every class it reaches, when no branch
outcome deposits into one (`env_count_frozen`): the count in a state class is not the
environment's. Second, the decline names a place exactly in the four cases AC8 lists
(`ver006_envObservation_ne_none_iff`). Third, the witness: on `T : E → P` beside an idle
ν-join, every class has `E = 0`, one injection gives `E = 1`, and the decline names `E` for
`PlaceBound(E, 0)` (`env_count_witness`). -/
@[evidence cites "VER-006" "AC8: Route B models an environment place under AlwaysAvailable / Bounded(k) only as an inexhaustible input, so its count in a state class is not the environment's; when a verdict would depend on that count or name layer (the property reads an environment place, a quiescence property only when quiescence is reachable; an inhibitor arc tests one; one is coloured; conflict priority prunes on one two transitions consume) Route B declines naming the place"]
theorem VER_006_routeB_env :
    (∀ (co envs : List PlaceId) (net : List Novel.RouteB.NuTrans)
        (role : Novel.RouteB.NuTrans → Novel.RouteB.Role) (conflict : Bool),
      (∀ T ∈ net, ∀ r ∈ T.rows, ∀ p ∈ envs, p ∉ r.places) →
      ∀ (S0 S : Novel.RouteB.NState co AMarking),
        Explorer.Reach
            (Novel.RouteB.routeB (Novel.RouteB.envBase envs) net role conflict) S0 S →
          ∀ p ∈ envs, S.b p = S0.b p) ∧
    (∀ (declared : PlaceId → Bool) (envs : List PlaceId) (coloured : PlaceId → Bool)
        (net : List Novel.RouteB.NuTrans) (conflict : Bool) (prop : Novel.RouteB.PropShape)
        (vacuous : Bool) (sinks markers : List PlaceId),
      Novel.RouteB.envObservation declared envs coloured net conflict prop vacuous sinks
          markers ≠ none ↔
        ∃ p ∈ envs, declared p = true ∧
          (coloured p = true ∨
            (net.any fun T => T.base.inhibitors.contains p) = true ∨
            (conflict = true ∧
              2 ≤ (net.filter fun T => T.base.inputs.any fun s => s.place == p).length) ∨
            p ∈ Novel.RouteB.observed prop vacuous (envs.filter declared) sinks markers)) ∧
    ((∀ S, Explorer.Reach
          (Novel.RouteB.routeB (Novel.RouteB.envBase [2]) Novel.RouteB.EnvW.net
            Novel.RouteB.Ignore.role false)
          (Novel.RouteB.initState Novel.RouteB.EnvW.co Novel.RouteB.Ignore.zero) S →
        S.b 2 = 0) ∧
      (∃ a, ReachADInj (Novel.RouteB.nuRows Novel.RouteB.EnvW.net) [2]
        Novel.RouteB.Ignore.zero a ∧ a 2 = 1) ∧
      Novel.RouteB.envObservation (fun _ => true) [2]
          (fun p => Novel.RouteB.EnvW.co.contains p) Novel.RouteB.EnvW.net false
          (.reach [2]) false [] [] = some 2) :=
  ⟨fun _ _ _ _ _ hno _ _ h => Novel.RouteB.env_count_frozen hno h,
   fun _ _ _ _ _ _ _ _ _ => ver006_envObservation_ne_none_iff,
   Novel.RouteB.EnvW.env_count_witness⟩

/-! ## VER-006 (F): the `Bounded(k)` premise check -/

/-- A premise check: from the cap, the registered environment places, the flat rows and the
initial marking, whether the verifier may run a route under `Bounded(k)`. -/
abbrev PremiseCheck : Type := Nat → List PlaceId → Rows → CMarking → Bool

/-- The reference: `bounded_premise_violation(..) == None` (`environment.rs`). -/
def refPremise : PremiseCheck := fun k envs rows m0 => boundedPremiseOK k envs rows m0

#spec_witness refPremise

requirement VER_006_premise
  id "VER-006"
  title "Environment Analysis Mode: the Bounded(k) premises"
  kind F
  scope "the SMT verifier under Bounded(k), before any route, all implementations"
  source verbatim "spec/07-verification.md"
  covers VER_006.s7
  reading "For every premise check P, cap k, environment places envs, flat rows and initial marking m0: P passes exactly when m0 holds at most k tokens on each place of envs (EnvCappedC) and no row deposits a token into a place of envs (NoEnvDeposit)."
  assumes "The flat rows stand for the verified net's transitions: a transition deposits into a place exactly when one of its rows does, since the flattener writes one row per branch of the output spec, and the runtimes read the output places of the spec (Rust t.output_places() in bounded_premise_violation, environment.rs), which are the places of its branches. The check is sufficient, not exact: a deposit that could never push the place above k is refused too. Untimed, counts only."
          "What the verifier does when the check fails (Unknown, naming the place and the broken premise, and no route runs) is line 2 of VER_006_verdict, whose check envPremiseOK reads the places each output spec names; on every net at flat place ids it is the check of every P meeting this block, applied to the net's flat rows (envPremiseOK_eq_premise). The order of the check (environment places in code-point order, the initial marking first, the first depositing transition in code-point order, a completion step complete:<t> of VER-004 named t) is the reason text, kind Q. Why the premises are needed is Novel/EnvSemantics: without them the encoding's post-cap blocks firings the executor makes (bounded_initial_overflow_wrong_proven, bounded_producer_overflow_wrong_proven) and the state-class graphs miss firings (supplied_bounded_deposit_wrong_proven, supplied_bounded_initial_wrong_proven, quiescence_bounded_initial_spurious); behind the check the reachable set, the supplied successor and the quiescence clause cover the executor (bounded_checked_sound, bounded_checked_supplied_sound, bounded_checked_quiescence_sound). AC3 is this block, line 2 of VER_006_verdict and line 3 of VER_006."
  signoff "2026-11-13 b320fdb9fbe5f6af ai"
  statement : PremiseCheck → Prop :=
    fun P => ∀ k envs rows m0,
      P k envs rows m0 = true ↔ EnvCappedC k envs m0 ∧ NoEnvDeposit rows envs

/- The pinned readable form of VER-006's premise block. -/
/--
info: def Libpetri.Spec.VER_006_premise : PremiseCheck → Prop :=
fun P =>
  ∀ (k : ℕ) (envs : List PlaceId) (rows : Rows) (m0 : CMarking),
    P k envs rows m0 = true ↔ EnvCappedC k envs m0 ∧ NoEnvDeposit rows envs
-/
#guard_msgs in #print VER_006_premise

/-- ✓ **The shipped check is the two premises.** Example: under `Bounded(1)` a net whose initial
marking holds one token on the environment place and in which no transition deposits into it
passes; two tokens there, or a transition that deposits into it, fail. -/
@[evidence holds VER_006_premise]
theorem VER_006_premise_reference : VER_006_premise refPremise :=
  fun _ _ _ _ => boundedPremiseOK_iff

/-- `t0 : a → E`, a transition that deposits into the environment place `E = 1` (AC3). -/
def ver006T0 : Transition :=
  { name := "t0", inputs := [{ place := 0, card := .one, guard := none }],
    inhibitors := [], reads := [], resets := [] }

/-- `t1 : exactly(2, E) → out`, demanding two tokens of `E = 1` (AC3). -/
def ver006T1 : Transition :=
  { name := "t1", inputs := [{ place := 1, card := .exactly 2, guard := none }],
    inhibitors := [], reads := [], resets := [] }

/-- The AC3 net `t0 : a → E`, `t1 : exactly(2, E) → out` (`a = 0`, `E = 1`, `out = 2`). -/
def ver006RowsAC3 : Rows := [(ver006T0, [1]), (ver006T1, [2])]

/-- `M0 = {a: 2}`. -/
def ver006M0A2 : CMarking := fun p => if p = 0 then [0, 0] else []

/-- `M0 = {E: 2}`. -/
def ver006M0E2 : CMarking := fun p => if p = 1 then [0, 0] else []

/-- `M0 = {E: 1}`. -/
def ver006M0E1 : CMarking := fun p => if p = 1 then [0] else []

/-- ✓ **The AC3 nets.** Example: under `Bounded(1)` with `E` registered, `t0 : a → E`,
`t1 : exactly(2, E) → out` from `{a: 2}` fails the check (`t0` deposits into `E`); `t1` alone
from `{E: 2}` fails it too (the initial count); `t1` alone from `{E: 1}` passes. -/
@[evidence nonvacuous VER_006_premise]
theorem VER_006_premise_nonvacuous :
    refPremise 1 [1] ver006RowsAC3 ver006M0A2 = false ∧
    refPremise 1 [1] [(ver006T1, [2])] ver006M0E2 = false ∧
    refPremise 1 [1] [(ver006T1, [2])] ver006M0E1 = true := by
  decide

/-- Mutant: the check that reads only the initial marking. -/
def ver006PremiseInitOnly : PremiseCheck := fun k envs _ m0 =>
  envs.all (fun e => decide ((m0 e).length ≤ k))

/-- ✗ **A depositing transition fails the check** (the deposit premise). Example: on the AC3
net from `{a: 2}`, the initial marking holds nothing on `E`, but `t0` deposits into it; a check
of the initial marking alone passes, and the post-cap then blocks `t0`'s second firing, which
the executor makes. -/
@[evidence forbids VER_006_premise]
theorem VER_006_premise_forbids_initOnly : ¬ VER_006_premise ver006PremiseInitOnly := by
  intro h
  have := (h 1 [1] ver006RowsAC3 ver006M0A2).mp (by decide)
  have h0 := this.2 (ver006T0, [1]) (by simp [ver006RowsAC3]) 1 (by simp)
  simp at h0

/-- Mutant: the check that reads only the deposits. -/
def ver006PremiseDepOnly : PremiseCheck := fun _ envs rows _ =>
  envs.all (fun e => rows.all fun tr => tr.2.count e == 0)

/-- ✗ **An overfull initial marking fails the check** (the initial-count premise). Example: `t1`
alone from `{E: 2}` under `Bounded(1)`: nothing deposits into `E`, but it starts above the cap;
a check of the deposits alone passes. -/
@[evidence forbids VER_006_premise]
theorem VER_006_premise_forbids_depOnly : ¬ VER_006_premise ver006PremiseDepOnly := by
  intro h
  have := (h 1 [1] [(ver006T1, [2])] ver006M0E2).mp (by decide)
  have h0 := this.1 1 (by simp)
  revert h0
  decide

/-! ## VER-006 (F): quiescence under modelled injection -/

/-- A quiescence test of the open system: from the place count, the flat rows, the registered
environment places, the injection mode and a marking, whether the marking is quiescent. -/
abbrev OpenQuiescent : Type := Nat → Rows → List PlaceId → InjMode → AMarking → Bool

/-- The reference: the relaxed quiescence conjunct of `encode_quiescent` (`smt_encoder.rs`). -/
def refOpenQuiescent : OpenQuiescent := fun np rows envs mode a => quiescentE np rows envs mode a

#spec_witness refOpenQuiescent

requirement VER_006_quiescent
  id "VER-006"
  title "Environment Analysis Mode: quiescence under modelled injection"
  kind F
  scope "the quiescence clause of DeadlockFree, TerminatesAtSink, QuiescentCount and JoinedOrDeadLettered on every route, AlwaysAvailable and Bounded(k), all implementations"
  source verbatim "spec/07-verification.md"
  covers VER_006.s9, VER_006.s10, VER_006.s11
  reading "For every quiescence test Q, place count np, flat rows, environment places envs, mode and marking a: Q calls a quiescent exactly when every row is permanently disabled (permDisabled: an input on an environment place demanding more than the cap, or a read on one under Bounded(0)) or has a disabling reason that holds at a (disableReasonsE: an input on a place that is not an environment place below its demand, any inhibitor arc whose place is marked, a read on a place that is not an environment place and is empty)."
  assumes "The model is the flat open system of Novel/EnvSemantics, untimed: every row is read as not reapable, which is every row of an untimed net and of a net under assumeNoReaping. The shipped encode_quiescent skips a reapable row (smt_encoder.rs), so 'every transition that is not reapable' is the rows here; the reap-aware reading without injection is VER-002's and ReapAware.lean's. The combination of the skip with injection is not proved: the reapable half of the two quiescence sentences has no evidence here, an open item. An inhibitor arc is a reason whatever its place, since it reads the current count. A place with two input arcs on one transition is outside the model (FlatOK, InputsDistinctPlaces)."
          "The third quoted sentence is the meaning of the reasons form, derived for every Q meeting the block, and it speaks only of reachable markings from a capped initial marking (which the Bounded(k) premises give): pointwise it is false, since under Bounded(1) a transition whose only input is exactly(2, E) on the environment place E is permanently disabled, so {E: 2} counts as quiescent although that transition is enabled there. VER_006_quiescent_stuck (a reachable capped marking Q calls quiescent is dead and stays dead under every injection, relaxed_violation_real), and VER_006_quiescent_exact for the other direction over reachable markings (a reachable marking stuck under every injection future has a reachable saturation Q calls quiescent, so a quiescence property loses no violation; relaxed_quiescence_exact, under a demand bound and for an injection-stable side condition). The two forms agree on reachable markings, not pointwise, which is why the block quotes the reasons form (ruling D49 (a), VB1)."
          "AC6 (when injection makes some transition enabled in every marking a quiescence property is vacuously true and the report names the reason) is VER_006_verdict's lines 4 and 5 over the same reasons; quiescence_vacuity_sound proves the note true here: when some row has no reason left and is not permanently disabled, no capped marking is stuck under injection. The body sentence 'Under a mode that models injection an environment place is an ordinary place for the rest set of [VER-014]: a token left on it is stranded unless the caller declares the place a sink, as the closure of [VER-022] does.' is an explanatory consequence, not a line of this block or of VER-014: VER-014's rest set reads every place that is not a sink and sets no environment place apart, so with injection modelled a token on an environment place is stranded like any other. Here InjStable covers the stranded-token disjunct over places that are not sinks, environment places included, which the runtimes treat so (stranding_excuses, rest_set.rs)."
  signoff "2026-11-13 3b37261915f411c2 ai"
  statement : OpenQuiescent → Prop :=
    fun Q => ∀ np rows envs mode a,
      Q np rows envs mode a = true ↔
        ∀ ft ∈ rows, permDisabled np envs mode ft.1 = true ∨
          (disableReasonsE np envs ft.1).any (fun r => r a) = true

/- The pinned readable form of VER-006's quiescence block. -/
/--
info: def Libpetri.Spec.VER_006_quiescent : OpenQuiescent → Prop :=
fun Q =>
  ∀ (np : ℕ) (rows : Rows) (envs : List PlaceId) (mode : InjMode) (a : AMarking),
    Q np rows envs mode a = true ↔
      ∀ ft ∈ rows, permDisabled np envs mode ft.1 = true ∨ ((disableReasonsE np envs ft.1).any fun r => r a) = true
-/
#guard_msgs in #print VER_006_quiescent

/-- The relaxed conjunct without its redundant first clause: a row with no reason left that is
not permanently disabled already fails the per-row clause. -/
theorem quiescentE_iff_rows {np : Nat} {rows : Rows} {envs : List PlaceId} {mode : InjMode}
    {a : AMarking} :
    quiescentE np rows envs mode a = true ↔
      ∀ ft ∈ rows, permDisabled np envs mode ft.1 = true ∨
        (disableReasonsE np envs ft.1).any (fun r => r a) = true := by
  rw [quiescentE_iff]
  refine ⟨fun h => h.2, fun h => ⟨fun hany => ?_, h⟩⟩
  obtain ⟨ft, hft, hx⟩ := List.any_eq_true.mp hany
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff] at hx
  rcases h ft hft with hp | hr
  · rw [hx.1] at hp; exact absurd hp (by simp)
  · rw [hx.2] at hr; exact absurd hr (by simp)

/-- ✓ **The shipped conjunct is the reasons form.** Example: on `env IN → T → OUT` under
`AlwaysAvailable`, `T`'s only input is on `IN`, so it has no reason left and no marking is
quiescent; under `Bounded(0)` the same input demands more than the cap, `T` is permanently
disabled, and every marking is. -/
@[evidence holds VER_006_quiescent]
theorem VER_006_quiescent_reference : VER_006_quiescent refOpenQuiescent :=
  fun _ _ _ _ _ => quiescentE_iff_rows

/-- **The meaning, from the block.** For every quiescence test meeting the block, a marking
reachable in the encoded open system from a capped initial marking that the test calls
quiescent enables no row, and no sequence of injections makes it enable one. Example: on
`env IN → T → OUT` under `AlwaysAvailable` no marking is called quiescent, and indeed the
environment can always enable `T`. The reachability matters: under `Bounded(1)` the marking
`{E: 2}` is called quiescent beside `exactly(2, E) → out`, which is enabled there, but no run
from a capped start reaches it (`VER_006_quiescent_pointwise`). -/
@[evidence cites "VER-006" "A marking quiescent in this sense that is reachable with injection, from an initial marking that holds at most `k` tokens on each environment place under `Bounded(k)`, enables no transition, and no sequence of injections makes it enable one."]
theorem VER_006_quiescent_stuck {Q : OpenQuiescent} (h : VER_006_quiescent Q) {np : Nat}
    {rows : Rows} {envs : List PlaceId} {mode : InjMode} {a0 a : AMarking}
    (hcap0 : mode.capped envs a0 = true) (ha : ReachAE rows envs mode a0 a)
    (hq : Q np rows envs mode a = true) : Dead rows a ∧ OpenStuck rows envs mode a :=
  relaxed_violation_real hcap0 ha (quiescentE_iff_rows.mpr ((h np rows envs mode a).mp hq))

/-- **Why the sentence speaks of reachable markings.** Example: under `Bounded(1)` with `E`
registered, `t1 : exactly(2, E) → out` demands more than the cap, so it counts as permanently
disabled and the marking `{E: 2}` is called quiescent, yet `t1` is enabled there. From a start
with at most one token on `E` no run reaches `{E: 2}`. -/
theorem VER_006_quiescent_pointwise :
    refOpenQuiescent 3 [(ver006T1, [2])] [1] (.bounded 1) (fun p => if p = 1 then 2 else 0) = true ∧
    enabledA (fun p => if p = 1 then 2 else 0) ver006T1 = true := by
  decide

/-- **No stuck marking is lost, from the block.** For every quiescence test meeting the block,
an injection-stable side condition `P`, a demand bound `N ≥ 1` and a capped initial marking:
some reachable marking satisfying `P` is stuck under every injection future exactly when some
reachable marking satisfying `P` is called quiescent. Example: a marking waiting on an inhibitor
arc that no injection can lift is found; one merely waiting for an arrival is not. -/
@[evidence cites "VER-006" "*While* the mode is `AlwaysAvailable` or `Bounded(k)`, the verifier *shall* treat a marking as quiescent exactly when every transition that is not reapable is permanently disabled or has a disabling reason that holds at the marking."]
theorem VER_006_quiescent_exact {Q : OpenQuiescent} (h : VER_006_quiescent Q) {np N : Nat}
    {rows : Rows} {envs : List PlaceId} {mode : InjMode} {a0 : AMarking}
    (hok : ∀ ft ∈ rows, FlatOK np ft.1) (hN : DemandBelow N rows) (hN1 : 1 ≤ N)
    (hcap0 : mode.capped envs a0 = true) {P : AMarking → Prop} (hP : InjStable envs P) :
    (∃ a, ReachAE rows envs mode a0 a ∧ OpenStuck rows envs mode a ∧ P a) ↔
      ∃ a, ReachAE rows envs mode a0 a ∧ Q np rows envs mode a = true ∧ P a := by
  have hQ : ∀ a, Q np rows envs mode a = quiescentE np rows envs mode a := by
    intro a
    apply Bool.eq_iff_iff.mpr
    rw [h np rows envs mode a, quiescentE_iff_rows]
  simp only [hQ]
  exact relaxed_quiescence_exact hok hN hN1 hcap0 hP

/-- Mutant: plain quiescence, the conjunct before `98b9297` (an environment input is a reason). -/
def ver006PlainQuiescent : OpenQuiescent := fun np rows _ _ a => quiescentBad np rows a

/-- ✗ **Waiting for input is not quiescence** (the first quoted sentence). Example: on
`env IN → T → OUT` from the empty marking under `AlwaysAvailable`, the plain test calls the
marking quiescent because `IN` is empty, and would report a deadlock on a net that is merely
waiting for its input; with injection `T` has no reason left. -/
@[evidence forbids VER_006_quiescent]
theorem VER_006_quiescent_forbids_plain : ¬ VER_006_quiescent ver006PlainQuiescent := by
  intro h
  obtain ⟨hq, _, hns⟩ := retrodict_98b9297_relaxation
  exact hns (VER_006_quiescent_stuck h rfl Relation.ReflTransGen.refl hq).2

/-- Mutant: `Bounded(k)` read as `AlwaysAvailable` (no transition is permanently disabled). -/
def ver006UncappedQuiescent : OpenQuiescent := fun np rows envs _ a =>
  quiescentE np rows envs .always a

/-- ✗ **A demand above the cap is permanently disabled** (the `unless` clause). Example: with
only `t1 : exactly(2, E) → out` and `E` registered under `Bounded(1)`, the environment can never
supply two tokens, so every marking is quiescent; a test that ignores the cap sees no reason
left for `t1` and calls no marking quiescent. -/
@[evidence forbids VER_006_quiescent]
theorem VER_006_quiescent_forbids_uncapped : ¬ VER_006_quiescent ver006UncappedQuiescent := by
  intro h
  have := (h 3 [(ver006T1, [2])] [1] (.bounded 1) (fun _ => 0)).mpr (by decide)
  revert this
  decide

/-- ✓ **The reasons on small nets.** Example: on `env IN → T → OUT` the empty marking is not
quiescent under `AlwaysAvailable` (the environment can enable `T`); with `t1 : exactly(2, E)`
under `Bounded(1)` it is (the demand is above the cap); and with `E` not registered, `t1` waits
on an ordinary place, so the empty marking is quiescent and `{E: 2}` is not. -/
@[evidence nonvacuous VER_006_quiescent]
theorem VER_006_quiescent_nonvacuous :
    refOpenQuiescent 2 netEnv [envPlace] .always m0A = false ∧
    refOpenQuiescent 3 [(ver006T1, [2])] [1] (.bounded 1) (fun _ => 0) = true ∧
    refOpenQuiescent 3 [(ver006T1, [2])] [] .always (fun _ => 0) = true ∧
    refOpenQuiescent 3 [(ver006T1, [2])] [] .always (fun p => if p = 1 then 2 else 0) = false := by
  decide

/-! ## VER-006 (F): `Arrivals(min, max)` is its closure -/

/-- An `Arrivals` rewrite: from the flat rows, the registered environment places (in
registration order), the first fresh place id, `min` and `max`, the closed net's rows and its
initial marking. -/
structure ArrClosure where
  /-- The closed net's rows. -/
  rows : Rows → List PlaceId → Nat → Nat → Nat → Rows
  /-- The closed net's initial marking, from the net's. -/
  seed : AMarking → List PlaceId → Nat → Nat → Nat → AMarking

/-- The reference: the [VER-022] closure with one arrival group `(min, max)` per environment
place (`closureRows`, `closureM0`; `open_net::close_arrivals_between`). -/
def refArrivals : ArrClosure := ⟨closureRows, closureM0⟩

#spec_witness refArrivals

requirement VER_006_arrivals
  id "VER-006"
  title "Environment Analysis Mode: Arrivals(min, max) is a net rewrite"
  kind F
  scope "the SMT verifier under Arrivals(min, max), before any route, all implementations"
  source verbatim "spec/07-verification.md"
  covers VER_006.s14
  reading "For every Arrivals rewrite C, all flat nets given as rows, environment places envs (distinct, below the fresh place id base), min ≤ max, and markings a0, a of the net (zero from base on), with every arc, reset and deposit of the rows below base:"
          "some marking reachable in the closed net (C's rows from C's seed) agrees with a below base exactly when the open system, in which a row fires or one token arrives on an environment place that has seen fewer than max, reaches a from a0 with some arrival counts;"
          "some dead marking reachable in the closed net agrees with a below base exactly when the open system reaches a with at least min arrivals on every environment place and no row of the net is enabled at a."
  assumes "The model is the flat open system of Novel/EnvSemantics (Arrivals.lean), untimed, counts only; the fresh places of the closure are the ids from base on, which stands for the name-freshness check of VER-022 ('A name the rewrite would add that the net already declares is rejected, as in [VER-022].', kind B of that block). The closure omits a source whose count is 0 with its transitions (groupRows), so Arrivals(k) has no mandatory source and Arrivals(k, k) no optional one; the line states the rows' effect, not their names. The names env:arrivals[i], env:arrive[i]:P, env:optional[i], env:arrive?[i]:P and env:decline[i], the report form arrivals(k) / arrivals(min..max), and that the rewritten net is verified with no environment place left (so every route, P-invariants and quiescence apply to it as to a closed net) are kind Q and N; that P-invariants range over the rewritten net is VER-005 on the closed net."
          "AC9 (Arrivals(k) bounds the total: for env IN → T → OUT, PlaceBound(OUT, k) Proven and PlaceBound(OUT, k − 1) Violated with k arrivals, while Bounded(k) gives Violated for both; DeadlockFree with OUT a sink decided without the AC6 note) is line 1, with OUT holding at most the arrivals so far (a closure without the optional source, which would prove PlaceBound(OUT, 0) under Arrivals(1), is killed: VER_006_arrivals_forbids_noOpt), and line 4 of VER_006_verdict, which allows the note only when some transition has no reason left: on the closed net T keeps its input on IN, an ordinary place there. arrivals_enumeration_sound composes line 1 with the closed enumeration: its Proven holds for every executor run under the environment. The trace wording is kind Q."
          "AC11 (Arrivals(min, max) requires the mandatory arrivals: QuiescentCount({OUT}, 2, 2) Proven under Arrivals(2, 2) and Violated under Arrivals(2) with a trace through env:decline[0]; Arrivals(k) and Arrivals(0, k) give the same verdicts, traces and scripts; min < 0 and max < min are rejected) is line 2 for the mandatory arrivals: a rewrite that drops the mandatory source is killed (VER_006_arrivals_forbids_noMin) on that net, where it lets a run rest with no arrival. Arrivals(k) = Arrivals(0, k) holds by construction (the mode has one form, arrivals 0 k). The rejection of min < 0 or max < min when the mode is built, and before any route runs for a mode value written directly (a Rust enum variant), is kind N (ruling D49 (a), VB3): the model's counts are natural numbers and the lines assume min ≤ max."
          "AC10 (under Arrivals(k) with a coloured environment place no ν route treats the injection transition as a mint; the ν routes decline naming the place) and the ν paragraph ('An injection transition producing into a coloured place ([NU-051]) is **not** a mint: the ν routes ([NU-050] Route A, [VER-012] Route B) MUST NOT classify it as one', and 'When an injected place is coloured, the ν routes decline with `Unknown` naming the place, exactly as AC8 does under `AlwaysAvailable`.') are not a line here: ArrClosure is the closure of the flat net and carries no ν layer. Step 3 of NU_055_refusal refuses a name-alignment call in which an arrival feeds a coloured place, and line 3 of NU_053_dispatch runs no colour-slot bound (Route A declines) when an arrival feeds a coloured place. For the other properties it is kind Q. All three runtimes decline on both ν routes before any mint is read, whatever the caller declares: the check colours every producer only to find which places are coloured (coloured_arrival_reason, smt_verifier.rs; colouredArrivalReason in SmtVerifier.java and smt-verifier.ts). A decline is the route's answer, and the call's verdict is what the pipeline gives after it: on Route B the Unknown naming the place, as AC8's; on Route A, and on Route B when a marked coloured place keeps Route B from building its graph, the flat encoding, which reads no names, with a report line naming the place (AC7's form). Tests: Rust smt_verifier.rs arrivals_into_a_coloured_place_is_declined_by_route_b and arrivals_into_a_coloured_place_is_not_coloured_by_route_a; Java EnvironmentArrivalsTest anArrivalIntoAColouredPlace_routeBDeclinesNamingThePlace, anArrivalIntoAColouredPlace_quiescenceDeclinesToo and anArrivalIntoAColouredPlace_routeADeclinesToTheFlatEncoding_namingThePlace; TypeScript arrivals-mode.test.ts 'no ν route treats an arrival as a mint: Route B declines naming the place'. A mint declaration naming an injection transition env:arrive[i]:P is refused in every runtime, since the declaration is judged on the caller's net (NU-010); the decline does not read the declarations either way."
  signoff "2026-11-13 935f095991d6f423 ai"
  statement : ArrClosure → Prop :=
    fun C => ∀ rows envs base lo hi a0 a,
      RowsBelow base rows → (∀ p ∈ envs, p < base) → envs.Nodup → lo ≤ hi →
      ZeroAbove base a0 → ZeroAbove base a →
      ((∃ x, ReachAD (C.rows rows envs base lo hi) (C.seed a0 envs base lo hi) x ∧
          AgreeBelow base x a) ↔
        ∃ c, ReachArr rows envs hi (a0, fun _ => 0) (a, c)) ∧
      ((∃ x, ReachAD (C.rows rows envs base lo hi) (C.seed a0 envs base lo hi) x ∧
          Dead (C.rows rows envs base lo hi) x ∧ AgreeBelow base x a) ↔
        ∃ c, ReachArr rows envs hi (a0, fun _ => 0) (a, c) ∧ (∀ p ∈ envs, lo ≤ c p) ∧
          Dead rows a)

/- The pinned readable form of VER-006's Arrivals block. -/
/--
info: def Libpetri.Spec.VER_006_arrivals : ArrClosure → Prop :=
fun C =>
  ∀ (rows : Rows) (envs : List PlaceId) (base lo hi : ℕ) (a0 a : AMarking),
    RowsBelow base rows →
      (∀ p ∈ envs, p < base) →
        envs.Nodup →
          lo ≤ hi →
            ZeroAbove base a0 →
              ZeroAbove base a →
                ((∃ x, ReachAD (C.rows rows envs base lo hi) (C.seed a0 envs base lo hi) x ∧ AgreeBelow base x a) ↔
                    ∃ c, ReachArr rows envs hi (a0, fun x => 0) (a, c)) ∧
                  ((∃ x,
                      ReachAD (C.rows rows envs base lo hi) (C.seed a0 envs base lo hi) x ∧
                        Dead (C.rows rows envs base lo hi) x ∧ AgreeBelow base x a) ↔
                    ∃ c, ReachArr rows envs hi (a0, fun x => 0) (a, c) ∧ (∀ p ∈ envs, lo ≤ c p) ∧ Dead rows a)
-/
#guard_msgs in #print VER_006_arrivals

/-- ✓ **The VER-022 closure is exact.** Example: on `env IN → T → OUT` under `Arrivals(2, 2)` the
closed net has a mandatory source of two tokens; it rests only after both have arrived and `T`
has fired twice, with `OUT = 2`, which is exactly the open system's rest with two arrivals. -/
@[evidence holds VER_006_arrivals]
theorem VER_006_arrivals_reference : VER_006_arrivals refArrivals :=
  fun _ _ _ _ _ _ _ hR hE hN hlh hA0 ha =>
    ⟨arrivals_closure_reach hR hE hN hlh hA0 ha, arrivals_closure_quiescent hR hE hN hlh hA0 ha⟩

/-- Mutant: the closure with no mandatory source (`min` read as 0): `Arrivals(2, 2)` closed as
`Arrivals(2)`. -/
def ver006ArrNoMin : ArrClosure :=
  ⟨fun rows envs base _ hi => closureRows rows envs base 0 hi,
   fun a0 envs base _ hi => closureM0 a0 envs base 0 hi⟩

/-- On `env IN → T → OUT` (`IN = 0`, `OUT = 1`), every arrival counted at `IN` is on `IN` or
has moved to `OUT`. -/
theorem ver006_arr_count {s : AMarking × (PlaceId → Nat)}
    (h : ReachArr netEnv [envPlace] 2 (m0A, fun _ => 0) s) : s.1 0 + s.1 1 = s.2 0 := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    rcases hs with ⟨⟨tr, hmem, hen, h1⟩, h2⟩ | ⟨p, hp, _, h1, h2⟩
    · rw [h1]
      have : tr = (tConsume, [outPlace]) := by simpa [netEnv] using hmem
      subst this
      simp only [enabledA, tConsume, envPlace, List.all_cons, List.all_nil, Bool.and_true,
        decide_eq_true_eq, Card.required] at hen
      rw [h2, ← ih]
      simp only [fireAD, tConsume, envPlace, outPlace, consumeAllAt, specAt, pre, Card.required,
        Card.consumesAll]
      simp
      omega
    · simp only [List.mem_singleton] at hp
      subst hp
      rw [h1, h2]
      simp only [injA, bumpC, envPlace]
      simp
      omega

/-- The closed net of the mutant on `env IN → T → OUT` declines both optional arrivals. -/
theorem ver006_noMin_rests :
    ∃ x, ReachAD (ver006ArrNoMin.rows netEnv [envPlace] 2 2 2)
        (ver006ArrNoMin.seed m0A [envPlace] 2 2 2) x ∧
      Dead (ver006ArrNoMin.rows netEnv [envPlace] 2 2 2) x ∧ AgreeBelow 2 x m0A := by
  let r := ver006ArrNoMin.rows netEnv [envPlace] 2 2 2
  let s0 := ver006ArrNoMin.seed m0A [envPlace] 2 2 2
  let dec := srcT s!"env:decline[{(0 : Nat)}]" (optP 2 0)
  have hmem : (dec, ([] : Deposit)) ∈ r := by
    simp [r, dec, ver006ArrNoMin, closureRows, envRows, groupRows]
  let s1 : AMarking := fun q => if q = 3 then 1 else 0
  have h1 : StepAD r s0 s1 := by
    refine ⟨(dec, []), hmem, by decide, ?_⟩
    funext q
    simp only [fireAD, dec, srcT, optP, consumeAllAt, specAt, pre, s0, s1, ver006ArrNoMin,
      closureM0, m0A, Card.required, Card.consumesAll]
    rcases q with _ | _ | _ | _ | q <;> simp
  have h2 : StepAD r s1 (fun _ => 0) := by
    refine ⟨(dec, []), hmem, by decide, ?_⟩
    funext q
    simp only [fireAD, dec, srcT, optP, consumeAllAt, specAt, pre, s1, Card.required,
      Card.consumesAll]
    rcases q with _ | _ | _ | _ | q <;> simp
  refine ⟨fun _ => 0, (Relation.ReflTransGen.single h1).tail h2, ?_, fun q _ => rfl⟩
  intro tr htr
  change tr ∈ closureRows netEnv [envPlace] 2 0 2 at htr
  revert tr
  decide

/-- ✗ **A run rests only after the mandatory arrivals** (line 2). Example: on `env IN → T → OUT`
under `Arrivals(2, 2)`, `QuiescentCount({OUT}, 2, 2)` holds: the closed net rests only with
`OUT = 2`. A closure without the mandatory source lets both optional arrivals be declined, and
the empty marking becomes a rest, although the open system never rests there with two
arrivals. -/
@[evidence forbids VER_006_arrivals]
theorem VER_006_arrivals_forbids_noMin : ¬ VER_006_arrivals ver006ArrNoMin := by
  intro h
  have hR : RowsBelow 2 netEnv := by
    intro tr htr
    simp only [netEnv, List.mem_singleton] at htr
    subst htr
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [tConsume, envPlace, outPlace]
  obtain ⟨c, hr, hlo, -⟩ :=
    ((h netEnv [envPlace] 2 2 2 m0A m0A hR (by simp [envPlace]) (by simp) le_rfl
      (fun _ _ => rfl) (fun _ _ => rfl)).2.mp ver006_noMin_rests)
  have hc := ver006_arr_count hr
  have := hlo envPlace (by simp)
  simp [m0A] at hc
  simp [envPlace] at this
  omega

/-- Mutant: the closure with no optional source (`max` read as `min`): `Arrivals(k)` closed as
`Arrivals(0, 0)`. -/
def ver006ArrNoOpt : ArrClosure :=
  ⟨fun rows envs base lo _ => closureRows rows envs base lo lo,
   fun a0 envs base lo _ => closureM0 a0 envs base lo lo⟩

/-- ✗ **Every arrival up to `max` is possible** (line 1). Example: on `env IN → T → OUT` under
`Arrivals(1)`, one token may arrive on `IN` and `T` moves it to `OUT`, so `OUT = 1` is reachable
and `PlaceBound(OUT, 0)` is violated; a closure without the optional source never delivers it,
and would prove the bound. -/
@[evidence forbids VER_006_arrivals]
theorem VER_006_arrivals_forbids_noOpt : ¬ VER_006_arrivals ver006ArrNoOpt := by
  intro h
  have hR : RowsBelow 2 netEnv := by
    intro tr htr
    simp only [netEnv, List.mem_singleton] at htr
    subst htr
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [tConsume, envPlace, outPlace]
  have hz : ZeroAbove 2 (ver006Out 1) := fun q hq => by
    have : q ≠ outPlace := by simp only [outPlace]; omega
    simp [ver006Out, this]
  have hopen : ∃ c, ReachArr netEnv [envPlace] 1 (m0A, fun _ => 0) (ver006Out 1, c) := by
    refine ⟨bumpC (fun _ => 0) envPlace, ?_⟩
    have h1 : StepArr netEnv [envPlace] 1 (m0A, fun _ => 0)
        (injA m0A envPlace, bumpC (fun _ => 0) envPlace) :=
      Or.inr ⟨envPlace, by simp, by decide, rfl, rfl⟩
    have h2 : StepArr netEnv [envPlace] 1 (injA m0A envPlace, bumpC (fun _ => 0) envPlace)
        (ver006Out 1, bumpC (fun _ => 0) envPlace) := by
      refine Or.inl ⟨⟨(tConsume, [outPlace]), by simp [netEnv],
        by simp [enabledA, injA, m0A, tConsume, envPlace, Card.required], ?_⟩, rfl⟩
      funext q
      simp only [fireAD, ver006Out, injA, m0A, tConsume, envPlace, outPlace, consumeAllAt,
        specAt, pre]
      rcases q with _ | _ | q <;> simp [Card.consumesAll, Card.required]
    exact (Relation.ReflTransGen.single h1).tail h2
  obtain ⟨x, hx, hag⟩ := ((h netEnv [envPlace] 2 0 1 m0A (ver006Out 1) hR (by simp [envPlace])
    (by simp) (by omega) (fun _ _ => rfl) hz).1.mpr hopen)
  have hrows : ver006ArrNoOpt.rows netEnv [envPlace] 2 0 1 = netEnv := by
    simp [ver006ArrNoOpt, closureRows, envRows, groupRows]
  have hseed : ver006ArrNoOpt.seed m0A [envPlace] 2 0 1 = m0A := by
    funext q
    simp only [ver006ArrNoOpt, closureM0, m0A]
    split
    · rfl
    · split <;> simp
  rw [hrows, hseed] at hx
  have := hag outPlace (by decide)
  rw [ver006_frozen_stays hx] at this
  simp [m0A, ver006Out] at this

/-- ✓ **`Arrivals(2, 2)` on `env IN → T → OUT`.** Example: the closed net's rows are the net's
row `T` and the mandatory group `env:arrive[0]:IN`; its seed holds the two mandatory tokens on
the fresh place 2 and nothing on the optional place 3. -/
@[evidence nonvacuous VER_006_arrivals]
theorem VER_006_arrivals_nonvacuous :
    (refArrivals.rows netEnv [envPlace] 2 2 2).length = 2 ∧
    refArrivals.seed m0A [envPlace] 2 2 2 2 = 2 ∧
    refArrivals.seed m0A [envPlace] 2 2 2 3 = 0 ∧
    (refArrivals.rows netEnv [envPlace] 2 0 2).length = 3 := by
  decide

/-! ## VER-006 (B): the verdict under an environment mode -/

open Libpetri.Spec.Verifier

/-- The environment analysis mode ([VER-006]): `AlwaysAvailable`, `Bounded(k)`,
`Arrivals(min, max)` (`Arrivals(k)` is `arrivals 0 k`) and `Ignore`. -/
inductive EnvMode where
  /-- `AlwaysAvailable`: injection at any time. -/
  | always
  /-- `Bounded(k)`: injection while fewer than `k` tokens are resident. -/
  | bounded (k : Nat)
  /-- `Arrivals(min, max)`: between `min` and `max` arrivals per environment place in total. -/
  | arrivals (lo hi : Nat)
  /-- `Ignore`: environment places are not modelled. -/
  | ignore
  deriving DecidableEq, Repr

/-- Whether the mode models injection (`AlwaysAvailable`, `Bounded(k)`). -/
def EnvMode.injects : EnvMode → Bool
  | .always | .bounded _ => true
  | _ => false

/-- Whether the modelled injection can supply `n` tokens to one firing: always under
`AlwaysAvailable`, when `n ≤ k` under `Bounded(k)`, never where no injection is modelled. -/
def EnvMode.supplies : EnvMode → Nat → Bool
  | .always, _ => true
  | .bounded k, n => decide (n ≤ k)
  | _, _ => false

/-- **An environment-aware decider**: a verifier entry point that also reads the mode and the
registered environment places. -/
abbrev EnvDecider (K : Type) : Type := EnvMode → List K → Decider K

section EnvDefs

variable {K : Type} [DecidableEq K]

/-- **The `Bounded(k)` premises, by name** (`bounded_premise_violation(..) == None`,
`environment.rs`): the initial marking holds at most `k` on each registered environment place,
and no transition's output spec names one. -/
def envPremiseOK (k : Nat) (envs : List K) (X : Reference.TimedNet K) (m0 : NMarking K) :
    Bool :=
  envs.all (fun e => decide (m0.count e ≤ k)) &&
    envs.all (fun e => X.net.transitions.all fun t =>
      match t.out with
      | none => true
      | some o => !decide (e ∈ outPlaces o))

/-- **A transition with no reason left** under the mode (`encode_quiescent`, `smt_encoder.rs`):
it is not reapable (its timing's flag, cleared under `assumeNoReaping`), has no inhibitor arc,
every input arc either demands nothing or sits on an environment place the injection can supply,
and every read arc sits on an environment place the injection can supply one token to. Such a
transition is enabled, through injection, in every marking. -/
def reasonFree (o : Options) (mode : EnvMode) (envs : List K) (X : Reference.TimedNet K)
    (t : Reference.Trans K) : Bool :=
  !(!o.assumeNoReaping && (X.timing t).reapable) && t.core.inhibitors.isEmpty &&
    t.core.inputs.all (fun s => s.card.required == 0 ||
      (decide (s.place ∈ envs) && mode.supplies s.card.required)) &&
    t.core.reads.all (fun p => decide (p ∈ envs) && mode.supplies 1)

/-- **No marking can be quiescent** under the mode (`quiescence_unreachable`): some transition
has no reason left. -/
def NoRest (o : Options) (mode : EnvMode) (envs : List K) (X : Reference.TimedNet K) : Bool :=
  X.net.transitions.any (reasonFree o mode envs X)

end EnvDefs

/-- The quiescence properties of [VER-002]: `DeadlockFree`, `TerminatesAtSink`,
`QuiescentCount` (`!is_reachability_safety`). -/
def quiescenceProp {K : Type} : VerProp K → Bool
  | .deadlockFree _ _ | .terminatesAtSink _ | .quiescentCount _ _ _ _ => true
  | _ => false

/-- The AC6 vacuity note (its wording is kind Q). -/
def vacuityNote : String :=
  "no marking of this net can be quiescent: a transition is enabled in every marking, so every quiescence property is vacuously true here"

/-- Why `Ignore` refuses a `Proven` (`IGNORE_MODE_VACUITY_REASON`). -/
def ignoreReason : String :=
  "environment places present but not modeled (mode=Ignore); a proof would be vacuous"

/-- Why a failed `Bounded(k)` premise gives `Unknown`. -/
def premiseReason : String :=
  "an environment place is outside the Bounded(k) premises: the initial marking holds more than k there, or a transition deposits into it"

/-- Why the reference steps aside under modelled injection. -/
def injectionAsideReason : String :=
  "the reference decides only the vacuous quiescence properties under modelled injection"

/-- Why the reference steps aside under `Arrivals`. -/
def arrivalsAsideReason : String :=
  "the reference leaves the Arrivals closure to the flat model (closureRows)"

/-- The verified-net function under `Ignore`: VER-001's, with no injection. -/
def ver006IgnoreAbs {K : Type} [DecidableEq K] : Abs K := inertAbs

#spec_witness ver006IgnoreAbs

/-- The `Ignore` refusal: a `Proven` becomes `Unknown`, every other verdict stands. -/
def ver006Downgrade : Verdict → Verdict
  | .proven _ => .unknown ignoreReason
  | v => v

section EnvRef

variable {K : Type} [LinearOrder K] [Hashable K]

/-- Under modelled injection with environment places registered, the reference decides only a
quiescence property that no marking can violate: `Proven`, as every runtime's encoding does when
`encode_quiescent` returns `None`. Everything else it leaves `Unknown`. -/
def injDecide (mode : EnvMode) (envs : List K) : Decider K := fun o X φ m0 =>
  if Unresolved X φ m0 then
    { verdict := .unknown
        "the property names a place that the net does not declare and the initial marking does not mark" }
  else if quiescenceProp φ && NoRest o mode envs X then
    { verdict := .proven "vacuous", route := .smt }
  else { verdict := .unknown injectionAsideReason }

/-- The verdict part of the reference. With no environment place registered every mode is the
closed net, decided by `refVerify`. Otherwise: `Ignore` runs `refVerify` over VER-001's net and
turns a `Proven` into `Unknown`; `Bounded(k)` checks the premises first; `AlwaysAvailable` and a
passed `Bounded(k)` run `injDecide`; `Arrivals` steps aside. -/
def envBase (mode : EnvMode) (envs : List K) : Decider K := fun o X φ m0 =>
  if envs = [] then refVerify ver006IgnoreAbs o X φ m0
  else match mode with
  | .ignore =>
    let r := refVerify ver006IgnoreAbs o X φ m0
    { r with verdict := ver006Downgrade r.verdict }
  | .bounded k =>
    if envPremiseOK k envs X m0 then injDecide (.bounded k) envs o X φ m0
    else { verdict := .unknown premiseReason }
  | .always => injDecide .always envs o X φ m0
  | .arrivals _ _ => { verdict := .unknown arrivalsAsideReason }

/-- Whether the mode is `Bounded(k)` and its premises fail. -/
def premiseFails (mode : EnvMode) (envs : List K) (X : Reference.TimedNet K) (m0 : NMarking K) :
    Bool :=
  match mode with
  | .bounded k => !envPremiseOK k envs X m0
  | _ => false

/-- **The reference environment-aware decider**: `envBase`, with the AC6 vacuity note on a
quiescence property when some transition has no reason left, except after a failed premise
(no route runs). -/
def refEnvVerify : EnvDecider K := fun mode envs o X φ m0 =>
  { envBase mode envs o X φ m0 with
    notes := if quiescenceProp φ && NoRest o mode envs X && !premiseFails mode envs X m0
             then [vacuityNote] else [] }

#spec_witness refEnvVerify

end EnvRef

requirement VER_006_verdict
  id "VER-006"
  title "Environment Analysis Mode: verdicts"
  kind B
  scope "the SMT verifier and every route it dispatches to, all implementations (SHOULD; the shall sentences bind an implementation that offers environment analysis)"
  source verbatim "spec/07-verification.md"
  covers VER_006.s15, VER_006.s8, VER_006.s16, VER_006.s12, VER_006.s13
  reading "For every firing relation F, violation reading V, verified-net function abs of the net without injection, and environment-aware decider D, and all registered environment places envs, options o, timed nets X, properties φ and initial markings m0:"
          "if envs is not empty, D under Ignore does not return Proven;"
          "if the Bounded(k) premise check fails (envPremiseOK: some environment place holds more than k initially, or some transition's output spec names one), D under Bounded(k) returns Unknown with the route Unavailable;"
          "if D under Ignore returns Violated with counterexampleConfirmed true, then for every query q that abs returns, its trace is a firing sequence under F of q's net from q's initial marking to a marking that violates q's property under V;"
          "under every mode, if D reports the vacuity note, φ is a quiescence property and some transition has no reason left under the mode (NoRest);"
          "under AlwaysAvailable or Bounded(k), with envs not empty, φ a quiescence property and some transition with no reason left, if D returns Proven or Violated, it reports the vacuity note."
  assumes "The decider is VER-003's with two more arguments, the mode and the registered environment places, so every VER-003 line applies to D mode envs for the verified-net function of that mode; for Ignore that function is abs, the verified net without injection, which line 3 reads (ruling D49 (a), VB2). Line 3 is that a quiescence Violated under Ignore is a rest of the net with a silent environment, which need not be a rest under injection: on env IN → T → OUT the empty marking violates TerminatesAtSink({OUT}) under Ignore and no marking can be quiescent under AlwaysAvailable (VER_006_verdict_nonvacuous). A reachability-safety Violated under Ignore is a counterexample under injection too, since a run without injection is a run with it (VER_006_frozen_in_injected)."
          "'On any route' and 'run no route' are read on the result: the lines hold whatever route the decider dispatches to, and a refusal placed inside one route after another route proved the property is killed (VER_006_verdict_forbids_noDowngrade). Run no route is the route Unavailable, as Rust, Java and TypeScript report it; the reason text naming the place and the premise, and the code-point order of the check, are kind Q. The premises themselves are VER_006_premise over the flat rows; envPremiseOK is the same check by name, reading the places of each output spec (outPlaces), as Rust's t.output_places() does, and on a net at flat place ids it equals every check meeting VER_006_premise on the net's flat rows (envPremiseOK_flat, envPremiseOK_eq_premise). Line 2 binds the refusal when the check fails, not its converse: a decider whose own check also refuses a place holding exactly k tokens (held >= k where the runtimes write held > k, environment.rs bounded_premise_violation) meets the five lines, because its answer (Unknown, route Unavailable, no note) is one VER-003 allows on every input and the runtimes give after a passed check too (Rust's in-flight refusal of VER-004 and the budget cut of VER-013, smt_verifier.rs). The 'exactly when' half is VER_006_premise's, over the check itself."
          "The vacuity condition is read on the verified net. The runtimes evaluate it after the terminal rewrite of EXEC-042, which gives every transition an inhibitor arc on each terminal place (terminal_places.rs, inhibit_on_terminals, applied before verify_net in smt_verifier.rs; TypeScript swaps the rewritten net in, Java does the same in prepare()), so on a net with a terminal place every transition keeps a reason and no note is reported. The nets X here are Reference nets, which have no terminal place, so NoRest reads the user's transitions and the two readings agree; nets with terminal places are outside X, and the terminal rewrite is EXEC-042's."
          "Lines 4 and 5 are AC6 and the reworded vacuity paragraph (ruling D49 (a), VB1). The note's presence is the line, its wording kind Q. Line 4 holds under every mode: under Ignore and Arrivals no injection is modelled, so an input or read arc on an environment place is an ordinary reason (EnvMode.supplies is false there), and the closure of Arrivals adds only transitions with an input arc; so under Ignore and Arrivals the note is allowed only for a net with a transition that needs no token at all, as on a closed net; under Arrivals the runtimes compute the condition on the closed net, which has the same transitions with no reason left as the net. Line 5 is scoped to a mode that models injection with environment places registered: there no enumeration or structural route runs (VER-017, VER-020 skip a net with environment places), and Route B and the flat encoding both append the note (smt_verifier.rs, quiescence_vacuous). Without environment places the enumeration route can decide a quiescence property on a net with an input-free transition and does not append the note in Rust; that corner is outside line 5. That the note is true (no capped marking is stuck under injection) is quiescence_vacuity_sound, cited by VER_006_quiescent. 'The verdict stands' is the absence of a refusal: no line forbids the Proven, and VER-003's soundness line holds of it on the verified net with injection."
          "AC4 (Ignore with registered environment places never returns Proven) and AC5 (on every route, including any structural or state-class route) are line 1, read at the decider (VER_006_verdict_forbids_noDowngrade). The body's 'a safety property that holds only because environment-gated transitions never fire' is the reason; the line refuses every Proven, as all runtimes do (ignores_environment, smt_verifier.rs; ruling D49 (a), VB3)."
          "The quiescence properties here are VER-002's three (quiescenceProp: DeadlockFree, TerminatesAtSink, QuiescentCount), the ones the property type VerProp carries. JoinedOrDeadLettered, which the vacuity paragraph also names, is NU-040's property and is not in VerProp, so lines 4 and 5 say nothing about it, and no block states its vacuity note: NU-040's block NU_040_jodl fixes which markings violate it and reads no environment mode. The runtimes report the note for it as for the other quiescence properties, since they test for a quiescence property as 'not reachability-safety' (Rust quiescence_vacuous and is_reachability_safety in smt_verifier.rs, Java isReachabilitySafety in SmtVerifier.java), and JoinedOrDeadLettered is not reachability-safety. The note is test evidence only for DeadlockFree (Rust ver006_route_b_quiescence_vacuity_note_and_decline); no test checks it for JoinedOrDeadLettered. AC6's QuiescentNameAligned exception (Unknown where no marking can rest) is step 5 of NU_055_refusal, over the call type of NU-055, which this decider does not carry. AC1 is the mode type EnvMode, an offer of configuration, kind N, which no line states; the defaults and the state-class API scope are kind N."
  signoff "2026-11-13 d171b9a7b7d07920 ai"
  statement : ∀ {K : Type} [LinearOrder K], FireRel K → SafetyViolRel K → Abs K → EnvDecider K →
      Prop :=
    fun F V abs D =>
      ∀ envs o X φ m0,
        (envs ≠ [] → ∀ meth, (D .ignore envs o X φ m0).verdict ≠ .proven meth) ∧
        (∀ k, envPremiseOK k envs X m0 = false →
          (∃ why, (D (.bounded k) envs o X φ m0).verdict = .unknown why) ∧
          (D (.bounded k) envs o X φ m0).route = .unavailable) ∧
        ((D .ignore envs o X φ m0).verdict = .violated →
          (D .ignore envs o X φ m0).confirmed = some true →
          ∀ q, abs o X φ m0 = .ok q →
            ∃ f, RunF F q.net.net (D .ignore envs o X φ m0).trace q.init f ∧
              V o.assumeNoReaping q.net q.prop f) ∧
        (∀ mode, vacuityNote ∈ (D mode envs o X φ m0).notes →
          quiescenceProp φ = true ∧ NoRest o mode envs X = true) ∧
        (∀ mode, mode.injects = true → envs ≠ [] → quiescenceProp φ = true →
          NoRest o mode envs X = true →
          ((D mode envs o X φ m0).verdict = .violated ∨
            ∃ meth, (D mode envs o X φ m0).verdict = .proven meth) →
          vacuityNote ∈ (D mode envs o X φ m0).notes)

/- The pinned readable form of VER-006's verdict block. -/
/--
info: def Libpetri.Spec.VER_006_verdict : {K : Type} →
  [LinearOrder K] → FireRel K → SafetyViolRel K → Abs K → EnvDecider K → Prop :=
fun {K} [LinearOrder K] F V abs D =>
  ∀ (envs : List K) (o : Options) (X : Reference.TimedNet K) (φ : VerProp K) (m0 : NMarking K),
    (envs ≠ [] → ∀ (meth : String), (D EnvMode.ignore envs o X φ m0).verdict ≠ Verdict.proven meth) ∧
      (∀ (k : ℕ),
          envPremiseOK k envs X m0 = false →
            (∃ why, (D (EnvMode.bounded k) envs o X φ m0).verdict = Verdict.unknown why) ∧
              (D (EnvMode.bounded k) envs o X φ m0).route = Route.unavailable) ∧
        ((D EnvMode.ignore envs o X φ m0).verdict = Verdict.violated →
            (D EnvMode.ignore envs o X φ m0).confirmed = some true →
              ∀ (q : Query K),
                abs o X φ m0 = Except.ok q →
                  ∃ f,
                    RunF F q.net.net (D EnvMode.ignore envs o X φ m0).trace q.init f ∧
                      V o.assumeNoReaping q.net q.prop f) ∧
          (∀ (mode : EnvMode),
              vacuityNote ∈ (D mode envs o X φ m0).notes → quiescenceProp φ = true ∧ NoRest o mode envs X = true) ∧
            ∀ (mode : EnvMode),
              mode.injects = true →
                envs ≠ [] →
                  quiescenceProp φ = true →
                    NoRest o mode envs X = true →
                      ((D mode envs o X φ m0).verdict = Verdict.violated ∨
                          ∃ meth, (D mode envs o X φ m0).verdict = Verdict.proven meth) →
                        vacuityNote ∈ (D mode envs o X φ m0).notes
-/
#guard_msgs in #print VER_006_verdict

/-- ✓ **The reference meets the verdict lines.** Example: on `env IN → T → OUT` with `IN`
registered, `Ignore` turns the dead-marking proof of `PlaceBound(OUT, 0)` into `Unknown`,
`Bounded(1)` from `{IN: 2}` refuses before any route, and `AlwaysAvailable` proves
`TerminatesAtSink({OUT})` vacuously with the note. -/
@[evidence holds VER_006_verdict]
theorem VER_006_verdict_reference {K : Type} [LinearOrder K] [Hashable K] :
    VER_006_verdict RefFire refSafetyViol ver006IgnoreAbs (refEnvVerify (K := K)) := by
  intro envs o X φ m0
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hne meth h
    simp only [refEnvVerify, envBase, hne, if_false] at h
    revert h
    cases (refVerify ver006IgnoreAbs o X φ m0).verdict <;> simp [ver006Downgrade]
  · intro k hk
    have hne : envs ≠ [] := by rintro rfl; simp [envPremiseOK] at hk
    simp [refEnvVerify, envBase, hne, hk]
  · intro hv hc q hq
    obtain ⟨-, -, -, -, h5, -⟩ := VER_003_reference (K := K) ver006IgnoreAbs o X φ m0
    obtain ⟨h5a, -⟩ := h5 q hq
    by_cases hne : envs = []
    · simp only [refEnvVerify, envBase, hne, if_true] at hv hc ⊢
      exact h5a hv hc
    · simp only [refEnvVerify, envBase, hne, if_false] at hv hc ⊢
      have hv' : (refVerify ver006IgnoreAbs o X φ m0).verdict = .violated := by
        revert hv
        cases (refVerify ver006IgnoreAbs o X φ m0).verdict <;> simp [ver006Downgrade]
      exact h5a hv' hc
  · intro mode h
    simp only [refEnvVerify] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      exact ⟨hc.1.1, hc.1.2⟩
    · simp at h
  · intro mode hinj hne hq hnr hdec
    have hpf : premiseFails mode envs X m0 = false := by
      cases mode with
      | bounded k =>
        cases hp : envPremiseOK k envs X m0
        · simp [refEnvVerify, envBase, hne, hp] at hdec
        · simp [premiseFails, hp]
      | always => rfl
      | arrivals _ _ => simp [EnvMode.injects] at hinj
      | ignore => simp [EnvMode.injects] at hinj
    simp [refEnvVerify, hq, hnr, hpf]

/-! ## The two premise checks agree -/

section PremiseLink

open Libpetri.Reference.Link

theorem ver006_mem_dedupAppend_left :
    ∀ (acc ds : List Deposit) (r : Deposit), r ∈ acc → r ∈ dedupAppend acc ds
  | _, [], _, h => h
  | acc, d :: ds, r, h => by
    unfold dedupAppend
    apply ver006_mem_dedupAppend_left
    split
    · exact h
    · exact List.mem_append_left _ h

theorem ver006_mem_dedupAppend :
    ∀ (acc ds : List Deposit) (r : Deposit), r ∈ dedupAppend acc ds → r ∈ acc ∨ r ∈ ds
  | _, [], _, h => Or.inl h
  | acc, d :: ds, r, h => by
    unfold dedupAppend at h
    rcases ver006_mem_dedupAppend _ ds r h with h | h
    · split at h
      · exact Or.inl h
      · rcases List.mem_append.mp h with h | h
        · exact Or.inl h
        · simp only [List.mem_singleton] at h
          subst h
          exact Or.inr List.mem_cons_self
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem ver006_branches_ne_nil : ∀ o : Reference.Out PlaceId, branches (toOutSpec o) ≠ []
  | .place _ => by simp [toOutSpec, branches]
  | .forward _ _ => by simp [toOutSpec, branches]
  | .and l r => by
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (ver006_branches_ne_nil l)
    obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ (ver006_branches_ne_nil r)
    apply List.ne_nil_of_mem (a := x ++ y)
    simp only [toOutSpec, branches, cross, List.mem_flatMap, List.mem_map]
    exact ⟨x, hx, y, hy, rfl⟩
  | .xor l _ => by
    simp only [toOutSpec, branches, ne_eq, List.append_eq_nil_iff, not_and]
    exact fun h => absurd h (ver006_branches_ne_nil l)
  | .timeout c => by simpa [toOutSpec, branches] using ver006_branches_ne_nil c

theorem ver006_branch_of_out :
    ∀ (o : Reference.Out PlaceId) (e : PlaceId), e ∈ Spec.outPlaces o →
      ∃ r ∈ branches (toOutSpec o), e ∈ r
  | .place p, e, h => ⟨[p], by simp [toOutSpec, branches], by simpa [Spec.outPlaces] using h⟩
  | .forward _ d, e, h => ⟨[d], by simp [toOutSpec, branches], by simpa [Spec.outPlaces] using h⟩
  | .and l r, e, h => by
    simp only [Spec.outPlaces, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨x, hx, hex⟩ := ver006_branch_of_out l e h
      obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ (ver006_branches_ne_nil r)
      refine ⟨x ++ y, ?_, List.mem_append_left _ hex⟩
      simp only [toOutSpec, branches, cross, List.mem_flatMap, List.mem_map]
      exact ⟨x, hx, y, hy, rfl⟩
    · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (ver006_branches_ne_nil l)
      obtain ⟨y, hy, hey⟩ := ver006_branch_of_out r e h
      refine ⟨x ++ y, ?_, List.mem_append_right _ hey⟩
      simp only [toOutSpec, branches, cross, List.mem_flatMap, List.mem_map]
      exact ⟨x, hx, y, hy, rfl⟩
  | .xor l r, e, h => by
    simp only [Spec.outPlaces, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨x, hx, hex⟩ := ver006_branch_of_out l e h
      exact ⟨x, by simp [toOutSpec, branches, hx], hex⟩
    · obtain ⟨x, hx, hex⟩ := ver006_branch_of_out r e h
      exact ⟨x, by simp [toOutSpec, branches, hx], hex⟩
  | .timeout c, e, h => by
    obtain ⟨x, hx, hex⟩ := ver006_branch_of_out c e (by simpa [Spec.outPlaces] using h)
    exact ⟨x, by simpa [toOutSpec, branches] using hx, hex⟩

theorem ver006_outPlaces_eq : ∀ o : Reference.Out PlaceId, Verifier.outPlaces o = Spec.outPlaces o
  | .place _ | .forward _ _ => rfl
  | .and l r | .xor l r => by
    simp [Verifier.outPlaces, Spec.outPlaces, ver006_outPlaces_eq l, ver006_outPlaces_eq r]
  | .timeout c => by simp [Verifier.outPlaces, Spec.outPlaces, ver006_outPlaces_eq c]

theorem ver006_branch_sub (o : Reference.Out PlaceId) :
    ∀ r ∈ branches (toOutSpec o), ∀ x ∈ r, x ∈ Spec.outPlaces o := by
  intro r hr x hx
  rw [branches_toOutSpec] at hr
  rw [← ver006_outPlaces_eq]
  exact Verifier.mem_outPlaces_branches o r hr x hx

theorem ver006_timeout_sub (c : PlaceId → Nat) :
    ∀ (o : Reference.Out PlaceId), ∀ r ∈ timeoutDeposits c (toOutSpec o), ∀ x ∈ r,
      x ∈ Spec.outPlaces o
  | .place p, r, hr, x, hx => by
    simp only [toOutSpec, timeoutDeposits, List.mem_singleton] at hr
    subst hr
    simpa [Spec.outPlaces] using hx
  | .forward s d, r, hr, x, hx => by
    simp only [toOutSpec, timeoutDeposits, List.mem_singleton] at hr
    subst hr
    simp only [List.mem_replicate] at hx
    simp [Spec.outPlaces, hx.2]
  | .and l r', r, hr, x, hx => by
    simp only [toOutSpec, timeoutDeposits, cross, List.mem_flatMap, List.mem_map] at hr
    obtain ⟨a, ha, b, hb, rfl⟩ := hr
    rcases List.mem_append.mp hx with h | h
    · simp [Spec.outPlaces, ver006_timeout_sub c l a ha x h]
    · simp [Spec.outPlaces, ver006_timeout_sub c r' b hb x h]
  | .xor l r', r, hr, x, hx => by
    simp only [toOutSpec, timeoutDeposits, List.mem_append] at hr
    rcases hr with h | h
    · simp [Spec.outPlaces, ver006_timeout_sub c l r h x hx]
    · simp [Spec.outPlaces, ver006_timeout_sub c r' r h x hx]
  | .timeout c', r, hr, x, hx => by
    have := ver006_timeout_sub c c' r (by simpa [toOutSpec, timeoutDeposits] using hr) x hx
    simpa [Spec.outPlaces] using this

theorem ver006_findTimeout_sub :
    ∀ (o : Reference.Out PlaceId) (c : OutSpec), findTimeout (toOutSpec o) = some c →
      ∃ o', c = toOutSpec o' ∧ ∀ x ∈ Spec.outPlaces o', x ∈ Spec.outPlaces o
  | .place _, c, h => by simp [toOutSpec, findTimeout] at h
  | .forward _ _, c, h => by simp [toOutSpec, findTimeout] at h
  | .timeout c', c, h => by
    simp only [toOutSpec, findTimeout, Option.some.injEq] at h
    exact ⟨c', h.symm, fun x hx => by simpa [Spec.outPlaces] using hx⟩
  | .and l r, c, h => by
    simp only [toOutSpec, findTimeout] at h
    cases hl : findTimeout (toOutSpec l) with
    | some c'' =>
      rw [hl] at h
      simp only [Option.some_or, Option.some.injEq] at h
      subst h
      obtain ⟨o', h1, h2⟩ := ver006_findTimeout_sub l _ hl
      exact ⟨o', h1, fun x hx => by simp [Spec.outPlaces, h2 x hx]⟩
    | none =>
      rw [hl] at h
      simp only [Option.none_or] at h
      obtain ⟨o', h1, h2⟩ := ver006_findTimeout_sub r _ h
      exact ⟨o', h1, fun x hx => by simp [Spec.outPlaces, h2 x hx]⟩
  | .xor l r, c, h => by
    simp only [toOutSpec, findTimeout] at h
    cases hl : findTimeout (toOutSpec l) with
    | some c'' =>
      rw [hl] at h
      simp only [Option.some_or, Option.some.injEq] at h
      subst h
      obtain ⟨o', h1, h2⟩ := ver006_findTimeout_sub l _ hl
      exact ⟨o', h1, fun x hx => by simp [Spec.outPlaces, h2 x hx]⟩
    | none =>
      rw [hl] at h
      simp only [Option.none_or] at h
      obtain ⟨o', h1, h2⟩ := ver006_findTimeout_sub r _ h
      exact ⟨o', h1, fun x hx => by simp [Spec.outPlaces, h2 x hx]⟩

/-- A transition's fixed rows deposit nothing into `e` exactly when its output spec does not
name `e`. -/
theorem ver006_rows_free (t : Transition) (o : Reference.Out PlaceId) (e : PlaceId) :
    (∀ r ∈ fixedRows t (toOutSpec o), r.count e = 0) ↔ e ∉ Spec.outPlaces o := by
  have hb : ∀ r ∈ branches (toOutSpec o), r ∈ fixedRows t (toOutSpec o) := by
    intro r hr
    unfold fixedRows
    split
    · exact hr
    · exact ver006_mem_dedupAppend_left _ _ _ hr
  constructor
  · intro h he
    obtain ⟨r, hr, her⟩ := ver006_branch_of_out o e he
    have := h r (hb r hr)
    exact absurd this (List.count_pos_iff.mpr her).ne'
  · intro he r hr
    apply List.count_eq_zero_of_not_mem
    intro her
    apply he
    unfold fixedRows at hr
    split at hr
    · exact ver006_branch_sub o r hr e her
    · rename_i c hc
      rcases ver006_mem_dedupAppend _ _ _ hr with h | h
      · exact ver006_branch_sub o r h e her
      · obtain ⟨o', rfl, hsub⟩ := ver006_findTimeout_sub o c hc
        exact hsub e (ver006_timeout_sub _ o' r h e her)

/-- ✓ **The premise check by name is the check over the flat rows.** On a net at flat place ids,
the check `VER_006_verdict` reads (`envPremiseOK`: the places each output spec names) and the
check `VER_006_premise` binds (`boundedPremiseOK`: the deposits of the flat rows) agree, from the
coloured marking with the same counts. Example: on `t0 : a → E`, `E` registered, both fail,
because `t0`'s output spec names `E` and its one flat row deposits a token there. -/
theorem envPremiseOK_flat (k : Nat) (envs : List PlaceId) (X : Reference.TimedNet PlaceId)
    (m0 : NMarking PlaceId) :
    envPremiseOK k envs X m0 =
      boundedPremiseOK k envs (flatRows (toSpecNet X.net)) (Reference.Link.lift m0.count) := by
  unfold envPremiseOK boundedPremiseOK
  congr 1
  · simp [Reference.Link.lift]
  · apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true, beq_iff_eq]
    refine forall_congr' fun e => imp_congr_right fun _ => ?_
    constructor
    · intro h tr htr
      simp only [flatRows, List.mem_flatMap, List.mem_map] at htr
      obtain ⟨tq, htq, r, hr, rfl⟩ := htr
      obtain ⟨t, ht, o, ho, rfl⟩ := mem_toSpecNet.mp htq
      have := h t ht
      rw [ho] at this
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at this
      exact (ver006_rows_free _ o e).mpr this r hr
    · intro h t ht
      cases ho : t.out with
      | none => rfl
      | some o =>
        simp only [Bool.not_eq_true', decide_eq_false_iff_not]
        refine (ver006_rows_free (toTransition t.core) o e).mp fun r hr => h (toTransition t.core, r) ?_
        simp only [flatRows, List.mem_flatMap, List.mem_map]
        exact ⟨_, mem_toSpecNet.mpr ⟨t, ht, o, ho, rfl⟩, r, hr, rfl⟩

/-- ✓ **Line 2's check is the premise block's check.** For every premise check meeting
`VER_006_premise`, the check `VER_006_verdict` reads by name gives the same answer on a net at
flat place ids as that check on the net's flat rows. Example: under `Bounded(1)` on `t0 : a → E`
with `E` registered, both refuse, since `t0` deposits into `E`. -/
theorem envPremiseOK_eq_premise {P : PremiseCheck} (h : VER_006_premise P) (k : Nat)
    (envs : List PlaceId) (X : Reference.TimedNet PlaceId) (m0 : NMarking PlaceId) :
    envPremiseOK k envs X m0 = P k envs (flatRows (toSpecNet X.net)) (Reference.Link.lift m0.count) := by
  rw [envPremiseOK_flat]
  exact Bool.eq_iff_iff.mpr ((VER_006_premise_reference _ _ _ _).trans (h _ _ _ _).symm)

end PremiseLink

/-! ## The requirement's net `env IN → T → OUT`, by name -/

/-- `T : IN → OUT` (`IN = 0`, `OUT = 1`), immediate. -/
def ver006T : Reference.Trans Nat :=
  { core := { name := "T", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 1) }

/-- The net `env IN → T → OUT`. -/
def ver006Net : Reference.Net Nat := { places := [0, 1], transitions := [ver006T] }

/-- The net, untimed. -/
def ver006X : Reference.TimedNet Nat := { net := ver006Net, timing := fun _ => .immediate, tol := 0 }

/-- The empty marking. -/
def ver006Empty : NMarking Nat := ⟨[], by decide, by decide⟩

/-- `{IN: 2}`. -/
def ver006In2 : NMarking Nat := ⟨[(0, 2)], by decide, by decide⟩

/-- ✓ **The verdicts on `env IN → T → OUT`.** Example: from the empty marking, without
injection `T` never fires, so `PlaceBound(OUT, 0)` holds on the dead initial marking: `Proven`
with no environment place registered, `Unknown` under `Ignore` with `IN` registered (the proof
would be vacuous). Under `Ignore` the empty marking is a rest that marks no sink, so
`TerminatesAtSink({OUT})` is `Violated` with the empty trace, a rest of the net while the
environment stays silent. Under `AlwaysAvailable`, `T`'s only input is on `IN`, so no marking can
be quiescent: the same property is `Proven` with the vacuity note. Under `Bounded(1)` from
`{IN: 2}` the premise fails: `Unknown`, route `Unavailable`, no note. Under `Bounded(0)`, `T`
demands more than the cap, so a rest exists and no note is given. -/
@[evidence nonvacuous VER_006_verdict]
theorem VER_006_verdict_nonvacuous :
    (refEnvVerify .ignore [] {} ver006X (.placeBound 1 0) ver006Empty).verdict =
      .proven "enumeration" ∧
    (refEnvVerify .ignore [0] {} ver006X (.placeBound 1 0) ver006Empty).verdict =
      .unknown ignoreReason ∧
    (refEnvVerify .ignore [0] {} ver006X (.terminatesAtSink [1]) ver006Empty).verdict =
      .violated ∧
    (refEnvVerify .ignore [0] {} ver006X (.terminatesAtSink [1]) ver006Empty).trace = [] ∧
    (refEnvVerify .ignore [0] {} ver006X (.terminatesAtSink [1]) ver006Empty).notes = [] ∧
    (refEnvVerify .always [0] {} ver006X (.terminatesAtSink [1]) ver006Empty).verdict =
      .proven "vacuous" ∧
    (refEnvVerify .always [0] {} ver006X (.terminatesAtSink [1]) ver006Empty).notes =
      [vacuityNote] ∧
    (refEnvVerify (.bounded 1) [0] {} ver006X (.terminatesAtSink [1]) ver006In2).verdict =
      .unknown premiseReason ∧
    (refEnvVerify (.bounded 1) [0] {} ver006X (.terminatesAtSink [1]) ver006In2).route =
      .unavailable ∧
    (refEnvVerify (.bounded 1) [0] {} ver006X (.terminatesAtSink [1]) ver006In2).notes = [] ∧
    (refEnvVerify (.bounded 0) [0] {} ver006X (.terminatesAtSink [1]) ver006Empty).notes = [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · rfl
  · rfl
  · decide
  · decide
  · decide

/-- **A Violated without injection is a run with injection.** Every marking the encoded net
reaches without the injection rules it also reaches with them, under `AlwaysAvailable`. So a
reachability-safety `Violated` under `Ignore` is a counterexample under injection too, while a
quiescence `Violated` need not be (`VER_006_verdict_nonvacuous`). Example: on `env IN → T → OUT`
the empty marking is reachable in both. -/
@[evidence cites "VER-006" "Only `Proven` is refused."]
theorem VER_006_frozen_in_injected {rows : Rows} {envs : List PlaceId} {a0 a : AMarking}
    (h : ReachAD rows a0 a) : ReachAE rows envs .always a0 a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail (Or.inl ⟨hs, rfl⟩)

/-- Mutant: `Ignore` without the downgrade, so the reference's `Proven` stands. -/
def ver006NoDowngrade : EnvDecider Nat := fun mode envs =>
  match mode with
  | .ignore => refVerify ver006IgnoreAbs
  | m => refEnvVerify m envs

/-- ✗ **No Proven under Ignore, on any route** (line 1). Example: on `env IN → T → OUT` from the
empty marking with `IN` registered, the dead-marking route proves `PlaceBound(OUT, 0)` only
because `T` never fires without injection; returning that `Proven` breaks the line. -/
@[evidence forbids VER_006_verdict]
theorem VER_006_verdict_forbids_noDowngrade :
    ¬ VER_006_verdict RefFire refSafetyViol ver006IgnoreAbs ver006NoDowngrade := by
  intro h
  have hv : (ver006NoDowngrade .ignore [0] {} ver006X (.placeBound 1 0) ver006Empty).verdict =
      .proven "enumeration" := by decide
  exact (h [0] {} ver006X (.placeBound 1 0) ver006Empty).1 (by simp) _ hv

/-- Mutant: `Bounded(k)` with no premise check. -/
def ver006NoPremise : EnvDecider Nat := fun mode envs o X φ m0 =>
  match mode with
  | .bounded k => injDecide (.bounded k) envs o X φ m0
  | m => refEnvVerify m envs o X φ m0

/-- ✗ **A failed premise is Unknown** (line 2). Example: on `env IN → T → OUT` from `{IN: 2}`
under `Bounded(1)`, the initial marking already holds more than the cap; a decider that skips the
check proves `TerminatesAtSink({OUT})` vacuously instead of refusing. -/
@[evidence forbids VER_006_verdict]
theorem VER_006_verdict_forbids_noPremise :
    ¬ VER_006_verdict RefFire refSafetyViol ver006IgnoreAbs ver006NoPremise := by
  intro h
  obtain ⟨⟨why, hw⟩, -⟩ :=
    (h [0] {} ver006X (.terminatesAtSink [1]) ver006In2).2.1 1 (by decide)
  have hv : (ver006NoPremise (.bounded 1) [0] {} ver006X (.terminatesAtSink [1]) ver006In2).verdict =
      .proven "vacuous" := by decide
  rw [hv] at hw
  exact Verdict.noConfusion hw

/-- Mutant: under `Ignore`, a confirmed `Violated` whose trace injects. -/
def ver006InjectTrace : EnvDecider Nat := fun mode envs o X φ m0 =>
  match mode with
  | .ignore => { verdict := .violated, route := .smt, trace := ["inject(0)"],
                 confirmed := some true, timing := some .untimedNet }
  | m => refEnvVerify m envs o X φ m0

/-- ✗ **Under Ignore the trace replays without injection** (line 3). Example: on
`env IN → T → OUT` a confirmed trace `inject(0)` names no transition of the net without
injection, so no firing sequence carries it. -/
@[evidence forbids VER_006_verdict]
theorem VER_006_verdict_forbids_injectTrace :
    ¬ VER_006_verdict RefFire refSafetyViol ver006IgnoreAbs ver006InjectTrace := by
  intro h
  obtain ⟨f, ⟨m1, ⟨t, ht, hn, -⟩, -⟩, -⟩ :=
    (h [0] {} ver006X (.placeBound 1 0) ver006Empty).2.2.1 rfl rfl _ rfl
  have ht' : t = ver006T := by
    simpa [ver006IgnoreAbs, inertAbs, refVerifiedNet, ver006X, ver006Net, ver006Empty,
      NMarking.places] using ht
  subst ht'
  simp [ver006T] at hn

/-- Mutant: the vacuity note on every result. -/
def ver006AlwaysNote : EnvDecider Nat := fun mode envs o X φ m0 =>
  { refEnvVerify mode envs o X φ m0 with notes := [vacuityNote] }

/-- ✗ **The note only where no marking can rest** (line 4). Example: `PlaceBound(OUT, 0)` is a
reachability property, which quiescence does not bear on; a note on it is false. -/
@[evidence forbids VER_006_verdict]
theorem VER_006_verdict_forbids_alwaysNote :
    ¬ VER_006_verdict RefFire refSafetyViol ver006IgnoreAbs ver006AlwaysNote := by
  intro h
  have := ((h [0] {} ver006X (.placeBound 1 0) ver006Empty).2.2.2.1 .always (by simp [ver006AlwaysNote])).1
  exact absurd this (by decide)

/-- Mutant: the reference without the vacuity note. -/
def ver006NoNote : EnvDecider Nat := fun mode envs o X φ m0 =>
  { refEnvVerify mode envs o X φ m0 with notes := [] }

/-- ✗ **A vacuous quiescence verdict carries the note** (line 5). Example: on
`env IN → T → OUT` under `AlwaysAvailable`, `TerminatesAtSink({OUT})` is `Proven` because no
marking can be quiescent; a `Proven` without the note reads as a guarantee about the net. -/
@[evidence forbids VER_006_verdict]
theorem VER_006_verdict_forbids_noNote :
    ¬ VER_006_verdict RefFire refSafetyViol ver006IgnoreAbs ver006NoNote := by
  intro h
  have := (h [0] {} ver006X (.terminatesAtSink [1]) ver006Empty).2.2.2.2 .always rfl (by simp)
    rfl (by decide) (Or.inr ⟨"vacuous", by decide⟩)
  simp [ver006NoNote] at this

/-! ## Consistency with VER-003 -/

section Joint

variable {K : Type} [LinearOrder K] [Hashable K]

/-- The injection step of an environment place `e` in the verified net under modelled
injection: no arc, one token into `e`, immediate. -/
def ver006InjT (e : K) : Reference.Trans K :=
  { core := { name := "inject", inputs := [], inhibitors := [], reads := [], resets := [] },
    out := some (.place e) }

/-- The verified query under modelled injection: VER-001's places, the net's transitions and one
injection step per registered environment place, the injection steps immediate. -/
def ver006InjQuery (envs : List K) (X : Reference.TimedNet K) (φ : VerProp K)
    (m0 : NMarking K) : Query K :=
  ⟨{ net := { places := (refVerifiedNet X.net m0).places,
              transitions := X.net.transitions ++ envs.map ver006InjT },
     timing := fun t => if t.core.name == "inject" && t.core.inputs.isEmpty then .immediate
                        else X.timing t,
     tol := X.tol }, φ, m0⟩

/-- **The verified-net function of each mode**: VER-001's net with no environment place
registered and under `Ignore` or `Arrivals`; with injection steps under `AlwaysAvailable` and a
passed `Bounded(k)`; none (the premise reason) after a failed `Bounded(k)` premise. -/
def ver006EnvAbs (mode : EnvMode) (envs : List K) : Abs K := fun o X φ m0 =>
  if envs = [] then ver006IgnoreAbs o X φ m0
  else match mode with
  | .always => .ok (ver006InjQuery envs X φ m0)
  | .bounded k =>
    if envPremiseOK k envs X m0 then .ok (ver006InjQuery envs X φ m0) else .error premiseReason
  | _ => ver006IgnoreAbs o X φ m0

omit [Hashable K] in
/-- On the verified net with injection steps no marking is quiescent in VER-002's sense, so no
quiescence property is violated there. -/
theorem ver006_inj_noViol {envs : List K} (hne : envs ≠ []) {X : Reference.TimedNet K}
    {φ : VerProp K} {m0 : NMarking K} (hq : quiescenceProp φ = true) (noReap : Bool)
    (f : K → Nat) :
    ¬ refSafetyViol noReap (ver006InjQuery envs X φ m0).net φ f := by
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil envs hne
  have hnq : ¬ VerQuiescent noReap (ver006InjQuery envs X φ m0).net f := by
    intro hQ
    have hmem : ver006InjT e ∈ (ver006InjQuery envs X φ m0).net.net.transitions := by
      simp only [ver006InjQuery, List.mem_append, List.mem_map]
      exact Or.inr ⟨e, he, rfl⟩
    have := (hQ _ hmem (by simp [Enabled, enabledNA, ver006InjT])).2
    simp [Reapable, TimingOf, ver006InjQuery, ver006InjT, Novel.TimedScg.Timing.reapable] at this
  cases φ with
  | deadlockFree s c => exact fun h => hnq h.1
  | terminatesAtSink s => exact fun h => hnq h.1
  | quiescentCount ps lo hi w => exact fun h => hnq h.1
  | mutualExclusion _ => simp [quiescenceProp] at hq
  | placeBound _ _ => simp [quiescenceProp] at hq
  | unreachable _ => simp [quiescenceProp] at hq

/-- ✓ **Every mode of the reference meets VER-003.** For each mode and registered environment
places, the reference environment-aware decider meets the verdict contract of [VER-003] for the
mode's verified-net function: VER-001's net under `Ignore`, `Arrivals` and with no environment
place, the net with one injection step per environment place under `AlwaysAvailable` and a
passed `Bounded(k)`. Example: on `env IN → T → OUT` under `AlwaysAvailable`, the vacuous `Proven`
of `TerminatesAtSink({OUT})` holds on the net with the injection step `inject`, which no marking
can disable. -/
theorem ver006_ver003 (mode : EnvMode) (envs : List K) :
    VER_003 RefFire refSafetyViol (ver006EnvAbs mode envs) (refEnvVerify mode envs) := by
  intro o X φ m0
  obtain ⟨l1, l2, l3, l4, l5, l9, l10, l11⟩ := VER_003_reference ver006IgnoreAbs o X φ m0
  by_cases hne : envs = []
  · have ha : ver006EnvAbs mode envs o X φ m0 = ver006IgnoreAbs o X φ m0 := by
      simp [ver006EnvAbs, hne]
    rw [ha]
    simp only [refEnvVerify, envBase, hne, if_true]
    exact ⟨l1, l2, l3, l4, l5, l9, l10, l11⟩
  · cases mode with
    | ignore =>
      have ha : ver006EnvAbs .ignore envs o X φ m0 = ver006IgnoreAbs o X φ m0 := by
        simp [ver006EnvAbs, hne]
      simp only [refEnvVerify, envBase, hne, if_false, ha]
      revert l1 l2 l3 l4 l5 l9 l10 l11
      generalize refVerify ver006IgnoreAbs o X φ m0 = r
      intro l1 l2 l3 l4 l5 l9 l10 l11
      cases hv : r.verdict with
      | proven meth =>
        simp only [hv, ver006Downgrade] at l1 l2 l3 l4 l5 l9 l10 l11 ⊢
        refine ⟨fun why h => by cases h; decide, by simp, fun _ => ⟨_, rfl⟩, fun _ _ => ⟨_, rfl⟩,
          fun q hq => ⟨by simp, by simp, by simp, (l5 q hq).2.2.2⟩, fun _ => l9 (by simp),
          by simp, by simp⟩
      | violated =>
        simp only [hv, ver006Downgrade] at l1 l2 l3 l4 l5 l9 l10 l11 ⊢
        exact ⟨l1, l2, l3, l4, l5, l9, l10, l11⟩
      | unknown why =>
        simp only [hv, ver006Downgrade] at l1 l2 l3 l4 l5 l9 l10 l11 ⊢
        exact ⟨l1, l2, l3, l4, l5, l9, l10, l11⟩
    | arrivals lo hi =>
      simp only [refEnvVerify, envBase, hne, if_false]
      refine ⟨fun why h => by cases h; decide, by simp, fun _ => ⟨_, rfl⟩, fun _ _ => ⟨_, rfl⟩,
        fun q _ => ⟨by simp, by simp, by simp, by simp⟩, by simp, by simp, by simp⟩
    | always =>
      have ha : ver006EnvAbs .always envs o X φ m0 = .ok (ver006InjQuery envs X φ m0) := by
        simp [ver006EnvAbs, hne]
      rw [ha]
      simp only [refEnvVerify, envBase, hne, if_false]
      unfold injDecide
      by_cases hu : Unresolved X φ m0
      · simp only [hu, if_true]
        refine ⟨fun why h => by cases h; decide, by simp, fun _ => ⟨_, rfl⟩, by simp,
          fun q _ => ⟨by simp, by simp, by simp, by simp⟩, by simp, by simp, by simp⟩
      · simp only [hu, if_false]
        by_cases hv : (quiescenceProp φ && NoRest o .always envs X) = true
        · simp only [hv, if_true]
          refine ⟨by simp, fun meth h => by cases h; decide, fun h => h.1.elim, by simp,
            fun q hq => ⟨by simp, by simp, ?_, by simp⟩, by simp, by simp, by simp⟩
          intro meth _ f _
          obtain rfl : ver006InjQuery envs X φ m0 = q := by simpa using hq
          simp only [Bool.and_eq_true] at hv
          exact ver006_inj_noViol hne hv.1 _ f
        · simp only [hv]
          refine ⟨fun why h => by cases h; decide, by simp, fun h => h.1.elim, by simp,
            fun q _ => ⟨by simp, by simp, by simp, by simp⟩, by simp, by simp, by simp⟩
    | bounded k =>
      by_cases hp : envPremiseOK k envs X m0 = true
      · have ha : ver006EnvAbs (.bounded k) envs o X φ m0 = .ok (ver006InjQuery envs X φ m0) := by
          simp [ver006EnvAbs, hne, hp]
        rw [ha]
        simp only [refEnvVerify, envBase, hne, if_false, hp]
        unfold injDecide
        by_cases hu : Unresolved X φ m0
        · simp only [hu, if_true]
          refine ⟨fun why h => by cases h; decide, by simp, fun _ => ⟨_, rfl⟩, by simp,
            fun q _ => ⟨by simp, by simp, by simp, by simp⟩, by simp, by simp, by simp⟩
        · simp only [hu, if_false]
          by_cases hv : (quiescenceProp φ && NoRest o (.bounded k) envs X) = true
          · simp only [hv, if_true]
            refine ⟨by simp, fun meth h => ?_, fun h => h.1.elim, by simp,
              fun q hq => ⟨by simp, by simp, ?_, by simp⟩, by simp, by simp, by simp⟩
            · simp only [Verdict.proven.injEq] at h
              rw [← h]; decide
            · intro meth _ f _
              obtain rfl : ver006InjQuery envs X φ m0 = q := by simpa using hq
              simp only [Bool.and_eq_true] at hv
              exact ver006_inj_noViol hne hv.1 _ f
          · simp only [hv]
            refine ⟨fun why h => by cases h; decide, by simp, fun h => h.1.elim, by simp,
              fun q _ => ⟨by simp, by simp, by simp, by simp⟩, by simp, by simp, by simp⟩
      · have ha : ver006EnvAbs (.bounded k) envs o X φ m0 = .error premiseReason := by
          simp [ver006EnvAbs, hne, hp]
        rw [ha]
        simp only [refEnvVerify, envBase, hne, hp, if_false]
        refine ⟨fun why h => by cases h; simp [premiseReason], by simp, fun _ => ⟨_, rfl⟩,
          fun _ _ => ⟨_, rfl⟩, fun q hq => by simp at hq, by simp, by simp, by simp⟩

omit [Hashable K] in
/-- Under `Ignore` the verified-net function is VER-001's, whatever is registered. -/
theorem ver006EnvAbs_ignore (envs : List K) : ver006EnvAbs .ignore envs = ver006IgnoreAbs (K := K) := by
  funext o X φ m0
  by_cases hne : envs = [] <;> simp [ver006EnvAbs, hne]

end Joint

/-- ✓ **One firing relation, one violation reading, one decider for CORE-022, VER-014, VER-002,
VER-003 and VER-006's verdicts.** Example: the reference firing `RefFire`, VER-014's rest set
with VER-002's reference violations, and `refEnvVerify` satisfy all of them at once: the verdict
lines of VER-006, and for every mode and registered environment places VER-003's contract for
that mode's verified net (VER-001's net under `Ignore`, the net with injection steps under
`AlwaysAvailable`). -/
@[evidence consistent CORE_022 VER_002 VER_003 VER_006_verdict VER_014]
theorem VER_006_verdict_joint {K : Type} [LinearOrder K] [Hashable K] :
    ∃ (F : FireRel K) (S : StrandRel K) (Vr : RestViolRel K) (V : SafetyViolRel K)
      (abs : Abs K) (envAbs : EnvMode → List K → Abs K) (D : EnvDecider K),
      CORE_022 F ∧ VER_014 S Vr ∧ VER_002 S V ∧ VER_006_verdict F V abs D ∧
      (∀ envs, envAbs .ignore envs = abs) ∧
      ∀ mode envs, VER_003 F V (envAbs mode envs) (D mode envs) :=
  ⟨RefFire, refStrand, refRestViol, refSafetyViol, ver006IgnoreAbs, ver006EnvAbs, refEnvVerify,
    CORE_022_reference, VER_014_reference, VER_002_reference, VER_006_verdict_reference,
    ver006EnvAbs_ignore, ver006_ver003⟩

end Libpetri.Spec
