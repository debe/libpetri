import Libpetri.Novel.ForwardDeposit
import Libpetri.Retrodict
import Mathlib.Logic.Relation

/-!
# Environment injection on both sides of Proposition 1 ([VER-006])

`Retrodict.lean` has the abstract side of injection (`ReachAInj`, `AlwaysAvailable` only) and
`ForwardDeposit.lean` its integer-post form (`ReachADInj`). Nothing connected either to the
executor. This module adds the concrete side and the `Bounded(k)` variant, and proves the
simulation the CHC route rests on.

**The encoding.** For a registered environment place `p` under `AlwaysAvailable` / `Bounded(k)`,
`encode_net` (`smt_encoder.rs`) emits one injection rule (`encode_injection_rule`,
`injection_conditions`): `[m_p < k] ∧ m'_p = m_p + 1 ∧ m'_q = m_q (q ≠ p)`. Under `Bounded(k)` it
also conjoins `m'_e ≤ k` for **every** environment place `e` to **every** transition rule
(`env_bound_conditions`, "legacy post-cap"), and the certificate check's step relation
(`encode_step_relation_smt2`) and the abstract replay (`within_env_bounds`) repeat it. That is
`StepAE`: a row step whose successor passes the post-cap, or one admitted injection.

`StepAE` is the rule body **without its strengthening conjuncts**. `encode_net` builds, and
`encode_transition_rule` conjoins to every transition rule, the P-invariant equalities and, with
[VER-016], the firing-counter update, the counters' non-negativity and the state-equation rows
(`invariant_conditions`, `counter_conditions`, `state_equation_conditions`);
`encode_step_relation_smt2` carries the counter conditions too. They are abstracted away here.
`Strengthening.lean`, `StateEquation.lean` and `Novel/Certificate.lean` prove that they remove
no reachable marking; this module does not re-prove that with the injection rules present, and
its theorems are about the unstrengthened relation.

**The executor.** `inject()` appends one token to an environment place at any time; the
environment the mode describes does so always (`AlwaysAvailable`) or while fewer than `k` tokens
are resident (`Bounded(k)`, [VER-006]: "injection refills the place up to k"). Firings are
`ForwardDeposit.StepCR` (a row's counts deposited), or `StepCD` at the spec level. That is
`StepCE` / `StepCDE`.

Results:
* `reachAE_always_iff` / `reachAE_always_unit_iff`: under `AlwaysAvailable` the encoded relation
  is `ForwardDeposit.ReachADInj`, and on unit rows `Retrodict.ReachAInj`.
* `proposition_one_inj` (**R5, concrete side**): `ReachCE ⊆ ReachAE` under `AlwaysAvailable`,
  with only the consume-all-unguarded premise of Proposition 1; `proposition_one_inj_spec` at the
  spec level (timeout outcomes included).
* `proposition_one_inj_bounded`: the same under `Bounded(k)`, **given two premises about the
  net**: no row deposits into an environment place (`NoEnvDeposit`) and the initial marking holds
  at most `k` on each (`EnvCappedC`). Under them the executor never exceeds `k` resident, so the
  post-cap removes no executor step.
* `reachAE_capped` / `bounded_demand_gate` (**Bounded(k) guard soundness**, [VER-006] AC3): the
  encoding never holds more than `k` on an environment place, and under the two premises no
  executor-reachable marking enables a transition that takes more than `k` from one. Without
  them the executor can hold more than `k` and fire such a transition, so the graph routes'
  `required > k` gate is wrong too (`Supplied.lean`, `supplied_bounded_*`).
* `bounded_initial_overflow_wrong_proven` / `bounded_producer_overflow_wrong_proven` (a
  divergence of the encoding, by `decide` plus a frozen-set induction; the verifier no longer
  reaches either net, `Premise.lean`): each premise is necessary, and each
  witness breaks only its own (the first keeps `NoEnvDeposit`, the second a capped seed). With
  `M0(E) = 2 > k = 1` the post-cap blocks *every* transition, one that never touches `E`
  included, and `PlaceBound(b, 0)` comes back `Proven` although the executor puts a token on `b`
  in one firing with no injection. With a transition that outputs into `E`, `PlaceBound(E, 1)`
  is `Proven` although two firings put two tokens there. Reproduced on the Rust before the
  check; `verify_net` now refuses both nets with `Unknown` (`bounded_premise_violation`,
  `Premise.bounded_initial_overflow_refused`, `bounded_producer_overflow_refused`).
* `retrodict_98b9297`: the pre-fix encoding (no injection rule) proves `PlaceBound(out, 0)` on
  `env → consume → out`, while the executor reaches `out = 1` by one `inject()` and one firing,
  and `proposition_one_inj` places that run in the fixed encoding.

Out of scope: the name → index seam (every `PlaceId` is indexed here; `resolve_env_injection`
silently drops a registered name the flat index lacks, which `Seam/` would have to cover), timing,
colours beyond counts, and `Ignore` (no injection; refused by [VER-006] AC4).
-/

namespace Libpetri.Novel.EnvSemantics

open Libpetri Libpetri.Novel.ForwardDeposit

/-- A flat net as the flattener writes it: one row per way a firing can end. -/
abbrev Rows := List (Transition × Deposit)

/-- The modelled environment ([VER-006]): `AlwaysAvailable` or `Bounded(k)`. `Arrivals` is a net
rewrite (`Arrivals.lean`), `Ignore` models nothing. Models `SmtVerifier::env_injection`: `None`
for `AlwaysAvailable`, `Some(k)` for `Bounded(k)`. -/
inductive InjMode where
  | always
  | bounded (k : Nat)
  deriving DecidableEq, Repr

namespace InjMode

/-- The injection rule's guard (`injection_conditions`: `(< m_pid k)` when bounded). -/
def admits : InjMode → Nat → Bool
  | always, _ => true
  | bounded k, n => decide (n < k)

/-- The post-cap `env_bound_conditions` conjoins to every transition rule: `(<= m'_e k)` for
every registered environment place `e` under `Bounded(k)`, nothing otherwise. -/
def capped (mode : InjMode) (envs : List PlaceId) (a : AMarking) : Bool :=
  match mode with
  | always => true
  | bounded k => envs.all fun e => decide (a e ≤ k)

end InjMode

theorem capped_bounded_iff {k : Nat} {envs : List PlaceId} {a : AMarking} :
    (InjMode.bounded k).capped envs a = true ↔ ∀ e ∈ envs, a e ≤ k := by
  simp [InjMode.capped, List.all_eq_true]

/-- One injection into `p` (`m'_p = m_p + 1`, every other column copied). -/
def injA (a : AMarking) (p : PlaceId) : AMarking := fun q => if q == p then a q + 1 else a q

/-- **One step of the encoded open system.** A row fires and its successor passes the post-cap,
or an admitted injection. It models the marking columns of two Rust relations, and omits
different conjuncts from each.

* The CHC rule set of `encode_net`: `encode_transition_rule` (`firing_conditions` plus
  `env_bound_conditions`) and `encode_injection_rule`. `StepAE` leaves out the strengthening
  conjuncts `encode_net` hands to every transition rule: the P-invariant equalities
  (`invariant_conditions`) and, with [VER-016], the firing-counter update and non-negativity
  (`counter_conditions`) and the state-equation rows (`state_equation_conditions`). It also
  drops the counter columns of `Reachable`, which the injection rule copies unchanged.
* The certificate check's step relation `encode_step_relation_smt2`. That relation has no
  P-invariant conjunct and no state-equation row (the certificate candidate carries them), so
  here `StepAE` leaves out only the counter update and non-negativity.

`firing_conditions`' `m' ≥ 0` holds on `Nat` and is not written. `Strengthening.lean`,
`StateEquation.lean` and `Novel/Certificate.lean` show the strengthening conjuncts remove no
reachable marking of the net without injection rules. -/
def StepAE (rows : Rows) (envs : List PlaceId) (mode : InjMode) (a a' : AMarking) : Prop :=
  (StepAD rows a a' ∧ mode.capped envs a' = true) ∨
    ∃ p ∈ envs, mode.admits (a p) = true ∧ a' = injA a p

/-- `R(N̂)` with the environment rules: the least fixpoint `Reachable` of the CHC system. -/
def ReachAE (rows : Rows) (envs : List PlaceId) (mode : InjMode) (a0 : AMarking) :
    AMarking → Prop :=
  Relation.ReflTransGen (StepAE rows envs mode) a0

/-! ## `AlwaysAvailable` is the existing injected relation -/

theorem stepAE_always (rows : Rows) (envs : List PlaceId) :
    StepAE rows envs .always = StepADInj rows envs := by
  funext a a'
  apply propext
  simp only [StepAE, StepADInj, InjMode.capped, InjMode.admits, and_true, true_and]
  rfl

/-- Under `AlwaysAvailable` the encoded relation is `ForwardDeposit.ReachADInj`. -/
theorem reachAE_always_iff (rows : Rows) (envs : List PlaceId) (a0 a : AMarking) :
    ReachAE rows envs .always a0 a ↔ ReachADInj rows envs a0 a := by
  unfold ReachAE ReachADInj
  rw [stepAE_always]

/-- On duplicate-free rows (every action branch, [IO-011]) a deposit-row step is `fireA`'s. -/
theorem stepAD_iff_stepARel {net : FlatNet} (h : ∀ ft ∈ net, ft.2.Nodup) (a a' : AMarking) :
    StepAD net a a' ↔ StepARel net a a' := by
  unfold StepAD StepARel
  constructor
  · rintro ⟨ft, hm, he, rfl⟩
    exact ⟨ft, hm, he, fireAD_eq_fireA (h ft hm) a ft.1⟩
  · rintro ⟨ft, hm, he, rfl⟩
    exact ⟨ft, hm, he, (fireAD_eq_fireA (h ft hm) a ft.1).symm⟩

/-- On unit rows the encoded `AlwaysAvailable` relation is `Retrodict.lean`'s `ReachAInj`. -/
theorem reachAE_always_unit_iff {net : FlatNet} (h : ∀ ft ∈ net, ft.2.Nodup)
    (envs : List PlaceId) (a0 a : AMarking) :
    ReachAE net envs .always a0 a ↔ ReachAInj net envs a0 a := by
  have hs : StepAE net envs .always = StepAInjRel net envs := by
    funext x y
    apply propext
    rw [stepAE_always]
    unfold StepADInj StepAInjRel
    rw [stepAD_iff_stepARel h]
  unfold ReachAE ReachAInj
  rw [hs]

/-! ## The encoding's own cap -/

theorem capped_injA {mode : InjMode} {envs : List PlaceId} {a : AMarking} {p : PlaceId}
    (hc : mode.capped envs a = true) (hadm : mode.admits (a p) = true) :
    mode.capped envs (injA a p) = true := by
  cases mode with
  | always => rfl
  | bounded k =>
    rw [capped_bounded_iff] at hc ⊢
    simp only [InjMode.admits, decide_eq_true_eq] at hadm
    intro e he
    unfold injA
    by_cases hep : e = p
    · subst hep; simp; omega
    · simp [hep, hc e he]

/-- **The encoding never holds more than `k` on an environment place** once the seed does: every
transition rule carries the post-cap and every injection its guard. -/
theorem reachAE_capped {rows : Rows} {envs : List PlaceId} {mode : InjMode} {a0 a : AMarking}
    (h0 : mode.capped envs a0 = true) (h : ReachAE rows envs mode a0 a) :
    mode.capped envs a = true := by
  induction h with
  | refl => exact h0
  | tail _ hs ih =>
    rcases hs with ⟨_, hc⟩ | ⟨p, _, hadm, rfl⟩
    · exact hc
    · exact capped_injA ih hadm

/-- `Bounded(k)`: every encoded reachable marking holds at most `k` on each environment place. -/
theorem reachAE_bounded_le {rows : Rows} {envs : List PlaceId} {k : Nat} {a0 a : AMarking}
    (h0 : ∀ e ∈ envs, a0 e ≤ k) (h : ReachAE rows envs (.bounded k) a0 a) : ∀ e ∈ envs, a e ≤ k :=
  capped_bounded_iff.mp (reachAE_capped (capped_bounded_iff.mpr h0) h)

/-! ## The executor with an environment -/

/-- The executor's `inject()`: one token of colour `c` appended to `p`. -/
def injC (m : CMarking) (p : PlaceId) (c : Colour) : CMarking :=
  fun q => if q == p then m q ++ [c] else m q

theorem alpha_injC (m : CMarking) (p : PlaceId) (c : Colour) :
    alpha (injC m p c) = injA (alpha m) p := by
  funext q
  unfold alpha injC injA
  by_cases h : q = p
  · subst h; simp
  · simp [h]

/-- **One concrete step of the open system**: the executor fires a row (`StepCR`), or the
environment the mode describes injects one token (always, or while fewer than `k` are
resident). -/
def StepCE (rows : Rows) (envs : List PlaceId) (mode : InjMode) (m m' : CMarking) : Prop :=
  StepCR rows m m' ∨ ∃ p ∈ envs, mode.admits (m p).length = true ∧ ∃ c, m' = injC m p c

def ReachCE (rows : Rows) (envs : List PlaceId) (mode : InjMode) (m0 : CMarking) :
    CMarking → Prop :=
  Relation.ReflTransGen (StepCE rows envs mode) m0

/-- The spec-level concrete step: a firing ends one of the ways its output spec offers
([IO-013]–[IO-016], `ForwardDeposit.StepCD`), or an injection. -/
def StepCDE (net : SpecNet) (envs : List PlaceId) (mode : InjMode) (m m' : CMarking) : Prop :=
  StepCD net m m' ∨ ∃ p ∈ envs, mode.admits (m p).length = true ∧ ∃ c, m' = injC m p c

theorem stepCDE_stepCE {net : SpecNet} {envs : List PlaceId} {mode : InjMode}
    (hFwd : ∀ to ∈ net, FixedForwards to.1 to.2) {m m' : CMarking}
    (h : StepCDE net envs mode m m') : StepCE (flatRows net) envs mode m m' := by
  rcases h with h | h
  · exact Or.inl (stepCD_stepCR hFwd h)
  · exact Or.inr h

/-! ## Proposition 1 with injection -/

/-- **Premise of the `Bounded(k)` simulation: no row deposits into an environment place.** -/
def NoEnvDeposit (rows : Rows) (envs : List PlaceId) : Prop :=
  ∀ tr ∈ rows, ∀ e ∈ envs, tr.2.count e = 0

/-- A firing whose deposit misses `p` never raises `p`. -/
theorem alphaFireC_le_of_count_zero (m : CMarking) (t : Transition) (d : Deposit) {p : PlaceId}
    (h : d.count p = 0) : alphaFireC m t (fun q => d.count q) p ≤ (m p).length := by
  unfold alphaFireC
  simp only [h]
  split <;> omega

theorem fireAD_le_of_count_zero (a : AMarking) (t : Transition) (d : Deposit) {p : PlaceId}
    (h : d.count p = 0) : fireAD a t d p ≤ a p := by
  unfold fireAD
  rw [h]
  split
  · omega
  · split <;> omega

/-- **Proposition 1 with injection, any mode.** A concrete open run is a run of the encoded open
system, and stays under the cap, when the seed is capped and (for `Bounded(k)`) no row deposits
into an environment place. -/
theorem proposition_one_inj_mode {rows : Rows} {envs : List PlaceId} {mode : InjMode}
    (hG : ∀ tr ∈ rows, GuardFreeConsumeAll tr.1)
    (hDep : mode = .always ∨ NoEnvDeposit rows envs) {m0 m : CMarking}
    (hCap0 : mode.capped envs (alpha m0) = true) (h : ReachCE rows envs mode m0 m) :
    ReachAE rows envs mode (alpha m0) (alpha m) ∧ mode.capped envs (alpha m) = true := by
  induction h with
  | refl => exact ⟨Relation.ReflTransGen.refl, hCap0⟩
  | @tail m1 m2 _ hs ih =>
    obtain ⟨ihR, ihC⟩ := ih
    rcases hs with hs | ⟨p, hp, hadm, c, rfl⟩
    · have hA := stepCR_simulated hG hs
      have hC : mode.capped envs (alpha m2) = true := by
        cases mode with
        | always => rfl
        | bounded k =>
          have hD : NoEnvDeposit rows envs := by
            rcases hDep with h | h
            · exact absurd h (by simp)
            · exact h
          obtain ⟨tr, hmem, _, hEff⟩ := hs
          rw [capped_bounded_iff] at ihC ⊢
          intro e he
          have h1 : alpha m2 e = alphaFireC m1 tr.1 (fun q => tr.2.count q) e := by rw [hEff]
          have h2 := alphaFireC_le_of_count_zero m1 tr.1 tr.2 (hD tr hmem e he)
          have h3 := ihC e he
          simp only [alpha] at h1 h3 ⊢
          omega
      exact ⟨ihR.tail (Or.inl ⟨hA, hC⟩), hC⟩
    · rw [alpha_injC]
      have hadm' : mode.admits (alpha m1 p) = true := hadm
      exact ⟨ihR.tail (Or.inr ⟨p, hp, hadm', rfl⟩), capped_injA ihC hadm'⟩

/-- **Proposition 1 with injection ([VER-006], `AlwaysAvailable`).** `α(R(N, env)) ⊆ R(N̂, inj)`:
every marking the executor reaches under an always-available environment is reachable in the
encoded system. The only premise is Proposition 1's own (consume-all arcs unguarded). -/
theorem proposition_one_inj {rows : Rows} {envs : List PlaceId}
    (hG : ∀ tr ∈ rows, GuardFreeConsumeAll tr.1) {m0 m : CMarking}
    (h : ReachCE rows envs .always m0 m) :
    ReachAE rows envs .always (alpha m0) (alpha m) :=
  (proposition_one_inj_mode hG (Or.inl rfl) rfl h).1

/-- `proposition_one_inj` at the spec level: every firing ends one of the ways its spec offers,
timeout forwards from `One` / `Exactly` inputs included, and the encoding reads `flatRows`. -/
theorem proposition_one_inj_spec {net : SpecNet} {envs : List PlaceId}
    (hWF : ∀ to ∈ net, GuardFreeConsumeAll to.1 ∧ FixedForwards to.1 to.2) {m0 m : CMarking}
    (h : Relation.ReflTransGen (StepCDE net envs .always) m0 m) :
    ReachAE (flatRows net) envs .always (alpha m0) (alpha m) :=
  proposition_one_inj (flatRows_guardFree fun to h => (hWF to h).1)
    (Relation.ReflTransGen.lift id
      (fun _ _ hs => stepCDE_stepCE (fun to h => (hWF to h).2) hs) m0 m h)

/-- The initial marking holds at most `k` on every environment place. -/
def EnvCappedC (k : Nat) (envs : List PlaceId) (m : CMarking) : Prop :=
  ∀ e ∈ envs, (m e).length ≤ k

/-- **Proposition 1 with injection, `Bounded(k)`**, under the two premises the encoder does not
check (`verify_net` does, before any route: `Premise.bounded_checked_sound`): no row deposits into an environment place, and `M0` holds at most `k` on each. The
executor then never exceeds `k` resident (the second conjunct), so the post-cap cuts no concrete
step. `bounded_*_wrong_proven` below show neither premise can be dropped. -/
theorem proposition_one_inj_bounded {rows : Rows} {envs : List PlaceId} {k : Nat}
    (hG : ∀ tr ∈ rows, GuardFreeConsumeAll tr.1) (hDep : NoEnvDeposit rows envs)
    {m0 m : CMarking} (hCap0 : EnvCappedC k envs m0) (h : ReachCE rows envs (.bounded k) m0 m) :
    ReachAE rows envs (.bounded k) (alpha m0) (alpha m) ∧ EnvCappedC k envs m := by
  obtain ⟨hR, hC⟩ := proposition_one_inj_mode hG (Or.inr hDep) (capped_bounded_iff.mpr hCap0) h
  exact ⟨hR, capped_bounded_iff.mp hC⟩

/-- **[VER-006] AC3 for the executor.** Under the same two premises, no reachable marking
enables a transition that takes more than `k` tokens from an environment place in one firing.
The encoding satisfies it outright (`bounded_demand_gate_encoded`); `check_place_enabled`
(`state_class_graph.rs`) and `encode_quiescent`'s `permanently_disabled` test it as
`required > k`, whatever the place holds. That test agrees with the executor **only under these
two premises**, which no route checks and `verify_net` now checks before any route runs
(`Premise.lean`): with a deposit into the environment place or `M0` above
`k` the executor fires such a transition, and the graph routes return a wrong `Proven`
(`supplied_bounded_deposit_wrong_proven`, `supplied_bounded_initial_wrong_proven`) or a spurious
deadlock (`quiescence_bounded_initial_spurious`). -/
theorem bounded_demand_gate {rows : Rows} {envs : List PlaceId} {k : Nat}
    (hG : ∀ tr ∈ rows, GuardFreeConsumeAll tr.1) (hDep : NoEnvDeposit rows envs)
    {m0 m : CMarking} (hCap0 : EnvCappedC k envs m0) (h : ReachCE rows envs (.bounded k) m0 m)
    (t : Transition) {s : InSpec} (hs : s ∈ t.inputs) (he : s.place ∈ envs)
    (hk : k < s.card.required) : enabledC m t = false := by
  have hcap := (proposition_one_inj_bounded hG hDep hCap0 h).2 s.place he
  cases hen : enabledC m t with
  | false => rfl
  | true =>
    unfold enabledC at hen
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hen
    have h1 := hen.1.1 s hs
    have h2 := matchCount_le m s
    omega

theorem bounded_demand_gate_encoded {rows : Rows} {envs : List PlaceId} {k : Nat}
    {a0 a : AMarking} (h0 : ∀ e ∈ envs, a0 e ≤ k) (h : ReachAE rows envs (.bounded k) a0 a)
    (t : Transition) {s : InSpec} (hs : s ∈ t.inputs) (he : s.place ∈ envs)
    (hk : k < s.card.required) : enabledA a t = false := by
  have hcap := reachAE_bounded_le h0 h s.place he
  cases hen : enabledA a t with
  | false => rfl
  | true =>
    unfold enabledA at hen
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hen
    have := hen.1.1 s hs
    omega

/-! ## The post-cap against the executor: both premises are necessary -/

section Overflow

/-- `t : one(a) → b`, places `a = 0`, `b = 1`; the environment place `E = 2` is on no arc of it. -/
def tAB : Transition :=
  { name := "t"
  , inputs := [{ place := 0, card := .one, guard := none }]
  , inhibitors := [], reads := [], resets := [] }

def rowsAB : Rows := [(tAB, [1])]

/-- `M0 = {a: 1, E: 2}`, above `Bounded(1)`'s cap on `E`. -/
def m0Over : CMarking := fun p => if p == 0 then [0] else if p == 2 then [0, 0] else []

/-- After one firing of `t`: `{b: 1, E: 2}`. -/
def m1Over : CMarking := fun p => if p == 1 then [0] else if p == 2 then [0, 0] else []

theorem over_step : StepCR rowsAB m0Over m1Over := by
  refine ⟨(tAB, [1]), by simp [rowsAB], by decide, ?_⟩
  funext p
  simp only [alpha, alphaFireC, m0Over, m1Over, consumedAt, specAt, tAB]
  rcases p with _ | _ | _ | p <;> simp [consumeCount, Card.consumesAll, Card.required]

/-- The encoded system from `α(M0)` never leaves it: the post-cap `m'_E ≤ 1` fails for every row
(`E` stays at 2), and the injection guard `m_E < 1` fails. -/
theorem over_frozen {a : AMarking}
    (h : ReachAE rowsAB [2] (.bounded 1) (alpha m0Over) a) : a = alpha m0Over := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    subst ih
    rcases hs with ⟨⟨tr, hm, _, rfl⟩, hc⟩ | ⟨p, hp, hadm, rfl⟩
    · simp only [rowsAB, List.mem_singleton] at hm
      subst hm
      exact absurd hc (by decide)
    · simp only [List.mem_singleton] at hp
      subst hp
      exact absurd hadm (by decide)

/-- **Live divergence: an initial marking above `k` freezes the encoding.** Under `Bounded(1)`
with `M0(E) = 2`, the executor fires `t` (which never touches `E`) and puts a token on `b` with
no injection at all, while every encoded reachable marking has `b = 0`: `PlaceBound(b, 0)` is
`Proven`. `smt_verifier.rs` returns exactly that (IC3/PDR) at every enumeration budget. Only
the capped seed fails: no row deposits into `E`. -/
theorem bounded_initial_overflow_wrong_proven :
    NoEnvDeposit rowsAB [2] ∧ ¬ EnvCappedC 1 [2] m0Over ∧
    (∃ m, ReachCE rowsAB [2] (.bounded 1) m0Over m ∧ (m 1).length = 1) ∧
    ∀ a, ReachAE rowsAB [2] (.bounded 1) (alpha m0Over) a → a 1 = 0 := by
  refine ⟨?_, fun h => absurd (h 2 (by simp)) (by decide), ⟨m1Over, Relation.ReflTransGen.single
    (show StepCE rowsAB [2] (.bounded 1) m0Over m1Over from Or.inl over_step), by decide⟩, ?_⟩
  · intro tr htr e he
    simp only [rowsAB, List.mem_singleton] at htr he
    subst htr he
    decide
  intro a h
  rw [over_frozen h]
  decide

/-- `t : one(a) → E`, places `a = 0`, `E = 1`: the net itself produces into its environment
place. -/
def tAE : Transition :=
  { name := "t"
  , inputs := [{ place := 0, card := .one, guard := none }]
  , inhibitors := [], reads := [], resets := [] }

def rowsAE : Rows := [(tAE, [1])]

def m0Prod : CMarking := fun p => if p == 0 then [0, 0] else []
def m1Prod : CMarking := fun p => if p == 0 then [0] else if p == 1 then [0] else []
def m2Prod : CMarking := fun p => if p == 1 then [0, 0] else []

theorem prod_step1 : StepCR rowsAE m0Prod m1Prod := by
  refine ⟨(tAE, [1]), by simp [rowsAE], by decide, ?_⟩
  funext p
  simp only [alpha, alphaFireC, m0Prod, m1Prod, consumedAt, specAt, tAE]
  rcases p with _ | _ | p <;> simp [consumeCount, Card.consumesAll, Card.required]

theorem prod_step2 : StepCR rowsAE m1Prod m2Prod := by
  refine ⟨(tAE, [1]), by simp [rowsAE], by decide, ?_⟩
  funext p
  simp only [alpha, alphaFireC, m1Prod, m2Prod, consumedAt, specAt, tAE]
  rcases p with _ | _ | p <;> simp [consumeCount, Card.consumesAll, Card.required]

/-- **Live divergence: a producing transition is cut by the post-cap.** Under `Bounded(1)` the
executor fires `t` twice and holds two tokens on `E` (the environment injected nothing), while
the encoding caps `E` at 1 on every reachable marking: `PlaceBound(E, 1)` is `Proven`. Only
`NoEnvDeposit` fails: the seed is capped (`E = 0`). -/
theorem bounded_producer_overflow_wrong_proven :
    EnvCappedC 1 [1] m0Prod ∧ ¬ NoEnvDeposit rowsAE [1] ∧
    (∃ m, ReachCE rowsAE [1] (.bounded 1) m0Prod m ∧ (m 1).length = 2) ∧
    ∀ a, ReachAE rowsAE [1] (.bounded 1) (alpha m0Prod) a → a 1 ≤ 1 := by
  refine ⟨?_, fun h => absurd (h (tAE, [1]) (by simp [rowsAE]) 1 (by simp)) (by decide),
    ⟨m2Prod, ?_, by decide⟩, ?_⟩
  · intro e he
    simp only [List.mem_singleton] at he
    subst he
    decide
  · exact (Relation.ReflTransGen.single
      (show StepCE rowsAE [1] (.bounded 1) m0Prod m1Prod from Or.inl prod_step1)).tail
      (show StepCE rowsAE [1] (.bounded 1) m1Prod m2Prod from Or.inl prod_step2)
  · intro a h
    exact reachAE_bounded_le (by decide) h 1 (by simp)

end Overflow

/-! ## Retrodiction of `98b9297`, concrete side -/

section Retro98

/-- The executor's run on `Retrodict.netEnv` (`env → consume → out`) from the empty marking: one
`inject()` into the environment place, then one firing of `consume`. -/
def mInj : CMarking := injC (fun _ => []) envPlace 0
def mOut : CMarking := fun p => if p == outPlace then [0] else []

theorem retro_fire : StepCR netEnv mInj mOut := by
  refine ⟨(tConsume, [outPlace]), by simp [netEnv], by decide, ?_⟩
  funext p
  simp only [alpha, alphaFireC, mInj, mOut, injC, consumedAt, specAt, tConsume, envPlace,
    outPlace]
  rcases p with _ | _ | p <;> simp [consumeCount, Card.consumesAll, Card.required]

/-- **Retrodiction of `98b9297`, both sides.** Without the injection rule the encoding proves
`PlaceBound(out, 0)` (`Retrodict.false_proven_without_injection`), while the executor reaches
`out = 1`; with the rule the executor's run is a run of the encoding (`proposition_one_inj`), so
the fixed encoding reaches the violation. -/
theorem retrodict_98b9297 :
    (∀ a, ReachA netEnv m0A a → a outPlace = 0) ∧
    ∃ m, ReachCE netEnv [envPlace] .always (fun _ => []) m ∧ (m outPlace).length = 1 ∧
      ReachAE netEnv [envPlace] .always m0A (alpha m) := by
  have hrun : ReachCE netEnv [envPlace] .always (fun _ => []) mOut :=
    (Relation.ReflTransGen.single
      (show StepCE netEnv [envPlace] .always (fun _ => []) mInj from
        Or.inr ⟨envPlace, by simp, rfl, 0, rfl⟩)).tail
      (show StepCE netEnv [envPlace] .always mInj mOut from Or.inl retro_fire)
  refine ⟨false_proven_without_injection, mOut, hrun, by decide, ?_⟩
  have hG : ∀ tr ∈ netEnv, GuardFreeConsumeAll tr.1 := by
    intro tr htr s hs hca
    simp only [netEnv, List.mem_singleton] at htr
    subst htr
    simp only [tConsume, List.mem_singleton] at hs
    subst hs
    exact absurd hca (by decide)
  exact proposition_one_inj hG hrun

end Retro98

end Libpetri.Novel.EnvSemantics
