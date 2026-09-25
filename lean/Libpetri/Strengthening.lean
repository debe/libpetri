/-
# Verifier-side strengthening: when conjoining a P-invariant is sound

All three language verifiers conjoin every computed P-invariant `y·M = y·M₀`
into the CHC transition-rule *bodies* (`invariant_conditions`,
`smt_encoder.rs:406-429`, heading the `strengthening` list `encode_net` builds
at `:157` and `encode_transition_rule` splices at `:502`; the
TypeScript and Java encoders mirror it). With `EncodeOptions::state_equation`
([VER-016]) that list also carries the firing-counter update and the
state-equation rows, which `StateEquation.lean` models; this file models the
options-off path. A
conjunct in a rule body does not annotate the encoding — it *removes*
successors from the least fixpoint. A wrong invariant therefore shrinks
`Reachable` below the true reachable set and can certify a false `Proven`,
the failure mode this development exists to close.

The C2 runtime gate (`validate_invariants_exact`, `p_invariant.rs:247-378`,
which now takes the whole `&FlatNet` so the H1 guard below cannot be
disabled by handing it an empty transition list; TS
`validateInvariantsExact` in `p-invariant-computer.ts`) re-validates
`y·C = 0` in exact arithmetic — but against the *linearized* incidence
matrix (`IncidenceMatrix::from_flat_net`, `incidence_matrix.rs:23-60`), whose
column is `post − pre` with `pre = required_count`
(`net_flattener.rs:50-54`). Consume-all and reset semantics are not linear —
they are the two `m'_i = post[i]` arms of the encoder's fire relation
(`firing_conditions`, `smt_encoder.rs:376-381`, modelled by `fireA`) — so
passing the gate is
necessary but not sufficient. This file proves, at the `fireA` level
([VER-004]'s untimed count abstraction, where the encoders operate), exactly
what *is* sufficient:

* `invariant_strengthening_sound` — under H1 (`y` vanishes on non-linear
  places) and H2 (`y` annihilates each incidence column), `y·M = y·M₀` holds
  on all of `ReachA` ([VER-005] AC2). The C2 gate now checks both: H2 was
  always its `y·C = 0` recheck, and H1 is the consume-all/reset support guard
  this file's necessity witness forced into all three validators. H3
  (env-freedom) is carried by `ReachA` itself, which has no injection rule.
* `strengthened_reach_eq` — under those hypotheses the strengthened relation
  reaches exactly the same markings: conjoining is sound.
* `invariant_strengthening_sound_inj` / `strengthened_reach_eq_inj` — the
  env-aware variant ([VER-006]): with injection rules present, soundness
  needs H3′ `y = 0` on injectable places — exactly what the injector columns
  of `incidence_matrix.rs:40-43` feed through the gate's `y·C = 0`.
* `consume_all_hypothesis_is_necessary`, `injection_hypothesis_is_necessary`
  — concrete nets where H2 still holds (`y·C = 0` alone still accepts `y`)
  yet dropping H1 / H3′ makes the strengthened relation lose a genuinely
  reachable violating state: the false-`Proven` shape, checked by
  `decide`/`omega`, not asserted.
* `bad_rule_nonvacuity` — `encode_property_violation`'s unresolvable-place
  fallback (`smt_encoder.rs:741-744`: unknown `pending` place ⇒ error-rule body
  `false`) proves every net vacuously; refusing to certify is the only
  sound behaviour.
* `quiescent_count_clause_exact` — the `QuiescentCount` arm's `Bad` is exactly
  [VER-002]'s error condition, so its two `false` fallbacks hide no violation.
-/
import Libpetri.Retrodict
import Libpetri.Strengthening.Hypotheses

namespace Libpetri

/-!
## Soundness of strengthening
-/

/-- **Soundness of P-invariant strengthening** (env-free case).

Hypotheses, exactly as the proof forces them:

* **H1** (`ZeroOnNonlinear`): per flat transition, `y` is zero below `n` on
  its reset and consume-all places — the arms where `firing_conditions`
  (`smt_encoder.rs:376-381`) emits `m'_i = post[i]` and the marking's history
  is erased. The C2 gate
  enforces it by *dropping* any invariant whose support meets such a place
  (see `consume_all_hypothesis_is_necessary`, the witness that forced it).
* **H2** (`dotInc y ft n = 0`): `y` annihilates every flat transition's
  incidence column — verbatim the exact-arithmetic check of the C2 gate
  (`validate_invariants_exact`, `p_invariant.rs:313-331`).
* **H3** (env-freedom): implicit in `ReachA`, which has no injection rule;
  `invariant_strengthening_sound_inj` is the env-aware variant.

Conclusion: `y·M = y·M₀` on every reachable abstract marking — the conjunct
of `invariant_conditions` (`smt_encoder.rs:406-429`) really is invariant
([VER-005] AC2). -/
theorem invariant_strengthening_sound {net : FlatNet} {a0 a : AMarking}
    {y : Weight} {n : Nat}
    (h1 : ∀ ft ∈ net, ZeroOnNonlinear y ft.1 n)
    (h2 : ∀ ft ∈ net, dotInc y ft n = 0)
    (h : ReachA net a0 a) :
    dot y a n = dot y a0 n := by
  induction h with
  | init => rfl
  | @step a1 ft hr hmem hen ih =>
    exact (dot_fireA y (h1 ft hmem) (h2 ft hmem) hen).trans ih

/-- One strengthened step: a `StepARel` step whose successor keeps `y·M' = y·M₀`. -/
def StepAStrRel (net : FlatNet) (y : Weight) (n : Nat) (a0 a a' : AMarking) : Prop :=
  StepARel net a a' ∧ dot y a' n = dot y a0 n

/-- `ReachA` with the invariant conjunct `y·M' = y·M₀` added to every
transition-rule body — the shape `encode_transition_rule` actually emits
(`smt_encoder.rs:502` conjoins the `strengthening` list, which `encode_net`
opens with `invariant_conditions` over the successor variables `m'_i` at
`:157`, inside the rule body, so a violating successor is pruned,
not flagged). -/
def ReachAStr (net : FlatNet) (y : Weight) (n : Nat) (a0 : AMarking) :
    AMarking → Prop :=
  Relation.ReflTransGen (StepAStrRel net y n a0) a0

theorem ReachAStr.init {net y n a0} : ReachAStr net y n a0 a0 := Relation.ReflTransGen.refl

theorem ReachAStr.step {net y n a0 a} {ft : FlatTransition} (h : ReachAStr net y n a0 a)
    (hmem : ft ∈ net) (hen : enabledA a ft.1 = true)
    (hc : dot y (fireA a ft.1 ft.2) n = dot y a0 n) : ReachAStr net y n a0 (fireA a ft.1 ft.2) :=
  Relation.ReflTransGen.tail h ⟨⟨ft, hmem, hen, rfl⟩, hc⟩

/-- Induction over `ReachAStr` with the cases of the former inductive. -/
@[elab_as_elim, induction_eliminator]
theorem ReachAStr.rec' {net y n a0} {motive : (a : AMarking) → ReachAStr net y n a0 a → Prop}
    (init : motive a0 ReachAStr.init)
    (step : ∀ {a ft} (hr : ReachAStr net y n a0 a) (hmem : ft ∈ net) (hen : enabledA a ft.1 = true)
      (hc : dot y (fireA a ft.1 ft.2) n = dot y a0 n), motive a hr →
      motive (fireA a ft.1 ft.2) (ReachAStr.step hr hmem hen hc))
    {a : AMarking} (h : ReachAStr net y n a0 a) : motive a h := by
  induction h with
  | refl => exact init
  | tail hr hs ih => obtain ⟨⟨ft, hmem, hen, rfl⟩, hc⟩ := hs; exact step hr hmem hen hc ih

/-- **Conjoining is sound**: under H1 + H2 (+ H3 via `ReachA`), the
strengthened relation reaches exactly the same markings. The forward
inclusion is the load-bearing one — a body conjunct can only remove states,
and H1/H2 guarantee it removes none. The converse is the trivial weakening
(dropping is always sound, which is why the C2 gate may *drop* freely). -/
theorem strengthened_reach_eq {net : FlatNet} {a0 : AMarking} {y : Weight} {n : Nat}
    (h1 : ∀ ft ∈ net, ZeroOnNonlinear y ft.1 n)
    (h2 : ∀ ft ∈ net, dotInc y ft n = 0) :
    ∀ a, ReachA net a0 a ↔ ReachAStr net y n a0 a := by
  intro a
  constructor
  · intro h
    induction h with
    | init => exact ReachAStr.init
    | @step a1 ft hr hmem hen ih =>
      exact ReachAStr.step ih hmem hen
        ((dot_fireA y (h1 ft hmem) (h2 ft hmem) hen).trans
          (invariant_strengthening_sound h1 h2 hr))
  · intro h
    induction h with
    | init => exact ReachA.init
    | @step a1 ft hr hmem hen _hconj ih => exact ReachA.step ih hmem hen

/-!
## The env-aware variant ([VER-006])
-/

/-- H3′-aware conservation: with injection rules present (`ReachAInj`,
modelling the injection loop of `encode_net`, `encode`'s body,
`smt_encoder.rs:175-184`), `y·M = y·M₀`
additionally needs `y` to
vanish on every injectable place — an injection mints a token nothing
consumed, so a nonzero weight there breaks conservation (the encoder knows:
"No P-invariant strengthening — injection deliberately breaks conservation",
`smt_encoder.rs:180`).

H3′ is exactly what the shipped env-aware matrix enforces mechanically: each
injectable place contributes an injector column `+e_p`
(`incidence_matrix.rs:40-43`; TS `incidence-matrix.ts`), and `y·C = 0`
on that column *is* `y p = 0`. This theorem is the sufficiency proof for
that design. -/
theorem invariant_strengthening_sound_inj {net : FlatNet} {envs : List PlaceId}
    {a0 a : AMarking} {y : Weight} {n : Nat}
    (h1 : ∀ ft ∈ net, ZeroOnNonlinear y ft.1 n)
    (h2 : ∀ ft ∈ net, dotInc y ft n = 0)
    (h3 : ∀ p ∈ envs, y p = 0)
    (h : ReachAInj net envs a0 a) :
    dot y a n = dot y a0 n := by
  induction h with
  | init => rfl
  | @step a1 ft hr hmem hen ih =>
    exact (dot_fireA y (h1 ft hmem) (h2 ft hmem) hen).trans ih
  | @inject a1 pinj hr hpin ih =>
    have hstep : dot y (fun q => if q == pinj then a1 q + 1 else a1 q) n
        = dot y a1 n := by
      rw [dot_eq_isum, dot_eq_isum]
      refine isum_congr fun q hq => ?_
      show y q * ((if q == pinj then a1 q + 1 else a1 q : Nat) : Int)
          = y q * (a1 q : Int)
      by_cases hqp : (q == pinj) = true
      · have hq' : q = pinj := by simpa using hqp
        subst hq'
        rw [h3 _ hpin]
        omega
      · rw [if_neg hqp]
    exact hstep.trans ih

/-- One step of `ReachAInjStr`: a strengthened firing, or an unconstrained injection. -/
def StepAInjStrRel (net : FlatNet) (envs : List PlaceId) (y : Weight) (n : Nat)
    (a0 a a' : AMarking) : Prop :=
  StepAStrRel net y n a0 a a' ∨ ∃ p ∈ envs, a' = fun q => if q == p then a q + 1 else a q

/-- The shipped strengthened shape with env injection: the invariant conjunct
sits in *transition*-rule bodies only (`encode_transition_rule`,
`smt_encoder.rs:485-511`); injection rules carry no invariant conjunct
(`encode_injection_rule`, `smt_encoder.rs:532-560` — with
`EncodeOptions::state_equation` they copy the firing counters, `:550-553`,
modelled in `StateEquation.lean`). -/
def ReachAInjStr (net : FlatNet) (envs : List PlaceId) (y : Weight)
    (n : Nat) (a0 : AMarking) : AMarking → Prop :=
  Relation.ReflTransGen (StepAInjStrRel net envs y n a0) a0

theorem ReachAInjStr.init {net envs y n a0} : ReachAInjStr net envs y n a0 a0 :=
  Relation.ReflTransGen.refl

theorem ReachAInjStr.step {net envs y n a0 a} {ft : FlatTransition}
    (h : ReachAInjStr net envs y n a0 a) (hmem : ft ∈ net) (hen : enabledA a ft.1 = true)
    (hc : dot y (fireA a ft.1 ft.2) n = dot y a0 n) :
    ReachAInjStr net envs y n a0 (fireA a ft.1 ft.2) :=
  Relation.ReflTransGen.tail h (Or.inl ⟨⟨ft, hmem, hen, rfl⟩, hc⟩)

theorem ReachAInjStr.inject {net envs y n a0 a} {p : PlaceId}
    (h : ReachAInjStr net envs y n a0 a) (hp : p ∈ envs) :
    ReachAInjStr net envs y n a0 (fun q => if q == p then a q + 1 else a q) :=
  Relation.ReflTransGen.tail h (Or.inr ⟨p, hp, rfl⟩)

/-- Induction over `ReachAInjStr` with the cases of the former inductive. -/
@[elab_as_elim, induction_eliminator]
theorem ReachAInjStr.rec' {net envs y n a0}
    {motive : (a : AMarking) → ReachAInjStr net envs y n a0 a → Prop}
    (init : motive a0 ReachAInjStr.init)
    (step : ∀ {a ft} (hr : ReachAInjStr net envs y n a0 a) (hmem : ft ∈ net)
      (hen : enabledA a ft.1 = true) (hc : dot y (fireA a ft.1 ft.2) n = dot y a0 n),
      motive a hr → motive (fireA a ft.1 ft.2) (ReachAInjStr.step hr hmem hen hc))
    (inject : ∀ {a p} (hr : ReachAInjStr net envs y n a0 a) (hp : p ∈ envs), motive a hr →
      motive (fun q => if q == p then a q + 1 else a q) (ReachAInjStr.inject hr hp))
    {a : AMarking} (h : ReachAInjStr net envs y n a0 a) : motive a h := by
  induction h with
  | refl => exact init
  | tail hr hs ih =>
    rcases hs with ⟨⟨ft, hmem, hen, rfl⟩, hc⟩ | ⟨p, hp, rfl⟩
    · exact step hr hmem hen hc ih
    · exact inject hr hp ih

/-- Conjoining stays sound under injection provided H3′ — the formal warrant
for keeping invariants in the transition rules while the injector columns
force `y = 0` on injectable places. -/
theorem strengthened_reach_eq_inj {net : FlatNet} {envs : List PlaceId}
    {a0 : AMarking} {y : Weight} {n : Nat}
    (h1 : ∀ ft ∈ net, ZeroOnNonlinear y ft.1 n)
    (h2 : ∀ ft ∈ net, dotInc y ft n = 0)
    (h3 : ∀ p ∈ envs, y p = 0) :
    ∀ a, ReachAInj net envs a0 a ↔ ReachAInjStr net envs y n a0 a := by
  intro a
  constructor
  · intro h
    induction h with
    | init => exact ReachAInjStr.init
    | @step a1 ft hr hmem hen ih =>
      exact ReachAInjStr.step ih hmem hen
        ((dot_fireA y (h1 ft hmem) (h2 ft hmem) hen).trans
          (invariant_strengthening_sound_inj h1 h2 h3 hr))
    | @inject a1 pinj hr hpin ih => exact ReachAInjStr.inject ih hpin
  · intro h
    induction h with
    | init => exact ReachAInj.init
    | @step a1 ft hr hmem hen _hconj ih => exact ReachAInj.step ih hmem hen
    | @inject a1 pinj hr hpin ih => exact ReachAInj.inject ih hpin

/-!
## Necessity: H1 and H3′ are load-bearing

Each witness keeps **H2 intact** — the weight vector still annihilates every
column of the shipped incidence matrix, so the C2 gate accepts it in exact
arithmetic — and violates exactly one of the other hypotheses. In both cases
the strengthened relation loses a genuinely reachable violating state: the
false-`Proven` shape. Small closed facts are `decide`d; the open inductions
are by hand, per house style.
-/

/-- Weight `1` on places `0` and `1` — the token-conservation law
`m₀ + m₁ = const` Farkas elimination finds for any one-in-one-out chain. -/
def yUnit : Weight := fun p => if p < 2 then 1 else 0

/-- With the conjunct in the transition rules and `yUnit envPlace ≠ 0`, the
strengthened injected relation freezes `outPlace` at `0`: the real
post-injection firing violates the conjunct (`y·M' = 1 ≠ 0 = y·M₀`), so the
rule body is unsatisfiable and the genuine successor is pruned. -/
theorem strengthened_inj_freezes :
    ∀ a, ReachAInjStr netEnv [envPlace] yUnit 2 m0A a → a outPlace = 0 := by
  intro a h
  induction h with
  | init => rfl
  | @step a1 ft hr hmem hen hconj ih =>
    exfalso
    have hft : ft = (tConsume, [outPlace]) := by simpa [netEnv] using hmem
    subst hft
    have hconj' : dot yUnit (fireA a1 tConsume [outPlace]) 2
        = dot yUnit m0A 2 := hconj
    have e0 : fireA a1 tConsume [outPlace] 0 = a1 0 - 1 + 0 := rfl
    have e1 : fireA a1 tConsume [outPlace] 1 = a1 1 - 0 + 1 := rfl
    rw [dot_two, dot_two, e0, e1, show yUnit 0 = 1 from rfl,
      show yUnit 1 = 1 from rfl, show m0A 0 = 0 from rfl,
      show m0A 1 = 0 from rfl] at hconj'
    omega
  | @inject a1 pinj hr hpin ih =>
    have hpe : pinj = envPlace := by simpa using hpin
    subst hpe
    exact ih

/-- **H3′ is load-bearing** (the [VER-006] net of `Retrodict.lean`).

`yUnit` is a perfect closed-net conservation law for `netEnv` — it
annihilates the only transition column (first conjunct), so the C2 gate run
over an env-*blind* matrix would accept it — and `yUnit envPlace = 1 ≠ 0`
violates H3′. The consequence: the true injected relation reaches
`outPlace = 1` (`injection_reaches_violation`, second conjunct), while the
strengthened relation freezes it at `0` (third conjunct) — a false `Proven`
for `PlaceBound(p₁, 0)`. This is exactly the law the injector columns of
`incidence_matrix.rs:40-43` exist to kill: `y·C = 0` on the `+e_envPlace`
column forces `y envPlace = 0`, i.e. H3′. -/
theorem injection_hypothesis_is_necessary :
    dotInc yUnit (tConsume, [outPlace]) 2 = 0
    ∧ (∃ a, ReachAInj netEnv [envPlace] m0A a ∧ a outPlace = 1)
    ∧ (∀ a, ReachAInjStr netEnv [envPlace] yUnit 2 m0A a → a outPlace = 0) :=
  ⟨by decide, injection_reaches_violation, strengthened_inj_freezes⟩

/-- Drains place `0` with an (unguarded) `In::All`, producing one token into
place `1`. Its shipped incidence column is `(−1, +1)`: `required_count` of
`In::All` is `1` (`required_count`, `input.rs:87`, modelled by
`Card.required`), and
`from_flat_net` builds the column from `pre`/`post` alone, never consulting
`consume_all` (`incidence_matrix.rs:31-38`). -/
def tAll : Transition :=
  { name := "drain_all"
  , inputs := [{ place := 0, card := .all, guard := none }]
  , inhibitors := [], reads := [], resets := [] }

def netAll : FlatNet := [(tAll, [1])]

/-- Two tokens on place `0` — one more than the linearized column claims the
firing consumes. -/
def a0All : AMarking := fun p => if p == 0 then 2 else 0

/-- The true relation reaches `p₁ = 1`: `tAll` is enabled and fires. -/
theorem consume_all_reaches_violation :
    ∃ a, ReachA netAll a0All a ∧ a 1 = 1 := by
  refine ⟨fireA a0All tAll [1], ?_, by decide⟩
  exact ReachA.step (ft := (tAll, [1])) ReachA.init (by simp [netAll]) (by decide)

/-- The strengthened relation freezes `p₁` at `0`: the drain takes `y·M` from
`2` to `1`, so the conjoined equality prunes the genuine successor. -/
theorem strengthened_all_freezes :
    ∀ a, ReachAStr netAll yUnit 2 a0All a → a 1 = 0 := by
  intro a h
  induction h with
  | init => rfl
  | @step a1 ft hr hmem hen hconj ih =>
    exfalso
    have hft : ft = (tAll, [1]) := by simpa [netAll] using hmem
    subst hft
    have hconj' : dot yUnit (fireA a1 tAll [1]) 2 = dot yUnit a0All 2 := hconj
    have e0 : fireA a1 tAll [1] 0 = 0 := rfl
    have e1 : fireA a1 tAll [1] 1 = a1 1 - 0 + 1 := rfl
    rw [dot_two, dot_two, e0, e1, show yUnit 0 = 1 from rfl,
      show yUnit 1 = 1 from rfl, show a0All 0 = 2 from rfl,
      show a0All 1 = 0 from rfl] at hconj'
    omega

/-- **H1 is load-bearing — this witness is why the C2 gate enforces it.**

`consumeAllAt tAll 0 = true` with `yUnit 0 = 1 ≠ 0` violates H1, yet `yUnit`
annihilates `tAll`'s shipped incidence column (first conjunct): the column is
built from `required_count` and never consults `consume_all`
(`incidence_matrix.rs:31-38`, `net_flattener.rs:50-54`), so both Farkas
computation and the C2 gate's `y·C = 0` recheck accept `yUnit` in exact
arithmetic — which is precisely why the gate needed a *separate* H1 guard on
top of it. The real firing drains BOTH tokens (`fireA`'s consume-all
arm, `firing_conditions`, `smt_encoder.rs:379-381`), dropping `y·M` from `2`
to `1`: the true
relation reaches `p₁ = 1` (second conjunct) while the strengthened relation
freezes `p₁` at `0` (third conjunct) — a false `Proven` for
`PlaceBound(p₁, 0)`. A `y·C = 0`-validated invariant is therefore not enough
on nets with `all`/`atLeast`/reset arcs. That is what shipped the H1 guard:
`validate_invariants_exact` and its TypeScript/Java twins now drop any
invariant whose support intersects a consume-all or reset place, and quote
this theorem in the drop reason. -/
theorem consume_all_hypothesis_is_necessary :
    (consumeAllAt tAll 0 = true ∧ yUnit 0 ≠ 0)
    ∧ dotInc yUnit (tAll, [1]) 2 = 0
    ∧ (∃ a, ReachA netAll a0All a ∧ a 1 = 1)
    ∧ (∀ a, ReachAStr netAll yUnit 2 a0All a → a 1 = 0) :=
  ⟨by decide, by decide, consume_all_reaches_violation, strengthened_all_freezes⟩

/-!
## The error-rule `false` fallback

`encode_property_violation` (`smt_encoder.rs:656-773`) emits `Bad ≡ false` in
two kinds of case.

* **Unresolved place.** `PlaceBound` and `JoinedOrDeadLettered` (`:741-744`)
  fall back to `false` for a place the flat net lacks, and `MutualExclusion` and
  `Unreachable` do so when none resolves. The verifier refuses such a property
  before any route runs (`unresolved_property_place_in_net`), so no verdict
  reaches this fallback.
* **Unviolatable predicate.** No marking is quiescent (`encode_quiescent`
  returns `None`, in every quiescence arm), no place can strand a token under
  `DeadlockFree` (`:681-684`), or `QuiescentCount` asks for `[0, ∞)`
  (`count_violation_condition` returns `None`). These are exact:
  `quiescent_count_clause_exact` proves it for the count clause.

With `Bad ≡ false` the error rule `Error :- Reachable(M) ∧ Bad(M)` has an
unsatisfiable body, so Spacer answers `sat`, reported as `Proven`
(`process_z3_result`, `smt_verifier.rs:3059-3101`), for every net, marking and
semantics. `bad_rule_nonvacuity` quantifies over an arbitrary reachable-set
predicate to make "regardless of semantics" literal, so it cannot tell the two
kinds apart; only an exactness proof can. The [VER-014] conditional-sink
disjuncts (`stranded_conditions`) and quiescence itself are not modelled.
-/

/-- The `Proven` verdict shape for a violation predicate `Bad` over a
reachable set `Reach`: no reachable state violates. -/
def ProvenFor (Reach : AMarking → Prop) (Bad : AMarking → Prop) : Prop :=
  ∀ a, Reach a → ¬ Bad a

/-- **A `false` error-rule body proves everything.** The verdict carries zero
information — it holds for any reachable set whatsoever, so it certifies a
net about which the encoder resolved nothing. The only sound behaviour for
an unresolvable property place is to refuse to certify (surface an error
instead of an error rule), which is the formal argument against
`encode_property_violation`'s `smt_encoder.rs:741-744` fallback. -/
theorem bad_rule_nonvacuity (Reach : AMarking → Prop) :
    ProvenFor Reach (fun _ => False) :=
  fun _ _ hbad => hbad

/-- Instantiated at the CHC relation: every net at every initial marking is
`Proven` under the `false` fallback. -/
theorem bad_rule_proves_every_net (net : FlatNet) (a0 : AMarking) :
    ProvenFor (ReachA net a0) (fun _ => False) :=
  bad_rule_nonvacuity _

/-!
## `QuiescentCount`'s count clause is exact ([VER-002])
-/

-- Keep core's `Zero ℕ` for `List.sum` below, as elaborated before Mathlib's algebra was imported.
attribute [local instance high] Zero.ofOfNat0

/-- `count_violation_condition` (`smt_encoder.rs:775-804`) over the count
`total` and whether every waiver is empty: the lower part when `min > 0`, the
upper part when `max` is bounded, `none` when neither applies. -/
def countClause (total : Nat) (waiversEmpty : Bool) (min : Nat) (max : Option Nat) :
    Option Bool :=
  match (if 0 < min then [decide (total < min) && waiversEmpty] else [])
      ++ (max.map fun k => decide (k < total)).toList with
  | [] => none
  | [b] => some b
  | parts => some (parts.any id)

/-- The `QuiescentCount` arm of `encode_property_violation`
(`smt_encoder.rs:751-771`) at one marking. `quiescent` stands for
`encode_quiescent`, unmodelled (`none`: no marking is quiescent). `counted` and
`waivers` are what `index_ordered` (`smt_encoder.rs:827-838`) returns: each
resolved place once, so the list sum is the count over the place set. -/
def quiescentCountBad (quiescent : Option (AMarking → Bool))
    (counted waivers : List PlaceId) (min : Nat) (max : Option Nat) (a : AMarking) :
    Bool :=
  match countClause (counted.map a).sum (waivers.all fun w => a w == 0) min max with
  | none => false
  | some bad =>
    match quiescent with
    | none => false
    | some q => q a && bad

/-- **The count clause is exact** ([VER-002] AC8): the emitted `Bad` holds iff
the marking is quiescent and its count is below `min` with every waiver empty,
or above `max`. A `Bad` weaker than this would certify a false `Proven`; the
arm's `false` fallbacks are the cases where the condition is unsatisfiable. -/
theorem quiescent_count_clause_exact (quiescent : Option (AMarking → Bool))
    (counted waivers : List PlaceId) (min : Nat) (max : Option Nat) (a : AMarking) :
    quiescentCountBad quiescent counted waivers min max a = true ↔
      (∃ q, quiescent = some q ∧ q a = true)
      ∧ (((counted.map a).sum < min ∧ ∀ w ∈ waivers, a w = 0)
        ∨ ∃ k, max = some k ∧ k < (counted.map a).sum) := by
  have hw : (waivers.all fun w => a w == 0) = true ↔ ∀ w ∈ waivers, a w = 0 := by
    simp
  have hclause : ∀ e : Bool, (e = true ↔ ∀ w ∈ waivers, a w = 0) →
      ((countClause (counted.map a).sum e min max).getD false = true ↔
        (((counted.map a).sum < min ∧ ∀ w ∈ waivers, a w = 0)
          ∨ ∃ k, max = some k ∧ k < (counted.map a).sum)) := by
    intro e he
    rw [← he]
    unfold countClause
    cases max <;> by_cases hmin : 0 < min <;> simp [hmin] <;> omega
  rw [← hclause _ hw]
  unfold quiescentCountBad
  cases countClause (counted.map a).sum (waivers.all fun w => a w == 0) min max <;>
    cases quiescent <;> simp

end Libpetri
