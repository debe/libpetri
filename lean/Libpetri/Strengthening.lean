/-
# Verifier-side strengthening: when conjoining a P-invariant is sound

All three language verifiers conjoin every computed P-invariant `y·M = y·M₀`
into the CHC transition-rule *bodies* (`invariant_conditions`,
`smt_encoder.rs:216-234`, spliced by `encode_transition_rule` at `:307`; the
TypeScript and Java encoders mirror it). A
conjunct in a rule body does not annotate the encoding — it *removes*
successors from the least fixpoint. A wrong invariant therefore shrinks
`Reachable` below the true reachable set and can certify a false `Proven`,
the failure mode this development exists to close.

The C2 runtime gate (`validate_invariants_exact`, `p_invariant.rs:207-344`,
which now takes the whole `&FlatNet` so the H1 guard below cannot be
disabled by handing it an empty transition list; TS
`validateInvariantsExact` in `p-invariant-computer.ts`) re-validates
`y·C = 0` in exact arithmetic — but against the *linearized* incidence
matrix (`IncidenceMatrix::from_flat_net`, `incidence_matrix.rs:23-60`), whose
column is `post − pre` with `pre = required_count`
(`net_flattener.rs:50-54`). Consume-all and reset semantics are not linear —
they are the two `m'_i = post[i]` arms of the encoder's fire relation
(`firing_conditions`, `smt_encoder.rs:180-187`, modelled by `fireA`) — so
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
  fallback (`smt_encoder.rs:473-474`: unknown `pending` place ⇒ error-rule body
  `false`) proves every net vacuously; refusing to certify is the only
  sound behaviour.
-/
import Libpetri.Retrodict

namespace Libpetri

/-!
## Weight vectors and the emitted sums

`PInvariant` (`p_invariant.rs:9-13`) carries `weights: Vec<i64>` over the
dense place index plus a `support` that `validate_invariants_exact` pins to
exactly the nonzero weights (`p_invariant.rs:277-288`). A weight vector is
modelled total over `PlaceId` with its support below `place_count`; sums are
hand-rolled over the first `n` places (`RingArith.lean` style — no Mathlib),
which is the sum `invariant_conditions` emits (`smt_encoder.rs:216-234`),
since the dense index of `flatten` (`net_flattener.rs:31-40`) keeps every
place id below `place_count`.
-/

/-- A P-invariant weight vector `y`: one integer weight per dense place index
(`PInvariant.weights`, `p_invariant.rs:9-13`). -/
abbrev Weight := PlaceId → Int

/-- The support of `y` lies below `n` — what `PInvariant.support ⊆
[0, place_count)` means for a total function. -/
def SupportBelow (n : Nat) (y : Weight) : Prop :=
  ∀ p, n ≤ p → y p = 0

/-- `Σ_{p < n} f p`, hand-rolled over the dense place index. -/
def isum (f : PlaceId → Int) : Nat → Int
  | 0 => 0
  | n + 1 => isum f n + f n

/-- The weighted token sum `y·M` over the first `n` places — the equality the
encoder conjoins on the successor variables `m'_i` (`invariant_conditions`,
`smt_encoder.rs:216-234`). -/
def dot (y : Weight) (m : AMarking) (n : Nat) : Int :=
  isum (fun p => y p * (m p : Int)) n

/-- `y·(post − pre)` over the first `n` places: `y` applied to one flat
transition's **incidence column exactly as the shipped matrix builds it** —
`C[t][p] = post − pre` with `pre = required_count`
(`incidence_matrix.rs:45-51` from `net_flattener.rs:50-54`; TS
`incidence-matrix.ts` from `net-flattener.ts`). `dotInc y ft n = 0` is
therefore *verbatim* the condition `validate_invariants_exact` re-validates in
exact arithmetic (`p_invariant.rs:302-320`; TS `p-invariant-computer.ts`).
Note what the column does **not** say: nothing about `consume_all` or
`reset_places` — that omission is H1 below. -/
def dotInc (y : Weight) (ft : FlatTransition) (n : Nat) : Int :=
  isum (fun p => y p * ((post ft.2 p : Int) - (pre ft.1 p : Int))) n

theorem isum_congr {f g : PlaceId → Int} :
    ∀ {n : Nat}, (∀ p, p < n → f p = g p) → isum f n = isum g n
  | 0, _ => rfl
  | n + 1, h => by
    show isum f n + f n = isum g n + g n
    rw [isum_congr fun p hp => h p (Nat.lt_succ_of_lt hp), h n n.lt_succ_self]

theorem isum_add (f g : PlaceId → Int) :
    ∀ n, isum (fun p => f p + g p) n = isum f n + isum g n
  | 0 => rfl
  | n + 1 => by
    show isum (fun p => f p + g p) n + (f n + g n)
        = (isum f n + f n) + (isum g n + g n)
    rw [isum_add f g n]
    omega

/-- A weight vector supported below `n` sums identically under any wider
truncation — the encoder's support-indexed sum (`invariant_conditions`,
`smt_encoder.rs:219-223`, iterates `inv.support` only) loses nothing against
the full `y·M`. -/
theorem dot_stable_of_support_below {y : Weight} {n : Nat}
    (hy : SupportBelow n y) (m : AMarking) :
    ∀ k, dot y m (n + k) = dot y m n
  | 0 => rfl
  | k + 1 => by
    show dot y m (n + k) + y (n + k) * (m (n + k) : Int) = dot y m n
    rw [dot_stable_of_support_below hy m k, hy (n + k) (Nat.le_add_right n k)]
    omega

/-- Two-place evaluation of `dot`, for the concrete witnesses below. -/
theorem dot_two (y : Weight) (m : AMarking) :
    dot y m 2 = y 0 * (m 0 : Int) + y 1 * (m 1 : Int) := by
  show 0 + y 0 * (m 0 : Int) + y 1 * (m 1 : Int) = _
  omega

/-!
## The hypotheses the proof forces

The abstract fire relation (`fireA`, modelling `firing_conditions`,
`smt_encoder.rs:177-201`) has exactly two non-linear arms: a reset place and a
consume-all place both get `m'_i = post[i]` (`smt_encoder.rs:180-187`), erasing
however many tokens the
place actually held. A weighted sum survives such an arm only where the
weight is zero — that is H1, and `consume_all_hypothesis_is_necessary` is the
counterexample that put it into the shipped gate. H2 is the incidence-column
condition the C2 gate always checked. H3 — env-freedom — is carried by the
reachability relation itself; its env-aware replacement H3′ appears with
`invariant_strengthening_sound_inj`.
-/

/-- **H1 (linearity).** Below the truncation bound, `y` vanishes on every
place where `fireA` is non-linear: reset places and consume-all places
(`Card.consumesAll`, i.e. `In::All` / `In::AtLeast` — `flatten`,
`net_flattener.rs:53-55`).
Only places below `n` matter: the emitted sum never reads past `place_count`. -/
def ZeroOnNonlinear (y : Weight) (t : Transition) (n : Nat) : Prop :=
  ∀ p, p < n → t.resets.contains p = true ∨ consumeAllAt t p = true → y p = 0

/-- Abstract enablement bounds the linear arm's `Nat` subtraction:
`pre[p] ≤ m p`, so `m p - pre[p] + post[p]` computes the exact integer
`m p − pre[p] + post[p]`. -/
theorem pre_le_of_enabledA {m : AMarking} {t : Transition}
    (hEn : enabledA m t = true) (p : PlaceId) : pre t p ≤ m p := by
  unfold pre
  cases hs : specAt t p with
  | none => exact Nat.zero_le _
  | some s =>
    obtain ⟨hmem, hplace⟩ := specAt_sound hs
    unfold enabledA at hEn
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hEn
    exact hplace ▸ hEn.1.1 s hmem

/-- One place's contribution to `y·M` across one abstract firing: with H1 at
`p` and enablement, the change is exactly `y p · (post[p] − pre[p])` — the
place's incidence-column entry. -/
theorem fire_term (y : Weight) {m : AMarking} {t : Transition} (br : List PlaceId)
    {n : Nat} (h1 : ZeroOnNonlinear y t n) (hEn : enabledA m t = true)
    (p : PlaceId) (hp : p < n) :
    y p * (fireA m t br p : Int)
      = y p * (m p : Int) + y p * ((post br p : Int) - (pre t p : Int)) := by
  by_cases hR : t.resets.contains p = true
  · rw [h1 p hp (Or.inl hR)]
    omega
  · by_cases hCA : consumeAllAt t p = true
    · rw [h1 p hp (Or.inr hCA)]
      omega
    · have hfa : fireA m t br p = m p - pre t p + post br p := by
        unfold fireA
        rw [if_neg hR, if_neg hCA]
      have hle : pre t p ≤ m p := pre_le_of_enabledA hEn p
      have hcast : ((m p - pre t p + post br p : Nat) : Int)
          = (m p : Int) + ((post br p : Int) - (pre t p : Int)) := by omega
      rw [hfa, hcast, Int.mul_add]

/-- Per-step conservation: one abstract firing preserves `y·M` when `y` is
(H1) zero on the firing's non-linear places and (H2) annihilates its
incidence column. [VER-005] AC2, with the hypothesis the shipped pipeline is
missing made explicit. -/
theorem dot_fireA (y : Weight) {m : AMarking} {t : Transition} {br : List PlaceId}
    {n : Nat} (h1 : ZeroOnNonlinear y t n) (h2 : dotInc y (t, br) n = 0)
    (hEn : enabledA m t = true) :
    dot y (fireA m t br) n = dot y m n := by
  have hsplit : dot y (fireA m t br) n = dot y m n + dotInc y (t, br) n := by
    have hcongr : isum (fun p => y p * (fireA m t br p : Int)) n
        = isum (fun p => y p * (m p : Int)
            + y p * ((post br p : Int) - (pre t p : Int))) n :=
      isum_congr fun p hp => fire_term y br h1 hEn p hp
    exact hcongr.trans (isum_add _ _ n)
  rw [hsplit, h2]
  omega

/-!
## Soundness of strengthening
-/

/-- **Soundness of P-invariant strengthening** (env-free case).

Hypotheses, exactly as the proof forces them:

* **H1** (`ZeroOnNonlinear`): per flat transition, `y` is zero below `n` on
  its reset and consume-all places — the arms where `firing_conditions`
  (`smt_encoder.rs:180-187`) emits `m'_i = post[i]` and the marking's history
  is erased. The C2 gate
  enforces it by *dropping* any invariant whose support meets such a place
  (see `consume_all_hypothesis_is_necessary`, the witness that forced it).
* **H2** (`dotInc y ft n = 0`): `y` annihilates every flat transition's
  incidence column — verbatim the exact-arithmetic check of the C2 gate
  (`validate_invariants_exact`, `p_invariant.rs:302-320`).
* **H3** (env-freedom): implicit in `ReachA`, which has no injection rule;
  `invariant_strengthening_sound_inj` is the env-aware variant.

Conclusion: `y·M = y·M₀` on every reachable abstract marking — the conjunct
of `invariant_conditions` (`smt_encoder.rs:216-234`) really is invariant
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

/-- `ReachA` with the invariant conjunct `y·M' = y·M₀` added to every
transition-rule body — the shape `encode_transition_rule` actually emits
(`smt_encoder.rs:307` conjoins `invariant_conditions` over the successor
variables `m'_i` inside the rule body, so a violating successor is pruned,
not flagged). -/
inductive ReachAStr (net : FlatNet) (y : Weight) (n : Nat) (a0 : AMarking) :
    AMarking → Prop
  | init : ReachAStr net y n a0 a0
  | step {a ft} :
      ReachAStr net y n a0 a → ft ∈ net → enabledA a ft.1 = true →
      dot y (fireA a ft.1 ft.2) n = dot y a0 n →
      ReachAStr net y n a0 (fireA a ft.1 ft.2)

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
modelling `encode`'s injection loop, `smt_encoder.rs:84-92`), `y·M = y·M₀`
additionally needs `y` to
vanish on every injectable place — an injection mints a token nothing
consumed, so a nonzero weight there breaks conservation (the encoder knows:
"No P-invariant strengthening — injection deliberately breaks conservation",
`smt_encoder.rs:89`).

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
      unfold dot
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

/-- The shipped strengthened shape with env injection: the invariant conjunct
sits in *transition*-rule bodies only (`encode_transition_rule`,
`smt_encoder.rs:302-310`); injection rules carry no conjunct
(`encode_injection_rule`, `smt_encoder.rs:321-344`). -/
inductive ReachAInjStr (net : FlatNet) (envs : List PlaceId) (y : Weight)
    (n : Nat) (a0 : AMarking) : AMarking → Prop
  | init : ReachAInjStr net envs y n a0 a0
  | step {a ft} :
      ReachAInjStr net envs y n a0 a → ft ∈ net → enabledA a ft.1 = true →
      dot y (fireA a ft.1 ft.2) n = dot y a0 n →
      ReachAInjStr net envs y n a0 (fireA a ft.1 ft.2)
  | inject {a p} :
      ReachAInjStr net envs y n a0 a → p ∈ envs →
      ReachAInjStr net envs y n a0 (fun q => if q == p then a q + 1 else a q)

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
arm, `firing_conditions`, `smt_encoder.rs:184-186`), dropping `y·M` from `2`
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

`encode_property_violation` falls back to a `false` violation condition when
a property references a place the flattener cannot resolve: the
`JoinedOrDeadLettered` arm at `smt_encoder.rs:473-474` ("Unknown pending
place name: no state can violate."), and identically the unresolved
`PlaceBound` arm at `:450-451` and the empty-condition arms at `:436-437` /
`:460-461`.
With `Bad ≡ false`, the error rule `Error :- Reachable(M) ∧ Bad(M)` has an
unsatisfiable body, so Spacer answers `sat` — reported as `Proven`
(`process_z3_result`, `smt_verifier.rs:1596-1638`) — for EVERY net, marking
and semantics. The
theorem quantifies over an arbitrary reachable-set predicate to make
"regardless of semantics" literal.
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
`encode_property_violation`'s `smt_encoder.rs:473-474` fallback. -/
theorem bad_rule_nonvacuity (Reach : AMarking → Prop) :
    ProvenFor Reach (fun _ => False) :=
  fun _ _ hbad => hbad

/-- Instantiated at the CHC relation: every net at every initial marking is
`Proven` under the `false` fallback. -/
theorem bad_rule_proves_every_net (net : FlatNet) (a0 : AMarking) :
    ProvenFor (ReachA net a0) (fun _ => False) :=
  bad_rule_nonvacuity _

end Libpetri
