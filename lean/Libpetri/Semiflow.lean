/-
# Semiflow strengthening and the vacuous colour layer

Two corollaries of `Strengthening.lean`, each the formal warrant for one shipped
verifier change ([VER-007], [NU-053] AC6).

**Where the laws come from.** Phase 3 of every verifier feeds the encoders the
conservation laws it can validate. The null-space basis
(`compute_p_invariants`, `p_invariant.rs`) is one basis of many: elimination
returns mixed-sign rows and rows that fold a reset place into a chain whose
other combinations avoid it — both lost to the exact gate
(`validate_invariants_exact`, `p_invariant.rs`), on a reset-heavy net every law
of the chains those arcs touch. The Farkas / Colom–Silva enumeration
(`compute_p_semiflows`, `p_invariant.rs`) returns the *minimal* semi-positive
laws instead. [VER-007] lets the verifier union the gate-validated semiflows
into the list the encoders receive (Java `SmtVerifier.semiflowInvariants`; the
Rust and TypeScript ports mirror it), off by default.

* `ValidLaw` — what the gate accepts, from either source: H1 + H2 of
  `Strengthening.lean`. `Semiflow` adds semi-positivity, the one thing a Farkas
  row has that a basis row need not.
* `ReachAStrs` — the rule body with **every** law of a list conjoined, which is
  what `invariant_conditions` (`smt_encoder.rs`) emits over the whole list.
* `semiflow_union_sound` — conjoining `basis ++ semiflows` preserves the
  abstract reachable set whenever every member passed the gate. The union is
  pure strengthening: it removes no successor, so it can never turn a
  `Violated` into a `Proven` ([VER-007] AC2/AC5). `semiflow_union_sound_inj` is
  the env-aware twin under H3′ ([VER-006]).
* `semiflow_gate_is_necessary` — `yUnit` is exactly what Farkas returns on
  `netAll` (semi-positive, `y·C = 0`) and is still unsound without H1: the
  semiflow source must pass the *same* gate as the basis ([VER-007] AC1).

**The colour-slot bound at zero.** The name-coloured encoder bounds the number
of simultaneously live names by `k = y·M0` for a covering non-negative
semiflow `y` (`colour_slot_bound`, `name_coloured_encoder.rs`; [NU-053]). At
`k = 0` no coloured token can ever exist, so every mint, join and coloured
consumer is dead on the reachable set and the zero-slot encoding — which emits
no rule for them — is exact rather than a fallback ([NU-053] AC6):

* `covered_place_empty` — a place with positive weight under a semi-positive
  validated law of initial sum `0` is empty on every reachable marking.
* `covered_transition_dead` — a flat transition that consumes from or produces
  into such a place is never enabled on the reachable set.
* `vacuous_colour_layer` — dropping those transitions (any sub-net that keeps
  the untouched rows) reaches exactly the same markings.
-/
import Libpetri.Strengthening

namespace Libpetri

/-!
## Validated laws, from either source
-/

/-- What the exact gate accepts, from either source: H1 (`ZeroOnNonlinear` on
every flat transition, the consume-all / reset support guard) and H2 (`y`
annihilates every incidence column, the exact-arithmetic `y·C = 0` recheck of
`validate_invariants_exact`, `p_invariant.rs`). Nothing here says where `y`
came from — that is the point. -/
structure ValidLaw (net : FlatNet) (n : Nat) (y : Weight) : Prop where
  h1 : ∀ ft ∈ net, ZeroOnNonlinear y ft.1 n
  h2 : ∀ ft ∈ net, dotInc y ft n = 0

/-- A validated P-semiflow (a Farkas row that passed the gate): a validated law
that is also semi-positive. Semi-positivity is unused by the strengthening
proof — a semiflow is sound to conjoin for the same reason any validated law
is — and load-bearing only for the colour-slot bound below. -/
structure Semiflow (net : FlatNet) (n : Nat) (y : Weight) : Prop
    extends ValidLaw net n y where
  nonneg : ∀ p, 0 ≤ y p

/-- `ReachA` with the conjunct `y·M' = y·M₀` added for **every** law in `ys` —
the rule body `invariant_conditions` (`smt_encoder.rs`) builds when handed the
whole list, spliced by `encode_transition_rule`. `ReachAStr` of
`Strengthening.lean` is the one-law case. -/
inductive ReachAStrs (net : FlatNet) (ys : List Weight) (n : Nat) (a0 : AMarking) :
    AMarking → Prop
  | init : ReachAStrs net ys n a0 a0
  | step {a ft} :
      ReachAStrs net ys n a0 a → ft ∈ net → enabledA a ft.1 = true →
      (∀ y ∈ ys, dot y (fireA a ft.1 ft.2) n = dot y a0 n) →
      ReachAStrs net ys n a0 (fireA a ft.1 ft.2)

/-- Conjoining a whole list of validated laws is sound: the strengthened
relation reaches exactly the same markings. Forward direction per law from
`dot_fireA` and `invariant_strengthening_sound`; the converse drops the
conjuncts. -/
theorem strengthened_reach_eq_list {net : FlatNet} {a0 : AMarking} {ys : List Weight}
    {n : Nat} (hv : ∀ y ∈ ys, ValidLaw net n y) :
    ∀ a, ReachA net a0 a ↔ ReachAStrs net ys n a0 a := by
  intro a
  constructor
  · intro h
    induction h with
    | init => exact ReachAStrs.init
    | @step a1 ft hr hmem hen ih =>
      exact ReachAStrs.step ih hmem hen fun y hy =>
        (dot_fireA y ((hv y hy).h1 ft hmem) ((hv y hy).h2 ft hmem) hen).trans
          (invariant_strengthening_sound (hv y hy).h1 (hv y hy).h2 hr)
  · intro h
    induction h with
    | init => exact ReachA.init
    | @step a1 ft hr hmem hen _hconj ih => exact ReachA.step ih hmem hen

/-- **Soundness of the semiflow union** ([VER-007]). With the basis rows and the
semiflows both gate-validated, handing the encoder `basis ++ semiflows` (the
union `SmtVerifier.semiflowInvariants` performs) preserves the abstract
reachable set. Pure strengthening: no successor is removed, so a `Violated`
verdict cannot become `Proven` and a `Proven` one is re-provable by the
certificate check against the same list. -/
theorem semiflow_union_sound {net : FlatNet} {a0 : AMarking}
    {basis semiflows : List Weight} {n : Nat}
    (hb : ∀ y ∈ basis, ValidLaw net n y)
    (hs : ∀ y ∈ semiflows, Semiflow net n y) :
    ∀ a, ReachA net a0 a ↔ ReachAStrs net (basis ++ semiflows) n a0 a :=
  strengthened_reach_eq_list fun y hy =>
    match List.mem_append.mp hy with
    | .inl h => hb y h
    | .inr h => (hs y h).toValidLaw

/-- Appending one more validated law never changes what the strengthened
relation reaches — the "adding laws is monotone-safe" reading of the union. -/
theorem strengthening_monotone {net : FlatNet} {a0 : AMarking} {ys : List Weight}
    {n : Nat} {y : Weight}
    (hv : ∀ y' ∈ ys, ValidLaw net n y') (hy : ValidLaw net n y) :
    ∀ a, ReachAStrs net ys n a0 a ↔ ReachAStrs net (ys ++ [y]) n a0 a := by
  intro a
  rw [← strengthened_reach_eq_list hv, ← strengthened_reach_eq_list]
  intro y' hy'
  match List.mem_append.mp hy' with
  | .inl h => exact hv y' h
  | .inr h =>
    rw [List.mem_singleton] at h
    exact h ▸ hy

/-!
## The env-aware twin ([VER-006])
-/

/-- A validated law in environment-analysis mode: H1, H2, and H3′ — zero weight
on every injectable place, which the injector columns of
`incidence_matrix.rs` force through the gate's own `y·C = 0`. -/
structure ValidLawInj (net : FlatNet) (envs : List PlaceId) (n : Nat) (y : Weight) : Prop
    extends ValidLaw net n y where
  h3 : ∀ p ∈ envs, y p = 0

/-- `ReachAInj` with every law of `ys` conjoined into the transition rules;
injection rules carry no conjunct (`encode_injection_rule`, `smt_encoder.rs`). -/
inductive ReachAInjStrs (net : FlatNet) (envs : List PlaceId) (ys : List Weight)
    (n : Nat) (a0 : AMarking) : AMarking → Prop
  | init : ReachAInjStrs net envs ys n a0 a0
  | step {a ft} :
      ReachAInjStrs net envs ys n a0 a → ft ∈ net → enabledA a ft.1 = true →
      (∀ y ∈ ys, dot y (fireA a ft.1 ft.2) n = dot y a0 n) →
      ReachAInjStrs net envs ys n a0 (fireA a ft.1 ft.2)
  | inject {a p} :
      ReachAInjStrs net envs ys n a0 a → p ∈ envs →
      ReachAInjStrs net envs ys n a0 (fun q => if q == p then a q + 1 else a q)

theorem strengthened_reach_eq_list_inj {net : FlatNet} {envs : List PlaceId}
    {a0 : AMarking} {ys : List Weight} {n : Nat}
    (hv : ∀ y ∈ ys, ValidLawInj net envs n y) :
    ∀ a, ReachAInj net envs a0 a ↔ ReachAInjStrs net envs ys n a0 a := by
  intro a
  constructor
  · intro h
    induction h with
    | init => exact ReachAInjStrs.init
    | @step a1 ft hr hmem hen ih =>
      exact ReachAInjStrs.step ih hmem hen fun y hy =>
        (dot_fireA y ((hv y hy).h1 ft hmem) ((hv y hy).h2 ft hmem) hen).trans
          (invariant_strengthening_sound_inj (hv y hy).h1 (hv y hy).h2 (hv y hy).h3 hr)
    | @inject a1 pinj hr hpin ih => exact ReachAInjStrs.inject ih hpin
  · intro h
    induction h with
    | init => exact ReachAInj.init
    | @step a1 ft hr hmem hen _hconj ih => exact ReachAInj.step ih hmem hen
    | @inject a1 pinj hr hpin ih => exact ReachAInj.inject ih hpin

/-- The semiflow union stays sound with injection rules present, provided every
member also satisfies H3′ — which the env-aware incidence matrix guarantees
for anything that passes the gate. -/
theorem semiflow_union_sound_inj {net : FlatNet} {envs : List PlaceId} {a0 : AMarking}
    {basis semiflows : List Weight} {n : Nat}
    (hb : ∀ y ∈ basis, ValidLawInj net envs n y)
    (hs : ∀ y ∈ semiflows, ValidLawInj net envs n y) :
    ∀ a, ReachAInj net envs a0 a ↔ ReachAInjStrs net envs (basis ++ semiflows) n a0 a :=
  strengthened_reach_eq_list_inj fun y hy =>
    match List.mem_append.mp hy with
    | .inl h => hb y h
    | .inr h => hs y h

/-!
## The semiflow source must pass the same gate
-/

/-- `yUnit` is semi-positive: the shape Farkas enumeration returns. -/
theorem yUnit_nonneg : ∀ p, 0 ≤ yUnit p := by
  intro p
  unfold yUnit
  split <;> omega

/-- **Semiflows need the H1 guard too** ([VER-007] AC1). `yUnit` is semi-positive
and annihilates the shipped incidence column of `netAll` — precisely a Farkas
row, so `compute_p_semiflows` returns it and a `y·C = 0`-only gate accepts it —
yet conjoining it prunes a genuinely reachable violating state
(`consume_all_hypothesis_is_necessary`). Hence the union of [VER-007] must run
the semiflows through the full gate (H1 included), never a cheaper one. -/
theorem semiflow_gate_is_necessary :
    (∀ p, 0 ≤ yUnit p)
    ∧ dotInc yUnit (tAll, [1]) 2 = 0
    ∧ (∃ a, ReachA netAll a0All a ∧ a 1 = 1)
    ∧ (∀ a, ReachAStr netAll yUnit 2 a0All a → a 1 = 0) :=
  ⟨yUnit_nonneg, consume_all_hypothesis_is_necessary.2.1,
    consume_all_hypothesis_is_necessary.2.2.1, consume_all_hypothesis_is_necessary.2.2.2⟩

/-!
## The colour-slot bound at zero ([NU-053] AC6)

`colour_slot_bound` (`name_coloured_encoder.rs`) returns `y·M0` for a
semi-positive validated law `y` with `y p ≥ 1` on every coloured place. The
lemmas below are what make `k = 0` an *exact* plan: with the initial weighted
sum at zero, conservation pins every covered place to zero tokens on every
reachable marking, so no mint (produces into a covered place), join or coloured
consumer (consumes from one) is ever enabled — and the encoder, which emits
one rule per colour slot for those classes, emits none for them.
-/

theorem isum_nonneg {f : PlaceId → Int} (hf : ∀ p, 0 ≤ f p) : ∀ n, 0 ≤ isum f n
  | 0 => Int.le_refl 0
  | n + 1 => by
    show 0 ≤ isum f n + f n
    have := isum_nonneg hf n
    have := hf n
    omega

/-- With every summand non-negative, one summand is bounded by the sum. -/
theorem isum_term_le {f : PlaceId → Int} (hf : ∀ p, 0 ≤ f p) :
    ∀ n p, p < n → f p ≤ isum f n
  | 0, p, h => absurd h (Nat.not_lt_zero p)
  | n + 1, p, h => by
    show f p ≤ isum f n + f n
    have hn := hf n
    rcases Nat.lt_or_ge p n with hlt | hge
    · have := isum_term_le hf n p hlt
      omega
    · have hpn : p = n := Nat.le_antisymm (Nat.le_of_lt_succ h) hge
      subst hpn
      have := isum_nonneg hf p
      omega

/-- A semi-positive weighted sum at zero empties every positively-weighted place. -/
theorem dot_zero_forces_empty {y : Weight} {a : AMarking} {n : Nat}
    (hy : ∀ p, 0 ≤ y p) (h0 : dot y a n = 0) {p : PlaceId} (hp : p < n) (hpos : 0 < y p) :
    a p = 0 := by
  have hf : ∀ q, 0 ≤ y q * (a q : Int) := fun q =>
    Int.mul_nonneg (hy q) (Int.natCast_nonneg (a q))
  have hterm : y p * (a p : Int) ≤ isum (fun q => y q * (a q : Int)) n :=
    isum_term_le hf n p hp
  unfold dot at h0
  rw [h0] at hterm
  rcases Nat.eq_zero_or_pos (a p) with hz | hgt
  · exact hz
  · exfalso
    have hpos' : 0 < (a p : Int) := by omega
    have := Int.mul_pos hpos hpos'
    omega

/-- A covered place (positive weight under a semi-positive validated law whose
initial sum is `0`) holds no token on any reachable marking. -/
theorem covered_place_empty {net : FlatNet} {a0 a : AMarking} {y : Weight} {n : Nat}
    (hv : ValidLaw net n y) (hy : ∀ p, 0 ≤ y p) (h0 : dot y a0 n = 0)
    (hr : ReachA net a0 a) {p : PlaceId} (hp : p < n) (hpos : 0 < y p) : a p = 0 :=
  dot_zero_forces_empty hy ((invariant_strengthening_sound hv.h1 hv.h2 hr).trans h0) hp hpos

/-- Whether a flat transition consumes from or produces into a covered place —
the mint / join / coloured-consumer classes of `build_plan`
(`name_coloured_encoder.rs`), read off the flat row's own incidence. -/
def touchesCovered (y : Weight) (n : Nat) (ft : FlatTransition) : Bool :=
  (List.range n).any fun p =>
    decide (0 < y p) && (decide (0 < pre ft.1 p) || decide (post ft.2 p = 1))

/-- A transition touching a covered place is never enabled on the reachable
set: consuming needs a token the place never holds; producing would put one
there, which the successor's conservation forbids. -/
theorem covered_transition_dead {net : FlatNet} {a0 : AMarking} {y : Weight} {n : Nat}
    {ft : FlatTransition}
    (hv : ValidLaw net n y) (hy : ∀ p, 0 ≤ y p) (h0 : dot y a0 n = 0)
    (hmem : ft ∈ net) (ht : touchesCovered y n ft = true) :
    ∀ a, ReachA net a0 a → enabledA a ft.1 = false := by
  intro a hr
  unfold touchesCovered at ht
  rw [List.any_eq_true] at ht
  obtain ⟨p, hpr, hcond⟩ := ht
  rw [List.mem_range] at hpr
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hcond
  obtain ⟨hpos, hio⟩ := hcond
  have hempty : a p = 0 := covered_place_empty hv hy h0 hr hpr hpos
  cases hen : enabledA a ft.1 with
  | false => rfl
  | true =>
    exfalso
    rcases hio with hpre | hpost
    · have := pre_le_of_enabledA hen p
      omega
    · have hsucc : ReachA net a0 (fireA a ft.1 ft.2) := ReachA.step hr hmem hen
      have hz : fireA a ft.1 ft.2 p = 0 := covered_place_empty hv hy h0 hsucc hpr hpos
      have hfire : 1 ≤ fireA a ft.1 ft.2 p := by
        simp only [fireA]
        split
        · omega
        · split <;> omega
      omega

/-- **The colour layer is vacuous at `k = 0`** ([NU-053] AC6). Any sub-net that
keeps every row not touching a covered place — in particular the `Untouched`
rows, the only ones the zero-slot coloured encoding emits a rule for — reaches
exactly the markings the full net reaches. Together with `covered_place_empty`
(the dropped coloured columns are identically zero) this is the exactness of
the `k = 0` plan; the encoder itself is modelled, not extracted. -/
theorem vacuous_colour_layer {net net' : FlatNet} {a0 : AMarking} {y : Weight} {n : Nat}
    (hv : ValidLaw net n y) (hy : ∀ p, 0 ≤ y p) (h0 : dot y a0 n = 0)
    (hsub : ∀ ft ∈ net', ft ∈ net)
    (hkeep : ∀ ft ∈ net, touchesCovered y n ft = false → ft ∈ net') :
    ∀ a, ReachA net a0 a ↔ ReachA net' a0 a := by
  intro a
  constructor
  · intro h
    induction h with
    | init => exact ReachA.init
    | @step a1 ft hr hmem hen ih =>
      cases ht : touchesCovered y n ft with
      | true =>
        have hdead := covered_transition_dead hv hy h0 hmem ht a1 hr
        rw [hdead] at hen
        exact Bool.noConfusion hen
      | false => exact ReachA.step ih (hkeep ft hmem ht) hen
  · intro h
    induction h with
    | init => exact ReachA.init
    | @step a1 ft hr hmem hen ih => exact ReachA.step ih (hsub ft hmem) hen

/-- Env-aware `covered_place_empty`: under H3′ the injected relation keeps every
covered place empty too (an injectable place cannot be covered — its weight is
zero — so injection never lands a token on one). -/
theorem covered_place_empty_inj {net : FlatNet} {envs : List PlaceId} {a0 a : AMarking}
    {y : Weight} {n : Nat}
    (hv : ValidLawInj net envs n y) (hy : ∀ p, 0 ≤ y p) (h0 : dot y a0 n = 0)
    (hr : ReachAInj net envs a0 a) {p : PlaceId} (hp : p < n) (hpos : 0 < y p) : a p = 0 :=
  dot_zero_forces_empty hy
    ((invariant_strengthening_sound_inj hv.h1 hv.h2 hv.h3 hr).trans h0) hp hpos

theorem covered_transition_dead_inj {net : FlatNet} {envs : List PlaceId} {a0 : AMarking}
    {y : Weight} {n : Nat} {ft : FlatTransition}
    (hv : ValidLawInj net envs n y) (hy : ∀ p, 0 ≤ y p) (h0 : dot y a0 n = 0)
    (hmem : ft ∈ net) (ht : touchesCovered y n ft = true) :
    ∀ a, ReachAInj net envs a0 a → enabledA a ft.1 = false := by
  intro a hr
  unfold touchesCovered at ht
  rw [List.any_eq_true] at ht
  obtain ⟨p, hpr, hcond⟩ := ht
  rw [List.mem_range] at hpr
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hcond
  obtain ⟨hpos, hio⟩ := hcond
  have hempty : a p = 0 := covered_place_empty_inj hv hy h0 hr hpr hpos
  cases hen : enabledA a ft.1 with
  | false => rfl
  | true =>
    exfalso
    rcases hio with hpre | hpost
    · have := pre_le_of_enabledA hen p
      omega
    · have hsucc : ReachAInj net envs a0 (fireA a ft.1 ft.2) := ReachAInj.step hr hmem hen
      have hz : fireA a ft.1 ft.2 p = 0 := covered_place_empty_inj hv hy h0 hsucc hpr hpos
      have hfire : 1 ≤ fireA a ft.1 ft.2 p := by
        simp only [fireA]
        split
        · omega
        · split <;> omega
      omega

/-- `vacuous_colour_layer` with injection rules present (same environment
places on both sides). -/
theorem vacuous_colour_layer_inj {net net' : FlatNet} {envs : List PlaceId} {a0 : AMarking}
    {y : Weight} {n : Nat}
    (hv : ValidLawInj net envs n y) (hy : ∀ p, 0 ≤ y p) (h0 : dot y a0 n = 0)
    (hsub : ∀ ft ∈ net', ft ∈ net)
    (hkeep : ∀ ft ∈ net, touchesCovered y n ft = false → ft ∈ net') :
    ∀ a, ReachAInj net envs a0 a ↔ ReachAInj net' envs a0 a := by
  intro a
  constructor
  · intro h
    induction h with
    | init => exact ReachAInj.init
    | @step a1 ft hr hmem hen ih =>
      cases ht : touchesCovered y n ft with
      | true =>
        have hdead := covered_transition_dead_inj hv hy h0 hmem ht a1 hr
        rw [hdead] at hen
        exact Bool.noConfusion hen
      | false => exact ReachAInj.step ih (hkeep ft hmem ht) hen
    | @inject a1 pinj hr hpin ih => exact ReachAInj.inject ih hpin
  · intro h
    induction h with
    | init => exact ReachAInj.init
    | @step a1 ft hr hmem hen ih => exact ReachAInj.step ih (hsub ft hmem) hen
    | @inject a1 pinj hr hpin ih => exact ReachAInj.inject ih hpin

end Libpetri
