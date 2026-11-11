import Libpetri.Spec.Registry
import Libpetri.StateEquation
import Libpetri.Novel.Certificate

set_option linter.missingDocs true

/-!
# VER-016: State-equation strengthening with firing counters (`spec/07-verification.md`)

With the option enabled the flat CHC encoding runs over augmented states `(M, n)`: one firing
counter per flat transition after the places. The initial fact sets every counter to 0, a
transition rule adds one to its own counter and copies the others, an injection rule copies all
of them, and every transition rule conjoins one row per non-injected place: the marking equation
`m'_p = M0_p + Σ_t C[p][t]·n'_t`, or its upper bound where a consume-all or reset arc clears `p`.

The requirement is a predicate over a pair `(I, R)`:

* `I : CntInit`, the initial fact: the augmented state it seeds for an initial marking;
* `R : CntRuleRel`, the rules read as a step relation on augmented states, for a flat net, its
  injected places, its place count and its initial marking (the rule relation of the encoding,
  not a row emitter).

The witness pair is `refCntInit` and `refRules`, the shipped rules (`StepCntStrRel`,
`StateEquation.lean`) without P-invariant laws. Lines 2 to 5 pin `R` from above and from below
on every augmented state, reachable or not, so the statement determines `R` up to logical
equivalence (`VER_016_unique`). The statement is checked against the witness
(`VER_016_reference`) and against ten wrong models, at least one per line: an initial fact
with non-zero counters, rules that bump two counters, rules without rows, the upper bound on
every place, the equality row on a cleared place, a row on an injected place, rows over the
source, rows over the old counters, the raw steps restricted to reachable sources, and an
injection guarded on an empty place. From the statement alone, the rules reach exactly the
augmented states the raw counter steps reach (`VER_016_reach_iff`), hence exactly the markings
of the abstraction with injection (`VER_016_markings`), and every row holds on all of them
(`VER_016_rows_hold`). The certificate side of AC3 is cited through
`Novel.Certificate.vc_sound_state_equation` (`VER_016_certificate`).
-/

namespace Libpetri.Spec

open Libpetri (FlatNet PlaceId AMarking Counters StepCntRel StepCntStrRel ReachCnt ReachAInj
  ProvenFor bump rowRhs cleared enabledA fireA)

/-! ## The model -/

/-- The initial fact of the encoding: `I a0` is the augmented state `(M, n)` it seeds for the
initial marking `a0`. -/
abbrev CntInit : Type := AMarking → AMarking × Counters

/-- The rules of the encoding with the option enabled, read as a step relation:
`R net envs w a0 s s'` says one rule (a transition rule or an environment-injection rule) of the
flat net `net` with the injected places `envs`, `w` places and the initial marking `a0` takes the
augmented state `s` to `s'`. -/
abbrev CntRuleRel : Type :=
  FlatNet → List PlaceId → Nat → AMarking → (AMarking × Counters) → (AMarking × Counters) → Prop

/-- The reference initial fact: the initial marking and every counter 0. -/
def refCntInit : CntInit := fun a0 => (a0, fun _ => 0)

/-- The reference rules: the shipped options-on rules (`StepCntStrRel`, `encode_net`,
`smt_encoder.rs`) with no P-invariant law; each transition rule conjoins the row of every
non-injected place below `w`, and each injection rule conjoins nothing. -/
def refRules : CntRuleRel := fun net envs w a0 => StepCntStrRel net envs [] w a0

#spec_witness refCntInit
#spec_witness refRules

/-! ## VER-016: State-equation strengthening with firing counters -/

requirement VER_016
  id "VER-016"
  title "State-Equation Strengthening with Firing Counters"
  kind B
  scope "the flat CHC encoding of every implementation, with the state-equation option enabled"
  source verbatim "spec/07-verification.md"
  quote "*While* the state-equation option is enabled, the initial fact of the flat CHC encoding *shall* set every firing counter to 0."
        "*While* the option is enabled, the rule of each transition *shall* fire that transition only where it is enabled, with the effect it has in the untimed abstraction of [VER-004], add one to its firing counter and copy every other counter, each environment-injection rule *shall* add one token to its place and copy every counter, and no rule but these and the initial fact *shall* derive a `Reachable` fact."
        "*While* the option is enabled, each transition rule *shall* require of its successor `(M', n')`, for every place that is not injected, the equality `m'_p = M0_p + Σ_t C[p][t]·n'_t` where no consume-all or reset arc clears the place, and the upper bound `m'_p ≤ M0_p + Σ_t C[p][t]·n'_t` where one does."
        "*While* the option is enabled, apart from the P-invariant conjuncts of [VER-005] and [VER-007] and the environment bounds of [VER-006], the rule of each transition *shall* accept its firing from every state `(M, n)` in which the transition is enabled and whose successor meets the rows above, and each environment-injection rule *shall* accept its injection from every state, so the rows remove no reachable state."
  reading "For every initial fact I and rule relation R:"
          "the initial fact for a0 is (a0, n) with every counter of n equal to 0;"
          "every rule step is a raw counter step: a firing of an enabled transition k (fireA) that bumps counter k and copies the rest, or an injection of one token into an injected place that copies every counter;"
          "whenever a rule takes any augmented state s by the firing of transition k to its successor, every place below the place count w that is not injected satisfies its row there (Libpetri.Row: the upper bound where some transition clears the place with a reset or consume-all arc, the equality elsewhere);"
          "from any augmented state s, reachable or not, the firing of an enabled transition k whose successor satisfies the row of every place below w that is not injected is a rule step;"
          "from any augmented state s, the injection of one token into an injected place, with every counter copied, is a rule step."
  assumes "The model is the pair (I, R) of CntInit and CntRuleRel over the untimed abstraction of VER-004 with injection: a flat net (FlatNet: transition and output places, the abstract semantics enabledA and fireA), its injected places envs, its place count w and its initial marking a0. Augmented states pair a count marking with Counters (Nat-valued, so the conjoined n' >= 0 holds by construction). The witness pair is refCntInit and refRules (StepCntStrRel with no P-invariant law)."
          "w stands for the place count P of the flat net, so every place an arc of the net touches lies below it; places at or beyond w are outside the encoding. The statement quantifies over every w, and refRules carries the rows of exactly the places below w."
          "R models the counter and row part of the rules. The P-invariant laws the rules also conjoin are VER-005 and VER-007's, and conjoining gate-validated laws together with the rows removes no reachable state (state_equation_reach_eq). The environment mode is AlwaysAvailable: the Bounded(k) cap on the injection rule and the environment bounds on the successor of a transition rule are VER-006's, only remove steps, and are not modelled (rows_hold still applies to the capped rules). These are the conjuncts the fourth quoted sentence sets apart."
          "Line 2 is the second quoted sentence: the marking half (enabledness, fireA, one token per injection, no rule but these and the initial fact) is the untimed abstraction of VER-004 with the injection of VER-006, and the counter half is the bump and the copy. Line 3 is the third quoted sentence, stated for every augmented state: the rule carries the row, not only that reachable states satisfy it. Lines 4 and 5 are the fourth quoted sentence: the rule requires of the source nothing beyond enabling and the successor rows, so a guard on the source rows (VER_016_forbids_srcRow), a guard on reachability (VER_016_forbids_reachOnly) or a guarded injection (VER_016_forbids_injEmpty) is ruled out, and the rows remove no reachable state (VER_016_reach_iff)."
          "Lines 2 to 5 determine R up to logical equivalence: on every pair satisfying VER-016, R is refRules (VER_016_unique). So a row on an injected place and the equality row on a cleared place are ruled out wherever they would refuse a step (VER_016_forbids_injRow, VER_016_forbids_eqRow), as are rows over the source or over the old counters (VER_016_forbids_oldCnt) and the upper bound on an exact place (VER_016_forbids_leAll). A conjunct that refuses no step is invisible at the level of the relation; that the script emits no such text is script text (AC2, the parity goldens of VER-013)."
          "The body's description of the rules ('the initial fact has n = 0', the counter update, the injection rule, 'in the same position', 'in transition order') is lines 1 to 5; the position and order of the conjuncts in the script are text and are not modelled. The inductiveness argument ('a clearing step's guard needs m_p >= pre_p') is row_fire, behind VER_016_reach_iff. 'The error rule quantifies the counters and constrains the marking only' is the violation of VER_016_certificate, which reads the marking only. 'The counterexample decoder reads a fact's marking from its leading P arguments' is the decoder's text and is not modelled."
          "The second paragraph (every linear consequence of the marking equation is a fact in every rule body; the 50-place agent-dispatch figures) is a motivation and a performance figure (kind Q); it states no line. The soundness sentence ('the counters are exact bookkeeping, so every row holds on every reachable augmented state and conjoining them removes none') is VER_016_rows_hold and VER_016_reach_iff, and VER_016_markings says the option neither adds nor loses a marking of the abstraction with injection."
          "'The option is off by default' and 'about 1.5x slower' are configuration (kind N) and a performance figure (kind Q). With the option off the encoding is VER-001's and this block says nothing."
          "The sentence on the certificate check is VER_016_certificate: a candidate over (M, n) that passes the three verification conditions against the raw counter step relation StepCntRel from (a0, 0), with a violation that reads the marking only, proves the property for every marking of the abstraction with injection (Novel.Certificate.vc_sound_state_equation). The composition of the candidate (the P-invariants, n >= 0 and the marking equation) is not modelled: VER_016_certificate covers any candidate over (M, n), not that the shipped one contains the marking equation; that is deferred to the pipeline model (RefVerifier, wave W10). That the check is on by default and that a caller may disable it, in which case a Proven rests on the solver's answer alone and the report says 'not applicable (disabled)', is configuration and report text (kind N and Q, ruling D52 (a))."
          "'The option does not apply to the name-coloured encoding or to Route B' is the scope of this block (the flat encoding). The report line for the name-coloured path is AC4 below."
          "AC1 (byte identity with the option disabled) and AC5 (byte identity of the HORN and certificate scripts across the four implementations) are about the SMT-LIB text, which is not modelled; they are checked by the golden-script parity tests of VER-013 (kind Q)."
          "AC2 (arity P + T, the initial fact ends in T zeros, the counter equalities of rule t, the marking equation of every exact place over the primed variables, the upper bound on a consume-all or reset place, none on an injected place) is lines 1 to 5 at the constraint level, with VER_016_unique for 'instead' and 'none' as above; the arity and the SMT-LIB spelling are text (kind Q, the parity goldens of VER-013). It is checked on the reference by VER_016_nonvacuous: on a net whose only transition drains place 0 with a consume-all arc, the firing rule exists from the initial fact and its successor meets the upper bound while the equality would fail; an injection rule copies the counters; and a firing from a state off the equation is refused."
          "AC3 (while the certificate check is enabled, a Proven that the fixpoint query decides passes the check with the equation in the candidate; a genuine violation stays Violated and its counterexample replays) is VER_016_certificate for the soundness of a check over (M, n), and VER_016_reach_iff with VER_016_markings for the violation: the rules remove no reachable marking, so a violating marking stays reachable. The content of the candidate, that the fixpoint query decides, the verdict and the replay are the pipeline's (RefVerifier, wave W10) and are not modelled here."
          "AC4 (the report lines 'State equation: encoded over T firing counters (VER-016)' when the option applied and 'State equation: not applied (name-coloured encoding)' on the coloured path, no line when a route or phase decides before the fixpoint query) is report text (kind Q), not modelled."
          "The Implementation notes name the per-language option, and the body the per-language certificate switch (kind N). The test derivation (the fork-that-may-halt net of VER-015 with the enumeration budget 0, the witness depth 0, the phases of VER-018 and VER-019 off and this option on, and the unreachable{ra, rb, halt} script) is AC2 to AC4 on fixtures, as above."
  signoff "pending"
  statement : CntInit → CntRuleRel → Prop :=
    fun I R =>
      (∀ a0, I a0 = (a0, fun _ => 0)) ∧
      (∀ net envs w a0 s s', R net envs w a0 s s' → StepCntRel net envs s s') ∧
      (∀ net envs w a0 s k ft, net[k]? = some ft → enabledA s.1 ft.1 = true →
        R net envs w a0 s (fireA s.1 ft.1 ft.2, bump s.2 k) →
        ∀ p, p < w → p ∉ envs → Libpetri.Row net a0 (fireA s.1 ft.1 ft.2) (bump s.2 k) p) ∧
      (∀ net envs (w : Nat) a0 s k ft, net[k]? = some ft → enabledA s.1 ft.1 = true →
        (∀ p, p < w → p ∉ envs → Libpetri.Row net a0 (fireA s.1 ft.1 ft.2) (bump s.2 k) p) →
        R net envs w a0 s (fireA s.1 ft.1 ft.2, bump s.2 k)) ∧
      (∀ net envs w a0 s p, p ∈ envs →
        R net envs w a0 s (fun q => if q == p then s.1 q + 1 else s.1 q, s.2))

/- The pinned readable form of VER-016: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.VER_016 : CntInit → CntRuleRel → Prop :=
fun I R =>
  (∀ (a0 : AMarking), I a0 = (a0, fun x => 0)) ∧
    (∀ (net : FlatNet) (envs : List PlaceId) (w : ℕ) (a0 : AMarking) (s s' : AMarking × Counters),
        R net envs w a0 s s' → StepCntRel net envs s s') ∧
      (∀ (net : FlatNet) (envs : List PlaceId) (w : ℕ) (a0 : AMarking) (s : AMarking × Counters) (k : ℕ)
          (ft : FlatTransition),
          net[k]? = some ft →
            enabledA s.1 ft.1 = true →
              R net envs w a0 s (fireA s.1 ft.1 ft.2, bump s.2 k) →
                ∀ p < w, p ∉ envs → Libpetri.Row net a0 (fireA s.1 ft.1 ft.2) (bump s.2 k) p) ∧
        (∀ (net : FlatNet) (envs : List PlaceId) (w : ℕ) (a0 : AMarking) (s : AMarking × Counters) (k : ℕ)
            (ft : FlatTransition),
            net[k]? = some ft →
              enabledA s.1 ft.1 = true →
                (∀ p < w, p ∉ envs → Libpetri.Row net a0 (fireA s.1 ft.1 ft.2) (bump s.2 k) p) →
                  R net envs w a0 s (fireA s.1 ft.1 ft.2, bump s.2 k)) ∧
          ∀ (net : FlatNet) (envs : List PlaceId) (w : ℕ) (a0 : AMarking) (s : AMarking × Counters),
            ∀ p ∈ envs, R net envs w a0 s (fun q => if (q == p) = true then s.1 q + 1 else s.1 q, s.2)
-/
#guard_msgs in #print VER_016

/-! ## The reference -/

/-- The reference pair satisfies VER-016: the shipped rules are raw counter steps that carry
their rows, accept every enabled firing whose successor meets them, and accept every injection. -/
@[evidence holds VER_016]
theorem VER_016_reference : VER_016 refCntInit refRules := by
  refine ⟨fun _ => rfl, ?_, ?_, ?_, ?_⟩
  · rintro net envs w a0 s s' (⟨k, ft, hk, hen, -, -, rfl⟩ | ⟨p, hp, rfl⟩)
    · exact Or.inl ⟨k, ft, hk, hen, rfl⟩
    · exact Or.inr ⟨p, hp, rfl⟩
  · rintro net envs w a0 s k ft hk hen (⟨k', ft', hk', hen', -, hrow, heq⟩ | ⟨p, hp, heq⟩)
      q hq hqe
    · obtain ⟨h1, h2⟩ := Prod.mk.inj heq
      rw [h1, h2]; exact hrow q hq hqe
    · -- an injection copies every counter, so it is not the firing of `k`
      have := congrArg (fun x => x.2 k) heq
      simp [bump] at this
  · intro net envs w a0 s k ft hk hen hrow
    exact Or.inl ⟨k, ft, hk, hen, by simp, hrow, rfl⟩
  · intro net envs w a0 s p hp
    exact Or.inr ⟨p, hp, rfl⟩

/-! ## What follows from the statement -/

/-- **The statement determines the rules**: on every pair satisfying VER-016 the rule relation
is the reference one, step for step. -/
theorem VER_016_unique {I : CntInit} {R : CntRuleRel} (h : VER_016 I R)
    (net : FlatNet) (envs : List PlaceId) (w : Nat) (a0 : AMarking)
    (s s' : AMarking × Counters) :
    R net envs w a0 s s' ↔ refRules net envs w a0 s s' := by
  obtain ⟨-, h2, h3, h4, h5⟩ := h
  constructor
  · intro hR
    rcases h2 net envs w a0 s s' hR with ⟨k, ft, hk, hen, rfl⟩ | ⟨p, hp, rfl⟩
    · exact Or.inl ⟨k, ft, hk, hen, by simp, h3 net envs w a0 s k ft hk hen hR, rfl⟩
    · exact Or.inr ⟨p, hp, rfl⟩
  · rintro (⟨k, ft, hk, hen, -, hrow, rfl⟩ | ⟨p, hp, rfl⟩)
    · exact h4 net envs w a0 s k ft hk hen hrow
    · exact h5 net envs w a0 s p hp

/-- **The rows remove no state**, from the statement alone: on every pair satisfying VER-016,
the augmented states the rules reach from the initial fact are exactly those the raw counter
steps reach from `(a0, 0)`. -/
theorem VER_016_reach_iff {I : CntInit} {R : CntRuleRel} (h : VER_016 I R)
    (net : FlatNet) (envs : List PlaceId) (w : Nat) (a0 : AMarking) (s : AMarking × Counters) :
    Relation.ReflTransGen (R net envs w a0) (I a0) s ↔ ReachCnt net envs a0 s.1 s.2 := by
  have hR : R net envs w a0 = refRules net envs w a0 := by
    funext x y
    exact propext (VER_016_unique h net envs w a0 x y)
  rw [h.1 a0, hR]
  exact (Libpetri.state_equation_reach_eq (ys := []) (w := w) (by simp) s.1 s.2).symm

/-- **The counters are bookkeeping**, from the statement alone: the markings the rules reach
are exactly the markings of the abstraction with injection (`counters_erase`,
`counters_exist`), so the option neither adds nor loses a marking and a violating marking stays
reachable. -/
theorem VER_016_markings {I : CntInit} {R : CntRuleRel} (h : VER_016 I R)
    (net : FlatNet) (envs : List PlaceId) (w : Nat) (a0 a : AMarking) :
    (∃ n, Relation.ReflTransGen (R net envs w a0) (I a0) (a, n)) ↔ ReachAInj net envs a0 a := by
  constructor
  · rintro ⟨n, hr⟩
    exact Libpetri.counters_erase ((VER_016_reach_iff h net envs w a0 (a, n)).mp hr)
  · intro hr
    obtain ⟨n, hn⟩ := Libpetri.counters_exist hr
    exact ⟨n, (VER_016_reach_iff h net envs w a0 (a, n)).mpr hn⟩

/-- **Every row holds on every reachable augmented state**, from the statement alone. -/
theorem VER_016_rows_hold {I : CntInit} {R : CntRuleRel} (h : VER_016 I R)
    {net : FlatNet} {envs : List PlaceId} {w : Nat} {a0 a : AMarking} {n : Counters}
    (hr : Relation.ReflTransGen (R net envs w a0) (I a0) (a, n)) :
    ∀ p, p ∉ envs → Libpetri.Row net a0 a n p :=
  Libpetri.rows_hold ((VER_016_reach_iff h net envs w a0 (a, n)).mp hr)

/-- **The certificate over `(M, n)` is sound** ([VER-016] AC3): a candidate that passes init,
consecution and safety against the raw counter step relation from `(a0, 0)`, with a violation
that reads the marking only, proves the property for every marking of the abstraction with
injection. Restates `Novel.Certificate.vc_sound_state_equation`. -/
@[evidence cites "VER-016" "AC3: a certificate over (M, n) passing init, consecution and safety against the raw counter step relation StepCntRel from (a0, 0), with a violation that reads the marking only, proves the property for every marking of ReachAInj; the composition of the candidate is not covered"]
theorem VER_016_certificate {net : FlatNet} {envs : List PlaceId} {a0 : AMarking}
    {Bad : AMarking → Prop} {Inv : AMarking × Counters → Prop}
    (h : Novel.Certificate.VCs (StepCntRel net envs) (refCntInit a0) (fun s => Bad s.1) Inv) :
    ProvenFor (ReachAInj net envs a0) Bad :=
  Novel.Certificate.vc_sound_state_equation h

/-! ## Examples -/

/-- `t`: one token from place `0` to place `1`. -/
def ver016_t : Libpetri.Transition :=
  { name := "t", inputs := [{ place := 0, card := .one, guard := none }],
    inhibitors := [], reads := [], resets := [] }

/-- The net with the one transition `t`. -/
def ver016_net : FlatNet := [(ver016_t, [1])]

/-- The empty marking. -/
def ver016_empty : AMarking := fun _ => 0

/-- One token in place `0`. -/
def ver016_one0 : AMarking := fun p => if p = 0 then 1 else 0

/-- Two tokens in place `0`. -/
def ver016_two0 : AMarking := fun p => if p = 0 then 2 else 0

/-- Five tokens in place `0`: on `netAll` with `a0All` this is off the upper-bound row of the
cleared place `0` (`5 ≤ 2` fails), so it is not reachable. -/
def ver016_five0 : AMarking := fun p => if p = 0 then 5 else 0

/-- After `t` fires from `({0: 1}, 0)` with the empty initial marking, place `0` misses its row:
it holds `0` where the equation says `0 - 1`. -/
theorem ver016_row0_off :
    ¬ Libpetri.Row ver016_net ver016_empty (fireA ver016_one0 ver016_t [1])
      (bump (fun _ => 0) 0) 0 := by
  unfold Libpetri.Row
  decide

/-- From `({0: 5}, 0)` on `netAll` with `a0All`, the successor of `drain_all` meets the row of
both places: place `0` is empty (`0 ≤ 1`) and place `1` holds the one token the equation says. -/
theorem ver016_five0_rows :
    ∀ p : Nat, p < 2 → p ∉ ([] : List PlaceId) →
      Libpetri.Row Libpetri.netAll Libpetri.a0All (fireA ver016_five0 Libpetri.tAll [1])
        (bump (fun _ => 0) 0) p := by
  intro p hp _
  rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;> (unfold Libpetri.Row; decide)

/-- ✓ **AC2 on the reference.** On `netAll` (`drain_all` clears place `0`, which holds two
tokens, with a consume-all arc), the firing rule exists from the initial fact and its successor
meets the upper bound of place `0` although the equality would fail; an injection into place
`0` of `ver016_net` copies the counters; and from the augmented state `({0: 1}, 0)` with the empty
initial marking, which is off the equation, the rule refuses the firing of `t`. -/
@[evidence nonvacuous VER_016]
theorem VER_016_nonvacuous :
    refRules Libpetri.netAll [] 1 Libpetri.a0All (refCntInit Libpetri.a0All)
        (fireA Libpetri.a0All Libpetri.tAll [1], bump (fun _ => 0) 0) ∧
      ((fireA Libpetri.a0All Libpetri.tAll [1] 0 : Nat) : Int) ≠
        rowRhs Libpetri.netAll Libpetri.a0All (bump (fun _ => 0) 0) 0 ∧
      refRules ver016_net [0] 2 ver016_empty (ver016_empty, fun _ => 0)
        (ver016_one0, fun _ => 0) ∧
      ¬ refRules ver016_net [] 2 ver016_empty (ver016_one0, fun _ => 0)
        (fireA ver016_one0 ver016_t [1], bump (fun _ => 0) 0) := by
  obtain ⟨-, -, hne, hrow⟩ := Libpetri.equality_row_is_unsound_on_a_clearing_place
  refine ⟨Or.inl ⟨0, (Libpetri.tAll, [1]), rfl, by decide, by simp, fun p hp _ => ?_, rfl⟩,
    hne, Or.inr ⟨0, by simp, ?_⟩, ?_⟩
  · obtain rfl : p = 0 := by omega
    exact hrow
  · refine Prod.ext (funext fun q => ?_) rfl
    by_cases hq : q = 0 <;> simp [ver016_one0, ver016_empty, hq]
  · rintro (⟨k, ft, hk, -, -, hrow', heq⟩ | ⟨p, hp, -⟩)
    · have hk0 : k = 0 := by
        have := congrArg (fun x => x.2 0) heq
        by_contra hne'
        simp [bump] at this
        omega
      subst hk0
      have hft : ft = (ver016_t, [1]) := by
        have : ver016_net[0]? = some (ver016_t, [1]) := rfl
        rw [this] at hk; exact (Option.some.inj hk).symm
      subst hft
      exact ver016_row0_off (hrow' 0 (by omega) (by simp))
    · simp at hp

/-! ## Wrong models -/

/-- An initial fact that starts every counter at 1. -/
def ver016_initOne : CntInit := fun a0 => (a0, fun _ => 1)

/-- ✗ Line 1 forbids an initial fact with a non-zero counter. -/
@[evidence forbids VER_016]
theorem VER_016_forbids_initOne : ¬ VER_016 ver016_initOne refRules := by
  intro h
  have := congrArg (fun s => s.2 0) (h.1 ver016_empty)
  simp [ver016_initOne] at this

/-- Rules whose firing of `k` bumps the counters of `k` and of `k + 1`. -/
def ver016_bumpTwo : CntRuleRel := fun net envs _ _ s s' =>
  (∃ k ft, net[k]? = some ft ∧ enabledA s.1 ft.1 = true ∧
      s' = (fireA s.1 ft.1 ft.2, bump (bump s.2 k) (k + 1)))
  ∨ ∃ p ∈ envs, s' = (fun q => if q == p then s.1 q + 1 else s.1 q, s.2)

/-- ✗ Line 2 forbids a rule that bumps two counters: the firing of `t` from `({0: 1}, 0)` also
bumps counter `1`, which no transition of the net has. -/
@[evidence forbids VER_016]
theorem VER_016_forbids_bumpTwo : ¬ VER_016 refCntInit ver016_bumpTwo := by
  intro h
  have hs := h.2.1 ver016_net [] 2 ver016_one0 (ver016_one0, fun _ => 0)
    (fireA ver016_one0 ver016_t [1], bump (bump (fun _ => 0) 0) 1)
    (Or.inl ⟨0, (ver016_t, [1]), rfl, by decide, rfl⟩)
  rcases hs with ⟨k, ft, hk, -, heq⟩ | ⟨p, hp, -⟩
  · have h1 := congrArg (fun x => x.2 1) heq
    by_cases hk1 : k = 1
    · subst hk1; simp [ver016_net] at hk
    · simp [bump, Ne.symm hk1] at h1
  · simp at hp

/-- Rules without rows: the raw counter steps themselves. -/
def ver016_noRow : CntRuleRel := fun net envs _ _ => StepCntRel net envs

/-- ✗ Line 3 forbids rules without rows: from `({0: 1}, 0)` with the empty initial marking, off
the equation, the raw firing of `t` gives a successor whose place `0` misses its row. -/
@[evidence forbids VER_016]
theorem VER_016_forbids_noRow : ¬ VER_016 refCntInit ver016_noRow := by
  intro h
  have := h.2.2.1 ver016_net [] 2 ver016_empty (ver016_one0, fun _ => 0) 0 (ver016_t, [1]) rfl
    (by decide) (Or.inl ⟨0, (ver016_t, [1]), rfl, by decide, rfl⟩) 0 (by omega) (by simp)
  exact ver016_row0_off this

/-- Rules with the upper bound on every non-injected place, exact or cleared: the sound but
weaker row everywhere. -/
def ver016_leAll : CntRuleRel := fun net envs w a0 s s' =>
  (∃ k ft, net[k]? = some ft ∧ enabledA s.1 ft.1 = true ∧
      (∀ p, p < w → p ∉ envs →
        ((fireA s.1 ft.1 ft.2 p : Nat) : Int) ≤ rowRhs net a0 (bump s.2 k) p) ∧
      s' = (fireA s.1 ft.1 ft.2, bump s.2 k))
  ∨ ∃ p ∈ envs, s' = (fun q => if q == p then s.1 q + 1 else s.1 q, s.2)

/-- ✗ Line 3 forbids the upper bound on an exact place: with initial marking `{0: 2}` and the
off-equation source `({0: 1}, 0)`, the firing of `t` meets `≤` on both places (`0 ≤ 1`,
`1 ≤ 1`), so the rule takes it, but the exact place `0` needs `0 = 1`. -/
@[evidence forbids VER_016]
theorem VER_016_forbids_leAll : ¬ VER_016 refCntInit ver016_leAll := by
  intro h
  have hR : ver016_leAll ver016_net [] 2 ver016_two0 (ver016_one0, fun _ => 0)
      (fireA ver016_one0 ver016_t [1], bump (fun _ => 0) 0) :=
    Or.inl ⟨0, (ver016_t, [1]), rfl, by decide, fun p hp _ => by
      rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;> decide, rfl⟩
  have h0 := h.2.2.1 ver016_net [] 2 ver016_two0 (ver016_one0, fun _ => 0) 0 (ver016_t, [1])
    rfl (by decide) hR 0 (by omega) (by simp)
  revert h0; unfold Libpetri.Row; decide

/-- Rules with the equality row on every non-injected place, cleared or not. -/
def ver016_eqRow : CntRuleRel := fun net envs w a0 s s' =>
  (∃ k ft, net[k]? = some ft ∧ enabledA s.1 ft.1 = true ∧
      (∀ p, p < w → p ∉ envs →
        ((fireA s.1 ft.1 ft.2 p : Nat) : Int) = rowRhs net a0 (bump s.2 k) p) ∧
      s' = (fireA s.1 ft.1 ft.2, bump s.2 k))
  ∨ ∃ p ∈ envs, s' = (fun q => if q == p then s.1 q + 1 else s.1 q, s.2)

/-- ✗ Line 4 forbids the equality row on a cleared place: on `netAll` the firing of
`drain_all` from the initial fact has a successor that meets the upper bound, so the rules
must take it, and the equality row refuses it (`equality_row_is_unsound_on_a_clearing_place`). -/
@[evidence forbids VER_016]
theorem VER_016_forbids_eqRow : ¬ VER_016 refCntInit ver016_eqRow := by
  intro h
  obtain ⟨-, -, hne, hrow⟩ := Libpetri.equality_row_is_unsound_on_a_clearing_place
  have h4 := h.2.2.2.1 Libpetri.netAll [] 1 Libpetri.a0All (Libpetri.a0All, fun _ => 0) 0
    (Libpetri.tAll, [1]) rfl (by decide) (fun p hp _ => by
      obtain rfl : p = 0 := by omega
      exact hrow)
  rcases h4 with ⟨k, ft, hk, -, hrow', heq⟩ | ⟨p, hp, -⟩
  · have hk0 : k = 0 := by
      have := congrArg (fun x => x.2 0) heq
      by_contra hne'
      simp [bump] at this
      omega
    subst hk0
    have hft : ft = (Libpetri.tAll, [1]) := by
      have : Libpetri.netAll[0]? = some (Libpetri.tAll, [1]) := rfl
      rw [this] at hk; exact (Option.some.inj hk).symm
    subst hft
    exact hne (hrow' 0 (by omega) (by simp))
  · simp at hp

/-- Rules that also conjoin the row of an injected place. -/
def ver016_injRow : CntRuleRel := fun net envs w a0 s s' =>
  (∃ k ft, net[k]? = some ft ∧ enabledA s.1 ft.1 = true ∧
      (∀ p, p < w → Libpetri.Row net a0 (fireA s.1 ft.1 ft.2) (bump s.2 k) p) ∧
      s' = (fireA s.1 ft.1 ft.2, bump s.2 k))
  ∨ ∃ p ∈ envs, s' = (fun q => if q == p then s.1 q + 1 else s.1 q, s.2)

/-- ✗ Line 4 forbids a row on an injected place: with place `0` injected and the empty initial
marking, the firing of `t` from `({0: 1}, 0)` has a successor whose only non-injected place `1`
meets its row, so the rules must take it; the row of place `0` would need `0 = 0 - 1`. -/
@[evidence forbids VER_016]
theorem VER_016_forbids_injRow : ¬ VER_016 refCntInit ver016_injRow := by
  intro h
  have h4 := h.2.2.2.1 ver016_net [0] 2 ver016_empty (ver016_one0, fun _ => 0) 0
    (ver016_t, [1]) rfl (by decide) (fun p hp hpe => by
      obtain rfl : p = 1 := by simp at hpe; omega
      unfold Libpetri.Row; decide)
  rcases h4 with ⟨k, ft, hk, -, hrow, heq⟩ | ⟨p, -, heq⟩
  · have hk0 : k = 0 := by
      have := congrArg (fun x => x.2 0) heq
      by_contra hne'
      simp [bump] at this
      omega
    subst hk0
    have hft : ft = (ver016_t, [1]) := by
      have : ver016_net[0]? = some (ver016_t, [1]) := rfl
      rw [this] at hk; exact (Option.some.inj hk).symm
    subst hft
    exact ver016_row0_off (hrow 0 (by omega))
  · have := congrArg (fun x => x.2 0) heq
    simp [bump] at this

/-- Rules that conjoin the rows over the source `(M, n)` instead of the successor `(M', n')`:
the primed-variable slip. -/
def ver016_srcRow : CntRuleRel := fun net envs w a0 s s' =>
  (∃ k ft, net[k]? = some ft ∧ enabledA s.1 ft.1 = true ∧
      (∀ p, p < w → p ∉ envs → Libpetri.Row net a0 s.1 s.2 p) ∧
      s' = (fireA s.1 ft.1 ft.2, bump s.2 k))
  ∨ ∃ p ∈ envs, s' = (fun q => if q == p then s.1 q + 1 else s.1 q, s.2)

/-- ✗ Line 4 forbids rows over the source: from `({0: 5}, 0)` on `netAll` with `a0All` the
successor of `drain_all` meets both rows, so the rules must take it, but the source row of the
cleared place `0` needs `5 ≤ 2`. -/
@[evidence forbids VER_016]
theorem VER_016_forbids_srcRow : ¬ VER_016 refCntInit ver016_srcRow := by
  intro h
  have h4 := h.2.2.2.1 Libpetri.netAll [] 2 Libpetri.a0All (ver016_five0, fun _ => 0) 0
    (Libpetri.tAll, [1]) rfl (by decide) ver016_five0_rows
  rcases h4 with ⟨k, ft, hk, hen, hrow, heq⟩ | ⟨p, hp, -⟩
  · have h0 := hrow 0 (by omega) (by simp)
    revert h0; unfold Libpetri.Row; decide
  · simp at hp

/-- Rules that conjoin the rows over the successor marking with the old counters `n`. -/
def ver016_oldCnt : CntRuleRel := fun net envs w a0 s s' =>
  (∃ k ft, net[k]? = some ft ∧ enabledA s.1 ft.1 = true ∧
      (∀ p, p < w → p ∉ envs → Libpetri.Row net a0 (fireA s.1 ft.1 ft.2) s.2 p) ∧
      s' = (fireA s.1 ft.1 ft.2, bump s.2 k))
  ∨ ∃ p ∈ envs, s' = (fun q => if q == p then s.1 q + 1 else s.1 q, s.2)

/-- ✗ Line 4 forbids rows over the old counters: on `ver016_net` from the initial fact
`({0: 1}, 0)` the firing of `t` meets both rows over `n'`, so the rules must take it, but over
the old counters place `0` needs `0 = 1`. -/
@[evidence forbids VER_016]
theorem VER_016_forbids_oldCnt : ¬ VER_016 refCntInit ver016_oldCnt := by
  intro h
  have h4 := h.2.2.2.1 ver016_net [] 2 ver016_one0 (ver016_one0, fun _ => 0) 0
    (ver016_t, [1]) rfl (by decide) (fun p hp _ => by
      rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;> (unfold Libpetri.Row; decide))
  rcases h4 with ⟨k, ft, hk, -, hrow, heq⟩ | ⟨p, hp, -⟩
  · have hk0 : k = 0 := by
      have := congrArg (fun x => x.2 0) heq
      by_contra hne'
      simp [bump] at this
      omega
    subst hk0
    have hft : ft = (ver016_t, [1]) := by
      have : ver016_net[0]? = some (ver016_t, [1]) := rfl
      rw [this] at hk; exact (Option.some.inj hk).symm
    subst hft
    have h0 := hrow 0 (by omega) (by simp)
    revert h0; unfold Libpetri.Row; decide
  · simp at hp

/-- The raw counter steps restricted to sources the raw counter steps reach, with no row. -/
def ver016_reachOnly : CntRuleRel := fun net envs _ a0 s s' =>
  ReachCnt net envs a0 s.1 s.2 ∧ StepCntRel net envs s s'

/-- ✗ Line 4 forbids a guard on reachability: the firing of `drain_all` from `({0: 5}, 0)` on
`netAll` meets both rows, so the rules must take it, but `({0: 5}, 0)` is not reachable from
`{0: 2}` (every reachable state meets the row `m_0 ≤ 2` of the cleared place). -/
@[evidence forbids VER_016]
theorem VER_016_forbids_reachOnly : ¬ VER_016 refCntInit ver016_reachOnly := by
  intro h
  obtain ⟨hr, -⟩ := h.2.2.2.1 Libpetri.netAll [] 2 Libpetri.a0All (ver016_five0, fun _ => 0) 0
    (Libpetri.tAll, [1]) rfl (by decide) ver016_five0_rows
  have h0 := Libpetri.rows_hold hr 0 (by simp)
  revert h0; unfold Libpetri.Row; decide

/-- The reference firing rules with an injection guarded on an empty place. -/
def ver016_injEmpty : CntRuleRel := fun net envs w a0 s s' =>
  (∃ k ft, net[k]? = some ft ∧ enabledA s.1 ft.1 = true ∧
      (∀ p, p < w → p ∉ envs → Libpetri.Row net a0 (fireA s.1 ft.1 ft.2) (bump s.2 k) p) ∧
      s' = (fireA s.1 ft.1 ft.2, bump s.2 k))
  ∨ ∃ p ∈ envs, s.1 p = 0 ∧ s' = (fun q => if q == p then s.1 q + 1 else s.1 q, s.2)

/-- ✗ Line 5 forbids a guarded injection: with place `0` injected, the injection from
`({0: 1}, 0)` must be a rule step, and the guarded rule refuses it. -/
@[evidence forbids VER_016]
theorem VER_016_forbids_injEmpty : ¬ VER_016 refCntInit ver016_injEmpty := by
  intro h
  rcases h.2.2.2.2 ver016_net [0] 2 ver016_empty (ver016_one0, fun _ => 0) 0 (by simp) with
    ⟨k, ft, hk, -, -, heq⟩ | ⟨p, hp, h0, -⟩
  · have := congrArg (fun x => x.2 k) heq
    simp [bump] at this
  · obtain rfl : p = 0 := by simpa using hp
    simp [ver016_one0] at h0

end Libpetri.Spec
