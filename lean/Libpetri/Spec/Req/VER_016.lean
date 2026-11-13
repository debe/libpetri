import Libpetri.Spec.Registry
import Libpetri.StateEquation
import Libpetri.Novel.Certificate
import Libpetri.Novel.ForwardDeposit
import Libpetri.Spec.Text.VER_016

set_option linter.missingDocs true

/-!
# VER-016: State-equation strengthening with firing counters (`spec/07-verification.md`)

With the option enabled the flat CHC encoding runs over augmented states `(M, n)`: one firing
counter per flat transition after the places. The initial fact sets every counter to 0, a
transition rule adds one to its own counter and copies the others, an injection rule copies all
of them, and every transition rule conjoins one row per non-injected place: the marking equation
`m'_p = M0_p + Σ_t C[p][t]·n'_t`, or its upper bound where a consume-all or reset arc clears `p`.

The flat transitions are deposit rows (`CntRows`): a transition and one way its firing can end,
with `d.count p` tokens landing in `p`, as `flatten` builds them (`post[p] += n`,
`net_flattener.rs`). The effect is `fireAD` and the column `C[p][k]` is the deposit count minus
`pre` (`cntCol`), so a row that deposits two tokens in one place (the timeout forward of an
`exactly(2)` input, [IO-014], `Novel/ForwardDeposit.lean`) moves both the marking and the row
by two. On rows that list each place at most once the reference is `StepCntStrRel` of
`StateEquation.lean`, which reads a deposit as a set (`VER_016_unit_rows`).

The requirement is a predicate over a pair `(I, R)`:

* `I : CntInit`, the initial fact: the augmented state it seeds for an initial marking;
* `R : CntRuleRel`, the rules read as a step relation on augmented states, for flat rows, their
  injected places, their place count and their initial marking (the rule relation of the
  encoding, not a row emitter).

The witness pair is `refCntInit` and `refRules`, the shipped rules without P-invariant laws.
Lines 2 to 5 pin `R` from above and from below on every augmented state, reachable or not, so
the statement determines `R` up to logical equivalence (`VER_016_unique`). The statement is
checked against the witness (`VER_016_reference`) and against twelve wrong models, at least one
per line: an initial fact with non-zero counters, rules that bump two counters, rules that read
a deposit as a set, rules without rows, the upper bound on every place, the equality row on a
cleared place, a row on an injected place, rows over the source, rows over the old counters,
rows with the unit column, the raw steps restricted to reachable sources, and an injection
guarded on an empty place. From the statement alone, the rules reach exactly the augmented
states the raw counter steps reach (`VER_016_reach_iff`), hence exactly the markings of the
deposit-row abstraction with injection (`VER_016_markings`), and every row holds on all of them
(`VER_016_rows_hold`). The certificate side of AC3 is `VER_016_certificate`.
-/

namespace Libpetri.Spec

open Libpetri (PlaceId AMarking Counters StepCntStrRel ProvenFor bump cleared enabledA fireA isum)
open Libpetri.Novel.ForwardDeposit (Deposit fireAD ReachADInj tFwd pb)

/-! ## The model -/

/-- The flat rows of the encoding: one row per way a firing can end, a transition and its
deposit (`d.count p` tokens land in `p`), as `flatten` builds them (`post[p] += n`,
`net_flattener.rs`; `NetFlattener.java`; `net-flattener.ts`). -/
abbrev CntRows : Type := List (Libpetri.Transition × Deposit)

/-- The initial fact of the encoding: `I a0` is the augmented state `(M, n)` it seeds for the
initial marking `a0`. -/
abbrev CntInit : Type := AMarking → AMarking × Counters

/-- The rules of the encoding with the option enabled, read as a step relation:
`R rows envs w a0 s s'` says one rule (a transition rule or an environment-injection rule) of
the flat rows `rows` with the injected places `envs`, `w` places and the initial marking `a0`
takes the augmented state `s` to `s'`. -/
abbrev CntRuleRel : Type :=
  CntRows → List PlaceId → Nat → AMarking → (AMarking × Counters) → (AMarking × Counters) → Prop

/-- The column `C[p][k]` of row `k`: its deposit count on `p` minus `pre`, `0` past the end
(`ft.post[p] - ft.pre[p]`, `state_equation_conditions`, `smt_encoder.rs`). -/
def cntCol (rows : CntRows) (k : Nat) (p : PlaceId) : Int :=
  match rows[k]? with
  | some tr => (tr.2.count p : Int) - (Libpetri.pre tr.1 p : Int)
  | none => 0

/-- `M0_p + Σ_k C[p][k]·n_k` over the row indices. -/
def cntRhs (rows : CntRows) (a0 : AMarking) (n : Counters) (p : PlaceId) : Int :=
  (a0 p : Int) + isum (fun k => cntCol rows k p * (n k : Int)) rows.length

/-- The row of `p`: `≤` where some row clears `p` with a reset or consume-all arc, `=`
elsewhere (`state_equation_conditions`, `nonlinear_places`). -/
def CntRow (rows : CntRows) (a0 a : AMarking) (n : Counters) (p : PlaceId) : Prop :=
  if cleared rows p = true then (a p : Int) ≤ cntRhs rows a0 n p
  else (a p : Int) = cntRhs rows a0 n p

/-- `CntRow` is decidable. -/
instance (rows : CntRows) (a0 a : AMarking) (n : Counters) (p : PlaceId) :
    Decidable (CntRow rows a0 a n p) := by
  unfold CntRow; infer_instance

/-- The raw counter step over deposit rows: row `k` fires with its deposit and bumps its
counter, or an injected place receives a token and every counter is copied. -/
def CntStep (rows : CntRows) (envs : List PlaceId) (s s' : AMarking × Counters) : Prop :=
  (∃ k tr, rows[k]? = some tr ∧ enabledA s.1 tr.1 = true ∧
      s' = (fireAD s.1 tr.1 tr.2, bump s.2 k))
  ∨ ∃ p ∈ envs, s' = (fun q => if q == p then s.1 q + 1 else s.1 q, s.2)

/-- The reference initial fact: the initial marking and every counter 0. -/
def refCntInit : CntInit := fun a0 => (a0, fun _ => 0)

/-- The reference rules: the shipped options-on rules (`encode_net`, `smt_encoder.rs`) with no
P-invariant law; each transition rule conjoins the row of every non-injected place below `w`,
and each injection rule conjoins nothing. -/
def refRules : CntRuleRel := fun rows envs w a0 s s' =>
  (∃ k tr, rows[k]? = some tr ∧ enabledA s.1 tr.1 = true ∧
      (∀ p, p < w → p ∉ envs → CntRow rows a0 (fireAD s.1 tr.1 tr.2) (bump s.2 k) p) ∧
      s' = (fireAD s.1 tr.1 tr.2, bump s.2 k))
  ∨ ∃ p ∈ envs, s' = (fun q => if q == p then s.1 q + 1 else s.1 q, s.2)

#spec_witness refCntInit
#spec_witness refRules

/-! ## VER-016: State-equation strengthening with firing counters -/

requirement VER_016
  id "VER-016"
  title "State-Equation Strengthening with Firing Counters"
  kind B
  scope "the flat CHC encoding of every implementation, with the state-equation option enabled"
  source verbatim "spec/07-verification.md"
  covers VER_016.s1, VER_016.s2, VER_016.s3, VER_016.s4
  reading "For every initial fact I and rule relation R:"
          "the initial fact for a0 is (a0, n) with every counter of n equal to 0;"
          "every rule step is a raw counter step (CntStep): the firing of an enabled row k with its deposit (fireAD: count tokens land in each place) that bumps counter k and copies the rest, or an injection of one token into an injected place that copies every counter;"
          "whenever a rule takes any augmented state s by the firing of row k to its successor, every place below the place count w that is not injected satisfies its row there (CntRow, over the columns deposit count minus pre: the upper bound where some row clears the place with a reset or consume-all arc, the equality elsewhere);"
          "from any augmented state s, reachable or not, the firing of an enabled row k whose successor satisfies the row of every place below w that is not injected is a rule step;"
          "from any augmented state s, the injection of one token into an injected place, with every counter copied, is a rule step."
  assumes "The model is the pair (I, R) of CntInit and CntRuleRel over the untimed abstraction of VER-004 with injection: the flat rows (CntRows: one row per way a firing can end, a transition with its deposit, d.count p tokens landing in p; the abstract semantics enabledA and fireAD), the injected places envs, the place count w and the initial marking a0. The column of row k is C[p][k] = d.count p - pre p (cntCol), as flatten writes it (post[p] += n: Rust net_flattener.rs, Java NetFlattener.java, TypeScript net-flattener.ts) and state_equation_conditions reads it (ft.post[p] - ft.pre[p], smt_encoder.rs). So a row that deposits k > 1 tokens in one place, the timeout forward of an exactly(k) input (IO-014, Novel/ForwardDeposit.lean), is covered with its k in both the effect and the column (VER_016_forbids_unitRules, VER_016_forbids_unitColumn). On rows whose deposits list each place at most once (every action branch, IO-011) refRules is StepCntStrRel of StateEquation.lean with no law, which reads a deposit as a set (VER_016_unit_rows). A forward of an all or atLeast input deposits the drained batch, which no row expresses (drained_forward_has_no_row); the verifier refuses such a net before any flat route reads it (branch_outcomes::drained_forward), so that net is outside this block. Augmented states pair a count marking with Counters (Nat-valued, so the conjoined n' >= 0 holds by construction). The witness pair is refCntInit and refRules."
          "w stands for the place count P of the flat net, so every place an arc of the net touches lies below it; places at or beyond w are outside the encoding. The statement quantifies over every w, and refRules carries the rows of exactly the places below w."
          "R models the counter and row part of the rules. The P-invariant laws the rules also conjoin are VER-005 and VER-007's, and conjoining gate-validated laws together with the rows removes no reachable state (state_equation_reach_eq, on rows that list each place at most once). The environment mode is AlwaysAvailable: the Bounded(k) cap on the injection rule and the environment bounds on the successor of a transition rule are VER-006's, only remove steps, and are not modelled (the capped rules reach a subset, so the rows still hold on them). These are the conjuncts the fourth quoted sentence sets apart."
          "Line 2 is the second quoted sentence: the marking half (enabledness, fireAD, one token per injection, no rule but these and the initial fact) is the untimed abstraction of VER-004 over deposit rows with the injection of VER-006, and the counter half is the bump and the copy. Line 3 is the third quoted sentence, stated for every augmented state: the rule carries the row, not only that reachable states satisfy it. Lines 4 and 5 are the fourth quoted sentence: the rule requires of the source nothing beyond enabling and the successor rows, so a guard on the source rows (VER_016_forbids_srcRow), a guard on reachability (VER_016_forbids_reachOnly) or a guarded injection (VER_016_forbids_injEmpty) is ruled out, and the rows remove no reachable state (VER_016_reach_iff)."
          "Lines 2 to 5 determine R up to logical equivalence: on every pair satisfying VER-016, R is refRules (VER_016_unique). So a row on an injected place and the equality row on a cleared place are ruled out wherever they would refuse a step (VER_016_forbids_injRow, VER_016_forbids_eqRow), as are rows over the source or over the old counters (VER_016_forbids_oldCnt), the upper bound on an exact place (VER_016_forbids_leAll), and the unit column on a row that deposits two tokens in one place (VER_016_forbids_unitColumn). A conjunct that refuses no step is invisible at the level of the relation; that the script emits no such text is script text (AC2, the parity goldens of VER-013)."
          "The body's description of the rules ('the initial fact has n = 0', the counter update, the injection rule, 'in the same position', 'in transition order') is lines 1 to 5; the position and order of the conjuncts in the script are text and are not modelled. The inductiveness argument ('a clearing step's guard needs m_p >= pre_p') is ver016_row_fire, behind VER_016_reach_iff. 'The error rule quantifies the counters and constrains the marking only' is the violation of VER_016_certificate, which reads the marking only. 'The counterexample decoder reads a fact's marking from its leading P arguments' is the decoder's text and is not modelled."
          "The second paragraph (every linear consequence of the marking equation is a fact in every rule body; the 50-place agent-dispatch figures) is a motivation and a performance figure (kind Q); it states no line. The soundness sentence ('the counters are exact bookkeeping, so every row holds on every reachable augmented state and conjoining them removes none') is VER_016_rows_hold and VER_016_reach_iff; the StateEquation.lean lemmas the sentence names (rows_hold, state_equation_reach_eq) are their case on rows that list each place at most once (VER_016_unit_rows). VER_016_markings says the option neither adds nor loses a marking of the deposit-row abstraction with injection (ReachADInj)."
          "'The option is off by default' and 'about 1.5x slower' are configuration (kind N) and a performance figure (kind Q). With the option off the encoding is VER-001's and this block says nothing."
          "The sentence on the certificate check is VER_016_certificate: a candidate over (M, n) that passes the three verification conditions against the raw counter step relation CntStep from (a0, 0), with a violation that reads the marking only, proves the property for every marking of ReachADInj (by Novel.Certificate.vc_sound_rel; Novel.Certificate.vc_sound_state_equation is the same result with deposits read as sets). The composition of the candidate (the P-invariants, n >= 0 and the marking equation) is not modelled: VER_016_certificate covers any candidate over (M, n), not that the shipped one contains the marking equation; no block states that: the pipeline model names the certificate check (rtStepNames in Verifier/Pipeline.lean) and does not enter it. That the check is on by default and that a caller may disable it, in which case a Proven rests on the solver's answer alone and the report says 'not applicable (disabled)', is configuration and report text (kind N and Q, ruling D52 (a))."
          "'The option does not apply to the name-coloured encoding or to Route B' is the scope of this block (the flat encoding). The report line for the name-coloured path is AC4 below."
          "AC1 (byte identity with the option disabled) and AC5 (byte identity of the HORN and certificate scripts across the four implementations) are about the SMT-LIB text, which is not modelled; they are checked by the golden-script parity tests of VER-013 (kind Q)."
          "AC2 (arity P + T, the initial fact ends in T zeros, the counter equalities of rule t, the marking equation of every exact place over the primed variables, the upper bound on a consume-all or reset place, none on an injected place) is lines 1 to 5 at the constraint level, with VER_016_unique for 'instead' and 'none' as above; the arity and the SMT-LIB spelling are text (kind Q, the parity goldens of VER-013). It is checked on the reference by VER_016_nonvacuous: on a net whose only transition drains place 0 with a consume-all arc, the firing rule exists from the initial fact and its successor meets the upper bound while the equality would fail; an injection rule copies the counters; a firing from a state off the equation is refused; and on the forward row of exactly(2, a) that deposits two tokens in b, the firing from {a: 2} reaches b = 2 with the row 2 = 0 + 2 n."
          "AC3 (while the certificate check is enabled, a Proven that the fixpoint query decides passes the check with the equation in the candidate; a genuine violation stays Violated and its counterexample replays) is VER_016_certificate for the soundness of a check over (M, n), and VER_016_reach_iff with VER_016_markings for the violation: the rules remove no reachable marking, so a violating marking stays reachable. The content of the candidate, that the fixpoint query decides, the verdict and the replay are the pipeline's and no block states them: the pipeline model (Verifier/Pipeline.lean) names the fixpoint query and the certificate check and does not enter them, and the verdict contract every route meets is VER_003."
          "AC4 (the report lines 'State equation: encoded over T firing counters (VER-016)' when the option applied and 'State equation: not applied (name-coloured encoding)' on the coloured path, no line when a route or phase decides before the fixpoint query) is report text (kind Q), not modelled."
          "The Implementation notes name the per-language option, and the body the per-language certificate switch (kind N). The test derivation (the fork-that-may-halt net of VER-015 with the enumeration budget 0, the witness depth 0, the phases of VER-018 and VER-019 off and this option on, and the unreachable{ra, rb, halt} script) is AC2 to AC4 on fixtures, as above."
  signoff "2026-11-13 103d3b889b9f137a ai"
  statement : CntInit → CntRuleRel → Prop :=
    fun I R =>
      (∀ a0, I a0 = (a0, fun _ => 0)) ∧
      (∀ rows envs w a0 s s', R rows envs w a0 s s' → CntStep rows envs s s') ∧
      (∀ rows envs w a0 s k tr, rows[k]? = some tr → enabledA s.1 tr.1 = true →
        R rows envs w a0 s (fireAD s.1 tr.1 tr.2, bump s.2 k) →
        ∀ p, p < w → p ∉ envs → CntRow rows a0 (fireAD s.1 tr.1 tr.2) (bump s.2 k) p) ∧
      (∀ rows envs (w : Nat) a0 s k tr, rows[k]? = some tr → enabledA s.1 tr.1 = true →
        (∀ p, p < w → p ∉ envs → CntRow rows a0 (fireAD s.1 tr.1 tr.2) (bump s.2 k) p) →
        R rows envs w a0 s (fireAD s.1 tr.1 tr.2, bump s.2 k)) ∧
      (∀ rows envs w a0 s p, p ∈ envs →
        R rows envs w a0 s (fun q => if q == p then s.1 q + 1 else s.1 q, s.2))

/- The pinned readable form of VER-016: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.VER_016 : CntInit → CntRuleRel → Prop :=
fun I R =>
  (∀ (a0 : AMarking), I a0 = (a0, fun x => 0)) ∧
    (∀ (rows : CntRows) (envs : List PlaceId) (w : ℕ) (a0 : AMarking) (s s' : AMarking × Counters),
        R rows envs w a0 s s' → CntStep rows envs s s') ∧
      (∀ (rows : CntRows) (envs : List PlaceId) (w : ℕ) (a0 : AMarking) (s : AMarking × Counters) (k : ℕ)
          (tr : Transition × Deposit),
          rows[k]? = some tr →
            enabledA s.1 tr.1 = true →
              R rows envs w a0 s (fireAD s.1 tr.1 tr.2, bump s.2 k) →
                ∀ p < w, p ∉ envs → CntRow rows a0 (fireAD s.1 tr.1 tr.2) (bump s.2 k) p) ∧
        (∀ (rows : CntRows) (envs : List PlaceId) (w : ℕ) (a0 : AMarking) (s : AMarking × Counters) (k : ℕ)
            (tr : Transition × Deposit),
            rows[k]? = some tr →
              enabledA s.1 tr.1 = true →
                (∀ p < w, p ∉ envs → CntRow rows a0 (fireAD s.1 tr.1 tr.2) (bump s.2 k) p) →
                  R rows envs w a0 s (fireAD s.1 tr.1 tr.2, bump s.2 k)) ∧
          ∀ (rows : CntRows) (envs : List PlaceId) (w : ℕ) (a0 : AMarking) (s : AMarking × Counters),
            ∀ p ∈ envs, R rows envs w a0 s (fun q => if (q == p) = true then s.1 q + 1 else s.1 q, s.2)
-/
#guard_msgs in #print VER_016

/-! ## The reference -/

/-- The reference pair satisfies VER-016: the shipped rules are raw counter steps that carry
their rows, accept every enabled firing whose successor meets them, and accept every injection. -/
@[evidence holds VER_016]
theorem VER_016_reference : VER_016 refCntInit refRules := by
  refine ⟨fun _ => rfl, ?_, ?_, ?_, ?_⟩
  · rintro rows envs w a0 s s' (⟨k, tr, hk, hen, -, rfl⟩ | ⟨p, hp, rfl⟩)
    · exact Or.inl ⟨k, tr, hk, hen, rfl⟩
    · exact Or.inr ⟨p, hp, rfl⟩
  · rintro rows envs w a0 s k tr hk hen (⟨k', tr', hk', hen', hrow, heq⟩ | ⟨p, hp, heq⟩)
      q hq hqe
    · obtain ⟨h1, h2⟩ := Prod.mk.inj heq
      rw [h1, h2]; exact hrow q hq hqe
    · -- an injection copies every counter, so it is not the firing of `k`
      have := congrArg (fun x => x.2 k) heq
      simp [bump] at this
  · intro rows envs w a0 s k tr hk hen hrow
    exact Or.inl ⟨k, tr, hk, hen, hrow, rfl⟩
  · intro rows envs w a0 s p hp
    exact Or.inr ⟨p, hp, rfl⟩

/-! ## The rows hold on the raw counter steps -/

/-- With every counter 0 the right-hand side of a row is the initial count. -/
theorem ver016_cntRhs_zero (rows : CntRows) (a0 : AMarking) (p : PlaceId) :
    cntRhs rows a0 (fun _ => 0) p = a0 p := by
  have : ∀ m, isum (fun k => cntCol rows k p * ((0 : Nat) : Int)) m = 0 := fun m => by
    simp [isum]
  unfold cntRhs
  rw [this]
  omega

/-- Firing row `k` adds its column, deposit count minus `pre`, to the right-hand side. -/
theorem ver016_cntRhs_bump {rows : CntRows} {a0 : AMarking} {n : Counters} {k : Nat}
    {tr : Libpetri.Transition × Deposit} (hk : rows[k]? = some tr) (p : PlaceId) :
    cntRhs rows a0 (bump n k) p
      = cntRhs rows a0 n p + ((tr.2.count p : Int) - (Libpetri.pre tr.1 p : Int)) := by
  have hlt : k < rows.length := (List.getElem?_eq_some_iff.mp hk).1
  have hc : cntCol rows k p = (tr.2.count p : Int) - (Libpetri.pre tr.1 p : Int) := by
    unfold cntCol
    rw [hk]
  unfold cntRhs
  rw [Libpetri.isum_bump _ n hlt, hc]
  omega

/-- One firing preserves the row over deposit rows: the linear arm moves both sides by the
column; a clearing arm leaves the deposit, at most `m − pre + count` because the guard needs
`m ≥ pre`. -/
theorem ver016_row_fire {rows : CntRows} {a0 a : AMarking} {n : Counters} {k : Nat}
    {tr : Libpetri.Transition × Deposit} (hk : rows[k]? = some tr)
    (hen : enabledA a tr.1 = true) {p : PlaceId} (hrow : CntRow rows a0 a n p) :
    CntRow rows a0 (fireAD a tr.1 tr.2) (bump n k) p := by
  have hle := Libpetri.pre_le_of_enabledA hen p
  unfold CntRow at hrow ⊢
  rw [ver016_cntRhs_bump hk p]
  by_cases hcl : cleared rows p = true
  · rw [if_pos hcl] at hrow ⊢
    unfold fireAD
    split
    · omega
    · split <;> omega
  · rw [if_neg hcl] at hrow ⊢
    have hmem := List.mem_of_getElem? hk
    have hlin : ¬ (tr.1.resets.contains p || Libpetri.consumeAllAt tr.1 p) = true :=
      fun h => hcl (List.any_eq_true.mpr ⟨tr, hmem, h⟩)
    simp only [Bool.or_eq_true, not_or] at hlin
    have hfa : fireAD a tr.1 tr.2 p = a p - Libpetri.pre tr.1 p + tr.2.count p := by
      unfold fireAD
      rw [if_neg hlin.1, if_neg hlin.2]
    rw [hfa]
    omega

/-- Every row holds on every augmented state the raw counter steps reach from `(a0, 0)`. -/
theorem ver016_rows_hold {rows : CntRows} {envs : List PlaceId} {a0 : AMarking}
    {s : AMarking × Counters}
    (h : Relation.ReflTransGen (CntStep rows envs) (a0, fun _ => 0) s) :
    ∀ p, p ∉ envs → CntRow rows a0 s.1 s.2 p := by
  induction h with
  | refl =>
    intro p _
    show CntRow rows a0 a0 (fun _ => 0) p
    unfold CntRow
    rw [ver016_cntRhs_zero]
    split <;> omega
  | tail _ hs ih =>
    rcases hs with ⟨k, tr, hk, hen, rfl⟩ | ⟨q, hq, rfl⟩
    · exact fun p hp => ver016_row_fire hk hen (ih p hp)
    · intro p hp
      have hpq : (p == q) = false := by
        simp only [beq_eq_false_iff_ne]
        exact fun h => hp (h ▸ hq)
      have := ih p hp
      unfold CntRow at this ⊢
      simp only [hpq]
      exact this

/-- The reference rules reach from `(a0, 0)` exactly what the raw counter steps reach. -/
theorem ver016_ref_reach_iff (rows : CntRows) (envs : List PlaceId) (w : Nat) (a0 : AMarking)
    (s : AMarking × Counters) :
    Relation.ReflTransGen (refRules rows envs w a0) (a0, fun _ => 0) s ↔
      Relation.ReflTransGen (CntStep rows envs) (a0, fun _ => 0) s := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hs ih =>
      refine Relation.ReflTransGen.tail ih ?_
      rcases hs with ⟨k, tr, hk, hen, -, rfl⟩ | ⟨p, hp, rfl⟩
      · exact Or.inl ⟨k, tr, hk, hen, rfl⟩
      · exact Or.inr ⟨p, hp, rfl⟩
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail hr hs ih =>
      refine Relation.ReflTransGen.tail ih ?_
      rcases hs with ⟨k, tr, hk, hen, rfl⟩ | ⟨p, hp, rfl⟩
      · exact Or.inl ⟨k, tr, hk, hen, fun q _ hq =>
          ver016_rows_hold (Relation.ReflTransGen.tail hr (Or.inl ⟨k, tr, hk, hen, rfl⟩)) q hq,
          rfl⟩
      · exact Or.inr ⟨p, hp, rfl⟩

/-- The counters are bookkeeping: erasing them maps the raw counter steps onto the deposit-row
abstraction with injection. -/
theorem ver016_counters_erase {rows : CntRows} {envs : List PlaceId} {a0 : AMarking}
    {s : AMarking × Counters}
    (h : Relation.ReflTransGen (CntStep rows envs) (a0, fun _ => 0) s) :
    ReachADInj rows envs a0 s.1 := by
  unfold ReachADInj
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih =>
    refine Relation.ReflTransGen.tail ih ?_
    rcases hs with ⟨k, tr, hk, hen, rfl⟩ | ⟨p, hp, rfl⟩
    · exact Or.inl ⟨tr, List.mem_of_getElem? hk, hen, rfl⟩
    · exact Or.inr ⟨p, hp, rfl⟩

/-- Every marking of the deposit-row abstraction with injection carries some counter vector. -/
theorem ver016_counters_exist {rows : CntRows} {envs : List PlaceId} {a0 a : AMarking}
    (h : ReachADInj rows envs a0 a) :
    ∃ n, Relation.ReflTransGen (CntStep rows envs) (a0, fun _ => 0) (a, n) := by
  unfold ReachADInj at h
  induction h with
  | refl => exact ⟨_, Relation.ReflTransGen.refl⟩
  | tail _ hs ih =>
    obtain ⟨n, hn⟩ := ih
    rcases hs with ⟨tr, hmem, hen, rfl⟩ | ⟨p, hp, rfl⟩
    · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hmem
      exact ⟨_, Relation.ReflTransGen.tail hn (Or.inl ⟨k, tr, hk, hen, rfl⟩)⟩
    · exact ⟨_, Relation.ReflTransGen.tail hn (Or.inr ⟨p, hp, rfl⟩)⟩

/-- **On rows that list each place at most once the reference is the shared model**: every
action branch is such a row ([IO-011]), and there `fireAD` is `fireA` and the deposit column is
`post − pre`, so `refRules` is `StepCntStrRel` of `StateEquation.lean` with no law. -/
theorem VER_016_unit_rows {rows : CntRows} (hnd : ∀ tr ∈ rows, tr.2.Nodup)
    (envs : List PlaceId) (w : Nat) (a0 : AMarking) (s s' : AMarking × Counters) :
    refRules rows envs w a0 s s' ↔ StepCntStrRel rows envs [] w a0 s s' := by
  have hcol : ∀ k p, cntCol rows k p = Libpetri.incAt rows k p := by
    intro k p
    unfold cntCol Libpetri.incAt
    cases hk : rows[k]? with
    | none => rfl
    | some tr =>
      simp only
      rw [Libpetri.Novel.ForwardDeposit.post_eq_count (hnd tr (List.mem_of_getElem? hk))]
  have hrow : ∀ a n p, CntRow rows a0 a n p ↔ Libpetri.Row rows a0 a n p := by
    intro a n p
    have : cntRhs rows a0 n p = Libpetri.rowRhs rows a0 n p := by
      unfold cntRhs Libpetri.rowRhs
      simp only [hcol]
    unfold CntRow Libpetri.Row
    rw [this]
  have hfire : ∀ (a : AMarking) (k : Nat) (tr : Libpetri.Transition × Deposit),
      rows[k]? = some tr → fireAD a tr.1 tr.2 = fireA a tr.1 tr.2 :=
    fun a _ tr hk =>
      Libpetri.Novel.ForwardDeposit.fireAD_eq_fireA (hnd tr (List.mem_of_getElem? hk)) a tr.1
  constructor
  · rintro (⟨k, tr, hk, hen, hr, rfl⟩ | ⟨p, hp, rfl⟩)
    · rw [hfire _ k tr hk] at hr ⊢
      exact Or.inl ⟨k, tr, hk, hen, by simp, fun p hp hpe => (hrow _ _ p).mp (hr p hp hpe), rfl⟩
    · exact Or.inr ⟨p, hp, rfl⟩
  · rintro (⟨k, tr, hk, hen, -, hr, rfl⟩ | ⟨p, hp, rfl⟩)
    · rw [← hfire _ k tr hk] at hr ⊢
      exact Or.inl ⟨k, tr, hk, hen, fun p hp hpe => (hrow _ _ p).mpr (hr p hp hpe), rfl⟩
    · exact Or.inr ⟨p, hp, rfl⟩

/-! ## What follows from the statement -/

/-- **The statement determines the rules**: on every pair satisfying VER-016 the rule relation
is the reference one, step for step. -/
theorem VER_016_unique {I : CntInit} {R : CntRuleRel} (h : VER_016 I R)
    (rows : CntRows) (envs : List PlaceId) (w : Nat) (a0 : AMarking)
    (s s' : AMarking × Counters) :
    R rows envs w a0 s s' ↔ refRules rows envs w a0 s s' := by
  obtain ⟨-, h2, h3, h4, h5⟩ := h
  constructor
  · intro hR
    rcases h2 rows envs w a0 s s' hR with ⟨k, tr, hk, hen, rfl⟩ | ⟨p, hp, rfl⟩
    · exact Or.inl ⟨k, tr, hk, hen, h3 rows envs w a0 s k tr hk hen hR, rfl⟩
    · exact Or.inr ⟨p, hp, rfl⟩
  · rintro (⟨k, tr, hk, hen, hrow, rfl⟩ | ⟨p, hp, rfl⟩)
    · exact h4 rows envs w a0 s k tr hk hen hrow
    · exact h5 rows envs w a0 s p hp

/-- **The rows remove no state**, from the statement alone: on every pair satisfying VER-016,
the augmented states the rules reach from the initial fact are exactly those the raw counter
steps reach from `(a0, 0)`. -/
theorem VER_016_reach_iff {I : CntInit} {R : CntRuleRel} (h : VER_016 I R)
    (rows : CntRows) (envs : List PlaceId) (w : Nat) (a0 : AMarking) (s : AMarking × Counters) :
    Relation.ReflTransGen (R rows envs w a0) (I a0) s ↔
      Relation.ReflTransGen (CntStep rows envs) (a0, fun _ => 0) s := by
  have hR : R rows envs w a0 = refRules rows envs w a0 := by
    funext x y
    exact propext (VER_016_unique h rows envs w a0 x y)
  rw [h.1 a0, hR]
  exact ver016_ref_reach_iff rows envs w a0 s

/-- **The counters are bookkeeping**, from the statement alone: the markings the rules reach
are exactly the markings of the deposit-row abstraction with injection, so the option neither
adds nor loses a marking and a violating marking stays reachable. -/
theorem VER_016_markings {I : CntInit} {R : CntRuleRel} (h : VER_016 I R)
    (rows : CntRows) (envs : List PlaceId) (w : Nat) (a0 a : AMarking) :
    (∃ n, Relation.ReflTransGen (R rows envs w a0) (I a0) (a, n)) ↔ ReachADInj rows envs a0 a := by
  constructor
  · rintro ⟨n, hr⟩
    exact ver016_counters_erase ((VER_016_reach_iff h rows envs w a0 (a, n)).mp hr)
  · intro hr
    obtain ⟨n, hn⟩ := ver016_counters_exist hr
    exact ⟨n, (VER_016_reach_iff h rows envs w a0 (a, n)).mpr hn⟩

/-- **Every row holds on every reachable augmented state**, from the statement alone. -/
theorem VER_016_rows_hold {I : CntInit} {R : CntRuleRel} (h : VER_016 I R)
    {rows : CntRows} {envs : List PlaceId} {w : Nat} {a0 a : AMarking} {n : Counters}
    (hr : Relation.ReflTransGen (R rows envs w a0) (I a0) (a, n)) :
    ∀ p, p ∉ envs → CntRow rows a0 a n p :=
  ver016_rows_hold ((VER_016_reach_iff h rows envs w a0 (a, n)).mp hr)

/-- **The certificate over `(M, n)` is sound** ([VER-016] AC3): a candidate that passes init,
consecution and safety against the raw counter step relation over deposit rows from `(a0, 0)`,
with a violation that reads the marking only, proves the property for every marking of the
deposit-row abstraction with injection (`Novel.Certificate.vc_sound_rel`;
`Novel.Certificate.vc_sound_state_equation` is the same result with deposits read as sets). -/
@[evidence cites "VER-016" "AC3: a certificate over (M, n) passing init, consecution and safety against the raw counter step relation over deposit rows (CntStep) from (a0, 0), with a violation that reads the marking only, proves the property for every marking of ReachADInj; the composition of the candidate is not covered"]
theorem VER_016_certificate {rows : CntRows} {envs : List PlaceId} {a0 : AMarking}
    {Bad : AMarking → Prop} {Inv : AMarking × Counters → Prop}
    (h : Novel.Certificate.VCs (CntStep rows envs) (refCntInit a0) (fun s => Bad s.1) Inv) :
    ProvenFor (ReachADInj rows envs a0) Bad := by
  intro a hr
  obtain ⟨n, hn⟩ := ver016_counters_exist hr
  exact Novel.Certificate.vc_sound_rel h (a, n) hn

/-! ## Examples -/

/-- `t`: one token from place `0` to place `1`. -/
def ver016_t : Libpetri.Transition :=
  { name := "t", inputs := [{ place := 0, card := .one, guard := none }],
    inhibitors := [], reads := [], resets := [] }

/-- The rows with the one transition `t`. -/
def ver016_net : CntRows := [(ver016_t, [1])]

/-- The forward row of `exactly(2, a) → xor(c, timeout(forward(a, b)))` that ends in the
timeout: `tFwd` (`exactly(2)` on `a = 0`) with the deposit `[b, b]`, two tokens in `b = 1`
(`fixed_rows_example`, the `t_b2` row of `flatten_forward_deposits_every_consumed_token`). -/
def ver016_fwd : CntRows := [(tFwd, [pb, pb])]

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
    ¬ CntRow ver016_net ver016_empty (fireAD ver016_one0 ver016_t [1])
      (bump (fun _ => 0) 0) 0 := by
  unfold CntRow
  decide

/-- On `netAll` (`drain_all` clears place `0`, which holds two tokens, with a consume-all arc),
the successor of the first firing meets the upper bound of place `0`. -/
theorem ver016_all_upper :
    CntRow Libpetri.netAll Libpetri.a0All (fireAD Libpetri.a0All Libpetri.tAll [1])
      (bump (fun _ => 0) 0) 0 := by
  unfold CntRow
  decide

/-- On `netAll` the equality row of place `0` fails after the first firing: the place is empty
while the linear count says `2 - 1`. -/
theorem ver016_all_ne :
    ((fireAD Libpetri.a0All Libpetri.tAll [1] 0 : Nat) : Int) ≠
      cntRhs Libpetri.netAll Libpetri.a0All (bump (fun _ => 0) 0) 0 := by
  decide

/-- From `({0: 5}, 0)` on `netAll` with `a0All`, the successor of `drain_all` meets the row of
both places: place `0` is empty (`0 ≤ 1`) and place `1` holds the one token the equation says. -/
theorem ver016_five0_rows :
    ∀ p : Nat, p < 2 → p ∉ ([] : List PlaceId) →
      CntRow Libpetri.netAll Libpetri.a0All (fireAD ver016_five0 Libpetri.tAll [1])
        (bump (fun _ => 0) 0) p := by
  intro p hp _
  rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;> (unfold CntRow; decide)

/-- From the initial fact `({a: 2}, 0)` the firing of the forward row ends at `b = 2` and meets
both rows: `a = 2 - 2·1` and `b = 0 + 2·1`. -/
theorem ver016_fwd_rows :
    ∀ p : Nat, p < 2 → p ∉ ([] : List PlaceId) →
      CntRow ver016_fwd ver016_two0 (fireAD ver016_two0 tFwd [pb, pb])
        (bump (fun _ => 0) 0) p := by
  intro p hp _
  rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;> (unfold CntRow; decide)

/-- ✓ **AC2 on the reference.** On `netAll` the firing rule exists from the initial fact and
its successor meets the upper bound of place `0` although the equality would fail; an injection
into place `0` of `ver016_net` copies the counters; from the augmented state `({0: 1}, 0)` with
the empty initial marking, which is off the equation, the rule refuses the firing of `t`; and on
the forward row that deposits two tokens in `b`, the firing from `({a: 2}, 0)` is a rule step
that ends at `b = 2`. -/
@[evidence nonvacuous VER_016]
theorem VER_016_nonvacuous :
    refRules Libpetri.netAll [] 1 Libpetri.a0All (refCntInit Libpetri.a0All)
        (fireAD Libpetri.a0All Libpetri.tAll [1], bump (fun _ => 0) 0) ∧
      ((fireAD Libpetri.a0All Libpetri.tAll [1] 0 : Nat) : Int) ≠
        cntRhs Libpetri.netAll Libpetri.a0All (bump (fun _ => 0) 0) 0 ∧
      refRules ver016_net [0] 2 ver016_empty (ver016_empty, fun _ => 0)
        (ver016_one0, fun _ => 0) ∧
      ¬ refRules ver016_net [] 2 ver016_empty (ver016_one0, fun _ => 0)
        (fireAD ver016_one0 ver016_t [1], bump (fun _ => 0) 0) ∧
      refRules ver016_fwd [] 2 ver016_two0 (refCntInit ver016_two0)
        (fireAD ver016_two0 tFwd [pb, pb], bump (fun _ => 0) 0) ∧
      fireAD ver016_two0 tFwd [pb, pb] pb = 2 := by
  refine ⟨Or.inl ⟨0, (Libpetri.tAll, [1]), rfl, by decide, fun p hp _ => ?_, rfl⟩,
    ver016_all_ne, Or.inr ⟨0, by simp, ?_⟩, ?_,
    Or.inl ⟨0, (tFwd, [pb, pb]), rfl, by decide, ver016_fwd_rows, rfl⟩, by decide⟩
  · obtain rfl : p = 0 := by omega
    exact ver016_all_upper
  · refine Prod.ext (funext fun q => ?_) rfl
    by_cases hq : q = 0 <;> simp [ver016_one0, ver016_empty, hq]
  · rintro (⟨k, tr, hk, -, hrow', heq⟩ | ⟨p, hp, -⟩)
    · have hk0 : k = 0 := by
        have := congrArg (fun x => x.2 0) heq
        by_contra hne'
        simp [bump] at this
        omega
      subst hk0
      have htr : tr = (ver016_t, [1]) := by
        have : ver016_net[0]? = some (ver016_t, [1]) := rfl
        rw [this] at hk; exact (Option.some.inj hk).symm
      subst htr
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
def ver016_bumpTwo : CntRuleRel := fun rows envs _ _ s s' =>
  (∃ k tr, rows[k]? = some tr ∧ enabledA s.1 tr.1 = true ∧
      s' = (fireAD s.1 tr.1 tr.2, bump (bump s.2 k) (k + 1)))
  ∨ ∃ p ∈ envs, s' = (fun q => if q == p then s.1 q + 1 else s.1 q, s.2)

/-- ✗ Line 2 forbids a rule that bumps two counters: the firing of `t` from `({0: 1}, 0)` also
bumps counter `1`, which no row of the net has. -/
@[evidence forbids VER_016]
theorem VER_016_forbids_bumpTwo : ¬ VER_016 refCntInit ver016_bumpTwo := by
  intro h
  have hs := h.2.1 ver016_net [] 2 ver016_one0 (ver016_one0, fun _ => 0)
    (fireAD ver016_one0 ver016_t [1], bump (bump (fun _ => 0) 0) 1)
    (Or.inl ⟨0, (ver016_t, [1]), rfl, by decide, rfl⟩)
  rcases hs with ⟨k, tr, hk, -, heq⟩ | ⟨p, hp, -⟩
  · have h1 := congrArg (fun x => x.2 1) heq
    by_cases hk1 : k = 1
    · subst hk1; simp [ver016_net] at hk
    · simp [bump, Ne.symm hk1] at h1
  · simp at hp

/-- The rules that read a deposit as a set: `StepCntStrRel` of `StateEquation.lean` with no
law, whose effect `fireA` and column `post − pre` put one token in each listed place. -/
def ver016_unitRules : CntRuleRel := fun rows envs w a0 => StepCntStrRel rows envs [] w a0

/-- ✗ Line 2 forbids reading a deposit as a set: on the forward row `(tFwd, [b, b])` from
`({a: 2}, 0)` the unit rule ends at `b = 1` (meeting its own unit rows), which is neither the
firing of the row (`b = 2`) nor an injection. -/
@[evidence forbids VER_016]
theorem VER_016_forbids_unitRules : ¬ VER_016 refCntInit ver016_unitRules := by
  intro h
  have hR : ver016_unitRules ver016_fwd [] 2 ver016_two0 (ver016_two0, fun _ => 0)
      (fireA ver016_two0 tFwd [pb, pb], bump (fun _ => 0) 0) :=
    Or.inl ⟨0, (tFwd, [pb, pb]), rfl, by decide, by simp, fun p hp _ => by
      rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;> (unfold Libpetri.Row; decide), rfl⟩
  rcases h.2.1 _ _ _ _ _ _ hR with ⟨k, tr, hk, -, heq⟩ | ⟨p, hp, -⟩
  · have h1 := congrArg (fun x => x.1 pb) heq
    cases k with
    | zero =>
      have htr : tr = (tFwd, [pb, pb]) := by
        have : ver016_fwd[0]? = some (tFwd, [pb, pb]) := rfl
        rw [this] at hk; exact (Option.some.inj hk).symm
      subst htr
      revert h1; decide
    | succ k => simp [ver016_fwd] at hk
  · simp at hp

/-- Rules without rows: the raw counter steps themselves. -/
def ver016_noRow : CntRuleRel := fun rows envs _ _ => CntStep rows envs

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
def ver016_leAll : CntRuleRel := fun rows envs w a0 s s' =>
  (∃ k tr, rows[k]? = some tr ∧ enabledA s.1 tr.1 = true ∧
      (∀ p, p < w → p ∉ envs →
        ((fireAD s.1 tr.1 tr.2 p : Nat) : Int) ≤ cntRhs rows a0 (bump s.2 k) p) ∧
      s' = (fireAD s.1 tr.1 tr.2, bump s.2 k))
  ∨ ∃ p ∈ envs, s' = (fun q => if q == p then s.1 q + 1 else s.1 q, s.2)

/-- ✗ Line 3 forbids the upper bound on an exact place: with initial marking `{0: 2}` and the
off-equation source `({0: 1}, 0)`, the firing of `t` meets `≤` on both places (`0 ≤ 1`,
`1 ≤ 1`), so the rule takes it, but the exact place `0` needs `0 = 1`. -/
@[evidence forbids VER_016]
theorem VER_016_forbids_leAll : ¬ VER_016 refCntInit ver016_leAll := by
  intro h
  have hR : ver016_leAll ver016_net [] 2 ver016_two0 (ver016_one0, fun _ => 0)
      (fireAD ver016_one0 ver016_t [1], bump (fun _ => 0) 0) :=
    Or.inl ⟨0, (ver016_t, [1]), rfl, by decide, fun p hp _ => by
      rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;> decide, rfl⟩
  have h0 := h.2.2.1 ver016_net [] 2 ver016_two0 (ver016_one0, fun _ => 0) 0 (ver016_t, [1])
    rfl (by decide) hR 0 (by omega) (by simp)
  revert h0; unfold CntRow; decide

/-- Rules with the equality row on every non-injected place, cleared or not. -/
def ver016_eqRow : CntRuleRel := fun rows envs w a0 s s' =>
  (∃ k tr, rows[k]? = some tr ∧ enabledA s.1 tr.1 = true ∧
      (∀ p, p < w → p ∉ envs →
        ((fireAD s.1 tr.1 tr.2 p : Nat) : Int) = cntRhs rows a0 (bump s.2 k) p) ∧
      s' = (fireAD s.1 tr.1 tr.2, bump s.2 k))
  ∨ ∃ p ∈ envs, s' = (fun q => if q == p then s.1 q + 1 else s.1 q, s.2)

/-- ✗ Line 4 forbids the equality row on a cleared place: on `netAll` the firing of
`drain_all` from the initial fact has a successor that meets the upper bound, so the rules
must take it, and the equality row refuses it (`ver016_all_ne`). -/
@[evidence forbids VER_016]
theorem VER_016_forbids_eqRow : ¬ VER_016 refCntInit ver016_eqRow := by
  intro h
  have h4 := h.2.2.2.1 Libpetri.netAll [] 1 Libpetri.a0All (Libpetri.a0All, fun _ => 0) 0
    (Libpetri.tAll, [1]) rfl (by decide) (fun p hp _ => by
      obtain rfl : p = 0 := by omega
      exact ver016_all_upper)
  rcases h4 with ⟨k, tr, hk, -, hrow', heq⟩ | ⟨p, hp, -⟩
  · have hk0 : k = 0 := by
      have := congrArg (fun x => x.2 0) heq
      by_contra hne'
      simp [bump] at this
      omega
    subst hk0
    have htr : tr = (Libpetri.tAll, [1]) := by
      have : Libpetri.netAll[0]? = some (Libpetri.tAll, [1]) := rfl
      rw [this] at hk; exact (Option.some.inj hk).symm
    subst htr
    exact ver016_all_ne (hrow' 0 (by omega) (by simp))
  · simp at hp

/-- Rules that also conjoin the row of an injected place. -/
def ver016_injRow : CntRuleRel := fun rows envs w a0 s s' =>
  (∃ k tr, rows[k]? = some tr ∧ enabledA s.1 tr.1 = true ∧
      (∀ p, p < w → CntRow rows a0 (fireAD s.1 tr.1 tr.2) (bump s.2 k) p) ∧
      s' = (fireAD s.1 tr.1 tr.2, bump s.2 k))
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
      unfold CntRow; decide)
  rcases h4 with ⟨k, tr, hk, -, hrow, heq⟩ | ⟨p, -, heq⟩
  · have hk0 : k = 0 := by
      have := congrArg (fun x => x.2 0) heq
      by_contra hne'
      simp [bump] at this
      omega
    subst hk0
    have htr : tr = (ver016_t, [1]) := by
      have : ver016_net[0]? = some (ver016_t, [1]) := rfl
      rw [this] at hk; exact (Option.some.inj hk).symm
    subst htr
    exact ver016_row0_off (hrow 0 (by omega))
  · have := congrArg (fun x => x.2 0) heq
    simp [bump] at this

/-- Rules that conjoin the rows over the source `(M, n)` instead of the successor `(M', n')`:
the primed-variable slip. -/
def ver016_srcRow : CntRuleRel := fun rows envs w a0 s s' =>
  (∃ k tr, rows[k]? = some tr ∧ enabledA s.1 tr.1 = true ∧
      (∀ p, p < w → p ∉ envs → CntRow rows a0 s.1 s.2 p) ∧
      s' = (fireAD s.1 tr.1 tr.2, bump s.2 k))
  ∨ ∃ p ∈ envs, s' = (fun q => if q == p then s.1 q + 1 else s.1 q, s.2)

/-- ✗ Line 4 forbids rows over the source: from `({0: 5}, 0)` on `netAll` with `a0All` the
successor of `drain_all` meets both rows, so the rules must take it, but the source row of the
cleared place `0` needs `5 ≤ 2`. -/
@[evidence forbids VER_016]
theorem VER_016_forbids_srcRow : ¬ VER_016 refCntInit ver016_srcRow := by
  intro h
  have h4 := h.2.2.2.1 Libpetri.netAll [] 2 Libpetri.a0All (ver016_five0, fun _ => 0) 0
    (Libpetri.tAll, [1]) rfl (by decide) ver016_five0_rows
  rcases h4 with ⟨k, tr, hk, hen, hrow, heq⟩ | ⟨p, hp, -⟩
  · have h0 := hrow 0 (by omega) (by simp)
    revert h0; unfold CntRow; decide
  · simp at hp

/-- Rules that conjoin the rows over the successor marking with the old counters `n`. -/
def ver016_oldCnt : CntRuleRel := fun rows envs w a0 s s' =>
  (∃ k tr, rows[k]? = some tr ∧ enabledA s.1 tr.1 = true ∧
      (∀ p, p < w → p ∉ envs → CntRow rows a0 (fireAD s.1 tr.1 tr.2) s.2 p) ∧
      s' = (fireAD s.1 tr.1 tr.2, bump s.2 k))
  ∨ ∃ p ∈ envs, s' = (fun q => if q == p then s.1 q + 1 else s.1 q, s.2)

/-- ✗ Line 4 forbids rows over the old counters: on `ver016_net` from the initial fact
`({0: 1}, 0)` the firing of `t` meets both rows over `n'`, so the rules must take it, but over
the old counters place `0` needs `0 = 1`. -/
@[evidence forbids VER_016]
theorem VER_016_forbids_oldCnt : ¬ VER_016 refCntInit ver016_oldCnt := by
  intro h
  have h4 := h.2.2.2.1 ver016_net [] 2 ver016_one0 (ver016_one0, fun _ => 0) 0
    (ver016_t, [1]) rfl (by decide) (fun p hp _ => by
      rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;> (unfold CntRow; decide))
  rcases h4 with ⟨k, tr, hk, -, hrow, heq⟩ | ⟨p, hp, -⟩
  · have hk0 : k = 0 := by
      have := congrArg (fun x => x.2 0) heq
      by_contra hne'
      simp [bump] at this
      omega
    subst hk0
    have htr : tr = (ver016_t, [1]) := by
      have : ver016_net[0]? = some (ver016_t, [1]) := rfl
      rw [this] at hk; exact (Option.some.inj hk).symm
    subst htr
    have h0 := hrow 0 (by omega) (by simp)
    revert h0; unfold CntRow; decide
  · simp at hp

/-- Rules with the effect of the deposit but the unit column of `StateEquation.lean`
(`Libpetri.Row`, `incAt`), which counts a place listed twice in a deposit once. -/
def ver016_unitColumn : CntRuleRel := fun rows envs w a0 s s' =>
  (∃ k tr, rows[k]? = some tr ∧ enabledA s.1 tr.1 = true ∧
      (∀ p, p < w → p ∉ envs → Libpetri.Row rows a0 (fireAD s.1 tr.1 tr.2) (bump s.2 k) p) ∧
      s' = (fireAD s.1 tr.1 tr.2, bump s.2 k))
  ∨ ∃ p ∈ envs, s' = (fun q => if q == p then s.1 q + 1 else s.1 q, s.2)

/-- ✗ Line 4 forbids the unit column: on the forward row `(tFwd, [b, b])` with initial marking
`{a: 2}`, the firing from the initial fact ends at `b = 2`, which meets the rows `a = 2 - 2·1`
and `b = 0 + 2·1`, so the rules must take it, but the unit column says `b = 0 + 1·1`. -/
@[evidence forbids VER_016]
theorem VER_016_forbids_unitColumn : ¬ VER_016 refCntInit ver016_unitColumn := by
  intro h
  have h4 := h.2.2.2.1 ver016_fwd [] 2 ver016_two0 (ver016_two0, fun _ => 0) 0
    (tFwd, [pb, pb]) rfl (by decide) ver016_fwd_rows
  rcases h4 with ⟨k, tr, hk, -, hrow, heq⟩ | ⟨p, hp, -⟩
  · have hk0 : k = 0 := by
      have := congrArg (fun x => x.2 0) heq
      by_contra hne'
      simp [bump] at this
      omega
    subst hk0
    have htr : tr = (tFwd, [pb, pb]) := by
      have : ver016_fwd[0]? = some (tFwd, [pb, pb]) := rfl
      rw [this] at hk; exact (Option.some.inj hk).symm
    subst htr
    have h1 := hrow 1 (by omega) (by simp)
    revert h1; unfold Libpetri.Row; decide
  · simp at hp

/-- The raw counter steps restricted to sources the raw counter steps reach, with no row. -/
def ver016_reachOnly : CntRuleRel := fun rows envs _ a0 s s' =>
  Relation.ReflTransGen (CntStep rows envs) (a0, fun _ => 0) s ∧ CntStep rows envs s s'

/-- ✗ Line 4 forbids a guard on reachability: the firing of `drain_all` from `({0: 5}, 0)` on
`netAll` meets both rows, so the rules must take it, but `({0: 5}, 0)` is not reachable from
`{0: 2}` (every reachable state meets the row `m_0 ≤ 2` of the cleared place). -/
@[evidence forbids VER_016]
theorem VER_016_forbids_reachOnly : ¬ VER_016 refCntInit ver016_reachOnly := by
  intro h
  obtain ⟨hr, -⟩ := h.2.2.2.1 Libpetri.netAll [] 2 Libpetri.a0All (ver016_five0, fun _ => 0) 0
    (Libpetri.tAll, [1]) rfl (by decide) ver016_five0_rows
  have h0 := ver016_rows_hold hr 0 (by simp)
  revert h0; unfold CntRow; decide

/-- The reference firing rules with an injection guarded on an empty place. -/
def ver016_injEmpty : CntRuleRel := fun rows envs w a0 s s' =>
  (∃ k tr, rows[k]? = some tr ∧ enabledA s.1 tr.1 = true ∧
      (∀ p, p < w → p ∉ envs → CntRow rows a0 (fireAD s.1 tr.1 tr.2) (bump s.2 k) p) ∧
      s' = (fireAD s.1 tr.1 tr.2, bump s.2 k))
  ∨ ∃ p ∈ envs, s.1 p = 0 ∧ s' = (fun q => if q == p then s.1 q + 1 else s.1 q, s.2)

/-- ✗ Line 5 forbids a guarded injection: with place `0` injected, the injection from
`({0: 1}, 0)` must be a rule step, and the guarded rule refuses it. -/
@[evidence forbids VER_016]
theorem VER_016_forbids_injEmpty : ¬ VER_016 refCntInit ver016_injEmpty := by
  intro h
  rcases h.2.2.2.2 ver016_net [0] 2 ver016_empty (ver016_one0, fun _ => 0) 0 (by simp) with
    ⟨k, tr, hk, -, -, heq⟩ | ⟨p, hp, h0, -⟩
  · have := congrArg (fun x => x.2 k) heq
    simp [bump] at this
  · obtain rfl : p = 0 := by simpa using hp
    simp [ver016_one0] at h0

end Libpetri.Spec
