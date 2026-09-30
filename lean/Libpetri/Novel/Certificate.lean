import Libpetri.StateEquation
import Libpetri.Novel.ForwardDeposit

/-!
# The IC3/PDR certificate check

When Spacer answers `sat` on the CHC query, `VerificationConditions::build`
(`rust/libpetri-verification/src/certificate_check.rs`) re-checks the model it returns with
three plain SMT queries, each expected `unsat`, over the candidate `R' := R ∧ Inv` (the pasted
`Reachable` interpretation conjoined with the validated P-invariant equalities, and with
[VER-016] the marking equation and `n ≥ 0`):

* VC1 (initiation): `¬R'(M₀)`, with `M₀` read as `initial_marking.count(flat.places[i])`;
* VC2 (consecution): `M ≥ 0 ∧ R'(M) ∧ T(M, M') ∧ ¬R'(M')`, where `T` is
  `smt_encoder::encode_step_relation_smt2` — the **unstrengthened** firing and env-injection
  disjuncts (`firing_conditions`, `injection_conditions`), no P-invariant conjunct;
* VC3 (safety): `M ≥ 0 ∧ R'(M) ∧ Bad(M)`, where `Bad` is
  `smt_encoder::encode_property_violation`, the error rule's own violation.

`unsat` on all three is `CertificateCheck::Passed`. The model:
* `R'` is an arbitrary predicate `I` on markings: the proof never inspects it, so any
  conjunct `Inv` rides along and is re-proven by VC1/VC2, which is why a wrong P-invariant
  cannot pass the check (it fails initiation or consecution instead).
* The queries range over `Int` variables with `M ≥ 0` asserted (VC2/VC3) and `m'_i ≥ 0` inside
  `T`; `AMarking = PlaceId → Nat` is that domain.
* `T` is `StepAInjRel` (`AlwaysAvailable`). A `Bounded(k)` environment place does not remove
  disjuncts: it adds a conjunct to each, `m'_p ≤ k` to every firing (`env_bound_conditions`) and
  `m_p < k` to its injection (`injection_conditions`). That only narrows `T`, and
  `vc_sound_rel` covers any relation.
* `StepAInjRel` fires a row through `fireA`, whose `post` reads the row as a set, so it excludes
  a row that deposits `k ≥ 2` tokens in one place (a timeout forward from an `exactly(k)`
  input), where `firing_conditions` writes `post[to] = k`. `vc_sound_rows` is `vc_sound` over
  `ForwardDeposit.StepADInj`, which fires every row with its deposit counts.

Results:
* `vc_sound_rel` — for any step relation, VC1 ∧ VC2 ∧ VC3 → `ProvenFor` its reachable set.
* `vc_sound` — **VC1 ∧ VC2 ∧ VC3 → `ProvenFor (ReachAInj net envs a0) Bad`**, and
  `vc_sound_rows` for deposit rows of any multiplicity.
* `vc_sound_state_equation` — the [VER-016] form: the VCs over `(M, n)` and the raw counter
  step `StepCntRel`, with `Bad` reading the marking only, prove the plain `ReachAInj` verdict.
* `vc_complete` — the reachable set itself passes the VCs whenever the verdict is true, so the
  check refuses no true `Proven` on the model's domain (a certificate Spacer finds may still
  fail it, e.g. outside linear arithmetic).
* `vc_blind_to_seam` — **what the check cannot catch.** `a0` and `Bad` are inputs the check
  shares with the encoder: VC1 reads the same seed (`initial_marking.count(flat.places[i])`
  over the same `flat`) and VC3 calls the same `encode_property_violation`. If the seed dropped
  a caller token (the stray-token Proven of the lean-gaps analysis, cause 1b) or `Bad` missed a
  violation (cause 1c), a certificate passes all three VCs while the caller's net violates.
  The witness has an empty net, a seed that lost one token, and a certificate that passes.
-/

namespace Libpetri.Novel.Certificate

open Libpetri

/-- The three verification conditions over a step relation `T`, seed `a0`, violation `Bad` and
candidate invariant `I` (each VC's `unsat` read as validity). -/
structure VCs {σ : Type} (T : σ → σ → Prop) (a0 : σ) (Bad : σ → Prop) (I : σ → Prop) :
    Prop where
  vc1 : I a0
  vc2 : ∀ a a', I a → T a a' → I a'
  vc3 : ∀ a, I a → ¬ Bad a

/-- The candidate is inductive: it holds on every state `T` reaches from `a0`. -/
theorem vc_inductive {σ : Type} {T : σ → σ → Prop} {a0 : σ} {Bad I : σ → Prop}
    (h : VCs T a0 Bad I) {a : σ} (hr : Relation.ReflTransGen T a0 a) : I a := by
  induction hr with
  | refl => exact h.vc1
  | tail _ hs ih => exact h.vc2 _ _ ih hs

/-- Soundness for any step relation. -/
theorem vc_sound_rel {σ : Type} {T : σ → σ → Prop} {a0 : σ} {Bad I : σ → Prop}
    (h : VCs T a0 Bad I) (a : σ) (hr : Relation.ReflTransGen T a0 a) : ¬ Bad a :=
  h.vc3 a (vc_inductive h hr)

/-- The candidate `R' := R ∧ Inv`: the pasted `Reachable` conjoined with the P-invariant
equalities over the first `n` places (`invariant_conditions`). -/
def candidate (R : AMarking → Prop) (invs : List Weight) (n : Nat) (a0 : AMarking) :
    AMarking → Prop :=
  fun a => R a ∧ ∀ y ∈ invs, dot y a n = dot y a0 n

/-- **`vc_sound`.** A certificate passing VC1–VC3 against the unstrengthened step relation
proves the property for the injected abstract reachable set — for any candidate, with no
assumption on the P-invariants it carries. -/
theorem vc_sound {net : FlatNet} {envs : List PlaceId} {a0 : AMarking}
    {Bad : AMarking → Prop} {I : AMarking → Prop}
    (h1 : I a0)
    (h2 : ∀ a a', I a → StepAInjRel net envs a a' → I a')
    (h3 : ∀ a, I a → ¬ Bad a) :
    ProvenFor (ReachAInj net envs a0) Bad :=
  vc_sound_rel ⟨h1, h2, h3⟩

/-- **`vc_sound` over deposit rows**: the step relation with integer posts, so a forward row with
`post[to] = k ≥ 2` is covered. -/
theorem vc_sound_rows {rows : List (Transition × ForwardDeposit.Deposit)} {envs : List PlaceId}
    {a0 : AMarking} {Bad : AMarking → Prop} {I : AMarking → Prop}
    (h1 : I a0)
    (h2 : ∀ a a', I a → ForwardDeposit.StepADInj rows envs a a' → I a')
    (h3 : ∀ a, I a → ¬ Bad a) :
    ProvenFor (ForwardDeposit.ReachADInj rows envs a0) Bad :=
  vc_sound_rel ⟨h1, h2, h3⟩

/-- `vc_sound` with the shipped candidate shape: nothing about `invs` is assumed. -/
theorem vc_sound_candidate {net : FlatNet} {envs : List PlaceId} {a0 : AMarking}
    {Bad : AMarking → Prop} {R : AMarking → Prop} {invs : List Weight} {n : Nat}
    (h : VCs (StepAInjRel net envs) a0 Bad (candidate R invs n a0)) :
    ProvenFor (ReachAInj net envs a0) Bad :=
  vc_sound_rel h

/-- **The [VER-016] form.** The certificate ranges over `(M, n)`, `T` is the raw counter step
(`StepCntRel`: fire and bump, or inject), the seed has zero counters, and `Bad` reads the
marking only (the error rule quantifies the counters). The VCs prove the plain verdict, because
every `ReachAInj` marking carries some counter vector (`counters_exist`). -/
theorem vc_sound_state_equation {net : FlatNet} {envs : List PlaceId} {a0 : AMarking}
    {Bad : AMarking → Prop} {I : AMarking × Counters → Prop}
    (h : VCs (StepCntRel net envs) (a0, fun _ => 0) (fun s => Bad s.1) I) :
    ProvenFor (ReachAInj net envs a0) Bad := by
  intro a hr
  obtain ⟨n, hn⟩ := counters_exist hr
  exact vc_sound_rel h (a, n) hn

/-- **Completeness on the model.** A true verdict has a certificate: the reachable set. -/
theorem vc_complete {net : FlatNet} {envs : List PlaceId} {a0 : AMarking}
    {Bad : AMarking → Prop} (hp : ProvenFor (ReachAInj net envs a0) Bad) :
    VCs (StepAInjRel net envs) a0 Bad (ReachAInj net envs a0) :=
  ⟨ReachAInj.init, fun _ _ h hs => Relation.ReflTransGen.tail h hs, hp⟩

/-! ## The seam the check shares with the encoder -/

/-- The caller's marking: one token on place `0`. -/
def a0Caller : AMarking := fun p => if p = 0 then 1 else 0

/-- The encoded seed after a seam bug dropped that token. -/
def a0Encoded : AMarking := fun _ => 0

/-- `Unreachable {p₀}` (or a stranding on `p₀`): the violation. -/
def badP0 : AMarking → Prop := fun a => 1 ≤ a 0

/-- The certificate Spacer would return for the encoded query: `m₀ = 0`. -/
def certP0 : AMarking → Prop := fun a => a 0 = 0

/-- **The check is blind to the seam.** On the empty net, with the seed the encoder computed,
`certP0` passes VC1–VC3 — yet the caller's net, started from the caller's marking, violates at
once. Because VC1 and VC3 read the same `a0` and `Bad` as the CHC query, no certificate check
over them can detect a seed or `Bad` that disagrees with the caller's net. -/
theorem vc_blind_to_seam :
    VCs (StepAInjRel [] []) a0Encoded badP0 certP0
    ∧ ReachAInj [] [] a0Caller a0Caller ∧ badP0 a0Caller := by
  refine ⟨⟨rfl, ?_, ?_⟩, ReachAInj.init, show 1 ≤ a0Caller 0 by decide⟩
  · rintro a a' _ (⟨ft, hft, _⟩ | ⟨p, hp, _⟩)
    · simp at hft
    · simp at hp
  · intro a ha hb
    simp only [certP0] at ha
    simp only [badP0] at hb
    omega

end Libpetri.Novel.Certificate
