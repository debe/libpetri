import Libpetri.Spec.Registry
import Libpetri.Semiflow
import Libpetri.Novel.RouteA.Simulate

set_option linter.missingDocs true

/-!
# VER-007: Invariant strengthening from P-semiflows (`spec/07-verification.md`)

The encoders of the verifier receive every conservation law that passed the exact gate, and
conjoin each one into their rule bodies. The option of VER-007 decides whether the
gate-validated P-semiflows join the gate-validated basis rows of [VER-005] in that list: never
(`off`, the default), always (`on`), or exactly when the gate dropped a basis row for its weight
on a consume-all or reset place (`auto`).

The requirement is a predicate over one function `E : SemiflowEnc`, the list of laws the encoders
receive, from the option's setting, the flat net as deposit rows, the injected environment
places, the place count, the basis rows and the enumerated semiflows (the shape of the Phase 3
code around `validate_invariants_exact` and `strengthen_with_semiflows`, `p_invariant.rs`, and the
`union_wanted` decision of `smt_verifier.rs`). The gate is `LawGate`: H1, zero weight on every
consume-all or reset place; H2, `y·C = 0` on the column of every deposit row, each column
counting every token the row deposits (`dotIncD`, the column `IncidenceMatrix::from_flat_net`
builds from `net_flattener.rs`'s `post[..] += n`); H3', zero weight on every injected place below
the place count, which the injector columns force through `y·C = 0`.

The witness is `refEnc`. The statement is checked against it (`VER_007_reference`), against an
`off` that lets the semiflows through, an `off` that skips the gate, an `off` and an `on` that
drop the basis rows, a gate that checks only `y·C = 0`, a gate without the injector columns, a
gate that forgets reset arcs, a gate that reads a multi-token deposit row as one token per place
(the pre-IO-014 reading), an `on` that drops the semiflows, and an `auto` that always unions,
never unions or unions on any dropped row. `VER_007_preserves_reach` derives AC6 from the
statement: whatever the setting, the relation with every handed law conjoined reaches exactly the
abstract reachable set over the deposit rows, so no `Violated` turns into `Proven`.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Novel.ForwardDeposit Libpetri.Novel.LinearBound Libpetri.Novel.RouteA

/-! ## The model -/

/-- The setting of the semiflow option (`SemiflowMode`, `smt_verifier.rs`; Java
`SmtVerifier.SemiflowMode`; TypeScript `boolean | 'auto'`; Python `True` / `False` / `"auto"`). -/
inductive SemiflowOpt where
  /-- The encoders see the basis rows only (the default). -/
  | off
  /-- The validated semiflows join the basis rows. -/
  | on
  /-- `on` exactly when the gate dropped a basis row under H1, `off` otherwise. -/
  | auto
  deriving DecidableEq, Repr

/-- What the encoders receive: `E md rows envs n a0 basis sfs` is the list of laws handed to the
encoders under the setting `md`, for the flat net with the deposit rows `rows`, the injected
environment places `envs`, the place count `n`, the initial marking `a0` (the gate's `y·M0`), the
basis rows `basis` of [VER-005] and the
semiflows `sfs` the Farkas enumeration returned (any subset of the minimal ones: the enumeration
may truncate). -/
abbrev SemiflowEnc : Type :=
  SemiflowOpt → List (Transition × Deposit) → List PlaceId → Nat → AMarking → List Weight →
    List Weight → List Weight

/-- The exact gate (`validate_invariants_exact`, `p_invariant.rs`) over deposit rows. -/
structure LawGate (rows : List (Transition × Deposit)) (envs : List PlaceId) (n : Nat)
    (y : Weight) : Prop where
  /-- H1: zero weight on every place a row's transition consumes with `all()` / `atLeast(n)` or
  clears with a reset arc. -/
  h1 : ∀ tr ∈ rows, ZeroOnNonlinear y tr.1 n
  /-- H2: `y·C = 0` on every row's column, the column counting each token the row deposits. -/
  h2 : ∀ tr ∈ rows, dotIncD y tr n = 0
  /-- H3': zero weight on every injected place below the place count (its injector column). -/
  h3 : ∀ p ∈ envs, p < n → y p = 0

/-- The integer range every implementation's gate holds: Java's `int` (`2^31 − 1`), the
narrowest of the four (Rust extracts `i64` weights and sums in checked `i128`, TypeScript keeps
weights and counts safe integers and sums in `BigInt`). -/
def lawRange : Int := 2147483647

/-- `LawFits B rows n a0 y`: every weight below `n`, and for each sum of the gate the sum of the
absolute values of its terms, is at most `B`: each row's `y·C[t]` and the initial `y·M0`. Under it
no operand, product or partial sum of the gate leaves `[-B, B]`, whatever the order of the terms;
an injector column's `y·C` is the injected place's weight. -/
def LawFits (B : Int) (rows : List (Transition × Deposit)) (n : Nat) (a0 : AMarking)
    (y : Weight) : Prop :=
  (∀ p, p < n → ((y p).natAbs : Int) ≤ B) ∧
  (∀ tr ∈ rows,
    isum (fun p => ((y p * ((tr.2.count p : Int) - (pre tr.1 p : Int))).natAbs : Int)) n ≤ B) ∧
  isum (fun p => ((y p * (a0 p : Int)).natAbs : Int)) n ≤ B

instance (B : Int) (rows : List (Transition × Deposit)) (n : Nat) (a0 : AMarking) (y : Weight) :
    Decidable (LawFits B rows n a0 y) := by
  unfold LawFits; infer_instance

/-- The basis lost a law to the H1 guard: some basis row weights a place that a row's transition
consumes with `all()` / `atLeast(n)` or clears with a reset arc (the drop reason
`Strengthening.lean H1` the runtimes key `auto` on). -/
def BasisLostH1 (rows : List (Transition × Deposit)) (n : Nat) (basis : List Weight) : Prop :=
  ∃ y ∈ basis, ¬ ∀ tr ∈ rows, ZeroOnNonlinear y tr.1 n

open Classical in
/-- The reference: the gate (`LawGate`) filters the basis rows, and the semiflows when the
setting unions them; `auto` unions exactly when the basis lost a law to H1. Deduplication of a
semiflow against an equal basis row (`strengthen_with_semiflows`) and the canonical order are
left out: the encoder conjoins each law, so neither changes the rule bodies' meaning. -/
noncomputable def refEnc : SemiflowEnc :=
  fun md rows envs n _a0 basis sfs =>
    let ok := fun y => decide (LawGate rows envs n y)
    let off := basis.filter ok
    let on := basis.filter ok ++ sfs.filter ok
    match md with
    | .off => off
    | .on => on
    | .auto => if BasisLostH1 rows n basis then on else off

#spec_witness refEnc

/-! ## VER-007: Invariant strengthening from P-semiflows -/

requirement VER_007
  id "VER-007"
  title "Invariant Strengthening from P-Semiflows"
  kind F
  scope "the SMT pipeline's Phase 3 and every encoder it feeds (flat and name-coloured), all implementations"
  source verbatim "spec/07-verification.md"
  quote "The verifier's encoders conjoin every accepted conservation law `y·M = y·M0` into the transition-rule bodies of the CHC/IC3 encoding ([VER-004], [VER-005])."
        "A law is accepted only by the **exact gate**: `y·C = 0` against the incidence matrix and `y·M0 = c` are re-checked in exact (overflow-checked) integer arithmetic, and `y` MUST carry zero weight on every place a transition consumes with `all()` / `atLeast(n)` or clears with a reset arc, because the encoder's fire relation is not linear there (Lean `Strengthening.lean`, hypotheses H1/H2; injected environment places are covered by [VER-006], H3')."
        "A law that fails the gate is dropped from the encoding and listed in the report."
        "The encoders *shall* receive a conservation law only when the law passed the exact gate: `y·C = 0` against every column of the incidence matrix, each column counting every token its flat transition deposits and the injector columns of [VER-006] included, and `y·M0` equal to the law's constant, both in exact integer arithmetic, and zero weight on every place a transition consumes with `all()` / `atLeast(n)` or clears with a reset arc."
        "The encoders *shall* receive every basis row of [VER-005] that passed the gate, whatever the option's setting."
        "A law whose weights or exact sums leave the implementation's integer range fails the gate with a weight-overflow reason."
        "Every implementation's range holds a law whose weights, and the sum of the absolute values of the terms of each of its sums `y·C` and `y·M0`, are at most `2^31 − 1`."
        "An implementation SHOULD therefore offer an option that unions the gate-validated semiflows into the invariant list the encoders receive, and SHOULD offer an **`auto`** setting that applies the condition above on the caller's behalf: compute and union the semiflows exactly when the basis lost a law to the H1 guard, and skip them otherwise."
        "*While* the option is off, the encoders *shall* receive exactly the basis rows that passed the gate."
        "*While* the option is on, the encoders *shall* receive exactly the basis rows and the enumerated semiflows that passed the gate."
        "*While* the option is `auto`, the encoders *shall* receive what they receive with the option on when the gate dropped a basis row for its weight on a consume-all or reset place, and what they receive with the option off otherwise."
        "Semiflows are re-validated by the same exact gate as the basis rows before use; a semiflow that fails it is dropped with a `Dropped semiflow:` report line and is never encoded."
  reading "For every encoding function E, and all flat nets given as deposit rows, injected places envs, place counts n, initial markings a0, basis rows basis, semiflows sfs and laws y:"
          "y is in the list E hands the encoders with the option off only when y is a basis row and passes the gate LawGate rows envs n (H1: zero on every consume-all or reset place; H2: y·C = 0 on the column of every deposit row, the column counting each deposited token; H3': zero on every injected place below n), and every basis row that passes the gate and fits the range 2^31 − 1 (LawFits: every weight, and the sum of the absolute values of the terms of each row's y·C and of y·a0, at most 2^31 − 1) is in it;"
          "y is in the list with the option on only when y is a basis row or a semiflow and passes the gate, and every basis row or semiflow that passes the gate and fits the range is in it;"
          "with the option auto the list is the option-on list when some basis row fails H1, and the option-off list otherwise."
  assumes "The verified net is its flat rows: one deposit row per flat transition and outcome, with the integer post vector the encoder writes (ForwardDeposit.flatRows, fireAD), so a timeout row that forwards two tokens is the row [b, b] and its column counts both (dotIncD; net_flattener.rs `post[..] += n`, as in VER-005). A gate that reads a row as one token per claimed place, the reading before the IO-014 fix, is killed (VER_007_forbids_unitColumn): it accepts a law that a reachable firing breaks (ver007_yBad_not_conserved). A forward that drains its source (VER-001 F3, refused by branch_outcomes::drained_forward before any flat route) has no row; Phase 3 is not run on such a net, and the statement says nothing about it."
          "The gate is LawGate: H1 and H2 of Strengthening.lean over deposit rows, plus H3' on the injected places below n; with no injected place (envs = []) H3' is empty. The runtime forces H3' through `y·C = 0` on the injector columns of the incidence matrix ([VER-006], incidence_matrix.rs); LawGate states the consequence, zero weight on each injected place. The constant check `y·M0 = c` is not a clause: a law here is a weight vector and its equation is `y·M = y·M0` with the constant read off M0 (ReachADInjStrs), so a law with a wrong constant does not exist in the model; only the overflow of y·M0 is, through LawFits. The weights are unbounded integers. The runtimes' checked arithmetic drops a law whose exact value leaves their integer range with a weight-overflow reason (the sixth quoted sentence): Java keeps weights and the constant in int and sums y·C in checked long (PInvariantComputer.validateExact), Rust extracts i64 weights and sums in checked i128 (validate_invariants_exact, p_invariant.rs), and TypeScript keeps weights, incidence entries and counts safe integers and sums in BigInt (p-invariant-computer.ts). So lines 2 and 3 are split: a law in a list passes LawGate, whatever its size; a law that passes LawGate is in the list when it fits the range 2^31 − 1 of the seventh quoted sentence (LawFits lawRange), under which no operand, product or partial sum of any runtime's gate leaves its range, whatever the order of the terms. A law outside the range may be dropped, which only shrinks the list, and VER_007_preserves_reach holds for every list a VER-007 encoding hands over. The model's encoding takes the initial marking a0 for this reason alone: the reference ignores it, and the gate's y·M0 = c is not a clause (the constant is read off a0)."
          "The statement fixes the list the encoders receive, not what an encoder does with it. That each encoder conjoins every received law, and only those, into its rule bodies is the encoder's obligation (VER-004 for the flat encoder, NU-050 for the name-coloured one) and out of scope here; the first quoted sentence and the 'receive' wording of the fourth and fifth are read through it. The reach corollary VER_007_preserves_reach models that conjoining (ReachADInjStrs: every handed law conjoined into the firing rules, the injection rules carrying none)."
          "The lists are read as sets (lines 2 and 3 are membership statements): the encoder conjoins each law, so the order (the canonical order of VER-013) and a semiflow equal to a basis row (deduplicated by strengthen_with_semiflows) do not change the rule bodies' meaning. Malformed rows (a weight vector of the wrong length, a support inconsistent with the weights) do not exist in the model: a weight is a total function on place indices, read below the place count n."
          "'The basis lost a law to the H1 guard' is BasisLostH1: some basis row fails H1 (ZeroOnNonlinear on some row's transition). All four runtimes key auto on the drop reason that names Strengthening.lean H1 (smt_verifier.rs union_wanted, smt-verifier.ts basisLostALaw, SmtVerifier.java basisLostALaw), which the gate checks before y·C = 0, so a row failing H1 is dropped with that reason whatever else it fails; a row dropped for y·C alone does not switch auto on (killed: VER_007_forbids_autoAnyDrop), and a basis row lost to H1 does (killed: VER_007_forbids_autoNever)."
          "The basis rows and the semiflows are inputs: their computation is VER-005's (the null-space basis) and the Farkas enumeration's, which may truncate the minimal set, so sfs is any list. The statement holds for every list, which is the 'arbitrary truncation' paragraph: a law the enumeration never returns is a proof the encoder does not get, never a proof it gets wrong. 'Implementations SHOULD report the truncation when it binds' is a report line (kind Q)."
          "'If the option is off, or it is `auto` and the gate dropped no basis row for its weight on a consume-all or reset place, then the verifier shall not compute the semiflows.' is kind Q: a pure function cannot tell a computed and discarded list from one never computed, and the sentence is about cost (the enumeration's run time and heap). Line 2 and line 4 state what the model can see: in those cases no semiflow that is not a validated basis row reaches the encoders. 'The enumeration is expensive and MUST be skipped when nothing will read it.' and 'An implementation MUST compute semiflows only when the option is on, or is `auto` and the gate dropped a basis row for its weight on a consume-all or reset place.' are the same obligation, kind Q, and 'Such a caller MUST request the union explicitly.' is the caller's, not the verifier's: auto's choice is line 4, which says nothing about the form of the invariant list a caller inspects."
          "The third quoted sentence has two halves. 'Dropped from the encoding' is lines 2 and 3 (a basis row that fails the gate is in no list: VER_007_forbids_offNoGate; one that passes is in every list: VER_007_forbids_offEmpty, VER_007_forbids_onSfsOnly). 'Listed in the report' is a report line for each dropped basis row, kind Q, as the `Dropped semiflow:` line of AC1 is for each dropped semiflow."
          "AC1 is quoted and is lines 2 and 3 for the semiflows: a semiflow that fails the gate is in no list. A gate that checks only y·C = 0 is killed (VER_007_forbids_gateCOnly, the Farkas row yUnit of semiflow_gate_is_necessary), and so are a gate without H3' (VER_007_forbids_noEnvZero, the law of injection_hypothesis_is_necessary), a gate whose H1 forgets reset arcs (VER_007_forbids_resetBlind) and a gate that reads a deposit row as one token per place (VER_007_forbids_unitColumn). The `Dropped semiflow:` report line is kind Q."
          "AC2 (with the option off the semiflows do not reach the encoders, are not computed, and the report is byte-identical to a build without the feature) is line 2 for the first clause, killed by an off that lets the semiflows through (VER_007_forbids_offLeaks); not computing them and the byte-identical report are kind Q, and off as the default is kind N."
          "AC3 (under auto the report says which way it went and why, the union happens exactly when the gate dropped a basis row for its weight on a consume-all or reset place, the verdict equals that of the explicit setting auto chose, and the report's off wording says the skipped semiflows add no constraint) is line 4 for the union and the verdict: the list auto hands the encoders equals the list of the setting it chose, so every phase reading the list answers alike. An auto that always unions, one that never unions and one that unions on any dropped row are killed (VER_007_forbids_autoAlways, VER_007_forbids_autoNever, VER_007_forbids_autoAnyDrop). The report lines and their wording are kind Q."
          "AC4 (the report line `  Semiflows encoded as invariants: N`, N counting the semiflows added after deduplication, and the result's invariant count and list including them) is line 3 for the list; the report line and the count are kind Q. An on that drops the semiflows is killed (VER_007_forbids_onOmits)."
          "AC5 (the certificate check receives the strengthened list and re-proves every law against the unstrengthened step relation on the flat encoding) is not a line here: the certificate check belongs to the verifier pipeline (RefVerifier, wave W10) and its soundness is Novel/Certificate.lean (vc_sound). This block fixes the list the check receives."
          "AC6 (a genuine violation stays Violated with the option enabled) follows from lines 2 to 4: every law in every list passes the gate, so the strengthened relation reaches exactly the abstract reachable set over the deposit rows with injection (VER_007_preserves_reach: ReachADInj equals ReachADInjStrs). This is also the paragraph sentence that the option is pure strengthening and can never turn a `Violated` into a `Proven`."
          "AC7 (the strengthened list reaches the name-coloured encoder of NU-050 as well as the flat one, witnessed by a coloured net whose script differs between the option's two states) is not a line here: E is the list Phase 3 hands to whichever encoder runs, and that the coloured encoder conjoins a coloured place's term as the sum over its colour slots belongs to the NU encoder model (wave W10); the differing script is a test (kind Q)."
          "'No other phase reads them: the colour-slot bound of [NU-053] is a linear program over the incidence matrix, not a semiflow search.' is kind N, a design fact about another phase: the NU-053 block's model takes the rows and no semiflow list. The rest of the cost paragraph, the 'What auto does not decide' paragraph and the trigger paragraph (one consume-all or reset arc on a busy place loses every basis row whose support touches it) are explanation: the trigger is BasisLostH1 and VER_007_nonvacuous shows it on a net with one consume-all arc. The Implementation notes name the per-language entry points (kind N); the test derivation is AC1 to AC7 on a budgeted work loop, as above."
  signoff "pending"
  statement : SemiflowEnc → Prop :=
    fun E =>
      (∀ rows envs n a0 basis sfs y,
        (y ∈ E .off rows envs n a0 basis sfs → y ∈ basis ∧ LawGate rows envs n y) ∧
        (y ∈ basis ∧ LawGate rows envs n y → LawFits lawRange rows n a0 y →
          y ∈ E .off rows envs n a0 basis sfs)) ∧
      (∀ rows envs n a0 basis sfs y,
        (y ∈ E .on rows envs n a0 basis sfs → (y ∈ basis ∨ y ∈ sfs) ∧ LawGate rows envs n y) ∧
        ((y ∈ basis ∨ y ∈ sfs) ∧ LawGate rows envs n y → LawFits lawRange rows n a0 y →
          y ∈ E .on rows envs n a0 basis sfs)) ∧
      (∀ rows envs n a0 basis sfs,
        (BasisLostH1 rows n basis → E .auto rows envs n a0 basis sfs = E .on rows envs n a0 basis sfs) ∧
        (¬ BasisLostH1 rows n basis → E .auto rows envs n a0 basis sfs = E .off rows envs n a0 basis sfs))

/- The pinned readable form of VER-007: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.VER_007 : SemiflowEnc → Prop :=
fun E =>
  (∀ (rows : List (Transition × Deposit)) (envs : List PlaceId) (n : ℕ) (a0 : AMarking) (basis sfs : List Weight)
      (y : Weight),
      (y ∈ E SemiflowOpt.off rows envs n a0 basis sfs → y ∈ basis ∧ LawGate rows envs n y) ∧
        (y ∈ basis ∧ LawGate rows envs n y →
          LawFits lawRange rows n a0 y → y ∈ E SemiflowOpt.off rows envs n a0 basis sfs)) ∧
    (∀ (rows : List (Transition × Deposit)) (envs : List PlaceId) (n : ℕ) (a0 : AMarking) (basis sfs : List Weight)
        (y : Weight),
        (y ∈ E SemiflowOpt.on rows envs n a0 basis sfs → (y ∈ basis ∨ y ∈ sfs) ∧ LawGate rows envs n y) ∧
          ((y ∈ basis ∨ y ∈ sfs) ∧ LawGate rows envs n y →
            LawFits lawRange rows n a0 y → y ∈ E SemiflowOpt.on rows envs n a0 basis sfs)) ∧
      ∀ (rows : List (Transition × Deposit)) (envs : List PlaceId) (n : ℕ) (a0 : AMarking) (basis sfs : List Weight),
        (BasisLostH1 rows n basis →
            E SemiflowOpt.auto rows envs n a0 basis sfs = E SemiflowOpt.on rows envs n a0 basis sfs) ∧
          (¬BasisLostH1 rows n basis →
            E SemiflowOpt.auto rows envs n a0 basis sfs = E SemiflowOpt.off rows envs n a0 basis sfs)
-/
#guard_msgs in #print VER_007

/-! ## The reference -/

/-- The reference satisfies VER-007. -/
@[evidence holds VER_007]
theorem VER_007_reference : VER_007 refEnc := by
  refine ⟨fun rows envs n a0 basis sfs y => ?_, fun rows envs n a0 basis sfs y => ?_,
    fun rows envs n a0 basis sfs => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have e : y ∈ refEnc .off rows envs n a0 basis sfs ↔ y ∈ basis ∧ LawGate rows envs n y := by
      simp [refEnc]
    exact ⟨e.mp, fun h _ => e.mpr h⟩
  · have e : y ∈ refEnc .on rows envs n a0 basis sfs ↔
        (y ∈ basis ∨ y ∈ sfs) ∧ LawGate rows envs n y := by
      simp [refEnc, or_and_right]
    exact ⟨e.mp, fun h _ => e.mpr h⟩
  · simp [refEnc, h]
  · simp [refEnc, h]

/-- Every law in every list a VER-007 encoding hands the encoders passed the gate. -/
theorem VER_007_gate {E : SemiflowEnc} (h : VER_007 E) (md : SemiflowOpt)
    (rows : List (Transition × Deposit)) (envs : List PlaceId) (n : Nat) (a0 : AMarking)
    (basis sfs : List Weight) :
    ∀ y ∈ E md rows envs n a0 basis sfs, LawGate rows envs n y := by
  obtain ⟨hoff, hon, hauto⟩ := h
  intro y hy
  cases md with
  | off => exact ((hoff rows envs n a0 basis sfs y).1 hy).2
  | on => exact ((hon rows envs n a0 basis sfs y).1 hy).2
  | auto =>
    by_cases hl : BasisLostH1 rows n basis
    · rw [(hauto rows envs n a0 basis sfs).1 hl] at hy
      exact ((hon rows envs n a0 basis sfs y).1 hy).2
    · rw [(hauto rows envs n a0 basis sfs).2 hl] at hy
      exact ((hoff rows envs n a0 basis sfs y).1 hy).2

/-! ## The strengthened relation (AC6) -/

/-- One step of `ReachADInjStrs`: a firing of a deposit row whose successor keeps every law of
`ys` at its initial value (the conjunct each law adds to the rule body), or an unconstrained
injection (`encode_injection_rule`, `smt_encoder.rs`). -/
def StepADInjStrs (rows : List (Transition × Deposit)) (envs : List PlaceId) (ys : List Weight)
    (n : Nat) (a0 a a' : AMarking) : Prop :=
  (∃ tr ∈ rows, enabledA a tr.1 = true ∧ a' = fireAD a tr.1 tr.2 ∧
      ∀ y ∈ ys, dot y a' n = dot y a0 n) ∨
    ∃ p ∈ envs, a' = fun q => if q == p then a q + 1 else a q

/-- `ReachADInj` with every law of `ys` conjoined into the firing rules. -/
def ReachADInjStrs (rows : List (Transition × Deposit)) (envs : List PlaceId) (ys : List Weight)
    (n : Nat) (a0 : AMarking) : AMarking → Prop :=
  Relation.ReflTransGen (StepADInjStrs rows envs ys n a0) a0

/-- One injection leaves `y·M` unchanged when `y` is zero on the injected place below `n`. -/
theorem ver007_dot_inject {y : Weight} {a : AMarking} {n p : Nat} (hp : p < n → y p = 0) :
    dot y (fun q => if q == p then a q + 1 else a q) n = dot y a n := by
  rw [dot_eq_isum, dot_eq_isum]
  apply isum_congr
  intro q hq
  by_cases hqp : q = p
  · subst hqp; simp [hp hq]
  · simp [hqp]

/-- A law that passes the gate is conserved on every marking reachable with injection. -/
theorem ver007_conserved {rows : List (Transition × Deposit)} {envs : List PlaceId}
    {ys : List Weight} {n : Nat} {a0 a : AMarking} (hv : ∀ y ∈ ys, LawGate rows envs n y)
    (h : ReachADInj rows envs a0 a) : ∀ y ∈ ys, dot y a n = dot y a0 n := by
  intro y hy
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    rcases hs with ⟨tr, hmem, hen, rfl⟩ | ⟨p, hp, rfl⟩
    · exact (dot_fireAD_eq y ((hv y hy).h1 tr hmem) ((hv y hy).h2 tr hmem) hen).trans ih
    · exact (ver007_dot_inject ((hv y hy).h3 p hp)).trans ih

/-- Conjoining gate-passing laws into the firing rules keeps the reachable set. -/
theorem ver007_strengthened_reach_eq {rows : List (Transition × Deposit)} {envs : List PlaceId}
    {ys : List Weight} {n : Nat} {a0 : AMarking} (hv : ∀ y ∈ ys, LawGate rows envs n y) :
    ∀ a, ReachADInj rows envs a0 a ↔ ReachADInjStrs rows envs ys n a0 a := by
  intro a
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail hr hs ih =>
      rcases hs with ⟨tr, hmem, hen, rfl⟩ | ⟨p, hp, rfl⟩
      · exact Relation.ReflTransGen.tail ih (Or.inl ⟨tr, hmem, hen, rfl,
          ver007_conserved hv (Relation.ReflTransGen.tail hr (Or.inl ⟨tr, hmem, hen, rfl⟩))⟩)
      · exact Relation.ReflTransGen.tail ih (Or.inr ⟨p, hp, rfl⟩)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hs ih =>
      rcases hs with ⟨tr, hmem, hen, rfl, -⟩ | ⟨p, hp, rfl⟩
      · exact Relation.ReflTransGen.tail ih (Or.inl ⟨tr, hmem, hen, rfl⟩)
      · exact Relation.ReflTransGen.tail ih (Or.inr ⟨p, hp, rfl⟩)

/-- **AC6: the option is pure strengthening.** Under any encoding that meets VER-007, whatever the
setting, the relation with every handed law conjoined into the firing rules (injection rules
carrying none) reaches exactly the abstract reachable set over the deposit rows, so a genuine
violation stays reachable and no `Violated` turns into `Proven`. -/
@[evidence cites "VER-007" "AC6 and the pure-strengthening sentence: for every encoding that meets the VER-007 block, under off, on and auto, the strengthened relation over deposit rows (every handed law conjoined, injection rules carrying none) reaches exactly the abstract reachable set ReachADInj, so a genuine violation stays Violated; encoder modelled, not extracted"]
theorem VER_007_preserves_reach {E : SemiflowEnc} (h : VER_007 E) (md : SemiflowOpt)
    (rows : List (Transition × Deposit)) (envs : List PlaceId) (n : Nat)
    (basis sfs : List Weight) (a0 : AMarking) :
    ∀ a, ReachADInj rows envs a0 a ↔
      ReachADInjStrs rows envs (E md rows envs n a0 basis sfs) n a0 a :=
  ver007_strengthened_reach_eq (VER_007_gate h md rows envs n a0 basis sfs)

/-! ## Examples -/

/-- The empty initial marking. -/
def ver007_z : AMarking := fun _ => 0

/-- Moves one token from place 2 to place 3: a linear transition beside `tAll`. -/
def ver007_tMove : Transition :=
  { name := "move"
  , inputs := [{ place := 2, card := .one, guard := none }]
  , inhibitors := [], reads := [], resets := [] }

/-- `netAll` (an `all()` drain of place 0 into place 1) beside a move from place 2 to place 3:
the basis row `yUnit` (places 0 and 1) fails H1, the law on places 2 and 3 avoids the drained
place and passes the gate. -/
def ver007_netMix : List (Transition × Deposit) := [(tAll, [1]), (ver007_tMove, [3])]

/-- The law `m₂ + m₃ = const` of `ver007_netMix`. -/
def ver007_y23 : Weight := fun p => if p = 2 ∨ p = 3 then 1 else 0

/-- A row that fails `y·C = 0` on `netEnv` and is zero wherever H1 asks: weight 1 on place 0. -/
def ver007_y0 : Weight := fun p => if p = 0 then 1 else 0

/-- `exactly(2, a)` whose timeout forwards both tokens to `b` (IO-014): the deposit row `[b, b]`
alone, places `a = 0`, `b = 1`. -/
def ver007_netBB : List (Transition × Deposit) := [(tFwd, [pb, pb])]

/-- The flat rows of `exactly(2, a) → xor(c, timeout(forward(a, b)))`: `[c]`, `[b]`, `[b, b]`
(`fixed_rows_example`), places `a = 0`, `b = 1`, `c = 2`. -/
def ver007_netFwd : List (Transition × Deposit) := [(tFwd, [pc]), (tFwd, [pb]), (tFwd, [pb, pb])]

/-- `a + 2b + 2c`: zero on every column of `ver007_netFwd` read one token per place, but the
`[b, b]` row deposits two tokens on `b`. -/
def ver007_yBad : Weight := fun p => if p = 0 then 1 else if p = 1 then 2 else if p = 2 then 2 else 0

/-- `M0 = {a: 2}`. -/
def ver007_a0Fwd : AMarking := fun p => if p = 0 then 2 else 0

/-- Moves a token from place 0 to place 1 and clears place 2. -/
def ver007_tMoveReset : Transition :=
  { name := "move_reset"
  , inputs := [{ place := 0, card := .one, guard := none }]
  , inhibitors := [], reads := [], resets := [2] }

/-- The move with a reset, alone. -/
def ver007_netReset : List (Transition × Deposit) := [(ver007_tMoveReset, [1])]

/-- `m₀ + m₁ + m₂`: zero on the move's column, but it weights the cleared place 2. -/
def ver007_y012 : Weight := fun p => if p < 3 then 1 else 0

/-- `netEnv` has no consume-all or reset arc, so H1 holds of every weight. -/
theorem ver007_h1_netEnv (y : Weight) : ∀ tr ∈ (netEnv : List (Transition × Deposit)),
    ZeroOnNonlinear y tr.1 2 := by
  simp only [netEnv, List.mem_singleton, forall_eq]
  intro p hp h
  exfalso
  rcases h with h | h <;> revert h <;> rcases p with _ | _ | p <;>
    first | decide | exact absurd hp (by omega)

theorem ver007_yUnit_netEnv : LawGate netEnv [] 2 yUnit :=
  ⟨ver007_h1_netEnv yUnit, by simp only [netEnv, List.mem_singleton, forall_eq]; decide,
    by simp⟩

theorem ver007_yUnit_netEnv_inj : ¬ LawGate netEnv [envPlace] 2 yUnit :=
  fun h => absurd (h.h3 envPlace (by simp) (by decide)) (by decide)

theorem ver007_yUnit_netAll : ¬ LawGate netAll [] 2 yUnit := fun h =>
  absurd (h.h1 (tAll, [1]) (by simp [netAll]) 0 (by decide) (Or.inr (by decide))) (by decide)

theorem ver007_yUnit_netAll_inc : ∀ tr ∈ (netAll : List (Transition × Deposit)),
    dotIncD yUnit tr 2 = 0 := by
  simp only [netAll, List.mem_singleton, forall_eq]
  decide

theorem ver007_lost_netMix : BasisLostH1 ver007_netMix 4 [yUnit] :=
  ⟨yUnit, by simp, fun h =>
    absurd (h (tAll, [1]) (by simp [ver007_netMix]) 0 (by decide) (Or.inr (by decide)))
      (by decide)⟩

theorem ver007_y23_netMix : LawGate ver007_netMix [] 4 ver007_y23 := by
  refine ⟨?_, ?_, by simp⟩
  · simp only [ver007_netMix, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq]
    constructor <;> intro p hp hnl <;> revert hnl <;> rcases p with _ | _ | _ | _ | p <;>
      first | decide | exact absurd hp (by omega)
  · simp only [ver007_netMix, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq]
    decide

theorem ver007_y23_ne_yUnit : ver007_y23 ≠ yUnit := fun h =>
  absurd (congrFun h 0) (by decide)

theorem ver007_notLost_netEnv : ¬ BasisLostH1 netEnv 2 [ver007_y0] := by
  rintro ⟨y, hy, hn⟩
  simp only [List.mem_singleton] at hy
  subst hy
  exact hn (ver007_h1_netEnv ver007_y0)

theorem ver007_y0_netEnv : ¬ LawGate netEnv [] 2 ver007_y0 := fun h =>
  absurd (h.h2 (tConsume, [outPlace]) (by simp [netEnv])) (by decide)

/-- `tFwd` has no consume-all or reset arc, so H1 holds of every weight on its rows. -/
theorem ver007_h1_tFwd (y : Weight) (k : Nat) (hk : k ≤ 3) : ZeroOnNonlinear y tFwd k := by
  intro p hp h
  exfalso
  rcases h with h | h <;> revert h <;> rcases p with _ | _ | _ | p <;>
    first | decide | exact absurd hp (by omega)

/-- The counting gate keeps `a + b` on the `[b, b]` row: two consumed, two deposited. -/
theorem ver007_yUnit_netBB : LawGate ver007_netBB [] 2 yUnit :=
  ⟨by simp only [ver007_netBB, List.mem_singleton, forall_eq]; exact ver007_h1_tFwd _ _ (by omega),
    by simp only [ver007_netBB, List.mem_singleton, forall_eq]; decide, by simp⟩

/-- The `[b, b]` column does not annihilate `a + 2b + 2c`: `-2 + 2·2 = 2`. -/
theorem ver007_yBad_netFwd : ¬ LawGate ver007_netFwd [] 3 ver007_yBad := fun h =>
  absurd (h.h2 (tFwd, [pb, pb]) (by simp [ver007_netFwd])) (by decide)

/-- And `a + 2b + 2c` is not conserved: from `a = 2` the timed-out firing deposits two tokens on
`b` and `y·M` goes from `2` to `4`. A gate that let it through would prune that reachable
marking (the IO-014 retrodiction, reached through Phase 3). -/
theorem ver007_yBad_not_conserved :
    ReachADInj ver007_netFwd [] ver007_a0Fwd (fireAD ver007_a0Fwd tFwd [pb, pb]) ∧
    dot ver007_yBad ver007_a0Fwd 3 = 2 ∧
    dot ver007_yBad (fireAD ver007_a0Fwd tFwd [pb, pb]) 3 = 4 :=
  ⟨Relation.ReflTransGen.single
      (Or.inl ⟨(tFwd, [pb, pb]), by simp [ver007_netFwd], by decide, rfl⟩),
    by decide, by decide⟩

theorem ver007_y012_netReset : ¬ LawGate ver007_netReset [] 3 ver007_y012 := fun h =>
  absurd (h.h1 (ver007_tMoveReset, [1]) (by simp [ver007_netReset]) 2 (by decide)
    (Or.inl (by decide))) (by decide)

/-- The reference on the three settings: on `netEnv` the law `yUnit` offered as a semiflow
reaches the encoders with the option on and not with it off; with `envPlace` injected the gate
drops it (H3'); on `netAll` the gate drops it (H1); a gate-passing basis row (`ver007_y23` on
`ver007_netMix`) reaches the encoders with the option off and a failing one (`yUnit` on
`netAll`) does not; on the `[b, b]` row the counting column keeps `a + b`; under `auto`, on
`ver007_netMix`, whose basis row `yUnit` fails H1, the semiflow `ver007_y23` reaches the encoders,
and on `netEnv`, whose basis lost nothing to H1, the semiflow `yUnit` does not. -/
@[evidence nonvacuous VER_007]
theorem VER_007_nonvacuous :
    yUnit ∈ refEnc .on netEnv [] 2 ver007_z [] [yUnit] ∧
    yUnit ∉ refEnc .off netEnv [] 2 ver007_z [] [yUnit] ∧
    yUnit ∉ refEnc .on netEnv [envPlace] 2 ver007_z [] [yUnit] ∧
    yUnit ∉ refEnc .on netAll [] 2 ver007_z [] [yUnit] ∧
    ver007_y23 ∈ refEnc .off ver007_netMix [] 4 ver007_z [ver007_y23] [] ∧
    yUnit ∉ refEnc .off netAll [] 2 ver007_z [yUnit] [] ∧
    yUnit ∈ refEnc .on ver007_netBB [] 2 ver007_z [] [yUnit] ∧
    ver007_y23 ∈ refEnc .auto ver007_netMix [] 4 ver007_z [yUnit] [ver007_y23] ∧
    yUnit ∉ refEnc .auto netEnv [] 2 ver007_z [ver007_y0] [yUnit] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [refEnc, ver007_yUnit_netEnv]
  · simp [refEnc]
  · simp [refEnc, ver007_yUnit_netEnv_inj]
  · simp [refEnc, ver007_yUnit_netAll]
  · simp [refEnc, ver007_y23_netMix]
  · simp [refEnc, ver007_yUnit_netAll]
  · simp [refEnc, ver007_yUnit_netBB]
  · simp [refEnc, ver007_lost_netMix, ver007_y23_netMix]
  · simp only [refEnc, ver007_notLost_netEnv, if_false, List.mem_filter, List.mem_singleton,
      decide_eq_true_eq, not_and]
    intro h
    rw [h]
    exact ver007_y0_netEnv

/-! ## Wrong models -/

open Classical in
/-- An encoding with the gate `ok` in place of `LawGate`, otherwise the reference. -/
noncomputable def ver007_withGate
    (ok : List (Transition × Deposit) → List PlaceId → Nat → Weight → Prop) : SemiflowEnc :=
  fun md rows envs n _a0 basis sfs =>
    let g := fun y => decide (ok rows envs n y)
    match md with
    | .off => basis.filter g
    | .on => basis.filter g ++ sfs.filter g
    | .auto => if BasisLostH1 rows n basis then basis.filter g ++ sfs.filter g
        else basis.filter g

/-- An `off` that lets the validated semiflows through (AC2 broken). -/
noncomputable def ver007_encOffLeaks : SemiflowEnc :=
  fun md rows envs n a0 basis sfs =>
    match md with
    | .off => refEnc .on rows envs n a0 basis sfs
    | md => refEnc md rows envs n a0 basis sfs

/-- An `off` that hands every basis row over without the gate. -/
noncomputable def ver007_encOffNoGate : SemiflowEnc :=
  fun md rows envs n a0 basis sfs =>
    match md with
    | .off => basis
    | md => refEnc md rows envs n a0 basis sfs

/-- An `off` that hands nothing over: the basis rows never reach the encoders. -/
noncomputable def ver007_encOffEmpty : SemiflowEnc :=
  fun md rows envs n a0 basis sfs =>
    match md with
    | .off => []
    | md => refEnc md rows envs n a0 basis sfs

open Classical in
/-- An `on` that hands over the validated semiflows only, dropping the basis rows. -/
noncomputable def ver007_encOnSfsOnly : SemiflowEnc :=
  fun md rows envs n a0 basis sfs =>
    match md with
    | .on => sfs.filter fun y => decide (LawGate rows envs n y)
    | md => refEnc md rows envs n a0 basis sfs

/-- A gate that re-checks only `y·C = 0`, without H1 and H3' (AC1 broken). -/
noncomputable def ver007_encGateCOnly : SemiflowEnc :=
  ver007_withGate fun rows _ n y => ∀ tr ∈ rows, dotIncD y tr n = 0

/-- A gate on the transition columns only, without the injector columns (H3' broken). -/
noncomputable def ver007_encNoEnvZero : SemiflowEnc :=
  fun md rows _ n a0 basis sfs => refEnc md rows [] n a0 basis sfs

/-- A gate whose H1 checks the consume-all places and forgets the reset places. -/
noncomputable def ver007_encResetBlind : SemiflowEnc :=
  ver007_withGate fun rows envs n y =>
    (∀ tr ∈ rows, ∀ p, p < n → consumeAllAt tr.1 p = true → y p = 0) ∧
    (∀ tr ∈ rows, dotIncD y tr n = 0) ∧ ∀ p ∈ envs, p < n → y p = 0

/-- A gate that reads every deposit row as one token per claimed place (`dotInc`, the
`post = if claimed then 1 else 0` column the flattener wrote before the IO-014 fix). -/
noncomputable def ver007_encUnitColumn : SemiflowEnc :=
  ver007_withGate fun rows envs n y =>
    (∀ tr ∈ rows, ZeroOnNonlinear y tr.1 n) ∧
    (∀ tr ∈ rows, dotInc y tr n = 0) ∧ ∀ p ∈ envs, p < n → y p = 0

/-- An `on` that drops the semiflows (AC4 broken). -/
noncomputable def ver007_encOnOmits : SemiflowEnc :=
  fun md rows envs n a0 basis sfs =>
    match md with
    | .on => refEnc .off rows envs n a0 basis sfs
    | md => refEnc md rows envs n a0 basis sfs

/-- An `auto` that always unions. -/
noncomputable def ver007_encAutoAlways : SemiflowEnc :=
  fun md rows envs n a0 basis sfs =>
    match md with
    | .auto => refEnc .on rows envs n a0 basis sfs
    | md => refEnc md rows envs n a0 basis sfs

/-- An `auto` that never unions. -/
noncomputable def ver007_encAutoNever : SemiflowEnc :=
  fun md rows envs n a0 basis sfs =>
    match md with
    | .auto => refEnc .off rows envs n a0 basis sfs
    | md => refEnc md rows envs n a0 basis sfs

open Classical in
/-- An `auto` that unions when the gate dropped any basis row, for whatever reason. -/
noncomputable def ver007_encAutoAnyDrop : SemiflowEnc :=
  fun md rows envs n a0 basis sfs =>
    match md with
    | .auto => if ∃ y ∈ basis, ¬ LawGate rows envs n y then refEnc .on rows envs n a0 basis sfs
        else refEnc .off rows envs n a0 basis sfs
    | md => refEnc md rows envs n a0 basis sfs

/-- Line 2 forbids an `off` that lets a validated semiflow through: `yUnit` on `netEnv`. -/
@[evidence forbids VER_007]
theorem VER_007_forbids_offLeaks : ¬ VER_007 ver007_encOffLeaks := by
  intro h
  have := ((h.1 netEnv [] 2 ver007_z [] [yUnit] yUnit).1
    (by simp [ver007_encOffLeaks, refEnc, ver007_yUnit_netEnv])).1
  simp at this

/-- Line 2 forbids an `off` that skips the gate on the basis rows: `yUnit` on `netAll` fails H1
and must not reach the encoders. -/
@[evidence forbids VER_007]
theorem VER_007_forbids_offNoGate : ¬ VER_007 ver007_encOffNoGate := by
  intro h
  have := ((h.1 netAll [] 2 ver007_z [yUnit] [] yUnit).1 (by simp [ver007_encOffNoGate])).2
  exact ver007_yUnit_netAll this

/-- Line 2 forbids an `off` that drops the basis rows: `ver007_y23` passes the gate on
`ver007_netMix` and must reach the encoders. -/
@[evidence forbids VER_007]
theorem VER_007_forbids_offEmpty : ¬ VER_007 ver007_encOffEmpty := by
  intro h
  have := (h.1 ver007_netMix [] 4 ver007_z [ver007_y23] [] ver007_y23).2 ⟨by simp, ver007_y23_netMix⟩
    (by decide)
  simp [ver007_encOffEmpty] at this

/-- Line 3 forbids an `on` that drops the basis rows: `ver007_y23` on `ver007_netMix`. -/
@[evidence forbids VER_007]
theorem VER_007_forbids_onSfsOnly : ¬ VER_007 ver007_encOnSfsOnly := by
  intro h
  have := (h.2.1 ver007_netMix [] 4 ver007_z [ver007_y23] [] ver007_y23).2
    ⟨Or.inl (by simp), ver007_y23_netMix⟩ (by decide)
  simp [ver007_encOnSfsOnly] at this

/-- Line 3 forbids a gate that re-checks only `y·C = 0`: the Farkas row `yUnit` on `netAll`
annihilates the shipped column and weights the drained place
(`semiflow_gate_is_necessary`). -/
@[evidence forbids VER_007]
theorem VER_007_forbids_gateCOnly : ¬ VER_007 ver007_encGateCOnly := by
  intro h
  have := ((h.2.1 netAll [] 2 ver007_z [] [yUnit] yUnit).1
    (by
      simp only [ver007_encGateCOnly, ver007_withGate, List.mem_append, List.mem_filter,
        decide_eq_true_eq]
      exact Or.inr ⟨by simp, ver007_yUnit_netAll_inc⟩)).2
  exact ver007_yUnit_netAll this

/-- Line 3 forbids a gate without the injector columns: `yUnit` on `netEnv` with `envPlace`
injected (`injection_hypothesis_is_necessary`). -/
@[evidence forbids VER_007]
theorem VER_007_forbids_noEnvZero : ¬ VER_007 ver007_encNoEnvZero := by
  intro h
  have := ((h.2.1 netEnv [envPlace] 2 ver007_z [] [yUnit] yUnit).1
    (by simp [ver007_encNoEnvZero, refEnc, ver007_yUnit_netEnv])).2
  exact ver007_yUnit_netEnv_inj this

/-- Line 3 forbids a gate whose H1 forgets reset arcs: `m₀ + m₁ + m₂` on a move from 0 to 1 that
clears place 2 annihilates the column and weights the cleared place. -/
@[evidence forbids VER_007]
theorem VER_007_forbids_resetBlind : ¬ VER_007 ver007_encResetBlind := by
  intro h
  have hg : (∀ tr ∈ ver007_netReset, ∀ p : Nat, p < 3 → consumeAllAt tr.1 p = true →
        ver007_y012 p = 0) ∧
      (∀ tr ∈ ver007_netReset, dotIncD ver007_y012 tr 3 = 0) ∧
      ∀ p ∈ ([] : List PlaceId), p < 3 → ver007_y012 p = 0 := by
    refine ⟨?_, ?_, by simp⟩
    · simp only [ver007_netReset, List.mem_singleton, forall_eq]
      intro p hp hca; revert hca
      rcases p with _ | _ | _ | p <;> first | decide | exact absurd hp (by omega)
    · simp only [ver007_netReset, List.mem_singleton, forall_eq]; decide
  have := ((h.2.1 ver007_netReset [] 3 ver007_z [] [ver007_y012] ver007_y012).1
    (by
      simp only [ver007_encResetBlind, ver007_withGate, List.mem_append, List.mem_filter,
        decide_eq_true_eq]
      exact Or.inr ⟨by simp, hg⟩)).2
  exact ver007_y012_netReset this

/-- Line 3 forbids a gate that reads a multi-token deposit row as one token per place: on the
rows `[c]`, `[b]`, `[b, b]` of a timeout forward from `exactly(2, a)`, the law `a + 2b + 2c`
annihilates the one-token columns but not the real `[b, b]` column, and it is false of the
executor (`ver007_yBad_not_conserved`). -/
@[evidence forbids VER_007]
theorem VER_007_forbids_unitColumn : ¬ VER_007 ver007_encUnitColumn := by
  intro h
  have hg : (∀ tr ∈ ver007_netFwd, ZeroOnNonlinear ver007_yBad tr.1 3) ∧
      (∀ tr ∈ ver007_netFwd, dotInc ver007_yBad tr 3 = 0) ∧
      ∀ p ∈ ([] : List PlaceId), p < 3 → ver007_yBad p = 0 := by
    refine ⟨?_, ?_, by simp⟩
    · simp only [ver007_netFwd, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq]
      exact ⟨ver007_h1_tFwd _ _ le_rfl, ver007_h1_tFwd _ _ le_rfl, ver007_h1_tFwd _ _ le_rfl⟩
    · simp only [ver007_netFwd, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq]
      decide
  have := ((h.2.1 ver007_netFwd [] 3 ver007_z [] [ver007_yBad] ver007_yBad).1
    (by
      simp only [ver007_encUnitColumn, ver007_withGate, List.mem_append, List.mem_filter,
        decide_eq_true_eq]
      exact Or.inr ⟨by simp, hg⟩)).2
  exact ver007_yBad_netFwd this

/-- Line 3 forbids an `on` that drops the semiflows: `yUnit` on `netEnv`. -/
@[evidence forbids VER_007]
theorem VER_007_forbids_onOmits : ¬ VER_007 ver007_encOnOmits := by
  intro h
  have := (h.2.1 netEnv [] 2 ver007_z [] [yUnit] yUnit).2 ⟨Or.inr (by simp), ver007_yUnit_netEnv⟩
    (by decide)
  simp [ver007_encOnOmits, refEnc] at this

/-- Line 4 forbids an `auto` that always unions: on `netEnv` with an empty basis nothing was
lost to H1, yet `yUnit` would reach the encoders. -/
@[evidence forbids VER_007]
theorem VER_007_forbids_autoAlways : ¬ VER_007 ver007_encAutoAlways := by
  intro h
  have hl : ¬ BasisLostH1 netEnv 2 [] := by rintro ⟨y, hy, -⟩; simp at hy
  have he := (h.2.2 netEnv [] 2 ver007_z [] [yUnit]).2 hl
  have hin : yUnit ∈ ver007_encAutoAlways .auto netEnv [] 2 ver007_z [] [yUnit] := by
    simp [ver007_encAutoAlways, refEnc, ver007_yUnit_netEnv]
  rw [he] at hin
  simp [ver007_encAutoAlways, refEnc] at hin

/-- Line 4 forbids an `auto` that never unions: on `ver007_netMix` the basis row `yUnit` fails
H1, so the semiflow `ver007_y23`, which passes the gate, must reach the encoders. -/
@[evidence forbids VER_007]
theorem VER_007_forbids_autoNever : ¬ VER_007 ver007_encAutoNever := by
  intro h
  have he := (h.2.2 ver007_netMix [] 4 ver007_z [yUnit] [ver007_y23]).1 ver007_lost_netMix
  have hin : ver007_y23 ∈ ver007_encAutoNever .on ver007_netMix [] 4 ver007_z [yUnit] [ver007_y23] := by
    simp [ver007_encAutoNever, refEnc, ver007_y23_netMix]
  rw [← he] at hin
  simp only [ver007_encAutoNever, refEnc, List.mem_filter, List.mem_singleton] at hin
  exact ver007_y23_ne_yUnit hin.1

/-- Line 4 forbids an `auto` that unions on any dropped row: on `netEnv` the basis row
`ver007_y0` fails `y·C = 0` but not H1, so the union stays off and `yUnit` must not reach the
encoders. -/
@[evidence forbids VER_007]
theorem VER_007_forbids_autoAnyDrop : ¬ VER_007 ver007_encAutoAnyDrop := by
  intro h
  have he := (h.2.2 netEnv [] 2 ver007_z [ver007_y0] [yUnit]).2 ver007_notLost_netEnv
  have hin : yUnit ∈ ver007_encAutoAnyDrop .auto netEnv [] 2 ver007_z [ver007_y0] [yUnit] := by
    have hd : ∃ y ∈ [ver007_y0], ¬ LawGate netEnv [] 2 y :=
      ⟨ver007_y0, by simp, ver007_y0_netEnv⟩
    simp only [ver007_encAutoAnyDrop, if_pos hd]
    simp [refEnc, ver007_yUnit_netEnv]
  rw [he] at hin
  simp only [ver007_encAutoAnyDrop, refEnc, List.mem_filter, List.mem_singleton,
    decide_eq_true_eq] at hin
  exact absurd (congrFun hin.1 1) (by decide)

end Libpetri.Spec
