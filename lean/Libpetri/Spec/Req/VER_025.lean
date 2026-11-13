import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Novel.FiringBound.Witness
import Libpetri.Spec.Text.VER_025

set_option linter.missingDocs true

/-!
# VER-025: Bounded witness phase (`spec/07-verification.md`)

Directly before the flat fixpoint query the verifier asks one bounded-run query at depth `D`
over firings and environment-injection steps; a `sat` answer is decoded, replayed under the
exact step relation, trimmed to an irredundant run and reported `Violated`; every other answer
hands over to the fixpoint query. The phase proves nothing.

The requirement is a predicate over a triple `(S, W, P)`:

* `S : ScriptRel`, the phase's script read as a constraint system over the selectors and the
  marking variables (the shape of `BmcModelEnv`, `Novel/FiringBound/Bmc.lean`);
* `W : PhaseFn`, the phase itself, from the depth, the entry gate, the name-alignment flag, the
  flat net, the injections, the seed, the violation and the solver's answer to an outcome, or to
  nothing when the phase does not run (the shape of `witnessPhase`, `Novel/FiringBound/Witness.lean`);
* `P : PipelineFn`, the pipeline around the phase, from the phase's outcome, the time it spent,
  the total budget and the fixpoint route to a verdict (the shape of `pipeline`).

The witness triple is `ver025_script` (`BmcModelEnv`), `witnessPhase` and `pipeline`. The
statement is checked against them (`VER_025_reference`), against wrong phases (one that reports
the solver's run without replaying it, one that reads a run from a model with no selector, a
trim that drops a needed step, a trim in another order, a trim without the cut to the violating
prefix, an injection step that ignores its bound, a phase that runs at depth 0), against wrong
pipelines (one that reads `unsat` as a proof, one that starves the fixpoint route after the
phase, one that never charges the phase's time) and against a script that is always
satisfiable. The report text, the budget, the option default and its
error are pure functions, pinned below with `#guard`.
-/

namespace Libpetri.Spec

open Libpetri (AMarking PlaceId Transition Card)
open Libpetri.Novel.FiringBound

/-! ## The model -/

/-- The phase's script read as a constraint system: `S rows injs n a0 badI d s M` says the
selector values `s` and the marking variables `M` satisfy the depth-`d` script of the flat net
`rows` (`n` places) with the injections `injs`, the seed `a0` and the integer violation `badI`.
The shape of `BmcModelEnv`. -/
abbrev ScriptRel : Type :=
  List Novel.FiringBound.Row → List Inj → Nat → AMarking → ((PlaceId → Int) → Prop) → Nat → (Nat → Int) →
    (Nat → PlaceId → Int) → Prop

/-- A witness phase: `W D enter nameAlignment rows injs a0 isBad ans` is the phase's outcome at
depth `D` on the flat net `rows` with the injections `injs`, the seed `a0` and the violation
`isBad`, when the solver answers `ans`; `none` when the phase does not run. `enter` is the entry
gate (the pipeline reached the flat fixpoint query, the encoding stays flat, and the ν gate lets
the phase run); `nameAlignment` says the property is a name-alignment property. The shape of
`witnessPhase`. -/
abbrev PhaseFn : Type :=
  Nat → Bool → Bool → List Novel.FiringBound.Row → List Inj → AMarking → (AMarking → Bool) → Witness.Answer →
    Option Witness.Outcome

/-- A pipeline around the phase: `P phase elapsed budget fixpoint` is the verdict, from the
phase's outcome (`none`: it did not run), the time it spent, the total budget and the fixpoint
route as a function of the budget it is given. The shape of `pipeline`. -/
abbrev PipelineFn : Type :=
  Option Witness.Outcome → Nat → Nat → (Nat → Witness.Verdict) → Witness.Verdict

/-- **The reference script**: `BmcModelEnv`, the constraint system `encode_bounded_run` emits
with the injection selectors (P4: the SMT-LIB text denotes it). -/
def ver025_script : ScriptRel := fun rows injs n a0 badI d s M =>
  BmcModelEnv rows injs n a0 badI d s M

/- The reference script, the phase model and the pipeline model are the witness triple of
VER-025's `holds` theorem. -/
#spec_witness ver025_script
#spec_witness witnessPhase
#spec_witness pipeline

/-! ## VER-025: Bounded witness phase -/

requirement VER_025
  id "VER-025"
  title "Bounded Witness Phase"
  kind B
  scope "the SMT verifier, all implementations"
  source verbatim "spec/07-verification.md"
  covers VER_025.s1, VER_025.s2, VER_025.s3, VER_025.s4, VER_025.s5, VER_025.s6, VER_025.s7,
        VER_025.s8, VER_025.s9, VER_025.s10, VER_025.s11, VER_025.s12, VER_025.s13, VER_025.s14,
        VER_025.s15, VER_025.s16, VER_025.s17, VER_025.s18, VER_025.s19, VER_025.s20, VER_025.s21,
        VER_025.s22, VER_025.s23, VER_025.s24, VER_025.s25, VER_025.s26, VER_025.s27, VER_025.s28
  reading "For every flat net (rows, n places), injection list, seed a0, depth d and violation (badI over integers, bad over markings) such that the rows are well formed (P1, P2), every injected place is a place of the net, no place is injected twice (P9), badI agrees with bad (P5) and a0 is within the post-caps: the script S at depth d has a model iff some run of at most d steps, firings and injections, replays under the exact step relation (replayEnv) to a marking that violates."
          "Under P1, P2, injected places in the net and P5: every model of S at depth d decodes, read at T + J (decode_bounded_run), to a run that replays to a violating marking."
          "The phase W does not run (none) iff the depth is 0 or the entry gate is closed."
          "Run at a positive depth on a name-alignment property, W ends inconclusive with the name-alignment reason, whatever the solver answers."
          "Whenever W reports a run r: the solver answered sat with a model s, the model decodes at T + J to a run (decodeModel), and r is the trim of that run (trim: the cut to the violating prefix, then passes from the last step to the first until one changes nothing)."
          "Run at a positive depth on any other property, a sat model that defines no selector gives inconclusive (did not replay); one whose decoded run replays to a violation gives a reported run; one whose decoded run does not gives inconclusive (did not replay)."
          "Run at a positive depth on any other property, unsat gives 'no run', unknown gives inconclusive (unknown), a transport failure inconclusive (transport) and a spent phase budget inconclusive (budget)."
          "The pipeline P answers Violated with the phase's run when the phase reported one."
          "On every other outcome of a phase that ran, the pipeline's verdict is the fixpoint route's verdict at the total budget minus the time the phase spent."
          "When the phase did not run, the pipeline's verdict is the fixpoint route's verdict at the whole budget."
  assumes "The model is the triple (S, W, P) of ScriptRel, PhaseFn and PipelineFn. S is the script read as a constraint system (P4 of Novel/FiringBound.lean: the SMT-LIB text the ports emit denotes BmcModelEnv, and the solver's sat and unsat are correct). W is the phase from the depth D, the entry gate enter, the name-alignment flag, the flat net as deposit rows (Row = transition and deposit, the exact abstract semantics of VER-004: enabledA, fireAD), the injection list (Inj = flat place index and bound, none under AlwaysAvailable), the seed, the violation isBad and the solver's answer (Witness.Answer: sat with the selector values the model defines, none for a selector it is silent on; unsat; unknown; a transport failure; a spent phase budget). P is the pipeline from the phase outcome, the time spent, the total budget and the fixpoint route as a function of the budget left. The witness triple is ver025_script (BmcModelEnv), witnessPhase and pipeline (Novel/FiringBound/Witness.lean)."
          "The entry gate of the first three quoted sentences is the input enter: the pipeline reached the flat fixpoint query, the fixpoint query does not take the name-coloured encoding (NU-053), and the net has no match transitions or the property is reachability-safety with a budget place declared. Which nets and properties open it is decided by the pipeline outside the model (VER-001, NU-050), so the sentences are encoded as line 3: the phase runs exactly when enter is true and D is positive. 'Directly before the fixpoint script is encoded' is the order of P: the phase's outcome is decided before the fixpoint route is called (lines 8 to 10)."
          "The fourth quoted sentence is line 3 at D = 0 and line 10: the phase does not run and the verdict is the fixpoint route's at the whole budget. Its 'route, report and scripts' are not in the model: the route is the fixpoint route's by line 10, the report has no phase line (ver025_report none = [], pinned below), and the scripts of encodeScripts() are outside it."
          "The fifth quoted sentence is line 3 and ver025_report none = [] (no report line). 'Send no query' is not expressible: the solver's answer is an input of W, so the model cannot see whether a query was sent; a W that does not run (none) uses no answer. The same holds for 'send no query' in the eighth quoted sentence, whose outcome line 4 fixes for every answer, so the outcome does not depend on one."
          "The sixth quoted sentence (Ignore) is the injection list []: under Ignore the verifier builds no injection, and lines 3 to 7 hold at every injection list, [] included, so the phase runs where it runs on any other flat net. At [] the step relation is the firing relation of VER-019 (replayEnv_nil, bmcModelEnv_nil). The Arrivals rewrite produces a closed net, which is again the case injs = []."
          "The seventh quoted sentence (the VER-003 replay disabled) is not an input of the model: lines 5 and 6 require the phase's own replay whatever the option, so a run W reports is a replayed one (VER_025_reported_run). counterexampleConfirmed is not in the model; that a run W reports is replayed is VER_025_reported_run."
          "The ninth and tenth quoted sentences are about the SMT-LIB text (byte identity across implementations; J = 0 byte-identical to VER-019). The text is not modelled (P4); the scripts are checked by the golden-file parity tests of VER-013. What the model states is the constraint system: lines 1 and 2, and at J = 0 BmcModelEnv is VER-019's BmcModel (bmcModelEnv_nil, cited for VER-025)."
          "The eleventh quoted sentence (decode) is decodeModel at T + J in lines 5 and 6, and decodeRust in line 2: values in [0, T) are transition steps (rows), values in [T, T + J) injection steps, anything else ends the run, a selector the model leaves undefined (none) is read as idle, and a model that defines none of the selectors below D yields no run, which line 6 makes inconclusive (did not replay), as decode_bounded_run returning None does. Line 2 reads a model of S, which defines every selector (Witness.defined; decodeModel_defined)."
          "The twelfth quoted sentence (replay) is replays (replayEnv followed by the property) in lines 1, 2, 5 and 6: a transition step fires a row that is enabled (enabledA) and whose successor passes the post-caps (capsOk), an injection step is taken only while its guard holds (injOk: below the bound under Bounded(k), always under AlwaysAvailable) and has no post-cap, and the run is accepted only when every step is taken and the last marking violates (stepIdx, Bmc.lean). That this is the step relation of the HORN rules is stepEnv_injsOf (StepEnv at the verifier's injection list is EnvSemantics.StepAE), cited for VER-025; that a replayed run is a derivation in the strengthened CHC system is witness_horn_derivation."
          "The thirteenth quoted sentence (trim) is line 5: the reported run is trim of the decoded run, the reference trim of Witness.lean (violatingPrefix: the shortest prefix that replays to a violating marking, the empty one included; then passes from the last index to the first, each replacing the run by the violating prefix of the run without that step when one exists, repeated until a pass changes nothing). The algorithm is part of the statement, so the run is fixed for a model and a trim in another order is told apart (VER_025_forbids_trimFirst), as is one without the cut (VER_025_forbids_noCut). What follows, from the statement alone (VER_025_reported_run, VER_025_initial_violation): the reported run is a sublist of the decoded run, replays, ends at the first violating marking it reaches, has no single step that can be dropped, and is the empty run when M0 violates. The trimmed run is not claimed to be a shortest run."
          "The fourteenth and seventeenth quoted sentences are line 5 (the reported run is the trimmed run, replayed) and line 8 (the result is Violated with that run). The labels (a transition's name, inject(<place>)) are the pure function ver025_stepLabel, pinned below. counterexampleConfirmed true, the route of the SMT pipeline and the result text of VER-018 and VER-019 (RESULT, VIOLATED, the trace, the Firing sequence line, the untimed warning) are outside the model."
          "The fifteenth quoted sentence (budget) is the pure function ver025_budgetMs, pinned below. The wall clock, the transport's clamp and 'the query shall receive what is left of it' are not modelled: elapsed is any number the phase spent, line 9 charges it against the total budget, and a spent phase budget is the answer budgetSpent (line 7)."
          "The sixteenth quoted sentence and the status lines are the pure functions ver025_header, ver025_status and ver025_report, pinned below: ver025_report gives no line when the phase does not run and the header and exactly one status line when it does. The reasons are ver025_reasonText; the transport's failure message (a reply with an (error ...) line included, which is the answer failure) and the NU-055 reason are parameters, since the spec does not fix their text in VER-025."
          "The eighteenth quoted sentence (the ν guard of NU-050) and the nineteenth (the counterexample-timing step of VER-023) are steps the result passes through after the pipeline of this model; neither is modelled. The model's Violated is the phase's result before them."
          "The twentieth to twenty-third quoted sentences are lines 6, 7, 9 and 10: unsat gives 'no run' and every other ending without a run gives inconclusive with its reason (lines 6, 7), and the pipeline then hands over to the fixpoint route at the total budget minus the time the phase spent (line 9), so the phase changes no verdict except through that time. The pipeline answers Proven only through the fixpoint route (VER_025_never_proven, from lines 8 to 10; Witness.Outcome has no proven outcome at all). 'Shall not read an unsat answer as a proof' is lines 7 and 9 together: unsat gives 'no run', after which the verdict is the fixpoint route's (VER_025_forbids_unsatProven). What 'no run' means is line 1 under P4: no run of at most D steps reaches a violation (VER_025_noRun_exact below, from the statement). It says nothing about D + 1 steps."
          "The twenty-fourth and twenty-sixth quoted sentences (default 8, the negative-depth error) are the pure functions ver025_depthDefault and ver025_depthError, pinned below. The twenty-fifth (a positive n asks one query at depth n) is the depth argument D of W, at which lines 5 and 6 decode; that one query is sent is not modelled, as for 'send no query'."
          "The twenty-seventh quoted sentence (the dump phase name witness) is the constant ver025_dumpPhase, pinned below; the dump itself is not modelled. The twenty-eighth (encodeScripts' witness member) is about the scripts, which are not modelled (P4)."
          "AC1 (envBoundedPair: t takes one(e) to p1, e under Bounded(2), empty M0, PlaceBound(p1, 1)) is VER_025_nonvacuous: at depth 8, a padded model's run of 5 steps is trimmed to a run of 4 steps, two inject(e) and two t, that replays and is irredundant, its status line is 'a run of 4 steps reaches a violation (replayed; depth 8)', and the pipeline answers Violated without the fixpoint route (no fixpoint query). 'Confirmed' is outside the model (seventh quoted sentence)."
          "AC2 (the same net, PlaceBound(p1, 4), shortest run 10 steps) is VER_025_ac2: at depth 10 a model gives a reported run of 10 steps; at depth 8 the answer unsat gives 'no run' (line 7), its status line is pinned, and the pipeline then answers what the fixpoint route answers at the budget left (line 9). That the depth-8 script is in fact unsat is the solver's answer under P4 (line 1 says what it means); it is not re-derived here by enumerating runs."
          "AC3 (depth 0 off) is line 3 and line 10, and ver025_report none = []; the encoded scripts and the dump are outside the model."
          "AC4 (the name-coloured encoding) and AC5 (the ν gates) are the entry gate enter of line 3, which the pipeline sets outside the model. AC5's ν guard note is the eighteenth quoted sentence, not modelled."
          "AC6 (name alignment) is line 4."
          "AC7 (the stub replies unsat, unknown, a transport failure, a spent budget, a sat model whose run does not replay: each its own status line, then the fixpoint query, never Proven) is lines 6, 7 and 9, VER_025_never_proven and the status lines pinned below."
          "AC8 (selector range: T + j decodes as injection j, T + J or more or a negative selector ends the run) is decodeRust and decodeModel in lines 2, 5 and 6, pinned on examples below (VER_025_ac8), with an undefined selector read as idle and a model with no selector read as no run."
          "AC9 (injection replay: an injection at a place holding its bound does not replay, an unbounded one always does, its label is inject(<place>), no post-cap) is the reference replay of lines 5 and 6, pinned on examples below (VER_025_ac9), and ver025_stepLabel."
          "AC10 (trim: a padded model is reported as a run of 4 steps; dropping any single step of a reported run makes it fail to replay) is line 5 with VER_025_reported_run, and VER_025_nonvacuous."
          "AC11 (M0 violates: a run of 0 steps) is VER_025_initial_violation (from the statement: a reported run is [] whenever M0 violates, whatever model the solver returned) and VER_025_ac11: an all-idle model, and a model on the ring t1: p0 to p1, t2: p1 to p0 that leaves M0 and comes back to a violating marking, are both reported as the run []; a run that passes a violating marking and goes on is reported cut there; its status line is 'a run of 0 steps'. The enumeration route and VER-018/019 being off is the entry gate."
          "AC12 (the replay option off) is the seventh quoted sentence: lines 5 and 6 hold whatever the option."
          "AC13 (Ignore) is the sixth quoted sentence: the injection list is []."
          "AC14 (scripts: J = 0 byte-identical to VER-019, golden witness.smt2, dump file names) is about the SMT-LIB text and the dump, outside the model (P4); at the constraint level, J = 0 is bmcModelEnv_nil."
          "AC15 (default 8, one query at a positive n, the error for -1) is ver025_depthDefault and ver025_depthError, pinned below, and the depth argument of W."
          "The test derivation (the envBoundedPair fixtures at depths 8 and 10, one test per gate and outcome, the depth-0 opt-out of tests that pin the fixpoint query) is AC1, AC2, AC3 and AC7, as above."
  signoff "2026-11-13 5ae1d410184671de"
  statement : ScriptRel → PhaseFn → PipelineFn → Prop :=
    fun S W P =>
      (∀ (rows : List Novel.FiringBound.Row) (injs : List Inj) (n : Nat) (a0 : AMarking)
          (badI : (PlaceId → Int) → Prop) (bad : AMarking → Prop) (d : Nat),
        WellFormedRows n rows → InjsIn n injs → InjsDistinct injs → BadAgrees badI bad →
          capsOk injs a0 = true →
          ((∃ s M, S rows injs n a0 badI d s M) ↔
            ∃ ts a, ts.length ≤ d ∧ replayEnv rows injs a0 ts = some a ∧ bad a)) ∧
      (∀ (rows : List Novel.FiringBound.Row) (injs : List Inj) (n : Nat) (a0 : AMarking)
          (badI : (PlaceId → Int) → Prop) (isBad : AMarking → Bool) (d : Nat) (s : Nat → Int)
          (M : Nat → PlaceId → Int),
        WellFormedRows n rows → InjsIn n injs → BadAgrees badI (fun a => isBad a = true) →
          S rows injs n a0 badI d s M →
          replays rows injs isBad a0 (decodeRust (rows.length + injs.length) s d) = true) ∧
      (∀ D enter na rows injs a0 isBad ans,
        W D enter na rows injs a0 isBad ans = none ↔ (D = 0 ∨ enter = false)) ∧
      (∀ D rows injs a0 isBad ans, D ≠ 0 →
        W D true true rows injs a0 isBad ans = some (.inconclusive .nameAlignment)) ∧
      (∀ D enter na rows injs a0 isBad ans r,
        W D enter na rows injs a0 isBad ans = some (.violated r) →
          ∃ s run, ans = .sat s ∧ decodeModel (rows.length + injs.length) s D = some run ∧
            r = trim (replays rows injs isBad a0) run) ∧
      (∀ D rows injs a0 isBad s, D ≠ 0 →
        (decodeModel (rows.length + injs.length) s D = none →
          W D true false rows injs a0 isBad (.sat s) = some (.inconclusive .noReplay)) ∧
        ∀ run, decodeModel (rows.length + injs.length) s D = some run →
          (replays rows injs isBad a0 run = true →
            ∃ r, W D true false rows injs a0 isBad (.sat s) = some (.violated r)) ∧
          (replays rows injs isBad a0 run = false →
            W D true false rows injs a0 isBad (.sat s) = some (.inconclusive .noReplay))) ∧
      (∀ D rows injs a0 isBad, D ≠ 0 →
        W D true false rows injs a0 isBad .unsat = some .noRun ∧
        W D true false rows injs a0 isBad .unknown = some (.inconclusive .unknown) ∧
        W D true false rows injs a0 isBad .failure = some (.inconclusive .transport) ∧
        W D true false rows injs a0 isBad .budgetSpent = some (.inconclusive .budget)) ∧
      (∀ r elapsed budget fixpoint, P (some (.violated r)) elapsed budget fixpoint = .violated r) ∧
      (∀ o elapsed budget fixpoint, (∀ r, o ≠ .violated r) →
        P (some o) elapsed budget fixpoint = fixpoint (budget - elapsed)) ∧
      (∀ elapsed budget fixpoint, P none elapsed budget fixpoint = fixpoint budget)

/- The pinned readable form of VER-025: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.VER_025 : ScriptRel → PhaseFn → PipelineFn → Prop :=
fun S W P =>
  (∀ (rows : List Novel.FiringBound.Row) (injs : List Inj) (n : ℕ) (a0 : AMarking) (badI : (PlaceId → ℤ) → Prop)
      (bad : AMarking → Prop) (d : ℕ),
      WellFormedRows n rows →
        InjsIn n injs →
          InjsDistinct injs →
            BadAgrees badI bad →
              capsOk injs a0 = true →
                ((∃ s M, S rows injs n a0 badI d s M) ↔
                  ∃ ts a, ts.length ≤ d ∧ replayEnv rows injs a0 ts = some a ∧ bad a)) ∧
    (∀ (rows : List Novel.FiringBound.Row) (injs : List Inj) (n : ℕ) (a0 : AMarking) (badI : (PlaceId → ℤ) → Prop)
        (isBad : AMarking → Bool) (d : ℕ) (s : ℕ → ℤ) (M : ℕ → PlaceId → ℤ),
        WellFormedRows n rows →
          InjsIn n injs →
            (BadAgrees badI fun a => isBad a = true) →
              S rows injs n a0 badI d s M →
                replays rows injs isBad a0 (decodeRust (rows.length + injs.length) s d) = true) ∧
      (∀ (D : ℕ) (enter na : Bool) (rows : List Novel.FiringBound.Row) (injs : List Inj) (a0 : AMarking)
          (isBad : AMarking → Bool) (ans : Witness.Answer),
          W D enter na rows injs a0 isBad ans = none ↔ D = 0 ∨ enter = false) ∧
        (∀ (D : ℕ) (rows : List Novel.FiringBound.Row) (injs : List Inj) (a0 : AMarking) (isBad : AMarking → Bool)
            (ans : Witness.Answer),
            D ≠ 0 →
              W D true true rows injs a0 isBad ans = some (Witness.Outcome.inconclusive Witness.Reason.nameAlignment)) ∧
          (∀ (D : ℕ) (enter na : Bool) (rows : List Novel.FiringBound.Row) (injs : List Inj) (a0 : AMarking)
              (isBad : AMarking → Bool) (ans : Witness.Answer) (r : List ℕ),
              W D enter na rows injs a0 isBad ans = some (Witness.Outcome.violated r) →
                ∃ s run,
                  ans = Witness.Answer.sat s ∧
                    decodeModel (rows.length + injs.length) s D = some run ∧
                      r = trim (replays rows injs isBad a0) run) ∧
            (∀ (D : ℕ) (rows : List Novel.FiringBound.Row) (injs : List Inj) (a0 : AMarking) (isBad : AMarking → Bool)
                (s : ℕ → Option ℤ),
                D ≠ 0 →
                  (decodeModel (rows.length + injs.length) s D = none →
                      W D true false rows injs a0 isBad (Witness.Answer.sat s) =
                        some (Witness.Outcome.inconclusive Witness.Reason.noReplay)) ∧
                    ∀ (run : List ℕ),
                      decodeModel (rows.length + injs.length) s D = some run →
                        (replays rows injs isBad a0 run = true →
                            ∃ r,
                              W D true false rows injs a0 isBad (Witness.Answer.sat s) =
                                some (Witness.Outcome.violated r)) ∧
                          (replays rows injs isBad a0 run = false →
                            W D true false rows injs a0 isBad (Witness.Answer.sat s) =
                              some (Witness.Outcome.inconclusive Witness.Reason.noReplay))) ∧
              (∀ (D : ℕ) (rows : List Novel.FiringBound.Row) (injs : List Inj) (a0 : AMarking)
                  (isBad : AMarking → Bool),
                  D ≠ 0 →
                    W D true false rows injs a0 isBad Witness.Answer.unsat = some Witness.Outcome.noRun ∧
                      W D true false rows injs a0 isBad Witness.Answer.unknown =
                          some (Witness.Outcome.inconclusive Witness.Reason.unknown) ∧
                        W D true false rows injs a0 isBad Witness.Answer.failure =
                            some (Witness.Outcome.inconclusive Witness.Reason.transport) ∧
                          W D true false rows injs a0 isBad Witness.Answer.budgetSpent =
                            some (Witness.Outcome.inconclusive Witness.Reason.budget)) ∧
                (∀ (r : List ℕ) (elapsed budget : ℕ) (fixpoint : ℕ → Witness.Verdict),
                    P (some (Witness.Outcome.violated r)) elapsed budget fixpoint = Witness.Verdict.violated r) ∧
                  (∀ (o : Witness.Outcome) (elapsed budget : ℕ) (fixpoint : ℕ → Witness.Verdict),
                      (∀ (r : List ℕ), o ≠ Witness.Outcome.violated r) →
                        P (some o) elapsed budget fixpoint = fixpoint (budget - elapsed)) ∧
                    ∀ (elapsed budget : ℕ) (fixpoint : ℕ → Witness.Verdict),
                      P none elapsed budget fixpoint = fixpoint budget
-/
#guard_msgs in #print VER_025

/-! ### The reference -/

/-- The reference phase does not run exactly when the depth is 0 or the entry gate is closed. -/
theorem ver025_gate (D : Nat) (enter na : Bool) (rows : List Novel.FiringBound.Row)
    (injs : List Inj) (a0 : AMarking) (isBad : AMarking → Bool) (ans : Witness.Answer) :
    witnessPhase D enter na rows injs a0 isBad ans = none ↔ (D = 0 ∨ enter = false) := by
  unfold witnessPhase
  by_cases h : D = 0 ∨ enter = false
  · rw [if_pos h]; exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]
    refine ⟨fun h' => ?_, fun h' => absurd h' h⟩
    split at h' <;> simp at h'

/-- The reference triple satisfies VER-025: the script is exact (`bmcEnv_complete`), a model's
decoded run replays (`bmcEnv_sat_replays`), a reported run is the trim of a `sat` model's
decoded run (`witnessPhase_violated_sound`), the outcomes are those of `witnessPhase`'s cases,
and the pipeline hands every outcome but a run to the fixpoint route at the total budget minus
the time the phase spent (`pipeline_some_eq`). -/
@[evidence holds VER_025]
theorem VER_025_reference : VER_025 ver025_script witnessPhase pipeline := by
  refine ⟨fun rows injs n a0 badI bad d hWF hIn hD hBad hcap0 =>
      bmcEnv_complete d hWF hIn hD hBad hcap0,
    fun rows injs n a0 badI isBad d s M hWF hIn hBad hm =>
      replays_iff.mpr (bmcEnv_sat_replays hWF hIn hBad hm),
    ver025_gate,
    fun D rows injs a0 isBad ans hD => by simp [witnessPhase, hD],
    fun D enter na rows injs a0 isBad ans r h => ?_,
    fun D rows injs a0 isBad s hD =>
      ⟨fun h => by simp [witnessPhase, hD, h],
        fun run hrun => ⟨fun h => by simp [witnessPhase, hD, hrun, h],
          fun h => by simp [witnessPhase, hD, hrun, h]⟩⟩,
    fun D rows injs a0 isBad hD => by simp [witnessPhase, hD],
    fun _ _ _ _ => rfl,
    fun _ _ _ _ h => pipeline_some_eq h,
    fun _ _ _ => rfl⟩
  obtain ⟨⟨s, run, hs, hd, -, hr, -⟩, -⟩ := witnessPhase_violated_sound h
  exact ⟨s, run, hs, hd, hr⟩

/-- **What a reported run is**, from the statement alone: on every triple satisfying VER-025, a
run the phase reports is the trim of the run decoded from a `sat` model, that decoded run
replays, and so the reported run is a sublist of it of at most `D` steps that replays to a
violating marking, ends at the first violating marking it reaches, and has no single step that
can be dropped. When `M0` violates, it is the empty run, whatever model the solver returned. -/
theorem VER_025_reported_run {S : ScriptRel} {W : PhaseFn} {P : PipelineFn}
    (h : VER_025 S W P) {D : Nat} {enter na : Bool} {rows : List Novel.FiringBound.Row}
    {injs : List Inj} {a0 : AMarking} {isBad : AMarking → Bool} {ans : Witness.Answer}
    {r : List Nat} (hW : W D enter na rows injs a0 isBad ans = some (.violated r)) :
    (∃ s run, ans = .sat s ∧ decodeModel (rows.length + injs.length) s D = some run ∧
      replays rows injs isBad a0 run = true ∧ r = trim (replays rows injs isBad a0) run ∧
      r.Sublist run) ∧
      r.length ≤ D ∧
      replays rows injs isBad a0 r = true ∧
      (∀ j, j < r.length → replays rows injs isBad a0 (r.take j) = false) ∧
      (∀ k, k < r.length → replays rows injs isBad a0 (r.eraseIdx k) = false) ∧
      (replays rows injs isBad a0 [] = true → r = []) := by
  obtain ⟨-, -, h3, h4, h5, h6, -⟩ := h
  have hrun : ¬ (D = 0 ∨ enter = false) := fun hc => by
    rw [(h3 D enter na rows injs a0 isBad ans).mpr hc] at hW; cases hW
  have hD : D ≠ 0 := fun h0 => hrun (Or.inl h0)
  have he : enter = true := by
    cases enter
    · exact absurd (Or.inr rfl) hrun
    · rfl
  subst he
  have hna : na = false := by
    cases na
    · rfl
    · rw [h4 D rows injs a0 isBad ans hD] at hW; cases hW
  subst hna
  obtain ⟨s, run, hs, hd, hr⟩ := h5 D true false rows injs a0 isBad ans r hW
  subst hs
  have hrep : replays rows injs isBad a0 run = true := by
    cases hrp : replays rows injs isBad a0 run
    · rw [((h6 D rows injs a0 isBad s hD).2 run hd).2 hrp] at hW; cases hW
    · rfl
  subst hr
  have hsub := trim_sublist (replays rows injs isBad a0) run
  have hlen : run.length ≤ D := decodeModel_length_le hd
  exact ⟨⟨s, run, rfl, hd, hrep, rfl, hsub⟩, le_trans hsub.length_le hlen,
    trim_sound _ hrep, trim_first _ hrep, trim_irredundant _ _, trim_initial _ hrep⟩

/-- **When `M0` violates, a reported run is the run of 0 steps**, from the statement alone. -/
theorem VER_025_initial_violation {S : ScriptRel} {W : PhaseFn} {P : PipelineFn}
    (h : VER_025 S W P) {D : Nat} {enter na : Bool} {rows : List Novel.FiringBound.Row}
    {injs : List Inj} {a0 : AMarking} {isBad : AMarking → Bool} {ans : Witness.Answer}
    {r : List Nat} (hW : W D enter na rows injs a0 isBad ans = some (.violated r))
    (h0 : replays rows injs isBad a0 [] = true) : r = [] :=
  (VER_025_reported_run h hW).2.2.2.2.2 h0

/-- **The pipeline answers `Proven` only through the fixpoint route**, from the statement alone:
a `Proven` around W is the fixpoint route's `Proven` at a budget of at most the total. -/
theorem VER_025_never_proven {S : ScriptRel} {W : PhaseFn} {P : PipelineFn}
    (h : VER_025 S W P) {D : Nat} {enter na : Bool} {rows : List Novel.FiringBound.Row}
    {injs : List Inj} {a0 : AMarking} {isBad : AMarking → Bool} {ans : Witness.Answer}
    {elapsed budget : Nat} {fixpoint : Nat → Witness.Verdict}
    (hP : P (W D enter na rows injs a0 isBad ans) elapsed budget fixpoint = .proven) :
    ∃ left, left ≤ budget ∧ fixpoint left = .proven := by
  obtain ⟨-, -, -, -, -, -, -, h8, h9, h10⟩ := h
  cases hw : W D enter na rows injs a0 isBad ans with
  | none => rw [hw, h10] at hP; exact ⟨budget, le_refl _, hP⟩
  | some o =>
    rw [hw] at hP
    cases o with
    | violated r => rw [h8] at hP; cases hP
    | noRun =>
      rw [h9 .noRun elapsed budget fixpoint (fun _ hr => by cases hr)] at hP
      exact ⟨budget - elapsed, Nat.sub_le _ _, hP⟩
    | inconclusive x =>
      rw [h9 (.inconclusive x) elapsed budget fixpoint (fun _ hr => by cases hr)] at hP
      exact ⟨budget - elapsed, Nat.sub_le _ _, hP⟩

/-- **What 'no run of at most `D` steps reaches a violation' means**, from the statement alone:
on every triple satisfying VER-025, the phase reports no run only on an `unsat` answer, and when
that answer is truthful about the script (P4), no run of at most `D` steps, firings and
injections, replays to a violating marking. It says nothing about longer runs. -/
theorem VER_025_noRun_exact {S : ScriptRel} {W : PhaseFn} {P : PipelineFn}
    (h : VER_025 S W P) {D : Nat} {enter na : Bool} {rows : List Novel.FiringBound.Row}
    {injs : List Inj} {n : Nat} {a0 : AMarking} {isBad : AMarking → Bool}
    {badI : (PlaceId → Int) → Prop} {ans : Witness.Answer}
    (hWF : WellFormedRows n rows) (hIn : InjsIn n injs) (hDist : InjsDistinct injs)
    (hBad : BadAgrees badI (fun a => isBad a = true)) (hcap0 : capsOk injs a0 = true)
    (hTruth : ans = .unsat → ¬ ∃ s M, S rows injs n a0 badI D s M)
    (hW : W D enter na rows injs a0 isBad ans = some .noRun) :
    ans = .unsat ∧
      ¬ ∃ ts a, ts.length ≤ D ∧ replayEnv rows injs a0 ts = some a ∧ isBad a = true := by
  obtain ⟨h1, -, h3, h4, -, h6, h7, -⟩ := h
  have hrun : ¬ (D = 0 ∨ enter = false) := fun hc => by
    rw [(h3 D enter na rows injs a0 isBad ans).mpr hc] at hW; cases hW
  have hD : D ≠ 0 := fun h0 => hrun (Or.inl h0)
  have he : enter = true := by
    cases enter
    · exact absurd (Or.inr rfl) hrun
    · rfl
  subst he
  have hu : ans = .unsat := by
    cases na
    · cases ans with
      | sat s =>
        cases hd : decodeModel (rows.length + injs.length) s D with
        | none => rw [(h6 D rows injs a0 isBad s hD).1 hd] at hW; cases hW
        | some run =>
          cases hr : replays rows injs isBad a0 run
          · rw [((h6 D rows injs a0 isBad s hD).2 run hd).2 hr] at hW; cases hW
          · obtain ⟨r, hr'⟩ := ((h6 D rows injs a0 isBad s hD).2 run hd).1 hr
            rw [hr'] at hW; cases hW
      | unsat => rfl
      | unknown => rw [(h7 D rows injs a0 isBad hD).2.1] at hW; cases hW
      | failure => rw [(h7 D rows injs a0 isBad hD).2.2.1] at hW; cases hW
      | budgetSpent => rw [(h7 D rows injs a0 isBad hD).2.2.2] at hW; cases hW
    · rw [h4 D rows injs a0 isBad ans hD] at hW; cases hW
  exact ⟨hu, fun hrun' => hTruth hu ((h1 rows injs n a0 badI _ D hWF hIn hDist hBad hcap0).mpr
    hrun')⟩

/-! ### Examples: the net `envBoundedPair` -/

/-- The transition `t` of `envBoundedPair`: a `one()` input on the environment place `e`
(index `0`) and an output to `p1` (index `1`). -/
def ver025_t : Transition :=
  { name := "t", inputs := [⟨0, .one, none⟩], inhibitors := [], reads := [], resets := [] }

/-- `envBoundedPair` as flat rows: `t` consumes one token of `e` and deposits one in `p1`. -/
def ver025_rows : List Novel.FiringBound.Row := [(ver025_t, [1])]

/-- The one injection of `envBoundedPair`: place `e` (index `0`) under `Bounded(2)`. With
`T = 1` and `J = 1`, selector `0` is `t`, `1` is `inject(e)` and `2` is idle. -/
def ver025_injs : List Inj := [(0, some 2)]

/-- The empty initial marking. -/
def ver025_a0 : AMarking := fun _ => 0

/-- `PlaceBound(p1, k)` is violated: `p1` holds more than `k` tokens. -/
def ver025_placeBound (k : Nat) : AMarking → Bool := fun a => decide (k < a 1)

/-- The selectors of a solver model: the listed values, then idle (`2`, which is `T + J`). -/
def ver025_sel (xs : List Int) : Nat → Int := fun i => xs.getD i 2

/-- A solver model that defines every selector: the listed values, then idle. -/
def ver025_model (xs : List Int) : Nat → Option Int := Witness.defined (ver025_sel xs)

/-- ✓ **AC1 and AC10**: on `envBoundedPair` with `PlaceBound(p1, 1)` at depth 8, a model padded
with a needless injection (`inject(e) t inject(e) inject(e) t`, then idle) is reported as the run
`inject(e) t inject(e) t`: four steps, two of them injections, that replay to `p1 = 2`; dropping
any single step leaves a run that does not replay to a violation (so the run needs both
injections); and the pipeline answers `Violated` with that run whatever the fixpoint route would
have answered (no fixpoint query). -/
@[evidence nonvacuous VER_025]
theorem VER_025_nonvacuous :
    decodeModel 2 (ver025_model [1, 0, 1, 1, 0]) 8 = some [1, 0, 1, 1, 0] ∧
      witnessPhase 8 true false ver025_rows ver025_injs ver025_a0 (ver025_placeBound 1)
        (.sat (ver025_model [1, 0, 1, 1, 0])) = some (.violated [1, 0, 1, 0]) ∧
      [1, 0, 1, 0].count 1 = 2 ∧
      replays ver025_rows ver025_injs (ver025_placeBound 1) ver025_a0 [1, 0, 1, 0] = true ∧
      (∀ k, k < 4 → replays ver025_rows ver025_injs (ver025_placeBound 1) ver025_a0
        ([1, 0, 1, 0].eraseIdx k) = false) ∧
      pipeline (witnessPhase 8 true false ver025_rows ver025_injs ver025_a0
        (ver025_placeBound 1) (.sat (ver025_model [1, 0, 1, 1, 0]))) 1 8 (fun _ => .unknown) =
        .violated [1, 0, 1, 0] :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **AC2**: on the same net with `PlaceBound(p1, 4)`, a depth-10 model alternating
`inject(e) t` five times is reported as that run of 10 steps (no step can be dropped), and at
depth 8 an `unsat` answer gives 'no run', after which the pipeline answers what the fixpoint
route answers at the budget the phase left. -/
theorem VER_025_ac2 :
    witnessPhase 10 true false ver025_rows ver025_injs ver025_a0 (ver025_placeBound 4)
        (.sat (ver025_model [1, 0, 1, 0, 1, 0, 1, 0, 1, 0])) =
      some (.violated [1, 0, 1, 0, 1, 0, 1, 0, 1, 0]) ∧
    witnessPhase 8 true false ver025_rows ver025_injs ver025_a0 (ver025_placeBound 4) .unsat =
      some .noRun ∧
    pipeline (witnessPhase 8 true false ver025_rows ver025_injs ver025_a0 (ver025_placeBound 4)
      .unsat) 1 8 (fun left => if left = 7 then .violated [] else .unknown) = .violated [] :=
  ⟨by decide, by decide, by decide⟩

/-- **AC8**: selector `T + 0 = 1` decodes as the injection, not as idle; the idle selector
`T + J = 2`, anything above it, and a negative selector end the run. A selector the model leaves
undefined is idle, and a model that defines no selector yields no run. -/
theorem VER_025_ac8 :
    decodeRust 2 (ver025_sel [1, 0, 2, 1]) 4 = [1, 0] ∧
    decodeRust 2 (ver025_sel [1, 3, 0]) 3 = [1] ∧
    decodeRust 2 (ver025_sel [0, -1, 0]) 3 = [0] ∧
    decodeModel 2 (fun i => if i = 1 then none else some 1) 3 = some [1] ∧
    decodeModel 2 (fun _ => none) 3 = none :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- **AC9**: an injection at a place that holds its bound does not replay; without a bound it
does; and an injection is checked against no post-cap: with `p1` above its cap of `0`, the
injection into `e` replays while the firing of `t` (whose successor is checked) does not. -/
theorem VER_025_ac9 :
    (replayEnv ver025_rows ver025_injs (fun p => if p = 0 then 2 else 0) [1]).isNone = true ∧
    (replayEnv ver025_rows [(0, none)] (fun p => if p = 0 then 2 else 0) [1]).isSome = true ∧
    (replayEnv ver025_rows [(0, some 2), (1, some 0)] (fun p => if p = 1 then 1 else 0)
      [1]).isSome = true ∧
    (replayEnv ver025_rows [(0, some 2), (1, some 0)] (fun p => if p = 1 then 1 else 1)
      [0]).isNone = true :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- The ring `t1: p0 → p1`, `t2: p1 → p0` as flat rows (`T = 2`, no injection, so `2` is idle). -/
def ver025_ring : List Novel.FiringBound.Row :=
  [({ name := "t1", inputs := [⟨0, .one, none⟩], inhibitors := [], reads := [], resets := [] },
      [1]),
   ({ name := "t2", inputs := [⟨1, .one, none⟩], inhibitors := [], reads := [], resets := [] },
      [0])]

/-- `M0 = {p0: 2}`. -/
def ver025_ringA0 : AMarking := fun p => if p = 0 then 2 else 0

/-- `PlaceBound(p0, 1)` is violated: `p0` holds more than one token. -/
def ver025_p0Above1 : AMarking → Bool := fun a => decide (1 < a 0)

/-- **AC11**: when `M0` violates, the phase reports the run of 0 steps, for an all-idle model
on `envBoundedPair` and for a model on the ring that leaves `M0` and comes back to a violating
marking (`t1, t2`, which replays and from which no single step can be dropped). A model whose run
passes a violating marking and goes on (`inject(e) t inject(e) t` under `PlaceBound(p1, 0)`) is
reported cut at that marking. A model that defines no selector yields no run, even when `M0`
violates. -/
theorem VER_025_ac11 :
    witnessPhase 8 true false ver025_rows ver025_injs (fun p => if p = 1 then 2 else 0)
      (ver025_placeBound 1) (.sat (ver025_model [])) = some (.violated []) ∧
    replays ver025_ring [] ver025_p0Above1 ver025_ringA0 [0, 1] = true ∧
    witnessPhase 8 true false ver025_ring [] ver025_ringA0 ver025_p0Above1
      (.sat (ver025_model [0, 1])) = some (.violated []) ∧
    witnessPhase 8 true false ver025_rows ver025_injs ver025_a0 (ver025_placeBound 0)
      (.sat (ver025_model [1, 0, 1, 0])) = some (.violated [1, 0]) ∧
    witnessPhase 8 true false ver025_rows ver025_injs (fun p => if p = 1 then 2 else 0)
      (ver025_placeBound 1) (.sat fun _ => none) = some (.inconclusive .noReplay) :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-! ### Violations -/

/-- The reference phase with the decode and the trim as parameters. -/
def ver025_phaseWith (dec : Nat → (Nat → Option Int) → Nat → Option (List Nat))
    (tr : (List Nat → Bool) → List Nat → List Nat) : PhaseFn :=
  fun D enter na rows injs a0 isBad ans =>
    if D = 0 ∨ enter = false then none
    else if na = true then some (.inconclusive .nameAlignment)
    else
      some <| match ans with
      | .sat s =>
        match dec (rows.length + injs.length) s D with
        | none => .inconclusive .noReplay
        | some run =>
          if replays rows injs isBad a0 run = true then .violated (tr (replays rows injs isBad a0) run)
          else .inconclusive .noReplay
      | .unsat => .noRun
      | .unknown => .inconclusive .unknown
      | .failure => .inconclusive .transport
      | .budgetSpent => .inconclusive .budget

/-- A phase that reports the solver's run without replaying it. -/
def ver025_noReplay : PhaseFn := fun D enter na rows injs a0 isBad ans =>
  match ans with
  | .sat s =>
    if D = 0 ∨ enter = false then none
    else if na = true then some (.inconclusive .nameAlignment)
    else some (.violated ((decodeModel (rows.length + injs.length) s D).getD []))
  | _ => witnessPhase D enter na rows injs a0 isBad ans

/-- ✗ A phase that does not replay violates VER-025 (line 6): a model selecting `t` first on
`envBoundedPair` decodes to the run `t`, which is not a run (`e` is empty), and the phase reports
it. -/
@[evidence forbids VER_025]
theorem VER_025_forbids_noReplay : ¬ VER_025 ver025_script ver025_noReplay pipeline := by
  intro h
  have := ((h.2.2.2.2.2.1 8 ver025_rows ver025_injs ver025_a0 (ver025_placeBound 1)
    (ver025_model [0]) (by decide)).2 [0] (by decide)).2 (by decide)
  revert this
  decide

/-- A phase that reads a model defining no selector as the empty run. -/
def ver025_emptyModelRun : PhaseFn :=
  ver025_phaseWith (fun T s D => some (decodeRust T (fun i => (s i).getD (T : Int)) D)) trim

/-- ✗ A phase that reads a run from a model with no selector violates VER-025 (line 6): when `M0`
violates, it reports the run of 0 steps from a model that defines nothing. -/
@[evidence forbids VER_025]
theorem VER_025_forbids_emptyModelRun : ¬ VER_025 ver025_script ver025_emptyModelRun pipeline := by
  intro h
  have := (h.2.2.2.2.2.1 8 ver025_rows ver025_injs (fun p => if p = 1 then 2 else 0)
    (ver025_placeBound 1) (fun _ => none) (by decide)).1 (by decide)
  revert this
  decide

/-- A pipeline that reads the phase's `unsat` ('no run') as a proof. -/
def ver025_unsatProven : PipelineFn := fun phase elapsed budget fixpoint =>
  match phase with
  | some (.violated r) => .violated r
  | some .noRun => .proven
  | some _ => fixpoint (budget - elapsed)
  | none => fixpoint budget

/-- ✗ A pipeline that answers `Proven` on the phase's `unsat` violates VER-025 (line 9): with a
fixpoint route that answers `Unknown`, it answers `Proven`. -/
@[evidence forbids VER_025]
theorem VER_025_forbids_unsatProven :
    ¬ VER_025 ver025_script witnessPhase ver025_unsatProven := by
  intro h
  have := h.2.2.2.2.2.2.2.2.1 .noRun 0 8 (fun _ => .unknown) (fun _ hr => by cases hr)
  revert this
  decide

/-- A pipeline that starves the fixpoint route after a phase that ran without a run: it hands
over no budget at all. -/
def ver025_starve : PipelineFn := fun phase _ budget fixpoint =>
  match phase with
  | some (.violated r) => .violated r
  | some _ => fixpoint 0
  | none => fixpoint budget

/-- ✗ A pipeline that starves the fixpoint route violates VER-025 (line 9): 'no run' after 1 ms
of an 8 ms budget turns a fixpoint `Proven` at the 7 ms left into `Unknown`. A statement that
only bounds the budget left by the total would accept it. -/
@[evidence forbids VER_025]
theorem VER_025_forbids_starve : ¬ VER_025 ver025_script witnessPhase ver025_starve := by
  intro h
  have := h.2.2.2.2.2.2.2.2.1 .noRun 1 8 (fun l => if l = 7 then .proven else .unknown)
    (fun _ hr => by cases hr)
  revert this
  decide

/-- A pipeline that never charges the phase's time: the fixpoint route always gets the whole
budget. -/
def ver025_noDeduct : PipelineFn := fun phase _ budget fixpoint =>
  match phase with
  | some (.violated r) => .violated r
  | _ => fixpoint budget

/-- ✗ A pipeline that ignores the time the phase spent violates VER-025 (line 9): the phase's
time counts against the total budget. -/
@[evidence forbids VER_025]
theorem VER_025_forbids_noDeduct : ¬ VER_025 ver025_script witnessPhase ver025_noDeduct := by
  intro h
  have := h.2.2.2.2.2.2.2.2.1 .noRun 1 8 (fun l => if l = 7 then .proven else .unknown)
    (fun _ hr => by cases hr)
  revert this
  decide

/-- A trim that drops the last step of the reported run without replaying the result. -/
def ver025_dropLast : PhaseFn := fun D enter na rows injs a0 isBad ans =>
  (witnessPhase D enter na rows injs a0 isBad ans).map fun
    | .violated r => .violated r.dropLast
    | o => o

/-- ✗ A trim that drops a needed step violates VER-025 (line 5): the run
`inject(e) inject(e) t t` is reported without its last `t`, which is not the trimmed run. -/
@[evidence forbids VER_025]
theorem VER_025_forbids_dropLast : ¬ VER_025 ver025_script ver025_dropLast pipeline := by
  intro h
  obtain ⟨s, run, hs, hd, hr⟩ := h.2.2.2.2.1 8 true false ver025_rows ver025_injs ver025_a0
    (ver025_placeBound 1) (.sat (ver025_model [1, 1, 0, 0])) [1, 1, 0] (by decide)
  cases hs
  rw [show decodeModel (ver025_rows.length + ver025_injs.length) (ver025_model [1, 1, 0, 0]) 8 =
    some [1, 1, 0, 0] by decide] at hd
  cases hd
  revert hr
  decide

/-- A trim that tries the first step before the reference passes. -/
def ver025_trimFirst (ok : List Nat → Bool) (run : List Nat) : List Nat :=
  trim ok (if ok (run.eraseIdx 0) = true then run.eraseIdx 0 else run)

/-- Two injections without a bound into places `0` and `1`, no transition (`T = 0`, `J = 2`, so
`2` is idle). -/
def ver025_twoInjs : List Inj := [(0, none), (1, none)]

/-- Violated once places `0` and `1` hold a token between them. -/
def ver025_badSum1 : AMarking → Bool := fun a => decide (1 ≤ a 0 + a 1)

/-- ✗ A trim in another order violates VER-025 (line 5), although its run replays, ends at its
first violating marking and is irredundant: from the model `inject(0) inject(1)` it reports
`inject(1)`, where the reference cuts the run to `inject(0)`. The quoted trim fixes the run for a
model, so the ports report the same run. -/
@[evidence forbids VER_025]
theorem VER_025_forbids_trimFirst :
    ¬ VER_025 ver025_script (ver025_phaseWith decodeModel ver025_trimFirst) pipeline := by
  intro h
  obtain ⟨s, run, hs, hd, hr⟩ := h.2.2.2.2.1 8 true false [] ver025_twoInjs ver025_a0
    ver025_badSum1 (.sat (ver025_model [0, 1])) [1] (by decide)
  cases hs
  rw [show decodeModel (([] : List Novel.FiringBound.Row).length + ver025_twoInjs.length)
    (ver025_model [0, 1]) 8 = some [0, 1] by decide] at hd
  cases hd
  revert hr
  decide

/-- The trim without the cut to the violating prefix: passes that drop a step only when the rest
replays as a whole, until one drops nothing. -/
def ver025_noCutPass (ok : List Nat → Bool) : Nat → List Nat → List Nat
  | 0, run => run
  | k + 1, run => ver025_noCutPass ok k (if ok (run.eraseIdx k) = true then run.eraseIdx k else run)

/-- The passes of `ver025_noCutPass` until one drops nothing. -/
def ver025_noCutLoop (ok : List Nat → Bool) : Nat → List Nat → List Nat
  | 0, run => run
  | fuel + 1, run =>
    if (ver025_noCutPass ok run.length run).length = run.length then run
    else ver025_noCutLoop ok fuel (ver025_noCutPass ok run.length run)

/-- The trim without the prefix cut. -/
def ver025_noCut (ok : List Nat → Bool) (run : List Nat) : List Nat :=
  ver025_noCutLoop ok (run.length + 1) run

/-- ✗ A trim without the cut to the violating prefix violates VER-025 (line 5): on the ring with
`M0` violating, the model `t1, t2` comes back to a violating marking, no single step of it can be
dropped, and it is reported as a run of 2 steps instead of the run of 0 steps. -/
@[evidence forbids VER_025]
theorem VER_025_forbids_noCut :
    ¬ VER_025 ver025_script (ver025_phaseWith decodeModel ver025_noCut) pipeline := by
  intro h
  obtain ⟨s, run, hs, hd, hr⟩ := h.2.2.2.2.1 8 true false ver025_ring [] ver025_ringA0
    ver025_p0Above1 (.sat (ver025_model [0, 1])) [0, 1] (by decide)
  cases hs
  rw [show decodeModel (ver025_ring.length + ([] : List Inj).length) (ver025_model [0, 1]) 8 =
    some [0, 1] by decide] at hd
  cases hd
  revert hr
  decide

/-- A phase whose replay ignores the injection bounds (it replays every injection as
`AlwaysAvailable`). -/
def ver025_noBound : PhaseFn := fun D enter na rows injs a0 isBad ans =>
  witnessPhase D enter na rows (injs.map fun j => (j.1, none)) a0 isBad ans

/-- `PlaceBound(e, k)` is violated: `e` holds more than `k` tokens. -/
def ver025_envAbove (k : Nat) : AMarking → Bool := fun a => decide (k < a 0)

/-- ✗ An injection step that ignores its bound violates VER-025 (line 6): three injections
into `e` under `Bounded(2)` are reported as a run to `e = 3`, which the exact step relation
refuses at the third injection. -/
@[evidence forbids VER_025]
theorem VER_025_forbids_noBound : ¬ VER_025 ver025_script ver025_noBound pipeline := by
  intro h
  have := ((h.2.2.2.2.2.1 8 ver025_rows ver025_injs ver025_a0 (ver025_envAbove 2)
    (ver025_model [1, 1, 1]) (by decide)).2 [1, 1, 1] (by decide)).2 (by decide)
  revert this
  decide

/-- A phase without the depth-0 switch: it runs whenever the entry gate is open, at depth 0
included. -/
def ver025_depth0Runs : PhaseFn := fun D enter na rows injs a0 isBad ans =>
  if enter = false then none
  else ver025_phaseWith decodeModel trim (D + 1) true na rows injs a0 isBad ans

/-- ✗ A phase that still runs at depth 0 violates VER-025 (line 3): at depth 0 with the gate
open it reports 'no run' on `unsat` instead of not running. -/
@[evidence forbids VER_025]
theorem VER_025_forbids_depth0Runs : ¬ VER_025 ver025_script ver025_depth0Runs pipeline := by
  intro h
  have := (h.2.2.1 0 true false ver025_rows ver025_injs ver025_a0 (ver025_placeBound 1)
    .unsat).mpr (Or.inl rfl)
  revert this
  decide

/-- A script that every assignment satisfies: a solver that answers `sat` on every query. -/
def ver025_alwaysSat : ScriptRel := fun _ _ _ _ _ _ _ _ => True

/-- ✗ A script that is always satisfiable violates VER-025 (line 1): on the empty net with a
violation no marking satisfies, it has a model although no run reaches a violation. -/
@[evidence forbids VER_025]
theorem VER_025_forbids_alwaysSat : ¬ VER_025 ver025_alwaysSat witnessPhase pipeline := by
  intro h
  have h1 := (h.1 [] [] 0 ver025_a0 (fun _ => False) (fun _ => False) 0
    (by simp [WellFormedRows]) (injsIn_nil 0) injsDistinct_nil (fun _ => Iff.rfl) rfl).mp
    ⟨fun _ => 0, fun _ _ => 0, trivial⟩
  obtain ⟨_, _, -, -, hb⟩ := h1
  exact hb

/-- ✓ VER-025 is consistent: the reference script, phase and pipeline satisfy it. Its model
(a script, a phase and a pipeline) shares no component with the firing relations of the CORE,
IO, EXEC and TIME blocks, so it has its own consistency theorem rather than a conjunct of
theirs. -/
@[evidence consistent VER_025]
theorem VER_025_consistent : ∃ (S : ScriptRel) (W : PhaseFn) (P : PipelineFn), VER_025 S W P :=
  ⟨_, _, _, VER_025_reference⟩

/-! ## Pure functions: the report, the labels, the budget and the option

These are kind-F lines of the quoted sentences: the exact text the spec states, as functions,
pinned with `#guard`. They are not part of the statement. -/

/-- The report header of the phase. -/
def ver025_header : String := "  Bounded witness phase (VER-025):"

/-- The inconclusive reason text: the transport's failure message and the NU-055 reason are
given; the others are fixed. -/
def ver025_reasonText (D budgetMs : Nat) (transport nameAlignment : String) :
    Witness.Reason → String
  | .transport => transport
  | .budget => s!"time budget of {budgetMs} ms exhausted"
  | .unknown => s!"the bounded run at depth {D} answered unknown"
  | .noReplay => "the bounded run did not replay under the exact semantics"
  | .nameAlignment => nameAlignment

/-- The status line of an outcome at depth `D`. -/
def ver025_status (D : Nat) (reason : Witness.Reason → String) : Witness.Outcome → String
  | .violated r =>
    s!"    Status: a run of {r.length} steps reaches a violation (replayed; depth {D})"
  | .noRun => s!"    Status: no run of at most {D} steps reaches a violation (not a proof)"
  | .inconclusive x => s!"    Status: inconclusive ({reason x})"

/-- The report lines of the phase: none when it does not run, the header and exactly one status
line when it does. -/
def ver025_report (D : Nat) (reason : Witness.Reason → String) :
    Option Witness.Outcome → List String
  | none => []
  | some o => [ver025_header, ver025_status D reason o]

/-- The label of an injection step. -/
def ver025_injectLabel (place : String) : String := s!"inject({place})"

/-- The label of step `t` of a reported run: the transition's name for `t < T`, the injected
place's label for `T + j`. -/
def ver025_stepLabel (T : Nat) (transition injected : Nat → String) (t : Nat) : String :=
  if t < T then transition t else ver025_injectLabel (injected (t - T))

/-- The phase budget in milliseconds: `max(1, floor(timeout_ms / 8))`. -/
def ver025_budgetMs (timeoutMs : Nat) : Nat := max 1 (timeoutMs / 8)

/-- The default witness depth. -/
def ver025_depthDefault : Nat := 8

/-- The argument error of a negative witness depth. -/
def ver025_depthError (n : Int) : String := s!"witnessDepth must be non-negative, got {n}"

/-- The phase name of the dump ([VER-013]). -/
def ver025_dumpPhase : String := "witness"

/-- The step name in the total-budget reason of [VER-013]. -/
def ver025_budgetStep : String := "witness phase"

/-- The reasons the examples print, with placeholder transport and NU-055 texts. -/
def ver025_reasons (D : Nat) : Witness.Reason → String :=
  ver025_reasonText D 1000 "transport failed" "decided only by the name-partition graph"

-- AC1: the run of 4 steps at depth 8, and its labels.
#guard ver025_report 8 (ver025_reasons 8) (some (.violated [1, 0, 1, 0])) ==
  ["  Bounded witness phase (VER-025):",
   "    Status: a run of 4 steps reaches a violation (replayed; depth 8)"]
#guard [1, 0, 1, 0].map (ver025_stepLabel 1 (fun _ => "t") (fun _ => "e")) ==
  ["inject(e)", "t", "inject(e)", "t"]
-- AC2: no run at depth 8; a run of 10 steps at depth 10.
#guard ver025_status 8 (ver025_reasons 8) .noRun ==
  "    Status: no run of at most 8 steps reaches a violation (not a proof)"
#guard ver025_status 10 (ver025_reasons 10) (.violated [1, 0, 1, 0, 1, 0, 1, 0, 1, 0]) ==
  "    Status: a run of 10 steps reaches a violation (replayed; depth 10)"
-- 'a run of 1 steps' is not special-cased; AC11: a run of 0 steps.
#guard ver025_status 8 (ver025_reasons 8) (.violated [0]) ==
  "    Status: a run of 1 steps reaches a violation (replayed; depth 8)"
#guard ver025_status 8 (ver025_reasons 8) (.violated []) ==
  "    Status: a run of 0 steps reaches a violation (replayed; depth 8)"
-- AC7: the inconclusive reasons.
#guard ver025_status 8 (ver025_reasons 8) (.inconclusive .unknown) ==
  "    Status: inconclusive (the bounded run at depth 8 answered unknown)"
#guard ver025_status 8 (ver025_reasons 8) (.inconclusive .budget) ==
  "    Status: inconclusive (time budget of 1000 ms exhausted)"
#guard ver025_status 8 (ver025_reasons 8) (.inconclusive .noReplay) ==
  "    Status: inconclusive (the bounded run did not replay under the exact semantics)"
#guard ver025_status 8 (ver025_reasons 8) (.inconclusive .transport) ==
  "    Status: inconclusive (transport failed)"
-- AC3 and the fifth quoted sentence: no report line when the phase does not run.
#guard ver025_report 0 (ver025_reasons 0) none == []
-- The budget: an eighth of the timeout, at least 1 ms.
#guard ver025_budgetMs 8000 == 1000
#guard ver025_budgetMs 7 == 1
#guard ver025_budgetMs 0 == 1
-- AC15: the default and the error.
#guard ver025_depthDefault == 8
#guard ver025_depthError (-1) == "witnessDepth must be non-negative, got -1"
-- The dump and budget-step names.
#guard ver025_dumpPhase == "witness"
#guard ver025_budgetStep == "witness phase"

end Libpetri.Spec
