import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Events
import Libpetri.Spec.Req.CORE_037
import Libpetri.Spec.Req.EVT_013
import Libpetri.Spec.Req.VER_006
import Libpetri.Spec.Text.CORE_037

set_option linter.missingDocs true

/-!
# CORE-037, the behaviour block: dead-arc events and report lines (`spec/01-core-model.md`)

The second part of CORE-037, beside the function block `CORE_037` (kind F, which fixes what a
dead arc is, the order of the report and the warning text). This file holds two blocks of kind B.

* `CORE_037_events`, a predicate over a pair of executors with events `(E, E0)`
  (`Reference/Events.lean`): `E` is the executor that reports dead arcs and `E0` the same
  executor without the report. Line 1: the events of the boot of a run that carry the warning
  text of an arc of the net are, in report order, one WARN per entry of the dead-arc report
  for the net, its environment places and the initial marking, each named after the transition
  that declares the arc. Line 2: no such event of the boot follows ExecutionStarted. Line 3: no
  step emits such an event. Lines 4 and 5: the other boot events are those of `E0`, and the
  steps of `E` are those of `E0` on the history with the dead-arc events left out.
* `CORE_037_verifier`, a predicate over a pair of environment-aware verifiers `(D, D0)`
  (`EnvDecider`, [VER-006]): `D` reports dead arcs and `D0` is the same verifier without the
  report. Line 1: the report lines of `D` that are `WARNING: ` followed by the warning text of an
  arc of the net are, in report order, one line per entry of the dead-arc report for the net as
  the caller passed it, the verification's initial marking and its environment places. Line 2:
  the notes of `D` with those lines left out are those of `D0`, and every other field of the
  result of `D` is that of `D0`.

The statements read CORE-037's reference report `refDeadArcs` and text `refDeadArcMsg` directly:
the F block fixes both (`CORE_037_unique`, `core037b_msg_unique`).

The witnesses wrap an executor or a verifier that knows nothing of dead arcs:
`core037bExec E0` puts the WARNs in front of `E0`'s boot and runs `E0`'s steps on the history
without them, and `core037bVerify D0` puts the lines in front of `D0`'s notes. The reference
pairs are `(core037bExec (refEvExec P), refEvExec P)` for both emission variants,
`(core037bExec (core037bUnknownExec P), core037bUnknownExec P)` (the reference with the
unknown-place WARNs of [CORE-072] AC4), and `(core037bVerify refEnvVerify, refEnvVerify)`.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## The terms the blocks read -/

section Terms

variable {T : Type}

/-- The dead-arc report of a run: [CORE-037]'s report for the net of `C`, its environment places
and the token counts of the initial marking `M0`. -/
def core037bBootReport (C : Cfg String T) (M0 : QMarking String T) : List (DeadArc String) :=
  refDeadArcs C.X.net (fun p => decide (p ∈ C.envs)) (fun p => (M0 p).length)

/-- The dead-arc WARN of one report entry: a log message named after the transition that
declares the arc, at level WARN, with the arc's warning text. -/
def core037bEvent (a : DeadArc String) : NetEvent String T :=
  .logMessage (some a.transition) .warn (refDeadArcMsg a)

/-- **Dead-arc event** (proposed term): a log message, at any level and under any name, whose
text is the warning text of a read, inhibitor or reset arc of the net. -/
def core037bDeadEv (X : Reference.Net String) : NetEvent String T → Bool
  | .logMessage _ _ msg => (deadArcCandidates X).any fun a => msg == refDeadArcMsg a
  | _ => false

/-- The dead-arc WARNs of a run, in report order. -/
def core037bWarnings (C : Cfg String T) (M0 : QMarking String T) : List (NetEvent String T) :=
  (core037bBootReport C M0).map core037bEvent

end Terms

/-- The prefix of a dead-arc report line. -/
def core037bPrefix : String := "WARNING: "

/-- The report lines of a verification: one line per entry of [CORE-037]'s report for the net as
the caller passed it, the environment places registered for the verification and the counts of
its initial marking, the warning text prefixed with `WARNING: `. -/
def core037bLines (X : Reference.Net String) (envs : List String) (m0 : NMarking String) :
    List String :=
  (refDeadArcs X (fun p => decide (p ∈ envs)) m0.count).map fun a =>
    core037bPrefix ++ refDeadArcMsg a

/-- **Dead-arc line** (proposed term): a report line that is `WARNING: ` followed by the warning
text of a read, inhibitor or reset arc of the net. -/
def core037bDeadLine (X : Reference.Net String) (l : String) : Bool :=
  (deadArcCandidates X).any fun a => l == core037bPrefix ++ refDeadArcMsg a

/-- A verifier result with the dead-arc lines of the net left out of its notes, every other field
as it is. -/
def core037bStrip (X : Reference.Net String) (r : Verifier.Result String) : Verifier.Result String :=
  { r with notes := r.notes.filter fun l => !core037bDeadLine X l }

/-! ## CORE-037: the events of the executors -/

requirement CORE_037_events
  id "CORE-037"
  title "Dead Arc Warning: executor events"
  kind B
  scope "every executor backend with its event store enabled (SHOULD; the shall sentences bind an executor that reports dead arcs); for Java, on a net and initial marking where no two places share a name with different token types ([MOD-024])"
  source verbatim "spec/01-core-model.md"
  covers CORE_037.s4, CORE_037.s5, CORE_037.s6
  reading "For every pair of executors with events E (the executor that reports dead arcs) and E0 (the same executor that does not report dead arcs), every token type T and every configuration C, with places named by strings:"
          "for every initial marking M0, the boot events of E for C and M0 that are dead-arc events (a log message whose text is refDeadArcMsg of a read, inhibitor or reset arc of C's net) are exactly, in order, one WARN log message per entry a of refDeadArcs for C's net, C's environment places and the token counts of M0, named a.transition, with the text refDeadArcMsg a;"
          "for every initial marking M0, no boot event of E for C and M0 that follows an ExecutionStarted is a dead-arc event;"
          "for every history H, every step of E appends no dead-arc event (in the model every log message a step appends is an engine diagnostic);"
          "for every initial marking M0, the boot events of E that are not dead-arc events are the boot events of E0;"
          "for every history H, E steps from s by label l to s' appending evs exactly when E0 does so given the history H with its dead-arc events left out."
  assumes "The model is a pair of executors with events (E, E0 : EvExec String T, Reference/Events.lean): E reports dead arcs, E0 is the same executor without the report. Places are their names (ruling D10), so the warning text, which names the place, is CORE-037's refDeadArcMsg. The statement reads CORE-037's reference report refDeadArcs and text refDeadArcMsg: the F block CORE_037 fixes both (CORE_037_unique for the report, core037b_msg_unique for the text), so a block over an abstract pair (Rep, Msg) would say nothing more. The environment places are C.envs, the places registered for the run, and the initial marking's counts are the lengths of its queues, as EVT-013's boot line reads them (Rust passes the seeded places, executor_core/executor.rs warn_dead_arcs; Java ExecutorSupport.deadArcs; TypeScript the findDeadArcs call in the constructors of bitmap-net-executor.ts and precompiled-net-executor.ts; Rust's PrecompiledNetExecutor::new registers no environment place and passes the empty set). Java finds seeded and environment places with Place equality, on name and token type (ExecutorSupport.deadArcs), where the model, Rust and TypeScript compare names (ruling D10): a token seeded on a same-named place of another token type silences the WARN in Rust and TypeScript and not in Java. That is the Place equality divergence of MOD-024, which this block does not settle."
          "A run has one boot (EvExec.boot): the model constructs the executor and starts its run at once, so it cannot tell construction from the start of the run, and the quoted sentences place the dead-arc events before ExecutionStarted. All three runtimes emit the warnings when the executor is constructed, before ExecutionStarted (Java warnDeadArcs, called from BitmapNetExecutor.Builder.build and the PrecompiledNetExecutor constructor; TypeScript the findDeadArcs call in the constructors of bitmap-net-executor.ts and precompiled-net-executor.ts; Rust: the bitmap executor's builder, the precompiled executor's builder and PrecompiledNetExecutor::new each call warn_dead_arcs before they return the executor). Line 2 kills an executor that warns after ExecutionStarted, the slip of moving the warning from the constructor into the run (CORE_037_events_forbids_late). Lines 1 and 2 fix the dead-arc events among themselves and against ExecutionStarted, not their place among the other boot events before it: Java and TypeScript emit the unknown-initial-place WARN of CORE-072 AC4 before them, Rust after ExecutionStarted (clash events SC-3), and no block fixes that order."
          "Dead-arc events are recognised by their text alone, at any level and under any name, so line 1 also kills a dead-arc WARN at another level (CORE_037_events_forbids_info) or under no transition name (CORE_037_events_forbids_unnamed), a report with one WARN per place instead of one per arc (CORE_037_events_forbids_perPlace), WARNs in kind order across transitions (CORE_037_events_forbids_kindMajor), no warning at all (CORE_037_events_forbids_silent), and the reference with engine diagnostics of EVT-013, whose dead-arc WARN carries a placeholder text (CORE_037_events_forbids_placeholder). The unknown-place WARN of CORE-072 AC4 and the multiplicity WARN of IO-016 carry other texts and are not dead-arc events. A captured action log statement is EVT-013's action log, not a boot event or a step of E, so an action that logs a warning text breaks no line: the second quoted sentence speaks of engine diagnostics, every boot event and every event a step of the model appends is one, and no action runs before ExecutionStarted. Line 5 leaves every dead-arc event out of the history E0 sees, an action's log statement with such a text included where the history holds one; no runtime step reads its event history, so this says only that the steps of E do not read those events."
          "Lines 2 and 3 (the second quoted sentence) are 'when the executor is constructed' and 'One message per dead arc': an executor that warns after ExecutionStarted breaks line 2 (CORE_037_events_forbids_late), and one that warns again in its steps breaks line 3 (CORE_037_events_forbids_rewarn). Lines 4 and 5 are the third quoted sentence and the bullet's 'never changes execution': the other boot events are E0's, and E's steps are E0's on the history without the dead-arc events, so no step reads them. An executor that drops ExecutionStarted when it warns breaks line 4 (CORE_037_events_forbids_noStart), and one that takes no step once a dead-arc WARN is in its history breaks line 5 (CORE_037_events_forbids_stopOnWarn). In the model the steps of E are the executor (EvExec.erase); on the reference pair they are the steps of refEvExec, word for word (core037b_ref_step)."
          "Lines 4 and 5 compare E with E0, and the block alone does not say which executor E0 is: taken alone they hold of any E once E0 is chosen as E with its dead-arc events left out. The forbids evidence of lines 4 and 5 fixes E0 = refEvExec polRust, and the reference pairs take E0 = refEvExec P and E0 = core037bUnknownExec P. The consistency theorem spec_consistent_all (ConsistencyAll) joins this block with the execution and event blocks: there E0 is the shared executor with events, of which the event blocks are stated, and E is a wrapper of it (the witness is core037bExec of the shared executor), so AC4's 'never changes execution' holds of an E0 that meets those blocks. The event blocks are stated of E0, not of E; the executor with the WARNs meets EVT-013 whenever E0 does (core037b_evt013), and carrying the other event blocks over to E is an open item."
          "The bullet's logger `libpetri.runtime` (omitted where the log-message event carries no logger field) and the event's timestamp are not modelled: NetEvent.logMessage carries the transition name, the level and the message only. 'Like AC4 it is emitted only where events are recorded' is the shared assumption of the executor event blocks that the event store is enabled (EVT-020); all three runtimes emit nothing under a disabled store (Rust E::ENABLED, Java eventStoreEnabled, TypeScript the noop store)."
          "AC1 (one WARN log-message event naming the transition and the place for a reset arc on an untouched, non-environment, initially empty place) and AC2 (the same for a read and an inhibitor arc, with their effects) are line 1, with CORE-037's text lines: CORE_037_events_nonvacuous shows the three WARNs of the test derivation's net and their bytes. AC3 (no warning for a seeded place, an environment place, a consumed place or a place an output spec names) is line 1 through refDeadArcs, whose clauses the F block checks; CORE_037_events_nonvacuous shows that seeding the reset arc's place drops its WARN and that a consumed place gets none. AC4's executor half (the warning never rejects a net and never changes execution): never changing execution is lines 4 and 5. That constructing an executor never fails on a dead arc is an offer clause: the model's boot is a total function, so no line can say it, and it belongs in a coverage theorem (an open item); CORE-040's build line covers building the net, not constructing the executor. The verifier halves of AC1 and AC4 are the block CORE_037_verifier."
          "The test derivation's executor half (construct each executor with an empty initial marking: one WARN naming kill and x; seed x: none; the same with a read and an inhibitor arc, and with x produced by another transition's XOR branch) is CORE_037_events_nonvacuous on the reference pair for a net with a read, an inhibitor and a reset arc; the XOR branch is the F block's CORE_037_nonvacuous. Python runs the Rust executor and inherits its events."
  signoff "2026-11-13 c16c90630c1f7afc ai"
  statement : ∀ {T : Type}, EvExec String T → EvExec String T → Prop :=
    fun E E0 => ∀ C,
      (∀ M0, (E.boot C M0).filter (core037bDeadEv C.X.net) = core037bWarnings C M0) ∧
      (∀ M0 (pre post : List (NetEvent String _)),
        E.boot C M0 = pre ++ NetEvent.executionStarted :: post →
        post.filter (core037bDeadEv C.X.net) = []) ∧
      (∀ H s l evs s', E.step C H s l evs s' → ∀ e ∈ evs, core037bDeadEv C.X.net e = false) ∧
      (∀ M0, (E.boot C M0).filter (fun e => !core037bDeadEv C.X.net e) = E0.boot C M0) ∧
      (∀ H s l evs s', E.step C H s l evs s' ↔
        E0.step C (H.filter fun e => !core037bDeadEv C.X.net e) s l evs s')

/-! ## CORE-037: the report lines of the verifier -/

requirement CORE_037_verifier
  id "CORE-037"
  title "Dead Arc Warning: verifier report lines"
  kind B
  scope "the SMT verifier, all implementations (SHOULD; the shall sentences bind a verifier that reports dead arcs)"
  source verbatim "spec/01-core-model.md"
  covers CORE_037.s7, CORE_037.s8
  reading "For every pair of environment-aware verifiers D (the verifier that reports dead arcs) and D0 (the same verifier that does not report dead arcs), on nets whose places are their names, and for every environment mode, environment places envs, options o, net X, property φ and initial marking m0:"
          "the notes of D's result that are dead-arc lines (WARNING: followed by refDeadArcMsg of a read, inhibitor or reset arc of X's net) are exactly, in order, one line per entry a of refDeadArcs for X's net as the caller passed it, envs and the counts of m0, the line being WARNING: followed by refDeadArcMsg a;"
          "D's result with the dead-arc lines left out of its notes (core037bStrip) is D0's result: the same verdict, route, trace, counterexampleConfirmed, counterexampleTiming, invariants and other notes."
  assumes "The model is a pair of environment-aware verifiers (D, D0 : EnvDecider String, the verifier entry point of VER-006: the environment mode, the registered environment places, the options, the user's net, the property and the initial marking to a Result). The report is the result's notes (Result.notes, one note per non-blank line of the report). All three verifiers write a blank line after the dead-arc lines when there is one (Java SmtVerifier.pipeline, TypeScript runPipeline in smt-verifier.ts, smt_verifier.rs finish), which is why the second quoted sentence leaves that blank line out with them; the model has no blank notes. The order of the dead-arc lines among the other notes and the line breaks are report wording (kind Q): Rust puts them after the total budget, Arrivals and reaping lines (smt_verifier.rs finish), Java and TypeScript after the reaping and in-flight lines (SmtVerifier.pipeline, runPipeline in smt-verifier.ts). Line 1 fixes the dead-arc lines among themselves only."
          "The model's Result holds the verdict, the route, the counterexample's transition labels, counterexampleConfirmed, counterexampleTiming, the P-invariants and the notes (Verifier/Result.lean). The runtime fields it leaves out (Rust counterexample_trace, the sequence of markings, discovered_invariants and statistics of VerificationResult, and their Java and TypeScript counterparts) are bound by the second quoted sentence and checked by no line. The elapsed time (Rust elapsed_ms) is wall-clock time that differs between any two runs, so the sentence excepts it and the model has no such field."
          "The report is judged on the net as the caller passed it, before every rewrite of the verified-net function (the Arrivals closure of VER-006, the inert places of VER-001, the in-flight split of VER-004, the terminal rewrite of EXEC-042), whose arcs are the verifier's own: Rust computes the lines first in verify (dead_arc_lines before with_arrivals, smt_verifier.rs), Java and TypeScript on callerNet. 'Its environment places' are the places registered for the verification, envs; under Arrivals all three count them as environment places although the closure clears them (Rust before the closure, Java and TypeScript by adding the arrival places back). 'The verification's initial marking' is m0, the marking passed in, read as counts (NMarking.count; a place starts empty when its count is 0). The statement reads CORE-037's reference report and text, which the F block fixes (CORE_037_unique, core037b_msg_unique)."
          "Line 1 recognises a dead-arc line by its text alone, so it kills a verifier that writes no line (CORE_037_verifier_forbids_silent), one that leaves out the WARNING: prefix (CORE_037_verifier_forbids_noPrefix) and one that warns about every read, inhibitor and reset arc, dead or not (CORE_037_verifier_forbids_everyArc). Line 2 is 'No result field changes and no verdict depends on it.' and AC4's verifier half: a verifier whose verdict changes when it reports a dead arc breaks it (CORE_037_verifier_forbids_verdict)."
          "Line 2 compares D with D0, and the block alone does not say which verifier D0 is: taken alone it holds of any D once D0 is chosen as D with its dead-arc lines left out. The forbids evidence of line 2 fixes D0 = refEnvVerify, and so does the reference pair, whose D0 notes hold no dead-arc line (core037b_refEnvVerify_clean). The consistency theorem spec_consistent_all (ConsistencyAll) joins this block with the verifier blocks: there D0 is the shared verifier, of which the verifier blocks are stated, and D is a wrapper of it (the witness is core037bVerify of the shared verifier), so AC4's 'never changes a verdict or a result field' holds of a D0 that meets those blocks. Every result field but the notes is D0's, so a line of another verifier block that reads only those fields holds of D when it holds of D0, and a line that asks for a note in the notes (VER-006's vacuity note) too."
          "AC1 and AC2, verifier half (one WARNING: line per dead reset, read or inhibitor arc, with its effect) are line 1 with CORE-037's text lines: CORE_037_verifier_nonvacuous shows the three lines of the test derivation's net, byte for byte, and that seeding the reset arc's place drops its line. AC3 (no line for a seeded place, an environment place, a consumed place or a place an output spec names) is line 1 through refDeadArcs, as in the F block. AC4, verifier half (never changes a verdict or a result field) is line 2. That verification never fails on a dead arc is an offer clause: the model's verifier (EnvDecider) is a total function, so no line can say it, and it belongs in a coverage theorem (an open item). The executor halves of AC1 to AC4 are the block CORE_037_events."
          "The test derivation's verifier half (verify any property of the same net and assert the report line) is CORE_037_verifier_nonvacuous, with a PlaceBound property under Ignore. Python runs the Rust verifier and inherits its report."
  signoff "2026-11-13 714dee4cb48fa43a ai"
  statement : EnvDecider String → EnvDecider String → Prop :=
    fun D D0 => ∀ mode envs o X φ m0,
      (D mode envs o X φ m0).notes.filter (core037bDeadLine X.net) = core037bLines X.net envs m0 ∧
      core037bStrip X.net (D mode envs o X φ m0) = D0 mode envs o X φ m0

/- The pinned readable forms: a change to a formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CORE_037_events : {T : Type} → EvExec String T → EvExec String T → Prop :=
fun {T} E E0 =>
  ∀ (C : Cfg String T),
    (∀ (M0 : QMarking String T), List.filter (core037bDeadEv C.X.net) (E.boot C M0) = core037bWarnings C M0) ∧
      (∀ (M0 : QMarking String T) (pre post : List (NetEvent String T)),
          E.boot C M0 = pre ++ NetEvent.executionStarted :: post → List.filter (core037bDeadEv C.X.net) post = []) ∧
        (∀ (H : List (NetEvent String T)) (s : XSt String T) (l : XLbl String T) (evs : List (NetEvent String T))
            (s' : XSt String T), E.step C H s l evs s' → ∀ e ∈ evs, core037bDeadEv C.X.net e = false) ∧
          (∀ (M0 : QMarking String T), List.filter (fun e => !core037bDeadEv C.X.net e) (E.boot C M0) = E0.boot C M0) ∧
            ∀ (H : List (NetEvent String T)) (s : XSt String T) (l : XLbl String T) (evs : List (NetEvent String T))
              (s' : XSt String T),
              E.step C H s l evs s' ↔ E0.step C (List.filter (fun e => !core037bDeadEv C.X.net e) H) s l evs s'
-/
#guard_msgs in #print CORE_037_events

/--
info: def Libpetri.Spec.CORE_037_verifier : EnvDecider String → EnvDecider String → Prop :=
fun D D0 =>
  ∀ (mode : EnvMode) (envs : List String) (o : Verifier.Options) (X : TimedNet String) (φ : VerProp String)
    (m0 : NMarking String),
    List.filter (core037bDeadLine X.net) (D mode envs o X φ m0).notes = core037bLines X.net envs m0 ∧
      core037bStrip X.net (D mode envs o X φ m0) = D0 mode envs o X φ m0
-/
#guard_msgs in #print CORE_037_verifier

/-! ## The F block fixes the report and the text -/

/-- The text lines of CORE-037 fix the warning text of every entry: every text that meets the F
block is `refDeadArcMsg`. With `CORE_037_unique` (the report is `refDeadArcs`) this is why the
two blocks here read the reference report and text directly. -/
theorem core037b_msg_unique (Rep : DeadArcReport String) (Msg : DeadArc String → String)
    (h : CORE_037 Rep Msg) : Msg = refDeadArcMsg := by
  funext a
  obtain ⟨k, t, p⟩ := a
  cases k
  · exact h.2.2.1 t p
  · exact h.2.2.2.1 t p
  · exact h.2.2.2.2 t p

/-! ## The witnesses -/

section Witnesses

variable {T : Type}

/-- **The executor with dead-arc WARNs** over `E0`: the boot emits the WARNs of the run's
dead-arc report, then `E0`'s boot events; a step is a step of `E0` given the history with the
dead-arc events left out (Java, TypeScript and Rust warn when the executor is constructed, before
the run, and never read the warnings back). -/
def core037bExec (E0 : EvExec String T) : EvExec String T where
  boot C M0 := core037bWarnings C M0 ++ E0.boot C M0
  step C H := E0.step C (H.filter fun e => !core037bDeadEv C.X.net e)

/- The executor with dead-arc WARNs is a witness model of CORE-037's events block. -/
#spec_witness core037bExec

/-- The reference executor with the unknown-place WARNs of [CORE-072] AC4 at deposits and
injections (EVT-013's `evt013_diagX`) and the reference boot: EVT-013's reference with engine
diagnostics without its placeholder dead-arc WARNs. -/
def core037bUnknownExec (P : EvPol) : EvExec String T := evt013_ext P (refBoot P) evt013_diagX

/- The reference with the unknown-place WARNs is a witness model of CORE-037's events block. -/
#spec_witness core037bUnknownExec

end Witnesses

/-- **The verifier with dead-arc lines** over `D0`: `D0`'s result with the dead-arc lines of the
net as the caller passed it in front of its notes (Rust `finish`, Java and TypeScript `verify`
write them at the head of the report). -/
def core037bVerify (D0 : EnvDecider String) : EnvDecider String := fun mode envs o X φ m0 =>
  { D0 mode envs o X φ m0 with
    notes := core037bLines X.net envs m0 ++ (D0 mode envs o X φ m0).notes }

/- The verifier with dead-arc lines is a witness model of CORE-037's verifier block. -/
#spec_witness core037bVerify

/-! ## The lines hold of the witnesses -/

section Holds

variable {T : Type}

/-- An entry of the reference report is a read, inhibitor or reset arc of the net. -/
theorem core037b_report_cand {X : Reference.Net String} {env : String → Bool}
    {m0 : String → Nat} {a : DeadArc String} (h : a ∈ refDeadArcs X env m0) :
    a ∈ deadArcCandidates X :=
  (List.mem_filter.1 h).1

/-- The WARN of an arc of the net is a dead-arc event. -/
theorem core037b_event_dead {X : Reference.Net String} {a : DeadArc String}
    (h : a ∈ deadArcCandidates X) : core037bDeadEv X (core037bEvent (T := T) a) = true := by
  simp only [core037bDeadEv, core037bEvent, List.any_eq_true, beq_iff_eq]
  exact ⟨a, h, rfl⟩

/-- An event that is not a log message is not a dead-arc event. -/
theorem core037b_noLog_dead (X : Reference.Net String) {e : NetEvent String T}
    (h : e.isLog = false) : core037bDeadEv X e = false := by
  cases e <;> first | rfl | simp [NetEvent.isLog, NetEvent.kind] at h

/-- The WARNs of a run are all dead-arc events. -/
theorem core037b_warnings_dead (C : Cfg String T) (M0 : QMarking String T) :
    ∀ e ∈ core037bWarnings C M0, core037bDeadEv C.X.net e = true := by
  intro e he
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he
  exact core037b_event_dead (core037b_report_cand ha)

/-- If the WARNs of a run followed by a boot `B` with no dead-arc event are split at an
ExecutionStarted, nothing after it is a dead-arc event: ExecutionStarted is no WARN, so it lies
in `B`, and so does everything after it. -/
theorem core037b_after_start (C : Cfg String T) (M0 : QMarking String T)
    {B pre post : List (NetEvent String T)} (hb : ∀ e ∈ B, core037bDeadEv C.X.net e = false)
    (h : core037bWarnings C M0 ++ B = pre ++ NetEvent.executionStarted :: post) :
    post.filter (core037bDeadEv C.X.net) = [] := by
  have hpost : ∀ e ∈ post, e ∈ B := by
    rcases List.append_eq_append_iff.1 h with ⟨as, -, hB⟩ | ⟨bs, hW, hx⟩
    · intro e he
      rw [hB]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ he)
    · cases bs with
      | nil =>
        simp only [List.nil_append] at hx
        intro e he
        rw [← hx]
        exact List.mem_cons_of_mem _ he
      | cons y bs =>
        simp only [List.cons_append, List.cons.injEq] at hx
        have hm : NetEvent.executionStarted ∈ core037bWarnings C M0 := by
          rw [hW, hx.1]
          exact List.mem_append_right _ (List.mem_cons_self ..)
        have := core037b_warnings_dead C M0 _ hm
        simp [core037bDeadEv] at this
  exact List.filter_eq_nil_iff.2 fun e he => by simp [hb e (hpost e he)]

/-- Every executor with events whose boot and steps emit no dead-arc event, wrapped with the
dead-arc WARNs, meets the events block against itself. -/
theorem core037b_events_of (E0 : EvExec String T)
    (hb : ∀ C M0, ∀ e ∈ E0.boot C M0, core037bDeadEv C.X.net e = false)
    (hs : ∀ C H s l evs s', E0.step C H s l evs s' → ∀ e ∈ evs, core037bDeadEv C.X.net e = false) :
    CORE_037_events (core037bExec E0) E0 := by
  intro C
  refine ⟨fun M0 => ?_, fun M0 _ _ h => core037b_after_start C M0 (hb C M0) h,
    fun H s l evs s' h => hs C _ s l evs s' h,
    fun M0 => ?_, fun _ _ _ _ _ => Iff.rfl⟩
  · show (core037bWarnings C M0 ++ E0.boot C M0).filter _ = _
    rw [List.filter_append, List.filter_eq_self.2 (core037b_warnings_dead C M0),
      List.filter_eq_nil_iff.2 (fun e he => by simp [hb C M0 e he]), List.append_nil]
  · show (core037bWarnings C M0 ++ E0.boot C M0).filter _ = _
    rw [List.filter_append,
      List.filter_eq_nil_iff.2 (fun e he => by simp [core037b_warnings_dead C M0 e he]),
      List.filter_eq_self.2 (fun e he => by simp [hb C M0 e he]), List.nil_append]

/-- ✓ The reference executor with the Rust and Python emission meets CORE-037's events block:
it warns once per dead arc at boot, in report order, then runs exactly as before. -/
@[evidence holds CORE_037_events]
theorem CORE_037_events_reference :
    CORE_037_events (core037bExec (refEvExec (N := String) (T := T) polRust)) (refEvExec polRust) :=
  core037b_events_of _ (fun C M0 e he => core037b_noLog_dead _ (refBoot_noLog polRust C M0 e he))
    (fun C H s l evs s' h e he => by
      obtain ⟨-, rfl⟩ := h
      exact core037b_noLog_dead _ (refEmitW_noLog polRust C H s l s' e he))

/-- ✓ The same with the Java and TypeScript emission (its boot also holds the snapshot of the
initial marking). -/
@[evidence holds CORE_037_events]
theorem CORE_037_events_referenceJT :
    CORE_037_events (core037bExec (refEvExec (N := String) (T := T) polJT)) (refEvExec polJT) :=
  core037b_events_of _ (fun C M0 e he => core037b_noLog_dead _ (refBoot_noLog polJT C M0 e he))
    (fun C H s l evs s' h e he => by
      obtain ⟨-, rfl⟩ := h
      exact core037b_noLog_dead _ (refEmitW_noLog polJT C H s l s' e he))

/-- On the reference the wrapped executor steps exactly as `refEvExec`: the reference's events
never read the history. -/
theorem core037b_ref_step (P : EvPol) (C : Cfg String T) (H : List (NetEvent String T))
    (s : XSt String T) (l : XLbl String T) (evs : List (NetEvent String T)) (s' : XSt String T) :
    (core037bExec (refEvExec P)).step C H s l evs s' ↔ (refEvExec P).step C H s l evs s' :=
  Iff.rfl

/-- No warning text of an arc starts like the unknown-place WARN of [CORE-072] AC4. -/
theorem core037b_unknownMsg_ne (a : DeadArc String) : evt013_unknownMsg ≠ refDeadArcMsg a := by
  intro h
  have := congrArg (fun y : String => y.toList.take 1) h
  obtain ⟨k, t, p⟩ := a
  cases k <;> simp [refDeadArcMsg, evt013_unknownMsg] at this

/-- Every event `evt013_diagX` adds is an unknown-place WARN. -/
theorem core037b_diagX_unknown (C : Cfg String T) (H : List (NetEvent String T))
    (s : XSt String T) (l : XLbl String T) :
    ∀ e ∈ evt013_diagX C H s l, ∃ nm, e = .logMessage (some nm) .warn evt013_unknownMsg := by
  intro e he
  unfold evt013_diagX at he
  repeat' split at he
  all_goals first
    | exact ⟨_, evt013_unknownWarns_mem he⟩
    | (simp only [evt013_settleWarns] at he
       repeat' split at he
       all_goals first | exact ⟨_, evt013_unknownWarns_mem he⟩ | cases he)
    | cases he

/-- ✓ The reference with the unknown-place WARNs of [CORE-072] AC4 meets CORE-037's events block
once it warns about dead arcs: those WARNs carry another text, so they are no dead-arc events. -/
@[evidence holds CORE_037_events]
theorem CORE_037_events_unknown :
    CORE_037_events (core037bExec (core037bUnknownExec (T := T) polJT))
      (core037bUnknownExec polJT) :=
  core037b_events_of _ (fun C M0 e he => core037b_noLog_dead _ (refBoot_noLog polJT C M0 e he))
    (fun C H s l evs s' h e he => by
      obtain ⟨-, rfl⟩ := h
      rcases List.mem_append.1 he with h' | h'
      · exact core037b_noLog_dead _ (refEmitW_noLog polJT C H s l s' e h')
      · obtain ⟨nm, rfl⟩ := core037b_diagX_unknown C H s l e h'
        simp only [core037bDeadEv, List.any_eq_false, beq_iff_eq]
        exact fun a _ => core037b_unknownMsg_ne a)

/-- The executor with dead-arc WARNs meets EVT-013 whenever the executor under it does: each WARN
names the transition of its own entry of the dead-arc report (EVT-013's boot line), and the
steps are those of `E0`, for which EVT-013 holds at every history. -/
theorem core037b_evt013 {E0 : EvExec String T} {A : ActionLogRel String T}
    (h : EVT_013 E0 A) : EVT_013 (core037bExec E0) A := by
  intro C
  obtain ⟨h1, ⟨hb, hi, hd⟩, he⟩ := h C
  refine ⟨h1, ⟨fun M0 e hm hl => ?_, fun H k evs => hi _ k evs,
    fun H l i evs hl => hd _ l i evs hl⟩, fun H l evs hl => he _ l evs hl⟩
  rcases List.mem_append.1 hm with h' | h'
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 h'
    exact Or.inr ⟨a, ha, rfl⟩
  · exact hb M0 e h' hl

/-- The reference with the unknown-place WARNs and the dead-arc WARNs meets EVT-013 with the
reference action log: one executor with real dead-arc texts for both blocks. -/
theorem core037b_unknown_evt013 :
    EVT_013 (core037bExec (core037bUnknownExec (T := T) polJT)) refALog :=
  core037b_evt013 ((evt013_iff _ _).2 ⟨evt013_line1_refALog _,
    evt013_ext_line2 refALog (fun C M0 e he hl => by
        rw [refBoot_noLog polJT C M0 e he] at hl; cases hl)
      evt013_diagX_inject evt013_diagX_deposit,
    evt013_ext_line3 refALog fun C H s l hl e he => by
      rw [evt013_diagX_ending C H s l hl] at he; cases he⟩)

end Holds

section HoldsVer

/-- A dead-arc line starts with `W`. -/
theorem core037b_deadLine_head {X : Reference.Net String} {l : String}
    (h : core037bDeadLine X l = true) : l.toList.take 1 = ['W'] := by
  simp only [core037bDeadLine, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨a, -, rfl⟩ := h
  simp [core037bPrefix]

/-- Every verifier whose notes hold no dead-arc line, wrapped with the dead-arc lines, meets the
verifier block against itself. -/
theorem core037b_verifier_of (D0 : EnvDecider String)
    (h : ∀ mode envs o X φ m0, ∀ l ∈ (D0 mode envs o X φ m0).notes,
      core037bDeadLine X.net l = false) :
    CORE_037_verifier (core037bVerify D0) D0 := by
  intro mode envs o X φ m0
  have hl : ∀ l ∈ core037bLines X.net envs m0, core037bDeadLine X.net l = true := by
    intro l hm
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hm
    simp only [core037bDeadLine, List.any_eq_true, beq_iff_eq]
    exact ⟨a, core037b_report_cand ha, rfl⟩
  constructor
  · show (core037bLines X.net envs m0 ++ (D0 mode envs o X φ m0).notes).filter _ = _
    rw [List.filter_append, List.filter_eq_self.2 hl,
      List.filter_eq_nil_iff.2 (fun l hm => by simp [h mode envs o X φ m0 l hm]), List.append_nil]
  · have hn : (core037bLines X.net envs m0 ++ (D0 mode envs o X φ m0).notes).filter
        (fun l => !core037bDeadLine X.net l) = (D0 mode envs o X φ m0).notes := by
      rw [List.filter_append, List.filter_eq_nil_iff.2 (fun l hm => by simp [hl l hm]),
        List.filter_eq_self.2 (fun l hm => by simp [h mode envs o X φ m0 l hm]), List.nil_append]
    simp only [core037bStrip, core037bVerify, hn]

/-- The notes of `refEnvVerify` hold no dead-arc line: they are empty or VER-006's vacuity note,
which starts with `n`. -/
theorem core037b_refEnvVerify_clean (mode : EnvMode) (envs : List String) (o : Verifier.Options)
    (X : Reference.TimedNet String) (φ : VerProp String) (m0 : NMarking String) :
    ∀ l ∈ (refEnvVerify mode envs o X φ m0).notes, core037bDeadLine X.net l = false := by
  intro l hl
  cases hd : core037bDeadLine X.net l with
  | false => rfl
  | true =>
    have h1 := core037b_deadLine_head hd
    simp only [refEnvVerify] at hl
    split at hl
    · rw [List.mem_singleton.1 hl] at h1
      simp [vacuityNote] at h1
    · cases hl

/-- ✓ The reference environment-aware verifier with the dead-arc lines meets CORE-037's verifier
block: its notes open with one `WARNING:` line per dead arc, and every field is that of
`refEnvVerify`. -/
@[evidence holds CORE_037_verifier]
theorem CORE_037_verifier_reference : CORE_037_verifier (core037bVerify refEnvVerify) refEnvVerify :=
  core037b_verifier_of _ core037b_refEnvVerify_clean

end HoldsVer

/-! ## Examples -/

/-- The net of the examples: `kill` reads `r`, is inhibited by `a` and resets `x`; `kill2` is
inhibited by `x`; `use` consumes from `a`. Nothing else touches `r` or `x`. -/
def core037b_net : Reference.Net String :=
  { places := ["a", "r", "x"],
    transitions :=
      [core037_tr "kill" ["r"] ["a"] ["x"],
       core037_tr "kill2" [] ["x"] [],
       { core := { name := "use", inputs := [⟨"a", .one⟩], inhibitors := [], reads := [],
                   resets := [] },
         out := none }] }

/-- The example net, untimed. -/
def core037b_X : Reference.TimedNet String :=
  { net := core037b_net, timing := fun _ => .immediate, tol := 0 }

/-- The configuration of the examples: the example net, no environment place. -/
def core037b_cfg : Cfg String Nat :=
  { X := core037b_X, prio := fun _ => 0, terminals := [], envs := [], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => false,
    res := 0 }

/-- The empty initial marking. -/
def core037b_empty : QMarking String Nat := fun _ => []

/-- The initial marking with one token on `x`. -/
def core037b_seeded : QMarking String Nat := fun p => if p = "x" then [1] else []

/-- The empty initial marking of a verification. -/
def core037b_vEmpty : NMarking String := ⟨[], by decide, by decide⟩

/-- The initial marking of a verification with one token on `x`. -/
def core037b_vSeeded : NMarking String := ⟨[("x", 1)], by decide, by decide⟩

/-- The property of the verifier examples: at most one token on `a`. -/
def core037b_phi : VerProp String := .placeBound "a" 1

/-- The read arc of `kill` on `r`. -/
def core037b_readMsg : String :=
  "read arc of 'kill' on 'r': no transition produces into or consumes from it and it starts empty; the transition can never be enabled."

/-- The reset arc of `kill` on `x`. -/
def core037b_resetMsg : String :=
  "reset arc of 'kill' on 'x': no transition produces into or consumes from it and it starts empty; the arc has no effect."

/-- The inhibitor arc of `kill2` on `x`. -/
def core037b_inhMsg : String :=
  "inhibitor arc of 'kill2' on 'x': no transition produces into or consumes from it and it starts empty; the arc never blocks."

set_option maxRecDepth 20000 in
/-- Constructed with an empty initial marking, the executor of the example net first warns three
times, all under level WARN: the read arc of `kill` on `r`, then the reset arc of `kill` on `x`,
then the inhibitor arc of `kill2` on `x` (two dead arcs on one place are two warnings), and only
then emits ExecutionStarted and the snapshot of the initial marking, which lists no place. The
inhibitor arc of `kill` on `a` gets no warning, because `use`
consumes from `a`. With one token on `x` the two warnings about `x` go away and the warning about
`r` stays, and the snapshot lists `x` with its token. -/
@[evidence nonvacuous CORE_037_events]
theorem CORE_037_events_nonvacuous :
    (core037bExec (refEvExec (N := String) (T := Nat) polRust)).boot core037b_cfg core037b_empty =
      [.logMessage (some "kill") .warn core037b_readMsg,
       .logMessage (some "kill") .warn core037b_resetMsg,
       .logMessage (some "kill2") .warn core037b_inhMsg,
       .executionStarted, .markingSnapshot []] ∧
    (core037bExec (refEvExec (N := String) (T := Nat) polRust)).boot core037b_cfg core037b_seeded =
      [.logMessage (some "kill") .warn core037b_readMsg, .executionStarted,
       .markingSnapshot [("x", [1])]] := by
  constructor <;> decide

/-- `refEnvVerify` writes no note on a `PlaceBound` property. -/
theorem core037b_refEnvVerify_notes (mode : EnvMode) (envs : List String) (o : Verifier.Options)
    (X : Reference.TimedNet String) (p : String) (k : Nat) (m0 : NMarking String) :
    (refEnvVerify mode envs o X (.placeBound p k) m0).notes = [] := by
  simp [refEnvVerify, quiescenceProp]

set_option maxRecDepth 20000 in
/-- Verifying "at most one token on `a`" for the example net from an empty initial marking, the
report opens with three lines: `WARNING: ` followed by the warning about the read arc of `kill` on
`r`, then about its reset arc on `x`, then about the inhibitor arc of `kill2` on `x`. The verdict
is the one the verifier gives without the lines. From one token on `x` only the line about `r` is
left. -/
@[evidence nonvacuous CORE_037_verifier]
theorem CORE_037_verifier_nonvacuous :
    (core037bVerify refEnvVerify .ignore [] {} core037b_X core037b_phi core037b_vEmpty).notes =
      ["WARNING: " ++ core037b_readMsg, "WARNING: " ++ core037b_resetMsg,
       "WARNING: " ++ core037b_inhMsg] ∧
    (core037bVerify refEnvVerify .ignore [] {} core037b_X core037b_phi core037b_vSeeded).notes =
      ["WARNING: " ++ core037b_readMsg] ∧
    (core037bVerify refEnvVerify .ignore [] {} core037b_X core037b_phi core037b_vEmpty).verdict =
      (refEnvVerify .ignore [] {} core037b_X core037b_phi core037b_vEmpty).verdict := by
  refine ⟨?_, ?_, rfl⟩
  · show core037bLines core037b_net [] core037b_vEmpty ++ _ = _
    rw [core037b_phi, core037b_refEnvVerify_notes]
    decide
  · show core037bLines core037b_net [] core037b_vSeeded ++ _ = _
    rw [core037b_phi, core037b_refEnvVerify_notes]
    decide

/-! ## Wrong executors -/

/-- An executor that steps as the reference (Rust emission) and boots with the events `f a` for
the entries `a` of the report `rep`, then the reference boot. -/
def core037b_bootMut (rep : Cfg String Nat → QMarking String Nat → List (DeadArc String))
    (f : DeadArc String → NetEvent String Nat) : EvExec String Nat where
  boot C M0 := (rep C M0).map f ++ refBoot polRust C M0
  step := (refEvExec polRust).step

set_option maxRecDepth 20000 in
/-- ✗ An executor that does not warn at all violates CORE-037 (line 1, AC1, AC2): constructed for
the example net with an empty initial marking it emits only ExecutionStarted and the snapshot,
where three dead-arc warnings belong. -/
@[evidence forbids CORE_037_events]
theorem CORE_037_events_forbids_silent :
    ¬ CORE_037_events (refEvExec (N := String) (T := Nat) polRust) (refEvExec polRust) := by
  intro h
  have := (h core037b_cfg).1 core037b_empty
  revert this
  decide

set_option maxRecDepth 20000 in
/-- ✗ EVT-013's reference with engine diagnostics violates CORE-037 (line 1): its dead-arc WARN
says only "dead arc: no transition produces into or consumes from its place and it starts empty",
which names neither the arc's kind, its transition nor its place, so the example net's boot holds
none of the three warnings CORE-037 asks for. -/
@[evidence forbids CORE_037_events]
theorem CORE_037_events_forbids_placeholder :
    ¬ CORE_037_events (evt013_diagExec (N := String) (T := Nat) polRust) (refEvExec polRust) := by
  intro h
  have := (h core037b_cfg).1 core037b_empty
  revert this
  decide

set_option maxRecDepth 20000 in
/-- ✗ Warning at level INFO violates CORE-037 (line 1): the three warnings of the example net
carry the right names and texts but not the level WARN. -/
@[evidence forbids CORE_037_events]
theorem CORE_037_events_forbids_info :
    ¬ CORE_037_events (core037b_bootMut core037bBootReport
        fun a => .logMessage (some a.transition) .info (refDeadArcMsg a)) (refEvExec polRust) := by
  intro h
  have := (h core037b_cfg).1 core037b_empty
  revert this
  decide

set_option maxRecDepth 20000 in
/-- ✗ A warning that names no transition violates CORE-037 (line 1): the example net's warning
about the read arc on `r` must name `kill`, the transition that declares the arc. -/
@[evidence forbids CORE_037_events]
theorem CORE_037_events_forbids_unnamed :
    ¬ CORE_037_events (core037b_bootMut core037bBootReport
        fun a => .logMessage none .warn (refDeadArcMsg a)) (refEvExec polRust) := by
  intro h
  have := (h core037b_cfg).1 core037b_empty
  revert this
  decide

set_option maxRecDepth 20000 in
/-- ✗ One warning per place violates CORE-037 (line 1, 'two dead arcs on one place are two
messages'): of the two dead arcs on `x` in the example net only the reset arc of `kill` is
warned about, and the inhibitor arc of `kill2` is missing. -/
@[evidence forbids CORE_037_events]
theorem CORE_037_events_forbids_perPlace :
    ¬ CORE_037_events (core037b_bootMut (fun C M0 => core037_firstPerPlace (core037bBootReport C M0))
        core037bEvent) (refEvExec polRust) := by
  intro h
  have := (h core037b_cfg).1 core037b_empty
  revert this
  decide

set_option maxRecDepth 20000 in
/-- ✗ Warnings in kind order across transitions violate CORE-037 (line 1, 'in report order'): on
the example net the inhibitor arc of `kill2` on `x` is warned about before the reset arc of
`kill` on `x`. -/
@[evidence forbids CORE_037_events]
theorem CORE_037_events_forbids_kindMajor :
    ¬ CORE_037_events (core037b_bootMut (fun C M0 => core037_kindMajor C.X.net
        (fun p => decide (p ∈ C.envs)) (fun p => (M0 p).length)) core037bEvent)
      (refEvExec polRust) := by
  intro h
  have := (h core037b_cfg).1 core037b_empty
  revert this
  decide

/-- The reference (Rust emission) with the dead-arc WARNs of the current marking appended to
every step. -/
def core037b_rewarnBase : EvExec String Nat :=
  emitExec (refBoot polRust) fun C H s l s' => refEmitW polRust C H s l s' ++
    (refDeadArcs C.X.net (fun p => decide (p ∈ C.envs)) (fun p => (s.M p).length)).map
      core037bEvent

set_option maxRecDepth 20000 in
/-- ✗ Warning again in the steps violates CORE-037 (line 3, 'when the executor is constructed'):
an executor that repeats the dead-arc warnings in every step, here as the clock advances by
nothing from the start of a run of the example net, emits the warning about `r` a second time. -/
@[evidence forbids CORE_037_events]
theorem CORE_037_events_forbids_rewarn :
    ¬ CORE_037_events (core037bExec core037b_rewarnBase) core037b_rewarnBase := by
  intro h
  have := (h core037b_cfg).2.2.1 [] (xinit core037b_empty 0) (.delay 0)
    (refEmitW polRust core037b_cfg [] (xinit core037b_empty 0) (.delay 0)
        { xinit core037b_empty 0 with now := 0 } ++
      (refDeadArcs core037b_cfg.X.net (fun p => decide (p ∈ core037b_cfg.envs))
        (fun p => ((xinit core037b_empty 0 : XSt String Nat).M p).length)).map core037bEvent)
    { xinit core037b_empty 0 with now := 0 } ⟨rfl, rfl⟩
  revert this
  decide

/-- An executor that warns when its run starts instead of when it is constructed: its boot is
the reference boot, ExecutionStarted first, followed by the dead-arc warnings. -/
def core037b_late : EvExec String Nat where
  boot C M0 := refBoot polRust C M0 ++ core037bWarnings C M0
  step := (core037bExec (refEvExec polRust)).step

set_option maxRecDepth 20000 in
/-- The executor that warns late starts the run of the example net with ExecutionStarted and the
snapshot of the empty initial marking, and only then warns three times. -/
theorem core037b_late_boot :
    core037b_late.boot core037b_cfg core037b_empty =
      [.executionStarted, .markingSnapshot [],
       .logMessage (some "kill") .warn core037b_readMsg,
       .logMessage (some "kill") .warn core037b_resetMsg,
       .logMessage (some "kill2") .warn core037b_inhMsg] := by
  decide

set_option maxRecDepth 20000 in
/-- ✗ Warning after ExecutionStarted violates CORE-037 (line 2, 'when the executor is
constructed'): this executor gives the example net the right three warnings in the right order,
but only after ExecutionStarted, as an executor would that moved the warning from its
constructor into its run. -/
@[evidence forbids CORE_037_events]
theorem CORE_037_events_forbids_late :
    ¬ CORE_037_events core037b_late (refEvExec polRust) := by
  intro h
  have := (h core037b_cfg).2.1 core037b_empty [] _ core037b_late_boot
  revert this
  decide

/-- An executor that, when it has a dead arc to report, emits the warnings and nothing else at
boot. -/
def core037b_noStart : EvExec String Nat where
  boot C M0 := if core037bWarnings C M0 = [] then refBoot polRust C M0 else core037bWarnings C M0
  step := (core037bExec (refEvExec polRust)).step

set_option maxRecDepth 20000 in
/-- ✗ Dropping ExecutionStarted when there is a dead arc violates CORE-037 (line 4, 'its other
events shall be those of the same executor without the report'): on the example net the run
starts with the three warnings and no ExecutionStarted. -/
@[evidence forbids CORE_037_events]
theorem CORE_037_events_forbids_noStart :
    ¬ CORE_037_events core037b_noStart (refEvExec polRust) := by
  intro h
  have := (h core037b_cfg).2.2.2.1 core037b_empty
  revert this
  decide

/-- An executor that takes no step once a dead-arc warning is in its history. -/
def core037b_stopOnWarn : EvExec String Nat where
  boot := (core037bExec (refEvExec polRust)).boot
  step C H s l evs s' :=
    (refEvExec polRust).step C H s l evs s' ∧ H.any (core037bDeadEv C.X.net) = false

set_option maxRecDepth 20000 in
/-- ✗ Stopping after a warning violates CORE-037 (line 5, 'as if the dead-arc events had never
been emitted'): after the warning about the read arc of `kill` on `r`, the executor refuses to let
the clock advance, which the executor without the report does from the same state. -/
@[evidence forbids CORE_037_events]
theorem CORE_037_events_forbids_stopOnWarn :
    ¬ CORE_037_events core037b_stopOnWarn (refEvExec polRust) := by
  intro h
  have := ((h core037b_cfg).2.2.2.2 [.logMessage (some "kill") .warn core037b_readMsg]
    (xinit core037b_empty 0) (.delay 0) [] { xinit core037b_empty 0 with now := 0 }).2
      ⟨rfl, rfl⟩
  have h2 := this.2
  revert h2
  decide

/-! ## Wrong verifiers -/

/-- A verifier that writes the given lines in front of `refEnvVerify`'s notes. -/
def core037b_linesMut (f : Reference.Net String → List String → NMarking String → List String) :
    EnvDecider String := fun mode envs o X φ m0 =>
  { refEnvVerify mode envs o X φ m0 with notes := f X.net envs m0 ++ (refEnvVerify mode envs o X φ m0).notes }

set_option maxRecDepth 20000 in
/-- ✗ A verifier that writes no dead-arc line violates CORE-037 (line 1, AC1, AC2): verifying the
example net from an empty initial marking, its report holds none of the three lines. -/
@[evidence forbids CORE_037_verifier]
theorem CORE_037_verifier_forbids_silent : ¬ CORE_037_verifier refEnvVerify refEnvVerify := by
  intro h
  have := (h .ignore [] {} core037b_X core037b_phi core037b_vEmpty).1
  rw [core037b_phi, core037b_refEnvVerify_notes] at this
  revert this
  decide

set_option maxRecDepth 20000 in
/-- ✗ Leaving out the `WARNING: ` prefix violates CORE-037 (line 1): the example net's report
says "read arc of 'kill' on 'r': …" where "WARNING: read arc of 'kill' on 'r': …" belongs. -/
@[evidence forbids CORE_037_verifier]
theorem CORE_037_verifier_forbids_noPrefix :
    ¬ CORE_037_verifier (core037b_linesMut fun X envs m0 =>
        (refDeadArcs X (fun p => decide (p ∈ envs)) m0.count).map refDeadArcMsg) refEnvVerify := by
  intro h
  have := (h .ignore [] {} core037b_X core037b_phi core037b_vEmpty).1
  simp only [core037b_linesMut, core037b_phi, core037b_refEnvVerify_notes] at this
  revert this
  decide

set_option maxRecDepth 20000 in
/-- ✗ Warning about every read, inhibitor and reset arc violates CORE-037 (line 1, AC3): the
example net's report also warns about the inhibitor arc of `kill` on `a`, which `use` consumes
from. -/
@[evidence forbids CORE_037_verifier]
theorem CORE_037_verifier_forbids_everyArc :
    ¬ CORE_037_verifier (core037b_linesMut fun X _ _ =>
        (deadArcCandidates X).map fun a => core037bPrefix ++ refDeadArcMsg a) refEnvVerify := by
  intro h
  have := (h .ignore [] {} core037b_X core037b_phi core037b_vEmpty).1
  simp only [core037b_linesMut, core037b_phi, core037b_refEnvVerify_notes] at this
  revert this
  decide

/-- Another verdict: `Proven` becomes `Unknown`, `Violated` becomes `Unknown`, `Unknown` becomes
`Violated`. -/
def core037b_flip : Verifier.Verdict → Verifier.Verdict
  | .proven m => .unknown m
  | .violated => .unknown "dead arc"
  | .unknown _ => .violated

/-- A verifier whose verdict changes when it reports a dead arc. -/
def core037b_verdictMut : EnvDecider String := fun mode envs o X φ m0 =>
  let r := core037bVerify refEnvVerify mode envs o X φ m0
  if core037bLines X.net envs m0 = [] then r else { r with verdict := core037b_flip r.verdict }

set_option maxRecDepth 20000 in
/-- ✗ A verdict that depends on the warning violates CORE-037 (line 2, AC4, 'no verdict depends
on it'): verifying the example net, which has dead arcs, this verifier answers otherwise than the
same verifier without the report. -/
@[evidence forbids CORE_037_verifier]
theorem CORE_037_verifier_forbids_verdict :
    ¬ CORE_037_verifier core037b_verdictMut refEnvVerify := by
  intro h
  have h2 := congrArg Verifier.Result.verdict
    (h .ignore [] {} core037b_X core037b_phi core037b_vEmpty).2
  have hl : core037bLines core037b_X.net [] core037b_vEmpty ≠ [] := by decide
  simp only [core037bStrip, core037b_verdictMut, if_neg hl, core037bVerify] at h2
  revert h2
  cases (refEnvVerify .ignore [] {} core037b_X core037b_phi core037b_vEmpty).verdict <;>
    simp [core037b_flip]

end Libpetri.Spec
