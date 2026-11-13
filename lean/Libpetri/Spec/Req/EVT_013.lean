import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Events
import Libpetri.Spec.Req.CORE_037

set_option linter.missingDocs true

/-!
# EVT-013: LogMessage Event (`spec/08-events-observability.md`)

A LogMessage event carries two kinds of message: the log statements of an action, which the
executor captures and reports under the action's transition, and the diagnostics of the engine
itself (a dead arc, [CORE-037]; an unknown place, [CORE-072]; a repeated output place,
[IO-016]). This block says what such an event carries and when the executor stays silent.

The block `EVT_013` is a predicate over an abstract executor with events `E : EvExec N T`
(`Reference/Events.lean`) and an **action log** `A : ActionLogRel N T`: how the executor reports
one log statement of a firing's action. The reference executor has no label for an action's log
statement (the outside label `alog` that the event design asked of the executor model is not
there), so the action log is a relation of its own here, next to the steps; it changes no state.

* Line 1 (the action log): a captured log statement of the action of firing `i`, a firing of
  transition `t`, is reported as one LogMessage that names `t` and keeps the statement's level
  and text, also after the firing settled.
* Line 2 (who a diagnostic names): a diagnostic of the boot names no transition, or the
  transition of a dead arc of [CORE-037]'s report; a diagnostic of an injection names no
  transition; a diagnostic of a deposit (the settling of a completion or a timeout outcome, a
  mid-action publication) names the transition of the firing whose tokens are deposited. The
  empty name counts as no name (`NetEvent.namesNone`), since every runtime writes the empty string
  at the seams.
* Line 3 (no diagnostic on an ending the caller asked for or the net was built for, nor on a
  refused injection request): a drain, a close, an immediate termination, the discarding of queued
  external events behind a close, a refused injection request ([ENV-006]), and the end of a run
  (quiescent, terminal, closed or stopped) emit no LogMessage.

The witnesses are the reference executor with events `refEvExec` (which emits no diagnostic, so
lines 2 and 3 hold of it without a log event) with the reference action log `refALog` (Java and
TypeScript) or with `refNoALog` (Rust and Python, which capture no action log), and
`evt013_diagExec`, the reference with engine diagnostics: a WARN per dead arc of [CORE-037]'s
report at boot, named after the declaring transition, and a WARN for the first token that lands on
a place the net does not declare, named after the depositing firing's transition or with the
empty name at an injection.

The worked example (`evt013_cfg`): transition `a` takes place 0's token, its asynchronous action
writes 50 into place 5, which the net does not declare; transition `u` reads place 7, which
nothing feeds, so its read arc is dead; a caller injects 5 into the environment place 9, which
the net does not declare either.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## The terms the block reads -/

/-- **Action log** (proposed term). How an executor reports a log statement of an action:
`A C s i t lvl msg evs` says that under `C`, in state `s`, the action of firing `i`, a firing of
transition `t`, logs the message `msg` at level `lvl`, and the executor appends the events `evs`.
The transition is the one the firing was started for: the action carries it, also after the
firing settled. The statement changes no executor state; an executor that captures no action log
(Rust, Python) is the empty relation. -/
abbrev ActionLogRel (N T : Type) :=
  Cfg N T → XSt N T → Nat → Trans N → LogLevel → String → List (NetEvent N T) → Prop

/-- The event names no transition: it carries no transition name, or the empty name, which every
runtime writes for a diagnostic at the initial-marking and injection seams. -/
def NetEvent.namesNone {N T : Type} (e : NetEvent N T) : Bool := e.trans?.all (· == "")

/-- The transition declares a read, inhibitor or reset arc: the arcs a dead-arc diagnostic
([CORE-037]) can name. -/
def declaresSideArc {N : Type} (t : Trans N) : Bool :=
  !t.core.reads.isEmpty || !t.core.inhibitors.isEmpty || !t.core.resets.isEmpty

/-- **Ending step** (proposed term): a step on the way to an end the caller asked for or the net
was built for: a drain ([ENV-011]), a close ([ENV-013]), an immediate termination ([ENV-015]),
the discarding of a queued external event behind a close, the refusal of an injection request
because the executor drains, is closed or stopped, or has finished ([ENV-002]), and the end of a
run for any of the four termination reasons ([EXEC-041]). -/
def EndingLbl {N T : Type} (l : XLbl N T) : Prop :=
  l = .drain ∨ l = .close ∨ l = .terminateNow ∨ (∃ k, l = .discard k) ∨
    (∃ p x, l = .request p x .refused) ∨ ∃ c, l = .finish c

/-! ## EVT-013: LogMessage Event -/

requirement EVT_013
  id "EVT-013"
  title "LogMessage Event"
  kind B
  scope "all executors (event store enabled); the action log of line 1 is offered by Java and TypeScript"
  source verbatim "spec/08-events-observability.md"
  quote "*Where* the implementation captures the log statements of actions (Java and TypeScript), the executor *shall* report each log statement it captures from the action of a firing as one LogMessage event that carries the firing's transition name, the statement's level and its message."
        "*When* the executor emits an engine diagnostic before the first step of a run, the diagnostic *shall* carry an empty or absent transition name, unless it reports a dead arc ([CORE-037]), in which case it *shall* carry the name of the transition that declares the arc."
        "*When* the executor emits an engine diagnostic as it injects a token into an environment place, the diagnostic *shall* carry an empty or absent transition name."
        "*When* the executor emits an engine diagnostic as it deposits the outcome of a firing or a batch that the firing published ([IO-015]), the diagnostic *shall* carry the name of that firing's transition."
        "*When* the caller drains, closes or stops the executor ([ENV-011], [ENV-013], [ENV-015]), the executor *shall not* emit an engine diagnostic for the request or for the queued external events it discards because of it."
        "*When* a run ends because it is quiescent, a terminal place is marked, or the caller closed or stopped it ([EXEC-041]), the executor *shall not* emit an engine diagnostic for that end."
        "*When* the executor refuses an injection request because it is draining, closed or stopped, or because the run has finished ([ENV-006]), it *shall not* emit an engine diagnostic for the refusal."
  reading "For every executor with events E, every action log A and every configuration C:"
          "if, in state s, the action of firing i, a firing of transition t, logs the message msg at level lvl and the executor appends the events evs, and firing i, when it is in flight in s, is a firing of t, then evs is the single LogMessage that names t and carries the level lvl and the message msg;"
          "every LogMessage the boot of a run emits names no transition (no name or the empty name) or names the transition of an arc that the dead-arc report of CORE-037 lists for the net, its environment places and the initial marking; for every history H, every LogMessage an injection step appends names no transition; and for every history H, every LogMessage that a step settling or depositing for firing i appends (a commit, a timeout deposit or a publication of firing i) names the transition of firing i, whenever firing i is in flight in the step's source state;"
          "for every history H, a drain, a close, an immediate termination, the discarding of a queued external event, the refusal of an injection request and the end of a run for any reason append no LogMessage."
  assumes "The model is an executor with events E : EvExec N T (Reference/Events.lean) together with an action log A : ActionLogRel N T. E gives the events of the boot of a run and the events each step appends, given the events H emitted before it. A gives the events the executor appends when the action of a firing, of a given transition, in a state makes a log statement; it is a relation of its own because the reference executor RefExec has no label for an action's log statement (the outside label alog the event design asked for, design events.md section 5, request 1, is not in XLbl), and a log statement changes no executor state. In the model every LogMessage of a step of E is therefore an engine diagnostic, and every LogMessage of A is an action's. The witnesses are the reference executor with events refEvExec under both emission variants, which emits no engine diagnostic, with the reference action log refALog or, for Rust and Python, the empty action log refNoALog; and evt013_diagExec, the reference with the engine diagnostics: one WARN per entry of CORE-037's dead-arc report refDeadArcs at boot, named after the transition that declares the arc, and one WARN for the first token on a place the net does not declare, named after the depositing firing's transition or with the empty name at an injection (the first-write-per-place rule of CORE-072 AC4, read off the history H)."
          "Line 1 is the first quoted sentence. AC1 (log statements within actions are captured as LogMessage events) and AC2 (the log level is preserved) are line 1: the event names the transition of the firing whose action logged, and keeps the statement's level and message. A capture that drops the level breaks it (EVT_013_mutant_levelDropped), and so does one that names no transition (EVT_013_mutant_unattributed). That a log statement is reported at all is coverage, not a line: Evt013CaptureCovers asks that every log statement of an action still running is reported, refALog meets it (evt013_refALog_covers) and refNoALog does not (evt013_refNoALog_uncovered). Java captures what a logging adapter the host installs receives on a thread where LogCaptureScope is bound (java/src/main/java/org/libpetri/debug/LogCaptureScope.java, bound by LogCaptureScope.call in BitmapNetExecutor.fireTransition), so line 1 is about the statements the sink receives. The action log is given the transition t the firing was started for, because the action carries it: TypeScript's context.log closes over the transition's name and checks no executor state (the logFn that fireTransition builds in typescript/src/runtime/bitmap-net-executor.ts and precompiled-net-executor.ts; TransitionContext.detachForTimeout in typescript/src/core/transition-context.ts replaces the write target and the output and keeps the log function), and Java's LogCaptureScope binds the transition's name and its wrapRunnable and wrapCallable helpers carry it to other threads (java/src/main/java/org/libpetri/debug/LogCaptureScope.java). So a statement made after the firing settled (an abandoned action logging after its timeout outcome was deposited, or background work logging after the action returned) is still reported under the firing's transition name, and line 1 covers it. While firing i is in flight, t is its transition (the hypothesis of line 1); once it settled, the model keeps no record of the firing (it leaves s.fl), so which transition t is cannot be checked against the state there. This is a limit of the model, not a runtime defect. Rust and Python capture nothing: the transition context's log function is never installed (the TransitionContext::new calls of fire_transition_sync and fire_transition_async in rust/libpetri-runtime/src/executor_core/executor.rs; rust/libpetri-core/src/context.rs log), an implementation status of the Where clause, not a runtime defect. AC3 (exception details are included when present), the logger name and the timestamp are not modelled: the model's log message carries the transition name, the level and the message only (NetEvent.logMessage, GlossaryEvents.lean)."
          "Line 2 is the second, third and fourth quoted sentences, and the first half of AC4 (a diagnostic no transition is responsible for carries an empty or absent transition name, one a transition is responsible for carries that transition's name). The empty name counts as no name (NetEvent.namesNone): every runtime fills the transition name of a diagnostic at the initial-marking and injection seams with the empty string (Java BitmapNetExecutor.java: the deposit in processExternalEvents and warnUnknownInitialPlaces; TypeScript bitmap-net-executor.ts: the constructor and processExternalEvents, through warnUnknownPlace; Rust executor_core/executor.rs: warn_unknown_places("") in run_sync, run_async and handle_signal), and Java uses null for the interrupted run's WARN. Boot: the boot part of line 2 says that a named boot diagnostic names the transition of an entry of CORE-037's dead-arc report, refDeadArcs, for the net, its environment places and the token counts of the initial marking. The model cannot tell a dead-arc diagnostic from an unknown-initial-place one, because the message is not modelled, and the event does not carry the arc, so which dead arc a diagnostic reports is not checked: a named boot diagnostic names the transition of some dead arc. An executor that names every boot diagnostic after the first transition of the net breaks it (EVT_013_mutant_bootFirstTransition), and so does one that names it after the last transition of the net that declares a read, inhibitor or reset arc, which need not declare a dead arc (EVT_013_mutant_bootLastSideArc). Injection: an executor that names an injection's diagnostic after the transition of the last firing in flight breaks it (EVT_013_mutant_injectLastFired). Deposit: the settling of a completion (commit), the deposit of a timeout outcome (tdeposit) and a mid-action publication (publish) name the depositing firing's transition (Java deposit with t.name() in BitmapNetExecutor.java processSyncOutput and processCompletedTransitions, and warnMultiplicity; TypeScript bitmap-net-executor.ts processCompletedTransitions, warnMultiplicity and warnUnknownPlace with t.name; Rust executor_core/executor.rs warn_multiplicity and warn_unknown_places with the transition's name in fire_transition_sync, handle_completion, handle_flush and fire_transition_async); an executor that reports a deposit's diagnostic with the empty name breaks it (EVT_013_mutant_depositUnnamed). The deposit part asks nothing of a batch that a firing published and that lands after the firing settled (ruling D17): the model's publication queue keeps the firing's ID but not its transition, and a settled firing has left s.fl, so the transition of such a late publication is not known to the line. Rust carries the name in the flush message (handle_flush in executor_core/executor.rs) and so meets the quoted sentence there too; the gap is the model's (an open item: carry the transition in the queue entry). The diagnostics themselves, which places and transitions they report and how often (once per distinct unknown place per executor, CORE-072 AC4; once per transition per execution, IO-016 AC4; one per dead arc, CORE-037), are those requirements' subject, not this block's; the history H of XEvRel is what such a once-per-executor line reads."
          "The second half of AC4 (every consumer of the event tolerates an absent transition name) and the two MUST sentences of the body on consumers (treat the transition name as optional; never key, filter or group on it without handling its absence) bind consumers of the event, not the executor, and are not encoded here. EVT-030 states it for the query helpers (its line on a nameless event), and every runtime's transition filter meets it: Java's transitionEvents compares the names with Objects.equals and skips a log message whose name is null, TypeScript compares an optional name and Rust an Option."
          "Line 3 is the fifth, sixth and seventh quoted sentences, and AC5 (no engine diagnostic on a caller-requested termination path, nor when a run ends as quiescent, terminal, closed or stopped, nor when an injection request is refused). In the model these are the drain, close and terminateNow steps (the fifth sentence's request), the discard steps that drop queued external events behind a close (the fifth sentence's discarded events), the finish step of each of the four termination reasons (the sixth sentence), and the answer refused to an injection request (the seventh sentence; Reply.refused, replyFor in GlossaryExec.lean: the executor drains, is closed or stopped, or has finished, which is ENV-006's refusal; the refusal is already the reply). The seventh sentence is needed because a refused request is neither the drain, close or stop request nor a queued event it discards, and a refusal after a quiescent or terminal finish is not the end of the run either, so the fifth and sixth sentences alone do not ban its diagnostic; every runtime meets it. No runtime warns about a refused request: TypeScript's inject returns false (typescript/src/runtime/bitmap-net-executor.ts inject), Rust's handle refuses silently (rust/libpetri-runtime/src/executor_handle.rs, ExecutorHandle inject, inject_many, drain and close), Java completes the injection with false. An executor that warns when a run ends closed breaks line 3 (EVT_013_mutant_warnOnClose), and so does one that warns about a refused request (EVT_013_mutant_warnOnRefused). Java emits a WARN with no transition name when the orchestrator's wait is interrupted (termination reason INTERRUPTED, in the finally of BitmapNetExecutor.executeLoop): an interrupt is none of the model's four reasons and none of the caller's requests, the returned marking is partial, and the sixth quoted sentence does not cover it; TypeScript and Rust emit no diagnostic at the end of a run. EXEC-042's 'no diagnostic event is emitted' for a terminal stop is line 3 for finish terminal."
          "Not encoded, as kind A: the SHOULD sentence that an engine diagnostic is emitted only where it reports something the caller did not ask for and would otherwise not learn (line 3 states it, as the fifth, sixth and seventh quoted sentences, for the endings the caller asked for or the net was built for and for a refused injection request), and the MUST sentence that where a queryable result already carries the information (EXEC-041 AC3, the termination reason) the event is an addition to it and never the only signal: that is an obligation on the API, and EXEC-041 states the termination reason."
          "Assumptions shared by the executor event blocks: the event store is enabled and its append does not fail (EVT-020); an event is a value (EVT-001); transition names are distinct (ruling D10), and no transition is named with the empty string, which would read as no name. The events of one step are contiguous in the model, since a step appends its events at once. Java appends ActionTimedOut events and the log messages it captures from actions from other threads than the orchestrator (the timeout callback BitmapNetExecutor.fireTransition hands java/src/main/java/org/libpetri/runtime/ExecutorSupport.java withActionTimeout, which appends through emitEvent from the timer thread; LogCaptureScope.java wrapRunnable and wrapCallable), so in a Java store such an event can fall between the events of one step; the lines are read on the store with those events left out, as the reading at the top of spec/08-events-observability.md says. TypeScript and Rust append every event from the orchestrator."
          "The test derivation (an action logs a warning; verify a LogMessage event with the correct level and message) is EVT_013_nonvacuous: the action of a firing of a logs a WARN and the reference action log reports one LogMessage naming a, at WARN, with the same text; the run's boot reports the dead read arc of u under u's name; the injection into the undeclared place 9 reports its WARN with the empty name; the settling of a's completion, which deposits 50 into the undeclared place 5, reports its WARN under a's name; and the end of a closed run emits events, none a LogMessage."
  signoff "2026-11-13 758e0297ac01144b ai"
  statement : ∀ {N T : Type} [DecidableEq N], EvExec N T → ActionLogRel N T → Prop :=
    fun E A => ∀ C,
      (∀ s i t lvl msg evs, (∀ f, s.fl.find? (·.id == i) = some f → f.t = t) →
        A C s i t lvl msg evs → evs = [.logMessage (some t.core.name) lvl msg]) ∧
      ((∀ M0, ∀ e ∈ E.boot C M0, e.isLog = true → e.namesNone = true ∨
          ∃ a ∈ refDeadArcs C.X.net (fun p => decide (p ∈ C.envs)) (fun p => (M0 p).length),
            e.trans? = some a.transition) ∧
        (∀ H k evs, on (fun s s' => E.step C H s (.inject k) evs s'), shall (fun _ _ =>
          ∀ e ∈ evs, e.isLog = true → e.namesNone = true)) ∧
        (∀ H l i evs, (l = .commit i ∨ l = .tdeposit i ∨ l = .publish i) →
          on (fun s s' => E.step C H s l evs s'), shall (fun s _ =>
            ∀ f, s.fl.find? (·.id == i) = some f →
              ∀ e ∈ evs, e.isLog = true → e.trans? = some f.t.core.name))) ∧
      (∀ H l evs, EndingLbl l → on (fun s s' => E.step C H s l evs s'), shall (fun _ _ =>
        ∀ e ∈ evs, e.isLog = false))

/- The pinned readable form of EVT-013: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EVT_013 : {N T : Type} → [DecidableEq N] → EvExec N T → ActionLogRel N T → Prop :=
fun {N T} [DecidableEq N] E A =>
  ∀ (C : Cfg N T),
    (∀ (s : XSt N T) (i : ℕ) (t : Reference.Trans N) (lvl : LogLevel) (msg : String) (evs : List (NetEvent N T)),
        (∀ (f : Firing N T), List.find? (fun x => x.id == i) s.fl = some f → f.t = t) →
          A C s i t lvl msg evs → evs = [NetEvent.logMessage (some t.core.name) lvl msg]) ∧
      ((∀ (M0 : QMarking N T),
            ∀ e ∈ E.boot C M0,
              e.isLog = true →
                e.namesNone = true ∨
                  ∃ a ∈ refDeadArcs C.X.net (fun p => decide (p ∈ C.envs)) fun p => (M0 p).length,
                    e.trans? = some a.transition) ∧
          (∀ (H : List (NetEvent N T)) (k : ℕ) (evs : List (NetEvent N T)),
              on fun s s' => E.step C H s (XLbl.inject k) evs s', shall fun x x_1 =>
                ∀ e ∈ evs, e.isLog = true → e.namesNone = true) ∧
            ∀ (H : List (NetEvent N T)) (l : XLbl N T) (i : ℕ) (evs : List (NetEvent N T)),
              l = XLbl.commit i ∨ l = XLbl.tdeposit i ∨ l = XLbl.publish i →
                on fun s s' => E.step C H s l evs s', shall fun s x =>
                  ∀ (f : Firing N T),
                    List.find? (fun x => x.id == i) s.fl = some f →
                      ∀ e ∈ evs, e.isLog = true → e.trans? = some f.t.core.name) ∧
        ∀ (H : List (NetEvent N T)) (l : XLbl N T) (evs : List (NetEvent N T)),
          EndingLbl l → on fun s s' => E.step C H s l evs s', shall fun x x_1 => ∀ e ∈ evs, e.isLog = false
-/
#guard_msgs in #print EVT_013

/-! ## The three lines, one at a time -/

section Lines

variable {N T : Type}

/-- Line 1 of `EVT_013` alone: a captured log statement of the action of firing `i`, a firing of
`t`, is one LogMessage naming `t`, with the statement's level and text. -/
def evt013_line1 (_E : EvExec N T) (A : ActionLogRel N T) : Prop :=
  ∀ C s i t lvl msg evs, (∀ f, s.fl.find? (·.id == i) = some f → f.t = t) →
    A C s i t lvl msg evs → evs = [.logMessage (some t.core.name) lvl msg]

/-- The boot diagnostics name no transition or the transition of a dead arc of [CORE-037]'s
report for the net, its environment places and the initial marking. -/
def evt013_bootNames [DecidableEq N] (C : Cfg N T) (M0 : QMarking N T) (e : NetEvent N T) :
    Prop :=
  e.namesNone = true ∨
    ∃ a ∈ refDeadArcs C.X.net (fun p => decide (p ∈ C.envs)) (fun p => (M0 p).length),
      e.trans? = some a.transition

/-- Line 2 of `EVT_013` alone: who a diagnostic of the boot, of an injection and of a deposit
names. -/
def evt013_line2 [DecidableEq N] (E : EvExec N T) (_A : ActionLogRel N T) : Prop :=
  ∀ C, (∀ M0, ∀ e ∈ E.boot C M0, e.isLog = true → evt013_bootNames C M0 e) ∧
    (∀ H k evs, on (fun s s' => E.step C H s (.inject k) evs s'), shall (fun _ _ =>
      ∀ e ∈ evs, e.isLog = true → e.namesNone = true)) ∧
    (∀ H l i evs, (l = .commit i ∨ l = .tdeposit i ∨ l = .publish i) →
      on (fun s s' => E.step C H s l evs s'), shall (fun s _ =>
        ∀ f, s.fl.find? (·.id == i) = some f →
          ∀ e ∈ evs, e.isLog = true → e.trans? = some f.t.core.name))

/-- Line 3 of `EVT_013` alone: no LogMessage on an ending step. -/
def evt013_line3 (E : EvExec N T) (_A : ActionLogRel N T) : Prop :=
  ∀ C H l evs, EndingLbl l → on (fun s s' => E.step C H s l evs s'), shall (fun _ _ =>
    ∀ e ∈ evs, e.isLog = false)

/-- Every line but line 1. -/
def evt013_but1 [DecidableEq N] (E : EvExec N T) (A : ActionLogRel N T) : Prop :=
  evt013_line2 E A ∧ evt013_line3 E A

/-- Every line but line 2. -/
def evt013_but2 (E : EvExec N T) (A : ActionLogRel N T) : Prop :=
  evt013_line1 E A ∧ evt013_line3 E A

/-- Every line but line 3. -/
def evt013_but3 [DecidableEq N] (E : EvExec N T) (A : ActionLogRel N T) : Prop :=
  evt013_line1 E A ∧ evt013_line2 E A

/-- `EVT_013` is its three lines. -/
theorem evt013_iff [DecidableEq N] (E : EvExec N T) (A : ActionLogRel N T) :
    EVT_013 E A ↔ evt013_line1 E A ∧ evt013_line2 E A ∧ evt013_line3 E A :=
  ⟨fun h => ⟨fun C => (h C).1, fun C => (h C).2.1, fun C => (h C).2.2⟩,
   fun h C => ⟨h.1 C, h.2.1 C, h.2.2 C⟩⟩

end Lines

/-! ## The witnesses -/

section Witnesses

variable {N T : Type}

/-- **The reference action log** (Java and TypeScript): a log statement of the action of a
firing of `t` is reported as one LogMessage naming `t`, with the statement's level and text, in
flight or not (Java `LogCaptureScope` with the transition's name, TypeScript `context.log`, both
carried by the action). -/
def refALog : ActionLogRel N T := fun _ _ _ t lvl msg evs =>
  evs = [.logMessage (some t.core.name) lvl msg]

/- The reference action log is a witness model of EVT-013. -/
#spec_witness refALog

/-- The action log of Rust and Python: nothing is captured (the transition context's log
function is never installed). -/
def refNoALog : ActionLogRel N T := fun _ _ _ _ _ _ _ => False

/- The empty action log is a witness model of EVT-013 (Rust, Python). -/
#spec_witness refNoALog

/-- The text of the reference's unknown-place WARN ([CORE-072] AC4; the place name is left out,
the model's places have no names to print). -/
def evt013_unknownMsg : String :=
  "unknown place: tokens are retained in the marking but inert (the net declares no arc on it)"

/-- The text of the reference's dead-arc WARN ([CORE-037]; the arc is left out). -/
def evt013_deadMsg : String :=
  "dead arc: no transition produces into or consumes from its place and it starts empty"

/-- The unknown-place WARNs of a deposit of the places `ps`, named `nm`: one per distinct place of
`ps` that the net does not declare and that no earlier event of the history `H` added a token to
(the first write to the place, [CORE-072] AC4). -/
def evt013_unknownWarns [DecidableEq N] [Ord N] (C : Cfg N T) (H : List (NetEvent N T)) (nm : String)
    (ps : List N) : List (NetEvent N T) :=
  (ps.dedup.filter fun p => !decide (p ∈ C.X.net.places) && !H.any (NetEvent.addsTo p)).map
    fun _ => .logMessage (some nm) .warn evt013_unknownMsg

/-- The unknown-place WARNs of settling firing `i` (its returned emission or its timeout
outcome), named after the firing's transition. -/
def evt013_settleWarns [DecidableEq N] [Ord N] (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T)
    (i : Nat) : List (NetEvent N T) :=
  match s.fl.find? (·.id == i) with
  | some f =>
    evt013_unknownWarns C H f.t.core.name
      (match f.out with
       | some (.ok e) => e.map Prod.fst
       | some (.timedOut e) => e.map Prod.fst
       | _ => [])
  | none => []

/-- The engine diagnostics the reference with diagnostics adds to a step: the unknown-place
WARNs of a deposit, named after the depositing firing's transition, and of an injection, with
the empty name (Java `deposit`, TypeScript `warnUnknownPlace`, Rust `warn_unknown_places`). -/
def evt013_diagX [DecidableEq N] [Ord N] (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T) :
    XLbl N T → List (NetEvent N T)
  | .commit i => evt013_settleWarns C H s i
  | .tdeposit i => evt013_settleWarns C H s i
  | .publish i =>
    match s.pq, s.fl.find? (·.id == i) with
    | (_, b) :: _, some f => evt013_unknownWarns C H f.t.core.name (b.map Prod.fst)
    | _, _ => []
  | .inject _ =>
    match s.eq with
    | (_, p, _) :: _ => evt013_unknownWarns C H "" [p]
    | [] => []
  | _ => []

/-- The boot of the reference with diagnostics: a WARN per entry of [CORE-037]'s dead-arc
report, named after the transition that declares the arc, then the reference boot (Java,
TypeScript and Rust warn about dead arcs when the executor is constructed, before the run). -/
def evt013_diagBoot [DecidableEq N] [Ord N] (P : EvPol) (C : Cfg N T) (M0 : QMarking N T) :
    List (NetEvent N T) :=
  (refDeadArcs C.X.net (fun p => decide (p ∈ C.envs)) (fun p => (M0 p).length)).map
      (fun a => .logMessage (some a.transition) .warn evt013_deadMsg) ++
    refBoot P C M0

/-- An executor with events that steps as the reference executor, boots with `boot` and appends
the extra events `x` to the reference events of each step. -/
def evt013_ext [DecidableEq N] [Ord N] (P : EvPol) (boot : Cfg N T → QMarking N T → List (NetEvent N T))
    (x : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → List (NetEvent N T)) :
    EvExec N T :=
  emitExec boot (fun C H s l s' => refEmitW P C H s l s' ++ x C H s l)

/-- **The reference with engine diagnostics** under emission variant `P`: the reference executor
with events, with the dead-arc WARNs at boot and the unknown-place WARNs of deposits and
injections. -/
def evt013_diagExec [DecidableEq N] [Ord N] (P : EvPol) : EvExec N T :=
  evt013_ext P (evt013_diagBoot P) evt013_diagX

/- The reference with engine diagnostics is a witness model of EVT-013. -/
#spec_witness evt013_diagExec

end Witnesses

/-! ## The lines hold of the witnesses -/

section Holds

variable {N T : Type} [DecidableEq N] [Ord N]
omit [DecidableEq N] [Ord N] in
/-- No step label of the reference emits a LogMessage. -/
theorem lblKinds_noLog (l : XLbl N T) : NetEventKind.logMessage ∉ lblKinds l := by
  cases l <;> simp [lblKinds]

/-- The reference emits no LogMessage in any step: it has no engine diagnostic. -/
theorem refEmitW_noLog (P : EvPol) (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T)
    (l : XLbl N T) (s' : XSt N T) : ∀ e ∈ refEmitW P C H s l s', e.isLog = false := by
  intro e he
  cases h : e.isLog with
  | false => rfl
  | true =>
    have hk : e.kind = .logMessage := by simpa [NetEvent.isLog] using h
    exact absurd (hk ▸ refEmitW_kind P C H s l s' e he) (lblKinds_noLog l)

/-- The reference boot emits no LogMessage. -/
theorem refBoot_noLog (P : EvPol) (C : Cfg N T) (M0 : QMarking N T) :
    ∀ e ∈ refBoot P C M0, e.isLog = false := by
  intro e he
  rcases refBoot_kind P C M0 e he with h | h <;> simp [NetEvent.isLog, h]

omit [DecidableEq N] [Ord N] in
/-- Line 1 holds of the reference action log, whatever the executor. -/
theorem evt013_line1_refALog (E : EvExec N T) : evt013_line1 E refALog :=
  fun _ _ _ _ _ _ _ _ h => h

omit [DecidableEq N] [Ord N] in
/-- Line 1 holds of the empty action log, whatever the executor. -/
theorem evt013_line1_refNoALog (E : EvExec N T) : evt013_line1 E refNoALog :=
  fun _ _ _ _ _ _ _ _ h => h.elim

/-- Lines 2 and 3 hold of the reference executor with events, whatever the action log: it emits
no LogMessage at all. -/
theorem evt013_ref_but1 (P : EvPol) (A : ActionLogRel N T) :
    evt013_but1 (refEvExec (N := N) (T := T) P) A := by
  refine ⟨fun C => ⟨fun M0 e he hl => ?_, fun H k evs s s' hs => ?_,
      fun H l i evs _ s s' hs => ?_⟩, fun C H l evs _ s s' hs => ?_⟩
  · rw [refBoot_noLog P C M0 e he] at hl; cases hl
  · obtain ⟨-, rfl⟩ := hs
    intro e he hl
    rw [refEmitW_noLog P C H s _ s' e he] at hl; cases hl
  · obtain ⟨-, rfl⟩ := hs
    intro f _ e he hl
    rw [refEmitW_noLog P C H s _ s' e he] at hl; cases hl
  · obtain ⟨-, rfl⟩ := hs
    exact refEmitW_noLog P C H s l s'

/-- The reference executor with events meets `EVT_013` with every action log that meets
line 1. -/
theorem evt013_ref (P : EvPol) {A : ActionLogRel N T}
    (h1 : evt013_line1 (refEvExec (N := N) (T := T) P) A) : EVT_013 (refEvExec P) A :=
  (evt013_iff _ _).2 ⟨h1, evt013_ref_but1 P A⟩

/-- ✓ The reference executor with the Java and TypeScript emission and the reference action
log meet EVT-013: a log statement of an action is reported under its transition with its level
and text, and no step emits a diagnostic. -/
@[evidence holds EVT_013]
theorem EVT_013_reference : EVT_013 (refEvExec (N := N) (T := T) polJT) refALog :=
  evt013_ref polJT (evt013_line1_refALog _)

/-- ✓ The reference executor with the Rust and Python emission and no action log meets EVT-013:
nothing is captured, so line 1 asks nothing of it. -/
@[evidence holds EVT_013]
theorem EVT_013_rust : EVT_013 (refEvExec (N := N) (T := T) polRust) refNoALog :=
  evt013_ref polRust (evt013_line1_refNoALog _)

omit [DecidableEq N] [Ord N] in
/-- Every unknown-place WARN is a WARN named `nm`. -/
theorem evt013_unknownWarns_mem [DecidableEq N] [Ord N] {C : Cfg N T} {H : List (NetEvent N T)}
    {nm : String} {ps : List N} {e : NetEvent N T} (h : e ∈ evt013_unknownWarns C H nm ps) :
    e = .logMessage (some nm) .warn evt013_unknownMsg := by
  simp only [evt013_unknownWarns, List.mem_map] at h
  obtain ⟨_, _, rfl⟩ := h
  rfl

/-- The boot part of line 2 holds of the boot with dead-arc WARNs: each names the transition of
its own entry of the dead-arc report. -/
theorem evt013_diagBoot_line (P : EvPol) (C : Cfg N T) (M0 : QMarking N T) :
    ∀ e ∈ evt013_diagBoot P C M0, e.isLog = true → evt013_bootNames C M0 e := by
  intro e he hl
  rcases List.mem_append.1 he with h | h
  · simp only [List.mem_map] at h
    obtain ⟨a, ha, rfl⟩ := h
    exact Or.inr ⟨a, ha, rfl⟩
  · rw [refBoot_noLog P C M0 e h] at hl; cases hl

/-- Line 2 of an executor that steps as the reference and adds the events `x`, from what `boot`
and `x` emit. -/
theorem evt013_ext_line2 {P : EvPol} {boot : Cfg N T → QMarking N T → List (NetEvent N T)}
    {x : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → List (NetEvent N T)}
    (A : ActionLogRel N T)
    (hb : ∀ C M0, ∀ e ∈ boot C M0, e.isLog = true → evt013_bootNames C M0 e)
    (hi : ∀ C H s k, ∀ e ∈ x C H s (.inject k), e.isLog = true → e.namesNone = true)
    (hd : ∀ C H s l i, (l = .commit i ∨ l = .tdeposit i ∨ l = .publish i) →
      ∀ f, s.fl.find? (·.id == i) = some f →
        ∀ e ∈ x C H s l, e.isLog = true → e.trans? = some f.t.core.name) :
    evt013_line2 (evt013_ext P boot x) A := by
  refine fun C => ⟨hb C, fun H k evs s s' hs => ?_, fun H l i evs hl s s' hs => ?_⟩
  · obtain ⟨-, rfl⟩ := hs
    intro e hm hlog
    rcases List.mem_append.1 hm with h | h
    · rw [refEmitW_noLog P C H s _ s' e h] at hlog; cases hlog
    · exact hi C H s k e h hlog
  · obtain ⟨-, rfl⟩ := hs
    intro f hf e hm hlog
    rcases List.mem_append.1 hm with h | h
    · rw [refEmitW_noLog P C H s _ s' e h] at hlog; cases hlog
    · exact hd C H s l i hl f hf e h hlog

/-- Line 3 of an executor that steps as the reference and adds the events `x`, when `x` adds no
LogMessage to an ending step. -/
theorem evt013_ext_line3 {P : EvPol} {boot : Cfg N T → QMarking N T → List (NetEvent N T)}
    {x : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → List (NetEvent N T)}
    (A : ActionLogRel N T) (he : ∀ C H s l, EndingLbl l → ∀ e ∈ x C H s l, e.isLog = false) :
    evt013_line3 (evt013_ext P boot x) A := by
  intro C H l evs hl s s' hs
  obtain ⟨-, rfl⟩ := hs
  intro e hm
  rcases List.mem_append.1 hm with h | h
  · exact refEmitW_noLog P C H s l s' e h
  · exact he C H s l hl e h

/-- The diagnostics of an injection are named with the empty name. -/
theorem evt013_diagX_inject (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T) (k : Nat) :
    ∀ e ∈ evt013_diagX C H s (.inject k), e.isLog = true → e.namesNone = true := by
  intro e he _
  simp only [evt013_diagX] at he
  split at he
  · rw [evt013_unknownWarns_mem he]; rfl
  · cases he

/-- The diagnostics of a deposit are named after the depositing firing's transition. -/
theorem evt013_diagX_deposit (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T)
    (l : XLbl N T) (i : Nat) (hl : l = .commit i ∨ l = .tdeposit i ∨ l = .publish i)
    (f : Firing N T) (hf : s.fl.find? (·.id == i) = some f) :
    ∀ e ∈ evt013_diagX C H s l, e.isLog = true → e.trans? = some f.t.core.name := by
  intro e he _
  rcases hl with rfl | rfl | rfl
  · simp only [evt013_diagX, evt013_settleWarns, hf] at he
    rw [evt013_unknownWarns_mem he]; rfl
  · simp only [evt013_diagX, evt013_settleWarns, hf] at he
    rw [evt013_unknownWarns_mem he]; rfl
  · simp only [evt013_diagX, hf] at he
    split at he
    · rename_i hf'
      cases hf'
      rw [evt013_unknownWarns_mem he]; rfl
    · cases he

/-- The reference with diagnostics adds nothing to an ending step. -/
theorem evt013_diagX_ending (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T) (l : XLbl N T)
    (hl : EndingLbl l) : evt013_diagX C H s l = [] := by
  rcases hl with rfl | rfl | rfl | ⟨k, rfl⟩ | ⟨p, x, rfl⟩ | ⟨c, rfl⟩ <;> rfl

/-- The reference with engine diagnostics meets `EVT_013` with every action log that meets
line 1. -/
theorem evt013_diag (P : EvPol) {A : ActionLogRel N T}
    (h1 : evt013_line1 (evt013_diagExec (N := N) (T := T) P) A) :
    EVT_013 (evt013_diagExec P) A :=
  (evt013_iff _ _).2 ⟨h1, evt013_ext_line2 A (evt013_diagBoot_line P) evt013_diagX_inject
    evt013_diagX_deposit,
    evt013_ext_line3 A fun C H s l hl e he => by rw [evt013_diagX_ending C H s l hl] at he; cases he⟩

/-- ✓ The reference with engine diagnostics and the Java and TypeScript emission meets EVT-013
with the reference action log: its dead-arc WARNs at boot name the transition that declares the
arc, its unknown-place WARN at an injection has the empty name, and its unknown-place WARN at a
deposit names the depositing firing's transition. -/
@[evidence holds EVT_013]
theorem EVT_013_diag : EVT_013 (evt013_diagExec (N := N) (T := T) polJT) refALog :=
  evt013_diag polJT (evt013_line1_refALog _)

/-- ✓ The reference with engine diagnostics and the Rust and Python emission meets EVT-013 with
no action log: Rust emits these diagnostics and captures no action log. -/
@[evidence holds EVT_013]
theorem EVT_013_diagRust : EVT_013 (evt013_diagExec (N := N) (T := T) polRust) refNoALog :=
  evt013_diag polRust (evt013_line1_refNoALog _)

end Holds

/-! ## The offer: every log statement of a running action is reported -/

section Coverage

variable {N T : Type}

/-- **Capture coverage** (the offer half of AC1, not a line of the block): an action log reports
every log statement of an action that is still running, at every level and with every text. The
Java and TypeScript reference meets it; the empty action log of Rust and Python does not. -/
def Evt013CaptureCovers (A : ActionLogRel N T) : Prop :=
  ∀ C s i f, s.fl.find? (·.id == i) = some f → f.out = none → ∀ lvl msg,
    ∃ evs, A C s i f.t lvl msg evs

/-- The reference action log reports every log statement of a running action. -/
theorem evt013_refALog_covers : Evt013CaptureCovers (refALog (N := N) (T := T)) :=
  fun _ _ _ _ _ _ _ _ => ⟨_, rfl⟩

end Coverage

/-! ## The worked example -/

/-- Transition `a`: takes the token of place 0; output spec `Place(1)`. -/
def evt013_tA : Trans Nat :=
  { core := { name := "a", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 1) }

/-- Transition `u`: takes a token of place 1 and reads place 7, which no transition feeds or
consumes from, so its read arc is dead. -/
def evt013_tU : Trans Nat :=
  { core := { name := "u", inputs := [⟨1, .one⟩], inhibitors := [], reads := [7], resets := [] },
    out := none }

/-- The configuration of the example: places 0, 1 and 7; transitions `a` then `u`, both
Immediate; place 9 an environment place the net does not declare; validation accepts every
completion. -/
def evt013_cfg : Cfg Nat Nat :=
  { X := { net := { places := [0, 1, 7], transitions := [evt013_tA, evt013_tU] },
           timing := fun _ => .immediate, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [9], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => false,
    res := 0 }

/-- The initial marking: 10 in place 0. -/
def evt013_m0 : QMarking Nat Nat := fun p => if p = 0 then [10] else []

/-- The empty initial marking. -/
def evt013_empty : QMarking Nat Nat := fun _ => []

/-- One cycle up to the asynchronous start of `a` (firing 0). -/
def evt013_toStart : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin, .start "a" false]

/-- The pass ends; a caller asks to inject 5 into place 9 (ticket 1); the next cycle reaches
step 2. -/
def evt013_toInject : List (XLbl Nat Nat) :=
  evt013_toStart ++ [.endPass, .request 9 5 .accepted, .endCompletions, .endPublications]

/-- The injection lands; `a`'s action writes 50 into place 5 and returns; the loop ends the cycle
and waits for the completion. -/
def evt013_toCommit : List (XLbl Nat Nat) :=
  evt013_toInject ++
    [.inject 1, .write 0 5 50, .ret 0 true, .endEvents, .update, .deadline [], .begin, .endPass]

/-- A caller closes an executor with an empty marking; one cycle reaches the termination test. -/
def evt013_toClose : List (XLbl Nat Nat) :=
  [.close, .endCompletions, .endPublications, .endEvents, .update, .deadline []]

/-- The state of the example with `a`'s action running (firing 0). -/
theorem evt013_running :
    ∃ s f, xrun evt013_cfg (xinit evt013_m0 0) evt013_toStart = some s ∧
      s.fl.find? (·.id == 0) = some f ∧ f.t.core.name = "a" ∧ f.out = none := by
  have h : ((xrun evt013_cfg (xinit evt013_m0 0) evt013_toStart).bind fun s =>
      (s.fl.find? (·.id == 0)).map fun f => f.t.core.name == "a" && f.out.isNone) = some true := by
    decide +kernel
  cases ho : xrun evt013_cfg (xinit evt013_m0 0) evt013_toStart with
  | none => simp [ho] at h
  | some s =>
    cases hf : s.fl.find? (·.id == 0) with
    | none => simp [ho, hf] at h
    | some f =>
      simp only [ho, hf, Option.bind_some, Option.map_some, Option.some.injEq, Bool.and_eq_true,
        beq_iff_eq, Option.isNone_iff_eq_none] at h
      exact ⟨s, f, rfl, hf, h.1, h.2⟩

/-- The text the action of `a` logs in the example. -/
def evt013_logMsg : String := "cache miss"

/-- Read a decided fact off a step of the reference with diagnostics: the step exists and its
events pass `q`. -/
theorem evt013_check (o : Option (XSt Nat Nat)) (l : XLbl Nat Nat)
    (x : Cfg Nat Nat → List (NetEvent Nat Nat) → XSt Nat Nat → XLbl Nat Nat →
      List (NetEvent Nat Nat))
    (q : XSt Nat Nat → List (NetEvent Nat Nat) → Bool)
    (h : (o.bind fun s => (xstep evt013_cfg s l).map fun s' =>
      q s (refEmitW polJT evt013_cfg [] s l s' ++ x evt013_cfg [] s l)) = some true) :
    ∃ s s' evs, (evt013_ext polJT (evt013_diagBoot polJT) x).step evt013_cfg [] s l evs s' ∧
      q s evs = true := by
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt013_cfg) (o := o) (l := l)
    (p := fun s s' => q s (refEmitW polJT evt013_cfg [] s l s' ++ x evt013_cfg [] s l)) h
  exact ⟨s, s', _, ⟨hs, rfl⟩, hp⟩

/-- ✓ Every line is exercised. The action of `a` (firing 0, still running) logs a WARN "cache
miss", and the reference action log reports exactly one LogMessage naming `a`, at WARN, with that
text. The boot of the run reports the dead read arc of `u` on place 7 with a WARN naming `u`. The
injection of 5 into place 9, which the net does not declare, reports the TokenAdded and a WARN
with the empty name. The settling of `a`'s completion, which deposits 50 into the undeclared
place 5, reports a WARN naming `a`. A closed run ends with a snapshot and an ExecutionCompleted,
neither a LogMessage. -/
@[evidence nonvacuous EVT_013]
theorem EVT_013_nonvacuous :
    (∃ s f, xrun evt013_cfg (xinit evt013_m0 0) evt013_toStart = some s ∧
      s.fl.find? (·.id == 0) = some f ∧
      refALog evt013_cfg s 0 f.t .warn evt013_logMsg [.logMessage (some "a") .warn evt013_logMsg]) ∧
    NetEvent.logMessage (some "u") .warn evt013_deadMsg ∈
      (evt013_diagExec (N := Nat) (T := Nat) polJT).boot evt013_cfg evt013_m0 ∧
    (∃ s s' evs, (evt013_diagExec polJT).step evt013_cfg [] s (.inject 1) evs s' ∧
      evs = [.tokenAdded 9 5, .logMessage (some "") .warn evt013_unknownMsg]) ∧
    (∃ s s' evs, (evt013_diagExec polJT).step evt013_cfg [] s (.commit 0) evs s' ∧
      evs.filter (·.isLog) = [.logMessage (some "a") .warn evt013_unknownMsg]) ∧
    (∃ s s' evs, (evt013_diagExec polJT).step evt013_cfg [] s (.finish .closed) evs s' ∧
      evs ≠ [] ∧ ∀ e ∈ evs, e.isLog = false) := by
  refine ⟨?_, by decide +kernel, ?_, ?_, ?_⟩
  · obtain ⟨s, f, ho, hf, hn, -⟩ := evt013_running
    exact ⟨s, f, ho, hf, by show _ = _; rw [hn]⟩
  · obtain ⟨s, s', evs, hs, hp⟩ := evt013_check (xrun evt013_cfg (xinit evt013_m0 0) evt013_toInject)
      (.inject 1) evt013_diagX
      (fun _ evs => evs == [.tokenAdded 9 5, .logMessage (some "") .warn evt013_unknownMsg])
      (by decide +kernel)
    exact ⟨s, s', evs, hs, by simpa using hp⟩
  · obtain ⟨s, s', evs, hs, hp⟩ := evt013_check (xrun evt013_cfg (xinit evt013_m0 0) evt013_toCommit)
      (.commit 0) evt013_diagX
      (fun _ evs => evs.filter (·.isLog) == [.logMessage (some "a") .warn evt013_unknownMsg])
      (by decide +kernel)
    exact ⟨s, s', evs, hs, by simpa using hp⟩
  · obtain ⟨s, s', evs, hs, hp⟩ := evt013_check
      (xrun evt013_cfg (xinit evt013_empty 0) evt013_toClose) (.finish .closed) evt013_diagX
      (fun _ evs => !evs.isEmpty && evs.all fun e => !e.isLog)
      (by decide +kernel)
    simp only [Bool.and_eq_true, List.isEmpty_eq_false_iff, List.all_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true] at hp
    exact ⟨s, s', evs, hs, hp.1, hp.2⟩

/-- The empty action log of Rust and Python does not offer the capture: in the example, `a`'s
action is running and a log statement of it is reported by no events at all. -/
theorem evt013_refNoALog_uncovered : ¬ Evt013CaptureCovers (refNoALog (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, f, -, hf, -, hout⟩ := evt013_running
  obtain ⟨_, hn⟩ := h evt013_cfg s 0 f hf hout .warn evt013_logMsg
  exact hn

/-! ## Wrong executors -/

section Mutants

variable {N T : Type}

/-- An action log that reports every log statement at INFO, whatever its level. -/
def evt013_infoALog : ActionLogRel N T := fun _ _ _ t _ msg evs =>
  evs = [.logMessage (some t.core.name) .info msg]

/-- An action log that reports a log statement under no transition. -/
def evt013_anonALog : ActionLogRel N T := fun _ _ _ _ lvl msg evs =>
  evs = [.logMessage none lvl msg]

variable [DecidableEq N] [Ord N]
/-- The boot that names every dead-arc WARN after the first transition of the net instead of the
transition that declares the arc. -/
def evt013_firstBoot (P : EvPol) (C : Cfg N T) (M0 : QMarking N T) : List (NetEvent N T) :=
  (refDeadArcs C.X.net (fun p => decide (p ∈ C.envs)) (fun p => (M0 p).length)).map
      (fun _ => .logMessage ((C.X.net.transitions.head?).map (·.core.name)) .warn evt013_deadMsg) ++
    refBoot P C M0

/-- The diagnostics of the reference, with an injection's WARN named after the transition of the
last firing in flight. -/
def evt013_lastFiredX (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T) :
    XLbl N T → List (NetEvent N T)
  | .inject _ =>
    match s.eq with
    | (_, p, _) :: _ =>
      evt013_unknownWarns C H ((s.fl.getLast?.map (·.t.core.name)).getD "") [p]
    | [] => []
  | l => evt013_diagX C H s l

/-- The diagnostics of the reference, with a settled completion's WARN given the empty name, as
at a seam. -/
def evt013_seamCommitX (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T) :
    XLbl N T → List (NetEvent N T)
  | .commit i => (evt013_settleWarns C H s i).map fun _ => .logMessage (some "") .warn evt013_unknownMsg
  | l => evt013_diagX C H s l

/-- The name of the last transition of the net that declares a read, inhibitor or reset arc. -/
def evt013_lastSide (C : Cfg N T) : Option String :=
  ((C.X.net.transitions.filter declaresSideArc).getLast?).map (·.core.name)

/-- The boot that names every dead-arc WARN after the last transition of the net that declares a
read, inhibitor or reset arc, instead of the transition that declares the dead arc. -/
def evt013_lastSideBoot (P : EvPol) (C : Cfg N T) (M0 : QMarking N T) : List (NetEvent N T) :=
  (refDeadArcs C.X.net (fun p => decide (p ∈ C.envs)) (fun p => (M0 p).length)).map
      (fun _ => .logMessage (evt013_lastSide C) .warn evt013_deadMsg) ++
    refBoot P C M0

/-- The text of a WARN about a refused injection request. -/
def evt013_refusedMsg : String := "event refused: executor is draining, closed or stopped"

/-- The diagnostics of the reference, with a WARN with no transition name when the executor
refuses an injection request. -/
def evt013_refusedWarnX (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T) :
    XLbl N T → List (NetEvent N T)
  | .request _ _ .refused => [.logMessage none .warn evt013_refusedMsg]
  | l => evt013_diagX C H s l

/-- The text of a WARN at the end of a closed run. -/
def evt013_closedMsg : String := "execution stopped before quiescence (CLOSED)"

/-- The diagnostics of the reference, with a WARN with no transition name when a run ends
closed. -/
def evt013_closeWarnX (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T) :
    XLbl N T → List (NetEvent N T)
  | .finish .closed => [.logMessage none .warn evt013_closedMsg]
  | l => evt013_diagX C H s l

end Mutants

/-- ✗ A capture that drops the level violates EVT-013 (line 1): `a`'s action logs a WARN and the
action log reports it at INFO. The executor keeps lines 2 and 3. -/
@[evidence mutant EVT_013]
theorem EVT_013_mutant_levelDropped :
    evt013_but1 (refEvExec (N := Nat) (T := Nat) polJT) evt013_infoALog ∧
      ¬ EVT_013 (refEvExec (N := Nat) (T := Nat) polJT) evt013_infoALog := by
  refine ⟨evt013_ref_but1 polJT _, fun h => ?_⟩
  obtain ⟨s, f, -, hf, -, -⟩ := evt013_running
  have heq := (h evt013_cfg).1 s 0 f.t .warn evt013_logMsg _
    (fun f' hf' => by rw [hf] at hf'; cases hf'; rfl) rfl
  simp at heq

/-- ✗ A capture that names no transition violates EVT-013 (line 1): `a`'s action logs a WARN and
the action log reports it under no transition. The executor keeps lines 2 and 3. -/
@[evidence mutant EVT_013]
theorem EVT_013_mutant_unattributed :
    evt013_but1 (refEvExec (N := Nat) (T := Nat) polJT) evt013_anonALog ∧
      ¬ EVT_013 (refEvExec (N := Nat) (T := Nat) polJT) evt013_anonALog := by
  refine ⟨evt013_ref_but1 polJT _, fun h => ?_⟩
  obtain ⟨s, f, -, hf, -, -⟩ := evt013_running
  have heq := (h evt013_cfg).1 s 0 f.t .warn evt013_logMsg _
    (fun f' hf' => by rw [hf] at hf'; cases hf'; rfl) rfl
  simp at heq

/-- Lines 1 and 3 hold of an executor that adds the extra events `x` to the reference steps when
`x` adds nothing to an ending step, with the reference action log. -/
theorem evt013_ext_but2 {boot : Cfg Nat Nat → QMarking Nat Nat → List (NetEvent Nat Nat)}
    {x : Cfg Nat Nat → List (NetEvent Nat Nat) → XSt Nat Nat → XLbl Nat Nat →
      List (NetEvent Nat Nat)}
    (hx : ∀ C H s l, EndingLbl l → x C H s l = []) :
    evt013_but2 (evt013_ext polJT boot x) refALog := by
  refine ⟨evt013_line1_refALog _, fun C H l evs hl s s' hs => ?_⟩
  obtain ⟨-, rfl⟩ := hs
  dsimp only
  rw [hx C H s l hl, List.append_nil]
  exact refEmitW_noLog polJT C H s l s'

/-- ✗ Naming a boot diagnostic after the wrong transition violates EVT-013 (line 2): the dead
read arc of `u` is reported under the name of `a`, the first transition of the net, which
declares no read, inhibitor or reset arc. The executor keeps lines 1 and 3. -/
@[evidence mutant EVT_013]
theorem EVT_013_mutant_bootFirstTransition :
    evt013_but2 (evt013_ext (N := Nat) (T := Nat) polJT (evt013_firstBoot polJT) evt013_diagX) refALog ∧
      ¬ EVT_013 (evt013_ext (N := Nat) (T := Nat) polJT (evt013_firstBoot polJT) evt013_diagX) refALog := by
  refine ⟨evt013_ext_but2 (evt013_diagX_ending), fun h => ?_⟩
  have hm : NetEvent.logMessage (some "a") .warn evt013_deadMsg ∈
      (evt013_ext (N := Nat) (T := Nat) polJT (evt013_firstBoot polJT) evt013_diagX).boot
        evt013_cfg evt013_m0 := by
    decide +kernel
  have hu : ∀ a ∈ refDeadArcs evt013_cfg.X.net (fun p => decide (p ∈ evt013_cfg.envs))
      (fun p => (evt013_m0 p).length), a.transition = "u" := by decide +kernel
  rcases (h evt013_cfg).2.1.1 evt013_m0 _ hm rfl with hn | ⟨a, ha, hn⟩
  · exact absurd hn (by decide)
  · simp [NetEvent.trans?, hu a ha] at hn

/-- Transition `v`: takes place 0's token and reads place 1, which `a` feeds, so its read arc is
not dead. -/
def evt013_tV : Trans Nat :=
  { core := { name := "v", inputs := [⟨0, .one⟩], inhibitors := [], reads := [1], resets := [] },
    out := none }

/-- The example with `v` declared after `u`. -/
def evt013_cfgV : Cfg Nat Nat :=
  { evt013_cfg with
    X := { evt013_cfg.X with
           net := { places := [0, 1, 7], transitions := [evt013_tA, evt013_tU, evt013_tV] } } }

/-- ✗ Naming a boot diagnostic after another transition that declares a side arc violates
EVT-013 (line 2): with `v`, which reads place 1, declared after `u`, the only dead arc is still
`u`'s read arc on place 7, but the boot reports it under `v`'s name, the last transition that
declares a read arc. The executor keeps lines 1 and 3. -/
@[evidence mutant EVT_013]
theorem EVT_013_mutant_bootLastSideArc :
    evt013_but2 (evt013_ext (N := Nat) (T := Nat) polJT (evt013_lastSideBoot polJT) evt013_diagX) refALog ∧
      ¬ EVT_013 (evt013_ext (N := Nat) (T := Nat) polJT (evt013_lastSideBoot polJT) evt013_diagX) refALog := by
  refine ⟨evt013_ext_but2 (evt013_diagX_ending), fun h => ?_⟩
  have hm : NetEvent.logMessage (some "v") .warn evt013_deadMsg ∈
      (evt013_ext (N := Nat) (T := Nat) polJT (evt013_lastSideBoot polJT) evt013_diagX).boot
        evt013_cfgV evt013_m0 := by
    decide +kernel
  have hu : ∀ a ∈ refDeadArcs evt013_cfgV.X.net (fun p => decide (p ∈ evt013_cfgV.envs))
      (fun p => (evt013_m0 p).length), a.transition = "u" := by decide +kernel
  rcases (h evt013_cfgV).2.1.1 evt013_m0 _ hm rfl with hn | ⟨a, ha, hn⟩
  · exact absurd hn (by decide)
  · simp [NetEvent.trans?, hu a ha] at hn

/-- ✗ Naming an injection's diagnostic after the last fired transition violates EVT-013
(line 2): while `a`'s action runs, the injection of 5 into the undeclared place 9 reports its
WARN under `a`'s name. The executor keeps lines 1 and 3. -/
@[evidence mutant EVT_013]
theorem EVT_013_mutant_injectLastFired :
    evt013_but2 (evt013_ext (N := Nat) (T := Nat) polJT (evt013_diagBoot polJT) evt013_lastFiredX) refALog ∧
      ¬ EVT_013 (evt013_ext (N := Nat) (T := Nat) polJT (evt013_diagBoot polJT) evt013_lastFiredX) refALog := by
  refine ⟨evt013_ext_but2 (fun C H s l hl => ?_), fun h => ?_⟩
  · rcases hl with rfl | rfl | rfl | ⟨k, rfl⟩ | ⟨p, x, rfl⟩ | ⟨c, rfl⟩ <;> rfl
  · obtain ⟨s, s', evs, hs, hp⟩ := evt013_check
      (xrun evt013_cfg (xinit evt013_m0 0) evt013_toInject) (.inject 1) evt013_lastFiredX
      (fun _ evs => evs.any fun e => e.isLog && !e.namesNone)
      (by decide +kernel)
    simp only [List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hp
    obtain ⟨e, he, hl, hn⟩ := hp
    rw [(h evt013_cfg).2.1.2.1 [] 1 evs s s' hs e he hl] at hn
    cases hn

/-- ✗ Giving a deposit's diagnostic the empty name violates EVT-013 (line 2): the settling of
`a`'s completion deposits 50 into the undeclared place 5 and reports its WARN with the empty name,
not `a`'s. The executor keeps lines 1 and 3. -/
@[evidence mutant EVT_013]
theorem EVT_013_mutant_depositUnnamed :
    evt013_but2 (evt013_ext (N := Nat) (T := Nat) polJT (evt013_diagBoot polJT) evt013_seamCommitX) refALog ∧
      ¬ EVT_013 (evt013_ext (N := Nat) (T := Nat) polJT (evt013_diagBoot polJT) evt013_seamCommitX) refALog := by
  refine ⟨evt013_ext_but2 (fun C H s l hl => ?_), fun h => ?_⟩
  · rcases hl with rfl | rfl | rfl | ⟨k, rfl⟩ | ⟨p, x, rfl⟩ | ⟨c, rfl⟩ <;> rfl
  · obtain ⟨s, s', evs, hs, hp⟩ := evt013_check
      (xrun evt013_cfg (xinit evt013_m0 0) evt013_toCommit) (.commit 0) evt013_seamCommitX
      (fun s evs => (s.fl.find? (·.id == 0)).any fun f =>
        evs.any fun e => e.isLog && e.trans? != some f.t.core.name)
      (by decide +kernel)
    simp only [Option.any_eq_true, List.any_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at hp
    obtain ⟨f, hf, e, he, hl, hn⟩ := hp
    exact hn ((h evt013_cfg).2.1.2.2 [] (.commit 0) 0 evs (Or.inl rfl) s s' hs f hf e he hl)

/-- ✗ A WARN when a run ends closed violates EVT-013 (line 3): the caller closes the executor and
the run's end reports "execution stopped before quiescence (CLOSED)". Its other steps emit as the
reference with diagnostics, so it keeps lines 1 and 2. -/
@[evidence mutant EVT_013]
theorem EVT_013_mutant_warnOnClose :
    evt013_but3 (evt013_ext (N := Nat) (T := Nat) polJT (evt013_diagBoot polJT) evt013_closeWarnX) refALog ∧
      ¬ EVT_013 (evt013_ext (N := Nat) (T := Nat) polJT (evt013_diagBoot polJT) evt013_closeWarnX) refALog := by
  refine ⟨⟨evt013_line1_refALog _, evt013_ext_line2 refALog (evt013_diagBoot_line polJT)
      (fun C H s k e he hl => evt013_diagX_inject C H s k e he hl)
      (fun C H s l i hl f hf e he hlog => by
        rcases hl with rfl | rfl | rfl
        · exact evt013_diagX_deposit C H s _ i (Or.inl rfl) f hf e he hlog
        · exact evt013_diagX_deposit C H s _ i (Or.inr (Or.inl rfl)) f hf e he hlog
        · exact evt013_diagX_deposit C H s _ i (Or.inr (Or.inr rfl)) f hf e he hlog)⟩,
    fun h => ?_⟩
  obtain ⟨s, s', evs, hs, hp⟩ := evt013_check
    (xrun evt013_cfg (xinit evt013_empty 0) evt013_toClose) (.finish .closed) evt013_closeWarnX
    (fun _ evs => evs.any (·.isLog))
    (by decide +kernel)
  simp only [List.any_eq_true] at hp
  obtain ⟨e, he, hl⟩ := hp
  rw [(h evt013_cfg).2.2 [] (.finish .closed) evs (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, rfl⟩)))))
    s s' hs e he] at hl
  cases hl

/-- ✗ A WARN about a refused injection request violates EVT-013 (line 3, the seventh quoted
sentence): once the caller has
closed the executor, a request to inject 5 into the environment place 9 is refused, and the
executor also reports "event refused". Its other steps emit as the reference with diagnostics,
so it keeps lines 1 and 2. -/
@[evidence mutant EVT_013]
theorem EVT_013_mutant_warnOnRefused :
    evt013_but3 (evt013_ext (N := Nat) (T := Nat) polJT (evt013_diagBoot polJT) evt013_refusedWarnX) refALog ∧
      ¬ EVT_013 (evt013_ext (N := Nat) (T := Nat) polJT (evt013_diagBoot polJT) evt013_refusedWarnX) refALog := by
  refine ⟨⟨evt013_line1_refALog _, evt013_ext_line2 refALog (evt013_diagBoot_line polJT)
      (fun C H s k e he hl => evt013_diagX_inject C H s k e he hl)
      (fun C H s l i hl f hf e he hlog => by
        rcases hl with rfl | rfl | rfl
        · exact evt013_diagX_deposit C H s _ i (Or.inl rfl) f hf e he hlog
        · exact evt013_diagX_deposit C H s _ i (Or.inr (Or.inl rfl)) f hf e he hlog
        · exact evt013_diagX_deposit C H s _ i (Or.inr (Or.inr rfl)) f hf e he hlog)⟩,
    fun h => ?_⟩
  obtain ⟨s, s', evs, hs, hp⟩ := evt013_check
    (xrun evt013_cfg (xinit evt013_empty 0) [.close]) (.request 9 5 .refused) evt013_refusedWarnX
    (fun _ evs => evs.any (·.isLog))
    (by decide +kernel)
  simp only [List.any_eq_true] at hp
  obtain ⟨e, he, hl⟩ := hp
  rw [(h evt013_cfg).2.2 [] (.request 9 5 .refused) evs
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨9, 5, rfl⟩))))) s s' hs e he] at hl
  cases hl

end Libpetri.Spec
