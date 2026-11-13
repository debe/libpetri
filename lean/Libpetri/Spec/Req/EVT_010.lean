import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Events
import Libpetri.Spec.Req.EXEC_022
import Libpetri.Spec.Req.EVT_008
import Libpetri.Spec.Req.EVT_009
import Libpetri.Spec.Text.EVT_010

set_option linter.missingDocs true

/-!
# EVT-010: ActionTimedOut Event (`spec/08-events-observability.md`)

When a firing ends with its timeout outcome, because the budget of the `Out.Timeout` node of its
output spec runs out before its action completes ([EXEC-022], [IO-013]), the executor reports it
with one `ActionTimedOut` event naming the firing's transition. The event is not the
`TransitionTimedOut` of a reap at a transition's timing deadline ([EVT-009]).

The runtimes emit it at different moments (`EvPol.atoAtExpire`): Java and TypeScript from the
action's timer, when the budget runs out (the model's outside step `expire i e`); Rust, which
Python also uses, when the executor settles the timeout outcome, by depositing it (`tdeposit i`)
or by failing the firing because the join-relay check of [NU-054] rejects it (`fail i`). The
block holds of both.

The block `EVT_010` is a predicate over an abstract executor with events `E : EvExec N T`
(`Reference/Events.lean`). It reads an event through its kind and the transition name it carries,
which every runtime's event has. It has three lines:

1. the boot of a run emits no `ActionTimedOut`, and a step emits one only if it is the expiry of a
   firing's budget, or a timeout deposit or fail step of a firing that holds a timeout outcome;
   the event names that firing's transition;
2. inside a timeout deposit, no `ActionTimedOut` comes after a `TokenAdded`;
3. on every run from the initial state, a firing has at most one `ActionTimedOut`, and exactly
   one once the run settles it after it ended with its timeout outcome.

The witness is the reference executor with events `refEvExec` under both emission variants. The
wrong executors step as the reference and emit otherwise: one that reports a reap as an
`ActionTimedOut`, one that reports a committed completion as timed out too, one that reports an
action's own error as a timeout, one that names no transition, one that reports every transition
at boot, one that reports the timeout after depositing its outcome, one that reports it twice
(at the expiry and at the deposit), and one that never reports it.

The worked example is `EVT-008`'s (`evt008_cfg`): transition `t` takes 7 and 8 from place 0, and
its output spec is "a token in place 1, or, if the action's budget runs out, the two inputs
forwarded to place 2". `t` starts asynchronously, its budget runs out, and the next completion
phase deposits 7 and 8 in place 2.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## Vocabulary -/

section Vocabulary

variable {N T : Type}

/-- The firing a step label ends or settles: `i` for the expiry of `i`'s budget (`expire i e`),
the deposit of its timeout outcome (`tdeposit i`) and a fail step of `i` (`fail i`); no firing for
every other label. -/
def evt010_lblId : XLbl N T → Option Nat
  | .expire i _ => some i
  | .tdeposit i => some i
  | .fail i => some i
  | _ => none

/-- The label is the expiry of a firing's budget (`expire i e`). -/
def evt010_isExpire : XLbl N T → Bool
  | .expire _ _ => true
  | _ => false

/-- No `ActionTimedOut` event of `evs` comes after a `TokenAdded` event of `evs`: however `evs` is
cut into `a`, an `ActionTimedOut` event, and `b`, no event of `a` is a `TokenAdded`. -/
def evt010_AtoFirst (evs : List (NetEvent N T)) : Prop :=
  ∀ a e b, evs = a ++ e :: b → e.kind = .actionTimedOut → ∀ e' ∈ a, e'.kind ≠ .tokenAdded

/-- The `ActionTimedOut` events of firing `i` in one step: those of a step labelled with `i`
(`evt010_lblId`), none for any other step. -/
def evt010_atoAt (i : Nat) (l : XLbl N T) (evs : List (NetEvent N T)) : Nat :=
  if evt010_lblId l = some i then kindCount .actionTimedOut evs else 0

/-- **The `ActionTimedOut` events of firing `i` along a labelled run**: the sum of
`evt010_atoAt i` over its steps. -/
def evt010_atoOf (i : Nat) (run : List (EvStep N T)) : Nat :=
  (run.map fun st => evt010_atoAt i st.lbl st.evs).sum

variable [DecidableEq N] [Ord N]
/-- The step settles firing `i` after `i` ended with its timeout outcome: it is a `tdeposit i` or
a `fail i` step, and the firing with identity `i` in flight in its source state holds a timeout
outcome. -/
def evt010_settlesTimeout (i : Nat) (st : EvStep N T) : Bool :=
  match st.lbl with
  | .tdeposit j | .fail j => j == i && (st.src.fl.find? (·.id == i)).any isTimeoutOut
  | _ => false

end Vocabulary

/-! ## EVT-010: one event per timed-out firing, at its expiry or its settle -/

requirement EVT_010
  id "EVT-010"
  title "ActionTimedOut Event"
  kind B
  scope "all executors (event store enabled)"
  source verbatim "spec/08-events-observability.md"
  covers EVT_010.s1, EVT_010.s2, EVT_010.s3
  reading "For every executor with events E and every configuration C:"
          "the events a run emits before its first step contain no ActionTimedOut event, whatever the initial marking; and for every history H, every ActionTimedOut event that a step labelled l from state s appends names the transition of a firing f in flight in s whose identity i is the one the label carries (an expiry expire i e, a timeout deposit tdeposit i or a fail step fail i), and the step is the expiry of that firing's budget or f holds a timeout outcome;"
          "for every history H, the events a timeout deposit tdeposit i appends have no ActionTimedOut event after a TokenAdded event;"
          "for every labelled run of E from the initial state of any marking M0 at any reading r0, and every firing identity i, the steps labelled with i append at most one ActionTimedOut event in all, and exactly one if some step of the run is a tdeposit i or fail i step from a state in which the firing with identity i holds a timeout outcome."
  assumes "The model is an executor with events E : EvExec N T (Reference/Events.lean): the events a run emits before its first step, and a step relation E.step C H s l evs s' saying that the step labelled l leads from s to s' and appends the events evs, given the events H emitted before it; a labelled run (LRun) chains such steps from the initial state xinit M0 r0. The witness is the reference executor with events refEvExec, the reference executor RefExec with its emission refEmitW, under both emission variants (polJT for Java and TypeScript, polRust for Rust and Python). refEvExec_erase (Reference/EventsLink.lean) shows that it steps exactly as RefExec, so the block constrains what is emitted and nothing else."
          "Naming. A firing ends with its timeout outcome at the model's outside step expire i e, the budget of an asynchronous firing whose output spec has a Timeout node running out before its action reported (EXEC-022 line 1; ruling D18 (b): the budget is host time, so the expiry is a free outside step). The executor then settles the firing in step 1: a tdeposit step deposits the timeout outcome, or, when the join-relay check of NU-054 rejects it, a fail step deposits nothing (ruling D24 (a)). 'Settles a firing that ended with its timeout outcome' is a tdeposit or fail step from a state in which the firing holds a timeout outcome (isTimeoutOut). A firing whose flushed batch the join-relay check already rejected ends with an error at its expiry, not with its timeout outcome (EXEC-022 line 2), so it is settled by a fail step that carries no ActionTimedOut (line 1 forbids it there); Java and TypeScript have no mid-action publication, so in those runtimes no firing is in that case. Rust: handle_completion appends ActionTimedOut when the completion carries timed_out, before the relay check and the deposit (rust/libpetri-runtime/src/executor_core/executor.rs); the select! of the task fire_transition_async spawns sets timed_out, and an error taken from the FlushGate's relay_error replaces the result. Java: withActionTimeout runs the onTimeout callback, which emits the event, after the timeout branch is produced (ExecutorSupport.withActionTimeout, called with that callback from fireTransition in BitmapNetExecutor.java and PrecompiledNetExecutor.java, java/src/main/java/org/libpetri/runtime). TypeScript: the catch of the race against the TimeoutSentinel emits it (fireTransition in typescript/src/runtime/bitmap-net-executor.ts and precompiled-net-executor.ts)."
          "Line 1 is the first quoted sentence. The boot of a run emits no ActionTimedOut (EVT_010_mutant_bootTimedOut breaks it). A step emits one only as the expiry of a firing's budget or as a settle of a firing holding a timeout outcome: an executor that reports a reap as an ActionTimedOut breaks it (EVT_010_mutant_reapAsActionTimedOut; the reap's own event is TransitionTimedOut, EVT-009), so does one that reports a committed completion as timed out (EVT_010_mutant_completedAndTimedOut), and so does one that reports the action's own error as a timeout (EVT_010_mutant_actionErrorAsTimeout: IO-013 AC6, a TimeoutException the action raises is an action failure, outcome err). The event names the firing's transition: EVT_010_mutant_anonymous names the empty string. The event carries no firing identity, so line 1 attributes it through the step label, and line 3 counts per identity on that attribution."
          "Line 2 is the second quoted sentence, read inside the step that deposits the outcome. Rust emits the event first and then the TokenAdded events of the outcome (handle_completion in executor_core/executor.rs appends it before the deposit loop); EVT_010_mutant_afterDeposit emits it after them. Java and TypeScript emit the event in the expiry step, which comes before the deposit step: only the expiry records a timeout outcome (EXEC-022 line 5), and a tdeposit needs a recorded one (EXEC-022 line 3), so their deposit steps carry no ActionTimedOut and line 2 holds of them trivially. Read across steps on such an executor, the sentence follows from line 1 together with EXEC-022 on the executor underneath (E.erase); it is not a further line here. The block reads the timeout outcome off E's state (isTimeoutOut): an executor that records the timeout branch as a returned emission (outcome ok), so that it reports TransitionCompleted and never an ActionTimedOut, meets the lines of this block, and it is EXEC-022 line 2 on E.erase that rejects it. Such a slip is the short form of Java's withActionTimeout without its TIMEOUT_SENTINEL check (java/src/main/java/org/libpetri/runtime/ExecutorSupport.java), or a Rust select! arm that builds its completion with timed_out None; the consistency theorem's conjunct on E.erase is what excludes it."
          "Line 3 is the third quoted sentence. It reads labelled runs from the initial state, where no firing is in flight and every identity is still to be handed out (XSt.nextId), so that 'each firing' is 'each identity' (EXEC-031; the reference keeps IdsIssued, exec022_idsIssued_step). At most one: EVT_010_mutant_reportedTwice reports the timeout at the expiry and again at the deposit. Exactly one once the outcome is settled: EVT_010_mutant_silentTimeout never reports it. 'No later than when it settles' allows both runtimes' moments: in the reference the Java and TypeScript event is in the expiry step, before the settle (evt010_runLB), the Rust event in the settle step. The line does not require the event for a firing whose timeout outcome is never settled in the run (a run that stops before step 1 settles it); that a recorded timeout outcome is settled at all is coverage, the second clause of Exec022Covers in the consistency theorem's ExecCoversW5 (ConsistencyExec.lean)."
          "Not claimed (ruling D65 (a), the weak form). That every ActionTimedOut is followed by the deposit of the timeout outcome: it is not after a join-relay rejection (Rust: ActionTimedOut, then TransitionFailed), nor, in Java and TypeScript, after a firing the run abandoned at a terminal stop (EXEC-042), whose timer still emits the event, also after ExecutionCompleted (clash evt-b#9, R7: Java and TypeScript emit from the timer with no check that the run is still live; EVT-003 leaves ActionTimedOut out of the orchestrator events it orders). Whether TransitionCompleted follows the event: Java and TypeScript emit it after depositing the timeout branch, Rust does not (clash evt-a#7, R2); that is EVT-007's, which allows both. The budget's duration and when the budget runs out are host time under ruling D18 (b), outside the model (EXEC-022's test-only point), so the block has no time clause: it is keyed on the expiry step, not on a clock."
          "The payload sentence 'Each ActionTimedOut event shall carry the duration of the `Timeout` node of the firing's output spec.' is the companion block EVT_010_payload in this file (rulings D33 (a) and D38 (a): payload fields are companion blocks). The model's event carries the transition name only (NetEvent.actionTimedOut, GlossaryEvents.lean) and its output spec has no durations (Out.timeout), so that block takes the Timeout durations as data and models the duration field as its own (Evt010DurExec); all three runtimes carry the field, the Timeout node's after duration. The timestamp, which the executor's epoch clock stamps (TIME-015), is not modelled (the epoch clock is the CORE-011 slice)."
          "AC1 (emitted for a firing whose action's Out.Timeout budget runs out before the action completes, and never for a transition reaped at its timing deadline) is lines 1 and 3: the event comes only from the expiry or the settle of a timed-out firing, never from a deadline step, and every settled timeout outcome has its event (EVT_010_nonvacuous; EVT_010_mutant_reapAsActionTimedOut). AC2 (the TokenAdded events of the timeout branch come after this event) is line 2 in the deposit step, and, for Java and TypeScript, the order of the expiry and the deposit steps (line 2 above)."
          "Assumptions shared by the executor event blocks: the event store is enabled and its append does not fail (EVT-020); no host callback throws inside a start or a deposit; an event is a value (EVT-001); transition names are distinct (ruling D10). IO-013 AC4 (an ActionTimedOut event is emitted on timeout) is this requirement's subject; the IO_013 block defers it here (clash evt-b#7, SC-10, ruling D20). The events of one step are contiguous in the model, since a step appends its events at once. Java appends ActionTimedOut events and the log messages it captures from actions from other threads than the orchestrator (the timeout callback BitmapNetExecutor.fireTransition hands java/src/main/java/org/libpetri/runtime/ExecutorSupport.java withActionTimeout, which appends through emitEvent from the timer thread; LogCaptureScope.java wrapRunnable and wrapCallable), so in a Java store such an event can fall between the events of one step; the lines are read on the store with those events left out, as the reading at the top of spec/08-events-observability.md says. TypeScript and Rust append every event from the orchestrator."
          "The test derivation (an action sleeps 500 ms with Out.Timeout at 100 ms, verify the ActionTimedOut event) is EVT_010_nonvacuous on the example, with the budget's expiry a step: under the Java and TypeScript emission the expiry of t's budget emits ActionTimedOut t and the deposit of 7 and 8 in place 2 emits none; under the Rust emission the deposit emits ActionTimedOut t and then the two TokenAdded events; on the whole run from the initial state firing 0 has exactly one ActionTimedOut under each emission."
  signoff "2026-11-13 62f3150f8891e0e3 ai"
  statement : ∀ {N T : Type} [DecidableEq N], EvExec N T → Prop :=
    fun E => ∀ C,
      ((∀ M0, ∀ e ∈ E.boot C M0, e.kind ≠ .actionTimedOut) ∧
        ∀ H l evs, on (fun s s' => E.step C H s l evs s'), shall (fun s _ =>
          ∀ e ∈ evs, e.kind = .actionTimedOut →
            ∃ i, evt010_lblId l = some i ∧ ∃ f ∈ s.fl, f.id = i ∧
              e.trans? = some f.t.core.name ∧
              (evt010_isExpire l = true ∨ isTimeoutOut f = true))) ∧
      (∀ H i evs, on (fun s s' => E.step C H s (.tdeposit i) evs s'), shall (fun _ _ =>
          evt010_AtoFirst evs)) ∧
      (∀ M0 r0 run, LRun E C (E.boot C M0) (xinit M0 r0) run → ∀ i,
          evt010_atoOf i run ≤ 1 ∧
            (run.any (evt010_settlesTimeout i) = true → evt010_atoOf i run = 1))

/- The pinned readable form of EVT-010: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EVT_010 : {N T : Type} → [DecidableEq N] → EvExec N T → Prop :=
fun {N T} [DecidableEq N] E =>
  ∀ (C : Cfg N T),
    ((∀ (M0 : QMarking N T), ∀ e ∈ E.boot C M0, e.kind ≠ NetEventKind.actionTimedOut) ∧
        ∀ (H : List (NetEvent N T)) (l : XLbl N T) (evs : List (NetEvent N T)),
          on fun s s' => E.step C H s l evs s', shall fun s x =>
            ∀ e ∈ evs,
              e.kind = NetEventKind.actionTimedOut →
                ∃ i,
                  evt010_lblId l = some i ∧
                    ∃ f ∈ s.fl,
                      f.id = i ∧ e.trans? = some f.t.core.name ∧ (evt010_isExpire l = true ∨ isTimeoutOut f = true)) ∧
      (∀ (H : List (NetEvent N T)) (i : ℕ) (evs : List (NetEvent N T)),
          on fun s s' => E.step C H s (XLbl.tdeposit i) evs s', shall fun x x_1 => evt010_AtoFirst evs) ∧
        ∀ (M0 : QMarking N T) (r0 : ℕ) (run : List (EvStep N T)),
          LRun E C (E.boot C M0) (xinit M0 r0) run →
            ∀ (i : ℕ), evt010_atoOf i run ≤ 1 ∧ (run.any (evt010_settlesTimeout i) = true → evt010_atoOf i run = 1)
-/
#guard_msgs in #print EVT_010

/-! ## The three lines, one at a time -/

section Lines

variable {N T : Type} [DecidableEq N] [Ord N]
/-- Line 1 of `EVT_010` alone: the boot emits no `ActionTimedOut`, and every `ActionTimedOut` a
step emits belongs to the firing its label names, names that firing's transition, and comes from
the expiry of its budget or from a settle of a firing that holds a timeout outcome. -/
def evt010_line1 (E : EvExec N T) : Prop :=
  ∀ C, (∀ M0, ∀ e ∈ E.boot C M0, e.kind ≠ .actionTimedOut) ∧
    ∀ H l evs, on (fun s s' => E.step C H s l evs s'), shall (fun s _ =>
      ∀ e ∈ evs, e.kind = .actionTimedOut →
        ∃ i, evt010_lblId l = some i ∧ ∃ f ∈ s.fl, f.id = i ∧
          e.trans? = some f.t.core.name ∧
          (evt010_isExpire l = true ∨ isTimeoutOut f = true))

/-- Line 2 of `EVT_010` alone: inside a timeout deposit no `ActionTimedOut` comes after a
`TokenAdded`. -/
def evt010_line2 (E : EvExec N T) : Prop :=
  ∀ C H i evs, on (fun s s' => E.step C H s (.tdeposit i) evs s'), shall (fun _ _ =>
    evt010_AtoFirst evs)

/-- Line 3 of `EVT_010` alone: on a run from the initial state, a firing has at most one
`ActionTimedOut`, and exactly one once the run settles it after it ended with its timeout
outcome. -/
def evt010_line3 (E : EvExec N T) : Prop :=
  ∀ C M0 r0 run, LRun E C (E.boot C M0) (xinit M0 r0) run → ∀ i,
    evt010_atoOf i run ≤ 1 ∧
      (run.any (evt010_settlesTimeout i) = true → evt010_atoOf i run = 1)

/-- Lines 2 and 3 of `EVT_010`: every line but line 1. -/
abbrev evt010_keeps23 (E : EvExec N T) : Prop := evt010_line2 E ∧ evt010_line3 E

/-- Lines 1 and 3 of `EVT_010`: every line but line 2. -/
abbrev evt010_keeps13 (E : EvExec N T) : Prop := evt010_line1 E ∧ evt010_line3 E

/-- Lines 1 and 2 of `EVT_010`: every line but line 3. -/
abbrev evt010_keeps12 (E : EvExec N T) : Prop := evt010_line1 E ∧ evt010_line2 E

omit [Ord N] in
/-- `EVT_010` is its three lines. -/
theorem evt010_iff (E : EvExec N T) :
    EVT_010 E ↔ evt010_line1 E ∧ evt010_line2 E ∧ evt010_line3 E :=
  ⟨fun h => ⟨fun C => (h C).1, fun C => (h C).2.1, fun C => (h C).2.2⟩,
   fun h C => ⟨h.1 C, h.2.1 C, h.2.2 C⟩⟩

end Lines

/-! ## The reference -/

section Reference

variable {N T : Type} [DecidableEq N] [Ord N]
omit [DecidableEq N] [Ord N] in
/-- `isTimeoutOut` says that the firing holds a timeout outcome. -/
theorem evt010_isTimeoutOut_iff {f : Firing N T} :
    isTimeoutOut f = true ↔ ∃ e, f.out = some (.timedOut e) := by
  unfold isTimeoutOut
  cases h : f.out with
  | none => simp
  | some o => cases o <;> simp

/-- **Where the reference emits `ActionTimedOut`**: only in a step of a firing `i` in flight (an
expiry, a timeout deposit or a fail step), naming its transition; under the Java and TypeScript
emission at the expiry, under the Rust emission at a settle of a firing that holds a timeout
outcome. -/
theorem evt010_refAto (P : EvPol) (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T)
    (l : XLbl N T) (s' : XSt N T) :
    ∀ e ∈ refEmitW P C H s l s', e.kind = .actionTimedOut →
      ∃ i f, evt010_lblId l = some i ∧ s.fl.find? (·.id == i) = some f ∧
        e = .actionTimedOut f.t.core.name ∧
        ((P.atoAtExpire = true ∧ evt010_isExpire l = true) ∨
          (P.atoAtExpire = false ∧ evt010_isExpire l = false ∧ isTimeoutOut f = true)) := by
  intro e he hk
  have hkind := refEmitW_kind P C H s l s' e he
  rw [hk] at hkind
  cases l with
  | expire i e' =>
    cases hP : P.atoAtExpire
    · simp [refEmitW, hP] at he
    · cases hf : s.fl.find? (·.id == i) with
      | none => simp [refEmitW, hP, hf] at he
      | some f =>
        simp only [refEmitW, hP, hf, if_true, List.mem_singleton] at he
        exact ⟨i, f, rfl, hf, he, Or.inl ⟨rfl, rfl⟩⟩
  | tdeposit i =>
    cases hf : s.fl.find? (·.id == i) with
    | none => simp [refEmitW, hf] at he
    | some f =>
      cases ho : f.out with
      | none => simp [refEmitW, hf, ho] at he
      | some o =>
        cases o with
        | ok e0 => simp [refEmitW, hf, ho] at he
        | err => simp [refEmitW, hf, ho] at he
        | timedOut e0 =>
          simp only [refEmitW, hf, ho, List.mem_append] at he
          rcases he with (h | h) | h
          · cases hP : P.atoAtExpire
            · simp only [hP, Bool.false_eq_true, if_false, List.mem_singleton] at h
              exact ⟨i, f, rfl, hf, h, Or.inr ⟨rfl, rfl, by simp [isTimeoutOut, ho]⟩⟩
            · simp [hP] at h
          · rw [kind_of_mem_addedEvs h] at hk; cases hk
          · split at h
            · simp only [List.mem_singleton] at h; subst h; cases hk
            · cases h
  | fail i =>
    cases hf : s.fl.find? (·.id == i) with
    | none => simp [refEmitW, hf] at he
    | some f =>
      simp only [refEmitW, hf, List.mem_append, List.mem_singleton] at he
      rcases he with h | rfl
      · split at h
        · rename_i hc
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
          simp only [List.mem_singleton] at h
          exact ⟨i, f, rfl, hf, h, Or.inr ⟨hc.1, rfl, hc.2⟩⟩
        · cases h
      · cases hk
  | _ => simp [lblKinds] at hkind

/-- The reference boot emits no `ActionTimedOut`. -/
theorem evt010_refBoot (P : EvPol) (C : Cfg N T) (M0 : QMarking N T) :
    ∀ e ∈ refBoot P C M0, e.kind ≠ .actionTimedOut := by
  intro e he hk
  rcases refBoot_kind P C M0 e he with h | h <;> rw [hk] at h <;> cases h

/-- Line 1 holds of every executor that steps as the reference and whose `ActionTimedOut`
events are each one the reference emits in the same step, under one of the two emission
variants. -/
theorem evt010_line1_of {boot : Cfg N T → QMarking N T → List (NetEvent N T)}
    {emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    (hb : ∀ C M0, ∀ e ∈ boot C M0, e.kind ≠ .actionTimedOut)
    (he : ∀ C H s l s', xstep C s l = some s' → ∀ e ∈ emit C H s l s',
      e.kind = .actionTimedOut → ∃ P, e ∈ refEmitW P C H s l s') :
    evt010_line1 (emitExec boot emit) := by
  intro C
  refine ⟨hb C, fun H l evs s s' hs e hm hk => ?_⟩
  obtain ⟨hx, rfl⟩ := hs
  obtain ⟨P, hP⟩ := he C H s l s' hx e hm hk
  obtain ⟨i, f, hl, hf, rfl, hc⟩ := evt010_refAto P C H s l s' e hP hk
  refine ⟨i, hl, f, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, rfl, ?_⟩
  rcases hc with ⟨-, h⟩ | ⟨-, -, h⟩
  · exact Or.inl h
  · exact Or.inr h

omit [DecidableEq N] [Ord N] in
/-- A list whose events before a cut are no `TokenAdded`, and whose events after it are no
`ActionTimedOut`, has its `ActionTimedOut` events first. -/
theorem evt010_atoFirst_append {pre rest : List (NetEvent N T)}
    (hpre : ∀ x ∈ pre, x.kind ≠ .tokenAdded) (hrest : ∀ x ∈ rest, x.kind ≠ .actionTimedOut) :
    evt010_AtoFirst (pre ++ rest) := by
  intro a e b h hk e' he'
  rcases List.append_eq_append_iff.1 h.symm with ⟨a', rfl, h2⟩ | ⟨c', rfl, h2⟩
  · exact hpre e' (List.mem_append_left _ he')
  · exact absurd hk (hrest e (by rw [h2]; simp))

/-- The events of a reference timeout deposit have their `ActionTimedOut` first. -/
theorem evt010_refTdeposit (P : EvPol) (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T)
    (i : Nat) (s' : XSt N T) : evt010_AtoFirst (refEmitW P C H s (.tdeposit i) s') := by
  have none : evt010_AtoFirst ([] : List (NetEvent N T)) :=
    evt010_atoFirst_append (pre := []) (rest := []) (by simp) (by simp)
  cases hf : s.fl.find? (·.id == i) with
  | none => simpa [refEmitW, hf] using none
  | some f =>
    cases ho : f.out with
    | none => simpa [refEmitW, hf, ho] using none
    | some o =>
      cases o with
      | ok e0 => simpa [refEmitW, hf, ho] using none
      | err => simpa [refEmitW, hf, ho] using none
      | timedOut e0 =>
        simp only [refEmitW, hf, ho, List.append_assoc]
        refine evt010_atoFirst_append ?_ ?_
        · intro x hx
          split at hx
          · cases hx
          · simp only [List.mem_singleton] at hx; subst hx; simp [NetEvent.kind]
        · intro x hx hk
          rcases List.mem_append.1 hx with h | h
          · rw [kind_of_mem_addedEvs h] at hk; cases hk
          · split at h
            · simp only [List.mem_singleton] at h; subst h; cases hk
            · cases h

omit [Ord N] in
/-- Line 2 holds of every executor that steps as the reference and emits, at a timeout deposit,
events whose `ActionTimedOut` come first. -/
theorem evt010_line2_of {boot : Cfg N T → QMarking N T → List (NetEvent N T)}
    {emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    (he : ∀ C H s i s', xstep C s (.tdeposit i) = some s' →
      evt010_AtoFirst (emit C H s (.tdeposit i) s')) :
    evt010_line2 (emitExec boot emit) := by
  intro C H i evs s s' hs
  obtain ⟨hx, rfl⟩ := hs
  exact he C H s i s' hx

/-! ### Counting the `ActionTimedOut` events of one firing along a run -/

omit [DecidableEq N] [Ord N] in
/-- The `ActionTimedOut` events of a step labelled with firing `i` are all its `ActionTimedOut`
events. -/
theorem evt010_atoAt_of {i : Nat} {l : XLbl N T} (h : evt010_lblId l = some i)
    (evs : List (NetEvent N T)) : evt010_atoAt i l evs = kindCount .actionTimedOut evs :=
  if_pos h

/-- A reference expiry emits one `ActionTimedOut` under the Java and TypeScript emission, none
under the Rust emission. -/
theorem evt010_refCount_expire (P : EvPol) (C : Cfg N T) (H : List (NetEvent N T))
    {s s' : XSt N T} {i : Nat} {e : List (N × T)} (hx : xstep C s (.expire i e) = some s') :
    kindCount .actionTimedOut (refEmitW P C H s (.expire i e) s') =
      if P.atoAtExpire then 1 else 0 := by
  obtain ⟨f, hf, -⟩ := expireStep_some hx
  cases hP : P.atoAtExpire <;> simp [refEmitW, hP, hf, kindCount, NetEvent.kind]

/-- A reference timeout deposit emits one `ActionTimedOut` under the Rust emission, none under
the Java and TypeScript emission. -/
theorem evt010_refCount_tdeposit (P : EvPol) (C : Cfg N T) (H : List (NetEvent N T))
    {s s' : XSt N T} {i : Nat} (hx : xstep C s (.tdeposit i) = some s') :
    kindCount .actionTimedOut (refEmitW P C H s (.tdeposit i) s') =
      if P.atoAtExpire then 0 else 1 := by
  obtain ⟨f, e, hf, ho, -⟩ := tdepositStep_some hx
  cases hP : P.atoAtExpire <;> cases hQ : P.completedAfterTimeout <;>
    simp [refEmitW, hf, ho, hP, hQ, kindCount, addedEvs, List.countP_append, List.countP_map,
      Function.comp_def, NetEvent.kind]

/-- A reference fail step emits one `ActionTimedOut` under the Rust emission when the failed
firing holds a timeout outcome, and none otherwise. -/
theorem evt010_refCount_fail (P : EvPol) (C : Cfg N T) (H : List (NetEvent N T))
    {s : XSt N T} {i : Nat} {f : Firing N T} (hf : s.fl.find? (·.id == i) = some f)
    (s' : XSt N T) :
    kindCount .actionTimedOut (refEmitW P C H s (.fail i) s') =
      if !P.atoAtExpire && isTimeoutOut f then 1 else 0 := by
  rw [refEmitW_fail P C H hf s']
  split <;> simp [kindCount, NetEvent.kind]

/-- **Firing `i` has had its `ActionTimedOut`** in the reference under emission variant `P`, and
can have no other: the identity `i` was handed out, and, under the Java and TypeScript emission,
every firing `i` in flight has its outcome set (its budget can no longer expire), under the Rust
emission no firing `i` is in flight (it can no longer be settled). -/
def evt010_Spent (P : EvPol) (i : Nat) (s : XSt N T) : Prop :=
  exec022_Closed (fun _ => P.atoAtExpire = true) i s

/-- **One reference step, for firing `i`**: it emits at most one `ActionTimedOut` of `i`, none
once `i` has had its event, and after one `i` has had its event. -/
theorem evt010_stepUB (P : EvPol) {C : Cfg N T} (H : List (NetEvent N T)) {s s' : XSt N T}
    {l : XLbl N T} (i : Nat) (hx : xstep C s l = some s') (hs : IdsIssued s) :
    evt010_atoAt i l (refEmitW P C H s l s') ≤ 1 ∧
      (evt010_Spent P i s → evt010_atoAt i l (refEmitW P C H s l s') = 0) ∧
      (evt010_atoAt i l (refEmitW P C H s l s') ≠ 0 → evt010_Spent P i s') := by
  unfold evt010_atoAt
  split
  · rename_i hl
    cases l with
    | expire j e =>
      simp only [evt010_lblId, Option.some.injEq] at hl
      subst hl
      rw [evt010_refCount_expire P C H hx]
      obtain ⟨f, hf, ho, -, -, -, hs'⟩ := expireStep_some hx
      cases hP : P.atoAtExpire
      · simp
      · simp only [if_true]
        refine ⟨le_refl _, fun hb => absurd ho (exec022_closed_set hb hf), fun _ => ?_⟩
        subst hs'
        exact exec022_closed_set_by (Q := fun _ => P.atoAtExpire = true)
          (h := fun g => { g with out := some (if g.relayBad then .err else .timedOut e) })
          hs hf (fun g => ⟨_, rfl, hP⟩) rfl rfl
    | tdeposit j =>
      simp only [evt010_lblId, Option.some.injEq] at hl
      subst hl
      rw [evt010_refCount_tdeposit P C H hx]
      obtain ⟨f, e, hf, -, -, -, -⟩ := tdepositStep_some hx
      cases hP : P.atoAtExpire
      · simp only [Bool.false_eq_true, if_false]
        refine ⟨le_refl _, fun hb => ?_, fun _ => ?_⟩
        · obtain ⟨-, -, hF⟩ := exec022_closed_out hb hf
          rw [hP] at hF
          cases hF
        · have hc := exec022_closed_tdeposit hx hs
          exact ⟨hc.1, fun g hg hid => by obtain ⟨-, -, hF⟩ := hc.2 g hg hid; exact hF.elim⟩
      · simp
    | fail j =>
      simp only [evt010_lblId, Option.some.injEq] at hl
      subst hl
      obtain ⟨f, hf, -, -, hs'⟩ := failStep_some (P := refXPol) hx
      rw [evt010_refCount_fail P C H hf]
      cases hP : P.atoAtExpire
      · refine ⟨by split <;> simp, fun hb => ?_, fun _ => ?_⟩
        · obtain ⟨-, -, hF⟩ := exec022_closed_out hb hf
          rw [hP] at hF
          cases hF
        · subst hs'
          have hid : f.id = j := by simpa using List.find?_some hf
          exact ⟨hid ▸ hs f (List.mem_of_find?_eq_some hf),
            fun g hg hgi => absurd hgi (exec022_mem_settle (s := s) (i := j) hg).2⟩
      · simp
    | _ => simp [evt010_lblId] at hl
  · simp

/-- The emission `emit` emits, at every step of a firing (an expiry, a timeout deposit, a fail
step), as many `ActionTimedOut` events as the reference under variant `P`. -/
def evt010_AgreesAto (P : EvPol)
    (emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)) :
    Prop :=
  ∀ C H s l s', xstep C s l = some s' → evt010_lblId l ≠ none →
    kindCount .actionTimedOut (emit C H s l s') = kindCount .actionTimedOut (refEmitW P C H s l s')

/-- An emission that agrees with the reference on the count of a firing's steps counts the same
`ActionTimedOut` events of firing `i` in every step. -/
theorem evt010_atoAt_agree {P : EvPol}
    {emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    (hag : evt010_AgreesAto P emit) {C : Cfg N T} {H : List (NetEvent N T)} {s s' : XSt N T}
    {l : XLbl N T} (i : Nat) (hx : xstep C s l = some s') :
    evt010_atoAt i l (emit C H s l s') = evt010_atoAt i l (refEmitW P C H s l s') := by
  unfold evt010_atoAt
  split
  · rename_i hl
    exact hag C H s l s' hx (by rw [hl]; simp)
  · rfl

omit [DecidableEq N] [Ord N] in
/-- The count along a run, one step at a time. -/
theorem evt010_atoOf_cons (i : Nat) (st : EvStep N T) (rest : List (EvStep N T)) :
    evt010_atoOf i (st :: rest) = evt010_atoAt i st.lbl st.evs + evt010_atoOf i rest := by
  simp [evt010_atoOf]

/-- **At most one, along a run**: on a run of an executor that steps as the reference and counts
a firing's events as the reference does, from a state whose identities were handed out, a firing
has at most one `ActionTimedOut`, and none once it has had its event. -/
theorem evt010_runUB (P : EvPol) {boot : Cfg N T → QMarking N T → List (NetEvent N T)}
    {emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    (hag : evt010_AgreesAto P emit) {C : Cfg N T} (i : Nat) :
    ∀ {H : List (NetEvent N T)} {s : XSt N T} {run : List (EvStep N T)},
      LRun (emitExec boot emit) C H s run → IdsIssued s →
        evt010_atoOf i run ≤ 1 ∧ (evt010_Spent P i s → evt010_atoOf i run = 0)
  | _, _, [], _, _ => ⟨Nat.zero_le _, fun _ => rfl⟩
  | H, s, st :: rest, hr, hs => by
    obtain ⟨h1, ⟨hx, hev⟩, hr'⟩ := hr
    subst h1
    obtain ⟨ih1, ih2⟩ := evt010_runUB P hag i hr' (exec022_idsIssued_step hx hs)
    obtain ⟨u1, u2, u3⟩ := evt010_stepUB P H i hx hs
    rw [evt010_atoOf_cons, hev, evt010_atoAt_agree hag i hx]
    by_cases h0 : evt010_atoAt i st.lbl (refEmitW P C H st.src st.lbl st.dst) = 0
    · rw [h0]
      exact ⟨by omega, fun hb => by rw [ih2 (exec022_closed_step hx hb)]⟩
    · rw [ih2 (u3 h0)]
      exact ⟨by omega, fun hb => absurd (u2 hb) h0⟩

/-- **At least one, along a run**: on a run of an executor that steps as the reference and
counts a firing's events as the reference does, that settles firing `i` after it ended with its
timeout outcome, firing `i` has an `ActionTimedOut`, counting `c` events already emitted, which
under the Java and TypeScript emission is at least one if a firing `i` already holds a timeout
outcome. -/
theorem evt010_runLB (P : EvPol) {boot : Cfg N T → QMarking N T → List (NetEvent N T)}
    {emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    (hag : evt010_AgreesAto P emit) {C : Cfg N T} (i : Nat) :
    ∀ {H : List (NetEvent N T)} {s : XSt N T} {run : List (EvStep N T)} (c : Nat),
      LRun (emitExec boot emit) C H s run →
      (P.atoAtExpire = true → (∃ f ∈ s.fl, f.id = i ∧ isTimeoutOut f = true) → 1 ≤ c) →
      run.any (evt010_settlesTimeout i) = true → 1 ≤ c + evt010_atoOf i run
  | _, _, [], _, _, _, hany => by simp at hany
  | H, s, st :: rest, c, hr, hc, hany => by
    obtain ⟨h1, ⟨hx, hev⟩, hr'⟩ := hr
    subst h1
    rw [evt010_atoOf_cons, hev, evt010_atoAt_agree hag i hx]
    by_cases hst : evt010_settlesTimeout i st = true
    · unfold evt010_settlesTimeout at hst
      cases hl : st.lbl with
      | tdeposit j =>
        rw [hl] at hst hx
        simp only [Bool.and_eq_true, beq_iff_eq, Option.any_eq_true] at hst
        obtain ⟨rfl, f, hf, ht⟩ := hst
        cases hP : P.atoAtExpire
        · rw [evt010_atoAt_of rfl, evt010_refCount_tdeposit P C H hx, hP]
          simp only [Bool.false_eq_true, if_false]
          omega
        · have := hc hP ⟨f, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, ht⟩
          omega
      | fail j =>
        rw [hl] at hst hx
        simp only [Bool.and_eq_true, beq_iff_eq, Option.any_eq_true] at hst
        obtain ⟨rfl, f, hf, ht⟩ := hst
        cases hP : P.atoAtExpire
        · rw [evt010_atoAt_of rfl, evt010_refCount_fail P C H hf, hP, ht]
          simp only [Bool.not_false, Bool.and_self, if_true]
          omega
        · have := hc hP ⟨f, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, ht⟩
          omega
      | _ => rw [hl] at hst; simp at hst
    · have hany' : rest.any (evt010_settlesTimeout i) = true := by
        simpa [List.any_cons, hst] using hany
      have hc' : P.atoAtExpire = true →
          (∃ f ∈ st.dst.fl, f.id = i ∧ isTimeoutOut f = true) →
          1 ≤ c + evt010_atoAt i st.lbl (refEmitW P C H st.src st.lbl st.dst) := by
        intro hP ⟨f', hf', hid, ht⟩
        obtain ⟨e, he⟩ := evt010_isTimeoutOut_iff.1 ht
        rcases exec022_onlyExpiry_step (i := i) hx f' hf' hid e he with
          ⟨f, hf, hfid, hfo⟩ | ⟨e', hl⟩
        · have := hc hP ⟨f, hf, hfid, evt010_isTimeoutOut_iff.2 ⟨e, hfo⟩⟩
          omega
        · rw [hl] at hx ⊢
          rw [evt010_atoAt_of rfl, evt010_refCount_expire P C H hx, hP]
          simp
      have := evt010_runLB P hag i _ hr' hc' hany'
      omega

/-- Line 3 holds of every executor that steps as the reference and counts the `ActionTimedOut`
events of a firing's steps as the reference does under one emission variant. -/
theorem evt010_line3_of (P : EvPol) {boot : Cfg N T → QMarking N T → List (NetEvent N T)}
    {emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    (hag : evt010_AgreesAto P emit) : evt010_line3 (emitExec boot emit) := by
  intro C M0 r0 run hr i
  have hs0 : IdsIssued (xinit (N := N) (T := T) M0 r0) := fun f hf => by simp [xinit] at hf
  have ub := (evt010_runUB P hag i hr hs0).1
  refine ⟨ub, fun hany => ?_⟩
  have lb := evt010_runLB P hag i 0 hr (fun _ ⟨f, hf, _⟩ => by simp [xinit] at hf) hany
  omega

/-- The reference meets `EVT_010` under every emission variant. -/
theorem evt010_ref (P : EvPol) : EVT_010 (refEvExec (N := N) (T := T) P) :=
  (evt010_iff _).2
    ⟨evt010_line1_of (fun C M0 => evt010_refBoot P C M0) (fun _ _ _ _ _ _ _ he _ => ⟨P, he⟩),
     evt010_line2_of (fun C H s i s' _ => evt010_refTdeposit P C H s i s'),
     evt010_line3_of P (fun _ _ _ _ _ _ _ => rfl)⟩

/-- ✓ The reference executor with the Java and TypeScript emission meets EVT-010: it reports a
timeout once, from the action's timer, at the moment the budget runs out, under the firing's
transition name, and reports nothing for a reap, a completion or an action's own error. -/
@[evidence holds EVT_010, evidence cites "IO-013" "AC4, an ActionTimedOut event on timeout: under both emission variants a firing that ends with its timeout outcome has exactly one ActionTimedOut, naming its transition, by the time the executor settles that outcome (EVT_010 lines 1 and 3)"]
theorem EVT_010_reference : EVT_010 (refEvExec (N := N) (T := T) polJT) := evt010_ref polJT

/-- ✓ The reference executor with the Rust and Python emission meets EVT-010 too: it reports a
timeout once, when it settles the timeout outcome, before the tokens of that outcome are added. -/
@[evidence holds EVT_010, evidence cites "EXEC-022" "Timeout fires first, ActionTimedOut event emitted: a firing whose budget runs out first has exactly one ActionTimedOut, emitted no later than the settle of its timeout outcome and before the TokenAdded events of that outcome (EVT_010 lines 2 and 3)"]
theorem EVT_010_rust : EVT_010 (refEvExec (N := N) (T := T) polRust) := evt010_ref polRust

end Reference

/-! ## The worked example -/

section Runs

variable {N T : Type} [DecidableEq N] [Ord N]
/-- The labelled run of `emitExec boot emit` from history `H` and state `s` along the labels
`ls`, if every label is a step. -/
def evt010Run (emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T →
    List (NetEvent N T)) (C : Cfg N T) :
    List (NetEvent N T) → XSt N T → List (XLbl N T) → Option (List (EvStep N T))
  | _, _, [] => some []
  | H, s, l :: ls => (xstep C s l).bind fun s' =>
      (evt010Run emit C (H ++ emit C H s l s') s' ls).map (⟨s, l, emit C H s l s', s'⟩ :: ·)

omit [Ord N] in
/-- A run `evt010Run` builds is a labelled run of `emitExec boot emit`. -/
theorem evt010Run_lrun {boot : Cfg N T → QMarking N T → List (NetEvent N T)}
    {emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    (C : Cfg N T) :
    ∀ {H : List (NetEvent N T)} {s : XSt N T} {ls : List (XLbl N T)} {run : List (EvStep N T)},
      evt010Run emit C H s ls = some run → LRun (emitExec boot emit) C H s run
  | H, s, [], run, h => by cases h; trivial
  | H, s, l :: ls, run, h => by
    simp only [evt010Run] at h
    cases hs : xstep C s l with
    | none => simp [hs] at h
    | some s' =>
      simp only [hs, Option.bind_some] at h
      cases hr : evt010Run emit C (H ++ emit C H s l s') s' ls with
      | none => simp [hr] at h
      | some run' =>
        simp only [hr, Option.map_some, Option.some.injEq] at h
        subst h
        exact ⟨rfl, ⟨hs, rfl⟩, evt010Run_lrun C hr⟩

omit [Ord N] in
/-- Read a decided fact off a run of `emitExec boot emit` from the initial state of `M0` at
reading 0: the run exists and passes `q`. -/
theorem evt010_runCheck {boot : Cfg N T → QMarking N T → List (NetEvent N T)}
    {emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    (C : Cfg N T) (M0 : QMarking N T) (ls : List (XLbl N T)) (q : List (EvStep N T) → Bool)
    (h : (evt010Run emit C (boot C M0) (xinit M0 0) ls).map q = some true) :
    ∃ run, LRun (emitExec boot emit) C (boot C M0) (xinit M0 0) run ∧ q run = true := by
  cases hr : evt010Run emit C (boot C M0) (xinit M0 0) ls with
  | none => simp [hr] at h
  | some run =>
    simp only [hr, Option.map_some, Option.some.injEq] at h
    exact ⟨run, evt010Run_lrun C hr, h⟩

end Runs

/-- The labels of the timeout run of the example (`evt008_cfg`): one cycle up to the
asynchronous start of `t`, the budget runs out with 7 and 8 forwarded to place 2, the pass ends,
and the next completion phase deposits the timeout outcome. -/
def evt010_labels : List (XLbl Nat Nat) :=
  evt008_pre ++ [.expire 0 evt008_tout, .endPass, .tdeposit 0]

/-- The state before the budget of `t` runs out. -/
def evt010_beforeExpire : Option (XSt Nat Nat) := xrun evt008_cfg (xinit evt008_m0 0) evt008_pre

/-- ✓ Every line is exercised by the reference on the example. Transition `t` takes 7 and 8 from
place 0 and starts its action; the action's budget runs out, so 7 and 8 are forwarded to place 2.
With the Java and TypeScript emission, the moment the budget runs out reports `ActionTimedOut t`,
and the later deposit adds 7 and 8 to place 2 with no second report. With the Rust emission, the
deposit reports `ActionTimedOut t` first and then adds 7 and 8. When the join-relay check rejects
the forwarded tokens, the Rust fail step reports `ActionTimedOut t` and then `TransitionFailed t`.
When the action throws instead, the fail step reports only `TransitionFailed t`, and when the
action returns a token for place 1 in time, the commit reports no timeout. Over the whole run, the
firing has exactly one `ActionTimedOut` under each emission. -/
@[evidence nonvacuous EVT_010]
theorem EVT_010_nonvacuous :
    (∃ s s' evs, (refEvExec polJT).step evt008_cfg [] s (.expire 0 evt008_tout) evs s' ∧
      evs = [.actionTimedOut "t"]) ∧
    (∃ s s' evs, (refEvExec polJT).step evt008_cfg [] s (.tdeposit 0) evs s' ∧
      evs.take 2 = [.tokenAdded 2 7, .tokenAdded 2 8] ∧ kindCount .actionTimedOut evs = 0) ∧
    (∃ s s' evs, (refEvExec polRust).step evt008_cfg [] s (.tdeposit 0) evs s' ∧
      evs = [.actionTimedOut "t", .tokenAdded 2 7, .tokenAdded 2 8]) ∧
    (∃ s s' evs, (refEvExec polRust).step evt008_cfgRelay [] s (.fail 0) evs s' ∧
      evs = [.actionTimedOut "t", .transitionFailed "t"]) ∧
    (∃ s s' evs, (refEvExec polRust).step evt008_cfg [] s (.fail 0) evs s' ∧
      evt008_fl0 s evt008_isErr = true ∧ evs = [.transitionFailed "t"]) ∧
    (∃ s s' evs, (refEvExec polRust).step evt008_cfg [] s (.commit 0) evs s' ∧ evs ≠ [] ∧
      kindCount .actionTimedOut evs = 0) ∧
    (∃ run, LRun (refEvExec polJT) evt008_cfg (refBoot polJT evt008_cfg evt008_m0)
        (xinit evt008_m0 0) run ∧
      run.any (evt010_settlesTimeout 0) = true ∧ evt010_atoOf 0 run = 1) ∧
    (∃ run, LRun (refEvExec polRust) evt008_cfg (refBoot polRust evt008_cfg evt008_m0)
        (xinit evt008_m0 0) run ∧
      run.any (evt010_settlesTimeout 0) = true ∧ evt010_atoOf 0 run = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨s, s', evs, hs, hp⟩ := evt008_check polJT evt008_cfg evt010_beforeExpire
      (.expire 0 evt008_tout) (fun _ evs => evs == [.actionTimedOut "t"]) (by decide +kernel)
    exact ⟨s, s', evs, hs, by simpa using hp⟩
  · obtain ⟨s, s', evs, hs, hp⟩ := evt008_check polJT evt008_cfg (evt008_expired evt008_cfg)
      (.tdeposit 0) (fun _ evs => evs.take 2 == [.tokenAdded 2 7, .tokenAdded 2 8] &&
        kindCount .actionTimedOut evs == 0) (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', evs, hs, hp.1, hp.2⟩
  · obtain ⟨s, s', evs, hs, hp⟩ := evt008_check polRust evt008_cfg (evt008_expired evt008_cfg)
      (.tdeposit 0) (fun _ evs => evs == [.actionTimedOut "t", .tokenAdded 2 7, .tokenAdded 2 8])
      (by decide +kernel)
    exact ⟨s, s', evs, hs, by simpa using hp⟩
  · obtain ⟨s, s', evs, hs, hp⟩ := evt008_check polRust evt008_cfgRelay
      (evt008_expired evt008_cfgRelay) (.fail 0)
      (fun _ evs => evs == [.actionTimedOut "t", .transitionFailed "t"]) (by decide +kernel)
    exact ⟨s, s', evs, hs, by simpa using hp⟩
  · obtain ⟨s, s', evs, hs, hp⟩ := evt008_check polRust evt008_cfg evt008_throws (.fail 0)
      (fun s evs => evt008_fl0 s evt008_isErr && evs == [.transitionFailed "t"])
      (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', evs, hs, hp.1, hp.2⟩
  · obtain ⟨s, s', evs, hs, hp⟩ := evt008_check polRust evt008_cfg evt008_returned (.commit 0)
      (fun _ evs => !evs.isEmpty && kindCount .actionTimedOut evs == 0) (by decide +kernel)
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, beq_iff_eq] at hp
    exact ⟨s, s', evs, hs, hp.1, hp.2⟩
  · obtain ⟨run, hr, hq⟩ := evt010_runCheck (boot := refBoot polJT) (emit := refEmitW polJT)
      evt008_cfg evt008_m0 evt010_labels
      (fun run => run.any (evt010_settlesTimeout 0) && evt010_atoOf 0 run == 1)
      (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq] at hq
    exact ⟨run, hr, hq.1, hq.2⟩
  · obtain ⟨run, hr, hq⟩ := evt010_runCheck (boot := refBoot polRust) (emit := refEmitW polRust)
      evt008_cfg evt008_m0 evt010_labels
      (fun run => run.any (evt010_settlesTimeout 0) && evt010_atoOf 0 run == 1)
      (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq] at hq
    exact ⟨run, hr, hq.1, hq.2⟩

/-! ## Wrong executors: the reference's steps, another emission -/

section Mutants

variable {N T : Type} [DecidableEq N] [Ord N]
/-- An emission that emits as the Java and TypeScript reference at every step of a firing counts
a firing's `ActionTimedOut` events as that reference does. -/
theorem evt010_agree_of_jt
    {emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    (he : ∀ C H s l s', evt010_lblId l ≠ none → emit C H s l s' = refEmitW polJT C H s l s') :
    evt010_AgreesAto polJT emit := fun C H s l s' _ hl => by rw [he C H s l s' hl]

/-- The Java and TypeScript emission with an `ActionTimedOut` for every name a deadline step
reaps, after its `TransitionTimedOut` events. -/
def evt010_reapEmit (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T) (l : XLbl N T)
    (s' : XSt N T) : List (NetEvent N T) :=
  match l with
  | .deadline ns => refEmitW polJT C H s l s' ++ ns.map .actionTimedOut
  | _ => refEmitW polJT C H s l s'

/-- The executor that also reports a reap as an `ActionTimedOut`. -/
def evt010_reapAto : EvExec N T := emitExec (refBoot polJT) evt010_reapEmit

/-- The Java and TypeScript emission with an `ActionTimedOut` after the `TransitionCompleted` of
a committed completion. -/
def evt010_commitEmit (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T) (l : XLbl N T)
    (s' : XSt N T) : List (NetEvent N T) :=
  match l with
  | .commit i => refEmitW polJT C H s l s' ++
      match s.fl.find? (·.id == i) with
      | some f => [.actionTimedOut f.t.core.name]
      | none => []
  | _ => refEmitW polJT C H s l s'

/-- The executor that reports a committed completion as timed out as well. -/
def evt010_commitAto : EvExec N T := emitExec (refBoot polJT) evt010_commitEmit

/-- The firing holds an error (its action threw or returned an error). -/
def evt010_isErr (f : Firing N T) : Bool :=
  match f.out with
  | some .err => true
  | _ => false

/-- The Rust emission with an `ActionTimedOut` before the `TransitionFailed` of a firing whose
action failed (an action's own timeout error read as the budget's). -/
def evt010_errEmit (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T) (l : XLbl N T)
    (s' : XSt N T) : List (NetEvent N T) :=
  match l with
  | .fail i =>
    (match s.fl.find? (·.id == i) with
     | some f => if evt010_isErr f then [.actionTimedOut f.t.core.name] else []
     | none => []) ++ refEmitW polRust C H s l s'
  | _ => refEmitW polRust C H s l s'

/-- The executor that reports an action's own error as an `ActionTimedOut`. -/
def evt010_errAto : EvExec N T := emitExec (refBoot polRust) evt010_errEmit

/-- The events of a timeout deposit, Rust order, with an `ActionTimedOut` that names no
transition. -/
def evt010_anonEvs (s : XSt N T) (i : Nat) : List (NetEvent N T) :=
  match s.fl.find? (·.id == i) with
  | some f =>
    match f.out with
    | some (.timedOut e) => .actionTimedOut "" :: addedEvs e
    | _ => []
  | none => []

/-- The events of a timeout deposit with the `ActionTimedOut` after the `TokenAdded` events of
the outcome. -/
def evt010_lateEvs (s : XSt N T) (i : Nat) : List (NetEvent N T) :=
  match s.fl.find? (·.id == i) with
  | some f =>
    match f.out with
    | some (.timedOut e) => addedEvs e ++ [.actionTimedOut f.t.core.name]
    | _ => []
  | none => []

/-- The Rust emission with the events of a timeout deposit replaced by `g s i`. -/
def evt010_atTdeposit (g : XSt N T → Nat → List (NetEvent N T)) (C : Cfg N T)
    (H : List (NetEvent N T)) (s : XSt N T) (l : XLbl N T) (s' : XSt N T) : List (NetEvent N T) :=
  match l with
  | .tdeposit i => g s i
  | _ => refEmitW polRust C H s l s'

/-- The executor that reports a timeout under no transition's name. -/
def evt010_anon : EvExec N T := emitExec (refBoot polRust) (evt010_atTdeposit evt010_anonEvs)

/-- The executor that reports a timeout after depositing its outcome. -/
def evt010_late : EvExec N T := emitExec (refBoot polRust) (evt010_atTdeposit evt010_lateEvs)

/-- The Java and TypeScript boot events followed by an `ActionTimedOut` for every transition of
the net. -/
def evt010_bootEvs (C : Cfg N T) (M0 : QMarking N T) : List (NetEvent N T) :=
  refBoot polJT C M0 ++ C.X.net.transitions.map fun t => .actionTimedOut t.core.name

/-- The executor that reports every transition as timed out when the run boots. -/
def evt010_bootAto : EvExec N T := emitExec evt010_bootEvs (refEmitW polJT)

/-- The Java and TypeScript emission, with the Rust events at a timeout deposit: the
`ActionTimedOut` at the expiry and again at the deposit. -/
def evt010_twiceEmit (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T) (l : XLbl N T)
    (s' : XSt N T) : List (NetEvent N T) :=
  match l with
  | .tdeposit _ => refEmitW polRust C H s l s'
  | _ => refEmitW polJT C H s l s'

/-- The executor that reports a timeout twice. -/
def evt010_twice : EvExec N T := emitExec (refBoot polJT) evt010_twiceEmit

/-- The Rust emission without its `ActionTimedOut` events. -/
def evt010_silentEmit (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T) (l : XLbl N T)
    (s' : XSt N T) : List (NetEvent N T) :=
  (refEmitW polRust C H s l s').filter fun e => e.kind != .actionTimedOut

/-- The executor that never reports a timeout. -/
def evt010_silent : EvExec N T := emitExec (refBoot polRust) evt010_silentEmit

omit [Ord N] in
/-- The events of `evt010_anonEvs` and `evt010_lateEvs` hold one `ActionTimedOut` when the
deposit is a step. -/
theorem evt010_tdep_count {C : Cfg N T} {s s' : XSt N T} {i : Nat}
    (hx : xstep C s (.tdeposit i) = some s') :
    kindCount .actionTimedOut (evt010_anonEvs s i) = 1 ∧
      kindCount .actionTimedOut (evt010_lateEvs s i) = 1 := by
  obtain ⟨f, e, hf, ho, -⟩ := tdepositStep_some hx
  simp [evt010_anonEvs, evt010_lateEvs, hf, ho, kindCount, addedEvs, List.countP_append,
    List.countP_map, Function.comp_def, NetEvent.kind]

/-- Changing only the events of a timeout deposit, to events with one `ActionTimedOut`, keeps
the Rust count. -/
theorem evt010_atTdeposit_agree {g : XSt N T → Nat → List (NetEvent N T)}
    (hg : ∀ C s i s', xstep C s (.tdeposit i) = some s' →
      kindCount .actionTimedOut (g s i) = 1) :
    evt010_AgreesAto polRust (evt010_atTdeposit g) := by
  intro C H s l s' hx _
  cases l with
  | tdeposit i =>
    show kindCount _ (g s i) = _
    rw [hg C s i s' hx, evt010_refCount_tdeposit polRust C H hx]
    rfl
  | _ => rfl

end Mutants

/-- ✗ Reporting a reap as an action timeout violates EVT-010 (line 1). Transition `u` is
`Window(3, 5)` and the host falls behind to reading 7, so the deadline step reaps `u`; this
executor reports `ActionTimedOut u` there as well, although no action's budget ran out. It keeps
lines 2 and 3, which count only the steps of a firing. -/
@[evidence mutant EVT_010]
theorem EVT_010_mutant_reapAsActionTimedOut :
    evt010_keeps23 (evt010_reapAto (N := Nat) (T := Nat)) ∧
      ¬ EVT_010 (evt010_reapAto (N := Nat) (T := Nat)) := by
  refine ⟨⟨evt010_line2_of fun C H s i s' _ => evt010_refTdeposit polJT C H s i s',
    evt010_line3_of polJT (evt010_agree_of_jt fun C H s l s' hl => ?_)⟩, fun h => ?_⟩
  · cases l with
    | deadline ns => simp [evt010_lblId] at hl
    | _ => rfl
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt009_cfg) (o := evt009_beforeDeadline)
      (l := .deadline ["u"])
      (p := fun s s' => (evt010_reapEmit evt009_cfg [] s (.deadline ["u"]) s').contains
        (.actionTimedOut "u"))
      (by decide +kernel)
    simp only [List.contains_eq_mem, decide_eq_true_eq] at hp
    obtain ⟨i, hi, -⟩ := (h evt009_cfg).1.2 [] _ _ s s' ⟨hs, rfl⟩ _ hp rfl
    simp [evt010_lblId] at hi

/-- ✗ Reporting a completed firing as timed out violates EVT-010 (line 1). `t`'s action returns
the token 50 for place 1 in time, and this executor commits it and also reports
`ActionTimedOut t`. It keeps lines 2 and 3. -/
@[evidence mutant EVT_010]
theorem EVT_010_mutant_completedAndTimedOut :
    evt010_keeps23 (evt010_commitAto (N := Nat) (T := Nat)) ∧
      ¬ EVT_010 (evt010_commitAto (N := Nat) (T := Nat)) := by
  refine ⟨⟨evt010_line2_of fun C H s i s' _ => evt010_refTdeposit polJT C H s i s',
    evt010_line3_of polJT (evt010_agree_of_jt fun C H s l s' hl => ?_)⟩, fun h => ?_⟩
  · cases l with
    | commit i => simp [evt010_lblId] at hl
    | _ => rfl
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt008_cfg) (o := evt008_returned)
      (l := .commit 0)
      (p := fun s s' => (evt010_commitEmit evt008_cfg [] s (.commit 0) s').contains
        (.actionTimedOut "t"))
      (by decide +kernel)
    simp only [List.contains_eq_mem, decide_eq_true_eq] at hp
    obtain ⟨i, hi, -⟩ := (h evt008_cfg).1.2 [] _ _ s s' ⟨hs, rfl⟩ _ hp rfl
    simp [evt010_lblId] at hi

/-- ✗ Reporting an action's own error as a timeout violates EVT-010 (line 1). `t`'s action throws
before its budget runs out (for example a timeout exception of its own), and this executor's fail
step reports `ActionTimedOut t` before `TransitionFailed t`, although the firing holds an error,
not a timeout outcome. It keeps line 2. -/
@[evidence mutant EVT_010]
theorem EVT_010_mutant_actionErrorAsTimeout :
    evt010_line2 (evt010_errAto (N := Nat) (T := Nat)) ∧
      ¬ EVT_010 (evt010_errAto (N := Nat) (T := Nat)) := by
  refine ⟨evt010_line2_of fun C H s i s' _ => evt010_refTdeposit polRust C H s i s', fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt008_cfg) (o := evt008_throws)
    (l := .fail 0)
    (p := fun s s' => (evt010_errEmit evt008_cfg [] s (.fail 0) s').contains (.actionTimedOut "t") &&
      s.fl.all fun f => f.id != 0 || !isTimeoutOut f)
    (by decide +kernel)
  simp only [Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at hp
  obtain ⟨i, hi, f, hf, hid, -, hc⟩ := (h evt008_cfg).1.2 [] _ _ s s' ⟨hs, rfl⟩ _ hp.1 rfl
  simp only [evt010_lblId, Option.some.injEq] at hi
  subst hi
  rcases hc with hc | hc
  · simp [evt010_isExpire] at hc
  · rcases hp.2 f hf with h0 | h0
    · exact h0 hid
    · rw [h0] at hc; cases hc

/-- ✗ Reporting a timeout under no transition's name violates EVT-010 (line 1). `t`'s budget runs
out and the deposit reports one `ActionTimedOut`, before the tokens, but it names the empty
string instead of `t`. It keeps lines 2 and 3. -/
@[evidence mutant EVT_010]
theorem EVT_010_mutant_anonymous :
    evt010_keeps23 (evt010_anon (N := Nat) (T := Nat)) ∧
      ¬ EVT_010 (evt010_anon (N := Nat) (T := Nat)) := by
  refine ⟨⟨evt010_line2_of fun C H s i s' _ => ?_,
    evt010_line3_of polRust (evt010_atTdeposit_agree fun C s i s' hx =>
      (evt010_tdep_count hx).1)⟩, fun h => ?_⟩
  · show evt010_AtoFirst (evt010_anonEvs s i)
    unfold evt010_anonEvs
    split
    · split
      · exact evt010_atoFirst_append (pre := [.actionTimedOut ""]) (by simp [NetEvent.kind])
          (fun x hx hk => by rw [kind_of_mem_addedEvs hx] at hk; cases hk)
      · exact evt010_atoFirst_append (pre := []) (rest := []) (by simp) (by simp)
    · exact evt010_atoFirst_append (pre := []) (rest := []) (by simp) (by simp)
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt008_cfg)
      (o := evt008_expired evt008_cfg) (l := .tdeposit 0)
      (p := fun s _ => (evt010_anonEvs s 0).contains (.actionTimedOut "") &&
        s.fl.all fun f => f.id != 0 || f.t.core.name != "")
      (by decide +kernel)
    simp only [Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq, List.all_eq_true,
      Bool.or_eq_true, bne_iff_ne, ne_eq] at hp
    obtain ⟨i, hi, f, hf, hid, hn, -⟩ := (h evt008_cfg).1.2 [] _ _ s s' ⟨hs, rfl⟩ _ hp.1 rfl
    simp only [evt010_lblId, Option.some.injEq] at hi
    subst hi
    simp only [NetEvent.trans?, Option.some.injEq] at hn
    rcases hp.2 f hf with h0 | h0
    · exact h0 hid
    · exact h0 hn.symm

/-- ✗ Reporting timeouts when the run boots violates EVT-010 (line 1): the boot of the example
reports `ActionTimedOut t` before `t` has even started. Every step emits as the reference, so it
keeps lines 2 and 3. -/
@[evidence mutant EVT_010]
theorem EVT_010_mutant_bootTimedOut :
    evt010_keeps23 (evt010_bootAto (N := Nat) (T := Nat)) ∧
      ¬ EVT_010 (evt010_bootAto (N := Nat) (T := Nat)) := by
  refine ⟨⟨evt010_line2_of fun C H s i s' _ => evt010_refTdeposit polJT C H s i s',
    evt010_line3_of polJT fun _ _ _ _ _ _ _ => rfl⟩, fun h => ?_⟩
  have hm : NetEvent.actionTimedOut "t" ∈ evt010_bootAto.boot evt008_cfg evt008_m0 := by
    decide +kernel
  exact (h evt008_cfg).1.1 evt008_m0 _ hm rfl

/-- ✗ Reporting a timeout after its outcome is deposited violates EVT-010 (line 2). `t`'s budget
runs out, and the deposit emits `TokenAdded` for 7 and 8 in place 2 first and `ActionTimedOut t`
after them. The event is still the firing's one report, so it keeps lines 1 and 3. -/
@[evidence mutant EVT_010]
theorem EVT_010_mutant_afterDeposit :
    evt010_keeps13 (evt010_late (N := Nat) (T := Nat)) ∧
      ¬ EVT_010 (evt010_late (N := Nat) (T := Nat)) := by
  refine ⟨⟨evt010_line1_of (fun C M0 => evt010_refBoot polRust C M0) fun C H s l s' hx e he hk => ?_,
    evt010_line3_of polRust (evt010_atTdeposit_agree fun C s i s' hx =>
      (evt010_tdep_count hx).2)⟩, fun h => ?_⟩
  · cases l with
    | tdeposit i =>
      refine ⟨polRust, ?_⟩
      change e ∈ evt010_lateEvs s i at he
      unfold evt010_lateEvs at he
      cases hf : s.fl.find? (·.id == i) with
      | none => simp [hf] at he
      | some f =>
        cases ho : f.out with
        | none => simp [hf, ho] at he
        | some o =>
          cases o with
          | ok e0 => simp [hf, ho] at he
          | err => simp [hf, ho] at he
          | timedOut e0 =>
            simp only [hf, ho, List.mem_append, List.mem_singleton] at he
            rcases he with h | rfl
            · rw [kind_of_mem_addedEvs h] at hk; cases hk
            · simp [refEmitW, hf, ho, polRust]
    | _ => exact ⟨polRust, he⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt008_cfg)
      (o := evt008_expired evt008_cfg) (l := .tdeposit 0)
      (p := fun s _ => evt010_lateEvs s 0 ==
        [.tokenAdded 2 7, .tokenAdded 2 8, .actionTimedOut "t"])
      (by decide +kernel)
    simp only [beq_iff_eq] at hp
    have h2 := (h evt008_cfg).2.1 [] 0 _ s s' ⟨hs, rfl⟩
    exact h2 [.tokenAdded 2 7, .tokenAdded 2 8] (.actionTimedOut "t") []
      (by show evt010_lateEvs s 0 = _; rw [hp]; rfl) rfl (.tokenAdded 2 7) (by simp) rfl

/-- ✗ Reporting a timeout twice violates EVT-010 (line 3). `t`'s budget runs out: this executor
reports `ActionTimedOut t` at that moment, as Java and TypeScript do, and again when it deposits
7 and 8, as Rust does, so the one firing has two reports. Each report alone is in a place line 1
allows, so it keeps lines 1 and 2. -/
@[evidence mutant EVT_010]
theorem EVT_010_mutant_reportedTwice :
    evt010_keeps12 (evt010_twice (N := Nat) (T := Nat)) ∧
      ¬ EVT_010 (evt010_twice (N := Nat) (T := Nat)) := by
  refine ⟨⟨evt010_line1_of (fun C M0 => evt010_refBoot polJT C M0) fun C H s l s' _ e he _ => ?_,
    evt010_line2_of fun C H s i s' _ => evt010_refTdeposit polRust C H s i s'⟩, fun h => ?_⟩
  · cases l with
    | tdeposit i => exact ⟨polRust, he⟩
    | _ => exact ⟨polJT, he⟩
  · obtain ⟨run, hr, hq⟩ := evt010_runCheck (boot := refBoot polJT) (emit := evt010_twiceEmit)
      evt008_cfg evt008_m0 evt010_labels (fun run => evt010_atoOf 0 run == 2)
      (by decide +kernel)
    simp only [beq_iff_eq] at hq
    have := ((h evt008_cfg).2.2 evt008_m0 0 run hr 0).1
    omega

/-- ✗ Never reporting a timeout violates EVT-010 (line 3). `t`'s budget runs out and 7 and 8 are
deposited in place 2, but this executor emits no `ActionTimedOut` at all. It reports nothing in a
wrong place, so it keeps lines 1 and 2. -/
@[evidence mutant EVT_010]
theorem EVT_010_mutant_silentTimeout :
    evt010_keeps12 (evt010_silent (N := Nat) (T := Nat)) ∧
      ¬ EVT_010 (evt010_silent (N := Nat) (T := Nat)) := by
  have none : ∀ (C : Cfg Nat Nat) H s l s', ∀ e ∈ evt010_silentEmit C H s l s',
      e.kind ≠ .actionTimedOut := by
    intro C H s l s' e he hk
    simp only [evt010_silentEmit, List.mem_filter, bne_iff_ne, ne_eq] at he
    exact he.2 hk
  refine ⟨⟨evt010_line1_of (fun C M0 => evt010_refBoot polRust C M0)
      fun C H s l s' _ e he hk => absurd hk (none C H s l s' e he),
    evt010_line2_of fun C H s i s' _ a e b hab hk => absurd hk (none C H s _ s' e
      (by rw [hab]; simp))⟩, fun h => ?_⟩
  obtain ⟨run, hr, hq⟩ := evt010_runCheck (boot := refBoot polRust) (emit := evt010_silentEmit)
    evt008_cfg evt008_m0 evt010_labels
    (fun run => run.any (evt010_settlesTimeout 0) && evt010_atoOf 0 run == 0)
    (by decide +kernel)
  simp only [Bool.and_eq_true, beq_iff_eq] at hq
  have := ((h evt008_cfg).2.2 evt008_m0 0 run hr 0).2 hq.1
  omega

/-! ## EVT-010, second block: the duration an `ActionTimedOut` event carries -/

section PayloadModel

/-- **Timeout durations**: the `after` duration, in milliseconds, of the `Timeout` node of each
transition's output spec. The model's `Out.timeout` carries no duration, so the payload block takes
the durations as data next to the configuration; only the value at a transition whose output spec
has a `Timeout` node is ever read. -/
abbrev Evt010Budgets (N : Type) := Trans N → Nat

/-- **An executor with events whose `ActionTimedOut` events carry a duration**: the executor with
events `ex`, and `dur bud C s l e`, the duration field of the event `e` that the step labelled `l`
from state `s` appends under configuration `C`, when the `Timeout` nodes of the net have the
durations `bud`. The model's event (`NetEvent.actionTimedOut`) carries the transition name only, so
the field is this block's own. -/
structure Evt010DurExec (N T : Type) where
  /-- The executor with events. -/
  ex  : EvExec N T
  /-- The duration field of each event a step appends. -/
  dur : Evt010Budgets N → Cfg N T → XSt N T → XLbl N T → NetEvent N T → Nat

/-- The duration of the `Timeout` node of the firing that the label `l` names in state `s`: the
first firing in flight with that identity, as `refEmitW` names its transition; `0` where the label
names none (no `ActionTimedOut` is emitted there). -/
def evt010_refDur {N T : Type} (bud : Evt010Budgets N) (_ : Cfg N T) (s : XSt N T) (l : XLbl N T)
    (_ : NetEvent N T) : Nat :=
  match evt010_lblId l with
  | some i =>
    match s.fl.find? (·.id == i) with
    | some f => bud f.t
    | none => 0
  | none => 0

/-- The reference executor with events under the emission variant `P`, with the duration field
`evt010_refDur`. -/
def evt010_refDurExec {N T : Type} [DecidableEq N] [Ord N] (P : EvPol) : Evt010DurExec N T :=
  ⟨refEvExec P, evt010_refDur⟩

end PayloadModel

/- The reference executor with events and its duration field is the witness model of the payload
block's `holds` theorems. -/
#spec_witness evt010_refDurExec

requirement EVT_010_payload
  id "EVT-010"
  title "ActionTimedOut Event (duration)"
  kind B
  scope "all executors (event store enabled)"
  source verbatim "spec/08-events-observability.md"
  covers EVT_010.s4
  reading "For every executor with events D whose ActionTimedOut events carry a duration, every assignment bud of durations to the Timeout nodes of the transitions, every configuration C and every history H:"
          "every ActionTimedOut event e that a step labelled l from state s appends carries as its duration bud of the transition of a firing f in flight in s whose identity is the one the label carries."
  assumes "This is the second block of EVT-010: the duration field. The first block, EVT_010, says when the event is emitted and which transition it names; this block adds what its duration holds. The model's events and output specs carry no durations: NetEvent.actionTimedOut carries the transition name only (Spec/GlossaryEvents.lean) and Out.timeout has no after duration (Reference/Semantics.lean). The block therefore takes the durations as data, bud : Trans N -> Nat, the after duration in milliseconds of the Timeout node of each transition's output spec, and models the field as dur, the duration an executor writes into each event a step appends (Evt010DurExec, an executor with events and its duration field). The witness is the reference executor with events refEvExec under both emission variants, with the duration field evt010_refDur: bud of the transition of the firing the step's label names. The field is this block's own until the shared model carries the duration on the Timeout node and on the event; the event blocks' other fields do not read it."
          "'The firing' is the one the first block's line 1 attributes the event to: a firing in flight whose identity the step label carries, the expiry expire i e of its budget under the Java and TypeScript emission, a timeout deposit tdeposit i or a fail step fail i under the Rust emission. The line reads the duration of that firing's own transition, the one whose output spec has the Timeout node whose budget ran out; only such a firing records a timeout outcome (EXEC-022), so bud is read only at transitions with a Timeout node. Every runtime carries the configured duration, not the time that elapsed: Java's NetEvent.ActionTimedOut carries t.actionTimeout().after(), a Duration, and is emitted by the onTimeout callback that fireTransition hands to ExecutorSupport.withActionTimeout (java/src/main/java/org/libpetri/runtime/BitmapNetExecutor.java and PrecompiledNetExecutor.java, fireTransition in each); TypeScript sets timeoutMs from timeoutSpec.afterMs and emits the event in the timeout branch of fireTransition (typescript/src/runtime/bitmap-net-executor.ts and precompiled-net-executor.ts, fireTransition in each); Rust sets timeout_ms from the after_ms of the Timeout node the spawned task slept on, carried on the completion as timed_out, which fire_transition_async sets and handle_completion emits (rust/libpetri-runtime/src/executor_core/executor.rs, the timeout_ms field of NetEvent::ActionTimedOut in rust/libpetri-event/src/net_event.rs); Python rides on Rust. The unit (a Java Duration, milliseconds in TypeScript and Rust) is the event's representation (kind N)."
          "An executor that steps and emits as the reference but reports zero (EVT_010_payload_mutant_zero) or the time elapsed since the firing started (EVT_010_payload_mutant_elapsed) meets the first block and breaks this line. The shared assumptions of the first block (store enabled, events are values, distinct names) apply; the timestamp is not modelled."
          "The test derivation (an action sleeps 500 ms with Out.Timeout at 100 ms, verify the ActionTimedOut event) is EVT_010_payload_nonvacuous on the example of the first block, with t's Timeout node at 100 ms: under the Java and TypeScript emission the expiry of t's budget reports ActionTimedOut t with duration 100, and under the Rust emission the deposit of the timeout outcome reports it with duration 100."
  signoff "2026-11-13 6d9570c61a2d44ce ai"
  statement : ∀ {N T : Type}, Evt010DurExec N T → Prop :=
    fun D => ∀ bud C H l evs, on (fun s s' => D.ex.step C H s l evs s'), shall (fun s _ =>
      ∀ e ∈ evs, e.kind = .actionTimedOut →
        ∃ f ∈ s.fl, evt010_lblId l = some f.id ∧ D.dur bud C s l e = bud f.t)

/- The pinned readable form of the companion: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EVT_010_payload : {N T : Type} → Evt010DurExec N T → Prop :=
fun {N T} D =>
  ∀ (bud : Evt010Budgets N) (C : Cfg N T) (H : List (NetEvent N T)) (l : XLbl N T) (evs : List (NetEvent N T)),
    on fun s s' => D.ex.step C H s l evs s', shall fun s x =>
      ∀ e ∈ evs,
        e.kind = NetEventKind.actionTimedOut → ∃ f ∈ s.fl, evt010_lblId l = some f.id ∧ D.dur bud C s l e = bud f.t
-/
#guard_msgs in #print EVT_010_payload

section Payload

variable {N T : Type} [DecidableEq N] [Ord N]

/-- The reference meets the payload block under every emission variant: an `ActionTimedOut` the
reference emits belongs to the first firing in flight with the label's identity
(`evt010_refAto`), and `evt010_refDur` reads that firing's transition. -/
theorem evt010_payload_ref (P : EvPol) : EVT_010_payload (evt010_refDurExec (N := N) (T := T) P) := by
  intro bud C H l evs s s' hs e he hk
  obtain ⟨-, rfl⟩ := hs
  obtain ⟨i, f, hl, hf, -, -⟩ := evt010_refAto P C H s l s' e he hk
  have hid : f.id = i := by simpa using List.find?_some hf
  refine ⟨f, List.mem_of_find?_eq_some hf, by rw [hl, hid], ?_⟩
  simp [evt010_refDurExec, evt010_refDur, hl, hf]

/-- ✓ The reference with the Java and TypeScript emission meets the payload block: the event of
the expiry carries the duration of the expired firing's `Timeout` node. -/
@[evidence holds EVT_010_payload]
theorem EVT_010_payload_reference :
    EVT_010_payload (evt010_refDurExec (N := N) (T := T) polJT) := evt010_payload_ref polJT

/-- ✓ The reference with the Rust emission meets the payload block: the event of the settle
carries the duration of the settled firing's `Timeout` node. -/
@[evidence holds EVT_010_payload]
theorem EVT_010_payload_rust :
    EVT_010_payload (evt010_refDurExec (N := N) (T := T) polRust) := evt010_payload_ref polRust

/-- The duration field that reports zero. -/
def evt010_zeroDur (_ : Evt010Budgets N) (_ : Cfg N T) (_ : XSt N T) (_ : XLbl N T)
    (_ : NetEvent N T) : Nat := 0

/-- The duration field that reports the time elapsed since the named firing started: the host
reading of the step's source state less the firing's start reading. -/
def evt010_elapsedDur (_ : Evt010Budgets N) (_ : Cfg N T) (s : XSt N T) (l : XLbl N T)
    (_ : NetEvent N T) : Nat :=
  match evt010_lblId l with
  | some i =>
    match s.fl.find? (·.id == i) with
    | some f => s.now - f.start
    | none => 0
  | none => 0

/-- The executor that steps and emits as the Java and TypeScript reference and reports a zero
duration. -/
def evt010_zeroDurExec : Evt010DurExec N T := ⟨refEvExec polJT, evt010_zeroDur⟩

/-- The executor that steps and emits as the Java and TypeScript reference and reports the time
elapsed since the firing started. -/
def evt010_elapsedDurExec : Evt010DurExec N T := ⟨refEvExec polJT, evt010_elapsedDur⟩

omit [Ord N] in
/-- The executor with events of `D` meets the first block of EVT-010. -/
def evt010_ExMeets (D : Evt010DurExec N T) : Prop := EVT_010 D.ex

end Payload

/-- The `Timeout` durations of the example: 100 ms for `t`, 0 for every other transition. -/
def evt010_bud : Evt010Budgets Nat := fun t => if t.core.name = "t" then 100 else 0

/-- ✓ The payload line is exercised by the reference under both emissions, on the example of the
first block with `t`'s `Timeout` node at 100 ms: with the Java and TypeScript emission the expiry
of `t`'s budget reports `ActionTimedOut t` with duration 100; with the Rust emission the deposit of
the timeout outcome reports `ActionTimedOut t` with duration 100, then adds 7 and 8. -/
@[evidence nonvacuous EVT_010_payload]
theorem EVT_010_payload_nonvacuous :
    (∃ s s' evs, (evt010_refDurExec polJT).ex.step evt008_cfg [] s (.expire 0 evt008_tout) evs s' ∧
      evs = [.actionTimedOut "t"] ∧
      (evt010_refDurExec polJT).dur evt010_bud evt008_cfg s (.expire 0 evt008_tout)
        (.actionTimedOut "t") = 100) ∧
    (∃ s s' evs, (evt010_refDurExec polRust).ex.step evt008_cfg [] s (.tdeposit 0) evs s' ∧
      evs = [.actionTimedOut "t", .tokenAdded 2 7, .tokenAdded 2 8] ∧
      (evt010_refDurExec polRust).dur evt010_bud evt008_cfg s (.tdeposit 0)
        (.actionTimedOut "t") = 100) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨s, s', evs, hs, hp⟩ := evt008_check polJT evt008_cfg evt010_beforeExpire
      (.expire 0 evt008_tout)
      (fun s evs => evs == [.actionTimedOut "t"] &&
        evt010_refDur evt010_bud evt008_cfg s (.expire 0 evt008_tout) (.actionTimedOut "t") == 100)
      (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', evs, hs, hp.1, hp.2⟩
  · obtain ⟨s, s', evs, hs, hp⟩ := evt008_check polRust evt008_cfg (evt008_expired evt008_cfg)
      (.tdeposit 0)
      (fun s evs => evs == [.actionTimedOut "t", .tokenAdded 2 7, .tokenAdded 2 8] &&
        evt010_refDur evt010_bud evt008_cfg s (.tdeposit 0) (.actionTimedOut "t") == 100)
      (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', evs, hs, hp.1, hp.2⟩

/-- ✗ Reporting a zero duration violates the payload block. `t`'s budget of 100 ms runs out and
this executor reports `ActionTimedOut t` with duration 0. It steps and emits as the reference, so
it meets the first block. -/
@[evidence mutant EVT_010_payload]
theorem EVT_010_payload_mutant_zero :
    evt010_ExMeets (evt010_zeroDurExec (N := Nat) (T := Nat)) ∧
      ¬ EVT_010_payload (evt010_zeroDurExec (N := Nat) (T := Nat)) := by
  refine ⟨EVT_010_reference, fun h => ?_⟩
  obtain ⟨s, s', evs, hs, hp⟩ := evt008_check polJT evt008_cfg evt010_beforeExpire
    (.expire 0 evt008_tout) (fun _ evs => evs == [.actionTimedOut "t"]) (by decide +kernel)
  have hev : evs = [.actionTimedOut "t"] := by simpa using hp
  obtain ⟨f, -, -, hd⟩ := h (fun _ => 100) evt008_cfg [] _ evs s s' hs (.actionTimedOut "t")
    (by simp [hev]) rfl
  simp [evt010_zeroDurExec, evt010_zeroDur] at hd

/-- ✗ Reporting the time elapsed since the firing started violates the payload block. `t` starts
at reading 0 and its budget of 100 ms runs out at the host reading of the expiry step; this
executor reports that reading less 0, not 100. It steps and emits as the reference, so it meets
the first block. -/
@[evidence mutant EVT_010_payload]
theorem EVT_010_payload_mutant_elapsed :
    evt010_ExMeets (evt010_elapsedDurExec (N := Nat) (T := Nat)) ∧
      ¬ EVT_010_payload (evt010_elapsedDurExec (N := Nat) (T := Nat)) := by
  refine ⟨EVT_010_reference, fun h => ?_⟩
  obtain ⟨s, s', evs, hs, hp⟩ := evt008_check polJT evt008_cfg evt010_beforeExpire
    (.expire 0 evt008_tout)
    (fun s evs => evs == [.actionTimedOut "t"] &&
      evt010_elapsedDur (fun _ => 100) evt008_cfg s (.expire 0 evt008_tout) (.actionTimedOut "t")
        != 100)
    (by decide +kernel)
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hp
  obtain ⟨f, -, -, hd⟩ := h (fun _ => 100) evt008_cfg [] _ evs s s' hs (.actionTimedOut "t")
    (by simp [hp.1]) rfl
  exact hp.2 hd

end Libpetri.Spec
