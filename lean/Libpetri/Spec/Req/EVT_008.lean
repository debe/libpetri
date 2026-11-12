import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Events
import Libpetri.Spec.Req.EXEC_021

set_option linter.missingDocs true

/-!
# EVT-008: TransitionFailed Event (`spec/08-events-observability.md`)

When a firing fails, the executor reports it with one `TransitionFailed` event naming the
transition, and it reports a failure at no other time. A firing fails for one of three causes
([EXEC-021], [EXEC-030]): its action throws or returns an error, output validation or the
join-relay check of [NU-054] rejects the tokens it returned, or the join-relay check rejects its
timeout outcome (ruling D24 (a)). In the executor model all three settle the firing in a
`fail i` step.

The block `EVT_008` is a predicate over an abstract executor with events `E : EvExec N T`
(`Reference/Events.lean`). It reads an event through its kind and the transition name it
carries, which every runtime's event has. Line 1: a fail step emits exactly one
`TransitionFailed`, it names the failed firing's transition, and the step emits no
`TransitionCompleted` and no `TokenAdded`. Line 2: nothing else emits a `TransitionFailed`,
neither another step nor the boot of a run. The error message and the exception type the event
carries are not modelled.

The witness is the reference executor with events `refEvExec` under both emission variants. The
wrong executors step as the reference and emit otherwise: one that reports nothing when
validation rejects the returned tokens, one that reports the failure twice, one that also
reports the failed firing as completed, one that reports the rejected tokens as added, one that
names no transition, one that reports a deposited timeout outcome as a failure, and one that
reports every transition as failed when the run boots.

The block reads "a firing fails" as "the executor settles it in a fail step". EXEC-021 anchors
that reading on the underlying executor (`evt008_asCompleted_anchored`): an executor that
settles a thrown action with a commit step meets `EVT_008` alone, and its steps break EXEC-021.

The worked example (`evt008_cfg`): transition `t` takes the two tokens 7 and 8 from place 0. Its
output spec is "a token in place 1, or, if the action's budget runs out, the two inputs forwarded
to place 2". The run shows each cause of a failure once: the action throws; the action returns a
token for place 2 only, which validation rejects; and, with a join-relay check that rejects every
token for place 2, the budget runs out and the timeout outcome is rejected.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## EVT-008: one failure event per failed firing, and only then -/

requirement EVT_008
  id "EVT-008"
  title "TransitionFailed Event"
  kind B
  scope "all executors (event store enabled)"
  source verbatim "spec/08-events-observability.md"
  quote "*If* a firing fails, because its action throws an exception or returns an error or because output validation or the join-relay check of [NU-054] rejects its outcome ([EXEC-021], [EXEC-030]), *then* the executor *shall* emit exactly one TransitionFailed event naming the firing's transition, and *shall not* emit a TransitionCompleted event or a TokenAdded event when it settles that firing."
        "The executor *shall* emit TransitionFailed events only when a firing fails."
  reading "For every executor with events E and every configuration C:"
          "for every history H of the events emitted before the step, a fail step of a firing identity i, from state s to state s', that appends the events evs, appends exactly one event of kind TransitionFailed; if f is the firing with identity i in flight in s, evs contains the TransitionFailed event naming f's transition; and no event of evs is a TransitionCompleted or a TokenAdded;"
          "the events a run emits before its first step contain no TransitionFailed event, whatever the initial marking, and for every history H a step whose label is not a fail step appends no TransitionFailed event."
  assumes "The model is an executor with events E : EvExec N T (Reference/Events.lean): the events a run emits before its first step, and a step relation E.step C H s l evs s' saying that the step labelled l leads from s to s' and appends the events evs, given the events H emitted before it. The witness is the reference executor with events refEvExec, the reference executor RefExec with its emission refEmitW, under both emission variants (polJT for Java and TypeScript, polRust for Rust and Python). refEvExec_erase (Reference/EventsLink.lean) shows that it steps exactly as RefExec, so the block constrains what is emitted and nothing else. Both lines hold for every history H."
          "Naming: a failed firing is one the executor settles in a fail step (label fail i), the label EXEC-021 and EXEC-030 use. The model has one fail label for the three causes the first quoted sentence lists (failCause, Reference/Exec.lean): the action threw or returned an error (outcome err); output validation or the join-relay check rejected a returned emission; the join-relay check rejected a timeout outcome (ruling D24 (a): the timeout outcome is not validated against the output spec, and the join-relay check still runs on it). The lead-in sentence of the section and the quoted sentence name all three, as EXEC-021, EXEC-030 and every runtime do (clash evt-a#11, ruling D17). The fail label is what anchors the word: EXEC-021 lets a commit step settle only a returned emission that passes output validation and the join-relay check, and a timeout deposit only a timeout outcome the check accepts, so on an executor whose underlying executor E.erase meets EXEC-021 a failed firing has no settle step other than a fail step. EVT_008 alone does not say this: an executor that settles a thrown action with a commit step emitting a TransitionCompleted never takes a fail step for it and meets EVT_008, and its underlying executor breaks EXEC-021 (evt008_asCompleted_anchored). The event blocks are joined to the executor theorem through E.erase for that reason (ConsistencyEvents.lean). Rust: emit_out_violation for a validation rejection, the relay_check branches and the Err branches of fire_transition_sync and handle_completion (rust/libpetri-runtime/src/executor_core/executor.rs 787-818, 880-890, 921-931, 1286-1299, 1329-1339); Java: handleTransitionFailure, called from processCompletedTransitions when the action failed or validateOutput threw (java/src/main/java/org/libpetri/runtime/BitmapNetExecutor.java 1883-1950); TypeScript: the flight.error branch and the catch of the validation block (typescript/src/runtime/bitmap-net-executor.ts 1228-1240 and 1298-1308)."
          "Line 1 is the first quoted sentence. Exactly one TransitionFailed: an executor that settles a rejected completion silently breaks it (EVT_008_mutant_silentRejection), and so does one that reports a thrown action twice (EVT_008_mutant_reportedTwice). It names the failed firing's transition: an executor that names none breaks it (EVT_008_mutant_anonymous). No TransitionCompleted and no TokenAdded: an executor that also reports the failed firing as completed (EVT_008_mutant_failedAndCompleted), or that reports the tokens validation rejected as added (EVT_008_mutant_rejectedReported), breaks it. AC1 (emitted when the action fails) is line 1 for the first cause; that a fail step is offered at all when an action fails is coverage, not a line here (ExecFailCovers, a clause of the consistency theorem's ExecCoversW5, ConsistencyExec.lean, which the reference meets)."
          "Line 1 does not fix where the TransitionFailed lies among the events of the step, and it allows an ActionTimedOut in the step: Rust settles a timeout outcome the join-relay check rejects with ActionTimedOut and then TransitionFailed (handle_completion, executor_core/executor.rs 1250-1299), while Java and TypeScript emit the ActionTimedOut from the action's timer (EVT-010's subject). Tokens the action published before it failed are not the fail step's: a publish step deposits them with their own TokenAdded events (ruling D17, EXEC-021 line 2). 'When it settles that firing' is the fail step: a TransitionCompleted naming the failed firing's transition in a later step (for example in the step that ends the completion phase, after the fail step) is not this block's subject. Which steps may emit a TransitionCompleted is EVT-007's."
          "Line 2 is the second quoted sentence: nothing but a fail step emits a TransitionFailed, neither the boot of a run nor a step with another label. An executor that reports a deposited timeout outcome as a failure breaks it (EVT_008_mutant_failOnTimeout), and so does one that reports every transition as failed at boot (EVT_008_mutant_bootFailed). Java and TypeScript validate a timeout outcome against the whole output spec and fail the firing where the reference deposits it (runtime defect RD-01, which breaks EXEC-021, EXEC-022 and IO-013). In such a run the event still marks a firing the runtime fails, so the defect is in which firings fail, not in when the event is emitted, and this block does not depend on it."
          "Not encoded: the payload, two sentences of the section left to a payload block of EVT-008 (rulings D33 (a) and D38 (a)). The first: Each TransitionFailed event *shall* carry the error message of the failure. The second, scoped to the executors whose event has the field: *Where* the TransitionFailed event carries the exception type (Java and TypeScript), it *shall* carry the name of the exception type of the failure. The model's event carries the transition name only (NetEvent.transitionFailed, GlossaryEvents.lean), and its failed outcome carries no error (Outcome.err), so neither sentence, nor AC2 (the error message is captured, and the exception type name where the event carries it), has a line here; a payload block needs an error on the failed outcome first. Java's event has errorMessage and exceptionType, the message and the class name of the failure's exception (java/src/main/java/org/libpetri/event/NetEvent.java TransitionFailed, BitmapNetExecutor.java handleTransitionFailure; the message is null for an exception that has none), TypeScript's errorMessage, exceptionType (the error's name) and an optional stack (typescript/src/event/net-event.ts), and Rust's one error text and no type (rust/libpetri-event/src/net_event.rs TransitionFailed), which Python passes on (rust/libpetri-py/src/events.rs). Of the fields the lead-in lists, the transition name is line 1, the error message and the exception type name are the two payload sentences, and the timestamp, which the executor's epoch clock stamps ([TIME-015]), is not modelled (the epoch clock is the CORE-011 slice)."
          "Assumptions shared by the executor event blocks: the event store is enabled and its append does not fail (EVT-020); no host callback throws inside a start or a deposit (Java and TypeScript report a throw of the execution-context provider after TransitionStarted, or of the event store in the middle of a deposit, as a TransitionFailed of a partly started or partly deposited firing: BitmapNetExecutor.java fireTransitionGuarded and processCompletedTransitions, bitmap-net-executor.ts fireTransitionContained 976-1010; no spec sentence describes these cases, and the model's start and deposit are atomic); an event is a value (EVT-001); transition names are distinct (ruling D10). A fault of the host runtime itself (Java's VirtualMachineError or LinkageError) is not a failure of a firing (EXEC-030). The events of one step are contiguous in the model, since a step appends its events at once. Java appends ActionTimedOut events and the log messages it captures from actions from other threads than the orchestrator (java/src/main/java/org/libpetri/runtime/ExecutorSupport.java 570-578, BitmapNetExecutor.java 1749-1752 and 2509-2512; LogCaptureScope.java 87-110), so in a Java store such an event can fall between the events of one step; the lines are read on the store with those events left out, as the reading at the top of spec/08-events-observability.md says. TypeScript and Rust append every event from the orchestrator."
          "The test derivation (an action throws, verify TransitionFailed with error details) is EVT_008_nonvacuous for the event and its transition name: each of the three causes settles transition t in a fail step that emits one TransitionFailed naming t (with Rust's ActionTimedOut before it for the rejected timeout outcome), while a commit and a timeout deposit emit events, none a TransitionFailed, and so does the boot of the run."
  signoff "pending"
  statement : ∀ {N T : Type} [DecidableEq N], EvExec N T → Prop :=
    fun E => ∀ C,
      (∀ H i evs, on (fun s s' => E.step C H s (.fail i) evs s'), shall (fun s _ =>
          kindCount .transitionFailed evs = 1 ∧
          (∀ f, s.fl.find? (·.id == i) = some f → NetEvent.transitionFailed f.t.core.name ∈ evs) ∧
          ∀ e ∈ evs, e.kind ≠ .transitionCompleted ∧ e.kind ≠ .tokenAdded)) ∧
      ((∀ M0, ∀ e ∈ E.boot C M0, e.kind ≠ .transitionFailed) ∧
        ∀ H l evs, (∀ i, l ≠ .fail i) →
          on (fun s s' => E.step C H s l evs s'), shall (fun _ _ =>
            ∀ e ∈ evs, e.kind ≠ .transitionFailed))

/- The pinned readable form of EVT-008: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EVT_008 : {N T : Type} → [DecidableEq N] → EvExec N T → Prop :=
fun {N T} [DecidableEq N] E =>
  ∀ (C : Cfg N T),
    (∀ (H : List (NetEvent N T)) (i : ℕ) (evs : List (NetEvent N T)),
        on fun s s' => E.step C H s (XLbl.fail i) evs s', shall fun s x =>
          kindCount NetEventKind.transitionFailed evs = 1 ∧
            (∀ (f : Firing N T),
                List.find? (fun x => x.id == i) s.fl = some f → NetEvent.transitionFailed f.t.core.name ∈ evs) ∧
              ∀ e ∈ evs, e.kind ≠ NetEventKind.transitionCompleted ∧ e.kind ≠ NetEventKind.tokenAdded) ∧
      (∀ (M0 : QMarking N T), ∀ e ∈ E.boot C M0, e.kind ≠ NetEventKind.transitionFailed) ∧
        ∀ (H : List (NetEvent N T)) (l : XLbl N T) (evs : List (NetEvent N T)),
          (∀ (i : ℕ), l ≠ XLbl.fail i) →
            on fun s s' => E.step C H s l evs s', shall fun x x_1 => ∀ e ∈ evs, e.kind ≠ NetEventKind.transitionFailed
-/
#guard_msgs in #print EVT_008

/-! ## The two lines, one at a time -/

section Lines

variable {N T : Type} [DecidableEq N] [Ord N]
/-- Line 1 of `EVT_008` alone: a fail step emits one `TransitionFailed`, naming the failed
firing's transition, and no `TransitionCompleted` and no `TokenAdded`. -/
def evt008_line1 (E : EvExec N T) : Prop :=
  ∀ C H i evs, on (fun s s' => E.step C H s (.fail i) evs s'), shall (fun s _ =>
    kindCount .transitionFailed evs = 1 ∧
    (∀ f, s.fl.find? (·.id == i) = some f → NetEvent.transitionFailed f.t.core.name ∈ evs) ∧
    ∀ e ∈ evs, e.kind ≠ .transitionCompleted ∧ e.kind ≠ .tokenAdded)

/-- Line 2 of `EVT_008` alone: nothing but a fail step emits a `TransitionFailed`, neither the
boot nor a step with another label. -/
def evt008_line2 (E : EvExec N T) : Prop :=
  ∀ C, (∀ M0, ∀ e ∈ E.boot C M0, e.kind ≠ .transitionFailed) ∧
    ∀ H l evs, (∀ i, l ≠ .fail i) →
      on (fun s s' => E.step C H s l evs s'), shall (fun _ _ =>
        ∀ e ∈ evs, e.kind ≠ .transitionFailed)

omit [Ord N] in
/-- `EVT_008` is its two lines. -/
theorem evt008_iff (E : EvExec N T) : EVT_008 E ↔ evt008_line1 E ∧ evt008_line2 E :=
  ⟨fun h => ⟨fun C => (h C).1, fun C => (h C).2⟩,
   fun h C => ⟨h.1 C, h.2 C⟩⟩

end Lines

/-! ## The reference -/

section Reference

variable {N T : Type} [DecidableEq N] [Ord N]
/-- The events of a reference fail step: under the Rust emission an `ActionTimedOut` when the
failed outcome is a timeout outcome, then the `TransitionFailed` of the firing's transition. -/
theorem refEmitW_fail (P : EvPol) (C : Cfg N T) (H : List (NetEvent N T)) {s : XSt N T}
    {i : Nat} {f : Firing N T} (hf : s.fl.find? (·.id == i) = some f) (s' : XSt N T) :
    refEmitW P C H s (.fail i) s' =
      (if !P.atoAtExpire && isTimeoutOut f then [.actionTimedOut f.t.core.name] else []) ++
        [.transitionFailed f.t.core.name] := by
  simp only [refEmitW, hf]

/-- Only a fail step emits a `TransitionFailed` in the reference. -/
theorem refEmitW_noFailed (P : EvPol) (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T)
    {l : XLbl N T} (hl : ∀ i, l ≠ .fail i) (s' : XSt N T) :
    ∀ e ∈ refEmitW P C H s l s', e.kind ≠ .transitionFailed := by
  intro e he hk
  have := refEmitW_kind P C H s l s' e he
  rw [hk] at this
  cases l with
  | fail i => exact hl i rfl
  | _ => simp [lblKinds] at this

/-- The reference boot emits no `TransitionFailed`. -/
theorem refBoot_noFailed (P : EvPol) (C : Cfg N T) (M0 : QMarking N T) :
    ∀ e ∈ refBoot P C M0, e.kind ≠ .transitionFailed := by
  intro e he hk
  rcases refBoot_kind P C M0 e he with h | h <;> rw [hk] at h <;> cases h

/-- Line 1 holds of the events a reference fail step emits. -/
theorem refFail_line1 (P : EvPol) (C : Cfg N T) (H : List (NetEvent N T)) {s s' : XSt N T}
    {i : Nat} (hx : xstep C s (.fail i) = some s') :
    kindCount .transitionFailed (refEmitW P C H s (.fail i) s') = 1 ∧
    (∀ f, s.fl.find? (·.id == i) = some f →
      NetEvent.transitionFailed f.t.core.name ∈ refEmitW P C H s (.fail i) s') ∧
    ∀ e ∈ refEmitW P C H s (.fail i) s', e.kind ≠ .transitionCompleted ∧ e.kind ≠ .tokenAdded := by
  obtain ⟨f, hf, -, -, -⟩ := failStep_some (P := refXPol) hx
  rw [refEmitW_fail P C H hf s']
  refine ⟨?_, fun g hg => ?_, ?_⟩
  · split <;> simp [kindCount, NetEvent.kind]
  · rw [hf] at hg
    cases hg
    simp
  · intro e he
    simp only [List.mem_append, List.mem_singleton] at he
    rcases he with h | rfl
    · split at h
      · simp only [List.mem_singleton] at h; subst h; simp [NetEvent.kind]
      · cases h
    · simp [NetEvent.kind]

/-- The reference meets `EVT_008` under every emission variant. -/
theorem evt008_ref (P : EvPol) : EVT_008 (refEvExec (N := N) (T := T) P) :=
  (evt008_iff _).2
    ⟨fun C H i evs s s' hs => by
      obtain ⟨hx, rfl⟩ := hs
      exact refFail_line1 P C H hx,
     fun C => ⟨refBoot_noFailed P C, fun H l evs hl s s' hs => by
      obtain ⟨-, rfl⟩ := hs
      exact refEmitW_noFailed P C H s hl s'⟩⟩

/-- ✓ The reference executor with the Java and TypeScript emission meets EVT-008: a failed
firing is reported once, under its transition's name, with no completion and no added token,
and no other step reports a failure. -/
@[evidence holds EVT_008]
theorem EVT_008_reference : EVT_008 (refEvExec (N := N) (T := T) polJT) := evt008_ref polJT

/-- ✓ The reference executor with the Rust and Python emission meets EVT-008 too, although its
fail step for a rejected timeout outcome also emits an `ActionTimedOut` first. -/
@[evidence holds EVT_008]
theorem EVT_008_rust : EVT_008 (refEvExec (N := N) (T := T) polRust) := evt008_ref polRust

end Reference

/-! ## The worked example -/

/-- Transition `t`: takes exactly two tokens from place 0; output spec `Xor(Place(1),
Timeout(d, ForwardInput(0, 2)))`. -/
def evt008_t : Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .exactly 2⟩], inhibitors := [], reads := [],
              resets := [] },
    out := some (.xor (.place 1) (.timeout (.forward 0 2))) }

/-- The configuration of the example: places 0 to 2 and transition `t`. Output validation
accepts a completion only if it produced a token in place 1 (the normal branch of `t`'s spec);
the join-relay check accepts everything; any emission may be the timeout outcome. -/
def evt008_cfg : Cfg Nat Nat :=
  { X := { net := { places := [0, 1, 2], transitions := [evt008_t] },
           timing := fun _ => .immediate, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [], reentrant := false,
    validate := fun _ d => d.contains 1, relay := fun _ _ _ => true,
    timeoutOut := fun _ _ _ => true, res := 0 }

/-- The example configuration with a join-relay check that rejects every token for place 2. -/
def evt008_cfgRelay : Cfg Nat Nat :=
  { evt008_cfg with relay := fun _ _ e => e.all fun x => x.1 != 2 }

/-- The initial marking: 7 and 8 in place 0. -/
def evt008_m0 : QMarking Nat Nat := fun p => if p = 0 then [7, 8] else []

/-- One cycle up to the asynchronous start of `t`. -/
def evt008_pre : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin, .start "t" false]

/-- The timeout outcome of the example: 7 and 8 forwarded to place 2. -/
def evt008_tout : List (Nat × Nat) := [(2, 7), (2, 8)]

/-- `t`'s action throws; the loop ends the pass and is back in step 1. -/
def evt008_throws : Option (XSt Nat Nat) :=
  xrun evt008_cfg (xinit evt008_m0 0) (evt008_pre ++ [.ret 0 false, .endPass])

/-- `t`'s action returns the token 5 for place 2 only, which validation rejects. -/
def evt008_rejected : Option (XSt Nat Nat) :=
  xrun evt008_cfg (xinit evt008_m0 0) (evt008_pre ++ [.write 0 2 5, .ret 0 true, .endPass])

/-- `t`'s action returns the token 50 for place 1, which validation accepts. -/
def evt008_returned : Option (XSt Nat Nat) :=
  xrun evt008_cfg (xinit evt008_m0 0) (evt008_pre ++ [.write 0 1 50, .ret 0 true, .endPass])

/-- `t`'s budget runs out first, with timeout outcome `evt008_tout`, under configuration `C`. -/
def evt008_expired (C : Cfg Nat Nat) : Option (XSt Nat Nat) :=
  xrun C (xinit evt008_m0 0) (evt008_pre ++ [.expire 0 evt008_tout, .endPass])

/-- The firing's outcome is an error (the action threw). -/
def evt008_isErr (f : Firing Nat Nat) : Bool :=
  match f.out with
  | some .err => true
  | _ => false

/-- The firing's outcome is a returned emission. -/
def evt008_isOk (f : Firing Nat Nat) : Bool :=
  match f.out with
  | some (.ok _) => true
  | _ => false

/-- The firing with identity 0 in `s` exists and passes `p`. -/
def evt008_fl0 (s : XSt Nat Nat) (p : Firing Nat Nat → Bool) : Bool :=
  (s.fl.find? (·.id == 0)).any p

/-- Read a decided fact off a fail-or-other step of the reference: the step exists and its
events, under variant `P`, pass `q`. -/
theorem evt008_check (P : EvPol) (C : Cfg Nat Nat) (o : Option (XSt Nat Nat)) (l : XLbl Nat Nat)
    (q : XSt Nat Nat → List (NetEvent Nat Nat) → Bool)
    (h : (o.bind fun s => (xstep C s l).map fun s' => q s (refEmitW P C [] s l s')) = some true) :
    ∃ s s' evs, (refEvExec P).step C [] s l evs s' ∧ q s evs = true := by
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := C) (o := o) (l := l)
    (p := fun s s' => q s (refEmitW P C [] s l s')) h
  exact ⟨s, s', _, ⟨hs, rfl⟩, hp⟩

/-- ✓ Both lines are exercised by the reference, with each cause of a failure once. `t`'s action
throws: the fail step emits exactly `TransitionFailed t`. `t`'s action returns 5 for place 2,
which validation rejects: again exactly `TransitionFailed t`. `t`'s budget runs out and the
join-relay check rejects the timeout outcome (7 and 8 for place 2): under the Rust emission the
fail step emits `ActionTimedOut t`, then `TransitionFailed t`. A returned 50 for place 1 is
committed with a `TokenAdded` and a `TransitionCompleted`, a timeout outcome the check accepts is
deposited with two `TokenAdded` events, and the boot emits `ExecutionStarted` and a snapshot:
none of these is a `TransitionFailed`. -/
@[evidence nonvacuous EVT_008]
theorem EVT_008_nonvacuous :
    (∃ s s' evs, (refEvExec polJT).step evt008_cfg [] s (.fail 0) evs s' ∧
      evt008_fl0 s evt008_isErr = true ∧ evs = [.transitionFailed "t"]) ∧
    (∃ s s' evs, (refEvExec polJT).step evt008_cfg [] s (.fail 0) evs s' ∧
      evt008_fl0 s evt008_isOk = true ∧ evs = [.transitionFailed "t"]) ∧
    (∃ s s' evs, (refEvExec polRust).step evt008_cfgRelay [] s (.fail 0) evs s' ∧
      evt008_fl0 s isTimeoutOut = true ∧ evs = [.actionTimedOut "t", .transitionFailed "t"]) ∧
    (∃ s s' evs, (refEvExec polJT).step evt008_cfg [] s (.commit 0) evs s' ∧ evs ≠ [] ∧
      ∀ e ∈ evs, e.kind ≠ .transitionFailed) ∧
    (∃ s s' evs, (refEvExec polRust).step evt008_cfg [] s (.tdeposit 0) evs s' ∧ evs ≠ [] ∧
      ∀ e ∈ evs, e.kind ≠ .transitionFailed) ∧
    ((refEvExec (N := Nat) (T := Nat) polJT).boot evt008_cfg evt008_m0 ≠ [] ∧
      ∀ e ∈ (refEvExec (N := Nat) (T := Nat) polJT).boot evt008_cfg evt008_m0,
        e.kind ≠ .transitionFailed) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, by decide +kernel⟩
  · obtain ⟨s, s', evs, hs, hp⟩ := evt008_check polJT evt008_cfg evt008_throws (.fail 0)
      (fun s evs => evt008_fl0 s evt008_isErr && evs == [.transitionFailed "t"])
      (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', evs, hs, hp.1, hp.2⟩
  · obtain ⟨s, s', evs, hs, hp⟩ := evt008_check polJT evt008_cfg evt008_rejected (.fail 0)
      (fun s evs => evt008_fl0 s evt008_isOk && evs == [.transitionFailed "t"])
      (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', evs, hs, hp.1, hp.2⟩
  · obtain ⟨s, s', evs, hs, hp⟩ := evt008_check polRust evt008_cfgRelay
      (evt008_expired evt008_cfgRelay) (.fail 0)
      (fun s evs => evt008_fl0 s isTimeoutOut &&
        evs == [.actionTimedOut "t", .transitionFailed "t"])
      (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', evs, hs, hp.1, hp.2⟩
  · obtain ⟨s, s', evs, hs, hp⟩ := evt008_check polJT evt008_cfg evt008_returned (.commit 0)
      (fun _ evs => !evs.isEmpty && evs.all fun e => e.kind != .transitionFailed)
      (by decide +kernel)
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
      List.all_eq_true, bne_iff_ne, ne_eq] at hp
    exact ⟨s, s', evs, hs, hp.1, hp.2⟩
  · obtain ⟨s, s', evs, hs, hp⟩ := evt008_check polRust evt008_cfg (evt008_expired evt008_cfg)
      (.tdeposit 0)
      (fun _ evs => !evs.isEmpty && evs.all fun e => e.kind != .transitionFailed)
      (by decide +kernel)
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
      List.all_eq_true, bne_iff_ne, ne_eq] at hp
    exact ⟨s, s', evs, hs, hp.1, hp.2⟩

/-! ## Wrong executors: the reference's steps, another emission -/

section Mutants

variable {N T : Type} [DecidableEq N] [Ord N]
/-- The Java and TypeScript emission with the events of a fail step replaced by `g C s i`. -/
def evt008_atFail (g : Cfg N T → XSt N T → Nat → List (NetEvent N T)) (C : Cfg N T)
    (H : List (NetEvent N T)) (s : XSt N T) (l : XLbl N T) (s' : XSt N T) : List (NetEvent N T) :=
  match l with
  | .fail i => g C s i
  | _ => refEmitW polJT C H s l s'

/-- An executor that only changes what a fail step emits keeps line 2. -/
theorem evt008_atFail_line2 (g : Cfg N T → XSt N T → Nat → List (NetEvent N T)) :
    evt008_line2 (emitExec (refBoot polJT) (evt008_atFail g)) := by
  intro C
  refine ⟨refBoot_noFailed polJT C, fun H l evs hl s s' hs => ?_⟩
  obtain ⟨-, rfl⟩ := hs
  have he : evt008_atFail g C H s l s' = refEmitW polJT C H s l s' := by
    cases l with
    | fail i => exact absurd rfl (hl i)
    | _ => rfl
  rw [he]
  exact refEmitW_noFailed polJT C H s hl s'

/-- An executor that emits as the reference at a fail step keeps line 1, whatever its boot. -/
theorem evt008_line1_of_refFail {boot : Cfg N T → QMarking N T → List (NetEvent N T)}
    {emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    (he : ∀ C H s i s', emit C H s (.fail i) s' = refEmitW polJT C H s (.fail i) s') :
    evt008_line1 (emitExec boot emit) := by
  intro C H i evs s s' hs
  obtain ⟨hx, rfl⟩ := hs
  rw [he]
  exact refFail_line1 polJT C H hx

/-- The fail events with nothing for a returned emission that validation or the join-relay check
rejected. -/
def evt008_silentEvs (_C : Cfg N T) (s : XSt N T) (i : Nat) : List (NetEvent N T) :=
  match s.fl.find? (·.id == i) with
  | some f =>
    match f.out with
    | some (.ok _) => []
    | _ => [.transitionFailed f.t.core.name]
  | none => []

/-- The executor that settles a rejected completion without an event. -/
def evt008_silent : EvExec N T := emitExec (refBoot polJT) (evt008_atFail evt008_silentEvs)

/-- The fail events with the `TransitionFailed` of the failed firing twice. -/
def evt008_twiceEvs (_C : Cfg N T) (s : XSt N T) (i : Nat) : List (NetEvent N T) :=
  match s.fl.find? (·.id == i) with
  | some f => [.transitionFailed f.t.core.name, .transitionFailed f.t.core.name]
  | none => []

/-- The executor that reports every failed firing twice. -/
def evt008_twice : EvExec N T := emitExec (refBoot polJT) (evt008_atFail evt008_twiceEvs)

/-- The fail events with a `TransitionCompleted` after the `TransitionFailed`. -/
def evt008_bothEvs (_C : Cfg N T) (s : XSt N T) (i : Nat) : List (NetEvent N T) :=
  match s.fl.find? (·.id == i) with
  | some f => [.transitionFailed f.t.core.name, .transitionCompleted f.t.core.name [] 0]
  | none => []

/-- The executor that reports a failed firing as failed and as completed. -/
def evt008_both : EvExec N T := emitExec (refBoot polJT) (evt008_atFail evt008_bothEvs)

/-- The fail events with a `TokenAdded` for each token of a rejected returned emission first. -/
def evt008_reportedEvs (_C : Cfg N T) (s : XSt N T) (i : Nat) : List (NetEvent N T) :=
  match s.fl.find? (·.id == i) with
  | some f =>
    (match f.out with
     | some (.ok e) => addedEvs e
     | _ => []) ++ [.transitionFailed f.t.core.name]
  | none => []

/-- The executor that reports the tokens validation rejected as added, then the failure. -/
def evt008_reported : EvExec N T := emitExec (refBoot polJT) (evt008_atFail evt008_reportedEvs)

/-- The fail events with a `TransitionFailed` that names no transition. -/
def evt008_anonEvs (_C : Cfg N T) (s : XSt N T) (i : Nat) : List (NetEvent N T) :=
  match s.fl.find? (·.id == i) with
  | some _ => [.transitionFailed ""]
  | none => []

/-- The executor that reports a failure under the empty name. -/
def evt008_anon : EvExec N T := emitExec (refBoot polJT) (evt008_atFail evt008_anonEvs)

/-- The Java and TypeScript emission with a `TransitionFailed` after a deposited timeout
outcome. -/
def evt008_timeoutEmit (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T) (l : XLbl N T)
    (s' : XSt N T) : List (NetEvent N T) :=
  match l with
  | .tdeposit i =>
    refEmitW polJT C H s l s' ++
      match s.fl.find? (·.id == i) with
      | some f => [.transitionFailed f.t.core.name]
      | none => []
  | _ => refEmitW polJT C H s l s'

/-- The executor that reports a deposited timeout outcome as a failure as well. -/
def evt008_failOnTimeout : EvExec N T := emitExec (refBoot polJT) evt008_timeoutEmit

/-- The Java and TypeScript boot events followed by a `TransitionFailed` for every transition of
the net. -/
def evt008_bootFailedEvs (C : Cfg N T) (M0 : QMarking N T) : List (NetEvent N T) :=
  refBoot polJT C M0 ++ C.X.net.transitions.map fun t => .transitionFailed t.core.name

/-- The executor that steps and emits as the reference but reports every transition as failed
when the run boots. -/
def evt008_bootFailed : EvExec N T := emitExec evt008_bootFailedEvs (refEmitW polJT)

end Mutants

/-- ✗ Settling a rejected completion without an event violates EVT-008 (line 1): `t`'s action
returns 5 for place 2, validation rejects it, and the fail step emits nothing. The executor
keeps line 2. -/
@[evidence mutant EVT_008]
theorem EVT_008_mutant_silentRejection :
    evt008_line2 (evt008_silent (N := Nat) (T := Nat)) ∧
      ¬ EVT_008 (evt008_silent (N := Nat) (T := Nat)) := by
  refine ⟨evt008_atFail_line2 _, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt008_cfg) (o := evt008_rejected)
    (l := .fail 0)
    (p := fun s _ => kindCount .transitionFailed (evt008_silentEvs evt008_cfg s 0) != 1)
    (by decide +kernel)
  simp only [bne_iff_ne, ne_eq] at hp
  exact hp ((h evt008_cfg).1 [] 0 _ s s' ⟨hs, rfl⟩).1

/-- ✗ Reporting a failure twice violates EVT-008 (line 1): when `t`'s action throws, the fail step
emits `TransitionFailed t` two times. Both name `t` and the step reports no completion, so only
"exactly one" is broken. The executor keeps line 2. -/
@[evidence mutant EVT_008]
theorem EVT_008_mutant_reportedTwice :
    evt008_line2 (evt008_twice (N := Nat) (T := Nat)) ∧
      ¬ EVT_008 (evt008_twice (N := Nat) (T := Nat)) := by
  refine ⟨evt008_atFail_line2 _, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt008_cfg) (o := evt008_throws)
    (l := .fail 0)
    (p := fun s _ => kindCount .transitionFailed (evt008_twiceEvs evt008_cfg s 0) != 1)
    (by decide +kernel)
  simp only [bne_iff_ne, ne_eq] at hp
  exact hp ((h evt008_cfg).1 [] 0 _ s s' ⟨hs, rfl⟩).1

/-- ✗ Reporting a failed firing as completed too violates EVT-008 (line 1): when `t`'s action
throws, the fail step emits `TransitionFailed t` and then `TransitionCompleted t`. The executor
keeps line 2. -/
@[evidence mutant EVT_008]
theorem EVT_008_mutant_failedAndCompleted :
    evt008_line2 (evt008_both (N := Nat) (T := Nat)) ∧
      ¬ EVT_008 (evt008_both (N := Nat) (T := Nat)) := by
  refine ⟨evt008_atFail_line2 _, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt008_cfg) (o := evt008_throws)
    (l := .fail 0)
    (p := fun s _ => (evt008_bothEvs evt008_cfg s 0).any fun e => e.kind == .transitionCompleted)
    (by decide +kernel)
  simp only [List.any_eq_true, beq_iff_eq] at hp
  obtain ⟨e, he, hk⟩ := hp
  exact ((h evt008_cfg).1 [] 0 _ s s' ⟨hs, rfl⟩).2.2 e he |>.1 hk

/-- ✗ Reporting the tokens validation rejected as added violates EVT-008 (line 1): the fail step
of `t`'s rejected completion emits `TokenAdded` for 5 in place 2, although place 2 stays empty.
The executor keeps line 2. -/
@[evidence mutant EVT_008]
theorem EVT_008_mutant_rejectedReported :
    evt008_line2 (evt008_reported (N := Nat) (T := Nat)) ∧
      ¬ EVT_008 (evt008_reported (N := Nat) (T := Nat)) := by
  refine ⟨evt008_atFail_line2 _, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt008_cfg) (o := evt008_rejected)
    (l := .fail 0)
    (p := fun s _ => (evt008_reportedEvs evt008_cfg s 0).any fun e => e.kind == .tokenAdded)
    (by decide +kernel)
  simp only [List.any_eq_true, beq_iff_eq] at hp
  obtain ⟨e, he, hk⟩ := hp
  exact ((h evt008_cfg).1 [] 0 _ s s' ⟨hs, rfl⟩).2.2 e he |>.2 hk

/-- ✗ Reporting a failure under no transition's name violates EVT-008 (line 1): when `t`'s action
throws, the fail step emits one `TransitionFailed`, but it names the empty string, not `t`. The
executor keeps line 2. -/
@[evidence mutant EVT_008]
theorem EVT_008_mutant_anonymous :
    evt008_line2 (evt008_anon (N := Nat) (T := Nat)) ∧
      ¬ EVT_008 (evt008_anon (N := Nat) (T := Nat)) := by
  refine ⟨evt008_atFail_line2 _, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt008_cfg) (o := evt008_throws)
    (l := .fail 0)
    (p := fun s _ => (s.fl.find? (·.id == 0)).any fun f =>
      !(evt008_anonEvs evt008_cfg s 0).contains (.transitionFailed f.t.core.name))
    (by decide +kernel)
  simp only [Option.any_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at hp
  obtain ⟨f, hf, hn⟩ := hp
  exact hn (((h evt008_cfg).1 [] 0 _ s s' ⟨hs, rfl⟩).2.1 f hf)

/-- ✗ Reporting a deposited timeout outcome as a failure violates EVT-008 (line 2): `t`'s budget
runs out, the join-relay check accepts the outcome, 7 and 8 land in place 2, and the deposit
step emits a `TransitionFailed t` as well. Its fail steps emit as the reference, so it keeps
line 1. -/
@[evidence mutant EVT_008]
theorem EVT_008_mutant_failOnTimeout :
    evt008_line1 (evt008_failOnTimeout (N := Nat) (T := Nat)) ∧
      ¬ EVT_008 (evt008_failOnTimeout (N := Nat) (T := Nat)) := by
  refine ⟨evt008_line1_of_refFail fun _ _ _ _ _ => rfl, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt008_cfg)
    (o := evt008_expired evt008_cfg) (l := .tdeposit 0)
    (p := fun s s' => (evt008_timeoutEmit evt008_cfg [] s (.tdeposit 0) s').any
      fun e => e.kind == .transitionFailed)
    (by decide +kernel)
  simp only [List.any_eq_true, beq_iff_eq] at hp
  obtain ⟨e, he, hk⟩ := hp
  exact (h evt008_cfg).2.2 [] (.tdeposit 0) _ (fun _ => by simp) s s' ⟨hs, rfl⟩ e he hk

/-- ✗ Reporting every transition as failed when the run boots violates EVT-008 (line 2): the
boot of the example reports `TransitionFailed t` before `t` has even started. Every step of this
executor emits as the reference, so it keeps line 1. -/
@[evidence mutant EVT_008]
theorem EVT_008_mutant_bootFailed :
    evt008_line1 (evt008_bootFailed (N := Nat) (T := Nat)) ∧
      ¬ EVT_008 (evt008_bootFailed (N := Nat) (T := Nat)) := by
  refine ⟨evt008_line1_of_refFail fun _ _ _ _ _ => rfl, fun h => ?_⟩
  have hm : NetEvent.transitionFailed "t" ∈ evt008_bootFailed.boot evt008_cfg evt008_m0 := by
    decide +kernel
  exact (h evt008_cfg).2.1 evt008_m0 _ hm rfl

/-! ## What anchors the fail label: EXEC-021 on the underlying executor -/

section Anchor

variable {N T : Type} [DecidableEq N] [Ord N]
/-- The firing with identity `i` in flight in `s` threw. -/
def evt008_errIn (s : XSt N T) (i : Nat) : Bool :=
  (s.fl.find? (·.id == i)).any fun f => match f.out with
    | some .err => true
    | _ => false

/-- The events of a thrown action settled as a completion: a `TransitionCompleted` with no
produced tokens. -/
def evt008_asCompletedEvs (s : XSt N T) (i : Nat) : List (NetEvent N T) :=
  match s.fl.find? (·.id == i) with
  | some f => [.transitionCompleted f.t.core.name [] (s.now - f.start)]
  | none => []

/-- The steps of an executor that settles a thrown action with a commit step: the reference fail
step's state change, under the label `commit i`, emitting an empty `TransitionCompleted`. A
thrown action has no fail step; every other step is the reference's. -/
def evt008_asCompletedStep : XEvRel N T := fun C H s l evs s' =>
  match l with
  | .fail i => evt008_errIn s i = false ∧ (refEvExec polJT).step C H s (.fail i) evs s'
  | .commit i => (refEvExec polJT).step C H s (.commit i) evs s' ∨
      (evt008_errIn s i = true ∧ xstep C s (.fail i) = some s' ∧ evs = evt008_asCompletedEvs s i)
  | l => (refEvExec polJT).step C H s l evs s'

/-- The executor that settles a thrown action as an empty completion. -/
def evt008_asCompleted : EvExec N T := { boot := refBoot polJT, step := evt008_asCompletedStep }

/-- `EVT_008` alone accepts it: its fail steps are reference fail steps, and its extra commit
steps emit a `TransitionCompleted`, not a `TransitionFailed`. -/
theorem evt008_asCompleted_meets : EVT_008 (evt008_asCompleted (N := N) (T := T)) := by
  intro C
  refine ⟨fun H i evs s s' hs => ?_, refBoot_noFailed polJT C, fun H l evs hl s s' hs => ?_⟩
  · obtain ⟨-, hx, rfl⟩ := hs
    exact refFail_line1 polJT C H hx
  · intro e he hk
    cases l with
    | fail i => exact hl i rfl
    | commit i =>
      rcases hs with ⟨-, rfl⟩ | ⟨-, -, rfl⟩
      · exact refEmitW_noFailed polJT C H s hl s' e he hk
      · unfold evt008_asCompletedEvs at he
        split at he
        · simp only [List.mem_singleton] at he; subst he; simp [NetEvent.kind] at hk
        · cases he
    | _ =>
      obtain ⟨-, rfl⟩ := hs
      exact refEmitW_noFailed polJT C H s hl s' e he hk

end Anchor

/-- The example configuration's validation reads a set of places. -/
theorem evt008_cfg_set : evt008_cfg.SetValidated := by
  intro t d d' hd
  show d.contains 1 = d'.contains 1
  rw [Bool.eq_iff_iff]
  simp [hd 1]

/-- EVT-008 reads "a firing fails" as "the executor settles it in a fail step", and EXEC-021
makes that reading hold. Take an executor that settles a thrown action with a commit step: when
`t`'s action throws, it emits `TransitionCompleted t` with no tokens and takes no fail step. It
meets EVT-008, which constrains fail steps and `TransitionFailed` events only, but its steps
break EXEC-021, where a commit step settles only a returned emission that passes validation. -/
theorem evt008_asCompleted_anchored :
    EVT_008 (evt008_asCompleted (N := Nat) (T := Nat)) ∧
    (∃ s s' evs, (evt008_asCompleted (N := Nat) (T := Nat)).step evt008_cfg [] s (.commit 0) evs s' ∧
      evs = [.transitionCompleted "t" [] 0]) ∧
    ¬ EXEC_021 (evt008_asCompleted (N := Nat) (T := Nat)).erase := by
  refine ⟨evt008_asCompleted_meets, ?_, fun h => ?_⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt008_cfg) (o := evt008_throws)
      (l := .fail 0)
      (p := fun s _ => evt008_errIn s 0 &&
        (evt008_asCompletedEvs s 0 == [.transitionCompleted "t" [] 0]))
      (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', _, Or.inr ⟨hp.1, hs, rfl⟩, hp.2⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt008_cfg) (o := evt008_throws)
      (l := .fail 0)
      (p := fun s _ => evt008_errIn s 0 && s.fl.all fun f => f.id != 0 || match f.out with
        | some .err => true
        | _ => false)
      (by decide +kernel)
    simp only [Bool.and_eq_true] at hp
    have hstep : (evt008_asCompleted (N := Nat) (T := Nat)).erase evt008_cfg s (.commit 0) s' :=
      ⟨[], evt008_asCompletedEvs s 0, Or.inr ⟨hp.1, hs, rfl⟩⟩
    obtain ⟨f, hf, hid, e, he, -⟩ := ((h evt008_cfg evt008_cfg_set 0).1) s s' hstep
    have hall := List.all_eq_true.1 hp.2 f hf
    rw [hid, he] at hall
    simp at hall

end Libpetri.Spec
