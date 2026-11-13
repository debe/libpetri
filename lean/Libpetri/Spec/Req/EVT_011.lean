import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Events
import Libpetri.Spec.Text.EVT_011

set_option linter.missingDocs true

/-!
# EVT-011: TokenAdded Event (`spec/08-events-observability.md`)

Whenever the executor deposits tokens into a place, it reports each of them with one `TokenAdded`
event naming the place, and it reports additions at no other time. In particular it reports no
addition for the tokens of the initial marking (ruling D76 (a): no runtime does; the start
snapshot of [EVT-014] carries them where the executor emits one). The requirement has two blocks
with the same spec ID (rulings D33 (a) and D38 (a)):

* `EVT_011`, for every executor: it reads an event only through its kind and the place it names.
  Line 1 counts: per place, the queue after a step that is not a start is the queue before it
  followed by as many tokens as the step has `TokenAdded` events naming the place. Line 2: neither
  the boot of a run nor a start emits one, and a start only takes tokens.
* `EVT_011_payload`, for the executors whose event carries the token (Java and TypeScript; Rust
  and Python when the event store captures tokens): per place, the queue before a step that is not
  a start, followed by the tokens of the step's `TokenAdded` events naming it, in order, is the
  queue after it. The count line of the first block is this line with the tokens forgotten
  (`evt011_of_payload`).

The four steps of the reference executor that deposit are the settling of a completion that
passed output validation (`commit`), the settling of a timeout outcome (`tdeposit`), a mid-action
publication (`publish`) and an injection (`inject`); every other step that is not a start leaves
the marking as it is (`evt011_refStep`).

Both lines carry the part of the marking frame of [EXEC-020] that a count needs: a step that is not
a start only appends at the tail of a queue, and a start only takes tokens. Without it a deposit
could hide in a start, or behind a token the same step removes.

The witness is the reference executor with events `refEvExec`, under both emission variants. Most
wrong executors step as the reference and emit otherwise: one that reports one event per place
instead of one per token, one that reports an injection when it is requested instead of when it
lands, one that reports the initial marking as added at boot (the literal reading of the old
"whether from initial marking" clause), one that reports a read token as put back when a
transition starts, and one that reports the tokens of a place newest first. Two also step
otherwise: one whose synchronous start deposits its action's outputs and reports nothing for them,
and one that writes a completion's first output over the oldest token of its place and reports
no addition for it.

The worked example (`evt011_cfg`): a caller injects 5 into the environment place 2, which lands
in step 2 and is reported once. Then transition `a` takes 10 from place 0 and reads 20 from place
1; its synchronous action writes 7 and then 8 into place 1, and the completion reports both, in
that order, and place 1 goes from 20 to 20, 7, 8.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## EVT-011, every executor: one event per deposited token, only at a deposit -/

requirement EVT_011
  id "EVT-011"
  title "TokenAdded Event"
  kind B
  scope "all executors (event store enabled)"
  source verbatim "spec/08-events-observability.md"
  covers EVT_011.s1, EVT_011.s2, EVT_011.s3, EVT_011.s4
  reading "For every executor with events E and every configuration C:"
          "for every history H of the events emitted before the step, a step whose label is not a start, from state s to state s', that appends the events evs leaves, for every place p, p's queue in s' equal to p's queue in s followed by as many tokens as evs has TokenAdded events naming p;"
          "the events a run emits before its first step contain no TokenAdded event, whatever the initial marking, and for every history H a start step appends no TokenAdded event and leaves every place's queue a sublist of what it was."
  assumes "The model is an executor with events E : EvExec N T (Reference/Events.lean): the events a run emits before its first step, and a step relation E.step C H s l evs s' saying that the step labelled l leads from s to s' and appends the events evs, given the events H emitted before it. The witness is the reference executor with events refEvExec, the reference executor RefExec with its emission refEmitW, under both emission variants (polJT for Java and TypeScript, polRust for Rust and Python). refEvExec_erase (Reference/EventsLink.lean) shows that it steps exactly as RefExec, so on the witness the block constrains only what is emitted. Both lines hold for every history H."
          "The marking frame (EXEC-020): over an arbitrary E each line also carries the part of the frame that counting deposits needs. Line 1 asks a step that is not a start to keep the queue it found as a prefix, so it only appends at the tail; line 2 asks a start to leave every queue a sublist of what it was, so it only takes tokens. The reference meets both (evt011_refStep, evt011_refStart_frame). Without them a deposit could hide in a start, or behind a token the same step removes, and a count of queue lengths would not see it: an executor whose synchronous start also deposits its action's outputs and reports nothing breaks line 2 (EVT_011_mutant_silentStart), and one that writes a completion's first output over the oldest token of its place and reports no addition for it, although the length of the queue grows by the number of events it reports, breaks line 1 (EVT_011_mutant_overwrite)."
          "Main block and companion (rulings D33 (a) and D38 (a)): this block reads an event only through its kind and the place it names (addedCount counts the events of kind TokenAdded that name the place), which every executor's event carries. The token an event carries is read only by the second block of EVT-011, EVT_011_payload, scoped to the executors whose TokenAdded event carries it: in Rust and Python the event carries the token only when the event store captures tokens (rust/libpetri-runtime/src/executor_core/event_payload.rs token_added_event; event_store.rs CAPTURES_TOKENS, false by default). Line 1 is the payload line with the tokens forgotten (evt011_of_payload)."
          "Line 1 is the first and third quoted sentences together with the part of the fourth that concerns steps: in the reference only four steps deposit, the settling of a completion that passed output validation (commit), the settling of a timeout outcome (tdeposit), a mid-action publication (publish) and an injection (inject), and every other step that is not a start leaves the marking as it is (evt011_refStep), so the line asks for one event per deposited token, naming its place, at a deposit and for no step that deposits nothing. Only Rust and Python offer a mid-action publication (IO-015); in Java and TypeScript that trigger never occurs. An executor that reports one event per place instead of one per token breaks it (EVT_011_mutant_perPlace), and so does one that reports an injection when a caller requests it rather than when it lands (EVT_011_mutant_atRequest): a refused request, a request still queued and a queued injection discarded after a close add nothing. A token deposited on a place the net does not declare is still reported (the marking is total; processCompletedTransitions in TypeScript bitmap-net-executor.ts). AC2 (the place name identifies the target place) is line 1; AC1 (emitted for every deposited token and at no other time: not for the initial marking, not at a start, not at an injection request) is line 1 with line 2."
          "Line 2 is the second quoted sentence and the rest of the fourth (ruling D76 (a)): the boot of a run reports no TokenAdded for the initial marking, and a start, which only takes tokens, reports none. The old clause 'whether from initial marking' asked for the opposite, and no runtime emits it: the only emission sites are the deposit of a completion, of a timeout outcome and of an injection (processSyncOutput, processCompletedTransitions and processExternalEvents in java/src/main/java/org/libpetri/runtime/BitmapNetExecutor.java and PrecompiledNetExecutor.java; processCompletedTransitions and processExternalEvents in typescript/src/runtime/bitmap-net-executor.ts), and in Rust also the mid-action publication (rust/libpetri-runtime/src/executor_core/executor.rs handle_flush, handle_signal, handle_completion), which Python runs on. An executor that reports the initial marking as added at boot breaks line 2 (EVT_011_mutant_bootAdded); so does one that reports a read token as put back at a start (EVT_011_mutant_readPutBack)."
          "The positive half of the second quoted sentence, that a MarkingSnapshot emitted at the start of a run reports the tokens of the initial marking, is EVT-014's requirement and is cited here, not stated: line 2 states only that the boot reports no TokenAdded."
          "The block reads an executor at the grain of the reference, where a start only takes tokens and every deposit is a step of its own. Java runs a synchronous action inside fireTransition and, when its future is already done, deposits the outputs in the same call and emits their TokenAdded events there (processSyncOutput, which fireTransition in BitmapNetExecutor.java calls when the future is already done; PrecompiledNetExecutor.java has the same path). The reference splits that call into the start, the action's writes and its return, and a commit inside the same firing pass (EXEC-003), so the fast path's deposit and its events are a commit's. A coarser model that folds the deposit into the start is read through that split, not as a counterexample; a fold that reports nothing is EVT_011_mutant_silentStart."
          "Not fixed here: the order of the TokenAdded events across places (the reference reports a deposit in emission order; the per-place order is the payload companion's), and the place of the TokenAdded events of a completion before its TransitionCompleted (EVT-007's). The timestamp the event carries is not modelled (the epoch clock is the CORE-011 slice). An injection batch is a sequence of inject steps; a batch cut short by a terminal place (EXEC-042) adds and reports nothing for the rest."
          "Assumptions shared by the executor event blocks: the event store is enabled and its append does not fail (EVT-020); no host callback throws inside a deposit (an append that throws in the middle of a deposit is out of scope); an event is a value (EVT-001); transition names are distinct (ruling D10). The events of one step are contiguous in the model, since a step appends its events at once. Java appends ActionTimedOut events and the log messages it captures from actions from other threads than the orchestrator (the timeout callback BitmapNetExecutor.fireTransition hands java/src/main/java/org/libpetri/runtime/ExecutorSupport.java withActionTimeout, which appends through emitEvent from the timer thread; LogCaptureScope.java wrapRunnable and wrapCallable), so in a Java store such an event can fall between the events of one step; the lines are read on the store with those events left out, as the reading at the top of spec/08-events-observability.md says. TypeScript and Rust append every event from the orchestrator."
          "The test derivation (add a token to a place, verify the TokenAdded event with the right place name) is EVT_011_nonvacuous: an injection of 5 into place 2 emits one TokenAdded naming place 2, which goes from no token to one; the settled completion of a synchronous action that wrote two tokens into place 1 emits two TokenAdded events naming place 1 and none naming place 0; the request that queued the injection emits none; the start of a transition emits events, none a TokenAdded, and takes the token of its input place; and the boot of a run on a marking of two tokens emits events, none a TokenAdded."
  signoff "2026-11-13 c38856d693e6dba0 ai"
  statement : ∀ {N T : Type} [DecidableEq N], EvExec N T → Prop :=
    fun E => ∀ C,
      (∀ H l evs, (∀ n sy, l ≠ .start n sy) →
        on (fun s s' => E.step C H s l evs s'), shall (fun s s' =>
          ∀ p, ∃ d, s'.M p = s.M p ++ d ∧ d.length = addedCount evs p)) ∧
      ((∀ M0, ∀ e ∈ E.boot C M0, e.kind ≠ .tokenAdded) ∧
        ∀ H n sy evs, on (fun s s' => E.step C H s (.start n sy) evs s'), shall (fun s s' =>
          (∀ e ∈ evs, e.kind ≠ .tokenAdded) ∧ ∀ p, (s'.M p).Sublist (s.M p)))

/- The pinned readable form of EVT-011: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EVT_011 : {N T : Type} → [DecidableEq N] → EvExec N T → Prop :=
fun {N T} [DecidableEq N] E =>
  ∀ (C : Cfg N T),
    (∀ (H : List (NetEvent N T)) (l : XLbl N T) (evs : List (NetEvent N T)),
        (∀ (n : String) (sy : Bool), l ≠ XLbl.start n sy) →
          on fun s s' => E.step C H s l evs s', shall fun s s' =>
            ∀ (p : N), ∃ d, s'.M p = s.M p ++ d ∧ d.length = addedCount evs p) ∧
      (∀ (M0 : QMarking N T), ∀ e ∈ E.boot C M0, e.kind ≠ NetEventKind.tokenAdded) ∧
        ∀ (H : List (NetEvent N T)) (n : String) (sy : Bool) (evs : List (NetEvent N T)),
          on fun s s' => E.step C H s (XLbl.start n sy) evs s', shall fun s s' =>
            (∀ e ∈ evs, e.kind ≠ NetEventKind.tokenAdded) ∧ ∀ (p : N), (s'.M p).Sublist (s.M p)
-/
#guard_msgs in #print EVT_011

/-! ## EVT-011, Java and TypeScript companion: which tokens, in the order appended -/

requirement EVT_011_payload
  id "EVT-011"
  title "TokenAdded Event (token payload)"
  kind B
  scope "Java and TypeScript executors; Rust and Python executors whose event store captures tokens (event store enabled)"
  source verbatim "spec/08-events-observability.md"
  covers EVT_011.s5
  reading "For every executor with events E, every configuration C and every history H: a step whose label is not a start, from state s to state s', that appends the events evs leaves, for every place p, p's queue in s followed by the tokens of the TokenAdded events in evs naming p, in event order, equal to p's queue in s'."
  assumes "This is the second block of EVT-011 (rulings D33 (a) and D38 (a)): the token payload, for the executors whose TokenAdded event carries the token. The first block, EVT_011, states the count and the emission points for every executor; this block adds which tokens and in which order. Java and TypeScript events always carry the token (processSyncOutput, processCompletedTransitions and processExternalEvents in BitmapNetExecutor.java; processCompletedTransitions and processExternalEvents in bitmap-net-executor.ts). Rust and Python carry it only when the event store captures tokens (event_payload.rs token_added_event); otherwise only the first block applies."
          "The model is an executor with events E : EvExec N T, as in the first block; the witness is refEvExec polJT, and EVT_011_payload_rust shows the line for the Rust and Python emission polRust, the variant whose store captures tokens (in the model every TokenAdded event carries its token). The line is the quoted sentence: per place, the queue before the step followed by the tokens of the TokenAdded events naming it, in emission order, is the queue after the step, so the reported tokens are exactly the appended ones, in the order they were appended at the tail (EXEC-020). AC3 (the tokens reported for a place in one deposit are the deposited ones, in the order appended) is this line. The count line of the first block follows from it (evt011_of_payload). An executor that reports the right number of tokens per place but newest first meets the first block and breaks this line (EVT_011_payload_mutant_reversed)."
          "Line 2 of the first block (no TokenAdded at boot or at a start) is not restated. The order across places and the place of TransitionCompleted among the events are EVT-007's; timestamps are not modelled; the shared assumptions of the first block (store enabled, no host callback throws inside a deposit, events are values, distinct names) apply."
          "The test derivation is EVT_011_payload_nonvacuous: the completion reports 7 then 8 for place 1, which goes from 20 to 20, 7, 8, and the injection reports 5 for place 2."
  signoff "2026-11-13 0c1712c72ad18124 ai"
  statement : ∀ {N T : Type} [DecidableEq N], EvExec N T → Prop :=
    fun E => ∀ C H l evs, (∀ n sy, l ≠ .start n sy) →
      on (fun s s' => E.step C H s l evs s'), shall (fun s s' =>
        ∀ p, s.M p ++ addedAt evs p = s'.M p)

/- The pinned readable form of the companion: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EVT_011_payload : {N T : Type} → [DecidableEq N] → EvExec N T → Prop :=
fun {N T} [DecidableEq N] E =>
  ∀ (C : Cfg N T) (H : List (NetEvent N T)) (l : XLbl N T) (evs : List (NetEvent N T)),
    (∀ (n : String) (sy : Bool), l ≠ XLbl.start n sy) →
      on fun s s' => E.step C H s l evs s', shall fun s s' => ∀ (p : N), s.M p ++ addedAt evs p = s'.M p
-/
#guard_msgs in #print EVT_011_payload

/-! ## The two lines of the first block, one at a time -/

section Lines

variable {N T : Type} [DecidableEq N] [Ord N]
/-- Line 1 of `EVT_011` alone: per place, a step that is not a start appends to the queue as many
tokens as it has `TokenAdded` events naming the place. -/
def evt011_line1 (E : EvExec N T) : Prop :=
  ∀ C H l evs, (∀ n sy, l ≠ .start n sy) →
    on (fun s s' => E.step C H s l evs s'), shall (fun s s' =>
      ∀ p, ∃ d, s'.M p = s.M p ++ d ∧ d.length = addedCount evs p)

/-- Line 2 of `EVT_011` alone: neither the boot nor a start emits a `TokenAdded` event, and a
start only takes tokens. -/
def evt011_line2 (E : EvExec N T) : Prop :=
  ∀ C, (∀ M0, ∀ e ∈ E.boot C M0, e.kind ≠ .tokenAdded) ∧
    ∀ H n sy evs, on (fun s s' => E.step C H s (.start n sy) evs s'), shall (fun s s' =>
      (∀ e ∈ evs, e.kind ≠ .tokenAdded) ∧ ∀ p, (s'.M p).Sublist (s.M p))

/-- `EVT_011` without the rule that a start only takes tokens: line 1, and neither the boot nor a
start emits a `TokenAdded` event. -/
def evt011_noStartFrame (E : EvExec N T) : Prop :=
  evt011_line1 E ∧ ∀ C, (∀ M0, ∀ e ∈ E.boot C M0, e.kind ≠ .tokenAdded) ∧
    ∀ H n sy evs, on (fun s s' => E.step C H s (.start n sy) evs s'), shall (fun _ _ =>
      ∀ e ∈ evs, e.kind ≠ .tokenAdded)

omit [Ord N] in
/-- `EVT_011` is its two lines. -/
theorem evt011_iff (E : EvExec N T) : EVT_011 E ↔ evt011_line1 E ∧ evt011_line2 E :=
  ⟨fun h => ⟨fun C => (h C).1, fun C => (h C).2⟩,
   fun h C => ⟨h.1 C, h.2 C⟩⟩

omit [Ord N] in
/-- The added tokens of two event lists, one after the other. -/
theorem evt011_addedAt_append (a b : List (NetEvent N T)) (p : N) :
    addedAt (a ++ b) p = addedAt a p ++ addedAt b p := by
  simp [addedAt, List.filterMap_append]

omit [Ord N] in
/-- The count of `TokenAdded` events naming `p` is the number of tokens they carry. -/
theorem evt011_addedCount_eq_length (evs : List (NetEvent N T)) (p : N) :
    addedCount evs p = (addedAt evs p).length := by
  induction evs with
  | nil => rfl
  | cons e es ih =>
    cases e with
    | tokenAdded q x =>
      by_cases h : q = p
      · simp [addedCount, addedAt, NetEvent.addsTo, h] at ih ⊢; omega
      · simp [addedCount, addedAt, NetEvent.addsTo, h] at ih ⊢; omega
    | _ => simpa [addedCount, addedAt, NetEvent.addsTo] using ih

omit [Ord N] in
/-- An event list with no `TokenAdded` event adds nothing to any place. -/
theorem evt011_addedAt_of_none (evs : List (NetEvent N T))
    (h : ∀ e ∈ evs, e.kind ≠ .tokenAdded) (p : N) : addedAt evs p = [] := by
  rw [addedAt, List.filterMap_eq_nil_iff]
  intro e he
  cases e with
  | tokenAdded q x => exact absurd rfl (h _ he)
  | _ => rfl

omit [Ord N] in
/-- The `TokenAdded` events of an emission, read at `p`, are the tokens it emits to `p`, in
emission order. -/
theorem evt011_addedAt_addedEvs (e : List (N × T)) (p : N) :
    addedAt (addedEvs e) p = qEmittedTo e p := by
  induction e with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨q, y⟩ := x
    by_cases h : q = p
    · subst h
      simp only [addedEvs, List.map_cons, qEmittedTo, List.filter_cons, decide_true,
        if_true] at ih ⊢
      simp only [addedAt, List.filterMap_cons, if_true] at ih ⊢
      rw [ih]
    · simp only [addedEvs, List.map_cons, qEmittedTo, List.filter_cons, h, decide_false] at ih ⊢
      simp only [addedAt, List.filterMap_cons, h, if_false] at ih ⊢
      exact ih

omit [Ord N] in
/-- The count line is the payload line with the tokens forgotten: an executor that meets the
payload companion meets line 1 of the first block. -/
theorem evt011_of_payload {E : EvExec N T} (h : EVT_011_payload E) : evt011_line1 E :=
  fun C H l evs hl s s' hs p =>
    ⟨_, (h C H l evs hl s s' hs p).symm, (evt011_addedCount_eq_length evs p).symm⟩

/-- Line 1 at one place gives the count: the length before plus the number of `TokenAdded` events
naming the place is the length after. -/
theorem evt011_count {a b : List T} {k : Nat} (h : ∃ d, b = a ++ d ∧ d.length = k) :
    a.length + k = b.length := by
  obtain ⟨d, rfl, rfl⟩ := h
  simp

end Lines

/-! ## The reference -/

section Reference

variable {N T : Type} [DecidableEq N] [Ord N]
/-- **What a step of the reference executor that is not a start adds**: per place, the queue
before the step followed by the tokens of the step's `TokenAdded` events naming the place is the
queue after it. The four deposits (`commit`, `tdeposit`, `publish`, `inject`) append exactly what
they report; every other step leaves the marking as it is and reports no addition. -/
theorem evt011_refStep (P : EvPol) {C : Cfg N T} (H : List (NetEvent N T)) {s s' : XSt N T}
    {l : XLbl N T} (hl : ∀ n sy, l ≠ .start n sy) (h : xstep C s l = some s') (p : N) :
    s.M p ++ addedAt (refEmitW P C H s l s') p = s'.M p := by
  have hnone : NetEventKind.tokenAdded ∉ lblKinds l →
      addedAt (refEmitW P C H s l s') p = [] := fun hk =>
    evt011_addedAt_of_none _ (fun e he hke => hk (hke ▸ refEmitW_kind P C H s l s' e he)) p
  have hframe : s'.M = s.M → NetEventKind.tokenAdded ∉ lblKinds l →
      s.M p ++ addedAt (refEmitW P C H s l s') p = s'.M p := fun hM hk => by
    rw [hnone hk, hM, List.append_nil]
  cases l with
  | commit i =>
    obtain ⟨f, e, hf, he, -, -, -, rfl⟩ := commitStep_some (P := refXPol) h
    simp only [refEmitW, hf, he, evt011_addedAt_append, evt011_addedAt_addedEvs, depositAt,
      qAppend_apply]
    simp [addedAt]
  | tdeposit i =>
    obtain ⟨f, e, hf, he, -, -, rfl⟩ := tdepositStep_some h
    simp only [refEmitW, hf, he, evt011_addedAt_append, evt011_addedAt_addedEvs, depositAt,
      qAppend_apply]
    split <;> split <;> simp [addedAt]
  | publish i =>
    obtain ⟨b, rest, hpq, -, -, rfl⟩ := publishStep_some h
    simp only [refEmitW, hpq, evt011_addedAt_addedEvs, qAppend_apply]
  | inject k =>
    obtain ⟨q, x, rest, heq, -, -, -, rfl⟩ := injectStep_some h
    simp only [refEmitW, heq, qAppendOne]
    by_cases hq : p = q
    · subst hq; simp [addedAt]
    · simp [addedAt, hq, Ne.symm hq]
  | start n sy => exact absurd rfl (hl n sy)
  | fail i =>
    obtain ⟨f, -, -, -, rfl⟩ := failStep_some (P := refXPol) h
    exact hframe rfl (by simp [lblKinds])
  | endCompletions =>
    obtain ⟨-, -, -, -, rfl⟩ := xstepW_endCompletions h; exact hframe rfl (by simp [lblKinds])
  | endPublications =>
    obtain ⟨-, -, -, rfl⟩ := xstepW_endPublications h; exact hframe rfl (by simp [lblKinds])
  | discard k =>
    obtain ⟨_, _, _, -, -, -, -, rfl⟩ := discardStep_some h; exact hframe rfl (by simp [lblKinds])
  | endEvents =>
    obtain ⟨-, -, -, rfl⟩ := xstepW_endEvents h; exact hframe rfl (by simp [lblKinds])
  | snapshot a =>
    obtain ⟨-, -, -, rfl⟩ := snapshotStep_some h; exact hframe rfl (by simp [lblKinds])
  | update =>
    obtain ⟨-, -, rfl⟩ := xstepW_update h; exact hframe rfl (by simp [lblKinds])
  | deadline ns =>
    obtain ⟨-, -, -, rfl⟩ := xstepW_deadline h; exact hframe rfl (by simp [lblKinds])
  | begin =>
    obtain ⟨-, -, -, -, rfl⟩ := xstepW_begin h; exact hframe rfl (by simp [lblKinds])
  | lose n =>
    obtain ⟨_, _, -, -, -, -, -, -, rfl⟩ := loseStep_some (P := refXPol) h
    exact hframe rfl (by simp [lblKinds])
  | endPass =>
    obtain ⟨-, -, -, -, rfl⟩ := xstepW_endPass h; exact hframe rfl (by simp [lblKinds])
  | finish c =>
    cases c with
    | quiescent =>
      obtain ⟨-, -, -, rfl⟩ := xstepW_finishQuiescent h; exact hframe rfl (by simp [lblKinds])
    | closed =>
      obtain ⟨-, -, -, -, rfl⟩ := xstepW_finishClosed h; exact hframe rfl (by simp [lblKinds])
    | terminal =>
      obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h; exact hframe rfl (by simp [lblKinds])
    | stopped =>
      obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h; exact hframe rfl (by simp [lblKinds])
  | park tmr =>
    obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := parkStep_some h; exact hframe rfl (by simp [lblKinds])
  | wake =>
    obtain ⟨-, -, rfl⟩ := wakeStep_some h; exact hframe rfl (by simp [lblKinds])
  | delay δ => exact hframe (xstepW_outside_frame h rfl).1 (by simp [lblKinds])
  | write i q x => exact hframe (xstepW_outside_frame h rfl).1 (by simp [lblKinds])
  | flush i => exact hframe (xstepW_outside_frame h rfl).1 (by simp [lblKinds])
  | ret i ok => exact hframe (xstepW_outside_frame h rfl).1 (by simp [lblKinds])
  | expire i e => exact hframe (xstepW_outside_frame h rfl).1 (by simp [lblKinds])
  | request q x r => exact hframe (xstepW_outside_frame h rfl).1 (by simp [lblKinds])
  | drain => exact hframe (xstepW_outside_frame h rfl).1 (by simp [lblKinds])
  | close => exact hframe (xstepW_outside_frame h rfl).1 (by simp [lblKinds])
  | terminateNow => exact hframe (xstepW_outside_frame h rfl).1 (by simp [lblKinds])

/-- A reference start emits no `TokenAdded`. -/
theorem evt011_refStart_noAdded (P : EvPol) (C : Cfg N T) (H : List (NetEvent N T))
    (s : XSt N T) (n : String) (sy : Bool) (s' : XSt N T) :
    ∀ e ∈ refEmitW P C H s (.start n sy) s', e.kind ≠ .tokenAdded := by
  intro e he hk
  have := refEmitW_kind P C H s (.start n sy) s' e he
  rw [hk] at this
  simp [lblKinds] at this

omit [Ord N] in
/-- A reference start only takes tokens: every queue after it is a sublist of the queue before it
(it is what remains once the start has removed its tokens from the head). -/
theorem evt011_refStart_frame {C : Cfg N T} {s s' : XSt N T} {n : String} {sy : Bool}
    (h : xstep C s (.start n sy) = some s') (p : N) : (s'.M p).Sublist (s.M p) := by
  obtain ⟨_, _, -, -, hr⟩ := xstep_start_qRemoved h
  rw [← hr p]
  exact List.sublist_append_right _ _

/-- The reference boot emits no `TokenAdded`. -/
theorem evt011_refBoot_noAdded (P : EvPol) (C : Cfg N T) (M0 : QMarking N T) :
    ∀ e ∈ refBoot P C M0, e.kind ≠ .tokenAdded := by
  intro e he hk
  rcases refBoot_kind P C M0 e he with h | h <;> rw [hk] at h <;> cases h

/-- Line 2 holds of every executor that boots and starts as the reference (`polJT`), whatever it
emits at the other steps. -/
theorem evt011_line2_of_ref
    {emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    (he : ∀ C H s n sy s', emit C H s (.start n sy) s' = refEmitW polJT C H s (.start n sy) s') :
    evt011_line2 (emitExec (refBoot polJT) emit) := by
  intro C
  refine ⟨evt011_refBoot_noAdded polJT C, fun H n sy evs s s' hs => ?_⟩
  obtain ⟨hx, rfl⟩ := hs
  rw [he]
  exact ⟨evt011_refStart_noAdded polJT C H s n sy s', evt011_refStart_frame hx⟩

/-- Line 1 holds of every executor that steps as the reference and, at each step that is not a
start, emits as many `TokenAdded` events per place as the reference (`polJT`), whatever its boot
and start events. -/
theorem evt011_line1_of_count {boot : Cfg N T → QMarking N T → List (NetEvent N T)}
    {emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    (he : ∀ C H s l s', (∀ n sy, l ≠ .start n sy) → ∀ p,
      addedCount (emit C H s l s') p = addedCount (refEmitW polJT C H s l s') p) :
    evt011_line1 (emitExec boot emit) := by
  intro C H l evs hl s s' hs p
  obtain ⟨hx, rfl⟩ := hs
  rw [he C H s l s' hl p]
  exact ⟨_, (evt011_refStep polJT H hl hx p).symm, (evt011_addedCount_eq_length _ p).symm⟩

/-- The reference meets the payload companion under every emission variant. -/
theorem evt011_payload_ref (P : EvPol) : EVT_011_payload (refEvExec (N := N) (T := T) P) := by
  intro C H l evs hl s s' hs p
  obtain ⟨hx, rfl⟩ := hs
  exact evt011_refStep P H hl hx p

/-- The reference meets the first block under every emission variant. -/
theorem evt011_ref (P : EvPol) : EVT_011 (refEvExec (N := N) (T := T) P) :=
  (evt011_iff _).2 ⟨evt011_of_payload (evt011_payload_ref P), fun C =>
    ⟨evt011_refBoot_noAdded P C, fun H n sy evs s s' hs => by
      obtain ⟨hx, rfl⟩ := hs
      exact ⟨evt011_refStart_noAdded P C H s n sy s', evt011_refStart_frame hx⟩⟩⟩

/-- ✓ The reference executor with the Java and TypeScript emission meets EVT-011: every deposit
appends its tokens at the tail and reports one `TokenAdded` event per token, naming its place;
the boot and the starts report none, and a start only takes tokens. -/
@[evidence holds EVT_011]
theorem EVT_011_reference : EVT_011 (refEvExec (N := N) (T := T) polJT) := evt011_ref polJT

/-- ✓ The reference executor with the Rust and Python emission meets EVT-011 too: the block is a
line for every executor. -/
@[evidence holds EVT_011]
theorem EVT_011_rust : EVT_011 (refEvExec (N := N) (T := T) polRust) := evt011_ref polRust

/-- ✓ The reference executor with the Java and TypeScript emission meets the payload companion:
the reported tokens of each place are exactly the appended ones, in the order they were
appended. -/
@[evidence holds EVT_011_payload]
theorem EVT_011_payload_reference : EVT_011_payload (refEvExec (N := N) (T := T) polJT) :=
  evt011_payload_ref polJT

/-- ✓ The reference executor with the Rust and Python emission meets the payload companion too:
this is the variant whose event store captures tokens, and its deposits report the same tokens in
the same order. -/
@[evidence holds EVT_011_payload]
theorem EVT_011_payload_rust : EVT_011_payload (refEvExec (N := N) (T := T) polRust) :=
  evt011_payload_ref polRust

end Reference

/-! ## The worked example -/

/-- Transition `a`: takes the token of place 0 and reads place 1. -/
def evt011_tA : Trans Nat :=
  { core := { name := "a", inputs := [⟨0, .one⟩], inhibitors := [], reads := [1], resets := [] },
    out := none }

/-- The configuration of the example: places 0 to 2, `a` Immediate, place 2 an environment
place, no validation to speak of. -/
def evt011_cfg : Cfg Nat Nat :=
  { X := { net := { places := [0, 1, 2], transitions := [evt011_tA] },
           timing := fun _ => .immediate, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [2], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => false,
    res := 0 }

/-- The initial marking: 10 in place 0, 20 in place 1, place 2 empty. -/
def evt011_m0 : QMarking Nat Nat := fun p =>
  if p = 0 then [10] else if p = 1 then [20] else []

/-- A caller asks to inject 5 into place 2 and the request is accepted (ticket 0); then step 1
and step 1b end. -/
def evt011_preInject : List (XLbl Nat Nat) :=
  [.request 2 5 .accepted, .endCompletions, .endPublications]

/-- The state before the request. -/
def evt011_init : Option (XSt Nat Nat) := some (xinit evt011_m0 0)

/-- The state before the injection lands. -/
def evt011_beforeInject : Option (XSt Nat Nat) :=
  xrun evt011_cfg (xinit evt011_m0 0) evt011_preInject

/-- The injection lands, the update arms `a`, the pass starts it synchronously (firing 1), its
action writes 7 and then 8 into place 1 and returns. -/
def evt011_preCommit : List (XLbl Nat Nat) :=
  evt011_preInject ++
    [.inject 0, .endEvents, .update, .deadline [], .begin, .start "a" true, .write 1 1 7,
     .write 1 1 8, .ret 1 true]

/-- The state before `a` starts. -/
def evt011_beforeStart : Option (XSt Nat Nat) :=
  xrun evt011_cfg (xinit evt011_m0 0)
    (evt011_preInject ++ [.inject 0, .endEvents, .update, .deadline [], .begin])

/-- The state before `a`'s completion is settled. -/
def evt011_beforeCommit : Option (XSt Nat Nat) :=
  xrun evt011_cfg (xinit evt011_m0 0) evt011_preCommit

/-- ✓ Both lines of the first block are exercised by the reference: the injection of 5 emits one
`TokenAdded` naming place 2, which goes from no token to one; the settled completion of `a`,
whose action wrote 7 and 8 into place 1, emits two `TokenAdded` events naming place 1 (which
goes from one token to three) and none naming place 0; the request that queued the injection
changes no queue and emits nothing; the start of `a` emits events, none a `TokenAdded`, and takes
the token 10 of place 0, which goes from one token to none; and the boot of the run emits events (`ExecutionStarted` and the snapshot), none a `TokenAdded`, although
the initial marking holds two tokens. -/
@[evidence nonvacuous EVT_011]
theorem EVT_011_nonvacuous :
    (∃ s s' evs, (refEvExec polJT).step evt011_cfg [] s (.inject 0) evs s' ∧
      addedCount evs 2 = 1 ∧ (s.M 2).length = 0 ∧ (s'.M 2).length = 1) ∧
    (∃ s s' evs, (refEvExec polJT).step evt011_cfg [] s (.commit 1) evs s' ∧
      addedCount evs 1 = 2 ∧ (s.M 1).length = 1 ∧ (s'.M 1).length = 3 ∧ addedCount evs 0 = 0) ∧
    (∃ s s' evs, (refEvExec polJT).step evt011_cfg [] s (.request 2 5 .accepted) evs s' ∧
      evs = [] ∧ s'.M = s.M) ∧
    (∃ s s' evs, (refEvExec polJT).step evt011_cfg [] s (.start "a" true) evs s' ∧ evs ≠ [] ∧
      (∀ e ∈ evs, e.kind ≠ .tokenAdded) ∧ s.M 0 = [10] ∧ s'.M 0 = []) ∧
    ((refEvExec (N := Nat) (T := Nat) polJT).boot evt011_cfg evt011_m0 ≠ [] ∧
      ∀ e ∈ (refEvExec (N := Nat) (T := Nat) polJT).boot evt011_cfg evt011_m0,
        e.kind ≠ .tokenAdded) := by
  refine ⟨?_, ?_, ?_, ?_, by decide +kernel⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt011_cfg) (o := evt011_beforeInject)
      (l := .inject 0)
      (p := fun s s' =>
        let evs := refEmitW polJT evt011_cfg [] s (.inject 0) s'
        addedCount evs 2 == 1 && (s.M 2).length == 0 && (s'.M 2).length == 1)
      (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    exact ⟨s, s', _, ⟨hs, rfl⟩, h1, h2, h3⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt011_cfg) (o := evt011_beforeCommit)
      (l := .commit 1)
      (p := fun s s' =>
        let evs := refEmitW polJT evt011_cfg [] s (.commit 1) s'
        addedCount evs 1 == 2 && (s.M 1).length == 1 && (s'.M 1).length == 3 &&
          addedCount evs 0 == 0)
      (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hp
    exact ⟨s, s', _, ⟨hs, rfl⟩, h1, h2, h3, h4⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt011_cfg) (o := evt011_init)
      (l := .request 2 5 .accepted)
      (p := fun s s' => (refEmitW polJT evt011_cfg [] s (.request 2 5 .accepted) s').isEmpty)
      (by decide +kernel)
    have hM := (xstepW_outside_frame (P := refXPol) hs rfl).1
    exact ⟨s, s', _, ⟨hs, rfl⟩, List.isEmpty_iff.1 hp, hM⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt011_cfg) (o := evt011_beforeStart)
      (l := .start "a" true)
      (p := fun s s' => !(refEmitW polJT evt011_cfg [] s (.start "a" true) s').isEmpty &&
        s.M 0 == [10] && s'.M 0 == [])
      (by decide +kernel)
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, beq_iff_eq] at hp
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    exact ⟨s, s', _, ⟨hs, rfl⟩, h1, evt011_refStart_noAdded polJT evt011_cfg [] s "a" true s', h2,
      h3⟩

/-- ✓ The payload line is exercised by the reference: the completion of `a` reports 7 then 8 for
place 1, which goes from 20 to 20, 7, 8, and nothing for place 0; the injection reports 5 for
place 2. -/
@[evidence nonvacuous EVT_011_payload]
theorem EVT_011_payload_nonvacuous :
    (∃ s s' evs, (refEvExec polJT).step evt011_cfg [] s (.commit 1) evs s' ∧
      addedAt evs 1 = [7, 8] ∧ s.M 1 = [20] ∧ s'.M 1 = [20, 7, 8] ∧ addedAt evs 0 = []) ∧
    (∃ s s' evs, (refEvExec polJT).step evt011_cfg [] s (.inject 0) evs s' ∧
      addedAt evs 2 = [5] ∧ s'.M 2 = [5]) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt011_cfg) (o := evt011_beforeCommit)
      (l := .commit 1)
      (p := fun s s' =>
        let evs := refEmitW polJT evt011_cfg [] s (.commit 1) s'
        addedAt evs 1 == [7, 8] && s.M 1 == [20] && s'.M 1 == [20, 7, 8] && addedAt evs 0 == [])
      (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hp
    exact ⟨s, s', _, ⟨hs, rfl⟩, h1, h2, h3, h4⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt011_cfg) (o := evt011_beforeInject)
      (l := .inject 0)
      (p := fun s s' =>
        let evs := refEmitW polJT evt011_cfg [] s (.inject 0) s'
        addedAt evs 2 == [5] && s'.M 2 == [5])
      (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', _, ⟨hs, rfl⟩, hp.1, hp.2⟩

/-! ## Wrong executors: the reference's steps, another emission -/

section Mutants

variable {N T : Type} [DecidableEq N] [Ord N]
/-- The Java and TypeScript emission with the events of a completion's deposit replaced by
`f e`, `e` the deposited emission. -/
def evt011_atCommit (f : List (N × T) → List (NetEvent N T)) (C : Cfg N T)
    (H : List (NetEvent N T)) (s : XSt N T) (l : XLbl N T) (s' : XSt N T) : List (NetEvent N T) :=
  match l with
  | .commit i =>
    match s.fl.find? (·.id == i) with
    | some g =>
      match g.out with
      | some (.ok e) => f e ++ [.transitionCompleted g.t.core.name e (s.now - g.start)]
      | _ => []
    | none => []
  | _ => refEmitW polJT C H s l s'

/-- One `TokenAdded` per place of the emission, with the first token emitted to it. -/
def evt011_perPlaceEvs (e : List (N × T)) : List (NetEvent N T) :=
  (e.map Prod.fst).dedup.flatMap fun p => ((qEmittedTo e p).take 1).map (NetEvent.tokenAdded p)

/-- The executor that reports one event per place of a completion's deposit instead of one per
token. -/
def evt011_perPlace : EvExec N T := emitExec (refBoot polJT) (evt011_atCommit evt011_perPlaceEvs)

/-- The `TokenAdded` events of an emission, newest first. -/
def evt011_reversedEvs (e : List (N × T)) : List (NetEvent N T) := addedEvs e.reverse

/-- The executor that reports the tokens of a completion's deposit newest first. -/
def evt011_reversed : EvExec N T := emitExec (refBoot polJT) (evt011_atCommit evt011_reversedEvs)

/-- The Java and TypeScript emission, with an injection reported when a caller's request is
accepted rather than when it lands. -/
def evt011_requestEmit (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T) (l : XLbl N T)
    (s' : XSt N T) : List (NetEvent N T) :=
  match l with
  | .request p x .accepted => [.tokenAdded p x]
  | .inject _ => []
  | _ => refEmitW polJT C H s l s'

/-- The executor that reports an injection at its request. -/
def evt011_atRequest : EvExec N T := emitExec (refBoot polJT) evt011_requestEmit

/-- The Java and TypeScript boot events followed by one `TokenAdded` for every token of the
initial marking on a declared place: the literal reading of "whether from initial marking". -/
def evt011_bootAddedEvs (C : Cfg N T) (M0 : QMarking N T) : List (NetEvent N T) :=
  refBoot polJT C M0 ++ C.X.net.places.dedup.flatMap fun p => (M0 p).map (NetEvent.tokenAdded p)

/-- The executor that steps and emits as the reference but reports the initial marking as added
at boot. -/
def evt011_bootAdded : EvExec N T := emitExec evt011_bootAddedEvs (refEmitW polJT)

/-- The Java and TypeScript emission, with a start also reporting the token each read arc reads
as put back (a read arc read as a take and a return). -/
def evt011_readPutBackEmit (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T) (l : XLbl N T)
    (s' : XSt N T) : List (NetEvent N T) :=
  match l, s.order with
  | .start _ _, t :: _ =>
    refEmitW polJT C H s l s' ++
      t.core.reads.flatMap fun p => ((vis s p).take 1).map (NetEvent.tokenAdded p)
  | _, _ => refEmitW polJT C H s l s'

/-- The executor that reports a read token as put back when a transition starts. -/
def evt011_readPutBack : EvExec N T := emitExec (refBoot polJT) evt011_readPutBackEmit

/-- Away from a commit, `evt011_atCommit` emits as the reference. -/
theorem evt011_atCommit_other (f : List (N × T) → List (NetEvent N T)) (C : Cfg N T)
    (H : List (NetEvent N T)) (s : XSt N T) {l : XLbl N T} (hl : ∀ i, l ≠ .commit i)
    (s' : XSt N T) : evt011_atCommit f C H s l s' = refEmitW polJT C H s l s' := by
  cases l with
  | commit i => exact absurd rfl (hl i)
  | _ => rfl

/-- An executor that changes only what a commit emits keeps line 2. -/
theorem evt011_atCommit_line2 (f : List (N × T) → List (NetEvent N T)) :
    evt011_line2 (emitExec (refBoot polJT) (evt011_atCommit f)) :=
  evt011_line2_of_ref fun _ _ _ _ _ _ => rfl

omit [Ord N] in
/-- Reporting newest first keeps the counts per place. -/
theorem evt011_addedCount_reversed (e : List (N × T)) (c : NetEvent N T) (p : N) :
    addedCount (evt011_reversedEvs e ++ [c]) p = addedCount (addedEvs e ++ [c]) p := by
  simp only [addedCount, List.countP_append, evt011_reversedEvs, addedEvs, List.map_reverse,
    List.countP_reverse]

/-- Reporting newest first keeps the first block. -/
theorem evt011_reversed_meets : EVT_011 (evt011_reversed (N := N) (T := T)) := by
  refine (evt011_iff _).2 ⟨evt011_line1_of_count fun C H s l s' _ p => ?_,
    evt011_atCommit_line2 _⟩
  cases l with
  | commit i =>
    simp only [evt011_atCommit, refEmitW]
    generalize s.fl.find? (·.id == i) = o
    rcases o with _ | g
    · rfl
    · simp only
      generalize g.out = r
      rcases r with _ | (e | _ | e)
      · rfl
      · exact evt011_addedCount_reversed _ _ p
      · rfl
      · rfl
  | _ => rfl

/-! ### Wrong executors that also step otherwise -/

/-- An executor that takes each step of the reference and then rewrites the marking: from `s` the
step labelled `l` goes where the reference goes (`s1`), except that the marking becomes
`g C H s l s1`, and appends `emit C H s l s1`. -/
def evt011_fused
    (g : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → QMarking N T)
    (emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)) :
    EvExec N T where
  boot := refBoot polJT
  step := fun C H s l evs s' =>
    ∃ s1, xstep C s l = some s1 ∧ evs = emit C H s l s1 ∧ s' = { s1 with M := g C H s l s1 }

/-- A fused executor that steps and emits as the reference away from the starts meets line 1. -/
theorem evt011_fused_line1
    {g : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → QMarking N T}
    {emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    (hg : ∀ C H s l s1, (∀ n sy, l ≠ .start n sy) → g C H s l s1 = s1.M)
    (he : ∀ C H s l s1, (∀ n sy, l ≠ .start n sy) → emit C H s l s1 = refEmitW polJT C H s l s1) :
    evt011_line1 (evt011_fused g emit) := by
  intro C H l evs hl s s' hs p
  obtain ⟨s1, hx, rfl, rfl⟩ := hs
  rw [hg C H s l s1 hl, he C H s l s1 hl]
  exact ⟨_, (evt011_refStep polJT H hl hx p).symm, (evt011_addedCount_eq_length _ p).symm⟩

/-- A fused executor that starts and emits at a start as the reference meets line 2. -/
theorem evt011_fused_line2
    {g : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → QMarking N T}
    {emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    (hg : ∀ C H s n sy s1, g C H s (.start n sy) s1 = s1.M)
    (he : ∀ C H s n sy s1, emit C H s (.start n sy) s1 = refEmitW polJT C H s (.start n sy) s1) :
    evt011_line2 (evt011_fused g emit) := by
  intro C
  refine ⟨evt011_refBoot_noAdded polJT C, fun H n sy evs s s' hs => ?_⟩
  obtain ⟨s1, hx, rfl, rfl⟩ := hs
  rw [hg, he]
  exact ⟨evt011_refStart_noAdded polJT C H s n sy s1, evt011_refStart_frame hx⟩

/-- The marking of the silent fast path: a synchronous start also appends the action's outputs
`out`; every other step leaves the reference's marking. -/
def evt011_silentStartM (out : List (N × T)) (_ : Cfg N T) (_ : List (NetEvent N T))
    (_ : XSt N T) (l : XLbl N T) (s1 : XSt N T) : QMarking N T :=
  match l with
  | .start _ true => qAppend s1.M out
  | _ => s1.M

/-- The executor whose synchronous start deposits the action's outputs `out` in the same step and
reports nothing for them (Java's fast path, `processSyncOutput`, with its `TokenAdded` emission
dropped). -/
def evt011_silentStart (out : List (N × T)) : EvExec N T :=
  evt011_fused (evt011_silentStartM out) (refEmitW polJT)

/-- The marking of the overwriting executor: a commit whose first event is a `TokenAdded` naming
`q` drops the oldest token of `q`, so its first output takes that token's place. -/
def evt011_overwriteM (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T) (l : XLbl N T)
    (s1 : XSt N T) : QMarking N T :=
  match l with
  | .commit _ =>
    match refEmitW polJT C H s l s1 with
    | .tokenAdded q _ :: _ => fun p => if p = q then (s1.M p).tail else s1.M p
    | _ => s1.M
  | _ => s1.M

/-- The emission of the overwriting executor: a commit does not report its first output. -/
def evt011_overwriteEmit (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T) (l : XLbl N T)
    (s1 : XSt N T) : List (NetEvent N T) :=
  match l with
  | .commit _ =>
    match refEmitW polJT C H s l s1 with
    | .tokenAdded _ _ :: rest => rest
    | evs => evs
  | _ => refEmitW polJT C H s l s1

/-- The executor that writes a completion's first output over the oldest token of its place, as
an in-place update, and reports no addition for it. -/
def evt011_overwrite : EvExec N T := evt011_fused evt011_overwriteM evt011_overwriteEmit

end Mutants

/-- ✗ Reporting one event per place instead of one per token violates EVT-011 (line 1): the
action of `a` wrote 7 and 8 into place 1, which goes from one token to three, and only one event
names place 1. The executor keeps line 2. -/
@[evidence mutant EVT_011]
theorem EVT_011_mutant_perPlace :
    evt011_line2 (evt011_perPlace (N := Nat) (T := Nat)) ∧
      ¬ EVT_011 (evt011_perPlace (N := Nat) (T := Nat)) := by
  refine ⟨evt011_atCommit_line2 _, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt011_cfg) (o := evt011_beforeCommit)
    (l := .commit 1)
    (p := fun s s' =>
      (s.M 1).length + addedCount (evt011_atCommit evt011_perPlaceEvs evt011_cfg [] s (.commit 1) s') 1
        != (s'.M 1).length)
    (by decide +kernel)
  simp only [bne_iff_ne, ne_eq] at hp
  exact hp (evt011_count ((h evt011_cfg).1 [] (.commit 1) _ (fun _ _ => by simp) s s' ⟨hs, rfl⟩ 1))

/-- ✗ Reporting an injection when the caller's request is accepted violates EVT-011 (line 1):
the request to inject 5 into place 2 reports a `TokenAdded` naming place 2, but the token only
waits in the event queue and place 2 stays empty. The executor keeps line 2. -/
@[evidence mutant EVT_011]
theorem EVT_011_mutant_atRequest :
    evt011_line2 (evt011_atRequest (N := Nat) (T := Nat)) ∧
      ¬ EVT_011 (evt011_atRequest (N := Nat) (T := Nat)) := by
  refine ⟨evt011_line2_of_ref fun _ _ _ _ _ _ => rfl, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt011_cfg) (o := evt011_init)
    (l := .request 2 5 .accepted)
    (p := fun s s' =>
      (s.M 2).length + addedCount (evt011_requestEmit evt011_cfg [] s (.request 2 5 .accepted) s') 2
        != (s'.M 2).length)
    (by decide +kernel)
  simp only [bne_iff_ne, ne_eq] at hp
  exact hp (evt011_count
    ((h evt011_cfg).1 [] (.request 2 5 .accepted) _ (fun _ _ => by simp) s s' ⟨hs, rfl⟩ 2))

/-- ✗ Reporting the initial marking as added when the run boots, as the old clause "whether from
initial marking" read, violates EVT-011 (line 2; ruling D76 (a)): the boot of the example reports
token 10 of place 0 as added. Every step of this executor emits as the reference, so it keeps
line 1. -/
@[evidence mutant EVT_011]
theorem EVT_011_mutant_bootAdded :
    evt011_line1 (evt011_bootAdded (N := Nat) (T := Nat)) ∧
      ¬ EVT_011 (evt011_bootAdded (N := Nat) (T := Nat)) := by
  refine ⟨evt011_line1_of_count fun _ _ _ _ _ _ _ => rfl, fun h => ?_⟩
  have hm : NetEvent.tokenAdded 0 10 ∈ evt011_bootAdded.boot evt011_cfg evt011_m0 := by
    decide +kernel
  exact (h evt011_cfg).2.1 evt011_m0 _ hm rfl

/-- ✗ Reporting the token a read arc reads as put back when a transition starts violates EVT-011
(line 2): `a` reads 20 from place 1, which keeps it, and its start reports a `TokenAdded` naming
place 1. Every other step emits as the reference, so the executor keeps line 1. -/
@[evidence mutant EVT_011]
theorem EVT_011_mutant_readPutBack :
    evt011_line1 (evt011_readPutBack (N := Nat) (T := Nat)) ∧
      ¬ EVT_011 (evt011_readPutBack (N := Nat) (T := Nat)) := by
  refine ⟨evt011_line1_of_count fun C H s l s' hl p => ?_, fun h => ?_⟩
  · cases l with
    | start n sy => exact absurd rfl (hl n sy)
    | _ => simp only [evt011_readPutBackEmit]
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt011_cfg) (o := evt011_beforeStart)
      (l := .start "a" true)
      (p := fun s s' => (evt011_readPutBackEmit evt011_cfg [] s (.start "a" true) s').any
        fun e => e.kind == .tokenAdded)
      (by decide +kernel)
    simp only [List.any_eq_true, beq_iff_eq] at hp
    obtain ⟨e, he, hk⟩ := hp
    exact ((h evt011_cfg).2.2 [] "a" true _ s s' ⟨hs, rfl⟩).1 e he hk

/-- ✗ Depositing a synchronous action's outputs inside its start and reporting nothing for them
violates EVT-011 (line 2): the action of `a` writes 7 and 8 into place 1, and the start takes
place 1 from 20 to 20, 7, 8 while it reports no `TokenAdded`. Every step that is not a start is
the reference's, so the executor keeps line 1, and its starts emit no `TokenAdded`: only the rule
that a start takes tokens and adds none rejects it. -/
@[evidence mutant EVT_011]
theorem EVT_011_mutant_silentStart :
    evt011_noStartFrame (evt011_silentStart (N := Nat) (T := Nat) [(1, 7), (1, 8)]) ∧
      ¬ EVT_011 (evt011_silentStart (N := Nat) (T := Nat) [(1, 7), (1, 8)]) := by
  refine ⟨⟨evt011_fused_line1 (fun _ _ _ l _ hl => ?_) (fun _ _ _ _ _ _ => rfl),
    fun C => ⟨evt011_refBoot_noAdded polJT C, fun H n sy evs s s' hs => ?_⟩⟩, fun h => ?_⟩
  · cases l with
    | start n sy => exact absurd rfl (hl n sy)
    | _ => rfl
  · obtain ⟨s1, -, rfl, -⟩ := hs
    exact evt011_refStart_noAdded polJT C H s n sy s1
  · obtain ⟨s, s1, -, hs, hp⟩ := step_of_check xstep (C := evt011_cfg) (o := evt011_beforeStart)
      (l := .start "a" true)
      (p := fun s s1 => s.M 1 == [20] && qAppend s1.M [(1, 7), (1, 8)] 1 == [20, 7, 8])
      (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨h1, h2⟩ := hp
    have hf := ((h evt011_cfg).2.2 [] "a" true _ s _ ⟨s1, hs, rfl, rfl⟩).2 1
    simp only [evt011_silentStartM, h1, h2] at hf
    simpa using hf.length_le

/-- The overwriting executor at the commit of `a`: place 1 held 20, the action wrote 7 and 8, and
the executor leaves 7, 8 and reports one `TokenAdded` naming place 1. The count of queue lengths
is right (one token before, one event, two after), and the old queue is not kept at the head. -/
theorem evt011_overwrite_commit :
    ∃ s s' evs, (evt011_overwrite (N := Nat) (T := Nat)).step evt011_cfg [] s (.commit 1) evs s' ∧
      s.M 1 = [20] ∧ s'.M 1 = [7, 8] ∧ addedCount evs 1 = 1 := by
  obtain ⟨s, s1, -, hs, hp⟩ := step_of_check xstep (C := evt011_cfg) (o := evt011_beforeCommit)
    (l := .commit 1)
    (p := fun s s1 => s.M 1 == [20] && evt011_overwriteM evt011_cfg [] s (.commit 1) s1 1 == [7, 8] &&
      addedCount (evt011_overwriteEmit evt011_cfg [] s (.commit 1) s1) 1 == 1)
    (by decide +kernel)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨h1, h2⟩, h3⟩ := hp
  exact ⟨s, _, _, ⟨s1, hs, rfl, rfl⟩, h1, h2, h3⟩

/-- ✗ Writing a completion's first output over the oldest token of its place, and reporting no
addition for it, violates EVT-011 (line 1): the action of `a` writes 7 and 8 into place 1, which
held 20; the executor leaves 7, 8 and reports only 8. The count of queue lengths looks right (one
token before, one event, two after), but the queue 20 is not kept at the head, so 7 was deposited
and never reported. Starts are the reference's, so the executor keeps line 2. -/
@[evidence mutant EVT_011]
theorem EVT_011_mutant_overwrite :
    evt011_line2 (evt011_overwrite (N := Nat) (T := Nat)) ∧
      ¬ EVT_011 (evt011_overwrite (N := Nat) (T := Nat)) := by
  refine ⟨evt011_fused_line2 (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl), fun h => ?_⟩
  obtain ⟨s, s', evs, hstep, h1, h2, -⟩ := evt011_overwrite_commit
  obtain ⟨d, hd, -⟩ := (h evt011_cfg).1 [] (.commit 1) evs (fun _ _ => by simp) s s' hstep 1
  rw [h1, h2] at hd
  simp at hd

/-- ✗ Reporting the tokens of a deposit newest first meets the first block (the counts are
right) and violates the payload companion: the completion of `a` reports 8 before 7 for place 1,
so the queue 20 followed by the reported tokens is 20, 8, 7, not the queue 20, 7, 8 the deposit
leaves. -/
@[evidence mutant EVT_011_payload]
theorem EVT_011_payload_mutant_reversed :
    EVT_011 (evt011_reversed (N := Nat) (T := Nat)) ∧
      ¬ EVT_011_payload (evt011_reversed (N := Nat) (T := Nat)) := by
  refine ⟨evt011_reversed_meets, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt011_cfg) (o := evt011_beforeCommit)
    (l := .commit 1)
    (p := fun s s' =>
      s.M 1 ++ addedAt (evt011_atCommit evt011_reversedEvs evt011_cfg [] s (.commit 1) s') 1
        != s'.M 1)
    (by decide +kernel)
  simp only [bne_iff_ne, ne_eq] at hp
  exact hp (h evt011_cfg [] (.commit 1) _ (fun _ _ => by simp) s s' ⟨hs, rfl⟩ 1)

/-- ✗ Reporting one event per place violates the payload companion too: place 1 gains 7 and 8
and only 7 is reported. -/
@[evidence forbids EVT_011_payload]
theorem EVT_011_payload_forbids_perPlace :
    ¬ EVT_011_payload (evt011_perPlace (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt011_cfg) (o := evt011_beforeCommit)
    (l := .commit 1)
    (p := fun s s' =>
      s.M 1 ++ addedAt (evt011_atCommit evt011_perPlaceEvs evt011_cfg [] s (.commit 1) s') 1
        != s'.M 1)
    (by decide +kernel)
  simp only [bne_iff_ne, ne_eq] at hp
  exact hp (h evt011_cfg [] (.commit 1) _ (fun _ _ => by simp) s s' ⟨hs, rfl⟩ 1)

end Libpetri.Spec
