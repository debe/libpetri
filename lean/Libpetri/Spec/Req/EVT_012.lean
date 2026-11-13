import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Events

set_option linter.missingDocs true

/-!
# EVT-012: TokenRemoved Event (`spec/08-events-observability.md`)

When a transition starts, the executor reports every token it takes out of a place, one
`TokenRemoved` event per token, and it reports removals at no other time. The requirement has
two blocks with the same spec ID (rulings D33 (a) and D38 (a)):

* `EVT_012`, for every executor: it reads an event only through its kind and the place it names,
  which every runtime's event carries. Line 1 counts: per place, the number of `TokenRemoved`
  events of a start plus the tokens the place keeps is what the place held before. Line 2: nothing
  else emits one, neither another step nor the boot of a run.
* `EVT_012_payload`, for the executors whose event carries the token (Java and TypeScript; Rust
  and Python when the event store captures tokens): per place, the tokens of the events, in
  order, followed by what the place keeps, are the queue before the start. So the events name
  the oldest tokens, oldest first. The count line of the first block is this line with the
  tokens forgotten (`evt012_of_payload`).

Both are predicates over an abstract executor with events `E : EvExec N T`
(`Reference/Events.lean`). The witness is the reference executor with events `refEvExec`, the
reference executor `RefExec` together with its emission, under both emission variants (Java and
TypeScript `polJT`, Rust and Python `polRust`). The wrong executors step as the reference and
emit otherwise: one that reports no event for the tokens a reset arc drains, one that also
reports the token a read arc reads, one that reports a discarded injection as a removal, one that
reports the initial marking as removed at boot, and one that reports the right tokens newest
first.

The worked example (`evt012_cfg`): transition `a` takes the token of place 3 and its action,
running synchronously inside the firing pass, writes 9 into place 1. Then transition `u` starts:
it takes exactly two tokens from place 0 (holding 10, 11, 12), drains place 1 (holding the old
20 and the same-pass 9) through a reset arc, and reads place 2 (holding 30). Its start reports
10 and 11 from place 0 and 20 from place 1, and nothing for place 2; place 0 keeps 12 and place 1
keeps the same-pass 9.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## EVT-012, every executor: one event per removed token, only at a start -/

requirement EVT_012
  id "EVT-012"
  title "TokenRemoved Event"
  kind B
  scope "all executors (event store enabled)"
  source verbatim "spec/08-events-observability.md"
  quote "Emitted when a token is removed from a place (consumed by input arc or cleared by reset arc)."
        "*When* a transition starts, the executor *shall* emit, for each place, one TokenRemoved event naming that place for each token the start removes from it, whether an input arc consumes the token or a reset arc drains it."
        "The executor *shall* emit TokenRemoved events only when a transition starts."
  reading "For every executor with events E and every configuration C:"
          "for every history H of the events emitted before the step, a start step of a name n, from state s to state s', that appends the events evs leaves, for every place p, the number of TokenRemoved events in evs naming p plus the length of p's queue in s' equal to the length of p's queue in s;"
          "the events a run emits before its first step contain no TokenRemoved event, whatever the initial marking, and for every history H a step whose label is not a start appends no TokenRemoved event."
  assumes "The model is an executor with events E : EvExec N T (Reference/Events.lean): the events a run emits before its first step, and a step relation E.step C H s l evs s' saying that the step labelled l leads from s to s' and appends the events evs, given the events H emitted before it. The witness is the reference executor with events refEvExec, the reference executor RefExec with its emission refEmitW, under both emission variants (polJT for Java and TypeScript, polRust for Rust and Python). refEvExec_erase (Reference/EventsLink.lean) shows that it steps exactly as RefExec, the executor the execution requirements hold of, so the block constrains what is emitted and nothing else. Both lines hold for every history H: no line here needs the earlier events."
          "Main block and companion (rulings D33 (a) and D38 (a)): this block reads an event only through its kind and the place it names (removedCount counts the events of kind TokenRemoved that name the place), which every executor's event carries. The token an event carries is read only by the second block of EVT-012, EVT_012_payload, scoped to the executors whose TokenRemoved event carries it: in Rust and Python the event carries the token only when the event store captures tokens (rust/libpetri-event/src/net_event.rs TokenRemoved, token an Option; event_store.rs CAPTURES_TOKENS, false by default; executor_core/event_payload.rs token_removed_event). Line 1 is the payload line with the tokens forgotten (evt012_of_payload)."
          "Removed is read as the executor model reads a start (EXEC-003, EXEC-010, EXEC-013): the start step consumes the input tokens and drains the reset places of the pass-visible marking, so a token a synchronous action deposited earlier in the same pass is neither removed nor reported, and a read arc removes nothing. Line 1 is the first two quoted sentences: one event per removed token, naming its place, whether an input arc or a reset arc removed it. An executor that reports no event for the tokens a reset arc drains breaks it (EVT_012_mutant_noResets); one that also reports the token a read arc reads breaks it, since the read place keeps its queue (EVT_012_forbids_readPeek). AC1 (emitted for every token removal) and AC2 (the place name identifies the source place) are line 1."
          "Line 2 is the third quoted sentence: nothing but a start emits a TokenRemoved event, neither the boot of a run (the events before its first step) nor a step with another label. An executor that reports the initial marking as removed at boot breaks it (EVT_012_mutant_bootRemoved), and so does one that reports a queued injection it discards after a close as a removal (EVT_012_mutant_atDiscard). No runtime removes a token elsewhere: Java emits TokenRemoved only in the consume of a start (java/src/main/java/org/libpetri/runtime/BitmapNetExecutor.java 1672-1724), TypeScript likewise (typescript/src/runtime/bitmap-net-executor.ts 1063 and 1085), and Rust only from consume_for_firing (rust/libpetri-runtime/src/executor_core/executor.rs 603-629), which Python runs on."
          "Not fixed here: the order of the TokenRemoved events across places (the reference emits the input places in declaration order, then the reset places, each place once at its first arc, as the runtimes walk the arcs; the payload order, inputs before resets, is EVT-006's under ruling D38 (a)), and that the TokenRemoved events of a start precede its TransitionStarted (EVT-006's first line). The timestamp the event carries is not modelled (the epoch clock is the CORE-011 slice). Correlated inputs of a match specification (ruling D16) take tokens that are not the oldest: the reference executor has no match specification, so the lines read every input place, and the correlated take is NU-020's (wave W9)."
          "Assumptions shared by the executor event blocks: the event store is enabled and its append does not fail (EVT-020: a store that reports itself not enabled receives nothing, storeSink); no host callback throws inside a start (an append or a key function that throws in the middle of a consume is out of scope); an event is a value (EVT-001); transition names are distinct (ruling D10). The events of one step are contiguous in the model, since a step appends its events at once. Java appends ActionTimedOut events and the log messages it captures from actions from other threads than the orchestrator (the timeout callback BitmapNetExecutor.fireTransition hands java/src/main/java/org/libpetri/runtime/ExecutorSupport.java withActionTimeout, which appends through emitEvent from the timer thread; LogCaptureScope.java wrapRunnable and wrapCallable), so in a Java store such an event can fall between the events of one step; the lines are read on the store with those events left out, as the reading at the top of spec/08-events-observability.md says. TypeScript and Rust append every event from the orchestrator."
          "The test derivation (fire a transition consuming a token, verify the TokenRemoved event) is EVT_012_nonvacuous: a start that takes two of the three tokens of an exactly(2) input, drains the old token of a reset place that also holds a same-pass deposit, and reads a read place emits two TokenRemoved events naming the input place, one naming the reset place and none naming the read place; a commit step emits events, none of them a TokenRemoved. A place named by two reset arcs is drained once, by its first arc (the builders append reset arcs without a check, and the runtimes walk them in declaration order: the reset-arc loop of BitmapNetExecutor.java fireTransition, bitmap-net-executor.ts 1080-1090, bitmap_backend.rs 835-857), so line 1 counts each drained token once: EVT_012_nonvacuous_repeatedReset fires a transition with reset arcs on places 0, 1 and 0 again and gets one event for the one token of place 0."
  signoff "2026-11-13 9c56a0df36d1cdf1 ai"
  statement : ∀ {N T : Type} [DecidableEq N], EvExec N T → Prop :=
    fun E => ∀ C,
      (∀ H n sy evs, on (fun s s' => E.step C H s (.start n sy) evs s'), shall (fun s s' =>
          ∀ p, removedCount evs p + (s'.M p).length = (s.M p).length)) ∧
      ((∀ M0, ∀ e ∈ E.boot C M0, e.kind ≠ .tokenRemoved) ∧
        ∀ H l evs, (∀ n sy, l ≠ .start n sy) →
          on (fun s s' => E.step C H s l evs s'), shall (fun _ _ =>
            ∀ e ∈ evs, e.kind ≠ .tokenRemoved))

/- The pinned readable form of EVT-012: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EVT_012 : {N T : Type} → [DecidableEq N] → EvExec N T → Prop :=
fun {N T} [DecidableEq N] E =>
  ∀ (C : Cfg N T),
    (∀ (H : List (NetEvent N T)) (n : String) (sy : Bool) (evs : List (NetEvent N T)),
        on fun s s' => E.step C H s (XLbl.start n sy) evs s', shall fun s s' =>
          ∀ (p : N), removedCount evs p + (s'.M p).length = (s.M p).length) ∧
      (∀ (M0 : QMarking N T), ∀ e ∈ E.boot C M0, e.kind ≠ NetEventKind.tokenRemoved) ∧
        ∀ (H : List (NetEvent N T)) (l : XLbl N T) (evs : List (NetEvent N T)),
          (∀ (n : String) (sy : Bool), l ≠ XLbl.start n sy) →
            on fun s s' => E.step C H s l evs s', shall fun x x_1 => ∀ e ∈ evs, e.kind ≠ NetEventKind.tokenRemoved
-/
#guard_msgs in #print EVT_012

/-! ## EVT-012, Java and TypeScript companion: which tokens, oldest first -/

requirement EVT_012_payload
  id "EVT-012"
  title "TokenRemoved Event (token payload)"
  kind B
  scope "Java and TypeScript executors; Rust and Python executors whose event store captures tokens (event store enabled); places without a correlated input of a match specification (NU-020)"
  source verbatim "spec/08-events-observability.md"
  quote "*Where* the TokenRemoved event carries the token (Java and TypeScript; Rust and Python when the event store captures tokens), the TokenRemoved events of a start *shall* carry, for each place, the tokens the start removes from it in the order they stood in the place's queue, and, where no correlated input of a match specification takes them ([NU-020]), these tokens followed by the tokens the place keeps *shall* be the place's queue before the start."
  reading "For every executor with events E, every configuration C and every history H: a start step of a name n, from state s to state s', that appends the events evs leaves, for every place p, the tokens of the TokenRemoved events in evs naming p, in event order, followed by p's queue in s', equal to p's queue in s."
  assumes "This is the second block of EVT-012 (rulings D33 (a) and D38 (a)): the token payload, for the executors whose TokenRemoved event carries the token. The first block, EVT_012, states the count and the emission point for every executor; this block adds which tokens and in which order. Java and TypeScript events always carry the token (BitmapNetExecutor.java 1672-1724, bitmap-net-executor.ts 1063 and 1085). Rust and Python carry it only when the event store captures tokens (the debug-aware stores and a Python store with capture on set CAPTURES_TOKENS; rust/libpetri-debug/src/debug_aware_event_store.rs, rust/libpetri-py/src/events.rs); otherwise the event carries no token and only the first block applies."
          "The model is an executor with events E : EvExec N T, as in the first block; the witness is refEvExec polJT. The line is the quoted sentence: per place, the tokens of the TokenRemoved events naming it, in emission order, followed by what the place holds after the start, are its queue before the start, so the reported tokens are the oldest of the queue, oldest first, and exactly the removed ones. The count line of the first block follows from it (evt012_of_payload). An executor that reports the right number of tokens per place but newest first meets the first block and breaks this line (EVT_012_payload_mutant_reversed)."
          "As in the first block, the removal is read on the pass-visible marking (EXEC-003): a reset place keeps the tokens a synchronous action deposited earlier in the pass, and they are not reported; read arcs remove nothing. Line 2 of the first block (no TokenRemoved event outside a start) is not restated. The order across places, the place of TransitionStarted among the events and the TransitionStarted payload are EVT-006's. Correlated inputs (ruling D16) are NU-020's: a correlated input of a match specification removes the frontmost token that matches the chosen name, which need not stand at the head of the queue, so the removed tokens keep their queue order but, followed by the kept tokens, are a reordering of the queue, not the queue (java/src/main/java/org/libpetri/runtime/BitmapNetExecutor.java 1666-1673, removeFirstMatching; typescript/src/runtime/bitmap-net-executor.ts 1047-1068; rust/libpetri-runtime/src/precompiled_backend.rs 1185-1192, ring_remove_matching). The quoted sentence scopes its second half to the other places, and a transition of the model has no match specification, so every place the line reads is of that kind; the queue order of the tokens a correlated input removes is left to NU-020; timestamps are not modelled; the shared assumptions of the first block (store enabled, no host callback throws inside a start, events are values, distinct names) apply."
          "The test derivation is EVT_012_payload_nonvacuous: the exactly(2) input reports 10 then 11 of 10, 11, 12 and keeps 12, and the reset place reports its old token 20 and keeps the same-pass 9."
  signoff "2026-11-13 053841e9c6f028d4 ai"
  statement : ∀ {N T : Type} [DecidableEq N], EvExec N T → Prop :=
    fun E => ∀ C H n sy evs,
      on (fun s s' => E.step C H s (.start n sy) evs s'), shall (fun s s' =>
        ∀ p, removedAt evs p ++ s'.M p = s.M p)

/- The pinned readable form of the companion: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EVT_012_payload : {N T : Type} → [DecidableEq N] → EvExec N T → Prop :=
fun {N T} [DecidableEq N] E =>
  ∀ (C : Cfg N T) (H : List (NetEvent N T)) (n : String) (sy : Bool) (evs : List (NetEvent N T)),
    on fun s s' => E.step C H s (XLbl.start n sy) evs s', shall fun s s' => ∀ (p : N), removedAt evs p ++ s'.M p = s.M p
-/
#guard_msgs in #print EVT_012_payload

/-! ## The two lines of the first block, one at a time -/

section Lines

variable {N T : Type} [DecidableEq N] [Ord N]
/-- Line 1 of `EVT_012` alone: per place, the `TokenRemoved` events of a start count the tokens
the place loses. -/
def evt012_line1 (E : EvExec N T) : Prop :=
  ∀ C H n sy evs, on (fun s s' => E.step C H s (.start n sy) evs s'), shall (fun s s' =>
    ∀ p, removedCount evs p + (s'.M p).length = (s.M p).length)

/-- Line 2 of `EVT_012` alone: nothing but a start emits a `TokenRemoved` event, neither the
boot nor a step with another label. -/
def evt012_line2 (E : EvExec N T) : Prop :=
  ∀ C, (∀ M0, ∀ e ∈ E.boot C M0, e.kind ≠ .tokenRemoved) ∧
    ∀ H l evs, (∀ n sy, l ≠ .start n sy) →
      on (fun s s' => E.step C H s l evs s'), shall (fun _ _ => ∀ e ∈ evs, e.kind ≠ .tokenRemoved)

omit [Ord N] in
/-- `EVT_012` is its two lines. -/
theorem evt012_iff (E : EvExec N T) : EVT_012 E ↔ evt012_line1 E ∧ evt012_line2 E :=
  ⟨fun h => ⟨fun C => (h C).1, fun C => (h C).2⟩,
   fun h C => ⟨h.1 C, h.2 C⟩⟩

omit [Ord N] in
/-- The count line is the payload line with the tokens forgotten: an executor that meets the
payload companion meets line 1 of the first block. -/
theorem evt012_of_payload {E : EvExec N T} (h : EVT_012_payload E) : evt012_line1 E := by
  intro C H n sy evs s s' hs p
  rw [removedCount_eq_length, ← List.length_append, h C H n sy evs s s' hs p]

end Lines

/-! ## The reference -/

section Reference

variable {N T : Type} [DecidableEq N] [Ord N]
/-- The reference meets the payload companion under every emission variant. -/
theorem evt012_payload_ref (P : EvPol) : EVT_012_payload (refEvExec (N := N) (T := T) P) := by
  intro C H n sy evs s s' hs p
  obtain ⟨hx, rfl⟩ := hs
  exact refStart_removedAt P H hx p

/-- The reference meets the first block under every emission variant. -/
theorem evt012_ref (P : EvPol) : EVT_012 (refEvExec (N := N) (T := T) P) :=
  (evt012_iff _).2 ⟨evt012_of_payload (evt012_payload_ref P), fun C =>
    ⟨refBoot_noRemoved P C, fun H l evs hl s s' hs => by
      obtain ⟨-, rfl⟩ := hs
      exact refEmitW_noRemoved P C H s hl s'⟩⟩

/-- ✓ The reference executor with the Java and TypeScript emission meets EVT-012: a start reports
one `TokenRemoved` event per token it removes, per place, and no other step reports one. -/
@[evidence holds EVT_012]
theorem EVT_012_reference : EVT_012 (refEvExec (N := N) (T := T) polJT) := evt012_ref polJT

/-- ✓ The reference executor with the Rust and Python emission meets EVT-012 too: the block is a
line for every executor. -/
@[evidence holds EVT_012]
theorem EVT_012_rust : EVT_012 (refEvExec (N := N) (T := T) polRust) := evt012_ref polRust

/-- ✓ The reference executor with the Java and TypeScript emission meets the payload companion:
the reported tokens of each place are its oldest, oldest first, and exactly the removed ones. -/
@[evidence holds EVT_012_payload]
theorem EVT_012_payload_reference : EVT_012_payload (refEvExec (N := N) (T := T) polJT) :=
  evt012_payload_ref polJT

end Reference

/-! ## The worked example -/

/-- Transition `a`: takes the token of place 3. -/
def evt012_tA : Trans Nat :=
  { core := { name := "a", inputs := [⟨3, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- Transition `u`: takes exactly two tokens from place 0, reads place 2, resets place 1. -/
def evt012_tU : Trans Nat :=
  { core := { name := "u", inputs := [⟨0, .exactly 2⟩], inhibitors := [], reads := [2],
              resets := [1] },
    out := none }

/-- The configuration of the example: places 0 to 3, both transitions Immediate and of one
priority (so `a` starts first), place 3 an environment place, no validation to speak of. -/
def evt012_cfg : Cfg Nat Nat :=
  { X := { net := { places := [0, 1, 2, 3], transitions := [evt012_tA, evt012_tU] },
           timing := fun _ => .immediate, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [3], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => false,
    res := 0 }

/-- The initial marking: 10, 11, 12 in place 0; 20 in place 1; 30 in place 2; 4 in place 3. -/
def evt012_m0 : QMarking Nat Nat := fun p =>
  if p = 0 then [10, 11, 12] else if p = 1 then [20] else if p = 2 then [30]
  else if p = 3 then [4] else []

/-- One cycle up to the firing pass, `a` started synchronously, its action writing 9 into place 1
and returning, its completion settled inside the pass. -/
def evt012_pre : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin,
   .start "a" true, .write 0 1 9, .ret 0 true]

/-- The state before `a`'s completion is settled. -/
def evt012_beforeCommit : Option (XSt Nat Nat) := xrun evt012_cfg (xinit evt012_m0 0) evt012_pre

/-- The state before `u` starts. -/
def evt012_beforeStart : Option (XSt Nat Nat) :=
  xrun evt012_cfg (xinit evt012_m0 0) (evt012_pre ++ [.commit 0])

/-- The state before a discard: a request into the environment place 3 accepted, then a close,
then step 1 and step 1b ended. -/
def evt012_beforeDiscard : Option (XSt Nat Nat) :=
  xrun evt012_cfg (xinit evt012_m0 0)
    [.request 3 5 .accepted, .close, .endCompletions, .endPublications]

/-- ✓ Both lines of the first block are exercised by the reference: `u`'s start emits two
`TokenRemoved` events naming place 0 (which goes from three tokens to one), one naming place 1
(which goes from the old 20 and the same-pass 9 to the 9), and none naming the read place 2
(which keeps its token); the commit of `a` before it emits events, none a `TokenRemoved`; and the
boot of the run emits events (`ExecutionStarted` and the snapshot), none a `TokenRemoved`,
although the initial marking holds six tokens. -/
@[evidence nonvacuous EVT_012]
theorem EVT_012_nonvacuous :
    (∃ s s' evs, (refEvExec polJT).step evt012_cfg [] s (.start "u" false) evs s' ∧
      removedCount evs 0 = 2 ∧ (s.M 0).length = 3 ∧ removedCount evs 1 = 1 ∧
      s.M 1 = [20, 9] ∧ s'.M 1 = [9] ∧ removedCount evs 2 = 0 ∧ s'.M 2 = [30]) ∧
    (∃ s s' evs, (refEvExec polJT).step evt012_cfg [] s (.commit 0) evs s' ∧ evs ≠ [] ∧
      ∀ e ∈ evs, e.kind ≠ .tokenRemoved) ∧
    ((refEvExec (N := Nat) (T := Nat) polJT).boot evt012_cfg evt012_m0 ≠ [] ∧
      ∀ e ∈ (refEvExec (N := Nat) (T := Nat) polJT).boot evt012_cfg evt012_m0,
        e.kind ≠ .tokenRemoved) := by
  refine ⟨?_, ?_, by decide +kernel⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt012_cfg) (o := evt012_beforeStart)
      (l := .start "u" false)
      (p := fun s s' =>
        let evs := refEmitW polJT evt012_cfg [] s (.start "u" false) s'
        removedCount evs 0 == 2 && (s.M 0).length == 3 && removedCount evs 1 == 1 &&
          s.M 1 == [20, 9] && s'.M 1 == [9] && removedCount evs 2 == 0 && s'.M 2 == [30])
      (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hp
    exact ⟨s, s', _, ⟨hs, rfl⟩, h1, h2, h3, h4, h5, h6, h7⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt012_cfg) (o := evt012_beforeCommit)
      (l := .commit 0)
      (p := fun s s' =>
        let evs := refEmitW polJT evt012_cfg [] s (.commit 0) s'
        !evs.isEmpty && evs.all fun e => e.kind != .tokenRemoved)
      (by decide +kernel)
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
      List.all_eq_true, bne_iff_ne, ne_eq] at hp
    exact ⟨s, s', _, ⟨hs, rfl⟩, hp.1, hp.2⟩

/-- ✓ The payload line is exercised by the reference: `u`'s start reports 10 then 11 for place 0,
which keeps 12, and the old 20 for place 1, which keeps the same-pass 9; nothing for the read
place 2. -/
@[evidence nonvacuous EVT_012_payload]
theorem EVT_012_payload_nonvacuous :
    ∃ s s' evs, (refEvExec polJT).step evt012_cfg [] s (.start "u" false) evs s' ∧
      removedAt evs 0 = [10, 11] ∧ s'.M 0 = [12] ∧ removedAt evs 1 = [20] ∧ s'.M 1 = [9] ∧
      removedAt evs 2 = [] := by
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt012_cfg) (o := evt012_beforeStart)
    (l := .start "u" false)
    (p := fun s s' =>
      let evs := refEmitW polJT evt012_cfg [] s (.start "u" false) s'
      removedAt evs 0 == [10, 11] && s'.M 0 == [12] && removedAt evs 1 == [20] &&
        s'.M 1 == [9] && removedAt evs 2 == [])
    (by decide +kernel)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hp
  exact ⟨s, s', _, ⟨hs, rfl⟩, h1, h2, h3, h4, h5⟩

/-- Transition `r` of the repeated-reset example: takes the token of place 2 and has three reset
arcs, on places 0, 1 and 0 again, in that declaration order. -/
def evt012_tR : Trans Nat :=
  { core := { name := "r", inputs := [⟨2, .one⟩], inhibitors := [], reads := [],
              resets := [0, 1, 0] },
    out := none }

/-- The repeated-reset example: the one transition `r` over places 0, 1 and 2. -/
def evt012_dupCfg : Cfg Nat Nat :=
  { X := { net := { places := [0, 1, 2], transitions := [evt012_tR] },
           timing := fun _ => .immediate, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => false,
    res := 0 }

/-- The initial marking of the repeated-reset example: 10 in place 0, 20 in place 1, 30 in
place 2. -/
def evt012_dupM0 : QMarking Nat Nat := fun p =>
  if p = 0 then [10] else if p = 1 then [20] else if p = 2 then [30] else []

/-- The state before `r` starts: one cycle up to the firing pass. -/
def evt012_dupBeforeStart : Option (XSt Nat Nat) :=
  xrun evt012_dupCfg (xinit evt012_dupM0 0)
    [.endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin]

/-- ✓ A place named by two reset arcs is drained once, at its first arc: `r` takes 30 from place
2 and has reset arcs on places 0, 1 and 0 again. Its start reports 30, then 10 for place 0, then
20 for place 1, one event for the one token of place 0, which ends empty, and the reset places in
the order of their first arcs, as the runtimes walk them. -/
@[evidence nonvacuous EVT_012]
theorem EVT_012_nonvacuous_repeatedReset :
    ∃ s s' evs, (refEvExec polJT).step evt012_dupCfg [] s (.start "r" false) evs s' ∧
      evs = [.tokenRemoved 2 30, .tokenRemoved 0 10, .tokenRemoved 1 20,
        .transitionStarted "r" [(2, 30), (0, 10), (1, 20)]] ∧
      removedCount evs 0 = 1 ∧ s.M 0 = [10] ∧ s'.M 0 = [] := by
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt012_dupCfg)
    (o := evt012_dupBeforeStart) (l := .start "r" false)
    (p := fun s s' =>
      let evs := refEmitW polJT evt012_dupCfg [] s (.start "r" false) s'
      evs == [.tokenRemoved 2 30, .tokenRemoved 0 10, .tokenRemoved 1 20,
          .transitionStarted "r" [(2, 30), (0, 10), (1, 20)]] &&
        removedCount evs 0 == 1 && s.M 0 == [10] && s'.M 0 == [])
    (by decide +kernel)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hp
  exact ⟨s, s', _, ⟨hs, rfl⟩, h1, h2, h3, h4⟩

/-! ## Wrong executors: the reference's steps, another emission -/

section Mutants

variable {N T : Type} [DecidableEq N] [Ord N]
/-- The Java and TypeScript emission with the events of a start replaced by `f C s n`. -/
def evt012_atStart (f : Cfg N T → XSt N T → String → List (NetEvent N T)) (C : Cfg N T)
    (H : List (NetEvent N T)) (s : XSt N T) (l : XLbl N T) (s' : XSt N T) : List (NetEvent N T) :=
  match l with
  | .start n _ => f C s n
  | _ => refEmitW polJT C H s l s'

/-- Away from a start, `evt012_atStart` emits as the reference. -/
theorem evt012_atStart_other (f : Cfg N T → XSt N T → String → List (NetEvent N T))
    (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T) {l : XLbl N T}
    (hl : ∀ n sy, l ≠ .start n sy) (s' : XSt N T) :
    evt012_atStart f C H s l s' = refEmitW polJT C H s l s' := by
  cases l with
  | start n sy => exact absurd rfl (hl n sy)
  | _ => rfl

/-- An executor that only changes what a start emits keeps line 2. -/
theorem evt012_atStart_line2 (f : Cfg N T → XSt N T → String → List (NetEvent N T)) :
    evt012_line2 (emitExec (refBoot polJT) (evt012_atStart f)) := by
  intro C
  refine ⟨refBoot_noRemoved polJT C, fun H l evs hl s s' hs => ?_⟩
  obtain ⟨-, rfl⟩ := hs
  rw [evt012_atStart_other f C H s hl s']
  exact refEmitW_noRemoved polJT C H s hl s'

/-- The start events with the input tokens only: no event for what a reset arc drains. -/
def evt012_noResetsEvs (_C : Cfg N T) (s : XSt N T) (n : String) : List (NetEvent N T) :=
  match s.order with
  | t :: _ =>
    (dedupFirst (inPlaces t)).flatMap
        (fun p => (qInputs (vis s) t p).map (NetEvent.tokenRemoved p)) ++
      [.transitionStarted n (removedListDecl (vis s) t)]
  | [] => []

/-- The executor that reports no event for the tokens a reset arc drains. -/
def evt012_noResets : EvExec N T :=
  emitExec (refBoot polJT) (evt012_atStart evt012_noResetsEvs)

/-- The start events with one more `TokenRemoved` per read arc, for the token it reads. -/
def evt012_readPeekEvs (_C : Cfg N T) (s : XSt N T) (n : String) : List (NetEvent N T) :=
  match s.order with
  | t :: _ =>
    removedEvs (vis s) t ++
      t.core.reads.flatMap (fun p => ((vis s p).take 1).map (NetEvent.tokenRemoved p)) ++
      [.transitionStarted n (removedListDecl (vis s) t)]
  | [] => []

/-- The executor that also reports the token a read arc reads as removed. -/
def evt012_readPeek : EvExec N T :=
  emitExec (refBoot polJT) (evt012_atStart evt012_readPeekEvs)

/-- The start events with each place's tokens reported newest first. -/
def evt012_reversedEvs (_C : Cfg N T) (s : XSt N T) (n : String) : List (NetEvent N T) :=
  match s.order with
  | t :: _ =>
    (dedupFirst (inPlaces t)).flatMap
        (fun p => (qInputs (vis s) t p).reverse.map (NetEvent.tokenRemoved p)) ++
      (dedupFirst t.core.resets).flatMap
        (fun p => (drained (vis s) t p).reverse.map (NetEvent.tokenRemoved p)) ++
      [.transitionStarted n (removedListDecl (vis s) t)]
  | [] => []

/-- The executor that reports the removed tokens of each place newest first. -/
def evt012_reversed : EvExec N T :=
  emitExec (refBoot polJT) (evt012_atStart evt012_reversedEvs)

/-- The Java and TypeScript emission, with a discarded injection reported as a removal from its
place. -/
def evt012_discardEmit (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T) (l : XLbl N T)
    (s' : XSt N T) : List (NetEvent N T) :=
  match l with
  | .discard _ =>
    match s.eq with
    | (_, p, x) :: _ => [.tokenRemoved p x]
    | [] => []
  | _ => refEmitW polJT C H s l s'

/-- The executor that reports a queued injection it discards after a close as a removal. -/
def evt012_atDiscard : EvExec N T := emitExec (refBoot polJT) evt012_discardEmit

/-- The Java and TypeScript boot events followed by one `TokenRemoved` for every token of the
initial marking on a declared place. -/
def evt012_bootRemovedEvs (C : Cfg N T) (M0 : QMarking N T) : List (NetEvent N T) :=
  refBoot polJT C M0 ++
    C.X.net.places.dedup.flatMap fun p => (M0 p).map (NetEvent.tokenRemoved p)

/-- The executor that steps and emits as the reference but reports the initial marking as
removed at boot. -/
def evt012_bootRemoved : EvExec N T := emitExec evt012_bootRemovedEvs (refEmitW polJT)

omit [Ord N] in
/-- The reversed start reports, per place, the removed tokens newest first. -/
theorem evt012_removedAt_reversedEvs {C : Cfg N T} {s : XSt N T} {t : Trans N}
    {rest : List (Trans N)} (ho : s.order = t :: rest) (n : String) (p : N) :
    removedAt (evt012_reversedEvs C s n) p =
      (qInputs (vis s) t p).reverse ++ (drained (vis s) t p).reverse := by
  simp only [evt012_reversedEvs, ho, removedAt_append,
    removedAt_flatMap (fun q => (qInputs (vis s) t q).reverse) _ (nodup_dedupFirst _),
    removedAt_flatMap (fun q => (drained (vis s) t q).reverse) _ (nodup_dedupFirst _),
    mem_dedupFirst]
  have h0 : removedAt ([.transitionStarted n (removedListDecl (vis s) t)] :
      List (NetEvent N T)) p = [] := rfl
  rw [h0, List.append_nil]
  congr 1
  · by_cases h : p ∈ inPlaces t
    · simp [h]
    · simp [h, qInputs_of_not_mem h]
  · by_cases h : p ∈ t.core.resets
    · simp [h]
    · simp [h, drained]

/-- Reporting newest first keeps the first block: the count per place is unchanged. -/
theorem evt012_reversed_meets : EVT_012 (evt012_reversed (N := N) (T := T)) := by
  refine (evt012_iff _).2 ⟨?_, evt012_atStart_line2 _⟩
  intro C H n sy evs s s' hs p
  obtain ⟨hx, rfl⟩ := hs
  obtain ⟨t, rest, ho, -, hq⟩ := xstep_start_qRemoved hx
  have hl := congrArg List.length (hq p)
  simp only [List.length_append] at hl
  show removedCount (evt012_reversedEvs C s n) p + _ = _
  rw [removedCount_eq_length, evt012_removedAt_reversedEvs ho, ← hl]
  simp [qRemoved]

/-- The start emission of the reference keeps line 1 for any executor that emits as the
reference at a start, whatever its boot events. -/
theorem evt012_line1_of_refStart {boot : Cfg N T → QMarking N T → List (NetEvent N T)}
    {emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    (he : ∀ C H s n sy s', emit C H s (.start n sy) s' = refEmitW polJT C H s (.start n sy) s') :
    evt012_line1 (emitExec boot emit) := by
  intro C H n sy evs s s' hs p
  obtain ⟨hx, rfl⟩ := hs
  rw [he, removedCount_eq_length, ← List.length_append, refStart_removedAt polJT H hx p]

end Mutants

/-- ✗ Leaving out the tokens a reset arc drains violates EVT-012 (line 1): `u`'s reset arc
takes the old 20 from place 1, which goes from two tokens to one, and no event names place 1.
The executor keeps line 2. -/
@[evidence mutant EVT_012]
theorem EVT_012_mutant_noResets :
    evt012_line2 (evt012_noResets (N := Nat) (T := Nat)) ∧
      ¬ EVT_012 (evt012_noResets (N := Nat) (T := Nat)) := by
  refine ⟨evt012_atStart_line2 _, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt012_cfg) (o := evt012_beforeStart)
    (l := .start "u" false)
    (p := fun s s' =>
      removedCount (evt012_noResetsEvs evt012_cfg s "u") 1 + (s'.M 1).length != (s.M 1).length)
    (by decide +kernel)
  simp only [bne_iff_ne, ne_eq] at hp
  exact hp ((h evt012_cfg).1 [] "u" false _ s s' ⟨hs, rfl⟩ 1)

/-- ✗ Reporting the token a read arc reads as removed violates EVT-012 (line 1): `u` reads 30
from place 2, which keeps it, and one event names place 2. -/
@[evidence forbids EVT_012]
theorem EVT_012_forbids_readPeek : ¬ EVT_012 (evt012_readPeek (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt012_cfg) (o := evt012_beforeStart)
    (l := .start "u" false)
    (p := fun s s' =>
      removedCount (evt012_readPeekEvs evt012_cfg s "u") 2 + (s'.M 2).length != (s.M 2).length)
    (by decide +kernel)
  simp only [bne_iff_ne, ne_eq] at hp
  exact hp ((h evt012_cfg).1 [] "u" false _ s s' ⟨hs, rfl⟩ 2)

/-- ✗ Reporting a discarded injection as a removal violates EVT-012 (line 2): after a close, the
queued injection of 5 into place 3 is discarded, and the discard step emits a `TokenRemoved`.
The executor keeps line 1, since its starts emit as the reference. -/
@[evidence mutant EVT_012]
theorem EVT_012_mutant_atDiscard :
    evt012_line1 (evt012_atDiscard (N := Nat) (T := Nat)) ∧
      ¬ EVT_012 (evt012_atDiscard (N := Nat) (T := Nat)) := by
  refine ⟨evt012_line1_of_refStart fun _ _ _ _ _ _ => rfl, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt012_cfg) (o := evt012_beforeDiscard)
    (l := .discard 0)
    (p := fun s s' => (evt012_discardEmit evt012_cfg [] s (.discard 0) s').any
      fun e => e.kind == .tokenRemoved)
    (by decide +kernel)
  simp only [List.any_eq_true, beq_iff_eq] at hp
  obtain ⟨e, he, hk⟩ := hp
  exact (h evt012_cfg).2.2 [] (.discard 0) _ (fun _ _ => by simp) s s' ⟨hs, rfl⟩ e he hk

/-- ✗ Reporting the initial marking as removed when the run boots violates EVT-012 (line 2): the
boot of the example reports token 10 of place 0 as removed although no transition has started.
Every step of this executor, starts included, emits as the reference, so it keeps line 1. -/
@[evidence mutant EVT_012]
theorem EVT_012_mutant_bootRemoved :
    evt012_line1 (evt012_bootRemoved (N := Nat) (T := Nat)) ∧
      ¬ EVT_012 (evt012_bootRemoved (N := Nat) (T := Nat)) := by
  refine ⟨evt012_line1_of_refStart fun _ _ _ _ _ _ => rfl, fun h => ?_⟩
  have hm : NetEvent.tokenRemoved 0 10 ∈ evt012_bootRemoved.boot evt012_cfg evt012_m0 := by
    decide +kernel
  exact (h evt012_cfg).2.1 evt012_m0 _ hm rfl

/-- ✗ Reporting each place's removed tokens newest first meets the first block (the counts are
right) and violates the payload companion: `u`'s start reports 11 before 10 for place 0, so the
reported tokens followed by the kept 12 are 11, 10, 12, not the queue 10, 11, 12. -/
@[evidence mutant EVT_012_payload]
theorem EVT_012_payload_mutant_reversed :
    EVT_012 (evt012_reversed (N := Nat) (T := Nat)) ∧
      ¬ EVT_012_payload (evt012_reversed (N := Nat) (T := Nat)) := by
  refine ⟨evt012_reversed_meets, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt012_cfg) (o := evt012_beforeStart)
    (l := .start "u" false)
    (p := fun s s' => removedAt (evt012_reversedEvs evt012_cfg s "u") 0 ++ s'.M 0 != s.M 0)
    (by decide +kernel)
  simp only [bne_iff_ne, ne_eq] at hp
  exact hp (h evt012_cfg [] "u" false _ s s' ⟨hs, rfl⟩ 0)

/-- ✗ Leaving out the tokens a reset arc drains violates the payload companion too: place 1
loses the old 20 and no event reports it. -/
@[evidence forbids EVT_012_payload]
theorem EVT_012_payload_forbids_noResets :
    ¬ EVT_012_payload (evt012_noResets (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt012_cfg) (o := evt012_beforeStart)
    (l := .start "u" false)
    (p := fun s s' => removedAt (evt012_noResetsEvs evt012_cfg s "u") 1 ++ s'.M 1 != s.M 1)
    (by decide +kernel)
  simp only [bne_iff_ne, ne_eq] at hp
  exact hp (h evt012_cfg [] "u" false _ s s' ⟨hs, rfl⟩ 1)

end Libpetri.Spec
