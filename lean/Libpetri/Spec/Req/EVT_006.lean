import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Events
import Libpetri.Spec.Req.EVT_012

set_option linter.missingDocs true

/-!
# EVT-006: TransitionStarted Event (`spec/08-events-observability.md`)

When a transition starts, the executor reports the tokens the start removes (one `TokenRemoved`
event per token, [EVT-012]) and then one `TransitionStarted` event naming the transition; it
reports a start at no other time. The requirement has two blocks with the same spec ID (rulings
D33 (a) and D38 (a)):

* `EVT_006`, for every executor: it reads an event only through its kind and the transition it
  names, which every runtime's event carries. Line 1: a start takes the head of the firing order,
  named as the start says, and its events are `TokenRemoved` events followed by exactly one
  `TransitionStarted` naming that transition, the last event of the start. Line 2: nothing else
  emits a `TransitionStarted`, neither another step nor the boot of a run. Which `TokenRemoved`
  events a start emits is EVT-012's.
* `EVT_006_payload`, for the executors whose `TransitionStarted` carries the removed tokens
  (Java and TypeScript; the Rust and Python event has no token list). Line 1: the list holds
  the tokens of the start's `TokenRemoved` events, in the same order. Line 2: the list is every
  token the firing rule removes from the pass-visible marking, the input arcs first in
  declaration order, then the reset arcs in declaration order, each place's tokens oldest first
  (`removedListDecl`).

Both are predicates over an abstract executor with events `E : EvExec N T`
(`Reference/Events.lean`); the witness is the reference executor with events `refEvExec`. The
wrong executors step as the reference (or, for the misnamed one, start the head under another
name) and emit otherwise: one that reports the start before the removals, one whose synchronous
path reports the start after the inline action, one that reports a start again when the action's
result is committed, one that reports a start for a head the pass can no longer start, one that
reports the start under another transition's name, one that lists only the input tokens (ruling
D38 (b)), one that also lists the tokens the read arcs read, one that lists the reset arcs'
tokens first, and one that takes a place named by two reset arcs at its last arc.

The worked example is EVT-012's (`evt012_cfg`): transition `a` takes the token of place 3 and its
synchronous action writes 9 into place 1; then `u` starts: it takes 10 and 11 from place 0, drains
the old 20 from place 1 through a reset arc, reads 30 from place 2. Its start reports
`TokenRemoved` 0 10, 0 11, 1 20, then `TransitionStarted u` listing (0, 10), (0, 11), (1, 20).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## EVT-006, every executor: removals first, then one TransitionStarted, only at a start -/

requirement EVT_006
  id "EVT-006"
  title "TransitionStarted Event"
  kind B
  scope "all executors (event store enabled)"
  source verbatim "spec/08-events-observability.md"
  quote "Emitted when a transition begins firing (tokens consumed, action dispatched)."
        "*When* a transition starts, the executor *shall* emit exactly one TransitionStarted event naming that transition as the last event of the start, and no event before it in that start other than TokenRemoved events ([EVT-012])."
        "The executor *shall* emit TransitionStarted events only when a transition starts."
  reading "For every executor with events E and every configuration C:"
          "for every history H of the events emitted before the step, a start step of a name n, from state s to state s', takes the head of the order of s, a transition named n, and appends events evs that are a list of TokenRemoved events followed by one TransitionStarted event naming n;"
          "the events a run emits before its first step contain no TransitionStarted event, whatever the initial marking, and for every history H a step whose label is not a start appends no TransitionStarted event."
  assumes "The model is an executor with events E : EvExec N T (Reference/Events.lean), as for EVT-012: the events a run emits before its first step, and a step relation E.step C H s l evs s' saying that the step labelled l leads from s to s' and appends the events evs, given the events H emitted before it. The witness is refEvExec, the reference executor RefExec with its emission refEmitW, under both emission variants (polJT for Java and TypeScript, polRust for Rust and Python); refEvExec_erase shows that it steps exactly as RefExec, so the block constrains what is emitted and, through the head of the order, which transition a start reports. Both lines hold for every history H."
          "Main block and companion (rulings D33 (a) and D38 (a)): this block reads an event only through its kind and the transition it names. The list of removed tokens is read only by the second block of EVT-006, EVT_006_payload, scoped to Java and TypeScript: the Rust TransitionStarted event carries the transition name and a timestamp only (rust/libpetri-event/src/net_event.rs TransitionStarted), and Python rides on it. Line 1 leaves the payload of the TransitionStarted event free, and AC2 (the list matches the removed tokens) is the companion's, scoped to Java and TypeScript in the markdown."
          "Line 1 is the first two quoted sentences. A start is the step that takes the head of the firing order and consumes and drains its tokens (EXEC-003, EXEC-010, EXEC-013). Line 1 says that head is the transition the start names, so the TransitionStarted names the transition whose tokens the start removes; an executor that reports the start of u under the name of another transition breaks it (EVT_006_mutant_misnamed). A TransitionStarted that is the last event of the start, after every TokenRemoved event of it, is emitted after token consumption (AC1, first half); an executor that reports the start before the removals breaks line 1 (EVT_006_mutant_startedFirst). Java emits the TokenRemoved events inside the consume and TransitionStarted after it, before it calls the action (java/src/main/java/org/libpetri/runtime/BitmapNetExecutor.java 1672-1733; PrecompiledNetExecutor.java 2334-2357), TypeScript likewise (typescript/src/runtime/bitmap-net-executor.ts 1063-1103; precompiled-net-executor.ts 1102-1201), and Rust from consume_and_emit then TransitionStarted, in both firing paths (rust/libpetri-runtime/src/executor_core/executor.rs 830-836 and 1469-1476)."
          "Action dispatched in the first quoted sentence names the moment of the event, not a further obligation: the start step is the dispatch, and that a ready transition can start is the executor model's (EXEC-003, EXEC-010), not a clause of this block. The action runs in later steps (its writes, its return, its log messages, the commit of its result), so every event the action causes comes after the TransitionStarted in the trace (AC1, second half). An executor whose synchronous path reports the start only after the inline action, when its result is committed, breaks both lines (EVT_006_forbids_syncStartedAfterAction: the synchronous start of a ends with a TokenRemoved event)."
          "Which TokenRemoved events a start emits is EVT-012's, as the cross-reference in the second quoted sentence says. Line 1 alone accepts a start with no TokenRemoved event, and line 2 alone accepts a TokenRemoved event of the start reported in a later step: EVT-012's line 1 (one event per removed token, place by place) rejects the first and its line 2 (TokenRemoved only at a start) the second. EVT_006_with_EVT_012_noRemovals shows the two blocks together reject an executor whose start reports TransitionStarted alone, which EVT_006 alone accepts; the realistic slip is a Rust consume_and_emit that gates the TokenRemoved append on the store capturing tokens instead of on the store being enabled (rust/libpetri-runtime/src/executor_core/executor.rs 603-631, event_payload.rs 28-39)."
          "Line 2 is the third quoted sentence: no runtime emits TransitionStarted outside these firing sites. An executor that reports a start again when it commits the action's result breaks it (EVT_006_mutant_startedAtCommit), and so does one that reports a start for a head of the order the pass finds it can no longer start, a lose step (EVT_006_mutant_startedOnLose); Java and TypeScript recheck that the head can fire before they consume and emit (BitmapNetExecutor.java 1672-1733, bitmap-net-executor.ts 1063-1103)."
          "Not fixed here: the timestamp the event carries (the epoch clock is the CORE-011 slice; so TIME-006's note that exact timing is observable from the firing event is not stated over this model); the defensive copy of the list (EVT-001; an event is a value here); which tokens are removed and in which order across places (EVT-012, and the payload companion below); correlated inputs of a match specification (ruling D16; the reference executor has no match specification, NU-020 owns the correlated take)."
          "Assumptions shared by the executor event blocks: the event store is enabled and its append does not fail (EVT-020); no host callback throws inside a start (an append or a key function that throws in the middle of a consume is out of scope); an event is a value (EVT-001); transition names are distinct (ruling D10). The events of one step are contiguous in the model, since a step appends its events at once. Java appends ActionTimedOut events and the log messages it captures from actions from other threads than the orchestrator (the timeout callback BitmapNetExecutor.fireTransition hands java/src/main/java/org/libpetri/runtime/ExecutorSupport.java withActionTimeout, which appends through emitEvent from the timer thread; LogCaptureScope.java wrapRunnable and wrapCallable), so in a Java store such an event can fall between the events of one step; the lines are read on the store with those events left out, as the reading at the top of spec/08-events-observability.md says. TypeScript and Rust append every event from the orchestrator."
          "The test derivation (fire a transition that consumes 2 tokens through an input arc and drains 1 through a reset arc, verify its 3 TokenRemoved events and then its TransitionStarted) is split: the shape is EVT_006_nonvacuous (u's start emits three TokenRemoved events, then TransitionStarted u, last), the listed tokens are EVT_006_payload_nonvacuous."
  signoff "2026-11-13 90c1568dfa620ec8 ai"
  statement : ∀ {N T : Type} [DecidableEq N], EvExec N T → Prop :=
    fun E => ∀ C,
      (∀ H n sy evs, on (fun s s' => E.step C H s (.start n sy) evs s'), shall (fun s _ =>
          (∃ t rest, s.order = t :: rest ∧ t.core.name = n) ∧
          ∃ rs : List (NetEvent _ _), ∃ pl, evs = rs ++ [.transitionStarted n pl] ∧
            ∀ e ∈ rs, e.kind = .tokenRemoved)) ∧
      ((∀ M0, ∀ e ∈ E.boot C M0, e.kind ≠ .transitionStarted) ∧
        ∀ H l evs, (∀ n sy, l ≠ .start n sy) →
          on (fun s s' => E.step C H s l evs s'), shall (fun _ _ =>
            ∀ e ∈ evs, e.kind ≠ .transitionStarted))

/- The pinned readable form of EVT-006: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EVT_006 : {N T : Type} → [DecidableEq N] → EvExec N T → Prop :=
fun {N T} [DecidableEq N] E =>
  ∀ (C : Cfg N T),
    (∀ (H : List (NetEvent N T)) (n : String) (sy : Bool) (evs : List (NetEvent N T)),
        on fun s s' => E.step C H s (XLbl.start n sy) evs s', shall fun s x =>
          (∃ t rest, s.order = t :: rest ∧ t.core.name = n) ∧
            ∃ rs pl, evs = rs ++ [NetEvent.transitionStarted n pl] ∧ ∀ e ∈ rs, e.kind = NetEventKind.tokenRemoved) ∧
      (∀ (M0 : QMarking N T), ∀ e ∈ E.boot C M0, e.kind ≠ NetEventKind.transitionStarted) ∧
        ∀ (H : List (NetEvent N T)) (l : XLbl N T) (evs : List (NetEvent N T)),
          (∀ (n : String) (sy : Bool), l ≠ XLbl.start n sy) →
            on fun s s' => E.step C H s l evs s', shall fun x x_1 => ∀ e ∈ evs, e.kind ≠ NetEventKind.transitionStarted
-/
#guard_msgs in #print EVT_006

/-! ## EVT-006, Java and TypeScript companion: the removed tokens -/

/-- The `TokenRemoved` events of a list of place and token pairs, one per pair, in list order. -/
def removalEvents {N T : Type} (pl : List (N × T)) : List (NetEvent N T) :=
  pl.map fun x => .tokenRemoved x.1 x.2

requirement EVT_006_payload
  id "EVT-006"
  title "TransitionStarted Event (removed tokens)"
  kind B
  scope "Java and TypeScript executors (event store enabled)"
  source verbatim "spec/08-events-observability.md"
  quote "*Where* the TransitionStarted event carries the removed tokens (Java and TypeScript), it *shall* list the tokens of the TokenRemoved events of the same start, in the same order."
        "*Where* the TransitionStarted event carries the removed tokens (Java and TypeScript), the list *shall* hold every token the firing rule removes from the marking visible to the pass ([EXEC-003], [EXEC-013]): the tokens the input arcs consume, then the tokens the reset arcs drain, each group in declaration order and each place's tokens oldest first."
  reading "For every executor with events E, every configuration C, every history H, and every start step of a name n from state s to state s' that appends the events evs:"
          "evs is the TokenRemoved events of a list pl of place and token pairs, in the order of pl, followed by one TransitionStarted event naming n that lists pl;"
          "the start takes the head t of the pass's order, a transition named n, and every TransitionStarted event in evs lists removedListDecl (vis s) t: for each input place of t in declaration order the tokens its input arc consumes from the pass-visible marking, oldest first, then for each reset place of t in declaration order the tokens its reset arc drains, oldest first."
  assumes "This is the second block of EVT-006 (rulings D33 (a) and D38 (a)): the removed-token list, for the executors whose TransitionStarted event carries it. The first block, EVT_006, states the shape and the emission point for every executor. Java's TransitionStarted carries List<Token<?>> consumedTokens (java/src/main/java/org/libpetri/event/NetEvent.java TransitionStarted) and TypeScript's consumedTokens (typescript/src/event/net-event.ts); Rust's carries none, so this block does not apply to Rust and Python. The runtimes call the list consumed tokens; under ruling D38 (a) it holds every removed token, consumed by an input arc or drained by a reset arc, which the markdown now says."
          "Line 1 is the first quoted sentence. Java and TypeScript append each removed token to the list at the moment they emit its TokenRemoved event, and emit TransitionStarted with that list (BitmapNetExecutor.java 1672-1733, PrecompiledNetExecutor.java 2328-2357, bitmap-net-executor.ts 1060-1103, precompiled-net-executor.ts 1094-1201). The runtimes list tokens only; the model pairs each listed token with the place its TokenRemoved event names, which line 1 makes the same thing, so the pairing adds nothing a runtime list does not determine from the events before it. With EVT_012_payload (per place, the tokens of the TokenRemoved events are the oldest of the queue and exactly the removed ones) line 1 gives AC2, the list matches the tokens the start actually removes (evt006_payload_matches). An executor that lists only the tokens the input arcs consume, the reading D38 (b) rejected, breaks line 1 (EVT_006_payload_mutant_inputsOnly), and so does one that also lists the tokens its read arcs read (EVT_006_payload_forbids_readsIncluded)."
          "Line 2 is the second quoted sentence (ruling D38 (a): the list is every removed token, inputs then resets). It computes the list with the firing rule from the source state (removedListDecl over the pass-visible marking vis s), not from the observed change of the marking: oldest first and the count per arc are the firing rule's (EXEC-003, EXEC-013, CORE-030, CORE-034), and that these are the tokens the step really removes is AC2 above. The start consumes and drains the pass-visible marking, so a token a synchronous action deposited earlier in the same pass is neither drained nor listed, and read arcs remove nothing. Java and TypeScript, bitmap and precompiled, walk the input arcs in declaration order, then the read arcs (peek only), then the reset arcs in declaration order (BitmapNetExecutor.java 1660-1731; PrecompiledNet.java compileFireProgram; typescript/src/runtime/precompiled-net.ts compileConsumeProgram). An executor that lists and reports the reset arcs' tokens first meets line 1 and breaks line 2 (EVT_006_payload_mutant_resetsFirst), and one that reports the start under another transition's name, listing that transition's tokens, breaks it too (EVT_006_payload_mutant_misnamed)."
          "Each place appears at most once per group: a transition has at most one input arc per place (CORE-030 rejects a second at build). A place named by two reset arcs is legal (the builders append reset arcs without a check) and is drained by its first arc in declaration order, the later arcs finding nothing the pass can drain (the reset-arc loop of BitmapNetExecutor.java fireTransition, bitmap-net-executor.ts 1080-1090, bitmap_backend.rs 835-857). removedListDecl takes each input place and each reset place once, at its first arc, so reset arcs on places 0, 1 and 0 again list place 0's drained tokens before place 1's (EVT_006_payload_nonvacuous_repeatedReset); an executor that takes such a place at its last arc lists place 1 first and breaks line 2 (EVT_006_payload_mutant_lastOccurrence). A place that is both an input place and a reset place lists its consumed tokens in the input group and the rest in the reset group, as Java's consume does."
          "As in the first block: the timestamp is not modelled, the defensive copy is EVT-001's, correlated inputs (ruling D16) are NU-020's, and the shared assumptions (store enabled, no host callback throws inside a start, events are values, distinct names) apply."
          "The test derivation (fire a transition that consumes 2 tokens through an input arc and drains 1 through a reset arc, verify TransitionStarted lists the same 3 tokens as its TokenRemoved events) is EVT_006_payload_nonvacuous: u's exactly(2) input consumes 10 and 11 and its reset arc drains 20, and TransitionStarted u lists (0, 10), (0, 11), (1, 20), the same as its three TokenRemoved events."
  signoff "2026-11-13 d4acea5fcf17d913 ai"
  statement : ∀ {N T : Type} [DecidableEq N], EvExec N T → Prop :=
    fun E => ∀ C H n sy evs,
      (on (fun s s' => E.step C H s (.start n sy) evs s'), shall (fun _ _ =>
        ∃ pl, evs = removalEvents pl ++ [.transitionStarted n pl])) ∧
      (on (fun s s' => E.step C H s (.start n sy) evs s'), shall (fun s _ =>
        ∃ t rest, s.order = t :: rest ∧ t.core.name = n ∧
          ∀ m pl, .transitionStarted m pl ∈ evs → pl = removedListDecl (vis s) t))

/- The pinned readable form of the companion: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EVT_006_payload : {N T : Type} → [DecidableEq N] → EvExec N T → Prop :=
fun {N T} [DecidableEq N] E =>
  ∀ (C : Cfg N T) (H : List (NetEvent N T)) (n : String) (sy : Bool) (evs : List (NetEvent N T)),
    (on fun s s' => E.step C H s (XLbl.start n sy) evs s', shall fun x x_1 =>
        ∃ pl, evs = removalEvents pl ++ [NetEvent.transitionStarted n pl]) ∧
      on fun s s' => E.step C H s (XLbl.start n sy) evs s', shall fun s x =>
        ∃ t rest,
          s.order = t :: rest ∧
            t.core.name = n ∧
              ∀ (m : String) (pl : List (N × T)), NetEvent.transitionStarted m pl ∈ evs → pl = removedListDecl (vis s) t
-/
#guard_msgs in #print EVT_006_payload

/-! ## The lines, one at a time -/

section Lines

variable {N T : Type}

/-- Line 1 of `EVT_006` alone: a start takes the head of the order, named as the start says, and
emits `TokenRemoved` events, then one `TransitionStarted` naming the transition. -/
def evt006_line1 (E : EvExec N T) : Prop :=
  ∀ C H n sy evs, on (fun s s' => E.step C H s (.start n sy) evs s'), shall (fun s _ =>
    (∃ t rest, s.order = t :: rest ∧ t.core.name = n) ∧
    ∃ rs pl, evs = rs ++ [.transitionStarted n pl] ∧ ∀ e ∈ rs, e.kind = .tokenRemoved)

/-- Line 2 of `EVT_006` alone: nothing but a start emits a `TransitionStarted`, neither the boot
nor a step with another label. -/
def evt006_line2 (E : EvExec N T) : Prop :=
  ∀ C, (∀ M0, ∀ e ∈ E.boot C M0, e.kind ≠ .transitionStarted) ∧
    ∀ H l evs, (∀ n sy, l ≠ .start n sy) →
      on (fun s s' => E.step C H s l evs s'), shall (fun _ _ =>
        ∀ e ∈ evs, e.kind ≠ .transitionStarted)

/-- `EVT_006` is its two lines. -/
theorem evt006_iff [DecidableEq N] [Ord N] (E : EvExec N T) : EVT_006 E ↔ evt006_line1 E ∧ evt006_line2 E :=
  ⟨fun h => ⟨fun C => (h C).1, fun C => (h C).2⟩, fun h C => ⟨h.1 C, h.2 C⟩⟩

/-- Line 1 of the companion alone: the list of a start's `TransitionStarted` is the tokens of its
`TokenRemoved` events, in order. -/
def evt006_payload_line1 (E : EvExec N T) : Prop :=
  ∀ C H n sy evs, on (fun s s' => E.step C H s (.start n sy) evs s'), shall (fun _ _ =>
    ∃ pl, evs = removalEvents pl ++ [.transitionStarted n pl])

/-- The companion implies line 1 of the first block: its line 1 gives the shape, its line 2 the
named head. -/
theorem evt006_line1_of_payload [DecidableEq N] [Ord N] {E : EvExec N T} (h : EVT_006_payload E) :
    evt006_line1 E := by
  intro C H n sy evs s s' hs
  obtain ⟨pl, rfl⟩ := (h C H n sy _).1 s s' hs
  obtain ⟨t, rest, ho, hn, -⟩ := (h C H n sy _).2 s s' hs
  refine ⟨⟨t, rest, ho, hn⟩, _, pl, rfl, fun e he => ?_⟩
  simp only [removalEvents, List.mem_map] at he
  obtain ⟨_, _, rfl⟩ := he
  rfl

/-- The `TokenRemoved` events of a list of place and token pairs, read at `p`: the tokens the
list pairs with `p`, in order. -/
theorem removedAt_removalEvents [DecidableEq N] [Ord N] (pl : List (N × T)) (p : N) :
    removedAt (removalEvents pl) p = qEmittedTo pl p := by
  induction pl with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : x.1 = p
    · simp only [removalEvents, removedAt, qEmittedTo, List.map_cons, List.filterMap_cons, h, if_true,
        List.filter_cons, decide_true] at ih ⊢
      rw [ih]
    · simp only [removalEvents, removedAt, qEmittedTo, List.map_cons, List.filterMap_cons, h, if_false,
        List.filter_cons, decide_false] at ih ⊢
      exact ih

end Lines

/-- **AC2, the list matches the tokens the start removes.** An executor that meets line 1 of the
companion and the EVT-012 payload companion lists, at every start and for every place, the
tokens the start removes from the place, oldest first: the listed tokens of the place followed by
what it keeps are its queue before the start. For `u` in the example, place 0's listed 10, 11
followed by the kept 12 are its queue 10, 11, 12. -/
@[evidence cites "EVT-006" "AC2 (the removed-tokens list matches the tokens the start actually removes): with EVT_012_payload, line 1 of the companion makes the list of a start's TransitionStarted, place by place, exactly the tokens the start removes, oldest first"]
theorem evt006_payload_matches {N T : Type} [DecidableEq N] [Ord N] {E : EvExec N T}
    (h6 : evt006_payload_line1 E) (h12 : EVT_012_payload E) {C : Cfg N T}
    {H : List (NetEvent N T)} {n : String} {sy : Bool} {evs : List (NetEvent N T)}
    {s s' : XSt N T} (hs : E.step C H s (.start n sy) evs s') :
    ∃ pl, .transitionStarted n pl ∈ evs ∧ ∀ p, qEmittedTo pl p ++ s'.M p = s.M p := by
  obtain ⟨pl, hpl⟩ := h6 C H n sy evs s s' hs
  refine ⟨pl, by simp [hpl], fun p => ?_⟩
  have h := h12 C H n sy evs s s' hs p
  rw [hpl, removedAt_append, removedAt_removalEvents] at h
  have h0 : removedAt ([.transitionStarted n pl] : List (NetEvent N T)) p = [] := rfl
  rwa [h0, List.append_nil] at h

/-! ## The reference -/

section Reference

variable {N T : Type} [DecidableEq N] [Ord N]
omit [DecidableEq N] [Ord N] in
/-- A label that is not a start has no `TransitionStarted` among its kinds. -/
theorem started_not_mem_lblKinds {l : XLbl N T} (hl : ∀ n sy, l ≠ .start n sy) :
    NetEventKind.transitionStarted ∉ lblKinds l := by
  cases l with
  | start n sy => exact absurd rfl (hl n sy)
  | _ => simp [lblKinds]

/-- The reference emits no `TransitionStarted` outside a start, and none at boot. -/
theorem evt006_line2_ref (P : EvPol) : evt006_line2 (refEvExec (N := N) (T := T) P) := by
  intro C
  refine ⟨fun M0 e he hk => ?_, fun H l evs hl s s' hs e he hk => ?_⟩
  · rcases refBoot_kind P C M0 e he with h | h <;> rw [hk] at h <;> cases h
  · obtain ⟨-, rfl⟩ := hs
    have := refEmitW_kind P C H s l s' e he
    rw [hk] at this
    exact started_not_mem_lblKinds hl this

/-- The reference meets the companion under every emission variant. -/
theorem evt006_payload_ref (P : EvPol) : EVT_006_payload (refEvExec (N := N) (T := T) P) := by
  intro C H n sy evs
  refine ⟨fun s s' hs => ?_, fun s s' hs => ?_⟩
  · obtain ⟨hx, rfl⟩ := hs
    obtain ⟨t, rest, ho, -, -⟩ := xstep_start_qRemoved hx
    exact ⟨removedListDecl (vis s) t, by rw [refEmitW_start P C H ho]; rfl⟩
  · obtain ⟨hx, rfl⟩ := hs
    obtain ⟨t, rest, ho, hn, -⟩ := xstep_start_qRemoved hx
    refine ⟨t, rest, ho, hn, fun m pl hm => ?_⟩
    rw [refEmitW_start P C H ho] at hm
    rcases List.mem_append.1 hm with h | h
    · have := kind_of_mem_removedEvs h
      simp [NetEvent.kind] at this
    · simp only [List.mem_singleton, NetEvent.transitionStarted.injEq] at h
      exact h.2

/-- The reference meets the first block under every emission variant. -/
theorem evt006_ref (P : EvPol) : EVT_006 (refEvExec (N := N) (T := T) P) :=
  (evt006_iff _).2 ⟨evt006_line1_of_payload (evt006_payload_ref P), evt006_line2_ref P⟩

/-- ✓ The reference executor with the Java and TypeScript emission meets EVT-006: a start takes
the transition it names, reports its removals, then one `TransitionStarted` naming the
transition, and nothing else reports a start. -/
@[evidence holds EVT_006]
theorem EVT_006_reference : EVT_006 (refEvExec (N := N) (T := T) polJT) := evt006_ref polJT

/-- ✓ The reference executor with the Rust and Python emission meets EVT-006 too: the block is a
line for every executor. -/
@[evidence holds EVT_006]
theorem EVT_006_rust : EVT_006 (refEvExec (N := N) (T := T) polRust) := evt006_ref polRust

/-- ✓ The reference executor with the Java and TypeScript emission meets the companion: the list
of a start's `TransitionStarted` is the tokens of its `TokenRemoved` events, input arcs first in
declaration order, then reset arcs. -/
@[evidence holds EVT_006_payload]
theorem EVT_006_payload_reference : EVT_006_payload (refEvExec (N := N) (T := T) polJT) :=
  evt006_payload_ref polJT

end Reference

/-! ## The worked example -/

/-- ✓ Both lines of the first block are exercised by the reference: `u`'s start takes `u`, the
head of the order, emits three `TokenRemoved` events (10 and 11 from place 0, 20 from place 1)
and then `TransitionStarted u`, the last event of the start; the commit of `a` before it emits
events, none a `TransitionStarted`; and the boot of the run emits events, none a
`TransitionStarted`. -/
@[evidence nonvacuous EVT_006]
theorem EVT_006_nonvacuous :
    (∃ s s' evs, (refEvExec polJT).step evt012_cfg [] s (.start "u" false) evs s' ∧
      (∃ t rest, s.order = t :: rest ∧ t.core.name = "u") ∧
      evs = [.tokenRemoved 0 10, .tokenRemoved 0 11, .tokenRemoved 1 20,
        .transitionStarted "u" [(0, 10), (0, 11), (1, 20)]]) ∧
    (∃ s s' evs, (refEvExec polJT).step evt012_cfg [] s (.commit 0) evs s' ∧ evs ≠ [] ∧
      ∀ e ∈ evs, e.kind ≠ .transitionStarted) ∧
    ((refEvExec (N := Nat) (T := Nat) polJT).boot evt012_cfg evt012_m0 ≠ [] ∧
      ∀ e ∈ (refEvExec (N := Nat) (T := Nat) polJT).boot evt012_cfg evt012_m0,
        e.kind ≠ .transitionStarted) := by
  refine ⟨?_, ?_, by decide +kernel⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt012_cfg) (o := evt012_beforeStart)
      (l := .start "u" false)
      (p := fun s s' => refEmitW polJT evt012_cfg [] s (.start "u" false) s' ==
        [.tokenRemoved 0 10, .tokenRemoved 0 11, .tokenRemoved 1 20,
          .transitionStarted "u" [(0, 10), (0, 11), (1, 20)]])
      (by decide +kernel)
    simp only [beq_iff_eq] at hp
    obtain ⟨t, rest, ho, hn, -⟩ := xstep_start_qRemoved hs
    exact ⟨s, s', _, ⟨hs, rfl⟩, ⟨t, rest, ho, hn⟩, hp⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt012_cfg) (o := evt012_beforeCommit)
      (l := .commit 0)
      (p := fun s s' =>
        let evs := refEmitW polJT evt012_cfg [] s (.commit 0) s'
        !evs.isEmpty && evs.all fun e => e.kind != .transitionStarted)
      (by decide +kernel)
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
      List.all_eq_true, bne_iff_ne, ne_eq] at hp
    exact ⟨s, s', _, ⟨hs, rfl⟩, hp.1, hp.2⟩

/-- ✓ The companion is exercised by the reference: `u` consumes 10 and 11 from place 0 and drains
20 from place 1; its `TransitionStarted` lists (0, 10), (0, 11), (1, 20), the same tokens in the
same order as its three `TokenRemoved` events, the input place before the reset place. -/
@[evidence nonvacuous EVT_006_payload]
theorem EVT_006_payload_nonvacuous :
    ∃ s s' evs, (refEvExec polJT).step evt012_cfg [] s (.start "u" false) evs s' ∧
      .transitionStarted "u" [(0, 10), (0, 11), (1, 20)] ∈ evs ∧
      (∃ t rest, s.order = t :: rest ∧ t.core.name = "u" ∧
        removedListDecl (vis s) t = [(0, 10), (0, 11), (1, 20)]) := by
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt012_cfg) (o := evt012_beforeStart)
    (l := .start "u" false)
    (p := fun s s' =>
      (refEmitW polJT evt012_cfg [] s (.start "u" false) s').contains
          (.transitionStarted "u" [(0, 10), (0, 11), (1, 20)]) &&
        match s.order with
        | t :: _ => removedListDecl (vis s) t == [(0, 10), (0, 11), (1, 20)]
        | [] => false)
    (by decide +kernel)
  simp only [Bool.and_eq_true, List.contains_iff_mem] at hp
  obtain ⟨h1, h2⟩ := hp
  obtain ⟨t, rest, ho, hn, -⟩ := xstep_start_qRemoved hs
  refine ⟨s, s', _, ⟨hs, rfl⟩, h1, t, rest, ho, hn, ?_⟩
  rw [ho] at h2
  simpa only [beq_iff_eq] using h2

/-! ## Wrong executors: the reference's steps, another emission -/

section Mutants

variable {N T : Type} [DecidableEq N] [Ord N]
/-- An executor that only changes what a start emits keeps line 2 of the first block. -/
theorem evt006_atStart_line2 (f : Cfg N T → XSt N T → String → List (NetEvent N T)) :
    evt006_line2 (emitExec (refBoot polJT) (evt012_atStart f)) := by
  intro C
  refine ⟨fun M0 e he hk => ?_, fun H l evs hl s s' hs e he hk => ?_⟩
  · rcases refBoot_kind polJT C M0 e he with h | h <;> rw [hk] at h <;> cases h
  · obtain ⟨-, rfl⟩ := hs
    rw [evt012_atStart_other f C H s hl s'] at he
    have := refEmitW_kind polJT C H s l s' e he
    rw [hk] at this
    exact started_not_mem_lblKinds hl this

/-- The start events built from two lists of the head `t` of the order: `TokenRemoved` events of
`ev s t`, then `TransitionStarted` listing `pay s t`. -/
def evt006_startWith (ev pay : XSt N T → Trans N → List (N × T)) (_C : Cfg N T) (s : XSt N T)
    (n : String) : List (NetEvent N T) :=
  match s.order with
  | t :: _ => removalEvents (ev s t) ++ [.transitionStarted n (pay s t)]
  | [] => []

/-- An executor whose start emits `evt006_startWith ev pay` meets the first block, whatever the
two lists. -/
theorem evt006_startWith_meets (ev pay : XSt N T → Trans N → List (N × T)) :
    EVT_006 (emitExec (refBoot polJT) (evt012_atStart (evt006_startWith ev pay))) := by
  refine (evt006_iff _).2 ⟨?_, evt006_atStart_line2 _⟩
  intro C H n sy evs s s' hs
  obtain ⟨hx, rfl⟩ := hs
  obtain ⟨t, rest, ho, hn, -⟩ := xstep_start_qRemoved hx
  refine ⟨⟨t, rest, ho, hn⟩, removalEvents (ev s t), pay s t, ?_, fun e he => ?_⟩
  · show evt006_startWith ev pay C s n = _
    simp only [evt006_startWith, ho]
  · simp only [removalEvents, List.mem_map] at he
    obtain ⟨_, _, rfl⟩ := he
    rfl

/-- An executor whose start emits `evt006_startWith f f` (the list is the reported tokens) meets
line 1 of the companion. -/
theorem evt006_startWith_line1 (f : XSt N T → Trans N → List (N × T)) :
    evt006_payload_line1 (emitExec (refBoot polJT) (evt012_atStart (evt006_startWith f f))) := by
  intro C H n sy evs s s' hs
  obtain ⟨hx, rfl⟩ := hs
  obtain ⟨t, rest, ho, -, -⟩ := xstep_start_qRemoved hx
  exact ⟨f s t, by show evt006_startWith f f C s n = _; simp only [evt006_startWith, ho]⟩

/-- The start events with `TransitionStarted` first, then the removals. -/
def evt006_startedFirstEvs (_C : Cfg N T) (s : XSt N T) (n : String) : List (NetEvent N T) :=
  match s.order with
  | t :: _ => .transitionStarted n (removedListDecl (vis s) t) :: removedEvs (vis s) t
  | [] => []

/-- The executor that reports the start before the tokens it removes. -/
def evt006_startedFirst : EvExec N T :=
  emitExec (refBoot polJT) (evt012_atStart evt006_startedFirstEvs)

/-- The Java and TypeScript emission, with a `TransitionStarted` of the committed firing's
transition before the events of a commit. -/
def evt006_commitEmit (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T) (l : XLbl N T)
    (s' : XSt N T) : List (NetEvent N T) :=
  match l with
  | .commit i =>
    match s.fl.find? (·.id == i) with
    | some f => .transitionStarted f.t.core.name [] :: refEmitW polJT C H s l s'
    | none => refEmitW polJT C H s l s'
  | _ => refEmitW polJT C H s l s'

/-- The executor that reports a start again when it commits the action's result. -/
def evt006_startedAtCommit : EvExec N T := emitExec (refBoot polJT) evt006_commitEmit

/-- The Java and TypeScript emission with the synchronous path reporting the start late: a
synchronous start emits only its removals, and the commit of a synchronous firing emits the
`TransitionStarted` of its transition before its own events. -/
def evt006_syncLateEmit (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T) (l : XLbl N T)
    (s' : XSt N T) : List (NetEvent N T) :=
  match l with
  | .start _ true =>
    match s.order with
    | t :: _ => removedEvs (vis s) t
    | [] => []
  | .commit i =>
    match s.fl.find? (·.id == i) with
    | some f =>
      if f.sync then .transitionStarted f.t.core.name [] :: refEmitW polJT C H s l s'
      else refEmitW polJT C H s l s'
    | none => refEmitW polJT C H s l s'
  | _ => refEmitW polJT C H s l s'

/-- The executor whose synchronous path reports the start after the inline action. -/
def evt006_syncStartedLate : EvExec N T := emitExec (refBoot polJT) evt006_syncLateEmit

/-- The Java and TypeScript emission with a `TransitionStarted` for a head that is lost. -/
def evt006_loseEmit (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T) (l : XLbl N T)
    (s' : XSt N T) : List (NetEvent N T) :=
  match l with
  | .lose n => [.transitionStarted n []]
  | _ => refEmitW polJT C H s l s'

/-- The executor that reports a start for a head the pass can no longer start. -/
def evt006_startedOnLose : EvExec N T := emitExec (refBoot polJT) evt006_loseEmit

/-- The executor that reports a start under another transition's name: a start labelled `n`
takes the head of the order whatever its name, and emits as the reference does for `n`, so the
`TransitionStarted n` lists the head's tokens. -/
def evt006_misnamed : EvExec N T where
  boot := refBoot polJT
  step := fun C H s l evs s' => evs = refEmitW polJT C H s l s' ∧
    (xstep C s l = some s' ∨ ∃ n m sy, l = .start n sy ∧ xstep C s (.start m sy) = some s')

/-- The tokens the input arcs of `t` consume from `M`, place by place in declaration order; no
reset tokens. -/
def evt006_inputsOnlyList (M : QMarking N T) (t : Trans N) : List (N × T) :=
  (dedupFirst (inPlaces t)).flatMap fun p => (qInputs M t p).map (p, ·)

/-- The tokens the reset arcs of `t` drain from `M`, then the tokens its input arcs consume. -/
def evt006_resetsFirstList (M : QMarking N T) (t : Trans N) : List (N × T) :=
  (dedupFirst t.core.resets).flatMap (fun p => (drained M t p).map (p, ·)) ++
    evt006_inputsOnlyList M t

/-- The removed tokens with each place taken at its last arc rather than its first (what
Mathlib's `List.dedup` keeps): a reset list 0, 1, 0 lists place 1's tokens before place 0's. -/
def evt006_lastOccList (M : QMarking N T) (t : Trans N) : List (N × T) :=
  (inPlaces t).dedup.flatMap (fun p => (qInputs M t p).map (p, ·)) ++
    t.core.resets.dedup.flatMap (fun p => (drained M t p).map (p, ·))

/-- The removed tokens, then the head of every read place: what the read arcs read. -/
def evt006_withReadsList (M : QMarking N T) (t : Trans N) : List (N × T) :=
  removedListDecl M t ++ t.core.reads.flatMap fun p => ((M p).take 1).map (p, ·)

/-- The executor that reports every removed token but lists only the consumed input tokens
(ruling D38 (b)). -/
def evt006_inputsOnly : EvExec N T :=
  emitExec (refBoot polJT) (evt012_atStart (evt006_startWith
    (fun s t => removedListDecl (vis s) t) (fun s t => evt006_inputsOnlyList (vis s) t)))

/-- The executor that also lists the tokens its read arcs read. -/
def evt006_readsIncluded : EvExec N T :=
  emitExec (refBoot polJT) (evt012_atStart (evt006_startWith
    (fun s t => removedListDecl (vis s) t) (fun s t => evt006_withReadsList (vis s) t)))

/-- The executor that reports and lists the reset arcs' tokens before the input arcs' tokens. -/
def evt006_resetsFirst : EvExec N T :=
  emitExec (refBoot polJT) (evt012_atStart (evt006_startWith
    (fun s t => evt006_resetsFirstList (vis s) t) (fun s t => evt006_resetsFirstList (vis s) t)))

/-- The executor that reports and lists a place named by several reset arcs at its last arc. -/
def evt006_lastOcc : EvExec N T :=
  emitExec (refBoot polJT) (evt012_atStart (evt006_startWith
    (fun s t => evt006_lastOccList (vis s) t) (fun s t => evt006_lastOccList (vis s) t)))

/-- The executor whose start reports `TransitionStarted` and no `TokenRemoved` event. -/
def evt006_noRemovals : EvExec N T :=
  emitExec (refBoot polJT) (evt012_atStart (evt006_startWith
    (fun _ _ => []) (fun s t => removedListDecl (vis s) t)))

omit [DecidableEq N] [Ord N] in
/-- Line 1 of the first block pins the last event of a start: a `TransitionStarted`. -/
theorem evt006_last_of_line1 {evs : List (NetEvent N T)} {n : String}
    (h : ∃ rs pl, evs = rs ++ [.transitionStarted n pl] ∧ ∀ e ∈ rs, e.kind = .tokenRemoved) :
    (evs.getLast?.map NetEvent.kind) = some .transitionStarted := by
  obtain ⟨rs, pl, rfl, -⟩ := h
  simp [NetEvent.kind]

/-- Whether the list of the last event, a `TransitionStarted`, differs from the tokens of the
events before it. -/
def evt006_payloadMismatch [DecidableEq T] (evs : List (NetEvent N T)) : Bool :=
  match evs.getLast? with
  | some (.transitionStarted _ q) => evs.dropLast != removalEvents q
  | _ => true

omit [Ord N] in
/-- Line 1 of the companion leaves no mismatch. -/
theorem evt006_noMismatch_of_line1 [DecidableEq T] {evs : List (NetEvent N T)} {n : String}
    (h : ∃ pl, evs = removalEvents pl ++ [.transitionStarted n pl]) :
    evt006_payloadMismatch evs = false := by
  obtain ⟨pl, rfl⟩ := h
  simp [evt006_payloadMismatch]

/-- The executor whose start emits as the reference keeps line 1 of the first block, whatever
its other steps emit. -/
theorem evt006_line1_of_refStart {boot : Cfg N T → QMarking N T → List (NetEvent N T)}
    {emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    (he : ∀ C H s n sy s', emit C H s (.start n sy) s' = refEmitW polJT C H s (.start n sy) s') :
    evt006_line1 (emitExec boot emit) := by
  intro C H n sy evs s s' hs
  obtain ⟨hx, rfl⟩ := hs
  obtain ⟨t, rest, ho, hn, -⟩ := xstep_start_qRemoved hx
  rw [he, refEmitW_start polJT C H ho]
  exact ⟨⟨t, rest, ho, hn⟩, _, _, rfl, fun e he => kind_of_mem_removedEvs he⟩

/-- The misnamed executor emits as the reference everywhere, so it keeps line 2 of the first
block. -/
theorem evt006_misnamed_line2 : evt006_line2 (evt006_misnamed (N := N) (T := T)) := by
  intro C
  refine ⟨fun M0 e he hk => ?_, fun H l evs hl s s' hs e he hk => ?_⟩
  · rcases refBoot_kind polJT C M0 e he with h | h <;> rw [hk] at h <;> cases h
  · obtain ⟨rfl, -⟩ := hs
    have := refEmitW_kind polJT C H s l s' e he
    rw [hk] at this
    exact started_not_mem_lblKinds hl this

/-- The misnamed executor's start lists the tokens of its `TokenRemoved` events, so it keeps
line 1 of the companion. -/
theorem evt006_misnamed_payload_line1 : evt006_payload_line1 (evt006_misnamed (N := N) (T := T)) := by
  intro C H n sy evs s s' hs
  obtain ⟨rfl, hx⟩ := hs
  have hx' : ∃ m, xstep C s (.start m sy) = some s' := by
    rcases hx with hx | ⟨n', m, sy', he, hx⟩
    · exact ⟨n, hx⟩
    · simp only [XLbl.start.injEq] at he
      obtain ⟨-, rfl⟩ := he
      exact ⟨m, hx⟩
  obtain ⟨m, hx'⟩ := hx'
  obtain ⟨t, rest, ho, -, -⟩ := xstep_start_qRemoved hx'
  exact ⟨removedListDecl (vis s) t, by rw [refEmitW_start polJT C H ho]; rfl⟩

end Mutants

/-- ✗ Reporting the start before the tokens it removes violates EVT-006 (line 1): `u`'s start
emits `TransitionStarted u` first and its last event is `TokenRemoved` 1 20. Nothing else
changes, so the executor keeps line 2. -/
@[evidence mutant EVT_006]
theorem EVT_006_mutant_startedFirst :
    evt006_line2 (evt006_startedFirst (N := Nat) (T := Nat)) ∧
      ¬ EVT_006 (evt006_startedFirst (N := Nat) (T := Nat)) := by
  refine ⟨evt006_atStart_line2 _, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt012_cfg) (o := evt012_beforeStart)
    (l := .start "u" false)
    (p := fun s _ => (evt006_startedFirstEvs evt012_cfg s "u").getLast?.map NetEvent.kind !=
      some .transitionStarted)
    (by decide +kernel)
  simp only [bne_iff_ne, ne_eq] at hp
  exact hp (evt006_last_of_line1 ((h evt012_cfg).1 [] "u" false _ s s' ⟨hs, rfl⟩).2)

/-- The state before `a` starts synchronously: one cycle up to the firing pass of the example. -/
def evt006_beforeSyncStart : Option (XSt Nat Nat) :=
  xrun evt012_cfg (xinit evt012_m0 0)
    [.endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin]

/-- ✗ Reporting a synchronous start only after the inline action, when its result is committed,
violates EVT-006 on both lines: the synchronous start of `a` emits only `TokenRemoved` 3 4, so
its last event is no `TransitionStarted` (line 1), and the commit of `a` emits
`TransitionStarted a` (line 2). -/
@[evidence forbids EVT_006]
theorem EVT_006_forbids_syncStartedAfterAction :
    ¬ EVT_006 (evt006_syncStartedLate (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt012_cfg) (o := evt006_beforeSyncStart)
    (l := .start "a" true)
    (p := fun s s' => (evt006_syncLateEmit evt012_cfg [] s (.start "a" true) s').getLast?.map
      NetEvent.kind != some .transitionStarted)
    (by decide +kernel)
  simp only [bne_iff_ne, ne_eq] at hp
  exact hp (evt006_last_of_line1 ((h evt012_cfg).1 [] "a" true _ s s' ⟨hs, rfl⟩).2)

/-- ✗ Reporting a start again when the action's result is committed violates EVT-006 (line 2):
the commit of `a` emits `TransitionStarted a` before its `TransitionCompleted`. Its starts emit as
the reference, so it keeps line 1. -/
@[evidence mutant EVT_006]
theorem EVT_006_mutant_startedAtCommit :
    evt006_line1 (evt006_startedAtCommit (N := Nat) (T := Nat)) ∧
      ¬ EVT_006 (evt006_startedAtCommit (N := Nat) (T := Nat)) := by
  refine ⟨evt006_line1_of_refStart fun _ _ _ _ _ _ => rfl, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt012_cfg) (o := evt012_beforeCommit)
    (l := .commit 0)
    (p := fun s s' => (evt006_commitEmit evt012_cfg [] s (.commit 0) s').any
      fun e => e.kind == .transitionStarted)
    (by decide +kernel)
  simp only [List.any_eq_true, beq_iff_eq] at hp
  obtain ⟨e, he, hk⟩ := hp
  exact (h evt012_cfg).2.2 [] (.commit 0) _ (fun _ _ => by simp) s s' ⟨hs, rfl⟩ e he hk

/-- Transition `a` of the lose example: takes the one token of place 0. -/
def evt006_loseA : Trans Nat :=
  { core := { name := "a", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- Transition `b` of the lose example: takes the one token of place 0 too. -/
def evt006_loseB : Trans Nat :=
  { core := { name := "b", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- The lose example: `a` and `b` compete for the one token of place 0. -/
def evt006_loseCfg : Cfg Nat Nat :=
  { X := { net := { places := [0], transitions := [evt006_loseA, evt006_loseB] },
           timing := fun _ => .immediate, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => false,
    res := 0 }

/-- The initial marking of the lose example: place 0 holds 7. -/
def evt006_loseM0 : QMarking Nat Nat := fun p => if p = 0 then [7] else []

/-- The state after `a` started and took the token, `b` at the head of the order. -/
def evt006_beforeLose : Option (XSt Nat Nat) :=
  xrun evt006_loseCfg (xinit evt006_loseM0 0)
    [.endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin,
     .start "a" false]

/-- ✗ Reporting a start for a head the pass can no longer start violates EVT-006 (line 2): `a`
and `b` both want the one token of place 0, `a` starts and takes it, and the step that drops `b`
emits `TransitionStarted b` though `b` never starts. Its starts emit as the reference, so it
keeps line 1. -/
@[evidence mutant EVT_006]
theorem EVT_006_mutant_startedOnLose :
    evt006_line1 (evt006_startedOnLose (N := Nat) (T := Nat)) ∧
      ¬ EVT_006 (evt006_startedOnLose (N := Nat) (T := Nat)) := by
  refine ⟨evt006_line1_of_refStart fun _ _ _ _ _ _ => rfl, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt006_loseCfg) (o := evt006_beforeLose)
    (l := .lose "b")
    (p := fun s s' => (evt006_loseEmit evt006_loseCfg [] s (.lose "b") s').any
      fun e => e.kind == .transitionStarted)
    (by decide +kernel)
  simp only [List.any_eq_true, beq_iff_eq] at hp
  obtain ⟨e, he, hk⟩ := hp
  exact (h evt006_loseCfg).2.2 [] (.lose "b") _ (fun _ _ => by simp) s s' ⟨hs, rfl⟩ e he hk

/-- ✗ Reporting a start under another transition's name violates EVT-006 (line 1): the executor
starts `u`, the head of the order, but reports it as a start of `a`, emitting `u`'s three
`TokenRemoved` events and then `TransitionStarted a`. Every event it emits is one the reference
would emit for that label, so it keeps line 2. -/
@[evidence mutant EVT_006]
theorem EVT_006_mutant_misnamed :
    evt006_line2 (evt006_misnamed (N := Nat) (T := Nat)) ∧
      ¬ EVT_006 (evt006_misnamed (N := Nat) (T := Nat)) := by
  refine ⟨evt006_misnamed_line2, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt012_cfg) (o := evt012_beforeStart)
    (l := .start "u" false)
    (p := fun s _ => match s.order with
      | t :: _ => t.core.name != "a"
      | [] => false)
    (by decide +kernel)
  have hm : evt006_misnamed.step evt012_cfg [] s (.start "a" false)
      (refEmitW polJT evt012_cfg [] s (.start "a" false) s') s' :=
    ⟨rfl, Or.inr ⟨"a", "u", false, rfl, hs⟩⟩
  obtain ⟨⟨t, rest, ho, hn⟩, -⟩ := (h evt012_cfg).1 [] "a" false _ s s' hm
  rw [ho] at hp
  simp only [bne_iff_ne, ne_eq] at hp
  exact hp hn

/-- ✗ Listing only the tokens the input arcs consume (the reading ruling D38 (b) rejected) meets
the first block and violates the companion (line 1): `u`'s start reports 10, 11 and the drained
20, but its `TransitionStarted` lists only (0, 10), (0, 11). -/
@[evidence mutant EVT_006_payload]
theorem EVT_006_payload_mutant_inputsOnly :
    EVT_006 (evt006_inputsOnly (N := Nat) (T := Nat)) ∧
      ¬ EVT_006_payload (evt006_inputsOnly (N := Nat) (T := Nat)) := by
  refine ⟨evt006_startWith_meets _ _, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt012_cfg) (o := evt012_beforeStart)
    (l := .start "u" false)
    (p := fun s _ => evt006_payloadMismatch (evt006_startWith
      (fun s t => removedListDecl (vis s) t) (fun s t => evt006_inputsOnlyList (vis s) t)
      evt012_cfg s "u"))
    (by decide +kernel)
  have h1 : ∃ pl, evt006_startWith (fun s t => removedListDecl (vis s) t)
      (fun s t => evt006_inputsOnlyList (vis s) t) evt012_cfg s "u" =
        removalEvents pl ++ [.transitionStarted "u" pl] :=
    (h evt012_cfg [] "u" false _).1 s s' ⟨hs, rfl⟩
  rw [evt006_noMismatch_of_line1 h1] at hp
  cases hp

/-- ✗ Also listing the token a read arc reads violates the companion (line 1): `u` reads 30 from
place 2, which keeps it, and its `TransitionStarted` lists (2, 30) after the three removed
tokens, while no `TokenRemoved` event reports it. -/
@[evidence forbids EVT_006_payload]
theorem EVT_006_payload_forbids_readsIncluded :
    ¬ EVT_006_payload (evt006_readsIncluded (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt012_cfg) (o := evt012_beforeStart)
    (l := .start "u" false)
    (p := fun s _ => evt006_payloadMismatch (evt006_startWith
      (fun s t => removedListDecl (vis s) t) (fun s t => evt006_withReadsList (vis s) t)
      evt012_cfg s "u"))
    (by decide +kernel)
  have h1 : ∃ pl, evt006_startWith (fun s t => removedListDecl (vis s) t)
      (fun s t => evt006_withReadsList (vis s) t) evt012_cfg s "u" =
        removalEvents pl ++ [.transitionStarted "u" pl] :=
    (h evt012_cfg [] "u" false _).1 s s' ⟨hs, rfl⟩
  rw [evt006_noMismatch_of_line1 h1] at hp
  cases hp

/-- ✗ Reporting and listing the reset arcs' tokens first meets line 1 of the companion (the list
is the reported tokens) and violates line 2: `u`'s start lists (1, 20), (0, 10), (0, 11), the
drained token of reset place 1 before the tokens input place 0 consumes. -/
@[evidence mutant EVT_006_payload]
theorem EVT_006_payload_mutant_resetsFirst :
    evt006_payload_line1 (evt006_resetsFirst (N := Nat) (T := Nat)) ∧
      ¬ EVT_006_payload (evt006_resetsFirst (N := Nat) (T := Nat)) := by
  refine ⟨evt006_startWith_line1 _, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt012_cfg) (o := evt012_beforeStart)
    (l := .start "u" false)
    (p := fun s _ => match s.order with
      | t :: _ => evt006_resetsFirstList (vis s) t != removedListDecl (vis s) t
      | [] => false)
    (by decide +kernel)
  obtain ⟨t, rest, ho, -, hall⟩ := (h evt012_cfg [] "u" false _).2 s s' ⟨hs, rfl⟩
  have hm : NetEvent.transitionStarted "u" (evt006_resetsFirstList (vis s) t) ∈
      evt012_atStart (evt006_startWith (fun s t => evt006_resetsFirstList (vis s) t)
        (fun s t => evt006_resetsFirstList (vis s) t)) evt012_cfg [] s (.start "u" false) s' := by
    simp [evt012_atStart, evt006_startWith, ho]
  have heq := hall _ _ hm
  simp only [ho, bne_iff_ne, ne_eq] at hp
  exact hp heq

/-- ✓ The list takes each reset place at its first arc: `r` (EVT-012's repeated-reset example)
takes 30 from place 2 and has reset arcs on places 0, 1 and 0 again, and its `TransitionStarted`
lists (2, 30), (0, 10), (1, 20), place 0's drained token before place 1's, as the runtimes walk
the reset arcs. -/
@[evidence nonvacuous EVT_006_payload]
theorem EVT_006_payload_nonvacuous_repeatedReset :
    ∃ s s' evs, (refEvExec polJT).step evt012_dupCfg [] s (.start "r" false) evs s' ∧
      .transitionStarted "r" [(2, 30), (0, 10), (1, 20)] ∈ evs ∧
      (∃ t rest, s.order = t :: rest ∧ t.core.name = "r" ∧
        removedListDecl (vis s) t = [(2, 30), (0, 10), (1, 20)]) := by
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt012_dupCfg)
    (o := evt012_dupBeforeStart) (l := .start "r" false)
    (p := fun s s' =>
      (refEmitW polJT evt012_dupCfg [] s (.start "r" false) s').contains
          (.transitionStarted "r" [(2, 30), (0, 10), (1, 20)]) &&
        match s.order with
        | t :: _ => removedListDecl (vis s) t == [(2, 30), (0, 10), (1, 20)]
        | [] => false)
    (by decide +kernel)
  simp only [Bool.and_eq_true, List.contains_iff_mem] at hp
  obtain ⟨h1, h2⟩ := hp
  obtain ⟨t, rest, ho, hn, -⟩ := xstep_start_qRemoved hs
  refine ⟨s, s', _, ⟨hs, rfl⟩, h1, t, rest, ho, hn, ?_⟩
  rw [ho] at h2
  simpa only [beq_iff_eq] using h2

/-- ✗ Taking a place named by several reset arcs at its last arc meets line 1 of the companion
(the list is the reported tokens) and violates line 2: `r`'s reset arcs name places 0, 1 and 0
again, and the start reports and lists (2, 30), (1, 20), (0, 10), place 1 before place 0. -/
@[evidence mutant EVT_006_payload]
theorem EVT_006_payload_mutant_lastOccurrence :
    evt006_payload_line1 (evt006_lastOcc (N := Nat) (T := Nat)) ∧
      ¬ EVT_006_payload (evt006_lastOcc (N := Nat) (T := Nat)) := by
  refine ⟨evt006_startWith_line1 _, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt012_dupCfg)
    (o := evt012_dupBeforeStart) (l := .start "r" false)
    (p := fun s _ => match s.order with
      | t :: _ => evt006_lastOccList (vis s) t != removedListDecl (vis s) t
      | [] => false)
    (by decide +kernel)
  obtain ⟨t, rest, ho, -, hall⟩ := (h evt012_dupCfg [] "r" false _).2 s s' ⟨hs, rfl⟩
  have hm : NetEvent.transitionStarted "r" (evt006_lastOccList (vis s) t) ∈
      evt012_atStart (evt006_startWith (fun s t => evt006_lastOccList (vis s) t)
        (fun s t => evt006_lastOccList (vis s) t)) evt012_dupCfg [] s (.start "r" false) s' := by
    simp [evt012_atStart, evt006_startWith, ho]
  have heq := hall _ _ hm
  simp only [ho, bne_iff_ne, ne_eq] at hp
  exact hp heq

/-- ✗ Reporting a start under another transition's name meets line 1 of the companion (the list
is the tokens of the `TokenRemoved` events) and violates line 2: the start of `u` is reported as
`TransitionStarted a` listing (0, 10), (0, 11), (1, 20), the tokens of `u`, not of `a`. -/
@[evidence mutant EVT_006_payload]
theorem EVT_006_payload_mutant_misnamed :
    evt006_payload_line1 (evt006_misnamed (N := Nat) (T := Nat)) ∧
      ¬ EVT_006_payload (evt006_misnamed (N := Nat) (T := Nat)) := by
  refine ⟨evt006_misnamed_payload_line1, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt012_cfg) (o := evt012_beforeStart)
    (l := .start "u" false)
    (p := fun s _ => match s.order with
      | t :: _ => t.core.name != "a"
      | [] => false)
    (by decide +kernel)
  have hm : evt006_misnamed.step evt012_cfg [] s (.start "a" false)
      (refEmitW polJT evt012_cfg [] s (.start "a" false) s') s' :=
    ⟨rfl, Or.inr ⟨"a", "u", false, rfl, hs⟩⟩
  obtain ⟨t, rest, ho, hn, -⟩ := (h evt012_cfg [] "a" false _).2 s s' hm
  rw [ho] at hp
  simp only [bne_iff_ne, ne_eq] at hp
  exact hp hn

/-- **EVT-006 together with EVT-012 rejects a start that reports no removal.** An executor whose
start emits `TransitionStarted` and no `TokenRemoved` event meets EVT-006 alone, since line 1
only asks that whatever comes before the `TransitionStarted` be removals. EVT-012 rejects it: for
`u` in the example, place 0 goes from 10, 11, 12 to 12 and no event names place 0. -/
@[evidence cites "EVT-006" "the TokenRemoved events of a start are EVT-012's: EVT_006 alone accepts a start that reports TransitionStarted with no TokenRemoved event, and EVT_012 (line 1, one event per removed token) rejects it"]
theorem EVT_006_with_EVT_012_noRemovals :
    EVT_006 (evt006_noRemovals (N := Nat) (T := Nat)) ∧
      ¬ EVT_012 (evt006_noRemovals (N := Nat) (T := Nat)) := by
  refine ⟨evt006_startWith_meets _ _, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt012_cfg) (o := evt012_beforeStart)
    (l := .start "u" false)
    (p := fun s s' => removedCount (evt006_startWith (fun _ _ => [])
        (fun s t => removedListDecl (vis s) t) evt012_cfg s "u") 0 + (s'.M 0).length !=
      (s.M 0).length)
    (by decide +kernel)
  simp only [bne_iff_ne, ne_eq] at hp
  exact hp ((h evt012_cfg).1 [] "u" false _ s s' ⟨hs, rfl⟩ 0)

end Libpetri.Spec
