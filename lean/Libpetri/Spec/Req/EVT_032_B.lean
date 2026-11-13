import Libpetri.Spec.Registry
import Libpetri.Reference.EventsLink
import Libpetri.Spec.Req.EVT_032

set_option linter.missingDocs true

/-!
# EVT-032, the run companion: the replay of a run's events (`spec/08-events-observability.md`)

The replay cache of [EVT-032] answers the state that the replay of recorded events gives. Its
first block, `EVT_032` (wave W6, kind F), compares the cache with that replay and says nothing
about the run the events came from. This second block (wave W11, design link E4 on RefEvents)
compares the replay with the run: on the whole event stream of a Java or TypeScript run, read
before the first step or after any step of the executor, the replay counts on every declared place
the tokens the executor holds there, and lists every transition that holds a clock as enabled (ruling D83 (a): the replayed enabled
set over-approximates, so the line is a subset, not an equality).

The block is a predicate over an abstract executor with events `E : EvExec N T`
(`Reference/Events.lean`). A labelled run from the initial state, with the boot events as its
history, gives the events `E.boot C M0 ++ EvStep.events run`, which the replay of [EVT-032]
reads through `NetEvent.replayView`; `runEnd` is the state the run ends in. Line 1 is the
count, line 2 the enabled set.

**The witness.** `refEvExec polJT`, the reference executor with the Java and TypeScript emission;
the proof is link E4 (`refReplay_agrees_jt` in `Reference/EventsLink.lean`). The Rust and Python
emission fails line 1 at the boot, since it reports no initial marking
(`EVT_032_B_forbids_rust`).

**The wrong executors.** All three step as the reference and emit otherwise: one without the
start snapshot and one whose completion reports no `TokenAdded` (line 1), and one that reports a
transition as enabled only the first time in a run (line 2). Each keeps the other line, by
`evt032b_line1_of` and `evt032b_line2_of`: line 1 reads only the token events and line 2 only the
others.

The worked example (`evt032b_cfg`): token 1 in place 0 and one transition `r` that takes it. In
one cycle `r` starts, its action puts 9 back, its completion is settled, and the next update arms
`r` again. The replay counts one token in place 0 and lists `r` as enabled.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

requirement EVT_032_B
  id "EVT-032"
  title "Marking Replay Cache (the replay of a run's events)"
  kind B
  scope "Java and TypeScript executors (event store enabled), read over the whole event stream of a run; Rust and Python report no initial marking"
  source verbatim "spec/08-events-observability.md"
  quote "*Where* the executor is a Java or TypeScript executor, which reports the initial marking in a `MarkingSnapshot` right after `ExecutionStarted` ([EVT-014]), the replay of all events a run has emitted before its first step, or up to the end of any of its steps, *shall* count, for every place the net declares, the tokens that place holds at that point, and *shall* list among the enabled transitions every transition that holds a clock at that point, also one whose clock restart is pending ([EVT-005])."
  reading "For every executor with events E and every configuration C, every initial marking M0, every reading r0 and every labelled run of E from the initial state of M0 at r0, with the boot events as its history, the run with no step included:"
          "the replay of the boot events followed by the events of the run counts, on every place the net declares, the tokens that place holds in the state the run ends in;"
          "and lists as enabled every transition whose status in that state holds a clock."
  assumes "The model is an executor with events E : EvExec N T (Reference/Events.lean): the events a run emits before its first step (the boot), and a step relation E.step C H s l evs s' saying that the step labelled l leads from s to s' and appends the events evs, given the events H emitted before it. A labelled run from the initial state xinit M0 r0, with the boot events as its history (LRun), emits the boot events followed by the events of each step; runEnd is the state it ends in. The replay is the replay of the first block of EVT-032 (replay over applyEv) read through the replay view of an executor event, NetEvent.replayView (recView after NetEvent.toRec, Reference/EventsLink.lean), so this block uses the replay rules the first block states and adds none. The witness is refEvExec polJT, the reference executor with the Java and TypeScript emission; the proof is design link E4 (refReplay_agrees_jt)."
          "Scope: the quoted sentence is scoped by runtime, to the Java and TypeScript executors, and not by the emission, so a Java or TypeScript executor that emitted no start snapshot would violate it rather than fall out of it. Java and TypeScript report the initial marking in the MarkingSnapshot right after ExecutionStarted (EVT-014 line 1); Rust and Python have no MarkingSnapshot producer and report no TokenAdded for the initial marking (ruling D76 (a)), so the replay of their stream misses every initial token (clash evt-c#11), and the sentence leaves them out. The reference with the Rust and Python emission violates line 1 at the boot of a run with a token in its initial marking (EVT_032_B_forbids_rust, replayAgrees_needs_snapshot), as the body's sentence on which streams report the initial marking says. A Java or TypeScript executor that dropped its start snapshot breaks line 1 the same way and keeps line 2 (EVT_032_B_mutant_noStartSnap)."
          "Both lines are read before the first step too: the run may have no step, and then the replay reads the boot events alone, which is the sentence's 'before its first step'. Both refutations of line 1 above use that run, with token 1 in place 0 and no TokenAdded or MarkingSnapshot to count it."
          "Line 1 is the count half of the quoted sentence: on every declared place the replayed count is the length of the place's queue after the step. It holds because the start snapshot gives the initial counts (EVT-014), every token a start takes has its TokenRemoved event (EVT-012), every token a deposit appends has its TokenAdded event (EVT-011), and the end snapshot restates the counts; replayAgrees_step checks each step of the reference. A completion that reports its TransitionCompleted and none of its TokenAdded events breaks line 1 and keeps line 2 (EVT_032_B_mutant_silentCommit). Line 1 is read on the places the net declares, as the markdown's third sentence on the run says: a TypeScript snapshot lists the places of the compiled net only (typescript/src/runtime/bitmap-net-executor.ts snapshotMarking), while Java lists every marked place, so on a place the net does not declare the end snapshot of the reference erases a count its TokenAdded events built (evt032b_undeclared: an action puts 9 into the undeclared place 5, and after the end snapshot the replay counts no token there while the executor holds one)."
          "Line 2 is the enabled half of the quoted sentence: every transition whose status holds a clock (isArmedS) is in the replayed enabled set. That includes a transition whose clock restart is pending (pendingS, TIME-012): another transition's start took its tokens in the intermediate marking, and it keeps its old stamp until the next enablement update, so in that window the marking may not enable it. The sentence says 'holds a clock, also one whose clock restart is pending' (the term of EVT-005) for that reason: the glossary entry Armed says that a transition that is not enabled is not armed, which leaves this window out, while EVT-005 calls such a transition armed; aligning the glossary entry is an open item. The set is an over-approximation (ruling D83 (a), clash evt-c#10): a transition that lost its clock because another firing took its tokens, and a reaped transition, stay listed until their next TransitionStarted (cov_replay_end in Reference/EventsLink.lean; clashEvt_replayEnabled), so the line is an inclusion and the converse is not stated. It holds because a transition gets a clock only from an update that reports it with TransitionEnabled, and only its own start removes it from the replayed set. The runtimes arm the same way: Java's updateDirtyTransitions emits TransitionEnabled whenever it sets a transition enabled and stamps a clock (java/src/main/java/org/libpetri/runtime/BitmapNetExecutor.java 1314-1320), restarts the clock of a transition still marked enabled with TransitionClockRestarted (1324-1330), which the replay leaves as it is, and clears the enabled mark when the transition starts (1755-1758); TypeScript does the same (typescript/src/runtime/bitmap-net-executor.ts 748-774). An executor that reports a transition as enabled only the first time in a run breaks line 2 and keeps line 1 (EVT_032_B_mutant_enabledOnce)."
          "The grain is a step of the executor: a step appends its events at once, and the lines are read at the end of a step. At an index inside the events of one step, for example between the TokenRemoved events of a firing that starts, the replayed counts can match no marking the executor held, as the markdown sentence after the quoted one says. Java appends ActionTimedOut events and the log messages it captures from other threads than the orchestrator (the reading at the top of spec/08-events-observability.md), so in a Java store such an event can fall between the events of one step; neither changes a replayed count or the replayed enabled set (the replay reads ActionTimedOut as an end event and a log message as other), so both lines hold on the store as recorded."
          "The line reads the whole event stream of a run, from its boot. A stream that lost its first events, such as a debug store that evicted its oldest events past its capacity (EVT-024) or a subscription opened after the run started, does not carry the start snapshot, and the line says nothing about it. The replay cache answers this replay through the first block: evt032b_cache shows that a cache meeting EVT_032, coherent with the stream, answers at the end of the stream the counts of line 1. That a debug protocol handler keeps its cache coherent (invalidate() after an eviction) is the known gap the first block records."
          "Not stated: the in-flight set of the replay is not compared with the firings in flight. The Java and TypeScript ActionTimedOut event comes from the action's timer (EVT-010, polJT), and the replay reads it as an end event, while the executor keeps the firing in flight until it settles the timeout outcome; and the set holds names, so it cannot count two firings of one transition (a re-entrant configuration, Rust and Python under ruling D8 (b)). Both lines hold for both values of Cfg.reentrant, so the block carries no hypothesis on it (design events.md, skeptic correction on D8). A line on the in-flight set would need a reentrant = false hypothesis and a reading of ActionTimedOut as the end of the action, not of the firing; it is left as an open item."
          "Acceptance criteria: AC1 (compute_at at 0 and at the length of the stream), AC2 and AC3 (clamping and repeated calls) are the first block's; the comparison of the replay with the run is this block. AC4 (counts, no payloads) is why line 1 compares counts and not tokens. AC5 is this block: line 1 and line 2 before the first step and after each step, for Java and TypeScript, and its Rust and Python clause is EVT_032_B_forbids_rust."
          "Assumptions shared by the executor event blocks: the event store is enabled and its append does not fail (EVT-020); an event is a value (EVT-001); transition names are distinct (ruling D10). The model has no ν firing, whose consumption the payload companion of EVT-012 scopes out; its TokenRemoved events are counted the same way."
          "The test derivation of the run companion, the second sentence of the markdown's test derivation, is EVT_032_B_nonvacuous: on the example run (token 1 in place 0, r takes it, its action puts 9 back, the completion is settled, the next update arms r again) the replay counts one token in place 0, where the executor holds 9, and lists r, which is armed, as enabled."
  signoff "2026-11-13 b032e418252cc0e5 ai"
  statement : ∀ {N T : Type} [DecidableEq N], EvExec N T → Prop :=
    fun E => ∀ C M0 r0 run, LRun E C (E.boot C M0) (xinit M0 r0) run →
      (∀ p ∈ C.X.net.places,
        (replay NetEvent.replayView (E.boot C M0 ++ EvStep.events run)).cnt p =
          ((runEnd (xinit M0 r0) run).M p).length) ∧
      (∀ n, isArmedS ((runEnd (xinit M0 r0) run).st n) = true →
        (replay NetEvent.replayView (E.boot C M0 ++ EvStep.events run)).en n = true)

/- The pinned readable form of the run companion: a change to the formula shows up as a diff
here. -/
/--
info: def Libpetri.Spec.EVT_032_B : {N T : Type} → [DecidableEq N] → EvExec N T → Prop :=
fun {N T} [DecidableEq N] E =>
  ∀ (C : Cfg N T) (M0 : QMarking N T) (r0 : ℕ) (run : List (EvStep N T)),
    LRun E C (E.boot C M0) (xinit M0 r0) run →
      (∀ p ∈ C.X.net.places,
          (replay NetEvent.replayView (E.boot C M0 ++ EvStep.events run)).cnt p =
            ((runEnd (xinit M0 r0) run).M p).length) ∧
        ∀ (n : String),
          isArmedS ((runEnd (xinit M0 r0) run).st n) = true →
            (replay NetEvent.replayView (E.boot C M0 ++ EvStep.events run)).en n = true
-/
#guard_msgs in #print EVT_032_B

/-! ## The two lines, one at a time -/

section Lines

variable {N T : Type} [DecidableEq N]

/-- Line 1 of `EVT_032_B` alone: the replayed counts are the tokens of every declared place. -/
def evt032b_line1 (E : EvExec N T) : Prop :=
  ∀ C M0 r0 run, LRun E C (E.boot C M0) (xinit M0 r0) run →
    ∀ p ∈ C.X.net.places,
      (replay NetEvent.replayView (E.boot C M0 ++ EvStep.events run)).cnt p =
        ((runEnd (xinit M0 r0) run).M p).length

/-- Line 2 of `EVT_032_B` alone: every armed transition is in the replayed enabled set. -/
def evt032b_line2 (E : EvExec N T) : Prop :=
  ∀ C M0 r0 run, LRun E C (E.boot C M0) (xinit M0 r0) run →
    ∀ n, isArmedS ((runEnd (xinit M0 r0) run).st n) = true →
      (replay NetEvent.replayView (E.boot C M0 ++ EvStep.events run)).en n = true

/-- `EVT_032_B` is its two lines. -/
theorem evt032b_iff (E : EvExec N T) : EVT_032_B E ↔ evt032b_line1 E ∧ evt032b_line2 E :=
  ⟨fun h => ⟨fun C M0 r0 run hr => (h C M0 r0 run hr).1, fun C M0 r0 run hr => (h C M0 r0 run hr).2⟩,
   fun ⟨h1, h2⟩ C M0 r0 run hr => ⟨h1 C M0 r0 run hr, h2 C M0 r0 run hr⟩⟩

end Lines

/-! ## The reference -/

/-- ✓ The Java and TypeScript reference meets EVT-032's run companion. For example, a run starts
with token 1 in place 0, and transition `r` takes it and puts back 9: the replay of
`MarkingSnapshot [(0, [1])]`, `TokenRemoved 0 1` and `TokenAdded 0 9` counts one token in place
0, as the executor holds `[9]` there, and the `TransitionEnabled` of `r`'s next arming lists `r`
as enabled again. -/
@[evidence holds EVT_032_B]
theorem EVT_032_B_reference {N T : Type} [DecidableEq N] [Ord N] :
    EVT_032_B (refEvExec (N := N) (T := T) polJT) :=
  fun _ _ _ _ h => refReplay_agrees_jt h

/-- ✗ The Rust and Python emission is out of scope: its boot reports no initial marking. A run
starts with token 1 in place 0 and has taken no step yet; the replay of its one event,
`ExecutionStarted`, counts no token in place 0. -/
@[evidence forbids EVT_032_B]
theorem EVT_032_B_forbids_rust : ¬ EVT_032_B (refEvExec (N := Nat) (T := Nat) polRust) := by
  intro h
  have := (h covCfg covM0 0 [] trivial).1 0 (by decide)
  revert this
  decide

/-! ## Moving a line between executors that differ only in some events -/

section Transfer

variable {N T : Type} [DecidableEq N]

/-- A token event of the replay: a snapshot, an addition or a removal. -/
def REv.isTok : REv N → Bool
  | .snapshot _ => true
  | .added _ => true
  | .removed _ => true
  | _ => false

/-- The replayed counts read only the token events: replaying a list from a state gives the
counts that replaying its token events alone gives from a state with the same counts. -/
theorem evt032b_cnt_filter {E : Type} (v : E → REv N) :
    ∀ (es : List E) (r1 r2 : RState N), r1.cnt = r2.cnt →
      (replayWith applyEv v r1 es).cnt =
        (replayWith applyEv v r2 (es.filter fun e => (v e).isTok)).cnt
  | [], _, _, h => h
  | e :: es, r1, r2, h => by
    have hc : ∀ (r : RState N) (l : List E),
        replayWith applyEv v r (e :: l) = replayWith applyEv v (applyEv r (v e)) l := fun _ _ => rfl
    by_cases ht : (v e).isTok = true
    · rw [List.filter_cons_of_pos (p := fun e => (v e).isTok) ht, hc, hc]
      apply evt032b_cnt_filter v es
      generalize v e = x at ht
      cases x <;> simp_all [applyEv, REv.isTok]
    · rw [List.filter_cons_of_neg (p := fun e => (v e).isTok) ht, hc]
      apply evt032b_cnt_filter v es
      generalize v e = x at ht
      cases x <;> simp_all [applyEv, REv.isTok]

/-- The replayed enabled and in-flight sets read only the other events: replaying a list from a
state gives the sets that replaying its other events alone gives from a state with the same
sets. -/
theorem evt032b_en_filter {E : Type} (v : E → REv N) :
    ∀ (es : List E) (r1 r2 : RState N), r1.en = r2.en → r1.fl = r2.fl →
      (replayWith applyEv v r1 es).en =
          (replayWith applyEv v r2 (es.filter fun e => !(v e).isTok)).en ∧
        (replayWith applyEv v r1 es).fl =
          (replayWith applyEv v r2 (es.filter fun e => !(v e).isTok)).fl
  | [], _, _, he, hf => ⟨he, hf⟩
  | e :: es, r1, r2, he, hf => by
    have hc : ∀ (r : RState N) (l : List E),
        replayWith applyEv v r (e :: l) = replayWith applyEv v (applyEv r (v e)) l := fun _ _ => rfl
    by_cases ht : (v e).isTok = true
    · rw [List.filter_cons_of_neg (p := fun e => !(v e).isTok) (by simp [ht]), hc]
      apply evt032b_en_filter v es
      · generalize v e = x at ht
        cases x <;> simp_all [applyEv, REv.isTok]
      · generalize v e = x at ht
        cases x <;> simp_all [applyEv, REv.isTok]
    · rw [List.filter_cons_of_pos (p := fun e => !(v e).isTok) (by simpa using ht), hc, hc]
      apply evt032b_en_filter v es
      · generalize v e = x at ht
        cases x <;> simp_all [applyEv, REv.isTok]
      · generalize v e = x at ht
        cases x <;> simp_all [applyEv, REv.isTok]

/-- Filtering twice keeps what the second filter keeps, when the first keeps everything the
second does. -/
theorem evt032b_filter_filter {α : Type} (q g : α → Bool) (h : ∀ x, g x = true → q x = true)
    (L : List α) : (L.filter q).filter g = L.filter g := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro x _
  cases hg : g x
  · rfl
  · simp [h x hg]

variable [Ord N]

/-- A run with the events of each step replaced by what the Java and TypeScript reference emits
on that step. -/
def evt032b_relabel (C : Cfg N T) (run : List (EvStep N T)) : List (EvStep N T) :=
  run.map fun st => ⟨st.src, st.lbl, refEmitW polJT C [] st.src st.lbl st.dst, st.dst⟩

/-- A run of an executor that steps as the reference, relabelled, is a run of the Java and
TypeScript reference, from any history. -/
theorem evt032b_relabel_lrun
    {b : Cfg N T → QMarking N T → List (NetEvent N T)}
    {e : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    (C : Cfg N T) :
    ∀ {H : List (NetEvent N T)} {s : XSt N T} {run : List (EvStep N T)},
      LRun (emitExec b e) C H s run → ∀ H', LRun (refEvExec polJT) C H' s (evt032b_relabel C run)
  | _, _, [], _, _ => trivial
  | _, _, _ :: _, ⟨hsrc, ⟨hx, _⟩, hrest⟩, _ =>
    ⟨hsrc, ⟨hx, rfl⟩, evt032b_relabel_lrun C hrest _⟩

/-- Relabelling keeps the state a run ends in. -/
theorem evt032b_runEnd_relabel (C : Cfg N T) :
    ∀ (s : XSt N T) (run : List (EvStep N T)), runEnd s (evt032b_relabel C run) = runEnd s run
  | _, [] => rfl
  | _, st :: rest => evt032b_runEnd_relabel C st.dst rest

/-- When an emission keeps, at every step, the events a filter keeps from the reference's, the
events of its runs keep them from the relabelled run's. -/
theorem evt032b_events_filter
    {b : Cfg N T → QMarking N T → List (NetEvent N T)}
    {e : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    (f : NetEvent N T → Bool)
    (he : ∀ C H s l s', (e C H s l s').filter f = (refEmitW polJT C H s l s').filter f)
    (C : Cfg N T) :
    ∀ {H : List (NetEvent N T)} {s : XSt N T} {run : List (EvStep N T)},
      LRun (emitExec b e) C H s run →
        (EvStep.events run).filter f = (EvStep.events (evt032b_relabel C run)).filter f
  | _, _, [], _ => rfl
  | H, _, st :: rest, ⟨_, ⟨_, hev⟩, hrest⟩ => by
    have ih := evt032b_events_filter f he C hrest
    show (st.evs ++ EvStep.events rest).filter f =
      (refEmitW polJT C [] st.src st.lbl st.dst ++ EvStep.events (evt032b_relabel C rest)).filter f
    rw [List.filter_append, List.filter_append, ih, hev, he]
    rfl

/-- **Line 1 moves along the token events.** An executor that steps as the reference and whose
boot and steps emit the reference's token events (snapshots, additions, removals), whatever else
they emit, meets line 1. -/
theorem evt032b_line1_of
    {b : Cfg N T → QMarking N T → List (NetEvent N T)}
    {e : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    (hb : ∀ C M0, (b C M0).filter (fun x => x.replayView.isTok) =
      (refBoot polJT C M0).filter (fun x => x.replayView.isTok))
    (he : ∀ C H s l s', (e C H s l s').filter (fun x => x.replayView.isTok) =
      (refEmitW polJT C H s l s').filter (fun x => x.replayView.isTok)) :
    evt032b_line1 (emitExec b e) := by
  intro C M0 r0 run hr p hp
  have href := refReplay_agrees_jt (evt032b_relabel_lrun C hr (refBoot polJT C M0))
  rw [evt032b_runEnd_relabel] at href
  rw [← href.1 p hp]
  show (replayWith applyEv NetEvent.replayView RState.empty (b C M0 ++ EvStep.events run)).cnt p =
    (replayWith applyEv NetEvent.replayView RState.empty
      (refBoot polJT C M0 ++ EvStep.events (evt032b_relabel C run))).cnt p
  rw [evt032b_cnt_filter _ _ _ RState.empty rfl,
    evt032b_cnt_filter _ (refBoot polJT C M0 ++ _) RState.empty RState.empty rfl,
    List.filter_append, List.filter_append, hb, evt032b_events_filter _ he C hr]

/-- **Line 2 moves along the other events.** An executor that steps as the reference and whose
boot and steps emit the reference's events other than token events, whatever token events they
emit, meets line 2. -/
theorem evt032b_line2_of
    {b : Cfg N T → QMarking N T → List (NetEvent N T)}
    {e : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    (hb : ∀ C M0, (b C M0).filter (fun x => !x.replayView.isTok) =
      (refBoot polJT C M0).filter (fun x => !x.replayView.isTok))
    (he : ∀ C H s l s', (e C H s l s').filter (fun x => !x.replayView.isTok) =
      (refEmitW polJT C H s l s').filter (fun x => !x.replayView.isTok)) :
    evt032b_line2 (emitExec b e) := by
  intro C M0 r0 run hr n hn
  have href := refReplay_agrees_jt (evt032b_relabel_lrun C hr (refBoot polJT C M0))
  rw [evt032b_runEnd_relabel] at href
  have h2 := href.2 n hn
  show (replayWith applyEv NetEvent.replayView RState.empty (b C M0 ++ EvStep.events run)).en n =
    true
  change (replayWith applyEv NetEvent.replayView RState.empty
      (refBoot polJT C M0 ++ EvStep.events (evt032b_relabel C run))).en n = true at h2
  rw [(evt032b_en_filter _ _ _ RState.empty rfl rfl).1] at h2 ⊢
  rw [List.filter_append, hb, evt032b_events_filter _ he C hr, ← List.filter_append]
  exact h2

end Transfer

/-! ## Decided runs of an executor that steps as the reference -/

section Runs

variable {N T : Type} [DecidableEq N]

/-- The labelled run of `emitExec boot emit` from history `H` and state `s` along the labels
`ls`, if every label is a step (`refRun` for any emission). -/
def evt032b_runOf (emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T →
    List (NetEvent N T)) (C : Cfg N T) :
    List (NetEvent N T) → XSt N T → List (XLbl N T) → Option (List (EvStep N T))
  | _, _, [] => some []
  | H, s, l :: ls => (xstep C s l).bind fun s' =>
      (evt032b_runOf emit C (H ++ emit C H s l s') s' ls).map (⟨s, l, emit C H s l s', s'⟩ :: ·)

/-- A run `evt032b_runOf` builds is a labelled run of `emitExec boot emit`. -/
theorem evt032b_runOf_lrun {boot : Cfg N T → QMarking N T → List (NetEvent N T)}
    {emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    (C : Cfg N T) :
    ∀ {H : List (NetEvent N T)} {s : XSt N T} {ls : List (XLbl N T)} {run : List (EvStep N T)},
      evt032b_runOf emit C H s ls = some run → LRun (emitExec boot emit) C H s run
  | H, s, [], run, h => by cases h; trivial
  | H, s, l :: ls, run, h => by
    simp only [evt032b_runOf] at h
    cases hs : xstep C s l with
    | none => simp [hs] at h
    | some s' =>
      simp only [hs, Option.bind_some] at h
      cases hr : evt032b_runOf emit C (H ++ emit C H s l s') s' ls with
      | none => simp [hr] at h
      | some run' =>
        simp only [hr, Option.map_some, Option.some.injEq] at h
        subst h
        exact ⟨rfl, ⟨hs, rfl⟩, evt032b_runOf_lrun C hr⟩

/-- A computed option whose checked value is `true` holds a value. -/
theorem evt032b_some_of_map {α : Type} {o : Option α} {q : α → Bool} (h : o.map q = some true) :
    ∃ a, o = some a ∧ q a = true := by
  cases o with
  | none => cases h
  | some a => exact ⟨a, rfl, Option.some.inj h⟩

end Runs

/-! ## The worked example -/

/-- The example net: place 0 and one Immediate transition `r` that takes the token of place 0. -/
def evt032b_cfg : Cfg Nat Nat :=
  { X := { net := { places := [0], transitions := [covTr "r" [0] none] },
           timing := fun _ => .immediate, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => false,
    res := 0 }

/-- The initial marking of the example: token 1 in place 0. -/
def evt032b_m0 : QMarking Nat Nat := fun p => if p = 0 then [1] else []

/-- One cycle in which `r` starts synchronously, its action puts 9 back into place 0 and its
completion is settled inside the pass, up to that settling. -/
def evt032b_toCommit : List (XLbl Nat Nat) :=
  covCyc ++ [.deadline [], .begin, .start "r" true, .write 0 0 9, .ret 0 true, .commit 0]

/-- The labels of the example: the first cycle to `r`'s completion, the end of its pass, and the
next cycle's update, which arms `r` again on the token 9. -/
def evt032b_labels : List (XLbl Nat Nat) := evt032b_toCommit ++ [.endPass] ++ covCyc

/-- The replayed state of a run of the example under a boot `b`, its count of place 0, whether it
lists `r` as enabled, and the executor's count and status of `r` at the end. -/
def evt032b_view (b : List (NetEvent Nat Nat)) (run : List (EvStep Nat Nat)) :
    Nat × Bool × Nat × Bool :=
  ((replay NetEvent.replayView (b ++ EvStep.events run)).cnt 0,
   (replay NetEvent.replayView (b ++ EvStep.events run)).en "r",
   ((runEnd (xinit evt032b_m0 0) run).M 0).length,
   isArmedS ((runEnd (xinit evt032b_m0 0) run).st "r"))

/-- ✓ The test derivation on the reference (Java and TypeScript): on the example run the replay
of the events, `ExecutionStarted`, the snapshot of token 1 in place 0, `TransitionEnabled r`,
`TokenRemoved 0 1`, `TransitionStarted r`, `TokenAdded 0 9`, `TransitionCompleted r` and the next
`TransitionEnabled r`, counts one token in place 0, where the executor holds `[9]`, and lists `r`,
which the executor has armed again, as enabled. -/
@[evidence nonvacuous EVT_032_B]
theorem EVT_032_B_nonvacuous :
    ∃ run, LRun (refEvExec polJT) evt032b_cfg (refBoot polJT evt032b_cfg evt032b_m0)
        (xinit evt032b_m0 0) run ∧
      evt032b_view (refBoot polJT evt032b_cfg evt032b_m0) run = (1, true, 1, true) := by
  obtain ⟨run, hr, hq⟩ := evt032b_some_of_map
    (o := refRun polJT evt032b_cfg (refBoot polJT evt032b_cfg evt032b_m0) (xinit evt032b_m0 0)
      evt032b_labels)
    (q := fun run => evt032b_view (refBoot polJT evt032b_cfg evt032b_m0) run == (1, true, 1, true))
    (by decide +kernel)
  exact ⟨run, refRun_lrun polJT _ hr, by simpa using hq⟩

/-- The example cycle with `r`'s action putting 9 into place 5, which the net does not declare,
then the next cycle, which finds nothing to do and finishes quiescent. -/
def evt032b_undeclLabels : List (XLbl Nat Nat) :=
  covCyc ++ [.deadline [], .begin, .start "r" true, .write 0 5 9, .ret 0 true, .commit 0,
    .endPass] ++ covCyc ++ [.deadline [], .finish .quiescent]

/-- **Line 1 needs "declared".** On the reference, `r`'s action puts 9 into place 5, which the
net does not declare: its `TokenAdded` gives the replay one token there, and the end snapshot,
which lists the declared places only (as TypeScript's does), sets the count back to zero, while
the executor still holds 9 in place 5. -/
theorem evt032b_undeclared :
    ∃ run, LRun (refEvExec polJT) evt032b_cfg (refBoot polJT evt032b_cfg evt032b_m0)
        (xinit evt032b_m0 0) run ∧
      (replay NetEvent.replayView (refBoot polJT evt032b_cfg evt032b_m0 ++ EvStep.events run)).cnt
          5 = 0 ∧
      ((runEnd (xinit evt032b_m0 0) run).M 5).length = 1 := by
  obtain ⟨run, hr, hq⟩ := evt032b_some_of_map
    (o := refRun polJT evt032b_cfg (refBoot polJT evt032b_cfg evt032b_m0) (xinit evt032b_m0 0)
      evt032b_undeclLabels)
    (q := fun run =>
      (replay NetEvent.replayView (refBoot polJT evt032b_cfg evt032b_m0 ++ EvStep.events run)).cnt
          5 == 0 &&
        ((runEnd (xinit evt032b_m0 0) run).M 5).length == 1)
    (by decide +kernel)
  simp only [Bool.and_eq_true, beq_iff_eq] at hq
  exact ⟨run, refRun_lrun polJT _ hr, hq.1, hq.2⟩

/-! ## Wrong executors, one per line -/

section Mutants

variable {N T : Type} [DecidableEq N] [Ord N]

omit [Ord N] in
/-- **The replay cache answers the run's counts.** A replay cache that meets the first block of
EVT-032, read from a cache coherent with a run's whole event stream at an index at or past its
end, answers on every declared place the tokens the executor holds at the end of the run, for an
executor that meets this block. For example, after the example run a seek to the end of its
eight events counts one token in place 0, where the executor holds 9. -/
theorem evt032b_cache {E : EvExec N T} {call : CacheCall N (NetEvent N T)}
    (hcall : EVT_032 NetEvent.replayView call) (hE : EVT_032_B E) {C : Cfg N T}
    {M0 : QMarking N T} {r0 : Nat} {run : List (EvStep N T)}
    (hr : LRun E C (E.boot C M0) (xinit M0 r0) run) {c : Cache N}
    (hc : c.Coherent NetEvent.replayView (E.boot C M0 ++ EvStep.events run)) {i : Nat}
    (hi : (E.boot C M0 ++ EvStep.events run).length ≤ i) :
    ∀ p ∈ C.X.net.places,
      (call c (E.boot C M0 ++ EvStep.events run) i).2.cnt p =
        ((runEnd (xinit M0 r0) run).M p).length := by
  intro p hp
  rw [(hcall c _ i hc).1, List.take_of_length_le hi]
  exact (hE C M0 r0 run hr).1 p hp

/-- The Java and TypeScript emission, without the start snapshot: its boot is `ExecutionStarted`
alone. -/
def evt032b_noStartSnap : EvExec N T := emitExec (refBoot polRust) (refEmitW polJT)

/-- The Java and TypeScript emission, with the settling of a completion reporting its
`TransitionCompleted` and none of its `TokenAdded` events. -/
def evt032b_silentCommitEmit (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T)
    (l : XLbl N T) (s' : XSt N T) : List (NetEvent N T) :=
  match l with
  | .commit i => (refEmitW polJT C H s (.commit i) s').filter fun x => x.kind != .tokenAdded
  | _ => refEmitW polJT C H s l s'

/-- The executor whose completion reports no addition. -/
def evt032b_silentCommit : EvExec N T := emitExec (refBoot polJT) evt032b_silentCommitEmit

/-- An event is a `TransitionEnabled` that an earlier `TransitionEnabled` of the same
transition in `H` already reported. -/
def evt032b_reported (H : List (NetEvent N T)) (x : NetEvent N T) : Bool :=
  x.kind == .transitionEnabled &&
    H.any fun h => h.kind == .transitionEnabled && h.trans? == x.trans?

/-- The Java and TypeScript emission, with an update reporting `TransitionEnabled` for a
transition only the first time in a run. -/
def evt032b_enabledOnceEmit (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T)
    (l : XLbl N T) (s' : XSt N T) : List (NetEvent N T) :=
  match l with
  | .update => (refEmitW polJT C H s .update s').filter fun x => !evt032b_reported H x
  | _ => refEmitW polJT C H s l s'

/-- The executor that reports each transition as enabled once per run. -/
def evt032b_enabledOnce : EvExec N T := emitExec (refBoot polJT) evt032b_enabledOnceEmit

omit [Ord N] in
/-- Every event that is not a token event of the replay is not a `TokenAdded`. -/
theorem evt032b_notTok_notAdded (x : NetEvent N T) :
    (!x.replayView.isTok) = true → (x.kind != .tokenAdded) = true := by
  cases x <;> simp [NetEvent.replayView, NetEvent.toRec, recView, REv.isTok, NetEvent.kind]

omit [Ord N] in
/-- Every token event of the replay is kept by the filter of `evt032b_enabledOnceEmit`. -/
theorem evt032b_tok_notReported (H : List (NetEvent N T)) (x : NetEvent N T) :
    x.replayView.isTok = true → (!evt032b_reported H x) = true := by
  cases x <;> simp [NetEvent.replayView, NetEvent.toRec, recView, REv.isTok, NetEvent.kind,
    evt032b_reported]

/-- The executor without the start snapshot meets line 2: the snapshot is a token event. -/
theorem evt032b_noStartSnap_line2 : evt032b_line2 (evt032b_noStartSnap (N := N) (T := T)) :=
  evt032b_line2_of
    (fun C M0 => by
      simp [refBoot, polRust, polJT, NetEvent.replayView, NetEvent.toRec, recView, REv.isTok])
    (fun _ _ _ _ _ => rfl)

/-- The executor whose completion reports no addition meets line 2: it drops token events only. -/
theorem evt032b_silentCommit_line2 : evt032b_line2 (evt032b_silentCommit (N := N) (T := T)) :=
  evt032b_line2_of (fun _ _ => rfl) (fun C H s l s' => by
    cases l with
    | commit i =>
      exact evt032b_filter_filter _ _ evt032b_notTok_notAdded _
    | _ => rfl)

/-- The executor that reports each transition as enabled once per run meets line 1: it drops
`TransitionEnabled` events only. -/
theorem evt032b_enabledOnce_line1 : evt032b_line1 (evt032b_enabledOnce (N := N) (T := T)) :=
  evt032b_line1_of (fun _ _ => rfl) (fun C H s l s' => by
    cases l with
    | update =>
      exact evt032b_filter_filter _ _ (evt032b_tok_notReported H) _
    | _ => rfl)

end Mutants

/-- ✗ A Java or TypeScript executor that drops the start snapshot violates EVT-032's run
companion (line 1) and keeps line 2: a run starts with token 1 in place 0 and has taken no step,
and the replay of `ExecutionStarted` alone counts no token there. -/
@[evidence mutant EVT_032_B]
theorem EVT_032_B_mutant_noStartSnap :
    evt032b_line2 (evt032b_noStartSnap (N := Nat) (T := Nat)) ∧
      ¬ EVT_032_B (evt032b_noStartSnap (N := Nat) (T := Nat)) := by
  refine ⟨evt032b_noStartSnap_line2, fun h => ?_⟩
  have := (h evt032b_cfg evt032b_m0 0 [] trivial).1 0 (by decide)
  revert this
  decide

/-- ✗ An executor whose completion reports no `TokenAdded` violates EVT-032's run companion
(line 1) and keeps line 2: `r` takes token 1 from place 0 and its completion puts 9 back without
reporting it, so the replay counts no token in place 0 where the executor holds `[9]`. -/
@[evidence mutant EVT_032_B]
theorem EVT_032_B_mutant_silentCommit :
    evt032b_line2 (evt032b_silentCommit (N := Nat) (T := Nat)) ∧
      ¬ EVT_032_B (evt032b_silentCommit (N := Nat) (T := Nat)) := by
  refine ⟨evt032b_silentCommit_line2, fun h => ?_⟩
  obtain ⟨run, hr, hq⟩ := evt032b_some_of_map
    (o := evt032b_runOf evt032b_silentCommitEmit evt032b_cfg
      (refBoot polJT evt032b_cfg evt032b_m0) (xinit evt032b_m0 0) evt032b_toCommit)
    (q := fun run => (evt032b_view (refBoot polJT evt032b_cfg evt032b_m0) run).1 == 0 &&
      (evt032b_view (refBoot polJT evt032b_cfg evt032b_m0) run).2.2.1 == 1)
    (by decide +kernel)
  have h1 := (h evt032b_cfg evt032b_m0 0 run
    (evt032b_runOf_lrun (boot := refBoot polJT) evt032b_cfg hr)).1 0 (by decide)
  simp only [evt032b_view, Bool.and_eq_true, beq_iff_eq] at hq
  change (replay NetEvent.replayView (refBoot polJT evt032b_cfg evt032b_m0 ++ EvStep.events run)).cnt 0 =
    ((runEnd (xinit evt032b_m0 0) run).M 0).length at h1
  omega

/-- ✗ An executor that reports each transition as enabled only the first time in a run violates
EVT-032's run companion (line 2) and keeps line 1: `r` is enabled, starts and completes, and the
next update arms it again without a `TransitionEnabled`, so the replay, which took `r` out of
the enabled set when it started, does not list it although it is armed. -/
@[evidence mutant EVT_032_B]
theorem EVT_032_B_mutant_enabledOnce :
    evt032b_line1 (evt032b_enabledOnce (N := Nat) (T := Nat)) ∧
      ¬ EVT_032_B (evt032b_enabledOnce (N := Nat) (T := Nat)) := by
  refine ⟨evt032b_enabledOnce_line1, fun h => ?_⟩
  obtain ⟨run, hr, hq⟩ := evt032b_some_of_map
    (o := evt032b_runOf evt032b_enabledOnceEmit evt032b_cfg
      (refBoot polJT evt032b_cfg evt032b_m0) (xinit evt032b_m0 0) evt032b_labels)
    (q := fun run => !(evt032b_view (refBoot polJT evt032b_cfg evt032b_m0) run).2.1 &&
      (evt032b_view (refBoot polJT evt032b_cfg evt032b_m0) run).2.2.2)
    (by decide +kernel)
  have h2 := (h evt032b_cfg evt032b_m0 0 run
    (evt032b_runOf_lrun (boot := refBoot polJT) evt032b_cfg hr)).2 "r"
  simp only [evt032b_view, Bool.and_eq_true, Bool.not_eq_true'] at hq
  have := h2 hq.2
  change (replay NetEvent.replayView (refBoot polJT evt032b_cfg evt032b_m0 ++ EvStep.events run)).en "r" = true at this
  rw [hq.1] at this
  cases this

end Libpetri.Spec
