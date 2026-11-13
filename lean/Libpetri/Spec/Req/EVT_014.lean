import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Events
import Libpetri.Spec.Req.CORE_073

set_option linter.missingDocs true

/-!
# EVT-014: MarkingSnapshot Event (`spec/08-events-observability.md`)

Java and TypeScript report the marking twice per run: once when the run starts, right after
`ExecutionStarted`, and once when it ends, before `ExecutionCompleted`. Each report is a
`MarkingSnapshot` event carrying the snapshot form of [CORE-073]: the marked places, ascending
by code point of the name, each with its whole queue. Rust and Python declare the event but no
executor of theirs emits it, so the requirement is one block scoped to Java and TypeScript, and
it has no block for every executor (ruling D38 (a), design note SC-6).

The block is a predicate over an abstract executor with events `E : EvExec String T`
(`Reference/Events.lean`), with place names as strings so that the order is the code-point order
of [CORE-073]. Line 1 is the start report, line 2 the end report, and both carry a marking in the
sense of `SnapCarries`: canonical (names strictly ascending, no empty queue), every declared
place with its queue, and every listed place with its own queue. Lines 3 and 4 hold every
snapshot event, at the boot and at any step, to the canonical form: a further snapshot is
allowed, but not one that lists a place twice, out of order or with no token.

**The witness.** The witness is the shared reference executor with events of Java and
TypeScript, `refEvExec polJT`, over string place names. Its snapshots list the declared places
that hold a token ascending by name (`snapOf`), and on strings that is the [CORE-073] snapshot
(`refSnapshot`) of the declared places (`evt014_snapOf_eq`). An executor that lists the places in
the order the net declares them violates EVT-014 (`EVT_014_forbids_declOrder`).

The worked example (`evt014_cfg`): the net declares the places `b`, `c` and `a`, in that order,
and one transition `t` that takes the token of `b`. The run starts with 1 on `b` and 2 on `a`,
`t` fires once, and the run ends quiescent. The start report lists `a` with 2, then `b` with 1,
and leaves out the empty `c`; the end report lists `a` with 2 only.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## What a snapshot event carries -/

/-- **The marking `M` is what the snapshot `m` carries**, for the net of `C`: `m` is canonical
([CORE-073]: names strictly ascending, which on strings is code-point order, and no place with
an empty queue), every place the net declares restores from `m` to its queue in `M`, and every
place `m` lists comes with its queue in `M`. A place the net does not declare may be listed
(Java) or left out (TypeScript), but never with tokens it does not hold. -/
def SnapCarries {T : Type} (C : Cfg String T) (M : QMarking String T) (m : QSnap String T) :
    Prop :=
  QCanon m ∧ (∀ p ∈ C.X.net.places, refRestore m p = M p) ∧ (∀ e ∈ m, e.2 = M e.1)

instance {T : Type} [DecidableEq T] (C : Cfg String T) (M : QMarking String T)
    (m : QSnap String T) : Decidable (SnapCarries C M m) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-! ## EVT-014, Java and TypeScript: a snapshot at the start and at the end of a run -/

requirement EVT_014
  id "EVT-014"
  title "MarkingSnapshot Event"
  kind B
  scope "Java and TypeScript executors (event store enabled); Rust and Python have no producer"
  source verbatim "spec/08-events-observability.md"
  quote "*Where* an executor emits MarkingSnapshot events (Java and TypeScript), *when* a run starts, the executor *shall* emit, before the run's first cycle, an ExecutionStarted event and, after it, a MarkingSnapshot event that carries the initial marking."
        "*Where* an executor emits MarkingSnapshot events (Java and TypeScript), *when* a run finishes ([EXEC-041]), whatever its termination reason, the executor *shall* emit a MarkingSnapshot event that carries the marking the run ends with and, after it, an ExecutionCompleted event."
        "*Where* an executor emits MarkingSnapshot events (Java and TypeScript), the marking a MarkingSnapshot event carries *shall* list every place the net declares that holds a token, *shall* list each place it lists with all of that place's tokens in FIFO order, and *shall not* list a place that holds no token."
        "*Where* an executor emits MarkingSnapshot events (Java and TypeScript), the marking a MarkingSnapshot event carries *shall* list each place at most once and *shall* list its places in ascending code-point order of the place name, also for a place name above U+FFFF ([CORE-073])."
  reading "For every executor with events E over string place names and every configuration C:"
          "for every initial marking M0, the events a run emits before its first step contain a MarkingSnapshot event with an ExecutionStarted event before it, and the snapshot m it carries is canonical (names strictly ascending, no empty queue), restores every declared place to its queue in M0, and lists every place with its queue in M0;"
          "for every history H, a finish step from state s to state s' that appends the events evs contains a MarkingSnapshot event with an ExecutionCompleted event after it, and the snapshot m it carries is canonical, restores every declared place to its queue in s', and lists every place with its queue in s';"
          "for every initial marking M0, every MarkingSnapshot event the run emits before its first step carries a canonical snapshot;"
          "for every history H and every label l, every MarkingSnapshot event a step labelled l appends carries a canonical snapshot."
  assumes "The model is an executor with events E : EvExec String T (Reference/Events.lean): the events a run emits before its first step (the boot), and a step relation E.step C H s l evs s' saying that the step labelled l leads from s to s' and appends the events evs. Place names are strings, so the order of QCanon is Lean's order on strings, which is code-point order (CORE-073). The witness is the shared reference executor with events of Java and TypeScript, refEvExec polJT, over string place names: its two snapshots list the declared places that hold a token ascending by name (snapOf, with String's order), and that is the CORE-073 snapshot of the declared places, evt014_declSnap, which is refSnapshot imported from Reference/Snapshot.lean and not a second form (evt014_snapOf_eq). The same executor meets every other executor event block (the consistency theorem joint_events_exec_sketch). An executor that lists the places in the order the net declares them breaks the block (EVT_014_forbids_declOrder): TypeScript listed them that way before it adopted the CORE-073 order (typescript/src/runtime/bitmap-net-executor.ts snapshotMarking)."
          "Scope (ruling D38 (a), design note SC-6): every line is about Java and TypeScript, so the requirement has no block for every executor. Java emits the start snapshot after ExecutionStarted and before its loop (java/src/main/java/org/libpetri/runtime/BitmapNetExecutor.java 1004-1013; PrecompiledNetExecutor.java 1842) and the end snapshot before ExecutionCompleted (BitmapNetExecutor.java 1080-1094; PrecompiledNetExecutor.java 1907); TypeScript likewise (typescript/src/runtime/bitmap-net-executor.ts 536-540 and 576-580; precompiled-net-executor.ts 596-600 and 628-632). Rust and Python declare the event but no executor emits it; the reference with the Rust and Python emission violates line 1 (EVT_014_forbids_rust)."
          "Line 1 is the first quoted sentence and the start half of AC1: the boot holds ExecutionStarted and, after it, a snapshot that carries the initial marking. An executor that reports the snapshot before ExecutionStarted breaks it and keeps lines 2 to 4 (EVT_014_mutant_snapFirst). Line 2 is the second quoted sentence and the end half of AC1: the finish step, whatever the cause, holds a snapshot that carries the marking the run ends with and, after it, ExecutionCompleted, both in the events of that one step. An executor that reports ExecutionCompleted first breaks it and keeps lines 1, 3 and 4 (EVT_014_mutant_completedFirst). Line 2 does not say 'immediately before', and the line allows any event between the two."
          "Which run ends line 2 reaches: a finish of the model, whose cause is quiescent, terminal, closed or stopped (Cause, EXEC-041). Java's INTERRUPTED end (a host cancellation observed in the orchestrator's wait, EXEC-041) is not a cause of the model, which has no host cancellation; Java emits the end snapshot, a WARN and then ExecutionCompleted on that path too, from the finally of its loop (BitmapNetExecutor.java 1062-1094), so the quoted sentence holds there as well. An expired run budget ends the caller's wait and not the loop (EXEC-041, last quoted sentence): TypeScript's run(timeoutMs) with the abandon policy rejects the caller's promise and reports stopped while the loop runs on, and when that loop finishes it emits the end snapshot and ExecutionCompleted (bitmap-net-executor.ts 494-519 and 570-580). A run that ends with an exception thrown out of the loop is not a finish (EXEC-041: a run ends only by finishing) and is outside this block: Java still emits both events from its finally, and TypeScript's executeLoop, which has no finally, emits neither (an open item for EXEC-041)."
          "SnapCarries is the third and fourth quoted sentences for the start and the end snapshot. Its first part, QCanon, is AC3 (only non-empty places; EVT_014_forbids_keepEmpty, a snapshot that keeps the empty place c), 'each place at most once' (EVT_014_forbids_duplicate, a snapshot that lists every place twice, in otherwise ascending order) and AC4 (ascending code-point order, also above U+FFFF; EVT_014_forbids_declOrder on the places b and a, EVT_014_forbids_utf16 on the names U+E000 and U+10000, which a UTF-16 order puts the other way round). Its second part is 'every declared place with all its tokens in FIFO order' (EVT_014_forbids_empty, a snapshot that lists nothing; EVT_014_forbids_lifo, a snapshot that lists the queue 2 then 3 of a as 3 then 2). Its third part is that a listed place carries its own queue (EVT_014_forbids_forged, a snapshot that lists the undeclared place z with a token z does not hold). For a snapshot that lists declared places only, as TypeScript's does, SnapCarries says that it is exactly the CORE-073 snapshot of the declared places (evt014_carries_iff)."
          "Lines 3 and 4 are the third and fourth quoted sentences for every other snapshot event: each such sentence speaks of every MarkingSnapshot event, so a snapshot the boot or any step emits besides the two of lines 1 and 2 must be canonical too (no place twice, ascending code-point order, no place without a token). An executor that also emits a snapshot that keeps the empty place c at the boot breaks line 3 and keeps lines 1, 2 and 4 (EVT_014_mutant_bootKeepEmpty); one that also emits a snapshot in declaration order at the start of each cycle breaks line 4 and keeps lines 1 to 3 (EVT_014_mutant_cycleDeclOrder); one that emits, after ExecutionCompleted, a second end snapshot that keeps the empty places breaks line 4 although its first end snapshot meets line 2 (EVT_014_forbids_finishKeepEmpty). Which marking such a further snapshot is of is not stated: no quoted sentence says when it is taken, no runtime emits one, and so the parts of SnapCarries that compare with a marking are not required of it."
          "Declared places (ruling D38 (a), clash evt-b#10): the marking a snapshot event carries is read over the places the net declares. TypeScript lists the places of the compiled net only (bitmap-net-executor.ts 1536-1552), and Java lists every marked place, an undeclared one included (java/src/main/java/org/libpetri/runtime/Marking.java 273-283), since an undeclared place keeps its tokens (CORE-072). Both meet the lines: a snapshot that also lists an undeclared place with its tokens meets them (EVT_014_allows_undeclared)."
          "Not stated: AC1 says 'at least', so a further snapshot elsewhere is not forbidden, only held to the canonical form (lines 3 and 4). AC2 (a deep defensive copy) holds by type: an event is a value (EVT-001), and a queue in the model is a list. AC5 and the paragraph on renderings (an archive or the debug protocol renders the same stream identically twice; the order is not promised past the event) are about renderings, which are EVT-025's and the debug protocol's, not the event's. The paragraph 'Emitting this event MUST NOT fail the run' is not a line here: in the model a snapshot is a value computed from the marking, place names are never ambiguous (a Lean place is its name), and that the event layer neither adds nor blocks a step is the consistency theorem's conjunct W.erase = E (EventsLink E1); the refusal over two same-named places is the host operation's (CORE-073). The timestamp is not modelled (the epoch clock is the CORE-011 slice)."
          "Assumptions shared by the executor event blocks: the event store is enabled and its append does not fail (EVT-020; Java's end snapshot sits in a try that swallows a store failure); an event is a value (EVT-001); transition names are distinct (ruling D10). The events of one step are contiguous in the model, since a step appends its events at once. Java appends ActionTimedOut events and the log messages it captures from actions from other threads than the orchestrator (the timeout callback BitmapNetExecutor.fireTransition hands java/src/main/java/org/libpetri/runtime/ExecutorSupport.java withActionTimeout, which appends through emitEvent from the timer thread; LogCaptureScope.java wrapRunnable and wrapCallable), so in a Java store such an event can fall between the events of one step; the lines are read on the store with those events left out, as the reading at the top of spec/08-events-observability.md says. TypeScript and Rust append every event from the orchestrator."
          "The test derivation (run a net, check the snapshot at the start and at the end and its accuracy) is EVT_014_nonvacuous: on the example net the start snapshot is a 2, b 1 (the declared but empty c left out, and a before b although the net declares b first), and the end snapshot after t fired is a 2. For AC4 the test derivation's names U+E000 and U+10000 are EVT_014_forbids_utf16."
  signoff "2026-11-13 ef545b035d52a039 ai"
  statement : ∀ {T : Type}, EvExec String T → Prop :=
    fun {T} E => ∀ C,
      (∀ M0, ∃ (pre : List (NetEvent String T)) (m : QSnap String T)
          (post : List (NetEvent String T)), E.boot C M0 = pre ++ NetEvent.markingSnapshot m :: post ∧
          NetEvent.executionStarted ∈ pre ∧ SnapCarries C M0 m) ∧
      (∀ H c evs, on (fun s s' => E.step C H s (.finish c) evs s'), shall (fun _ s' =>
          ∃ (pre : List (NetEvent String T)) (m : QSnap String T)
            (post : List (NetEvent String T)), evs = pre ++ NetEvent.markingSnapshot m :: post ∧
            NetEvent.executionCompleted ∈ post ∧ SnapCarries C s'.M m)) ∧
      (∀ M0 (m : QSnap String T), NetEvent.markingSnapshot m ∈ E.boot C M0 → QCanon m) ∧
      (∀ H l evs, on (fun s s' => E.step C H s l evs s'), shall (fun _ _ =>
          ∀ m : QSnap String T, NetEvent.markingSnapshot m ∈ evs → QCanon m))

/- The pinned readable form of EVT-014: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EVT_014 : {T : Type} → EvExec String T → Prop :=
fun {T} E =>
  ∀ (C : Cfg String T),
    (∀ (M0 : QMarking String T),
        ∃ pre m post,
          E.boot C M0 = pre ++ NetEvent.markingSnapshot m :: post ∧
            NetEvent.executionStarted ∈ pre ∧ SnapCarries C M0 m) ∧
      (∀ (H : List (NetEvent String T)) (c : Cause) (evs : List (NetEvent String T)),
          on fun s s' => E.step C H s (XLbl.finish c) evs s', shall fun x s' =>
            ∃ pre m post,
              evs = pre ++ NetEvent.markingSnapshot m :: post ∧
                NetEvent.executionCompleted ∈ post ∧ SnapCarries C s'.M m) ∧
        (∀ (M0 : QMarking String T) (m : QSnap String T), NetEvent.markingSnapshot m ∈ E.boot C M0 → QCanon m) ∧
          ∀ (H : List (NetEvent String T)) (l : XLbl String T) (evs : List (NetEvent String T)),
            on fun s s' => E.step C H s l evs s', shall fun x x_1 =>
              ∀ (m : QSnap String T), NetEvent.markingSnapshot m ∈ evs → QCanon m
-/
#guard_msgs in #print EVT_014

/-! ## The two lines, one at a time -/

section Lines

variable {T : Type}

/-- Line 1 of `EVT_014` alone: the boot holds a snapshot of the initial marking after
`ExecutionStarted`. -/
def evt014_line1 (E : EvExec String T) : Prop :=
  ∀ C M0, ∃ pre m post, E.boot C M0 = pre ++ .markingSnapshot m :: post ∧
    .executionStarted ∈ pre ∧ SnapCarries C M0 m

/-- Line 2 of `EVT_014` alone: a finish step holds a snapshot of the final marking before
`ExecutionCompleted`. -/
def evt014_line2 (E : EvExec String T) : Prop :=
  ∀ C H c evs, on (fun s s' => E.step C H s (.finish c) evs s'), shall (fun _ s' =>
    ∃ pre m post, evs = pre ++ .markingSnapshot m :: post ∧
      .executionCompleted ∈ post ∧ SnapCarries C s'.M m)

/-- Line 3 of `EVT_014` alone: every snapshot the boot emits is canonical. -/
def evt014_line3 (E : EvExec String T) : Prop :=
  ∀ C M0 (m : QSnap String T), .markingSnapshot m ∈ E.boot C M0 → QCanon m

/-- Line 4 of `EVT_014` alone: every snapshot a step emits is canonical. -/
def evt014_line4 (E : EvExec String T) : Prop :=
  ∀ C H l evs, on (fun s s' => E.step C H s l evs s'), shall (fun _ _ =>
    ∀ m : QSnap String T, .markingSnapshot m ∈ evs → QCanon m)

/-- `EVT_014` is its four lines. -/
theorem evt014_iff (E : EvExec String T) :
    EVT_014 E ↔ evt014_line1 E ∧ evt014_line2 E ∧ evt014_line3 E ∧ evt014_line4 E :=
  ⟨fun h => ⟨fun C => (h C).1, fun C => (h C).2.1, fun C => (h C).2.2.1, fun C => (h C).2.2.2⟩,
   fun h C => ⟨h.1 C, h.2.1 C, h.2.2.1 C, h.2.2.2 C⟩⟩

/-- Lines 2 to 4 of `EVT_014`: all but line 1. -/
def evt014_but1 (E : EvExec String T) : Prop :=
  evt014_line2 E ∧ evt014_line3 E ∧ evt014_line4 E

/-- Lines 1, 3 and 4 of `EVT_014`: all but line 2. -/
def evt014_but2 (E : EvExec String T) : Prop :=
  evt014_line1 E ∧ evt014_line3 E ∧ evt014_line4 E

/-- Lines 1, 2 and 4 of `EVT_014`: all but line 3. -/
def evt014_but3 (E : EvExec String T) : Prop :=
  evt014_line1 E ∧ evt014_line2 E ∧ evt014_line4 E

/-- Lines 1 to 3 of `EVT_014`: all but line 4. -/
def evt014_but4 (E : EvExec String T) : Prop :=
  evt014_line1 E ∧ evt014_line2 E ∧ evt014_line3 E

end Lines

/-! ## The snapshot of the declared places, and what carries a marking -/

section Snap

variable {T : Type}

/-- The marking `M` restricted to the places of `L`, with `L` as its support. -/
def evt014_restrictFin (L : List String) (M : QMarking String T) : FinQ String T where
  M := fun p => if p ∈ L then M p else []
  supp := L
  hsupp := fun k h => by
    by_contra hk
    exact h (if_neg hk)

/-- The [CORE-073] snapshot of the places of `L`: `refSnapshot`, imported, on the restriction. -/
def evt014_snapOn (L : List String) (M : QMarking String T) : QSnap String T :=
  refSnapshot (evt014_restrictFin L M)

/-- The [CORE-073] snapshot of the places the net declares. -/
def evt014_declSnap (C : Cfg String T) (M : QMarking String T) : QSnap String T :=
  evt014_snapOn C.X.net.places M

/-- The snapshot of any list of places that covers the declared ones carries the marking: the
declared places exactly, and the others of the list truthfully. -/
theorem evt014_snapOn_carries {C : Cfg String T} {L : List String}
    (hL : ∀ p ∈ C.X.net.places, p ∈ L) (M : QMarking String T) :
    SnapCarries C M (evt014_snapOn L M) := by
  refine ⟨snapshot_canon _, fun p hp => ?_, fun e he => ?_⟩
  · rw [evt014_snapOn, restore_snapshot]
    exact if_pos (hL p hp)
  · obtain ⟨k, q⟩ := e
    obtain ⟨hne, rfl⟩ := (mem_snapshot _).mp he
    show (if k ∈ L then M k else []) = M k
    by_cases hk : k ∈ L
    · exact if_pos hk
    · exact absurd (if_neg hk) hne

/-- The snapshot of the declared places carries the marking. -/
theorem evt014_declSnap_carries (C : Cfg String T) (M : QMarking String T) :
    SnapCarries C M (evt014_declSnap C M) :=
  evt014_snapOn_carries (fun _ h => h) M

/-- **A snapshot of declared places carries the marking exactly when it is the [CORE-073]
snapshot of the declared places**: for a payload that lists declared places only (TypeScript's),
`SnapCarries` pins it down to one list. -/
theorem evt014_carries_iff {C : Cfg String T} {M : QMarking String T} {m : QSnap String T}
    (hk : ∀ e ∈ m, e.1 ∈ C.X.net.places) : SnapCarries C M m ↔ m = evt014_declSnap C M := by
  constructor
  · rintro ⟨hc, hd, -⟩
    refine canon_ext hc (snapshot_canon _) fun p => ?_
    rw [evt014_declSnap, evt014_snapOn, restore_snapshot]
    show refRestore m p = if p ∈ C.X.net.places then M p else []
    by_cases hp : p ∈ C.X.net.places
    · rw [if_pos hp, hd p hp]
    · rw [if_neg hp]
      exact restore_eq_nil_of_not_mem fun hm => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
        exact hp (hk e he)
  · rintro rfl
    exact evt014_declSnap_carries C M

end Snap

/-! ## The witness: the reference, with the snapshot of CORE-073 -/

section Witness

variable {T : Type}


/-- The boot of an executor that reports the snapshot `f C M0` right after `ExecutionStarted`. -/
def evt014Boot (f : Cfg String T → QMarking String T → QSnap String T) (C : Cfg String T)
    (M0 : QMarking String T) : List (NetEvent String T) :=
  [.executionStarted, .markingSnapshot (f C M0)]

/-- The emission of the Java and TypeScript reference, with the snapshot `f C M` of the marking
reported at a finish step, before `ExecutionCompleted`. -/
def evt014Emit (f : Cfg String T → QMarking String T → QSnap String T) (C : Cfg String T)
    (H : List (NetEvent String T)) (s : XSt String T) (l : XLbl String T) (s' : XSt String T) :
    List (NetEvent String T) :=
  match l with
  | .finish _ => [.markingSnapshot (f C s.M), .executionCompleted]
  | _ => refEmitW polJT C H s l s'

/-- The executor with events that steps as the reference, emits as the Java and TypeScript
reference, and reports the snapshot `f C M` of the marking at the start and at the end of a
run. -/
def evt014With (f : Cfg String T → QMarking String T → QSnap String T) : EvExec String T :=
  emitExec (evt014Boot f) (evt014Emit f)

/-- With the reference's own payload (`snapOf`), `evt014With` is the Java and TypeScript
reference itself. -/
theorem evt014With_snapOf : evt014With (T := T) snapOf = refEvExec polJT := by
  unfold evt014With refEvExec emitExec
  congr
  funext C H s l evs s'
  cases l <;> rfl

/-- Away from a finish step, `evt014With f` emits exactly what the Java and TypeScript reference
emits, whatever `f`. -/
theorem evt014Emit_other (f : Cfg String T → QMarking String T → QSnap String T)
    (C : Cfg String T) (H : List (NetEvent String T)) (s : XSt String T) {l : XLbl String T}
    (hl : ∀ c, l ≠ .finish c) (s' : XSt String T) :
    evt014Emit f C H s l s' = refEmitW polJT C H s l s' := by
  cases l with
  | finish c => exact absurd rfl (hl c)
  | _ => rfl

/-- Event by event, `evt014With f` emits the kinds the Java and TypeScript reference emits, at
the boot and at every step: only the payload of a snapshot depends on `f`. -/
theorem evt014With_kinds (f g : Cfg String T → QMarking String T → QSnap String T)
    (C : Cfg String T) (M0 : QMarking String T) (H : List (NetEvent String T)) (s : XSt String T)
    (l : XLbl String T) (s' : XSt String T) :
    (evt014Boot f C M0).map NetEvent.kind = (evt014Boot g C M0).map NetEvent.kind ∧
      (evt014Emit f C H s l s').map NetEvent.kind = (evt014Emit g C H s l s').map NetEvent.kind := by
  refine ⟨rfl, ?_⟩
  cases l <;> rfl

/-- On string names the snapshot order is the order of strings: `snapArrange` sorts as the
[CORE-073] snapshot form does. -/
theorem evt014_snapArrange_string (L : List String) : snapArrange L = L.insertionSort (· ≤ ·) := by
  unfold snapArrange
  have h : (fun a b : String => compare a b ≠ .gt) = (· ≤ ·) := by
    funext a b; apply propext; rw [Ne, compare_gt_iff_gt, not_lt]
  simp only [h]

/-- **The reference's payload is the [CORE-073] snapshot**: on string place names the
reference lists the declared places that hold a token ascending by name, which is the snapshot
form of [CORE-073] of the declared places. -/
theorem evt014_snapOf_eq (C : Cfg String T) (M : QMarking String T) :
    snapOf C M = evt014_declSnap C M := by
  have hm : ∀ k ∈ (C.X.net.places.insertionSort (· ≤ ·)).dedup, k ∈ C.X.net.places := fun k hk =>
    (List.perm_insertionSort _ _).mem_iff.1 (List.mem_dedup.1 hk)
  simp only [snapOf, evt014_snapArrange_string, evt014_declSnap, evt014_snapOn, refSnapshot,
    snapKeys, evt014_restrictFin]
  have hf : (C.X.net.places.insertionSort (· ≤ ·)).dedup.filter (fun p => !(M p).isEmpty) =
      (C.X.net.places.insertionSort (· ≤ ·)).dedup.filter
        (fun k => !(if k ∈ C.X.net.places then M k else []).isEmpty) :=
    List.filter_congr fun k hk => by rw [if_pos (hm k hk)]
  rw [hf]
  refine List.map_congr_left fun k hk => ?_
  rw [if_pos (hm k (List.mem_filter.1 hk).1)]

/-- The reference's payload carries the marking. -/
theorem evt014_snapOf_carries (C : Cfg String T) (M : QMarking String T) :
    SnapCarries C M (snapOf C M) :=
  evt014_snapOf_eq C M ▸ evt014_declSnap_carries C M

/-- The declared places that hold a token, in the order the net declares them: the payload of an
executor that does not sort its snapshot (TypeScript before it adopted the order of
[CORE-073]). -/
def evt014_declOrder (C : Cfg String T) (M : QMarking String T) : QSnap String T :=
  (C.X.net.places.dedup.filter fun p => !(M p).isEmpty).map fun p => (p, M p)

/-- A finish step keeps the marking. -/
theorem xstep_finish_M {C : Cfg String T} {s s' : XSt String T} {c : Cause}
    (h : xstep C s (.finish c) = some s') : s'.M = s.M := by
  cases c with
  | quiescent => obtain ⟨-, -, -, rfl⟩ := xstepW_finishQuiescent h; rfl
  | terminal => obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h; rfl
  | closed => obtain ⟨-, -, -, -, rfl⟩ := xstepW_finishClosed h; rfl
  | stopped => obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h; rfl

/-- The finish steps of an executor that emits `evt014Emit f` meet line 2 when every snapshot `f`
reports carries its marking, whatever its boot. -/
theorem evt014_line2_of {f : Cfg String T → QMarking String T → QSnap String T}
    (hf : ∀ C M, SnapCarries C M (f C M))
    (boot : Cfg String T → QMarking String T → List (NetEvent String T)) :
    evt014_line2 (emitExec boot (evt014Emit f)) := by
  intro C H c evs s s' hs
  obtain ⟨hx, rfl⟩ := hs
  refine ⟨[], f C s.M, [.executionCompleted], rfl, List.mem_singleton_self _, ?_⟩
  rw [xstep_finish_M hx]
  exact hf C s.M

/-- The boot `evt014Boot f` meets line 1 when every snapshot `f` reports carries its marking,
whatever the steps. -/
theorem evt014_line1_of {f : Cfg String T → QMarking String T → QSnap String T}
    (hf : ∀ C M, SnapCarries C M (f C M))
    (emit : Cfg String T → List (NetEvent String T) → XSt String T → XLbl String T →
      XSt String T → List (NetEvent String T)) :
    evt014_line1 (emitExec (evt014Boot f) emit) :=
  fun C M0 => ⟨[.executionStarted], f C M0, [], rfl, List.mem_singleton_self _, hf C M0⟩

/-- Away from a finish step, the Java and TypeScript reference emits no snapshot. -/
theorem evt014_refEmit_noSnap {C : Cfg String T} {H : List (NetEvent String T)}
    {s : XSt String T} {l : XLbl String T} {s' : XSt String T} (hl : ∀ c, l ≠ .finish c)
    (m : QSnap String T) : NetEvent.markingSnapshot m ∉ refEmitW polJT C H s l s' := by
  intro hm
  have := refEmitW_kind polJT C H s l s' _ hm
  cases l with
  | finish c => exact hl c rfl
  | _ => simp [lblKinds, NetEvent.kind] at this

/-- The boot `evt014Boot f` meets line 3 when every snapshot `f` reports is canonical, whatever
the steps. -/
theorem evt014_line3_of {f : Cfg String T → QMarking String T → QSnap String T}
    (hf : ∀ C M, QCanon (f C M))
    (emit : Cfg String T → List (NetEvent String T) → XSt String T → XLbl String T →
      XSt String T → List (NetEvent String T)) :
    evt014_line3 (emitExec (evt014Boot f) emit) := by
  intro C M0 m hm
  simp only [emitExec, evt014Boot, List.mem_cons, List.not_mem_nil,
    or_false, reduceCtorEq, false_or, NetEvent.markingSnapshot.injEq] at hm
  subst hm
  exact hf C M0

/-- The steps of an executor that emits `evt014Emit f` meet line 4 when every snapshot `f`
reports is canonical, whatever its boot. -/
theorem evt014_line4_of {f : Cfg String T → QMarking String T → QSnap String T}
    (hf : ∀ C M, QCanon (f C M))
    (boot : Cfg String T → QMarking String T → List (NetEvent String T)) :
    evt014_line4 (emitExec boot (evt014Emit f)) := by
  intro C H l evs s s' hs m hm
  obtain ⟨-, rfl⟩ := hs
  by_cases hl : ∃ c, l = .finish c
  · obtain ⟨c, rfl⟩ := hl
    simp only [evt014Emit, List.mem_cons, List.not_mem_nil, or_false,
      reduceCtorEq, NetEvent.markingSnapshot.injEq] at hm
    subst hm
    exact hf C s.M
  · have hl' : ∀ c, l ≠ .finish c := fun c h => hl ⟨c, h⟩
    have he : evt014Emit f C H s l s' = refEmitW polJT C H s l s' := by
      cases l <;> first | rfl | exact absurd rfl (hl' _)
    rw [he] at hm
    exact absurd hm (evt014_refEmit_noSnap hl' m)

/-- `evt014With f` meets EVT-014 when every snapshot `f` reports carries its marking. -/
theorem evt014With_holds {f : Cfg String T → QMarking String T → QSnap String T}
    (hf : ∀ C M, SnapCarries C M (f C M)) : EVT_014 (evt014With f) :=
  (evt014_iff _).2 ⟨evt014_line1_of hf _, evt014_line2_of hf _,
    evt014_line3_of (fun C M => (hf C M).1) _, evt014_line4_of (fun C M => (hf C M).1) _⟩

/-- A two-event list split around one event. -/
theorem evt014_split2 {x y z : NetEvent String T} {pre post : List (NetEvent String T)}
    (h : [x, y] = pre ++ z :: post) :
    (pre = [] ∧ z = x ∧ post = [y]) ∨ (pre = [x] ∧ z = y ∧ post = []) := by
  rcases pre with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp only [List.nil_append, List.cons.injEq] at h
    exact Or.inl ⟨rfl, h.1.symm, h.2.symm⟩
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
    exact Or.inr ⟨by rw [h.1], h.2.1.symm, h.2.2.symm⟩
  · simp at h

/-- When `evt014With f` meets line 1, the snapshot `f` reports at the start carries the initial
marking. -/
theorem evt014With_boot_carries {f : Cfg String T → QMarking String T → QSnap String T}
    (h : evt014_line1 (evt014With f)) (C : Cfg String T) (M0 : QMarking String T) :
    SnapCarries C M0 (f C M0) := by
  obtain ⟨pre, m, post, he, hs, hc⟩ := h C M0
  rcases evt014_split2 he with ⟨rfl, -, -⟩ | ⟨-, hz, -⟩
  · cases hs
  · cases hz
    exact hc

end Witness

/-! ## The reference meets EVT-014 -/

/-- ✓ The reference executor with the Java and TypeScript emission meets EVT-014: it reports the
initial marking right after `ExecutionStarted` and the final marking right before
`ExecutionCompleted`, each time with the declared places that hold a token, ascending by name,
which is the [CORE-073] snapshot of the declared places. -/
@[evidence holds EVT_014]
theorem EVT_014_reference {T : Type} : EVT_014 (refEvExec (N := String) (T := T) polJT) := by
  rw [← evt014With_snapOf]
  exact evt014With_holds evt014_snapOf_carries

/-- ✓ A snapshot that also lists a place the net does not declare, with its tokens, meets
EVT-014, as Java's does: here the executor also lists the undeclared place `z` whenever it holds
a token. TypeScript leaves such a place out, which the witness does too. -/
@[evidence allows EVT_014]
theorem EVT_014_allows_undeclared {T : Type} :
    EVT_014 (evt014With (T := T) fun C M => evt014_snapOn (C.X.net.places ++ ["z"]) M) :=
  evt014With_holds fun _ M => evt014_snapOn_carries (fun _ h => List.mem_append_left _ h) M

/-! ## The worked example -/

/-- Transition `t`: takes the token of place `b`. -/
def evt014_tT : Trans String :=
  { core := { name := "t", inputs := [⟨"b", .one⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- The configuration of the example: the net declares `b`, `c` and `a`, in that order, and the
transition `t`, Immediate. -/
def evt014_cfg : Cfg String Nat :=
  { X := { net := { places := ["b", "c", "a"], transitions := [evt014_tT] },
           timing := fun _ => .immediate, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => false,
    res := 0 }

/-- The initial marking: 1 on `b`, 2 on `a`, nothing on `c`. -/
def evt014_m0 : QMarking String Nat := fun p => if p = "b" then [1] else if p = "a" then [2] else []

/-- The labels of the run up to its termination test: one cycle in which `t` starts
synchronously, returns and is settled, then a second cycle that finds nothing to do. -/
def evt014_labels : List (XLbl String Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin,
   .start "t" true, .ret 0 true, .commit 0, .endPass,
   .endCompletions, .endPublications, .endEvents, .update, .deadline []]

/-- The state before the run finishes quiescent. -/
def evt014_beforeFinish : Option (XSt String Nat) :=
  xrun evt014_cfg (xinit evt014_m0 0) evt014_labels

/-- ✓ Both lines are exercised by the witness on the example: the start snapshot is `a` 2,
`b` 1, after `ExecutionStarted` (the empty `c` left out, and `a` first although the net declares
`b` first); after `t` took the token of `b`, the quiescent finish reports `a` 2 alone, before
`ExecutionCompleted`. -/
@[evidence nonvacuous EVT_014]
theorem EVT_014_nonvacuous :
    (refEvExec (N := String) (T := Nat) polJT).boot evt014_cfg evt014_m0 =
      [.executionStarted, .markingSnapshot [("a", [2]), ("b", [1])]] ∧
    ∃ s s' evs, (refEvExec (N := String) (T := Nat) polJT).step evt014_cfg [] s
      (.finish .quiescent) evs s' ∧
      evs = [.markingSnapshot [("a", [2])], .executionCompleted] ∧ s'.M "b" = [] := by
  refine ⟨by decide +kernel, ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt014_cfg) (o := evt014_beforeFinish)
    (l := .finish .quiescent)
    (p := fun s s' =>
      refEmitW polJT evt014_cfg [] s (.finish .quiescent) s' ==
          [.markingSnapshot [("a", [2])], .executionCompleted] && s'.M "b" == [])
    (by decide +kernel)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨s, s', _, ⟨hs, rfl⟩, hp.1, hp.2⟩

/-! ## Wrong executors -/

/-- ✗ The reference with the Rust and Python emission violates EVT-014 (line 1): it reports no
snapshot at all, so the requirement is scoped to Java and TypeScript. -/
@[evidence forbids EVT_014]
theorem EVT_014_forbids_rust : ¬ EVT_014 (refEvExec (N := String) (T := Nat) polRust) := by
  intro h
  obtain ⟨pre, m, post, he, hs, -⟩ := (h evt014_cfg).1 evt014_m0
  have he' : [NetEvent.executionStarted] = pre ++ .markingSnapshot m :: post := he
  rcases pre with _ | ⟨a, rest⟩
  · simp at he'
  · simp at he'

/-- ✗ Listing the places in the order the net declares them violates EVT-014: the example net
declares `b` before `a`, so the start snapshot lists `b` first. This was TypeScript's payload
before it adopted the order of [CORE-073]. -/
@[evidence forbids EVT_014]
theorem EVT_014_forbids_declOrder : ¬ EVT_014 (evt014With (T := Nat) evt014_declOrder) := by
  intro h
  have := evt014With_boot_carries ((evt014_iff _).1 h).1 evt014_cfg evt014_m0
  revert this
  decide +kernel

/-- The [CORE-073] example names U+10000 and U+E000, both declared and marked. -/
def evt014_cfgCP : Cfg String Nat :=
  { evt014_cfg with
    X := { net := { places := [snapNameAstral, snapNameBmp], transitions := [] },
           timing := fun _ => .immediate, tol := 0 } }

/-- 1 on U+10000, 2 on U+E000. -/
def evt014_m0CP : QMarking String Nat := fun p =>
  if p = snapNameAstral then [1] else if p = snapNameBmp then [2] else []

/-- ✗ Sorting the places by UTF-16 code unit violates EVT-014 (AC4): U+10000 is the surrogate
D800 in UTF-16, so that order lists it before U+E000, while code-point order lists U+E000
first. -/
@[evidence forbids EVT_014]
theorem EVT_014_forbids_utf16 :
    ¬ EVT_014 (evt014With (T := Nat) fun C M =>
      core073_snapUtf16 (evt014_restrictFin C.X.net.places M)) := by
  intro h
  have := evt014With_boot_carries ((evt014_iff _).1 h).1 evt014_cfgCP evt014_m0CP
  revert this
  decide +kernel

/-- ✗ Keeping a declared place that holds no token violates EVT-014 (AC3): the start snapshot
of the example lists `c` with an empty queue. -/
@[evidence forbids EVT_014]
theorem EVT_014_forbids_keepEmpty :
    ¬ EVT_014 (evt014With (T := Nat) fun C M =>
      core073_snapKeep (evt014_restrictFin C.X.net.places M)) := by
  intro h
  have := evt014With_boot_carries ((evt014_iff _).1 h).1 evt014_cfg evt014_m0
  revert this
  decide +kernel

/-- ✗ A snapshot that lists no place violates EVT-014: the example starts with tokens on the
declared places `a` and `b`. -/
@[evidence forbids EVT_014]
theorem EVT_014_forbids_empty : ¬ EVT_014 (evt014With (T := Nat) fun _ _ => []) := by
  intro h
  have := evt014With_boot_carries ((evt014_iff _).1 h).1 evt014_cfg evt014_m0
  revert this
  decide +kernel

/-- ✗ A snapshot that lists the undeclared place `z` with a token `z` does not hold violates
EVT-014: the declared places are right and in order, but the entry for `z` is made up. -/
@[evidence forbids EVT_014]
theorem EVT_014_forbids_forged :
    ¬ EVT_014 (evt014With (T := Nat) fun C M => evt014_declSnap C M ++ [("z", [0])]) := by
  intro h
  have := evt014With_boot_carries ((evt014_iff _).1 h).1 evt014_cfg evt014_m0
  revert this
  decide +kernel

/-- ✗ Listing a place twice violates EVT-014, even in otherwise ascending order: on the example
the start snapshot lists `a` with 2, `a` with 2 again, `b` with 1 and `b` with 1 again. -/
@[evidence forbids EVT_014]
theorem EVT_014_forbids_duplicate :
    ¬ EVT_014 (evt014With (T := Nat) fun C M => (evt014_declSnap C M).flatMap fun e => [e, e]) := by
  intro h
  have := evt014With_boot_carries ((evt014_iff _).1 h).1 evt014_cfg evt014_m0
  revert this
  decide +kernel

/-- The example marking with two tokens on `a`, 2 placed before 3, and 1 on `b`. -/
def evt014_m0Two : QMarking String Nat := fun p =>
  if p = "b" then [1] else if p = "a" then [2, 3] else []

/-- ✗ Listing a queue newest first violates EVT-014 (all of a place's tokens in FIFO order): `a`
holds 2 and then 3, and the snapshot lists `a` with 3, 2. With one token per place, as in the
example run, the reversed snapshot looks the same, so this example puts two tokens on `a`. -/
@[evidence forbids EVT_014]
theorem EVT_014_forbids_lifo :
    ¬ EVT_014 (evt014With (T := Nat) fun C M =>
      (evt014_declSnap C M).map fun e => (e.1, e.2.reverse)) := by
  intro h
  have := evt014With_boot_carries ((evt014_iff _).1 h).1 evt014_cfg evt014_m0Two
  revert this
  decide +kernel

/-- The executor that reports the start snapshot before `ExecutionStarted`. -/
def evt014_snapFirst : EvExec String Nat :=
  emitExec (fun C M0 => [.markingSnapshot (evt014_declSnap C M0), .executionStarted])
    (evt014Emit evt014_declSnap)

/-- ✗ Reporting the start snapshot before `ExecutionStarted` violates EVT-014 (line 1). Its
snapshot is the right one and its steps are the witness's, so it keeps lines 2 to 4. -/
@[evidence mutant EVT_014]
theorem EVT_014_mutant_snapFirst :
    evt014_but1 evt014_snapFirst ∧ ¬ EVT_014 evt014_snapFirst := by
  refine ⟨⟨evt014_line2_of evt014_declSnap_carries _, fun C M0 m hm => ?_,
    evt014_line4_of (fun C M => (evt014_declSnap_carries C M).1) _⟩, fun h => ?_⟩
  · simp only [evt014_snapFirst, emitExec, List.mem_cons, List.not_mem_nil,
      or_false, reduceCtorEq, NetEvent.markingSnapshot.injEq] at hm
    subst hm
    exact (evt014_declSnap_carries C M0).1
  obtain ⟨pre, m, post, he, hs, -⟩ := (h evt014_cfg).1 evt014_m0
  rcases evt014_split2 he with ⟨rfl, -, -⟩ | ⟨-, hz, -⟩
  · cases hs
  · cases hz

/-- The emission of the witness with `ExecutionCompleted` reported before the end snapshot. -/
def evt014_completedFirstEmit (C : Cfg String Nat) (H : List (NetEvent String Nat))
    (s : XSt String Nat) (l : XLbl String Nat) (s' : XSt String Nat) :
    List (NetEvent String Nat) :=
  match l with
  | .finish _ => [.executionCompleted, .markingSnapshot (evt014_declSnap C s.M)]
  | _ => refEmitW polJT C H s l s'

/-- The executor that reports `ExecutionCompleted` before the end snapshot. -/
def evt014_completedFirst : EvExec String Nat :=
  emitExec (evt014Boot evt014_declSnap) evt014_completedFirstEmit

/-- ✗ Reporting `ExecutionCompleted` before the end snapshot violates EVT-014 (line 2): when the
example run finishes, the snapshot comes last. Its boot is the witness's and its end snapshot is
the right one, so it keeps lines 1, 3 and 4. -/
@[evidence mutant EVT_014]
theorem EVT_014_mutant_completedFirst :
    evt014_but2 evt014_completedFirst ∧ ¬ EVT_014 evt014_completedFirst := by
  refine ⟨⟨evt014_line1_of evt014_declSnap_carries _,
    evt014_line3_of (fun C M => (evt014_declSnap_carries C M).1) _,
    fun C H l evs s s' hs m hm => ?_⟩, fun h => ?_⟩
  · obtain ⟨-, rfl⟩ := hs
    by_cases hl : ∃ c, l = .finish c
    · obtain ⟨c, rfl⟩ := hl
      simp only [evt014_completedFirstEmit, List.mem_cons, List.not_mem_nil,
        or_false, reduceCtorEq, false_or, NetEvent.markingSnapshot.injEq] at hm
      subst hm
      exact (evt014_declSnap_carries C s.M).1
    · have hl' : ∀ c, l ≠ .finish c := fun c h => hl ⟨c, h⟩
      have he : evt014_completedFirstEmit C H s l s' = refEmitW polJT C H s l s' := by
        cases l <;> first | rfl | exact absurd rfl (hl' _)
      rw [he] at hm
      exact absurd hm (evt014_refEmit_noSnap hl' m)
  obtain ⟨s, s', -, hs, -⟩ := step_of_check xstep (C := evt014_cfg) (o := evt014_beforeFinish)
    (l := .finish .quiescent) (p := fun _ _ => true) (by decide +kernel)
  obtain ⟨pre, m, post, he, hs', -⟩ :=
    (h evt014_cfg).2.1 [] .quiescent _ s s' ⟨hs, rfl⟩
  rcases evt014_split2 he with ⟨-, hz, -⟩ | ⟨-, -, rfl⟩
  · cases hz
  · cases hs'

/-- The executor that, at the boot, also reports a second snapshot that keeps the declared
places with no token. -/
def evt014_bootKeepEmpty : EvExec String Nat :=
  emitExec (fun C M0 => [.executionStarted, .markingSnapshot (evt014_declSnap C M0),
      .markingSnapshot (core073_snapKeep (evt014_restrictFin C.X.net.places M0))])
    (evt014Emit evt014_declSnap)

/-- ✗ A further snapshot at the start that lists an empty place violates EVT-014 (line 3): on
the example the boot reports the right snapshot `a` 2, `b` 1, and then a second one that also
lists the empty place `c`. The right snapshot is there and the steps are the witness's, so it
keeps lines 1, 2 and 4. -/
@[evidence mutant EVT_014]
theorem EVT_014_mutant_bootKeepEmpty :
    evt014_but3 evt014_bootKeepEmpty ∧ ¬ EVT_014 evt014_bootKeepEmpty := by
  refine ⟨⟨fun C M0 => ⟨[.executionStarted], evt014_declSnap C M0, _, rfl,
      List.mem_singleton_self _, evt014_declSnap_carries C M0⟩,
    evt014_line2_of evt014_declSnap_carries _,
    evt014_line4_of (fun C M => (evt014_declSnap_carries C M).1) _⟩, fun h => ?_⟩
  have := (h evt014_cfg).2.2.1 evt014_m0
    (core073_snapKeep (evt014_restrictFin evt014_cfg.X.net.places evt014_m0))
    (by simp [evt014_bootKeepEmpty, emitExec])
  revert this
  decide +kernel

/-- The emission of the witness plus, at the start of every cycle, a snapshot of the marking in
the order the net declares its places (`evt014_declOrder`). -/
def evt014_cycleDeclOrderEmit (C : Cfg String Nat) (H : List (NetEvent String Nat))
    (s : XSt String Nat) (l : XLbl String Nat) (s' : XSt String Nat) :
    List (NetEvent String Nat) :=
  match l with
  | .finish _ => [.markingSnapshot (evt014_declSnap C s.M), .executionCompleted]
  | .begin => refEmitW polJT C H s l s' ++ [.markingSnapshot (evt014_declOrder C s'.M)]
  | _ => refEmitW polJT C H s l s'

/-- The executor that also reports a snapshot in declaration order at the start of every
cycle. -/
def evt014_cycleDeclOrder : EvExec String Nat :=
  emitExec (evt014Boot evt014_declSnap) evt014_cycleDeclOrderEmit

/-- ✗ A further snapshot during the run that lists the places in declaration order violates
EVT-014 (line 4): on the example the first cycle starts with the snapshot `b` 1, `a` 2, because
the net declares `b` first. Its start and end snapshots are the witness's, so it keeps lines 1
to 3. -/
@[evidence mutant EVT_014]
theorem EVT_014_mutant_cycleDeclOrder :
    evt014_but4 evt014_cycleDeclOrder ∧ ¬ EVT_014 evt014_cycleDeclOrder := by
  refine ⟨⟨evt014_line1_of evt014_declSnap_carries _, fun C H c evs s s' hs => ?_,
    evt014_line3_of (fun C M => (evt014_declSnap_carries C M).1) _⟩, fun h => ?_⟩
  · obtain ⟨hx, rfl⟩ := hs
    refine ⟨[], evt014_declSnap C s.M, [.executionCompleted], rfl, List.mem_singleton_self _, ?_⟩
    rw [xstep_finish_M hx]
    exact evt014_declSnap_carries C s.M
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt014_cfg)
      (o := xrun evt014_cfg (xinit evt014_m0 0) (evt014_labels.take 5)) (l := .begin)
      (p := fun _ s' => evt014_declOrder evt014_cfg s'.M == [("b", [1]), ("a", [2])])
      (by decide +kernel)
    simp only [beq_iff_eq] at hp
    have := (h evt014_cfg).2.2.2 [] .begin _ s s' ⟨hs, rfl⟩ [("b", [1]), ("a", [2])] (by
      show _ ∈ refEmitW polJT evt014_cfg [] s .begin s' ++
        [.markingSnapshot (evt014_declOrder evt014_cfg s'.M)]
      rw [hp]
      exact List.mem_append_right _ (List.mem_singleton_self _))
    revert this
    decide +kernel

/-- The emission of the witness with, after `ExecutionCompleted`, a second end snapshot that
keeps the declared places with no token. -/
def evt014_finishKeepEmptyEmit (C : Cfg String Nat) (H : List (NetEvent String Nat))
    (s : XSt String Nat) (l : XLbl String Nat) (s' : XSt String Nat) :
    List (NetEvent String Nat) :=
  match l with
  | .finish _ => [.markingSnapshot (evt014_declSnap C s.M), .executionCompleted,
      .markingSnapshot (core073_snapKeep (evt014_restrictFin C.X.net.places s.M))]
  | _ => refEmitW polJT C H s l s'

/-- ✗ A second end snapshot that lists empty places violates EVT-014, although the first end
snapshot is right: when the example run finishes, `a` 2 comes before `ExecutionCompleted`, and
after it a snapshot that also lists the emptied `b` and the empty `c`. -/
@[evidence forbids EVT_014]
theorem EVT_014_forbids_finishKeepEmpty :
    ¬ EVT_014 (emitExec (evt014Boot evt014_declSnap) evt014_finishKeepEmptyEmit) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt014_cfg) (o := evt014_beforeFinish)
    (l := .finish .quiescent)
    (p := fun s _ =>
      !decide (QCanon (core073_snapKeep (evt014_restrictFin evt014_cfg.X.net.places s.M))))
    (by decide +kernel)
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hp
  exact hp ((h evt014_cfg).2.2.2 [] (.finish .quiescent) _ s s' ⟨hs, rfl⟩ _
    (by simp [evt014_finishKeepEmptyEmit]))

end Libpetri.Spec
