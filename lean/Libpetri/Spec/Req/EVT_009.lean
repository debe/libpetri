import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Events
import Libpetri.Reference.ExecLink
import Libpetri.Spec.Req.TIME_cycle
import Libpetri.Spec.Req.CONC_005_cycle
import Libpetri.Spec.Req.CONC_001
import Libpetri.Spec.Req.EXEC_003
import Libpetri.Spec.Text.EVT_009

set_option linter.missingDocs true

/-!
# EVT-009: TransitionTimedOut Event (`spec/08-events-observability.md`)

When the executor reaps a transition ([TIME-013]), it reports the reap with one
`TransitionTimedOut` event naming the transition, and it reports it at no other time. The
requirement has two blocks with the same spec ID (rulings D33 (a) and D38 (a)):

* `EVT_009`, for every executor: it reads an event only through its kind and the transition it
  names, which every runtime's event carries. Line 1: a step that reaps a transition emits
  exactly one `TransitionTimedOut` naming it. Line 2: every `TransitionTimedOut` a step emits
  names a transition that step reaps, and the boot of a run emits none.
* `EVT_009_payload`, for the executors whose event carries the deadline and the elapsed time
  (Java and TypeScript): the deadline is the transition's latest bound, without the deadline
  tolerance, and the elapsed time is the transition's elapsed time at the reading of the deadline
  step that reaps it.

Both are predicates over an abstract executor with events `E : EvExec N T`
(`Reference/Events.lean`). To reap is the executor's status change to the status reaped
(`Status.reaped`, the glossary's `ReapedE`, ruling D6): a name not reaped before the step and
reaped after it. It is not the glossary's state predicate `Reaped` (enabled and not armed), which
also holds of an enabled name whose status is off. The witness is the reference executor with
events `refEvExec`, under both emission variants. The wrong executors step as the reference and
emit otherwise: one that reaps silently, one that reports a reap as an `ActionTimedOut`, one that
reports an `Exact` transition started past its target as timed out, one that reports at boot, one
whose deadline field adds the tolerance, and one whose elapsed field is read at the update's
reading.

The worked examples. In `evt009_cfg`, transition `u` is `Window(3, 5)` on place 0, transition `x`
is `Exact(3)` on place 1, the tolerance is 1 ms, both are armed at reading 0. The host falls
behind and the next cycle reads 7. Its deadline step reaps `u` (elapsed 7 is past 5 + 1) and
emits one `TransitionTimedOut` for `u` with deadline 5 and elapsed 7; `x` is not reapable, is not
reaped, and starts in the pass with no `TransitionTimedOut`. In `evt009_cfgD`, the markdown's test
derivation, `u` is `Deadline(5)`: the update arms it at reading 0, the host is delayed to reading 7
before the deadline step, and that step reaps `u` and reports deadline 5 and elapsed 7.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Novel.TimedScg (Timing)

/-! ## Vocabulary -/

section Vocabulary

variable {N T : Type}

/-- The number of `TransitionTimedOut` events of `evs` naming the transition `n`. It reads the
kind and the transition name of an event only, which every executor's event carries. -/
def timedOutCount (evs : List (NetEvent N T)) (n : String) : Nat :=
  evs.countP fun e => e.kind == .transitionTimedOut && e.trans? == some n

end Vocabulary

/-! ## EVT-009, every executor: one event per reap, only at a reap -/

requirement EVT_009
  id "EVT-009"
  title "TransitionTimedOut Event"
  kind B
  scope "all executors (event store enabled)"
  source verbatim "spec/08-events-observability.md"
  covers EVT_009.s1, EVT_009.s2, EVT_009.s4
  reading "For every executor with events E and every configuration C:"
          "if the transition names of C are pairwise distinct, then for every history H a step from state s to state s' that appends the events evs and leaves a name n reaped that was not reaped in s appends exactly one TransitionTimedOut event naming n;"
          "the events a run emits before its first step contain no TransitionTimedOut event, whatever the initial marking, and for every history H every TransitionTimedOut event a step from s to s' appends names a name that is not reaped in s and is reaped in s'."
  assumes "The model is an executor with events E : EvExec N T (Reference/Events.lean): the events a run emits before its first step, and a step relation E.step C H s l evs s' saying that the step labelled l leads from s to s' and appends the events evs, given the events H emitted before it. The witness is the reference executor with events refEvExec, the reference executor RefExec with its emission refEmitW, under both emission variants (polJT for Java and TypeScript, polRust for Rust and Python). refEvExec_erase (Reference/EventsLink.lean) shows that it steps exactly as RefExec, so the block constrains what is emitted and nothing else. Both lines hold for every history H."
          "To reap is read at the grain of the executor: the step takes a name from a status that is not reaped (off or armed) to the executor status reaped (Status.reaped, the glossary's ReapedE, ruling D6). It is not the glossary's state predicate Reaped on the timed view (enabled and not armed), which also holds of an enabled name whose status is off, such as a transition whose firing is in flight in an executor that is not re-entrant, or a pass loser; a step that leaves a name off reaps nothing. Which transitions are reaped, and in which step, is TIME-013's: its executor companion TIME_013_cycle says that the deadline step of a cycle ([EXEC-001] step 4) reaps exactly the transitions expired at its reading (its lines 1 and 2), and that a step other than a deadline step reaps nothing (its line 6); the consequences below that need these read TIME_013_cycle as a premise. This block says what is emitted when a reap happens, so it holds whatever reaps: an executor whose deadline step leaves an expired transition off instead of reaped and reports nothing meets it, and TIME_013_cycle line 1 rejects it (evt009_disarmSilent_needs_time013)."
          "Main block and companion (rulings D33 (a) and D38 (a)): this block reads an event only through its kind and the transition it names (timedOutCount, and trans? in line 2), which every executor's event carries. The deadline and the elapsed time an event carries are read only by the second block of EVT-009, EVT_009_payload, scoped to Java and TypeScript: the Rust event, which Python runs on, carries the transition name and the timestamp only (rust/libpetri-event/src/net_event.rs TransitionTimedOut)."
          "Line 1 is the first quoted sentence: a reap emits exactly one event, and it names the reaped transition. It needs pairwise distinct transition names, the third quoted sentence (ruling D10, NamesDistinct): the status is kept per name, and two transitions of one name that expire together are one reaped name with two events. An executor that reaps silently breaks it (EVT_009_mutant_silentReap), and so does one that reports the reap as an ActionTimedOut, the event of an action's Out.Timeout ([EVT-010]) (EVT_009_forbids_asActionTimedOut)."
          "Line 2 is the second quoted sentence: an event names a transition the same step reaps, and the boot of a run reaps nothing and emits none. An executor that reports an Exact transition it starts past its target as timed out breaks it (EVT_009_mutant_onLateStart): Exact is enforced softly, fires at the first opportunity at or after its target and is never reaped ([TIME-006]), so AC1 read alone (an event whenever the elapsed time is past the bound plus the tolerance) does not describe it (clash C8, ruled D5). So does one that reports a TransitionTimedOut at boot (EVT_009_forbids_atBoot). No runtime emits the event elsewhere: Java and TypeScript emit it only in the deadline enforcement of a cycle (enforceDeadlines in java/src/main/java/org/libpetri/runtime/BitmapNetExecutor.java and PrecompiledNetExecutor.java, typescript/src/runtime/bitmap-net-executor.ts and precompiled-net-executor.ts), Rust only after enforce_deadlines (in run_sync and run_async, rust/libpetri-runtime/src/executor_core/executor.rs), each once per reaped transition, and the precompiled executors likewise."
          "AC1 (emitted in the deadline step of a cycle at whose reading a reapable, armed transition's elapsed time is strictly greater than its latest bound plus the deadline tolerance, never for an Exact transition) is evt009_ac1 and evt009_ac1_otherSteps. evt009_ac1: for an executor that also meets TIME-013's executor companion, a deadline step emits exactly one TransitionTimedOut for every transition of the net expired at its reading (reapable and armed, ruling D5), and every TransitionTimedOut it emits names such a transition; an Exact transition is never reapable ([TIME-006]), so never expired. evt009_ac1_otherSteps: for an executor that also meets TIME_013_cycle, whose line 6 says a step other than a deadline step reaps nothing, no other step emits a TransitionTimedOut, so neither does the start of an Exact transition past its target. The event comes in the deadline step of the first cycle whose reading puts the elapsed time past the bound plus the tolerance, not at the instant the elapsed time crosses it: in EVT_009_nonvacuous the host falls behind and the event comes at reading 7."
          "AC2 (after the event the transition is reaped: it stays enabled but is not armed, and does not fire until one of its arc places is written) is evt009_ac2 and evt009_ac2_enabled. evt009_ac2 speaks of every labelled run from a state whose firing pass has no ready order left (the initial state, or a restored marking) of an executor that also meets CONC-005's executor companion, CONC-001 and EXEC-003: the event's step leaves the name reaped, so not armed; a step of the run takes the name out of the reaped status only by writing one of the transition's arc places (CONC_005_cycle line 3, which allows no other way out on such runs); no step of the run starts the name while it is reaped (EXEC-003 line 1: a start needs a stamp); and a step that writes none of the transition's arc places leaves its enablement as it was (CONC-001 line 2 and CONC_005_cycle line 4). evt009_ac2_enabled: for an executor that also meets TIME_013_cycle, with distinct names, the event's step leaves the transition enabled, because only a deadline step reaps (TIME_013_cycle line 6) and a deadline step reaps only expired, hence armed and enabled, transitions and keeps the marking (TIME_013_cycle line 2). Together: the transition stays enabled and reaped, and does not fire, until a step writes one of its arc places."
          "Not fixed here: the order of the TransitionTimedOut events of one deadline step (the reference emits them in declaration order, as Java and Rust do), the timestamp the event carries (the epoch clock is the CORE-011 slice), and the deadline and elapsed fields (the second block). The opening sentence of the markdown section (TransitionTimedOut reports a reap) is the subject line of the quoted sentences; the condition for a reap is TIME-013's, reached through AC1."
          "Assumptions shared by the executor event blocks: the event store is enabled and its append does not fail (EVT-020: a store that reports itself not enabled receives nothing, storeSink); an event is a value (EVT-001); transition names are distinct (ruling D10). The events of one step are contiguous in the model, since a step appends its events at once. Java appends ActionTimedOut events and the log messages it captures from actions from other threads than the orchestrator (the timeout callback BitmapNetExecutor.fireTransition hands java/src/main/java/org/libpetri/runtime/ExecutorSupport.java withActionTimeout, which appends through emitEvent from the timer thread; LogCaptureScope.java wrapRunnable and wrapCallable), so in a Java store such an event can fall between the events of one step; the lines are read on the store with those events left out, as the reading at the top of spec/08-events-observability.md says. TypeScript and Rust append every event from the orchestrator."
          "The test derivation (a Deadline(100ms) transition, firing delayed 200 ms, a TransitionTimedOut event) is EVT_009_nonvacuous_deadline in milliseconds: a Deadline(5) transition armed by the update at reading 0, tolerance 1, the host delayed to reading 7 before the deadline step, which reaps it and emits exactly one TransitionTimedOut, for it. EVT_009_nonvacuous adds a Window(3, 5) transition reaped by the next cycle at reading 7, and an Exact(3) transition of the same net that is not reaped and whose start emits no TransitionTimedOut."
  signoff "2026-11-13 3b83953ac7adb832 ai"
  statement : ∀ {N T : Type} [DecidableEq N], EvExec N T → Prop :=
    fun E => ∀ C,
      (NamesDistinct C.X → ∀ H l evs n, on (fun s s' => E.step C H s l evs s'), shall (fun s s' =>
          s.st n ≠ .reaped → s'.st n = .reaped → timedOutCount evs n = 1)) ∧
      ((∀ M0, ∀ e ∈ E.boot C M0, e.kind ≠ .transitionTimedOut) ∧
        ∀ H l evs, on (fun s s' => E.step C H s l evs s'), shall (fun s s' =>
          ∀ e ∈ evs, e.kind = .transitionTimedOut →
            ∃ n, e.trans? = some n ∧ s.st n ≠ .reaped ∧ s'.st n = .reaped))

/- The pinned readable form of EVT-009: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EVT_009 : {N T : Type} → [DecidableEq N] → EvExec N T → Prop :=
fun {N T} [DecidableEq N] E =>
  ∀ (C : Cfg N T),
    (NamesDistinct C.X →
        ∀ (H : List (NetEvent N T)) (l : XLbl N T) (evs : List (NetEvent N T)) (n : String),
          on fun s s' => E.step C H s l evs s', shall fun s s' =>
            s.st n ≠ Status.reaped → s'.st n = Status.reaped → timedOutCount evs n = 1) ∧
      (∀ (M0 : QMarking N T), ∀ e ∈ E.boot C M0, e.kind ≠ NetEventKind.transitionTimedOut) ∧
        ∀ (H : List (NetEvent N T)) (l : XLbl N T) (evs : List (NetEvent N T)),
          on fun s s' => E.step C H s l evs s', shall fun s s' =>
            ∀ e ∈ evs,
              e.kind = NetEventKind.transitionTimedOut →
                ∃ n, e.trans? = some n ∧ s.st n ≠ Status.reaped ∧ s'.st n = Status.reaped
-/
#guard_msgs in #print EVT_009

/-! ## EVT-009, Java and TypeScript companion: the deadline and the elapsed time -/

requirement EVT_009_payload
  id "EVT-009"
  title "TransitionTimedOut Event (deadline and elapsed time)"
  kind B
  scope "Java and TypeScript executors (event store enabled)"
  source verbatim "spec/08-events-observability.md"
  covers EVT_009.s3
  reading "For every executor with events E, every configuration C and every history H: every TransitionTimedOut event naming n with deadline d and elapsed time el that a step from state s to state s' appends names a transition u of the net under n, with d the latest bound of u's timing and el the elapsed time of u on the timed view of s at the cycle reading of s'."
  assumes "This is the second block of EVT-009 (rulings D33 (a) and D38 (a)): the deadline and elapsed fields, for the executors whose TransitionTimedOut event carries them. The first block, EVT_009, states when the event is emitted for every executor; this block adds what the two duration fields hold. Java builds the event from t.timing().latest() and the elapsed milliseconds the deadline check compared (enforceDeadlines in java/src/main/java/org/libpetri/runtime/BitmapNetExecutor.java and PrecompiledNetExecutor.java), TypeScript from timingLatest(t.timing) and the elapsed time it compared (enforceDeadlines in typescript/src/runtime/bitmap-net-executor.ts and precompiled-net-executor.ts). Rust and Python carry neither field (rust/libpetri-event/src/net_event.rs TransitionTimedOut), so only the first block applies to them."
          "The model is an executor with events E : EvExec N T, as in the first block; the witness is refEvExec polJT. The reading of a step is the cycle reading of its target state: a reap happens only in the deadline step (TIME_013_cycle), which moves the cycle reading to the reading it judges at (viewAt s s'.cyc, ruling D61 (c)), so the elapsed time is the one the deadline step compared with the bound plus the tolerance. The elapsed time is the glossary's Elapsed time, the time since the transition was last newly armed ([TIME-010], ruling D5), not the time since it was first enabled: a clock restart ([TIME-012]) starts it again. An executor whose deadline field adds the tolerance meets the first block and breaks this line (EVT_009_payload_mutant_plusTol), and so does one whose elapsed field is read at the update's reading while the reap is judged at the deadline step's (EVT_009_payload_mutant_updateReading)."
          "This block does not say on its own which step reaps or what the cycle reading of the target state is: for an executor that meets only this block, s'.cyc may be any value, and the line speaks of every step that emits the event. That the event is emitted only at a reaping step is the first block's line 2, that only the deadline step reaps is TIME_013_cycle's lines 1, 2 and 6, and that the deadline step's s'.cyc is the update's reading or the host's later present reading is TIME_010_cycle line 4. The reference's elapsed field, read at max s.cyc s.now, agrees with this line through the reference deadline step (xstepW_deadline)."
          "Durations are firing-clock readings in milliseconds; Java truncates its nanosecond readings to milliseconds before it subtracts, which the model's whole-millisecond readings do not show. The timestamp is not modelled. The shared assumptions of the first block (store enabled, events are values, distinct names) apply."
          "The test derivation is EVT_009_payload_nonvacuous and EVT_009_nonvacuous_deadline: the Window(3, 5) transition reaped at reading 7 reports deadline 5, not 6, and elapsed time 7; the Deadline(5) transition armed by the update at reading 0 and reaped by the deadline step at reading 7 reports elapsed time 7, the deadline step's reading, not 0, the update's."
  signoff "2026-11-13 6e7d17ef5af90b01 ai"
  statement : ∀ {N T : Type} [DecidableEq N], EvExec N T → Prop :=
    fun E => ∀ C H l evs,
      on (fun s s' => E.step C H s l evs s'), shall (fun s s' =>
        ∀ n d el, NetEvent.transitionTimedOut n d el ∈ evs →
          ∃ u, findT C n = some u ∧ d = (TimingOf C.X u).latest ∧
            el = Elapsed (viewAt s s'.cyc) u)

/- The pinned readable form of the companion: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EVT_009_payload : {N T : Type} → [DecidableEq N] → EvExec N T → Prop :=
fun {N T} [DecidableEq N] E =>
  ∀ (C : Cfg N T) (H : List (NetEvent N T)) (l : XLbl N T) (evs : List (NetEvent N T)),
    on fun s s' => E.step C H s l evs s', shall fun s s' =>
      ∀ (n : String) (d el : ℕ),
        NetEvent.transitionTimedOut n d el ∈ evs →
          ∃ u, findT C n = some u ∧ d = (TimingOf C.X u).latest ∧ el = Elapsed (viewAt s s'.cyc) u
-/
#guard_msgs in #print EVT_009_payload

/-! ## The lines of the first block, one at a time -/

section Lines

variable {N T : Type} [DecidableEq N] [Ord N]
/-- Line 1 of `EVT_009` alone: a step that reaps a name emits exactly one `TransitionTimedOut`
naming it (distinct names). -/
def evt009_line1 (E : EvExec N T) : Prop :=
  ∀ C, NamesDistinct C.X → ∀ H l evs n, on (fun s s' => E.step C H s l evs s'), shall
    (fun s s' => s.st n ≠ .reaped → s'.st n = .reaped → timedOutCount evs n = 1)

/-- Line 2 of `EVT_009` alone: the boot emits no `TransitionTimedOut`, and every one a step
emits names a name the step reaps. -/
def evt009_line2 (E : EvExec N T) : Prop :=
  ∀ C, (∀ M0, ∀ e ∈ E.boot C M0, e.kind ≠ .transitionTimedOut) ∧
    ∀ H l evs, on (fun s s' => E.step C H s l evs s'), shall (fun s s' =>
      ∀ e ∈ evs, e.kind = .transitionTimedOut →
        ∃ n, e.trans? = some n ∧ s.st n ≠ .reaped ∧ s'.st n = .reaped)

omit [Ord N] in
/-- `EVT_009` is its two lines. -/
theorem evt009_iff (E : EvExec N T) : EVT_009 E ↔ evt009_line1 E ∧ evt009_line2 E :=
  ⟨fun h => ⟨fun C => (h C).1, fun C => (h C).2⟩, fun h C => ⟨h.1 C, h.2 C⟩⟩

end Lines

/-! ## Emissions that agree with the reference at the deadline step -/

section Emissions

variable {N T : Type} [DecidableEq N] [Ord N]
/-- The `TransitionTimedOut` events of a deadline step reaping `ns`, one per name the net holds,
in the order of `ns`, with the deadline and elapsed fields `dl` and `el`. -/
def evt009_deadlineEvs (dl el : Cfg N T → XSt N T → Trans N → Nat) (C : Cfg N T) (s : XSt N T)
    (ns : List String) : List (NetEvent N T) :=
  ns.filterMap fun m => (findT C m).map fun u => .transitionTimedOut m (dl C s u) (el C s u)

/-- The reference deadline field: the latest bound of the transition, without the tolerance. -/
def evt009_refDl (C : Cfg N T) (_s : XSt N T) (u : Trans N) : Nat := (C.X.timing u).latest

/-- The reference elapsed field: the elapsed time at the deadline step's reading. -/
def evt009_refEl (_C : Cfg N T) (s : XSt N T) (u : Trans N) : Nat :=
  (viewAt s (max s.cyc s.now)).elapsed u

/-- The reference emits `evt009_deadlineEvs` at a deadline step. -/
theorem refEmitW_deadline (P : EvPol) (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T)
    (ns : List String) (s' : XSt N T) :
    refEmitW P C H s (.deadline ns) s' = evt009_deadlineEvs evt009_refDl evt009_refEl C s ns :=
  rfl

omit [DecidableEq N] [Ord N] in
/-- Counting the events of a deadline step: when the net holds every name of `ns`, there is one
`TransitionTimedOut` naming `n` per occurrence of `n` in `ns`. -/
theorem timedOutCount_deadlineEvs (dl el : Cfg N T → XSt N T → Trans N → Nat) (C : Cfg N T)
    (s : XSt N T) (n : String) :
    ∀ ns : List String, (∀ m ∈ ns, (findT C m).isSome) →
      timedOutCount (evt009_deadlineEvs dl el C s ns) n = ns.count n
  | [], _ => rfl
  | m :: ns, hf => by
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 (hf m List.mem_cons_self)
    have ih := timedOutCount_deadlineEvs dl el C s n ns fun m' hm' => hf m' (List.mem_cons_of_mem _ hm')
    unfold evt009_deadlineEvs at ih ⊢
    rw [List.filterMap_cons, hu, Option.map_some]
    simp only [timedOutCount, List.countP_cons, List.count_cons] at ih ⊢
    rw [ih]
    by_cases h : m = n
    · subst h; simp [NetEvent.kind, NetEvent.trans?]
    · simp [NetEvent.kind, NetEvent.trans?, h]

omit [DecidableEq N] [Ord N] in
/-- An event of a deadline step names a name of `ns`. -/
theorem mem_deadlineEvs {dl el : Cfg N T → XSt N T → Trans N → Nat} {C : Cfg N T} {s : XSt N T}
    {ns : List String} {e : NetEvent N T} (he : e ∈ evt009_deadlineEvs dl el C s ns) :
    ∃ m ∈ ns, ∃ u, findT C m = some u ∧ e = .transitionTimedOut m (dl C s u) (el C s u) := by
  simp only [evt009_deadlineEvs, List.mem_filterMap, Option.map_eq_some_iff] at he
  obtain ⟨m, hm, u, hu, rfl⟩ := he
  exact ⟨m, hm, u, hu, rfl⟩

omit [DecidableEq N] [Ord N] in
/-- Every name a deadline step reaps is the name of a transition of the net. -/
theorem findT_of_mem_expiredNames {P : XPol N T} {C : Cfg N T} {s : XSt N T} {m : String}
    (h : m ∈ expiredNames P C s) : (findT C m).isSome := by
  obtain ⟨u, hu, hn, -⟩ := mem_expiredNames h
  unfold findT
  rw [List.find?_isSome]
  exact ⟨u, hu, by simp [hn]⟩

omit [DecidableEq N] [Ord N] in
/-- Every name a deadline step reaps is armed before it, so not reaped. -/
theorem not_reaped_of_mem_expiredNames {P : XPol N T} {C : Cfg N T} {s : XSt N T} {m : String}
    (h : m ∈ expiredNames P C (atDeadline s)) : s.st m ≠ .reaped := by
  obtain ⟨-, -, -, -, hs⟩ := mem_expiredNames h
  intro hr
  simp [atDeadline, hr, stampOf] at hs

omit [DecidableEq N] [Ord N] in
/-- With distinct names, the names a deadline step reaps are distinct. -/
theorem expiredNames_nodup {P : XPol N T} {C : Cfg N T} (hN : NamesDistinct C.X)
    (s : XSt N T) : (expiredNames P C s).Nodup :=
  List.Nodup.sublist (List.Sublist.map _ List.filter_sublist) hN

omit [Ord N] in
/-- **Line 1 for every emission that agrees with the reference at the deadline step**: whatever
the boot and the other steps emit, an executor that steps as the reference and emits
`evt009_deadlineEvs` at a deadline step meets line 1. -/
theorem evt009_line1_of {boot : Cfg N T → QMarking N T → List (NetEvent N T)}
    {emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    (dl el : Cfg N T → XSt N T → Trans N → Nat)
    (hd : ∀ C H s ns s', emit C H s (.deadline ns) s' = evt009_deadlineEvs dl el C s ns) :
    evt009_line1 (emitExec boot emit) := by
  intro C hN H l evs n s s' hs hn hr
  obtain ⟨hx, rfl⟩ := hs
  rcases reaped_origin (P := refXPol) hx hr with h | ⟨⟨ns, rfl⟩, hm⟩
  · exact absurd h hn
  obtain ⟨-, -, hns, -⟩ := xstepW_deadline (P := refXPol) hx
  rw [hd, timedOutCount_deadlineEvs dl el C s n ns (by
    rw [hns]; exact fun m hm => findT_of_mem_expiredNames hm)]
  rw [hns]
  exact List.count_eq_one_of_mem (expiredNames_nodup hN _) hm

omit [Ord N] in
/-- **Line 2 for every emission whose `TransitionTimedOut` events sit at the deadline step**: an
executor that steps as the reference, emits none at boot and at a step that is not a deadline
step, and at a deadline step reaping `ns` emits only ones naming a name of `ns`, meets line 2. -/
theorem evt009_line2_of {boot : Cfg N T → QMarking N T → List (NetEvent N T)}
    {emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    (hb : ∀ C M0, ∀ e ∈ boot C M0, e.kind ≠ .transitionTimedOut)
    (ho : ∀ C H s l s', (∀ ns, l ≠ .deadline ns) →
      ∀ e ∈ emit C H s l s', e.kind ≠ .transitionTimedOut)
    (hd : ∀ C H s ns s', ∀ e ∈ emit C H s (.deadline ns) s', e.kind = .transitionTimedOut →
      ∃ m ∈ ns, e.trans? = some m) :
    evt009_line2 (emitExec boot emit) := by
  intro C
  refine ⟨hb C, fun H l evs s s' hs e he hk => ?_⟩
  obtain ⟨hx, rfl⟩ := hs
  by_cases hl : ∃ ns, l = .deadline ns
  · obtain ⟨ns, rfl⟩ := hl
    obtain ⟨m, hm, ht⟩ := hd C H s ns s' e he hk
    obtain ⟨-, -, hns, rfl⟩ := xstepW_deadline (P := refXPol) hx
    refine ⟨m, ht, ?_, by simp [hm]⟩
    rw [hns] at hm
    exact not_reaped_of_mem_expiredNames hm
  · exact absurd hk (ho C H s l s' (fun ns h => hl ⟨ns, h⟩) e he)

omit [DecidableEq N] [Ord N] in
/-- The deadline events of the reference form name a name of `ns`. -/
theorem deadlineEvs_names {dl el : Cfg N T → XSt N T → Trans N → Nat} {C : Cfg N T}
    {s : XSt N T} {ns : List String} :
    ∀ e ∈ evt009_deadlineEvs dl el C s ns, e.kind = .transitionTimedOut → ∃ m ∈ ns,
      e.trans? = some m := by
  intro e he _
  obtain ⟨m, hm, u, -, rfl⟩ := mem_deadlineEvs he
  exact ⟨m, hm, rfl⟩

/-- The reference emits no `TransitionTimedOut` at a step that is not a deadline step. -/
theorem refEmitW_noTimedOut (P : EvPol) (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T)
    {l : XLbl N T} (hl : ∀ ns, l ≠ .deadline ns) (s' : XSt N T) :
    ∀ e ∈ refEmitW P C H s l s', e.kind ≠ .transitionTimedOut := by
  intro e he hk
  have := refEmitW_kind P C H s l s' e he
  rw [hk] at this
  cases l with
  | deadline ns => exact hl ns rfl
  | _ => simp [lblKinds] at this

/-- The reference boot emits no `TransitionTimedOut`. -/
theorem refBoot_noTimedOut (P : EvPol) (C : Cfg N T) (M0 : QMarking N T) :
    ∀ e ∈ refBoot P C M0, e.kind ≠ .transitionTimedOut := by
  intro e he hk
  rcases refBoot_kind P C M0 e he with h | h <;> rw [hk] at h <;> cases h

end Emissions

/-! ## The reference -/

section Reference

variable {N T : Type} [DecidableEq N] [Ord N]
/-- The reference meets the first block under every emission variant. -/
theorem evt009_ref (P : EvPol) : EVT_009 (refEvExec (N := N) (T := T) P) :=
  (evt009_iff _).2
    ⟨evt009_line1_of evt009_refDl evt009_refEl (refEmitW_deadline P),
     evt009_line2_of (refBoot_noTimedOut P)
       (fun C H s _ s' hl => refEmitW_noTimedOut P C H s hl s')
       (fun C H s ns s' => by rw [refEmitW_deadline]; exact deadlineEvs_names)⟩

/-- The reference meets the payload companion under every emission variant. -/
theorem evt009_payload_ref (P : EvPol) : EVT_009_payload (refEvExec (N := N) (T := T) P) := by
  intro C H l evs s s' hs n d el he
  obtain ⟨hx, rfl⟩ := hs
  by_cases hl : ∃ ns, l = .deadline ns
  · obtain ⟨ns, rfl⟩ := hl
    rw [refEmitW_deadline] at he
    obtain ⟨m, -, u, hu, he'⟩ := mem_deadlineEvs he
    obtain ⟨-, -, -, rfl⟩ := xstepW_deadline (P := refXPol) hx
    simp only [NetEvent.transitionTimedOut.injEq] at he'
    obtain ⟨rfl, rfl, rfl⟩ := he'
    exact ⟨u, hu, rfl, rfl⟩
  · exact absurd rfl (refEmitW_noTimedOut P C H s (fun ns h => hl ⟨ns, h⟩) s' _ he)

/-- ✓ The reference executor with the Java and TypeScript emission meets EVT-009: the deadline
step that reaps a transition reports it once, and nothing else reports a `TransitionTimedOut`. -/
@[evidence holds EVT_009]
theorem EVT_009_reference : EVT_009 (refEvExec (N := N) (T := T) polJT) := evt009_ref polJT

/-- ✓ The reference executor with the Rust and Python emission meets EVT-009 too: the block is a
line for every executor. -/
@[evidence holds EVT_009]
theorem EVT_009_rust : EVT_009 (refEvExec (N := N) (T := T) polRust) := evt009_ref polRust

/-- ✓ The reference executor with the Java and TypeScript emission meets the payload companion:
a reported deadline is the transition's latest bound, and the reported elapsed time is the one
the deadline step compared. -/
@[evidence holds EVT_009_payload]
theorem EVT_009_payload_reference : EVT_009_payload (refEvExec (N := N) (T := T) polJT) :=
  evt009_payload_ref polJT

end Reference

/-! ## AC1 and AC2, with TIME-013's executor companion -/

section Consequences

variable {N T : Type} [DecidableEq N] [Ord N]
omit [DecidableEq N] [Ord N] in
/-- An expired transition is armed, so its name is not reaped. -/
theorem evt009_not_reaped_of_expired {C : Cfg N T} {s : XSt N T} {r : Nat} {u : Trans N}
    (h : Expired C.X (viewAt s r) u) : s.st u.core.name ≠ .reaped := by
  intro hr
  have := h.2.1.2
  simp [viewAt, hr, stampOf] at this

omit [Ord N] in
/-- **AC1** for every executor that meets EVT-009 and TIME-013's executor companion: a deadline
step emits exactly one `TransitionTimedOut` for each transition of the net that is expired at its
reading, and every `TransitionTimedOut` it emits names a transition of the net expired at that
reading. -/
@[evidence cites "EVT-009" "AC1: emitted in the deadline step of a cycle at whose reading a reapable, armed transition's elapsed time is strictly greater than its latest bound plus the deadline tolerance; read with TIME-013's executor companion, a deadline step emits exactly one TransitionTimedOut for each reapable, armed transition whose elapsed time at its reading is past the bound plus the tolerance, and only for those (ruling D5), so never for an Exact transition", evidence cites "TIME-013" "the executor shall reap it in the deadline step of that cycle and emit TransitionTimedOut ([EVT-009]): with EVT-009, the deadline step that reaps an expired transition emits exactly one TransitionTimedOut naming it"]
theorem evt009_ac1 {E : EvExec N T} (hE : EVT_009 E) (hT : TIME_013_cycle E.erase)
    {C : Cfg N T} (hN : NamesDistinct C.X) {H : List (NetEvent N T)} {ns : List String}
    {evs : List (NetEvent N T)} {s s' : XSt N T} (hs : E.step C H s (.deadline ns) evs s') :
    (∀ u ∈ C.X.net.transitions, Expired C.X (viewAt s s'.cyc) u →
      timedOutCount evs u.core.name = 1) ∧
    (∀ e ∈ evs, e.kind = .transitionTimedOut →
      ∃ u ∈ C.X.net.transitions, e.trans? = some u.core.name ∧ Expired C.X (viewAt s s'.cyc) u) := by
  have hx : E.erase C s (.deadline ns) s' := ⟨H, evs, hs⟩
  refine ⟨fun u hu hexp => ?_, fun e he hk => ?_⟩
  · exact (hE C).1 hN H _ evs u.core.name s s' hs (evt009_not_reaped_of_expired hexp)
      ((hT C).1 ns u hu s s' hx hexp)
  · obtain ⟨n, ht, hn, hr⟩ := (hE C).2.2 H _ evs s s' hs e he hk
    obtain ⟨-, hc⟩ := (hT C).2.1 ns n s s' hx
    obtain ⟨-, u, hu, rfl, hexp⟩ := hc (by rw [hr]; exact Ne.symm hn)
    exact ⟨u, hu, ht, hexp⟩

omit [Ord N] in
/-- **AC1 at every other step**, for every executor that meets EVT-009 and TIME-013's executor
companion: a step that is not a deadline step emits no `TransitionTimedOut`, because it reaps
nothing (TIME_013_cycle line 6). So the start of an
`Exact` transition past its target, three milliseconds late or three hours, reports no timeout. -/
@[evidence cites "EVT-009" "AC1: never for an Exact transition; read with TIME-013's executor companion, whose line 6 says a step other than a deadline step reaps nothing, no step other than a deadline step emits a TransitionTimedOut, so neither does the late start of an Exact transition"]
theorem evt009_ac1_otherSteps {E : EvExec N T} (hE : EVT_009 E)
    (hT : TIME_013_cycle E.erase) {C : Cfg N T} {H : List (NetEvent N T)}
    {l : XLbl N T} {evs : List (NetEvent N T)} {s s' : XSt N T} (hl : ∀ ns, l ≠ .deadline ns)
    (hs : E.step C H s l evs s') : ∀ e ∈ evs, e.kind ≠ .transitionTimedOut := by
  intro e he hk
  obtain ⟨n, -, hn, hr⟩ := (hE C).2.2 H l evs s s' hs e he hk
  exact (hT C).2.2.2.2.2 l n hl s s' ⟨H, evs, hs⟩ hn hr

omit [DecidableEq N] [Ord N] in
/-- A labelled run with its events forgotten is a run of the executor underneath. -/
theorem evt009_lrun_xrun {E : EvExec N T} {C : Cfg N T} :
    ∀ {H : List (NetEvent N T)} {s : XSt N T} {run : List (EvStep N T)}, LRun E C H s run →
      XRun E.erase C s (run.map fun st => (st.src, st.lbl, st.dst))
  | _, _, [], _ => trivial
  | H, _, st :: _, ⟨h1, h2, h3⟩ => ⟨h1, ⟨H, st.evs, h2⟩, evt009_lrun_xrun h3⟩

omit [DecidableEq N] [Ord N] in
/-- Every step of a labelled run is a step of the executor, given the events emitted before it. -/
theorem evt009_lrun_step {E : EvExec N T} {C : Cfg N T} :
    ∀ {H : List (NetEvent N T)} {s : XSt N T} {run : List (EvStep N T)}, LRun E C H s run →
      ∀ st ∈ run, ∃ H', E.step C H' st.src st.lbl st.evs st.dst
  | _, _, [], _, _, h => absurd h List.not_mem_nil
  | H, _, st :: _, ⟨_, h2, h3⟩, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨H, h2⟩
    · exact evt009_lrun_step h3 x hx

omit [Ord N] in
/-- **AC2** on every labelled run from a state with no ready order left (the initial state, or a
restored marking), for every executor that meets EVT-009, CONC-005's executor companion, CONC-001
and EXEC-003. Say the deadline step reaps `u` and reports it. Then `u` is reaped, so not armed;
until a later step writes one of `u`'s arc places nothing takes it out of the reaped status, no
step starts it, and its enablement stays as it was. -/
@[evidence cites "EVT-009" "AC2: after this event the transition is reaped: it stays enabled but is not armed, and does not fire until one of its arc places is written; on a run from a state with no ready order left, the step of the event leaves the name reaped, only a step that writes one of the transition's arc places ends the reaped state (CONC-005), no step starts the name while it is reaped (EXEC-003 line 1), and a step that writes none of its arc places keeps its enablement (CONC-001, CONC-005)"]
theorem evt009_ac2 {E : EvExec N T} (hE : EVT_009 E) (hW : CONC_005_cycle E.erase)
    (hC : CONC_001 E.erase) (hX : EXEC_003 E.erase) {C : Cfg N T} {H0 : List (NetEvent N T)}
    {s0 : XSt N T} {run : List (EvStep N T)} (h0 : s0.order = []) (hr : LRun E C H0 s0 run)
    {st : EvStep N T} (hst : st ∈ run) {e : NetEvent N T} (he : e ∈ st.evs)
    (hk : e.kind = .transitionTimedOut) :
    ∃ n, e.trans? = some n ∧ st.dst.st n = .reaped ∧
      ∀ u, findT C n = some u → ∀ st' ∈ run,
        (st'.src.st n = .reaped → st'.dst.st n ≠ .reaped →
          ∃ p, ArcPlace u p ∧ conc005StepWrites st'.src st'.lbl p) ∧
        (st'.src.st n = .reaped → ∀ sy, st'.lbl ≠ .start n sy) ∧
        ((∀ p, ArcPlace u p → ¬ conc005StepWrites st'.src st'.lbl p) →
          (Enabled u (qCount st'.dst.M) ↔ Enabled u (qCount st'.src.M))) := by
  obtain ⟨H, hs⟩ := evt009_lrun_step hr st hst
  obtain ⟨n, ht, -, hre⟩ := (hE C).2.2 H st.lbl st.evs st.src st.dst hs e he hk
  refine ⟨n, ht, hre, fun u hu st' hst' => ⟨fun h1 h2 => ?_, fun h1 sy hl => ?_, fun hnw => ?_⟩⟩
  · obtain ⟨-, hname⟩ := findT_spec hu
    subst hname
    exact (hW C u).2.2.1 hu s0 _ h0 (evt009_lrun_xrun hr) _ (List.mem_map_of_mem hst') h1 h2
  · obtain ⟨H', hs'⟩ := evt009_lrun_step hr st' hst'
    have hx : E.erase C st'.src (.start n sy) st'.dst := ⟨H', st'.evs, hl ▸ hs'⟩
    obtain ⟨-, -, -, -, hsome, -⟩ := (hX C).1 n sy _ _ hx
    rw [h1] at hsome
    simp [stampOf] at hsome
  · obtain ⟨H', hs'⟩ := evt009_lrun_step hr st' hst'
    have hx : E.erase C st'.src st'.lbl st'.dst := ⟨H', st'.evs, hs'⟩
    cases hsd : startOrDeposit st'.lbl
    · rw [(hC C).2.1 st'.lbl hsd _ _ hx]
    · exact (hW C u).2.2.2 st'.lbl hsd _ _ hx hnw

omit [Ord N] in
/-- **AC2, enabled**, for every executor that meets EVT-009 and TIME-013's executor companion,
with distinct names: the step that reports `u` timed out leaves `u` reaped and enabled. Only a
deadline step reaps (TIME_013_cycle line 6), it reaps only an expired transition, which is armed,
so enabled, and it does not touch the marking (line 2). -/
@[evidence cites "EVT-009" "AC2: it stays enabled; read with TIME-013's executor companion, the step of the event leaves the transition reaped and enabled, as the deadline step reaps only expired, hence enabled, transitions and keeps the marking"]
theorem evt009_ac2_enabled {E : EvExec N T} (hE : EVT_009 E) (hT : TIME_013_cycle E.erase)
    {C : Cfg N T} (hN : NamesDistinct C.X)
    {H : List (NetEvent N T)} {l : XLbl N T} {evs : List (NetEvent N T)} {s s' : XSt N T}
    (hs : E.step C H s l evs s') {e : NetEvent N T} (he : e ∈ evs)
    (hk : e.kind = .transitionTimedOut) :
    ∃ n u, e.trans? = some n ∧ findT C n = some u ∧ s'.st n = .reaped ∧
      Enabled u (qCount s'.M) := by
  obtain ⟨n, ht, hn, hr⟩ := (hE C).2.2 H l evs s s' hs e he hk
  have hx : E.erase C s l s' := ⟨H, evs, hs⟩
  cases l with
  | deadline ns =>
    obtain ⟨hM, hc⟩ := (hT C).2.1 ns n s s' hx
    obtain ⟨-, u, hu, hname, hexp⟩ := hc (by rw [hr]; exact Ne.symm hn)
    refine ⟨n, u, ht, hname ▸ findT_of_mem hN hu, hr, ?_⟩
    rw [hM]
    exact hexp.2.1.1
  | _ => exact absurd hr ((hT C).2.2.2.2.2 _ n (fun _ h => by cases h) s s' hx hn)

end Consequences

/-! ## The worked example -/

/-- Transition `u`: takes the token of place 0. -/
def evt009_tU : Trans Nat :=
  { core := { name := "u", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- Transition `x`: takes the token of place 1. -/
def evt009_tX : Trans Nat :=
  { core := { name := "x", inputs := [⟨1, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- The configuration of the example: `u` is `Window(3, 5)`, `x` is `Exact(3)`, the tolerance is
1 ms, both of one priority, no environment place, no validation to speak of. -/
def evt009_cfg : Cfg Nat Nat :=
  { X := { net := { places := [0, 1], transitions := [evt009_tU, evt009_tX] },
           timing := fun t => if t.core.name = "u" then .window 3 5 else .exact 3, tol := 1 },
    prio := fun _ => 0, terminals := [], envs := [], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => false,
    res := 0 }

/-- The initial marking: 7 in place 0, 8 in place 1. -/
def evt009_m0 : QMarking Nat Nat := fun p => if p = 0 then [7] else if p = 1 then [8] else []

/-- The names of the example are distinct. -/
theorem evt009_names : NamesDistinct evt009_cfg.X := by unfold NamesDistinct; decide

/-- The first cycle at reading 0 (both armed, neither ready, the pass empty), a wait of 7 ms,
and the second cycle up to its update. -/
def evt009_pre : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin, .endPass,
   .delay 7, .wake, .endCompletions, .endPublications, .endEvents, .update]

/-- The state before the deadline step of the second cycle. -/
def evt009_beforeDeadline : Option (XSt Nat Nat) := xrun evt009_cfg (xinit evt009_m0 0) evt009_pre

/-- The state before `x` starts in the second cycle's pass. -/
def evt009_beforeStart : Option (XSt Nat Nat) :=
  xrun evt009_cfg (xinit evt009_m0 0) (evt009_pre ++ [.deadline ["u"], .begin])

/-- ✓ Both lines of the first block are exercised by the reference, on `u` (`Window(3, 5)`) and `x`
(`Exact(3)`) armed at reading 0 with tolerance 1: at reading 7 the deadline step reaps `u`, which
was armed, and emits exactly one `TransitionTimedOut`, naming `u`; `x` is past its target too, is
not reaped, and its start emits no `TransitionTimedOut`; the boot of the run emits events (the
`ExecutionStarted` and the snapshot), none a `TransitionTimedOut`. -/
@[evidence nonvacuous EVT_009]
theorem EVT_009_nonvacuous :
    (∃ s s' evs, (refEvExec polJT).step evt009_cfg [] s (.deadline ["u"]) evs s' ∧
      s.st "u" ≠ .reaped ∧ s'.st "u" = .reaped ∧ timedOutCount evs "u" = 1 ∧
      kindCount .transitionTimedOut evs = 1 ∧ s'.st "x" ≠ .reaped) ∧
    (∃ s s' evs, (refEvExec polJT).step evt009_cfg [] s (.start "x" false) evs s' ∧ evs ≠ [] ∧
      ∀ e ∈ evs, e.kind ≠ .transitionTimedOut) ∧
    ((refEvExec (N := Nat) (T := Nat) polJT).boot evt009_cfg evt009_m0 ≠ [] ∧
      ∀ e ∈ (refEvExec (N := Nat) (T := Nat) polJT).boot evt009_cfg evt009_m0,
        e.kind ≠ .transitionTimedOut) := by
  refine ⟨?_, ?_, by decide +kernel⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt009_cfg) (o := evt009_beforeDeadline)
      (l := .deadline ["u"])
      (p := fun s s' =>
        let evs := refEmitW polJT evt009_cfg [] s (.deadline ["u"]) s'
        decide (s.st "u" ≠ .reaped) && decide (s'.st "u" = .reaped) &&
          timedOutCount evs "u" == 1 && kindCount .transitionTimedOut evs == 1 &&
          decide (s'.st "x" ≠ .reaped))
      (by decide +kernel)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hp
    exact ⟨s, s', _, ⟨hs, rfl⟩, h1, h2, h3, h4, h5⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt009_cfg) (o := evt009_beforeStart)
      (l := .start "x" false)
      (p := fun s s' =>
        let evs := refEmitW polJT evt009_cfg [] s (.start "x" false) s'
        !evs.isEmpty && evs.all fun e => e.kind != .transitionTimedOut)
      (by decide +kernel)
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
      List.all_eq_true, bne_iff_ne, ne_eq] at hp
    exact ⟨s, s', _, ⟨hs, rfl⟩, hp.1, hp.2⟩

/-- ✓ The payload line is exercised by the reference: the deadline step at reading 7 reports `u`
with deadline 5 (its latest bound, the tolerance 1 left out) and elapsed time 7 (armed at 0). -/
@[evidence nonvacuous EVT_009_payload]
theorem EVT_009_payload_nonvacuous :
    ∃ s s' evs, (refEvExec polJT).step evt009_cfg [] s (.deadline ["u"]) evs s' ∧
      evs = [.transitionTimedOut "u" 5 7] := by
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt009_cfg) (o := evt009_beforeDeadline)
    (l := .deadline ["u"])
    (p := fun s s' => refEmitW polJT evt009_cfg [] s (.deadline ["u"]) s' ==
      [.transitionTimedOut "u" 5 7])
    (by decide +kernel)
  simp only [beq_iff_eq] at hp
  exact ⟨s, s', _, ⟨hs, rfl⟩, hp⟩

/-- The configuration of the markdown's test derivation: `u` is `Deadline(5)`, `x` is `Exact(3)`,
the tolerance is 1 ms, otherwise as `evt009_cfg`. -/
def evt009_cfgD : Cfg Nat Nat :=
  { X := { net := { places := [0, 1], transitions := [evt009_tU, evt009_tX] },
           timing := fun t => if t.core.name = "u" then .deadline 5 else .exact 3, tol := 1 },
    prio := fun _ => 0, terminals := [], envs := [], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => false,
    res := 0 }

/-- The first cycle up to its update at reading 0, then a delay of 7 ms before the deadline step:
the host is held up between the update and the deadline step, so `u` does not fire. -/
def evt009_beforeDeadlineD : Option (XSt Nat Nat) :=
  xrun evt009_cfgD (xinit evt009_m0 0)
    [.endCompletions, .endPublications, .endEvents, .update, .delay 7]

/-- ✓ The test derivation, in milliseconds: `u` is `Deadline(5)` with tolerance 1. The update at
reading 0 arms it, the host is held up until reading 7, and the deadline step then reaps `u` and
emits exactly one event, `TransitionTimedOut` for `u` with deadline 5 and elapsed time 7. The
elapsed time is measured at the deadline step's reading 7, not at the update's reading 0. -/
@[evidence nonvacuous EVT_009 EVT_009_payload]
theorem EVT_009_nonvacuous_deadline :
    ∃ s s' evs, (refEvExec polJT).step evt009_cfgD [] s (.deadline ["u"]) evs s' ∧
      s.cyc = 0 ∧ s'.cyc = 7 ∧ s.st "u" ≠ .reaped ∧ s'.st "u" = .reaped ∧
      evs = [.transitionTimedOut "u" 5 7] := by
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt009_cfgD) (o := evt009_beforeDeadlineD)
    (l := .deadline ["u"])
    (p := fun s s' => s.cyc == 0 && s'.cyc == 7 && decide (s.st "u" ≠ .reaped) &&
      decide (s'.st "u" = .reaped) &&
      refEmitW polJT evt009_cfgD [] s (.deadline ["u"]) s' == [.transitionTimedOut "u" 5 7])
    (by decide +kernel)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hp
  exact ⟨s, s', _, ⟨hs, rfl⟩, h1, h2, h3, h4, h5⟩

/-! ## Wrong executors: the reference's steps, another emission -/

section Mutants

variable {N T : Type} [DecidableEq N] [Ord N]
/-- The Java and TypeScript emission with the events of a deadline step replaced by `f C s ns`. -/
def evt009_atDeadline (f : Cfg N T → XSt N T → List String → List (NetEvent N T))
    (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T) (l : XLbl N T) (s' : XSt N T) :
    List (NetEvent N T) :=
  match l with
  | .deadline ns => f C s ns
  | _ => refEmitW polJT C H s l s'

/-- Away from a deadline step, `evt009_atDeadline` emits as the reference. -/
theorem evt009_atDeadline_other (f : Cfg N T → XSt N T → List String → List (NetEvent N T))
    (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T) {l : XLbl N T}
    (hl : ∀ ns, l ≠ .deadline ns) (s' : XSt N T) :
    evt009_atDeadline f C H s l s' = refEmitW polJT C H s l s' := by
  cases l with
  | deadline ns => exact absurd rfl (hl ns)
  | _ => rfl

/-- The executor that reaps silently: its deadline step emits nothing. -/
def evt009_silentReap : EvExec N T :=
  emitExec (refBoot polJT) (evt009_atDeadline fun _ _ _ => [])

/-- The executor that reports a reap as an `ActionTimedOut`, the event of an action's
`Out.Timeout`. -/
def evt009_asActionTimedOut : EvExec N T :=
  emitExec (refBoot polJT) (evt009_atDeadline fun C _ ns =>
    ns.filterMap fun m => (findT C m).map fun _ => .actionTimedOut m)

/-- The executor whose deadline field adds the tolerance to the latest bound. -/
def evt009_plusTol : EvExec N T :=
  emitExec (refBoot polJT) (evt009_atDeadline
    (evt009_deadlineEvs (fun C _ u => (C.X.timing u).latest + C.X.tol) evt009_refEl))

/-- The start events of the reference, followed by a `TransitionTimedOut` for the started
transition when its elapsed time at the cycle reading is past its latest bound plus the
tolerance (AC1 read alone: an `Exact` transition started past its target reported as timed
out). -/
def evt009_lateStartEmit (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T) (l : XLbl N T)
    (s' : XSt N T) : List (NetEvent N T) :=
  match l with
  | .start n _ =>
    refEmitW polJT C H s l s' ++
      match findT C n with
      | some u =>
        if (C.X.timing u).latest + C.X.tol < (viewAt s s.cyc).elapsed u
        then [.transitionTimedOut n (C.X.timing u).latest ((viewAt s s.cyc).elapsed u)] else []
      | none => []
  | _ => refEmitW polJT C H s l s'

/-- The executor that reports a transition started past its latest bound plus the tolerance as
timed out. -/
def evt009_onLateStart : EvExec N T := emitExec (refBoot polJT) evt009_lateStartEmit

/-- The Java and TypeScript boot events followed by one `TransitionTimedOut` per reapable
transition of the net. -/
def evt009_bootEvs (C : Cfg N T) (M0 : QMarking N T) : List (NetEvent N T) :=
  refBoot polJT C M0 ++ (C.X.net.transitions.filter fun u => (C.X.timing u).reapable).map
    fun u => .transitionTimedOut u.core.name (C.X.timing u).latest 0

/-- The executor that reports a `TransitionTimedOut` at boot. -/
def evt009_atBoot : EvExec N T := emitExec evt009_bootEvs (refEmitW polJT)

/-- A silent reap keeps line 2: it emits no `TransitionTimedOut` at all. -/
theorem evt009_silentReap_line2 : evt009_line2 (evt009_silentReap (N := N) (T := T)) :=
  evt009_line2_of (refBoot_noTimedOut polJT)
    (fun C H s l s' hl => by
      rw [evt009_atDeadline_other _ C H s hl s']; exact refEmitW_noTimedOut polJT C H s hl s')
    (fun _ _ _ _ _ e he _ => by simp [evt009_atDeadline] at he)

/-- Reporting a transition started late keeps line 1: its deadline steps emit as the
reference. -/
theorem evt009_onLateStart_line1 : evt009_line1 (evt009_onLateStart (N := N) (T := T)) :=
  evt009_line1_of evt009_refDl evt009_refEl (fun _ _ _ _ _ => rfl)

/-- Adding the tolerance to the deadline field keeps the first block: kinds and names are
unchanged. -/
theorem evt009_plusTol_meets : EVT_009 (evt009_plusTol (N := N) (T := T)) :=
  (evt009_iff _).2
    ⟨evt009_line1_of _ _ (fun _ _ _ _ _ => rfl),
     evt009_line2_of (refBoot_noTimedOut polJT)
       (fun C H s l s' hl => by
         rw [evt009_atDeadline_other _ C H s hl s']; exact refEmitW_noTimedOut polJT C H s hl s')
       (fun C _ s ns _ e he hk =>
         deadlineEvs_names (dl := fun C _ u => (C.X.timing u).latest + C.X.tol)
           (el := evt009_refEl) (C := C) (s := s) (ns := ns) e he hk)⟩

/-- The elapsed field read at the update's reading (the cycle reading before the deadline step),
while the reap is judged at the deadline step's reading. -/
def evt009_updEl (_C : Cfg N T) (s : XSt N T) (u : Trans N) : Nat := (viewAt s s.cyc).elapsed u

/-- The executor whose elapsed field is read at the update's reading. -/
def evt009_updateReading : EvExec N T :=
  emitExec (refBoot polJT) (evt009_atDeadline (evt009_deadlineEvs evt009_refDl evt009_updEl))

/-- Reading the elapsed field at the update's reading keeps the first block: kinds and names are
unchanged. -/
theorem evt009_updateReading_meets : EVT_009 (evt009_updateReading (N := N) (T := T)) :=
  (evt009_iff _).2
    ⟨evt009_line1_of _ _ (fun _ _ _ _ _ => rfl),
     evt009_line2_of (refBoot_noTimedOut polJT)
       (fun C H s l s' hl => by
         rw [evt009_atDeadline_other _ C H s hl s']; exact refEmitW_noTimedOut polJT C H s hl s')
       (fun C _ s ns _ e he hk =>
         deadlineEvs_names (dl := evt009_refDl) (el := evt009_updEl) (C := C) (s := s) (ns := ns)
           e he hk)⟩

/-- The deadline step's target with the names of `ns` left off instead of reaped. -/
def evt009_disarm (ns : List String) (s : XSt N T) : XSt N T :=
  { s with st := fun n => if ns.contains n then .off else s.st n }

/-- The steps of the executor that disarms instead of reaping and reports nothing: its deadline
step leaves the names it should reap off and emits no event; every other step is the
reference's. -/
def evt009_disarmSilentStep : XEvRel N T := fun C H s l evs s' =>
  match l with
  | .deadline ns => ∃ s1, xstep C s (.deadline ns) = some s1 ∧ s' = evt009_disarm ns s1 ∧ evs = []
  | l => (refEvExec polJT).step C H s l evs s'

/-- The executor that disarms an expired transition to off instead of reaping it, and reports
nothing. -/
def evt009_disarmSilent : EvExec N T := { boot := refBoot polJT, step := evt009_disarmSilentStep }

/-- `EVT_009` alone accepts the silent disarm: no step takes a name to the reaped status (its
deadline step leaves its names off, and its other steps are the reference's, which reap only at a
deadline step), and no step emits a `TransitionTimedOut`. -/
theorem evt009_disarmSilent_meets : EVT_009 (evt009_disarmSilent (N := N) (T := T)) := by
  intro C
  refine ⟨fun _ H l evs n s s' hs hn hr => ?_, refBoot_noTimedOut polJT C,
    fun H l evs s s' hs e he hk => ?_⟩
  · cases l with
    | deadline ns =>
      obtain ⟨s1, hx, rfl, -⟩ := hs
      obtain ⟨-, -, -, rfl⟩ := xstepW_deadline (P := refXPol) hx
      simp only [evt009_disarm] at hr
      split at hr
      · cases hr
      · simp_all
    | _ =>
      obtain ⟨hx, -⟩ := hs
      rcases reaped_origin (P := refXPol) hx hr with h | ⟨⟨ns, h⟩, -⟩
      · exact absurd h hn
      · cases h
  · cases l with
    | deadline ns =>
      obtain ⟨s1, -, -, rfl⟩ := hs
      simp at he
    | _ =>
      obtain ⟨-, rfl⟩ := hs
      exact absurd hk (refEmitW_noTimedOut polJT C H s (fun _ h => by cases h) s' e he)

end Mutants

/-- ✗ Reaping silently violates EVT-009 (line 1): at reading 7 the deadline step reaps `u`, which
was armed, and emits no `TransitionTimedOut`. The executor keeps line 2. -/
@[evidence mutant EVT_009]
theorem EVT_009_mutant_silentReap :
    evt009_line2 (evt009_silentReap (N := Nat) (T := Nat)) ∧
      ¬ EVT_009 (evt009_silentReap (N := Nat) (T := Nat)) := by
  refine ⟨evt009_silentReap_line2, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt009_cfg) (o := evt009_beforeDeadline)
    (l := .deadline ["u"])
    (p := fun s s' => decide (s.st "u" ≠ .reaped) && decide (s'.st "u" = .reaped))
    (by decide +kernel)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  have := (h evt009_cfg).1 evt009_names [] _ _ "u" s s' ⟨hs, rfl⟩ hp.1 hp.2
  simp [evt009_atDeadline, timedOutCount] at this

/-- ✗ Reporting a reap as an `ActionTimedOut` violates EVT-009 (line 1): at reading 7 the deadline
step reaps `u` and emits an `ActionTimedOut` naming `u`, which is the event of an action's
timeout, and no `TransitionTimedOut`. -/
@[evidence forbids EVT_009]
theorem EVT_009_forbids_asActionTimedOut :
    ¬ EVT_009 (evt009_asActionTimedOut (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt009_cfg) (o := evt009_beforeDeadline)
    (l := .deadline ["u"])
    (p := fun s s' => decide (s.st "u" ≠ .reaped) && decide (s'.st "u" = .reaped) &&
      timedOutCount (evt009_atDeadline (fun C _ ns => ns.filterMap fun m =>
        (findT C m).map fun _ => (NetEvent.actionTimedOut m : NetEvent Nat Nat))
        evt009_cfg [] s (.deadline ["u"]) s') "u" == 0)
    (by decide +kernel)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
  have := (h evt009_cfg).1 evt009_names [] _ _ "u" s s' ⟨hs, rfl⟩ hp.1.1 hp.1.2
  rw [hp.2] at this
  exact absurd this (by decide)

/-- ✗ Reporting an `Exact` transition started past its target as timed out violates EVT-009
(line 2): `x`, `Exact(3)` armed at 0 with tolerance 1, starts at reading 7 (elapsed 7, past 3 + 1)
and its start emits a `TransitionTimedOut` naming `x`, which no step reaped. Its deadline steps
emit as the reference, so it keeps line 1. -/
@[evidence mutant EVT_009]
theorem EVT_009_mutant_onLateStart :
    evt009_line1 (evt009_onLateStart (N := Nat) (T := Nat)) ∧
      ¬ EVT_009 (evt009_onLateStart (N := Nat) (T := Nat)) := by
  refine ⟨evt009_onLateStart_line1, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt009_cfg) (o := evt009_beforeStart)
    (l := .start "x" false)
    (p := fun s s' => decide (NetEvent.transitionTimedOut "x" 3 7 ∈
        evt009_lateStartEmit evt009_cfg [] s (.start "x" false) s') &&
      decide (s'.st "x" ≠ .reaped))
    (by decide +kernel)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨n, ht, -, hr⟩ := (h evt009_cfg).2.2 [] _ _ s s' ⟨hs, rfl⟩ _ hp.1 rfl
  simp only [NetEvent.trans?, Option.some.injEq] at ht
  subst ht
  exact hp.2 hr

/-- ✗ Reporting a `TransitionTimedOut` at boot violates EVT-009 (line 2): the run of the example
reports `u` as timed out before its first step, before any clock has run. -/
@[evidence forbids EVT_009]
theorem EVT_009_forbids_atBoot : ¬ EVT_009 (evt009_atBoot (N := Nat) (T := Nat)) := by
  intro h
  have hm : NetEvent.transitionTimedOut "u" 5 0 ∈ evt009_atBoot.boot evt009_cfg evt009_m0 := by
    decide +kernel
  exact (h evt009_cfg).2.1 evt009_m0 _ hm rfl

/-- ✗ Adding the tolerance to the deadline field meets the first block (the right event at the
right step) and violates the payload companion: at reading 7 the reap of `u`, `Window(3, 5)`
with tolerance 1, reports deadline 6 instead of its latest bound 5. -/
@[evidence mutant EVT_009_payload]
theorem EVT_009_payload_mutant_plusTol :
    EVT_009 (evt009_plusTol (N := Nat) (T := Nat)) ∧
      ¬ EVT_009_payload (evt009_plusTol (N := Nat) (T := Nat)) := by
  refine ⟨evt009_plusTol_meets, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt009_cfg) (o := evt009_beforeDeadline)
    (l := .deadline ["u"])
    (p := fun s s' => decide (NetEvent.transitionTimedOut "u" 6 7 ∈
      evt009_atDeadline (evt009_deadlineEvs (fun C _ u => (C.X.timing u).latest + C.X.tol)
        evt009_refEl) evt009_cfg [] s (.deadline ["u"]) s'))
    (by decide +kernel)
  simp only [decide_eq_true_eq] at hp
  obtain ⟨u, hu, hd, -⟩ := h evt009_cfg [] _ _ s s' ⟨hs, rfl⟩ "u" 6 7 hp
  have hf : findT evt009_cfg "u" = some evt009_tU := by rfl
  rw [hf, Option.some.injEq] at hu
  subst hu
  revert hd; decide

/-- ✗ Reading the elapsed field at the update's reading meets the first block (the right event at
the right step) and violates the payload companion: `u`, `Deadline(5)`, is armed by the update at
reading 0, and the deadline step at reading 7 reaps it but reports elapsed time 0, the update's
reading, where the transition's elapsed time at the deadline step's reading is 7. -/
@[evidence mutant EVT_009_payload]
theorem EVT_009_payload_mutant_updateReading :
    EVT_009 (evt009_updateReading (N := Nat) (T := Nat)) ∧
      ¬ EVT_009_payload (evt009_updateReading (N := Nat) (T := Nat)) := by
  refine ⟨evt009_updateReading_meets, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt009_cfgD) (o := evt009_beforeDeadlineD)
    (l := .deadline ["u"])
    (p := fun s s' => decide (NetEvent.transitionTimedOut "u" 5 0 ∈
        evt009_atDeadline (evt009_deadlineEvs evt009_refDl evt009_updEl) evt009_cfgD [] s
          (.deadline ["u"]) s') &&
      Elapsed (viewAt s s'.cyc) evt009_tU == 7)
    (by decide +kernel)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
  obtain ⟨u, hu, -, hel⟩ := h evt009_cfgD [] _ _ s s' ⟨hs, rfl⟩ "u" 5 0 hp.1
  have hf : findT evt009_cfgD "u" = some evt009_tU := by rfl
  rw [hf, Option.some.injEq] at hu
  subst hu
  rw [hp.2] at hel
  exact absurd hel (by decide)

/-- EVT-009 needs TIME-013 for AC1 and AC2. An executor whose deadline step leaves the expired
`u` off instead of reaped, and reports nothing, meets `EVT_009` (it reaps nothing, so it owes no
event), but at reading 7 `u` (`Window(3, 5)`, tolerance 1, armed at 0) is expired and not reaped,
which TIME-013's executor companion forbids. -/
@[evidence cites "EVT-009" "AC1 and AC2: the transition is reaped when its elapsed time is past the bound plus the tolerance; EVT-009 alone accepts an executor that disarms the expired transition to off and reports nothing, and TIME-013's executor companion rejects it, so AC1 and AC2 are read with it"]
theorem evt009_disarmSilent_needs_time013 :
    EVT_009 (evt009_disarmSilent (N := Nat) (T := Nat)) ∧
      ¬ TIME_013_cycle (evt009_disarmSilent (N := Nat) (T := Nat)).erase := by
  refine ⟨evt009_disarmSilent_meets, fun h => ?_⟩
  obtain ⟨s, s1, -, hs, hp⟩ := step_of_check xstep (C := evt009_cfg) (o := evt009_beforeDeadline)
    (l := .deadline ["u"])
    (p := fun s s1 => decide (Expired evt009_cfg.X (viewAt s s1.cyc) evt009_tU))
    (by decide +kernel)
  simp only [decide_eq_true_eq] at hp
  have hr := (h evt009_cfg).1 ["u"] evt009_tU List.mem_cons_self s (evt009_disarm ["u"] s1)
    ⟨[], [], s1, hs, rfl, rfl⟩ (by simpa [evt009_disarm] using hp)
  simp [evt009_disarm, evt009_tU] at hr

end Libpetri.Spec
