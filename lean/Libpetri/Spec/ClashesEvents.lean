import Libpetri.Spec.Req.EVT_003
import Libpetri.Spec.Req.EVT_004
import Libpetri.Spec.Req.EVT_007
import Libpetri.Spec.Req.EVT_008
import Libpetri.Spec.Req.EVT_010
import Libpetri.Spec.Req.EVT_011
import Libpetri.Spec.Req.EVT_032
import Libpetri.Spec.Req.EXEC_042
import Libpetri.Reference.EventsLink

set_option linter.missingDocs true

/-!
# The event clashes (EVT-001 to EVT-032), after the rulings

The confirmed clashes of plan section 6 that touch an executor event requirement and need a
theorem of their own in wave W7, stated over the reference executor with events `refEvExec`
(`Reference/Events.lean`) under its two emission variants (`polJT` for Java and TypeScript,
`polRust` for Rust and Python), and over the replay of `Reference/Replay.lean`. Every ruling is
decided (plan section 5, accepted 2026-11-10); each theorem below records the evidence for the
decided reading, never a reading the user rejected.

A rejected reading is a plain definition over an abstract executor with events
`V : EvExec N T`, not a requirement block (as in `ClashesExec.lean`): the registry's `conflict`
and `ambiguity` roles name requirement blocks only. So the evidence is a citation of the spec ID
whose text had the two readings, stated against the blocks of the decided reading (EVT-003,
EVT-007, EVT-010 and the others named below); where the theorem also shows those blocks holding
together, it is `consistent` evidence for them as well.

| Clash | Ruling | Evidence here |
|---|---|---|
| evt-a#3 (EVT-003 AC1 'after all transitions complete' against EXEC-042) | D74 (a) | `clashEvt_endMarker`: no executor with events meets EXEC-041 and EVT-003, offers the terminal stop at once (EXEC-042's coverage) and reports `ExecutionCompleted` only with nothing in flight; the reference meets all but the last |
| evt-a#7, evt-b#2, exec#13 (`TransitionCompleted` after a timeout outcome) | D65 (a) | `clashEvt_completedAfterTimeout`: the Java and TypeScript emission reports it at every deposit of a timeout outcome, the Rust emission at none, and both meet EVT-007, EVT-008 and EVT-011 |
| evt-b#9, exec#13 (`ActionTimedOut` after `ExecutionCompleted`) | D65 (a) | `clashEvt_lateActionTimedOut`: on a run that stops on a terminal place while a firing with a `Timeout` node is in flight, the Java and TypeScript emission reports that firing's `ActionTimedOut` after `ExecutionCompleted`, the Rust emission reports nothing after it, and both meet EVT-003 and EVT-010 |
| evt-b#1 (`TokenAdded` for the initial marking) | D76 (a) | `clashEvt_initialAdded`: no executor with events meets EVT-011 and reports every token of the initial marking as added; the reference meets EVT-011, and the boot that reports them meets the old reading |
| evt-c#10 (the replay's enabled set) | D83 (a) | `clashEvt_replayEnabled`: on a reference run where two transitions compete for one token, the replay of the events lists the loser as enabled after the run disarmed it and emptied its input place, while the reference meets EVT-004 and the replay cache meets EVT-032 |

Not here:

* Clashes whose evidence is a line or a theorem of an existing block: evt-a#1 (ruling D5; EVT-004
  reads armed, `EVT_004_mutant_silentSelf`), evt-a#2 and evt-a#15 (ruling D5; EVT-005 and
  `evt005_one_of`), evt-a#5 and events SC-7 (ruling D98; `EVT_002_executionId` and
  `EVT_002_lifecycleId`), evt-a#8 (ruling D38; `EVT_006_payload`, inputs then resets), evt-a#10,
  evt-b#3 (ruling D38; the main and companion blocks), evt-a#11 (ruled D17; EVT-008), evt-b#8
  (ruled D5; `evt009_ac1`), evt-b#6 and evt-c#1 (ruling D29; EVT-020 and `EVT_021_allows_live`,
  the live store), and the store-tier clashes evt-c#2 to evt-c#9 and evt-c#11 to evt-c#16 (rulings
  D29, D83, D86; the blocks EVT-020 to EVT-032 of wave W6, and `replay_no_initial` for evt-c#11).
* Clashes whose evidence is a line of another block of this wave: evt-a#4 (ruling D38, durations
  as bounds) in the EVT-003 and EVT-007 companions; evt-a#14 (ruled D17) in EVT-007
  (`EVT_007_allows_publishedAfter`); evt-b#4 and evt-b#5 (D20) in EVT-013; evt-b#10 and events
  SC-6 (D38, D20) in EVT-014; evt-b#13 (ruling D18 (b)) in EVT-010, which has no time clause; the
  TIME-006 deferral (D38) to a link line.
* Editorial clashes with no change of behaviour (D20): evt-a#6, evt-a#9, evt-b#7 and events
  SC-10 (the IO-013 assumes text, fixed by the integrator), evt-b#11, evt-b#12, events SC-3.
* evt-a#12 (ruling D8 (b)): every line of the existing event blocks holds for every configuration,
  re-entrant or not; evt-a#13 (ruling D66 (a)): EVT-001 has no block, the TypeScript array shared
  with the event is an implementation-status note.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

namespace ClashEvt

variable {N T : Type}

/-! ## Candidate readings -/

/-- **EVT-003 AC1 read literally** (not a requirement block): a step reports
`ExecutionCompleted` only when no firing is in flight ("after all transitions complete"). -/
def CompletedWhenIdle (V : EvExec N T) : Prop :=
  ∀ C H s l evs s', V.step C H s l evs s' → evs.any (·.kind == .executionCompleted) = true →
    s.fl = []

/-- The events of a trace after its first `ExecutionCompleted` (none when it has none). -/
def afterCompleted : List (NetEvent N T) → List (NetEvent N T)
  | [] => []
  | e :: r => if e.kind = .executionCompleted then r else afterCompleted r

/-- **`ExecutionCompleted` read as the last event of every trace** (not a requirement block). -/
def EndsAtCompleted (V : EvExec N T) : Prop :=
  ∀ C M0 r0 tr, Trace V C M0 r0 tr → afterCompleted tr = []

/-- **The old EVT-011 clause 'whether from initial marking'** (not a requirement block): the boot
of a run reports every token of the initial marking on a declared place as added. -/
def ReportsInitial (V : EvExec N T) : Prop :=
  ∀ C M0 p x, p ∈ C.X.net.places → x ∈ M0 p →
    (NetEvent.tokenAdded p x : NetEvent N T) ∈ V.boot C M0

/-! ## The reference against the readings -/

/-- A decided fact about an optional value yields the value. -/
theorem some_of_map {α : Type} {o : Option α} {q : α → Bool} (h : o.map q = some true) :
    ∃ a, o = some a ∧ q a = true := by
  cases o with
  | none => simp at h
  | some a => exact ⟨a, rfl, by simpa using h⟩

variable [DecidableEq N] [Ord N]
/-- Under the Java and TypeScript emission every deposit of a timeout outcome reports a
`TransitionCompleted`. -/
theorem ref_completesTimeout (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T) (i : Nat)
    (s' : XSt N T) (hs : xstep C s (.tdeposit i) = some s') :
    ∃ e ∈ refEmitW polJT C H s (.tdeposit i) s', e.kind = .transitionCompleted := by
  obtain ⟨f, e, hf, ho, -⟩ := tdepositStep_some (C := C) (s := s) (s' := s') (i := i) hs
  refine ⟨.transitionCompleted f.t.core.name e (s.now - f.start), ?_, rfl⟩
  simp [refEmitW, hf, ho, polJT]

/-- Under the Rust emission no deposit of a timeout outcome reports a `TransitionCompleted`. -/
theorem ref_silentTimeout (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T) (i : Nat)
    (s' : XSt N T) : ∀ e ∈ refEmitW polRust C H s (.tdeposit i) s', e.kind ≠ .transitionCompleted := by
  intro e he hk
  simp only [refEmitW] at he
  split at he
  · split at he
    · simp only [polRust, Bool.false_eq_true, ite_false, List.append_nil,
        List.mem_append, List.mem_singleton] at he
      rcases he with rfl | h
      · cases hk
      · rw [kind_of_mem_addedEvs h] at hk; cases hk
    · cases he
  · cases he

/-- The boot that reports the initial marking as added (`evt011_bootAdded`, EVT-011's mutant)
meets the old reading. -/
theorem bootAdded_reports : ReportsInitial (evt011_bootAdded (N := N) (T := T)) := by
  intro C M0 p x hp hx
  show _ ∈ evt011_bootAddedEvs C M0
  simp only [evt011_bootAddedEvs, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_dedup]
  exact Or.inr ⟨p, hp, x, hx, rfl⟩

/-! ## A run that stops on a terminal place with a firing in flight

Places 0, 1, 2 and 9; place 9 is terminal. Transition `a` takes the token of place 0 and has
output `Place 9`; transition `b` takes the token of place 1 and has output
`Xor(Place 2, Timeout(d, Place 2))`, so its action has a budget. Both are immediate with one
priority, so the ready order is `a` before `b`. -/

/-- Transition `a`: one token from 0, output `Place 9`. -/
def cevA : Trans Nat :=
  { core := { name := "a", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 9) }

/-- Transition `b`: one token from 1, output `Xor(Place 2, Timeout(d, Place 2))`. -/
def cevB : Trans Nat :=
  { core := { name := "b", inputs := [⟨1, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.xor (.place 2) (.timeout (.place 2))) }

/-- The configuration: terminal place 9, every output valid, every timeout outcome possible. -/
def cevC : Cfg Nat Nat :=
  { X := { net := { places := [0, 1, 2, 9], transitions := [cevA, cevB] },
           timing := fun _ => .immediate, tol := 0 },
    prio := fun _ => 0, terminals := [9], envs := [], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true,
    timeoutOut := fun _ _ _ => true, res := 0 }

/-- The initial marking: 7 in place 0, 8 in place 1. -/
def cevM : QMarking Nat Nat := fun p => if p = 0 then [7] else if p = 1 then [8] else []

/-- One cycle: `a` and `b` start asynchronously; `a` writes 5 into place 9 and returns, and the
loop settles it, which marks the terminal place while `b` is in flight. -/
def cevStop : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin,
   .start "a" false, .start "b" false, .endPass, .write 0 9 5, .ret 0 true, .commit 0]

/-- The same run up to the terminal stop, then `b`'s budget expires with outcome 8 in place 2. -/
def cevLate : List (XLbl Nat Nat) := cevStop ++ [.finish .terminal, .expire 1 [(2, 8)]]

/-- Only 8 in place 1: `b` alone. -/
def cevMB : QMarking Nat Nat := fun p => if p = 1 then [8] else []

/-- `b` starts asynchronously and its budget expires with outcome 8 in place 2; the loop may then
deposit the timeout outcome. -/
def cevTimeout : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin,
   .start "b" false, .endPass, .expire 0 [(2, 8)]]

/-- After `a`'s completion is settled the terminal place 9 is marked, the loop is still running,
and `b` is in flight. -/
theorem cev_stopInFlight :
    ∃ s, xrun cevC (xinit cevM 0) cevStop = some s ∧ ¬ Live cevC s ∧
      isExecPhase s.phase = true ∧ s.fl ≠ [] := by
  obtain ⟨s, hs, hq⟩ := some_of_map (o := xrun cevC (xinit cevM 0) cevStop)
    (q := fun s => !liveB cevC s && isExecPhase s.phase && !s.fl.isEmpty) (by decide +kernel)
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hq
  exact ⟨s, hs, by simp [Live, hq.1.1], hq.1.2, hq.2⟩

/-- A deposit of a timeout outcome is a step of the reference: `b`'s budget expired with outcome
8 in place 2. -/
theorem cev_tdeposit : ∃ s s', RefExec cevC s (.tdeposit 0) s' := by
  obtain ⟨s, s', -, hs, -⟩ := step_of_check xstep (C := cevC)
    (o := xrun cevC (xinit cevMB 0) cevTimeout) (l := .tdeposit 0) (p := fun _ _ => true)
    (by decide +kernel)
  exact ⟨s, s', hs⟩

/-! ## A run in which two transitions compete for one token -/

/-- `T1`: takes the token of place 0. -/
def cevT1 : Trans Nat :=
  { core := { name := "T1", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- `T2`: takes the token of place 0. -/
def cevT2 : Trans Nat :=
  { core := { name := "T2", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- Two immediate transitions competing for place 0, `T1` first in the ready order. -/
def cevC2 : Cfg Nat Nat :=
  { X := { net := { places := [0], transitions := [cevT1, cevT2] },
           timing := fun _ => .immediate, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true,
    timeoutOut := fun _ _ _ => false, res := 0 }

/-- One token in place 0. -/
def cevM2 : QMarking Nat Nat := fun p => if p = 0 then [1] else []

/-- The update arms both; `T1` starts and takes the token; `T2`, next in the order, can no longer
start and loses its clock; the pass ends. -/
def cevLose : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin,
   .start "T1" false, .lose "T2", .endPass]

end ClashEvt

open ClashEvt

/-! ## evt-a#3: the end-of-run marker (ruling D74 (a)) -/

/-- The conflict of clash evt-a#3: no executor with events meets EXEC-041 and EVT-003, offers
the terminal stop at once from every running state with a marked terminal place ([EXEC-042]'s
coverage conjunct `Exec042Covers`) and reports `ExecutionCompleted` only with nothing in flight.
On the run `cevStop` place 9 is marked while `b` is in flight; the stop is offered there, it
leaves the loop (EXEC-041), so EVT-003 makes it report `ExecutionCompleted`, with `b` still in
flight. -/
theorem clashEvt_endMarker_conflict :
    ¬ ∃ V : EvExec Nat Nat, EXEC_041 V.erase ∧ Exec042Covers V.erase ∧ EVT_003 V ∧
      CompletedWhenIdle V := by
  rintro ⟨V, h41, hcov, h3, hidle⟩
  obtain ⟨s, -, hL, hp, hfl⟩ := cev_stopInFlight
  obtain ⟨s', H, evs, hs⟩ := hcov cevC s hL hp
  have hph : s'.phase = .done .terminal := ((h41 cevC).1 .terminal s s' ⟨H, evs, hs⟩).2
  have hc := (h3 cevC).1.2 H (.finish .terminal) evs s s' hs
  dsimp only at hc
  rw [show (isExecPhase s.phase && !isExecPhase s'.phase) = true by rw [hp, hph]; rfl,
    if_pos rfl] at hc
  simp only [kindCount] at hc
  have hpos : 0 < evs.countP (fun e => e.kind == .executionCompleted) := by omega
  obtain ⟨e, he, hk⟩ := List.countP_pos_iff.1 hpos
  exact hfl (hidle _ _ _ _ _ _ hs (List.any_eq_true.2 ⟨e, he, hk⟩))

/-- ✗ **evt-a#3, ruling D74 (a): `ExecutionCompleted` ends every run, and only a quiescent end has
nothing in flight.** Worked example: `a` and `b` start, `a` returns and its token marks the
terminal place 9 while `b` is still running. The run stops at once (EXEC-042), and that stop
reports `ExecutionCompleted` (EVT-003) with `b` in flight, so "after all transitions complete"
cannot be kept together with the terminal stop. The reference, under both emissions, meets
EXEC-041, EXEC-042 and its coverage conjunct, and EVT-003; it breaks the literal reading. -/
@[evidence cites "EVT-003" "ExecutionCompleted is emitted at most once per run, when the loop ends, after its last orchestrator event; 'nothing in flight' holds only for the quiescent end (ruling D74 (a)): when a terminal place is marked while another firing is in flight the run stops at once (EXEC-042) and reports ExecutionCompleted with that firing still in flight, so 'after all transitions complete' cannot hold together with the terminal stop", evidence consistent EVT_003 EXEC_041 EXEC_042]
theorem clashEvt_endMarker :
    (¬ ∃ V : EvExec Nat Nat, EXEC_041 V.erase ∧ Exec042Covers V.erase ∧ EVT_003 V ∧
      CompletedWhenIdle V) ∧
      ∀ P : EvPol,
        EXEC_041 (refEvExec (N := Nat) (T := Nat) P).erase ∧
        EXEC_042 (refEvExec (N := Nat) (T := Nat) P).erase ∧
        Exec042Covers (refEvExec (N := Nat) (T := Nat) P).erase ∧
        EVT_003 (refEvExec (N := Nat) (T := Nat) P) ∧
        ¬ CompletedWhenIdle (refEvExec (N := Nat) (T := Nat) P) := by
  refine ⟨clashEvt_endMarker_conflict, fun P => ?_⟩
  have h41 : EXEC_041 (refEvExec (N := Nat) (T := Nat) P).erase := by
    rw [refEvExec_erase]; exact EXEC_041_reference
  have hcov : Exec042Covers (refEvExec (N := Nat) (T := Nat) P).erase := by
    rw [refEvExec_erase]; exact exec042_ref_covers
  refine ⟨h41, by rw [refEvExec_erase]; exact EXEC_042_reference, hcov, evt003_ref P,
    fun h => clashEvt_endMarker_conflict ⟨_, h41, hcov, evt003_ref P, h⟩⟩

/-! ## evt-a#7, evt-b#2, exec#13: `TransitionCompleted` after a timeout (ruling D65 (a)) -/

/-- ? **evt-a#7, evt-b#2, exec#13, ruling D65 (a): after a timeout outcome, `TransitionCompleted`
is allowed, not required.** Worked example: `b`'s budget runs out and the loop deposits its
timeout outcome, 8 in place 2. Java and TypeScript report `TokenAdded` and then
`TransitionCompleted` for `b`; Rust and Python report `ActionTimedOut` and `TokenAdded` only. Both
emissions meet EVT-007, whose third line states the weak form, and EVT-008 and EVT-011. -/
@[evidence cites "EVT-007" "after a timeout outcome is deposited, TransitionCompleted may follow and is not required (ruling D65 (a)): the Java and TypeScript emission reports it at every deposit of a timeout outcome and the Rust emission at none, and both meet EVT-007, EVT-008 and EVT-011", evidence consistent EVT_007 EVT_008 EVT_011]
theorem clashEvt_completedAfterTimeout :
    EVT_007 (refEvExec (N := Nat) (T := Nat) polJT) ∧
      EVT_007 (refEvExec (N := Nat) (T := Nat) polRust) ∧
      EVT_008 (refEvExec (N := Nat) (T := Nat) polJT) ∧
      EVT_008 (refEvExec (N := Nat) (T := Nat) polRust) ∧
      EVT_011 (refEvExec (N := Nat) (T := Nat) polJT) ∧
      EVT_011 (refEvExec (N := Nat) (T := Nat) polRust) ∧
      ∃ s s', RefExec cevC s (.tdeposit 0) s' ∧
        (∃ e ∈ refEmitW polJT cevC [] s (.tdeposit 0) s', e.kind = .transitionCompleted) ∧
        ∀ e ∈ refEmitW polRust cevC [] s (.tdeposit 0) s', e.kind ≠ .transitionCompleted := by
  obtain ⟨s, s', hs⟩ := cev_tdeposit
  exact ⟨EVT_007_reference, EVT_007_rust, EVT_008_reference, EVT_008_rust, EVT_011_reference,
    EVT_011_rust, s, s', hs, ref_completesTimeout cevC [] s 0 s' hs,
    ref_silentTimeout cevC [] s 0 s'⟩

/-! ## evt-b#9, exec#13: `ActionTimedOut` after `ExecutionCompleted` (ruling D65 (a)) -/

/-- ? **evt-b#9, exec#13, ruling D65 (a): in Java and TypeScript an `ActionTimedOut` may follow
`ExecutionCompleted`.** Worked example: `a` returns and marks the terminal place 9 while `b` is
still running, so the run stops and reports `ExecutionCompleted`; then `b`'s budget runs out. Java
and TypeScript report `ActionTimedOut` for `b` from the action's timer, after `ExecutionCompleted`;
it is not an orchestrator event. Rust and Python report it only when the loop deposits the
timeout outcome, which never happens after the stop, so nothing follows `ExecutionCompleted`
there. So `ExecutionCompleted` is the last orchestrator event of a run, not its last event. -/
@[evidence cites "EVT-010" "an ActionTimedOut may follow ExecutionCompleted for a firing the run abandoned (ruling D65 (a)): in Java and TypeScript the action's timer reports it after a terminal stop, and in Rust and Python nothing follows ExecutionCompleted on the same run", evidence cites "EVT-003" "no orchestrator event follows ExecutionCompleted, and ActionTimedOut is not an orchestrator event (ruling D65 (a)): on a run that stops on a terminal place with a timed firing in flight, the Java and TypeScript trace ends with that firing's ActionTimedOut after ExecutionCompleted", evidence consistent EVT_003 EVT_010]
theorem clashEvt_lateActionTimedOut :
    (EVT_003 (refEvExec (N := Nat) (T := Nat) polJT) ∧ EVT_010 (refEvExec (N := Nat) (T := Nat) polJT) ∧
      EVT_003 (refEvExec (N := Nat) (T := Nat) polRust) ∧
      EVT_010 (refEvExec (N := Nat) (T := Nat) polRust)) ∧
    (∃ tr, Trace (refEvExec polJT) cevC cevM 0 tr ∧
        afterCompleted tr = [NetEvent.actionTimedOut "b"]) ∧
      (NetEvent.actionTimedOut "b" : NetEvent Nat Nat).isOrch = false ∧
      ¬ EndsAtCompleted (refEvExec (N := Nat) (T := Nat) polJT) ∧
      (∃ tr, Trace (refEvExec polRust) cevC cevM 0 tr ∧
        (NetEvent.executionCompleted : NetEvent Nat Nat) ∈ tr ∧ afterCompleted tr = []) := by
  obtain ⟨tr, htr, hq⟩ := some_of_map (o := refTrace polJT cevC cevM 0 cevLate)
    (q := fun tr => afterCompleted tr == [NetEvent.actionTimedOut "b"]) (by decide +kernel)
  obtain ⟨tr', htr', hq'⟩ := some_of_map (o := refTrace polRust cevC cevM 0 cevLate)
    (q := fun tr => decide ((NetEvent.executionCompleted : NetEvent Nat Nat) ∈ tr) &&
      (afterCompleted tr).isEmpty) (by decide +kernel)
  simp only [beq_iff_eq] at hq
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at hq'
  have hT := refTrace_trace _ htr
  refine ⟨⟨EVT_003_reference, EVT_010_reference, EVT_003_rust, EVT_010_rust⟩, ⟨tr, hT, hq⟩, rfl,
    fun h => ?_, ⟨tr', refTrace_trace _ htr', hq'⟩⟩
  have := h cevC cevM 0 tr hT
  rw [hq] at this
  cases this

/-! ## evt-b#1: no `TokenAdded` for the initial marking (ruling D76 (a)) -/

/-- The conflict of clash evt-b#1: no executor with events meets EVT-011 and reports every token
of the initial marking as added. With 7 in place 0 of `cevC`, the old reading asks for a
`TokenAdded` of 7 at boot, which EVT-011's second line forbids. -/
theorem clashEvt_initialAdded_conflict : ¬ ∃ V : EvExec Nat Nat, EVT_011 V ∧ ReportsInitial V := by
  rintro ⟨V, h11, hR⟩
  exact (h11 cevC).2.1 cevM _ (hR cevC cevM 0 7 (by decide) (by decide)) rfl

/-- ✗ **evt-b#1, ruling D76 (a): the tokens of the initial marking get no `TokenAdded`.** Worked
example: a run starts with 7 in place 0. The old clause 'whether from initial marking' asks the
boot to report 7 as added; EVT-011 now says the boot reports no `TokenAdded`, and no runtime emits
one (the start snapshot carries the initial marking in Java and TypeScript). No executor meets
both; the reference meets EVT-011 under both emissions, and the boot that reports the initial
marking as added meets the old clause. -/
@[evidence cites "EVT-011" "the tokens of the initial marking get no TokenAdded event (ruling D76 (a)): no executor meets EVT-011 and also reports each token of the initial marking as added at boot, and the reference, under both emissions, meets EVT-011"]
theorem clashEvt_initialAdded :
    (¬ ∃ V : EvExec Nat Nat, EVT_011 V ∧ ReportsInitial V) ∧
      EVT_011 (refEvExec (N := Nat) (T := Nat) polJT) ∧
      EVT_011 (refEvExec (N := Nat) (T := Nat) polRust) ∧
      ReportsInitial (evt011_bootAdded (N := Nat) (T := Nat)) :=
  ⟨clashEvt_initialAdded_conflict, EVT_011_reference, EVT_011_rust, bootAdded_reports⟩

/-! ## evt-c#10: the replay's enabled set over-approximates (ruling D83 (a)) -/

/-- ✓ **evt-c#10, ruling D83 (a): the replay's enabled set is an over-approximation.** Worked
example: `T1` and `T2` both need the one token of place 0. The update reports both as enabled,
`T1` starts and takes the token, and `T2` silently loses its clock. The replay of these events
still lists `T2` as enabled, while the run has `T2` disarmed and place 0 empty: no event removes a
name from the replayed set except its own start. The reference meets EVT-004 and the replay cache
meets EVT-032, so the replayed set contains every armed name and may hold more. -/
@[evidence consistent EVT_004 EVT_032]
theorem clashEvt_replayEnabled :
    EVT_004 (refEvExec (N := Nat) (T := Nat) polJT) ∧
      EVT_032 (NetEvent.replayView (N := Nat) (T := Nat))
        (refReplayCall (NetEvent.replayView (N := Nat) (T := Nat))) ∧
      ∃ tr s, refTrace polJT cevC2 cevM2 0 cevLose = some tr ∧
        Trace (refEvExec polJT) cevC2 cevM2 0 tr ∧ xrun cevC2 (xinit cevM2 0) cevLose = some s ∧
        (replay NetEvent.replayView tr).en "T2" = true ∧ isArmedS (s.st "T2") = false ∧
        s.M 0 = [] := by
  obtain ⟨tr, htr, hq⟩ := some_of_map (o := refTrace polJT cevC2 cevM2 0 cevLose)
    (q := fun tr => (replay NetEvent.replayView tr).en "T2") (by decide +kernel)
  obtain ⟨s, hs, hq'⟩ := some_of_map (o := xrun cevC2 (xinit cevM2 0) cevLose)
    (q := fun s => !isArmedS (s.st "T2") && (s.M 0).isEmpty) (by decide +kernel)
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff] at hq'
  exact ⟨EVT_004_reference, EVT_032_reference _, tr, s, htr, refTrace_trace _ htr, hs, hq, hq'.1,
    hq'.2⟩

end Libpetri.Spec
