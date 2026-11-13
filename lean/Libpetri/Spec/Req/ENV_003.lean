import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Exec
import Libpetri.Spec.Text.ENV_003

set_option linter.missingDocs true

/-!
# ENV-003: inject() thread safety (`spec/06-environment-places.md`)

What an accepted injection does, over the executor model (`RefExec`, `Reference/Exec.lean`). A
caller's `inject()` is the outside step `request p x r`; when the executor accepts it (`r =
accepted`) the event joins the tail of the event queue `eq` under a ticket drawn from the supply
`nextId`. The orchestrator later injects it (`inject k`, step 2 or the wake of the wait), discards
it once closed or terminated (`discard k`, `terminateNow`), or the run ends.

The requirement is a predicate over an abstract executor `R : XRel N T` (glossary
`GlossaryExec.lean`):

1. an accepted request only queues the event, at the tail, under the supply's ticket, moves the
   supply on and wakes the loop, and changes no other part of the state (the token does not land
   at the call);
2. an injection takes the oldest queued event, removes it from the queue and adds its token at the
   tail of its place, no other place changed (ruling D48 (a));
3. no other step changes the event queue, except a discard, an immediate termination and the
   finish;
4. a discard, an immediate termination and the finish only remove queued events and keep the
   others in order, so with lines 1 to 3 events are injected in the order they were accepted;
5. no step moves the ticket supply back, so no two accepted calls share a ticket;
6. on a run that finishes (`IdealRun`, kind A), every accepted event is injected unless the
   executor is closed, terminated immediately or stopped on a marked terminal place after
   accepting it (the condition of ruling D20, clash env-a#7).

The offer, that in step 2 of a cycle, with no terminal place marked, the executor neither closed
nor stopped and an event queued, the orchestrator can inject the oldest event, is coverage:
`Env003Covers`, a clause of the consistency theorem's `ExecCoversW5`, never a line.

The evidence checks it against the reference executor and thirteen wrong executors: a token
applied at the call, a queue that pushes at the head, a ticket reused, a request that does not wake
the loop, an injection of the newest event, an injected token put at the head of its place, an
injection that leaves its event queued, a queue kept per place, an end of step 2 that drops what is
still queued, a discard that moves the head to the tail, a supply reset, a termination test that
forgets queued events, and a terminal stop latched at the call. A fourteenth, a step 2 that never
injects, meets every line and fails only the coverage clause.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## The steps lines 3, 4 and 6 read -/

namespace Env003

variable {N T : Type}

/-- The step accepts an injection request and queues it under ticket `k`: the ticket is the
supply's next value in the step's source state, which line 1 makes the ticket of the new entry. -/
def accepts (k : Nat) (e : XStep N T) : Bool :=
  match e.2.1 with
  | .request _ _ .accepted => e.1.nextId == k
  | _ => false

/-- The step injects the event of ticket `k`. -/
def injects (k : Nat) (e : XStep N T) : Bool :=
  match e.2.1 with
  | .inject j => j == k
  | _ => false

/-- The step serves ticket `k` (injects it) or releases the executor from serving it: a close
([ENV-013]), an immediate termination ([ENV-015]) or a stop on a terminal place ([EXEC-042]),
which counts only when a terminal place is marked in the step's source state (not Live under
`C`): a terminal stop with no terminal place marked releases nothing. -/
def serves [DecidableEq N] (C : Cfg N T) (k : Nat) (e : XStep N T) : Bool :=
  match e.2.1 with
  | .inject j => j == k
  | .close | .terminateNow => true
  | .finish .terminal => !liveB C e.1
  | _ => false

/-- The labels that leave the event queue as it is (line 3): every label except an accepted
request (line 1), an injection (line 2), a discard ([ENV-013]), an immediate termination
([ENV-015]) and a finish ([EXEC-041]). -/
def keepsQueue : XLbl N T → Bool
  | .request _ _ .accepted | .inject _ | .discard _ | .terminateNow | .finish _ => false
  | _ => true

/-- The labels that may drop queued events (line 4): a discard ([ENV-013]), an immediate
termination ([ENV-015]) and a finish ([EXEC-041]). -/
def dropsQueue : XLbl N T → Bool
  | .discard _ | .terminateNow | .finish _ => true
  | _ => false

end Env003

/-! ## ENV-003: inject() Thread Safety -/

requirement ENV_003
  id "ENV-003"
  title "inject() Thread Safety"
  kind B
  scope "all executors with environment places"
  source verbatim "spec/06-environment-places.md"
  covers ENV_003.s1, ENV_003.s2, ENV_003.s3, ENV_003.s4, ENV_003.s5, ENV_003.s6, ENV_003.s7,
        ENV_003.s8, ENV_003.s9
  reading "For every executor R and every configuration C:"
          "an accepted request of token x into place p leaves the state as it was except that the event queue gains (n, p, x) at its tail, n the ticket supply's value before the step, the supply moves on to n + 1, and the parked flag is cleared;"
          "an injection with ticket k happens only when the event queue starts with an entry (k, p, x): it leaves the rest of the queue and adds x at the tail of place p, every other place unchanged;"
          "every step that is not an accepted request, an injection, a discard, an immediate termination or a finish leaves the event queue as it was;"
          "a discard, an immediate termination and a finish leave an event queue that is a sublist of the one before (entries removed, the others kept in order);"
          "no step lowers the ticket supply;"
          "for every start state and every ticket k, on every run that reaches its finish, a step that accepts a request under ticket k is followed, at it or later, by the injection of k, a close, an immediate termination or a finish on a terminal place from a state where a terminal place is marked."
  assumes "The model is an executor R : XRel N T (glossary GlossaryExec.lean): R C s l s' says that under configuration C the step labelled l leads from executor state s to s'. A caller's inject() is the outside step request p x r with the reply r; the event queue eq holds the accepted events with their tickets, drawn from the supply nextId that firing identities share. The witness is the reference executor RefExec (Reference/Exec.lean), the graph of a step function checked rule by rule against the Rust executor."
          "AC1 and AC2 (inject() callable from a thread other than the orchestrator's, concurrent calls without data races) are kind Q: threads, locks and memory visibility are not in the model. The model reads them at the grain of interleaving: request is an outside step (CONC-001), offered by the reference in every phase of a running loop, so an injection can arrive between any two executor steps; that it is offered at all is coverage of the consistency theorem, not a line here. The Java ConcurrentLinkedQueue, the TypeScript single thread and the Rust FIFO channel are what make the step atomic, and the tests are the evidence (coverage matrix: Rust only)."
          "The first quoted sentence ('safe to call from any thread') is AC1 and AC2, kind Q as above. The second ('It enqueues the token for processing on the next orchestrator cycle') is lines 1 and 6 and the coverage clause Env003Covers. Line 1 is the enqueue: the token does not land in the marking at the call (ENV_003_forbids_atCall: the Novel spike ApplyInPlace). Env003Covers is the processing: in step 2, with no terminal place marked and the executor neither closed nor stopped, the orchestrator can inject the oldest queued event (env003_covers_noInject: a step 2 that never injects is stuck with the event queued, a run that never finishes, which line 6 alone does not see; it meets every line and fails the clause). The cycle position is EXEC-001's and CONC-010's: an event queued when step 2 begins is injected before that cycle's enablement update (EXEC-001 line 5, step 2 ends only with an empty queue), and the wait never parks with an event queued (CONC-010 line 1, ENV-005). Ruling D70 (a) and clash env-a#8: Rust injects in the wait as well as in step 2 (the wait's signal arm), so lines 2 and 6 say 'the orchestrator injects it', never which phase; the reference offers inject in step 2 and in the wait, and Env003Covers asks only for step 2."
          "The first EARS sentence is line 1: an accepted request changes only the event queue, by appending its entry at the tail (ENV_003_forbids_headQueue: a stack), the ticket supply, by moving on so that the entry has a ticket of its own (ENV_003_forbids_reusesTicket: two queued entries share a ticket, so ENV-004 cannot tell their answers apart), and the parked flag, which it clears: 'wakes the orchestrator if it is waiting' reads as the flag false after the step, a loop that was blocked is woken and one that was not stays unblocked (ENV_003_forbids_noWake: an accepted request that leaves a blocked loop blocked). ENV-005 line 3 says the same of the flag; ENV-005 builds on this block (its Depends on line names ENV-003), so the [ENV-005] of the sentence is a cross-reference, and ENV-005 is not in this block's Depends on line. Whether a request is accepted, refused or answered with an error is ENV-002's and ENV-006's subject; this block constrains the accepted ones."
          "The second EARS sentence is line 2, the new sentence of ruling D48 (a) (events FIFO by acceptance, appended at the tail): an injection takes the head of the queue (ENV_003_forbids_newestFirst), removes it (ENV_003_forbids_keepsQueued: the same event would be injected again) and appends its token at the tail of its place, the glossary's queue order for a deposit (ENV_003_forbids_headOfPlace). The line fixes the marking exactly (qAppendOne), which is the sentence's 'shall not change any other place'. That an injected token writes its place, so a reaped transition with an arc on it is no longer reaped (ruling D6), is the glossary Write entry and TIME-013's companion line; where the loop goes after an injection from the wait is EXEC-001's."
          "The third EARS sentence is line 3 and the fourth is line 4. Line 3: no step other than an accepted request, an injection, a discard, an immediate termination or a finish changes the queue (ENV_003_forbids_perPlaceQueues: one queue per place drains place by place and loses the order across places; ENV_003_forbids_clearsAtEnd: an end of step 2 that empties the queue, the TypeScript walk of a fixed prefix followed by clearing the whole queue, drops an event accepted during the walk). Line 4: a discard, an immediate termination and a finish only remove entries and keep the rest in order (ENV_003_forbids_rotates: a discard that moves the head to the tail keeps every event and passes lines 3 and 6). With lines 1 and 2 they give FIFO by acceptance. When a discard may come (only once the executor is closed or stopped) is ENV-004 line 2 and ENV-013; the immediate termination that drops the whole queue is ENV-015; the finish empties the queue (EXEC-041; ENV-004 for the answer each dropped call gets). The reference meets line 4: discard removes the head, and terminateNow and every finish set the queue to empty. A refused request is a step that keeps the queue, as ENV-006 also says. A close keeps the queue and later discard steps drop it, as the Java and TypeScript loops do; Java's close() on an executor whose loop is not running completes the queued calls with false at once (BitmapNetExecutor.close), which the model does not reach: it has no state before the loop starts, and after the finish the queue is already empty."
          "The fifth EARS sentence is line 5, the 'fresh ticket' of the first: the supply never goes back, so with line 1 every accepted call gets a ticket no earlier call of the run had. Firing identities draw from the same supply (a start moves it on), so the line also reads EXEC-031's identity supply; the reference never lowers it. The line is load-bearing for line 6, whose watch keeps one flag per ticket: an executor that resets the supply at the enablement update and whose termination test forgets the event queue accepts 7 and 8 under the same ticket 0, injects the 7, and finishes with the 8 never injected and no close, while one injection of ticket 0 pays both acceptances (ENV_003_forbids_resetsSupply). Line 6 reads every start state, including ones whose queue already holds a ticket at or above the supply; from a start state whose queued tickets are distinct and below the supply (every initial state; ENV-004's env004_Fresh), lines 1 to 5 keep them so."
          "The sixth EARS sentence is line 6 and the reading of AC3. The markdown's AC3 carries the exception (clash env-a#7, ruling D20): ENV-013 and EXEC-042 drop queued events, so a close (ENV-013), an immediate termination (ENV-015, Java) or a stop because a terminal place is marked (EXEC-042) after the acceptance releases the executor; the end of a run on a host cancellation (EXEC-041) releases it too and is outside the model (the host cancellation assumption below). The reference shows the exception is needed: ENV_003_allows_closeDiscards decides a reference run that finishes with an accepted event discarded after a close. A terminal stop releases only when a terminal place is marked in the state it starts from (Env003.serves): ENV_003_forbids_latchTerminal is the TypeScript terminal latch moved from processExternalEvents into inject() (or Java's isTerminal test next to externalEventQueue.offer), which stops the loop when an event for a terminal place is accepted, before its token is in the marking, and drops an event accepted earlier for another place; EXEC-042's last line catches it too. Rust injects every event sent before its close (one FIFO channel for events and the close signal); that is a run whose close step comes after those injections, and line 6 holds of it either way."
          "Host cancellation (kind Q, Java): the sentence and AC3 also release an event when the run ends on a cancellation the executor observes in its wait (EXEC-041). In Java an interrupt raised while the orchestrator waits (awaitExternalEvent, awaitCompletionPolling and the hosted wait of both executors) ends the run as INTERRUPTED, and the finally completes the events still queued with false; Semaphore.acquire throws on the interrupt even when an inject() has just released a permit, so an event accepted just before the wait can be among them. The model has no host cancellation (EXEC-041's assumes: no step reports interrupted), so line 6 has no release for it and reads only runs that end by a finish of the model; the exception is checked by the Java tests EXEC-041's test derivation names. Rust, TypeScript and Python observe no such cancellation."
          "One injector per executor (ruling D44 (a), kind A for Rust, as ENV-006's scope note says): the model reads the lifecycle as shared by every injector, as Java, TypeScript and Python have it. In Rust the drained flag belongs to the ExecutorHandle (executor_handle.rs inject tests only its own handle), so a second sender on the same channel is answered true after another handle drained or closed, and handle_signal drops that event on receipt while draining (executor_core/executor.rs, the ExecutorSignal::Event arm that discards). Such an accepted call is never injected, which line 6 would forbid, and its removal is none of line 3's steps; under the assumption a handle's own drain or close is the executor's, so the call is refused (ENV-006 line 1) and no such event is queued."
          "Line 6 is liveness read on runs that reach their finish (IdealRun, an assumption of kind A of glossary GlossaryExec.lean): on a finite run 'eventually' reads 'before the finish'. A run of an open executor with environment places that is never drained or closed does not finish, and line 6 says nothing about it; there, Env003Covers says the injection is always on offer in step 2, and that the loop takes it rather than stalling is the loop's own fairness, outside the model. Line 6 is load-bearing beyond lines 1 to 5: an executor whose termination test forgets the event queue finishes quiescent with an accepted event never injected (ENV_003_forbids_forgets), the Java or TypeScript loop exit reading only the transitions and the actions in flight. ENV_003_nonvacuous decides reference runs that finish after an injection, so the assumption holds of some runs and the line is not vacuous (onIdealRuns_of_none)."
          "Its offers are in ExecCoversW5.Env003Covers (ConsistencyExec.lean; the convention of GlossaryExec.lean: offers are coverage clauses, never block lines). The seventh EARS sentence demands an answer and is quoted whole; it has no safety half, and its existence half is that clause: the inject step of the oldest entry exists in every such state, which the reference meets by its inject rule (env003_ref_covers); other steps (a request, a snapshot) may come first, and nothing ends step 2 while an event is queued (EXEC-001 line 5). Depends on: ENV-002 (which places accept), ENV-013, ENV-015, EXEC-041 and EXEC-042 (the releases and drops of lines 3, 4 and 6), EXEC-001 (step 2) and CONC-010 (the wait)."
          "Scope: Rust run_sync has no signal channel and no inject() (rust/README.md, Checkpoint and resume: 'run_sync has no signal channel', and injections travel on that channel), so the requirement reads the executors that accept injections. Python rides on the Rust runtime."
          "The test derivation (ten threads each inject a token, all ten are processed) is ENV_003_nonvacuous, part 5: ten requests are accepted, the executor drains, the ten tokens are injected in the order they were accepted and land at the tail of place 0 behind its initial token, and the run finishes quiescent; the threads are AC1 and AC2."
  signoff "2026-11-13 b4210631b2c3af53 ai"
  statement : ∀ {N T : Type} [DecidableEq N], XRel N T → Prop :=
    fun R => ∀ C,
      (∀ p x, on (fun s s' => R C s (.request p x .accepted) s'), shall (fun s s' =>
        s' = { s with eq := s.eq ++ [(s.nextId, p, x)], nextId := s.nextId + 1,
                      parked := false })) ∧
      (∀ k, on (fun s s' => R C s (.inject k) s'), shall (fun s s' =>
        ∃ p x rest, s.eq = (k, p, x) :: rest ∧ s'.eq = rest ∧ s'.M = qAppendOne s.M p x)) ∧
      (∀ l, Env003.keepsQueue l = true →
        on (fun s s' => R C s l s'), shall (fun s s' => s'.eq = s.eq)) ∧
      (∀ l, Env003.dropsQueue l = true →
        on (fun s s' => R C s l s'), shall (fun s s' => s'.eq.Sublist s.eq)) ∧
      (∀ l, on (fun s s' => R C s l s'), shall (fun s s' => s.nextId ≤ s'.nextId)) ∧
      (∀ s0 k, on-ideal-runs (IdealRun R C s0), shall
        (when Env003.accepts k, shall Env003.serves C k))

/- The pinned readable form of ENV-003: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.ENV_003 : {N T : Type} → [DecidableEq N] → XRel N T → Prop :=
fun {N T} [DecidableEq N] R =>
  ∀ (C : Cfg N T),
    (∀ (p : N) (x : T),
        on fun s s' => R C s (XLbl.request p x Reply.accepted) s', shall fun s s' =>
          s' =
            { M := s.M, now := s.now, cyc := s.cyc, st := s.st, fl := s.fl, nextId := s.nextId + 1, cq := s.cq,
              pq := s.pq, eq := s.eq ++ [(s.nextId, p, x)], mode := s.mode, phase := s.phase, order := s.order,
              delta := s.delta, started := s.started, parked := false }) ∧
      (∀ (k : ℕ),
          on fun s s' => R C s (XLbl.inject k) s', shall fun s s' =>
            ∃ p x rest, s.eq = (k, p, x) :: rest ∧ s'.eq = rest ∧ s'.M = qAppendOne s.M p x) ∧
        (∀ (l : XLbl N T), Env003.keepsQueue l = true → on fun s s' => R C s l s', shall fun s s' => s'.eq = s.eq) ∧
          (∀ (l : XLbl N T),
              Env003.dropsQueue l = true → on fun s s' => R C s l s', shall fun s s' => s'.eq.Sublist s.eq) ∧
            (∀ (l : XLbl N T), on fun s s' => R C s l s', shall fun s s' => s.nextId ≤ s'.nextId) ∧
              ∀ (s0 : XSt N T) (k : ℕ),
                on-ideal-runs IdealRun R C s0, shall when Env003.accepts k, shall Env003.serves C k
-/
#guard_msgs in #print ENV_003

/-! ### The reference

Lines 1 to 5 read one step each, as does the offer of `Env003Covers`. Line 6 tracks one queued entry along the run
(`Env003.Pending`): while it is queued, the mode is open or draining and the loop runs, every step
that does not serve or release it keeps it so (`Env003.pending_step`), and a run that keeps it to
its end cannot have finished. -/

namespace Env003

variable {N T : Type} [DecidableEq N]

/-- Line 3 on the reference: a label that keeps the queue leaves `eq` as it was. -/
theorem frame {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T} (h : RefExec C s l s')
    (hk : keepsQueue l = true) : s'.eq = s.eq := by
  cases l with
  | delay δ => cases xstepW_delay h; rfl
  | write i p x => obtain ⟨_, _, _, rfl⟩ := writeStep_some h; rfl
  | flush i =>
    obtain ⟨_, _, _, _, _, ⟨_, _, rfl⟩ | ⟨_, rfl⟩⟩ := flushStep_some h <;> rfl
  | ret i ok => obtain ⟨_, _, _, rfl⟩ := retStep_some h; rfl
  | expire i e => obtain ⟨_, _, _, _, _, _, rfl⟩ := expireStep_some h; rfl
  | request p x r =>
    obtain ⟨-, ⟨rfl, -⟩ | ⟨-, rfl⟩⟩ := requestStep_some h
    · simp [keepsQueue] at hk
    · rfl
  | drain => obtain ⟨-, rfl⟩ := drainStep_some h; rfl
  | close => obtain ⟨-, rfl⟩ := closeStep_some h; rfl
  | terminateNow => simp [keepsQueue] at hk
  | commit i => obtain ⟨_, _, _, _, _, _, _, rfl⟩ := commitStep_some h; rfl
  | fail i => obtain ⟨_, _, _, _, rfl⟩ := failStep_some h; rfl
  | tdeposit i => obtain ⟨_, _, _, _, _, _, rfl⟩ := tdepositStep_some h; rfl
  | endCompletions => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endCompletions h; rfl
  | publish i => obtain ⟨_, _, _, _, _, rfl⟩ := publishStep_some h; rfl
  | endPublications => obtain ⟨-, -, -, rfl⟩ := xstepW_endPublications h; rfl
  | inject k => simp [keepsQueue] at hk
  | discard k => simp [keepsQueue] at hk
  | endEvents => obtain ⟨-, -, -, rfl⟩ := xstepW_endEvents h; rfl
  | snapshot a => obtain ⟨-, -, -, rfl⟩ := snapshotStep_some h; rfl
  | update => obtain ⟨-, -, rfl⟩ := xstepW_update h; rfl
  | deadline ns => obtain ⟨-, -, -, rfl⟩ := xstepW_deadline h; rfl
  | begin => obtain ⟨-, -, -, -, rfl⟩ := xstepW_begin h; rfl
  | start n sy => obtain ⟨_, _, _, _, _, _, _, _, _, rfl⟩ := startStep_some h; rfl
  | lose n => obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := loseStep_some h; rfl
  | endPass => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endPass h; rfl
  | finish c => simp [keepsQueue] at hk
  | park tmr => obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := parkStep_some h; rfl
  | wake => obtain ⟨-, -, rfl⟩ := wakeStep_some h; rfl

/-- Line 4 on the reference: a discard drops the head, and an immediate termination and every
finish empty the queue. -/
theorem drops {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T} (h : RefExec C s l s')
    (hd : dropsQueue l = true) : s'.eq.Sublist s.eq := by
  cases l with
  | discard k =>
    obtain ⟨p, x, rest, he, -, -, -, rfl⟩ := discardStep_some h
    rw [he]
    exact List.sublist_cons_self _ _
  | terminateNow => obtain ⟨-, rfl⟩ := terminateStep_some h; exact List.nil_sublist _
  | finish c =>
    cases c with
    | quiescent => obtain ⟨-, -, -, rfl⟩ := xstepW_finishQuiescent h; exact List.nil_sublist _
    | closed => obtain ⟨-, -, -, -, rfl⟩ := xstepW_finishClosed h; exact List.nil_sublist _
    | terminal => obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h; exact List.nil_sublist _
    | stopped => obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h; exact List.nil_sublist _
  | _ => simp [dropsQueue] at hd

/-- Line 5 on the reference: an accepted request and a start move the supply on, and every other
rule keeps it. -/
theorem supply {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T} (h : RefExec C s l s') :
    s.nextId ≤ s'.nextId := by
  cases l with
  | delay δ => cases xstepW_delay h; exact Nat.le_refl _
  | write i p x => obtain ⟨_, _, _, rfl⟩ := writeStep_some h; exact Nat.le_refl _
  | flush i =>
    obtain ⟨_, _, _, _, _, ⟨_, _, rfl⟩ | ⟨_, rfl⟩⟩ := flushStep_some h <;> exact Nat.le_refl _
  | ret i ok => obtain ⟨_, _, _, rfl⟩ := retStep_some h; exact Nat.le_refl _
  | expire i e => obtain ⟨_, _, _, _, _, _, rfl⟩ := expireStep_some h; exact Nat.le_refl _
  | request p x r =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := requestStep_some h
    · exact Nat.le_succ _
    · exact Nat.le_refl _
  | drain => obtain ⟨-, rfl⟩ := drainStep_some h; exact Nat.le_refl _
  | close => obtain ⟨-, rfl⟩ := closeStep_some h; exact Nat.le_refl _
  | terminateNow => obtain ⟨-, rfl⟩ := terminateStep_some h; exact Nat.le_refl _
  | commit i => obtain ⟨_, _, _, _, _, _, _, rfl⟩ := commitStep_some h; exact Nat.le_refl _
  | fail i => obtain ⟨_, _, _, _, rfl⟩ := failStep_some h; exact Nat.le_refl _
  | tdeposit i => obtain ⟨_, _, _, _, _, _, rfl⟩ := tdepositStep_some h; exact Nat.le_refl _
  | endCompletions => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endCompletions h; exact Nat.le_refl _
  | publish i => obtain ⟨_, _, _, _, _, rfl⟩ := publishStep_some h; exact Nat.le_refl _
  | endPublications => obtain ⟨-, -, -, rfl⟩ := xstepW_endPublications h; exact Nat.le_refl _
  | inject k => obtain ⟨_, _, _, -, -, -, -, rfl⟩ := injectStep_some h; exact Nat.le_refl _
  | discard k => obtain ⟨_, _, _, -, -, -, -, rfl⟩ := discardStep_some h; exact Nat.le_refl _
  | endEvents => obtain ⟨-, -, -, rfl⟩ := xstepW_endEvents h; exact Nat.le_refl _
  | snapshot a => obtain ⟨-, -, -, rfl⟩ := snapshotStep_some h; exact Nat.le_refl _
  | update => obtain ⟨-, -, rfl⟩ := xstepW_update h; exact Nat.le_refl _
  | deadline ns => obtain ⟨-, -, -, rfl⟩ := xstepW_deadline h; exact Nat.le_refl _
  | begin => obtain ⟨-, -, -, -, rfl⟩ := xstepW_begin h; exact Nat.le_refl _
  | start n sy =>
    obtain ⟨_, _, _, _, _, _, _, _, _, rfl⟩ := startStep_some h; exact Nat.le_succ _
  | lose n => obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := loseStep_some h; exact Nat.le_refl _
  | endPass => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endPass h; exact Nat.le_refl _
  | finish c =>
    cases c with
    | quiescent => obtain ⟨-, -, -, rfl⟩ := xstepW_finishQuiescent h; exact Nat.le_refl _
    | closed => obtain ⟨-, -, -, -, rfl⟩ := xstepW_finishClosed h; exact Nat.le_refl _
    | terminal => obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h; exact Nat.le_refl _
    | stopped => obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h; exact Nat.le_refl _
  | park tmr => obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := parkStep_some h; exact Nat.le_refl _
  | wake => obtain ⟨-, -, rfl⟩ := wakeStep_some h; exact Nat.le_refl _

/-- The offer of `Env003Covers` on the reference: its inject rule takes the head of the queue in step 2 whenever no
terminal place is marked and the executor is open or draining. -/
theorem offer {C : Cfg N T} {s : XSt N T} {k : Nat} {p : N} {x : T}
    {rest : List (Nat × N × T)} (hp : s.phase = .events) (hl : Live C s)
    (hc : s.mode.closing = false) (he : s.eq = (k, p, x) :: rest) :
    ∃ s', RefExec C s (.inject k) s' := by
  unfold Live at hl
  exact ⟨_, by simp [RefExec, xstep, xstepW, injectStep, he, hl, hc, hp]; rfl⟩

omit [DecidableEq N] in
/-- The entry of ticket `k` is queued, the executor is open or draining, and the loop runs. -/
def Pending (k : Nat) (s : XSt N T) : Prop :=
  (∃ p x, (k, p, x) ∈ s.eq) ∧ s.mode.closing = false ∧ isExecPhase s.phase = true

omit [DecidableEq N] in
/-- A step that leaves the await phase for step 1, or keeps any other running phase, keeps the
loop running. -/
theorem exec_awaitOr {p : Phase} (hp : isExecPhase p = true) :
    isExecPhase (if p = .await then .completions else p) = true := by
  split <;> simp_all [isExecPhase]

/-- An accepting step makes its entry pending. -/
theorem accept_pending {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T} {k : Nat}
    (h : RefExec C s l s') (ha : accepts k (s, l, s') = true) : Pending k s' := by
  cases l with
  | request p x r =>
    cases r with
    | accepted =>
      simp only [accepts, beq_iff_eq] at ha
      obtain ⟨hr, ⟨-, rfl⟩ | ⟨hne, -⟩⟩ := requestStep_some h
      · unfold replyFor at hr
        split at hr
        · cases hr
        · split at hr
          · rename_i hc
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
            refine ⟨⟨p, x, by simp [ha]⟩, ?_, hc.2⟩
            simp [hc.1, Mode.closing]
          · cases hr
      · exact absurd rfl hne
    | refused => simp [accepts] at ha
    | error => simp [accepts] at ha
  | _ => simp [accepts] at ha

/-- A step that neither serves nor releases ticket `k` keeps it pending. -/
theorem pending_step {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T} {k : Nat}
    (h : RefExec C s l s') (hq : Pending k s) (hr : serves C k (s, l, s') = false) :
    Pending k s' := by
  obtain ⟨⟨p, x, hm⟩, hc, he⟩ := hq
  cases l with
  | delay δ => cases xstepW_delay h; exact ⟨⟨p, x, hm⟩, hc, he⟩
  | write i q y => obtain ⟨_, _, _, rfl⟩ := writeStep_some h; exact ⟨⟨p, x, hm⟩, hc, he⟩
  | flush i =>
    obtain ⟨_, _, _, _, _, ⟨_, _, rfl⟩ | ⟨_, rfl⟩⟩ := flushStep_some h <;>
      exact ⟨⟨p, x, hm⟩, hc, he⟩
  | ret i ok => obtain ⟨_, _, _, rfl⟩ := retStep_some h; exact ⟨⟨p, x, hm⟩, hc, he⟩
  | expire i e => obtain ⟨_, _, _, _, _, _, rfl⟩ := expireStep_some h; exact ⟨⟨p, x, hm⟩, hc, he⟩
  | request q y r =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := requestStep_some h
    · exact ⟨⟨p, x, List.mem_append_left _ hm⟩, hc, he⟩
    · exact ⟨⟨p, x, hm⟩, hc, he⟩
  | drain => obtain ⟨-, rfl⟩ := drainStep_some h; exact ⟨⟨p, x, hm⟩, rfl, he⟩
  | close => simp [serves] at hr
  | terminateNow => simp [serves] at hr
  | commit i =>
    obtain ⟨_, _, _, _, _, _, _, rfl⟩ := commitStep_some h
    exact ⟨⟨p, x, hm⟩, hc, exec_awaitOr he⟩
  | fail i =>
    obtain ⟨_, _, _, _, rfl⟩ := failStep_some h
    exact ⟨⟨p, x, hm⟩, hc, exec_awaitOr he⟩
  | tdeposit i =>
    obtain ⟨_, _, _, _, _, _, rfl⟩ := tdepositStep_some h
    exact ⟨⟨p, x, hm⟩, hc, exec_awaitOr he⟩
  | endCompletions =>
    obtain ⟨-, -, -, -, rfl⟩ := xstepW_endCompletions h; exact ⟨⟨p, x, hm⟩, hc, rfl⟩
  | publish i =>
    obtain ⟨_, _, _, _, _, rfl⟩ := publishStep_some h
    exact ⟨⟨p, x, hm⟩, hc, exec_awaitOr he⟩
  | endPublications =>
    obtain ⟨-, -, -, rfl⟩ := xstepW_endPublications h; exact ⟨⟨p, x, hm⟩, hc, rfl⟩
  | inject j =>
    obtain ⟨q, y, rest, heq, -, -, -, rfl⟩ := injectStep_some h
    have hj : j ≠ k := by simpa [serves] using hr
    rw [heq] at hm
    rcases List.mem_cons.mp hm with hh | ht
    · exact absurd (congrArg Prod.fst hh).symm hj
    · exact ⟨⟨p, x, ht⟩, hc, exec_awaitOr he⟩
  | discard j =>
    obtain ⟨_, _, _, _, -, hcl, -⟩ := discardStep_some h
    simp [hc] at hcl
  | endEvents =>
    obtain ⟨-, -, he', -⟩ := xstepW_endEvents h
    simp [he'] at hm
  | snapshot a => obtain ⟨-, -, -, rfl⟩ := snapshotStep_some h; exact ⟨⟨p, x, hm⟩, hc, he⟩
  | update => obtain ⟨-, -, rfl⟩ := xstepW_update h; exact ⟨⟨p, x, hm⟩, hc, rfl⟩
  | deadline ns => obtain ⟨-, -, -, rfl⟩ := xstepW_deadline h; exact ⟨⟨p, x, hm⟩, hc, rfl⟩
  | begin => obtain ⟨-, -, -, -, rfl⟩ := xstepW_begin h; exact ⟨⟨p, x, hm⟩, hc, rfl⟩
  | start n sy =>
    obtain ⟨_, _, _, _, _, _, _, _, _, rfl⟩ := startStep_some h; exact ⟨⟨p, x, hm⟩, hc, he⟩
  | lose n =>
    obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := loseStep_some h; exact ⟨⟨p, x, hm⟩, hc, he⟩
  | endPass =>
    obtain ⟨-, -, -, -, rfl⟩ := xstepW_endPass h
    refine ⟨⟨p, x, hm⟩, hc, ?_⟩
    simp only
    split <;> rfl
  | finish c =>
    cases c with
    | quiescent =>
      obtain ⟨-, -, hf, -⟩ := xstepW_finishQuiescent h
      simp only [finishQ, restB, Bool.and_eq_true, List.isEmpty_iff] at hf
      simp [hf.1.2] at hm
    | closed =>
      obtain ⟨-, -, hcl, -⟩ := xstepW_finishClosed h
      simp [hc] at hcl
    | terminal =>
      obtain ⟨-, hl, -⟩ := xstepW_finishTerminal h
      simp [serves, hl] at hr
    | stopped =>
      obtain ⟨-, -, hst, -⟩ := xstepW_finishStopped h
      simp [hst, Mode.closing] at hc
  | park tmr =>
    obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := parkStep_some h; exact ⟨⟨p, x, hm⟩, hc, he⟩
  | wake => obtain ⟨-, -, rfl⟩ := wakeStep_some h; exact ⟨⟨p, x, hm⟩, hc, rfl⟩

omit [DecidableEq N] in
/-- The end of a run that starts with step `e` is the end of its rest from `e`'s target. -/
theorem last_cons (s0 : XSt N T) (e : XStep N T) (rest : List (XStep N T)) :
    XRun.last s0 (e :: rest) = XRun.last e.2.2 rest := by
  cases rest with
  | nil => rfl
  | cons e' rest' =>
    simp only [XRun.last, List.getLast?_cons_cons]
    cases hz : (e' :: rest').getLast? with
    | none => simp at hz
    | some z => rfl

/-- Line 6 on the reference, as the scan of the `when T, shall R` watch: from a state that owes
nothing, or owes ticket `k` while it is pending, a run that ends finished pays every debt. -/
theorem scan_ok {C : Cfg N T} (k : Nat) :
    ∀ (tr : List (XStep N T)) (s : XSt N T) (a : Bool), XRun RefExec C s tr →
      isExecPhase (XRun.last s tr).phase = false → (a = true → Pending k s) →
      (whenShall (accepts k) (serves C k)).scan a tr = true
  | [], s, a, _, hl, ha => by
    cases a with
    | false => rfl
    | true =>
      have := (ha rfl).2.2
      simp [XRun.last] at hl
      simp [hl] at this
  | ⟨s₁, l, s₂⟩ :: rest, s, a, ⟨h1, hstep, hrun⟩, hl, ha => by
    simp only at h1
    subst h1
    simp only [Watch.scan, whenShall, Bool.true_and]
    refine scan_ok k rest s₂ _ hrun (by rwa [last_cons] at hl) fun ha' => ?_
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at ha'
    obtain ⟨hor, hsv⟩ := ha'
    rcases hor with hat | hacc
    · exact pending_step hstep (ha hat) hsv
    · exact accept_pending hstep hacc

end Env003

/-- ✓ The reference executor satisfies ENV-003: its request rule queues an accepted event at the
tail under ticket `nextId`, moves the supply on, clears the parked flag and touches nothing else
(`requestStep_some`); its inject rule takes the head of the queue and appends its token at the
tail of its place (`injectStep_some`); every other rule keeps the queue except discard, terminate
and finish (`Env003.frame`), which only drop entries (`Env003.drops`); no rule lowers the supply
(`Env003.supply`); and an accepted entry stays queued, with the executor open or draining and the loop
running, until it is injected or a close, an immediate termination or a terminal stop from a
state with a terminal place marked comes (`Env003.pending_step`), so a run that finishes has
served it (`Env003.scan_ok`). -/
@[evidence holds ENV_003]
theorem ENV_003_reference {N T : Type} [DecidableEq N] :
    ENV_003 (RefExec (N := N) (T := T)) := by
  intro C
  refine ⟨fun p x s s' h => ?_, fun k s s' h => ?_, fun l hk s s' h => Env003.frame h hk,
    fun l hd s s' h => Env003.drops h hd, fun l s s' h => Env003.supply h,
    fun s0 k tr hi => ?_⟩
  · obtain ⟨-, ⟨-, rfl⟩ | ⟨hne, -⟩⟩ := requestStep_some h
    · rfl
    · exact absurd rfl hne
  · obtain ⟨p, x, rest, heq, -, -, -, rfl⟩ := injectStep_some h
    exact ⟨p, x, rest, heq, rfl, rfl⟩
  · exact Env003.scan_ok k tr s0 false hi.1 hi.2 (fun h => by cases h)

/-- **The coverage conjunct ENV-003 asks of the consistency theorem's `ExecCoversW5`**: in step 2
of a cycle ([EXEC-001]), with no terminal place marked, the executor neither closed nor stopped
and an event queued, the orchestrator can inject the oldest entry (the seventh EARS sentence, and
the processing of the second quoted sentence). Offers are never a line of a block (glossary
`GlossaryExec.lean`). -/
def Env003Covers {N T : Type} [DecidableEq N] (E : XRel N T) : Prop :=
  ∀ C s k p x rest, s.phase = .events → Live C s → s.mode.closing = false →
    s.eq = (k, p, x) :: rest → ∃ s', E C s (.inject k) s'

/-- The reference meets ENV-003's coverage conjunct: its inject rule takes the head of the queue
in every such state (`Env003.offer`). -/
theorem env003_ref_covers {N T : Type} [DecidableEq N] :
    Env003Covers (RefExec (N := N) (T := T)) :=
  fun _ _ _ _ _ _ hp hl hc he => Env003.offer hp hl hc he

/-! ### Examples

A net with no transitions and two environment places, `0` and `1`; place `0` starts with token
`9`. Every decided run below starts from the initial state and is decided by evaluation. -/

/-- The configuration of the examples. -/
def env003_c : Cfg Nat Nat :=
  { X := { net := { places := [0, 1], transitions := [] }, timing := fun _ => .immediate,
           tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [0, 1], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => false,
    res := 0 }

/-- The initial state: `9` in place `0`. -/
def env003_s0 : XSt Nat Nat := xinit (fun p => if p = 0 then [9] else []) 0

/-- Two events accepted, `7` into place `0` (ticket `0`) and `8` into place `1` (ticket `1`), then
step 1 and step 1b end: the loop is in step 2 with both queued. -/
def env003_two : List (XLbl Nat Nat) :=
  [.request 0 7 .accepted, .request 1 8 .accepted, .endCompletions, .endPublications]

/-- A run that finishes: step 2 ends with nothing queued, then `7` is accepted for place `0`
(ticket `0`) and the executor drains; the cycle finds work queued, so the pass is empty and the
loop injects the event from the wait; the next cycle finishes quiescent. -/
def env003_late : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .request 0 7 .accepted, .drain, .update,
   .deadline [], .begin, .endPass, .inject 0, .endCompletions, .endPublications, .endEvents,
   .update, .deadline [], .finish .quiescent]

/-- The test derivation: ten events accepted for place `0`, tokens `10` to `19` (tickets `0` to
`9`), the executor drains, step 2 injects all ten, and the run finishes quiescent. -/
def env003_ten : List (XLbl Nat Nat) :=
  (List.range 10).map (fun i => .request 0 (10 + i) .accepted) ++
  [.drain, .endCompletions, .endPublications] ++ (List.range 10).map (fun i => .inject i) ++
  [.endEvents, .update, .deadline [], .finish .quiescent]

/-- A close after an accepted event: the event is discarded and the run finishes closed. -/
def env003_closed : List (XLbl Nat Nat) :=
  [.request 0 7 .accepted, .close, .endCompletions, .endPublications, .discard 0, .endEvents,
   .update, .deadline [], .finish .closed]

/-- The trace of a run of the step function `g`, if every label is a step. -/
def env003Trace {N T : Type} (g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T))
    (C : Cfg N T) : XSt N T → List (XLbl N T) → Option (List (XStep N T))
  | _, [] => some []
  | s, l :: ls => (g C s l).bind fun s' => (env003Trace g C s' ls).map ((s, l, s') :: ·)

/-- A trace `env003Trace g` builds is a run of `g`'s graph. -/
theorem env003Trace_run {N T : Type} {g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)}
    {C : Cfg N T} : ∀ {s : XSt N T} {ls : List (XLbl N T)} {tr : List (XStep N T)},
      env003Trace g C s ls = some tr → XRun (fun C s l s' => g C s l = some s') C s tr
  | s, [], tr, h => by cases h; trivial
  | s, l :: ls, tr, h => by
    simp only [env003Trace] at h
    cases hs : g C s l with
    | none => simp [hs] at h
    | some s' =>
      simp only [hs, Option.bind_some] at h
      cases ht : env003Trace g C s' ls with
      | none => simp [ht] at h
      | some tr' =>
        simp only [ht, Option.map_some, Option.some.injEq] at h
        subst h
        exact ⟨rfl, hs, env003Trace_run ht⟩

/-- Read a decided fact `p` off the trace of a label run. -/
theorem env003_of_check {N T : Type} {g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)}
    {C : Cfg N T} {s : XSt N T} {ls : List (XLbl N T)} {p : List (XStep N T) → Bool}
    (h : (env003Trace g C s ls).map p = some true) :
    ∃ tr, env003Trace g C s ls = some tr ∧ p tr = true := by
  cases ht : env003Trace g C s ls with
  | none => simp [ht] at h
  | some tr => simp only [ht, Option.map_some, Option.some.injEq] at h; exact ⟨tr, rfl, h⟩

/-! ### Violation: the token lands at the call -/

/-- An executor that applies an accepted injection at the call: the token goes into the marking
and nothing is queued (the Novel spike ApplyInPlace). -/
def env003_atCallStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .request p x r => (xstep C s (.request p x r)).map fun s₁ =>
      if r = .accepted then { s with M := qAppendOne s.M p x, parked := false } else s₁
  | l => xstep C s l

/-- The executor of `env003_atCallStep`. -/
def env003_atCall {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env003_atCallStep C s l = some s'

/-- ✗ Applying the token at the call violates ENV-003 (line 1): the accepted `7` is in place `0`
right after the request. -/
@[evidence forbids ENV_003]
theorem ENV_003_forbids_atCall : ¬ ENV_003 (env003_atCall (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env003_atCallStep (C := env003_c)
    (o := some env003_s0) (l := .request 0 7 .accepted)
    (p := fun s s' => s'.M 0 != s.M 0) (by decide)
  have := congrArg XSt.M ((h env003_c).1 0 7 s s' hs)
  simp [this] at hp

/-! ### Violation: a stack instead of a queue -/

/-- An executor that pushes an accepted event at the head of its queue. -/
def env003_headQueueStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .request p x r => (xstep C s (.request p x r)).map fun s₁ =>
      if r = .accepted then { s₁ with eq := (s.nextId, p, x) :: s.eq } else s₁
  | l => xstep C s l

/-- The executor of `env003_headQueueStep`. -/
def env003_headQueue {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env003_headQueueStep C s l = some s'

/-- ✗ A stack violates ENV-003 (line 1, the tail): with `7` queued, `8` is pushed in front of
it. -/
@[evidence forbids ENV_003]
theorem ENV_003_forbids_headQueue : ¬ ENV_003 (env003_headQueue (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env003_headQueueStep (C := env003_c)
    (o := xrun env003_c env003_s0 [.request 0 7 .accepted]) (l := .request 1 8 .accepted)
    (p := fun s s' => s'.eq != s.eq ++ [(s.nextId, 1, 8)]) (by decide)
  have := congrArg XSt.eq ((h env003_c).1 1 8 s s' hs)
  simp [this] at hp

/-! ### Violation: a reused ticket -/

/-- An executor that queues an accepted event under the supply's value without moving the supply
on: the next event gets the same ticket. -/
def env003_reusesTicketStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .request p x r => (xstep C s (.request p x r)).map fun s₁ =>
      if r = .accepted then { s₁ with nextId := s.nextId } else s₁
  | l => xstep C s l

/-- The executor of `env003_reusesTicketStep`. -/
def env003_reusesTicket {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env003_reusesTicketStep C s l = some s'

/-- ✗ Reusing a ticket violates ENV-003 (line 1, the entry's own ticket): the supply stays at `0`
after the accepted request. -/
@[evidence forbids ENV_003]
theorem ENV_003_forbids_reusesTicket :
    ¬ ENV_003 (env003_reusesTicket (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env003_reusesTicketStep (C := env003_c)
    (o := some env003_s0) (l := .request 0 7 .accepted)
    (p := fun s s' => s'.nextId != s.nextId + 1) (by decide)
  have := congrArg XSt.nextId ((h env003_c).1 0 7 s s' hs)
  simp [this] at hp

/-! ### Violation: the newest event first -/

/-- An executor that injects the newest queued event, ticket `k`, and leaves the older ones. -/
def env003_newestFirstStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .inject k =>
    match s.eq.getLast? with
    | some (j, p, x) =>
      if j == k && liveB C s && !s.mode.closing && (s.phase = .events || s.phase = .await) then
        some { s with M := qAppendOne s.M p x, st := unreap C [p] s.st, eq := s.eq.dropLast,
                      phase := if s.phase = .await then .completions else s.phase,
                      parked := false }
      else none
    | none => none
  | l => xstep C s l

/-- The executor of `env003_newestFirstStep`. -/
def env003_newestFirst {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env003_newestFirstStep C s l = some s'

/-- ✗ Injecting the newest event first violates ENV-003 (line 2, the oldest entry): with tickets
`0` and `1` queued, ticket `1` is injected. -/
@[evidence forbids ENV_003]
theorem ENV_003_forbids_newestFirst :
    ¬ ENV_003 (env003_newestFirst (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env003_newestFirstStep (C := env003_c)
    (o := xrun env003_c env003_s0 env003_two) (l := .inject 1)
    (p := fun s _ => s.eq.head?.map (·.1) != some 1) (by decide)
  obtain ⟨p, x, rest, heq, -⟩ := (h env003_c).2.1 1 s s' hs
  simp [heq] at hp

/-! ### Violation: the injected token at the head of its place -/

/-- An executor that puts an injected token at the head of its place instead of the tail. -/
def env003_headOfPlaceStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .inject k => (xstep C s (.inject k)).bind fun s₁ => s.eq.head?.map fun (_, p, x) =>
      { s₁ with M := fun q => if q = p then x :: s.M q else s.M q }
  | l => xstep C s l

/-- The executor of `env003_headOfPlaceStep`. -/
def env003_headOfPlace {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env003_headOfPlaceStep C s l = some s'

/-- ✗ Putting the injected token at the head of its place violates ENV-003 (line 2, the tail):
place `0` holds `9`, and the injected `7` lands in front of it. -/
@[evidence forbids ENV_003]
theorem ENV_003_forbids_headOfPlace :
    ¬ ENV_003 (env003_headOfPlace (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env003_headOfPlaceStep (C := env003_c)
    (o := xrun env003_c env003_s0 env003_two) (l := .inject 0)
    (p := fun s s' => s.eq.head? == some (0, 0, 7) && s'.M 0 != s.M 0 ++ [7]) (by decide)
  obtain ⟨p, x, rest, heq, -, hM⟩ := (h env003_c).2.1 0 s s' hs
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, heq, List.head?_cons,
    Option.some.injEq, Prod.mk.injEq, true_and] at hp
  obtain ⟨⟨rfl, rfl⟩, hne⟩ := hp
  exact hne (by rw [hM]; simp [qAppendOne])

/-! ### Violation: the injected event stays queued -/

/-- An executor whose injection leaves the injected event in the queue. -/
def env003_keepsQueuedStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .inject k => (xstep C s (.inject k)).map fun s₁ => { s₁ with eq := s.eq }
  | l => xstep C s l

/-- The executor of `env003_keepsQueuedStep`. -/
def env003_keepsQueued {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env003_keepsQueuedStep C s l = some s'

/-- ✗ Leaving the injected event queued violates ENV-003 (line 2, removed from the queue): after
injecting ticket `0`, ticket `0` is still the head, to be injected again. -/
@[evidence forbids ENV_003]
theorem ENV_003_forbids_keepsQueued :
    ¬ ENV_003 (env003_keepsQueued (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env003_keepsQueuedStep (C := env003_c)
    (o := xrun env003_c env003_s0 env003_two) (l := .inject 0)
    (p := fun s s' => s'.eq != s.eq.drop 1) (by decide)
  obtain ⟨p, x, rest, heq, hr, -⟩ := (h env003_c).2.1 0 s s' hs
  simp [heq, hr] at hp

/-! ### Violation: one queue per place -/

/-- An executor that keeps one queue per place: when step 2 begins, the events of the oldest
event's place come first, the others after them, so the order across places is lost. -/
def env003_perPlaceQueuesStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .endPublications => (xstep C s .endPublications).map fun s₁ =>
      match s.eq with
      | (_, p0, _) :: _ =>
        { s₁ with eq := s.eq.filter (·.2.1 == p0) ++ s.eq.filter (·.2.1 != p0) }
      | [] => s₁
  | l => xstep C s l

/-- The executor of `env003_perPlaceQueuesStep`. -/
def env003_perPlaceQueues {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env003_perPlaceQueuesStep C s l = some s'

/-- ✗ One queue per place violates ENV-003 (line 3): events for places `0`, `1`, `0` are accepted
in that order, and step 2 begins with the second event for place `0` ahead of the one for place
`1`. -/
@[evidence forbids ENV_003]
theorem ENV_003_forbids_perPlaceQueues :
    ¬ ENV_003 (env003_perPlaceQueues (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env003_perPlaceQueuesStep (C := env003_c)
    (o := xrun env003_c env003_s0
      [.request 0 7 .accepted, .request 1 8 .accepted, .request 0 6 .accepted, .endCompletions])
    (l := .endPublications) (p := fun s s' => s'.eq != s.eq) (by decide)
  have := (h env003_c).2.2.1 .endPublications rfl s s' hs
  simp [this] at hp

/-! ### Violation: the end of step 2 drops what is still queued -/

/-- An executor whose step 2 walks a fixed prefix of the queue and then clears the whole queue:
the TypeScript `processExternalEvents` reading `const len = this.externalQueue.length` and ending
with `this.externalQueue.length = 0` instead of dropping only what it deposited. An `inject()` made
during the walk is dropped. In the model, the end of step 2 empties the queue whatever is still
queued. -/
def env003_clearsAtEndStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .endEvents =>
    if s.phase = .events && liveB C s then some { s with phase := .update, eq := [] } else none
  | l => xstep C s l

/-- The executor of `env003_clearsAtEndStep`. -/
def env003_clearsAtEnd {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env003_clearsAtEndStep C s l = some s'

/-- ✗ Clearing the queue at the end of step 2 violates ENV-003 (line 3): `7` is injected, `8`
was accepted during the walk, and the end of step 2 drops it. -/
@[evidence forbids ENV_003]
theorem ENV_003_forbids_clearsAtEnd :
    ¬ ENV_003 (env003_clearsAtEnd (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env003_clearsAtEndStep (C := env003_c)
    (o := xrun env003_c env003_s0
      [.request 0 7 .accepted, .endCompletions, .endPublications, .request 1 8 .accepted,
       .inject 0])
    (l := .endEvents) (p := fun s s' => s.eq == [(1, 1, 8)] && s'.eq != s.eq) (by decide)
  have := (h env003_c).2.2.1 .endEvents rfl s s' hs
  simp [this] at hp

/-! ### Violation: a discard that reorders the queue -/

/-- An executor whose discard moves the head of the queue to its tail instead of dropping it:
nothing is lost, every event is still injected or dropped later, but the order is not the order
of acceptance. -/
def env003_rotatesStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .discard k => (xstep C s (.discard k)).map fun s₁ => { s₁ with eq := s₁.eq ++ s.eq.take 1 }
  | l => xstep C s l

/-- The executor of `env003_rotatesStep`. -/
def env003_rotates {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env003_rotatesStep C s l = some s'

/-- ✗ A discard that moves the head to the tail violates ENV-003 (line 4): with tickets `0` and
`1` queued and the executor closed, the discard of `0` leaves `1` ahead of `0`. -/
@[evidence forbids ENV_003]
theorem ENV_003_forbids_rotates : ¬ ENV_003 (env003_rotates (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env003_rotatesStep (C := env003_c)
    (o := xrun env003_c env003_s0
      [.request 0 7 .accepted, .request 1 8 .accepted, .close, .endCompletions,
       .endPublications])
    (l := .discard 0) (p := fun s s' => !(s'.eq.isSublist s.eq)) (by decide)
  have := (h env003_c).2.2.2.1 (.discard 0) rfl s s' hs
  simp [List.isSublist_iff_sublist.mpr this] at hp

/-! ### Violation: an accepted request that does not wake the loop -/

/-- An executor whose accepted request leaves the parked flag as it was: a loop blocked in its
wait stays blocked with the event queued. -/
def env003_noWakeStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .request p x r => (xstep C s (.request p x r)).map fun s₁ =>
      if r = .accepted then { s₁ with parked := s.parked } else s₁
  | l => xstep C s l

/-- The executor of `env003_noWakeStep`. -/
def env003_noWake {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env003_noWakeStep C s l = some s'

/-- The first cycle with nothing enabled, then the loop blocks in its wait with no timer. -/
def env003_parked : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin, .endPass,
   .park none]

/-- ✗ Not waking the loop violates ENV-003 (line 1, the wake): the loop is blocked, `7` is
accepted, and the loop is still blocked after the request. -/
@[evidence forbids ENV_003]
theorem ENV_003_forbids_noWake : ¬ ENV_003 (env003_noWake (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env003_noWakeStep (C := env003_c)
    (o := xrun env003_c env003_s0 env003_parked) (l := .request 0 7 .accepted)
    (p := fun _ s' => s'.parked) (by decide)
  have := congrArg XSt.parked ((h env003_c).1 0 7 s s' hs)
  simp [this] at hp

/-! ### Violation: a termination test that forgets queued events -/

/-- An executor whose termination test reads only the transitions, the firings in flight and the
completion and publication queues, not the event queue (rest as "no enabled transitions and no
in-flight", the original EXEC-040 wording): it finishes quiescent and drops what is queued. -/
def env003_forgetsStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .finish .quiescent =>
    if s.phase = .test && liveB C s &&
        (C.X.net.transitions.all (fun u => !armedB s u) && s.fl.isEmpty && s.cq.isEmpty &&
          s.pq.isEmpty) && (C.envs.isEmpty || s.mode != .open) then
      some { s with phase := .done .quiescent, eq := [] }
    else none
  | l => xstep C s l

/-- The executor of `env003_forgetsStep`. -/
def env003_forgets {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env003_forgetsStep C s l = some s'

/-- The run of `env003_late` up to its first termination test, then the finish the forgetful
test allows there. -/
def env003_forgetRun : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .request 0 7 .accepted, .drain, .update,
   .deadline [], .finish .quiescent]

/-- ✗ A termination test that forgets queued events violates ENV-003 (line 6): `7` is accepted
after step 2, the executor drains, and the run finishes quiescent at the next test with the event
never injected and no close, termination or terminal stop. The executor keeps lines 1 to 5 and
the offer of `Env003Covers`; only line 6 catches it. -/
@[evidence forbids ENV_003]
theorem ENV_003_forbids_forgets : ¬ ENV_003 (env003_forgets (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨tr, ht, hp⟩ := env003_of_check (g := env003_forgetsStep) (C := env003_c)
    (s := env003_s0) (ls := env003_forgetRun)
    (p := fun tr => !isExecPhase (XRun.last env003_s0 tr).phase &&
      !(whenShall (Env003.accepts 0) (Env003.serves env003_c 0)).scan false tr) (by decide)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  have hw : (whenShall (Env003.accepts 0) (Env003.serves env003_c 0)).scan false tr = true :=
    (h env003_c).2.2.2.2.2 env003_s0 0 tr ⟨env003Trace_run ht, hp.1⟩
  rw [hp.2] at hw
  exact Bool.false_ne_true hw

/-! ### Violation: a ticket supply that goes back -/

/-- An executor that resets the ticket supply at the enablement update: an event accepted after
the reset gets a ticket an earlier queued event already holds. -/
def env003_resetsSupplyStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .update => (xstep C s .update).map fun s₁ => { s₁ with nextId := 0 }
  | l => xstep C s l

/-- The executor of `env003_resetsSupplyStep`. -/
def env003_resetsSupply {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env003_resetsSupplyStep C s l = some s'

/-- `7` accepted under ticket `0` after step 2, the update resets the supply, and `8` is accepted
under ticket `0` as well. -/
def env003_resetRun : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .request 0 7 .accepted, .update,
   .request 1 8 .accepted]

/-- ✗ Resetting the ticket supply violates ENV-003 (line 5): the update after the first
acceptance lowers the supply from `1` to `0`. -/
@[evidence forbids ENV_003]
theorem ENV_003_forbids_resetsSupply :
    ¬ ENV_003 (env003_resetsSupply (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env003_resetsSupplyStep (C := env003_c)
    (o := xrun env003_c env003_s0 (env003_resetRun.take 4)) (l := .update)
    (p := fun s s' => decide (s'.nextId < s.nextId)) (by decide)
  have := (h env003_c).2.2.2.2.1 .update s s' hs
  simp only [decide_eq_true_eq] at hp
  omega

/-- What the reset breaks: on `env003_resetRun` the two accepted calls share ticket `0`, so an
injection of ticket `0` cannot say which call it answers, and the watch of line 6, one flag per
ticket, would let one injection pay both acceptances. -/
theorem env003_resetsSupply_sharesTicket :
    ∃ tr, env003Trace env003_resetsSupplyStep env003_c env003_s0 env003_resetRun = some tr ∧
      (XRun.last env003_s0 tr).eq = [(0, 0, 7), (0, 1, 8)] := by
  obtain ⟨tr, ht, hp⟩ := env003_of_check (g := env003_resetsSupplyStep) (C := env003_c)
    (s := env003_s0) (ls := env003_resetRun)
    (p := fun tr => (XRun.last env003_s0 tr).eq == [(0, 0, 7), (0, 1, 8)]) (by decide)
  exact ⟨tr, ht, by simpa using hp⟩

/-! ### Violation: a terminal stop latched at the call -/

/-- An executor that stops on a terminal place as soon as an event for a terminal place is
queued, before its token is in the marking: the TypeScript EXEC-042 latch
`terminalFlags[pid] → terminalReached` moved from `processExternalEvents` into `inject()`, or
Java's `isTerminal` test placed next to `externalEventQueue.offer`. The loop exits with reason
terminal and drops every queued event, those accepted earlier for other places included. -/
def env003_latchTerminalStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .finish .terminal =>
    if isExecPhase s.phase && (!liveB C s || s.eq.any (fun e => decide (e.2.1 ∈ C.terminals)))
    then some { s with phase := .done .terminal, eq := [], pq := [] } else none
  | l => xstep C s l

/-- The executor of `env003_latchTerminalStep`. -/
def env003_latchTerminal {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env003_latchTerminalStep C s l = some s'

/-- The examples' net with place `1` terminal. -/
def env003_termC : Cfg Nat Nat := { env003_c with terminals := [1] }

/-- ✗ Latching the terminal stop at the call violates ENV-003 (line 6, a terminal stop releases
only when a terminal place is marked): `7` is accepted for place `0` (ticket `0`), `8` for the
terminal place `1`, and the executor stops with no terminal place marked and `7` never
injected. -/
@[evidence forbids ENV_003]
theorem ENV_003_forbids_latchTerminal :
    ¬ ENV_003 (env003_latchTerminal (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨tr, ht, hp⟩ := env003_of_check (g := env003_latchTerminalStep) (C := env003_termC)
    (s := env003_s0) (ls := [.request 0 7 .accepted, .request 1 8 .accepted, .finish .terminal])
    (p := fun tr => !isExecPhase (XRun.last env003_s0 tr).phase &&
      !(whenShall (Env003.accepts 0) (Env003.serves env003_termC 0)).scan false tr) (by decide)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  have hw : (whenShall (Env003.accepts 0) (Env003.serves env003_termC 0)).scan false tr = true :=
    (h env003_termC).2.2.2.2.2 env003_s0 0 tr ⟨env003Trace_run ht, hp.1⟩
  rw [hp.2] at hw
  exact Bool.false_ne_true hw

/-! ### Coverage: step 2 never injects -/

/-- An executor with the inject rule removed: Java's `processExternalEvents` guard inverted or
widened, the TypeScript early return reading the wrong flag, or Rust's Phase 2 polling a receiver
that `inject` never sends on. The termination test still sees the queue, so the loop never
finishes: a drained executor with an event queued is stuck in step 2. Every step of it is a step
of the reference, so every line holds of it (`env003_of_sub`); only the coverage clause
`Env003Covers` catches it. -/
def env003_noInjectStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .inject _ => none
  | l => xstep C s l

/-- The executor of `env003_noInjectStep`. -/
def env003_noInject {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env003_noInjectStep C s l = some s'

/-- A run of an executor is a run of every executor that has all its steps. -/
theorem env003_run_sub {N T : Type} {R R' : XRel N T}
    (hsub : ∀ C s l s', R C s l s' → R' C s l s') {C : Cfg N T} :
    ∀ {s : XSt N T} {tr : List (XStep N T)}, XRun R C s tr → XRun R' C s tr
  | _, [], _ => trivial
  | _, _ :: _, ⟨h1, h2, h3⟩ => ⟨h1, hsub _ _ _ _ h2, env003_run_sub hsub h3⟩

/-- Every line of ENV-003 reads only the steps and the finished runs of the executor, so an
executor whose steps are all steps of the reference satisfies ENV-003. -/
theorem env003_of_sub {N T : Type} [DecidableEq N] {R : XRel N T}
    (hsub : ∀ C s l s', R C s l s' → RefExec C s l s') : ENV_003 R := by
  intro C
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ENV_003_reference (N := N) (T := T) C
  exact ⟨fun p x s s' h => h1 p x s s' (hsub _ _ _ _ h),
    fun k s s' h => h2 k s s' (hsub _ _ _ _ h),
    fun l hk s s' h => h3 l hk s s' (hsub _ _ _ _ h),
    fun l hd s s' h => h4 l hd s s' (hsub _ _ _ _ h),
    fun l s s' h => h5 l s s' (hsub _ _ _ _ h),
    fun s0 k tr hi => h6 s0 k tr ⟨env003_run_sub hsub hi.1, hi.2⟩⟩

/-- Every step of `env003_noInject` is a step of the reference. -/
theorem env003_noInject_sub {N T : Type} [DecidableEq N] {C : Cfg N T} {s s' : XSt N T}
    {l : XLbl N T} (h : env003_noInject C s l s') : RefExec C s l s' := by
  cases l with
  | inject k => simp [env003_noInject, env003_noInjectStep] at h
  | _ => exact h

/-- The injection in step 2 is coverage, not a line: an executor whose step 2 never injects meets
every line of ENV-003 (`env003_of_sub`) and fails its coverage conjunct `Env003Covers` (the
seventh EARS sentence): `7` is accepted, the executor drains, steps 1 and 1b end, and in step 2,
with no terminal place marked and `7` queued, the executor offers no injection. -/
@[evidence cites "ENV-003" "while the orchestrator is in the external-events step of a cycle, no terminal place is marked, the executor is neither closed nor terminated immediately and its queue of accepted events is not empty, the orchestrator shall inject the oldest entry: an executor whose step 2 never injects meets every line of the block and fails its coverage clause Env003Covers in ExecCoversW5"]
theorem env003_covers_noInject :
    ENV_003 (env003_noInject (N := Nat) (T := Nat)) ∧
      ¬ Env003Covers (env003_noInject (N := Nat) (T := Nat)) := by
  refine ⟨env003_of_sub fun _ _ _ _ h => env003_noInject_sub h, fun h => ?_⟩
  obtain ⟨s, -, -, -, hp⟩ := step_of_check xstep (C := env003_c)
    (o := xrun env003_c env003_s0
      [.request 0 7 .accepted, .drain, .endCompletions, .endPublications])
    (l := .inject 0)
    (p := fun s _ => s.phase == .events && liveB env003_c s && !s.mode.closing &&
      s.eq == [(0, 0, 7)]) (by decide)
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hp
  obtain ⟨⟨⟨hph, hl⟩, hc⟩, he⟩ := hp
  obtain ⟨s', hs'⟩ := h env003_c s 0 0 7 [] hph hl hc he
  simp [env003_noInject, env003_noInjectStep] at hs'

/-! ### The exception of line 6 is needed -/

/-- The reference allows an accepted event that is never injected: `7` is accepted, the executor
closes, step 2 discards the event and the run finishes closed. So the unconditional reading of AC3
is false of the reference, and line 6 needs its release by a close (clash env-a#7, ruling D20). -/
@[evidence allows ENV_003]
theorem ENV_003_allows_closeDiscards :
    ∃ tr, IdealRun RefExec env003_c env003_s0 tr ∧ tr.any (Env003.accepts 0) = true ∧
      tr.any (Env003.injects 0) = false := by
  obtain ⟨tr, ht, hp⟩ := env003_of_check (g := xstep) (C := env003_c) (s := env003_s0)
    (ls := env003_closed)
    (p := fun tr => !isExecPhase (XRun.last env003_s0 tr).phase &&
      tr.any (Env003.accepts 0) && !tr.any (Env003.injects 0)) (by decide)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  exact ⟨tr, ⟨env003Trace_run ht, hp.1.1⟩, hp.1.2, hp.2⟩

/-! ### Every line exercised -/

/-- Every line of ENV-003 is exercised by the reference: (1) an accepted request queues its event
under ticket `0`; (2) with tickets `0` and `1` queued, injecting `0` appends `7` behind the `9`
place `0` already holds and leaves ticket `1` queued; (3) step 1b ends with two events queued and
keeps them; (4) the run `env003_late` accepts ticket `0`, injects it from the wait and finishes;
(5) the test derivation: ten accepted events, injected in acceptance order behind `9`, and the run
finishes; (6) after a close, a discard drops ticket `0` and keeps ticket `1` (line 4). Part 1
moves the supply on (line 5). -/
@[evidence nonvacuous ENV_003]
theorem ENV_003_nonvacuous :
    (∃ s s', RefExec env003_c s (.request 0 7 .accepted) s' ∧ s'.eq = [(0, 0, 7)]) ∧
    (∃ s s', RefExec env003_c s (.inject 0) s' ∧ s.eq.length = 2 ∧ s'.M 0 = [9, 7] ∧
      s'.eq = [(1, 1, 8)]) ∧
    (∃ s s', RefExec env003_c s .endPublications s' ∧ s'.eq.length = 2) ∧
    (∃ tr, IdealRun RefExec env003_c env003_s0 tr ∧ tr.any (Env003.accepts 0) = true ∧
      tr.any (Env003.injects 0) = true) ∧
    (∃ tr, IdealRun RefExec env003_c env003_s0 tr ∧
      (List.range 10).all (fun k => tr.any (Env003.accepts k) && tr.any (Env003.injects k)) ∧
      (XRun.last env003_s0 tr).M 0 = 9 :: (List.range 10).map (10 + ·)) ∧
    (∃ s s', RefExec env003_c s (.discard 0) s' ∧ s.eq = [(0, 0, 7), (1, 1, 8)] ∧
      s'.eq = [(1, 1, 8)]) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env003_c) (o := some env003_s0)
      (l := .request 0 7 .accepted) (p := fun _ s' => s'.eq == [(0, 0, 7)]) (by decide)
    exact ⟨s, s', hs, by simpa using hp⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env003_c)
      (o := xrun env003_c env003_s0 env003_two) (l := .inject 0)
      (p := fun s s' => s.eq.length == 2 && s'.M 0 == [9, 7] && s'.eq == [(1, 1, 8)])
      (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', hs, hp.1.1, hp.1.2, hp.2⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env003_c)
      (o := xrun env003_c env003_s0 (env003_two.take 3)) (l := .endPublications)
      (p := fun _ s' => s'.eq.length == 2) (by decide)
    exact ⟨s, s', hs, by simpa using hp⟩
  · obtain ⟨tr, ht, hp⟩ := env003_of_check (g := xstep) (C := env003_c) (s := env003_s0)
      (ls := env003_late)
      (p := fun tr => !isExecPhase (XRun.last env003_s0 tr).phase &&
        tr.any (Env003.accepts 0) && tr.any (Env003.injects 0)) (by decide)
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
    exact ⟨tr, ⟨env003Trace_run ht, hp.1.1⟩, hp.1.2, hp.2⟩
  · obtain ⟨tr, ht, hp⟩ := env003_of_check (g := xstep) (C := env003_c) (s := env003_s0)
      (ls := env003_ten)
      (p := fun tr => !isExecPhase (XRun.last env003_s0 tr).phase &&
        (List.range 10).all (fun k => tr.any (Env003.accepts k) && tr.any (Env003.injects k)) &&
        (XRun.last env003_s0 tr).M 0 == 9 :: (List.range 10).map (10 + ·)) (by decide)
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hp
    exact ⟨tr, ⟨env003Trace_run ht, hp.1.1⟩, hp.1.2, hp.2⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env003_c)
      (o := xrun env003_c env003_s0
        [.request 0 7 .accepted, .request 1 8 .accepted, .close, .endCompletions,
         .endPublications])
      (l := .discard 0)
      (p := fun s s' => s.eq == [(0, 0, 7), (1, 1, 8)] && s'.eq == [(1, 1, 8)]) (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', hs, hp.1, hp.2⟩

end Libpetri.Spec
