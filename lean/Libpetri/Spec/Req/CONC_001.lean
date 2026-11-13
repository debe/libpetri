import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Exec
import Libpetri.Spec.Text.CONC_001

set_option linter.missingDocs true

/-!
# CONC-001: Orchestrator thread ownership (`spec/05-concurrency.md`)

A requirement block over the executor model (`RefExec`, `Reference/Exec.lean`). The labels of an
executor step (glossary `GlossaryExec.lean`) split into the steps the orchestrator takes (the
phases of [EXEC-001]) and the **outside steps** (`XLbl.outside`): an action writing, flushing or
returning, the budget of an action expiring, a caller requesting an injection, draining, closing
or terminating the executor, and the firing clock advancing. Thread identity is not observable in
a step relation; "owned and mutated exclusively by the orchestrator" is read as "changed only by
the orchestrator's own steps, and the token queues only by its starts and deposits", and the
hand-off of AC3 as "what an outside step hands over is applied by a later orchestrator step, never
before it was handed over".

The statement is a predicate over an abstract executor `R : XRel N T`, with seven lines: an
outside step changes neither the clock status of any transition name nor the state of the
orchestrator's current cycle; a step that neither starts a firing nor deposits changes no token
queue; and, on every run that starts with nothing in flight and nothing queued, no commit of a
firing precedes its return, no timeout deposit precedes its expiry, no settle without a deposit
precedes its return or expiry, no publication of a firing precedes its first flush, and no
injection precedes the accepted request that queued it. The evidence checks it against the
reference executor (`CONC_001_reference`), against executors whose outside steps write a clock or
the cycle state (a return that re-arms its transition, a return that pushes its transition onto
the ready order), against executors that write the token queues in a step that is no deposit (a
return that deposits at once, a flush that lands in the marking at the call, an injection applied
at the call, a snapshot that folds running actions' buffers in), and against executors whose
orchestrator takes what was not handed over (a commit of an action still running, a commit of an
expiry, a timeout outcome no expiry handed back, a settle of a running firing, a publication of
tokens never flushed, an injection of a refused request).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## The events the lines speak of -/

section Events

variable {N T : Type}

/-- The outcome is a returned emission. -/
def conc001Ok : Option (Outcome N T) → Bool
  | some (.ok _) => true
  | _ => false

/-- The outcome is a timeout outcome. -/
def conc001Timed : Option (Outcome N T) → Bool
  | some (.timedOut _) => true
  | _ => false

/-- The step is the return of firing `i`'s action (normally or not). -/
def conc001Returned (i : Nat) (e : XStep N T) : Bool :=
  match e.2.1 with
  | .ret j _ => j == i
  | _ => false

/-- The step is the expiry of firing `i`'s budget. -/
def conc001Expired (i : Nat) (e : XStep N T) : Bool :=
  match e.2.1 with
  | .expire j _ => j == i
  | _ => false

/-- The step hands firing `i`'s outcome back to the orchestrator: its action returns, or its
budget expires. -/
def conc001Ended (i : Nat) (e : XStep N T) : Bool :=
  conc001Returned i e || conc001Expired i e

/-- The step deposits firing `i`'s returned emission (`commit`). -/
def conc001Committed (i : Nat) (e : XStep N T) : Bool :=
  match e.2.1 with
  | .commit j => j == i
  | _ => false

/-- The step deposits firing `i`'s timeout outcome (`tdeposit`). -/
def conc001TDeposited (i : Nat) (e : XStep N T) : Bool :=
  match e.2.1 with
  | .tdeposit j => j == i
  | _ => false

/-- The step settles firing `i` without a deposit (`fail`). -/
def conc001Failed (i : Nat) (e : XStep N T) : Bool :=
  match e.2.1 with
  | .fail j => j == i
  | _ => false

/-- The step is a flush of firing `i`'s action (a mid-action publication, [IO-015]). -/
def conc001Flushed (i : Nat) (e : XStep N T) : Bool :=
  match e.2.1 with
  | .flush j => j == i
  | _ => false

/-- The step deposits a publication of firing `i` (step 1b). -/
def conc001Published (i : Nat) (e : XStep N T) : Bool :=
  match e.2.1 with
  | .publish j => j == i
  | _ => false

/-- The step is an injection request the executor accepts, and it newly queues an event with
ticket `k`: the event queue after the step holds ticket `k` and the one before did not. Whatever
the executor's numbering of tickets, this is the request that handed event `k` over. -/
def conc001Queued (k : Nat) (e : XStep N T) : Bool :=
  match e.2.1 with
  | .request _ _ .accepted => e.2.2.eq.any (·.1 == k) && !e.1.eq.any (·.1 == k)
  | _ => false

/-- The step injects the queued event with ticket `k` (step 2). -/
def conc001Injected (k : Nat) (e : XStep N T) : Bool :=
  match e.2.1 with
  | .inject j => j == k
  | _ => false

end Events

/-! ## CONC-001: Orchestrator Thread Ownership -/

requirement CONC_001
  id "CONC-001"
  title "Orchestrator Thread Ownership"
  kind B
  scope "all executors"
  source verbatim "spec/05-concurrency.md"
  covers CONC_001.s1, CONC_001.s2, CONC_001.s3, CONC_001.s4, CONC_001.s5, CONC_001.s6
  reading "For every executor R and every configuration C:"
          "an outside step (an action writing, flushing, returning or expiring, a caller requesting an injection, draining, closing or terminating the executor, the clock advancing) leaves the clock status of every transition name, the loop phase, the cycle's clock reading, the rest of the pass's ready order, the pass's same-pass tail and the pass's started flag as they were;"
          "a step that is neither a start nor a deposit (a commit, a timeout deposit, a publication, an injection) leaves the marking as it was;"
          "on every run of R that starts with no firing in flight, no publication queued and no event queued, and for every firing identity i: no commit of i comes before the first return of the action of i;"
          "on every such run, for every firing identity i: no timeout deposit of i comes before the first expiry of the budget of i;"
          "on every such run, for every firing identity i: no settle of i without a deposit comes before the first step in which the action of i returns or its budget expires;"
          "on every such run, for every firing identity i: no step deposits a publication of i before the first flush of the action of i;"
          "on every such run, for every ticket k: no step injects the event with ticket k before the first accepted injection request that newly queues an event with ticket k."
  assumes "The model is an executor R : XRel N T (glossary GlossaryExec.lean): R C s l s' says that under configuration C the step labelled l leads from executor state s to s'. The labels are split once, in the glossary, into the steps of the orchestrator loop ([EXEC-001]: settling, publication, injection, the snapshot answer, the update, the deadline step, the termination test, the firing pass, the wait) and the outside steps (XLbl.outside: write, flush, ret, expire, request, drain, close, terminateNow, delay). The witness is the reference executor RefExec (Reference/Exec.lean), the graph of a step function checked rule by rule against the Rust executor."
          "Naming: 'marking state' is the marking (XSt.M, the token queues) and the clock status by transition name (XSt.st: whether a name is armed, its stamp, the restart flag, reaped), which is the runtimes' enablement flag and enabled-at timestamp. 'The orchestrator' is the orchestrator loop of EXEC-001, a logical thread: Java runs it on one thread and also invokes actions inline on it, TypeScript has one thread, Rust and Python run it as one task. The orchestrator's current cycle is the loop phase (XSt.phase), the cycle reading the update and the deadline step take (XSt.cyc), the rest of the pass's ready order (XSt.order, the runtimes' ready queues and Java's dirty set), whether the pass has started a transition (XSt.started) and the same-pass tail (XSt.delta, which defines the pass-visible marking). They are not marking state, but only the orchestrator keeps them, and an outside step that wrote them would act on the marking or the clocks through the orchestrator's next step: a transition pushed onto the order starts out of turn, and a cleared tail shows the pass tokens it deposited itself. Line 1 does not frame the firings in flight, the three queues, the ticket supply, the lifecycle mode, the host reading XSt.now or the parked flag: handing over, closing and waking the loop are what outside steps do."
          "A step relation does not observe threads, so 'owned and mutated exclusively by a single logical orchestrator thread' is read as lines 1 and 2, the first and second EARS sentences: no step that is not the orchestrator's changes a clock status or the current cycle, and no step changes a token queue unless it starts a firing or deposits. Every outside step is neither a start nor a deposit, so by line 2 it leaves the token queues as they were. Line 2 also binds the orchestrator's own steps: a settle without a deposit, the snapshot answer, the update, the deadline step, the termination test, the end markers, a lost start, the wait and a discard change no token. A return that deposits its emission at once (CONC_001_forbids_depositAtReturn), a flush that lands its batch in the marking at the call (CONC_001_forbids_publishAtFlush), an injection applied at the call (CONC_001_forbids_injectAtCall) and a snapshot answer that first folds the buffers of the running actions into the marking (CONC_001_forbids_freshSnapshot) break line 2; a return that re-arms its transition at the call (CONC_001_forbids_rearmAtReturn) and a completion callback that pushes its transition onto the ready order (CONC_001_forbids_orderAtReturn) break line 1. Neither line says what a start or a deposit writes, or which clocks the orchestrator's steps set: that is EXEC-001, EXEC-020, EXEC-021, EXEC-022, IO-015 (publication), ENV-003 (injection) and the TIME blocks."
          "Lines 3 to 7 are AC3 ('communicated back via a thread-safe mechanism, then applied on the orchestrator thread') and the third to fifth EARS sentences. The hand-off is the outside step that queues a firing's outcome (ret, expire), a batch (flush) or an event (an accepted request); 'then applied' is the orchestrator step that settles or deposits it (commit, tdeposit, fail, publish, inject). The third EARS sentence pairs them: produced tokens with a return (line 3), a timeout outcome with an expiry (line 4), a settle without a deposit with either (line 5). An orchestrator that commits what a running action has written so far (CONC_001_forbids_commitUnreturned), one that commits an emission an expiry handed back (CONC_001_forbids_commitAtExpiry), one that deposits a timeout outcome no expiry handed back (CONC_001_forbids_selfTimeout), one that settles a running firing without a deposit, so that a transition that is not re-entrant may start again (CONC_001_forbids_failUnreturned), one that publishes an action's buffer without a flush (CONC_001_forbids_publishUnflushed), and one that queues and injects a request it refused (CONC_001_forbids_queueRefused) break lines 3, 3, 4, 5, 6 and 7. That a deposit is exactly what was handed over (the returned emission, the flushed batch, the injected token) is EXEC-020, EXEC-021, CONC-003 and ENV-003; that each is deposited at most once is EXEC-020 and ENV-004. The thread safety of the hand-off (a lock-free queue, a channel, a promise callback) is the representation (kind Q) and is not encoded."
          "Lines 3 to 7 are read on runs that start with no firing in flight, no publication queued and no event queued, which every executor's initial state is (xinit). They speak of the first hand-off of an identity. The model names one firing by one identity and one event by one ticket, both drawn from one supply (XSt.nextId, as EXEC-021, EXEC-030 and EXEC-031 read it), and the reference hands out a fresh one at every start and every accepted request, so there 'before the first' hand-off is 'before its only one'. An executor that hands one identity to two firings, or one ticket to two events, is outside that naming convention, which no requirement states, and the lines bind only the first firing or event of an identity. Line 7 does not fix how tickets are numbered: the request that hands event k over is the accepted request that newly queues ticket k."
          "Ruling D43 (a): only the orchestrator writes the marking, and a thread other than the orchestrator may read it as [ENV-014] allows. AC2 is reworded accordingly: its write half is lines 1 and 2. Its read half is not a line: in the model the snapshot answer is an orchestrator step (Java's foreign read of a parked executor, ENV-014 AC9, and its last published marking after the 2 s cap are ENV-014's subject and are outside this model), and line 2 binds it to leave the token queues as they were, so no line about writes depends on who reads."
          "The body sentence 'No locking or synchronization is needed for marking access.' and AC1 (the marking has no locks, mutexes or atomic operations) are about the representation (kind Q): a step relation does not observe a lock. They follow from the reading of lines 1 and 2 when the orchestrator is one thread of control, and are checked by inspection, as the test derivation says ('Inspect marking implementation for absence of synchronization primitives.'); not encoded. Java asserts the ownership at run time (BitmapNetExecutor)."
          "AC3 is lines 1 to 7 as said above; the Rust executor's completion, flush and signal channels (executor_core/executor.rs handle_completion, handle_flush, handle_signal), Java's completion queue and TypeScript's promise callbacks are its mechanisms."
          "The 'Kind' line is B, the kind of the encoded lines (one-letter convention, ruling D21); AC1, the thread identity of AC2 and the thread safety of AC3 are Q content without a line."
  signoff "2026-11-13 1d951f4b3445aece ai"
  statement : ∀ {N T : Type} [DecidableEq N], XRel N T → Prop :=
    fun R => ∀ C,
      (∀ l, l.outside = true →
        on (fun s s' => R C s l s'), shall (fun s s' => s'.st = s.st ∧ s'.phase = s.phase ∧
          s'.cyc = s.cyc ∧ s'.order = s.order ∧ s'.delta = s.delta ∧ s'.started = s.started)) ∧
      (∀ l, startOrDeposit l = false →
        on (fun s s' => R C s l s'), shall (fun s s' => s'.M = s.M)) ∧
      (∀ s0 tr, s0.fl = [] → s0.pq = [] → s0.eq = [] → XRun R C s0 tr →
        (∀ i, (until conc001Returned i, never conc001Committed i) tr) ∧
        (∀ i, (until conc001Expired i, never conc001TDeposited i) tr) ∧
        (∀ i, (until conc001Ended i, never conc001Failed i) tr) ∧
        (∀ i, (until conc001Flushed i, never conc001Published i) tr) ∧
        (∀ k, (until conc001Queued k, never conc001Injected k) tr))

/- The pinned readable form of CONC-001: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CONC_001 : {N T : Type} → [DecidableEq N] → XRel N T → Prop :=
fun {N T} [DecidableEq N] R =>
  ∀ (C : Cfg N T),
    (∀ (l : XLbl N T),
        l.outside = true →
          on fun s s' => R C s l s', shall fun s s' =>
            s'.st = s.st ∧
              s'.phase = s.phase ∧ s'.cyc = s.cyc ∧ s'.order = s.order ∧ s'.delta = s.delta ∧ s'.started = s.started) ∧
      (∀ (l : XLbl N T), startOrDeposit l = false → on fun s s' => R C s l s', shall fun s s' => s'.M = s.M) ∧
        ∀ (s0 : XSt N T) (tr : List (XStep N T)),
          s0.fl = [] →
            s0.pq = [] →
              s0.eq = [] →
                XRun R C s0 tr →
                  (∀ (i : ℕ), (until conc001Returned i, never conc001Committed i) tr) ∧
                    (∀ (i : ℕ), (until conc001Expired i, never conc001TDeposited i) tr) ∧
                      (∀ (i : ℕ), (until conc001Ended i, never conc001Failed i) tr) ∧
                        (∀ (i : ℕ), (until conc001Flushed i, never conc001Published i) tr) ∧
                          ∀ (k : ℕ), (until conc001Queued k, never conc001Injected k) tr
-/
#guard_msgs in #print CONC_001

/-! ### The reference -/

section Reference

variable {N T : Type} [DecidableEq N]

omit [DecidableEq N] in
/-- If no step before the first `go` of a run is `bad`, from a state where `I` holds, and every
step that is not a `go` keeps `I`, then `until go, never bad` holds of every run from such a
state. -/
theorem conc001_untilNever {E : XRel N T} {C : Cfg N T} (I : XSt N T → Prop)
    (go bad : XStep N T → Bool)
    (hpres : ∀ s l s', E C s l s' → I s → go (s, l, s') = false → I s')
    (hbad : ∀ s l s', E C s l s' → I s → bad (s, l, s') = false) :
    ∀ s0 tr, I s0 → XRun E C s0 tr → (until go, never bad) tr := by
  have hdone : ∀ tr : List (XStep N T), (untilNever go bad).scan true tr = true := by
    intro tr
    induction tr with
    | nil => rfl
    | cons e rest ih =>
      show ((true || !bad e) && (untilNever go bad).scan (true || go e) rest) = true
      simp [ih]
  intro s0 tr
  induction tr generalizing s0 with
  | nil => intro _ _; rfl
  | cons e rest ih =>
    intro hI hr
    obtain ⟨a, l, b⟩ := e
    obtain ⟨rfl, hs, hrest⟩ := hr
    show (untilNever go bad).scan false ((a, l, b) :: rest) = true
    simp only [Watch.scan, untilNever, hbad a l b hs hI, Bool.not_false, Bool.or_true,
      Bool.true_and, Bool.false_or]
    cases hg : go (a, l, b)
    · exact ih b (hpres a l b hs hI hg) hrest
    · exact hdone rest

/-- Line 1 of the reference: an outside step keeps every clock status and the state of the
current cycle. -/
theorem conc001_outside {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T} (h : RefExec C s l s')
    (ho : l.outside = true) :
    s'.st = s.st ∧ s'.phase = s.phase ∧ s'.cyc = s.cyc ∧ s'.order = s.order ∧
      s'.delta = s.delta ∧ s'.started = s.started := by
  cases l with
  | delay δ => cases xstepW_delay h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | write i p x =>
    obtain ⟨f, -, -, rfl⟩ := writeStep_some h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | flush i =>
    obtain ⟨f, -, -, -, -, ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ := flushStep_some h <;>
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | ret i ok => obtain ⟨f, -, -, rfl⟩ := retStep_some h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | expire i e =>
    obtain ⟨f, -, -, -, -, -, rfl⟩ := expireStep_some h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | request p x r =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := requestStep_some h <;>
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | drain => obtain ⟨-, rfl⟩ := drainStep_some h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | close => obtain ⟨-, rfl⟩ := closeStep_some h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | terminateNow =>
    obtain ⟨-, rfl⟩ := terminateStep_some h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | _ => simp [XLbl.outside] at ho

/-- Line 2 of the reference: a step that is neither a start nor a deposit keeps the marking. -/
theorem conc001_tokens {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T} (h : RefExec C s l s')
    (hd : startOrDeposit l = false) : s'.M = s.M := by
  cases l with
  | start _ _ | commit _ | tdeposit _ | publish _ | inject _ => simp [startOrDeposit] at hd
  | delay _ | write _ _ _ | flush _ | ret _ _ | expire _ _ | request _ _ _ | drain | close
  | terminateNow => exact (xstepW_outside_frame h rfl).1
  | fail i => obtain ⟨f, -, -, -, rfl⟩ := failStep_some (P := refXPol) h; rfl
  | endCompletions => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endCompletions h; rfl
  | endPublications => obtain ⟨-, -, -, rfl⟩ := xstepW_endPublications h; rfl
  | discard k => obtain ⟨p, x, rest, -, -, -, -, rfl⟩ := discardStep_some h; rfl
  | endEvents => obtain ⟨-, -, -, rfl⟩ := xstepW_endEvents h; rfl
  | snapshot a => obtain ⟨-, -, -, rfl⟩ := snapshotStep_some h; rfl
  | update => obtain ⟨-, -, rfl⟩ := xstepW_update h; rfl
  | deadline ns => obtain ⟨-, -, -, rfl⟩ := xstepW_deadline h; rfl
  | finish c =>
    cases c with
    | quiescent => obtain ⟨-, -, -, rfl⟩ := xstepW_finishQuiescent h; rfl
    | closed => obtain ⟨-, -, -, -, rfl⟩ := xstepW_finishClosed h; rfl
    | terminal => obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h; rfl
    | stopped => obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h; rfl
  | begin => obtain ⟨-, -, -, -, rfl⟩ := xstepW_begin h; rfl
  | lose n => obtain ⟨t, rest, -, -, -, -, -, -, rfl⟩ := loseStep_some (P := refXPol) h; rfl
  | endPass => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endPass h; rfl
  | park tmr => obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := parkStep_some h; rfl
  | wake => obtain ⟨-, -, rfl⟩ := wakeStep_some h; rfl

omit [DecidableEq N] in
/-- A member of an updated firing list is an updated member (with the identity updated) or an
untouched one. -/
theorem conc001_mem_updFiring {s : XSt N T} {i : Nat} {h : Firing N T → Firing N T}
    {f : Firing N T} (hf : f ∈ updFiring s i h) :
    ∃ g ∈ s.fl, (g.id = i ∧ f = h g) ∨ (g.id ≠ i ∧ f = g) := by
  unfold updFiring at hf
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
  by_cases hid : g.id = i
  · exact ⟨g, hg, Or.inl ⟨hid, by simp [hid]⟩⟩
  · exact ⟨g, hg, Or.inr ⟨hid, by simp [hid]⟩⟩

/-- What one step does to the firings in flight, the publication queue and the event queue: a
firing after the step has no outcome, or it was in flight before with the same identity and
either the same outcome, or the step is its return and the outcome is no timeout outcome, or the
step is its expiry and the outcome is no returned emission; a queued publication was queued
before or the step is its flush; a queued event was queued before or the step is an accepted
request. -/
def conc001Frame (s : XSt N T) (l : XLbl N T) (s' : XSt N T) : Prop :=
  (∀ f ∈ s'.fl, f.out = none ∨ ∃ g ∈ s.fl, g.id = f.id ∧
      (g.out = f.out ∨ (∃ ok, l = .ret f.id ok ∧ conc001Timed f.out = false) ∨
        ∃ e, l = .expire f.id e ∧ conc001Ok f.out = false)) ∧
  (∀ b ∈ s'.pq, b ∈ s.pq ∨ l = .flush b.1) ∧
  (∀ v ∈ s'.eq, v ∈ s.eq ∨ ∃ p x, l = .request p x .accepted)

omit [DecidableEq N] in
/-- A step that only removes firings and queue entries keeps the frame. -/
theorem conc001Frame_sub {s s' : XSt N T} {l : XLbl N T} (hfl : ∀ f ∈ s'.fl, f ∈ s.fl)
    (hpq : ∀ b ∈ s'.pq, b ∈ s.pq) (heq : ∀ v ∈ s'.eq, v ∈ s.eq) : conc001Frame s l s' :=
  ⟨fun f hf => Or.inr ⟨f, hfl f hf, rfl, Or.inl rfl⟩, fun b hb => Or.inl (hpq b hb),
    fun v hv => Or.inl (heq v hv)⟩

omit [DecidableEq N] in
/-- An update of firing `i` that keeps every identity and outcome keeps the frame. -/
theorem conc001Frame_upd {s : XSt N T} {l : XLbl N T} {i : Nat} {h : Firing N T → Firing N T}
    (hid : ∀ g, (h g).id = g.id) (hout : ∀ g, (h g).out = g.out) :
    ∀ f ∈ updFiring s i h, f.out = none ∨ ∃ g ∈ s.fl, g.id = f.id ∧
      (g.out = f.out ∨ (∃ ok, l = .ret f.id ok ∧ conc001Timed f.out = false) ∨
        ∃ e, l = .expire f.id e ∧ conc001Ok f.out = false) := by
  intro f hf
  obtain ⟨g, hg, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := conc001_mem_updFiring hf
  · exact Or.inr ⟨g, hg, (hid g).symm, Or.inl (hout g).symm⟩
  · exact Or.inr ⟨_, hg, rfl, Or.inl rfl⟩

/-- Every step of the reference executor keeps the frame. -/
theorem conc001_frame {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T} (h : RefExec C s l s') :
    conc001Frame s l s' := by
  have hsub : ∀ {s₁ : XSt N T}, s₁.fl = s.fl → s₁.pq = s.pq → s₁.eq = s.eq →
      conc001Frame s l s₁ := fun hf hp he =>
    conc001Frame_sub (fun f h => hf ▸ h) (fun b h => hp ▸ h) (fun v h => he ▸ h)
  have hset : ∀ {i : Nat} {e : List (N × T)} {s₁ : XSt N T}, s₁.fl = (settle s i).fl →
      s₁.pq = s.pq → s₁.eq = s.eq → conc001Frame s l s₁ := fun hf hp he =>
    conc001Frame_sub (fun f h => by rw [hf] at h; exact List.mem_of_mem_filter h)
      (fun b h => hp ▸ h) (fun v h => he ▸ h)
  cases l with
  | delay δ => cases xstepW_delay h; exact hsub rfl rfl rfl
  | write i p x =>
    obtain ⟨f, -, -, rfl⟩ := writeStep_some h
    exact ⟨conc001Frame_upd (fun _ => rfl) (fun _ => rfl), fun b hb => Or.inl hb,
      fun v hv => Or.inl hv⟩
  | flush i =>
    obtain ⟨f, -, -, -, -, ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ := flushStep_some h
    · refine ⟨conc001Frame_upd (fun _ => rfl) (fun _ => rfl), fun b hb => ?_,
        fun v hv => Or.inl hv⟩
      rcases List.mem_append.mp hb with hb | hb
      · exact Or.inl hb
      · simp only [List.mem_singleton] at hb
        subst hb
        exact Or.inr rfl
    · exact ⟨conc001Frame_upd (fun _ => rfl) (fun _ => rfl), fun b hb => Or.inl hb,
        fun v hv => Or.inl hv⟩
  | ret i ok =>
    obtain ⟨f, -, -, rfl⟩ := retStep_some h
    refine ⟨fun g hg => ?_, fun b hb => Or.inl hb, fun v hv => Or.inl hv⟩
    obtain ⟨g₀, hg₀, ⟨hid, rfl⟩ | ⟨-, rfl⟩⟩ := conc001_mem_updFiring hg
    · refine Or.inr ⟨g₀, hg₀, rfl, Or.inr (Or.inl ⟨ok, by rw [hid], ?_⟩)⟩
      dsimp only
      split <;> rfl
    · exact Or.inr ⟨_, hg₀, rfl, Or.inl rfl⟩
  | expire i e =>
    obtain ⟨f, -, -, -, -, -, rfl⟩ := expireStep_some h
    refine ⟨fun g hg => ?_, fun b hb => Or.inl hb, fun v hv => Or.inl hv⟩
    obtain ⟨g₀, hg₀, ⟨hid, rfl⟩ | ⟨-, rfl⟩⟩ := conc001_mem_updFiring hg
    · refine Or.inr ⟨g₀, hg₀, rfl, Or.inr (Or.inr ⟨e, by rw [hid], ?_⟩)⟩
      dsimp only
      split <;> rfl
    · exact Or.inr ⟨_, hg₀, rfl, Or.inl rfl⟩
  | request p x r =>
    obtain ⟨-, ⟨rfl, rfl⟩ | ⟨-, rfl⟩⟩ := requestStep_some h
    · refine ⟨fun f hf => Or.inr ⟨f, hf, rfl, Or.inl rfl⟩, fun b hb => Or.inl hb,
        fun v hv => ?_⟩
      rcases List.mem_append.mp hv with hv | hv
      · exact Or.inl hv
      · exact Or.inr ⟨p, x, rfl⟩
    · exact hsub rfl rfl rfl
  | drain => obtain ⟨-, rfl⟩ := drainStep_some h; exact hsub rfl rfl rfl
  | close => obtain ⟨-, rfl⟩ := closeStep_some h; exact hsub rfl rfl rfl
  | terminateNow =>
    obtain ⟨-, rfl⟩ := terminateStep_some h
    exact conc001Frame_sub (fun f h => h) (fun b h => h) (fun v h => by simp at h)
  | commit i =>
    obtain ⟨f, e, -, -, -, -, -, rfl⟩ := commitStep_some (P := refXPol) h
    exact hset (i := i) (e := e) rfl rfl rfl
  | fail i =>
    obtain ⟨f, -, -, -, rfl⟩ := failStep_some (P := refXPol) h
    exact hset (i := i) (e := []) rfl rfl rfl
  | tdeposit i =>
    obtain ⟨f, e, -, -, -, -, rfl⟩ := tdepositStep_some h
    exact hset (i := i) (e := e) rfl rfl rfl
  | endCompletions =>
    obtain ⟨-, -, -, -, rfl⟩ := xstepW_endCompletions h; exact hsub rfl rfl rfl
  | publish i =>
    obtain ⟨b, rest, hpq, -, -, rfl⟩ := publishStep_some h
    exact conc001Frame_sub (fun f h => h) (fun c hc => by rw [hpq]; exact List.mem_cons_of_mem _ hc)
      (fun v h => h)
  | endPublications =>
    obtain ⟨-, -, -, rfl⟩ := xstepW_endPublications h; exact hsub rfl rfl rfl
  | inject k =>
    obtain ⟨p, x, rest, heq, -, -, -, rfl⟩ := injectStep_some h
    exact conc001Frame_sub (fun f h => h) (fun b h => h)
      (fun v hv => by rw [heq]; exact List.mem_cons_of_mem _ hv)
  | discard k =>
    obtain ⟨p, x, rest, heq, -, -, -, rfl⟩ := discardStep_some h
    exact conc001Frame_sub (fun f h => h) (fun b h => h)
      (fun v hv => by rw [heq]; exact List.mem_cons_of_mem _ hv)
  | endEvents => obtain ⟨-, -, -, rfl⟩ := xstepW_endEvents h; exact hsub rfl rfl rfl
  | snapshot a => obtain ⟨-, -, -, rfl⟩ := snapshotStep_some h; exact hsub rfl rfl rfl
  | update => obtain ⟨-, -, rfl⟩ := xstepW_update h; exact hsub rfl rfl rfl
  | deadline ns => obtain ⟨-, -, -, rfl⟩ := xstepW_deadline h; exact hsub rfl rfl rfl
  | finish c =>
    cases c with
    | quiescent =>
      obtain ⟨-, -, -, rfl⟩ := xstepW_finishQuiescent h
      exact conc001Frame_sub (fun f h => h) (fun b h => h) (fun v h => by simp at h)
    | closed =>
      obtain ⟨-, -, -, -, rfl⟩ := xstepW_finishClosed h
      exact conc001Frame_sub (fun f h => h) (fun b h => h) (fun v h => by simp at h)
    | terminal =>
      obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h
      exact conc001Frame_sub (fun f h => h) (fun b h => by simp at h) (fun v h => by simp at h)
    | stopped =>
      obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h
      exact conc001Frame_sub (fun f h => h) (fun b h => by simp at h) (fun v h => by simp at h)
  | begin => obtain ⟨-, -, -, -, rfl⟩ := xstepW_begin h; exact hsub rfl rfl rfl
  | start n sy =>
    obtain ⟨t, rest, -, -, -, -, -, -, -, rfl⟩ := startStep_some (P := refXPol) h
    refine ⟨fun f hf => ?_, fun b hb => Or.inl hb, fun v hv => Or.inl hv⟩
    rcases List.mem_append.mp hf with hf | hf
    · exact Or.inr ⟨f, hf, rfl, Or.inl rfl⟩
    · simp only [List.mem_singleton] at hf
      subst hf
      exact Or.inl rfl
  | lose n => obtain ⟨t, rest, -, -, -, -, -, -, rfl⟩ := loseStep_some (P := refXPol) h
              exact hsub rfl rfl rfl
  | endPass => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endPass h; exact hsub rfl rfl rfl
  | park tmr =>
    obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := parkStep_some h; exact hsub rfl rfl rfl
  | wake => obtain ⟨-, -, rfl⟩ := wakeStep_some h; exact hsub rfl rfl rfl

/-- Line 3 of the reference: before the return of firing `i`, no firing with identity `i` holds
a returned emission, so no commit of `i` deposits. -/
theorem conc001_line3 (C : Cfg N T) (i : Nat) :
    ∀ s0 tr, s0.fl = [] → XRun RefExec C s0 tr →
      (until conc001Returned i, never conc001Committed i) tr := by
  intro s0 tr h0 hr
  refine conc001_untilNever (fun s => ∀ f ∈ s.fl, f.id = i → conc001Ok f.out = false) _ _ ?_ ?_
    s0 tr (by simp [h0]) hr
  · intro s l s' hs hI hgo f hf hid
    rcases (conc001_frame hs).1 f hf with h | ⟨g, hg, hgid, ho | ⟨ok, rfl, -⟩ | ⟨e, rfl, he⟩⟩
    · rw [h]; rfl
    · rw [← ho]; exact hI g hg (hgid.trans hid)
    · simp [conc001Returned, hid] at hgo
    · exact he
  · intro s l s' hs hI
    cases l with
    | commit j =>
      simp only [conc001Committed, beq_eq_false_iff_ne]
      rintro rfl
      obtain ⟨f, e, hf, he, -⟩ := commitStep_some (P := refXPol) hs
      have := hI f (List.mem_of_find?_eq_some hf) (by simpa using List.find?_some hf)
      simp [he, conc001Ok] at this
    | _ => rfl

/-- Line 4 of the reference: before the expiry of firing `i`, no firing with identity `i` holds
a timeout outcome, so no timeout deposit of `i` happens. -/
theorem conc001_line4 (C : Cfg N T) (i : Nat) :
    ∀ s0 tr, s0.fl = [] → XRun RefExec C s0 tr →
      (until conc001Expired i, never conc001TDeposited i) tr := by
  intro s0 tr h0 hr
  refine conc001_untilNever (fun s => ∀ f ∈ s.fl, f.id = i → conc001Timed f.out = false) _ _
    ?_ ?_ s0 tr (by simp [h0]) hr
  · intro s l s' hs hI hgo f hf hid
    rcases (conc001_frame hs).1 f hf with h | ⟨g, hg, hgid, ho | ⟨ok, rfl, he⟩ | ⟨e, rfl, -⟩⟩
    · rw [h]; rfl
    · rw [← ho]; exact hI g hg (hgid.trans hid)
    · exact he
    · simp [conc001Expired, hid] at hgo
  · intro s l s' hs hI
    cases l with
    | tdeposit j =>
      simp only [conc001TDeposited, beq_eq_false_iff_ne]
      rintro rfl
      obtain ⟨f, e, hf, he, -⟩ := tdepositStep_some hs
      have := hI f (List.mem_of_find?_eq_some hf) (by simpa using List.find?_some hf)
      simp [he, conc001Timed] at this
    | _ => rfl

/-- Line 5 of the reference: before the return or expiry of firing `i`, every firing with
identity `i` has no outcome, so no settle of `i` without a deposit happens. -/
theorem conc001_line5 (C : Cfg N T) (i : Nat) :
    ∀ s0 tr, s0.fl = [] → XRun RefExec C s0 tr →
      (until conc001Ended i, never conc001Failed i) tr := by
  intro s0 tr h0 hr
  refine conc001_untilNever (fun s => ∀ f ∈ s.fl, f.id = i → f.out = none) _ _ ?_ ?_ s0 tr
    (by simp [h0]) hr
  · intro s l s' hs hI hgo f hf hid
    rcases (conc001_frame hs).1 f hf with h | ⟨g, hg, hgid, ho | ⟨ok, rfl, -⟩ | ⟨e, rfl, -⟩⟩
    · exact h
    · rw [← ho]; exact hI g hg (hgid.trans hid)
    · simp [conc001Ended, conc001Returned, hid] at hgo
    · simp [conc001Ended, conc001Returned, conc001Expired, hid] at hgo
  · intro s l s' hs hI
    cases l with
    | fail j =>
      simp only [conc001Failed, beq_eq_false_iff_ne]
      rintro rfl
      obtain ⟨f, hf, -, hc, -⟩ := failStep_some (P := refXPol) hs
      have := hI f (List.mem_of_find?_eq_some hf) (by simpa using List.find?_some hf)
      simp [failCause, this] at hc
    | _ => rfl

/-- Line 6 of the reference: before the first flush of firing `i`, no publication of `i` is
queued, so none is deposited. -/
theorem conc001_line6 (C : Cfg N T) (i : Nat) :
    ∀ s0 tr, s0.pq = [] → XRun RefExec C s0 tr →
      (until conc001Flushed i, never conc001Published i) tr := by
  intro s0 tr h0 hr
  refine conc001_untilNever (fun s => ∀ b ∈ s.pq, b.1 ≠ i) _ _ ?_ ?_ s0 tr (by simp [h0]) hr
  · intro s l s' hs hI hgo b hb hid
    rcases (conc001_frame hs).2.1 b hb with h | rfl
    · exact hI b h hid
    · simp [conc001Flushed, hid] at hgo
  · intro s l s' hs hI
    cases l with
    | publish j =>
      simp only [conc001Published, beq_eq_false_iff_ne]
      rintro rfl
      obtain ⟨b, rest, hpq, -⟩ := publishStep_some hs
      exact hI (j, b) (by rw [hpq]; exact List.mem_cons_self ..) rfl
    | _ => rfl

/-- Line 7 of the reference: before the accepted request that newly queues ticket `k`, no event
with ticket `k` is queued, so none is injected. -/
theorem conc001_line7 (C : Cfg N T) (k : Nat) :
    ∀ s0 tr, s0.eq = [] → XRun RefExec C s0 tr →
      (until conc001Queued k, never conc001Injected k) tr := by
  intro s0 tr h0 hr
  refine conc001_untilNever (fun s => ∀ v ∈ s.eq, v.1 ≠ k) _ _ ?_ ?_ s0 tr (by simp [h0]) hr
  · intro s l s' hs hI hgo v hv hid
    rcases (conc001_frame hs).2.2 v hv with h | ⟨p, x, rfl⟩
    · exact hI v h hid
    · have h1 : s'.eq.any (·.1 == k) = true := List.any_eq_true.mpr ⟨v, hv, by simp [hid]⟩
      have h2 : s.eq.any (·.1 == k) = false := by
        rw [List.any_eq_false]
        intro w hw
        simpa using hI w hw
      simp [conc001Queued, h1, h2] at hgo
  · intro s l s' hs hI
    cases l with
    | inject j =>
      simp only [conc001Injected, beq_eq_false_iff_ne]
      rintro rfl
      obtain ⟨p, x, rest, heq, -⟩ := injectStep_some hs
      exact hI (j, p, x) (by rw [heq]; exact List.mem_cons_self ..) rfl
    | _ => rfl

end Reference

/-- ✓ The reference executor satisfies CONC-001: an outside step keeps every clock status and the
state of the current cycle (`conc001_outside`), a step that neither starts nor deposits keeps the
marking (`conc001_tokens`), and every step keeps the frame of the firings' outcomes and the two
queues (`conc001_frame`), so a commit, a timeout deposit, a settle without a deposit, a
publication and an injection each need the outside step that handed it over first. -/
@[evidence holds CONC_001]
theorem CONC_001_reference {N T : Type} [DecidableEq N] :
    CONC_001 (RefExec (N := N) (T := T)) := by
  intro C
  exact ⟨fun l ho s s' h => conc001_outside h ho, fun l hd s s' h => conc001_tokens h hd,
    fun s0 tr hfl hpq heq hr =>
      ⟨fun i => conc001_line3 C i s0 tr hfl hr, fun i => conc001_line4 C i s0 tr hfl hr,
        fun i => conc001_line5 C i s0 tr hfl hr, fun i => conc001_line6 C i s0 tr hpq hr,
        fun k => conc001_line7 C k s0 tr heq hr⟩⟩

/-! ### Examples

One transition `t` takes a token from place `0` (an environment place) and has the output spec
`And(1, Timeout(d, 2))`; validation and the relay check accept everything, and the timeout
outcome goes to place `2`. -/

/-- The transition of the examples. -/
def conc001T : Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.and (.place 1) (.timeout (.place 2))) }

/-- The configuration of the examples. -/
def conc001C : Cfg Nat Nat :=
  { X := { net := { places := [0, 1, 2], transitions := [conc001T] },
           timing := fun _ => .immediate, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [0], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true,
    timeoutOut := fun _ _ e => e.map Prod.fst == [2], res := 0 }

/-- The initial marking: one token `7` in place `0`. -/
def conc001M0 : QMarking Nat Nat := fun p => if p = 0 then [7] else []

/-- One cycle up to an asynchronous start of `t` (firing `0`) and the end of the pass. -/
def conc001Pre : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin, .start "t" false,
    .endPass]

/-- The executor whose steps are given by `g`. -/
def conc001Graph {N T : Type} (g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)) :
    XRel N T :=
  fun C s l s' => g C s l = some s'

/-- The trace of a label run of the step function `g`, if every label is a step. -/
def conc001Trace {N T : Type} (g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T))
    (C : Cfg N T) : XSt N T → List (XLbl N T) → Option (List (XStep N T))
  | _, [] => some []
  | s, l :: ls => (g C s l).bind fun s' => (conc001Trace g C s' ls).map ((s, l, s') :: ·)

/-- A trace `conc001Trace` builds is a run of the executor of `g`. -/
theorem conc001Trace_run {N T : Type} {g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)}
    {C : Cfg N T} :
    ∀ {s : XSt N T} {ls : List (XLbl N T)} {tr : List (XStep N T)},
      conc001Trace g C s ls = some tr → XRun (conc001Graph g) C s tr
  | s, [], tr, h => by cases h; trivial
  | s, l :: ls, tr, h => by
    simp only [conc001Trace] at h
    cases hs : g C s l with
    | none => simp [hs] at h
    | some s' =>
      simp only [hs, Option.bind_some] at h
      cases ht : conc001Trace g C s' ls with
      | none => simp [ht] at h
      | some tr' =>
        simp only [ht, Option.map_some, Option.some.injEq] at h
        subst h
        exact ⟨rfl, hs, conc001Trace_run ht⟩

/-- Read a decided fact `p` off the trace of a label run of `g`. -/
theorem conc001_run_of_check {N T : Type}
    (g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)) {C : Cfg N T} {s0 : XSt N T}
    {ls : List (XLbl N T)} {p : List (XStep N T) → Bool}
    (h : (conc001Trace g C s0 ls).map p = some true) :
    ∃ tr, XRun (conc001Graph g) C s0 tr ∧ p tr = true := by
  cases ht : conc001Trace g C s0 ls with
  | none => simp [ht] at h
  | some tr => exact ⟨tr, conc001Trace_run ht, by simpa [ht] using h⟩

/-! ### Violations of line 1: an outside step writes a clock or the current cycle -/

/-- An executor whose `ret` re-arms the returning firing's transition at the call, stamping it
with the present reading. -/
def conc001_rearmAtReturnStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .ret i ok => (xstep C s (.ret i ok)).map fun s₁ =>
      match s.fl.find? (·.id == i) with
      | some f => { s₁ with st := fun n => if n = f.t.core.name then .armed s.now false else s₁.st n }
      | none => s₁
  | l => xstep C s l

/-- The executor of `conc001_rearmAtReturnStep`. -/
def conc001_rearmAtReturn {N T : Type} [DecidableEq N] : XRel N T :=
  conc001Graph conc001_rearmAtReturnStep

/-- ✗ A return that re-arms its transition at the call violates CONC-001 (line 1, the enablement
flags and timestamps): firing `0` of `t` returns, and the return step arms `t`, which its start
had turned off. -/
@[evidence forbids CONC_001]
theorem CONC_001_forbids_rearmAtReturn :
    ¬ CONC_001 (conc001_rearmAtReturn (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check conc001_rearmAtReturnStep (C := conc001C)
    (o := xrun conc001C (xinit conc001M0 0) (conc001Pre ++ [.write 0 1 5]))
    (l := .ret 0 true) (p := fun s s' => s'.st "t" != s.st "t") (by decide)
  have := ((h conc001C).1 (.ret 0 true) rfl s s' hs).1
  simp [this] at hp

/-- An executor whose `ret` also pushes the returning firing's transition onto the ready order
(the completion callback marks its transition dirty). -/
def conc001_orderAtReturnStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .ret i ok => (xstep C s (.ret i ok)).map fun s₁ =>
      match s.fl.find? (·.id == i) with
      | some f => { s₁ with order := s₁.order ++ [f.t] }
      | none => s₁
  | l => xstep C s l

/-- The executor of `conc001_orderAtReturnStep`. -/
def conc001_orderAtReturn {N T : Type} [DecidableEq N] : XRel N T :=
  conc001Graph conc001_orderAtReturnStep

/-- ✗ A completion callback that writes the ready order violates CONC-001 (line 1, the current
cycle): firing `0` of `t` returns, and the return step puts `t` onto the order, where the next
pass would start it out of turn. -/
@[evidence forbids CONC_001]
theorem CONC_001_forbids_orderAtReturn :
    ¬ CONC_001 (conc001_orderAtReturn (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check conc001_orderAtReturnStep (C := conc001C)
    (o := xrun conc001C (xinit conc001M0 0) (conc001Pre ++ [.write 0 1 5]))
    (l := .ret 0 true) (p := fun s s' => s'.order.length != s.order.length) (by decide)
  have := ((h conc001C).1 (.ret 0 true) rfl s s' hs).2.2.2.1
  simp [this] at hp

/-! ### Violations of line 2: a step that is no deposit writes the token queues -/

/-- An executor whose `ret` deposits what the action wrote at once, at the call; it settles as
the reference. -/
def conc001_depositAtReturnStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .ret i ok => (xstep C s (.ret i ok)).map fun s₁ =>
      match s.fl.find? (·.id == i) with
      | some f => if ok then { s₁ with M := qAppend s₁.M f.buf } else s₁
      | none => s₁
  | l => xstep C s l

/-- The executor of `conc001_depositAtReturnStep`. -/
def conc001_depositAtReturn {N T : Type} [DecidableEq N] : XRel N T :=
  conc001Graph conc001_depositAtReturnStep

/-- ✗ An action return that deposits at once violates CONC-001 (line 2): the action of firing `0`
writes `5` to place `1` and returns, and the return step puts `5` into place `1`. -/
@[evidence forbids CONC_001]
theorem CONC_001_forbids_depositAtReturn :
    ¬ CONC_001 (conc001_depositAtReturn (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check conc001_depositAtReturnStep (C := conc001C)
    (o := xrun conc001C (xinit conc001M0 0) (conc001Pre ++ [.write 0 1 5]))
    (l := .ret 0 true) (p := fun s s' => s'.M 1 != s.M 1) (by decide)
  have := (h conc001C).2.1 (.ret 0 true) rfl s s' hs
  simp [this] at hp

/-- An executor whose `flush` lands the batch in the marking at the call (and still queues it). -/
def conc001_publishAtFlushStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .flush i => (xstep C s (.flush i)).map fun s₁ =>
      match s.fl.find? (·.id == i) with
      | some f => { s₁ with M := qAppend s₁.M f.buf }
      | none => s₁
  | l => xstep C s l

/-- The executor of `conc001_publishAtFlushStep`. -/
def conc001_publishAtFlush {N T : Type} [DecidableEq N] : XRel N T :=
  conc001Graph conc001_publishAtFlushStep

/-- ✗ A publication that lands in the marking at the call violates CONC-001 (line 2): the action
of firing `0` writes `5` to place `1` and flushes, and the flush step puts `5` into place `1`. -/
@[evidence forbids CONC_001]
theorem CONC_001_forbids_publishAtFlush :
    ¬ CONC_001 (conc001_publishAtFlush (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check conc001_publishAtFlushStep (C := conc001C)
    (o := xrun conc001C (xinit conc001M0 0) (conc001Pre ++ [.write 0 1 5]))
    (l := .flush 0) (p := fun s s' => s'.M 1 != s.M 1) (by decide)
  have := (h conc001C).2.1 (.flush 0) rfl s s' hs
  simp [this] at hp

/-- An executor whose accepted `request` appends the token to the marking at the call. -/
def conc001_injectAtCallStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .request p x r => (xstep C s (.request p x r)).map fun s₁ =>
      if r = .accepted then { s₁ with M := qAppendOne s₁.M p x } else s₁
  | l => xstep C s l

/-- The executor of `conc001_injectAtCallStep`. -/
def conc001_injectAtCall {N T : Type} [DecidableEq N] : XRel N T :=
  conc001Graph conc001_injectAtCallStep

/-- ✗ An injection applied at the call violates CONC-001 (line 2): a caller requests to inject
`9` into the environment place `0`, and the request step puts `9` into place `0`. -/
@[evidence forbids CONC_001]
theorem CONC_001_forbids_injectAtCall :
    ¬ CONC_001 (conc001_injectAtCall (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check conc001_injectAtCallStep (C := conc001C)
    (o := some (xinit conc001M0 0)) (l := .request 0 9 .accepted)
    (p := fun s s' => s'.M 0 != s.M 0) (by decide)
  have := (h conc001C).2.1 (.request 0 9 .accepted) rfl s s' hs
  simp [this] at hp

/-- An executor whose snapshot answer first folds what every running action has written into the
marking, to answer with a "fresh" marking (the in-flight contexts' outputs drained before the
copy). -/
def conc001_freshSnapshotStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .snapshot a => (xstep C s (.snapshot a)).map fun s₁ =>
      { s₁ with M := qAppend s₁.M ((s.fl.filter (·.out.isNone)).flatMap (·.buf)) }
  | l => xstep C s l

/-- The executor of `conc001_freshSnapshotStep`. -/
def conc001_freshSnapshot {N T : Type} [DecidableEq N] : XRel N T :=
  conc001Graph conc001_freshSnapshotStep

/-- ✗ A snapshot answer that deposits the running actions' buffers violates CONC-001 (line 2):
the action of firing `0` writes `5` to place `1` and has not returned, and the snapshot step of
step 2 puts `5` into place `1`. -/
@[evidence forbids CONC_001]
theorem CONC_001_forbids_freshSnapshot :
    ¬ CONC_001 (conc001_freshSnapshot (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check conc001_freshSnapshotStep (C := conc001C)
    (o := xrun conc001C (xinit conc001M0 0)
      (conc001Pre ++ [.write 0 1 5, .endCompletions, .endPublications]))
    (l := .snapshot (some true)) (p := fun s s' => s'.M 1 != s.M 1) (by decide)
  have := (h conc001C).2.1 (.snapshot (some true)) rfl s s' hs
  simp [this] at hp

/-! ### Violations of lines 3 to 7: the orchestrator applies what was not handed over -/

/-- An executor whose orchestrator, in step 1, also commits a firing whose action has not
returned, depositing what it has written so far (it polls the action's buffer). -/
def conc001_commitUnreturnedStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .commit i =>
    match xstep C s (.commit i) with
    | some s' => some s'
    | none =>
      match s.fl.find? (·.id == i) with
      | some f =>
        if f.out.isNone && s.phase = .completions then some (depositAt C s i f.buf) else none
      | none => none
  | l => xstep C s l

/-- The executor of `conc001_commitUnreturnedStep`. -/
def conc001_commitUnreturned {N T : Type} [DecidableEq N] : XRel N T :=
  conc001Graph conc001_commitUnreturnedStep

/-- ✗ Committing an action that has not returned violates CONC-001 (line 3): the action of firing
`0` writes `5` to place `1`, and the next step 1 commits firing `0` before any return. -/
@[evidence forbids CONC_001]
theorem CONC_001_forbids_commitUnreturned :
    ¬ CONC_001 (conc001_commitUnreturned (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨tr, hr, hp⟩ := conc001_run_of_check conc001_commitUnreturnedStep (C := conc001C)
    (s0 := xinit conc001M0 0) (ls := conc001Pre ++ [.write 0 1 5, .commit 0])
    (p := fun tr => !(untilNever (conc001Returned 0) (conc001Committed 0)).scan false tr)
    (by decide)
  have h1 : (untilNever (conc001Returned 0) (conc001Committed 0)).scan false tr = true :=
    ((h conc001C).2.2 _ tr rfl rfl rfl hr).1 0
  simp [h1] at hp

/-- An executor whose expiry hands back what the action has written so far as a returned
emission (a timeout taken for a normal completion), which step 1 then commits. -/
def conc001_commitAtExpiryStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .expire i e => (xstep C s (.expire i e)).map fun s₁ =>
      { s₁ with fl := updFiring s₁ i fun g => { g with out := some (.ok g.buf) } }
  | l => xstep C s l

/-- The executor of `conc001_commitAtExpiryStep`. -/
def conc001_commitAtExpiry {N T : Type} [DecidableEq N] : XRel N T :=
  conc001Graph conc001_commitAtExpiryStep

/-- ✗ Committing produced tokens that an expiry, not a return, handed back violates CONC-001
(line 3, the pairing of produced tokens with a return): the action of firing `0` writes `5` to
place `1`, its budget expires, and step 1 commits firing `0` with no return before it. -/
@[evidence forbids CONC_001]
theorem CONC_001_forbids_commitAtExpiry :
    ¬ CONC_001 (conc001_commitAtExpiry (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨tr, hr, hp⟩ := conc001_run_of_check conc001_commitAtExpiryStep (C := conc001C)
    (s0 := xinit conc001M0 0) (ls := conc001Pre ++ [.write 0 1 5, .expire 0 [(2, 4)], .commit 0])
    (p := fun tr => !(untilNever (conc001Returned 0) (conc001Committed 0)).scan false tr)
    (by decide)
  have h1 : (untilNever (conc001Returned 0) (conc001Committed 0)).scan false tr = true :=
    ((h conc001C).2.2 _ tr rfl rfl rfl hr).1 0
  simp [h1] at hp

/-- An executor whose orchestrator, in step 1, decides the timeout of an asynchronous firing with
a `Timeout` node itself and deposits the timeout outcome `2 ↦ 0` while the action still runs,
with no expiry of its budget handed back. -/
def conc001_selfTimeoutStep (C : Cfg Nat Nat) (s : XSt Nat Nat) :
    XLbl Nat Nat → Option (XSt Nat Nat)
  | .tdeposit i =>
    match xstep C s (.tdeposit i) with
    | some s' => some s'
    | none =>
      match s.fl.find? (·.id == i) with
      | some f =>
        if f.out.isNone && !f.sync && hasTimeoutB f.t && s.phase = .completions then
          some (depositAt C s i [(2, 0)])
        else none
      | none => none
  | l => xstep C s l

/-- The executor of `conc001_selfTimeoutStep`. -/
def conc001_selfTimeout : XRel Nat Nat := conc001Graph conc001_selfTimeoutStep

/-- ✗ Depositing a timeout outcome no expiry handed back violates CONC-001 (line 4): firing `0`
of `t` (output spec `And(1, Timeout(d, 2))`) is in flight, and the next step 1 deposits its
timeout outcome before its budget expired. -/
@[evidence forbids CONC_001]
theorem CONC_001_forbids_selfTimeout : ¬ CONC_001 conc001_selfTimeout := by
  intro h
  obtain ⟨tr, hr, hp⟩ := conc001_run_of_check conc001_selfTimeoutStep (C := conc001C)
    (s0 := xinit conc001M0 0) (ls := conc001Pre ++ [.tdeposit 0])
    (p := fun tr => !(untilNever (conc001Expired 0) (conc001TDeposited 0)).scan false tr)
    (by decide)
  have h1 : (untilNever (conc001Expired 0) (conc001TDeposited 0)).scan false tr = true :=
    ((h conc001C).2.2 _ tr rfl rfl rfl hr).2.1 0
  simp [h1] at hp

/-- An executor whose orchestrator, in step 1, settles a firing whose action is still running
without a deposit (it drops the firing from those in flight). -/
def conc001_failUnreturnedStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .fail i =>
    match xstep C s (.fail i) with
    | some s' => some s'
    | none =>
      match s.fl.find? (·.id == i) with
      | some f => if f.out.isNone && s.phase = .completions then some (settle s i) else none
      | none => none
  | l => xstep C s l

/-- The executor of `conc001_failUnreturnedStep`. -/
def conc001_failUnreturned {N T : Type} [DecidableEq N] : XRel N T :=
  conc001Graph conc001_failUnreturnedStep

/-- ✗ Settling a running firing without a deposit violates CONC-001 (line 5): firing `0` of `t`
is in flight, and the next step 1 settles it with no return or expiry before it, so `t`, which is
not re-entrant, could start again while its action runs. -/
@[evidence forbids CONC_001]
theorem CONC_001_forbids_failUnreturned :
    ¬ CONC_001 (conc001_failUnreturned (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨tr, hr, hp⟩ := conc001_run_of_check conc001_failUnreturnedStep (C := conc001C)
    (s0 := xinit conc001M0 0) (ls := conc001Pre ++ [.fail 0])
    (p := fun tr => !(untilNever (conc001Ended 0) (conc001Failed 0)).scan false tr)
    (by decide)
  have h1 : (untilNever (conc001Ended 0) (conc001Failed 0)).scan false tr = true :=
    ((h conc001C).2.2 _ tr rfl rfl rfl hr).2.2.1 0
  simp [h1] at hp

/-- An executor whose orchestrator, in step 1b with no publication queued, publishes what a
running asynchronous action has written so far, without a flush. -/
def conc001_publishUnflushedStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .publish i =>
    match xstep C s (.publish i) with
    | some s' => some s'
    | none =>
      match s.fl.find? (·.id == i) with
      | some f =>
        if f.out.isNone && !f.buf.isEmpty && s.pq.isEmpty && s.phase = .publications then
          some { s with M := qAppend s.M f.buf, fl := updFiring s i fun g => { g with buf := [] } }
        else none
      | none => none
  | l => xstep C s l

/-- The executor of `conc001_publishUnflushedStep`. -/
def conc001_publishUnflushed {N T : Type} [DecidableEq N] : XRel N T :=
  conc001Graph conc001_publishUnflushedStep

/-- ✗ Publishing what an action wrote without its flush violates CONC-001 (line 6): the action of
firing `0` writes `5` to place `1`, and step 1b deposits it as a publication of firing `0`. -/
@[evidence forbids CONC_001]
theorem CONC_001_forbids_publishUnflushed :
    ¬ CONC_001 (conc001_publishUnflushed (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨tr, hr, hp⟩ := conc001_run_of_check conc001_publishUnflushedStep (C := conc001C)
    (s0 := xinit conc001M0 0) (ls := conc001Pre ++ [.write 0 1 5, .endCompletions, .publish 0])
    (p := fun tr => !(untilNever (conc001Flushed 0) (conc001Published 0)).scan false tr)
    (by decide)
  have h1 : (untilNever (conc001Flushed 0) (conc001Published 0)).scan false tr = true :=
    ((h conc001C).2.2 _ tr rfl rfl rfl hr).2.2.2.1 0
  simp [h1] at hp

/-- An executor that answers a request `refused` and still queues its event. -/
def conc001_queueRefusedStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .request p x r =>
    if r = replyFor C s p && r = .refused then
      some { s with eq := s.eq ++ [(s.nextId, p, x)], nextId := s.nextId + 1 }
    else xstep C s (.request p x r)
  | l => xstep C s l

/-- The executor of `conc001_queueRefusedStep`. -/
def conc001_queueRefused {N T : Type} [DecidableEq N] : XRel N T :=
  conc001Graph conc001_queueRefusedStep

/-- ✗ Injecting a refused request violates CONC-001 (line 7): the executor drains, a caller's
request to inject `9` is refused, and step 2 injects it with ticket `0`. -/
@[evidence forbids CONC_001]
theorem CONC_001_forbids_queueRefused :
    ¬ CONC_001 (conc001_queueRefused (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨tr, hr, hp⟩ := conc001_run_of_check conc001_queueRefusedStep (C := conc001C)
    (s0 := xinit conc001M0 0)
    (ls := [.drain, .request 0 9 .refused, .endCompletions, .endPublications, .inject 0])
    (p := fun tr => !(untilNever (conc001Queued 0) (conc001Injected 0)).scan false tr)
    (by decide)
  have h1 : (untilNever (conc001Queued 0) (conc001Injected 0)).scan false tr = true :=
    ((h conc001C).2.2 _ tr rfl rfl rfl hr).2.2.2.2 0
  simp [h1] at hp

/-! ### Every line exercised -/

/-- The run of the nonvacuous example: a caller's request is accepted (ticket `0`) and injected;
`t` starts (firing `1`), its action writes `5` to `1`, flushes, and returns; the completion is
committed and the publication deposited; `t` starts again on the injected token (firing `2`), its
budget expires with the timeout outcome `4` in `2`, which is deposited; a second request is
accepted (ticket `3`) and injected, `t` starts on it (firing `4`), its action fails, and the
firing is settled without a deposit. -/
def conc001Run : List (XLbl Nat Nat) :=
  [.request 0 9 .accepted, .endCompletions, .endPublications, .inject 0, .endEvents, .update,
    .deadline [], .begin, .start "t" false, .endPass, .write 1 1 5, .flush 1, .ret 1 true,
    .commit 1, .endCompletions, .publish 1, .endPublications, .endEvents, .update, .deadline [],
    .begin, .start "t" false, .endPass, .expire 2 [(2, 4)], .tdeposit 2,
    .request 0 8 .accepted, .endCompletions, .endPublications, .inject 3, .endEvents, .update,
    .deadline [], .begin, .start "t" false, .endPass, .ret 4 false, .fail 4]

/-- Every line of CONC-001 is exercised by the reference: on a run from the initial state, outside
steps happen (line 1's premise) and steps that are no deposit happen (line 2's premise), and a
completion is committed (firing `1`), a timeout outcome is deposited (firing `2`), a firing is
settled without a deposit (firing `4`), a publication is deposited (firing `1`) and an event is
injected (ticket `0`), each after the outside step that handed it over (lines 3 to 7 constrain
events that occur). -/
@[evidence nonvacuous CONC_001]
theorem CONC_001_nonvacuous :
    ∃ tr, XRun RefExec conc001C (xinit conc001M0 0) tr ∧
      (occurs (fun e : XStep Nat Nat => e.2.1.outside)) tr ∧
      (occurs (fun e : XStep Nat Nat => !startOrDeposit e.2.1)) tr ∧
      (occurs (conc001Committed (N := Nat) (T := Nat) 1)) tr ∧
      (occurs (conc001TDeposited (N := Nat) (T := Nat) 2)) tr ∧
      (occurs (conc001Failed (N := Nat) (T := Nat) 4)) tr ∧
      (occurs (conc001Published (N := Nat) (T := Nat) 1)) tr ∧
      (occurs (conc001Injected (N := Nat) (T := Nat) 0)) tr := by
  obtain ⟨tr, hr, hp⟩ := conc001_run_of_check xstep (C := conc001C)
    (s0 := xinit conc001M0 0) (ls := conc001Run)
    (p := fun tr => tr.any (fun e => e.2.1.outside) && tr.any (fun e => !startOrDeposit e.2.1) &&
      tr.any (conc001Committed 1) && tr.any (conc001TDeposited 2) && tr.any (conc001Failed 4) &&
      tr.any (conc001Published 1) && tr.any (conc001Injected 0))
    (by decide)
  simp only [Bool.and_eq_true] at hp
  exact ⟨tr, hr, hp.1.1.1.1.1.1, hp.1.1.1.1.1.2, hp.1.1.1.1.2, hp.1.1.1.2, hp.1.1.2, hp.1.2,
    hp.2⟩

end Libpetri.Spec
