import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Exec
import Libpetri.Reference.Snapshot
import Libpetri.Spec.Text.ENV_014

set_option linter.missingDocs true

/-!
# ENV-014: Mid-Execution Marking Snapshot (`spec/06-environment-places.md`)

A block over the executor model (`RefExec`, `Reference/Exec.lean`). A snapshot request is
answered by one step labelled `snapshot a` (glossary `GlossaryExec.lean`): `a = none` is a
rejection, `a = some true` a marking that reports work in flight, `a = some false` a marking that
reports a restore point. The marking of an answer is the marking of the state the step is taken
from. The requirement is a predicate over an abstract executor `R : XRel N T` with six lines: an
answer leaves the state as it was; an executor that has been drained, closed or terminated
rejects; a running executor that has been none of these does not reject; and an answer that
reports a restore point is taken from a state with no firing in flight (line 4), no accepted
external event still queued (line 5) and, on a run that starts with nothing in flight and nothing
published, no published batch still waiting for step 1b (line 6).

The evidence checks the block against the reference executor and against eight wrong executors:
one whose answer drains the executor and one whose answer wakes a parked orchestrator (line 1),
one that answers after a drain (line 2), one that rejects while work is in flight (line 3), one
that counts a firing as in flight only once its action suspends and one that always reports a
restore point (line 4), one whose flag reads the actions alone (line 5), and one that answers
before step 1b has deposited a settled firing's published batch (line 6). Decided runs of the
reference exercise every line, the test derivation of AC5 to AC7 included, and
`env014_restorePoint_restores` links a restore-point answer to [CORE-073]'s restore.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## ENV-014: Mid-Execution Marking Snapshot -/

requirement ENV_014
  id "ENV-014"
  title "Mid-Execution Marking Snapshot"
  kind B
  scope "all executors"
  source verbatim "spec/06-environment-places.md"
  covers ENV_014.s1, ENV_014.s2, ENV_014.s3, ENV_014.s4, ENV_014.s5, ENV_014.s6, ENV_014.s7,
        ENV_014.s8, ENV_014.s9, ENV_014.s10, ENV_014.s11, ENV_014.s12, ENV_014.s13
  reading "For every executor R and every configuration C:"
          "for every answer a, a snapshot step answered a ends in the state it starts from;"
          "for every answer a, a snapshot step answered a from a state whose mode is not open (draining, closed or stopped) answers none;"
          "for every answer a, a snapshot step answered a from a state whose mode is open and whose loop is running (an executing phase) does not answer none;"
          "a snapshot step answered some false starts in a state with no firing in flight;"
          "a snapshot step answered some false starts in a state whose event queue is empty;"
          "on every run of R that starts in a state with no firing in flight and no published batch queued, a snapshot step answered some false starts in a state whose publication queue is empty."
  assumes "The model is an executor R : XRel N T (glossary GlossaryExec.lean): R C s l s' says that under configuration C the step labelled l leads from executor state s to s'. A snapshot request and its answer are one step labelled snapshot a, taken at the instant the executor captures the marking. The answer a is none for a rejection, some true for a marking that reports work in flight, some false for a marking that reports a restore point. The witness is the reference executor RefExec (Reference/Exec.lean): it answers snapAnswer s (some of whether a firing is in flight or an event is queued while the mode is open, none otherwise), in step 2 after the injections, at entry to the enablement update and in the wait, which is Rust's Snapshot arm of handle_signal (executor_core/executor.rs) and Java's serviceMarkingRequest after the external-events phase."
          "Which marking an answer returns is a modelling assumption (kind A), not a line. The label carries no marking: the model reads the marking of an answer as the marking s.M of the state the step starts from, which line 1 makes the marking of the state it ends in too, and an executor that answers with any other marking cannot be written in the model, so no mutant can break what follows. Four quoted duties rest on that reading alone: 'An answer that reports a restore point describes the instant at which the executor captured it'; the second half of 'An answer to a request the orchestrator could not serve ...', a parked executor answers with the current marking, which is AC9's 'MUST return the current marking, not an earlier published one'; the first half of that sentence, that an answer describing an earlier instant (Java's unserved request, ruling D43 (a)) reports work in flight; and the marking side of the body's 'MUST be decided at the same instant the marking is captured'. The lines pin the flag side of that last duty: the flag is read off the state of the step, so an indication computed at another instant shows as an answer some false from a state with work in flight, which lines 4 to 6 forbid. The first two duties become lines of their own once the label carries the marking (an answer some (m, b) with m = s.M when b is false, and when the loop is parked); the glossary has no such label yet."
          "The three conforming shapes of the body (refuse, indicate, defer) are one abstraction. An indication is the flag of the answer. A refusal of a restore-point snapshot while work is in flight is an answer some true: the caller can tell it from a restore point, and the rejection none is reserved for a drained, closed or stopped executor (the quoted paragraph 'The answer and its two readings'). A deferral is an answer step taken later, at a state with nothing in flight. An executor that never answers some false meets the block: it never offers a restore point. The reference answers some false exactly when nothing is in flight and nothing is queued, and ENV_014_nonvacuous decides such an answer."
          "Work in flight (the quoted definition) is read off the state. A firing is in flight while it is in XSt.fl, from the start step that consumes its inputs to the settle step that commits or fails its completion (EXEC-001, EXEC-031), so a firing whose action returned but whose completion is not yet processed still counts (Rust decrements in_flight_count only when it processes the completion, in Phase 1 and in the wait of run_async, executor_core/executor.rs). Tokens its action published mid-action (IO-015) wait in XSt.pq as flushed batches until step 1b deposits them, which can come after the settle step (EXEC-001 step 1b, Phase 1b of run_async, executor_core/executor.rs). An accepted external event is queued while it is in XSt.eq, from the request step answered accepted (ENV-003) to its inject or discard step (ENV-004). The fourth quoted shall sentence keeps a firing in flight until its completion is processed and every token its action published is deposited: line 4 is the part up to the settle step, line 6 the part after it."
          "Line 1 is the first quoted shall sentence and the first quoted body sentence ('without affecting lifecycle', 'neither stops nor pauses execution'): the answer changes no field of the state, which is the sentence's 'its whole state': the marking, the clock reading of the host and of the cycle, the clocks of the transitions, the mode, the firings in flight, the completion, publication and event queues, the identity supply, the phase, the pass order and its same-pass counts, and the parked flag. It owns CORE-071's 'MUST NOT mutate the live marking' for a snapshot (plan section 7). An executor whose answer drains it, as a snapshot taken through drain() would, breaks it (ENV_014_forbids_drainingSnapshot), and so does one that serves a request in the wait by waking the orchestrator (ENV_014_forbids_wakingSnapshot, AC9)."
          "Line 2 is the second quoted shall sentence and AC4: once the mode is draining (ENV-011), closed (ENV-013) or stopped (ENV-015, the immediate termination; Java's terminateNow sets closed, so snapshot() throws), the answer is none. ENV_014_nonvacuous parts 5 to 7 decide a rejection after a drain, after a close (the test derivation's 'call after close() and verify rejection') and after an immediate termination. An executor that answers a drained request with a marking breaks it (ENV_014_forbids_answersAfterDrain); Rust's executor arm has no draining test (the Snapshot arm of handle_signal, executor_core/executor.rs), and Rust meets the line at its handle, which refuses once drained (ExecutorHandle::snapshot, executor_handle.rs): with one sender per run, a request sent before the drain is a snapshot step before the drain step, in channel order (map note, with ENV-011)."
          "Line 3 is the third quoted shall sentence and AC1 (reworded under ruling D20, ENVB-R7 item 3, to 'while the executor is running and has been neither drained, closed nor terminated'): a running open executor answers with a marking, whatever is in flight. An executor that rejects while work is in flight, a refusal the caller cannot tell from a closed executor, breaks it (ENV_014_forbids_rejectsWhileBusy). Line 3 binds only a running loop, and so does the quoted 'reserved, while the run lasts': after a run ended on its own the runtimes differ (Java and TypeScript still answer, snapshot() in BitmapNetExecutor and in bitmap-net-executor.ts; the Rust handle answers Err once the channel is gone, ExecutorHandle::snapshot in executor_handle.rs), and the block leaves that open."
          "That a snapshot step is offered at all is coverage, and no line says it. An executor with no snapshot step meets every line: line 2's 'shall reject' and line 3's 'shall not reject' are both met by never answering, and so are AC2's 'serviced within one orchestrator cycle' and AC8's 'does not park the orchestrator against itself', which rest on the same coverage. The consistency theorem excludes it: its coverage conjunct ExecCoversW5 (ConsistencyExec.lean) has the clause Env014Covers, that a live state in step 2, at entry to the update or in the wait has a snapshot step; env014_snapshot_offered proves it of the reference."
          "Line 4 is the fourth quoted shall sentence up to the settle step, the action half of 'Consequently a snapshot offered as a restore point ... MUST be taken at a moment when no work is in flight', AC5 and AC6. The start step that consumes a firing's inputs is the step that puts it in flight, synchronous or not, so 'from the moment its inputs are consumed' (the quoted sentence and the first half of AC8) needs no line of its own: an executor that counts a firing as in flight only once its action suspends answers some false from inside a synchronous action and breaks line 4 (ENV_014_forbids_suspendOnlyInFlight; Java's inline capture on the orchestrator thread answers true, snapshot() in BitmapNetExecutor). So does an executor that always reports a restore point (ENV_014_forbids_alwaysRestorePoint). AC6 is ENV_014_nonvacuous part 1: the net's only marked place feeds a transition whose action is in flight, the consumed token is in no place of the marking, and the answer is some true."
          "Line 5 is the fifth quoted shall sentence, the event half, the paragraph 'Two conforming shapes for the pending-event half' and AC7: an answer some false comes from a state whose event queue is empty. An executor whose indication reads the actions alone breaks it (ENV_014_forbids_actionsOnlyFlag): an event accepted while the loop waits is in neither the marking nor the flag. TypeScript and Java read the marking outside the event queue and OR the pending queue into the flag (the reference's reading). Rust and Python serve the request on the same FIFO channel as injections (handle_signal, executor_core/executor.rs): every event accepted before the request is injected before the answer, so the event queue holds no such event when the marking is captured; an event accepted after the request was sent is a request step after the snapshot step, in channel order, which is what the quoted sentence's 'accepted before a snapshot() request' allows. ENV_014_nonvacuous part 4 is AC7's test derivation: an event accepted while the loop is parked, the snapshot flagged."
          "Line 6 is the fourth quoted shall sentence after the settle step, with reason (1) ('those tokens are simply absent'), AC8's 'outputs deposited, no token missing' and the pending-event paragraph's 'a token the executor has accepted is never absent from a snapshot that reports itself a restore point': an answer some false comes from a state with no flushed batch waiting for step 1b. An executor that serves the request before step 1b (Rust's loop with Phase 2 moved before Phase 1b, its flag still in_flight_count or a queued event) answers some false after the settle and before the deposit, with the published token in no place, and breaks line 6 alone (ENV_014_forbids_answerBeforeDeposit). Line 6 reads runs that start with no firing in flight and no batch queued: the initial state xinit, or a restored marking. From an arbitrary state the reference itself answers some false with a batch queued (env014_needs_runStart), because its flag reads the firings and the events only; on its own runs a batch is queued only while its firing is in flight or in steps 1 and 1b, where it does not answer (env014_pubInv_step). ENV_014_nonvacuous part 8 decides a reference run whose action flushes a batch in the wait, answers some true with the batch queued and some false only once step 1b has deposited it."
          "AC8: a snapshot requested by a running action is a snapshot with that firing in flight (line 4), from its synchronous prefix on. The deferred arm is an answer step taken after that firing settled and its published tokens were deposited (Rust and Python serve the request of an inline synchronous action at the next cycle), which may be some false when nothing else is in flight; the block allows it. That the orchestrator does not park against itself, that the deferred reply is not blocked on from the orchestrator's own thread of control, and the body's 'An implementation with that shape MUST detect the case and capture directly on the calling thread, after whatever synchronisation of internal token storage any other marking read performs' (the inline-action form of the same duty) are thread properties (kind Q): the model has no threads, and a step relation cannot wait for itself."
          "AC9: a parked executor answers without waking: line 1 keeps the parked flag and the phase of an answer in the wait (ENV_014_nonvacuous part 3 answers from a parked state and stays parked, and ENV_014_forbids_wakingSnapshot breaks it), and that the answer carries the current marking is the modelling assumption of the second paragraph. 'Without the orchestrator's participation' (Java's park epoch, Rust's race of the clock's wait against its signal channel) is a thread property (kind Q). AC9's marking() half is not a step of the model: a foreign marking() read is a read of s.M, current by construction, and its thread half is kind Q under ruling D43 (a), which CONC-001's block records for foreign reads. The last published marking of Java's unserved request after its 2 s best-effort cap (ruling D43 (a), ENVB-R4 (a)) is an answer whose marking is earlier than the state's, outside the model by the second paragraph; its flag is forced true, which is the duty the second paragraph accounts for."
          "Kind Q, outside the lines: AC2's 'within one orchestrator cycle' is a latency, which rests on coverage (the reference offers an answer at entry to every enablement update, env014_snapshot_offered, so a request is answered in the cycle it arrives in or in the wait); AC2's 'keeps running afterwards' is line 1 (the answer changes neither the mode nor the phase). AC3 (an owned copy, independent of subsequent executor state) is a property of the returned value: in the model the marking of an answer is a value, so later steps cannot change it; aliasing is tested, not proven. Java's 2 s cap and 50 ms recheck are implementation choices (kind N)."
          "CORE-073: a restore-point answer restores, through the snapshot form, to the marking of the state it was taken from, with nothing in flight and nothing queued (env014_restorePoint_restores). The test derivation's second half (snapshot again at quiescence and restore to an equivalent marking) is that theorem together with ENV_014_nonvacuous part 2. The guarantee 'restore and resume' needs CORE-073's own block for the seeding (refSeed)."
  signoff "2026-11-13 98ccafcb0c495997 ai"
  statement : ∀ {N T : Type} [DecidableEq N], XRel N T → Prop :=
    fun R => ∀ C,
      (∀ a, on (fun s s' => R C s (.snapshot a) s'), shall (fun s s' => s' = s)) ∧
      (∀ a, on (fun s s' => R C s (.snapshot a) s'),
        shall (fun s _ => s.mode ≠ .open → a = none)) ∧
      (∀ a, on (fun s s' => R C s (.snapshot a) s'),
        shall (fun s _ => s.mode = .open → isExecPhase s.phase = true → a ≠ none)) ∧
      (on (fun s s' => R C s (.snapshot (some false)) s'), shall (fun s _ => s.fl = [])) ∧
      (on (fun s s' => R C s (.snapshot (some false)) s'), shall (fun s _ => s.eq = [])) ∧
      (∀ s0 tr, s0.fl = [] → s0.pq = [] → XRun R C s0 tr →
        ∀ x ∈ tr, x.2.1 = .snapshot (some false) → x.1.pq = [])

/- The pinned readable form of ENV-014: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.ENV_014 : {N T : Type} → [DecidableEq N] → XRel N T → Prop :=
fun {N T} [DecidableEq N] R =>
  ∀ (C : Cfg N T),
    (∀ (a : Option Bool), on fun s s' => R C s (XLbl.snapshot a) s', shall fun s s' => s' = s) ∧
      (∀ (a : Option Bool), on fun s s' => R C s (XLbl.snapshot a) s', shall fun s x => s.mode ≠ Mode.open → a = none) ∧
        (∀ (a : Option Bool),
            on fun s s' => R C s (XLbl.snapshot a) s', shall fun s x =>
              s.mode = Mode.open → isExecPhase s.phase = true → a ≠ none) ∧
          (on fun s s' => R C s (XLbl.snapshot (some false)) s', shall fun s x => s.fl = []) ∧
            (on fun s s' => R C s (XLbl.snapshot (some false)) s', shall fun s x => s.eq = []) ∧
              ∀ (s0 : XSt N T) (tr : List (XStep N T)),
                s0.fl = [] → s0.pq = [] → XRun R C s0 tr → ∀ x ∈ tr, x.2.1 = XLbl.snapshot (some false) → x.1.pq = []
-/
#guard_msgs in #print ENV_014

/-! ### The reference -/

section Reference

variable {N T : Type} [DecidableEq N]

/-- The reference's answer is `snapAnswer`, and the step changes nothing. -/
theorem env014_ref_step {C : Cfg N T} {s s' : XSt N T} {a : Option Bool}
    (h : RefExec C s (.snapshot a) s') : a = snapAnswer s ∧ s' = s := by
  obtain ⟨-, -, ha, hs⟩ := snapshotStep_some h
  exact ⟨ha, hs⟩

omit [DecidableEq N] in
/-- An answer `some false` of the reference: nothing in flight, nothing queued. -/
theorem env014_snapAnswer_false {s : XSt N T} (h : some false = snapAnswer s) :
    s.fl = [] ∧ s.eq = [] := by
  unfold snapAnswer at h
  split at h
  · simp only [Option.some.injEq] at h
    have h' := h.symm
    simp only [Bool.or_eq_false_iff, Bool.not_eq_false', List.isEmpty_iff] at h'
    exact h'
  · exact absurd h (by simp)

/-- Coverage (AC1 and AC2, for the consistency theorem's `ExecCoversW5`): the reference answers a
snapshot request in every live state at entry to the enablement update, in step 2 and in the
wait, and the answer is the state itself. -/
theorem env014_snapshot_offered (C : Cfg N T) (s : XSt N T) (hL : Live C s)
    (hp : s.phase = .events ∨ s.phase = .update ∨ s.phase = .await) :
    RefExec C s (.snapshot (snapAnswer s)) s := by
  have hl : liveB C s = true := hL
  show snapshotStep C s (snapAnswer s) = some s
  unfold snapshotStep
  rcases hp with hp | hp | hp <;> simp [hl, hp]

/-! #### Published batches on the reference's runs (line 6) -/

/-- The identity and the synchrony of each firing in flight. -/
def env014_ids (s : XSt N T) : List (Nat × Bool) := s.fl.map fun g => (g.id, g.sync)

/-- What the reference keeps on its runs about published batches: the identities in flight are
distinct and drawn from the supply; every queued batch carries an identity drawn from the supply
and no synchronous firing in flight has it; and outside steps 1 and 1b every queued batch
belongs to an asynchronous firing still in flight. -/
def env014_PubInv (s : XSt N T) : Prop :=
  ((env014_ids s).map Prod.fst).Nodup ∧
  (∀ x ∈ env014_ids s, x.1 < s.nextId) ∧
  (∀ e ∈ s.pq, e.1 < s.nextId) ∧
  (∀ e ∈ s.pq, (e.1, true) ∉ env014_ids s) ∧
  (s.phase = .completions ∨ s.phase = .publications ∨
    ∀ e ∈ s.pq, (e.1, false) ∈ env014_ids s)

omit [DecidableEq N] in
/-- A run that starts with nothing in flight and nothing published starts in the invariant. -/
theorem env014_pubInv_start {s : XSt N T} (hfl : s.fl = []) (hpq : s.pq = []) :
    env014_PubInv s := by
  have hi : env014_ids s = [] := by simp [env014_ids, hfl]
  refine ⟨by simp [hi], by simp [hi], by simp [hpq], by simp [hpq], Or.inr (Or.inr ?_)⟩
  simp [hpq]

omit [DecidableEq N] in
/-- A step that keeps the identities and synchrony in flight, keeps or shrinks the batch queue,
never lowers the supply, and leaves steps 1 and 1b only where every batch has its firing. -/
theorem env014_pubInv_mono {s s' : XSt N T} (hi : env014_PubInv s)
    (hids : env014_ids s' = env014_ids s) (hpq : ∀ e ∈ s'.pq, e ∈ s.pq)
    (hn : s.nextId ≤ s'.nextId)
    (hown : s'.phase = .completions ∨ s'.phase = .publications ∨
      ∀ e ∈ s.pq, (e.1, false) ∈ env014_ids s) : env014_PubInv s' := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hi
  refine ⟨hids ▸ h1, fun x hx => Nat.lt_of_lt_of_le (h2 x (hids ▸ hx)) hn,
    fun e he => Nat.lt_of_lt_of_le (h3 e (hpq e he)) hn, fun e he => hids ▸ h4 e (hpq e he), ?_⟩
  rcases hown with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr fun e he => hids ▸ h e (hpq e he))

omit [DecidableEq N] in
/-- Outside steps 1 and 1b every queued batch has its firing. -/
theorem env014_pubInv_own {s : XSt N T} (hi : env014_PubInv s) (h1 : s.phase ≠ .completions)
    (h2 : s.phase ≠ .publications) : ∀ e ∈ s.pq, (e.1, false) ∈ env014_ids s := by
  rcases hi.2.2.2.2 with h | h | h
  · exact absurd h h1
  · exact absurd h h2
  · exact h

omit [DecidableEq N] in
/-- Updating a firing's record by a map that keeps its identity and synchrony keeps both. -/
theorem env014_ids_upd {s s' : XSt N T} {i : Nat} {h : Firing N T → Firing N T}
    (hfl : s'.fl = updFiring s i h) (hh : ∀ g, (h g).id = g.id ∧ (h g).sync = g.sync) :
    env014_ids s' = env014_ids s := by
  unfold env014_ids
  rw [hfl]
  exact updFiring_map (fun g => (g.id, g.sync)) fun g => by rw [(hh g).1, (hh g).2]

omit [DecidableEq N] in
/-- The firing a settle step finds is in flight, under its identity. -/
theorem env014_find_mem {s : XSt N T} {i : Nat} {f : Firing N T}
    (hf : s.fl.find? (·.id == i) = some f) : (i, f.sync) ∈ env014_ids s := by
  have hm := List.mem_of_find?_eq_some hf
  have he : f.id = i := by simpa using List.find?_some hf
  exact List.mem_map.mpr ⟨f, hm, by rw [he]⟩

omit [DecidableEq N] in
/-- Settling keeps the invariant: in the firing pass only a synchronous firing settles, and no
queued batch carries a synchronous firing's identity. -/
theorem env014_pubInv_settle {s s' : XSt N T} {i : Nat} {f : Firing N T}
    (hi : env014_PubInv s) (hf : s.fl.find? (·.id == i) = some f) (hok : settleOk s f = true)
    (hfl : s'.fl = s.fl.filter (·.id != i)) (hpq : s'.pq = s.pq) (hn : s'.nextId = s.nextId)
    (hph : s'.phase = if s.phase = .await then .completions else s.phase) :
    env014_PubInv s' := by
  have hids : env014_ids s' = (env014_ids s).filter (fun x => x.1 != i) := by
    simp only [env014_ids, hfl, List.filter_map]
    rfl
  have hown5 := hi.2.2.2.2
  obtain ⟨h1, h2, h3, h4, -⟩ := hi
  have sub : ∀ x ∈ env014_ids s', x ∈ env014_ids s := fun x hx =>
    (List.mem_filter.mp (hids ▸ hx)).1
  refine ⟨?_, fun x hx => hn ▸ h2 x (sub x hx), fun e he => hn ▸ h3 e (hpq ▸ he),
    fun e he hm => h4 e (hpq ▸ he) (sub _ hm), ?_⟩
  · rw [hids]
    exact h1.sublist ((List.filter_sublist).map _)
  · rw [hpq]
    cases hp : s.phase with
    | completions => exact Or.inl (by rw [hph, hp]; rfl)
    | await => exact Or.inl (by rw [hph, hp]; rfl)
    | pass =>
      have hsy : f.sync = true := by simpa [settleOk, hp] using hok
      have hown := env014_pubInv_own ⟨h1, h2, h3, h4, hown5⟩ (by rw [hp]; decide)
        (by rw [hp]; decide)
      refine Or.inr (Or.inr fun e he => ?_)
      have hne : e.1 ≠ i := by
        rintro rfl
        exact h4 e he (hsy ▸ env014_find_mem hf)
      rw [hids]
      exact List.mem_filter.mpr ⟨hown e he, by simpa using hne⟩
    | _ => simp [settleOk, hp] at hok

/-- **Every reference step keeps the invariant.** -/
theorem env014_pubInv_step {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : RefExec C s l s') (hi : env014_PubInv s) : env014_PubInv s' := by
  have same : ∀ {s'' : XSt N T}, env014_ids s'' = env014_ids s → s''.pq = s.pq →
      s''.nextId = s.nextId → s''.phase = s.phase → env014_PubInv s'' :=
    fun hids hpq hn hph => env014_pubInv_mono hi hids (fun e he => hpq ▸ he) (hn ▸ le_refl _)
      (by rw [hph]; exact hi.2.2.2.2)
  have own : ∀ {s'' : XSt N T}, env014_ids s'' = env014_ids s → s''.pq = s.pq →
      s''.nextId = s.nextId → s.phase ≠ .completions → s.phase ≠ .publications →
      env014_PubInv s'' :=
    fun hids hpq hn h1 h2 => env014_pubInv_mono hi hids (fun e he => hpq ▸ he) (hn ▸ le_refl _)
      (Or.inr (Or.inr (env014_pubInv_own hi h1 h2)))
  have exempt : ∀ {s'' : XSt N T}, env014_ids s'' = env014_ids s → (∀ e ∈ s''.pq, e ∈ s.pq) →
      s''.nextId = s.nextId → (s''.phase = .completions ∨ s''.phase = .publications) →
      env014_PubInv s'' :=
    fun hids hpq hn hph => env014_pubInv_mono hi hids hpq (hn ▸ le_refl _)
      (hph.elim Or.inl (fun h => Or.inr (Or.inl h)))
  cases l with
  | delay δ => cases xstepW_delay h; exact same rfl rfl rfl rfl
  | write i p x =>
    obtain ⟨f, -, -, rfl⟩ := writeStep_some h
    exact same (env014_ids_upd rfl fun _ => ⟨rfl, rfl⟩) rfl rfl rfl
  | flush i =>
    obtain ⟨f, hf, -, hsy, -, ⟨-, -, hs'⟩ | ⟨-, hs'⟩⟩ := flushStep_some h
    · have hids : env014_ids s' = env014_ids s := env014_ids_upd (by rw [hs'])
        (h := fun g => { g with buf := [], pub := g.pub ++ g.buf.map Prod.fst })
        fun _ => ⟨rfl, rfl⟩
      have hpq : s'.pq = s.pq ++ [(i, f.buf)] := by rw [hs']
      have hn : s'.nextId = s.nextId := by rw [hs']
      have hph : s'.phase = s.phase := by rw [hs']
      have hmem : (i, false) ∈ env014_ids s := hsy ▸ env014_find_mem hf
      obtain ⟨h1, h2, h3, h4, h5⟩ := hi
      refine ⟨hids ▸ h1, fun x hx => hn ▸ h2 x (hids ▸ hx), fun e he => ?_, fun e he hm => ?_,
        ?_⟩
      · rw [hpq] at he
        rw [hn]
        rcases List.mem_append.mp he with he | he
        · exact h3 e he
        · rw [List.mem_singleton.mp he]; exact h2 _ hmem
      · rw [hids] at hm
        rw [hpq] at he
        rcases List.mem_append.mp he with he | he
        · exact h4 e he hm
        · rw [List.mem_singleton.mp he] at hm
          have := List.inj_on_of_nodup_map h1 hm hmem rfl
          simp at this
      · rw [hph, hpq, hids]
        rcases h5 with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · refine Or.inr (Or.inr fun e he => ?_)
          rcases List.mem_append.mp he with he | he
          · exact h e he
          · rw [List.mem_singleton.mp he]; exact hmem
    · exact same (env014_ids_upd (by rw [hs']) (h := fun g => { g with buf := [], relayBad := true })
        fun _ => ⟨rfl, rfl⟩) (by rw [hs']) (by rw [hs']) (by rw [hs'])
  | ret i ok =>
    obtain ⟨f, -, -, rfl⟩ := retStep_some h
    exact same (env014_ids_upd rfl fun _ => ⟨rfl, rfl⟩) rfl rfl rfl
  | expire i e =>
    obtain ⟨f, -, -, -, -, -, rfl⟩ := expireStep_some h
    exact same (env014_ids_upd rfl fun _ => ⟨rfl, rfl⟩) rfl rfl rfl
  | request p x r =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := requestStep_some h
    · exact env014_pubInv_mono hi rfl (fun e he => he) (Nat.le_succ _) (hi.2.2.2.2)
    · exact hi
  | drain => obtain ⟨-, rfl⟩ := drainStep_some h; exact same rfl rfl rfl rfl
  | close => obtain ⟨-, rfl⟩ := closeStep_some h; exact same rfl rfl rfl rfl
  | terminateNow => obtain ⟨-, rfl⟩ := terminateStep_some h; exact same rfl rfl rfl rfl
  | commit i =>
    obtain ⟨f, e, hf, -, hc, -, -, rfl⟩ := commitStep_some h
    simp only [canSettle, Bool.and_eq_true] at hc
    exact env014_pubInv_settle hi hf hc.2 rfl rfl rfl rfl
  | fail i =>
    obtain ⟨f, hf, hc, -, rfl⟩ := failStep_some h
    simp only [canSettle, Bool.and_eq_true] at hc
    exact env014_pubInv_settle hi hf hc.2 rfl rfl rfl rfl
  | tdeposit i =>
    obtain ⟨f, e, hf, -, hc, -, rfl⟩ := tdepositStep_some h
    simp only [canSettle, Bool.and_eq_true] at hc
    exact env014_pubInv_settle hi hf hc.2 rfl rfl rfl rfl
  | endCompletions =>
    obtain ⟨-, -, -, -, rfl⟩ := xstepW_endCompletions h
    exact exempt rfl (fun e he => he) rfl (Or.inr rfl)
  | publish i =>
    obtain ⟨b, rest, hq, -, hp, rfl⟩ := publishStep_some h
    refine exempt rfl (fun e he => by rw [hq]; exact List.mem_cons_of_mem _ he) rfl ?_
    rcases hp with hp | ⟨hp, -⟩ <;> simp [hp]
  | endPublications =>
    obtain ⟨-, -, hq, rfl⟩ := xstepW_endPublications h
    exact env014_pubInv_mono hi rfl (fun e he => he) (le_refl _)
      (Or.inr (Or.inr (by simp [hq])))
  | inject k =>
    obtain ⟨_, _, _, -, -, -, hp, rfl⟩ := injectStep_some h
    rcases hp with hp | hp
    · exact own rfl rfl rfl (by rw [hp]; decide) (by rw [hp]; decide)
    · exact exempt rfl (fun e he => he) rfl (Or.inl (by simp [hp]))
  | discard k =>
    obtain ⟨_, _, _, -, -, -, hp, rfl⟩ := discardStep_some h
    rcases hp with hp | hp
    · exact own rfl rfl rfl (by rw [hp]; decide) (by rw [hp]; decide)
    · exact exempt rfl (fun e he => he) rfl (Or.inl (by simp [hp]))
  | snapshot a => obtain ⟨-, -, -, rfl⟩ := snapshotStep_some h; exact hi
  | endEvents =>
    obtain ⟨hp, -, -, rfl⟩ := xstepW_endEvents h
    exact own rfl rfl rfl (by rw [hp]; decide) (by rw [hp]; decide)
  | update =>
    obtain ⟨hp, -, rfl⟩ := xstepW_update h
    exact own rfl rfl rfl (by rw [hp]; decide) (by rw [hp]; decide)
  | deadline ns =>
    obtain ⟨hp, -, -, rfl⟩ := xstepW_deadline h
    exact own rfl rfl rfl (by rw [hp]; decide) (by rw [hp]; decide)
  | finish c =>
    cases c with
    | quiescent =>
      obtain ⟨hp, -, -, rfl⟩ := xstepW_finishQuiescent h
      exact own rfl rfl rfl (by rw [hp]; decide) (by rw [hp]; decide)
    | closed =>
      obtain ⟨hp, -, -, -, rfl⟩ := xstepW_finishClosed h
      exact own rfl rfl rfl (by rw [hp]; decide) (by rw [hp]; decide)
    | terminal =>
      obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h
      exact ⟨hi.1, hi.2.1, by simp, by simp, Or.inr (Or.inr (by simp))⟩
    | stopped =>
      obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h
      exact ⟨hi.1, hi.2.1, by simp, by simp, Or.inr (Or.inr (by simp))⟩
  | begin =>
    obtain ⟨hp, -, -, -, rfl⟩ := xstepW_begin h
    exact own rfl rfl rfl (by rw [hp]; decide) (by rw [hp]; decide)
  | start n sy =>
    obtain ⟨t, rest, -, hp, -, -, -, -, -, hs'⟩ := startStep_some h
    have hown := env014_pubInv_own hi (by rw [hp]; decide) (by rw [hp]; decide)
    obtain ⟨h1, h2, h3, h4, -⟩ := hi
    have hids : env014_ids s' = env014_ids s ++ [(s.nextId, sy)] := by
      rw [hs']; simp [env014_ids]
    have hn : s'.nextId = s.nextId + 1 := by rw [hs']
    have hpq : s'.pq = s.pq := by rw [hs']
    rw [env014_PubInv, hids, hn, hpq]
    refine ⟨?_, fun x hx => ?_, fun e he => Nat.lt_succ_of_lt (h3 e he), fun e he hm => ?_, ?_⟩
    · rw [List.map_append]
      refine List.nodup_append.mpr ⟨h1, List.nodup_singleton _, ?_⟩
      intro a ha b hb
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
      subst hb
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
      exact Nat.ne_of_lt (h2 y hy)
    · rcases List.mem_append.mp hx with hx | hx
      · exact Nat.lt_succ_of_lt (h2 x hx)
      · rw [List.mem_singleton.mp hx]; exact Nat.lt_succ_self _
    · rcases List.mem_append.mp hm with hm | hm
      · exact h4 e he hm
      · have := congrArg Prod.fst (List.mem_singleton.mp hm)
        simp only at this
        have := h3 e he
        omega
    · exact Or.inr (Or.inr fun e he => List.mem_append_left _ (hown e he))
  | lose n =>
    obtain ⟨_, _, -, hp, -, -, -, -, rfl⟩ := loseStep_some h
    exact same rfl rfl rfl rfl
  | endPass =>
    obtain ⟨hp, -, -, -, rfl⟩ := xstepW_endPass h
    exact own rfl rfl rfl (by rw [hp]; decide) (by rw [hp]; decide)
  | park tmr =>
    obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := parkStep_some h
    exact same rfl rfl rfl rfl
  | wake =>
    obtain ⟨-, -, rfl⟩ := wakeStep_some h
    exact exempt rfl (fun e he => he) rfl (Or.inl rfl)

/-- Along a run of the reference from the invariant, every step is a reference step taken from a
state in the invariant. -/
theorem env014_pubInv_run {C : Cfg N T} :
    ∀ {s0 : XSt N T} {tr : List (XStep N T)}, env014_PubInv s0 → XRun RefExec C s0 tr →
      ∀ x ∈ tr, env014_PubInv x.1 ∧ RefExec C x.1 x.2.1 x.2.2
  | _, [], _, _ => fun x hx => absurd hx List.not_mem_nil
  | s0, st :: rest, hi, ⟨h1, h2, h3⟩ => by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨h1 ▸ hi, h2⟩
    · exact env014_pubInv_run (env014_pubInv_step h2 (h1 ▸ hi)) h3 x hx

end Reference

/-- ✓ The reference executor satisfies ENV-014: its answer step leaves the state as it is and
answers `snapAnswer s` (`snapshotStep_some`), which is `none` exactly when the mode is not open,
and `some false` only with nothing in flight and nothing queued; on its runs from a start with
nothing in flight and nothing published it answers only outside steps 1 and 1b, where a queued
batch has its firing in flight (`env014_pubInv_run`), so `some false` comes with no batch
queued. -/
@[evidence holds ENV_014]
theorem ENV_014_reference {N T : Type} [DecidableEq N] :
    ENV_014 (RefExec (N := N) (T := T)) := by
  intro C
  refine ⟨fun a s s' h => ?_, fun a s s' h => ?_, fun a s s' h => ?_, fun s s' h => ?_,
    fun s s' h => ?_, fun s0 tr hfl hpq hr x hx hl => ?_⟩
  · exact (env014_ref_step h).2
  · intro hm
    rw [(env014_ref_step h).1]
    simp [snapAnswer, hm]
  · intro hm _
    rw [(env014_ref_step h).1]
    simp [snapAnswer, hm]
  · exact (env014_snapAnswer_false (env014_ref_step h).1).1
  · exact (env014_snapAnswer_false (env014_ref_step h).1).2
  · obtain ⟨hi, hs⟩ := env014_pubInv_run (env014_pubInv_start hfl hpq) hr x hx
    rw [hl] at hs
    obtain ⟨-, hph, ha, -⟩ := snapshotStep_some hs
    have hf := (env014_snapAnswer_false ha).1
    have hown := env014_pubInv_own hi (by rcases hph with h | h | h <;> rw [h] <;> decide)
      (by rcases hph with h | h | h <;> rw [h] <;> decide)
    rw [List.eq_nil_iff_forall_not_mem]
    intro e he
    have := hown e he
    simp [env014_ids, hf] at this

/-- Line 6 needs its start: from a state of step 2 that holds a settled firing's batch, a state
the reference never reaches from such a start, the reference answers `some false` with the batch
queued, since its flag reads the firings and the events only. -/
theorem env014_needs_runStart :
    ∃ s, RefExec (N := Nat) (T := Nat)
      { prio := fun _ => 0, terminals := [], envs := [], reentrant := false,
        validate := fun _ _ => true, relay := fun _ _ _ => true,
        timeoutOut := fun _ _ _ => false, res := 0,
        X := { net := { places := [0], transitions := [] }, timing := fun _ => .immediate,
               tol := 0 } }
      s (.snapshot (some false)) s ∧ s.pq ≠ [] :=
  ⟨{ xinit (fun _ => []) 0 with phase := .events, pq := [(0, [(0, 5)])] }, rfl, by simp⟩

/-- Every executor that meets ENV-014 answers a snapshot request without changing the live
marking or the lifecycle mode (line 1): the frame part of [CORE-071]'s observation path, for the
snapshot answer. -/
@[evidence cites "CORE-071" "It MUST NOT mutate ... the live marking (the snapshot answer of [ENV-014])"]
theorem env014_snapshot_frame {N T : Type} [DecidableEq N] {R : XRel N T} (hR : ENV_014 R)
    {C : Cfg N T} {s s' : XSt N T} {a : Option Bool} (hs : R C s (.snapshot a) s') :
    s'.M = s.M ∧ s'.mode = s.mode := by
  have h1 : s' = s := (hR C).1 a s s' hs
  subst h1
  exact ⟨rfl, rfl⟩

/-! ### Restore points ([CORE-073]) -/

/-- An answer that reports a restore point restores, through the snapshot form of [CORE-073],
to the marking of the state it was taken from, which the answer leaves unchanged, with nothing in
flight and nothing queued. -/
theorem env014_restorePoint_restores {N T : Type} [LinearOrder N] {R : XRel N T}
    (hR : ENV_014 R) {C : Cfg N T} {s s' : XSt N T}
    (hs : R C s (.snapshot (some false)) s') (F : FinQ N T) (hF : F.M = s.M) :
    refRestore (refSnapshot F) = s'.M ∧ s'.fl = [] ∧ s'.eq = [] := by
  have h1 : s' = s := (hR C).1 _ s s' hs
  subst h1
  exact ⟨by rw [restore_snapshot, hF], (hR C).2.2.2.1 _ _ hs, (hR C).2.2.2.2.1 _ _ hs⟩

/-! ### Examples

One environment place `0` and a transition `t` that takes a token from it and outputs to place
`1`. Place `0` starts with token `5`, so `t` is the net's only enabled transition and place `0`
its only marked place (AC6). -/

/-- Transition `t`: one token from the environment place `0`, output `1`. -/
def env014_t : Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 1) }

/-- The configuration of the examples: place `0` is an environment place. -/
def env014_c : Cfg Nat Nat :=
  { X := { net := { places := [0, 1], transitions := [env014_t] },
           timing := fun _ => .immediate, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [0], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => false,
    res := 0 }

/-- The initial state: token `5` in place `0`. -/
def env014_s0 : XSt Nat Nat := xinit (fun p => if p = 0 then [5] else []) 0

/-- The first cycle up to its firing pass. -/
def env014_toPass : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin]

/-- `t` starts asynchronously, the pass ends, and the next cycle reaches step 2 with the firing
in flight: the consumed token is in no place (AC6). -/
def env014_inFlight : List (XLbl Nat Nat) :=
  env014_toPass ++ [.start "t" false, .endPass, .endCompletions, .endPublications]

/-- The action writes `5` to place `1` and returns; the completion is committed in the wait, and
the next cycle reaches step 2 with nothing in flight: a restore point. -/
def env014_settled : List (XLbl Nat Nat) :=
  env014_inFlight ++ [.endEvents, .update, .deadline [], .begin, .endPass, .write 0 1 5,
    .ret 0 true, .commit 0, .endCompletions, .endPublications]

/-- The loop finds nothing to do and blocks in its wait. -/
def env014_parked : List (XLbl Nat Nat) :=
  env014_settled ++ [.endEvents, .update, .deadline [], .begin, .endPass, .park none]

/-- An event for place `0` is accepted while the loop is blocked (AC7). -/
def env014_queued : List (XLbl Nat Nat) := env014_parked ++ [.request 0 7 .accepted]

/-- The executor is drained (AC4). -/
def env014_drained : List (XLbl Nat Nat) := env014_queued ++ [.drain]

/-- The first cycle, with `t` started synchronously: the pass waits for its action (AC8). -/
def env014_sync : List (XLbl Nat Nat) := env014_toPass ++ [.start "t" true]

/-- The executor is closed (AC4, the test derivation's 'call after close()'). -/
def env014_closed : List (XLbl Nat Nat) := env014_parked ++ [.close]

/-- The executor is terminated immediately ([ENV-015]). -/
def env014_terminated : List (XLbl Nat Nat) := env014_parked ++ [.terminateNow]

/-- `t` starts asynchronously; in the wait its action writes `5` to place `1`, flushes it (a
queued batch), returns, and its completion is committed; step 1 ends, and the loop is in step 1b
with the batch still queued (line 6). -/
def env014_published : List (XLbl Nat Nat) :=
  env014_inFlight ++ [.endEvents, .update, .deadline [], .begin, .endPass, .write 0 1 5,
    .flush 0, .ret 0 true, .commit 0, .endCompletions]

/-- The reference's run of line 6: in the wait the batch is queued with `t` in flight and the
answer is `some true`; after step 1b has deposited it the answer is `some false`. -/
def env014_pubRun : List (XLbl Nat Nat) :=
  env014_inFlight ++ [.endEvents, .update, .deadline [], .begin, .endPass, .write 0 1 5,
    .flush 0, .snapshot (some true), .ret 0 true, .commit 0, .endCompletions, .publish 0,
    .endPublications, .snapshot (some false)]

/-- The reference state after `ls` from `env014_s0`. -/
def env014_at (ls : List (XLbl Nat Nat)) : Option (XSt Nat Nat) := xrun env014_c env014_s0 ls

/-- The trace of a label run of the step function `g`, if every label is a step. -/
def env014_trace (g : Cfg Nat Nat → XSt Nat Nat → XLbl Nat Nat → Option (XSt Nat Nat))
    (C : Cfg Nat Nat) : XSt Nat Nat → List (XLbl Nat Nat) → Option (List (XStep Nat Nat))
  | _, [] => some []
  | s, l :: ls => (g C s l).bind fun s' => (env014_trace g C s' ls).map ((s, l, s') :: ·)

/-- A trace `env014_trace` builds is a run of the executor of `g`. -/
theorem env014_trace_run {g : Cfg Nat Nat → XSt Nat Nat → XLbl Nat Nat → Option (XSt Nat Nat)}
    {C : Cfg Nat Nat} :
    ∀ {s : XSt Nat Nat} {ls : List (XLbl Nat Nat)} {tr : List (XStep Nat Nat)},
      env014_trace g C s ls = some tr → XRun (fun C s l s' => g C s l = some s') C s tr
  | s, [], tr, h => by cases h; trivial
  | s, l :: ls, tr, h => by
    simp only [env014_trace] at h
    cases hs : g C s l with
    | none => simp [hs] at h
    | some s' =>
      simp only [hs, Option.bind_some] at h
      cases ht : env014_trace g C s' ls with
      | none => simp [ht] at h
      | some tr' =>
        simp only [ht, Option.map_some, Option.some.injEq] at h
        subst h
        exact ⟨rfl, hs, env014_trace_run ht⟩

/-- Read a decided fact `p` off the trace of a label run of `g`. -/
theorem env014_run_of_check
    (g : Cfg Nat Nat → XSt Nat Nat → XLbl Nat Nat → Option (XSt Nat Nat)) {C : Cfg Nat Nat}
    {s0 : XSt Nat Nat} {ls : List (XLbl Nat Nat)} {p : List (XStep Nat Nat) → Bool}
    (h : (env014_trace g C s0 ls).map p = some true) :
    ∃ tr, XRun (fun C s l s' => g C s l = some s') C s0 tr ∧ p tr = true := by
  cases ht : env014_trace g C s0 ls with
  | none => simp [ht] at h
  | some tr => exact ⟨tr, env014_trace_run ht, by simpa [ht] using h⟩

/-- The label is an answer that reports a restore point. -/
def env014_isRestore : XLbl Nat Nat → Bool
  | .snapshot (some false) => true
  | _ => false

/-- The label is an answer that reports work in flight. -/
def env014_isTrueSnap : XLbl Nat Nat → Bool
  | .snapshot (some true) => true
  | _ => false

/-- A label `env014_isTrueSnap` accepts is the answer `some true`. -/
theorem env014_isTrueSnap_eq {l : XLbl Nat Nat} (h : env014_isTrueSnap l = true) :
    l = .snapshot (some true) := by
  match l, h with
  | .snapshot (some true), _ => rfl

/-- A label `env014_isRestore` accepts is the answer `some false`. -/
theorem env014_isRestore_eq {l : XLbl Nat Nat} (h : env014_isRestore l = true) :
    l = .snapshot (some false) := by
  match l, h with
  | .snapshot (some false), _ => rfl

/-- A wrong executor that answers snapshot requests by `g` and takes every other step as the
reference does. -/
def env014_snapStep (g : Cfg Nat Nat → XSt Nat Nat → Option Bool → Option (XSt Nat Nat))
    (C : Cfg Nat Nat) (s : XSt Nat Nat) : XLbl Nat Nat → Option (XSt Nat Nat)
  | .snapshot a => g C s a
  | l => xstep C s l

/-- The executor of `env014_snapStep g`. -/
def env014_snapRel (g : Cfg Nat Nat → XSt Nat Nat → Option Bool → Option (XSt Nat Nat)) :
    XRel Nat Nat :=
  fun C s l s' => env014_snapStep g C s l = some s'

/-! ### Violation: the answer drains the executor (line 1) -/

/-- An answer that drains the executor, as a snapshot taken through `drain()` would: the request
is answered and the executor stops accepting. -/
def env014_drainingSnap (C : Cfg Nat Nat) (s : XSt Nat Nat) (a : Option Bool) :
    Option (XSt Nat Nat) :=
  (snapshotStep C s a).map fun s' => { s' with mode := .draining }

/-- ✗ An answer that drains the executor violates ENV-014 (line 1, 'without affecting
lifecycle'): with `t` in flight the answer `some true` leaves the executor draining. -/
@[evidence forbids ENV_014]
theorem ENV_014_forbids_drainingSnapshot :
    ¬ ENV_014 (env014_snapRel env014_drainingSnap) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check (env014_snapStep env014_drainingSnap)
    (C := env014_c) (o := env014_at env014_inFlight) (l := .snapshot (some true))
    (p := fun s s' => s.mode != s'.mode) (by decide)
  have := (h env014_c).1 _ s s' hs
  subst this
  simp at hp

/-! ### Violation: the answer wakes a parked orchestrator (line 1, AC9) -/

/-- An answer that needs the orchestrator to leave its wait: a request to a parked executor wakes
it and the loop goes back to step 1. -/
def env014_wakingSnap (C : Cfg Nat Nat) (s : XSt Nat Nat) (a : Option Bool) :
    Option (XSt Nat Nat) :=
  (snapshotStep C s a).map fun s' =>
    if s'.parked then { s' with parked := false, phase := .completions } else s'

/-- ✗ An answer that wakes the parked orchestrator violates ENV-014 (line 1, AC9 'answers
without waking'): the loop is blocked in its wait and the answer `some false` unblocks it. -/
@[evidence forbids ENV_014]
theorem ENV_014_forbids_wakingSnapshot :
    ¬ ENV_014 (env014_snapRel env014_wakingSnap) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check (env014_snapStep env014_wakingSnap)
    (C := env014_c) (o := env014_at env014_parked) (l := .snapshot (some false))
    (p := fun s s' => s.parked != s'.parked) (by decide)
  have := (h env014_c).1 _ s s' hs
  subst this
  simp at hp

/-! ### Violation: an answer after a drain (line 2) -/

/-- An answer that ignores the lifecycle: a drained, closed or stopped executor still answers
with a marking and its flag (Rust's executor arm alone, without the handle's refusal). -/
def env014_afterDrainSnap (C : Cfg Nat Nat) (s : XSt Nat Nat) (a : Option Bool) :
    Option (XSt Nat Nat) :=
  if liveB C s && (s.phase = .events || s.phase = .update || s.phase = .await) &&
      a == some (!s.fl.isEmpty || !s.eq.isEmpty) then some s else none

/-- ✗ Answering a drained executor violates ENV-014 (line 2, AC4): after the drain the request is
answered `some true`. -/
@[evidence forbids ENV_014]
theorem ENV_014_forbids_answersAfterDrain :
    ¬ ENV_014 (env014_snapRel env014_afterDrainSnap) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check (env014_snapStep env014_afterDrainSnap)
    (C := env014_c) (o := env014_at env014_drained) (l := .snapshot (some true))
    (p := fun s _ => s.mode == .draining) (by decide)
  have hm : s.mode = .draining := by simpa using hp
  have := (h env014_c).2.1 _ s s' hs (by rw [hm]; decide)
  exact absurd this (by simp)

/-! ### Violation: a rejection while work is in flight (line 3) -/

/-- A refusal shape misread as a rejection: while work is in flight the request is rejected like
a request to a closed executor, and otherwise answered as a restore point. -/
def env014_busyRejectSnap (C : Cfg Nat Nat) (s : XSt Nat Nat) (a : Option Bool) :
    Option (XSt Nat Nat) :=
  if liveB C s && (s.phase = .events || s.phase = .update || s.phase = .await) &&
      a == (if s.mode = .open && s.fl.isEmpty && s.eq.isEmpty then some false else none)
  then some s else none

/-- ✗ Rejecting a running open executor violates ENV-014 (line 3, AC1): with `t` in flight the
request is answered `none`, which the caller cannot tell from a closed executor. -/
@[evidence forbids ENV_014]
theorem ENV_014_forbids_rejectsWhileBusy :
    ¬ ENV_014 (env014_snapRel env014_busyRejectSnap) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check (env014_snapStep env014_busyRejectSnap)
    (C := env014_c) (o := env014_at env014_inFlight) (l := .snapshot none)
    (p := fun s _ => s.mode == .open && isExecPhase s.phase) (by decide)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact (h env014_c).2.2.1 _ s s' hs hp.1 hp.2 rfl

/-! ### Violation: in flight only once the action suspends (line 4, AC8) -/

/-- An executor that answers inside the firing pass as well (an inline action asking for a
snapshot on the orchestrator's thread), and counts a firing as in flight only once its action has
suspended: a synchronous action still running its prefix is not counted. -/
def env014_suspendOnlySnap (C : Cfg Nat Nat) (s : XSt Nat Nat) (a : Option Bool) :
    Option (XSt Nat Nat) :=
  if liveB C s &&
      (s.phase = .events || s.phase = .update || s.phase = .await || s.phase = .pass) &&
      a == (if s.mode = .open then some (s.fl.any (!·.sync) || !s.eq.isEmpty) else none)
  then some s else none

/-- ✗ Not counting a synchronous action's prefix violates ENV-014 (line 4, AC8 and the quoted
'from the moment its inputs are consumed'): `t` has started synchronously, its token consumed,
and the snapshot its action asks for is answered `some false`. -/
@[evidence forbids ENV_014]
theorem ENV_014_forbids_suspendOnlyInFlight :
    ¬ ENV_014 (env014_snapRel env014_suspendOnlySnap) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check (env014_snapStep env014_suspendOnlySnap)
    (C := env014_c) (o := env014_at env014_sync) (l := .snapshot (some false))
    (p := fun s _ => !s.fl.isEmpty) (by decide)
  have := (h env014_c).2.2.2.1 s s' hs
  simp [this] at hp

/-! ### Violation: always a restore point (line 4, AC5 and AC6) -/

/-- An executor without the indication: every answer of an open executor reports a restore
point. -/
def env014_alwaysRestoreSnap (C : Cfg Nat Nat) (s : XSt Nat Nat) (a : Option Bool) :
    Option (XSt Nat Nat) :=
  if liveB C s && (s.phase = .events || s.phase = .update || s.phase = .await) &&
      a == (if s.mode = .open then some false else none)
  then some s else none

/-- ✗ Reporting a restore point with an action in flight violates ENV-014 (line 4, AC5 and AC6):
the net's only marked place fed `t`, whose action is in flight, and the answer is
`some false`. -/
@[evidence forbids ENV_014]
theorem ENV_014_forbids_alwaysRestorePoint :
    ¬ ENV_014 (env014_snapRel env014_alwaysRestoreSnap) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check (env014_snapStep env014_alwaysRestoreSnap)
    (C := env014_c) (o := env014_at env014_inFlight) (l := .snapshot (some false))
    (p := fun s _ => !s.fl.isEmpty) (by decide)
  have := (h env014_c).2.2.2.1 s s' hs
  simp [this] at hp

/-! ### Violation: an indication from the actions alone (line 5, AC7) -/

/-- An executor whose indication reads the actions alone and forgets the accepted events still
queued. -/
def env014_actionsOnlySnap (C : Cfg Nat Nat) (s : XSt Nat Nat) (a : Option Bool) :
    Option (XSt Nat Nat) :=
  if liveB C s && (s.phase = .events || s.phase = .update || s.phase = .await) &&
      a == (if s.mode = .open then some !s.fl.isEmpty else none)
  then some s else none

/-- ✗ An indication that ignores the event queue violates ENV-014 (line 5, AC7): an event is
accepted while the loop waits with nothing in flight, and the answer reports a restore point
whose marking does not hold the event's token. -/
@[evidence forbids ENV_014]
theorem ENV_014_forbids_actionsOnlyFlag :
    ¬ ENV_014 (env014_snapRel env014_actionsOnlySnap) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check (env014_snapStep env014_actionsOnlySnap)
    (C := env014_c) (o := env014_at env014_queued) (l := .snapshot (some false))
    (p := fun s _ => !s.eq.isEmpty && (s.M 0).isEmpty) (by decide)
  have := (h env014_c).2.2.2.2.1 s s' hs
  simp [this] at hp

/-! ### Violation: an answer before step 1b deposits (line 6, AC8 'outputs deposited') -/

/-- An executor that serves snapshot requests before step 1b as well (Rust's loop with Phase 2,
`handle_signal`, moved before Phase 1b, `handle_flush`), its flag still the firings in flight or
a queued event. -/
def env014_earlySnap (C : Cfg Nat Nat) (s : XSt Nat Nat) (a : Option Bool) :
    Option (XSt Nat Nat) :=
  if liveB C s && (s.phase = .publications || s.phase = .events || s.phase = .update ||
      s.phase = .await) && a == snapAnswer s then some s else none

/-- ✗ Answering before step 1b violates ENV-014 (line 6, AC8 'outputs deposited, no token
missing'): `t`'s action flushes `5` for place `1` in the wait and returns, its completion is
committed, and in step 1b, before the batch lands, the answer reports a restore point with the
published token in no place. Lines 1 to 5 hold of this executor: its answers are the
reference's. -/
@[evidence forbids ENV_014]
theorem ENV_014_forbids_answerBeforeDeposit :
    ¬ ENV_014 (env014_snapRel env014_earlySnap) := by
  intro h
  obtain ⟨tr, hr, hp⟩ := env014_run_of_check (env014_snapStep env014_earlySnap)
    (C := env014_c) (s0 := env014_s0) (ls := env014_published ++ [.snapshot (some false)])
    (p := fun tr => tr.any fun x => env014_isRestore x.2.1 && !x.1.pq.isEmpty &&
      (x.1.M 1).isEmpty) (by decide)
  obtain ⟨x, hx, hb⟩ := List.any_eq_true.mp hp
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hb
  exact hb.1.2 ((h env014_c).2.2.2.2.2 env014_s0 tr rfl rfl hr x hx
    (env014_isRestore_eq hb.1.1))

/-! ### Every line exercised -/

/-- Every line of ENV-014 is exercised by the reference, on the test derivation's runs: (1) AC6:
with `t`'s action in flight, the net's only token is in no place and the answer is `some true`;
(2) after the completion is committed, nothing is in flight or queued and the answer is
`some false`, with the output token in place `1` (the restore point of the test derivation);
(3) AC9: the loop is blocked in its wait, the answer is `some false`, and the loop stays blocked;
(4) AC7: an event accepted while the loop waits, nothing in flight, the answer is `some true`;
(5) AC4: after a drain the answer is `none`; (6) after a close the answer is `none` (the test
derivation's 'call after close() and verify rejection'); (7) after an immediate termination the
answer is `none`; (8) line 6: a run from the initial state in which the action flushes a batch in
the wait, the answer is `some true` while the batch is queued and `some false` once step 1b has
deposited it, with the published token in place `1`. -/
@[evidence nonvacuous ENV_014]
theorem ENV_014_nonvacuous :
    (∃ s s', env014_at env014_inFlight = some s ∧
      RefExec env014_c s (.snapshot (some true)) s' ∧
      s.fl ≠ [] ∧ s.M 0 = [] ∧ s.M 1 = []) ∧
    (∃ s s', env014_at env014_settled = some s ∧
      RefExec env014_c s (.snapshot (some false)) s' ∧ s.M 1 = [5]) ∧
    (∃ s s', env014_at env014_parked = some s ∧
      RefExec env014_c s (.snapshot (some false)) s' ∧ s.parked = true ∧ s'.parked = true) ∧
    (∃ s s', env014_at env014_queued = some s ∧
      RefExec env014_c s (.snapshot (some true)) s' ∧ s.fl = [] ∧ s.eq ≠ []) ∧
    (∃ s s', env014_at env014_drained = some s ∧
      RefExec env014_c s (.snapshot none) s' ∧ s.mode = .draining) ∧
    (∃ s s', env014_at env014_closed = some s ∧
      RefExec env014_c s (.snapshot none) s' ∧ s.mode = .closed) ∧
    (∃ s s', env014_at env014_terminated = some s ∧
      RefExec env014_c s (.snapshot none) s' ∧ s.mode = .stopped) ∧
    (∃ tr, XRun RefExec env014_c env014_s0 tr ∧
      (∃ x ∈ tr, x.2.1 = .snapshot (some true) ∧ x.1.pq ≠ []) ∧
      (∃ x ∈ tr, x.2.1 = .snapshot (some false) ∧ x.1.M 1 = [5])) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨s, s', ho, hs, hp⟩ := step_of_check xstep (C := env014_c)
      (o := env014_at env014_inFlight) (l := .snapshot (some true))
      (p := fun s _ => !s.fl.isEmpty && (s.M 0).isEmpty && (s.M 1).isEmpty) (by decide)
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
      List.isEmpty_iff] at hp
    exact ⟨s, s', ho, hs, hp.1.1, hp.1.2, hp.2⟩
  · obtain ⟨s, s', ho, hs, hp⟩ := step_of_check xstep (C := env014_c)
      (o := env014_at env014_settled) (l := .snapshot (some false))
      (p := fun s _ => s.M 1 == [5]) (by decide)
    exact ⟨s, s', ho, hs, by simpa using hp⟩
  · obtain ⟨s, s', ho, hs, hp⟩ := step_of_check xstep (C := env014_c)
      (o := env014_at env014_parked) (l := .snapshot (some false))
      (p := fun s s' => s.parked && s'.parked) (by decide)
    simp only [Bool.and_eq_true] at hp
    exact ⟨s, s', ho, hs, hp.1, hp.2⟩
  · obtain ⟨s, s', ho, hs, hp⟩ := step_of_check xstep (C := env014_c)
      (o := env014_at env014_queued) (l := .snapshot (some true))
      (p := fun s _ => s.fl.isEmpty && !s.eq.isEmpty) (by decide)
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
      List.isEmpty_iff] at hp
    exact ⟨s, s', ho, hs, hp.1, hp.2⟩
  · obtain ⟨s, s', ho, hs, hp⟩ := step_of_check xstep (C := env014_c)
      (o := env014_at env014_drained) (l := .snapshot none)
      (p := fun s _ => s.mode == .draining) (by decide)
    exact ⟨s, s', ho, hs, by simpa using hp⟩
  · obtain ⟨s, s', ho, hs, hp⟩ := step_of_check xstep (C := env014_c)
      (o := env014_at env014_closed) (l := .snapshot none)
      (p := fun s _ => s.mode == .closed) (by decide)
    exact ⟨s, s', ho, hs, by simpa using hp⟩
  · obtain ⟨s, s', ho, hs, hp⟩ := step_of_check xstep (C := env014_c)
      (o := env014_at env014_terminated) (l := .snapshot none)
      (p := fun s _ => s.mode == .stopped) (by decide)
    exact ⟨s, s', ho, hs, by simpa using hp⟩
  · obtain ⟨tr, hr, hp⟩ := env014_run_of_check xstep (C := env014_c) (s0 := env014_s0)
      (ls := env014_pubRun)
      (p := fun tr => (tr.any fun x => env014_isTrueSnap x.2.1 && !x.1.pq.isEmpty) &&
        (tr.any fun x => env014_isRestore x.2.1 && x.1.M 1 == [5])) (by decide)
    simp only [Bool.and_eq_true, List.any_eq_true] at hp
    obtain ⟨⟨x, hx, hb⟩, ⟨y, hy, hc⟩⟩ := hp
    simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff] at hb
    simp only [beq_iff_eq] at hc
    exact ⟨tr, hr, ⟨x, hx, env014_isTrueSnap_eq hb.1, hb.2⟩,
      ⟨y, hy, env014_isRestore_eq hc.1, hc.2⟩⟩

end Libpetri.Spec
