import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Exec
import Libpetri.Spec.GlossaryBuild

set_option linter.missingDocs true

/-!
# EXEC-042: Terminal places (`spec/04-execution-model.md`)

Two blocks under one ID.

* `EXEC_042` (kind B): the run, over an abstract executor `R : XRel N T` (glossary
  `GlossaryExec.lean`), checked against the reference executor `RefExec`
  (`Reference/Exec.lean`). A terminal place is marked when the state is not `Live`. While a
  terminal place is marked the executor takes no step but `finish terminal` (the strict stop) and
  answers to a snapshot request that change nothing; the settle or publish step that marks a
  terminal place deposits the whole outcome or batch; an injection into a terminal place marks
  it; a step that leaves a terminal place marked, outside steps included, takes no firing out of
  flight but the one it settles; the `finish terminal` step happens only when a terminal place is marked, keeps the marking and
  the firings in flight (abandoned), and refuses the queued external events.
* `EXEC_042_build` (kind F): the build-time check (AC5), over an abstract net builder
  `NB : NetBuilder B` (`Reference/Build.lean`), checked against the reference net builder
  `refNetBuild`.

That `finish terminal` is offered at once, firings in flight or not, is coverage:
`Exec042Covers` below is the conjunct for the consistency theorem's `ExecCoversW5`. The compose
check (AC6) is the composition model's (wave W8); the verification paragraph (AC7 to AC9) is
cited by the theorems of `Novel/InFlight.lean` and `Novel/TerminalRewrite.lean`.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## EXEC-042: Terminal Places (the run) -/

requirement EXEC_042
  id "EXEC-042"
  title "Terminal Places"
  kind B
  scope "all executors, for a net that declares terminal places (SHOULD)"
  source verbatim "spec/04-execution-model.md"
  quote "A net MAY declare **terminal places** (`terminal(place)` on the net builder)."
        "A terminal place states, in the model, that the run is over once the place holds a token."
        "The executor ends the run at that point."
        "on the initial marking, before the first cycle;"
        "after every token it deposits, from an action's completion, a mid-action publication ([IO-015]), an external injection, or a synchronous action's output within the firing pass ([EXEC-001])."
        "Once a deposit marks a terminal place, **no transition starts afterwards**."
        "That includes a transition that was already enabled later in the same firing pass."
        "The deposit that marks the terminal place completes atomically: all the tokens of that completion's outcome, or of that published batch, are deposited."
        "*While* a terminal place holds a token, the executor *shall not* take any step of its loop other than ending the run with the termination reason `terminal`: it starts no transition and processes no completion, publication or external event."
        "*When* the executor deposits the outcome of a completion (its returned emission or its timeout outcome) or a published batch ([IO-015]) and one of its tokens marks a terminal place, it *shall* deposit all of that outcome or batch before the run ends."
        "Actions still in flight are abandoned. Their late results are discarded and never deposited, as in [ENV-015]."
        "Completions and external events still queued behind the deposit are not admitted. A queued external event is refused ([ENV-004]), exactly as after [ENV-013]."
        "The run ends with the termination reason `terminal` ([EXEC-041]), a completed reason."
        "The reason `terminal` takes precedence: while a terminal place holds a token, the run does not end `quiescent`, `closed` or `stopped` ([EXEC-041]); a caller whose run budget expired earlier may still have been told `stopped` ([ENV-016])."
        "A firing whose mid-action publication ([IO-015]) marked the terminal place is still running: it is abandoned like any other action in flight."
        "A snapshot taken afterwards ([ENV-014]) still reports abandoned work as work in flight."
        "Answering a snapshot request changes nothing and is not a step of the loop; [ENV-014] states the answer."
        "*If* no terminal place holds a token, *then* the executor *shall not* end the run with the termination reason `terminal`."
        "*When* a terminal place holds a token, the executor *shall* end the run with the termination reason `terminal` without waiting for the actions still in flight."
        "*When* the executor ends the run on a terminal place, it *shall* return the marking it holds at that point and *shall not* restore the tokens that abandoned firings consumed."
        "*When* the executor ends the run on a terminal place, it *shall* keep every firing still in flight as abandoned work in flight and *shall* refuse every external event still queued ([ENV-004])."
        "A terminal place MAY be an environment place: injecting into it ends the run."
        "*When* the executor injects an external event into a terminal place, it *shall* deposit the event's token there, which ends the run."
  reading "For every executor R and every configuration C, where a state is live when none of the terminal places of C holds a token:"
          "while the state is not live, R takes no executor step (a step that is not an outside step) other than finish terminal, except an answer to a snapshot request that leaves the state as it is;"
          "a commit or tdeposit step of a firing i whose target state is not live deposits exactly the whole outcome e the firing ended with (its returned emission, or its timeout outcome), each token at the tail of its place;"
          "a publish step of a firing i whose target state is not live deposits exactly the whole batch b at the head of the publication queue, which is firing i's, each token at the tail of its place;"
          "an inject step of ticket k, where the event at the head of the event queue has ticket k and is for a terminal place, leads to a state that is not live;"
          "a step whose target state is not live, an outside step included, keeps in flight (by its id) every firing that was in flight before it, except the firing it settles;"
          "a finish terminal step starts in a state that is not live, leaves the marking unchanged, keeps the firings in flight, and empties the queue of external events."
  assumes "The model is an executor R : XRel N T (glossary GlossaryExec.lean): R C s l s' says that under configuration C the step labelled l leads from executor state s to s'. The terminal places are the configuration's (Cfg.terminals); a state is live (glossary Live) when none of them holds a token. Outside steps (XLbl.outside: time passing, an action writing, flushing, returning or timing out, a caller requesting an injection, draining, closing or terminating) are not the executor's; every other label is a step of the executor's loop, except the answer to a snapshot request (EXEC-041's naming, and the quoted sentence 'Answering a snapshot request changes nothing and is not a step of the loop'). The witness is the reference executor RefExec (Reference/Exec.lean), whose every rule but finish terminal requires a live state."
          "Naming: 'ends the run with the termination reason terminal' is the finish terminal step (EXEC-041 names the reasons). 'Processes a completion' is a settle step (commit, fail, tdeposit), 'a publication' a publish step, 'an external event' an inject or discard step. A deposit from an action's completion is a commit step (in step 1, or inside the firing pass for a synchronous action, EXEC-001), a deposit of a timeout outcome a tdeposit step (EXEC-022), a deposit from a mid-action publication a publish step (IO-015), an external injection an inject step."
          "Line 1 is the first quoted shall sentence, the check points and 'no transition starts afterwards': every executor step other than finish terminal requires a live state, so the check runs after every deposit (a deposit step leads to a state the next step checks) and on the initial marking (the first step from it). An executor that checks only at the next cycle boundary starts a transition later in the same pass (EXEC_042_mutant_checkAtBoundary_killed, AC4). An executor that treats the stop as a close, admitting the queued and later completions and ending only when nothing is in flight (the behaviour of ENV-011 and ENV-013), settles a completion behind the deposit (EXEC_042_forbids_closeLike, AC2). Line 1 also forbids finish quiescent, finish closed and finish stopped while a terminal place is marked: that is the quoted precedence sentence (Java computes TERMINAL before every other reason; the reference offers no other finish from a state that is not live). Its last clause is about what a caller was told, not about a finish step: a run budget that expired earlier ends the caller's wait and reports the reason stopped (EXEC-041), and TypeScript keeps that reason when its abandoned loop later stops on a terminal place (it assigns terminal, closed or quiescent only while the reason is still running, typescript/src/runtime/bitmap-net-executor.ts, run and executeLoop); the loop itself still ends with a terminal finish, which line 1 states."
          "Snapshots: an answer to a snapshot request is exempt from line 1 only when it leaves the state as it is, so it cannot unmark the terminal place or settle anything; what it answers is ENV-014's. The reference answers none while a terminal place is marked (snapshotStep requires a live state); Java breaks its loop before serviceMarkingRequest; Rust answers a snapshot queued behind the stop after its loop, from the state finish terminal leaves. That state keeps the firings in flight (lines 5 and 6), so its answer reports the abandoned work as work in flight: EXEC_042_nonvacuous decides snapAnswer of the state AC2's run ends in to be some true, the quoted 'A snapshot taken afterwards ([ENV-014]) still reports abandoned work as work in flight.'"
          "Line 2 is the second quoted shall sentence for a completion and 'the deposit that marks the terminal place completes atomically': the step that marks a terminal place deposits the firing's whole outcome, not the outputs up to the first token in a terminal place (EXEC_042_forbids_partialDeposit). That every commit and tdeposit deposits its whole outcome is EXEC-020's, EXEC-021's and EXEC-022's; this line states it for the step that ends the run. Which label deposits which outcome (a commit a returned emission, a tdeposit a timeout outcome) is not this line's: EXEC-021 line 1 ties a commit to a returned emission, and EXEC-022 ties a tdeposit to a timeout outcome. Outside the model: an event store throwing on TokenAdded while Java deposits a completion (processSyncOutput and processCompletedTransitions in BitmapNetExecutor.java), which Java reports as a failure of a partly deposited firing; if a token of the deposited prefix marked a terminal place, the stop is latched with a partial outcome. The model's deposit is atomic and has no host callback that can throw, so line 2 reads the model's deposits only (as EXEC-030's assumes do for its line 1)."
          "Line 3 is the second quoted shall sentence for a published batch and the check point 'a mid-action publication ([IO-015])': a publish step that marks a terminal place deposits the whole batch at the head of the publication queue (EXEC_042_forbids_partialPublish). The publishing firing is still running when its batch marks the place; it is abandoned like any other action in flight (the quoted bullet), so its later writes and its returned emission are never deposited. EXEC_042_nonvacuous publishes a batch of a that marks 9 and 3, with a and b both still in flight, and finishes terminal. A batch still queued at the stop is discarded: the reference's finish terminal empties the publication queue (EXEC-020)."
          "Line 4 is 'A terminal place MAY be an environment place: injecting into it ends the run.' and its shall sentence: an inject step of a queued event for a terminal place marks that place, so the state is not live and line 1 ends the run there (AC3). An executor that drops such an event instead of injecting it, so that a terminal environment place can never be marked from outside, violates it (EXEC_042_forbids_dropTerminalInject). That every inject step deposits its event's token at the tail of its place is ENV-003's; line 4 states only that the place is marked."
          "Line 5 is 'keep every firing still in flight as abandoned work in flight' from the deposit on, and with line 6 the quoted 'A snapshot taken afterwards ([ENV-014]) still reports abandoned work as work in flight.': every step whose target state is not live takes no firing out of flight except the one it settles (a commit, fail or tdeposit of that firing). The line covers outside steps too: between the deposit and the finish, line 1 leaves only outside steps and unchanged snapshot answers, so an action of an abandoned firing that returns, writes, flushes or times out after the stop must not take its firing out of the list. It compares ids because those outside steps rewrite the firing's record (its buffer or outcome) while it stays in flight; the reference keeps the list of ids on every outside step (exec042_fl_keep_id, from xstepW_outside_frame). An executor that cancels the firings in flight at the deposit that marks a terminal place (clearing its in-flight map at the latch) violates it (EXEC_042_forbids_cancelInFlight), although its finish terminal keeps the list it finds, which is then empty. An executor whose completion callback deregisters a late action (whenComplete(() -> inFlight.remove(t)) or .then(() => inFlight.delete(t))) violates it (EXEC_042_forbids_retDropAfterStop): on AC2's run, b's action returns after the stop, finish terminal then keeps an empty list, and a snapshot would report no work in flight. The runtimes keep the firing: Rust changes in_flight_count only in its orchestrator loop (rust/libpetri-runtime/src/executor_core/executor.rs), Java removes from inFlight only in processCompletedTransitions and fireTransitionGuarded (BitmapNetExecutor.java), TypeScript deletes from inFlight only in processCompletedTransitions and its fire guard (typescript/src/runtime/bitmap-net-executor.ts); none of these runs after the stop."
          "Line 6 is the third, fifth and sixth quoted shall sentences: the finish terminal step happens only when a terminal place is marked (EXEC_042_forbids_terminalAtRest), keeps the marking, so the tokens the abandoned firings consumed stay consumed (EXEC_042_forbids_rollbackOnStop), keeps the firings in flight, which a snapshot taken afterwards reports as in flight (EXEC_042_forbids_dropInFlight), and empties the queue of external events, which refuses them (EXEC_042_forbids_keepQueued). Emptying the queue is how this level reads 'refuse': a refused event and a dropped one look the same here, and the completion signal of each event cleared by finish terminal is false (ENV-004, design R17), a line the ENV-004 block owes. The reference also empties the publication queue (EXEC-020: a queued publication is discarded)."
          "The fourth quoted shall sentence ('without waiting for the actions still in flight') says that finish terminal is offered at once, firings in flight or not. That is coverage, which a safety line cannot state, so no line of this block encodes it; coverage belongs to the consistency theorem, whose coverage conjunct ExecCoversW5 (ConsistencyExec.lean) carries it. An executor that offers finish terminal only once every action in flight has returned (exec042_wait, a stop written in the shape of a close) satisfies this block (exec042_wait_meets) and the wave 0 ExecCovers, and fails that conjunct. The conjunct is Exec042Covers (finish terminal offered from every running state that is not live): the reference meets it (exec042_ref_covers, from exec042_finish_offered) and exec042_wait does not (exec042_wait_not_covered, on AC2's run with b's action not returned)."
          "Late results: after the stop the run is over, so no step deposits anything (EXEC-041: no executor step after finish). Before the finish, line 1 forbids settling a completion, and an action's own steps (write, ret, expire) leave the marking unchanged (CONC-001). Together: once a terminal place is marked, every later step of a run is an outside step, an unchanged snapshot answer or finish terminal (exec042_stop_absorbs, under CONC-001's frame of outside steps; exec042_ref_stop_absorbs for the reference)."
          "Requests: a request that arrives between the terminal deposit and the finish is accepted into the event queue and cleared by the finish (Rust: inject returns true once enqueued, the event is dropped with the receiver). Its answer is ENV-004's."
          "Events: 'No diagnostic event is emitted ([EVT-013] AC5): the stop was designed, not caller-requested.' is not encoded here; the executor relation carries no events, and EVT-013 (AC5) is the requirement that states it."
          "Scope: the configuration's terminal places are given; that they are the places the net declared, and that a declared terminal place is not consumed or read, is the build block EXEC_042_build. A terminal place that is an environment place ends the run when an injection marks it (line 4, AC3)."
          "Runtimes (java/README.md, rust/README.md and typescript/README.md, on terminal places): Java and Rust deposit a synchronous action's outputs inside the firing pass (a commit in phase pass) and break the pass there; TypeScript settles a synchronous firing in step 1, so a transition started earlier in the same pass is abandoned instead. Both are runs of RefExec (settleOk: a synchronous firing may settle in the pass or in step 1), and line 1 holds of both."
          "AC1 (initial marking marks a terminal place: fires nothing, ends terminal) is line 1 from the initial state (exec042_stop_absorbs); EXEC_042_nonvacuous finishes terminal from the initial state of such a net and shows that step 1 of the loop is not offered there."
          "AC2 (an asynchronous completion marks a terminal place; the run does not wait for another action in flight, whose result never appears) is lines 1, 5 and 6; EXEC_042_nonvacuous's AC2 run finishes terminal with the other firing still in flight and its output place empty, and no settle of it is offered. That the finish is offered with the action not returned is the coverage conjunct Exec042Covers."
          "AC3 (an injection marks a terminal environment place; an event queued behind it is refused) is lines 1, 4 and 6; EXEC_042_nonvacuous's AC3 run injects into the terminal environment place, which leaves a state that is not live, offers no second inject, and finishes with the second event cleared."
          "AC4 (no transition starts after the deposit that marks a terminal place, in both deposit locations) is line 1; EXEC_042_nonvacuous's AC4 run settles a synchronous firing inside the pass, offers no start of the next transition in the order, and finishes terminal."
          "AC5 (a transition that consumes or reads a terminal place is rejected when the net is built) is the build block EXEC_042_build."
          "AC6 (compose and instantiate reject a subnet body that declares a terminal place, with an error that names the place) is stated by the composition blocks over the composition model (RefCompose): MOD-010 line 4 for instantiate (the failure and the message naming one of the body's terminal places) and MOD-025 line 7 for direct composition (the failure; its message is tested, not proven). Composing an instance needs no line of its own: an instance exists only after instantiate succeeded."
          "AC7, AC8 and AC9 (the verification paragraph: DeadlockFree with terminal places, byte-identical scripts without them, the QuiescentCount lower bound) are the verifier's; their evidence is the cites of Novel/InFlight.lean (split_covers_executor, split_stop_sound, quiescent_count_stop_sound, terminal_stop_witness) and the TerminalRewrite theorems, not encoded here. AC9's executor half (both executors end with a = ok = 0) is AC2's run up to renaming (s is place 0, a is place 1, ok is place 2, done is place 9, f is transition a with an extra output 3, t is transition b): EXEC_042_nonvacuous's AC2 run ends with places 1 and 2 empty."
  signoff "2026-11-13 85b468e1f92b7cd1 ai"
  statement : ∀ {N T : Type} [DecidableEq N], XRel N T → Prop :=
    fun R => ∀ C,
      (while (fun s => ¬ Live C s), never (fun s s' =>
        ∃ l, l.outside = false ∧ l ≠ .finish .terminal ∧ (∀ a, l = .snapshot a → s' ≠ s) ∧
          R C s l s')) ∧
      (∀ i, on (fun s s' => (R C s (.commit i) s' ∨ R C s (.tdeposit i) s') ∧ ¬ Live C s'),
        shall (fun s s' => ∃ f ∈ s.fl, f.id = i ∧ ∃ e,
          (f.out = some (.ok e) ∨ f.out = some (.timedOut e)) ∧ s'.M = qAppend s.M e)) ∧
      (∀ i, on (fun s s' => R C s (.publish i) s' ∧ ¬ Live C s'),
        shall (fun s s' => ∃ b, s.pq.head? = some (i, b) ∧ s'.M = qAppend s.M b)) ∧
      (∀ k, on (fun s s' => R C s (.inject k) s' ∧
          ∃ p x, s.eq.head? = some (k, p, x) ∧ p ∈ C.terminals),
        shall (fun _ s' => ¬ Live C s')) ∧
      (∀ l, on (fun s s' => R C s l s' ∧ ¬ Live C s'),
        shall (fun s s' => ∀ f ∈ s.fl,
          (∀ i, l = .commit i ∨ l = .fail i ∨ l = .tdeposit i → f.id ≠ i) →
            ∃ g ∈ s'.fl, g.id = f.id)) ∧
      (on (fun s s' => R C s (.finish .terminal) s'), shall (fun s s' =>
        ¬ Live C s ∧ s'.M = s.M ∧ s'.fl = s.fl ∧ s'.eq = []))

/- The pinned readable form of EXEC-042: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EXEC_042 : {N T : Type} → [DecidableEq N] → XRel N T → Prop :=
fun {N T} [DecidableEq N] R =>
  ∀ (C : Cfg N T),
    (while fun s => ¬Live C s, never fun s s' =>
        ∃ l,
          l.outside = false ∧
            l ≠ XLbl.finish Cause.terminal ∧ (∀ (a : Option Bool), l = XLbl.snapshot a → s' ≠ s) ∧ R C s l s') ∧
      (∀ (i : ℕ),
          on fun s s' => (R C s (XLbl.commit i) s' ∨ R C s (XLbl.tdeposit i) s') ∧ ¬Live C s', shall fun s s' =>
            ∃ f ∈ s.fl,
              f.id = i ∧
                ∃ e, (f.out = some (Outcome.ok e) ∨ f.out = some (Outcome.timedOut e)) ∧ s'.M = qAppend s.M e) ∧
        (∀ (i : ℕ),
            on fun s s' => R C s (XLbl.publish i) s' ∧ ¬Live C s', shall fun s s' =>
              ∃ b, s.pq.head? = some (i, b) ∧ s'.M = qAppend s.M b) ∧
          (∀ (k : ℕ),
              on fun s s' => R C s (XLbl.inject k) s' ∧ ∃ p x, s.eq.head? = some (k, p, x) ∧ p ∈ C.terminals, shall
                fun x s' => ¬Live C s') ∧
            (∀ (l : XLbl N T),
                on fun s s' => R C s l s' ∧ ¬Live C s', shall fun s s' =>
                  ∀ f ∈ s.fl,
                    (∀ (i : ℕ), l = XLbl.commit i ∨ l = XLbl.fail i ∨ l = XLbl.tdeposit i → f.id ≠ i) →
                      ∃ g ∈ s'.fl, g.id = f.id) ∧
              on fun s s' => R C s (XLbl.finish Cause.terminal) s', shall fun s s' =>
                ¬Live C s ∧ s'.M = s.M ∧ s'.fl = s.fl ∧ s'.eq = []
-/
#guard_msgs in #print EXEC_042

/-! ### The reference -/

section Reference

variable {N T : Type} [DecidableEq N]

/-- Every executor rule of the reference but `finish terminal` requires a live state. -/
theorem exec042_live_of_step {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : RefExec C s l s') (ho : l.outside = false) (hl : l ≠ .finish .terminal) :
    liveB C s = true := by
  have hcs : ∀ {i f}, canSettle C s i f = true → liveB C s = true := by
    intro i f hc
    unfold canSettle at hc
    simp only [Bool.and_eq_true] at hc
    exact hc.1.1.2
  cases l with
  | commit i => obtain ⟨f, -, -, -, hc, -⟩ := commitStep_some h; exact hcs hc
  | fail i => obtain ⟨f, -, hc, -⟩ := failStep_some h; exact hcs hc
  | tdeposit i => obtain ⟨f, -, -, -, hc, -⟩ := tdepositStep_some h; exact hcs hc
  | endCompletions => exact (xstepW_endCompletions h).2.1
  | publish i => obtain ⟨-, -, -, hl', -⟩ := publishStep_some h; exact hl'
  | endPublications => exact (xstepW_endPublications h).2.1
  | inject k => obtain ⟨-, -, -, -, hl', -⟩ := injectStep_some h; exact hl'
  | discard k => obtain ⟨-, -, -, -, hl', -⟩ := discardStep_some h; exact hl'
  | endEvents => exact (xstepW_endEvents h).2.1
  | snapshot a => exact (snapshotStep_some h).1
  | update => exact (xstepW_update h).2.1
  | deadline ns => exact (xstepW_deadline h).2.1
  | begin => exact (xstepW_begin h).2.1
  | start n sy => obtain ⟨-, -, -, -, hl', -⟩ := startStep_some h; exact hl'
  | lose n => obtain ⟨-, -, -, -, hl', -⟩ := loseStep_some h; exact hl'
  | endPass => exact (xstepW_endPass h).2.1
  | finish c =>
    cases c with
    | quiescent => exact (xstepW_finishQuiescent h).2.1
    | closed => exact (xstepW_finishClosed h).2.1
    | stopped => exact (xstepW_finishStopped h).2.1
    | terminal => exact absurd rfl hl
  | park tmr => exact (parkStep_some h).2.1
  | wake => exact (wakeStep_some h).2.1
  | _ => simp [XLbl.outside] at ho

/-- The marking after a deposit of `e` by `depositAt` is the old one with `e` at the tails. -/
theorem exec042_depositAt_M (C : Cfg N T) (s : XSt N T) (i : Nat) (e : List (N × T)) :
    (depositAt C s i e).M = qAppend s.M e := rfl

/-- Every executor rule of the reference keeps in flight every firing but the one it settles: a
settle removes its own firing, a start adds one, every other rule leaves the list as it is. -/
theorem exec042_fl_keep {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : RefExec C s l s') (ho : l.outside = false) :
    ∀ f ∈ s.fl, (∀ i, l = .commit i ∨ l = .fail i ∨ l = .tdeposit i → f.id ≠ i) → f ∈ s'.fl := by
  intro f hf hne
  have hset : ∀ i, f.id ≠ i → f ∈ (settle s i).fl := fun i hi => by
    simp [settle, List.mem_filter, hf, hi]
  cases l with
  | commit i =>
    obtain ⟨_, _, _, _, _, _, _, rfl⟩ := commitStep_some h; exact hset i (hne i (.inl rfl))
  | fail i =>
    obtain ⟨_, _, _, _, rfl⟩ := failStep_some h; exact hset i (hne i (.inr (.inl rfl)))
  | tdeposit i =>
    obtain ⟨_, _, _, _, _, _, rfl⟩ := tdepositStep_some h; exact hset i (hne i (.inr (.inr rfl)))
  | endCompletions => rw [(xstepW_endCompletions h).2.2.2.2]; exact hf
  | publish i => obtain ⟨_, _, _, _, _, rfl⟩ := publishStep_some h; exact hf
  | endPublications => rw [(xstepW_endPublications h).2.2.2]; exact hf
  | inject k => obtain ⟨_, _, _, _, _, _, _, rfl⟩ := injectStep_some h; exact hf
  | discard k => obtain ⟨_, _, _, _, _, _, _, rfl⟩ := discardStep_some h; exact hf
  | endEvents => rw [(xstepW_endEvents h).2.2.2]; exact hf
  | snapshot a => rw [(snapshotStep_some h).2.2.2]; exact hf
  | update => rw [(xstepW_update h).2.2]; exact hf
  | deadline ns => rw [(xstepW_deadline h).2.2.2]; exact hf
  | begin => rw [(xstepW_begin h).2.2.2.2]; exact hf
  | start n sy =>
    obtain ⟨_, _, _, _, _, _, _, _, _, rfl⟩ := startStep_some h; exact List.mem_append_left _ hf
  | lose n => obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := loseStep_some h; exact hf
  | endPass => rw [(xstepW_endPass h).2.2.2.2]; exact hf
  | finish c =>
    cases c with
    | quiescent => rw [(xstepW_finishQuiescent h).2.2.2]; exact hf
    | closed => rw [(xstepW_finishClosed h).2.2.2.2]; exact hf
    | stopped => rw [(xstepW_finishStopped h).2.2.2]; exact hf
    | terminal => rw [(xstepW_finishTerminal h).2.2]; exact hf
  | park tmr => rw [(parkStep_some h).2.2.2.2.2.2.2.2]; exact hf
  | wake => rw [(wakeStep_some h).2.2]; exact hf
  | _ => simp [XLbl.outside] at ho

/-- Every rule of the reference, outside steps included, keeps in flight (by id) every firing but
the one it settles: an executor rule by `exec042_fl_keep`; an outside step (a write, flush,
return or expiry rewrites the firing's record through `updFiring`; time passing, a request, drain,
close and terminate leave the list alone) keeps the list of ids (`xstepW_outside_frame`). -/
theorem exec042_fl_keep_id {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : RefExec C s l s') :
    ∀ f ∈ s.fl, (∀ i, l = .commit i ∨ l = .fail i ∨ l = .tdeposit i → f.id ≠ i) →
      ∃ g ∈ s'.fl, g.id = f.id := by
  intro f hf hne
  cases ho : l.outside
  · exact ⟨f, exec042_fl_keep h ho f hf hne, rfl⟩
  · have hm : s'.fl.map (·.id) = s.fl.map (·.id) := (xstepW_outside_frame h ho).2.2.2.1
    have hmem : f.id ∈ s'.fl.map (·.id) := by rw [hm]; exact List.mem_map_of_mem hf
    obtain ⟨g, hg, he⟩ := List.mem_map.1 hmem
    exact ⟨g, hg, he⟩

end Reference

/-- ✓ The reference executor satisfies EXEC-042: every rule but `finish terminal` requires a live
state (`exec042_live_of_step`), `commit` and `tdeposit` deposit the whole outcome (`depositAt`),
`publish` the whole head batch, `inject` appends its token to its place, every rule, outside
steps included, keeps in flight every firing but the one it settles (`exec042_fl_keep_id`), and `finish terminal` requires a
non-live state and changes only the phase and the two queues. -/
@[evidence holds EXEC_042]
theorem EXEC_042_reference {N T : Type} [DecidableEq N] :
    EXEC_042 (RefExec (N := N) (T := T)) := by
  intro C
  refine ⟨fun s s' ⟨l, ho, hl, _, h⟩ hn => hn (exec042_live_of_step h ho hl),
    fun i s s' hh => ?_, fun i s s' hh => ?_, fun k s s' hh => ?_,
    fun l s s' ⟨h, _⟩ => exec042_fl_keep_id h, fun s s' h => ?_⟩
  · obtain ⟨h, -⟩ := hh
    rcases h with h | h
    · obtain ⟨f, e, hf, he, -, -, -, rfl⟩ := commitStep_some h
      exact ⟨f, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, e, .inl he, rfl⟩
    · obtain ⟨f, e, hf, he, -, -, rfl⟩ := tdepositStep_some h
      exact ⟨f, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, e, .inr he, rfl⟩
  · obtain ⟨h, -⟩ := hh
    obtain ⟨b, rest, hpq, -, -, rfl⟩ := publishStep_some h
    exact ⟨b, by simp [hpq], rfl⟩
  · obtain ⟨h, p, x, hhd, hp⟩ := hh
    obtain ⟨p', x', rest, he, -, -, -, rfl⟩ := injectStep_some h
    rw [he] at hhd
    simp only [List.head?_cons, Option.some.injEq, Prod.mk.injEq] at hhd
    obtain ⟨-, rfl, rfl⟩ := hhd
    intro hL
    have := List.all_eq_true.1 hL p' hp
    simp [qAppendOne] at this
  · obtain ⟨-, hl, rfl⟩ := xstepW_finishTerminal h
    exact ⟨fun hL => by simp [Live, hl] at hL, rfl, rfl, rfl⟩

/-! ### Consequence: the stop absorbs the run -/

/-- Whether a state is live depends on its marking only. -/
theorem exec042_live_congr {N T : Type} {C : Cfg N T} {s s' : XSt N T} (h : s'.M = s.M) :
    Live C s' ↔ Live C s := by
  simp [Live, liveB, h]

/-- Once a terminal place is marked, every later step of a run of an executor satisfying EXEC-042
is an outside step, an answer to a snapshot request that changes nothing, or `finish terminal`,
given that outside steps leave the marking as it is ([CONC-001]): nothing starts, nothing
settles, nothing is injected (AC1, AC2, AC3, AC4). -/
theorem exec042_stop_absorbs {N T : Type} [DecidableEq N] {R : XRel N T} (h : EXEC_042 R)
    {C : Cfg N T}
    (hO : ∀ s l s', l.outside = true → R C s l s' → s'.M = s.M) :
    ∀ (tr : List (XStep N T)) (s0 : XSt N T), XRun R C s0 tr → ¬ Live C s0 →
      ∀ st ∈ tr, st.2.1.outside = true ∨ st.2.1 = .finish .terminal ∨
        ((∃ a, st.2.1 = .snapshot a) ∧ st.2.2 = st.1)
  | [], _, _, _ => by simp
  | (a, l, s1) :: rest, s0, hr, hL => by
    obtain ⟨ha, hs, hrest⟩ := hr
    simp only at ha hs
    subst ha
    have hcase : l.outside = true ∨ l = .finish .terminal ∨ ((∃ x, l = .snapshot x) ∧ s1 = a) := by
      cases ho : l.outside
      · by_cases ht : l = .finish .terminal
        · exact .inr (.inl ht)
        · by_cases hsn : (∃ x, l = .snapshot x) ∧ s1 = a
          · exact .inr (.inr hsn)
          · exact ((h C).1 a s1 ⟨l, ho, ht, fun x hx he => hsn ⟨⟨x, hx⟩, he⟩, hs⟩ hL).elim
      · exact .inl rfl
    have hM : s1.M = a.M := by
      rcases hcase with ho | ht | ⟨-, he⟩
      · exact hO a l s1 ho hs
      · subst ht; exact ((h C).2.2.2.2.2 a s1 hs).2.1
      · rw [he]
    have hL1 : ¬ Live C s1 := fun h1 => hL ((exec042_live_congr hM).1 h1)
    intro st hst
    rcases List.mem_cons.1 hst with rfl | hst
    · exact hcase
    · exact exec042_stop_absorbs h hO rest s1 hrest hL1 st hst

/-- The reference executor: once a terminal place is marked, every later step of a run is an
outside step, an unchanged snapshot answer or `finish terminal`. -/
theorem exec042_ref_stop_absorbs {N T : Type} [DecidableEq N] {C : Cfg N T}
    (tr : List (XStep N T)) (s0 : XSt N T) (hr : XRun RefExec C s0 tr) (hL : ¬ Live C s0) :
    ∀ st ∈ tr, st.2.1.outside = true ∨ st.2.1 = .finish .terminal ∨
      ((∃ a, st.2.1 = .snapshot a) ∧ st.2.2 = st.1) :=
  exec042_stop_absorbs EXEC_042_reference
    (fun _ _ _ ho hs => (xstepW_outside_frame hs ho).1) tr s0 hr hL

/-! ### Examples

Places `0` to `3` and `9`; place `9` is terminal and an environment place. Transition `a` takes a
token from `0` and has output `And(9, 3)`; transition `b` takes a token from `1` and has output
`Place 2`; both have priority 0, so the ready order is the declaration order, `a` before `b`
(EXEC-002). The validator is the reference validator of IO-015. -/

/-- Transition `a`: one token from `0`, output `And(9, 3)`. -/
def exec042_ta : Trans Nat :=
  { core := { name := "a", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.and (.place 9) (.place 3)) }

/-- Transition `b`: one token from `1`, output `Place 2`. -/
def exec042_tb : Trans Nat :=
  { core := { name := "b", inputs := [⟨1, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 2) }

/-- The configuration: terminal and environment place `9`, `a` declared before `b`. -/
def exec042_C : Cfg Nat Nat :=
  { X := { net := { places := [0, 1, 2, 3, 9], transitions := [exec042_ta, exec042_tb] },
           timing := fun _ => .immediate, tol := 0 },
    prio := fun _ => 0, terminals := [9], envs := [9],
    reentrant := false, validate := cfgValidate ioRefValidate, relay := fun _ _ _ => true,
    timeoutOut := fun _ _ _ => false, res := 0 }

/-- The initial marking: `7` in `0`, `8` in `1`. -/
def exec042_m0 : QMarking Nat Nat := fun p => if p = 0 then [7] else if p = 1 then [8] else []

/-- One cycle up to the firing pass. -/
def exec042_pre : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin]

/-- The reference state after `ls` from the initial marking. -/
def exec042_at (ls : List (XLbl Nat Nat)) : Option (XSt Nat Nat) :=
  xrun exec042_C (xinit exec042_m0 0) ls

/-- AC4: `a` starts synchronously, writes `5` to `9` and `6` to `3`, and returns. -/
def exec042_runSync : List (XLbl Nat Nat) :=
  exec042_pre ++ [.start "a" true, .write 0 9 5, .write 0 3 6, .ret 0 true]

/-- AC2: `a` and `b` start asynchronously; `a` writes `5` to `9` and `6` to `3` and returns. -/
def exec042_runAsync : List (XLbl Nat Nat) :=
  exec042_pre ++ [.start "a" false, .start "b" false, .endPass, .write 0 9 5, .write 0 3 6,
    .ret 0 true]

/-- A mid-action publication: `a` and `b` start asynchronously; `a` writes `5` to `9` and `6` to
`3` and flushes them without returning; the next cycle reaches step 1b. -/
def exec042_runPub : List (XLbl Nat Nat) :=
  exec042_pre ++ [.start "a" false, .start "b" false, .endPass, .write 0 9 5, .write 0 3 6,
    .flush 0, .endCompletions]

/-- AC3: two injections into the terminal environment place `9` are accepted, then step 2. -/
def exec042_runInject : List (XLbl Nat Nat) :=
  [.request 9 5 .accepted, .request 9 6 .accepted, .endCompletions, .endPublications]

/-- AC1: the initial marking marks the terminal place `9`. -/
def exec042_m0T : QMarking Nat Nat := fun p => if p = 9 then [1] else []

/-! ### Every line exercised -/

/-- ✓ Every line of EXEC-042 is exercised by the reference.
AC4: a synchronous firing of `a` settles inside the pass and deposits `5` in `9` and `6` in `3`
(its whole outcome, line 2); `b`, next in the order, is not offered a start, and `finish terminal`
is (line 1). AC2: `a` settles in step 1 while `b` is in flight; no settle of `b` is offered, and
`finish terminal` keeps `b` in flight with `2` empty and `1` consumed, so a snapshot of the end
state reports work in flight (lines 1, 5 and 6). Publication: `a`'s flushed batch marks `9` and
`3` while `a` and `b` are both in flight, and the run finishes terminal (lines 3 and 5). AC3: the
first injection marks `9`, the second is not injected, and `finish terminal` clears it (lines 1, 4
and 6). AC1: from an initial marking that marks `9`, `finish terminal` is the step offered and the
loop's first step is not (line 1). -/
@[evidence nonvacuous EXEC_042]
theorem EXEC_042_nonvacuous :
    (∃ s s', RefExec exec042_C s (.commit 0) s' ∧ ¬ Live exec042_C s' ∧ s.phase = .pass ∧
      s'.M 9 = [5] ∧ s'.M 3 = [6] ∧ xstep exec042_C s' (.start "b" false) = none ∧
      ∃ s'', RefExec exec042_C s' (.finish .terminal) s'') ∧
    (∃ s s', RefExec exec042_C s (.finish .terminal) s' ∧ ¬ Live exec042_C s ∧
      s'.fl.length = 1 ∧ s'.M 2 = [] ∧ s'.M 1 = [] ∧ snapAnswer s' = some true ∧
      xstep exec042_C s (.ret 1 true) ≠ none) ∧
    (∃ s s', RefExec exec042_C s (.publish 0) s' ∧ ¬ Live exec042_C s' ∧
      s'.M 9 = [5] ∧ s'.M 3 = [6] ∧ s'.fl.length = 2 ∧
      ∃ s'', RefExec exec042_C s' (.finish .terminal) s'') ∧
    (∃ s s', RefExec exec042_C s (.inject 0) s' ∧ s.eq.head? = some (0, 9, 5) ∧
      ¬ Live exec042_C s') ∧
    (∃ s s', RefExec exec042_C s (.finish .terminal) s' ∧ s.eq.length = 1 ∧ s'.eq = [] ∧
      s'.M 9 = [5] ∧ xstep exec042_C s (.inject 1) = none) ∧
    (∃ s', RefExec exec042_C (xinit exec042_m0T 0) (.finish .terminal) s' ∧
      xstep exec042_C (xinit exec042_m0T 0) .endCompletions = none) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨s, s', ho, hs, hp⟩ := step_of_check xstep (C := exec042_C)
      (o := exec042_at exec042_runSync) (l := .commit 0)
      (p := fun s s' => !liveB exec042_C s' && s.phase == .pass && s'.M 9 == [5] &&
        s'.M 3 == [6] && (xstep exec042_C s' (.start "b" false)).isNone &&
        (xstep exec042_C s' (.finish .terminal)).isSome) (by decide)
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, Option.isNone_iff_eq_none,
      Option.isSome_iff_exists] at hp
    obtain ⟨⟨⟨⟨⟨hl, hph⟩, h9⟩, h3⟩, hb⟩, ⟨s'', hf⟩⟩ := hp
    exact ⟨s, s', hs, by simp [Live, hl], hph, h9, h3, hb, s'', hf⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := exec042_C)
      (o := exec042_at (exec042_runAsync ++ [.commit 0])) (l := .finish .terminal)
      (p := fun s s' => !liveB exec042_C s && s'.fl.length == 1 && s'.M 2 == [] &&
        s'.M 1 == [] && snapAnswer s' == some true &&
        (xstep exec042_C s (.ret 1 true)).isSome) (by decide)
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, Option.isSome_iff_ne_none] at hp
    obtain ⟨⟨⟨⟨⟨hl, hfl⟩, h2⟩, h1⟩, hsn⟩, hr⟩ := hp
    exact ⟨s, s', hs, by simp [Live, hl], hfl, h2, h1, hsn, hr⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := exec042_C)
      (o := exec042_at exec042_runPub) (l := .publish 0)
      (p := fun _ s' => !liveB exec042_C s' && s'.M 9 == [5] && s'.M 3 == [6] &&
        s'.fl.length == 2 && (xstep exec042_C s' (.finish .terminal)).isSome) (by decide)
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, Option.isSome_iff_exists] at hp
    obtain ⟨⟨⟨⟨hl, h9⟩, h3⟩, hfl⟩, ⟨s'', hf⟩⟩ := hp
    exact ⟨s, s', hs, by simp [Live, hl], h9, h3, hfl, s'', hf⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := exec042_C)
      (o := exec042_at exec042_runInject) (l := .inject 0)
      (p := fun s s' => s.eq.head? == some (0, 9, 5) && !liveB exec042_C s') (by decide)
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hp
    exact ⟨s, s', hs, hp.1, by simp [Live, hp.2]⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := exec042_C)
      (o := exec042_at (exec042_runInject ++ [.inject 0])) (l := .finish .terminal)
      (p := fun s s' => s.eq.length == 1 && s'.eq.isEmpty && s'.M 9 == [5] &&
        (xstep exec042_C s (.inject 1)).isNone) (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff, Option.isNone_iff_eq_none] at hp
    obtain ⟨⟨⟨he, he'⟩, h9⟩, hi⟩ := hp
    exact ⟨s, s', hs, he, he', h9, hi⟩
  · refine ⟨_, rfl, by decide⟩

/-! ### Coverage: the stop does not wait (the fourth quoted shall sentence) -/

/-- **The coverage conjunct EXEC-042 asks of the consistency theorem's `ExecCoversW5`**: from every
running state in which a terminal place is marked, `finish terminal` is offered, whatever is in
flight or queued. Coverage is never a line of a block; this is the clause for `ExecCovers`. -/
def Exec042Covers {N T : Type} [DecidableEq N] (E : XRel N T) : Prop :=
  ∀ C s, ¬ Live C s → isExecPhase s.phase = true → ∃ s', E C s (.finish .terminal) s'

/-- Coverage (the fourth quoted shall sentence, for the consistency theorem's `ExecCoversW5`): the
reference offers `finish terminal` from every running state that is not live, whatever is in
flight or queued. -/
theorem exec042_finish_offered {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T)
    (hL : ¬ Live C s) (hp : isExecPhase s.phase = true) :
    ∃ s', RefExec C s (.finish .terminal) s' := by
  have hl : liveB C s = false := by simpa [Live] using hL
  exact ⟨{ s with phase := .done .terminal, eq := [], pq := [] }, by
    simp [RefExec, xstep, xstepW, hp, hl]⟩

/-- The reference meets the coverage conjunct. -/
theorem exec042_ref_covers {N T : Type} [DecidableEq N] :
    Exec042Covers (RefExec (N := N) (T := T)) :=
  fun C s hL hp => exec042_finish_offered C s hL hp

/-- Every line of EXEC-042 is a constraint on the steps an executor takes, so a sub-relation of
an executor that satisfies EXEC-042 satisfies it too. -/
theorem exec042_sub {N T : Type} [DecidableEq N] {R R' : XRel N T}
    (hR : ∀ C s l s', R C s l s' → R' C s l s') (h : EXEC_042 R') : EXEC_042 R := by
  intro C
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h C
  exact ⟨fun s s' ⟨l, a, b, c, hs⟩ => h1 s s' ⟨l, a, b, c, hR _ _ _ _ hs⟩,
    fun i s s' ⟨hh, hL⟩ => h2 i s s' ⟨hh.imp (hR _ _ _ _) (hR _ _ _ _), hL⟩,
    fun i s s' ⟨hh, hL⟩ => h3 i s s' ⟨hR _ _ _ _ hh, hL⟩,
    fun k s s' ⟨hh, hq⟩ => h4 k s s' ⟨hR _ _ _ _ hh, hq⟩,
    fun l s s' ⟨hh, hL⟩ => h5 l s s' ⟨hR _ _ _ _ hh, hL⟩,
    fun s s' hh => h6 s s' (hR _ _ _ _ hh)⟩

/-- An executor whose stop waits for the actions in flight: `finish terminal` is offered only
once every firing in flight has its outcome set (`if terminal && in_flight_count == 0 { break; }`,
the stop written in the shape of a close); otherwise the reference. -/
def exec042_waitStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .finish .terminal =>
      if s.fl.all (·.out.isSome) then xstep C s (.finish .terminal) else none
  | l => xstep C s l

/-- The executor of `exec042_waitStep`. -/
def exec042_wait {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec042_waitStep C s l = some s'

/-- The waiting executor is a sub-relation of the reference. -/
theorem exec042_wait_ref {N T : Type} [DecidableEq N] {C : Cfg N T} {s s' : XSt N T}
    {l : XLbl N T} (h : exec042_wait C s l s') : RefExec C s l s' := by
  unfold exec042_wait at h
  unfold RefExec
  cases l with
  | finish c =>
    cases c with
    | terminal =>
      unfold exec042_waitStep at h
      by_cases hw : (s.fl.all fun x => x.out.isSome) = true
      · rw [if_pos hw] at h; exact h
      · rw [if_neg hw] at h; cases h
    | _ => exact h
  | _ => exact h

/-- The gap the coverage conjunct closes: the waiting executor satisfies every line of EXEC-042,
since it only takes fewer steps than the reference. -/
theorem exec042_wait_meets {N T : Type} [DecidableEq N] : EXEC_042 (exec042_wait (N := N) (T := T)) :=
  exec042_sub (fun _ _ _ _ h => exec042_wait_ref h) EXEC_042_reference

/-- The waiting executor fails the coverage conjunct: on the AC2 run, once `a`'s completion marks
`9` with `b`'s action not returned, it offers no `finish terminal`. -/
theorem exec042_wait_not_covered : ¬ Exec042Covers (exec042_wait (N := Nat) (T := Nat)) := by
  intro h
  have hd : (xrun exec042_C (xinit exec042_m0 0) (exec042_runAsync ++ [.commit 0])).map
      (fun s => !liveB exec042_C s && isExecPhase s.phase &&
        (exec042_waitStep exec042_C s (.finish .terminal)).isNone) = some true := by decide
  cases hs : xrun exec042_C (xinit exec042_m0 0) (exec042_runAsync ++ [.commit 0]) with
  | none => rw [hs] at hd; cases hd
  | some s =>
    rw [hs] at hd
    simp only [Option.map_some, Option.some.injEq, Bool.and_eq_true, Bool.not_eq_true',
      Option.isNone_iff_eq_none] at hd
    obtain ⟨⟨hl, hp⟩, hw⟩ := hd
    obtain ⟨s', hs'⟩ := h exec042_C s (by simp [Live, hl]) hp
    exact absurd (hs'.symm.trans hw) (by simp)

/-! ### Mutant: the check at the next cycle boundary (AC4) -/

/-- An executor that checks terminal places only between cycles: a start ignores them, so a
transition later in the same pass still starts after a synchronous deposit marked one. -/
def exec042_checkAtBoundaryStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .start n sy => startStep refXPol { C with terminals := [] } s n sy
  | l => xstep C s l

/-- The executor of `exec042_checkAtBoundaryStep`. -/
def exec042_checkAtBoundary {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec042_checkAtBoundaryStep C s l = some s'

/-- Mutant reading of EXEC-042: the check at the next cycle boundary. No step of the next cycle
happens while a terminal place is marked, but the pass under way runs to its end. Lines 2 to 6
are as in EXEC-042. -/
def EXEC_042_mutant_checkAtBoundary {N T : Type} [DecidableEq N] (R : XRel N T) : Prop :=
  ∀ C,
    (while (fun s => ¬ Live C s), never (fun s s' =>
      ∃ l, l.outside = false ∧ l ≠ .finish .terminal ∧ (∀ a, l = .snapshot a → s' ≠ s) ∧
        (∀ n sy, l ≠ .start n sy) ∧ R C s l s')) ∧
    (∀ i, on (fun s s' => (R C s (.commit i) s' ∨ R C s (.tdeposit i) s') ∧ ¬ Live C s'),
      shall (fun s s' => ∃ f ∈ s.fl, f.id = i ∧ ∃ e,
        (f.out = some (.ok e) ∨ f.out = some (.timedOut e)) ∧ s'.M = qAppend s.M e)) ∧
    (∀ i, on (fun s s' => R C s (.publish i) s' ∧ ¬ Live C s'),
      shall (fun s s' => ∃ b, s.pq.head? = some (i, b) ∧ s'.M = qAppend s.M b)) ∧
    (∀ k, on (fun s s' => R C s (.inject k) s' ∧
        ∃ p x, s.eq.head? = some (k, p, x) ∧ p ∈ C.terminals),
      shall (fun _ s' => ¬ Live C s')) ∧
    (∀ l, on (fun s s' => R C s l s' ∧ ¬ Live C s'),
      shall (fun s s' => ∀ f ∈ s.fl,
        (∀ i, l = .commit i ∨ l = .fail i ∨ l = .tdeposit i → f.id ≠ i) →
          ∃ g ∈ s'.fl, g.id = f.id)) ∧
    (on (fun s s' => R C s (.finish .terminal) s'), shall (fun s s' =>
      ¬ Live C s ∧ s'.M = s.M ∧ s'.fl = s.fl ∧ s'.eq = []))

/-- The boundary-checking executor kills the mutant: it meets the boundary reading (its other
steps are the reference's, and its start keeps the firings in flight and adds one), but after
`a`'s synchronous deposit marks `9` inside the pass it starts `b`, next in the order (line 1,
AC4). -/
@[evidence mutant EXEC_042]
theorem EXEC_042_mutant_checkAtBoundary_killed :
    EXEC_042_mutant_checkAtBoundary (exec042_checkAtBoundary (N := Nat) (T := Nat)) ∧
      ¬ EXEC_042 (exec042_checkAtBoundary (N := Nat) (T := Nat)) := by
  refine ⟨fun C => ⟨fun s s' ⟨l, ho, hl, hsn, hns, h⟩ hn => ?_,
    fun i s s' h => (EXEC_042_reference C).2.1 i s s' h,
    fun i s s' h => (EXEC_042_reference C).2.2.1 i s s' h,
    fun k s s' h => (EXEC_042_reference C).2.2.2.1 k s s' h,
    fun l s s' ⟨h, hL⟩ => ?_,
    fun s s' h => (EXEC_042_reference C).2.2.2.2.2 s s' h⟩, fun h => ?_⟩
  · cases l with
    | start n sy => exact hns n sy rfl
    | _ => exact (EXEC_042_reference C).1 s s' ⟨_, ho, hl, hsn, h⟩ hn
  · cases l with
    | start n sy =>
      intro f hf _
      obtain ⟨_, _, _, _, _, _, _, _, _, rfl⟩ := startStep_some h
      exact ⟨f, List.mem_append_left _ hf, rfl⟩
    | _ => exact (EXEC_042_reference C).2.2.2.2.1 _ s s' ⟨h, hL⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec042_checkAtBoundaryStep (C := exec042_C)
      (o := exec042_at (exec042_runSync ++ [.commit 0])) (l := .start "b" false)
      (p := fun s _ => !liveB exec042_C s) (by decide)
    exact (h exec042_C).1 s s' ⟨.start "b" false, rfl, by simp, ⟨fun _ ha => (nomatch ha), hs⟩⟩
      (by simpa [Live] using hp)

/-- ✗ Checking terminal places only at the next cycle boundary violates EXEC-042 (line 1, AC4). -/
@[evidence forbids EXEC_042]
theorem EXEC_042_forbids_checkAtBoundary :
    ¬ EXEC_042 (exec042_checkAtBoundary (N := Nat) (T := Nat)) :=
  EXEC_042_mutant_checkAtBoundary_killed.2

/-! ### Violation: the stop as a close (AC2, clash env-b#4) -/

/-- An executor that treats a terminal stop as a close ([ENV-013]): it keeps settling the
completions, queued behind the deposit or later, and ends the run only when nothing is in flight. -/
def exec042_closeLikeStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .commit i => commitStep refXPol { C with terminals := [] } s i
  | .fail i => failStep refXPol { C with terminals := [] } s i
  | .tdeposit i => tdepositStep { C with terminals := [] } s i
  | .finish .terminal => if s.fl.isEmpty then xstep C s (.finish .terminal) else none
  | l => xstep C s l

/-- The executor of `exec042_closeLikeStep`. -/
def exec042_closeLike {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec042_closeLikeStep C s l = some s'

/-- ✗ A stop that admits completions behind the terminal deposit violates EXEC-042 (line 1,
AC2): `a` and `b` both return, `a`'s completion marks `9`, and `b`'s completion is still admitted.
-/
@[evidence forbids EXEC_042]
theorem EXEC_042_forbids_closeLike : ¬ EXEC_042 (exec042_closeLike (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec042_closeLikeStep (C := exec042_C)
    (o := exec042_at (exec042_runAsync ++ [.write 1 2 4, .ret 1 true, .commit 0]))
    (l := .commit 1) (p := fun s _ => !liveB exec042_C s) (by decide)
  exact (h exec042_C).1 s s' ⟨.commit 1, rfl, by simp, ⟨fun _ ha => (nomatch ha), hs⟩⟩
    (by simpa [Live] using hp)

/-! ### Violation: a partial deposit at the terminal place -/

/-- An emission up to and including its first token in a terminal place. -/
def exec042_cut {N T : Type} [DecidableEq N] (C : Cfg N T) : List (N × T) → List (N × T)
  | [] => []
  | (p, x) :: rest => if p ∈ C.terminals then [(p, x)] else (p, x) :: exec042_cut C rest

/-- An executor that stops depositing a returned emission at its first token in a terminal place;
otherwise the reference. -/
def exec042_partialStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .commit i => (xstep C s (.commit i)).map fun s₁ =>
      match s.fl.find? (·.id == i) with
      | some f =>
        match f.out with
        | some (.ok e) => { s₁ with M := qAppend s.M (exec042_cut C e) }
        | _ => s₁
      | none => s₁
  | l => xstep C s l

/-- The executor of `exec042_partialStep`. -/
def exec042_partial {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec042_partialStep C s l = some s'

/-- ✗ Cutting the deposit short at the terminal place violates EXEC-042 (line 2): `a`'s
synchronous emission `[(9, 5), (3, 6)]` deposits `5` in `9` and stops, so `3` stays empty. -/
@[evidence forbids EXEC_042]
theorem EXEC_042_forbids_partialDeposit :
    ¬ EXEC_042 (exec042_partial (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec042_partialStep (C := exec042_C)
    (o := exec042_at exec042_runSync) (l := .commit 0)
    (p := fun s s' => !liveB exec042_C s' && s.fl.all fun f => f.id != 0 ||
      match f.out with
      | some (.ok e) | some (.timedOut e) => qAppend s.M e 3 != s'.M 3
      | _ => true) (by decide)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  obtain ⟨f, hf, hid, e, he, hM⟩ :=
    (h exec042_C).2.1 0 s s' ⟨.inl hs, by simp [Live, hp.1]⟩
  have hg := List.all_eq_true.mp hp.2 f hf
  simp only [hid, bne_self_eq_false, Bool.false_or] at hg
  rcases he with he | he <;> rw [he] at hg <;> simp [hM] at hg

/-! ### Violation: a partial publication at the terminal place (line 3) -/

/-- An executor that stops depositing a published batch at its first token in a terminal place;
otherwise the reference. -/
def exec042_partialPubStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .publish i => (xstep C s (.publish i)).map fun s₁ =>
      match s.pq with
      | (_, b) :: _ => { s₁ with M := qAppend s.M (exec042_cut C b) }
      | [] => s₁
  | l => xstep C s l

/-- ✗ Cutting a published batch short at the terminal place violates EXEC-042 (line 3): `a`'s
flushed batch `[(9, 5), (3, 6)]` deposits `5` in `9` and stops, so `3` stays empty. -/
@[evidence forbids EXEC_042]
theorem EXEC_042_forbids_partialPublish :
    ¬ EXEC_042 (fun C s l s' => exec042_partialPubStep (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec042_partialPubStep (C := exec042_C)
    (o := exec042_at exec042_runPub) (l := .publish 0)
    (p := fun s s' => !liveB exec042_C s' &&
      match s.pq.head? with
      | some (_, b) => qAppend s.M b 3 != s'.M 3
      | none => true) (by decide)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  obtain ⟨b, hb, hM⟩ := (h exec042_C).2.2.1 0 s s' ⟨hs, by simp [Live, hp.1]⟩
  have hg := hp.2
  rw [hb] at hg
  simp [hM] at hg

/-! ### Violation: an injection into a terminal place dropped (line 4, AC3) -/

/-- An executor whose event check reads the event's own place instead of the latch: an event
queued for a terminal place is dropped unapplied by its `inject` step (Rust
`if self.compiled.is_terminal(pid) { break; }`, Java `if (isTerminal[pid]) continue;`), so a
terminal environment place is never marked from outside; otherwise the reference. -/
def exec042_dropTerminalInjectStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .inject k =>
    match s.eq with
    | (j, p, _) :: rest =>
      if p ∈ C.terminals then
        if j == k && liveB C s && !s.mode.closing && (s.phase = .events || s.phase = .await) then
          some { s with eq := rest, phase := if s.phase = .await then .completions else s.phase,
                        parked := false }
        else none
      else xstep C s (.inject k)
    | [] => none
  | l => xstep C s l

/-- ✗ Dropping an event for a terminal place instead of injecting it violates EXEC-042 (line 4,
AC3): the first event for the terminal environment place `9` leaves `9` empty and the state
live. -/
@[evidence forbids EXEC_042]
theorem EXEC_042_forbids_dropTerminalInject :
    ¬ EXEC_042 (fun C s l s' =>
      exec042_dropTerminalInjectStep (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec042_dropTerminalInjectStep (C := exec042_C)
    (o := exec042_at exec042_runInject) (l := .inject 0)
    (p := fun s s' => s.eq.head? == some (0, 9, 5) && liveB exec042_C s') (by decide)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact (h exec042_C).2.2.2.1 0 s s' ⟨hs, 9, 5, hp.1, by decide⟩ hp.2

/-! ### Violation: the firings in flight cancelled at the deposit (line 5, AC2) -/

/-- The deposit labels at which an implementation latches the stop. -/
def exec042_isDeposit {N T : Type} : XLbl N T → Bool
  | .commit _ | .tdeposit _ | .publish _ | .inject _ => true
  | _ => false

/-- An executor that cancels the work in flight where it latches the stop: a deposit step that
marks a terminal place also drops every firing in flight (Java
`inFlight.values().forEach(f -> f.cancel(true)); inFlight.clear();` at the latch, Rust
`in_flight_count = 0` with the join set aborted); its `finish terminal` is the reference's, so it
keeps the list it finds, which is then empty. -/
def exec042_cancelStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) (l : XLbl N T) :
    Option (XSt N T) :=
  (xstep C s l).map fun s₁ =>
    if exec042_isDeposit l && !liveB C s₁ then { s₁ with fl := [] } else s₁

/-- ✗ Cancelling the firings in flight at the deposit that marks a terminal place violates
EXEC-042 (line 5, AC2): `a`'s completion marks `9` while `b` is in flight, and `b` leaves flight
although that step does not settle it. -/
@[evidence forbids EXEC_042]
theorem EXEC_042_forbids_cancelInFlight :
    ¬ EXEC_042 (fun C s l s' => exec042_cancelStep (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec042_cancelStep (C := exec042_C)
    (o := exec042_at exec042_runAsync) (l := .commit 0)
    (p := fun s s' => !liveB exec042_C s' && s'.fl.isEmpty && s.fl.any (·.id != 0)) (by decide)
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff, List.any_eq_true,
    bne_iff_ne, ne_eq] at hp
  obtain ⟨⟨hl, he⟩, f, hf, hid⟩ := hp
  have hk := (h exec042_C).2.2.2.2.1 (.commit 0) s s' ⟨hs, by simp [Live, hl]⟩ f hf
    (fun i hi => by
      rcases hi with hi | hi | hi <;> cases hi
      exact hid)
  simp [he] at hk

/-- An executor whose bookkeeping deregisters a late action: an action returning while a terminal
place is marked takes its own firing out of the list of firings in flight (a completion callback
such as `whenComplete(() -> inFlight.remove(t))`); its late result is still never deposited.
Otherwise the reference. -/
def exec042_retDropStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .ret i ok => (xstep C s (.ret i ok)).map fun s₁ =>
      if liveB C s then s₁ else { s₁ with fl := s₁.fl.filter (·.id != i) }
  | l => xstep C s l

/-- ✗ An executor that drops an abandoned firing when its action returns after the stop violates
EXEC-042 (line 5): on the AC2 run, `a`'s completion marks `9` while `b` is in flight; `b`'s action
then returns, and `b` leaves the list of firings in flight, so `finish terminal` keeps an empty
list and a snapshot afterwards would report no work in flight although `b` was abandoned. -/
@[evidence forbids EXEC_042]
theorem EXEC_042_forbids_retDropAfterStop :
    ¬ EXEC_042 (fun C s l s' => exec042_retDropStep (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec042_retDropStep (C := exec042_C)
    (o := exec042_at (exec042_runAsync ++ [.commit 0])) (l := .ret 1 true)
    (p := fun s s' => !liveB exec042_C s' && s.fl.any (·.id == 1) && s'.fl.all (·.id != 1))
    (by decide)
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true, List.all_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq] at hp
  obtain ⟨⟨hl, f, hf, hid⟩, hall⟩ := hp
  obtain ⟨g, hg, hgid⟩ := (h exec042_C).2.2.2.2.1 (.ret 1 true) s s' ⟨hs, by simp [Live, hl]⟩ f hf
    (fun i hi => by rcases hi with hi | hi | hi <;> cases hi)
  exact hall g hg (hgid.trans hid)

/-! ### Violations of the finish line -/

/-- An executor whose `finish terminal` step is changed by `g` (applied to the source and the
reference target); otherwise the reference. -/
def exec042_finishWith {N T : Type} [DecidableEq N] (g : XSt N T → XSt N T → XSt N T)
    (C : Cfg N T) (s : XSt N T) : XLbl N T → Option (XSt N T)
  | .finish .terminal => (xstep C s (.finish .terminal)).map (g s)
  | l => xstep C s l

/-- The consumed tokens of every firing in flight, put back at the heads of their places. -/
def exec042_rollback {N T : Type} (s s₁ : XSt N T) : XSt N T :=
  { s₁ with M := fun p => s.fl.flatMap (·.deliv.inputs p) ++ s₁.M p }

/-- ✗ A stop that restores the tokens the abandoned firings consumed violates EXEC-042 (line 6):
on the AC2 run, `b` is in flight at the stop and its consumed `8` goes back to `1`. -/
@[evidence forbids EXEC_042]
theorem EXEC_042_forbids_rollbackOnStop :
    ¬ EXEC_042 (fun C s l s' => exec042_finishWith (N := Nat) (T := Nat) exec042_rollback C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check (exec042_finishWith exec042_rollback)
    (C := exec042_C) (o := exec042_at (exec042_runAsync ++ [.commit 0])) (l := .finish .terminal)
    (p := fun s s' => s'.M 1 != s.M 1) (by decide)
  have := ((h exec042_C).2.2.2.2.2 s s' hs).2.1
  simp [this] at hp

/-- ✗ A stop that drops the firings in flight violates EXEC-042 (line 6): on the AC2 run, `b` is
in flight at the stop and is no longer reported. -/
@[evidence forbids EXEC_042]
theorem EXEC_042_forbids_dropInFlight :
    ¬ EXEC_042 (fun C s l s' =>
      exec042_finishWith (N := Nat) (T := Nat) (fun _ s₁ => { s₁ with fl := [] }) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check (exec042_finishWith fun _ s₁ => { s₁ with fl := [] })
    (C := exec042_C) (o := exec042_at (exec042_runAsync ++ [.commit 0])) (l := .finish .terminal)
    (p := fun s s' => s'.fl.length != s.fl.length) (by decide)
  have := ((h exec042_C).2.2.2.2.2 s s' hs).2.2.1
  simp [this] at hp

/-- ✗ A stop that keeps the queued external events (for a later injection) violates EXEC-042
(line 6): on the AC3 run, the second event is still queued after the stop. -/
@[evidence forbids EXEC_042]
theorem EXEC_042_forbids_keepQueued :
    ¬ EXEC_042 (fun C s l s' =>
      exec042_finishWith (N := Nat) (T := Nat) (fun s s₁ => { s₁ with eq := s.eq }) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check (exec042_finishWith fun s s₁ => { s₁ with eq := s.eq })
    (C := exec042_C) (o := exec042_at (exec042_runInject ++ [.inject 0])) (l := .finish .terminal)
    (p := fun _ s' => !s'.eq.isEmpty) (by decide)
  have := ((h exec042_C).2.2.2.2.2 s s' hs).2.2.2
  simp [this] at hp

/-- An executor that also reports `terminal` at a quiescent rest, where no terminal place is
marked; otherwise the reference. -/
def exec042_terminalAtRestStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .finish .terminal =>
      if s.phase = .test && finishQ C s then some { s with phase := .done .terminal, eq := [], pq := [] }
      else xstep C s (.finish .terminal)
  | l => xstep C s l

/-- ✗ Reporting `terminal` at a rest with no terminal place marked violates EXEC-042 (line 6):
from the empty marking a drained executor reaches a rest and ends `terminal`. -/
@[evidence forbids EXEC_042]
theorem EXEC_042_forbids_terminalAtRest :
    ¬ EXEC_042 (fun C s l s' => exec042_terminalAtRestStep (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec042_terminalAtRestStep (C := exec042_C)
    (o := xrun exec042_C (xinit (fun _ => []) 0)
      [.drain, .endCompletions, .endPublications, .endEvents, .update, .deadline []])
    (l := .finish .terminal) (p := fun s _ => liveB exec042_C s) (by decide)
  exact ((h exec042_C).2.2.2.2.2 s s' hs).1 (by simpa [Live] using hp)

/-! ## EXEC-042: the build check (AC5) -/

requirement EXEC_042_build
  id "EXEC-042"
  title "Terminal Places"
  kind F
  scope "the net builder of every implementation, used without composition and without fusion sets"
  source verbatim "spec/04-execution-model.md"
  quote "A terminal place MUST NOT be an input or a read-arc place of any transition: such a transition could never fire, so the net is rejected when it is built."
        "*If* a declared terminal place is an input place or a read-arc place of a transition of the net, *then* building the net *shall* fail."
        "*When* a net is built without composition and without fusion sets and no declared terminal place is an input place or a read-arc place of one of its transitions, building it *shall* succeed, and the built net's terminal places *shall* be exactly the declared ones."
  reading "For every transition builder B, every net builder NB over its instances, and every input inp (declared places, added transitions, declared terminal places):"
          "if a declared terminal place of inp is an input place or a read place of one of its added transitions, NB rejects inp;"
          "if none is, NB returns a net;"
          "a net NB returns for inp has exactly the declared terminal places of inp as its terminal places."
  assumes "A net builder (NetBuilder B, Reference/Build.lean) is the build call of one implementation's net builder, read as a function from what the host added (NetIn B) to a built net (BuiltNet) or a rejection with a message (a panic or an exception). The added transitions are instances of the transition builder B (a net holds only builder outputs, the W2 tracer decision). The clash (NetIn.TerminalClash) is a declared terminal place that an added transition's definition names on an input arc or a read arc (TransDef.ConsumesOrReads). The witness is the reference net builder refNetBuild."
          "Line 1 is the first quoted sentence and the first shall sentence (Rust validate_terminals, Java checkTerminals, TypeScript requireWellFormedTerminals all reject both an input arc and a read arc). A builder without the check (EXEC_042_build_forbids_noCheck) or one that checks input arcs only (EXEC_042_build_forbids_inputsOnly) violates it. Only the rejection is stated, not its message: the messages differ between the runtimes and the spec fixes none."
          "Lines 2 and 3 are the second shall sentence and the body's 'A net MAY declare terminal places': a terminal place on an inhibitor arc, on a reset arc or on an output is allowed, so a builder that rejects every declared terminal place (EXEC_042_build_mutant_rejectAll_killed) violates line 2, and one that drops the declarations, so that the run has no terminal place, violates line 3 (EXEC_042_build_forbids_dropTerminals). Line 3 reads the terminal places as a set; the reference keeps them once each in declaration order (refNetBuild_terminals)."
          "Scope: as for CORE-040, a builder used without composition (MOD-020, MOD-025) and without fusion sets (MOD-060, MOD-061), whose own rejections (fusion overlap, a reference to a bound port place) would make line 2 fail; the second shall sentence names that scope ('a net built without composition and without fusion sets'), so it is no stronger than line 2; what a composed net does with terminal places is the composition model's, and AC6 (compose and instantiate reject a subnet body that declares a terminal place) is MOD-010 line 4 and MOD-025 line 7. With no terminal place declared, line 2 is CORE-040's line 4."
          "AC5 (a transition that consumes or reads a terminal place is rejected when the net is built) is line 1; EXEC_042_build_nonvacuous rejects a net whose transition reads the terminal place and builds one whose transition has it as inhibitor and output."
  signoff "2026-11-13 ca476acb02bf289b ai"
  statement : ∀ {N A : Type} [DecidableEq N] (B : TBuilder N A), NetBuilder B → Prop :=
    fun B NB => ∀ inp : NetIn B,
      (inp.TerminalClash → ∃ e, NB inp = .error e) ∧
      (¬ inp.TerminalClash → ∃ b, NB inp = .ok b) ∧
      (∀ b, NB inp = .ok b → ∀ p, p ∈ b.terminals ↔ p ∈ inp.terminals)

/- The pinned readable form of the build block. -/
/--
info: def Libpetri.Spec.EXEC_042_build : {N A : Type} → [DecidableEq N] → (B : TBuilder N A) → NetBuilder B → Prop :=
fun {N A} [DecidableEq N] B NB =>
  ∀ (inp : NetIn B),
    (inp.TerminalClash → ∃ e, NB inp = Except.error e) ∧
      (¬inp.TerminalClash → ∃ b, NB inp = Except.ok b) ∧
        ∀ (b : BuiltNet N A), NB inp = Except.ok b → ∀ (p : N), p ∈ b.terminals ↔ p ∈ inp.terminals
-/
#guard_msgs in #print EXEC_042_build

/-- ✓ The reference net builder satisfies the build block: it rejects exactly a clash
(`refNetBuild_error_iff`, `refNetBuild_ok_iff`) and keeps the declared terminal places once each
(`refNetBuild_terminals`). -/
@[evidence holds EXEC_042_build]
theorem EXEC_042_build_reference {N A : Type} [DecidableEq N] (B : TBuilder N A) :
    EXEC_042_build B (refNetBuild (B := B)) := by
  intro inp
  refine ⟨refNetBuild_error_iff.2, refNetBuild_ok_iff.2, fun b hb p => ?_⟩
  rw [refNetBuild_terminals hb]
  exact List.mem_eraseDups

/-! ### Examples -/

/-- A transition that consumes from `0` and reads the terminal place `9`, output `Place 2`. -/
def exec042_inRead : TransIn Nat Unit :=
  { core := { name := "r", inputs := [⟨0, .one⟩], inhibitors := [], reads := [9], resets := [] },
    out := some (.place 2) }

/-- A transition that consumes from `0`, is inhibited by the terminal place `9` and outputs to it.
-/
def exec042_inInh : TransIn Nat Unit :=
  { core := { name := "a", inputs := [⟨0, .one⟩], inhibitors := [9], reads := [], resets := [] },
    out := some (.place 9) }

/-- The reference transition builder at the example's types. -/
abbrev exec042_B : TBuilder Nat Unit := refTransBuild (N := Nat) (A := Unit)

/-- The reference transition builder's instance of `exec042_inRead`. -/
def exec042_xRead : exec042_B.I :=
  ⟨(0, exec042_inRead.resolve), 0, exec042_inRead,
    refTransBuildRaw_ok.2 ⟨(refBuild_eq_none_iff _).1 (by decide),
      ⟨fun _ h => by simp [exec042_inRead] at h, rfl⟩⟩⟩

/-- The reference transition builder's instance of `exec042_inInh`. -/
def exec042_xInh : exec042_B.I :=
  ⟨(0, exec042_inInh.resolve), 0, exec042_inInh,
    refTransBuildRaw_ok.2 ⟨(refBuild_eq_none_iff _).1 (by decide),
      ⟨fun _ h => by simp [exec042_inInh] at h, rfl⟩⟩⟩

/-- A net with terminal place `9` and the transition that reads it. -/
def exec042_netRead : NetIn exec042_B := ⟨[0, 2, 9], [exec042_xRead], [9]⟩

/-- A net with terminal place `9` and the transition inhibited by it and writing it. -/
def exec042_netInh : NetIn exec042_B := ⟨[0, 9], [exec042_xInh], [9]⟩

/-- The reading transition clashes with the terminal place. -/
theorem exec042_netRead_clash : exec042_netRead.TerminalClash :=
  ⟨9, by decide, exec042_xRead, by simp [exec042_netRead],
    .inr (by show 9 ∈ exec042_inRead.resolve.core.reads; decide)⟩

/-- The inhibited transition does not clash with the terminal place. -/
theorem exec042_netInh_noClash : ¬ exec042_netInh.TerminalClash :=
  refNetBuild_ok_iff.1 ⟨_, rfl⟩

/-- ✓ The build block is exercised by the reference: the net whose transition reads the terminal
place is rejected (line 1, AC5), the net whose transition is inhibited by it and writes it builds
(line 2), with terminal place `9` (line 3). -/
@[evidence nonvacuous EXEC_042_build]
theorem EXEC_042_build_nonvacuous :
    (∃ e, refNetBuild exec042_netRead = .error e) ∧
    ∃ b, refNetBuild exec042_netInh = .ok b ∧ b.terminals = [9] :=
  ⟨refNetBuild_error_iff.2 exec042_netRead_clash, _, rfl, rfl⟩

/-! ### Wrong builders -/

section Wrong

variable {N A : Type} [DecidableEq N]

/-- A net builder without the terminal check: it accepts every input. -/
def exec042_noCheckNB (B : TBuilder N A) : NetBuilder B := fun inp => .ok inp.collect

/-- A net builder that rejects a terminal place on an input arc only, not on a read arc. -/
def exec042_inputsOnlyNB (B : TBuilder N A) : NetBuilder B := fun inp =>
  if inp.terminals.any (fun p => (inp.trans.map B.defOf).any fun d =>
      decide (p ∈ d.core.inputs.map (·.place)))
  then .error "EXEC-042" else .ok inp.collect

/-- A net builder that rejects every declared terminal place. -/
def exec042_rejectAllNB (B : TBuilder N A) : NetBuilder B := fun inp =>
  if inp.terminals.isEmpty then refNetBuild inp else .error "EXEC-042"

/-- A net builder that drops the declared terminal places from the net it returns. -/
def exec042_dropTerminalsNB (B : TBuilder N A) : NetBuilder B := fun inp =>
  (refNetBuild inp).map fun b => { b with terminals := [] }

/-- Mutant reading of the build block without line 2: a clash is rejected and the terminal places
are kept, with no line on when the builder accepts. -/
def EXEC_042_build_mutant_rejectAll (B : TBuilder N A) (NB : NetBuilder B) : Prop :=
  ∀ inp : NetIn B,
    (inp.TerminalClash → ∃ e, NB inp = .error e) ∧
    (∀ b, NB inp = .ok b → ∀ p, p ∈ b.terminals ↔ p ∈ inp.terminals)

end Wrong

/-- ✗ A builder without the terminal check violates the build block (line 1, AC5): it builds the
net whose transition reads the terminal place. -/
@[evidence forbids EXEC_042_build]
theorem EXEC_042_build_forbids_noCheck : ¬ EXEC_042_build exec042_B (exec042_noCheckNB exec042_B) := by
  intro h
  obtain ⟨e, he⟩ := (h exec042_netRead).1 exec042_netRead_clash
  cases he

/-- ✗ A builder that checks input arcs only violates the build block (line 1, AC5): it builds the
net whose transition reads the terminal place. -/
@[evidence forbids EXEC_042_build]
theorem EXEC_042_build_forbids_inputsOnly :
    ¬ EXEC_042_build exec042_B (exec042_inputsOnlyNB exec042_B) := by
  intro h
  obtain ⟨e, he⟩ := (h exec042_netRead).1 exec042_netRead_clash
  have : exec042_inputsOnlyNB exec042_B exec042_netRead = .ok exec042_netRead.collect := rfl
  rw [this] at he
  cases he

/-- The builder that rejects every terminal place kills the mutant without line 2: it rejects
every clash and returns only nets without terminal places, which it keeps, but it rejects the net
whose terminal place is only an inhibitor place and an output (line 2). -/
@[evidence mutant EXEC_042_build]
theorem EXEC_042_build_mutant_rejectAll_killed :
    EXEC_042_build_mutant_rejectAll exec042_B (exec042_rejectAllNB exec042_B) ∧
      ¬ EXEC_042_build exec042_B (exec042_rejectAllNB exec042_B) := by
  refine ⟨fun inp => ⟨fun hc => ?_, fun b hb => ?_⟩, fun h => ?_⟩
  · unfold exec042_rejectAllNB
    split
    · exact refNetBuild_error_iff.2 hc
    · exact ⟨_, rfl⟩
  · unfold exec042_rejectAllNB at hb
    split at hb
    · exact (EXEC_042_build_reference exec042_B inp).2.2 b hb
    · cases hb
  · obtain ⟨b, hb⟩ := (h exec042_netInh).2.1 exec042_netInh_noClash
    cases hb

/-- ✗ A builder that drops the declared terminal places violates the build block (line 3): the
net with terminal place `9` builds with no terminal place. -/
@[evidence forbids EXEC_042_build]
theorem EXEC_042_build_forbids_dropTerminals :
    ¬ EXEC_042_build exec042_B (exec042_dropTerminalsNB exec042_B) := by
  intro h
  have := ((h exec042_netInh).2.2 _ rfl 9).2 (by decide)
  simp at this

end Libpetri.Spec
