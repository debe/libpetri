import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Exec
import Libpetri.Spec.Text.EXEC_022

set_option linter.missingDocs true

/-!
# EXEC-022: Action timeout handling (`spec/04-execution-model.md`)

A requirement block over the executor model (`RefExec`, `Reference/Exec.lean`). When a
transition's output spec has a `Timeout` node, the action of a firing races its budget. In the
model the budget's end is the outside step `expire i e` (the firing `i` ends with its timeout
outcome `e`), the action's end is the outside step `ret i ok`, and the executor deposits the
timeout outcome in a later settle step, `tdeposit i`.

Ruling D18 (b): the budget is host time ([TIME-015]: action timeouts are not virtualized), so
`expire` is a free outside step of an asynchronous firing whose output spec has a `Timeout` node,
either side may win a tie, and "never before the budget has elapsed" is a test-only point (kind Q)
for its timing; its step form is line 5 (only the expiry records a timeout outcome). Ruling
D24 (a): the timeout outcome is not validated against the output spec, and the join-relay check of
[NU-054] runs on it; both are [EXEC-021]'s lines 3 and 5, not restated here.

The block has eight lines:

1. an expiry step happens only for a firing in flight whose action has not reported, that is not
   synchronous and whose output spec has a `Timeout` node, under every configuration; under a
   configuration whose timeout outcomes are token-level ones, its timeout outcome is the
   token-level outcome of that node's child (`exec022_QOutcome`: a minted token for each `Place`,
   every consumed token for each `ForwardInput`, in consumption order, as the same token);
2. the expiry step deposits nothing, queues no publication, and records exactly the announced
   outcome (an error on a firing a relay check already rejected, [NU-054]);
3. a `tdeposit` step deposits exactly the timeout outcome the firing recorded, at the tails;
4. a flush of a firing that ended with its timeout outcome deposits and queues nothing;
5. the firing record frame: no step changes an outcome a firing recorded, and only the expiry of
   `i` records a timeout outcome of `i`;
6. after the expiry of `i`, no step commits a completion of `i` (a trace line);
7. after the action of `i` returns while `i` is open, no step ends `i` with its timeout outcome or
   deposits one (a trace line);
8. after the timeout deposit of `i`, no step settles `i` again (a trace line).

Lines 6 to 8 read runs from a state in which every firing in flight has an identity the supply
has already handed out (`IdsIssued`), as EXEC-031's trace lines do.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## Block-local terms -/

section Terms

variable {N T : Type}

/-- **The token-level emissions of a `Timeout` child** for a firing that delivered `δ`, in the
order of the tree ([IO-013], [IO-014]; Rust `collect_timeout_outputs`): a `Place` node gives one
minted token (any value: the executor mints it), a `ForwardInput(src, dst)` gives every token the
firing consumed from `src`, in consumption order, each the same token in `dst` (so it keeps its
value and `created_at`), an `And` gives its children's emissions one after the other. `Xor` and
`Timeout` are read as in `Out.timeoutDeposits` (a spec that builds has neither inside the child,
[IO-013]). -/
def exec022_Emits (δ : QDelivered N T) : Out N → List (N × T) → Prop
  | .place p, e => ∃ x, e = [(p, x)]
  | .forward src dst, e => e = (δ.inputs src).map fun x => (dst, x)
  | .and l r, e => ∃ e₁ e₂, e = e₁ ++ e₂ ∧ exec022_Emits δ l e₁ ∧ exec022_Emits δ r e₂
  | .xor l r, e => exec022_Emits δ l e ∨ exec022_Emits δ r e
  | .timeout c, e => exec022_Emits δ c e

/-- **The token-level timeout outcome** of `t` for a firing that delivered `δ`: `t`'s output spec
has a `Timeout` node, and `e` puts in every place the same tokens, in the same order, as an
emission of that node's child. Places are compared one by one ([CORE-036]): the order between
places is not part of the outcome, the order inside a place is (FIFO, [EXEC-020]). The token-level
form of the glossary term Timeout outcome. -/
def exec022_QOutcome [DecidableEq N] (t : Trans N) (δ : QDelivered N T)
    (e : List (N × T)) : Prop :=
  ∃ o c e₀, t.out = some o ∧ o.findTimeout = some c ∧ exec022_Emits δ c e₀ ∧
    ∀ p, qEmittedTo e p = qEmittedTo e₀ p

/-- The configuration's timeout outcomes are token-level timeout outcomes: whatever outcome
`C.timeoutOut` accepts is the one the `Timeout` child gives. The premise of line 1, as EXEC-021
judges under `Cfg.SetValidated`. -/
def exec022_OutcomeSound [DecidableEq N] (C : Cfg N T) : Prop :=
  ∀ t δ e, C.timeoutOut t δ e = true → exec022_QOutcome t δ e

/-- **Firing `i` has recorded the outcome `o`**: the identity `i` was handed out, and every firing
in flight with identity `i` holds `o` (it ended with `o`, by its return or by its expiry). -/
def exec022_Recorded (o : Outcome N T) (i : Nat) (s : XSt N T) : Prop :=
  i < s.nextId ∧ ∀ f ∈ s.fl, f.id = i → f.out = some o

/-- The step is the expiry of firing `i`'s budget. -/
def exec022_isExpire (i : Nat) : XStep N T → Bool
  | (_, .expire j _, _) => j == i
  | _ => false

/-- The step commits the completion of firing `i`: the completion reaches the marking. -/
def exec022_isCommit (i : Nat) : XStep N T → Bool
  | (_, .commit j, _) => j == i
  | _ => false

/-- The step is a return of firing `i`'s action, normal or with an error, while firing `i` is
open (no outcome recorded): the action completes before the firing has ended. -/
def exec022_isOpenReturn (i : Nat) : XStep N T → Bool
  | (s, .ret j _, _) => j == i && s.fl.any fun f => f.id == i && f.out.isNone
  | _ => false

/-- The step ends firing `i` with its timeout outcome (`expire`) or deposits a timeout outcome
of `i` (`tdeposit`). -/
def exec022_isTimeout (i : Nat) : XStep N T → Bool
  | (_, .expire j _, _) => j == i
  | (_, .tdeposit j, _) => j == i
  | _ => false

/-- The step deposits the timeout outcome of firing `i`. -/
def exec022_isTDeposit (i : Nat) : XStep N T → Bool
  | (_, .tdeposit j, _) => j == i
  | _ => false

/-- The step settles firing `i`: it deposits a completion (`commit`), deposits nothing (`fail`),
or deposits a timeout outcome (`tdeposit`). -/
def exec022_isSettle (i : Nat) : XStep N T → Bool
  | (_, .commit j, _) => j == i
  | (_, .fail j, _) => j == i
  | (_, .tdeposit j, _) => j == i
  | _ => false

end Terms

/-! ## EXEC-022: Action Timeout Handling -/

requirement EXEC_022
  id "EXEC-022"
  title "Action Timeout Handling"
  kind T
  scope "all executors"
  source verbatim "spec/04-execution-model.md"
  covers EXEC_022.s1, EXEC_022.s2, EXEC_022.s3, EXEC_022.s4, EXEC_022.s5, EXEC_022.s6, EXEC_022.s7,
        EXEC_022.s8, EXEC_022.s9, EXEC_022.s10, EXEC_022.s11, EXEC_022.s12, EXEC_022.s13,
        EXEC_022.s14, EXEC_022.s15
  reading "For every executor R, every configuration C and every firing identity i:"
          "an expiry step of i with timeout outcome e happens only for a firing i in flight whose action has not reported (no outcome set), that is not synchronous, and whose transition's output spec has a Timeout node (hasTimeoutB), and, if the timeout outcomes C accepts are token-level timeout outcomes (exec022_OutcomeSound), e is the token-level timeout outcome of that node's child for what the firing delivered (exec022_QOutcome);"
          "an expiry step of i with timeout outcome e changes neither the marking nor the queue of publications not yet deposited, and after it every firing i holds the outcome e (an error, if a flushed batch of it failed the join-relay check);"
          "a step that deposits the timeout outcome of i (tdeposit) deposits exactly the outcome e the firing recorded, each token at the tail of its place in order;"
          "a flush step of i from a state in which every firing i holds a timeout outcome changes neither the marking nor the queue of publications;"
          "every step keeps an outcome firing i has recorded (exec022_Recorded), and a step after which a firing i holds a timeout outcome it did not hold before is an expiry step of i;"
          "on every run of R from a state in which every firing in flight has an identity the supply has already handed out, no commit step of i comes after an expiry step of i;"
          "on every such run, no expiry step of i and no tdeposit step of i comes after a return step of i (normal or with an error) taken while firing i was open;"
          "on every such run, no commit, fail or tdeposit step of i comes after a tdeposit step of i."
  assumes "The model is an executor R : XRel N T (glossary GlossaryExec.lean): R C s l s' says that under configuration C the step labelled l leads from executor state s to s'. A firing starts in a firing pass; its action writes (write), publishes (flush) and returns (ret, normally or with an error), or its budget runs out first (expire i e, with the timeout outcome e); a settle step in step 1 then deposits the outcome (commit for a completion, tdeposit for a timeout outcome) or deposits nothing (fail). The witness is the reference executor RefExec (Reference/Exec.lean), checked rule by rule against the Rust executor: the expiry is the select! of the spawned task against tokio::time::sleep, only for an asynchronous firing whose spec has a Timeout node (fire_transition_async, executor_core/executor.rs), and the timeout outcome reaches the marking through handle_completion in Phase 1, like a completion."
          "The first sentence and the two bullets of the markdown are the race the block reads as lines 1, 5, 6 and 7: the expiry is offered only while the action has not reported, the action's return counts only while the firing is open, and whichever reports first fixes how the firing ends (line 5). 'Action completes first: normal output validation' is the completion's commit or fail step, EXEC-021's subject; line 7 says no timeout outcome follows it. 'Timeout fires first: the firing is abandoned' is lines 2, 4, 5 and 6: nothing the action had not published is deposited or published, a late return of the action does not change how the firing ended, and its completion is never committed. Whether the action is stopped is the side-effect paragraph of IO-013, implementation-defined and not encoded. 'The timeout child output receives tokens' is lines 1, 2 and 3. 'ActionTimedOut event emitted' is the event kind the tdeposit label carries (design table R-EXEC-8); the event, its payload and its order are EVT-010's, on the event model of wave W7."
          "Ruling D18 (b), host time. The budget's duration is not in the model: an expiry is a free outside step, offered at any point while the firing's action has not reported. The sentence 'While the budget of a firing has not elapsed, the executor shall not end the firing with its timeout outcome.' is encoded in its step form only: line 5 says that a timeout outcome is recorded by the expiry step and by no other step, so the firing ends with its timeout outcome only at the model's event of its budget running out (EXEC_022_forbids_clockTimeout: a budget timed on the firing clock, a delay step that records the timeout outcome). That the expiry comes only once the duration has elapsed is a test-only point (kind Q), checked by the runtimes' timing tests, because the budget elapses in real time on the host's timer inside a per-action wait (Rust: the tokio::time::sleep arm of the select! in fire_transition_async, executor_core/executor.rs; Java: completeOnTimeout in ExecutorSupport.withActionTimeout; TypeScript: the setTimeout raced against the action in fireTransition, bitmap-net-executor.ts) and not on the firing clock ([TIME-015], spec/03-timing.md, the scope limit 'action timeouts are not virtualized'). A host counter in the state would make it a line; the ruling chose not to add one. The sentence 'The budget is host time ...' is the reason, and states no executor step. The kind is T, the plan's primary kind for this ID: the block is the race between an action and its budget, read without the clock; every line is a step or trace line, and the duration itself is the Q point above."
          "The tie (ruling D18 (b), clash exec#3): 'When the action completes at the instant the budget runs out, either side may win.' is read as: both the return and the expiry are offered from the same state. Rust's biased select! prefers the completion, Java and TypeScript take whichever completes the shared future first. EXEC_022_allows_completionFirst and EXEC_022_allows_timeoutFirst show the reference offering both from one state; the lines then fix what follows either side."
          "Every line is a safety line, so an executor that never offers an expiry step meets the block. When an asynchronous firing whose spec has a Timeout node expires is AC2's test-only point under ruling D18 (b). That the expiry is offered at all, and that a recorded timeout outcome the join-relay check accepts is then deposited, is coverage: Exec022Covers, a clause of the consistency theorem's ExecCoversW5 (ConsistencyExec.lean), which the reference meets (refExec_timeoutCovers); EXEC_022_allows_timeoutFirst shows the reference offering the expiry and the deposit."
          "Line 1's last conjunct alone reads the premise exec022_OutcomeSound C; its guards (firing open, not synchronous, a Timeout node) hold under every configuration. The reference takes the timeout outcome the configuration accepts (C.timeoutOut), as it takes the verdicts of output validation from C, so the line can say that the outcome is the Timeout child's only of a configuration whose check accepts nothing else; under another configuration line 1 constrains the guard of the expiry and not its outcome. Real configurations come from the build. No Cfg.WF field or link lemma shows yet that the configuration a net builds has a sound timeoutOut; that link is still open: the module doc of ConsistencyAll.lean (spec_consistent_all) lists it among the links not yet made. EXEC-021 reads its premise Cfg.SetValidated the same way and discharges it for built validators by cfgValidate_setValidated. Lines 2 to 8 hold under every configuration."
          "The first shall sentence is line 1's not-synchronous and Timeout-node conjuncts. 'Completed before it handed control back' is the sync flag of the firing (Firing.sync): the pass waits for the action's return (Rust's inline run_sync branch of fire_transition_async, executor_core/executor.rs; Java and TypeScript invoke the action inline and race only the future it returns, so an action whose future is already complete never times out, clash exec#2). A Timeout node is line 1's hasTimeoutB conjunct. Neither conjunct reads the premise exec022_OutcomeSound, so the sentence binds under every configuration: EXEC_022_forbids_syncTimeout and EXEC_022_forbids_noTimeoutNode break it under a configuration whose timeout-outcome check accepts every outcome."
          "The third shall sentence is line 1's 'no outcome set' conjunct and line 7. Line 7 triggers on a return of i taken while firing i is open, that is, the action completed before the firing ended: after it no expiry and no timeout deposit of i follows, whatever the steps between do (EXEC_022_forbids_timeoutAfterReturn: an expiry after the return; EXEC_022_forbids_errorAsTimeout: an action error read as the budget's timeout and deposited as the timeout outcome). A late return of an abandoned action, after the expiry, is not a completion that came first, so it does not trigger line 7; that it changes nothing is lines 5 and 6."
          "The fourth shall sentence, 'If a firing has already ended, by the return of its action or by its budget running out, then the executor shall not change how it ended.', is line 5's first half: every step keeps an outcome a firing recorded (exec022_Recorded). EXEC_022_forbids_lateError breaks it: a late error of the abandoned action replaces the timeout outcome, and the firing then fails and its forwarded tokens are lost (TypeScript: a rejection handler on the action's own promise next to the race; Java: exceptionally on actionFuture instead of on its timed copy). The firing record documents the same frame (Firing.out: set once, by its return or by the expiry of its budget)."
          "The fifth shall sentence is line 1's last conjunct together with lines 2, 3 and 5: the expiry announces the token-level outcome e (line 1), records exactly e (line 2), no other step records a timeout outcome and none changes it (line 5), and the deposit is the recorded outcome (line 3). EXEC_022_forbids_mergeAtExpiry breaks line 2: the expiry announces e and records the action's unpublished writes with it (the Java and TypeScript slip of producing the timeout branch before context.detachForTimeout()). A minted token's value is free (the executor mints it; Rust mints the unit token stamped by the firing clock, TIME-015 AC13, below this model). A forwarded token is the consumed token itself (tokens are identities in the queue model), so 'keeping its value and created_at' is token identity, and 'in consumption order' is the order of what the start delivered (QDelivered.inputs, the FIFO prefix of EXEC-010). Outcomes are compared place by place, so an executor emitting the children of an And in another order deposits the same marking and meets the line. Forwarding only the first consumed token breaks it (EXEC_022_forbids_forwardFirst)."
          "The sixth shall sentence is lines 3 and 8: the tdeposit step appends exactly the recorded outcome at the tails (EXEC_022_forbids_merge: the action's unpublished output merged into the deposit), and after it no commit, fail or tdeposit of the firing follows (EXEC_022_forbids_doubleDeposit: a deposit that leaves the firing in flight and its queue entry in place deposits the outcome twice). With lines 1, 2 and 5, a deposited timeout outcome is the token-level outcome the expiry announced. That a recorded timeout outcome is deposited at all, and not left queued, is coverage: the second clause of Exec022Covers in the consistency theorem's ExecCoversW5."
          "The seventh shall sentence is lines 2, 4 and 6. Line 2: the expiry step deposits nothing and queues no publication, so the tokens the action wrote and had not published are dropped, not published (EXEC_022_forbids_flushAtTimeout). Line 4: a later flush of the abandoned action deposits and queues nothing (EXEC_022_forbids_lateFlush: a flush callback that does not check whether its firing was abandoned). Rust and Python meet line 4 although their flush closure can outlive the cancelled action (Context::flush_fn in libpetri-core hands out a clone that a spawned task or a Python context can keep): the closure shares a gate with the firing's task (FlushGate, executor_core/executor.rs), the task marks the firing ended when the action returns or its budget runs out, before it sends the completion, and the closure checks that mark and sends under one lock, so a flush after the expiry is refused with an error and deposits nothing. A flush callback that skips that check is EXEC_022_forbids_lateFlush, the behaviour RD-15 in spec/runtime-defects.md recorded for Rust and Python. Java and TypeScript have no mid-action publication. Line 6: after the expiry no commit step deposits the completion of the abandoned action (EXEC_022_forbids_lateCompletion: a late return accepted and committed). The lines constrain the executor and not the abandoned action: a late return or flush may still be a step, provided it changes neither the marking, the queue, nor how the firing ended. A publish step of i after the expiry is not banned: it deposits a batch the action flushed before the budget ran out (ruling D17), which the plain sentence 'Output the action published before the budget ran out stays in the marking ([EXEC-020], [IO-015]).' states; that it stays is the marking frame, EXEC-020's and EXEC-031's subject."
          "The sentence 'The timeout outcome is not validated against the output spec, and the join-relay check of [NU-054] still runs on it ([EXEC-021]).' is ruling D24 (a). It is EXEC-021's lines 3 and 5 (a timed-out firing fails only when the relay check rejects its outcome; a tdeposit happens only when the relay check accepts it), not restated here. An executor that validates the timeout outcome against the whole spec fails And(A, Timeout(d, B)) on every timeout, the behaviour RD-01 in spec/runtime-defects.md recorded for Java and TypeScript; that breaks EXEC-021 and no line of this block (its timeout firing ends with a fail step, which this block does not constrain). Every runtime deposits the timeout branch on the places the rewritten output spec names, as given (MOD-031): Rust directly, Java and TypeScript because outputToHarvest and forwardToHarvest of their TransitionContext take actual places and Java reads a ForwardInput's source through the raw input (ExecutorSupport.java produceTimeoutOutputRecursive, executor-support.ts produceTimeoutOutput). An executor that resolves the branch's places through the correspondence a second time puts, in a composed net whose correspondence collides, a token on another place than the Timeout child names, or forwards one taken from another input, so the outcome the expiry records, and line 3 then deposits, is not the child's token-level outcome and line 1 fails: the behaviour RD-31 in spec/runtime-defects.md recorded for Java and TypeScript."
          "The relay check on flushed batches belongs to NU-054: a batch the check rejects is dropped, marks the firing relayBad, and the firing then fails as it does for a violation found at completion. Line 2 reads that rule at the expiry, so the expiry of a relayBad firing records an error and not the timeout outcome (Rust takes the FlushGate's relay_error after the select! in fire_transition_async, executor_core/executor.rs; EXEC_022_forbids_relayIgnoredAtExpiry: the slot read in the action's arm only, so the timeout outcome of a relay-rejected firing is deposited). That the later batches of a relayBad firing are dropped is NU-054's and not line 4's: line 4 reads a firing that holds a timeout outcome."
          "Lines 6 to 8 identify the firing by its identity. Identities are drawn once from one supply (XSt.nextId); the premise IdsIssued says every firing in flight at the start of the run has an identity the supply has already handed out, true at the start of every run (nothing is in flight) and kept by every reference step (exec022_idsIssued_step). Without it a later start could reuse an identity, as in EXEC-031."
          "AC1 (an action that completes in 50ms with a 100ms timeout completes normally) and AC2 (an action that hands control back and takes 200ms with a 100ms timeout ends with the timeout branch and an ActionTimedOut event) are host-time behaviour under ruling D18 (b): which side wins is decided by the host's timer, outside the model, so their timing is test-only (kind Q). What the model says of each outcome is line 7 for AC1 (after the return, no timeout outcome; the completion's validation is EXEC-021's) and lines 1 to 6 for AC2, with the event EVT-010's; EXEC_022_allows_completionFirst and EXEC_022_allows_timeoutFirst are the two outcomes on one example, and EXEC_022_nonvacuous runs both to their deposits."
          "AC3 (ForwardInput in the timeout child forwards every consumed token, one output token per consumed token, in consumption order, each keeping its created_at) is line 1's exec022_QOutcome with lines 2 and 3: EXEC_022_nonvacuous consumes 7 and 8 and deposits [7, 8] in the forward's target; EXEC_022_forbids_forwardFirst forwards 7 alone."
          "AC4 (output the action wrote and had not published before the budget expired is discarded, not merged with the timeout branch; output it published before stays) is lines 2, 3, 4 and 6: EXEC_022_nonvacuous writes 50 to place 1 before the expiry, and place 1 stays empty after the timeout deposit; the published half is ruling D17, as in the seventh shall sentence above."
          "The test derivation (slow action with a timeout, verify the timeout branch tokens and the event) is EXEC_022_nonvacuous's timeout run, without the event (EVT-010, wave W7)."
  signoff "2026-11-13 4269c3fa66f4ad07 ai"
  statement : ∀ {N T : Type} [DecidableEq N], XRel N T → Prop :=
    fun R => ∀ C i,
      (∀ e, on (fun s s' => R C s (.expire i e) s'), shall (fun s _ =>
        ∃ f ∈ s.fl, f.id = i ∧ f.out = none ∧ f.sync = false ∧ hasTimeoutB f.t = true ∧
          (exec022_OutcomeSound C → exec022_QOutcome f.t f.deliv e))) ∧
      (∀ e, on (fun s s' => R C s (.expire i e) s'), shall (fun s s' =>
        s'.M = s.M ∧ s'.pq = s.pq ∧
          ∀ f ∈ s'.fl, f.id = i → f.out = some (if f.relayBad then .err else .timedOut e))) ∧
      (on (fun s s' => R C s (.tdeposit i) s'), shall (fun s s' =>
        ∃ f ∈ s.fl, f.id = i ∧ ∃ e, f.out = some (.timedOut e) ∧ s'.M = qAppend s.M e)) ∧
      (on (fun s s' => R C s (.flush i) s'), shall (fun s s' =>
        (∀ f ∈ s.fl, f.id = i → ∃ e, f.out = some (.timedOut e)) →
          s'.M = s.M ∧ s'.pq = s.pq)) ∧
      (∀ l, on (fun s s' => R C s l s'), shall (fun s s' =>
        (∀ o, exec022_Recorded o i s → exec022_Recorded o i s') ∧
          ∀ f' ∈ s'.fl, f'.id = i → ∀ e, f'.out = some (.timedOut e) →
            (∃ f ∈ s.fl, f.id = i ∧ f.out = some (.timedOut e)) ∨ ∃ e', l = .expire i e')) ∧
      (∀ s0 tr, IdsIssued s0 → XRun R C s0 tr →
        (after (exec022_isExpire i), never (exec022_isCommit i)) tr) ∧
      (∀ s0 tr, IdsIssued s0 → XRun R C s0 tr →
        (after (exec022_isOpenReturn i), never (exec022_isTimeout i)) tr) ∧
      (∀ s0 tr, IdsIssued s0 → XRun R C s0 tr →
        (after (exec022_isTDeposit i), never (exec022_isSettle i)) tr)

/- The pinned readable form of EXEC-022: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EXEC_022 : {N T : Type} → [DecidableEq N] → XRel N T → Prop :=
fun {N T} [DecidableEq N] R =>
  ∀ (C : Cfg N T) (i : ℕ),
    (∀ (e : List (N × T)),
        on fun s s' => R C s (XLbl.expire i e) s', shall fun s x =>
          ∃ f ∈ s.fl,
            f.id = i ∧
              f.out = none ∧
                f.sync = false ∧ hasTimeoutB f.t = true ∧ (exec022_OutcomeSound C → exec022_QOutcome f.t f.deliv e)) ∧
      (∀ (e : List (N × T)),
          on fun s s' => R C s (XLbl.expire i e) s', shall fun s s' =>
            s'.M = s.M ∧
              s'.pq = s.pq ∧
                ∀ f ∈ s'.fl, f.id = i → f.out = some (if f.relayBad = true then Outcome.err else Outcome.timedOut e)) ∧
        (on fun s s' => R C s (XLbl.tdeposit i) s', shall fun s s' =>
            ∃ f ∈ s.fl, f.id = i ∧ ∃ e, f.out = some (Outcome.timedOut e) ∧ s'.M = qAppend s.M e) ∧
          (on fun s s' => R C s (XLbl.flush i) s', shall fun s s' =>
              (∀ f ∈ s.fl, f.id = i → ∃ e, f.out = some (Outcome.timedOut e)) → s'.M = s.M ∧ s'.pq = s.pq) ∧
            (∀ (l : XLbl N T),
                on fun s s' => R C s l s', shall fun s s' =>
                  (∀ (o : Outcome N T), exec022_Recorded o i s → exec022_Recorded o i s') ∧
                    ∀ f' ∈ s'.fl,
                      f'.id = i →
                        ∀ (e : List (N × T)),
                          f'.out = some (Outcome.timedOut e) →
                            (∃ f ∈ s.fl, f.id = i ∧ f.out = some (Outcome.timedOut e)) ∨ ∃ e', l = XLbl.expire i e') ∧
              (∀ (s0 : XSt N T) (tr : List (XStep N T)),
                  IdsIssued s0 → XRun R C s0 tr → (after exec022_isExpire i, never exec022_isCommit i) tr) ∧
                (∀ (s0 : XSt N T) (tr : List (XStep N T)),
                    IdsIssued s0 → XRun R C s0 tr → (after exec022_isOpenReturn i, never exec022_isTimeout i) tr) ∧
                  ∀ (s0 : XSt N T) (tr : List (XStep N T)),
                    IdsIssued s0 → XRun R C s0 tr → (after exec022_isTDeposit i, never exec022_isSettle i) tr
-/
#guard_msgs in #print EXEC_022

/-! ### The reference -/

section Reference

variable {N T : Type} [DecidableEq N]

/-- One step keeps the identity supply: the supply never goes back, and every firing in flight
after the step was in flight before it (same identity) or got an identity the step handed out. -/
def exec022_IdFrame (s s' : XSt N T) : Prop :=
  s.nextId ≤ s'.nextId ∧
    ∀ f ∈ s'.fl, (∃ g ∈ s.fl, g.id = f.id) ∨ (s.nextId ≤ f.id ∧ f.id < s'.nextId)

omit [DecidableEq N] in
/-- A step that keeps the supply and only keeps, updates or drops firings keeps the frame. -/
theorem exec022_idFrame_of {s s' : XSt N T} (hn : s'.nextId = s.nextId)
    (hfl : ∀ f ∈ s'.fl, ∃ g ∈ s.fl, g.id = f.id) : exec022_IdFrame s s' :=
  ⟨hn ▸ Nat.le_refl _, fun f hf => Or.inl (hfl f hf)⟩

omit [DecidableEq N] in
/-- A firing of `updFiring s j h` is a firing of `s` with another identity, kept as it was, or a
firing of `s` with identity `j`, updated by `h`. -/
theorem exec022_mem_upd {s : XSt N T} {j : Nat} {h : Firing N T → Firing N T}
    {f : Firing N T} (hf : f ∈ updFiring s j h) :
    ∃ g ∈ s.fl, (g.id ≠ j ∧ g = f) ∨ (g.id = j ∧ f = h g) := by
  unfold updFiring at hf
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
  refine ⟨g, hg, ?_⟩
  by_cases hgj : g.id = j
  · exact Or.inr ⟨hgj, by simp [hgj]⟩
  · exact Or.inl ⟨hgj, by simp [hgj]⟩

omit [DecidableEq N] in
/-- Updating firing `i`'s record by an `h` that keeps identities keeps every identity. -/
theorem exec022_mem_updFiring {s : XSt N T} {i : Nat} {h : Firing N T → Firing N T}
    (hh : ∀ g, (h g).id = g.id) {f : Firing N T} (hf : f ∈ updFiring s i h) :
    ∃ g ∈ s.fl, g.id = f.id := by
  obtain ⟨g, hg, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := exec022_mem_upd hf
  · exact ⟨g, hg, rfl⟩
  · exact ⟨g, hg, (hh g).symm⟩

omit [DecidableEq N] in
/-- A settle drops firing `i` and keeps the others. -/
theorem exec022_mem_settle {s : XSt N T} {i : Nat} {f : Firing N T}
    (hf : f ∈ (settle s i).fl) : f ∈ s.fl ∧ f.id ≠ i := by
  simp only [settle, List.mem_filter, bne_iff_ne, ne_eq] at hf
  exact hf

/-- Every reference step (at any judgement points `P`) keeps the identity frame: only `start`
adds a firing, with the identity it draws from the supply; `request` draws a ticket; every other
step keeps, updates or drops firings, and keeps the supply. -/
theorem exec022_idFrame_step {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : xstepW P C s l = some s') : exec022_IdFrame s s' := by
  have same : ∀ {s'' : XSt N T}, s''.nextId = s.nextId → s''.fl = s.fl →
      exec022_IdFrame s s'' := fun hn hfl =>
    exec022_idFrame_of hn fun f hf => ⟨f, hfl ▸ hf, rfl⟩
  have upd : ∀ {s'' : XSt N T} {i : Nat} {h : Firing N T → Firing N T},
      s''.fl = updFiring s i h → s''.nextId = s.nextId → (∀ g, (h g).id = g.id) →
      exec022_IdFrame s s'' :=
    fun hfl hn hh => exec022_idFrame_of hn fun f hf => exec022_mem_updFiring hh (hfl ▸ hf)
  have stl : ∀ {s'' : XSt N T} {i : Nat}, s''.nextId = s.nextId → s''.fl = (settle s i).fl →
      exec022_IdFrame s s'' := fun hn hfl =>
    exec022_idFrame_of hn fun f hf => ⟨f, (exec022_mem_settle (hfl ▸ hf)).1, rfl⟩
  cases l with
  | delay δ => obtain rfl := xstepW_delay h; exact same rfl rfl
  | write i p x =>
    obtain ⟨-, -, -, rfl⟩ := writeStep_some h; exact upd rfl rfl (fun _ => rfl)
  | flush i =>
    obtain ⟨-, -, -, -, -, ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ := flushStep_some h
    · exact upd rfl rfl (fun _ => rfl)
    · exact upd rfl rfl (fun _ => rfl)
  | ret i ok => obtain ⟨-, -, -, rfl⟩ := retStep_some h; exact upd rfl rfl (fun _ => rfl)
  | expire i e =>
    obtain ⟨-, -, -, -, -, -, rfl⟩ := expireStep_some h; exact upd rfl rfl (fun _ => rfl)
  | request p x r =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := requestStep_some h
    · exact ⟨Nat.le_succ _, fun f hf => Or.inl ⟨f, hf, rfl⟩⟩
    · exact same rfl rfl
  | drain => obtain ⟨-, rfl⟩ := drainStep_some h; exact same rfl rfl
  | close => obtain ⟨-, rfl⟩ := closeStep_some h; exact same rfl rfl
  | terminateNow => obtain ⟨-, rfl⟩ := terminateStep_some h; exact same rfl rfl
  | commit i =>
    obtain ⟨-, -, -, -, -, -, -, rfl⟩ := commitStep_some h; exact stl rfl rfl
  | fail i => obtain ⟨-, -, -, -, rfl⟩ := failStep_some h; exact stl rfl rfl
  | tdeposit i => obtain ⟨-, -, -, -, -, -, rfl⟩ := tdepositStep_some h; exact stl rfl rfl
  | endCompletions => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endCompletions h; exact same rfl rfl
  | publish i => obtain ⟨-, -, -, -, -, rfl⟩ := publishStep_some h; exact same rfl rfl
  | endPublications => obtain ⟨-, -, -, rfl⟩ := xstepW_endPublications h; exact same rfl rfl
  | inject k => obtain ⟨-, -, -, -, -, -, -, rfl⟩ := injectStep_some h; exact same rfl rfl
  | discard k => obtain ⟨-, -, -, -, -, -, -, rfl⟩ := discardStep_some h; exact same rfl rfl
  | snapshot a => obtain ⟨-, -, -, rfl⟩ := snapshotStep_some h; exact same rfl rfl
  | endEvents => obtain ⟨-, -, -, rfl⟩ := xstepW_endEvents h; exact same rfl rfl
  | update => obtain ⟨-, -, rfl⟩ := xstepW_update h; exact same rfl rfl
  | deadline ns => obtain ⟨-, -, -, rfl⟩ := xstepW_deadline h; exact same rfl rfl
  | finish c =>
    cases c with
    | quiescent => obtain ⟨-, -, -, rfl⟩ := xstepW_finishQuiescent h; exact same rfl rfl
    | closed => obtain ⟨-, -, -, -, rfl⟩ := xstepW_finishClosed h; exact same rfl rfl
    | terminal => obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h; exact same rfl rfl
    | stopped => obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h; exact same rfl rfl
  | begin => obtain ⟨-, -, -, -, rfl⟩ := xstepW_begin h; exact same rfl rfl
  | start n sy =>
    obtain ⟨-, -, -, -, -, -, -, -, -, rfl⟩ := startStep_some h
    refine ⟨Nat.le_succ _, fun f hf => ?_⟩
    rcases List.mem_append.mp hf with hf | hf
    · exact Or.inl ⟨f, hf, rfl⟩
    · rw [List.mem_singleton] at hf
      subst hf
      exact Or.inr ⟨Nat.le_refl _, Nat.lt_succ_self _⟩
  | lose n => obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := loseStep_some h; exact same rfl rfl
  | endPass => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endPass h; exact same rfl rfl
  | park tmr => obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := parkStep_some h; exact same rfl rfl
  | wake => obtain ⟨-, -, rfl⟩ := wakeStep_some h; exact same rfl rfl

/-- Every reference step keeps `IdsIssued`. -/
theorem exec022_idsIssued_step {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : xstepW P C s l = some s') (hs : IdsIssued s) : IdsIssued s' := by
  have hfr := exec022_idFrame_step h
  intro f hf
  rcases hfr.2 f hf with ⟨g, hg, hid⟩ | ⟨-, hlt⟩
  · exact hid ▸ Nat.lt_of_lt_of_le (hs g hg) hfr.1
  · exact hlt

/-- The outcome is a completion's (`ok`). -/
def exec022_isOkOut : Outcome N T → Bool
  | .ok _ => true
  | _ => false

/-- The outcome is a timeout outcome. -/
def exec022_isTimedOutOut : Outcome N T → Bool
  | .timedOut _ => true
  | _ => false

/-- Firing `i` has ended with an outcome satisfying `P`: the identity `i` was handed out, and
every firing in flight with identity `i` holds an outcome `P` accepts. After the expiry of `i`
(`P` = not a completion), its return (`P` = not a timeout outcome), or its settle (`P` = nothing:
no firing `i` is left) this holds for the rest of the run. -/
def exec022_Closed (P : Outcome N T → Prop) (i : Nat) (s : XSt N T) : Prop :=
  i < s.nextId ∧ ∀ f ∈ s.fl, f.id = i → ∃ o, f.out = some o ∧ P o

omit [DecidableEq N] in
/-- A firing has recorded `o` exactly when it is closed with the outcome `o`. -/
theorem exec022_recorded_iff {o : Outcome N T} {i : Nat} {s : XSt N T} :
    exec022_Recorded o i s ↔ exec022_Closed (· = o) i s :=
  ⟨fun h => ⟨h.1, fun f hf hid => ⟨o, h.2 f hf hid, rfl⟩⟩,
   fun h => ⟨h.1, fun f hf hid => by obtain ⟨o', ho, rfl⟩ := h.2 f hf hid; exact ho⟩⟩

omit [DecidableEq N] in
/-- A closed firing has an outcome set, so no outside step of it is offered. -/
theorem exec022_closed_set {P : Outcome N T → Prop} {s : XSt N T} {i : Nat} {f : Firing N T}
    (hb : exec022_Closed P i s) (hf : s.fl.find? (·.id == i) = some f) : f.out ≠ none := by
  obtain ⟨o, ho, -⟩ := hb.2 f (List.mem_of_find?_eq_some hf) (by simpa using List.find?_some hf)
  rw [ho]
  exact Option.some_ne_none _

omit [DecidableEq N] in
/-- The closed firing's outcome, read off the record the step finds. -/
theorem exec022_closed_out {P : Outcome N T → Prop} {s : XSt N T} {i : Nat} {f : Firing N T}
    (hb : exec022_Closed P i s) (hf : s.fl.find? (·.id == i) = some f) :
    ∃ o, f.out = some o ∧ P o :=
  hb.2 f (List.mem_of_find?_eq_some hf) (by simpa using List.find?_some hf)

omit [DecidableEq N] in
/-- Updating the record of another identity `j` keeps every firing `i`'s outcome. -/
theorem exec022_closed_upd {P : Outcome N T → Prop} {s : XSt N T} {i j : Nat}
    {h : Firing N T → Firing N T} (hb : exec022_Closed P i s) (hj : j ≠ i)
    (hh : ∀ g, (h g).id = g.id) :
    ∀ f ∈ updFiring s j h, f.id = i → ∃ o, f.out = some o ∧ P o := by
  intro f hf hid
  obtain ⟨g, hg, ⟨-, rfl⟩ | ⟨hgj, rfl⟩⟩ := exec022_mem_upd hf
  · exact hb.2 g hg hid
  · exact absurd (hgj.symm.trans ((hh g).symm.trans hid)) hj

/-- Every reference step keeps a closed firing closed: an outside step of `i` needs an open
outcome, an outside step of another firing leaves firing `i` alone, a settle only drops firings,
and a start draws an identity above `i`. -/
theorem exec022_closed_step {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    {i : Nat} {Q : Outcome N T → Prop} (h : xstepW P C s l = some s')
    (hb : exec022_Closed Q i s) : exec022_Closed Q i s' := by
  refine ⟨Nat.lt_of_lt_of_le hb.1 (exec022_idFrame_step h).1, ?_⟩
  have sub : ∀ {s'' : XSt N T}, (∀ f ∈ s''.fl, f ∈ s.fl) →
      ∀ f ∈ s''.fl, f.id = i → ∃ o, f.out = some o ∧ Q o :=
    fun hs f hf hid => hb.2 f (hs f hf) hid
  have same : ∀ {s'' : XSt N T}, s''.fl = s.fl →
      ∀ f ∈ s''.fl, f.id = i → ∃ o, f.out = some o ∧ Q o :=
    fun hfl => sub fun f hf => hfl ▸ hf
  have stl : ∀ {s'' : XSt N T} {j : Nat}, s''.fl = (settle s j).fl →
      ∀ f ∈ s''.fl, f.id = i → ∃ o, f.out = some o ∧ Q o :=
    fun hfl => sub fun f hf => (exec022_mem_settle (hfl ▸ hf)).1
  have opn : ∀ {j : Nat} {f : Firing N T}, s.fl.find? (·.id == j) = some f → f.out = none →
      j ≠ i := fun hf ho hj => exec022_closed_set hb (hj ▸ hf) ho
  cases l with
  | delay δ => obtain rfl := xstepW_delay h; exact same rfl
  | write j p x =>
    obtain ⟨f, hf, ho, rfl⟩ := writeStep_some h
    exact exec022_closed_upd hb (opn hf ho) (fun _ => rfl)
  | flush j =>
    obtain ⟨f, hf, ho, -, -, ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ := flushStep_some h
    · exact exec022_closed_upd hb (opn hf ho) (fun _ => rfl)
    · exact exec022_closed_upd hb (opn hf ho) (fun _ => rfl)
  | ret j ok =>
    obtain ⟨f, hf, ho, rfl⟩ := retStep_some h
    exact exec022_closed_upd hb (opn hf ho) (fun _ => rfl)
  | expire j e =>
    obtain ⟨f, hf, ho, -, -, -, rfl⟩ := expireStep_some h
    exact exec022_closed_upd hb (opn hf ho) (fun _ => rfl)
  | request p x r =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := requestStep_some h
    · exact same rfl
    · exact same rfl
  | drain => obtain ⟨-, rfl⟩ := drainStep_some h; exact same rfl
  | close => obtain ⟨-, rfl⟩ := closeStep_some h; exact same rfl
  | terminateNow => obtain ⟨-, rfl⟩ := terminateStep_some h; exact same rfl
  | commit j => obtain ⟨-, -, -, -, -, -, -, rfl⟩ := commitStep_some h; exact stl rfl
  | fail j => obtain ⟨-, -, -, -, rfl⟩ := failStep_some h; exact stl rfl
  | tdeposit j => obtain ⟨-, -, -, -, -, -, rfl⟩ := tdepositStep_some h; exact stl rfl
  | endCompletions => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endCompletions h; exact same rfl
  | publish j => obtain ⟨-, -, -, -, -, rfl⟩ := publishStep_some h; exact same rfl
  | endPublications => obtain ⟨-, -, -, rfl⟩ := xstepW_endPublications h; exact same rfl
  | inject k => obtain ⟨-, -, -, -, -, -, -, rfl⟩ := injectStep_some h; exact same rfl
  | discard k => obtain ⟨-, -, -, -, -, -, -, rfl⟩ := discardStep_some h; exact same rfl
  | snapshot a => obtain ⟨-, -, -, rfl⟩ := snapshotStep_some h; exact same rfl
  | endEvents => obtain ⟨-, -, -, rfl⟩ := xstepW_endEvents h; exact same rfl
  | update => obtain ⟨-, -, rfl⟩ := xstepW_update h; exact same rfl
  | deadline ns => obtain ⟨-, -, -, rfl⟩ := xstepW_deadline h; exact same rfl
  | finish c =>
    cases c with
    | quiescent => obtain ⟨-, -, -, rfl⟩ := xstepW_finishQuiescent h; exact same rfl
    | closed => obtain ⟨-, -, -, -, rfl⟩ := xstepW_finishClosed h; exact same rfl
    | terminal => obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h; exact same rfl
    | stopped => obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h; exact same rfl
  | begin => obtain ⟨-, -, -, -, rfl⟩ := xstepW_begin h; exact same rfl
  | start n sy =>
    obtain ⟨-, -, -, -, -, -, -, -, -, rfl⟩ := startStep_some h
    intro f hf hid
    rcases List.mem_append.mp hf with hf | hf
    · exact hb.2 f hf hid
    · rw [List.mem_singleton] at hf
      subst hf
      have := hb.1
      simp only at hid
      omega
  | lose n => obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := loseStep_some h; exact same rfl
  | endPass => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endPass h; exact same rfl
  | park tmr => obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := parkStep_some h; exact same rfl
  | wake => obtain ⟨-, -, rfl⟩ := wakeStep_some h; exact same rfl

/-- Only the expiry of `i` records a timeout outcome of `i`: every other reference step keeps the
outcome of every firing it keeps, gives a new firing no outcome, and a return records a completion
or an error. -/
theorem exec022_onlyExpiry_step {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    {i : Nat} (h : xstepW P C s l = some s') :
    ∀ f' ∈ s'.fl, f'.id = i → ∀ e, f'.out = some (.timedOut e) →
      (∃ f ∈ s.fl, f.id = i ∧ f.out = some (.timedOut e)) ∨ ∃ e', l = .expire i e' := by
  intro f' hf' hid e he
  have kept : f' ∈ s.fl → ∃ f ∈ s.fl, f.id = i ∧ f.out = some (.timedOut e) :=
    fun hm => ⟨f', hm, hid, he⟩
  have upd : ∀ {s'' : XSt N T} {j : Nat} {g' : Firing N T → Firing N T}, f' ∈ s''.fl →
      s''.fl = updFiring s j g' → (∀ g, (g' g).id = g.id) → (∀ g, (g' g).out = g.out) →
      ∃ f ∈ s.fl, f.id = i ∧ f.out = some (.timedOut e) := by
    intro s'' j g' hm hfl hid' hout
    rw [hfl] at hm
    obtain ⟨g, hg, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := exec022_mem_upd hm
    · exact kept hg
    · exact ⟨g, hg, (hid' g).symm.trans hid, (hout g).symm.trans he⟩
  have stl : ∀ {s'' : XSt N T} {j : Nat}, f' ∈ s''.fl → s''.fl = (settle s j).fl →
      ∃ f ∈ s.fl, f.id = i ∧ f.out = some (.timedOut e) :=
    fun hm hfl => kept (exec022_mem_settle (hfl ▸ hm)).1
  cases l with
  | delay δ => obtain rfl := xstepW_delay h; exact Or.inl (kept hf')
  | write j p x =>
    obtain ⟨_, _, _, rfl⟩ := writeStep_some h
    exact Or.inl (upd hf' rfl (fun _ => rfl) (fun _ => rfl))
  | flush j =>
    obtain ⟨_, _, _, _, _, ⟨_, _, rfl⟩ | ⟨_, rfl⟩⟩ := flushStep_some h
    · exact Or.inl (upd hf' rfl (fun _ => rfl) (fun _ => rfl))
    · exact Or.inl (upd hf' rfl (fun _ => rfl) (fun _ => rfl))
  | ret j ok =>
    obtain ⟨_, _, _, rfl⟩ := retStep_some h
    obtain ⟨g, hg, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := exec022_mem_upd hf'
    · exact Or.inl (kept hg)
    · exfalso
      revert he
      cases ok <;> cases g.relayBad <;> simp
  | expire j e₀ =>
    obtain ⟨_, _, _, _, _, _, rfl⟩ := expireStep_some h
    obtain ⟨g, hg, ⟨-, rfl⟩ | ⟨hgj, rfl⟩⟩ := exec022_mem_upd hf'
    · exact Or.inl (kept hg)
    · have hji : j = i := hgj.symm.trans hid
      subst hji
      exact Or.inr ⟨e₀, rfl⟩
  | request p x r =>
    obtain ⟨_, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩ := requestStep_some h
    · exact Or.inl (kept hf')
    · exact Or.inl (kept hf')
  | drain => obtain ⟨_, rfl⟩ := drainStep_some h; exact Or.inl (kept hf')
  | close => obtain ⟨_, rfl⟩ := closeStep_some h; exact Or.inl (kept hf')
  | terminateNow => obtain ⟨_, rfl⟩ := terminateStep_some h; exact Or.inl (kept hf')
  | commit j =>
    obtain ⟨_, _, _, _, _, _, _, rfl⟩ := commitStep_some h; exact Or.inl (stl hf' rfl)
  | fail j => obtain ⟨_, _, _, _, rfl⟩ := failStep_some h; exact Or.inl (stl hf' rfl)
  | tdeposit j =>
    obtain ⟨_, _, _, _, _, _, rfl⟩ := tdepositStep_some h; exact Or.inl (stl hf' rfl)
  | endCompletions => obtain ⟨_, _, _, _, rfl⟩ := xstepW_endCompletions h; exact Or.inl (kept hf')
  | publish j => obtain ⟨_, _, _, _, _, rfl⟩ := publishStep_some h; exact Or.inl (kept hf')
  | endPublications => obtain ⟨_, _, _, rfl⟩ := xstepW_endPublications h; exact Or.inl (kept hf')
  | inject k => obtain ⟨_, _, _, _, _, _, _, rfl⟩ := injectStep_some h; exact Or.inl (kept hf')
  | discard k => obtain ⟨_, _, _, _, _, _, _, rfl⟩ := discardStep_some h; exact Or.inl (kept hf')
  | snapshot a => obtain ⟨_, _, _, rfl⟩ := snapshotStep_some h; exact Or.inl (kept hf')
  | endEvents => obtain ⟨_, _, _, rfl⟩ := xstepW_endEvents h; exact Or.inl (kept hf')
  | update => obtain ⟨_, _, rfl⟩ := xstepW_update h; exact Or.inl (kept hf')
  | deadline ns => obtain ⟨_, _, _, rfl⟩ := xstepW_deadline h; exact Or.inl (kept hf')
  | finish c =>
    cases c with
    | quiescent => obtain ⟨_, _, _, rfl⟩ := xstepW_finishQuiescent h; exact Or.inl (kept hf')
    | closed => obtain ⟨_, _, _, _, rfl⟩ := xstepW_finishClosed h; exact Or.inl (kept hf')
    | terminal => obtain ⟨_, _, rfl⟩ := xstepW_finishTerminal h; exact Or.inl (kept hf')
    | stopped => obtain ⟨_, _, _, rfl⟩ := xstepW_finishStopped h; exact Or.inl (kept hf')
  | begin => obtain ⟨_, _, _, _, rfl⟩ := xstepW_begin h; exact Or.inl (kept hf')
  | start n sy =>
    obtain ⟨_, _, _, _, _, _, _, _, _, rfl⟩ := startStep_some h
    rcases List.mem_append.mp hf' with hm | hm
    · exact Or.inl (kept hm)
    · rw [List.mem_singleton] at hm
      subst hm
      simp at he
  | lose n => obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := loseStep_some h; exact Or.inl (kept hf')
  | endPass => obtain ⟨_, _, _, _, rfl⟩ := xstepW_endPass h; exact Or.inl (kept hf')
  | park tmr => obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := parkStep_some h; exact Or.inl (kept hf')
  | wake => obtain ⟨_, _, rfl⟩ := wakeStep_some h; exact Or.inl (kept hf')

omit [DecidableEq N] in
/-- After a step that sets the outcome of every firing `i` by `h` (from a state whose identities
were handed out, and in which a firing `i` is in flight), firing `i` is closed for every `P`
that accepts every outcome `h` sets. -/
theorem exec022_closed_set_by {Q : Outcome N T → Prop} {s : XSt N T} {i : Nat}
    {f : Firing N T} {h : Firing N T → Firing N T} (hs : IdsIssued s)
    (hf : s.fl.find? (·.id == i) = some f)
    (hout : ∀ g, ∃ o, (h g).out = some o ∧ Q o) {s' : XSt N T}
    (hfl : s'.fl = updFiring s i h) (hn : s'.nextId = s.nextId) : exec022_Closed Q i s' := by
  have hid : f.id = i := by simpa using List.find?_some hf
  refine ⟨hn ▸ hid ▸ hs f (List.mem_of_find?_eq_some hf), fun g' hg' hid' => ?_⟩
  rw [hfl] at hg'
  unfold updFiring at hg'
  obtain ⟨g, -, rfl⟩ := List.mem_map.mp hg'
  by_cases hgi : g.id = i
  · have he : (g.id == i) = true := by simp [hgi]
    rw [he, if_pos rfl]
    exact hout g
  · have hne : (g.id == i) = false := by simpa using hgi
    rw [hne, if_neg Bool.false_ne_true] at hid'
    exact absurd hid' hgi

omit [DecidableEq N] in
/-- An expiry of `i` closes `i` against a completion: every firing `i` now holds a timeout
outcome, or an error after a relay-rejected batch. -/
theorem exec022_closed_expire {C : Cfg N T} {s s' : XSt N T} {i : Nat} {e : List (N × T)}
    (h : expireStep C s i e = some s') (hs : IdsIssued s) :
    exec022_Closed (fun o => exec022_isOkOut o = false) i s' := by
  obtain ⟨f, hf, -, -, -, -, rfl⟩ := expireStep_some h
  refine exec022_closed_set_by (h := fun g =>
    { g with out := some (if g.relayBad then .err else .timedOut e) }) hs hf
    (fun g => ?_) rfl rfl
  cases g.relayBad <;> exact ⟨_, rfl, rfl⟩

omit [DecidableEq N] in
/-- A return of `i` closes `i` against a timeout outcome: every firing `i` now holds a completion
or an error. -/
theorem exec022_closed_ret {s s' : XSt N T} {i : Nat} {ok : Bool}
    (h : retStep s i ok = some s') (hs : IdsIssued s) :
    exec022_Closed (fun o => exec022_isTimedOutOut o = false) i s' := by
  obtain ⟨f, hf, -, rfl⟩ := retStep_some h
  refine exec022_closed_set_by (h := fun g =>
    { g with out := some (if ok && !g.relayBad then .ok g.buf else .err) }) hs hf
    (fun g => ?_) rfl rfl
  cases ok <;> cases g.relayBad <;> exact ⟨_, rfl, rfl⟩

/-- A timeout deposit of `i` leaves no firing `i` in flight, for good: `i` is closed with no
outcome accepted. -/
theorem exec022_closed_tdeposit {C : Cfg N T} {s s' : XSt N T} {i : Nat}
    (h : tdepositStep C s i = some s') (hs : IdsIssued s) :
    exec022_Closed (fun _ => False) i s' := by
  obtain ⟨f, e, hf, -, -, -, rfl⟩ := tdepositStep_some h
  have hid : f.id = i := by simpa using List.find?_some hf
  exact ⟨hid ▸ hs f (List.mem_of_find?_eq_some hf),
    fun g hg hgi => absurd hgi (exec022_mem_settle (s := s) (i := i) hg).2⟩

/-- No step commits a firing closed against a completion: a commit needs a completion. -/
theorem exec022_commit_closed {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    {i : Nat} (h : xstepW P C s l = some s') (hd : exec022_isCommit i (s, l, s') = true)
    (hb : exec022_Closed (fun o => exec022_isOkOut o = false) i s) : False := by
  cases l with
  | commit j =>
    simp only [exec022_isCommit, beq_iff_eq] at hd
    subst hd
    obtain ⟨f, e, hf, he, -⟩ := commitStep_some h
    obtain ⟨o, ho, hbad⟩ := exec022_closed_out hb hf
    rw [he, Option.some.injEq] at ho
    subst ho
    simp [exec022_isOkOut] at hbad
  | _ => simp [exec022_isCommit] at hd

/-- No step ends with or deposits a timeout outcome for a firing closed against one: an expiry
needs no outcome set, a tdeposit needs a timeout outcome. -/
theorem exec022_timeout_closed {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    {i : Nat} (h : xstepW P C s l = some s') (hd : exec022_isTimeout i (s, l, s') = true)
    (hb : exec022_Closed (fun o => exec022_isTimedOutOut o = false) i s) : False := by
  cases l with
  | expire j e =>
    simp only [exec022_isTimeout, beq_iff_eq] at hd
    subst hd
    obtain ⟨f, hf, ho, -⟩ := expireStep_some h
    exact exec022_closed_set hb hf ho
  | tdeposit j =>
    simp only [exec022_isTimeout, beq_iff_eq] at hd
    subst hd
    obtain ⟨f, e, hf, he, -⟩ := tdepositStep_some h
    obtain ⟨o, ho, hbad⟩ := exec022_closed_out hb hf
    rw [he, Option.some.injEq] at ho
    subst ho
    simp [exec022_isTimedOutOut] at hbad
  | _ => simp [exec022_isTimeout] at hd

/-- No step settles a firing that is no longer in flight: every settle finds its firing. -/
theorem exec022_settle_closed {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    {i : Nat} (h : xstepW P C s l = some s') (hd : exec022_isSettle i (s, l, s') = true)
    (hb : exec022_Closed (fun _ => False) i s) : False := by
  cases l with
  | commit j =>
    simp only [exec022_isSettle, beq_iff_eq] at hd
    subst hd
    obtain ⟨f, -, hf, -⟩ := commitStep_some h
    obtain ⟨-, -, hF⟩ := exec022_closed_out hb hf
    exact hF
  | fail j =>
    simp only [exec022_isSettle, beq_iff_eq] at hd
    subst hd
    obtain ⟨f, hf, -⟩ := failStep_some h
    obtain ⟨-, -, hF⟩ := exec022_closed_out hb hf
    exact hF
  | tdeposit j =>
    simp only [exec022_isSettle, beq_iff_eq] at hd
    subst hd
    obtain ⟨f, -, hf, -⟩ := tdepositStep_some h
    obtain ⟨-, -, hF⟩ := exec022_closed_out hb hf
    exact hF
  | _ => simp [exec022_isSettle] at hd

/-- The scan of a trace line over a run of the reference step at judgement points `P`: a `trig`
step closes `i` with outcomes `Q`, a closed firing has no `badStep`, so with the ban memory `b`
every step is accepted, provided the identities were handed out and a set ban means `i` is
closed. -/
theorem exec022_scan {P : XPol N T} {C : Cfg N T} {i : Nat} {Q : Outcome N T → Prop}
    {trig badStep : XStep N T → Bool}
    (hEst : ∀ {s s' : XSt N T} {l : XLbl N T}, xstepW P C s l = some s' →
      IdsIssued s → trig (s, l, s') = true → exec022_Closed Q i s')
    (hBlk : ∀ {s s' : XSt N T} {l : XLbl N T}, xstepW P C s l = some s' →
      exec022_Closed Q i s → badStep (s, l, s') = true → False) :
    ∀ {s : XSt N T} {tr : List (XStep N T)} (b : Bool),
      XRun (fun C s l s' => xstepW P C s l = some s') C s tr → IdsIssued s →
      (b = true → exec022_Closed Q i s) →
      (afterNever trig badStep).scan b tr = true
  | _, [], _, _, _, _ => rfl
  | s, (s₁, l, s') :: rest, b, ⟨h1, hstep, hrest⟩, hs, hb => by
    simp only at h1
    subst h1
    have hs' := exec022_idsIssued_step hstep hs
    have hok : (b && badStep (s₁, l, s')) = false := by
      cases b with
      | false => rfl
      | true =>
        cases hd : badStep (s₁, l, s') with
        | false => rfl
        | true => exact (hBlk hstep (hb rfl) hd).elim
    have hnext : (b || trig (s₁, l, s')) = true → exec022_Closed Q i s' := by
      intro hn
      cases ht : trig (s₁, l, s') with
      | true => exact hEst hstep hs ht
      | false =>
        rw [ht, Bool.or_false] at hn
        exact exec022_closed_step hstep (hb hn)
    show (!(b && badStep (s₁, l, s')) &&
      (afterNever trig badStep).scan (b || trig (s₁, l, s')) rest) = true
    rw [hok, exec022_scan hEst hBlk _ hrest hs' hnext]
    rfl

/-- The executor of any judgement points `P` satisfies EXEC-022: its expiry rule checks that the
firing is open, asynchronous and has a `Timeout` node, takes an outcome the configuration accepts,
and only records it (`expireStep_some`); its `tdeposit` rule appends the recorded outcome
(`tdepositStep_some`); its flush needs an open firing (`flushStep_some`); no step changes a
recorded outcome (`exec022_closed_step`) and only the expiry records a timeout outcome
(`exec022_onlyExpiry_step`); an expiry closes the firing against a completion, a return closes it
against a timeout outcome, and a timeout deposit removes it, for the rest of the run
(`exec022_scan`). -/
theorem exec022_xstepW (P : XPol N T) :
    EXEC_022 (fun C s l s' => xstepW P C s l = some s') := by
  intro C i
  refine ⟨fun e s s' h => ?_, fun e s s' h => ?_, fun s s' h => ?_, fun s s' h hall => ?_,
    fun l s s' h => ?_, fun s0 tr hs hr => ?_, fun s0 tr hs hr => ?_, fun s0 tr hs hr => ?_⟩
  · obtain ⟨f, hf, ho, hsy, hT, hto, -⟩ := expireStep_some h
    exact ⟨f, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, ho, hsy, hT,
      fun hC => hC _ _ _ hto⟩
  · obtain ⟨-, -, -, -, -, -, rfl⟩ := expireStep_some h
    refine ⟨rfl, rfl, fun g' hg' hid => ?_⟩
    obtain ⟨g, -, ⟨hgi, rfl⟩ | ⟨-, rfl⟩⟩ := exec022_mem_upd hg'
    · exact absurd hid hgi
    · rfl
  · obtain ⟨f, e, hf, he, -, -, rfl⟩ := tdepositStep_some h
    exact ⟨f, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, e, he, rfl⟩
  · obtain ⟨f, hf, ho, -⟩ := flushStep_some h
    obtain ⟨e, he⟩ := hall f (List.mem_of_find?_eq_some hf) (by simpa using List.find?_some hf)
    rw [ho] at he
    exact absurd he (by simp)
  · exact ⟨fun o ho => exec022_recorded_iff.mpr (exec022_closed_step h
      (exec022_recorded_iff.mp ho)), exec022_onlyExpiry_step h⟩
  · refine exec022_scan (Q := fun o => exec022_isOkOut o = false)
      (fun {s s' l} hst hs ht => ?_) (fun hst hb hd => exec022_commit_closed hst hd hb)
      false hr hs (fun h => absurd h Bool.false_ne_true)
    cases l with
    | expire j e =>
      simp only [exec022_isExpire, beq_iff_eq] at ht
      subst ht
      exact exec022_closed_expire hst hs
    | _ => simp [exec022_isExpire] at ht
  · refine exec022_scan (Q := fun o => exec022_isTimedOutOut o = false)
      (fun {s s' l} hst hs ht => ?_) (fun hst hb hd => exec022_timeout_closed hst hd hb)
      false hr hs (fun h => absurd h Bool.false_ne_true)
    cases l with
    | ret j ok =>
      simp only [exec022_isOpenReturn, Bool.and_eq_true, beq_iff_eq] at ht
      obtain ⟨rfl, -⟩ := ht
      exact exec022_closed_ret hst hs
    | _ => simp [exec022_isOpenReturn] at ht
  · refine exec022_scan (Q := fun _ => False)
      (fun {s s' l} hst hs ht => ?_) (fun hst hb hd => exec022_settle_closed hst hd hb)
      false hr hs (fun h => absurd h Bool.false_ne_true)
    cases l with
    | tdeposit j =>
      simp only [exec022_isTDeposit, beq_iff_eq] at ht
      subst ht
      exact exec022_closed_tdeposit hst hs
    | _ => simp [exec022_isTDeposit] at ht

end Reference

/-- ✓ The reference executor satisfies EXEC-022 (`exec022_xstepW` at `refXPol`). -/
@[evidence holds EXEC_022]
theorem EXEC_022_reference {N T : Type} [DecidableEq N] :
    EXEC_022 (RefExec (N := N) (T := T)) :=
  exec022_xstepW refXPol

/-! ### Examples

The transition `t` takes two tokens from place `0` (an `Exactly(2)` input arc); its output spec is
`Xor(Place(1), Timeout(d, ForwardInput(0, 2)))`: the action writes place `1`, or the budget runs
out and the two consumed tokens are forwarded to place `2`. The initial marking holds `7` and `8`
in place `0`. The configuration's timeout outcomes are `exec022_refOut`, which is sound
(`exec022_refOut_sound`). -/

/-- A timeout-outcome check for the examples: a `Timeout` child that is one `ForwardInput(s, d)`
forwards exactly the consumed tokens of `s`, in order; one that is a `Place p` mints one token in
`p`; any other child or no `Timeout` node has no outcome here. -/
def exec022_refOut (t : Trans Nat) (δ : QDelivered Nat Nat) (e : List (Nat × Nat)) : Bool :=
  match t.out.bind Out.findTimeout with
  | some (.forward src dst) => e == (δ.inputs src).map fun x => (dst, x)
  | some (.place p) =>
    match e with
    | [(q, _)] => q == p
    | _ => false
  | _ => false

/-- The example check accepts only token-level timeout outcomes. -/
theorem exec022_refOut_sound (t : Trans Nat) (δ : QDelivered Nat Nat) (e : List (Nat × Nat))
    (h : exec022_refOut t δ e = true) : exec022_QOutcome t δ e := by
  unfold exec022_refOut at h
  cases ho : t.out with
  | none => simp [ho] at h
  | some o =>
    rw [ho] at h
    cases hc : o.findTimeout with
    | none => simp [hc] at h
    | some c =>
      simp only [Option.bind_some, hc] at h
      refine ⟨o, c, e, ho, hc, ?_, fun _ => rfl⟩
      cases c with
      | forward src dst => simpa [exec022_Emits] using h
      | place p =>
        match e, h with
        | [(q, x)], h => exact ⟨x, by simp at h; rw [h]⟩
      | and l r => simp at h
      | xor l r => simp at h
      | timeout c => simp at h

/-- A transition named `t`: two tokens from `0` (`Exactly(2)`), output spec `o`. -/
def exec022_t (o : Out Nat) : Trans Nat :=
  { core := { name := "t", inputs := [{ place := 0, card := .exactly 2 }], inhibitors := [],
              reads := [], resets := [] },
    out := some o }

/-- `Xor(Place(1), Timeout(d, ForwardInput(0, 2)))`. -/
def exec022_spec : Out Nat := .xor (.place 1) (.timeout (.forward 0 2))

/-- The configuration of the examples for transition `t`. -/
def exec022_cfg (t : Trans Nat) : Cfg Nat Nat :=
  { X := { net := { places := [0, 1, 2], transitions := [t] }, timing := fun _ => .immediate,
           tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [], reentrant := false,
    validate := cfgValidate ioRefValidate, relay := fun _ _ _ => true,
    timeoutOut := exec022_refOut, res := 0 }

/-- The configuration with the timeout transition. -/
def exec022_C : Cfg Nat Nat := exec022_cfg (exec022_t exec022_spec)

/-- The configuration with the timeout transition and a join-relay check that rejects every
token for place `1` (the action's own output place) and accepts the timeout outcome. -/
def exec022_Crelay : Cfg Nat Nat :=
  { exec022_C with relay := fun _ _ e => e.all fun x => x.1 != 1 }

/-- Every example configuration's timeout outcomes are token-level outcomes. -/
theorem exec022_cfg_sound (t : Trans Nat) : exec022_OutcomeSound (exec022_cfg t) :=
  exec022_refOut_sound

/-- The initial marking: `7` and `8` in place `0`. -/
def exec022_m0 : QMarking Nat Nat := fun p => if p = 0 then [7, 8] else []

/-- The initial state of the examples. -/
def exec022_s0 : XSt Nat Nat := xinit exec022_m0 0

/-- The initial state has nothing in flight. -/
theorem exec022_s0_issued : IdsIssued exec022_s0 := fun _ hf => by
  simp [exec022_s0, xinit] at hf

/-- One cycle up to the start of `t`, synchronous or not. -/
def exec022_pre (sy : Bool) : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin, .start "t" sy]

/-- The timeout outcome of the example: `7` and `8` forwarded to place `2`, in consumption
order. -/
def exec022_out : List (Nat × Nat) := [(2, 7), (2, 8)]

/-- The race: `t` started asynchronously, its action wrote `50` to place `1` and has not
published it. -/
def exec022_race : List (XLbl Nat Nat) := exec022_pre false ++ [.write 0 1 50]

/-- The race after the budget ran out. -/
def exec022_expired : List (XLbl Nat Nat) := exec022_race ++ [.expire 0 exec022_out]

/-- Every firing with identity `0` in `s` satisfies `p`. -/
def exec022_all0 (s : XSt Nat Nat) (p : Firing Nat Nat → Bool) : Bool :=
  s.fl.all fun f => f.id != 0 || p f

/-- Read `p` off every firing with identity `0`. -/
theorem exec022_of_all0 {s : XSt Nat Nat} {p : Firing Nat Nat → Bool}
    (h : exec022_all0 s p = true) {f : Firing Nat Nat} (hf : f ∈ s.fl) (hid : f.id = 0) :
    p f = true := by
  have := List.all_eq_true.mp h f hf
  simpa [hid] using this

/-- The firing holds a timeout outcome. -/
def exec022_isTOB (f : Firing Nat Nat) : Bool :=
  match f.out with
  | some (.timedOut _) => true
  | _ => false

/-- Read a timeout outcome off `exec022_isTOB`. -/
theorem exec022_of_isTOB {f : Firing Nat Nat} (h : exec022_isTOB f = true) :
    ∃ e, f.out = some (.timedOut e) := by
  unfold exec022_isTOB at h
  split at h
  · exact ⟨_, ‹_›⟩
  · exact absurd h Bool.false_ne_true

/-- The firing holds the timeout outcome of the example. -/
def exec022_isOutB (f : Firing Nat Nat) : Bool :=
  match f.out with
  | some (.timedOut e) => e == exec022_out
  | _ => false

/-- `exec022_isOutB` says the firing holds the timeout outcome of the example. -/
theorem exec022_isOutB_iff {f : Firing Nat Nat} :
    exec022_isOutB f = true ↔ f.out = some (.timedOut exec022_out) := by
  unfold exec022_isOutB
  cases f.out with
  | none => simp
  | some o => cases o <;> simp

/-- A decided check of `exec022_Recorded` for the example's timeout outcome and identity `0`. -/
theorem exec022_recorded_of {s : XSt Nat Nat}
    (h : (decide (0 < s.nextId) && exec022_all0 s exec022_isOutB) = true) :
    exec022_Recorded (.timedOut exec022_out) 0 s := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, fun f hf hid => exec022_isOutB_iff.mp (exec022_of_all0 h.2 hf hid)⟩

/-! ### The race, both ways (ruling D18 (b)) -/

/-- ✓ The completion may win: from the race state the action's return is offered, and its
completion is then committed (`50` lands in place `1`, nothing in place `2`). -/
@[evidence allows EXEC_022]
theorem EXEC_022_allows_completionFirst :
    ∃ s s', xrun exec022_C exec022_s0 exec022_race = some s ∧
      RefExec exec022_C s (.ret 0 true) s' ∧
      ∃ s'', xrun exec022_C s' [.endPass, .commit 0] = some s'' ∧
        s''.M 1 = [50] ∧ s''.M 2 = [] := by
  obtain ⟨s, s', hs, hstep, hp⟩ := step_of_check xstep (C := exec022_C)
    (o := xrun exec022_C exec022_s0 exec022_race) (l := .ret 0 true)
    (p := fun _ s' => (xrun exec022_C s' [.endPass, .commit 0]).any
      fun s'' => s''.M 1 == [50] && s''.M 2 == []) (by decide)
  refine ⟨s, s', hs, hstep, ?_⟩
  cases h : xrun exec022_C s' [.endPass, .commit 0] with
  | none => simp [h] at hp
  | some s'' =>
    simp only [h, Option.any_some, Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s'', rfl, hp⟩

/-- ✓ The budget may win: from the same race state the expiry is offered, and the timeout
outcome is then deposited (`7` and `8` land in place `2`, the unpublished `50` nowhere). -/
@[evidence allows EXEC_022]
theorem EXEC_022_allows_timeoutFirst :
    ∃ s s', xrun exec022_C exec022_s0 exec022_race = some s ∧
      RefExec exec022_C s (.expire 0 exec022_out) s' ∧
      ∃ s'', xrun exec022_C s' [.endPass, .tdeposit 0] = some s'' ∧
        s''.M 2 = [7, 8] ∧ s''.M 1 = [] := by
  obtain ⟨s, s', hs, hstep, hp⟩ := step_of_check xstep (C := exec022_C)
    (o := xrun exec022_C exec022_s0 exec022_race) (l := .expire 0 exec022_out)
    (p := fun _ s' => (xrun exec022_C s' [.endPass, .tdeposit 0]).any
      fun s'' => s''.M 2 == [7, 8] && s''.M 1 == []) (by decide)
  refine ⟨s, s', hs, hstep, ?_⟩
  cases h : xrun exec022_C s' [.endPass, .tdeposit 0] with
  | none => simp [h] at hp
  | some s'' =>
    simp only [h, Option.any_some, Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s'', rfl, hp⟩

/-! ### Every line exercised -/

/-- Read a decided check off a reference trace: the run exists and the check holds of it. -/
theorem exec022_xtrace_of_check {C : Cfg Nat Nat} {s : XSt Nat Nat} {ls : List (XLbl Nat Nat)}
    {p : List (XStep Nat Nat) → Bool} (h : (xtrace C s ls).map p = some true) :
    ∃ tr, XRun RefExec C s tr ∧ p tr = true := by
  cases ht : xtrace C s ls with
  | none => simp [ht] at h
  | some tr =>
    simp only [ht, Option.map_some, Option.some.injEq] at h
    exact ⟨tr, xtrace_run ht, h⟩

/-- Every line of EXEC-022 is exercised by the reference: the expiry of the asynchronous firing
records `[7, 8]` forwarded to `2`, under a configuration that meets line 1's premise (lines 1
and 2, AC3); its timeout deposit puts `7` then `8` in place `2` and leaves place `1`, which the
action wrote `50` to, empty (lines 2 and 3, AC3, AC4, the test derivation); a flush step of the
firing exists while it is open (the trigger of line 4), and after the expiry the firing holds the
timeout outcome across the next step (the premise of line 4 and the frame of line 5); a run with
the expiry and the timeout deposit (the triggers of lines 6 and 8) and a run with a return of the
open firing and its commit (the trigger of line 7) exist. -/
@[evidence nonvacuous EXEC_022]
theorem EXEC_022_nonvacuous :
    exec022_OutcomeSound exec022_C ∧
    (∃ s s', RefExec exec022_C s (.expire 0 exec022_out) s') ∧
    (∃ s s', RefExec exec022_C s (.tdeposit 0) s' ∧ s'.M 2 = [7, 8] ∧ s'.M 1 = [] ∧
      s'.M 0 = []) ∧
    (∃ s s', RefExec exec022_C s (.flush 0) s' ∧ s'.pq.length = s.pq.length + 1) ∧
    (∃ s s', RefExec exec022_C s .endPass s' ∧
      exec022_Recorded (.timedOut exec022_out) 0 s ∧
      exec022_Recorded (.timedOut exec022_out) 0 s') ∧
    (∃ tr, XRun RefExec exec022_C exec022_s0 tr ∧ tr.any (exec022_isExpire 0) = true ∧
      tr.any (exec022_isTDeposit 0) = true) ∧
    (∃ tr, XRun RefExec exec022_C exec022_s0 tr ∧ tr.any (exec022_isOpenReturn 0) = true ∧
      tr.any (exec022_isCommit 0) = true) := by
  refine ⟨exec022_cfg_sound _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨s, s', -, hs, -⟩ := step_of_check xstep (C := exec022_C)
      (o := xrun exec022_C exec022_s0 exec022_race) (l := .expire 0 exec022_out)
      (p := fun _ _ => true) (by decide)
    exact ⟨s, s', hs⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := exec022_C)
      (o := xrun exec022_C exec022_s0 (exec022_expired ++ [.endPass]))
      (l := .tdeposit 0)
      (p := fun _ s' => s'.M 2 == [7, 8] && s'.M 1 == [] && s'.M 0 == []) (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', hs, hp.1.1, hp.1.2, hp.2⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := exec022_C)
      (o := xrun exec022_C exec022_s0 exec022_race) (l := .flush 0)
      (p := fun s s' => s'.pq.length == s.pq.length + 1) (by decide)
    exact ⟨s, s', hs, by simpa using hp⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := exec022_C)
      (o := xrun exec022_C exec022_s0 exec022_expired) (l := .endPass)
      (p := fun s s' => (decide (0 < s.nextId) && exec022_all0 s exec022_isOutB) &&
        (decide (0 < s'.nextId) && exec022_all0 s' exec022_isOutB)) (by decide)
    rw [Bool.and_eq_true] at hp
    exact ⟨s, s', hs, exec022_recorded_of hp.1, exec022_recorded_of hp.2⟩
  · obtain ⟨tr, hr, hp⟩ := exec022_xtrace_of_check (C := exec022_C) (s := exec022_s0)
      (ls := exec022_expired ++ [.endPass, .tdeposit 0])
      (p := fun tr => tr.any (exec022_isExpire 0) && tr.any (exec022_isTDeposit 0)) (by decide)
    rw [Bool.and_eq_true] at hp
    exact ⟨tr, hr, hp.1, hp.2⟩
  · obtain ⟨tr, hr, hp⟩ := exec022_xtrace_of_check (C := exec022_C) (s := exec022_s0)
      (ls := exec022_race ++ [.ret 0 true, .endPass, .commit 0])
      (p := fun tr => tr.any (exec022_isOpenReturn 0) && tr.any (exec022_isCommit 0))
      (by decide)
    rw [Bool.and_eq_true] at hp
    exact ⟨tr, hr, hp.1, hp.2⟩


/-! ### Decided runs of a step function -/

section Runs

variable {N T : Type}

/-- The trace of a label run of step function `g`, if every label is a step. -/
def exec022_trace (g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)) (C : Cfg N T) :
    XSt N T → List (XLbl N T) → Option (List (XStep N T))
  | _, [] => some []
  | s, l :: ls => (g C s l).bind fun s' => (exec022_trace g C s' ls).map ((s, l, s') :: ·)

/-- A trace `exec022_trace` builds is a run of the graph of `g`. -/
theorem exec022_trace_run {g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)} {C : Cfg N T} :
    ∀ {s : XSt N T} {ls : List (XLbl N T)} {tr : List (XStep N T)},
      exec022_trace g C s ls = some tr → XRun (fun C s l s' => g C s l = some s') C s tr
  | s, [], tr, h => by cases h; trivial
  | s, l :: ls, tr, h => by
    simp only [exec022_trace] at h
    cases hs : g C s l with
    | none => simp [hs] at h
    | some s' =>
      simp only [hs, Option.bind_some] at h
      cases ht : exec022_trace g C s' ls with
      | none => simp [ht] at h
      | some tr' =>
        simp only [ht, Option.map_some, Option.some.injEq] at h
        subst h
        exact ⟨rfl, hs, exec022_trace_run ht⟩

/-- Read a decided check `p` off the trace of a label run: the run exists and `p` holds of it. -/
theorem exec022_trace_of_check {g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)}
    {C : Cfg N T} {s : XSt N T} {ls : List (XLbl N T)} {p : List (XStep N T) → Bool}
    (h : (exec022_trace g C s ls).map p = some true) :
    ∃ tr, XRun (fun C s l s' => g C s l = some s') C s tr ∧ p tr = true := by
  cases ht : exec022_trace g C s ls with
  | none => simp [ht] at h
  | some tr =>
    simp only [ht, Option.map_some, Option.some.injEq] at h
    exact ⟨tr, exec022_trace_run ht, h⟩

/-- A run of the graph of `g`, from a state whose identities were handed out, on which a commit
of `i` follows the expiry of `i`, refutes EXEC-022 (line 6) for that executor. -/
theorem exec022_refuteAbandon [DecidableEq N]
    {g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)} {C : Cfg N T} {s : XSt N T}
    {ls : List (XLbl N T)} {i : Nat} (hs : IdsIssued s)
    (h : (exec022_trace g C s ls).map
      (fun tr => !(afterNever (exec022_isExpire i) (exec022_isCommit i)).scan false tr) =
        some true) :
    ¬ EXEC_022 (fun C s l s' => g C s l = some s') := by
  intro hR
  obtain ⟨tr, hr, hp⟩ := exec022_trace_of_check h
  have : (afterNever (exec022_isExpire i) (exec022_isCommit i)).scan false tr = true :=
    (hR C i).2.2.2.2.2.1 s tr hs hr
  simp [this] at hp

/-- A run of the graph of `g`, from a state whose identities were handed out, on which an expiry
or a timeout deposit of `i` follows a return of `i` taken while `i` was open, refutes EXEC-022
(line 7) for that executor. -/
theorem exec022_refuteAfterReturn [DecidableEq N]
    {g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)} {C : Cfg N T} {s : XSt N T}
    {ls : List (XLbl N T)} {i : Nat} (hs : IdsIssued s)
    (h : (exec022_trace g C s ls).map
      (fun tr => !(afterNever (exec022_isOpenReturn i) (exec022_isTimeout i)).scan false tr) =
        some true) :
    ¬ EXEC_022 (fun C s l s' => g C s l = some s') := by
  intro hR
  obtain ⟨tr, hr, hp⟩ := exec022_trace_of_check h
  have : (afterNever (exec022_isOpenReturn i) (exec022_isTimeout i)).scan false tr = true :=
    (hR C i).2.2.2.2.2.2.1 s tr hs hr
  simp [this] at hp

/-- A run of the graph of `g`, from a state whose identities were handed out, on which a settle
of `i` follows the timeout deposit of `i`, refutes EXEC-022 (line 8) for that executor. -/
theorem exec022_refuteResettle [DecidableEq N]
    {g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)} {C : Cfg N T} {s : XSt N T}
    {ls : List (XLbl N T)} {i : Nat} (hs : IdsIssued s)
    (h : (exec022_trace g C s ls).map
      (fun tr => !(afterNever (exec022_isTDeposit i) (exec022_isSettle i)).scan false tr) =
        some true) :
    ¬ EXEC_022 (fun C s l s' => g C s l = some s') := by
  intro hR
  obtain ⟨tr, hr, hp⟩ := exec022_trace_of_check h
  have : (afterNever (exec022_isTDeposit i) (exec022_isSettle i)).scan false tr = true :=
    (hR C i).2.2.2.2.2.2.2 s tr hs hr
  simp [this] at hp

end Runs

/-! ### Wrong expiry rules -/

/-- The expiry rule with its guards as switches: `opn` (the firing's action has not reported),
`async` (the firing is not synchronous), `node` (its output spec has a `Timeout` node), and the
outcome check `out`. With every switch on and `out = C.timeoutOut` it is the reference rule. -/
def exec022_expireW {N T : Type} [DecidableEq N] (opn async node : Bool)
    (out : Trans N → QDelivered N T → List (N × T) → Bool) (s : XSt N T) (i : Nat)
    (e : List (N × T)) : Option (XSt N T) :=
  match s.fl.find? (·.id == i) with
  | some f =>
    if (!opn || f.out.isNone) && (!async || !f.sync) && (!node || hasTimeoutB f.t) &&
        out f.t f.deliv e then
      some { s with cq := s.cq ++ [i], parked := false,
                    fl := updFiring s i fun g =>
                      { g with out := some (if g.relayBad then .err else .timedOut e) } }
    else none
  | none => none

/-- The reference executor with the expiry rule `exec022_expireW opn async node (out C)`. -/
def exec022_expireMut {N T : Type} [DecidableEq N] (opn async node : Bool)
    (out : Cfg N T → Trans N → QDelivered N T → List (N × T) → Bool) (C : Cfg N T)
    (s : XSt N T) : XLbl N T → Option (XSt N T)
  | .expire i e => exec022_expireW opn async node (out C) s i e
  | l => xstep C s l

/-- The example configuration for `t` with a timeout-outcome check that accepts every outcome:
not sound (`exec022_OutcomeSound` fails), so only line 1's guards, not its outcome, read it. -/
def exec022_Cany (t : Trans Nat) : Cfg Nat Nat :=
  { exec022_cfg t with timeoutOut := fun _ _ _ => true }

/-- ✗ A timeout of a synchronous firing violates EXEC-022 (line 1, the first shall sentence):
`t` starts synchronously, and the expiry rule without the `sync` guard ends it with its timeout
outcome while the pass waits for its action. The configuration's timeout-outcome check accepts
every outcome, so the guard binds whatever the configuration. -/
@[evidence forbids EXEC_022]
theorem EXEC_022_forbids_syncTimeout :
    ¬ EXEC_022 (N := Nat) (T := Nat)
      (fun C s l s' => exec022_expireMut true false true (·.timeoutOut) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check (exec022_expireMut true false true (·.timeoutOut))
    (C := exec022_Cany (exec022_t exec022_spec))
    (o := xrun (exec022_Cany (exec022_t exec022_spec)) exec022_s0 (exec022_pre true))
    (l := .expire 0 exec022_out) (p := fun s _ => exec022_all0 s (·.sync)) (by decide)
  obtain ⟨f, hf, hid, -, hsy, -⟩ := (h (exec022_Cany (exec022_t exec022_spec)) 0).1 _ s s' hs
  have := exec022_of_all0 hp hf hid
  simp [hsy] at this

/-- ✗ A timeout of a transition without a `Timeout` node violates EXEC-022 (line 1, the first
shall sentence): `t` has the output spec `Place(1)`, and the expiry rule without the node guard
and the outcome check ends its asynchronous firing with an empty timeout outcome. The
configuration's timeout-outcome check accepts every outcome, so the guard binds whatever the
configuration. -/
@[evidence forbids EXEC_022]
theorem EXEC_022_forbids_noTimeoutNode :
    ¬ EXEC_022 (N := Nat) (T := Nat)
      (fun C s l s' => exec022_expireMut true true false (fun _ _ _ _ => true) C s l =
        some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check (exec022_expireMut true true false
      (fun _ _ _ _ => true)) (C := exec022_Cany (exec022_t (.place 1)))
    (o := xrun (exec022_Cany (exec022_t (.place 1))) exec022_s0 (exec022_pre false))
    (l := .expire 0 [])
    (p := fun s _ => exec022_all0 s fun f => !hasTimeoutB f.t) (by decide)
  obtain ⟨f, hf, hid, -, -, hT, -⟩ := (h (exec022_Cany (exec022_t (.place 1))) 0).1 _ s s' hs
  have := exec022_of_all0 hp hf hid
  simp [hT] at this

/-- The `Timeout` child, if it is a `ForwardInput`, as its two places. -/
def exec022_fwdOf (t : Trans Nat) : Option (Nat × Nat) :=
  match t.out.bind Out.findTimeout with
  | some (.forward src dst) => some (src, dst)
  | _ => none

/-- An outcome check that forwards only the first consumed token. -/
def exec022_firstOnly (t : Trans Nat) (δ : QDelivered Nat Nat) (e : List (Nat × Nat)) : Bool :=
  match exec022_fwdOf t with
  | some (src, dst) => e == ((δ.inputs src).take 1).map fun x => (dst, x)
  | none => false

/-- With the `Timeout` child `ForwardInput(0, 2)` and the consumed tokens `7` and `8`, forwarding
`7` alone is not the timeout outcome. -/
theorem exec022_firstOnly_not {t : Trans Nat} {δ : QDelivered Nat Nat}
    (ht : exec022_fwdOf t = some (0, 2)) (hδ : δ.inputs 0 = [7, 8]) :
    ¬ exec022_QOutcome t δ [(2, 7)] := by
  rintro ⟨o, c, e₀, ho, hc, hem, hp⟩
  unfold exec022_fwdOf at ht
  rw [ho, Option.bind_some, hc] at ht
  cases c with
  | forward src dst =>
    simp only [Option.some.injEq, Prod.mk.injEq] at ht
    obtain ⟨rfl, rfl⟩ := ht
    simp only [exec022_Emits, hδ] at hem
    subst hem
    have := hp 2
    simp [qEmittedTo] at this
  | place _ => simp at ht
  | and _ _ => simp at ht
  | xor _ _ => simp at ht
  | timeout _ => simp at ht

/-- ✗ Forwarding only the first consumed token violates EXEC-022 (line 1, AC3): the firing
consumed `7` and `8`, and the expiry records `7` alone in place `2`. -/
@[evidence forbids EXEC_022]
theorem EXEC_022_forbids_forwardFirst :
    ¬ EXEC_022 (N := Nat) (T := Nat)
      (fun C s l s' => exec022_expireMut true true true (fun _ => exec022_firstOnly) C s l =
        some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check (exec022_expireMut true true true
      (fun _ => exec022_firstOnly)) (C := exec022_C)
    (o := xrun exec022_C exec022_s0 exec022_race) (l := .expire 0 [(2, 7)])
    (p := fun s _ => exec022_all0 s fun f =>
      exec022_fwdOf f.t == some (0, 2) && f.deliv.inputs 0 == [7, 8]) (by decide)
  obtain ⟨f, hf, hid, -, -, -, hq⟩ := (h exec022_C 0).1 _ s s' hs
  have := exec022_of_all0 hp hf hid
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact exec022_firstOnly_not this.1 this.2 (hq (exec022_cfg_sound _))

/-- ✗ A timeout after the return violates EXEC-022 (line 7, the third shall sentence): the
action returns, and the expiry rule without the `opn` guard still ends the firing with its
timeout outcome. -/
@[evidence forbids EXEC_022]
theorem EXEC_022_forbids_timeoutAfterReturn :
    ¬ EXEC_022 (N := Nat) (T := Nat)
      (fun C s l s' => exec022_expireMut false true true (·.timeoutOut) C s l = some s') :=
  exec022_refuteAfterReturn (C := exec022_C) (i := 0) exec022_s0_issued
    (ls := exec022_race ++ [.ret 0 true, .expire 0 exec022_out]) (by decide)

/-! ### Violation: publishing the unpublished output at the timeout -/

/-- A step function whose expiry also queues what the action had written and not published, as a
publication; otherwise the reference. -/
def exec022_flushAtTimeoutStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .expire i e => (xstep C s (.expire i e)).map fun s₁ =>
      match s.fl.find? (·.id == i) with
      | some f => { s₁ with pq := s₁.pq ++ [(i, f.buf)] }
      | none => s₁
  | l => xstep C s l

/-- ✗ Publishing the unpublished output at the timeout violates EXEC-022 (line 2, the seventh
shall sentence, AC4): the action wrote `50` to place `1`, and the expiry queues it. -/
@[evidence forbids EXEC_022]
theorem EXEC_022_forbids_flushAtTimeout :
    ¬ EXEC_022 (N := Nat) (T := Nat)
      (fun C s l s' => exec022_flushAtTimeoutStep C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec022_flushAtTimeoutStep (C := exec022_C)
    (o := xrun exec022_C exec022_s0 exec022_race) (l := .expire 0 exec022_out)
    (p := fun s s' => s'.pq.length != s.pq.length) (by decide)
  have := ((h exec022_C 0).2.1 _ s s' hs).2.1
  simp [this] at hp

/-! ### Violation: recording the unpublished output with the timeout outcome -/

/-- A step function whose expiry announces `e` but records the action's unpublished writes
followed by `e` (the timeout branch produced before `context.detachForTimeout()`, or without it);
otherwise the reference. -/
def exec022_mergeAtExpiryStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .expire i e => (xstep C s (.expire i e)).map fun s₁ =>
      { s₁ with fl := updFiring s i fun g =>
          { g with out := some (if g.relayBad then .err else .timedOut (g.buf ++ e)) } }
  | l => xstep C s l

/-- ✗ Recording the unpublished output with the timeout outcome violates EXEC-022 (line 2, the
fifth shall sentence, AC4): the expiry announces `[7, 8]` forwarded to `2`, and the firing
records `50` for place `1` with it, which the timeout deposit then puts in place `1`. -/
@[evidence forbids EXEC_022]
theorem EXEC_022_forbids_mergeAtExpiry :
    ¬ EXEC_022 (N := Nat) (T := Nat)
      (fun C s l s' => exec022_mergeAtExpiryStep C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec022_mergeAtExpiryStep (C := exec022_C)
    (o := xrun exec022_C exec022_s0 exec022_race) (l := .expire 0 exec022_out)
    (p := fun _ s' => s'.fl.any fun f => f.id == 0 && !f.relayBad && !exec022_isOutB f)
    (by decide)
  obtain ⟨f, hf, hp⟩ := List.any_eq_true.mp hp
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hp
  obtain ⟨⟨hid, hrb⟩, hne⟩ := hp
  have hrec := ((h exec022_C 0).2.1 _ s s' hs).2.2 f hf hid
  rw [hrb, if_neg Bool.false_ne_true] at hrec
  rw [exec022_isOutB_iff.mpr hrec] at hne
  exact absurd hne (by decide)

/-! ### Violation: depositing the timeout outcome of a relay-rejected firing -/

/-- A step function whose expiry records the timeout outcome even on a firing whose flushed batch
the join-relay check rejected (the Rust relay slot read in the action's arm only); otherwise the
reference. -/
def exec022_relayIgnoredStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .expire i e => (xstep C s (.expire i e)).map fun s₁ =>
      { s₁ with fl := updFiring s i fun g => { g with out := some (.timedOut e) } }
  | l => xstep C s l

/-- ✗ Ignoring a relay rejection at the expiry violates EXEC-022 (line 2, NU-054 read at the
expiry, the D24 (a) sentence): the action flushes `50` for place `1`, the relay check rejects the
batch, and the expiry still records the timeout outcome, which the timeout deposit puts in place
`2`. -/
@[evidence forbids EXEC_022]
theorem EXEC_022_forbids_relayIgnoredAtExpiry :
    ¬ EXEC_022 (N := Nat) (T := Nat)
      (fun C s l s' => exec022_relayIgnoredStep C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec022_relayIgnoredStep (C := exec022_Crelay)
    (o := xrun exec022_Crelay exec022_s0 (exec022_race ++ [.flush 0]))
    (l := .expire 0 exec022_out)
    (p := fun _ s' => s'.fl.any fun f => f.id == 0 && f.relayBad &&
      (match f.out with | some .err => false | _ => true)) (by decide)
  obtain ⟨f, hf, hp⟩ := List.any_eq_true.mp hp
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨hid, hrb⟩, hne⟩ := hp
  have hrec := ((h exec022_Crelay 0).2.1 _ s s' hs).2.2 f hf hid
  rw [hrb, if_pos rfl] at hrec
  rw [hrec] at hne
  exact absurd hne Bool.false_ne_true

/-! ### Violation: merging the unpublished output into the timeout deposit -/

/-- A step function whose timeout deposit also deposits what the action had written and not
published; otherwise the reference. -/
def exec022_mergeStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .tdeposit i => (xstep C s (.tdeposit i)).bind fun s₁ =>
      (s.fl.find? (·.id == i)).map fun f => { s₁ with M := qAppend s₁.M f.buf }
  | l => xstep C s l

/-- ✗ Merging the unpublished output into the timeout deposit violates EXEC-022 (line 3, the
sixth shall sentence, AC4): the action wrote `50` to place `1`, and the timeout deposit puts it
there together with the forwarded `7` and `8`. -/
@[evidence forbids EXEC_022]
theorem EXEC_022_forbids_merge :
    ¬ EXEC_022 (N := Nat) (T := Nat) (fun C s l s' => exec022_mergeStep C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec022_mergeStep (C := exec022_C)
    (o := xrun exec022_C exec022_s0 (exec022_expired ++ [.endPass]))
    (l := .tdeposit 0)
    (p := fun s s' => exec022_all0 s fun f => match f.out with
      | some (.timedOut e) => qAppend s.M e 1 != s'.M 1
      | _ => true) (by decide)
  obtain ⟨f, hf, hid, e, he, hM⟩ := (h exec022_C 0).2.2.1 s s' hs
  have := exec022_of_all0 hp hf hid
  rw [he] at this
  simp [hM] at this

/-! ### Violation: publishing a late flush of an abandoned action -/

/-- A step function whose flush does not check whether its firing has ended: a flush of a
firing that holds an outcome still queues the buffer; otherwise the reference. -/
def exec022_lateFlushStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .flush i =>
    match s.fl.find? (·.id == i) with
    | some f =>
      if f.out.isSome && !f.sync && !f.buf.isEmpty then
        some { s with pq := s.pq ++ [(i, f.buf)], parked := false,
                      fl := updFiring s i fun g =>
                        { g with buf := [], pub := g.pub ++ g.buf.map Prod.fst } }
      else xstep C s (.flush i)
    | none => none
  | l => xstep C s l

/-- ✗ Publishing a late flush of an abandoned action violates EXEC-022 (line 4, the seventh
shall sentence): the budget runs out, the action, which the runtime could not stop, flushes the
`50` it wrote for place `1`, and the flush queues it. -/
@[evidence forbids EXEC_022]
theorem EXEC_022_forbids_lateFlush :
    ¬ EXEC_022 (N := Nat) (T := Nat) (fun C s l s' => exec022_lateFlushStep C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec022_lateFlushStep (C := exec022_C)
    (o := xrun exec022_C exec022_s0 exec022_expired) (l := .flush 0)
    (p := fun s s' => exec022_all0 s exec022_isTOB && s'.pq.length != s.pq.length) (by decide)
  simp only [Bool.and_eq_true] at hp
  have := ((h exec022_C 0).2.2.2.1 s s' hs fun f hf hid =>
    exec022_of_isTOB (exec022_of_all0 hp.1 hf hid)).2
  simp [this] at hp

/-! ### Violation: a late error of the abandoned action replaces the timeout outcome -/

/-- A step function whose return, on a firing that already holds a timeout outcome, replaces it
by an error when the action fails late (TypeScript: a rejection handler on the action's own
promise next to the race; Java: `exceptionally` on `actionFuture` instead of on its timed copy);
otherwise the reference. -/
def exec022_lateErrorStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .ret i ok =>
    match retStep s i ok with
    | some s' => some s'
    | none =>
      match s.fl.find? (·.id == i) with
      | some f =>
        match f.out, ok with
        | some (.timedOut _), false =>
          some { s with parked := false,
                        fl := updFiring s i fun g => { g with out := some .err } }
        | _, _ => none
      | none => none
  | l => xstep C s l

/-- ✗ Letting a late error replace the timeout outcome violates EXEC-022 (line 5, the fourth
shall sentence, AC3): the budget runs out with `7` and `8` forwarded to place `2`, the abandoned
action then fails, and the firing now holds an error, so it fails and `7` and `8` are lost. -/
@[evidence forbids EXEC_022]
theorem EXEC_022_forbids_lateError :
    ¬ EXEC_022 (N := Nat) (T := Nat) (fun C s l s' => exec022_lateErrorStep C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec022_lateErrorStep (C := exec022_C)
    (o := xrun exec022_C exec022_s0 exec022_expired) (l := .ret 0 false)
    (p := fun s s' => (decide (0 < s.nextId) && exec022_all0 s exec022_isOutB) &&
      s'.fl.any fun f => f.id == 0 && !exec022_isOutB f) (by decide)
  rw [Bool.and_eq_true] at hp
  have hrec := ((h exec022_C 0).2.2.2.2.1 _ s s' hs).1 _ (exec022_recorded_of hp.1)
  obtain ⟨f, hf, hp⟩ := List.any_eq_true.mp hp.2
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hp
  rw [exec022_isOutB_iff.mpr (hrec.2 f hf hp.1)] at hp
  exact absurd hp.2 (by decide)

/-! ### Violation: a budget timed on the firing clock -/

/-- A step function that times the budget on the firing clock ([TIME-015] says it must not): a
delay step ends every open asynchronous firing whose spec has a `Timeout` node with a timeout
outcome, without an expiry; otherwise the reference. -/
def exec022_clockStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .delay δ =>
    let due := fun g : Firing N T => g.out.isNone && !g.sync && hasTimeoutB g.t
    some { s with now := s.now + δ, cq := s.cq ++ (s.fl.filter due).map (·.id),
                  fl := s.fl.map fun g => if due g then { g with out := some (.timedOut []) }
                                          else g }
  | l => xstep C s l

/-- ✗ Ending a firing with a timeout outcome on a delay step violates EXEC-022 (line 5, the
second shall sentence in its step form, [TIME-015]): the firing is open, time passes on the
firing clock, and the firing now holds a timeout outcome without an expiry. -/
@[evidence forbids EXEC_022]
theorem EXEC_022_forbids_clockTimeout :
    ¬ EXEC_022 (N := Nat) (T := Nat) (fun C s l s' => exec022_clockStep C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec022_clockStep (C := exec022_C)
    (o := xrun exec022_C exec022_s0 exec022_race) (l := .delay 1)
    (p := fun s s' => exec022_all0 s (·.out.isNone) &&
      s'.fl.any fun f => f.id == 0 && exec022_isTOB f) (by decide)
  rw [Bool.and_eq_true] at hp
  obtain ⟨f, hf, hq⟩ := List.any_eq_true.mp hp.2
  simp only [Bool.and_eq_true, beq_iff_eq] at hq
  obtain ⟨e, he⟩ := exec022_of_isTOB hq.2
  rcases ((h exec022_C 0).2.2.2.2.1 _ s s' hs).2 f hf hq.1 e he with ⟨g, hg, hgid, hgo⟩ | ⟨_, hl⟩
  · have := exec022_of_all0 hp.1 hg hgid
    rw [hgo] at this
    exact absurd this Bool.false_ne_true
  · cases hl

/-! ### Violation: an action error read as the budget's timeout -/

/-- A step function whose return reads an action error on a transition with a `Timeout` node as
the budget's timeout (Java: an action whose own future fails with a `TimeoutException` taken for
the budget's), recording a timeout outcome; otherwise the reference. -/
def exec022_errorAsTimeoutStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .ret i ok => (retStep s i ok).map fun s₁ =>
      if !ok && (s.fl.find? (·.id == i)).any (fun f => hasTimeoutB f.t) then
        { s₁ with fl := updFiring s₁ i fun g => { g with out := some (.timedOut []) } }
      else s₁
  | l => xstep C s l

/-- ✗ Reading an action error as the budget's timeout violates EXEC-022 (line 7, the third shall
sentence): the action fails before the budget runs out, and the executor deposits a timeout
outcome. -/
@[evidence forbids EXEC_022]
theorem EXEC_022_forbids_errorAsTimeout :
    ¬ EXEC_022 (N := Nat) (T := Nat)
      (fun C s l s' => exec022_errorAsTimeoutStep C s l = some s') :=
  exec022_refuteAfterReturn (C := exec022_C) (i := 0) exec022_s0_issued
    (ls := exec022_race ++ [.ret 0 false, .endPass, .tdeposit 0]) (by decide)

/-! ### Violation: committing the completion of an abandoned action -/

/-- A step function that accepts the return of an action whose budget has already run out,
replacing the timeout outcome by the completion; otherwise the reference. -/
def exec022_lateCompletionStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .ret i ok =>
    match s.fl.find? (·.id == i) with
    | some _ =>
      some { s with cq := s.cq ++ [i], parked := false,
                    fl := updFiring s i fun g =>
                      { g with out := some (if ok && !g.relayBad then .ok g.buf else .err) } }
    | none => none
  | l => xstep C s l

/-- ✗ Committing the completion of an abandoned action violates EXEC-022 (line 6, the seventh
shall sentence): the budget runs out, the action returns late with `50` for place `1`, and its
completion is committed. -/
@[evidence forbids EXEC_022]
theorem EXEC_022_forbids_lateCompletion :
    ¬ EXEC_022 (N := Nat) (T := Nat)
      (fun C s l s' => exec022_lateCompletionStep C s l = some s') :=
  exec022_refuteAbandon (C := exec022_C) (i := 0) exec022_s0_issued
    (ls := exec022_expired ++ [.ret 0 true, .endPass, .commit 0]) (by decide)

/-! ### Violation: depositing the timeout outcome twice -/

/-- A step function whose timeout deposit leaves the firing in flight and its queue entry in
place; otherwise the reference. -/
def exec022_doubleDepositStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .tdeposit i => (xstep C s (.tdeposit i)).map fun s₁ => { s₁ with fl := s.fl, cq := s.cq }
  | l => xstep C s l

/-- ✗ Depositing the timeout outcome twice violates EXEC-022 (line 8, the sixth shall
sentence): the firing stays in flight after its timeout deposit, and a second deposit puts `7`
and `8` in place `2` again. -/
@[evidence forbids EXEC_022]
theorem EXEC_022_forbids_doubleDeposit :
    ¬ EXEC_022 (N := Nat) (T := Nat)
      (fun C s l s' => exec022_doubleDepositStep C s l = some s') :=
  exec022_refuteResettle (C := exec022_C) (i := 0) exec022_s0_issued
    (ls := exec022_expired ++ [.endPass, .tdeposit 0, .tdeposit 0]) (by decide)

end Libpetri.Spec
