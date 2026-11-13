import Libpetri.Spec.Req.EXEC_022
import Libpetri.Spec.Req.NU_054

set_option linter.missingDocs true

/-!
# NU-054: the failure of a firing the relay check rejects (`spec/12-nu-nets.md`)

The fourth block of NU-054, beside `NU_054_build`, `NU_054_check` and `NU_054_verifier`
(`NU_054.lean`). `NU_054_check` says which firings exist: a completion whose tokens in a relay
target do not all project to the chosen name is no firing of the ν firing relation. This block
says what the executor does with such a completion instead, on the executor model `RefExec`
(`Reference/Exec.lean`): it fails the firing, deposits none of the rejected output or timeout
outcome, keeps the batches published before (ruling D17), checks a batch published mid-action
when it is published, never deposits a refused batch later (only a flush queues, and a publish
deposits only what is queued), and fails a firing one of whose batches was refused.

**The ν side.** The executor reads the relay check from its configuration (`Cfg.relay`, "part of
output validation"). This block fixes that check to NU-054's: `relayVerdict mt cn` reads, for a
transition `t`, its match `mt t` and the chosen name `cn t δ` of a firing that delivered `δ`, and
accepts an emission exactly when every token it puts on a relay target projects to that name
(`relayVerdict_iff`, `nu054f_relayPass_iff` for the bridge to `RelayOk`). The block quantifies over
every `mt` and `cn`: it does not depend on how the start chose the name. A configuration whose
relay check is `relayVerdict mt cn` is one with output validation on ([CONC-026]). No consistency
theorem ties `mt` and `cn` to the net's matches yet (an open item).

Evidence: the reference (`NU_054_fail_reference`), a worked example on the join `j1` of AC4
(`NU_054_fail_nonvacuous`), and nine wrong executors, at least one per line: a commit without the
check (line 1), a timeout deposit without the check (line 2), a failure that deposits the
conforming part and one that withdraws a queued batch (line 3), a flush without the check and one
that deposits at once (line 4), a flush that drops the bad batch but lets the firing complete
(line 5, Rust's "recording it and returning `Ok`"), a publish of a batch never queued (line 6),
and a return that queues the action's output unchecked (line 7).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## Vocabulary -/

section Terms

variable {N V Nm : Type} [DecidableEq N] [DecidableEq Nm]

/-- **The NU-054 relay verdict** as a configuration's join-relay check (`Cfg.relay`): for a
transition `t` with match `mt t` and a firing that delivered `δ`, whose chosen name is `cn t δ`,
an emission `e` passes when every token it puts on a relay target has a name under that target's
key projection, and that name is the chosen name. A transition without a match passes
everything. -/
def relayVerdict (mt : Trans N → Option (MatchSpec N (KeyFn V Nm)))
    (cn : Trans N → QDelivered N (Stamped V) → Option Nm) :
    Trans N → QDelivered N (Stamped V) → List (N × Stamped V) → Bool := fun t δ e =>
  match mt t with
  | none => true
  | some ms => ms.relays.all fun r => (qEmittedTo e r.1).all fun x =>
      match cn t δ, r.2 x.val with
      | some n, some m => decide (m = n)
      | _, _ => false

/-- **The relay check passes** for firing `f` and emission `e`: every token `e` puts on a relay
target of `f`'s transition has a name under that target's key projection, and it is the chosen
name of `f`. -/
def RelayPass (mt : Trans N → Option (MatchSpec N (KeyFn V Nm)))
    (cn : Trans N → QDelivered N (Stamped V) → Option Nm) (f : Firing N (Stamped V))
    (e : List (N × Stamped V)) : Prop :=
  ∀ ms, mt f.t = some ms → ∀ r ∈ ms.relays, ∀ x ∈ qEmittedTo e r.1,
    ∃ n, cn f.t f.deliv = some n ∧ r.2 x.val = some n

/-- The verdict accepts exactly what passes the check. -/
theorem relayVerdict_iff {mt : Trans N → Option (MatchSpec N (KeyFn V Nm))}
    {cn : Trans N → QDelivered N (Stamped V) → Option Nm} {f : Firing N (Stamped V)}
    {e : List (N × Stamped V)} :
    relayVerdict mt cn f.t f.deliv e = true ↔ RelayPass mt cn f e := by
  unfold relayVerdict RelayPass
  cases hm : mt f.t with
  | none => simp
  | some ms =>
    simp only [List.all_eq_true, Option.some.injEq, forall_eq']
    refine forall₂_congr fun r _ => forall₂_congr fun x _ => ?_
    cases cn f.t f.deliv <;> cases r.2 x.val <;> simp [eq_comm]

omit [DecidableEq Nm] in
/-- **The bridge to `RelayOk`** ([NU-054]'s check in `NU_054_check`): when the firing's chosen
name is `n`, the check passes exactly when the emission is `RelayOk` for every match of the
transition. -/
theorem nu054f_relayPass_iff {mt : Trans N → Option (MatchSpec N (KeyFn V Nm))}
    {cn : Trans N → QDelivered N (Stamped V) → Option Nm} {f : Firing N (Stamped V)}
    {e : List (N × Stamped V)} {n : Nm} (hn : cn f.t f.deliv = some n) :
    RelayPass mt cn f e ↔ ∀ ms, mt f.t = some ms → RelayOk ms n e := by
  unfold RelayPass RelayOk
  simp only [hn, Option.some.injEq, exists_eq_left']

/-- The chosen name read off a delivery: the projection of the first token the firing took from
its first match key. A firing of a matched transition takes only tokens of the chosen name on its
keys ([NU-021]), so this is the chosen name of every ν firing; the examples use it. -/
def keyName (mt : Trans N → Option (MatchSpec N (KeyFn V Nm))) :
    Trans N → QDelivered N (Stamped V) → Option Nm := fun t δ =>
  (mt t).bind fun ms => ms.keys.head?.bind fun k => (δ.inputs k.1).head?.bind fun x => k.2 x.val

/-- The step is a flush of firing `i` whose batch the relay check rejects: the first firing with
identity `i` holds a buffer that fails `relayVerdict mt cn`. -/
def nu054f_isRefusedFlush (mt : Trans N → Option (MatchSpec N (KeyFn V Nm)))
    (cn : Trans N → QDelivered N (Stamped V) → Option Nm) (i : Nat) :
    XStep N (Stamped V) → Bool
  | (s, .flush j, _) => j == i &&
      match s.fl.find? (·.id == i) with
      | some f => !relayVerdict mt cn f.t f.deliv f.buf
      | none => false
  | _ => false

end Terms

/-- The step deposits the returned output (`commit`) or the timeout outcome (`tdeposit`) of
firing `i`. -/
def nu054f_isDeposit {N T : Type} (i : Nat) : XStep N T → Bool
  | (_, .commit j, _) => j == i
  | (_, .tdeposit j, _) => j == i
  | _ => false

/-! ## The block -/

requirement NU_054_fail
  id "NU-054"
  title "Join Relay (a firing the relay check rejects)"
  kind B
  scope "every executor with output validation on; the settle, flush and failure of a firing of a transition with a match specification"
  source verbatim "spec/12-nu-nets.md"
  quote "*While* output validation is on, *if* the output the action of a transition with a match specification returns, or the timeout outcome of its firing, puts into one of the transition's relay targets a token that has no name, or a name other than the chosen name, under that relay target's key projection, *then* the executor *shall* fail the firing with a TransitionFailed event ([EVT-008]) and *shall* deposit none of the tokens of that output or outcome."
        "*When* the executor fails a firing of a transition with a match specification, it *shall not* deposit any token of the firing's output or timeout outcome, *shall not* restore the tokens the firing consumed, and *shall not* withdraw a batch the action flushed before the firing failed ([IO-015]), whether the executor has already deposited that batch or still holds it queued ([EXEC-021], [CONC-003])."
        "*While* output validation is on, *if* a batch that the action of a transition with a match specification publishes before it completes ([IO-015]) puts into one of the transition's relay targets a token that has no name, or a name other than the chosen name, under that relay target's key projection, *then* the executor *shall not* deposit that batch, *shall* fail the firing, and *shall* deposit neither the output the action returns nor the timeout outcome of the firing."
  reading "For every executor E, every assignment mt of a match to each transition, every reading cn of the chosen name of a firing from what it delivered, every configuration C whose join-relay check is the NU-054 verdict relayVerdict mt cn (output validation on), and every firing identity i:"
          "a commit step of i deposits exactly the output e the action of i returned, each token at the tail of its place, and only when every token e puts on a relay target has a name under that target's key projection and that name is the chosen name of i (RelayPass);"
          "a tdeposit step of i deposits exactly the timeout outcome e firing i recorded, and only when e passes the same check;"
          "a fail step of i changes neither the marking nor the queue of batches published and not yet deposited;"
          "a flush step of i changes no marking, and either leaves the queue of published batches as it was or appends the buffer of a firing i, and then only a buffer that passes the check;"
          "on every run of E from a state in which every firing in flight has an identity the supply has already handed out, no commit or tdeposit step of i comes after a flush step of i whose batch fails the check;"
          "a publish step of i deposits exactly a batch of i that is in the queue of published batches, each token at the tail of its place;"
          "and a step other than a flush of i adds no batch of i to that queue."
  assumes "The model is an executor E : XRel N (Stamped V) (glossary GlossaryExec.lean) over tokens that carry a value and a creation stamp (GlossaryNu.lean, Stamped), the token type of the ν kernel. E C s l s' says that under configuration C the step labelled l leads from executor state s to s'. A firing starts in a firing pass and settles in a later step: commit deposits a returned output, tdeposit a timeout outcome, fail nothing (the settle steps of EXEC-021). The action writes (write), publishes what it wrote (flush, a batch queued in XSt.pq and deposited later by publish, ruling D17) and returns (ret), or its budget runs out (expire). The witness is the reference executor RefExec, checked rule by rule against the Rust executor."
          "The ν side is read through the configuration. The executor consults its join-relay check C.relay (Cfg.relay: 'part of output validation'); the lines fix it to NU-054's check: mt gives each transition its match specification and cn the chosen name of a firing from what its start delivered, and relayVerdict mt cn accepts an emission exactly when every token it puts on a relay target projects to that name (relayVerdict_iff; for a firing whose chosen name is n it is NU_054_check's RelayOk, nu054f_relayPass_iff). The lines hold for every mt and cn, so they do not depend on how the start chose the name: RefExec's start delivers the heads of the input queues (qDelivered), not the correlated take of RefNuFire, and the block needs only the name. Nothing yet ties mt and cn to the net: no consistency theorem states C.relay = relayVerdict (the match each transition carries) keyName on the delivery of a correlated take, so until that link exists the block says that the executor respects whatever relay check of the NU-054 shape its configuration carries (an open item: the link C.relay = relayVerdict in a consistency theorem)."
          "'While output validation is on' is the premise C.relay = relayVerdict mt cn. 'The check is on by default and is skipped only where output validation itself is skipped ([CONC-026])': under the validation skip the relay check accepts everything (Cfg.SkipsValidation). The premise then still holds, but only with a match assignment that gives no transition a match (the check that accepts everything is relayVerdict (fun _ => none) cn), so every RelayPass conjunct is empty, the trigger of line 5 never fires, and what remains is the frame of the settle, flush and publish steps that EXEC-021, EXEC-022 and CONC-003 state for every executor. NU_054_fail_nonvacuous shows the reference depositing a token of another name into a relay target under the skip. Rust checks no relay when skip_output_validation is set: relay_check accepts every output, and fire_transition_async builds no relay guard for a flush (rust/libpetri-runtime/src/executor_core/executor.rs). 'The runtime check is independent of the mode' holds because nothing here reads a fragment mode."
          "Lines 1, 2, 4 and 6 bind every transition, not only one with a match specification: for a transition without a match RelayPass holds trivially, and the lines restate what other blocks state for every executor. A commit deposits exactly the returned output at the tails (CONC-003 line 1, EXEC-020), a tdeposit exactly the timeout outcome (EXEC-022), a flush deposits nothing and queues at most the action's buffer ([IO-015] mid-action publication), and a publish deposits a queued batch (CONC-003 line 2, which also fixes that it is the oldest one). These exact deposits are here so that the relay conjunct reads on the tokens actually deposited, and so that each of the three quoted sentences has its own wrong models in this block."
          "The first quoted sentence is lines 1 and 2: a returned output or a timeout outcome that fails the check is never the emission of a commit or tdeposit step; the steps in which the action writes or returns deposit nothing (EXEC_021's line 4) and, by line 7, hand nothing to the publication queue, so the output cannot reach the marking through a later publish either (NU_054_fail_forbids_retQueues: a return that queues the output unchecked); and the fail step deposits nothing (line 3). Rust runs the check after the output-spec check of a completion and on the timeout path (relay_check, called from handle_completion in executor_core/executor.rs); Java (BitmapNetExecutor.validateOutput, ExecutorSupport.validateRelays) and TypeScript (processCompletedTransitions in bitmap-net-executor.ts, validateRelays in executor-support.ts) run it inside output validation. 'Shall fail the firing' is an offer: that a firing whose returned output or timeout outcome the check rejects is settled by a fail step is the clause ExecFailCovers of the consistency theorem's ExecCoversW5 (refExec_failCovers), not a line (blocks state safety, offers are coverage). The TransitionFailed event is the event the fail label carries (Reference/Events.lean, EVT-008). Its error, 'naming the transition, the place, the matched name and the name found', and the 'no name' error of a projection that throws or of an absent value checked without calling the projection, are message text and failure mechanism (kind N). They are built by relay_check in executor_core/executor.rs and by validateRelays in java/src/main/java/org/libpetri/runtime/ExecutorSupport.java and typescript/src/runtime/executor-support.ts, and pinned by the runtimes' tests: token_of_another_name_fails_the_firing, token_projecting_to_no_name_fails_the_firing and absent_value_has_no_name_and_the_projection_is_not_called in rust/libpetri-runtime/src/nu_relay_tests.rs; nuRelay_wrongNameFailsTheFiring, nuRelay_noNameFailsTheFiring and nuRelay_throwingKeyFunctionIsNoName in AbstractNetExecutorEngineTest; and 'a token of another name fails the firing, naming transition, place and both names', 'a token projecting to no name fails the firing', 'an absent value has no name, and the projection is not called on it' and 'a key function that throws projects no name: the firing fails with the relay error' in typescript/tests/runtime/nu-join-relay.test.ts."
          "The timeout outcome is checked and not validated against the output spec (ruling D24 (a)): line 2 reads the check on every tdeposit step and EXEC_021 forbids validating the outcome. Every runtime runs only the relay check on a timeout outcome (processCompletedTransitions in java/src/main/java/org/libpetri/runtime/BitmapNetExecutor.java, processCompletedTransitions in typescript/src/runtime/bitmap-net-executor.ts, handle_completion in rust/libpetri-runtime/src/executor_core/executor.rs), so a relay violation of a timeout outcome fails the firing in every runtime and And(A, Timeout(d, B)) deposits B on a timeout. An executor that also validated the timeout outcome against the whole output spec, the Java and TypeScript behaviour RD-01 recorded, would fail that firing on every timeout. Clash nu-c#8: a timed-out firing whose timeout outcome writes a unit token, or a forward of another input, into a relay target deposits nothing, where IO-013's sentence says a timed-out firing deposits the tokens of the child. The spec edits of this block add that exception to the text of IO-013 and IO-014 as sentences without shall, so the quotes of IO_013 and IO_014 stay as they are."
          "The second quoted sentence is line 3, read on every fail step whatever its cause ('fails the firing like any other validation failure'; one fail label serves the action's error, the output-spec rejection and the relay rejection). The marking is unchanged, so nothing of the output or outcome is deposited, the consumed tokens stay consumed, and a batch already deposited stays in the marking; the queue of published batches is unchanged, so a batch flushed before the failure and still queued is deposited by its publish step (ruling D17: 'deposits none of the checked batch while tokens of a batch published earlier with ctx.flush() stay'). That no later step withdraws a queued batch either is CONC-003's line 3 (conc003Kept). EXEC_021's line 2 states the same frame for every executor, which the sentence cites; line 3 is here so that the NU-054 reading has its own wrong models: a failure that deposits the conforming part of the output (NU_054_fail_forbids_partialDeposit) and one that withdraws the queued batch (NU_054_fail_forbids_failDropsPub)."
          "The third quoted sentence is lines 4 to 7. 'Shall not deposit that batch' is lines 4, 6 and 7 together: a flush deposits nothing itself and queues only a batch that passes the check (line 4), no other step adds a batch of i to the queue (line 7, together with line 4 for every other identity), and a publish deposits only a batch of i that is queued (line 6), so a refused batch reaches the marking neither at its flush nor later. The wrong models are a flush that deposits at once (NU_054_fail_forbids_flushDeposits), a flush without the check (NU_054_fail_forbids_flushNoGuard), a publish of a batch that was never queued (NU_054_fail_forbids_publishUnqueued) and a return that queues the output (NU_054_fail_forbids_retQueues). 'A batch published mid-action ([IO-015]) is checked when it is published': Rust's flush callback, built in fire_transition_async, checks the batch before it sends it (executor_core/executor.rs). Rust drops every later batch of a firing once one was refused (the callback keeps the refusal in FlushGate.relay_error and refuses each later batch with it); line 4 allows that (the queue stays as it was) and does not require it, since the markdown does not say what happens to a later batch."
          "'Shall fail the firing, and shall deposit neither the output the action returns nor the timeout outcome' is line 5: 'In Rust, a relay violation found while flushing a mid-action batch makes ctx.flush() return Err carrying the relay message, rather than recording it and returning Ok; the firing then fails as it does for a violation found at completion.' After a refused flush of i, no commit or tdeposit of i follows in the run, so the firing, if it is settled at all, is settled by a fail step; NU_054_fail_forbids_recordOk is the executor that drops the batch and lets the firing complete. The trigger is a flush whose batch fails relayVerdict mt cn, which rejects only on a transition with a match, as the sentence says; in the model the relay check is the only thing that refuses a non-empty batch an open asynchronous firing flushes (flushStep). That the fail step is then offered is coverage, not a line. On the reference it is ExecFailCovers: the reference records an error at the return or expiry of a firing marked relayBad (in Rust the task of fire_transition_async takes FlushGate.relay_error as the firing's error, executor_core/executor.rs), and ExecFailCovers offers fail for an error. ExecFailCovers has no disjunct for a firing whose batch was refused, so for another executor the offer follows only jointly: CONC_010 queues its return, a commit or tdeposit of a passing outcome is what ValidatedBy and Exec022Covers would offer and line 5 forbids, and no clause forces a refusing flush to record the error (an open item: a relayBad disjunct of ExecFailCovers). That ctx.flush() returns Err to the action, with the relay message, is the action-side API of Rust (kind N): the model's flush step hands nothing back to the action. Java and TypeScript have no mid-action publication (IO-015's flush is Rust's and Python's), so lines 4 to 7 hold there with no flush step and no publish step."
          "Line 5 identifies the firing by its identity. Identities are drawn once from one supply (XSt.nextId); the premise IdsIssued says every firing in flight at the start of the run has an identity the supply has already handed out, true at the start of every run and kept by every reference step (exec022_idsIssued_step), as in EXEC_022's trace lines. The trigger reads the first firing with identity i, which is the one every reference rule acts on. The block does not require E to draw fresh identities, so line 5 also binds a later firing that reused identity i; no runtime and not the reference reuses one."
          "'The relay check runs before the multiplicity diagnostic of [IO-016] AC4, in both executor backends of every language, so a firing that both violates the relay contract and over-writes a place fails with the relay error and emits no multiplicity WARN': the reference event model emits no multiplicity WARN yet (Reference/Events.lean, 'Not emitted by the reference yet'), so the order is test evidence (kind Q): Rust checks the relay before warn_multiplicity (handle_completion in executor_core/executor.rs), Java inside BitmapNetExecutor.validateOutput before warnMultiplicity, and TypeScript in processCompletedTransitions before warnMultiplicity (bitmap-net-executor.ts). On a fail step the reference emits only TransitionFailed, never a deposit's diagnostics, which is the model's half of it."
          "AC2 (a join whose action writes into a relay target a token of another name or of no name fails that firing; the same net with a conforming action fires normally; both backends in every language agree; a throwing projection fails with the 'no name' error; no IO-016 AC4 WARN): the refusal is lines 1 and 3 with the fail offer of ExecFailCovers, worked in NU_054_fail_nonvacuous on AC4's join j1 (a token of another name and a unit token of a timeout branch fail the firing, the conforming output and the timeout forward of a match key are deposited); which firings exist is NU_054_check's; 'both executor backends agree', the error text and the WARN order are kind Q and N as above. AC1 (the build rejections) is NU_054_build's; AC3 to AC7 (verdicts, classifier, report notes, key fixtures) are NU_054_verifier's and the verifier pipeline's; none of them is about a failing firing."
  signoff "2026-11-13 d287eadd8994842f ai"
  statement : ∀ {N V : Type} [DecidableEq N], XRel N (Stamped V) → Prop :=
    fun E => ∀ (Nm : Type) [DecidableEq Nm] (mt : Trans _ → Option (MatchSpec _ (KeyFn _ Nm)))
      (cn : Trans _ → QDelivered _ (Stamped _) → Option Nm) C,
      C.relay = relayVerdict mt cn → ∀ i,
      (on (fun s s' => E C s (.commit i) s'), shall (fun s s' =>
        ∃ f ∈ s.fl, f.id = i ∧ ∃ e, f.out = some (.ok e) ∧ s'.M = qAppend s.M e ∧
          RelayPass mt cn f e)) ∧
      (on (fun s s' => E C s (.tdeposit i) s'), shall (fun s s' =>
        ∃ f ∈ s.fl, f.id = i ∧ ∃ e, f.out = some (.timedOut e) ∧ s'.M = qAppend s.M e ∧
          RelayPass mt cn f e)) ∧
      (on (fun s s' => E C s (.fail i) s'), shall (fun s s' => s'.M = s.M ∧ s'.pq = s.pq)) ∧
      (on (fun s s' => E C s (.flush i) s'), shall (fun s s' => s'.M = s.M ∧
        (s'.pq = s.pq ∨ ∃ f ∈ s.fl, f.id = i ∧ s'.pq = s.pq ++ [(i, f.buf)] ∧
          RelayPass mt cn f f.buf))) ∧
      (∀ s0 tr, IdsIssued s0 → XRun E C s0 tr →
        (after (nu054f_isRefusedFlush mt cn i), never (nu054f_isDeposit i)) tr) ∧
      (on (fun s s' => E C s (.publish i) s'), shall (fun s s' =>
        ∃ b, (i, b) ∈ s.pq ∧ s'.M = qAppend s.M b)) ∧
      (on (fun s s' => ∃ l, l ≠ .flush i ∧ E C s l s'), shall (fun s s' =>
        ∀ b, (i, b) ∈ s'.pq → (i, b) ∈ s.pq))

/- The pinned readable form of NU_054_fail: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.NU_054_fail : {N V : Type} → [DecidableEq N] → XRel N (Stamped V) → Prop :=
fun {N V} [DecidableEq N] E =>
  ∀ (Nm : Type) [inst_1 : DecidableEq Nm] (mt : Reference.Trans N → Option (MatchSpec N (KeyFn V Nm)))
    (cn : Reference.Trans N → QDelivered N (Stamped V) → Option Nm) (C : Cfg N (Stamped V)),
    C.relay = relayVerdict mt cn →
      ∀ (i : ℕ),
        (on fun s s' => E C s (XLbl.commit i) s', shall fun s s' =>
            ∃ f ∈ s.fl, f.id = i ∧ ∃ e, f.out = some (Outcome.ok e) ∧ s'.M = qAppend s.M e ∧ RelayPass mt cn f e) ∧
          (on fun s s' => E C s (XLbl.tdeposit i) s', shall fun s s' =>
              ∃ f ∈ s.fl,
                f.id = i ∧ ∃ e, f.out = some (Outcome.timedOut e) ∧ s'.M = qAppend s.M e ∧ RelayPass mt cn f e) ∧
            (on fun s s' => E C s (XLbl.fail i) s', shall fun s s' => s'.M = s.M ∧ s'.pq = s.pq) ∧
              (on fun s s' => E C s (XLbl.flush i) s', shall fun s s' =>
                  s'.M = s.M ∧
                    (s'.pq = s.pq ∨ ∃ f ∈ s.fl, f.id = i ∧ s'.pq = s.pq ++ [(i, f.buf)] ∧ RelayPass mt cn f f.buf)) ∧
                (∀ (s0 : XSt N (Stamped V)) (tr : List (XStep N (Stamped V))),
                    IdsIssued s0 →
                      XRun E C s0 tr → (after nu054f_isRefusedFlush mt cn i, never nu054f_isDeposit i) tr) ∧
                  (on fun s s' => E C s (XLbl.publish i) s', shall fun s s' =>
                      ∃ b, (i, b) ∈ s.pq ∧ s'.M = qAppend s.M b) ∧
                    on fun s s' => ∃ l, l ≠ XLbl.flush i ∧ E C s l s', shall fun s s' =>
                      ∀ (b : List (N × Stamped V)), (i, b) ∈ s'.pq → (i, b) ∈ s.pq
-/
#guard_msgs in #print NU_054_fail

/-! ## The reference -/

section Reference

variable {N T : Type} [DecidableEq N]

/-- **Firing `i` has had a batch refused**: the identity `i` was handed out, and the first firing
with identity `i`, if any, is marked `relayBad` and has not ended with a completion or a timeout
outcome (it is open, or it ended with an error). -/
def nu054f_Refused (i : Nat) (s : XSt N T) : Prop :=
  i < s.nextId ∧ ∀ f, s.fl.find? (·.id == i) = some f →
    f.relayBad = true ∧ (f.out = none ∨ f.out = some .err)

omit [DecidableEq N] in
/-- The first firing `i` after an update of firing `j`'s record by an `h` that keeps identities
is the first firing `i` before it, updated when `i = j`. -/
theorem nu054f_find_upd {s : XSt N T} {i j : Nat} {h : Firing N T → Firing N T}
    (hh : ∀ g, (h g).id = g.id) :
    (updFiring s j h).find? (·.id == i) =
      (s.fl.find? (·.id == i)).map (fun g => if g.id == j then h g else g) := by
  unfold updFiring
  rw [List.find?_map]
  have hp : ((fun g : Firing N T => g.id == i) ∘ fun g => if g.id == j then h g else g) =
      (fun g => g.id == i) := by
    funext g
    simp only [Function.comp_apply]
    split <;> simp [hh]
  rw [hp]

omit [DecidableEq N] in
/-- An update of firing `j`'s record keeps a refused firing `i` refused, when the update keeps it
marked and open or failed. -/
theorem nu054f_refused_upd {s s' : XSt N T} {i j : Nat} {h : Firing N T → Firing N T}
    (hfl : s'.fl = updFiring s j h) (hh : ∀ g, (h g).id = g.id)
    (hk : ∀ g, j = i → g.relayBad = true → (g.out = none ∨ g.out = some .err) →
      (h g).relayBad = true ∧ ((h g).out = none ∨ (h g).out = some .err)) (hn : s.nextId ≤ s'.nextId) (hb : nu054f_Refused i s) :
    nu054f_Refused i s' := by
  refine ⟨Nat.lt_of_lt_of_le hb.1 hn, fun f hf => ?_⟩
  rw [hfl, nu054f_find_upd hh] at hf
  obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hf
  have hgi : g.id = i := by simpa using List.find?_some hg
  obtain ⟨hr, ho⟩ := hb.2 g hg
  by_cases hj : g.id = j
  · have hb' : (g.id == j) = true := by simp [hj]
    simp only [hb', if_true]
    exact hk g (hj ▸ hgi) hr ho
  · have hb' : (g.id == j) = false := by simpa using hj
    simp only [hb', Bool.false_eq_true, if_false]
    exact ⟨hr, ho⟩

omit [DecidableEq N] in
/-- A settle keeps a refused firing `i` refused: it drops firings and keeps the supply. -/
theorem nu054f_refused_settle {s s' : XSt N T} {i j : Nat} (hfl : s'.fl = (settle s j).fl)
    (hn : s'.nextId = s.nextId) (hb : nu054f_Refused i s) : nu054f_Refused i s' := by
  refine ⟨hn ▸ hb.1, fun f hf => ?_⟩
  rw [hfl] at hf
  simp only [settle] at hf
  rw [List.find?_filter] at hf
  have hfi := List.find?_some hf
  by_cases hji : j = i
  · subst hji
    simp at hfi
  · have hp : (fun a : Firing N T => decide ((a.id != j) = true ∧ (a.id == i) = true)) =
        (fun a => a.id == i) := by
      funext a
      by_cases ha : a.id = i
      · have : a.id ≠ j := fun h => hji (h.symm.trans ha)
        simp [ha, show i ≠ j from fun h => hji h.symm]
      · simp [ha]
    rw [hp] at hf
    exact hb.2 f hf

omit [DecidableEq N] in
/-- Appending a firing with a fresh identity keeps a refused firing `i` refused. -/
theorem nu054f_refused_append {s s' : XSt N T} {i : Nat} {g : Firing N T}
    (hfl : s'.fl = s.fl ++ [g]) (hg : g.id = s.nextId) (hn : s.nextId ≤ s'.nextId)
    (hb : nu054f_Refused i s) : nu054f_Refused i s' := by
  refine ⟨Nat.lt_of_lt_of_le hb.1 hn, fun f hf => ?_⟩
  rw [hfl, List.find?_append] at hf
  cases h : s.fl.find? (·.id == i) with
  | some f0 =>
    rw [h, Option.some_or, Option.some.injEq] at hf
    subst hf
    exact hb.2 _ h
  | none =>
    rw [h, Option.none_or] at hf
    have := List.find?_some hf
    simp only [List.find?_cons, List.find?_nil] at hf
    have hgi : (g.id == i) = false := by
      have := hb.1
      simp only [beq_eq_false_iff_ne, ne_eq]
      omega
    simp [hgi] at hf

omit [DecidableEq N] in
/-- A step that keeps the firings and does not lower the supply keeps a refused firing refused. -/
theorem nu054f_refused_same {s s' : XSt N T} {i : Nat} (hfl : s'.fl = s.fl)
    (hn : s.nextId ≤ s'.nextId) (hb : nu054f_Refused i s) : nu054f_Refused i s' :=
  ⟨Nat.lt_of_lt_of_le hb.1 hn, fun f hf => hb.2 f (hfl ▸ hf)⟩

/-- Every reference step keeps a refused firing refused: writes and flushes keep it marked, its
return and its expiry record an error (the rules read `relayBad`), settles only drop firings, and a
start draws an identity above `i`. -/
theorem nu054f_refused_step {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    {i : Nat} (h : xstepW P C s l = some s') (hb : nu054f_Refused i s) : nu054f_Refused i s' := by
  have same : ∀ {s'' : XSt N T}, s'' = { s'' with fl := s.fl, nextId := s.nextId } →
      nu054f_Refused i s'' := fun he => by
    rw [he]; exact nu054f_refused_same rfl (Nat.le_refl _) hb
  cases l with
  | delay δ => obtain rfl := xstepW_delay h; exact nu054f_refused_same rfl (Nat.le_refl _) hb
  | write j p x =>
    obtain ⟨-, -, -, rfl⟩ := writeStep_some h
    exact nu054f_refused_upd rfl (fun _ => rfl) (fun g _ hr ho => ⟨hr, ho⟩) (Nat.le_refl _) hb
  | flush j =>
    obtain ⟨-, -, -, -, -, ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ := flushStep_some h
    · exact nu054f_refused_upd rfl (fun _ => rfl) (fun g _ hr ho => ⟨hr, ho⟩) (Nat.le_refl _) hb
    · exact nu054f_refused_upd rfl (fun _ => rfl) (fun g _ _ ho => ⟨rfl, ho⟩) (Nat.le_refl _) hb
  | ret j ok =>
    obtain ⟨-, -, -, rfl⟩ := retStep_some h
    exact nu054f_refused_upd rfl (fun _ => rfl) (fun g _ hr _ => ⟨hr, Or.inr (by simp [hr])⟩)
      (Nat.le_refl _) hb
  | expire j e =>
    obtain ⟨-, -, -, -, -, -, rfl⟩ := expireStep_some h
    exact nu054f_refused_upd rfl (fun _ => rfl) (fun g _ hr _ => ⟨hr, Or.inr (by simp [hr])⟩)
      (Nat.le_refl _) hb
  | request p x r =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := requestStep_some h
    · exact ⟨Nat.lt_of_lt_of_le hb.1 (Nat.le_succ _), hb.2⟩
    · exact hb
  | drain => obtain ⟨-, rfl⟩ := drainStep_some h; exact nu054f_refused_same rfl (Nat.le_refl _) hb
  | close => obtain ⟨-, rfl⟩ := closeStep_some h; exact nu054f_refused_same rfl (Nat.le_refl _) hb
  | terminateNow =>
    obtain ⟨-, rfl⟩ := terminateStep_some h; exact nu054f_refused_same rfl (Nat.le_refl _) hb
  | commit j =>
    obtain ⟨-, -, -, -, -, -, -, rfl⟩ := commitStep_some h
    exact nu054f_refused_settle (j := j) rfl rfl hb
  | fail j =>
    obtain ⟨-, -, -, -, rfl⟩ := failStep_some h; exact nu054f_refused_settle (j := j) rfl rfl hb
  | tdeposit j =>
    obtain ⟨-, -, -, -, -, -, rfl⟩ := tdepositStep_some h
    exact nu054f_refused_settle (j := j) rfl rfl hb
  | endCompletions =>
    obtain ⟨-, -, -, -, rfl⟩ := xstepW_endCompletions h
    exact nu054f_refused_same rfl (Nat.le_refl _) hb
  | publish j =>
    obtain ⟨-, -, -, -, -, rfl⟩ := publishStep_some h
    exact nu054f_refused_same rfl (Nat.le_refl _) hb
  | endPublications =>
    obtain ⟨-, -, -, rfl⟩ := xstepW_endPublications h
    exact nu054f_refused_same rfl (Nat.le_refl _) hb
  | inject k =>
    obtain ⟨-, -, -, -, -, -, -, rfl⟩ := injectStep_some h
    exact nu054f_refused_same rfl (Nat.le_refl _) hb
  | discard k =>
    obtain ⟨-, -, -, -, -, -, -, rfl⟩ := discardStep_some h
    exact nu054f_refused_same rfl (Nat.le_refl _) hb
  | snapshot a =>
    obtain ⟨-, -, -, rfl⟩ := snapshotStep_some h; exact nu054f_refused_same rfl (Nat.le_refl _) hb
  | endEvents =>
    obtain ⟨-, -, -, rfl⟩ := xstepW_endEvents h; exact nu054f_refused_same rfl (Nat.le_refl _) hb
  | update => obtain ⟨-, -, rfl⟩ := xstepW_update h; exact nu054f_refused_same rfl (Nat.le_refl _) hb
  | deadline ns =>
    obtain ⟨-, -, -, rfl⟩ := xstepW_deadline h; exact nu054f_refused_same rfl (Nat.le_refl _) hb
  | finish c =>
    cases c with
    | quiescent =>
      obtain ⟨-, -, -, rfl⟩ := xstepW_finishQuiescent h
      exact nu054f_refused_same rfl (Nat.le_refl _) hb
    | closed =>
      obtain ⟨-, -, -, -, rfl⟩ := xstepW_finishClosed h
      exact nu054f_refused_same rfl (Nat.le_refl _) hb
    | terminal =>
      obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h
      exact nu054f_refused_same rfl (Nat.le_refl _) hb
    | stopped =>
      obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h
      exact nu054f_refused_same rfl (Nat.le_refl _) hb
  | begin => obtain ⟨-, -, -, -, rfl⟩ := xstepW_begin h; exact nu054f_refused_same rfl (Nat.le_refl _) hb
  | start n sy =>
    obtain ⟨-, -, -, -, -, -, -, -, -, rfl⟩ := startStep_some h
    exact nu054f_refused_append rfl rfl (Nat.le_succ _) hb
  | lose n =>
    obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := loseStep_some h
    exact nu054f_refused_same rfl (Nat.le_refl _) hb
  | endPass => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endPass h; exact nu054f_refused_same rfl (Nat.le_refl _) hb
  | park tmr =>
    obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := parkStep_some h
    exact nu054f_refused_same rfl (Nat.le_refl _) hb
  | wake => obtain ⟨-, -, rfl⟩ := wakeStep_some h; exact nu054f_refused_same rfl (Nat.le_refl _) hb

/-- Only a flush adds to the publication queue: after a reference step labelled `l`, every entry
of the queue was already queued, or `l` is a flush of the entry's firing. -/
theorem nu054f_pq_step {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : xstepW P C s l = some s') :
    ∀ x ∈ s'.pq, x ∈ s.pq ∨ ∃ j, l = .flush j ∧ x.1 = j := by
  have keep : ∀ {s'' : XSt N T}, s''.pq = s.pq →
      ∀ x ∈ s''.pq, x ∈ s.pq ∨ ∃ j, l = .flush j ∧ x.1 = j :=
    fun he x hx => Or.inl (he ▸ hx)
  have clear : ∀ {s'' : XSt N T}, s''.pq = [] →
      ∀ x ∈ s''.pq, x ∈ s.pq ∨ ∃ j, l = .flush j ∧ x.1 = j :=
    fun he x hx => by rw [he] at hx; cases hx
  cases l with
  | delay δ => obtain rfl := xstepW_delay h; exact keep rfl
  | write j p x => obtain ⟨-, -, -, rfl⟩ := writeStep_some h; exact keep rfl
  | flush j =>
    obtain ⟨f, -, -, -, -, ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ := flushStep_some h
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr ⟨j, rfl, by rw [List.mem_singleton.mp hx]⟩
    · exact keep rfl
  | ret j ok => obtain ⟨-, -, -, rfl⟩ := retStep_some h; exact keep rfl
  | expire j e => obtain ⟨-, -, -, -, -, -, rfl⟩ := expireStep_some h; exact keep rfl
  | request p x r =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := requestStep_some h
    · exact keep rfl
    · exact keep rfl
  | drain => obtain ⟨-, rfl⟩ := drainStep_some h; exact keep rfl
  | close => obtain ⟨-, rfl⟩ := closeStep_some h; exact keep rfl
  | terminateNow => obtain ⟨-, rfl⟩ := terminateStep_some h; exact keep rfl
  | commit j => obtain ⟨-, -, -, -, -, -, -, rfl⟩ := commitStep_some h; exact keep rfl
  | fail j => obtain ⟨-, -, -, -, rfl⟩ := failStep_some h; exact keep rfl
  | tdeposit j => obtain ⟨-, -, -, -, -, -, rfl⟩ := tdepositStep_some h; exact keep rfl
  | endCompletions => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endCompletions h; exact keep rfl
  | publish j =>
    obtain ⟨b, rest, he, -, -, rfl⟩ := publishStep_some h
    intro x hx
    exact Or.inl (he ▸ List.mem_cons_of_mem _ hx)
  | endPublications => obtain ⟨-, -, -, rfl⟩ := xstepW_endPublications h; exact keep rfl
  | inject k => obtain ⟨-, -, -, -, -, -, -, rfl⟩ := injectStep_some h; exact keep rfl
  | discard k => obtain ⟨-, -, -, -, -, -, -, rfl⟩ := discardStep_some h; exact keep rfl
  | snapshot a => obtain ⟨-, -, -, rfl⟩ := snapshotStep_some h; exact keep rfl
  | endEvents => obtain ⟨-, -, -, rfl⟩ := xstepW_endEvents h; exact keep rfl
  | update => obtain ⟨-, -, rfl⟩ := xstepW_update h; exact keep rfl
  | deadline ns => obtain ⟨-, -, -, rfl⟩ := xstepW_deadline h; exact keep rfl
  | finish c =>
    cases c with
    | quiescent => obtain ⟨-, -, -, rfl⟩ := xstepW_finishQuiescent h; exact keep rfl
    | closed => obtain ⟨-, -, -, -, rfl⟩ := xstepW_finishClosed h; exact keep rfl
    | terminal => obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h; exact clear rfl
    | stopped => obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h; exact clear rfl
  | begin => obtain ⟨-, -, -, -, rfl⟩ := xstepW_begin h; exact keep rfl
  | start n sy => obtain ⟨-, -, -, -, -, -, -, -, -, rfl⟩ := startStep_some h; exact keep rfl
  | lose n => obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := loseStep_some h; exact keep rfl
  | endPass => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endPass h; exact keep rfl
  | park tmr => obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := parkStep_some h; exact keep rfl
  | wake => obtain ⟨-, -, rfl⟩ := wakeStep_some h; exact keep rfl

/-- No reference step deposits the output or the timeout outcome of a refused firing: a commit
needs a completion, a tdeposit a timeout outcome, on the first firing with that identity. -/
theorem nu054f_deposit_refused {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    {i : Nat} (h : xstepW P C s l = some s') (hd : nu054f_isDeposit i (s, l, s') = true)
    (hb : nu054f_Refused i s) : False := by
  cases l with
  | commit j =>
    simp only [nu054f_isDeposit, beq_iff_eq] at hd
    subst hd
    obtain ⟨f, e, hf, he, -⟩ := commitStep_some h
    rcases (hb.2 f hf).2 with ho | ho <;> rw [ho] at he <;> cases he
  | tdeposit j =>
    simp only [nu054f_isDeposit, beq_iff_eq] at hd
    subst hd
    obtain ⟨f, e, hf, he, -⟩ := tdepositStep_some h
    rcases (hb.2 f hf).2 with ho | ho <;> rw [ho] at he <;> cases he
  | _ => simp [nu054f_isDeposit] at hd

/-- The scan of `after T, never B` over a run of the reference step at judgement points `P`: a
`trig` step establishes the invariant `Inv`, every step keeps it, and no `bad` step leaves a
state where it holds; so with the memory `b` every step is accepted, provided the identities were
handed out and a set memory means `Inv` holds. -/
theorem nu054f_scan {P : XPol N T} {C : Cfg N T} {Inv : XSt N T → Prop}
    {trig bad : XStep N T → Bool}
    (hEst : ∀ {s s' : XSt N T} {l : XLbl N T}, xstepW P C s l = some s' → IdsIssued s →
      trig (s, l, s') = true → Inv s')
    (hKeep : ∀ {s s' : XSt N T} {l : XLbl N T}, xstepW P C s l = some s' → Inv s → Inv s')
    (hBlk : ∀ {s s' : XSt N T} {l : XLbl N T}, xstepW P C s l = some s' → Inv s →
      bad (s, l, s') = true → False) :
    ∀ {s : XSt N T} {tr : List (XStep N T)} (b : Bool),
      XRun (fun C s l s' => xstepW P C s l = some s') C s tr → IdsIssued s →
      (b = true → Inv s) → (afterNever trig bad).scan b tr = true
  | _, [], _, _, _, _ => rfl
  | s, (s₁, l, s') :: rest, b, ⟨h1, hstep, hrest⟩, hs, hb => by
    simp only at h1
    subst h1
    have hs' := exec022_idsIssued_step hstep hs
    have hok : (b && bad (s₁, l, s')) = false := by
      cases b with
      | false => rfl
      | true =>
        cases hd : bad (s₁, l, s') with
        | false => rfl
        | true => exact (hBlk hstep (hb rfl) hd).elim
    have hnext : (b || trig (s₁, l, s')) = true → Inv s' := by
      intro hn
      cases ht : trig (s₁, l, s') with
      | true => exact hEst hstep hs ht
      | false =>
        rw [ht, Bool.or_false] at hn
        exact hKeep hstep (hb hn)
    show (!(b && bad (s₁, l, s')) && (afterNever trig bad).scan (b || trig (s₁, l, s')) rest) = true
    rw [hok, nu054f_scan hEst hKeep hBlk _ hrest hs' hnext]
    rfl

end Reference

section ReferenceNu

variable {N V Nm : Type} [DecidableEq N] [DecidableEq Nm]

/-- A refused flush of `i` leaves firing `i` refused: the reference drops the batch and marks the
firing `relayBad` (`flushStep_some`), and the firing is still open. -/
theorem nu054f_refused_flush {P : XPol N (Stamped V)} {C : Cfg N (Stamped V)}
    {mt : Trans N → Option (MatchSpec N (KeyFn V Nm))}
    {cn : Trans N → QDelivered N (Stamped V) → Option Nm} (hC : C.relay = relayVerdict mt cn)
    {s s' : XSt N (Stamped V)} {l : XLbl N (Stamped V)} {i : Nat}
    (h : xstepW P C s l = some s') (hs : IdsIssued s)
    (ht : nu054f_isRefusedFlush mt cn i (s, l, s') = true) : nu054f_Refused i s' := by
  cases l with
  | flush j =>
    simp only [nu054f_isRefusedFlush, Bool.and_eq_true, beq_iff_eq] at ht
    obtain ⟨rfl, ht⟩ := ht
    obtain ⟨f, hf, ho, -, -, br⟩ := flushStep_some h
    rw [hf] at ht
    simp only [Bool.not_eq_true'] at ht
    have hid : f.id = j := by simpa using List.find?_some hf
    rcases br with ⟨-, hr, -⟩ | ⟨-, rfl⟩
    · rw [hC, ht] at hr; cases hr
    · refine ⟨hid ▸ hs f (List.mem_of_find?_eq_some hf), fun g hg => ?_⟩
      have hg' : (updFiring s j fun g => { g with buf := [], relayBad := true }).find?
          (·.id == j) = some g := hg
      rw [nu054f_find_upd (h := fun g => { g with buf := [], relayBad := true }) (fun _ => rfl),
        hf] at hg'
      have hfj : (f.id == j) = true := by simp [hid]
      simp only [hfj, if_true, Option.map_some, Option.some.injEq] at hg'
      subst hg'
      exact ⟨rfl, Or.inl ho⟩
  | _ => simp [nu054f_isRefusedFlush] at ht

/-- The executor of any judgement points `P` meets NU-054's failure lines: its `commit` and
`tdeposit` rules consult the configured relay check and append the emission (`commitStep_some`,
`tdepositStep_some`), its `fail` rule is a settle, which keeps the marking and the publication
queue (`failStep_some`), its `flush` rule queues a batch only when the relay check accepts it
(`flushStep_some`), and a refused flush leaves the firing marked, so that its return or expiry
records an error and no commit or tdeposit follows (`nu054f_scan`). -/
theorem nu054f_xstepW (P : XPol N (Stamped V)) :
    NU_054_fail (fun C s l s' => xstepW P C s l = some s') := by
  intro Nm _ mt cn C hC i
  refine ⟨fun s s' h => ?_, fun s s' h => ?_, fun s s' h => ?_, fun s s' h => ?_,
    fun s0 tr hs hr => ?_, fun s s' h => ?_, fun s s' ⟨l, hl, h⟩ b hb => ?_⟩
  · obtain ⟨f, e, hf, he, -, -, hr, rfl⟩ := commitStep_some h
    rw [hC] at hr
    exact ⟨f, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, e, he, rfl,
      relayVerdict_iff.mp hr⟩
  · obtain ⟨f, e, hf, he, -, hr, rfl⟩ := tdepositStep_some h
    rw [hC] at hr
    exact ⟨f, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, e, he, rfl,
      relayVerdict_iff.mp hr⟩
  · obtain ⟨f, -, -, -, rfl⟩ := failStep_some h
    exact ⟨rfl, rfl⟩
  · obtain ⟨f, hf, -, -, -, ⟨-, hr, rfl⟩ | ⟨-, rfl⟩⟩ := flushStep_some h
    · rw [hC] at hr
      exact ⟨rfl, Or.inr ⟨f, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, rfl,
        relayVerdict_iff.mp hr⟩⟩
    · exact ⟨rfl, Or.inl rfl⟩
  · exact nu054f_scan (Inv := nu054f_Refused i)
      (fun hst hs ht => nu054f_refused_flush hC hst hs ht)
      (fun hst hb => nu054f_refused_step hst hb)
      (fun hst hb hd => nu054f_deposit_refused hst hd hb)
      false hr hs (fun h => absurd h Bool.false_ne_true)
  · obtain ⟨b, rest, he, -, -, rfl⟩ := publishStep_some h
    exact ⟨b, he ▸ List.mem_cons_self .., rfl⟩
  · rcases nu054f_pq_step h _ hb with hb | ⟨j, rfl, hj⟩
    · exact hb
    · exact absurd (by rw [show i = j from hj]) hl

end ReferenceNu

/-- ✓ The reference executor satisfies the failure lines of NU-054: it deposits a returned output
or a timeout outcome only when every token in a relay target projects to the chosen name, a
failure deposits nothing and keeps the queued batches, a flush queues only a batch that passes,
and after a refused flush the firing can only fail (`nu054f_xstepW` at `refXPol`). -/
@[evidence holds NU_054_fail]
theorem NU_054_fail_reference {N V : Type} [DecidableEq N] :
    NU_054_fail (RefExec (N := N) (T := Stamped V)) :=
  nu054f_xstepW refXPol

/-! ## Examples

The join `j1` of AC4 (`NU_054.lean`): correlated inputs A = 0 and B = 1 (a token's name is its
value), relay target C = 2, sink E = 3, output spec `xor(and(C, E), timeout(C))`. The marking
holds X@0 in A and X@1 in B, X = 1. A token of value 0 stands for an absent value (the unit token
of an `Out.place` leaf in a timeout branch): the relay projection gives it no name. The chosen
name is read off the delivered key token (`keyName`), here X. Output-spec validation accepts every
produced set, so only the relay check decides; timeout outcomes are those into C alone. -/

/-- `j1` as the executor's transition. -/
def nu054f_t : Trans Nat := (nu054_j1 nu054_outUnit).base

/-- The match of each transition: `j1` carries `nu054_ms` (keys A and B, relay target C). -/
def nu054f_mt : Trans Nat → Option (MatchSpec Nat (KeyFn Nat Nat)) := fun t =>
  if t.core.name = "j1" then some nu054_ms else none

/-- The configuration of the examples with join-relay check `rel`. -/
def nu054f_cfg (rel : Trans Nat → QDelivered Nat (Stamped Nat) → List (Nat × Stamped Nat) → Bool) :
    Cfg Nat (Stamped Nat) :=
  { X := { net := { places := [0, 1, 2, 3], transitions := [nu054f_t] },
           timing := fun _ => .immediate, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [], reentrant := false,
    validate := fun _ _ => true, relay := rel,
    timeoutOut := fun _ _ e => e.map Prod.fst == [2], res := 0 }

/-- Output validation on: the relay check is NU-054's. -/
def nu054f_C : Cfg Nat (Stamped Nat) := nu054f_cfg (relayVerdict nu054f_mt (keyName nu054f_mt))

/-- The validation skip of [CONC-026]: the relay check accepts everything. -/
def nu054f_Cskip : Cfg Nat (Stamped Nat) := nu054f_cfg fun _ _ _ => true

/-- One cycle up to an asynchronous start of `j1`. -/
def nu054f_pre : List (XLbl Nat (Stamped Nat)) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin, .start "j1" false]

/-- The reference state after `pre`, then `body`, then the end of the pass. -/
def nu054f_at (C : Cfg Nat (Stamped Nat)) (body : List (XLbl Nat (Stamped Nat))) :
    Option (XSt Nat (Stamped Nat)) :=
  xrun C (xinit nu054_M 0) (nu054f_pre ++ body ++ [.endPass])

/-- The action writes `x` into C and a token into E, and returns. -/
def nu054f_body (x : Stamped Nat) : List (XLbl Nat (Stamped Nat)) :=
  [.write 0 2 x, .write 0 3 (nu020_tok 7 5), .ret 0 true]

/-- The action writes Y (= 2) into C and flushes it, then writes X into C and a token into E, and
returns. -/
def nu054f_bodyFlushBad : List (XLbl Nat (Stamped Nat)) :=
  [.write 0 2 (nu020_tok 2 5), .flush 0, .write 0 2 (nu020_tok 1 6), .write 0 3 (nu020_tok 7 6),
    .ret 0 true]

/-- The action writes a token into E and flushes it, then writes Y into C and returns. -/
def nu054f_bodyFlushGood : List (XLbl Nat (Stamped Nat)) :=
  [.write 0 3 (nu020_tok 7 5), .flush 0, .write 0 2 (nu020_tok 2 6), .ret 0 true]

/-- Every firing with identity `0` in `s` satisfies `p`. -/
def nu054f_all0 (s : XSt Nat (Stamped Nat)) (p : Firing Nat (Stamped Nat) → Bool) : Bool :=
  s.fl.all fun f => f.id != 0 || p f

/-- Read `p` off every firing with identity `0`. -/
theorem nu054f_of_all0 {s : XSt Nat (Stamped Nat)} {p : Firing Nat (Stamped Nat) → Bool}
    (h : nu054f_all0 s p = true) {f : Firing Nat (Stamped Nat)} (hf : f ∈ s.fl) (hid : f.id = 0) :
    p f = true := by
  have := List.all_eq_true.mp h f hf
  simpa [hid] using this

/-- The initial state has nothing in flight, so its identities were handed out. -/
theorem nu054f_init_issued : IdsIssued (xinit (N := Nat) (T := Stamped Nat) nu054_M 0) :=
  fun _ hf => by simp [xinit] at hf

/-- A decided commit step and its outcome under `nu054f_C`. -/
theorem nu054f_step {g : Cfg Nat (Stamped Nat) → XSt Nat (Stamped Nat) → XLbl Nat (Stamped Nat) →
      Option (XSt Nat (Stamped Nat))} {C : Cfg Nat (Stamped Nat)} {o : Option (XSt Nat (Stamped Nat))}
    {l : XLbl Nat (Stamped Nat)} {p : XSt Nat (Stamped Nat) → XSt Nat (Stamped Nat) → Bool}
    (h : (o.bind fun s => (g C s l).map (p s)) = some true) :
    ∃ s s', g C s l = some s' ∧ p s s' = true := by
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check g h
  exact ⟨s, s', hs, hp⟩

/-- ✓ Worked example (AC2, AC4, D17, CONC-026). The join `j1` takes X from A and B. When its
action returns X in C and a token in E, the output is deposited and C holds X. When it returns
Y in C instead, the firing fails: C stays empty and no commit is possible. When its budget runs
out with a unit token in C (no name), the firing fails and C stays empty; when the budget runs out
with A's X forwarded into C, C holds X. When the action flushes Y into C, the batch is not queued
and the firing later fails although its returned output passes the check. When the action
flushes a token into E and then returns Y in C, the firing fails and the flushed token still
lands in E. With output validation skipped, the output with Y in C is deposited. -/
@[evidence nonvacuous NU_054_fail]
theorem NU_054_fail_nonvacuous :
    (∃ s s', RefExec nu054f_C s (.commit 0) s' ∧ s'.M 2 = [nu020_tok 1 5]) ∧
    (∃ s s', RefExec nu054f_C s (.fail 0) s' ∧ s'.M 2 = [] ∧
      xstep nu054f_C s (.commit 0) = none) ∧
    (∃ s s', RefExec nu054f_C s (.fail 0) s' ∧ s'.M 2 = [] ∧
      xstep nu054f_C s (.tdeposit 0) = none) ∧
    (∃ s s', RefExec nu054f_C s (.tdeposit 0) s' ∧ s'.M 2 = [nu020_tok 1 0]) ∧
    (∃ s s', RefExec nu054f_C s (.flush 0) s' ∧ s'.pq = [] ∧ s.fl.length = 1) ∧
    (∃ s s', RefExec nu054f_C s (.fail 0) s' ∧ s'.M 2 = [] ∧ s'.M 3 = [] ∧
      xstep nu054f_C s (.commit 0) = none) ∧
    (∃ s s', RefExec nu054f_C s (.publish 0) s' ∧ s'.M 3 = [nu020_tok 7 5] ∧ s'.M 2 = []) ∧
    (∃ s s', RefExec nu054f_Cskip s (.commit 0) s' ∧ s'.M 2 = [nu020_tok 2 5]) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨s, s', hs, hp⟩ := nu054f_step (g := xstep) (C := nu054f_C)
      (o := nu054f_at nu054f_C (nu054f_body (nu020_tok 1 5))) (l := .commit 0)
      (p := fun _ s' => s'.M 2 == [nu020_tok 1 5]) (by decide)
    exact ⟨s, s', hs, by simpa using hp⟩
  · obtain ⟨s, s', hs, hp⟩ := nu054f_step (g := xstep) (C := nu054f_C)
      (o := nu054f_at nu054f_C (nu054f_body (nu020_tok 2 5))) (l := .fail 0)
      (p := fun s s' => s'.M 2 == [] && (xstep nu054f_C s (.commit 0)).isNone) (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at hp
    exact ⟨s, s', hs, hp⟩
  · obtain ⟨s, s', hs, hp⟩ := nu054f_step (g := xstep) (C := nu054f_C)
      (o := nu054f_at nu054f_C [.expire 0 [(2, nu020_tok 0 5)]]) (l := .fail 0)
      (p := fun s s' => s'.M 2 == [] && (xstep nu054f_C s (.tdeposit 0)).isNone) (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at hp
    exact ⟨s, s', hs, hp⟩
  · obtain ⟨s, s', hs, hp⟩ := nu054f_step (g := xstep) (C := nu054f_C)
      (o := nu054f_at nu054f_C [.expire 0 [(2, nu020_tok 1 0)]]) (l := .tdeposit 0)
      (p := fun _ s' => s'.M 2 == [nu020_tok 1 0]) (by decide)
    exact ⟨s, s', hs, by simpa using hp⟩
  · obtain ⟨s, s', hs, hp⟩ := nu054f_step (g := xstep) (C := nu054f_C)
      (o := xrun nu054f_C (xinit nu054_M 0) (nu054f_pre ++ [.write 0 2 (nu020_tok 2 5)]))
      (l := .flush 0) (p := fun s s' => s'.pq.isEmpty && s.fl.length == 1) (by decide)
    simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hp
    exact ⟨s, s', hs, hp⟩
  · obtain ⟨s, s', hs, hp⟩ := nu054f_step (g := xstep) (C := nu054f_C)
      (o := nu054f_at nu054f_C nu054f_bodyFlushBad) (l := .fail 0)
      (p := fun s s' => s'.M 2 == [] && s'.M 3 == [] && (xstep nu054f_C s (.commit 0)).isNone)
      (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at hp
    exact ⟨s, s', hs, hp.1.1, hp.1.2, hp.2⟩
  · obtain ⟨s, s', hs, hp⟩ := nu054f_step (g := xstep) (C := nu054f_C)
      (o := (nu054f_at nu054f_C nu054f_bodyFlushGood).bind fun s =>
        xrun nu054f_C s [.fail 0, .endCompletions])
      (l := .publish 0) (p := fun _ s' => s'.M 3 == [nu020_tok 7 5] && s'.M 2 == []) (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', hs, hp⟩
  · obtain ⟨s, s', hs, hp⟩ := nu054f_step (g := xstep) (C := nu054f_Cskip)
      (o := nu054f_at nu054f_Cskip (nu054f_body (nu020_tok 2 5))) (l := .commit 0)
      (p := fun _ s' => s'.M 2 == [nu020_tok 2 5]) (by decide)
    exact ⟨s, s', hs, by simpa using hp⟩

/-! ## Forbidden models: one per line -/

/-- A step function that is the reference except on the labels `g` answers. -/
def nu054f_patch (g : Cfg Nat (Stamped Nat) → XSt Nat (Stamped Nat) → XLbl Nat (Stamped Nat) →
    Option (Option (XSt Nat (Stamped Nat)))) :
    Cfg Nat (Stamped Nat) → XSt Nat (Stamped Nat) → XLbl Nat (Stamped Nat) →
      Option (XSt Nat (Stamped Nat)) := fun C s l =>
  match g C s l with
  | some r => r
  | none => xstep C s l

/-- An executor that commits a returned output without the relay check. -/
def nu054f_commitNoRelay : Cfg Nat (Stamped Nat) → XSt Nat (Stamped Nat) →
    XLbl Nat (Stamped Nat) → Option (XSt Nat (Stamped Nat)) :=
  nu054f_patch fun C s l => match l with
    | .commit i => some (commitStep refXPol { C with relay := fun _ _ _ => true } s i)
    | _ => none

/-- ✗ Committing without the relay check violates line 1: the action of `j1` returns Y in C, and
the executor deposits it although Y is not the chosen name X. -/
@[evidence forbids NU_054_fail]
theorem NU_054_fail_forbids_commitNoRelay :
    ¬ NU_054_fail (fun C s l s' => nu054f_commitNoRelay C s l = some s') := by
  intro h
  obtain ⟨s, s', hs, hp⟩ := nu054f_step (g := nu054f_commitNoRelay) (C := nu054f_C)
    (o := nu054f_at nu054f_C (nu054f_body (nu020_tok 2 5))) (l := .commit 0)
    (p := fun s _ => nu054f_all0 s fun f => match f.out with
      | some (.ok e) => !relayVerdict nu054f_mt (keyName nu054f_mt) f.t f.deliv e
      | _ => true) (by decide)
  obtain ⟨f, hf, hid, e, he, -, hr⟩ := (h Nat nu054f_mt (keyName nu054f_mt) nu054f_C rfl 0).1 s s' hs
  have hg := nu054f_of_all0 hp hf hid
  simp [he, relayVerdict_iff.mpr hr] at hg

/-- An executor that deposits a timeout outcome without the relay check. -/
def nu054f_tdepositNoRelay : Cfg Nat (Stamped Nat) → XSt Nat (Stamped Nat) →
    XLbl Nat (Stamped Nat) → Option (XSt Nat (Stamped Nat)) :=
  nu054f_patch fun C s l => match l with
    | .tdeposit i => some (tdepositStep { C with relay := fun _ _ _ => true } s i)
    | _ => none

/-- ✗ Depositing a timeout outcome without the relay check violates line 2: the budget of `j1`
runs out with a unit token in C, which has no name, and the executor deposits it. -/
@[evidence forbids NU_054_fail]
theorem NU_054_fail_forbids_tdepositNoRelay :
    ¬ NU_054_fail (fun C s l s' => nu054f_tdepositNoRelay C s l = some s') := by
  intro h
  obtain ⟨s, s', hs, hp⟩ := nu054f_step (g := nu054f_tdepositNoRelay) (C := nu054f_C)
    (o := nu054f_at nu054f_C [.expire 0 [(2, nu020_tok 0 5)]]) (l := .tdeposit 0)
    (p := fun s _ => nu054f_all0 s fun f => match f.out with
      | some (.timedOut e) => !relayVerdict nu054f_mt (keyName nu054f_mt) f.t f.deliv e
      | _ => true) (by decide)
  obtain ⟨f, hf, hid, e, he, -, hr⟩ := (h Nat nu054f_mt (keyName nu054f_mt) nu054f_C rfl 0).2.1 s s' hs
  have hg := nu054f_of_all0 hp hf hid
  simp [he, relayVerdict_iff.mpr hr] at hg

/-- An executor whose failure deposits the conforming part of a rejected output: every token
whose own one-token emission the relay check accepts. -/
def nu054f_partialDeposit : Cfg Nat (Stamped Nat) → XSt Nat (Stamped Nat) →
    XLbl Nat (Stamped Nat) → Option (XSt Nat (Stamped Nat)) :=
  nu054f_patch fun C s l => match l with
    | .fail i => some ((xstep C s (.fail i)).bind fun s₁ =>
        (s.fl.find? (·.id == i)).map fun f => match f.out with
          | some (.ok e) =>
            { s₁ with M := qAppend s₁.M (e.filter fun pt => C.relay f.t f.deliv [pt]) }
          | _ => s₁)
    | _ => none

/-- ✗ A failure that deposits the conforming part violates line 3 ("deposits nothing"): the action
of `j1` returns Y in C and a token in E; the firing fails, and the executor still deposits the
token in E. -/
@[evidence forbids NU_054_fail]
theorem NU_054_fail_forbids_partialDeposit :
    ¬ NU_054_fail (fun C s l s' => nu054f_partialDeposit C s l = some s') := by
  intro h
  obtain ⟨s, s', hs, hp⟩ := nu054f_step (g := nu054f_partialDeposit) (C := nu054f_C)
    (o := nu054f_at nu054f_C (nu054f_body (nu020_tok 2 5))) (l := .fail 0)
    (p := fun s s' => s'.M 3 != s.M 3) (by decide)
  have := ((h Nat nu054f_mt (keyName nu054f_mt) nu054f_C rfl 0).2.2.1 s s' hs).1
  simp [this] at hp

/-- An executor whose flush queues every batch, without the relay check. -/
def nu054f_flushNoGuard : Cfg Nat (Stamped Nat) → XSt Nat (Stamped Nat) →
    XLbl Nat (Stamped Nat) → Option (XSt Nat (Stamped Nat)) :=
  nu054f_patch fun C s l => match l with
    | .flush i => some (flushStep { C with relay := fun _ _ _ => true } s i)
    | _ => none

/-- ✗ A flush without the relay check violates line 4: the action of `j1` flushes Y into C, and
the executor queues the batch for deposit. -/
@[evidence forbids NU_054_fail]
theorem NU_054_fail_forbids_flushNoGuard :
    ¬ NU_054_fail (fun C s l s' => nu054f_flushNoGuard C s l = some s') := by
  intro h
  obtain ⟨s, s', hs, hp⟩ := nu054f_step (g := nu054f_flushNoGuard) (C := nu054f_C)
    (o := xrun nu054f_C (xinit nu054_M 0) (nu054f_pre ++ [.write 0 2 (nu020_tok 2 5)]))
    (l := .flush 0)
    (p := fun s s' => s'.pq.length != s.pq.length &&
      nu054f_all0 s fun f => !relayVerdict nu054f_mt (keyName nu054f_mt) f.t f.deliv f.buf)
    (by decide)
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hp
  rcases ((h Nat nu054f_mt (keyName nu054f_mt) nu054f_C rfl 0).2.2.2.1 s s' hs).2 with hq | ⟨f, hf, hid, -, hr⟩
  · exact hp.1 (by rw [hq])
  · have hg := nu054f_of_all0 hp.2 hf hid
    rw [relayVerdict_iff.mpr hr] at hg
    cases hg

/-- An executor whose flush drops a batch the relay check rejects but does not mark the firing:
the firing goes on and completes (Rust's "recording it and returning `Ok`"). -/
def nu054f_recordOk : Cfg Nat (Stamped Nat) → XSt Nat (Stamped Nat) →
    XLbl Nat (Stamped Nat) → Option (XSt Nat (Stamped Nat)) :=
  nu054f_patch fun C s l => match l with
    | .flush i => some ((flushStep C s i).map fun s₁ =>
        { s₁ with fl := s₁.fl.map fun g => if g.id == i then { g with relayBad := false } else g })
    | _ => none

/-- ✗ A flush that drops the bad batch and lets the firing complete violates line 5: the action
of `j1` flushes Y into C, which is refused, then writes X into C and a token into E and returns;
the executor commits that output. -/
@[evidence forbids NU_054_fail]
theorem NU_054_fail_forbids_recordOk :
    ¬ NU_054_fail (fun C s l s' => nu054f_recordOk C s l = some s') := by
  intro h
  obtain ⟨tr, hr, hp⟩ := exec022_trace_of_check (g := nu054f_recordOk) (C := nu054f_C)
    (s := xinit nu054_M 0)
    (ls := nu054f_pre ++ nu054f_bodyFlushBad ++ [.endPass, .commit 0])
    (p := fun tr => !(afterNever (nu054f_isRefusedFlush nu054f_mt (keyName nu054f_mt) 0)
      (nu054f_isDeposit 0)).scan false tr) (by decide)
  have h2 : (afterNever (nu054f_isRefusedFlush nu054f_mt (keyName nu054f_mt) 0)
      (nu054f_isDeposit 0)).scan false tr = true :=
    (h Nat nu054f_mt (keyName nu054f_mt) nu054f_C rfl 0).2.2.2.2.1 _ tr nu054f_init_issued hr
  simp [h2] at hp

/-- An executor whose failure also withdraws the batches the firing published and the executor
has not deposited yet. -/
def nu054f_failDropsPub : Cfg Nat (Stamped Nat) → XSt Nat (Stamped Nat) →
    XLbl Nat (Stamped Nat) → Option (XSt Nat (Stamped Nat)) :=
  nu054f_patch fun C s l => match l with
    | .fail i => some ((xstep C s (.fail i)).map fun s₁ =>
        { s₁ with pq := s₁.pq.filter (·.1 != i) })
    | _ => none

/-- ✗ A failure that withdraws a published batch violates line 3 ("shall not withdraw a batch the
action flushed before the firing failed"): the action of `j1` flushes a token into E, then returns
Y in C; the firing fails, and the executor drops the queued batch, so the token never reaches E. -/
@[evidence forbids NU_054_fail]
theorem NU_054_fail_forbids_failDropsPub :
    ¬ NU_054_fail (fun C s l s' => nu054f_failDropsPub C s l = some s') := by
  intro h
  obtain ⟨s, s', hs, hp⟩ := nu054f_step (g := nu054f_failDropsPub) (C := nu054f_C)
    (o := nu054f_at nu054f_C nu054f_bodyFlushGood) (l := .fail 0)
    (p := fun s s' => !s.pq.isEmpty && s'.pq.isEmpty) (by decide)
  have := ((h Nat nu054f_mt (keyName nu054f_mt) nu054f_C rfl 0).2.2.1 s s' hs).2
  simp [this] at hp

/-- An executor whose flush deposits what the action wrote straight into the marking, without
the queue and without the relay check. -/
def nu054f_flushDeposits : Cfg Nat (Stamped Nat) → XSt Nat (Stamped Nat) →
    XLbl Nat (Stamped Nat) → Option (XSt Nat (Stamped Nat)) :=
  nu054f_patch fun _ s l => match l with
    | .flush i => some ((s.fl.find? (·.id == i)).bind fun f =>
        if f.buf.isEmpty then none
        else some { s with M := qAppend s.M f.buf, fl := updFiring s i fun g => { g with buf := [] } })
    | _ => none

/-- ✗ A flush that deposits at once violates line 4 ("shall not deposit that batch"): the action
of `j1` flushes Y into C, and the executor puts Y into C at the flush. -/
@[evidence forbids NU_054_fail]
theorem NU_054_fail_forbids_flushDeposits :
    ¬ NU_054_fail (fun C s l s' => nu054f_flushDeposits C s l = some s') := by
  intro h
  obtain ⟨s, s', hs, hp⟩ := nu054f_step (g := nu054f_flushDeposits) (C := nu054f_C)
    (o := xrun nu054f_C (xinit nu054_M 0) (nu054f_pre ++ [.write 0 2 (nu020_tok 2 5)]))
    (l := .flush 0) (p := fun s s' => s'.M 2 != s.M 2) (by decide)
  have := ((h Nat nu054f_mt (keyName nu054f_mt) nu054f_C rfl 0).2.2.2.1 s s' hs).1
  simp [this] at hp

/-- An executor whose publish step deposits what the action holds when nothing of the firing is
queued: a batch that never went through the flush and its check. -/
def nu054f_publishUnqueued : Cfg Nat (Stamped Nat) → XSt Nat (Stamped Nat) →
    XLbl Nat (Stamped Nat) → Option (XSt Nat (Stamped Nat)) :=
  nu054f_patch fun _ s l => match l with
    | .publish i =>
      if s.pq.any (·.1 == i) then none
      else some ((s.fl.find? (·.id == i)).bind fun f =>
        if f.buf.isEmpty then none
        else some { s with M := qAppend s.M f.buf, fl := updFiring s i fun g => { g with buf := [] } })
    | _ => none

/-- ✗ A publish of a batch that was never queued violates line 6: the action of `j1` writes Y
into C, nothing of the firing is queued, and the executor's publish step puts Y into C. -/
@[evidence forbids NU_054_fail]
theorem NU_054_fail_forbids_publishUnqueued :
    ¬ NU_054_fail (fun C s l s' => nu054f_publishUnqueued C s l = some s') := by
  intro h
  obtain ⟨s, s', hs, hp⟩ := nu054f_step (g := nu054f_publishUnqueued) (C := nu054f_C)
    (o := xrun nu054f_C (xinit nu054_M 0) (nu054f_pre ++ [.write 0 2 (nu020_tok 2 5)]))
    (l := .publish 0) (p := fun s _ => s.pq.isEmpty) (by decide)
  obtain ⟨b, hb, -⟩ := (h Nat nu054f_mt (keyName nu054f_mt) nu054f_C rfl 0).2.2.2.2.2.1 s s' hs
  simp only [List.isEmpty_iff] at hp
  rw [hp] at hb
  cases hb

/-- An executor whose return hands what the action wrote to the publication queue, unchecked,
and completes with an empty output (Rust: the completion sending through the raw flush sender,
not through the guarded flush callback). -/
def nu054f_retQueues : Cfg Nat (Stamped Nat) → XSt Nat (Stamped Nat) →
    XLbl Nat (Stamped Nat) → Option (XSt Nat (Stamped Nat)) :=
  nu054f_patch fun C s l => match l with
    | .ret i true => some ((xstep C s (.ret i true)).bind fun s₁ =>
        (s.fl.find? (·.id == i)).map fun f =>
          { s₁ with pq := s₁.pq ++ [(i, f.buf)],
                    fl := s₁.fl.map fun g => if g.id == i then { g with out := some (.ok []) } else g })
    | _ => none

/-- ✗ A return that queues the action's output violates line 7: the action of `j1` writes Y into
C and a token into E and returns; the executor queues that output as a batch, so the commit of the
empty output passes the check and a later publish would put Y into C. -/
@[evidence forbids NU_054_fail]
theorem NU_054_fail_forbids_retQueues :
    ¬ NU_054_fail (fun C s l s' => nu054f_retQueues C s l = some s') := by
  intro h
  obtain ⟨s, s', hs, hp⟩ := nu054f_step (g := nu054f_retQueues) (C := nu054f_C)
    (o := xrun nu054f_C (xinit nu054_M 0)
      (nu054f_pre ++ [.write 0 2 (nu020_tok 2 5), .write 0 3 (nu020_tok 7 5)]))
    (l := .ret 0 true) (p := fun s s' => s.pq.isEmpty && s'.pq.any (·.1 == 0)) (by decide)
  simp only [Bool.and_eq_true, List.isEmpty_iff, List.any_eq_true, beq_iff_eq] at hp
  obtain ⟨hq, ⟨j, b⟩, hx, rfl⟩ := hp
  have := (h Nat nu054f_mt (keyName nu054f_mt) nu054f_C rfl 0).2.2.2.2.2.2 s s'
    ⟨.ret 0 true, by simp, hs⟩ b hx
  rw [hq] at this
  cases this

end Libpetri.Spec
