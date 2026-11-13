import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Exec
import Libpetri.Spec.Text.ENV_016

set_option linter.missingDocs true

/-!
# ENV-016: Observable Termination (`spec/06-environment-places.md`)

ENV-016 has two halves. The first, `awaitTermination`, needs the event model (its answer waits
for ExecutionCompleted), so it is the second block of ENV-016, `ENV_016_await`
(`ENV_016_l1.lean`, wave W7, ruling D47 (c)). This file states the second half, the policy of
run-with-timeout for the loop when the caller's timeout expires, over the executor model
(`RefExec`, `Reference/Exec.lean`).

The expiry of the caller's timeout is an event of the host, not a step of the loop, and ruling
D18 (b) keeps host time out of the model. So the expiry is not a label of `XLbl`: the model of
this block is a pair, an executor `R : XRel N T` and the expiry handling `X : ExpiryRel N T` of
its run-with-timeout. `X C pol s s'` says that when the caller's timeout expires under policy
`pol`, the executor goes from `s` to `s'`. The witnesses are `RefExec` and `refExpiry`: abandon
changes nothing, close is the reference close step.

The three lines: under abandon the expiry leaves the executor as it was; under close it is the
executor's own close step whenever the executor is open or draining, and changes nothing once it
is closed or stopped; and no expiry while the loop runs ends the run or changes the marking. That
an expiry while the loop runs always takes effect is an offer, so it is no line: `Env016Covers`
below is the coverage clause for the consistency theorem's `ExecCoversW5`, over the expiry
handling (`env016_ref_covers`; an expiry handler that never runs meets every line and fails it,
`env016_covers_unhandled`). The evidence checks the block against the reference and six wrong
implementations: one that closes under abandon, one whose timer completes the loop's result (the
defect Java's `loop.copy()` avoids), one that ignores the close policy, one that terminates at
once instead of closing, one whose executor refuses a close while its loop runs, and one whose
close finishes the run at the expiry.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## The expiry of the caller's timeout -/

/-- What run-with-timeout does with the loop when the caller's timeout expires ([ENV-016]). -/
inductive TimeoutPolicy where
  /-- Leave the loop running. -/
  | abandon
  /-- Close the executor ([ENV-013]). -/
  | close
  deriving DecidableEq, Repr

/-- The expiry handling of a run-with-timeout: `X C pol s s'` says that, under configuration
`C`, the expiry of the caller's timeout under policy `pol` takes the executor from state `s` to
`s'`. -/
abbrev ExpiryRel (N T : Type) := Cfg N T → TimeoutPolicy → XSt N T → XSt N T → Prop

/-- The reference expiry, as a function: abandon changes nothing; close is the reference close
step (`closeStep`), and changes nothing when the executor is already closed or stopped. -/
def refExpiryStep {N T : Type} [DecidableEq N] (s : XSt N T) : TimeoutPolicy → XSt N T
  | .abandon => s
  | .close => (closeStep s).getD s

/-- **The reference expiry handling**: the graph of `refExpiryStep`. Java's
`run(Duration, RunTimeoutPolicy)` (in `BitmapNetExecutor`) fails only a copy of the
loop's future and calls `close()` under CLOSE; TypeScript's `run(timeoutMs, onTimeout)`
(`run` in `bitmap-net-executor.ts`) rejects the caller's promise and calls `close()` under
`'close'`. -/
def refExpiry {N T : Type} [DecidableEq N] : ExpiryRel N T :=
  fun _ pol s s' => s' = refExpiryStep s pol

/- The reference expiry handling is the second witness model of ENV-016's `holds` theorem. -/
#spec_witness refExpiry

/-! ## ENV-016: Observable Termination -/

requirement ENV_016
  id "ENV-016"
  title "Observable Termination"
  kind B
  scope "executors that provide run-with-timeout with a timeout policy (Java, TypeScript)"
  source verbatim "spec/06-environment-places.md"
  covers ENV_016.s11, ENV_016.s12, ENV_016.s13, ENV_016.s14, ENV_016.s15, ENV_016.s16, ENV_016.s17,
        ENV_016.s18
  reading "For every executor R, every expiry handling X of its run-with-timeout and every configuration C:"
          "an expiry under abandon from state s ends in s itself;"
          "an expiry under close from a state s whose mode is open or draining ends in a state that a close step of R reaches from s, and from a state s whose mode is closed or stopped it ends in s itself;"
          "an expiry from a state in which the loop is running ends in a state in which the loop is still running, with the same marking."
  assumes "The model is a pair: an executor R : XRel N T (glossary GlossaryExec.lean), where R C s l s' says that under configuration C the step labelled l leads from executor state s to s', and the expiry handling X : ExpiryRel N T of its run-with-timeout, where X C pol s s' says that the expiry of the caller's timeout under policy pol (TimeoutPolicy: abandon or close) takes the executor from s to s'. The expiry is an event of the host's clock, which the model does not carry (ruling D18 (b)), so it is a relation beside R and not a label of XLbl. The caller's own result (Java's returned stage failing with a TimeoutException, TypeScript's rejected promise) is not executor state and is outside the model. The witnesses are the reference executor RefExec (Reference/Exec.lean) and refExpiry: abandon changes nothing, close is RefExec's close step, or nothing when the executor is already closed or stopped."
          "That the expiry is handled under the policy the caller chose, and not another, is the meaning of X's policy argument: X C pol s s' is the handling of a run whose caller chose pol, so lines 1 and 2 say what each choice does, and the coverage clause Env016Covers says that the handling takes effect at all. The binding of the caller's argument to pol is not modelled further; an implementation that swapped the two policies breaks line 1 on the abandon side (ENV_016_forbids_abandonCloses) and line 2 on the close side (ENV_016_forbids_closeIgnored)."
          "Scope (Status Proposed, priority MAY, ruling D47 (c)): the block applies to the implementations that expose the policy, Java (run(Duration, RunTimeoutPolicy) in BitmapNetExecutor and PrecompiledNetExecutor) and TypeScript (run(timeoutMs, onTimeout) in both executors). Rust and Python have no run-with-timeout policy (spec/runtime-defects.md, UB-03). Java's PetriNetExecutor interface has a default run(timeout, policy) that ignores the policy and abandons: an executor that keeps that default does not provide the close policy, and one that claimed to would break line 2 (ENV_016_forbids_closeIgnored)."
          "Its offer is in ExecCoversW5.Env016Covers (ConsistencyExec.lean; the convention of GlossaryExec.lean: offers are coverage clauses, never block lines). Sentence s13 ('act on the expiry under the policy the caller chose') demands an answer and is covered whole; its safety halves are lines 1 and 2, and its existence half is that clause: from every state in which the loop is running, an expiry under either policy has an outcome in X, which the reference meets (env016_ref_covers). AC3 is lines 1 to 3 with that clause. Under abandon the expiry changes nothing and the loop keeps running (line 1; ENV_016_forbids_abandonCloses: an expiry that closes the executor under abandon breaks it). Under close, from an open or draining executor, the expiry is the executor's own close step (line 2; ENV_016_forbids_closeIgnored: an expiry that leaves the executor open breaks it, and so does ENV_016_forbids_closeTerminates, an expiry that stops the loop without waiting for its firings in flight, as terminateNow does under ENV-015). Line 2 reads 'already closed or stopped' on the lifecycle mode, not on the steps R offers, so line 2 and Env016Covers together require R to have a close step from every open or draining state in which its loop runs: an executor that refuses close() while its loop runs, so that the close policy acts as abandon, breaks line 2 (ENV_016_forbids_closeRefusedWhileRunning), and an expiry handling that gave such an executor no outcome there instead would fail Env016Covers. The expiry under close does not stop the loop at once (line 3; ENV_016_forbids_closeFinishes). That the loop then stops once its in-flight actions complete is ENV-013's requirement (its item 4), not a line of this block; ENV_016_nonvacuous part 3 shows it on the test derivation's run. Env016Covers makes the expiry take effect at all: an implementation whose expiry handler never runs meets every line and fails the clause (env016_covers_unhandled). The clause asks for an outcome only while the loop runs: once the run has returned, Java's orTimeout and TypeScript's cleared timer no longer fire."
          "The MUST NOT sentence is line 3 with line 1: no expiry while the loop runs ends the run or changes the marking, so the result the loop reports, the marking at its finish and the fact that it ended (EXEC-041), is fixed only by a finish step of the loop. Line 3 adds to line 1 only under close, where it constrains R's own close step; under abandon it follows from line 1. An implementation whose timer completes the loop's own result with the marking at the expiry, the defect Java's loop.copy() avoids, breaks line 1 (ENV_016_forbids_expiryCompletes); one whose close finishes the run at once, reporting the marking at the expiry, breaks line 3 although its expiry is its own close step (ENV_016_forbids_closeFinishes). 'An abandoned loop can still report its real final marking' is ENV_016_nonvacuous part 2: after an expiry under abandon the action in flight returns, its output is deposited, and the loop finishes quiescent with that output in the marking it reports."
          "The termination reason an abandoned run reports is EXEC-041's question, not this block's (env-b ENVB-R6 (a), ruling D53 (c)): TypeScript sets its reason to stopped when the caller's timeout expires and, when the loop later ends on its own, replaces it with the cause of that finish (RD-52). That field is reporting state outside the executor state of the model, and D53 (c) allows stopped while the loop runs on, since stopped is not a completed reason. Lines 1 and 3 speak of the executor state and the marking only."
          "Java closes the executor from a callback that runs after the returned stage has failed (whenCompleteAsync), so loop steps may come between the expiry and the close. The model places the expiry at the moment close() takes effect; a run in which loop steps come first is a run of R whose close step comes later. TypeScript calls close() in the turn that rejects the promise."
          "Which policy is the default is configuration (kind N) and not a line: run(timeout) without a policy abandons in Java and TypeScript, the historical default of the text. The lines hold for whichever policy the caller chooses."
          "The awaitTermination sentences (s1 to s10, the first paragraph with them), AC1 and AC2 are the second block of ENV-016, ENV_016_await (ENV_016_l1.lean, wave W7, ruling D47 (c)), over the event model RefEvents, since the answer waits for the step that emits ExecutionCompleted: awaitTermination answers true when the loop was never started, false while it runs, true only after the finish step that answers the queued inject() calls and only once no emission of ExecutionCompleted is still to come, and true once the loop has finished, whatever a failing event store did. Blocking, the timeout of awaitTermination and 'promptly' are kind Q."
          "The test derivation (a net with an action still in flight when a short timeout expires, under each policy; the executor closed under close and the loop stopping once the action completes, the loop still live under abandon and reporting the action's output) is ENV_016_nonvacuous: at the expiry the loop is still running, parked with a firing in flight; under close the executor is closed by R's close step and the loop finishes closed after the action completes; under abandon the executor is unchanged and the loop goes on to finish quiescent with the action's output. The awaitTermination half of the test derivation is ENV_016_await_nonvacuous, on the same run."
  signoff "2026-11-13 e3c4e69a7b654c37 ai"
  statement : ∀ {N T : Type} [DecidableEq N], XRel N T → ExpiryRel N T → Prop :=
    fun R X => ∀ C,
      (on (fun s s' => X C .abandon s s'), shall (fun s s' => s' = s)) ∧
      (on (fun s s' => X C .close s s'),
        shall (fun s s' => ((s.mode = .open ∨ s.mode = .draining) → R C s .close s') ∧
          ((s.mode = .closed ∨ s.mode = .stopped) → s' = s))) ∧
      (∀ pol, on (fun s s' => X C pol s s' ∧ isExecPhase s.phase = true),
        shall (fun s s' => isExecPhase s'.phase = true ∧ s'.M = s.M))

/- The pinned readable form of ENV-016: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.ENV_016 : {N T : Type} → [DecidableEq N] → XRel N T → ExpiryRel N T → Prop :=
fun {N T} [DecidableEq N] R X =>
  ∀ (C : Cfg N T),
    (on fun s s' => X C TimeoutPolicy.abandon s s', shall fun s s' => s' = s) ∧
      (on fun s s' => X C TimeoutPolicy.close s s', shall fun s s' =>
          (s.mode = Mode.open ∨ s.mode = Mode.draining → R C s XLbl.close s') ∧
            (s.mode = Mode.closed ∨ s.mode = Mode.stopped → s' = s)) ∧
        ∀ (pol : TimeoutPolicy),
          on fun s s' => X C pol s s' ∧ isExecPhase s.phase = true, shall fun s s' =>
            isExecPhase s'.phase = true ∧ s'.M = s.M
-/
#guard_msgs in #print ENV_016

/-! ### The reference -/

/-- ✓ The reference executor with the reference expiry handling satisfies ENV-016: abandon is
the identity; close is `closeStep`, which is RefExec's close step
from an open or draining executor and undefined, so the identity, from a closed or stopped one;
and `closeStep` changes only the mode and the parked flag, so the phase and the marking stay
(`closeStep_some`). -/
@[evidence holds ENV_016]
theorem ENV_016_reference {N T : Type} [DecidableEq N] :
    ENV_016 (RefExec (N := N) (T := T)) refExpiry := by
  intro C
  refine ⟨fun s s' h => h,
    fun s s' h => ⟨fun hm => ?_, fun hm => ?_⟩, fun pol s s' ⟨h, _⟩ => ?_⟩
  · change s' = (closeStep s).getD s at h
    change closeStep s = some s'
    rcases hm with hm | hm <;> simp [closeStep, hm] at h ⊢ <;> exact h.symm
  · change s' = (closeStep s).getD s at h
    rcases hm with hm | hm <;> simp [closeStep, hm] at h <;> exact h
  · change s' = refExpiryStep s pol at h
    subst h
    cases pol with
    | abandon => exact ⟨‹_›, rfl⟩
    | close =>
      simp only [refExpiryStep]
      cases hc : closeStep s with
      | none => exact ⟨‹_›, rfl⟩
      | some s1 =>
        obtain ⟨-, rfl⟩ := closeStep_some hc
        exact ⟨‹_›, rfl⟩

/-- **The coverage conjunct ENV-016 asks of the consistency theorem's `ExecCoversW5`**: from
every state in which the loop is running, the expiry of the caller's timeout under either policy
has an outcome in the expiry handling `X` (sentence s13, AC3 "the executor is closed
on timeout"). It is a clause over the expiry handling, not over the executor. Offers are never a
line of a block (glossary `GlossaryExec.lean`). -/
def Env016Covers {N T : Type} (X : ExpiryRel N T) : Prop :=
  ∀ C pol s, isExecPhase s.phase = true → ∃ s', X C pol s s'

/-- The reference expiry handling meets ENV-016's coverage conjunct: it is the graph of a total
function (`refExpiryStep`), so every expiry has an outcome. -/
theorem env016_ref_covers {N T : Type} [DecidableEq N] :
    Env016Covers (refExpiry (N := N) (T := T)) :=
  fun _ pol s _ => ⟨refExpiryStep s pol, rfl⟩

/-! ### Examples

Place `0` holds one token; transition `t` takes it and outputs to place `1` through an
asynchronous action. No place is an environment place, so the loop finishes quiescent once
nothing is armed, in flight or queued. -/

/-- Transition `t`: one token from place `0`, output `1`. -/
def env016_t : Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 1) }

/-- The configuration of the examples. -/
def env016_c : Cfg Nat Nat :=
  { X := { net := { places := [0, 1], transitions := [env016_t] },
           timing := fun _ => .immediate, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => false,
    res := 0 }

/-- The initial state: one token in place `0`. -/
def env016_s0 : XSt Nat Nat := xinit (fun p => if p = 0 then [5] else []) 0

/-- The first cycle starts `t` asynchronously; the second finds nothing to start, and the loop
blocks in its wait with the firing in flight. -/
def env016_toPark : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin, .start "t" false,
   .endPass, .endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin,
   .endPass, .park none]

/-- After the expiry: the action writes `7` to place `1` and returns, the wait settles it, and
the next cycle reaches its termination test. -/
def env016_toTest : List (XLbl Nat Nat) :=
  [.write 0 1 7, .ret 0 true, .commit 0, .endCompletions, .endPublications, .endEvents, .update,
   .deadline []]

/-- The reference state after `ls` from `env016_s0`. -/
def env016_at (ls : List (XLbl Nat Nat)) : Option (XSt Nat Nat) := xrun env016_c env016_s0 ls

/-- The state the loop reaches by `ls` after an expiry under `pol` at the parked state. -/
def env016_after (pol : TimeoutPolicy) (ls : List (XLbl Nat Nat)) : Option (XSt Nat Nat) :=
  (env016_at env016_toPark).bind fun s => xrun env016_c (refExpiryStep s pol) ls

/-- Read a state off a decided check of an optional state. -/
theorem env016_of_map {o : Option (XSt Nat Nat)} {p : XSt Nat Nat → Bool}
    (h : o.map p = some true) : ∃ s, o = some s ∧ p s = true := by
  cases ho : o with
  | none => simp [ho] at h
  | some s => exact ⟨s, rfl, by simpa [ho] using h⟩

/-- `env016_s0`'s loop is running (it has not finished). -/
theorem env016_s0_running : isExecPhase env016_s0.phase = true := rfl

/-! ### Coverage: the expiry is never handled -/

/-- An implementation whose expiry handler never runs: the caller's timeout expires and nothing
happens, under either policy, so a close policy never closes. -/
def env016_unhandled {N T : Type} : ExpiryRel N T := fun _ _ _ _ => False

/-- The expiry taking effect is coverage, not a line: an expiry handling that never runs meets
every line of ENV-016 (they say nothing of an expiry that has no outcome) and fails its coverage
conjunct `Env016Covers` (sentence s13, AC3 "the executor is closed on timeout"): at
the start of a run the expiry under close has no outcome. -/
@[evidence cites "ENV-016" "when the caller's timeout expires while the loop is running, the implementation shall act on the expiry under the policy the caller chose: an expiry handler that never runs meets every line of the block and fails its coverage clause Env016Covers in ExecCoversW5"]
theorem env016_covers_unhandled :
    ENV_016 (RefExec (N := Nat) (T := Nat)) env016_unhandled ∧
      ¬ Env016Covers (env016_unhandled (N := Nat) (T := Nat)) := by
  refine ⟨fun _ => ⟨fun _ _ h => h.elim, fun _ _ h => h.elim, fun _ _ _ h => h.1.elim⟩,
    fun h => ?_⟩
  obtain ⟨_, hx⟩ := h env016_c .close env016_s0 env016_s0_running
  exact hx

/-! ### Violation: abandon closes the executor (line 1) -/

/-- An implementation that closes the executor whatever the policy. -/
def env016_abandonCloses {N T : Type} [DecidableEq N] : ExpiryRel N T :=
  fun _ _ s s' => s' = refExpiryStep s .close

/-- ✗ Closing under abandon violates ENV-016 (line 1, AC3 "under *abandon* it keeps running"):
an open executor is closed by an expiry under abandon. -/
@[evidence forbids ENV_016]
theorem ENV_016_forbids_abandonCloses :
    ¬ ENV_016 (RefExec (N := Nat) (T := Nat)) env016_abandonCloses := by
  intro h
  have h2 := (h env016_c).1 env016_s0 (refExpiryStep env016_s0 .close) rfl
  have hm := congrArg XSt.mode h2
  simp [refExpiryStep, closeStep, env016_s0, xinit] at hm

/-! ### Violation: the timer completes the loop's result (line 1) -/

/-- An implementation whose timer completes the loop's own result: under either policy the
run is reported finished (stopped) at the expiry, with the marking it had then. Java avoids this
by failing a copy of the loop's future (`loop.copy()` in `run(Duration, RunTimeoutPolicy)` of `BitmapNetExecutor`). -/
def env016_expiryCompletes {N T : Type} : ExpiryRel N T :=
  fun _ _ s s' => s' = { s with phase := .done .stopped }

/-- ✗ Completing the loop's result at the expiry violates ENV-016 (line 1, "MUST NOT complete
the loop's own result"): under abandon a running loop is finished by the expiry, so the
executor is not left as it was. -/
@[evidence forbids ENV_016]
theorem ENV_016_forbids_expiryCompletes :
    ¬ ENV_016 (RefExec (N := Nat) (T := Nat)) env016_expiryCompletes := by
  intro h
  have h2 := (h env016_c).1 env016_s0 { env016_s0 with phase := .done .stopped } rfl
  have hp := congrArg (fun s : XSt Nat Nat => isExecPhase s.phase) h2
  exact absurd hp (by decide)

/-! ### Violations: close is not the executor's close (line 2) -/

/-- An implementation that ignores the close policy and abandons (the default method of Java's
`PetriNetExecutor` interface, which delegates to `run(timeout)`). -/
def env016_closeIgnored {N T : Type} : ExpiryRel N T := fun _ _ s s' => s' = s

/-- ✗ Ignoring the close policy violates ENV-016 (line 2, AC3 "Under a *close* policy the
executor is closed on timeout"): the executor is open, and the expiry leaves it open. -/
@[evidence forbids ENV_016]
theorem ENV_016_forbids_closeIgnored :
    ¬ ENV_016 (RefExec (N := Nat) (T := Nat)) env016_closeIgnored := by
  intro h
  have h3 := ((h env016_c).2.1 env016_s0 env016_s0 rfl).1 (Or.inl rfl)
  have h3' : closeStep env016_s0 = some env016_s0 := h3
  have hm := congrArg (Option.map XSt.mode) h3'
  simp [closeStep, env016_s0, xinit] at hm

/-- An implementation whose close policy terminates the executor at once ([ENV-015]'s
`terminateNow`), without waiting for the firings in flight, instead of closing it. -/
def env016_closeTerminates {N T : Type} [DecidableEq N] : ExpiryRel N T :=
  fun _ pol s s' => match pol with
    | .abandon => s' = s
    | .close => s' = (terminateStep s).getD s

/-- ✗ Terminating instead of closing violates ENV-016 (line 2, "stop it per [ENV-013]"): the
expiry under close puts the open executor in the stopped mode, which no close step reaches. -/
@[evidence forbids ENV_016]
theorem ENV_016_forbids_closeTerminates :
    ¬ ENV_016 (RefExec (N := Nat) (T := Nat)) env016_closeTerminates := by
  intro h
  have h3 := ((h env016_c).2.1 env016_s0 ((terminateStep env016_s0).getD env016_s0) rfl).1
    (Or.inl rfl)
  have h3' : closeStep env016_s0 = some ((terminateStep env016_s0).getD env016_s0) := h3
  have hm := congrArg (Option.map XSt.mode) h3'
  simp [closeStep, terminateStep, env016_s0, xinit] at hm

/-- An executor that refuses `close()` while its loop runs: the reference, with no close step
from a state whose loop is running. The Java-shaped slip is `close()` opening with
`if (running) return;`; the TypeScript one is `close(): void { if (this.running) return; ... }`;
the channel-shaped one is a close signal sent without blocking and dropped when the channel is
full. -/
def env016_closeRefused {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => RefExec C s l s' ∧ (l = .close → isExecPhase s.phase = false)

/-- Its expiry, as a function: abandon changes nothing; close applies that executor's close step
when there is one, so once the loop has finished, and changes nothing otherwise. -/
def env016_closeRefusedStep {N T : Type} [DecidableEq N] (s : XSt N T) :
    TimeoutPolicy → XSt N T
  | .abandon => s
  | .close => if isExecPhase s.phase then s else (closeStep s).getD s

/-- Its expiry handling: the graph of `env016_closeRefusedStep`. -/
def env016_closeRefusedX {N T : Type} [DecidableEq N] : ExpiryRel N T :=
  fun _ pol s s' => s' = env016_closeRefusedStep s pol

/-- ✗ An executor that refuses a close while its loop runs violates ENV-016 (line 2,
"*shall* close the executor as a call of `close()` does ([ENV-013]), even while its loop is
running"): at the start of a run the executor is open and its loop is running, and the expiry
under close leaves it open, so the close policy acts as abandon. The expiry is its executor's own
close step whenever that executor offers one, so a line 2 that read "already closed or stopped"
as "R has no close step from s" would accept it; an expiry handling that gave this executor no
outcome there, instead of leaving it open, would meet line 2 and fail `Env016Covers`. -/
@[evidence forbids ENV_016]
theorem ENV_016_forbids_closeRefusedWhileRunning :
    ¬ ENV_016 (env016_closeRefused (N := Nat) (T := Nat)) env016_closeRefusedX := by
  intro h
  have hx0 : env016_closeRefusedX env016_c .close env016_s0 env016_s0 := by
    change env016_s0 = env016_closeRefusedStep env016_s0 .close
    simp only [env016_closeRefusedStep, env016_s0_running, if_true]
  obtain ⟨-, hx⟩ := ((h env016_c).2.1 env016_s0 env016_s0 hx0).1 (Or.inl rfl)
  rw [env016_s0_running] at hx
  exact absurd (hx rfl) (by decide)

/-! ### Violation: close finishes the run at the expiry (line 3) -/

/-- An executor whose close finishes the run at once, reporting the marking it has then and
abandoning its firings in flight; every other step is the reference's. -/
def env016_closeFinishesStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .close => (closeStep s).map fun s' => { s' with phase := .done .closed, eq := [] }
  | l => xstep C s l

/-- The executor of `env016_closeFinishesStep`. -/
def env016_closeFinishes {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env016_closeFinishesStep C s l = some s'

/-- Its expiry handling: abandon changes nothing, close is that executor's close step. -/
def env016_closeFinishesX {N T : Type} [DecidableEq N] : ExpiryRel N T :=
  fun C pol s s' => match pol with
    | .abandon => s' = s
    | .close => s' = (env016_closeFinishesStep C s .close).getD s

/-- ✗ A close that finishes the run at the expiry violates ENV-016 (line 3, "MUST NOT complete
the loop's own result"), although the expiry is that executor's own close step: the run is
reported finished, with the marking it had at the expiry. -/
@[evidence forbids ENV_016]
theorem ENV_016_forbids_closeFinishes :
    ¬ ENV_016 (env016_closeFinishes (N := Nat) (T := Nat)) env016_closeFinishesX := by
  intro h
  have h4 := (h env016_c).2.2 .close env016_s0
    ((env016_closeFinishesStep env016_c env016_s0 .close).getD env016_s0)
    ⟨rfl, env016_s0_running⟩
  exact absurd h4.1 (by decide)

/-! ### Every line exercised -/

/-- Every line of ENV-016 is exercised by the reference, on the test derivation's run with an
action in flight: (1) the loop blocks in its wait with the firing of `t` in flight and nothing
yet in place `1`, so it is running when the caller's timeout expires; the expiry under close has an outcome
(`Env016Covers`) and is RefExec's close step, which closes the executor (lines 2 and 3); the
expiry under abandon leaves the state as it is (line 1). (2) After the expiry under abandon, the action writes `7` to
place `1` and returns, its output is deposited, and the loop finishes quiescent with `7` in
place `1`: an abandoned loop reports its real final marking. (3) After the expiry under close,
the same action completes and the loop finishes closed with `7` in place `1` ([ENV-013]: the
executor terminates after its firings in flight complete). -/
@[evidence nonvacuous ENV_016]
theorem ENV_016_nonvacuous :
    (∃ s s', env016_at env016_toPark = some s ∧ isExecPhase s.phase = true ∧
      s.parked = true ∧ s.fl ≠ [] ∧ s.M 1 = [] ∧
      refExpiry env016_c .abandon s s ∧
      refExpiry env016_c .close s s' ∧ RefExec env016_c s .close s' ∧ s'.mode = .closed) ∧
    (∃ s, env016_after .abandon (env016_toTest ++ [.finish .quiescent]) = some s ∧
      s.phase = .done .quiescent ∧ s.M 1 = [7]) ∧
    (∃ s, env016_after .close (env016_toTest ++ [.finish .closed]) = some s ∧
      s.phase = .done .closed ∧ s.M 1 = [7]) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨s, ho, hp⟩ := env016_of_map (o := env016_at env016_toPark)
      (p := fun s => isExecPhase s.phase && s.parked && !s.fl.isEmpty && s.M 1 == [] &&
        (closeStep s).isSome && ((closeStep s).map (·.mode) == some .closed)) (by decide)
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, beq_iff_eq]
      at hp
    obtain ⟨⟨⟨⟨⟨hrun, hpk⟩, hfl⟩, hM⟩, hsome⟩, hmode⟩ := hp
    obtain ⟨s1, hs1⟩ := Option.isSome_iff_exists.mp hsome
    refine ⟨s, s1, ho, hrun, hpk, hfl, hM, rfl, ?_, hs1, ?_⟩
    · change s1 = (closeStep s).getD s
      rw [hs1]; rfl
    · rw [hs1] at hmode
      simpa using hmode
  · obtain ⟨s, ho, hp⟩ := env016_of_map
      (o := env016_after .abandon (env016_toTest ++ [.finish .quiescent]))
      (p := fun s => s.phase == .done .quiescent && s.M 1 == [7]) (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, ho, hp.1, hp.2⟩
  · obtain ⟨s, ho, hp⟩ := env016_of_map
      (o := env016_after .close (env016_toTest ++ [.finish .closed]))
      (p := fun s => s.phase == .done .closed && s.M 1 == [7]) (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, ho, hp.1, hp.2⟩

end Libpetri.Spec
