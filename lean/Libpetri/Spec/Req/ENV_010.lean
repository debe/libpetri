import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Exec

set_option linter.missingDocs true

/-!
# ENV-010: Implicit long-running behavior (`spec/06-environment-places.md`)

An executor with environment places does not end at quiescence while it is open and no terminal
place is marked, and it waits for external events instead: it answers and accepts an injection,
goes on from its termination test to its firing pass, injects what was accepted and leaves its
wait for it. The model is the executor model (`RefExec`, `Reference/Exec.lean`). The requirement
is a predicate over an abstract executor `R : XRel N T` (glossary `GlossaryExec.lean`) with two
lines, both on the steps `R` takes. The steps it offers (it answers and accepts an injection, goes
on from its termination test, injects and leaves its wait) are coverage: `Env010Covers`, a clause
of the consistency theorem's `ExecCoversW5`, never a line. The block is checked against the
reference executor and against two wrong executors that break a line (one that ends at quiescence
whatever is registered, the same executor as one that waits only when a separate long-running flag
is set, run with the flag unset, AC2; and one whose wait refuses injections as if it had ended).
Four more wrong executors are each the reference with one kind of step taken away: they meet both
lines and fail only the coverage clause (a mute wait, a hold at the termination test, a step 2
that never injects and a wait an arrival does not end). The TypeScript inject, which refuses at
the call once a terminal place is marked, is allowed.

Ruling D73 (a) gives the guard: the executor never ends at quiescence while environment places are
registered, the mode is open (not drained, closed or stopped) and no terminal place is marked; a
drain, a close, an immediate termination and a terminal place let it end ([ENV-011], [ENV-013],
[ENV-015], [EXEC-042]). Ruling D20 (ENVB-R7 item 1) and ruling D5 read quiescence with "armed",
as [EXEC-040] does.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## ENV-010: Implicit Long-Running Behavior -/

requirement ENV_010
  id "ENV-010"
  title "Implicit Long-Running Behavior"
  kind B
  scope "executors with environment places"
  source verbatim "spec/06-environment-places.md"
  quote "When environment places are registered with the executor, the executor does NOT terminate at quiescence (no transition armed, no firing in flight, and no completion, publication or external event queued, as in [EXEC-040]) while it has not been drained ([ENV-011]), closed ([ENV-013]) or stopped by an immediate termination ([ENV-015]) and no terminal place is marked ([EXEC-042])."
        "Instead, it waits for external events that may enable new transitions."
        "This behavior is derived from the presence of environment places: no explicit flag is needed."
        "*While* environment places are registered, the executor is open (it has not been drained, closed or stopped by an immediate termination) and no terminal place is marked ([EXEC-042]), the executor *shall not* terminate as quiescent ([EXEC-041])."
        "*While* environment places are registered, the executor is open and running and no terminal place is marked, *when* a caller asks to inject a token into a registered environment place, the executor *shall* answer the request and *shall* accept the injection."
        "*While* environment places are registered, the executor is open and no terminal place is marked, *when* the loop reaches its termination test ([EXEC-040]), the executor *shall* go on to its firing pass ([EXEC-001])."
        "*While* environment places are registered, the executor is open and no terminal place is marked, *when* an accepted injection is queued, the executor *shall* leave its wait ([ENV-005]) and *shall* inject the oldest queued injection in its event step ([ENV-003])."
        "The executor *shall not* need a long-running flag or any setting other than the registered environment places to wait at quiescence."
  reading "For every executor R and every configuration C that registers at least one environment place:"
          "(1) while no terminal place is marked and the executor's mode is open (not draining, closed or stopped), R takes no finish quiescent step;"
          "(2) on every request step of R that asks to inject into a registered environment place while no terminal place is marked, the mode is open and the run has not finished, the reply is accepted."
  assumes "The model is an executor R : XRel N T (glossary GlossaryExec.lean): R C s l s' says that under configuration C the step labelled l leads from executor state s to s'. The registered environment places are C.envs (glossary: Environment place, ENV-001); 'environment places are registered' is C.envs ≠ []. The run has not finished ('running') while its phase is not done (isExecPhase), and a run ends with a step finish c, where c is the termination cause of EXEC-041; 'terminate as quiescent' is finish quiescent. A request step request p x r is a caller asking to inject x into p and getting the reply r (accepted, refused or error). The mode is open until a drain (draining, ENV-011), a close (closed, ENV-013) or an immediate termination (stopped, ENV-015): 'open (it has not been drained, closed or stopped by an immediate termination)' is mode = open. 'No terminal place is marked' is the glossary term Live. 'The termination test' is the phase test, 'its firing pass' is the phase pass that the step begin enters, 'its wait' is the phase await (step 6), 'its event step' is the phase events (step 2), and the queued injections are the event queue eq, oldest first. The witness is the reference executor RefExec (Reference/Exec.lean), checked rule by rule against the Rust executor: the termination checks of executor_core/executor.rs (1084-1095), the exit test of the wait (1137-1143) and ExecutorHandle::inject (executor_handle.rs 67-74); and against Java and TypeScript, whose shouldTerminate (BitmapNetExecutor.java 1264-1276, bitmap-net-executor.ts 697-711) ends an executor with environment places only when draining or closed."
          "Guard (ruling D73 (a)). Line 1 forbids only the quiescent finish, which is what the requirement is about. The other causes are tied to their own conditions by EXEC-041 (finish closed only once closed or stopped, finish stopped only once stopped, finish terminal only with a terminal place marked, and no step but a finish ends the run), so an executor that meets EXEC-041 and line 1 does not end at all under the guard. The reference offers no finish of any cause there. The guard is the open mode and not the registered places alone: a drained executor with environment places ends at quiescence (ENV-011), which line 1 allows (ENV_010_allows_drainedQuiescence). A marked terminal place ends the run whatever is registered (EXEC-042), which is why both lines and the coverage clause carry Live. Runtime exits that sit outside the guard: in Rust an executor whose signal channel has closed, every sender dropped, accepts no injection and ends at quiescence as a drained one does (dropping an ExecutorHandle sends a drain first), which is a drain in the model; Rust's run_sync has no signal channel and accepts no injection, so it is not an executor this requirement binds; a Java interrupt taken while the loop waits ends the run as interrupted, a cause EXEC-041 keeps out of the model (N), as are faults of the host runtime."
          "Quiescence (rulings D5, D13 (a) and D20, ENVB-R7 item 1) is EXEC-040's rest: no transition armed, no firing in flight, no completion, publication or external event queued (Rest of GlossaryExec). A reaped transition that is still enabled does not count. Line 1 does not need the term: it forbids the quiescent finish in every state under the guard, at rest or not, and EXEC-040 and EXEC-041 already allow that finish only at rest."
          "The first shall sentence and the first quoted body sentence are line 1, and so is AC3 (an executor with environment places does not terminate at quiescence). ENV_010_forbids_quiesceAnyway is an executor that ends at quiescence whatever is registered: started with an environment place and nothing to do, it ends at its first termination test."
          "The second shall sentence is line 2 and the first part of Env010Covers: the request is answered (the clause, a step that is offered in every state under the guard) and the answer is an acceptance (line 2). Line 2 alone does not make the executor answer, since it speaks only of the request steps R takes; the clause does. ENV_010_forbids_deafWait answers an injection refused while its wait is parked, as if it had ended (it breaks line 2). env010_covers_muteWait does not answer at all while parked, so the caller can not inject (it meets both lines and fails the first part of the clause). Line 2 and the clause carry Live: once a terminal place is marked the run is about to end with finish terminal (EXEC-042), and what a request there gets is ENV-006's, where the reference accepts it and the finish answers it false, and TypeScript refuses it at the call (bitmap-net-executor.ts 611 and 652, the terminalReached test). The caller learns false either way, and ENV_010_allows_terminalRefusal shows that ENV-010 allows the TypeScript shape."
          "AC1 and the sentence 'Instead, it waits for external events that may enable new transitions.' are line 1 together with the first two parts of Env010Covers: at quiescence the executor does not end (line 1), goes on from its termination test to its firing pass (the second part), whose end leads to the wait (EXEC-001, CONC-010), and accepts a caller's injection there (the first part). The third shall sentence is the second part. env010_covers_hold is an executor that holds at its termination test once its only work is queued injections: it accepts every request and never goes on to inject them (it meets both lines and fails the second part). That the end of the pass leads to the park (endPass, park) is EXEC-001's and CONC-010's."
          "AC5 (injecting a token resumes execution from quiescence) and the fourth shall sentence are the first, third and fourth parts of Env010Covers: the injection is accepted while the executor idles (the first part), the wait does not stay idle with an injection queued, it wakes or injects (the fourth part), and step 2 injects the oldest queued injection (the third part). env010_covers_stuckWait is a wait that an arrival does not end, and env010_covers_noInject a step 2 that never injects; each meets both lines and fails its part of the clause. What the inject step does to the queue and the marking is ENV-003's, that an accepted request clears the park is ENV-005's (CONC-010), and that the injected token arms the transition it enables is the injected-token clause of TIME-010 and TIME-013 (the inject step writes its place, ruling D6). ENV_010_nonvacuous decides the test derivation on the reference: an executor with one environment place reaches a test at rest and does not end, parks, accepts an injection while parked, injects it, fires the transition it enables, reaches a test at rest again and does not end, is drained, and then ends quiescent with the token moved."
          "AC2, the fifth shall sentence and the body sentence on the flag: the only premise on the configuration, of the statement and of Env010Covers, is C.envs ≠ [], and the configuration has no long-running field, so the waiting is derived from the registered places alone. An executor that waits only when a separate long-running flag is set (env010_flagStep) is the reference when the flag is set (env010_flagStep_true) and the quiesceAnyway executor when it is not, so with the flag at its unset default it is forbidden (ENV_010_forbids_quiesceAnyway). An executor with such a flag set by default meets the statement; that no such flag exists on the executor API is API shape (kind Q), with no Lean witness beyond the unset flag: Rust derives the waiting from the registered set (rust/libpetri-runtime/src/executor.rs 142), Java and TypeScript from the environment places given to the builder (BitmapNetExecutor.java 351, bitmap-net-executor.ts 345)."
          "AC4 and the sentence 'When no environment places are registered, the executor terminates at quiescence per [EXEC-040].' belong to EXEC-040, whose block is premised on C.envs = [], the complement of this block's premise. env010_finish_iff_noEnvs is the bridge on the reference: at a termination test at rest, with no terminal place marked and the mode open, a finish quiescent step is offered exactly when no environment place is registered. ENV_010_allows_noEnvQuiescence shows the same net without environment places ending at its first test."
          "Its offers are in ExecCoversW5.Env010Covers (ConsistencyExec.lean; the convention of GlossaryExec.lean: offers are coverage clauses, never block lines), as ENV-002's are in Env002Covers. The second, third and fourth EARS sentences demand an answer and are quoted whole; the safety half of the second is line 2, and their existence halves are that clause: in every state where environment places are registered, no terminal place is marked and the mode is open, R offers the accepted request, the begin step at the test, the inject step in step 2 and the way out of the wait. The clause reads every such state, reachable or not, and the reference meets it (env010_ref_covers). Requests into a place that is not an environment place are ENV-002's (Java and TypeScript answer error, Rust and Python deposit, ruling D89 (a)); line 2 and the first part of Env010Covers speak only of registered environment places, where all four runtimes accept. Requests while draining, closed, stopped or after the finish are refused (ENV-006, ENV-011, ENV-013). Injections before the run starts are outside the model, whose runs start at xinit in mode open."
  signoff "pending"
  statement : ∀ {N T : Type} [DecidableEq N], XRel N T → Prop :=
    fun R => ∀ C, C.envs ≠ [] →
      (while (fun s => Live C s ∧ s.mode = .open), never (fun s s' =>
        R C s (.finish .quiescent) s')) ∧
      (∀ p x r, on (fun s s' => R C s (.request p x r) s' ∧ p ∈ C.envs ∧ Live C s ∧
          s.mode = .open ∧ isExecPhase s.phase = true),
        shall (fun _ _ => r = .accepted))

/- The pinned readable form of ENV-010: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.ENV_010 : {N T : Type} → [DecidableEq N] → XRel N T → Prop :=
fun {N T} [DecidableEq N] R =>
  ∀ (C : Cfg N T),
    C.envs ≠ [] →
      (while fun s => Live C s ∧ s.mode = Mode.open, never fun s s' => R C s (XLbl.finish Cause.quiescent) s') ∧
        ∀ (p : N) (x : T) (r : Reply),
          on fun s s' =>
            R C s (XLbl.request p x r) s' ∧ p ∈ C.envs ∧ Live C s ∧ s.mode = Mode.open ∧ isExecPhase s.phase = true,
            shall fun x x_1 => r = Reply.accepted
-/
#guard_msgs in #print ENV_010

/-! ### The reference -/

section Reference

variable {N T : Type} [DecidableEq N]

/-- The executor with judgement points `P` meets ENV-010. Line 1: `finish quiescent` requires
`finishQ`, whose second conjunct fails while environment places are registered and the mode is
open (`xstepW_finishQuiescent`). Line 2: the reply to a request is `replyFor`, which accepts an
environment place while the mode is open and the run has not finished (`requestStep_some`). -/
theorem env010_xstepW (P : XPol N T) :
    ENV_010 (fun C s l s' => xstepW P C s l = some s') := by
  intro C hE
  refine ⟨?_, ?_⟩
  · rintro s s' h ⟨-, hm⟩
    have hq := (xstepW_finishQuiescent h).2.2.1
    simp [finishQ, hm, hE] at hq
  · rintro p x r s s' ⟨h, hp, -, hm, hx⟩
    have hr := (requestStep_some (C := C) h).1
    simp [hr, replyFor, hp, hm, hx]

end Reference

/-- ✓ The reference executor satisfies ENV-010 (`env010_xstepW` at `refXPol`). -/
@[evidence holds ENV_010]
theorem ENV_010_reference {N T : Type} [DecidableEq N] :
    ENV_010 (RefExec (N := N) (T := T)) :=
  env010_xstepW refXPol

/-- **The coverage conjunct ENV-010 asks of the consistency theorem's `ExecCoversW5`**: in every
state of an executor with environment places registered, where no terminal place is marked and the
mode is open, (1) while the run has not finished, `E` has a request step into every registered
environment place whose reply is accepted (the second EARS sentence); (2) at the termination test,
`E` has a begin step, the start of its firing pass (the third EARS sentence); (3) in step 2 with an
injection queued, `E` has an inject step for the oldest one, and (4) in the wait with an injection
queued, `E` has a wake step or an inject step that leaves the wait (the fourth EARS sentence).
Offers are never a line of a block (glossary `GlossaryExec.lean`). -/
def Env010Covers {N T : Type} (E : XRel N T) : Prop :=
  ∀ C, C.envs ≠ [] → ∀ s, Live C s → s.mode = .open →
    (∀ p x, p ∈ C.envs → isExecPhase s.phase = true →
      ∃ s', E C s (.request p x .accepted) s') ∧
    (s.phase = .test → ∃ s', E C s .begin s') ∧
    (∀ k p x rest, s.phase = .events → s.eq = (k, p, x) :: rest →
      ∃ s', E C s (.inject k) s') ∧
    (s.phase = .await → s.eq ≠ [] →
      ∃ s', (E C s .wake s' ∨ ∃ k, E C s (.inject k) s') ∧ s'.phase ≠ .await)

/-- The executor with judgement points `P` meets ENV-010's coverage conjunct: under the guard the
request, `begin`, `inject` (step 2, with the queue's head) and `wake` rules all fire. -/
theorem env010_xstepW_covers {N T : Type} [DecidableEq N] (P : XPol N T) :
    Env010Covers (fun C s l s' => xstepW P C s l = some s') := by
  intro C hE s hL hm
  have hl : liveB C s = true := hL
  refine ⟨fun p x hp hx => ?_, fun hph => ?_, fun k p x rest hph heq => ?_, fun hph _ => ?_⟩
  · exact ⟨_, by simp [xstepW, requestStep, replyFor, hp, hm, hx]; rfl⟩
  · exact ⟨_, by simp [xstepW, hph, hl, finishQ, hm, hE, Mode.closing]; rfl⟩
  · exact ⟨_, by simp [xstepW, injectStep, heq, hl, hph, hm, Mode.closing]; rfl⟩
  · exact ⟨{ s with phase := .completions, parked := false },
      Or.inl (by simp [xstepW, wakeStep, hph, hl]), by simp⟩

/-- The reference meets ENV-010's coverage conjunct (`env010_xstepW_covers` at `refXPol`). -/
theorem env010_ref_covers {N T : Type} [DecidableEq N] :
    Env010Covers (RefExec (N := N) (T := T)) :=
  env010_xstepW_covers refXPol

/-! ### Every line reads only states where no terminal place is marked -/

section Live

variable {N T : Type} [DecidableEq N]

/-- Both lines of ENV-010 are guarded by `Live`, so an executor that agrees with the reference at
every state where no terminal place is marked meets ENV-010, whatever it does once one is. -/
theorem env010_of_live {E : XRel N T}
    (h : ∀ C s l s', Live C s → (E C s l s' ↔ RefExec C s l s')) : ENV_010 E := by
  intro C hE
  obtain ⟨h1, h2⟩ := ENV_010_reference (N := N) (T := T) C hE
  exact ⟨fun s s' hs g => h1 s s' ((h C s _ s' g.1).1 hs) g,
    fun p x r s s' ⟨hs, hp, hl, hm, hx⟩ => h2 p x r s s' ⟨(h C s _ s' hl).1 hs, hp, hl, hm, hx⟩⟩

end Live

/-! ### The bridge to EXEC-040 -/

section Bridge

variable {N T : Type} [DecidableEq N]

/-- **The bridge to EXEC-040** (AC4): at a termination test at rest, with no terminal place marked
and the mode open, the reference offers a finish quiescent step exactly when no environment place
is registered. The registered places decide between ending and waiting, and nothing else does
(AC2). -/
theorem env010_finish_iff_noEnvs (C : Cfg N T) (s : XSt N T) (hL : Live C s)
    (hp : s.phase = .test) (hr : Rest C s) (hm : s.mode = .open) :
    (∃ s', RefExec C s (.finish .quiescent) s') ↔ C.envs = [] := by
  have hl : liveB C s = true := hL
  have hr' : restB C s = true := hr
  constructor
  · rintro ⟨s', h⟩
    have hq := (xstepW_finishQuiescent h).2.2.1
    simpa [finishQ, hm, hr'] using hq
  · intro hE
    exact ⟨{ s with phase := .done .quiescent, eq := [] }, by
      simp [RefExec, xstep, xstepW, hp, hl, finishQ, hr', hE]⟩

end Bridge

/-! ### Examples

One environment place `0` and one Immediate transition `t : 0 → 1`; validation and the relay check
accept everything (they are EXEC-021's subject); no terminal place. The marking starts empty. -/

/-- The transition `t`: one token from the environment place `0`, output spec `Out.place 1`. -/
def env010_t : Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 1) }

/-- The configuration of the examples, with environment places `envs`. -/
def env010_cfgOf (envs : List Nat) : Cfg Nat Nat :=
  { X := { net := { places := [0, 1], transitions := [env010_t] }, timing := fun _ => .immediate,
           tol := 0 },
    prio := fun _ => 0, terminals := [], envs := envs, reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true,
    timeoutOut := fun _ _ _ => false, res := 0 }

/-- Place `0` registered as an environment place. -/
def env010_cfg : Cfg Nat Nat := env010_cfgOf [0]

/-- The same net with no environment place. -/
def env010_cfg0 : Cfg Nat Nat := env010_cfgOf []

/-- The environment place `0` is registered in `env010_cfg`. -/
theorem env010_cfg_envs : env010_cfg.envs ≠ [] := by simp [env010_cfg, env010_cfgOf]

/-- The empty initial marking. -/
def env010_m0 : QMarking Nat Nat := fun _ => []

/-- Steps 1 to 4 of a cycle with nothing queued, up to the termination test. -/
def env010_toTest : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline []]

/-- From the first test to the park: an empty firing pass, then the wait with no timer. -/
def env010_toPark : List (XLbl Nat Nat) := env010_toTest ++ [.begin, .endPass, .park none]

/-- Parked, then a caller injects `5` into `0` (ticket `0`): the loop is in its wait, no longer
parked, with the injection queued. -/
def env010_queued : List (XLbl Nat Nat) := env010_toPark ++ [.request 0 5 .accepted]

/-- From there the wait wakes and the loop runs steps 1 and 1b: it is in step 2 with the
injection queued. -/
def env010_toEvents : List (XLbl Nat Nat) :=
  env010_queued ++ [.wake, .endCompletions, .endPublications]

/-- Up to the second termination test: while parked a caller injects `5` into `0` (ticket `0`),
the wait injects it and goes back to step 1, `t` starts (firing `1`), its action writes `5` to `1`
and returns, the completion is committed, and the next cycle reaches its test. -/
def env010_afterFire : List (XLbl Nat Nat) :=
  env010_queued ++ [.inject 0] ++ env010_toTest ++
    [.begin, .start "t" false, .endPass, .write 1 1 5, .ret 1 true, .commit 1] ++ env010_toTest

/-- The test derivation: after every transition fired the executor is still running; it is
drained, wakes, and ends quiescent at its next test. -/
def env010_full : List (XLbl Nat Nat) :=
  env010_afterFire ++ [.begin, .endPass, .drain, .wake] ++ env010_toTest ++ [.finish .quiescent]

/-- Read a decided fact off a state: if the check `p` of the state `o` evaluates to `true`, the
state exists. -/
theorem env010_state_of_check {N T : Type} {o : Option (XSt N T)} {p : XSt N T → Bool}
    (h : o.map p = some true) : ∃ s, o = some s ∧ p s = true := by
  cases ho : o with
  | none => simp [ho] at h
  | some s => simp only [ho, Option.map_some, Option.some.injEq] at h; exact ⟨s, rfl, h⟩

/-! ### Violation: ending at quiescence whatever is registered (line 1; AC1, AC2, AC3) -/

/-- The finish premise of an executor that waits only when a long-running flag `lr` is set: rest,
and the flag unset, or no environment place, or the mode not open. -/
def env010_finishQ {N T : Type} (lr : Bool) (C : Cfg N T) (s : XSt N T) : Bool :=
  restB C s && (!lr || C.envs.isEmpty || s.mode != .open)

/-- An executor with a long-running flag `lr`: it waits at quiescence with environment places only
when the flag is set; every rule but the finish quiescent and begin premises is the reference's.
With the flag unset it ends at quiescence whatever is registered. -/
def env010_flagStep {N T : Type} [DecidableEq N] (lr : Bool) (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .finish .quiescent =>
    if s.phase = .test && liveB C s && env010_finishQ lr C s then
      some { s with phase := .done .quiescent, eq := [] } else none
  | .begin =>
    if s.phase = .test && liveB C s && !env010_finishQ lr C s &&
        !(s.mode.closing && s.fl.isEmpty) then
      some { s with phase := .pass, order := readyOrder C s, delta := fun _ => 0,
                    started := false }
    else none
  | l => xstep C s l

/-- With the flag set, the flag executor is the reference. -/
theorem env010_flagStep_true {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T)
    (l : XLbl N T) : env010_flagStep true C s l = xstep C s l := by
  cases l with
  | finish c => cases c <;> simp [env010_flagStep, env010_finishQ, xstep, xstepW, finishQ]
  | begin => simp [env010_flagStep, env010_finishQ, xstep, xstepW, finishQ]
  | _ => rfl

/-- ✗ An executor that ends at quiescence whatever is registered (the flag executor with its flag
unset) violates ENV-010 (line 1): started with the environment place `0` and nothing to do, it
ends at its first termination test, with the mode open. -/
@[evidence forbids ENV_010]
theorem ENV_010_forbids_quiesceAnyway :
    ¬ ENV_010 (fun C s l s' => env010_flagStep (N := Nat) (T := Nat) false C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check (env010_flagStep false) (C := env010_cfg)
    (o := xrun env010_cfg (xinit env010_m0 0) env010_toTest) (l := .finish .quiescent)
    (p := fun s _ => liveB env010_cfg s && decide (s.mode = .open)) (by decide)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  exact (h env010_cfg env010_cfg_envs).1 s s' hs ⟨hp.1, hp.2⟩

/-! ### Violation: a deaf wait (line 2; AC1, AC5) -/

/-- An executor whose wait is deaf: parked at quiescence, it answers every injection into an
environment place refused, as if it had ended; every other rule is the reference's. -/
def env010_deafStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .request p x r =>
    if s.parked = true ∧ p ∈ C.envs then (if r = .refused then some s else none)
    else requestStep C s p x r
  | l => xstep C s l

/-- ✗ A deaf wait violates ENV-010 (line 2): the executor with the environment place `0` parks at
quiescence with the mode open and no terminal place marked, and a caller's injection into `0` is
refused. -/
@[evidence forbids ENV_010]
theorem ENV_010_forbids_deafWait :
    ¬ ENV_010 (fun C s l s' => env010_deafStep (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env010_deafStep (C := env010_cfg)
    (o := xrun env010_cfg (xinit env010_m0 0) env010_toPark) (l := .request 0 5 .refused)
    (p := fun s _ => liveB env010_cfg s && decide (s.mode = .open) && isExecPhase s.phase)
    (by decide)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  have := (h env010_cfg env010_cfg_envs).2 0 5 .refused s s'
    ⟨hs, by simp [env010_cfg, env010_cfgOf], hp.1.1, hp.1.2, hp.2⟩
  cases this

/-! ### Coverage: the reference with one kind of step taken away (Env010Covers)

Each is a sub-relation of the reference, so it meets both lines, which speak only of the steps an
executor takes; each fails the one part of the coverage clause `Env010Covers` that names the step
it lacks. -/

section Without

variable {N T : Type} [DecidableEq N]

/-- The reference without the steps that `bad` marks. -/
def env010_without (bad : Cfg N T → XSt N T → XLbl N T → Bool) : XRel N T :=
  fun C s l s' => bad C s l = false ∧ RefExec C s l s'

/-- Every sub-relation of the reference meets ENV-010. -/
theorem env010_without_meets (bad : Cfg N T → XSt N T → XLbl N T → Bool) :
    ENV_010 (env010_without bad) := by
  intro C hE
  obtain ⟨h1, h2⟩ := ENV_010_reference (N := N) (T := T) C hE
  exact ⟨fun s s' h g => h1 s s' h.2 g,
    fun p x r s s' ⟨h, hrest⟩ => h2 p x r s s' ⟨h.2, hrest⟩⟩

/-- A mute wait (Java's or TypeScript's inject whose future or promise the loop never completes
while it is parked): no request into an environment place is answered while parked. -/
def env010_muteBad : Cfg N T → XSt N T → XLbl N T → Bool
  | C, s, .request p _ _ => s.parked && decide (p ∈ C.envs)
  | _, _, _ => false

/-- A hold at the termination test (an idle test that reads the transitions and the firings in
flight, not the event queue): with nothing in flight and an injection queued, no firing pass
begins. -/
def env010_holdBad : Cfg N T → XSt N T → XLbl N T → Bool
  | _, s, .begin => !s.eq.isEmpty && s.fl.isEmpty
  | _, _, _ => false

/-- A step 2 that never injects (the queue read only in the wait, never at the top of the
loop). -/
def env010_noInjectBad : Cfg N T → XSt N T → XLbl N T → Bool
  | _, s, .inject _ => decide (s.phase = .events)
  | _, _, _ => false

/-- A wait that an arrival does not end (a wait condition that reads the firings in flight but not
the event queue): in the wait with an injection queued, neither a wake nor an inject. -/
def env010_stuckBad : Cfg N T → XSt N T → XLbl N T → Bool
  | _, s, .wake => decide (s.phase = .await) && !s.eq.isEmpty
  | _, s, .inject _ => decide (s.phase = .await) && !s.eq.isEmpty
  | _, _, _ => false

end Without

/-- The answer is coverage, not a line: a mute wait meets every line of ENV-010 (it answers nothing
it should not) and fails the first part of its coverage conjunct `Env010Covers`. Parked at
quiescence, with the mode open and no terminal place marked, it has no request step into the
environment place `0`, so a caller can not inject. -/
@[evidence cites "ENV-010" "when a caller asks to inject a token into a registered environment place, the executor shall answer the request and shall accept the injection: a wait that answers no request while parked meets every line of the block and fails its coverage clause Env010Covers in ExecCoversW5"]
theorem env010_covers_muteWait :
    ENV_010 (env010_without (env010_muteBad (N := Nat) (T := Nat))) ∧
      ¬ Env010Covers (env010_without (env010_muteBad (N := Nat) (T := Nat))) := by
  refine ⟨env010_without_meets _, fun h => ?_⟩
  obtain ⟨s, -, hp⟩ := env010_state_of_check
    (o := xrun env010_cfg (xinit env010_m0 0) env010_toPark)
    (p := fun s => s.parked && liveB env010_cfg s && decide (s.mode = .open) &&
      isExecPhase s.phase) (by decide)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨⟨hpk, hl⟩, hm⟩, hx⟩ := hp
  obtain ⟨-, hb, -⟩ := (h env010_cfg env010_cfg_envs s hl hm).1 0 5
    (by simp [env010_cfg, env010_cfgOf]) hx
  simp [env010_muteBad, hpk, env010_cfg, env010_cfgOf] at hb

/-- Going on from the test is coverage, not a line: an executor that holds at its termination test
once its only work is a queued injection meets every line of ENV-010 and fails the second part of
its coverage conjunct `Env010Covers`. At its first test a caller injects into `0`; with the mode
open and no terminal place marked, no firing pass begins. -/
@[evidence cites "ENV-010" "when the loop reaches its termination test, the executor shall go on to its firing pass: an executor that holds at its test with only queued injections to do meets every line of the block and fails its coverage clause Env010Covers in ExecCoversW5"]
theorem env010_covers_hold :
    ENV_010 (env010_without (env010_holdBad (N := Nat) (T := Nat))) ∧
      ¬ Env010Covers (env010_without (env010_holdBad (N := Nat) (T := Nat))) := by
  refine ⟨env010_without_meets _, fun h => ?_⟩
  obtain ⟨s, -, hp⟩ := env010_state_of_check
    (o := xrun env010_cfg (xinit env010_m0 0) (env010_toTest ++ [.request 0 5 .accepted]))
    (p := fun s => decide (s.phase = .test) && liveB env010_cfg s && decide (s.mode = .open) &&
      !s.eq.isEmpty && s.fl.isEmpty) (by decide)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨⟨⟨hph, hl⟩, hm⟩, hq⟩, hfl⟩ := hp
  obtain ⟨-, hb, -⟩ := (h env010_cfg env010_cfg_envs s hl hm).2.1 hph
  simp [env010_holdBad, hq, hfl] at hb

/-- The injection in step 2 is coverage, not a line: an executor whose step 2 never injects meets
every line of ENV-010 and fails the third part of its coverage conjunct `Env010Covers`. Parked, a
caller injects into `0`, the wait wakes and the loop reaches step 2 with the injection queued, the
mode open and no terminal place marked; it has no inject step. -/
@[evidence cites "ENV-010" "when an accepted injection is queued, the executor shall inject the oldest queued injection in its event step: an executor whose step 2 never injects meets every line of the block and fails its coverage clause Env010Covers in ExecCoversW5"]
theorem env010_covers_noInject :
    ENV_010 (env010_without (env010_noInjectBad (N := Nat) (T := Nat))) ∧
      ¬ Env010Covers (env010_without (env010_noInjectBad (N := Nat) (T := Nat))) := by
  refine ⟨env010_without_meets _, fun h => ?_⟩
  obtain ⟨s, -, hp⟩ := env010_state_of_check
    (o := xrun env010_cfg (xinit env010_m0 0) env010_toEvents)
    (p := fun s => decide (s.phase = .events) && liveB env010_cfg s && decide (s.mode = .open) &&
      decide (s.eq = [(0, 0, 5)])) (by decide)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨⟨hph, hl⟩, hm⟩, hq⟩ := hp
  obtain ⟨-, hb, -⟩ := (h env010_cfg env010_cfg_envs s hl hm).2.2.1 0 0 5 [] hph hq
  simp [env010_noInjectBad, hph] at hb

/-- Leaving the wait is coverage, not a line: a wait that an arrival does not end meets every line
of ENV-010 and fails the fourth part of its coverage conjunct `Env010Covers`. Parked, a caller
injects into `0`; with the injection queued, the mode open and no terminal place marked, the wait
neither wakes nor injects. -/
@[evidence cites "ENV-010" "when an accepted injection is queued, the executor shall leave its wait: a wait that an arrival does not end meets every line of the block and fails its coverage clause Env010Covers in ExecCoversW5"]
theorem env010_covers_stuckWait :
    ENV_010 (env010_without (env010_stuckBad (N := Nat) (T := Nat))) ∧
      ¬ Env010Covers (env010_without (env010_stuckBad (N := Nat) (T := Nat))) := by
  refine ⟨env010_without_meets _, fun h => ?_⟩
  obtain ⟨s, -, hp⟩ := env010_state_of_check
    (o := xrun env010_cfg (xinit env010_m0 0) env010_queued)
    (p := fun s => decide (s.phase = .await) && liveB env010_cfg s && decide (s.mode = .open) &&
      !s.eq.isEmpty) (by decide)
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff]
    at hp
  obtain ⟨⟨⟨hph, hl⟩, hm⟩, hq⟩ := hp
  obtain ⟨s', hs, -⟩ := (h env010_cfg env010_cfg_envs s hl hm).2.2.2 hph hq
  rcases hs with ⟨hb, -⟩ | ⟨k, hb, -⟩
  · simp [env010_stuckBad, hph, hq] at hb
  · simp [env010_stuckBad, hph, hq] at hb

/-! ### Allowed: the TypeScript inject refuses once a terminal place is marked (ENV-006) -/

/-- The TypeScript inject (`if (this.closed || this.draining || this.terminalReached) return
false;`, bitmap-net-executor.ts 611 and 652): a request into an environment place while a terminal
place is marked, the mode open and the run not finished is refused; every other rule is the
reference's. -/
def env010_tsStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .request p x r =>
    if p ∈ C.envs ∧ liveB C s = false ∧ s.mode = .open ∧ isExecPhase s.phase = true then
      (if r = .refused then some s else none)
    else requestStep C s p x r
  | l => xstep C s l

/-- Where no terminal place is marked, the TypeScript executor is the reference. -/
theorem env010_tsStep_live {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T)
    (l : XLbl N T) (hL : Live C s) : env010_tsStep C s l = xstep C s l := by
  have hl : liveB C s = true := hL
  cases l with
  | request p x r => simp [env010_tsStep, hl, xstep, xstepW]
  | _ => rfl

/-- The configuration of the examples with place `1` terminal. -/
def env010_cfgT : Cfg Nat Nat := { env010_cfg with terminals := [1] }

/-- Park, accept `5` into `0`, inject it, fire `t`, which deposits into the terminal place `1` on
its commit: the state right after the terminal deposit, still in step 1. -/
def env010_toTerminal : List (XLbl Nat Nat) :=
  env010_queued ++ [.inject 0] ++ env010_toTest ++
    [.begin, .start "t" false, .endPass, .write 1 1 5, .ret 1 true, .commit 1]

/-- ✓ ENV-010 allows the TypeScript inject: it meets every line (each is guarded by `Live`, and
where no terminal place is marked it is the reference), and right after the terminal deposit, with
the mode open and the run not finished, it refuses a request into `0` that the reference accepts
(ENV-006: the finish that follows answers the reference's acceptance false, so the caller learns
the same). -/
@[evidence allows ENV_010]
theorem ENV_010_allows_terminalRefusal :
    ENV_010 (fun C s l s' => env010_tsStep (N := Nat) (T := Nat) C s l = some s') ∧
      ∃ s s', env010_tsStep env010_cfgT s (.request 0 6 .refused) = some s' ∧
        ¬ Live env010_cfgT s ∧ s.mode = .open ∧ isExecPhase s.phase = true ∧
        ∃ s'', RefExec env010_cfgT s (.request 0 6 .accepted) s'' := by
  refine ⟨env010_of_live fun C s l s' hl => by
    simp only [RefExec, env010_tsStep_live C s l hl], ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env010_tsStep (C := env010_cfgT)
    (o := xrun env010_cfgT (xinit env010_m0 0) env010_toTerminal) (l := .request 0 6 .refused)
    (p := fun s _ => !liveB env010_cfgT s && decide (s.mode = .open) && isExecPhase s.phase &&
      (xstep env010_cfgT s (.request 0 6 .accepted)).isSome) (by decide)
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    Option.isSome_iff_exists] at hp
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hp
  exact ⟨s, s', hs, by simp [Live, h1], h2, h3, h4⟩

/-! ### Allowed: without environment places the executor ends at quiescence (AC4) -/

/-- ✓ ENV-010 allows the end at quiescence without environment places: the reference satisfies it,
and the same net with no environment place, started with nothing to do, ends quiescent at its first
termination test, at rest, with no terminal place marked and the mode open ([EXEC-040]). -/
@[evidence allows ENV_010]
theorem ENV_010_allows_noEnvQuiescence :
    ENV_010 (RefExec (N := Nat) (T := Nat)) ∧
      ∃ s s', RefExec env010_cfg0 s (.finish .quiescent) s' ∧ env010_cfg0.envs = [] ∧
        Live env010_cfg0 s ∧ s.mode = .open ∧ Rest env010_cfg0 s := by
  refine ⟨ENV_010_reference, ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env010_cfg0)
    (o := xrun env010_cfg0 (xinit env010_m0 0) env010_toTest) (l := .finish .quiescent)
    (p := fun s _ => liveB env010_cfg0 s && decide (s.mode = .open) && restB env010_cfg0 s)
    (by decide)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  exact ⟨s, s', hs, rfl, hp.1.1, hp.1.2, hp.2⟩

/-! ### Allowed: a drained executor with environment places ends at quiescence (ruling D73 (a)) -/

/-- ✓ ENV-010 allows a drained executor with environment places to end at quiescence (the guard
is the open mode, not the registered places alone; [ENV-011]): the reference satisfies it, and on
the test derivation, after the drain, the executor with the environment place `0` ends quiescent
at its next termination test, with the mode draining and the token in `1`. -/
@[evidence allows ENV_010]
theorem ENV_010_allows_drainedQuiescence :
    ENV_010 (RefExec (N := Nat) (T := Nat)) ∧
      ∃ s s', RefExec env010_cfg s (.finish .quiescent) s' ∧ env010_cfg.envs ≠ [] ∧
        Live env010_cfg s ∧ s.mode = .draining ∧ s'.M 1 = [5] := by
  refine ⟨ENV_010_reference, ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env010_cfg)
    (o := xrun env010_cfg (xinit env010_m0 0) env010_full.dropLast) (l := .finish .quiescent)
    (p := fun s s' => liveB env010_cfg s && decide (s.mode = .draining) && s'.M 1 == [5])
    (by decide)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
  exact ⟨s, s', hs, env010_cfg_envs, hp.1.1, hp.1.2, hp.2⟩

/-! ### Every line exercised -/

/-- Both lines of ENV-010, and the four parts of its coverage clause `Env010Covers`, are exercised
by the reference, on the test derivation. (1) The whole run: the executor with the environment
place `0` fires `t` on the injected token, is drained and ends quiescent with the token in `1`.
(2) At its first termination test it is at rest, no terminal place is marked and the mode is open
(line 1's guard, the trigger of the clause's second part): it offers no finish quiescent and offers
the firing pass. (3) The same holds at its second test, after every transition fired ("verify
executor still running"). (4) Parked at quiescence with the mode open, it accepts a request into
`0` (line 2 and the clause's first part). (5) In the wait with that injection queued it wakes and
leaves the wait (the clause's fourth part). (6) In step 2 with the injection queued it injects it
(the clause's third part). -/
@[evidence nonvacuous ENV_010]
theorem ENV_010_nonvacuous :
    (∃ s, xrun env010_cfg (xinit env010_m0 0) env010_full = some s ∧
      s.phase = .done .quiescent ∧ s.M 1 = [5] ∧ s.M 0 = []) ∧
    (∃ s, xrun env010_cfg (xinit env010_m0 0) env010_toTest = some s ∧ Live env010_cfg s ∧
      s.mode = .open ∧ s.phase = .test ∧ Rest env010_cfg s ∧
      (¬ ∃ s', RefExec env010_cfg s (.finish .quiescent) s') ∧ ∃ s', RefExec env010_cfg s .begin s') ∧
    (∃ s, xrun env010_cfg (xinit env010_m0 0) env010_afterFire = some s ∧ Live env010_cfg s ∧
      s.mode = .open ∧ s.phase = .test ∧ Rest env010_cfg s ∧ s.M 1 = [5] ∧
      (¬ ∃ s', RefExec env010_cfg s (.finish .quiescent) s') ∧ ∃ s', RefExec env010_cfg s .begin s') ∧
    (∃ s s', RefExec env010_cfg s (.request 0 5 .accepted) s' ∧ s.parked = true ∧
      Live env010_cfg s ∧ s.mode = .open ∧ isExecPhase s.phase = true) ∧
    (∃ s s', xrun env010_cfg (xinit env010_m0 0) env010_queued = some s ∧
      RefExec env010_cfg s .wake s' ∧ Live env010_cfg s ∧ s.mode = .open ∧ s.phase = .await ∧
      s.eq ≠ [] ∧ s'.phase ≠ .await) ∧
    (∃ s s', xrun env010_cfg (xinit env010_m0 0) env010_toEvents = some s ∧
      RefExec env010_cfg s (.inject 0) s' ∧ Live env010_cfg s ∧ s.mode = .open ∧
      s.phase = .events ∧ s.eq = [(0, 0, 5)] ∧ s'.M 0 = [5]) := by
  have test : ∀ ls : List (XLbl Nat Nat),
      (xrun env010_cfg (xinit env010_m0 0) ls).map (fun s => liveB env010_cfg s &&
        decide (s.mode = .open) && decide (s.phase = .test) && restB env010_cfg s &&
        (xstep env010_cfg s (.finish .quiescent)).isNone &&
        (xstep env010_cfg s .begin).isSome) = some true →
      ∃ s, xrun env010_cfg (xinit env010_m0 0) ls = some s ∧ Live env010_cfg s ∧
        s.mode = .open ∧ s.phase = .test ∧ Rest env010_cfg s ∧
        (¬ ∃ s', RefExec env010_cfg s (.finish .quiescent) s') ∧
        ∃ s', RefExec env010_cfg s .begin s' := by
    intro ls h
    obtain ⟨s, hs, hp⟩ := env010_state_of_check h
    simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none,
      Option.isSome_iff_exists] at hp
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, s', h6⟩ := hp
    exact ⟨s, hs, h1, h2, h3, h4, fun ⟨s'', h''⟩ => by simp [RefExec, h5] at h'', s', h6⟩
  refine ⟨?_, test _ (by decide), ?_, ?_, ?_, ?_⟩
  · obtain ⟨s, hs, hp⟩ := env010_state_of_check (o := xrun env010_cfg (xinit env010_m0 0)
      env010_full) (p := fun s => decide (s.phase = .done .quiescent) && s.M 1 == [5] &&
        s.M 0 == []) (by decide)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
    exact ⟨s, hs, hp.1.1, hp.1.2, hp.2⟩
  · obtain ⟨s, hs, h1, h2, h3, h4, h5, h6⟩ := test env010_afterFire (by decide)
    have hM : (xrun env010_cfg (xinit env010_m0 0) env010_afterFire).map (fun s => s.M 1 == [5]) =
        some true := by decide
    rw [hs] at hM
    simp only [Option.map_some, Option.some.injEq, beq_iff_eq] at hM
    exact ⟨s, hs, h1, h2, h3, h4, hM, h5, h6⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env010_cfg)
      (o := xrun env010_cfg (xinit env010_m0 0) env010_toPark) (l := .request 0 5 .accepted)
      (p := fun s _ => s.parked && liveB env010_cfg s && decide (s.mode = .open) &&
        isExecPhase s.phase) (by decide)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    exact ⟨s, s', hs, hp.1.1.1, hp.1.1.2, hp.1.2, hp.2⟩
  · obtain ⟨s, s', ho, hs, hp⟩ := step_of_check xstep (C := env010_cfg)
      (o := xrun env010_cfg (xinit env010_m0 0) env010_queued) (l := .wake)
      (p := fun s s' => liveB env010_cfg s && decide (s.mode = .open) &&
        decide (s.phase = .await) && !s.eq.isEmpty && decide (s'.phase ≠ .await)) (by decide)
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      List.isEmpty_eq_false_iff] at hp
    exact ⟨s, s', ho, hs, hp.1.1.1.1, hp.1.1.1.2, hp.1.1.2, hp.1.2, hp.2⟩
  · obtain ⟨s, s', ho, hs, hp⟩ := step_of_check xstep (C := env010_cfg)
      (o := xrun env010_cfg (xinit env010_m0 0) env010_toEvents) (l := .inject 0)
      (p := fun s s' => liveB env010_cfg s && decide (s.mode = .open) &&
        decide (s.phase = .events) && decide (s.eq = [(0, 0, 5)]) && s'.M 0 == [5]) (by decide)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
    exact ⟨s, s', ho, hs, hp.1.1.1.1, hp.1.1.1.2, hp.1.1.2, hp.1.2, hp.2⟩

end Libpetri.Spec
