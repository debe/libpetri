import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Exec
import Libpetri.Spec.Text.ENV_002

set_option linter.missingDocs true

/-!
# ENV-002: Environment place registration (`spec/06-environment-places.md`)

Ruling D89 (a): an injection into a place that is not a registered environment place is an
error for an executor whose inject takes an environment-place handle (Java, TypeScript), and an
assumption on the host for an executor whose inject takes a place name (Rust, Python), which
deposits into whatever place the name resolves to. The ID carries two blocks (ruling D33 (a)).

* `ENV_002` (kind B, Java and TypeScript) is a predicate over an abstract executor
  `R : XRel N T` (glossary `GlossaryExec.lean`) and reads its `request p x r` steps: a caller asks
  to inject `x` into `p` and the executor answers `r`. For a place outside the configuration's
  environment places `C.envs`, the answer is an error and the state is unchanged. For a place in
  `C.envs`, the answer is never an error. Lines 1 and 3 together make the registration fixed for
  the run (`env002_error_iff`). The offers, an error answer in every state and an acceptance by an
  open executor in a phase of the run with no terminal place marked, are coverage: `Env002Covers`, a clause of the consistency
  theorem's `ExecCoversW5`, never a line. The block is checked against the reference executor
  (`RefExec`), against three wrong executors that each break exactly one line (`mutant`
  evidence), and against the name-keyed executor of Rust and Python, an executor that tests the
  lifecycle before the registration, one whose registrations never match and one whose
  registrations shrink during the run (`forbids` evidence); two more fail only the coverage clause.
* `ENV_002_host` (kind A, Rust and Python) is a predicate over a run: every request of the run
  names a registered environment place. Under it, every run of the name-keyed executor is a run of
  the reference (`env002_host_transfer`), and without it some is not (`env002_host_needed`).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## ENV-002: Environment Place Registration (handle-typed inject) -/

requirement ENV_002
  id "ENV-002"
  title "Environment Place Registration"
  kind B
  scope "executors whose inject takes an environment-place handle (Java, TypeScript)"
  source verbatim "spec/06-environment-places.md"
  covers ENV_002.s1, ENV_002.s2, ENV_002.s3, ENV_002.s4, ENV_002.s6, ENV_002.s7, ENV_002.s8,
        ENV_002.s9, ENV_002.s10, ENV_002.s11
  reading "For every executor R, every configuration C, every place p and every token x:"
          "if p is not one of C's environment places, a request step that asks to inject x into p answers with an error;"
          "if p is not one of C's environment places, a request step that asks to inject x into p leaves the executor state as it was;"
          "if p is one of C's environment places, a request step that asks to inject x into p does not answer with an error."
  assumes "The model is an executor R : XRel N T (glossary GlossaryExec.lean): R C s l s' says that under configuration C the step labelled l leads from executor state s to s'. The label request p x r is the outside step of a caller asking to inject token x into place p, with the executor's answer r: accepted (queued), refused (the executor is draining, closed, stopped or finished, ENV-006) or error (not an environment place). The witness is the reference executor RefExec (Reference/Exec.lean), whose request rule answers replyFor C s p and changes the state only on an accepted answer."
          "Scope (ruling D89 (a)): Java and TypeScript, whose inject takes an EnvironmentPlace handle and tests registration first (BitmapNetExecutor.inject and PrecompiledNetExecutor.inject return a failed future; the TypeScript inject rejects its promise and injectNoAwait throws). Rust and Python take a place name and deposit into the place it names whatever the registration (executor_handle.rs inject, executor_core/executor.rs handle_signal): the name-keyed executor env002_nameKeyed violates lines 1 and 2 (ENV_002_forbids_nameKeyed). For them the second block of this ID, ENV_002_host (kind A), states the host assumption instead."
          "The registered environment places are the configuration field C.envs (kind N): the quoted 'Environment places must be registered with the executor before execution begins.' and 'The executor maintains a set of registered environment places.' are that encoding. AC1 (the builder accepts registrations) is that field: every builder of the three languages fills it (Java Builder.environmentPlaces, TypeScript options.environmentPlaces, Rust ExecutorOptions.environment_places); it is configuration, not a step. That the reference's answer to an unregistered place depends on the configuration alone, in every state, is env002_registration_fixed (cited for ENV-001 AC3)."
          "The quoted 'The set of registered environment places is fixed when the executor is built; no step of a run adds or removes one.' is lines 1 and 3 together: under ENV-002 a request step answers with an error exactly when its place is not in C.envs, in every state (env002_error_iff), so the registrations an executor honours are C.envs throughout the run. An executor that adds a place during a run breaks line 1. One that removes the registrations once a ticket has been drawn breaks line 3 (env002_shrinks, ENV_002_forbids_shrinks). Every runtime copies the registrations at build: Java's executor constructors take Set.copyOf of the caller's set (both builder overloads and a direct constructor call), and TypeScript, Rust and Python copy them as well, so a host that adds a place to its own set after build() or removes one changes nothing the executor answers. An executor that tests the caller's live set has both shapes, the behaviour RD-35 in spec/runtime-defects.md recorded for Java's Set overload. One that ignores the registrations and answers every injection with an error breaks line 3 (env002_neverMatches, ENV_002_forbids_neverMatches): the shape of a registration set built from the handles while inject tests the names."
          "Line 1 is the first EARS sentence. Its 'shall not answer with a refusal even when it is draining, closed, stopped or finished' is the order of the two tests: registration before the lifecycle, as Java (inject, then the closed and draining flags) and TypeScript (the throw, then the closed, draining and terminal flags) do. An executor that tests the lifecycle first answers a closed executor's unregistered injection with a refusal (ENV_002_forbids_lifecycleFirst). An executor that may answer a closed executor's unregistered injection with a refusal besides the error breaks line 1 only (ENV_002_mutant_mayRefuse). 'Answer with an error' also excludes an acceptance, which is the 'only' of AC2: an accepted request names a registered place (env002_only_registered_accept, cited for AC2)."
          "Line 2 is the second EARS sentence: the request changes nothing, so no token is queued (the event queue XSt.eq is unchanged), the marking is unchanged and the loop is not woken (XSt.parked is unchanged). An executor that answers with an error and still queues the token breaks line 2 only (ENV_002_mutant_errorButQueue)."
          "Its offers are in ExecCoversW5.Env002Covers (ConsistencyExec.lean; the convention of GlossaryExec.lean: offers are coverage clauses, never block lines). The third and the fifth EARS sentences demand an answer and are quoted whole; their safety halves are lines 1 and 3, and their existence halves are that clause. The third EARS sentence and the 'returns' of AC3 say the error is an answer the executor gives in every state, open, draining, closed, stopped or after the run finished, not a call that blocks: Env002Covers offers it in every executor state, reachable or not, which is more than 'every state of the run' and which the reference meets (env002_ref_covers). An executor without a request step for an unregistered place satisfies every line and fails that clause (env002_covers_noAnswer); it is also the reference restricted to a host that meets ENV_002_host, which is why a name-keyed executor under that assumption is indistinguishable from the reference on the host's runs."
          "Line 3 is the fourth EARS sentence: a registered place is never answered with an error, in any state; once the executor is draining, closed, stopped or finished the answer is a refusal (ENV-006), a false future in Java and false in TypeScript. An executor that may answer a registered place with an error besides the reference's answer breaks line 3 only (env002_mayErrorRegistered, ENV_002_mutant_mayErrorRegistered): the shape of a registration test by object identity that misses an equal handle the caller built anew."
          "The fifth EARS sentence, the 'accept' of AC2 and the 'success' of the test derivation, is the second half of Env002Covers: while the executor is open (not draining, closed or stopped), in a phase of the run (isExecPhase, not finished) and no terminal place is marked (Live, EXEC-042), R offers to accept an injection into a registered place. The terminal condition is TypeScript's: once a terminal place is marked and before the loop ends, its inject() returns false at once and its injectNoAwait returns without queueing (the terminalReached test of both executors, also reached by an initial marking that marks a terminal place), where Java and the reference accept the call and drop the event when the run ends (ENV-003 line 6, ENV-004); for inject() both answers give the caller false, and the clause asks for neither, as ENV-010's line 2 and Env010Covers do (env002_covers_terminalRefuse). That clause requires the accepting step to exist; that an open running executor never refuses a registered place instead is ENV-010's line 2, and what the accepted request does (queue the token with a ticket, FIFO) is ENV-003's. An executor that refuses every registered place meets every line and fails the clause (env002_refuseRegistered, env002_covers_refuseRegistered): the shape of a lifecycle flag that starts set. Injections before the run starts are outside the model, whose runs start at xinit in mode open."
          "AC1 is the configuration field C.envs, and line 3 and Env002Covers say the executor honours it. AC2 is line 1 for 'only' and Env002Covers for 'accept'. AC3 is line 1 and Env002Covers. AC4 is the second block, ENV_002_host. A refusal is ENV-006's subject, on the same request label. The Java error is a failed future and the TypeScript error a rejected promise (inject) or a thrown exception (injectNoAwait); the model does not tell them apart, all are the answer error."
          "The test derivation's Java and TypeScript clause (register 3 environment places; inject into a registered one, success; inject into an unregistered one, error) is ENV_002_nonvacuous: with places 0, 1 and 2 registered, a request into 0 is accepted and its token lands in place 0 at the next injection step, a request into 0 by the closed executor is refused, not answered with an error, and a request into place 3 is answered with an error, by an open and by a closed executor, with the state unchanged. Its Rust and Python clause (AC4 is an assumption on the host, which no executor test checks) is the kind A of the second block."
  signoff "2026-11-13 04a47dd90e755d34 ai"
  statement : ∀ {N T : Type} [DecidableEq N], XRel N T → Prop :=
    fun R => ∀ C p x,
      (p ∉ C.envs →
        (∀ r, on (fun s s' => R C s (.request p x r) s'), shall (fun _ _ => r = .error)) ∧
        (∀ r, on (fun s s' => R C s (.request p x r) s'), shall (fun s s' => s' = s))) ∧
      (p ∈ C.envs →
        (∀ r, on (fun s s' => R C s (.request p x r) s'), shall (fun _ _ => r ≠ .error)))

/- The pinned readable form of ENV-002: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.ENV_002 : {N T : Type} → [DecidableEq N] → XRel N T → Prop :=
fun {N T} [DecidableEq N] R =>
  ∀ (C : Cfg N T) (p : N) (x : T),
    (p ∉ C.envs →
        (∀ (r : Reply), on fun s s' => R C s (XLbl.request p x r) s', shall fun x x_1 => r = Reply.error) ∧
          ∀ (r : Reply), on fun s s' => R C s (XLbl.request p x r) s', shall fun s s' => s' = s) ∧
      (p ∈ C.envs → ∀ (r : Reply), on fun s s' => R C s (XLbl.request p x r) s', shall fun x x_1 => r ≠ Reply.error)
-/
#guard_msgs in #print ENV_002

/-! ## ENV-002: the host of a name-keyed inject -/

requirement ENV_002_host
  id "ENV-002"
  title "Environment Place Registration (host of a name-keyed inject)"
  kind A
  scope "executors whose inject takes a place name (Rust, Python), and their hosts"
  source verbatim "spec/06-environment-places.md"
  covers ENV_002.s5, ENV_002.s12, ENV_002.s13
  reading "For a configuration C and a run tr (a list of steps, each a source state, a label and a target state):"
          "every request step of tr asks to inject into one of C's environment places."
  assumes "Ruling D89 (a). The block is an assumption on the host (kind A), not a behaviour of the executor: a Rust or Python executor answers a request into any place, deposits into the place the name resolves to (an unknown one is retained, CORE-072), and registration feeds only the long-running decision (ENV-010) and the dead-arc report (CORE-037, rust/libpetri-runtime/src/executor.rs). The statement reads only the labels of a run, so it is a predicate on what the host asks, whatever executor answers."
          "What the assumption buys is env002_host_transfer: every run of the name-keyed executor env002_nameKeyed (the reference with the registration test removed from its answer, the Rust and Python shape) that meets ENV_002_host is a run of the reference executor RefExec, so every property proved of RefExec runs (the first block of this ID included) holds of the name-keyed executor on the runs of a host that meets it. The assumption is load-bearing: a name-keyed run with one request into an unregistered place is not a run of the reference (env002_host_needed). The verifier's open-system model makes the same assumption (Novel.EnvSemantics.StepCE injects only into a registered environment place), and CORE-037 states it for the dead-arc report ('a host injects tokens only into environment places')."
          "The second quoted sentence describes the name-keyed executor; it is the model env002_nameKeyed, not a line. AC4 is the one line, and the test derivation's Rust and Python clause says no executor test checks it. AC1 to AC3 and the test derivation's Java and TypeScript clause are the first block's."
  signoff "2026-11-13 75617b78406d7c87 ai"
  statement : ∀ {N T : Type}, Cfg N T → List (XStep N T) → Prop :=
    fun C tr => ∀ st ∈ tr, ∀ p x r, st.2.1 = .request p x r → p ∈ C.envs

/- The pinned readable form of the host block. -/
/--
info: def Libpetri.Spec.ENV_002_host : {N T : Type} → Cfg N T → List (XStep N T) → Prop :=
fun {N T} C tr => ∀ st ∈ tr, ∀ (p : N) (x : T) (r : Reply), st.2.1 = XLbl.request p x r → p ∈ C.envs
-/
#guard_msgs in #print ENV_002_host

/-! ### The reference -/

section Reference

variable {N T : Type} [DecidableEq N]

/-- The reference answers a request into an unregistered place with an error, in every state. -/
theorem env002_replyFor_unreg {C : Cfg N T} {p : N} (hp : p ∉ C.envs) (s : XSt N T) :
    replyFor C s p = .error := by
  simp [replyFor, hp]

/-- The reference never answers a request into a registered place with an error. -/
theorem env002_replyFor_reg {C : Cfg N T} {p : N} (hp : p ∈ C.envs) (s : XSt N T) :
    replyFor C s p ≠ .error := by
  unfold replyFor
  simp only [hp, not_true_eq_false, if_false]
  split <;> decide

/-- A reference request step into an unregistered place answers with an error and changes
nothing (`requestStep_some`). -/
theorem env002_ref_unreg {C : Cfg N T} {s s' : XSt N T} {p : N} {x : T} {r : Reply}
    (hp : p ∉ C.envs) (h : RefExec C s (.request p x r) s') : r = .error ∧ s' = s := by
  obtain ⟨hr, ⟨ha, -⟩ | ⟨-, hs⟩⟩ := requestStep_some h
  · rw [hr, env002_replyFor_unreg hp] at ha
    exact absurd ha (by decide)
  · exact ⟨hr.trans (env002_replyFor_unreg hp s), hs⟩

/-- The reference offers the error answer to a request into an unregistered place in every
state, and the step changes nothing. -/
theorem env002_ref_error {C : Cfg N T} {p : N} (x : T) (hp : p ∉ C.envs) (s : XSt N T) :
    RefExec C s (.request p x .error) s := by
  show requestStep C s p x .error = some s
  simp [requestStep, env002_replyFor_unreg hp]

/-- A reference request step into a registered place does not answer with an error. -/
theorem env002_ref_reg {C : Cfg N T} {s s' : XSt N T} {p : N} {x : T} {r : Reply}
    (hp : p ∈ C.envs) (h : RefExec C s (.request p x r) s') : r ≠ .error :=
  (requestStep_some h).1 ▸ env002_replyFor_reg hp s

/-- The state after queueing `x` for `p` with a fresh ticket (the reference's accepted request). -/
def env002Enq (s : XSt N T) (p : N) (x : T) : XSt N T :=
  { s with eq := s.eq ++ [(s.nextId, p, x)], nextId := s.nextId + 1, parked := false }

/-- An open reference executor in a phase of the run accepts a request into a registered place
and queues it. -/
theorem env002_ref_accept {C : Cfg N T} {p : N} (x : T) (hp : p ∈ C.envs) {s : XSt N T}
    (hm : s.mode = .open) (he : isExecPhase s.phase = true) :
    RefExec C s (.request p x .accepted) (env002Enq s p x) := by
  show requestStep C s p x .accepted = some _
  simp [requestStep, replyFor, hp, hm, he, env002Enq]

end Reference

/-- ✓ The reference executor satisfies ENV-002: its request rule answers `replyFor`, which is an
error exactly for an unregistered place whatever the state, and changes the state only on an
accepted answer (`requestStep_some`). -/
@[evidence holds ENV_002]
theorem ENV_002_reference {N T : Type} [DecidableEq N] : ENV_002 (RefExec (N := N) (T := T)) := by
  intro C p x
  exact ⟨fun hp => ⟨fun _ _ _ h => (env002_ref_unreg hp h).1, fun _ _ _ h => (env002_ref_unreg hp h).2⟩,
    fun hp _ _ _ h => env002_ref_reg hp h⟩

/-- **The coverage conjunct ENV-002 asks of the consistency theorem's `ExecCoversW5`**: an
injection into a place that is not a registered environment place is answered with an error in
every state (the third EARS sentence, AC3), and one into a registered environment place is
accepted in every open state of the run with no terminal place marked (the fifth EARS sentence,
AC2). Offers are never a line
of a block (glossary `GlossaryExec.lean`). -/
def Env002Covers {N T : Type} (E : XRel N T) : Prop :=
  ∀ C p x,
    (p ∉ C.envs → ∀ s, ∃ s', E C s (.request p x .error) s') ∧
    (p ∈ C.envs → ∀ s, s.mode = .open → isExecPhase s.phase = true → Live C s →
      ∃ s', E C s (.request p x .accepted) s')

/-- The reference meets ENV-002's coverage conjunct: it offers the error answer in every state
(`env002_ref_error`) and the acceptance in every open running state, terminal place marked or
not (`env002_ref_accept`). -/
theorem env002_ref_covers {N T : Type} [DecidableEq N] : Env002Covers (RefExec (N := N) (T := T)) :=
  fun _ _ x => ⟨fun hp s => ⟨s, env002_ref_error x hp s⟩,
    fun hp _ hm he _ => ⟨_, env002_ref_accept x hp hm he⟩⟩

/-- AC2: under ENV-002, an accepted request names a registered environment place. -/
@[evidence cites "ENV-002" "AC2: Where inject takes an environment-place handle (Java, TypeScript), only registered environment places accept injections."]
theorem env002_only_registered_accept {N T : Type} [DecidableEq N] {R : XRel N T}
    (h : ENV_002 R) {C : Cfg N T} {s s' : XSt N T} {p : N} {x : T}
    (hs : R C s (.request p x .accepted) s') : p ∈ C.envs := by
  by_contra hp
  have hr : Reply.accepted = .error := ((h C p x).1 hp).1 .accepted s s' hs
  exact absurd hr (by decide)

/-- The registration is fixed for the run: under ENV-002, a request step answers with an error
exactly when its place is not one of the configuration's environment places, whatever the state
the step starts from. No step can add a registration (line 1) or remove one (line 3). -/
@[evidence cites "ENV-002" "The set of registered environment places is fixed when the executor is built; no step of a run adds or removes one."]
theorem env002_error_iff {N T : Type} [DecidableEq N] {R : XRel N T} (h : ENV_002 R)
    {C : Cfg N T} {s s' : XSt N T} {p : N} {x : T} {r : Reply}
    (hs : R C s (.request p x r) s') : r = .error ↔ p ∉ C.envs :=
  ⟨fun he hp => (h C p x).2 hp r s s' hs he, fun hp => ((h C p x).1 hp).1 r s s' hs⟩

/-- ENV-001 AC3: registration is configuration. Whether the reference answers a request into
`p` with an error is decided by the configuration's environment places alone, the same in every
state of every run: no step registers or unregisters a place. -/
@[evidence cites "ENV-001" "AC3: Environment places are registered with the executor at construction time."]
theorem env002_registration_fixed {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T)
    (p : N) : replyFor C s p = .error ↔ p ∉ C.envs :=
  ⟨fun h hp => env002_replyFor_reg hp s h, fun hp => env002_replyFor_unreg hp s⟩

/-! ### Wrong executors -/

section Models

variable {N T : Type} [DecidableEq N]

/-- An executor that is the reference except on requests: it answers `rep C s p` and queues the
token when `q` says so for the answer. -/
def env002Step (rep : Cfg N T → XSt N T → N → Reply) (q : Reply → Bool) (C : Cfg N T)
    (s : XSt N T) : XLbl N T → Option (XSt N T)
  | .request p x r =>
    if r = rep C s p then (if q r then some (env002Enq s p x) else some s) else none
  | l => xstep C s l

/-- The executor of `env002Step rep q`. -/
def env002Rel (rep : Cfg N T → XSt N T → N → Reply) (q : Reply → Bool) : XRel N T :=
  fun C s l s' => env002Step rep q C s l = some s'

/-- Queue on an accepted answer only (the reference). -/
def env002QAcc : Reply → Bool := fun r => decide (r = .accepted)

/-- A request step of `env002Rel rep q` answers `rep`. -/
theorem env002Rel_answer {rep : Cfg N T → XSt N T → N → Reply} {q : Reply → Bool}
    {C : Cfg N T} {s s' : XSt N T} {p : N} {x : T} {r : Reply}
    (h : env002Rel rep q C s (.request p x r) s') : r = rep C s p := by
  change env002Step rep q C s (.request p x r) = some s' at h
  by_cases hr : r = rep C s p
  · exact hr
  · simp [env002Step, hr] at h

/-- Lines 1 and 2, and the error half of `Env002Covers`, hold of an `env002Rel rep q` that
answers an unregistered place with an error in every state and queues nothing on an error. -/
theorem env002Rel_unreg {rep : Cfg N T → XSt N T → N → Reply} {q : Reply → Bool}
    (hrep : ∀ C s p, p ∉ C.envs → rep C s p = .error) (hq : q .error = false)
    {C : Cfg N T} {p : N} (x : T) (hp : p ∉ C.envs) :
    (∀ r, on (fun s s' => env002Rel rep q C s (.request p x r) s'),
      shall (fun _ _ => r = .error)) ∧
    (∀ r, on (fun s s' => env002Rel rep q C s (.request p x r) s'), shall (fun s s' => s' = s)) ∧
    (∀ s, ∃ s', env002Rel rep q C s (.request p x .error) s') := by
  refine ⟨fun r s s' h => (env002Rel_answer h).trans (hrep C s p hp), fun r s s' h => ?_,
    fun s => ⟨s, ?_⟩⟩
  · have hr := (env002Rel_answer h).trans (hrep C s p hp)
    subst hr
    change env002Step rep q C s (.request p x .error) = some s' at h
    simp [env002Step, hrep C s p hp, hq] at h
    exact h.symm
  · change env002Step rep q C s (.request p x .error) = some s
    simp [env002Step, hrep C s p hp, hq]

/-- The answer of a name-keyed inject (Rust, Python): accepted while the executor is open and
running, refused otherwise, whatever the place. -/
def env002NkRep (_ : Cfg N T) (s : XSt N T) (_ : N) : Reply :=
  if s.mode = .open && isExecPhase s.phase then .accepted else .refused

/-- **The name-keyed executor** (Rust and Python): it queues an injection into any place while it
is open (`ExecutorHandle::inject` tests only its drained flag; `handle_signal` deposits into the
named place). -/
def env002_nameKeyed : XRel N T := env002Rel env002NkRep env002QAcc

/-- The answer of an executor that tests the lifecycle before the registration. -/
def env002LfRep (C : Cfg N T) (s : XSt N T) (p : N) : Reply :=
  if s.mode = .open && isExecPhase s.phase then (if p ∈ C.envs then .accepted else .error)
  else .refused

/-- An executor that refuses every request once it is not open, before it tests the
registration. -/
def env002_lifecycleFirst : XRel N T := env002Rel env002LfRep env002QAcc

/-- An executor whose registrations never match: every injection is answered with an error, the
registered places included (a registration set built from the handles while inject tests the
names). -/
def env002_neverMatches : XRel N T := env002Rel (fun _ _ _ => .error) env002QAcc

/-- The answer of an executor whose registrations are removed once a ticket has been drawn: the
reference's answer while the supply is untouched, an error for every place after that. -/
def env002ShrinkRep (C : Cfg N T) (s : XSt N T) (p : N) : Reply :=
  if s.nextId = 0 then replyFor C s p else .error

/-- An executor whose registrations shrink during the run (an executor that tests the caller's
mutable set, from which the host removes a place after its first injection: the behaviour RD-35
recorded). -/
def env002_shrinks : XRel N T := env002Rel env002ShrinkRep env002QAcc

/-- An executor that answers an unregistered place with an error and still queues the token. -/
def env002_errorButQueue : XRel N T :=
  env002Rel replyFor (fun r => decide (r ≠ .refused))

/-- An executor that has no request step for an unregistered place (the call never returns). It
is also the reference restricted to a host that meets `ENV_002_host`. -/
def env002_noAnswer : XRel N T :=
  fun C s l s' => RefExec C s l s' ∧ ∀ p x r, l = .request p x r → p ∈ C.envs

/-- An executor that may also answer a request into an unregistered place with a refusal once it
is not open, besides the reference's error. -/
def env002_mayRefuse : XRel N T :=
  fun C s l s' => RefExec C s l s' ∨
    ∃ p x, l = .request p x .refused ∧ p ∉ C.envs ∧ s.mode ≠ .open ∧ s' = s

/-- An executor that may also answer a request into a registered place with an error, besides
the reference's answer (a registration test by object identity that misses an equal handle the
caller built anew). -/
def env002_mayErrorRegistered : XRel N T :=
  fun C s l s' => RefExec C s l s' ∨
    ∃ p x, l = .request p x .error ∧ p ∈ C.envs ∧ s' = s

/-- The answer of an executor that refuses every registered place (a lifecycle flag that starts
set) and answers every other place with an error. -/
def env002RefuseRep (C : Cfg N T) (_ : XSt N T) (p : N) : Reply :=
  if p ∈ C.envs then .refused else .error

/-- An executor that refuses every injection into a registered place, even while open. -/
def env002_refuseRegistered : XRel N T := env002Rel env002RefuseRep env002QAcc

/-- The answer of the TypeScript inject: an error for an unregistered place; for a registered
one, accepted while the executor is open, running and no terminal place is marked, refused
otherwise (the `terminalReached` test of both TypeScript executors). -/
def env002TsRep (C : Cfg N T) (s : XSt N T) (p : N) : Reply :=
  if p ∉ C.envs then .error
  else if s.mode = .open && isExecPhase s.phase && liveB C s then .accepted else .refused

/-- The TypeScript executor: it refuses a registered place once a terminal place is marked,
before the loop ends, where the reference accepts and drops the event at the finish. -/
def env002_tsTerminal : XRel N T := env002Rel env002TsRep env002QAcc

end Models

/-! ### The example configuration: places `0`, `1`, `2` registered, place `3` not -/

/-- Three registered environment places `0`, `1`, `2`; place `3` is not registered. No
transition: the requests and injections are what the examples exercise. -/
def env002_C : Cfg Nat Nat :=
  { X := { net := { places := [0, 1, 2, 3], transitions := [] }, timing := fun _ => .immediate,
           tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [0, 1, 2], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => true,
    res := 0 }

/-- The initial state: empty marking, open, at the top of the loop. -/
def env002_s0 : XSt Nat Nat := xinit (fun _ => []) 0

/-- The initial state, closed. -/
def env002_sClosed : XSt Nat Nat := { env002_s0 with mode := .closed }

theorem env002_3_unreg : (3 : Nat) ∉ env002_C.envs := by decide

theorem env002_0_reg : (0 : Nat) ∈ env002_C.envs := by decide

/-! ### Mutant readings: ENV-002 without one of its lines -/

/-- ENV-002 without line 1 (an unregistered place is answered with an error). -/
def ENV_002_noAnswerLine {N T : Type} [DecidableEq N] (R : XRel N T) : Prop :=
  ∀ C p x,
    (p ∉ C.envs →
      (∀ r, on (fun s s' => R C s (.request p x r) s'), shall (fun s s' => s' = s))) ∧
    (p ∈ C.envs →
      (∀ r, on (fun s s' => R C s (.request p x r) s'), shall (fun _ _ => r ≠ .error)))

/-- ENV-002 without line 2 (the state is unchanged). -/
def ENV_002_noFrameLine {N T : Type} [DecidableEq N] (R : XRel N T) : Prop :=
  ∀ C p x,
    (p ∉ C.envs →
      (∀ r, on (fun s s' => R C s (.request p x r) s'), shall (fun _ _ => r = .error))) ∧
    (p ∈ C.envs →
      (∀ r, on (fun s s' => R C s (.request p x r) s'), shall (fun _ _ => r ≠ .error)))

/-- ENV-002 without line 3 (a registered place is never answered with an error). -/
def ENV_002_noRegErrorLine {N T : Type} [DecidableEq N] (R : XRel N T) : Prop :=
  ∀ C p x,
    (p ∉ C.envs →
      (∀ r, on (fun s s' => R C s (.request p x r) s'), shall (fun _ _ => r = .error)) ∧
      (∀ r, on (fun s s' => R C s (.request p x r) s'), shall (fun s s' => s' = s)))

/-- Line 1 is load-bearing: an executor that may refuse an unregistered place once it is closed
meets lines 2 and 3 but not line 1. A closed executor answers the request into place `3` with a
refusal. -/
@[evidence mutant ENV_002]
theorem ENV_002_mutant_mayRefuse :
    ENV_002_noAnswerLine (env002_mayRefuse (N := Nat) (T := Nat)) ∧
      ¬ ENV_002 (env002_mayRefuse (N := Nat) (T := Nat)) := by
  refine ⟨fun C p x => ⟨fun hp r s s' h => ?_, fun hp r s s' h => ?_⟩, fun h => ?_⟩
  · rcases h with h | ⟨_, _, hl, -, -, hs⟩
    · exact (env002_ref_unreg hp h).2
    · exact hs
  · rcases h with h | ⟨_, _, hl, hp', -, -⟩
    · exact env002_ref_reg hp h
    · cases hl
      exact absurd hp hp'
  · have hr : Reply.refused = .error :=
      ((h env002_C 3 5).1 env002_3_unreg).1 .refused env002_sClosed env002_sClosed
        (Or.inr ⟨3, 5, rfl, env002_3_unreg, by decide, rfl⟩)
    exact absurd hr (by decide)

/-- Line 2 is load-bearing: an executor that answers an unregistered place with an error but
queues the token meets lines 1 and 3 but not line 2. -/
@[evidence mutant ENV_002]
theorem ENV_002_mutant_errorButQueue :
    ENV_002_noFrameLine (env002_errorButQueue (N := Nat) (T := Nat)) ∧
      ¬ ENV_002 (env002_errorButQueue (N := Nat) (T := Nat)) := by
  refine ⟨fun C p x => ⟨fun hp r s s' h =>
        (env002Rel_answer h).trans (env002_replyFor_unreg hp s),
    fun hp r s s' h => (env002Rel_answer h) ▸ env002_replyFor_reg hp s⟩, fun h => ?_⟩
  · have hs : env002_errorButQueue env002_C env002_s0 (.request 3 5 .error)
        (env002Enq env002_s0 3 5) := by
      change env002Step replyFor _ env002_C env002_s0 (.request 3 5 .error) = some _
      simp [env002Step, env002_replyFor_unreg env002_3_unreg]
    have := ((h env002_C 3 5).1 env002_3_unreg).2 .error _ _ hs
    have hl := congrArg (fun s : XSt Nat Nat => s.eq.length) this
    simp [env002Enq, env002_s0, xinit] at hl

/-- The error answer is coverage, not a line: an executor with no request step for an
unregistered place meets every line of ENV-002 (they say nothing of a step that does not exist)
and fails its coverage conjunct `Env002Covers` (the third EARS sentence, AC3). It is also the
reference restricted to a host that meets `ENV_002_host`. -/
@[evidence cites "ENV-002" "the executor shall answer an injection into a place that is not a registered environment place with an error in every state of the run: an executor with no request step for an unregistered place meets every line of the block and fails its coverage clause Env002Covers in ExecCoversW5"]
theorem env002_covers_noAnswer :
    ENV_002 (env002_noAnswer (N := Nat) (T := Nat)) ∧
      ¬ Env002Covers (env002_noAnswer (N := Nat) (T := Nat)) := by
  refine ⟨fun C p x => ⟨fun hp => ⟨fun r s s' h => (env002_ref_unreg hp h.1).1,
      fun r s s' h => (env002_ref_unreg hp h.1).2⟩,
    fun hp r s s' h => env002_ref_reg hp h.1⟩, fun h => ?_⟩
  obtain ⟨s', -, hreg⟩ := (h env002_C 3 5).1 env002_3_unreg env002_s0
  exact env002_3_unreg (hreg 3 5 .error rfl)

/-- Line 3 is load-bearing: an executor that may also answer a registered place with an error
meets lines 1 and 2 but not line 3. The open executor answers the request into the registered
place `0` with an error. -/
@[evidence mutant ENV_002]
theorem ENV_002_mutant_mayErrorRegistered :
    ENV_002_noRegErrorLine (env002_mayErrorRegistered (N := Nat) (T := Nat)) ∧
      ¬ ENV_002 (env002_mayErrorRegistered (N := Nat) (T := Nat)) := by
  refine ⟨fun C p x => fun hp => ⟨fun r s s' h => ?_, fun r s s' h => ?_⟩, fun h => ?_⟩
  · rcases h with h | ⟨_, _, hl, hp', -⟩
    · exact (env002_ref_unreg hp h).1
    · cases hl
      exact absurd hp' hp
  · rcases h with h | ⟨_, _, hl, hp', -⟩
    · exact (env002_ref_unreg hp h).2
    · cases hl
      exact absurd hp' hp
  · exact (h env002_C 0 5).2 env002_0_reg .error env002_s0 env002_s0
      (Or.inr ⟨0, 5, rfl, env002_0_reg, rfl⟩) rfl

/-- The acceptance is coverage, not a line: an executor that refuses every registered place
meets every line of ENV-002 and fails its coverage conjunct `Env002Covers` (the fifth EARS
sentence, AC2). The open executor at its first state has no accepting step for the registered
place `0`. -/
@[evidence cites "ENV-002" "while the run has not finished, the executor is not draining, closed or stopped and no terminal place is marked, the executor shall accept an injection into a registered environment place: an executor that refuses every registered place meets every line of the block and fails its coverage clause Env002Covers in ExecCoversW5"]
theorem env002_covers_refuseRegistered :
    ENV_002 (env002_refuseRegistered (N := Nat) (T := Nat)) ∧
      ¬ Env002Covers (env002_refuseRegistered (N := Nat) (T := Nat)) := by
  refine ⟨fun C p x => ⟨fun hp =>
      ⟨(env002Rel_unreg (fun C s p hp => by simp [env002RefuseRep, hp]) (by decide) x hp).1,
        (env002Rel_unreg (fun C s p hp => by simp [env002RefuseRep, hp]) (by decide) x hp).2.1⟩,
    fun hp r s s' h => ?_⟩, fun h => ?_⟩
  · rw [env002Rel_answer h]
    simp [env002RefuseRep, hp]
  · obtain ⟨s', hs⟩ := (h env002_C 0 5).2 env002_0_reg env002_s0 rfl rfl rfl
    have := env002Rel_answer hs
    simp [env002RefuseRep, env002_0_reg] at this

/-- The terminal condition of the fifth EARS sentence is needed for TypeScript: its inject refuses
a registered place once a terminal place is marked, before the loop ends. That executor meets
every line of ENV-002 and the coverage conjunct `Env002Covers`, which asks for the acceptance
only while no terminal place is marked. -/
@[evidence cites "ENV-002" "while the run has not finished, the executor is not draining, closed or stopped and no terminal place is marked, the executor shall accept an injection into a registered environment place: TypeScript, which refuses once a terminal place is marked, meets every line of the block and its coverage clause Env002Covers"]
theorem env002_covers_terminalRefuse {N T : Type} [DecidableEq N] :
    ENV_002 (env002_tsTerminal (N := N) (T := T)) ∧
      Env002Covers (env002_tsTerminal (N := N) (T := T)) := by
  have hrep : ∀ (C : Cfg N T) s p, p ∉ C.envs → env002TsRep C s p = .error :=
    fun C s p hp => by simp [env002TsRep, hp]
  refine ⟨fun C p x => ⟨fun hp => ⟨(env002Rel_unreg hrep (by decide) x hp).1,
      (env002Rel_unreg hrep (by decide) x hp).2.1⟩, fun hp r s s' h => ?_⟩,
    fun C p x => ⟨fun hp => (env002Rel_unreg hrep (by decide) x hp).2.2,
      fun hp s hm he hL => ⟨env002Enq s p x, ?_⟩⟩⟩
  · rw [env002Rel_answer h]
    unfold env002TsRep
    simp only [hp, not_true_eq_false, if_false]
    split <;> decide
  · change env002Step env002TsRep env002QAcc C s (.request p x .accepted) = some _
    have hL' : liveB C s = true := hL
    simp [env002Step, env002TsRep, hp, hm, he, hL', env002QAcc]

/-- ✗ The name-keyed executor of Rust and Python violates ENV-002 (line 1): an open executor
accepts the request into the unregistered place `3` and queues it. This is why the block is
scoped to the handle-typed inject and the host block covers the name-keyed one. -/
@[evidence forbids ENV_002]
theorem ENV_002_forbids_nameKeyed : ¬ ENV_002 (env002_nameKeyed (N := Nat) (T := Nat)) := by
  intro h
  have hs : env002_nameKeyed env002_C env002_s0 (.request 3 5 .accepted)
      (env002Enq env002_s0 3 5) := rfl
  have hr : Reply.accepted = .error := ((h env002_C 3 5).1 env002_3_unreg).1 .accepted _ _ hs
  exact absurd hr (by decide)

/-- ✗ Testing the lifecycle before the registration violates ENV-002 (line 1): a closed executor
answers the request into the unregistered place `3` with a refusal. -/
@[evidence forbids ENV_002]
theorem ENV_002_forbids_lifecycleFirst :
    ¬ ENV_002 (env002_lifecycleFirst (N := Nat) (T := Nat)) := by
  intro h
  have hs : env002_lifecycleFirst env002_C env002_sClosed (.request 3 5 .refused)
      env002_sClosed := rfl
  have hr : Reply.refused = .error := ((h env002_C 3 5).1 env002_3_unreg).1 .refused _ _ hs
  exact absurd hr (by decide)

/-- ✗ Registrations that never match violate ENV-002 (line 3): the open executor answers the
request into the registered place `0` with an error. Lines 1 and 2 alone accept this executor
(`env002Rel_unreg`). -/
@[evidence forbids ENV_002]
theorem ENV_002_forbids_neverMatches :
    ¬ ENV_002 (env002_neverMatches (N := Nat) (T := Nat)) := by
  intro h
  have hs : env002_neverMatches env002_C env002_s0 (.request 0 5 .error) env002_s0 := rfl
  exact (h env002_C 0 5).2 env002_0_reg .error _ _ hs rfl

/-- ✗ Registrations removed during the run violate ENV-002 (line 3): after the injection into
the registered place `0` is accepted, the still open executor answers the next injection into
`0` with an error. Lines 1 and 2 alone accept this executor (`env002Rel_unreg`). -/
@[evidence forbids ENV_002]
theorem ENV_002_forbids_shrinks : ¬ ENV_002 (env002_shrinks (N := Nat) (T := Nat)) := by
  intro h
  have h2 : env002_shrinks env002_C (env002Enq env002_s0 0 5) (.request 0 6 .error)
      (env002Enq env002_s0 0 5) := rfl
  exact (h env002_C 0 6).2 env002_0_reg .error _ _ h2 rfl

/-- Lines 1 and 2 and the error half of `Env002Covers` do not catch the two registration slips:
the executors whose registrations never match or shrink during the run answer every unregistered
place as the reference does. -/
theorem env002_registrationSlips_unreg {C : Cfg Nat Nat} {p : Nat} (x : Nat) (hp : p ∉ C.envs) :
    (∀ s, ∃ s', env002_neverMatches C s (.request p x .error) s') ∧
      (∀ s, ∃ s', env002_shrinks C s (.request p x .error) s') :=
  ⟨((env002Rel_unreg (fun _ _ _ _ => rfl) (by decide) x hp).2.2),
    ((env002Rel_unreg (fun C s p hp => by
      unfold env002ShrinkRep; split
      · exact env002_replyFor_unreg hp s
      · rfl) (by decide) x hp).2.2)⟩

/-- Every line of ENV-002 is exercised by the reference, with places `0`, `1`, `2` registered
(the test derivation's Java and TypeScript clause): a request into `0` is accepted, and its token
`5` lands in place `0` at the next injection step; the closed executor refuses a request into `0`
and has no error answer for it; a request into `3` is answered with an error, by the open and by
the closed executor, and the state stays as it was. -/
@[evidence nonvacuous ENV_002]
theorem ENV_002_nonvacuous :
    (∃ s', RefExec env002_C env002_s0 (.request 0 5 .accepted) s' ∧ s'.eq.length = 1) ∧
    (∃ s s', RefExec env002_C s (.inject 0) s' ∧ s'.M 0 = [5]) ∧
    RefExec env002_C env002_sClosed (.request 0 5 .refused) env002_sClosed ∧
    (¬ ∃ s', RefExec env002_C env002_sClosed (.request 0 5 .error) s') ∧
    RefExec env002_C env002_s0 (.request 3 5 .error) env002_s0 ∧
    RefExec env002_C env002_sClosed (.request 3 5 .error) env002_sClosed ∧
    ¬ ∃ s', RefExec env002_C env002_sClosed (.request 3 5 .refused) s' := by
  refine ⟨⟨env002Enq env002_s0 0 5, rfl, rfl⟩, ?_, rfl, fun ⟨s', hs⟩ => ?_,
    env002_ref_error 5 env002_3_unreg _, env002_ref_error 5 env002_3_unreg _, fun ⟨s', hs⟩ => ?_⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := env002_C)
      (o := xrun env002_C env002_s0 [.request 0 5 .accepted, .endCompletions, .endPublications])
      (l := .inject 0) (p := fun _ s' => s'.M 0 == [5]) (by decide)
    exact ⟨s, s', hs, by simpa using hp⟩
  · exact env002_ref_reg env002_0_reg hs rfl
  · exact absurd (env002_ref_unreg env002_3_unreg hs).1 (by decide)

/-! ### The host block -/

section Host

variable {N T : Type} [DecidableEq N]

/-- On a request into a registered place, the name-keyed executor is the reference. -/
theorem env002_nameKeyed_request {C : Cfg N T} {s : XSt N T} {p : N} {x : T} {r : Reply}
    (hp : p ∈ C.envs) :
    env002Step env002NkRep env002QAcc C s (.request p x r) = xstep C s (.request p x r) := by
  show _ = requestStep C s p x r
  simp [env002Step, requestStep, replyFor, hp, env002NkRep, env002QAcc, env002Enq]

/-- On every label other than a request, the name-keyed executor is the reference. -/
theorem env002_nameKeyed_other {C : Cfg N T} {s : XSt N T} {l : XLbl N T}
    (hl : ∀ p x r, l ≠ .request p x r) :
    env002Step env002NkRep env002QAcc C s l = xstep C s l := by
  cases l with
  | request p x r => exact absurd rfl (hl p x r)
  | _ => rfl

/-- Under the host assumption, every run of the name-keyed executor (Rust, Python) is a run of
the reference executor: the two differ only on requests into unregistered places, which such a
host never makes. -/
@[evidence cites "ENV-002" "Where inject takes a place name (Rust, Python), the host injects only into registered environment places."]
theorem env002_host_transfer {C : Cfg N T} :
    ∀ {s0 : XSt N T} {tr : List (XStep N T)}, XRun env002_nameKeyed C s0 tr →
      ENV_002_host C tr → XRun RefExec C s0 tr
  | _, [], _, _ => trivial
  | _, ⟨a, l, b⟩ :: rest, ⟨h1, h2, h3⟩, hh => by
    refine ⟨h1, ?_, env002_host_transfer h3 fun st hm => hh st (List.mem_cons_of_mem _ hm)⟩
    show xstep C a l = some b
    by_cases hreq : ∃ p x r, l = .request p x r
    · obtain ⟨p, x, r, rfl⟩ := hreq
      have hp := hh ⟨a, .request p x r, b⟩ List.mem_cons_self p x r rfl
      rw [← env002_nameKeyed_request hp]
      exact h2
    · push Not at hreq
      rw [← env002_nameKeyed_other hreq]
      exact h2

/-- The host assumption is load-bearing: a name-keyed run with one request into the unregistered
place `3` is not a run of the reference, which answers that request with an error. -/
theorem env002_host_needed :
    XRun env002_nameKeyed env002_C env002_s0
        [(env002_s0, .request 3 5 .accepted, env002Enq env002_s0 3 5)] ∧
      ¬ XRun RefExec env002_C env002_s0
        [(env002_s0, .request 3 5 .accepted, env002Enq env002_s0 3 5)] ∧
      ¬ ENV_002_host env002_C
        [(env002_s0, (.request 3 5 .accepted : XLbl Nat Nat), env002Enq env002_s0 3 5)] := by
  refine ⟨⟨rfl, rfl, trivial⟩, fun hr => ?_, fun h => ?_⟩
  · exact absurd (env002_ref_unreg env002_3_unreg hr.2.1).1 (by decide)
  · exact env002_3_unreg (h _ List.mem_cons_self 3 5 .accepted rfl)

end Host

/-- ✗ A host that injects into the unregistered place `3` does not meet the host block. -/
@[evidence forbids ENV_002_host]
theorem ENV_002_host_forbids_unregistered :
    ¬ ENV_002_host env002_C
      [(env002_s0, (.request 3 5 .accepted : XLbl Nat Nat), env002Enq env002_s0 3 5)] :=
  fun h => env002_3_unreg (h _ List.mem_cons_self 3 5 .accepted rfl)

/-- The host block is met by a run of the reference with a request into the registered place `0`
that is accepted. -/
@[evidence nonvacuous ENV_002_host]
theorem ENV_002_host_nonvacuous :
    XRun RefExec env002_C env002_s0
        [(env002_s0, .request 0 5 .accepted, env002Enq env002_s0 0 5)] ∧
      ENV_002_host env002_C
        [(env002_s0, (.request 0 5 .accepted : XLbl Nat Nat), env002Enq env002_s0 0 5)] := by
  refine ⟨⟨rfl, rfl, trivial⟩, fun st hm p x r hl => ?_⟩
  rw [List.mem_singleton] at hm
  subst hm
  cases hl
  decide

end Libpetri.Spec
