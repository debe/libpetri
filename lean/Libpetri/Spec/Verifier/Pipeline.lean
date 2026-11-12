import Libpetri.Spec.Req.VER_003

set_option linter.missingDocs true
set_option autoImplicit false

/-!
# The verifier's pipeline (RefVerifier L1b)

`Result.lean` dispatches pure phases (`firstDecided`): the first phase that decides wins. The
runtimes run the same dispatch as a sequence of **named steps** that call a **solver** and share
one **stop** (the total budget and cancellation of [VER-013]). This file adds those three things
and nothing else.

* **The solver** (`Oracle`): a call sends a script and gets a reply, either a verdict line
  (`sat`, `unsat`, `unknown`) or a failure with a reason (missing executable, version too old,
  `timeout` line, watchdog kill, `(error …)` line, other stderr text, unexpected stdout, non-zero
  exit, or not started because the run was stopped). How raw streams are classified into a reply
  is VER-013's block-local function, not modelled here.
* **A phase program** (`PhaseProg`): a phase that may ask the solver (`ask`) and poll the stop
  inside a long loop (`poll`) before it returns a `PhaseOut`. A phase of `Result.lean` is a
  program that asks nothing (`Step.lift`). `Yields R P out` says the program `P` can return `out`
  when every solver call comes back with a reply the relation `R` allows; `byOracle O` allows the
  oracle's reply or a refusal to start, `failing` allows only failures.
* **The stop** (`Stop`): the stop seen at the i-th poll, `none` or why (`budget N`, `cancelled`).
  The run's trail (`Trail`) counts the polls, names the running step, records the first stop and
  the step it was charged to, the steps entered and the scripts started. A stop is sticky: once
  recorded, every later poll answers "stopped". A solver call polls before it starts the process
  (no process starts once stopped; the call then fails with `notStarted`) and once after it
  returns (Rust `note_if_expired`), so a deadline that passed during the call is charged to the
  running step.
* **The pipeline** (`runPipeline`): the steps in order; a step whose guard (`applies`) is false is
  skipped without a poll; an applicable step first polls (the poll is charged to the step that
  just ended, or to `net preparation` before the first step), then is entered and run; the first
  decision wins. `pipeVerify` is the decider: poll on entry, refuse an unresolved property place,
  build the verified query, run the pipeline, pack the result. An `Unknown` reached after a stop
  carries the stop's reason, `total verification budget of N ms exhausted during <step>` or
  `verification cancelled during <step>`; a `Proven` or `Violated` reached before the stop stands.
* **The order** (`Before`, `Ordered`): `Before names a b` says every `a` of the step list comes
  before every `b`; then in every run every entry of `a` precedes every entry of `b`
  (`runPipeline_ordered`). `rtStepNames` is the runtimes' step list (the same thirteen names in
  Rust, Java and TypeScript).
* **The reference** (`rtPipeline`): the runtimes' step names, where the reference enumeration of
  `Result.lean` sits at `state-space enumeration` and every other step is not entered (its phase
  slice is a later block's). Without a stop it is `refVerify` (`pipeVerify_noStop`); with any
  stop and any oracle it meets VER-003 (`pipeVerify_VER_003`), from the general
  `pipeVerify_VER_003_of`: a pipeline whose steps keep the phase contract under the oracle
  (`ProgSound`) meets VER-003 whatever the stop does.
-/

namespace Libpetri.Spec.Verifier

open Libpetri Libpetri.Novel.Seam

/-! ## The solver -/

/-- The verdict line of a solver reply ([VER-013] reply classification). -/
inductive SolverAnswer where
  /-- `sat`. -/
  | sat
  /-- `unsat`. -/
  | unsat
  /-- `unknown`. -/
  | unknown
  deriving DecidableEq, Repr

/-- Why a solver call gave no verdict line ([VER-013]). -/
inductive SolverFailure where
  /-- No executable resolved (`z3` on `PATH`, `LIBPETRI_Z3`). -/
  | missing
  /-- The executable is below 4.8.0 or reports no version. -/
  | tooOld
  /-- The `timeout` line of the `-T` backstop. -/
  | timeoutLine
  /-- The watchdog killed the process. -/
  | killed
  /-- An `(error …)` line, on stdout or stderr. -/
  | errorLine
  /-- Other stderr text. -/
  | stderrText
  /-- Unexpected stdout. -/
  | unexpected
  /-- A non-zero exit. -/
  | nonZeroExit
  /-- The run was stopped (total budget or cancellation): no process was started. -/
  | notStarted
  deriving DecidableEq, Repr

/-- A solver reply: a verdict line, or a failure with its reason. -/
inductive SolverReply where
  /-- The first verdict line. -/
  | answer (a : SolverAnswer)
  /-- No verdict line: the failure and its reason. -/
  | failure (f : SolverFailure) (reason : String)
  deriving DecidableEq, Repr

/-- **The solver**: the reply to a script. A pure function, so equal scripts get equal replies:
no solver state survives a query ([VER-013]). -/
abbrev Oracle : Type := String → SolverReply

/-! ## Phase programs -/

/-- **A phase program**: return, ask the solver, or poll the stop. -/
inductive PhaseProg (α : Type) where
  /-- The phase returns `a`. -/
  | done (a : α)
  /-- One solver process for `script`; the phase continues with the reply. -/
  | ask (script : String) (k : SolverReply → PhaseProg α)
  /-- A deadline poll inside a long loop ([VER-013]: graph builds, siphon search, Farkas, the
  colour-slot simplex); the phase continues with whether the run is stopped. -/
  | poll (k : Bool → PhaseProg α)

/-- **The program can return `a`** when every solver call comes back with a reply `R` allows and
every poll answers either way. -/
inductive Yields {α : Type} (R : String → SolverReply → Prop) : PhaseProg α → α → Prop where
  /-- A returned value. -/
  | done (a : α) : Yields R (.done a) a
  /-- A solver call answered with an allowed reply. -/
  | ask {s : String} {k : SolverReply → PhaseProg α} {r : SolverReply} {a : α} :
      R s r → Yields R (k r) a → Yields R (.ask s k) a
  /-- A poll answered either way. -/
  | poll {k : Bool → PhaseProg α} {a : α} (b : Bool) : Yields R (k b) a → Yields R (.poll k) a

/-- The replies a run with the oracle `O` can see: the oracle's reply, or a refusal to start a
process once the run is stopped. -/
def byOracle (O : Oracle) (s : String) (r : SolverReply) : Prop :=
  r = O s ∨ ∃ why, r = .failure .notStarted why

/-- The replies of a solver that always fails ([VER-013] AC2-AC4: missing, too old, timeout,
error line, killed, non-zero exit). -/
def failing (_ : String) (r : SolverReply) : Prop :=
  ∃ f why, r = .failure f why

theorem Yields.done_iff {α : Type} {R : String → SolverReply → Prop} {a b : α} :
    Yields R (.done a) b ↔ b = a := by
  constructor
  · intro h; cases h; rfl
  · intro h; subst h; exact .done _

/-! ## The stop and the trail -/

/-- What stopped a run ([VER-013]). -/
inductive StopKind where
  /-- The total budget of `ms` milliseconds ran out. -/
  | budget (ms : Nat)
  /-- The caller cancelled. -/
  | cancelled
  deriving DecidableEq, Repr

/-- **The stop**: what the i-th poll of a run sees (`none`: not stopped). The poll counter stands
for the clock and the cancellation flag; nothing is assumed about the function. -/
abbrev Stop : Type := Nat → Option StopKind

/-- No total budget and no cancellation. -/
def noStop : Stop := fun _ => none

/-- A stop of kind `k` from the `i`-th poll on. -/
def stopFrom (i : Nat) (k : StopKind) : Stop := fun j => if i ≤ j then some k else none

/-- **The stop reason** ([VER-013]), naming the step the stop was charged to. -/
def stopReason : StopKind → String → String
  | .budget ms, step => "total verification budget of " ++ toString ms ++ " ms exhausted during " ++ step
  | .cancelled, step => "verification cancelled during " ++ step

theorem stopReason_ne_empty (k : StopKind) (n : String) : stopReason k n ≠ "" := by
  intro h
  have := congrArg String.length h
  cases k <;> simp [stopReason] at this

/-- The reason of a solver call refused because the run is stopped (Rust `total_budget::clamp`). -/
def refusedReason : Option (StopKind × String) → String
  | some (.budget ms, _) => "total verification budget of " ++ toString ms ++ " ms exhausted; z3 not started"
  | some (.cancelled, _) => "verification cancelled; z3 not started"
  | none => "z3 not started"

/-- **The trail of a run**. -/
structure Trail where
  /-- Polls made so far. -/
  polls : Nat := 0
  /-- The step running now: `net preparation` until the first step is entered. -/
  running : String := "net preparation"
  /-- The route of the running step. -/
  route : Route := .unavailable
  /-- The first stop seen, and the step it was charged to. -/
  stopped : Option (StopKind × String) := none
  /-- The steps entered, in order. -/
  entered : List String := []
  /-- The scripts a solver process was started for, in order. -/
  started : List String := []

/-- **A poll**: stopped if a stop was already recorded, or the stop function says so now; the
first stop is charged to the running step. -/
def pollStop (stop : Stop) (t : Trail) : Bool × Trail :=
  match t.stopped with
  | some _ => (true, { t with polls := t.polls + 1 })
  | none =>
    match stop t.polls with
    | some k => (true, { t with polls := t.polls + 1, stopped := some (k, t.running) })
    | none => (false, { t with polls := t.polls + 1 })

section PollLemmas

variable {stop : Stop} {t : Trail}

theorem pollStop_frame :
    (pollStop stop t).2.running = t.running ∧ (pollStop stop t).2.route = t.route ∧
      (pollStop stop t).2.entered = t.entered ∧ (pollStop stop t).2.started = t.started := by
  unfold pollStop
  cases t.stopped with
  | some _ => exact ⟨rfl, rfl, rfl, rfl⟩
  | none => cases stop t.polls <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem pollStop_keeps {x : StopKind × String} (h : t.stopped = some x) :
    (pollStop stop t).1 = true ∧ (pollStop stop t).2.stopped = some x := by
  unfold pollStop
  simp [h]

theorem pollStop_false (h : (pollStop stop t).1 = false) :
    t.stopped = none ∧ (pollStop stop t).2.stopped = none := by
  obtain ⟨p, r, rt, st, e, sd⟩ := t
  cases st with
  | some x => simp [pollStop] at h
  | none =>
    cases hk : stop p with
    | some k => simp [pollStop, hk] at h
    | none => simp [pollStop, hk]

theorem pollStop_true (h : (pollStop stop t).1 = true) :
    ∃ x, (pollStop stop t).2.stopped = some x := by
  obtain ⟨p, r, rt, st, e, sd⟩ := t
  cases st with
  | some x => exact ⟨x, rfl⟩
  | none =>
    cases hk : stop p with
    | some k => exact ⟨(k, r), by simp [pollStop, hk]⟩
    | none => simp [pollStop, hk] at h

theorem pollStop_noStop (h : t.stopped = none) :
    pollStop noStop t = (false, { t with polls := t.polls + 1 }) := by
  unfold pollStop
  rw [h]
  rfl

end PollLemmas

/-! ## Running a phase program -/

/-- **Run a phase program** with the oracle `O` under the stop `stop`. A solver call polls first:
when stopped, no process starts and the reply is `notStarted`; otherwise the script is recorded
as started, the oracle answers, and a second poll charges a stop that came during the call to
the running step. -/
def execProg {α : Type} (O : Oracle) (stop : Stop) : PhaseProg α → Trail → α × Trail
  | .done a, t => (a, t)
  | .ask s k, t =>
    if (pollStop stop t).1 then
      execProg O stop (k (.failure .notStarted (refusedReason (pollStop stop t).2.stopped)))
        (pollStop stop t).2
    else
      execProg O stop (k (O s))
        (pollStop stop { (pollStop stop t).2 with started := (pollStop stop t).2.started ++ [s] }).2
  | .poll k, t => execProg O stop (k (pollStop stop t).1) (pollStop stop t).2

section ExecLemmas

variable {α : Type} {O : Oracle} {stop : Stop}

/-- What a run returns is something the program can return under the oracle. -/
theorem execProg_yields : ∀ (P : PhaseProg α) (t : Trail),
    Yields (byOracle O) P (execProg O stop P t).1
  | .done a, t => .done a
  | .ask s k, t => by
    simp only [execProg]
    split
    · exact .ask (Or.inr ⟨_, rfl⟩) (execProg_yields _ _)
    · exact .ask (Or.inl rfl) (execProg_yields _ _)
  | .poll k, t => by
    simp only [execProg]
    exact .poll _ (execProg_yields _ _)

/-- A run leaves the running step, its route and the entered steps as they were. -/
theorem execProg_frame : ∀ (P : PhaseProg α) (t : Trail),
    (execProg O stop P t).2.running = t.running ∧ (execProg O stop P t).2.route = t.route ∧
      (execProg O stop P t).2.entered = t.entered
  | .done a, t => ⟨rfl, rfl, rfl⟩
  | .ask s k, t => by
    simp only [execProg]
    obtain ⟨h1, h2, h3, -⟩ := pollStop_frame (stop := stop) (t := t)
    split
    · obtain ⟨g1, g2, g3⟩ := execProg_frame (k _) (pollStop stop t).2
      exact ⟨g1.trans h1, g2.trans h2, g3.trans h3⟩
    · obtain ⟨g1, g2, g3⟩ := execProg_frame (k (O s))
        (pollStop stop { (pollStop stop t).2 with started := (pollStop stop t).2.started ++ [s] }).2
      obtain ⟨f1, f2, f3, -⟩ := pollStop_frame (stop := stop)
        (t := { (pollStop stop t).2 with started := (pollStop stop t).2.started ++ [s] })
      exact ⟨g1.trans (f1.trans h1), g2.trans (f2.trans h2), g3.trans (f3.trans h3)⟩
  | .poll k, t => by
    simp only [execProg]
    obtain ⟨h1, h2, h3, -⟩ := pollStop_frame (stop := stop) (t := t)
    obtain ⟨g1, g2, g3⟩ := execProg_frame (k (pollStop stop t).1) (pollStop stop t).2
    exact ⟨g1.trans h1, g2.trans h2, g3.trans h3⟩

/-- **The first stop stays recorded, and no process starts after it.** -/
theorem execProg_after_stop {x : StopKind × String} : ∀ (P : PhaseProg α) (t : Trail),
    t.stopped = some x →
      (execProg O stop P t).2.stopped = some x ∧ (execProg O stop P t).2.started = t.started
  | .done a, t, _ => ⟨by assumption, rfl⟩
  | .ask s k, t, h => by
    simp only [execProg]
    obtain ⟨hp, hs⟩ := pollStop_keeps (stop := stop) h
    rw [if_pos hp]
    obtain ⟨g1, g2⟩ := execProg_after_stop (k _) (pollStop stop t).2 hs
    exact ⟨g1, g2.trans (pollStop_frame.2.2.2)⟩
  | .poll k, t, h => by
    simp only [execProg]
    obtain ⟨-, hs⟩ := pollStop_keeps (stop := stop) h
    obtain ⟨g1, g2⟩ := execProg_after_stop (k _) (pollStop stop t).2 hs
    exact ⟨g1, g2.trans (pollStop_frame.2.2.2)⟩

/-- A recorded stop is never replaced. -/
theorem execProg_keeps {x : StopKind × String} {P : PhaseProg α} {t : Trail}
    (h : t.stopped = some x) : (execProg O stop P t).2.stopped = some x :=
  (execProg_after_stop P t h).1

/-- A program that asks nothing and polls nothing returns its value and changes nothing. -/
theorem execProg_done {a : α} {t : Trail} : execProg O stop (.done a) t = (a, t) := rfl

end ExecLemmas

/-! ## The pipeline -/

/-- **A pipeline step**: a name (the step a stop is charged to), the route its decision reports,
a guard (a step whose guard fails is not entered and makes no poll) and its program. Generic in
the query type `Q`, so the ν pipeline can use a query that carries match specifications. -/
structure GStep (Q : Type) where
  /-- The step's name. -/
  name : String
  /-- The route its decision reports, and the route of a stop charged to it. -/
  route : Route
  /-- The guard: whether the step is entered for these options and this query. -/
  applies : Options → Q → Bool := fun _ _ => true
  /-- The step's program. -/
  run : Options → Q → PhaseProg PhaseOut

/-- A pure phase of `Result.lean` as a pipeline step that is always entered and asks nothing. -/
def Step.lift {K : Type} (s : Step K) : GStep (Query K) :=
  { name := s.name, route := s.route, run := fun o q => .done (s.run o q) }

/-- Entering a step: it becomes the running step, with its route, and is logged. -/
def Trail.enter {Q : Type} (s : GStep Q) (t : Trail) : Trail :=
  { t with running := s.name, route := s.route, entered := t.entered ++ [s.name] }

/-- **The pipeline**: the steps in order. A step whose guard fails is skipped without a poll. An
applicable step polls first, before it is recorded as running, so a stop found there is charged
to the step that just ended; when stopped the pipeline ends with no decision. Otherwise the step
is entered and run; an aside goes on to the next step, a decision ends the pipeline. -/
def runPipeline {Q : Type} (O : Oracle) (stop : Stop) (o : Options) (q : Q) :
    List (GStep Q) → Trail → Option (Route × PhaseOut) × Trail
  | [], t => (none, t)
  | s :: ss, t =>
    if s.applies o q then
      if (pollStop stop t).1 then (none, (pollStop stop t).2)
      else
        match execProg O stop (s.run o q) ((pollStop stop t).2.enter s) with
        | (.aside _, t') => runPipeline O stop o q ss t'
        | (.decided v tr c, t') => (some (s.route, .decided v tr c), t')
    else runPipeline O stop o q ss t

section PipelineLemmas

variable {Q : Type} {O : Oracle} {stop : Stop} {o : Options} {q : Q}

/-- **A decision comes from one applicable step**, as something its program can return under the
oracle, never an aside. -/
theorem runPipeline_step : ∀ {steps : List (GStep Q)} {t : Trail} {r : Route} {out : PhaseOut},
    (runPipeline O stop o q steps t).1 = some (r, out) →
      ∃ s ∈ steps, s.route = r ∧ s.applies o q = true ∧ Yields (byOracle O) (s.run o q) out ∧
        ∀ n, out ≠ .aside n
  | [], t, r, out, h => by simp [runPipeline] at h
  | s :: ss, t, r, out, h => by
    simp only [runPipeline] at h
    split at h
    · rename_i happ
      split at h
      · simp at h
      · split at h
        · rename_i n t' he
          obtain ⟨s', hs', h1, h2, h3, h4⟩ := runPipeline_step h
          exact ⟨s', List.mem_cons_of_mem _ hs', h1, h2, h3, h4⟩
        · rename_i v tr c t' he
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hy := execProg_yields (O := O) (stop := stop) (s.run o q)
            ((pollStop stop t).2.enter s)
          rw [he] at hy
          exact ⟨s, List.mem_cons_self, rfl, happ, hy, fun n hn => by cases hn⟩
    · obtain ⟨s', hs', h1, h2, h3, h4⟩ := runPipeline_step h
      exact ⟨s', List.mem_cons_of_mem _ hs', h1, h2, h3, h4⟩

/-- **The steps entered are logged in pipeline order**: the log grows by a sublist of the step
names. -/
theorem runPipeline_entered : ∀ (steps : List (GStep Q)) (t : Trail),
    ∃ l, (runPipeline O stop o q steps t).2.entered = t.entered ++ l ∧
      l.Sublist (steps.map GStep.name)
  | [], t => ⟨[], by simp [runPipeline]⟩
  | s :: ss, t => by
    simp only [runPipeline]
    split
    · split
      · exact ⟨[], by rw [pollStop_frame.2.2.1]; simp, List.nil_sublist _⟩
      · have hf := (execProg_frame (O := O) (stop := stop) (s.run o q)
          ((pollStop stop t).2.enter s)).2.2
        have he : ((pollStop stop t).2.enter s).entered = t.entered ++ [s.name] := by
          simp only [Trail.enter]; rw [pollStop_frame.2.2.1]
        split
        · rename_i n t' hx
          rw [hx] at hf
          obtain ⟨l, hl, hsub⟩ := runPipeline_entered ss t'
          refine ⟨s.name :: l, ?_, ?_⟩
          · rw [hl, hf, he]; simp
          · simpa using hsub
        · rename_i v tr c t' hx
          rw [hx] at hf
          exact ⟨[s.name], by rw [hf, he], by simp⟩
    · obtain ⟨l, hl, hsub⟩ := runPipeline_entered ss t
      exact ⟨l, hl, hsub.trans (List.sublist_cons_self _ _)⟩

/-- **After a stop the pipeline decides nothing, starts no process, and keeps the first stop.** -/
theorem runPipeline_after_stop {x : StopKind × String} : ∀ (steps : List (GStep Q)) (t : Trail),
    t.stopped = some x →
      (runPipeline O stop o q steps t).1 = none ∧
        (runPipeline O stop o q steps t).2.stopped = some x ∧
        (runPipeline O stop o q steps t).2.started = t.started
  | [], t, h => ⟨rfl, h, rfl⟩
  | s :: ss, t, h => by
    simp only [runPipeline]
    split
    · obtain ⟨hp, hs⟩ := pollStop_keeps (stop := stop) h
      rw [if_pos hp]
      exact ⟨rfl, hs, pollStop_frame.2.2.2⟩
    · exact runPipeline_after_stop ss t h

/-- A recorded stop is never replaced. -/
theorem runPipeline_keeps {x : StopKind × String} : ∀ (steps : List (GStep Q)) (t : Trail),
    t.stopped = some x → (runPipeline O stop o q steps t).2.stopped = some x :=
  fun steps t h => (runPipeline_after_stop steps t h).2.1

/-- **Without a stop, a pipeline of pure phases is `firstDecided`.** -/
theorem runPipeline_lift_noStop {K : Type} {q : Query K} : ∀ (steps : List (Step K)) (t : Trail),
    t.stopped = none →
      (runPipeline O noStop o q (steps.map Step.lift) t).1 = firstDecided steps o q
  | [], t, _ => rfl
  | s :: ss, t, h => by
    simp only [List.map_cons, runPipeline, Step.lift, pollStop_noStop h, if_true,
      Bool.false_eq_true, if_false, execProg_done, firstDecided]
    cases hs : s.run o q with
    | aside n =>
      exact runPipeline_lift_noStop ss _ (by simp only [Trail.enter]; exact h)
    | decided v tr c => rfl

end PipelineLemmas

/-! ## The order of the steps -/

/-- **`a` before `b` in a list**: the list splits so that every `a` is in the first part, every
`b` in the second, and each part holds one of them. -/
def Before {α : Type} [DecidableEq α] (names : List α) (a b : α) : Prop :=
  ∃ k, k < names.length + 1 ∧ a ∈ names.take k ∧ b ∉ names.take k ∧ a ∉ names.drop k ∧
    b ∈ names.drop k

instance {α : Type} [DecidableEq α] (names : List α) (a b : α) : Decidable (Before names a b) := by
  unfold Before; infer_instance

/-- **No `b` entry precedes an `a` entry** in a log. -/
def Ordered {α : Type} (e : List α) (a b : α) : Prop :=
  ∃ e₁ e₂, e = e₁ ++ e₂ ∧ b ∉ e₁ ∧ a ∉ e₂

/-- An order of the list is kept by every sublist of it. -/
theorem Before.ordered {α : Type} [DecidableEq α] {names e : List α} {a b : α}
    (h : Before names a b) (hs : e.Sublist names) : Ordered e a b := by
  obtain ⟨k, -, -, hb, ha, -⟩ := h
  rw [← List.take_append_drop k names] at hs
  obtain ⟨e₁, e₂, rfl, h1, h2⟩ := List.sublist_append_iff.mp hs
  exact ⟨e₁, e₂, rfl, fun hm => hb (h1.subset hm), fun hm => ha (h2.subset hm)⟩

/-- **In every run, the steps are entered in the pipeline's order**: when `a` is before `b` in
the step names, no entry of `b` precedes an entry of `a`. -/
theorem runPipeline_ordered {Q : Type} {O : Oracle} {stop : Stop} {o : Options} {q : Q}
    {steps : List (GStep Q)} {t : Trail} (ht : t.entered = []) {a b : String}
    (h : Before (steps.map GStep.name) a b) :
    Ordered (runPipeline O stop o q steps t).2.entered a b := by
  obtain ⟨l, hl, hs⟩ := runPipeline_entered (O := O) (stop := stop) (o := o) (q := q) steps t
  rw [hl, ht, List.nil_append]
  exact h.ordered hs

/-- **The runtimes' pipeline steps**, in order, as Rust (`smt_verifier.rs` `step!`), Java
(`SmtVerifier.enter`) and TypeScript (`SmtVerifier.enter`) name them. Before the first is
`net preparation`. The linear bound appears twice: ahead of the enumeration on a net the
enumeration route takes, and after the P-invariants otherwise; a run enters at most one. -/
def rtStepNames : List String :=
  ["Route B (ν name-partition graph)", "linear bound", "state-space enumeration", "flattening",
   "structural pre-check", "P-invariant computation", "linear bound", "state-equation phase",
   "firing-bound phase", "colour-slot bound", "witness phase", "IC3/PDR query",
   "certificate check"]

/-- The orders the spec states as MUST: the linear bound ([VER-015]), the state-equation phase
([VER-018]), the firing bound ([VER-019]) and the witness phase ([VER-025]) before the fixpoint
query; the firing bound after the state-equation phase; the enumeration ([VER-017]) and Route B
([VER-012]) before the SMT pipeline. -/
theorem rtStepNames_order :
    Before rtStepNames "linear bound" "IC3/PDR query" ∧
    Before rtStepNames "state-equation phase" "IC3/PDR query" ∧
    Before rtStepNames "firing-bound phase" "IC3/PDR query" ∧
    Before rtStepNames "witness phase" "IC3/PDR query" ∧
    Before rtStepNames "state-equation phase" "firing-bound phase" ∧
    Before rtStepNames "state-space enumeration" "flattening" ∧
    Before rtStepNames "Route B (ν name-partition graph)" "state-space enumeration" ∧
    Before rtStepNames "IC3/PDR query" "certificate check" := by
  decide

/-- The second linear bound comes after the enumeration, so "the linear bound before the
enumeration" is not an order of the step list; it holds of the runs where the enumeration
route applies (VER-015's line). -/
theorem rtStepNames_not_before :
    ¬ Before rtStepNames "linear bound" "state-space enumeration" := by
  decide

/-! ## The decider -/

/-- The reason a stop recorded in the trail gives. -/
def Trail.stopText (t : Trail) : String :=
  match t.stopped with
  | some (k, n) => stopReason k n
  | none => "verification stopped"

theorem Trail.stopText_ne_empty (t : Trail) : t.stopText ≠ "" := by
  unfold Trail.stopText
  split
  · exact stopReason_ne_empty _ _
  · decide

/-- The result of a stopped run: `Unknown` with the stop reason, the route of the step it was
charged to. -/
def stoppedResult {K : Type} (t : Trail) : Result K :=
  { verdict := .unknown t.stopText, route := t.route }

/-- **A verdict reached before the stop stands**; an `Unknown` reached after a stop carries the
stop reason (Rust `finish`). -/
def finishVerdict (t : Trail) : Verdict → Verdict
  | .unknown why =>
    match t.stopped with
    | some (k, n) => .unknown (stopReason k n)
    | none => .unknown why
  | v => v

theorem finishVerdict_proven (t : Trail) (m : String) :
    finishVerdict t (.proven m) = .proven m := rfl

theorem finishVerdict_violated (t : Trail) : finishVerdict t .violated = .violated := rfl

theorem finishVerdict_unknown {t : Trail} {v : Verdict} {why : String}
    (h : finishVerdict t v = .unknown why) : ∃ why', v = .unknown why' := by
  cases v with
  | unknown w => exact ⟨w, rfl⟩
  | proven m => simp [finishVerdict] at h
  | violated => simp [finishVerdict] at h

theorem finishVerdict_proven_iff {t : Trail} {v : Verdict} {m : String} :
    finishVerdict t v = .proven m ↔ v = .proven m := by
  cases v with
  | unknown w =>
    simp only [finishVerdict]
    split <;> simp
  | proven _ => rfl
  | violated => simp [finishVerdict]

theorem finishVerdict_violated_iff {t : Trail} {v : Verdict} :
    finishVerdict t v = .violated ↔ v = .violated := by
  cases v with
  | unknown w =>
    simp only [finishVerdict]
    split <;> simp
  | proven _ => simp [finishVerdict]
  | violated => rfl

theorem finishVerdict_noStop {t : Trail} (h : t.stopped = none) (v : Verdict) :
    finishVerdict t v = v := by
  cases v with
  | unknown w => simp [finishVerdict, h]
  | _ => rfl

section Decider

variable {K : Type} [DecidableEq K]

/-- **Pack a pipeline outcome** into the result record: a decision reports its route, trace,
confirmation, the timing label (`UNTIMED_NET` on an untimed net; on a timed net `TIMED_EXACT`
for Route B, which explores timed behaviour, and `UNTIMED_ABSTRACTION` for every other route)
and the invariants `invs`, its verdict finished by the stop; no decision is the stop's `Unknown`
when the run was stopped, and `Unknown` "no route decided" otherwise. -/
def packResult (X : Reference.TimedNet K) (invs : List (PInv K)) :
    Option (Route × PhaseOut) × Trail → Result K
  | (some (route, .decided v tr c), t) =>
    { verdict := finishVerdict t v, route, trace := tr, confirmed := c,
      timing := if v = .violated then
        some (if Untimed X then .untimedNet else if route = .nuScg then .timedExact
          else .untimedAbstraction) else none,
      invariants := invs }
  | (_, t) =>
    match t.stopped with
    | some _ => stoppedResult t
    | none => { verdict := .unknown "no route decided", invariants := invs }

/-- **The pipeline decider**: poll on entry (a call stopped before it starts is `Unknown`
naming `net preparation`), refuse an unresolved property place, build the verified query with
`abs`, run the steps, pack the result with the invariants `inv` reports. -/
def pipeVerify (abs : Abs K) (inv : Query K → List (PInv K)) (steps : List (GStep (Query K)))
    (O : Oracle) (stop : Stop) : Decider K := fun o X φ m0 =>
  if (pollStop stop {}).1 then stoppedResult (pollStop stop {}).2
  else if Unresolved X φ m0 then
    { verdict := .unknown
        "the property names a place that the net does not declare and the initial marking does not mark" }
  else
    match abs o X φ m0 with
    | .error why => { verdict := .unknown "the verified net cannot be built", notes := [why] }
    | .ok q => packResult X (inv q) (runPipeline O stop o q steps (pollStop stop {}).2)

/-- **The phase contract for a program** ([VER-003] through `PhaseSound`): whatever the program
returns under replies `R` allows, a `Proven` names a method and holds on every reachable
marking, a confirmed `Violated` carries a firing sequence to a violating marking, an `Unknown`
has a reason. A solver-backed phase states the solver's soundness inside `R`. -/
def ProgSound (R : String → SolverReply → Prop) (V : SafetyViolRel K)
    (P : Options → Query K → PhaseProg PhaseOut) : Prop :=
  ∀ o q out, Yields R (P o q) out →
    (∀ meth tr c, out = .decided (.proven meth) tr c →
      meth ≠ "" ∧ ∀ f, Reference.Reach q.net.net q.init f → ¬ V o.assumeNoReaping q.net q.prop f) ∧
    (∀ tr, out = .decided .violated tr (some true) →
      ∃ f, Reference.Run q.net.net tr q.init f ∧ V o.assumeNoReaping q.net q.prop f) ∧
    (∀ why tr c, out = .decided (.unknown why) tr c → why ≠ "")

/-- A sound pure phase is a sound program, under any replies. -/
theorem PhaseSound.prog {V : SafetyViolRel K} {P : Phase K} (h : PhaseSound V P)
    (R : String → SolverReply → Prop) : ProgSound R V (fun o q => .done (P o q)) := by
  intro o q out hy
  rw [Yields.done_iff] at hy
  subst hy
  exact h o q

end Decider

/-- **A sound pipeline meets VER-003 whatever the stop does.** The premises: every step keeps the
phase contract under the oracle's replies (including refusals); a step's decision names a route
other than `Unavailable`; a `Violated` decided at a violating initial marking has the empty trace,
is not marked unconfirmed, and is confirmed unless Route B decided it; the reported invariants are
conserved. -/
theorem pipeVerify_VER_003_of {K : Type} [LinearOrder K] {V : SafetyViolRel K} {abs : Abs K}
    {inv : Query K → List (PInv K)} {steps : List (GStep (Query K))} {O : Oracle} {stop : Stop}
    (hs : ∀ s ∈ steps, ProgSound (byOracle O) V s.run)
    (hr : ∀ s ∈ steps, s.route ≠ .unavailable)
    (hinit : ∀ o q t tr c r, V o.assumeNoReaping q.net q.prop q.init →
      (runPipeline O stop o q steps t).1 = some (r, .decided .violated tr c) →
        tr = [] ∧ c ≠ some false ∧ (r ≠ .nuScg → c = some true))
    (hinv : ∀ q, ∀ i ∈ inv q, ∀ f, ReachF RefFire q.net.net q.init f → i.dot f = i.const) :
    VER_003 RefFire V abs (pipeVerify abs inv steps O stop) := by
  intro o X φ m0
  by_cases hp : (pollStop stop {}).1 = true
  · simp only [pipeVerify, hp, if_true, stoppedResult]
    refine ⟨?_, by simp, fun _ => ⟨_, rfl⟩, fun _ _ => ⟨_, rfl⟩, ?_, by simp, by simp, by simp⟩
    · intro why h
      simp only [Verdict.unknown.injEq] at h
      subst h
      exact Trail.stopText_ne_empty _
    · intro q _
      exact ⟨by simp, by simp, by simp, by simp⟩
  have hp' : (pollStop stop {}).1 = false := by simpa using hp
  by_cases hu : Unresolved X φ m0
  · simp [pipeVerify, hp', hu]
  cases ha : abs o X φ m0 with
  | error e => simp [pipeVerify, hp', hu, ha]
  | ok q =>
    simp only [pipeVerify, hp', Bool.false_eq_true, if_false, hu, ha]
    generalize hR : runPipeline O stop o q steps (pollStop stop {}).2 = R
    obtain ⟨res, t⟩ := R
    have hq : ∀ q', Except.ok (ε := String) q = .ok q' → q = q' := by
      intro q' h; simpa using h
    rcases res with _ | ⟨r, out⟩
    · -- no decision
      simp only [packResult]
      split
      · simp only [stoppedResult]
        refine ⟨?_, by simp, fun h => h.1.elim, by simp, ?_, by simp, by simp, by simp⟩
        · intro why h
          simp only [Verdict.unknown.injEq] at h
          subst h
          exact Trail.stopText_ne_empty _
        · intro q' _
          exact ⟨by simp, by simp, by simp, by simp⟩
      · refine ⟨by simp, by simp, fun h => h.1.elim, by simp, ?_, by simp, by simp, by simp⟩
        intro q' hq'
        obtain rfl := hq q' hq'
        exact ⟨by simp, by simp, by simp, hinv q⟩
    · have h1 : (runPipeline O stop o q steps (pollStop stop {}).2).1 = some (r, out) := by
        rw [hR]
      obtain ⟨s, hsm, hsr, -, hy, hna⟩ := runPipeline_step h1
      obtain ⟨hpv, hvv, hkv⟩ := hs s hsm o q out hy
      cases out with
      | aside n => exact absurd rfl (hna n)
      | decided v tr c =>
        simp only [packResult]
        refine ⟨?_, ?_, fun h => h.1.elim, by simp, ?_, ?_, ?_, ?_⟩
        · intro why hw
          obtain ⟨why', rfl⟩ := finishVerdict_unknown hw
          simp only [finishVerdict] at hw
          split at hw
          · simp only [Verdict.unknown.injEq] at hw
            subst hw
            exact stopReason_ne_empty _ _
          · simp only [Verdict.unknown.injEq] at hw
            subst hw
            exact hkv why' tr c rfl
        · intro meth hm
          rw [finishVerdict_proven_iff] at hm
          subst hm
          exact (hpv meth tr c rfl).1
        · intro q' hq'
          obtain rfl := hq q' hq'
          refine ⟨?_, ?_, ?_, hinv q⟩
          · intro hvi hc
            rw [finishVerdict_violated_iff] at hvi
            subst hvi
            subst hc
            obtain ⟨f, hrun, hvf⟩ := hvv tr rfl
            exact ⟨f, runF_ref.mpr hrun, hvf⟩
          · intro hi hvi
            rw [finishVerdict_violated_iff] at hvi
            subst hvi
            exact hinit o q _ tr c r hi h1
          · intro meth hm f hf
            rw [finishVerdict_proven_iff] at hm
            subst hm
            exact (hpv meth tr c rfl).2 f ((reachF_ref _ _ _).mp hf)
        · intro hvi
          have : v ≠ .violated := fun h => hvi (by rw [h]; rfl)
          simp [this]
        · intro hvi
          rw [finishVerdict_violated_iff] at hvi
          subst hvi
          by_cases hT : Untimed X <;> by_cases hnu : r = .nuScg <;> simp [hT, hnu]
        · intro _
          simpa [hsr] using hr s hsm

/-! ## The reference pipeline -/

section Reference

variable {K : Type} [LinearOrder K] [Hashable K]

/-- The reference dispatch of `Result.lean` as one phase: the first decision of the initial
marking, dead initial marking and enumeration phases, or an aside. -/
def refEnumPhase : Phase K := fun o q =>
  match firstDecided refSteps o q with
  | some (_, out) => out
  | none => .aside "no reference phase decided"

/-- The reference dispatch as a program that asks nothing. -/
def refEnumProg (o : Options) (q : Query K) : PhaseProg PhaseOut := .done (refEnumPhase o q)

/-- A step of the runtimes' list whose phase slice is a later block's: never entered here. -/
def idleStep {Q : Type} (name : String) (route : Route) : GStep Q :=
  { name, route, applies := fun _ _ => false, run := fun _ _ => .done (.aside "not modelled") }

/-- **The reference pipeline** under the runtimes' step names: Route B is never entered (a
`Reference.TimedNet` has no match transition), the enumeration step runs the reference dispatch
of `Result.lean` on every query, and every SMT step is not entered (its phase slice is a later
block's: VER-015, VER-020, VER-005/007, VER-018, VER-019, NU-053, VER-025, the fixpoint query
and the certificate check). -/
def rtPipeline : List (GStep (Query K)) :=
  [idleStep "Route B (ν name-partition graph)" .nuScg,
   idleStep "linear bound" .smt,
   { name := "state-space enumeration", route := .enumeration, run := refEnumProg },
   idleStep "flattening" .smt,
   idleStep "structural pre-check" .smt,
   idleStep "P-invariant computation" .smt,
   idleStep "linear bound" .smt,
   idleStep "state-equation phase" .smt,
   idleStep "firing-bound phase" .smt,
   idleStep "colour-slot bound" .smt,
   idleStep "witness phase" .smt,
   idleStep "IC3/PDR query" .smt,
   idleStep "certificate check" .smt]

theorem rtPipeline_names : (rtPipeline (K := K)).map GStep.name = rtStepNames := rfl

theorem refEnumPhase_sound : PhaseSound refSafetyViol (refEnumPhase (K := K)) := by
  intro o q
  unfold refEnumPhase
  cases hd : firstDecided refSteps o q with
  | none => exact ⟨by simp, by simp, by simp⟩
  | some ro =>
    obtain ⟨r, out⟩ := ro
    obtain ⟨hp, hv, hk⟩ := firstDecided_sound refSteps_sound hd
    exact ⟨fun meth tr c h => hp meth tr c h, fun tr h => hv tr h, fun why tr c h => hk why tr c h⟩

/-- Only the enumeration step of the reference pipeline is ever entered. -/
theorem rtPipeline_applies {s : GStep (Query K)} (hs : s ∈ rtPipeline) {o : Options}
    {q : Query K} (ha : s.applies o q = true) :
    s.route = .enumeration ∧ s.run = refEnumProg := by
  simp only [rtPipeline, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact ⟨rfl, rfl⟩ | simp [idleStep] at ha

/-- Every step of the reference pipeline keeps the phase contract, under any replies. -/
theorem rtPipeline_sound (R : String → SolverReply → Prop) :
    ∀ s ∈ rtPipeline (K := K), ProgSound R refSafetyViol s.run := by
  intro s hs
  simp only [rtPipeline, List.mem_cons, List.not_mem_nil, or_false] at hs
  have hidle : ∀ (n : String) (r : Route),
      ProgSound R refSafetyViol (idleStep (Q := Query K) n r).run := by
    intro n r o q out hy
    rw [show (idleStep (Q := Query K) n r).run o q = .done (.aside "not modelled") from rfl,
      Yields.done_iff] at hy
    subst hy
    exact ⟨by simp, by simp, by simp⟩
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact hidle _ _ | exact refEnumPhase_sound.prog R

theorem rtPipeline_route : ∀ s ∈ rtPipeline (K := K), s.route ≠ .unavailable := by
  intro s hs
  simp only [rtPipeline, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [idleStep]

/-- **An initial violation is decided at once** by the reference pipeline: whatever the stop
and the oracle, a `Violated` it decides at a violating initial marking has the empty trace,
confirmed. -/
theorem rtPipeline_initial {O : Oracle} {stop : Stop} {o : Options} {q : Query K} {t : Trail}
    {tr : List String} {c : Option Bool} {r : Route}
    (hi : refSafetyViol o.assumeNoReaping q.net q.prop q.init)
    (h : (runPipeline O stop o q rtPipeline t).1 = some (r, .decided .violated tr c)) :
    tr = [] ∧ c = some true := by
  obtain ⟨s, hs, -, ha, hy, -⟩ := runPipeline_step h
  obtain ⟨-, hrun⟩ := rtPipeline_applies hs ha
  rw [hrun] at hy
  rw [show refEnumProg o q = .done (refEnumPhase o q) from rfl, Yields.done_iff] at hy
  unfold refEnumPhase at hy
  rcases refSteps_initial hi with h0 | h0 <;> rw [h0] at hy
  · cases hy
  · simp only [PhaseOut.decided.injEq] at hy
    obtain ⟨-, rfl, rfl⟩ := hy
    exact ⟨rfl, rfl⟩

/-- **The reference pipeline meets VER-003 under every stop and every oracle**, for every
verified-net function. -/
theorem pipeVerify_VER_003 (abs : Abs K) (O : Oracle) (stop : Stop) :
    VER_003 RefFire refSafetyViol abs (pipeVerify abs inertInvariants rtPipeline O stop) :=
  pipeVerify_VER_003_of (rtPipeline_sound _) rtPipeline_route
    (fun _ _ _ _ _ _ hi h => by
      obtain ⟨h1, h2⟩ := rtPipeline_initial hi h
      exact ⟨h1, by simp [h2], fun _ => h2⟩)
    inertInvariants_conserved

/-- Without a stop, the reference pipeline decides what `firstDecided refSteps` decides and
records no stop. -/
theorem rtPipeline_noStop {O : Oracle} {o : Options} {q : Query K} {t : Trail}
    (h : t.stopped = none) :
    ∃ t', runPipeline O noStop o q rtPipeline t = (firstDecided refSteps o q, t') ∧
      t'.stopped = none := by
  have h1 : (pollStop noStop t).2.stopped = none := by rw [pollStop_noStop h]; exact h
  simp only [rtPipeline, runPipeline, idleStep, Bool.false_eq_true, if_false, if_true,
    pollStop_noStop h]
  simp only [refEnumProg, execProg_done]
  cases hd : firstDecided refSteps o q with
  | none =>
    simp only [refEnumPhase, hd]
    exact ⟨_, rfl, by simpa [Trail.enter] using h⟩
  | some ro =>
    obtain ⟨r, out⟩ := ro
    obtain rfl := refSteps_route hd
    obtain ⟨-, -, -, -, hna⟩ := firstDecided_step hd
    cases out with
    | aside n => exact absurd rfl (hna n)
    | decided v tr c =>
      simp only [refEnumPhase, hd]
      exact ⟨_, rfl, by simpa [Trail.enter] using h⟩

/-- **With no total budget and no cancellation, the reference pipeline is `refVerify`**
([VER-013] AC8: with no total budget set, verdicts are those of the requirement without it),
whatever the oracle. -/
theorem pipeVerify_noStop (abs : Abs K) (O : Oracle) :
    pipeVerify abs inertInvariants rtPipeline O noStop = refVerify abs := by
  funext o X φ m0
  have h0 : pollStop noStop ({} : Trail) = (false, { polls := 1 }) := rfl
  simp only [pipeVerify, refVerify, h0, Bool.false_eq_true, if_false]
  by_cases hu : Unresolved X φ m0
  · simp [hu]
  simp only [hu, if_false, refDispatch]
  cases ha : abs o X φ m0 with
  | error e => rfl
  | ok q =>
    simp only
    obtain ⟨t', ht, hs⟩ := rtPipeline_noStop (O := O) (o := o) (q := q)
      (t := { polls := 1 }) rfl
    rw [ht]
    cases hd : firstDecided refSteps o q with
    | none => simp [packResult, hs]
    | some ro =>
      obtain ⟨r, out⟩ := ro
      obtain rfl := refSteps_route hd
      cases out with
      | aside n =>
        obtain ⟨-, -, -, -, hna⟩ := firstDecided_step hd
        exact absurd rfl (hna n)
      | decided v tr c => simp [packResult, finishVerdict_noStop hs]

end Reference

/-! ## Worked examples -/

/-- A demo solver phase: one query; `sat` is `Proven`, `unsat` an unconfirmed `Violated`, an
`unknown` answer or a failure `Unknown` with a reason. -/
def demoQuery (script : String) : PhaseProg PhaseOut :=
  .ask script fun
    | .answer .sat => .done (.decided (.proven "IC3/PDR") [] none)
    | .answer .unsat => .done (.decided .violated [] none)
    | .answer .unknown => .done (.decided (.unknown "the solver answered unknown") [] none)
    | .failure _ why => .done (.decided (.unknown ("solver failure: " ++ why)) [] none)

/-- A demo pipeline over the trivial query: a linear bound that steps aside, then the query. -/
def demoSteps : List (GStep Unit) :=
  [{ name := "linear bound", route := .smt, run := fun _ _ => .done (.aside "no weighting") },
   { name := "IC3/PDR query", route := .smt, run := fun _ _ => demoQuery "horn" }]

/-- A solver that answers `sat`. -/
def satOracle : Oracle := fun _ => .answer .sat

/-- A run of the demo pipeline under the stop `stop`. -/
def demoRun (stop : Stop) : Option (Route × PhaseOut) × Trail :=
  runPipeline satOracle stop {} () demoSteps {}

/-- **A stop is charged to the step that was running.** The demo run polls at the entry of the
linear bound (poll 0), at the entry of the query (poll 1), before the solver process (poll 2) and
after it (poll 3). Cancelled from poll 0: charged to `net preparation`, nothing entered. From
poll 1, on entering the query: charged to `linear bound`, the step that just ended, not to the
query about to start. From poll 2: charged to the query, and no process starts. -/
theorem demo_blame :
    (demoRun (stopFrom 0 .cancelled)).2.stopped = some (.cancelled, "net preparation") ∧
    (demoRun (stopFrom 0 .cancelled)).2.entered = [] ∧
    (demoRun (stopFrom 1 .cancelled)).2.stopped = some (.cancelled, "linear bound") ∧
    (demoRun (stopFrom 1 .cancelled)).2.entered = ["linear bound"] ∧
    (demoRun (stopFrom 2 (.budget 100))).2.stopped = some (.budget 100, "IC3/PDR query") ∧
    (demoRun (stopFrom 2 (.budget 100))).2.started = [] := by
  decide

/-- **A stop before the verdict gives the stop's `Unknown`; a verdict before the stop stands.**
Under a 100 ms budget spent from poll 2, the query is refused and its `Unknown` becomes
`total verification budget of 100 ms exhausted during IC3/PDR query`. Cancelled from poll 3,
after the solver answered `sat`, the `Proven` stands although the stop is recorded. -/
theorem demo_finish :
    finishVerdict (demoRun (stopFrom 2 (.budget 100))).2
        (.unknown "solver failure: total verification budget of 100 ms exhausted; z3 not started") =
      .unknown "total verification budget of 100 ms exhausted during IC3/PDR query" ∧
    (demoRun (stopFrom 2 (.budget 100))).1.map Prod.fst = some .smt ∧
    (demoRun (stopFrom 3 .cancelled)).2.stopped = some (.cancelled, "IC3/PDR query") ∧
    (demoRun (stopFrom 3 .cancelled)).2.started = ["horn"] ∧
    finishVerdict (demoRun (stopFrom 3 .cancelled)).2 (.proven "IC3/PDR") = .proven "IC3/PDR" ∧
    (demoRun noStop).2.stopped = none := by
  decide

theorem demo_decisions :
    demoRun (stopFrom 2 (.budget 100)) =
      (some (.smt, .decided (.unknown
        "solver failure: total verification budget of 100 ms exhausted; z3 not started") [] none),
       (demoRun (stopFrom 2 (.budget 100))).2) ∧
    (demoRun (stopFrom 3 .cancelled)).1 = some (.smt, .decided (.proven "IC3/PDR") [] none) := by
  constructor <;> rfl

/-- **A failing solver never makes the demo query `Proven`**: under replies that are all
failures, it returns `Unknown` with a reason. -/
theorem demoQuery_failing {s : String} {out : PhaseOut} (h : Yields failing (demoQuery s) out) :
    ∃ why, out = .decided (.unknown why) [] none ∧ why ≠ "" := by
  cases h with
  | ask hr hk =>
    obtain ⟨f, why, rfl⟩ := hr
    rw [Yields.done_iff] at hk
    refine ⟨_, hk, fun h => ?_⟩
    have := congrArg String.length h
    simp at this

/-- **On the AC11 net, a call cancelled before it starts** is `Unknown` with the reason
`verification cancelled during net preparation`; without a stop the same call is the reference
verdict, `Violated` with the empty trace. -/
theorem demo_ac11 :
    (pipeVerify inertAbs inertInvariants rtPipeline satOracle (stopFrom 0 .cancelled) {} ver003X
      (.deadlockFree [1] []) ver003P0).verdict =
      .unknown "verification cancelled during net preparation" ∧
    (pipeVerify inertAbs inertInvariants rtPipeline satOracle noStop {} ver003X
      (.deadlockFree [1] []) ver003P0).verdict = .violated ∧
    (pipeVerify inertAbs inertInvariants rtPipeline satOracle noStop {} ver003X
      (.deadlockFree [1] []) ver003P0).trace = [] := by
  decide

end Libpetri.Spec.Verifier
