import Libpetri.Spec.GlossaryTime
import Libpetri.Spec.GlossaryQueue
import Libpetri.Spec.Req.EXEC_002
import Libpetri.Spec.Req.IO_015

set_option linter.missingDocs true

/-!
# Glossary: the executor (Phase 2, `RefExec`)

The terms the execution, concurrency and environment requirements use ([EXEC-001] to [EXEC-042],
[CONC-001] to [CONC-011], [ENV-002] to [ENV-016]), for the reference executor of
`Libpetri/Reference/Exec.lean`. The Phase 1 step (`RefTStep`, `GlossaryTime.lean`) fires a
transition atomically; the executor splits a firing into a **start** inside a firing pass and a
**settle** in a later step (or inside the pass, for a synchronous action), with the action's
writes, flushes and return in between as outside steps.

The types and the label set are fixed here once, in full (wave 0 of the RefExec design): rules
are added in `Reference/Exec.lean` per label, so a proof that inverts one label never breaks
when another label gets its rule.

* `Cfg`: what is fixed for a run (the timed net, priorities, terminal and environment places,
  re-entrancy, the output validator, the join-relay check, the timeout outcome, the timer
  resolution). `Cfg.WF` is the build-time well-formedness a link lemma takes as a premise; it is
  never part of the executor relation.
* `XSt`: the executor state: the queue marking, two clock readings (`now`, the host's present,
  and `cyc`, the cycle reading: the enablement update's, which stamps what it newly arms, until
  the deadline step replaces it by a reading of its own, never earlier), a clock status per
  transition name,
  the firings in flight, the completion, publication and event queues, the lifecycle mode, the
  loop phase and the current pass.
* `XLbl`: one label per executor step of [EXEC-001], plus the outside steps (time passing, an
  action writing, flushing, returning or timing out, a caller injecting, draining or closing).
* `XRel N T := Cfg N T → XSt N T → XLbl N T → XSt N T → Prop`: an executor. A requirement is a
  predicate over an abstract `XRel`, so it is checked against the reference (`RefExec`) and
  against mutants.
* `XPol`: the one-field mutation record. The reference rules read their judgement points from
  it (`refXPol`), so a plausible wrong reading is a one-field change of `refXPol`.

The coverage conditions (`ExecCovers`) and the agreement with the shared output validator
(`ValidatedBy`) are used only in the consistency theorem (`ConsistencyExec.lean`), never in a
requirement block.

**Convention: blocks state safety, offers are coverage** (user decision on review finding
W5-SR-5). That a step exists ("the executor has a step ...", an `∃ s'` over the executor) is
never a line of a requirement block; every block over `XRel` states safety only, so a
sub-relation of a satisfying executor satisfies it too and a refinement argument carries every
block over. Each offer a block's markdown demands is a clause of the consistency theorem's
`ExecCoversW5`, defined next to the block and named after it (`Env002Covers`, `Env011Covers`,
`Exec042Covers`, ...), with a reference proof. Where a markdown sentence itself demands an answer
or an acceptance, the block quotes the sentence whole, its lines state the safety half, and its
assumes says that the existence half is that clause ("its offers are in ExecCoversW5.<clause>").
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## Types -/

/-- The clock status of a transition name ([TIME-010] to [TIME-013]). -/
inductive Status where
  /-- No clock: not enabled at the last update, or in flight and not re-entrant, or a loser of
  the pass (its clock is lost). -/
  | off
  /-- Armed at `stamp`; `restart` is the [TIME-012] flag a start sets on another armed name that
  its live intermediate marking disables (ruling D7); the next update re-stamps it. -/
  | armed (stamp : Nat) (restart : Bool)
  /-- Reaped by the deadline step ([TIME-013]); only a write of one of its arc places turns it
  off again (ruling D6). -/
  | reaped
  deriving DecidableEq, Repr

/-- How a firing in flight ended, as queued for the orchestrator. -/
inductive Outcome (N T : Type) where
  /-- The action returned normally with emission `e` (places and tokens, in emission order). -/
  | ok (e : List (N × T))
  /-- The action threw or returned an error ([EXEC-030]). -/
  | err
  /-- The budget of the output spec's `Timeout` node expired first ([EXEC-022], [IO-013]); `e`
  is the timeout outcome the executor deposits. -/
  | timedOut (e : List (N × T))

/-- A firing in flight. -/
structure Firing (N T : Type) where
  /-- Its identity, drawn from `XSt.nextId`. -/
  id    : Nat
  /-- The transition that started. -/
  t     : Trans N
  /-- What the start handed the action (consumed and read tokens). -/
  deliv : QDelivered N T
  /-- The host reading at the start. -/
  start : Nat
  /-- A synchronous action: the pass waits for its return, and it never expires (R-EXEC-1 (b)). -/
  sync  : Bool
  /-- What the action wrote since its last flush ([CONC-003]), in write order. -/
  buf   : List (N × T)
  /-- The places of the batches it has flushed ([IO-015], mid-action publication, item 1). -/
  pub   : List N
  /-- A flushed batch failed the join-relay check of [NU-054]: the batch was dropped, every later
  batch is dropped too, and the firing ends with an error whatever its action returns or its
  budget does (Rust: the relay guard of the flush callback and the slot read after the task). -/
  relayBad : Bool
  /-- Set once, by its return or by the expiry of its budget. -/
  out   : Option (Outcome N T)

/-- The lifecycle mode of an executor with environment places ([ENV-011], [ENV-013]). -/
inductive Mode where
  /-- Accepting injections. -/
  | open
  /-- Draining: refusing new injections, finishing what is queued and in flight. -/
  | draining
  /-- Closed: refusing injections, discarding queued ones. -/
  | closed
  /-- Stopped by an immediate termination ([ENV-015], Java): refusing injections, the queued
  ones discarded, the loop ending at the end of its current cycle without waiting for the
  firings in flight. -/
  | stopped
  deriving DecidableEq, Repr

/-- The mode refuses injections and ends the run once nothing is in flight: closed, or stopped
([ENV-013], [ENV-015]). -/
def Mode.closing : Mode → Bool
  | .closed | .stopped => true
  | _ => false

/-- Why a run finished ([EXEC-041]). -/
inductive Cause where
  /-- Nothing armed, in flight or queued ([EXEC-040]). -/
  | quiescent
  /-- A terminal place is marked ([EXEC-042]). -/
  | terminal
  /-- Closed, with nothing in flight ([ENV-013]). -/
  | closed
  /-- Stopped by an immediate termination at the end of its cycle, firings in flight abandoned
  ([ENV-015]). -/
  | stopped
  deriving DecidableEq, Repr

/-- Where the orchestrator loop is ([EXEC-001]). Each phase is entered by the step that ends the
one before, so a requirement can speak of "at entry to" a phase. -/
inductive Phase where
  /-- Step 1: settle completed firings. -/
  | completions
  /-- Step 1b: deposit mid-action publications (Rust, Python). -/
  | publications
  /-- Step 2: inject queued environment events. -/
  | events
  /-- Step 3: the enablement update. -/
  | update
  /-- Step 4: reap expired transitions. -/
  | deadline
  /-- The termination test ([EXEC-040], R-EXEC-10). -/
  | test
  /-- Step 5: the firing pass. -/
  | pass
  /-- Step 6: wait for work. -/
  | await
  /-- The run finished with cause `c`. -/
  | done (c : Cause)
  deriving DecidableEq, Repr

/-- The answer to an injection request ([ENV-002], [ENV-006]). -/
inductive Reply where
  /-- Queued for injection. -/
  | accepted
  /-- Refused: the executor is draining, closed, stopped or done. -/
  | refused
  /-- Not an environment place. -/
  | error
  deriving DecidableEq, Repr

/-- What is fixed for one run. -/
structure Cfg (N T : Type) where
  /-- The timed net. -/
  X          : TimedNet N
  /-- The priority of each transition ([EXEC-002]). -/
  prio       : Trans N → Int
  /-- The terminal places ([EXEC-042]). -/
  terminals  : List N
  /-- The environment places ([ENV-001]). -/
  envs       : List N
  /-- R-EXEC-4 (b), ruling D8 (b): a transition may start again while a firing of it is in
  flight (Rust, Python `true`; Java, TypeScript `false`). -/
  reentrant  : Bool
  /-- Output validation ([IO-015]): the verdict on the produced set of a completion, read as
  the places of its emission followed by the places it published (`validIn`). The validation
  skip of [CONC-026] is `fun _ _ => true`; `cfgValidate V` builds it from an output validator. -/
  validate   : Trans N → List N → Bool
  /-- The join-relay check of [NU-054], part of output validation: the verdict on an emission of
  a firing that delivered `δ`. `fun _ _ _ => true` for a transition without relay targets and
  under the [CONC-026] skip. -/
  relay      : Trans N → QDelivered N T → List (N × T) → Bool
  /-- The timeout outcomes of a firing that delivered `δ` ([IO-013], [IO-014]). -/
  timeoutOut : Trans N → QDelivered N T → List (N × T) → Bool
  /-- The timer resolution of the wait ([CONC-010]): it bounds the park timer only. -/
  res        : Nat

/-- The build-time well-formedness of a configuration (ruling R13 of the design): every
transition builds, none has an input arc and a read arc on one place (ruling D15), and names are
pairwise distinct (ruling D10). A premise of link lemmas and of the blocks that need it; never
part of an executor relation. -/
structure Cfg.WF {N T : Type} [DecidableEq N] (C : Cfg N T) : Prop where
  /-- Every transition builds ([CORE-022], glossary: Builds). -/
  build : ∀ t ∈ C.X.net.transitions, Builds t
  /-- No input arc and read arc on one place ([EXEC-012], ruling D15). -/
  noIR  : ∀ t ∈ C.X.net.transitions, NoInputRead t
  /-- Transition names are pairwise distinct (ruling D10). -/
  names : NamesDistinct C.X

/-- The executor state. -/
structure XSt (N T : Type) where
  /-- The marking, as FIFO queues ([CORE-013]). -/
  M       : QMarking N T
  /-- The host's present reading of the firing clock. -/
  now     : Nat
  /-- The cycle reading: the reading the enablement update takes (the stamp of what it newly
  arms), replaced by the deadline step's own reading, never an earlier one (`atDeadline`, ruling
  D61 (c)); steps 4 and 5 and the park decision judge at the deadline step's reading. -/
  cyc     : Nat
  /-- The clock status by transition name. -/
  st      : String → Status
  /-- The firings in flight. -/
  fl      : List (Firing N T)
  /-- The supply of firing identities and event tickets. -/
  nextId  : Nat
  /-- The completion queue: identities of firings whose outcome is set, in arrival order. -/
  cq      : List Nat
  /-- The publication queue: flushed batches with their firing's identity, in flush order. -/
  pq      : List (Nat × List (N × T))
  /-- The event queue: accepted injections with their ticket ([ENV-003], [ENV-004]). -/
  eq      : List (Nat × N × T)
  /-- The lifecycle mode. -/
  mode    : Mode
  /-- The loop phase. -/
  phase   : Phase
  /-- The rest of the pass's ready order ([EXEC-002], [TIME-014]). -/
  order   : List (Trans N)
  /-- The tokens deposited inside the current pass, per place: the tail the pass does not see
  ([EXEC-003], R-EXEC-11 (a)). -/
  delta   : N → Nat
  /-- Some transition started in the current pass. -/
  started : Bool
  /-- The loop is parked in step 6 ([CONC-010]). -/
  parked  : Bool

/-- The full label set. The first group are executor steps, the second outside steps. -/
inductive XLbl (N T : Type) where
  /-- Step 1: settle firing `i`'s returned emission and deposit it: the admitted completion
  passed output validation (glossary: Admitted completion). The step that emits
  TransitionCompleted. -/
  | commit (i : Nat)
  /-- Step 1: settle firing `i` without a deposit: the action failed, output validation rejected
  its outcome, or the join-relay check of [NU-054] rejected it, also for a timeout outcome
  ([EXEC-021], [EXEC-030], ruling D24 (a)). -/
  | fail (i : Nat)
  /-- Step 1: settle firing `i`'s timeout outcome and deposit it ([EXEC-022], [IO-013]). -/
  | tdeposit (i : Nat)
  /-- End of step 1. -/
  | endCompletions
  /-- Step 1b: deposit the oldest queued publication, of firing `i`. -/
  | publish (i : Nat)
  /-- End of step 1b. -/
  | endPublications
  /-- Step 2: inject the queued event with ticket `k`. -/
  | inject (k : Nat)
  /-- Step 2: discard the queued event with ticket `k` (closed). -/
  | discard (k : Nat)
  /-- End of step 2. -/
  | endEvents
  /-- A snapshot request answered with `ans` ([ENV-014]). -/
  | snapshot (ans : Option Bool)
  /-- Step 3: the enablement update. -/
  | update
  /-- Step 4: reap exactly the names `ns`. -/
  | deadline (ns : List String)
  /-- Start the firing pass. -/
  | begin
  /-- Step 5: start the head of the order, named `n`, synchronous or not. -/
  | start (n : String) (sync : Bool)
  /-- Step 5: the head of the order, named `n`, can no longer start; its clock is lost. -/
  | lose (n : String)
  /-- End of the firing pass. -/
  | endPass
  /-- The run finishes with cause `c`. -/
  | finish (c : Cause)
  /-- Step 6: park, with a timer when a boundary is ahead. -/
  | park (timeout : Option Nat)
  /-- Step 6: wake up. -/
  | wake
  /-- Outside: the host clock advances by `δ`. -/
  | delay (δ : Nat)
  /-- Outside: the action of firing `i` writes token `x` to place `p`. -/
  | write (i : Nat) (p : N) (x : T)
  /-- Outside: the action of firing `i` flushes what it wrote ([IO-015], mid-action
  publication). -/
  | flush (i : Nat)
  /-- Outside: the action of firing `i` returns, normally (`ok`) or with an error. -/
  | ret (i : Nat) (ok : Bool)
  /-- Outside: the budget of firing `i` expires with timeout outcome `e`. -/
  | expire (i : Nat) (e : List (N × T))
  /-- Outside: a caller asks to inject `x` into `p`; the executor answers `r`. -/
  | request (p : N) (x : T) (r : Reply)
  /-- Outside: a caller drains the executor. -/
  | drain
  /-- Outside: a caller closes the executor. -/
  | close
  /-- Outside: a caller terminates the executor immediately ([ENV-015], Java). -/
  | terminateNow

/-- The outside steps ([CONC-001]): the steps the orchestrator does not take. -/
def XLbl.outside {N T : Type} : XLbl N T → Bool
  | .delay _ | .write _ _ _ | .flush _ | .ret _ _ | .expire _ _ | .request _ _ _ | .drain
  | .close | .terminateNow => true
  | _ => false

/-- An executor: `E C s l s'` says that, under configuration `C`, the step labelled `l` leads
from `s` to `s'`. -/
abbrev XRel (N T : Type) := Cfg N T → XSt N T → XLbl N T → XSt N T → Prop

/-! ## Derived terms -/

variable {N T : Type}

/-- The transition the net holds under name `n` (ruling D10). -/
def findT (C : Cfg N T) (n : String) : Option (Trans N) :=
  C.X.net.transitions.find? (·.core.name == n)

/-- The pass-visible marking: every queue without the tokens deposited inside the current pass
([EXEC-003], R-EXEC-11 (a)). -/
def vis (s : XSt N T) : QMarking N T := fun p => (s.M p).take ((s.M p).length - s.delta p)

/-- The same-pass tail of every queue: the tokens deposited inside the current pass. -/
def hid (s : XSt N T) : QMarking N T := fun p => (s.M p).drop ((s.M p).length - s.delta p)

/-- The marking right after a start of `t` in the pass: the pass-visible marking with `t`'s
consumption and drains applied, followed by the same-pass tail (drains take only the visible
prefix, [EXEC-013]). -/
def liveAfter [DecidableEq N] (s : XSt N T) (t : Trans N) : QMarking N T :=
  fun p => qConsume (vis s) t p ++ hid s p

/-- No terminal place is marked ([EXEC-042]). -/
def liveB (C : Cfg N T) (s : XSt N T) : Bool := C.terminals.all fun p => (s.M p).isEmpty

/-- The stamp a status holds, if armed. -/
def stampOf : Status → Option Nat
  | .armed k _ => some k
  | _ => none

/-- The Phase 1 state at reading `r` (design R21): `viewAt s s.cyc` is what steps 4 and 5 and
the park decision judge, `viewAt s s.now` the host's present. -/
def viewAt (s : XSt N T) (r : Nat) : TSt N :=
  ⟨qCount s.M, r, fun n => stampOf (s.st n)⟩

/-- The state the deadline step judges (ruling D61 (c)): the cycle reading moved to the host's
present reading, or kept when the present is earlier (a later reading is never earlier). The
update's reading, which stamps what it newly arms, is the cycle reading before it; from the
deadline step on, the firing pass and the park decision judge at this one. -/
def atDeadline (s : XSt N T) : XSt N T := { s with cyc := max s.cyc s.now }

/-- A firing of the transition named `n` is in flight. -/
def inFlightN (s : XSt N T) (n : String) : Bool := s.fl.any (·.t.core.name == n)

/-- No synchronous firing is waiting for its return: the pass may go on. -/
def passFree (s : XSt N T) : Bool := s.fl.all fun g => !(g.sync && g.out.isNone)

/-- Ruling D6: a write of the places `ps` turns a reaped name with an arc place in `ps` off. -/
def unreap [DecidableEq N] (C : Cfg N T) (ps : List N) (st : String → Status) :
    String → Status := fun n =>
  match st n, findT C n with
  | .reaped, some u => if (arcPlaces u).any (fun p => decide (p ∈ ps)) then .off else .reaped
  | x, _ => x

/-- `t`'s output spec has a `Timeout` node ([EXEC-022]). -/
def hasTimeoutB (t : Trans N) : Bool :=
  match t.out with
  | some o => o.findTimeout.isSome
  | none => false

/-- The number of tokens of emission `e` for place `p`. -/
def countIn [DecidableEq N] (e : List (N × T)) (p : N) : Nat := (e.filter (·.1 == p)).length

/-- Is the loop running (not finished)? -/
def isExecPhase : Phase → Bool
  | .done _ => false
  | _ => true

/-- May a queued outcome of `f` be settled in the current phase: in step 1, on the wake of the
wait (R-EXEC-9), or inside the pass for a synchronous firing (NR-2: "may", never "must"). After an
immediate termination no later step 1 and no wait settles anything ([ENV-015]: results are
discarded); the pass under way still settles its synchronous firing, as it waits for it. -/
def settleOk (s : XSt N T) (f : Firing N T) : Bool :=
  match s.phase with
  | .completions | .await => s.mode != .stopped
  | .pass => f.sync
  | _ => false

/-- The guard every settle step shares: the loop is running, no terminal place is marked, `i`'s
outcome is queued, and the phase allows settling `f`. -/
def canSettle (C : Cfg N T) (s : XSt N T) (i : Nat) (f : Firing N T) : Bool :=
  isExecPhase s.phase && liveB C s && s.cq.contains i && settleOk s f

/-- Remove settled firing `i` and its queue entry; a settle in the wait wakes the loop into
step 1. -/
def settle (s : XSt N T) (i : Nat) : XSt N T :=
  { s with fl := s.fl.filter (·.id != i), cq := s.cq.erase i,
           phase := if s.phase = .await then .completions else s.phase,
           parked := false }

/-- **The places output validation reads** for firing `f` with returned emission `e`
([IO-015], mid-action publication, item 1; ruling D27 (a)): the places of `e`, then the places
`f` has already published. Rust: `output_conforms(.., flushed_places)`. -/
def validIn (f : Firing N T) (e : List (N × T)) : List N := e.map Prod.fst ++ f.pub

/-- The configuration validator built from an output validator `V` ([IO-015]): a transition
with an output spec is validated by `V`; one without has nothing to validate. -/
def cfgValidate (V : OutputValidator N) : Trans N → List N → Bool := fun t d =>
  match t.out with
  | some o => V o d
  | none => true

/-- The validation skip of [CONC-026]: no output validation and no join-relay check. -/
def Cfg.SkipsValidation (C : Cfg N T) : Prop :=
  C.validate = (fun _ _ => true) ∧ C.relay = (fun _ _ _ => true)

/-- The configured verdict reads a produced **set** of places ([IO-015]: every validator
satisfying IO-015 does, `IO_015_setOnly`): two lists with the same members get the same verdict.
A requirement that fixes which places validation reads assumes it, so that the order and
repetition of the list `validIn` builds are not part of the requirement (Rust validates a
`HashSet`). -/
def Cfg.SetValidated (C : Cfg N T) : Prop :=
  ∀ t (d d' : List N), (∀ q, q ∈ d ↔ q ∈ d') → C.validate t d = C.validate t d'

/-- The configuration validator built from a validator satisfying [IO-015] reads sets. -/
theorem cfgValidate_setValidated [DecidableEq N] {V : OutputValidator N} (hV : IO_015 V)
    (C : Cfg N T) (hC : C.validate = cfgValidate V) : C.SetValidated := by
  intro t d d' hd
  rw [hC]
  unfold cfgValidate
  split
  · exact IO_015_setOnly hV _ d d' hd
  · rfl

/-! ## The mutation record -/

/-- The judgement points of the reference rules. Each plausible wrong reading of the design is a
one-field change of `refXPol`. -/
structure XPol (N T : Type) where
  /-- The places output validation reads (reference: `validIn`). -/
  validIn       : Firing N T → List (N × T) → List N
  /-- The marking a start re-checks enablement on (reference: `vis`). -/
  recheckOn     : XSt N T → QMarking N T
  /-- The marking a start sets the [TIME-012] restart flag from (reference: `liveAfter`). -/
  restartOn     : XSt N T → Trans N → QMarking N T
  /-- The update keeps a reaped name reaped (reference: `true`; design R9). -/
  updReaped     : Bool
  /-- The update keeps the old stamp of a restarted name (reference: `false`). -/
  keepOnRestart : Bool
  /-- The reading a fresh stamp takes (reference: `now` at the update). -/
  stampAt       : XSt N T → Nat
  /-- `expiredCmp bound elapsed`: a name is expired (reference: `bound < elapsed`). -/
  expiredCmp    : Nat → Nat → Bool

/-- The reference judgement points. -/
def refXPol [DecidableEq N] : XPol N T where
  validIn       := validIn
  recheckOn     := vis
  restartOn     := liveAfter
  updReaped     := true
  keepOnRestart := false
  stampAt       := (·.now)
  expiredCmp    := fun b el => decide (b < el)

/-- After a start of `t` in state `s`: `t` is off; another armed name that the start's marking
(`P.restartOn`) disables gets the restart flag ([TIME-012], ruling D7). -/
def afterStart [DecidableEq N] (P : XPol N T) (C : Cfg N T) (s : XSt N T) (t : Trans N) :
    String → Status := fun n =>
  if n = t.core.name then .off else
  match s.st n, findT C n with
  | .armed k r, some u =>
      if enabledNA (qCount (P.restartOn s t)) u.core then .armed k r else .armed k true
  | x, _ => x

/-- Step 3: re-evaluate every name at the update (no dirty set; design R15). An enabled armed
name keeps its stamp unless restarted; an enabled off name is armed unless it is in flight and
the executor is not re-entrant; a reaped name stays reaped. -/
def updSt (P : XPol N T) (C : Cfg N T) (s : XSt N T) : String → Status := fun n =>
  match findT C n with
  | none => .off
  | some u =>
    let fresh : Status :=
      if enabledNA (qCount s.M) u.core && (C.reentrant || !inFlightN s n)
      then .armed (P.stampAt s) false else .off
    match s.st n with
    | .armed k rs =>
        if enabledNA (qCount s.M) u.core then
          (if rs && !P.keepOnRestart then .armed (P.stampAt s) false else .armed k false)
        else .off
    | .off => fresh
    | .reaped => if P.updReaped then .reaped else fresh

/-- `u` is expired at the cycle reading ([TIME-013]): reapable, armed, and its elapsed time is
past its latest bound plus the tolerance, as `P.expiredCmp` compares them. -/
def expiredAt (P : XPol N T) (C : Cfg N T) (s : XSt N T) (u : Trans N) : Bool :=
  (C.X.timing u).reapable && (viewAt s s.cyc).armed u &&
    P.expiredCmp ((C.X.timing u).latest + C.X.tol) ((viewAt s s.cyc).elapsed u)

/-- The names step 4 reaps: every expired transition at the cycle reading. -/
def expiredNames (P : XPol N T) (C : Cfg N T) (s : XSt N T) : List String :=
  (C.X.net.transitions.filter (expiredAt P C s)).map (·.core.name)

/-- The reference comparison is `tExpired`'s. -/
theorem expiredAt_ref [DecidableEq N] (C : Cfg N T) (s : XSt N T) (u : Trans N) :
    expiredAt refXPol C s u = tExpired C.X (viewAt s s.cyc) u := rfl

/-- The pass's ready order: the reference order of [EXEC-002] over the cycle reading. -/
def readyOrder [DecidableEq N] (C : Cfg N T) (s : XSt N T) : List (Trans N) :=
  let ts := C.X.net.transitions
  (refReadyOrder (ReadyIn.ofTSt C.X C.prio (viewAt s s.cyc) ts)).filterMap (ts[·]?)

/-- `u` is armed: enabled and holding a stamp. -/
def armedB (s : XSt N T) (u : Trans N) : Bool :=
  enabledNA (qCount s.M) u.core && (stampOf (s.st u.core.name)).isSome

/-- Rest at the termination test (ruling D13, R-EXEC-10): nothing armed, in flight or queued. -/
def restB (C : Cfg N T) (s : XSt N T) : Bool :=
  C.X.net.transitions.all (fun u => !armedB s u) && s.fl.isEmpty && s.cq.isEmpty &&
    s.pq.isEmpty && s.eq.isEmpty

/-! ## Glossary terms -/

/-- **Glossary: Admitted completion.** "A completion is an action that returned normally
[EXEC-020]. The executor admits it when it processes it, in step 1 of a cycle or, for a
synchronous action, inside the firing pass [EXEC-001]. It never admits the completion of a
firing that ended with its timeout outcome [EXEC-022], that a stop on a terminal place abandoned
[EXEC-042] or that an immediate termination abandoned [ENV-015]. Only an admitted completion
deposits, and only when output validation, if enabled [CONC-026], does not reject its produced
set [EXEC-020], [EXEC-021]."

Firing `i` (record `f`) returned normally with emission `e`, and state `s` may settle it: the
loop runs, no terminal place is marked, its outcome is queued and the phase allows it. The
settle step is `commit i` when validation accepts and `fail i` when it rejects. -/
def AdmittedCompletion (C : Cfg N T) (s : XSt N T) (i : Nat) (f : Firing N T)
    (e : List (N × T)) : Prop :=
  s.fl.find? (·.id == i) = some f ∧ f.out = some (.ok e) ∧ canSettle C s i f = true

/-- **Offered emission** (no glossary entry; the per-run hypothesis of link L2): the places of
`e` are a deposit the output spec of `t` offers for what `t` consumes at the pass-visible
marking of `s`. Validation reads sets of places ([IO-015]), so a validated emission can deposit
more tokens than any deposit offers; such runs are real and are IO-016's subject, not RefQFire's.
-/
def OfferedEmission [DecidableEq N] (s : XSt N T) (t : Trans N) (e : List (N × T)) : Prop :=
  ∃ ch, deposit (nconsumed (qCount (vis s)) t.core) t.out ch = some (e.map Prod.fst)

/-- **Agreement with the shared output validator** (consistency theorem only): on every
configuration whose validator is `V`'s, `E` settles every admitted completion that the
join-relay check accepts as `V` decides: a `commit` when `V` accepts its produced set (`validIn`),
a `fail` when `V` rejects it. -/
def ValidatedBy (E : XRel N T) (V : OutputValidator N) : Prop :=
  ∀ C, C.validate = cfgValidate V → ∀ s i f e, AdmittedCompletion C s i f e →
    C.relay f.t f.deliv e = true →
    (cfgValidate V f.t (validIn f e) = true → ∃ s', E C s (.commit i) s') ∧
    (cfgValidate V f.t (validIn f e) = false → ∃ s', E C s (.fail i) s')

/-- **Executor coverage** (consistency theorem only; wave 0 part): the host clock can always
advance, and every firing in flight whose outcome is not set can return, normally or with an
error. The empty relation fails it (`exec_coverage_excludes_empty`). The existence halves of
wave W5 are the separate conjunct `ExecCoversW5` (`ConsistencyExec.lean`; the convention above):
the answers to injection requests (`Env002Covers`, `Env006Covers`, `Env010Covers`), the injection
of a queued event (`Env003Covers`, `Env010Covers`), the way out of the wait (`Env005Covers`,
`Conc010Covers`, `Env010Covers`), the outcome of a run-budget expiry (`Env016Covers`, over the
expiry handling), `expire` and the
timeout deposit (`Exec022Covers`), `begin` from a test with a firing in flight and `start` or
`lose` for the head of every non-empty order (`conc002Covers`), and `finish` at each rest test
(`Exec040Covers`, `Env011Covers`, `Env013Covers`), at a marked terminal place (`Exec042Covers`)
and after a stop (`Env015Covers`). The scenario run of the design is no coverage clause: each
block's nonvacuous evidence runs the reference on its own scenario. -/
def ExecCovers (E : XRel N T) : Prop :=
  (∀ C s δ, ∃ s', E C s (.delay δ) s') ∧
  (∀ C s i f ok, s.fl.find? (·.id == i) = some f → f.out = none → ∃ s', E C s (.ret i ok) s')


/-! ## Derived terms of the wave 1 rules (injection, snapshot, lifecycle, wait) -/

/-- The answer to an injection request into `p` in state `s` ([ENV-002], [ENV-006], rulings D44
(a) and D89 (a)): `error` when `p` is not an environment place (the Java and TypeScript reading;
Rust and Python deposit into any place, an assumption of their own); `refused` when the executor
is draining, closed, stopped or finished; `accepted` otherwise. -/
def replyFor [DecidableEq N] (C : Cfg N T) (s : XSt N T) (p : N) : Reply :=
  if p ∉ C.envs then .error
  else if s.mode = .open && isExecPhase s.phase then .accepted else .refused

/-- The answer to a snapshot request ([ENV-014]): none once the executor drains, closes or
stops; otherwise whether work is in flight, a firing in flight or an injection queued (ruling D43
(a)). The marking the answer carries is the state's own `M`. -/
def snapAnswer (s : XSt N T) : Option Bool :=
  if s.mode = .open then some (!s.fl.isEmpty || !s.eq.isEmpty) else none

/-- The smaller of two optional waits; `none` is no wait. -/
def optMin : Option Nat → Option Nat → Option Nat
  | some a, some b => some (min a b)
  | some a, none => some a
  | none, b => b

/-- The wait, from the cycle reading, until armed transition `u`'s next timing boundary
([CONC-010], ruling D13 (a)): its earliest bound while it is not reached, and for a reapable
transition the reading at which it becomes expired. `none` when `u` is not armed or no boundary
is ahead. -/
def boundaryOf (C : Cfg N T) (s : XSt N T) (u : Trans N) : Option Nat :=
  let v := viewAt s s.cyc
  if v.armed u then
    let el := v.elapsed u
    let tm := C.X.timing u
    optMin (if el < tm.earliest then some (tm.earliest - el) else none)
      (if tm.reapable && decide (el ≤ tm.latest + C.X.tol)
       then some (tm.latest + C.X.tol + 1 - el) else none)
  else none

/-- The wait until the nearest timing boundary of any transition of the net, from the cycle
reading (design R8: the park decision judges at the reading of the cycle's update). -/
def nextBoundary (C : Cfg N T) (s : XSt N T) : Option Nat :=
  C.X.net.transitions.foldr (fun u acc => optMin (boundaryOf C s u) acc) none

/-- A park timer `tmr` the wait may set ([CONC-010] AC3): with a boundary ahead, a timer no later
than it plus the timer resolution; with none ahead, any timer or none (Rust re-checks after
60 s). -/
def timerOk (C : Cfg N T) (s : XSt N T) (tmr : Option Nat) : Bool :=
  match nextBoundary C s, tmr with
  | some b, some x => decide (x ≤ b + C.res)
  | some _, none => false
  | none, _ => true

/-- No transition is Ready or Expired at the cycle reading: nothing the loop could act on
without new work ([CONC-010] line 1, design R8). -/
def nothingDue [DecidableEq N] (C : Cfg N T) (s : XSt N T) : Bool :=
  C.X.net.transitions.all fun u =>
    !(decide (Ready C.X (viewAt s s.cyc) u) || tExpired C.X (viewAt s s.cyc) u)

/-! ## Glossary terms of the executor state -/

/-- **Glossary: Armed**, in the executor state. "A transition is armed when it is enabled and
holds a clock: a stamp, the firing-clock reading taken by the enablement update that most
recently newly armed it [TIME-010]."

`u` is enabled at the marking and its name holds an armed status. -/
def ArmedE (s : XSt N T) (u : Trans N) : Prop := armedB s u = true

/-- **Glossary: Reaped**, in the executor state. "A reaped transition keeps its tokens and stays
enabled but not armed, and does not fire, until a firing or an injected token writes one of its
arc places; it is then newly armed if it is enabled [TIME-013]."

`u`'s name holds the reaped status (the write that ends it is `unreap`, ruling D6). -/
def ReapedE (s : XSt N T) (u : Trans N) : Prop := s.st u.core.name = .reaped

/-- No terminal place is marked ([EXEC-042]): the loop may go on. -/
def Live (C : Cfg N T) (s : XSt N T) : Prop := liveB C s = true

/-- Rest at the termination test (ruling D13 (a), R-EXEC-10): nothing armed, nothing in flight,
nothing queued. -/
def Rest (C : Cfg N T) (s : XSt N T) : Prop := restB C s = true

/-- A firing of the transition named `n` is in flight. -/
def InFlight (s : XSt N T) (n : String) : Prop := inFlightN s n = true

instance (s : XSt N T) (u : Trans N) : Decidable (ArmedE s u) :=
  inferInstanceAs (Decidable (_ = true))
instance (s : XSt N T) (u : Trans N) : Decidable (ReapedE s u) :=
  inferInstanceAs (Decidable (_ = _))
instance (C : Cfg N T) (s : XSt N T) : Decidable (Live C s) :=
  inferInstanceAs (Decidable (_ = true))
instance (C : Cfg N T) (s : XSt N T) : Decidable (Rest C s) :=
  inferInstanceAs (Decidable (_ = true))
instance (s : XSt N T) (n : String) : Decidable (InFlight s n) :=
  inferInstanceAs (Decidable (_ = true))

/-! ## Runs -/

/-- One step of a run: source state, label, target state. -/
abbrev XStep (N T : Type) := XSt N T × XLbl N T × XSt N T

/-- A run of executor `E` under `C` from `s0`: consecutive steps, each one of `E`. The trace
forms of Ears (`after T, until G, never B` and the others) read such a list. -/
def XRun (E : XRel N T) (C : Cfg N T) : XSt N T → List (XStep N T) → Prop
  | _, [] => True
  | s, st :: rest => st.1 = s ∧ E C st.1 st.2.1 st.2.2 ∧ XRun E C st.2.2 rest

/-- The state a run from `s0` ends in. -/
def XRun.last (s0 : XSt N T) (tr : List (XStep N T)) : XSt N T :=
  (tr.getLast?.map (·.2.2)).getD s0

/-- **Ideal run** (the kind A assumption of the liveness lines, design R-EXEC liveness): a run of
`E` from `s0` that reaches its finish. On a finite run "eventually" reads "before the finish":
every action in flight returned or expired, every queued item was processed, unless the finish
abandoned it (a terminal place, an immediate termination). A net that never finishes has no
ideal run, so a liveness line over ideal runs says nothing about it; a block pairs it with a
decided ideal run of its example (nonvacuous evidence). -/
def IdealRun (E : XRel N T) (C : Cfg N T) (s0 : XSt N T) (tr : List (XStep N T)) : Prop :=
  XRun E C s0 tr ∧ isExecPhase (XRun.last s0 tr).phase = false

/-! ## Shared step vocabulary

Predicates on labels, steps and states that several executor blocks read. They live here once
so that the blocks judge one write, one deposit label, one update and one accepted ticket. -/

section StepVocabulary

variable {N T : Type}

/-- The label's step may change the token queues: a start (it consumes) and the four deposits (a
returned emission, a timeout outcome, a flushed batch, an injected event). [CONC-001]'s marking
frame and [CONC-005]'s write companion read it. -/
def startOrDeposit : XLbl N T → Bool
  | .start _ _ | .commit _ | .tdeposit _ | .publish _ | .inject _ => true
  | _ => false

/-- **Glossary: Write**, at the grain of the executor. "A firing writes a place when it consumes
from it, deposits into it or drains it through a reset arc. Draining a reset place that is already
empty counts as a write. An injected token writes the place it lands in [ENV-003]."

The places a step labelled `l` from state `s` writes: a start consumes from the input places and
drains the reset places of the head of the pass's order; a commit or a timeout deposit deposits the
emission of its firing; a publication deposits the oldest queued batch; an injection deposits its
token into the place of the oldest queued event. No other step writes. -/
def cycWrites (s : XSt N T) : XLbl N T → List N
  | .start _ _ =>
    match s.order with
    | t :: _ => inPlaces t ++ t.core.resets
    | [] => []
  | .commit i =>
    match s.fl.find? (·.id == i) with
    | some f =>
      match f.out with
      | some (.ok e) => e.map Prod.fst
      | _ => []
    | none => []
  | .tdeposit i =>
    match s.fl.find? (·.id == i) with
    | some f =>
      match f.out with
      | some (.timedOut e) => e.map Prod.fst
      | _ => []
    | none => []
  | .publish _ =>
    match s.pq with
    | (_, b) :: _ => b.map Prod.fst
    | [] => []
  | .inject _ =>
    match s.eq with
    | (_, p, _) :: _ => [p]
    | [] => []
  | _ => []

/-- The step is the enablement update (step 3 of [EXEC-001]). -/
def isUpdate (e : XStep N T) : Bool :=
  match e.2.1 with
  | .update => true
  | _ => false

/-- The step starts a transition (step 5 of [EXEC-001]). -/
def isStart (e : XStep N T) : Bool :=
  match e.2.1 with
  | .start _ _ => true
  | _ => false

/-- The step accepts an injection request with ticket `k`: a request answered `accepted` from a
state whose next identity is `k` (the ticket an accepted request takes, `XSt.nextId`). -/
def acceptsTicket (k : Nat) (e : XStep N T) : Bool :=
  match e.2.1 with
  | .request _ _ r => r == .accepted && e.1.nextId == k
  | _ => false

/-- Every firing in flight has an identity the supply has already handed out (`XSt.nextId`): true
when nothing is in flight, and kept by every reference step, so a later start never reuses an
identity ([EXEC-022], [EXEC-031]). -/
def IdsIssued (s : XSt N T) : Prop := ∀ f ∈ s.fl, f.id < s.nextId

end StepVocabulary

end Libpetri.Spec
