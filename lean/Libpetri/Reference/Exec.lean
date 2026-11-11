import Libpetri.Spec.GlossaryExec

set_option linter.missingDocs true

/-!
# The reference executor (`RefExec`, Phase 2)

Written from the spec ([EXEC-001] and the requirements it cites), checked rule by rule against
the Rust executor (`rust/libpetri-runtime/src/executor_core/executor.rs`), which is the runtime
the design follows where the runtimes differ. The reference is a **partial step function**
`xstepW P C s l : Option (XSt N T)`: every label carries all of its choices (the emission a
return hands back, the names a deadline step reaps, whether a start is synchronous), so the
reference is deterministic given the label, and membership of a concrete run is decidable by
evaluation (`xrun`). `RefExec C s l s'` is its graph. Requirements quantify over an abstract
`XRel`, so a mutant can be any relation.

`P : XPol N T` holds the judgement points; the reference is `xstepW refXPol`, and a one-field
change of `refXPol` is a mutant. Each label has its own rule function (`commitStep`,
`failStep`, ...), and each rule its inversion lemma (`commitStep_some`, ...), so a proof about
one label never unfolds the others, and adding a rule breaks no finished proof.

**Rules.** Outside: `delay`, `write`, `flush`, `ret`, `expire`, `request`, `drain`, `close`,
`terminateNow`. Step 1: `commit`, `fail`, `tdeposit`, `endCompletions`. Step 1b: `publish`,
`endPublications`. Step 2: `inject`, `discard`, `endEvents`, and the `snapshot` answer. Steps 3 and
4: `update`, `deadline`. The termination test: the four `finish` causes and `begin`. Step 5:
`start`, `lose`, `endPass`. Step 6: `park`, `wake`. Wave 0 (the EXEC-021 tracer) wrote the
action's outside steps, settling, publication, the update, the deadline step, the test and the
pass; wave 1 wrote injection, the snapshot, the lifecycle (drain, close and the immediate
termination of [ENV-015], ruling D47 (c)) and the wait.

**Rulings the rules follow.** D8 (b): re-entrancy is the configuration's (`Cfg.reentrant`).
D13 (a): the termination test follows the update and the deadline step, rest is "nothing armed,
in flight or queued", the loop waits while actions are in flight, and every arrival (a return,
an expiry, a flush, an accepted request, a drain, a close) wakes it. D18 (b): an action budget is
host time, so `expire` is a free outside step of an asynchronous firing with a `Timeout` node,
either side may win a tie, and "never early" is not a rule. D44 (a), D48 (a): injections are
FIFO by acceptance and appended at the tail; once closed the queued ones are discarded (Java,
TypeScript; Rust injects what was sent before its close, a run whose `close` comes after those
injections). D85 (a): a close keeps starting ready transitions while a firing is in flight.
D47 (c): the immediate termination of [ENV-015] is modelled (Java only).

**The invariant at the phase boundaries** (`InvU`, end of the file): after the update and after
the deadline step an armed name's transition is enabled, an off name's enabled transition is in
flight under `¬reentrant`, and a reaped name's transition is enabled (`invU_boundary`).

**Rust correspondence** (`executor_core/executor.rs`, async loop `run_async`):

* `commit`, `fail`, `tdeposit` in phase `completions`: `handle_completion` (1248-1345), called in
  Phase 1 (1044-1048) while no terminal place is marked. Validation reads the returned outputs
  and `flushed_places` (`output_conforms`, 674-704, called at 1266-1270); the timeout path skips
  validation and still runs the relay check (1261-1299, ruling D24 (a)); a violation or a relay
  rejection deposits nothing (`return`), an error result emits TransitionFailed (1331-1339).
* `commit`, `fail` inside the pass for a synchronous firing: `fire_transition_async`'s sync branch
  (1491-1572), the same checks inline; a synchronous firing has no timeout race.
* `publish`: Phase 1b, `handle_flush` (1347-1365), unconditional, FIFO on one channel.
* `update`: Phase 3 at `cycle_now` (1063-1065); `deadline`: Phase 4 at the same reading
  (1067-1083), a reference run with no delay between the two. The reference deadline step takes a
  reading of its own (`atDeadline`, never earlier than the update's, ruling D61 (c)), so a runtime
  that reads the clock again after its update (TypeScript's `cycleNowMs`) is a run with a delay
  between the update and the deadline step; `finish`: the termination checks (1085-1095) and the terminal check at the top of
  the loop (1035-1042).
* `inject`, `discard`, `snapshot`: Phase 2's `handle_signal` (1368-1448); a close discards
  what is still queued behind it (1427-1432). `request`, `drain`, `close`: `ExecutorHandle`
  (executor_handle.rs 67-125), refusing once drained or closed.
* `park`, `wake`: Phase 6 (1131-1199), the timer from `cycle_now` (1145); every channel arm
  wakes the loop.
* `begin`, `start`, `lose`, `endPass`: Phase 5 (1097-1124); the recheck is
  `recheck_can_fire` against the pass snapshot (`bitmap_backend.rs:708-713`), a loser is
  `disable`d.
* `expire`: the spawned task's `select!` against the budget (1679-1705), only for an async
  firing whose spec has a `Timeout` node; `ret`: the task's completion message; `flush`: the
  action's `ctx.flush()` with the relay guard of its callback (1640-1670); a synchronous firing
  has no callback, so its flush is no step. A batch the relay check rejects marks the firing
  `relayBad`, and its completion, normal or timed out, becomes an error (1711-1715).
-/

namespace Libpetri.Reference

open Libpetri Libpetri.Spec Libpetri.Novel.Seam

variable {N T : Type} [DecidableEq N]

/-! ## Outside steps -/

/-- Apply `g` to firing `i`, if it is in flight with no outcome set. -/
def onOpen (s : XSt N T) (i : Nat) (g : Firing N T → XSt N T) : Option (XSt N T) :=
  match s.fl.find? (·.id == i) with
  | some f => if f.out.isNone then some (g f) else none
  | none => none

/-- Replace firing `i`'s record by `h` of it. -/
def updFiring (s : XSt N T) (i : Nat) (h : Firing N T → Firing N T) : List (Firing N T) :=
  s.fl.map fun g => if g.id == i then h g else g

/-- `write i p x`: the action of firing `i` buffers `(p, x)`. -/
def writeStep (s : XSt N T) (i : Nat) (p : N) (x : T) : Option (XSt N T) :=
  onOpen s i fun _ => { s with fl := updFiring s i fun g => { g with buf := g.buf ++ [(p, x)] } }

/-- `flush i`: the non-empty buffer of an asynchronous firing becomes a queued publication; its
places count for validation. A synchronous firing cannot flush (Rust: `ctx.flush()` returns `Err`
when no flush callback is installed, the buffer untouched; `flush` of the Rust context module), and an empty
flush is no step (`Ok` with nothing sent). A batch the join-relay check of [NU-054] rejects, and
every batch after it, is dropped and marks the firing `relayBad` (the relay guard of the flush
callback, executor_core/executor.rs 1640-1670). -/
def flushStep (C : Cfg N T) (s : XSt N T) (i : Nat) : Option (XSt N T) :=
  match s.fl.find? (·.id == i) with
  | some f =>
    if f.out.isNone && !f.sync && !f.buf.isEmpty then
      if !f.relayBad && C.relay f.t f.deliv f.buf then
        some { s with pq := s.pq ++ [(i, f.buf)], parked := false,
                      fl := updFiring s i fun g =>
                        { g with buf := [], pub := g.pub ++ g.buf.map Prod.fst } }
      else some { s with fl := updFiring s i fun g => { g with buf := [], relayBad := true } }
    else none
  | none => none

/-- `ret i ok`: the action returns; a normal return freezes the buffer as its emission. A firing
whose flushed batch failed the relay check ends with an error (executor_core/executor.rs 1711-1715). -/
def retStep (s : XSt N T) (i : Nat) (ok : Bool) : Option (XSt N T) :=
  onOpen s i fun _ =>
    { s with cq := s.cq ++ [i], parked := false,
             fl := updFiring s i fun g =>
               { g with out := some (if ok && !g.relayBad then .ok g.buf else .err) } }

/-- `expire i e`: the budget of an asynchronous firing with a `Timeout` node expires first, with
timeout outcome `e`. A firing whose flushed batch failed the relay check ends with an error here
too: the slot is read after the `select!` (executor_core/executor.rs 1711-1715). -/
def expireStep (C : Cfg N T) (s : XSt N T) (i : Nat) (e : List (N × T)) : Option (XSt N T) :=
  match s.fl.find? (·.id == i) with
  | some f =>
    if f.out.isNone && !f.sync && hasTimeoutB f.t && C.timeoutOut f.t f.deliv e then
      some { s with cq := s.cq ++ [i], parked := false,
                    fl := updFiring s i fun g =>
                      { g with out := some (if g.relayBad then .err else .timedOut e) } }
    else none
  | none => none

/-! ## Step 1: settling -/

/-- The state after depositing emission `e` of firing `i`: appended at the tails, reaped names
whose arc places it writes turned off (D6), and, inside the pass, counted as same-pass tail. -/
def depositAt (C : Cfg N T) (s : XSt N T) (i : Nat) (e : List (N × T)) : XSt N T :=
  { settle s i with
    M := qAppend s.M e, st := unreap C (e.map Prod.fst) s.st,
    delta := if s.phase = .pass then (fun p => s.delta p + countIn e p) else s.delta }

/-- `commit i`: a returned emission that output validation and the relay check accept is
deposited. -/
def commitStep (P : XPol N T) (C : Cfg N T) (s : XSt N T) (i : Nat) : Option (XSt N T) :=
  match s.fl.find? (·.id == i) with
  | some f =>
    match f.out with
    | some (.ok e) =>
      if canSettle C s i f && C.validate f.t (P.validIn f e) && C.relay f.t f.deliv e
      then some (depositAt C s i e) else none
    | _ => none
  | none => none

/-- Why a settle deposits nothing: the action failed; validation or the relay check rejects a
returned emission; the relay check rejects a timeout outcome (ruling D24 (a): the timeout outcome
is not validated against the output spec). -/
def failCause (P : XPol N T) (C : Cfg N T) (f : Firing N T) : Bool :=
  match f.out with
  | some .err => true
  | some (.ok e) => !(C.validate f.t (P.validIn f e) && C.relay f.t f.deliv e)
  | some (.timedOut e) => !C.relay f.t f.deliv e
  | none => false

/-- `fail i`: the firing is settled without a deposit; nothing is restored and nothing already
published is withdrawn. -/
def failStep (P : XPol N T) (C : Cfg N T) (s : XSt N T) (i : Nat) : Option (XSt N T) :=
  match s.fl.find? (·.id == i) with
  | some f => if canSettle C s i f && failCause P C f then some (settle s i) else none
  | none => none

/-- `tdeposit i`: a timeout outcome the relay check accepts is deposited, unvalidated. -/
def tdepositStep (C : Cfg N T) (s : XSt N T) (i : Nat) : Option (XSt N T) :=
  match s.fl.find? (·.id == i) with
  | some f =>
    match f.out with
    | some (.timedOut e) =>
      if canSettle C s i f && C.relay f.t f.deliv e then some (depositAt C s i e) else none
    | _ => none
  | none => none

/-- `publish i`: the oldest queued publication, of firing `i`, lands at the tails (ruling D17:
whatever happens to the completion). -/
def publishStep (C : Cfg N T) (s : XSt N T) (i : Nat) : Option (XSt N T) :=
  match s.pq with
  | (j, b) :: rest =>
    if j == i && liveB C s &&
        (s.phase = .publications || (s.phase = .await && s.mode != .stopped)) then
      some { s with M := qAppend s.M b, st := unreap C (b.map Prod.fst) s.st, pq := rest,
                    phase := if s.phase = .await then .completions else s.phase,
                    parked := false }
    else none
  | [] => none

/-! ## Step 2: injection, and the snapshot request -/

/-- `inject k`: the oldest queued injection, ticket `k`, lands at the tail of its place (ruling
D48 (a): FIFO by acceptance, appended at the tail); an injected token writes its place (ruling D6),
so a reaped transition with an arc on it is no longer reaped. Offered in step 2 and on the wake of
the wait (R-EXEC-9 (a)), while the executor is open or draining. Rust: `handle_signal`'s `Event`
arm (executor_core/executor.rs 1377-1393), Phase 2 (1055-1058) and the wait's signal arm (1175-1190). -/
def injectStep (C : Cfg N T) (s : XSt N T) (k : Nat) : Option (XSt N T) :=
  match s.eq with
  | (j, p, x) :: rest =>
    if j == k && liveB C s && !s.mode.closing && (s.phase = .events || s.phase = .await) then
      some { s with M := qAppendOne s.M p x, st := unreap C [p] s.st, eq := rest,
                    phase := if s.phase = .await then .completions else s.phase,
                    parked := false }
    else none
  | [] => none

/-- `discard k`: the oldest queued injection, ticket `k`, is dropped unapplied once the executor
is closed or stopped (ruling D44 (a), Java and TypeScript; Rust injects what was sent before its
close, a run in which the `close` step comes after those injections). -/
def discardStep (C : Cfg N T) (s : XSt N T) (k : Nat) : Option (XSt N T) :=
  match s.eq with
  | (j, _, _) :: rest =>
    if j == k && liveB C s && s.mode.closing && (s.phase = .events || s.phase = .await) then
      some { s with eq := rest, phase := if s.phase = .await then .completions else s.phase,
                    parked := false }
    else none
  | [] => none

/-- `snapshot a`: the executor answers a snapshot request with `a = snapAnswer s` and the marking
`M`, and changes nothing ([ENV-014], ruling D43 (a)). Offered after step 2's injections, before
the update, and in the wait. Rust: `handle_signal`'s `Snapshot` arm (1433-1446), the in-flight
flag read in the same step as the marking; Java: `serviceMarkingRequest` after the external-events
phase. -/
def snapshotStep (C : Cfg N T) (s : XSt N T) (a : Option Bool) : Option (XSt N T) :=
  if liveB C s && (s.phase = .events || s.phase = .update || s.phase = .await) &&
      a == snapAnswer s then some s else none

/-! ## Outside: requests and the lifecycle -/

/-- `request p x r`: a caller asks to inject `x` into `p` and gets `r = replyFor C s p`; an
accepted request queues the event with a fresh ticket and wakes the wait ([ENV-003], [ENV-005]).
Rust: `ExecutorHandle::inject` (executor_handle.rs 67-74), refusing once drained or closed. -/
def requestStep (C : Cfg N T) (s : XSt N T) (p : N) (x : T) (r : Reply) : Option (XSt N T) :=
  if r = replyFor C s p then
    if r = .accepted then
      some { s with eq := s.eq ++ [(s.nextId, p, x)], nextId := s.nextId + 1, parked := false }
    else some s
  else none

/-- `drain`: an open executor starts draining and wakes ([ENV-011]). Rust: `drain()`
(executor_handle.rs 106-113) and the `Drain` signal (1424-1426). -/
def drainStep (s : XSt N T) : Option (XSt N T) :=
  if s.mode = .open then some { s with mode := .draining, parked := false } else none

/-- `close`: an open or draining executor closes and wakes ([ENV-013]). Nothing in flight is
abandoned, and the loop goes on starting ready transitions while a firing is in flight (ruling
D85 (a)). Rust: `close()` (executor_handle.rs 122-125) and the `Close` signal (1427-1432). -/
def closeStep (s : XSt N T) : Option (XSt N T) :=
  if s.mode = .open || s.mode = .draining then some { s with mode := .closed, parked := false }
  else none

/-- `terminateNow`: an immediate termination ([ENV-015], ruling D47 (c); Java only): the executor
stops accepting, the queued injections are dropped at once (Java completes them with `false` in
`terminateNow`), and the loop ends at the end of its current cycle (`finish stopped`). -/
def terminateStep (s : XSt N T) : Option (XSt N T) :=
  if s.mode != .stopped then some { s with mode := .stopped, eq := [], parked := false }
  else none

/-! ## Step 6: the wait -/

/-- `park tmr`: with nothing queued and nothing Ready or Expired at the cycle reading, the loop
waits, with a timer no later than the next timing boundary plus the timer resolution
([CONC-010], ruling D13 (a), design R8). Rust: Phase 6 (1131-1199), the timer from
`millis_until_next_timed_transition(cycle_now)` (1145). -/
def parkStep (C : Cfg N T) (s : XSt N T) (tmr : Option Nat) : Option (XSt N T) :=
  if s.phase = .await && liveB C s && !s.parked && s.cq.isEmpty && s.pq.isEmpty &&
      s.eq.isEmpty && nothingDue C s && timerOk C s tmr
  then some { s with parked := true } else none

/-- `wake`: the wait ends (a timer, a spurious wake-up, an arrival) and the loop goes back to
step 1. -/
def wakeStep (C : Cfg N T) (s : XSt N T) : Option (XSt N T) :=
  if s.phase = .await && liveB C s then some { s with phase := .completions, parked := false }
  else none

/-! ## The firing pass -/

/-- The termination test's two finish premises (quiescent, closed). -/
def finishQ (C : Cfg N T) (s : XSt N T) : Bool := restB C s && (C.envs.isEmpty || s.mode != .open)

/-- `start n sy`: the head of the order starts, if it is armed and enabled on the marking the
pass judges (`P.recheckOn`, the pass-visible one). -/
def startStep (P : XPol N T) (C : Cfg N T) (s : XSt N T) (n : String) (sy : Bool) :
    Option (XSt N T) :=
  match s.order with
  | t :: rest =>
    if s.phase = .pass && liveB C s && passFree s && t.core.name == n &&
        (stampOf (s.st n)).isSome && enabledNA (qCount (P.recheckOn s)) t.core then
      some { s with M := liveAfter s t, order := rest, started := true, nextId := s.nextId + 1,
                    fl := s.fl ++ [⟨s.nextId, t, qDelivered (vis s) t, s.now, sy, [], [], false,
                      none⟩],
                    st := unreap C (inPlaces t ++ t.core.resets) (afterStart P C s t) }
    else none
  | [] => none

/-- `lose n`: the head of the order cannot start; its clock is lost. -/
def loseStep (P : XPol N T) (C : Cfg N T) (s : XSt N T) (n : String) : Option (XSt N T) :=
  match s.order with
  | t :: rest =>
    if s.phase = .pass && liveB C s && passFree s && t.core.name == n &&
        !((stampOf (s.st n)).isSome && enabledNA (qCount (P.recheckOn s)) t.core) then
      some { s with order := rest, st := fun m => if m = n then .off else s.st m }
    else none
  | [] => none

/-! ## The step function -/

/-- One step of the executor with judgement points `P`. -/
def xstepW (P : XPol N T) (C : Cfg N T) (s : XSt N T) : XLbl N T → Option (XSt N T)
  -- outside steps
  | .delay δ => some { s with now := s.now + δ }
  | .write i p x => writeStep s i p x
  | .flush i => flushStep C s i
  | .ret i ok => retStep s i ok
  | .expire i e => expireStep C s i e
  | .request p x r => requestStep C s p x r
  | .drain => drainStep s
  | .close => closeStep s
  | .terminateNow => terminateStep s
  -- step 1
  | .commit i => commitStep P C s i
  | .fail i => failStep P C s i
  | .tdeposit i => tdepositStep C s i
  | .endCompletions =>
      if s.phase = .completions && liveB C s && s.cq.isEmpty && s.mode != .stopped then
        some { s with phase := .publications } else none
  -- step 1b
  | .publish i => publishStep C s i
  | .endPublications =>
      if s.phase = .publications && liveB C s && s.pq.isEmpty then
        some { s with phase := .events } else none
  -- step 2
  | .inject k => injectStep C s k
  | .discard k => discardStep C s k
  | .snapshot a => snapshotStep C s a
  | .endEvents =>
      if s.phase = .events && liveB C s && s.eq.isEmpty then
        some { s with phase := .update } else none
  -- step 3: the update's reading, the stamp of what it newly arms (R-EXEC-3)
  | .update =>
      if s.phase = .update && liveB C s then
        some { s with cyc := s.now, st := updSt P C s, phase := .deadline } else none
  -- step 4: take the deadline step's reading, never earlier than the update's (ruling D61 (c)),
  -- and reap every expired name at it (equality, not inclusion); steps 5 and 6 judge at it
  | .deadline ns =>
      if s.phase = .deadline && liveB C s && ns == expiredNames P C (atDeadline s) then
        some { s with cyc := max s.cyc s.now,
                      st := fun n => if ns.contains n then .reaped else s.st n, phase := .test }
      else none
  -- the termination test
  | .finish .quiescent =>
      if s.phase = .test && liveB C s && finishQ C s then
        some { s with phase := .done .quiescent, eq := [] } else none
  | .finish .closed =>
      if s.phase = .test && liveB C s && s.mode.closing && s.fl.isEmpty then
        some { s with phase := .done .closed, eq := [] } else none
  | .finish .terminal =>
      if isExecPhase s.phase && !liveB C s then
        some { s with phase := .done .terminal, eq := [], pq := [] } else none
  -- the end of the cycle after an immediate termination: at the top of the loop
  | .finish .stopped =>
      if s.phase = .completions && liveB C s && s.mode = .stopped then
        some { s with phase := .done .stopped, eq := [], pq := [] } else none
  | .begin =>
      if s.phase = .test && liveB C s && !finishQ C s && !(s.mode.closing && s.fl.isEmpty) then
        some { s with phase := .pass, order := readyOrder C s, delta := fun _ => 0,
                      started := false }
      else none
  -- step 5
  | .start n sy => startStep P C s n sy
  | .lose n => loseStep P C s n
  | .endPass =>
      if s.phase = .pass && liveB C s && s.order.isEmpty && passFree s then
        some { s with phase := if s.started then .completions else .await } else none
  -- step 6
  | .park tmr => parkStep C s tmr
  | .wake => wakeStep C s

/-- One step of the reference executor. -/
def xstep (C : Cfg N T) (s : XSt N T) (l : XLbl N T) : Option (XSt N T) := xstepW refXPol C s l

/-- **The reference executor**: the graph of `xstep`. -/
def RefExec : XRel N T := fun C s l s' => xstep C s l = some s'

/- The reference executor is the witness model of the executor requirements' `holds` theorems. -/
#spec_witness RefExec

/-- A run, as a fold; membership of a concrete run is decidable through it. -/
def xrun (C : Cfg N T) (s : XSt N T) : List (XLbl N T) → Option (XSt N T)
  | [] => some s
  | l :: ls => (xstep C s l).bind fun s' => xrun C s' ls

/-- The initial state from queue marking `M0` at reading `r0`: every name off (the first update
arms what `M0` enables, design R19), phase `completions`, nothing in flight or queued. -/
def xinit (M0 : QMarking N T) (r0 : Nat) : XSt N T where
  M := M0
  now := r0
  cyc := r0
  st := fun _ => .off
  fl := []
  nextId := 0
  cq := []
  pq := []
  eq := []
  mode := .open
  phase := .completions
  order := []
  delta := fun _ => 0
  started := false
  parked := false

/-! ## Inversion lemmas (one per label with a rule used by a block) -/

/-- Inversion of `commit`. -/
theorem commitStep_some {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {i : Nat}
    (h : commitStep P C s i = some s') :
    ∃ f e, s.fl.find? (·.id == i) = some f ∧ f.out = some (.ok e) ∧
      canSettle C s i f = true ∧ C.validate f.t (P.validIn f e) = true ∧
      C.relay f.t f.deliv e = true ∧ s' = depositAt C s i e := by
  unfold commitStep at h
  split at h
  · rename_i f hf
    split at h
    · rename_i e he
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true] at hc
        exact ⟨f, e, hf, he, hc.1.1, hc.1.2, hc.2, (Option.some.inj h).symm⟩
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [DecidableEq N] in
/-- Inversion of `fail`. -/
theorem failStep_some {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {i : Nat}
    (h : failStep P C s i = some s') :
    ∃ f, s.fl.find? (·.id == i) = some f ∧ canSettle C s i f = true ∧
      failCause P C f = true ∧ s' = settle s i := by
  unfold failStep at h
  split at h
  · rename_i f hf
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      exact ⟨f, hf, hc.1, hc.2, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [DecidableEq N] in
/-- What `failCause` says, case by case. -/
theorem failCause_cases {P : XPol N T} {C : Cfg N T} {f : Firing N T}
    (h : failCause P C f = true) :
    f.out = some .err ∨
      (∃ e, f.out = some (.ok e) ∧
        (C.validate f.t (P.validIn f e) = false ∨ C.relay f.t f.deliv e = false)) ∨
      (∃ e, f.out = some (.timedOut e) ∧ C.relay f.t f.deliv e = false) := by
  unfold failCause at h
  split at h
  · exact Or.inl ‹_›
  · rename_i e he
    simp only [Bool.not_eq_true', Bool.and_eq_false_iff] at h
    exact Or.inr (Or.inl ⟨e, he, h⟩)
  · rename_i e he
    simp only [Bool.not_eq_true'] at h
    exact Or.inr (Or.inr ⟨e, he, h⟩)
  · exact absurd h (by simp)

/-- The `commit` step of the reference executor. -/
theorem refExec_commit {C : Cfg N T} {s s' : XSt N T} {i : Nat}
    (h : RefExec C s (.commit i) s') :
    ∃ f e, s.fl.find? (·.id == i) = some f ∧ f.out = some (.ok e) ∧
      canSettle C s i f = true ∧ C.validate f.t (validIn f e) = true ∧
      C.relay f.t f.deliv e = true ∧ s' = depositAt C s i e :=
  commitStep_some (P := refXPol) h

/-- The `fail` step of the reference executor. -/
theorem refExec_fail {C : Cfg N T} {s s' : XSt N T} {i : Nat}
    (h : RefExec C s (.fail i) s') :
    ∃ f, s.fl.find? (·.id == i) = some f ∧ canSettle C s i f = true ∧
      failCause refXPol C f = true ∧ s' = settle s i :=
  failStep_some (P := refXPol) h

/-- Inversion of `tdeposit`. -/
theorem tdepositStep_some {C : Cfg N T} {s s' : XSt N T} {i : Nat}
    (h : tdepositStep C s i = some s') :
    ∃ f e, s.fl.find? (·.id == i) = some f ∧ f.out = some (.timedOut e) ∧
      canSettle C s i f = true ∧ C.relay f.t f.deliv e = true ∧ s' = depositAt C s i e := by
  unfold tdepositStep at h
  split at h
  · rename_i f hf
    split at h
    · rename_i e he
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true] at hc
        exact ⟨f, e, hf, he, hc.1, hc.2, (Option.some.inj h).symm⟩
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [DecidableEq N] in
/-- A `write` step leaves the marking as it is: the token waits in the firing's buffer. -/
theorem writeStep_M {s s' : XSt N T} {i : Nat} {p : N} {x : T}
    (h : writeStep s i p x = some s') : s'.M = s.M := by
  unfold writeStep onOpen at h
  split at h
  · split at h
    · cases h; rfl
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [DecidableEq N] in
/-- A `ret` step leaves the marking as it is: the emission waits for its settle step. -/
theorem retStep_M {s s' : XSt N T} {i : Nat} {ok : Bool}
    (h : retStep s i ok = some s') : s'.M = s.M := by
  unfold retStep onOpen at h
  split at h
  · split at h
    · cases h; rfl
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-! ## Inversion lemmas of the other rules (wave 1)

One lemma per label: the guard facts of the rule and the target state. A block proof inverts one
label with its lemma; `RefExec C s l s'` unfolds to the rule function of `l` at `refXPol`, so
each lemma applies to a `RefExec` step directly. -/

/-- Inversion of `delay`. -/
theorem xstepW_delay {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {δ : Nat}
    (h : xstepW P C s (.delay δ) = some s') : s' = { s with now := s.now + δ } :=
  (Option.some.inj h).symm

omit [DecidableEq N] in
/-- Inversion of `write`. -/
theorem writeStep_some {s s' : XSt N T} {i : Nat} {p : N} {x : T}
    (h : writeStep s i p x = some s') :
    ∃ f, s.fl.find? (·.id == i) = some f ∧ f.out = none ∧
      s' = { s with fl := updFiring s i fun g => { g with buf := g.buf ++ [(p, x)] } } := by
  unfold writeStep onOpen at h
  split at h
  · rename_i f hf
    split at h
    · rename_i ho
      exact ⟨f, hf, Option.isNone_iff_eq_none.mp ho, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [DecidableEq N] in
/-- Inversion of `ret`. -/
theorem retStep_some {s s' : XSt N T} {i : Nat} {ok : Bool}
    (h : retStep s i ok = some s') :
    ∃ f, s.fl.find? (·.id == i) = some f ∧ f.out = none ∧
      s' = { s with cq := s.cq ++ [i], parked := false,
                    fl := updFiring s i fun g =>
                      { g with out := some (if ok && !g.relayBad then .ok g.buf else .err) } } := by
  unfold retStep onOpen at h
  split at h
  · rename_i f hf
    split at h
    · rename_i ho
      exact ⟨f, hf, Option.isNone_iff_eq_none.mp ho, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [DecidableEq N] in
/-- Inversion of `flush`: either the batch passes the relay check and is queued, or it is
dropped and the firing is marked `relayBad`. -/
theorem flushStep_some {C : Cfg N T} {s s' : XSt N T} {i : Nat}
    (h : flushStep C s i = some s') :
    ∃ f, s.fl.find? (·.id == i) = some f ∧ f.out = none ∧ f.sync = false ∧ f.buf ≠ [] ∧
      ((f.relayBad = false ∧ C.relay f.t f.deliv f.buf = true ∧
        s' = { s with pq := s.pq ++ [(i, f.buf)], parked := false,
                      fl := updFiring s i fun g =>
                        { g with buf := [], pub := g.pub ++ g.buf.map Prod.fst } }) ∨
       ((f.relayBad = true ∨ C.relay f.t f.deliv f.buf = false) ∧
        s' = { s with fl := updFiring s i fun g => { g with buf := [], relayBad := true } })) := by
  unfold flushStep at h
  split at h
  · rename_i f hf
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none,
        List.isEmpty_eq_false_iff] at hc
      obtain ⟨⟨ho, hsy⟩, hb⟩ := hc
      split at h
      · rename_i hr
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hr
        exact ⟨f, hf, ho, hsy, hb, Or.inl ⟨hr.1, hr.2, (Option.some.inj h).symm⟩⟩
      · rename_i hr
        simp only [Bool.and_eq_true, Bool.not_eq_true', not_and] at hr
        refine ⟨f, hf, ho, hsy, hb, Or.inr ⟨?_, (Option.some.inj h).symm⟩⟩
        cases hrb : f.relayBad
        · exact Or.inr (by simpa using hr hrb)
        · exact Or.inl rfl
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [DecidableEq N] in
/-- Inversion of `expire` (ruling D18 (b): a free outside step of an asynchronous firing whose
output spec has a `Timeout` node, while its outcome is not set). -/
theorem expireStep_some {C : Cfg N T} {s s' : XSt N T} {i : Nat} {e : List (N × T)}
    (h : expireStep C s i e = some s') :
    ∃ f, s.fl.find? (·.id == i) = some f ∧ f.out = none ∧ f.sync = false ∧
      hasTimeoutB f.t = true ∧ C.timeoutOut f.t f.deliv e = true ∧
      s' = { s with cq := s.cq ++ [i], parked := false,
                    fl := updFiring s i fun g =>
                      { g with out := some (if g.relayBad then .err else .timedOut e) } } := by
  unfold expireStep at h
  split at h
  · rename_i f hf
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none] at hc
      obtain ⟨⟨⟨ho, hsy⟩, ht⟩, hto⟩ := hc
      exact ⟨f, hf, ho, hsy, ht, hto, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Inversion of `endCompletions`. -/
theorem xstepW_endCompletions {P : XPol N T} {C : Cfg N T} {s s' : XSt N T}
    (h : xstepW P C s .endCompletions = some s') :
    s.phase = .completions ∧ liveB C s = true ∧ s.cq = [] ∧ s.mode ≠ .stopped ∧
      s' = { s with phase := .publications } := by
  simp only [xstepW] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff, bne_iff_ne, ne_eq] at hc
    exact ⟨hc.1.1.1, hc.1.1.2, hc.1.2, hc.2, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- Inversion of `publish`. -/
theorem publishStep_some {C : Cfg N T} {s s' : XSt N T} {i : Nat}
    (h : publishStep C s i = some s') :
    ∃ b rest, s.pq = (i, b) :: rest ∧ liveB C s = true ∧
      (s.phase = .publications ∨ (s.phase = .await ∧ s.mode ≠ .stopped)) ∧
      s' = { s with M := qAppend s.M b, st := unreap C (b.map Prod.fst) s.st, pq := rest,
                    phase := if s.phase = .await then .completions else s.phase,
                    parked := false } := by
  unfold publishStep at h
  split at h
  · rename_i j b rest he
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne,
        ne_eq] at hc
      obtain ⟨⟨rfl, hl⟩, hph⟩ := hc
      exact ⟨b, rest, he, hl, hph, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Inversion of `endPublications`. -/
theorem xstepW_endPublications {P : XPol N T} {C : Cfg N T} {s s' : XSt N T}
    (h : xstepW P C s .endPublications = some s') :
    s.phase = .publications ∧ liveB C s = true ∧ s.pq = [] ∧ s' = { s with phase := .events } := by
  simp only [xstepW] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at hc
    exact ⟨hc.1.1, hc.1.2, hc.2, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- Inversion of `inject`. -/
theorem injectStep_some {C : Cfg N T} {s s' : XSt N T} {k : Nat}
    (h : injectStep C s k = some s') :
    ∃ p x rest, s.eq = (k, p, x) :: rest ∧ liveB C s = true ∧ s.mode.closing = false ∧
      (s.phase = .events ∨ s.phase = .await) ∧
      s' = { s with M := qAppendOne s.M p x, st := unreap C [p] s.st, eq := rest,
                    phase := if s.phase = .await then .completions else s.phase,
                    parked := false } := by
  unfold injectStep at h
  split at h
  · rename_i j p x rest he
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Bool.or_eq_true,
        decide_eq_true_eq] at hc
      obtain ⟨⟨⟨rfl, hl⟩, hm⟩, hph⟩ := hc
      exact ⟨p, x, rest, he, hl, hm, hph, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [DecidableEq N] in
/-- Inversion of `discard`. -/
theorem discardStep_some {C : Cfg N T} {s s' : XSt N T} {k : Nat}
    (h : discardStep C s k = some s') :
    ∃ p x rest, s.eq = (k, p, x) :: rest ∧ liveB C s = true ∧ s.mode.closing = true ∧
      (s.phase = .events ∨ s.phase = .await) ∧
      s' = { s with eq := rest, phase := if s.phase = .await then .completions else s.phase,
                    parked := false } := by
  unfold discardStep at h
  split at h
  · rename_i j p x rest he
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨rfl, hl⟩, hm⟩, hph⟩ := hc
      exact ⟨p, x, rest, he, hl, hm, hph, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [DecidableEq N] in
/-- Inversion of `snapshot`: the answer is `snapAnswer s`, and nothing changes. -/
theorem snapshotStep_some {C : Cfg N T} {s s' : XSt N T} {a : Option Bool}
    (h : snapshotStep C s a = some s') :
    liveB C s = true ∧ (s.phase = .events ∨ s.phase = .update ∨ s.phase = .await) ∧
      a = snapAnswer s ∧ s' = s := by
  unfold snapshotStep at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    obtain ⟨⟨hl, hph⟩, ha⟩ := hc
    exact ⟨hl, by rcases hph with (h1 | h2) | h3 <;> simp_all, ha, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- Inversion of `endEvents`. -/
theorem xstepW_endEvents {P : XPol N T} {C : Cfg N T} {s s' : XSt N T}
    (h : xstepW P C s .endEvents = some s') :
    s.phase = .events ∧ liveB C s = true ∧ s.eq = [] ∧ s' = { s with phase := .update } := by
  simp only [xstepW] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at hc
    exact ⟨hc.1.1, hc.1.2, hc.2, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- Inversion of `update`: the update's reading, every name re-evaluated. -/
theorem xstepW_update {P : XPol N T} {C : Cfg N T} {s s' : XSt N T}
    (h : xstepW P C s .update = some s') :
    s.phase = .update ∧ liveB C s = true ∧
      s' = { s with cyc := s.now, st := updSt P C s, phase := .deadline } := by
  simp only [xstepW] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact ⟨hc.1, hc.2, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- Inversion of `deadline`: the cycle reading moves to the deadline step's reading, and exactly
the names expired at it are reaped. -/
theorem xstepW_deadline {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {ns : List String}
    (h : xstepW P C s (.deadline ns) = some s') :
    s.phase = .deadline ∧ liveB C s = true ∧ ns = expiredNames P C (atDeadline s) ∧
      s' = { s with cyc := max s.cyc s.now,
                    st := fun n => if ns.contains n then .reaped else s.st n, phase := .test } := by
  simp only [xstepW] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    exact ⟨hc.1.1, hc.1.2, hc.2, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- Inversion of `finish quiescent`. -/
theorem xstepW_finishQuiescent {P : XPol N T} {C : Cfg N T} {s s' : XSt N T}
    (h : xstepW P C s (.finish .quiescent) = some s') :
    s.phase = .test ∧ liveB C s = true ∧ finishQ C s = true ∧
      s' = { s with phase := .done .quiescent, eq := [] } := by
  simp only [xstepW] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact ⟨hc.1.1, hc.1.2, hc.2, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- Inversion of `finish closed`. -/
theorem xstepW_finishClosed {P : XPol N T} {C : Cfg N T} {s s' : XSt N T}
    (h : xstepW P C s (.finish .closed) = some s') :
    s.phase = .test ∧ liveB C s = true ∧ s.mode.closing = true ∧ s.fl = [] ∧
      s' = { s with phase := .done .closed, eq := [] } := by
  simp only [xstepW] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at hc
    exact ⟨hc.1.1.1, hc.1.1.2, hc.1.2, hc.2, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- Inversion of `finish terminal`. -/
theorem xstepW_finishTerminal {P : XPol N T} {C : Cfg N T} {s s' : XSt N T}
    (h : xstepW P C s (.finish .terminal) = some s') :
    isExecPhase s.phase = true ∧ liveB C s = false ∧
      s' = { s with phase := .done .terminal, eq := [], pq := [] } := by
  simp only [xstepW] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
    exact ⟨hc.1, hc.2, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- Inversion of `finish stopped`: at the top of the loop after an immediate termination. -/
theorem xstepW_finishStopped {P : XPol N T} {C : Cfg N T} {s s' : XSt N T}
    (h : xstepW P C s (.finish .stopped) = some s') :
    s.phase = .completions ∧ liveB C s = true ∧ s.mode = .stopped ∧
      s' = { s with phase := .done .stopped, eq := [], pq := [] } := by
  simp only [xstepW] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact ⟨hc.1.1, hc.1.2, hc.2, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- Inversion of `begin`. -/
theorem xstepW_begin {P : XPol N T} {C : Cfg N T} {s s' : XSt N T}
    (h : xstepW P C s .begin = some s') :
    s.phase = .test ∧ liveB C s = true ∧ finishQ C s = false ∧
      ¬ (s.mode.closing = true ∧ s.fl = []) ∧
      s' = { s with phase := .pass, order := readyOrder C s, delta := fun _ => 0,
                    started := false } := by
  simp only [xstepW] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.and_eq_false_iff,
      List.isEmpty_eq_false_iff] at hc
    obtain ⟨⟨⟨hp, hl⟩, hq⟩, hcl⟩ := hc
    refine ⟨hp, hl, hq, ?_, (Option.some.inj h).symm⟩
    rintro ⟨h1, h2⟩
    rcases hcl with h3 | h3
    · simp [h1] at h3
    · exact h3 h2
  · exact absurd h (by simp)

/-- Inversion of `start`. -/
theorem startStep_some {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {n : String} {sy : Bool}
    (h : startStep P C s n sy = some s') :
    ∃ t rest, s.order = t :: rest ∧ s.phase = .pass ∧ liveB C s = true ∧ passFree s = true ∧
      t.core.name = n ∧ (stampOf (s.st n)).isSome = true ∧
      enabledNA (qCount (P.recheckOn s)) t.core = true ∧
      s' = { s with M := liveAfter s t, order := rest, started := true, nextId := s.nextId + 1,
                    fl := s.fl ++ [⟨s.nextId, t, qDelivered (vis s) t, s.now, sy, [], [], false,
                      none⟩],
                    st := unreap C (inPlaces t ++ t.core.resets) (afterStart P C s t) } := by
  unfold startStep at h
  split at h
  · rename_i t rest ho
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      obtain ⟨⟨⟨⟨⟨hp, hl⟩, hpf⟩, hn⟩, hst⟩, he⟩ := hc
      exact ⟨t, rest, ho, hp, hl, hpf, hn, hst, he, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [DecidableEq N] in
/-- Inversion of `lose`. -/
theorem loseStep_some {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {n : String}
    (h : loseStep P C s n = some s') :
    ∃ t rest, s.order = t :: rest ∧ s.phase = .pass ∧ liveB C s = true ∧ passFree s = true ∧
      t.core.name = n ∧
      ¬ ((stampOf (s.st n)).isSome = true ∧ enabledNA (qCount (P.recheckOn s)) t.core = true) ∧
      s' = { s with order := rest, st := fun m => if m = n then .off else s.st m } := by
  unfold loseStep at h
  split at h
  · rename_i t rest ho
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true',
        Bool.and_eq_false_iff] at hc
      obtain ⟨⟨⟨⟨hp, hl⟩, hpf⟩, hn⟩, hne⟩ := hc
      refine ⟨t, rest, ho, hp, hl, hpf, hn, ?_, (Option.some.inj h).symm⟩
      rintro ⟨h1, h2⟩
      rcases hne with h3 | h3 <;> simp_all
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Inversion of `endPass`. -/
theorem xstepW_endPass {P : XPol N T} {C : Cfg N T} {s s' : XSt N T}
    (h : xstepW P C s .endPass = some s') :
    s.phase = .pass ∧ liveB C s = true ∧ s.order = [] ∧ passFree s = true ∧
      s' = { s with phase := if s.started then .completions else .await } := by
  simp only [xstepW] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at hc
    exact ⟨hc.1.1.1, hc.1.1.2, hc.1.2, hc.2, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- Inversion of `park`. -/
theorem parkStep_some {C : Cfg N T} {s s' : XSt N T} {tmr : Option Nat}
    (h : parkStep C s tmr = some s') :
    s.phase = .await ∧ liveB C s = true ∧ s.parked = false ∧ s.cq = [] ∧ s.pq = [] ∧
      s.eq = [] ∧ nothingDue C s = true ∧ timerOk C s tmr = true ∧
      s' = { s with parked := true } := by
  unfold parkStep at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.isEmpty_iff] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨hp, hl⟩, hpk⟩, hcq⟩, hpq⟩, heq⟩, hd⟩, ht⟩ := hc
    exact ⟨hp, hl, hpk, hcq, hpq, heq, hd, ht, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

omit [DecidableEq N] in
/-- Inversion of `wake`. -/
theorem wakeStep_some {C : Cfg N T} {s s' : XSt N T} (h : wakeStep C s = some s') :
    s.phase = .await ∧ liveB C s = true ∧
      s' = { s with phase := .completions, parked := false } := by
  unfold wakeStep at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact ⟨hc.1, hc.2, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- Inversion of `request`: the reply is `replyFor C s p`; only an accepted request changes the
state, and only the event queue, the ticket supply and the parked flag. -/
theorem requestStep_some {C : Cfg N T} {s s' : XSt N T} {p : N} {x : T} {r : Reply}
    (h : requestStep C s p x r = some s') :
    r = replyFor C s p ∧
      ((r = .accepted ∧
          s' = { s with eq := s.eq ++ [(s.nextId, p, x)], nextId := s.nextId + 1, parked := false })
        ∨ (r ≠ .accepted ∧ s' = s)) := by
  unfold requestStep at h
  split at h
  · rename_i hr
    split at h
    · rename_i ha
      exact ⟨hr, Or.inl ⟨ha, (Option.some.inj h).symm⟩⟩
    · rename_i ha
      exact ⟨hr, Or.inr ⟨ha, (Option.some.inj h).symm⟩⟩
  · exact absurd h (by simp)

omit [DecidableEq N] in
/-- Inversion of `drain`. -/
theorem drainStep_some {s s' : XSt N T} (h : drainStep s = some s') :
    s.mode = .open ∧ s' = { s with mode := .draining, parked := false } := by
  unfold drainStep at h
  split at h
  · exact ⟨‹_›, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

omit [DecidableEq N] in
/-- Inversion of `close`. -/
theorem closeStep_some {s s' : XSt N T} (h : closeStep s = some s') :
    (s.mode = .open ∨ s.mode = .draining) ∧ s' = { s with mode := .closed, parked := false } := by
  unfold closeStep at h
  split at h
  · rename_i hc
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
    exact ⟨hc, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

omit [DecidableEq N] in
/-- Inversion of `terminateNow`. -/
theorem terminateStep_some {s s' : XSt N T} (h : terminateStep s = some s') :
    s.mode ≠ .stopped ∧ s' = { s with mode := .stopped, eq := [], parked := false } := by
  unfold terminateStep at h
  split at h
  · rename_i hc
    simp only [bne_iff_ne, ne_eq] at hc
    exact ⟨hc, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-! ## Outside steps leave the marking, the clocks, the phase and the firings' identities -/

omit [DecidableEq N] in
/-- Updating firing `i`'s record keeps every projection the update keeps. -/
theorem updFiring_map {β : Type} {s : XSt N T} {i : Nat} {h : Firing N T → Firing N T}
    (proj : Firing N T → β) (hh : ∀ g, proj (h g) = proj g) :
    (updFiring s i h).map proj = s.fl.map proj := by
  unfold updFiring
  rw [List.map_map]
  apply List.map_congr_left
  intro g _
  simp only [Function.comp]
  split <;> simp [hh]

/-- An outside step ([CONC-001]) changes neither the marking, nor any clock status, nor the loop
phase, nor which firings are in flight (their identities and transitions). -/
theorem xstepW_outside_frame {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : xstepW P C s l = some s') (ho : l.outside = true) :
    s'.M = s.M ∧ s'.st = s.st ∧ s'.phase = s.phase ∧ s'.fl.map (·.id) = s.fl.map (·.id) ∧
      s'.fl.map (·.t) = s.fl.map (·.t) := by
  cases l with
  | delay δ => cases xstepW_delay h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | write i p x =>
    obtain ⟨f, -, -, rfl⟩ := writeStep_some h
    exact ⟨rfl, rfl, rfl, updFiring_map _ fun _ => rfl, updFiring_map _ fun _ => rfl⟩
  | flush i =>
    obtain ⟨f, -, -, -, -, ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ := flushStep_some h <;>
      exact ⟨rfl, rfl, rfl, updFiring_map _ fun _ => rfl, updFiring_map _ fun _ => rfl⟩
  | ret i ok =>
    obtain ⟨f, -, -, rfl⟩ := retStep_some h
    exact ⟨rfl, rfl, rfl, updFiring_map _ fun _ => rfl, updFiring_map _ fun _ => rfl⟩
  | expire i e =>
    obtain ⟨f, -, -, -, -, -, rfl⟩ := expireStep_some h
    exact ⟨rfl, rfl, rfl, updFiring_map _ fun _ => rfl, updFiring_map _ fun _ => rfl⟩
  | request p x r =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := requestStep_some h <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | drain => obtain ⟨-, rfl⟩ := drainStep_some h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | close => obtain ⟨-, rfl⟩ := closeStep_some h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | terminateNow => obtain ⟨-, rfl⟩ := terminateStep_some h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | _ => simp [XLbl.outside] at ho


/-! ## The clock-status invariant at the phase boundaries (`InvU`)

What the status of a name says about its transition's enablement, in the reference executor
(design section 3, link L3's premise). Clause 3 (a reaped name's transition is enabled) and the
in-flight clause (under `¬reentrant` a name in flight is off, [CONC-002] line 3a, ruling D8 (b))
hold in every reachable state. Clauses 1 and 2 hold at the two phase boundaries, after the update
(phase `deadline`) and after the deadline step (phase `test`): inside a cycle a deposit or a start
changes enablement without touching the statuses, and the next update restores them. The proofs
go through every rule with the per-label inversion lemmas above (`invX_step`). -/

/-- InvU clause 1: an armed name's transition is enabled. -/
def ArmedEnabled (C : Cfg N T) (s : XSt N T) : Prop :=
  ∀ n u, findT C n = some u → (stampOf (s.st n)).isSome = true →
    enabledNA (qCount s.M) u.core = true

/-- InvU clause 2: an off name whose transition is enabled has a firing in flight, and the
executor is not re-entrant. -/
def OffEnabledInFlight (C : Cfg N T) (s : XSt N T) : Prop :=
  ∀ n u, findT C n = some u → s.st n = .off → enabledNA (qCount s.M) u.core = true →
    inFlightN s n = true ∧ C.reentrant = false

/-- InvU clause 3: a reaped name's transition is enabled (glossary: Reaped, "stays enabled"). -/
def ReapedEnabled (C : Cfg N T) (s : XSt N T) : Prop :=
  ∀ n u, findT C n = some u → s.st n = .reaped → enabledNA (qCount s.M) u.core = true

/-- Under `¬reentrant` a name with a firing in flight is off ([CONC-002] line 3a). -/
def InFlightOff (C : Cfg N T) (s : XSt N T) : Prop :=
  C.reentrant = false → ∀ n, inFlightN s n = true → s.st n = .off

/-- **InvU**: the three clauses. -/
def InvU (C : Cfg N T) (s : XSt N T) : Prop :=
  ArmedEnabled C s ∧ OffEnabledInFlight C s ∧ ReapedEnabled C s

/-- The phase boundaries InvU is stated at: after the update, after the deadline step. -/
def isBoundary : Phase → Bool
  | .deadline | .test => true
  | _ => false

/-- The inductive invariant: clause 3 and the in-flight clause everywhere, clauses 1 and 2 at
the boundaries. -/
def InvX (C : Cfg N T) (s : XSt N T) : Prop :=
  ReapedEnabled C s ∧ InFlightOff C s ∧
    (isBoundary s.phase = true → ArmedEnabled C s ∧ OffEnabledInFlight C s)

/-! ### Helper facts -/

omit [DecidableEq N] in
private theorem all_congr' {α : Type} {l : List α} {f g : α → Bool}
    (h : ∀ x ∈ l, f x = g x) : l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons, h a List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

omit [DecidableEq N] in
/-- Enablement reads only the arc places. -/
theorem enabledNA_congr {m m' : N → Nat} {u : Trans N} (h : ∀ p ∈ arcPlaces u, m p = m' p) :
    enabledNA m u.core = enabledNA m' u.core := by
  unfold enabledNA
  rw [all_congr' (l := u.core.inputs) fun x hx => by
        rw [h x.place (by simp only [arcPlaces, List.mem_append, List.mem_map]
                          exact Or.inl (Or.inl (Or.inl ⟨x, hx, rfl⟩)))],
      all_congr' (l := u.core.inhibitors) fun x hx => by
        rw [h x (by simp [arcPlaces, hx])],
      all_congr' (l := u.core.reads) fun x hx => by
        rw [h x (by simp [arcPlaces, hx])]]

/-- A reaped status survives `unreap` only when no arc place was written. -/
theorem unreap_reaped {C : Cfg N T} {ps : List N} {st : String → Status} {n : String}
    (h : unreap C ps st n = .reaped) :
    st n = .reaped ∧ ∀ u, findT C n = some u → ∀ p ∈ arcPlaces u, p ∉ ps := by
  unfold unreap at h
  cases hs : st n <;> cases hf : findT C n <;> simp only [hs, hf] at h
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact ⟨rfl, fun u hu => by simp at hu⟩
  · rename_i u
    refine ⟨rfl, fun u' hu' p hp hps => ?_⟩
    simp only [Option.some.injEq] at hu'
    subst hu'
    have : (arcPlaces u).any (fun p => decide (p ∈ ps)) = true :=
      List.any_eq_true.mpr ⟨p, hp, by simpa using hps⟩
    simp [this] at h

/-- `unreap` keeps an off status. -/
theorem unreap_off {C : Cfg N T} {ps : List N} {st : String → Status} {n : String}
    (h : st n = .off) : unreap C ps st n = .off := by
  unfold unreap
  cases hf : findT C n <;> simp [h]

omit [DecidableEq N] in
/-- A queue marking's count after appending `e`, at a place `e` does not name. -/
theorem qCount_qAppend_of_not_mem [DecidableEq N] {M : QMarking N T} {e : List (N × T)} {p : N}
    (h : p ∉ e.map Prod.fst) : qCount (qAppend M e) p = qCount M p := by
  simp [qCount, qAppend_apply, qEmittedTo_length, List.count_eq_zero_of_not_mem h]

/-- A queue marking's count after appending one token elsewhere. -/
theorem qCount_qAppendOne_of_ne {M : QMarking N T} {p q : N} {x : T} (h : p ≠ q) :
    qCount (qAppendOne M q x) p = qCount M p := by
  simp [qCount, qAppendOne, h]

/-- A start of `t` leaves every queue but its input and reset places as it was. -/
theorem liveAfter_of_not_mem {s : XSt N T} {t : Trans N} {p : N}
    (h : p ∉ inPlaces t ++ t.core.resets) : liveAfter s t p = s.M p := by
  simp only [List.mem_append, not_or] at h
  have hn : nspecAt t.core p = none := by
    unfold nspecAt
    rw [List.find?_eq_none]
    intro x hx hxp
    exact h.1 (by simp only [decide_eq_true_eq] at hxp; subst hxp; exact List.mem_map_of_mem hx)
  simp [liveAfter, qConsume, h.2, qPostInput_of_none hn, vis, hid, List.take_append_drop]

omit [DecidableEq N] in
/-- Which transitions are in flight, read off the firings' transitions. -/
theorem inFlightN_eq_of_map {s s' : XSt N T} (h : s'.fl.map (·.t) = s.fl.map (·.t)) (n : String) :
    inFlightN s' n = inFlightN s n := by
  have e1 : inFlightN s' n = (s'.fl.map (·.t)).any (·.core.name == n) := by
    simp [inFlightN, List.any_map, Function.comp_def]
  have e2 : inFlightN s n = (s.fl.map (·.t)).any (·.core.name == n) := by
    simp [inFlightN, List.any_map, Function.comp_def]
  rw [e1, e2, h]

omit [DecidableEq N] in
/-- The phase a settle step leaves: never a boundary. -/
theorem canSettle_phase {C : Cfg N T} {s : XSt N T} {i : Nat} {f : Firing N T}
    (h : canSettle C s i f = true) : isBoundary (settle s i).phase = false := by
  unfold canSettle settleOk at h
  simp only [Bool.and_eq_true] at h
  have h2 := h.2
  simp only [settle]
  revert h2
  cases s.phase <;> simp [isBoundary]

omit [DecidableEq N] in
/-- Settling removes a firing and adds none. -/
theorem inFlightN_settle {s : XSt N T} {i : Nat} {n : String}
    (h : inFlightN (settle s i) n = true) : inFlightN s n = true := by
  simp only [inFlightN, settle, List.any_eq_true, List.mem_filter] at h ⊢
  obtain ⟨g, ⟨hg, -⟩, hn⟩ := h
  exact ⟨g, hg, hn⟩

/-! ### Preservation -/

omit [DecidableEq N] in
/-- A step that keeps the marking, the statuses and which transitions are in flight, and does not
enter a boundary from outside one, keeps the invariant. -/
theorem invX_frame {C : Cfg N T} {s s' : XSt N T} (hM : s'.M = s.M) (hst : s'.st = s.st)
    (hfl : ∀ n, inFlightN s' n = inFlightN s n)
    (hb : isBoundary s'.phase = true → isBoundary s.phase = true) (hi : InvX C s) :
    InvX C s' := by
  obtain ⟨h3, hf, h12⟩ := hi
  refine ⟨fun n u hu hr => ?_, fun hre n hn => ?_, fun hbd => ?_⟩
  · rw [hM]; rw [hst] at hr; exact h3 n u hu hr
  · rw [hst]; rw [hfl] at hn; exact hf hre n hn
  · obtain ⟨h1, h2⟩ := h12 (hb hbd)
    refine ⟨fun n u hu ha => ?_, fun n u hu ho he => ?_⟩
    · rw [hM]; rw [hst] at ha; exact h1 n u hu ha
    · rw [hst] at ho; rw [hM] at he; rw [hfl]; exact h2 n u hu ho he

omit [DecidableEq N] in
/-- Outside a boundary only the two everywhere-clauses are owed. -/
theorem invX_of_nonBoundary {C : Cfg N T} {s : XSt N T} (hb : isBoundary s.phase = false)
    (h3 : ReapedEnabled C s) (hf : InFlightOff C s) : InvX C s :=
  ⟨h3, hf, fun h => by simp [hb] at h⟩

/-- A write of the places `ps` (a deposit, an injection, a start) keeps clause 3 when every count
it changes is at a place of `ps` and every status it leaves reaped was reaped. -/
theorem reapedEnabled_write {C : Cfg N T} {s s' : XSt N T} (ps : List N) (st₀ : String → Status)
    (hi : ReapedEnabled C s) (hst : s'.st = unreap C ps st₀)
    (h0 : ∀ n, st₀ n = .reaped → s.st n = .reaped)
    (hM : ∀ p, p ∉ ps → qCount s'.M p = qCount s.M p) : ReapedEnabled C s' := by
  intro n u hu hr
  rw [hst] at hr
  obtain ⟨h1, h2⟩ := unreap_reaped hr
  rw [enabledNA_congr (m' := qCount s.M) fun p hp => hM p (h2 u hu p hp)]
  exact hi n u hu (h0 n h1)

/-- The deposit of a settle step keeps the invariant. -/
theorem invX_depositAt {C : Cfg N T} {s : XSt N T} {i : Nat} {f : Firing N T}
    {e : List (N × T)} (hc : canSettle C s i f = true) (hi : InvX C s) :
    InvX C (depositAt C s i e) := by
  refine invX_of_nonBoundary (canSettle_phase hc)
    (reapedEnabled_write (e.map Prod.fst) s.st hi.1 rfl (fun _ h => h)
      fun p hp => qCount_qAppend_of_not_mem hp) fun hre n hn => ?_
  exact unreap_off (hi.2.1 hre n (inFlightN_settle hn))

omit [DecidableEq N] in
/-- A settle step without a deposit keeps the invariant. -/
theorem invX_settle {C : Cfg N T} {s : XSt N T} {i : Nat} {f : Firing N T}
    (hc : canSettle C s i f = true) (hi : InvX C s) : InvX C (settle s i) :=
  invX_of_nonBoundary (canSettle_phase hc) (fun n u hu hr => hi.1 n u hu hr)
    fun hre n hn => hi.2.1 hre n (inFlightN_settle hn)

/-- The status after a start reaped only where it was reaped. -/
theorem afterStart_reaped {P : XPol N T} {C : Cfg N T} {s : XSt N T} {t : Trans N} {n : String}
    (h : afterStart P C s t n = .reaped) : s.st n = .reaped := by
  unfold afterStart at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · split at h <;> exact absurd h (by simp)
    · assumption

/-- A start keeps an off status of another name. -/
theorem afterStart_off {P : XPol N T} {C : Cfg N T} {s : XSt N T} {t : Trans N} {n : String}
    (h : s.st n = .off) : afterStart P C s t n = .off := by
  unfold afterStart
  split
  · rfl
  · simp [h]

/-- The update of the reference: what a status it leaves says about enablement. -/
theorem updSt_ref {C : Cfg N T} {s : XSt N T} {n : String} {u : Trans N}
    (hf : findT C n = some u) :
    (updSt refXPol C s n = .reaped → s.st n = .reaped) ∧
    ((stampOf (updSt refXPol C s n)).isSome = true → enabledNA (qCount s.M) u.core = true) ∧
    (updSt refXPol C s n = .off → enabledNA (qCount s.M) u.core = true →
      inFlightN s n = true ∧ C.reentrant = false) ∧
    (s.st n = .off → C.reentrant = false → inFlightN s n = true →
      updSt refXPol C s n = .off) := by
  unfold updSt
  simp only [hf, refXPol]
  cases hs : s.st n with
  | off =>
    by_cases he : enabledNA (qCount s.M) u.core = true <;>
      cases hr : C.reentrant <;> cases hfl : inFlightN s n <;> simp [he, stampOf]
  | armed k rs =>
    by_cases he : enabledNA (qCount s.M) u.core = true <;> cases rs <;> simp [he, stampOf]
  | reaped => simp [stampOf]

omit [DecidableEq N] in
/-- The names a deadline step reaps are armed, hence enabled. -/
theorem mem_expiredNames {P : XPol N T} {C : Cfg N T} {s : XSt N T} {n : String}
    (h : n ∈ expiredNames P C s) :
    ∃ u ∈ C.X.net.transitions, u.core.name = n ∧ enabledNA (qCount s.M) u.core = true ∧
      (stampOf (s.st n)).isSome = true := by
  simp only [expiredNames, List.mem_map, List.mem_filter] at h
  obtain ⟨u, ⟨hu, hx⟩, rfl⟩ := h
  simp only [expiredAt, Bool.and_eq_true, TSt.armed, viewAt] at hx
  exact ⟨u, hu, rfl, hx.1.2.1, hx.1.2.2⟩

/-- Every step of the reference executor keeps the invariant (distinct names: the deadline step
reaps by name). -/
theorem invX_step {C : Cfg N T} (hN : NamesDistinct C.X) {s s' : XSt N T} {l : XLbl N T}
    (h : xstep C s l = some s') (hi : InvX C s) : InvX C s' := by
  by_cases ho : l.outside = true
  · obtain ⟨hM, hst, hph, -, ht⟩ := xstepW_outside_frame h ho
    exact invX_frame hM hst (inFlightN_eq_of_map ht) (by rw [hph]; exact id) hi
  cases l with
  | delay | write | flush | ret | expire | request | drain | close | terminateNow =>
    simp [XLbl.outside] at ho
  | commit i =>
    obtain ⟨f, e, -, -, hc, -, -, rfl⟩ := commitStep_some h
    exact invX_depositAt hc hi
  | fail i =>
    obtain ⟨f, -, hc, -, rfl⟩ := failStep_some h
    exact invX_settle hc hi
  | tdeposit i =>
    obtain ⟨f, e, -, -, hc, -, rfl⟩ := tdepositStep_some h
    exact invX_depositAt hc hi
  | endCompletions =>
    obtain ⟨-, -, -, -, rfl⟩ := xstepW_endCompletions h
    exact invX_frame (s := s) rfl rfl (fun _ => rfl) (by simp [isBoundary]) hi
  | publish i =>
    obtain ⟨b, rest, -, -, hph, rfl⟩ := publishStep_some h
    refine invX_of_nonBoundary ?_ (reapedEnabled_write (b.map Prod.fst) s.st hi.1 rfl
      (fun _ h => h) fun p hp => qCount_qAppend_of_not_mem hp) fun hre n hn => ?_
    · rcases hph with hp | ⟨hp, -⟩ <;> simp [hp, isBoundary]
    · exact unreap_off (hi.2.1 hre n hn)
  | endPublications =>
    obtain ⟨-, -, -, rfl⟩ := xstepW_endPublications h
    exact invX_frame (s := s) rfl rfl (fun _ => rfl) (by simp [isBoundary]) hi
  | inject k =>
    obtain ⟨p, x, rest, -, -, -, hph, rfl⟩ := injectStep_some h
    refine invX_of_nonBoundary ?_ (reapedEnabled_write [p] s.st hi.1 rfl
      (fun _ h => h) fun q hq => qCount_qAppendOne_of_ne (by simpa using hq)) fun hre n hn => ?_
    · rcases hph with hp | hp <;> simp [hp, isBoundary]
    · exact unreap_off (hi.2.1 hre n hn)
  | discard k =>
    obtain ⟨p, x, rest, -, -, -, hph, rfl⟩ := discardStep_some h
    exact invX_frame (s := s) rfl rfl (fun _ => rfl)
      (by rcases hph with hp | hp <;> simp [hp, isBoundary]) hi
  | snapshot a =>
    obtain ⟨-, -, -, rfl⟩ := snapshotStep_some h
    exact hi
  | endEvents =>
    obtain ⟨-, -, -, rfl⟩ := xstepW_endEvents h
    exact invX_frame (s := s) rfl rfl (fun _ => rfl) (by simp [isBoundary]) hi
  | update =>
    obtain ⟨-, -, rfl⟩ := xstepW_update h
    refine ⟨fun n u hu hr => ?_, fun hre n hn => ?_, fun _ => ⟨fun n u hu ha => ?_,
      fun n u hu ho he => ?_⟩⟩
    · exact hi.1 n u hu ((updSt_ref hu).1 hr)
    · show updSt refXPol C s n = .off
      cases hf : findT C n with
      | none => unfold updSt; simp [hf]
      | some u => exact (updSt_ref hf).2.2.2 (hi.2.1 hre n hn) hre hn
    · exact (updSt_ref (s := s) hu).2.1 ha
    · exact (updSt_ref (s := s) hu).2.2.1 ho he
  | deadline ns =>
    obtain ⟨hph, -, hns, rfl⟩ := xstepW_deadline h
    obtain ⟨h3, hf, h12⟩ := hi
    obtain ⟨h1, h2⟩ := h12 (by simp [hph, isBoundary])
    have hst : ∀ n, ((if ns.contains n = true then Status.reaped else s.st n) = .reaped ∧
        n ∈ ns) ∨ ((if ns.contains n = true then Status.reaped else s.st n) = s.st n ∧
        n ∉ ns) := by
      intro n; by_cases hc : n ∈ ns <;> simp [hc]
    refine ⟨fun n u hu hr => ?_, fun hre n hn => ?_, fun _ => ⟨fun n u hu ha => ?_,
      fun n u hu ho he => ?_⟩⟩
    · change (if ns.contains n = true then Status.reaped else s.st n) = .reaped at hr
      change enabledNA (qCount s.M) u.core = true
      rcases hst n with ⟨-, hc⟩ | ⟨he, -⟩
      · subst hns
        obtain ⟨u', hu', hn', he', -⟩ := mem_expiredNames hc
        have hin : InNet C.X u' := (inNet_iff_mem hN u').mpr hu'
        unfold InNet at hin
        unfold findT at hu
        rw [← hn', hin] at hu
        cases hu
        exact he'
      · rw [he] at hr
        exact h3 n u hu hr
    · change (if ns.contains n = true then Status.reaped else s.st n) = .off
      have hoff := hf hre n hn
      rcases hst n with ⟨-, hc⟩ | ⟨he, -⟩
      · subst hns
        obtain ⟨u', -, -, -, hs⟩ := mem_expiredNames hc
        simp [hoff, stampOf, atDeadline] at hs
      · rw [he]; exact hoff
    · change (stampOf (if ns.contains n = true then Status.reaped else s.st n)).isSome = true
        at ha
      rcases hst n with ⟨he', -⟩ | ⟨he', -⟩
      · rw [he'] at ha; simp [stampOf] at ha
      · rw [he'] at ha; exact h1 n u hu ha
    · change (if ns.contains n = true then Status.reaped else s.st n) = .off at ho
      rcases hst n with ⟨he', -⟩ | ⟨he', -⟩
      · rw [he'] at ho; cases ho
      · rw [he'] at ho; exact h2 n u hu ho he
  | finish c =>
    cases c with
    | quiescent =>
      obtain ⟨-, -, -, rfl⟩ := xstepW_finishQuiescent h
      exact invX_frame (s := s) rfl rfl (fun _ => rfl) (by simp [isBoundary]) hi
    | closed =>
      obtain ⟨-, -, -, -, rfl⟩ := xstepW_finishClosed h
      exact invX_frame (s := s) rfl rfl (fun _ => rfl) (by simp [isBoundary]) hi
    | terminal =>
      obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h
      exact invX_frame (s := s) rfl rfl (fun _ => rfl) (by simp [isBoundary]) hi
    | stopped =>
      obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h
      exact invX_frame (s := s) rfl rfl (fun _ => rfl) (by simp [isBoundary]) hi
  | begin =>
    obtain ⟨-, -, -, -, rfl⟩ := xstepW_begin h
    exact invX_frame (s := s) rfl rfl (fun _ => rfl) (by simp [isBoundary]) hi
  | start n sy =>
    obtain ⟨t, rest, -, hph, -, -, hn, -, -, rfl⟩ := startStep_some h
    refine invX_of_nonBoundary (by simp [hph, isBoundary])
      (reapedEnabled_write (inPlaces t ++ t.core.resets) (afterStart refXPol C s t) hi.1 rfl
        (fun _ h => afterStart_reaped h) fun p hp => by
          simp only [qCount]; rw [liveAfter_of_not_mem hp]) fun hre m hm => ?_
    apply unreap_off
    simp only [inFlightN, List.any_append, List.any_cons, List.any_nil, Bool.or_false,
      Bool.or_eq_true, beq_iff_eq] at hm
    rcases hm with hm | hm
    · exact afterStart_off (hi.2.1 hre m hm)
    · unfold afterStart; simp [hm]
  | lose n =>
    obtain ⟨t, rest, -, hph, -, -, -, -, rfl⟩ := loseStep_some h
    refine invX_of_nonBoundary (by simp [hph, isBoundary]) (fun m u hu hr => ?_)
      fun hre m hm => ?_
    · by_cases hmn : m = n
      · simp [hmn] at hr
      · simp only [hmn, ite_false] at hr
        exact hi.1 m u hu hr
    · show (if m = n then Status.off else s.st m) = .off
      split
      · rfl
      · exact hi.2.1 hre m hm
  | endPass =>
    obtain ⟨-, -, -, -, rfl⟩ := xstepW_endPass h
    exact invX_frame (s := s) rfl rfl (fun _ => rfl) (by split <;> simp [isBoundary]) hi
  | park tmr =>
    obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := parkStep_some h
    exact invX_frame (s := s) rfl rfl (fun _ => rfl) (fun h => h) hi
  | wake =>
    obtain ⟨-, -, rfl⟩ := wakeStep_some h
    exact invX_frame (s := s) rfl rfl (fun _ => rfl) (by simp [isBoundary]) hi

omit [DecidableEq N] in
/-- The initial state meets the invariant: every name is off, nothing is in flight, the phase is
step 1. -/
theorem invX_xinit (C : Cfg N T) (M0 : QMarking N T) (r0 : Nat) : InvX C (xinit M0 r0) :=
  ⟨fun _ _ _ hr => by simp [xinit] at hr, fun _ _ hn => by simp [xinit, inFlightN] at hn,
   fun hb => by simp [xinit, isBoundary] at hb⟩

/-- Every run of the reference executor keeps the invariant. -/
theorem invX_xrun {C : Cfg N T} (hN : NamesDistinct C.X) :
    ∀ {s s' : XSt N T} {ls : List (XLbl N T)}, xrun C s ls = some s' → InvX C s → InvX C s'
  | s, s', [], h, hi => by cases h; exact hi
  | s, s', l :: ls, h, hi => by
    simp only [xrun] at h
    cases hs : xstep C s l with
    | none => simp [hs] at h
    | some s₁ =>
      simp only [hs, Option.bind_some] at h
      exact invX_xrun hN h (invX_step hN hs hi)

/-- **InvU at the phase boundaries**: in every state a run of the reference executor reaches from
an initial state, with distinct transition names, after the update and after the deadline step,
an armed name's transition is enabled, an off name's enabled transition is in flight under
`¬reentrant`, and a reaped name's transition is enabled. -/
theorem invU_boundary {C : Cfg N T} (hN : NamesDistinct C.X) {M0 : QMarking N T} {r0 : Nat}
    {ls : List (XLbl N T)} {s : XSt N T} (h : xrun C (xinit M0 r0) ls = some s)
    (hb : s.phase = .deadline ∨ s.phase = .test) : InvU C s := by
  obtain ⟨h3, -, h12⟩ := invX_xrun hN h (invX_xinit C M0 r0)
  obtain ⟨h1, h2⟩ := h12 (by rcases hb with hb | hb <;> simp [hb, isBoundary])
  exact ⟨h1, h2, h3⟩

/-- In every reachable state a reaped name's transition is enabled. -/
theorem reapedEnabled_reachable {C : Cfg N T} (hN : NamesDistinct C.X) {M0 : QMarking N T}
    {r0 : Nat} {ls : List (XLbl N T)} {s : XSt N T} (h : xrun C (xinit M0 r0) ls = some s) :
    ReapedEnabled C s :=
  (invX_xrun hN h (invX_xinit C M0 r0)).1

/-- In every reachable state of a non-re-entrant executor a name with a firing in flight is off
([CONC-002] line 3a, ruling D8 (b)). -/
theorem inFlightOff_reachable {C : Cfg N T} (hN : NamesDistinct C.X) {M0 : QMarking N T}
    {r0 : Nat} {ls : List (XLbl N T)} {s : XSt N T} (h : xrun C (xinit M0 r0) ls = some s) :
    InFlightOff C s :=
  (invX_xrun hN h (invX_xinit C M0 r0)).2.1

/-! ## Runs as traces -/

/-- The trace of steps of a run of the reference executor, if every label is a step: the bridge
from a decided label run (`xrun`) to the step traces the trace forms of Ears read. -/
def xtrace (C : Cfg N T) : XSt N T → List (XLbl N T) → Option (List (XStep N T))
  | _, [] => some []
  | s, l :: ls => (xstep C s l).bind fun s' => (xtrace C s' ls).map ((s, l, s') :: ·)

/-- A trace `xtrace` builds is a run of the reference executor. -/
theorem xtrace_run {C : Cfg N T} :
    ∀ {s : XSt N T} {ls : List (XLbl N T)} {tr : List (XStep N T)},
      xtrace C s ls = some tr → XRun RefExec C s tr
  | s, [], tr, h => by cases h; trivial
  | s, l :: ls, tr, h => by
    simp only [xtrace] at h
    cases hs : xstep C s l with
    | none => simp [hs] at h
    | some s' =>
      simp only [hs, Option.bind_some] at h
      cases ht : xtrace C s' ls with
      | none => simp [ht] at h
      | some tr' =>
        simp only [ht, Option.map_some, Option.some.injEq] at h
        subst h
        exact ⟨rfl, hs, xtrace_run ht⟩

/-- The trace ends where the run ends. -/
theorem xtrace_last {C : Cfg N T} :
    ∀ {s : XSt N T} {ls : List (XLbl N T)} {tr : List (XStep N T)},
      xtrace C s ls = some tr → xrun C s ls = some (XRun.last s tr)
  | s, [], tr, h => by cases h; rfl
  | s, l :: ls, tr, h => by
    simp only [xtrace] at h
    cases hs : xstep C s l with
    | none => simp [hs] at h
    | some s' =>
      simp only [hs, Option.bind_some] at h
      cases ht : xtrace C s' ls with
      | none => simp [ht] at h
      | some tr' =>
        simp only [ht, Option.map_some, Option.some.injEq] at h
        subst h
        simp only [xrun, hs, Option.bind_some, xtrace_last ht]
        cases tr' with
        | nil => rfl
        | cons x xs => simp [XRun.last, List.getLast?_cons]


/-! ## Decided runs -/

omit [DecidableEq N] in
/-- Read a decided fact off a run prefix `o` and one more step `g C s l`: if the check `p` of
the step's source and target evaluates to `true`, both states exist. -/
theorem step_of_check (g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)) {C : Cfg N T}
    {o : Option (XSt N T)} {l : XLbl N T} {p : XSt N T → XSt N T → Bool}
    (h : (o.bind fun s => (g C s l).map (p s)) = some true) :
    ∃ s s', o = some s ∧ g C s l = some s' ∧ p s s' = true := by
  cases ho : o with
  | none => simp [ho] at h
  | some s =>
    cases hg : g C s l with
    | none => simp [ho, hg] at h
    | some s' => simp only [ho, hg, Option.bind_some, Option.map_some, Option.some.injEq] at h
                 exact ⟨s, s', rfl, hg, h⟩

end Libpetri.Reference
