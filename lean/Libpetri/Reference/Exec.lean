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

**Wave 0 (tracer) rules.** Outside: `delay`, `write`, `flush`, `ret`, `expire`. Step 1:
`commit`, `fail`, `tdeposit`, `endCompletions`. Step 1b: `publish`, `endPublications`. Step 2's
end `endEvents`. Steps 3 and 4: `update`, `deadline`. The termination test: the three
`finish` causes and `begin`. Step 5: `start`, `lose`, `endPass`. The labels `inject`,
`discard`, `snapshot`, `request`, `drain`, `close`, `park` and `wake` are fixed in the label type
but have no rule yet (`none`); wave 1 adds them.

**Rust correspondence** (`executor.rs`, async loop `run_async`):

* `commit`, `fail`, `tdeposit` in phase `completions`: `handle_completion` (1248-1345), called in
  Phase 1 (1044-1048) while no terminal place is marked. Validation reads the returned outputs
  and `flushed_places` (`output_conforms`, 674-704, called at 1266-1270); the timeout path skips
  validation and still runs the relay check (1261-1299, ruling D24 (a)); a violation or a relay
  rejection deposits nothing (`return`), an error result emits TransitionFailed (1331-1339).
* `commit`, `fail` inside the pass for a synchronous firing: `fire_transition_async`'s sync branch
  (1491-1572), the same checks inline; a synchronous firing has no timeout race.
* `publish`: Phase 1b, `handle_flush` (1347-1365), unconditional, FIFO on one channel.
* `update`: Phase 3 at `cycle_now` (1063-1065); `deadline`: Phase 4 at the same reading
  (1067-1083); `finish`: the termination checks (1085-1095) and the terminal check at the top of
  the loop (1035-1042).
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
callback, executor.rs 1640-1670). -/
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
whose flushed batch failed the relay check ends with an error (executor.rs 1711-1715). -/
def retStep (s : XSt N T) (i : Nat) (ok : Bool) : Option (XSt N T) :=
  onOpen s i fun _ =>
    { s with cq := s.cq ++ [i], parked := false,
             fl := updFiring s i fun g =>
               { g with out := some (if ok && !g.relayBad then .ok g.buf else .err) } }

/-- `expire i e`: the budget of an asynchronous firing with a `Timeout` node expires first, with
timeout outcome `e`. A firing whose flushed batch failed the relay check ends with an error here
too: the slot is read after the `select!` (executor.rs 1711-1715). -/
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
    if j == i && liveB C s && (s.phase = .publications || s.phase = .await) then
      some { s with M := qAppend s.M b, st := unreap C (b.map Prod.fst) s.st, pq := rest,
                    phase := if s.phase = .await then .completions else s.phase,
                    parked := false }
    else none
  | [] => none

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
  -- step 1
  | .commit i => commitStep P C s i
  | .fail i => failStep P C s i
  | .tdeposit i => tdepositStep C s i
  | .endCompletions =>
      if s.phase = .completions && liveB C s && s.cq.isEmpty then
        some { s with phase := .publications } else none
  -- step 1b
  | .publish i => publishStep C s i
  | .endPublications =>
      if s.phase = .publications && liveB C s && s.pq.isEmpty then
        some { s with phase := .events } else none
  -- step 2 (its injection rules are wave 1)
  | .endEvents =>
      if s.phase = .events && liveB C s && s.eq.isEmpty then
        some { s with phase := .update } else none
  -- step 3: one reading, shared with steps 4 and 5 (R-EXEC-3)
  | .update =>
      if s.phase = .update && liveB C s then
        some { s with cyc := s.now, st := updSt P C s, phase := .deadline } else none
  -- step 4: reap every expired name at the cycle reading (equality, not inclusion)
  | .deadline ns =>
      if s.phase = .deadline && liveB C s && ns == expiredNames P C s then
        some { s with st := fun n => if ns.contains n then .reaped else s.st n, phase := .test }
      else none
  -- the termination test
  | .finish .quiescent =>
      if s.phase = .test && liveB C s && finishQ C s then
        some { s with phase := .done .quiescent, eq := [] } else none
  | .finish .closed =>
      if s.phase = .test && liveB C s && s.mode = .closed && s.fl.isEmpty then
        some { s with phase := .done .closed, eq := [] } else none
  | .finish .terminal =>
      if isExecPhase s.phase && !liveB C s then
        some { s with phase := .done .terminal, eq := [], pq := [] } else none
  | .begin =>
      if s.phase = .test && liveB C s && !finishQ C s && !(s.mode = .closed && s.fl.isEmpty) then
        some { s with phase := .pass, order := readyOrder C s, delta := fun _ => 0,
                      started := false }
      else none
  -- step 5
  | .start n sy => startStep P C s n sy
  | .lose n => loseStep P C s n
  | .endPass =>
      if s.phase = .pass && liveB C s && s.order.isEmpty && passFree s then
        some { s with phase := if s.started then .completions else .await } else none
  -- fixed labels whose rules come in wave 1
  | .inject _ | .discard _ | .snapshot _ | .request _ _ _ | .drain | .close | .park _ | .wake =>
      none

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
