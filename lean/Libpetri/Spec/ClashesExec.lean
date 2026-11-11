import Libpetri.Spec.Req.EXEC_021

set_option linter.missingDocs true

/-!
# Clashes of the execution, concurrency and environment slice, over `RefExec`

The confirmed clashes of plan section 6 that name a conflict, an ambiguity or a run as their
evidence, stated over the reference executor of `Reference/Exec.lean`. Every ruling is decided
(plan section 5, accepted 2026-11-10); each theorem below records the evidence for the decided
reading, never a reading the user rejected.

A candidate reading is a plain definition over an abstract executor `E : XRel N T`, not a
requirement block (as in `ClashesTime.lean`): the registry's `conflict` and `ambiguity` roles name
requirement blocks only, so the evidence is a citation of the spec ID whose text has the two
readings. Where a block exists (EXEC-021), the conflict is a theorem over every executor.

| Clash | Ruling | Evidence here |
|---|---|---|
| refexec R1 / NR-3 (EXEC-001 line 1) | D70 (a) | `clashExec_naiveLine1`: the literal 'no start after a deposit until the next update' fails on the reference run `cxRunPass`, where a synchronous firing is admitted inside its pass and the pass goes on; the ruled trigger 'a deposit made outside a firing pass' holds there |
| exec#18, env-a#8 (R-EXEC-9, strict step order) | D70 (a) | `clashExec_strictOrder`: an injection processed by the wait itself (Rust) is a reference step; an update still follows it before any start |
| exec#5 (R-EXEC-3, readings per cycle) | D61 (c) | `clashExec_twoReadings`: a start whose host reading is past latest plus tolerance, of a transition that was not expired at the deadline step's reading |
| refexec R8 / NR-5 (CONC-010 park) | D61 (c) | `clashExec_parkAtCycle`: the wait parks while a transition is Ready at the host's present reading, because nothing is due at the cycle reading |
| exec#4 (R-EXEC-2, timeout outcome validated) | D24 (a) | `clashExec_timeoutValidated_conflict`: no executor meets EXEC-021 and fails every timed-out firing whose outcome the output spec rejects (the Java and TypeScript behaviour, an executor defect under D24 (a)) |
| env-b#1 (ENVB-R2, start after close) | D85 (a) | `clashExec_closeKeepsStarting`: after a close the reference begins a new cycle and starts a transition while a firing is in flight |
| env-a#5 (ENV-004, when 'closed or draining' is tested) | D20 (no ruling) | `clashExec_env004_ambiguity`: refused at the call holds of the reference; refused at processing fails (an event accepted before a drain is injected while draining) |
| env-a#7 (ENV-003 AC3 against the ENV-013 discard line) | D20 (no ruling) | `clashExec_env003_conflict`: the reference never injects once closing, and an ideal run accepts an event that it then discards |
| env-b#5, exec#21 (quiescence: 'enabled' or 'armed') | D5, D20 | `clashExec_quiescentArmed`: the reference finishes quiescent with a reaped transition still enabled; it never finishes with one armed |
| env-b#3 (ENV-010 unconditional) | D73 (a) | `clashExec_env010_guard`: an executor with environment places finishes only once it no longer accepts injections; the unconditional reading fails after a drain |
| exec#11 (cause of a close at rest) | D53 (c) | `clashExec_closedRest_bothCauses`: at a closed rest the reference offers both `finish quiescent` and `finish closed` |

The other confirmed clashes of the slice carry no theorem here: they are wording edits (D20), or
their evidence is a line of a requirement block (refexec R10 / NR-4 is `EXEC_021`'s
`exec021_runAB`; exec#15 is EXEC_031's line 1; exec#14 and exec#17 are EXEC_040's assumes and
test point), or they belong to a block of a later sub-wave (exec#1 to exec#3 to EXEC-022,
conc-b#9 and conc-b#11 to CONC-010, env-a#1, env-a#2, env-a#6 and env-b#2 to the ENV blocks,
refexec R9 to the CONC-005 companion).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Novel.TimedScg (Timing)

namespace ClashExec

variable {N T : Type}

/-! ## Step predicates and decided runs -/

/-- The step deposits into the marking: a settle with a deposit, a publication or an injection. -/
def isDeposit (e : XStep N T) : Bool :=
  match e.2.1 with
  | .commit _ | .tdeposit _ | .publish _ | .inject _ => true
  | _ => false

/-- The step is a caller's close. -/
def isClose (e : XStep N T) : Bool :=
  match e.2.1 with
  | .close => true
  | _ => false

/-- The step injects the event with ticket `k`. -/
def injectsTicket (k : Nat) (e : XStep N T) : Bool :=
  match e.2.1 with
  | .inject j => j == k
  | _ => false

/-- A decided fact about an optional state yields the state. -/
theorem some_of_map {o : Option (XSt N T)} {q : XSt N T → Bool} (h : o.map q = some true) :
    ∃ s, o = some s ∧ q s = true := by
  cases o with
  | none => simp at h
  | some s => exact ⟨s, rfl, by simpa using h⟩

variable [DecidableEq N]

/-- Read a decided fact `q` off the reference run from `s` with labels `ls`. -/
theorem run_of_check {C : Cfg N T} {s : XSt N T} {ls : List (XLbl N T)}
    {q : List (XStep N T) → Bool} (h : (xtrace C s ls).map q = some true) :
    ∃ tr, XRun RefExec C s tr ∧ q tr = true := by
  cases ht : xtrace C s ls with
  | none => simp [ht] at h
  | some tr =>
    simp only [ht, Option.map_some, Option.some.injEq] at h
    exact ⟨tr, xtrace_run ht, h⟩

end ClashExec

open ClashExec

/-! ## The nets of the examples -/

/-- A transition without an output spec: name, input places (one token each), inhibitor places. -/
def cxT (n : String) (ins inh : List Nat) : Trans Nat :=
  { core := { name := n, inputs := ins.map (⟨·, .one⟩), inhibitors := inh, reads := [],
              resets := [] },
    out := none }

/-- The configuration of the examples: transitions `ts` with timing `tm`, environment places
`envs`, one priority, no terminal place, every output accepted, not re-entrant. -/
def cxCfg (ts : List (Trans Nat)) (tm : Trans Nat → Timing) (envs : List Nat) : Cfg Nat Nat :=
  { X := { net := { places := [0, 1, 2], transitions := ts }, timing := tm, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := envs, reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => false,
    res := 0 }

/-- The marking with token `7` in place `0` and token `9` in place `2`. -/
def cxM : QMarking Nat Nat := fun p => if p = 0 then [7] else if p = 2 then [9] else []

/-- The empty marking. -/
def cxM0 : QMarking Nat Nat := fun _ => []

/-- Steps 1 to 4 of a cycle with nothing to settle, publish, inject or reap. -/
def cxQuiet : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline []]

/-- A net with no transition and environment place `0`. -/
def cxCfgEnv : Cfg Nat Nat := cxCfg [] (fun _ => .immediate) [0]

/-! ## EXEC-001 line 1: a deposit inside the pass (refexec R1, NR-3, ruling D70 (a)) -/

/-- `a`: one token from `0`; its action writes to `1`. -/
def cxA : Trans Nat := cxT "a" [0] []

/-- `b`: one token from `2`, inhibited by place `1`. -/
def cxB : Trans Nat := cxT "b" [2] [1]

/-- The net of `a` and `b`, both `Immediate`. -/
def cxCfgPass : Cfg Nat Nat := cxCfg [cxA, cxB] (fun _ => .immediate) []

/-- **The run `runPass`** of the design spike: `a` starts synchronously, its action writes `8` to
place `1` and returns, the pass admits it (a deposit inside the pass that marks `b`'s inhibitor
place), and the pass goes on to start `b`, which the pass-visible marking still enables. -/
def cxRunPass : List (XLbl Nat Nat) :=
  cxQuiet ++ [.begin, .start "a" true, .write 0 1 8, .ret 0 true, .commit 0, .start "b" false,
    .endPass]

/-- **Candidate reading of EXEC-001's 'No transition fires before completions are processed'**
over every deposit (not a requirement block): after any deposit, no transition starts before the
next enablement update. -/
def ExecNaiveLine1 (E : XRel Nat Nat) : Prop :=
  ∀ C s0 tr, XRun E C s0 tr → AfterUntilNever isDeposit isUpdate isStart tr

/-- **The reading of ruling D70 (a)** (design NR-3): the trigger is a deposit made outside a firing
pass. It is the deposit trigger of EXEC_001's first two lines. -/
def ExecRuledLine1 (E : XRel Nat Nat) : Prop :=
  ∀ C s0 tr, XRun E C s0 tr →
    AfterUntilNever (fun e => isDeposit e && e.1.phase != .pass) isUpdate isStart tr

/-- ✗ The literal reading of EXEC-001's line 'No transition fires before completions are
processed', read over every deposit, is false of the reference executor: on `cxRunPass` the pass
admits `a`'s synchronous completion and then starts `b` with no update in between (Rust keeps
looping over the pass after an inline commit, executor_core/executor.rs Phase 5). On the same run the ruled
reading (a deposit made outside a firing pass) holds. -/
@[evidence cites "EXEC-001" "line 1 reads 'since the last deposit made outside a firing pass' (ruling D70 (a), design NR-3): on the reference run runPass a synchronous firing is admitted inside its pass and a later transition of the same pass starts with no enablement update in between, so the literal reading over every deposit fails while the ruled reading holds on that run"]
theorem clashExec_naiveLine1 :
    (∃ tr, XRun RefExec cxCfgPass (xinit cxM 0) tr ∧
      ¬ AfterUntilNever isDeposit isUpdate isStart tr ∧
      AfterUntilNever (fun e => isDeposit e && e.1.phase != .pass) isUpdate isStart tr) ∧
    ¬ ExecNaiveLine1 RefExec := by
  obtain ⟨tr, hr, hq⟩ := run_of_check (C := cxCfgPass) (s := xinit cxM 0) (ls := cxRunPass)
    (q := fun tr => !decide (AfterUntilNever isDeposit isUpdate isStart tr) &&
      decide (AfterUntilNever (fun e => isDeposit e && e.1.phase != .pass) isUpdate isStart tr))
    (by decide +kernel)
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq] at hq
  exact ⟨⟨tr, hr, hq.1, hq.2⟩, fun h => hq.1 (h _ _ _ hr)⟩

/-! ## The strict step order (R-EXEC-9, ruling D70 (a)) -/

/-- **Candidate reading of EXEC-001 AC1 as a strict step order** (not a requirement block): no
deposit is made by the wait itself; completions, publications and events are processed only in
steps 1, 1b and 2 of a cycle (or inside the pass for a synchronous firing). -/
def ExecStrictOrder (E : XRel Nat Nat) : Prop :=
  ∀ C s0 tr, XRun E C s0 tr → ∀ e ∈ tr, isDeposit e = true → e.1.phase ≠ .await

/-- The run of the wait that processes its own wake-up item: a quiet cycle with nothing ready, the
loop parks, a caller's request for place `0` is accepted and wakes it, the wait injects the event,
and the next cycle runs up to its update. -/
def cxRunWake : List (XLbl Nat Nat) :=
  cxQuiet ++ [.begin, .endPass, .park none, .request 0 5 .accepted, .inject 0, .endCompletions,
    .endPublications, .endEvents, .update]

/-- The step is an injection made by the wait. -/
def cxInjectInWait (e : XStep Nat Nat) : Bool := isDeposit e && e.1.phase == .await

/-- ✗ The strict step order is false of the reference executor: on `cxRunWake` the wait injects
the event that woke it before the next cycle's step 1 (Rust's wait processes the item that ends
it). An enablement update still follows the injection before any start, which is the order every
runtime keeps (EXEC-001 AC3). -/
@[evidence cites "EXEC-001" "AC1 does not fix a strict order of labels per cycle (ruling D70 (a), R-EXEC-9): on the reference run in which the parked wait is woken by an accepted request, the wait injects the event itself, before the next cycle's completions, and the next enablement update still comes before any start"]
theorem clashExec_strictOrder :
    (∃ tr, XRun RefExec cxCfgEnv (xinit cxM0 0) tr ∧ tr.any cxInjectInWait = true ∧
      AfterUntilNever isDeposit isUpdate isStart tr) ∧
    ¬ ExecStrictOrder RefExec := by
  obtain ⟨tr, hr, hq⟩ := run_of_check (C := cxCfgEnv) (s := xinit cxM0 0) (ls := cxRunWake)
    (q := fun tr => tr.any cxInjectInWait && decide (AfterUntilNever isDeposit isUpdate isStart tr))
    (by decide +kernel)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
  refine ⟨⟨tr, hr, hq.1, hq.2⟩, fun h => ?_⟩
  obtain ⟨e, he, hw⟩ := List.any_eq_true.mp hq.1
  simp only [cxInjectInWait, Bool.and_eq_true, beq_iff_eq] at hw
  exact h _ _ _ hr e he hw.1 hw.2

/-! ## Readings per cycle (R-EXEC-3, ruling D61 (c)) -/

/-- `u`: one token from `0`. -/
def cxU : Trans Nat := cxT "u" [0] []

/-- The net of `u` alone, `Window(3, 5)`, tolerance `0`. -/
def cxCfgW : Cfg Nat Nat := cxCfg [cxU] (fun _ => .window 3 5) []

/-- The run up to the start of `u` with two readings: `u` is armed at `0` and not ready; the
clock reads `4` at the next update, where `u` is ready and not expired, so the pass offers it;
the host clock then advances to `7` before the pass reaches `u` (Java reads the clock again in
the firing step). -/
def cxRunTwo : List (XLbl Nat Nat) :=
  cxQuiet ++ [.begin, .endPass, .delay 4, .wake] ++ cxQuiet ++ [.begin, .delay 3]

/-- **Candidate reading of TIME-013 at the start's own reading** (not a requirement block): a
transition never starts at a host reading at which it is expired. -/
def StartJudgedAtNow (E : XRel Nat Nat) : Prop :=
  ∀ C s n sy s', E C s (.start n sy) s' → ∀ u, findT C n = some u →
    tExpired C.X (viewAt s s.now) u = false

/-- **The reading of ruling D61 (c)**: expiry is judged at the deadline step's reading, the cycle
reading `cyc`, which the firing pass and the park decision share. -/
def StartJudgedAtCycle (E : XRel Nat Nat) : Prop :=
  ∀ C s n sy s', E C s (.start n sy) s' → ∀ u, findT C n = some u →
    tExpired C.X (viewAt s s.cyc) u = false

/-- ✗ A reference start of `u` at host reading `7`, past `u`'s latest bound `5` plus tolerance
`0`, while `u` was not expired at the cycle reading `4`: the literal reading 'never past latest
plus tolerance' at the start's own reading fails, and the start meets the D61 (c) reading. -/
@[evidence cites "TIME-013" "expiry is judged at the reading of the deadline step (ruling D61 (c), R-EXEC-3): on the reference executor a Window(3, 5) transition, not expired at the cycle reading 4, starts after the host clock has reached 7, past latest plus tolerance; Java takes such later readings in its firing step"]
theorem clashExec_twoReadings :
    (∃ s s', xrun cxCfgW (xinit cxM 0) cxRunTwo = some s ∧
      RefExec cxCfgW s (.start "u" false) s' ∧
      tExpired cxCfgW.X (viewAt s s.now) cxU = true ∧
      tExpired cxCfgW.X (viewAt s s.cyc) cxU = false) ∧
    ¬ StartJudgedAtNow RefExec := by
  obtain ⟨s, s', ho, hs, hp⟩ := step_of_check xstep (C := cxCfgW)
    (o := xrun cxCfgW (xinit cxM 0) cxRunTwo) (l := .start "u" false)
    (p := fun s _ => tExpired cxCfgW.X (viewAt s s.now) cxU &&
      !tExpired cxCfgW.X (viewAt s s.cyc) cxU) (by decide +kernel)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  refine ⟨⟨s, s', ho, hs, hp.1, hp.2⟩, fun h => ?_⟩
  have := h cxCfgW s "u" false s' hs cxU rfl
  rw [hp.1] at this
  exact absurd this (by decide)

/-! ## The park decision at the cycle reading (refexec R8, NR-5, ruling D61 (c)) -/

/-- The net of `u` alone, `Delayed(3)`. -/
def cxCfgD : Cfg Nat Nat := cxCfg [cxU] (fun _ => .delayed 3) []

/-- The run up to the wait: `u` is armed at `0` and not ready, the pass starts nothing, and the
host clock advances to `5` before the loop parks. -/
def cxRunPark : List (XLbl Nat Nat) := cxQuiet ++ [.begin, .endPass, .delay 5]

/-- **Candidate reading of CONC-010's park condition at the present reading** (not a requirement
block): the loop parks only when no transition is Ready at the host's present reading. -/
def ParkJudgedAtNow (E : XRel Nat Nat) : Prop :=
  ∀ C s tmr s', E C s (.park tmr) s' → ∀ u ∈ C.X.net.transitions, ¬ Ready C.X (viewAt s s.now) u

/-- ✗ The reference parks, with a timer at the boundary `3` of the cycle reading `0`, while `u` is
Ready at the present reading `5`: the park decision judges at the cycle reading (Rust parks on
`cycle_now`), and the timer ends the wait at once. -/
@[evidence cites "CONC-010" "the park decision judges at the cycle reading, not the present one (ruling D61 (c), design NR-5): the reference parks with a timer at the next boundary of the cycle reading while a Delayed(3) transition is already Ready at the host's present reading, as Rust parks on cycle_now"]
theorem clashExec_parkAtCycle :
    (∃ s s', xrun cxCfgD (xinit cxM 0) cxRunPark = some s ∧ RefExec cxCfgD s (.park (some 3)) s' ∧
      Ready cxCfgD.X (viewAt s s.now) cxU ∧ nothingDue cxCfgD s = true) ∧
    ¬ ParkJudgedAtNow RefExec := by
  obtain ⟨s, s', ho, hs, hp⟩ := step_of_check xstep (C := cxCfgD)
    (o := xrun cxCfgD (xinit cxM 0) cxRunPark) (l := .park (some 3))
    (p := fun s _ => decide (Ready cxCfgD.X (viewAt s s.now) cxU) && nothingDue cxCfgD s)
    (by decide +kernel)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  exact ⟨⟨s, s', ho, hs, hp.1, hp.2⟩,
    fun h => h cxCfgD s (some 3) s' hs cxU (List.mem_singleton_self _) hp.1⟩

/-! ## The timeout outcome is not validated (exec#4, R-EXEC-2, ruling D24 (a)) -/

/-- Firing `i` of `s` ended with a timeout outcome that the join-relay check accepts and the
output validation of `C` rejects, and `s` may settle it. -/
def timeoutRejected {N T : Type} (C : Cfg N T) (s : XSt N T) (i : Nat) : Bool :=
  match s.fl.find? (·.id == i) with
  | some f =>
    match f.out with
    | some (.timedOut e) =>
      canSettle C s i f && C.relay f.t f.deliv e && !C.validate f.t (e.map Prod.fst)
    | _ => false
  | none => false

/-- **The Java and TypeScript reading** (not a requirement block): the executor validates the
timeout outcome against the output spec and fails the firing when validation rejects it
(BitmapNetExecutor.java, the timeout branch of the completion handler). With
`And(A, Timeout(d, B))` it fails every timeout, as the outcome `B` never satisfies the `And`. -/
def TimeoutValidated {N T : Type} (E : XRel N T) : Prop :=
  ∀ C s i, timeoutRejected C s i = true → ∃ s', E C s (.fail i) s'

/-- The Java and TypeScript reading is met by an executor: the EXEC-021 mutant that validates
the timeout outcome. -/
theorem timeoutValidated_mutant : TimeoutValidated (exec021_validateTimeout (N := Nat) (T := Nat)) := by
  intro C s i h
  refine ⟨settle s i, ?_⟩
  show exec021_validateTimeoutStep C s (.fail i) = some (settle s i)
  unfold timeoutRejected at h
  simp only [exec021_validateTimeoutStep]
  split at h
  · rename_i f hf
    rw [hf]
    split at h
    · rename_i e he
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
      simp [he, h.1.1, h.2]
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- ✗ **Conflict**: no executor meets EXEC-021 and also fails the timed-out firings whose outcome
the output spec rejects. On `And(1, Timeout(d, 2))` the budget of firing `0` expires with outcome
`2`; the join-relay check accepts it and output validation rejects it, so such an executor takes a
fail step, which EXEC-021's third line allows only for an error, a rejected returned emission or
a timeout outcome the relay check rejects. Under ruling D24 (a) the timeout outcome is not
validated, and the Java and TypeScript behaviour is a recorded executor defect (RD-01 in
`spec/runtime-defects.md`). -/
@[evidence cites "EXEC-021" "the timeout outcome is not validated against the output spec (ruling D24 (a)): no executor satisfies the block and also fails a timed-out firing of And(1, Timeout(d, 2)) whose outcome 2 the join-relay check accepts and output validation rejects, which is what the Java and TypeScript executors do (a recorded executor defect)"]
theorem clashExec_timeoutValidated_conflict :
    ¬ ∃ E : XRel Nat Nat, EXEC_021 E ∧ TimeoutValidated E := by
  rintro ⟨E, hE, hJ⟩
  let p : Firing Nat Nat → Bool := fun f => match f.out with
    | some (.timedOut e) => exec021_cTO.relay f.t f.deliv e
    | _ => false
  obtain ⟨s, -, hq⟩ := some_of_map (o := exec021_runTO 5)
    (q := fun s => timeoutRejected exec021_cTO s 0 && exec021_all0 s p) (by decide +kernel)
  simp only [Bool.and_eq_true] at hq
  obtain ⟨s', hs⟩ := hJ exec021_cTO s 0 hq.1
  obtain ⟨f, hf, hid, hout⟩ := (hE exec021_cTO (exec021_cfg_set _) 0).2.2.1 s s' hs
  have hg := exec021_of_all0 hq.2 hf hid
  rcases hout with ho | ⟨e, ho, -⟩ | ⟨e, ho, hr⟩ <;> simp [p, ho] at hg
  simp [hr] at hg

/-- The two readings are each met by some executor: the reference meets EXEC-021 and the
validating mutant meets the Java and TypeScript reading, so the conflict is between the two
readings, not a vacuous one. -/
theorem clashExec_timeoutValidated_sides :
    EXEC_021 (RefExec (N := Nat) (T := Nat)) ∧
      TimeoutValidated (exec021_validateTimeout (N := Nat) (T := Nat)) :=
  ⟨EXEC_021_reference, timeoutValidated_mutant⟩

/-! ## A close does not bound the run (env-b#1, ENVB-R2, ruling D85 (a)) -/

/-- `d`: one token from `2`, `Delayed(5)`. -/
def cxDl : Trans Nat := cxT "d" [2] []

/-- The net of `a` (`Immediate`, its action never returns) and `d` (`Delayed(5)`). -/
def cxCfgClose : Cfg Nat Nat :=
  cxCfg [cxA, cxDl] (fun t => if t.core.name = "d" then .delayed 5 else .immediate) []

/-- The run: `a` starts asynchronously and stays in flight; a caller closes the executor; five
units later the next cycle begins its pass, because `a` is still in flight, and starts `d`. -/
def cxRunClose : List (XLbl Nat Nat) :=
  cxQuiet ++ [.begin, .start "a" false, .endPass, .close, .delay 5] ++ cxQuiet ++
    [.begin, .start "d" false]

/-- **Candidate reading of ENV-013's 'terminates after in-flight actions complete' as a ban on
starts** (not a requirement block): after a close, no transition starts. -/
def CloseStopsStarting (E : XRel Nat Nat) : Prop :=
  ∀ C s0 tr, XRun E C s0 tr → AfterNever isClose isStart tr

/-- ✗ After a close the reference keeps starting ready transitions while a firing is in flight
(ruling D85 (a): every runtime does, so a close alone does not bound the run). -/
@[evidence cites "ENV-013" "a closed executor keeps starting ready transitions while a firing is in flight (ruling D85 (a)): on the reference executor a close lands while an asynchronous firing is in flight, and the next cycle begins its pass and starts a Delayed(5) transition, so close alone does not bound the run"]
theorem clashExec_closeKeepsStarting :
    (∃ tr, XRun RefExec cxCfgClose (xinit cxM 0) tr ∧ ¬ AfterNever isClose isStart tr) ∧
    ¬ CloseStopsStarting RefExec := by
  obtain ⟨tr, hr, hq⟩ := run_of_check (C := cxCfgClose) (s := xinit cxM 0) (ls := cxRunClose)
    (q := fun tr => !decide (AfterNever isClose isStart tr)) (by decide +kernel)
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hq
  exact ⟨⟨tr, hr, hq⟩, fun h => hq (h _ _ _ hr)⟩

/-! ## ENV-004: when 'closed or draining' is tested (env-a#5) -/

/-- **The call-time reading of ENV-004 AC2** (not a requirement block): a request is accepted only
while the executor is open. -/
def RefusedAtCall (E : XRel Nat Nat) : Prop :=
  ∀ C s p x r s', E C s (.request p x r) s' → r = .accepted → s.mode = .open

/-- **The processing-time reading of ENV-004 AC2** (not a requirement block): an event is
injected only while the executor is open. -/
def RefusedAtProcessing (E : XRel Nat Nat) : Prop :=
  ∀ C s k s', E C s (.inject k) s' → s.mode = .open

/-- The reference accepts a request only while open. -/
theorem refusedAtCall_reference : RefusedAtCall RefExec := by
  intro C s p x r s' h hr
  obtain ⟨hrf, -⟩ := requestStep_some (C := C) h
  subst hr
  unfold replyFor at hrf
  split at hrf
  · exact absurd hrf (by decide)
  · split at hrf
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact hc.1
    · exact absurd hrf (by decide)

/-- The run: a request for environment place `0` is accepted, a caller drains the executor, and
step 2 is reached. -/
def cxRunDrain : List (XLbl Nat Nat) :=
  [.request 0 5 .accepted, .drain, .endCompletions, .endPublications]

/-- ? **Ambiguity of ENV-004 AC2**: read at the call, the reference meets it; read at processing,
it does not, as an event accepted before a drain is injected while the executor drains (ENV-011
processes the events queued before the drain). -/
@[evidence cites "ENV-004" "'closed or draining' is tested when inject() is called, not when the event is processed: the reference accepts only while open, and injects an event accepted before a drain while it drains (ENV-011), so the processing-time reading fails"]
theorem clashExec_env004_ambiguity : RefusedAtCall RefExec ∧ ¬ RefusedAtProcessing RefExec := by
  refine ⟨refusedAtCall_reference, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := cxCfgEnv)
    (o := xrun cxCfgEnv (xinit cxM0 0) cxRunDrain) (l := .inject 0)
    (p := fun s _ => s.mode == .draining) (by decide +kernel)
  have := h cxCfgEnv s 0 s' hs
  simp only [beq_iff_eq] at hp
  rw [hp] at this
  exact absurd this (by decide)

/-! ## ENV-003 AC3 against the ENV-013 discard line (env-a#7) -/

/-- **The discard line of ENV-013** (rulings D44 (a), D85 (a)): once the executor is closing
(closed or stopped), no event is injected. -/
def NoInjectWhenClosing (E : XRel Nat Nat) : Prop :=
  ∀ C s k s', E C s (.inject k) s' → s.mode.closing = false

/-- **The unconditional reading of ENV-003 AC3** (not a requirement block): on every ideal run,
every accepted event is injected. -/
def EveryAcceptedInjected (E : XRel Nat Nat) : Prop :=
  ∀ C s0 tr, IdealRun E C s0 tr → ∀ k, WhenShall (acceptsTicket k) (injectsTicket k) tr

/-- The reference never injects once closing. -/
theorem noInjectWhenClosing_reference : NoInjectWhenClosing RefExec :=
  fun _ _ _ _ h => by
    obtain ⟨-, -, -, -, -, hm, -⟩ := injectStep_some h
    exact hm

/-- The run: a request for place `0` is accepted with ticket `0`, a caller closes the executor,
step 2 discards the event, and the run finishes closed. -/
def cxRunCloseDiscard : List (XLbl Nat Nat) :=
  [.request 0 5 .accepted, .close, .endCompletions, .endPublications, .discard 0, .endEvents,
   .update, .deadline [], .finish .closed]

/-- ✗ **Conflict of the unconditional ENV-003 AC3 with the discard line**: the reference meets the
discard line, and an ideal run of it accepts the event of ticket `0` and finishes closed without
injecting it. The EARS sentence of AC3 carries the condition 'unless the executor is closed or
stops on a terminal place first'. -/
@[evidence cites "ENV-003" "AC3 holds unless the executor is closed or stops on a terminal place first: the reference never injects once closing (the ENV-013 discard line), and an ideal run accepts an event, is closed, discards the event and finishes closed, so the unconditional reading fails"]
theorem clashExec_env003_conflict :
    NoInjectWhenClosing RefExec ∧ ¬ EveryAcceptedInjected RefExec := by
  refine ⟨noInjectWhenClosing_reference, fun h => ?_⟩
  obtain ⟨tr, hr, hq⟩ := run_of_check (C := cxCfgEnv) (s := xinit cxM0 0)
    (ls := cxRunCloseDiscard)
    (q := fun tr => !isExecPhase (XRun.last (xinit cxM0 0) tr).phase &&
      !decide (WhenShall (acceptsTicket 0) (injectsTicket 0) tr)) (by decide +kernel)
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hq
  exact hq.2 (h _ _ _ ⟨hr, hq.1⟩ 0)

/-! ## Quiescence: 'enabled' or 'armed' (env-b#5, exec#21, ruling D5) -/

/-- **Candidate reading of ENV-010 and ENV-011's quiescence with 'enabled'** (not a requirement
block): the run finishes quiescent only when no transition is enabled. -/
def QuiescentNoneEnabled (E : XRel Nat Nat) : Prop :=
  ∀ C s s', E C s (.finish .quiescent) s' → ∀ u ∈ C.X.net.transitions,
    enabledNA (qCount s.M) u.core = false

/-- **The reading of ruling D5** (glossary Rest, EXEC-040 condition 1): the run finishes quiescent
only when no transition is armed. -/
def QuiescentNoneArmed (E : XRel Nat Nat) : Prop :=
  ∀ C s s', E C s (.finish .quiescent) s' → ∀ u ∈ C.X.net.transitions, ¬ ArmedE s u

/-- The reference finishes quiescent only when no transition is armed. -/
theorem quiescentNoneArmed_reference : QuiescentNoneArmed RefExec := by
  intro C s s' h u hu ha
  obtain ⟨-, -, hf, -⟩ := xstepW_finishQuiescent h
  simp only [finishQ, restB, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hf
  have := hf.1.1.1.1.1 u hu
  unfold ArmedE at ha
  rw [ha] at this
  exact absurd this (by decide)

/-- The run on `Window(3, 5)`: `u` is armed at `0` and not ready, the clock jumps to `6`, and the
deadline step of the next cycle reaps `u` with its token in place `0`. -/
def cxRunReap : List (XLbl Nat Nat) :=
  cxQuiet ++ [.begin, .endPass, .delay 6, .wake, .endCompletions, .endPublications, .endEvents,
    .update, .deadline ["u"]]

/-- ✗ The reference finishes quiescent while the reaped `u` is still enabled (its token stays in
place `0`): quiescence reads 'nothing armed' (ruling D5), not 'nothing enabled'. The Phase 1
counterpart is `exec040_rest_reaped_enabled` (`ClashesTime.lean`). -/
@[evidence cites "ENV-010" "quiescence reads 'no transition armed', not 'enabled' (ruling D5, glossary Rest): on the reference executor a Window(3, 5) transition reaped at reading 6 keeps its token and stays enabled, and the run finishes quiescent, while no run finishes quiescent with a transition armed"]
theorem clashExec_quiescentArmed :
    (∃ s s', xrun cxCfgW (xinit cxM 0) cxRunReap = some s ∧
      RefExec cxCfgW s (.finish .quiescent) s' ∧ ReapedE s cxU ∧
      enabledNA (qCount s.M) cxU.core = true) ∧
    QuiescentNoneArmed RefExec ∧ ¬ QuiescentNoneEnabled RefExec := by
  obtain ⟨s, s', ho, hs, hp⟩ := step_of_check xstep (C := cxCfgW)
    (o := xrun cxCfgW (xinit cxM 0) cxRunReap) (l := .finish .quiescent)
    (p := fun s _ => decide (ReapedE s cxU) && enabledNA (qCount s.M) cxU.core)
    (by decide +kernel)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  refine ⟨⟨s, s', ho, hs, hp.1, hp.2⟩, quiescentNoneArmed_reference, fun h => ?_⟩
  have := h cxCfgW s s' hs cxU (List.mem_singleton_self _)
  rw [hp.2] at this
  exact absurd this (by decide)

/-! ## ENV-010 and its guard (env-b#3, ruling D73 (a)) -/

/-- **The unconditional reading of ENV-010** (not a requirement block): an executor with
environment places never finishes quiescent. -/
def EnvNeverQuiescent (E : XRel Nat Nat) : Prop :=
  ∀ C s s', C.envs ≠ [] → ¬ E C s (.finish .quiescent) s'

/-- **The reading of ruling D73 (a)**: an executor with environment places finishes, for any
cause, only once it no longer accepts injections: it is draining, closed or stopped, or a terminal
place is marked. -/
def EnvEndsOnlyWhenNotAccepting (E : XRel Nat Nat) : Prop :=
  ∀ C s c s', C.envs ≠ [] → E C s (.finish c) s' → ¬ (s.mode = .open ∧ Live C s)

/-- The reference meets the guard of ruling D73 (a). -/
theorem envEndsOnlyWhenNotAccepting_reference : EnvEndsOnlyWhenNotAccepting RefExec := by
  intro C s c s' hE h ⟨hm, hl⟩
  cases c with
  | quiescent =>
    obtain ⟨-, -, hf, -⟩ := xstepW_finishQuiescent h
    simp only [finishQ, Bool.and_eq_true, Bool.or_eq_true, List.isEmpty_iff, hm,
      bne_self_eq_false] at hf
    exact hE (hf.2.elim id (fun h => absurd h (by decide)))
  | closed =>
    obtain ⟨-, -, hc, -⟩ := xstepW_finishClosed h
    rw [hm] at hc
    exact absurd hc (by decide)
  | terminal =>
    obtain ⟨-, hlf, -⟩ := xstepW_finishTerminal h
    unfold Live at hl
    rw [hl] at hlf
    exact absurd hlf (by decide)
  | stopped =>
    obtain ⟨-, -, hst, -⟩ := xstepW_finishStopped h
    rw [hm] at hst
    exact absurd hst (by decide)

/-- ✗ ENV-010's unconditional sentence is false of the reference, which meets the D73 (a) guard:
after a drain, an executor with an environment place and nothing to do finishes quiescent. -/
@[evidence cites "ENV-010" "an executor with environment places does not terminate at quiescence while it can still accept an injection (ruling D73 (a)): the reference finishes only once it is draining, closed or stopped or a terminal place is marked, and after a drain an executor with an environment place finishes quiescent, so the unconditional reading fails"]
theorem clashExec_env010_guard :
    EnvEndsOnlyWhenNotAccepting RefExec ∧ ¬ EnvNeverQuiescent RefExec := by
  refine ⟨envEndsOnlyWhenNotAccepting_reference, fun h => ?_⟩
  obtain ⟨s, s', -, hs, -⟩ := step_of_check xstep (C := cxCfgEnv)
    (o := xrun cxCfgEnv (xinit cxM0 0) (.drain :: cxQuiet)) (l := .finish .quiescent)
    (p := fun _ _ => true) (by decide +kernel)
  exact h cxCfgEnv s s' (by decide) hs

/-! ## The cause of a close at rest (exec#11, ruling D53 (c)) -/

/-- The run: an executor with an environment place and nothing to do waits in its first cycle, a
caller closes it, and the next cycle reaches its termination test at rest. -/
def cxRunClosedRest : List (XLbl Nat Nat) :=
  cxQuiet ++ [.begin, .endPass, .park none, .close, .wake] ++ cxQuiet

/-- ✓ At a closed rest the reference offers both causes, `finish quiescent` (Java, Rust) and
`finish closed` (TypeScript): ruling D53 (c) allows either, and only a truncated run is never
reported as completed. -/
@[evidence cites "EXEC-041" "when close() lands on a run at rest, either cause may be reported (ruling D53 (c)): at the closed rest of the reference both the quiescent finish and the closed finish are steps"]
theorem clashExec_closedRest_bothCauses :
    ∃ s, xrun cxCfgEnv (xinit cxM0 0) cxRunClosedRest = some s ∧
      (∃ s', RefExec cxCfgEnv s (.finish .quiescent) s') ∧
      (∃ s', RefExec cxCfgEnv s (.finish .closed) s') := by
  obtain ⟨s, hs, hq⟩ := some_of_map (o := xrun cxCfgEnv (xinit cxM0 0) cxRunClosedRest)
    (q := fun s => (xstep cxCfgEnv s (.finish .quiescent)).isSome &&
      (xstep cxCfgEnv s (.finish .closed)).isSome) (by decide +kernel)
  simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hq
  exact ⟨s, hs, hq.1, hq.2⟩

end Libpetri.Spec
