import Libpetri.Spec.Registry
import Libpetri.Spec.Req.ENV_002
import Libpetri.Spec.Req.ENV_003
import Libpetri.Spec.Req.ENV_004
import Libpetri.Spec.Req.ENV_010
import Libpetri.Spec.Req.EXEC_001
import Libpetri.Spec.Req.CONC_002
import Libpetri.Spec.Req.CONC_005_cycle
import Libpetri.Spec.Req.TIME_cycle

set_option linter.missingDocs true
/- The decided runs below unfold about 130 reference steps on a net of ten transitions. -/
set_option maxRecDepth 100000

/-!
# ENV-012: Event-driven workflow pattern (`spec/06-environment-places.md`)

ENV-012 is kind Q and has no requirement block (plan section 3, ruling D21 (a)). Its one
behaviour sentence, AC3 ("The net reacts to each injection by enabling relevant transitions."),
is what other blocks already say: ENV-002 (a registered place is not answered with an error),
ENV-010 (an open, running executor with no terminal place marked accepts an injection, and an
executor with environment places does not end at quiescence but waits for the next event),
ENV-003 (an accepted injection is queued with a ticket of its own, FIFO, and injected unless the
executor is closed, terminated immediately or stopped on a terminal place), ENV-004 (the
injection puts the token at the tail of its own place and changes the marking in no other way),
and for the arming: EXEC-001 line 8 (an update arms every enabled transition that is off, not
reaped and, when the executor is not re-entrant, not in flight; the re-entrancy exception is
CONC-002 line 5), TIME-010's executor companion (the stamp of a newly armed transition is the
update's reading, and nothing arms outside an update), and CONC-005's and TIME-013's executor
companions (an injection that writes a reaped transition's arc place ends its reaping, so the
next update can arm it again). TIME-010 and TIME-013 themselves are Phase 1 blocks, and an
injection is not a step of the Phase 1 relation, so they do not carry AC3. A second block with
the same predicate would duplicate these. What remains is a scale scenario, and this file
decides it on the reference executor `RefExec`, tagged with `cites "ENV-012"`:

* a net with ten registered environment places `0` to `9`, the event sources, and one Immediate
  consumer `t<i> : i → 10 + i` per source;
* ten requests from ten sources, in a scrambled order, five while the loop is parked and five
  while it runs step 1, all accepted (AC1, AC2);
* the ten injections, each in its own place, then the update arms all ten consumers, which fire
  and move every token on (AC3);
* back at rest the executor does not end; it waits, accepts one more event into place `4`, arms
  only `t4`, fires it, and is at rest again without ending (the body's "runs indefinitely,
  processing events as they arrive").

`env012_reference_blocks` records that the executor of the scenario is the one all of these
blocks hold of. `env012_forbids_injectNotDirty` is the killing mutant of AC3: an executor whose
injection never marks its place dirty (the slip of dropping the dirty bit in an injection path)
is not ruled out by ENV-002, ENV-003, ENV-004 or ENV-010, which say nothing about arming, and
EXEC-001 line 8 rejects it on this scenario. "~10 environment places", "runs indefinitely" and the concurrency of
AC2 are quality targets: a decided run shows one instance, the general statements are the blocks
above, and the thread safety of a concurrent `inject()` is ENV-003's. Concurrency is modelled as
atomic request steps interleaved with the loop (while parked and during step 1), not as racing
callers. No test in any language cites ENV-012 yet; a 10-place test per language is an open
item. The scenario has one pending event per place, so per-place FIFO and the no-merge of two
events into one place are ENV-003's and ENV-004's evidence, not this file's. No runtime caps the
number of environment places: Java and TypeScript keep them in a set built from the builder's
list, Rust in a set of names.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## The scenario -/

/-- The consumer of source `i`: one token from environment place `i`, output `Out.place (10 + i)`,
named `t<i>`. -/
def env012_t (i : Nat) : Trans Nat :=
  { core := { name := s!"t{i}", inputs := [⟨i, .one⟩], inhibitors := [], reads := [],
              resets := [] },
    out := some (.place (10 + i)) }

/-- Ten event sources, places `0` to `9`, each with its consumer; places `10` to `19` collect
what the consumers produce. Every transition is Immediate with priority `0`; validation and the
relay check accept everything (they are EXEC-021's subject); no terminal place. -/
def env012_C : Cfg Nat Nat :=
  { X := { net := { places := List.range 20, transitions := (List.range 10).map env012_t },
           timing := fun _ => .immediate, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := List.range 10, reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true,
    timeoutOut := fun _ _ _ => false, res := 0 }

/-- The start: empty marking, reading `0`, open. -/
def env012_s0 : XSt Nat Nat := xinit (fun _ => []) 0

/-- Steps 1 to 4 of a cycle with nothing queued, up to the termination test. -/
def env012_toTest : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline []]

/-- A request from source `i`: inject the token `100 + i` into place `i`, answered accepted. -/
def env012_req (i : Nat) : XLbl Nat Nat := .request i (100 + i) .accepted

/-- The sources heard from while the loop is parked, in arrival order. -/
def env012_early : List Nat := [3, 7, 0, 9, 1]

/-- The sources heard from after the wake, while the loop runs step 1, in arrival order. -/
def env012_late : List Nat := [5, 2, 8, 4, 6]

/-- The first cycle finds nothing to do and parks; then the ten requests arrive, five while
parked, then the wake, then five while the loop runs step 1. -/
def env012_arrive : List (XLbl Nat Nat) :=
  env012_toTest ++ [.begin, .endPass, .park none] ++ env012_early.map env012_req ++ [.wake] ++
    env012_late.map env012_req

/-- Steps 1 and 1b end, and step 2 injects the ten queued events by ticket, oldest first. -/
def env012_injectAll : List (XLbl Nat Nat) :=
  env012_arrive ++ [.endCompletions, .endPublications] ++ (List.range 10).map (.inject ·)

/-- The same ten requests arriving in the opposite order (`6`, `4`, `8`, `2`, `5` while parked,
then `1`, `9`, `0`, `7`, `3` after the wake), then steps 1, 1b and the ten injections. -/
def env012_injectRev : List (XLbl Nat Nat) :=
  env012_toTest ++ [.begin, .endPass, .park none] ++ env012_late.reverse.map env012_req ++
    [.wake] ++ env012_early.reverse.map env012_req ++ [.endCompletions, .endPublications] ++
    (List.range 10).map (.inject ·)

/-- Step 2 ends, the update runs (it arms what the injections enabled), and the firing pass
begins. -/
def env012_toPass : List (XLbl Nat Nat) :=
  env012_injectAll ++ [.endEvents, .update, .deadline [], .begin]

/-- The order in which the ten actions return. -/
def env012_retOrder : List Nat := [6, 4, 8, 2, 5, 1, 9, 0, 7, 3]

/-- The pass starts all ten consumers (firings `10` to `19`, asynchronous); each action writes
its token on and returns, in `env012_retOrder`; the next cycle commits them in that order and
reaches its termination test. -/
def env012_round1 : List (XLbl Nat Nat) :=
  env012_toPass ++ (List.range 10).map (fun i => .start s!"t{i}" false) ++ [.endPass] ++
    env012_retOrder.flatMap (fun i => [.write (10 + i) (10 + i) (100 + i), .ret (10 + i) true]) ++
    env012_retOrder.map (fun i => .commit (10 + i)) ++ env012_toTest

/-- One more event, later: the loop parks, source `4` sends `204` (ticket `20`), the loop wakes
and injects it, and the update of that cycle runs. -/
def env012_again : List (XLbl Nat Nat) :=
  env012_round1 ++ [.begin, .endPass, .park none, .request 4 204 .accepted, .wake, .endCompletions,
    .endPublications, .inject 20, .endEvents, .update]

/-- `t4` fires on the new event (firing `21`) and the next cycle reaches its test. -/
def env012_round2 : List (XLbl Nat Nat) :=
  env012_again ++ [.deadline [], .begin, .start "t4" false, .endPass, .write 21 14 204,
    .ret 21 true, .commit 21] ++ env012_toTest

/-- Read a decided fact off a state: if the check `p` of the state `o` evaluates to `true`, the
state exists. -/
theorem env012_state_of_check {o : Option (XSt Nat Nat)} {p : XSt Nat Nat → Bool}
    (h : o.map p = some true) : ∃ s, o = some s ∧ p s = true := by
  cases ho : o with
  | none => simp [ho] at h
  | some s => simp only [ho, Option.map_some, Option.some.injEq] at h; exact ⟨s, rfl, h⟩

/-! ## The executor of the scenario is the one the blocks hold of -/

/-- The scenario runs on the reference executor, which meets every block that owns ENV-012's
content. ENV-002: a registered place is not answered with an error. ENV-003: an accepted request
is queued with a ticket of its own and injected oldest first. ENV-004: the injection lands in its
own place only. ENV-010: an open executor with environment places does not end at quiescence.
EXEC-001: an update arms every enabled transition that is off and not reaped (line 8). CONC-002:
the one exception, a transition already in flight when the executor is not re-entrant. TIME-010's
companion: nothing arms outside an update, and the update stamps what it arms with its reading.
CONC-005's and TIME-013's companions: an injection into a reaped transition's arc place ends the
reaping, so the next update can arm it. -/
theorem env012_reference_blocks :
    ENV_002 (RefExec (N := Nat) (T := Nat)) ∧ ENV_003 (RefExec (N := Nat) (T := Nat)) ∧
      ENV_004 (RefExec (N := Nat) (T := Nat)) ∧ ENV_010 (RefExec (N := Nat) (T := Nat)) ∧
      EXEC_001 (RefExec (N := Nat) (T := Nat)) ∧ CONC_002 (RefExec (N := Nat) (T := Nat)) ∧
      TIME_010_cycle (RefExec (N := Nat) (T := Nat)) ∧
      TIME_013_cycle (RefExec (N := Nat) (T := Nat)) ∧
      CONC_005_cycle (RefExec (N := Nat) (T := Nat)) :=
  ⟨ENV_002_reference, ENV_003_reference, ENV_004_reference, ENV_010_reference,
    EXEC_001_reference, CONC_002_reference, TIME_010_cycle_reference, TIME_013_cycle_reference,
    CONC_005_cycle_reference⟩

/-! ## AC1: ten registered environment places -/

/-- Ten environment places at once. The net registers places `0` to `9`. Starting empty, the
executor reaches its wait, and ten callers each ask to inject into a different one of the ten
places: `3`, `7`, `0`, `9`, `1` while the loop is parked, `5`, `2`, `8`, `4`, `6` after it woke.
Every request is a step of the reference answered accepted, and the event queue then holds ten
events, one per place, with the tickets `0` to `9` in arrival order. Nothing has reached the
marking yet. -/
@[evidence cites "ENV-012" "AC1: 10+ environment places can be registered simultaneously."]
theorem env012_ten_registered :
    env012_C.envs = List.range 10 ∧
    ∃ s, xrun env012_C env012_s0 env012_arrive = some s ∧
      s.eq.map (·.1) = List.range 10 ∧
      s.eq.map (·.2.1) = env012_early ++ env012_late ∧
      ∀ p < 20, s.M p = [] := by
  refine ⟨rfl, ?_⟩
  obtain ⟨s, hs, hp⟩ := env012_state_of_check (o := xrun env012_C env012_s0 env012_arrive)
    (p := fun s => s.eq.map (·.1) == List.range 10 &&
      s.eq.map (·.2.1) == env012_early ++ env012_late &&
      (List.range 20).all (fun p => (s.M p).isEmpty)) (by decide)
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    List.isEmpty_iff] at hp
  exact ⟨s, hs, hp.1.1, hp.1.2, hp.2⟩

/-! ## AC2: injections from several sources -/

/-- Ten sources, interleaved with the loop. The ten requests of `env012_ten_registered` arrive in
a scrambled order, half while the loop is parked and half while it runs step 1. Step 2 then
injects them oldest first, and after it every source's token sits in its own place and nowhere
else: place `i` holds exactly `100 + i` for each source `i`, and the output places `10` to `19`
are still empty. The same requests arriving in the opposite order give the same marking. -/
@[evidence cites "ENV-012" "AC2: Injection from multiple concurrent sources works correctly."]
theorem env012_sources :
    (∃ s, xrun env012_C env012_s0 env012_injectAll = some s ∧
      (∀ i < 10, s.M i = [100 + i] ∧ s.M (10 + i) = []) ∧ s.eq = []) ∧
    (∃ s, xrun env012_C env012_s0 env012_injectRev = some s ∧
      (∀ i < 10, s.M i = [100 + i] ∧ s.M (10 + i) = []) ∧ s.eq = []) := by
  constructor
  · obtain ⟨s, hs, hp⟩ := env012_state_of_check (o := xrun env012_C env012_s0 env012_injectAll)
      (p := fun s => (List.range 10).all (fun i => s.M i == [100 + i] && (s.M (10 + i)).isEmpty) &&
        s.eq.isEmpty) (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
      List.isEmpty_iff] at hp
    exact ⟨s, hs, hp.1, hp.2⟩
  · obtain ⟨s, hs, hp⟩ := env012_state_of_check (o := xrun env012_C env012_s0 env012_injectRev)
      (p := fun s =>
        (List.range 10).all (fun i => s.M i == [100 + i] && (s.M (10 + i)).isEmpty) &&
        s.eq.isEmpty) (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
      List.isEmpty_iff] at hp
    exact ⟨s, hs, hp.1, hp.2⟩

/-! ## AC3: each injection enables its consumer -/

/-- The net reacts to each injection. After the ten injections the update of the same cycle arms
every consumer `t0` to `t9`, and the firing pass offers all ten. They fire, and at the next
termination test every token has moved on: place `i` is empty and place `10 + i` holds
`100 + i`. Later a single event into place `4` arms `t4` and no other consumer, and after `t4`
fires place `14` holds `104` and then `204`. -/
@[evidence cites "ENV-012" "AC3: The net reacts to each injection by enabling relevant transitions."]
theorem env012_reacts :
    (∃ s, xrun env012_C env012_s0 env012_toPass = some s ∧
      (∀ i < 10, armedB s (env012_t i) = true) ∧ s.order.length = 10) ∧
    (∃ s, xrun env012_C env012_s0 env012_round1 = some s ∧
      ∀ i < 10, s.M i = [] ∧ s.M (10 + i) = [100 + i]) ∧
    (∃ s, xrun env012_C env012_s0 env012_again = some s ∧
      ∀ i < 10, armedB s (env012_t i) = decide (i = 4)) ∧
    (∃ s, xrun env012_C env012_s0 env012_round2 = some s ∧ s.M 14 = [104, 204] ∧ s.M 4 = []) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨s, hs, hp⟩ := env012_state_of_check (o := xrun env012_C env012_s0 env012_toPass)
      (p := fun s => (List.range 10).all (fun i => armedB s (env012_t i)) &&
        s.order.length == 10) (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hp
    exact ⟨s, hs, hp.1, hp.2⟩
  · obtain ⟨s, hs, hp⟩ := env012_state_of_check (o := xrun env012_C env012_s0 env012_round1)
      (p := fun s => (List.range 10).all (fun i => (s.M i).isEmpty && s.M (10 + i) == [100 + i]))
      (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
      List.isEmpty_iff] at hp
    exact ⟨s, hs, hp⟩
  · obtain ⟨s, hs, hp⟩ := env012_state_of_check (o := xrun env012_C env012_s0 env012_again)
      (p := fun s => (List.range 10).all (fun i => armedB s (env012_t i) == decide (i = 4)))
      (by decide)
    simp only [beq_iff_eq, List.all_eq_true, List.mem_range] at hp
    exact ⟨s, hs, hp⟩
  · obtain ⟨s, hs, hp⟩ := env012_state_of_check (o := xrun env012_C env012_s0 env012_round2)
      (p := fun s => s.M 14 == [104, 204] && (s.M 4).isEmpty) (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hp
    exact ⟨s, hs, hp⟩

/-! ## AC3's killing mutant: an injection that never marks its place dirty -/

/-- An executor whose injection never marks the injected place dirty, so its update never
re-evaluates a transition that only environment places feed: the update keeps the clock status of
every transition whose input places are all environment places. It is the slip of dropping the
dirty bit in an injection path (TypeScript's `processExternalEvents`, Java's injection deposit,
Rust's `inject_external_token`); every other step is the reference's. -/
def env012_injectNotDirtyStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .update => (xstep C s .update).map fun s' =>
      { s' with st := fun n =>
          if (findT C n).any (fun u => u.core.inputs.all (fun a => C.envs.contains a.place))
          then s.st n else s'.st n }
  | l => xstep C s l

/-- The executor of `env012_injectNotDirtyStep`. -/
def env012_injectNotDirty {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => env012_injectNotDirtyStep C s l = some s'

/-- Dropping the dirty bit of an injection breaks AC3. On the ten-source net, the ten requests
are accepted, queued and injected exactly as on the reference, so each place `i` holds `100 + i`.
But the update that follows leaves `t0` off: it is enabled, not in flight and not reaped, and it
holds no clock, so it never fires. EXEC-001 line 8 forbids that state after an update, so this
executor does not meet EXEC-001. -/
@[evidence forbids EXEC_001]
theorem env012_forbids_injectNotDirty :
    ¬ EXEC_001 (env012_injectNotDirty (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨tr, hr, hq⟩ := Exec001.run_of_check (g := env012_injectNotDirtyStep)
    (C := env012_C) (s := env012_s0) (ls := env012_injectAll ++ [.endEvents, .update])
    (q := fun tr => tr.any fun e => isUpdate e && e.2.2.st "t0" == .off &&
      enabledNA (qCount e.2.2.M) (env012_t 0).core && !inFlightN e.2.2 "t0")
    (by decide +kernel)
  obtain ⟨⟨s, l, s'⟩, he, hb⟩ := List.any_eq_true.1 hq
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hb
  obtain ⟨⟨⟨hu, hoff⟩, hen⟩, hfl⟩ := hb
  have hl : l = .update := by cases l <;> simp_all [isUpdate]
  subst hl
  have hx := (h env012_C).2 s s' (Exec001.run_mem hr _ he) "t0" (env012_t 0) rfl
  have hname : (env012_t 0).core.name = "t0" := rfl
  rcases hx.1 hen (Or.inr (by simp [InFlight, hfl])) with ha | ha
  · simp [ArmedE, armedB, hname, hoff, stampOf] at ha
  · simp [ReapedE, hname, hoff] at ha

/-! ## The body: the executor goes on, processing events as they arrive -/

/-- Processing events as they arrive. After all ten consumers fired, the executor is at its
termination test with nothing armed, in flight or queued, the mode open and no terminal place
marked, and it does not end: no quiescent finish is offered, the firing pass is. It parks,
accepts one more event into place `4` while parked, processes it, and at its next test is at rest
again, still without a quiescent finish. A decided run shows one such return to the wait; that it
never ends while open is ENV-010's line 1. -/
@[evidence cites "ENV-012" "The engine supports event-driven workflow patterns where ~10 environment places represent external event sources (activity signals, data streams, tool requests, state changes, etc.) and the executor runs indefinitely, processing events as they arrive."]
theorem env012_goes_on :
    (∃ s, xrun env012_C env012_s0 env012_round1 = some s ∧ s.phase = .test ∧
      Rest env012_C s ∧ Live env012_C s ∧ s.mode = .open ∧
      (¬ ∃ s', RefExec env012_C s (.finish .quiescent) s') ∧ ∃ s', RefExec env012_C s .begin s') ∧
    (∃ s, xrun env012_C env012_s0 env012_round2 = some s ∧ s.phase = .test ∧
      Rest env012_C s ∧ s.mode = .open ∧ ¬ ∃ s', RefExec env012_C s (.finish .quiescent) s') := by
  constructor
  · obtain ⟨s, hs, hp⟩ := env012_state_of_check (o := xrun env012_C env012_s0 env012_round1)
      (p := fun s => decide (s.phase = .test) && restB env012_C s && liveB env012_C s &&
        decide (s.mode = .open) && (xstep env012_C s (.finish .quiescent)).isNone &&
        (xstep env012_C s .begin).isSome) (by decide)
    simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none,
      Option.isSome_iff_exists] at hp
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, s', h6⟩ := hp
    exact ⟨s, hs, h1, h2, h3, h4, fun ⟨s'', h''⟩ => by simp [RefExec, h5] at h'', s', h6⟩
  · obtain ⟨s, hs, hp⟩ := env012_state_of_check (o := xrun env012_C env012_s0 env012_round2)
      (p := fun s => decide (s.phase = .test) && restB env012_C s &&
        decide (s.mode = .open) && (xstep env012_C s (.finish .quiescent)).isNone) (by decide)
    simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at hp
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hp
    exact ⟨s, hs, h1, h2, h3, fun ⟨s'', h''⟩ => by simp [RefExec, h4] at h''⟩

end Libpetri.Spec
