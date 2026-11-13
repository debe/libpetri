import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Exec

set_option linter.missingDocs true

/-!
# TIME-014: Competitive scheduling with timing (`spec/03-timing.md`)

A block over the executor model (`RefExec`, `Reference/Exec.lean`). A firing pass opens with a
`begin` step, which fixes the pass's order, then walks the order from its head: the head either
starts (`start`) or cannot start and loses its clock (`lose`); the pass ends with `endPass`. The
requirement is a predicate over an abstract executor `R : XRel N T` (glossary
`GlossaryExec.lean`): after every `begin` step of a run, the transitions the pass offers come in
the ready order of [EXEC-002] at the cycle reading; the pass does not close, by `endPass` or any
other step a pass cannot hold, before it has offered all of them; and the reading the pass judges
at is the deadline step's reading, which is not earlier than the host reading the cycle's update
took (ruling D61 (c)).

The evidence checks it against the reference executor and against six executors that order or
judge the pass otherwise: lower priority first, every transition of the net offered by priority
whether ready or not (as `clash014_allOrder` orders them), a gate one tick late, `Immediate`
before `Delayed` among equal priorities (the ordering reading of the old second bullet, ruling
D9), a pass that breaks at its first `lose`, a cycle reading that is never renewed, and a pass that
takes a reading of its own when it begins (the step-5 reading RD-16 in `spec/runtime-defects.md`
recorded for Java). The
second shall sentence, "a `Delayed` transition shall not fire before its earliest bound", follows
from the block for every executor that satisfies it (`TIME_014_started_ready`,
`TIME_014_not_before_earliest`). The examples are the acceptance criteria, with the scenario of
AC2 chosen by ruling D9 (b) and R-EXEC-5 (b): the primary transition waits for an event token.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Novel.TimedScg (Timing)

/-! ## The firing pass, as the trace shows it -/

section Pass

variable {N T : Type}

/-- The name a step offers to the pass: the name of a `start` or of a `lose`, nothing for any
other step. -/
def time014_offered : XStep N T → Option String
  | (_, .start n _, _) => some n
  | (_, .lose n, _) => some n
  | _ => none

/-- The step is a `begin`: it opens a firing pass. -/
def time014_isBegin : XStep N T → Bool
  | (_, .begin, _) => true
  | _ => false

/-- The steps of a trace up to its first `begin`: the rest of the pass a `begin` step opened, and
the rest of its cycle. -/
def time014_pass : List (XStep N T) → List (XStep N T)
  | [] => []
  | st :: rest => if time014_isBegin st then [] else st :: time014_pass rest

/-- The names the steps offer, in order. -/
def time014_offers (w : List (XStep N T)) : List String := w.filterMap time014_offered

/-- A label a firing pass can hold before it closes: a `start` or a `lose` of the order, a
settle of a synchronous firing inside its own pass (`commit`, `fail`, `tdeposit`, ruling D70 (a)),
or an outside step ([CONC-001]). -/
def time014_inPass : XLbl N T → Bool
  | .start _ _ | .lose _ | .commit _ | .fail _ | .tdeposit _ => true
  | l => l.outside

/-- The step is a `finish` with cause `terminal` ([EXEC-042]). -/
def time014_isTerminal : XStep N T → Bool
  | (_, .finish .terminal, _) => true
  | _ => false

/-- The steps of a trace before the pass closes, and the step that closes it: the first step
whose label a pass cannot hold (`endPass`, a terminal finish, the next `begin`, or a step of any
other phase), if there is one. -/
def time014_close : List (XStep N T) → List (XStep N T) × Option (XStep N T)
  | [] => ([], none)
  | st :: rest =>
    if time014_inPass st.2.1 then (st :: (time014_close rest).1, (time014_close rest).2)
    else ([], some st)

/-- The step takes a reading of the firing clock for the cycle: an update or a deadline step
(ruling D61 (c)). -/
def time014_rereads : XLbl N T → Bool
  | .update | .deadline _ => true
  | _ => false

/-- The names of the pass's ready order at state `s`: the reference order of [EXEC-002] over the
cycle reading (`readyOrder`, glossary `GlossaryExec.lean`). -/
def time014_orderNames [DecidableEq N] (C : Cfg N T) (s : XSt N T) : List String :=
  (readyOrder C s).map (·.core.name)

end Pass

/-! ## TIME-014: Competitive Scheduling with Timing -/

requirement TIME_014
  id "TIME-014"
  title "Competitive Scheduling with Timing"
  kind T
  scope "all executors"
  source verbatim "spec/03-timing.md"
  quote "When multiple transitions compete for the same tokens, timing interacts with priority:"
        "Higher priority transitions are preferred."
        "*While* several ready transitions compete for the same tokens, the executor *shall* fire them in the order of [EXEC-002], so the transition with the highest priority takes the tokens first ([EXEC-003])."
        "*While* a `Delayed` transition is armed and its elapsed time is less than its earliest bound, it *shall not* fire, so a ready transition competing for the same tokens takes them first whatever their priorities ([TIME-004])."
  reading "For every executor R and every configuration C:"
          "in every run of R that opens with a begin step from state s, read up to the next begin step, the names of its start and lose steps, in order, are a prefix of the names of the ready order of EXEC-002 at the cycle reading of s (readyOrder C s);"
          "in every such run, if the pass closes, at the first step whose label a pass cannot hold (anything but a start, a lose, a settle of a synchronous firing, or an outside step), and that step is not a terminal finish, the start and lose steps before it name the whole of that order;"
          "in every run of R that opens with an update step from state s, the cycle reading at the next begin step, with no other update step between, is not earlier than the host reading of s, the update's reading; and in every run of R that opens with a deadline step to state s', the cycle reading at the next begin step, with no update or deadline step between, is the cycle reading of s', the deadline step's reading."
  assumes "The model is an executor R : XRel N T (glossary GlossaryExec.lean): R C s l s' says that under configuration C the step labelled l leads from executor state s to s'. A firing pass opens with a begin step, which fixes the pass's order, then takes the head of that order once per step: start, the head starts, or lose, it cannot start and its clock is lost; endPass ends the pass. 'Fire' is read as 'start': a firing starts in the pass and settles in a later step (EXEC-001). The witness is the reference executor RefExec (Reference/Exec.lean), whose Phase 5 follows the Rust executor (executor_core/executor.rs, Phase 5: the ready list is walked, a transition that fails its recheck is disabled)."
          "readyOrder C s is the reference order of EXEC-002 over the timed view of s at its cycle reading (viewAt s s.cyc), the reading the deadline step of the cycle took, which the pass and the park decision judge at (ruling D61 (c)): the ready transitions sorted by priority descending, stamp ascending and declaration order ascending, and on the all-immediate fast path in declaration order (ruling D14 (a)). Ready is the glossary term: armed, elapsed time at least the earliest bound, not expired. Line 1 fixes the order to that function, so this block is also EXEC-002's executor line: the pass starts its firings in that order."
          "Transitions are read by name throughout, under ruling D10 (NamesDistinct, part of Cfg.WF): line 1 compares the names a pass offers with the names of the order, so with two transitions of one name a start of the one that is not ready would pass for the one that is. Nets with duplicate names are outside the block, as they are outside TIME-013."
          "The first shall sentence is lines 1 and 2: the pass offers the ready transitions in the order of EXEC-002, one start or lose for each in turn (line 1), and does not close before it has offered every one of them (line 2), so no ready transition is passed over. A pass closes at its first step whose label it cannot hold: endPass, a park or a wake, a step of steps 1 to 4, a termination test, or the next begin. It can hold start and lose, the settle (commit, fail, tdeposit) of a synchronous firing inside its own pass (ruling D70 (a)), and the outside steps, which come at any time (CONC-001). Line 1 alone does not exclude a pass that stops early; an executor whose gate is one tick late ends the pass at the bound of the fallback transition without offering it and breaks only line 2 (TIME_014_forbids_lateGate), and so does an executor whose pass breaks at its first lose and goes on to step 1 without an endPass (the break-for-continue slip in the Phase 5 loop, TIME_014_forbids_breakOnLose). An executor that offers the lower priority first breaks line 1 (TIME_014_forbids_lowFirst)."
          "Scope of the window: line 1 reads a pass up to the next begin step, so a run that starts inside a pass says nothing about that pass (EXEC-003 says a start takes the head of the pass's order). Because line 1 runs to the next begin and line 2 makes the pass offer the whole order before it closes, no start or lose may come between the close of a pass and the next begin; this is EXEC-001's step order (start and lose are step 5), not an addition to it. A pass that a terminal place stops (EXEC-042: nothing later in the pass fires) closes with a terminal finish, so line 2 does not apply to it. A run cut before its pass closes says nothing under line 2: that the pass closes at all is liveness, which no line here states. Re-entrancy (ruling D8 (b)) changes nothing here: a transition in flight that may not start again is off after the update, so it is not ready and not in the order."
          "The consequence 'so the transition with the highest priority takes the tokens first ([EXEC-003])' is line 1 together with EXEC-003, whose statement holds both halves over the same model: its line 3 lets a lose happen only for a head that is not armed or not enabled on the pass-visible marking, and its line 2 fixes what a start consumes. So an executor that offers the right order and turns every offer into a lose satisfies this block and breaks EXEC-003. TIME_014_nonvacuous shows two Immediate transitions on one token: the one of priority 10 starts, the one of priority -10 loses."
          "The second shall sentence follows from line 1: the ready order holds only ready transitions (EXEC-002 line 1), so a transition started in the pass was ready at the cycle reading of the pass, its elapsed time at least its earliest bound (TIME_014_started_ready); under distinct names (ruling D10) a transition armed below its earliest bound at that reading is not started in that pass (TIME_014_not_before_earliest). Its clause 'so a ready transition competing for the same tokens takes them first whatever their priorities' is line 2 with EXEC-003: the ready competitor is in the order and is offered, the Delayed one is not. TIME_014_nonvacuous shows it with a Delayed transition of priority 10 and an Immediate one of priority -10 on one token: only the Immediate one is in the order, and it starts. An executor that offers every transition of the net by priority, ready or not (as clash014_allOrder orders them), starts the Delayed one first and breaks line 1 (TIME_014_forbids_allOrder). The Phase 1 form of the gate is TIME-010 line 4 (time010_gate)."
          "Line 3 is ruling D61 (c) as far as the pass needs it, in two halves. The reading the pass judges at is the deadline step's reading: no step between the deadline step and the begin step moves it. And it is not earlier than the host reading the update of its cycle took, the reading that stamps what the update newly arms (TIME-010's companion, line 1), so the elapsed time of the second shall sentence and the Ready of the first are measured at the present cycle and not at an older reading. Without that half lines 1 and 2 hold of an executor that never renews its reading (the clock reading hoisted out of the loop): a Delayed transition then never reaches its earliest bound at the cycle reading and never fires, and line 3 rejects it (TIME_014_forbids_staleReading). The reference stamps at the update's reading and takes a reading of its own at the deadline step, never an earlier one (atDeadline), which the pass and the park decision share. A run with no delay between the update and the deadline step is an executor that takes one reading per cycle, as Rust and Java do (executor_core/executor.rs, cycle_now; BitmapNetExecutor.java and PrecompiledNetExecutor.java, cycleNanos, taken before the update); a run with a delay between them is an executor that takes a second reading after its update, as TypeScript does (updateDirtyTransitions stamps at its own reading, and cycleNowMs, taken after it, is shared by the deadline step and the pass, typescript/src/runtime/bitmap-net-executor.ts). TIME_014_twoReadings shows the reference start a Delayed(3000) transition in the cycle whose update armed it at reading 0 and whose deadline step ran at 3000. A pass that takes a reading of its own when it begins and judges readiness there breaks line 1 at the reading line 3 fixes (TIME_014_forbids_passReread). Such a third reading is the behaviour RD-16 in spec/runtime-defects.md recorded for Java's fireReadyGeneral; Java's pass judges at its cycle reading (fireReadyTransitions(cycleNanos)). How the deadline step and the park decision use the reading is TIME-013's companion and CONC-010's, not this block's."
          "The first quoted sentence introduces the bullets; the bullet 'Higher priority transitions are preferred.' is EXEC-002's priority sort, which line 1 applies to the pass. The second bullet is read as ruling D9 (b) restricts it, to a Delayed transition before its earliest bound, whatever the priorities; once both are ready the order of EXEC-002 applies, stamp included. Read as an ordering rule, Immediate before Delayed whenever priorities are equal, it contradicts EXEC-002 (TIME_014_bullet2_order_conflicts_EXEC_002, ClashesTime.lean), and an executor that offers Immediate first breaks line 1 when the Delayed transition was armed first (TIME_014_forbids_immediateFirst). The third bullet, the fallback, is AC2: the fallback starts in the first pass whose cycle reading is at or after its earliest bound, if it is still armed (its clock not restarted, TIME-012) and the high-priority transition is not also ready in that pass."
          "AC1 (T1 with priority 10 and Immediate, also taking an event token from a second input place that holds one, and T2 with priority -10 and Delayed(3s), on one shared input; T1 fires first) is checked on the reference: in the first pass T2 is armed but not in the order, and T1 starts (TIME_014_nonvacuous). AC2 is read with the scenario of ruling D9 (b) and R-EXEC-5 (b), the requirement's own test derivation (the primary action waits for an event): T1's event place stays empty, so T1 is not enabled, T2 is armed at 0, the pass at reading 0 offers nothing, the executor waits with a timer of 3000 ms, and at cycle reading 3000 the order is T2 alone and T2 starts. The reading where T1 is in flight when a new token arrives holds on Java and TypeScript only (on Rust T1 starts again), so it is not used."
          "AC2's 'becomes ready and fires' is these lines together with two requirements outside the block. Line 3 makes a cycle whose update runs at or after 3000 judge at a reading not earlier, lines 1 and 2 put T2 in the order of its pass and offer it, and EXEC-003 line 3 forbids a lose of T2 while it is armed and enabled, so it starts. That a cycle runs at all once 3000 ms have passed, that is, that the wait wakes on its timer, is CONC-010's (step 6): an executor that parks for ever has only finite runs that stop before the bound, and every line holds of them. TIME_014_nonvacuous shows the reference doing it, and the update step at host reading 3000 that line 3 reads."
          "The test derivation (PrimaryAction with priority 10 and Immediate against FallbackAction with priority -10 and a delay of 3s) is the net of the AC1 and AC2 examples, transitions primary and fallback."
  signoff "2026-11-13 b3bcafa0d68de6a2 ai"
  statement : ∀ {N T : Type} [DecidableEq N], XRel N T → Prop :=
    fun R => (∀ C s s' tr,
      XRun R C s ((s, .begin, s') :: tr) →
        time014_offers (time014_pass tr) <+: time014_orderNames C s ∧
        ∀ w st, time014_close tr = (w, some st) → time014_isTerminal st = false →
          time014_offers w = time014_orderNames C s) ∧
      (∀ C s s' tr, XRun R C s ((s, .update, s') :: tr) →
        ∀ (mid : List (XStep _ _)) (c d : XSt _ _) rest, tr = mid ++ (c, .begin, d) :: rest →
          (∀ x ∈ mid, x.2.1 ≠ .update) → s.now ≤ c.cyc) ∧
      ∀ C s ns s' tr, XRun R C s ((s, .deadline ns, s') :: tr) →
        ∀ (mid : List (XStep _ _)) (c d : XSt _ _) rest, tr = mid ++ (c, .begin, d) :: rest →
          (∀ x ∈ mid, time014_rereads x.2.1 = false) → c.cyc = s'.cyc

/- The pinned readable form of TIME-014: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.TIME_014 : {N T : Type} → [DecidableEq N] → XRel N T → Prop :=
fun {N T} [DecidableEq N] R =>
  (∀ (C : Cfg N T) (s s' : XSt N T) (tr : List (XStep N T)),
      XRun R C s ((s, XLbl.begin, s') :: tr) →
        time014_offers (time014_pass tr) <+: time014_orderNames C s ∧
          ∀ (w : List (XStep N T)) (st : XStep N T),
            time014_close tr = (w, some st) →
              time014_isTerminal st = false → time014_offers w = time014_orderNames C s) ∧
    (∀ (C : Cfg N T) (s s' : XSt N T) (tr : List (XStep N T)),
        XRun R C s ((s, XLbl.update, s') :: tr) →
          ∀ (mid : List (XStep N T)) (c d : XSt N T) (rest : List (XSt N T × XLbl N T × XSt N T)),
            tr = mid ++ (c, XLbl.begin, d) :: rest → (∀ x ∈ mid, x.2.1 ≠ XLbl.update) → s.now ≤ c.cyc) ∧
      ∀ (C : Cfg N T) (s : XSt N T) (ns : List String) (s' : XSt N T) (tr : List (XStep N T)),
        XRun R C s ((s, XLbl.deadline ns, s') :: tr) →
          ∀ (mid : List (XStep N T)) (c d : XSt N T) (rest : List (XSt N T × XLbl N T × XSt N T)),
            tr = mid ++ (c, XLbl.begin, d) :: rest → (∀ x ∈ mid, time014_rereads x.2.1 = false) → c.cyc = s'.cyc
-/
#guard_msgs in #print TIME_014

/-! ### The reference -/

section Reference

variable {N T : Type} [DecidableEq N]

/-- A step that is not `begin`, `start` or `lose` keeps the pass's order: only the pass opening
sets it and only the pass's own steps take its head. -/
theorem time014_xstepW_order {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : xstepW P C s l = some s') (hb : l ≠ .begin) (hs : ∀ n sy, l ≠ .start n sy)
    (hl : ∀ n, l ≠ .lose n) : s'.order = s.order := by
  cases l with
  | begin => exact absurd rfl hb
  | start n sy => exact absurd rfl (hs n sy)
  | lose n => exact absurd rfl (hl n)
  | finish c =>
    cases c <;> simp only [xstepW] at h <;> split at h <;> simp at h <;> subst h <;> rfl
  | _ =>
    simp only [xstepW, writeStep, flushStep, retStep, expireStep, requestStep, drainStep,
      closeStep, terminateStep, commitStep, failStep, tdepositStep, depositAt, settle,
      publishStep, injectStep, discardStep, snapshotStep, parkStep, wakeStep, onOpen] at h
    all_goals (repeat' split at h) <;> (try simp at h) <;> (try (subst h; rfl))

/-- The window invariant of a reference run from `s` up to its first `begin`: the names offered
are a prefix of the names of `s`'s order, and all of them once an `endPass` comes. -/
theorem time014_window {C : Cfg N T} :
    ∀ (tr : List (XStep N T)) (s : XSt N T), XRun RefExec C s tr →
      time014_offers (time014_pass tr) <+: s.order.map (·.core.name) ∧
      ∀ w a b rest, time014_pass tr = w ++ (a, .endPass, b) :: rest →
        time014_offers w = s.order.map (·.core.name)
  | [], s, _ => ⟨by simp [time014_pass, time014_offers], fun w a b rest h => by
      simp [time014_pass] at h⟩
  | (s0, l, s1) :: tr, s, hr => by
    obtain ⟨rfl, hs, hr'⟩ := hr
    dsimp only at hs hr'
    have ih := time014_window tr s1 hr'
    cases l with
    | begin =>
      refine ⟨by simp [time014_pass, time014_isBegin, time014_offers], fun w a b rest h => ?_⟩
      simp [time014_pass, time014_isBegin] at h
    | start n sy =>
      obtain ⟨t, rest, ho, -, -, -, hn, -, -, h1⟩ := startStep_some hs
      have h1o : s1.order = rest := by rw [h1]
      rw [h1o] at ih
      subst hn
      refine ⟨?_, fun w a b rest' h => ?_⟩
      · simpa [time014_pass, time014_isBegin, time014_offers, time014_offered, ho] using ih.1
      · cases w with
        | nil => simp [time014_pass, time014_isBegin] at h
        | cons x w' =>
          simp only [time014_pass, time014_isBegin, Bool.false_eq_true, ↓reduceIte,
            List.cons_append, List.cons.injEq] at h
          obtain ⟨rfl, h'⟩ := h
          simpa [time014_offers, time014_offered, ho] using ih.2 w' a b rest' h'
    | lose n =>
      obtain ⟨t, rest, ho, -, -, -, hn, -, h1⟩ := loseStep_some hs
      have h1o : s1.order = rest := by rw [h1]
      rw [h1o] at ih
      subst hn
      refine ⟨?_, fun w a b rest' h => ?_⟩
      · simpa [time014_pass, time014_isBegin, time014_offers, time014_offered, ho] using ih.1
      · cases w with
        | nil => simp [time014_pass, time014_isBegin] at h
        | cons x w' =>
          simp only [time014_pass, time014_isBegin, Bool.false_eq_true, ↓reduceIte,
            List.cons_append, List.cons.injEq] at h
          obtain ⟨rfl, h'⟩ := h
          simpa [time014_offers, time014_offered, ho] using ih.2 w' a b rest' h'
    | endPass =>
      have h0 : s0.order = [] := (xstepW_endPass hs).2.2.1
      have ho : s1.order = s0.order := time014_xstepW_order hs nofun nofun nofun
      rw [ho, h0] at ih
      refine ⟨?_, fun w a b rest' h => ?_⟩
      · simpa [time014_pass, time014_isBegin, time014_offers, time014_offered, h0] using ih.1
      · cases w with
        | nil => simp [time014_offers, h0]
        | cons x w' =>
          simp only [time014_pass, time014_isBegin, Bool.false_eq_true, ↓reduceIte,
            List.cons_append, List.cons.injEq] at h
          obtain ⟨rfl, h'⟩ := h
          simpa [time014_offers, time014_offered, h0] using ih.2 w' a b rest' h'
    | _ =>
      have ho : s1.order = s0.order := time014_xstepW_order hs nofun nofun nofun
      rw [ho] at ih
      refine ⟨?_, fun w a b rest' h => ?_⟩
      · simpa [time014_pass, time014_isBegin, time014_offers, time014_offered] using ih.1
      · cases w with
        | nil => simp [time014_pass, time014_isBegin] at h
        | cons x w' =>
          simp only [time014_pass, time014_isBegin, Bool.false_eq_true, ↓reduceIte,
            List.cons_append, List.cons.injEq] at h
          obtain ⟨rfl, h'⟩ := h
          simpa [time014_offers, time014_offered] using ih.2 w' a b rest' h'

/-- A step whose label a pass can hold keeps the reference in phase `pass`. -/
theorem time014_inPass_phase {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : xstepW P C s l = some s') (hp : s.phase = .pass) (hin : time014_inPass l = true) :
    s'.phase = .pass := by
  cases l with
  | start n sy =>
    obtain ⟨t, rest, -, -, -, -, -, -, -, h1⟩ := startStep_some h
    rw [h1]; exact hp
  | lose n =>
    obtain ⟨t, rest, -, -, -, -, -, -, h1⟩ := loseStep_some h
    rw [h1]; exact hp
  | commit i =>
    simp only [xstepW, commitStep] at h
    repeat' split at h
    all_goals (try simp at h)
    subst h; simp [depositAt, settle, hp]
  | fail i =>
    simp only [xstepW, failStep] at h
    repeat' split at h
    all_goals (try simp at h)
    subst h; simp [settle, hp]
  | tdeposit i =>
    simp only [xstepW, tdepositStep] at h
    repeat' split at h
    all_goals (try simp at h)
    subst h; simp [depositAt, settle, hp]
  | _ =>
    rw [(xstepW_outside_frame h (by simpa [time014_inPass] using hin)).2.2.1]; exact hp

/-- From phase `pass`, the only reference steps whose label a pass cannot hold are `endPass`
and a terminal finish. -/
theorem time014_inPass_close {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : xstepW P C s l = some s') (hp : s.phase = .pass) (hin : time014_inPass l = false) :
    l = .endPass ∨ l = .finish .terminal := by
  cases l with
  | endPass => exact Or.inl rfl
  | finish c =>
    cases c with
    | terminal => exact Or.inr rfl
    | _ => simp [xstepW, hp] at h
  | publish i =>
    simp only [xstepW, publishStep] at h
    repeat' split at h
    all_goals simp_all
  | inject k =>
    simp only [xstepW, injectStep] at h
    repeat' split at h
    all_goals simp_all
  | discard k =>
    simp only [xstepW, discardStep] at h
    repeat' split at h
    all_goals simp_all
  | snapshot a => simp [xstepW, snapshotStep, hp] at h
  | park tmr => simp [xstepW, parkStep, hp] at h
  | wake => simp [xstepW, wakeStep, hp] at h
  | delay _ | write _ _ _ | flush _ | ret _ _ | expire _ _ | request _ _ _ | drain | close
  | terminateNow | start _ _ | lose _ | commit _ | fail _ | tdeposit _ =>
    simp [time014_inPass, XLbl.outside] at hin
  | _ => simp [xstepW, hp] at h

/-- The close of a reference run from phase `pass`: the steps before it offer the whole of the
order, unless it is a terminal finish. -/
theorem time014_close_ref {C : Cfg N T} :
    ∀ (tr : List (XStep N T)) (s : XSt N T), XRun RefExec C s tr → s.phase = .pass →
      ∀ w st, time014_close tr = (w, some st) → time014_isTerminal st = false →
        time014_offers w = s.order.map (·.core.name)
  | [], _, _, _, _, _, h, _ => by simp [time014_close] at h
  | (s0, l, s1) :: tr, s, hr, hp, w, st, h, ht => by
    obtain ⟨rfl, hs, hr'⟩ := hr
    dsimp only at hs hr'
    by_cases hin : time014_inPass l = true
    · simp only [time014_close, hin, ↓reduceIte, Prod.mk.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      have ih := time014_close_ref tr s1 hr' (time014_inPass_phase hs hp hin) _ st
        (Prod.ext rfl h2) ht
      cases l with
      | start n sy =>
        obtain ⟨t, rest, ho, -, -, -, hn, -, -, h1⟩ := startStep_some hs
        have h1o : s1.order = rest := by rw [h1]
        rw [h1o] at ih
        subst hn
        simpa [time014_offers, time014_offered, ho] using ih
      | lose n =>
        obtain ⟨t, rest, ho, -, -, -, hn, -, h1⟩ := loseStep_some hs
        have h1o : s1.order = rest := by rw [h1]
        rw [h1o] at ih
        subst hn
        simpa [time014_offers, time014_offered, ho] using ih
      | begin => simp [time014_inPass, XLbl.outside] at hin
      | _ =>
        rw [time014_xstepW_order hs nofun nofun nofun] at ih
        simpa [time014_offers, time014_offered] using ih
    · simp only [time014_close, hin, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq,
        Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rcases time014_inPass_close hs hp (by simpa using hin) with rfl | rfl
      · simp [time014_offers, (xstepW_endPass hs).2.2.1]
      · simp [time014_isTerminal] at ht

/-- No reference step other than the update and the deadline step changes the cycle reading. -/
theorem time014_xstepW_cyc {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : xstepW P C s l = some s') (hu : time014_rereads l = false) : s'.cyc = s.cyc := by
  cases l with
  | update => simp [time014_rereads] at hu
  | deadline ns => simp [time014_rereads] at hu
  | begin => rw [(xstepW_begin h).2.2.2.2]
  | start n sy =>
    obtain ⟨t, rest, -, -, -, -, -, -, -, h1⟩ := startStep_some h
    rw [h1]
  | lose n =>
    obtain ⟨t, rest, -, -, -, -, -, -, h1⟩ := loseStep_some h
    rw [h1]
  | endPass => rw [(xstepW_endPass h).2.2.2.2]
  | finish c =>
    cases c <;> simp only [xstepW] at h <;> split at h <;> simp at h <;> subst h <;> rfl
  | _ =>
    simp only [xstepW, writeStep, flushStep, retStep, expireStep, requestStep, drainStep,
      closeStep, terminateStep, commitStep, failStep, tdepositStep, depositAt, settle,
      publishStep, injectStep, discardStep, snapshotStep, parkStep, wakeStep, onOpen] at h
    all_goals (repeat' split at h) <;> (try simp at h) <;> (try (subst h; rfl))

/-- No reference step other than the update moves the cycle reading back: the deadline step takes
a reading that is not earlier ([TIME-010], ruling D61 (c)). -/
theorem time014_xstepW_cyc_le {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : xstepW P C s l = some s') (hu : l ≠ .update) : s.cyc ≤ s'.cyc := by
  cases l with
  | update => exact absurd rfl hu
  | deadline ns =>
    obtain ⟨-, -, -, rfl⟩ := xstepW_deadline h
    exact Nat.le_max_left _ _
  | _ => exact Nat.le_of_eq (time014_xstepW_cyc h rfl).symm

/-- In a reference run, the cycle reading at a `begin` is not earlier than the reading at the
start of the run, as long as no update comes between. -/
theorem time014_cyc_le_ref {C : Cfg N T} {c d : XSt N T} {rest : List (XStep N T)} :
    ∀ (mid : List (XStep N T)) (s : XSt N T), XRun RefExec C s (mid ++ (c, .begin, d) :: rest) →
      (∀ x ∈ mid, x.2.1 ≠ .update) → s.cyc ≤ c.cyc
  | [], s, hr, _ => by
    obtain ⟨rfl, -⟩ := hr
    exact Nat.le_refl _
  | (s0, l, s1) :: mid, s, hr, hu => by
    obtain ⟨rfl, hs, hr'⟩ := hr
    dsimp only at hs hr'
    exact Nat.le_trans (time014_xstepW_cyc_le hs (hu _ List.mem_cons_self))
      (time014_cyc_le_ref mid s1 hr' fun x hx => hu x (List.mem_cons_of_mem _ hx))

/-- In a reference run, the cycle reading at a `begin` is the reading at the start of the run, as
long as no update and no deadline step comes between. -/
theorem time014_cyc_ref {C : Cfg N T} {c d : XSt N T} {rest : List (XStep N T)} :
    ∀ (mid : List (XStep N T)) (s : XSt N T), XRun RefExec C s (mid ++ (c, .begin, d) :: rest) →
      (∀ x ∈ mid, time014_rereads x.2.1 = false) → c.cyc = s.cyc
  | [], s, hr, _ => by
    obtain ⟨rfl, -⟩ := hr
    rfl
  | (s0, l, s1) :: mid, s, hr, hu => by
    obtain ⟨rfl, hs, hr'⟩ := hr
    dsimp only at hs hr'
    rw [time014_cyc_ref mid s1 hr' fun x hx => hu x (List.mem_cons_of_mem _ hx)]
    exact time014_xstepW_cyc hs (hu _ List.mem_cons_self)

end Reference

/-- ✓ The reference executor satisfies TIME-014: its `begin` step sets the pass's order to
`readyOrder` (`xstepW_begin`), `start` and `lose` take the head (`startStep_some`,
`loseStep_some`), no other step changes the order (`time014_xstepW_order`), and `endPass` needs it
empty (`time014_window`). -/
@[evidence holds TIME_014]
theorem TIME_014_reference {N T : Type} [DecidableEq N] :
    TIME_014 (RefExec (N := N) (T := T)) := by
  refine ⟨fun C s s' tr hr => ?_, fun C s s' tr hr mid c d rest htr hu => ?_,
    fun C s ns s' tr hr mid c d rest htr hu => ?_⟩
  · obtain ⟨-, hb, hr'⟩ := hr
    dsimp only at hb hr'
    have hb' := xstepW_begin hb
    have ho : s'.order = readyOrder C s := by rw [hb'.2.2.2.2]
    have hp : s'.phase = .pass := by rw [hb'.2.2.2.2]
    have := time014_window tr s' hr'
    rw [ho] at this
    refine ⟨this.1, fun w st h ht => ?_⟩
    have := time014_close_ref tr s' hr' hp w st h ht
    rwa [ho] at this
  · obtain ⟨-, hs, hr'⟩ := hr
    dsimp only at hs hr'
    subst htr
    have h1 : s'.cyc = s.now := by
      simp only [RefExec, xstep, xstepW] at hs
      split at hs
      · cases hs; rfl
      · simp at hs
    rw [← h1]
    exact time014_cyc_le_ref mid s' hr' hu
  · obtain ⟨-, -, hr'⟩ := hr
    dsimp only at hr'
    subst htr
    exact time014_cyc_ref mid s' hr' hu

/-! ### What the block gives for the second shall sentence -/

section Gate

variable {N T : Type} [DecidableEq N]

/-- A transition of the ready order is a transition of the net, and it is Ready (glossary) in the
timed view at the cycle reading: the order of [EXEC-002] holds only ready transitions
(`EXEC_002_reference`, line 1). -/
theorem time014_readyOrder_ready {C : Cfg N T} {s : XSt N T} {t : Trans N}
    (ht : t ∈ readyOrder C s) :
    t ∈ C.X.net.transitions ∧ Ready C.X (viewAt s s.cyc) t := by
  unfold readyOrder at ht
  simp only [List.mem_filterMap] at ht
  obtain ⟨i, hi, hti⟩ := ht
  have hmem := ((EXEC_002_reference _).1.mem_iff).1 hi
  rw [ReadyIn.mem_readyList] at hmem
  obtain ⟨hlt, hrd⟩ := hmem
  have hlt' : i < C.X.net.transitions.length := hlt
  rw [List.getElem?_eq_getElem hlt', Option.some.injEq] at hti
  subst hti
  exact ⟨List.getElem_mem hlt', (ReadyIn.ofTSt_ready _ _ _ _ i hlt').1 hrd⟩

/-- For every executor satisfying TIME-014: a transition started in a pass is in the pass's ready
order and was Ready at the cycle reading of the pass, so its elapsed time was at least its
earliest bound (the first clause of the second shall sentence). -/
theorem TIME_014_started_ready {R : XRel N T} (h : TIME_014 R) {C : Cfg N T} {s s' : XSt N T}
    {tr : List (XStep N T)} (hr : XRun R C s ((s, .begin, s') :: tr)) {a b : XSt N T}
    {n : String} {sy : Bool} (hn : (a, .start n sy, b) ∈ time014_pass tr) :
    ∃ t ∈ readyOrder C s, t.core.name = n ∧ Ready C.X (viewAt s s.cyc) t := by
  have h1 : n ∈ time014_offers (time014_pass tr) := List.mem_filterMap.2 ⟨_, hn, rfl⟩
  have h2 := (h.1 C s s' tr hr).1.subset h1
  simp only [time014_orderNames, List.mem_map] at h2
  obtain ⟨t, ht, rfl⟩ := h2
  exact ⟨t, ht, rfl, (time014_readyOrder_ready ht).2⟩

/-- For every executor satisfying TIME-014, under distinct names (ruling D10): a transition of the
net whose elapsed time at the cycle reading of a pass is below its earliest bound does not start
in that pass. -/
theorem TIME_014_not_before_earliest {R : XRel N T} (h : TIME_014 R) {C : Cfg N T}
    (hN : NamesDistinct C.X) {u : Trans N} (hu : u ∈ C.X.net.transitions) {s s' : XSt N T}
    {tr : List (XStep N T)} (hr : XRun R C s ((s, .begin, s') :: tr))
    (hlow : Elapsed (viewAt s s.cyc) u < (TimingOf C.X u).earliest) (a b : XSt N T) (sy : Bool) :
    (a, .start u.core.name sy, b) ∉ time014_pass tr := by
  intro hn
  obtain ⟨t, ht, hname, hready⟩ := TIME_014_started_ready h hr hn
  have htu : t = u := List.inj_on_of_nodup_map hN (time014_readyOrder_ready ht).1 hu hname
  subst htu
  exact absurd hready.2.1 (by omega)

end Gate

/-! ### Decided runs of a step function -/

section Runs

variable {N T : Type}

/-- Run the labels `ls` from `s` with the step function `g`. -/
def time014_run (g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)) (C : Cfg N T) :
    XSt N T → List (XLbl N T) → Option (XSt N T)
  | s, [] => some s
  | s, l :: ls => (g C s l).bind fun s' => time014_run g C s' ls

/-- The trace of steps of the labels `ls` from `s` with the step function `g`. -/
def time014_trace (g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)) (C : Cfg N T) :
    XSt N T → List (XLbl N T) → Option (List (XStep N T))
  | _, [] => some []
  | s, l :: ls => (g C s l).bind fun s' => (time014_trace g C s' ls).map ((s, l, s') :: ·)

/-- A trace `time014_trace` builds is a run of the graph of `g`, with the labels it was given. -/
theorem time014_trace_run {g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)} {C : Cfg N T} :
    ∀ {s : XSt N T} {ls : List (XLbl N T)} {tr : List (XStep N T)},
      time014_trace g C s ls = some tr →
        XRun (fun C s l s' => g C s l = some s') C s tr ∧ tr.map (·.2.1) = ls
  | s, [], tr, h => by cases h; exact ⟨trivial, rfl⟩
  | s, l :: ls, tr, h => by
    simp only [time014_trace] at h
    cases hs : g C s l with
    | none => simp [hs] at h
    | some s' =>
      simp only [hs, Option.bind_some] at h
      cases ht : time014_trace g C s' ls with
      | none => simp [ht] at h
      | some tr' =>
        simp only [ht, Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨hr, hl⟩ := time014_trace_run ht
        exact ⟨⟨rfl, hs, hr⟩, by simp [hl]⟩

/-- A pass scene: run `pre` from `s0`, then `begin`, then trace `body`; the state before the
`begin`, the state after it, and the trace of `body`. -/
def time014_scene (g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)) (C : Cfg N T)
    (s0 : XSt N T) (pre body : List (XLbl N T)) :
    Option (XSt N T × XSt N T × List (XStep N T)) :=
  (time014_run g C s0 pre).bind fun s =>
    (g C s .begin).bind fun s' => (time014_trace g C s' body).map fun tr => (s, s', tr)

/-- Read a decided check `p` off a pass scene: the scene is a run of the graph of `g` that opens
with the `begin` step, with the labels of `body` after it. -/
theorem time014_scene_check (g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T))
    {C : Cfg N T} {s0 : XSt N T} {pre body : List (XLbl N T)}
    {p : XSt N T → XSt N T → List (XStep N T) → Bool}
    (h : (time014_scene g C s0 pre body).map (fun x => p x.1 x.2.1 x.2.2) = some true) :
    ∃ s s' tr, XRun (fun C s l s' => g C s l = some s') C s ((s, .begin, s') :: tr) ∧
      tr.map (·.2.1) = body ∧ p s s' tr = true := by
  unfold time014_scene at h
  cases h1 : time014_run g C s0 pre with
  | none => simp [h1] at h
  | some s =>
    cases h2 : g C s .begin with
    | none => simp [h1, h2] at h
    | some s' =>
      cases h3 : time014_trace g C s' body with
      | none => simp [h1, h2, h3] at h
      | some tr =>
        simp only [h1, h2, h3, Option.bind_some, Option.map_some, Option.some.injEq] at h
        obtain ⟨hr, hl⟩ := time014_trace_run h3
        exact ⟨s, s', tr, ⟨rfl, h2, hr⟩, hl, h⟩

/-- Read a decided check `p` off a run of the labels `body`, from the state the labels `pre`
lead to from `s0`. -/
theorem time014_from_check (g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T))
    {C : Cfg N T} {s0 : XSt N T} {pre body : List (XLbl N T)}
    {p : XSt N T → List (XStep N T) → Bool}
    (h : (time014_run g C s0 pre).bind (fun s => (time014_trace g C s body).map (p s)) =
      some true) :
    ∃ s tr, XRun (fun C s l s' => g C s l = some s') C s tr ∧ tr.map (·.2.1) = body ∧
      p s tr = true := by
  cases h1 : time014_run g C s0 pre with
  | none => simp [h1] at h
  | some s =>
    cases h2 : time014_trace g C s body with
    | none => simp [h1, h2] at h
    | some tr =>
      simp only [h1, h2, Option.bind_some, Option.map_some, Option.some.injEq] at h
      obtain ⟨hr, hl⟩ := time014_trace_run h2
      exact ⟨s, tr, hr, hl, h⟩

end Runs

/-! ### The pass's order, set by the `begin` step

The reference sorts the ready transitions with `List.mergeSort`, which the kernel does not
evaluate on two or more elements. The decided runs below therefore use an executor whose `begin`
step takes an order checked against EXEC-002 without sorting (`time014_orderAs`); it is the
reference executor (`time014_orderAs_eq`, `time014_withOrder_ready`). -/

section Orders

variable {N T : Type} [DecidableEq N]

/-- The reference executor, except that the `begin` step sets the pass's order to `f C s`. -/
def time014_withOrder (f : Cfg N T → XSt N T → List (Trans N)) (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .begin => (xstep C s .begin).map fun s1 => { s1 with order := f C s }
  | l => xstep C s l

/-- The executor of `time014_withOrder f`. -/
def time014_exec (f : Cfg N T → XSt N T → List (Trans N)) : XRel N T :=
  fun C s l s' => time014_withOrder f C s l = some s'

/-- With the ready order, `time014_withOrder` is the reference step. -/
theorem time014_withOrder_ready (C : Cfg N T) (s : XSt N T) (l : XLbl N T) :
    time014_withOrder readyOrder C s l = xstep C s l := by
  cases l with
  | begin =>
    simp only [time014_withOrder]
    cases h : xstep C s .begin with
    | none => rfl
    | some s1 =>
      have e := (xstepW_begin h).2.2.2.2
      subst e
      rfl
  | _ => rfl

/-- Is `L` (declaration indices) the ready order of [EXEC-002] at `s`? Checked without sorting:
on the fast path `L` is the ready list, otherwise a permutation of it sorted by the key. -/
def time014_isOrder (C : Cfg N T) (s : XSt N T) (L : List Nat) : Bool :=
  let I := ReadyIn.ofTSt C.X C.prio (viewAt s s.cyc) C.X.net.transitions
  if I.FastPath then L == I.readyList else L.isPerm I.readyList && decide (L.Pairwise I.key.lt)

/-- A checked `L` is the ready order (`EXEC_002_forced`). -/
theorem time014_isOrder_eq {C : Cfg N T} {s : XSt N T} {L : List Nat}
    (h : time014_isOrder C s L = true) :
    readyOrder C s = L.filterMap (C.X.net.transitions[·]?) := by
  unfold time014_isOrder at h
  unfold readyOrder
  simp only at h ⊢
  congr 1
  by_cases hf : (ReadyIn.ofTSt C.X C.prio (viewAt s s.cyc) C.X.net.transitions).FastPath
  · rw [if_pos hf] at h
    simp only [refReadyOrder, if_pos hf]
    exact (beq_iff_eq.1 h).symm
  · rw [if_neg hf] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at h
    exact EXEC_002_forced EXEC_002_reference hf h.1 h.2

/-- The order `L` where the check accepts it, the ready order elsewhere. -/
def time014_orderAs (L : List Nat) (C : Cfg N T) (s : XSt N T) : List (Trans N) :=
  if time014_isOrder C s L then L.filterMap (C.X.net.transitions[·]?) else readyOrder C s

/-- `time014_orderAs L` is the ready order. -/
theorem time014_orderAs_eq (L : List Nat) (C : Cfg N T) (s : XSt N T) :
    time014_orderAs L C s = readyOrder C s := by
  unfold time014_orderAs
  split
  · exact (time014_isOrder_eq ‹_›).symm
  · rfl

/-- A run of the executor with order `time014_orderAs L` is a run of the reference executor. -/
theorem time014_run_ref {L : List Nat} {C : Cfg N T} {s : XSt N T} {tr : List (XStep N T)}
    (h : XRun (fun C s l s' => time014_withOrder (time014_orderAs L) C s l = some s') C s tr) :
    XRun RefExec C s tr := by
  have e : (fun C s l s' => time014_withOrder (time014_orderAs L) C s l = some s') =
      (RefExec : XRel N T) := by
    funext C s l s'
    have hf : time014_orderAs (N := N) (T := T) L = readyOrder :=
      funext fun C => funext fun s => time014_orderAs_eq L C s
    rw [hf]
    simp only [time014_withOrder_ready]
    rfl
  rwa [e] at h

/-- The executor whose `begin` step sets the order to `F C s` of the ready order. -/
def time014_post (F : Cfg N T → XSt N T → List (Trans N) → List (Trans N)) :
    Cfg N T → XSt N T → List (Trans N) :=
  fun C s => F C s (readyOrder C s)

/-- A run of the executor of `F` over `time014_orderAs L` is a run of the executor of `F` over
the ready order. -/
theorem time014_run_post {F : Cfg N T → XSt N T → List (Trans N) → List (Trans N)}
    {L : List Nat} {C : Cfg N T} {s : XSt N T} {tr : List (XStep N T)}
    (h : XRun (fun C s l s' =>
      time014_withOrder (fun C s => F C s (time014_orderAs L C s)) C s l = some s') C s tr) :
    XRun (time014_exec (time014_post F)) C s tr := by
  simp only [time014_orderAs_eq] at h
  exact h

end Orders

/-! ### Examples

Places: `0` the contested input, `1` a second input (an event place where the scenario injects).
Timings are in milliseconds: `Delayed(3s)` is `delayed 3000`. No transition has an output spec,
and validation accepts everything; the examples stop at the end of the pass. -/

/-- A transition named `n` taking one token from each place of `ins`, without an output spec. -/
def time014_tr (n : String) (ins : List Nat) : Trans Nat :=
  { core := { name := n, inputs := ins.map fun p => ⟨p, .one⟩, inhibitors := [], reads := [],
              resets := [] },
    out := none }

/-- The configuration of an example: transitions `ts`, timing and priority by name, environment
places `envs`. -/
def time014_cfg (ts : List (Trans Nat)) (tm : String → Timing) (pr : String → Int)
    (envs : List Nat) : Cfg Nat Nat :=
  { X := { net := { places := [0, 1], transitions := ts }, timing := fun t => tm t.core.name,
           tol := 0 },
    prio := fun t => pr t.core.name, terminals := [], envs := envs, reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => false,
    res := 0 }

/-- The test derivation's net (AC1, AC2): `primary` (priority 10, `Immediate`) takes a token from
`0` and an event token from `1`; `fallback` (priority -10, `Delayed(3s)`) takes a token from
`0`. -/
def time014_cAC : Cfg Nat Nat :=
  time014_cfg [time014_tr "primary" [0, 1], time014_tr "fallback" [0]]
    (fun n => if n = "fallback" then .delayed 3000 else .immediate)
    (fun n => if n = "primary" then 10 else -10) []

/-- Competition: `hi` (priority 10) and `lo` (priority -10), both `Immediate`, on one token. -/
def time014_cHL : Cfg Nat Nat :=
  time014_cfg [time014_tr "hi" [0], time014_tr "lo" [0]] (fun _ => .immediate)
    (fun n => if n = "hi" then 10 else -10) []

/-- "Whatever their priorities": `slow` (priority 10, `Delayed(3s)`) and `quick` (priority -10,
`Immediate`) on one token. -/
def time014_cWP : Cfg Nat Nat :=
  time014_cfg [time014_tr "slow" [0], time014_tr "quick" [0]]
    (fun n => if n = "slow" then .delayed 3000 else .immediate)
    (fun n => if n = "slow" then 10 else -10) []

/-- Ruling D9: `slow` (`Delayed(3s)`) and `quick` (`Immediate`, also taking an event token from
the environment place `1`), equal priority. -/
def time014_cD9 : Cfg Nat Nat :=
  time014_cfg [time014_tr "slow" [0], time014_tr "quick" [0, 1]]
    (fun n => if n = "slow" then .delayed 3000 else .immediate) (fun _ => 0) [1]

/-- Three `Immediate` transitions of priority 0 (the all-immediate fast path, declaration
order): `x` takes the token of `1`, `y` the tokens of `0` and `1`, `z` the token of `0`; `y` and
`z` compete for the token of `0`. -/
def time014_cXYZ : Cfg Nat Nat :=
  time014_cfg [time014_tr "x" [1], time014_tr "y" [0, 1], time014_tr "z" [0]]
    (fun _ => .immediate) (fun _ => 0) []

/-- One token in `0`. -/
def time014_m0 : QMarking Nat Nat := fun p => if p = 0 then [7] else []

/-- One token in `0` and one in `1`. -/
def time014_m01 : QMarking Nat Nat := fun p => if p = 0 then [7] else if p = 1 then [8] else []

/-- Steps 1 to 4 of a cycle with nothing to settle, publish or inject. -/
def time014_cyc : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline []]

/-- AC2 up to the second pass: the pass at reading 0 offers nothing, the executor waits with a
timer of 3000, and the next cycle runs at reading 3000. -/
def time014_preAC2 : List (XLbl Nat Nat) :=
  time014_cyc ++ [.begin, .endPass, .park (some 3000), .delay 3000, .wake] ++ time014_cyc

/-- Ruling D9 up to the second pass: `slow` is armed at 0; at 3000 an event token for `quick` is
accepted and injected, and the update arms `quick` at 3000. -/
def time014_preD9 : List (XLbl Nat Nat) :=
  time014_cyc ++ [.begin, .endPass, .delay 3000, .request 1 9 .accepted, .wake, .endCompletions,
    .endPublications, .inject 0, .endEvents, .update, .deadline []]

/-- The transition `fallback` of the AC net. -/
def time014_fallback : Trans Nat := time014_tr "fallback" [0]

/-- The transition `slow` of the "whatever their priorities" net. -/
def time014_slow : Trans Nat := time014_tr "slow" [0]

/-- Every line of TIME-014 is exercised by the reference, each pass read up to its end:
* two `Immediate` transitions on one token, priority 10 and -10: the order is both, the one of
  priority 10 starts and the other loses (first shall sentence; lines 1 and 2);
* a `Delayed(3s)` transition of priority 10, armed at 0, and an `Immediate` one of priority -10
  on one token: only the `Immediate` one is in the order, and it starts (second shall sentence,
  "whatever their priorities");
* AC1: `primary` and `fallback` both enabled at 0: the order is `primary` alone, `fallback` is
  armed and not offered, `primary` starts;
* AC2, ruling D9 (b): `primary`'s event place empty: at reading 0 the order is empty while
  `fallback` is armed; at cycle reading 3000 the order is `fallback`, and it starts;
* ruling D9: once a `Delayed` transition armed at 0 and an `Immediate` one armed at 3000 are both
  ready with equal priority, the `Delayed` one is offered first (stamp order of [EXEC-002]). -/
@[evidence nonvacuous TIME_014]
theorem TIME_014_nonvacuous :
    (∃ s s' tr, XRun RefExec time014_cHL s ((s, .begin, s') :: tr) ∧
      tr.map (·.2.1) = [.start "hi" false, .lose "lo", .endPass] ∧
      time014_orderNames time014_cHL s = ["hi", "lo"]) ∧
    (∃ s s' tr, XRun RefExec time014_cWP s ((s, .begin, s') :: tr) ∧
      tr.map (·.2.1) = [.start "quick" false, .endPass] ∧
      time014_orderNames time014_cWP s = ["quick"] ∧ (viewAt s s.cyc).armed time014_slow = true) ∧
    (∃ s s' tr, XRun RefExec time014_cAC s ((s, .begin, s') :: tr) ∧
      tr.map (·.2.1) = [.start "primary" false, .endPass] ∧
      time014_orderNames time014_cAC s = ["primary"] ∧
      (viewAt s s.cyc).armed time014_fallback = true) ∧
    (∃ s s' tr, XRun RefExec time014_cAC s ((s, .begin, s') :: tr) ∧
      tr.map (·.2.1) = [.endPass] ∧ time014_orderNames time014_cAC s = [] ∧
      (viewAt s s.cyc).armed time014_fallback = true) ∧
    (∃ s s' tr, XRun RefExec time014_cAC s ((s, .begin, s') :: tr) ∧
      tr.map (·.2.1) = [.start "fallback" false, .endPass] ∧
      time014_orderNames time014_cAC s = ["fallback"] ∧ s.cyc = 3000) ∧
    (∃ s s' tr, XRun RefExec time014_cD9 s ((s, .begin, s') :: tr) ∧
      tr.map (·.2.1) = [.start "slow" false, .lose "quick", .endPass] ∧
      time014_orderNames time014_cD9 s = ["slow", "quick"]) ∧
    (∃ s s1 s2 s3, XRun RefExec time014_cAC s
        [(s, .update, s1), (s1, .deadline [], s2), (s2, .begin, s3)] ∧
      s.now = 3000 ∧ s2.cyc = 3000) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨s, s', tr, hr, hl, hp⟩ := time014_scene_check
      (time014_withOrder (time014_orderAs [0, 1])) (C := time014_cHL)
      (s0 := xinit time014_m0 0) (pre := time014_cyc)
      (body := [.start "hi" false, .lose "lo", .endPass])
      (p := fun s _ _ => (time014_orderAs [0, 1] time014_cHL s).map (·.core.name) == ["hi", "lo"])
      (by decide +kernel)
    rw [time014_orderAs_eq] at hp
    exact ⟨s, s', tr, time014_run_ref hr, hl, by simpa [time014_orderNames] using hp⟩
  · obtain ⟨s, s', tr, hr, hl, hp⟩ := time014_scene_check xstep (C := time014_cWP)
      (s0 := xinit time014_m0 0) (pre := time014_cyc) (body := [.start "quick" false, .endPass])
      (p := fun s _ _ => time014_orderNames time014_cWP s == ["quick"] &&
        (viewAt s s.cyc).armed time014_slow) (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', tr, hr, hl, hp⟩
  · obtain ⟨s, s', tr, hr, hl, hp⟩ := time014_scene_check xstep (C := time014_cAC)
      (s0 := xinit time014_m01 0) (pre := time014_cyc) (body := [.start "primary" false, .endPass])
      (p := fun s _ _ => time014_orderNames time014_cAC s == ["primary"] &&
        (viewAt s s.cyc).armed time014_fallback) (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', tr, hr, hl, hp⟩
  · obtain ⟨s, s', tr, hr, hl, hp⟩ := time014_scene_check xstep (C := time014_cAC)
      (s0 := xinit time014_m0 0) (pre := time014_cyc) (body := [.endPass])
      (p := fun s _ _ => time014_orderNames time014_cAC s == [] &&
        (viewAt s s.cyc).armed time014_fallback) (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', tr, hr, hl, hp⟩
  · obtain ⟨s, s', tr, hr, hl, hp⟩ := time014_scene_check xstep (C := time014_cAC)
      (s0 := xinit time014_m0 0) (pre := time014_preAC2)
      (body := [.start "fallback" false, .endPass])
      (p := fun s _ _ => time014_orderNames time014_cAC s == ["fallback"] && s.cyc == 3000)
      (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', tr, hr, hl, hp⟩
  · obtain ⟨s, s', tr, hr, hl, hp⟩ := time014_scene_check
      (time014_withOrder (time014_orderAs [0, 1])) (C := time014_cD9)
      (s0 := xinit time014_m0 0) (pre := time014_preD9)
      (body := [.start "slow" false, .lose "quick", .endPass])
      (p := fun s _ _ =>
        (time014_orderAs [0, 1] time014_cD9 s).map (·.core.name) == ["slow", "quick"])
      (by decide +kernel)
    rw [time014_orderAs_eq] at hp
    exact ⟨s, s', tr, time014_run_ref hr, hl, by simpa [time014_orderNames] using hp⟩
  · obtain ⟨s, tr, hr, hl, hp⟩ := time014_from_check xstep (C := time014_cAC)
      (s0 := xinit time014_m0 0)
      (pre := time014_cyc ++ [.begin, .endPass, .park (some 3000), .delay 3000, .wake,
        .endCompletions, .endPublications, .endEvents])
      (body := [.update, .deadline [], .begin])
      (p := fun s tr => match tr with
        | [_, _, (c, _, _)] => s.now == 3000 && c.cyc == 3000
        | _ => false)
      (by decide +kernel)
    rcases tr with _ | ⟨⟨a1, l1, b1⟩, _ | ⟨⟨a2, l2, b2⟩, _ | ⟨⟨a3, l3, b3⟩, _ | ⟨_, _⟩⟩⟩⟩ <;>
      simp at hl
    obtain ⟨rfl, rfl, rfl⟩ := hl
    have ha : a1 = s := hr.1
    subst ha
    obtain ⟨-, h1, e2, h2, e3, h3, -⟩ := hr
    dsimp only at h1 e2 h2 e3 h3
    subst e2 e3
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨_, _, _, _, ⟨rfl, h1, rfl, h2, rfl, h3, trivial⟩, hp⟩

/-! ### Executors that order the pass otherwise -/

section Mutants

variable {N T : Type} [DecidableEq N]

/-- Insert `a` before the first element `b` with `le a b`. -/
def time014_ins {α : Type} (le : α → α → Bool) (a : α) : List α → List α
  | [] => [a]
  | b :: l => if le a b then a :: b :: l else b :: time014_ins le a l

/-- Insertion sort by `le`; on a tie the earlier element stays first. -/
def time014_isort {α : Type} (le : α → α → Bool) : List α → List α
  | [] => []
  | a :: l => time014_ins le a (time014_isort le l)

/-- Lower priority first: the ready order reversed. -/
def time014_lowFirst : Cfg N T → XSt N T → List (Trans N) → List (Trans N) :=
  fun _ _ o => o.reverse

/-- A gate one tick late: of the ready order, only the transitions whose elapsed time at the cycle
reading is past their earliest bound. -/
def time014_lateGate : Cfg N T → XSt N T → List (Trans N) → List (Trans N) :=
  fun C s o => o.filter fun t => decide ((C.X.timing t).earliest < (viewAt s s.cyc).elapsed t)

/-- The ordering reading of the old second bullet: the ready order sorted again, priority
descending, and among equal priority `Immediate` before `Delayed`, ties kept in place. -/
def time014_immFirst : Cfg N T → XSt N T → List (Trans N) → List (Trans N) :=
  fun C _ o => time014_isort (fun a b => decide (C.prio b < C.prio a) ||
    (decide (C.prio a = C.prio b) &&
      (decide (C.X.timing a = .immediate) || !decide (C.X.timing b = .immediate)))) o

/-- Every transition of the net by the canonical key of [EXEC-002], ready or not, as
`clash014_allOrder` (ClashesTime.lean) orders them: a transition below its earliest bound is
offered, and starts if it is armed and enabled. -/
def time014_allOrder (C : Cfg N T) (s : XSt N T) : List (Trans N) :=
  let ts := C.X.net.transitions
  let I := ReadyIn.ofTSt C.X C.prio (viewAt s s.cyc) ts
  (time014_isort (fun a b => !decide (I.key.lt b a)) (List.range I.n)).filterMap (ts[·]?)

/-- A pass that breaks at its first `lose`: `break` for `continue` in the Phase 5 loop on a
failed recheck (the `else` branch of Rust `executor_core/executor.rs` Phase 5, Java and TypeScript
`fireReadyGeneral`). The loser loses its clock as in the reference, and the step leaves phase
`pass` as `endPass` would (to `completions` when something started, `await` otherwise), under the
`lose` label: the rest of the order is not offered. -/
def time014_breakOnLose (C : Cfg N T) (s : XSt N T) : XLbl N T → Option (XSt N T)
  | .lose n => (xstep C s (.lose n)).map fun s1 =>
      { s1 with phase := if s1.started then .completions else .await }
  | l => xstep C s l

/-- A stale cycle reading: the clock reading taken once, outside the loop, and reused by every
cycle (TypeScript `cycleNowMs` or Rust `now` hoisted above the `loop`). The update arms what is
newly enabled as the reference does but keeps the old cycle reading, so the deadline step, the
pass and the park decision judge at it. -/
def time014_staleReading (C : Cfg N T) (s : XSt N T) : XLbl N T → Option (XSt N T)
  | .update => (xstep C s .update).map fun s1 => { s1 with cyc := s.cyc }
  | .deadline ns => (xstep C s (.deadline ns)).map fun s1 => { s1 with cyc := s.cyc }
  | l => xstep C s l

/-- A firing pass that takes a reading of its own when it begins (a third reading per cycle, the
behaviour RD-16 recorded for Java's `fireReadyGeneral`) and judges readiness there, not at the
deadline step's reading. -/
def time014_passReread (C : Cfg N T) (s : XSt N T) : XLbl N T → Option (XSt N T)
  | .begin => xstep C { s with cyc := s.now } .begin
  | l => xstep C s l

end Mutants

/-- ✗ Offering the lower priority first violates TIME-014 (line 1): with `hi` (10) and `lo` (-10)
on one token, the pass starts `lo` and `hi` loses; the names `lo, hi` are not a prefix of the
ready order `hi, lo`. -/
@[evidence forbids TIME_014]
theorem TIME_014_forbids_lowFirst :
    ¬ TIME_014 (time014_exec (time014_post time014_lowFirst) (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', tr, hr, -, hp⟩ := time014_scene_check
    (time014_withOrder fun C s => time014_lowFirst C s (time014_orderAs [0, 1] C s))
    (C := time014_cHL) (s0 := xinit time014_m0 0) (pre := time014_cyc)
    (body := [.start "lo" false, .lose "hi", .endPass])
    (p := fun s _ tr => !(time014_offers (time014_pass tr)).isPrefixOf
      ((time014_orderAs [0, 1] time014_cHL s).map (·.core.name)))
    (by decide +kernel)
  have := (h.1 _ s s' tr (time014_run_post hr)).1
  rw [time014_orderAs_eq] at hp
  rw [← List.isPrefixOf_iff_prefix] at this
  simp only [time014_orderNames] at this
  simp [this] at hp

/-- ✗ Offering a transition below its earliest bound violates TIME-014 (line 1, the second shall
sentence): with `slow` (priority 10, `Delayed(3s)`, armed at 0) and `quick` (priority -10,
`Immediate`) on one token, the order of every transition by the key starts `slow` at reading 0. -/
@[evidence forbids TIME_014]
theorem TIME_014_forbids_allOrder :
    ¬ TIME_014 (time014_exec time014_allOrder (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', tr, hr, -, hp⟩ := time014_scene_check (time014_withOrder time014_allOrder)
    (C := time014_cWP) (s0 := xinit time014_m0 0) (pre := time014_cyc)
    (body := [.start "slow" false, .lose "quick", .endPass])
    (p := fun s _ tr =>
      !(time014_offers (time014_pass tr)).isPrefixOf (time014_orderNames time014_cWP s))
    (by decide +kernel)
  have := (h.1 _ s s' tr hr).1
  rw [← List.isPrefixOf_iff_prefix] at this
  simp [this] at hp

/-- ✗ A gate one tick late violates TIME-014 (line 2): in AC2, at cycle reading 3000 `fallback`
is ready, the late gate leaves it out of the pass, and the pass ends having offered nothing. -/
@[evidence forbids TIME_014]
theorem TIME_014_forbids_lateGate :
    ¬ TIME_014 (time014_exec (time014_post time014_lateGate) (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', tr, hr, hl, hp⟩ := time014_scene_check
    (time014_withOrder (time014_post time014_lateGate))
    (C := time014_cAC) (s0 := xinit time014_m0 0) (pre := time014_preAC2) (body := [.endPass])
    (p := fun s _ _ => time014_orderNames time014_cAC s != []) (by decide +kernel)
  rcases tr with _ | ⟨⟨a, l, b⟩, _ | ⟨x, tr'⟩⟩ <;> simp at hl
  subst hl
  have := (h.1 _ s s' _ hr).2 [] (a, .endPass, b)
    (by simp [time014_close, time014_inPass, XLbl.outside]) rfl
  simp only [time014_offers, List.filterMap_nil] at this
  simp [← this] at hp

/-- ✗ The ordering reading of the old second bullet violates TIME-014 (line 1, ruling D9): with
`slow` (`Delayed(3s)`, armed at 0) and `quick` (`Immediate`, armed at 3000) of equal priority,
both ready at cycle reading 3000, the order of [EXEC-002] is `slow, quick` (stamp ascending), and
the executor that puts `Immediate` first starts `quick`. -/
@[evidence forbids TIME_014]
theorem TIME_014_forbids_immediateFirst :
    ¬ TIME_014 (time014_exec (time014_post time014_immFirst) (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', tr, hr, -, hp⟩ := time014_scene_check
    (time014_withOrder fun C s => time014_immFirst C s (time014_orderAs [0, 1] C s))
    (C := time014_cD9) (s0 := xinit time014_m0 0) (pre := time014_preD9)
    (body := [.start "quick" false, .lose "slow", .endPass])
    (p := fun s _ tr => !(time014_offers (time014_pass tr)).isPrefixOf
      ((time014_orderAs [0, 1] time014_cD9 s).map (·.core.name)))
    (by decide +kernel)
  have := (h.1 _ s s' tr (time014_run_post hr)).1
  rw [time014_orderAs_eq] at hp
  rw [← List.isPrefixOf_iff_prefix] at this
  simp only [time014_orderNames] at this
  simp [this] at hp

/-- ✗ A pass that breaks at its first `lose` violates TIME-014 (line 2): with `x`, `y`, `z` all
ready (order `x, y, z`), `x` starts and takes the token of `1`, `y` loses, and the pass closes
with the step to step 1. `z`, ready and competing with `y` for the token still in `0`, is never
offered: the pass closes having offered `x, y`. The reference from the same state starts `z`. -/
@[evidence forbids TIME_014]
theorem TIME_014_forbids_breakOnLose :
    ¬ TIME_014 (fun C s l s' => time014_breakOnLose (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  obtain ⟨s, s', tr, hr, -, hp⟩ := time014_scene_check time014_breakOnLose
    (C := time014_cXYZ) (s0 := xinit time014_m01 0) (pre := time014_cyc)
    (body := [.start "x" false, .lose "y", .endCompletions])
    (p := fun s _ tr => match time014_close tr with
      | (w, some st) =>
        !time014_isTerminal st && time014_offers w != time014_orderNames time014_cXYZ s
      | _ => false)
    (by decide +kernel)
  have h1 := (h.1 _ s s' tr hr).2
  cases hc : time014_close tr with
  | mk w o =>
    rw [hc] at hp
    cases o with
    | none => simp at hp
    | some st =>
      simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hp
      exact hp.2 (h1 w st hc hp.1)

/-- ✗ A stale cycle reading violates TIME-014 (line 3): in AC2, the second cycle's update runs at
host reading 3000, but the pass of that cycle judges at reading 0, where `fallback` (armed at 0,
bound 3000) is not ready; it never becomes ready and never fires. -/
@[evidence forbids TIME_014]
theorem TIME_014_forbids_staleReading :
    ¬ TIME_014 (fun C s l s' => time014_staleReading (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  obtain ⟨s, tr, hr, hl, hp⟩ := time014_from_check time014_staleReading (C := time014_cAC)
    (s0 := xinit time014_m0 0)
    (pre := time014_cyc ++ [.begin, .endPass, .park (some 3000), .delay 3000, .wake,
      .endCompletions, .endPublications, .endEvents])
    (body := [.update, .deadline [], .begin])
    (p := fun s tr => match tr with
      | [_, _, (c, _, _)] => decide (c.cyc < s.now)
      | _ => false)
    (by decide +kernel)
  rcases tr with _ | ⟨⟨a1, l1, b1⟩, _ | ⟨⟨a2, l2, b2⟩, _ | ⟨⟨a3, l3, b3⟩, _ | ⟨_, _⟩⟩⟩⟩ <;>
    simp at hl
  obtain ⟨rfl, rfl, rfl⟩ := hl
  have ha : a1 = s := hr.1
  subst ha
  have := h.2.1 _ a1 b1 _ hr [(a2, .deadline [], b2)] a3 b3 [] rfl (by simp)
  simp only [decide_eq_true_eq] at hp
  omega

/-- ✗ A pass that takes a reading of its own when it begins violates TIME-014 (line 1, with
line 3 fixing the reading the pass judges at to the deadline step's): in AC2 without the event
token, the update and the deadline step run at reading 0, the clock reaches 3000 before the pass
begins, and the pass starts `fallback`, which is not ready at the deadline step's reading. This is
the step-5 reading `spec/runtime-defects.md` recorded for Java as RD-16. -/
@[evidence forbids TIME_014]
theorem TIME_014_forbids_passReread :
    ¬ TIME_014 (fun C s l s' => time014_passReread (N := Nat) (T := Nat) C s l = some s') := by
  intro h
  obtain ⟨s, s', tr, hr, hl, hp⟩ := time014_scene_check time014_passReread (C := time014_cAC)
    (s0 := xinit time014_m0 0) (pre := time014_cyc ++ [.delay 3000])
    (body := [.start "fallback" false])
    (p := fun s _ tr => time014_offers (time014_pass tr) == ["fallback"] &&
      time014_orderNames time014_cAC s == [])
    (by decide +kernel)
  have h1 := (h.1 _ s s' tr hr).1
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  rw [hp.1, hp.2] at h1
  simp at h1

/-- ✓ The reference admits two readings per cycle, as TypeScript takes them (ruling D61 (c)): in
AC2 without the event token, the first update runs at reading 0 and arms `fallback` with stamp 0,
the clock reaches 3000 before the deadline step, the deadline step takes reading 3000, and the
pass of that same cycle starts `fallback`. Line 3 holds of the run: the pass judges at the
deadline step's reading, which is not earlier than the update's. -/
@[evidence cites "TIME-014" "the reading the pass judges at is the deadline step's reading, not earlier than the update's (ruling D61 (c)): on the reference executor an update at reading 0 arms a Delayed(3000) transition, the deadline step of the same cycle runs at 3000, and the pass starts the transition in the cycle that armed it, as an executor with a second reading after its update (TypeScript) does"]
theorem TIME_014_twoReadings :
    ∃ s s' tr, XRun RefExec time014_cAC s ((s, .begin, s') :: tr) ∧
      tr.map (·.2.1) = [.start "fallback" false] ∧ s.cyc = 3000 ∧
      (viewAt s s.cyc).stamp "fallback" = some 0 ∧
      time014_orderNames time014_cAC s = ["fallback"] := by
  obtain ⟨s, s', tr, hr, hl, hp⟩ := time014_scene_check xstep (C := time014_cAC)
    (s0 := xinit time014_m0 0)
    (pre := [.endCompletions, .endPublications, .endEvents, .update, .delay 3000, .deadline []])
    (body := [.start "fallback" false])
    (p := fun s _ _ => s.cyc == 3000 && (viewAt s s.cyc).stamp "fallback" == some 0 &&
      time014_orderNames time014_cAC s == ["fallback"])
    (by decide +kernel)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨s, s', tr, hr, hl, hp.1.1, hp.1.2, hp.2⟩

end Libpetri.Spec
