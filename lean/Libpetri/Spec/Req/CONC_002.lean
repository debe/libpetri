import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Exec
import Libpetri.Spec.Text.CONC_002

set_option linter.missingDocs true

/-!
# CONC-002: Non-blocking action dispatch (`spec/05-concurrency.md`)

A block over the executor model (`RefExec`, `Reference/Exec.lean`). A firing starts in a firing
pass (`start`) and settles in a later step (`commit`, `fail`, `tdeposit`), with its action's
writes, flushes and return in between as outside steps. CONC-002 says the start does not wait for
the action: the start deposits nothing and leaves the firing in flight, the loop does not wait at
its termination test for a firing in flight, a firing in flight never makes the pass skip a
transition, and it never makes the enablement update withhold a clock from another transition.
Whether a transition may start again while an earlier firing of it is in flight is the
configuration's (`Cfg.reentrant`, ruling D8 (b)): an executor that is not re-entrant (Java,
TypeScript) neither arms nor starts it; a re-entrant one (Rust, Python) may
(`CONC_002_allows_reentrant`).

The requirement is a predicate over an abstract executor `R : XRel N T`, checked against the
reference executor and against executors that deposit at the start, await the action inside the
start, record an asynchronous start as a synchronous one, wait at the termination test for the
firings in flight, skip a ready transition while another firing is in flight, withhold clocks at
the update while a firing is in flight, or ignore the re-entrancy setting.

Every line is a safety line, so every executor whose steps are steps of a satisfying executor
satisfies it too (`CONC_002_sub`). An executor that only refuses to go on while a firing is in
flight (one that starts every action synchronously, one that joins every returned handle before
the next step of the pass, one that never begins a pass while a firing is in flight) therefore
meets the block, and the existence half of the requirement is the coverage condition
`conc002Covers`, for the consistency theorem: the reference meets it
(`conc002_covers_reference`) and each of those three executors fails it.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## CONC-002: Non-Blocking Action Dispatch -/

requirement CONC_002
  id "CONC-002"
  title "Non-Blocking Action Dispatch"
  kind B
  scope "all executors"
  source verbatim "spec/05-concurrency.md"
  covers CONC_002.s1, CONC_002.s2, CONC_002.s3, CONC_002.s4, CONC_002.s5, CONC_002.s6, CONC_002.s7,
        CONC_002.s8, CONC_002.s9
  reading "For every executor R, every configuration C and every transition name n:"
          "a start step of n deposits nothing: every queue after it is a sublist of the queue before it (the step only takes the tokens the firing consumes and drains);"
          "a start step of n with sync flag sy adds one firing whose transition is the head of the pass's ready order, named n, whose sync flag is sy and whose outcome is not set, and the firings in flight after it are those before it and that one;"
          "in a state at the termination test, every executor step R takes is the begin of a firing pass or a finish (an answer to a snapshot request that leaves the state as it is is not a step of the loop and is allowed);"
          "a lose step of n happens only when the head of the pass's ready order is a transition named n that holds no clock or is not enabled on the pass-visible marking;"
          "after an update step, the transition the net holds under n holds a clock stamp if it is enabled on the marking, was not reaped, and either C is re-entrant or no firing of n is in flight;"
          "if C is not re-entrant, then on every run of R from a state with no firing in flight, no start step of n is taken while a firing of n is in flight, and every state the run reaches in which a firing of n is in flight gives n no clock stamp."
  assumes "The model is an executor R : XRel N T (glossary GlossaryExec.lean): R C s l s' says that under configuration C the step labelled l leads from executor state s to s'. A firing starts in a firing pass (start) and settles in a later step (commit, fail or tdeposit, or inside the pass for a synchronous firing); the outside steps write, flush, ret and expire are its action writing a token, publishing what it wrote, returning, and its budget expiring. The witness is the reference executor RefExec (Reference/Exec.lean)."
          "Every line is a safety line, so an executor whose steps are steps of a satisfying executor satisfies the block too (CONC_002_sub). The first quoted sentence has a safety half and an existence half. The safety half is lines 1 and 2: the start step takes the consumed tokens and deposits none, and it leaves the firing in flight with no outcome, so the completion is taken up only by a later step. That the outputs then arrive only through what the action returned or flushed is CONC-003 (commit and publish) and CONC-001 (outside steps keep the marking), cited, not restated. The existence half, that the orchestrator goes on once the handle is returned, is the coverage condition conc002Covers, a clause of the consistency theorem's ExecCoversW5 (ConsistencyExec.lean) and never a line of a block: at a live termination test with a firing in flight the executor can begin a firing pass, and in a pass that no synchronous firing holds up (passFree) it can start the head of the order asynchronously or pass over it. The reference meets it (conc002_covers_reference). An executor that starts every action synchronously, one that joins every returned handle before the next step of the pass (Java's execute(ctx).toCompletableFuture().join()), and one that never begins a pass while a firing is in flight all meet this block and fail conc002Covers (conc002_syncOnly_uncovered, conc002_join_uncovered, conc002_noBegin_uncovered)."
          "Where the action body runs is not encoded (kind N): the model has no threads. 'Concurrency is provided by whatever drives that returned handle', the inline-or-pool choice of the third sentence and the inline-invoking case of the fourth sentence of the body are read through the sync flag of a start: a synchronous firing is an action invoked inline that has not yet returned its handle, and the pass takes no further step until its ret step (passFree), which is how an action that blocks before returning its handle blocks the whole net. Line 2 records the flag of the label in the firing. Which actions block is the action's choice, not the executor's: conc002Covers asks that the head of the order can always start asynchronously, so an executor cannot make every start synchronous. An asynchronous firing never holds up the pass."
          "Lines 3 to 5 are the non-blocking requirement in safety form (design repair R5): the loop does not wait at its termination test for the firings in flight, the pass never skips a transition because of them (firings in flight are in neither premise), and the update never withholds a clock because of them (only a firing of the transition itself, on an executor that is not re-entrant, is in the premise of line 5). Line 3 forbids every executor step at the test other than begin and finish, with or without a firing in flight; that is the loop structure EXEC-040 shares. Line 4 restates EXEC-003's lose line, which forbids the same skipping executor. Waiting in another phase is a refusal to take a step, so it is existence, and conc002Covers carries it."
          "Re-entrancy follows ruling D8 (b): it is implementation-defined, and the configuration carries it (Cfg.reentrant: Rust and Python true, Java and TypeScript false). The quoted 'Whether an executor starts a transition again while an earlier firing of it is in flight is not specified' sentence is that choice; line 6 binds only a configuration that is not re-entrant. A re-entrant reference executor arms a transition at the first update after its start and may start it again while the earlier firing is in flight (CONC_002_allows_reentrant). Line 6 reads runs from a state with no firing in flight, the initial state xinit or a restored marking, and names transitions by name (ruling D10, unique names). That a transition is armed again by the first update after its firing has settled is line 5."
          "The quoted sentence 'While an action runs its inputs are consumed and its outputs not yet deposited, and other transitions fire' is lines 1 to 5. The rest of the paragraph after the acceptance criteria (the verification model splits every transition in two, 'The verification model allows it, which is sound for every implementation', a counterexample that starts a transition again is reported, conflict priority does not rely on the restart) is the subject of VER-004 and NU-052; it is cited, not encoded."
          "AC1 (the orchestrator does not await an action's completion inline and continues once the action returns its handle) is lines 1 and 2 for the safety half and conc002Covers for the going on; CONC_002_nonvacuous starts a transition that consumes a token and leaves it in flight."
          "AC2 (actions backed by concurrent work execute concurrently) is about threads and elapsed time, not encoded (test evidence); the model allows two firings in flight at once (CONC_002_nonvacuous starts u while t is in flight)."
          "AC3 (the orchestrator continues processing other transitions while such actions run) is lines 3 to 5 and conc002Covers; CONC_002_nonvacuous begins a firing pass from a termination test with a firing in flight and keeps the clock of a transition that waits for its delay while another firing is in flight."
          "The test derivation (two actions backed by a 100 ms sleep take about 100 ms, not 200 ms) is a timing measurement, not encoded (test evidence)."
  signoff "2026-11-13 850823bbf843d44e ai"
  statement : ∀ {N T : Type} [DecidableEq N], XRel N T → Prop :=
    fun R => ∀ C (n : String),
      (on (fun s s' => ∃ sy, R C s (.start n sy) s'), shall (fun s s' =>
        ∀ p, List.Sublist (s'.M p) (s.M p))) ∧
      (∀ sy, on (fun s s' => R C s (.start n sy) s'), shall (fun s s' =>
        ∃ f : Firing _ _, (∃ rest, s.order = f.t :: rest) ∧ f.t.core.name = n ∧ f.sync = sy ∧
          f.out = none ∧ List.Perm s'.fl (f :: s.fl))) ∧
      (while (fun s => s.phase = .test), never (fun s s' =>
        ∃ l, R C s l s' ∧ l.outside = false ∧ l ≠ .begin ∧ (∀ a, l = .snapshot a → s' ≠ s) ∧
          ∀ c, l ≠ .finish c)) ∧
      (on (fun s s' => R C s (.lose n) s'), shall (fun s _ =>
        ∃ t rest, s.order = t :: rest ∧ t.core.name = n ∧
          ¬ ((stampOf (s.st n)).isSome = true ∧ enabledNA (qCount (vis s)) t.core = true))) ∧
      (on (fun s s' => R C s .update s'), shall (fun s s' =>
        ∀ u, findT C n = some u → enabledNA (qCount s.M) u.core = true → s.st n ≠ .reaped →
          (C.reentrant = true ∨ ¬ InFlight s n) → (stampOf (s'.st n)).isSome = true)) ∧
      (C.reentrant = false → ∀ s0 tr, s0.fl = [] → XRun R C s0 tr → ∀ x ∈ tr,
        (∀ sy, x.2.1 = .start n sy → ¬ InFlight x.1 n) ∧
        (InFlight x.2.2 n → stampOf (x.2.2.st n) = none))

/- The pinned readable form of CONC-002: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CONC_002 : {N T : Type} → [DecidableEq N] → XRel N T → Prop :=
fun {N T} [DecidableEq N] R =>
  ∀ (C : Cfg N T) (n : String),
    (on fun s s' => ∃ sy, R C s (XLbl.start n sy) s', shall fun s s' => ∀ (p : N), (s'.M p).Sublist (s.M p)) ∧
      (∀ (sy : Bool),
          on fun s s' => R C s (XLbl.start n sy) s', shall fun s s' =>
            ∃ f,
              (∃ rest, s.order = f.t :: rest) ∧
                f.t.core.name = n ∧ f.sync = sy ∧ f.out = none ∧ s'.fl.Perm (f :: s.fl)) ∧
        (while fun s => s.phase = Phase.test, never fun s s' =>
            ∃ l,
              R C s l s' ∧
                l.outside = false ∧
                  l ≠ XLbl.begin ∧
                    (∀ (a : Option Bool), l = XLbl.snapshot a → s' ≠ s) ∧ ∀ (c : Cause), l ≠ XLbl.finish c) ∧
          (on fun s s' => R C s (XLbl.lose n) s', shall fun s x =>
              ∃ t rest,
                s.order = t :: rest ∧
                  t.core.name = n ∧ ¬((stampOf (s.st n)).isSome = true ∧ enabledNA (qCount (vis s)) t.core = true)) ∧
            (on fun s s' => R C s XLbl.update s', shall fun s s' =>
                ∀ (u : Reference.Trans N),
                  findT C n = some u →
                    enabledNA (qCount s.M) u.core = true →
                      s.st n ≠ Status.reaped → C.reentrant = true ∨ ¬InFlight s n → (stampOf (s'.st n)).isSome = true) ∧
              (C.reentrant = false →
                ∀ (s0 : XSt N T) (tr : List (XStep N T)),
                  s0.fl = [] →
                    XRun R C s0 tr →
                      ∀ x ∈ tr,
                        (∀ (sy : Bool), x.2.1 = XLbl.start n sy → ¬InFlight x.1 n) ∧
                          (InFlight x.2.2 n → stampOf (x.2.2.st n) = none))
-/
#guard_msgs in #print CONC_002

/-! ### The reference -/

section Reference

variable {N T : Type} [DecidableEq N]

/-- A start of `t` keeps every queue a sublist of what it was: the pass-visible prefix loses its
consumed head or is drained, the same-pass tail stays. -/
theorem conc002_liveAfter_sublist (s : XSt N T) (t : Trans N) (p : N) :
    List.Sublist (liveAfter s t p) (s.M p) := by
  rw [show s.M p = vis s p ++ hid s p from (List.take_append_drop _ _).symm]
  unfold liveAfter qConsume qPostInput
  apply List.Sublist.append _ (List.Sublist.refl _)
  split
  · exact List.nil_sublist _
  · exact List.drop_sublist _ _

/-- From the termination test the reference takes only `begin` or a `finish` among its executor
steps: every other rule needs another phase. -/
theorem conc002_test_step {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : xstep C s l = some s') (hp : s.phase = .test) (ho : l.outside = false) :
    l = .begin ∨ ∃ c, l = .finish c := by
  have hs : ∀ {i} {f : Firing N T}, canSettle C s i f = true → False := fun hc => by
    simp [canSettle, settleOk, hp] at hc
  cases l with
  | delay | write | flush | ret | expire | request | drain | close | terminateNow =>
    simp [XLbl.outside] at ho
  | commit i => obtain ⟨f, e, -, -, hc, -⟩ := commitStep_some h; exact (hs hc).elim
  | fail i => obtain ⟨f, -, hc, -⟩ := failStep_some h; exact (hs hc).elim
  | tdeposit i => obtain ⟨f, e, -, -, hc, -⟩ := tdepositStep_some h; exact (hs hc).elim
  | endCompletions =>
    obtain ⟨hph, -⟩ := xstepW_endCompletions h; rw [hp] at hph; cases hph
  | publish i =>
    obtain ⟨b, rest, -, -, hph, -⟩ := publishStep_some h
    rcases hph with hph | ⟨hph, -⟩ <;> rw [hp] at hph <;> cases hph
  | endPublications =>
    obtain ⟨hph, -⟩ := xstepW_endPublications h; rw [hp] at hph; cases hph
  | inject k =>
    obtain ⟨p, x, rest, -, -, -, hph, -⟩ := injectStep_some h
    rcases hph with hph | hph <;> rw [hp] at hph <;> cases hph
  | discard k =>
    obtain ⟨p, x, rest, -, -, -, hph, -⟩ := discardStep_some h
    rcases hph with hph | hph <;> rw [hp] at hph <;> cases hph
  | snapshot a =>
    obtain ⟨-, hph, -⟩ := snapshotStep_some h
    rcases hph with hph | hph | hph <;> rw [hp] at hph <;> cases hph
  | endEvents => obtain ⟨hph, -⟩ := xstepW_endEvents h; rw [hp] at hph; cases hph
  | update => obtain ⟨hph, -⟩ := xstepW_update h; rw [hp] at hph; cases hph
  | deadline ns => obtain ⟨hph, -⟩ := xstepW_deadline h; rw [hp] at hph; cases hph
  | begin => exact Or.inl rfl
  | finish c => exact Or.inr ⟨c, rfl⟩
  | start m sy =>
    obtain ⟨t, rest, -, hph, -⟩ := startStep_some h; rw [hp] at hph; cases hph
  | lose m => obtain ⟨t, rest, -, hph, -⟩ := loseStep_some h; rw [hp] at hph; cases hph
  | endPass => obtain ⟨hph, -⟩ := xstepW_endPass h; rw [hp] at hph; cases hph
  | park tmr => obtain ⟨hph, -⟩ := parkStep_some h; rw [hp] at hph; cases hph
  | wake => obtain ⟨hph, -⟩ := wakeStep_some h; rw [hp] at hph; cases hph

/-- Every step of the reference keeps the in-flight clause (`InFlightOff`: under `¬reentrant`
a name with a firing in flight is off). Unlike `invX_step` it needs no other clause and no
distinct names: a start turns its own name off, the update keeps an off name in flight off, the
deadline step reaps only names holding a stamp, and nothing else arms. -/
theorem conc002_inFlightOff_step {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : xstep C s l = some s') (hi : InFlightOff C s) : InFlightOff C s' := by
  by_cases ho : l.outside = true
  · obtain ⟨-, hst, -, -, ht⟩ := xstepW_outside_frame h ho
    intro hre n hn
    rw [hst]; rw [inFlightN_eq_of_map ht] at hn; exact hi hre n hn
  cases l with
  | delay | write | flush | ret | expire | request | drain | close | terminateNow =>
    simp [XLbl.outside] at ho
  | commit i =>
    obtain ⟨f, e, -, -, -, -, -, rfl⟩ := commitStep_some h
    exact fun hre n hn => unreap_off (hi hre n (inFlightN_settle hn))
  | fail i =>
    obtain ⟨f, -, -, -, rfl⟩ := failStep_some h
    exact fun hre n hn => hi hre n (inFlightN_settle hn)
  | tdeposit i =>
    obtain ⟨f, e, -, -, -, -, rfl⟩ := tdepositStep_some h
    exact fun hre n hn => unreap_off (hi hre n (inFlightN_settle hn))
  | endCompletions => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endCompletions h; exact hi
  | publish i =>
    obtain ⟨b, rest, -, -, -, rfl⟩ := publishStep_some h
    exact fun hre n hn => unreap_off (hi hre n hn)
  | endPublications => obtain ⟨-, -, -, rfl⟩ := xstepW_endPublications h; exact hi
  | inject k =>
    obtain ⟨p, x, rest, -, -, -, -, rfl⟩ := injectStep_some h
    exact fun hre n hn => unreap_off (hi hre n hn)
  | discard k => obtain ⟨p, x, rest, -, -, -, -, rfl⟩ := discardStep_some h; exact hi
  | snapshot a => obtain ⟨-, -, -, rfl⟩ := snapshotStep_some h; exact hi
  | endEvents => obtain ⟨-, -, -, rfl⟩ := xstepW_endEvents h; exact hi
  | update =>
    obtain ⟨-, -, rfl⟩ := xstepW_update h
    intro hre n hn
    show updSt refXPol C s n = .off
    cases hf : findT C n with
    | none => unfold updSt; simp [hf]
    | some u => exact (updSt_ref hf).2.2.2 (hi hre n hn) hre hn
  | deadline ns =>
    obtain ⟨-, -, hns, rfl⟩ := xstepW_deadline h
    intro hre n hn
    have hoff := hi hre n hn
    change (if ns.contains n = true then Status.reaped else s.st n) = .off
    by_cases hc : n ∈ ns
    · subst hns
      obtain ⟨-, -, -, -, hs⟩ := mem_expiredNames hc
      simp [hoff, stampOf, atDeadline] at hs
    · simp [hc, hoff]
  | finish c =>
    cases c with
    | quiescent => obtain ⟨-, -, -, rfl⟩ := xstepW_finishQuiescent h; exact hi
    | closed => obtain ⟨-, -, -, -, rfl⟩ := xstepW_finishClosed h; exact hi
    | terminal => obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h; exact hi
    | stopped => obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h; exact hi
  | begin => obtain ⟨-, -, -, -, rfl⟩ := xstepW_begin h; exact hi
  | start m sy =>
    obtain ⟨t, rest, -, -, -, -, -, -, -, rfl⟩ := startStep_some h
    intro hre k hk
    apply unreap_off
    simp only [inFlightN, List.any_append, List.any_cons, List.any_nil, Bool.or_false,
      Bool.or_eq_true, beq_iff_eq] at hk
    rcases hk with hk | hk
    · exact afterStart_off (hi hre k hk)
    · unfold afterStart; simp [hk]
  | lose m =>
    obtain ⟨t, rest, -, -, -, -, -, -, rfl⟩ := loseStep_some h
    intro hre k hk
    show (if k = m then Status.off else s.st k) = .off
    split
    · rfl
    · exact hi hre k hk
  | endPass => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endPass h; exact hi
  | park tmr => obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := parkStep_some h; exact hi
  | wake => obtain ⟨-, -, rfl⟩ := wakeStep_some h; exact hi

/-- Along a run of the reference from a state meeting the in-flight clause, every step is a
reference step and both of its states meet the clause. -/
theorem conc002_run_inFlightOff {C : Cfg N T} :
    ∀ {s0 : XSt N T} {tr : List (XStep N T)}, XRun RefExec C s0 tr → InFlightOff C s0 →
      ∀ x ∈ tr, RefExec C x.1 x.2.1 x.2.2 ∧ InFlightOff C x.1 ∧ InFlightOff C x.2.2
  | _, [], _, _, x, hx => by simp at hx
  | _, y :: rest, ⟨h1, h2, h3⟩, hi, x, hx => by
    have hy : InFlightOff C y.1 := h1 ▸ hi
    have hy' : InFlightOff C y.2.2 := conc002_inFlightOff_step h2 hy
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨h2, hy, hy'⟩
    · exact conc002_run_inFlightOff h3 hy' x hx

/-- After an update of the reference, the transition the net holds under `n` holds a stamp when
it is enabled, was not reaped, and the configuration is re-entrant or `n` is not in flight. -/
theorem conc002_update_armed {C : Cfg N T} {s : XSt N T} {n : String} {u : Trans N}
    (hf : findT C n = some u) (he : enabledNA (qCount s.M) u.core = true)
    (hr : s.st n ≠ .reaped) (hc : C.reentrant = true ∨ ¬ InFlight s n) :
    (stampOf (updSt refXPol C s n)).isSome = true := by
  obtain ⟨h1, -, h3, -⟩ := updSt_ref (s := s) hf
  cases hu : updSt refXPol C s n with
  | armed k r => rfl
  | off =>
    obtain ⟨hin, hre⟩ := h3 hu he
    rcases hc with hc | hc
    · rw [hre] at hc; cases hc
    · exact absurd hin hc
  | reaped => exact absurd (h1 hu) hr

end Reference

/-- ✓ The reference executor satisfies CONC-002: a start leaves the consumed queues' remainders
and the same-pass tails (`conc002_liveAfter_sublist`) and appends one firing of the order's head
with the label's sync flag and no outcome (`startStep_some`); from the test only `begin` and
`finish` apply (`conc002_test_step`); `lose` requires the head to be unarmed or disabled on
`vis` (`loseStep_some`); the update arms every enabled name that is not reaped, except one in
flight under `¬reentrant` (`conc002_update_armed`); and under `¬reentrant` a name in flight
stays off along every run from a state with nothing in flight (`conc002_run_inFlightOff`),
while `start` needs a stamp. -/
@[evidence holds CONC_002]
theorem CONC_002_reference {N T : Type} [DecidableEq N] :
    CONC_002 (RefExec (N := N) (T := T)) := by
  intro C n
  refine ⟨fun s s' ⟨sy, h⟩ => ?_, fun sy s s' h => ?_,
    fun s s' ⟨l, h, ho, hb, _, hf⟩ hp => ?_, fun s s' h => ?_, fun s s' h => ?_,
    fun hre s0 tr h0 hr x hx => ?_⟩
  · obtain ⟨t, rest, -, -, -, -, -, -, -, rfl⟩ := startStep_some h
    exact fun p => conc002_liveAfter_sublist s t p
  · obtain ⟨t, rest, ho, -, -, -, hn, -, -, rfl⟩ := startStep_some h
    exact ⟨_, ⟨rest, ho⟩, hn, rfl, rfl, List.perm_append_singleton _ _⟩
  · rcases conc002_test_step h hp ho with rfl | ⟨c, rfl⟩
    · exact hb rfl
    · exact hf c rfl
  · obtain ⟨t, rest, ho, -, -, -, hn, hne, -⟩ := loseStep_some h
    exact ⟨t, rest, ho, hn, hne⟩
  · obtain ⟨-, -, rfl⟩ := xstepW_update h
    exact fun u hf he hr hc => conc002_update_armed hf he hr hc
  · have hi0 : InFlightOff C s0 := fun _ m hm => by simp [inFlightN, h0] at hm
    obtain ⟨hs, h1, h2⟩ := conc002_run_inFlightOff hr hi0 x hx
    refine ⟨fun sy hl hin => ?_, fun hin => ?_⟩
    · rw [hl] at hs
      obtain ⟨t, rest, -, -, -, -, -, hst, -⟩ := startStep_some hs
      rw [h1 hre n hin] at hst
      simp [stampOf] at hst
    · rw [h2 hre n hin]; rfl

/-! ### Every line is a safety line -/

/-- A run of `R'` is a run of `R` when every step of `R'` is a step of `R`. -/
theorem conc002_run_mono {N T : Type} {R R' : XRel N T} {C : Cfg N T}
    (hs : ∀ C s l s', R' C s l s' → R C s l s') :
    ∀ {s0 : XSt N T} {tr : List (XStep N T)}, XRun R' C s0 tr → XRun R C s0 tr
  | _, [], _ => trivial
  | _, _ :: _, ⟨h1, h2, h3⟩ => ⟨h1, hs _ _ _ _ h2, conc002_run_mono hs h3⟩

/-- CONC-002 is closed under taking fewer steps: an executor whose steps are steps of one that
satisfies CONC-002 satisfies it too. So no line of the block can reject an executor that only
refuses to go on; that half of the requirement is the coverage condition `conc002Covers`. -/
theorem CONC_002_sub {N T : Type} [DecidableEq N] {R R' : XRel N T}
    (hs : ∀ C s l s', R' C s l s' → R C s l s') (h : CONC_002 R) : CONC_002 R' := by
  intro C n
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h C n
  exact ⟨fun s s' ⟨sy, hr⟩ => h1 s s' ⟨sy, hs _ _ _ _ hr⟩,
    fun sy s s' hr => h2 sy s s' (hs _ _ _ _ hr),
    fun s s' ⟨l, hr, hrest⟩ hp => h3 s s' ⟨l, hs _ _ _ _ hr, hrest⟩ hp,
    fun s s' hr => h4 s s' (hs _ _ _ _ hr), fun s s' hr => h5 s s' (hs _ _ _ _ hr),
    fun hre s0 tr h0 hr => h6 hre s0 tr h0 (conc002_run_mono hs hr)⟩

/-! ### The existence half: coverage for the consistency theorem -/

/-- **The coverage CONC-002 needs** (for the consistency theorem's `ExecCoversW5`, never a line of
a block): the orchestrator goes on while firings are in flight. (a) At a live termination test
with a firing in flight, the executor can begin a firing pass. (b) In a live firing pass that no
synchronous firing holds up (`passFree`), the executor can start the head of the order
asynchronously or pass over it. Clause (b) asks for an asynchronous start, so which actions
block before returning their handle is the action's choice, never the executor's. -/
def conc002Covers {N T : Type} [DecidableEq N] (E : XRel N T) : Prop :=
  (∀ C s, s.phase = .test → Live C s → s.fl ≠ [] → ∃ s', E C s .begin s') ∧
  (∀ C s t rest, s.phase = .pass → Live C s → passFree s = true → s.order = t :: rest →
    (∃ s', E C s (.start t.core.name false) s') ∨ ∃ s', E C s (.lose t.core.name) s')

/-- The reference meets the coverage of CONC-002: `begin` needs only a live test that is not at
rest, and a head that cannot start asynchronously is one `lose` passes over. -/
theorem conc002_covers_reference {N T : Type} [DecidableEq N] :
    conc002Covers (RefExec (N := N) (T := T)) := by
  refine ⟨fun C s hp hl hfl => ?_, fun C s t rest hp hl hpf ho => ?_⟩
  · have hl' : liveB C s = true := hl
    have he : s.fl.isEmpty = false := by simpa using hfl
    have hr : finishQ C s = false := by simp [finishQ, restB, he]
    apply Option.isSome_iff_exists.mp
    show (xstepW refXPol C s .begin).isSome = true
    simp only [xstepW]
    rw [if_pos (by simp [hp, hl', hr, he])]
    rfl
  · have hl' : liveB C s = true := hl
    by_cases hc : (stampOf (s.st t.core.name)).isSome = true ∧
        enabledNA (qCount (vis s)) t.core = true
    · refine Or.inl (Option.isSome_iff_exists.mp ?_)
      show (startStep refXPol C s t.core.name false).isSome = true
      simp only [startStep, ho]
      rw [if_pos (by simp [hp, hl', hpf, hc.1, hc.2, refXPol])]
      rfl
    · refine Or.inr (Option.isSome_iff_exists.mp ?_)
      show (loseStep refXPol C s t.core.name).isSome = true
      simp only [loseStep, ho]
      have hc' : ((stampOf (s.st t.core.name)).isSome &&
          enabledNA (qCount (vis s)) t.core) = false := by
        cases h1 : (stampOf (s.st t.core.name)).isSome <;>
          cases h2 : enabledNA (qCount (vis s)) t.core <;> simp_all
      rw [if_pos (by simp only [refXPol]; simp [hp, hl', hpf, hc'])]
      rfl

/-! ### Examples

Transitions take one token from one place and put one into another; every timing is immediate
unless said otherwise, every priority `0`, nothing is validated. `t` takes from `0` and gives `1`,
`u` takes from `2`, `v` takes from `0`; `u` and `v` give `3`. -/

/-- A transition named `nm` taking one token from `i`, output spec `Out.place o`. -/
def conc002_tr (nm : String) (i o : Nat) : Trans Nat :=
  { core := { name := nm, inputs := [⟨i, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place o) }

/-- `t`: from `0` to `1`. -/
def conc002_t : Trans Nat := conc002_tr "t" 0 1
/-- `u`: from `2` to `3`. -/
def conc002_u : Trans Nat := conc002_tr "u" 2 3
/-- `v`: from `0` to `3`, competing with `t`. -/
def conc002_v : Trans Nat := conc002_tr "v" 0 3

/-- The configuration of the examples over transitions `ts`, re-entrant or not. -/
def conc002_cfg (ts : List (Trans Nat)) (re : Bool) : Cfg Nat Nat :=
  { X := { net := { places := [0, 1, 2, 3], transitions := ts }, timing := fun _ => .immediate,
           tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [], reentrant := re,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => false,
    res := 0 }

/-- `t` alone, not re-entrant (Java, TypeScript). -/
def conc002_cT : Cfg Nat Nat := conc002_cfg [conc002_t] false
/-- `t` alone, re-entrant (Rust, Python). -/
def conc002_cRe : Cfg Nat Nat := conc002_cfg [conc002_t] true
/-- `t` and `u`, not re-entrant. -/
def conc002_cTU : Cfg Nat Nat := conc002_cfg [conc002_t, conc002_u] false
/-- `t` and `v`, not re-entrant. -/
def conc002_cTV : Cfg Nat Nat := conc002_cfg [conc002_t, conc002_v] false
/-- `w`: from `2` to `3`, inhibited by a token in `0`. -/
def conc002_w : Trans Nat :=
  { core := { name := "w", inputs := [⟨2, .one⟩], inhibitors := [0], reads := [], resets := [] },
    out := some (.place 3) }
/-- `t` and `w`, not re-entrant: `w` is enabled only once `t` has taken the token of `0`. -/
def conc002_cTW : Cfg Nat Nat := conc002_cfg [conc002_t, conc002_w] false

/-- Two tokens in `0`, one in `2`. -/
def conc002_m0 : QMarking Nat Nat := fun p => if p = 0 then [7, 8] else if p = 2 then [9] else []
/-- One token in `0`. -/
def conc002_m1 : QMarking Nat Nat := fun p => if p = 0 then [7] else []
/-- One token in `0`, one in `2`. -/
def conc002_m2 : QMarking Nat Nat := fun p => if p = 0 then [7] else if p = 2 then [9] else []

/-- One cycle up to the begin of the firing pass. -/
def conc002_pre : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin]

/-- Start `t` asynchronously, end the pass, and run the next cycle up to its enablement update. -/
def conc002_toUpdateEve : List (XLbl Nat Nat) :=
  conc002_pre ++ [.start "t" false, .endPass, .endCompletions, .endPublications, .endEvents]

/-- Start `t` asynchronously, end the pass, and run the next cycle to its enablement update. -/
def conc002_toUpdate : List (XLbl Nat Nat) := conc002_toUpdateEve ++ [.update]

/-- Start `t`, end the pass, and start `t` again in the next cycle's pass. -/
def conc002_twice : List (XLbl Nat Nat) :=
  conc002_pre ++ [.start "t" false, .endPass] ++ conc002_pre ++ [.start "t" false]

/-- Start `t`, end the pass, and run the next cycle to its termination test. -/
def conc002_toTest : List (XLbl Nat Nat) := conc002_toUpdate ++ [.deadline []]

/-- A run of the step function `g`, as a fold. -/
def conc002_grun {N T : Type} (g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T))
    (C : Cfg N T) (s : XSt N T) : List (XLbl N T) → Option (XSt N T)
  | [] => some s
  | l :: ls => (g C s l).bind fun s' => conc002_grun g C s' ls

/-- The step trace of a run of the step function `g`, if every label is a step. -/
def conc002_trace {N T : Type} (g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T))
    (C : Cfg N T) : XSt N T → List (XLbl N T) → Option (List (XStep N T))
  | _, [] => some []
  | s, l :: ls => (g C s l).bind fun s' => (conc002_trace g C s' ls).map ((s, l, s') :: ·)

/-- A trace `conc002_trace` builds is a run of the graph of `g`. -/
theorem conc002_trace_run {N T : Type} (g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T))
    {C : Cfg N T} :
    ∀ {s : XSt N T} {ls : List (XLbl N T)} {tr : List (XStep N T)},
      conc002_trace g C s ls = some tr → XRun (fun C s l s' => g C s l = some s') C s tr
  | s, [], tr, h => by cases h; trivial
  | s, l :: ls, tr, h => by
    simp only [conc002_trace] at h
    cases hs : g C s l with
    | none => simp [hs] at h
    | some s' =>
      simp only [hs, Option.bind_some] at h
      cases ht : conc002_trace g C s' ls with
      | none => simp [ht] at h
      | some tr' =>
        simp only [ht, Option.map_some, Option.some.injEq] at h
        subst h
        exact ⟨rfl, hs, conc002_trace_run g ht⟩

/-- Read a decided fact off a whole run of `g`: if the check `p` of its trace evaluates to `true`,
the run exists. -/
theorem conc002_run_of_check {N T : Type} (g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T))
    {C : Cfg N T} {s0 : XSt N T} {ls : List (XLbl N T)} {p : List (XStep N T) → Bool}
    (h : (conc002_trace g C s0 ls).map p = some true) :
    ∃ tr, XRun (fun C s l s' => g C s l = some s') C s0 tr ∧ p tr = true := by
  cases ht : conc002_trace g C s0 ls with
  | none => simp [ht] at h
  | some tr =>
    simp only [ht, Option.map_some, Option.some.injEq] at h
    exact ⟨tr, conc002_trace_run g ht, h⟩

/-- The step of a trace is a start of `n` from a state in which a firing of `n` is in flight. -/
def conc002_restart {N T : Type} (n : String) (x : XStep N T) : Bool :=
  match x.2.1 with
  | .start m _ => m == n && inFlightN x.1 n
  | _ => false

/-- What `conc002_restart` checks. -/
theorem conc002_restart_spec {N T : Type} {n : String} {x : XStep N T}
    (h : conc002_restart n x = true) : ∃ sy, x.2.1 = .start n sy ∧ inFlightN x.1 n = true := by
  obtain ⟨s, l, s'⟩ := x
  cases l <;> simp [conc002_restart] at h ⊢
  obtain ⟨rfl, h⟩ := h
  exact ⟨rfl, h⟩

/-! ### Violation: depositing at the start -/

/-- An executor whose start step deposits the firing's output at once: the token `x` lands in
every place of the started transition's output spec (an atomic firing). -/
def conc002_atomicStep {N T : Type} [DecidableEq N] (x : T) (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .start n sy => (xstep C s (.start n sy)).map fun s₁ =>
      match findT C n with
      | some t => { s₁ with M := qAppend s₁.M (((t.out.map outPlaces).getD []).map (·, x)) }
      | none => s₁
  | l => xstep C s l

/-- The executor of `conc002_atomicStep`. -/
def conc002_atomic {N T : Type} [DecidableEq N] (x : T) : XRel N T :=
  fun C s l s' => conc002_atomicStep x C s l = some s'

/-- ✗ Depositing at the start violates CONC-002 (line 1): `t` starts and place `1` gains a
token. -/
@[evidence forbids CONC_002]
theorem CONC_002_forbids_atomic : ¬ CONC_002 (conc002_atomic (N := Nat) (T := Nat) 0) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check (conc002_atomicStep 0) (C := conc002_cT)
    (o := conc002_grun (conc002_atomicStep 0) conc002_cT (xinit conc002_m0 0) conc002_pre)
    (l := .start "t" false) (p := fun s s' => decide ((s.M 1).length < (s'.M 1).length))
    (by decide)
  have := ((h conc002_cT "t").1 s s' ⟨false, hs⟩ 1).length_le
  simp only [decide_eq_true_eq] at hp
  omega

/-! ### Violation: awaiting the action inside the start -/

/-- An executor whose start step runs the action to its completion and settles it before going
on: start, a normal return with nothing written, and the commit, in one step. -/
def conc002_awaitInlineStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .start n sy => ((xstep C s (.start n sy)).bind fun s₁ => xstep C s₁ (.ret s.nextId true)).bind
      fun s₂ => xstep C s₂ (.commit s.nextId)
  | l => xstep C s l

/-- The executor of `conc002_awaitInlineStep`. -/
def conc002_awaitInline {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => conc002_awaitInlineStep C s l = some s'

/-- ✗ Awaiting the completion inside the start violates CONC-002 (line 2): `t` starts with an
action that writes nothing, and after the start no firing is in flight. Line 1 does not reject
it: the start consumes `7` and deposits nothing. -/
@[evidence forbids CONC_002]
theorem CONC_002_forbids_awaitInline :
    ¬ CONC_002 (conc002_awaitInline (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check conc002_awaitInlineStep (C := conc002_cT)
    (o := conc002_grun conc002_awaitInlineStep conc002_cT (xinit conc002_m0 0) conc002_pre)
    (l := .start "t" true) (p := fun s s' => s'.fl.length == s.fl.length) (by decide)
  obtain ⟨f, -, -, -, -, hperm⟩ := (h conc002_cT "t").2.1 true s s' hs
  have := hperm.length_eq
  simp only [List.length_cons, beq_iff_eq] at this hp
  omega

/-! ### Violation: an asynchronous start recorded as a synchronous one -/

/-- An executor that starts every action as a synchronous one, whatever the label says: each
start holds up the pass until the action returns, a serial executor. -/
def conc002_allSyncStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .start n _ => xstep C s (.start n true)
  | l => xstep C s l

/-- The executor of `conc002_allSyncStep`. -/
def conc002_allSync {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => conc002_allSyncStep C s l = some s'

/-- ✗ Recording an asynchronous start as a synchronous firing violates CONC-002 (line 2, the
sync flag): `t` starts asynchronously, and the firing it adds holds up the pass. -/
@[evidence forbids CONC_002]
theorem CONC_002_forbids_allSync : ¬ CONC_002 (conc002_allSync (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check conc002_allSyncStep (C := conc002_cT)
    (o := conc002_grun conc002_allSyncStep conc002_cT (xinit conc002_m0 0) conc002_pre)
    (l := .start "t" false) (p := fun _ s' => s'.fl.all (·.sync)) (by decide)
  obtain ⟨f, -, -, hsy, -, hperm⟩ := (h conc002_cT "t").2.1 false s s' hs
  have hf : f ∈ s'.fl := hperm.mem_iff.mpr (by simp)
  have := List.all_eq_true.mp hp f hf
  rw [hsy] at this
  cases this

/-! ### Violation: a serial executor waiting at the test -/

/-- A serial executor: it begins a firing pass only when nothing is in flight, and at the
termination test with a firing in flight it parks to wait for it. -/
def conc002_serialWaitStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .park tmr =>
      if decide (s.phase = .test) && !s.fl.isEmpty then some { s with phase := .await, parked := true }
      else xstep C s (.park tmr)
  | .begin => if s.fl.isEmpty then xstep C s .begin else none
  | l => xstep C s l

/-- The executor of `conc002_serialWaitStep`. -/
def conc002_serialWait {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => conc002_serialWaitStep C s l = some s'

/-- ✗ Waiting at the termination test for a firing in flight violates CONC-002 (line 3): `t`
starts, and at the next test, with `t` in flight, the serial executor parks. -/
@[evidence forbids CONC_002]
theorem CONC_002_forbids_serialWait : ¬ CONC_002 (conc002_serialWait (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check conc002_serialWaitStep (C := conc002_cT)
    (o := conc002_grun conc002_serialWaitStep conc002_cT (xinit conc002_m0 0) conc002_toTest)
    (l := .park none) (p := fun s _ => decide (s.phase = .test)) (by decide)
  simp only [decide_eq_true_eq] at hp
  exact (h conc002_cT "t").2.2.1 s s'
    ⟨.park none, hs, rfl, (fun h => by cases h), (fun _ h => by cases h), (fun c h => by cases h)⟩ hp

/-! ### Violation: a serial executor skipping a ready transition -/

/-- A serial executor that starts a transition only when nothing is in flight, and passes over a
ready head of the order when something is. EXEC-003's lose line forbids it too; line 4 restates
that line as the reason a pass with a firing in flight goes on. -/
def conc002_serialSkipStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .start n sy => if s.fl.isEmpty then xstep C s (.start n sy) else none
  | .lose n =>
    match s.order with
    | t :: rest =>
      if s.phase = .pass && liveB C s && passFree s && t.core.name == n &&
          (!((stampOf (s.st n)).isSome && enabledNA (qCount (vis s)) t.core) || !s.fl.isEmpty)
      then some { s with order := rest, st := fun m => if m = n then .off else s.st m }
      else none
    | [] => none
  | l => xstep C s l

/-- The executor of `conc002_serialSkipStep`. -/
def conc002_serialSkip {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => conc002_serialSkipStep C s l = some s'

/-- ✗ Skipping a ready transition because a firing is in flight violates CONC-002 (line 4):
`t` and `u` are ready, `t` starts, and `u`, armed and enabled on the pass-visible marking, is
passed over. -/
@[evidence forbids CONC_002]
theorem CONC_002_forbids_serialSkip : ¬ CONC_002 (conc002_serialSkip (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check conc002_serialSkipStep (C := conc002_cTU)
    (o := conc002_grun conc002_serialSkipStep conc002_cTU (xinit conc002_m0 0)
      (conc002_pre ++ [.start "t" false]))
    (l := .lose "u")
    (p := fun s _ => match s.order with
      | t :: _ => (stampOf (s.st "u")).isSome && enabledNA (qCount (vis s)) t.core
      | [] => false)
    (by decide)
  obtain ⟨t, rest, ho, -, hne⟩ := (h conc002_cTU "u").2.2.2.1 s s' hs
  rw [ho] at hp
  simp only [Bool.and_eq_true] at hp
  exact hne hp

/-! ### Violation: withholding clocks while a firing is in flight -/

/-- An executor whose enablement update leaves every name without a clock while any firing is
in flight, and behaves as the reference otherwise: its passes start nothing until the firings in
flight have settled, a serial executor that skips no armed transition. -/
def conc002_withholdStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .update => (xstep C s .update).map fun s' =>
      if s.fl.isEmpty then s' else { s' with st := fun _ => .off }
  | l => xstep C s l

/-- The executor of `conc002_withholdStep`. -/
def conc002_withhold {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => conc002_withholdStep C s l = some s'

/-- ✗ Withholding a clock because another firing is in flight violates CONC-002 (line 5): `t`
takes the token of `0` and is in flight, and at the next update `w`, now enabled, not reaped and
not in flight, gets no clock. -/
@[evidence forbids CONC_002]
theorem CONC_002_forbids_withhold : ¬ CONC_002 (conc002_withhold (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check conc002_withholdStep (C := conc002_cTW)
    (o := conc002_grun conc002_withholdStep conc002_cTW (xinit conc002_m2 0) conc002_toUpdateEve)
    (l := .update)
    (p := fun s s' => enabledNA (qCount s.M) conc002_w.core && s.st "w" != .reaped &&
      !inFlightN s "w" && (stampOf (s'.st "w")).isNone)
    (by decide)
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true',
    Option.isNone_iff_eq_none] at hp
  obtain ⟨⟨⟨he, hr⟩, hin⟩, hst⟩ := hp
  have hni : ¬ InFlight s "w" := fun hi => by
    have : inFlightN s "w" = true := hi
    rw [hin] at this; cases this
  have := (h conc002_cTW "w").2.2.2.2.1 s s' hs conc002_w rfl he hr (Or.inr hni)
  rw [hst] at this
  cases this

/-! ### Violation: ignoring the re-entrancy setting -/

/-- An executor that is re-entrant whatever the configuration says: it re-arms and restarts a
transition while an earlier firing of it is in flight (Rust's behaviour, on a configuration that
asks for Java's). -/
def conc002_ignoreFlag {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => RefExec { C with reentrant := true } s l s'

/-- ✗ Ignoring the re-entrancy setting violates CONC-002 (line 6): on a configuration that is
not re-entrant, `t` starts, and in the next pass it starts again while its first firing is in
flight. -/
@[evidence forbids CONC_002]
theorem CONC_002_forbids_ignoreFlag : ¬ CONC_002 (conc002_ignoreFlag (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨tr, hr, hp⟩ := conc002_run_of_check (fun C s l => xstep { C with reentrant := true } s l)
    (C := conc002_cT) (s0 := xinit conc002_m0 0) (ls := conc002_twice)
    (p := fun tr => tr.any (conc002_restart "t")) (by decide)
  obtain ⟨x, hx, hb⟩ := List.any_eq_true.mp hp
  obtain ⟨sy, hl, hin⟩ := conc002_restart_spec hb
  exact ((h conc002_cT "t").2.2.2.2.2 rfl (xinit conc002_m0 0) tr rfl hr x hx).1 sy hl hin

/-- An executor that arms a transition while an earlier firing of it is in flight, as a
re-entrant one does, but never starts it then. -/
def conc002_armNoStartStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .start n sy => if inFlightN s n then none else xstep { C with reentrant := true } s (.start n sy)
  | l => xstep { C with reentrant := true } s l

/-- The executor of `conc002_armNoStartStep`. -/
def conc002_armNoStart {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => conc002_armNoStartStep C s l = some s'

/-- ✗ Arming a transition in flight violates CONC-002 (line 6, the clock half), although the
executor never starts it again: on a configuration that is not re-entrant, `t` starts, and the
next update gives it a stamp while it is in flight. -/
@[evidence forbids CONC_002]
theorem CONC_002_forbids_armNoStart : ¬ CONC_002 (conc002_armNoStart (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨tr, hr, hp⟩ := conc002_run_of_check conc002_armNoStartStep
    (C := conc002_cT) (s0 := xinit conc002_m0 0) (ls := conc002_toUpdate)
    (p := fun tr => tr.any fun x => inFlightN x.2.2 "t" && (stampOf (x.2.2.st "t")).isSome)
    (by decide)
  obtain ⟨x, hx, hb⟩ := List.any_eq_true.mp hp
  simp only [Bool.and_eq_true] at hb
  have := ((h conc002_cT "t").2.2.2.2.2 rfl (xinit conc002_m0 0) tr rfl hr x hx).2 hb.1
  rw [this] at hb
  simp at hb

/-! ### Executors only coverage rejects

Each of these takes only steps of the reference, so it meets CONC-002 (`CONC_002_sub`), and each
fails `conc002Covers`: it does not go on while a firing is in flight. -/

/-- The steps of the firing pass: `start`, `lose` and `endPass`. -/
def conc002_passStep {N T : Type} : XLbl N T → Bool
  | .start _ _ | .lose _ | .endPass => true
  | _ => false

/-- The reference restricted to synchronous starts: every action runs inline to its return
before the pass goes on. -/
def conc002_syncOnly {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => RefExec C s l s' ∧ ∀ n, l ≠ .start n false

/-- A Java-style executor that joins every returned handle inside the firing pass
(`execute(ctx).toCompletableFuture().join()`): the reference, with every step of the pass
waiting until every firing in flight has returned. -/
def conc002_join {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => RefExec C s l s' ∧
    (conc002_passStep l = true → s.fl.all (fun g => g.out.isSome) = true)

/-- The reference that never begins a firing pass while a firing is in flight. -/
def conc002_noBegin {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => RefExec C s l s' ∧ (l = .begin → s.fl = [])

/-- The three executors meet CONC-002: they take only steps of the reference. -/
theorem conc002_refusers_meet {N T : Type} [DecidableEq N] :
    CONC_002 (conc002_syncOnly (N := N) (T := T)) ∧ CONC_002 (conc002_join (N := N) (T := T)) ∧
      CONC_002 (conc002_noBegin (N := N) (T := T)) :=
  ⟨CONC_002_sub (fun _ _ _ _ h => h.1) CONC_002_reference,
    CONC_002_sub (fun _ _ _ _ h => h.1) CONC_002_reference,
    CONC_002_sub (fun _ _ _ _ h => h.1) CONC_002_reference⟩

/-- The executor that starts every action synchronously fails the coverage: at the first pass
`t` is armed and enabled, so it can neither start asynchronously nor be passed over. -/
theorem conc002_syncOnly_uncovered : ¬ conc002Covers (conc002_syncOnly (N := Nat) (T := Nat)) := by
  intro hc
  obtain ⟨-, s, -, -, hp⟩ := step_of_check xstep (C := conc002_cT)
    (o := xrun conc002_cT (xinit conc002_m0 0) conc002_pre.dropLast) (l := .begin)
    (p := fun _ s => decide (s.phase = .pass) && liveB conc002_cT s && passFree s &&
      match s.order with
      | t :: _ => (stampOf (s.st t.core.name)).isSome && enabledNA (qCount (vis s)) t.core
      | [] => false)
    (by decide)
  cases ho : s.order with
  | nil => simp [ho] at hp
  | cons t rest =>
    rw [ho] at hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    obtain ⟨⟨⟨hph, hl⟩, hpf⟩, hst, hen⟩ := hp
    rcases hc.2 conc002_cT s t rest hph hl hpf ho with ⟨_, -, hn⟩ | ⟨_, hlose, -⟩
    · exact hn _ rfl
    · obtain ⟨t', rest', ho', -, -, -, -, hne, -⟩ := loseStep_some hlose
      rw [ho] at ho'
      cases ho'
      exact hne ⟨hst, hen⟩

/-- The executor that joins every returned handle in the pass fails the coverage: after `t`
starts asynchronously, `u` heads the order, no synchronous firing holds up the pass, and it
neither starts nor passes over `u` while `t` has not returned. -/
theorem conc002_join_uncovered : ¬ conc002Covers (conc002_join (N := Nat) (T := Nat)) := by
  intro hc
  obtain ⟨-, s, -, -, hp⟩ := step_of_check xstep (C := conc002_cTU)
    (o := xrun conc002_cTU (xinit conc002_m0 0) conc002_pre) (l := .start "t" false)
    (p := fun _ s => decide (s.phase = .pass) && liveB conc002_cTU s && passFree s &&
      !s.order.isEmpty && !(s.fl.all fun g => g.out.isSome))
    (by decide)
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hp
  obtain ⟨⟨⟨⟨hph, hl⟩, hpf⟩, hne⟩, hfl⟩ := hp
  cases ho : s.order with
  | nil => simp [ho] at hne
  | cons t rest =>
    rcases hc.2 conc002_cTU s t rest hph hl hpf ho with ⟨_, -, hj⟩ | ⟨_, -, hj⟩
    · rw [hj rfl] at hfl; cases hfl
    · rw [hj rfl] at hfl; cases hfl

/-- The executor that never begins a pass while a firing is in flight fails the coverage: at the
second termination test `t` is in flight and the loop is live. -/
theorem conc002_noBegin_uncovered : ¬ conc002Covers (conc002_noBegin (N := Nat) (T := Nat)) := by
  intro hc
  obtain ⟨s, -, -, -, hp⟩ := step_of_check xstep (C := conc002_cT)
    (o := xrun conc002_cT (xinit conc002_m0 0) conc002_toTest) (l := .begin)
    (p := fun s _ => decide (s.phase = .test) && liveB conc002_cT s && !s.fl.isEmpty)
    (by decide)
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hp
  obtain ⟨⟨hph, hl⟩, hfl⟩ := hp
  have hne : s.fl ≠ [] := fun h => by simp [h] at hfl
  obtain ⟨_, -, h0⟩ := hc.1 conc002_cT s hph hl hne
  exact hne (h0 rfl)

/-! ### Every line exercised, and the re-entrant executor -/

/-- Every line of CONC-002 is exercised by the reference: `t` starts, takes `7` from `0` and
leaves a firing in flight with no outcome (lines 1 and 2, AC1); with `t` in flight `u` starts
too, two firings in flight (AC2); at the next termination test, with `t` in flight, the loop
begins a firing pass (line 3, AC3); `v` loses the token of `0` to `t` and is passed over
(line 4); with `t` in flight, the update arms `w`, which `t`'s start has just enabled
(line 5); and on a configuration that is not re-entrant the update after `t`'s start finds `t`
enabled and in flight and leaves it without a stamp (line 6). -/
@[evidence nonvacuous CONC_002]
theorem CONC_002_nonvacuous :
    (∃ s s', RefExec conc002_cT s (.start "t" false) s' ∧ s.M 0 = [7, 8] ∧ s'.M 0 = [8] ∧
      s'.fl.length = 1) ∧
    (∃ s s', RefExec conc002_cTU s (.start "u" false) s' ∧ s'.fl.length = 2) ∧
    (∃ s s', RefExec conc002_cT s .begin s' ∧ s.phase = .test ∧ s.fl.length = 1) ∧
    (∃ s s', RefExec conc002_cTV s (.lose "v") s') ∧
    (∃ s s', RefExec conc002_cTW s .update s' ∧ InFlight s "t" ∧ ¬ InFlight s "w" ∧
      enabledNA (qCount s.M) conc002_w.core = true ∧ stampOf (s.st "w") = none ∧
      (stampOf (s'.st "w")).isSome = true) ∧
    (∃ tr, XRun RefExec conc002_cT (xinit conc002_m0 0) tr ∧ ∃ x ∈ tr, x.2.1 = .update ∧
      InFlight x.2.2 "t" ∧ enabledNA (qCount x.2.2.M) conc002_t.core = true ∧
      stampOf (x.2.2.st "t") = none) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := conc002_cT)
      (o := xrun conc002_cT (xinit conc002_m0 0) conc002_pre) (l := .start "t" false)
      (p := fun s s' => s.M 0 == [7, 8] && s'.M 0 == [8] && s'.fl.length == 1) (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', hs, hp.1.1, hp.1.2, hp.2⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := conc002_cTU)
      (o := xrun conc002_cTU (xinit conc002_m0 0) (conc002_pre ++ [.start "t" false]))
      (l := .start "u" false) (p := fun _ s' => s'.fl.length == 2) (by decide)
    exact ⟨s, s', hs, by simpa using hp⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := conc002_cT)
      (o := xrun conc002_cT (xinit conc002_m0 0) conc002_toTest) (l := .begin)
      (p := fun s _ => decide (s.phase = .test) && s.fl.length == 1) (by decide)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
    exact ⟨s, s', hs, hp.1, hp.2⟩
  · obtain ⟨s, s', -, hs, -⟩ := step_of_check xstep (C := conc002_cTV)
      (o := xrun conc002_cTV (xinit conc002_m1 0) (conc002_pre ++ [.start "t" false]))
      (l := .lose "v") (p := fun _ _ => true) (by decide)
    exact ⟨s, s', hs⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := conc002_cTW)
      (o := xrun conc002_cTW (xinit conc002_m2 0) conc002_toUpdateEve) (l := .update)
      (p := fun s s' => inFlightN s "t" && !inFlightN s "w" &&
        enabledNA (qCount s.M) conc002_w.core && (stampOf (s.st "w")).isNone &&
        (stampOf (s'.st "w")).isSome)
      (by decide)
    simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none] at hp
    obtain ⟨⟨⟨⟨hi, hw⟩, he⟩, hn⟩, hst⟩ := hp
    refine ⟨s, s', hs, hi, fun h => ?_, he, hn, hst⟩
    have : inFlightN s "w" = true := h
    rw [hw] at this; cases this
  · obtain ⟨tr, hr, hp⟩ := conc002_run_of_check xstep
      (C := conc002_cT) (s0 := xinit conc002_m0 0) (ls := conc002_toUpdate)
      (p := fun tr => tr.any fun x => (match x.2.1 with | .update => true | _ => false) &&
        inFlightN x.2.2 "t" && enabledNA (qCount x.2.2.M) conc002_t.core &&
        (stampOf (x.2.2.st "t")).isNone)
      (by decide)
    obtain ⟨⟨s, l, s'⟩, hx, hb⟩ := List.any_eq_true.mp hp
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hb
    obtain ⟨⟨⟨hl, hin⟩, he⟩, hst⟩ := hb
    refine ⟨tr, hr, ⟨s, l, s'⟩, hx, ?_, hin, he, hst⟩
    cases l <;> simp at hl ⊢

/-- ✓ CONC-002 allows a re-entrant executor (Rust, Python; ruling D8 (b)): the reference meets
CONC-002, and on a re-entrant configuration it starts `t`, re-arms it at the next update and
starts it again while the first firing is in flight. Line 6 binds only a configuration that is
not re-entrant. -/
@[evidence allows CONC_002]
theorem CONC_002_allows_reentrant :
    CONC_002 (RefExec (N := Nat) (T := Nat)) ∧
      ∃ tr, XRun RefExec conc002_cRe (xinit conc002_m0 0) tr ∧
        ∃ x ∈ tr, (∃ sy, x.2.1 = .start "t" sy) ∧ InFlight x.1 "t" := by
  refine ⟨CONC_002_reference, ?_⟩
  obtain ⟨tr, hr, hp⟩ := conc002_run_of_check xstep
    (C := conc002_cRe) (s0 := xinit conc002_m0 0) (ls := conc002_twice)
    (p := fun tr => tr.any (conc002_restart "t")) (by decide)
  obtain ⟨x, hx, hb⟩ := List.any_eq_true.mp hp
  obtain ⟨sy, hl, hin⟩ := conc002_restart_spec hb
  exact ⟨tr, hr, x, hx, ⟨sy, hl⟩, hin⟩

end Libpetri.Spec
