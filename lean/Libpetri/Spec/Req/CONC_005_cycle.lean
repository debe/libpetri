import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Exec
import Libpetri.Spec.Text.CONC_005

set_option linter.missingDocs true

/-!
# CONC-005, executor companion: the dirty set over the cycle (`spec/05-concurrency.md`)

The second block of CONC-005 (ruling D33 (a)): the same sentences as `CONC_005`, stated over an
abstract executor `R : XRel N T` (glossary `GlossaryExec.lean`) instead of the atomic timed step.
It carries what the atomic step cannot show: an injected token, a firing whose consumption (its
start) and deposit (its commit, timeout deposit or publication) are separate steps with other
steps between, and the enablement update of a cycle.

The four lines:

1. a write of one of a reaped transition's arc places ends its reaping;
2. an update leaves a reaped transition reaped (design repair R9);
3. on runs from a state with no pass order left, only such a write ends a reaping (R9);
4. a consumption, a deposit or an injection that writes none of a transition's arc places leaves
   its enablement as it was.

The evidence checks the statement against the reference executor (`RefExec`) and against wrong
executors: for line 1 an injection, a firing's commit and a start that drains an empty reset place,
each not ending a reaping; for line 2 an update that re-evaluates reaped transitions (the
`XPol.updReaped` mutant of the design); for line 3 a firing pass that also visits the reaped
transitions and passes over them; for line 4 a start that consumes through a read arc.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## The places a step writes -/

section Writes

variable {N T : Type}

/-- **Glossary: Write**, for a step of the executor (ruling D6): the step labelled `l` from state
`s` writes place `p`. A start consumes from the input places and drains the reset places of the
head of the pass's ready order (whether or not a token moves); a commit or a timeout deposit
deposits into the places of the emission it settles; a publication deposits into the places of
the oldest flushed batch; an injection writes the place of the oldest queued event. No other step
writes a place.

This is the readable form of membership in `cycWrites` (`GlossaryExec.lean`, the Write the
TIME-013 companion also reads), place for place and label for label (`conc005c_writes_iff`): a
start writes the places of the head of the order whatever name its label carries, and a
publication or an injection writes the places of the head of its queue whatever identity its
label carries. So CONC-005 and TIME-013 judge one write. -/
def conc005StepWrites (s : XSt N T) : XLbl N T → N → Prop
  | .start _ _, p => ∃ t rest, s.order = t :: rest ∧ (p ∈ inPlaces t ∨ ResetArc t p)
  | .commit i, p => ∃ f e, s.fl.find? (·.id == i) = some f ∧ f.out = some (.ok e) ∧
      p ∈ e.map Prod.fst
  | .tdeposit i, p => ∃ f e, s.fl.find? (·.id == i) = some f ∧ f.out = some (.timedOut e) ∧
      p ∈ e.map Prod.fst
  | .publish _, p => ∃ i b rest, s.pq = (i, b) :: rest ∧ p ∈ b.map Prod.fst
  | .inject _, p => ∃ k x rest, s.eq = (k, p, x) :: rest
  | _, _ => False

/-- A step writes a place exactly when the place is in the list of the places it writes. -/
theorem conc005c_writes_iff (s : XSt N T) (l : XLbl N T) (p : N) :
    conc005StepWrites s l p ↔ p ∈ cycWrites s l := by
  cases l with
  | start n sy =>
    simp only [conc005StepWrites, cycWrites]
    cases s.order with
    | nil => simp
    | cons t rest => simp [ResetArc]
  | commit i =>
    simp only [conc005StepWrites, cycWrites]
    cases s.fl.find? (·.id == i) with
    | none => simp
    | some f =>
      cases hf : f.out with
      | none => simp [hf]
      | some o => cases o <;> simp [hf]
  | tdeposit i =>
    simp only [conc005StepWrites, cycWrites]
    cases s.fl.find? (·.id == i) with
    | none => simp
    | some f =>
      cases hf : f.out with
      | none => simp [hf]
      | some o => cases o <;> simp [hf]
  | publish i =>
    simp only [conc005StepWrites, cycWrites]
    cases s.pq with
    | nil => simp
    | cons b rest => obtain ⟨i', b⟩ := b; simp
  | inject k =>
    simp only [conc005StepWrites, cycWrites]
    cases s.eq with
    | nil => simp
    | cons e rest => obtain ⟨k', q, x⟩ := e; simp [eq_comm]
  | _ => simp [conc005StepWrites, cycWrites]

end Writes

/-! ## CONC-005 over the executor cycle -/

requirement CONC_005_cycle
  id "CONC-005"
  title "Dirty Set Optimization (executor cycle)"
  kind B
  scope "all executors"
  source verbatim "spec/05-concurrency.md"
  covers CONC_005.s1, CONC_005.s2, CONC_005.s3, CONC_005.s4
  reading "For every executor R, every configuration C and every transition u:"
          "if the net of C holds u under its name, a step of R that writes one of u's arc places (a start from a state whose pass order begins with a transition that consumes from it or drains it, a commit, timeout deposit or publication that deposits into it, an injection that lands in it) leaves u not reaped when u was reaped before it;"
          "if the net of C holds u under its name, an update step of R leaves u reaped when u was reaped before it;"
          "if the net of C holds u under its name, then on every run of R from a state whose firing pass has no ready order left, every step that leaves u not reaped after u was reaped before it writes one of u's arc places;"
          "a start, commit, timeout deposit, publication or injection step of R that writes none of u's arc places leaves u enabled on the marking exactly when u was enabled on the marking before it."
  assumes "The model is an executor R : XRel N T (glossary GlossaryExec.lean): R C s l s' says that under configuration C the step labelled l leads from executor state s to s'. A transition name holds a clock status: off, armed at a stamp, or reaped (Status); ReapedE is the glossary's Reaped in the executor state. The witness is the reference executor RefExec (Reference/Exec.lean). This block is the executor companion of CONC_005 (ruling D33 (a): a second block with the same ID). CONC_005 states the first three quoted sentences over the atomic timed step (RefTStep); this block adds what that step cannot show: the injected token, the consumption and the deposit of a firing as separate steps with other steps between, and the enablement update of a cycle."
          "A step writes a place in the sense of the glossary's Write (ruling D6), read off the step and the state it starts from (conc005StepWrites): a start consumes from the input places and drains the reset places of the head of the pass's ready order, whether or not a token moves; a commit or a timeout deposit deposits into the places of the emission it settles; a publication deposits into the places of the oldest flushed batch; an injection writes the place of the oldest queued event. No other step writes a place: a failed firing deposits nothing ([EXEC-030]), an action's outside steps buffer, flush and return without touching the marking ([CONC-001]), and reading through a read arc or testing through an inhibitor arc is no write. Arc place is the glossary term: an input, read, inhibitor or reset place. This is the Write of the TIME-013 companion (cycWrites, TIME_cycle.lean) label for label: a start writes the places of the head of its order whatever name its label carries, so the two blocks judge the same steps to write the same places."
          "A re-run of a transition's enablement check is read through what it decides, as in CONC_005. The reference executor has no dirty set: its update re-evaluates every name in every cycle (design repair R15). For a transition that is armed or off this is not observable: re-running the check of a transition none of whose arc places was written gives the verdict it gave before (line 4), an update keeps the stamp of an armed name whose clock runs and whose transition is enabled ([TIME-012], line 4 of TIME_012_cycle), and no step other than an update moves a stamp ([TIME-010], line 2 of TIME_010_cycle). An update that restamps every armed transition re-runs their clocks with no write; it breaks TIME_012_cycle (TIME_012_cycle_forbids_restampAll), not this block. A re-run is observable for a reaped transition, which is enabled and holds no clock: re-running its check would arm it again, the next deadline step would reap it again, and so on, a storm of TransitionTimedOut events (design repair R9, clash conc-a#6, ruling D6). So the second and the fourth quoted sentences are lines 2 and 3: an update leaves a reaped transition reaped, and only a write of one of its arc places ends its reaping. An update that re-evaluates reaped transitions (refXPol with updReaped false) breaks both (CONC_005_cycle_forbids_reEvaluateAll)."
          "Line 1 is the first quoted sentence for a reaped transition, and the fourth quoted sentence's 'shall end its reaped state': the write ends the reaping, so the next enablement update re-runs the check and arms the transition if it is enabled. That this update leaves every enabled transition that is not reaped holding a clock, unless the executor is not re-entrant and a firing of the transition is in flight, is [CONC-002] (line 5), cited, not restated; the stamp it takes is [TIME-010]. Line 1 asks only that the name is no longer reaped; that the write leaves it off, not armed, is line 5 of TIME_013_cycle with line 2 of TIME_010_cycle. Each kind of write is checked: an injection (CONC_005_cycle_forbids_injectNoWrite), the deposit of a firing at its commit (CONC_005_cycle_forbids_commitNoWrite) and the consumption of a firing at its start, a drain of a reset place that is already empty included (CONC_005_cycle_forbids_emptyDrainNoWrite), each not ending the reaping of a transition whose arc place it writes, break line 1. For a transition that is armed or off the first sentence holds because the update re-evaluates every name; that a written armed transition that stays enabled stays armed, and whether its clock restarts, is [TIME-010] and [TIME-012]."
          "The model clears the reaped status at the write itself (ruling D6, the write rule unreap of GlossaryExec.lean), because it has no dirty set: the write is the step where a dirty bit would be set, and the next update re-runs the check of every name that is not reaped. An executor that keeps the name reaped at the write, records the write in a dirty set and clears the reaping at the next update arms the same transitions at that update, but as a step relation it breaks lines 1 and 2; the model does not allow that representation, and the status a write leaves is the model's reading of 'dirty', not a further sentence of CONC-005."
          "Line 3 is read on runs from a state whose firing pass has no ready order left (s0.order = []: the initial state xinit, or a restored marking), not on every step from every state. A firing pass passes over the head of its order without starting it by dropping its clock (lose), which turns the name off, so a reaped transition at the head of an order would stop being reaped without a write. The reference never puts a reaped transition in an order: the ready order holds only Ready transitions, which hold a clock ([EXEC-002], [TIME-014]), and no step reaps inside a pass (conc005c_OrderInv). An executor whose pass also visits the reaped transitions and passes over them breaks line 3 (CONC_005_cycle_forbids_visitReaped); it meets lines 1, 2 and 4, so only line 3 excludes it (CONC_005_cycle_mutant_noRunLine_killed). Line 2 states for the update what line 3 states on runs, and holds from every state."
          "TIME-013 carries the same persistence rule in the same words ('only a firing or an injected token that writes one of its arc places shall end its reaped state'), and its companion TIME_cycle.lean states it in lines 3 to 5 of TIME_013_cycle with the same Write. CONC-005 quotes it as the dirty-set rule: a reaped transition is the one whose check the executor does not re-run. The two encodings agree on line 2. Line 3 here is read on runs and allows no lose step, where line 4 of TIME_013_cycle holds from every state and allows a lose of the name; so line 3 also excludes the executor that passes over reaped names, which TIME_013_cycle allows."
          "Line 4 is the third quoted sentence at the grain of the executor: the consumption of a firing (start), its deposit (commit, timeout deposit, publication) and an injected token (inject) are separate steps, the steps CONC-001 calls deposits (startOrDeposit, the labels CONC-001's line 2 reads), and each one that writes none of u's arc places leaves u's enablement on the marking as it was. Every other step leaves the marking as it was, so u's enablement too: that is line 2 of [CONC-001] (CONC_001), cited, not restated. Line 4 is the soundness of the reverse index in the interleaved case CONC_005 defers to this block, and it holds of every transition, in the net or not. A start that also takes the token of a read place (a read arc treated as an input arc) breaks it (CONC_005_cycle_forbids_readConsumes)."
          "The exception 'or when the transition itself fires' needs no line here: a reaped transition holds no clock, so it does not start ([EXEC-003], [TIME-013]), and a start turns the started name off, after which the next update re-evaluates it like any name that is off ([CONC-002] line 5). Rust marks the fired transition dirty when it starts (bitmap_backend.rs post_fire); Java and TypeScript also when its completion is processed."
          "Re-entrancy follows ruling D8 (b): the configuration carries it (Cfg.reentrant). In Java and TypeScript, which are not re-entrant, the enablement update skips a transition whose firing is in flight although a firing or an injected token wrote one of its arc places, and re-evaluates it at the first update after its completion is processed, which writes none of its arc places. In the model such a transition is off, not reaped (InFlightOff), so lines 1 to 3 do not speak of it and line 4 speaks of the marking only; that it holds no clock while in flight and holds one again after the first update that follows its completion is [CONC-002] lines 5 and 6, cited, not restated."
          "Transitions are identified by name (ruling D10): the clock status is kept per name, and lines 1 to 3 speak of the transition the net holds under the name (findT, the first transition with that name), as the reference's write rule (unreap) does. With distinct names (Cfg.WF.names, which the statement does not assume) that is every transition of the net."
          "The enablement check is read as Enabled: the transitions of the model carry no match specification (ruling D30); the ν-match check of a transition with one ([NU-020]) reads only its correlated inputs, which are arc places, so line 4 holds of it as well. It is not encoded here, as in CONC_005."
          "The body's first paragraph (only transitions affected by a place need re-evaluation; a reverse index maps each place to the transitions that reference it) is read as in CONC_005: a transition references a place when the place is one of its arc places (clash conc-a#7). The paragraph after the quoted sentences (the dirty set is a bitmap whose bits the executor sets and clears, only dirty transitions are re-evaluated each cycle) is representation, kind Q: the model has no dirty set and no bit."
          "AC1 (adding a token to place P only marks transitions connected to P as dirty) is lines 1 and 4 at the grain of the executor: in CONC_005_cycle_nonvacuous an injection into place 0, the input place of the reaped transition u, ends its reaping and the next update arms it, an injection into place 1, none of u's arc places, leaves u reaped and its enablement as it was, and the two halves of a firing end a reaping as well: a start that drains u's empty inhibitor place, and a commit that deposits into u's input place. AC2 (transitions not connected to P are not re-evaluated) is lines 2 and 3, with the mutants CONC_005_cycle_forbids_reEvaluateAll and CONC_005_cycle_forbids_visitReaped; CONC_005_cycle_nonvacuous exercises an update while u is reaped. AC3 (dirty bits are cleared after re-evaluation) is representation and is not encoded. The test derivation (50 transitions, exactly 3 re-evaluated) counts re-evaluations, a cost ([PERF-003]), and is not encoded."
          "Out of this block: the deadline step that reaps a transition is [TIME-013] and [EXEC-001]; the stamp a newly armed transition takes is [TIME-010]; how a start's drains take the pass-visible prefix of a queue is [EXEC-003] and [EXEC-013]; the injection request and its queue are [ENV-003]."
  signoff "2026-11-13 5743a54f91350a9d ai"
  statement : ∀ {N T : Type} [DecidableEq N], XRel N T → Prop :=
    fun R => ∀ (C : Cfg _ _) (u : Trans _),
      (findT C u.core.name = some u → ∀ l, on (fun s s' => R C s l s'), shall (fun s s' =>
          ReapedE s u → (∃ p, ArcPlace u p ∧ conc005StepWrites s l p) → ¬ ReapedE s' u)) ∧
      (findT C u.core.name = some u → on (fun s s' => R C s .update s'), shall (fun s s' =>
          ReapedE s u → ReapedE s' u)) ∧
      (findT C u.core.name = some u → ∀ s0 tr, s0.order = [] → XRun R C s0 tr → ∀ x ∈ tr,
          ReapedE x.1 u → ¬ ReapedE x.2.2 u → ∃ p, ArcPlace u p ∧ conc005StepWrites x.1 x.2.1 p) ∧
      (∀ l, startOrDeposit l = true → on (fun s s' => R C s l s'), shall (fun s s' =>
          (∀ p, ArcPlace u p → ¬ conc005StepWrites s l p) →
            (Enabled u (qCount s'.M) ↔ Enabled u (qCount s.M))))

/- The pinned readable form of the companion: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CONC_005_cycle : {N T : Type} → [DecidableEq N] → XRel N T → Prop :=
fun {N T} [DecidableEq N] R =>
  ∀ (C : Cfg N T) (u : Reference.Trans N),
    (findT C u.core.name = some u →
        ∀ (l : XLbl N T),
          on fun s s' => R C s l s', shall fun s s' =>
            ReapedE s u → (∃ p, ArcPlace u p ∧ conc005StepWrites s l p) → ¬ReapedE s' u) ∧
      (findT C u.core.name = some u →
          on fun s s' => R C s XLbl.update s', shall fun s s' => ReapedE s u → ReapedE s' u) ∧
        (findT C u.core.name = some u →
            ∀ (s0 : XSt N T) (tr : List (XStep N T)),
              s0.order = [] →
                XRun R C s0 tr →
                  ∀ x ∈ tr, ReapedE x.1 u → ¬ReapedE x.2.2 u → ∃ p, ArcPlace u p ∧ conc005StepWrites x.1 x.2.1 p) ∧
          ∀ (l : XLbl N T),
            startOrDeposit l = true →
              on fun s s' => R C s l s', shall fun s s' =>
                (∀ (p : N), ArcPlace u p → ¬conc005StepWrites s l p) →
                  (Enabled u (qCount s'.M) ↔ Enabled u (qCount s.M))
-/
#guard_msgs in #print CONC_005_cycle

/-! ## The reference executor -/

section Reference

variable {N T : Type} [DecidableEq N]

/-- A write of one of `u`'s arc places turns `u`'s reaped name off. -/
theorem conc005c_unreap_hit {C : Cfg N T} {ps : List N} {st : String → Status} {u : Trans N}
    (hu : findT C u.core.name = some u) (hr : st u.core.name = .reaped) {p : N}
    (hp : p ∈ arcPlaces u) (hps : p ∈ ps) : unreap C ps st u.core.name = .off := by
  have ha : (arcPlaces u).any (fun q => decide (q ∈ ps)) = true :=
    List.any_eq_true.mpr ⟨p, hp, by simpa using hps⟩
  unfold unreap
  rw [hr, hu]
  simp [ha]

/-- A write that leaves `u`'s reaped name not reaped wrote one of `u`'s arc places. -/
theorem conc005c_unreap_change {C : Cfg N T} {ps : List N} {st : String → Status} {u : Trans N}
    (hu : findT C u.core.name = some u) (hr : st u.core.name = .reaped)
    (hn : unreap C ps st u.core.name ≠ .reaped) : ∃ p, ArcPlace u p ∧ p ∈ ps := by
  refine Classical.byContradiction fun hc => hn ?_
  have ha : (arcPlaces u).any (fun q => decide (q ∈ ps)) = false := by
    rw [List.any_eq_false]
    intro q hq hqs
    exact hc ⟨q, (arcPlace_iff u q).2 hq, by simpa using hqs⟩
  unfold unreap
  rw [hr, hu]
  simp [ha]

/-- A start of another transition keeps a reaped name reaped before its write is applied. -/
theorem conc005c_afterStart_reaped {P : XPol N T} {C : Cfg N T} {s : XSt N T} {t : Trans N}
    {n : String} (hne : n ≠ t.core.name) (hr : s.st n = .reaped) :
    afterStart P C s t n = .reaped := by
  unfold afterStart
  rw [if_neg hne, hr]

/-- The reference update keeps a reaped name of the net reaped. -/
theorem conc005c_updSt_reaped {C : Cfg N T} {s : XSt N T} {u : Trans N}
    (hu : findT C u.core.name = some u) (hr : s.st u.core.name = .reaped) :
    updSt refXPol C s u.core.name = .reaped := by
  unfold updSt
  rw [hu]
  simp [hr, refXPol]

/-- Line 1 for the reference: a write of one of `u`'s arc places ends `u`'s reaping. -/
theorem conc005c_line1 {C : Cfg N T} {u : Trans N} (hu : findT C u.core.name = some u)
    {s s' : XSt N T} {l : XLbl N T} (h : RefExec C s l s') (hr : ReapedE s u)
    (hw : ∃ p, ArcPlace u p ∧ conc005StepWrites s l p) : ¬ ReapedE s' u := by
  obtain ⟨p, hp, hw⟩ := hw
  have hp' := (arcPlace_iff u p).1 hp
  unfold ReapedE at hr ⊢
  cases l with
  | commit i =>
    obtain ⟨f, e, hf, he, hm⟩ := hw
    obtain ⟨f', e', hf', he', -, -, -, rfl⟩ := commitStep_some h
    rw [hf, Option.some.injEq] at hf'
    subst hf'
    rw [he, Option.some.injEq, Outcome.ok.injEq] at he'
    subst he'
    show unreap C (e.map Prod.fst) s.st u.core.name ≠ .reaped
    rw [conc005c_unreap_hit hu hr hp' hm]
    simp
  | tdeposit i =>
    obtain ⟨f, e, hf, he, hm⟩ := hw
    obtain ⟨f', e', hf', he', -, -, rfl⟩ := tdepositStep_some h
    rw [hf, Option.some.injEq] at hf'
    subst hf'
    rw [he, Option.some.injEq, Outcome.timedOut.injEq] at he'
    subst he'
    show unreap C (e.map Prod.fst) s.st u.core.name ≠ .reaped
    rw [conc005c_unreap_hit hu hr hp' hm]
    simp
  | publish i =>
    obtain ⟨j, b, rest, hpq, hm⟩ := hw
    obtain ⟨b', rest', hpq', -, -, rfl⟩ := publishStep_some h
    rw [hpq] at hpq'
    simp only [List.cons.injEq, Prod.mk.injEq] at hpq'
    obtain ⟨⟨-, rfl⟩, rfl⟩ := hpq'
    show unreap C (b.map Prod.fst) s.st u.core.name ≠ .reaped
    rw [conc005c_unreap_hit hu hr hp' hm]
    simp
  | inject k =>
    obtain ⟨j, x, rest, heq⟩ := hw
    obtain ⟨p', x', rest', heq', -, -, -, rfl⟩ := injectStep_some h
    rw [heq] at heq'
    simp only [List.cons.injEq, Prod.mk.injEq] at heq'
    obtain ⟨⟨-, rfl, rfl⟩, rfl⟩ := heq'
    show unreap C [p] s.st u.core.name ≠ .reaped
    rw [conc005c_unreap_hit hu hr hp' (List.mem_singleton_self p)]
    simp
  | start n sy =>
    obtain ⟨t, rest, ho, hpw⟩ := hw
    obtain ⟨t', rest', ho', -, -, -, hn', hst', -, rfl⟩ := startStep_some h
    rw [ho] at ho'
    simp only [List.cons.injEq] at ho'
    obtain ⟨rfl, rfl⟩ := ho'
    show unreap C (inPlaces t ++ t.core.resets) (afterStart refXPol C s t) u.core.name ≠ .reaped
    have hne : u.core.name ≠ t.core.name := by
      intro he
      rw [he, hn'] at hr
      rw [hr] at hst'
      simp [stampOf] at hst'
    rw [conc005c_unreap_hit hu (conc005c_afterStart_reaped hne hr) hp' (List.mem_append.2 hpw)]
    simp
  | _ => exact absurd hw (by simp [conc005StepWrites])

/-- Line 2 for the reference: the update keeps a reaped name of the net reaped. -/
theorem conc005c_line2 {C : Cfg N T} {u : Trans N} (hu : findT C u.core.name = some u)
    {s s' : XSt N T} (h : RefExec C s .update s') (hr : ReapedE s u) : ReapedE s' u := by
  obtain ⟨-, -, rfl⟩ := xstepW_update h
  exact conc005c_updSt_reaped hu hr

/-- Line 4 for the reference: a step that writes none of `u`'s arc places keeps the count of
every one of them, so `u`'s enablement. -/
theorem conc005c_line4 {C : Cfg N T} {u : Trans N} {s s' : XSt N T} {l : XLbl N T}
    (h : RefExec C s l s') (hw : ∀ p, ArcPlace u p → ¬ conc005StepWrites s l p) :
    (Enabled u (qCount s'.M) ↔ Enabled u (qCount s.M)) := by
  suffices hM : ∀ p ∈ arcPlaces u, qCount s'.M p = qCount s.M p by
    unfold Enabled
    rw [enabledNA_congr hM]
  intro p hp
  have hw' := hw p ((arcPlace_iff u p).2 hp)
  by_cases ho : l.outside = true
  · obtain ⟨hM, -⟩ := xstepW_outside_frame h ho
    rw [hM]
  cases l with
  | commit i =>
    obtain ⟨f, e, hf, he, -, -, -, rfl⟩ := commitStep_some h
    exact qCount_qAppend_of_not_mem fun hm => hw' ⟨f, e, hf, he, hm⟩
  | tdeposit i =>
    obtain ⟨f, e, hf, he, -, -, rfl⟩ := tdepositStep_some h
    exact qCount_qAppend_of_not_mem fun hm => hw' ⟨f, e, hf, he, hm⟩
  | publish i =>
    obtain ⟨b, rest, hpq, -, -, rfl⟩ := publishStep_some h
    exact qCount_qAppend_of_not_mem fun hm => hw' ⟨i, b, rest, hpq, hm⟩
  | inject k =>
    obtain ⟨q, x, rest, heq, -, -, -, rfl⟩ := injectStep_some h
    exact qCount_qAppendOne_of_ne fun hpq => hw' ⟨k, x, rest, hpq ▸ heq⟩
  | start n sy =>
    obtain ⟨t, rest, ho', -, -, -, hn, -, -, rfl⟩ := startStep_some h
    show qCount (liveAfter s t) p = qCount s.M p
    simp only [qCount]
    rw [liveAfter_of_not_mem fun hm => hw' ⟨t, rest, ho', List.mem_append.1 hm⟩]
  | fail i =>
    obtain ⟨f, -, -, -, rfl⟩ := failStep_some h
    rfl
  | endCompletions =>
    obtain ⟨-, -, -, -, rfl⟩ := xstepW_endCompletions h
    rfl
  | endPublications =>
    obtain ⟨-, -, -, rfl⟩ := xstepW_endPublications h
    rfl
  | discard k =>
    obtain ⟨-, -, -, -, -, -, -, rfl⟩ := discardStep_some h
    rfl
  | snapshot a =>
    obtain ⟨-, -, -, rfl⟩ := snapshotStep_some h
    rfl
  | endEvents =>
    obtain ⟨-, -, -, rfl⟩ := xstepW_endEvents h
    rfl
  | update =>
    obtain ⟨-, -, rfl⟩ := xstepW_update h
    rfl
  | deadline ns =>
    obtain ⟨-, -, -, rfl⟩ := xstepW_deadline h
    rfl
  | finish c =>
    cases c with
    | quiescent => obtain ⟨-, -, -, rfl⟩ := xstepW_finishQuiescent h; rfl
    | closed => obtain ⟨-, -, -, -, rfl⟩ := xstepW_finishClosed h; rfl
    | terminal => obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h; rfl
    | stopped => obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h; rfl
  | begin =>
    obtain ⟨-, -, -, -, rfl⟩ := xstepW_begin h
    rfl
  | lose n =>
    obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := loseStep_some h
    rfl
  | endPass =>
    obtain ⟨-, -, -, -, rfl⟩ := xstepW_endPass h
    rfl
  | park tmr =>
    obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := parkStep_some h
    rfl
  | wake =>
    obtain ⟨-, -, rfl⟩ := wakeStep_some h
    rfl
  | _ => simp [XLbl.outside] at ho

/-! ### Line 3: no reaped name in a pass order -/

/-- The invariant line 3 needs: no transition of the pass's ready order has a reaped name, and an
order is left only inside a pass or after the run finished. -/
def conc005c_OrderInv (s : XSt N T) : Prop :=
  (∀ t ∈ s.order, s.st t.core.name ≠ .reaped) ∧
    (s.order ≠ [] → s.phase = .pass ∨ isExecPhase s.phase = false)

omit [DecidableEq N] in
/-- A state with no order left meets the invariant. -/
theorem conc005c_inv_nil {s : XSt N T} (h : s.order = []) : conc005c_OrderInv s :=
  ⟨by simp [h], fun hn => absurd h hn⟩

omit [DecidableEq N] in
/-- Outside a pass, a running loop has no order left. -/
theorem conc005c_order_nil {s : XSt N T} (hi : conc005c_OrderInv s) (hp : s.phase ≠ .pass)
    (he : isExecPhase s.phase = true) : s.order = [] := by
  refine Classical.byContradiction fun hne => ?_
  rcases hi.2 hne with h | h
  · exact hp h
  · rw [he] at h
    cases h

omit [DecidableEq N] in
/-- A step from a running phase other than the pass that keeps the order keeps the invariant. -/
theorem conc005c_inv_keep {s s' : XSt N T} (hi : conc005c_OrderInv s) (hp : s.phase ≠ .pass)
    (he : isExecPhase s.phase = true) (ho : s'.order = s.order) : conc005c_OrderInv s' :=
  conc005c_inv_nil (ho.trans (conc005c_order_nil hi hp he))

/-- A transition of a pass's ready order holds a clock, so its name is not reaped
([EXEC-002] line 1: the order holds only ready transitions). -/
theorem conc005c_readyOrder_not_reaped {C : Cfg N T} {s : XSt N T} {t : Trans N}
    (ht : t ∈ readyOrder C s) : s.st t.core.name ≠ .reaped := by
  unfold readyOrder at ht
  simp only [List.mem_filterMap] at ht
  obtain ⟨i, hi, hti⟩ := ht
  have hmem := ((EXEC_002_reference _).1.mem_iff).1 hi
  rw [ReadyIn.mem_readyList] at hmem
  obtain ⟨hlt, hrd⟩ := hmem
  have hlt' : i < C.X.net.transitions.length := hlt
  rw [List.getElem?_eq_getElem hlt', Option.some.injEq] at hti
  subst hti
  have hR := (ReadyIn.ofTSt_ready _ _ _ _ i hlt').1 hrd
  intro hr
  have hs := hR.1.2
  simp [viewAt, hr, stampOf] at hs

omit [DecidableEq N] in
/-- A step that keeps the order, settles like `settle` and leaves reaped only names that were
reaped keeps the invariant. -/
theorem conc005c_inv_settle {s s' : XSt N T} {i : Nat} (hi : conc005c_OrderInv s)
    (ho : s'.order = s.order) (hph : s'.phase = (settle s i).phase)
    (hst : ∀ n, s'.st n = .reaped → s.st n = .reaped) : conc005c_OrderInv s' := by
  refine ⟨fun t ht hr => hi.1 t (ho ▸ ht) (hst _ hr), fun hne => ?_⟩
  rw [ho] at hne
  rw [hph]
  rcases hi.2 hne with hp | hp
  · left
    simp [settle, hp]
  · right
    have hna : s.phase ≠ .await := fun h => by rw [h] at hp; cases hp
    simp only [settle, if_neg hna]
    exact hp

/-- Every step of the reference keeps the invariant. -/
theorem conc005c_inv_step {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : RefExec C s l s') (hi : conc005c_OrderInv s) : conc005c_OrderInv s' := by
  cases l with
  | delay δ => cases xstepW_delay h; exact hi
  | write i p x => obtain ⟨f, -, -, rfl⟩ := writeStep_some h; exact hi
  | flush i =>
    obtain ⟨f, -, -, -, -, ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ := flushStep_some h <;> exact hi
  | ret i ok => obtain ⟨f, -, -, rfl⟩ := retStep_some h; exact hi
  | expire i e => obtain ⟨f, -, -, -, -, -, rfl⟩ := expireStep_some h; exact hi
  | request p x r =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := requestStep_some h <;> exact hi
  | drain => obtain ⟨-, rfl⟩ := drainStep_some h; exact hi
  | close => obtain ⟨-, rfl⟩ := closeStep_some h; exact hi
  | terminateNow => obtain ⟨-, rfl⟩ := terminateStep_some h; exact hi
  | commit i =>
    obtain ⟨f, e, -, -, -, -, -, rfl⟩ := commitStep_some h
    exact conc005c_inv_settle (i := i) hi rfl rfl fun n hn => (unreap_reaped hn).1
  | tdeposit i =>
    obtain ⟨f, e, -, -, -, -, rfl⟩ := tdepositStep_some h
    exact conc005c_inv_settle (i := i) hi rfl rfl fun n hn => (unreap_reaped hn).1
  | fail i =>
    obtain ⟨f, -, -, -, rfl⟩ := failStep_some h
    exact conc005c_inv_settle (i := i) hi rfl rfl fun _ hn => hn
  | endCompletions =>
    obtain ⟨hp, -, -, -, rfl⟩ := xstepW_endCompletions h
    exact conc005c_inv_keep hi (by simp [hp]) (by simp [hp, isExecPhase]) rfl
  | publish i =>
    obtain ⟨b, rest, -, -, hp, rfl⟩ := publishStep_some h
    refine conc005c_inv_keep hi ?_ ?_ rfl <;>
      rcases hp with hp | ⟨hp, -⟩ <;> simp [hp, isExecPhase]
  | endPublications =>
    obtain ⟨hp, -, -, rfl⟩ := xstepW_endPublications h
    exact conc005c_inv_keep hi (by simp [hp]) (by simp [hp, isExecPhase]) rfl
  | inject k =>
    obtain ⟨p, x, rest, -, -, -, hp, rfl⟩ := injectStep_some h
    refine conc005c_inv_keep hi ?_ ?_ rfl <;>
      rcases hp with hp | hp <;> simp [hp, isExecPhase]
  | discard k =>
    obtain ⟨p, x, rest, -, -, -, hp, rfl⟩ := discardStep_some h
    refine conc005c_inv_keep hi ?_ ?_ rfl <;>
      rcases hp with hp | hp <;> simp [hp, isExecPhase]
  | snapshot a =>
    obtain ⟨-, -, -, rfl⟩ := snapshotStep_some h
    exact hi
  | endEvents =>
    obtain ⟨hp, -, -, rfl⟩ := xstepW_endEvents h
    exact conc005c_inv_keep hi (by simp [hp]) (by simp [hp, isExecPhase]) rfl
  | update =>
    obtain ⟨hp, -, rfl⟩ := xstepW_update h
    exact conc005c_inv_keep hi (by simp [hp]) (by simp [hp, isExecPhase]) rfl
  | deadline ns =>
    obtain ⟨hp, -, -, rfl⟩ := xstepW_deadline h
    exact conc005c_inv_keep hi (by simp [hp]) (by simp [hp, isExecPhase]) rfl
  | finish c =>
    have hdone : ∀ s₁ : XSt N T, s₁.order = s.order → s₁.st = s.st →
        isExecPhase s₁.phase = false → conc005c_OrderInv s₁ := fun s₁ ho hst hph =>
      ⟨fun t ht => by rw [hst]; exact hi.1 t (ho ▸ ht), fun _ => Or.inr hph⟩
    cases c with
    | quiescent =>
      obtain ⟨-, -, -, rfl⟩ := xstepW_finishQuiescent h
      exact hdone _ rfl rfl rfl
    | closed =>
      obtain ⟨-, -, -, -, rfl⟩ := xstepW_finishClosed h
      exact hdone _ rfl rfl rfl
    | terminal =>
      obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h
      exact hdone _ rfl rfl rfl
    | stopped =>
      obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h
      exact hdone _ rfl rfl rfl
  | begin =>
    obtain ⟨-, -, -, -, rfl⟩ := xstepW_begin h
    exact ⟨fun t ht => conc005c_readyOrder_not_reaped ht, fun _ => Or.inl rfl⟩
  | start n sy =>
    obtain ⟨t, rest, ho, hp, -, -, -, -, -, rfl⟩ := startStep_some h
    refine ⟨fun t' ht' hr => ?_, fun _ => Or.inl hp⟩
    have h1 := afterStart_reaped (unreap_reaped hr).1
    exact hi.1 t' (by rw [ho]; exact List.mem_cons_of_mem _ ht') h1
  | lose n =>
    obtain ⟨t, rest, ho, hp, -, -, -, -, rfl⟩ := loseStep_some h
    refine ⟨fun t' ht' hr => ?_, fun _ => Or.inl hp⟩
    change (if t'.core.name = n then Status.off else s.st t'.core.name) = .reaped at hr
    split at hr
    · cases hr
    · exact hi.1 t' (by rw [ho]; exact List.mem_cons_of_mem _ ht') hr
  | endPass =>
    obtain ⟨-, -, ho, -, rfl⟩ := xstepW_endPass h
    exact conc005c_inv_nil ho
  | park tmr =>
    obtain ⟨hp, -, -, -, -, -, -, -, rfl⟩ := parkStep_some h
    exact conc005c_inv_keep hi (by simp [hp]) (by simp [hp, isExecPhase]) rfl
  | wake =>
    obtain ⟨hp, -, rfl⟩ := wakeStep_some h
    exact conc005c_inv_keep hi (by simp [hp]) (by simp [hp, isExecPhase]) rfl

/-- Line 3 for one step of the reference: a step from a state meeting the invariant that ends
`u`'s reaping writes one of `u`'s arc places. -/
theorem conc005c_line3_step {C : Cfg N T} {u : Trans N} (hu : findT C u.core.name = some u)
    {s s' : XSt N T} {l : XLbl N T} (h : RefExec C s l s') (hi : conc005c_OrderInv s)
    (hr : ReapedE s u) (hn : ¬ ReapedE s' u) : ∃ p, ArcPlace u p ∧ conc005StepWrites s l p := by
  unfold ReapedE at hr hn
  by_cases ho : l.outside = true
  · obtain ⟨-, hst, -⟩ := xstepW_outside_frame h ho
    rw [hst] at hn
    exact absurd hr hn
  cases l with
  | commit i =>
    obtain ⟨f, e, hf, he, -, -, -, rfl⟩ := commitStep_some h
    obtain ⟨p, hp, hm⟩ := conc005c_unreap_change hu hr hn
    exact ⟨p, hp, f, e, hf, he, hm⟩
  | tdeposit i =>
    obtain ⟨f, e, hf, he, -, -, rfl⟩ := tdepositStep_some h
    obtain ⟨p, hp, hm⟩ := conc005c_unreap_change hu hr hn
    exact ⟨p, hp, f, e, hf, he, hm⟩
  | publish i =>
    obtain ⟨b, rest, hpq, -, -, rfl⟩ := publishStep_some h
    obtain ⟨p, hp, hm⟩ := conc005c_unreap_change hu hr hn
    exact ⟨p, hp, i, b, rest, hpq, hm⟩
  | inject k =>
    obtain ⟨q, x, rest, heq, -, -, -, rfl⟩ := injectStep_some h
    obtain ⟨p, hp, hm⟩ := conc005c_unreap_change hu hr hn
    rw [List.mem_singleton] at hm
    subst hm
    exact ⟨p, hp, k, x, rest, heq⟩
  | start n sy =>
    obtain ⟨t, rest, ho', -, -, -, htn, hst', -, rfl⟩ := startStep_some h
    have hne : u.core.name ≠ t.core.name := by
      intro he
      rw [he, htn] at hr
      rw [hr] at hst'
      simp [stampOf] at hst'
    obtain ⟨p, hp, hm⟩ := conc005c_unreap_change hu
      (conc005c_afterStart_reaped (P := refXPol) (C := C) hne hr) hn
    exact ⟨p, hp, t, rest, ho', List.mem_append.1 hm⟩
  | lose n =>
    obtain ⟨t, rest, ho', -, -, -, htn, -, rfl⟩ := loseStep_some h
    exfalso
    by_cases hun : u.core.name = n
    · have ht := hi.1 t (by rw [ho']; exact List.mem_cons_self ..)
      rw [htn, ← hun] at ht
      exact ht hr
    · apply hn
      show (if u.core.name = n then Status.off else s.st u.core.name) = .reaped
      rw [if_neg hun]
      exact hr
  | update =>
    obtain ⟨-, -, rfl⟩ := xstepW_update h
    exact absurd (conc005c_updSt_reaped hu hr) hn
  | deadline ns =>
    obtain ⟨-, -, -, rfl⟩ := xstepW_deadline h
    exfalso
    apply hn
    show (if ns.contains u.core.name = true then Status.reaped else s.st u.core.name) = .reaped
    split
    · rfl
    · exact hr
  | fail i =>
    obtain ⟨f, -, -, -, rfl⟩ := failStep_some h
    exact absurd hr hn
  | endCompletions =>
    obtain ⟨-, -, -, -, rfl⟩ := xstepW_endCompletions h
    exact absurd hr hn
  | endPublications =>
    obtain ⟨-, -, -, rfl⟩ := xstepW_endPublications h
    exact absurd hr hn
  | discard k =>
    obtain ⟨q, x, rest, -, -, -, -, rfl⟩ := discardStep_some h
    exact absurd hr hn
  | snapshot a =>
    obtain ⟨-, -, -, rfl⟩ := snapshotStep_some h
    exact absurd hr hn
  | endEvents =>
    obtain ⟨-, -, -, rfl⟩ := xstepW_endEvents h
    exact absurd hr hn
  | finish c =>
    cases c with
    | quiescent => obtain ⟨-, -, -, rfl⟩ := xstepW_finishQuiescent h; exact absurd hr hn
    | closed => obtain ⟨-, -, -, -, rfl⟩ := xstepW_finishClosed h; exact absurd hr hn
    | terminal => obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h; exact absurd hr hn
    | stopped => obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h; exact absurd hr hn
  | begin =>
    obtain ⟨-, -, -, -, rfl⟩ := xstepW_begin h
    exact absurd hr hn
  | endPass =>
    obtain ⟨-, -, -, -, rfl⟩ := xstepW_endPass h
    exact absurd hr hn
  | park tmr =>
    obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := parkStep_some h
    exact absurd hr hn
  | wake =>
    obtain ⟨-, -, rfl⟩ := wakeStep_some h
    exact absurd hr hn
  | _ => simp [XLbl.outside] at ho

/-- Line 3 for the reference, on every run from a state meeting the invariant. -/
theorem conc005c_line3_run {C : Cfg N T} {u : Trans N} (hu : findT C u.core.name = some u) :
    ∀ (s : XSt N T) (tr : List (XStep N T)), conc005c_OrderInv s → XRun RefExec C s tr →
      ∀ x ∈ tr, ReapedE x.1 u → ¬ ReapedE x.2.2 u →
        ∃ p, ArcPlace u p ∧ conc005StepWrites x.1 x.2.1 p
  | _, [], _, _, x, hx => by cases hx
  | s, y :: tr, hi, ⟨h1, h2, h3⟩, x, hx => by
    have hi' : conc005c_OrderInv y.1 := h1 ▸ hi
    rcases List.mem_cons.1 hx with rfl | hx
    · exact conc005c_line3_step hu h2 hi'
    · exact conc005c_line3_run hu y.2.2 tr (conc005c_inv_step h2 hi') h3 x hx

end Reference

/-- ✓ The reference executor satisfies the companion block. Line 1: every write rule turns a
reaped name with a written arc place off (`unreap`). Line 2: the update keeps a reaped name of the
net reaped (`refXPol.updReaped`). Line 3: on a run from a state with no order left, no pass order
holds a reaped name (the ready order holds only transitions with a clock), so a reaped name
changes only by a write rule. Line 4: a step changes the queue of a place only if it writes it. -/
@[evidence holds CONC_005_cycle]
theorem CONC_005_cycle_reference {N T : Type} [DecidableEq N] :
    CONC_005_cycle (RefExec (N := N) (T := T)) := fun _ _ =>
  ⟨fun hu _ _ _ h hr hw => conc005c_line1 hu h hr hw,
   fun hu _ _ h hr => conc005c_line2 hu h hr,
   fun hu s0 tr h0 hrun => conc005c_line3_run hu s0 tr (conc005c_inv_nil h0) hrun,
   fun _ _ _ _ h hw => conc005c_line4 h hw⟩

/-! ## Decided runs -/

section Runs

variable {N T : Type}

/-- The graph of a step function: an executor. -/
def conc005c_graph (g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)) : XRel N T :=
  fun C s l s' => g C s l = some s'

/-- The state a run of the step function `g` from `s` along the labels `ls` ends in. -/
def conc005c_run (g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)) (C : Cfg N T) :
    XSt N T → List (XLbl N T) → Option (XSt N T)
  | s, [] => some s
  | s, l :: ls => (g C s l).bind fun s' => conc005c_run g C s' ls

/-- The run of the step function `g` from `s` along the labels `ls`, as the list of its steps. -/
def conc005c_trace (g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)) (C : Cfg N T) :
    XSt N T → List (XLbl N T) → Option (List (XStep N T))
  | _, [] => some []
  | s, l :: ls => (g C s l).bind fun s' => (conc005c_trace g C s' ls).map ((s, l, s') :: ·)

/-- A trace of `g` is a run of the executor of `g`. -/
theorem conc005c_trace_run {g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)}
    {C : Cfg N T} : ∀ {s : XSt N T} {ls : List (XLbl N T)} {tr : List (XStep N T)},
    conc005c_trace g C s ls = some tr → XRun (conc005c_graph g) C s tr
  | _, [], tr, h => by cases h; trivial
  | s, l :: ls, tr, h => by
    simp only [conc005c_trace] at h
    cases hg : g C s l with
    | none => simp [hg] at h
    | some s' =>
      cases ht : conc005c_trace g C s' ls with
      | none => simp [hg, ht] at h
      | some tr' =>
        simp only [hg, ht, Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst h
        exact ⟨rfl, hg, conc005c_trace_run ht⟩

/-- A decided check `q` of a trace of `g` gives a run of the executor of `g` passing `q`. -/
theorem conc005c_run_check {g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)} {C : Cfg N T}
    {s : XSt N T} {ls : List (XLbl N T)} {q : List (XStep N T) → Bool}
    (h : (conc005c_trace g C s ls).map q = some true) :
    ∃ tr, XRun (conc005c_graph g) C s tr ∧ q tr = true := by
  cases ht : conc005c_trace g C s ls with
  | none => simp [ht] at h
  | some tr =>
    simp only [ht, Option.map_some, Option.some.injEq] at h
    exact ⟨tr, conc005c_trace_run ht, h⟩

/-- The label is a step that passes over the head of the pass's order. -/
def conc005c_isLose : XLbl N T → Bool
  | .lose _ => true
  | _ => false

theorem conc005c_isLose_eq {l : XLbl N T} (h : conc005c_isLose l = true) : ∃ n, l = .lose n := by
  cases l <;> simp_all [conc005c_isLose]

end Runs

/-! ### The example: a reaped transition and two injections -/

/-- `u` takes one token from place `0`. -/
def conc005c_u : Trans Nat :=
  { core := { name := "u", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- `u` alone, `Window(3, 5)`, tolerance `0`; places `0` and `1` are environment places. -/
def conc005c_C : Cfg Nat Nat :=
  { X := { net := { places := [0, 1], transitions := [conc005c_u] },
           timing := fun _ => .window 3 5, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [0, 1], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => false,
    res := 0 }

/-- One token `7` in place `0`. -/
def conc005c_m0 : QMarking Nat Nat := fun p => if p = 0 then [7] else []

/-- The initial state of the example. -/
def conc005c_s0 : XSt Nat Nat := xinit conc005c_m0 0

theorem conc005c_u_found : findT conc005c_C conc005c_u.core.name = some conc005c_u := rfl

/-- Steps 1, 1b and 2 of a cycle with nothing queued. -/
def conc005c_top : List (XLbl Nat Nat) := [.endCompletions, .endPublications, .endEvents]

/-- Up to the reap: the first update arms `u` at `0`, which is not yet ready; the clock jumps to
`6`; the next deadline step reaps `u` (elapsed `6` is past `5`). -/
def conc005c_toReap : List (XLbl Nat Nat) :=
  conc005c_top ++ [.update, .deadline [], .begin, .endPass, .delay 6, .wake] ++ conc005c_top ++
    [.update, .deadline ["u"]]

/-- Up to the next update, with `u` reaped and enabled. -/
def conc005c_toUpdate : List (XLbl Nat Nat) :=
  conc005c_toReap ++ [.begin, .endPass, .wake] ++ conc005c_top

/-- Up to the injection of ticket `0`: the update keeps `u` reaped, the pass starts nothing, a
caller asks to inject `9` into place `1`. -/
def conc005c_toInject0 : List (XLbl Nat Nat) :=
  conc005c_toUpdate ++ [.update, .deadline [], .begin, .endPass, .request 1 9 .accepted]

/-- Up to the injection of ticket `1`: the wait injects `9` into place `1` (none of `u`'s arc
places), the next cycle keeps `u` reaped, a caller asks to inject `5` into place `0`. -/
def conc005c_toInject1 : List (XLbl Nat Nat) :=
  conc005c_toInject0 ++ [.inject 0] ++ conc005c_top ++
    [.update, .deadline [], .begin, .endPass, .request 0 5 .accepted]

/-- The whole run: the wait injects `5` into place `0`, `u`'s input place, which ends the
reaping, and the next update arms `u` again. -/
def conc005c_full : List (XLbl Nat Nat) :=
  conc005c_toInject1 ++ [.inject 1] ++ conc005c_top ++ [.update]

/-- The reference step function. -/
def conc005c_ref : Cfg Nat Nat → XSt Nat Nat → XLbl Nat Nat → Option (XSt Nat Nat) :=
  fun C s l => xstep C s l

/-! ### The firing half: a start that drains, a commit that deposits -/

/-- `u` again, now also inhibited by place `2`. -/
def conc005c_ui : Trans Nat :=
  { core := { name := "u", inputs := [⟨0, .one⟩], inhibitors := [2], reads := [], resets := [] },
    out := none }

/-- `t` takes one token from place `1` and drains place `2`. -/
def conc005c_t : Trans Nat :=
  { core := { name := "t", inputs := [⟨1, .one⟩], inhibitors := [], reads := [], resets := [2] },
    out := none }

/-- `w` takes one token from place `1`. -/
def conc005c_w : Trans Nat :=
  { core := { name := "w", inputs := [⟨1, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- The net of `a` and `b`: the transition named `"u"` is `Window(3, 5)`, every other one
`Window(6, 100)`; tolerance `0`, no environment place. -/
def conc005c_C2 (a b : Trans Nat) : Cfg Nat Nat :=
  { X := { net := { places := [0, 1, 2], transitions := [a, b] },
           timing := fun t => if t.core.name = "u" then .window 3 5 else .window 6 100, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => false,
    res := 0 }

/-- One token in place `0`, one in place `1`, place `2` empty. -/
def conc005c_m2 : QMarking Nat Nat := fun p => if p = 0 then [7] else if p = 1 then [8] else []

/-- Both transitions armed at `0`; at `6` the deadline step reaps `u` and the pass begins, with
the other transition (ready at `6`) at the head of its order. -/
def conc005c_toPass : List (XLbl Nat Nat) :=
  conc005c_top ++ [.update, .deadline [], .begin, .endPass, .delay 6, .wake] ++ conc005c_top ++
    [.update, .deadline ["u"], .begin]

/-- After `conc005c_toPass` in the net of `u` and `w`: `w` starts asynchronously (firing `0`),
which writes place `1` only, so `u` stays reaped; the pass started a firing, so the next cycle
begins at once; `w`'s action writes `9` into place `0`, `u`'s input place, and returns, so the
next step, in step 1 of that cycle, commits firing `0`. -/
def conc005c_toCommit : List (XLbl Nat Nat) :=
  conc005c_toPass ++ [.start "w" false, .endPass, .write 0 0 9, .ret 0 true]

/-- ✓ Every line of the companion is exercised by the reference. In the example, an update finds
`u` reaped and leaves it reaped (line 2); an injection into place `1`, none of `u`'s arc places,
leaves `u` reaped and enabled (line 4); an injection into place `0`, `u`'s input place, ends the
reaping (lines 1 and 3, on a run from the initial state, whose order is empty), and the next
update arms `u` again. The two halves of a firing end a reaping too (line 1): the start of `t`
drains place `2`, an empty inhibitor place of the reaped `u`, and the commit of `w`'s firing
deposits into place `0`, the input place of the reaped `u`. -/
@[evidence nonvacuous CONC_005_cycle]
theorem CONC_005_cycle_nonvacuous :
    (∃ s s', RefExec conc005c_C s .update s' ∧ ReapedE s conc005c_u ∧ ReapedE s' conc005c_u) ∧
    (∃ s s', RefExec conc005c_C s (.inject 0) s' ∧ conc005StepWrites s (.inject 0) 1 ∧
      (∀ p, ArcPlace conc005c_u p → ¬ conc005StepWrites s (.inject 0) p) ∧
      Enabled conc005c_u (qCount s.M) ∧ Enabled conc005c_u (qCount s'.M) ∧
      ReapedE s conc005c_u ∧ ReapedE s' conc005c_u) ∧
    (∃ s s', RefExec conc005c_C s (.inject 1) s' ∧ ReapedE s conc005c_u ∧
      ArcPlace conc005c_u 0 ∧ conc005StepWrites s (.inject 1) 0 ∧ ¬ ReapedE s' conc005c_u) ∧
    (∃ tr, XRun RefExec conc005c_C conc005c_s0 tr ∧ conc005c_s0.order = [] ∧
      (∃ x ∈ tr, ReapedE x.1 conc005c_u ∧ ¬ ReapedE x.2.2 conc005c_u) ∧
      (∃ x ∈ tr, (stampOf (x.2.2.st "u")).isSome = true ∧ x.1.st "u" = .off)) ∧
    (∃ s s', RefExec (conc005c_C2 conc005c_ui conc005c_t) s (.start "t" true) s' ∧
      ReapedE s conc005c_ui ∧ s.M 2 = [] ∧ ArcPlace conc005c_ui 2 ∧
      conc005StepWrites s (.start "t" true) 2 ∧ ¬ ReapedE s' conc005c_ui) ∧
    (∃ s s', RefExec (conc005c_C2 conc005c_u conc005c_w) s (.commit 0) s' ∧
      ReapedE s conc005c_u ∧ ArcPlace conc005c_u 0 ∧ conc005StepWrites s (.commit 0) 0 ∧
      ¬ ReapedE s' conc005c_u) := by
  have hArc0 : ArcPlace conc005c_u 0 := by simp [ArcPlace, inPlaces, conc005c_u]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check conc005c_ref (C := conc005c_C)
      (o := conc005c_run conc005c_ref conc005c_C conc005c_s0 conc005c_toUpdate) (l := .update)
      (p := fun s s' => s.st "u" == .reaped && s'.st "u" == .reaped) (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', hs, hp.1, hp.2⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check conc005c_ref (C := conc005c_C)
      (o := conc005c_run conc005c_ref conc005c_C conc005c_s0 conc005c_toInject0) (l := .inject 0)
      (p := fun s s' => s.eq == [(0, 1, 9)] && enabledNA (qCount s.M) conc005c_u.core &&
        enabledNA (qCount s'.M) conc005c_u.core && s.st "u" == .reaped &&
        s'.st "u" == .reaped) (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨⟨⟨⟨heq, he⟩, he'⟩, hr⟩, hr'⟩ := hp
    have hw1 : conc005StepWrites s (.inject 0) 1 := ⟨0, 9, [], heq⟩
    refine ⟨s, s', hs, hw1, ?_, he, he', hr, hr'⟩
    intro p hp hw
    obtain ⟨k, x, rest, hx⟩ := hw
    rw [heq] at hx
    simp only [List.cons.injEq, Prod.mk.injEq] at hx
    obtain ⟨⟨-, rfl, -⟩, -⟩ := hx
    simp [ArcPlace, inPlaces, ReadArc, InhibitorArc, ResetArc, conc005c_u] at hp
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check conc005c_ref (C := conc005c_C)
      (o := conc005c_run conc005c_ref conc005c_C conc005c_s0 conc005c_toInject1) (l := .inject 1)
      (p := fun s s' => s.eq == [(1, 0, 5)] && s.st "u" == .reaped && !(s'.st "u" == .reaped))
      (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne] at hp
    obtain ⟨⟨heq, hr⟩, hr'⟩ := hp
    exact ⟨s, s', hs, hr, hArc0, ⟨1, 5, [], heq⟩, hr'⟩
  · obtain ⟨tr, hrun, hq⟩ := conc005c_run_check (g := conc005c_ref) (C := conc005c_C)
      (s := conc005c_s0) (ls := conc005c_full)
      (q := fun tr => tr.any (fun x => x.1.st "u" == .reaped && !(x.2.2.st "u" == .reaped)) &&
        tr.any (fun x => (stampOf (x.2.2.st "u")).isSome && x.1.st "u" == .off))
      (by decide +kernel)
    simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq, Bool.not_eq_true',
      beq_eq_false_iff_ne] at hq
    obtain ⟨⟨x, hx, hx1, hx2⟩, ⟨y, hy, hy1, hy2⟩⟩ := hq
    exact ⟨tr, hrun, rfl, ⟨x, hx, hx1, hx2⟩, ⟨y, hy, hy1, hy2⟩⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check conc005c_ref
      (C := conc005c_C2 conc005c_ui conc005c_t)
      (o := conc005c_run conc005c_ref (conc005c_C2 conc005c_ui conc005c_t) (xinit conc005c_m2 0)
        conc005c_toPass) (l := .start "t" true)
      (p := fun s s' => s.st "u" == .reaped && (s.M 2).isEmpty &&
        decide (2 ∈ cycWrites s (.start "t" true)) && !(s'.st "u" == .reaped))
      (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne,
      List.isEmpty_iff, decide_eq_true_eq] at hp
    obtain ⟨⟨⟨hr, hM⟩, hw⟩, hr'⟩ := hp
    exact ⟨s, s', hs, hr, hM, by simp [ArcPlace, InhibitorArc, conc005c_ui],
      (conc005c_writes_iff _ _ _).2 hw, hr'⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check conc005c_ref
      (C := conc005c_C2 conc005c_u conc005c_w)
      (o := conc005c_run conc005c_ref (conc005c_C2 conc005c_u conc005c_w) (xinit conc005c_m2 0)
        conc005c_toCommit) (l := .commit 0)
      (p := fun s s' => s.st "u" == .reaped && decide (0 ∈ cycWrites s (.commit 0)) &&
        !(s'.st "u" == .reaped))
      (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne,
      decide_eq_true_eq] at hp
    obtain ⟨⟨hr, hw⟩, hr'⟩ := hp
    exact ⟨s, s', hs, hr, hArc0, (conc005c_writes_iff _ _ _).2 hw, hr'⟩

/-! ## Wrong executors -/

section Mutants

variable {N T : Type} [DecidableEq N]

/-- An executor whose injection does not end a reaping: the token lands, the clock statuses stay
as they were (injection not treated as a write); otherwise the reference. -/
def conc005c_injectNoWrite (C : Cfg N T) (s : XSt N T) : XLbl N T → Option (XSt N T)
  | .inject k => (injectStep C s k).map fun s' => { s' with st := s.st }
  | l => xstep C s l

/-- The judgement points of an update that re-evaluates every transition, reaped ones included
(design repair R9: `updReaped := false`). -/
def conc005c_reEvaluateAll : XPol N T := { refXPol with updReaped := false }

/-- An executor whose firing pass also visits the reaped transitions: its order is the ready
order followed by every transition of the net whose name is reaped, so the pass passes over them
and takes their clock status (a lose turns the name off); otherwise the reference. -/
def conc005c_visitReaped (C : Cfg N T) (s : XSt N T) : XLbl N T → Option (XSt N T)
  | .begin => (xstep C s .begin).map fun s' =>
      { s' with order := s'.order ++ C.X.net.transitions.filter (s.st ·.core.name == .reaped) }
  | l => xstep C s l

/-- An executor whose start also takes every token of the started transition's read places (a
read arc treated as an input arc); otherwise the reference. -/
def conc005c_readConsumes (C : Cfg N T) (s : XSt N T) : XLbl N T → Option (XSt N T)
  | .start n sy => (xstep C s (.start n sy)).map fun s' =>
      { s' with M := fun p =>
          if p ∈ (s.order.head?.map (·.core.reads)).getD [] then [] else s'.M p }
  | l => xstep C s l

/-- An executor whose commit does not end a reaping: the emission lands, the clock statuses stay
as they were (a firing's deposit not treated as a write); otherwise the reference. -/
def conc005c_commitNoWrite (C : Cfg N T) (s : XSt N T) : XLbl N T → Option (XSt N T)
  | .commit i => (xstep C s (.commit i)).map fun s' => { s' with st := s.st }
  | l => xstep C s l

/-- An executor whose start counts a reset place as written only when its drain moved a token:
the write rule (`unreap`) is applied to the input places and to the reset places that are not
empty on the pass-visible marking; otherwise the reference. The glossary's Write counts the drain
of an empty reset place as a write. -/
def conc005c_emptyDrainNoWrite (C : Cfg N T) (s : XSt N T) : XLbl N T → Option (XSt N T)
  | .start n sy =>
    match s.order with
    | t :: _ => (xstep C s (.start n sy)).map fun s' =>
        { s' with st := unreap C (inPlaces t ++ t.core.resets.filter (fun p => !(vis s p).isEmpty))
                          (afterStart refXPol C s t) }
    | [] => none
  | l => xstep C s l

end Mutants

/-- ✗ An injection that does not end a reaping violates the companion (line 1): in the example,
`5` lands in place `0`, `u`'s input place, while `u` is reaped, and `u` stays reaped, so no later
update re-runs its enablement check. -/
@[evidence forbids CONC_005_cycle]
theorem CONC_005_cycle_forbids_injectNoWrite :
    ¬ CONC_005_cycle (conc005c_graph (conc005c_injectNoWrite (N := Nat) (T := Nat))) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check conc005c_injectNoWrite (C := conc005c_C)
    (o := conc005c_run conc005c_injectNoWrite conc005c_C conc005c_s0 conc005c_toInject1)
    (l := .inject 1)
    (p := fun s s' => s.eq == [(1, 0, 5)] && s.st "u" == .reaped && s'.st "u" == .reaped)
    (by decide +kernel)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨heq, hr⟩, hr'⟩ := hp
  exact (h conc005c_C conc005c_u).1 conc005c_u_found (.inject 1) s s' hs hr
    ⟨0, by simp [ArcPlace, inPlaces, conc005c_u], 1, 5, [], heq⟩ hr'

/-- ✗ A commit that does not end a reaping violates the companion (line 1): `w`'s action writes
`9` into place `0`, `u`'s input place, while `u` is reaped, and the commit of that firing leaves
`u` reaped. -/
@[evidence forbids CONC_005_cycle]
theorem CONC_005_cycle_forbids_commitNoWrite :
    ¬ CONC_005_cycle (conc005c_graph (conc005c_commitNoWrite (N := Nat) (T := Nat))) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check conc005c_commitNoWrite
    (C := conc005c_C2 conc005c_u conc005c_w)
    (o := conc005c_run conc005c_commitNoWrite (conc005c_C2 conc005c_u conc005c_w)
      (xinit conc005c_m2 0) conc005c_toCommit) (l := .commit 0)
    (p := fun s s' => s.st "u" == .reaped && decide (0 ∈ cycWrites s (.commit 0)) &&
      s'.st "u" == .reaped)
    (by decide +kernel)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
  obtain ⟨⟨hr, hw⟩, hr'⟩ := hp
  exact (h (conc005c_C2 conc005c_u conc005c_w) conc005c_u).1 rfl (.commit 0) s s' hs hr
    ⟨0, by simp [ArcPlace, inPlaces, conc005c_u], (conc005c_writes_iff _ _ _).2 hw⟩ hr'

/-- ✗ A start that does not count the drain of an empty reset place as a write violates the
companion (line 1): `t`'s start drains place `2`, which is empty and an inhibitor place of the
reaped `u`, and `u` stays reaped. -/
@[evidence forbids CONC_005_cycle]
theorem CONC_005_cycle_forbids_emptyDrainNoWrite :
    ¬ CONC_005_cycle (conc005c_graph (conc005c_emptyDrainNoWrite (N := Nat) (T := Nat))) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check conc005c_emptyDrainNoWrite
    (C := conc005c_C2 conc005c_ui conc005c_t)
    (o := conc005c_run conc005c_emptyDrainNoWrite (conc005c_C2 conc005c_ui conc005c_t)
      (xinit conc005c_m2 0) conc005c_toPass) (l := .start "t" true)
    (p := fun s s' => s.st "u" == .reaped && decide (2 ∈ cycWrites s (.start "t" true)) &&
      s'.st "u" == .reaped)
    (by decide +kernel)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
  obtain ⟨⟨hr, hw⟩, hr'⟩ := hp
  exact (h (conc005c_C2 conc005c_ui conc005c_t) conc005c_ui).1 rfl (.start "t" true) s s' hs hr
    ⟨2, by simp [ArcPlace, InhibitorArc, conc005c_ui], (conc005c_writes_iff _ _ _).2 hw⟩ hr'

/-- ✗ An update that re-evaluates reaped transitions violates the companion (line 2): in the
example, the update after the reap finds `u` reaped and enabled and arms it again, so the next
deadline step can reap it again (a storm of TransitionTimedOut events). -/
@[evidence forbids CONC_005_cycle]
theorem CONC_005_cycle_forbids_reEvaluateAll :
    ¬ CONC_005_cycle (conc005c_graph (xstepW (conc005c_reEvaluateAll (N := Nat) (T := Nat)))) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check (xstepW conc005c_reEvaluateAll) (C := conc005c_C)
    (o := conc005c_run (xstepW conc005c_reEvaluateAll) conc005c_C conc005c_s0 conc005c_toUpdate)
    (l := .update) (p := fun s s' => s.st "u" == .reaped && !(s'.st "u" == .reaped))
    (by decide +kernel)
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne] at hp
  exact hp.2 ((h conc005c_C conc005c_u).2.1 conc005c_u_found s s' hs hp.1)

/-- ✗ A firing pass that also visits the reaped transitions violates the companion (line 3): on
the run from the initial state, the pass after the reap has `u` in its order and passes over it,
which turns `u` off without a write, so the next update arms it again. Its update keeps reaped
transitions reaped: only line 3 excludes it. -/
@[evidence forbids CONC_005_cycle]
theorem CONC_005_cycle_forbids_visitReaped :
    ¬ CONC_005_cycle (conc005c_graph (conc005c_visitReaped (N := Nat) (T := Nat))) := by
  intro h
  obtain ⟨tr, hrun, hq⟩ := conc005c_run_check (g := conc005c_visitReaped) (C := conc005c_C)
    (s := conc005c_s0) (ls := conc005c_toReap ++ [.begin, .lose "u"])
    (q := fun tr => tr.any fun x =>
      conc005c_isLose x.2.1 && x.1.st "u" == .reaped && !(x.2.2.st "u" == .reaped))
    (by decide +kernel)
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    beq_eq_false_iff_ne] at hq
  obtain ⟨x, hx, ⟨hl, hr⟩, hr'⟩ := hq
  obtain ⟨p, -, hw⟩ := (h conc005c_C conc005c_u).2.2.1 conc005c_u_found conc005c_s0 tr rfl hrun
    x hx hr hr'
  obtain ⟨n, hn⟩ := conc005c_isLose_eq hl
  rw [hn] at hw
  exact hw

/-- `rd` reads place `0` and has no other arc. -/
def conc005c_rd : Trans Nat :=
  { core := { name := "rd", inputs := [], inhibitors := [], reads := [0], resets := [] },
    out := none }

/-- `rd` and `u`, both `Immediate` and of equal priority (so `rd`, declared first, is first in
the ready order), sharing place `0`. -/
def conc005c_CR : Cfg Nat Nat :=
  { X := { net := { places := [0], transitions := [conc005c_rd, conc005c_u] },
           timing := fun _ => .immediate, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [],
    reentrant := false, validate := fun _ _ => true, relay := fun _ _ _ => true,
    timeoutOut := fun _ _ _ => false, res := 0 }

/-- ✗ A start that consumes through a read arc violates the companion (line 4): `rd` writes no
place, yet its start under the mutant empties place `0`, `u`'s input place, and `u`, enabled
before the start, is not enabled after it. -/
@[evidence forbids CONC_005_cycle]
theorem CONC_005_cycle_forbids_readConsumes :
    ¬ CONC_005_cycle (conc005c_graph (conc005c_readConsumes (N := Nat) (T := Nat))) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check conc005c_readConsumes (C := conc005c_CR)
    (o := conc005c_run conc005c_readConsumes conc005c_CR (xinit conc005c_m0 0)
      (conc005c_top ++ [.update, .deadline [], .begin]))
    (l := .start "rd" false)
    (p := fun s s' => enabledNA (qCount s.M) conc005c_u.core &&
      !enabledNA (qCount s'.M) conc005c_u.core &&
      (s.order.head?.map fun t => t.core.inputs.isEmpty && t.core.resets.isEmpty) == some true)
    (by decide +kernel)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  obtain ⟨⟨he, hne⟩, hhead⟩ := hp
  have hw : ∀ p, ArcPlace conc005c_u p → ¬ conc005StepWrites s (.start "rd" false) p := by
    intro p _ hw
    obtain ⟨t, rest, ho, hpw⟩ := hw
    rw [ho] at hhead
    simp at hhead
    rcases hpw with hpw | hpw
    · simp [inPlaces, hhead.1] at hpw
    · simp [ResetArc, hhead.2] at hpw
  have := ((h conc005c_CR conc005c_u).2.2.2 (.start "rd" false) rfl s s' hs hw).2 he
  unfold Enabled at this
  rw [hne] at this
  cases this

/-! ### Mutant reading: no run line -/

/-- Mutant reading of the companion without line 3: a write ends a reaping, an update keeps a
reaping, and an unwritten step keeps enablement, but nothing says that only a write ends a
reaping. -/
def CONC_005_cycle_mutant_noRunLine {N T : Type} [DecidableEq N] (R : XRel N T) : Prop :=
  ∀ (C : Cfg N T) (u : Trans N),
    (findT C u.core.name = some u → ∀ l, on (fun s s' => R C s l s'), shall (fun s s' =>
        ReapedE s u → (∃ p, ArcPlace u p ∧ conc005StepWrites s l p) → ¬ ReapedE s' u)) ∧
    (findT C u.core.name = some u → on (fun s s' => R C s .update s'), shall (fun s s' =>
        ReapedE s u → ReapedE s' u)) ∧
    (∀ l, startOrDeposit l = true → on (fun s s' => R C s l s'), shall (fun s s' =>
        (∀ p, ArcPlace u p → ¬ conc005StepWrites s l p) →
          (Enabled u (qCount s'.M) ↔ Enabled u (qCount s.M))))

/-- Off the begin of a pass, the mutant is the reference. -/
theorem conc005c_visitReaped_eq {N T : Type} [DecidableEq N] {C : Cfg N T} {s : XSt N T}
    {l : XLbl N T} (hb : l ≠ .begin) : conc005c_visitReaped C s l = xstep C s l := by
  cases l <;> first | rfl | exact absurd rfl hb

/-- The firing pass that also visits the reaped transitions kills the mutant reading: it differs
from the reference only at the begin of a pass, which writes no place, keeps every clock status
and keeps the marking, so it meets lines 1, 2 and 4; line 3 excludes it
(`CONC_005_cycle_forbids_visitReaped`). -/
@[evidence mutant CONC_005_cycle]
theorem CONC_005_cycle_mutant_noRunLine_killed :
    CONC_005_cycle_mutant_noRunLine (conc005c_graph (conc005c_visitReaped (N := Nat) (T := Nat))) ∧
      ¬ CONC_005_cycle (conc005c_graph (conc005c_visitReaped (N := Nat) (T := Nat))) := by
  refine ⟨fun C u => ⟨fun hu l s s' h hr hw => ?_, fun hu s s' h hr => ?_,
    fun l _ s s' h hw => ?_⟩, CONC_005_cycle_forbids_visitReaped⟩
  · by_cases hb : l = .begin
    · subst hb
      obtain ⟨p, -, hw⟩ := hw
      exact hw.elim
    · have h' : xstep C s l = some s' := by rw [← conc005c_visitReaped_eq hb]; exact h
      exact conc005c_line1 hu h' hr hw
  · have h' : xstep C s .update = some s' := by
      rw [← conc005c_visitReaped_eq (fun e => by cases e)]; exact h
    exact conc005c_line2 hu h' hr
  · by_cases hb : l = .begin
    · subst hb
      obtain ⟨s1, h1, rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨-, -, -, -, rfl⟩ := xstepW_begin h1
      exact Iff.rfl
    · have h' : xstep C s l = some s' := by rw [← conc005c_visitReaped_eq hb]; exact h
      exact conc005c_line4 h' hw


end Libpetri.Spec
