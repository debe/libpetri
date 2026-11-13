import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Exec

set_option linter.missingDocs true

/-!
# EXEC-003: Competitive conflict resolution (`spec/04-execution-model.md`)

A block over the executor model (`RefExec`, `Reference/Exec.lean`). A firing pass walks its
ready order head first: a `start n` starts the head, a `lose n` drops it and takes its clock; the
order changes in no other step of the pass, and the pass ends only once the order is empty. Start
and lose judge the head on the **pass-visible marking** `vis s` (glossary `GlossaryExec.lean`):
every queue without the tail of tokens deposited inside the current pass (`hid s`, of length
`XSt.delta`). A synchronous action settled inside the pass deposits into that tail, so the rest of
the pass does not count, consume, drain or deliver what it deposited; the tail stays in the marking
to the end of the pass, and the next pass begins with the same marking, all of it visible. Ruling
D75 (a): the inhibitor arcs read the pass-visible marking too.

The requirement is a predicate over an abstract executor `R : XRel N T`, checked against the
reference, against a mutant that re-checks on the live marking (the one-field change
`recheckOn := (·.M)` of `refXPol`), and against executors that start out of order, drain the live
marking, hand the action the live queue, test inhibitor arcs on the live marking, keep a loser's
clock, let a same-pass deposit become visible, cut the hidden tail at the end of the pass, prune
the order when a synchronous action settles, end the pass before the order is empty, cut the
marking at the next begin, or keep the hidden tail into the next pass.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## EXEC-003: Competitive Conflict Resolution -/

requirement EXEC_003
  id "EXEC-003"
  title "Competitive Conflict Resolution"
  kind B
  scope "all executors"
  source verbatim "spec/04-execution-model.md"
  quote "When multiple transitions compete for the same input tokens, the highest-priority ready transition fires first and consumes the tokens."
        "Lower-priority transitions become disabled if their inputs are no longer satisfied."
        "A firing pass takes the transitions of its ready order ([EXEC-002]) one at a time from the front: it starts the next transition, or it drops it and goes on with the rest."
        "The pass-visible marking is the marking a firing pass began with, minus the tokens earlier firings of the same pass consumed or drained; tokens a synchronous action deposited during the pass are not part of it."
        "*When* a firing pass starts or drops a transition, the transition *shall* be the next one of the pass's ready order, and it *shall* leave that order."
        "*When* a firing pass starts a transition, the transition *shall* hold a clock and be enabled on the pass-visible marking, with input counts, read arcs and inhibitor arcs all judged on that marking."
        "*If* the next transition of a firing pass's ready order holds a clock and is enabled on the pass-visible marking, *then* the executor *shall not* drop it."
        "*When* a firing pass drops a transition, the transition *shall* lose its clock ([TIME-012]), and the marking *shall* stay unchanged."
        "*While* a firing pass is under way, its ready order *shall* change only when the pass starts or drops a transition."
        "*When* a firing pass ends, its ready order *shall* be empty, so a transition of the order that does not hold a clock or is not enabled on the pass-visible marking when it is next is dropped, loses its clock and does not start in that pass."
        "*When* a transition starts in a firing pass, it *shall* consume, drain and hand its action only tokens of the pass-visible marking, so a token a synchronous action deposited earlier in the same pass survives its `all()`, `atLeast(n)` and reset arcs and does not reach its action."
        "*While* a firing pass is under way, the executor *shall* change the pass-visible marking only by starting a transition, and *shall* keep every token deposited earlier in the pass, so a token a synchronous action deposits in the pass does not become part of the pass-visible marking."
        "*When* a firing pass begins, the executor *shall* keep the marking, and every token of the marking *shall* be part of the pass-visible marking of the new pass."
  reading "For every executor R and every configuration C:"
          "a start step of the name n starts the head t of the pass's order, named n, holding a clock and enabled on the pass-visible marking (input counts, read arcs and inhibitor arcs), and removes it from the order;"
          "a start step of t leaves in every place p the pass-visible queue of p with t's consumption and drains applied, followed by the tail of p deposited inside the pass, keeps that tail hidden, and every firing it adds is handed what t takes from the pass-visible marking;"
          "a lose step of the name n drops the head t of the pass's order, named n, only when t holds no clock or is not enabled on the pass-visible marking, and removes it from the order;"
          "a lose step of the name n leaves n without a clock and the marking unchanged;"
          "every step from inside a firing pass other than a start leaves the pass-visible marking unchanged and only extends the hidden tail of every place;"
          "every step from inside a firing pass other than a start or a lose leaves the pass's order unchanged;"
          "an end of pass step happens only when the pass's order is empty;"
          "a begin step leaves the marking unchanged and makes all of it pass-visible."
  assumes "The model is an executor R : XRel N T (glossary GlossaryExec.lean): R C s l s' says that under configuration C the step labelled l leads from executor state s to s'. The witness is the reference executor RefExec (Reference/Exec.lean). The pass-visible marking is the derived term vis s: each queue of s.M without its last s.delta p tokens, the tokens deposited inside the current pass (hid s). It is the model's form of the definition sentence, read inductively: lines 2 and 5 say how vis changes inside a pass, and line 8 where it starts. The sentence before it ('takes the transitions of its ready order one at a time from the front') is lines 1, 3, 6 and 7 together. 'Drops' is the lose step, 'the next one of the ready order' the head of s.order, and 'holds a clock' is stampOf (s.st n) being some stamp, whatever the restart flag (the glossary's 'armed' adds 'enabled', which the sentences state separately, on the pass-visible marking)."
          "The headline sentence ('the highest-priority ready transition fires first and consumes the tokens') is lines 1, 3, 6 and 7 together with the order the pass begins with: the pass takes its transitions head first, each start or lose takes the head and removes it, nothing else changes the order, and the pass does not end before the order is empty, so the first transition of the order that is still enabled on the pass-visible marking consumes the tokens. Which order the begin step sets (the ready order of EXEC-002 at the cycle reading) is TIME-014's first line and EXEC-002's companion line, not restated here, so this block takes no side in ruling D14 (the all-immediate fast path). The second quoted sentence ('become disabled') is lines 3 and 4: the loser leaves the order and its clock is gone (ruled: it loses its clock, TIME-012's sentence on the recheck); a later enablement update arms it again if it is enabled (TIME-010, CONC-005 companion)."
          "EARS mapping. 'Starts or drops ... the next one ... leave that order' is lines 1 and 3 (head, name, removal). 'Hold a clock and be enabled on the pass-visible marking' is line 1. 'Shall not drop it' is line 3. 'Lose its clock ... marking stay unchanged' is line 4. 'Its ready order shall change only when the pass starts or drops' is line 6. 'When a firing pass ends, its ready order shall be empty' is line 7; its 'so' clause follows from lines 1, 3, 4, 6 and 7: every entry leaves the order by a start or a lose before the pass ends, line 1 forbids starting one without a clock or not enabled on the pass-visible marking, so it leaves by a lose and line 4 takes its clock, and line 6 keeps it from coming back into the order of that pass (names are pairwise distinct, ruling D10). 'Consume, drain and hand its action only tokens of the pass-visible marking' is line 2. 'Change the pass-visible marking only by starting a transition, and keep every token deposited earlier in the pass' is line 5 for every step but a start, and line 2's last two conjuncts (the tail follows the consumed queue, delta unchanged) for a start. 'When a firing pass begins ... keep the marking ... part of the pass-visible marking' is line 8."
          "Line 2 fixes the exact marking after a start: the FIFO prefix of every input queue is consumed ([EXEC-010]), reset places and all() or atLeast(n) inputs are drained to the end of the pass-visible queue ([EXEC-013], [IO-003], [IO-004]), read arcs peek at the pass-visible queue ([EXEC-012]), and a start deposits nothing ([CONC-002]). Those are the cited requirements' rules applied to the pass-visible queue (qConsume and qDelivered of Reference/Queue.lean); what this block adds is the queue they apply to, as AC5 says. That a start adds exactly one firing is EXEC-001's and CONC-002's; line 2 only says what any firing it adds is handed."
          "Line 1 kills an executor that re-checks on the live marking (EXEC_003_mutant_liveRecheck_killed, the XPol field recheckOn) and one that starts any ready transition of the order rather than its head (EXEC_003_forbids_anyOrder). Line 2 kills an executor that consumes and drains the live marking (EXEC_003_forbids_drainSwallows) and one that removes the right tokens but hands the action the live queue, deposit included (EXEC_003_forbids_liveDeliver). Line 3 kills an executor that tests inhibitor arcs on the live marking (EXEC_003_forbids_liveInhibitor, ruling D75 (b)); the inhibitor test is part of the enablement test lines 1 and 3 share, and this mutant breaks it by a wrongful lose. Line 4 kills an executor whose loser keeps its clock (EXEC_003_forbids_loserKeepsClock). Line 5 kills an executor whose in-pass deposit is visible to the rest of the pass (EXEC_003_forbids_visibleDeposit) and one whose end of pass cuts every queue back to its pass-visible prefix, losing the same-pass deposits (EXEC_003_forbids_tailCut). Line 6 kills an executor whose in-pass settle prunes from the order the entries no longer enabled, so they never lose their clock (EXEC_003_forbids_pruneOrder). Line 7 kills an executor that ends the pass with entries still in the order (EXEC_003_forbids_earlyEnd). Line 8 kills an executor whose begin cuts the marking to the pass-visible one of the previous pass (EXEC_003_forbids_beginCut) and one that keeps the hidden tail into the next pass (EXEC_003_forbids_staleDelta)."
          "The lines are safety lines over the steps an executor takes: none obliges a step to happen. That the loop reaches the pass and that a pass under way takes its next step is EXEC-001's; TIME-014 states the same progress over a whole pass (the starts and loses of a pass name its ready order, all of it once the pass ends), of which lines 6 and 7 are the step form. A pass that a terminal place stops (EXEC-042) has no end of pass step, and line 7 says nothing of it. Steps outside a pass (step 1 settles, injections, publications) do not drop tokens by EXEC-001's frame, not this block's, so the tail line 5 keeps to the end of the pass and line 8 makes visible is the same tail when no outside step intervenes, as in every example here."
          "Ruling D75 (a): inside a firing pass an inhibitor arc reads the pass-visible marking, as the input counts and the drains do (Rust recheck_can_fire on the pass snapshot, bitmap_backend.rs 708-713, inhibitors tested on that snapshot, compiled_net.rs 355-361; Java canEnable(tid, fireScanBitmap, true)). CORE-022 and CORE-031 say that a transition shall not fire while an inhibitor place is marked; their blocks are stated over the one-step firing of a marking, and AC4's added sentence says that inside a firing pass the marking a transition fires from in that sense is the pass-visible marking. The assumes line in CORE-022 and CORE-031 that says so, and the bridge from a reference start to those blocks, belong to the integrator; EXEC_003_start_inhibitors states the start half here."
          "AC1 (T1 priority 10, T2 priority 5, one token, T1 fires, T2 disabled) and the test derivation are EXEC_003_nonvacuous's first part: T1 heads the order and starts, T2 loses and has no clock. The decided runs take the all-immediate single-priority path, where the order is the declaration order, because the kernel does not evaluate the general path's merge sort on two or more ready transitions; with priorities 10 and 5 EXEC-002 forces the same order, and the block reads only the head. The priority half of AC1 is therefore EXEC-002's and TIME-014's, not exercised here."
          "AC2 (T1 not ready, T2 may fire) is EXEC_003_allows_notReady: with T1 Delayed(10) and armed but below its earliest bound, the order of the pass holds T2 only, and T2 starts and takes the token T1 is waiting for. That a transition that is not ready is not in the order is TIME-014's first line."
          "AC3 is lines 1, 3 and 5: T1 consumes P's token, its synchronous action refills P inside the pass (the in-pass commit step of EXEC-021), the refill stays outside the pass-visible marking (line 5, third part), and T2, judged on it, loses (EXEC_003_nonvacuous, second part). 'May fire no earlier than the next cycle' is line 3's removal from the order with line 6 (it does not come back in that pass), line 5 (the refill stays in the marking to the end of the pass, seventh part) and line 8 (the next pass begins with the refill pass-visible, sixth part, where T2 is in the order again). The wording fix of ruling D20 (the reason is the recheck, not 'outputs deposit in step 1') is in the markdown."
          "AC4 is line 1 for counts: enablement on the pass-visible marking compares every input arc's required count, exactly(n) and atLeast(n) included, with the pass-visible count. 'Visible at the next cycle' is line 8. The inhibitor sentence added under D75 (a) is line 1 for inhibitor arcs (EXEC_003_nonvacuous, fifth part: T4 starts while its inhibitor place holds a same-pass deposit). Its ν part (a correlated join whose correlated input place received a same-pass deposit fires no earlier than the next cycle) is not stated here: the start of RefExec takes no match specification. It is a follow-up line of this block, to be added when RefExec's start takes the ν firing of RefNu (W9, NU-020's correlated take), recorded with the integrator."
          "AC5 is line 2: a reset arc (and an all() or atLeast(n) input) applied to the pass-visible queue takes its prefix, and the same-pass tail follows it unchanged (EXEC_003_nonvacuous, fourth part: the reset of T3 takes the old token 3 and leaves the deposited 8); what reaches the action is taken from the pass-visible queue too (EXEC_003_forbids_liveDeliver). Rust drainable (precompiled_backend.rs 690-695), Java drainable() (PrecompiledNetExecutor.java 791)."
          "The closing paragraph ('as if every firing in it started before any of them deposited') is the observational form of lines 2 and 5: moving each in-pass settle behind the last start of its pass keeps every start's pass-visible marking equal to the live marking of the moved run. It is link L5 of Reference/ExecLink.lean (ExecLink.hoist_vis), proved there, and it is not a line here. Its second sentence (verification reads such a firing as two steps) is VER-004's."
          "TypeScript settles every firing in step 1 (bitmap-net-executor.ts processCompletedTransitions), so no deposit happens inside its passes: its runs are runs of RefExec without an in-pass commit step, and the lines hold of them with an empty hidden tail."
          "Which transitions keep their clocks across a start (the restart flag on the live intermediate marking, ruling D7) is TIME-012's companion line, and re-entrancy (ruling D8 (b)) is CONC-002's; neither is stated here. Transition names are pairwise distinct (ruling D10, Cfg.WF), so the name a start or lose step carries names one transition and leaves the order with it."
  signoff "2026-11-13 f60959664ca0b8db ai"
  statement : ∀ {N T : Type} [DecidableEq N], XRel N T → Prop :=
    fun R => ∀ C,
      (∀ n sy, on (fun s s' => R C s (.start n sy) s'), shall (fun s s' =>
        ∃ t rest, s.order = t :: rest ∧ t.core.name = n ∧ (stampOf (s.st n)).isSome = true ∧
          enabledNA (qCount (vis s)) t.core = true ∧ s'.order = rest)) ∧
      (∀ n sy, on (fun s s' => R C s (.start n sy) s'), shall (fun s s' =>
        ∃ t rest, s.order = t :: rest ∧ (∀ p, s'.M p = qConsume (vis s) t p ++ hid s p) ∧
          s'.delta = s.delta ∧ ∀ f ∈ s'.fl, f ∉ s.fl → f.deliv = qDelivered (vis s) t)) ∧
      (∀ n, on (fun s s' => R C s (.lose n) s'), shall (fun s s' =>
        ∃ t rest, s.order = t :: rest ∧ t.core.name = n ∧
          ¬ ((stampOf (s.st n)).isSome = true ∧ enabledNA (qCount (vis s)) t.core = true) ∧
          s'.order = rest)) ∧
      (∀ n, on (fun s s' => R C s (.lose n) s'), shall (fun s s' =>
        s'.st n = .off ∧ s'.M = s.M)) ∧
      (on (fun s s' => s.phase = .pass ∧ ∃ l, R C s l s' ∧ ∀ n sy, l ≠ .start n sy),
        shall (fun s s' => vis s' = vis s ∧ ∀ p, hid s p <+: hid s' p)) ∧
      (on (fun s s' => s.phase = .pass ∧ ∃ l, R C s l s' ∧ (∀ n sy, l ≠ .start n sy) ∧
          ∀ n, l ≠ .lose n),
        shall (fun s s' => s'.order = s.order)) ∧
      (on (fun s s' => R C s .endPass s'), shall (fun s _ => s.order = [])) ∧
      (on (fun s s' => R C s .begin s'), shall (fun s s' => s'.M = s.M ∧ vis s' = s'.M))

/- The pinned readable form of EXEC-003: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EXEC_003 : {N T : Type} → [DecidableEq N] → XRel N T → Prop :=
fun {N T} [DecidableEq N] R =>
  ∀ (C : Cfg N T),
    (∀ (n : String) (sy : Bool),
        on fun s s' => R C s (XLbl.start n sy) s', shall fun s s' =>
          ∃ t rest,
            s.order = t :: rest ∧
              t.core.name = n ∧
                (stampOf (s.st n)).isSome = true ∧ enabledNA (qCount (vis s)) t.core = true ∧ s'.order = rest) ∧
      (∀ (n : String) (sy : Bool),
          on fun s s' => R C s (XLbl.start n sy) s', shall fun s s' =>
            ∃ t rest,
              s.order = t :: rest ∧
                (∀ (p : N), s'.M p = qConsume (vis s) t p ++ hid s p) ∧
                  s'.delta = s.delta ∧ ∀ f ∈ s'.fl, f ∉ s.fl → f.deliv = qDelivered (vis s) t) ∧
        (∀ (n : String),
            on fun s s' => R C s (XLbl.lose n) s', shall fun s s' =>
              ∃ t rest,
                s.order = t :: rest ∧
                  t.core.name = n ∧
                    ¬((stampOf (s.st n)).isSome = true ∧ enabledNA (qCount (vis s)) t.core = true) ∧ s'.order = rest) ∧
          (∀ (n : String), on fun s s' => R C s (XLbl.lose n) s', shall fun s s' => s'.st n = Status.off ∧ s'.M = s.M) ∧
            (on fun s s' => s.phase = Phase.pass ∧ ∃ l, R C s l s' ∧ ∀ (n : String) (sy : Bool), l ≠ XLbl.start n sy,
                shall fun s s' => vis s' = vis s ∧ ∀ (p : N), hid s p <+: hid s' p) ∧
              (on fun s s' =>
                  s.phase = Phase.pass ∧
                    ∃ l,
                      R C s l s' ∧ (∀ (n : String) (sy : Bool), l ≠ XLbl.start n sy) ∧ ∀ (n : String), l ≠ XLbl.lose n,
                  shall fun s s' => s'.order = s.order) ∧
                (on fun s s' => R C s XLbl.endPass s', shall fun s x => s.order = []) ∧
                  on fun s s' => R C s XLbl.begin s', shall fun s s' => s'.M = s.M ∧ vis s' = s'.M
-/
#guard_msgs in #print EXEC_003

/-! ### The reference -/

section Reference

variable {N T : Type} [DecidableEq N]

/-- The lines of EXEC-003 with the marking a start or a lose judges on as a parameter `rc` (the
reference judges on `vis`). -/
def exec003Lines (rc : XSt N T → QMarking N T) (R : XRel N T) : Prop :=
  ∀ C,
    (∀ n sy, on (fun s s' => R C s (.start n sy) s'), shall (fun s s' =>
      ∃ t rest, s.order = t :: rest ∧ t.core.name = n ∧ (stampOf (s.st n)).isSome = true ∧
        enabledNA (qCount (rc s)) t.core = true ∧ s'.order = rest)) ∧
    (∀ n sy, on (fun s s' => R C s (.start n sy) s'), shall (fun s s' =>
      ∃ t rest, s.order = t :: rest ∧ (∀ p, s'.M p = qConsume (vis s) t p ++ hid s p) ∧
        s'.delta = s.delta ∧ ∀ f ∈ s'.fl, f ∉ s.fl → f.deliv = qDelivered (vis s) t)) ∧
    (∀ n, on (fun s s' => R C s (.lose n) s'), shall (fun s s' =>
      ∃ t rest, s.order = t :: rest ∧ t.core.name = n ∧
        ¬ ((stampOf (s.st n)).isSome = true ∧ enabledNA (qCount (rc s)) t.core = true) ∧
        s'.order = rest)) ∧
    (∀ n, on (fun s s' => R C s (.lose n) s'), shall (fun s s' =>
      s'.st n = .off ∧ s'.M = s.M)) ∧
    (on (fun s s' => s.phase = .pass ∧ ∃ l, R C s l s' ∧ ∀ n sy, l ≠ .start n sy),
      shall (fun s s' => vis s' = vis s ∧ ∀ p, hid s p <+: hid s' p)) ∧
    (on (fun s s' => s.phase = .pass ∧ ∃ l, R C s l s' ∧ (∀ n sy, l ≠ .start n sy) ∧
        ∀ n, l ≠ .lose n),
      shall (fun s s' => s'.order = s.order)) ∧
    (on (fun s s' => R C s .endPass s'), shall (fun s _ => s.order = [])) ∧
    (on (fun s s' => R C s .begin s'), shall (fun s s' => s'.M = s.M ∧ vis s' = s'.M))

/-- A deposit inside the pass joins the hidden tail: the pass-visible marking is unchanged. -/
theorem vis_depositAt {C : Cfg N T} {s : XSt N T} {i : Nat} {e : List (N × T)}
    (hph : s.phase = .pass) : vis (depositAt C s i e) = vis s := by
  funext p
  have hc : countIn e p = (qEmittedTo e p).length := by
    simp only [countIn, qEmittedTo, List.length_map]
    rfl
  simp only [vis, depositAt, settle, hph, if_true, qAppend_apply, List.length_append, hc,
    Nat.add_sub_add_right]
  exact List.take_append_of_le_length (Nat.sub_le _ _)

/-- A deposit inside the pass extends the hidden tail. -/
theorem hid_depositAt {C : Cfg N T} {s : XSt N T} {i : Nat} {e : List (N × T)}
    (hph : s.phase = .pass) (p : N) : hid s p <+: hid (depositAt C s i e) p := by
  have hc : countIn e p = (qEmittedTo e p).length := by
    simp only [countIn, qEmittedTo, List.length_map]
    rfl
  simp only [hid, depositAt, settle, hph, if_true, qAppend_apply, List.length_append, hc,
    Nat.add_sub_add_right]
  rw [List.drop_append_of_le_length (Nat.sub_le _ _)]
  exact List.prefix_append _ _

omit [DecidableEq N] in
/-- What lines 5 and 6 ask of a step from inside the pass, for a step that keeps the marking, the
hidden tail counts and the order. -/
theorem exec003_frame {s s' : XSt N T} {X : Prop} (hM : s'.M = s.M) (hd : s'.delta = s.delta)
    (ho : s'.order = s.order) :
    vis s' = vis s ∧ (∀ p, hid s p <+: hid s' p) ∧ (X → s'.order = s.order) := by
  refine ⟨?_, fun p => ?_, fun _ => ho⟩
  · funext p
    simp only [vis, hM, hd]
  · simp only [hid, hM, hd]
    exact List.prefix_refl _

/-- Every step of `xstepW P` from inside a pass, other than a start, leaves the pass-visible
marking unchanged and only extends the hidden tail, and, if it is not a lose either, keeps the
order: only a settle deposits inside the pass, and it deposits into the hidden tail
(`vis_depositAt`, `hid_depositAt`); `publish`, `inject` and `begin` are not offered in the pass;
only `begin`, `start` and `lose` set the order. -/
theorem xstepW_pass_frame (P : XPol N T) {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (hph : s.phase = .pass) (h : xstepW P C s l = some s') (hl : ∀ n sy, l ≠ .start n sy) :
    vis s' = vis s ∧ (∀ p, hid s p <+: hid s' p) ∧ ((∀ n, l ≠ .lose n) → s'.order = s.order) := by
  cases l with
  | delay δ => cases xstepW_delay h; exact exec003_frame rfl rfl rfl
  | write i p x => obtain ⟨-, -, -, rfl⟩ := writeStep_some h; exact exec003_frame rfl rfl rfl
  | flush i =>
    obtain ⟨-, -, -, -, -, ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ := flushStep_some h <;>
      exact exec003_frame rfl rfl rfl
  | ret i ok => obtain ⟨-, -, -, rfl⟩ := retStep_some h; exact exec003_frame rfl rfl rfl
  | expire i e =>
    obtain ⟨-, -, -, -, -, -, rfl⟩ := expireStep_some h; exact exec003_frame rfl rfl rfl
  | request p x r =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := requestStep_some h <;> exact exec003_frame rfl rfl rfl
  | drain => obtain ⟨-, rfl⟩ := drainStep_some h; exact exec003_frame rfl rfl rfl
  | close => obtain ⟨-, rfl⟩ := closeStep_some h; exact exec003_frame rfl rfl rfl
  | terminateNow => obtain ⟨-, rfl⟩ := terminateStep_some h; exact exec003_frame rfl rfl rfl
  | commit i =>
    obtain ⟨-, -, -, -, -, -, -, rfl⟩ := commitStep_some h
    exact ⟨vis_depositAt hph, hid_depositAt hph, fun _ => rfl⟩
  | fail i => obtain ⟨-, -, -, -, rfl⟩ := failStep_some h; exact exec003_frame rfl rfl rfl
  | tdeposit i =>
    obtain ⟨-, -, -, -, -, -, rfl⟩ := tdepositStep_some h
    exact ⟨vis_depositAt hph, hid_depositAt hph, fun _ => rfl⟩
  | endCompletions =>
    obtain ⟨-, -, -, -, rfl⟩ := xstepW_endCompletions h; exact exec003_frame rfl rfl rfl
  | publish i =>
    obtain ⟨-, -, -, -, hp, -⟩ := publishStep_some h
    rcases hp with hp | ⟨hp, -⟩ <;> simp [hph] at hp
  | endPublications =>
    obtain ⟨-, -, -, rfl⟩ := xstepW_endPublications h; exact exec003_frame rfl rfl rfl
  | inject k =>
    obtain ⟨-, -, -, -, -, -, hp, -⟩ := injectStep_some h
    rcases hp with hp | hp <;> simp [hph] at hp
  | discard k =>
    obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := discardStep_some h; exact exec003_frame rfl rfl rfl
  | endEvents => obtain ⟨-, -, -, rfl⟩ := xstepW_endEvents h; exact exec003_frame rfl rfl rfl
  | snapshot a => obtain ⟨-, -, -, rfl⟩ := snapshotStep_some h; exact exec003_frame rfl rfl rfl
  | update => obtain ⟨-, -, rfl⟩ := xstepW_update h; exact exec003_frame rfl rfl rfl
  | deadline ns => obtain ⟨-, -, -, rfl⟩ := xstepW_deadline h; exact exec003_frame rfl rfl rfl
  | finish c =>
    cases c with
    | quiescent =>
      obtain ⟨-, -, -, rfl⟩ := xstepW_finishQuiescent h; exact exec003_frame rfl rfl rfl
    | terminal => obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h; exact exec003_frame rfl rfl rfl
    | closed =>
      obtain ⟨-, -, -, -, rfl⟩ := xstepW_finishClosed h; exact exec003_frame rfl rfl rfl
    | stopped =>
      obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h; exact exec003_frame rfl rfl rfl
  | begin =>
    obtain ⟨hp, -⟩ := xstepW_begin h
    simp [hph] at hp
  | start n sy => exact absurd rfl (hl n sy)
  | lose n =>
    obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := loseStep_some h
    exact ⟨rfl, fun _ => List.prefix_refl _, fun hn => absurd rfl (hn n)⟩
  | endPass => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endPass h; exact exec003_frame rfl rfl rfl
  | park tmr =>
    obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := parkStep_some h; exact exec003_frame rfl rfl rfl
  | wake => obtain ⟨-, -, rfl⟩ := wakeStep_some h; exact exec003_frame rfl rfl rfl

/-- The executor of any judgement points `P` meets the lines of EXEC-003 over the marking
`P.recheckOn` judges on: `start` and `lose` take the head of the order and judge it on
`P.recheckOn` (`startStep_some`, `loseStep_some`), a start leaves `liveAfter`, which applies the
consumption to the visible prefix, and hands its new firing `qDelivered (vis s) t`, a lose turns
the name off, a step in the pass other than a start keeps the visible prefix, only extends the
hidden tail and, unless it is a lose, keeps the order (`xstepW_pass_frame`), `endPass` needs an
empty order (`xstepW_endPass`), and `begin` keeps the marking and empties the hidden tail
(`xstepW_begin`). -/
theorem exec003Lines_xstepW (P : XPol N T) :
    exec003Lines P.recheckOn (fun C s l s' => xstepW P C s l = some s') := by
  intro C
  refine ⟨fun n sy s s' h => ?_, fun n sy s s' h => ?_, fun n s s' h => ?_, fun n s s' h => ?_,
    fun s s' ⟨hph, l, h, hl⟩ => (xstepW_pass_frame P hph h hl).imp_right And.left,
    fun s s' ⟨hph, l, h, hl, hlo⟩ => (xstepW_pass_frame P hph h hl).2.2 hlo,
    fun s s' h => (xstepW_endPass h).2.2.1, fun s s' h => ?_⟩
  · obtain ⟨t, rest, ho, -, -, -, hn, hst, he, rfl⟩ := startStep_some h
    exact ⟨t, rest, ho, hn, hst, he, rfl⟩
  · obtain ⟨t, rest, ho, -, -, -, -, -, -, rfl⟩ := startStep_some h
    refine ⟨t, rest, ho, fun _ => rfl, rfl, fun f hf hn => ?_⟩
    rcases List.mem_append.mp hf with h1 | h1
    · exact absurd h1 hn
    · simp at h1
      rw [h1]
  · obtain ⟨t, rest, ho, -, -, -, hn, hne, rfl⟩ := loseStep_some h
    exact ⟨t, rest, ho, hn, hne, rfl⟩
  · obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := loseStep_some h
    exact ⟨by simp, rfl⟩
  · obtain ⟨-, -, -, -, rfl⟩ := xstepW_begin h
    refine ⟨rfl, ?_⟩
    funext p
    simp [vis]

end Reference

/-- ✓ The reference executor satisfies EXEC-003: its `start` and `lose` rules judge the head of
the order on the pass-visible marking, a start consumes, drains and delivers from the visible
prefix only, a deposit in the pass joins the hidden tail, which stays to the end of the pass, only
`start` and `lose` change the order of a pass, `endPass` needs an empty order, and `begin` keeps
the marking and makes all of it visible (`exec003Lines_xstepW` at `refXPol`). -/
@[evidence holds EXEC_003]
theorem EXEC_003_reference {N T : Type} [DecidableEq N] :
    EXEC_003 (RefExec (N := N) (T := T)) :=
  exec003Lines_xstepW refXPol

/-- The inhibitor half of line 1 (ruling D75 (a)): under EXEC-003, a transition that starts in a
pass has every inhibitor place unmarked in the pass-visible marking, whatever a same-pass deposit
put into the live one. The start half of the bridge to [CORE-022] and [CORE-031]. -/
theorem EXEC_003_start_inhibitors {N T : Type} [DecidableEq N] {R : XRel N T} (h : EXEC_003 R)
    {C : Cfg N T} {s s' : XSt N T} {n : String} {sy : Bool} (hs : R C s (.start n sy) s') :
    ∃ t rest, s.order = t :: rest ∧ t.core.name = n ∧ ∀ p ∈ t.core.inhibitors, vis s p = [] := by
  obtain ⟨t, rest, ho, hn, -, he, -⟩ := (h C).1 n sy s s' hs
  refine ⟨t, rest, ho, hn, fun p hp => ?_⟩
  simp only [enabledNA, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at he
  have := he.1.2 p hp
  simpa [qCount] using this

/-! ### Examples

Places: `0` is `P`, the place `t1` and `t2` compete for; `1` is the reset place of `t3`; `2` and
`3` are the own inputs of `t3` and `t4`; `4` is the inhibitor place of `t4`. The transitions are
declared `t1, t2, t3, t4`, all `Immediate` with one priority, so the order of a pass is the
declaration order (the fast path of EXEC-002). The examples take that path because the kernel does
not evaluate the general path's merge sort on two or more ready transitions; with priorities
10, 5, 3 and 2 EXEC-002 forces the same order (EXEC_002_forced), and this block reads only the
head of whatever order the pass walks. The AC2 example has priorities and a `Delayed` transition.

The run starts `t1` synchronously; its action writes `5` to `P`, `8` to `1` and `6` to `4` and
returns, and the pass settles it (`commit 0`) before going on: `t2` loses although `P` holds `5`
again, `t3`'s reset takes the old token `3` from place `1` and leaves the deposited `8`, and `t4`
starts although its inhibitor place holds the deposited `6`. -/

/-- A transition without an output spec: name, input arcs, inhibitor places, reset places. -/
def exec003_tr (n : String) (ins : List (NInSpec Nat)) (inh resets : List Nat) : Trans Nat :=
  { core := { name := n, inputs := ins, inhibitors := inh, reads := [], resets := resets },
    out := none }

/-- `t1`: one token from `P`. -/
def exec003_t1 : Trans Nat := exec003_tr "t1" [⟨0, .one⟩] [] []
/-- `t2`: one token from `P`. -/
def exec003_t2 : Trans Nat := exec003_tr "t2" [⟨0, .one⟩] [] []
/-- `t3`: one token from `2`, reset arc on `1`. -/
def exec003_t3 : Trans Nat := exec003_tr "t3" [⟨2, .one⟩] [] [1]
/-- `t4`: one token from `3`, inhibitor arc on `4`. -/
def exec003_t4 : Trans Nat := exec003_tr "t4" [⟨3, .one⟩] [4] []

/-- The priorities of the AC2 example. -/
def exec003_prio (t : Trans Nat) : Int :=
  if t.core.name = "t1" then 10 else if t.core.name = "t2" then 5
  else if t.core.name = "t3" then 3 else 2

/-- The configuration of the examples, with priorities `pr` and timing `tm`: no output validation
to speak of (no transition has an output spec), no terminal or environment places. -/
def exec003_cfgT (ts : List (Trans Nat)) (pr : Trans Nat → Int) (tm : Trans Nat → Libpetri.Novel.TimedScg.Timing) : Cfg Nat Nat :=
  { X := { net := { places := [0, 1, 2, 3, 4], transitions := ts }, timing := tm, tol := 0 },
    prio := pr, terminals := [], envs := [], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => false,
    res := 0 }

/-- The four transitions, all `Immediate`, one priority. -/
def exec003_cfg : Cfg Nat Nat :=
  exec003_cfgT [exec003_t1, exec003_t2, exec003_t3, exec003_t4] (fun _ => 0) fun _ => .immediate

/-- The initial marking: `7` in `P`, the old token `3` in `1`, `9` in `2`, `4` in `3`. -/
def exec003_m0 : QMarking Nat Nat := fun p =>
  if p = 0 then [7] else if p = 1 then [3] else if p = 2 then [9] else if p = 3 then [4] else []

/-- A run of step function `g` under `C` from `s`. -/
def exec003_run (g : Cfg Nat Nat → XSt Nat Nat → XLbl Nat Nat → Option (XSt Nat Nat))
    (C : Cfg Nat Nat) (s : XSt Nat Nat) : List (XLbl Nat Nat) → Option (XSt Nat Nat)
  | [] => some s
  | l :: ls => (g C s l).bind fun s' => exec003_run g C s' ls

/-- One cycle up to the start of the pass. -/
def exec003_pre : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin]

/-- The pass up to the in-pass settle of `t1`: `t1` starts synchronously, its action writes `5`
to `P`, `8` to `1` and `6` to `4`, and returns. -/
def exec003_toRet : List (XLbl Nat Nat) :=
  exec003_pre ++ [.start "t1" true, .write 0 0 5, .write 0 1 8, .write 0 4 6, .ret 0 true]

/-- ... then the pass settles `t1` (its deposits join the hidden tail). -/
def exec003_toCommit : List (XLbl Nat Nat) := exec003_toRet ++ [.commit 0]

/-- ... then `t2` loses. -/
def exec003_toLose : List (XLbl Nat Nat) := exec003_toCommit ++ [.lose "t2"]

/-- ... then `t3` starts. -/
def exec003_toT3 : List (XLbl Nat Nat) := exec003_toLose ++ [.start "t3" false]

/-- ... then `t4` starts, the pass ends, and the next cycle runs up to its pass. -/
def exec003_toNext : List (XLbl Nat Nat) :=
  exec003_toT3 ++ [.start "t4" false, .endPass, .endCompletions, .endPublications, .endEvents,
    .update, .deadline []]

/-- The state the reference reaches along `ls`. -/
def exec003_at (ls : List (XLbl Nat Nat)) : Option (XSt Nat Nat) :=
  exec003_run xstep exec003_cfg (xinit exec003_m0 0) ls

/-! ### Mutant: the recheck on the live marking (the XPol field `recheckOn`) -/

/-- The judgement points of an executor that re-checks the head of the order on the live
marking. -/
def exec003_livePol {N T : Type} [DecidableEq N] : XPol N T :=
  { refXPol with recheckOn := (·.M) }

/-- The executor with those judgement points. -/
def exec003_liveRecheck {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => xstepW exec003_livePol C s l = some s'

/-- Mutant reading of EXEC-003: a start or a lose judges the head on the live marking, so a
same-pass deposit counts. The other lines are as in EXEC-003. -/
def EXEC_003_mutant_liveRecheck {N T : Type} [DecidableEq N] (R : XRel N T) : Prop :=
  exec003Lines (·.M) R

/-- The head of the order of `s` satisfies `p`. -/
def exec003_head (s : XSt Nat Nat) (p : Trans Nat → Bool) : Bool :=
  match s.order with
  | t :: _ => p t
  | [] => false

/-- Read `p` off the head of the order. -/
theorem exec003_of_head {s : XSt Nat Nat} {p : Trans Nat → Bool} (h : exec003_head s p = true)
    {t : Trans Nat} {rest : List (Trans Nat)} (ho : s.order = t :: rest) : p t = true := by
  simpa [exec003_head, ho] using h

/-- The executor that re-checks on the live marking kills the mutant: it satisfies the mutant
reading, but not EXEC-003. After `t1`'s action refilled `P` inside the pass, `t2` is enabled on
the live marking and starts, although the pass-visible `P` is empty (AC3, line 1). -/
@[evidence mutant EXEC_003]
theorem EXEC_003_mutant_liveRecheck_killed :
    EXEC_003_mutant_liveRecheck (exec003_liveRecheck (N := Nat) (T := Nat)) ∧
      ¬ EXEC_003 (exec003_liveRecheck (N := Nat) (T := Nat)) := by
  refine ⟨exec003Lines_xstepW exec003_livePol, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check (xstepW exec003_livePol) (C := exec003_cfg)
    (o := exec003_run (xstepW exec003_livePol) exec003_cfg (xinit exec003_m0 0) exec003_toCommit)
    (l := .start "t2" false)
    (p := fun s _ => exec003_head s fun t => !enabledNA (qCount (vis s)) t.core) (by decide +kernel)
  obtain ⟨t, rest, ho, -, -, he, -⟩ := (h exec003_cfg).1 "t2" false s s' hs
  have := exec003_of_head hp ho
  simp [he] at this

/-! ### Violation: starting a transition other than the head of the order -/

/-- An executor whose pass starts any transition of its order, not only the head (the rest of
the order kept). -/
def exec003_anyOrderStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .start n sy =>
    match s.order.find? (·.core.name == n) with
    | some t => xstep C { s with order := t :: s.order.filter (·.core.name != n) } (.start n sy)
    | none => none
  | l => xstep C s l

/-- The executor of `exec003_anyOrderStep`. -/
def exec003_anyOrder {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec003_anyOrderStep C s l = some s'

/-- ✗ Starting a transition behind the head of the order violates EXEC-003 (line 1, the headline
sentence): at the start of the pass `t2` starts while `t1` heads the order and is enabled (AC1:
with T1 of the higher priority at the head, T2 starts first). -/
@[evidence forbids EXEC_003]
theorem EXEC_003_forbids_anyOrder : ¬ EXEC_003 (exec003_anyOrder (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec003_anyOrderStep (C := exec003_cfg)
    (o := exec003_run exec003_anyOrderStep exec003_cfg (xinit exec003_m0 0) exec003_pre)
    (l := .start "t2" false)
    (p := fun s _ => exec003_head s fun t => t.core.name != "t2") (by decide +kernel)
  obtain ⟨t, rest, ho, hn, -⟩ := (h exec003_cfg).1 "t2" false s s' hs
  have := exec003_of_head hp ho
  simp [hn] at this

/-! ### Violation: a drain that swallows a same-pass deposit -/

/-- An executor whose start consumes and drains the live marking. -/
def exec003_drainSwallowsStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .start n sy => (xstep C s (.start n sy)).bind fun s₁ =>
      s.order.head?.map fun t => { s₁ with M := qConsume s.M t }
  | l => xstep C s l

/-- The executor of `exec003_drainSwallowsStep`. -/
def exec003_drainSwallows {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec003_drainSwallowsStep C s l = some s'

/-- ✗ A drain that swallows a same-pass deposit violates EXEC-003 (line 2, AC5): `t3`'s reset
empties place `1`, taking the `8` that `t1`'s action deposited in the pass. -/
@[evidence forbids EXEC_003]
theorem EXEC_003_forbids_drainSwallows :
    ¬ EXEC_003 (exec003_drainSwallows (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec003_drainSwallowsStep (C := exec003_cfg)
    (o := exec003_run exec003_drainSwallowsStep exec003_cfg (xinit exec003_m0 0) exec003_toLose)
    (l := .start "t3" false)
    (p := fun s s' => exec003_head s fun t => s'.M 1 != qConsume (vis s) t 1 ++ hid s 1)
    (by decide +kernel)
  obtain ⟨t, rest, ho, hM, -⟩ := (h exec003_cfg).2.1 "t3" false s s' hs
  have := exec003_of_head hp ho
  simp [hM] at this

/-! ### Violation: inhibitor arcs tested on the live marking (ruling D75 (b)) -/

/-- An executor that judges input counts and read arcs on the pass-visible marking but inhibitor
arcs on the live one: a head whose inhibitor place a same-pass deposit marked loses. -/
def exec003_liveInhStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .start n sy =>
    match s.order with
    | t :: _ => if t.core.inhibitors.all (fun p => (s.M p).isEmpty) then xstep C s (.start n sy)
                else none
    | [] => none
  | .lose n =>
    match s.order with
    | t :: rest =>
      if s.phase = .pass && liveB C s && passFree s && t.core.name == n &&
          !((stampOf (s.st n)).isSome && enabledNA (qCount (vis s)) t.core &&
            t.core.inhibitors.all (fun p => (s.M p).isEmpty)) then
        some { s with order := rest, st := fun m => if m = n then .off else s.st m }
      else none
    | [] => none
  | l => xstep C s l

/-- The executor of `exec003_liveInhStep`. -/
def exec003_liveInh {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec003_liveInhStep C s l = some s'

/-- ✗ Testing inhibitor arcs on the live marking violates EXEC-003 (line 3, ruling D75 (a)):
`t4` heads the order, holds a clock and is enabled on the pass-visible marking, yet loses because
`t1`'s action deposited `6` into its inhibitor place in the same pass. -/
@[evidence forbids EXEC_003]
theorem EXEC_003_forbids_liveInhibitor : ¬ EXEC_003 (exec003_liveInh (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec003_liveInhStep (C := exec003_cfg)
    (o := exec003_run exec003_liveInhStep exec003_cfg (xinit exec003_m0 0) exec003_toT3)
    (l := .lose "t4")
    (p := fun s _ => exec003_head s fun t =>
      (stampOf (s.st "t4")).isSome && enabledNA (qCount (vis s)) t.core) (by decide +kernel)
  obtain ⟨t, rest, ho, -, hne, -⟩ := (h exec003_cfg).2.2.1 "t4" s s' hs
  have := exec003_of_head hp ho
  simp only [Bool.and_eq_true] at this
  exact hne this

/-! ### Violation: a loser that keeps its clock -/

/-- An executor whose loser keeps its clock status. -/
def exec003_keepClockStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .lose n => (xstep C s (.lose n)).map fun s₁ => { s₁ with st := s.st }
  | l => xstep C s l

/-- The executor of `exec003_keepClockStep`. -/
def exec003_keepClock {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec003_keepClockStep C s l = some s'

/-- ✗ A loser that keeps its clock violates EXEC-003 (line 4, AC1 "T2 disabled", TIME-012's
recheck sentence): `t2` loses and is still armed. -/
@[evidence forbids EXEC_003]
theorem EXEC_003_forbids_loserKeepsClock :
    ¬ EXEC_003 (exec003_keepClock (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec003_keepClockStep (C := exec003_cfg)
    (o := exec003_run exec003_keepClockStep exec003_cfg (xinit exec003_m0 0) exec003_toCommit)
    (l := .lose "t2") (p := fun _ s' => decide (s'.st "t2" ≠ .off)) (by decide +kernel)
  have := ((h exec003_cfg).2.2.2.1 "t2" s s' hs).1
  simp [this] at hp

/-! ### Violation: a same-pass deposit visible to the rest of the pass -/

/-- An executor whose in-pass settle deposits into the visible part of the marking. -/
def exec003_visibleDepositStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .commit i => (xstep C s (.commit i)).map fun s₁ => { s₁ with delta := s.delta }
  | l => xstep C s l

/-- The executor of `exec003_visibleDepositStep`. -/
def exec003_visibleDeposit {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec003_visibleDepositStep C s l = some s'

/-- ✗ A same-pass deposit that becomes visible violates EXEC-003 (line 5, AC3 and AC4): the
in-pass settle of `t1` makes its `5` in `P` visible to the rest of the pass. -/
@[evidence forbids EXEC_003]
theorem EXEC_003_forbids_visibleDeposit :
    ¬ EXEC_003 (exec003_visibleDeposit (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec003_visibleDepositStep (C := exec003_cfg)
    (o := exec003_run exec003_visibleDepositStep exec003_cfg (xinit exec003_m0 0) exec003_toRet)
    (l := .commit 0) (p := fun s s' => decide (s.phase = .pass) && vis s' 0 != vis s 0)
    (by decide +kernel)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  have := ((h exec003_cfg).2.2.2.2.1 s s' ⟨hp.1, .commit 0, hs, fun _ _ h => by cases h⟩).1
  simp [this] at hp

/-! ### Violation: the hidden tail kept into the next pass -/

/-- An executor whose `begin` keeps the hidden tail of the previous pass. -/
def exec003_staleDeltaStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .begin => (xstep C s .begin).map fun s₁ => { s₁ with delta := s.delta }
  | l => xstep C s l

/-- The executor of `exec003_staleDeltaStep`. -/
def exec003_staleDelta {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec003_staleDeltaStep C s l = some s'

/-- ✗ Keeping the hidden tail into the next pass violates EXEC-003 (line 8, AC4 "visible at the
next cycle"): at the next pass `t1`'s deposit `5` in `P` is still not pass-visible. -/
@[evidence forbids EXEC_003]
theorem EXEC_003_forbids_staleDelta : ¬ EXEC_003 (exec003_staleDelta (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec003_staleDeltaStep (C := exec003_cfg)
    (o := exec003_run exec003_staleDeltaStep exec003_cfg (xinit exec003_m0 0) exec003_toNext)
    (l := .begin) (p := fun _ s' => vis s' 0 != s'.M 0) (by decide +kernel)
  have := ((h exec003_cfg).2.2.2.2.2.2.2 s s' hs).2
  simp [this] at hp

/-! ### Violation: the action handed the live queue -/

/-- The firing list after a start from `s`, with what the newest firing (the one the start
appended) was handed taken from the live marking. -/
def exec003_liveDeliv {N T : Type} [DecidableEq N] (s : XSt N T) (s₁ : XSt N T) : XSt N T :=
  match s.order with
  | t :: _ => { s₁ with fl := s₁.fl.map fun g => if g.id = s.nextId then
                  { g with deliv := qDelivered s.M t } else g }
  | [] => s₁

/-- An executor whose start removes from the marking what the reference removes, the visible
prefix, but builds what it hands the action from the live queue: an `all()` input hands the action
the same-pass deposit as well, which also stays in the place. -/
def exec003_liveDeliverStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .start n sy => (xstep C s (.start n sy)).map (exec003_liveDeliv s)
  | l => xstep C s l

/-- The executor of `exec003_liveDeliverStep`. -/
def exec003_liveDeliver {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec003_liveDeliverStep C s l = some s'

/-- `t5`: an `all()` input on place `1`. -/
def exec003_t5 : Trans Nat := exec003_tr "t5" [⟨1, .all⟩] [] []

/-- `t1` (one from `P`) and `t5`, both `Immediate`, one priority. -/
def exec003_cfgAll : Cfg Nat Nat :=
  exec003_cfgT [exec003_t1, exec003_t5] (fun _ => 0) fun _ => .immediate

/-- `7` in `P`, the old `3` in place `1`. -/
def exec003_m0All : QMarking Nat Nat := fun p => if p = 0 then [7] else if p = 1 then [3] else []

/-- `t1` starts synchronously, its action writes `5` to place `1`, the pass settles it. -/
def exec003_passAll : List (XLbl Nat Nat) :=
  exec003_pre ++ [.start "t1" true, .write 0 1 5, .ret 0 true, .commit 0]

/-- ✗ Handing the action the live queue violates EXEC-003 (line 2, AC5): `t5`'s `all()` leaves
the deposited `5` in place `1`, as it must, and also hands it to the action, which receives
`[3, 5]` where the pass-visible marking delivers `[3]`; the deposit is used twice. -/
@[evidence forbids EXEC_003]
theorem EXEC_003_forbids_liveDeliver :
    ¬ EXEC_003 (exec003_liveDeliver (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec003_liveDeliverStep (C := exec003_cfgAll)
    (o := exec003_run exec003_liveDeliverStep exec003_cfgAll (xinit exec003_m0All 0)
      exec003_passAll)
    (l := .start "t5" false)
    (p := fun s s' => s.fl.all (·.id != s.nextId) &&
      (match s'.fl.find? (·.id == s.nextId) with
       | some f => f.deliv.inputs 1 == [3, 5]
       | none => false) &&
      exec003_head s (fun t => (qDelivered (vis s) t).inputs 1 == [3]))
    (by decide +kernel)
  simp only [Bool.and_eq_true] at hp
  obtain ⟨⟨hall, hf⟩, hhd⟩ := hp
  obtain ⟨t, rest, ho, -, -, hd⟩ := (h exec003_cfgAll).2.1 "t5" false s s' hs
  have ht := exec003_of_head hhd ho
  cases hfind : s'.fl.find? (·.id == s.nextId) with
  | none => simp [hfind] at hf
  | some f =>
    simp only [hfind, beq_iff_eq] at hf
    have hmem : f ∈ s'.fl := List.mem_of_find?_eq_some hfind
    have hid' : f.id = s.nextId := by simpa using List.find?_some hfind
    have hn : f ∉ s.fl := by
      intro hm
      have := List.all_eq_true.mp hall f hm
      simp [hid'] at this
    have := hd f hmem hn
    rw [this] at hf
    simp only [beq_iff_eq] at ht
    rw [ht] at hf
    simp at hf

/-! ### Violation: the hidden tail cut at the end of the pass -/

/-- An executor whose `endPass` cuts every queue back to its pass-visible prefix and clears the
deposit counts, so the tokens a synchronous action deposited in the pass are lost instead of
becoming visible at the next pass (a cleanup that applies `truncate(live - deposit_delta)`). -/
def exec003_tailCutStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .endPass => (xstep C s .endPass).map fun s₁ => { s₁ with M := vis s₁, delta := fun _ => 0 }
  | l => xstep C s l

/-- The executor of `exec003_tailCutStep`. -/
def exec003_tailCut {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec003_tailCutStep C s l = some s'

/-- ✗ Cutting the hidden tail at the end of the pass violates EXEC-003 (line 5, AC3 and AC4 "at
the next cycle"): the end of the pass drops `t1`'s deposit `5` from `P`, so the next pass never
sees it. The cut keeps the pass-visible marking, so only the hidden tail line catches it. -/
@[evidence forbids EXEC_003]
theorem EXEC_003_forbids_tailCut : ¬ EXEC_003 (exec003_tailCut (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec003_tailCutStep (C := exec003_cfg)
    (o := exec003_run exec003_tailCutStep exec003_cfg (xinit exec003_m0 0)
      (exec003_toT3 ++ [.start "t4" false]))
    (l := .endPass)
    (p := fun s s' => decide (s.phase = .pass) && !((hid s 0).isPrefixOf (hid s' 0)))
    (by decide +kernel)
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hp
  have := ((h exec003_cfg).2.2.2.2.1 s s' ⟨hp.1, .endPass, hs, fun _ _ h => by cases h⟩).2 0
  rw [← List.isPrefixOf_iff_prefix] at this
  simp [this] at hp

/-! ### Violation: the order pruned when a synchronous action settles -/

/-- An executor whose in-pass settle re-filters the rest of the order to the entries still armed
and enabled on the pass-visible marking, dropping the others silently instead of offering them as
losers, so they keep their clocks (a refreshed ready list that skips a dropped entry). -/
def exec003_pruneOrderStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .commit i => (xstep C s (.commit i)).map fun s₁ =>
      if s.phase = .pass then
        { s₁ with order := s₁.order.filter fun t =>
            (stampOf (s₁.st t.core.name)).isSome && enabledNA (qCount (vis s₁)) t.core }
      else s₁
  | l => xstep C s l

/-- The executor of `exec003_pruneOrderStep`. -/
def exec003_pruneOrder {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec003_pruneOrderStep C s l = some s'

/-- ✗ Pruning the order when a synchronous action settles violates EXEC-003 (line 6, "shall lose
its clock"): the settle of `t1` removes `t2` from the order, so `t2` never loses and keeps its
clock past the pass. -/
@[evidence forbids EXEC_003]
theorem EXEC_003_forbids_pruneOrder : ¬ EXEC_003 (exec003_pruneOrder (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec003_pruneOrderStep (C := exec003_cfg)
    (o := exec003_run exec003_pruneOrderStep exec003_cfg (xinit exec003_m0 0) exec003_toRet)
    (l := .commit 0)
    (p := fun s s' => decide (s.phase = .pass) &&
      s'.order.map (·.core.name) != s.order.map (·.core.name))
    (by decide +kernel)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  have := (h exec003_cfg).2.2.2.2.2.1 s s'
    ⟨hp.1, .commit 0, hs, (fun _ _ h => by cases h), (fun _ h => by cases h)⟩
  simp [this] at hp

/-! ### Violation: a pass that ends before its order is empty -/

/-- An executor whose pass may end with entries still in the order: they are neither started nor
dropped and keep their clocks (an early exit from the walk over the ready list). The order itself
is left as it was. -/
def exec003_earlyEndStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .endPass => (xstep C { s with order := [] } .endPass).map fun s₁ => { s₁ with order := s.order }
  | l => xstep C s l

/-- The executor of `exec003_earlyEndStep`. -/
def exec003_earlyEnd {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec003_earlyEndStep C s l = some s'

/-- ✗ Ending the pass before its order is empty violates EXEC-003 (line 7, the headline sentence
and "shall lose its clock"): the pass ends right after it begins, with `t1` at the head of its
order. -/
@[evidence forbids EXEC_003]
theorem EXEC_003_forbids_earlyEnd : ¬ EXEC_003 (exec003_earlyEnd (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec003_earlyEndStep (C := exec003_cfg)
    (o := exec003_run exec003_earlyEndStep exec003_cfg (xinit exec003_m0 0) exec003_pre)
    (l := .endPass) (p := fun s _ => !s.order.isEmpty) (by decide +kernel)
  have := (h exec003_cfg).2.2.2.2.2.2.1 s s' hs
  simp [this] at hp

/-! ### Violation: the next pass begins on a cut marking -/

/-- An executor whose `begin` replaces the marking by the pass-visible marking it finds, so the
tail deposited in the previous pass is lost instead of becoming visible. -/
def exec003_beginCutStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .begin => (xstep C s .begin).map fun s₁ => { s₁ with M := vis s }
  | l => xstep C s l

/-- The executor of `exec003_beginCutStep`. -/
def exec003_beginCut {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec003_beginCutStep C s l = some s'

/-- ✗ Beginning the next pass on the cut marking violates EXEC-003 (line 8, AC4 "visible at the
next cycle"): the next pass begins with `P` empty, `t1`'s deposit `5` gone. Everything left is
pass-visible, so only the line's first half catches it. -/
@[evidence forbids EXEC_003]
theorem EXEC_003_forbids_beginCut : ¬ EXEC_003 (exec003_beginCut (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec003_beginCutStep (C := exec003_cfg)
    (o := exec003_run exec003_beginCutStep exec003_cfg (xinit exec003_m0 0) exec003_toNext)
    (l := .begin) (p := fun s s' => s'.M 0 != s.M 0) (by decide +kernel)
  have := ((h exec003_cfg).2.2.2.2.2.2.2 s s' hs).1
  simp [this] at hp

/-! ### Every line exercised -/

/-- Every line of EXEC-003 is exercised by the reference. With `t1` started asynchronously
(nothing refills `P`), `t2` loses and has no clock (AC1, the test derivation). With `t1`'s
synchronous action refilling `P` inside the pass, `t2` loses although the live `P` holds `5`, and
the pass-visible `P` is empty (AC3, line 3); the in-pass settle deposits `5` in `P` while the
pass-visible `P` stays empty (line 5); `t3`'s reset takes the old `3` and leaves the deposited `8`
(AC5, line 2); `t4` starts although its inhibitor place holds the deposited `6` (D75 (a), line 1);
the next pass offers `t2` again, with `5` pass-visible (AC3 "the next cycle", line 8); and the
pass ends with its order empty and the deposited `5` still in the hidden tail of `P` (lines 5 and
7). -/
@[evidence nonvacuous EXEC_003]
theorem EXEC_003_nonvacuous :
    (∃ s s', RefExec exec003_cfg s (.lose "t2") s' ∧ s.M 0 = [] ∧ s'.st "t2" = .off) ∧
    (∃ s s', RefExec exec003_cfg s (.lose "t2") s' ∧ s.M 0 = [5] ∧ vis s 0 = [] ∧
      s'.st "t2" = .off) ∧
    (∃ s s', RefExec exec003_cfg s (.commit 0) s' ∧ s.phase = .pass ∧ s'.M 0 = [5] ∧
      vis s' 0 = []) ∧
    (∃ s s', RefExec exec003_cfg s (.start "t3" false) s' ∧ s.M 1 = [3, 8] ∧ s'.M 1 = [8]) ∧
    (∃ s s', RefExec exec003_cfg s (.start "t4" false) s' ∧ s.M 4 = [6]) ∧
    (∃ s s', RefExec exec003_cfg s .begin s' ∧ vis s' 0 = [5] ∧
      "t2" ∈ s'.order.map (·.core.name)) ∧
    (∃ s s', RefExec exec003_cfg s .endPass s' ∧ s.order = [] ∧ hid s' 0 = [5]) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := exec003_cfg)
      (o := exec003_at (exec003_pre ++ [.start "t1" false])) (l := .lose "t2")
      (p := fun s s' => s.M 0 == [] && decide (s'.st "t2" = .off)) (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
    exact ⟨s, s', hs, hp⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := exec003_cfg)
      (o := exec003_at exec003_toCommit) (l := .lose "t2")
      (p := fun s s' => s.M 0 == [5] && vis s 0 == [] && decide (s'.st "t2" = .off))
      (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
    exact ⟨s, s', hs, hp.1.1, hp.1.2, hp.2⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := exec003_cfg)
      (o := exec003_at exec003_toRet) (l := .commit 0)
      (p := fun s s' => decide (s.phase = .pass) && s'.M 0 == [5] && vis s' 0 == [])
      (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
    exact ⟨s, s', hs, hp.1.1, hp.1.2, hp.2⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := exec003_cfg)
      (o := exec003_at exec003_toLose) (l := .start "t3" false)
      (p := fun s s' => s.M 1 == [3, 8] && s'.M 1 == [8]) (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', hs, hp⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := exec003_cfg)
      (o := exec003_at exec003_toT3) (l := .start "t4" false)
      (p := fun s _ => s.M 4 == [6]) (by decide +kernel)
    exact ⟨s, s', hs, by simpa using hp⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := exec003_cfg)
      (o := exec003_at exec003_toNext) (l := .begin)
      (p := fun _ s' => vis s' 0 == [5] && (s'.order.map (·.core.name)).contains "t2")
      (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hp
    exact ⟨s, s', hs, hp⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := exec003_cfg)
      (o := exec003_at (exec003_toT3 ++ [.start "t4" false])) (l := .endPass)
      (p := fun s s' => s.order.isEmpty && hid s' 0 == [5]) (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hp
    exact ⟨s, s', hs, hp⟩

/-! ### AC2: a transition that is not ready does not block a competitor -/

/-- `t1` Delayed(10) of priority 10, `t2` Immediate of priority 5, both on `P`. -/
def exec003_cfgAC2 : Cfg Nat Nat :=
  exec003_cfgT [exec003_t1, exec003_t2] exec003_prio fun t =>
    if t.core.name = "t1" then Libpetri.Novel.TimedScg.Timing.delayed 10
    else Libpetri.Novel.TimedScg.Timing.immediate

/-- AC2: EXEC-003 allows the lower-priority `t2` to take the token while `t1`, of higher priority,
is armed and enabled but below its earliest bound: the reference satisfies EXEC-003 and, at
reading `0`, starts `t2` from the token `t1` waits for. -/
@[evidence allows EXEC_003]
theorem EXEC_003_allows_notReady :
    EXEC_003 (RefExec (N := Nat) (T := Nat)) ∧
      ∃ s s', RefExec exec003_cfgAC2 s (.start "t2" false) s' ∧
        (stampOf (s.st "t1")).isSome = true ∧ enabledNA (qCount s.M) exec003_t1.core = true ∧
        s'.M 0 = [] := by
  refine ⟨EXEC_003_reference, ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := exec003_cfgAC2)
    (o := exec003_run xstep exec003_cfgAC2 (xinit exec003_m0 0) exec003_pre)
    (l := .start "t2" false)
    (p := fun s s' => (stampOf (s.st "t1")).isSome && enabledNA (qCount s.M) exec003_t1.core &&
      s'.M 0 == [])
    (by decide +kernel)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨s, s', hs, hp.1.1, hp.1.2, hp.2⟩

end Libpetri.Spec
