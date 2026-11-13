import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Exec
import Libpetri.Spec.Req.EXEC_022
import Libpetri.Spec.Text.EXEC_031

set_option linter.missingDocs true

/-!
# EXEC-031: No rollback (`spec/04-execution-model.md`)

A requirement block over the executor model (`RefExec`, `Reference/Exec.lean`). A firing fails
when its action throws or returns an error ([EXEC-030], the label `ret i false`), or when output
validation or the join-relay check rejects what it produced ([EXEC-021], [NU-054]); a failed
firing is settled by a `fail i` step. No rollback has three lines in the model: the fail step puts
nothing back, neither into the marking nor into the publication queue (line 1); after the error
return (taken while the firing is open) or the fail step, no later step deposits on behalf of the
failed firing, neither its completion nor a timeout outcome (line 2, a trace line read with
`after T, never B` of `Ears.lean`); and on a run on which the firing fails, the steps in which its
action reports put nothing back either (line 3).

Lines 2 and 3 read runs from a state in which every firing in flight has an identity the supply
has already handed out (`IdsIssued`); the initial state has nothing in flight, and the
reference keeps the property on every step (`exec031_idsIssued_step`). After an error return the
firing holds the error outcome until its fail step, and after the fail step it is gone, so no
later `commit i` or `tdeposit i` finds a firing `i` it could deposit (`exec031_Banned`).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## Block-local terms -/

section Terms

variable {N T : Type}

/-- The step is the fail step of firing `i`. -/
def exec031_isFail (i : Nat) : XStep N T → Bool
  | (_, .fail j, _) => j == i
  | _ => false

/-- The step shows that firing `i` failed: its action returned an error (`ret i false`) while
firing `i` was open (no outcome recorded, as `exec022_isOpenReturn` reads it), or the fail step
of `i` settled it. A late error return of an action whose firing already ended, by its budget
running out, does not fail the firing ([EXEC-022]: a firing that has ended keeps how it ended). -/
def exec031_isFailed (i : Nat) : XStep N T → Bool
  | (_, .fail j, _) => j == i
  | (s, .ret j false, _) => j == i && s.fl.any fun f => f.id == i && f.out.isNone
  | _ => false

/-- The step is a report of firing `i`'s action: a return (`ret`, normal or with an error) or the
expiry of its budget (`expire`). -/
def exec031_isReport (i : Nat) : XStep N T → Bool
  | (_, .ret j _, _) => j == i
  | (_, .expire j _, _) => j == i
  | _ => false

/-- The step deposits the completion (`commit`) or the timeout outcome (`tdeposit`) of firing
`i`: the two settle steps that deposit. -/
def exec031_isDeposit (i : Nat) : XStep N T → Bool
  | (_, .commit j, _) => j == i
  | (_, .tdeposit j, _) => j == i
  | _ => false

end Terms

/-! ## EXEC-031: No Rollback -/

requirement EXEC_031
  id "EXEC-031"
  title "No Rollback"
  kind B
  scope "all executors"
  source verbatim "spec/04-execution-model.md"
  covers EXEC_031.s1, EXEC_031.s2, EXEC_031.s3, EXEC_031.s4, EXEC_031.s5
  reading "For every executor R, every configuration C and every firing identity i:"
          "a fail step of i leaves the marking and the publication queue unchanged;"
          "on every run of R that starts in a state in which every firing in flight has an identity the supply has already handed out (so an identity names one firing), no commit step of i and no tdeposit step of i comes after an error return of i's action (ret i false) taken while firing i is open (no outcome recorded) or after a fail step of i;"
          "on every such run on which i's action returns an error while firing i is open or i has a fail step, every return step and every expiry step of i leaves the marking and the publication queue unchanged."
  assumes "The model is an executor R : XRel N T (glossary GlossaryExec.lean): R C s l s' says that under configuration C the step labelled l leads from executor state s to s'. A firing starts in a firing pass; its action reports in a ret step (a normal return, or an error) or an expire step (its budget ran out, with a timeout outcome); a settle step then deposits the outcome (commit, tdeposit) or deposits nothing (fail). The witness is the reference executor RefExec (Reference/Exec.lean)."
          "The third quoted sentence names three causes of a failure, and the model has the same three. An action error is the label ret i false ([EXEC-030]). A rejection by output validation or by the join-relay check (of a returned emission, of a flushed batch, which marks the firing relayBad, or of a timeout outcome) is decided at the settle, which is then a fail i step. That a rejection is settled by fail i and never by a deposit is EXEC-021's lines 1, 3 and 5 (under C.SetValidated) and NU-054's subject; this block reads the labels and does not restate that classification. The trigger of line 2 is either label, the error return or the fail step. The error return counts only while firing i is open: an action whose budget ran out has ended its firing with the timeout outcome, and EXEC-022 lets its late return still be a step, provided it changes neither the marking, the queue, nor how the firing ended (EXEC-022's fourth shall sentence and its line 5). Such a late error return is not a failure of the firing, whose timeout outcome is then deposited; EXEC_031_allows_lateErrorAfterExpiry is that run, on an executor that offers the late return as a step that changes nothing."
          "The first quoted sentence is the block as a whole. The second is the two shall sentences, which the third extends from an action failure to every failure: EXEC-021's third shall sentence says the same of a validation failure. The rationale sentence of the markdown (rollback would need compensation logic and conflicts with asynchronous actions) states no behaviour and is not encoded."
          "The first shall sentence is lines 1 and 3. Line 1: the fail step changes neither the marking nor the publication queue, so the settle puts no consumed token back, neither into a place (EXEC_031_forbids_failRestores) nor as a publication queued for a later publish step (EXEC_031_forbids_failQueues, whose fail step keeps the marking: exec031_failQueues_markingOnly). Line 1 restates EXEC-030's item 2 and EXEC-021's line 2; the restatement is known clash exec#15, kept under ruling D20. It is stronger than 'restores nothing': the fail step also removes nothing, so the tokens the action already published into the marking stay, and the batches it flushed that are still queued stay queued."
          "Line 3: on a run on which firing i fails, the steps in which its action reports (ret i, expire i) change neither the marking nor the publication queue, so no rollback runs when the action reports its error, before the settle (EXEC_031_forbids_restoreAtError; that executor passes lines 1 and 2 on its run: exec031_restoreAtError_onlyLine3). The line reads every report of a failing firing, a normal return too, since a validation failure is known only at the settle. EXEC-021's line 4 says the same of the marking for the ret and write steps of every firing."
          "The second shall sentence is line 2: after the error return or the fail step of firing i, no later step deposits its completion (commit i) or a timeout outcome (tdeposit i). A retry of the failed action breaks the commit half (EXEC_031_forbids_retry). A rollback that deposits the consumed tokens as a timeout outcome after the fail breaks the tdeposit half and passes a line that bans commit steps only (EXEC_031_forbids_rollbackLater, exec031_rollbackLater_commitOnly). An executor that turns an action error into a timeout outcome has no fail step at all and is caught only by the error-return trigger (EXEC_031_forbids_errAsTimeout, exec031_errAsTimeout_failOnly). A publish step of i after the failure is not banned: it deposits a batch the action itself flushed before the failure was settled (ruling D17), and lines 1 and 3 keep the fail step and the report steps from queueing any other."
          "Lines 2 and 3 identify the firing by its identity. Identities are drawn once from one supply (XSt.nextId), the naming convention of the glossary that EXEC-021 also reads, and the premise of both lines says that every firing in flight at the start of the run has an identity the supply has already handed out: true at the start of every run (nothing is in flight) and kept by every reference step (exec031_idsIssued_step). Without it a later start could reuse the identity of a failed firing, and the reference itself would show a commit of i after a fail of i (exec031_needs_idsIssued). An executor that hands out one identity twice is outside the model; that it does not is this naming convention, not a sentence of EXEC-031."
          "AC1 (failed action, consumed tokens permanently removed) is lines 1, 2 and 3 for the steps of the failed firing. The other half of 'permanently', that no step outside the failed firing (a phase step such as endCompletions, update or begin, an injection, the start of another firing) puts the consumed tokens back, is the marking frame of the executor: which steps may change the marking at all. That frame is stated over this model by CONC-001's line 2 (a step that is neither a start nor a deposit leaves the marking as it was), and the steps that do change the marking are pinned by their own blocks: a start by EXEC-003's line 2, an injection by ENV-003's line 2, a commit by EXEC-021's line 1, a timeout deposit by EXEC-022's line 3 and a publication by CONC-003's lines. None of them puts back a token a failed firing consumed, so this block cites that frame and does not restate it. EXEC_031_nonvacuous runs a net whose first firing consumes the token 7 and fails on an action error, and at the finish the token 7 is in no place of the net; its third part fails a firing on output validation (the action returns a token for a place outside its output spec), and that token is never deposited. The test derivation (fire a transition consuming a token, the action fails, the token is in no place) is the first run."
          "The TransitionFailed event of the failure is EXEC-030's and EVT-008's, on the event model of wave W7; host faults that are not action failures are EXEC-030's assumption (R-EXEC-7)."
  signoff "2026-11-13 029bfecc80e62997 ai"
  statement : ∀ {N T : Type} [DecidableEq N], XRel N T → Prop :=
    fun R => ∀ C i,
      (on (fun s s' => R C s (.fail i) s'), shall (fun s s' => s'.M = s.M ∧ s'.pq = s.pq)) ∧
      (∀ s0 tr, IdsIssued s0 → XRun R C s0 tr →
        (after (exec031_isFailed i), never (exec031_isDeposit i)) tr) ∧
      (∀ s0 tr, IdsIssued s0 → XRun R C s0 tr → tr.any (exec031_isFailed i) = true →
        ∀ st ∈ tr, exec031_isReport i st = true → st.2.2.M = st.1.M ∧ st.2.2.pq = st.1.pq)

/- The pinned readable form of EXEC-031: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EXEC_031 : {N T : Type} → [DecidableEq N] → XRel N T → Prop :=
fun {N T} [DecidableEq N] R =>
  ∀ (C : Cfg N T) (i : ℕ),
    (on fun s s' => R C s (XLbl.fail i) s', shall fun s s' => s'.M = s.M ∧ s'.pq = s.pq) ∧
      (∀ (s0 : XSt N T) (tr : List (XStep N T)),
          IdsIssued s0 → XRun R C s0 tr → (after exec031_isFailed i, never exec031_isDeposit i) tr) ∧
        ∀ (s0 : XSt N T) (tr : List (XStep N T)),
          IdsIssued s0 →
            XRun R C s0 tr →
              tr.any (exec031_isFailed i) = true →
                ∀ st ∈ tr, exec031_isReport i st = true → st.2.2.M = st.1.M ∧ st.2.2.pq = st.1.pq
-/
#guard_msgs in #print EXEC_031

/-! ### The reference -/

section Reference

variable {N T : Type} [DecidableEq N]

/-- One step keeps the identity supply: the supply never goes back, and every firing in flight
after the step was in flight before it (same identity) or got an identity the step handed out. -/
def exec031_IdFrame (s s' : XSt N T) : Prop :=
  s.nextId ≤ s'.nextId ∧
    ∀ f ∈ s'.fl, (∃ g ∈ s.fl, g.id = f.id) ∨ (s.nextId ≤ f.id ∧ f.id < s'.nextId)

omit [DecidableEq N] in
/-- A step that keeps the supply and only keeps, updates or drops firings keeps the frame. -/
theorem exec031_idFrame_of {s s' : XSt N T} (hn : s'.nextId = s.nextId)
    (hfl : ∀ f ∈ s'.fl, ∃ g ∈ s.fl, g.id = f.id) : exec031_IdFrame s s' :=
  ⟨hn ▸ Nat.le_refl _, fun f hf => Or.inl (hfl f hf)⟩

omit [DecidableEq N] in
/-- Updating firing `i`'s record by an `h` that keeps identities keeps every identity. -/
theorem exec031_mem_updFiring {s : XSt N T} {i : Nat} {h : Firing N T → Firing N T}
    (hh : ∀ g, (h g).id = g.id) {f : Firing N T} (hf : f ∈ updFiring s i h) :
    ∃ g ∈ s.fl, g.id = f.id := by
  unfold updFiring at hf
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
  refine ⟨g, hg, ?_⟩
  split <;> simp [hh]

omit [DecidableEq N] in
/-- A settle drops firing `i` and keeps the others. -/
theorem exec031_mem_settle {s : XSt N T} {i : Nat} {f : Firing N T}
    (hf : f ∈ (settle s i).fl) : f ∈ s.fl ∧ f.id ≠ i := by
  simp only [settle, List.mem_filter, bne_iff_ne, ne_eq] at hf
  exact hf

/-- Every reference step (at any judgement points `P`) keeps the identity frame: only `start`
adds a firing, with the identity it draws from the supply; `request` draws a ticket; every other
step keeps, updates or drops firings, and keeps the supply. -/
theorem exec031_idFrame_step {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : xstepW P C s l = some s') : exec031_IdFrame s s' := by
  have same : ∀ {s'' : XSt N T}, s''.nextId = s.nextId → s''.fl = s.fl →
      exec031_IdFrame s s'' := fun hn hfl =>
    exec031_idFrame_of hn fun f hf => ⟨f, hfl ▸ hf, rfl⟩
  have upd : ∀ {s'' : XSt N T} {i : Nat} {h : Firing N T → Firing N T},
      s''.fl = updFiring s i h → s''.nextId = s.nextId → (∀ g, (h g).id = g.id) →
      exec031_IdFrame s s'' :=
    fun hfl hn hh => exec031_idFrame_of hn fun f hf => exec031_mem_updFiring hh (hfl ▸ hf)
  have stl : ∀ {s'' : XSt N T} {i : Nat}, s''.nextId = s.nextId → s''.fl = (settle s i).fl →
      exec031_IdFrame s s'' := fun hn hfl =>
    exec031_idFrame_of hn fun f hf => ⟨f, (exec031_mem_settle (hfl ▸ hf)).1, rfl⟩
  cases l with
  | delay δ => obtain rfl := xstepW_delay h; exact same rfl rfl
  | write i p x =>
    obtain ⟨-, -, -, rfl⟩ := writeStep_some h; exact upd rfl rfl (fun _ => rfl)
  | flush i =>
    obtain ⟨-, -, -, -, -, ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ := flushStep_some h
    · exact upd rfl rfl (fun _ => rfl)
    · exact upd rfl rfl (fun _ => rfl)
  | ret i ok => obtain ⟨-, -, -, rfl⟩ := retStep_some h; exact upd rfl rfl (fun _ => rfl)
  | expire i e =>
    obtain ⟨-, -, -, -, -, -, rfl⟩ := expireStep_some h; exact upd rfl rfl (fun _ => rfl)
  | request p x r =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := requestStep_some h
    · exact ⟨Nat.le_succ _, fun f hf => Or.inl ⟨f, hf, rfl⟩⟩
    · exact same rfl rfl
  | drain => obtain ⟨-, rfl⟩ := drainStep_some h; exact same rfl rfl
  | close => obtain ⟨-, rfl⟩ := closeStep_some h; exact same rfl rfl
  | terminateNow => obtain ⟨-, rfl⟩ := terminateStep_some h; exact same rfl rfl
  | commit i =>
    obtain ⟨-, -, -, -, -, -, -, rfl⟩ := commitStep_some h; exact stl rfl rfl
  | fail i => obtain ⟨-, -, -, -, rfl⟩ := failStep_some h; exact stl rfl rfl
  | tdeposit i => obtain ⟨-, -, -, -, -, -, rfl⟩ := tdepositStep_some h; exact stl rfl rfl
  | endCompletions => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endCompletions h; exact same rfl rfl
  | publish i => obtain ⟨-, -, -, -, -, rfl⟩ := publishStep_some h; exact same rfl rfl
  | endPublications => obtain ⟨-, -, -, rfl⟩ := xstepW_endPublications h; exact same rfl rfl
  | inject k => obtain ⟨-, -, -, -, -, -, -, rfl⟩ := injectStep_some h; exact same rfl rfl
  | discard k => obtain ⟨-, -, -, -, -, -, -, rfl⟩ := discardStep_some h; exact same rfl rfl
  | snapshot a => obtain ⟨-, -, -, rfl⟩ := snapshotStep_some h; exact same rfl rfl
  | endEvents => obtain ⟨-, -, -, rfl⟩ := xstepW_endEvents h; exact same rfl rfl
  | update => obtain ⟨-, -, rfl⟩ := xstepW_update h; exact same rfl rfl
  | deadline ns => obtain ⟨-, -, -, rfl⟩ := xstepW_deadline h; exact same rfl rfl
  | finish c =>
    cases c with
    | quiescent => obtain ⟨-, -, -, rfl⟩ := xstepW_finishQuiescent h; exact same rfl rfl
    | closed => obtain ⟨-, -, -, -, rfl⟩ := xstepW_finishClosed h; exact same rfl rfl
    | terminal => obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h; exact same rfl rfl
    | stopped => obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h; exact same rfl rfl
  | begin => obtain ⟨-, -, -, -, rfl⟩ := xstepW_begin h; exact same rfl rfl
  | start n sy =>
    obtain ⟨-, -, -, -, -, -, -, -, -, rfl⟩ := startStep_some h
    refine ⟨Nat.le_succ _, fun f hf => ?_⟩
    rcases List.mem_append.mp hf with hf | hf
    · exact Or.inl ⟨f, hf, rfl⟩
    · rw [List.mem_singleton] at hf
      subst hf
      exact Or.inr ⟨Nat.le_refl _, Nat.lt_succ_self _⟩
  | lose n => obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := loseStep_some h; exact same rfl rfl
  | endPass => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endPass h; exact same rfl rfl
  | park tmr => obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := parkStep_some h; exact same rfl rfl
  | wake => obtain ⟨-, -, rfl⟩ := wakeStep_some h; exact same rfl rfl

omit [DecidableEq N] in
/-- The identity frame keeps `IdsIssued`. -/
theorem exec031_idsIssued_frame {s s' : XSt N T} (hfr : exec031_IdFrame s s')
    (hs : IdsIssued s) : IdsIssued s' := by
  intro f hf
  rcases hfr.2 f hf with ⟨g, hg, hid⟩ | ⟨-, hlt⟩
  · exact hid ▸ Nat.lt_of_lt_of_le (hs g hg) hfr.1
  · exact hlt

/-- Every reference step keeps `IdsIssued`. -/
theorem exec031_idsIssued_step {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : xstepW P C s l = some s') (hs : IdsIssued s) : IdsIssued s' :=
  exec031_idsIssued_frame (exec031_idFrame_step h) hs

/-- After a fail step of `i`: the identity `i` was handed out, and no firing in flight has it. -/
def exec031_Gone (i : Nat) (s : XSt N T) : Prop := i < s.nextId ∧ ∀ f ∈ s.fl, f.id ≠ i

omit [DecidableEq N] in
/-- The identity frame keeps `exec031_Gone i`: a firing after the step had its identity before
the step, or got a fresh one, above `i`. -/
theorem exec031_gone_frame {i : Nat} {s s' : XSt N T} (hfr : exec031_IdFrame s s')
    (hg : exec031_Gone i s) : exec031_Gone i s' := by
  refine ⟨Nat.lt_of_lt_of_le hg.1 hfr.1, fun f hf => ?_⟩
  rcases hfr.2 f hf with ⟨g, hgm, hid⟩ | ⟨hle, -⟩
  · exact hid ▸ hg.2 g hgm
  · intro he
    have := Nat.lt_of_lt_of_le hg.1 hle
    omega

omit [DecidableEq N] in
/-- A fail step of `i` from a state whose identities were handed out establishes
`exec031_Gone i`. -/
theorem exec031_gone_fail {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {i : Nat}
    (h : failStep P C s i = some s') (hs : IdsIssued s) : exec031_Gone i s' := by
  obtain ⟨f, hf, -, -, rfl⟩ := failStep_some h
  have hid : f.id = i := by simpa using List.find?_some hf
  refine ⟨hid ▸ hs f (List.mem_of_find?_eq_some hf), fun g hg => (exec031_mem_settle hg).2⟩

/-- After a failure of `i` is known (an error return of its action, or its fail step): the
identity `i` was handed out, and every firing in flight with identity `i` holds the error outcome.
After the fail step no firing `i` is left at all. -/
def exec031_Banned (i : Nat) (s : XSt N T) : Prop :=
  i < s.nextId ∧ ∀ f ∈ s.fl, f.id = i → f.out = some .err

omit [DecidableEq N] in
/-- A firing that is gone is banned. -/
theorem exec031_banned_of_gone {i : Nat} {s : XSt N T} (h : exec031_Gone i s) :
    exec031_Banned i s :=
  ⟨h.1, fun f hf hid => absurd hid (h.2 f hf)⟩

omit [DecidableEq N] in
/-- A banned firing has no open outcome, so no outside step of it is offered. -/
theorem exec031_banned_closed {s : XSt N T} {i : Nat} {f : Firing N T}
    (hb : exec031_Banned i s) (hf : s.fl.find? (·.id == i) = some f) : f.out ≠ none := by
  have := hb.2 f (List.mem_of_find?_eq_some hf) (by simpa using List.find?_some hf)
  rw [this]
  exact Option.some_ne_none _

omit [DecidableEq N] in
/-- Updating the record of another identity `j` keeps the error outcome of every firing `i`. -/
theorem exec031_banned_upd {s : XSt N T} {i j : Nat} {h : Firing N T → Firing N T}
    (hb : exec031_Banned i s) (hj : j ≠ i) (hh : ∀ g, (h g).id = g.id) :
    ∀ f ∈ updFiring s j h, f.id = i → f.out = some .err := by
  intro f hf hid
  unfold updFiring at hf
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
  by_cases hgj : g.id = j
  · have he : (g.id == j) = true := by simp [hgj]
    rw [he, if_pos rfl, hh, hgj] at hid
    exact absurd hid hj
  · have hne : (g.id == j) = false := by simpa using hgj
    rw [hne, if_neg Bool.false_ne_true] at hid ⊢
    exact hb.2 g hg hid

/-- Every reference step keeps the ban of `i`: an outside step of `i` needs an open outcome, an
outside step of another firing leaves firing `i` alone, a settle only drops firings, and a start
draws an identity above `i`. -/
theorem exec031_banned_step {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    {i : Nat} (h : xstepW P C s l = some s') (hb : exec031_Banned i s) :
    exec031_Banned i s' := by
  refine ⟨Nat.lt_of_lt_of_le hb.1 (exec031_idFrame_step h).1, ?_⟩
  have sub : ∀ {s'' : XSt N T}, (∀ f ∈ s''.fl, f ∈ s.fl) →
      ∀ f ∈ s''.fl, f.id = i → f.out = some .err := fun hs f hf hid => hb.2 f (hs f hf) hid
  have same : ∀ {s'' : XSt N T}, s''.fl = s.fl →
      ∀ f ∈ s''.fl, f.id = i → f.out = some .err := fun hfl => sub fun f hf => hfl ▸ hf
  have stl : ∀ {s'' : XSt N T} {j : Nat}, s''.fl = (settle s j).fl →
      ∀ f ∈ s''.fl, f.id = i → f.out = some .err :=
    fun hfl => sub fun f hf => (exec031_mem_settle (hfl ▸ hf)).1
  have opn : ∀ {j : Nat} {f : Firing N T}, s.fl.find? (·.id == j) = some f → f.out = none →
      j ≠ i := fun hf ho hj => exec031_banned_closed hb (hj ▸ hf) ho
  cases l with
  | delay δ => obtain rfl := xstepW_delay h; exact same rfl
  | write j p x =>
    obtain ⟨f, hf, ho, rfl⟩ := writeStep_some h
    exact exec031_banned_upd hb (opn hf ho) (fun _ => rfl)
  | flush j =>
    obtain ⟨f, hf, ho, -, -, ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ := flushStep_some h
    · exact exec031_banned_upd hb (opn hf ho) (fun _ => rfl)
    · exact exec031_banned_upd hb (opn hf ho) (fun _ => rfl)
  | ret j ok =>
    obtain ⟨f, hf, ho, rfl⟩ := retStep_some h
    exact exec031_banned_upd hb (opn hf ho) (fun _ => rfl)
  | expire j e =>
    obtain ⟨f, hf, ho, -, -, -, rfl⟩ := expireStep_some h
    exact exec031_banned_upd hb (opn hf ho) (fun _ => rfl)
  | request p x r =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := requestStep_some h
    · exact same rfl
    · exact same rfl
  | drain => obtain ⟨-, rfl⟩ := drainStep_some h; exact same rfl
  | close => obtain ⟨-, rfl⟩ := closeStep_some h; exact same rfl
  | terminateNow => obtain ⟨-, rfl⟩ := terminateStep_some h; exact same rfl
  | commit j => obtain ⟨-, -, -, -, -, -, -, rfl⟩ := commitStep_some h; exact stl rfl
  | fail j => obtain ⟨-, -, -, -, rfl⟩ := failStep_some h; exact stl rfl
  | tdeposit j => obtain ⟨-, -, -, -, -, -, rfl⟩ := tdepositStep_some h; exact stl rfl
  | endCompletions => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endCompletions h; exact same rfl
  | publish j => obtain ⟨-, -, -, -, -, rfl⟩ := publishStep_some h; exact same rfl
  | endPublications => obtain ⟨-, -, -, rfl⟩ := xstepW_endPublications h; exact same rfl
  | inject k => obtain ⟨-, -, -, -, -, -, -, rfl⟩ := injectStep_some h; exact same rfl
  | discard k => obtain ⟨-, -, -, -, -, -, -, rfl⟩ := discardStep_some h; exact same rfl
  | snapshot a => obtain ⟨-, -, -, rfl⟩ := snapshotStep_some h; exact same rfl
  | endEvents => obtain ⟨-, -, -, rfl⟩ := xstepW_endEvents h; exact same rfl
  | update => obtain ⟨-, -, rfl⟩ := xstepW_update h; exact same rfl
  | deadline ns => obtain ⟨-, -, -, rfl⟩ := xstepW_deadline h; exact same rfl
  | finish c =>
    cases c with
    | quiescent => obtain ⟨-, -, -, rfl⟩ := xstepW_finishQuiescent h; exact same rfl
    | closed => obtain ⟨-, -, -, -, rfl⟩ := xstepW_finishClosed h; exact same rfl
    | terminal => obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h; exact same rfl
    | stopped => obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h; exact same rfl
  | begin => obtain ⟨-, -, -, -, rfl⟩ := xstepW_begin h; exact same rfl
  | start n sy =>
    obtain ⟨-, -, -, -, -, -, -, -, -, rfl⟩ := startStep_some h
    intro f hf hid
    rcases List.mem_append.mp hf with hf | hf
    · exact hb.2 f hf hid
    · rw [List.mem_singleton] at hf
      subst hf
      have := hb.1
      simp only at hid
      omega
  | lose n => obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := loseStep_some h; exact same rfl
  | endPass => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endPass h; exact same rfl
  | park tmr => obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := parkStep_some h; exact same rfl
  | wake => obtain ⟨-, -, rfl⟩ := wakeStep_some h; exact same rfl

omit [DecidableEq N] in
/-- An error return of `i` from a state whose identities were handed out bans `i`: the firing
holds the error outcome. -/
theorem exec031_banned_errRet {s s' : XSt N T} {i : Nat} (h : retStep s i false = some s')
    (hs : IdsIssued s) : exec031_Banned i s' := by
  obtain ⟨f, hf, -, rfl⟩ := retStep_some h
  have hid : f.id = i := by simpa using List.find?_some hf
  refine ⟨hid ▸ hs f (List.mem_of_find?_eq_some hf), fun g' hg' hid' => ?_⟩
  unfold updFiring at hg'
  obtain ⟨g, -, rfl⟩ := List.mem_map.mp hg'
  by_cases hgi : g.id = i
  · simp [hgi]
  · have hne : (g.id == i) = false := by simpa using hgi
    rw [hne, if_neg Bool.false_ne_true] at hid'
    exact absurd hid' hgi

/-- A depositing settle step of `i` needs a firing `i` with a deposit outcome, so none is offered
while `i` is banned. -/
theorem exec031_deposit_banned {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    {i : Nat} (h : xstepW P C s l = some s') (hd : exec031_isDeposit i (s, l, s') = true)
    (hb : exec031_Banned i s) : False := by
  cases l with
  | commit j =>
    simp only [exec031_isDeposit, beq_iff_eq] at hd
    subst hd
    obtain ⟨f, e, hf, he, -⟩ := commitStep_some h
    have := hb.2 f (List.mem_of_find?_eq_some hf) (by simpa using List.find?_some hf)
    simp [he] at this
  | tdeposit j =>
    simp only [exec031_isDeposit, beq_iff_eq] at hd
    subst hd
    obtain ⟨f, e, hf, he, -⟩ := tdepositStep_some h
    have := hb.2 f (List.mem_of_find?_eq_some hf) (by simpa using List.find?_some hf)
    simp [he] at this
  | _ => simp [exec031_isDeposit] at hd

/-- The scan of line 2 over a run of the reference step at judgement points `P`: with the ban
memory `b`, every step is accepted, provided the identities were handed out and a set ban means
the firing is banned. -/
theorem exec031_scan {P : XPol N T} {C : Cfg N T} {i : Nat} :
    ∀ {s : XSt N T} {tr : List (XStep N T)} (b : Bool),
      XRun (fun C s l s' => xstepW P C s l = some s') C s tr → IdsIssued s →
      (b = true → exec031_Banned i s) →
      (afterNever (exec031_isFailed i) (exec031_isDeposit i)).scan b tr = true
  | _, [], _, _, _, _ => rfl
  | s, (s₁, l, s') :: rest, b, ⟨h1, hstep, hrest⟩, hs, hb => by
    simp only at h1
    subst h1
    have hs' := exec031_idsIssued_step hstep hs
    have hok : (b && exec031_isDeposit i (s₁, l, s')) = false := by
      cases b with
      | false => rfl
      | true =>
        cases hd : exec031_isDeposit i (s₁, l, s') with
        | false => rfl
        | true => exact (exec031_deposit_banned hstep hd (hb rfl)).elim
    have hnext : (b || exec031_isFailed i (s₁, l, s')) = true → exec031_Banned i s' := by
      intro hn
      cases hfl : exec031_isFailed i (s₁, l, s') with
      | true =>
        cases l with
        | fail j =>
          simp only [exec031_isFailed, beq_iff_eq] at hfl
          subst hfl
          exact exec031_banned_of_gone (exec031_gone_fail hstep hs)
        | ret j ok =>
          cases ok with
          | false =>
            simp only [exec031_isFailed, Bool.and_eq_true, beq_iff_eq] at hfl
            obtain ⟨rfl, -⟩ := hfl
            exact exec031_banned_errRet hstep hs
          | true => simp [exec031_isFailed] at hfl
        | _ => simp [exec031_isFailed] at hfl
      | false =>
        rw [hfl, Bool.or_false] at hn
        exact exec031_banned_step hstep (hb hn)
    show (!(b && exec031_isDeposit i (s₁, l, s')) &&
      (afterNever (exec031_isFailed i) (exec031_isDeposit i)).scan
        (b || exec031_isFailed i (s₁, l, s')) rest) = true
    rw [hok, exec031_scan _ hrest hs' hnext]
    rfl

/-- A report step of the reference (a return or an expiry) changes neither the marking nor the
publication queue: it only records the outcome. -/
theorem exec031_report_keeps {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    {i : Nat} (h : xstepW P C s l = some s') (hr : exec031_isReport i (s, l, s') = true) :
    s'.M = s.M ∧ s'.pq = s.pq := by
  cases l with
  | ret j ok => obtain ⟨-, -, -, rfl⟩ := retStep_some h; exact ⟨rfl, rfl⟩
  | expire j e => obtain ⟨-, -, -, -, -, -, rfl⟩ := expireStep_some h; exact ⟨rfl, rfl⟩
  | _ => simp [exec031_isReport] at hr

omit [DecidableEq N] in
/-- Every step of a run is a step of its executor. -/
theorem exec031_run_mem {R : XRel N T} {C : Cfg N T} :
    ∀ {s : XSt N T} {tr : List (XStep N T)}, XRun R C s tr →
      ∀ st ∈ tr, R C st.1 st.2.1 st.2.2
  | _, [], _, st, hst => by simp at hst
  | _, _ :: _, ⟨_, h, hr⟩, st, hst => by
    rcases List.mem_cons.mp hst with rfl | hst
    · exact h
    · exact exec031_run_mem hr st hst

/-- The executor of any judgement points `P` satisfies the lines of EXEC-031: its fail step is a
`settle`, which keeps the marking and the publication queue (`failStep_some`); an error return or
a fail of `i` bans `i` for good (`exec031_scan`); and its report steps only record outcomes
(`exec031_report_keeps`). -/
theorem exec031_xstepW (P : XPol N T) :
    EXEC_031 (fun C s l s' => xstepW P C s l = some s') := by
  intro C i
  refine ⟨fun s s' h => ?_, fun s0 tr hs hr => ?_, fun s0 tr _ hr _ st hst hrep => ?_⟩
  · obtain ⟨f, -, -, -, rfl⟩ := failStep_some h
    exact ⟨rfl, rfl⟩
  · exact exec031_scan false hr hs (fun h => absurd h Bool.false_ne_true)
  · obtain ⟨a, l, b⟩ := st
    exact exec031_report_keeps (exec031_run_mem hr _ hst) hrep

end Reference

/-- ✓ The reference executor satisfies EXEC-031 (`exec031_xstepW` at `refXPol`). -/
@[evidence holds EXEC_031]
theorem EXEC_031_reference {N T : Type} [DecidableEq N] :
    EXEC_031 (RefExec (N := N) (T := T)) :=
  exec031_xstepW refXPol

/-! ### Decided runs of a step function -/

section Runs

variable {N T : Type}

/-- The trace of a label run of step function `g`, if every label is a step. -/
def exec031_trace (g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)) (C : Cfg N T) :
    XSt N T → List (XLbl N T) → Option (List (XStep N T))
  | _, [] => some []
  | s, l :: ls => (g C s l).bind fun s' => (exec031_trace g C s' ls).map ((s, l, s') :: ·)

/-- A trace `exec031_trace` builds is a run of the graph of `g`. -/
theorem exec031_trace_run {g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)} {C : Cfg N T} :
    ∀ {s : XSt N T} {ls : List (XLbl N T)} {tr : List (XStep N T)},
      exec031_trace g C s ls = some tr → XRun (fun C s l s' => g C s l = some s') C s tr
  | s, [], tr, h => by cases h; trivial
  | s, l :: ls, tr, h => by
    simp only [exec031_trace] at h
    cases hs : g C s l with
    | none => simp [hs] at h
    | some s' =>
      simp only [hs, Option.bind_some] at h
      cases ht : exec031_trace g C s' ls with
      | none => simp [ht] at h
      | some tr' =>
        simp only [ht, Option.map_some, Option.some.injEq] at h
        subst h
        exact ⟨rfl, hs, exec031_trace_run ht⟩

/-- Read a decided check `p` off the trace of a label run: the run exists and `p` holds of it. -/
theorem exec031_trace_of_check {g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)}
    {C : Cfg N T} {s : XSt N T} {ls : List (XLbl N T)} {p : List (XStep N T) → Bool}
    (h : (exec031_trace g C s ls).map p = some true) :
    ∃ tr, XRun (fun C s l s' => g C s l = some s') C s tr ∧ p tr = true := by
  cases ht : exec031_trace g C s ls with
  | none => simp [ht] at h
  | some tr =>
    simp only [ht, Option.map_some, Option.some.injEq] at h
    exact ⟨tr, exec031_trace_run ht, h⟩

/-- `after T, never B` is the scan of its watch from `false`. -/
theorem exec031_afterNever_iff {trig bad : XStep N T → Bool} {tr : List (XStep N T)} :
    (after trig, never bad) tr ↔ (afterNever trig bad).scan false tr = true := Iff.rfl

/-- A run of the graph of `g` from a state whose identities were handed out, on which a deposit
of `i` follows an error return or a fail of `i`, refutes EXEC-031 (line 2) for that executor. -/
theorem exec031_refute [DecidableEq N] {g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)}
    {C : Cfg N T} {s : XSt N T} {ls : List (XLbl N T)} {i : Nat} (hs : IdsIssued s)
    (h : (exec031_trace g C s ls).map
      (fun tr => !(afterNever (exec031_isFailed i) (exec031_isDeposit i)).scan false tr) =
        some true) :
    ¬ EXEC_031 (fun C s l s' => g C s l = some s') := by
  intro hR
  obtain ⟨tr, hr, hp⟩ := exec031_trace_of_check h
  have := exec031_afterNever_iff.mp ((hR C i).2.1 s tr hs hr)
  simp [this] at hp

/-- A run of the graph of `g` from a state whose identities were handed out, on which firing `i`
fails and one of its report steps changes the queue of place `p`, refutes EXEC-031 (line 3). -/
theorem exec031_refuteReport [DecidableEq N] [DecidableEq T]
    {g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)} {C : Cfg N T} {s : XSt N T}
    {ls : List (XLbl N T)} {i : Nat} {p : N} (hs : IdsIssued s)
    (h : (exec031_trace g C s ls).map
      (fun tr => tr.any (exec031_isFailed i) &&
        tr.any (fun st => exec031_isReport i st && (st.2.2.M p != st.1.M p))) = some true) :
    ¬ EXEC_031 (fun C s l s' => g C s l = some s') := by
  intro hR
  obtain ⟨tr, hr, hp⟩ := exec031_trace_of_check h
  rw [Bool.and_eq_true] at hp
  obtain ⟨hf, hrep⟩ := hp
  obtain ⟨st, hst, hst'⟩ := List.any_eq_true.mp hrep
  rw [Bool.and_eq_true, bne_iff_ne] at hst'
  exact hst'.2 (congrFun ((hR C i).2.2 s tr hs hr hf st hst hst'.1).1 p)

end Runs

/-! ### Examples

One transition `t` takes one token from place `0` and has output spec `Out.place 1`; the
validator is the reference validator of IO-015, the join-relay check accepts everything. Place
`0` holds the tokens `7` and `8`. -/

/-- The transition `t`: one token from `0`, output to `1`. -/
def exec031_t : Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 1) }

/-- The configuration of the examples. -/
def exec031_cfg : Cfg Nat Nat :=
  { X := { net := { places := [0, 1], transitions := [exec031_t] },
           timing := fun _ => .immediate, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [], reentrant := false,
    validate := cfgValidate ioRefValidate,
    relay := fun _ _ _ => true,
    timeoutOut := fun _ _ _ => false,
    res := 0 }

/-- The initial marking: the tokens `7` and `8` in place `0`. -/
def exec031_m0 : QMarking Nat Nat := fun p => if p = 0 then [7, 8] else []

/-- The initial state. -/
def exec031_s0 : XSt Nat Nat := xinit exec031_m0 0

/-- Nothing is in flight at the start. -/
theorem exec031_s0_issued : IdsIssued exec031_s0 := fun f hf => by
  simp [exec031_s0, xinit] at hf

/-- One cycle up to an asynchronous start of `t`. -/
def exec031_cycle : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin, .start "t" false]

/-- The first firing (identity `0`, consuming `7`) fails: its action returns an error, and the
fail step settles it. -/
def exec031_failRun : List (XLbl Nat Nat) := exec031_cycle ++ [.ret 0 false, .endPass, .fail 0]

/-- The consumed tokens of firing `f`, as an emission back into their input places. -/
def exec031_restore {N T : Type} (f : Firing N T) : List (N × T) :=
  (inPlaces f.t).flatMap fun p => (f.deliv.inputs p).map ((p, ·))

/-! ### Violation: a fail step that restores the consumed tokens -/

/-- A step function whose `fail` step puts the consumed tokens back at the head of their places
(a rollback at the fail step); otherwise the reference. -/
def exec031_failRestoresStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .fail i => (xstep C s (.fail i)).bind fun s₁ => (s.fl.find? (·.id == i)).map fun f =>
      { s₁ with M := fun p => f.deliv.inputs p ++ s₁.M p }
  | l => xstep C s l

/-- ✗ A rollback at the fail step violates EXEC-031 (line 1, the marking half): the first firing
fails, and its fail step puts the consumed `7` back into place `0`. -/
@[evidence forbids EXEC_031]
theorem EXEC_031_forbids_failRestores :
    ¬ EXEC_031 (N := Nat) (T := Nat) (fun C s l s' => exec031_failRestoresStep C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec031_failRestoresStep (C := exec031_cfg)
    (o := xrun exec031_cfg exec031_s0 (exec031_cycle ++ [.ret 0 false, .endPass]))
    (l := .fail 0) (p := fun s s' => s'.M 0 != s.M 0) (by decide)
  have := ((h exec031_cfg 0).1 s s' hs).1
  simp [this] at hp

/-! ### Violation: a fail step that queues the rollback as a publication -/

/-- A step function whose `fail` step settles the failure as the reference does and queues the
consumed tokens as one more publication of the firing, which the publications phase of the next
cycle lands (a compensation sent down the flush channel); otherwise the reference. -/
def exec031_failQueuesStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .fail i => (xstep C s (.fail i)).bind fun s₁ => (s.fl.find? (·.id == i)).map fun f =>
      { s₁ with pq := s₁.pq ++ [(i, exec031_restore f)] }
  | l => xstep C s l

/-- ✗ A rollback queued at the fail step violates EXEC-031 (line 1, the publication-queue half):
the first firing fails, and its fail step queues a publication. -/
@[evidence forbids EXEC_031]
theorem EXEC_031_forbids_failQueues :
    ¬ EXEC_031 (N := Nat) (T := Nat) (fun C s l s' => exec031_failQueuesStep C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec031_failQueuesStep (C := exec031_cfg)
    (o := xrun exec031_cfg exec031_s0 (exec031_cycle ++ [.ret 0 false, .endPass]))
    (l := .fail 0) (p := fun s s' => s'.pq.length != s.pq.length) (by decide)
  have := ((h exec031_cfg 0).1 s s' hs).2
  simp [this] at hp

/-- The publication-queue half of line 1 is load-bearing: on the queued-rollback run the fail
step keeps the marking, no commit or tdeposit of the failed firing follows (line 2 holds), and
the publish step of the next cycle puts the consumed `7` back at the tail of place `0`. -/
theorem exec031_failQueues_markingOnly :
    ∃ tr, XRun (fun C s l s' => exec031_failQueuesStep C s l = some s') exec031_cfg
        exec031_s0 tr ∧
      tr.all (fun st => !exec031_isFail 0 st || st.2.2.M 0 == st.1.M 0) = true ∧
      (after (exec031_isFailed 0), never (exec031_isDeposit 0)) tr ∧
      (XRun.last exec031_s0 tr).M 0 = [8, 7] := by
  obtain ⟨tr, hr, hp⟩ := exec031_trace_of_check (g := exec031_failQueuesStep)
    (C := exec031_cfg) (s := exec031_s0) (ls := exec031_failRun ++ [.endCompletions, .publish 0])
    (p := fun tr => tr.all (fun st => !exec031_isFail 0 st || st.2.2.M 0 == st.1.M 0) &&
      (afterNever (exec031_isFailed 0) (exec031_isDeposit 0)).scan false tr &&
      (XRun.last exec031_s0 tr).M 0 == [8, 7])
    (by decide)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨tr, hr, hp.1.1, exec031_afterNever_iff.mpr hp.1.2, hp.2⟩

/-! ### Violation: a rollback when the action reports its error -/

/-- A step function whose error return `ret i false` puts firing `i`'s consumed tokens back at
the head of their places (a compensation in the action's completion callback, before the settle);
otherwise the reference, whose later fail step leaves the marking alone. -/
def exec031_restoreAtErrorStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .ret i false => (xstep C s (.ret i false)).bind fun s₁ =>
      (s.fl.find? (·.id == i)).map fun f => { s₁ with M := fun p => f.deliv.inputs p ++ s₁.M p }
  | l => xstep C s l

/-- ✗ A rollback at the error return violates EXEC-031 (line 3): the first firing's action
returns an error, that return step puts the consumed `7` back into place `0`, and the firing then
fails. -/
@[evidence forbids EXEC_031]
theorem EXEC_031_forbids_restoreAtError :
    ¬ EXEC_031 (N := Nat) (T := Nat)
      (fun C s l s' => exec031_restoreAtErrorStep C s l = some s') :=
  exec031_refuteReport (C := exec031_cfg) (i := 0) (p := 0) exec031_s0_issued
    (ls := exec031_failRun) (by decide)

/-- Line 3 is load-bearing: on the run of the rollback at the error return, the fail step keeps
the marking and the publication queue, no commit or tdeposit of the failed firing follows, and
at the end the consumed `7` is back at the head of place `0`. -/
theorem exec031_restoreAtError_onlyLine3 :
    ∃ tr, XRun (fun C s l s' => exec031_restoreAtErrorStep C s l = some s') exec031_cfg
        exec031_s0 tr ∧
      tr.all (fun st => !exec031_isFail 0 st ||
        (st.2.2.M 0 == st.1.M 0 && st.2.2.M 1 == st.1.M 1 &&
          st.2.2.pq.length == st.1.pq.length)) = true ∧
      (after (exec031_isFailed 0), never (exec031_isDeposit 0)) tr ∧
      (XRun.last exec031_s0 tr).M 0 = [7, 8] := by
  obtain ⟨tr, hr, hp⟩ := exec031_trace_of_check (g := exec031_restoreAtErrorStep)
    (C := exec031_cfg) (s := exec031_s0) (ls := exec031_failRun)
    (p := fun tr => tr.all (fun st => !exec031_isFail 0 st ||
        (st.2.2.M 0 == st.1.M 0 && st.2.2.M 1 == st.1.M 1 &&
          st.2.2.pq.length == st.1.pq.length)) &&
      (afterNever (exec031_isFailed 0) (exec031_isDeposit 0)).scan false tr &&
      (XRun.last exec031_s0 tr).M 0 == [7, 8])
    (by decide)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨tr, hr, hp.1.1, exec031_afterNever_iff.mpr hp.1.2, hp.2⟩

/-! ### Violation: a retry of the failed action -/

/-- A step function whose `fail` step settles the failure and puts the firing back in flight
with its outcome cleared, so its action runs again on the tokens it consumed; otherwise the
reference. -/
def exec031_retryStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .fail i => (xstep C s (.fail i)).bind fun s₁ => (s.fl.find? (·.id == i)).map fun f =>
      { s₁ with fl := s₁.fl ++ [{ f with buf := [], out := none }] }
  | l => xstep C s l

/-- ✗ A retry of the failed action violates EXEC-031 (line 2, the commit half): the first firing
fails, its action runs again, writes `9` to `1`, returns, and its completion is committed. -/
@[evidence forbids EXEC_031]
theorem EXEC_031_forbids_retry :
    ¬ EXEC_031 (N := Nat) (T := Nat) (fun C s l s' => exec031_retryStep C s l = some s') :=
  exec031_refute (C := exec031_cfg) (i := 0) exec031_s0_issued
    (ls := exec031_failRun ++ [.write 0 1 9, .ret 0 true, .commit 0]) (by decide)

/-! ### Violation: a rollback deposited after the fail step -/

/-- A step function whose `fail` step settles the failure and then queues a compensation: the
firing comes back with the consumed tokens as a timeout outcome, which a later `tdeposit` puts
back; otherwise the reference. -/
def exec031_rollbackLaterStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .fail i => (xstep C s (.fail i)).bind fun s₁ => (s.fl.find? (·.id == i)).map fun f =>
      { s₁ with fl := s₁.fl ++ [{ f with out := some (.timedOut (exec031_restore f)) }],
                cq := s₁.cq ++ [i] }
  | l => xstep C s l

/-- The labels of the rollback run: the first firing fails, then its compensation is deposited. -/
def exec031_rollbackRun : List (XLbl Nat Nat) := exec031_failRun ++ [.tdeposit 0]

/-- ✗ A rollback deposited after the fail step violates EXEC-031 (line 2, the tdeposit half): the
first firing fails, its fail step leaves the marking as it is, and a later `tdeposit 0` puts the
consumed `7` back into place `0`. -/
@[evidence forbids EXEC_031]
theorem EXEC_031_forbids_rollbackLater :
    ¬ EXEC_031 (N := Nat) (T := Nat)
      (fun C s l s' => exec031_rollbackLaterStep C s l = some s') :=
  exec031_refute (C := exec031_cfg) (i := 0) exec031_s0_issued (ls := exec031_rollbackRun)
    (by decide)

/-- A commit step of firing `i`. -/
def exec031_isCommit {N T : Type} (i : Nat) : XStep N T → Bool
  | (_, .commit j, _) => j == i
  | _ => false

/-- The tdeposit half of line 2 is load-bearing: the rollback run passes a line that bans only
commit steps after the failure, deposits the consumed `7` back at the tail of place `0`, and
fails line 2. -/
theorem exec031_rollbackLater_commitOnly :
    ∃ tr, XRun (fun C s l s' => exec031_rollbackLaterStep C s l = some s') exec031_cfg
        exec031_s0 tr ∧
      (after (exec031_isFailed 0), never (exec031_isCommit 0)) tr ∧
      ¬ (after (exec031_isFailed 0), never (exec031_isDeposit 0)) tr ∧
      (XRun.last exec031_s0 tr).M 0 = [8, 7] := by
  obtain ⟨tr, hr, hp⟩ := exec031_trace_of_check (g := exec031_rollbackLaterStep)
    (C := exec031_cfg) (s := exec031_s0) (ls := exec031_rollbackRun)
    (p := fun tr => (afterNever (exec031_isFailed 0) (exec031_isCommit 0)).scan false tr &&
      !(afterNever (exec031_isFailed 0) (exec031_isDeposit 0)).scan false tr &&
      (XRun.last exec031_s0 tr).M 0 == [8, 7])
    (by decide)
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hp
  refine ⟨tr, hr, exec031_afterNever_iff.mpr hp.1.1, fun h => ?_, hp.2⟩
  simp [exec031_afterNever_iff.mp h] at hp

/-! ### Violation: an action error turned into a timeout outcome -/

/-- A step function whose error return `ret i false` records a timeout outcome holding the
consumed tokens instead of the error (a handler that maps every rejection of the raced action to
the timeout branch, with a compensation as the outcome); otherwise the reference, whose
`tdeposit` then deposits it. No fail step of the firing ever happens. -/
def exec031_errAsTimeoutStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .ret i false => (xstep C s (.ret i false)).map fun s₁ =>
      { s₁ with fl := updFiring s₁ i fun g => { g with out := some (.timedOut (exec031_restore g)) } }
  | l => xstep C s l

/-- The labels of the error-as-timeout run: the first firing's action returns an error, and its
outcome is then deposited as a timeout outcome. -/
def exec031_errAsTimeoutRun : List (XLbl Nat Nat) :=
  exec031_cycle ++ [.ret 0 false, .endPass, .tdeposit 0]

/-- ✗ An action error turned into a timeout outcome violates EXEC-031 (line 2, the error-return
trigger): the first firing's action returns an error, and a later `tdeposit 0` puts the consumed
`7` back into place `0`. -/
@[evidence forbids EXEC_031]
theorem EXEC_031_forbids_errAsTimeout :
    ¬ EXEC_031 (N := Nat) (T := Nat)
      (fun C s l s' => exec031_errAsTimeoutStep C s l = some s') :=
  exec031_refute (C := exec031_cfg) (i := 0) exec031_s0_issued (ls := exec031_errAsTimeoutRun)
    (by decide)

/-- The error-return trigger of line 2 is load-bearing: the error-as-timeout run has no fail
step, so a line triggered by fail steps only accepts it, while the consumed `7` is back at the
tail of place `0`. -/
theorem exec031_errAsTimeout_failOnly :
    ∃ tr, XRun (fun C s l s' => exec031_errAsTimeoutStep C s l = some s') exec031_cfg
        exec031_s0 tr ∧
      tr.any (exec031_isFail 0) = false ∧
      (after (exec031_isFail 0), never (exec031_isDeposit 0)) tr ∧
      ¬ (after (exec031_isFailed 0), never (exec031_isDeposit 0)) tr ∧
      (XRun.last exec031_s0 tr).M 0 = [8, 7] := by
  obtain ⟨tr, hr, hp⟩ := exec031_trace_of_check (g := exec031_errAsTimeoutStep)
    (C := exec031_cfg) (s := exec031_s0) (ls := exec031_errAsTimeoutRun)
    (p := fun tr => !tr.any (exec031_isFail 0) &&
      (afterNever (exec031_isFail 0) (exec031_isDeposit 0)).scan false tr &&
      !(afterNever (exec031_isFailed 0) (exec031_isDeposit 0)).scan false tr &&
      (XRun.last exec031_s0 tr).M 0 == [8, 7])
    (by decide)
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hp
  refine ⟨tr, hr, hp.1.1.1, exec031_afterNever_iff.mpr hp.1.1.2, fun h => ?_, hp.2⟩
  simp [exec031_afterNever_iff.mp h] at hp

/-! ### The premise of lines 2 and 3 -/

/-- A state in which firing `0` (an error outcome, queued) is in flight although the supply has
not handed out the identity `0` yet. -/
def exec031_badSupply : XSt Nat Nat :=
  { exec031_s0 with
    fl := [⟨0, exec031_t, ⟨fun _ => [], fun _ => []⟩, 0, false, [], [], false, some .err⟩],
    cq := [0] }

/-- The premise of line 2 is load-bearing: from a state whose firing in flight has an identity
the supply has not handed out, the reference fails that firing, starts a new firing with the same
identity and commits it. -/
theorem exec031_needs_idsIssued :
    ¬ IdsIssued exec031_badSupply ∧
      ∃ tr, XRun RefExec exec031_cfg exec031_badSupply tr ∧
        ¬ (after (exec031_isFailed 0), never (exec031_isDeposit 0)) tr := by
  refine ⟨fun h => absurd (h _ (List.mem_singleton_self _)) (by decide), ?_⟩
  obtain ⟨tr, hr, hp⟩ := exec031_trace_of_check (g := xstep) (C := exec031_cfg)
    (s := exec031_badSupply)
    (ls := [.fail 0] ++ exec031_cycle ++ [.write 0 1 9, .ret 0 true, .endPass, .commit 0])
    (p := fun tr => !(afterNever (exec031_isFailed 0) (exec031_isDeposit 0)).scan false tr)
    (by decide)
  refine ⟨tr, hr, fun h => ?_⟩
  simp [exec031_afterNever_iff.mp h] at hp

/-! ### Every line exercised -/

/-- The labels of the example run: the first firing consumes `7` and fails; the second consumes
`8`, writes `9` to `1` and is committed; the run then finishes quiescent. -/
def exec031_run : List (XLbl Nat Nat) :=
  exec031_failRun ++ exec031_cycle ++ [.write 1 1 9, .ret 1 true, .endPass, .commit 1] ++
    [.endCompletions, .endPublications, .endEvents, .update, .deadline [], .finish .quiescent]

/-- A normal return of firing `i`'s action. -/
def exec031_isOkRet {N T : Type} (i : Nat) : XStep N T → Bool
  | (_, .ret j true, _) => j == i
  | _ => false

/-- The labels of the validation run: the first firing consumes `7`, its action writes `9` to
place `0` (outside its output spec `Out.place 1`) and returns normally, and output validation
fails it; the second consumes `8`, writes `5` to `1` and is committed; the run then finishes
quiescent. -/
def exec031_valRun : List (XLbl Nat Nat) :=
  exec031_cycle ++ [.write 0 0 9, .ret 0 true, .endPass, .fail 0] ++
    exec031_cycle ++ [.write 1 1 5, .ret 1 true, .endPass, .commit 1] ++
    [.endCompletions, .endPublications, .endEvents, .update, .deadline [], .finish .quiescent]

/-- Every line of EXEC-031 is exercised by the reference. On a run from the initial state (whose
identities were handed out), the first firing consumes `7`, its action returns an error (a
report, and the trigger of lines 2 and 3) and the fail step settles it (the trigger of line 1);
the second firing's completion is committed (a deposit, of another firing); the run finishes, and
the token `7` is in no place of the net (AC1, the test derivation). The fail step of the first
firing exists. On a second run the first firing returns normally with a token for a place outside
its output spec, output validation fails it, and at the finish neither `7` nor the produced `9`
is in any place: the failure the third quoted sentence adds settles the same way. -/
@[evidence nonvacuous EXEC_031]
theorem EXEC_031_nonvacuous :
    (∃ tr, XRun RefExec exec031_cfg exec031_s0 tr ∧
      tr.any (exec031_isFail 0) = true ∧ tr.any (exec031_isFailed 0) = true ∧
      tr.any (exec031_isReport 0) = true ∧ tr.any (exec031_isDeposit 1) = true ∧
      isExecPhase (XRun.last exec031_s0 tr).phase = false ∧
      ∀ p ∈ exec031_cfg.X.net.places, 7 ∉ (XRun.last exec031_s0 tr).M p) ∧
    (∃ s s', RefExec exec031_cfg s (.fail 0) s') ∧
    (∃ tr, XRun RefExec exec031_cfg exec031_s0 tr ∧
      tr.any (exec031_isOkRet 0) = true ∧ tr.any (exec031_isFail 0) = true ∧
      tr.any (exec031_isDeposit 1) = true ∧
      isExecPhase (XRun.last exec031_s0 tr).phase = false ∧
      ∀ p ∈ exec031_cfg.X.net.places,
        7 ∉ (XRun.last exec031_s0 tr).M p ∧ 9 ∉ (XRun.last exec031_s0 tr).M p) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨tr, hr, hp⟩ := exec031_trace_of_check (g := xstep) (C := exec031_cfg)
      (s := exec031_s0) (ls := exec031_run)
      (p := fun tr => tr.any (exec031_isFail 0) && tr.any (exec031_isFailed 0) &&
        tr.any (exec031_isReport 0) && tr.any (exec031_isDeposit 1) &&
        !isExecPhase (XRun.last exec031_s0 tr).phase &&
        exec031_cfg.X.net.places.all fun p => !((XRun.last exec031_s0 tr).M p).contains 7)
      (by decide)
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hp
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hp
    refine ⟨tr, hr, h1, h2, h3, h4, h5, fun p hp hm => ?_⟩
    have := h6 p hp
    simp [hm] at this
  · obtain ⟨s, s', -, hs, -⟩ := step_of_check xstep (C := exec031_cfg)
      (o := xrun exec031_cfg exec031_s0 (exec031_cycle ++ [.ret 0 false, .endPass]))
      (l := .fail 0) (p := fun _ _ => true) (by decide)
    exact ⟨s, s', hs⟩
  · obtain ⟨tr, hr, hp⟩ := exec031_trace_of_check (g := xstep) (C := exec031_cfg)
      (s := exec031_s0) (ls := exec031_valRun)
      (p := fun tr => tr.any (exec031_isOkRet 0) && tr.any (exec031_isFail 0) &&
        tr.any (exec031_isDeposit 1) &&
        !isExecPhase (XRun.last exec031_s0 tr).phase &&
        exec031_cfg.X.net.places.all fun p =>
          !((XRun.last exec031_s0 tr).M p).contains 7 &&
            !((XRun.last exec031_s0 tr).M p).contains 9)
      (by decide)
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hp
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hp
    refine ⟨tr, hr, h1, h2, h3, h4, fun p hp => ⟨fun hm => ?_, fun hm => ?_⟩⟩
    · have := h5 p hp
      simp [hm] at this
    · have := h5 p hp
      simp [hm] at this

/-! ### A late error return after the expiry -/

/-- The step is an error return of firing `i`'s action (`ret i false`), whatever the firing's
state. -/
def exec031_isErrRet {N T : Type} (i : Nat) : XStep N T → Bool
  | (_, .ret j false, _) => j == i
  | _ => false

/-- The reference, plus a late error return of an action whose firing already ended, offered as
a step that changes nothing ([EXEC-022]: a late return may still be a step, provided it changes
neither the marking, the queue, nor how the firing ended). -/
def exec031_lateRetStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .ret i false =>
    match s.fl.find? (·.id == i) with
    | some f => if f.out.isSome then some s else xstep C s (.ret i false)
    | none => xstep C s (.ret i false)
  | l => xstep C s l

/-- ✓ EXEC-031 allows a late error return after the expiry: on the example of EXEC-022 the
budget of firing `0` runs out (its timeout outcome forwards `7` and `8` to place `2`), its
abandoned action then returns an error, as a step that changes nothing, and the timeout outcome
is deposited. The error return is not taken while the firing is open, so it does not fail the
firing, and line 2 accepts the run. -/
@[evidence allows EXEC_031]
theorem EXEC_031_allows_lateErrorAfterExpiry :
    ∃ tr, XRun (fun C s l s' => exec031_lateRetStep C s l = some s') exec022_C exec022_s0 tr ∧
      tr.any (exec031_isErrRet 0) = true ∧ tr.any (exec031_isDeposit 0) = true ∧
      tr.any (exec031_isFailed 0) = false ∧
      (after (exec031_isFailed 0), never (exec031_isDeposit 0)) tr := by
  obtain ⟨tr, hr, hp⟩ := exec031_trace_of_check (g := exec031_lateRetStep) (C := exec022_C)
    (s := exec022_s0) (ls := exec022_expired ++ [.ret 0 false, .endPass, .tdeposit 0])
    (p := fun tr => tr.any (exec031_isErrRet 0) && tr.any (exec031_isDeposit 0) &&
      !tr.any (exec031_isFailed 0) &&
      (afterNever (exec031_isFailed 0) (exec031_isDeposit 0)).scan false tr)
    (by decide)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hp
  exact ⟨tr, hr, h1, h2, h3, exec031_afterNever_iff.mpr h4⟩

end Libpetri.Spec
