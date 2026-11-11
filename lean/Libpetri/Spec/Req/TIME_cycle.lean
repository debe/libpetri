import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Exec

set_option linter.missingDocs true

/-!
# TIME-010, TIME-012, TIME-013, TIME-015 at the grain of the executor (`spec/03-timing.md`)

The four companion blocks of ruling D33 (a) (design NR-1): second blocks with the same IDs as
the Phase 1 blocks `TIME_010`, `TIME_012`, `TIME_013` and `TIME_015`, stated over the executor
model (`RefExec`, `Reference/Exec.lean`) instead of the atomic timed step. The Phase 1 blocks
keep their statements and sign-offs; each companion states the lines those blocks deferred to the
cycle relation ("Phase 2" in their assumes):

* `TIME_010_cycle`: a transition is armed and stamped only by the enablement update, with the
  reading that update takes, not the reading of the cycle in which the arming firing started and
  not the moment an action completed; the update takes the present reading, the deadline step
  judges at that reading or at a later one of its own, and no other step takes a reading (ruling
  D61 (c)).
* `TIME_012_cycle`: a start in the firing pass judges the other armed transitions on its live
  intermediate marking (ruling D7), the next update restamps the ones that lost their clock, ends
  their restart, and keeps the others; no other step undoes the restart; a transition the pass
  drops loses its clock.
* `TIME_013_cycle`: the deadline step reaps every expired transition at its reading and nothing
  else; an update leaves a reaped transition reaped, and only a write of one of its arc places, by
  a firing or by an injected token, ends its reaped state (design R9).
* `TIME_015_cycle`: the host reading never goes back, and a completed wait is followed by an update
  before any start.

Each requirement is a predicate over an abstract executor `R : XRel N T` (glossary
`GlossaryExec.lean`). The evidence checks each one against the reference executor and against one
executor per load-bearing line that gets that line wrong, on small decided runs.

The glossary term Write, at the grain of the executor, is `cycWrites` below: it is where the
injection clause of the glossary's Write, which the Phase 1 step leaves out (`Writes`,
`GlossaryTime.lean`), is stated.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Novel.TimedScg (Timing)

/-! ## Vocabulary -/

section Vocabulary

variable {N T : Type}

/-- The step is a `wake`: the wait of step 6 completed. -/
def tcIsWake : XStep N T → Bool
  | (_, .wake, _) => true
  | _ => false

end Vocabulary

/-! ## What the reference steps do to clock statuses and readings -/

section Steps

variable {N T : Type} [DecidableEq N]

/-- `unreap` turns a reaped status off or keeps it, and keeps every other status: it never
changes the stamp a status holds. -/
theorem tc_stampOf_unreap (C : Cfg N T) (ps : List N) (st : String → Status) (n : String) :
    stampOf (unreap C ps st n) = stampOf (st n) := by
  unfold unreap
  cases h : st n <;> cases hf : findT C n <;> simp only []
  split <;> rfl

/-- A write of no place changes no status. -/
theorem tc_unreap_nil (C : Cfg N T) (st : String → Status) : unreap C [] st = st := by
  funext n
  unfold unreap
  cases h : st n <;> cases hf : findT C n <;> simp

/-- `unreap` keeps an armed status. -/
theorem tc_unreap_armed {C : Cfg N T} {ps : List N} {st : String → Status} {n : String}
    {k : Nat} {r : Bool} (h : st n = .armed k r) : unreap C ps st n = .armed k r := by
  unfold unreap
  rw [h]

/-- A write of one of its arc places turns a reaped name off. -/
theorem tc_unreap_write {C : Cfg N T} {ps : List N} {st : String → Status} {n : String}
    {u : Trans N} {p : N} (h : st n = .reaped) (hf : findT C n = some u) (hp : p ∈ arcPlaces u)
    (hps : p ∈ ps) : unreap C ps st n = .off := by
  have ha : (arcPlaces u).any (fun p => decide (p ∈ ps)) = true :=
    List.any_eq_true.mpr ⟨p, hp, by simpa using hps⟩
  unfold unreap
  rw [h, hf]
  simp [ha]

/-- A reaped name leaves the reaped status under `unreap` only through a write of one of its arc
places. -/
theorem tc_unreap_left {C : Cfg N T} {ps : List N} {st : String → Status} {n : String}
    (h : st n = .reaped) (hne : unreap C ps st n ≠ .reaped) :
    ∃ u, findT C n = some u ∧ ∃ p ∈ arcPlaces u, p ∈ ps := by
  unfold unreap at hne
  rw [h] at hne
  cases hf : findT C n with
  | none => simp [hf] at hne
  | some u =>
    simp only [hf] at hne
    by_cases ha : (arcPlaces u).any (fun p => decide (p ∈ ps)) = true
    · obtain ⟨p, hp, hps⟩ := List.any_eq_true.mp ha
      exact ⟨u, rfl, p, hp, by simpa using hps⟩
    · simp [ha] at hne

/-- A start of `t` turns `t`'s own name off. -/
theorem tc_afterStart_self {P : XPol N T} {C : Cfg N T} {s : XSt N T} {t : Trans N} :
    afterStart P C s t t.core.name = .off := by
  simp [afterStart]

/-- A start of `t` keeps the stamp of every other armed name, and sets its restart flag when its
transition is not enabled in the marking the start judges (`P.restartOn`). -/
theorem tc_afterStart_armed {P : XPol N T} {C : Cfg N T} {s : XSt N T} {t : Trans N}
    {m : String} {u : Trans N} {k : Nat} {r : Bool} (hm : m ≠ t.core.name)
    (hu : findT C m = some u) (hs : s.st m = .armed k r) :
    afterStart P C s t m = .armed k (r || !enabledNA (qCount (P.restartOn s t)) u.core) := by
  unfold afterStart
  rw [if_neg hm, hs, hu]
  by_cases he : enabledNA (qCount (P.restartOn s t)) u.core = true <;> simp [he]

/-- A start keeps the reaped status of another name. -/
theorem tc_afterStart_reaped {P : XPol N T} {C : Cfg N T} {s : XSt N T} {t : Trans N}
    {m : String} (hm : m ≠ t.core.name) (hs : s.st m = .reaped) :
    afterStart P C s t m = .reaped := by
  unfold afterStart
  rw [if_neg hm, hs]

/-- A start removes a stamp or keeps it. -/
theorem tc_afterStart_stamp {P : XPol N T} {C : Cfg N T} {s : XSt N T} {t : Trans N}
    (m : String) :
    stampOf (afterStart P C s t m) = none ∨ stampOf (afterStart P C s t m) = stampOf (s.st m) := by
  unfold afterStart
  by_cases hm : m = t.core.name
  · simp [hm, stampOf]
  · rw [if_neg hm]
    right
    cases hs : s.st m <;> cases hf : findT C m <;> simp only []
    split <;> rfl

/-- **What every step does to the clock statuses.** An update re-evaluates them (`updSt`), a
deadline step reaps the names it lists, a lose turns its name off, a start applies `afterStart`
and then the write of its consumption and drains, and every other step applies the write of its
label (`cycWrites`; a step that writes nothing leaves every status as it was). -/
theorem tc_st_step {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : xstepW P C s l = some s') :
    (l = .update ∧ s'.st = updSt P C s) ∨
    (∃ ns, l = .deadline ns ∧ s'.st = fun n => if ns.contains n then .reaped else s.st n) ∨
    (∃ n, l = .lose n ∧ s'.st = fun m => if m = n then .off else s.st m) ∨
    (∃ n sy t rest, l = .start n sy ∧ s.order = t :: rest ∧ t.core.name = n ∧
      (stampOf (s.st n)).isSome = true ∧
      s'.st = unreap C (inPlaces t ++ t.core.resets) (afterStart P C s t)) ∨
    ((l ≠ .update ∧ (∀ ns, l ≠ .deadline ns) ∧ (∀ n, l ≠ .lose n) ∧ (∀ n sy, l ≠ .start n sy)) ∧
      s'.st = unreap C (cycWrites s l) s.st) := by
  have keep : (l ≠ .update ∧ (∀ ns, l ≠ .deadline ns) ∧ (∀ n, l ≠ .lose n) ∧
      (∀ n sy, l ≠ .start n sy)) → s'.st = s.st → cycWrites s l = [] →
      (l ≠ .update ∧ (∀ ns, l ≠ .deadline ns) ∧ (∀ n, l ≠ .lose n) ∧ (∀ n sy, l ≠ .start n sy)) ∧
        s'.st = unreap C (cycWrites s l) s.st := fun hl hs hw => ⟨hl, by rw [hw, tc_unreap_nil, hs]⟩
  cases l with
  | update => exact Or.inl ⟨rfl, by rw [(xstepW_update h).2.2]⟩
  | deadline ns => exact Or.inr (Or.inl ⟨ns, rfl, by rw [(xstepW_deadline h).2.2.2]⟩)
  | lose n =>
    obtain ⟨t, rest, -, -, -, -, -, -, h1⟩ := loseStep_some h
    exact Or.inr (Or.inr (Or.inl ⟨n, rfl, by rw [h1]⟩))
  | start n sy =>
    obtain ⟨t, rest, ho, -, -, -, hn, hst, -, h1⟩ := startStep_some h
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, sy, t, rest, rfl, ho, hn, hst, by rw [h1]⟩)))
  | commit i =>
    obtain ⟨f, e, hf, he, -, -, -, rfl⟩ := commitStep_some h
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨by simp, ?_⟩)))
    simp [cycWrites, hf, he, depositAt]
  | tdeposit i =>
    obtain ⟨f, e, hf, he, -, -, rfl⟩ := tdepositStep_some h
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨by simp, ?_⟩)))
    simp [cycWrites, hf, he, depositAt]
  | publish i =>
    obtain ⟨b, rest, hpq, -, -, rfl⟩ := publishStep_some h
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨by simp, ?_⟩)))
    simp [cycWrites, hpq]
  | inject k =>
    obtain ⟨p, x, rest, heq, -, -, -, rfl⟩ := injectStep_some h
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨by simp, ?_⟩)))
    simp [cycWrites, heq]
  | fail i =>
    obtain ⟨f, -, -, -, rfl⟩ := failStep_some h
    exact Or.inr (Or.inr (Or.inr (Or.inr (keep (by simp) rfl rfl))))
  | endCompletions =>
    obtain ⟨-, -, -, -, rfl⟩ := xstepW_endCompletions h
    exact Or.inr (Or.inr (Or.inr (Or.inr (keep (by simp) rfl rfl))))
  | endPublications =>
    obtain ⟨-, -, -, rfl⟩ := xstepW_endPublications h
    exact Or.inr (Or.inr (Or.inr (Or.inr (keep (by simp) rfl rfl))))
  | discard k =>
    obtain ⟨p, x, rest, -, -, -, -, rfl⟩ := discardStep_some h
    exact Or.inr (Or.inr (Or.inr (Or.inr (keep (by simp) rfl rfl))))
  | endEvents =>
    obtain ⟨-, -, -, rfl⟩ := xstepW_endEvents h
    exact Or.inr (Or.inr (Or.inr (Or.inr (keep (by simp) rfl rfl))))
  | snapshot a =>
    obtain ⟨-, -, -, rfl⟩ := snapshotStep_some h
    exact Or.inr (Or.inr (Or.inr (Or.inr (keep (by simp) rfl rfl))))
  | finish c =>
    refine Or.inr (Or.inr (Or.inr (Or.inr (keep (by simp) ?_ rfl))))
    cases c with
    | quiescent => obtain ⟨-, -, -, rfl⟩ := xstepW_finishQuiescent h; rfl
    | closed => obtain ⟨-, -, -, -, rfl⟩ := xstepW_finishClosed h; rfl
    | terminal => obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h; rfl
    | stopped => obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h; rfl
  | begin =>
    obtain ⟨-, -, -, -, rfl⟩ := xstepW_begin h
    exact Or.inr (Or.inr (Or.inr (Or.inr (keep (by simp) rfl rfl))))
  | endPass =>
    obtain ⟨-, -, -, -, rfl⟩ := xstepW_endPass h
    exact Or.inr (Or.inr (Or.inr (Or.inr (keep (by simp) rfl rfl))))
  | park tmr =>
    obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := parkStep_some h
    exact Or.inr (Or.inr (Or.inr (Or.inr (keep (by simp) rfl rfl))))
  | wake =>
    obtain ⟨-, -, rfl⟩ := wakeStep_some h
    exact Or.inr (Or.inr (Or.inr (Or.inr (keep (by simp) rfl rfl))))
  | delay δ =>
    exact Or.inr (Or.inr (Or.inr (Or.inr
      (keep (by simp) (xstepW_outside_frame h rfl).2.1 rfl))))
  | write i p x =>
    exact Or.inr (Or.inr (Or.inr (Or.inr
      (keep (by simp) (xstepW_outside_frame h rfl).2.1 rfl))))
  | flush i =>
    exact Or.inr (Or.inr (Or.inr (Or.inr
      (keep (by simp) (xstepW_outside_frame h rfl).2.1 rfl))))
  | ret i ok =>
    exact Or.inr (Or.inr (Or.inr (Or.inr
      (keep (by simp) (xstepW_outside_frame h rfl).2.1 rfl))))
  | expire i e =>
    exact Or.inr (Or.inr (Or.inr (Or.inr
      (keep (by simp) (xstepW_outside_frame h rfl).2.1 rfl))))
  | request p x r =>
    exact Or.inr (Or.inr (Or.inr (Or.inr
      (keep (by simp) (xstepW_outside_frame h rfl).2.1 rfl))))
  | drain =>
    exact Or.inr (Or.inr (Or.inr (Or.inr
      (keep (by simp) (xstepW_outside_frame h rfl).2.1 rfl))))
  | close =>
    exact Or.inr (Or.inr (Or.inr (Or.inr
      (keep (by simp) (xstepW_outside_frame h rfl).2.1 rfl))))
  | terminateNow =>
    exact Or.inr (Or.inr (Or.inr (Or.inr
      (keep (by simp) (xstepW_outside_frame h rfl).2.1 rfl))))

/-- The reference update: the stamp of a name it leaves armed is the reading of the update unless
the name was armed before with its clock running (no restart pending). -/
theorem tc_updSt_newly {C : Cfg N T} {s : XSt N T} {n : String} {k : Nat} {r : Bool}
    (h : updSt refXPol C s n = .armed k r) (hn : ∀ k₀, s.st n ≠ .armed k₀ false) : k = s.now := by
  unfold updSt at h
  cases hf : findT C n with
  | none => simp [hf] at h
  | some u =>
    simp only [hf] at h
    cases hs : s.st n with
    | off =>
      simp only [hs] at h
      split at h
      · simp only [Status.armed.injEq] at h
        exact (h.1.symm.trans rfl)
      · exact absurd h (by simp)
    | armed k₀ rs =>
      simp only [hs] at h
      cases rs with
      | false => exact absurd hs (hn k₀)
      | true =>
        split at h
        · simp only [refXPol, Bool.not_false, Bool.and_self, ite_true, Status.armed.injEq] at h
          exact h.1.symm
        · exact absurd h (by simp)
    | reaped => simp [hs, refXPol] at h

/-- The reference update on a name whose transition the net holds and that is armed: with a
restart pending and the transition enabled it takes the update's reading, with its clock running
and the transition enabled it keeps its stamp. -/
theorem tc_updSt_armed {C : Cfg N T} {s : XSt N T} {n : String} {u : Trans N} {k : Nat}
    {r : Bool} (hf : findT C n = some u) (hs : s.st n = .armed k r)
    (he : enabledNA (qCount s.M) u.core = true) :
    updSt refXPol C s n = .armed (if r then s.now else k) false := by
  unfold updSt
  simp only [hf, hs, he, ite_true]
  cases r <;> simp [refXPol]

/-- The reference update keeps a reaped name of the net reaped. -/
theorem tc_updSt_reaped {C : Cfg N T} {s : XSt N T} {n : String} {u : Trans N}
    (hf : findT C n = some u) (hs : s.st n = .reaped) : updSt refXPol C s n = .reaped := by
  unfold updSt
  simp [hf, hs, refXPol]

/-- Only an update and a deadline step change the cycle reading (ruling D61 (c): the reference
deadline step takes its own reading, never earlier than the update's). -/
theorem tc_xstepW_cyc {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : xstepW P C s l = some s') (hu : l ≠ .update) (hd : ∀ ns, l ≠ .deadline ns) :
    s'.cyc = s.cyc := by
  cases l with
  | update => exact absurd rfl hu
  | deadline ns => exact absurd rfl (hd ns)
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

/-- Only a delay changes the host reading. -/
theorem tc_xstepW_now {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : xstepW P C s l = some s') (hd : ∀ δ, l ≠ .delay δ) : s'.now = s.now := by
  cases l with
  | delay δ => exact absurd rfl (hd δ)
  | begin => rw [(xstepW_begin h).2.2.2.2]
  | start n sy =>
    obtain ⟨t, rest, -, -, -, -, -, -, -, h1⟩ := startStep_some h
    rw [h1]
  | lose n =>
    obtain ⟨t, rest, -, -, -, -, -, -, h1⟩ := loseStep_some h
    rw [h1]
  | endPass => rw [(xstepW_endPass h).2.2.2.2]
  | update => rw [(xstepW_update h).2.2]
  | finish c =>
    cases c <;> simp only [xstepW] at h <;> split at h <;> simp at h <;> subst h <;> rfl
  | _ =>
    simp only [xstepW, writeStep, flushStep, retStep, expireStep, requestStep, drainStep,
      closeStep, terminateStep, commitStep, failStep, tdepositStep, depositAt, settle,
      publishStep, injectStep, discardStep, snapshotStep, parkStep, wakeStep, onOpen] at h
    all_goals (repeat' split at h) <;> (try simp at h) <;> (try (subst h; rfl))

/-- The phases between the completion of a wait and the next update: steps 1, 1b and 2, the
update itself, or the run finished. -/
def tcBeforeUpdate : Phase → Bool
  | .completions | .publications | .events | .update | .done _ => true
  | _ => false

/-- A step of the reference other than an update keeps the loop before the update: steps 1, 1b
and 2 move only forward to the update, and a finish ends the run. -/
theorem tc_beforeUpdate_step {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : xstepW P C s l = some s') (hp : tcBeforeUpdate s.phase = true) (hu : l ≠ .update) :
    tcBeforeUpdate s'.phase = true := by
  have settled : ∀ i, tcBeforeUpdate (settle s i).phase = true := by
    intro i
    simp only [settle]
    split
    · rfl
    · exact hp
  have await_or : ∀ p : Phase, (p = .await → False) → tcBeforeUpdate p = true →
      tcBeforeUpdate (if p = .await then .completions else p) = true := by
    intro p hne hp'
    rw [if_neg hne]
    exact hp'
  have notAwait : s.phase ≠ .await := by
    intro he
    rw [he] at hp
    exact absurd hp (by decide)
  cases l with
  | update => exact absurd rfl hu
  | commit i =>
    obtain ⟨f, e, -, -, -, -, -, rfl⟩ := commitStep_some h
    exact settled i
  | fail i =>
    obtain ⟨f, -, -, -, rfl⟩ := failStep_some h
    exact settled i
  | tdeposit i =>
    obtain ⟨f, e, -, -, -, -, rfl⟩ := tdepositStep_some h
    exact settled i
  | endCompletions => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endCompletions h; rfl
  | publish i =>
    obtain ⟨b, rest, -, -, -, rfl⟩ := publishStep_some h
    exact await_or _ notAwait hp
  | endPublications => obtain ⟨-, -, -, rfl⟩ := xstepW_endPublications h; rfl
  | inject k =>
    obtain ⟨p, x, rest, -, -, -, -, rfl⟩ := injectStep_some h
    exact await_or _ notAwait hp
  | discard k =>
    obtain ⟨p, x, rest, -, -, -, -, rfl⟩ := discardStep_some h
    exact await_or _ notAwait hp
  | snapshot a => obtain ⟨-, -, -, rfl⟩ := snapshotStep_some h; exact hp
  | endEvents => obtain ⟨-, -, -, rfl⟩ := xstepW_endEvents h; rfl
  | deadline ns =>
    obtain ⟨hph, -⟩ := xstepW_deadline h
    rw [hph] at hp; exact absurd hp (by decide)
  | finish c =>
    cases c with
    | quiescent =>
      obtain ⟨hph, -⟩ := xstepW_finishQuiescent h
      rw [hph] at hp; exact absurd hp (by decide)
    | closed =>
      obtain ⟨hph, -⟩ := xstepW_finishClosed h
      rw [hph] at hp; exact absurd hp (by decide)
    | terminal => obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h; rfl
    | stopped => obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h; rfl
  | begin =>
    obtain ⟨hph, -⟩ := xstepW_begin h
    rw [hph] at hp; exact absurd hp (by decide)
  | start n sy =>
    obtain ⟨t, rest, -, hph, -⟩ := startStep_some h
    rw [hph] at hp; exact absurd hp (by decide)
  | lose n =>
    obtain ⟨t, rest, -, hph, -⟩ := loseStep_some h
    rw [hph] at hp; exact absurd hp (by decide)
  | endPass =>
    obtain ⟨hph, -⟩ := xstepW_endPass h
    rw [hph] at hp; exact absurd hp (by decide)
  | park tmr =>
    obtain ⟨hph, -⟩ := parkStep_some h
    rw [hph] at hp; exact absurd hp (by decide)
  | wake =>
    obtain ⟨hph, -⟩ := wakeStep_some h
    rw [hph] at hp; exact absurd hp (by decide)
  | _ => rw [(xstepW_outside_frame h rfl).2.2.1]; exact hp

end Steps

/-! ## Decided runs of a step function -/

section Runs

variable {N T : Type}

/-- Run the labels `ls` from `s` with the step function `g`. -/
def tcRun (g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)) (C : Cfg N T) :
    XSt N T → List (XLbl N T) → Option (XSt N T)
  | s, [] => some s
  | s, l :: ls => (g C s l).bind fun s' => tcRun g C s' ls

/-- The trace of steps of the labels `ls` from `s` with the step function `g`. -/
def tcTrace (g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)) (C : Cfg N T) :
    XSt N T → List (XLbl N T) → Option (List (XStep N T))
  | _, [] => some []
  | s, l :: ls => (g C s l).bind fun s' => (tcTrace g C s' ls).map ((s, l, s') :: ·)

/-- A trace `tcTrace` builds is a run of the graph of `g`. -/
theorem tcTrace_run {g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)} {C : Cfg N T} :
    ∀ {s : XSt N T} {ls : List (XLbl N T)} {tr : List (XStep N T)},
      tcTrace g C s ls = some tr → XRun (fun C s l s' => g C s l = some s') C s tr
  | s, [], tr, h => by cases h; trivial
  | s, l :: ls, tr, h => by
    simp only [tcTrace] at h
    cases hs : g C s l with
    | none => simp [hs] at h
    | some s' =>
      simp only [hs, Option.bind_some] at h
      cases ht : tcTrace g C s' ls with
      | none => simp [ht] at h
      | some tr' =>
        simp only [ht, Option.map_some, Option.some.injEq] at h
        subst h
        exact ⟨rfl, hs, tcTrace_run ht⟩

/-- Read a decided check `p` off a trace of the labels `body` from the state the labels `pre`
lead to. -/
theorem tc_trace_check (g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)) {C : Cfg N T}
    {s0 : XSt N T} {pre body : List (XLbl N T)} {p : List (XStep N T) → Bool}
    (h : (tcRun g C s0 pre).bind (fun s => (tcTrace g C s body).map p) = some true) :
    ∃ s tr, XRun (fun C s l s' => g C s l = some s') C s tr ∧ p tr = true := by
  cases h1 : tcRun g C s0 pre with
  | none => simp [h1] at h
  | some s =>
    cases h2 : tcTrace g C s body with
    | none => simp [h1, h2] at h
    | some tr =>
      simp only [h1, h2, Option.bind_some, Option.map_some, Option.some.injEq] at h
      exact ⟨s, tr, tcTrace_run h2, h⟩

end Runs

/-! ## Example nets

Places are numbers, tokens are numbers, timings are in milliseconds. Every transition takes one
token from each input place, has no output spec, and validation accepts every emission. Priorities
are equal and the executor is not re-entrant. -/

/-- A transition named `n` with input places `ins`, read places `reads` and reset places
`resets`. -/
def tc_tr (n : String) (ins reads resets : List Nat) : Trans Nat :=
  { core := { name := n, inputs := ins.map fun p => ⟨p, .one⟩, inhibitors := [], reads := reads,
              resets := resets },
    out := none }

/-- The configuration of an example: transitions `ts`, timing by name, environment places
`envs`, tolerance 0. -/
def tc_cfg (ts : List (Trans Nat)) (tm : String → Timing) (envs : List Nat) : Cfg Nat Nat :=
  { X := { net := { places := [0, 1, 2, 3], transitions := ts },
           timing := fun t => tm t.core.name, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := envs, reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => false,
    res := 0 }

/-- The queue marking with the queues `l` lists. -/
def tc_mk (l : List (Nat × List Nat)) : QMarking Nat Nat := fun p => (l.lookup p).getD []

/-- Steps 1, 1b and 2 with nothing to settle, publish or inject, then the update. -/
def tc_cyc : List (XLbl Nat Nat) := [.endCompletions, .endPublications, .endEvents, .update]

/-- `a` takes the token of place 0, `b` the token of place 1. -/
def tc_a : Trans Nat := tc_tr "a" [0] [] []
/-- `b` takes the token of place 1. -/
def tc_b : Trans Nat := tc_tr "b" [1] [] []

/-- A sequence: `a`, enabled at the start, deposits into place 1, which enables `b`. Both
`Immediate`. -/
def tc_cSeq : Cfg Nat Nat := tc_cfg [tc_a, tc_b] (fun _ => .immediate) []

/-- The sequence net with one token in place 0. -/
def tc_mSeq : QMarking Nat Nat := tc_mk [(0, [7])]

/-- `R` refreshes the timer place 0: it takes its token (and a trigger token from place 1). -/
def tc_R : Trans Nat := tc_tr "R" [0, 1] [] []
/-- `T`, `Delayed(5)`, takes the token of the timer place 0. -/
def tc_T : Trans Nat := tc_tr "T" [0] [] []

/-- TIME-012's test derivation: `R` (`Immediate`) and `T` (`Delayed(5)`) on the timer place 0. -/
def tc_cRef : Cfg Nat Nat :=
  tc_cfg [tc_R, tc_T] (fun n => if n = "T" then .delayed 5 else .immediate) []

/-- One token in the timer place, one trigger token. -/
def tc_mRef : QMarking Nat Nat := tc_mk [(0, [7]), (1, [3])]

/-- Two tokens in the timer place (AC4, surplus), one trigger token. -/
def tc_mSur : QMarking Nat Nat := tc_mk [(0, [7, 9]), (1, [3])]

/-- `a` takes the token of place 2 (its action deposits into place 0). -/
def tc_Ra : Trans Nat := tc_tr "a" [2] [] []
/-- `r` takes the token of place 1 and drains place 0 through a reset arc. -/
def tc_Rr : Trans Nat := tc_tr "r" [1] [] [0]
/-- `T` only reads place 0. -/
def tc_RT : Trans Nat := tc_tr "T" [] [0] []

/-- The reset exception: `a`, `r` and `T`, all `Immediate` (the fast path, declaration order). -/
def tc_cRes : Cfg Nat Nat := tc_cfg [tc_Ra, tc_Rr, tc_RT] (fun _ => .immediate) []

/-- One token in each of places 0, 1 and 2. -/
def tc_mRes : QMarking Nat Nat := tc_mk [(0, [3]), (1, [2]), (2, [1])]

/-- `u`, `Window(3, 5)`, takes the token of place 0. -/
def tc_U : Trans Nat := tc_tr "u" [0] [] []

/-- A reapable transition: `u`, `Window(3, 5)`, tolerance 0; places 0 and 1 are environment
places. -/
def tc_cWin : Cfg Nat Nat := tc_cfg [tc_U] (fun _ => .window 3 5) [0, 1]

/-- `t`, `Delayed(5)`, takes the token of place 0. -/
def tc_D : Trans Nat := tc_tr "t" [0] [] []

/-- A delayed transition: `t`, `Delayed(5)`. -/
def tc_cDel : Cfg Nat Nat := tc_cfg [tc_D] (fun _ => .delayed 5) []

/-- One token in place 0. -/
def tc_m0 : QMarking Nat Nat := tc_mk [(0, [7])]

/-! ## TIME-010: the stamp is taken by the enablement update -/

requirement TIME_010_cycle
  id "TIME-010"
  title "Clock Starts on Enablement (executor cycle)"
  kind T
  scope "all executors"
  source verbatim "spec/03-timing.md"
  quote "The executor arms transitions in the enablement update of a cycle ([EXEC-001] step 3)."
        "A transition is newly armed by the first enablement update that finds it enabled while it is not armed, and its stamp is the firing-clock reading that update takes."
        "A synchronous action's deposit is first seen by the enablement update of the next cycle, and an asynchronous completion or an injected token by the enablement update of the cycle that takes it in (steps 1 and 2)."
        "So the stamp is neither the reading of the cycle in which the arming firing started nor the moment an action completed."
        "A clock restarted in a firing ([TIME-012]) is stamped the same way, by the next enablement update that finds the transition enabled."
        "*When* a transition is newly armed, the executor *shall* stamp it with the firing-clock reading taken by the enablement update that newly arms it ([EXEC-001] step 3)."
        "The executor *shall not* arm a transition or give an armed transition a different stamp in any step other than an enablement update ([EXEC-001] step 3); another step may only take a stamp away ([TIME-012], [TIME-013])."
        "*When* the executor runs the enablement update of a cycle ([EXEC-001] step 3), it *shall* take the current reading of the firing clock, and the deadline step of that cycle ([EXEC-001] step 4) *shall* judge expiry at that reading or at a later reading it takes itself."
        "The firing pass and the decision to wait of a cycle *shall* judge elapsed time at the reading of its deadline step, and no other step of the cycle *shall* take a new reading for these judgements."
  reading "For every executor R and every configuration C:"
          "an update step that leaves a name armed with stamp k, when before it the name was off, reaped, or armed with a restart pending, has k equal to the cycle reading the update takes;"
          "every step other than an update leaves the stamp of every name as it was, or leaves the name without a stamp;"
          "an update step takes the host's present reading of the firing clock as the cycle reading;"
          "a deadline step keeps the cycle reading, or replaces it by the host's present reading when that reading is not earlier;"
          "every step other than an update and a deadline step leaves the cycle reading as it was."
  assumes "The model is an executor R : XRel N T (glossary GlossaryExec.lean): R C s l s' says that under configuration C the step labelled l leads from executor state s to s'. A name's clock status is off, armed with a stamp and a restart flag, or reaped; stampOf reads the stamp of an armed status. The state holds two readings of the one firing clock: now, the host's present reading, which only the outside delay step advances (TIME-015's companion line 1), and cyc, the cycle reading, which the enablement update sets (line 3) and the deadline step may move to a later reading (line 4); the deadline step, the ready order of the pass and the park decision judge at it (design R21). The witness is the reference executor RefExec (Reference/Exec.lean), whose update re-evaluates every name (updSt)."
          "This is the companion of the Phase 1 block TIME_010 (ruling D33 (a), design NR-1). That block states the clock on the atomic timed step, where a firing and the update that arms what it enables are one step; it defers to the cycle relation the reading a new stamp takes. Line 1 is that reading: a transition is newly armed when the update finds it enabled while it is not armed (off or reaped), or finds it enabled with a restart pending ([TIME-012]), and the new stamp is the cycle reading of that update. An executor that stamps with the reading of the cycle in which the arming firing started (the reading of the previous update) breaks line 1 (TIME_010_cycle_forbids_stampAtStart)."
          "Line 2 is the new sentence that only the enablement update arms: a deposit, an injection, a firing or the return of an action never arms a transition or moves its stamp, though a start, a drop or a reap may take a clock away (TIME-012, TIME-013). An executor that arms what a commit enables at the moment of the commit, the moment an action completed, breaks line 2 (TIME_010_cycle_forbids_armOnCommit). Together the two lines give the quoted sentences on when the update sees a deposit: a synchronous deposit inside the pass is first armed by the next cycle's update, an asynchronous completion or an injected token by the update of the cycle whose step 1 or step 2 takes it in. TIME_010_cycle_nonvacuous shows both: b, enabled by a synchronous deposit in the pass of cycle reading 0, is stamped 5 by the update at reading 5; enabled by an asynchronous completion that returned at 3 and was committed at 7, it is stamped 7."
          "That an update does arm an enabled transition that is off is EXEC-001's line 8 (UpdateExact), with re-entrancy CONC-002's; that a reaped transition stays reaped until a write is TIME-013's companion. The first case of 'newly armed', a transition enabled in the initial marking, is the first update of a run from the initial state (xinit has every name off, design R19), which stamps it with the start reading."
          "The quoted 'shall not fire' sentences of TIME-010 are not lines here: a start needs a stamp (EXEC-003 line 1), and the earliest bound is judged at the cycle reading by the ready order of the pass (TIME-014 line 1 and its consequence TIME_014_not_before_earliest). The elapsed time is the glossary definition, read at the cycle reading (viewAt s s.cyc). AC1 and AC2 are the Phase 1 block's examples; on the executor the restart of AC2 is TIME-011, and the stamp the update takes on re-enablement is line 1."
          "Lines 3 to 5 are the two sentences on readings, ruling D61 (c): the enablement update takes the present reading, which is the stamp of what it newly arms (line 1); the deadline step judges expiry at that reading or at a later reading it takes itself, never at an earlier one (line 4); from the deadline step on the cycle reading is fixed, so the firing pass and the decision to wait judge at the deadline step's reading (line 5), as the ready order of the pass (TIME-014 line 1) and the park decision (CONC-010) read it. An update that keeps the reading of an older cycle breaks line 3 (TIME_010_cycle_forbids_staleUpdate), a deadline step that judges at a reading earlier than the update's breaks line 4 (TIME_010_cycle_forbids_deadlineRewind), and a pass that reads the clock again when it begins breaks line 5 (TIME_010_cycle_forbids_rereadAtBegin). With TIME-015's companion line 1 (the host reading never goes back) the readings of successive cycles are non-decreasing. These lines are TIME-010's, a MUST, and not TIME-015's, a SHOULD on the injectable clock: they hold of every executor on any firing clock."
          "The reference stamps at the update's reading and takes a reading of its own at the deadline step, the host's present one or the update's when the present is earlier (atDeadline: the second case of line 4 on every reachable state, where the cycle reading is never ahead of the present). Rust takes one reading per cycle and judges the deadline step, the pass and the park decision at it (executor_core/executor.rs:1064, :1070, :1102, :1145): a reference run with no delay between the update and the deadline step. TypeScript takes the update's reading and a second reading that its deadline step and its pass share (bitmap-net-executor.ts:715, :553): a reference run with a delay between them. Java takes three readings per cycle (BitmapNetExecutor.java:1292, :1451, :1528): its update and its deadline step are instances of lines 3 and 4, but its firing pass judges readiness at a third reading, which line 5 with TIME-014 line 1 rules out; that is a recorded executor defect, RD-16 in spec/runtime-defects.md."
          "Transition names are taken to be pairwise distinct (ruling D10, Cfg.WF.names, which the statement does not assume): the status is kept per name."
  signoff "pending"
  statement : ∀ {N T : Type} [DecidableEq N], XRel N T → Prop :=
    fun R => ∀ C,
      (∀ n k r, on (fun s s' => R C s .update s'), shall (fun s s' =>
        s'.st n = .armed k r → (∀ k₀, s.st n ≠ .armed k₀ false) → k = s'.cyc)) ∧
      (∀ l n, l ≠ .update → on (fun s s' => R C s l s'), shall (fun s s' =>
        stampOf (s'.st n) = none ∨ stampOf (s'.st n) = stampOf (s.st n))) ∧
      (on (fun s s' => R C s .update s'), shall (fun s s' => s'.cyc = s.now)) ∧
      (∀ ns, on (fun s s' => R C s (.deadline ns) s'), shall (fun s s' =>
        s'.cyc = s.cyc ∨ (s'.cyc = s.now ∧ s.cyc ≤ s.now))) ∧
      (∀ l, l ≠ .update → (∀ ns, l ≠ .deadline ns) → on (fun s s' => R C s l s'), shall
        (fun s s' => s'.cyc = s.cyc))

/- The pinned readable form of TIME_010_cycle: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.TIME_010_cycle : {N T : Type} → [DecidableEq N] → XRel N T → Prop :=
fun {N T} [DecidableEq N] R =>
  ∀ (C : Cfg N T),
    (∀ (n : String) (k : ℕ) (r : Bool),
        on fun s s' => R C s XLbl.update s', shall fun s s' =>
          s'.st n = Status.armed k r → (∀ (k₀ : ℕ), s.st n ≠ Status.armed k₀ false) → k = s'.cyc) ∧
      (∀ (l : XLbl N T) (n : String),
          l ≠ XLbl.update →
            on fun s s' => R C s l s', shall fun s s' =>
              stampOf (s'.st n) = none ∨ stampOf (s'.st n) = stampOf (s.st n)) ∧
        (on fun s s' => R C s XLbl.update s', shall fun s s' => s'.cyc = s.now) ∧
          (∀ (ns : List String),
              on fun s s' => R C s (XLbl.deadline ns) s', shall fun s s' =>
                s'.cyc = s.cyc ∨ s'.cyc = s.now ∧ s.cyc ≤ s.now) ∧
            ∀ (l : XLbl N T),
              l ≠ XLbl.update →
                (∀ (ns : List String), l ≠ XLbl.deadline ns) →
                  on fun s s' => R C s l s', shall fun s s' => s'.cyc = s.cyc
-/
#guard_msgs in #print TIME_010_cycle

/-- ✓ The reference executor satisfies the TIME-010 companion: its update stamps with the
reading it takes (`tc_updSt_newly`), no other step sets a stamp (`tc_st_step`), the update takes
the host reading as the cycle reading, the deadline step takes the host reading when it is not
earlier and keeps the cycle reading otherwise, and no other step changes it (`tc_xstepW_cyc`). -/
@[evidence holds TIME_010_cycle]
theorem TIME_010_cycle_reference {N T : Type} [DecidableEq N] :
    TIME_010_cycle (RefExec (N := N) (T := T)) := by
  refine fun C => ⟨fun n k r s s' h hst hn => ?_, fun l n hl s s' h => ?_,
    fun s s' h => by rw [(xstepW_update h).2.2], fun ns s s' h => ?_,
    fun l hl hd s s' h => tc_xstepW_cyc h hl hd⟩
  rotate_right
  · obtain ⟨-, -, -, rfl⟩ := xstepW_deadline h
    by_cases hc : s.cyc ≤ s.now
    · exact Or.inr ⟨Nat.max_eq_right hc, hc⟩
    · exact Or.inl (Nat.max_eq_left (Nat.le_of_lt (Nat.lt_of_not_le hc)))
  · obtain ⟨-, -, rfl⟩ := xstepW_update h
    exact tc_updSt_newly hst hn
  · rcases tc_st_step h with ⟨rfl, -⟩ | ⟨ns, rfl, he⟩ | ⟨m, rfl, he⟩ |
      ⟨m, sy, t, rest, rfl, -, -, -, he⟩ |
      ⟨-, he⟩
    · exact absurd rfl hl
    · rw [he]; by_cases hc : n ∈ ns <;> simp [hc, stampOf]
    · rw [he]; by_cases hc : n = m <;> simp [hc, stampOf]
    · rw [he, tc_stampOf_unreap]; exact tc_afterStart_stamp n
    · rw [he, tc_stampOf_unreap]; exact Or.inr rfl

/-- The reading of the cycle in which the arming firing started: an update that stamps with the
previous cycle reading (`XPol.stampAt := (·.cyc)`). -/
def tc_stampAtStart {N T : Type} [DecidableEq N] : XPol N T :=
  { refXPol with stampAt := (·.cyc) }

/-- ✗ Stamping with the reading of the cycle in which the arming firing started violates the
TIME-010 companion (line 1): `a` deposits synchronously in the pass of cycle reading 0, the next
update runs at 5 and stamps `b` with 0. -/
@[evidence forbids TIME_010_cycle]
theorem TIME_010_cycle_forbids_stampAtStart :
    ¬ TIME_010_cycle
      (fun C s l s' => xstepW (tc_stampAtStart (N := Nat) (T := Nat)) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check (xstepW tc_stampAtStart) (C := tc_cSeq)
    (o := tcRun (xstepW tc_stampAtStart) tc_cSeq (xinit tc_mSeq 0)
      (tc_cyc ++ [.deadline [], .begin, .start "a" true, .write 0 1 8, .ret 0 true, .commit 0,
        .endPass, .delay 5, .endCompletions, .endPublications, .endEvents]))
    (l := .update)
    (p := fun s s' => decide (s.st "b" = .off) && decide (s'.st "b" = .armed 0 false) &&
      s'.cyc == 5)
    (by decide +kernel)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
  have := (h tc_cSeq).1 "b" 0 false s s' hs hp.1.2 (fun k₀ => by rw [hp.1.1]; simp)
  rw [hp.2] at this
  exact absurd this (by decide)

/-- An executor that arms at the moment of the commit: the reference commit, then every off name
of the net that the deposit enabled is armed with the host reading. -/
def tc_armOnCommit (C : Cfg Nat Nat) (s : XSt Nat Nat) : XLbl Nat Nat → Option (XSt Nat Nat)
  | .commit i => (xstep C s (.commit i)).map fun s1 =>
      { s1 with st := fun n =>
          match s1.st n, findT C n with
          | .off, some u => if enabledNA (qCount s1.M) u.core then .armed s1.now false else .off
          | x, _ => x }
  | l => xstep C s l

/-- ✗ Arming at the moment an action completed violates the TIME-010 companion (line 2): the
asynchronous firing of `a` is committed at host reading 7, and the commit itself stamps `b`. -/
@[evidence forbids TIME_010_cycle]
theorem TIME_010_cycle_forbids_armOnCommit :
    ¬ TIME_010_cycle (fun C s l s' => tc_armOnCommit C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check tc_armOnCommit (C := tc_cSeq)
    (o := tcRun tc_armOnCommit tc_cSeq (xinit tc_mSeq 0)
      (tc_cyc ++ [.deadline [], .begin, .start "a" false, .endPass] ++ tc_cyc ++
        [.deadline [], .begin, .endPass, .delay 3, .write 0 1 8, .ret 0 true, .delay 4, .wake]))
    (l := .commit 0)
    (p := fun s s' => decide (s.st "b" = .off) && decide (s'.st "b" = .armed 7 false))
    (by decide +kernel)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  rcases (h tc_cSeq).2.1 (.commit 0) "b" (by simp) s s' hs with h1 | h1 <;>
    simp [hp.1, hp.2, stampOf] at h1

/-- An update that keeps the reading of an older cycle. -/
def tc_staleUpdate (C : Cfg Nat Nat) (s : XSt Nat Nat) : XLbl Nat Nat → Option (XSt Nat Nat)
  | .update => (xstep C s .update).map fun s1 => { s1 with cyc := s.cyc }
  | l => xstep C s l

/-- A deadline step that judges at a reading earlier than the update's: it moves the cycle reading
back by one. -/
def tc_deadlineRewind (C : Cfg Nat Nat) (s : XSt Nat Nat) : XLbl Nat Nat → Option (XSt Nat Nat)
  | .deadline ns => (xstep C s (.deadline ns)).map fun s1 => { s1 with cyc := s.cyc - 1 }
  | l => xstep C s l

/-- A pass that reads the clock again when it begins, after the deadline step judged at the
update's reading. -/
def tc_rereadAtBegin (C : Cfg Nat Nat) (s : XSt Nat Nat) : XLbl Nat Nat → Option (XSt Nat Nat)
  | .begin => (xstep C s .begin).map fun s1 => { s1 with cyc := s.now }
  | l => xstep C s l

/-- ✗ An update that keeps an older cycle reading violates the TIME-010 companion (line 3): the
update runs at host reading 5 and keeps the reading 0 of the start. -/
@[evidence forbids TIME_010_cycle]
theorem TIME_010_cycle_forbids_staleUpdate :
    ¬ TIME_010_cycle (fun C s l s' => tc_staleUpdate C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check tc_staleUpdate (C := tc_cDel)
    (o := tcRun tc_staleUpdate tc_cDel (xinit tc_m0 0)
      [.delay 5, .endCompletions, .endPublications, .endEvents])
    (l := .update)
    (p := fun s s' => s.now == 5 && s'.cyc == 0) (by decide +kernel)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  have : s'.cyc = s.now := (h tc_cDel).2.2.1 s s' hs
  omega

/-- ✗ A deadline step that judges at an earlier reading violates the TIME-010 companion (line 4):
the update takes reading 5, the host reading is 5, and the deadline step judges at 4. -/
@[evidence forbids TIME_010_cycle]
theorem TIME_010_cycle_forbids_deadlineRewind :
    ¬ TIME_010_cycle (fun C s l s' => tc_deadlineRewind C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check tc_deadlineRewind (C := tc_cDel)
    (o := tcRun tc_deadlineRewind tc_cDel (xinit tc_m0 0) (.delay 5 :: tc_cyc))
    (l := .deadline [])
    (p := fun s s' => s.cyc == 5 && s.now == 5 && s'.cyc == 4) (by decide +kernel)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  rcases (h tc_cDel).2.2.2.1 [] s s' hs with h1 | ⟨h1, -⟩ <;> omega

/-- ✗ A pass that reads the clock again violates the TIME-010 companion (line 5): the update and
the deadline step judge at reading 0, the host reading reaches 3, and the pass begins at 3. -/
@[evidence forbids TIME_010_cycle]
theorem TIME_010_cycle_forbids_rereadAtBegin :
    ¬ TIME_010_cycle (fun C s l s' => tc_rereadAtBegin C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check tc_rereadAtBegin (C := tc_cDel)
    (o := tcRun tc_rereadAtBegin tc_cDel (xinit tc_m0 0) (tc_cyc ++ [.deadline [], .delay 3]))
    (l := .begin)
    (p := fun s s' => s.cyc == 0 && s'.cyc == 3) (by decide +kernel)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  have : s'.cyc = s.cyc := (h tc_cDel).2.2.2.2 .begin (by simp) (fun _ => by simp) s s' hs
  omega

/-- Every line of the TIME-010 companion is exercised by the reference:
* a synchronous deposit of `a` in the pass of cycle reading 0 enables `b`, and `b` stays off until
  the update of the next cycle, at host reading 5, stamps it 5 (the reading of that update, not
  0, the reading of the cycle in which the arming firing started), and takes the host reading 5
  as the cycle reading;
* the asynchronous firing of `a` returns at 3, is committed at 7, and the commit leaves `b` off
  although it is enabled; the update at 7 stamps it 7 (not 3, the moment the action completed);
* the deadline step and the pass that follow the update at 5 keep the cycle reading 5. -/
@[evidence nonvacuous TIME_010_cycle]
theorem TIME_010_cycle_nonvacuous :
    (∃ s s', RefExec tc_cSeq s .update s' ∧ s.st "b" = .off ∧ s.cyc = 0 ∧ s.now = 5 ∧
      s'.st "b" = .armed 5 false ∧ s'.cyc = 5) ∧
    (∃ s s', RefExec tc_cSeq s (.ret 0 true) s' ∧ s.now = 3) ∧
    (∃ s s', RefExec tc_cSeq s (.commit 0) s' ∧ s.now = 7 ∧ s'.st "b" = .off ∧
      enabledNA (qCount s'.M) tc_b.core = true) ∧
    (∃ s s', RefExec tc_cSeq s .update s' ∧ s.st "b" = .off ∧ s'.st "b" = .armed 7 false ∧
      s'.cyc = 7) ∧
    (∃ s s', RefExec tc_cSeq s (.deadline []) s' ∧ s.cyc = 5 ∧ s'.cyc = 5) ∧
    (∃ s s', RefExec tc_cSeq s .begin s' ∧ s.cyc = 5 ∧ s'.cyc = 5) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := tc_cSeq)
      (o := xrun tc_cSeq (xinit tc_mSeq 0)
        (tc_cyc ++ [.deadline [], .begin, .start "a" true, .write 0 1 8, .ret 0 true, .commit 0,
          .endPass, .delay 5, .endCompletions, .endPublications, .endEvents]))
      (l := .update)
      (p := fun s s' => decide (s.st "b" = .off) && s.cyc == 0 && s.now == 5 &&
        decide (s'.st "b" = .armed 5 false) && s'.cyc == 5)
      (by decide +kernel)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
    exact ⟨s, s', hs, hp.1.1.1.1, hp.1.1.1.2, hp.1.1.2, hp.1.2, hp.2⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := tc_cSeq)
      (o := xrun tc_cSeq (xinit tc_mSeq 0)
        (tc_cyc ++ [.deadline [], .begin, .start "a" false, .endPass] ++ tc_cyc ++
          [.deadline [], .begin, .endPass, .delay 3, .write 0 1 8]))
      (l := .ret 0 true) (p := fun s _ => s.now == 3) (by decide +kernel)
    simp only [beq_iff_eq] at hp
    exact ⟨s, s', hs, hp⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := tc_cSeq)
      (o := xrun tc_cSeq (xinit tc_mSeq 0)
        (tc_cyc ++ [.deadline [], .begin, .start "a" false, .endPass] ++ tc_cyc ++
          [.deadline [], .begin, .endPass, .delay 3, .write 0 1 8, .ret 0 true, .delay 4, .wake]))
      (l := .commit 0)
      (p := fun s s' => s.now == 7 && decide (s'.st "b" = .off) &&
        enabledNA (qCount s'.M) tc_b.core)
      (by decide +kernel)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
    exact ⟨s, s', hs, hp.1.1, hp.1.2, hp.2⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := tc_cSeq)
      (o := xrun tc_cSeq (xinit tc_mSeq 0)
        (tc_cyc ++ [.deadline [], .begin, .start "a" false, .endPass] ++ tc_cyc ++
          [.deadline [], .begin, .endPass, .delay 3, .write 0 1 8, .ret 0 true, .delay 4, .wake,
            .commit 0, .endCompletions, .endPublications, .endEvents]))
      (l := .update)
      (p := fun s s' => decide (s.st "b" = .off) && decide (s'.st "b" = .armed 7 false) &&
        s'.cyc == 7)
      (by decide +kernel)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
    exact ⟨s, s', hs, hp.1.1, hp.1.2, hp.2⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := tc_cSeq)
      (o := xrun tc_cSeq (xinit tc_mSeq 0)
        (tc_cyc ++ [.deadline [], .begin, .start "a" true, .write 0 1 8, .ret 0 true, .commit 0,
          .endPass, .delay 5] ++ tc_cyc))
      (l := .deadline [])
      (p := fun s s' => s.cyc == 5 && s'.cyc == 5)
      (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', hs, hp.1, hp.2⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := tc_cSeq)
      (o := xrun tc_cSeq (xinit tc_mSeq 0)
        (tc_cyc ++ [.deadline [], .begin, .start "a" true, .write 0 1 8, .ret 0 true, .commit 0,
          .endPass, .delay 5] ++ tc_cyc ++ [.deadline []]))
      (l := .begin)
      (p := fun s s' => s.cyc == 5 && s'.cyc == 5)
      (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', hs, hp.1, hp.2⟩

/-! ## TIME-012: the restart of a clock across a start, at the next update -/

requirement TIME_012_cycle
  id "TIME-012"
  title "Clock Restart on Intermediate Disablement (executor cycle)"
  kind T
  scope "all executors"
  source verbatim "spec/03-timing.md"
  quote "The intermediate marking comes from the live marking `t` fires from: the tokens in the places when `t` fires, minus what `t` consumes."
        "Inside a firing pass this includes tokens a synchronous action deposited earlier in the same pass, because they are really there and a transition they keep enabled was never disabled."
        "Outputs of an asynchronous action still in flight are not in the marking yet, so they do not count."
        "A transition that the recheck finds disabled ([EXEC-003] AC3) is disarmed and loses its clock as well, even when a same-pass deposit refilled its place and keeps it enabled in the live marking."
        "It is newly armed, with a fresh stamp, by a later enablement update that finds it enabled ([TIME-010])."
        "*When* a transition `t` fires, each armed transition other than `t` that is not enabled in the intermediate marking *shall* lose its clock."
        "*When* a transition `t` fires, each armed transition other than `t` that is enabled in the intermediate marking and after the firing *shall* keep its stamp."
        "*When* a transition fires, it *shall* lose its clock."
        "*When* a transition `t` fires and a transition that lost its clock in that firing is enabled after it, that transition *shall* be newly armed ([TIME-010])."
        "*If* the enablement recheck of a firing pass finds a transition disabled ([EXEC-003] AC3), *then* the transition *shall* lose its clock, even when a same-pass deposit keeps it enabled in the live marking."
        "A reset arc drains its place, so every armed transition with a read arc on a reset place, or an input arc on it whose required count is positive, starts a fresh clock when it is enabled again, unless a same-pass deposit that the reset does not take ([EXEC-003] AC5) keeps it enabled in the intermediate marking."
        "*When* a firing pass starts a transition `t`, each other armed transition that is not enabled in the intermediate marking of `t` *shall* lose its clock at the next enablement update ([EXEC-001] step 3), even when a deposit before that update refills its places, and that update *shall* stamp it with the reading the update takes if it is enabled ([TIME-010]), after which its clock runs from that stamp."
        "Until that update the transition keeps its old stamp, so it can still start later in the same pass on that stamp if the recheck finds it enabled; this needs an inhibitor arc, because without one a transition that is not enabled in the intermediate marking of `t` is not enabled in the pass-visible marking at a later start either."
  reading "For every executor R and every configuration C:"
          "a start step of the name n from a state whose pass order begins with t leaves every other name m, whose transition u the net holds and which is armed with stamp k and restart flag r, armed with stamp k, its restart flag set exactly when r was set or u is not enabled in the live intermediate marking of t (the pass-visible marking with t's consumption and drains applied, followed by the tokens deposited earlier in the pass);"
          "a start step of the name n leaves n off;"
          "an update step from a state in which name m, whose transition u the net holds, is armed with a restart pending and u is enabled at the marking, leaves m armed with the update's cycle reading as its stamp and no restart pending;"
          "an update step from a state in which name m, whose transition u the net holds, is armed with its clock running (no restart pending) and u is enabled at the marking, leaves m armed with the stamp it held and no restart pending;"
          "a lose step of the name n leaves n off;"
          "a step other than a start, a lose step, a deadline step or an update leaves every armed name armed with the same stamp and the same restart flag."
  assumes "The model is an executor R : XRel N T (glossary GlossaryExec.lean): R C s l s' says that under configuration C the step labelled l leads from executor state s to s'. A firing is split: its start in the firing pass consumes and drains (the first half of the section), and its outputs are deposited by a later settle step (the second half). A name's clock status is off, armed with a stamp and a restart flag, or reaped (glossary: Status). liveAfter s t (GlossaryExec) is the marking right after a start of t: the pass-visible marking with t's consumption and drains applied, followed by the tokens deposited earlier in the pass. The witness is the reference executor RefExec (Reference/Exec.lean), whose start applies afterStart and whose update applies updSt."
          "This is the companion of the Phase 1 block TIME_012 (ruling D33 (a), design NR-1), which states the rule on the atomic timed step and defers to the cycle relation the live intermediate marking inside a pass, the exception of the reset bullet for a same-pass deposit, the fifth shall sentence (the recheck) and AC5 (an asynchronous action). On the executor, 'loses its clock' in a firing is a restart flag the start sets (ruling D7, the intermediate marking taken from the live marking, liveAfter), and the clock is taken away by the next update, which restamps the transition and ends the restart if it is enabled (line 3) and leaves it off if it is not (EXEC-001 line 8, TIME-011). Line 1 is the first and second shall sentences at the start, line 3 the fourth with the new sentence ('stamp it with the reading the update takes ... after which its clock runs from that stamp'), line 4 the second at the update ('keep its stamp'), line 2 the third ('When a transition fires, it shall lose its clock'), line 5 the fifth, and line 6 the new sentence's 'even when a deposit before that update refills its places': no step between the start and the update gives the clock back or moves it."
          "Line 1 reads the intermediate marking from the live marking, as the quoted sentences ask: the tokens a synchronous action deposited earlier in the same pass count, so a transition they keep enabled keeps its clock, and a reset arc drains only the pass-visible tokens (EXEC-003 AC5), so a same-pass deposit it does not take keeps a transition enabled (the reset bullet's exception). Outputs of an asynchronous action in flight are not in the marking, so they do not count. An executor that takes the marking before the start breaks line 1 (TIME_012_cycle_forbids_restartBefore: a refill by the firing's own outputs would hide the gap, which a synchronous action must not do), and so does one that takes the pass-visible marking without the same-pass deposits (TIME_012_cycle_forbids_restartOnVis, the reset exception)."
          "Line 3 is what makes a restart a restart: an executor that keeps the old stamp of a marked transition at the update (the rule before 6.0.0, survivesOld) breaks it (TIME_012_cycle_forbids_survivesOld). An update that restamps a marked transition and leaves the mark set breaks it too (TIME_012_cycle_forbids_stickyRestart): every later update would restamp it again and its clock would never run; the runtimes clear the mark at the end of the enablement scan (Rust bitmap_backend.rs:636-639, Java BitmapNetExecutor.java:1334-1336, TypeScript bitmap-net-executor.ts:778-781). Line 4 keeps a running clock: an update that restamps every armed transition breaks it (TIME_012_cycle_forbids_restampAll). Line 6: a commit whose deposit refills the place and clears the mark, the rule before 6.0.0 put in the deposit, breaks it (TIME_012_cycle_forbids_commitHeals). Line 2: a start that keeps its own transition's clock breaks it (TIME_012_cycle_forbids_startKeepsClock); under re-entrancy (ruling D8 (b)) the started transition is armed again, with a fresh stamp, by the next update that finds it enabled, as bullet 4 says. Line 5 overlaps EXEC-003 line 4, which states the same for a drop; it is kept here because it is TIME-012's fifth sentence: a loser loses its clock even when a same-pass deposit keeps it enabled in the live marking (TIME_012_cycle_forbids_loseKeepsClock). The two rules apply in sequence in one pass: a transition can keep its stamp through a start by line 1 and lose its clock to the recheck later in the same pass by line 5; TIME_012_cycle_nonvacuous shows it. A marked transition keeps its old stamp until the update (line 1), and a start needs only a stamp and the recheck on the pass-visible marking (EXEC-003 line 1), so it can still start later in the same pass on that stamp, as the quoted sentence says; the runtimes do the same, as their pass reads no mark (Rust bitmap_backend.rs:425-440 sets it, :626-639 reads and clears it in the scan). This takes an inhibitor arc: a same-pass deposit into an inhibitor place disables the transition in the live intermediate marking, which counts the deposit, but not in the pass-visible marking, which does not; without an inhibitor arc a transition disabled in the intermediate marking stays disabled in every later pass-visible marking of the pass."
          "Bullet 1 (an inhibitor arc never disables by a removal) and bullet 2 (a reset place restarts the clocks of transitions with a positive requirement on it or a read arc on it) are enabledNA read on liveAfter, as in the Phase 1 block. The ν-join clause of bullet 1 is the NU blocks', deferred with the ν firing kernel. The paragraph on the state class graph and on the events ([VER-010], [EVT-005], [EVT-004]) is not encoded here."
          "AC1 (a synchronous refill restarts T) is TIME_012_cycle_nonvacuous's first case: R starts and marks T, the update at reading 2 stamps T 2; that T then fires no earlier than 5 after the refill is TIME-014 line 1 with the stamp. AC2 (T only reads P) is the reset example's read arc and the Phase 1 block's TIME_012_ac2. AC3 (a reset drain) is the Phase 1 block's TIME_012_ac3, and its same-pass exception is the reset example here. AC4 (surplus tokens keep the clock) is the surplus case: T is not marked and keeps stamp 0 through the update at 2; its event clause is EVT's. AC5 (an asynchronous action restarts T as well) is the asynchronous case: R starts asynchronously and marks T, the next update finds T disabled and leaves it off, and the update after the completion arms it with the reading 3. AC6 (each restart emits exactly one of TransitionClockRestarted or TransitionEnabled) is EVT-004 and EVT-005 over the update, on the event model (W7)."
          "Transition names are taken to be pairwise distinct (ruling D10, Cfg.WF.names, which the statement does not assume): line 1 judges the transition the net holds under m (findT)."
  signoff "pending"
  statement : ∀ {N T : Type} [DecidableEq N], XRel N T → Prop :=
    fun R => ∀ C,
      (∀ n sy t rest m u k r, m ≠ n → findT C m = some u →
        on (fun s s' => R C s (.start n sy) s'), shall (fun s s' => s.order = t :: rest →
          s.st m = .armed k r →
            s'.st m = .armed k (r || !enabledNA (qCount (liveAfter s t)) u.core))) ∧
      (∀ n sy, on (fun s s' => R C s (.start n sy) s'), shall (fun _ s' => s'.st n = .off)) ∧
      (∀ m u k, findT C m = some u → on (fun s s' => R C s .update s'), shall (fun s s' =>
        s.st m = .armed k true → enabledNA (qCount s.M) u.core = true →
          s'.st m = .armed s'.cyc false)) ∧
      (∀ m u k, findT C m = some u → on (fun s s' => R C s .update s'), shall (fun s s' =>
        s.st m = .armed k false → enabledNA (qCount s.M) u.core = true →
          s'.st m = .armed k false)) ∧
      (∀ n, on (fun s s' => R C s (.lose n) s'), shall (fun _ s' => s'.st n = .off)) ∧
      (∀ l n k r, (∀ n sy, l ≠ .start n sy) → (∀ n, l ≠ .lose n) → (∀ ns, l ≠ .deadline ns) →
        l ≠ .update → on (fun s s' => R C s l s'), shall (fun s s' =>
          s.st n = .armed k r → s'.st n = .armed k r))

/- The pinned readable form of TIME_012_cycle: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.TIME_012_cycle : {N T : Type} → [DecidableEq N] → XRel N T → Prop :=
fun {N T} [DecidableEq N] R =>
  ∀ (C : Cfg N T),
    (∀ (n : String) (sy : Bool) (t : Reference.Trans N) (rest : List (Reference.Trans N)) (m : String)
        (u : Reference.Trans N) (k : ℕ) (r : Bool),
        m ≠ n →
          findT C m = some u →
            on fun s s' => R C s (XLbl.start n sy) s', shall fun s s' =>
              s.order = t :: rest →
                s.st m = Status.armed k r →
                  s'.st m = Status.armed k (r || !enabledNA (qCount (liveAfter s t)) u.core)) ∧
      (∀ (n : String) (sy : Bool), on fun s s' => R C s (XLbl.start n sy) s', shall fun x s' => s'.st n = Status.off) ∧
        (∀ (m : String) (u : Reference.Trans N) (k : ℕ),
            findT C m = some u →
              on fun s s' => R C s XLbl.update s', shall fun s s' =>
                s.st m = Status.armed k true →
                  enabledNA (qCount s.M) u.core = true → s'.st m = Status.armed s'.cyc false) ∧
          (∀ (m : String) (u : Reference.Trans N) (k : ℕ),
              findT C m = some u →
                on fun s s' => R C s XLbl.update s', shall fun s s' =>
                  s.st m = Status.armed k false →
                    enabledNA (qCount s.M) u.core = true → s'.st m = Status.armed k false) ∧
            (∀ (n : String), on fun s s' => R C s (XLbl.lose n) s', shall fun x s' => s'.st n = Status.off) ∧
              ∀ (l : XLbl N T) (n : String) (k : ℕ) (r : Bool),
                (∀ (n : String) (sy : Bool), l ≠ XLbl.start n sy) →
                  (∀ (n : String), l ≠ XLbl.lose n) →
                    (∀ (ns : List String), l ≠ XLbl.deadline ns) →
                      l ≠ XLbl.update →
                        on fun s s' => R C s l s', shall fun s s' =>
                          s.st n = Status.armed k r → s'.st n = Status.armed k r
-/
#guard_msgs in #print TIME_012_cycle

/-- ✓ The reference executor satisfies the TIME-012 companion: its start applies `afterStart`
on the live intermediate marking (`refXPol.restartOn = liveAfter`), its update restamps a marked
name, clears its mark and keeps a running clock (`tc_updSt_armed`), its lose turns the name off,
and every other step keeps an armed status (`tc_st_step`, `tc_unreap_armed`). -/
@[evidence holds TIME_012_cycle]
theorem TIME_012_cycle_reference {N T : Type} [DecidableEq N] :
    TIME_012_cycle (RefExec (N := N) (T := T)) := by
  refine fun C => ⟨fun n sy t rest m u k r hmn hu s s' h ho hs => ?_, fun n sy s s' h => ?_,
    fun m u k hu s s' h hs he => ?_, fun m u k hu s s' h hs he => ?_, fun n s s' h => ?_,
    fun l n k r h1 h2 h3 h4 s s' h hs => ?_⟩
  · obtain ⟨t', rest', ho', -, -, -, hn, -, -, h1⟩ := startStep_some h
    rw [ho] at ho'
    obtain ⟨rfl, rfl⟩ := List.cons.inj ho'
    rw [h1]
    exact tc_unreap_armed (tc_afterStart_armed (by rw [hn]; exact hmn) hu hs)
  · obtain ⟨t, rest, -, -, -, -, hn, -, -, h1⟩ := startStep_some h
    rw [h1]
    show unreap C _ (afterStart refXPol C s t) n = .off
    rw [← hn]
    exact unreap_off tc_afterStart_self
  · obtain ⟨-, -, rfl⟩ := xstepW_update h
    show updSt refXPol C s m = .armed s.now false
    rw [tc_updSt_armed hu hs he]
    rfl
  · obtain ⟨-, -, rfl⟩ := xstepW_update h
    show updSt refXPol C s m = .armed k false
    rw [tc_updSt_armed hu hs he]
    rfl
  · obtain ⟨t, rest, -, -, -, -, -, -, h1⟩ := loseStep_some h
    rw [h1]
    simp
  · rcases tc_st_step h with ⟨rfl, -⟩ | ⟨ns, rfl, -⟩ | ⟨m, rfl, -⟩ | ⟨m, sy, -, -, rfl, -⟩ | ⟨-, he⟩
    · exact absurd rfl h4
    · exact absurd rfl (h3 ns)
    · exact absurd rfl (h2 m)
    · exact absurd rfl (h1 m sy)
    · rw [he]; exact tc_unreap_armed hs

/-- The marking before the start: the restart flag judged before `t` consumes. -/
def tc_restartBefore {N T : Type} [DecidableEq N] : XPol N T :=
  { refXPol with restartOn := fun s _ => s.M }

/-- The pass-visible marking: the restart flag judged without the tokens deposited earlier in the
pass. -/
def tc_restartOnVis {N T : Type} [DecidableEq N] : XPol N T :=
  { refXPol with restartOn := fun s t => qConsume (vis s) t }

/-- The rule before 6.0.0: the update keeps the old stamp of a marked transition. -/
def tc_survivesOld {N T : Type} [DecidableEq N] : XPol N T :=
  { refXPol with keepOnRestart := true }

/-- ✗ Judging the restart on the marking before the start violates the TIME-012 companion
(line 1, AC1): `R` takes the only token of the timer place, which disables `T` in the
intermediate marking, and the start leaves `T`'s clock running. -/
@[evidence forbids TIME_012_cycle]
theorem TIME_012_cycle_forbids_restartBefore :
    ¬ TIME_012_cycle
      (fun C s l s' => xstepW (tc_restartBefore (N := Nat) (T := Nat)) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check (xstepW tc_restartBefore) (C := tc_cRef)
    (o := tcRun (xstepW tc_restartBefore) tc_cRef (xinit tc_mRef 0)
      (tc_cyc ++ [.deadline [], .begin]))
    (l := .start "R" true)
    (p := fun s s' => match s.order with
      | t :: _ => decide (s.st "T" = .armed 0 false) && decide (s'.st "T" = .armed 0 false) &&
          !enabledNA (qCount (liveAfter s t)) tc_T.core
      | [] => false)
    (by decide +kernel)
  cases ho : s.order with
  | nil => simp [ho] at hp
  | cons t rest =>
    simp only [ho, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hp
    have := (h tc_cRef).1 "R" true t rest "T" tc_T 0 false (by decide) rfl s s' hs ho hp.1.1
    rw [hp.1.2, hp.2] at this
    simp at this

/-- ✗ Judging the restart on the pass-visible marking violates the TIME-012 companion (line 1,
the reset bullet's exception): `a` deposits a token into place 0 synchronously in the pass, `r`
then drains place 0 through its reset arc, which takes only the pass-visible token, and `T`, which
reads place 0, is marked for a restart although the deposit keeps it enabled. -/
@[evidence forbids TIME_012_cycle]
theorem TIME_012_cycle_forbids_restartOnVis :
    ¬ TIME_012_cycle
      (fun C s l s' => xstepW (tc_restartOnVis (N := Nat) (T := Nat)) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check (xstepW tc_restartOnVis) (C := tc_cRes)
    (o := tcRun (xstepW tc_restartOnVis) tc_cRes (xinit tc_mRes 0)
      (tc_cyc ++ [.deadline [], .begin, .start "a" true, .write 0 0 8, .ret 0 true, .commit 0]))
    (l := .start "r" false)
    (p := fun s s' => match s.order with
      | t :: _ => decide (s.st "T" = .armed 0 false) && decide (s'.st "T" = .armed 0 true) &&
          enabledNA (qCount (liveAfter s t)) tc_RT.core
      | [] => false)
    (by decide +kernel)
  cases ho : s.order with
  | nil => simp [ho] at hp
  | cons t rest =>
    simp only [ho, Bool.and_eq_true, decide_eq_true_eq] at hp
    have := (h tc_cRes).1 "r" false t rest "T" tc_RT 0 false (by decide) rfl s s' hs ho hp.1.1
    rw [hp.1.2, hp.2] at this
    simp at this

/-- A start that keeps the clock of the transition it starts. -/
def tc_startKeepsClock (C : Cfg Nat Nat) (s : XSt Nat Nat) : XLbl Nat Nat → Option (XSt Nat Nat)
  | .start n sy => (xstep C s (.start n sy)).map fun s1 =>
      { s1 with st := fun m => if m = n then s.st m else s1.st m }
  | l => xstep C s l

/-- ✗ A start that keeps its own transition's clock violates the TIME-012 companion (line 2):
`R` starts and stays armed with stamp 0. -/
@[evidence forbids TIME_012_cycle]
theorem TIME_012_cycle_forbids_startKeepsClock :
    ¬ TIME_012_cycle (fun C s l s' => tc_startKeepsClock C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check tc_startKeepsClock (C := tc_cRef)
    (o := tcRun tc_startKeepsClock tc_cRef (xinit tc_mRef 0) (tc_cyc ++ [.deadline [], .begin]))
    (l := .start "R" true)
    (p := fun _ s' => decide (s'.st "R" = .armed 0 false))
    (by decide +kernel)
  simp only [decide_eq_true_eq] at hp
  have : s'.st "R" = .off := (h tc_cRef).2.1 "R" true s s' hs
  rw [hp] at this
  exact absurd this (by simp)

/-- ✗ Keeping the old stamp of a transition marked for a restart violates the TIME-012 companion
(line 3, AC1): `R` refills the timer place synchronously, the update at reading 2 finds `T`
marked and enabled, and keeps its stamp 0. -/
@[evidence forbids TIME_012_cycle]
theorem TIME_012_cycle_forbids_survivesOld :
    ¬ TIME_012_cycle
      (fun C s l s' => xstepW (tc_survivesOld (N := Nat) (T := Nat)) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check (xstepW tc_survivesOld) (C := tc_cRef)
    (o := tcRun (xstepW tc_survivesOld) tc_cRef (xinit tc_mRef 0)
      (tc_cyc ++ [.deadline [], .begin, .start "R" true, .write 0 0 8, .ret 0 true, .commit 0,
        .endPass, .delay 2, .endCompletions, .endPublications, .endEvents]))
    (l := .update)
    (p := fun s s' => decide (s.st "T" = .armed 0 true) && enabledNA (qCount s.M) tc_T.core &&
      decide (s'.st "T" = .armed 0 false) && s'.cyc == 2)
    (by decide +kernel)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
  have := (h tc_cRef).2.2.1 "T" tc_T 0 rfl s s' hs hp.1.1.1 hp.1.1.2
  rw [hp.1.2, hp.2] at this
  exact absurd this (by simp)

/-- An update that restamps every armed transition with its reading. -/
def tc_restampAll (C : Cfg Nat Nat) (s : XSt Nat Nat) : XLbl Nat Nat → Option (XSt Nat Nat)
  | .update => (xstep C s .update).map fun s1 =>
      { s1 with st := fun n =>
          match s1.st n with
          | .armed _ r => .armed s1.cyc r
          | x => x }
  | l => xstep C s l

/-- ✗ Restamping a running clock violates the TIME-012 companion (line 4, AC4): with two tokens
in the timer place, `R` takes one and returns one, `T` stays enabled in the intermediate marking,
and the update at reading 2 restamps it. -/
@[evidence forbids TIME_012_cycle]
theorem TIME_012_cycle_forbids_restampAll :
    ¬ TIME_012_cycle (fun C s l s' => tc_restampAll C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check tc_restampAll (C := tc_cRef)
    (o := tcRun tc_restampAll tc_cRef (xinit tc_mSur 0)
      (tc_cyc ++ [.deadline [], .begin, .start "R" true, .write 0 0 8, .ret 0 true, .commit 0,
        .endPass, .delay 2, .endCompletions, .endPublications, .endEvents]))
    (l := .update)
    (p := fun s s' => decide (s.st "T" = .armed 0 false) && enabledNA (qCount s.M) tc_T.core &&
      decide (s'.st "T" = .armed 2 false))
    (by decide +kernel)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  have := (h tc_cRef).2.2.2.1 "T" tc_T 0 rfl s s' hs hp.1.1 hp.1.2
  rw [hp.2] at this
  exact absurd this (by simp)

/-- A drop that keeps the clock of the transition it drops. -/
def tc_loseKeepsClock (C : Cfg Nat Nat) (s : XSt Nat Nat) : XLbl Nat Nat → Option (XSt Nat Nat)
  | .lose n => (xstep C s (.lose n)).map fun s1 => { s1 with st := s.st }
  | l => xstep C s l

/-- ✗ A recheck loser that keeps its clock violates the TIME-012 companion (line 5): after `r`
drains place 0, `T` is not enabled on the pass-visible marking and is dropped, and keeps its
stamp 0, although the token `a` deposited keeps it enabled in the live marking. -/
@[evidence forbids TIME_012_cycle]
theorem TIME_012_cycle_forbids_loseKeepsClock :
    ¬ TIME_012_cycle (fun C s l s' => tc_loseKeepsClock C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check tc_loseKeepsClock (C := tc_cRes)
    (o := tcRun tc_loseKeepsClock tc_cRes (xinit tc_mRes 0)
      (tc_cyc ++ [.deadline [], .begin, .start "a" true, .write 0 0 8, .ret 0 true, .commit 0,
        .start "r" false]))
    (l := .lose "T")
    (p := fun _ s' => decide (s'.st "T" = .armed 0 false))
    (by decide +kernel)
  simp only [decide_eq_true_eq] at hp
  have : s'.st "T" = .off := (h tc_cRes).2.2.2.2.1 "T" s s' hs
  rw [hp] at this
  exact absurd this (by simp)

/-- An update that restamps a marked transition and leaves its mark set (the runtimes clear the
mark at the end of the enablement scan: Rust `bitmap_backend.rs` 636-639, Java
`BitmapNetExecutor.java` 1334-1336, TypeScript `bitmap-net-executor.ts` 778-781). -/
def tc_stickyRestart (C : Cfg Nat Nat) (s : XSt Nat Nat) : XLbl Nat Nat → Option (XSt Nat Nat)
  | .update => (xstep C s .update).map fun s1 =>
      { s1 with st := fun n =>
          match s1.st n, s.st n with
          | .armed k _, .armed _ true => .armed k true
          | x, _ => x }
  | l => xstep C s l

/-- A commit whose deposit heals the mark: every marked transition its deposit leaves enabled
keeps its old clock (the rule before 6.0.0, put in the deposit instead of the update). -/
def tc_commitHeals (C : Cfg Nat Nat) (s : XSt Nat Nat) : XLbl Nat Nat → Option (XSt Nat Nat)
  | .commit i => (xstep C s (.commit i)).map fun s1 =>
      { s1 with st := fun n =>
          match s1.st n, findT C n with
          | .armed k true, some u =>
              if enabledNA (qCount s1.M) u.core then .armed k false else .armed k true
          | x, _ => x }
  | l => xstep C s l

/-- ✗ A mark that outlives its update violates the TIME-012 companion (line 3, AC1): `R` refills
the timer place synchronously, and the update at reading 2 stamps `T` 2 but leaves it marked, so
every later update would restamp it and its clock would never run. -/
@[evidence forbids TIME_012_cycle]
theorem TIME_012_cycle_forbids_stickyRestart :
    ¬ TIME_012_cycle (fun C s l s' => tc_stickyRestart C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check tc_stickyRestart (C := tc_cRef)
    (o := tcRun tc_stickyRestart tc_cRef (xinit tc_mRef 0)
      (tc_cyc ++ [.deadline [], .begin, .start "R" true, .write 0 0 8, .ret 0 true, .commit 0,
        .endPass, .delay 2, .endCompletions, .endPublications, .endEvents]))
    (l := .update)
    (p := fun s s' => decide (s.st "T" = .armed 0 true) && enabledNA (qCount s.M) tc_T.core &&
      decide (s'.st "T" = .armed 2 true) && s'.cyc == 2)
    (by decide +kernel)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
  have := (h tc_cRef).2.2.1 "T" tc_T 0 rfl s s' hs hp.1.1.1 hp.1.1.2
  rw [hp.1.2, hp.2] at this
  exact absurd this (by simp)

/-- ✗ A deposit that heals the mark violates the TIME-012 companion (line 6, AC1): `R` takes the
only token of the timer place, which marks `T`; the commit of its refill at reading 2 clears the
mark, so the next update would keep `T`'s stamp 0 and `T` would start 3 ms after the refill. -/
@[evidence forbids TIME_012_cycle]
theorem TIME_012_cycle_forbids_commitHeals :
    ¬ TIME_012_cycle (fun C s l s' => tc_commitHeals C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check tc_commitHeals (C := tc_cRef)
    (o := tcRun tc_commitHeals tc_cRef (xinit tc_mRef 0)
      (tc_cyc ++ [.deadline [], .begin, .start "R" true, .write 0 0 8, .delay 2, .ret 0 true]))
    (l := .commit 0)
    (p := fun s s' => decide (s.st "T" = .armed 0 true) && decide (s'.st "T" = .armed 0 false))
    (by decide +kernel)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  have := (h tc_cRef).2.2.2.2.2 (.commit 0) "T" 0 true (by simp) (by simp) (by simp) (by simp)
    s s' hs hp.1
  rw [hp.2] at this
  exact absurd this (by simp)

/-- Every line of the TIME-012 companion is exercised by the reference:
* AC1: `R` starts synchronously and takes the only token of the timer place; `T` is marked for a
  restart and `R` is off; the commit of the refill leaves `T` marked though it is enabled again;
  the update at reading 2 stamps `T` 2 and clears the mark;
* AC5: `R` starts asynchronously; the next update, at reading 1, finds `T` marked and disabled
  and leaves it off; the update after the completion, at reading 3, arms it with 3;
* AC4: with two tokens in the timer place `T` is not marked and the update at 2 keeps its
  stamp 0;
* the reset exception and the recheck in one pass: `a` deposits into place 0 synchronously, `r`
  drains the pass-visible token, `T` (reading place 0) keeps its stamp 0, then `T` is dropped by
  the recheck and loses its clock while the deposited token keeps it enabled. -/
@[evidence nonvacuous TIME_012_cycle]
theorem TIME_012_cycle_nonvacuous :
    (∃ s s', RefExec tc_cRef s (.start "R" true) s' ∧ s.st "T" = .armed 0 false ∧
      s'.st "T" = .armed 0 true ∧ s'.st "R" = .off) ∧
    (∃ s s', RefExec tc_cRef s .update s' ∧ s.st "T" = .armed 0 true ∧
      enabledNA (qCount s.M) tc_T.core = true ∧ s'.st "T" = .armed 2 false ∧ s'.cyc = 2) ∧
    (∃ s s', RefExec tc_cRef s .update s' ∧ s.st "T" = .armed 0 true ∧ s'.st "T" = .off) ∧
    (∃ s s', RefExec tc_cRef s .update s' ∧ s.st "T" = .off ∧ s'.st "T" = .armed 3 false) ∧
    (∃ s s', RefExec tc_cRef s .update s' ∧ s.st "T" = .armed 0 false ∧
      enabledNA (qCount s.M) tc_T.core = true ∧ s'.st "T" = .armed 0 false ∧ s'.cyc = 2) ∧
    (∃ s s', RefExec tc_cRes s (.start "r" false) s' ∧ s.st "T" = .armed 0 false ∧
      s'.st "T" = .armed 0 false) ∧
    (∃ s s', RefExec tc_cRes s (.lose "T") s' ∧ s'.st "T" = .off ∧
      enabledNA (qCount s'.M) tc_RT.core = true) ∧
    (∃ s s', RefExec tc_cRef s (.commit 0) s' ∧ s.st "T" = .armed 0 true ∧
      s'.st "T" = .armed 0 true ∧ enabledNA (qCount s'.M) tc_T.core = true) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := tc_cRef)
      (o := xrun tc_cRef (xinit tc_mRef 0) (tc_cyc ++ [.deadline [], .begin]))
      (l := .start "R" true)
      (p := fun s s' => decide (s.st "T" = .armed 0 false) && decide (s'.st "T" = .armed 0 true) &&
        decide (s'.st "R" = .off))
      (by decide +kernel)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    exact ⟨s, s', hs, hp.1.1, hp.1.2, hp.2⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := tc_cRef)
      (o := xrun tc_cRef (xinit tc_mRef 0)
        (tc_cyc ++ [.deadline [], .begin, .start "R" true, .write 0 0 8, .ret 0 true, .commit 0,
          .endPass, .delay 2, .endCompletions, .endPublications, .endEvents]))
      (l := .update)
      (p := fun s s' => decide (s.st "T" = .armed 0 true) && enabledNA (qCount s.M) tc_T.core &&
        decide (s'.st "T" = .armed 2 false) && s'.cyc == 2)
      (by decide +kernel)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
    exact ⟨s, s', hs, hp.1.1.1, hp.1.1.2, hp.1.2, hp.2⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := tc_cRef)
      (o := xrun tc_cRef (xinit tc_mRef 0)
        (tc_cyc ++ [.deadline [], .begin, .start "R" false, .endPass, .delay 1,
          .endCompletions, .endPublications, .endEvents]))
      (l := .update)
      (p := fun s s' => decide (s.st "T" = .armed 0 true) && decide (s'.st "T" = .off))
      (by decide +kernel)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    exact ⟨s, s', hs, hp.1, hp.2⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := tc_cRef)
      (o := xrun tc_cRef (xinit tc_mRef 0)
        (tc_cyc ++ [.deadline [], .begin, .start "R" false, .endPass, .delay 1] ++ tc_cyc ++
          [.deadline [], .begin, .endPass, .delay 2, .write 0 0 8, .ret 0 true, .wake, .commit 0,
            .endCompletions, .endPublications, .endEvents]))
      (l := .update)
      (p := fun s s' => decide (s.st "T" = .off) && decide (s'.st "T" = .armed 3 false))
      (by decide +kernel)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    exact ⟨s, s', hs, hp.1, hp.2⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := tc_cRef)
      (o := xrun tc_cRef (xinit tc_mSur 0)
        (tc_cyc ++ [.deadline [], .begin, .start "R" true, .write 0 0 8, .ret 0 true, .commit 0,
          .endPass, .delay 2, .endCompletions, .endPublications, .endEvents]))
      (l := .update)
      (p := fun s s' => decide (s.st "T" = .armed 0 false) && enabledNA (qCount s.M) tc_T.core &&
        decide (s'.st "T" = .armed 0 false) && s'.cyc == 2)
      (by decide +kernel)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
    exact ⟨s, s', hs, hp.1.1.1, hp.1.1.2, hp.1.2, hp.2⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := tc_cRes)
      (o := xrun tc_cRes (xinit tc_mRes 0)
        (tc_cyc ++ [.deadline [], .begin, .start "a" true, .write 0 0 8, .ret 0 true, .commit 0]))
      (l := .start "r" false)
      (p := fun s s' => decide (s.st "T" = .armed 0 false) && decide (s'.st "T" = .armed 0 false))
      (by decide +kernel)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    exact ⟨s, s', hs, hp.1, hp.2⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := tc_cRes)
      (o := xrun tc_cRes (xinit tc_mRes 0)
        (tc_cyc ++ [.deadline [], .begin, .start "a" true, .write 0 0 8, .ret 0 true, .commit 0,
          .start "r" false]))
      (l := .lose "T")
      (p := fun _ s' => decide (s'.st "T" = .off) && enabledNA (qCount s'.M) tc_RT.core)
      (by decide +kernel)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    exact ⟨s, s', hs, hp.1, hp.2⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := tc_cRef)
      (o := xrun tc_cRef (xinit tc_mRef 0)
        (tc_cyc ++ [.deadline [], .begin, .start "R" true, .write 0 0 8, .ret 0 true]))
      (l := .commit 0)
      (p := fun s s' => decide (s.st "T" = .armed 0 true) && decide (s'.st "T" = .armed 0 true) &&
        enabledNA (qCount s'.M) tc_T.core)
      (by decide +kernel)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    exact ⟨s, s', hs, hp.1.1, hp.1.2, hp.2⟩

/-! ## TIME-013: the deadline step, and how a reaped transition comes back -/

requirement TIME_013_cycle
  id "TIME-013"
  title "Deadline Enforcement (executor cycle)"
  kind T
  scope "all executors"
  source verbatim "spec/03-timing.md"
  quote "When a reapable transition is expired, that is, armed with an elapsed time strictly greater than its latest bound plus the deadline tolerance, the executor reaps it: it disarms the transition without firing it and emits a `TransitionTimedOut` event."
        "*If* a reapable transition is armed and its elapsed time is greater than its latest bound plus the deadline tolerance, *then* the executor *shall* reap it in the deadline step of that cycle ([EXEC-001] step 4) and emit `TransitionTimedOut` ([EVT-009])."
        "The executor *shall not* reap a transition that is not reapable."
        "*When* a firing or an injected token writes one of a reaped transition's arc places (an input, read, inhibitor or reset place) and the transition is enabled afterwards, the transition *shall* be newly armed with a fresh clock ([TIME-010])."
        "*While* a transition is reaped, an enablement update *shall* leave it reaped, and only a firing or an injected token that writes one of its arc places *shall* end its reaped state."
        "The deadline step *shall* judge expiry at its reading of the firing clock ([TIME-010]), and it *shall not* reap a transition that is not expired at that reading or change the marking."
        "A firing writes a place when it consumes from it, deposits into it or drains it through a reset arc; draining a reset place that is already empty counts as a write."
        "A reaped transition keeps its input tokens and is not armed again until one of its arc places is written, so an executor that fell behind can come to rest at a marking that still enables it."
  reading "For every executor R and every configuration C:"
          "a deadline step from s to s' leaves reaped every transition of the net that is expired in s at the reading of the deadline step (the cycle reading of s');"
          "a deadline step from s to s' leaves the marking as it was and changes the status of a name only to reaped, and only of a name of a transition of the net that is expired in s at the reading of the deadline step;"
          "an update step leaves reaped every name of a transition of the net that is reaped before it;"
          "a step that takes a name of a transition u of the net out of the reaped status writes one of u's arc places, or is a lose step of that name;"
          "a step that writes one of the arc places of a transition u of the net, from a state in which u's name is reaped, leaves that name off."
  assumes "The model is an executor R : XRel N T (glossary GlossaryExec.lean): R C s l s' says that under configuration C the step labelled l leads from executor state s to s'. A name's clock status is off, armed with a stamp and a restart flag, or reaped (glossary: ReapedE). Expired is the glossary term, read on the timed view of the state at the reading of the deadline step (viewAt s s'.cyc: the marking and the stamps before the step, the reading the step judges at, which is the update's reading or a later one, TIME-010's companion lines 3 to 5, ruling D61 (c)): reapable, armed, elapsed time strictly greater than the latest bound plus the tolerance (ruling D4). Write is the glossary term at the grain of the executor, cycWrites: a start writes the input and reset places of its transition, a commit or a timeout deposit the places of its emission, a publication the places of its batch, an injection the place of its token. The witness is the reference executor RefExec (Reference/Exec.lean)."
          "This is the companion of the Phase 1 block TIME_013 (ruling D33 (a), design NR-1), which encodes the reap as far as one atomic step can (a reap is available from every expired transition, and only from one) and defers to the cycle relation that the reap is taken, in the deadline step of the very cycle, and the injected-token clause. Line 1 is the 'shall reap it in the deadline step of that cycle' sentence: the deadline step reaps every transition expired at its reading, which is the reading the update of that cycle took or a later one (TIME-010's companion, ruling D61 (c)); so a transition still armed in the first cycle whose reading puts it strictly past its bound is reaped in that cycle (AC1's second sentence, TIME-015 AC6). An executor that reaps one cycle late breaks it (TIME_013_cycle_forbids_reapLate). That the transition does not fire in the pass of that cycle is EXEC-001 line 6 with EXEC-003 line 1 (a start needs a stamp, a reaped name has none), and that the pass comes after the deadline step is EXEC-001 line 2, which excludes the refresh rescue of ClashesTime (clash013_refresh_rescue)."
          "Line 2 is the first quoted sentence ('it disarms the transition without firing it'), the new sentence that the deadline step judges at its reading, reaps nothing that is not expired at it and does not change the marking, and the shall sentence on not reaping a transition that is not reapable: the deadline step reaps only expired transitions, so only reapable ones (Exact, Immediate and Delayed transitions are never expired, TIME-006), keeps their tokens ('keeps its input tokens') and changes no other status. An executor that reaps at the bound instead of strictly past it breaks it (TIME_013_cycle_forbids_reapAtBound). That the deadline step emits TransitionTimedOut is EVT-009's, on the event model (W7)."
          "Lines 3 and 4 are the new shall sentence (design R9) and the last quoted sentence: an update leaves a reaped transition reaped (an executor that re-evaluates every transition re-arms it, re-reaps it and emits a TransitionTimedOut storm: TIME_013_cycle_forbids_reEvaluateAll), and only a write of one of its arc places ends the reaped state (TIME_013_cycle_forbids_injectWritesAll: an injection into another place unreaps it). Line 4 also allows a lose step of the name: a firing pass drops only names of its ready order (EXEC-003 line 3), which holds only ready, hence armed, transitions (TIME-014 line 1), so in a run from an initial state a reaped name is never dropped; the line speaks of every state of R, and a state whose pass order holds a reaped name is not reachable. The reference drop turns the dropped name off whatever its status (loseStep, Reference/Exec.lean), so the line keeps that case instead of the quoted sentence naming it; the sentence's 'only a firing or an injected token' speaks of the runs an executor takes."
          "Line 5 is the shall sentence on a write, at the grain of the executor: a firing that writes an arc place (its start consumes or drains it, its settle deposits into it, a publication deposits into it) or an injected token that lands in one ends the reaped state, and the next update arms the transition with its reading if it is enabled (TIME-010's companion line 1 and EXEC-001 line 8). This is the glossary's injection clause of Write, which the Phase 1 relation leaves out (GlossaryTime.lean, Writes). An executor whose injection does not count as a write keeps the transition reaped for ever (TIME_013_cycle_forbids_injectNoWrite). AC4 (a reaped transition does not fire while none of its arc places is written; once one is written it is armed again with a fresh clock and may fire) is lines 3 to 5 with TIME-010's companion: TIME_013_cycle_nonvacuous reaps u, keeps it reaped through an update and through an injection into another place, ends the reaped state by an injection into its input place, arms it at the next update and starts it three ms later. AC4's two backends are CONC-020's and the precompiled link (ExecLink)."
          "The sentence 'While a transition is reaped, the transition shall not fire' is EXEC-003 line 1: a start needs a stamp, which a reaped name does not hold. The sentence 'If a reapable transition's elapsed time is greater than its latest bound plus the deadline tolerance, then the transition shall not fire' is line 1 with EXEC-001 line 2 and TIME-014 line 1: the deadline step reaps the transition before the pass, and the pass's order holds only ready transitions, which are not expired. Both stay quoted by the Phase 1 block. AC2 (the tolerance is configurable, 5 ms by default) and AC3 (an Exact transition past its target is not disabled) are the Phase 1 block's; AC3 follows here from line 2. The tolerance is TimedNet.tol; the examples take 0 (strict enforcement), which TIME-015 asks for under an injected clock."
          "Transition names are taken to be pairwise distinct (ruling D10, Cfg.WF.names, which the statement does not assume): the status is kept per name, and lines 3 to 5 judge the transition the net holds under the name (findT)."
  signoff "pending"
  statement : ∀ {N T : Type} [DecidableEq N], XRel N T → Prop :=
    fun R => ∀ C,
      (∀ ns u, u ∈ C.X.net.transitions → on (fun s s' => R C s (.deadline ns) s'), shall
        (fun s s' => Expired C.X (viewAt s s'.cyc) u → s'.st u.core.name = .reaped)) ∧
      (∀ ns n, on (fun s s' => R C s (.deadline ns) s'), shall (fun s s' => s'.M = s.M ∧
        (s'.st n ≠ s.st n → s'.st n = .reaped ∧
          ∃ u ∈ C.X.net.transitions, u.core.name = n ∧ Expired C.X (viewAt s s'.cyc) u))) ∧
      (∀ n u, findT C n = some u → on (fun s s' => R C s .update s'), shall (fun s s' =>
        s.st n = .reaped → s'.st n = .reaped)) ∧
      (∀ l n u, findT C n = some u → on (fun s s' => R C s l s'), shall (fun s s' =>
        s.st n = .reaped → s'.st n ≠ .reaped →
          l = .lose n ∨ ∃ p ∈ arcPlaces u, p ∈ cycWrites s l)) ∧
      (∀ l n u, findT C n = some u → on (fun s s' => R C s l s'), shall (fun s s' =>
        s.st n = .reaped → (∃ p ∈ arcPlaces u, p ∈ cycWrites s l) → s'.st n = .off))

/- The pinned readable form of TIME_013_cycle: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.TIME_013_cycle : {N T : Type} → [DecidableEq N] → XRel N T → Prop :=
fun {N T} [DecidableEq N] R =>
  ∀ (C : Cfg N T),
    (∀ (ns : List String),
        ∀ u ∈ C.X.net.transitions,
          on fun s s' => R C s (XLbl.deadline ns) s', shall fun s s' =>
            Expired C.X (viewAt s s'.cyc) u → s'.st u.core.name = Status.reaped) ∧
      (∀ (ns : List String) (n : String),
          on fun s s' => R C s (XLbl.deadline ns) s', shall fun s s' =>
            s'.M = s.M ∧
              (s'.st n ≠ s.st n →
                s'.st n = Status.reaped ∧
                  ∃ u ∈ C.X.net.transitions, u.core.name = n ∧ Expired C.X (viewAt s s'.cyc) u)) ∧
        (∀ (n : String) (u : Reference.Trans N),
            findT C n = some u →
              on fun s s' => R C s XLbl.update s', shall fun s s' => s.st n = Status.reaped → s'.st n = Status.reaped) ∧
          (∀ (l : XLbl N T) (n : String) (u : Reference.Trans N),
              findT C n = some u →
                on fun s s' => R C s l s', shall fun s s' =>
                  s.st n = Status.reaped →
                    s'.st n ≠ Status.reaped → l = XLbl.lose n ∨ ∃ p ∈ arcPlaces u, p ∈ cycWrites s l) ∧
            ∀ (l : XLbl N T) (n : String) (u : Reference.Trans N),
              findT C n = some u →
                on fun s s' => R C s l s', shall fun s s' =>
                  s.st n = Status.reaped → (∃ p ∈ arcPlaces u, p ∈ cycWrites s l) → s'.st n = Status.off
-/
#guard_msgs in #print TIME_013_cycle

/-- The names expired at the cycle reading of a state: applied to `atDeadline s`, the names the
reference deadline step reaps, expired at the deadline step's reading. -/
theorem tc_mem_expiredNames {N T : Type} [DecidableEq N] {C : Cfg N T} {s : XSt N T}
    {n : String} :
    n ∈ expiredNames refXPol C s ↔
      ∃ u ∈ C.X.net.transitions, u.core.name = n ∧ Expired C.X (viewAt s s.cyc) u := by
  simp only [expiredNames, List.mem_map, List.mem_filter, expiredAt_ref, ← expired_iff]
  constructor
  · rintro ⟨u, ⟨hu, hx⟩, rfl⟩; exact ⟨u, hu, rfl, hx⟩
  · rintro ⟨u, hu, rfl, hx⟩; exact ⟨u, ⟨hu, hx⟩, rfl⟩

/-- ✓ The reference executor satisfies the TIME-013 companion: its deadline step reaps exactly the
expired names (`tc_mem_expiredNames`), its update keeps a reaped name reaped (`tc_updSt_reaped`),
and every other step changes a reaped status only through the write of its label
(`tc_st_step`, `tc_unreap_left`, `tc_unreap_write`). -/
@[evidence holds TIME_013_cycle]
theorem TIME_013_cycle_reference {N T : Type} [DecidableEq N] :
    TIME_013_cycle (RefExec (N := N) (T := T)) := by
  refine fun C => ⟨fun ns u hu s s' h hx => ?_, fun ns n s s' h => ?_,
    fun n u hu s s' h hs => ?_, fun l n u hu s s' h hs hne => ?_,
    fun l n u hu s s' h hs hw => ?_⟩
  · obtain ⟨-, -, rfl, rfl⟩ := xstepW_deadline h
    have hm : u.core.name ∈ expiredNames refXPol C (atDeadline s) :=
      tc_mem_expiredNames.2 ⟨u, hu, rfl, hx⟩
    simp [hm]
  · obtain ⟨-, -, rfl, rfl⟩ := xstepW_deadline h
    refine ⟨rfl, fun hne => ?_⟩
    by_cases hm : n ∈ expiredNames refXPol C (atDeadline s)
    · exact ⟨by simp [hm], tc_mem_expiredNames.1 hm⟩
    · simp [hm] at hne
  · obtain ⟨-, -, rfl⟩ := xstepW_update h
    exact tc_updSt_reaped hu hs
  · rcases tc_st_step h with ⟨rfl, he⟩ | ⟨ns, rfl, he⟩ | ⟨m, rfl, he⟩ |
      ⟨m, sy, t, rest, rfl, ho, hn, hst, he⟩ | ⟨-, he⟩
    · rw [he] at hne; exact absurd (tc_updSt_reaped hu hs) hne
    · rw [he] at hne; by_cases hc : n ∈ ns <;> simp [hc, hs] at hne
    · by_cases hnm : n = m
      · exact Or.inl (by rw [hnm])
      · rw [he] at hne; simp [hnm, hs] at hne
    · have hnt : n ≠ t.core.name := by
        rintro rfl
        rw [← hn, hs] at hst
        simp [stampOf] at hst
      rw [he] at hne
      obtain ⟨u', hu', p, hp, hps⟩ := tc_unreap_left (tc_afterStart_reaped hnt hs) hne
      rw [hu] at hu'
      cases hu'
      exact Or.inr ⟨p, hp, by simp only [cycWrites, ho]; exact hps⟩
    · rw [he] at hne
      obtain ⟨u', hu', p, hp, hps⟩ := tc_unreap_left hs hne
      rw [hu] at hu'
      cases hu'
      exact Or.inr ⟨p, hp, hps⟩
  · obtain ⟨p, hp, hps⟩ := hw
    rcases tc_st_step h with ⟨rfl, -⟩ | ⟨ns, rfl, -⟩ | ⟨m, rfl, -⟩ |
      ⟨m, sy, t, rest, rfl, ho, hn, hst, he⟩ | ⟨-, he⟩
    · simp [cycWrites] at hps
    · simp [cycWrites] at hps
    · simp [cycWrites] at hps
    · have hnt : n ≠ t.core.name := by
        rintro rfl
        rw [← hn, hs] at hst
        simp [stampOf] at hst
      simp only [cycWrites, ho] at hps
      rw [he]
      exact tc_unreap_write (tc_afterStart_reaped hnt hs) hu hp hps
    · rw [he]
      exact tc_unreap_write hs hu hp hps

/-- A deadline step one cycle late: a transition is reaped only once its elapsed time is past the
bound plus the tolerance plus one. -/
def tc_reapLate {N T : Type} [DecidableEq N] : XPol N T :=
  { refXPol with expiredCmp := fun b el => decide (b + 1 < el) }

/-- A deadline step at the bound: a transition is reaped once its elapsed time reaches the bound
plus the tolerance (not strictly past it). -/
def tc_reapAtBound {N T : Type} [DecidableEq N] : XPol N T :=
  { refXPol with expiredCmp := fun b el => decide (b ≤ el) }

/-- An update that re-evaluates every transition, reaped or not (design R9). -/
def tc_reEvaluateAll {N T : Type} [DecidableEq N] : XPol N T :=
  { refXPol with updReaped := false }

/-- An injection that counts as a write of every place: it ends every reaped state. -/
def tc_injectWritesAll (C : Cfg Nat Nat) (s : XSt Nat Nat) : XLbl Nat Nat → Option (XSt Nat Nat)
  | .inject k => (xstep C s (.inject k)).map fun s1 =>
      { s1 with st := fun n => if s1.st n = .reaped then .off else s1.st n }
  | l => xstep C s l

/-- An injection that does not count as a write: it changes no status. -/
def tc_injectNoWrite (C : Cfg Nat Nat) (s : XSt Nat Nat) : XLbl Nat Nat → Option (XSt Nat Nat)
  | .inject k => (xstep C s (.inject k)).map fun s1 => { s1 with st := s.st }
  | l => xstep C s l

/-- The `Window(3, 5)` transition is a transition of its net. -/
theorem tc_U_mem : tc_U ∈ tc_cWin.X.net.transitions := List.mem_singleton_self _

/-- The first cycle of the window net: `u` armed at 0, not ready, the pass empty. -/
def tc_preW : List (XLbl Nat Nat) := tc_cyc ++ [.deadline [], .begin, .endPass]

/-- ✗ Reaping one cycle late violates the TIME-013 companion (line 1): at cycle reading 6 `u`,
`Window(3, 5)` armed at 0 with tolerance 0, is expired, and the deadline step leaves it armed. -/
@[evidence forbids TIME_013_cycle]
theorem TIME_013_cycle_forbids_reapLate :
    ¬ TIME_013_cycle
      (fun C s l s' => xstepW (tc_reapLate (N := Nat) (T := Nat)) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check (xstepW tc_reapLate) (C := tc_cWin)
    (o := tcRun (xstepW tc_reapLate) tc_cWin (xinit tc_m0 0)
      (tc_preW ++ [.delay 6, .wake] ++ tc_cyc))
    (l := .deadline [])
    (p := fun s s' => decide (Expired tc_cWin.X (viewAt s s'.cyc) tc_U) &&
      decide (s'.st "u" = .armed 0 false))
    (by decide +kernel)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  have : s'.st "u" = .reaped := (h tc_cWin).1 [] tc_U tc_U_mem s s' hs hp.1
  rw [hp.2] at this
  exact absurd this (by simp)

/-- ✗ Reaping at the bound violates the TIME-013 companion (line 2): at cycle reading 5 `u`,
`Window(3, 5)` armed at 0 with tolerance 0, has elapsed time exactly 5 and is not expired, and
the deadline step reaps it. -/
@[evidence forbids TIME_013_cycle]
theorem TIME_013_cycle_forbids_reapAtBound :
    ¬ TIME_013_cycle
      (fun C s l s' => xstepW (tc_reapAtBound (N := Nat) (T := Nat)) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check (xstepW tc_reapAtBound) (C := tc_cWin)
    (o := tcRun (xstepW tc_reapAtBound) tc_cWin (xinit tc_m0 0)
      (tc_preW ++ [.delay 5, .wake] ++ tc_cyc))
    (l := .deadline ["u"])
    (p := fun s s' => decide (s.st "u" = .armed 0 false) && decide (s'.st "u" = .reaped) &&
      !decide (Expired tc_cWin.X (viewAt s s'.cyc) tc_U))
    (by decide +kernel)
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at hp
  obtain ⟨-, hc⟩ := (h tc_cWin).2.1 ["u"] "u" s s' hs
  obtain ⟨-, u, hu, -, hx⟩ := hc (by rw [hp.1.1, hp.1.2]; simp)
  have : u = tc_U := List.eq_of_mem_singleton hu
  subst this
  exact hp.2 hx

/-- ✗ An update that re-evaluates a reaped transition violates the TIME-013 companion (line 3):
`u` is reaped at reading 6, nothing writes place 0, and the update of the next cycle arms it
again (the next deadline step would reap it again, a TransitionTimedOut storm). -/
@[evidence forbids TIME_013_cycle]
theorem TIME_013_cycle_forbids_reEvaluateAll :
    ¬ TIME_013_cycle
      (fun C s l s' => xstepW (tc_reEvaluateAll (N := Nat) (T := Nat)) C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check (xstepW tc_reEvaluateAll) (C := tc_cWin)
    (o := tcRun (xstepW tc_reEvaluateAll) tc_cWin (xinit tc_m0 0)
      (tc_preW ++ [.delay 6, .wake] ++ tc_cyc ++ [.deadline ["u"], .begin, .endPass, .delay 1,
        .wake, .endCompletions, .endPublications, .endEvents]))
    (l := .update)
    (p := fun s s' => decide (s.st "u" = .reaped) && decide (s'.st "u" = .armed 7 false))
    (by decide +kernel)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  have : s'.st "u" = .reaped := (h tc_cWin).2.2.1 "u" tc_U rfl s s' hs hp.1
  rw [hp.2] at this
  exact absurd this (by simp)

/-- ✗ An injection that ends every reaped state violates the TIME-013 companion (line 4): `u` is
reaped, an event is injected into place 1, on which `u` has no arc, and `u` is no longer
reaped. -/
@[evidence forbids TIME_013_cycle]
theorem TIME_013_cycle_forbids_injectWritesAll :
    ¬ TIME_013_cycle (fun C s l s' => tc_injectWritesAll C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check tc_injectWritesAll (C := tc_cWin)
    (o := tcRun tc_injectWritesAll tc_cWin (xinit tc_m0 0)
      (tc_preW ++ [.delay 6, .wake] ++ tc_cyc ++ [.deadline ["u"], .begin, .endPass,
        .request 1 9 .accepted, .wake, .endCompletions, .endPublications]))
    (l := .inject 0)
    (p := fun s s' => decide (s.st "u" = .reaped) && decide (s'.st "u" = .off) &&
      decide (cycWrites s (.inject 0) = [1]))
    (by decide +kernel)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  rcases (h tc_cWin).2.2.2.1 (.inject 0) "u" tc_U rfl s s' hs hp.1.1 (by rw [hp.1.2]; simp) with
    hl | ⟨q, hq, hq'⟩
  · simp at hl
  · rw [hp.2] at hq'
    simp only [arcPlaces, tc_U, tc_tr] at hq
    simp at hq hq'
    omega

/-- ✗ An injection that is not a write violates the TIME-013 companion (line 5): `u` is reaped,
an event is injected into its input place 0, and `u` stays reaped. -/
@[evidence forbids TIME_013_cycle]
theorem TIME_013_cycle_forbids_injectNoWrite :
    ¬ TIME_013_cycle (fun C s l s' => tc_injectNoWrite C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check tc_injectNoWrite (C := tc_cWin)
    (o := tcRun tc_injectNoWrite tc_cWin (xinit tc_m0 0)
      (tc_preW ++ [.delay 6, .wake] ++ tc_cyc ++ [.deadline ["u"], .begin, .endPass,
        .request 0 9 .accepted, .wake, .endCompletions, .endPublications]))
    (l := .inject 0)
    (p := fun s s' => decide (s.st "u" = .reaped) && decide (s'.st "u" = .reaped) &&
      decide (cycWrites s (.inject 0) = [0]))
    (by decide +kernel)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  have : s'.st "u" = .off := (h tc_cWin).2.2.2.2 (.inject 0) "u" tc_U rfl s s' hs hp.1.1
    ⟨0, by simp [arcPlaces, tc_U, tc_tr], by rw [hp.2]; simp⟩
  rw [hp.1.2] at this
  exact absurd this (by simp)

/-- The window net from its first cycle to the reap at reading 6, then two accepted events: one
for place 1 (no arc of `u`) and one for place 0 (`u`'s input place). -/
def tc_preReap : List (XLbl Nat Nat) :=
  tc_preW ++ [.delay 6, .wake] ++ tc_cyc ++ [.deadline ["u"], .begin, .endPass,
    .request 1 9 .accepted, .request 0 9 .accepted, .wake, .endCompletions, .endPublications]

/-- Every line of the TIME-013 companion is exercised by the reference, on `u`, `Window(3, 5)`
with tolerance 0 (AC1, AC4, TIME-015 AC6):
* at cycle reading 5, elapsed time exactly the bound, the deadline step reaps nothing;
* at cycle reading 6 it reaps `u` and keeps the marking;
* the update of the next cycle keeps `u` reaped though it is enabled;
* an event injected into place 1 keeps it reaped, one injected into its input place 0 ends the
  reaped state;
* the next update arms `u` with its reading 6, and `u` starts at cycle reading 9. -/
@[evidence nonvacuous TIME_013_cycle]
theorem TIME_013_cycle_nonvacuous :
    (∃ s s', RefExec tc_cWin s (.deadline []) s' ∧ s.cyc = 5 ∧ s.st "u" = .armed 0 false ∧
      s'.st "u" = .armed 0 false) ∧
    (∃ s s', RefExec tc_cWin s (.deadline ["u"]) s' ∧ s.cyc = 6 ∧ s'.st "u" = .reaped ∧
      s'.M = s.M) ∧
    (∃ s s', RefExec tc_cWin s .update s' ∧ s.st "u" = .reaped ∧
      enabledNA (qCount s.M) tc_U.core = true ∧ s'.st "u" = .reaped) ∧
    (∃ s s', RefExec tc_cWin s (.inject 0) s' ∧ s.st "u" = .reaped ∧ s'.st "u" = .reaped) ∧
    (∃ s s', RefExec tc_cWin s (.inject 1) s' ∧ s.st "u" = .reaped ∧ s'.st "u" = .off) ∧
    (∃ s s', RefExec tc_cWin s .update s' ∧ s.st "u" = .off ∧ s'.st "u" = .armed 6 false) ∧
    (∃ s s', RefExec tc_cWin s (.start "u" false) s' ∧ s.cyc = 9) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := tc_cWin)
      (o := xrun tc_cWin (xinit tc_m0 0) (tc_preW ++ [.delay 5, .wake] ++ tc_cyc))
      (l := .deadline [])
      (p := fun s s' => s.cyc == 5 && decide (s.st "u" = .armed 0 false) &&
        decide (s'.st "u" = .armed 0 false))
      (by decide +kernel)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
    exact ⟨s, s', hs, hp.1.1, hp.1.2, hp.2⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := tc_cWin)
      (o := xrun tc_cWin (xinit tc_m0 0) (tc_preW ++ [.delay 6, .wake] ++ tc_cyc))
      (l := .deadline ["u"])
      (p := fun s s' => s.cyc == 6 && decide (s'.st "u" = .reaped))
      (by decide +kernel)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
    exact ⟨s, s', hs, hp.1, hp.2, by obtain ⟨-, -, -, rfl⟩ := xstepW_deadline hs; rfl⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := tc_cWin)
      (o := xrun tc_cWin (xinit tc_m0 0)
        (tc_preW ++ [.delay 6, .wake] ++ tc_cyc ++ [.deadline ["u"], .begin, .endPass, .delay 1,
          .wake, .endCompletions, .endPublications, .endEvents]))
      (l := .update)
      (p := fun s s' => decide (s.st "u" = .reaped) && enabledNA (qCount s.M) tc_U.core &&
        decide (s'.st "u" = .reaped))
      (by decide +kernel)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    exact ⟨s, s', hs, hp.1.1, hp.1.2, hp.2⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := tc_cWin)
      (o := xrun tc_cWin (xinit tc_m0 0) tc_preReap)
      (l := .inject 0)
      (p := fun s s' => decide (s.st "u" = .reaped) && decide (s'.st "u" = .reaped))
      (by decide +kernel)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    exact ⟨s, s', hs, hp.1, hp.2⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := tc_cWin)
      (o := xrun tc_cWin (xinit tc_m0 0) (tc_preReap ++ [.inject 0]))
      (l := .inject 1)
      (p := fun s s' => decide (s.st "u" = .reaped) && decide (s'.st "u" = .off))
      (by decide +kernel)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    exact ⟨s, s', hs, hp.1, hp.2⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := tc_cWin)
      (o := xrun tc_cWin (xinit tc_m0 0) (tc_preReap ++ [.inject 0, .inject 1, .endEvents]))
      (l := .update)
      (p := fun s s' => decide (s.st "u" = .off) && decide (s'.st "u" = .armed 6 false))
      (by decide +kernel)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    exact ⟨s, s', hs, hp.1, hp.2⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := tc_cWin)
      (o := xrun tc_cWin (xinit tc_m0 0)
        (tc_preReap ++ [.inject 0, .inject 1, .endEvents, .update, .deadline [], .begin, .endPass,
          .delay 3, .wake] ++ tc_cyc ++ [.deadline [], .begin]))
      (l := .start "u" false)
      (p := fun s _ => s.cyc == 9)
      (by decide +kernel)
    simp only [beq_iff_eq] at hp
    exact ⟨s, s', hs, hp⟩

/-! ## TIME-015: the readings of the firing clock, and the re-check after a wait -/

section Wait

variable {N T : Type}

/-- A line `after T, until G, never B` holds of every run of `E` when some invariant `I` of the
states holds after every `T` step, is kept by every step that is not a `G` step, and allows no
`B` step. -/
theorem tc_aun_of_inv {E : XRel N T} {C : Cfg N T} (I : XSt N T → Prop)
    {trig go bad : XStep N T → Bool}
    (hbad : ∀ s l s', E C s l s' → I s → bad (s, l, s') = false)
    (hkeep : ∀ s l s', E C s l s' → I s → go (s, l, s') = false → I s')
    (htrig : ∀ s l s', E C s l s' → trig (s, l, s') = true → I s') :
    ∀ s0 tr, XRun E C s0 tr → AfterUntilNever trig go bad tr := by
  suffices H : ∀ (tr : List (XStep N T)) (s0 : XSt N T) (b : Bool), XRun E C s0 tr →
      (b = true → I s0) → (afterUntilNever trig go bad).scan b tr = true from
    fun s0 tr h => H tr s0 false h (by simp)
  intro tr
  induction tr with
  | nil => intro _ _ _ _; rfl
  | cons e rest ih =>
    intro s0 b hr hb
    obtain ⟨s, l, s'⟩ := e
    obtain ⟨he, hE, hr'⟩ := hr
    simp only at he hE hr'
    subst he
    simp only [Watch.scan, afterUntilNever, Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨?_, ih s' _ hr' ?_⟩
    · cases b
      · simp
      · simp [hbad _ _ _ hE (hb rfl)]
    · intro hn
      simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hn
      rcases hn with ⟨h1, h2⟩ | h1
      · exact hkeep _ _ _ hE (hb h1) h2
      · exact htrig _ _ _ hE h1

end Wait

requirement TIME_015_cycle
  id "TIME-015"
  title "Injectable Clock (executor cycle)"
  kind A
  scope "all executors, on the default or an injected firing clock"
  source verbatim "spec/03-timing.md"
  quote "*While* an executor runs on an injected clock, successive readings of its firing clock *shall* be non-decreasing."
        "*When* the executor's wait completes, the executor *shall* re-check its boundary conditions before it fires any transition, so an armed transition *shall not* fire before its earliest bound because a wait completed early ([TIME-010])."
        "The executor MUST re-check its boundary conditions and MUST NOT treat \"the wait completed\" as \"the boundary is reached\"."
  reading "For every executor R and every configuration C:"
          "no step lowers the host's reading of the firing clock;"
          "in every run of R, after a step that completes the wait (a wake), no start happens before the next update."
  assumes "The model is an executor R : XRel N T (glossary GlossaryExec.lean): R C s l s' says that under configuration C the step labelled l leads from executor state s to s'. The state holds two readings of the one firing clock: now, the host's present reading, which only the outside delay step advances, and cyc, the cycle reading, which the enablement update sets and the deadline step may move to a later reading, and at which the deadline step, the ready order of the pass and the park decision judge (TIME-010's companion lines 3 to 5, ruling D61 (c)). The model does not say where the readings come from, so line 1 holds of the default clock as of an injected one: the quoted sentence opens with 'While an executor runs on an injected clock' because an injected clock is the one the host can get wrong; the default firing clocks are monotonic sources (System.nanoTime, performance.now, a monotonic Instant), so the line asks nothing of them they do not do. The wait of step 6 is park and wake; a wake is offered at any time in the wait, so a timer that fires early and a spurious completion are both a wake. The witness is the reference executor RefExec (Reference/Exec.lean)."
          "This is the companion of the Phase 1 block TIME_015 (ruling D33 (a), design NR-1), which states the readings and the re-check on the atomic timed step and defers the executor loop to the cycle relation. Line 1 is the first shall sentence on the host's reading: a clock that goes back breaks it (TIME_015_cycle_forbids_rewind). Which reading each step of a cycle judges at (ruling D61 (c)) is an executor rule for every executor on any clock, so it is stated by TIME-010 (a MUST) and its companion, lines 3 to 5, not here: the SHOULD priority of TIME-015 does not carry it. With line 1 those lines make the readings of successive cycles non-decreasing."
          "Line 2 is the second shall sentence and contract 3 (spurious completion): after the wait completes the loop runs steps 1 to 4 again, so the enablement update re-reads the clock and the deadline step and the ready order of the next pass are judged at that reading, and a transition whose earliest bound a wait that completed early did not reach is not ready in that pass (TIME-014 line 1). An executor that trusts the wait and goes straight to its firing pass breaks it (TIME_015_cycle_forbids_wakeToPass). That the update comes before the deadline step and the deadline step before the pass is EXEC-001 lines 1 and 2, whose trigger includes the wake."
          "AC4 (a wait that completes early fires nothing early) is TIME_015_cycle_nonvacuous: t, Delayed(5) and armed at 0, parks with a timer of 5, the wait completes at 2, the update takes reading 2 and the pass offers nothing, the next wait completes at 5 and t starts. AC6 (with tolerance 0, a Deadline transition is reaped on the first cycle strictly past its bound, not on one that observes exactly its bound) is TIME-013's companion line 1 at the reading of the deadline step (TIME-010's companion lines 3 and 4), and TIME_013_cycle_nonvacuous shows both cycles. AC7 (a boundary already due advances on the next cycle) is CONC-010's park guard: the executor does not wait while a transition is Ready or Expired at the cycle reading, and its timer is at most the next boundary plus the timer resolution. AC8 (a completing action, an injected event, a drain and a close wake the wait) is CONC-010's wake line. AC11 (an injection or a completion from inside the wait only enqueues, and is taken in by a later step 1 or step 2) is CONC-001 line 1 (an outside step changes neither the marking nor a clock status) with ENV-003 and EXEC-001; ruling D70 (a) lets the wait itself take the queued item and go on to step 1. AC13 (executor-stamped tokens carry the injected epoch clock) is the CORE-011 epoch slice (W11). AC5 (abort on shutdown), AC9 (no cost on the default path), AC15 (an absent boundary suspends) and the seam's shape (both halves of the wait, the readiness predicate, the two time bases) are properties of the host interface, not of a step relation; the wait without a timer is park none, which CONC-010 allows only when no boundary is ahead. AC1, AC2, AC3, AC10, AC12 and AC14 are the Phase 1 block's."
  signoff "pending"
  statement : ∀ {N T : Type} [DecidableEq N], XRel N T → Prop :=
    fun R => ∀ C,
      (∀ l, on (fun s s' => R C s l s'), shall (fun s s' => s.now ≤ s'.now)) ∧
      (∀ s0 tr, XRun R C s0 tr → (after tcIsWake, until isUpdate, never isStart) tr)

/- The pinned readable form of TIME_015_cycle: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.TIME_015_cycle : {N T : Type} → [DecidableEq N] → XRel N T → Prop :=
fun {N T} [DecidableEq N] R =>
  ∀ (C : Cfg N T),
    (∀ (l : XLbl N T), on fun s s' => R C s l s', shall fun s s' => s.now ≤ s'.now) ∧
      ∀ (s0 : XSt N T) (tr : List (XStep N T)), XRun R C s0 tr → (after tcIsWake, until isUpdate, never isStart) tr
-/
#guard_msgs in #print TIME_015_cycle

/-- ✓ The reference executor satisfies the TIME-015 companion: only a delay moves the host
reading, forward (`tc_xstepW_now`); and from a wake to the next update the loop stays in steps 1,
1b, 2 and the update, where no start is offered (`tc_beforeUpdate_step`). -/
@[evidence holds TIME_015_cycle]
theorem TIME_015_cycle_reference {N T : Type} [DecidableEq N] :
    TIME_015_cycle (RefExec (N := N) (T := T)) := by
  refine fun C => ⟨fun l s s' h => ?_,
    tc_aun_of_inv (fun s => tcBeforeUpdate s.phase = true) ?_ ?_ ?_⟩
  · by_cases hd : ∃ δ, l = .delay δ
    · obtain ⟨δ, rfl⟩ := hd
      rw [xstepW_delay h]
      exact Nat.le_add_right _ _
    · exact Nat.le_of_eq (tc_xstepW_now h fun δ he => hd ⟨δ, he⟩).symm
  · intro s l s' h hI
    cases l with
    | start n sy =>
      obtain ⟨t, rest, -, hph, -⟩ := startStep_some h
      rw [hph] at hI
      exact absurd hI (by decide)
    | _ => rfl
  · intro s l s' h hI hgo
    have hu : l ≠ .update := by
      rintro rfl
      simp [isUpdate] at hgo
    exact tc_beforeUpdate_step h hI hu
  · intro s l s' h ht
    cases l with
    | wake =>
      obtain ⟨-, -, rfl⟩ := wakeStep_some h
      rfl
    | _ => simp [tcIsWake] at ht

/-- A clock that goes back: a delay lowers the host reading. -/
def tc_rewind (C : Cfg Nat Nat) (s : XSt Nat Nat) : XLbl Nat Nat → Option (XSt Nat Nat)
  | .delay δ => some { s with now := s.now - δ }
  | l => xstep C s l

/-- An executor that trusts its wait: a wake goes straight to the termination test and the firing
pass, judged at the present reading, skipping steps 1 to 4. -/
def tc_wakeToPass (C : Cfg Nat Nat) (s : XSt Nat Nat) : XLbl Nat Nat → Option (XSt Nat Nat)
  | .wake => (xstep C s .wake).map fun s1 => { s1 with phase := .test, cyc := s.now }
  | l => xstep C s l

/-- ✗ A clock that goes back violates the TIME-015 companion (line 1): from host reading 5 a
delay of 3 leaves the reading at 2. -/
@[evidence forbids TIME_015_cycle]
theorem TIME_015_cycle_forbids_rewind :
    ¬ TIME_015_cycle (fun C s l s' => tc_rewind C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check tc_rewind (C := tc_cDel)
    (o := some (xinit tc_m0 5)) (l := .delay 3)
    (p := fun s s' => s.now == 5 && s'.now == 2) (by decide +kernel)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  have : s.now ≤ s'.now := (h tc_cDel).1 (.delay 3) s s' hs
  omega

/-- ✗ Trusting the wait violates the TIME-015 companion (line 2): `t`, `Delayed(5)` and armed at
0, parks with a timer of 5; the wait completes at 5 and `t` starts with no update between. -/
@[evidence forbids TIME_015_cycle]
theorem TIME_015_cycle_forbids_wakeToPass :
    ¬ TIME_015_cycle (fun C s l s' => tc_wakeToPass C s l = some s') := by
  intro h
  obtain ⟨s, tr, hr, hp⟩ := tc_trace_check tc_wakeToPass (C := tc_cDel) (s0 := xinit tc_m0 0)
    (pre := tc_cyc ++ [.deadline [], .begin, .endPass, .park (some 5), .delay 5])
    (body := [.wake, .begin, .start "t" false])
    (p := fun tr => !decide (AfterUntilNever tcIsWake isUpdate isStart tr))
    (by decide +kernel)
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hp
  exact hp ((h tc_cDel).2 s tr hr)

/-- The run of AC4: `t`, `Delayed(5)` and armed at 0, parks with a timer of 5; the wait completes
early, at 2; the cycle at reading 2 offers nothing and parks with a timer of 3; the wait completes
at 5, and the cycle at reading 5 starts `t`. -/
def tc_runAC4 : List (XLbl Nat Nat) :=
  tc_cyc ++ [.deadline [], .begin, .endPass, .park (some 5), .delay 2, .wake] ++ tc_cyc ++
    [.deadline [], .begin, .endPass, .park (some 3), .delay 3, .wake] ++ tc_cyc ++
    [.deadline [], .begin, .start "t" false]

/-- Every line of the TIME-015 companion is exercised by the reference, on AC4's run: a delay
advances the host reading; the update after the early wake takes reading 2 and its pass offers
nothing while `t` is armed at 0; the whole run, with two wakes and a start, is a run of the
reference; and `t` starts at cycle reading 5. -/
@[evidence nonvacuous TIME_015_cycle]
theorem TIME_015_cycle_nonvacuous :
    (∃ s s', RefExec tc_cDel s (.delay 2) s' ∧ s'.now = s.now + 2) ∧
    (∃ s s', RefExec tc_cDel s .update s' ∧ s.now = 2 ∧ s'.cyc = 2) ∧
    (∃ s s', RefExec tc_cDel s .begin s' ∧ s.cyc = 2 ∧ s.st "t" = .armed 0 false ∧
      s'.order = []) ∧
    (∃ s0 tr, XRun RefExec tc_cDel s0 tr ∧ tr.any tcIsWake = true ∧ tr.any isStart = true) ∧
    (∃ s s', RefExec tc_cDel s (.start "t" false) s' ∧ s.cyc = 5) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := tc_cDel)
      (o := xrun tc_cDel (xinit tc_m0 0) (tc_cyc ++ [.deadline [], .begin, .endPass,
        .park (some 5)]))
      (l := .delay 2) (p := fun s s' => s'.now == s.now + 2) (by decide +kernel)
    simp only [beq_iff_eq] at hp
    exact ⟨s, s', hs, hp⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := tc_cDel)
      (o := xrun tc_cDel (xinit tc_m0 0) (tc_cyc ++ [.deadline [], .begin, .endPass,
        .park (some 5), .delay 2, .wake, .endCompletions, .endPublications, .endEvents]))
      (l := .update) (p := fun s s' => s.now == 2 && s'.cyc == 2) (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', hs, hp.1, hp.2⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := tc_cDel)
      (o := xrun tc_cDel (xinit tc_m0 0) (tc_cyc ++ [.deadline [], .begin, .endPass,
        .park (some 5), .delay 2, .wake] ++ tc_cyc ++ [.deadline []]))
      (l := .begin)
      (p := fun s s' => s.cyc == 2 && decide (s.st "t" = .armed 0 false) && s'.order.isEmpty)
      (by decide +kernel)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.isEmpty_iff] at hp
    exact ⟨s, s', hs, hp.1.1, hp.1.2, hp.2⟩
  · have hx : (xtrace tc_cDel (xinit tc_m0 0) tc_runAC4).map
        (fun tr => tr.any tcIsWake && tr.any isStart) = some true := by decide +kernel
    cases ht : xtrace tc_cDel (xinit tc_m0 0) tc_runAC4 with
    | none => simp [ht] at hx
    | some tr =>
      simp only [ht, Option.map_some, Option.some.injEq, Bool.and_eq_true] at hx
      exact ⟨_, tr, xtrace_run ht, hx.1, hx.2⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := tc_cDel)
      (o := xrun tc_cDel (xinit tc_m0 0) (tc_runAC4.dropLast))
      (l := .start "t" false) (p := fun s _ => s.cyc == 5) (by decide +kernel)
    simp only [beq_iff_eq] at hp
    exact ⟨s, s', hs, hp⟩

end Libpetri.Spec
