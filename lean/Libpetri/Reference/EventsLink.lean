import Libpetri.Reference.Events
import Libpetri.Reference.Replay
import Libpetri.Reference.ExecLink
import Libpetri.Spec.Req.TIME_cycle
import Libpetri.Spec.Req.EVT_011

set_option linter.missingDocs true

/-!
# Links of the event model (wave W7)

The links that tie the executor events (`Reference/Events.lean`) to the models they sit on, so
that the event requirements and the execution requirements speak of one executor, and the
executor events and the store tier speak of one event type (design events.md, section 3).

* **E1, erasure** (`emitExec_erase`, `refEvExec_erase`): an executor with events built by
  `emitExec` steps exactly as the reference executor `RefExec`, whatever it emits. So the event
  layer adds no step and removes none: the consistency theorem's conjunct `V.erase = E` holds of
  the reference with `E = RefExec`, the executor every execution block holds of.
* **E2, the queue firing** (`segment_events`, `qFireEvs`, `RefQEv`, `refQEv_tier1`): on an L2
  segment (a start, steps that leave the marking alone, the commit of the started firing;
  `segment_refQFire`) the events of the start and of the commit are the event image of one
  `RefQFire` step, followed by the one `TransitionCompleted`. On that image the tier-1 removal and
  addition lines of the evt-b spike hold.
* **E3, the timed step** (`atomic_preUpdate`, `atomic_update_events`): on an L3 segment (one pass
  with one synchronous firing and the next update; `atomic_refTStep`) the update announces each
  transition as the atomic grain does (the evt-a spike's `refEmit`), except that a transition that
  lost the pass recheck is announced with `TransitionEnabled` where the atomic grain says
  `TransitionClockRestarted` (clash evt-a#2, [TIME-012] AC5 and AC6; decided in
  `atomic_loser_run`).
* **E4, the replay** (`ReplayAgrees`, `replayAgrees_step`, `refReplay_agrees`): replaying a run's
  events with [EVT-032]'s replay (`NetEvent.replayView`) gives, on every declared place, the
  tokens the executor holds, and an enabled set that contains every armed transition, provided
  the boot carries the snapshot of the initial marking (every runtime's emission;
  `replayAgrees_needs_snapshot` shows an emission without it fails, clash evt-c#11).
  `cov_replay_end` shows the enabled set is strictly wider (ruling D83 (a)).
* **E5, coverage** (`EvCovers`, `refEvCovers`, `evCovers_excludes_silent`): one decided trace of
  the reference holds all twelve kinds the executor tier emits (every kind but `LogMessage`, for
  which the executor has no label), and an executor that emits nothing fails the condition.
* **E6, scope** (`polBlind`, `refEmitW_polBlind`, `refBoot_polBlind`): the two emission variants
  emit the same events at every step once the three points of `EvPol` are left out (snapshots,
  where `ActionTimedOut` is emitted, the completion of a timeout deposit; the runtimes differ in
  the last two), which is why each main
  block's `_rust` holds theorem goes through with the same proof.
* **The replay view** (`NetEvent.toRec`, `NetEvent.replayView`): the map that forgets what the
  replay does not read (tokens, durations, payload lists; a snapshot's queues become counts),
  so the replay of [EVT-032] reads an executor event through `recView`. It keeps the kind
  (`NetEvent.toRec_kind`): the executor events, the recorded events of the replay, the level
  table of [EVT-023] and the query helpers of [EVT-030] read one kind type.

This file imports two blocks for their lemmas about the reference: `TIME_cycle` (`tc_st_step`,
what each step does to the clock statuses) and `EVT_011` (`evt011_refStep`, what a deposit
appends). No block imports this file; the consistency theorem of the events does.
-/

namespace Libpetri.Reference

open Libpetri Libpetri.Spec Libpetri.Novel.Seam

variable {N T : Type} [DecidableEq N] [Ord N]

/-! ## E1: the event layer adds and removes no step -/

omit [Ord N] in
/-- **E1**: an executor with events built by `emitExec` erases to the reference executor: it has
a step from `s` with label `l` to `s'` (with some history and events) exactly when `RefExec`
has it. -/
theorem emitExec_erase (boot : Cfg N T → QMarking N T → List (NetEvent N T))
    (emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)) :
    (emitExec boot emit).erase = RefExec := by
  funext C s l s'
  apply propext
  constructor
  · rintro ⟨_, _, h, -⟩
    exact h
  · intro h
    exact ⟨[], _, h, rfl⟩

/-- **E1 for the reference**: under every emission variant, the reference executor with events
erases to `RefExec`. -/
theorem refEvExec_erase (P : EvPol) : (refEvExec (N := N) (T := T) P).erase = RefExec :=
  emitExec_erase _ _

/-- A step of the reference executor with events is a step of `RefExec` that appends the
reference emission, under any history. -/
theorem refEvExec_step_iff (P : EvPol) (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T)
    (l : XLbl N T) (evs : List (NetEvent N T)) (s' : XSt N T) :
    (refEvExec P).step C H s l evs s' ↔ RefExec C s l s' ∧ evs = refEmitW P C H s l s' :=
  Iff.rfl


/-! ## E2: the events of a start and its commit are the event image of one queue firing -/

section E2

/-- **The event image of a queue firing** (`RefQFire`): firing `t` from `M` with emission `e`
reports one `TokenRemoved` per token it removes (input places in declaration order, then reset
places), then `TransitionStarted` with those tokens, then one `TokenAdded` per token of `e` in
emission order. This is the tier-1 emission of the evt-b spike (`obsQ`), in the place order of
the executors (design events.md, SC-4). -/
def qFireEvs (M : QMarking N T) (t : Trans N) (e : List (N × T)) : List (NetEvent N T) :=
  removedEvs M t ++ [.transitionStarted t.core.name (removedListDecl M t)] ++ addedEvs e

/-- **The queue firing with its events**: a `RefQFire` step that appends `qFireEvs`. -/
def RefQEv (t : Trans N) (M : QMarking N T) (δ : QDelivered N T) (e : List (N × T))
    (M' : QMarking N T) (evs : List (NetEvent N T)) : Prop :=
  RefQFire t M δ e M' ∧ evs = qFireEvs M t e

omit [Ord N] in
/-- The `TokenRemoved` events of the image, read at `p`: the tokens the firing removes from `p`. -/
theorem removedAt_qFireEvs (M : QMarking N T) (t : Trans N) (e : List (N × T)) (p : N) :
    removedAt (qFireEvs M t e) p = qRemoved M t p := by
  have h1 : removedAt ([.transitionStarted t.core.name (removedListDecl M t)] :
      List (NetEvent N T)) p = [] := rfl
  have h2 : removedAt (addedEvs e : List (NetEvent N T)) p = [] :=
    removedAt_of_none _ (fun x hx => by rw [kind_of_mem_addedEvs hx]; decide) p
  rw [qFireEvs, removedAt_append, removedAt_append, removedAt_removedEvs, h1, h2]
  simp

omit [Ord N] in
/-- The `TokenAdded` events of the image, read at `p`: the tokens `e` emits to `p`, in order. -/
theorem addedAt_qFireEvs (M : QMarking N T) (t : Trans N) (e : List (N × T)) (p : N) :
    addedAt (qFireEvs M t e) p = qEmittedTo e p := by
  have h0 : addedAt (removedEvs M t) p = [] :=
    evt011_addedAt_of_none _ (fun x hx => by rw [kind_of_mem_removedEvs hx]; decide) p
  have h1 : addedAt ([.transitionStarted t.core.name (removedListDecl M t)] :
      List (NetEvent N T)) p = [] := rfl
  rw [qFireEvs, evt011_addedAt_append, evt011_addedAt_append, h0, h1,
    evt011_addedAt_addedEvs]
  simp

omit [Ord N] in
/-- **The tier-1 removal and addition lines hold of the image** (the evt-b spike's `EVT_012` and
`EVT_011_fire` over the queue firing): per place, the tokens of the `TokenRemoved` events followed
by what the consume leaves are the queue before the firing, and what the consume leaves followed by
the tokens of the `TokenAdded` events is the queue after it. -/
theorem refQEv_tier1 {t : Trans N} {M : QMarking N T} {δ : QDelivered N T} {e : List (N × T)}
    {M' : QMarking N T} {evs : List (NetEvent N T)} (h : RefQEv t M δ e M' evs) (p : N) :
    removedAt evs p ++ qConsume M t p = M p ∧ qConsume M t p ++ addedAt evs p = M' p := by
  obtain ⟨⟨-, -, -, rfl⟩, rfl⟩ := h
  refine ⟨by rw [removedAt_qFireEvs, qRemoved_append_qConsume], ?_⟩
  rw [addedAt_qFireEvs, qFire, qAppend_apply]

/-- **E2, the event image of L2.** Take an L2 segment of the reference executor (`segment_refQFire`,
`ExecLink.lean`): a start from a pass state with no same-pass deposit, then steps that leave the
marking alone, then the commit of the started firing. Under every emission variant and every
history, the events of the start step followed by the events of the commit step are the event
image of the queue firing (`qFireEvs`) followed by the one `TransitionCompleted` of the firing; with
an offered emission the two steps are one `RefQEv` step, the queue firing with its events.

For example, a start of `r` that takes the token 1 of place 0, followed by the inline commit of
the token 9 for place 0, reports `TokenRemoved 0 1`, `TransitionStarted r [(0, 1)]`,
`TokenAdded 0 9` and `TransitionCompleted r [(0, 9)]`, which is what the queue firing of `r`
reports plus the completion. -/
theorem segment_events (P : EvPol) {C : Cfg N T} {s s' : XSt N T} {n : String} {sy : Bool}
    {i : Nat} {mid : List (XLbl N T)} (h : xrun C s (.start n sy :: mid ++ [.commit i]) = some s')
    (hd : ∀ p, s.delta p = 0) (hmid : ∀ l ∈ mid, l.marks = false)
    (hfresh : ∀ g ∈ s.fl, g.id ≠ s.nextId) (hi : i = s.nextId) :
    ∃ (t : Trans N) (f : Firing N T) (e : List (N × T)) (s₁ s₂ : XSt N T),
      xstep C s (.start n sy) = some s₁ ∧ xrun C s₁ mid = some s₂ ∧
      xstep C s₂ (.commit i) = some s' ∧ s.order.head? = some t ∧ t.core.name = n ∧
      f.t = t ∧ f.out = some (.ok e) ∧ s'.M = qFire s.M t e ∧
      (∀ H H', refEmitW P C H s (.start n sy) s₁ ++ refEmitW P C H' s₂ (.commit i) s' =
        qFireEvs s.M t e ++ [.transitionCompleted n e (s₂.now - f.start)]) ∧
      (OfferedEmission s t e → RefQEv t s.M f.deliv e s'.M (qFireEvs s.M t e)) := by
  rw [List.cons_append] at h
  obtain ⟨s₁, h1, h⟩ := xrun_cons.mp h
  obtain ⟨s₂, h2, h3⟩ := xrun_append.mp h
  obtain ⟨s₃, hc, h4⟩ := xrun_cons.mp h3
  cases h4
  obtain ⟨f, e, hf, hout, -, -, -, -⟩ := refExec_commit hc
  obtain ⟨t, hhd, hn, hft, -, hM, hq⟩ := segment_refQFire_split (xrun_cons.mpr ⟨s₁, h1, h2⟩)
    hc hf hout hd hmid hfresh hi
  refine ⟨t, f, e, s₁, s₂, h1, h2, hc, hhd, hn, hft, hout, hM, fun H H' => ?_,
    fun ho => ⟨hq ho, rfl⟩⟩
  cases ho : s.order with
  | nil => rw [ho] at hhd; cases hhd
  | cons t' rest =>
    rw [ho] at hhd
    obtain rfl : t' = t := Option.some.inj hhd
    rw [refEmitW_start P C H ho, vis_of_delta_zero hd]
    have hc' : refEmitW P C H' s₂ (.commit i) s' =
        addedEvs e ++ [.transitionCompleted n e (s₂.now - f.start)] := by
      simp only [refEmitW, hf, hout, hft, hn]
    rw [hc', qFireEvs, hn]
    simp

end E2

/-! ## E3: the announcements of an atomic segment are the atomic grain's, but for recheck losers -/

section E3

omit [Ord N] in
/-- **The state before the update of an L3 segment** (`atomicLabels`, `ExecLink.lean`): from a
state with no firing in flight and no restart flag pending, the segment's last step is an update
from a state `sU` that holds the queue firing's marking, has nothing in flight, the reading of the
segment's start, the started transition off, and every other name of the net either as one atomic
firing leaves it (`preOf`: the restart flag where the start's consumption disables it, the end of
a reap where the firing writes an arc place) or, if it lost the pass recheck, off; a loser was
armed with its clock running and disabled by the start's consumption. -/
theorem atomic_preUpdate {C : Cfg N T} (hN : NamesDistinct C.X) {s s' : XSt N T} {n : String}
    {i : Nat} {e : List (N × T)} {ls : List String} (hfl : s.fl = [])
    (hnr : ∀ x k, s.st x ≠ .armed k true) (h : xrun C s (atomicLabels n i e ls) = some s') :
    ∃ (t : Trans N) (sU : XSt N T), t ∈ C.X.net.transitions ∧ t.core.name = n ∧
      xstep C sU .update = some s' ∧ sU.M = qFire s.M t e ∧ sU.fl = [] ∧
      sU.st t.core.name = .off ∧
      ∀ x u, findT C x = some u → x ≠ t.core.name →
        sU.st x = preOf (s.st x) (enabledNA (mid t (qCount s.M)) u.core)
            (writesArc t (e.map Prod.fst) u) ∨
        (sU.st x = .off ∧ (∃ k, s.st x = .armed k false) ∧
          enabledNA (mid t (qCount s.M)) u.core = false) := by
  unfold atomicLabels at h
  obtain ⟨sA, hA, hT⟩ := xrun_append.mp h
  obtain ⟨s₅, h5, hL⟩ := xrun_append.mp hA
  obtain ⟨s₃, h3, hRC⟩ := xrun_append.mp h5
  obtain ⟨s₂, h2, hW⟩ := xrun_append.mp h3
  obtain ⟨s₁, hb, h2⟩ := xrun_cons.mp h2
  obtain ⟨s₂', hs, h2⟩ := xrun_cons.mp h2
  obtain rfl : s₂' = s₂ := Option.some.inj h2
  obtain ⟨-, -, -, -, hs1⟩ := xstepW_begin hb
  have hd1 : ∀ p, s₁.delta p = 0 := by rw [hs1]; intro; rfl
  have hs1M : s₁.M = s.M := by rw [hs1]
  have hs1st : s₁.st = s.st := by rw [hs1]
  have hs1o : s₁.order = readyOrder C s := by rw [hs1]
  have hs1fl : s₁.fl = [] := by rw [hs1, hfl]
  have hs1ph : s₁.phase = .pass := by rw [hs1]
  obtain ⟨t, rest, ho, -, -, -, hn, -, -, rfl⟩ := startStep_some (P := refXPol) hs
  rw [hs1o] at ho
  obtain ⟨ht, -⟩ :=
    mem_readyOrder (show t ∈ readyOrder C s by rw [ho]; exact List.mem_cons_self)
  have hW' := writes_single e (by show s₁.fl ++ _ = _; rw [hs1fl]; rfl) hW
  subst hW'
  obtain ⟨s₄, hr, hrest⟩ := xrun_cons.mp hRC
  obtain ⟨s₅', hcm, h5'⟩ := xrun_cons.mp hrest
  obtain rfl : s₅ = s₅' := (Option.some.inj h5').symm
  obtain ⟨f, hf, -, rfl⟩ := retStep_some (show retStep _ i true = some s₄ from hr)
  dsimp only at hf
  simp only [List.find?_cons, List.find?_nil] at hf
  have hid : (s₁.nextId == i) = true := by
    cases hb : (s₁.nextId == i)
    · rw [hb] at hf; exact absurd hf (by simp)
    · rfl
  rw [hid] at hf
  obtain rfl := Option.some.inj hf
  obtain ⟨f', e', hf', hout', -, -, -, hs5⟩ := refExec_commit hcm
  simp only [updFiring, List.map_cons, List.map_nil, hid, if_true, List.find?_cons] at hf'
  obtain rfl := Option.some.inj hf'
  simp only [Bool.true_and, Bool.not_false, if_true, List.nil_append, Option.some.injEq,
    Outcome.ok.injEq] at hout'
  subst hout'
  obtain ⟨hLe, hLst⟩ := loses_run hL
  -- the end of the cycle, up to the update
  unfold cycleEndLabels at hT
  obtain ⟨u1, hu1, hT⟩ := xrun_cons.mp hT
  obtain ⟨-, -, -, -, rfl⟩ := xstepW_endPass hu1
  obtain ⟨u2, hu2, hT⟩ := xrun_cons.mp hT
  obtain ⟨-, -, -, -, rfl⟩ := xstepW_endCompletions hu2
  obtain ⟨u3, hu3, hT⟩ := xrun_cons.mp hT
  obtain ⟨-, -, -, rfl⟩ := xstepW_endPublications hu3
  obtain ⟨u4, hu4, hT⟩ := xrun_cons.mp hT
  obtain ⟨-, -, -, rfl⟩ := xstepW_endEvents hu4
  obtain ⟨s'', hU, hT⟩ := xrun_cons.mp hT
  cases hT
  have hAM : sA.M = qFire s.M t e := by
    rw [hLe]
    show s₅.M = _
    rw [hs5]
    show qAppend (liveAfter s₁ t) e = _
    rw [liveAfter_of_delta_zero hd1, hs1M]
    rfl
  have hAfl : sA.fl = [] := by
    rw [hLe]
    have hid' : s₁.nextId = i := by simpa using hid
    show s₅.fl = []
    rw [hs5]
    show List.filter _ _ = []
    simp [updFiring, hid']
  have hvis5 : qCount (vis s₅) = mid t (qCount s.M) := by
    rw [hs5, vis_depositAt (by exact hs1ph) (by exact hd1)]
    show qCount (liveAfter s₁ t) = _
    rw [liveAfter_of_delta_zero hd1, hs1M, qCount_qConsume]
  have hord5 : s₅.order = rest := by rw [hs5]; rfl
  have h5t : s₅.st t.core.name = .off := by
    rw [hs5]
    show unreap C (e.map Prod.fst) (unreap C (inPlaces t ++ t.core.resets)
      (afterStart refXPol C s₁ t)) t.core.name = _
    exact unreap_off (unreap_off (by unfold afterStart; simp))
  refine ⟨t, _, ht, hn, hU, hAM, hAfl, ?_, fun x u hfx hxt => ?_⟩
  · show sA.st t.core.name = .off
    rcases hLst t.core.name with h' | ⟨h', -⟩
    · rw [h', h5t]
    · exact h'
  · show sA.st x = _ ∨ (sA.st x = .off ∧ _)
    have hpre : s₅.st x = preOf (s.st x) (enabledNA (mid t (qCount s.M)) u.core)
        (writesArc t (e.map Prod.fst) u) := by
      rw [hs5]
      show unreap C (e.map Prod.fst) (unreap C (inPlaces t ++ t.core.resets)
        (afterStart refXPol C s₁ t)) x = _
      rw [pre_status hfx hxt, liveAfter_of_delta_zero hd1, hs1M, qCount_qConsume, hs1st]
    rcases hLst x with h' | ⟨h', u', hu', hu'x, hnot⟩
    · exact Or.inl (h'.trans hpre)
    · right
      rw [hord5] at hu'
      obtain ⟨hu'n, hr'⟩ := mem_readyOrder
        (show u' ∈ readyOrder C s by rw [ho]; exact List.mem_cons_of_mem _ hu')
      obtain rfl : u' = u := by
        have := findT_of_mem hN hu'n
        rw [hu'x, hfx] at this
        exact (Option.some.inj this).symm
      have hsome : (stampOf (s.st x)).isSome = true := by
        have := hr'.1.2
        simpa [viewAt, hu'x] using this
      rw [hvis5] at hnot
      refine ⟨h', ?_⟩
      cases hsx : s.st x with
      | off => simp [hsx, stampOf] at hsome
      | reaped => simp [hsx, stampOf] at hsome
      | armed k r =>
        cases r with
        | true => exact absurd hsx (hnr x k)
        | false =>
          refine ⟨⟨k, rfl⟩, ?_⟩
          cases he1 : enabledNA (mid t (qCount s.M)) u'.core
          · rfl
          · rw [hpre, hsx] at hnot
            simp [preOf, he1, stampOf] at hnot

/-- The `TransitionClockRestarted` events of a reference update: the net's names whose restart
was pending and that the update leaves armed. -/
theorem mem_update_restarted (P : EvPol) (C : Cfg N T) (H : List (NetEvent N T)) (s s' : XSt N T)
    (x : String) :
    NetEvent.transitionClockRestarted x ∈ refEmitW P C H s .update s' ↔
      x ∈ netNames C ∧ pendingS (s.st x) = true ∧ isArmedS (s'.st x) = true := by
  simp only [refEmitW, List.mem_append, List.mem_filterMap]
  constructor
  · rintro (⟨m, -, hm⟩ | ⟨m, hmn, hm⟩)
    · split at hm <;> simp at hm
    · split at hm
      · rename_i hc
        simp only [Option.some.injEq, NetEvent.transitionClockRestarted.injEq] at hm
        subst hm
        simp only [Bool.and_eq_true] at hc
        exact ⟨hmn, hc⟩
      · simp at hm
  · rintro ⟨hx, hp, ha⟩
    exact Or.inr ⟨x, hx, by simp [hp, ha]⟩

/-- The `TransitionEnabled` events of a reference update: the net's names that were off and that
the update leaves armed. -/
theorem mem_update_enabled (P : EvPol) (C : Cfg N T) (H : List (NetEvent N T)) (s s' : XSt N T)
    (x : String) :
    NetEvent.transitionEnabled x ∈ refEmitW P C H s .update s' ↔
      x ∈ netNames C ∧ s.st x = .off ∧ isArmedS (s'.st x) = true := by
  simp only [refEmitW, List.mem_append, List.mem_filterMap]
  constructor
  · rintro (⟨m, hmn, hm⟩ | ⟨m, -, hm⟩)
    · split at hm
      · rename_i hc
        simp only [Option.some.injEq, NetEvent.transitionEnabled.injEq] at hm
        subst hm
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        exact ⟨hmn, hc⟩
      · simp at hm
    · split at hm <;> simp at hm
  · rintro ⟨hx, ho, ha⟩
    exact Or.inl ⟨x, hx, by simp [ho, ha]⟩

/-- The status `updOf` gives is armed exactly when the name is enabled and was not reaped. -/
theorem isArmedS_updOf (st : Status) (e2 : Bool) (now : Nat) :
    isArmedS (updOf st e2 now) = (e2 && st != .reaped) := by
  cases st with
  | armed k r => cases r <;> cases e2 <;> rfl
  | off => cases e2 <;> rfl
  | reaped => cases e2 <;> rfl

/-- **E3, the event image of L3.** On an L3 segment (`atomic_refTStep`: one pass with one
synchronous start of `t`, its writes, return and inline commit, the recheck losers, and the next
update, from a state with nothing in flight and no restart pending), the update announces each
transition of the net as the atomic grain of the timed step does (the evt-a spike's emission
`refEmit`: `TransitionEnabled` for what the firing newly arms, `TransitionClockRestarted` for an
armed transition the firing's intermediate marking disabled and that is armed again, nothing for
one whose clock runs on), with one exception: a transition that loses the pass recheck is off at
the update, so its restart is announced as `TransitionEnabled` (the gap the executor observed,
[TIME-012] AC5 and AC6, clash evt-a#2). Written `e1` for "enabled in the intermediate marking",
`e2` for "enabled after the firing", `w` for "the firing writes an arc place":

* the started transition gets `TransitionEnabled` exactly when it is enabled after its firing, and
  never `TransitionClockRestarted`;
* another transition gets `TransitionClockRestarted` only if it was armed with its clock running,
  `e1` is false and `e2` true, and if so it gets that or `TransitionEnabled`;
* one armed with `e1` true gets neither;
* one off before the segment gets `TransitionEnabled` exactly when `e2`, never a restart;
* one reaped before gets `TransitionEnabled` exactly when `w` and `e2`, never a restart.

For example, when `r` takes the only token `T` waits for and its action puts it back inside the
pass, the update announces `r` with `TransitionEnabled` and `T` with `TransitionClockRestarted`
(`EVT_005`'s run); when `T` is immediate too, it is in the pass's order after `r`, loses the
recheck and is announced with `TransitionEnabled` (`atomic_loser_run`). -/
theorem atomic_update_events (P : EvPol) {C : Cfg N T} (hN : NamesDistinct C.X)
    {s s' : XSt N T} {n : String} {i : Nat} {e : List (N × T)} {ls : List String}
    (hfl : s.fl = []) (hnr : ∀ x k, s.st x ≠ .armed k true)
    (h : xrun C s (atomicLabels n i e ls) = some s') (H : List (NetEvent N T)) :
    ∃ (t : Trans N) (sU : XSt N T), t ∈ C.X.net.transitions ∧ t.core.name = n ∧
      xstep C sU .update = some s' ∧
      (NetEvent.transitionEnabled n ∈ refEmitW P C H sU .update s' ↔
        enabledNA (qCount (qFire s.M t e)) t.core = true) ∧
      NetEvent.transitionClockRestarted n ∉ refEmitW P C H sU .update s' ∧
      ∀ x u, findT C x = some u → x ≠ n →
        let e1 := enabledNA (mid t (qCount s.M)) u.core
        let e2 := enabledNA (qCount (qFire s.M t e)) u.core
        let evs := refEmitW P C H sU .update s'
        (NetEvent.transitionClockRestarted x ∈ evs →
          (∃ k, s.st x = .armed k false) ∧ e1 = false ∧ e2 = true) ∧
        ((∃ k, s.st x = .armed k false) → e1 = false → e2 = true →
          NetEvent.transitionClockRestarted x ∈ evs ∨ NetEvent.transitionEnabled x ∈ evs) ∧
        ((∃ k, s.st x = .armed k false) → e1 = true →
          NetEvent.transitionClockRestarted x ∉ evs ∧ NetEvent.transitionEnabled x ∉ evs) ∧
        (s.st x = .off → NetEvent.transitionClockRestarted x ∉ evs ∧
          (NetEvent.transitionEnabled x ∈ evs ↔ e2 = true)) ∧
        (s.st x = .reaped → NetEvent.transitionClockRestarted x ∉ evs ∧
          (NetEvent.transitionEnabled x ∈ evs ↔
            writesArc t (e.map Prod.fst) u = true ∧ e2 = true)) := by
  obtain ⟨t, sU, ht, hn, hU, hUM, hUfl, hUt, hpre⟩ := atomic_preUpdate hN hfl hnr h
  obtain ⟨-, -, rfl⟩ := xstepW_update hU
  have hst : ∀ x u, findT C x = some u →
      isArmedS (updSt refXPol C sU x) =
        (enabledNA (qCount (qFire s.M t e)) u.core && sU.st x != .reaped) := by
    intro x u hfx
    rw [updSt_of_noFlight hfx hUfl, isArmedS_updOf, hUM]
  have hnet : ∀ x u, findT C x = some u → x ∈ netNames C := fun x u hfx => by
    obtain ⟨hu, hux⟩ := findT_spec hfx
    exact List.mem_map.mpr ⟨u, hu, hux⟩
  have htf : findT C t.core.name = some t := findT_of_mem hN ht
  refine ⟨t, sU, ht, hn, hU, ?_, ?_, fun x u hfx hxn => ?_⟩
  · rw [mem_update_enabled]
    subst hn
    simp only [hUt, hst _ _ htf, true_and]
    constructor
    · rintro ⟨-, h'⟩; simpa using h'
    · intro h'; exact ⟨hnet _ _ htf, by simp [h']⟩
  · rw [mem_update_restarted]
    subst hn
    simp [hUt, pendingS]
  · have hxt : x ≠ t.core.name := hn ▸ hxn
    simp only [mem_update_restarted, mem_update_enabled, hst x u hfx]
    have hx := hnet x u hfx
    rcases hpre x u hfx hxt with hp | ⟨hp, hk, he1⟩
    · rw [hp]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rintro ⟨-, hpend, harm⟩
        cases hsx : s.st x with
        | armed k r =>
          cases r with
          | true => exact absurd hsx (hnr x k)
          | false =>
            rw [hsx] at hpend harm
            cases he1 : enabledNA (mid t (qCount s.M)) u.core <;>
              simp_all [preOf, pendingS]
        | off => rw [hsx] at hpend; simp [preOf, pendingS] at hpend
        | reaped =>
          rw [hsx] at hpend
          cases hw : writesArc t (e.map Prod.fst) u <;> simp_all [preOf, pendingS]
      · rintro ⟨k, hsx⟩ he1 he2
        left
        rw [hsx]
        simp [preOf, he1, he2, pendingS, hx]
      · rintro ⟨k, hsx⟩ he1
        rw [hsx]
        simp [preOf, he1, pendingS]
      · intro hsx
        rw [hsx]
        simp [preOf, pendingS, hx]
      · intro hsx
        rw [hsx]
        cases hw : writesArc t (e.map Prod.fst) u <;> simp [preOf, pendingS, hx]
    · rw [hp]
      obtain ⟨k, hsx⟩ := hk
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rintro ⟨-, hpend, -⟩; simp [pendingS] at hpend
      · intro _ _ he2
        right
        simp [hx, he2]
      · intro _ he1'
        rw [he1] at he1'
        cases he1'
      · intro hsx'; rw [hsx] at hsx'; cases hsx'
      · intro hsx'; rw [hsx] at hsx'; cases hsx'

end E3

/-! ## E6: the emission variants differ only at the three points `EvPol` names -/

section E6

/-- The step is a timeout deposit. -/
def isTdepositL : XLbl N T → Bool
  | .tdeposit _ => true
  | _ => false

/-- **The events every emission variant agrees on**, at a step labelled `l`: every event but a
`MarkingSnapshot` (absent from an emission without snapshots, `polNoSnap`), an `ActionTimedOut`
(emitted at the expiry by Java and TypeScript, at the settle by Rust and Python) and the
`TransitionCompleted` of a timeout deposit (Java and TypeScript only). These are the three fields
of `EvPol`. -/
def polBlind (l : XLbl N T) (e : NetEvent N T) : Bool :=
  e.kind != .markingSnapshot && e.kind != .actionTimedOut &&
    !(isTdepositL l && e.kind == .transitionCompleted)

/-- **E6, the scope of the main blocks.** Two emission variants emit, at every step, the same
events in the same order once the three variant points are left out (`polBlind`). So a line that
reads only those events holds of the Rust and Python emission `polRust` exactly when it holds of
the Java and TypeScript emission `polJT`; the main block of each executor event requirement is
stated so, and its `_rust` holds theorem is this fact for that block. For example, at the commit
of `r` both variants report `TokenAdded 0 9` and `TransitionCompleted r`, and at the deposit of a
timeout outcome both report the `TokenAdded` events of the outcome, Java and TypeScript then add
a `TransitionCompleted` and Rust puts an `ActionTimedOut` first. -/
theorem refEmitW_polBlind (P P' : EvPol) (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T)
    (l : XLbl N T) (s' : XSt N T) :
    (refEmitW P C H s l s').filter (polBlind l) = (refEmitW P' C H s l s').filter (polBlind l) := by
  cases l with
  | fail i =>
    simp only [refEmitW]
    split
    · simp only [List.filter_append]
      congr 1
      · split <;> split <;> simp [polBlind, NetEvent.kind]
    · rfl
  | tdeposit i =>
    simp only [refEmitW]
    split
    · split
      · simp only [List.filter_append]
        congr 1
        · congr 1
          split <;> split <;> simp [polBlind, NetEvent.kind, isTdepositL]
        · split <;> split <;> simp [polBlind, NetEvent.kind, isTdepositL]
      · rfl
    · rfl
  | expire i e =>
    simp only [refEmitW]
    split <;> split <;> (try split) <;> simp [polBlind, NetEvent.kind]
  | finish c =>
    simp only [refEmitW, List.filter_append]
    congr 1
    split <;> split <;> simp [polBlind, NetEvent.kind]
  | _ => rfl

/-- **E6 at the boot**: without the snapshot, every variant boots with `ExecutionStarted` alone. -/
theorem refBoot_polBlind (P : EvPol) (C : Cfg N T) (M0 : QMarking N T) :
    (refBoot P C M0).filter (fun e => e.kind != .markingSnapshot) = [.executionStarted] := by
  simp only [refBoot, List.filter_append]
  split <;> simp [NetEvent.kind]

end E6

end Libpetri.Reference

namespace Libpetri.Spec

variable {N T : Type} [DecidableEq N] [Ord N]

/-! ## The replay view of an executor event -/

/-- The recorded event of the replay an executor event is: the kind, the transition name and the
place, and a snapshot's queues as counts ([EVT-032]: the map that forgets what the replay does
not read). -/
def NetEvent.toRec : NetEvent N T → RecEvent N
  | .executionStarted => .executionStarted
  | .executionCompleted => .executionCompleted
  | .transitionEnabled t => .transitionEnabled t
  | .transitionClockRestarted t => .transitionClockRestarted t
  | .transitionStarted t _ => .transitionStarted t
  | .transitionCompleted t _ _ => .transitionCompleted t
  | .transitionFailed t => .transitionFailed t
  | .transitionTimedOut t _ _ => .transitionTimedOut t
  | .actionTimedOut t => .actionTimedOut t
  | .tokenAdded p _ => .tokenAdded p
  | .tokenRemoved p _ => .tokenRemoved p
  | .markingSnapshot m => .markingSnapshot (m.map fun e => (e.1, e.2.length))
  | .logMessage .. => .logMessage

/-- The replay view of an executor event: `recView` after `NetEvent.toRec`. -/
def NetEvent.replayView (e : NetEvent N T) : REv N := recView e.toRec

omit [DecidableEq N] [Ord N] in
/-- The recorded event keeps the kind: one kind type for the executor events and the replay. -/
theorem NetEvent.toRec_kind (e : NetEvent N T) : e.toRec.kind = e.kind := by
  cases e <;> rfl

omit [Ord N] in
/-- The replay counts a `TokenRemoved` as one token taken from its place. -/
theorem NetEvent.replayView_tokenRemoved (p : N) (x : T) :
    (NetEvent.tokenRemoved p x).replayView = .removed p := rfl

/-! ## E5: coverage of the event kinds -/

/-- The kinds the executor tier emits: every kind but `LogMessage` (the reference executor has no
label for an action's log, [EVT-013]). -/
def execKinds : List NetEventKind :=
  [.executionStarted, .executionCompleted, .transitionEnabled, .transitionClockRestarted,
   .transitionStarted, .transitionCompleted, .transitionFailed, .transitionTimedOut,
   .actionTimedOut, .tokenAdded, .tokenRemoved, .markingSnapshot]

/-- `execKinds` is every kind but `LogMessage`. -/
theorem execKinds_complete (k : NetEventKind) : k ∈ execKinds ∨ k = .logMessage := by
  cases k <;> simp [execKinds]

/-- **Coverage of event kinds** (design link E5; a consistency condition, never a block line):
one event trace of `V` holds an event of every kind in `ks`, so a line over traces cannot hold of
`V` merely because `V` never emits the kinds it speaks of. Stated over place and token type `Nat`,
where the scenario lives. -/
def EvCoversKinds (ks : List NetEventKind) (V : EvExec Nat Nat) : Prop :=
  ∃ C M0 r0 tr, Trace V C M0 r0 tr ∧ ∀ k ∈ ks, ∃ e ∈ tr, e.kind = k

/-- **E5**: one trace of `V` holds an event of every kind the executor tier emits. -/
def EvCovers (V : EvExec Nat Nat) : Prop := EvCoversKinds execKinds V

end Libpetri.Spec

namespace Libpetri.Reference

open Libpetri Libpetri.Spec Libpetri.Novel.Seam

variable {N T : Type} [DecidableEq N] [Ord N]

/-! ## E4: the replay of a run's events agrees with the executor state -/

section E4

/-- The replay of executor events ([EVT-032]'s replay over the replay view of an executor
event, `NetEvent.replayView`), from the replayed state `r`. -/
abbrev evFold (r : RState N) (evs : List (NetEvent N T)) : RState N :=
  replayWith applyEv NetEvent.replayView r evs

/-- The replay of executor events from the empty state. -/
abbrev evReplay (evs : List (NetEvent N T)) : RState N :=
  Libpetri.Spec.replay NetEvent.replayView evs

omit [Ord N] in
/-- One event, then the rest. -/
theorem evFold_cons (r : RState N) (e : NetEvent N T) (es : List (NetEvent N T)) :
    evFold r (e :: es) = evFold (applyEv r e.replayView) es := rfl

omit [Ord N] in
/-- Replaying `H ++ evs` is replaying `evs` from the state `H` gives. -/
theorem evReplay_append (H evs : List (NetEvent N T)) :
    evReplay (H ++ evs) = evFold (evReplay H) evs := by
  unfold evReplay Libpetri.Spec.replay
  exact replayWith_append _ _ _ _ _

omit [Ord N] in
/-- Events that are neither a snapshot nor a removal add to a place's replayed count exactly
their `TokenAdded` events naming it. -/
theorem evFold_cnt_add (p : N) : ∀ (evs : List (NetEvent N T)) (r : RState N),
    (∀ e ∈ evs, e.kind ≠ .markingSnapshot ∧ e.kind ≠ .tokenRemoved) →
      (evFold r evs).cnt p = r.cnt p + addedCount evs p
  | [], r, _ => by simp [evFold, replayWith, addedCount]
  | e :: es, r, h => by
    rw [evFold_cons, evFold_cnt_add p es _ (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    have he := h e List.mem_cons_self
    have hc : addedCount (e :: es) p = (if e.addsTo p then 1 else 0) + addedCount es p := by
      simp only [addedCount, List.countP_cons]; split <;> omega
    rw [hc]
    cases e with
    | tokenAdded q x =>
      by_cases hq : q = p
      · subst hq
        simp [NetEvent.replayView, NetEvent.toRec, recView, applyEv, Spec.setAt, NetEvent.addsTo]
        omega
      · have hq' : p ≠ q := fun h' => hq h'.symm
        simp [NetEvent.replayView, NetEvent.toRec, recView, applyEv, Spec.setAt, NetEvent.addsTo,
          hq,
          hq']
    | tokenRemoved q x => exact absurd rfl he.2
    | markingSnapshot m => exact absurd rfl he.1
    | _ => simp [NetEvent.replayView, NetEvent.toRec, recView, applyEv, NetEvent.addsTo]

omit [Ord N] in
/-- Events that are neither a snapshot nor an addition take from a place's replayed count exactly
their `TokenRemoved` events naming it (the count stops at zero). -/
theorem evFold_cnt_sub (p : N) : ∀ (evs : List (NetEvent N T)) (r : RState N),
    (∀ e ∈ evs, e.kind ≠ .markingSnapshot ∧ e.kind ≠ .tokenAdded) →
      (evFold r evs).cnt p = r.cnt p - removedCount evs p
  | [], r, _ => by simp [evFold, replayWith, removedCount]
  | e :: es, r, h => by
    rw [evFold_cons, evFold_cnt_sub p es _ (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    have he := h e List.mem_cons_self
    have hc : removedCount (e :: es) p =
        (if e.removesFrom p then 1 else 0) + removedCount es p := by
      simp only [removedCount, List.countP_cons]; split <;> omega
    rw [hc]
    cases e with
    | tokenRemoved q x =>
      by_cases hq : q = p
      · subst hq
        simp [NetEvent.replayView, NetEvent.toRec, recView, applyEv, Spec.setAt,
          NetEvent.removesFrom]
        omega
      · have hq' : p ≠ q := fun h' => hq h'.symm
        simp [NetEvent.replayView, NetEvent.toRec, recView, applyEv, Spec.setAt,
          NetEvent.removesFrom, hq, hq']
    | tokenAdded q x => exact absurd rfl he.2
    | markingSnapshot m => exact absurd rfl he.1
    | _ => simp [NetEvent.replayView, NetEvent.toRec, recView, applyEv, NetEvent.removesFrom]

omit [Ord N] in
/-- The replay keeps a transition enabled through events that start no transition of that name. -/
theorem evFold_en_keep (n : String) : ∀ (evs : List (NetEvent N T)) (r : RState N),
    (∀ e ∈ evs, e.kind = .transitionStarted → e.trans? ≠ some n) → r.en n = true →
      (evFold r evs).en n = true
  | [], r, _, hr => hr
  | e :: es, r, h, hr => by
    rw [evFold_cons]
    apply evFold_en_keep n es _ (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have he := h e List.mem_cons_self
    cases e with
    | transitionEnabled t =>
      simp only [NetEvent.replayView, NetEvent.toRec, recView, applyEv, Spec.setAt]
      split <;> simp_all
    | transitionStarted t m =>
      have hne : t ≠ n := fun h' => he rfl (by simp [NetEvent.trans?, h'])
      simp only [NetEvent.replayView, NetEvent.toRec, recView, applyEv, Spec.setAt]
      rw [if_neg (fun h' => hne h'.symm)]
      exact hr
    | _ => simpa [NetEvent.replayView, NetEvent.toRec, recView, applyEv] using hr

omit [Ord N] in
/-- A `TransitionEnabled` of `n` among events that start no transition leaves `n` enabled in the
replay. -/
theorem evFold_en_enabled (n : String) : ∀ (evs : List (NetEvent N T))
    (r : RState N), (∀ e ∈ evs, e.kind ≠ .transitionStarted) →
      NetEvent.transitionEnabled n ∈ evs → (evFold r evs).en n = true
  | [], r, _, hm => by cases hm
  | e :: es, r, h, hm => by
    rw [evFold_cons]
    rcases List.mem_cons.mp hm with he | he
    · subst he
      apply evFold_en_keep n es _ (fun x hx hk => absurd hk (h x (List.mem_cons_of_mem _ hx)))
      simp [NetEvent.replayView, NetEvent.toRec, recView, applyEv, Spec.setAt]
    · exact evFold_en_enabled n es _ (fun x hx => h x (List.mem_cons_of_mem _ hx)) he

omit [Ord N] in
/-- Looking a key up in a list of keys paired with their values. -/
theorem lookup_map_pair (f : N → Nat) (p : N) :
    ∀ L : List N, (L.map fun q => (q, f q)).lookup p = if p ∈ L then some (f p) else none
  | [] => by simp
  | q :: L => by
    rw [List.map_cons, List.lookup_cons, lookup_map_pair f p L]
    by_cases h : p = q
    · subst h; simp
    · have hb : (p == q) = false := by simp [h]
      simp [hb, h]

/-- **The snapshot gives the declared counts**: the replay view of the reference snapshot of `M`
counts, on every declared place, the tokens `M` holds there (a declared place without a token is
not listed and counts zero). -/
theorem snapshot_cnt (C : Cfg N T) (M : QMarking N T) (r : RState N) {p : N}
    (hp : p ∈ C.X.net.places) :
    (applyEv r (NetEvent.markingSnapshot (snapOf C M) : NetEvent N T).replayView).cnt p =
      (M p).length := by
  simp only [NetEvent.replayView, NetEvent.toRec, recView, applyEv, snapOf, List.map_map]
  have hf : ((fun e : N × Nat => (e.1, e.2)) ∘ (fun e : N × List T => (e.1, e.2.length)) ∘
      fun q => (q, M q)) = fun q => (q, (M q).length) := rfl
  rw [show ((fun e : N × List T => (e.1, e.2.length)) ∘ fun q => (q, M q)) =
      fun q => (q, (M q).length) from rfl, lookup_map_pair (fun q => (M q).length) p]
  by_cases hm : (M p).isEmpty = true
  · have : p ∉ (snapArrange C.X.net.places).dedup.filter (fun p => !(M p).isEmpty) := by
      simp [hm]
    rw [if_neg this]
    simp [List.isEmpty_iff.mp hm]
  · have : p ∈ (snapArrange C.X.net.places).dedup.filter (fun p => !(M p).isEmpty) := by
      simp [List.mem_dedup, mem_snapArrange, hp, hm]
    rw [if_pos this]
    rfl

/-- A status is armed when it holds a stamp. -/
theorem isArmedS_eq_isSome (x : Status) : isArmedS x = (stampOf x).isSome := by
  cases x <;> rfl

omit [Ord N] in
/-- `unreap` arms nothing and disarms nothing. -/
theorem isArmedS_unreap (C : Cfg N T) (ps : List N) (st : String → Status) (n : String) :
    isArmedS (unreap C ps st n) = isArmedS (st n) := by
  rw [isArmedS_eq_isSome, isArmedS_eq_isSome, tc_stampOf_unreap]

omit [Ord N] in
/-- A start of `t` arms nothing: a name armed after it is not `t`'s and was armed before. -/
theorem isArmedS_afterStart {P : XPol N T} {C : Cfg N T} {s : XSt N T} {t : Trans N} {n : String}
    (h : isArmedS (afterStart P C s t n) = true) : n ≠ t.core.name ∧ isArmedS (s.st n) = true := by
  unfold afterStart at h
  by_cases hn : n = t.core.name
  · rw [if_pos hn] at h; cases h
  · rw [if_neg hn] at h
    refine ⟨hn, ?_⟩
    cases hs : s.st n <;> cases hf : findT C n <;> simp only [hs, hf] at h <;> try exact h
    all_goals simp [isArmedS]

/-- Only a start emits `TransitionStarted` in the reference. -/
theorem refEmitW_noStarted (P : EvPol) (C : Cfg N T) (H : List (NetEvent N T))
    (s : XSt N T) {l : XLbl N T} (hl : ∀ n sy, l ≠ .start n sy) (s' : XSt N T) :
    ∀ e ∈ refEmitW P C H s l s', e.kind ≠ .transitionStarted := by
  intro e he hk
  have := refEmitW_kind P C H s l s' e he
  rw [hk] at this
  cases l with
  | start n sy => exact hl n sy rfl
  | _ => simp [lblKinds] at this

/-- **Replay agreement** (design link E4): the replayed state `r` and the executor state `s` agree
on what the replay reconstructs: on every declared place the replayed count is the number of
tokens the place holds, and every armed transition is in the replay's enabled set (an
over-approximation, ruling D83 (a): the replay keeps a transition enabled until it starts). -/
def ReplayAgrees (C : Cfg N T) (r : RState N) (s : XSt N T) : Prop :=
  (∀ p ∈ C.X.net.places, r.cnt p = (s.M p).length) ∧ ∀ n, isArmedS (s.st n) = true → r.en n = true

/-- **E4, one step**: a step of the reference executor with events keeps replay agreement, under
every emission variant. A start's `TokenRemoved` events take what it removes, a deposit's
`TokenAdded` events add what it appends, a finish's snapshot (where the variant emits one) restates the
counts, an update's `TransitionEnabled` events announce what it arms, and no other step arms. -/
theorem replayAgrees_step (P : EvPol) {C : Cfg N T} {H : List (NetEvent N T)} {s s' : XSt N T}
    {l : XLbl N T} (hs : xstep C s l = some s') {r : RState N} (hr : ReplayAgrees C r s) :
    ReplayAgrees C (evFold r (refEmitW P C H s l s')) s' := by
  have hk := refEmitW_kind P C H s l s'
  refine ⟨fun p hp => ?_, fun n hn => ?_⟩
  · by_cases hst : ∃ n sy, l = .start n sy
    · obtain ⟨n, sy, rfl⟩ := hst
      have hrem := refStart_removedAt P H hs p
      rw [evFold_cnt_sub p _ _ (fun e he => by
        have := hk e he
        constructor <;> intro h <;> rw [h] at this <;> simp [lblKinds] at this),
        hr.1 p hp, removedCount_eq_length]
      have := congrArg List.length hrem
      rw [List.length_append] at this
      omega
    · have hl : ∀ n sy, l ≠ .start n sy := fun n sy h => hst ⟨n, sy, h⟩
      by_cases hf : ∃ c, l = .finish c
      · obtain ⟨c, rfl⟩ := hf
        have hM : s'.M = s.M := xstepW_M_frame hs (by simp [XLbl.marks])
        rw [hM]
        simp only [refEmitW]
        cases P.snapshots
        · simpa [evFold, replayWith, NetEvent.replayView, NetEvent.toRec, recView, applyEv]
            using hr.1 p hp
        · simp only [ite_true, List.singleton_append]
          rw [evFold_cons, evFold_cons]
          exact snapshot_cnt C s.M r hp
      · have hf' : ∀ c, l ≠ .finish c := fun c h => hf ⟨c, h⟩
        rw [evFold_cnt_add p _ _ (fun e he => by
          refine ⟨fun h => ?_, refEmitW_noRemoved P C H s hl s' e he⟩
          have := hk e he
          rw [h] at this
          cases l with
          | finish c => exact hf' c rfl
          | _ => simp [lblKinds] at this), hr.1 p hp, evt011_addedCount_eq_length]
        have := congrArg List.length (evt011_refStep P H hl hs p)
        rw [List.length_append] at this
        omega
  · have hs' : xstepW refXPol C s l = some s' := hs
    rcases tc_st_step hs' with ⟨rfl, hst⟩ | ⟨ns, rfl, hst⟩ | ⟨m, rfl, hst⟩ |
      ⟨m, sy, t, rest, rfl, ho, htn, -, hst⟩ | ⟨⟨-, -, -, hsta⟩, hst⟩
    · -- the update: an armed name was armed before, or the update armed it and announced it
      have hnos := refEmitW_noStarted P C H s (l := .update) (by intro _ _ h; cases h) s'
      cases hsn : isArmedS (s.st n)
      · apply evFold_en_enabled n _ _ hnos
        have hn0 := hn
        rw [hst] at hn
        unfold updSt at hn
        cases hft : findT C n with
        | none => simp [hft, isArmedS] at hn
        | some u =>
          simp only [hft] at hn
          cases hsx : s.st n with
          | armed k r => simp [hsx, isArmedS] at hsn
          | reaped => simp [hsx, refXPol, isArmedS] at hn
          | off =>
            obtain ⟨hu, hun⟩ := findT_spec hft
            simp only [refEmitW]
            apply List.mem_append_left
            apply List.mem_filterMap.mpr
            refine ⟨n, List.mem_map.mpr ⟨u, hu, hun⟩, ?_⟩
            simp [hsx, hn0]
      · exact evFold_en_keep n _ _ (fun e he hk' => absurd hk' (hnos e he)) (hr.2 n hsn)
    · -- the deadline step: it only reaps
      rw [hst] at hn
      simp only at hn
      split at hn
      · cases hn
      · exact evFold_en_keep n _ _
          (fun e he hk' => absurd hk'
            (refEmitW_noStarted P C H s (by intro _ _ h; cases h) s' e he))
          (hr.2 n hn)
    · -- a lose: it only disarms
      rw [hst] at hn
      simp only at hn
      split at hn
      · cases hn
      · exact evFold_en_keep n _ _
          (fun e he hk' => absurd hk'
            (refEmitW_noStarted P C H s (by intro _ _ h; cases h) s' e he))
          (hr.2 n hn)
    · -- a start: the started transition goes off, every other armed name was armed before
      rw [hst, isArmedS_unreap] at hn
      obtain ⟨hnt, hsn⟩ := isArmedS_afterStart hn
      apply evFold_en_keep n _ _ _ (hr.2 n hsn)
      intro e he hk'
      rw [refEmitW_start P C H ho m sy s'] at he
      rcases List.mem_append.mp he with he | he
      · rw [kind_of_mem_removedEvs he] at hk'; cases hk'
      · rw [List.mem_singleton] at he
        subst he
        simp only [NetEvent.trans?]
        intro h'
        exact hnt ((Option.some.inj h').symm.trans htn.symm)
    · -- every other step: a write ends a reap, nothing arms
      rw [hst, isArmedS_unreap] at hn
      exact evFold_en_keep n _ _
        (fun e he hk' => absurd hk' (refEmitW_noStarted P C H s hsta s' e he)) (hr.2 n hn)

/-- The state a labelled run ends in, from `s`. -/
def runEnd (s : XSt N T) : List (EvStep N T) → XSt N T
  | [] => s
  | st :: rest => runEnd st.dst rest

/-- **E4, a run**: a labelled run of the reference executor with events keeps replay agreement. -/
theorem replayAgrees_lrun (P : EvPol) {C : Cfg N T} :
    ∀ {H : List (NetEvent N T)} {s : XSt N T} {run : List (EvStep N T)},
      LRun (refEvExec P) C H s run → ReplayAgrees C (evReplay H) s →
        ReplayAgrees C (evReplay (H ++ EvStep.events run)) (runEnd s run)
  | H, s, [], _, h => by simpa [EvStep.events, runEnd] using h
  | H, s, st :: rest, ⟨hsrc, ⟨hx, hev⟩, hrest⟩, h => by
    have h1 : ReplayAgrees C (evReplay (H ++ st.evs)) st.dst := by
      rw [evReplay_append, hev]
      exact replayAgrees_step P hx (hsrc ▸ h)
    have := replayAgrees_lrun P hrest h1
    simpa [EvStep.events, List.flatMap_cons, List.append_assoc, runEnd] using this

/-- Replay agreement at the boot, when the boot carries the snapshot of the initial marking (every
runtime's emission): nothing is armed yet, and the snapshot gives the declared counts. -/
theorem replayAgrees_boot (P : EvPol) (hP : P.snapshots = true) (C : Cfg N T) (M0 : QMarking N T)
    (r0 : Nat) : ReplayAgrees C (evReplay (refBoot P C M0)) (xinit M0 r0) := by
  refine ⟨fun p hp => ?_, fun n hn => by simp [xinit, isArmedS] at hn⟩
  simp only [refBoot, hP, ite_true, List.singleton_append]
  show (evFold _ _).cnt p = _
  rw [evFold_cons, evFold_cons]
  exact snapshot_cnt C M0 _ hp

/-- **E4, the replay of a run** (design link E4, the base of the [EVT-032] executor companion):
for every labelled run of the reference executor with events from the initial state, under an
emission variant whose boot carries the snapshot of the initial marking (`polJT` and `polRust`),
replaying the run's events (the boot events, then the events of each step) gives, on
every declared place, the number of tokens the place holds at the end of the run, and an enabled
set that contains every transition armed at the end.

For example, if the initial marking puts token 1 in place 0 and `r` consumes it and its action
puts back 9, the replay of `MarkingSnapshot [(0, [1])]`, `TokenRemoved 0 1` and `TokenAdded 0 9`
counts one token in place 0, as the executor holds `[9]` there. -/
theorem refReplay_agrees (P : EvPol) (hP : P.snapshots = true) {C : Cfg N T}
    {M0 : QMarking N T} {r0 : Nat} {run : List (EvStep N T)}
    (h : LRun (refEvExec P) C (refBoot P C M0) (xinit M0 r0) run) :
    ReplayAgrees C (evReplay (refBoot P C M0 ++ EvStep.events run)) (runEnd (xinit M0 r0) run) :=
  replayAgrees_lrun P h (replayAgrees_boot P hP C M0 r0)

/-- E4 for the Java and TypeScript emission. -/
theorem refReplay_agrees_jt {C : Cfg N T} {M0 : QMarking N T} {r0 : Nat}
    {run : List (EvStep N T)}
    (h : LRun (refEvExec polJT) C (refBoot polJT C M0) (xinit M0 r0) run) :
    ReplayAgrees C (evReplay (refBoot polJT C M0 ++ EvStep.events run))
      (runEnd (xinit M0 r0) run) :=
  refReplay_agrees polJT rfl h

end E4

/-! ## E5: one scenario trace holds every kind the executor tier emits -/

section E5

/-- A transition of the coverage scenario: one token from each input place, output spec `out`. -/
def covTr (n : String) (ins : List Nat) (out : Option (Out Nat)) : Trans Nat :=
  { core := { name := n, inputs := ins.map fun p => ⟨p, .one⟩, inhibitors := [], reads := [],
              resets := [] },
    out := out }

/-- **The coverage scenario.** Places 0 to 6, place 5 terminal. `r` (immediate) takes the tokens
of places 0 and 1; `T` (`delayed 50`) waits for the token of place 0; `f` (`delayed 1`) takes
place 2's token; `a` (`delayed 2`) takes place 3's token and has a `Timeout` node that puts its
outcome in place 5; `w` (`window 3 4`) waits for place 6's token. Every output is valid and every
emission may be a timeout outcome. The delays make one transition ready per pass. -/
def covCfg : Cfg Nat Nat :=
  { X := { net := { places := [0, 1, 2, 3, 4, 5, 6],
                    transitions := [covTr "r" [0, 1] none, covTr "T" [0] none, covTr "f" [2] none,
                      covTr "a" [3] (some (.timeout (.place 5))), covTr "w" [6] none] },
           timing := fun u => if u.core.name = "T" then .delayed 50
             else if u.core.name = "f" then .delayed 1
             else if u.core.name = "a" then .delayed 2
             else if u.core.name = "w" then .window 3 4 else .immediate,
           tol := 0 },
    prio := fun _ => 0, terminals := [5], envs := [], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => true,
    res := 0 }

/-- The initial marking of the scenario: one token in each of places 0, 1, 2, 3 and 6. -/
def covM0 : QMarking Nat Nat := fun p =>
  if p = 0 then [1] else if p = 1 then [4] else if p = 2 then [2] else if p = 3 then [3]
  else if p = 6 then [6] else []

/-- Steps 1, 1b and 2 with nothing to do, then the update. -/
def covCyc : List (XLbl Nat Nat) := [.endCompletions, .endPublications, .endEvents, .update]

/-- The labels of the scenario. At reading 0 the update arms all five transitions and `r` starts
synchronously; its action puts 9 back into place 0 and is committed inside the pass, which takes
`T`'s clock. At reading 1 the update restarts `T`'s clock and `f` starts asynchronously; its
action throws. At reading 12 `f` is settled as failed, the deadline step reaps `w` (12 past its
latest bound 4) and `a` starts asynchronously; its budget runs out with outcome 7 for place 5,
which is deposited, and the run finishes on the marked terminal place. -/
def covRun : List (XLbl Nat Nat) :=
  covCyc ++ [.deadline [], .begin, .start "r" true, .write 0 0 9, .ret 0 true, .commit 0,
    .endPass, .delay 1] ++
  covCyc ++ [.deadline [], .begin, .start "f" false, .endPass, .ret 1 false, .delay 11,
    .fail 1] ++
  covCyc ++ [.deadline ["w"], .begin, .start "a" false, .endPass, .expire 2 [(5, 7)],
    .tdeposit 2, .finish .terminal]

/-- The events of the scenario under the Java and TypeScript emission. -/
def covTraceJT : List (NetEvent Nat Nat) :=
  [.executionStarted, .markingSnapshot [(0, [1]), (1, [4]), (2, [2]), (3, [3]), (6, [6])],
   .transitionEnabled "r", .transitionEnabled "T", .transitionEnabled "f",
   .transitionEnabled "a", .transitionEnabled "w",
   .tokenRemoved 0 1, .tokenRemoved 1 4, .transitionStarted "r" [(0, 1), (1, 4)],
   .tokenAdded 0 9, .transitionCompleted "r" [(0, 9)] 0,
   .transitionClockRestarted "T",
   .tokenRemoved 2 2, .transitionStarted "f" [(2, 2)], .transitionFailed "f",
   .transitionTimedOut "w" 4 12,
   .tokenRemoved 3 3, .transitionStarted "a" [(3, 3)], .actionTimedOut "a",
   .tokenAdded 5 7, .transitionCompleted "a" [(5, 7)] 0,
   .markingSnapshot [(0, [9]), (5, [7]), (6, [6])], .executionCompleted]

/-- The events of the scenario under the Rust and Python emission: the `ActionTimedOut` of `a`
comes with the deposit of its timeout outcome, which reports no `TransitionCompleted`. The two
snapshots are the model's; Rust's carry the counts of these queues (RD-50). -/
def covTraceRust : List (NetEvent Nat Nat) :=
  [.executionStarted, .markingSnapshot [(0, [1]), (1, [4]), (2, [2]), (3, [3]), (6, [6])],
   .transitionEnabled "r", .transitionEnabled "T", .transitionEnabled "f",
   .transitionEnabled "a", .transitionEnabled "w",
   .tokenRemoved 0 1, .tokenRemoved 1 4, .transitionStarted "r" [(0, 1), (1, 4)],
   .tokenAdded 0 9, .transitionCompleted "r" [(0, 9)] 0,
   .transitionClockRestarted "T",
   .tokenRemoved 2 2, .transitionStarted "f" [(2, 2)], .transitionFailed "f",
   .transitionTimedOut "w" 4 12,
   .tokenRemoved 3 3, .transitionStarted "a" [(3, 3)], .actionTimedOut "a",
   .tokenAdded 5 7, .markingSnapshot [(0, [9]), (5, [7]), (6, [6])], .executionCompleted]

/-- The Java and TypeScript trace of the scenario, decided. -/
theorem covTrace_jt : refTrace polJT covCfg covM0 0 covRun = some covTraceJT := by
  decide +kernel

/-- The Rust and Python trace of the scenario, decided. -/
theorem covTrace_rust : refTrace polRust covCfg covM0 0 covRun = some covTraceRust := by
  decide +kernel

/-- **E5 for the reference.** The Java and TypeScript trace of the scenario holds all twelve kinds
the executor tier emits: `ExecutionStarted` and the snapshot of the initial marking, the five
`TransitionEnabled` events of the first update, `r`'s removals, start, addition and completion,
`T`'s `TransitionClockRestarted`, `f`'s start and `TransitionFailed`, `w`'s
`TransitionTimedOut`, `a`'s start and `ActionTimedOut`, the deposit of its timeout outcome with
its completion, and the final snapshot and `ExecutionCompleted`. -/
theorem refEvCovers : EvCovers (refEvExec polJT) :=
  ⟨covCfg, covM0, 0, covTraceJT, refTrace_trace polJT covTrace_jt, by decide⟩

/-- E5 for the Rust and Python emission: the same scenario holds all twelve kinds, with the
`ActionTimedOut` of `a` at the deposit of its timeout outcome and no `TransitionCompleted` there. -/
theorem refEvCovers_rust : EvCovers (refEvExec polRust) :=
  ⟨covCfg, covM0, 0, covTraceRust, refTrace_trace polRust covTrace_rust, by decide⟩

/-- An executor that steps as the reference and emits nothing at all. -/
def silentEvExec : EvExec Nat Nat := emitExec (fun _ _ => []) (fun _ _ _ _ _ => [])

/-- The silent executor appends nothing on any run. -/
theorem silent_events {C : Cfg Nat Nat} :
    ∀ {H : List (NetEvent Nat Nat)} {s : XSt Nat Nat} {run : List (EvStep Nat Nat)},
      LRun silentEvExec C H s run → EvStep.events run = []
  | _, _, [], _ => rfl
  | _, _, st :: rest, ⟨_, ⟨_, hev⟩, hrest⟩ => by
    simp only [EvStep.events, List.flatMap_cons] at hrest ⊢
    rw [hev]
    exact silent_events hrest

/-- **Coverage is not vacuous**: an executor that steps exactly as the reference but emits no
event meets every safety line on events that only forbids, and fails the coverage condition. -/
theorem evCovers_excludes_silent : ¬ EvCovers silentEvExec := by
  rintro ⟨C, M0, r0, tr, ⟨run, hrun, rfl⟩, hk⟩
  obtain ⟨e, he, -⟩ := hk .executionStarted (by decide)
  rw [silent_events hrun] at he
  cases he

/-! ### E3 on a decided run: the recheck loser -/

/-- Two immediate transitions with one priority (the fast path, declaration order): `r` and `T`
both take the token of place 0. -/
def loserCfg : Cfg Nat Nat :=
  { X := { net := { places := [0], transitions := [covTr "r" [0] none, covTr "T" [0] none] },
           timing := fun _ => .immediate, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => false,
    res := 0 }

/-- One token, 1, in place 0. -/
def loserM0 : QMarking Nat Nat := fun p => if p = 0 then [1] else []

/-- **The exception of E3, decided.** After the first update has armed `r` and `T` (both with
their clocks running, nothing in flight), the L3 segment starts `r`, which takes the token; its
action puts 9 back and is committed inside the pass; `T`, next in the pass's order, loses the
recheck (the token it was armed for is gone in the marking the pass sees); the next update finds
both enabled. The atomic grain reports `T`'s clock restart (`TransitionClockRestarted`); the
executor, which turned `T` off at the recheck, reports `TransitionEnabled` for both. -/
theorem atomic_loser_run :
    (xrun loserCfg (xinit loserM0 0) (covCyc ++ [.deadline []])).map
        (fun s => s.fl.isEmpty && decide (s.st "r" = .armed 0 false) &&
          decide (s.st "T" = .armed 0 false)) = some true ∧
    refTrace polRust loserCfg loserM0 0
        (covCyc ++ [.deadline []] ++ atomicLabels "r" 0 [(0, 9)] ["T"]) =
      some [.executionStarted, .markingSnapshot [(0, [1])], .transitionEnabled "r",
        .transitionEnabled "T", .tokenRemoved 0 1, .transitionStarted "r" [(0, 1)], .tokenAdded 0 9,
        .transitionCompleted "r" [(0, 9)] 0, .transitionEnabled "r", .transitionEnabled "T"] := by
  decide +kernel

/-! ### E4 on the scenario -/

/-- The scenario's state at the end of the run. -/
def covEnd : Option (XSt Nat Nat) := xrun covCfg (xinit covM0 0) covRun

/-- **The replay's enabled set is wider than the armed set** (ruling D83 (a)): at the end of the
scenario `w` is reaped, so not armed, and the replay of the Java and TypeScript trace still lists
it as enabled, because no event after its `TransitionEnabled` started it. The counts agree on
every declared place: one token in each of places 0, 5 and 6 and none elsewhere, as the executor
holds them. -/
theorem cov_replay_end :
    (evReplay covTraceJT).en "w" = true ∧ covEnd.map (fun s => s.st "w") = some .reaped ∧
      covEnd.map (fun s => covCfg.X.net.places.map fun p => (s.M p).length) =
        some (covCfg.X.net.places.map fun p => (evReplay covTraceJT).cnt p) := by
  decide +kernel

/-- **The snapshot is needed** (clash evt-c#11): the boot of an emission without snapshots
(`polNoSnap`) is `ExecutionStarted` alone, so the replay of the boot counts no token in place 0
where the initial marking holds one, and replay agreement fails at the boot. -/
theorem replayAgrees_needs_snapshot :
    ¬ ReplayAgrees covCfg (evReplay (refBoot polNoSnap covCfg covM0)) (xinit covM0 0) := by
  intro h
  have := h.1 0 (by decide)
  revert this
  decide

end E5

end Libpetri.Reference
