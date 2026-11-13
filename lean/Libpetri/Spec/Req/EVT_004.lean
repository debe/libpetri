import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Events
import Libpetri.Spec.Req.TIME_cycle

set_option linter.missingDocs true

/-!
# EVT-004: TransitionEnabled Event (`spec/08-events-observability.md`)

An enablement update reports each transition it arms that was not armed before it, with one
`TransitionEnabled` event naming it, and no other step reports one. "Enabled" in this requirement
means armed (rulings D5 and D39): a transition the marking keeps enabled is announced again when
the executor arms it again after its own firing, after the enablement recheck of a firing pass
disarmed it, or after a reap and a later write of one of its arc places. A transition that stays
armed across the update gets no `TransitionEnabled`, also when its clock restarts there: that
restart is `TransitionClockRestarted`'s ([EVT-005]).

The block is a predicate over an abstract executor with events `E : EvExec N T`
(`Reference/Events.lean`). It reads an event only through its kind and the transition name it
carries (`namedCount`), which every runtime's event carries, so it has no payload companion.
The witness is the reference executor with events `refEvExec` under both emission variants
(Java and TypeScript `polJT`, Rust and Python `polRust`). The wrong executors step as the
reference and emit otherwise: one that stays silent when a transition that has already started is
armed again, one that also announces a restarted transition as enabled, one that announces every
armed transition at every update, one that announces a transition as soon as a deposit enables
it in the marking, and one that announces the transitions the initial marking enables when the
run boots.

"Armed" is read from the executor's own clock status. What a start, a recheck or an update does
to that status is [TIME-010] and [TIME-012]'s (`TIME_012_cycle`), so a wrong executor that keeps
a started transition armed meets this block alone and is rejected only together with
`TIME_012_cycle` on the steps it takes (`EVT_004_allows_startKeepsArmed`).

The worked example (`evt004_cfg`): transition `T` (`delayed(5)`) and the refresh transition `r`
(immediate, synchronous) both take place 0's token. The first update arms both and reports both.
`r` starts, its action writes 9 back into place 0 and its completion is settled inside the pass.
At the next update `r`, which lost its clock when it started, is armed again and reported with
`TransitionEnabled`; `T`, whose clock restart is pending, stays armed and gets no
`TransitionEnabled` (it gets `TransitionClockRestarted`, [EVT-005]). With two tokens in place 0
(`evt004_m2`), `T` stays armed with its old stamp and gets neither event.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## Vocabulary -/

/-- The number of events of kind `k` in `evs` that name transition `n`. -/
def namedCount {N T : Type} (k : NetEventKind) (n : String) (evs : List (NetEvent N T)) : Nat :=
  evs.countP fun e => e.kind == k && e.trans? == some n

/-! ## EVT-004 -/

requirement EVT_004
  id "EVT-004"
  title "TransitionEnabled Event"
  kind B
  scope "all executors (event store enabled)"
  source verbatim "spec/08-events-observability.md"
  quote "Enabled in this requirement means armed: a transition that is armed again after its own firing, after the enablement recheck of a firing pass disarmed it, or after a reap and a later write of one of its arc places is announced again, even when the marking kept it enabled."
        "A transition whose clock restarts while it stays armed is announced with `TransitionClockRestarted` instead ([EVT-005])."
        "*When* a transition is armed after an enablement update and was not armed before it, the executor *shall* emit, at that update, exactly one TransitionEnabled event naming the transition."
        "The executor *shall* emit a TransitionEnabled event naming a transition only at an enablement update before which the transition was not armed and after which it is armed."
  reading "For every executor with events E and every configuration C:"
          "when the transition names of C's net are pairwise distinct, for every history H, an enablement update from state s to state s' that appends the events evs contains, for every name n, exactly one TransitionEnabled event naming n if n is a transition of the net that is not armed in s and armed in s', and none otherwise;"
          "the events a run emits before its first step contain no TransitionEnabled event, whatever the initial marking, and for every history H a step whose label is not the enablement update appends no TransitionEnabled event."
  assumes "The model is an executor with events E : EvExec N T (Reference/Events.lean): the events a run emits before its first step, and a step relation E.step C H s l evs s' saying that the step labelled l leads from s to s' and appends the events evs, given the events H emitted before it. The witness is the reference executor with events refEvExec, the reference executor RefExec with its emission refEmitW, under both emission variants (polJT for Java and TypeScript, polRust for Rust and Python). refEvExec_erase (Reference/EventsLink.lean) shows that it steps exactly as RefExec, so the block constrains what is emitted and nothing else. Both lines hold for every history H. The block reads an event only through its kind and the transition name it carries (namedCount), which every runtime's TransitionEnabled carries; the timestamp is not modelled (the epoch clock is the CORE-011 slice), so there is no payload companion."
          "Enabled is read as Armed (rulings D5 and D39, clash evt-a#1): armed is the executor's clock status (isArmedS of the status, GlossaryExec Status.armed), set only by the enablement update. The body sentence and both acceptance criteria say armed. Read as the marking-level Enabled, the requirement would contradict every runtime, which announce a transition again after its own firing and after a reaped transition is re-armed although the marking never disabled it (Rust post_fire and update_enablement in bitmap_backend.rs, emitted by update_enablement_and_emit in executor_core/executor.rs; Java updateDirtyTransitions in BitmapNetExecutor.java; TypeScript updateDirtyTransitions in bitmap-net-executor.ts). A transition whose clock restart is pending ([TIME-012], EVT-005) is still armed before the update (it keeps its old stamp until then), so it gets no TransitionEnabled: the second line of each block and the per-update image of TIME-012 AC6 are in EVT_005.lean."
          "Armed is read from the executor's own state, and the block says nothing about what a start, a recheck or an update does to that state: TIME_012_cycle (a start leaves the started transition off, the recheck's lose turns a transition off, the update stamps a pending transition afresh and clears its flag) and TIME_010_cycle do, on the same executor through W.erase = E in the joint theorem of the event blocks. So EVT-004 alone allows an executor whose start leaves the started transition armed with its old stamp; it reports nothing when r is armed again after its own firing in the worked example, and TIME_012_cycle line 2 rejects its steps (EVT_004_allows_startKeepsArmed). That executor is the slip of Rust post_fire without its enabled_flags clear (bitmap_backend.rs) or of Java's fire path without clearEnabledBit; no runtime ships it."
          "Line 1 is the third and fourth quoted sentences at the update: exactly one event for a transition that is armed after the update and was not armed before it (the markdown says exactly one), none for one that stays armed, none for one the update leaves unarmed. AC1 (emitted each time a transition that was not armed before an enablement update is armed after it) is the first case, AC2 (not emitted if the transition was already armed, also when its clock restarts) the second. The second quoted sentence is line 1 for a restarted transition, which is armed before the update and so gets no TransitionEnabled; that it gets one TransitionClockRestarted is EVT_005 line 1, and evt005_one_of (EVT_005.lean) shows that the two blocks together report each such update of a transition with exactly one of the two events. An executor that does not announce a transition that has already started in the run when it is armed again breaks line 1 (EVT_004_mutant_silentSelf, the event image of announcing on the marking-level edge), so does one that also announces a restarted transition (EVT_004_forbids_bothEvents) and one that announces every armed transition at every update (EVT_004_forbids_everyUpdate). The line counts per name, so it needs the names of the net pairwise distinct (ruling D10; the builders reject a duplicate name; the markdown states the assumption, as TIME-010 does for the timing requirements); the reference emits one event per declared transition."
          "Line 2 is the fourth quoted sentence away from the update: no TransitionEnabled at the boot of a run (the first update arms what the initial marking enables) and none at any other step. An executor that announces the transitions the initial marking enables when it boots breaks it (EVT_004_mutant_bootEnabled), and so does one that announces a transition as soon as a completion's deposit enables it in the marking, before an update arms it (EVT_004_mutant_atCommit). Every runtime emits TransitionEnabled at one place only, its enablement update (Rust update_enablement_and_emit in executor_core/executor.rs, Java updateDirtyTransitions in BitmapNetExecutor.java and PrecompiledNetExecutor.java, TypeScript updateDirtyTransitions in bitmap-net-executor.ts and precompiled-net-executor.ts), which Python runs on."
          "Not fixed here: the order of the TransitionEnabled and TransitionClockRestarted events inside one update (Rust emits every TransitionEnabled first, update_enablement_and_emit in executor_core/executor.rs; Java and TypeScript emit each event as they scan, so no line orders them), and which transitions an update may arm while a firing of them is in flight (ruling D8: Java and TypeScript skip a transition in flight, the isInFlight test of updateDirtyTransitions in BitmapNetExecutor.java and its inFlightFlags test in bitmap-net-executor.ts; Rust arms it again; both are runs of RefExec, Cfg.reentrant, and the line is an arming edge that holds for both). That every TransitionStarted of a transition follows a TransitionEnabled or TransitionClockRestarted of it since its previous start is a trace corollary not stated here. Assumptions shared by the executor event blocks: the event store is enabled (EVT-020; Rust skips the events when it is not, the NoopChangeTracker branch of update_enablement_and_emit in executor_core/executor.rs) and its append does not fail; an event is a value (EVT-001)."
          "The test derivation (add a token enabling a transition, verify TransitionEnabled for it) is EVT_004_nonvacuous: in the worked example the second update reports r, which its own start disarmed, and not T, which stays armed; the boot reports no TransitionEnabled although the initial marking enables both transitions; and with two tokens in place 0 the second update reports nothing for T, which keeps its stamp."
  signoff "2026-11-13 7f2ec3f635627dab ai"
  statement : ∀ {N T : Type} [DecidableEq N], EvExec N T → Prop :=
    fun E => ∀ C,
      (NamesDistinct C.X → ∀ H evs n, on (fun s s' => E.step C H s .update evs s'), shall
        (fun s s' => namedCount .transitionEnabled n evs =
          if n ∈ C.X.net.transitions.map (·.core.name) ∧ isArmedS (s.st n) = false ∧
              isArmedS (s'.st n) = true then 1 else 0)) ∧
      ((∀ M0, ∀ e ∈ E.boot C M0, e.kind ≠ .transitionEnabled) ∧
        ∀ H l evs, l ≠ .update → on (fun s s' => E.step C H s l evs s'), shall (fun _ _ =>
          ∀ e ∈ evs, e.kind ≠ .transitionEnabled))

/- The pinned readable form of EVT-004: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EVT_004 : {N T : Type} → [DecidableEq N] → EvExec N T → Prop :=
fun {N T} [DecidableEq N] E =>
  ∀ (C : Cfg N T),
    (NamesDistinct C.X →
        ∀ (H evs : List (NetEvent N T)) (n : String),
          on fun s s' => E.step C H s XLbl.update evs s', shall fun s s' =>
            namedCount NetEventKind.transitionEnabled n evs =
              if
                  n ∈ List.map (fun x => x.core.name) C.X.net.transitions ∧
                    isArmedS (s.st n) = false ∧ isArmedS (s'.st n) = true then
                1
              else 0) ∧
      (∀ (M0 : QMarking N T), ∀ e ∈ E.boot C M0, e.kind ≠ NetEventKind.transitionEnabled) ∧
        ∀ (H : List (NetEvent N T)) (l : XLbl N T) (evs : List (NetEvent N T)),
          l ≠ XLbl.update →
            on fun s s' => E.step C H s l evs s', shall fun x x_1 => ∀ e ∈ evs, e.kind ≠ NetEventKind.transitionEnabled
-/
#guard_msgs in #print EVT_004

/-! ## The two lines, one at a time -/

section Lines

variable {N T : Type} [DecidableEq N] [Ord N]
/-- Line 1 of `EVT_004` alone: an update announces exactly the transitions it arms that were not
armed before it, once each. -/
def evt004_line1 (E : EvExec N T) : Prop :=
  ∀ C, NamesDistinct C.X → ∀ H evs n, on (fun s s' => E.step C H s .update evs s'), shall
    (fun s s' => namedCount .transitionEnabled n evs =
      if n ∈ C.X.net.transitions.map (·.core.name) ∧ isArmedS (s.st n) = false ∧
          isArmedS (s'.st n) = true then 1 else 0)

/-- Line 2 of `EVT_004` alone: nothing but an update emits a `TransitionEnabled` event, neither the
boot nor a step with another label. -/
def evt004_line2 (E : EvExec N T) : Prop :=
  ∀ C, (∀ M0, ∀ e ∈ E.boot C M0, e.kind ≠ .transitionEnabled) ∧
    ∀ H l evs, l ≠ .update → on (fun s s' => E.step C H s l evs s'), shall (fun _ _ =>
      ∀ e ∈ evs, e.kind ≠ .transitionEnabled)

omit [Ord N] in
/-- `EVT_004` is its two lines. -/
theorem evt004_iff (E : EvExec N T) : EVT_004 E ↔ evt004_line1 E ∧ evt004_line2 E :=
  ⟨fun h => ⟨fun C => (h C).1, fun C => (h C).2⟩, fun h C => ⟨h.1 C, h.2 C⟩⟩

end Lines

/-! ## Counting the events that name a transition -/

section Count

variable {N T : Type}

/-- Counting over a concatenation. -/
theorem namedCount_append (k : NetEventKind) (n : String) (a b : List (NetEvent N T)) :
    namedCount k n (a ++ b) = namedCount k n a + namedCount k n b :=
  List.countP_append ..

/-- A list with no event of kind `k` names no transition with kind `k`. -/
theorem namedCount_eq_zero {k : NetEventKind} {n : String} {evs : List (NetEvent N T)}
    (h : ∀ e ∈ evs, e.kind ≠ k) : namedCount k n evs = 0 := by
  unfold namedCount
  rw [List.countP_eq_zero]
  intro e he
  simp [h e he]

/-- One event per name of a duplicate-free list that passes `f`: each passing name is counted
once, every other name not at all. -/
theorem namedCount_filterMap {k : NetEventKind} {mk : String → NetEvent N T}
    (hk : ∀ m, (mk m).kind = k) (ht : ∀ m, (mk m).trans? = some m) (f : String → Bool)
    (n : String) : ∀ l : List String, l.Nodup →
      namedCount k n (l.filterMap fun m => if f m then some (mk m) else none) =
        if n ∈ l ∧ f n = true then 1 else 0
  | [], _ => by simp [namedCount]
  | m :: l, hnd => by
    obtain ⟨hm, hl⟩ := List.nodup_cons.1 hnd
    have ih := namedCount_filterMap hk ht f n l hl
    by_cases hmn : m = n
    · subst hmn
      rw [if_neg (by simp [hm])] at ih
      cases hf : f m <;> simp [hf, namedCount, hk, ht] at ih ⊢ <;> exact ih
    · have hne : (n ∈ m :: l) ↔ n ∈ l := by simp [Ne.symm hmn]
      cases hf : f m <;>
        simp [hf, namedCount, hk, ht, hmn, hne] at ih ⊢ <;> exact ih

end Count

/-! ## The reference -/

section Reference

variable {N T : Type} [DecidableEq N] [Ord N]
omit [Ord N] in
/-- The reference update never arms a reaped name: it keeps it reaped (design R9), or turns a
name outside the net off. -/
theorem updSt_reaped_not_armed {C : Cfg N T} {s : XSt N T} {n : String}
    (h : s.st n = .reaped) : isArmedS (updSt refXPol C s n) = false := by
  unfold updSt
  cases findT C n <;> simp [h, refXPol, isArmedS]

omit [Ord N] in
/-- At a reference update, "off before" and "not armed before" agree for a name armed after. -/
theorem ref_update_off_iff {C : Cfg N T} {s s' : XSt N T} (hx : xstep C s .update = some s')
    (n : String) :
    (s.st n = .off ∧ isArmedS (s'.st n) = true) ↔
      (isArmedS (s.st n) = false ∧ isArmedS (s'.st n) = true) := by
  obtain ⟨-, -, rfl⟩ := xstepW_update hx
  cases h : s.st n with
  | off => simp [isArmedS]
  | armed k b => simp [isArmedS]
  | reaped =>
    have h2 := updSt_reaped_not_armed (C := C) h
    simp only [isArmedS] at h2 ⊢
    simp [h2]

/-- The `TransitionEnabled` events of a reference update: one per net name that goes from off to
armed. -/
theorem refEmitW_update_enabled (P : EvPol) {C : Cfg N T} (hd : NamesDistinct C.X)
    (H : List (NetEvent N T)) {s s' : XSt N T} (hx : xstep C s .update = some s') (n : String) :
    namedCount .transitionEnabled n (refEmitW P C H s .update s') =
      if n ∈ C.X.net.transitions.map (·.core.name) ∧ isArmedS (s.st n) = false ∧
          isArmedS (s'.st n) = true then 1 else 0 := by
  simp only [refEmitW, netNames]
  rw [namedCount_append,
    namedCount_filterMap (mk := NetEvent.transitionEnabled) (fun _ => rfl) (fun _ => rfl)
      (fun m => decide (s.st m = .off) && isArmedS (s'.st m)) n _ hd,
    namedCount_eq_zero (k := .transitionEnabled), Nat.add_zero]
  · have := ref_update_off_iff hx n
    by_cases hm : n ∈ C.X.net.transitions.map (·.core.name)
    · simp only [hm, true_and, Bool.and_eq_true, decide_eq_true_eq]
      by_cases hc : isArmedS (s.st n) = false ∧ isArmedS (s'.st n) = true
      · rw [if_pos (this.2 hc), if_pos hc]
      · rw [if_neg (fun h => hc (this.1 h)), if_neg hc]
    · simp [hm]
  · intro e he
    simp only [List.mem_filterMap] at he
    obtain ⟨m, -, hm⟩ := he
    split at hm
    · cases hm; simp [NetEvent.kind]
    · cases hm

/-- No step of the reference but an update emits `TransitionEnabled`. -/
theorem refEmitW_noEnabled (P : EvPol) (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T)
    {l : XLbl N T} (hl : l ≠ .update) (s' : XSt N T) :
    ∀ e ∈ refEmitW P C H s l s', e.kind ≠ .transitionEnabled := by
  intro e he hk
  have := refEmitW_kind P C H s l s' e he
  rw [hk] at this
  cases l with
  | update => exact hl rfl
  | _ => simp [lblKinds] at this

/-- The reference boot emits no `TransitionEnabled`. -/
theorem refBoot_noEnabled (P : EvPol) (C : Cfg N T) (M0 : QMarking N T) :
    ∀ e ∈ refBoot P C M0, e.kind ≠ .transitionEnabled := by
  intro e he hk
  rcases refBoot_kind P C M0 e he with h | h <;> rw [hk] at h <;> cases h

/-- Line 1 holds of every executor that steps as the reference and emits as the reference at an
update, whatever it emits elsewhere and whatever its boot. -/
theorem evt004_line1_of_refUpdate (P : EvPol)
    {boot : Cfg N T → QMarking N T → List (NetEvent N T)}
    {emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    (he : ∀ C H s s', emit C H s .update s' = refEmitW P C H s .update s') :
    evt004_line1 (emitExec boot emit) := by
  intro C hd H evs n s s' hs
  obtain ⟨hx, rfl⟩ := hs
  rw [he]
  exact refEmitW_update_enabled P hd H hx n

/-- Line 2 holds of every executor whose boot is the reference's and whose steps other than the
update emit as the reference. -/
theorem evt004_line2_of_refOff
    {emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    (P : EvPol) (he : ∀ C H s l s', l ≠ .update → emit C H s l s' = refEmitW P C H s l s') :
    evt004_line2 (emitExec (refBoot P) emit) := by
  intro C
  refine ⟨refBoot_noEnabled P C, fun H l evs hl s s' hs => ?_⟩
  obtain ⟨-, rfl⟩ := hs
  rw [he C H s l s' hl]
  exact refEmitW_noEnabled P C H s hl s'

/-- The reference meets EVT-004 under every emission variant. -/
theorem evt004_ref (P : EvPol) : EVT_004 (refEvExec (N := N) (T := T) P) :=
  (evt004_iff _).2 ⟨evt004_line1_of_refUpdate P fun _ _ _ _ => rfl, evt004_line2_of_refOff P fun _ _ _ _ _ _ => rfl⟩

/-- ✓ The reference executor with the Java and TypeScript emission meets EVT-004: each update
reports, once, every transition it arms that was not armed before it, and nothing else reports
`TransitionEnabled`. -/
@[evidence holds EVT_004]
theorem EVT_004_reference : EVT_004 (refEvExec (N := N) (T := T) polJT) := evt004_ref polJT

/-- ✓ The reference executor with the Rust and Python emission meets EVT-004 too: the block is a
line for every executor. -/
@[evidence holds EVT_004]
theorem EVT_004_rust : EVT_004 (refEvExec (N := N) (T := T) polRust) := evt004_ref polRust

end Reference

/-! ## The worked example -/

/-- `T`: takes the token of place 0; `delayed(5)` in `evt004_cfg`. -/
def evt004_tT : Trans Nat :=
  { core := { name := "T", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- `r`, the refresh: takes the token of place 0; immediate in `evt004_cfg`. -/
def evt004_tR : Trans Nat :=
  { core := { name := "r", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- The configuration of the example: places 0 and 1, `T` with `delayed(5)`, `r` immediate, one
priority, no terminal or environment place, every output valid. -/
def evt004_cfg : Cfg Nat Nat :=
  { X := { net := { places := [0, 1], transitions := [evt004_tT, evt004_tR] },
           timing := fun u => if u.core.name = "T" then .delayed 5 else .immediate, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => false,
    res := 0 }

/-- One token in place 0: the refresh takes `T`'s only token ([TIME-012] AC1). -/
def evt004_m1 : QMarking Nat Nat := fun p => if p = 0 then [1] else []

/-- Two tokens in place 0: the refresh leaves one for `T` ([TIME-012] AC4, surplus). -/
def evt004_m2 : QMarking Nat Nat := fun p => if p = 0 then [1, 2] else []

/-- The run: cycle 1 arms `T` and `r`; `r` (ready; `T` is not, it waits 5 ms) starts
synchronously, its action writes 9 into place 0 and returns, and its completion is settled in the
pass; cycle 2, one millisecond later, ends with its update. -/
def evt004_run : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin,
   .start "r" true, .write 0 0 9, .ret 0 true, .commit 0, .endPass,
   .endCompletions, .endPublications, .endEvents, .delay 1]

/-- The state before the second update, from initial marking `m`. -/
def evt004_beforeUpdate (m : QMarking Nat Nat) : Option (XSt Nat Nat) :=
  xrun evt004_cfg (xinit m 0) evt004_run

/-- The names of the example are distinct. -/
theorem evt004_cfg_distinct : NamesDistinct evt004_cfg.X := by
  unfold NamesDistinct; decide

/-- ✓ Both lines of EVT-004 are exercised by the reference: at the second update of the example
`r`, which its own start disarmed although place 0 was refilled at once, is armed again and
reported with one `TransitionEnabled`, while `T`, armed before and after, gets none; with two
tokens in place 0 the second update reports nothing for `T`, which stays armed; and the boot emits
events, none a `TransitionEnabled`, although the initial marking enables both transitions. -/
@[evidence nonvacuous EVT_004]
theorem EVT_004_nonvacuous :
    (∃ s s' evs, (refEvExec polJT).step evt004_cfg [] s .update evs s' ∧
      namedCount .transitionEnabled "r" evs = 1 ∧ s.st "r" = .off ∧ isArmedS (s'.st "r") = true ∧
      namedCount .transitionEnabled "T" evs = 0 ∧ isArmedS (s.st "T") = true ∧
      isArmedS (s'.st "T") = true) ∧
    (∃ s s' evs, (refEvExec polJT).step evt004_cfg [] s .update evs s' ∧
      namedCount .transitionEnabled "T" evs = 0 ∧ s.st "T" = .armed 0 false ∧
      s'.st "T" = .armed 0 false) ∧
    ((refEvExec (N := Nat) (T := Nat) polJT).boot evt004_cfg evt004_m1 ≠ [] ∧
      ∀ e ∈ (refEvExec (N := Nat) (T := Nat) polJT).boot evt004_cfg evt004_m1,
        e.kind ≠ .transitionEnabled) := by
  refine ⟨?_, ?_, by decide +kernel⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt004_cfg)
      (o := evt004_beforeUpdate evt004_m1) (l := .update)
      (p := fun s s' =>
        let evs := refEmitW polJT evt004_cfg [] s .update s'
        namedCount .transitionEnabled "r" evs == 1 && s.st "r" == .off && isArmedS (s'.st "r") &&
          namedCount .transitionEnabled "T" evs == 0 && isArmedS (s.st "T") &&
          isArmedS (s'.st "T"))
      (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hp
    exact ⟨s, s', _, ⟨hs, rfl⟩, h1, h2, h3, h4, h5, h6⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt004_cfg)
      (o := evt004_beforeUpdate evt004_m2) (l := .update)
      (p := fun s s' =>
        namedCount .transitionEnabled "T" (refEmitW polJT evt004_cfg [] s .update s') == 0 &&
          s.st "T" == .armed 0 false && s'.st "T" == .armed 0 false)
      (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    exact ⟨s, s', _, ⟨hs, rfl⟩, h1, h2, h3⟩

/-! ## Wrong executors: the reference's steps, another emission -/

section Mutants

variable {N T : Type} [DecidableEq N] [Ord N]
/-- The Java and TypeScript emission with the events of an update replaced by `f C H s s'`. -/
def evt004_atUpdate
    (f : Cfg N T → List (NetEvent N T) → XSt N T → XSt N T → List (NetEvent N T))
    (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T) (l : XLbl N T) (s' : XSt N T) :
    List (NetEvent N T) :=
  match l with
  | .update => f C H s s'
  | _ => refEmitW polJT C H s l s'

/-- Away from an update, `evt004_atUpdate` emits as the reference. -/
theorem evt004_atUpdate_other
    (f : Cfg N T → List (NetEvent N T) → XSt N T → XSt N T → List (NetEvent N T))
    (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T) {l : XLbl N T} (hl : l ≠ .update)
    (s' : XSt N T) : evt004_atUpdate f C H s l s' = refEmitW polJT C H s l s' := by
  cases l with
  | update => exact absurd rfl hl
  | _ => rfl

/-- An executor that changes only what an update emits keeps line 2. -/
theorem evt004_atUpdate_line2
    (f : Cfg N T → List (NetEvent N T) → XSt N T → XSt N T → List (NetEvent N T)) :
    evt004_line2 (emitExec (refBoot polJT) (evt004_atUpdate f)) :=
  evt004_line2_of_refOff polJT fun C H s _ s' hl => evt004_atUpdate_other f C H s hl s'

/-- The update events without the `TransitionEnabled` of a transition that has started before in
the run (history `H`): the transition is announced only the first time it is armed. -/
def evt004_silentSelfEvs (C : Cfg N T) (H : List (NetEvent N T)) (s s' : XSt N T) :
    List (NetEvent N T) :=
  (refEmitW polJT C H s .update s').filter fun e =>
    !(e.kind == .transitionEnabled &&
      H.any fun h => h.kind == .transitionStarted && h.trans? == e.trans?)

/-- The executor that does not announce a transition that has already started when it is armed
again (the event image of announcing on the marking-level Enabled edge). -/
def evt004_silentSelf : EvExec N T :=
  emitExec (refBoot polJT) (evt004_atUpdate evt004_silentSelfEvs)

/-- The update events with one more `TransitionEnabled` for each name whose clock restart was
pending and that stays armed. -/
def evt004_bothEvs (C : Cfg N T) (H : List (NetEvent N T)) (s s' : XSt N T) :
    List (NetEvent N T) :=
  refEmitW polJT C H s .update s' ++ (netNames C).filterMap fun n =>
    if pendingS (s.st n) && isArmedS (s'.st n) then some (.transitionEnabled n) else none

/-- The executor that reports a clock restart with both events. -/
def evt004_bothEvents : EvExec N T :=
  emitExec (refBoot polJT) (evt004_atUpdate evt004_bothEvs)

/-- The update events with one more `TransitionEnabled` for each name armed before and after. -/
def evt004_everyUpdateEvs (C : Cfg N T) (H : List (NetEvent N T)) (s s' : XSt N T) :
    List (NetEvent N T) :=
  refEmitW polJT C H s .update s' ++ (netNames C).filterMap fun n =>
    if isArmedS (s.st n) && isArmedS (s'.st n) then some (.transitionEnabled n) else none

/-- The executor that announces every armed transition at every update. -/
def evt004_everyUpdate : EvExec N T :=
  emitExec (refBoot polJT) (evt004_atUpdate evt004_everyUpdateEvs)

/-- The Java and TypeScript boot events followed by one `TransitionEnabled` for each transition
the initial marking enables. -/
def evt004_bootEnabledEvs (C : Cfg N T) (M0 : QMarking N T) : List (NetEvent N T) :=
  refBoot polJT C M0 ++ (C.X.net.transitions.filter fun u => enabledNA (qCount M0) u.core).map
    fun u => .transitionEnabled u.core.name

/-- The executor that steps and emits as the reference but announces the transitions the initial
marking enables when the run boots. -/
def evt004_bootEnabled : EvExec N T := emitExec evt004_bootEnabledEvs (refEmitW polJT)

/-- The Java and TypeScript emission, with a completion also announcing each transition that
is not armed and that the marking after its deposit enables. -/
def evt004_atCommitEmit (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T) (l : XLbl N T)
    (s' : XSt N T) : List (NetEvent N T) :=
  match l with
  | .commit _ => refEmitW polJT C H s l s' ++
      (C.X.net.transitions.filter fun u =>
        !isArmedS (s.st u.core.name) && enabledNA (qCount s'.M) u.core).map
        fun u => .transitionEnabled u.core.name
  | _ => refEmitW polJT C H s l s'

/-- The executor that announces a transition as soon as a deposit enables it in the marking,
before any update arms it. -/
def evt004_atCommit : EvExec N T := emitExec (refBoot polJT) evt004_atCommitEmit

end Mutants

/-- The history of the example before its second update: `r` has started. -/
def evt004_hist : List (NetEvent Nat Nat) := [.transitionStarted "r" [(0, 1)]]

/-- ✗ Not announcing a transition that has already started when it is armed again violates
EVT-004 (line 1): at the second update of the example `r`, which its start disarmed, is armed
again, and this executor reports nothing for it because `r` started before. The marking never
disabled `r` (its action refilled place 0 in the same pass), so this is also what an executor
announcing on the marking-level Enabled edge reports. The executor keeps line 2. -/
@[evidence mutant EVT_004]
theorem EVT_004_mutant_silentSelf :
    evt004_line2 (evt004_silentSelf (N := Nat) (T := Nat)) ∧
      ¬ EVT_004 (evt004_silentSelf (N := Nat) (T := Nat)) := by
  refine ⟨evt004_atUpdate_line2 _, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt004_cfg)
    (o := evt004_beforeUpdate evt004_m1) (l := .update)
    (p := fun s s' => decide (namedCount .transitionEnabled "r"
        (evt004_silentSelfEvs evt004_cfg evt004_hist s s') ≠
      if "r" ∈ evt004_cfg.X.net.transitions.map (·.core.name) ∧ isArmedS (s.st "r") = false ∧
          isArmedS (s'.st "r") = true then 1 else 0))
    (by decide +kernel)
  exact of_decide_eq_true hp
    ((h evt004_cfg).1 evt004_cfg_distinct evt004_hist _ "r" s s' ⟨hs, rfl⟩)

/-- ✗ Reporting a clock restart with a `TransitionEnabled` as well violates EVT-004 (line 1): at
the second update of the example `T`, whose clock restart is pending, stays armed, and this
executor reports a `TransitionEnabled` for it. -/
@[evidence forbids EVT_004]
theorem EVT_004_forbids_bothEvents : ¬ EVT_004 (evt004_bothEvents (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt004_cfg)
    (o := evt004_beforeUpdate evt004_m1) (l := .update)
    (p := fun s s' => decide (namedCount .transitionEnabled "T"
        (evt004_bothEvs evt004_cfg [] s s') ≠
      if "T" ∈ evt004_cfg.X.net.transitions.map (·.core.name) ∧ isArmedS (s.st "T") = false ∧
          isArmedS (s'.st "T") = true then 1 else 0))
    (by decide +kernel)
  exact of_decide_eq_true hp ((h evt004_cfg).1 evt004_cfg_distinct [] _ "T" s s' ⟨hs, rfl⟩)

/-- ✗ Announcing every armed transition at every update violates EVT-004 (line 1, AC2): with two
tokens in place 0, `T` stays armed with its stamp across the second update, and this executor
reports a `TransitionEnabled` for it again. -/
@[evidence forbids EVT_004]
theorem EVT_004_forbids_everyUpdate : ¬ EVT_004 (evt004_everyUpdate (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt004_cfg)
    (o := evt004_beforeUpdate evt004_m2) (l := .update)
    (p := fun s s' => decide (namedCount .transitionEnabled "T"
        (evt004_everyUpdateEvs evt004_cfg [] s s') ≠
      if "T" ∈ evt004_cfg.X.net.transitions.map (·.core.name) ∧ isArmedS (s.st "T") = false ∧
          isArmedS (s'.st "T") = true then 1 else 0))
    (by decide +kernel)
  exact of_decide_eq_true hp ((h evt004_cfg).1 evt004_cfg_distinct [] _ "T" s s' ⟨hs, rfl⟩)

/-- ✗ Announcing the transitions the initial marking enables when the run boots violates
EVT-004 (line 2): the boot of the example reports `T` before any update has armed it. Every step
of this executor emits as the reference, so it keeps line 1. -/
@[evidence mutant EVT_004]
theorem EVT_004_mutant_bootEnabled :
    evt004_line1 (evt004_bootEnabled (N := Nat) (T := Nat)) ∧
      ¬ EVT_004 (evt004_bootEnabled (N := Nat) (T := Nat)) := by
  refine ⟨evt004_line1_of_refUpdate polJT fun _ _ _ _ => rfl, fun h => ?_⟩
  have hm : NetEvent.transitionEnabled "T" ∈
      evt004_bootEnabled.boot evt004_cfg evt004_m1 := by decide +kernel
  exact (h evt004_cfg).2.1 evt004_m1 _ hm rfl

/-- ✗ Announcing a transition when a deposit enables it in the marking violates EVT-004
(line 2): in the example the completion of `r`, settled inside the pass, puts 9 back into place 0,
and this executor reports `TransitionEnabled` for `r` at that completion, before any update has
armed it. Its updates report as the reference, so it keeps line 1. -/
@[evidence mutant EVT_004]
theorem EVT_004_mutant_atCommit :
    evt004_line1 (evt004_atCommit (N := Nat) (T := Nat)) ∧
      ¬ EVT_004 (evt004_atCommit (N := Nat) (T := Nat)) := by
  refine ⟨evt004_line1_of_refUpdate polJT fun _ _ _ _ => rfl, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt004_cfg)
    (o := xrun evt004_cfg (xinit evt004_m1 0) (evt004_run.take 9)) (l := .commit 0)
    (p := fun s s' => (evt004_atCommitEmit evt004_cfg [] s (.commit 0) s').any
      fun e => e.kind == .transitionEnabled)
    (by decide +kernel)
  simp only [List.any_eq_true, beq_iff_eq] at hp
  obtain ⟨e, he, hk⟩ := hp
  exact (h evt004_cfg).2.2 [] (.commit 0) _ (by simp) s s' ⟨hs, rfl⟩ e he hk

/-! ## Wrong steps: what the block leaves to [TIME-012] -/

section StepExec

variable {N T : Type} [DecidableEq N] [Ord N]
/-- The executor with events that steps by the step function `g` and emits as the reference
with the Java and TypeScript emission. -/
def evtStepExec (g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)) : EvExec N T where
  boot := refBoot polJT
  step := fun C H s l evs s' => g C s l = some s' ∧ evs = refEmitW polJT C H s l s'

/-- A run of the step function `g` from state `s`, as a fold. -/
def evtRunWith (g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)) (C : Cfg N T) :
    XSt N T → List (XLbl N T) → Option (XSt N T)
  | s, [] => some s
  | s, l :: ls => (g C s l).bind fun s' => evtRunWith g C s' ls

/-- Every executor that updates as the reference and emits as the reference meets EVT-004,
whatever its other steps do to the clock status. -/
theorem evt004_stepExec (g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T))
    (hg : ∀ C s, g C s .update = xstep C s .update) : EVT_004 (evtStepExec g) := by
  intro C
  refine ⟨fun hd H evs n s s' hs => ?_, refBoot_noEnabled polJT C, fun H l evs hl s s' hs => ?_⟩
  · obtain ⟨hx, rfl⟩ := hs
    rw [hg] at hx
    exact refEmitW_update_enabled polJT hd H hx n
  · obtain ⟨-, rfl⟩ := hs
    exact refEmitW_noEnabled polJT C H s hl s'

/-- The reference step, except that a start leaves the started transition with the status it
had before (armed, with its old stamp). -/
def evt004_startKeepsStep (C : Cfg N T) (s : XSt N T) (l : XLbl N T) : Option (XSt N T) :=
  match l with
  | .start n sy => (xstep C s (.start n sy)).map fun s' =>
      { s' with st := fun m => if m = n then s.st m else s'.st m }
  | l => xstep C s l

end StepExec

/-- ✓ EVT-004 alone allows an executor whose start leaves the started transition armed: in the
worked example `r` fires and its action puts a token back into place 0, and at the next update
this executor reports no `TransitionEnabled` for `r`, because by its own clock status `r` never
stopped being armed. What a start does to that status is [TIME-012]'s: its companion line on
the cycle (a start leaves the started transition off) rejects the steps of this executor, so only
the two requirements together, on the same executor, rule it out. -/
@[evidence allows EVT_004]
theorem EVT_004_allows_startKeepsArmed :
    EVT_004 (evtStepExec (N := Nat) (T := Nat) evt004_startKeepsStep) ∧
      (∃ s s' evs, (evtStepExec evt004_startKeepsStep).step evt004_cfg evt004_hist s .update
          evs s' ∧ namedCount .transitionEnabled "r" evs = 0 ∧ isArmedS (s'.st "r") = true) ∧
      ¬ TIME_012_cycle (evtStepExec (N := Nat) (T := Nat) evt004_startKeepsStep).erase := by
  refine ⟨evt004_stepExec _ fun _ _ => rfl, ?_, fun h => ?_⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check evt004_startKeepsStep (C := evt004_cfg)
      (o := evtRunWith evt004_startKeepsStep evt004_cfg (xinit evt004_m1 0) evt004_run)
      (l := .update)
      (p := fun s s' => namedCount .transitionEnabled "r"
          (refEmitW polJT evt004_cfg evt004_hist s .update s') == 0 && isArmedS (s'.st "r"))
      (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', _, ⟨hs, rfl⟩, hp.1, hp.2⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check evt004_startKeepsStep (C := evt004_cfg)
      (o := evtRunWith evt004_startKeepsStep evt004_cfg (xinit evt004_m1 0) (evt004_run.take 6))
      (l := .start "r" true) (p := fun _ s' => decide (s'.st "r" ≠ .off)) (by decide +kernel)
    exact of_decide_eq_true hp ((h evt004_cfg).2.1 "r" true s s' ⟨[], _, hs, rfl⟩)

end Libpetri.Spec
