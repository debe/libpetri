import Libpetri.Spec.Req.EVT_004

set_option linter.missingDocs true

/-!
# EVT-005: TransitionClockRestarted Event (`spec/08-events-observability.md`)

An enablement update reports each transition whose clock restart was pending before it and whose
clock it restarts (it leaves the transition armed with the update's reading as its stamp and no
restart pending), with exactly one `TransitionClockRestarted` event naming it, and no other step
reports one. A clock restart is pending (`pendingS`, the executor status `armed _ true`) when a start of
another transition left the transition not enabled in its intermediate marking ([TIME-012],
ruling D7) and the executor has not disarmed it since: neither the enablement recheck of the
pass nor a start of its own. Such a transition keeps its old stamp until the next update, which
stamps it afresh if it finds it enabled. If the executor did disarm it (it "observed the gap"),
it is not armed at the update, and the update that arms it again reports `TransitionEnabled`
([EVT-004]); if the update finds it disabled, it goes off and nothing is reported.

The block is a predicate over an abstract executor with events `E : EvExec N T`
(`Reference/Events.lean`); it reads an event only through its kind and the transition name it
carries (`namedCount`, `EVT_004.lean`). The witness is the reference executor with events
`refEvExec` under both emission variants. The wrong executors step as the reference and emit
otherwise: one that reports no restart, one that reports a restart already at the start that
took the clock, one that reports a restart when the run boots, and one that reports a transition
armed again after its own firing as restarted. Two wrong executors also step otherwise: one whose
update reports the restart but keeps the old stamp, and one whose update does not clear the restart
flag and so reports the restart again at every later update; line 1 rejects both, because it asks
for the fresh stamp. "Pending" is read from the executor's own status, and when a start sets it is
[TIME-012]'s (`TIME_012_cycle`): an executor that never flags a restart meets this block alone and
is rejected only together with `TIME_012_cycle` on its steps (`EVT_005_allows_neverFlags`).

Together with [EVT-004], every update that arms a transition afresh or restarts its pending clock
reports it with exactly one of the two events (`evt005_one_of`, [TIME-012] AC6), and a transition that
keeps its clock across a firing gets neither ([TIME-012] AC4).

The worked example is EVT-004's (`evt004_cfg`): `T` (`delayed(5)`) and the refresh `r` share
place 0's only token; `r` starts synchronously, which makes `T`'s clock restart pending, and its
action puts a token back in the same pass. The next update reports `TransitionEnabled` for `r` and
`TransitionClockRestarted` for `T`. When `r`'s action is asynchronous and returns only after the
next update (`evt005_gapRun`), that update finds `T` disabled and turns it off, and the update
after the deposit reports `TransitionEnabled` for `T` instead. So does a pass in which `T` is ready
and comes after `r` (`evt005_readyCfg`): the pass rechecks `T` after `r`'s consumption, `T` loses
its clock there, and the next update reports `TransitionEnabled` for it.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

requirement EVT_005
  id "EVT-005"
  title "TransitionClockRestarted Event"
  kind B
  scope "all executors (event store enabled)"
  source verbatim "spec/08-events-observability.md"
  quote "A transition's clock restart is pending when it is armed, a start of another transition since the last enablement update left it not enabled in that start's intermediate marking ([TIME-012]), and neither the enablement recheck of a firing pass nor a start of its own has disarmed it since."
        "An enablement update restarts the clock of a transition when it leaves the transition armed with the update's clock reading as its stamp and its clock restart no longer pending."
        "*When* an enablement update restarts the clock of a transition whose clock restart was pending before the update, the executor *shall* emit, at that update, exactly one TransitionClockRestarted event naming the transition."
        "The executor *shall* emit a TransitionClockRestarted event naming a transition only at an enablement update before which the transition's clock restart was pending and that restarts the transition's clock."
  reading "For every executor with events E and every configuration C:"
          "when the transition names of C's net are pairwise distinct, for every history H, an enablement update from state s to state s' that appends the events evs contains, for every name n, exactly one TransitionClockRestarted event naming n if n is a transition of the net whose clock restart is pending in s and whose status in s' is armed at the cycle reading of s' with no restart pending, and none otherwise;"
          "the events a run emits before its first step contain no TransitionClockRestarted event, whatever the initial marking, and for every history H a step whose label is not the enablement update appends no TransitionClockRestarted event."
  assumes "The model is an executor with events E : EvExec N T (Reference/Events.lean), as in EVT_004: the boot events of a run and a step relation E.step C H s l evs s' with the history H of the events emitted before the step. The witness is refEvExec, RefExec with its emission refEmitW, under both emission variants (polJT for Java and TypeScript, polRust for Rust and Python); refEvExec_erase (Reference/EventsLink.lean) shows that it steps exactly as RefExec. Both lines hold for every history H. The block reads an event only through its kind and the transition name it carries (namedCount, EVT_004.lean); the timestamp is not modelled, so there is no payload companion."
          "Restart pending is the executor status Status.armed k true (pendingS, the proposed glossary term Restart pending of Reference/Events.lean; rulings D5, D7 and D39, clashes evt-a#2 and evt-a#15): afterStart sets it on every other armed transition the start's live intermediate marking disables (TIME-012); a start of the transition itself turns it off, the enablement recheck of the pass turns it off (lose), and the next update clears it, re-stamping the transition if it finds it enabled and turning it off otherwise. This is the observed gap of the body: the runtimes keep the enabled flag of such a transition and set a restart bit (Rust bitmap_backend.rs flag_clock_restarts 425-439 and update_enablement 624-639; Java BitmapNetExecutor.java 1324-1336; TypeScript bitmap-net-executor.ts 760-780), and clear the enabled flag on a failed recheck while the bit is ignored, so the next update reports TransitionEnabled (Rust executor_core/executor.rs 423-435, bitmap_backend.rs disable 892-898). Java does not flag a transition in flight (BitmapNetExecutor.java 1872) and Rust does; in RefExec a transition in flight is off and never flagged, so both are runs of it (ruling D8). A restart of the clock is the status the update leaves: armed at the update's reading s'.cyc with the flag cleared (Status.armed s'.cyc false), which is what TIME_012_cycle line 3 says an update does to a pending transition it finds enabled; at a reference update a pending transition is armed after it exactly when this holds (updW_pending_iff). Pending is read from the executor's own state, and when a start sets it is TIME_012_cycle line 1's, on the same executor through W.erase = E in the joint theorem of the event blocks. So EVT-005 alone allows an executor whose start never flags a restart: in the worked example it reports neither event for T, which keeps its old stamp, and TIME_012_cycle line 1 rejects its steps (EVT_005_allows_neverFlags)."
          "Line 1 is the second, third and fourth quoted sentences at the update: exactly one event for a transition whose clock restart was pending and whose clock the update restarts (the markdown says exactly one), none for any other name, so none on initial enablement and none on re-enablement after an observed disablement (AC2: both are TransitionEnabled, EVT_004 line 1), and none for a transition that keeps its clock (TIME-012 AC4, EVT_005_time012_ac4). AC1 (emitted only when the transition stays armed but its clock restarts) is the line read from left to right. An executor that does not report a restart breaks it (EVT_005_mutant_silentRestart), and so does one that reports the fired transition, armed again after its own firing, as restarted (EVT_005_forbids_restartOnOwnFiring). Because the line asks for the fresh stamp and the cleared flag, it also rejects an update that reports the restart but keeps the old stamp (EVT_005_mutant_keepStamp: the update rule before 6.0.0 with the 6.0.0 event, or the restart branch without its stamp assignment, Rust bitmap_backend.rs 629, Java BitmapNetExecutor.java 1327, TypeScript bitmap-net-executor.ts 768) and one that leaves the restart flag set and so reports the restart again at a later update with no start in between (EVT_005_mutant_keepFlag: the scan without its trailing clear, Rust bitmap_backend.rs 636-639, Java BitmapNetExecutor.java 1334-1337, TypeScript bitmap-net-executor.ts 778-781). The line counts per name, so it needs the names of the net pairwise distinct (ruling D10; the markdown states the assumption, as in EVT-004)."
          "Line 2 is the fourth quoted sentence away from the update: no TransitionClockRestarted at the boot of a run or at any step but the update. An executor that reports the restart already at the start that takes the clock breaks it (EVT_005_mutant_eagerRestart), and so does one that reports a restart for the transitions the initial marking enables when the run boots (EVT_005_mutant_bootRestarted). Every runtime emits TransitionClockRestarted at its enablement update only (Rust executor_core/executor.rs 587-592, Java BitmapNetExecutor.java 1328 and PrecompiledNetExecutor.java 2054, TypeScript bitmap-net-executor.ts 770 and precompiled-net-executor.ts 820)."
          "Not fixed here: the order of the events inside one update (Rust reports every TransitionEnabled before every TransitionClockRestarted, executor_core/executor.rs 579-592; Java and TypeScript report each as they scan). That one update never reports both events for one name, and that every update that arms a transition afresh or restarts its pending clock reports exactly one of the two, follow from this block and EVT_004 together (evt005_one_of, cited for TIME-012 AC6 in its per-update form; the run-level count, each restart announced exactly once by a later update, is not stated). Assumptions shared by the executor event blocks: the event store is enabled (EVT-020) and its append does not fail; an event is a value (EVT-001)."
          "The test derivation is EVT_005_nonvacuous: in EVT-004's worked example the update after the refresh reports TransitionClockRestarted once for T, whose clock restart is pending, and none for r, armed again after its own start; and the boot reports none. Its second sentence (an executor that re-evaluates between the consumption and the deposit reports TransitionEnabled instead) is EVT_005_time012_ac6: with r's action asynchronous, the update between its start and its deposit turns T off, and the update after the deposit reports TransitionEnabled for T. As clash evt-a#2 notes, T must not be ready in the pass (the derivation says armed but not yet ready): a ready T that comes after the consuming transition fails the enablement recheck of the pass, loses its clock there and is reported with TransitionEnabled, which is the last clause of the derivation (EVT_005_nonvacuous_readyRecheck)."
  signoff "pending"
  statement : ∀ {N T : Type} [DecidableEq N], EvExec N T → Prop :=
    fun E => ∀ C,
      (NamesDistinct C.X → ∀ H evs n, on (fun s s' => E.step C H s .update evs s'), shall
        (fun s s' => namedCount .transitionClockRestarted n evs =
          if n ∈ C.X.net.transitions.map (·.core.name) ∧ pendingS (s.st n) = true ∧
              s'.st n = .armed s'.cyc false then 1 else 0)) ∧
      ((∀ M0, ∀ e ∈ E.boot C M0, e.kind ≠ .transitionClockRestarted) ∧
        ∀ H l evs, l ≠ .update → on (fun s s' => E.step C H s l evs s'), shall (fun _ _ =>
          ∀ e ∈ evs, e.kind ≠ .transitionClockRestarted))

/- The pinned readable form of EVT-005: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EVT_005 : {N T : Type} → [DecidableEq N] → EvExec N T → Prop :=
fun {N T} [DecidableEq N] E =>
  ∀ (C : Cfg N T),
    (NamesDistinct C.X →
        ∀ (H evs : List (NetEvent N T)) (n : String),
          on fun s s' => E.step C H s XLbl.update evs s', shall fun s s' =>
            namedCount NetEventKind.transitionClockRestarted n evs =
              if
                  n ∈ List.map (fun x => x.core.name) C.X.net.transitions ∧
                    pendingS (s.st n) = true ∧ s'.st n = Status.armed s'.cyc false then
                1
              else 0) ∧
      (∀ (M0 : QMarking N T), ∀ e ∈ E.boot C M0, e.kind ≠ NetEventKind.transitionClockRestarted) ∧
        ∀ (H : List (NetEvent N T)) (l : XLbl N T) (evs : List (NetEvent N T)),
          l ≠ XLbl.update →
            on fun s s' => E.step C H s l evs s', shall fun x x_1 =>
              ∀ e ∈ evs, e.kind ≠ NetEventKind.transitionClockRestarted
-/
#guard_msgs in #print EVT_005

/-! ## The two lines, one at a time -/

section Lines

variable {N T : Type} [DecidableEq N] [Ord N]
/-- Line 1 of `EVT_005` alone: an update reports exactly the transitions whose clock restart was
pending and whose clock it restarts, once each. -/
def evt005_line1 (E : EvExec N T) : Prop :=
  ∀ C, NamesDistinct C.X → ∀ H evs n, on (fun s s' => E.step C H s .update evs s'), shall
    (fun s s' => namedCount .transitionClockRestarted n evs =
      if n ∈ C.X.net.transitions.map (·.core.name) ∧ pendingS (s.st n) = true ∧
          s'.st n = .armed s'.cyc false then 1 else 0)

/-- Line 2 of `EVT_005` alone: nothing but an update emits a `TransitionClockRestarted` event,
neither the boot nor a step with another label. -/
def evt005_line2 (E : EvExec N T) : Prop :=
  ∀ C, (∀ M0, ∀ e ∈ E.boot C M0, e.kind ≠ .transitionClockRestarted) ∧
    ∀ H l evs, l ≠ .update → on (fun s s' => E.step C H s l evs s'), shall (fun _ _ =>
      ∀ e ∈ evs, e.kind ≠ .transitionClockRestarted)

omit [Ord N] in
/-- `EVT_005` is its two lines. -/
theorem evt005_iff (E : EvExec N T) : EVT_005 E ↔ evt005_line1 E ∧ evt005_line2 E :=
  ⟨fun h => ⟨fun C => (h C).1, fun C => (h C).2⟩, fun h C => ⟨h.1 C, h.2 C⟩⟩

end Lines

/-! ## The reference -/

section Reference

variable {N T : Type} [DecidableEq N] [Ord N]
omit [Ord N] in
/-- At an update that stamps a restarted transition afresh at the present reading (as the
reference does), a transition whose clock restart was pending is armed after the update exactly
when the update restarts its clock: armed at the update's reading, with no restart pending. -/
theorem updW_pending_iff {P : XPol N T} (hk : P.keepOnRestart = false)
    (hst : ∀ s, P.stampAt s = s.now) {C : Cfg N T} {s s' : XSt N T}
    (hx : xstepW P C s .update = some s') (n : String) :
    (pendingS (s.st n) = true ∧ isArmedS (s'.st n) = true) ↔
      (pendingS (s.st n) = true ∧ s'.st n = .armed s'.cyc false) := by
  obtain ⟨-, -, rfl⟩ := xstepW_update hx
  cases h : s.st n with
  | off => simp [pendingS]
  | reaped => simp [pendingS]
  | armed k r =>
    cases r with
    | false => simp [pendingS]
    | true =>
      simp only [pendingS, true_and, updSt, h]
      cases findT C n with
      | none => simp [isArmedS]
      | some u =>
        by_cases he : enabledNA (qCount s.M) u.core = true <;> simp [he, hk, hst, isArmedS]

/-- The `TransitionClockRestarted` events of an update of a step rule that stamps a restarted
transition afresh at the present reading, under the reference emission: one per net name whose
clock restart was pending and whose clock the update restarts. -/
theorem refEmitW_update_restartedW (P : EvPol) {Q : XPol N T} (hk : Q.keepOnRestart = false)
    (hst : ∀ s, Q.stampAt s = s.now) {C : Cfg N T} (hd : NamesDistinct C.X)
    (H : List (NetEvent N T)) {s s' : XSt N T} (hx : xstepW Q C s .update = some s')
    (n : String) :
    namedCount .transitionClockRestarted n (refEmitW P C H s .update s') =
      if n ∈ C.X.net.transitions.map (·.core.name) ∧ pendingS (s.st n) = true ∧
          s'.st n = .armed s'.cyc false then 1 else 0 := by
  simp only [refEmitW, netNames]
  rw [namedCount_append, namedCount_eq_zero (k := .transitionClockRestarted),
    namedCount_filterMap (mk := NetEvent.transitionClockRestarted) (fun _ => rfl) (fun _ => rfl)
      (fun m => pendingS (s.st m) && isArmedS (s'.st m)) n _ hd, Nat.zero_add]
  · have := updW_pending_iff hk hst hx n
    simp only [Bool.and_eq_true]
    by_cases hm : n ∈ C.X.net.transitions.map (·.core.name)
    · by_cases hc : pendingS (s.st n) = true ∧ isArmedS (s'.st n) = true
      · rw [if_pos ⟨hm, hc⟩, if_pos ⟨hm, this.1 hc⟩]
      · rw [if_neg (fun h => hc h.2), if_neg (fun h => hc (this.2 h.2))]
    · rw [if_neg (fun h => hm h.1), if_neg (fun h => hm h.1)]
  · intro e he
    simp only [List.mem_filterMap] at he
    obtain ⟨m, -, hm⟩ := he
    split at hm
    · cases hm; simp [NetEvent.kind]
    · cases hm

/-- The `TransitionClockRestarted` events of a reference update: one per net name whose clock
restart was pending and whose clock the update restarts. -/
theorem refEmitW_update_restarted (P : EvPol) {C : Cfg N T} (hd : NamesDistinct C.X)
    (H : List (NetEvent N T)) {s s' : XSt N T} (hx : xstep C s .update = some s') (n : String) :
    namedCount .transitionClockRestarted n (refEmitW P C H s .update s') =
      if n ∈ C.X.net.transitions.map (·.core.name) ∧ pendingS (s.st n) = true ∧
          s'.st n = .armed s'.cyc false then 1 else 0 :=
  refEmitW_update_restartedW P (Q := refXPol) rfl (fun _ => rfl) hd H hx n

/-- No step of the reference but an update emits `TransitionClockRestarted`. -/
theorem refEmitW_noRestarted (P : EvPol) (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T)
    {l : XLbl N T} (hl : l ≠ .update) (s' : XSt N T) :
    ∀ e ∈ refEmitW P C H s l s', e.kind ≠ .transitionClockRestarted := by
  intro e he hk
  have := refEmitW_kind P C H s l s' e he
  rw [hk] at this
  cases l with
  | update => exact hl rfl
  | _ => simp [lblKinds] at this

/-- The reference boot emits no `TransitionClockRestarted`. -/
theorem refBoot_noRestarted (P : EvPol) (C : Cfg N T) (M0 : QMarking N T) :
    ∀ e ∈ refBoot P C M0, e.kind ≠ .transitionClockRestarted := by
  intro e he hk
  rcases refBoot_kind P C M0 e he with h | h <;> rw [hk] at h <;> cases h

/-- Line 1 holds of every executor that steps as the reference and emits as the reference at an
update, whatever it emits elsewhere and whatever its boot. -/
theorem evt005_line1_of_refUpdate (P : EvPol)
    {boot : Cfg N T → QMarking N T → List (NetEvent N T)}
    {emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    (he : ∀ C H s s', emit C H s .update s' = refEmitW P C H s .update s') :
    evt005_line1 (emitExec boot emit) := by
  intro C hd H evs n s s' hs
  obtain ⟨hx, rfl⟩ := hs
  rw [he]
  exact refEmitW_update_restarted P hd H hx n

/-- Line 2 holds of every executor whose boot is the reference's and whose steps other than the
update emit as the reference. -/
theorem evt005_line2_of_refOff
    {emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T)}
    (P : EvPol) (he : ∀ C H s l s', l ≠ .update → emit C H s l s' = refEmitW P C H s l s') :
    evt005_line2 (emitExec (refBoot P) emit) := by
  intro C
  refine ⟨refBoot_noRestarted P C, fun H l evs hl s s' hs => ?_⟩
  obtain ⟨-, rfl⟩ := hs
  rw [he C H s l s' hl]
  exact refEmitW_noRestarted P C H s hl s'

/-- The reference meets EVT-005 under every emission variant. -/
theorem evt005_ref (P : EvPol) : EVT_005 (refEvExec (N := N) (T := T) P) :=
  (evt005_iff _).2 ⟨evt005_line1_of_refUpdate P fun _ _ _ _ => rfl,
    evt005_line2_of_refOff P fun _ _ _ _ _ _ => rfl⟩

/-- ✓ The reference executor with the Java and TypeScript emission meets EVT-005: each update
reports, once, every transition whose clock restart was pending and that it leaves armed, and
nothing else reports `TransitionClockRestarted`. -/
@[evidence holds EVT_005]
theorem EVT_005_reference : EVT_005 (refEvExec (N := N) (T := T) polJT) := evt005_ref polJT

/-- ✓ The reference executor with the Rust and Python emission meets EVT-005 too: the block is a
line for every executor. -/
@[evidence holds EVT_005]
theorem EVT_005_rust : EVT_005 (refEvExec (N := N) (T := T) polRust) := evt005_ref polRust

end Reference

/-! ## With EVT-004: exactly one of the two events per arming ([TIME-012] AC6) -/

/-- **Each arming is reported by exactly one of the two events** ([TIME-012] AC6, per update):
for an executor that meets EVT-004 and EVT-005, an update reports a transition of the net by one
`TransitionEnabled` or one `TransitionClockRestarted`, never both: the first when the transition
was not armed before the update and is armed after it, the second when its clock restart was
pending and the update restarts its clock. A transition that stays armed with its clock gets
neither. For example, in EVT-004's worked example the update after the refresh reports `r`
(armed again after its own start) by `TransitionEnabled` only and `T` (restart pending, stamped
afresh) by `TransitionClockRestarted` only. -/
@[evidence cites "TIME-012" "AC6 at the enablement update that arms the transition again: each restart emits exactly one of TransitionClockRestarted or TransitionEnabled, the first when the restart is still pending at the update, the second when the executor disarmed the transition before it; and AC4's event clause, a transition that keeps its clock gets neither"]
theorem evt005_one_of {N T : Type} [DecidableEq N] [Ord N] {E : EvExec N T} (h4 : EVT_004 E)
    (h5 : EVT_005 E) {C : Cfg N T} (hd : NamesDistinct C.X) (H : List (NetEvent N T))
    {s s' : XSt N T} {evs : List (NetEvent N T)} (hs : E.step C H s .update evs s')
    (n : String) :
    namedCount .transitionEnabled n evs + namedCount .transitionClockRestarted n evs =
      if n ∈ C.X.net.transitions.map (·.core.name) ∧
          ((isArmedS (s.st n) = false ∧ isArmedS (s'.st n) = true) ∨
            (pendingS (s.st n) = true ∧ s'.st n = .armed s'.cyc false)) then 1 else 0 := by
  rw [(h4 C).1 hd H evs n s s' hs, (h5 C).1 hd H evs n s s' hs]
  by_cases hm : n ∈ C.X.net.transitions.map (·.core.name)
  · cases s.st n with
    | off => by_cases ha : isArmedS (s'.st n) = true <;> simp_all [isArmedS, pendingS]
    | reaped => by_cases ha : isArmedS (s'.st n) = true <;> simp_all [isArmedS, pendingS]
    | armed k b =>
      cases b <;> by_cases hr : s'.st n = .armed s'.cyc false <;> simp_all [isArmedS, pendingS]
  · simp [hm]

/-! ## The worked example (EVT-004's configuration) -/

/-- ✓ Both lines of EVT-005 are exercised by the reference: at the second update of EVT-004's
example `T`, whose clock restart the refresh's start made pending, is stamped afresh and
reported with one `TransitionClockRestarted`, while `r`, armed again after its own start, gets
none; and the boot emits events, none a `TransitionClockRestarted`. -/
@[evidence nonvacuous EVT_005]
theorem EVT_005_nonvacuous :
    (∃ s s' evs, (refEvExec polJT).step evt004_cfg [] s .update evs s' ∧
      namedCount .transitionClockRestarted "T" evs = 1 ∧ s.st "T" = .armed 0 true ∧
      s'.st "T" = .armed 1 false ∧
      namedCount .transitionClockRestarted "r" evs = 0 ∧ isArmedS (s'.st "r") = true) ∧
    ((refEvExec (N := Nat) (T := Nat) polJT).boot evt004_cfg evt004_m1 ≠ [] ∧
      ∀ e ∈ (refEvExec (N := Nat) (T := Nat) polJT).boot evt004_cfg evt004_m1,
        e.kind ≠ .transitionClockRestarted) := by
  refine ⟨?_, by decide +kernel⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt004_cfg)
    (o := evt004_beforeUpdate evt004_m1) (l := .update)
    (p := fun s s' =>
      let evs := refEmitW polJT evt004_cfg [] s .update s'
      namedCount .transitionClockRestarted "T" evs == 1 && s.st "T" == .armed 0 true &&
        s'.st "T" == .armed 1 false && namedCount .transitionClockRestarted "r" evs == 0 &&
        isArmedS (s'.st "r"))
    (by decide +kernel)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hp
  exact ⟨s, s', _, ⟨hs, rfl⟩, h1, h2, h3, h4, h5⟩

/-- The run of the observed gap: as EVT-004's run, but `r`'s action is asynchronous; the next
cycle's update comes before its action writes 9 into place 0 and returns, its completion is
settled while the loop waits, and the cycle after that ends with its update. -/
def evt005_gapRun : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin,
   .start "r" false, .endPass,
   .endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin, .endPass,
   .write 0 0 9, .ret 0 true, .commit 0,
   .endCompletions, .endPublications, .endEvents, .delay 1, .update]

/-- ✓ [TIME-012] AC6 on two whole runs: each restart of `T` is reported by exactly one event.
In EVT-004's run (synchronous refresh) the update after the refresh reports
`TransitionClockRestarted` for `T`. When the refresh's action is asynchronous, the update between
its start and its deposit finds `T` disabled and turns it off, so the update after the deposit
reports `TransitionEnabled` for `T` instead (the executor observed the gap). These are the Rust
and Python traces; Java and TypeScript add the snapshot of the initial marking after
`ExecutionStarted`. -/
@[evidence cites "TIME-012" "AC6: each restart emits exactly one of TransitionClockRestarted or TransitionEnabled; on the run of the AC1 refill with a synchronous action the restart is a TransitionClockRestarted, and with an asynchronous action whose deposit comes after the next enablement update it is a TransitionEnabled (AC5, the gap the executor observed)"]
theorem EVT_005_time012_ac6 :
    refTrace polRust evt004_cfg evt004_m1 0 (evt004_run ++ [.update]) =
      some [.executionStarted, .transitionEnabled "T", .transitionEnabled "r",
        .tokenRemoved 0 1, .transitionStarted "r" [(0, 1)],
        .tokenAdded 0 9, .transitionCompleted "r" [(0, 9)] 0,
        .transitionEnabled "r", .transitionClockRestarted "T"] ∧
    refTrace polRust evt004_cfg evt004_m1 0 evt005_gapRun =
      some [.executionStarted, .transitionEnabled "T", .transitionEnabled "r",
        .tokenRemoved 0 1, .transitionStarted "r" [(0, 1)],
        .tokenAdded 0 9, .transitionCompleted "r" [(0, 9)] 0,
        .transitionEnabled "T", .transitionEnabled "r"] := by
  decide +kernel

/-- ✓ [TIME-012] AC4 (surplus keeps): with two tokens in place 0 the refresh takes one and its
action puts one back, `T` stays enabled in the intermediate marking and keeps its stamp 0, and the
update after the refresh reports neither `TransitionEnabled` nor `TransitionClockRestarted` for
`T`. -/
@[evidence cites "TIME-012" "AC4: T's clock continues, and neither TransitionClockRestarted nor TransitionEnabled is emitted for T after the refresh"]
theorem EVT_005_time012_ac4 :
    ∃ s s' evs, (refEvExec polJT).step evt004_cfg [] s .update evs s' ∧
      s.st "T" = .armed 0 false ∧ s'.st "T" = .armed 0 false ∧
      namedCount .transitionEnabled "T" evs = 0 ∧
      namedCount .transitionClockRestarted "T" evs = 0 := by
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt004_cfg)
    (o := evt004_beforeUpdate evt004_m2) (l := .update)
    (p := fun s s' =>
      let evs := refEmitW polJT evt004_cfg [] s .update s'
      s.st "T" == .armed 0 false && s'.st "T" == .armed 0 false &&
        namedCount .transitionEnabled "T" evs == 0 &&
        namedCount .transitionClockRestarted "T" evs == 0)
    (by decide +kernel)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hp
  exact ⟨s, s', _, ⟨hs, rfl⟩, h1, h2, h3, h4⟩

/-- The configuration of the ready recheck: EVT-004's places and transitions with `r` first and
both transitions immediate, so both are ready in the first pass and `r` comes first. -/
def evt005_readyCfg : Cfg Nat Nat :=
  { evt004_cfg with
    X := { net := { places := [0, 1], transitions := [evt004_tR, evt004_tT] },
           timing := fun _ => .immediate, tol := 0 } }

/-- The run of the ready recheck: `r` starts synchronously, its action writes 9 into place 0 and
returns, and its completion is settled in the pass; the pass then rechecks `T`, which fails
because the deposit made inside the pass is not visible to it, so `T` loses its clock; the next
cycle, one millisecond later, ends with its update. -/
def evt005_readyRun : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin,
   .start "r" true, .write 0 0 9, .ret 0 true, .commit 0, .lose "T", .endPass,
   .endCompletions, .endPublications, .endEvents, .delay 1]

/-- ✓ A ready transition that loses its clock in the pass is announced with `TransitionEnabled`,
not `TransitionClockRestarted`: `T` and `r` are both immediate and share place 0's only token,
and `r` comes first. `r` starts, which makes `T`'s clock restart pending, and its action puts a
token back at once. The pass then rechecks `T`: the deposit made inside the pass is not visible to
it, so `T` is disarmed. At the next update `T` is off before and armed after, and the update
reports one `TransitionEnabled` and no `TransitionClockRestarted` for it. -/
@[evidence nonvacuous EVT_005]
theorem EVT_005_nonvacuous_readyRecheck :
    ∃ s s' evs, (refEvExec polJT).step evt005_readyCfg [] s .update evs s' ∧
      s.st "T" = .off ∧ s'.st "T" = .armed 1 false ∧
      namedCount .transitionEnabled "T" evs = 1 ∧
      namedCount .transitionClockRestarted "T" evs = 0 := by
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt005_readyCfg)
    (o := xrun evt005_readyCfg (xinit evt004_m1 0) evt005_readyRun) (l := .update)
    (p := fun s s' =>
      let evs := refEmitW polJT evt005_readyCfg [] s .update s'
      s.st "T" == .off && s'.st "T" == .armed 1 false &&
        namedCount .transitionEnabled "T" evs == 1 &&
        namedCount .transitionClockRestarted "T" evs == 0)
    (by decide +kernel)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hp
  exact ⟨s, s', _, ⟨hs, rfl⟩, h1, h2, h3, h4⟩

/-! ## Wrong executors: the reference's steps, another emission -/

section Mutants

variable {N T : Type} [DecidableEq N] [Ord N]
/-- The update events without the `TransitionClockRestarted` ones. -/
def evt005_silentRestartEvs (C : Cfg N T) (H : List (NetEvent N T)) (s s' : XSt N T) :
    List (NetEvent N T) :=
  (refEmitW polJT C H s .update s').filter fun e => e.kind != .transitionClockRestarted

/-- The executor that restarts the clock but does not report it. -/
def evt005_silentRestart : EvExec N T :=
  emitExec (refBoot polJT) (evt004_atUpdate evt005_silentRestartEvs)

/-- The update events with a re-armed transition that has started before in the run (history
`H`) reported as restarted rather than enabled. -/
def evt005_ownFiringEvs (C : Cfg N T) (H : List (NetEvent N T)) (s s' : XSt N T) :
    List (NetEvent N T) :=
  (refEmitW polJT C H s .update s').map fun e =>
    match e with
    | .transitionEnabled n =>
      if H.any (fun h => h.kind == .transitionStarted && h.trans? == some n)
      then .transitionClockRestarted n else e
    | _ => e

/-- The executor that reports a transition armed again after its own firing as restarted. -/
def evt005_ownFiring : EvExec N T :=
  emitExec (refBoot polJT) (evt004_atUpdate evt005_ownFiringEvs)

/-- The Java and TypeScript emission, with a start also reporting `TransitionClockRestarted` for
every transition whose clock restart it makes pending. -/
def evt005_eagerEmit (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T) (l : XLbl N T)
    (s' : XSt N T) : List (NetEvent N T) :=
  match l with
  | .start .. => refEmitW polJT C H s l s' ++ (netNames C).filterMap fun n =>
      if !pendingS (s.st n) && pendingS (s'.st n) then some (.transitionClockRestarted n)
      else none
  | _ => refEmitW polJT C H s l s'

/-- The executor that reports a restart already at the start that takes the clock. -/
def evt005_eagerRestart : EvExec N T := emitExec (refBoot polJT) evt005_eagerEmit

/-- An executor that changes only what an update emits keeps line 2 of EVT-005. -/
theorem evt005_atUpdate_line2
    (f : Cfg N T → List (NetEvent N T) → XSt N T → XSt N T → List (NetEvent N T)) :
    evt005_line2 (emitExec (refBoot polJT) (evt004_atUpdate f)) :=
  evt005_line2_of_refOff polJT fun C H s _ s' hl => evt004_atUpdate_other f C H s hl s'

end Mutants

/-- ✗ Restarting the clock without reporting it violates EVT-005 (line 1): at the second update
of EVT-004's example `T`'s clock restart is pending and the update stamps it afresh, and this
executor reports nothing for `T`. The executor keeps line 2. -/
@[evidence mutant EVT_005]
theorem EVT_005_mutant_silentRestart :
    evt005_line2 (evt005_silentRestart (N := Nat) (T := Nat)) ∧
      ¬ EVT_005 (evt005_silentRestart (N := Nat) (T := Nat)) := by
  refine ⟨evt005_atUpdate_line2 _, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt004_cfg)
    (o := evt004_beforeUpdate evt004_m1) (l := .update)
    (p := fun s s' => decide (namedCount .transitionClockRestarted "T"
        (evt005_silentRestartEvs evt004_cfg [] s s') ≠
      if "T" ∈ evt004_cfg.X.net.transitions.map (·.core.name) ∧ pendingS (s.st "T") = true ∧
          s'.st "T" = .armed s'.cyc false then 1 else 0))
    (by decide +kernel)
  exact of_decide_eq_true hp ((h evt004_cfg).1 evt004_cfg_distinct [] _ "T" s s' ⟨hs, rfl⟩)

/-- ✗ Reporting a transition armed again after its own firing as restarted violates EVT-005
(line 1): at the second update of EVT-004's example `r`, which started before and lost its clock
at its own start, is reported with `TransitionClockRestarted`, but its clock restart was not
pending. -/
@[evidence forbids EVT_005]
theorem EVT_005_forbids_restartOnOwnFiring :
    ¬ EVT_005 (evt005_ownFiring (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt004_cfg)
    (o := evt004_beforeUpdate evt004_m1) (l := .update)
    (p := fun s s' => decide (namedCount .transitionClockRestarted "r"
        (evt005_ownFiringEvs evt004_cfg evt004_hist s s') ≠
      if "r" ∈ evt004_cfg.X.net.transitions.map (·.core.name) ∧ pendingS (s.st "r") = true ∧
          s'.st "r" = .armed s'.cyc false then 1 else 0))
    (by decide +kernel)
  exact of_decide_eq_true hp
    ((h evt004_cfg).1 evt004_cfg_distinct evt004_hist _ "r" s s' ⟨hs, rfl⟩)

/-- ✗ Reporting a restart already at the start that takes the clock violates EVT-005 (line 2):
in EVT-004's example the refresh's start takes `T`'s only token, `T`'s clock restart becomes
pending, and this executor reports `TransitionClockRestarted` for `T` at that start. Its updates
report as the reference, so it keeps line 1. -/
@[evidence mutant EVT_005]
theorem EVT_005_mutant_eagerRestart :
    evt005_line1 (evt005_eagerRestart (N := Nat) (T := Nat)) ∧
      ¬ EVT_005 (evt005_eagerRestart (N := Nat) (T := Nat)) := by
  refine ⟨evt005_line1_of_refUpdate polJT fun _ _ _ _ => rfl, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := evt004_cfg)
    (o := xrun evt004_cfg (xinit evt004_m1 0) (evt004_run.take 6)) (l := .start "r" true)
    (p := fun s s' => (evt005_eagerEmit evt004_cfg [] s (.start "r" true) s').any
      fun e => e.kind == .transitionClockRestarted)
    (by decide +kernel)
  simp only [List.any_eq_true, beq_iff_eq] at hp
  obtain ⟨e, he, hk⟩ := hp
  exact (h evt004_cfg).2.2 [] (.start "r" true) _ (by simp) s s' ⟨hs, rfl⟩ e he hk

/-- The Java and TypeScript boot events followed by one `TransitionClockRestarted` for each
transition the initial marking enables. -/
def evt005_bootRestartedEvs {N T : Type} [DecidableEq N] [Ord N] (C : Cfg N T) (M0 : QMarking N T) :
    List (NetEvent N T) :=
  refBoot polJT C M0 ++ (C.X.net.transitions.filter fun u => enabledNA (qCount M0) u.core).map
    fun u => .transitionClockRestarted u.core.name

/-- The executor that steps and emits as the reference but reports a clock restart for the
transitions the initial marking enables when the run boots. -/
def evt005_bootRestarted {N T : Type} [DecidableEq N] [Ord N] : EvExec N T :=
  emitExec evt005_bootRestartedEvs (refEmitW polJT)

/-- ✗ Reporting a clock restart when the run boots violates EVT-005 (line 2): the boot of
EVT-004's example reports `TransitionClockRestarted` for `T`, although no clock has run yet. Every
step of this executor emits as the reference, so it keeps line 1. -/
@[evidence mutant EVT_005]
theorem EVT_005_mutant_bootRestarted :
    evt005_line1 (evt005_bootRestarted (N := Nat) (T := Nat)) ∧
      ¬ EVT_005 (evt005_bootRestarted (N := Nat) (T := Nat)) := by
  refine ⟨evt005_line1_of_refUpdate polJT fun _ _ _ _ => rfl, fun h => ?_⟩
  have hm : NetEvent.transitionClockRestarted "T" ∈
      evt005_bootRestarted.boot evt004_cfg evt004_m1 := by decide +kernel
  exact (h evt004_cfg).2.1 evt004_m1 _ hm rfl

/-! ## Wrong steps: the fresh stamp, and what the block leaves to [TIME-012] -/

section StepExec

variable {N T : Type} [DecidableEq N] [Ord N]
/-- Every executor that emits as the reference keeps line 2 of EVT-005, whatever its steps. -/
theorem evt005_line2_stepExec (g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)) :
    evt005_line2 (evtStepExec g) := by
  intro C
  refine ⟨refBoot_noRestarted polJT C, fun H l evs hl s s' hs => ?_⟩
  obtain ⟨-, rfl⟩ := hs
  exact refEmitW_noRestarted polJT C H s hl s'

/-- Every executor that emits as the reference and whose update stamps a restarted transition
afresh at the present reading meets EVT-005, whatever its other steps do to the clock status. -/
theorem evt005_stepExec {P : XPol N T} (hk : P.keepOnRestart = false)
    (hst : ∀ s, P.stampAt s = s.now) (g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T))
    (hg : ∀ C s, g C s .update = xstepW P C s .update) : EVT_005 (evtStepExec g) := by
  intro C
  refine ⟨fun hd H evs n s s' hs => ?_, (evt005_line2_stepExec g C)⟩
  obtain ⟨hx, rfl⟩ := hs
  rw [hg] at hx
  exact refEmitW_update_restartedW polJT hk hst hd H hx n

/-- The reference rules, except that the update keeps the old stamp of a transition whose clock
restart was pending (the update rule before 6.0.0). -/
def evt005_keepStampPol : XPol N T := { refXPol with keepOnRestart := true }

/-- The reference step, except that the update leaves the restart flag set on a transition whose
clock restart was pending and that it stamps afresh. -/
def evt005_keepFlagStep (C : Cfg N T) (s : XSt N T) (l : XLbl N T) : Option (XSt N T) :=
  match l with
  | .update => (xstep C s .update).map fun s' =>
      { s' with st := fun n => match s.st n, s'.st n with
          | .armed _ true, .armed k _ => .armed k true
          | _, x => x }
  | l => xstep C s l

/-- The reference rules, except that a start judges the restart flag on the marking before its
own consumption, so it never flags a restart. -/
def evt005_neverFlagPol : XPol N T := { refXPol with restartOn := fun s _ => s.M }

end StepExec

/-- ✗ Reporting a clock restart while keeping the old stamp violates EVT-005 (line 1): at the
second update of EVT-004's example `T`'s clock restart is pending, this executor reports
`TransitionClockRestarted` for `T` but leaves its stamp at 0 instead of the update's reading 1,
so its clock did not restart. It emits as the reference everywhere else, so it keeps line 2. -/
@[evidence mutant EVT_005]
theorem EVT_005_mutant_keepStamp :
    evt005_line2 (evtStepExec (N := Nat) (T := Nat) (xstepW evt005_keepStampPol)) ∧
      ¬ EVT_005 (evtStepExec (N := Nat) (T := Nat) (xstepW evt005_keepStampPol)) := by
  refine ⟨evt005_line2_stepExec _, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check (xstepW evt005_keepStampPol) (C := evt004_cfg)
    (o := evtRunWith (xstepW evt005_keepStampPol) evt004_cfg (xinit evt004_m1 0) evt004_run)
    (l := .update)
    (p := fun s s' => decide (namedCount .transitionClockRestarted "T"
        (refEmitW polJT evt004_cfg [] s .update s') ≠
      if "T" ∈ evt004_cfg.X.net.transitions.map (·.core.name) ∧ pendingS (s.st "T") = true ∧
          s'.st "T" = .armed s'.cyc false then 1 else 0))
    (by decide +kernel)
  exact of_decide_eq_true hp ((h evt004_cfg).1 evt004_cfg_distinct [] _ "T" s s' ⟨hs, rfl⟩)

/-- ✗ Leaving the restart flag set at the update violates EVT-005 (line 1): at the second update
of EVT-004's example this executor stamps `T` afresh and reports `TransitionClockRestarted`, but
`T`'s restart is still pending by its own state, so the next update would report the restart again
with no start in between. It emits as the reference everywhere else, so it keeps line 2. -/
@[evidence mutant EVT_005]
theorem EVT_005_mutant_keepFlag :
    evt005_line2 (evtStepExec (N := Nat) (T := Nat) evt005_keepFlagStep) ∧
      ¬ EVT_005 (evtStepExec (N := Nat) (T := Nat) evt005_keepFlagStep) := by
  refine ⟨evt005_line2_stepExec _, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check evt005_keepFlagStep (C := evt004_cfg)
    (o := evtRunWith evt005_keepFlagStep evt004_cfg (xinit evt004_m1 0) evt004_run)
    (l := .update)
    (p := fun s s' => decide (namedCount .transitionClockRestarted "T"
        (refEmitW polJT evt004_cfg [] s .update s') ≠
      if "T" ∈ evt004_cfg.X.net.transitions.map (·.core.name) ∧ pendingS (s.st "T") = true ∧
          s'.st "T" = .armed s'.cyc false then 1 else 0))
    (by decide +kernel)
  exact of_decide_eq_true hp ((h evt004_cfg).1 evt004_cfg_distinct [] _ "T" s s' ⟨hs, rfl⟩)

/-- ✓ EVT-005 alone allows an executor that never flags a clock restart: in EVT-004's example the
refresh `r` takes `T`'s only token, but this executor checks `T` against the marking before that
consumption, so `T` keeps its old stamp 0, and the next update reports neither event for `T`.
When a start makes a restart pending is [TIME-012]'s: its companion line on the cycle (a start
flags every other armed transition its intermediate marking disables) rejects the steps of this
executor, so only the two requirements together, on the same executor, rule it out. -/
@[evidence allows EVT_005]
theorem EVT_005_allows_neverFlags :
    EVT_005 (evtStepExec (N := Nat) (T := Nat) (xstepW evt005_neverFlagPol)) ∧
      (∃ s s' evs, (evtStepExec (xstepW evt005_neverFlagPol)).step evt004_cfg [] s .update
          evs s' ∧ s'.st "T" = .armed 0 false ∧
          namedCount .transitionClockRestarted "T" evs = 0 ∧
          namedCount .transitionEnabled "T" evs = 0) ∧
      ¬ TIME_012_cycle (evtStepExec (N := Nat) (T := Nat) (xstepW evt005_neverFlagPol)).erase := by
  refine ⟨evt005_stepExec rfl (fun _ => rfl) _ fun _ _ => rfl, ?_, fun h => ?_⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check (xstepW evt005_neverFlagPol) (C := evt004_cfg)
      (o := evtRunWith (xstepW evt005_neverFlagPol) evt004_cfg (xinit evt004_m1 0) evt004_run)
      (l := .update)
      (p := fun s s' =>
        let evs := refEmitW polJT evt004_cfg [] s .update s'
        s'.st "T" == .armed 0 false && namedCount .transitionClockRestarted "T" evs == 0 &&
          namedCount .transitionEnabled "T" evs == 0)
      (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    exact ⟨s, s', _, ⟨hs, rfl⟩, h1, h2, h3⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check (xstepW evt005_neverFlagPol) (C := evt004_cfg)
      (o := evtRunWith (xstepW evt005_neverFlagPol) evt004_cfg (xinit evt004_m1 0)
        (evt004_run.take 6))
      (l := .start "r" true)
      (p := fun s s' => match s.order with
        | t :: _ => s.st "T" == .armed 0 false &&
            !enabledNA (qCount (liveAfter s t)) evt004_tT.core && s'.st "T" == .armed 0 false
        | [] => false)
      (by decide +kernel)
    cases ho : s.order with
    | nil => simp [ho] at hp
    | cons t rest =>
      simp only [ho, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hp
      obtain ⟨⟨h1, h2⟩, h3⟩ := hp
      have := (h evt004_cfg).1 "r" true t rest "T" evt004_tT 0 false (by decide) rfl s s'
        ⟨[], _, hs, rfl⟩ ho h1
      rw [h3, h2] at this
      simp at this

end Libpetri.Spec
