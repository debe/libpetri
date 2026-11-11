import Libpetri.Reference.Exec
import Libpetri.Reference.Link
import Libpetri.Novel.InFlight
import Libpetri.Novel.ReapAware
import Libpetri.Novel.TerminalRewrite
import Libpetri.Novel.EnvSemantics.Step

set_option linter.missingDocs true

/-!
# Links from the reference executor to the Phase 1 models (`ExecLink`)

The reference executor (`RefExec`, `Reference/Exec.lean`) splits a firing into a start inside a
firing pass and a settle in a later step. The Phase 1 models fire atomically: `RefQFire`
(`Reference/Queue.lean`) on queue markings, `RefTStep` (`Reference/Timed.lean`) with the firing
clock. This file proves that the executor is the same model seen at a finer grain (design
refexec-final, section 3, links L1, L2, L3, L7, L9, L10 and L11):

* **L1, the marking frame** (`xstepW_M_frame`, `xstepW_M_cases`): only `start`, `commit`,
  `tdeposit`, `publish` and `inject` change the marking; a start replaces it by `liveAfter`, the
  others append at the tails.
* **L2, the queue firing** (`segment_refQFire`, `refQFire_realised`): a start from a pass state
  with no same-pass deposit, followed by steps that leave the marking alone, followed by the
  commit of that firing, is a `RefQFire` step of the started transition from the marking of the
  start, with the delivered tokens the firing recorded and the committed emission, provided the
  emission is one the output spec offers (`OfferedEmission`, a per-run hypothesis: validation
  reads sets of places, so a validated emission can carry more tokens than any offered deposit,
  and those runs are [IO-016]'s subject, not `RefQFire`'s). Conversely every `RefQFire` step of
  the head of a pass order is realised by a synchronous start, its writes, its return and its
  inline commit.
* **L3, the timed step** (`atomic_refTStep`, `deadline_reaps`, `delay_view`): from a state at the
  termination test with no firing in flight, no restart flag pending and the cycle reading equal
  to the present, a pass with one synchronous start and its inline commit, then the next update
  with no delay in between, is one `RefTStep` firing of the clock view (`viewAt s s.cyc`). The
  stamp arithmetic is `status_agrees` (the refexec-final spike), which needs two premises at the
  test state: no restart flag, and `InvU` (an off name not in flight is not enabled). A deadline
  step is a sequence of `RefTStep` reaps, and a delay is a `RefTStep` delay.
* **L7, no refresh rescue** (`no_start_while_expired`): in every reachable state where a start
  happens, no transition of the net is expired at the cycle reading. The deadline step reaps the
  full expired set at that reading, and nothing in the termination test or the pass gives a name
  an older stamp.
* **L9, the dirty set** (`updSt_eq_updDirty`, `cleanAt_of_frame`, `lose_written`): the update
  re-evaluates every name, the runtimes only the dirty ones. The two agree: the update leaves
  every clean name as it is, and a name stays clean from a phase boundary as long as its status,
  the counts of its arc places and whether it is in flight are unchanged. A loser of the pass
  recheck had an arc place written (the consumption that disabled it), so it is dirty even though
  Rust's `disable` writes nothing.
* **L10, reaped** (`reapedE_iff_reaped`): at a phase boundary the executor's reaped status is
  the Phase 1 term Reaped of the clock view, for a name that is not in flight or under a
  re-entrant executor.
* **L11, the initial state** (`init_update_eq_TSt_init`): the first update from `xinit M0 r0`
  gives the clock view `TSt.init`, the initial state of the timed reference step.

The agreement conjuncts of the consistency theorem are `QueueAgrees E Q` and `AtomicAgrees E R`
(over an abstract executor and its label runs, `XRunL`); `queueAgrees_ref` and
`atomicAgrees_ref` prove them of `RefExec` with `RefQFire` and `RefTStep`. A link that needs the
build-time well-formedness takes `C.WF`, or the part of it it uses (the distinct names of ruling
D10), as a premise, never as part of the executor (design R13); L1 and L2 need none.
`atomic_nonvacuous` decides a run from an initial state on which the L3 premises hold.

The second half of the file reads the executor on flat place identities (`N = PlaceId`), where
the verifier's models live, and proves three more links (design refexec-final, section 3, links
L5, L6 and L8):

* **L5, the count projection** (`count_projection`, `hoist_vis`, `rest_split`): the counts of
  every state a run reaches are a marking of `InFlight.XStep` (the executor of the verifier's
  split argument, gated by the strict stop) with exactly the firings in flight pending. A
  synchronous firing settled inside its pass is moved behind the pass's last start (`Hoist`); the
  pass-visible marking is then the live marking of the moved run, as if every firing of the pass
  started before any deposited ([EXEC-003]). A fail is a completion with the empty row (clash
  28). The rows a run uses are a per-run hypothesis (`RowsCover`), as `OfferedEmission` is for L2;
  a publication and an injection are outside it. Where nothing is in flight,
  `InFlight.split_rest_sound` applies. The agreement conjunct is `CountAgrees E`.
* **L8, environment injection** (`inject_injC`, `inject_stepStopInj`, `aRun_reachStopInj`): an
  injection is `EnvSemantics.injC`, a token appended at the tail of an environment place; on atomic
  runs (`ARun`: injections, steps that leave the marking alone, and atomic segments, a start and
  its commit with nothing that changes the marking in between, enabled on the live marking) the
  counts are a run of `TerminalRewrite.StepStopInjRel`, so the verified net's injected relation
  reaches them (`aRun_verified`).
* **L6, rests** (`atomic_rest_sound`, `atomic_restsAt`): with no environment place, the marking of
  every rest of an atomic run is untimed-reachable and reap-quiescent, and under valid timings it
  is a rest of `ReapAware`'s cycle model, so `rest_sound` and `reap_aware_ac3` apply. The
  restriction to live-consistent starts is needed: `corrected2_witness` decides a run whose
  pass-visible recheck fires two transitions into each other's inhibitor places and rests where no
  atomic order goes (exec map CORRECTED 2).

**Deferred:** L3' (the gap lemma `atomic_gap_nonreapable`, a delay between the start and the
update), and a cell-by-cell projection of the executor's cycles onto `ReapAware.Cycle` (L6 is
proved at the level of rests).
-/

namespace Libpetri.Reference

open Libpetri Libpetri.Spec Libpetri.Novel.Seam

variable {N T : Type} [DecidableEq N]

/-! ## Label runs -/

/-- A run of labels of an abstract executor `E` from `s` to `s'`: each label is a step of `E`
from the state the previous one reached. The agreement conjuncts quantify over it, so a mutant
executor is checked on the same segments as the reference. -/
def XRunL (E : XRel N T) (C : Cfg N T) : XSt N T → List (XLbl N T) → XSt N T → Prop
  | s, [], s' => s' = s
  | s, l :: ls, s' => ∃ s1, E C s l s1 ∧ XRunL E C s1 ls s'

omit [DecidableEq N] in
/-- A label run through the first `ls₁` labels, then the rest. -/
theorem xrunL_append {E : XRel N T} {C : Cfg N T} :
    ∀ {s s' : XSt N T} {ls₁ ls₂ : List (XLbl N T)},
      XRunL E C s (ls₁ ++ ls₂) s' ↔ ∃ s₁, XRunL E C s ls₁ s₁ ∧ XRunL E C s₁ ls₂ s'
  | s, s', [], ls₂ => by simp [XRunL]
  | s, s', l :: ls₁, ls₂ => by
    simp only [List.cons_append, XRunL]
    constructor
    · rintro ⟨s₁, h1, h2⟩
      obtain ⟨s₂, h3, h4⟩ := xrunL_append.mp h2
      exact ⟨s₂, ⟨s₁, h1, h3⟩, h4⟩
    · rintro ⟨s₂, ⟨s₁, h1, h3⟩, h4⟩
      exact ⟨s₁, h1, xrunL_append.mpr ⟨s₂, h3, h4⟩⟩

/-- One label, then the rest, of a decided run. -/
theorem xrun_cons {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T} {ls : List (XLbl N T)} :
    xrun C s (l :: ls) = some s' ↔ ∃ s₁, xstep C s l = some s₁ ∧ xrun C s₁ ls = some s' := by
  simp only [xrun, Option.bind_eq_some_iff]

/-- A decided run through `ls₁`, then `ls₂`. -/
theorem xrun_append {C : Cfg N T} :
    ∀ {s s' : XSt N T} {ls₁ ls₂ : List (XLbl N T)},
      xrun C s (ls₁ ++ ls₂) = some s' ↔ ∃ s₁, xrun C s ls₁ = some s₁ ∧ xrun C s₁ ls₂ = some s'
  | s, s', [], ls₂ => by simp [xrun]
  | s, s', l :: ls₁, ls₂ => by
    rw [List.cons_append, xrun_cons]
    constructor
    · rintro ⟨s₁, h1, h2⟩
      obtain ⟨s₂, h3, h4⟩ := xrun_append.mp h2
      exact ⟨s₂, xrun_cons.mpr ⟨s₁, h1, h3⟩, h4⟩
    · rintro ⟨s₂, h, h4⟩
      obtain ⟨s₁, h1, h3⟩ := xrun_cons.mp h
      exact ⟨s₁, h1, xrun_append.mpr ⟨s₂, h3, h4⟩⟩

/-- A label run of the reference executor is a decided run. -/
theorem xrunL_ref {C : Cfg N T} :
    ∀ {s s' : XSt N T} {ls : List (XLbl N T)}, XRunL RefExec C s ls s' ↔ xrun C s ls = some s'
  | s, s', [] => by simp [XRunL, xrun, eq_comm]
  | s, s', l :: ls => by
    rw [xrun_cons]
    simp only [XRunL, RefExec]
    constructor
    · rintro ⟨s₁, h1, h2⟩; exact ⟨s₁, h1, xrunL_ref.mp h2⟩
    · rintro ⟨s₁, h1, h2⟩; exact ⟨s₁, h1, xrunL_ref.mpr h2⟩

/-! ## L1: the marking frame -/

/-- The labels whose step may change the marking ([CONC-001], [EXEC-020]): a start (consumption
and drains on the pass-visible prefix), a commit or a timeout deposit (the emission), a
publication (a flushed batch) and an injection (one token). -/
def _root_.Libpetri.Spec.XLbl.marks : XLbl N T → Bool
  | .start _ _ | .commit _ | .tdeposit _ | .publish _ | .inject _ => true
  | _ => false

/-- **L1, frame**: every other step leaves the marking as it is. -/
theorem xstepW_M_frame {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : xstepW P C s l = some s') (hl : l.marks = false) : s'.M = s.M := by
  by_cases ho : l.outside = true
  · exact (xstepW_outside_frame h ho).1
  cases l with
  | delay | write | flush | ret | expire | request | drain | close | terminateNow =>
    simp [XLbl.outside] at ho
  | start | commit | tdeposit | publish | inject => simp [XLbl.marks] at hl
  | fail i => obtain ⟨f, -, -, -, rfl⟩ := failStep_some h; rfl
  | endCompletions => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endCompletions h; rfl
  | endPublications => obtain ⟨-, -, -, rfl⟩ := xstepW_endPublications h; rfl
  | discard k => obtain ⟨_, _, _, -, -, -, -, rfl⟩ := discardStep_some h; rfl
  | snapshot a => obtain ⟨-, -, -, rfl⟩ := snapshotStep_some h; rfl
  | endEvents => obtain ⟨-, -, -, rfl⟩ := xstepW_endEvents h; rfl
  | update => obtain ⟨-, -, rfl⟩ := xstepW_update h; rfl
  | deadline ns => obtain ⟨-, -, -, rfl⟩ := xstepW_deadline h; rfl
  | finish c =>
    cases c with
    | quiescent => obtain ⟨-, -, -, rfl⟩ := xstepW_finishQuiescent h; rfl
    | closed => obtain ⟨-, -, -, -, rfl⟩ := xstepW_finishClosed h; rfl
    | terminal => obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h; rfl
    | stopped => obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h; rfl
  | begin => obtain ⟨-, -, -, -, rfl⟩ := xstepW_begin h; rfl
  | lose n => obtain ⟨_, _, -, -, -, -, -, -, rfl⟩ := loseStep_some h; rfl
  | endPass => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endPass h; rfl
  | park tmr => obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := parkStep_some h; rfl
  | wake => obtain ⟨-, -, rfl⟩ := wakeStep_some h; rfl

/-- **L1, shapes**: a step leaves the marking as it is, or it is a start that replaces it by the
pass-visible marking with the head of the order consumed and the same-pass tail behind it, or a
settle or a publication that appends a list at the tails, or an injection that appends one
token at the tail of its place. -/
theorem xstepW_M_cases {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : xstepW P C s l = some s') :
    s'.M = s.M ∨
      (∃ n sy t, l = .start n sy ∧ s.order.head? = some t ∧ s'.M = liveAfter s t) ∨
      (∃ i e, (l = .commit i ∨ l = .tdeposit i) ∧ s'.M = qAppend s.M e) ∨
      (∃ i b, l = .publish i ∧ s.pq.head? = some (i, b) ∧ s'.M = qAppend s.M b) ∨
      (∃ k p x, l = .inject k ∧ s.eq.head? = some (k, p, x) ∧ s'.M = qAppendOne s.M p x) := by
  cases hm : l.marks
  · exact Or.inl (xstepW_M_frame h hm)
  cases l with
  | start n sy =>
    obtain ⟨t, rest, ho, -, -, -, -, -, -, rfl⟩ := startStep_some h
    exact Or.inr (Or.inl ⟨n, sy, t, rfl, by simp [ho], rfl⟩)
  | commit i =>
    obtain ⟨f, e, -, -, -, -, -, rfl⟩ := commitStep_some h
    exact Or.inr (Or.inr (Or.inl ⟨i, e, Or.inl rfl, rfl⟩))
  | tdeposit i =>
    obtain ⟨f, e, -, -, -, -, rfl⟩ := tdepositStep_some h
    exact Or.inr (Or.inr (Or.inl ⟨i, e, Or.inr rfl, rfl⟩))
  | publish i =>
    obtain ⟨b, rest, hq, -, -, rfl⟩ := publishStep_some h
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i, b, rfl, by simp [hq], rfl⟩)))
  | inject k =>
    obtain ⟨p, x, rest, he, -, -, -, rfl⟩ := injectStep_some h
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨k, p, x, rfl, by simp [he], rfl⟩)))
  | _ => simp [XLbl.marks] at hm

/-- A run of steps that leave the marking alone leaves it alone. -/
theorem xrun_M_frame {C : Cfg N T} :
    ∀ {s s' : XSt N T} {ls : List (XLbl N T)}, xrun C s ls = some s' →
      (∀ l ∈ ls, l.marks = false) → s'.M = s.M
  | s, s', [], h, _ => by cases h; rfl
  | s, s', l :: ls, h, hl => by
    obtain ⟨s₁, h1, h2⟩ := xrun_cons.mp h
    rw [xrun_M_frame h2 fun l' hl' => hl l' (List.mem_cons_of_mem _ hl'),
      xstepW_M_frame h1 (hl l List.mem_cons_self)]

/-! ## L2: a start and its commit are one `RefQFire` step -/

omit [DecidableEq N] in
/-- With no same-pass deposit, the pass sees the whole marking. -/
theorem vis_of_delta_zero {s : XSt N T} (h : ∀ p, s.delta p = 0) : vis s = s.M := by
  funext p; simp [vis, h p]

omit [DecidableEq N] in
/-- With no same-pass deposit, the same-pass tail is empty. -/
theorem hid_of_delta_zero {s : XSt N T} (h : ∀ p, s.delta p = 0) (p : N) : hid s p = [] := by
  simp [hid, h p]

/-- With no same-pass deposit, a start consumes from the whole marking. -/
theorem liveAfter_of_delta_zero {s : XSt N T} (h : ∀ p, s.delta p = 0) (t : Trans N) :
    liveAfter s t = qConsume s.M t := by
  funext p
  simp only [liveAfter, vis_of_delta_zero h, hid_of_delta_zero h, List.append_nil]

/-- What a firing's start fixed: its identity, its transition and the tokens it delivered. -/
def fkey (g : Firing N T) : Nat × Trans N × QDelivered N T := (g.id, g.t, g.deliv)

omit [DecidableEq N] in
/-- Updating one firing's record by a map that keeps the start record. -/
theorem mem_updFiring {s : XSt N T} {i : Nat} {h : Firing N T → Firing N T}
    (hh : ∀ g, fkey (h g) = fkey g) {g' : Firing N T} (hg : g' ∈ updFiring s i h) :
    ∃ g ∈ s.fl, fkey g = fkey g' := by
  unfold updFiring at hg
  obtain ⟨g, hgm, rfl⟩ := List.mem_map.mp hg
  exact ⟨g, hgm, by split <;> simp [hh]⟩

omit [DecidableEq N] in
/-- Settling removes firings and adds none. -/
theorem mem_settle {s : XSt N T} {i : Nat} {g' : Firing N T} (hg : g' ∈ (settle s i).fl) :
    g' ∈ s.fl :=
  (List.mem_filter.mp hg).1

/-- Every step but a start adds no firing and keeps the start record of every firing in flight.
-/
theorem xstepW_fl_origin {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : xstepW P C s l = some s') (hl : ∀ n sy, l ≠ .start n sy) :
    ∀ g' ∈ s'.fl, ∃ g ∈ s.fl, fkey g = fkey g' := by
  intro g' hg'
  have keep : ∀ g ∈ s.fl, s'.fl = s.fl → g' = g → ∃ g ∈ s.fl, fkey g = fkey g' :=
    fun g hg _ he => ⟨g, hg, by rw [he]⟩
  have same : s'.fl = s.fl → ∃ g ∈ s.fl, fkey g = fkey g' := fun he => ⟨g', he ▸ hg', rfl⟩
  cases l with
  | start n sy => exact absurd rfl (hl n sy)
  | delay δ => cases xstepW_delay h; exact same rfl
  | write i p x =>
    obtain ⟨f, -, -, rfl⟩ := writeStep_some h
    exact mem_updFiring (by intro; rfl) hg'
  | flush i =>
    obtain ⟨f, -, -, -, -, ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ := flushStep_some h
    · exact mem_updFiring (by intro; rfl) hg'
    · exact mem_updFiring (by intro; rfl) hg'
  | ret i ok =>
    obtain ⟨f, -, -, rfl⟩ := retStep_some h
    exact mem_updFiring (by intro; rfl) hg'
  | expire i e =>
    obtain ⟨f, -, -, -, -, -, rfl⟩ := expireStep_some h
    exact mem_updFiring (by intro; rfl) hg'
  | request p x r =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := requestStep_some h <;> exact same rfl
  | drain => obtain ⟨-, rfl⟩ := drainStep_some h; exact same rfl
  | close => obtain ⟨-, rfl⟩ := closeStep_some h; exact same rfl
  | terminateNow => obtain ⟨-, rfl⟩ := terminateStep_some h; exact same rfl
  | commit i =>
    obtain ⟨f, e, -, -, -, -, -, rfl⟩ := commitStep_some h
    exact ⟨g', mem_settle hg', rfl⟩
  | fail i =>
    obtain ⟨f, -, -, -, rfl⟩ := failStep_some h
    exact ⟨g', mem_settle hg', rfl⟩
  | tdeposit i =>
    obtain ⟨f, e, -, -, -, -, rfl⟩ := tdepositStep_some h
    exact ⟨g', mem_settle hg', rfl⟩
  | endCompletions => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endCompletions h; exact same rfl
  | publish i => obtain ⟨b, rest, -, -, -, rfl⟩ := publishStep_some h; exact same rfl
  | endPublications => obtain ⟨-, -, -, rfl⟩ := xstepW_endPublications h; exact same rfl
  | inject k => obtain ⟨_, _, _, -, -, -, -, rfl⟩ := injectStep_some h; exact same rfl
  | discard k => obtain ⟨_, _, _, -, -, -, -, rfl⟩ := discardStep_some h; exact same rfl
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
  | lose n => obtain ⟨_, _, -, -, -, -, -, -, rfl⟩ := loseStep_some h; exact same rfl
  | endPass => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endPass h; exact same rfl
  | park tmr => obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := parkStep_some h; exact same rfl
  | wake => obtain ⟨-, -, rfl⟩ := wakeStep_some h; exact same rfl

/-- A run of steps that leave the marking alone (no start among them) keeps the start record of
every firing in flight and adds none. -/
theorem xrun_fl_origin {C : Cfg N T} :
    ∀ {s s' : XSt N T} {ls : List (XLbl N T)}, xrun C s ls = some s' →
      (∀ l ∈ ls, l.marks = false) → ∀ g' ∈ s'.fl, ∃ g ∈ s.fl, fkey g = fkey g'
  | s, s', [], h, _ => by cases h; exact fun g' hg' => ⟨g', hg', rfl⟩
  | s, s', l :: ls, h, hl => by
    obtain ⟨s₁, h1, h2⟩ := xrun_cons.mp h
    intro g' hg'
    obtain ⟨g₁, hg₁, he₁⟩ :=
      xrun_fl_origin h2 (fun l' hl' => hl l' (List.mem_cons_of_mem _ hl')) g' hg'
    have hns : ∀ n sy, l ≠ .start n sy := by
      rintro n sy rfl; simp [XLbl.marks] at hl
    obtain ⟨g, hg, he⟩ := xstepW_fl_origin h1 hns g₁ hg₁
    exact ⟨g, hg, he.trans he₁⟩

/-- **L2, one start**: the start of the head `t` of the order consumes from the pass-visible
marking with the same-pass tail behind it, records the tokens it delivers, and for every emission
the output spec offers on the pass-visible marking it is the consumption half of a `RefQFire`
step from that marking. -/
theorem start_refQFire {C : Cfg N T} {s s' : XSt N T} {n : String} {sy : Bool}
    (h : RefExec C s (.start n sy) s') :
    ∃ t rest, s.order = t :: rest ∧ t.core.name = n ∧ s'.M = liveAfter s t ∧
      s'.fl = s.fl ++ [⟨s.nextId, t, qDelivered (vis s) t, s.now, sy, [], [], false, none⟩] ∧
      ∀ e, OfferedEmission s t e →
        RefQFire t (vis s) (qDelivered (vis s) t) e (qFire (vis s) t e) := by
  obtain ⟨t, rest, ho, -, -, -, hn, -, hen, rfl⟩ := startStep_some (P := refXPol) h
  exact ⟨t, rest, ho, hn, rfl, rfl, fun e ⟨ch, hch⟩ => ⟨hen, ⟨ch, hch⟩, rfl, rfl⟩⟩

/-- **L2, the segment, split at the commit**: the run to the state `s₁` the commit leaves from,
the firing record `f` the commit finds there and its emission `e`. -/
theorem segment_refQFire_split {C : Cfg N T} {s s₁ s' : XSt N T} {n : String} {sy : Bool}
    {i : Nat} {mid : List (XLbl N T)} {f : Firing N T} {e : List (N × T)}
    (h : xrun C s (.start n sy :: mid) = some s₁) (hc : RefExec C s₁ (.commit i) s')
    (hf : s₁.fl.find? (·.id == i) = some f) (hout : f.out = some (.ok e))
    (hd : ∀ p, s.delta p = 0) (hmid : ∀ l ∈ mid, l.marks = false)
    (hfresh : ∀ g ∈ s.fl, g.id ≠ s.nextId) (hi : i = s.nextId) :
    ∃ t, s.order.head? = some t ∧ t.core.name = n ∧ f.t = t ∧ f.deliv = qDelivered s.M t ∧
      s'.M = qFire s.M t e ∧ (OfferedEmission s t e → RefQFire t s.M f.deliv e s'.M) := by
  obtain ⟨s₀, h1, h2⟩ := xrun_cons.mp h
  obtain ⟨t, rest, ho, hn, hM1, hfl1, hq⟩ := start_refQFire h1
  obtain ⟨f', e', hf', hout', -, -, -, rfl⟩ := refExec_commit hc
  rw [hf] at hf'
  obtain rfl := Option.some.inj hf'
  rw [hout] at hout'
  obtain rfl : e = e' := by simpa using hout'
  have hfm : f ∈ s₁.fl := List.mem_of_find?_eq_some hf
  have hfi : f.id = i := by simpa using List.find?_some hf
  obtain ⟨g, hg, hk⟩ := xrun_fl_origin h2 hmid f hfm
  rw [hfl1] at hg
  have hkey : fkey f = (s.nextId, t, qDelivered s.M t) := by
    rcases List.mem_append.mp hg with hg | hg
    · exact absurd (by simp only [fkey, Prod.mk.injEq] at hk; rw [hk.1, hfi, hi]) (hfresh g hg)
    · simp only [List.mem_singleton] at hg
      rw [← hk, hg, vis_of_delta_zero hd]; rfl
  simp only [fkey, Prod.mk.injEq] at hkey
  have hM : (depositAt C s₁ i e).M = qFire s.M t e := by
    show qAppend s₁.M e = _
    rw [xrun_M_frame h2 hmid, hM1, liveAfter_of_delta_zero hd]; rfl
  refine ⟨t, by simp [ho], hn, hkey.2.1, hkey.2.2, hM, fun ho' => ?_⟩
  have hq' := hq e ho'
  rw [vis_of_delta_zero hd] at hq'
  rw [hkey.2.2, hM]
  exact hq'

/-- **L2, the segment**: a start from a pass state with no same-pass deposit, then steps that
leave the marking alone, then the commit of the started firing (fresh identity), is one
`RefQFire` step of the started transition from the marking of the start: the delivered tokens
are what the firing recorded, the emission is what it committed, and the marking after the
commit is the queue firing's result. The emission must be an offered deposit
(`OfferedEmission`): validation reads sets of places, so a validated emission can carry more
tokens than an offered deposit, and such runs are [IO-016]'s subject, not `RefQFire`'s. A firing
that flushed has its published batches outside `e` (`f.pub`); the segment then stops before their
publication. -/
theorem segment_refQFire {C : Cfg N T} {s s' : XSt N T} {n : String} {sy : Bool} {i : Nat}
    {mid : List (XLbl N T)} (h : xrun C s (.start n sy :: mid ++ [.commit i]) = some s')
    (hd : ∀ p, s.delta p = 0) (hmid : ∀ l ∈ mid, l.marks = false)
    (hfresh : ∀ g ∈ s.fl, g.id ≠ s.nextId) (hi : i = s.nextId) :
    ∃ (t : Trans N) (f : Firing N T) (e : List (N × T)), s.order.head? = some t ∧
      t.core.name = n ∧ f.id = i ∧ f.t = t ∧
      f.deliv = qDelivered s.M t ∧ f.out = some (.ok e) ∧ s'.M = qFire s.M t e ∧
      (OfferedEmission s t e → RefQFire t s.M f.deliv e s'.M) := by
  rw [List.cons_append] at h
  obtain ⟨s₁, h1, h⟩ := xrun_cons.mp h
  obtain ⟨s₂, h2, h3⟩ := xrun_append.mp h
  obtain ⟨s₃, h3, h4⟩ := xrun_cons.mp h3
  cases h4
  obtain ⟨t, rest, ho, hn, hM1, hfl1, hq⟩ := start_refQFire h1
  obtain ⟨f, e, hf, hout, -, -, -, rfl⟩ := refExec_commit h3
  have hfm : f ∈ s₂.fl := List.mem_of_find?_eq_some hf
  have hfi : f.id = i := by simpa using List.find?_some hf
  obtain ⟨g, hg, hk⟩ := xrun_fl_origin h2 hmid f hfm
  rw [hfl1] at hg
  have hkey : fkey f = (s.nextId, t, qDelivered s.M t) := by
    rcases List.mem_append.mp hg with hg | hg
    · exact absurd (by simp only [fkey, Prod.mk.injEq] at hk; rw [hk.1, hfi, hi]) (hfresh g hg)
    · simp only [List.mem_singleton] at hg
      rw [← hk, hg, vis_of_delta_zero hd]; rfl
  simp only [fkey, Prod.mk.injEq] at hkey
  have hM : (depositAt C s₂ i e).M = qFire s.M t e := by
    show qAppend s₂.M e = _
    rw [xrun_M_frame h2 hmid, hM1, liveAfter_of_delta_zero hd]; rfl
  refine ⟨t, f, e, by simp [ho], hn, hfi, hkey.2.1, hkey.2.2, hout, hM, fun ho' => ?_⟩
  have hq' := hq e ho'
  rw [vis_of_delta_zero hd] at hq'
  rw [hkey.2.2, hM]
  exact hq'

omit [DecidableEq N] in
/-- The firing with identity `i`, appended behind firings with other identities. -/
theorem find_fresh_append {l : List (Firing N T)} {g : Firing N T} {i : Nat}
    (hl : ∀ g' ∈ l, g'.id ≠ i) (hg : g.id = i) : (l ++ [g]).find? (·.id == i) = some g := by
  rw [List.find?_append, List.find?_eq_none.mpr (by intro x hx; simpa using hl x hx)]
  simp [hg]

omit [DecidableEq N] in
/-- Updating firing `i`, appended behind firings with other identities. -/
theorem map_upd_fresh_append {l : List (Firing N T)} {g : Firing N T} {i : Nat}
    (hl : ∀ g' ∈ l, g'.id ≠ i) (hg : g.id = i) (h : Firing N T → Firing N T) :
    (l ++ [g]).map (fun g' => if g'.id == i then h g' else g') = l ++ [h g] := by
  rw [List.map_append]
  congr 1
  · conv_rhs => rw [← List.map_id l]
    exact List.map_congr_left fun x hx => by simp [hl x hx]
  · simp [hg]

/-- An action's writes land in its buffer, in write order. -/
theorem writes_run {C : Cfg N T} {l : List (Firing N T)} {i : Nat} (hl : ∀ g' ∈ l, g'.id ≠ i) :
    ∀ (ws : List (N × T)) (s : XSt N T) (g : Firing N T), s.fl = l ++ [g] → g.id = i →
      g.out = none →
      xrun C s (ws.map fun x => .write i x.1 x.2) =
        some { s with fl := l ++ [{ g with buf := g.buf ++ ws }] }
  | [], s, g, hs, _, _ => by
    simp only [List.map_nil, xrun, List.append_nil]
    cases s; simp only at hs; subst hs; rfl
  | (p, x) :: ws, s, g, hs, hg, ho => by
    have h1 : xstep C s (.write i p x) =
        some { s with fl := l ++ [{ g with buf := g.buf ++ [(p, x)] }] } := by
      show writeStep s i p x = _
      unfold writeStep onOpen updFiring
      rw [hs, find_fresh_append hl hg]
      dsimp only
      rw [if_pos (by simp [ho]), map_upd_fresh_append hl hg]
    simp only [List.map_cons, xrun, h1, Option.bind_some]
    rw [writes_run hl ws _ { g with buf := g.buf ++ [(p, x)] } rfl hg ho]
    simp [List.append_assoc]

/-- **L2, converse**: every `RefQFire` step of the head of a pass order, from a pass state with no
same-pass deposit, whose emission validation and the relay check accept, is realised by the
reference executor: a synchronous start, the action's writes of the emission, its normal return
and its inline commit leave the queue firing's result. -/
theorem refQFire_realised {C : Cfg N T} {s : XSt N T} {t : Trans N} {rest : List (Trans N)}
    {δ : QDelivered N T} {e : List (N × T)} {M' : QMarking N T}
    (ho : s.order = t :: rest) (hph : s.phase = .pass) (hl : liveB C s = true)
    (hpf : passFree s = true) (hst : (stampOf (s.st t.core.name)).isSome = true)
    (hd : ∀ p, s.delta p = 0) (hfresh : ∀ g ∈ s.fl, g.id ≠ s.nextId)
    (hv : C.validate t (e.map Prod.fst) = true) (hr : C.relay t (qDelivered s.M t) e = true)
    (hq : RefQFire t s.M δ e M') :
    ∃ s', xrun C s (.start t.core.name true :: (e.map fun x => .write s.nextId x.1 x.2) ++
        [.ret s.nextId true, .commit s.nextId]) = some s' ∧ s'.M = M' ∧
      δ = qDelivered s.M t := by
  obtain ⟨hen, -, hδ, hM'⟩ := hq
  -- the start
  let f₀ : Firing N T := ⟨s.nextId, t, qDelivered (vis s) t, s.now, true, [], [], false, none⟩
  let s₁ : XSt N T :=
    { s with M := liveAfter s t, order := rest, started := true, nextId := s.nextId + 1,
             fl := s.fl ++ [f₀],
             st := unreap C (inPlaces t ++ t.core.resets) (afterStart refXPol C s t) }
  have h1 : xstep C s (.start t.core.name true) = some s₁ := by
    show startStep refXPol C s t.core.name true = _
    unfold startStep
    rw [ho]
    dsimp only
    rw [if_pos (by simp [hph, hl, hpf, hst, refXPol, vis_of_delta_zero hd, hen])]
  -- the writes
  have h2 := writes_run (C := C) (l := s.fl) (i := s.nextId) hfresh e s₁ f₀ rfl rfl rfl
  let s₂ : XSt N T := { s₁ with fl := s.fl ++ [{ f₀ with buf := f₀.buf ++ e }] }
  -- the return
  let f₂ : Firing N T := { f₀ with buf := [] ++ e, out := some (.ok e) }
  let s₃ : XSt N T := { s₂ with cq := s₂.cq ++ [s.nextId], parked := false, fl := s.fl ++ [f₂] }
  have h3 : xstep C s₂ (.ret s.nextId true) = some s₃ := by
    show retStep s₂ s.nextId true = _
    unfold retStep onOpen updFiring
    rw [show s₂.fl = s.fl ++ [{ f₀ with buf := f₀.buf ++ e }] from rfl,
      find_fresh_append hfresh rfl]
    dsimp only
    rw [if_pos (show f₀.out.isNone = true from rfl), map_upd_fresh_append hfresh rfl]
    simp [s₃, f₂, f₀]
  -- the inline commit
  have hlive : liveB C s₃ = true := by
    simp only [liveB, List.all_eq_true, List.isEmpty_iff] at hl ⊢
    intro p hp
    show liveAfter s t p = []
    rw [liveAfter_of_delta_zero hd]
    simp only [qConsume, qPostInput, hl p hp, List.drop_nil, ite_self]
  have h4 : xstep C s₃ (.commit s.nextId) = some (depositAt C s₃ s.nextId e) := by
    show commitStep refXPol C s₃ s.nextId = _
    unfold commitStep
    rw [show s₃.fl = s.fl ++ [f₂] from rfl, find_fresh_append hfresh rfl]
    dsimp only
    rw [show f₂.out = some (.ok e) from rfl]
    dsimp only
    rw [if_pos]
    simp only [canSettle, settleOk, Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨?_, hlive⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · show isExecPhase s.phase = true
      rw [hph]; rfl
    · simp [s₃, s₂, s₁]
    · show (match s.phase with
        | .completions | .await => s.mode != .stopped
        | .pass => f₂.sync
        | _ => false) = true
      rw [hph]
    · simpa [refXPol, validIn, f₂, f₀] using hv
    · simpa [f₂, f₀, vis_of_delta_zero hd] using hr
  refine ⟨depositAt C s₃ s.nextId e, ?_, ?_, hδ⟩
  · rw [List.cons_append, xrun_cons]
    refine ⟨s₁, h1, ?_⟩
    rw [xrun_append]
    refine ⟨s₂, h2, ?_⟩
    simp only [xrun, h3, h4, Option.bind_some]
  · show qAppend (liveAfter s t) e = M'
    rw [liveAfter_of_delta_zero hd, hM']
    rfl

/-! ## L3: one pass with one synchronous firing is one `RefTStep` firing

### The stamp arithmetic (`status_agrees`, from the refexec-final spike) -/

/-- The update of one status when no firing of the name is in flight (`updSt` of the reference,
`updSt_of_noFlight`): an armed name keeps its stamp while enabled unless its restart flag is set,
an off name enabled is newly armed, a reaped name stays reaped. -/
def updOf (st : Status) (e2 : Bool) (now : Nat) : Status :=
  match st with
  | .armed k rs => if e2 then (if rs then .armed now false else .armed k false) else .off
  | .off => if e2 then .armed now false else .off
  | .reaped => .reaped

/-- What one atomic firing of another transition does to a status before the update: the
restart flag when the live intermediate marking disables the name (`e1` false), and a write of
one of its arc places (`w`) ends a reap. -/
def preOf (st : Status) (e1 w : Bool) : Status :=
  match st with
  | .armed k r => if e1 then .armed k r else .armed k true
  | .reaped => if w then .off else .reaped
  | .off => .off

/-- One atomic firing of another transition (start, commit, the next update with no clock
advance), on the status of a name that is not in flight. -/
def stepStatus (st : Status) (e1 w e2 : Bool) (now : Nat) : Status := updOf (preOf st e1 w) e2 now

/-- `restampW refPolicy` on the same bits: keep the stamp `s` when armed (`a`) and enabled in the
intermediate marking (`e1`) and after (`e2`); else a fresh stamp `now` when enabled after and
armed before or written (`w`). -/
def refDecide (a e1 e2 w : Bool) (s now : Nat) : Option Nat :=
  if a && e1 && e2 then some s
  else if e2 && (a || w) then some now else none

/-- **`status_agrees`**: the executor's status rule over one atomic firing is `refPolicy`'s
stamp rule, in every case, under the two premises a phase boundary supplies: no restart flag is
pending, and an off name that becomes enabled was written (`InvU`: an enabled off name not in
flight does not exist at a boundary, and a count change on an arc place is a write). -/
theorem status_agrees (st : Status) (e1 w e2 : Bool) (now : Nat)
    (hnr : ∀ k, st ≠ .armed k true) (hoff : st = .off → e2 = true → w = true) :
    stampOf (stepStatus st e1 w e2 now) =
      refDecide (stampOf st).isSome e1 e2 w ((stampOf st).getD 0) now := by
  cases st with
  | off =>
    cases e1 <;> cases w <;> cases e2 <;>
      simp_all [stepStatus, updOf, preOf, refDecide, stampOf]
  | reaped =>
    cases e1 <;> cases w <;> cases e2 <;> simp [stepStatus, updOf, preOf, refDecide, stampOf]
  | armed k r =>
    cases r with
    | true => exact absurd rfl (hnr k)
    | false =>
      cases e1 <;> cases w <;> cases e2 <;> simp [stepStatus, updOf, preOf, refDecide, stampOf]

/-- A loser of the pass recheck is off where the status rule says `armed k true`: the update
treats both alike. -/
theorem updOf_off_eq (k : Nat) (e2 : Bool) (now : Nat) :
    updOf .off e2 now = updOf (.armed k true) e2 now := by
  cases e2 <;> rfl

/-- The reference update of a name of the net with no firing in flight is `updOf`. -/
theorem updSt_of_noFlight {C : Cfg N T} {s : XSt N T} {x : String} {u : Trans N}
    (hf : findT C x = some u) (hfl : s.fl = []) :
    updSt refXPol C s x = updOf (s.st x) (enabledNA (qCount s.M) u.core) s.now := by
  unfold updSt
  rw [hf]
  simp only [inFlightN, hfl, List.any_nil, refXPol]
  cases s.st x with
  | armed k rs => cases rs <;> rfl
  | off => cases enabledNA (qCount s.M) u.core <;> simp [updOf]
  | reaped => rfl

/-- `restampW refPolicy` on a name other than the fired one is `refDecide`, when an armed name is
enabled (`InvU` clause 1). -/
theorem restampW_ref {X : TimedNet N} {v : TSt N} {t u : Trans N} {d : List N} {m' : N → Nat}
    (hne : u.core.name ≠ t.core.name)
    (harm : (v.stamp u.core.name).isSome = true → enabledNA v.m u.core = true) :
    restampW refPolicy X v t d m' u =
      refDecide (v.stamp u.core.name).isSome (enabledNA (mid t v.m) u.core)
        (enabledNA m' u.core) (writesArc t d u) ((v.stamp u.core.name).getD 0) v.now := by
  have ha : v.armed u = (v.stamp u.core.name).isSome := by
    unfold TSt.armed
    cases h : (v.stamp u.core.name).isSome
    · simp
    · simp [harm h]
  unfold restampW refDecide
  simp only [refPolicy, ha]
  cases hs : v.stamp u.core.name <;> simp [hne]

/-! ### Counts -/

/-- The counts after a consume are the intermediate marking of [TIME-012]. -/
theorem qCount_qConsume (M : QMarking N T) (t : Trans N) :
    qCount (qConsume M t) = mid t (qCount M) := by
  have h := qCount_qFire M t ([] : List (N × T))
  have hd : depProd (([] : List (N × T)).map Prod.fst) = fun _ => 0 := by
    funext p; simp [depProd]
  rw [hd] at h
  exact h

/-- A place the firing does not write keeps its count. -/
theorem fireNC_of_not_writes {t : Trans N} {d : List N} {p : N} (m : N → Nat)
    (h : writes t d p = false) : fireNC m t.core (depProd d) p = m p := by
  simp only [writes, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
  obtain ⟨⟨hi, hr⟩, hd⟩ := h
  have hn : nspecAt t.core p = none := by
    unfold nspecAt
    rw [List.find?_eq_none]
    intro x hx hxp
    exact hi (by simp only [decide_eq_true_eq] at hxp; subst hxp; exact List.mem_map_of_mem hx)
  simp [fireNC, hr, nconsumed, hn, depProd, List.count_eq_zero_of_not_mem hd]

/-- A transition none of whose arc places the firing writes keeps its enablement. -/
theorem enabled_of_not_writesArc {t u : Trans N} {d : List N} (m : N → Nat)
    (h : writesArc t d u = false) :
    enabledNA (fireNC m t.core (depProd d)) u.core = enabledNA m u.core := by
  apply enabledNA_congr
  intro p hp
  apply fireNC_of_not_writes
  simp only [writesArc, List.any_eq_false] at h
  simpa using h p hp

/-- The count of a place in an emission is the length of its emitted tokens. -/
theorem countIn_eq (e : List (N × T)) (p : N) : countIn e p = (qEmittedTo e p).length := by
  unfold countIn qEmittedTo
  rw [List.length_map]
  rfl

/-- After a commit inside a pass that had no same-pass deposit, the pass still sees the marking
before the commit. -/
theorem vis_depositAt {C : Cfg N T} {s : XSt N T} {i : Nat} {e : List (N × T)}
    (hph : s.phase = .pass) (hd : ∀ p, s.delta p = 0) : vis (depositAt C s i e) = s.M := by
  funext p
  simp only [vis, depositAt, settle, hph, if_true, hd p, Nat.zero_add, qAppend_apply,
    List.length_append, countIn_eq, Nat.add_sub_cancel]
  exact List.take_left' rfl

/-! ### The pass order -/

/-- The reference order holds only ready indices. -/
theorem mem_refReadyOrder {I : ReadyIn} {a : Nat} (h : a ∈ refReadyOrder I) :
    a ∈ I.readyList := by
  unfold refReadyOrder at h
  split at h
  · exact h
  · exact (sortBy_perm _ _).mem_iff.mp h

/-- Every transition of a pass order is a transition of the net, Ready at the cycle reading. -/
theorem mem_readyOrder {C : Cfg N T} {s : XSt N T} {u : Trans N} (h : u ∈ readyOrder C s) :
    u ∈ C.X.net.transitions ∧ Ready C.X (viewAt s s.cyc) u := by
  unfold readyOrder at h
  obtain ⟨a, ha, hu⟩ := List.mem_filterMap.mp h
  obtain ⟨hlt, hr⟩ := (ReadyIn.mem_readyList _ a).mp (mem_refReadyOrder ha)
  simp only [ReadyIn.ofTSt] at hlt
  rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at hu
  subst hu
  exact ⟨List.getElem_mem hlt, (ReadyIn.ofTSt_ready _ _ _ _ a hlt).mp hr⟩

omit [DecidableEq N] in
/-- The net's transition named `x`. -/
theorem findT_spec {C : Cfg N T} {x : String} {u : Trans N} (h : findT C x = some u) :
    u ∈ C.X.net.transitions ∧ u.core.name = x :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

omit [DecidableEq N] in
/-- Under distinct names, a transition of the net is the one its name finds. -/
theorem findT_of_mem {C : Cfg N T} (hN : NamesDistinct C.X) {u : Trans N}
    (hu : u ∈ C.X.net.transitions) : findT C u.core.name = some u :=
  (inNet_iff_mem hN u).mpr hu

/-! ### The steps of the segment -/

/-- The recheck losers of a pass: each `lose` turns its name off, and only a name of the order
that is not armed and enabled on the pass-visible marking loses. Nothing else changes. -/
theorem loses_run {C : Cfg N T} :
    ∀ {s s' : XSt N T} {ls : List String}, xrun C s (ls.map XLbl.lose) = some s' →
      s' = { s with order := s'.order, st := s'.st } ∧
      ∀ x, s'.st x = s.st x ∨ (s'.st x = .off ∧ ∃ u ∈ s.order, u.core.name = x ∧
        ¬ ((stampOf (s.st x)).isSome = true ∧ enabledNA (qCount (vis s)) u.core = true))
  | s, s', [], h => by cases h; exact ⟨rfl, fun _ => Or.inl rfl⟩
  | s, s', x0 :: ls, h => by
    obtain ⟨s₁, h1, h2⟩ := xrun_cons.mp h
    obtain ⟨u0, rest, ho, -, -, -, hx0, hng, hs1⟩ := loseStep_some (P := refXPol) h1
    obtain ⟨he, hst⟩ := loses_run h2
    have hvis : vis s₁ = vis s := by rw [hs1]; rfl
    refine ⟨by rw [he, hs1], fun x => ?_⟩
    have hs1x : s₁.st x = if x = x0 then .off else s.st x := by rw [hs1]
    by_cases hx : x = x0
    · subst hx
      right
      refine ⟨?_, u0, by simp [ho], hx0, by simpa [refXPol] using hng⟩
      rcases hst x with h | ⟨h, -⟩
      · rw [h, hs1x, if_pos rfl]
      · exact h
    · have hstx := hst x
      rw [hs1x, if_neg hx] at hstx
      rcases hstx with h | ⟨h, u, hu, hun, hnot⟩
      · exact Or.inl h
      · rw [hvis] at hnot
        have hu' : u ∈ s.order := by
          rw [ho]; rw [hs1] at hu; exact List.mem_cons_of_mem _ hu
        exact Or.inr ⟨h, u, hu', hun, hnot⟩

/-- An action's writes land in the buffer of the only firing in flight. -/
theorem writes_single {C : Cfg N T} {i : Nat} :
    ∀ (ws : List (N × T)) {s s' : XSt N T} {g : Firing N T}, s.fl = [g] →
      xrun C s (ws.map fun x => .write i x.1 x.2) = some s' →
      s' = { s with fl := [{ g with buf := g.buf ++ ws }] }
  | [], s, s', g, hs, h => by
    cases h
    cases s; simp only at hs; subst hs; simp
  | (p, x) :: ws, s, s', g, hs, h => by
    obtain ⟨s₁, h1, h2⟩ := xrun_cons.mp h
    obtain ⟨f, hf, -, hs1⟩ := writeStep_some (show writeStep s i p x = some s₁ from h1)
    rw [hs] at hf
    have hfg : f = g ∧ (g.id == i) = true := by
      simp only [List.find?_cons, List.find?_nil] at hf
      split at hf
      · exact ⟨(Option.some.inj hf).symm, ‹_›⟩
      · exact absurd hf (by simp)
    have hfl1 : s₁.fl = [{ g with buf := g.buf ++ [(p, x)] }] := by
      rw [hs1]
      simp only [updFiring, hs, List.map_cons, List.map_nil, hfg.2, if_true]
    rw [writes_single ws hfl1 h2, hs1]
    simp [List.append_assoc]

/-- The end of the cycle after the pass: steps 1, 1b and 2 with nothing queued, then the update.
-/
def cycleEndLabels : List (XLbl N T) :=
  [.endPass, .endCompletions, .endPublications, .endEvents, .update]

/-- The end of the cycle changes only the phase, the cycle reading and the statuses (the update).
-/
theorem cycleEnd_run {C : Cfg N T} {s s' : XSt N T} (h : xrun C s cycleEndLabels = some s') :
    s'.M = s.M ∧ s'.fl = s.fl ∧ s'.cyc = s.now ∧ s'.st = updSt refXPol C s := by
  obtain ⟨s₁, h1, h⟩ := xrun_cons.mp h
  obtain ⟨-, -, -, -, rfl⟩ := xstepW_endPass h1
  obtain ⟨s₂, h2, h⟩ := xrun_cons.mp h
  obtain ⟨-, -, -, -, rfl⟩ := xstepW_endCompletions h2
  obtain ⟨s₃, h3, h⟩ := xrun_cons.mp h
  obtain ⟨-, -, -, rfl⟩ := xstepW_endPublications h3
  obtain ⟨s₄, h4, h⟩ := xrun_cons.mp h
  obtain ⟨-, -, -, rfl⟩ := xstepW_endEvents h4
  obtain ⟨s₅, h5, h⟩ := xrun_cons.mp h
  obtain ⟨-, -, rfl⟩ := xstepW_update h5
  cases h
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A write of one of `u`'s arc places by a firing of `t` with deposit `d`: by its consumption or
drains, or by its deposit. -/
theorem writesArc_split (t u : Trans N) (d : List N) :
    writesArc t d u = ((arcPlaces u).any (fun p => decide (p ∈ inPlaces t ++ t.core.resets)) ||
      (arcPlaces u).any (fun p => decide (p ∈ d))) := by
  apply Bool.eq_iff_iff.mpr
  simp only [writesArc, writes, inPlaces, List.any_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    List.mem_append]
  constructor
  · rintro ⟨p, hp, (h | h) | h⟩
    · exact Or.inl ⟨p, hp, Or.inl h⟩
    · exact Or.inl ⟨p, hp, Or.inr h⟩
    · exact Or.inr ⟨p, hp, h⟩
  · rintro (⟨p, hp, h | h⟩ | ⟨p, hp, h⟩)
    · exact ⟨p, hp, Or.inl (Or.inl h)⟩
    · exact ⟨p, hp, Or.inl (Or.inr h)⟩
    · exact ⟨p, hp, Or.inr h⟩

/-- The status of a name other than the started one after the start and the commit of emission
places `d`, before the pass's losers and the update: `preOf` of its status at the start. -/
theorem pre_status {C : Cfg N T} {s₁ : XSt N T} {t u : Trans N} {x : String} {d : List N}
    (hfx : findT C x = some u) (hxt : x ≠ t.core.name) :
    unreap C d (unreap C (inPlaces t ++ t.core.resets) (afterStart refXPol C s₁ t)) x =
      preOf (s₁.st x) (enabledNA (qCount (liveAfter s₁ t)) u.core) (writesArc t d u) := by
  have hA : afterStart refXPol C s₁ t x = (match s₁.st x with
      | .armed k r =>
        if enabledNA (qCount (liveAfter s₁ t)) u.core then .armed k r else .armed k true
      | y => y) := by
    unfold afterStart
    rw [if_neg hxt, hfx]
    cases s₁.st x <;> rfl
  rw [writesArc_split]
  cases hs : s₁.st x with
  | off =>
    rw [hs] at hA
    exact unreap_off (unreap_off hA)
  | armed k r =>
    rw [hs] at hA
    unfold unreap
    rw [hA]
    cases enabledNA (qCount (liveAfter s₁ t)) u.core <;> simp [preOf]
  | reaped =>
    rw [hs] at hA
    unfold unreap
    rw [hA, hfx]
    cases h1 : (arcPlaces u).any (fun p => decide (p ∈ inPlaces t ++ t.core.resets)) <;>
      cases h2 : (arcPlaces u).any (fun p => decide (p ∈ d)) <;>
      simp only [h1, h2, preOf, ↓reduceIte, Bool.or_true, Bool.or_false, Bool.false_eq_true]

/-- The labels of one atomic firing in the executor: the pass begins, the head of the order
starts synchronously as firing `i`, its action writes `e`, returns normally and is committed
inside the pass, the rest of the order loses the recheck (`ls`), and the cycle ends with the next
update. -/
def atomicLabels (n : String) (i : Nat) (e : List (N × T)) (ls : List String) :
    List (XLbl N T) :=
  [.begin, .start n true] ++ (e.map fun x => .write i x.1 x.2) ++ [.ret i true, .commit i] ++
    ls.map .lose ++ cycleEndLabels

/-- **L3, one atomic firing**: from a state with `InvU`, no firing in flight, no restart flag
pending and the cycle reading equal to the present, the segment `atomicLabels` (the pass begins,
which needs the termination test; one synchronous start, its writes, its return and inline
commit, the recheck losers, the next update, no delay) is one `RefTStep` firing of the started
transition between the clock views, provided the emission's places are a deposit the output spec
offers. The started transition is the head of the pass order, a transition of the net, and the
marking after the segment is the queue firing's result (`qFire`). -/
theorem atomic_refTStep {C : Cfg N T} (hN : NamesDistinct C.X) {s s' : XSt N T} {n : String}
    {i : Nat} {e : List (N × T)} {ls : List String}
    (hinv : InvU C s) (hfl : s.fl = []) (hnow : s.now = s.cyc)
    (hnr : ∀ x k, s.st x ≠ .armed k true)
    (h : xrun C s (atomicLabels n i e ls) = some s') :
    ∃ t ∈ C.X.net.transitions, t.core.name = n ∧ s'.M = qFire s.M t e ∧
      ((∃ ch, deposit (nconsumed (qCount s.M) t.core) t.out ch = some (e.map Prod.fst)) →
        RefTStep C.X (viewAt s s.cyc) (.fire t (e.map Prod.fst)) (viewAt s' s'.cyc)) := by
  obtain ⟨hI1, hI2, hI3⟩ := hinv
  unfold atomicLabels at h
  obtain ⟨sA, hA, hT⟩ := xrun_append.mp h
  obtain ⟨s₅, h5, hL⟩ := xrun_append.mp hA
  obtain ⟨s₃, h3, hRC⟩ := xrun_append.mp h5
  obtain ⟨s₂, h2, hW⟩ := xrun_append.mp h3
  -- begin and start
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
  obtain ⟨t, rest, ho, -, -, -, hn, -, hen, rfl⟩ := startStep_some (P := refXPol) hs
  rw [hs1o] at ho
  have hen0 : enabledNA (qCount s.M) t.core = true := by
    simpa [refXPol, vis_of_delta_zero hd1, hs1M] using hen
  obtain ⟨ht, hready⟩ :=
    mem_readyOrder (show t ∈ readyOrder C s by rw [ho]; exact List.mem_cons_self)
  -- the writes
  have hW' := writes_single e (by show s₁.fl ++ _ = _; rw [hs1fl]; rfl) hW
  subst hW'
  -- the return and the commit
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
  -- the losers and the end of the cycle
  obtain ⟨hLe, hLst⟩ := loses_run hL
  obtain ⟨hTM, hTfl, hTcyc, hTst⟩ := cycleEnd_run hT
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
  have hAnow : sA.now = s.now := by
    rw [hLe]
    show s₅.now = s.now
    rw [hs5]
    show s₁.now = s.now
    rw [hs1]
  have hvis5 : qCount (vis s₅) = mid t (qCount s.M) := by
    rw [hs5, vis_depositAt (by exact hs1ph) (by exact hd1)]
    show qCount (liveAfter s₁ t) = _
    rw [liveAfter_of_delta_zero hd1, hs1M, qCount_qConsume]
  have hord5 : s₅.order = rest := by rw [hs5]; rfl
  refine ⟨t, ht, hn, by rw [hTM, hAM], fun hoff => ?_⟩
  obtain ⟨ha, hg, hx⟩ := (ready_iff _ _ _).mp hready
  -- the clock view after the segment
  have hview : viewAt s' s'.cyc =
      { m := qCount (qFire s.M t e), now := (viewAt s s.cyc).now,
        stamp := restampAll refPolicy C.X (viewAt s s.cyc) t (e.map Prod.fst)
          (qCount (qFire s.M t e)) } := by
    show (⟨qCount s'.M, s'.cyc, fun n => stampOf (s'.st n)⟩ : TSt N) = _
    rw [hTM, hAM, hTcyc, hAnow, hnow, hTst]
    congr 1
    funext x
    unfold restampAll
    cases hfx : C.X.net.transitions.find? (·.core.name == x) with
    | none =>
      have hfx' : findT C x = none := hfx
      unfold updSt
      rw [hfx']
      rfl
    | some u =>
      have hfx' : findT C x = some u := hfx
      obtain ⟨hu, hux⟩ := findT_spec hfx'
      simp only
      rw [updSt_of_noFlight hfx' hAfl, hAM, hAnow, hnow]
      by_cases hxt : x = t.core.name
      · -- the started transition: off after its start, newly armed if enabled after the firing
        subst hxt
        obtain rfl : t = u := Option.some.inj ((findT_of_mem hN ht).symm.trans hfx')
        have hoffA : sA.st t.core.name = .off := by
          have h5t : s₅.st t.core.name = .off := by
            rw [hs5]
            show unreap C (e.map Prod.fst) (unreap C (inPlaces t ++ t.core.resets)
              (afterStart refXPol C s₁ t)) t.core.name = _
            exact unreap_off (unreap_off (by unfold afterStart; simp))
          rcases hLst t.core.name with h | ⟨h, -⟩
          · rw [h, h5t]
          · exact h
        rw [hoffA]
        unfold restampW
        have ha' : (viewAt s s.cyc).armed t = true := ha
        simp only [refPolicy, ha', bne_self_eq_false, Bool.and_false, Bool.false_and,
          Bool.true_or, Bool.and_true]
        cases enabledNA (qCount (qFire s.M t e)) t.core <;> simp [updOf, stampOf, viewAt]
      · -- another transition: `status_agrees`
        have hpre : s₅.st x = preOf (s.st x) (enabledNA (mid t (qCount s.M)) u.core)
            (writesArc t (e.map Prod.fst) u) := by
          rw [hs5]
          show unreap C (e.map Prod.fst) (unreap C (inPlaces t ++ t.core.resets)
            (afterStart refXPol C s₁ t)) x = _
          rw [pre_status hfx' hxt, liveAfter_of_delta_zero hd1, hs1M, qCount_qConsume, hs1st]
        have hupd : updOf (sA.st x) (enabledNA (qCount (qFire s.M t e)) u.core) s.cyc =
            updOf (s₅.st x) (enabledNA (qCount (qFire s.M t e)) u.core) s.cyc := by
          rcases hLst x with h | ⟨h, u', hu', hu'x, hnot⟩
          · rw [h]
          · -- a recheck loser: armed at the start, disabled by the start's consumption
            rw [hord5] at hu'
            obtain ⟨hu'n, hr'⟩ := mem_readyOrder
              (show u' ∈ readyOrder C s by rw [ho]; exact List.mem_cons_of_mem _ hu')
            obtain rfl : u' = u := by
              have := findT_of_mem hN hu'n
              rw [hu'x, hfx'] at this
              exact (Option.some.inj this).symm
            have hsome : (stampOf (s.st x)).isSome = true := by
              have := hr'.1.2
              simpa [viewAt, hu'x] using this
            rw [hvis5] at hnot
            rw [h, hpre]
            cases hsx : s.st x with
            | off => simp [hsx, stampOf] at hsome
            | reaped => simp [hsx, stampOf] at hsome
            | armed k r =>
              cases r with
              | true => exact absurd hsx (hnr x k)
              | false =>
                cases he1 : enabledNA (mid t (qCount s.M)) u'.core
                · simp only [preOf]
                  exact updOf_off_eq k _ _
                · rw [hpre, hsx] at hnot
                  simp [preOf, he1, stampOf] at hnot
        rw [hupd, hpre]
        have hharm : ((viewAt s s.cyc).stamp u.core.name).isSome = true →
            enabledNA (viewAt s s.cyc).m u.core = true := fun h' =>
          hI1 u.core.name u (findT_of_mem hN hu) h'
        rw [restampW_ref (X := C.X) (t := t) (d := e.map Prod.fst) (m' := qCount (qFire s.M t e))
          (by rw [hux]; exact hxt) hharm]
        have hoff' : s.st x = .off → enabledNA (qCount (qFire s.M t e)) u.core = true →
            writesArc t (e.map Prod.fst) u = true := by
          intro hso he2
          cases hw : writesArc t (e.map Prod.fst) u
          · rw [qCount_qFire, enabled_of_not_writesArc _ hw] at he2
            have := (hI2 x u hfx' hso he2).1
            simp [inFlightN, hfl] at this
          · rfl
        have hag := status_agrees (s.st x) (enabledNA (mid t (qCount s.M)) u.core)
          (writesArc t (e.map Prod.fst) u) (enabledNA (qCount (qFire s.M t e)) u.core) s.cyc
          (hnr x) hoff'
        simp only [stepStatus] at hag
        rw [hag]
        simp only [viewAt, hux]
  rw [hview]
  exact RefTStepW.fire C.X _ t _ _ ht ⟨hen0, hoff, qCount_qFire s.M t e⟩ ha hg hx

/-! ### Delays and the deadline step -/

/-- **L3, delay**: a delay is a `RefTStep` delay of the present view (`viewAt s s.now`). -/
theorem delay_view {C : Cfg N T} {s s' : XSt N T} {δ : Nat} (h : RefExec C s (.delay δ) s') :
    RefTStep C.X (viewAt s s.now) (.delay δ) (viewAt s' s'.now) := by
  cases xstepW_delay h
  exact RefTStepW.delay C.X (viewAt s s.now) δ

/-- One reap step of the timed reference, of some transition. -/
def ReapStep (X : TimedNet N) (v v' : TSt N) : Prop := ∃ t, RefTStep X v (.reap t) v'

/-- Reaping a list of expired transitions with distinct names, one at a time: each stays expired
until its own reap, since a reap removes only its own stamp. -/
theorem reaps_of_list {X : TimedNet N} :
    ∀ (L : List (Trans N)) (v : TSt N), (∀ u ∈ L, u ∈ X.net.transitions) →
      (L.map (·.core.name)).Nodup → (∀ u ∈ L, tExpired X v u = true) →
      Relation.ReflTransGen (ReapStep X) v
        { v with stamp := fun x => if x ∈ L.map (·.core.name) then none else v.stamp x }
  | [], v, _, _, _ => by
    simp only [List.map_nil, List.not_mem_nil, if_false]
    exact .refl
  | u :: L, v, hin, hnd, hx => by
    let v₁ : TSt N := { v with stamp := fun x => if x = u.core.name then none else v.stamp x }
    have h1 : ReapStep X v v₁ :=
      ⟨u, RefTStepW.reap X v u (hin u List.mem_cons_self) (hx u List.mem_cons_self)⟩
    rw [List.map_cons, List.nodup_cons] at hnd
    have hx' : ∀ u' ∈ L, tExpired X v₁ u' = true := by
      intro u' hu'
      have hne : u'.core.name ≠ u.core.name := fun he =>
        hnd.1 (he ▸ List.mem_map_of_mem hu')
      have : tExpired X v₁ u' = tExpired X v u' := by
        unfold tExpired TSt.armed TSt.elapsed
        simp only [v₁, if_neg hne]
      rw [this]
      exact hx u' (List.mem_cons_of_mem _ hu')
    have ih := reaps_of_list L v₁ (fun u' hu' => hin u' (List.mem_cons_of_mem _ hu')) hnd.2 hx'
    have he : ({ v₁ with stamp := fun x => if x ∈ L.map (·.core.name) then none else v₁.stamp x }
        : TSt N) = { v with stamp := fun x =>
          if x ∈ (u :: L).map (·.core.name) then none else v.stamp x } := by
      simp only [v₁, List.map_cons, List.mem_cons]
      congr 1
      funext x
      by_cases h1 : x = u.core.name <;> by_cases h2 : x ∈ L.map (·.core.name) <;> simp [h1, h2]
    exact .head h1 (he ▸ ih)

/-- **L3, deadline**: the deadline step is a `RefTStep` delay of the clock view from the update's
reading to the deadline step's reading (ruling D61 (c): never earlier), followed by a sequence of
`RefTStep` reaps, one per transition expired at that reading (distinct names). -/
theorem deadline_reaps {C : Cfg N T} (hN : NamesDistinct C.X) {s s' : XSt N T}
    {ns : List String} (h : RefExec C s (.deadline ns) s') :
    s.cyc ≤ s'.cyc ∧ RefTStep C.X (viewAt s s.cyc) (.delay (s'.cyc - s.cyc)) (viewAt s s'.cyc) ∧
      Relation.ReflTransGen (ReapStep C.X) (viewAt s s'.cyc) (viewAt s' s'.cyc) := by
  obtain ⟨-, -, hns, rfl⟩ := xstepW_deadline h
  refine ⟨Nat.le_max_left _ _, ?_, ?_⟩
  · have hd := RefTStepW.delay (P := refPolicy) C.X (viewAt s s.cyc) (max s.cyc s.now - s.cyc)
    have he : (viewAt s s.cyc).now + (max s.cyc s.now - s.cyc) = max s.cyc s.now := by
      simp only [viewAt]; omega
    simp only [he] at hd
    exact hd
  let L := C.X.net.transitions.filter (expiredAt refXPol C (atDeadline s))
  have hr := reaps_of_list (X := C.X) L (viewAt s (max s.cyc s.now))
    (fun u hu => (List.mem_filter.mp hu).1)
    ((List.Sublist.map _ List.filter_sublist).nodup hN)
    (fun u hu => (expiredAt_ref C (atDeadline s) u).symm ▸ (List.mem_filter.mp hu).2)
  have hns' : ns = L.map (·.core.name) := hns
  convert hr using 1
  show (⟨qCount s.M, max s.cyc s.now,
      fun x => stampOf (if ns.contains x = true then .reaped else s.st x)⟩ : TSt N) = _
  simp only [viewAt]
  congr 1
  funext x
  rw [← hns']
  by_cases hx : x ∈ ns <;> simp [hx, stampOf]

/-! ### Two invariants of the cycle: no restart flag at the boundaries, nothing overdue in the
pass -/

/-- No name holds the [TIME-012] restart flag: the update clears every flag, and only a start
sets one. -/
def NoRestart (s : XSt N T) : Prop := ∀ x k, s.st x ≠ .armed k true

/-- No transition of the net holds a stamp that is past its latest bound plus the tolerance at
the cycle reading, for a reapable timing: the deadline step reaped every expired transition, and
nothing since gave a name an older stamp. -/
def NoOverdue (C : Cfg N T) (s : XSt N T) : Prop :=
  ∀ u ∈ C.X.net.transitions, ∀ k, stampOf (s.st u.core.name) = some k →
    ¬ ((C.X.timing u).reapable = true ∧ (C.X.timing u).latest + C.X.tol < s.cyc - k)

/-- The termination test and the pass. -/
def inPass : Phase → Bool
  | .test | .pass => true
  | _ => false

omit [DecidableEq N] in
/-- With nothing overdue, no transition of the net is expired at the cycle reading. -/
theorem not_expired_of_noOverdue {C : Cfg N T} {s : XSt N T} (h : NoOverdue C s) {u : Trans N}
    (hu : u ∈ C.X.net.transitions) : tExpired C.X (viewAt s s.cyc) u = false := by
  cases hs : stampOf (s.st u.core.name) with
  | none => simp [tExpired, TSt.armed, viewAt, hs]
  | some k =>
    have := h u hu k hs
    simp only [tExpired, TSt.armed, TSt.elapsed, viewAt, hs, Option.isSome_some, Option.getD_some,
      Bool.and_true, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    by_cases hr : (C.X.timing u).reapable = true
    · exact Or.inr fun hlt => this ⟨hr, hlt⟩
    · exact Or.inl (Or.inl (by simpa using hr))

/-- `unreap` keeps every stamp it leaves. -/
theorem stampOf_unreap {C : Cfg N T} {ps : List N} {st : String → Status} {x : String}
    {k : Nat} (h : stampOf (unreap C ps st x) = some k) : stampOf (st x) = some k := by
  unfold unreap at h
  cases hs : st x <;> cases hf : findT C x <;> simp only [hs, hf] at h <;> try exact h
  split at h <;> simp [stampOf] at h

/-- A start keeps every stamp it leaves (the restart flag keeps the old stamp until the update). -/
theorem stampOf_afterStart {P : XPol N T} {C : Cfg N T} {s : XSt N T} {t : Trans N}
    {x : String} {k : Nat} (h : stampOf (afterStart P C s t x) = some k) :
    stampOf (s.st x) = some k := by
  unfold afterStart at h
  split at h
  · simp [stampOf] at h
  · split at h
    · rename_i k' r u _ hs _
      rw [hs]
      split at h <;> simpa [stampOf] using h
    · assumption

omit [DecidableEq N] in
/-- Nothing overdue survives a step that keeps the cycle reading and only keeps or drops stamps.
-/
theorem noOverdue_mono {C : Cfg N T} {s s' : XSt N T} (hc : s'.cyc = s.cyc)
    (hst : ∀ x k, stampOf (s'.st x) = some k → stampOf (s.st x) = some k) (h : NoOverdue C s) :
    NoOverdue C s' := by
  intro u hu k hk
  rw [hc]
  exact h u hu k (hst _ k hk)

/-- The update leaves no restart flag. -/
theorem updSt_noRestart {C : Cfg N T} {s : XSt N T} (x : String) (k : Nat) :
    updSt refXPol C s x ≠ .armed k true := by
  unfold updSt
  cases findT C x with
  | none => simp
  | some u =>
    simp only [refXPol]
    cases s.st x with
    | armed k' rs => cases rs <;> split_ifs <;> simp
    | off => split_ifs <;> simp
    | reaped => simp

/-- The reference executor's invariant for L3 and L7: `InvX`, no restart flag at the phase
boundaries, nothing overdue in the termination test and the pass. -/
def InvR (C : Cfg N T) (s : XSt N T) : Prop :=
  InvX C s ∧ (isBoundary s.phase = true → NoRestart s) ∧
    (inPass s.phase = true → NoOverdue C s)

omit [DecidableEq N] in
/-- The phase after a settle step that stays in the termination test or the pass. -/
theorem settle_phase {C : Cfg N T} {s : XSt N T} {i : Nat} {f : Firing N T}
    (hc : canSettle C s i f = true) (hp : inPass (settle s i).phase = true) :
    s.phase = .pass ∧ (settle s i).phase = .pass := by
  unfold canSettle settleOk at hc
  simp only [Bool.and_eq_true] at hc
  have h2 := hc.2
  simp only [settle] at hp ⊢
  revert h2 hp
  cases s.phase <;> simp [inPass]

/-- Every step of the reference executor keeps `InvR` (distinct names). -/
theorem invR_step {C : Cfg N T} (hN : NamesDistinct C.X) {s s' : XSt N T} {l : XLbl N T}
    (h : xstep C s l = some s') (hi : InvR C s) : InvR C s' := by
  obtain ⟨hx, hnr, hno⟩ := hi
  refine ⟨invX_step hN h hx, ?_⟩
  -- steps that keep the phase, the statuses and the cycle reading
  have keep : s'.phase = s.phase → s'.st = s.st → s'.cyc = s.cyc →
      (isBoundary s'.phase = true → NoRestart s') ∧ (inPass s'.phase = true → NoOverdue C s') :=
    fun hp hs hc => ⟨fun hb x k => by rw [hs]; exact hnr (hp ▸ hb) x k,
      fun hq => noOverdue_mono hc (fun x k hk => by rwa [hs] at hk) (hno (hp ▸ hq))⟩
  -- steps that leave both sets of phases
  have leave : isBoundary s'.phase = false → inPass s'.phase = false →
      (isBoundary s'.phase = true → NoRestart s') ∧ (inPass s'.phase = true → NoOverdue C s') :=
    fun h1 h2 => ⟨fun h => by simp [h1] at h, fun h => by simp [h2] at h⟩
  cases l with
  | delay δ => cases xstepW_delay h; exact keep rfl rfl rfl
  | write i p x => obtain ⟨f, -, -, rfl⟩ := writeStep_some h; exact keep rfl rfl rfl
  | flush i =>
    obtain ⟨f, -, -, -, -, ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ := flushStep_some h <;> exact keep rfl rfl rfl
  | ret i ok => obtain ⟨f, -, -, rfl⟩ := retStep_some h; exact keep rfl rfl rfl
  | expire i e => obtain ⟨f, -, -, -, -, -, rfl⟩ := expireStep_some h; exact keep rfl rfl rfl
  | request p x r =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := requestStep_some h <;> exact keep rfl rfl rfl
  | drain => obtain ⟨-, rfl⟩ := drainStep_some h; exact keep rfl rfl rfl
  | close => obtain ⟨-, rfl⟩ := closeStep_some h; exact keep rfl rfl rfl
  | terminateNow => obtain ⟨-, rfl⟩ := terminateStep_some h; exact keep rfl rfl rfl
  | commit i =>
    obtain ⟨f, e, -, -, hc, -, -, rfl⟩ := commitStep_some h
    refine ⟨fun hb => by simp [depositAt, canSettle_phase hc] at hb, fun hq => ?_⟩
    obtain ⟨hp, -⟩ := settle_phase hc hq
    exact noOverdue_mono (s := s) rfl (fun x k hk => stampOf_unreap hk) (hno (by simp [hp, inPass]))
  | tdeposit i =>
    obtain ⟨f, e, -, -, hc, -, rfl⟩ := tdepositStep_some h
    refine ⟨fun hb => by simp [depositAt, canSettle_phase hc] at hb, fun hq => ?_⟩
    obtain ⟨hp, -⟩ := settle_phase hc hq
    exact noOverdue_mono (s := s) rfl (fun x k hk => stampOf_unreap hk) (hno (by simp [hp, inPass]))
  | fail i =>
    obtain ⟨f, -, hc, -, rfl⟩ := failStep_some h
    refine ⟨fun hb => by simp [canSettle_phase hc] at hb, fun hq => ?_⟩
    obtain ⟨hp, -⟩ := settle_phase hc hq
    exact noOverdue_mono (s := s) rfl (fun x k hk => hk) (hno (by simp [hp, inPass]))
  | endCompletions =>
    obtain ⟨-, -, -, -, rfl⟩ := xstepW_endCompletions h; exact leave rfl rfl
  | publish i =>
    obtain ⟨b, rest, -, -, hph, rfl⟩ := publishStep_some h
    rcases hph with hp | ⟨hp, -⟩ <;> exact leave (by simp [hp, isBoundary]) (by simp [hp, inPass])
  | endPublications => obtain ⟨-, -, -, rfl⟩ := xstepW_endPublications h; exact leave rfl rfl
  | inject k =>
    obtain ⟨p, x, rest, -, -, -, hph, rfl⟩ := injectStep_some h
    rcases hph with hp | hp <;> exact leave (by simp [hp, isBoundary]) (by simp [hp, inPass])
  | discard k =>
    obtain ⟨p, x, rest, -, -, -, hph, rfl⟩ := discardStep_some h
    rcases hph with hp | hp <;> exact leave (by simp [hp, isBoundary]) (by simp [hp, inPass])
  | snapshot a => obtain ⟨-, -, -, rfl⟩ := snapshotStep_some h; exact keep rfl rfl rfl
  | endEvents => obtain ⟨-, -, -, rfl⟩ := xstepW_endEvents h; exact leave rfl rfl
  | update =>
    obtain ⟨-, -, rfl⟩ := xstepW_update h
    exact ⟨fun _ x k => updSt_noRestart x k, fun h => by simp [inPass] at h⟩
  | deadline ns =>
    obtain ⟨hph, -, hns, rfl⟩ := xstepW_deadline h
    have hnr0 := hnr (by simp [hph, isBoundary])
    obtain ⟨h1, -⟩ := hx.2.2 (by simp [hph, isBoundary])
    refine ⟨fun _ x k => ?_, fun _ u hu k hk => ?_⟩
    · show (if ns.contains x = true then Status.reaped else s.st x) ≠ _
      split
      · simp
      · exact hnr0 x k
    · change stampOf (if ns.contains u.core.name = true then Status.reaped else s.st u.core.name)
        = some k at hk
      split at hk
      · simp [stampOf] at hk
      · rename_i hnot
        rintro ⟨hr, hlt⟩
        apply hnot
        have hen := h1 u.core.name u (findT_of_mem hN hu) (by rw [hk]; rfl)
        have hexp : expiredAt refXPol C (atDeadline s) u = true := by
          rw [expiredAt_ref]
          simp [tExpired, TSt.armed, TSt.elapsed, viewAt, atDeadline, hk, hr, hen, hlt]
        rw [hns]
        simp only [expiredNames, List.contains_iff_mem, List.mem_map, List.mem_filter]
        exact ⟨u, ⟨hu, hexp⟩, rfl⟩
  | finish c =>
    cases c with
    | quiescent => obtain ⟨-, -, -, rfl⟩ := xstepW_finishQuiescent h; exact leave rfl rfl
    | closed => obtain ⟨-, -, -, -, rfl⟩ := xstepW_finishClosed h; exact leave rfl rfl
    | terminal => obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h; exact leave rfl rfl
    | stopped => obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h; exact leave rfl rfl
  | begin =>
    obtain ⟨hph, -, -, -, rfl⟩ := xstepW_begin h
    exact ⟨fun h => by simp [isBoundary] at h,
      fun _ => noOverdue_mono (s := s) rfl (fun _ _ hk => hk) (hno (by simp [hph, inPass]))⟩
  | start n sy =>
    obtain ⟨t, rest, -, hph, -, -, -, -, -, rfl⟩ := startStep_some h
    exact ⟨fun h => by simp [hph, isBoundary] at h,
      fun _ => noOverdue_mono (s := s) rfl (fun _ _ hk => stampOf_afterStart (stampOf_unreap hk))
        (hno (by simp [hph, inPass]))⟩
  | lose n =>
    obtain ⟨t, rest, -, hph, -, -, -, -, rfl⟩ := loseStep_some h
    refine ⟨fun h => by simp [hph, isBoundary] at h,
      fun _ => noOverdue_mono (s := s) rfl (fun x k hk => ?_) (hno (by simp [hph, inPass]))⟩
    change stampOf (if x = n then Status.off else s.st x) = some k at hk
    split at hk
    · simp [stampOf] at hk
    · exact hk
  | endPass =>
    obtain ⟨-, -, -, -, rfl⟩ := xstepW_endPass h
    exact leave (by split <;> rfl) (by split <;> rfl)
  | park tmr =>
    obtain ⟨hph, -, -, -, -, -, -, -, rfl⟩ := parkStep_some h
    exact leave (by simp [hph, isBoundary]) (by simp [hph, inPass])
  | wake => obtain ⟨-, -, rfl⟩ := wakeStep_some h; exact leave rfl rfl

omit [DecidableEq N] in
/-- The initial state meets `InvR`. -/
theorem invR_xinit (C : Cfg N T) (M0 : QMarking N T) (r0 : Nat) : InvR C (xinit M0 r0) :=
  ⟨invX_xinit C M0 r0, fun h => by simp [xinit, isBoundary] at h,
    fun h => by simp [xinit, inPass] at h⟩

/-- Every run of the reference executor keeps `InvR`. -/
theorem invR_xrun {C : Cfg N T} (hN : NamesDistinct C.X) :
    ∀ {s s' : XSt N T} {ls : List (XLbl N T)}, xrun C s ls = some s' → InvR C s → InvR C s'
  | s, s', [], h, hi => by cases h; exact hi
  | s, s', l :: ls, h, hi => by
    obtain ⟨s₁, h1, h2⟩ := xrun_cons.mp h
    exact invR_xrun hN h2 (invR_step hN h1 hi)

/-- **No restart flag at the phase boundaries**, in every reachable state. -/
theorem noRestart_reachable {C : Cfg N T} (hN : NamesDistinct C.X) {M0 : QMarking N T}
    {r0 : Nat} {ls : List (XLbl N T)} {s : XSt N T} (h : xrun C (xinit M0 r0) ls = some s)
    (hb : s.phase = .deadline ∨ s.phase = .test) : NoRestart s :=
  (invR_xrun hN h (invR_xinit C M0 r0)).2.1 (by rcases hb with hb | hb <;> simp [hb, isBoundary])

/-! ## L7: no refresh rescue -/

/-- **L7** (`no_start_while_expired`): in every reachable state where a transition starts, no
transition of the net is expired at the cycle reading. The deadline step reaps the full expired
set at the reading the pass judges at, and nothing in the termination test or the pass gives a
name an older stamp. So the refresh rescue of `ClashesTime.clash013_refresh_rescue` (a refresh
transition firing first and restarting an expired transition's clock) is not a run of the
executor. -/
theorem no_start_while_expired {C : Cfg N T} (hN : NamesDistinct C.X) {M0 : QMarking N T}
    {r0 : Nat} {ls : List (XLbl N T)} {s s' : XSt N T} {n : String} {sy : Bool}
    (h : xrun C (xinit M0 r0) ls = some s) (hs : RefExec C s (.start n sy) s') :
    ∀ u ∈ C.X.net.transitions, tExpired C.X (viewAt s s.cyc) u = false := by
  obtain ⟨-, -, -, hph, -⟩ := startStep_some (P := refXPol) hs
  have hno := (invR_xrun hN h (invR_xinit C M0 r0)).2.2 (by simp [hph, inPass])
  exact fun u hu => not_expired_of_noOverdue hno hu

/-- In every reachable state at the termination test, no transition of the net is expired at the
cycle reading: the source view of every L3 segment from a reachable state has nothing to reap. -/
theorem noExpired_at_test {C : Cfg N T} (hN : NamesDistinct C.X) {M0 : QMarking N T}
    {r0 : Nat} {ls : List (XLbl N T)} {s : XSt N T} (h : xrun C (xinit M0 r0) ls = some s)
    (hph : s.phase = .test) :
    ∀ u ∈ C.X.net.transitions, tExpired C.X (viewAt s s.cyc) u = false := by
  have hno := (invR_xrun hN h (invR_xinit C M0 r0)).2.2 (by simp [hph, inPass])
  exact fun u hu => not_expired_of_noOverdue hno hu

/-- **L3 on reachable states**: from a state at the termination test that a run from an initial
state reaches, with no firing in flight and the cycle reading equal to the present, the atomic
segment is one `RefTStep` firing between the clock views. `InvU` and the absence of restart
flags come from the run (`invU_boundary`, `noRestart_reachable`). -/
theorem atomic_refTStep_reachable {C : Cfg N T} (hW : C.WF) {M0 : QMarking N T} {r0 : Nat}
    {ls : List (XLbl N T)} {s s' : XSt N T} {n : String} {i : Nat} {e : List (N × T)}
    {lose : List String} (hr : xrun C (xinit M0 r0) ls = some s) (hph : s.phase = .test)
    (hfl : s.fl = []) (hnow : s.now = s.cyc)
    (h : xrun C s (atomicLabels n i e lose) = some s') :
    ∃ t ∈ C.X.net.transitions, t.core.name = n ∧ s'.M = qFire s.M t e ∧
      ((∃ ch, deposit (nconsumed (qCount s.M) t.core) t.out ch = some (e.map Prod.fst)) →
        RefTStep C.X (viewAt s s.cyc) (.fire t (e.map Prod.fst)) (viewAt s' s'.cyc)) :=
  atomic_refTStep hW.names (invU_boundary hW.names hr (Or.inr hph)) hfl hnow
    (noRestart_reachable hW.names hr (Or.inr hph)) h

/-! ## L9: the dirty set -/

/-- A name of the net is **clean** in state `s` when re-evaluating it would change nothing: it
holds no restart flag, and its status says what `InvU` says about its transition's enablement
(armed only if enabled; off and enabled only while a firing of it is in flight under
`¬reentrant`; reaped only if enabled). -/
def CleanAt (C : Cfg N T) (s : XSt N T) (x : String) : Prop :=
  (∀ k, s.st x ≠ .armed k true) ∧ ∀ u, findT C x = some u →
    ((stampOf (s.st x)).isSome = true → enabledNA (qCount s.M) u.core = true) ∧
    (s.st x = .off → enabledNA (qCount s.M) u.core = true →
      inFlightN s x = true ∧ C.reentrant = false) ∧
    (s.st x = .reaped → enabledNA (qCount s.M) u.core = true)

/-- The update leaves a clean name as it is. -/
theorem updSt_clean {C : Cfg N T} {s : XSt N T} {x : String} {u : Trans N}
    (hf : findT C x = some u) (h : CleanAt C s x) : updSt refXPol C s x = s.st x := by
  obtain ⟨hnr, hc⟩ := h
  obtain ⟨h1, h2, -⟩ := hc u hf
  unfold updSt
  rw [hf]
  simp only [refXPol]
  cases hs : s.st x with
  | armed k rs =>
    cases rs with
    | true => exact absurd hs (hnr k)
    | false =>
      have := h1 (by simp [hs, stampOf])
      simp [this]
  | off =>
    by_cases he : enabledNA (qCount s.M) u.core = true
    · obtain ⟨hfl, hre⟩ := h2 hs he
      simp [hfl, hre]
    · simp [he]
  | reaped => rfl

/-- The update of only the names `D` marks dirty; every other name keeps its status (Rust's
`dirty_set` of the bitmap backend). -/
def updDirty (P : XPol N T) (C : Cfg N T) (s : XSt N T) (D : String → Bool) :
    String → Status :=
  fun x => if D x then updSt P C s x else s.st x

/-- **L9**: on the names of the net, the reference update (every name re-evaluated) equals the
update of any dirty set that holds every name that is not clean. -/
theorem updSt_eq_updDirty {C : Cfg N T} {s : XSt N T} {D : String → Bool}
    (hD : ∀ x, ¬ CleanAt C s x → D x = true) :
    ∀ x u, findT C x = some u → updSt refXPol C s x = updDirty refXPol C s D x := by
  intro x u hf
  unfold updDirty
  split
  · rfl
  · rename_i hx
    by_cases hc : CleanAt C s x
    · exact updSt_clean hf hc
    · exact absurd (hD x hc) hx

omit [DecidableEq N] in
/-- **L9, which names are clean**: from a phase boundary with `InvU` and no restart flag, a name
stays clean as long as its status, the counts of its transition's arc places and whether a
firing of it is in flight are unchanged. So a dirty set that holds every name with a written arc
place (a count change needs a write), every name whose status a step changed (a start, a recheck
loser, an end of a reap) and every name whose firing settled is enough. -/
theorem cleanAt_of_frame {C : Cfg N T} {s₀ s : XSt N T} {x : String} (hinv : InvU C s₀)
    (hnr : NoRestart s₀) (hst : s.st x = s₀.st x)
    (hcnt : ∀ u, findT C x = some u → ∀ p ∈ arcPlaces u, qCount s.M p = qCount s₀.M p)
    (hfl : inFlightN s x = inFlightN s₀ x) : CleanAt C s x := by
  obtain ⟨h1, h2, h3⟩ := hinv
  refine ⟨fun k => by rw [hst]; exact hnr x k, fun u hf => ?_⟩
  have he : enabledNA (qCount s.M) u.core = enabledNA (qCount s₀.M) u.core :=
    enabledNA_congr (hcnt u hf)
  rw [he, hst, hfl]
  exact ⟨h1 x u hf, h2 x u hf, h3 x u hf⟩

/-- **L9, losers are written**: a name that loses the pass recheck while it holds a stamp was
not enabled on the pass-visible marking; if its transition was enabled on a marking `m₀` (the
update's, where the pass order found it armed), one of its arc places has a different count on
the pass-visible marking. Rust's `disable` writes nothing, and the loser is dirty because the
consumption that disabled it wrote that place. -/
theorem lose_written {C : Cfg N T} {s s' : XSt N T} {x : String} (h : RefExec C s (.lose x) s')
    (hst : (stampOf (s.st x)).isSome = true) :
    ∃ t, s.order.head? = some t ∧ t.core.name = x ∧ ∀ m₀ : N → Nat,
      enabledNA m₀ t.core = true → ∃ p ∈ arcPlaces t, qCount (vis s) p ≠ m₀ p := by
  obtain ⟨t, rest, ho, -, -, -, hn, hng, -⟩ := loseStep_some (P := refXPol) h
  refine ⟨t, by simp [ho], hn, fun m₀ hen => ?_⟩
  by_cases hall : ∀ p ∈ arcPlaces t, qCount (vis s) p = m₀ p
  · refine absurd ⟨hst, ?_⟩ hng
    show enabledNA (qCount (vis s)) t.core = true
    rw [enabledNA_congr hall]
    exact hen
  · simpa using hall

/-! ## L11: the initial state -/

/-- The labels from the initial state to its first update: the empty steps 1, 1b and 2, then the
update. -/
def initLabels : List (XLbl N T) := [.endCompletions, .endPublications, .endEvents, .update]

/-- **L11**: the first update from the initial state `xinit M0 r0` arms exactly what `M0`
enables, stamped `r0`: its clock view is the initial state of the timed reference step
(`TSt.init`, [TIME-010] "newly armed when it is enabled in the initial marking"; design R19). -/
theorem init_update_eq_TSt_init (C : Cfg N T) (M0 : QMarking N T) (r0 : Nat) {s : XSt N T}
    (h : xrun C (xinit M0 r0) initLabels = some s) :
    viewAt s s.cyc = TSt.init C.X (qCount M0) r0 := by
  obtain ⟨s₁, h1, h⟩ := xrun_cons.mp h
  obtain ⟨-, -, -, -, rfl⟩ := xstepW_endCompletions h1
  obtain ⟨s₂, h2, h⟩ := xrun_cons.mp h
  obtain ⟨-, -, -, rfl⟩ := xstepW_endPublications h2
  obtain ⟨s₃, h3, h⟩ := xrun_cons.mp h
  obtain ⟨-, -, -, rfl⟩ := xstepW_endEvents h3
  obtain ⟨s₄, h4, h⟩ := xrun_cons.mp h
  obtain ⟨-, -, rfl⟩ := xstepW_update h4
  cases h
  simp only [viewAt, TSt.init]
  congr 1
  funext n
  show stampOf (updSt refXPol C _ n) = _
  unfold updSt findT
  cases hf : C.X.net.transitions.find? (·.core.name == n) with
  | none => rfl
  | some u =>
    by_cases he : enabledNA (qCount M0) u.core = true <;>
      simp [he, xinit, stampOf, inFlightN, refXPol]

/-- The first update exists whenever no terminal place is marked at the start. -/
theorem init_update_exists (C : Cfg N T) (M0 : QMarking N T) (r0 : Nat)
    (hl : liveB C (xinit M0 r0) = true) : ∃ s, xrun C (xinit M0 r0) initLabels = some s := by
  simp only [xinit, liveB] at hl
  simp only [initLabels, xrun, xstep, xstepW, xinit, liveB, hl, List.isEmpty_nil,
    Bool.true_and, decide_true, ↓reduceIte, Option.bind_some, Bool.and_self, bne_iff_ne, ne_eq,
    reduceCtorEq, not_false_eq_true]
  exact ⟨_, rfl⟩

/-! ## L10: the executor's reaped status is Phase 1's Reaped -/

omit [DecidableEq N] in
/-- **L10**: under `InvU`, the executor's reaped status of a transition of the net is the Phase
1 term Reaped of the clock view (enabled and not armed), when no firing of it is in flight or the
executor is re-entrant. With a firing in flight under `¬reentrant` the name is off while enabled
([CONC-002] line 3a), which the clock view also reads as Reaped. -/
theorem reapedE_iff_reaped {C : Cfg N T} {s : XSt N T} {u : Trans N} (hinv : InvU C s)
    (hu : findT C u.core.name = some u)
    (hfl : inFlightN s u.core.name = false ∨ C.reentrant = true) :
    ReapedE s u ↔ Reaped (viewAt s s.cyc) u := by
  obtain ⟨h1, h2, h3⟩ := hinv
  simp only [ReapedE, Reaped, Armed, Enabled, viewAt]
  constructor
  · intro hr
    exact ⟨h3 _ u hu hr, fun ⟨_, hs⟩ => by simp [hr, stampOf] at hs⟩
  · rintro ⟨he, hna⟩
    cases hs : s.st u.core.name with
    | reaped => rfl
    | armed k r => exact absurd ⟨he, by simp [hs, stampOf]⟩ hna
    | off =>
      obtain ⟨hf, hre⟩ := h2 _ u hu hs he
      rcases hfl with hfl | hfl
      · simp [hf] at hfl
      · simp [hre] at hfl

/-- **L10 on reachable states**: at the termination test of a run from an initial state, with
the build-time well-formedness. -/
theorem reapedE_iff_reaped_reachable {C : Cfg N T} (hW : C.WF) {M0 : QMarking N T} {r0 : Nat}
    {ls : List (XLbl N T)} {s : XSt N T} (h : xrun C (xinit M0 r0) ls = some s)
    (hb : s.phase = .deadline ∨ s.phase = .test) {u : Trans N} (hu : u ∈ C.X.net.transitions)
    (hfl : inFlightN s u.core.name = false ∨ C.reentrant = true) :
    ReapedE s u ↔ Reaped (viewAt s s.cyc) u :=
  reapedE_iff_reaped (invU_boundary hW.names h hb) ((inNet_iff_mem hW.names u).mpr hu) hfl

end Libpetri.Reference

/-! ## The agreement conjuncts -/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

variable {N T : Type} [DecidableEq N]

/-- **Queue agreement** (consistency theorem only; link L2): on every segment of `E` from a pass
state with no same-pass deposit that starts the head `t` of the order as a fresh firing `i`,
then takes steps that leave the marking alone, then commits firing `i` with the record `f` and
emission `e` it finds, the record is `t`'s with the tokens the queue firing of `t` from the
start's marking delivers, and the segment is a step of `Q` from that marking to the marking after
the commit when the emission is offered. -/
def QueueAgrees (E : XRel N T) (Q : QFireRel N T) : Prop :=
  ∀ (C : Cfg N T) (s s₁ s' : XSt N T) (n : String) (sy : Bool) (mid : List (XLbl N T)) (i : Nat)
    (f : Firing N T) (e : List (N × T)),
    (∀ p, s.delta p = 0) → (∀ g ∈ s.fl, g.id ≠ s.nextId) → (∀ l ∈ mid, l.marks = false) →
    i = s.nextId → XRunL E C s (.start n sy :: mid) s₁ → E C s₁ (.commit i) s' →
    s₁.fl.find? (·.id == i) = some f → f.out = some (.ok e) →
    ∃ t, s.order.head? = some t ∧ t.core.name = n ∧ f.t = t ∧ f.deliv = qDelivered s.M t ∧
      (OfferedEmission s t e → Q t s.M f.deliv e s'.M)

/-- **Atomic agreement** (consistency theorem only; link L3): every delay of `E` is a delay of
`R` on the present view; every deadline step is a sequence of reaps of `R` on the clock view; and
every atomic segment (`atomicLabels`) from a state with `InvU`, no firing in flight, no restart
flag and the cycle reading equal to the present is one firing of `R` on the clock view, when the
emission's places are an offered deposit. Every clause takes the build-time well-formedness
`C.WF` where it needs it (design R13). -/
def AtomicAgrees (E : XRel N T) (R : TimedNet N → TSt N → TLbl N → TSt N → Prop) : Prop :=
  (∀ C s δ s', E C s (.delay δ) s' → R C.X (viewAt s s.now) (.delay δ) (viewAt s' s'.now)) ∧
  (∀ C s ns s', C.WF → E C s (.deadline ns) s' →
    ∃ v, R C.X (viewAt s s.cyc) (.delay (s'.cyc - s.cyc)) v ∧
      Relation.ReflTransGen (fun v v' => ∃ t, R C.X v (.reap t) v') v (viewAt s' s'.cyc)) ∧
  (∀ C s s' n i e ls, C.WF → InvU C s → s.fl = [] → s.now = s.cyc → NoRestart s →
    XRunL E C s (atomicLabels n i e ls) s' →
    ∃ t ∈ C.X.net.transitions, t.core.name = n ∧
      ((∃ ch, deposit (nconsumed (qCount s.M) t.core) t.out ch = some (e.map Prod.fst)) →
        R C.X (viewAt s s.cyc) (.fire t (e.map Prod.fst)) (viewAt s' s'.cyc)))

/-- The reference executor agrees with the reference queue firing (L2). -/
theorem queueAgrees_ref : QueueAgrees (RefExec (N := N) (T := T)) RefQFire := by
  intro C s s₁ s' n sy mid i f e hd hfresh hmid hi hrun hc hf hout
  obtain ⟨t, ho, hn, hft, hfd, -, hq⟩ :=
    segment_refQFire_split (xrunL_ref.mp hrun) hc hf hout hd hmid hfresh hi
  exact ⟨t, ho, hn, hft, hfd, hq⟩

/-- The reference executor agrees with the timed reference step (L3). -/
theorem atomicAgrees_ref : AtomicAgrees (RefExec (N := N) (T := T)) RefTStep :=
  ⟨fun _ _ _ _ h => delay_view h,
   fun _ _ _ _ hW h => ⟨_, (deadline_reaps hW.names h).2.1, (deadline_reaps hW.names h).2.2⟩,
   fun _ _ _ _ _ _ _ hW hinv hfl hnow hnr hrun => by
     obtain ⟨t, ht, hn, -, hr⟩ := atomic_refTStep hW.names hinv hfl hnow hnr (xrunL_ref.mp hrun)
     exact ⟨t, ht, hn, hr⟩⟩

end Libpetri.Spec

namespace Libpetri.Reference

open Libpetri Libpetri.Spec Libpetri.Novel.Seam

/-! ## A decided atomic segment (the L3 premises are met on a real run) -/

/-- The example transition: one token from place 0, output `Place(1)`. -/
def linkT : Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 1) }

/-- The example configuration: `linkT` alone, immediate, no environment place, the reference
validator. -/
def linkC : Cfg Nat Nat :=
  { X := { net := { places := [0, 1], transitions := [linkT] }, timing := fun _ => .immediate,
           tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [], reentrant := false,
    validate := cfgValidate ioRefValidate, relay := fun _ _ _ => true,
    timeoutOut := fun _ _ _ => false, res := 0 }

/-- The example's initial marking: one token in place 0. -/
def linkM : QMarking Nat Nat := fun p => if p = 0 then [3] else []

/-- The labels from the initial state to the first termination test. -/
def linkPre : List (XLbl Nat Nat) := initLabels ++ [.deadline []]

/-- **Non-vacuity of L3**: a run from an initial state reaches a termination test with nothing
in flight and the cycle reading equal to the present, and the atomic segment of `linkT` writing
`7` into place 1 is a run from there. So `atomic_refTStep_reachable` applies to a real run. -/
theorem atomic_nonvacuous :
    ∃ s s', xrun linkC (xinit linkM 0) linkPre = some s ∧ s.phase = .test ∧ s.fl = [] ∧
      s.now = s.cyc ∧ xrun linkC s (atomicLabels "t" 0 [(1, 7)] []) = some s' ∧
      s'.M 1 = [7] := by
  have h1 : (xrun linkC (xinit linkM 0) linkPre).isSome = true := by decide
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp h1
  have h2 : (xrun linkC (xinit linkM 0) linkPre).map
      (fun s => (decide (s.phase = .test), s.fl.isEmpty, decide (s.now = s.cyc))) =
      some (true, true, true) := by decide
  have h3 : ((xrun linkC (xinit linkM 0) linkPre).bind fun s =>
      (xrun linkC s (atomicLabels "t" 0 [(1, 7)] [])).map (·.M 1)) = some [7] := by decide
  rw [hs] at h2 h3
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq,
    List.isEmpty_iff] at h2
  simp only [Option.bind_some] at h3
  obtain ⟨s', hs', hM⟩ : ∃ s', xrun linkC s (atomicLabels "t" 0 [(1, 7)] []) = some s' ∧
      s'.M 1 = [7] := by
    cases hx : xrun linkC s (atomicLabels "t" 0 [(1, 7)] []) with
    | none => rw [hx] at h3; simp at h3
    | some s' => rw [hx] at h3; exact ⟨s', rfl, by simpa using h3⟩
  exact ⟨s, s', hs, h2.1, h2.2.1, h2.2.2, hs', hM⟩

end Libpetri.Reference

namespace Libpetri.Reference

open Libpetri Libpetri.Spec Libpetri.Novel.Seam
open Libpetri.Reference.Link (toTransition toInSpec specAt_toTransition)

/-! ## Flat place identities: the count projection

The links below read the executor on flat place identities (`N = PlaceId`), where the Phase 1
nets of `InFlight`, `ReapAware`, `TerminalRewrite` and `EnvSemantics` live. A named transition
`u` is the flat transition `toTransition u.core` (`Reference/Link.lean`). -/

section Flat

variable {T : Type}

/-- Enablement of the flat transition is enablement of the named one. -/
theorem enabledA_toTransition (a : AMarking) (u : NTransition PlaceId) :
    enabledA a (toTransition u) = enabledNA a u := by
  simp only [enabledA, enabledNA, toTransition, List.all_map, Function.comp_def, toInSpec]
  rfl

/-- The flat firing with deposit `d` is the named firing with the deposit's counts. -/
theorem fireAD_toTransition (a : AMarking) (u : NTransition PlaceId) (d : List PlaceId) :
    Novel.ForwardDeposit.fireAD a (toTransition u) d = fireNC a u (depProd d) := by
  funext p
  unfold Novel.ForwardDeposit.fireAD consumeAllAt pre fireNC nconsumed
  rw [specAt_toTransition]
  have hr : (toTransition u).resets.contains p = decide (p ∈ u.resets) := by
    simp [toTransition]
  rw [hr]
  by_cases hres : p ∈ u.resets
  · simp [hres, depProd]
  · simp only [hres, decide_false, Bool.false_eq_true, if_false]
    cases hs : nspecAt u p with
    | none => simp [depProd]
    | some sp =>
      simp only [Option.map_some, toInSpec]
      by_cases hca : sp.card.consumesAll = true
      · simp [hca, depProd]
      · simp [hca, depProd]

/-- The start of a firing (`InFlight.startA`: inputs taken, drains and resets emptied) is the
intermediate marking of [TIME-012]. -/
theorem startA_toTransition (a : AMarking) (u : Trans PlaceId) :
    Novel.InFlight.startA a (toTransition u.core) = mid u a := by
  unfold Novel.InFlight.startA mid
  rw [fireAD_toTransition]
  congr 1

/-- A start never raises a count. -/
theorem startA_le (a : AMarking) (t : Transition) (p : PlaceId) :
    Novel.InFlight.startA a t p ≤ a p := by
  unfold Novel.InFlight.startA Novel.ForwardDeposit.fireAD
  simp only [List.count_nil]
  split_ifs <;> omega

/-- The places of an emission counted the flat way. -/
theorem count_map_fst (e : List (PlaceId × T)) (p : PlaceId) :
    (e.map Prod.fst).count p = countIn e p := by
  unfold countIn
  rw [List.count, List.countP_map, List.countP_eq_length_filter]
  rfl

/-- Appending an emission raises each count by the emission's count. -/
theorem qCount_qAppend (M : QMarking PlaceId T) (e : List (PlaceId × T)) (p : PlaceId) :
    qCount (qAppend M e) p = qCount M p + countIn e p := by
  simp only [qCount, qAppend_apply, List.length_append, countIn_eq]

/-- The firing with deposit `d` splits into its start and the deposit. -/
theorem fireNC_eq_mid_add (m : PlaceId → Nat) (u : Trans PlaceId) (d : List PlaceId)
    (p : PlaceId) : fireNC m u.core (depProd d) p = mid u m p + d.count p := by
  unfold mid fireNC depProd
  split_ifs <;> simp

/-- Adding a row at the end of the pending deposits. -/
theorem addAll_append_one (a : AMarking) (g : List Novel.InFlight.Row)
    (r : Novel.InFlight.Row) :
    Novel.InFlight.addAll a (g ++ [r]) = Novel.InFlight.addD (Novel.InFlight.addAll a g) r.2 := by
  funext p
  simp only [Novel.InFlight.addAll, Novel.InFlight.addD, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

/-- Adding rows is monotone in the base marking. -/
theorem addAll_mono {a b : AMarking} (h : ∀ p, a p ≤ b p) (g : List Novel.InFlight.Row)
    (p : PlaceId) : Novel.InFlight.addAll a g p ≤ Novel.InFlight.addAll b g p := by
  simp only [Novel.InFlight.addAll]
  have := h p
  omega

/-- No terminal place holds a token, read on a count marking. -/
abbrev NoTerm (C : Cfg PlaceId T) : AMarking → Prop :=
  Novel.TerminalRewrite.NoTerminal C.terminals

/-- A running executor's marking marks no terminal place. -/
theorem noTerm_of_liveB {C : Cfg PlaceId T} {s : XSt PlaceId T} (h : liveB C s = true) :
    NoTerm C (qCount s.M) := by
  intro p hp
  unfold liveB at h
  rw [List.all_eq_true] at h
  simpa [qCount] using h p hp

/-- Fewer tokens mark no more terminal places. -/
theorem noTerm_mono {C : Cfg PlaceId T} {a b : AMarking} (h : ∀ p, a p ≤ b p)
    (hb : NoTerm C b) : NoTerm C a := by
  intro p hp
  have := h p
  have := hb p hp
  omega

end Flat

/-! ## Two invariants of every run: the same-pass tail fits, identities are fresh -/

section Inv

variable {N T : Type} [DecidableEq N]

/-- The same-pass count of every place is at most its queue length. -/
def DeltaLe (s : XSt N T) : Prop := ∀ p, s.delta p ≤ (s.M p).length

/-- The identities of the firings in flight are distinct and below the supply. -/
def IdsFresh (s : XSt N T) : Prop :=
  (s.fl.map (·.id)).Nodup ∧ ∀ g ∈ s.fl, g.id < s.nextId

omit [DecidableEq N] in
/-- The length of the same-pass tail. -/
theorem hid_length {s : XSt N T} (hd : DeltaLe s) (p : N) : (hid s p).length = s.delta p := by
  simp only [hid, List.length_drop]
  have := hd p
  omega

omit [DecidableEq N] in
/-- The visible prefix and the tail add up to the queue. -/
theorem qCount_vis_add {s : XSt N T} (hd : DeltaLe s) (p : N) :
    qCount (vis s) p + s.delta p = qCount s.M p := by
  simp only [qCount, vis, List.length_take]
  have := hd p
  omega

/-- After a start the pass sees the consumed visible marking. -/
theorem vis_start {s s' : XSt N T} (hd : DeltaLe s) (t : Trans N) (hM : s'.M = liveAfter s t)
    (hD : s'.delta = s.delta) : vis s' = qConsume (vis s) t := by
  funext p
  simp only [vis, hM, hD, liveAfter, List.length_append, hid_length hd, Nat.add_sub_cancel]
  exact List.take_left' rfl

/-- A deposit inside the pass stays out of the visible marking. -/
theorem vis_depositAt_pass {C : Cfg N T} {s : XSt N T} {i : Nat} {e : List (N × T)}
    (hph : s.phase = .pass) (hd : DeltaLe s) : vis (depositAt C s i e) = vis s := by
  funext p
  simp only [vis, depositAt, settle, hph, if_true, qAppend_apply, List.length_append, countIn_eq]
  have h1 := hd p
  rw [show (s.M p).length + (qEmittedTo e p).length - (s.delta p + (qEmittedTo e p).length)
      = (s.M p).length - s.delta p by omega]
  exact List.take_append_of_le_length (by omega)

/-- The labels whose step leaves the marking, the same-pass counts, the pass order and the
firings in flight as they are, and enters no firing pass: every label but a start, a lose, a
settle, a publication, an injection and the two ends of the pass. -/
def _root_.Libpetri.Spec.XLbl.quiet {N T : Type} : XLbl N T → Bool
  | .start _ _ | .lose _ | .commit _ | .fail _ | .tdeposit _ | .publish _ | .inject _ | .begin
  | .endPass => false
  | _ => true

/-- **The quiet frame**: a quiet step keeps the marking, the same-pass counts, the order, the
identities and transitions of the firings in flight, never lowers the identity supply, enters no
pass, and leaves a pass only by ending the run. -/
theorem xstepW_quiet_frame {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : xstepW P C s l = some s') (hq : l.quiet = true) :
    s'.M = s.M ∧ s'.delta = s.delta ∧ s'.order = s.order ∧
      s'.fl.map (·.id) = s.fl.map (·.id) ∧ s'.fl.map (·.t) = s.fl.map (·.t) ∧
      s.nextId ≤ s'.nextId ∧ (s'.phase = .pass → s.phase = .pass) ∧
      (s.phase = .pass → s'.phase = .pass ∨ isExecPhase s'.phase = false) ∧
      (isExecPhase s'.phase = true → isExecPhase s.phase = true) := by
  cases l with
  | delay δ => cases xstepW_delay h; exact ⟨rfl, rfl, rfl, rfl, rfl, le_refl _, id, Or.inl, id⟩
  | write i p x =>
    obtain ⟨f, -, -, rfl⟩ := writeStep_some h
    exact ⟨rfl, rfl, rfl, updFiring_map _ fun _ => rfl, updFiring_map _ fun _ => rfl, le_refl _,
      id, Or.inl, id⟩
  | flush i =>
    obtain ⟨f, -, -, -, -, ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ := flushStep_some h <;>
      exact ⟨rfl, rfl, rfl, updFiring_map _ fun _ => rfl, updFiring_map _ fun _ => rfl,
        le_refl _, id, Or.inl, id⟩
  | ret i ok =>
    obtain ⟨f, -, -, rfl⟩ := retStep_some h
    exact ⟨rfl, rfl, rfl, updFiring_map _ fun _ => rfl, updFiring_map _ fun _ => rfl, le_refl _,
      id, Or.inl, id⟩
  | expire i e =>
    obtain ⟨f, -, -, -, -, -, rfl⟩ := expireStep_some h
    exact ⟨rfl, rfl, rfl, updFiring_map _ fun _ => rfl, updFiring_map _ fun _ => rfl, le_refl _,
      id, Or.inl, id⟩
  | request p x r =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := requestStep_some h
    · exact ⟨rfl, rfl, rfl, rfl, rfl, Nat.le_succ _, id, Or.inl, id⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, le_refl _, id, Or.inl, id⟩
  | drain => obtain ⟨-, rfl⟩ := drainStep_some h; exact ⟨rfl, rfl, rfl, rfl, rfl, le_refl _, id, Or.inl, id⟩
  | close => obtain ⟨-, rfl⟩ := closeStep_some h; exact ⟨rfl, rfl, rfl, rfl, rfl, le_refl _, id, Or.inl, id⟩
  | terminateNow =>
    obtain ⟨-, rfl⟩ := terminateStep_some h; exact ⟨rfl, rfl, rfl, rfl, rfl, le_refl _, id, Or.inl, id⟩
  | endCompletions =>
    obtain ⟨hp, -, -, -, rfl⟩ := xstepW_endCompletions h
    exact ⟨rfl, rfl, rfl, rfl, rfl, le_refl _, by simp, by simp [hp], by simp [hp, isExecPhase]⟩
  | endPublications =>
    obtain ⟨hp, -, -, rfl⟩ := xstepW_endPublications h
    exact ⟨rfl, rfl, rfl, rfl, rfl, le_refl _, by simp, by simp [hp], by simp [hp, isExecPhase]⟩
  | discard k =>
    obtain ⟨_, _, _, -, -, -, hp, rfl⟩ := discardStep_some h
    rcases hp with hp | hp <;>
      exact ⟨rfl, rfl, rfl, rfl, rfl, le_refl _, by simp [hp], by simp [hp], by simp [hp, isExecPhase]⟩
  | snapshot a =>
    obtain ⟨-, -, -, rfl⟩ := snapshotStep_some h
    exact ⟨rfl, rfl, rfl, rfl, rfl, le_refl _, id, Or.inl, id⟩
  | endEvents =>
    obtain ⟨hp, -, -, rfl⟩ := xstepW_endEvents h
    exact ⟨rfl, rfl, rfl, rfl, rfl, le_refl _, by simp, by simp [hp], by simp [hp, isExecPhase]⟩
  | update =>
    obtain ⟨hp, -, rfl⟩ := xstepW_update h
    exact ⟨rfl, rfl, rfl, rfl, rfl, le_refl _, by simp, by simp [hp], by simp [hp, isExecPhase]⟩
  | deadline ns =>
    obtain ⟨hp, -, -, rfl⟩ := xstepW_deadline h
    exact ⟨rfl, rfl, rfl, rfl, rfl, le_refl _, by simp, by simp [hp], by simp [hp, isExecPhase]⟩
  | finish c =>
    cases c with
    | quiescent =>
      obtain ⟨-, -, -, rfl⟩ := xstepW_finishQuiescent h
      exact ⟨rfl, rfl, rfl, rfl, rfl, le_refl _, by simp, fun _ => Or.inr rfl, by simp [isExecPhase]⟩
    | closed =>
      obtain ⟨-, -, -, -, rfl⟩ := xstepW_finishClosed h
      exact ⟨rfl, rfl, rfl, rfl, rfl, le_refl _, by simp, fun _ => Or.inr rfl, by simp [isExecPhase]⟩
    | terminal =>
      obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h
      exact ⟨rfl, rfl, rfl, rfl, rfl, le_refl _, by simp, fun _ => Or.inr rfl, by simp [isExecPhase]⟩
    | stopped =>
      obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h
      exact ⟨rfl, rfl, rfl, rfl, rfl, le_refl _, by simp, fun _ => Or.inr rfl, by simp [isExecPhase]⟩
  | park tmr =>
    obtain ⟨hp, -, -, -, -, -, -, -, rfl⟩ := parkStep_some h
    exact ⟨rfl, rfl, rfl, rfl, rfl, le_refl _, id, Or.inl, id⟩
  | wake =>
    obtain ⟨hp, -, rfl⟩ := wakeStep_some h
    exact ⟨rfl, rfl, rfl, rfl, rfl, le_refl _, by simp, by simp [hp], by simp [hp, isExecPhase]⟩
  | start | lose | commit | fail | tdeposit | publish | inject | begin | endPass =>
    simp [XLbl.quiet] at hq

omit [DecidableEq N] in
/-- Settling keeps the identities distinct and below the supply. -/
theorem idsFresh_settle {s : XSt N T} (hi : IdsFresh s) (i : Nat) {s' : XSt N T}
    (hfl : s'.fl = s.fl.filter (·.id != i)) (hn : s'.nextId = s.nextId) : IdsFresh s' := by
  refine ⟨?_, fun g hg => ?_⟩
  · rw [hfl]
    exact hi.1.sublist ((List.filter_sublist).map _)
  · rw [hfl] at hg
    rw [hn]
    exact hi.2 g (List.mem_filter.mp hg).1

/-- **Every step keeps the identities fresh and the same-pass tail within its queue.** -/
theorem idsFresh_deltaLe_step {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : xstepW P C s l = some s') (hi : IdsFresh s) (hd : DeltaLe s) :
    IdsFresh s' ∧ DeltaLe s' := by
  cases hq : l.quiet
  · cases l with
    | start n sy =>
      obtain ⟨t, rest, -, -, -, -, -, -, -, rfl⟩ := startStep_some h
      refine ⟨⟨?_, fun g hg => ?_⟩, fun p => ?_⟩
      · simp only [List.map_append, List.map_cons, List.map_nil]
        refine List.nodup_append.mpr ⟨hi.1, List.nodup_singleton _, ?_⟩
        intro a ha b hb
        simp only [List.mem_singleton] at hb
        subst hb
        obtain ⟨g, hg, rfl⟩ := List.mem_map.mp ha
        exact Nat.ne_of_lt (hi.2 g hg)
      · simp only [List.mem_append, List.mem_singleton] at hg
        rcases hg with hg | rfl
        · exact Nat.lt_succ_of_lt (hi.2 g hg)
        · exact Nat.lt_succ_self _
      · simp only [liveAfter, List.length_append, hid_length hd]
        omega
    | lose n =>
      obtain ⟨_, _, -, -, -, -, -, -, rfl⟩ := loseStep_some h
      exact ⟨hi, hd⟩
    | commit i =>
      obtain ⟨f, e, -, -, -, -, -, rfl⟩ := commitStep_some h
      refine ⟨idsFresh_settle hi i rfl rfl, fun p => ?_⟩
      simp only [depositAt, qAppend_apply, List.length_append, countIn_eq]
      have := hd p
      split <;> simp <;> omega
    | tdeposit i =>
      obtain ⟨f, e, -, -, -, -, rfl⟩ := tdepositStep_some h
      refine ⟨idsFresh_settle hi i rfl rfl, fun p => ?_⟩
      simp only [depositAt, qAppend_apply, List.length_append, countIn_eq]
      have := hd p
      split <;> simp <;> omega
    | fail i =>
      obtain ⟨f, -, -, -, rfl⟩ := failStep_some h
      exact ⟨idsFresh_settle hi i rfl rfl, hd⟩
    | publish i =>
      obtain ⟨b, rest, -, -, -, rfl⟩ := publishStep_some h
      refine ⟨hi, fun p => ?_⟩
      simp only [qAppend_apply, List.length_append]
      have := hd p
      omega
    | inject k =>
      obtain ⟨q, x, rest, -, -, -, -, rfl⟩ := injectStep_some h
      refine ⟨hi, fun p => ?_⟩
      simp only [qAppendOne]
      have := hd p
      split <;> simp <;> omega
    | begin =>
      obtain ⟨-, -, -, -, rfl⟩ := xstepW_begin h
      exact ⟨hi, fun p => Nat.zero_le _⟩
    | endPass =>
      obtain ⟨-, -, -, -, rfl⟩ := xstepW_endPass h
      exact ⟨hi, hd⟩
    | _ => simp [XLbl.quiet] at hq
  · obtain ⟨hM, hD, -, hid, -, hn, -⟩ := xstepW_quiet_frame h hq
    refine ⟨⟨hid ▸ hi.1, fun g hg => ?_⟩, fun p => ?_⟩
    · have : g.id ∈ s.fl.map (·.id) := hid ▸ List.mem_map_of_mem hg
      obtain ⟨g₀, hg₀, he⟩ := List.mem_map.mp this
      have := hi.2 g₀ hg₀
      omega
    · rw [hM, hD]; exact hd p

omit [DecidableEq N] in
/-- The initial state has fresh identities and an empty same-pass tail. -/
theorem idsFresh_deltaLe_xinit (M0 : QMarking N T) (r0 : Nat) :
    IdsFresh (xinit M0 r0) ∧ DeltaLe (xinit M0 r0) :=
  ⟨⟨List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩, fun _ => Nat.zero_le _⟩

/-- Along a decided run. -/
theorem idsFresh_deltaLe_xrun {C : Cfg N T} :
    ∀ {s s' : XSt N T} {ls : List (XLbl N T)}, xrun C s ls = some s' →
      IdsFresh s ∧ DeltaLe s → IdsFresh s' ∧ DeltaLe s'
  | s, s', [], h, hi => by cases h; exact hi
  | s, s', l :: ls, h, hi => by
    obtain ⟨s₁, h1, h2⟩ := xrun_cons.mp h
    exact idsFresh_deltaLe_xrun h2 (idsFresh_deltaLe_step h1 hi.1 hi.2)

omit [DecidableEq N] in
/-- **Settling one firing**: with distinct identities, the names of the firings left are the
names before with the settled firing's name taken out once. -/
theorem names_filter_perm {l : List (Firing N T)} (hn : (l.map (·.id)).Nodup) {f : Firing N T}
    (hf : f ∈ l) {i : Nat} (hi : f.id = i) :
    (l.map (·.t.core.name)).Perm (f.t.core.name :: (l.filter (·.id != i)).map (·.t.core.name)) := by
  induction l with
  | nil => exact absurd hf List.not_mem_nil
  | cons g l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    obtain ⟨hgn, hn⟩ := hn
    rcases List.mem_cons.mp hf with rfl | hfl
    · have hrest : l.filter (·.id != i) = l := by
        rw [List.filter_eq_self]
        intro x hx
        simp only [bne_iff_ne, ne_eq]
        rintro rfl
        exact hgn ⟨x, hx, hi.symm⟩
      simp [hi, hrest]
    · by_cases hg : g.id = i
      · exact absurd ⟨f, hfl, hi.trans hg.symm⟩ hgn
      · have hfg : (g :: l).filter (·.id != i) = g :: l.filter (·.id != i) := by
          simp [hg]
        rw [hfg, List.map_cons, List.map_cons]
        exact ((ih hn hfl).cons _).trans (List.Perm.swap _ _ _)

end Inv

/-! ## L5: the count projection is an `InFlight.XStep` run (pass normalisation, `hoist_vis`)

`InFlight.XStep` is the executor of the verifier's split argument: a row starts when it is
enabled on the live marking, and an in-flight transition completes with one of its rows. The
reference executor differs in one place: a synchronous firing settled inside its pass deposits
behind the pass-visible marking, and the later starts of the pass are judged on that visible
marking ([EXEC-003], R-EXEC-11 (a)). Moving each such in-pass deposit behind the last start of its
pass (to the end of the pass) gives a run in which every start is judged on the live marking, and
the visible marking of the original run is the live marking of the moved one (`hoist_vis`).

The simulation `Hoist C R s x g` carries the moved run's state `x` and the deposits `g` the pass
has moved (the ghost rows), in the order they were settled:

* the executor's counts are `x`'s marking plus the moved rows;
* in a pass, `x`'s marking is the pass-visible one;
* outside a pass, while the loop runs, nothing is moved;
* `x`'s pending names are the names of the firings in flight and of the moved rows, as a multiset;
* every moved row is a row of `R`, and each moved row lands on a marking no terminal place marks;
* the pass order holds transitions of the net.

A firing that fails is a completion with the empty row (clash 28); a timeout deposit is a
completion with its timeout row. The rows a run uses are a per-run hypothesis (`RowsCover`), as
`OfferedEmission` is for L2. A publication (a flushed batch, CONC-003) and an injection have no
counterpart in `InFlight.XStep`, whose header excludes `ctx.flush()` and environment places, so
`RowsCover` excludes them; L8 covers injections. -/

section L5

variable {T : Type}

open Libpetri.Novel.InFlight (addD addAll)

/-- The names of the firings in flight, one per firing. -/
def flNames {N : Type} (s : XSt N T) : List String := s.fl.map (·.t.core.name)

/-- The names of a list of rows. -/
def rowNames (g : List Novel.InFlight.Row) : List String := g.map (·.1.name)

/-- **The rows a step uses are rows of `R`** (per-run hypothesis): a commit or a timeout deposit
of firing `i` deposits the row of its transition with the places of its outcome, a fail the row
of its transition with nothing; a publication and an injection are outside the projection. -/
def RowsCover (R : List Novel.InFlight.Row) (y : XStep PlaceId T) : Prop :=
  match y.2.1 with
  | .commit i | .tdeposit i =>
      ∀ f ∈ y.1.fl, f.id = i → ∀ e, (f.out = some (.ok e) ∨ f.out = some (.timedOut e)) →
        (toTransition f.t.core, e.map Prod.fst) ∈ R
  | .fail i => ∀ f ∈ y.1.fl, f.id = i → (toTransition f.t.core, []) ∈ R
  | .publish _ | .inject _ => False
  | _ => True

/-- **The L5 simulation** between an executor state `s` and a state `x` of `InFlight.XStep`
over the rows `R`, with the moved rows `g`. -/
structure Hoist (C : Cfg PlaceId T) (R : List Novel.InFlight.Row) (s : XSt PlaceId T)
    (x : Novel.InFlight.XState) (g : List Novel.InFlight.Row) : Prop where
  /-- The executor's counts are the moved run's marking plus the moved rows. -/
  marking : addAll x.a g = qCount s.M
  /-- In a pass, the moved run's marking is the pass-visible one. -/
  visible : s.phase = .pass → x.a = qCount (vis s)
  /-- Outside a pass, while the loop runs, nothing is moved. -/
  quiet : s.phase ≠ .pass → isExecPhase s.phase = true → g = []
  /-- The pending names are those of the firings in flight and of the moved rows. -/
  pend : x.pend.Perm (flNames s ++ rowNames g)
  /-- The moved rows are rows of `R`. -/
  rows : ∀ r ∈ g, r ∈ R
  /-- Each moved row lands on a marking that marks no terminal place. -/
  gLive : ∀ j < g.length, NoTerm C (addAll x.a (g.take j))
  /-- The pass order holds transitions of the net. -/
  order : ∀ u ∈ s.order, u ∈ C.X.net.transitions

/-- The initial state: nothing in flight, nothing moved. -/
theorem hoist_xinit (C : Cfg PlaceId T) (R : List Novel.InFlight.Row) (M0 : QMarking PlaceId T) (r0 : Nat) :
    Hoist C R (xinit M0 r0) ⟨qCount M0, []⟩ [] where
  marking := Novel.InFlight.addAll_nil _
  visible := fun h => by simp [xinit] at h
  quiet := fun _ _ => rfl
  pend := by simp [flNames, rowNames, xinit]
  rows := fun _ h => absurd h List.not_mem_nil
  gLive := fun _ h => absurd h (Nat.not_lt_zero _)
  order := fun _ h => by simp [xinit] at h

/-- **Completing the moved rows**: from `x`, the moved rows complete one after the other, in the
order they were settled, and the run reaches the marking with all of them deposited, with the
other pending names left. -/
theorem flush_moved {R : List Novel.InFlight.Row} {live : AMarking → Prop} :
    ∀ (g : List Novel.InFlight.Row) (a : AMarking) (pend L : List String), (∀ r ∈ g, r ∈ R) →
      pend.Perm (L ++ rowNames g) → (∀ j < g.length, live (addAll a (g.take j))) →
      ∃ pend', Relation.ReflTransGen (Novel.InFlight.XStep R live) ⟨a, pend⟩
        ⟨addAll a g, pend'⟩ ∧ pend'.Perm L
  | [], a, pend, L, _, hp, _ => ⟨pend, by rw [Novel.InFlight.addAll_nil], by simpa [rowNames] using hp⟩
  | r :: g, a, pend, L, hr, hp, hl => by
    have hp' : pend.Perm (r.1.name :: (L ++ rowNames g)) :=
      hp.trans (by simp only [rowNames, List.map_cons]; exact List.perm_middle)
    have hmem : r.1.name ∈ pend := hp'.symm.subset List.mem_cons_self
    have h0 : live a := by simpa [Novel.InFlight.addAll_nil] using hl 0 (by simp)
    have hstep : Novel.InFlight.XStep R live ⟨a, pend⟩ ⟨addD a r.2, pend.erase r.1.name⟩ :=
      Novel.InFlight.XStep.complete ⟨a, pend⟩ r (hr r List.mem_cons_self) h0 hmem
    have hpe : (pend.erase r.1.name).Perm (L ++ rowNames g) := by
      have := hp'.erase r.1.name
      simpa using this
    obtain ⟨pend', hrun, hpp⟩ := flush_moved g (addD a r.2) (pend.erase r.1.name) L
      (fun r' h => hr r' (List.mem_cons_of_mem _ h)) hpe
      (fun j hj => by
        have := hl (j + 1) (by simp; omega)
        simpa [Novel.InFlight.addAll_cons] using this)
    refine ⟨pend', Relation.ReflTransGen.head hstep ?_, hpp⟩
    rw [Novel.InFlight.addAll_cons]
    exact hrun

/-- The moved rows add up to the same-pass counts. -/
theorem hoist_sum {C : Cfg PlaceId T} {R : List Novel.InFlight.Row} {s : XSt PlaceId T}
    {x : Novel.InFlight.XState} {g : List Novel.InFlight.Row} (hh : Hoist C R s x g) (hd : DeltaLe s)
    (hp : s.phase = .pass) (p : PlaceId) : (g.map fun r => r.2.count p).sum = s.delta p := by
  have h1 := congrFun hh.marking p
  have h2 := qCount_vis_add hd p
  rw [← hh.visible hp] at h2
  simp only [Novel.InFlight.addAll] at h1
  omega

/-- The guard of a settle step, unpacked. -/
theorem canSettle_parts {C : Cfg PlaceId T} {s : XSt PlaceId T} {i : Nat} {f : Firing PlaceId T}
    (h : canSettle C s i f = true) :
    liveB C s = true ∧ isExecPhase s.phase = true ∧
      (s.phase = .pass ∨ s.phase = .completions ∨ s.phase = .await) := by
  unfold canSettle settleOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hx, hl⟩, -⟩, hs⟩ := h
  refine ⟨hl, hx, ?_⟩
  revert hs
  cases s.phase <;> simp

/-- A settle step that deposits row `r` (a commit, a timeout deposit, or a fail with the empty
row) keeps the simulation: inside the pass the row is moved, outside it the moved run completes
it. -/
theorem hoist_settle {C : Cfg PlaceId T} {R : List Novel.InFlight.Row} {s s' : XSt PlaceId T} {i : Nat}
    {f : Firing PlaceId T} {r : Novel.InFlight.Row} (hf : f ∈ s.fl) (hfi : f.id = i) (hcs : canSettle C s i f = true)
    (hr : r ∈ R) (hrn : r.1.name = f.t.core.name)
    (hM : qCount s'.M = addD (qCount s.M) r.2)
    (hfl : s'.fl = s.fl.filter (·.id != i)) (hord : s'.order = s.order)
    (hph : s'.phase = if s.phase = .await then .completions else s.phase)
    (hvis : s.phase = .pass → vis s' = vis s)
    (hi : IdsFresh s) {x : Novel.InFlight.XState} {g : List Novel.InFlight.Row} (hh : Hoist C R s x g) :
    ∃ x' g', Relation.ReflTransGen (Novel.InFlight.XStep R (NoTerm C)) x x' ∧
      Hoist C R s' x' g' := by
  obtain ⟨hl, hx, hph3⟩ := canSettle_parts hcs
  have hnames := names_filter_perm hi.1 hf hfi
  have hfl' : flNames s' = (s.fl.filter (·.id != i)).map (·.t.core.name) := by
    simp [flNames, hfl]
  by_cases hp : s.phase = .pass
  · -- inside the pass: the row is moved behind the pass
    have hp' : s'.phase = .pass := by simp [hph, hp]
    refine ⟨x, g ++ [r], Relation.ReflTransGen.refl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [addAll_append_one, hh.marking, hM]
    · intro _; rw [hvis hp]; exact hh.visible hp
    · intro h; exact absurd hp' h
    · refine hh.pend.trans ?_
      rw [hfl']
      simp only [flNames, rowNames, List.map_append, List.map_cons, List.map_nil, hrn]
      refine (hnames.append_right _).trans ?_
      simpa [List.append_assoc] using (List.perm_middle (l₁ := (s.fl.filter (·.id != i)).map
        (·.t.core.name) ++ g.map (·.1.name)) (l₂ := []) (a := f.t.core.name)).symm
    · intro r' h
      rcases List.mem_append.mp h with h | h
      · exact hh.rows r' h
      · rw [List.mem_singleton.mp h]; exact hr
    · intro j hj
      simp only [List.length_append, List.length_singleton] at hj
      by_cases hjl : j < g.length
      · rw [List.take_append_of_le_length (Nat.le_of_lt hjl)]; exact hh.gLive j hjl
      · have hj' : j = g.length := by omega
        subst hj'
        rw [List.take_append_of_le_length (le_refl _), List.take_length, hh.marking]
        exact noTerm_of_liveB hl
    · rw [hord]; exact hh.order
  · -- outside the pass: nothing is moved, the moved run completes the row
    have hg : g = [] := hh.quiet hp hx
    subst hg
    have hxa : x.a = qCount s.M := by simpa [Novel.InFlight.addAll_nil] using hh.marking
    have hmem : r.1.name ∈ x.pend := by
      rw [hrn]
      exact hh.pend.symm.subset (by simp [flNames]; exact Or.inl ⟨f, hf, rfl⟩)
    have hstep := Novel.InFlight.XStep.complete (live := NoTerm C) x r hr
      (by rw [hxa]; exact noTerm_of_liveB hl) hmem
    refine ⟨_, [], Relation.ReflTransGen.single hstep, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [Novel.InFlight.addAll_nil, hxa, hM]
    · intro h
      rw [hph] at h
      split at h
      · exact absurd h (by simp)
      · exact absurd h hp
    · intro _ _; rfl
    · have := (hh.pend.trans (by simpa [rowNames, flNames] using hnames)).erase r.1.name
      rw [hrn] at this ⊢
      simpa [hfl', rowNames] using this
    · intro _ h; exact absurd h List.not_mem_nil
    · intro _ h; exact absurd h (Nat.not_lt_zero _)
    · rw [hord]; exact hh.order

/-- **L5, one step.** Every step of the reference executor that uses rows of `R` keeps the
simulation, with zero or more `InFlight.XStep` steps on the moved side: a start is a start, a
settle outside the pass is a completion, a settle inside the pass is moved, the end of the pass
completes the moved rows, and every other step is no step. -/
theorem hoist_step {C : Cfg PlaceId T} {R : List Novel.InFlight.Row}
    (hR : ∀ u ∈ C.X.net.transitions, ∃ d, (toTransition u.core, d) ∈ R)
    {s s' : XSt PlaceId T} {l : XLbl PlaceId T} (h : RefExec C s l s') (hc : RowsCover R (s, l, s'))
    (hi : IdsFresh s) (hd : DeltaLe s) {x : Novel.InFlight.XState} {g : List Novel.InFlight.Row}
    (hh : Hoist C R s x g) :
    ∃ x' g', Relation.ReflTransGen (Novel.InFlight.XStep R (NoTerm C)) x x' ∧
      Hoist C R s' x' g' := by
  cases hq : l.quiet
  · cases l with
    | start n sy =>
      obtain ⟨t, rest, ho, hp, hl, -, -, -, hen, hs'⟩ := startStep_some (P := refXPol) h
      have hM : s'.M = liveAfter s t := by rw [hs']
      have hD : s'.delta = s.delta := by rw [hs']
      have hph : s'.phase = .pass := by rw [hs']; exact hp
      have hfn : flNames s' = flNames s ++ [t.core.name] := by rw [hs']; simp [flNames]
      have hord : s'.order = rest := by rw [hs']
      have ht : t ∈ C.X.net.transitions := hh.order t (by simp [ho])
      obtain ⟨d, hdR⟩ := hR t ht
      have hxa : x.a = qCount (vis s) := hh.visible hp
      have hle : ∀ p, x.a p ≤ qCount s.M p := fun p => by
        rw [hxa]; have := qCount_vis_add hd p; omega
      have hlive : NoTerm C x.a := noTerm_mono hle (noTerm_of_liveB hl)
      have hen' : enabledA x.a (toTransition t.core) = true := by
        rw [enabledA_toTransition, hxa]; exact hen
      have hstep := Novel.InFlight.XStep.start (live := NoTerm C) x (toTransition t.core, d) hdR
        hlive hen'
      have hmid : Novel.InFlight.startA x.a (toTransition t.core) = qCount (qConsume (vis s) t) := by
        rw [startA_toTransition, hxa, qCount_qConsume]
      refine ⟨_, g, Relation.ReflTransGen.single hstep, ⟨?_, ?_, ?_, ?_, hh.rows, ?_, ?_⟩⟩
      · funext p
        have hs := hoist_sum hh hd hp p
        simp only [Novel.InFlight.addAll] at hs ⊢
        rw [hs, hmid, hM]
        simp only [qCount, liveAfter, List.length_append, hid_length hd]
      · intro _; rw [vis_start hd t hM hD]; exact hmid
      · intro h'; exact absurd hph h'
      · refine (hh.pend.cons _).trans ?_
        rw [hfn]
        simp only [rowNames, List.append_assoc, List.cons_append, List.nil_append]
        exact List.perm_middle.symm
      · intro j hj
        exact noTerm_mono (addAll_mono (fun p => startA_le _ _ p) _) (hh.gLive j hj)
      · intro u hu; rw [hord] at hu; exact hh.order u (by simp [ho, hu])
    | lose n =>
      obtain ⟨t, rest, ho, hp, -, -, -, -, rfl⟩ := loseStep_some (P := refXPol) h
      exact ⟨x, g, Relation.ReflTransGen.refl, ⟨hh.marking, hh.visible, hh.quiet, hh.pend,
        hh.rows, hh.gLive, fun u hu => hh.order u (by simp [ho, hu])⟩⟩
    | begin =>
      obtain ⟨hp, -, -, -, rfl⟩ := xstepW_begin (P := refXPol) h
      have hg : g = [] := hh.quiet (by simp [hp]) (by simp [hp, isExecPhase])
      subst hg
      refine ⟨x, [], Relation.ReflTransGen.refl, ⟨hh.marking, ?_, fun _ _ => rfl, hh.pend,
        hh.rows, hh.gLive, fun u hu => (mem_readyOrder hu).1⟩⟩
      intro _
      rw [vis_of_delta_zero (fun _ => rfl)]
      simpa [Novel.InFlight.addAll_nil] using hh.marking
    | endPass =>
      obtain ⟨hp, -, -, -, rfl⟩ := xstepW_endPass (P := refXPol) h
      obtain ⟨pend', hrun, hpp⟩ :=
        flush_moved g x.a x.pend (flNames s) hh.rows hh.pend hh.gLive
      refine ⟨_, [], hrun, ⟨?_, ?_, fun _ _ => rfl, ?_, fun _ h => absurd h List.not_mem_nil,
        fun _ h => absurd h (Nat.not_lt_zero _), hh.order⟩⟩
      · rw [Novel.InFlight.addAll_nil]; exact hh.marking
      · intro h'
        simp only at h'
        split at h' <;> exact absurd h' (by simp)
      · simpa [rowNames, flNames] using hpp
    | commit i =>
      obtain ⟨f, e, hfind, he, hcs, -, -, rfl⟩ := commitStep_some (P := refXPol) h
      have hfm := List.mem_of_find?_eq_some hfind
      have hfi : f.id = i := by simpa using List.find?_some hfind
      refine hoist_settle (s' := depositAt C s i e) hfm hfi hcs (hc f hfm hfi e (Or.inl he)) rfl ?_ rfl rfl rfl
        (fun hp => vis_depositAt_pass hp hd) hi hh
      funext p
      simp [depositAt, Novel.InFlight.addD, qCount_qAppend, count_map_fst]
    | tdeposit i =>
      obtain ⟨f, e, hfind, he, hcs, -, rfl⟩ := tdepositStep_some h
      have hfm := List.mem_of_find?_eq_some hfind
      have hfi : f.id = i := by simpa using List.find?_some hfind
      refine hoist_settle (s' := depositAt C s i e) hfm hfi hcs (hc f hfm hfi e (Or.inr he)) rfl ?_ rfl rfl rfl
        (fun hp => vis_depositAt_pass hp hd) hi hh
      funext p
      simp [depositAt, Novel.InFlight.addD, qCount_qAppend, count_map_fst]
    | fail i =>
      obtain ⟨f, hfind, hcs, -, rfl⟩ := failStep_some (P := refXPol) h
      have hfm := List.mem_of_find?_eq_some hfind
      have hfi : f.id = i := by simpa using List.find?_some hfind
      refine hoist_settle (s' := settle s i) (r := (toTransition f.t.core, [])) hfm hfi hcs (hc f hfm hfi) rfl ?_ rfl
        rfl rfl (fun _ => rfl) hi hh
      funext p
      simp [settle, Novel.InFlight.addD]
    | publish i => exact absurd hc id
    | inject k => exact absurd hc id
    | _ => simp [XLbl.quiet] at hq
  · obtain ⟨hM, hD, hO, -, hT, -, hpp, hpq, hex⟩ := xstepW_quiet_frame (P := refXPol) h hq
    have hvis : vis s' = vis s := by funext p; simp [vis, hM, hD]
    refine ⟨x, g, Relation.ReflTransGen.refl, ⟨?_, ?_, ?_, ?_, hh.rows, hh.gLive, ?_⟩⟩
    · rw [hM]; exact hh.marking
    · intro h'; rw [hvis]; exact hh.visible (hpp h')
    · intro hn hx
      apply hh.quiet _ (hex hx)
      intro hs
      rcases hpq hs with h1 | h1
      · exact hn h1
      · rw [h1] at hx; exact absurd hx (by simp)
    · have : flNames s' = flNames s := by
        have := congrArg (List.map (·.core.name)) hT
        simp only [List.map_map] at this
        exact this
      rw [this]; exact hh.pend
    · rw [hO]; exact hh.order

/-- The last state of a run with one more step in front. -/
theorem xrun_last_cons {N : Type} (s0 : XSt N T) (y : XStep N T) (rest : List (XStep N T)) :
    XRun.last s0 (y :: rest) = XRun.last y.2.2 rest := by
  cases rest with
  | nil => rfl
  | cons z zs => simp [XRun.last, List.getLast?_cons]

/-- **L5, runs.** Along a run of the reference executor that uses rows of `R`, the simulation
holds at the last state, reached by an `InFlight.XStep` run on the moved side. -/
theorem hoist_run {C : Cfg PlaceId T} {R : List Novel.InFlight.Row}
    (hR : ∀ u ∈ C.X.net.transitions, ∃ d, (toTransition u.core, d) ∈ R) :
    ∀ {s0 : XSt PlaceId T} {tr : List (XStep PlaceId T)}, XRun RefExec C s0 tr →
      (∀ y ∈ tr, RowsCover R y) → IdsFresh s0 ∧ DeltaLe s0 →
      ∀ {x : Novel.InFlight.XState} {g : List Novel.InFlight.Row}, Hoist C R s0 x g →
      ∃ x' g', Relation.ReflTransGen (Novel.InFlight.XStep R (NoTerm C)) x x' ∧
        Hoist C R (XRun.last s0 tr) x' g' ∧ IdsFresh (XRun.last s0 tr) ∧
        DeltaLe (XRun.last s0 tr)
  | s0, [], _, _, hi, x, g, hh => ⟨x, g, Relation.ReflTransGen.refl, hh, hi⟩
  | s0, y :: rest, hr, hc, hi, x, g, hh => by
    obtain ⟨hy1, hstep, hrest⟩ := hr
    subst hy1
    have hcy : RowsCover R (y.1, y.2.1, y.2.2) := hc y List.mem_cons_self
    obtain ⟨x₁, g₁, hrun₁, hh₁⟩ := hoist_step hR hstep hcy hi.1 hi.2 hh
    have hi₁ := idsFresh_deltaLe_step hstep hi.1 hi.2
    obtain ⟨x₂, g₂, hrun₂, hh₂, hi₂⟩ :=
      hoist_run hR hrest (fun z hz => hc z (List.mem_cons_of_mem _ hz)) hi₁ hh₁
    rw [xrun_last_cons]
    exact ⟨x₂, g₂, hrun₁.trans hrun₂, hh₂, hi₂⟩

/-- **L5, the count projection** ([VER-004], [EXEC-042]): the counts of every state a run of the
reference executor reaches from an initial state, using rows of `R`, are a marking of
`InFlight.XStep` over `R` gated by the strict stop, with exactly the firings in flight pending
(by name, as a multiset). The moved run completes each in-pass settle at the end of its pass. -/
theorem count_projection {C : Cfg PlaceId T} {R : List Novel.InFlight.Row}
    (hR : ∀ u ∈ C.X.net.transitions, ∃ d, (toTransition u.core, d) ∈ R)
    {M0 : QMarking PlaceId T} {r0 : Nat} {tr : List (XStep PlaceId T)}
    (ht : XRun RefExec C (xinit M0 r0) tr) (hc : ∀ y ∈ tr, RowsCover R y) :
    ∃ pend, Novel.InFlight.XReach R (NoTerm C) (qCount M0)
        ⟨qCount (XRun.last (xinit M0 r0) tr).M, pend⟩ ∧
      pend.Perm (flNames (XRun.last (xinit M0 r0) tr)) := by
  obtain ⟨x, g, hrun, hh, -⟩ := hoist_run hR ht hc (idsFresh_deltaLe_xinit M0 r0)
    (hoist_xinit C R M0 r0)
  obtain ⟨pend', hrun', hpp⟩ := flush_moved g x.a x.pend _ hh.rows hh.pend hh.gLive
  refine ⟨pend', hrun.trans ?_, hpp⟩
  rw [← hh.marking]
  exact hrun'

/-- **`hoist_vis`** ([EXEC-003], the observational form): in a pass, the pass-visible counts of
the executor are a marking of the moved run, so every start of the pass is judged on a live
marking of `InFlight.XStep`: as if every firing of the pass started before any of them
deposited. -/
theorem hoist_vis {C : Cfg PlaceId T} {R : List Novel.InFlight.Row}
    (hR : ∀ u ∈ C.X.net.transitions, ∃ d, (toTransition u.core, d) ∈ R)
    {M0 : QMarking PlaceId T} {r0 : Nat} {tr : List (XStep PlaceId T)}
    (ht : XRun RefExec C (xinit M0 r0) tr) (hc : ∀ y ∈ tr, RowsCover R y)
    (hp : (XRun.last (xinit M0 r0) tr).phase = .pass) :
    ∃ x, Novel.InFlight.XReach R (NoTerm C) (qCount M0) x ∧
      x.a = qCount (vis (XRun.last (xinit M0 r0) tr)) := by
  obtain ⟨x, g, hrun, hh, -⟩ := hoist_run hR ht hc (idsFresh_deltaLe_xinit M0 r0)
    (hoist_xinit C R M0 r0)
  exact ⟨x, hrun, hh.visible hp⟩

/-- **L5 at a rest**: where nothing is in flight, the executor's counts are a marking of
`InFlight.XStep` with nothing pending, so `InFlight.split_rest_sound` applies: they are a marking
of the split net with nothing pending, and a quiescence `Proven` of the split net covers them. -/
theorem rest_split {C : Cfg PlaceId T} {R : List Novel.InFlight.Row}
    (hR : ∀ u ∈ C.X.net.transitions, ∃ d, (toTransition u.core, d) ∈ R)
    {M0 : QMarking PlaceId T} {r0 : Nat} {tr : List (XStep PlaceId T)}
    (ht : XRun RefExec C (xinit M0 r0) tr) (hc : ∀ y ∈ tr, RowsCover R y)
    (hfl : (XRun.last (xinit M0 r0) tr).fl = [])
    {sp : String → Bool} (hnames : Novel.InFlight.NamesUnique R)
    (hcrit : ∀ r ∈ R, sp r.1.name = false → Novel.InFlight.Untested R r.2)
    (hlive : ∀ r ∈ R, sp r.1.name = false → ∀ a, NoTerm C a → NoTerm C (addD a r.2)) :
    Novel.InFlight.SReach R sp (NoTerm C) (qCount M0)
      ⟨qCount (XRun.last (xinit M0 r0) tr).M, []⟩ := by
  obtain ⟨pend, hx, hpp⟩ := count_projection hR ht hc
  have : pend = [] := by simpa [flNames, hfl] using hpp
  subst this
  exact Novel.InFlight.split_rest_sound hnames hcrit hlive hx

/-- **The L5 agreement conjunct** (consistency theorem): every run of the executor `E` from an
initial state that uses rows of `R` ends at counts that are a marking of `InFlight.XStep` over
`R`, gated by the strict stop, with exactly its firings in flight pending. -/
def CountAgrees (E : XRel PlaceId T) : Prop :=
  ∀ (C : Cfg PlaceId T) (R : List Novel.InFlight.Row),
    (∀ u ∈ C.X.net.transitions, ∃ d, (toTransition u.core, d) ∈ R) →
    ∀ (M0 : QMarking PlaceId T) (r0 : Nat) (tr : List (XStep PlaceId T)),
      XRun E C (xinit M0 r0) tr → (∀ y ∈ tr, RowsCover R y) →
      ∃ pend, Novel.InFlight.XReach R (NoTerm C) (qCount M0)
          ⟨qCount (XRun.last (xinit M0 r0) tr).M, pend⟩ ∧
        pend.Perm (flNames (XRun.last (xinit M0 r0) tr))

/-- The reference executor meets the L5 agreement conjunct. -/
theorem countAgrees_ref : CountAgrees (RefExec (N := PlaceId) (T := T)) :=
  fun _ _ hR _ _ _ ht hc => count_projection hR ht hc

end L5

/-! ## Queued injections, and where a clock status `reaped` comes from -/

section Queue

variable {N T : Type} [DecidableEq N]

/-- Every queued injection is for an environment place. -/
def EqEnvs (C : Cfg N T) (s : XSt N T) : Prop := ∀ y ∈ s.eq, y.2.1 ∈ C.envs

/-- An accepted request is for an environment place. -/
theorem mem_envs_of_accepted {C : Cfg N T} {s : XSt N T} {p : N}
    (h : Reply.accepted = replyFor C s p) : p ∈ C.envs := by
  unfold replyFor at h
  by_contra hp
  simp [hp] at h

/-- **Every step queues injections only for environment places.** -/
theorem eqEnvs_step {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : xstepW P C s l = some s') (he : EqEnvs C s) : EqEnvs C s' := by
  cases l with
  | delay δ => cases xstepW_delay h; exact he
  | write i p x => obtain ⟨f, -, -, rfl⟩ := writeStep_some h; exact he
  | flush i =>
    obtain ⟨f, -, -, -, -, ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ := flushStep_some h <;> exact he
  | ret i ok => obtain ⟨f, -, -, rfl⟩ := retStep_some h; exact he
  | expire i e => obtain ⟨f, -, -, -, -, -, rfl⟩ := expireStep_some h; exact he
  | request p x r =>
    obtain ⟨hr, ⟨ha, rfl⟩ | ⟨-, rfl⟩⟩ := requestStep_some h
    · intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact he y hy
      · rw [List.mem_singleton.mp hy]
        exact mem_envs_of_accepted (ha ▸ hr)
    · exact he
  | drain => obtain ⟨-, rfl⟩ := drainStep_some h; exact he
  | close => obtain ⟨-, rfl⟩ := closeStep_some h; exact he
  | terminateNow => obtain ⟨-, rfl⟩ := terminateStep_some h; exact fun _ h => absurd h List.not_mem_nil
  | commit i => obtain ⟨f, e, -, -, -, -, -, rfl⟩ := commitStep_some h; exact he
  | fail i => obtain ⟨f, -, -, -, rfl⟩ := failStep_some h; exact he
  | tdeposit i => obtain ⟨f, e, -, -, -, -, rfl⟩ := tdepositStep_some h; exact he
  | endCompletions => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endCompletions h; exact he
  | publish i => obtain ⟨b, rest, -, -, -, rfl⟩ := publishStep_some h; exact he
  | endPublications => obtain ⟨-, -, -, rfl⟩ := xstepW_endPublications h; exact he
  | inject k =>
    obtain ⟨p, x, rest, hq, -, -, -, rfl⟩ := injectStep_some h
    exact fun y hy => he y (by rw [hq]; exact List.mem_cons_of_mem _ hy)
  | discard k =>
    obtain ⟨p, x, rest, hq, -, -, -, rfl⟩ := discardStep_some h
    exact fun y hy => he y (by rw [hq]; exact List.mem_cons_of_mem _ hy)
  | snapshot a => obtain ⟨-, -, -, rfl⟩ := snapshotStep_some h; exact he
  | endEvents => obtain ⟨-, -, -, rfl⟩ := xstepW_endEvents h; exact he
  | update => obtain ⟨-, -, rfl⟩ := xstepW_update h; exact he
  | deadline ns => obtain ⟨-, -, -, rfl⟩ := xstepW_deadline h; exact he
  | finish c =>
    cases c with
    | quiescent =>
      obtain ⟨-, -, -, rfl⟩ := xstepW_finishQuiescent h; exact fun _ h => absurd h List.not_mem_nil
    | closed =>
      obtain ⟨-, -, -, -, rfl⟩ := xstepW_finishClosed h; exact fun _ h => absurd h List.not_mem_nil
    | terminal =>
      obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h; exact fun _ h => absurd h List.not_mem_nil
    | stopped =>
      obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h; exact fun _ h => absurd h List.not_mem_nil
  | begin => obtain ⟨-, -, -, -, rfl⟩ := xstepW_begin h; exact he
  | start n sy => obtain ⟨t, rest, -, -, -, -, -, -, -, rfl⟩ := startStep_some h; exact he
  | lose n => obtain ⟨_, _, -, -, -, -, -, -, rfl⟩ := loseStep_some h; exact he
  | endPass => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endPass h; exact he
  | park tmr => obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := parkStep_some h; exact he
  | wake => obtain ⟨-, -, rfl⟩ := wakeStep_some h; exact he

/-- Along a decided run. -/
theorem eqEnvs_xrun {C : Cfg N T} :
    ∀ {s s' : XSt N T} {ls : List (XLbl N T)}, xrun C s ls = some s' → EqEnvs C s → EqEnvs C s'
  | s, s', [], h, he => by cases h; exact he
  | s, s', l :: ls, h, he => by
    obtain ⟨s₁, h1, h2⟩ := xrun_cons.mp h
    exact eqEnvs_xrun h2 (eqEnvs_step h1 he)

/-- **Where `reaped` comes from**: a name reaped after a step was reaped before it, or the step
is the deadline step and the name is expired at the deadline step's reading. -/
theorem reaped_origin {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : xstepW P C s l = some s') {n : String} (hr : s'.st n = .reaped) :
    s.st n = .reaped ∨ (∃ ns, l = .deadline ns) ∧ n ∈ expiredNames P C (atDeadline s) := by
  have hun : ∀ {ps : List N} {st : String → Status}, unreap C ps st n = .reaped → st n = .reaped :=
    fun h' => by
      unfold unreap at h'
      split at h'
      · split at h' <;> simp_all
      · exact h'
  have haft : ∀ {t : Trans N}, afterStart P C s t n = .reaped → s.st n = .reaped := fun h' => by
    unfold afterStart at h'
    split at h'
    · exact absurd h' (by simp)
    · split at h'
      · split at h' <;> exact absurd h' (by simp)
      · exact h'
  cases l with
  | delay δ => cases xstepW_delay h; exact Or.inl hr
  | write i p x => obtain ⟨f, -, -, rfl⟩ := writeStep_some h; exact Or.inl hr
  | flush i =>
    obtain ⟨f, -, -, -, -, ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ := flushStep_some h <;> exact Or.inl hr
  | ret i ok => obtain ⟨f, -, -, rfl⟩ := retStep_some h; exact Or.inl hr
  | expire i e => obtain ⟨f, -, -, -, -, -, rfl⟩ := expireStep_some h; exact Or.inl hr
  | request p x r =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := requestStep_some h <;> exact Or.inl hr
  | drain => obtain ⟨-, rfl⟩ := drainStep_some h; exact Or.inl hr
  | close => obtain ⟨-, rfl⟩ := closeStep_some h; exact Or.inl hr
  | terminateNow => obtain ⟨-, rfl⟩ := terminateStep_some h; exact Or.inl hr
  | commit i => obtain ⟨f, e, -, -, -, -, -, rfl⟩ := commitStep_some h; exact Or.inl (hun hr)
  | fail i => obtain ⟨f, -, -, -, rfl⟩ := failStep_some h; exact Or.inl hr
  | tdeposit i => obtain ⟨f, e, -, -, -, -, rfl⟩ := tdepositStep_some h; exact Or.inl (hun hr)
  | endCompletions => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endCompletions h; exact Or.inl hr
  | publish i => obtain ⟨b, rest, -, -, -, rfl⟩ := publishStep_some h; exact Or.inl (hun hr)
  | endPublications => obtain ⟨-, -, -, rfl⟩ := xstepW_endPublications h; exact Or.inl hr
  | inject k => obtain ⟨p, x, rest, -, -, -, -, rfl⟩ := injectStep_some h; exact Or.inl (hun hr)
  | discard k => obtain ⟨p, x, rest, -, -, -, -, rfl⟩ := discardStep_some h; exact Or.inl hr
  | snapshot a => obtain ⟨-, -, -, rfl⟩ := snapshotStep_some h; exact Or.inl hr
  | endEvents => obtain ⟨-, -, -, rfl⟩ := xstepW_endEvents h; exact Or.inl hr
  | update =>
    obtain ⟨-, -, rfl⟩ := xstepW_update h
    left
    simp only [updSt] at hr
    split at hr
    · exact absurd hr (by simp)
    · split at hr
      · split at hr
        · split at hr <;> exact absurd hr (by simp)
        · exact absurd hr (by simp)
      · split at hr <;> exact absurd hr (by simp)
      · assumption
  | deadline ns =>
    obtain ⟨-, -, hns, rfl⟩ := xstepW_deadline h
    simp only at hr
    split at hr
    · rename_i hc
      exact Or.inr ⟨⟨ns, rfl⟩, hns ▸ (List.contains_iff_mem.mp hc)⟩
    · exact Or.inl hr
  | finish c =>
    cases c with
    | quiescent => obtain ⟨-, -, -, rfl⟩ := xstepW_finishQuiescent h; exact Or.inl hr
    | closed => obtain ⟨-, -, -, -, rfl⟩ := xstepW_finishClosed h; exact Or.inl hr
    | terminal => obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h; exact Or.inl hr
    | stopped => obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h; exact Or.inl hr
  | begin => obtain ⟨-, -, -, -, rfl⟩ := xstepW_begin h; exact Or.inl hr
  | start n' sy =>
    obtain ⟨t, rest, -, -, -, -, -, -, -, rfl⟩ := startStep_some h
    exact Or.inl (haft (hun hr))
  | lose m =>
    obtain ⟨_, _, -, -, -, -, -, -, rfl⟩ := loseStep_some h
    simp only at hr
    split at hr
    · exact absurd hr (by simp)
    · exact Or.inl hr
  | endPass => obtain ⟨-, -, -, -, rfl⟩ := xstepW_endPass h; exact Or.inl hr
  | park tmr => obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := parkStep_some h; exact Or.inl hr
  | wake => obtain ⟨-, -, rfl⟩ := wakeStep_some h; exact Or.inl hr

/-- A reaped name names a transition of the net whose timing is reapable ([TIME-013]: only
`Deadline` and `Window` are reaped). -/
def ReapedReapable (C : Cfg N T) (s : XSt N T) : Prop :=
  ∀ n, s.st n = .reaped → ∃ u, findT C n = some u ∧ (C.X.timing u).reapable = true

/-- **Every step reaps only reapable transitions.** -/
theorem reapedReapable_step {P : XPol N T} {C : Cfg N T} (hN : NamesDistinct C.X)
    {s s' : XSt N T} {l : XLbl N T} (h : xstepW P C s l = some s') (hr : ReapedReapable C s) :
    ReapedReapable C s' := by
  intro n hn
  rcases reaped_origin h hn with h0 | ⟨-, hx⟩
  · exact hr n h0
  · unfold expiredNames at hx
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hmem, hexp⟩ := List.mem_filter.mp hu
    refine ⟨u, findT_of_mem hN hmem, ?_⟩
    unfold expiredAt at hexp
    simp only [Bool.and_eq_true] at hexp
    exact hexp.1.1

/-- Along a decided run. -/
theorem reapedReapable_xrun {C : Cfg N T} (hN : NamesDistinct C.X) :
    ∀ {s s' : XSt N T} {ls : List (XLbl N T)}, xrun C s ls = some s' →
      ReapedReapable C s → ReapedReapable C s'
  | s, s', [], h, hr => by cases h; exact hr
  | s, s', l :: ls, h, hr => by
    obtain ⟨s₁, h1, h2⟩ := xrun_cons.mp h
    exact reapedReapable_xrun hN h2 (reapedReapable_step hN h1 hr)

end Queue

/-! ## L8: injections and atomic firings are steps of the strict-stop relation with injection

`TerminalRewrite.StepStopInjRel` is the runtime the verifier's terminal rewrite is sound for
([EXEC-042]): from a marking that marks no terminal place, a flat transition fires atomically or
one token is injected into an environment place. An `inject` step of the reference executor is
`EnvSemantics.injC` on the queues (a token appended at the tail of its place) and the injection
step on the counts; the place is an environment place because only an accepted request queues
an injection ([ENV-002]). A firing is atomic when its start and its commit come one after the
other with nothing that changes the marking in between, and it is enabled on the live marking
with no same-pass deposit on a place it drains or resets (`LiveConsistent`; exec map CORRECTED 2:
without it the pass-visible recheck fires what no atomic order fires). On runs made of such
firings, injections and steps that leave the marking alone (`ARun`), the counts are a run of
`StepStopInjRel`, so the verified net's injected relation reaches them
(`terminal_rewrite_sound_inj`). -/

section L8

variable {T : Type}

/-- **The injection is `injC`**: an `inject` step appends the queued token at the tail of its
place, which is `EnvSemantics.injC` on coloured markings. -/
theorem inject_injC {C : Cfg PlaceId Colour} {s s' : XSt PlaceId Colour} {k : Nat}
    (h : RefExec C s (.inject k) s') :
    ∃ p x rest, s.eq = (k, p, x) :: rest ∧ s'.M = Novel.EnvSemantics.injC s.M p x := by
  obtain ⟨p, x, rest, hq, -, -, -, rfl⟩ := injectStep_some h
  refine ⟨p, x, rest, hq, ?_⟩
  funext q
  simp only [qAppendOne, Novel.EnvSemantics.injC, beq_iff_eq]

/-- **The injection on counts**: one token more in the injected place, nowhere else, from a
marking that marks no terminal place, into an environment place. -/
theorem inject_stepStopInj {C : Cfg PlaceId T} {s s' : XSt PlaceId T} {k : Nat}
    (h : RefExec C s (.inject k) s') (he : EqEnvs C s) (net : FlatNet) :
    Novel.TerminalRewrite.StepStopInjRel net C.envs C.terminals (qCount s.M) (qCount s'.M) := by
  obtain ⟨p, x, rest, hq, hl, -, -, rfl⟩ := injectStep_some h
  refine ⟨noTerm_of_liveB hl, Or.inr ⟨p, he _ (by rw [hq]; exact List.mem_cons_self), ?_⟩⟩
  funext q
  simp only [qCount, qAppendOne, beq_iff_eq]
  split <;> simp

/-- **Live-consistent start** (the restriction of L6 and L8): `t` is enabled on the live marking
too, and no same-pass deposit sits on a place it resets or drains. -/
def LiveConsistent (s : XSt PlaceId T) (t : Trans PlaceId) : Prop :=
  enabledNA (qCount s.M) t.core = true ∧
    ∀ p, (p ∈ t.core.resets ∨ (nspecAt t.core p).any (·.card.consumesAll) = true) →
      s.delta p = 0

/-- A live-consistent start leaves the intermediate marking of the live counts. -/
theorem qCount_liveAfter {s : XSt PlaceId T} {t : Trans PlaceId} (hd : DeltaLe s)
    (hen : enabledNA (qCount (vis s)) t.core = true) (hlc : LiveConsistent s t) :
    qCount (liveAfter s t) = mid t (qCount s.M) := by
  funext p
  have hv := qCount_vis_add hd p
  show (liveAfter s t p).length = _
  simp only [liveAfter, List.length_append, hid_length hd]
  rw [show (qConsume (vis s) t p).length = qCount (qConsume (vis s) t) p from rfl,
    qCount_qConsume]
  unfold mid fireNC nconsumed
  by_cases hres : p ∈ t.core.resets
  · simp [hres, hlc.2 p (Or.inl hres)]
  · simp only [hres, if_false]
    cases hs : nspecAt t.core p with
    | none => simp only; omega
    | some sp =>
      simp only
      by_cases hca : sp.card.consumesAll = true
      · have h0 := hlc.2 p (Or.inr (by simp [hs, hca]))
        simp only [hca, if_true]
        omega
      · simp only [hca, Bool.false_eq_true, if_false]
        obtain ⟨hmem, hpl⟩ := nspecAt_place hs
        unfold enabledNA at hen
        simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hen
        have := hen.1.1 sp hmem
        rw [hpl] at this
        omega

/-- **An atomic segment**: the head `t` of the pass order starts (`start n sy`), steps that leave
the marking alone follow (`ms`: the action's writes and return, the end of the pass, step 1's
other bookkeeping), and the commit of that firing (identity `s.nextId`, emission `e`) settles it;
`t` is live-consistent at `s`. -/
def AtomicSeg (C : Cfg PlaceId T) (s : XSt PlaceId T) (t : Trans PlaceId)
    (e : List (PlaceId × T)) (s' : XSt PlaceId T) : Prop :=
  ∃ n sy ms s₁, s.order.head? = some t ∧ xrun C s (.start n sy :: ms) = some s₁ ∧
    (∀ l ∈ ms, l.marks = false) ∧ (∃ f ∈ s₁.fl, f.id = s.nextId ∧ f.out = some (.ok e)) ∧
    RefExec C s₁ (.commit s.nextId) s' ∧ LiveConsistent s t

/-- **An atomic segment is one firing on the counts**: from a marking that marks no terminal
place, `t` is enabled on the live counts and the segment leaves `fireNC` of them with the
emission's places. -/
theorem atomicSeg_count {C : Cfg PlaceId T} {s s' : XSt PlaceId T} {t : Trans PlaceId}
    {e : List (PlaceId × T)} (hi : IdsFresh s) (hd : DeltaLe s) (h : AtomicSeg C s t e s') :
    liveB C s = true ∧ enabledNA (qCount s.M) t.core = true ∧
      qCount s'.M = fireNC (qCount s.M) t.core (depProd (e.map Prod.fst)) := by
  obtain ⟨n, sy, ms, s₁, hhead, hrun, hmid, ⟨g, hg, hgi, hge⟩, hc, hlc⟩ := h
  obtain ⟨s₀, h0, h1⟩ := xrun_cons.mp hrun
  obtain ⟨t', rest, ho, -, hl, -, -, -, hen, hs₀⟩ := startStep_some (P := refXPol) h0
  have htt : t' = t := by rw [ho] at hhead; simpa using hhead
  subst htt
  have hM₀ : qCount s₀.M = mid t' (qCount s.M) := by
    rw [hs₀]; exact qCount_liveAfter hd hen hlc
  have hM₁ : s₁.M = s₀.M := xrun_M_frame h1 hmid
  have hi₁ := (idsFresh_deltaLe_xrun hrun ⟨hi, hd⟩).1
  obtain ⟨f, e', hfind, he', -, -, -, hs'⟩ := commitStep_some (P := refXPol) hc
  have hfm := List.mem_of_find?_eq_some hfind
  have hfi : f.id = s.nextId := by simpa using List.find?_some hfind
  have hfg : f = g := List.inj_on_of_nodup_map hi₁.1 hfm hg (by rw [hfi, hgi])
  subst hfg
  have hee : e' = e := by rw [he'] at hge; simpa using hge
  subst hee
  refine ⟨hl, hlc.1, ?_⟩
  funext p
  rw [hs', fireNC_eq_mid_add, ← hM₀, ← hM₁, count_map_fst]
  exact qCount_qAppend _ _ p

/-- The invariants the L8 run argument carries. -/
def RunInv (C : Cfg PlaceId T) (s : XSt PlaceId T) : Prop :=
  IdsFresh s ∧ DeltaLe s ∧ EqEnvs C s

/-- One step keeps them. -/
theorem runInv_step {C : Cfg PlaceId T} {s s' : XSt PlaceId T} {l : XLbl PlaceId T}
    (h : RefExec C s l s') (hi : RunInv C s) : RunInv C s' :=
  let h2 := idsFresh_deltaLe_step h hi.1 hi.2.1
  ⟨h2.1, h2.2, eqEnvs_step h hi.2.2⟩

/-- A decided run keeps them. -/
theorem runInv_xrun {C : Cfg PlaceId T} {s s' : XSt PlaceId T} {ls : List (XLbl PlaceId T)}
    (h : xrun C s ls = some s') (hi : RunInv C s) : RunInv C s' :=
  let h2 := idsFresh_deltaLe_xrun h ⟨hi.1, hi.2.1⟩
  ⟨h2.1, h2.2, eqEnvs_xrun h hi.2.2⟩

/-- They hold initially. -/
theorem runInv_xinit (C : Cfg PlaceId T) (M0 : QMarking PlaceId T) (r0 : Nat) :
    RunInv C (xinit M0 r0) :=
  ⟨(idsFresh_deltaLe_xinit M0 r0).1, (idsFresh_deltaLe_xinit M0 r0).2,
    fun _ h => absurd h List.not_mem_nil⟩

/-- An atomic segment keeps them. -/
theorem runInv_atomicSeg {C : Cfg PlaceId T} {s s' : XSt PlaceId T} {t : Trans PlaceId}
    {e : List (PlaceId × T)} (h : AtomicSeg C s t e s') (hi : RunInv C s) : RunInv C s' := by
  obtain ⟨n, sy, ms, s₁, -, hrun, -, -, hc, -⟩ := h
  exact runInv_step hc (runInv_xrun hrun hi)

/-- **Atomic runs** over the flat net `net`: steps that leave the marking alone, injections, and
atomic segments whose row (the started transition with the emission's places, one token per
place) is a row of `net`. -/
inductive ARun (C : Cfg PlaceId T) (net : FlatNet) : XSt PlaceId T → XSt PlaceId T → Prop
  /-- No step. -/
  | refl (s : XSt PlaceId T) : ARun C net s s
  /-- A step that leaves the marking alone. -/
  | frame {s s₁ s' : XSt PlaceId T} {l : XLbl PlaceId T} :
      RefExec C s l s₁ → l.marks = false → ARun C net s₁ s' → ARun C net s s'
  /-- An injection. -/
  | inject {s s₁ s' : XSt PlaceId T} {k : Nat} :
      RefExec C s (.inject k) s₁ → ARun C net s₁ s' → ARun C net s s'
  /-- An atomic firing of a row of `net`. -/
  | fire {s s₁ s' : XSt PlaceId T} {t : Trans PlaceId} {e : List (PlaceId × T)} :
      AtomicSeg C s t e s₁ → (toTransition t.core, e.map Prod.fst) ∈ net →
      (e.map Prod.fst).Nodup → ARun C net s₁ s' → ARun C net s s'

/-- An atomic run is a decided run. -/
theorem aRun_xrun {C : Cfg PlaceId T} {net : FlatNet} {s s' : XSt PlaceId T}
    (h : ARun C net s s') : ∃ ls, xrun C s ls = some s' := by
  induction h with
  | refl s => exact ⟨[], rfl⟩
  | @frame s s₁ s' l h1 _ _ ih =>
    obtain ⟨ls, hls⟩ := ih
    exact ⟨l :: ls, xrun_cons.mpr ⟨s₁, h1, hls⟩⟩
  | @inject s s₁ s' k h1 _ ih =>
    obtain ⟨ls, hls⟩ := ih
    exact ⟨.inject k :: ls, xrun_cons.mpr ⟨s₁, h1, hls⟩⟩
  | @fire s s₁ s' t e hseg _ _ _ ih =>
    obtain ⟨ls, hls⟩ := ih
    obtain ⟨n, sy, ms, s₂, -, hrun, -, -, hc, -⟩ := hseg
    refine ⟨(.start n sy :: ms) ++ .commit s.nextId :: ls, xrun_append.mpr ⟨s₂, hrun, ?_⟩⟩
    exact xrun_cons.mpr ⟨s₁, hc, hls⟩

/-- **L8, runs** ([EXEC-042], [ENV-003]): the counts of an atomic run are a run of the strict-stop
relation with injection over `net` and the configuration's environment and terminal places. -/
theorem aRun_reachStopInj {C : Cfg PlaceId T} {net : FlatNet} {s s' : XSt PlaceId T}
    (h : ARun C net s s') (hi : RunInv C s) :
    Novel.TerminalRewrite.ReachStopInj net C.envs C.terminals (qCount s.M) (qCount s'.M) := by
  induction h with
  | refl s => exact Relation.ReflTransGen.refl
  | @frame s s₁ s' l h1 hl _ ih =>
    have hM : s₁.M = s.M := xstepW_M_frame h1 hl
    have := ih (runInv_step h1 hi)
    rwa [hM] at this
  | @inject s s₁ s' k h1 _ ih =>
    exact Relation.ReflTransGen.head (inject_stepStopInj h1 hi.2.2 net) (ih (runInv_step h1 hi))
  | @fire s s₁ s' t e hseg hrow hnd _ ih =>
    obtain ⟨hl, hen, hM⟩ := atomicSeg_count hi.1 hi.2.1 hseg
    refine Relation.ReflTransGen.head ⟨noTerm_of_liveB hl, Or.inl ⟨_, hrow, ?_, ?_⟩⟩
      (ih (runInv_atomicSeg hseg hi))
    · rw [enabledA_toTransition]; exact hen
    · rw [← Novel.ForwardDeposit.fireAD_eq_fireA hnd, fireAD_toTransition, hM]

/-- **L8, the verified net**: the counts of every atomic run from an initial state are reachable
in the verified net's injected relation (`TerminalRewrite.terminal_rewrite_sound_inj`), the
relation the injection rules encode. -/
theorem aRun_verified {C : Cfg PlaceId T} {net : FlatNet} {M0 : QMarking PlaceId T} {r0 : Nat}
    {s : XSt PlaceId T} (h : ARun C net (xinit M0 r0) s) :
    ReachAInj (Novel.TerminalRewrite.verifiedNet C.terminals net) C.envs (qCount M0)
      (qCount s.M) :=
  Novel.TerminalRewrite.terminal_rewrite_sound_inj net C.envs C.terminals
    (aRun_reachStopInj h (runInv_xinit C M0 r0))

end L8

/-! ## L6: rests of atomic runs are rests of `ReapAware`'s cycle model

`ReapAware.Cycle` fires atomically from the live marking (`FireStep`: `enabledA b ft.1`), so a
cycle of the reference executor projects to it only when every firing of the cycle is atomic and
enabled on the live marking (exec map CORRECTED 2; `corrected2_witness` below shows the pass-visible
recheck reaching a marking no atomic order reaches). On those runs (`ARun` without injections,
no environment place, as `ReapAware` has none), every marking the executor comes to rest at (the
termination test with nothing armed, in flight or queued, where `finish quiescent` is offered) is
untimed-reachable and reap-quiescent (`atomic_rest_sound`): reachable by L8, and every enabled
transition there is reaped (InvU at the test, with nothing in flight) and reaped only if its
timing is reapable (`ReapedReapable`). Under valid timings that is a rest of `ReapAware`'s model
(`atomic_restsAt`), so `rest_sound` and `reap_aware_ac3` read it: `restsAt_of_reach` builds the
model's run, one cycle per firing with every cell dirty.

The projection is made at the level of rests: the executor's own cycles are not mapped one to one
onto `Cycle`'s cells (the executor's statuses carry restart flags and reaped marks the cell model
spells differently); what `rest_sound` concludes is proved of the executor directly. -/

section L6

variable {T : Type}

/-- The executor's timing read on flat transitions (by name): the earliest bound, and for a
reapable timing the reap threshold, latest bound plus tolerance ([TIME-013]). -/
def flatTiming (C : Cfg PlaceId T) : Transition → Novel.ReapAware.TTiming := fun t =>
  match findT C t.name with
  | some u => ⟨(C.X.timing u).earliest,
      if (C.X.timing u).reapable then some ((C.X.timing u).latest + C.X.tol) else none⟩
  | none => ⟨0, none⟩

/-- The flat reading is reapable exactly when the net's timing is. -/
theorem reapable_flatTiming {C : Cfg PlaceId T} (hN : NamesDistinct C.X) {u : Trans PlaceId}
    (hu : u ∈ C.X.net.transitions) :
    Novel.ReapAware.reapable (flatTiming C) (toTransition u.core) = (C.X.timing u).reapable := by
  unfold Novel.ReapAware.reapable flatTiming
  rw [show (toTransition u.core).name = u.core.name from rfl, findT_of_mem hN hu]
  cases hr : (C.X.timing u).reapable <;> simp [hr]

/-- Under valid timings ([TIME-001] AC4) the reap threshold is never below the earliest bound. -/
theorem flatTiming_ok {C : Cfg PlaceId T}
    (hV : ∀ u ∈ C.X.net.transitions, (C.X.timing u).Valid) :
    ∀ t l, (flatTiming C t).latest = some l → (flatTiming C t).earliest ≤ l := by
  intro t l h
  unfold flatTiming at h ⊢
  cases hf : findT C t.name with
  | none => simp [hf] at h
  | some u =>
    simp only [hf] at h ⊢
    have hv := hV u (findT_spec hf).1
    revert h hv
    cases C.X.timing u <;>
      simp [Novel.TimedScg.Timing.reapable, Novel.TimedScg.Timing.earliest,
        Novel.TimedScg.Timing.latest, Novel.TimedScg.Timing.Valid]
    omega

end L6

section L6rest

variable {N T : Type} [DecidableEq N]

/-- **At a rest every enabled transition is reapable** ([EXEC-040], [TIME-013]): at the
termination test of a reachable state with nothing armed, in flight or queued, a transition of
the net that the marking enables is reaped, so its timing is reapable. -/
theorem rest_reapable {C : Cfg N T} (hN : NamesDistinct C.X) {M0 : QMarking N T} {r0 : Nat}
    {ls : List (XLbl N T)} {s : XSt N T} (h : xrun C (xinit M0 r0) ls = some s)
    (hp : s.phase = .test) (hrest : restB C s = true) :
    ∀ u ∈ C.X.net.transitions, enabledNA (qCount s.M) u.core = true →
      (C.X.timing u).reapable = true := by
  obtain ⟨-, hoff, -⟩ := invU_boundary hN h (Or.inr hp)
  have hrr := reapedReapable_xrun hN h (fun n hn => by simp [xinit] at hn)
  unfold restB at hrest
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', List.isEmpty_iff] at hrest
  obtain ⟨⟨⟨⟨hna, hfl⟩, -⟩, -⟩, -⟩ := hrest
  intro u hu hen
  have hf := findT_of_mem hN hu
  cases hst : s.st u.core.name with
  | off =>
    have := (hoff _ u hf hst hen).1
    simp [inFlightN, hfl] at this
  | armed k r =>
    have := hna u hu
    simp [armedB, hen, hst, stampOf] at this
  | reaped =>
    obtain ⟨u', hf', hr⟩ := hrr _ hst
    rw [hf] at hf'
    cases hf'
    exact hr

end L6rest

section L6atomic

variable {T : Type}

/-- **L6, rest soundness of atomic runs** (the conclusion of `ReapAware.rest_sound`, for the
executor): with no environment place, the marking of every rest of an atomic run from an initial
state is reachable in the untimed flat net and reap-quiescent under the executor's timing. -/
theorem atomic_rest_sound {C : Cfg PlaceId T} (hN : NamesDistinct C.X) (henv : C.envs = [])
    {net : FlatNet} (hnet : ∀ ft ∈ net, ∃ u ∈ C.X.net.transitions, ft.1 = toTransition u.core)
    {M0 : QMarking PlaceId T} {r0 : Nat} {s : XSt PlaceId T} (h : ARun C net (xinit M0 r0) s)
    (hp : s.phase = .test) (hrest : restB C s = true) :
    ReachA net (qCount M0) (qCount s.M) ∧
      Novel.ReapAware.ReapQuiescentA (Novel.ReapAware.reapable (flatTiming C)) net (qCount s.M) := by
  refine ⟨?_, ?_⟩
  · have h1 := aRun_reachStopInj h (runInv_xinit C M0 r0)
    unfold Novel.TerminalRewrite.ReachStopInj at h1
    unfold ReachA
    have hle : Novel.TerminalRewrite.StepStopInjRel net C.envs C.terminals ≤ StepARel net := by
      intro a b hab
      rcases hab.2 with hs | ⟨p, hp, -⟩
      · exact hs
      · rw [henv] at hp; exact absurd hp List.not_mem_nil
    exact Relation.ReflTransGen.mono hle _ _ h1
  · obtain ⟨ls, hls⟩ := aRun_xrun h
    intro ft hft hen
    obtain ⟨u, hu, hft1⟩ := hnet ft hft
    rw [hft1, reapable_flatTiming hN hu]
    rw [hft1, enabledA_toTransition] at hen
    exact rest_reapable hN hls hp hrest u hu hen

/-- The cells of the constructed runs: armed at clock 0, dirty. -/
def warmCells : Transition → Cell := fun _ => ⟨false, true, some 0, true⟩

/-- On the warm cells the update leaves exactly the enabled transitions armed at 0. -/
theorem upd_warm (now : Nat) (b : AMarking) (t : Transition) :
    Novel.ReapAware.upd now ⟨b, warmCells⟩ t =
      if enabledA b t then ⟨true, true, some 0, false⟩ else ⟨false, false, none, false⟩ := by
  unfold Novel.ReapAware.upd updateCell warmCells
  cases enabledA b t <;> rfl

/-- One atomic firing is one cycle of the model, at the firing's earliest bound. -/
theorem cycle_fire {tm : Transition → Novel.ReapAware.TTiming} {net : FlatNet}
    (htm : ∀ t l, (tm t).latest = some l → (tm t).earliest ≤ l) {b : AMarking}
    {ft : FlatTransition} (hft : ft ∈ net) (hen : enabledA b ft.1 = true) :
    Novel.ReapAware.Cycle enforceBB tm net (tm ft.1).earliest ⟨b, warmCells⟩
      ⟨fireA b ft.1 ft.2, warmCells⟩ := by
  have hcell : Novel.ReapAware.enf enforceBB tm (tm ft.1).earliest ⟨b, warmCells⟩ ft.1 =
      ⟨true, true, some 0, false⟩ := by
    unfold Novel.ReapAware.enf
    rw [upd_warm, hen]
    cases hl : (tm ft.1).latest with
    | none => rfl
    | some l =>
      have := htm ft.1 l hl
      simp only [enforceBB, reaps, deadlineExpired, Nat.sub_zero, Bool.true_and,
        decide_eq_true_eq, if_true]
      rw [if_neg (by omega)]
  refine ⟨fun hh => ?_, Relation.ReflTransGen.single ⟨ft, hft, ?_, hen, rfl⟩, fun _ _ => Or.inl rfl,
    fun _ _ _ _ => rfl⟩
  · have := hh ft hft
    rw [hcell] at this
    exact absurd this (by simp)
  · rw [hcell]
    simp [fires, windowOpen]

/-- **The model rests at every reachable reap-quiescent marking**: one warm-up cycle, one cycle
per firing, then a halting test late enough that every enabled (reapable) transition is reaped. -/
theorem restsAt_of_reach {tm : Transition → Novel.ReapAware.TTiming} {net : FlatNet}
    (htm : ∀ t l, (tm t).latest = some l → (tm t).earliest ≤ l) {a0 a : AMarking}
    (hr : ReachA net a0 a)
    (hq : Novel.ReapAware.ReapQuiescentA (Novel.ReapAware.reapable tm) net a) :
    Novel.ReapAware.RestsAt enforceBB tm net a0 a := by
  -- a late test: past every reap threshold of the net
  let late : Nat := (net.map fun ft => (tm ft.1).latest.getD 0).sum + 1
  have hlate : ∀ ft ∈ net, ∀ l, (tm ft.1).latest = some l → l < late := by
    intro ft hft l hl
    have : (tm ft.1).latest.getD 0 ≤ (net.map fun ft => (tm ft.1).latest.getD 0).sum :=
      List.le_sum_of_mem (List.mem_map.mpr ⟨ft, hft, rfl⟩)
    rw [hl] at this
    simp only [Option.getD_some] at this
    omega
  have hhalt : Novel.ReapAware.Halts enforceBB tm net late ⟨a, warmCells⟩ := by
    intro ft hft
    unfold Novel.ReapAware.enf
    rw [upd_warm]
    cases hen : enabledA a ft.1
    · cases (tm ft.1).latest <;> rfl
    · have hrp := hq ft hft hen
      unfold Novel.ReapAware.reapable at hrp
      obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp hrp
      have := hlate ft hft l hl
      simp only [hl, if_true, enforceBB, reaps, deadlineExpired, Nat.sub_zero, Bool.true_and]
      rw [if_pos (by simpa using this)]
  -- the firings, one cycle each, from the warm cells
  have hruns : ∀ c, ReachA net a0 c →
      Novel.ReapAware.Runs enforceBB tm net ⟨a0, warmCells⟩ ⟨c, warmCells⟩ := by
    intro c hc
    unfold ReachA at hc
    induction hc with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hs ih =>
      obtain ⟨ft, hft, hen, rfl⟩ := hs
      exact Relation.ReflTransGen.tail ih ⟨_, cycle_fire htm hft hen⟩
  by_cases hex : ∃ ft ∈ net, enabledA a0 ft.1 = true
  · obtain ⟨ft, hft, hen⟩ := hex
    have hwarm : Novel.ReapAware.Cycle enforceBB tm net 0 ⟨a0, Novel.ReapAware.initCells⟩
        ⟨a0, warmCells⟩ := by
      refine ⟨fun hh => ?_, Relation.ReflTransGen.refl, fun _ _ => Or.inl rfl, fun _ _ _ _ => rfl⟩
      have := hh ft hft
      unfold Novel.ReapAware.enf Novel.ReapAware.upd updateCell Novel.ReapAware.initCells at this
      rw [hen] at this
      cases hl : (tm ft.1).latest <;> simp_all [enforceBB, reaps, deadlineExpired]
    exact ⟨⟨a, warmCells⟩, late,
      Relation.ReflTransGen.head ⟨0, hwarm⟩ (hruns a hr), hhalt, rfl⟩
  · -- nothing is enabled initially, so nothing ever fires
    have ha : a = a0 := by
      rcases Relation.ReflTransGen.cases_head hr with h0 | ⟨c, ⟨ft, hft, hen, -⟩, -⟩
      · exact h0.symm
      · exact absurd ⟨ft, hft, hen⟩ hex
    subst ha
    refine ⟨⟨a, Novel.ReapAware.initCells⟩, 0, Relation.ReflTransGen.refl, fun ft hft => ?_, rfl⟩
    have hen : enabledA a ft.1 = false := by
      cases h : enabledA a ft.1
      · rfl
      · exact absurd ⟨ft, hft, h⟩ hex
    unfold Novel.ReapAware.enf Novel.ReapAware.upd updateCell Novel.ReapAware.initCells
    rw [hen]
    cases (tm ft.1).latest <;> simp [enforceBB, reaps]

/-- **L6, the link** ([VER-002], [VER-004] AC3, [EXEC-040]): with no environment place and
valid timings, every rest of an atomic run of the reference executor is a rest of `ReapAware`'s
cycle model over the same flat net and the executor's timing, so `ReapAware.rest_sound` and
`reap_aware_ac3` apply to it. -/
theorem atomic_restsAt {C : Cfg PlaceId T} (hN : NamesDistinct C.X) (henv : C.envs = [])
    (hV : ∀ u ∈ C.X.net.transitions, (C.X.timing u).Valid) {net : FlatNet}
    (hnet : ∀ ft ∈ net, ∃ u ∈ C.X.net.transitions, ft.1 = toTransition u.core)
    {M0 : QMarking PlaceId T} {r0 : Nat} {s : XSt PlaceId T} (h : ARun C net (xinit M0 r0) s)
    (hp : s.phase = .test) (hrest : restB C s = true) :
    Novel.ReapAware.RestsAt enforceBB (flatTiming C) net (qCount M0) (qCount s.M) :=
  let hs := atomic_rest_sound hN henv hnet h hp hrest
  restsAt_of_reach (flatTiming_ok hV) hs.1 hs.2

/-! ### The restriction is needed (exec map CORRECTED 2)

Two synchronous transitions, each depositing into the other's inhibitor place: `a` takes place 0,
is inhibited by place 2 and outputs place 3; `b` takes place 1, is inhibited by place 3 and
outputs place 2. In one pass `a` starts and settles inline, and `b` still starts, because the
pass-visible marking does not show `a`'s deposit in place 3 ([EXEC-003] AC3). The executor then
comes to rest with places 2 and 3 both marked. No order of atomic firings reaches that marking:
after either firing the other is inhibited. So this rest is not a rest of `ReapAware`'s model,
and the live-consistency hypothesis of L6 and L8 cannot be dropped (the second start is enabled
on the visible marking only). -/

/-- Transition `a` of the witness. -/
def c2A : Trans Nat :=
  { core := { name := "a", inputs := [⟨0, .one⟩], inhibitors := [2], reads := [], resets := [] },
    out := some (.place 3) }

/-- Transition `b` of the witness. -/
def c2B : Trans Nat :=
  { core := { name := "b", inputs := [⟨1, .one⟩], inhibitors := [3], reads := [], resets := [] },
    out := some (.place 2) }

/-- The witness configuration: `a` and `b`, immediate, no environment or terminal place, the
reference validator. -/
def c2C : Cfg Nat Nat :=
  { X := { net := { places := [0, 1, 2, 3], transitions := [c2A, c2B] },
           timing := fun _ => .immediate, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [], reentrant := false,
    validate := cfgValidate ioRefValidate, relay := fun _ _ _ => true,
    timeoutOut := fun _ _ _ => false, res := 0 }

/-- The witness's initial marking: one token in places 0 and 1. -/
def c2M : QMarking Nat Nat := fun p => if p = 0 ∨ p = 1 then [5] else []

/-- The witness run: one pass in which `a` and `b` both start and settle inline, then the next
cycle to its termination test. -/
def c2Labels : List (XLbl Nat Nat) :=
  initLabels ++ [.deadline [], .begin, .start "a" true, .write 0 3 7, .ret 0 true, .commit 0,
    .start "b" true, .write 1 2 7, .ret 1 true, .commit 1, .endPass, .endCompletions,
    .endPublications, .endEvents, .update, .deadline []]

/-- The witness's flat net: `a` and `b` with their one output place each. -/
def c2Net : FlatNet := [(toTransition c2A.core, [3]), (toTransition c2B.core, [2])]

/-- The untimed flat net keeps places 0 and 3, and places 1 and 2, at one token each, and never
empties both input places. -/
theorem c2_inv {a : AMarking} (h : ReachA c2Net (qCount c2M) a) :
    a 0 + a 3 = 1 ∧ a 1 + a 2 = 1 ∧ 1 ≤ a 0 + a 1 := by
  unfold ReachA at h
  induction h with
  | refl => simp [qCount, c2M]
  | tail _ hs ih =>
    obtain ⟨ft, hft, hen, rfl⟩ := hs
    simp only [c2Net, List.mem_cons, List.mem_nil_iff, or_false] at hft
    rcases hft with rfl | rfl <;>
      simp [enabledA, fireA, toTransition, toInSpec, c2A, c2B, pre, specAt, consumeAllAt, post,
        Card.required, Card.consumesAll] at hen ⊢ <;> omega

/-- **CORRECTED 2, decided**: the reference executor rests (termination test, nothing armed, in
flight or queued) at a marking with places 2 and 3 marked and places 0 and 1 empty, which the
untimed flat net does not reach; so it is not a rest of `ReapAware`'s cycle model either. -/
theorem corrected2_witness :
    ∃ s, xrun c2C (xinit c2M 0) c2Labels = some s ∧ s.phase = .test ∧ restB c2C s = true ∧
      qCount s.M 2 = 1 ∧ qCount s.M 3 = 1 ∧ ¬ ReachA c2Net (qCount c2M) (qCount s.M) ∧
      ¬ Novel.ReapAware.RestsAt enforceBB (flatTiming c2C) c2Net (qCount c2M) (qCount s.M) := by
  have h1 : (xrun c2C (xinit c2M 0) c2Labels).isSome = true := by decide
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp h1
  have h2 : (xrun c2C (xinit c2M 0) c2Labels).map
      (fun s => (decide (s.phase = .test), restB c2C s, qCount s.M 0, qCount s.M 1, qCount s.M 2,
        qCount s.M 3)) = some (true, true, 0, 0, 1, 1) := by decide
  rw [hs] at h2
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq] at h2
  obtain ⟨hp, hr, h0, h1', h2', h3⟩ := h2
  have hnr : ¬ ReachA c2Net (qCount c2M) (qCount s.M) := fun h => by
    have := (c2_inv h).2.2
    omega
  exact ⟨s, hs, hp, hr, h2', h3, hnr, fun h => hnr (Novel.ReapAware.rest_sound h).1⟩

end L6atomic

/-! ## The links apply to real runs (non-vacuity of L5, L6 and L8)

On the example of L3 (`linkC`: one transition `t` from place 0 to place 1), the run to the first
termination test, the pass with one synchronous firing of `t` settled inline, and the next cycle
to its termination test is an atomic run that comes to rest; so `atomic_rest_sound`,
`atomic_restsAt` and `aRun_verified` hold of a real run. A trace that ends with `t` in flight
meets `RowsCover`, so `count_projection` gives a marking of `InFlight.XStep` with `t` pending. -/

section NonVacuous

/-- Steps that leave the marking alone form an atomic run. -/
theorem aRun_of_frames {T : Type} {C : Cfg PlaceId T} {net : FlatNet} :
    ∀ {s s' : XSt PlaceId T} {ls : List (XLbl PlaceId T)}, xrun C s ls = some s' →
      (∀ l ∈ ls, l.marks = false) → ∀ {s'' : XSt PlaceId T}, ARun C net s' s'' → ARun C net s s''
  | s, s', [], h, _, _, hr => by cases h; exact hr
  | s, s', l :: ls, h, hl, _, hr => by
    obtain ⟨s₁, h1, h2⟩ := xrun_cons.mp h
    exact ARun.frame h1 (hl l List.mem_cons_self)
      (aRun_of_frames h2 (fun l' h' => hl l' (List.mem_cons_of_mem _ h')) hr)

/-- The example's flat net: `t` with its output place. -/
def linkNet : FlatNet := [(toTransition linkT.core, [1])]

/-- The labels of the pass, after `begin`: the synchronous start, the action's write and return,
and the inline commit. -/
def linkSeg : List (XLbl Nat Nat) := [.start "t" true, .write 0 1 7, .ret 0 true, .commit 0]

/-- The labels from the end of the pass to the next termination test. -/
def linkPost : List (XLbl Nat Nat) :=
  [.endPass, .endCompletions, .endPublications, .endEvents, .update, .deadline []]

/-- **L6 and L8 are not vacuous**: the example run is an atomic run that comes to rest at a
termination test with the token moved to place 1. -/
theorem link_aRun_nonvacuous :
    ∃ s, ARun linkC linkNet (xinit linkM 0) s ∧ s.phase = .test ∧ restB linkC s = true ∧
      qCount s.M 0 = 0 ∧ qCount s.M 1 = 1 := by
  -- to the start of the pass
  have hB : (xrun linkC (xinit linkM 0) (linkPre ++ [.begin])).isSome = true := by decide
  obtain ⟨sB, hsB⟩ := Option.isSome_iff_exists.mp hB
  obtain ⟨sT, hsT, hbeg⟩ := xrun_append.mp hsB
  obtain ⟨sB', hbeg', hnil⟩ := xrun_cons.mp hbeg
  cases hnil
  obtain ⟨-, -, -, -, hsB'⟩ := xstepW_begin (P := refXPol) hbeg'
  have hdelta : ∀ p, sB.delta p = 0 := by rw [hsB']; intro p; rfl
  have hord : sB.order = readyOrder linkC sT := by rw [hsB']
  -- the pass
  have hS : (xrun linkC sB linkSeg).isSome = true := by
    have : ((xrun linkC (xinit linkM 0) (linkPre ++ [.begin])).bind fun s =>
      xrun linkC s linkSeg).isSome = true := by decide
    rw [hsB] at this; exact this
  obtain ⟨s₂, hs₂⟩ := Option.isSome_iff_exists.mp hS
  obtain ⟨s₁, hs₁, hc⟩ := xrun_append.mp (show xrun linkC sB
    ([.start "t" true, .write 0 1 7, .ret 0 true] ++ [.commit 0]) = some s₂ from hs₂)
  obtain ⟨s₂', hc', hnil⟩ := xrun_cons.mp hc
  cases hnil
  have hchk : ((xrun linkC (xinit linkM 0) (linkPre ++ [.begin])).bind fun s =>
      (xrun linkC s [.start "t" true, .write 0 1 7, .ret 0 true]).map fun s₁ =>
        (s.order.length, s.nextId, enabledNA (qCount s.M) linkT.core,
          s₁.fl.any fun f => f.id == 0 && match f.out with
            | some (.ok e) => e == [(1, 7)]
            | _ => false)) = some (1, 0, true, true) := by decide
  rw [hsB, Option.bind_some, hs₁, Option.map_some, Option.some.injEq, Prod.mk.injEq,
    Prod.mk.injEq, Prod.mk.injEq] at hchk
  obtain ⟨hlen, hnext, hen, hret⟩ := hchk
  have hhead : sB.order.head? = some linkT := by
    cases ho : sB.order with
    | nil => rw [ho] at hlen; simp at hlen
    | cons u rest =>
      have hu : u ∈ readyOrder linkC sT := by rw [← hord, ho]; exact List.mem_cons_self
      have := (mem_readyOrder hu).1
      simp only [linkC, List.mem_singleton] at this
      rw [this]; rfl
  have hseg : AtomicSeg linkC sB linkT [(1, 7)] s₂ := by
    refine ⟨"t", true, [.write 0 1 7, .ret 0 true], s₁, hhead, hs₁, by decide, ?_, ?_, hen,
      fun p _ => hdelta p⟩
    · obtain ⟨f, hf, hfc⟩ := List.any_eq_true.mp hret
      simp only [Bool.and_eq_true, beq_iff_eq] at hfc
      obtain ⟨hfi, hfo⟩ := hfc
      refine ⟨f, hf, hnext ▸ hfi, ?_⟩
      revert hfo
      rcases f.out with _ | (e | _ | e) <;> simp
    · rw [hnext]; exact hc'
  -- to the next termination test
  have hE : ((xrun linkC (xinit linkM 0) (linkPre ++ [.begin] ++ linkSeg ++ linkPost)).map
      fun s => (decide (s.phase = .test), restB linkC s, qCount s.M 0, qCount s.M 1)) =
      some (true, true, 0, 1) := by decide
  have hpost : (xrun linkC s₂ linkPost).isSome = true := by
    have : ((xrun linkC (xinit linkM 0) (linkPre ++ [.begin] ++ linkSeg)).bind fun s =>
      xrun linkC s linkPost).isSome = true := by decide
    rw [xrun_append.mpr ⟨sB, hsB, hs₂⟩] at this
    exact this
  obtain ⟨sE, hsE⟩ := Option.isSome_iff_exists.mp hpost
  rw [xrun_append.mpr ⟨s₂, xrun_append.mpr ⟨sB, hsB, hs₂⟩, hsE⟩] at hE
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq] at hE
  obtain ⟨hp, hr, h0, h1⟩ := hE
  refine ⟨sE, ?_, hp, hr, h0, h1⟩
  refine aRun_of_frames hsB (by decide) ?_
  exact ARun.fire hseg (by simp [linkNet]) (by decide)
    (aRun_of_frames hsE (by decide) (ARun.refl _))

/-- The example's rest is a rest of `ReapAware`'s model, through `atomic_restsAt`. -/
theorem link_restsAt_nonvacuous :
    ∃ s, ARun linkC linkNet (xinit linkM 0) s ∧ qCount s.M 1 = 1 ∧
      Novel.ReapAware.RestsAt enforceBB (flatTiming linkC) linkNet (qCount linkM) (qCount s.M) := by
  obtain ⟨s, h, hp, hr, -, h1⟩ := link_aRun_nonvacuous
  refine ⟨s, h, h1, atomic_restsAt (by unfold NamesDistinct; decide) rfl
    (fun u _ => by simp [linkC, Novel.TimedScg.Timing.Valid]) (fun ft hft => ?_) h hp hr⟩
  simp only [linkNet, List.mem_singleton] at hft
  exact ⟨linkT, by simp [linkC], by rw [hft]⟩

/-- A decided trace lists its labels. -/
theorem xtrace_labels {T : Type} {C : Cfg PlaceId T} :
    ∀ {s : XSt PlaceId T} {ls : List (XLbl PlaceId T)} {tr : List (XStep PlaceId T)},
      xtrace C s ls = some tr → tr.map (·.2.1) = ls
  | s, [], tr, h => by cases h; rfl
  | s, l :: ls, tr, h => by
    simp only [xtrace] at h
    cases hs : xstep C s l with
    | none => simp [hs] at h
    | some s' =>
      simp only [hs, Option.bind_some] at h
      cases ht : xtrace C s' ls with
      | none => simp [ht] at h
      | some tr' =>
        simp only [ht, Option.map_some, Option.some.injEq] at h
        subst h
        simp [xtrace_labels ht]

/-- **L5 is not vacuous**: the example trace to a pass with `t` started meets `RowsCover` (it
settles nothing), and its counts are a marking of `InFlight.XStep` with `t` pending. -/
theorem link_hoist_nonvacuous :
    ∃ tr, xtrace linkC (xinit linkM 0) (linkPre ++ [.begin, .start "t" true]) = some tr ∧
      ∃ pend, Novel.InFlight.XReach linkNet (NoTerm linkC) (qCount linkM)
        ⟨qCount (XRun.last (xinit linkM 0) tr).M, pend⟩ ∧ pend = ["t"] := by
  have h1 : (xtrace linkC (xinit linkM 0) (linkPre ++ [.begin, .start "t" true])).isSome = true := by
    decide
  obtain ⟨tr, ht⟩ := Option.isSome_iff_exists.mp h1
  have hc : ∀ y ∈ tr, RowsCover linkNet y := by
    intro y hy
    have hl : y.2.1 ∈ linkPre ++ [.begin, .start "t" true] := by
      rw [← xtrace_labels ht]; exact List.mem_map_of_mem hy
    unfold RowsCover
    simp only [linkPre, initLabels, List.cons_append, List.nil_append, List.mem_cons,
      List.mem_nil_iff, or_false] at hl
    rcases hl with h | h | h | h | h | h | h <;> rw [h] <;> trivial
  obtain ⟨pend, hx, hpp⟩ := count_projection (fun u hu => ⟨[1], by
    simp only [linkC, List.mem_singleton] at hu; simp [linkNet, hu]⟩) (xtrace_run ht) hc
  have hfl : ((xrun linkC (xinit linkM 0) (linkPre ++ [.begin, .start "t" true])).map
      fun s => s.fl.map (·.t.core.name)) = some ["t"] := by decide
  rw [xtrace_last ht, Option.map_some, Option.some.injEq] at hfl
  refine ⟨tr, ht, pend, hx, ?_⟩
  have := hpp.length_eq
  simp only [flNames, hfl, List.length_cons, List.length_nil] at this
  match pend, this with
  | [n], _ =>
    have := hpp.mem_iff.mp List.mem_cons_self
    simp only [flNames, hfl, List.mem_singleton] at this
    rw [this]

end NonVacuous

end Libpetri.Reference
