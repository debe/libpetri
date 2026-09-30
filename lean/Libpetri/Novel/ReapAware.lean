import Libpetri.Novel.ReapingVsUntimed
import Libpetri.Novel.Seam.Bad

/-!
# Reap-aware quiescence restores [VER-004] AC3 ([VER-002], [TIME-013])

`ReapingVsUntimed.lean` showed that AC3 fails for the quiescence properties when quiescence is
read as "no transition enabled": a `Deadline` / `Window` transition past its latest bound is
reaped (its enabled bit cleared, its tokens left in place), and the executor then comes to rest
at a marking where the untimed net still enables it. The fix shipped in every language reads
quiescence as **reap-quiescence**: a marking is quiescent when every transition it enables is
*reapable* (timing `Deadline` or `Window`). The flat encoder skips reapable transitions in
`encode_quiescent` (`smt_encoder.rs`, the `ft.reapable` `continue`).

This module proves that reading sound for every timed execution, over a general executor model
built from `TimedCycle.lean`'s per-transition cell.

**The executor model** (`Cycle`). State: the marking and one `Cell` per transition. One cycle at
clock reading `now` (any `Nat`, so any schedule, monotone or not, [TIME-015]):

1. *update enablement*: `updateCell` on every transition, with `tokens` refreshed from the live
   marking (it is read only on a dirty cell, as `can_enable` is);
2. *enforce deadlines*: a reapable transition (timing with a latest bound `l`) goes through
   `enforce l now`: `enforceBB`, which both shipped backends run since the [TIME-013] ruling,
   or `enforcePB`, the precompiled path before it (it also marked the reaped transition dirty,
   `TimedCycle.lean`); any other transition is never reaped ([TIME-006], [TIME-013]);
3. *termination*: if no transition of the net has its enabled bit set, the loop stops
   (`run_sync`'s `enabled_count() == 0` break, `run_async`'s same test with nothing in flight);
   the run **rests** at the current marking;
4. *fire*: otherwise any number of firings, each of a transition whose cell passes `fires`
   (bit set, window open) and which is enabled on the live marking (`recheck_can_fire`), with any
   outcome row of the flat net. Afterwards every transition that reads a place whose count
   changed is dirty (`mark_place_dirty`), and a bit set after enforcement is cleared only with a
   dirty mark; clocks and further dirty bits are left to the adversary.

The proofs never read what `enforce` does to a reapable transition's cell, so they hold for
`enforceBB`, `enforcePB`, and any other reaping rule: soundness needs only that non-reapable
transitions are never reaped.

Everything the model leaves open — the clock readings, which ready transitions fire and in what
order, the outcome, extra dirty bits — is chosen by the adversary, so every run of either
backend on an atomic-firing net (`run_sync` with sync actions, no environment places) is a run of
the model. As in `ReapingVsUntimed.MarkingFaithful`, an async action that consumes at start and
deposits at completion is outside the model; the verifier reads the in-flight split net for
the transitions where that matters (`InFlight.lean`), which is again a net of atomic rows. The
two results are not composed: `InFlight.lean` is untimed, and that a timed run whose actions
span cycles is a run of this model over the split net (the start keeps the timing, the
completion step is immediate and never reapable) is argued in prose only.

One untimed graph route applies the same reading: `open_net/graph_route.rs::decide_on_graph`
counts a class of the open net's closed graph ([VER-022]) as a rest when every transition it
enables is reapable. That graph is built untimed, so its classes are the untimed reachable
markings, and `reap_aware_ac3` is what makes its `Proven` hold for the executor's rests.

`scg_verifier.rs::decide_over_state_space_reaping` reads a built graph the same way, but it
produces no `Proven` that rests on this module. Its only caller with a reapable set is the
[VER-023] timed check, `smt_verifier.rs::timed_counterexample_check`. That check builds the
on-time **timed** graph of the verified net (`StateClassGraphOptions { untimed: false }`) and only
annotates a `Violated`; it never turns a verdict into `Proven`. The reap-aware bad contains the
strict one (`reapQuiescent_of_quiescent`), so reading that graph reap-aware only adds rests, and
`SPURIOUS_UNDER_TIMING` (no on-time run reaches a violating rest) stays sound for the on-time
runs the graph holds. The graph does not hold the runs a late executor takes after a reap, so
that annotation says nothing about them. The [VER-017] enumeration does not use the reap-aware
reading: it runs only when `scg_verifier::is_untimed` holds, when every transition is immediate
and none is reapable, and it calls `decide_over_state_space`, the wrapper that passes an empty
set. With nothing reapable the two readings agree (`reap_quiescent_iff_quiescent`).
`SmtVerifier::reapable_set` names the reapable transitions for every route (the net's `deadline`
and `window` transitions, `reaping::reapable_transitions`; none under `assume_no_reaping`), and
`open_net/verify_open_net.rs::verify_open_net` names them the same way on the closed net for both
of its routes.

Results:
* `cycle_inv` / `run_inv`: the invariant "every enabled transition has its bit set, is dirty,
  or is reapable" holds at the start of every cycle.
* **`rest_sound`**: every marking at which a run comes to rest is untimed-reachable **and
  reap-quiescent**.
* **`reap_aware_ac3`**: a `Proven` for `ReapQuiescentA ∧ Q` over the untimed reachable set
  implies `¬ Q` at every marking any timed run rests at — [VER-004] AC3 for the quiescence
  properties. `marking_ac3` is the marking-property half (every visited marking is reachable).
* **`witness_caught`**: on `ReapingVsUntimed.lean`'s witness, the model's run `[0, 10]` rests at
  `{p₀}` (`witness_rests`, both backends), `{p₀}` is reap-quiescent, and the reap-aware
  `DeadlockFree` violation holds there, so the reap-aware verdict is `Violated`, not `Proven`.
  The strict `Bad` is not violated there (`reaping_refutes_ver004_ac3`), which is the old gap.
* **`reap_quiescent_iff_quiescent`**: with no reapable transition, reap-quiescence is the strict
  quiescence, so nothing changes on untimed nets.
* **Seam**: `quiescentBad_filter_iff` / `deadlockBad_filter_eq` — `Seam.Bad`'s encoded
  quiescence and `DeadlockFree` violation over the flat net *without* its reapable rows (what
  `encode_quiescent` now emits) are exactly reap-quiescence and a stranded token;
  `reapDeadlockBad_iff` is the named reading.
-/

namespace Libpetri.Novel.ReapAware

open Libpetri Libpetri.Novel.ReapingVsUntimed Libpetri.Novel.Seam

/-! ## Reap-quiescence -/

/-- **Reap-quiescent** ([VER-002]): every flat transition the marking enables is reapable. -/
def ReapQuiescentA (rp : Transition → Bool) (net : FlatNet) (a : AMarking) : Prop :=
  ∀ ft ∈ net, enabledA a ft.1 = true → rp ft.1 = true

/-- Strict quiescence implies reap-quiescence. -/
theorem reapQuiescent_of_quiescent {rp : Transition → Bool} {net : FlatNet} {a : AMarking}
    (h : QuiescentA net a) : ReapQuiescentA rp net a := by
  intro ft hft hen
  rw [h ft hft] at hen
  exact absurd hen Bool.false_ne_true

/-- **No reapable transition, no change**: reap-quiescence is strict quiescence. -/
theorem reap_quiescent_iff_quiescent {rp : Transition → Bool} {net : FlatNet}
    (hnr : ∀ ft ∈ net, rp ft.1 = false) (a : AMarking) :
    ReapQuiescentA rp net a ↔ QuiescentA net a := by
  refine ⟨fun h ft hft => ?_, reapQuiescent_of_quiescent⟩
  cases hen : enabledA a ft.1 with
  | false => rfl
  | true =>
    have := h ft hft hen
    rw [hnr ft hft] at this
    exact absurd this Bool.false_ne_true

/-! ## The executor model -/

/-- A transition's timing at the granularity the executor reads: the earliest firing offset
([TIME-010]) and, for `Deadline` / `Window`, the reap threshold `latest + tolerance`
([TIME-013]; `none` for `Immediate`, `Delayed`, `Exact`, which are never reaped). -/
structure TTiming where
  earliest : Nat
  latest   : Option Nat

/-- Reapable: the timing has a latest bound (`Deadline` or `Window`). -/
def reapable (tm : Transition → TTiming) (t : Transition) : Bool := (tm t).latest.isSome

/-- The executor state at the start of a cycle: the marking and one cell per transition. -/
structure XState where
  a     : AMarking
  cells : Transition → Cell

/-- `initialize`: nothing enabled, everything dirty (`mark_all_dirty`). -/
def initCells : Transition → Cell :=
  fun _ => { tokens := false, enabled := false, clock := none, dirty := true }

/-- Phase 1: the dirty-gated update, `tokens` refreshed from the live marking. -/
def upd (now : Nat) (s : XState) (t : Transition) : Cell :=
  updateCell now { s.cells t with tokens := enabledA s.a t }

/-- Phase 2: deadline enforcement, only on reapable transitions. -/
def enf (enforce : Nat → Nat → Cell → Cell) (tm : Transition → TTiming) (now : Nat)
    (s : XState) (t : Transition) : Cell :=
  match (tm t).latest with
  | some l => enforce l now (upd now s t)
  | none => upd now s t

/-- The loop's termination test after enforcement: no transition of the net is enabled. -/
def Halts (enforce : Nat → Nat → Cell → Cell) (tm : Transition → TTiming) (net : FlatNet)
    (now : Nat) (s : XState) : Prop :=
  ∀ ft ∈ net, (enf enforce tm now s ft.1).enabled = false

/-- One firing of the fire phase: the transition passes the ready gate on its post-enforcement
cell and `recheck_can_fire` on the live marking, and some outcome row is deposited. -/
def FireStep (enforce : Nat → Nat → Cell → Cell) (tm : Transition → TTiming) (net : FlatNet)
    (now : Nat) (s : XState) (b b' : AMarking) : Prop :=
  ∃ ft ∈ net, fires (tm ft.1).earliest now (enf enforce tm now s ft.1) = true ∧
    enabledA b ft.1 = true ∧ b' = fireA b ft.1 ft.2

/-- The places whose count a transition's enablement reads: inputs, inhibitors, reads. -/
def Touches (t : Transition) (p : PlaceId) : Prop :=
  p ∈ t.inputs.map InSpec.place ∨ p ∈ t.inhibitors ∨ p ∈ t.reads

/-- **One running cycle** from `s` to `s'` at clock `now`: the loop did not stop, the fire
phase moved the marking from `s.a` to `s'.a` by zero or more firings, and the cells afterwards
are anything that keeps two rules of both backends: a bit set after enforcement is cleared only
together with a dirty mark (`post_fire` dirties the fired transition; an [EXEC-003] loser's
input place changed), and every transition touching a changed place is dirty
(`mark_place_dirty`). Clocks, `tokens` and extra dirty bits are free. -/
def Cycle (enforce : Nat → Nat → Cell → Cell) (tm : Transition → TTiming) (net : FlatNet)
    (now : Nat) (s s' : XState) : Prop :=
  ¬ Halts enforce tm net now s ∧
    Relation.ReflTransGen (FireStep enforce tm net now s) s.a s'.a ∧
    (∀ t, (enf enforce tm now s t).enabled = true →
      (s'.cells t).enabled = true ∨ (s'.cells t).dirty = true) ∧
    (∀ t p, Touches t p → s.a p ≠ s'.a p → (s'.cells t).dirty = true)

/-- The runs: cycles at arbitrary clock readings. -/
def Runs (enforce : Nat → Nat → Cell → Cell) (tm : Transition → TTiming) (net : FlatNet) :
    XState → XState → Prop :=
  Relation.ReflTransGen fun s s' => ∃ now, Cycle enforce tm net now s s'

/-- A run from `a0` **rests** at `a`: it reaches a cycle whose termination test stops the loop,
at marking `a`. -/
def RestsAt (enforce : Nat → Nat → Cell → Cell) (tm : Transition → TTiming) (net : FlatNet)
    (a0 a : AMarking) : Prop :=
  ∃ s now, Runs enforce tm net ⟨a0, initCells⟩ s ∧ Halts enforce tm net now s ∧ s.a = a

/-! ## The invariant -/

/-- Every enabled transition has its bit set, is dirty, or is reapable. -/
def Inv (tm : Transition → TTiming) (net : FlatNet) (s : XState) : Prop :=
  ∀ ft ∈ net, enabledA s.a ft.1 = true →
    (s.cells ft.1).enabled = true ∨ (s.cells ft.1).dirty = true ∨ reapable tm ft.1 = true

theorem inv_init (tm : Transition → TTiming) (net : FlatNet) (a0 : AMarking) :
    Inv tm net ⟨a0, initCells⟩ :=
  fun _ _ _ => Or.inr (Or.inl rfl)

/-- After the update an enabled transition's bit is set, unless it is reapable. -/
theorem upd_enabled {tm : Transition → TTiming} {net : FlatNet} {s : XState}
    (hi : Inv tm net s) (now : Nat) {ft : FlatTransition} (hft : ft ∈ net)
    (hen : enabledA s.a ft.1 = true) :
    (upd now s ft.1).enabled = true ∨ reapable tm ft.1 = true := by
  rcases hi ft hft hen with h | h | h
  · left
    unfold upd updateCell
    split
    · split
      · rfl
      · split
        · rename_i _ _ h2
          simp [hen] at h2
        · exact h
    · exact h
  · left
    unfold upd updateCell
    simp only [h, if_true, hen, Bool.true_and]
    cases hc : (s.cells ft.1).enabled <;> simp
  · right; exact h

/-- Enforcement touches only reapable transitions: whatever `enforce` does (either backend, or
any other), a bit it leaves set is set, and one it clears belongs to a reapable transition. -/
theorem enf_enabled (enforce : Nat → Nat → Cell → Cell)
    (tm : Transition → TTiming) (now : Nat) (s : XState) (t : Transition)
    (h : (upd now s t).enabled = true) :
    (enf enforce tm now s t).enabled = true ∨ reapable tm t = true := by
  unfold enf reapable
  cases hl : (tm t).latest with
  | none => left; exact h
  | some l => right; rfl

/-- **At the termination test every enabled transition is reapable.** -/
theorem halts_reapQuiescent {enforce : Nat → Nat → Cell → Cell}
    {tm : Transition → TTiming} {net : FlatNet} {s : XState} {now : Nat}
    (hi : Inv tm net s) (hh : Halts enforce tm net now s) :
    ReapQuiescentA (reapable tm) net s.a := by
  intro ft hft hen
  rcases upd_enabled hi now hft hen with h | h
  · rcases enf_enabled enforce tm now s ft.1 h with h' | h'
    · rw [hh ft hft] at h'; exact absurd h' Bool.false_ne_true
    · exact h'
  · exact h

/-- Enablement reads only the touched places. -/
theorem enabledA_congr {t : Transition} {a b : AMarking} (h : ∀ p, Touches t p → a p = b p) :
    enabledA a t = enabledA b t := by
  unfold enabledA
  have h1 : t.inputs.all (fun s => s.card.required ≤ a s.place)
      = t.inputs.all (fun s => s.card.required ≤ b s.place) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true, decide_eq_true_eq]
    exact forall_congr' fun s => forall_congr' fun hs => by
      rw [h s.place (Or.inl (List.mem_map.mpr ⟨s, hs, rfl⟩))]
  have h2 : t.inhibitors.all (fun p => a p == 0) = t.inhibitors.all (fun p => b p == 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    exact forall_congr' fun p => forall_congr' fun hp => by rw [h p (Or.inr (Or.inl hp))]
  have h3 : t.reads.all (fun p => 1 ≤ a p) = t.reads.all (fun p => 1 ≤ b p) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true, decide_eq_true_eq]
    exact forall_congr' fun p => forall_congr' fun hp => by rw [h p (Or.inr (Or.inr hp))]
  rw [h1, h2, h3]

/-- A cycle preserves the invariant. -/
theorem cycle_inv {enforce : Nat → Nat → Cell → Cell}
    {tm : Transition → TTiming} {net : FlatNet} {now : Nat} {s s' : XState}
    (hi : Inv tm net s) (hc : Cycle enforce tm net now s s') : Inv tm net s' := by
  obtain ⟨_, _, hkeep, hD⟩ := hc
  intro ft hft hen'
  by_cases hen : enabledA s.a ft.1 = true
  · rcases upd_enabled hi now hft hen with h | h
    · rcases enf_enabled enforce tm now s ft.1 h with h' | h'
      · rcases hkeep ft.1 h' with h'' | h''
        · exact Or.inl h''
        · exact Or.inr (Or.inl h'')
      · exact Or.inr (Or.inr h')
    · exact Or.inr (Or.inr h)
  · right; left
    by_contra hnd
    apply hen
    rw [enabledA_congr (b := s'.a) (fun p hp => ?_)]
    · exact hen'
    · by_contra hne
      exact hnd (hD ft.1 p hp hne)

/-- The fire phase moves the marking only by untimed firings of the net. -/
theorem firePhase_reach {enforce : Nat → Nat → Cell → Cell} {tm : Transition → TTiming}
    {net : FlatNet} {now : Nat} {s : XState} {a0 b b' : AMarking} (hr : ReachA net a0 b)
    (h : Relation.ReflTransGen (FireStep enforce tm net now s) b b') : ReachA net a0 b' := by
  induction h with
  | refl => exact hr
  | tail _ hs ih =>
    obtain ⟨ft, hft, _, hen, rfl⟩ := hs
    exact ReachA.step ih hft hen

/-- Every state of a run satisfies the invariant and has an untimed-reachable marking. -/
theorem run_inv {enforce : Nat → Nat → Cell → Cell}
    {tm : Transition → TTiming} {net : FlatNet} {a0 : AMarking} {s : XState}
    (h : Runs enforce tm net ⟨a0, initCells⟩ s) : Inv tm net s ∧ ReachA net a0 s.a := by
  induction h with
  | refl => exact ⟨inv_init tm net a0, ReachA.init⟩
  | tail _ hs ih =>
    obtain ⟨now, hc⟩ := hs
    exact ⟨cycle_inv ih.1 hc, firePhase_reach ih.2 hc.2.1⟩

/-- **Soundness of reap-aware quiescence.** Every marking at which a timed run of either
backend comes to rest is untimed-reachable and reap-quiescent. -/
theorem rest_sound {enforce : Nat → Nat → Cell → Cell}
    {tm : Transition → TTiming} {net : FlatNet} {a0 a : AMarking}
    (h : RestsAt enforce tm net a0 a) :
    ReachA net a0 a ∧ ReapQuiescentA (reapable tm) net a := by
  obtain ⟨s, now, hr, hh, rfl⟩ := h
  obtain ⟨hi, hreach⟩ := run_inv hr
  exact ⟨hreach, halts_reapQuiescent hi hh⟩

theorem rest_sound_BB {tm : Transition → TTiming} {net : FlatNet} {a0 a : AMarking}
    (h : RestsAt enforceBB tm net a0 a) :
    ReachA net a0 a ∧ ReapQuiescentA (reapable tm) net a :=
  rest_sound h

theorem rest_sound_PB {tm : Transition → TTiming} {net : FlatNet} {a0 a : AMarking}
    (h : RestsAt enforcePB tm net a0 a) :
    ReachA net a0 a ∧ ReapQuiescentA (reapable tm) net a :=
  rest_sound h

/-- **[VER-004] AC3 for the quiescence properties, restored.** A quiescence property's reap-aware
`Bad` is `ReapQuiescentA ∧ Q` (`Q` the stranding / sink / count clause). A `Proven` for it over
the untimed reachable set means no timed run of either backend ever rests at a marking with
`Q`. -/
theorem reap_aware_ac3 {enforce : Nat → Nat → Cell → Cell}
    {tm : Transition → TTiming} {net : FlatNet} {a0 : AMarking} {Q : AMarking → Prop}
    (hp : ProvenFor (ReachA net a0) (fun a => ReapQuiescentA (reapable tm) net a ∧ Q a))
    {a : AMarking} (h : RestsAt enforce tm net a0 a) : ¬ Q a := by
  obtain ⟨hr, hq⟩ := rest_sound h
  exact fun hQ => hp a hr ⟨hq, hQ⟩

/-- **[VER-004] AC3 for the marking properties**: a `Proven` for any predicate of the marking
holds at every cycle start of every run. -/
theorem marking_ac3 {enforce : Nat → Nat → Cell → Cell}
    {tm : Transition → TTiming} {net : FlatNet} {a0 : AMarking} {Bad : AMarking → Prop}
    (hp : ProvenFor (ReachA net a0) Bad) {s : XState}
    (h : Runs enforce tm net ⟨a0, initCells⟩ s) : ¬ Bad s.a :=
  hp _ (run_inv h).2

/-- The same for every marking inside a fire phase. -/
theorem marking_ac3_phase {enforce : Nat → Nat → Cell → Cell}
    {tm : Transition → TTiming} {net : FlatNet} {a0 : AMarking} {Bad : AMarking → Prop}
    (hp : ProvenFor (ReachA net a0) Bad) {s : XState} {now : Nat} {b : AMarking}
    (h : Runs enforce tm net ⟨a0, initCells⟩ s)
    (hb : Relation.ReflTransGen (FireStep enforce tm net now s) s.a b) : ¬ Bad b :=
  hp _ (firePhase_reach (run_inv h).2 hb)

/-! ## The witness is caught -/

/-- `ReapingVsUntimed.lean`'s witness timing: `t = window(3, 5)` (tolerance folded in). -/
def tmR : Transition → TTiming := fun _ => { earliest := 3, latest := some 5 }

/-- The reap-aware `DeadlockFree` violation: reap-quiescent, and a token stranded off the
sinks. -/
def reapDlfBad (rp : Transition → Bool) (net : FlatNet) (sinks : List PlaceId) (n : Nat)
    (a : AMarking) : Prop :=
  ReapQuiescentA rp net a ∧ Strands sinks n a

/-- **The model's run `[0, 10]` of the witness rests at `{p₀}`**, under the shipped reaping rule
and the pre-ruling precompiled one (`witness_rests_PB`): cycle 0
enables `t` and fires nothing (the window opens at 3); cycle 10 reaps it, and the loop stops. -/
theorem witness_rests_BB : RestsAt enforceBB tmR netR a0R a0R := by
  refine ⟨⟨a0R, fun t => { enf enforceBB tmR 0 ⟨a0R, initCells⟩ t with dirty := false }⟩, 10,
    ?_, ?_, rfl⟩
  · refine Relation.ReflTransGen.single ⟨0, ?_, Relation.ReflTransGen.refl,
      fun _ h => Or.inl h, fun _ _ _ hne => absurd rfl hne⟩
    intro hh
    have := hh (tR, [1]) (by simp [netR])
    revert this
    decide
  · intro ft hft
    have : ft = (tR, [1]) := by simpa [netR] using hft
    subst this
    decide

theorem witness_rests_PB : RestsAt enforcePB tmR netR a0R a0R := by
  refine ⟨⟨a0R, fun t => { enf enforcePB tmR 0 ⟨a0R, initCells⟩ t with dirty := false }⟩, 10,
    ?_, ?_, rfl⟩
  · refine Relation.ReflTransGen.single ⟨0, ?_, Relation.ReflTransGen.refl,
      fun _ h => Or.inl h, fun _ _ _ hne => absurd rfl hne⟩
    intro hh
    have := hh (tR, [1]) (by simp [netR])
    revert this
    decide
  · intro ft hft
    have : ft = (tR, [1]) := by simpa [netR] using hft
    subst this
    decide

/-- **The old witness is caught.** The timed run rests at `{p₀}` (both backends); `{p₀}` is
reap-quiescent and strands a token off the sink `{p₁}`, so the reap-aware `DeadlockFree` `Bad`
holds at the (reachable) initial marking and the reap-aware verdict is not `Proven` — while the
strict `Bad` is `Proven` (`reaping_refutes_ver004_ac3`). -/
theorem witness_caught :
    RestsAt enforceBB tmR netR a0R a0R ∧ RestsAt enforcePB tmR netR a0R a0R
    ∧ reapDlfBad (reapable tmR) netR sinksR 2 a0R
    ∧ ¬ ProvenFor (ReachA netR a0R) (reapDlfBad (reapable tmR) netR sinksR 2)
    ∧ ProvenFor (ReachA netR a0R) (dlfBad netR sinksR 2) := by
  have hbad : reapDlfBad (reapable tmR) netR sinksR 2 a0R :=
    ⟨fun _ _ _ => rfl, 0, by decide, by decide, by decide⟩
  exact ⟨witness_rests_BB, witness_rests_PB, hbad, fun hp => hp a0R ReachA.init hbad,
    untimed_dlf_proven⟩

/-- The soundness theorem agrees on the witness: it predicts exactly what the run shows. -/
theorem witness_rest_reapQuiescent :
    ReachA netR a0R a0R ∧ ReapQuiescentA (reapable tmR) netR a0R :=
  rest_sound_BB witness_rests_BB

/-! ## The encoded `Bad` over the net without its reapable rows (`Seam.Bad`) -/

/-- **`encode_quiescent` skipping reapable rows is reap-quiescence.** -/
theorem quiescentBad_filter_iff {p : Nat} {flat : FlatNet} (rp : Transition → Bool)
    (hok : ∀ ft ∈ flat, FlatOK p ft.1) (a : AMarking) :
    quiescentBad p (flat.filter (fun ft => !rp ft.1)) a = true ↔ ReapQuiescentA rp flat a := by
  rw [quiescentBad_iff (fun ft hft => hok ft (List.mem_filter.mp hft).1)]
  constructor
  · intro h ft hft hen
    by_contra hr
    have := h ft (List.mem_filter.mpr ⟨hft, by simpa using hr⟩)
    rw [hen] at this; exact Bool.noConfusion this
  · intro h ft hft
    obtain ⟨hmem, hnr⟩ := List.mem_filter.mp hft
    cases hen : enabledA a ft.1 with
    | false => rfl
    | true =>
      have := h ft hmem hen
      simp [this] at hnr

/-- **`DeadlockFree`'s encoded `Bad` without the reapable rows** is reap-quiescence and a
stranded token. -/
theorem deadlockBad_filter_eq {N : Type} [DecidableEq N] {flat : FlatNet} (ix : PlaceIndex N)
    (rp : Transition → Bool) (hok : ∀ ft ∈ flat, FlatOK ix.size ft.1) (sinks : List N)
    (cond : List (CondSinks N)) (a : AMarking) :
    deadlockBad (flat.filter (fun ft => !rp ft.1)) ix sinks cond a = true ↔
      ReapQuiescentA rp flat a ∧
      ∃ i < ix.size, ∃ ms, strandingExcuses ix sinks cond i = some ms ∧ 1 ≤ a i ∧
        ∀ k ∈ ms, a k = 0 := by
  rw [deadlockBad_eq, quiescentBad_filter_iff rp hok]

/-- The named net without its reapable transitions. -/
def liveNet {N : Type} (rpN : NTransition N → Bool) (net : NNet N) : NNet N :=
  { places := net.places, transitions := net.transitions.filter (fun ft => !rpN ft.1) }

/-- Named reap-quiescence: every enabled transition is reapable. -/
def NReapQuiescent {N : Type} [DecidableEq N] (rpN : NTransition N → Bool) (net : NNet N)
    (m : N → Nat) : Prop :=
  ∀ ft ∈ net.transitions, enabledNA m ft.1 = true → rpN ft.1 = true

theorem nQuiescent_liveNet_iff {N : Type} [DecidableEq N] (rpN : NTransition N → Bool)
    (net : NNet N) (m : N → Nat) :
    NQuiescent (liveNet rpN net) m ↔ NReapQuiescent rpN net m := by
  unfold NQuiescent NReapQuiescent liveNet
  constructor
  · intro h ft hft hen
    by_contra hr
    have := h ft (List.mem_filter.mpr ⟨hft, by simpa using hr⟩)
    rw [hen] at this; exact Bool.noConfusion this
  · intro h ft hft
    obtain ⟨hmem, hnr⟩ := List.mem_filter.mp hft
    cases hen : enabledNA m ft.1 with
    | false => rfl
    | true =>
      have := h ft hmem hen
      simp [this] at hnr

/-- **The named reading**: on a covered marking, the encoded `DeadlockFree` violation of the net
without its reapable transitions holds iff the named marking is reap-quiescent and strands a
token. -/
theorem reapDeadlockBad_iff {N : Type} [DecidableEq N] {ix : PlaceIndex N} {net : NNet N}
    (rpN : NTransition N → Bool) (hA : ArcsIn ix net) (hD : InputsDistinct net)
    (sinks : List N) (cond : List (CondSinks N)) {m : N → Nat} (h : Covers ix m) :
    deadlockBad (flatNet ix (liveNet rpN net)) ix sinks cond (restrict ix m) = true ↔
      NReapQuiescent rpN net m ∧ ∃ n, m n ≠ 0 ∧ ¬ Resting sinks cond m n := by
  have hA' : ArcsIn ix (liveNet rpN net) :=
    fun ft hft => hA ft (List.mem_filter.mp hft).1
  have hD' : InputsDistinct (liveNet rpN net) :=
    fun ft hft => hD ft (List.mem_filter.mp hft).1
  rw [deadlockBad_iff hA' hD' sinks cond h, NDeadlock, nQuiescent_liveNet_iff]

end Libpetri.Novel.ReapAware
