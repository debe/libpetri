import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryTime
import Libpetri.Spec.Text.TIME_002

set_option linter.missingDocs true

/-!
# TIME-002: Immediate timing (`spec/03-timing.md`)

The requirement is a predicate over an abstract timed step relation `R : TRel N` (glossary
`GlossaryTime.lean`). For each transition of the net with timing `Immediate` it says three
things: the transition may fire whenever it is armed, however long it has been armed; no step
disarms it while it stays enabled; and no step reaps it.

The evidence theorems check the statement against the timed reference step (`RefTStep`),
against an executor that never fires, against one whose firing disarms a still-enabled armed
transition it does not write, and against the mutant reading that treats `Immediate` as a
deadline at the maximum duration, its finite `latest()`.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Novel.TimedScg (Timing maxDurationMs)

/-! ## TIME-002: Immediate timing -/

requirement TIME_002
  id "TIME-002"
  title "Immediate Timing"
  kind T
  scope "all executors"
  source verbatim "spec/03-timing.md"
  covers TIME_002.s1, TIME_002.s2
  reading "For every timed net X and every transition u the net holds under its name, with timing Immediate:"
          "while u is armed, the step relation has every firing of u that the reference semantics has, with the same successor marking;"
          "no step disarms u while it stays enabled (StaysArmed): when the net's names are distinct, every step other than a reap of u, a firing of u itself included, leaves u armed if u was armed before it and is enabled after it;"
          "the step relation has no reap of u."
  assumes "A step relates two states of the executor (glossary: TSt); a step is a delay of the clock, a firing or a reap (TRel). Firings are atomic, and the relation may be late: a delay may pass any bound. Armed, Elapsed time, Ready and Reapable are the glossary terms (GlossaryTime.lean)."
          "Line 1 is the first 'shall' sentence. Readiness is read through the step relation: a transition whose timing does not stop it is one the relation may fire. Immediate has earliest bound 0 and is not reapable, so it is ready whenever it is armed, at every elapsed time, also past its finite latest() (the maximum duration). The firing order among ready transitions (priority, FIFO) is EXEC-002 and is not part of an atomic step."
          "Line 2 is the same sentence for steps that would make u not ready by disarming it while it stays enabled, whatever the label of the step; TIME_002_forbids_drop shows a firing of another transition that drops u's stamp, and TIME_002_forbids_selfDrop a firing of u itself that leaves u enabled and unarmed. It is the frame StaysArmed shared with TIME-003 to TIME-006 (GlossaryTime.lean); its exception for the reap of u is empty here, by line 3. Distinct names (NamesDistinct, ruling D10) are needed because stamps are kept per name, so the reap of another transition of the same name would drop u's stamp. A firing that leaves u enabled re-arms it, possibly with a fresh stamp (TIME-012); this line says only that u stays armed."
          "Line 3 is the second 'shall' sentence: no reap step of u exists at all. Together with line 2 it excludes a reap under another label."
          "The interval [0, ∞), earliest() = 0, latest() = maximum duration and hasDeadline() = false are the Timing accessors (time002_interval, cited); the reading of the maximum duration as no bound (ruling D11) is what line 1 and line 3 state for the executor."
          "AC1 (fires immediately when enabled) is read as readiness, line 1, exercised in TIME_002_nonvacuous at elapsed time 0. Line 1 speaks of an armed transition; 'when enabled' becomes 'when armed' only through TIME-010 (a transition enabled in the initial marking or after a firing that writes one of its arc places is newly armed) and TIME-012, which ConsistencyTime conjoins: an executor that never arms a newly enabled Immediate transition meets this block on its own. That it fires on the next cycle, before any other ready transition, is the eager Phase 2 executor's and EXEC-002's, not an atomic step's (ruling D3). AC2 (no deadline enforcement) is lines 2 and 3, exercised in TIME_002_nonvacuous past the maximum duration plus the tolerance, where u is still armed, still fires and has no reap."
  signoff "2026-11-13 d2b484cbad973046 ai"
  statement : ∀ {N : Type} [DecidableEq N], TRel N → Prop :=
    fun R => ∀ (X : TimedNet _) (u : Trans _), InNet X u → TimingOf X u = .immediate →
      (∀ s d m', Armed s u → RefFire u s.m d m' → ∃ s', R X s (.fire u d) s' ∧ s'.m = m') ∧
      StaysArmed R X u ∧
      (∀ s s', ¬ R X s (.reap u) s')

/- The pinned readable form of TIME-002: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.TIME_002 : {N : Type} → [DecidableEq N] → TRel N → Prop :=
fun {N} [DecidableEq N] R =>
  ∀ (X : TimedNet N) (u : Reference.Trans N),
    InNet X u →
      TimingOf X u = Timing.immediate →
        (∀ (s : TSt N) (d : List N) (m' : N → ℕ),
            Armed s u → RefFire u s.m d m' → ∃ s', R X s (TLbl.fire u d) s' ∧ s'.m = m') ∧
          StaysArmed R X u ∧ ∀ (s s' : TSt N), ¬R X s (TLbl.reap u) s'
-/
#guard_msgs in #print TIME_002

/-! ### The lines, for any policy -/

section Lines

variable {N : Type} [DecidableEq N]

/-- An armed transition of the net with earliest bound 0, not expired under `P`, takes every
reference firing it has, under any policy with the spec's gate. -/
theorem time002_fires {P : Policy N} (hg : P.gate = refPolicy.gate) {X : TimedNet N}
    {u : Trans N} (hu : InNet X u) (h0 : (X.timing u).earliest = 0) {s : TSt N} {d : List N}
    {m' : N → Nat} (ha : Armed s u) (hx : P.expired X s u = false) (hf : RefFire u s.m d m') :
    ∃ s', RefTStepW P X s (.fire u d) s' ∧ s'.m = m' :=
  ⟨_, RefTStepW.fire X s u d m' (inNet_mem hu) hf ((armed_iff s u).1 ha)
    (by rw [hg]; simp [refPolicy, h0]) hx, rfl⟩

/-- A reap, under any policy, starts from a state in which its transition is expired and drops
its stamp, so the transition is not armed after it. -/
theorem time002_reap_inv {P : Policy N} {X : TimedNet N} {u : Trans N} {s s' : TSt N}
    (h : RefTStepW P X s (.reap u) s') : P.expired X s u = true ∧ ¬ Armed s' u := by
  cases h with
  | reap _ _ hx => exact ⟨hx, fun ha => by simpa using ha.2⟩

/-- The spec never finds an `Immediate` transition expired: it is not reapable. -/
theorem time002_refUnexpired {X : TimedNet N} {u : Trans N} (hi : X.timing u = .immediate)
    (s : TSt N) : (refPolicy (N := N)).expired X s u = false := by
  simp [refPolicy, tExpired, hi, Timing.reapable]

end Lines

/-- The timed reference step satisfies TIME-002: an `Immediate` transition has earliest bound 0
and is never expired under `refPolicy` (it is not reapable), so an armed one fires with every
reference firing (line 1), no reap of it exists (line 3), and every other step leaves it armed
if it is enabled after (line 2, `staysArmed_of`). -/
@[evidence holds TIME_002]
theorem TIME_002_reference {N : Type} [DecidableEq N] : TIME_002 (RefTStep (N := N)) := by
  intro X u hu hi
  have hnr : ∀ s s', ¬ RefTStep X s (.reap u) s' := fun s s' h => by
    have := (time002_reap_inv h).1
    rw [time002_refUnexpired hi] at this
    exact Bool.noConfusion this
  refine ⟨fun s d m' ha hf => time002_fires rfl hu (by simp [hi, Timing.earliest]) ha
    (time002_refUnexpired hi s) hf, staysArmed_of rfl hu, hnr⟩

/-! ### Examples (AC1, AC2) -/

/-- The transition of the examples: one input arc on place `0`, no output spec. -/
def time002_u : Trans Nat :=
  { core := { name := "u", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- The timed net of the examples: `u` with `Immediate` timing and the default tolerance of
5 ms. -/
def time002_X : TimedNet Nat :=
  { net := { places := [0], transitions := [time002_u] }, timing := fun _ => .immediate, tol := 5 }

theorem time002_u_inX : InNet time002_X time002_u := rfl

theorem time002_namesDistinct : NamesDistinct time002_X := by unfold NamesDistinct; decide

/-- The state at clock reading `n`: one token in `u`'s input place, `u` armed since `0`. -/
def time002_at (n : Nat) : TSt Nat :=
  { m := fun p => if p = 0 then 1 else 0, now := n,
    stamp := fun k => if k = "u" then some 0 else none }

/-- `u` is armed at every clock reading. -/
theorem time002_armed (n : Nat) : Armed (time002_at n) time002_u :=
  ⟨by show Enabled time002_u (fun p : Nat => if p = 0 then 1 else 0); decide,
    by simp [time002_at, time002_u]⟩

/-- The marking after `u` fires: place `0` empty. -/
def time002_m1 : Nat → Nat := fireNC (time002_at 0).m time002_u.core (depProd [])

/-- `u` has a reference firing at every clock reading. -/
theorem time002_u_refFire (n : Nat) : RefFire time002_u (time002_at n).m [] time002_m1 :=
  ⟨by show enabledNA (fun p : Nat => if p = 0 then 1 else 0) time002_u.core = true; decide,
    ⟨.action 0, rfl⟩, rfl⟩

/-- The clock reading of AC2's example: one millisecond past the maximum duration plus the
tolerance, measured from `u`'s stamp `0`. -/
def time002_late : Nat := MaxDuration + 6

/-- An executor that never fires: the relation with no step. -/
def time002_idle : TRel Nat := fun _ _ _ _ => False

/-- ✗ An executor that does not fire an armed `Immediate` transition violates TIME-002
(line 1): at `T = 0` the transition `u` is armed and has a reference firing, which the idle
relation does not take. -/
@[evidence forbids TIME_002]
theorem TIME_002_forbids_idle : ¬ TIME_002 time002_idle := by
  intro h
  obtain ⟨_, hs, -⟩ := (h time002_X time002_u time002_u_inX rfl).1 (time002_at 0) []
    time002_m1 (time002_armed 0) (time002_u_refFire 0)
  exact hs

/-! ### Mutant: `Immediate` reaped at the maximum duration -/

/-- The policy that reads `Immediate` as a deadline at its finite `latest()`, the maximum
duration: an armed `Immediate` transition past the maximum duration plus the tolerance is
expired, and is reaped. Everything else is decided as the spec does. -/
def time002_reapMaxPolicy : Policy Nat :=
  { refPolicy with
    expired := fun X s t => ((X.timing t).reapable || decide (X.timing t = .immediate)) &&
      s.armed t && decide ((X.timing t).latest + X.tol < s.elapsed t) }

/-- Mutant reading of TIME-002 that treats `Immediate` as `Deadline(maximum duration)`: an armed
`Immediate` transition may fire until its elapsed time passes the maximum duration plus the
tolerance (line 1), no step but its reap disarms it while it stays enabled (line 2), and a reap
of it happens only past that bound and disarms it (line 3). -/
def TIME_002_mutant_reapMax {N : Type} [DecidableEq N] (R : TRel N) : Prop :=
  ∀ (X : TimedNet N) (u : Trans N), InNet X u → TimingOf X u = .immediate →
    (∀ s d m', Armed s u → ¬ MaxDuration + Tolerance X < Elapsed s u → RefFire u s.m d m' →
        ∃ s', R X s (.fire u d) s' ∧ s'.m = m') ∧
    StaysArmed R X u ∧
    (on (fun s s' => R X s (.reap u) s'), shall (fun s s' =>
        Armed s u ∧ MaxDuration + Tolerance X < Elapsed s u ∧ ¬ Armed s' u))

/-- The step that reaps `Immediate` at the maximum duration kills the mutant: it satisfies the
mutant reading, but not TIME-002, since at `T = MAX_DURATION_MS + 6` it reaps `u`, armed since
`0` (line 3). -/
@[evidence mutant TIME_002]
theorem TIME_002_mutant_reapMax_killed :
    TIME_002_mutant_reapMax (RefTStepW time002_reapMaxPolicy) ∧
      ¬ TIME_002 (RefTStepW time002_reapMaxPolicy) := by
  have hx : ∀ (X : TimedNet Nat) (u : Trans Nat), X.timing u = .immediate → ∀ s,
      time002_reapMaxPolicy.expired X s u = true ↔
        Armed s u ∧ MaxDuration + Tolerance X < Elapsed s u := fun X u hi s => by
    simp [time002_reapMaxPolicy, hi, Timing.reapable, Timing.latest, armed_iff, elapsed_eq]
  refine ⟨fun X u hu hi => ⟨fun s d m' ha hp hf => time002_fires (P := time002_reapMaxPolicy) rfl hu
      (by simp [hi, Timing.earliest]) ha ?_ hf,
    staysArmed_of (P := time002_reapMaxPolicy) rfl hu,
    fun s s' h => ?_⟩,
    fun h => ?_⟩
  · cases e : time002_reapMaxPolicy.expired X s u
    · rfl
    · exact absurd ((hx X u hi s).1 e).2 hp
  · obtain ⟨he, hna⟩ := time002_reap_inv h
    obtain ⟨ha, hp⟩ := (hx X u hi s).1 he
    exact ⟨ha, hp, hna⟩
  · exact (h time002_X time002_u time002_u_inX rfl).2.2 (time002_at time002_late) _
      (RefTStepW.reap _ _ _ (by simp [time002_X]) (by decide))

/-! ### Every line exercised -/

/-- Every line of TIME-002 is exercised by the reference step, with tolerance 5 ms. AC1: armed
at `T = 0` (elapsed 0), `u` fires (line 1). AC2: a delay to `T = MAX_DURATION_MS + 6` keeps `u`
armed (line 2); there its elapsed time is past its finite `latest()` plus the tolerance, yet it
still fires (line 1) and has no reap (line 3), where the mutant reading reaps it. -/
@[evidence nonvacuous TIME_002]
theorem TIME_002_nonvacuous :
    NamesDistinct time002_X ∧
      (∃ s', RefTStep time002_X (time002_at 0) (.fire time002_u []) s' ∧ s'.m = time002_m1) ∧
      RefTStep time002_X (time002_at 0) (.delay time002_late) (time002_at time002_late) ∧
      Armed (time002_at 0) time002_u ∧ Armed (time002_at time002_late) time002_u ∧
      (TimingOf time002_X time002_u).latest + Tolerance time002_X <
        Elapsed (time002_at time002_late) time002_u ∧
      (∃ s', RefTStep time002_X (time002_at time002_late) (.fire time002_u []) s' ∧
        s'.m = time002_m1) ∧
      (∀ s', ¬ RefTStep time002_X (time002_at time002_late) (.reap time002_u) s') ∧
      (∃ s', RefTStepW time002_reapMaxPolicy time002_X (time002_at time002_late)
        (.reap time002_u) s') := by
  have hfires : ∀ n,
      ∃ s', RefTStep time002_X (time002_at n) (.fire time002_u []) s' ∧ s'.m = time002_m1 :=
    fun n => time002_fires rfl time002_u_inX rfl (time002_armed n)
      (time002_refUnexpired rfl _) (time002_u_refFire n)
  refine ⟨time002_namesDistinct, hfires 0, RefTStepW.delay _ _ _, time002_armed 0,
    time002_armed _, by decide, hfires _, fun s' h => ?_,
    ⟨_, RefTStepW.reap _ _ _ (by simp [time002_X]) (by decide)⟩⟩
  have := (time002_reap_inv h).1
  rw [time002_refUnexpired rfl] at this
  exact Bool.noConfusion this

/-! ### Two transitions: line 2 through another firing -/

/-- A second `Immediate` transition with no arcs, so always enabled, and writing none of `u`'s
arc places. -/
def time002_v : Trans Nat :=
  { core := { name := "v", inputs := [], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- The two-transition net: `u` and `v`, both `Immediate`, tolerance 5 ms. -/
def time002_Y : TimedNet Nat :=
  { net := { places := [0], transitions := [time002_u, time002_v] },
    timing := fun _ => .immediate, tol := 5 }

theorem time002_u_inY : InNet time002_Y time002_u := rfl

theorem time002_namesDistinctY : NamesDistinct time002_Y := by unfold NamesDistinct; decide

/-- The state at `T = 0` in the two-transition net: one token in `u`'s input place, `u` and `v`
both armed since `0`. -/
def time002_two : TSt Nat :=
  { m := fun p => if p = 0 then 1 else 0, now := 0,
    stamp := fun k => if k = "u" then some 0 else if k = "v" then some 0 else none }

/-- `v` fires and leaves the marking as it is. -/
theorem time002_v_refFire : RefFire time002_v time002_two.m [] time002_two.m :=
  ⟨by simp [enabledNA, time002_v], ⟨.action 0, rfl⟩,
    by funext p; simp [fireNC, nconsumed, nspecAt, time002_v, depProd]⟩

/-- The state after `v` fires at `T = 0` under the policy `P`. -/
def time002_afterV (P : Policy Nat) : TSt Nat :=
  { m := time002_two.m, now := 0,
    stamp := restampAll P time002_Y time002_two time002_v [] time002_two.m }

/-- `v` fires at `T = 0`, under any policy with the spec's gate and expiry. -/
theorem time002_v_fires {P : Policy Nat} (hg : P.gate = refPolicy.gate)
    (hx : P.expired = refPolicy.expired) :
    RefTStepW P time002_Y time002_two (.fire time002_v []) (time002_afterV P) :=
  RefTStepW.fire _ _ _ _ _ (by simp [time002_Y]) time002_v_refFire (by decide)
    (by rw [hg]; decide) (by rw [hx]; decide)

/-- The policy under which only a write arms: a firing keeps no stamp, and arms a transition
only if it writes one of its arc places, so it drops the stamp of an armed transition it does
not write even when that transition stays enabled. -/
def time002_dropPolicy : Policy Nat :=
  { refPolicy with
    keep := fun _ _ _ _ _ _ => false
    rearm := fun _ _ t d m' u => enabledNA m' u.core && writesArc t d u }

/-- ✗ An executor whose firing disarms a still-enabled armed `Immediate` transition violates
TIME-002 (line 2): at `T = 0` `v` fires, writing none of `u`'s arc places, `u` stays enabled,
and the step drops `u`'s stamp, so `u` is no longer ready. -/
@[evidence forbids TIME_002]
theorem TIME_002_forbids_drop : ¬ TIME_002 (RefTStepW time002_dropPolicy) := by
  intro h
  have := (h time002_Y time002_u time002_u_inY rfl).2.1 _ time002_namesDistinctY _ _
    (time002_v_fires rfl rfl) (by decide) (by decide) (by simp)
  revert this
  decide

/-- Line 2 exercised through another firing by the reference step: at `T = 0` `v` fires, and
`u` stays enabled and armed with its stamp `0`. -/
@[evidence nonvacuous TIME_002]
theorem TIME_002_nonvacuous_two :
    NamesDistinct time002_Y ∧ Armed time002_two time002_u ∧
      RefTStep time002_Y time002_two (.fire time002_v []) (time002_afterV refPolicy) ∧
      Enabled time002_u (time002_afterV refPolicy).m ∧ Armed (time002_afterV refPolicy) time002_u ∧
      (time002_afterV refPolicy).stamp "u" = some 0 :=
  ⟨time002_namesDistinctY, by decide, time002_v_fires rfl rfl, by decide, by decide, by decide⟩

/-- ✗ An executor whose firing of `u` itself leaves `u` enabled but unarmed violates TIME-002
(line 2): with two tokens in `u`'s input place at `T = 0`, `u` fires and stays enabled, and the
self-drop policy gives it no clock, a reap hidden in its own firing. -/
@[evidence forbids TIME_002]
theorem TIME_002_forbids_selfDrop : ¬ TIME_002 (RefTStepW (selfDropPolicy (N := Nat))) := fun h =>
  selfDrop_not_staysArmed (s := { time002_at 0 with m := fun p => if p = 0 then 2 else 0 })
    (d := []) time002_u_inX time002_namesDistinct (by decide)
    ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩ (by decide) (by decide) (by decide)
    (h time002_X time002_u time002_u_inX rfl).2.1

/-! ### The Timing accessors -/

/-- The interval bullets of TIME-002: `Immediate` has earliest bound 0, latest bound the
maximum duration, no deadline, and is not reapable. -/
@[evidence cites "TIME-002" "earliest() = 0, latest() = maximum duration, hasDeadline() = false"]
theorem time002_interval :
    Timing.immediate.earliest = 0 ∧ Timing.immediate.latest = maxDurationMs ∧
      Timing.immediate.hasDeadline = false ∧ Timing.immediate.reapable = false :=
  ⟨rfl, rfl, rfl, rfl⟩

end Libpetri.Spec
