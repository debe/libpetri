import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryTime
import Libpetri.Spec.Req.TIME_010

set_option linter.missingDocs true

/-!
# TIME-004: Delayed timing (`spec/03-timing.md`)

The requirement is a predicate over an abstract timed step relation `R : TRel N` (glossary
`GlossaryTime.lean`), for every transition whose timing is `Delayed(after)`. The evidence
theorems check it against the timed reference step (`RefTStep`), against a relation that fires
without looking at the clock, and against two mutant readings: a gate that opens only strictly
past `after`, a gate measured from the creation of the consumed tokens instead of from the
stamp, two executors that drop or restart the clock of `u` when a transition of another name
fires and leaves `u` enabled throughout (a reap or a restart hidden in a firing), and one whose
firing of `u` itself leaves `u` enabled and unarmed. Lines 3 and 4 use the clock frame shared
with TIME-003, TIME-005 and TIME-006 (`ClockFrame`, `GlossaryTime.lean`).

The lemmas of the section `Lines` are stated for any policy (`RefTStepW P`), so that every
mutant reuses them and needs only its counterexample.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Novel.TimedScg (Timing maxDurationMs)

/-! ## TIME-004: Delayed timing -/

requirement TIME_004
  id "TIME-004"
  title "Delayed Timing"
  kind T
  scope "all executors"
  source verbatim "spec/03-timing.md"
  quote "*While* a transition with `Delayed(after)` timing is armed and its elapsed time is less than `after`, the transition *shall not* fire."
        "*While* a transition with `Delayed(after)` timing is armed and its elapsed time is at least `after`, its timing *shall not* stop it from being ready."
        "The executor *shall not* reap a transition with `Delayed` timing ([TIME-013])."
  reading "For every timed net X, every transition u and every bound a such that u's timing is Delayed(a):"
          "no firing of u starts from a state in which u is armed and its elapsed time is below a (this restates [TIME-010] line 4 for this timing);"
          "from every state in which u, the net's transition of its name, is armed and its elapsed time is at least a, every reference firing of u is a step, to the marking that firing gives;"
          "no step reaps u;"
          "when u is the net's transition of its name, its clock is framed (ClockFrame): when the net's names are distinct, no step but a reap of u disarms u while it stays enabled, a firing of u itself included, and a delay, the reap of a transition of another name, and a firing of a transition of another name that leaves u enabled in its intermediate marking and after it keep u's stamp."
  assumes "A step relates two states of the executor (glossary: TSt), each holding a marking, the reading of the firing clock and a stamp per transition name; a step is a delay of the clock, a firing or a reap (TRel). Firings are atomic. Armed, Elapsed time, Reapable and Reaped are the glossary terms (GlossaryTime.lean); bounds are in milliseconds."
          "Line 2 reads 'its timing shall not stop it from being ready' on the step relation: a Delayed transition that is armed and past its bound is ready (glossary: Ready; Delayed is not reapable, so it is never expired), and a ready transition can take every reference firing it has, as Covers says for all transitions. Line 2 is that coverage for this timing, so the step relation may not refuse such a firing for a timing reason. Choosing among several ready transitions (priority, FIFO) is [EXEC-002] and [TIME-014]; the atomic step relation of Phase 1 has no such choice."
          "Lines 3 and 4 read 'shall not reap' with the glossary meaning of reaping, to disarm without firing: no step labelled as a reap of u (line 3), and the frame ClockFrame shared with TIME-003, TIME-005 and TIME-006 (line 4, GlossaryTime.lean). Its first part, StaysArmed, says no step leaves u enabled and unarmed (reaped, in the glossary's state reading), a firing of u itself included: a firing of u that leaves u enabled re-arms it (TIME_004_forbids_selfDrop). Its other parts keep u's stamp across a delay, a reap of another name and a firing of another name that leaves u enabled throughout; the last is [TIME-012] line 2 specialised to u: without it a firing of an unrelated transition could drop u's clock, a reap hidden in a firing (TIME_004_mutant_dropClean_killed), or restart it, which pushes u's bound back so that its timing stops it from being ready (TIME_004_mutant_restart_killed). A firing that disables u in its intermediate marking or after it drops or restarts u's clock as [TIME-011] and [TIME-012] say, and which stamp a firing of u itself leaves (a fresh one) is [TIME-012] line 4; this block fixes neither. A reap labelled with a transition other than u that carries u's name is not constrained by line 3: it is excluded by [TIME-013] line 1 (only a transition of the net is reaped) together with NamesDistinct (ruling D10). That a delay advances the clock by its length is [TIME-015] line 2."
          "The interval bullets (earliest bound after, latest bound the maximum duration, hasDeadline false) are the Timing accessors (time004_interval). The construction bullet is [TIME-001] AC4 (Timing.Valid, ruling D11): Delayed(after) is valid exactly when after is at most the maximum duration."
          "AC1 (cannot fire before after has elapsed since enablement) is line 1, with 'since enablement' read as the elapsed time since the stamp ([TIME-010]); measuring from the creation of the consumed tokens is the mutant TIME_004_mutant_tokenAge_killed. AC2 (after after, the transition can fire at any time) is line 2, which holds in every state past the bound, however late, and lines 3 and 4, by which neither a later clock reading nor an unrelated firing takes the transition's clock away or moves it."
          "The test derivation (Delayed(3s), enabled at T=0, not ready at T=2s, ready at T=3s) is the nonvacuous example TIME_004_nonvacuous, in milliseconds; it also fires an unrelated transition at T=500 that keeps u's stamp (line 4)."
  signoff "pending"
  statement : ∀ {N : Type} [DecidableEq N], TRel N → Prop :=
    fun R => ∀ (X : TimedNet _) u a, TimingOf X u = .delayed a →
      (while (fun s => Armed s u ∧ Elapsed s u < a),
          never (fun s s' => ∃ d, R X s (.fire u d) s')) ∧
      (∀ s d m', InNet X u → Armed s u → a ≤ Elapsed s u → RefFire u s.m d m' →
          ∃ s', R X s (.fire u d) s' ∧ s'.m = m') ∧
      (∀ s s', ¬ R X s (.reap u) s') ∧
      (InNet X u → ClockFrame R X u)

/- The pinned readable form of TIME-004: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.TIME_004 : {N : Type} → [DecidableEq N] → TRel N → Prop :=
fun {N} [DecidableEq N] R =>
  ∀ (X : TimedNet N) (u : Reference.Trans N) (a : ℕ),
    TimingOf X u = Timing.delayed a →
      (while fun s => Armed s u ∧ Elapsed s u < a, never fun s s' => ∃ d, R X s (TLbl.fire u d) s') ∧
        (∀ (s : TSt N) (d : List N) (m' : N → ℕ),
            InNet X u → Armed s u → a ≤ Elapsed s u → RefFire u s.m d m' → ∃ s', R X s (TLbl.fire u d) s' ∧ s'.m = m') ∧
          (∀ (s s' : TSt N), ¬R X s (TLbl.reap u) s') ∧ (InNet X u → ClockFrame R X u)
-/
#guard_msgs in #print TIME_004

/-! ### The lines, for any policy -/

section Lines

variable {N : Type} [DecidableEq N]

/-- Inversion of a reap step, under any policy: the reaped transition is in the net, the
policy calls it expired, and the step drops the stamp of its name and nothing else. -/
theorem time004_reap_inv {P : Policy N} {X : TimedNet N} {s s' : TSt N} {t : Trans N}
    (h : RefTStepW P X s (.reap t) s') :
    t ∈ X.net.transitions ∧ P.expired X s t = true ∧
      s' = { s with stamp := fun n => if n = t.core.name then none else s.stamp n } := by
  match h with
  | .reap _ _ _ ht hx => exact ⟨ht, hx, rfl⟩

/-- No reap of a transition the policy never calls expired. -/
theorem time004_no_reap {P : Policy N} {X : TimedNet N} {t : Trans N}
    (hx : ∀ s, P.expired X s t = false) (s s' : TSt N) : ¬ RefTStepW P X s (.reap t) s' :=
  fun h => absurd (time004_reap_inv h).2.1 (by simp [hx s])

/-- A transition of the net that is armed, past the policy's gate and not expired for it takes
every reference firing it has, under any policy. -/
theorem time004_fires {P : Policy N} {X : TimedNet N} {s : TSt N} {u : Trans N} {d : List N}
    {m' : N → Nat} (hu : InNet X u) (ha : Armed s u) (hg : P.gate X s u = true)
    (hx : P.expired X s u = false) (hf : RefFire u s.m d m') :
    ∃ s', RefTStepW P X s (.fire u d) s' ∧ s'.m = m' :=
  ⟨_, RefTStepW.fire X s u d m' (inNet_mem hu) hf ((armed_iff s u).1 ha) hg hx, rfl⟩

omit [DecidableEq N] in
/-- The expiry test of the spec never calls a transition of a timing that is not reapable
expired. -/
theorem time004_tExpired_false {X : TimedNet N} {t : Trans N}
    (h : (TimingOf X t).reapable = false) (s : TSt N) : tExpired X s t = false := by
  have h' : (X.timing t).reapable = false := h
  simp [tExpired, h']

/-- The spec's gate is open for a transition whose earliest bound is at most its elapsed
time. -/
theorem time004_gate_open {X : TimedNet N} {s : TSt N} {t : Trans N}
    (h : (TimingOf X t).earliest ≤ Elapsed s t) : (refPolicy (N := N)).gate X s t = true := by
  simpa [refPolicy, elapsed_eq] using h

/-- Line 3, and the delay and reap parts of the clock frame, for any policy that never calls a
`Delayed` transition expired. -/
theorem time004_never_reaped {P : Policy N} {X : TimedNet N} {u : Trans N}
    (hx : ∀ s, P.expired X s u = false) :
    (∀ s s', ¬ RefTStepW P X s (.reap u) s') ∧
      (∀ δ, on (fun s s' => RefTStepW P X s (.delay δ) s'),
        shall (fun s s' => s'.stamp u.core.name = s.stamp u.core.name)) ∧
      (∀ t, t.core.name ≠ u.core.name → on (fun s s' => RefTStepW P X s (.reap t) s'),
        shall (fun s s' => s'.stamp u.core.name = s.stamp u.core.name)) :=
  ⟨time004_no_reap hx, fun _ _ _ h => frame_delay h _,
    fun _ hn _ _ h => frame_reapOther h (Ne.symm hn)⟩

/-- Lines 1 and 2 for any policy with the spec's gate that never calls the `Delayed(a)`
transition `u` expired. -/
theorem time004_lines12 {P : Policy N} (hg : P.gate = refPolicy.gate) {X : TimedNet N}
    {u : Trans N} {a : Nat} (hT : TimingOf X u = .delayed a)
    (hx : ∀ s, P.expired X s u = false) :
    (while (fun s => Armed s u ∧ Elapsed s u < a),
        never (fun s s' => ∃ d, RefTStepW P X s (.fire u d) s')) ∧
      (∀ s d m', InNet X u → Armed s u → a ≤ Elapsed s u → RefFire u s.m d m' →
        ∃ s', RefTStepW P X s (.fire u d) s' ∧ s'.m = m') := by
  refine ⟨fun s s' ⟨d, h⟩ ⟨_, hlt⟩ => ?_, fun s d m' hu ha hle hf => ?_⟩
  · have := time010_gate hg h
    rw [hT] at this
    exact absurd this (by simp [Timing.earliest]; omega)
  · exact time004_fires hu ha (by rw [hg]; exact time004_gate_open (by rw [hT]; exact hle))
      (hx s) hf

end Lines

/-- The timed reference step satisfies TIME-004: a firing of a `Delayed(a)` transition passes
the spec's gate, so its elapsed time is at least `a` (line 1); an armed transition past `a` is
not expired, since `Delayed` is not reapable, so it takes every reference firing it has
(line 2); for the same reason it is never reaped (line 3); and the reference step meets the
clock frame of every transition of the net (line 4, `clockFrame_refTStep`). -/
@[evidence holds TIME_004]
theorem TIME_004_reference {N : Type} [DecidableEq N] : TIME_004 (RefTStep (N := N)) := by
  intro X u a hT
  have hx : ∀ s, (refPolicy (N := N)).expired X s u = false :=
    time004_tExpired_false (by rw [hT]; rfl)
  exact ⟨(time004_lines12 rfl hT hx).1, (time004_lines12 rfl hT hx).2, time004_no_reap hx,
    fun hu => clockFrame_refTStep hu⟩

/-! ### The timing itself -/

/-- The interval bullets and the construction bullet of TIME-004: `Delayed(after)` has earliest
bound `after`, the maximum duration as its latest bound, no deadline, is not reapable, and is
valid exactly when `after` is at most the maximum duration ([TIME-001] AC4). -/
@[evidence cites "TIME-004" "earliest() = after, latest() = maximum duration, hasDeadline() = false, construction 0 <= after <= maximum duration"]
theorem time004_interval (a : Nat) :
    (Timing.delayed a).earliest = a ∧ (Timing.delayed a).latest = maxDurationMs ∧
      (Timing.delayed a).hasDeadline = false ∧ (Timing.delayed a).reapable = false ∧
      ((Timing.delayed a).Valid ↔ a ≤ maxDurationMs) :=
  ⟨rfl, rfl, rfl, rfl, Iff.rfl⟩

/-! ### Examples -/

/-- The `Delayed` transition of the examples: one input arc on place `0`, an inhibitor arc on
place `1`, no output spec. -/
def time004_u : Trans Nat :=
  { core := { name := "u", inputs := [⟨0, .one⟩], inhibitors := [1], reads := [], resets := [] },
    out := none }

/-- A transition with no arcs and a deadline, so that it can be reaped. -/
def time004_v : Trans Nat :=
  { core := { name := "v", inputs := [], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- The timing of the examples: `u` is `Delayed(3000)` (3 s), every other transition
`Deadline(1000)`. -/
def time004_timing (t : Trans Nat) : Timing :=
  if t.core.name = "u" then .delayed 3000 else .deadline 1000

/-- The timed net of the examples, with the default tolerance of 5 ms. -/
def time004_X : TimedNet Nat :=
  { net := { places := [0, 1], transitions := [time004_u, time004_v] },
    timing := time004_timing, tol := 5 }

theorem time004_u_in : InNet time004_X time004_u := rfl

theorem time004_u_timing : TimingOf time004_X time004_u = .delayed 3000 := rfl

/-- The initial marking: one token in place `0`, place `1` empty. -/
def time004_m0 : Nat → Nat := fun p => if p = 0 then 1 else 0

/-- The initial state at `T = 0`: both transitions are enabled, so both are stamped `0`. -/
def time004_s0 : TSt Nat := TSt.init time004_X time004_m0 0

/-- The initial state with the clock at `n`. -/
def time004_at (n : Nat) : TSt Nat := { time004_s0 with now := n }

/-- The marking after `u` fires from the initial marking. -/
def time004_m1 : Nat → Nat := fireNC time004_m0 time004_u.core (depProd [])

/-- `u` has a reference firing from the initial marking. -/
theorem time004_u_refFire : RefFire time004_u time004_m0 [] time004_m1 :=
  ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩

/-- A relation that fires every reference firing and ignores the clock (`time010_untimed`)
violates TIME-004 (line 1): at `T = 0` it fires `u`, armed with elapsed time `0`, below its
bound of 3000 ms. -/
@[evidence forbids TIME_004]
theorem TIME_004_forbids_untimed : ¬ TIME_004 time010_untimed := by
  intro h
  have hfire : time010_untimed time004_X time004_s0 (.fire time004_u [])
      { m := time004_m1, now := 0, stamp := time004_s0.stamp } :=
    ⟨time004_u_refFire, rfl, rfl⟩
  exact (h time004_X time004_u 3000 rfl).1 _ _ ⟨_, hfire⟩ (by decide)

/-! ### Mutant: the gate opens only strictly past `after` -/

/-- The policy whose gate asks for an elapsed time strictly greater than the earliest bound,
and decides everything else as the spec does. -/
def time004_strictGatePolicy : Policy Nat :=
  { refPolicy with gate := fun X s t => decide ((X.timing t).earliest < s.elapsed t) }

/-- Mutant reading of TIME-004 with the gate strictly past `after`: line 2 asks only for the
firings of a transition whose elapsed time is greater than `after`. The other lines are as in
TIME-004. -/
def TIME_004_mutant_strictGate {N : Type} [DecidableEq N] (R : TRel N) : Prop :=
  ∀ (X : TimedNet N) u a, TimingOf X u = .delayed a →
    (while (fun s => Armed s u ∧ Elapsed s u < a),
        never (fun s s' => ∃ d, R X s (.fire u d) s')) ∧
    (∀ s d m', InNet X u → Armed s u → a < Elapsed s u → RefFire u s.m d m' →
        ∃ s', R X s (.fire u d) s' ∧ s'.m = m') ∧
    (∀ s s', ¬ R X s (.reap u) s') ∧
    (InNet X u → ClockFrame R X u)

/-- The step with the strict gate kills the mutant: it satisfies the mutant reading, but not
TIME-004, since at `T = 3000`, with elapsed time exactly 3000, `u` cannot fire (AC test
derivation: "fire at T=3s → ready"). -/
@[evidence mutant TIME_004]
theorem TIME_004_mutant_strictGate_killed :
    TIME_004_mutant_strictGate (RefTStepW time004_strictGatePolicy) ∧
      ¬ TIME_004 (RefTStepW time004_strictGatePolicy) := by
  refine ⟨fun X u a hT => ⟨fun s s' ⟨d, h⟩ ⟨_, hlt⟩ => ?_, fun s d m' hu ha hlt hf => ?_,
    time004_no_reap (time004_tExpired_false (by rw [hT]; rfl)),
    fun hu => clockFrame_of (P := time004_strictGatePolicy) rfl rfl hu⟩, fun h => ?_⟩
  · have hg := (refTStepW_fire_inv h).2.2.2.1
    have hT' : X.timing u = .delayed a := hT
    simp [time004_strictGatePolicy, hT', Timing.earliest, ← elapsed_eq] at hg
    omega
  · have hT' : X.timing u = .delayed a := hT
    refine time004_fires hu ha ?_ (time004_tExpired_false (by rw [hT]; rfl) s) hf
    simpa [time004_strictGatePolicy, hT', Timing.earliest, ← elapsed_eq] using hlt
  · obtain ⟨s', hs, -⟩ := (h time004_X time004_u 3000 rfl).2.1 (time004_at 3000) [] _
      time004_u_in (by decide) (by decide) time004_u_refFire
    have hg := (refTStepW_fire_inv hs).2.2.2.1
    revert hg
    decide

/-! ### Mutant: the delay measured from the creation of the tokens -/

/-- The policy whose gate measures the delay from the creation of the tokens the transition
consumes instead of from its stamp. A count marking keeps no creation time, so the policy takes
it as the parameter `born`: the reading at which the tokens of the example were created. -/
def time004_tokenAgePolicy (born : Nat) : Policy Nat :=
  { refPolicy with gate := fun X s t => decide ((X.timing t).earliest ≤ s.now - born) }

/-- Mutant reading of TIME-004 that measures the delay from the creation of the tokens, at
reading `born`: lines 1 and 2 compare `after` with the clock reading minus `born` instead of
with the elapsed time. The other lines are as in TIME-004. -/
def TIME_004_mutant_tokenAge {N : Type} [DecidableEq N] (born : Nat) (R : TRel N) : Prop :=
  ∀ (X : TimedNet N) u a, TimingOf X u = .delayed a →
    (while (fun s => Armed s u ∧ ClockReading s - born < a),
        never (fun s s' => ∃ d, R X s (.fire u d) s')) ∧
    (∀ s d m', InNet X u → Armed s u → a ≤ ClockReading s - born → RefFire u s.m d m' →
        ∃ s', R X s (.fire u d) s' ∧ s'.m = m') ∧
    (∀ s s', ¬ R X s (.reap u) s') ∧
    (InNet X u → ClockFrame R X u)

/-- The state at `T = 6000`: the token in place `0` was created at `0`, but `u` was newly armed
only at `5000`, when its inhibitor place `1` was drained; `v` holds no clock. -/
def time004_late : TSt Nat :=
  { m := time004_m0, now := 6000, stamp := fun n => if n = "u" then some 5000 else none }

/-- The step that measures from the creation of the tokens kills the mutant: it satisfies the
mutant reading, but not TIME-004. At `T = 6000` the token `u` consumes is 6000 ms old, so the
mutant fires `u`, armed only 1000 ms before (AC1: "since enablement"). -/
@[evidence mutant TIME_004]
theorem TIME_004_mutant_tokenAge_killed :
    TIME_004_mutant_tokenAge 0 (RefTStepW (time004_tokenAgePolicy 0)) ∧
      ¬ TIME_004 (RefTStepW (time004_tokenAgePolicy 0)) := by
  refine ⟨fun X u a hT => ⟨fun s s' ⟨d, h⟩ ⟨_, hlt⟩ => ?_, fun s d m' hu ha hle hf => ?_,
    time004_no_reap (time004_tExpired_false (by rw [hT]; rfl)),
    fun hu => clockFrame_of (P := (time004_tokenAgePolicy 0)) rfl rfl hu⟩, fun h => ?_⟩
  · have hg := (refTStepW_fire_inv h).2.2.2.1
    have hT' : X.timing u = .delayed a := hT
    simp [time004_tokenAgePolicy, hT', Timing.earliest] at hg
    simp [ClockReading] at hlt
    omega
  · have hT' : X.timing u = .delayed a := hT
    refine time004_fires hu ha ?_ (time004_tExpired_false (by rw [hT]; rfl) s) hf
    simpa [time004_tokenAgePolicy, hT', Timing.earliest] using hle
  · have hs : RefTStepW (time004_tokenAgePolicy 0) time004_X time004_late (.fire time004_u [])
        { m := time004_m1, now := 6000,
          stamp := restampAll (time004_tokenAgePolicy 0) time004_X time004_late time004_u []
            time004_m1 } :=
      RefTStepW.fire _ _ _ _ _ (inNet_mem time004_u_in) time004_u_refFire (by decide)
        (by decide) (by decide)
    exact (h time004_X time004_u 3000 rfl).1 _ _ ⟨_, hs⟩ (by decide)

/-! ### Mutants: a reap or a restart hidden in another transition's firing -/

/-- Mutant reading of TIME-004 with line 4 cut down: `u`'s clock is framed across delays and
reaps of other names only, and a firing may do anything to it (no `StaysArmed`, no firing
part of the clock frame). -/
def TIME_004_mutant_noKeep {N : Type} [DecidableEq N] (R : TRel N) : Prop :=
  ∀ (X : TimedNet N) u a, TimingOf X u = .delayed a →
    (while (fun s => Armed s u ∧ Elapsed s u < a),
        never (fun s s' => ∃ d, R X s (.fire u d) s')) ∧
    (∀ s d m', InNet X u → Armed s u → a ≤ Elapsed s u → RefFire u s.m d m' →
        ∃ s', R X s (.fire u d) s' ∧ s'.m = m') ∧
    (∀ s s', ¬ R X s (.reap u) s') ∧
    (∀ δ, on (fun s s' => R X s (.delay δ) s'),
        shall (fun s s' => s'.stamp u.core.name = s.stamp u.core.name)) ∧
    (∀ t, t.core.name ≠ u.core.name → on (fun s s' => R X s (.reap t) s'),
        shall (fun s s' => s'.stamp u.core.name = s.stamp u.core.name))

/-- Every policy with the spec's gate and expiry test satisfies the mutant reading, whatever it
does to the stamps across a firing. -/
theorem time004_noKeep_of {P : Policy Nat} (hg : P.gate = refPolicy.gate)
    (hx : P.expired = refPolicy.expired) : TIME_004_mutant_noKeep (RefTStepW P) := by
  intro X u a hT
  have hx' : ∀ s, P.expired X s u = false := fun s => by
    rw [hx]; exact time004_tExpired_false (by rw [hT]; rfl) s
  exact ⟨(time004_lines12 hg hT hx').1, (time004_lines12 hg hT hx').2, time004_never_reaped hx'⟩

/-- The clean-set drop: a firing keeps or re-arms only the clocks of the transitions whose arc
places it writes (the dirty set of the runtimes); every other armed transition loses its clock,
though it stays enabled. -/
def time004_dropCleanPolicy : Policy Nat :=
  { refPolicy with
    keep := fun X s t d m' u => refPolicy.keep X s t d m' u && writesArc t d u
    rearm := fun _ _ t d m' u => enabledNA m' u.core && writesArc t d u }

/-- The restart on every firing: no armed transition keeps its stamp across a firing; each one
enabled after it is armed again with the current reading. -/
def time004_restartPolicy : Policy Nat := { refPolicy with keep := fun _ _ _ _ _ _ => false }

/-- The marking after `v`, which has no arcs, fires from the initial marking. -/
def time004_mv : Nat → Nat := fireNC time004_m0 time004_v.core (depProd [])

/-- `v` has a reference firing from the initial marking. -/
theorem time004_v_refFire : RefFire time004_v time004_m0 [] time004_mv :=
  ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩

/-- The clean-set drop kills the mutant: it satisfies the mutant reading, but not TIME-004
(line 4). At `T = 500` the unrelated `v` fires; `u` stays enabled in the intermediate marking and
after it, yet loses its clock: it is left reaped, though `Delayed` is never reaped (sentence 3),
and no step fires it again (AC2). -/
@[evidence mutant TIME_004]
theorem TIME_004_mutant_dropClean_killed :
    TIME_004_mutant_noKeep (RefTStepW time004_dropCleanPolicy) ∧
      ¬ TIME_004 (RefTStepW time004_dropCleanPolicy) := by
  refine ⟨time004_noKeep_of rfl rfl, fun h => ?_⟩
  have hs := RefTStepW.fire (P := time004_dropCleanPolicy) time004_X (time004_at 500) time004_v
    [] time004_mv (by simp [time004_X]) time004_v_refFire (by decide) (by decide) (by decide)
  have := ((h time004_X time004_u 3000 rfl).2.2.2 time004_u_in).2.2.2 time004_v [] (by decide)
    _ _ hs (by decide) (by decide) (by decide)
  revert this
  decide

/-- The restart on every firing kills the mutant: it satisfies the mutant reading, but not
TIME-004 (line 4). At `T = 500` the unrelated `v` fires and `u`, enabled throughout, is
restamped `500` instead of keeping `0`, so in a busy net its bound of 3000 ms is pushed back by
every firing and its timing stops it from being ready (sentence 2). -/
@[evidence mutant TIME_004]
theorem TIME_004_mutant_restart_killed :
    TIME_004_mutant_noKeep (RefTStepW time004_restartPolicy) ∧
      ¬ TIME_004 (RefTStepW time004_restartPolicy) := by
  refine ⟨time004_noKeep_of rfl rfl, fun h => ?_⟩
  have hs := RefTStepW.fire (P := time004_restartPolicy) time004_X (time004_at 500) time004_v
    [] time004_mv (by simp [time004_X]) time004_v_refFire (by decide) (by decide) (by decide)
  have := ((h time004_X time004_u 3000 rfl).2.2.2 time004_u_in).2.2.2 time004_v [] (by decide)
    _ _ hs (by decide) (by decide) (by decide)
  revert this
  decide

/-! ### A reap hidden in the transition's own firing -/

theorem time004_namesDistinct : NamesDistinct time004_X := by unfold NamesDistinct; decide

/-- ✗ An executor whose firing of `u` itself leaves `u` enabled but unarmed violates TIME-004
(line 4, `StaysArmed`): with two tokens in `u`'s input place at `T = 3000`, `u` fires and stays
enabled, and the self-drop policy gives it no clock, so it is left reaped, though `Delayed` is
never reaped. -/
@[evidence forbids TIME_004]
theorem TIME_004_forbids_selfDrop : ¬ TIME_004 (RefTStepW (selfDropPolicy (N := Nat))) := fun h =>
  selfDrop_not_staysArmed
    (s := { m := fun p => if p = 0 then 2 else 0, now := 3000,
            stamp := fun n => if n = "u" then some 0 else none })
    (d := []) time004_u_in time004_namesDistinct (by decide)
    ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩ (by decide) (by decide) (by decide)
    ((h time004_X time004_u 3000 rfl).2.2.2 time004_u_in).1

/-! ### Every line exercised -/

/-- Every line of TIME-004 is exercised by the reference step, on the test derivation in
milliseconds. `u` is `Delayed(3000)` and armed at `T = 0`. Two seconds later (elapsed 2000,
below 3000) it cannot fire (line 1); at `T = 3000` it can (line 2), and it still can at the
maximum duration plus the tolerance plus one, where a `Deadline` with that bound would be
expired, and no reap of `u` is a step there (line 3). The delays keep its stamp `0` (line 4).
At `T = 2000` the deadline transition `v` is expired and reaped, and `u` keeps its stamp
(line 4). At `T = 500` `v` fires instead; `u`, armed, is enabled in the intermediate marking and
after the firing, and keeps its stamp `0` (line 4). -/
@[evidence nonvacuous TIME_004]
theorem TIME_004_nonvacuous :
    RefTStep time004_X time004_s0 (.delay 2000) (time004_at 2000) ∧
      Armed (time004_at 2000) time004_u ∧ Elapsed (time004_at 2000) time004_u = 2000 ∧
      (∀ d s', ¬ RefTStep time004_X (time004_at 2000) (.fire time004_u d) s') ∧
      RefTStep time004_X time004_s0 (.delay 3000) (time004_at 3000) ∧
      (time004_at 3000).stamp "u" = time004_s0.stamp "u" ∧
      (∃ s', RefTStep time004_X (time004_at 3000) (.fire time004_u []) s') ∧
      (∃ s', RefTStep time004_X (time004_at (maxDurationMs + 6)) (.fire time004_u []) s') ∧
      (∀ s', ¬ RefTStep time004_X (time004_at (maxDurationMs + 6)) (.reap time004_u) s') ∧
      Expired time004_X (time004_at 2000) time004_v ∧
      (∃ s', RefTStep time004_X (time004_at 2000) (.reap time004_v) s' ∧
        s'.stamp "u" = some 0) ∧
      (∃ s', RefTStep time004_X (time004_at 500) (.fire time004_v []) s' ∧
        Armed (time004_at 500) time004_u ∧ Enabled time004_u (Mid time004_v time004_m0) ∧
        Enabled time004_u s'.m ∧ s'.stamp "u" = some 0) := by
  refine ⟨RefTStepW.delay _ _ 2000, by decide, by decide, fun d s' h => ?_,
    RefTStepW.delay _ _ 3000, rfl,
    ⟨_, RefTStepW.fire _ _ _ _ _ (inNet_mem time004_u_in) time004_u_refFire (by decide)
      (by decide) (by decide)⟩,
    ⟨_, RefTStepW.fire _ _ _ _ _ (inNet_mem time004_u_in) time004_u_refFire (by decide)
      (by decide) (by decide)⟩,
    fun s' h => ?_, by decide,
    ⟨_, RefTStepW.reap _ _ _ (by simp [time004_X]) (by decide), by decide⟩,
    ⟨_, RefTStepW.fire _ _ _ _ _ (by simp [time004_X]) time004_v_refFire (by decide) (by decide)
      (by decide), by decide, by decide, by decide, by decide⟩⟩
  · have := time010_gate rfl h
    revert this
    decide
  · exact absurd (time004_reap_inv h).2.1 (by decide)

end Libpetri.Spec
