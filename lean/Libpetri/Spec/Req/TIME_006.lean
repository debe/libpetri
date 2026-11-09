import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryTime
import Libpetri.Spec.Req.TIME_010

set_option linter.missingDocs true

/-!
# TIME-006: Exact timing (`spec/03-timing.md`)

The requirement is a predicate over an abstract timed step relation `R : TRel N` (glossary
`GlossaryTime.lean`), for every transition whose timing is `Exact(at)`. It describes the
executor, which enforces `Exact` softly (ruling D3): gated at `at`, then ready however late, and
never reaped. The verification reading of the interval `[at, at]` is not this block; it is
cited (`time006_graph_interval`, and `Late.relaxLate` for the late executor).

The evidence theorems check it against the timed reference step (`RefTStep`), against a
relation that fires without looking at the clock, against the mutant that enforces `Exact`
hard, as `Window(at, at)`, and reaps it past `at` plus the tolerance, and against two executors
that drop or restart the clock of `u` when a transition of another name fires and leaves `u`
enabled throughout (a reap or a restart hidden in a firing), and one whose firing of `u` itself
leaves `u` enabled and unarmed. Lines 3 and 4 use the clock frame shared with TIME-003 to
TIME-005 (`ClockFrame`, `GlossaryTime.lean`).

The lemmas of the section `Lines` are stated for any policy (`RefTStepW P`), so that every
mutant reuses them and needs only its counterexample.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Novel.TimedScg (Timing maxDurationMs eftT lftT)

/-! ## TIME-006: Exact timing -/

requirement TIME_006
  id "TIME-006"
  title "Exact Timing"
  kind T
  scope "all executors"
  source verbatim "spec/03-timing.md"
  quote "*While* a transition with `Exact(at)` timing is armed and its elapsed time is less than `at`, the transition *shall not* fire."
        "*While* a transition with `Exact(at)` timing is armed and its elapsed time is at least `at`, its timing *shall not* stop it from being ready."
        "The executor *shall not* reap a transition with `Exact` timing, however late it observes it ([TIME-013])."
  reading "For every timed net X, every transition u and every bound a such that u's timing is Exact(a):"
          "no firing of u starts from a state in which u is armed and its elapsed time is below a (this restates [TIME-010] line 4 for this timing);"
          "from every state in which u, the net's transition of its name, is armed and its elapsed time is at least a, every reference firing of u is a step, to the marking that firing gives;"
          "no step reaps u;"
          "when u is the net's transition of its name, its clock is framed (ClockFrame): when the net's names are distinct, no step but a reap of u disarms u while it stays enabled, a firing of u itself included, and a delay, the reap of a transition of another name, and a firing of a transition of another name that leaves u enabled in its intermediate marking and after it keep u's stamp."
  assumes "A step relates two states of the executor (glossary: TSt), each holding a marking, the reading of the firing clock and a stamp per transition name; a step is a delay of the clock, a firing or a reap (TRel). Firings are atomic. Armed, Elapsed time, Reapable and Reaped are the glossary terms (GlossaryTime.lean); bounds are in milliseconds."
          "The block describes the executor (ruling D3), as the section says: Exact is enforced softly, gated at a and never force-disabled. The verification reading of [at, at] belongs to [VER-002] and [VER-012] and is only cited here: the state class graph reads Exact(a) as the interval [a, a] (time006_graph_interval), and the late-executor analysis lifts its latest bound (Late.relaxLate). No single step relation satisfies both readings, so this block takes no position on the logical-time one."
          "Line 2 reads 'its timing shall not stop it from being ready' on the step relation: an Exact transition that is armed and past its bound is ready (glossary: Ready; Exact is not reapable, so it is never expired, though hasDeadline is true), and a ready transition can take every reference firing it has, as Covers says for all transitions. Line 2 holds however late the state is, which is 'never force-disabled for overrunning at'."
          "Lines 3 and 4 read 'shall not reap' with the glossary meaning of reaping, to disarm without firing: no step labelled as a reap of u (line 3), and the frame ClockFrame shared with TIME-003 to TIME-005 (line 4, GlossaryTime.lean). Its first part, StaysArmed, says no step leaves u enabled and unarmed (reaped, in the glossary's state reading), a firing of u itself included: a firing of u that leaves u enabled re-arms it (TIME_006_forbids_selfDrop). Its other parts keep u's stamp across a delay, a reap of another name and a firing of another name that leaves u enabled throughout; the last is [TIME-012] line 2 specialised to u: without it a firing of an unrelated transition could drop u's clock, a reap hidden in a firing that force-disables u (TIME_006_mutant_dropClean_killed), or restart it, which pushes at back so that its timing stops it from being ready (TIME_006_mutant_restart_killed). A firing that disables u in its intermediate marking or after it drops or restarts u's clock as [TIME-011] and [TIME-012] say, and which stamp a firing of u itself leaves (a fresh one) is [TIME-012] line 4; this block fixes neither. That a delay advances the clock by its length is [TIME-015] line 2. A reap labelled with a transition other than u that carries u's name is not constrained by line 3: it is excluded by [TIME-013] line 1 (only a transition of the net is reaped) together with NamesDistinct (ruling D10)."
          "AC1 (cannot fire before at) is line 1. AC2's 'not force-disabled for being observed late' is lines 2, 3 and 4. AC2's 'fires at the first opportunity at or after at' is liveness of the cycle loop ([EXEC-001], [EXEC-002]), which the atomic step relation of Phase 1 does not state; line 2 makes every such firing available from the bound on. 'Exactness is observable from the firing event' is the event log ([EVT-006], [EVT-007]), not this block; that a late Exact transition emits no TransitionTimedOut ([EVT-009]) follows from line 3, as only a reap emits it."
          "The interval bullets (earliest and latest bound at, hasDeadline true) are the Timing accessors (time006_interval). The construction bullet is [TIME-001] AC4 (Timing.Valid, ruling D11): Exact(at) is valid exactly when at is at most the maximum duration. The advice to use Delayed(at) or Window(at, at + slack) instead is not a requirement on the executor."
          "The test derivation (Exact(50ms) under a busy executor that cannot run a cycle until well past 50ms: it still fires and is not timed out) is the nonvacuous example TIME_006_nonvacuous: at 1000 ms, far past 50 plus the tolerance, the transition can fire and no reap of it is a step; at 10 ms an unrelated transition fires and the transition keeps its stamp (line 4)."
  signoff "pending"
  statement : ∀ {N : Type} [DecidableEq N], TRel N → Prop :=
    fun R => ∀ (X : TimedNet _) u a, TimingOf X u = .exact a →
      (while (fun s => Armed s u ∧ Elapsed s u < a),
          never (fun s s' => ∃ d, R X s (.fire u d) s')) ∧
      (∀ s d m', InNet X u → Armed s u → a ≤ Elapsed s u → RefFire u s.m d m' →
          ∃ s', R X s (.fire u d) s' ∧ s'.m = m') ∧
      (∀ s s', ¬ R X s (.reap u) s') ∧
      (InNet X u → ClockFrame R X u)

/--
info: def Libpetri.Spec.TIME_006 : {N : Type} → [DecidableEq N] → TRel N → Prop :=
fun {N} [DecidableEq N] R =>
  ∀ (X : TimedNet N) (u : Reference.Trans N) (a : ℕ),
    TimingOf X u = Timing.exact a →
      (while fun s => Armed s u ∧ Elapsed s u < a, never fun s s' => ∃ d, R X s (TLbl.fire u d) s') ∧
        (∀ (s : TSt N) (d : List N) (m' : N → ℕ),
            InNet X u → Armed s u → a ≤ Elapsed s u → RefFire u s.m d m' → ∃ s', R X s (TLbl.fire u d) s' ∧ s'.m = m') ∧
          (∀ (s s' : TSt N), ¬R X s (TLbl.reap u) s') ∧ (InNet X u → ClockFrame R X u)
-/
#guard_msgs in #print TIME_006

/-! ### The lines, for any policy -/

section Lines

variable {N : Type} [DecidableEq N]

/-- Inversion of a reap step, under any policy: the reaped transition is in the net, the
policy calls it expired, and the step drops the stamp of its name and nothing else. -/
theorem time006_reap_inv {P : Policy N} {X : TimedNet N} {s s' : TSt N} {t : Trans N}
    (h : RefTStepW P X s (.reap t) s') :
    t ∈ X.net.transitions ∧ P.expired X s t = true ∧
      s' = { s with stamp := fun n => if n = t.core.name then none else s.stamp n } := by
  match h with
  | .reap _ _ _ ht hx => exact ⟨ht, hx, rfl⟩

/-- A reap, under any policy, leaves the reaped transition reaped if it was armed: the marking
stays, so it is still enabled, and its stamp is gone. -/
theorem time006_reap_reaped {P : Policy N} {X : TimedNet N} {s s' : TSt N} {u : Trans N}
    (h : RefTStepW P X s (.reap u) s') (ha : Armed s u) : Reaped s' u := by
  rw [(time006_reap_inv h).2.2]
  exact ⟨ha.1, fun h' => by simpa using h'.2⟩

/-- A transition of the net that is armed, past the policy's gate and not expired for it takes
every reference firing it has, under any policy. -/
theorem time006_fires {P : Policy N} {X : TimedNet N} {s : TSt N} {u : Trans N} {d : List N}
    {m' : N → Nat} (hu : InNet X u) (ha : Armed s u) (hg : P.gate X s u = true)
    (hx : P.expired X s u = false) (hf : RefFire u s.m d m') :
    ∃ s', RefTStepW P X s (.fire u d) s' ∧ s'.m = m' :=
  ⟨_, RefTStepW.fire X s u d m' (inNet_mem hu) hf ((armed_iff s u).1 ha) hg hx, rfl⟩

/-- The spec's gate is open for a transition whose earliest bound is at most its elapsed
time. -/
theorem time006_gate_open {X : TimedNet N} {s : TSt N} {t : Trans N}
    (h : (TimingOf X t).earliest ≤ Elapsed s t) : (refPolicy (N := N)).gate X s t = true := by
  simpa [refPolicy, elapsed_eq] using h

/-- Line 1 for any policy with the spec's gate. -/
theorem time006_gate {P : Policy N} (hg : P.gate = refPolicy.gate) {X : TimedNet N}
    {u : Trans N} {a : Nat} (hT : TimingOf X u = .exact a) :
    while (fun s => Armed s u ∧ Elapsed s u < a),
      never (fun s s' => ∃ d, RefTStepW P X s (.fire u d) s') := by
  intro s s' ⟨d, h⟩ ⟨_, hlt⟩
  have := time010_gate hg h
  rw [hT] at this
  exact absurd this (by simp [Timing.earliest]; omega)

/-- Line 3, and the delay and reap parts of the clock frame, for any policy that never calls the
transition expired. -/
theorem time006_never_reaped {P : Policy N} {X : TimedNet N} {u : Trans N}
    (hx : ∀ s, P.expired X s u = false) :
    (∀ s s', ¬ RefTStepW P X s (.reap u) s') ∧
      (∀ δ, on (fun s s' => RefTStepW P X s (.delay δ) s'),
        shall (fun s s' => s'.stamp u.core.name = s.stamp u.core.name)) ∧
      (∀ t, t.core.name ≠ u.core.name → on (fun s s' => RefTStepW P X s (.reap t) s'),
        shall (fun s s' => s'.stamp u.core.name = s.stamp u.core.name)) :=
  ⟨fun s s' h => absurd (time006_reap_inv h).2.1 (by simp [hx s]),
    fun _ _ _ h => frame_delay h _, fun _ hn _ _ h => frame_reapOther h (Ne.symm hn)⟩

/-- Lines 1 and 2 for any policy with the spec's gate that never calls the `Exact(a)` transition
`u` expired. -/
theorem time006_lines12 {P : Policy N} (hg : P.gate = refPolicy.gate) {X : TimedNet N}
    {u : Trans N} {a : Nat} (hT : TimingOf X u = .exact a)
    (hx : ∀ s, P.expired X s u = false) :
    (while (fun s => Armed s u ∧ Elapsed s u < a),
        never (fun s s' => ∃ d, RefTStepW P X s (.fire u d) s')) ∧
      (∀ s d m', InNet X u → Armed s u → a ≤ Elapsed s u → RefFire u s.m d m' →
        ∃ s', RefTStepW P X s (.fire u d) s' ∧ s'.m = m') :=
  ⟨time006_gate hg hT, fun s _ _ hu ha hle hf =>
    time006_fires hu ha (by rw [hg]; exact time006_gate_open (by rw [hT]; exact hle)) (hx s) hf⟩

end Lines

/-- The spec's expiry test never calls an `Exact` transition expired: `Exact` is not
reapable. -/
theorem time006_tExpired_exact {N : Type} {X : TimedNet N} {u : Trans N} {a : Nat}
    (hT : TimingOf X u = .exact a) (s : TSt N) : tExpired X s u = false := by
  have hT' : X.timing u = .exact a := hT
  simp [tExpired, hT', Timing.reapable]

/-- The timed reference step satisfies TIME-006: a firing of an `Exact(a)` transition passes
the spec's gate, so its elapsed time is at least `a` (line 1); an armed transition past `a` is
never expired, since `Exact` is not reapable, so it takes every reference firing it has however
late (line 2), and it is never reaped (line 3); the reference step meets the clock frame of
every transition of the net (line 4, `clockFrame_refTStep`). -/
@[evidence holds TIME_006]
theorem TIME_006_reference {N : Type} [DecidableEq N] : TIME_006 (RefTStep (N := N)) := by
  intro X u a hT
  obtain ⟨h1, h2⟩ := time006_lines12 (P := refPolicy) rfl hT (time006_tExpired_exact hT)
  exact ⟨h1, h2, (time006_never_reaped (P := refPolicy) (time006_tExpired_exact hT)).1,
    fun hu => clockFrame_refTStep hu⟩

/-! ### The timing itself, and the verification reading (cited) -/

/-- The interval bullets and the construction bullet of TIME-006: `Exact(at)` has `at` as both
bounds and a deadline, is not reapable, and is valid exactly when `at` is at most the maximum
duration ([TIME-001] AC4). -/
@[evidence cites "TIME-006" "earliest() = latest() = at, hasDeadline() = true, not reapable, construction 0 <= at <= maximum duration"]
theorem time006_interval (a : Nat) :
    (Timing.exact a).earliest = a ∧ (Timing.exact a).latest = a ∧
      (Timing.exact a).hasDeadline = true ∧ (Timing.exact a).reapable = false ∧
      ((Timing.exact a).Valid ↔ a ≤ maxDurationMs) :=
  ⟨rfl, rfl, rfl, rfl, Iff.rfl⟩

/-- The verification reading of `Exact(at)`: the state class graph gives it the zero-width
interval `[at, at]` (in seconds), its earliest firing time equal to its latest. -/
@[evidence cites "TIME-006" "the interval [at, at] is the precise value used for verification and simulation (logical time)"]
theorem time006_graph_interval (a : Nat) :
    ((eftT (.exact a) : ℚ) : Libpetri.Novel.Dbm.Bound) = lftT (.exact a) := rfl

/-! ### Examples -/

/-- The `Exact` transition of the examples: one input arc on place `0`, no output spec. -/
def time006_u : Trans Nat :=
  { core := { name := "u", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- A transition with no arcs, of another name, so that a reap of another transition can be
exercised. -/
def time006_v : Trans Nat :=
  { core := { name := "v", inputs := [], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- The timing of the examples: `u` is `Exact(50)`, every other transition `Deadline(10)`. -/
def time006_timing (t : Trans Nat) : Timing :=
  if t.core.name = "u" then .exact 50 else .deadline 10

/-- The timed net of the examples, with the default tolerance of 5 ms. -/
def time006_X : TimedNet Nat :=
  { net := { places := [0], transitions := [time006_u, time006_v] },
    timing := time006_timing, tol := 5 }

theorem time006_u_in : InNet time006_X time006_u := rfl

/-- The initial marking: one token in place `0`. -/
def time006_m0 : Nat → Nat := fun p => if p = 0 then 1 else 0

/-- The initial state at `T = 0`: both transitions are enabled, so both are stamped `0`. -/
def time006_s0 : TSt Nat := TSt.init time006_X time006_m0 0

/-- The initial state with the clock at `n`. -/
def time006_at (n : Nat) : TSt Nat := { time006_s0 with now := n }

/-- The marking after `u` fires from the initial marking. -/
def time006_m1 : Nat → Nat := fireNC time006_m0 time006_u.core (depProd [])

/-- `u` has a reference firing from the initial marking. -/
theorem time006_u_refFire : RefFire time006_u time006_m0 [] time006_m1 :=
  ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩

/-- A relation that fires every reference firing and ignores the clock (`time010_untimed`)
violates TIME-006 (line 1): at `T = 0` it fires `u`, armed with elapsed time `0`, below `at`
of 50 ms. -/
@[evidence forbids TIME_006]
theorem TIME_006_forbids_untimed : ¬ TIME_006 time010_untimed := by
  intro h
  have hfire : time010_untimed time006_X time006_s0 (.fire time006_u [])
      { m := time006_m1, now := 0, stamp := time006_s0.stamp } :=
    ⟨time006_u_refFire, rfl, rfl⟩
  exact (h time006_X time006_u 50 rfl).1 _ _ ⟨_, hfire⟩ (by decide)

/-! ### Mutant: `Exact` enforced hard, as `Window(at, at)` -/

/-- The expiry test that reaps every timing with a deadline, `Exact` included: armed and
elapsed time greater than the latest bound plus the tolerance. -/
def time006_hardExpired (X : TimedNet Nat) (s : TSt Nat) (t : Trans Nat) : Bool :=
  (X.timing t).hasDeadline && s.armed t && decide ((X.timing t).latest + X.tol < s.elapsed t)

/-- The policy with the hard expiry test, and the spec's other decisions. -/
def time006_hardPolicy : Policy Nat := { refPolicy with expired := time006_hardExpired }

/-- Mutant reading of TIME-006 that enforces `Exact(at)` hard, as `Window(at, at)`: ready from
`at` up to `at` plus the tolerance, not fired past it, and reaped only past it, which leaves it
reaped. The other lines are as in TIME-006. -/
def TIME_006_mutant_hard {N : Type} [DecidableEq N] (R : TRel N) : Prop :=
  ∀ (X : TimedNet N) u a, TimingOf X u = .exact a →
    (while (fun s => Armed s u ∧ Elapsed s u < a),
        never (fun s s' => ∃ d, R X s (.fire u d) s')) ∧
    (∀ s d m', InNet X u → Armed s u → a ≤ Elapsed s u → Elapsed s u ≤ a + Tolerance X →
        RefFire u s.m d m' → ∃ s', R X s (.fire u d) s' ∧ s'.m = m') ∧
    (while (fun s => Armed s u ∧ a + Tolerance X < Elapsed s u),
        never (fun s s' => ∃ d, R X s (.fire u d) s')) ∧
    (on (fun s s' => R X s (.reap u) s'),
        shall (fun s s' => Armed s u ∧ a + Tolerance X < Elapsed s u ∧ Reaped s' u)) ∧
    (InNet X u → ClockFrame R X u)

/-- The hard expiry test on an `Exact(a)` transition. -/
theorem time006_hard_exact {X : TimedNet Nat} {s : TSt Nat} {u : Trans Nat} {a : Nat}
    (hT : TimingOf X u = .exact a) :
    time006_hardPolicy.expired X s u = true ↔ Armed s u ∧ a + Tolerance X < Elapsed s u := by
  have hT' : X.timing u = .exact a := hT
  simp [time006_hardPolicy, time006_hardExpired, hT', Timing.hasDeadline, Timing.latest,
    armed_iff, elapsed_eq]

/-- The hard step kills the mutant: it satisfies the mutant reading, but not TIME-006. Under a
busy executor that first looks at `T = 1000`, far past `50 + 5`, it reaps `u` (test derivation:
"verify it still fires and emits no `TransitionTimedOut`"). -/
@[evidence mutant TIME_006]
theorem TIME_006_mutant_hard_killed :
    TIME_006_mutant_hard (RefTStepW time006_hardPolicy) ∧
      ¬ TIME_006 (RefTStepW time006_hardPolicy) := by
  refine ⟨fun X u a hT => ⟨time006_gate (P := time006_hardPolicy) rfl hT,
    fun s d m' hu ha hle hle' hf => ?_, fun s s' ⟨d, h⟩ hx => ?_, fun s s' h => ?_,
    fun hu => clockFrame_of (P := time006_hardPolicy) rfl rfl hu⟩, fun h => ?_⟩
  · refine time006_fires hu ha (time006_gate_open (by rw [hT]; exact hle)) ?_ hf
    cases hx : time006_hardPolicy.expired X s u
    · rfl
    · exact absurd ((time006_hard_exact hT).1 hx).2 (by omega)
  · have hf := (refTStepW_fire_inv h).2.2.2.2.1
    rw [(time006_hard_exact hT).2 hx] at hf
    exact Bool.noConfusion hf
  · obtain ⟨ha, hlt⟩ := (time006_hard_exact hT).1 (time006_reap_inv h).2.1
    exact ⟨ha, hlt, time006_reap_reaped h ha⟩
  · have hs := RefTStepW.reap (P := time006_hardPolicy) time006_X (time006_at 1000) time006_u
      (inNet_mem time006_u_in) (by decide)
    exact (h time006_X time006_u 50 rfl).2.2.1 _ _ hs

/-! ### Mutants: a reap or a restart hidden in another transition's firing -/

/-- Mutant reading of TIME-006 with line 4 cut down: `u`'s clock is framed across delays and
reaps of other names only, and a firing may do anything to it (no `StaysArmed`, no firing part
of the clock frame). -/
def TIME_006_mutant_noKeep {N : Type} [DecidableEq N] (R : TRel N) : Prop :=
  ∀ (X : TimedNet N) u a, TimingOf X u = .exact a →
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
theorem time006_noKeep_of {P : Policy Nat} (hg : P.gate = refPolicy.gate)
    (hx : P.expired = refPolicy.expired) : TIME_006_mutant_noKeep (RefTStepW P) := by
  intro X u a hT
  have hx' : ∀ s, P.expired X s u = false := fun s => by
    rw [hx]; exact time006_tExpired_exact hT s
  exact ⟨(time006_lines12 hg hT hx').1, (time006_lines12 hg hT hx').2, time006_never_reaped hx'⟩

/-- The clean-set drop: a firing keeps or re-arms only the clocks of the transitions whose arc
places it writes (the dirty set of the runtimes); every other armed transition loses its clock,
though it stays enabled. -/
def time006_dropCleanPolicy : Policy Nat :=
  { refPolicy with
    keep := fun X s t d m' u => refPolicy.keep X s t d m' u && writesArc t d u
    rearm := fun _ _ t d m' u => enabledNA m' u.core && writesArc t d u }

/-- The restart on every firing: no armed transition keeps its stamp across a firing; each one
enabled after it is armed again with the current reading. -/
def time006_restartPolicy : Policy Nat := { refPolicy with keep := fun _ _ _ _ _ _ => false }

/-- The marking after `v`, which has no arcs, fires from the initial marking. -/
def time006_mv : Nat → Nat := fireNC time006_m0 time006_v.core (depProd [])

/-- `v` has a reference firing from the initial marking. -/
theorem time006_v_refFire : RefFire time006_v time006_m0 [] time006_mv :=
  ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩

/-- The clean-set drop kills the mutant: it satisfies the mutant reading, but not TIME-006
(line 4). At `T = 10` the unrelated `v` fires; `u` stays enabled in the intermediate marking and
after it, yet loses its clock: it is left reaped, force-disabled with no reap step and no
`TransitionTimedOut` (sentence 3). -/
@[evidence mutant TIME_006]
theorem TIME_006_mutant_dropClean_killed :
    TIME_006_mutant_noKeep (RefTStepW time006_dropCleanPolicy) ∧
      ¬ TIME_006 (RefTStepW time006_dropCleanPolicy) := by
  refine ⟨time006_noKeep_of rfl rfl, fun h => ?_⟩
  have hs := RefTStepW.fire (P := time006_dropCleanPolicy) time006_X (time006_at 10) time006_v
    [] time006_mv (by simp [time006_X]) time006_v_refFire (by decide) (by decide) (by decide)
  have := ((h time006_X time006_u 50 rfl).2.2.2 time006_u_in).2.2.2 time006_v [] (by decide)
    _ _ hs (by decide) (by decide) (by decide)
  revert this
  decide

/-- The restart on every firing kills the mutant: it satisfies the mutant reading, but not
TIME-006 (line 4). At `T = 10` the unrelated `v` fires and `u`, enabled throughout, is restamped
`10` instead of keeping `0`, so `at` is pushed back by every firing of a busy net (sentence 2). -/
@[evidence mutant TIME_006]
theorem TIME_006_mutant_restart_killed :
    TIME_006_mutant_noKeep (RefTStepW time006_restartPolicy) ∧
      ¬ TIME_006 (RefTStepW time006_restartPolicy) := by
  refine ⟨time006_noKeep_of rfl rfl, fun h => ?_⟩
  have hs := RefTStepW.fire (P := time006_restartPolicy) time006_X (time006_at 10) time006_v
    [] time006_mv (by simp [time006_X]) time006_v_refFire (by decide) (by decide) (by decide)
  have := ((h time006_X time006_u 50 rfl).2.2.2 time006_u_in).2.2.2 time006_v [] (by decide)
    _ _ hs (by decide) (by decide) (by decide)
  revert this
  decide

/-! ### A reap hidden in the transition's own firing -/

theorem time006_namesDistinct : NamesDistinct time006_X := by unfold NamesDistinct; decide

/-- ✗ An executor whose firing of `u` itself leaves `u` enabled but unarmed violates TIME-006
(line 4, `StaysArmed`): with two tokens in `u`'s input place at `T = 50`, `u` fires and stays
enabled, and the self-drop policy gives it no clock, so it is left reaped, though `Exact` is
never reaped. -/
@[evidence forbids TIME_006]
theorem TIME_006_forbids_selfDrop : ¬ TIME_006 (RefTStepW (selfDropPolicy (N := Nat))) := fun h =>
  selfDrop_not_staysArmed
    (s := { m := fun p => if p = 0 then 2 else 0, now := 50,
            stamp := fun n => if n = "u" then some 0 else none })
    (d := []) time006_u_in time006_namesDistinct (by decide)
    ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩ (by decide) (by decide) (by decide)
    ((h time006_X time006_u 50 rfl).2.2.2 time006_u_in).1

/-! ### Every line exercised -/

/-- Every line of TIME-006 is exercised by the reference step, on the test derivation in
milliseconds with a tolerance of 5 ms. `u` is `Exact(50)` and armed at `T = 0`. At `T = 49` it
cannot fire (line 1); at `T = 50` it can (line 2); under a busy executor that first looks at
`T = 1000`, far past `50 + 5`, it still can, and no reap of it is a step (lines 2 and 3). The
delays keep its stamp `0` (line 4). At `T = 1000` the deadline transition `v` is expired and
reaped, and `u` keeps its stamp (line 4). At `T = 10` `v` fires instead; `u`, armed, is enabled
in the intermediate marking and after the firing, and keeps its stamp `0` (line 4). -/
@[evidence nonvacuous TIME_006]
theorem TIME_006_nonvacuous :
    RefTStep time006_X time006_s0 (.delay 49) (time006_at 49) ∧
      Armed (time006_at 49) time006_u ∧ Elapsed (time006_at 49) time006_u = 49 ∧
      (∀ d s', ¬ RefTStep time006_X (time006_at 49) (.fire time006_u d) s') ∧
      RefTStep time006_X time006_s0 (.delay 50) (time006_at 50) ∧
      (∃ s', RefTStep time006_X (time006_at 50) (.fire time006_u []) s') ∧
      RefTStep time006_X time006_s0 (.delay 1000) (time006_at 1000) ∧
      (time006_at 1000).stamp "u" = time006_s0.stamp "u" ∧
      (∃ s', RefTStep time006_X (time006_at 1000) (.fire time006_u []) s') ∧
      (∀ s', ¬ RefTStep time006_X (time006_at 1000) (.reap time006_u) s') ∧
      Expired time006_X (time006_at 1000) time006_v ∧
      (∃ s', RefTStep time006_X (time006_at 1000) (.reap time006_v) s' ∧
        s'.stamp "u" = some 0) ∧
      (∃ s', RefTStep time006_X (time006_at 10) (.fire time006_v []) s' ∧
        Armed (time006_at 10) time006_u ∧ Enabled time006_u (Mid time006_v time006_m0) ∧
        Enabled time006_u s'.m ∧ s'.stamp "u" = some 0) := by
  refine ⟨RefTStepW.delay _ _ 49, by decide, by decide, fun d s' h => ?_,
    RefTStepW.delay _ _ 50,
    ⟨_, RefTStepW.fire _ _ _ _ _ (inNet_mem time006_u_in) time006_u_refFire (by decide)
      (by decide) (by decide)⟩,
    RefTStepW.delay _ _ 1000, rfl,
    ⟨_, RefTStepW.fire _ _ _ _ _ (inNet_mem time006_u_in) time006_u_refFire (by decide)
      (by decide) (by decide)⟩,
    fun s' h => ?_, by decide,
    ⟨_, RefTStepW.reap _ _ _ (by simp [time006_X]) (by decide), by decide⟩,
    ⟨_, RefTStepW.fire _ _ _ _ _ (by simp [time006_X]) time006_v_refFire (by decide) (by decide)
      (by decide), by decide, by decide, by decide, by decide⟩⟩
  · have := time010_gate rfl h
    revert this
    decide
  · exact absurd (time006_reap_inv h).2.1 (by decide)

end Libpetri.Spec
