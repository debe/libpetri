import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryTime
import Libpetri.Spec.Text.TIME_003

set_option linter.missingDocs true

/-!
# TIME-003: Deadline timing (`spec/03-timing.md`)

The requirement is a predicate over an abstract timed step relation `R : TRel N` (glossary
`GlossaryTime.lean`). For each transition of the net with timing `Deadline(by)` it says five
things: the transition may fire while armed and not past `by` plus the tolerance; it does not
fire once past that bound; it can be reaped once past it; a reap of it happens only past the
bound and leaves it unarmed; and its clock is framed (`ClockFrame`, shared with TIME-004 to
TIME-006): no step but its own reap disarms it while it stays enabled, and a delay, the reap of
another name and a firing of another name that leaves it enabled throughout keep its stamp, so
the elapsed time the reap sentence reads grows with the clock.

The step relation is atomic and may be late (`Reference/Timed.lean`), so the reap sentence is
stated by its safety part and by the reap step being available. That a cycle reaps it, and that
a strongly urgent semantics fires it within `by`, are not properties of one step: the first is
the Phase 2 executor's, the second the verification graph's (ruling D3, cited from
`Novel/TimedScg/Run.lean`, not encoded here).

The evidence theorems check the statement against the timed reference step (`RefTStep`),
against executors that never reap, that block without a reap step, that reap early and that
disarm on an unrelated firing or on its own firing, and against the mutant readings that reap
at the bound itself, that reap without the tolerance, that read the elapsed time off whatever
stamp the state holds (an executor that restamps on every delay) and that let an unrelated
firing restart the clock.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Novel.TimedScg (Timing maxDurationMs)

/-! ## TIME-003: Deadline timing -/

requirement TIME_003
  id "TIME-003"
  title "Deadline Timing"
  kind T
  scope "all executors"
  source verbatim "spec/03-timing.md"
  covers TIME_003.s1, TIME_003.s2
  reading "For every timed net X and every transition u the net holds under its name, with timing Deadline(by):"
          "while u is armed and its elapsed time is not greater than by plus the tolerance, the step relation has every firing of u that the reference semantics has, with the same successor marking;"
          "no firing of u starts from a state in which u is armed and its elapsed time is greater than by plus the tolerance;"
          "from a state in which u is armed and its elapsed time is greater than by plus the tolerance, the step relation has a reap of u;"
          "a reap of u starts from a state in which u is armed and its elapsed time is greater than by plus the tolerance, and leaves u not armed;"
          "u's clock is framed (ClockFrame): when the net's names are distinct, no step but the reap of u disarms u while it stays enabled, and a delay, the reap of a transition of another name, and a firing of a transition of another name that leaves u enabled in its intermediate marking and after it keep u's stamp."
  assumes "A step relates two states of the executor (glossary: TSt); a step is a delay of the clock, a firing or a reap (TRel). Firings are atomic, and the relation may be late: a delay may pass any bound. Armed, Elapsed time, Expired, Reaped and Deadline tolerance are the glossary terms (GlossaryTime.lean). For a Deadline(by) transition, expired is exactly armed with an elapsed time strictly greater than by plus the tolerance, since Deadline is reapable and its latest bound is by."
          "Line 1 is the first 'shall' sentence. Readiness is read through the step relation: a transition whose timing does not stop it is one the relation may fire. Its earliest bound is 0, so the only timing obstacle is expiry, and line 1 asks for every reference firing up to and including the bound, so an executor that refuses to fire at the bound is excluded; one that reaps early is excluded by line 4. The firing order among ready transitions (priority, FIFO) is EXEC-002 and is not part of an atomic step."
          "Lines 2 to 4 are the second 'shall' sentence (ruling D4: strictly past by plus the tolerance, and the tolerance is MUST). An atomic relation cannot say that a reap happens, only that it is available and is the only way out: line 3 is the reap step being available (TIME-013 states the same for every expired transition, its last line), line 2 that the expired transition does not fire instead, and line 4 that a reap happens only when it is expired and disarms it. That the reap happens in the deadline step of the very cycle in which the bound is passed ([EXEC-001] step 4) and emits TransitionTimedOut ([EVT-009]) is the Phase 2 executor's, not this block's. Rust and Java (one reading per cycle, shared by the deadline step and the firing pass: cycle_now, cycleNanos) and TypeScript (the deadline step and the pass share cycleNowMs) conform to line 2. A firing pass that takes a clock reading of its own, later than the deadline step's, and checks only the earliest bound there breaks it: a Deadline transition whose elapsed time passes by plus the tolerance between the two readings is not reaped and fires. That is the behaviour RD-16 in spec/runtime-defects.md recorded for Java's fireReadyGeneral."
          "Line 5 is the frame ClockFrame shared with TIME-004 to TIME-006 (GlossaryTime.lean). Its first part is the first 'shall' sentence for steps that would make u not ready by disarming it: the only step that may take the clock from an enabled Deadline transition is its reap, and a firing of u itself that leaves u enabled re-arms it (TIME_003_forbids_selfDrop). Its other parts read 'elapsed time' in the second 'shall' sentence through the glossary (Elapsed: the clock reading minus the stamp taken when the transition was most recently newly armed): a delay, the reap of another transition and a firing of another transition that leaves u enabled throughout newly arm nothing, so they keep u's stamp. Without them an executor that restamps every armed transition on each delay (TIME_003_mutant_anyStamp_killed), or restarts every armed clock on every firing (TIME_003_mutant_restart_killed), keeps the elapsed time of u from growing in a busy net and never reaps it. That a delay advances the clock by its length is TIME-015 line 2, conjoined in ConsistencyTime. Distinct names (NamesDistinct, ruling D10) are needed because stamps are kept per name. Under ruling D6 an injected token also writes arc places, but injection is not a step of the Phase 1 relation."
          "The body sentence that the transition must fire within by (plus the tolerance) is not a property of the executor, which may be late (ruling D3): the executor reaps instead. The strongly urgent reading, under which time cannot pass beyond the latest bound of an enabled transition, is the verification semantics (Novel.TimedScg.TStep, timed_run_sound) and is not encoded here."
          "Construction (0 < by <= maximum duration) is TIME-001 AC4 (ruling D11), a property of Timing.Valid, not of the step relation (time003_construction, cited); the interval, earliest() = 0, latest() = by and hasDeadline() = true are the Timing accessors (time003_interval, cited)."
          "AC1 (fires immediately after enablement) is line 1 at elapsed time 0, exercised in TIME_003_nonvacuous. AC2 (a transition still armed past by plus the deadline tolerance does not fire after that bound; if it is still armed on the first cycle whose elapsed time is strictly greater than the bound, it is reaped in that cycle) is lines 2 to 4, exercised in TIME_003_nonvacuous with Deadline(5000 ms) and tolerance 5 ms: u fires at elapsed 5005 and cannot be reaped there, and at 5006 it cannot fire, is reaped and is no longer armed. Its first sentence is the safety line 2 (no firing past the bound). Its second sentence is conditional on u still being armed, so a competitor that disables u before its bound does not falsify it ([TIME-011]); on the step relation it is lines 3 and 4, the reap offered in every state strictly past the bound and in no other. That the reap happens in the first such cycle is a property of the cycle loop ([EXEC-001] step 4), which the atomic Phase 1 relation does not have, and is deferred to Phase 2 (RefExec). The test derivation's 'verify transition disabled' after the reap is the reaped transition staying unarmed: across delays and other reaps by line 5, across a firing that writes none of its arc places by TIME-010 line 1 and TIME-013, so it is covered only jointly, in ConsistencyTime. The TransitionTimedOut event of AC2 is EVT-009, deferred to Phase 2."
  signoff "2026-11-13 d4286d66f31f5dbe ai"
  statement : ∀ {N : Type} [DecidableEq N], TRel N → Prop :=
    fun R => ∀ (X : TimedNet _) (u : Trans _) (b : Nat), InNet X u → TimingOf X u = .deadline b →
      (∀ s d m', Armed s u → ¬ b + Tolerance X < Elapsed s u → RefFire u s.m d m' →
          ∃ s', R X s (.fire u d) s' ∧ s'.m = m') ∧
      (while (fun s => Armed s u ∧ b + Tolerance X < Elapsed s u),
          never (fun s s' => ∃ d, R X s (.fire u d) s')) ∧
      (∀ s, Armed s u → b + Tolerance X < Elapsed s u → ∃ s', R X s (.reap u) s') ∧
      (on (fun s s' => R X s (.reap u) s'), shall (fun s s' =>
          Armed s u ∧ b + Tolerance X < Elapsed s u ∧ ¬ Armed s' u)) ∧
      ClockFrame R X u

/- The pinned readable form of TIME-003: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.TIME_003 : {N : Type} → [DecidableEq N] → TRel N → Prop :=
fun {N} [DecidableEq N] R =>
  ∀ (X : TimedNet N) (u : Reference.Trans N) (b : ℕ),
    InNet X u →
      TimingOf X u = Timing.deadline b →
        (∀ (s : TSt N) (d : List N) (m' : N → ℕ),
            Armed s u →
              ¬b + Tolerance X < Elapsed s u → RefFire u s.m d m' → ∃ s', R X s (TLbl.fire u d) s' ∧ s'.m = m') ∧
          (while fun s => Armed s u ∧ b + Tolerance X < Elapsed s u, never fun s s' => ∃ d, R X s (TLbl.fire u d) s') ∧
            (∀ (s : TSt N), Armed s u → b + Tolerance X < Elapsed s u → ∃ s', R X s (TLbl.reap u) s') ∧
              (on fun s s' => R X s (TLbl.reap u) s', shall fun s s' =>
                  Armed s u ∧ b + Tolerance X < Elapsed s u ∧ ¬Armed s' u) ∧
                ClockFrame R X u
-/
#guard_msgs in #print TIME_003

/-! ### The lines for one transition, for any policy and any expiry threshold -/

section Lines

variable {N : Type} [DecidableEq N]

/-- The five lines of TIME-003 for the transition `u` of the net `X`, with `Past e` read as
"the elapsed time `e` is past the bound". TIME-003 is these lines with `Past e` the strict test
`by + tolerance < e` (`time003_iff`); the mutant readings change only `Past`. -/
def DeadlineLines (R : TRel N) (X : TimedNet N) (u : Trans N) (Past : Nat → Prop) : Prop :=
  (∀ s d m', Armed s u → ¬ Past (Elapsed s u) → RefFire u s.m d m' →
      ∃ s', R X s (.fire u d) s' ∧ s'.m = m') ∧
  (while (fun s => Armed s u ∧ Past (Elapsed s u)),
      never (fun s s' => ∃ d, R X s (.fire u d) s')) ∧
  (∀ s, Armed s u → Past (Elapsed s u) → ∃ s', R X s (.reap u) s') ∧
  (on (fun s s' => R X s (.reap u) s'), shall (fun s s' =>
      Armed s u ∧ Past (Elapsed s u) ∧ ¬ Armed s' u)) ∧
  ClockFrame R X u

/-- The first four lines of `DeadlineLines`: the deadline lines without the clock frame. -/
def DeadlineCore (R : TRel N) (X : TimedNet N) (u : Trans N) (Past : Nat → Prop) : Prop :=
  (∀ s d m', Armed s u → ¬ Past (Elapsed s u) → RefFire u s.m d m' →
      ∃ s', R X s (.fire u d) s' ∧ s'.m = m') ∧
  (while (fun s => Armed s u ∧ Past (Elapsed s u)),
      never (fun s s' => ∃ d, R X s (.fire u d) s')) ∧
  (∀ s, Armed s u → Past (Elapsed s u) → ∃ s', R X s (.reap u) s') ∧
  (on (fun s s' => R X s (.reap u) s'), shall (fun s s' =>
      Armed s u ∧ Past (Elapsed s u) ∧ ¬ Armed s' u))

/-- `DeadlineLines` is `DeadlineCore` and the clock frame. -/
theorem deadlineLines_iff {R : TRel N} {X : TimedNet N} {u : Trans N} {Past : Nat → Prop} :
    DeadlineLines R X u Past ↔ DeadlineCore R X u Past ∧ ClockFrame R X u :=
  ⟨fun h => ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩, h.2.2.2.2⟩,
    fun ⟨⟨h1, h2, h3, h4⟩, h5⟩ => ⟨h1, h2, h3, h4, h5⟩⟩

/-- TIME-003 is `DeadlineLines` with the strict test past `by` plus the tolerance. -/
theorem time003_iff (R : TRel N) :
    TIME_003 R ↔ ∀ (X : TimedNet N) (u : Trans N) (b : Nat), InNet X u →
      TimingOf X u = .deadline b → DeadlineLines R X u (fun e => b + Tolerance X < e) :=
  Iff.rfl

/-- A transition of the net with earliest bound 0, armed and not expired under `P`, takes every
reference firing it has, under any policy with the spec's gate. -/
theorem time003_fires {P : Policy N} (hg : P.gate = refPolicy.gate) {X : TimedNet N}
    {u : Trans N} (hu : InNet X u) (h0 : (X.timing u).earliest = 0) {s : TSt N} {d : List N}
    {m' : N → Nat} (ha : Armed s u) (hx : P.expired X s u = false) (hf : RefFire u s.m d m') :
    ∃ s', RefTStepW P X s (.fire u d) s' ∧ s'.m = m' :=
  ⟨_, RefTStepW.fire X s u d m' (inNet_mem hu) hf ((armed_iff s u).1 ha)
    (by rw [hg]; simp [refPolicy, h0]) hx, rfl⟩

/-- A firing, under any policy, starts from a state in which its transition is not expired. -/
theorem time003_fire_unexpired {P : Policy N} {X : TimedNet N} {u : Trans N} {d : List N}
    {s s' : TSt N} (h : RefTStepW P X s (.fire u d) s') : P.expired X s u = false :=
  (refTStepW_fire_inv h).2.2.2.2.1

/-- A reap, under any policy, starts from a state in which its transition is expired, drops its
stamp and keeps the marking. -/
theorem time003_reap_inv {P : Policy N} {X : TimedNet N} {u : Trans N} {s s' : TSt N}
    (h : RefTStepW P X s (.reap u) s') :
    P.expired X s u = true ∧ s'.stamp u.core.name = none ∧ s'.m = s.m := by
  cases h with
  | reap _ _ hx => exact ⟨hx, by simp, rfl⟩

/-- A reaped transition is not armed after the reap, under any policy. -/
theorem time003_reap_unarmed {P : Policy N} {X : TimedNet N} {u : Trans N} {s s' : TSt N}
    (h : RefTStepW P X s (.reap u) s') : ¬ Armed s' u := fun ha => by
  have := ha.2
  rw [(time003_reap_inv h).2.1] at this
  simp at this

/-- An expired transition of the net can be reaped, under any policy. -/
theorem time003_reap_exists {P : Policy N} {X : TimedNet N} {u : Trans N} (hu : InNet X u)
    {s : TSt N} (hx : P.expired X s u = true) : ∃ s', RefTStepW P X s (.reap u) s' :=
  ⟨_, RefTStepW.reap X s u (inNet_mem hu) hx⟩

/-- **The deadline lines for any policy.** Under a policy whose gate is the spec's, a transition
of the net with earliest bound 0, whose expiry under the policy is exactly "armed and `Past` of
its elapsed time", meets the four deadline lines with that `Past`, whatever the policy does to
the stamps. -/
theorem time003_core {P : Policy N} (hg : P.gate = refPolicy.gate) {X : TimedNet N}
    {u : Trans N} (hu : InNet X u) (h0 : (X.timing u).earliest = 0) (Past : Nat → Prop)
    (hx : ∀ s, P.expired X s u = true ↔ Armed s u ∧ Past (Elapsed s u)) :
    DeadlineCore (RefTStepW P) X u Past := by
  refine ⟨fun s d m' ha hp hf => time003_fires hg hu h0 ha ?_ hf,
    fun s s' ⟨d, h⟩ hp => ?_, fun s ha hp => time003_reap_exists hu ((hx s).2 ⟨ha, hp⟩),
    fun s s' h => ?_⟩
  · cases e : P.expired X s u
    · rfl
    · exact absurd ((hx s).1 e).2 hp
  · have e := time003_fire_unexpired h
    rw [(hx s).2 hp] at e
    exact Bool.noConfusion e
  · obtain ⟨ha, hp⟩ := (hx s).1 (time003_reap_inv h).1
    exact ⟨ha, hp, time003_reap_unarmed h⟩

/-- **The lines for any policy.** Under a policy whose `keep`, `rearm` and gate are the spec's,
a transition of the net with earliest bound 0, whose expiry under the policy is exactly "armed
and `Past` of its elapsed time", meets the five lines with that `Past`. -/
theorem time003_lines {P : Policy N} (hk : P.keep = refPolicy.keep)
    (hr : P.rearm = refPolicy.rearm) (hg : P.gate = refPolicy.gate) {X : TimedNet N}
    {u : Trans N} (hu : InNet X u) (h0 : (X.timing u).earliest = 0) (Past : Nat → Prop)
    (hx : ∀ s, P.expired X s u = true ↔ Armed s u ∧ Past (Elapsed s u)) :
    DeadlineLines (RefTStepW P) X u Past :=
  deadlineLines_iff.2 ⟨time003_core hg hu h0 Past hx, clockFrame_of hk hr hu⟩

/-- The spec's expiry of a `Deadline(by)` transition: armed and strictly past `by` plus the
tolerance. -/
theorem time003_refExpired {X : TimedNet N} {u : Trans N} {b : Nat}
    (hb : X.timing u = .deadline b) (s : TSt N) :
    (refPolicy (N := N)).expired X s u = true ↔ Armed s u ∧ b + Tolerance X < Elapsed s u := by
  show tExpired X s u = true ↔ _
  rw [← expired_iff]
  simp [Expired, Reapable, hb, Timing.reapable, Timing.latest]

end Lines

/-- The timed reference step satisfies TIME-003: every `Deadline(by)` transition has earliest
bound 0 and is expired under `refPolicy` exactly when it is armed and strictly past `by` plus the
tolerance, so `time003_lines` applies with the strict test. -/
@[evidence holds TIME_003]
theorem TIME_003_reference {N : Type} [DecidableEq N] : TIME_003 (RefTStep (N := N)) :=
  fun _ _ _ hu hb => time003_lines rfl rfl rfl hu (by simp [hb, Timing.earliest]) _
    (time003_refExpired hb)

/-! ### Examples (AC1, AC2) -/

/-- The transition of the examples: one input arc on place `0`, no output spec. -/
def time003_u : Trans Nat :=
  { core := { name := "u", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- The timed net of the examples: `u` with `Deadline(5000)` (AC2's five seconds, in
milliseconds), and the default tolerance of 5 ms. -/
def time003_X : TimedNet Nat :=
  { net := { places := [0], transitions := [time003_u] },
    timing := fun _ => .deadline 5000, tol := 5 }

theorem time003_u_inX : InNet time003_X time003_u := rfl

theorem time003_namesDistinct : NamesDistinct time003_X := by unfold NamesDistinct; decide

/-- The state at clock reading `n`: one token in `u`'s input place, `u` armed since `0`. -/
def time003_at (n : Nat) : TSt Nat :=
  { m := fun p => if p = 0 then 1 else 0, now := n,
    stamp := fun k => if k = "u" then some 0 else none }

/-- `u` is armed at every clock reading. -/
theorem time003_armed (n : Nat) : Armed (time003_at n) time003_u :=
  ⟨by show Enabled time003_u (fun p : Nat => if p = 0 then 1 else 0); decide,
    by simp [time003_at, time003_u]⟩

/-- The marking after `u` fires: place `0` empty. -/
def time003_m1 : Nat → Nat := fireNC (time003_at 0).m time003_u.core (depProd [])

/-- `u` has a reference firing at every clock reading. -/
theorem time003_u_refFire (n : Nat) : RefFire time003_u (time003_at n).m [] time003_m1 :=
  ⟨by show enabledNA (fun p : Nat => if p = 0 then 1 else 0) time003_u.core = true; decide,
    ⟨.action 0, rfl⟩, rfl⟩

/-- An executor that never reaps: the reference step with no transition ever expired. -/
def time003_noReapPolicy : Policy Nat := { refPolicy with expired := fun _ _ _ => false }

/-- ✗ An executor without deadline enforcement violates TIME-003 (line 2): at `T = 5006` the
`Deadline(5000)` transition `u`, armed since `0`, is past `5000 + 5` and still fires. -/
@[evidence forbids TIME_003]
theorem TIME_003_forbids_noReap : ¬ TIME_003 (RefTStepW time003_noReapPolicy) := by
  intro h
  have hfire : RefTStepW time003_noReapPolicy time003_X (time003_at 5006) (.fire time003_u [])
      { m := time003_m1, now := 5006,
        stamp := restampAll time003_noReapPolicy time003_X (time003_at 5006) time003_u []
          time003_m1 } :=
    RefTStepW.fire _ _ _ _ _ (by simp [time003_X]) (time003_u_refFire 5006) (by decide)
      (by decide) rfl
  exact (h time003_X time003_u 5000 time003_u_inX rfl).2.1 _ _ ⟨_, hfire⟩ (by decide)

/-! ### Mutant: reap at the bound itself -/

/-- The policy that reaps a reapable transition once its elapsed time reaches its latest bound
plus the tolerance (`≥` instead of `>`), and decides everything else as the spec does. -/
def time003_reapGePolicy : Policy Nat :=
  { refPolicy with expired := fun X s t =>
      (X.timing t).reapable && s.armed t && decide ((X.timing t).latest + X.tol ≤ s.elapsed t) }

/-- Mutant reading of TIME-003 in which a `Deadline(by)` transition is past its bound once its
elapsed time reaches `by` plus the tolerance: the five lines with `≤` in place of `<`. -/
def TIME_003_mutant_reapGe {N : Type} [DecidableEq N] (R : TRel N) : Prop :=
  ∀ (X : TimedNet N) (u : Trans N) (b : Nat), InNet X u → TimingOf X u = .deadline b →
    DeadlineLines R X u (fun e => b + Tolerance X ≤ e)

/-- The step that reaps at the bound kills the mutant: it satisfies the mutant reading, but not
TIME-003, since at `T = 5005` (elapsed `5005 = 5000 + 5`, not past the bound) it refuses to fire
`u`, which the spec still allows (AC2: reaped only once elapsed is strictly greater). -/
@[evidence mutant TIME_003]
theorem TIME_003_mutant_reapGe_killed :
    TIME_003_mutant_reapGe (RefTStepW time003_reapGePolicy) ∧
      ¬ TIME_003 (RefTStepW time003_reapGePolicy) := by
  refine ⟨fun X u b hu hb => time003_lines (P := time003_reapGePolicy) rfl rfl rfl hu
    (by simp [hb, Timing.earliest]) _ fun s => ?_, fun h => ?_⟩
  · simp [time003_reapGePolicy, hb, Timing.reapable, Timing.latest, armed_iff, elapsed_eq]
  · obtain ⟨_, hs, -⟩ := (h time003_X time003_u 5000 time003_u_inX rfl).1 (time003_at 5005) []
      time003_m1 (by decide) (by decide) (time003_u_refFire 5005)
    have := time003_fire_unexpired hs
    revert this
    decide

/-! ### Mutant: reap without the tolerance -/

/-- The policy that reaps a reapable transition once its elapsed time is strictly greater than
its latest bound, ignoring the tolerance, and decides everything else as the spec does. -/
def time003_noTolPolicy : Policy Nat :=
  { refPolicy with expired := fun X s t =>
      (X.timing t).reapable && s.armed t && decide ((X.timing t).latest < s.elapsed t) }

/-- Mutant reading of TIME-003 without the deadline tolerance: a `Deadline(by)` transition is
past its bound once its elapsed time is strictly greater than `by`. -/
def TIME_003_mutant_noTol {N : Type} [DecidableEq N] (R : TRel N) : Prop :=
  ∀ (X : TimedNet N) (u : Trans N) (b : Nat), InNet X u → TimingOf X u = .deadline b →
    DeadlineLines R X u (fun e => b < e)

/-- The step that ignores the tolerance kills the mutant: it satisfies the mutant reading, but
not TIME-003, since at `T = 5003` (elapsed `5003`, inside the 5 ms tolerance band past `5000`)
it refuses to fire `u`, which the spec still allows. -/
@[evidence mutant TIME_003]
theorem TIME_003_mutant_noTol_killed :
    TIME_003_mutant_noTol (RefTStepW time003_noTolPolicy) ∧
      ¬ TIME_003 (RefTStepW time003_noTolPolicy) := by
  refine ⟨fun X u b hu hb => time003_lines (P := time003_noTolPolicy) rfl rfl rfl hu
    (by simp [hb, Timing.earliest]) _ fun s => ?_, fun h => ?_⟩
  · simp [time003_noTolPolicy, hb, Timing.reapable, Timing.latest, armed_iff, elapsed_eq]
  · obtain ⟨_, hs, -⟩ := (h time003_X time003_u 5000 time003_u_inX rfl).1 (time003_at 5003) []
      time003_m1 (by decide) (by decide) (time003_u_refFire 5003)
    have := time003_fire_unexpired hs
    revert this
    decide

/-! ### Every line exercised -/

/-- The state after the reap at `T = 5006`: the marking kept, `u`'s stamp dropped. -/
def time003_reaped : TSt Nat :=
  { time003_at 5006 with stamp := fun n => if n = "u" then none else (time003_at 5006).stamp n }

/-- Every line of TIME-003 is exercised by the reference step, with `Deadline(5000)` and
tolerance 5 ms. AC1: armed at `T = 0` (elapsed 0), `u` fires (line 1). A delay of 5005 ms keeps
`u` armed (line 5). At `T = 5005`, elapsed equal to the bound plus the tolerance, `u` still fires
(line 1) and has no reap (line 4). AC2: at `T = 5006`, elapsed strictly greater, `u` is armed
and cannot fire (line 2), it is reaped (line 3), and after the reap it is not armed but still
enabled, that is reaped (line 4). The delays exercise the delay part of line 5. -/
@[evidence nonvacuous TIME_003]
theorem TIME_003_nonvacuous :
    NamesDistinct time003_X ∧
      (∃ s', RefTStep time003_X (time003_at 0) (.fire time003_u []) s' ∧ s'.m = time003_m1) ∧
      RefTStep time003_X (time003_at 0) (.delay 5005) (time003_at 5005) ∧
      Armed (time003_at 0) time003_u ∧ Armed (time003_at 5005) time003_u ∧
      (∃ s', RefTStep time003_X (time003_at 5005) (.fire time003_u []) s') ∧
      (∀ s', ¬ RefTStep time003_X (time003_at 5005) (.reap time003_u) s') ∧
      Armed (time003_at 5006) time003_u ∧
      (∀ d s', ¬ RefTStep time003_X (time003_at 5006) (.fire time003_u d) s') ∧
      RefTStep time003_X (time003_at 5006) (.reap time003_u) time003_reaped ∧
      ¬ Armed time003_reaped time003_u ∧ Reaped time003_reaped time003_u := by
  have hfires : ∀ n, n ≤ 5005 →
      ∃ s', RefTStep time003_X (time003_at n) (.fire time003_u []) s' ∧ s'.m = time003_m1 :=
    fun n hn => time003_fires rfl time003_u_inX rfl (time003_armed n)
      (by
        show tExpired time003_X (time003_at n) time003_u = false
        simp [tExpired, time003_X, Timing.reapable, Timing.latest, TSt.elapsed, time003_at]
        omega)
      (time003_u_refFire n)
  refine ⟨time003_namesDistinct, hfires 0 (by omega), RefTStepW.delay _ _ 5005, by decide,
    by decide, (hfires 5005 le_rfl).imp fun _ h => h.1, fun s' h => ?_, by decide,
    fun d s' h => ?_, RefTStepW.reap _ _ _ (by simp [time003_X]) (by decide), by decide,
    by decide⟩
  · have := (time003_reap_inv h).1
    revert this
    decide
  · have := time003_fire_unexpired h
    revert this
    decide

/-! ### Mutant: elapsed time read off whatever stamp the state holds -/

/-- The snooze executor: the reference step, except that a delay gives every armed name a fresh
stamp at the new reading, so an armed transition's elapsed time is 0 after every delay. Firings
and reaps are the reference's. -/
def time003_snooze : TRel Nat := fun X s l s' =>
  match l with
  | .delay δ => s' = TSt.mk s.m (s.now + δ) (fun n => (s.stamp n).map fun _ => s.now + δ)
  | .fire t d => RefTStep X s (.fire t d) s'
  | .reap t => RefTStep X s (.reap t) s'

/-- Mutant reading of TIME-003 that reads the elapsed time off whatever stamp the state holds:
the four deadline lines (`DeadlineCore`) with the strict test and `StaysArmed`, without the
parts of the clock frame that tie `u`'s stamp to the clock. -/
def TIME_003_mutant_anyStamp {N : Type} [DecidableEq N] (R : TRel N) : Prop :=
  ∀ (X : TimedNet N) (u : Trans N) (b : Nat), InNet X u → TimingOf X u = .deadline b →
    DeadlineCore R X u (fun e => b + Tolerance X < e) ∧ StaysArmed R X u

/-- The snooze executor kills the mutant: its firings and reaps are the reference's and its
delays keep every armed transition armed, so it meets the mutant reading, but it never lets an
elapsed time grow and so never reaps; TIME-003 rejects it by line 5 (the delay part of the clock
frame), since its delay of 5006 ms from `T = 0` moves `u`'s stamp from `0` to `5006`. -/
@[evidence mutant TIME_003]
theorem TIME_003_mutant_anyStamp_killed :
    TIME_003_mutant_anyStamp time003_snooze ∧ ¬ TIME_003 time003_snooze := by
  refine ⟨fun X u b hu hb => ?_, fun h => ?_⟩
  · have L := deadlineLines_iff.1 (TIME_003_reference X u b hu hb)
    refine ⟨L.1, fun l hd s s' h ha hen hl => ?_⟩
    cases l with
    | delay δ =>
      have h' : s' = _ := h
      subst h'
      exact ⟨hen, by simpa using ha.2⟩
    | fire t d => exact L.2.1 _ hd s s' h ha hen hl
    | reap t => exact L.2.1 _ hd s s' h ha hen hl
  · have := (h time003_X time003_u 5000 time003_u_inX rfl).2.2.2.2.2.1 5006 (time003_at 0) _
      rfl
    revert this
    decide

/-! ### Executors that break the reap lines -/

/-- An executor with no reap step: the reference step with every reap removed. It blocks the
firing of an expired transition but never reaps it. -/
def time003_noReapStep : TRel Nat := fun X s l s' => RefTStep X s l s' ∧ ∀ t, l ≠ .reap t

/-- ✗ An executor that blocks an expired transition without reaping it violates TIME-003
(line 3): at `T = 5006` the `Deadline(5000)` transition `u`, armed since `0`, is past
`5000 + 5` and has no reap step. -/
@[evidence forbids TIME_003]
theorem TIME_003_forbids_noReapStep : ¬ TIME_003 time003_noReapStep := by
  intro h
  obtain ⟨_, _, hl⟩ := (h time003_X time003_u 5000 time003_u_inX rfl).2.2.1 (time003_at 5006)
    (by decide) (by decide)
  exact hl time003_u rfl

/-- An executor that may reap early: the reference step, plus a reap of any armed transition
at any elapsed time that drops its stamp. Firing is still allowed until the bound. -/
def time003_earlyReap : TRel Nat := fun X s l s' => RefTStep X s l s' ∨
  ∃ t, l = .reap t ∧ s.armed t = true ∧
    s' = { s with stamp := fun n => if n = t.core.name then none else s.stamp n }

/-- ✗ An executor that reaps before the bound violates TIME-003 (line 4): at `T = 0` it reaps
the `Deadline(5000)` transition `u`, armed since `0`, whose elapsed time is `0`. -/
@[evidence forbids TIME_003]
theorem TIME_003_forbids_earlyReap : ¬ TIME_003 time003_earlyReap := by
  intro h
  have := ((h time003_X time003_u 5000 time003_u_inX rfl).2.2.2.1 (time003_at 0) _
    (Or.inr ⟨time003_u, rfl, by decide, rfl⟩)).2.1
  revert this
  decide

/-! ### Two transitions: the clock frame through another firing and another reap -/

/-- A second `Deadline(5000)` transition with no arcs, so always enabled, and writing none of
`u`'s arc places. -/
def time003_v : Trans Nat :=
  { core := { name := "v", inputs := [], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- The two-transition net: `u` and `v`, both `Deadline(5000)`, tolerance 5 ms. -/
def time003_Y : TimedNet Nat :=
  { net := { places := [0], transitions := [time003_u, time003_v] },
    timing := fun _ => .deadline 5000, tol := 5 }

theorem time003_u_inY : InNet time003_Y time003_u := rfl

theorem time003_namesDistinctY : NamesDistinct time003_Y := by unfold NamesDistinct; decide

/-- The state at clock reading `n` in the two-transition net: one token in `u`'s input place,
`u` stamped `su` and `v` stamped `sv`. -/
def time003_two (n su sv : Nat) : TSt Nat :=
  { m := fun p => if p = 0 then 1 else 0, now := n,
    stamp := fun k => if k = "u" then some su else if k = "v" then some sv else none }

/-- `v` fires and leaves the marking as it is. -/
theorem time003_v_refFire (n su sv : Nat) :
    RefFire time003_v (time003_two n su sv).m [] (time003_two n su sv).m :=
  ⟨by simp [enabledNA, time003_v], ⟨.action 0, rfl⟩,
    by funext p; simp [fireNC, nconsumed, nspecAt, time003_v, depProd]⟩

/-- The state after `v` fires at `T = 3000` under the policy `P`. -/
def time003_afterV (P : Policy Nat) : TSt Nat :=
  { m := (time003_two 3000 0 0).m, now := 3000,
    stamp := restampAll P time003_Y (time003_two 3000 0 0) time003_v [] (time003_two 3000 0 0).m }

/-- `v` fires at `T = 3000`, under any policy with the spec's gate and expiry. -/
theorem time003_v_fires {P : Policy Nat} (hg : P.gate = refPolicy.gate)
    (hx : P.expired = refPolicy.expired) :
    RefTStepW P time003_Y (time003_two 3000 0 0) (.fire time003_v []) (time003_afterV P) :=
  RefTStepW.fire _ _ _ _ _ (by simp [time003_Y]) (time003_v_refFire 3000 0 0) (by decide)
    (by rw [hg]; decide) (by rw [hx]; decide)

/-- The policy under which only a write arms: a firing keeps no stamp, and arms a transition
only if it writes one of its arc places, so it drops the stamp of an armed transition it does
not write even when that transition stays enabled. -/
def time003_dropPolicy : Policy Nat :=
  { refPolicy with
    keep := fun _ _ _ _ _ _ => false
    rearm := fun _ _ t d m' u => enabledNA m' u.core && writesArc t d u }

/-- ✗ An executor whose firing disarms a still-enabled armed transition violates TIME-003
(line 5, `StaysArmed`): at `T = 3000` `v` fires, writing none of `u`'s arc places, `u` stays enabled, and the
step drops `u`'s stamp. -/
@[evidence forbids TIME_003]
theorem TIME_003_forbids_drop : ¬ TIME_003 (RefTStepW time003_dropPolicy) := by
  intro h
  have := (h time003_Y time003_u 5000 time003_u_inY rfl).2.2.2.2.1 _ time003_namesDistinctY _ _
    (time003_v_fires rfl rfl) (by decide) (by decide) (by simp)
  revert this
  decide

/-- The state after the reap of `v` at `T = 5006`. -/
def time003_reapedV : TSt Nat :=
  { time003_two 5006 0 0 with
    stamp := fun n => if n = "v" then none else (time003_two 5006 0 0).stamp n }

/-- Line 5 (the clock frame) exercised in the two-transition net by the reference step: at `T = 3000`
`v` fires, `u` stays enabled and armed with its stamp `0`; at `T = 5006` `v` is reaped and `u`'s
stamp is still `0`. -/
@[evidence nonvacuous TIME_003]
theorem TIME_003_nonvacuous_two :
    NamesDistinct time003_Y ∧ Armed (time003_two 3000 0 0) time003_u ∧
      RefTStep time003_Y (time003_two 3000 0 0) (.fire time003_v []) (time003_afterV refPolicy) ∧
      Enabled time003_u (time003_afterV refPolicy).m ∧ Armed (time003_afterV refPolicy) time003_u ∧
      (time003_afterV refPolicy).stamp "u" = some 0 ∧
      RefTStep time003_Y (time003_two 5006 0 0) (.reap time003_v) time003_reapedV ∧
      time003_reapedV.stamp "u" = some 0 :=
  ⟨time003_namesDistinctY, by decide, time003_v_fires rfl rfl, by decide, by decide, by decide,
    RefTStepW.reap _ _ _ (by simp [time003_Y]) (by decide), by decide⟩

/-! ### Mutant: every armed clock restarts on every firing -/

/-- The restart on every firing: no armed transition keeps its stamp across a firing; each one
enabled after it is armed again with the current reading. -/
def time003_restartPolicy : Policy Nat := { refPolicy with keep := fun _ _ _ _ _ _ => false }

/-- Mutant reading of TIME-003 without the firing part of the clock frame: the four deadline
lines, `StaysArmed`, and `u`'s stamp kept across a delay and across the reap of another name, but
a firing of another name may restart `u`'s clock. -/
def TIME_003_mutant_restart {N : Type} [DecidableEq N] (R : TRel N) : Prop :=
  ∀ (X : TimedNet N) (u : Trans N) (b : Nat), InNet X u → TimingOf X u = .deadline b →
    DeadlineCore R X u (fun e => b + Tolerance X < e) ∧ StaysArmed R X u ∧
    (∀ δ, on (fun s s' => R X s (.delay δ) s'), shall (fun s s' =>
      s'.stamp u.core.name = s.stamp u.core.name)) ∧
    (∀ t, t.core.name ≠ u.core.name → on (fun s s' => R X s (.reap t) s'), shall (fun s s' =>
      s'.stamp u.core.name = s.stamp u.core.name))

/-- The restart on every firing kills the mutant: it satisfies the mutant reading, but not
TIME-003 (line 5, the firing part of the clock frame). At `T = 3000` the unrelated `v` fires and
`u`, enabled throughout, is restamped `3000` instead of keeping `0`, so in a busy net every
firing pushes `u`'s bound back and `u` is never reaped. -/
@[evidence mutant TIME_003]
theorem TIME_003_mutant_restart_killed :
    TIME_003_mutant_restart (RefTStepW time003_restartPolicy) ∧
      ¬ TIME_003 (RefTStepW time003_restartPolicy) := by
  refine ⟨fun X u b hu hb => ⟨time003_core (P := time003_restartPolicy) rfl hu
      (by simp [hb, Timing.earliest]) _ (time003_refExpired hb), staysArmed_of (P := time003_restartPolicy) rfl hu,
      fun _ _ _ h => frame_delay h _, fun _ hn _ _ h => frame_reapOther h (Ne.symm hn)⟩,
    fun h => ?_⟩
  have := (h time003_Y time003_u 5000 time003_u_inY rfl).2.2.2.2.2.2.2 time003_v []
    (by decide) _ _ (time003_v_fires rfl rfl) (by decide) (by decide) (by decide)
  revert this
  decide

/-- ✗ An executor whose firing of `u` itself leaves `u` enabled but unarmed violates TIME-003
(line 5, `StaysArmed`): with two tokens in `u`'s input place at `T = 0`, `u` fires and stays
enabled, and the self-drop policy gives it no clock. -/
@[evidence forbids TIME_003]
theorem TIME_003_forbids_selfDrop : ¬ TIME_003 (RefTStepW (selfDropPolicy (N := Nat))) := fun h =>
  selfDrop_not_staysArmed (s := { time003_at 0 with m := fun p => if p = 0 then 2 else 0 })
    (d := []) time003_u_inX time003_namesDistinct (by decide)
    ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩ (by decide) (by decide) (by decide)
    (h time003_X time003_u 5000 time003_u_inX rfl).2.2.2.2.1

/-! ### The Timing accessors -/

/-- The interval bullets of TIME-003: `Deadline(by)` has earliest bound 0, latest bound `by`,
a deadline, and is reapable. -/
@[evidence cites "TIME-003" "earliest() = 0, latest() = by, hasDeadline() = true"]
theorem time003_interval (b : Nat) :
    (Timing.deadline b).earliest = 0 ∧ (Timing.deadline b).latest = b ∧
      (Timing.deadline b).hasDeadline = true ∧ (Timing.deadline b).reapable = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The construction bullet of TIME-003 ([TIME-001] AC4, ruling D11): `Deadline(by)` is valid
exactly when `0 < by <= maximum duration`. -/
@[evidence cites "TIME-003" "Construction: 0 < by <= maximum duration"]
theorem time003_construction (b : Nat) :
    (Timing.deadline b).Valid ↔ 0 < b ∧ b ≤ maxDurationMs :=
  Timing.valid_deadline_iff b

/-- `Deadline(0)` and `Deadline(MAX + 1)` are rejected; `Deadline(1)` and `Deadline(MAX)` are
accepted. -/
@[evidence cites "TIME-003" "Construction: 0 < by <= maximum duration (boundary cases)"]
theorem time003_construction_examples :
    ¬ (Timing.deadline 0).Valid ∧ ¬ (Timing.deadline (maxDurationMs + 1)).Valid ∧
      (Timing.deadline 1).Valid ∧ (Timing.deadline maxDurationMs).Valid := by
  simp only [time003_construction]
  decide

end Libpetri.Spec
