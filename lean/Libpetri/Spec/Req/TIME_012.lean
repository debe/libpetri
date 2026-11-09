import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryTime

set_option linter.missingDocs true

/-!
# TIME-012: Clock restart on intermediate disablement (`spec/03-timing.md`)

The requirement is a predicate over an abstract timed step relation `R : TRel N` (glossary
`GlossaryTime.lean`). The intermediate marking is the glossary's `Mid`, taken from the live
marking the firing starts from (ruling D7, revised). The evidence theorems check the predicate
against the timed reference step (`RefTStep`), against a relation that keeps every clock across
a firing, and against two mutant readings: the rule before 6.0.0, which compares only the
markings before and after the firing (`survivesOld`), and an intermediate marking that forgets
the reset arcs (`noReset`). A last section shows that a firing fused with a hidden delay
(`fireAdvancesClock`) is excluded only by the clock frame `time012_FramesClock`, a glossary
request.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Novel.TimedScg (Timing)

/-! ## TIME-012: Clock restart on intermediate disablement -/

requirement TIME_012
  id "TIME-012"
  title "Clock Restart on Intermediate Disablement"
  kind T
  scope "all executors"
  source verbatim "spec/03-timing.md"
  quote "The marking between the halves is the intermediate marking `M - Pre(t)` of Berthomieu and Diaz."
        "This holds even when `t`'s own outputs refill the place, and it holds whether `t`'s action completes synchronously or asynchronously: a synchronous action MUST NOT hide the gap."
        "The intermediate marking comes from the live marking `t` fires from: the tokens in the places when `t` fires, minus what `t` consumes."
        "*When* a transition `t` fires, each armed transition other than `t` that is not enabled in the intermediate marking *shall* lose its clock."
        "*When* a transition `t` fires, each armed transition other than `t` that is enabled in the intermediate marking and after the firing *shall* keep its stamp."
        "*When* a transition fires, it *shall* lose its clock."
        "*When* a transition `t` fires and a transition that lost its clock in that firing is enabled after it, that transition *shall* be newly armed ([TIME-010])."
  reading "For every timed net X:"
          "a firing of t from a state in which the net's transition u, named differently from t, is armed and not enabled in the intermediate marking of t (taken from the state's marking) leaves u armed with the reading of the firing clock after the firing if u is enabled after it, and leaves u without a stamp otherwise;"
          "a firing of t from a state in which the net's transition u, named differently from t, is armed and enabled in the intermediate marking of t, and after which u is enabled, leaves u's stamp as it was;"
          "a firing of t from a state in which the net's transition u named like t (t itself when t is the net's transition of its name) is armed leaves u armed with the reading of the firing clock after the firing if u is enabled after it, and leaves u without a stamp otherwise."
  assumes "A step relates two states of the executor (glossary: TSt), each holding a marking, the reading of the firing clock and a stamp per transition name; a step is a delay of the clock, a firing or a reap (TRel). Firings are atomic: the step that starts a firing completes it. Armed, Mid (the intermediate marking: inputs consumed, reset places drained, nothing deposited) and Enabled are the glossary terms."
          "The intermediate marking is computed from the marking of the state the firing step starts from, which is the live marking (ruling D7, revised). In a firing pass of several firings each firing is its own atomic step, so a token a synchronous action deposited earlier in the pass is in that marking and counts, as the section says. This agrees with a pass only for arcs that take a fixed number of tokens: a draining arc (reset, all(), atLeast(n)) later in a pass takes only the tokens present when the pass began ([EXEC-003] AC5), while Mid drains the live place. The section's bullet on reset places now carries the exception for this case (ruling 2): a same-pass deposit that the reset does not take ([EXEC-003] AC5) and that keeps the transition enabled in the intermediate marking keeps its clock. The Phase 1 relation has no pass, so a same-pass deposit never arises in it, and Mid draining the whole live place is the bullet without its exception; the exception, and an intermediate marking that keeps a deposit the reset does not take, are deferred to Phase 2 (RefExec). Outputs of an asynchronous action still in flight do not exist in the Phase 1 relation, which has no asynchronous actions. The enablement recheck of the pass ([EXEC-003] AC3-AC5) is not part of this block; see the next line. A synchronous action does not hide the gap: in the atomic Phase 1 step its deposit is the step's deposit d, which Mid t s.m never sees, so line 1 applies to a refill by the firing's own outputs (AC1). The asynchronous half is AC5, deferred below."
          "The fifth 'shall' sentence, 'If the enablement recheck of a firing pass finds a transition disabled ([EXEC-003] AC3), then the transition shall lose its clock, even when a same-pass deposit keeps it enabled in the live marking.', and the body's sentences on it (a transition the recheck finds disabled is disarmed even when a same-pass deposit refilled its place, and is newly armed, with a fresh stamp, by a later enablement update that finds it enabled) are not encoded and not quoted (ruling 1). The recheck judges a transition on the marking of the pass, which the atomic Phase 1 relation does not have: each firing is its own step and sees the live marking. Deferred to Phase 2 (RefExec), with the order of the two rules inside one pass: the intermediate-marking rule is applied at each firing on the live marking, and the recheck afterwards on the pass's marking, so a transition can keep its stamp through a firing by sentence 2 and then lose its clock to the recheck later in the same pass. The two rules are applied in sequence, they do not contradict each other."
          "To lose a clock is to hold no stamp after the firing. Sentences 1 and 4 together are line 1 of the formula: an armed transition other than t that is not enabled in the intermediate marking holds no stamp after the firing, unless it is enabled after it, in which case it is newly armed, that is armed with the current reading of the firing clock ([TIME-010]). Sentences 3 and 4 together are line 3, for the fired transition itself; it presupposes, as sentence 4 does, a clock to lose, so it speaks of the transition armed before the firing. An unarmed transition does not fire ([TIME-010] line 5). Line 2 is sentence 2. An armed transition enabled in the intermediate marking but not after the firing is disabled by the firing's deposit; that case is [TIME-011], not this block."
          "Transitions are identified by name (ruling D10): 'other than t' is 'named differently from t', and lines 1-3 speak of the transition the net holds under the name (InNet). Line 3 picks it by t's name, so a fired t that is not the net's transition of its name (a foreign or duplicate-named t) still restarts the clock under that name. The section assumes pairwise distinct names (NamesDistinct), under which InNet is membership in the net."
          "Bullet 1 (removing tokens never disables through an inhibitor arc) is time012_inhibitor_never: a transition enabled before whose input and read arcs still hold in the intermediate marking is enabled there. Its ν-join clause is not encoded: the Phase 1 relation has no ν correlation, it belongs to the NU blocks."
          "Bullet 2 (a reset arc drains its place) is time012_reset_disables, read as an input arc with a positive required count or a read arc on a reset place of t; with line 1 such a transition restarts its clock. Its exception for a same-pass deposit the reset does not take is Phase 2, as said above. An input arc whose required count is 0 stays enabled in a drained place and keeps its clock (the time012_Tzero conjuncts of TIME_012_ac3). Bullet 3 (surplus tokens keep the clock) is AC4. Bullet 4 (the fired transition always starts a fresh clock) is line 3."
          "AC1, AC2, AC3 and AC4 are the examples TIME_012_ac1 (input refill), TIME_012_ac2 (read only), TIME_012_ac3 (reset drain with a positive requirement) and TIME_012_ac4 (surplus keeps), in milliseconds, with T Delayed(5) and the refresh transition Immediate. TIME-012 fixes only the stamp a firing leaves; AC1's lower bound (T fires no earlier than d after the refill) follows from TIME-012 together with [TIME-010] lines 2 and 4, which frame the stamps across the other steps and gate the firing. TIME_012_ac1 shows the bound for the reference step: T does not fire 4 ms after the refill. AC5 (an asynchronous action) and AC6 (TransitionClockRestarted or TransitionEnabled) need in-flight actions and the event log, and are deferred to the Phase 2 executor; AC4's event clause (no TransitionClockRestarted or TransitionEnabled for T) needs the event log and is deferred with AC6. The state class graph's persistence rule ([VER-010]) is in Novel/TimedScg/Run.lean: persistence_rule, fired_never_persists, reset_restarts and surplus_keeps cite this ID."
          "A firing is instantaneous on the firing clock: that frame is not a sentence of this section and is not in the statement. Without it a firing fused with a hidden delay satisfies TIME-012 (TIME_012_gap_fireAdvancesClock); the frame is time012_FramesClock, which the reference satisfies (TIME_012_reference_framesClock) and which ConsistencyTime conjoins."
          "Injected tokens are not steps of the Phase 1 relation, which has no environment places, so injection plays no part here."
  signoff "pending"
  statement : ∀ {N : Type} [DecidableEq N], TRel N → Prop :=
    fun R => ∀ X : TimedNet _,
      (∀ t d u, InNet X u → u.core.name ≠ t.core.name →
          on (fun s s' => R X s (.fire t d) s'), shall (fun s s' => Armed s u →
            ¬ Enabled u (Mid t s.m) →
              (Enabled u s'.m → Armed s' u ∧ s'.stamp u.core.name = some (ClockReading s')) ∧
                (¬ Enabled u s'.m → s'.stamp u.core.name = none))) ∧
      (∀ t d u, InNet X u → u.core.name ≠ t.core.name →
          on (fun s s' => R X s (.fire t d) s'), shall (fun s s' => Armed s u →
            Enabled u (Mid t s.m) → Enabled u s'.m →
              s'.stamp u.core.name = s.stamp u.core.name)) ∧
      (∀ t d u, InNet X u → u.core.name = t.core.name →
          on (fun s s' => R X s (.fire t d) s'), shall (fun s s' => Armed s u →
            (Enabled u s'.m → Armed s' u ∧ s'.stamp u.core.name = some (ClockReading s')) ∧
              (¬ Enabled u s'.m → s'.stamp u.core.name = none)))

/- The pinned readable form of TIME-012: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.TIME_012 : {N : Type} → [DecidableEq N] → TRel N → Prop :=
fun {N} [DecidableEq N] R =>
  ∀ (X : TimedNet N),
    (∀ (t : Reference.Trans N) (d : List N) (u : Reference.Trans N),
        InNet X u →
          u.core.name ≠ t.core.name →
            on fun s s' => R X s (TLbl.fire t d) s', shall fun s s' =>
              Armed s u →
                ¬Enabled u (Mid t s.m) →
                  (Enabled u s'.m → Armed s' u ∧ s'.stamp u.core.name = some (ClockReading s')) ∧
                    (¬Enabled u s'.m → s'.stamp u.core.name = none)) ∧
      (∀ (t : Reference.Trans N) (d : List N) (u : Reference.Trans N),
          InNet X u →
            u.core.name ≠ t.core.name →
              on fun s s' => R X s (TLbl.fire t d) s', shall fun s s' =>
                Armed s u → Enabled u (Mid t s.m) → Enabled u s'.m → s'.stamp u.core.name = s.stamp u.core.name) ∧
        ∀ (t : Reference.Trans N) (d : List N) (u : Reference.Trans N),
          InNet X u →
            u.core.name = t.core.name →
              on fun s s' => R X s (TLbl.fire t d) s', shall fun s s' =>
                Armed s u →
                  (Enabled u s'.m → Armed s' u ∧ s'.stamp u.core.name = some (ClockReading s')) ∧
                    (¬Enabled u s'.m → s'.stamp u.core.name = none)
-/
#guard_msgs in #print TIME_012

/-! ### The three lines, for an intermediate marking `M` -/

section Lines

variable {N : Type} [DecidableEq N]

/-- The three lines of TIME-012 with the intermediate marking replaced by `M t m`. With
`M = Mid` they are TIME-012 (`time012Lines_mid`); the mutant readings choose another `M`. -/
def time012Lines (M : Trans N → CountMarking N → CountMarking N) (R : TRel N) : Prop :=
  ∀ X : TimedNet N,
    (∀ t d u, InNet X u → u.core.name ≠ t.core.name →
        on (fun s s' => R X s (.fire t d) s'), shall (fun s s' => Armed s u →
          ¬ Enabled u (M t s.m) →
            (Enabled u s'.m → Armed s' u ∧ s'.stamp u.core.name = some (ClockReading s')) ∧
              (¬ Enabled u s'.m → s'.stamp u.core.name = none))) ∧
    (∀ t d u, InNet X u → u.core.name ≠ t.core.name →
        on (fun s s' => R X s (.fire t d) s'), shall (fun s s' => Armed s u →
          Enabled u (M t s.m) → Enabled u s'.m →
            s'.stamp u.core.name = s.stamp u.core.name)) ∧
    (∀ t d u, InNet X u → u.core.name = t.core.name →
        on (fun s s' => R X s (.fire t d) s'), shall (fun s s' => Armed s u →
          (Enabled u s'.m → Armed s' u ∧ s'.stamp u.core.name = some (ClockReading s')) ∧
            (¬ Enabled u s'.m → s'.stamp u.core.name = none)))

theorem time012Lines_mid (R : TRel N) : TIME_012 R ↔ time012Lines (fun t m => Mid t m) R :=
  Iff.rfl

/-- The policy that keeps the stamp of an armed transition other than the fired one when it is
enabled in `M t m` and after the firing, takes a fresh stamp from `f`, and decides everything else
as the spec does. -/
def time012PolicyF (M : Trans N → CountMarking N → CountMarking N) (f : TSt N → Nat) :
    Policy N :=
  { refPolicy with
    keep := fun _ s t _ m' u =>
      (s.armed u && u.core.name != t.core.name && enabledNA (M t s.m) u.core &&
        enabledNA m' u.core),
    fresh := f }

/-- `time012PolicyF` with the spec's fresh stamp, the clock reading before the firing. -/
def time012Policy (M : Trans N → CountMarking N → CountMarking N) : Policy N :=
  time012PolicyF M (fun s => s.now)

/-- The spec's policy is the policy of the glossary's intermediate marking. -/
theorem time012Policy_mid : time012Policy (fun t m => Mid t m) = (refPolicy (N := N)) := by
  unfold time012Policy time012PolicyF refPolicy
  congr

/-- A transition that does not keep its stamp and was armed is armed again, with the reading
`f s`, exactly when it is enabled after the firing; otherwise it holds no stamp. -/
theorem time012_lost {M : Trans N → CountMarking N → CountMarking N} {f : TSt N → Nat}
    {X : TimedNet N} {t u : Trans N} {d : List N} {s s' : TSt N}
    (hs : s'.stamp u.core.name = restampW (time012PolicyF M f) X s t d s'.m u)
    (hn : ClockReading s' = f s) (ha : s.armed u = true)
    (hk : (time012PolicyF M f).keep X s t d s'.m u = false) :
    (Enabled u s'.m → Armed s' u ∧ s'.stamp u.core.name = some (ClockReading s')) ∧
      (¬ Enabled u s'.m → s'.stamp u.core.name = none) := by
  have hr : (time012PolicyF M f).rearm X s t d s'.m u = enabledNA s'.m u.core := by
    simp [time012PolicyF, refPolicy, ha]
  unfold restampW at hs
  rw [hk, hr] at hs
  refine ⟨fun hen => ?_, fun hen => ?_⟩
  · have hen' : enabledNA s'.m u.core = true := hen
    rw [if_neg (by simp), if_pos hen'] at hs
    refine ⟨⟨hen, by rw [hs]; rfl⟩, by rw [hs, hn]; rfl⟩
  · have hen' : ¬ enabledNA s'.m u.core = true := hen
    rw [if_neg (by simp), if_neg hen'] at hs
    exact hs

/-- The three lines read with `M` hold of every relation whose firing steps restamp the net's
transitions as `time012PolicyF M f` does and leave the clock reading `f s`, whatever the reading
`f` is. -/
theorem time012Lines_of (M : Trans N → CountMarking N → CountMarking N) (f : TSt N → Nat)
    (R : TRel N)
    (hR : ∀ X s t d s' u, R X s (.fire t d) s' → InNet X u →
      s'.stamp u.core.name = restampW (time012PolicyF M f) X s t d s'.m u ∧
        ClockReading s' = f s) :
    time012Lines M R := by
  intro X
  refine ⟨fun t d u hu hne s s' h ha hmid => ?_, fun t d u hu hne s s' h ha hmid hen => ?_,
    fun t d u hu heq s s' h ha => ?_⟩
  · obtain ⟨hs, hn⟩ := hR X s t d s' u h hu
    have ha' : s.armed u = true := (armed_iff s u).1 ha
    have hmid' : enabledNA (M t s.m) u.core = false := by simpa [Enabled] using hmid
    exact time012_lost hs hn ha' (by simp [time012PolicyF, hmid'])
  · obtain ⟨hs, -⟩ := hR X s t d s' u h hu
    have ha' : s.armed u = true := (armed_iff s u).1 ha
    have hk : (time012PolicyF M f).keep X s t d s'.m u = true := by
      simp only [time012PolicyF, Bool.and_eq_true]
      exact ⟨⟨⟨ha', by simpa using hne⟩, hmid⟩, hen⟩
    rw [hs]
    unfold restampW
    rw [if_pos hk]
  · obtain ⟨hs, hn⟩ := hR X s t d s' u h hu
    have ha' : s.armed u = true := (armed_iff s u).1 ha
    exact time012_lost hs hn ha' (by simp [time012PolicyF, heq])

/-- Every policy `time012Policy M` satisfies the three lines read with `M`. -/
theorem time012Lines_policy (M : Trans N → CountMarking N → CountMarking N) :
    time012Lines M (RefTStepW (time012Policy M)) := by
  refine time012Lines_of M (fun s => s.now) _ fun X s t d s' u h hu => ?_
  obtain ⟨-, -, -, -, -, he⟩ := refTStepW_fire_inv h
  refine ⟨?_, by rw [he]⟩
  rw [he]
  exact restampAll_inNet hu s t d s'.m

/-- **Local frame term (glossary request `FramesClock`).** A firing is instantaneous on the
firing clock: every firing step of `R` leaves the clock reading as it is. -/
def time012_FramesClock (R : TRel N) : Prop :=
  ∀ X s t d s', R X s (.fire t d) s' → ClockReading s' = ClockReading s

/-- Every step `RefTStepW P` frames the firing clock, whatever the policy. -/
theorem time012_framesClock_refW (P : Policy N) : time012_FramesClock (RefTStepW P) := by
  intro X s t d s' h
  obtain ⟨-, -, -, -, -, he⟩ := refTStepW_fire_inv h
  rw [he]

end Lines

/-- The timed reference step satisfies TIME-012: `refPolicy` keeps the stamp of an armed
transition other than the fired one exactly when it is enabled in the intermediate marking
(`mid`, which is the glossary's `Mid`) and after the firing (line 2), and otherwise re-arms an
armed transition with the current reading when it is enabled after the firing and drops its
stamp when it is not (lines 1 and 3; the fired transition is armed, since it fires). -/
@[evidence holds TIME_012]
theorem TIME_012_reference {N : Type} [DecidableEq N] : TIME_012 (RefTStep (N := N)) := by
  have := time012Lines_policy (N := N) (fun t m => Mid t m)
  rw [time012Policy_mid] at this
  exact this

/-! ### Bullets 1 and 2, for any net -/

section Bullets

variable {N : Type} [DecidableEq N]

/-- The intermediate marking never holds more tokens than the marking it comes from. -/
theorem time012_mid_le (t : Trans N) (m : CountMarking N) (p : N) : Mid t m p ≤ m p := by
  unfold Mid
  split <;> omega

/-- Bullet 1: removing tokens never disables through an inhibitor arc. A transition enabled at
`m` whose input arcs and read arcs still hold in the intermediate marking of `t` is enabled
there. -/
theorem time012_inhibitor_never (t u : Trans N) (m : CountMarking N) (hen : Enabled u m)
    (hin : ∀ a ∈ u.core.inputs, a.card.required ≤ Mid t m a.place)
    (hrd : ∀ p ∈ u.core.reads, 1 ≤ Mid t m p) : Enabled u (Mid t m) := by
  have h := hen
  unfold Enabled enabledNA at h ⊢
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h ⊢
  refine ⟨⟨hin, fun p hp => ?_⟩, hrd⟩
  have h1 := h.1.2 p hp
  have h2 := time012_mid_le t m p
  omega

/-- Bullet 2: a reset arc drains its place, so a transition with an input arc of positive
required count, or a read arc, on a reset place of `t` is not enabled in the intermediate marking
of `t`. By line 1 of TIME-012 its clock restarts. -/
theorem time012_reset_disables (t u : Trans N) (m : CountMarking N) (p : N) (hr : ResetArc t p)
    (huse : (∃ a ∈ u.core.inputs, a.place = p ∧ 1 ≤ a.card.required) ∨ ReadArc u p) :
    ¬ Enabled u (Mid t m) := by
  have hz : Mid t m p = 0 := by simp [Mid, hr]
  unfold Enabled enabledNA
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq, not_and]
  intro ⟨hin, _⟩ hrd
  rcases huse with ⟨a, ha, rfl, hreq⟩ | hp
  · have := hin a ha
    omega
  · have := hrd p hp
    omega

end Bullets

/-! ### Examples (AC1-AC4, bullets 1 and 2) -/

/-- `T` with one input arc on place `0` (AC1, AC3, AC4). -/
def time012_Tin : Trans Nat :=
  { core := { name := "T", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- `T` with only a read arc on place `0` (AC2). -/
def time012_Trd : Trans Nat :=
  { core := { name := "T", inputs := [], inhibitors := [], reads := [0], resets := [] },
    out := none }

/-- `T` with an input arc on place `0` whose required count is `0` (bullet 2's qualifier). -/
def time012_Tzero : Trans Nat :=
  { core :=
      { name := "T", inputs := [⟨0, .exactly 0⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- `T` with an input arc on place `1` and an inhibitor arc on place `0` (bullet 1). -/
def time012_Tinh : Trans Nat :=
  { core := { name := "T", inputs := [⟨1, .one⟩], inhibitors := [0], reads := [], resets := [] },
    out := none }

/-- The refresh transition: takes one token from place `0` and puts one back. -/
def time012_r : Trans Nat :=
  { core := { name := "r", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 0) }

/-- The draining refresh: resets place `0` and puts one token back (AC3). -/
def time012_z : Trans Nat :=
  { core := { name := "z", inputs := [], inhibitors := [], reads := [], resets := [0] },
    out := some (.place 0) }

/-- A transition that drains place `0` and deposits nothing (bullet 1). -/
def time012_y : Trans Nat :=
  { core := { name := "y", inputs := [], inhibitors := [], reads := [], resets := [0] },
    out := none }

/-- A transition that takes the token of place `0` and puts nothing back. -/
def time012_c : Trans Nat :=
  { core := { name := "c", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- The timing of the examples: `T` is `Delayed(5)`, every other transition `Immediate`. -/
def time012_timing (t : Trans Nat) : Timing :=
  if t.core.name = "T" then .delayed 5 else .immediate

/-- The timed net of the examples, with `T` the given transition; tolerance 0. -/
def time012_X (T : Trans Nat) : TimedNet Nat :=
  { net := { places := [0, 1, 2], transitions := [T, time012_r, time012_z, time012_y, time012_c] },
    timing := time012_timing, tol := 0 }

/-- The state at `T = 10` with marking `m`: every transition holds the stamp `0`. -/
def time012_s (m : Nat → Nat) : TSt Nat := { m := m, now := 10, stamp := fun _ => some 0 }

/-- The state after `t` fires with deposit `d` from `time012_s m`, in `time012_X T`, under
policy `P`. -/
def time012_after (P : Policy Nat) (T : Trans Nat) (m : Nat → Nat) (t : Trans Nat)
    (d : List Nat) : TSt Nat :=
  { m := fireNC m t.core (depProd d), now := 10,
    stamp := restampAll P (time012_X T) (time012_s m) t d (fireNC m t.core (depProd d)) }

/-- One token in place `0`. -/
def time012_m1 : Nat → Nat := fun p => if p = 0 then 1 else 0

/-- Two tokens in place `0` (AC4). -/
def time012_m2 : Nat → Nat := fun p => if p = 0 then 2 else 0

/-- One token in place `1`, place `0` empty (bullet 1). -/
def time012_mi : Nat → Nat := fun p => if p = 1 then 1 else 0

theorem time012_Tin_in : InNet (time012_X time012_Tin) time012_Tin := rfl
theorem time012_r_in : InNet (time012_X time012_Tin) time012_r := rfl

/-- AC1 (input refill): `T` consumes from place `0`, holding its one token, armed since `0`. At
`T = 10` the refresh `r` takes the token and puts one back. `T` is not enabled in the
intermediate marking and restarts its clock at `10`; the refresh itself restarts too (line 3).
With `Delayed(5)`, `T` cannot fire 4 ms after the refill, and can 5 ms after it. Without the
refill (`c` takes the token) `T` and `c` hold no stamp. -/
@[evidence nonvacuous TIME_012]
theorem TIME_012_ac1 :
    RefTStep (time012_X time012_Tin) (time012_s time012_m1) (.fire time012_r [0])
        (time012_after refPolicy time012_Tin time012_m1 time012_r [0]) ∧
      Armed (time012_s time012_m1) time012_Tin ∧
      ¬ Enabled time012_Tin (Mid time012_r time012_m1) ∧
      Armed (time012_after refPolicy time012_Tin time012_m1 time012_r [0]) time012_Tin ∧
      (time012_after refPolicy time012_Tin time012_m1 time012_r [0]).stamp "T" = some 10 ∧
      (time012_after refPolicy time012_Tin time012_m1 time012_r [0]).stamp "r" = some 10 ∧
      (∀ d s', ¬ RefTStep (time012_X time012_Tin)
        { time012_after refPolicy time012_Tin time012_m1 time012_r [0] with now := 14 }
        (.fire time012_Tin d) s') ∧
      (∃ s', RefTStep (time012_X time012_Tin)
        { time012_after refPolicy time012_Tin time012_m1 time012_r [0] with now := 15 }
        (.fire time012_Tin []) s') ∧
      RefTStep (time012_X time012_Tin) (time012_s time012_m1) (.fire time012_c [])
        (time012_after refPolicy time012_Tin time012_m1 time012_c []) ∧
      (time012_after refPolicy time012_Tin time012_m1 time012_c []).stamp "T" = none ∧
      (time012_after refPolicy time012_Tin time012_m1 time012_c []).stamp "c" = none := by
  refine ⟨RefTStepW.fire _ _ _ _ _ (by simp [time012_X]) ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
      (by decide) (by decide) (by decide), by decide, by decide, by decide, by decide, by decide,
    fun d s' h => ?_,
    ⟨_, RefTStepW.fire _ _ _ _ _ (by simp [time012_X]) ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
      (by decide) (by decide) (by decide)⟩,
    RefTStepW.fire _ _ _ _ _ (by simp [time012_X]) ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
      (by decide) (by decide) (by decide), by decide, by decide⟩
  obtain ⟨-, -, -, hg, -⟩ := refTStepW_fire_inv h
  revert hg
  decide

/-- AC2 (read only): `T` only reads place `0`. The refresh `r` empties it in the intermediate
marking, so `T` restarts its clock at `10`. -/
@[evidence nonvacuous TIME_012]
theorem TIME_012_ac2 :
    RefTStep (time012_X time012_Trd) (time012_s time012_m1) (.fire time012_r [0])
        (time012_after refPolicy time012_Trd time012_m1 time012_r [0]) ∧
      Armed (time012_s time012_m1) time012_Trd ∧
      ¬ Enabled time012_Trd (Mid time012_r time012_m1) ∧
      Armed (time012_after refPolicy time012_Trd time012_m1 time012_r [0]) time012_Trd ∧
      (time012_after refPolicy time012_Trd time012_m1 time012_r [0]).stamp "T" = some 10 :=
  ⟨RefTStepW.fire _ _ _ _ _ (by simp [time012_X]) ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
      (by decide) (by decide) (by decide), by decide, by decide, by decide, by decide⟩

/-- AC3 (reset drain, positive requirement): `z` drains place `0` through a reset arc and puts a
token back. `T`, whose input arc requires one token, restarts at `10`. With an input arc that
requires no token `T` stays enabled in the drained place and keeps its stamp `0`. -/
@[evidence nonvacuous TIME_012]
theorem TIME_012_ac3 :
    RefTStep (time012_X time012_Tin) (time012_s time012_m1) (.fire time012_z [0])
        (time012_after refPolicy time012_Tin time012_m1 time012_z [0]) ∧
      ¬ Enabled time012_Tin (Mid time012_z time012_m1) ∧
      (time012_after refPolicy time012_Tin time012_m1 time012_z [0]).stamp "T" = some 10 ∧
      RefTStep (time012_X time012_Tzero) (time012_s time012_m1) (.fire time012_z [0])
        (time012_after refPolicy time012_Tzero time012_m1 time012_z [0]) ∧
      Armed (time012_s time012_m1) time012_Tzero ∧
      Enabled time012_Tzero (Mid time012_z time012_m1) ∧
      (time012_after refPolicy time012_Tzero time012_m1 time012_z [0]).stamp "T" = some 0 :=
  ⟨RefTStepW.fire _ _ _ _ _ (by simp [time012_X]) ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
      (by decide) (by decide) (by decide), by decide, by decide,
    RefTStepW.fire _ _ _ _ _ (by simp [time012_X]) ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
      (by decide) (by decide) (by decide), by decide, by decide, by decide⟩

/-- The reset example of AC3 under bullet 2: `T`'s input arc on `z`'s reset place requires one
token, so `T` is not enabled in the intermediate marking whatever the marking. -/
theorem TIME_012_ac3_general (m : Nat → Nat) : ¬ Enabled time012_Tin (Mid time012_z m) :=
  time012_reset_disables _ _ m 0 (by decide) (.inl ⟨_, List.mem_singleton.2 rfl, rfl, by decide⟩)

/-- AC4 (surplus keeps): place `0` holds two tokens and the refresh takes one and returns one.
`T` stays enabled in the intermediate marking and keeps its stamp `0`. -/
@[evidence nonvacuous TIME_012]
theorem TIME_012_ac4 :
    RefTStep (time012_X time012_Tin) (time012_s time012_m2) (.fire time012_r [0])
        (time012_after refPolicy time012_Tin time012_m2 time012_r [0]) ∧
      Armed (time012_s time012_m2) time012_Tin ∧
      Enabled time012_Tin (Mid time012_r time012_m2) ∧
      Enabled time012_Tin (time012_after refPolicy time012_Tin time012_m2 time012_r [0]).m ∧
      (time012_after refPolicy time012_Tin time012_m2 time012_r [0]).stamp "T" = some 0 :=
  ⟨RefTStepW.fire _ _ _ _ _ (by simp [time012_X]) ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
      (by decide) (by decide) (by decide), by decide, by decide, by decide, by decide⟩

/-- Bullet 1: `T` consumes from place `1` and is inhibited by place `0`, which is empty. `y`
drains place `0` (a write, though it is empty); `T` stays enabled in the intermediate marking
and keeps its stamp `0`. -/
@[evidence nonvacuous TIME_012]
theorem TIME_012_inhibitor_keeps :
    RefTStep (time012_X time012_Tinh) (time012_s time012_mi) (.fire time012_y [])
        (time012_after refPolicy time012_Tinh time012_mi time012_y []) ∧
      Armed (time012_s time012_mi) time012_Tinh ∧
      Enabled time012_Tinh (Mid time012_y time012_mi) ∧
      (time012_after refPolicy time012_Tinh time012_mi time012_y []).stamp "T" = some 0 :=
  ⟨RefTStepW.fire _ _ _ _ _ (by simp [time012_X]) ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
      (by decide) (by decide) (by decide), by decide, by decide, by decide⟩

/-! ### Relations that keep or restart the wrong clocks -/

/-- The policy whose firing transition keeps its stamp when it is enabled after the firing, as
does every other armed transition enabled after it. -/
def time012_firedKeepsPolicy : Policy Nat :=
  { refPolicy with keep := fun _ s _ _ m' u => s.armed u && enabledNA m' u.core }

/-- ✗ A firing transition that keeps its clock violates TIME-012 (line 3): in AC1 the refresh
`r` fires at `T = 10`, is enabled after, and keeps its stamp `0` instead of restarting at `10`. -/
@[evidence forbids TIME_012]
theorem TIME_012_forbids_firedKeeps : ¬ TIME_012 (RefTStepW time012_firedKeepsPolicy) := by
  intro h
  have hstep : RefTStepW time012_firedKeepsPolicy (time012_X time012_Tin) (time012_s time012_m1)
      (.fire time012_r [0])
      (time012_after time012_firedKeepsPolicy time012_Tin time012_m1 time012_r [0]) :=
    RefTStepW.fire _ _ _ _ _ (by simp [time012_X]) ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
      (by decide) (by decide) (by decide)
  have e := ((h (time012_X time012_Tin)).2.2 _ _ _ time012_r_in rfl _ _ hstep (by decide)).1
    (by decide) |>.2
  exact absurd e (by decide)

/-- The policy that keeps no stamp: every firing restarts the clock of every transition armed
before it and enabled after it. -/
def time012_restartAllPolicy : Policy Nat := { refPolicy with keep := fun _ _ _ _ _ _ => false }

/-- ✗ Restarting every clock on every firing violates TIME-012 (line 2): in AC4 the refresh
leaves `T` enabled in the intermediate marking and after the firing, and `T` gets the stamp `10`
instead of keeping `0`. -/
@[evidence forbids TIME_012]
theorem TIME_012_forbids_restartAll : ¬ TIME_012 (RefTStepW time012_restartAllPolicy) := by
  intro h
  have hstep : RefTStepW time012_restartAllPolicy (time012_X time012_Tin) (time012_s time012_m2)
      (.fire time012_r [0])
      (time012_after time012_restartAllPolicy time012_Tin time012_m2 time012_r [0]) :=
    RefTStepW.fire _ _ _ _ _ (by simp [time012_X]) ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
      (by decide) (by decide) (by decide)
  have e := (h (time012_X time012_Tin)).2.1 _ _ _ time012_Tin_in (by decide) _ _ hstep
    (by decide) (by decide) (by decide)
  exact absurd e (by decide)

/-! ### Mutant: the rule before 6.0.0 (`survivesOld`) -/

/-- The pre-6.0.0 policy: an armed transition other than the fired one keeps its stamp when it
is enabled before and after the firing; the intermediate marking plays no part. -/
def time012_survivesOldPolicy : Policy Nat := time012Policy (fun _ m => m)

/-- Mutant reading of TIME-012 before 6.0.0: lines 1 and 2 test enablement in the marking before
the firing instead of the intermediate marking, so only the markings before and after the firing
are compared. Line 3 is as in TIME-012. -/
def TIME_012_mutant_survivesOld {N : Type} [DecidableEq N] (R : TRel N) : Prop :=
  time012Lines (fun _ m => m) R

/-- The pre-6.0.0 step kills the mutant: it satisfies the mutant reading, but not TIME-012. In
AC1 the refresh refills `T`'s input place in one firing; `T` is enabled before and after, so it
keeps its stamp `0` and would be ready at `5` instead of `15`. -/
@[evidence mutant TIME_012]
theorem TIME_012_mutant_survivesOld_killed :
    TIME_012_mutant_survivesOld (RefTStepW time012_survivesOldPolicy) ∧
      ¬ TIME_012 (RefTStepW time012_survivesOldPolicy) := by
  refine ⟨time012Lines_policy _, fun h => ?_⟩
  have hstep : RefTStepW time012_survivesOldPolicy (time012_X time012_Tin) (time012_s time012_m1)
      (.fire time012_r [0])
      (time012_after time012_survivesOldPolicy time012_Tin time012_m1 time012_r [0]) :=
    RefTStepW.fire _ _ _ _ _ (by simp [time012_X]) ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
      (by decide) (by decide) (by decide)
  have e := ((h (time012_X time012_Tin)).1 _ _ _ time012_Tin_in (by decide) _ _ hstep
    (by decide) (by decide)).1 (by decide) |>.2
  exact absurd e (by decide)

/-! ### Mutant: an intermediate marking without the resets (`noReset`) -/

/-- The intermediate marking without the reset arcs: inputs consumed, reset places left as they
are. -/
def time012_midNoReset {N : Type} [DecidableEq N] (t : Trans N) (m : CountMarking N) :
    CountMarking N :=
  fun p => m p - Consumes t m p

/-- The policy that keeps a stamp by `time012_midNoReset`. -/
def time012_noResetPolicy : Policy Nat := time012Policy time012_midNoReset

/-- Mutant reading of TIME-012 whose intermediate marking forgets the reset arcs. -/
def TIME_012_mutant_noReset {N : Type} [DecidableEq N] (R : TRel N) : Prop :=
  time012Lines time012_midNoReset R

/-- The step that ignores the resets kills the mutant: it satisfies the mutant reading, but not
TIME-012. In AC3 `z` drains `T`'s input place and puts a token back; without the drain `T` looks
enabled in the intermediate marking and keeps its stamp `0` instead of restarting at `10`. -/
@[evidence mutant TIME_012]
theorem TIME_012_mutant_noReset_killed :
    TIME_012_mutant_noReset (RefTStepW time012_noResetPolicy) ∧
      ¬ TIME_012 (RefTStepW time012_noResetPolicy) := by
  refine ⟨time012Lines_policy _, fun h => ?_⟩
  have hstep : RefTStepW time012_noResetPolicy (time012_X time012_Tin) (time012_s time012_m1)
      (.fire time012_z [0])
      (time012_after time012_noResetPolicy time012_Tin time012_m1 time012_z [0]) :=
    RefTStepW.fire _ _ _ _ _ (by simp [time012_X]) ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
      (by decide) (by decide) (by decide)
  have e := ((h (time012_X time012_Tin)).1 _ _ _ time012_Tin_in (by decide) _ _ hstep
    (by decide) (by decide)).1 (by decide) |>.2
  exact absurd e (by decide)

/-! ### The firing clock across a firing (`fireAdvancesClock`) -/

/-- The timed reference step frames the firing clock: a firing leaves the clock reading as it
is. TIME-012 alone does not say so (`TIME_012_gap_fireAdvancesClock`); the frame is the glossary
request `FramesClock`, here `time012_FramesClock`. -/
theorem TIME_012_reference_framesClock {N : Type} [DecidableEq N] :
    time012_FramesClock (RefTStep (N := N)) :=
  time012_framesClock_refW _

/-- The policy that stamps a restarted clock `1000` ms after the firing starts. -/
def time012_advPolicy : Policy Nat := time012PolicyF (fun t m => Mid t m) (fun s => s.now + 1000)

/-- A firing fused with a hidden delay of `1000` ms: the firing step is a step of
`time012_advPolicy` whose clock then reads `1000` ms later. Delays and reaps are as in the
reference. -/
def time012_fireAdvancesClock : TRel Nat := fun X s l s' =>
  ∃ s0, RefTStepW time012_advPolicy X s l s0 ∧
    s' = { s0 with now := s0.now + (match l with | .fire _ _ => 1000 | _ => 0) }

/-- ✗ The hidden delay is a gap of TIME-012, closed by the clock frame: `fireAdvancesClock`
satisfies TIME-012, since it stamps every restarted clock with the reading after the firing,
and it does not frame the firing clock. In AC1 the refresh fires at `10` and the clock reads
`1010` after it, so every clock the firing keeps gains `1000` ms without a delay step. -/
theorem TIME_012_gap_fireAdvancesClock :
    TIME_012 time012_fireAdvancesClock ∧ ¬ time012_FramesClock time012_fireAdvancesClock := by
  refine ⟨time012Lines_of _ (fun s => s.now + 1000) _ fun X s t d s' u h hu => ?_, fun h => ?_⟩
  · obtain ⟨s0, h0, rfl⟩ := h
    obtain ⟨-, -, -, -, -, he⟩ := refTStepW_fire_inv h0
    refine ⟨?_, by rw [he]⟩
    rw [he]
    exact restampAll_inNet hu s t d s0.m
  · have hstep : RefTStepW time012_advPolicy (time012_X time012_Tin) (time012_s time012_m1)
        (.fire time012_r [0])
        (time012_after time012_advPolicy time012_Tin time012_m1 time012_r [0]) :=
      RefTStepW.fire _ _ _ _ _ (by simp [time012_X]) ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
        (by decide) (by decide) (by decide)
    have e := h _ _ _ _ _ ⟨_, hstep, rfl⟩
    exact absurd e (by decide)

end Libpetri.Spec
