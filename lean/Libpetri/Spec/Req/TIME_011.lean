import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryTime
import Libpetri.Spec.Req.TIME_010

set_option linter.missingDocs true

/-!
# TIME-011: Clock restarts on re-enablement (`spec/03-timing.md`)

The requirement is a predicate over an abstract timed step relation `R : TRel N` (glossary
`GlossaryTime.lean`), like [TIME-010]. The evidence theorems check it against the timed reference
step (`RefTStep`), against a relation that fires without touching any stamp, against the mutant
that resumes the clock a transition held before it was disabled, and against the mutant that
reads "discard" as "disarm" and keeps the stamp of a disabled transition (a step TIME-010 admits).
`time011_backdate_gap` shows why the later steps are left to TIME-010. AC1 is the
nonvacuous example: `Delayed(5 s)`, disabled at `3 s`, enabled again at `7 s`, ready at `12 s`,
in milliseconds as the timings are.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Novel.TimedScg (Timing)

/-! ## TIME-011: Clock restarts on re-enablement -/

requirement TIME_011
  id "TIME-011"
  title "Clock Restarts on Re-enablement"
  kind T
  scope "all executors"
  source verbatim "spec/03-timing.md"
  quote "If a transition stops being armed and is later armed again, the clock restarts from zero."
        "The previous elapsed time is discarded."
        "*When* an armed transition stops being enabled, the executor *shall* discard its stamp."
        "*When* a transition that lost its clock is armed again, its elapsed time *shall* be measured from the moment it was armed again, not from any earlier stamp."
  reading "For every timed net X:"
          "a transition of the net that is armed before a step and is not enabled at the marking after it holds no stamp after the step;"
          "a transition of the net that is not armed before a step and is armed after it holds the reading of the firing clock after the step."
  assumes "A step relates two states of the executor (glossary: TSt), each holding a marking, the reading of the firing clock and a stamp per transition name; a step is a delay of the clock, a firing or a reap (TRel). Firings are atomic: the step that starts a firing completes it. Armed, Enabled and Elapsed time are the glossary terms (GlossaryTime.lean): a transition is armed when it is enabled at the marking and holds a stamp."
          "Line 1 is the first 'shall' sentence. 'Discard its stamp' is read on the state: the transition holds no stamp after the step (none), not merely that it is not armed, which a transition that is not enabled never is. The line is the hygiene of the state the sentence literally asks for: no glossary predicate reads the stamp of a transition that is not enabled (Armed, Ready and Expired all ask for it enabled), and a stale stamp cannot be resumed because line 2 overwrites it when the transition is armed again. TIME_011_mutant_disarm_killed shows the line is not implied by its weaker 'disarm' reading, and time011_lazy_TIME_010 that the stale-stamp step it kills satisfies TIME-010. The line reads only the marking after the step: a transition disabled in the intermediate marking of a firing and enabled again after it is TIME-012 (ruling D7), whose pre-6.0.0 mutant (keep a stamp when enabled before and after, the intermediate marking playing no part) TIME_012_mutant_survivesOld_killed kills."
          "Line 2 is the second 'shall' sentence and the restart of the opening paragraph. A transition that is not armed before a step may still hold a stamp (a stale one, or none after a reap, [TIME-013]); no resume is possible because the line asks every such transition armed after the step to hold the current reading, overwriting whatever it held, so its elapsed time is 0 after the step and is measured from that reading. It is the stamp value of TIME-010 line 1 without TIME-010's question of which steps may arm (time011_line2_of_time010): next to TIME-010, line 1 is the only line this block adds (time011_iff_line1), and the resuming mutant it kills is the one TIME-010 kills too. Which steps re-arm (a firing that writes an arc place, ruling D6) is TIME-010, not this block."
          "'Measured from the moment it was armed again' over the later steps is TIME-010 line 2: a transition armed before and after a step keeps its stamp unless a firing restarts its clock ([TIME-012]). This block does not restate it: TIME-011 alone admits a delay that backdates the stamp of a transition that stays armed, which TIME-010 line 2 forbids (time011_backdate_gap). time011_elapsed_from_rearm derives the elapsed time after a delay from TIME-010 and TIME-011 together, which is how ConsistencyTime conjoins them."
          "An injected token can also disable or re-arm a transition ([ENV-003], ruling D6). Injection is not a step of the Phase 1 relation, which has no environment places; the two lines are stated for the steps it has."
          "Transitions are identified by name (ruling D10): a stamp is kept per name, and both lines speak of the transition the net holds under the name (InNet). Under pairwise distinct names (NamesDistinct) InNet is membership in the net (inNet_iff_mem)."
          "AC1 (Delayed(5 s), disabled at 3 s, re-enabled later, waits another 5 s) is TIME_011_nonvacuous in milliseconds: u is armed at 0, a consumer takes its token at 3000 and u holds no stamp (line 1), the source refills the place at 7000 and u is armed with the stamp 7000 (line 2), u cannot fire at 11999 and can at 12000. The resuming mutant would let u fire at 7000. For every relation satisfying TIME-010 and TIME-011 whose delay advances the clock by the delay, a transition armed again cannot fire after a delay shorter than its earliest bound (time011_no_early_fire)."
  signoff "2026-11-13 79f782cb6058365b ai"
  statement : ∀ {N : Type} [DecidableEq N], TRel N → Prop :=
    fun R => ∀ X : TimedNet _,
      (∀ l u, InNet X u → on (fun s s' => R X s l s'), shall (fun s s' =>
          Armed s u → ¬ Enabled u s'.m → s'.stamp u.core.name = none)) ∧
      (∀ l u, InNet X u → on (fun s s' => R X s l s'), shall (fun s s' =>
          ¬ Armed s u → Armed s' u → s'.stamp u.core.name = some (ClockReading s')))

/- The pinned readable form of TIME-011: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.TIME_011 : {N : Type} → [DecidableEq N] → TRel N → Prop :=
fun {N} [DecidableEq N] R =>
  ∀ (X : TimedNet N),
    (∀ (l : TLbl N) (u : Reference.Trans N),
        InNet X u →
          on fun s s' => R X s l s', shall fun s s' => Armed s u → ¬Enabled u s'.m → s'.stamp u.core.name = none) ∧
      ∀ (l : TLbl N) (u : Reference.Trans N),
        InNet X u →
          on fun s s' => R X s l s', shall fun s s' =>
            ¬Armed s u → Armed s' u → s'.stamp u.core.name = some (ClockReading s')
-/
#guard_msgs in #print TIME_011

/-! ### The two lines, for any policy -/

section Lines

variable {N : Type} [DecidableEq N]

/-- The spec's `keep` keeps a stamp only for a transition enabled after the firing. -/
theorem refPolicy_keep_enabled (X : TimedNet N) (s : TSt N) (t : Trans N) (d : List N)
    (m' : N → Nat) (u : Trans N) (h : (refPolicy (N := N)).keep X s t d m' u = true) :
    enabledNA m' u.core = true := by
  simp only [refPolicy, Bool.and_eq_true] at h
  exact h.2

/-- The spec's `rearm` arms only a transition enabled after the firing. -/
theorem refPolicy_rearm_enabled (X : TimedNet N) (s : TSt N) (t : Trans N) (d : List N)
    (m' : N → Nat) (u : Trans N) (h : (refPolicy (N := N)).rearm X s t d m' u = true) :
    enabledNA m' u.core = true := by
  simp only [refPolicy, Bool.and_eq_true] at h
  exact h.1

/-- Line 1 for any policy whose `keep` and `rearm` ask for the transition enabled after the
firing: a step that leaves an armed transition of the net disabled leaves it no stamp. A delay
or a reap cannot disable it, since it keeps the marking. -/
theorem time011_discard {P : Policy N}
    (hk : ∀ X s t d m' u, P.keep X s t d m' u = true → enabledNA m' u.core = true)
    (hr : ∀ X s t d m' u, P.rearm X s t d m' u = true → enabledNA m' u.core = true)
    {X : TimedNet N} {u : Trans N} (hu : InNet X u) {s s' : TSt N} {l : TLbl N}
    (h : RefTStepW P X s l s') (ha : Armed s u) (hne : ¬ Enabled u s'.m) :
    s'.stamp u.core.name = none := by
  cases l with
  | delay δ =>
    exact absurd (by rw [refTStepW_marking h (fun _ _ e => by cases e)]; exact ha.1) hne
  | reap t =>
    exact absurd (by rw [refTStepW_marking h (fun _ _ e => by cases e)]; exact ha.1) hne
  | fire t d =>
    obtain ⟨-, -, -, -, -, he⟩ := refTStepW_fire_inv h
    have hne' : enabledNA s'.m u.core ≠ true := hne
    rw [he]
    show restampAll P X s t d s'.m u.core.name = none
    rw [restampAll_inNet hu]
    unfold restampW
    rw [if_neg (fun h1 => hne' (hk _ _ _ _ _ _ h1)), if_neg (fun h2 => hne' (hr _ _ _ _ _ _ h2))]

/-- Line 2 for any policy whose `keep` keeps a stamp only for a transition that was armed or is
disabled after the firing: a transition of the net newly armed by a step was armed by a firing,
through `rearm`, and holds the policy's fresh reading, and the clock reading is unchanged. It is
`time010_newly` under a weaker hypothesis on `keep`. -/
theorem time011_fresh {P : Policy N}
    (hk : ∀ X s t d m' u, P.keep X s t d m' u = true →
      s.armed u = true ∨ enabledNA m' u.core = false)
    {X : TimedNet N} {u : Trans N} (hu : InNet X u) {s s' : TSt N} {l : TLbl N}
    (h : RefTStepW P X s l s') (hna : ¬ Armed s u) (ha : Armed s' u) :
    ∃ t d, l = .fire t d ∧ P.rearm X s t d s'.m u = true ∧
      s'.stamp u.core.name = some (P.fresh s) ∧ ClockReading s' = ClockReading s := by
  cases l with
  | delay δ => exact absurd (time010_nonfire_armed h (fun _ _ e => by cases e) u ha) hna
  | reap t => exact absurd (time010_nonfire_armed h (fun _ _ e => by cases e) u ha) hna
  | fire t d =>
    obtain ⟨-, -, -, -, -, he⟩ := refTStepW_fire_inv h
    have hna' : s.armed u = false := by simpa [armed_iff] using hna
    have hen : enabledNA s'.m u.core = true := ha.1
    have hs : s'.stamp u.core.name = restampW P X s t d s'.m u := by
      rw [he]; exact restampAll_inNet hu s t d s'.m
    have hsome := ha.2
    rw [hs] at hsome
    unfold restampW at hs hsome
    have h1 : ¬ P.keep X s t d s'.m u = true := fun h1 => by
      rcases hk _ _ _ _ _ _ h1 with h | h
      · simp [h] at hna'
      · simp [h] at hen
    rw [if_neg h1] at hs hsome
    by_cases h2 : P.rearm X s t d s'.m u = true
    · rw [if_pos h2] at hs
      exact ⟨t, d, rfl, h2, hs, by rw [he]⟩
    · rw [if_neg h2] at hsome
      simp at hsome

/-- The weaker line 2 of the mutant readings, for any policy that stamps with the current
reading: a transition newly armed by a step holds the stamp it held or the current reading. -/
theorem time011_old_or_fresh {P : Policy N} (hf : ∀ s, P.fresh s = s.now) {X : TimedNet N}
    {u : Trans N} {s s' : TSt N} {l : TLbl N} (h : RefTStepW P X s l s') (ha : Armed s' u) :
    s'.stamp u.core.name = s.stamp u.core.name ∨
      s'.stamp u.core.name = some (ClockReading s') := by
  rcases time010_stamp_cases h u ha with e | ⟨-, e, hn⟩
  · exact .inl e
  · exact .inr (by rw [e, hn, hf])

end Lines

/-- The timed reference step satisfies TIME-011: a delay or a reap keeps the marking, so it
disables nothing, and a firing that leaves a transition disabled neither keeps its stamp nor
re-arms it, since `refPolicy`'s `keep` and `rearm` both ask for the transition enabled after the
firing (line 1); a step newly arms a transition only as a firing, through `refPolicy.rearm`,
with the current reading (`time010_newly`, line 2). -/
@[evidence holds TIME_011]
theorem TIME_011_reference {N : Type} [DecidableEq N] : TIME_011 (RefTStep (N := N)) := by
  intro X
  refine ⟨fun l u hu s s' h ha hne =>
    time011_discard refPolicy_keep_enabled refPolicy_rearm_enabled hu h ha hne,
    fun l u hu s s' h hna ha => ?_⟩
  obtain ⟨t, d, rfl, -, e, hn⟩ := time010_newly refPolicy_keep_armed hu h hna ha
  rw [e, hn]
  rfl

/-- TIME-011 and TIME-010 together measure the elapsed time of a transition armed again from
the moment it was armed again: after a step newly arms `u` and the clock then advances by `δ`
with `u` still armed, its elapsed time is `δ`. TIME-011 line 2 gives the stamp at the re-arming
step, TIME-010 line 2 keeps it across the delay. -/
@[evidence cites "TIME-011" "its elapsed time shall be measured from the moment it was armed again, not from any earlier stamp: derived over two steps from TIME-011 line 2 (fresh stamp) and TIME-010 line 2 (an armed transition keeps its stamp across a delay)"]
theorem time011_elapsed_from_rearm {N : Type} [DecidableEq N] {R : TRel N} (h10 : TIME_010 R)
    (h11 : TIME_011 R) {X : TimedNet N} {u : Trans N} (hu : InNet X u) {s0 s1 s2 : TSt N}
    {l : TLbl N} {δ : Nat} (h1 : R X s0 l s1) (hna : ¬ Armed s0 u) (ha1 : Armed s1 u)
    (h2 : R X s1 (.delay δ) s2) (ha2 : Armed s2 u)
    (hc : ClockReading s2 = ClockReading s1 + δ) : Elapsed s2 u = δ := by
  have e1 := (h11 X).2 l u hu s0 s1 h1 hna ha1
  rcases (h10 X).2.1 (.delay δ) u s1 s2 h2 ha1 ha2 with e2 | ⟨⟨t, d, e⟩, -⟩
  · simp only [Elapsed, e2, e1, hc, Option.getD_some]
    omega
  · cases e

/-- TIME-011 line 2 follows from TIME-010 line 1, which has the same antecedents and concludes
the same stamp next to the firing that arms. In the conjunction ConsistencyTime takes, line 2 adds
nothing to TIME-010; it is stated so that the block reads its second 'shall' sentence on its own. -/
theorem time011_line2_of_time010 {N : Type} [DecidableEq N] {R : TRel N} (h10 : TIME_010 R)
    (X : TimedNet N) :
    ∀ l u, InNet X u → on (fun s s' => R X s l s'), shall (fun s s' =>
      ¬ Armed s u → Armed s' u → s'.stamp u.core.name = some (ClockReading s')) :=
  fun l u hu s s' h hna ha => by
    obtain ⟨_, _, -, -, e⟩ := (h10 X).1 l u hu s s' h hna ha
    exact e

/-- Next to TIME-010, TIME-011 is its line 1 alone: discarding the stamp of an armed transition
a step leaves disabled is the only content this block adds to the conjunction. -/
theorem time011_iff_line1 {N : Type} [DecidableEq N] {R : TRel N} (h10 : TIME_010 R) :
    TIME_011 R ↔ ∀ X : TimedNet N, ∀ l u, InNet X u → on (fun s s' => R X s l s'),
      shall (fun s s' => Armed s u → ¬ Enabled u s'.m → s'.stamp u.core.name = none) :=
  ⟨fun h X => (h X).1, fun h X => ⟨h X, time011_line2_of_time010 h10 X⟩⟩

/-- AC1 for every relation that satisfies TIME-010 and TIME-011 and advances the clock by the
delay: a transition armed again by a step cannot fire after a delay shorter than its earliest
bound, measured from the re-arming. If it is still armed its elapsed time is the delay
(`time011_elapsed_from_rearm`) and TIME-010 line 4 forbids the firing; if not, TIME-010 line 5
does. -/
@[evidence cites "TIME-011" "AC1: a transition armed again must wait its full earliest bound from the moment it was armed again, for every relation satisfying TIME-010 and TIME-011 whose delay advances the clock by the delay"]
theorem time011_no_early_fire {N : Type} [DecidableEq N] {R : TRel N} (h10 : TIME_010 R)
    (h11 : TIME_011 R) {X : TimedNet N} {u : Trans N} (hu : InNet X u) {s0 s1 s2 : TSt N}
    {l : TLbl N} {δ : Nat} (h1 : R X s0 l s1) (hna : ¬ Armed s0 u) (ha1 : Armed s1 u)
    (h2 : R X s1 (.delay δ) s2) (hc : ClockReading s2 = ClockReading s1 + δ)
    (hlt : δ < (TimingOf X u).earliest) : ¬ ∃ d s3, R X s2 (.fire u d) s3 := by
  rintro ⟨d, s3, h3⟩
  by_cases ha2 : Armed s2 u
  · exact (h10 X).2.2.2.1 u s2 s3 ⟨d, h3⟩
      ⟨ha2, by rw [time011_elapsed_from_rearm h10 h11 hu h1 hna ha1 h2 ha2 hc]; exact hlt⟩
  · exact (h10 X).2.2.2.2 u s2 s3 ⟨d, h3⟩ ha2

/-! ### Example (AC1, in milliseconds) -/

/-- The source of the example: no arcs, one output on place `0`. -/
def time011_src : Trans Nat :=
  { core := { name := "src", inputs := [], inhibitors := [], reads := [], resets := [] },
    out := some (.place 0) }

/-- The transition of AC1: one input arc on place `0`, no output spec. -/
def time011_u : Trans Nat :=
  { core := { name := "u", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- The consumer that disables `u`: one input arc on place `0`, no output spec. -/
def time011_c : Trans Nat :=
  { core := { name := "c", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- The timing of the example: `u` is `Delayed(5000)`, every other transition `Immediate`. -/
def time011_timing (t : Trans Nat) : Timing :=
  if t.core.name = "u" then .delayed 5000 else .immediate

/-- The timed net of AC1: the source, `u` and the consumer, tolerance 0. -/
def time011_X : TimedNet Nat :=
  { net := { places := [0], transitions := [time011_src, time011_u, time011_c] },
    timing := time011_timing, tol := 0 }

theorem time011_u_inX : InNet time011_X time011_u := rfl

/-- The initial marking: one token in place `0`. -/
def time011_m0 : Nat → Nat := fun p => if p = 0 then 1 else 0

/-- The initial state at `T = 0`: every transition is enabled, so every one is stamped `0`. -/
def time011_a0 : TSt Nat := TSt.init time011_X time011_m0 0

/-- The state at `T = 3000`, before the consumer fires. -/
def time011_a1 : TSt Nat := { time011_a0 with now := 3000 }

/-- The marking after the consumer takes the token: place `0` is empty. -/
def time011_m2 : Nat → Nat := fireNC time011_m0 time011_c.core (depProd [])

/-- The state after the consumer fires at `T = 3000` under policy `P`. -/
def time011_a2 (P : Policy Nat) : TSt Nat :=
  { m := time011_m2, now := 3000, stamp := restampAll P time011_X time011_a1 time011_c [] time011_m2 }

/-- The state at `T = 7000`, after a delay of 4000 from `time011_a2 P`. -/
def time011_a3 (P : Policy Nat) : TSt Nat := { time011_a2 P with now := 7000 }

/-- The marking after the source refills place `0`. -/
def time011_m4 : Nat → Nat := fireNC time011_m2 time011_src.core (depProd [0])

/-- The state after the source fires at `T = 7000` under policy `P`. -/
def time011_a4 (P : Policy Nat) : TSt Nat :=
  { m := time011_m4, now := 7000,
    stamp := restampAll P time011_X (time011_a3 P) time011_src [0] time011_m4 }

/-- The consumer fires at `T = 3000` under every policy whose gate and expiry are the spec's. -/
theorem time011_c_fires {P : Policy Nat} (hg : P.gate = refPolicy.gate)
    (hx : P.expired = refPolicy.expired) :
    RefTStepW P time011_X time011_a1 (.fire time011_c []) (time011_a2 P) := by
  refine RefTStepW.fire _ _ _ _ _ (by simp [time011_X]) ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
    (by decide) ?_ ?_
  · rw [hg]; decide
  · rw [hx]; decide

/-- The source fires at `T = 7000` under every policy whose gate and expiry are the spec's and
that left the source armed. -/
theorem time011_src_fires {P : Policy Nat} (hg : P.gate = refPolicy.gate)
    (hx : P.expired = refPolicy.expired) (ha : (time011_a3 P).armed time011_src = true) :
    RefTStepW P time011_X (time011_a3 P) (.fire time011_src [0]) (time011_a4 P) := by
  have hf : Fires time011_src time011_m2 [0] time011_m4 := ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
  refine RefTStepW.fire _ _ _ _ _ (by simp [time011_X]) hf ha ?_ ?_
  · rw [hg]
    simp [refPolicy, time011_X, time011_timing, time011_src, Timing.earliest]
  · rw [hx]
    simp [refPolicy, tExpired, time011_X, time011_timing, time011_src, Timing.reapable]

/-- A relation that fires every reference firing and leaves every stamp as it is: nothing else
is a step. -/
def time011_frozen : TRel Nat := fun _ s l s' =>
  match l with
  | .fire t d => RefFire t s.m d s'.m ∧ s'.now = s.now ∧ s'.stamp = s.stamp
  | _ => False

/-- ✗ A firing that leaves every stamp in place violates TIME-011 (line 1): at `T = 3000` the
consumer takes `u`'s token, and `u`, disabled, still holds the stamp `0`. -/
@[evidence forbids TIME_011]
theorem TIME_011_forbids_frozen : ¬ TIME_011 time011_frozen := by
  intro h
  have hfire : time011_frozen time011_X time011_a1 (.fire time011_c [])
      { m := time011_m2, now := 3000, stamp := time011_a1.stamp } :=
    ⟨⟨by decide, ⟨.action 0, rfl⟩, rfl⟩, rfl, rfl⟩
  exact absurd ((h time011_X).1 _ time011_u time011_u_inX _ _ hfire (by decide) (by decide))
    (by decide)

/-! ### Mutant: the clock resumes after a disablement -/

/-- Mutant reading of TIME-011 in which the clock pauses and resumes: a disabled transition is
only disarmed (line 1 holds of every relation), and a transition armed again holds the stamp it
held or the current reading (line 2). -/
def TIME_011_mutant_resume {N : Type} [DecidableEq N] (R : TRel N) : Prop :=
  ∀ X : TimedNet N,
    (∀ l u, InNet X u → on (fun s s' => R X s l s'), shall (fun s s' =>
        Armed s u → ¬ Enabled u s'.m → ¬ Armed s' u)) ∧
    (∀ l u, InNet X u → on (fun s s' => R X s l s'), shall (fun s s' =>
        ¬ Armed s u → Armed s' u → s'.stamp u.core.name = s.stamp u.core.name ∨
          s'.stamp u.core.name = some (ClockReading s')))

/-- The resuming step (`time010_resumePolicy`: every stamp a transition other than the fired one
holds is kept, armed or not) kills the mutant: it satisfies the mutant reading, but not
TIME-011. In AC1, `u` keeps its stamp `0` while the consumer's firing leaves it disabled, and
when the source refills its place at `T = 7000` it is armed again with the stamp `0`, so it
could fire at once instead of at `T = 12000`. -/
@[evidence mutant TIME_011]
theorem TIME_011_mutant_resume_killed :
    TIME_011_mutant_resume (RefTStepW time010_resumePolicy) ∧
      ¬ TIME_011 (RefTStepW time010_resumePolicy) := by
  refine ⟨fun X => ⟨fun l u _ s s' _ _ hne ha => hne ha.1,
      fun l u _ s s' h _ ha => time011_old_or_fresh (fun _ => rfl) h ha⟩, fun h => ?_⟩
  have hstep := time011_src_fires (P := time010_resumePolicy) rfl rfl (by decide)
  exact absurd ((h time011_X).2 _ time011_u time011_u_inX _ _ hstep (by decide) (by decide))
    (by decide)

/-! ### Mutant: "discard" read as "disarm" -/

/-- The policy that keeps the stamp of every transition the firing leaves disabled, and decides
everything else as the spec does: a disabled transition is not armed, but holds a stale stamp. -/
def time011_lazyPolicy : Policy Nat :=
  { refPolicy with keep := fun X s t d m' u =>
      refPolicy.keep X s t d m' u || ((s.stamp u.core.name).isSome && !enabledNA m' u.core) }

/-- Mutant reading of TIME-011 that reads "discard its stamp" as "disarm it": a disabled
transition is only not armed (line 1 holds of every relation). Line 2 is as in TIME-011. -/
def TIME_011_mutant_disarm {N : Type} [DecidableEq N] (R : TRel N) : Prop :=
  ∀ X : TimedNet N,
    (∀ l u, InNet X u → on (fun s s' => R X s l s'), shall (fun s s' =>
        Armed s u → ¬ Enabled u s'.m → ¬ Armed s' u)) ∧
    (∀ l u, InNet X u → on (fun s s' => R X s l s'), shall (fun s s' =>
        ¬ Armed s u → Armed s' u → s'.stamp u.core.name = some (ClockReading s')))

/-- The lazy `keep` keeps a stamp only for a transition that was armed or that the firing leaves
disabled. -/
theorem time011_lazy_keep : ∀ X s t d m' u, time011_lazyPolicy.keep X s t d m' u = true →
    s.armed u = true ∨ enabledNA m' u.core = false := fun X s t d m' u h => by
  simp only [time011_lazyPolicy, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with h | ⟨-, h⟩
  · exact .inl (refPolicy_keep_armed X s t d m' u h)
  · exact .inr h

/-- The step that keeps stale stamps kills the mutant: it satisfies the mutant reading, since a
transition armed again still gets the current reading, but not TIME-011, since at `T = 3000`
the consumer's firing leaves `u` disabled with the stamp `0`. -/
@[evidence mutant TIME_011]
theorem TIME_011_mutant_disarm_killed :
    TIME_011_mutant_disarm (RefTStepW time011_lazyPolicy) ∧
      ¬ TIME_011 (RefTStepW time011_lazyPolicy) := by
  refine ⟨fun X => ⟨fun l u _ s s' _ _ hne ha => hne ha.1, fun l u hu s s' h hna ha => ?_⟩,
    fun h => ?_⟩
  · obtain ⟨-, -, -, -, e, hn⟩ := time011_fresh time011_lazy_keep hu h hna ha
    rw [e, hn]
    rfl
  · exact absurd ((h time011_X).1 _ time011_u time011_u_inX _ _
      (time011_c_fires (P := time011_lazyPolicy) rfl rfl) (by decide) (by decide)) (by decide)

/-- The stale-stamp step satisfies TIME-010, so the disarm mutant is one that only TIME-011
kills: TIME-010 never reads the stamp of a transition that is not enabled, and the stale stamp
is overwritten when the transition is armed again (`time011_fresh`). The difference from the
reference is state no glossary predicate reads (Armed, Ready and Expired all ask for the
transition enabled); TIME-011 line 1 asks for it because the spec's sentence says "discard its
stamp". -/
theorem time011_lazy_TIME_010 : TIME_010 (RefTStepW time011_lazyPolicy) := by
  have hk : ∀ X s t d m' u, time011_lazyPolicy.keep X s t d m' u = true →
      (s.stamp u.core.name).isSome = true := fun X s t d m' u h => by
    simp only [time011_lazyPolicy, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h, -⟩
    · exact refPolicy_keep_stamp X s t d m' u h
    · exact h
  intro X
  refine ⟨fun l u hu s s' h hna ha => ?_, fun l u s s' h _ ha => ?_,
    fun t d u hu s s' h => time010_arms (P := time011_lazyPolicy) hk refPolicy_rearm_writes hu h,
    fun u s s' ⟨d, h⟩ ⟨_, hlt⟩ =>
      absurd (time010_gate (P := time011_lazyPolicy) rfl h) (by omega),
    fun u s s' ⟨d, h⟩ hna => hna (time010_armed h)⟩
  · obtain ⟨t, d, rfl, hr, e, hn⟩ := time011_fresh time011_lazy_keep hu h hna ha
    have hna' : s.armed u = false := by simpa [armed_iff] using hna
    simp only [time011_lazyPolicy, refPolicy, hna', Bool.false_or, Bool.and_eq_true] at hr
    exact ⟨t, d, rfl, (writesArc_iff t d u).1 hr.2, by rw [e, hn]; rfl⟩
  · rcases time010_stamp_cases h u ha with e | ⟨hf, e, hn⟩
    · exact .inl e
    · exact .inr ⟨hf, by rw [e, hn]; rfl⟩

/-! ### Why the second sentence rests on TIME-010 -/

/-- TIME-011 alone does not fix the stamp of a transition that stays armed: the backdating
relation of TIME-010 (`time010_backdateRel`, which `TIME_010_forbids_backdate` rejects)
satisfies it (a backdating delay keeps the marking and which stamps are held, so both lines are
vacuous on it) but not TIME-010, whose line 2 keeps a stamp across a delay. In AC1,
one backdating millisecond after the re-arming at `T = 7000`, `u` would hold the stamp `0` and
could fire at `T = 7001`. This is why "measured from the moment it was armed again" over the
later steps is cited (`time011_elapsed_from_rearm`, `time011_no_early_fire`) and not stated. -/
theorem time011_backdate_gap :
    TIME_011 time010_backdateRel ∧ ¬ TIME_010 time010_backdateRel := by
  refine ⟨fun X => ?_, fun h => ?_⟩
  · have href := TIME_011_reference (N := Nat) X
    refine ⟨fun l u hu s s' h ha hne => ?_, fun l u hu s s' h hna ha => ?_⟩
    · rcases h with h | ⟨δ, -, rfl⟩
      · exact href.1 l u hu s s' h ha hne
      · exact absurd ha.1 hne
    · rcases h with h | ⟨δ, -, rfl⟩
      · exact href.2 l u hu s s' h hna ha
      · exact absurd ⟨ha.1, by simpa [time010_backdate] using ha.2⟩ hna
  · have := (h time011_X).2.1 (.delay 1) time011_u (time011_a4 refPolicy)
      (time010_backdate (time011_a4 refPolicy) 1) (.inr ⟨1, rfl, rfl⟩) (by decide) (by decide)
    rcases this with e | ⟨⟨t, d, e⟩, -⟩
    · exact absurd e (by decide)
    · cases e

/-! ### Both lines exercised (AC1) -/

/-- The state of AC1 after a delay of `δ` from the re-arming at `T = 7000`. -/
def time011_later (δ : Nat) : TSt Nat :=
  { time011_a4 refPolicy with now := 7000 + δ }

/-- Both lines of TIME-011 are exercised by the reference step, on AC1 in milliseconds. `u`
(`Delayed(5000)`) is armed at `T = 0` with the stamp `0`. At `T = 3000` the consumer takes its
token: `u` was armed and is no longer enabled, and holds no stamp (line 1). At `T = 7000` the
source refills the place: `u` was not armed and is armed again with the stamp `7000` (line 2).
It cannot fire at `T = 11999` (elapsed 4999) and can at `T = 12000`: the full delay applies
again. -/
@[evidence nonvacuous TIME_011]
theorem TIME_011_nonvacuous :
    Armed time011_a0 time011_u ∧ time011_a0.stamp "u" = some 0 ∧
      RefTStep time011_X time011_a0 (.delay 3000) time011_a1 ∧
      RefTStep time011_X time011_a1 (.fire time011_c []) (time011_a2 refPolicy) ∧
      Armed time011_a1 time011_u ∧ ¬ Enabled time011_u (time011_a2 refPolicy).m ∧
      (time011_a2 refPolicy).stamp "u" = none ∧
      RefTStep time011_X (time011_a2 refPolicy) (.delay 4000) (time011_a3 refPolicy) ∧
      RefTStep time011_X (time011_a3 refPolicy) (.fire time011_src [0]) (time011_a4 refPolicy) ∧
      ¬ Armed (time011_a3 refPolicy) time011_u ∧ Armed (time011_a4 refPolicy) time011_u ∧
      (time011_a4 refPolicy).stamp "u" = some 7000 ∧
      RefTStep time011_X (time011_a4 refPolicy) (.delay 4999) (time011_later 4999) ∧
      (∀ d s', ¬ RefTStep time011_X (time011_later 4999) (.fire time011_u d) s') ∧
      RefTStep time011_X (time011_a4 refPolicy) (.delay 5000) (time011_later 5000) ∧
      (∃ s', RefTStep time011_X (time011_later 5000) (.fire time011_u []) s') := by
  refine ⟨by decide, by decide, RefTStepW.delay _ _ 3000, time011_c_fires rfl rfl, by decide,
    by decide, by decide, RefTStepW.delay _ _ 4000, time011_src_fires rfl rfl (by decide),
    by decide, by decide, by decide, RefTStepW.delay _ _ 4999, fun d s' h => ?_,
    RefTStepW.delay _ _ 5000,
    ⟨_, RefTStepW.fire _ _ _ _ _ (by simp [time011_X]) ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
      (by decide) (by decide) (by decide)⟩⟩
  have := time010_gate rfl h
  revert this
  decide

end Libpetri.Spec
