import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryTime

set_option linter.missingDocs true

/-!
# TIME-010: Clock starts on enablement (`spec/03-timing.md`)

The requirement is a predicate over an abstract timed step relation `R : TRel N` (glossary
`GlossaryTime.lean`). The evidence theorems check it against the timed reference step
(`RefTStep`), against a relation that fires without looking at the clock, and against the
mutant reading that measures every clock from the start of the run.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Novel.TimedScg (Timing)

/-! ## TIME-010: Clock starts on enablement -/

requirement TIME_010
  id "TIME-010"
  title "Clock Starts on Enablement"
  kind T
  scope "all executors"
  source verbatim "spec/03-timing.md"
  quote "A transition is newly armed when it is enabled in the initial marking, afterwards when it is enabled after a firing or an injected token writes one of its arc places while it is not armed, and when its clock restarts in a firing ([TIME-012])."
        "*While* a transition is armed, its elapsed time *shall* be the current reading of the firing clock minus its stamp."
        "*While* a transition is armed and its elapsed time is less than its earliest bound, the transition *shall not* fire."
        "*While* a transition is not armed, the transition *shall not* fire."
  reading "For every timed net X:"
          "a transition of the net that is not armed before a step and is armed after it was armed by a firing that writes one of its arc places, and holds the reading of the firing clock after the step;"
          "a transition that is armed before and after a step holds the stamp it held before, or the step is a firing and the transition holds the reading of the firing clock after it;"
          "a firing that writes an arc place of the net's transition u, from a state in which u is not armed, leaves u armed if u is enabled after it;"
          "no transition fires from a state in which it is armed and its elapsed time is below its earliest bound;"
          "no transition fires from a state in which it is not armed."
  assumes "A step relates two states of the executor (glossary: TSt), each holding a marking, the reading of the firing clock and a stamp per transition name; a step is a delay of the clock, a firing or a reap (TRel). Firings are atomic: the step that starts a firing completes it. Armed, Elapsed time, Arc place and Write are the glossary terms (GlossaryTime.lean)."
          "Line 1 of the formula is the first 'shall' sentence at the grain of the Phase 1 step, together with the quoted sentence on being newly armed. A transition that is not armed before a step and is armed after it is newly armed, so the step is a firing that writes one of its arc places, and the new stamp is the reading of the firing clock after the step (which a firing does not advance). Nothing else newly arms a transition in the step relation: a delay or a reap arms nothing."
          "The first 'shall' sentence, 'When a transition is newly armed, the executor shall stamp it with the firing-clock reading taken by the enablement update that newly arms it ([EXEC-001] step 3).', is encoded only at the grain of the atomic Phase 1 step, so it is not quoted. The step relation has no cycles: the enablement update is part of the firing step that makes the transition enabled, and its reading is the reading of that step, which lines 1 and 2 fix. The section's paragraph on the enablement update says more: a synchronous action's deposit is first seen by the enablement update of the next cycle, an asynchronous completion or an injected token by the update of the cycle that takes it in, so the stamp is neither the reading of the cycle in which the arming firing started nor the moment an action completed, and a clock restarted in a firing is stamped by the next enablement update that finds the transition enabled. In the atomic step these readings coincide; that they can differ, and that the stamp is the later one, needs the cycle relation of Phase 2 (RefExec, [EXEC-001] steps 1 to 3) and is deferred to it. No mutant is given for the wrong reading (the reading of the cycle that started the arming firing): the Phase 1 relation cannot tell it apart."
          "Line 2 reads 'newly armed' through 'most recently newly armed' of the section's first paragraph: a transition armed before and after a step keeps its stamp, unless the step is a firing that restarts its clock ([TIME-012], glossary: Armed), which stamps it with the current reading as well. When a firing keeps, drops or restarts a clock is TIME-011, TIME-012 and TIME-013, not this block; this block fixes which steps may set a stamp and the value a new stamp takes."
          "Line 3 is the converse of line 1 for firings: a firing that writes an arc place of a transition that is not armed, and leaves it enabled, arms it. Lines 1 and 3 together are the quoted sentence's second case, as an equivalence, for a transition that is not armed before the step. Its third case, a clock that restarts in a firing ([TIME-012]), is line 2's second case for a transition armed before the firing and enabled after it: the restart stamps it with the current reading. Which firings restart a clock, including a transition with no arc place the firing writes that stays enabled after its own firing, is [TIME-012] lines 1 and 3, not this block. Its first case is outside the step relation: the initial marking is the initial state (TSt.init stamps every transition enabled in it with the start reading). Injected tokens are not steps of the Phase 1 relation, which has no environment places."
          "The second 'shall' sentence (elapsed time is the clock reading minus the stamp) is the glossary definition Elapsed, which line 4 of the formula uses; no step relation can break it, so it is not a separate line."
          "Transitions are identified by name (ruling D10): a stamp is kept per name, and lines 1 and 3 speak of the transition the net holds under the name (InNet). The section assumes pairwise distinct names (NamesDistinct), under which InNet is membership in the net (inNet_iff_mem)."
          "AC1 (enabled at T=10, earliest 3 s, ready at T=13) is the nonvacuous example TIME_010_nonvacuous, in milliseconds as the timings are: armed at 10, not fireable at 12, fireable at 13. The same example re-arms a reaped transition when a firing writes its input place and leaves it unarmed after a firing that writes none of its arc places (ruling D6)."
          "AC2 (disabled at T=11, re-enabled at T=15, ready at T=18) is the restart of TIME-011, which drops the stamp when the transition is disabled; this block fixes that the stamp taken at 15 is 15 (line 1), not one held from before (TIME_010_mutant_resume_killed), and that the transition does not fire before 18 (line 4)."
  signoff "pending"
  statement : ∀ {N : Type} [DecidableEq N], TRel N → Prop :=
    fun R => ∀ X : TimedNet _,
      (∀ l u, InNet X u → on (fun s s' => R X s l s'), shall (fun s s' => ¬ Armed s u →
          Armed s' u → ∃ t d, l = .fire t d ∧ (∃ p, ArcPlace u p ∧ Writes t d p) ∧
            s'.stamp u.core.name = some (ClockReading s'))) ∧
      (∀ l u, on (fun s s' => R X s l s'), shall (fun s s' => Armed s u → Armed s' u →
          s'.stamp u.core.name = s.stamp u.core.name ∨
            (∃ t d, l = .fire t d) ∧ s'.stamp u.core.name = some (ClockReading s'))) ∧
      (∀ t d u, InNet X u → on (fun s s' => R X s (.fire t d) s'), shall (fun s s' =>
          ¬ Armed s u → (∃ p, ArcPlace u p ∧ Writes t d p) → Enabled u s'.m → Armed s' u)) ∧
      (∀ u, while (fun s => Armed s u ∧ Elapsed s u < (TimingOf X u).earliest),
          never (fun s s' => ∃ d, R X s (.fire u d) s')) ∧
      (∀ u, while (fun s => ¬ Armed s u), never (fun s s' => ∃ d, R X s (.fire u d) s'))

/- The pinned readable form of TIME-010: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.TIME_010 : {N : Type} → [DecidableEq N] → TRel N → Prop :=
fun {N} [DecidableEq N] R =>
  ∀ (X : TimedNet N),
    (∀ (l : TLbl N) (u : Reference.Trans N),
        InNet X u →
          on fun s s' => R X s l s', shall fun s s' =>
            ¬Armed s u →
              Armed s' u →
                ∃ t d,
                  l = TLbl.fire t d ∧
                    (∃ p, ArcPlace u p ∧ Writes t d p) ∧ s'.stamp u.core.name = some (ClockReading s')) ∧
      (∀ (l : TLbl N) (u : Reference.Trans N),
          on fun s s' => R X s l s', shall fun s s' =>
            Armed s u →
              Armed s' u →
                s'.stamp u.core.name = s.stamp u.core.name ∨
                  (∃ t d, l = TLbl.fire t d) ∧ s'.stamp u.core.name = some (ClockReading s')) ∧
        (∀ (t : Reference.Trans N) (d : List N) (u : Reference.Trans N),
            InNet X u →
              on fun s s' => R X s (TLbl.fire t d) s', shall fun s s' =>
                ¬Armed s u → (∃ p, ArcPlace u p ∧ Writes t d p) → Enabled u s'.m → Armed s' u) ∧
          (∀ (u : Reference.Trans N),
              while fun s => Armed s u ∧ Elapsed s u < (TimingOf X u).earliest, never fun s s' =>
                ∃ d, R X s (TLbl.fire u d) s') ∧
            ∀ (u : Reference.Trans N), while fun s => ¬Armed s u, never fun s s' => ∃ d, R X s (TLbl.fire u d) s'
-/
#guard_msgs in #print TIME_010

/-! ### The five lines, for any policy -/

section Lines

variable {N : Type} [DecidableEq N]

/-- The spec's `keep` asks for an armed transition. -/
theorem refPolicy_keep_armed (X : TimedNet N) (s : TSt N) (t : Trans N) (d : List N)
    (m' : N → Nat) (u : Trans N) (h : (refPolicy (N := N)).keep X s t d m' u = true) :
    s.armed u = true := by
  simp only [refPolicy, Bool.and_eq_true] at h
  exact h.1.1.1

/-- The spec's `keep` keeps a stamp only where there is one. -/
theorem refPolicy_keep_stamp (X : TimedNet N) (s : TSt N) (t : Trans N) (d : List N)
    (m' : N → Nat) (u : Trans N) (h : (refPolicy (N := N)).keep X s t d m' u = true) :
    (s.stamp u.core.name).isSome = true := by
  have := refPolicy_keep_armed X s t d m' u h
  simp only [TSt.armed, Bool.and_eq_true] at this
  exact this.2

/-- The spec's `rearm` arms an unarmed transition whose arc place the firing writes, if it is
enabled after the firing. -/
theorem refPolicy_rearm_writes (X : TimedNet N) (s : TSt N) (t : Trans N) (d : List N)
    (m' : N → Nat) (u : Trans N) (_ : s.armed u = false) (hw : writesArc t d u = true)
    (hen : enabledNA m' u.core = true) : (refPolicy (N := N)).rearm X s t d m' u = true := by
  simp [refPolicy, hw, hen]

/-- A delay or a reap, under any policy, arms nothing: a transition armed after it was armed
before it. -/
theorem time010_nonfire_armed {P : Policy N} {X : TimedNet N} {s s' : TSt N} {l : TLbl N}
    (h : RefTStepW P X s l s') (hl : ∀ t d, l ≠ .fire t d) (u : Trans N) (ha : Armed s' u) :
    Armed s u := by
  have hsome := ha.2
  match h with
  | .delay _ _ _ => exact ha
  | .reap _ _ t _ _ =>
    by_cases hn : u.core.name = t.core.name
    · simp [hn] at hsome
    · exact ⟨ha.1, by simpa [hn] using hsome⟩
  | .fire _ _ t d _ _ _ _ _ _ => exact absurd rfl (hl t d)

/-- Stamps for any policy: a step keeps a stamp, or it is a firing that sets it to the
policy's fresh reading and leaves the clock reading as it is. -/
theorem time010_stamp_cases {P : Policy N} {X : TimedNet N} {s s' : TSt N} {l : TLbl N}
    (h : RefTStepW P X s l s') (u : Trans N) (ha : Armed s' u) :
    s'.stamp u.core.name = s.stamp u.core.name ∨
      (∃ t d, l = .fire t d) ∧ s'.stamp u.core.name = some (P.fresh s) ∧
        ClockReading s' = ClockReading s := by
  have hsome := ha.2
  match h with
  | .delay _ _ _ => exact .inl rfl
  | .reap _ _ t _ _ =>
    by_cases hn : u.core.name = t.core.name
    · simp [hn] at hsome
    · simp [hn]
  | .fire _ _ t d m' _ _ _ _ _ =>
    rcases restampAll_cases P X s t d m' u.core.name with e | e | e
    · exact .inl e
    · exact .inr ⟨⟨t, d, rfl⟩, e, rfl⟩
    · simp [e] at hsome

/-- Line 1 for any policy whose `keep` asks for an armed transition: only a firing arms a
transition of the net that was not armed, through `rearm`, with the fresh reading. -/
theorem time010_newly {P : Policy N}
    (hk : ∀ X s t d m' u, P.keep X s t d m' u = true → s.armed u = true)
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
    have hs : s'.stamp u.core.name = restampW P X s t d s'.m u := by
      rw [he]; exact restampAll_inNet hu s t d s'.m
    have hsome := ha.2
    rw [hs] at hsome
    unfold restampW at hs hsome
    have h1 : ¬ P.keep X s t d s'.m u = true := fun h1 => by
      simp [hk _ _ _ _ _ _ h1] at hna'
    rw [if_neg h1] at hs hsome
    by_cases h2 : P.rearm X s t d s'.m u = true
    · rw [if_pos h2] at hs
      exact ⟨t, d, rfl, h2, hs, by rw [he]⟩
    · rw [if_neg h2] at hsome
      simp at hsome

/-- Line 3 for any policy whose `keep` keeps only a stamp there is and whose `rearm` arms an
unarmed transition whose arc place the firing writes. -/
theorem time010_arms {P : Policy N}
    (hk : ∀ X s t d m' u, P.keep X s t d m' u = true → (s.stamp u.core.name).isSome = true)
    (hr : ∀ X s t d m' u, s.armed u = false → writesArc t d u = true →
      enabledNA m' u.core = true → P.rearm X s t d m' u = true)
    {X : TimedNet N} {t : Trans N} {d : List N} {u : Trans N} (hu : InNet X u) {s s' : TSt N}
    (h : RefTStepW P X s (.fire t d) s') (hna : ¬ Armed s u)
    (hw : ∃ p, ArcPlace u p ∧ Writes t d p) (hen : Enabled u s'.m) : Armed s' u := by
  obtain ⟨-, -, -, -, -, he⟩ := refTStepW_fire_inv h
  rw [he]
  refine ⟨hen, ?_⟩
  have hna' : s.armed u = false := by simpa [armed_iff] using hna
  have hw' : writesArc t d u = true := (writesArc_iff t d u).2 hw
  have hen' : enabledNA s'.m u.core = true := hen
  show (restampAll P X s t d s'.m u.core.name).isSome = true
  rw [restampAll_inNet hu]
  unfold restampW
  by_cases h1 : P.keep X s t d s'.m u = true
  · rw [if_pos h1]; exact hk _ _ _ _ _ _ h1
  · rw [if_neg h1, if_pos (hr _ _ _ _ _ _ hna' hw' hen')]; rfl

/-- Line 4 for any policy with the spec's gate. -/
@[evidence cites "TIME-014" "second shall sentence, first clause only ('While a Delayed transition is armed and its elapsed time is less than its earliest bound, it shall not fire'): under any policy with the spec's gate, a firing transition has elapsed time at least its earliest bound; the clause on a competing ready transition taking the tokens first whatever their priorities is not covered"]
theorem time010_gate {P : Policy N} (hg : P.gate = refPolicy.gate) {X : TimedNet N}
    {u : Trans N} {d : List N} {s s' : TSt N} (h : RefTStepW P X s (.fire u d) s') :
    (TimingOf X u).earliest ≤ Elapsed s u := by
  obtain ⟨-, -, -, hgate, -⟩ := refTStepW_fire_inv h
  rw [hg] at hgate
  simpa [refPolicy, elapsed_eq] using hgate

/-- Line 5 for any policy: a firing transition is armed. -/
theorem time010_armed {P : Policy N} {X : TimedNet N} {u : Trans N} {d : List N}
    {s s' : TSt N} (h : RefTStepW P X s (.fire u d) s') : Armed s u :=
  (armed_iff s u).2 (refTStepW_fire_inv h).2.2.1

end Lines

/-- The timed reference step satisfies TIME-010: a delay and a reap arm nothing and keep every
stamp they do not drop; a firing newly arms a transition only through `refPolicy.rearm`, which
for a transition that was not armed asks for a written arc place, and stamps it with the current
reading (`refPolicy.fresh`, line 1); a firing keeps a stamp or restarts it at the current reading
(line 2); a firing that writes an arc place of an unarmed transition and leaves it enabled
re-arms it (line 3); and a firing needs its transition armed and past `refPolicy`'s
earliest-bound gate (lines 4 and 5). -/
@[evidence holds TIME_010]
theorem TIME_010_reference {N : Type} [DecidableEq N] : TIME_010 (RefTStep (N := N)) := by
  intro X
  refine ⟨fun l u hu s s' h hna ha => ?_, fun l u s s' h _ ha => ?_,
    fun t d u hu s s' h => time010_arms refPolicy_keep_stamp refPolicy_rearm_writes hu h,
    fun u s s' ⟨d, h⟩ ⟨_, hlt⟩ => ?_, fun u s s' ⟨d, h⟩ hna => hna (time010_armed h)⟩
  · obtain ⟨t, d, rfl, hr, e, hn⟩ := time010_newly refPolicy_keep_armed hu h hna ha
    have hna' : s.armed u = false := by simpa [armed_iff] using hna
    simp only [refPolicy, hna', Bool.false_or, Bool.and_eq_true] at hr
    exact ⟨t, d, rfl, (writesArc_iff t d u).1 hr.2, by rw [e, hn]; rfl⟩
  · rcases time010_stamp_cases h u ha with e | ⟨hf, e, hn⟩
    · exact .inl e
    · exact .inr ⟨hf, by rw [e, hn]; rfl⟩
  · exact absurd (time010_gate rfl h) (by omega)

/-! ### Examples (AC1, AC2 and a reaped transition) -/

/-- The source of the examples: no arcs but one output on place `0`. -/
def time010_src : Trans Nat :=
  { core := { name := "src", inputs := [], inhibitors := [], reads := [], resets := [] },
    out := some (.place 0) }

/-- The transition of AC1: one input arc on place `0`, no output spec. -/
def time010_u : Trans Nat :=
  { core := { name := "u", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- A transition with no arcs and no output spec: its firing writes no place. -/
def time010_w : Trans Nat :=
  { core := { name := "w", inputs := [], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- The timing of the examples: `u` is `Delayed(3)`, every other transition `Immediate`. -/
def time010_timing (t : Trans Nat) : Timing :=
  if t.core.name = "u" then .delayed 3 else .immediate

/-- The timed net of AC1 and AC2: the source and `u`, tolerance 0. -/
def time010_X : TimedNet Nat :=
  { net := { places := [0], transitions := [time010_src, time010_u] },
    timing := time010_timing, tol := 0 }

/-- The timed net of the reaped example: `time010_X` with `time010_w` added. -/
def time010_Y : TimedNet Nat :=
  { net := { places := [0], transitions := [time010_src, time010_u, time010_w] },
    timing := time010_timing, tol := 0 }

theorem time010_u_inX : InNet time010_X time010_u := rfl

theorem time010_u_inY : InNet time010_Y time010_u := rfl

/-- The state at `T = 10`: nothing marked, the source armed since `0`, `u` (disabled) without a
clock. -/
def time010_s0 : TSt Nat :=
  { m := fun _ => 0, now := 10, stamp := fun n => if n = "src" then some 0 else none }

/-- The marking after the source fires once from the empty marking: one token in place `0`. -/
def time010_m1 : Nat → Nat := fireNC time010_s0.m time010_src.core (depProd [0])

/-- The state after the source fires at `T = 10` under policy `P`. -/
def time010_after (P : Policy Nat) : TSt Nat :=
  { m := time010_m1, now := 10, stamp := restampAll P time010_X time010_s0 time010_src [0] time010_m1 }

/-- The source fires from `time010_s0` under every policy whose gate and expiry are the spec's:
it is armed, `Immediate` and not reapable. -/
theorem time010_src_fires {P : Policy Nat} (hg : P.gate = refPolicy.gate)
    (hx : P.expired = refPolicy.expired) :
    RefTStepW P time010_X time010_s0 (.fire time010_src [0]) (time010_after P) := by
  refine RefTStepW.fire _ _ _ _ _ (by simp [time010_X]) ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
    (by decide) ?_ ?_
  · rw [hg]; decide
  · rw [hx]; decide

/-- A relation that fires every reference firing and ignores the clock: the stamps and the
reading stay as they are, and nothing else is a step. -/
def time010_untimed : TRel Nat := fun _ s l s' =>
  match l with
  | .fire t d => RefFire t s.m d s'.m ∧ s'.now = s.now ∧ s'.stamp = s.stamp
  | _ => False

/-- ✗ Firing without a clock violates TIME-010 (line 5): from a state in which no transition
holds a stamp, the untimed relation fires the source, which is not armed. -/
@[evidence forbids TIME_010]
theorem TIME_010_forbids_untimed : ¬ TIME_010 time010_untimed := by
  intro h
  let s : TSt Nat := { time010_s0 with stamp := fun _ => none }
  have hfire : time010_untimed time010_X s (.fire time010_src [0])
      { m := time010_m1, now := 10, stamp := fun _ => none } :=
    ⟨⟨by decide, ⟨.action 0, rfl⟩, rfl⟩, rfl, rfl⟩
  exact (h time010_X).2.2.2.2 time010_src s _ ⟨_, hfire⟩ (by decide)

/-! ### Mutant: every clock from the start of the run -/

/-- The policy that stamps every newly armed transition with `0`, the start of the run, and
decides everything else as the spec does. -/
def time010_fromStartPolicy : Policy Nat := { refPolicy with fresh := fun _ => 0 }

/-- Mutant reading of TIME-010 that measures every clock from the start of the run: a new stamp
is `0`, the reading at which the run started, instead of the current reading (lines 1 and 2).
The other lines are as in TIME-010. -/
def TIME_010_mutant_fromStart {N : Type} [DecidableEq N] (R : TRel N) : Prop :=
  ∀ X : TimedNet N,
    (∀ l u, InNet X u → on (fun s s' => R X s l s'), shall (fun s s' => ¬ Armed s u →
        Armed s' u → ∃ t d, l = .fire t d ∧ (∃ p, ArcPlace u p ∧ Writes t d p) ∧
          s'.stamp u.core.name = some 0)) ∧
    (∀ l u, on (fun s s' => R X s l s'), shall (fun s s' => Armed s u → Armed s' u →
        s'.stamp u.core.name = s.stamp u.core.name ∨
          (∃ t d, l = .fire t d) ∧ s'.stamp u.core.name = some 0)) ∧
    (∀ t d u, InNet X u → on (fun s s' => R X s (.fire t d) s'), shall (fun s s' =>
        ¬ Armed s u → (∃ p, ArcPlace u p ∧ Writes t d p) → Enabled u s'.m → Armed s' u)) ∧
    (∀ u, while (fun s => Armed s u ∧ Elapsed s u < (TimingOf X u).earliest),
        never (fun s s' => ∃ d, R X s (.fire u d) s')) ∧
    (∀ u, while (fun s => ¬ Armed s u), never (fun s s' => ∃ d, R X s (.fire u d) s'))

/-- The step that stamps from the start kills the mutant: it satisfies the mutant reading, but
not TIME-010, since `u`, newly armed at `T = 10` when the source fills its input place, gets the
stamp `0` instead of `10`. -/
@[evidence mutant TIME_010]
theorem TIME_010_mutant_fromStart_killed :
    TIME_010_mutant_fromStart (RefTStepW time010_fromStartPolicy) ∧
      ¬ TIME_010 (RefTStepW time010_fromStartPolicy) := by
  refine ⟨fun X => ⟨fun l u hu s s' h hna ha => ?_, fun l u s s' h _ ha => ?_,
      fun t d u hu s s' h => time010_arms (P := time010_fromStartPolicy) refPolicy_keep_stamp
        refPolicy_rearm_writes hu h,
      fun u s s' ⟨d, h⟩ ⟨_, hlt⟩ =>
        absurd (time010_gate (P := time010_fromStartPolicy) rfl h) (by omega),
      fun u s s' ⟨d, h⟩ hna => hna (time010_armed h)⟩, fun h => ?_⟩
  · obtain ⟨t, d, rfl, hr, e, -⟩ :=
      time010_newly (P := time010_fromStartPolicy) refPolicy_keep_armed hu h hna ha
    have hna' : s.armed u = false := by simpa [armed_iff] using hna
    simp only [time010_fromStartPolicy, refPolicy, hna', Bool.false_or, Bool.and_eq_true] at hr
    exact ⟨t, d, rfl, (writesArc_iff t d u).1 hr.2, e⟩
  · rcases time010_stamp_cases h u ha with e | ⟨hf, e, -⟩
    · exact .inl e
    · exact .inr ⟨hf, e⟩
  · have hstep := time010_src_fires (P := time010_fromStartPolicy) rfl rfl
    obtain ⟨_, _, -, -, e⟩ := (h time010_X).1 _ time010_u time010_u_inX _ _ hstep
      (by decide) (by decide)
    exact absurd e (by decide)

/-! ### Mutant: a clock resumes after a disablement (TIME-011, AC2) -/

/-- The policy that keeps every stamp a transition other than the fired one still holds, armed
or not, so a transition armed again resumes the clock it held before it was disabled. -/
def time010_resumePolicy : Policy Nat :=
  { refPolicy with keep := fun X s t d m' u =>
      (s.stamp u.core.name).isSome && u.core.name != t.core.name || refPolicy.keep X s t d m' u }

/-- Mutant reading of TIME-010 in which a transition armed again may resume the stamp it held:
line 1 asks only that a transition is newly armed by a firing and that its stamp is the one it
held or the current reading. The other lines are as in TIME-010. -/
def TIME_010_mutant_resume {N : Type} [DecidableEq N] (R : TRel N) : Prop :=
  ∀ X : TimedNet N,
    (∀ l u, InNet X u → on (fun s s' => R X s l s'), shall (fun s s' => ¬ Armed s u →
        Armed s' u → (∃ t d, l = .fire t d) ∧
          (s'.stamp u.core.name = s.stamp u.core.name ∨
            s'.stamp u.core.name = some (ClockReading s')))) ∧
    (∀ l u, on (fun s s' => R X s l s'), shall (fun s s' => Armed s u → Armed s' u →
        s'.stamp u.core.name = s.stamp u.core.name ∨
          (∃ t d, l = .fire t d) ∧ s'.stamp u.core.name = some (ClockReading s'))) ∧
    (∀ t d u, InNet X u → on (fun s s' => R X s (.fire t d) s'), shall (fun s s' =>
        ¬ Armed s u → (∃ p, ArcPlace u p ∧ Writes t d p) → Enabled u s'.m → Armed s' u)) ∧
    (∀ u, while (fun s => Armed s u ∧ Elapsed s u < (TimingOf X u).earliest),
        never (fun s s' => ∃ d, R X s (.fire u d) s')) ∧
    (∀ u, while (fun s => ¬ Armed s u), never (fun s s' => ∃ d, R X s (.fire u d) s'))

/-- AC2's state at `T = 15`: `u` was armed at `10` and disabled at `11`, and still holds the
stamp `10`; nothing is marked, the source is armed since `0`. -/
def time010_s15 : TSt Nat :=
  { m := fun _ => 0, now := 15,
    stamp := fun n => if n = "src" then some 0 else if n = "u" then some 10 else none }

/-- The resuming step kills the mutant: it satisfies the mutant reading, but not TIME-010. In
AC2's state at `T = 15` the source fills `u`'s input place and `u` is armed again with its old
stamp `10`, so it would be ready at `13` instead of `18`. -/
@[evidence mutant TIME_010]
theorem TIME_010_mutant_resume_killed :
    TIME_010_mutant_resume (RefTStepW time010_resumePolicy) ∧
      ¬ TIME_010 (RefTStepW time010_resumePolicy) := by
  have hk : ∀ X s t d m' u, time010_resumePolicy.keep X s t d m' u = true →
      (s.stamp u.core.name).isSome = true := fun X s t d m' u h => by
    simp only [time010_resumePolicy, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨h, -⟩ | h
    · exact h
    · exact refPolicy_keep_stamp X s t d m' u h
  refine ⟨fun X => ⟨fun l u hu s s' h hna ha => ?_, fun l u s s' h _ ha => ?_,
      fun t d u hu s s' h => time010_arms (P := time010_resumePolicy) hk
        refPolicy_rearm_writes hu h,
      fun u s s' ⟨d, h⟩ ⟨_, hlt⟩ =>
        absurd (time010_gate (P := time010_resumePolicy) rfl h) (by omega),
      fun u s s' ⟨d, h⟩ hna => hna (time010_armed h)⟩, fun h => ?_⟩
  · have hf : ∃ t d, l = .fire t d := by
      cases l with
      | fire t d => exact ⟨t, d, rfl⟩
      | delay δ => exact absurd (time010_nonfire_armed h (fun _ _ e => by cases e) u ha) hna
      | reap t => exact absurd (time010_nonfire_armed h (fun _ _ e => by cases e) u ha) hna
    rcases time010_stamp_cases h u ha with e | ⟨-, e, hn⟩
    · exact ⟨hf, .inl e⟩
    · exact ⟨hf, .inr (by rw [e, hn]; rfl)⟩
  · rcases time010_stamp_cases h u ha with e | ⟨hf, e, hn⟩
    · exact .inl e
    · exact .inr ⟨hf, by rw [e, hn]; rfl⟩
  · have hstep : RefTStepW time010_resumePolicy time010_X time010_s15 (.fire time010_src [0])
        { m := fireNC time010_s15.m time010_src.core (depProd [0]), now := 15,
          stamp := restampAll time010_resumePolicy time010_X time010_s15 time010_src [0]
            (fireNC time010_s15.m time010_src.core (depProd [0])) } :=
      RefTStepW.fire _ _ _ _ _ (by simp [time010_X]) ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
        (by decide) (by decide) (by decide)
    obtain ⟨_, _, -, -, e⟩ := (h time010_X).1 _ time010_u time010_u_inX _ _ hstep
      (by decide) (by decide)
    exact absurd e (by decide)

/-! ### Mutant: a firing re-arms a reaped transition whatever it writes -/

/-- The policy that arms every enabled transition that does not keep its stamp, whether or not
the firing wrote one of its arc places. -/
def time010_rearmAnyPolicy : Policy Nat :=
  { refPolicy with rearm := fun _ _ _ _ m' u => enabledNA m' u.core }

/-- Mutant reading of TIME-010 in which any firing newly arms a transition enabled after it:
line 1 does not ask for a written arc place. The other lines are as in TIME-010. -/
def TIME_010_mutant_rearmAny {N : Type} [DecidableEq N] (R : TRel N) : Prop :=
  ∀ X : TimedNet N,
    (∀ l u, InNet X u → on (fun s s' => R X s l s'), shall (fun s s' => ¬ Armed s u →
        Armed s' u → ∃ t d, l = .fire t d ∧ s'.stamp u.core.name = some (ClockReading s'))) ∧
    (∀ l u, on (fun s s' => R X s l s'), shall (fun s s' => Armed s u → Armed s' u →
        s'.stamp u.core.name = s.stamp u.core.name ∨
          (∃ t d, l = .fire t d) ∧ s'.stamp u.core.name = some (ClockReading s'))) ∧
    (∀ t d u, InNet X u → on (fun s s' => R X s (.fire t d) s'), shall (fun s s' =>
        ¬ Armed s u → (∃ p, ArcPlace u p ∧ Writes t d p) → Enabled u s'.m → Armed s' u)) ∧
    (∀ u, while (fun s => Armed s u ∧ Elapsed s u < (TimingOf X u).earliest),
        never (fun s s' => ∃ d, R X s (.fire u d) s')) ∧
    (∀ u, while (fun s => ¬ Armed s u), never (fun s s' => ∃ d, R X s (.fire u d) s'))

/-- A reaped state at `T = 20`, as a reap leaves it: `u` is enabled (one token in place `0`)
but holds no clock; the source and `w` are armed since `0`. -/
def time010_r0 : TSt Nat :=
  { m := fun p => if p = 0 then 1 else 0, now := 20,
    stamp := fun n => if n = "u" then none else some 0 }

/-- The state after a firing of `t` with deposit `d` from the reaped state, in `time010_Y`,
under policy `P`. -/
def time010_rAfter (P : Policy Nat) (t : Trans Nat) (d : List Nat) : TSt Nat :=
  { m := fireNC time010_r0.m t.core (depProd d), now := 20,
    stamp := restampAll P time010_Y time010_r0 t d (fireNC time010_r0.m t.core (depProd d)) }

/-- `w` fires from the reaped state under every policy whose gate and expiry are the spec's. -/
theorem time010_w_fires {P : Policy Nat} (hg : P.gate = refPolicy.gate)
    (hx : P.expired = refPolicy.expired) :
    RefTStepW P time010_Y time010_r0 (.fire time010_w []) (time010_rAfter P time010_w []) := by
  refine RefTStepW.fire _ _ _ _ _ (by simp [time010_Y]) ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
    (by decide) ?_ ?_
  · rw [hg]; decide
  · rw [hx]; decide

/-- The step that re-arms on any firing kills the mutant: it satisfies the mutant reading, but
not TIME-010. From the reaped state, `w` fires and writes no place, and `u` is armed again. -/
@[evidence mutant TIME_010]
theorem TIME_010_mutant_rearmAny_killed :
    TIME_010_mutant_rearmAny (RefTStepW time010_rearmAnyPolicy) ∧
      ¬ TIME_010 (RefTStepW time010_rearmAnyPolicy) := by
  refine ⟨fun X => ⟨fun l u hu s s' h hna ha => ?_, fun l u s s' h _ ha => ?_,
      fun t d u hu s s' h => time010_arms (P := time010_rearmAnyPolicy) refPolicy_keep_stamp
        (fun _ _ _ _ _ _ _ _ hen => hen) hu h,
      fun u s s' ⟨d, h⟩ ⟨_, hlt⟩ =>
        absurd (time010_gate (P := time010_rearmAnyPolicy) rfl h) (by omega),
      fun u s s' ⟨d, h⟩ hna => hna (time010_armed h)⟩, fun h => ?_⟩
  · obtain ⟨t, d, rfl, -, e, hn⟩ :=
      time010_newly (P := time010_rearmAnyPolicy) refPolicy_keep_armed hu h hna ha
    exact ⟨t, d, rfl, by rw [e, hn]; rfl⟩
  · rcases time010_stamp_cases h u ha with e | ⟨hf, e, hn⟩
    · exact .inl e
    · exact .inr ⟨hf, by rw [e, hn]; rfl⟩
  · obtain ⟨t, d, e, ⟨p, -, hw⟩, -⟩ := (h time010_Y).1 _ time010_u time010_u_inY _ _
      (time010_w_fires (P := time010_rearmAnyPolicy) rfl rfl) (by decide) (by decide)
    cases e
    simp [Writes, inPlaces, ResetArc, Produced, time010_w] at hw

/-! ### Every line exercised -/

/-- The state of AC1 after a delay of `δ` from the firing at `T = 10`. -/
def time010_later (δ : Nat) : TSt Nat :=
  { time010_after refPolicy with now := 10 + δ }

/-- Every line of TIME-010 is exercised by the reference step. AC1: at `T = 10` the transition
`u` is not armed and cannot fire (line 5); the source fires and writes `u`'s input place, and
`u` is newly armed (lines 1 and 3) with the stamp `10`; two milliseconds later it cannot fire
(line 4, elapsed 2 below its earliest bound 3); three milliseconds later it can. A delay keeps
the stamp (line 2). A reaped `u` at `T = 20`: `w` fires and writes none of its arc places, and
`u` stays unarmed (line 1); the source fires and writes its input place, and `u` is armed again
with the stamp `20` (lines 1 and 3). -/
@[evidence nonvacuous TIME_010]
theorem TIME_010_nonvacuous :
    (∀ d s', ¬ RefTStep time010_X time010_s0 (.fire time010_u d) s') ∧
      RefTStep time010_X time010_s0 (.fire time010_src [0]) (time010_after refPolicy) ∧
      ¬ Armed time010_s0 time010_u ∧ Armed (time010_after refPolicy) time010_u ∧
      (time010_after refPolicy).stamp "u" = some 10 ∧
      RefTStep time010_X (time010_after refPolicy) (.delay 2) (time010_later 2) ∧
      (time010_later 2).stamp "u" = some 10 ∧
      (∀ d s', ¬ RefTStep time010_X (time010_later 2) (.fire time010_u d) s') ∧
      RefTStep time010_X (time010_after refPolicy) (.delay 3) (time010_later 3) ∧
      (∃ s', RefTStep time010_X (time010_later 3) (.fire time010_u []) s') ∧
      Reaped time010_r0 time010_u ∧
      RefTStep time010_Y time010_r0 (.fire time010_w []) (time010_rAfter refPolicy time010_w []) ∧
      ¬ Armed (time010_rAfter refPolicy time010_w []) time010_u ∧
      RefTStep time010_Y time010_r0 (.fire time010_src [0])
        (time010_rAfter refPolicy time010_src [0]) ∧
      Armed (time010_rAfter refPolicy time010_src [0]) time010_u ∧
      (time010_rAfter refPolicy time010_src [0]).stamp "u" = some 20 := by
  refine ⟨fun d s' h => ?_, time010_src_fires rfl rfl, by decide, by decide, by decide,
    RefTStepW.delay _ _ 2, by decide, fun d s' h => ?_, RefTStepW.delay _ _ 3,
    ⟨_, RefTStepW.fire _ _ _ _ _ (by simp [time010_X]) ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
      (by decide) (by decide) (by decide)⟩, by decide, time010_w_fires rfl rfl, by decide,
    RefTStepW.fire _ _ _ _ _ (by simp [time010_Y]) ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
      (by decide) (by decide) (by decide), by decide, by decide⟩
  · exact absurd (time010_armed h) (by decide)
  · have := time010_gate rfl h
    revert this
    decide

end Libpetri.Spec
