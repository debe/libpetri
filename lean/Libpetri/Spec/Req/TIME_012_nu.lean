import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryTime
import Libpetri.Reference.Nu

set_option linter.missingDocs true
set_option autoImplicit false

/-!
# TIME-012, the ν-join clause (`spec/03-timing.md`)

The second block of TIME-012, beside `TIME_012` in `TIME_012.lean`. TIME-012 reads enablement
in the intermediate marking of a firing; its first bullet says that removing tokens disables a
transition through, among others, ν-join bindings. A matched transition ([NU-020]) is armed
only while it is enabled and some name is eligible, so a firing that takes the last token of
every shared name out of a correlated input disables the join in the intermediate marking, even
when the input still holds tokens of other names, and a firing that leaves another shared name
keeps the join enabled.

The block is a predicate over an abstract timed ν step relation `R : NuTRel N V Nm`: states hold
a queue marking of stamped tokens ([NU-020] reads `createdAt`), the reading of the firing clock
and a stamp per transition name; a firing step names the fired ν transition, its chosen name
and its emission. The intermediate marking of a firing is `NuMid`: the correlated takes of the
chosen name for a matched transition (`nuConsume`), the queue consume (`qConsume`) otherwise.
Armed is the glossary's term read by names (`NuArmed`: ν-enabled and holding a stamp).

The reference (`RefNuTStep`) is the atomic timed step of `Reference/Timed.lean` with the ν
firing kernel `RefNuFire` in place of the count firing and every enablement test read by names.
The reference executor `RefExec` has no ν kernel yet, so this block is not on `RefExec`: the
Phase 1 shape of `TIME_012` (one firing per step, no pass, no actions in flight) is used, and the
link to the count reading is `time012nu_mid_count` (without a match the ν intermediate marking
counts as the glossary's `Mid`).

Wrong models: the step that keeps a join's clock when the join is enabled on the token counts in
the intermediate marking (`countKeep`), the step that leaves a stale stamp on a join that is
disabled after the firing (`staleKeep`), the step that restarts a join's clock whenever the
firing takes a token of the join's chosen name out of a correlated input (`tookBound`, the
literal first reading of the NU-050 sentence, clash nu-b#10), the step that lets a fired
join keep its clock (`selfKeep`), the step that gives every transition left without a stamp the
stamp `0` (`staleArm`), and the step that never arms a transition that held no stamp
(`noArm`). Two frames are kept out of the statement, as in `TIME_012`:
the clock frame (`time012nu_FramesClock`) and the frame that ties the label's chosen name to the
tokens the firing took (`time012nu_FramesMid`); the last section shows the steps each excludes.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Novel.TimedScg (Timing)

/-! ## Vocabulary -/

section Vocab

variable {N V Nm : Type}

/-- A timed ν net: its transitions, each possibly matched, and the timing of each transition
([TIME-001]). -/
structure NuTimedNet (N V Nm : Type) where
  /-- The transitions, with their match specifications. -/
  trans  : List (NuTrans N (KeyFn V Nm))
  /-- The timing of each transition. -/
  timing : Trans N → Timing

/-- A state of the timed ν executor: the queue marking of stamped tokens, the reading of the
firing clock and the stamp per transition name. -/
structure NuTSt (N V : Type) where
  /-- The marking, as queues of stamped tokens. -/
  M     : QMarking N (Stamped V)
  /-- The reading of the firing clock. -/
  now   : Nat
  /-- The stamp by transition name. -/
  stamp : String → Option Nat

/-- A step of the timed ν executor: the clock advances by `δ`, or `t` fires with chosen name
`c` (`none` without a match) and emission `e`. -/
inductive NuTLbl (N V Nm : Type) where
  /-- The firing clock advances by `δ`. -/
  | delay (δ : Nat)
  /-- `t` fires with chosen name `c` and emission `e`. -/
  | fire (t : NuTrans N (KeyFn V Nm)) (c : Option Nm) (e : List (N × Stamped V))

/-- A timed ν step relation: `R X s l s'`. -/
abbrev NuTRel (N V Nm : Type) :=
  NuTimedNet N V Nm → NuTSt N V → NuTLbl N V Nm → NuTSt N V → Prop

variable [DecidableEq N] [LinearOrder Nm]

/-- **The intermediate marking of a ν firing** ([TIME-012] read by names): the marking the
firing of `t` with chosen name `c` leaves before it deposits anything. A matched transition
takes the first tokens of its chosen name from each correlated input (`nuConsume`, which also
drains the reset places); a transition without a match takes the queue heads (`qConsume`). -/
def NuMid (t : NuTrans N (KeyFn V Nm)) (M : QMarking N (Stamped V)) (c : Option Nm) :
    QMarking N (Stamped V) :=
  match t.mspec, c with
  | some ms, some n => nuConsume ms t M n
  | _, _ => qConsume M t.base

/-- **Armed, read by names**: `u` is ν-enabled at the state's marking ([NU-020]: enabled on the
counts and, when matched, with some name eligible) and holds a stamp. -/
def NuArmed (s : NuTSt N V) (u : NuTrans N (KeyFn V Nm)) : Prop :=
  NuEnabled u s.M ∧ (s.stamp u.base.core.name).isSome = true

/-- `u` is the net's transition of its name. -/
def NuInNet (X : NuTimedNet N V Nm) (u : NuTrans N (KeyFn V Nm)) : Prop :=
  X.trans.find? (·.base.core.name == u.base.core.name) = some u

end Vocab

/-! ## The block -/

requirement TIME_012_nu
  id "TIME-012"
  title "Clock Restart on Intermediate Disablement (ν-join bindings)"
  kind T
  scope "every executor that runs matched transitions ([NU-020]), read on the atomic timed ν step"
  source verbatim "spec/03-timing.md"
  quote "*When* a transition fires, it *shall* lose its clock."
        "*When* a transition `t` fires and a transition that lost its clock in that firing is enabled after it, that transition *shall* be newly armed ([TIME-010])."
        "A matched transition ([NU-020]) is armed only while it is enabled and some name is eligible ([NU-022]), in the intermediate marking as in any other marking."
        "*When* a transition `t` fires, each armed matched transition other than `t` that is not enabled in the intermediate marking or has no eligible name there *shall* lose its clock, even when its correlated inputs still hold tokens."
        "*When* a transition `t` fires and a matched transition that lost its clock in that firing has no eligible name after it, that transition *shall not* be newly armed, even when it is enabled after the firing."
        "*When* a transition `t` fires, each armed matched transition other than `t` that is enabled with an eligible name both in the intermediate marking and after the firing *shall* keep its stamp, even when `t` took tokens of the name it would have joined on."
        "Removing tokens disables a transition only through input arcs, read arcs, cardinality requirements and ν-join bindings, never through inhibitor arcs."
        "The fired transition itself always starts a fresh clock when it is enabled again."
  reading "For every timed ν net X:"
          "a firing of t from a state in which the net's matched transition u, named differently from t, is armed (read by names) and is not ν-enabled in the intermediate marking of t (taken from the state's marking with t's chosen name) leaves u armed with the reading of the firing clock after the firing if u is ν-enabled after it, and leaves u without a stamp otherwise;"
          "a firing of t from a state in which the net's matched transition u, named differently from t, is armed (read by names) and is ν-enabled in the intermediate marking of t and after the firing leaves u's stamp as it was;"
          "a firing of t from a state in which the net's matched transition u named like t is armed (read by names) leaves u armed with the reading of the firing clock after the firing if u is ν-enabled after it, and leaves u without a stamp otherwise;"
          "every firing after which the net's matched transition u is not ν-enabled leaves u without a stamp;"
          "a firing of t that writes one of the arc places of the net's matched transition u, from a state in which u is not armed (read by names), leaves u armed with the reading of the firing clock after the firing if u is ν-enabled after it."
  assumes "A step relates two states of the ν executor (NuTSt), each holding a queue marking of stamped tokens, the reading of the firing clock and a stamp per transition name; a firing step names the fired transition, its chosen name and its emission (NuTRel). Firings are atomic: the step that starts a firing completes it, as in the TIME_012 block. ν-enabled is the glossary's NuEnabled ([NU-020]): enabled on the token counts ([CORE-022]) and, for a matched transition, some name eligible; the section's 'enabled and has an eligible name' and 'enabled with an eligible name' are NuEnabled, and its bare 'enabled' is the glossary's count-level term. Armed read by names is NuArmed. The intermediate marking is NuMid: the correlated takes of the chosen name and the drained reset places for a matched transition (nuConsume), the queue consume otherwise (qConsume); without a match it counts as the glossary's Mid (time012nu_mid_count)."
          "The statement reads the intermediate marking off the firing's label, so it takes the label's chosen name to be the name whose tokens the firing took, as the TIME_012 block takes its label to name the fired transition; for a matched transition the reference chooses that name by the [NU-022] selection (refNuFire_selectsBy). The tie is the frame time012nu_FramesMid (the marking after a firing is the intermediate marking of its label with the emission at the tails, [EXEC-020]), which the reference satisfies (TIME_012_nu_reference_framesMid); a step that takes the chosen name's tokens but labels its firing with no name satisfies the statement and breaks the frame (TIME_012_nu_gap_unnamedLabel). A firing is instantaneous on the firing clock: that frame is time012nu_FramesClock, which the reference satisfies (TIME_012_nu_reference_framesClock); a firing fused with a hidden delay satisfies the statement and breaks it (TIME_012_nu_gap_fireAdvancesClock). Neither frame is a sentence of this section, so neither is in the statement; they belong in the consistency theorem that takes this block, as time012_FramesClock is in ConsistencyTime."
          "The block speaks of matched transitions only. For a transition without a match ν-enabled is enabled on the counts (time012nu_enabled_unmatched), and the TIME_012 block states the rule for it, its own clock as the fired transition included."
          "To lose a clock is to hold no stamp after the firing, as in the TIME_012 block. Line 1 is the fourth quoted sentence together with the second and the fifth: a matched transition that lost its clock is newly armed, with the reading of the firing clock, when it is ν-enabled after the firing, and otherwise holds no stamp, even when it is enabled on its counts. Line 2 is the sixth quoted sentence. Line 3 is the first, second, fifth and last quoted sentences for a matched fired transition, read by names as TIME_012 line 3: the net's transition named like t. Lines 4 and 5 are the third quoted sentence, which also gives the reading of armed and enabled every line uses (NuArmed and NuEnabled). Line 4 is its 'armed only while it is enabled and some name is eligible' on the marking after a firing: a matched transition that is not ν-enabled there holds no stamp, whether or not it held one before, so a join cannot carry a clock it got on its counts before any name was shared (NU-050 AC4 on the executor side). Line 5 is its 'as in any other marking': the arming rule of TIME-010's quoted sentence on being newly armed (a firing that writes one of its arc places while it is not armed and leaves it enabled), read by names, with the stamp TIME-010 line 1 gives a newly armed transition. The TIME_010 block states that rule on the count relation only, and this is its ν reading. Lines 1 and 3 fix the stamp of a transition armed before a firing, lines 4 and 5 that of one not armed before, so a firing fixes the stamp of every matched transition of the net except one armed before, ν-enabled in the intermediate marking and not after (the TIME-011 case below) and one not armed before whose arc places the firing does not write (whose enablement the firing does not change)."
          "'Even when its correlated inputs still hold tokens' is the example TIME_012_nu_nonvacuous: the join is enabled on the counts in the intermediate marking and loses its clock; its second half, the taker, is 'even when it is enabled after the firing' (one token in each input, no stamp). 'Even when t took tokens of the name it would have joined on' is TIME_012_nu_keeps: another shared name keeps the join enabled and its clock runs on. TIME_012_nu_matched fires a matched transition, so the intermediate marking is the correlated take of its chosen name: a second join sharing an input keeps its stamp (line 2) and the fired join starts a fresh clock (line 3). Each line has a wrong model it forbids: countKeep (line 1, the first half), staleKeep (line 1, the second half), tookBound (line 2), selfKeep (line 3), staleArm (line 4: a transition with no stamp before the firing is given the stamp 0 even when no name is shared after it) and noArm (line 5: a transition with no stamp before the firing is never given one)."
          "The bullet's ν-join clause (removing tokens disables through ν-join bindings) is line 1 with NuEnabled in place of the count enablement; the step that reads the intermediate marking on the counts (countKeep) is forbidden by TIME_012_nu_forbids_countKeep. The bullet's other clauses (input arcs, read arcs, cardinality requirements, never inhibitor arcs) are the count reading of the TIME_012 block (time012_inhibitor_never)."
          "An armed matched transition that is ν-enabled in the intermediate marking and not after the firing (the firing deposits into one of its inhibitor places) is constrained by neither line; that case is [TIME-011] ('*When* an armed transition stops being enabled, the executor *shall* discard its stamp.'), as in the TIME_012 block, and the reference gives it no stamp. [TIME-011] has no ν reading yet."
          "The pass, the enablement recheck of [EXEC-003] AC3-AC5, a same-pass deposit and asynchronous actions are not in the atomic step; they are the TIME_012 block's Phase 2 deferrals, and the reference executor RefExec has no ν firing kernel yet, so the ν-join clause is not stated on RefExec, and the sentence on a firing pass that starts a transition is not read by names here. The join's one-cycle wait after a same-pass deposit into a correlated input ([EXEC-003] AC4) is not part of this clause. The deadline step, reaps ([TIME-013]) and injected tokens are not steps of the ν relation; the reference fires only an armed transition past its earliest bound."
          "AC1-AC6 of TIME-012 are about transitions without a match and are accounted for in the TIME_012 block. AC7 is TIME_012_nu_nonvacuous (the refresh restarts the join although both inputs held tokens throughout), AC8 is TIME_012_nu_keeps (the join's clock continues), and AC9 is TIME_012_nu_matched (a join sharing an input with the fired join keeps its clock; the fired join starts a fresh one). AC8's event clause (no TransitionClockRestarted or TransitionEnabled for the join) needs the event log and is deferred with AC4's and AC6, as in the TIME_012 block. The Route B graph's reading of the same rule ([NU-050]) is NU-050's timed block, not this block."
  signoff "2026-11-13 f72291b63bd6aa11 ai"
  statement : ∀ {N V Nm : Type} [DecidableEq N] [LinearOrder Nm], NuTRel N V Nm → Prop :=
    fun R => ∀ X : NuTimedNet _ _ _,
      (∀ t c e u, NuInNet X u → u.mspec.isSome = true → u.base.core.name ≠ t.base.core.name →
          on (fun s s' => R X s (.fire t c e) s'), shall (fun s s' => NuArmed s u →
            ¬ NuEnabled u (NuMid t s.M c) →
              (NuEnabled u s'.M → NuArmed s' u ∧ s'.stamp u.base.core.name = some s'.now) ∧
                (¬ NuEnabled u s'.M → s'.stamp u.base.core.name = none))) ∧
      (∀ t c e u, NuInNet X u → u.mspec.isSome = true → u.base.core.name ≠ t.base.core.name →
          on (fun s s' => R X s (.fire t c e) s'), shall (fun s s' => NuArmed s u →
            NuEnabled u (NuMid t s.M c) → NuEnabled u s'.M →
              s'.stamp u.base.core.name = s.stamp u.base.core.name)) ∧
      (∀ t c e u, NuInNet X u → u.mspec.isSome = true → u.base.core.name = t.base.core.name →
          on (fun s s' => R X s (.fire t c e) s'), shall (fun s s' => NuArmed s u →
            (NuEnabled u s'.M → NuArmed s' u ∧ s'.stamp u.base.core.name = some s'.now) ∧
              (¬ NuEnabled u s'.M → s'.stamp u.base.core.name = none))) ∧
      (∀ t c e u, NuInNet X u → u.mspec.isSome = true →
          on (fun s s' => R X s (.fire t c e) s'), shall (fun _ s' => ¬ NuEnabled u s'.M →
            s'.stamp u.base.core.name = none)) ∧
      (∀ t c e u, NuInNet X u → u.mspec.isSome = true →
          on (fun s s' => R X s (.fire t c e) s'), shall (fun s s' => ¬ NuArmed s u →
            (∃ p, ArcPlace u.base p ∧ Writes t.base (e.map Prod.fst) p) → NuEnabled u s'.M →
              NuArmed s' u ∧ s'.stamp u.base.core.name = some s'.now))

/- The pinned readable form of the ν-join clause: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.TIME_012_nu : {N V Nm : Type} → [DecidableEq N] → [LinearOrder Nm] → NuTRel N V Nm → Prop :=
fun {N V Nm} [DecidableEq N] [LinearOrder Nm] R =>
  ∀ (X : NuTimedNet N V Nm),
    (∀ (t : NuTrans N (KeyFn V Nm)) (c : Option Nm) (e : List (N × Stamped V)) (u : NuTrans N (KeyFn V Nm)),
        NuInNet X u →
          u.mspec.isSome = true →
            u.base.core.name ≠ t.base.core.name →
              on fun s s' => R X s (NuTLbl.fire t c e) s', shall fun s s' =>
                NuArmed s u →
                  ¬NuEnabled u (NuMid t s.M c) →
                    (NuEnabled u s'.M → NuArmed s' u ∧ s'.stamp u.base.core.name = some s'.now) ∧
                      (¬NuEnabled u s'.M → s'.stamp u.base.core.name = none)) ∧
      (∀ (t : NuTrans N (KeyFn V Nm)) (c : Option Nm) (e : List (N × Stamped V)) (u : NuTrans N (KeyFn V Nm)),
          NuInNet X u →
            u.mspec.isSome = true →
              u.base.core.name ≠ t.base.core.name →
                on fun s s' => R X s (NuTLbl.fire t c e) s', shall fun s s' =>
                  NuArmed s u →
                    NuEnabled u (NuMid t s.M c) →
                      NuEnabled u s'.M → s'.stamp u.base.core.name = s.stamp u.base.core.name) ∧
        (∀ (t : NuTrans N (KeyFn V Nm)) (c : Option Nm) (e : List (N × Stamped V)) (u : NuTrans N (KeyFn V Nm)),
            NuInNet X u →
              u.mspec.isSome = true →
                u.base.core.name = t.base.core.name →
                  on fun s s' => R X s (NuTLbl.fire t c e) s', shall fun s s' =>
                    NuArmed s u →
                      (NuEnabled u s'.M → NuArmed s' u ∧ s'.stamp u.base.core.name = some s'.now) ∧
                        (¬NuEnabled u s'.M → s'.stamp u.base.core.name = none)) ∧
          (∀ (t : NuTrans N (KeyFn V Nm)) (c : Option Nm) (e : List (N × Stamped V)) (u : NuTrans N (KeyFn V Nm)),
              NuInNet X u →
                u.mspec.isSome = true →
                  on fun s s' => R X s (NuTLbl.fire t c e) s', shall fun x s' =>
                    ¬NuEnabled u s'.M → s'.stamp u.base.core.name = none) ∧
            ∀ (t : NuTrans N (KeyFn V Nm)) (c : Option Nm) (e : List (N × Stamped V)) (u : NuTrans N (KeyFn V Nm)),
              NuInNet X u →
                u.mspec.isSome = true →
                  on fun s s' => R X s (NuTLbl.fire t c e) s', shall fun s s' =>
                    ¬NuArmed s u →
                      (∃ p, ArcPlace u.base p ∧ Writes t.base (List.map Prod.fst e) p) →
                        NuEnabled u s'.M → NuArmed s' u ∧ s'.stamp u.base.core.name = some s'.now
-/
#guard_msgs in #print TIME_012_nu

/-! ## The reference timed ν step -/

section Ref

variable {N V Nm : Type} [DecidableEq N] [LinearOrder Nm]

/-- ν enablement as a test: enabled on the counts and, for a matched transition, some
candidate name ([NU-022]'s `cands`, the eligible names). -/
def nuEnabledB (u : NuTrans N (KeyFn V Nm)) (M : QMarking N (Stamped V)) : Bool :=
  enabledNA (qCount M) u.base.core &&
    match u.mspec with
    | none => true
    | some ms => !(cands (matchIn ms u M)).isEmpty

/-- The test is ν enablement. -/
theorem nuEnabledB_iff (u : NuTrans N (KeyFn V Nm)) (M : QMarking N (Stamped V)) :
    nuEnabledB u M = true ↔ NuEnabled u M := by
  unfold nuEnabledB NuEnabled
  cases h : u.mspec with
  | none =>
    simp [Enabled]
  | some ms =>
    simp only [Bool.and_eq_true, Bool.not_eq_true', Enabled]
    constructor
    · rintro ⟨he, hc⟩
      refine ⟨he, fun ms' hms => ?_⟩
      cases hms
      cases hl : cands (matchIn ms u M) with
      | nil => rw [hl] at hc; simp at hc
      | cons n _ => exact ⟨n, mem_cands.1 (by rw [hl]; exact List.mem_cons_self ..)⟩
    · rintro ⟨he, hn⟩
      refine ⟨he, ?_⟩
      obtain ⟨n, hn⟩ := hn ms rfl
      have hm := mem_cands.2 hn
      cases hl : cands (matchIn ms u M) with
      | nil => rw [hl] at hm; exact absurd hm List.not_mem_nil
      | cons _ _ => rfl

/-- Armed, read by names, as a test. -/
def nuArmedB (s : NuTSt N V) (u : NuTrans N (KeyFn V Nm)) : Bool :=
  nuEnabledB u s.M && (s.stamp u.base.core.name).isSome

/-- The test is armed, read by names. -/
theorem nuArmedB_iff (s : NuTSt N V) (u : NuTrans N (KeyFn V Nm)) :
    nuArmedB s u = true ↔ NuArmed s u := by
  simp [nuArmedB, NuArmed, nuEnabledB_iff]

/-- A keep rule: given the state before the firing, the fired transition, its chosen name, the
marking after the firing and a transition `u`, whether `u` keeps its stamp. -/
abbrev NuKeep (N V Nm : Type) :=
  NuTSt N V → NuTrans N (KeyFn V Nm) → Option Nm → QMarking N (Stamped V) →
    NuTrans N (KeyFn V Nm) → Bool

/-- The spec's keep rule: an armed transition other than the fired one keeps its stamp when it
is ν-enabled in the intermediate marking and after the firing. -/
def refNuKeep : NuKeep N V Nm := fun s t c M' u =>
  nuArmedB s u && u.base.core.name != t.base.core.name && nuEnabledB u (NuMid t s.M c) &&
    nuEnabledB u M'

/-- The stamps after `t` fires with chosen name `c` and emission `e` to marking `M'`, under the
keep rule `k`: each name of the net keeps its stamp when `k` says so; otherwise its transition
is armed with the current reading when it is ν-enabled after the firing and was armed before or
had an arc place written ([TIME-010], as in `refPolicy`); otherwise it holds no stamp. A name
the net does not hold has no stamp. -/
def nuRestamp (k : NuKeep N V Nm) (X : NuTimedNet N V Nm) (s : NuTSt N V)
    (t : NuTrans N (KeyFn V Nm)) (c : Option Nm) (e : List (N × Stamped V))
    (M' : QMarking N (Stamped V)) : String → Option Nat := fun nm =>
  match X.trans.find? (·.base.core.name == nm) with
  | some u =>
    if k s t c M' u then s.stamp nm
    else if nuEnabledB u M' && (nuArmedB s u || writesArc t.base (e.map Prod.fst) u.base) then
      some s.now
    else none
  | none => none

/-- The elapsed time of `t`: the clock reading minus its stamp (0 without a stamp). -/
def nuElapsed (s : NuTSt N V) (t : NuTrans N (KeyFn V Nm)) : Nat :=
  s.now - (s.stamp t.base.core.name).getD s.now

/-- **The timed ν step under keep rule `k`.** A delay advances the clock; an armed transition of
the net past its earliest bound fires as `RefNuFire` says, and the stamps are recomputed. -/
inductive RefNuTStepK (k : NuKeep N V Nm) :
    NuTimedNet N V Nm → NuTSt N V → NuTLbl N V Nm → NuTSt N V → Prop
  /-- The clock advances; the marking and every stamp stay. -/
  | delay (X : NuTimedNet N V Nm) (s : NuTSt N V) (δ : Nat) :
      RefNuTStepK k X s (.delay δ) { s with now := s.now + δ }
  /-- An armed transition of the net past its earliest bound fires. -/
  | fire (X : NuTimedNet N V Nm) (s : NuTSt N V) (t : NuTrans N (KeyFn V Nm)) (c : Option Nm)
      (δ : QDelivered N (Stamped V)) (e : List (N × Stamped V)) (M' : QMarking N (Stamped V))
      (ht : t ∈ X.trans) (hf : RefNuFire t s.M c δ e M') (ha : nuArmedB s t = true)
      (hg : (X.timing t.base).earliest ≤ nuElapsed s t) :
      RefNuTStepK k X s (.fire t c e) { M := M', now := s.now, stamp := nuRestamp k X s t c e M' }

/-- **The timed ν reference step** (witness model): the step under the spec's keep rule. -/
def RefNuTStep : NuTRel N V Nm := RefNuTStepK refNuKeep

/-- A firing step, inverted. -/
theorem refNuTStepK_fire_inv {k : NuKeep N V Nm} {X : NuTimedNet N V Nm} {s s' : NuTSt N V}
    {t : NuTrans N (KeyFn V Nm)} {c : Option Nm} {e : List (N × Stamped V)}
    (h : RefNuTStepK k X s (.fire t c e) s') :
    t ∈ X.trans ∧ (∃ δ, RefNuFire t s.M c δ e s'.M) ∧ nuArmedB s t = true ∧ s'.now = s.now ∧
      s'.stamp = nuRestamp k X s t c e s'.M := by
  cases h
  exact ⟨by assumption, ⟨_, by assumption⟩, by assumption, rfl, rfl⟩

/-- The stamp a net's transition holds after a firing, by the keep rule and the re-arm rule. -/
theorem nuRestamp_inNet {k : NuKeep N V Nm} {X : NuTimedNet N V Nm} {u : NuTrans N (KeyFn V Nm)}
    (hu : NuInNet X u) (s : NuTSt N V) (t : NuTrans N (KeyFn V Nm)) (c : Option Nm)
    (e : List (N × Stamped V)) (M' : QMarking N (Stamped V)) :
    nuRestamp k X s t c e M' u.base.core.name =
      if k s t c M' u then s.stamp u.base.core.name
      else if nuEnabledB u M' && (nuArmedB s u || writesArc t.base (e.map Prod.fst) u.base) then
        some s.now
      else none := by
  unfold nuRestamp
  rw [show X.trans.find? (·.base.core.name == u.base.core.name) = some u from hu]

/-- An armed transition of the net that the keep rule does not keep is armed again with the
reading after the firing when it is ν-enabled then, and holds no stamp otherwise. -/
theorem nuRestamp_lost {k : NuKeep N V Nm} {X : NuTimedNet N V Nm} {u : NuTrans N (KeyFn V Nm)}
    (hu : NuInNet X u) {s0 s' : NuTSt N V} {t : NuTrans N (KeyFn V Nm)} {c : Option Nm}
    {e : List (N × Stamped V)} (ha : NuArmed s0 u) (hk : k s0 t c s'.M u = false)
    (hnow : s'.now = s0.now) (hst : s'.stamp = nuRestamp k X s0 t c e s'.M) :
    (NuEnabled u s'.M → NuArmed s' u ∧ s'.stamp u.base.core.name = some s'.now) ∧
      (¬ NuEnabled u s'.M → s'.stamp u.base.core.name = none) := by
  have ha' : nuArmedB s0 u = true := (nuArmedB_iff s0 u).2 ha
  have hs : s'.stamp u.base.core.name =
      if nuEnabledB u s'.M = true then some s0.now else none := by
    rw [hst, nuRestamp_inNet hu, hk, ha']
    simp
  refine ⟨fun hen => ?_, fun hen => ?_⟩
  · have hen' := (nuEnabledB_iff u s'.M).2 hen
    rw [if_pos hen'] at hs
    exact ⟨⟨hen, by rw [hs]; rfl⟩, by rw [hs, hnow]⟩
  · have hen' : ¬ nuEnabledB u s'.M = true := fun h' => hen ((nuEnabledB_iff _ _).1 h')
    rw [if_neg hen'] at hs
    exact hs

/-- **The five lines hold of every relation whose firings restamp by a keep rule** `k`, from a
state `s0` with the marking and stamps of the state before (its clock reading may differ), when
`k` keeps only what is ν-enabled in the intermediate marking (`hk1`), keeps every armed
transition other than the fired one that is ν-enabled in the intermediate marking and after the
firing (`hk2`), never keeps a transition named like the fired one (`hk3`), and keeps only an armed
transition that is ν-enabled after the firing (`hk4`, `hk5`). -/
theorem time012nu_ofRel (R : NuTRel N V Nm) (k : NuKeep N V Nm)
    (hk1 : ∀ s t c M' u, k s t c M' u = true → nuEnabledB u (NuMid t s.M c) = true)
    (hk2 : ∀ s t c M' u, nuArmedB s u = true → u.base.core.name ≠ t.base.core.name →
      nuEnabledB u (NuMid t s.M c) = true → nuEnabledB u M' = true → k s t c M' u = true)
    (hk3 : ∀ s t c M' u, u.base.core.name = t.base.core.name → k s t c M' u = false)
    (hk4 : ∀ s t c M' u, k s t c M' u = true → nuEnabledB u M' = true)
    (hk5 : ∀ s t c M' u, k s t c M' u = true → nuArmedB s u = true)
    (hR : ∀ X s t c e s', R X s (.fire t c e) s' → ∃ s0 : NuTSt N V, s0.M = s.M ∧
      s0.stamp = s.stamp ∧ s'.now = s0.now ∧ s'.stamp = nuRestamp k X s0 t c e s'.M) :
    TIME_012_nu R := by
  have tr : ∀ {s s0 : NuTSt N V} (u : NuTrans N (KeyFn V Nm)), s0.M = s.M →
      s0.stamp = s.stamp → NuArmed s u → NuArmed s0 u := by
    intro s s0 u hM hS ha
    unfold NuArmed at *
    rw [hM, hS]
    exact ha
  intro X
  refine ⟨fun t c e u hu _ hne s s' h ha hmid => ?_,
    fun t c e u hu _ hne s s' h ha hmid hen => ?_,
    fun t c e u hu _ heq s s' h ha => ?_,
    fun t c e u hu _ s s' h hen => ?_,
    fun t c e u hu _ s s' h ha hw hen => ?_⟩
  · obtain ⟨s0, hM, hS, hnow, hst⟩ := hR X s t c e s' h
    have hk : k s0 t c s'.M u = false := by
      cases hkk : k s0 t c s'.M u with
      | false => rfl
      | true =>
        have := (nuEnabledB_iff _ _).1 (hk1 _ _ _ _ _ hkk)
        rw [hM] at this
        exact absurd this hmid
    exact nuRestamp_lost hu (tr u hM hS ha) hk hnow hst
  · obtain ⟨s0, hM, hS, -, hst⟩ := hR X s t c e s' h
    have hk := hk2 s0 t c s'.M u ((nuArmedB_iff s0 u).2 (tr u hM hS ha)) hne
      ((nuEnabledB_iff _ _).2 (by rw [hM]; exact hmid)) ((nuEnabledB_iff _ _).2 hen)
    rw [hst, nuRestamp_inNet hu, if_pos hk, hS]
  · obtain ⟨s0, hM, hS, hnow, hst⟩ := hR X s t c e s' h
    exact nuRestamp_lost hu (tr u hM hS ha) (hk3 _ _ _ _ _ heq) hnow hst
  · obtain ⟨s0, -, -, -, hst⟩ := hR X s t c e s' h
    have hen' : nuEnabledB u s'.M = false := by
      cases hb : nuEnabledB u s'.M with
      | false => rfl
      | true => exact absurd ((nuEnabledB_iff _ _).1 hb) hen
    have hk : k s0 t c s'.M u = false := by
      cases hkk : k s0 t c s'.M u with
      | false => rfl
      | true => rw [hk4 _ _ _ _ _ hkk] at hen'; exact absurd hen' (by decide)
    rw [hst, nuRestamp_inNet hu, hk, hen']
    simp
  · obtain ⟨s0, hM, hS, hnow, hst⟩ := hR X s t c e s' h
    have ha0 : nuArmedB s0 u = false := by
      cases hb : nuArmedB s0 u with
      | false => rfl
      | true =>
        have h0 := (nuArmedB_iff _ _).1 hb
        exact absurd (by unfold NuArmed at h0 ⊢; rw [← hM, ← hS]; exact h0) ha
    have hk : k s0 t c s'.M u = false := by
      cases hkk : k s0 t c s'.M u with
      | false => rfl
      | true => rw [hk5 _ _ _ _ _ hkk] at ha0; exact absurd ha0 (by decide)
    have hen' := (nuEnabledB_iff _ _).2 hen
    have hw' := (writesArc_iff _ _ _).2 hw
    have hs : s'.stamp u.base.core.name = some s'.now := by
      rw [hst, nuRestamp_inNet hu, hk, ha0, hen', hw', hnow]
      simp
    exact ⟨⟨hen, by rw [hs]; rfl⟩, hs⟩

/-- The spec's keep rule keeps only what is ν-enabled in the intermediate marking. -/
theorem refNuKeep_mid : ∀ (s : NuTSt N V) t (c : Option Nm) M' u,
    refNuKeep s t c M' u = true → nuEnabledB u (NuMid t s.M c) = true := by
  intro _ _ _ _ _ hk
  simp only [refNuKeep, Bool.and_eq_true] at hk
  exact hk.1.2

/-- The spec's keep rule keeps what line 2 keeps. -/
theorem refNuKeep_keeps : ∀ (s : NuTSt N V) (t : NuTrans N (KeyFn V Nm)) (c : Option Nm) M' u,
    nuArmedB s u = true → u.base.core.name ≠ t.base.core.name →
      nuEnabledB u (NuMid t s.M c) = true → nuEnabledB u M' = true → refNuKeep s t c M' u = true := by
  intro _ _ _ _ _ ha hne hmid hen
  simp [refNuKeep, ha, hne, hmid, hen]

/-- The spec's keep rule keeps only what is ν-enabled after the firing. -/
theorem refNuKeep_after : ∀ (s : NuTSt N V) (t : NuTrans N (KeyFn V Nm)) (c : Option Nm) M' u,
    refNuKeep s t c M' u = true → nuEnabledB u M' = true := by
  intro _ _ _ _ _ hk
  simp only [refNuKeep, Bool.and_eq_true] at hk
  exact hk.2

/-- The spec's keep rule keeps only an armed transition. -/
theorem refNuKeep_armed : ∀ (s : NuTSt N V) (t : NuTrans N (KeyFn V Nm)) (c : Option Nm) M' u,
    refNuKeep s t c M' u = true → nuArmedB s u = true := by
  intro _ _ _ _ _ hk
  simp only [refNuKeep, Bool.and_eq_true] at hk
  exact hk.1.1.1

/-- The spec's keep rule never keeps a transition named like the fired one. -/
theorem refNuKeep_fired : ∀ (s : NuTSt N V) (t : NuTrans N (KeyFn V Nm)) (c : Option Nm) M' u,
    u.base.core.name = t.base.core.name → refNuKeep s t c M' u = false := by
  intro _ _ _ _ _ heq
  simp [refNuKeep, heq]

/-- **The five lines hold of every step under a keep rule** that satisfies `hk1`-`hk5` of
`time012nu_ofRel`. -/
theorem time012nu_of (k : NuKeep N V Nm)
    (hk1 : ∀ s t c M' u, k s t c M' u = true → nuEnabledB u (NuMid t s.M c) = true)
    (hk2 : ∀ s t c M' u, nuArmedB s u = true → u.base.core.name ≠ t.base.core.name →
      nuEnabledB u (NuMid t s.M c) = true → nuEnabledB u M' = true → k s t c M' u = true)
    (hk3 : ∀ s t c M' u, u.base.core.name = t.base.core.name → k s t c M' u = false)
    (hk4 : ∀ s t c M' u, k s t c M' u = true → nuEnabledB u M' = true)
    (hk5 : ∀ s t c M' u, k s t c M' u = true → nuArmedB s u = true) :
    TIME_012_nu (RefNuTStepK k) :=
  time012nu_ofRel _ k hk1 hk2 hk3 hk4 hk5 fun _ s _ _ _ _ h => by
    obtain ⟨-, -, -, hnow, hst⟩ := refNuTStepK_fire_inv h
    exact ⟨s, rfl, rfl, hnow, hst⟩

/-- **Frame (kept out of the statement): a firing is instantaneous on the firing clock.** Every
firing step of `R` leaves the clock reading as it is. -/
def time012nu_FramesClock (R : NuTRel N V Nm) : Prop :=
  ∀ X s t c e s', R X s (.fire t c e) s' → s'.now = s.now

/-- **Frame (kept out of the statement): the label names the take.** The marking after a firing
step is the intermediate marking of its label (the tokens of the chosen name taken) with the
emission appended at the tails ([EXEC-020]). -/
def time012nu_FramesMid (R : NuTRel N V Nm) : Prop :=
  ∀ X s t c e s', R X s (.fire t c e) s' → s'.M = qAppend (NuMid t s.M c) e

/-- Every step under a keep rule frames the firing clock. -/
theorem time012nu_framesClock_K (k : NuKeep N V Nm) : time012nu_FramesClock (RefNuTStepK k) :=
  fun _ _ _ _ _ _ h => (refNuTStepK_fire_inv h).2.2.2.1

/-- Every step under a keep rule leaves the intermediate marking of its label with the emission
at the tails. -/
theorem time012nu_framesMid_K (k : NuKeep N V Nm) : time012nu_FramesMid (RefNuTStepK k) := by
  intro X s t c e s' h
  obtain ⟨-, ⟨δ, hf⟩, -, -, -⟩ := refNuTStepK_fire_inv h
  unfold RefNuFire at hf
  unfold NuMid
  cases hm : t.mspec with
  | none =>
    rw [hm] at hf
    obtain ⟨rfl, -, -, -, hM⟩ := hf
    rw [hM]; rfl
  | some ms =>
    rw [hm] at hf
    obtain ⟨n, rfl, -, -, -, -, -, hM⟩ := hf
    exact hM

end Ref

#spec_witness RefNuTStep

/-- The timed ν reference step satisfies the ν-join clause of TIME-012. A join keeps its clock
across a firing exactly when it was armed, is not the fired transition, and has an eligible name
both in the intermediate marking and after the firing; a join that loses its clock and has an
eligible name after the firing is armed again with the current reading, and one without holds no
stamp. A fired join always starts a fresh clock. A join with no clock whose inputs come to share a
name in a firing that writes one of them is armed with the current reading, and a join that
shares no name after a firing holds no stamp. -/
@[evidence holds TIME_012_nu]
theorem TIME_012_nu_reference {N V Nm : Type} [DecidableEq N] [LinearOrder Nm] :
    TIME_012_nu (RefNuTStep (N := N) (V := V) (Nm := Nm)) :=
  time012nu_of _ refNuKeep_mid refNuKeep_keeps refNuKeep_fired refNuKeep_after refNuKeep_armed

/-- The reference step frames the firing clock: a firing at reading `10` leaves the clock at
`10`. -/
theorem TIME_012_nu_reference_framesClock {N V Nm : Type} [DecidableEq N] [LinearOrder Nm] :
    time012nu_FramesClock (RefNuTStep (N := N) (V := V) (Nm := Nm)) :=
  time012nu_framesClock_K _

/-- The reference step leaves the intermediate marking of its label with the emission at the
tails: a join that fires on name `2` leaves exactly its inputs without their first tokens of
name `2`, plus what it emits. -/
theorem TIME_012_nu_reference_framesMid {N V Nm : Type} [DecidableEq N] [LinearOrder Nm] :
    time012nu_FramesMid (RefNuTStep (N := N) (V := V) (Nm := Nm)) :=
  time012nu_framesMid_K _

/-! ## Links to the count reading -/

section Link

variable {N V Nm : Type} [DecidableEq N] [LinearOrder Nm]

/-- Without a match, ν enablement is enablement on the counts. -/
theorem time012nu_enabled_unmatched {u : NuTrans N (KeyFn V Nm)} (h : u.mspec = none)
    (M : QMarking N (Stamped V)) : NuEnabled u M ↔ Enabled u.base (qCount M) := by
  rw [← nuEnabledB_iff]
  simp [nuEnabledB, h, Enabled]

/-- Without a match on the fired transition, the ν intermediate marking counts as the glossary's
`Mid` of [TIME-012]: inputs consumed, reset places drained, nothing deposited. -/
theorem time012nu_mid_count {t : NuTrans N (KeyFn V Nm)} (h : t.mspec = none)
    (M : QMarking N (Stamped V)) (c : Option Nm) :
    qCount (NuMid t M c) = Mid t.base (qCount M) := by
  have h1 : NuMid t M c = qFire M t.base [] := by
    unfold NuMid; rw [h]; rfl
  rw [h1, qCount_qFire, mid_eq]
  rfl

end Link

/-! ## Examples -/

/-- The key projection of the examples: a token's value is its name. -/
def time012nu_key : KeyFn Nat Nat := some

/-- The join `J`: one token from place `0` and one from place `1`, both of one name. -/
def time012nu_J : NuTrans Nat (KeyFn Nat Nat) :=
  { base := { core := { name := "J", inputs := [⟨0, .one⟩, ⟨1, .one⟩], inhibitors := [],
                        reads := [], resets := [] }, out := none },
    mspec := some { keys := [(0, time012nu_key), (1, time012nu_key)] } }

/-- The refresh `r`: takes the head of place `0` and puts a token back into place `0`. -/
def time012nu_r : NuTrans Nat (KeyFn Nat Nat) :=
  { base := { core := { name := "r", inputs := [⟨0, .one⟩], inhibitors := [], reads := [],
                        resets := [] }, out := some (.place 0) } }

/-- The taker `c`: takes the head of place `0` and puts a token into place `2`. -/
def time012nu_c : NuTrans Nat (KeyFn Nat Nat) :=
  { base := { core := { name := "c", inputs := [⟨0, .one⟩], inhibitors := [], reads := [],
                        resets := [] }, out := some (.place 2) } }

/-- The net of the examples: `J`, `r` and `c`, all immediate. -/
def time012nu_X : NuTimedNet Nat Nat Nat :=
  { trans := [time012nu_J, time012nu_r, time012nu_c], timing := fun _ => .immediate }

/-- A token of name `n` created at `k`. -/
def time012nu_tok (n : Nat) (k : Int) : Stamped Nat := ⟨n, k⟩

/-- Marking A: place `0` holds a token of name `1` then one of name `2`; place `1` holds a
token of name `1`. The join can join on name `1` only. -/
def time012nu_MA : QMarking Nat (Stamped Nat) := fun p =>
  if p = 0 then [time012nu_tok 1 1, time012nu_tok 2 2]
  else if p = 1 then [time012nu_tok 1 1] else []

/-- Marking B: places `0` and `1` each hold a token of name `1` then one of name `2`. The join
can join on either name. -/
def time012nu_MB : QMarking Nat (Stamped Nat) := fun p =>
  if p = 0 ∨ p = 1 then [time012nu_tok 1 1, time012nu_tok 2 2] else []

/-- The state at clock reading `10` with marking `M`: every transition holds the stamp `0`. -/
def time012nu_s (M : QMarking Nat (Stamped Nat)) : NuTSt Nat Nat :=
  { M := M, now := 10, stamp := fun _ => some 0 }

/-- The state after `t` fires with emission `e` from `time012nu_s M`, under keep rule `k`. -/
def time012nu_after (k : NuKeep Nat Nat Nat) (M : QMarking Nat (Stamped Nat))
    (t : NuTrans Nat (KeyFn Nat Nat)) (e : List (Nat × Stamped Nat)) : NuTSt Nat Nat :=
  { M := qFire M t.base e, now := 10,
    stamp := nuRestamp k time012nu_X (time012nu_s M) t none e (qFire M t.base e) }

/-- The refresh's emission: a new token of name `1`, created at `3`, into place `0`. -/
def time012nu_eR : List (Nat × Stamped Nat) := [(0, time012nu_tok 1 3)]

/-- The taker's emission: a token into place `2`. -/
def time012nu_eC : List (Nat × Stamped Nat) := [(2, time012nu_tok 7 5)]

/-- `J` is the net's transition of its name. -/
theorem time012nu_J_in : NuInNet time012nu_X time012nu_J := rfl

/-- Every unmatched firing of the examples, from any state, is a step of `RefNuTStepK k`, for
every keep rule. -/
theorem time012nu_stepAt (k : NuKeep Nat Nat Nat) (s : NuTSt Nat Nat)
    (t : NuTrans Nat (KeyFn Nat Nat)) (e : List (Nat × Stamped Nat))
    (ht : t ∈ time012nu_X.trans) (hm : t.mspec = none)
    (hen : enabledNA (qCount s.M) t.base.core = true)
    (hd : ∃ ch, deposit (nconsumed (qCount s.M) t.base.core) t.base.out ch = some (e.map Prod.fst))
    (ha : nuArmedB s t = true) :
    RefNuTStepK k time012nu_X s (.fire t none e)
      { M := qFire s.M t.base e, now := s.now,
        stamp := nuRestamp k time012nu_X s t none e (qFire s.M t.base e) } := by
  refine RefNuTStepK.fire _ _ _ _ (qDelivered s.M t.base) _ _ ht ?_ ha
    (by simp [time012nu_X, Timing.earliest])
  unfold RefNuFire
  rw [hm]
  exact ⟨rfl, hen, hd, rfl, rfl⟩

/-- Every unmatched firing of the examples from `time012nu_s M` is a step of `RefNuTStepK k`. -/
theorem time012nu_step (k : NuKeep Nat Nat Nat) (M : QMarking Nat (Stamped Nat))
    (t : NuTrans Nat (KeyFn Nat Nat)) (e : List (Nat × Stamped Nat))
    (ht : t ∈ time012nu_X.trans) (hm : t.mspec = none)
    (hen : enabledNA (qCount M) t.base.core = true)
    (hd : ∃ ch, deposit (nconsumed (qCount M) t.base.core) t.base.out ch = some (e.map Prod.fst))
    (ha : nuArmedB (time012nu_s M) t = true) :
    RefNuTStepK k time012nu_X (time012nu_s M) (.fire t none e) (time012nu_after k M t e) :=
  time012nu_stepAt k (time012nu_s M) t e ht hm hen hd ha

/-- **Worked example (AC7): the join loses its clock although its inputs still hold tokens.**
Place `0` holds a token of name `1` and one of name `2`, place `1` a token of name `1`; the join
`J` is armed since `0` and could join on name `1`. At `10` the refresh `r` takes the head of
place `0` (name `1`) and puts a new token of name `1` back at its tail. In the intermediate
marking place `0` holds only name `2` and place `1` only name `1`: `J` is enabled on the counts
(one token each) but no name is shared, so it loses its clock. After the firing name `1` is
shared again, and `J` is armed with the fresh stamp `10`. Had the taker `c` fired instead,
sending its token elsewhere, `J` would hold no stamp after the firing, although it is still
enabled on its counts, with one token in each input. -/
@[evidence nonvacuous TIME_012_nu]
theorem TIME_012_nu_nonvacuous :
    RefNuTStep time012nu_X (time012nu_s time012nu_MA) (.fire time012nu_r none time012nu_eR)
        (time012nu_after refNuKeep time012nu_MA time012nu_r time012nu_eR) ∧
      NuArmed (time012nu_s time012nu_MA) time012nu_J ∧
      Enabled time012nu_J.base (qCount (NuMid time012nu_r time012nu_MA none)) ∧
      ¬ NuEnabled time012nu_J (NuMid time012nu_r time012nu_MA none) ∧
      NuArmed (time012nu_after refNuKeep time012nu_MA time012nu_r time012nu_eR) time012nu_J ∧
      (time012nu_after refNuKeep time012nu_MA time012nu_r time012nu_eR).stamp "J" = some 10 ∧
      RefNuTStep time012nu_X (time012nu_s time012nu_MA) (.fire time012nu_c none time012nu_eC)
        (time012nu_after refNuKeep time012nu_MA time012nu_c time012nu_eC) ∧
      Enabled time012nu_J.base
        (qCount (time012nu_after refNuKeep time012nu_MA time012nu_c time012nu_eC).M) ∧
      (time012nu_after refNuKeep time012nu_MA time012nu_c time012nu_eC).stamp "J" = none := by
  refine ⟨time012nu_step _ _ _ _ (by simp [time012nu_X]) rfl (by decide)
      ⟨.action 0, rfl⟩ (by decide), (nuArmedB_iff _ _).1 (by decide), by decide,
    fun h => absurd ((nuEnabledB_iff _ _).2 h) (by decide), (nuArmedB_iff _ _).1 (by decide),
    by decide,
    time012nu_step _ _ _ _ (by simp [time012nu_X]) rfl (by decide) ⟨.action 0, rfl⟩ (by decide),
    by decide, by decide⟩

/-- **Worked example (AC8): another shared name keeps the clock.** Places `0` and `1` each hold
a token of name `1` and then one of name `2`; the join `J` is armed since `0` and would join on
name `1`, the older one. At `10` the taker `c` takes the head of place `0`, the token of name
`1`. Name `2` is still in both inputs, in the intermediate marking and after the firing, so `J`
keeps its stamp `0`. -/
@[evidence nonvacuous TIME_012_nu]
theorem TIME_012_nu_keeps :
    RefNuTStep time012nu_X (time012nu_s time012nu_MB) (.fire time012nu_c none time012nu_eC)
        (time012nu_after refNuKeep time012nu_MB time012nu_c time012nu_eC) ∧
      NuArmed (time012nu_s time012nu_MB) time012nu_J ∧
      NuEnabled time012nu_J (NuMid time012nu_c time012nu_MB none) ∧
      NuEnabled time012nu_J (time012nu_after refNuKeep time012nu_MB time012nu_c time012nu_eC).M ∧
      (time012nu_after refNuKeep time012nu_MB time012nu_c time012nu_eC).stamp "J" = some 0 :=
  ⟨time012nu_step _ _ _ _ (by simp [time012nu_X]) rfl (by decide) ⟨.action 0, rfl⟩ (by decide),
    (nuArmedB_iff _ _).1 (by decide), (nuEnabledB_iff _ _).1 (by decide),
    (nuEnabledB_iff _ _).1 (by decide), by decide⟩

/-! ### Two joins sharing a correlated input -/

/-- The match of `J1`: places `0` and `1`, keyed by the token's name. -/
def time012nu_ms1 : MatchSpec Nat (KeyFn Nat Nat) :=
  { keys := [(0, time012nu_key), (1, time012nu_key)] }

/-- The join `J1`: one token from place `0` and one from place `1`, both of one name. -/
def time012nu_J1 : NuTrans Nat (KeyFn Nat Nat) :=
  { base := { core := { name := "J1", inputs := [⟨0, .one⟩, ⟨1, .one⟩], inhibitors := [],
                        reads := [], resets := [] }, out := none },
    mspec := some time012nu_ms1 }

/-- The join `J2`: one token from place `0` and one from place `3`, both of one name. -/
def time012nu_J2 : NuTrans Nat (KeyFn Nat Nat) :=
  { base := { core := { name := "J2", inputs := [⟨0, .one⟩, ⟨3, .one⟩], inhibitors := [],
                        reads := [], resets := [] }, out := none },
    mspec := some { keys := [(0, time012nu_key), (3, time012nu_key)] } }

/-- The net of two joins sharing place `0`, both immediate. -/
def time012nu_X2 : NuTimedNet Nat Nat Nat :=
  { trans := [time012nu_J1, time012nu_J2], timing := fun _ => .immediate }

/-- Marking C: place `0` holds a token of name `1` and then two of name `2`; place `1` two
tokens of name `2`; place `3` a token of name `1`. `J1` can join on name `2` only, `J2` on name
`1` only. -/
def time012nu_MC : QMarking Nat (Stamped Nat) := fun p =>
  if p = 0 then [time012nu_tok 1 1, time012nu_tok 2 2, time012nu_tok 2 2]
  else if p = 1 then [time012nu_tok 2 2, time012nu_tok 2 2]
  else if p = 3 then [time012nu_tok 1 1] else []

/-- The marking `J1`'s firing on name `2` leaves (it emits nothing). -/
def time012nu_MC1 : QMarking Nat (Stamped Nat) :=
  qAppend (nuConsume time012nu_ms1 time012nu_J1 time012nu_MC 2) []

/-- The state after `J1` fires on name `2` from `time012nu_s time012nu_MC`, under keep rule `k`. -/
def time012nu_afterJ1 (k : NuKeep Nat Nat Nat) : NuTSt Nat Nat :=
  { M := time012nu_MC1, now := 10,
    stamp := nuRestamp k time012nu_X2 (time012nu_s time012nu_MC) time012nu_J1 (some 2) []
      time012nu_MC1 }

/-- `J1` fires on name `2` from marking C, by the reference firing. -/
theorem time012nu_fireJ1 : RefNuFire time012nu_J1 time012nu_MC (some 2)
    (nuDelivered time012nu_ms1 time012nu_J1 time012nu_MC 2) [] time012nu_MC1 := by
  rw [refNuFire_matched (ms := time012nu_ms1) rfl]
  exact ⟨2, rfl, by decide, by decide, ⟨.action 0, rfl⟩, by simp [RelayOk, time012nu_ms1], rfl,
    rfl⟩

/-- `J1`'s firing on name `2` is a step of `RefNuTStepK k`, for every keep rule. -/
theorem time012nu_stepJ1 (k : NuKeep Nat Nat Nat) :
    RefNuTStepK k time012nu_X2 (time012nu_s time012nu_MC) (.fire time012nu_J1 (some 2) [])
      (time012nu_afterJ1 k) :=
  RefNuTStepK.fire _ _ _ (some 2) _ [] _ (by simp [time012nu_X2]) time012nu_fireJ1 (by decide)
    (by simp [time012nu_X2, Timing.earliest])

/-- `J1` is the net's transition of its name. -/
theorem time012nu_J1_in : NuInNet time012nu_X2 time012nu_J1 := rfl

/-- `J2` is the net's transition of its name. -/
theorem time012nu_J2_in : NuInNet time012nu_X2 time012nu_J2 := rfl

/-- **Worked example (AC9): a join fires, and a join sharing an input keeps its clock.** Place
`0` holds a token of name `1` and then two of name `2`, place `1` two tokens of name `2`, place
`3` a token of name `1`; both joins are armed since `0`. At `10` `J1` fires on name `2`: it takes
the first token of name `2` from place `0` and from place `1`, and leaves the token of name `1`
at the head of place `0`. `J2` can still join on name `1`, in the intermediate marking and after
the firing, so it keeps its stamp `0`. `J1` itself can join again on name `2`, and starts a fresh
clock at `10`. -/
@[evidence nonvacuous TIME_012_nu]
theorem TIME_012_nu_matched :
    RefNuTStep time012nu_X2 (time012nu_s time012nu_MC) (.fire time012nu_J1 (some 2) [])
        (time012nu_afterJ1 refNuKeep) ∧
      NuArmed (time012nu_s time012nu_MC) time012nu_J2 ∧
      NuEnabled time012nu_J2 (NuMid time012nu_J1 time012nu_MC (some 2)) ∧
      NuEnabled time012nu_J2 (time012nu_afterJ1 refNuKeep).M ∧
      (time012nu_afterJ1 refNuKeep).stamp "J2" = some 0 ∧
      NuArmed (time012nu_s time012nu_MC) time012nu_J1 ∧
      NuArmed (time012nu_afterJ1 refNuKeep) time012nu_J1 ∧
      (time012nu_afterJ1 refNuKeep).stamp "J1" = some 10 :=
  ⟨time012nu_stepJ1 _, (nuArmedB_iff _ _).1 (by decide), (nuEnabledB_iff _ _).1 (by decide),
    (nuEnabledB_iff _ _).1 (by decide), by decide, (nuArmedB_iff _ _).1 (by decide),
    (nuArmedB_iff _ _).1 (by decide), by decide⟩

/-! ## Wrong models -/

/-- The keep rule without the ν-join clause: a transition keeps its stamp when it is enabled on
the counts of the intermediate marking (and ν-enabled after the firing), whether or not a name
is shared there. -/
def time012nu_countKeep : NuKeep Nat Nat Nat := fun s t c M' u =>
  nuArmedB s u && u.base.core.name != t.base.core.name &&
    enabledNA (qCount (NuMid t s.M c)) u.base.core && nuEnabledB u M'

/-- ✗ Reading the intermediate marking on the token counts violates line 1. In the first worked
example the refresh leaves one token in each input of the join but no shared name; the count
reading keeps the join's stamp `0` instead of restarting it at `10`, so the join could fire at
once on a clock that ran while no name was shared. -/
@[evidence forbids TIME_012_nu]
theorem TIME_012_nu_forbids_countKeep : ¬ TIME_012_nu (RefNuTStepK time012nu_countKeep) := by
  intro h
  have hstep := time012nu_step time012nu_countKeep time012nu_MA time012nu_r time012nu_eR
    (by simp [time012nu_X]) rfl (by decide) ⟨.action 0, rfl⟩ (by decide)
  have e := (((h time012nu_X).1 _ _ _ _ time012nu_J_in rfl (by decide) _ _ hstep
    ((nuArmedB_iff _ _).1 (by decide))
    (fun h' => absurd ((nuEnabledB_iff _ _).2 h') (by decide))).1
    ((nuEnabledB_iff _ _).1 (by decide))).2
  exact absurd e (by decide)

/-- The keep rule that leaves a stale stamp: besides what the spec keeps, an armed transition
other than the fired one keeps its stamp when it is not ν-enabled after the firing (its stamp is
cleared only at a later update). -/
def time012nu_staleKeep : NuKeep Nat Nat Nat := fun s t c M' u =>
  refNuKeep s t c M' u ||
    (nuArmedB s u && u.base.core.name != t.base.core.name && !nuEnabledB u M')

/-- ✗ Leaving a stale stamp on a join with no eligible name violates line 1. In the first worked
example the taker `c` takes the token of name `1` from place `0`; the join `J` has no shared
name in the intermediate marking or after the firing, though one token sits in each input, so
it must hold no stamp. The stale rule leaves it the stamp `0`, so `J` would fire at once when a
name is shared again. -/
@[evidence forbids TIME_012_nu]
theorem TIME_012_nu_forbids_staleKeep : ¬ TIME_012_nu (RefNuTStepK time012nu_staleKeep) := by
  intro h
  have hstep := time012nu_step time012nu_staleKeep time012nu_MA time012nu_c time012nu_eC
    (by simp [time012nu_X]) rfl (by decide) ⟨.action 0, rfl⟩ (by decide)
  have e := (((h time012nu_X).1 _ _ _ _ time012nu_J_in rfl (by decide) _ _ hstep
    ((nuArmedB_iff _ _).1 (by decide))
    (fun h' => absurd ((nuEnabledB_iff _ _).2 h') (by decide))).2
    (fun h' => absurd ((nuEnabledB_iff _ _).2 h') (by decide)))
  exact absurd e (by decide)

/-- Whether the firing of `t` with chosen name `c` takes a token of `u`'s chosen name out of one
of `u`'s correlated inputs. -/
def time012nu_tookBound (s : NuTSt Nat Nat) (t : NuTrans Nat (KeyFn Nat Nat)) (c : Option Nat)
    (u : NuTrans Nat (KeyFn Nat Nat)) : Bool :=
  match u.mspec with
  | none => false
  | some ms =>
    match refSelect (matchIn ms u s.M) with
    | none => false
    | some b => ms.keys.any fun k =>
        decide ((named k.2 b (NuMid t s.M c k.1)).length < (named k.2 b (s.M k.1)).length)

/-- The keep rule of the literal first reading of the NU-050 sentence (clash nu-b#10): a join
restarts its clock whenever the firing takes a token of its chosen name out of a correlated
input, even when another name stays shared. -/
def time012nu_tookBoundKeep : NuKeep Nat Nat Nat := fun s t c M' u =>
  refNuKeep s t c M' u && !time012nu_tookBound s t c u

/-- ✗ Restarting a join whose chosen name lost a token violates line 2. In the second worked
example the taker takes the token of name `1` from place `0`; name `2` stays shared, but the
literal reading restarts the join at `10` instead of keeping its stamp `0`. -/
@[evidence forbids TIME_012_nu]
theorem TIME_012_nu_forbids_tookBound : ¬ TIME_012_nu (RefNuTStepK time012nu_tookBoundKeep) := by
  intro h
  have hstep := time012nu_step time012nu_tookBoundKeep time012nu_MB time012nu_c time012nu_eC
    (by simp [time012nu_X]) rfl (by decide) ⟨.action 0, rfl⟩ (by decide)
  have e := (h time012nu_X).2.1 _ _ _ _ time012nu_J_in rfl (by decide) _ _ hstep
    ((nuArmedB_iff _ _).1 (by decide)) ((nuEnabledB_iff _ _).1 (by decide))
    ((nuEnabledB_iff _ _).1 (by decide))
  exact absurd e (by decide)

/-- The keep rule that lets a fired join keep its clock: an armed transition, the fired one
included, keeps its stamp when it is ν-enabled in the intermediate marking and after the firing. -/
def time012nu_selfKeep : NuKeep Nat Nat Nat := fun s t c M' u =>
  nuArmedB s u && nuEnabledB u (NuMid t s.M c) && nuEnabledB u M'

/-- ✗ A fired join that keeps its clock violates line 3. In the third worked example `J1` fires on
name `2` at `10` and can join on name `2` again afterwards; it must start a fresh clock at `10`,
but this rule leaves it the stamp `0`, so it could fire again at once. -/
@[evidence forbids TIME_012_nu]
theorem TIME_012_nu_forbids_selfKeep : ¬ TIME_012_nu (RefNuTStepK time012nu_selfKeep) := by
  intro h
  have e := (((h time012nu_X2).2.2.1 _ _ _ _ time012nu_J1_in rfl rfl _ _
    (time012nu_stepJ1 time012nu_selfKeep) ((nuArmedB_iff _ _).1 (by decide))).1
    ((nuEnabledB_iff _ _).1 (by decide))).2
  exact absurd e (by decide)

/-! ### A join that held no stamp -/

/-- Marking D: place `0` holds a token of name `2`, place `1` a token of name `1`. The join `J`
is enabled on its counts, but no name is shared. -/
def time012nu_MD : QMarking Nat (Stamped Nat) := fun p =>
  if p = 0 then [time012nu_tok 2 2] else if p = 1 then [time012nu_tok 1 1] else []

/-- The state at clock reading `10` with marking D: the join `J` holds no stamp, every other
transition the stamp `0`. -/
def time012nu_sD : NuTSt Nat Nat :=
  { M := time012nu_MD, now := 10, stamp := fun n => if n = "J" then none else some 0 }

/-- The step that gives every transition left without a stamp the stamp `0`: the reference step,
except that a name with no stamp before the firing that the reference leaves without one gets the
stamp `0`. -/
def time012nu_staleArm : NuTRel Nat Nat Nat := fun X s l s' => ∃ s'', RefNuTStep X s l s'' ∧
  s' = { s'' with stamp := fun n =>
    if (s.stamp n).isSome then s''.stamp n else some ((s''.stamp n).getD 0) }

/-- ✗ Giving a clock to a join that shares no name violates line 4. Place `0` holds a token of
name `2` and place `1` one of name `1`; the join `J` holds no stamp. At `10` the taker `c` takes
the token of place `0`, so `J` is not even enabled on its counts afterwards and must hold no
stamp. This step gives it the stamp `0`, so `J` would fire at once as soon as both inputs share a
name. -/
@[evidence forbids TIME_012_nu]
theorem TIME_012_nu_forbids_staleArm : ¬ TIME_012_nu time012nu_staleArm := by
  intro h
  have hstep : time012nu_staleArm time012nu_X time012nu_sD (.fire time012nu_c none time012nu_eC)
      _ :=
    ⟨_, time012nu_stepAt refNuKeep time012nu_sD time012nu_c time012nu_eC
      (by simp [time012nu_X]) rfl (by decide) ⟨.action 0, rfl⟩ (by decide), rfl⟩
  have e := (h time012nu_X).2.2.2.1 _ _ _ _ time012nu_J_in rfl _ _ hstep
    (fun h' => absurd ((nuEnabledB_iff _ _).2 h') (by decide))
  exact absurd e (by decide)

/-- The step that never arms a transition that held no stamp: the reference step, except that a
name with no stamp before the firing holds none after it. -/
def time012nu_noArm : NuTRel Nat Nat Nat := fun X s l s' => ∃ s'', RefNuTStep X s l s'' ∧
  s' = { s'' with stamp := fun n => if (s.stamp n).isSome then s''.stamp n else none }

/-- ✗ Never arming a join that comes to share a name violates line 5. Place `0` holds a token of
name `2` and place `1` one of name `1`; the join `J` holds no stamp. At `10` the refresh `r` takes
the token of name `2` from place `0` and puts one of name `1` there, so both inputs share name `1`
and `J` must be armed with the stamp `10`. This step leaves it without a clock, so `J` could never
fire. -/
@[evidence forbids TIME_012_nu]
theorem TIME_012_nu_forbids_noArm : ¬ TIME_012_nu time012nu_noArm := by
  intro h
  have hstep : time012nu_noArm time012nu_X time012nu_sD (.fire time012nu_r none time012nu_eR) _ :=
    ⟨_, time012nu_stepAt refNuKeep time012nu_sD time012nu_r time012nu_eR
      (by simp [time012nu_X]) rfl (by decide) ⟨.action 0, rfl⟩ (by decide), rfl⟩
  have e := ((h time012nu_X).2.2.2.2 _ _ _ _ time012nu_J_in rfl _ _ hstep
    (fun h' => absurd ((nuArmedB_iff _ _).2 h') (by decide))
    ((writesArc_iff _ _ _).1 (by decide)) ((nuEnabledB_iff _ _).1 (by decide))).2
  exact absurd e (by decide)

/-! ## The two frames the statement leaves out -/

section Gaps

variable {N V Nm : Type} [DecidableEq N] [LinearOrder Nm]

/-- A firing fused with a hidden delay of `1000`: the firing is the reference firing from the
state whose clock reads `1000` later. Delays are as in the reference. -/
def time012nu_fireAdvancesClock : NuTRel N V Nm := fun X s l s' =>
  match l with
  | .fire t c e => RefNuTStep X { s with now := s.now + 1000 } (.fire t c e) s'
  | .delay δ => RefNuTStep X s (.delay δ) s'

/-- A firing whose label carries no chosen name: the reference firing (the real matched take of
the selected name), its stamps recomputed with the spec's keep rule read on the label, so on the
queue heads. -/
inductive time012nu_unnamed : NuTRel N V Nm
  /-- The clock advances; the marking and every stamp stay. -/
  | delay (X : NuTimedNet N V Nm) (s : NuTSt N V) (δ : Nat) :
      time012nu_unnamed X s (.delay δ) { s with now := s.now + δ }
  /-- `t` fires as `RefNuFire` says with chosen name `c`; the label names none. -/
  | fire (X : NuTimedNet N V Nm) (s : NuTSt N V) (t : NuTrans N (KeyFn V Nm)) (c : Option Nm)
      (δ : QDelivered N (Stamped V)) (e : List (N × Stamped V)) (M' : QMarking N (Stamped V))
      (ht : t ∈ X.trans) (hf : RefNuFire t s.M c δ e M') (ha : nuArmedB s t = true)
      (hg : (X.timing t.base).earliest ≤ nuElapsed s t) :
      time012nu_unnamed X s (.fire t none e)
        { M := M', now := s.now, stamp := nuRestamp refNuKeep X s t none e M' }

/-- A firing step of the unnamed relation, inverted. -/
theorem time012nu_unnamed_inv {X : NuTimedNet N V Nm} {s s' : NuTSt N V}
    {t : NuTrans N (KeyFn V Nm)} {c : Option Nm} {e : List (N × Stamped V)}
    (h : time012nu_unnamed X s (.fire t c e) s') :
    c = none ∧ s'.now = s.now ∧ s'.stamp = nuRestamp refNuKeep X s t none e s'.M := by
  cases h
  exact ⟨rfl, rfl, rfl⟩

end Gaps

/-- ✗ The hidden delay is a gap of the statement, closed by the clock frame: a firing fused with
a delay of `1000` satisfies the five lines, since it stamps every restarted clock with the
reading after the firing, and it does not frame the firing clock. In the first worked example
the refresh fires at `10` and the clock reads `1010` after it, so the join's restarted clock
reads `1010` and every clock the firing keeps gains `1000` without a delay step. -/
theorem TIME_012_nu_gap_fireAdvancesClock :
    TIME_012_nu (time012nu_fireAdvancesClock (N := Nat) (V := Nat) (Nm := Nat)) ∧
      ¬ time012nu_FramesClock (time012nu_fireAdvancesClock (N := Nat) (V := Nat) (Nm := Nat)) := by
  refine ⟨time012nu_ofRel _ refNuKeep refNuKeep_mid refNuKeep_keeps refNuKeep_fired
    refNuKeep_after refNuKeep_armed
    fun X s t c e s' h => ?_, fun h => ?_⟩
  · have h' : RefNuTStep X { s with now := s.now + 1000 } (.fire t c e) s' := h
    obtain ⟨-, -, -, hnow, hst⟩ := refNuTStepK_fire_inv h'
    exact ⟨{ s with now := s.now + 1000 }, rfl, rfl, hnow, hst⟩
  · have hstep : time012nu_fireAdvancesClock time012nu_X (time012nu_s time012nu_MA)
        (.fire time012nu_r none time012nu_eR) _ :=
      time012nu_stepAt refNuKeep { time012nu_s time012nu_MA with now := 1010 } time012nu_r
        time012nu_eR (by simp [time012nu_X]) rfl (by decide) ⟨.action 0, rfl⟩ (by decide)
    have e := h _ _ _ _ _ _ hstep
    exact absurd e (by decide)

/-- ✗ A label without the chosen name is a gap of the statement, closed by the frame
`time012nu_FramesMid`: the statement reads the intermediate marking off the label, so a step
that takes the tokens of the chosen name but labels its firing with no name is judged on the
queue heads, and it satisfies the five lines. In the third worked example `J1` fires on name
`2` and leaves the token of name `1` at the head of place `0`, so `J2` can still join on name
`1`; the unnamed step reads the intermediate marking as if `J1` had taken that head and
restarts `J2` at `10`, where the reference keeps its stamp `0`. The frame catches it: after the
firing place `0` holds name `1` first, not name `2`. -/
theorem TIME_012_nu_gap_unnamedLabel :
    TIME_012_nu (time012nu_unnamed (N := Nat) (V := Nat) (Nm := Nat)) ∧
      ¬ time012nu_FramesMid (time012nu_unnamed (N := Nat) (V := Nat) (Nm := Nat)) ∧
      time012nu_unnamed time012nu_X2 (time012nu_s time012nu_MC) (.fire time012nu_J1 none [])
        { M := time012nu_MC1, now := 10,
          stamp := nuRestamp refNuKeep time012nu_X2 (time012nu_s time012nu_MC) time012nu_J1
            none [] time012nu_MC1 } ∧
      nuRestamp refNuKeep time012nu_X2 (time012nu_s time012nu_MC) time012nu_J1 none []
        time012nu_MC1 "J2" = some 10 ∧
      (time012nu_afterJ1 refNuKeep).stamp "J2" = some 0 := by
  have hstep : time012nu_unnamed time012nu_X2 (time012nu_s time012nu_MC)
      (.fire time012nu_J1 none [])
      { M := time012nu_MC1, now := 10,
        stamp := nuRestamp refNuKeep time012nu_X2 (time012nu_s time012nu_MC) time012nu_J1
          none [] time012nu_MC1 } :=
    time012nu_unnamed.fire _ _ _ (some 2) _ [] _ (by simp [time012nu_X2]) time012nu_fireJ1
      (by decide) (by simp [time012nu_X2, Timing.earliest])
  refine ⟨time012nu_ofRel _ refNuKeep refNuKeep_mid refNuKeep_keeps refNuKeep_fired
    refNuKeep_after refNuKeep_armed
    fun X s t c e s' h => ?_, fun h => ?_, hstep, by decide, by decide⟩
  · obtain ⟨rfl, hnow, hst⟩ := time012nu_unnamed_inv h
    exact ⟨s, rfl, rfl, hnow, hst⟩
  · have e := congrFun (h _ _ _ _ _ _ hstep) 0
    exact absurd e (by decide)

end Libpetri.Spec
