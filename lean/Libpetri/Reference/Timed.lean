import Libpetri.Reference.Semantics
import Libpetri.Novel.TimedScg.Timing
import Libpetri.Spec.Registry

set_option linter.missingDocs true

/-!
# The timed reference step ([TIME-010] – [TIME-013], Phase 1)

Written from the spec, not from any implementation. The untimed reference semantics
(`Semantics.lean`, `Fires`) says which firings exist; this file adds the clock that decides
which of them the executor may take, one atomic step at a time:

* a **timed net** (`TimedNet`) is a net with a `Timing` per transition
  (`Novel.TimedScg.Timing`, milliseconds) and the deadline tolerance;
* a **state** (`TSt`) is the marking, the current reading of the firing clock and one stamp per
  transition name (`none`: holds no clock). A transition is **armed** when it is enabled and
  holds a stamp ([TIME-010], glossary: Armed), **reaped** when it is enabled and holds none;
* a **step** (`TLbl`) is a delay of the clock, a firing or a reap.

`RefTStepW P` is the step relation for a policy `P`, which fixes the four timing decisions: which
armed transitions keep their stamp across a firing, which are (newly or again) armed after it,
when a transition is expired, and the earliest-bound gate, plus the reading a fresh stamp takes.
`RefTStep` is `RefTStepW refPolicy`, the reading of the spec, and is registered as a witness
model. The other policies of the requirement blocks are mutants: each changes one decision.

`refPolicy` reads the spec as follows.

* **keep** ([TIME-012]): an armed transition other than the fired one keeps its stamp when it
  is enabled both in the intermediate marking (`mid`, the marking after consumption and resets,
  before any deposit) and after the firing.
* **re-arm** ([TIME-010], [TIME-012], [TIME-013]): a transition that did not keep its stamp is
  armed with a fresh stamp when it is enabled after the firing and either was armed before (its
  clock restarts) or the firing wrote one of its arc places (`writes`: consumed from, drained
  or deposited into; ruling D6). A reaped transition whose arc places the firing does not write
  stays unarmed.
* **expired** ([TIME-013]): a reapable timing (`Deadline` / `Window`), armed, with elapsed time
  strictly greater than its latest bound plus the tolerance.
* **gate** ([TIME-010]): elapsed time at least the earliest bound.

The step is atomic: one firing completes in the step that starts it, there is no priority and
no eagerness, and a delay may pass any bound (the executor may be late). It states only safety,
and is grown into a full executor in a later phase. A firing pass of several firings
([EXEC-003]) is outside Phase 1. For clocks a sequence of atomic steps agrees with it: each step
computes its intermediate marking from the live marking it fires from, so a token deposited
earlier in the same pass counts, as [TIME-012] says. It does not model the pass's enablement
recheck, which does not count such a token ([EXEC-003] AC3-AC5), so only a pass of one firing is
a single step of this relation, and the Phase 2 executor is tied back to it on such passes alone.

`refTStep_projects`: every timed firing is a reference firing (`Fires`) with the same marking
effect.
-/

namespace Libpetri.Reference

open Libpetri Libpetri.Novel.Seam
open Libpetri.Novel.TimedScg (Timing)

variable {N : Type}

/-- A timed net: the untimed net, a timing per transition and the deadline tolerance in
milliseconds ([TIME-013]). -/
structure TimedNet (N : Type) where
  /-- The untimed net. -/
  net    : Net N
  /-- The timing of each transition ([TIME-001]). -/
  timing : Trans N → Timing
  /-- The deadline tolerance ([TIME-013]). -/
  tol    : Nat

/-- Executor state: the marking, the current reading of the firing clock, and the stamp of each
transition by name ([TIME-010]; `none`: no clock). -/
structure TSt (N : Type) where
  /-- The marking, as token counts. -/
  m     : N → Nat
  /-- The current reading of the firing clock. -/
  now   : Nat
  /-- The stamp by transition name. -/
  stamp : String → Option Nat

/-- A step of the timed executor: the clock advances by `δ`, a transition fires with deposit
`d`, or a transition is reaped. -/
inductive TLbl (N : Type) where
  /-- The firing clock advances by `δ`. -/
  | delay (δ : Nat)
  /-- Transition `t` fires and deposits `d`. -/
  | fire (t : Trans N) (d : List N)
  /-- Transition `t` is reaped. -/
  | reap (t : Trans N)

namespace TSt

/-- `t` is armed: enabled at the marking and holding a stamp. -/
def armed (s : TSt N) (t : Trans N) : Bool :=
  enabledNA s.m t.core && (s.stamp t.core.name).isSome

/-- The elapsed time of `t`: the clock reading minus its stamp (0 without a stamp). -/
def elapsed (s : TSt N) (t : Trans N) : Nat :=
  s.now - (s.stamp t.core.name).getD s.now

/-- The initial state from marking `m0` at clock reading `now0`: every transition of the net
enabled at `m0` is stamped `now0`, every other name holds no stamp ([TIME-010], "newly armed
when it is enabled in the initial marking"). -/
def init (X : TimedNet N) (m0 : N → Nat) (now0 : Nat) : TSt N :=
  { m := m0, now := now0,
    stamp := fun n => match X.net.transitions.find? (·.core.name == n) with
      | some u => if enabledNA m0 u.core then some now0 else none
      | none => none }

end TSt

/-- `t` is expired: its timing is reapable, it is armed, and its elapsed time is strictly
greater than its latest bound plus the tolerance ([TIME-013]). -/
def tExpired (X : TimedNet N) (s : TSt N) (t : Trans N) : Bool :=
  (X.timing t).reapable && s.armed t && decide ((X.timing t).latest + X.tol < s.elapsed t)

/-- The intermediate marking of a firing of `t` from `m` ([TIME-012]): consumption and resets
applied, nothing deposited. -/
def mid [DecidableEq N] (t : Trans N) (m : N → Nat) : N → Nat := fireNC m t.core (fun _ => 0)

/-- The arc places of `u`: its input, inhibitor, read and reset places. -/
def arcPlaces (u : Trans N) : List N :=
  u.core.inputs.map (·.place) ++ u.core.inhibitors ++ u.core.reads ++ u.core.resets

/-- The firing of `t` with deposit `d` writes `p`: `t` has an input arc on `p` (it consumes
from it), a reset arc on `p` (it drains it, even when empty), or deposits into `p`. -/
def writes [DecidableEq N] (t : Trans N) (d : List N) (p : N) : Bool :=
  decide (p ∈ t.core.inputs.map (·.place)) || decide (p ∈ t.core.resets) || decide (p ∈ d)

/-- The firing of `t` with deposit `d` writes one of `u`'s arc places. -/
def writesArc [DecidableEq N] (t : Trans N) (d : List N) (u : Trans N) : Bool :=
  (arcPlaces u).any (writes t d)

/-- The four timing decisions of the timed step, and the reading a fresh stamp takes. In `keep`
and `rearm` the arguments are the net, the state before the firing, the fired transition, its
deposit, the marking after it, and the transition whose stamp is decided. -/
structure Policy (N : Type) where
  /-- `u` keeps its stamp across the firing. -/
  keep    : TimedNet N → TSt N → Trans N → List N → (N → Nat) → Trans N → Bool
  /-- `u`, not keeping its stamp, is armed with a fresh one after the firing. -/
  rearm   : TimedNet N → TSt N → Trans N → List N → (N → Nat) → Trans N → Bool
  /-- `t` is expired: it may be reaped, and may not fire. -/
  expired : TimedNet N → TSt N → Trans N → Bool
  /-- `t` has passed its earliest bound. -/
  gate    : TimedNet N → TSt N → Trans N → Bool
  /-- The reading a fresh stamp takes, given the state before the firing. -/
  fresh   : TSt N → Nat

/-- The stamp `u` holds after `t` fires from `s` with deposit `d` to marking `m'`, under
policy `P`. -/
def restampW (P : Policy N) (X : TimedNet N) (s : TSt N) (t : Trans N) (d : List N)
    (m' : N → Nat) (u : Trans N) : Option Nat :=
  if P.keep X s t d m' u then s.stamp u.core.name
  else if P.rearm X s t d m' u then some (P.fresh s)
  else none

/-- The stamps after `t` fires: each name of the net gets `restampW` of the net's transition of
that name, every other name none. -/
def restampAll (P : Policy N) (X : TimedNet N) (s : TSt N) (t : Trans N) (d : List N)
    (m' : N → Nat) : String → Option Nat :=
  fun n => match X.net.transitions.find? (·.core.name == n) with
    | some u => restampW P X s t d m' u
    | none => none

/-- **The timed step for policy `P`.** -/
inductive RefTStepW [DecidableEq N] (P : Policy N) :
    TimedNet N → TSt N → TLbl N → TSt N → Prop
  /-- The clock advances; the marking and every stamp stay. -/
  | delay (X : TimedNet N) (s : TSt N) (δ : Nat) :
      RefTStepW P X s (.delay δ) { s with now := s.now + δ }
  /-- An expired transition of the net loses its stamp; nothing else changes. -/
  | reap (X : TimedNet N) (s : TSt N) (t : Trans N) (ht : t ∈ X.net.transitions)
      (hx : P.expired X s t = true) :
      RefTStepW P X s (.reap t)
        { s with stamp := fun n => if n = t.core.name then none else s.stamp n }
  /-- An armed transition of the net past its gate and not expired fires as the reference
  semantics says; the stamps are recomputed. -/
  | fire (X : TimedNet N) (s : TSt N) (t : Trans N) (d : List N) (m' : N → Nat)
      (ht : t ∈ X.net.transitions) (hf : Fires t s.m d m') (ha : s.armed t = true)
      (hg : P.gate X s t = true) (hx : P.expired X s t = false) :
      RefTStepW P X s (.fire t d) { m := m', now := s.now, stamp := restampAll P X s t d m' }

/-- The spec's policy (see the module docstring). -/
def refPolicy [DecidableEq N] : Policy N where
  keep _ s t _ m' u := s.armed u && u.core.name != t.core.name &&
    enabledNA (mid t s.m) u.core && enabledNA m' u.core
  rearm _ s t d m' u := enabledNA m' u.core && (s.armed u || writesArc t d u)
  expired := tExpired
  gate X s t := decide ((X.timing t).earliest ≤ s.elapsed t)
  fresh s := s.now

/-- **The timed reference step** (witness model): `RefTStepW refPolicy`. -/
def RefTStep [DecidableEq N] : TimedNet N → TSt N → TLbl N → TSt N → Prop :=
  RefTStepW refPolicy

#spec_witness RefTStep

/-- Every timed firing, under any policy, is a reference firing with the same marking
effect. -/
theorem refTStepW_fire_fires [DecidableEq N] {P : Policy N} {X : TimedNet N} {s s' : TSt N}
    {t : Trans N} {d : List N} (h : RefTStepW P X s (.fire t d) s') : Fires t s.m d s'.m := by
  cases h
  assumption

/-- A delay or a reap leaves the marking as it is. -/
theorem refTStepW_marking [DecidableEq N] {P : Policy N} {X : TimedNet N} {s s' : TSt N}
    {l : TLbl N} (h : RefTStepW P X s l s') (hl : ∀ t d, l ≠ .fire t d) : s'.m = s.m := by
  cases h with
  | delay => rfl
  | reap => rfl
  | fire => exact absurd rfl (hl _ _)

/-- **Projection onto the untimed reference**: every firing step of `RefTStep` is a step of
`Fires`, from the step's marking to its successor's. -/
theorem refTStep_projects [DecidableEq N] {X : TimedNet N} {s s' : TSt N} {t : Trans N}
    {d : List N} (h : RefTStep X s (.fire t d) s') : Fires t s.m d s'.m :=
  refTStepW_fire_fires h

/-- A `RefTStep` firing of a net's transition is a labelled step of the untimed net. -/
theorem refTStep_lstep [DecidableEq N] {X : TimedNet N} {s s' : TSt N} {t : Trans N}
    {d : List N} (h : RefTStep X s (.fire t d) s') : LStep X.net t.core.name s.m s'.m := by
  have hf := refTStep_projects h
  cases h
  exact ⟨t, by assumption, rfl, d, hf⟩

end Libpetri.Reference
