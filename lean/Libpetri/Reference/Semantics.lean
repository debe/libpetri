import Libpetri.Novel.Seam.Bad
import Libpetri.Novel.ForwardDeposit

/-!
# The reference semantics: untimed firing on named count markings

Written from the spec, not from any implementation. A named net (`Net N`) is its declared places
and its transitions; a transition is a `Seam.NTransition` (input arcs with cardinality,
inhibitors, reads, resets, by name) together with an optional output spec (`Out N`).

**One firing** (`Fires t m d m'`) of `t` from the count marking `m`:

* **Enabled** ([CORE-022], [IO-005]): every input place holds at least `requiredCount`
  ([IO-001]–[IO-004], [IO-007]), every read place at least one token ([CORE-032]), every
  inhibitor place none ([CORE-031]). Reset arcs never gate ([CORE-034]).
  This is `Seam.enabledNA`.
* **Consumption** ([IO-007]): `One` takes 1, `Exactly(n)` takes `n`, `All` / `AtLeast` take every
  token (`consumptionCount(available) = available`). This is `Seam.nconsumed`.
* **Outcome** ([IO-013]–[IO-016]): the firing ends one of the ways its output spec offers
  (`deposit`, indexed by `ForwardDeposit.Choice`):
  - the action writes one branch of `Out.branches` — one token per claimed place, a `forward`
    claiming its `to` ([IO-015], [IO-016]); a transition with no output spec writes nothing;
  - or the executor's timeout fires, and the marking receives the first `Timeout` node's child
    and nothing else ([IO-013] AC5), where `forward(from, to)` deposits **one token in `to` per
    token the firing consumed from `from`** ([IO-014] AC2/AC4). From an `All` / `AtLeast` input
    that is the whole drained batch (transfer semantics): `consumed` is the firing's actual
    consumption, so no special case is needed.
* **Effect** ([CORE-034], [EXEC-013], [EXEC-020]): a reset place ends holding exactly what the
  firing deposited there; every other place loses what was consumed and gains what was
  deposited. This is `Seam.fireNC` with the deposit's counts (`Seam.depProd`).

The untimed semantics ignores priorities and timing ([VER-004]): every enabled transition may
fire, and every outcome is available. The properties are [VER-002]'s, read on count markings
(`Violates`). Quiescence is **reap-quiescence** ([VER-002], [TIME-013]): every enabled
transition is reapable (timing `Deadline` or `Window`), because a late executor reaps such a
transition and comes to rest with it enabled (`Novel/ReapAware.lean`, `rest_sound`). On a net
with no reapable transition it is the plain "no transition enabled" (`Quiescent`,
`reapQuiescent_iff_quiescent`). `Delayed`, `Exact` and `Immediate` timing are never reaped and
only restrict firing, so the untimed abstraction treats them as `Immediate`.

`ForwardDeposit.lean` states the same outcome rule over flat place ids; `Link.lean` proves this
file's step is its `StepCD` there, and the named `Seam.StepNC` here.
-/

namespace Libpetri.Reference

open Libpetri Libpetri.Novel.Seam

/-- An output spec by place name ([IO-010]–[IO-014]), n-ary `And` / `Xor` read as right-nested
binary nodes. -/
inductive Out (N : Type) where
  | place (p : N)
  | and (l r : Out N)
  | xor (l r : Out N)
  | timeout (c : Out N)
  | forward (src dst : N)
  deriving Repr, Inhabited

/-- A transition: its arcs, its output spec (`none` = no output spec), and whether its timing
is reapable ([TIME-013]: `Deadline` or `Window`). Timing plays no part in firing; `reapable` is
read only by quiescence. -/
structure Trans (N : Type) where
  core     : NTransition N
  out      : Option (Out N)
  reapable : Bool := false

/-- A named net: declared places and transitions. The declared places play no part in firing;
a place is a place of the net by use, and a marked name no arc touches is inert ([CORE-072]). -/
structure Net (N : Type) where
  places      : List N
  transitions : List (Trans N)

/-- The cross product of alternative lists: an `And` deposits one alternative of each child. -/
def cross {N : Type} (xs ys : List (List N)) : List (List N) :=
  xs.flatMap fun x => ys.map fun y => x ++ y

variable {N : Type}

/-- The branches an action may write ([IO-015], [IO-016]): one token per claimed place. -/
def Out.branches : Out N → List (List N)
  | .place p => [[p]]
  | .forward _ dst => [[dst]]
  | .and l r => cross l.branches r.branches
  | .xor l r => l.branches ++ r.branches
  | .timeout c => c.branches

/-- What a timeout child deposits ([IO-013] AC5, [IO-014]): a token per place, and per
`forward from to` one token in `to` per token consumed from `from`. -/
def Out.timeoutDeposits (consumed : N → Nat) : Out N → List (List N)
  | .place p => [[p]]
  | .forward src dst => [List.replicate (consumed src) dst]
  | .and l r => cross (l.timeoutDeposits consumed) (r.timeoutDeposits consumed)
  | .xor l r => l.timeoutDeposits consumed ++ r.timeoutDeposits consumed
  | .timeout c => c.timeoutDeposits consumed

/-- The first `Timeout` node's child, in pre-order. -/
def Out.findTimeout : Out N → Option (Out N)
  | .timeout c => some c
  | .and l r => l.findTimeout.or r.findTimeout
  | .xor l r => l.findTimeout.or r.findTimeout
  | _ => none

/-- **The deposit** of a firing that consumed `consumed p` from each `p` and ended with `ch`;
`none` for a way of ending the spec does not offer. -/
def deposit (consumed : N → Nat) : Option (Out N) → Novel.ForwardDeposit.Choice → Option (List N)
  | none, .action 0 => some []
  | none, _ => none
  | some o, .action i => o.branches[i]?
  | some o, .timedOut j => o.findTimeout.bind fun c => (c.timeoutDeposits consumed)[j]?

variable [DecidableEq N]

/-- **One firing**: `t` is enabled at `m`, ends with deposit `d`, and leaves `m'`. -/
def Fires (t : Trans N) (m : N → Nat) (d : List N) (m' : N → Nat) : Prop :=
  enabledNA m t.core = true ∧
    (∃ ch, deposit (nconsumed m t.core) t.out ch = some d) ∧
    m' = fireNC m t.core (depProd d)

/-- One step labelled with the fired transition's name. -/
def LStep (net : Net N) (l : String) (m m' : N → Nat) : Prop :=
  ∃ t ∈ net.transitions, t.core.name = l ∧ ∃ d, Fires t m d m'

/-- One step. -/
def Step (net : Net N) (m m' : N → Nat) : Prop := ∃ l, LStep net l m m'

/-- The reachable markings. -/
def Reach (net : Net N) (m0 : N → Nat) : (N → Nat) → Prop :=
  Relation.ReflTransGen (Step net) m0

/-- A firing sequence: the labels in order, from the first marking to the last. -/
inductive Run (net : Net N) : List String → (N → Nat) → (N → Nat) → Prop
  | nil (m : N → Nat) : Run net [] m m
  | cons {l : String} {ls : List String} {m m1 m2 : N → Nat} :
      LStep net l m m1 → Run net ls m1 m2 → Run net (l :: ls) m m2

/-- No transition is enabled ([EXEC-040]). -/
def Quiescent (net : Net N) (m : N → Nat) : Prop :=
  ∀ t ∈ net.transitions, enabledNA m t.core = false

/-- **Reap-quiescent** ([VER-002], [TIME-013]): every enabled transition is reapable. -/
def ReapQuiescent (net : Net N) (m : N → Nat) : Prop :=
  ∀ t ∈ net.transitions, enabledNA m t.core = true → t.reapable = true

omit [DecidableEq N] in
/-- Strict quiescence implies reap-quiescence. -/
theorem Quiescent.reap {net : Net N} {m : N → Nat} (h : Quiescent net m) :
    ReapQuiescent net m := by
  intro t ht hen
  rw [h t ht] at hen
  exact absurd hen Bool.false_ne_true

omit [DecidableEq N] in
/-- **No reapable transition, no change**: reap-quiescence is quiescence. -/
theorem reapQuiescent_iff_quiescent {net : Net N} (hnr : ∀ t ∈ net.transitions, t.reapable = false)
    (m : N → Nat) : ReapQuiescent net m ↔ Quiescent net m := by
  refine ⟨fun h t ht => ?_, Quiescent.reap⟩
  cases hen : enabledNA m t.core with
  | false => rfl
  | true =>
    have := h t ht hen
    rw [hnr t ht] at this
    exact absurd this Bool.false_ne_true

/-- A [VER-002] property. `mutualExclusion ps`: no two entries of `ps` are marked at once
(pairwise; `[p, q]` is `MutualExclusion(p1, p2)`). -/
inductive Property (N : Type) where
  | deadlockFree (sinks : List N)
  | terminatesAtSink (sinks : List N)
  | placeBound (p : N) (bound : Nat)
  | mutualExclusion (places : List N)
  | unreachable (places : List N)
  | quiescentCount (places : List N) (min : Nat) (max : Option Nat)

/-- **When a marking violates a property** ([VER-002]); "quiescent" is `ReapQuiescent`:
* `deadlockFree sinks`: quiescent, and some place of any name — declared, used, or inert —
  holds a token and is not a sink;
* `terminatesAtSink sinks`: quiescent, and no sink holds a token;
* `placeBound p k`: `p` holds more than `k`;
* `mutualExclusion ps`: two entries of `ps`, at different positions, marked — pairwise, so
  `[p, q]` is violated iff both are marked, and a place listed twice pairs with itself;
* `unreachable ps`: every listed place marked;
* `quiescentCount ps lo hi`: quiescent, and the total over `ps` is below `lo` or above `hi`. -/
def Violates (net : Net N) : Property N → (N → Nat) → Prop
  | .deadlockFree sinks, m => ReapQuiescent net m ∧ ∃ n, m n ≠ 0 ∧ n ∉ sinks
  | .terminatesAtSink sinks, m => ReapQuiescent net m ∧ ∀ s ∈ sinks, m s = 0
  | .placeBound p k, m => k < m p
  | .mutualExclusion ps, m => 2 ≤ (ps.filter (fun p => m p != 0)).length
  | .unreachable ps, m => ∀ p ∈ ps, m p ≠ 0
  | .quiescentCount ps lo hi, m =>
    ReapQuiescent net m ∧ ((ps.map m).sum < lo ∨ ∃ h, hi = some h ∧ h < (ps.map m).sum)

/-! ## Every enabled transition can fire, so quiescence is the absence of a step -/

omit [DecidableEq N] in
/-- Every output spec offers an action branch. -/
theorem branches_ne_nil : ∀ o : Out N, o.branches ≠ []
  | .place _ => by simp [Out.branches]
  | .forward _ _ => by simp [Out.branches]
  | .and l r => by
    have hl := branches_ne_nil l
    have hr := branches_ne_nil r
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hl
    obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hr
    exact List.ne_nil_of_mem (a := x ++ y)
      (List.mem_flatMap.mpr ⟨x, hx, List.mem_map.mpr ⟨y, hy, rfl⟩⟩)
  | .xor l r => by simp [Out.branches, branches_ne_nil l]
  | .timeout c => branches_ne_nil c

omit [DecidableEq N] in
theorem exists_deposit (c : N → Nat) (o : Option (Out N)) :
    ∃ ch d, deposit c o ch = some d := by
  cases o with
  | none => exact ⟨.action 0, [], rfl⟩
  | some o =>
    obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ (branches_ne_nil o)
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hd
    exact ⟨.action i, d, hi⟩

/-- **Quiescent iff no step.** -/
theorem quiescent_iff_no_step (net : Net N) (m : N → Nat) :
    Quiescent net m ↔ ∀ m', ¬ Step net m m' := by
  constructor
  · rintro hq m' ⟨l, t, ht, _, d, hen, _, _⟩
    rw [hq t ht] at hen
    exact Bool.false_ne_true hen
  · intro h t ht
    cases hen : enabledNA m t.core with
    | false => rfl
    | true =>
      obtain ⟨ch, d, hd⟩ := exists_deposit (nconsumed m t.core) t.out
      exact absurd ⟨t.core.name, t, ht, rfl, d, hen, ⟨ch, hd⟩, rfl⟩ (h _)

end Libpetri.Reference
