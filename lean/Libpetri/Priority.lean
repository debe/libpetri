/-
# Conflict-only priority pruning — and why the `willFire` guard is load-bearing

Models `rust/libpetri-verification/src/priority_semantics.rs`
`PrioritySemantics::Conflict`, restricted to the untimed fragment.

`Conflict` *removes* transitions from the analysed relation, so unlike every
other part of the encoding it can only ever lose behaviour. Paper A's step 4
("priority abstraction") states that priorities are **not** encoded, so
Theorem 2 does not cover this mode at all — the shipped soundness argument lives
only in the doc comment on the enum.

Commit `c23cd9e` (NU-052) added the fourth condition: `H` must *actually fire*
in this class, because a name-disabled ν join produces no name-successor and so
must not pre-empt a conflicting drain. `preFixPrune` below is the condition as
it stood before that commit; `postFixPrune` is the shipped one.
`willFire_guard_is_necessary` is the concrete configuration separating them.

The fix round of 2026-09-30 ([VER-004]) added a fifth: `H` pre-empts nothing
while an earlier firing of it is in flight (`inflight:<H>` marked on the split
net, `priority_dominated`'s `marking.count(in_flight_place(h)) == 0`), since
the Java and TypeScript executors do not start `H` again then, and `L` fires.
`preInFlightPrune` is the condition between the two fixes;
`inFlight_guard_is_necessary` separates it from the shipped one. The verifier
also splits every pruner and every depositor into a pruner's input or read
places (`in_flight::conflict_demand`), and turns `Conflict` off when one of them
cannot be split; that side is described in `Novel/InFlight.lean` and not
modelled here.
-/
import Libpetri.Basic

namespace Libpetri

/-- A transition together with the ν name-layer verdict the base marking cannot
see. `nameEnabled = false` models a join that is base-enabled — its input places
hold tokens — but whose correlated names do not match, so it cannot fire
(`name_state_class_graph.rs:601`, the `will_fire` guard). `inFlight = true`
models a marked `inflight:<t>` on the split net: an earlier firing of the
transition has started and its action has not completed. -/
structure NuTransition where
  base        : Transition
  nameEnabled : Bool
  inFlight    : Bool := false

/-- Demand on `p` from consumed input arcs only. Read and inhibitor arcs
deliberately do not count (`priority_semantics.rs:32`). -/
def demand (t : Transition) (p : PlaceId) : Nat := pre t p

/-- Real competition: some consumed place cannot satisfy both demands at once
(`priority_semantics.rs:31-32`). -/
def competes (places : List PlaceId) (m : AMarking) (H L : Transition) : Bool :=
  places.any fun p =>
    0 < demand H p && 0 < demand L p && m p < demand H p + demand L p

/-- **Pre-`c23cd9e`.** Prune `L` when some strictly-higher-priority `H` is
*base*-enabled and competes. Blind to the name layer. -/
def preFixPrune (places : List PlaceId) (m : AMarking)
    (cands : List NuTransition) (L : NuTransition) : Bool :=
  cands.any fun H =>
    enabledA m H.base && decide (L.base.priority < H.base.priority)
      && competes places m H.base L.base

/-- **Between `c23cd9e` and the in-flight guard.** Prune `L` when some
strictly-higher-priority `H` is base-enabled, will fire, and competes. -/
def preInFlightPrune (places : List PlaceId) (m : AMarking)
    (cands : List NuTransition) (L : NuTransition) : Bool :=
  cands.any fun H =>
    enabledA m H.base && H.nameEnabled && decide (L.base.priority < H.base.priority)
      && competes places m H.base L.base

/-- **Shipped.** Same, plus: `H` must actually fire in this class, and no earlier
firing of `H` is in flight (`priority_dominated`, `name_state_class_graph.rs:574`). -/
def postFixPrune (places : List PlaceId) (m : AMarking)
    (cands : List NuTransition) (L : NuTransition) : Bool :=
  cands.any fun H =>
    enabledA m H.base && H.nameEnabled && !H.inFlight
      && decide (L.base.priority < H.base.priority) && competes places m H.base L.base

/-- What the executor really does: it fires `L` when `L` is enabled at both the
base and name layers and nothing that *actually fires* out-competes it. An `H`
in flight does not start again on the Java and TypeScript executors, so it
out-competes nothing there; the Rust executor may start it again ([CONC-002]),
which makes this a superset of the Rust's firings (the prune keeps more). -/
def executorFires (places : List PlaceId) (m : AMarking)
    (cands : List NuTransition) (L : NuTransition) : Bool :=
  enabledA m L.base && L.nameEnabled && !postFixPrune places m cands L

/-- The shipped prune never contradicts the executor: if it drops `L`, the
executor was not going to fire `L` either. Trivial by construction — which is
the point, the shipped condition is exactly the executor's rule. -/
theorem postFixPrune_agrees_with_executor
    (places : List PlaceId) (m : AMarking) (cands : List NuTransition) (L : NuTransition) :
    postFixPrune places m cands L = true → executorFires places m cands L = false := by
  intro h
  unfold executorFires
  simp [h]

/-! ## The `c23cd9e` configuration

Place 0 holds a single coloured token. Two consumers compete for it:

* `join` — priority 10, a ν join whose correlated name does not match, so it is
  base-enabled but cannot fire;
* `drain` — priority 0, the orphan drain, which can fire.
-/

section WillFire

def pJoin : Transition :=
  { name := "join", inputs := [{ place := 0, card := .one, guard := none }]
  , inhibitors := [], reads := [], resets := [], priority := 10 }

def pDrain : Transition :=
  { name := "drain", inputs := [{ place := 0, card := .one, guard := none }]
  , inhibitors := [], reads := [], resets := [], priority := 0 }

/-- The join is base-enabled but name-disabled. -/
def joinNu : NuTransition := { base := pJoin, nameEnabled := false }
def drainNu : NuTransition := { base := pDrain, nameEnabled := true }

/-- One token in place 0 — not enough for both consumers. -/
def mOne : AMarking := fun p => if p == 0 then 1 else 0

def placesOne : List PlaceId := [0]
def candsOne : List NuTransition := [joinNu, drainNu]

/-- The two really do compete for the single token. -/
theorem join_and_drain_compete : competes placesOne mOne pJoin pDrain = true := by decide

/-- **Retrodiction of `c23cd9e`.** The pre-fix condition prunes the drain, the
shipped condition does not, and the executor does fire the drain.

Pruning the drain is exactly the reported symptom: the orphan token is never
consumed in the analysis, so the analyser reports a stall the executor cannot
produce — and, in the other direction, a genuinely reachable post-drain state is
dropped from the explored set. -/
theorem willFire_guard_is_necessary :
    preFixPrune placesOne mOne candsOne drainNu = true
    ∧ postFixPrune placesOne mOne candsOne drainNu = false
    ∧ executorFires placesOne mOne candsOne drainNu = true := by
  refine ⟨by decide, by decide, by decide⟩

end WillFire

/-! ## The in-flight guard (2026-09-30)

The Java/TypeScript witness of the fix round: `H : c → ok` at priority 10 with
a 100 ms action, `L : c → bad` at priority 0, and `g : s, inhibitor c → c`.
`H` starts and consumes `c`; `g` refills `c` while `H`'s action runs. Now `H`
is base-enabled and competes with `L` for the one token, but it is in flight:
Java and TypeScript do not start it again, so `L` fires and marks `bad`.
-/

section InFlightGuard

def hSplit : Transition :=
  { name := "H", inputs := [{ place := 0, card := .one, guard := none }]
  , inhibitors := [], reads := [], resets := [], priority := 10 }

def lSplit : Transition :=
  { name := "L", inputs := [{ place := 0, card := .one, guard := none }]
  , inhibitors := [], reads := [], resets := [], priority := 0 }

/-- `H` is base-enabled on the refilled token and its earlier firing is in flight. -/
def hInFlight : NuTransition := { base := hSplit, nameEnabled := true, inFlight := true }
def lIdle : NuTransition := { base := lSplit, nameEnabled := true }

def candsSplit : List NuTransition := [hInFlight, lIdle]

/-- **The in-flight guard is needed.** The prune before the guard drops `L`, the
shipped prune keeps it, and an executor that does not start `H` again fires
`L`. -/
theorem inFlight_guard_is_necessary :
    preInFlightPrune placesOne mOne candsSplit lIdle = true
    ∧ postFixPrune placesOne mOne candsSplit lIdle = false
    ∧ executorFires placesOne mOne candsSplit lIdle = true := by
  refine ⟨by decide, by decide, by decide⟩

end InFlightGuard

end Libpetri
