/-
# Retrodictions: the four Bitmap/Precompiled divergences

Machine-checked minimal witnesses for the four real divergences between
`PrecompiledBackend` and the `BitmapBackend` reference found (and fixed) in
the backend-refinement work. The **pre-fix** code is commit `1bdf586`
(`rust/libpetri-runtime/src/precompiled_backend.rs` at that revision); each
section keeps a local model of the pre-fix behavior and exhibits an input on
which it observably diverges from the reference semantics the rest of this
development proves the post-fix code equal to. None of the four was reachable
by the shipped differential suite (no timed nets, no read+reset overlap, no
duplicate inputs, no unknown-place tokens) — which is the coverage lesson.

* (a) `tid_order_diverges` — pre-fix `collect_ready_general` drained each
  priority level in ascending **tid** order; EXEC-002 demands enablement-time
  order. Fixed by the in-place `(enabled_at, tid)` sort (fix (a)).
* (b) `read_reset_order_diverges` — pre-fix `consume_for_firing` peeked read
  arcs **after** the RESET tail; a `read(p)+reset(p)` transition observed an
  empty place. Fixed by peeking at the `reset_ops_start` boundary (fix (b)).
* (c) `canEnable_insufficient_for_totality` — with duplicate input arcs on
  one place, `cardinality_check` passes each spec individually, yet the
  second `ring_remove_first` finds the head slot already empty (`None` —
  the shipped `.unwrap()` panics). Fixed by rejecting duplicate input places
  at compile time (fix (c), CORE-030 AC3).
* (d) `unknown_place_drop` — pre-fix `produce_token` was a no-op for places
  the program does not know: producing was the *identity* on the pool, i.e.
  a lost token, violating conservation. Fixed by the `extra_marking`
  side-map (fix (d), CORE-072 AC3).
-/
import Libpetri.Conservation
import Libpetri.Sched

namespace Libpetri

instance (K : SchedKey) : DecidableRel K.lt := fun a b => by
  unfold SchedKey.lt
  infer_instance

/-! ## (a) Ready order within a priority level -/

/-- Two same-priority transitions; tid 1 became enabled at 3, tid 0 later at
5 (declaration order opposite to enablement order — the staggered case the
suite never built). -/
def Ka : SchedKey :=
  { prio := fun _ => 0
    clock := fun tid => if tid = 0 then 5 else 3 }

/-- The pre-fix per-level drain order was ascending tid — `[0, 1]` — which is
*not* canonically sorted (tid 1 enabled first must fire first); `[1, 0]` is.
With `eq_of_perm_of_sorted`, the post-fix output (`LevelBlocks` shape) is
forced to `[1, 0]`, so the pre-fix output provably differs from every
correct one. -/
theorem tid_order_diverges :
    ¬ ([0, 1].Pairwise Ka.lt) ∧ ([1, 0].Pairwise Ka.lt) := by
  constructor
  · intro h
    rw [List.pairwise_cons] at h
    have := h.1 1 (by simp)
    unfold SchedKey.lt Ka at this
    rcases this with h' | ⟨_, h' | ⟨h', _⟩⟩ <;> simp at h' <;> omega
  · rw [List.pairwise_cons]
    refine ⟨fun tid hm => ?_, by simp⟩
    have : tid = 0 := by simpa using hm
    subst this
    unfold SchedKey.lt Ka
    right
    exact ⟨rfl, Or.inl (by simp)⟩

/-! ## (b) Read-vs-reset ordering — a shared demo pool

Two places: place 0 (block `[0,4)`) holds one token `9`, place 1 (block
`[4,8)`) holds one token `7`. -/

def demoPool : Pool :=
  { pool := fun idx => if idx = 0 then some 9 else if idx = 4 then some 7 else none
    len := 8
    offset := fun p => if p = 0 then 0 else 4
    head := fun _ => 0
    tail := fun _ => 1
    cnt := fun _ => 1
    cap := fun _ => 4
    nplaces := 2 }

/-- `read(1)` and `reset(1)` on one transition, plus a trigger input. -/
def tReadReset : Transition :=
  { name := "t"
    inputs := [{ place := 0, card := .one, guard := none }]
    inhibitors := []
    reads := [1]
    resets := [1] }

/-- The pre-fix read loop (commit `1bdf586`,
`precompiled_backend.rs:1046-1055`): peek *after* the whole consume program,
resets included. -/
def preFixReads (s : Pool) (t : Transition) : TokenBag :=
  peekReads
    (execOpsFrom (execOpsFrom ⟨s, emptyBag, emptyBag⟩ (t.inputs.map opOfSpec))
      (t.resets.map .reset)).pool
    t.reads

/-- Pre-fix, the read observes the already-drained place (the shipped
executor then failed the firing: `ctx.read()` had nothing to deliver);
post-fix (`consumeForFiring`, the `reset_ops_start` boundary) it observes the
pre-reset front token `7`, as the reference always did. -/
theorem read_reset_order_diverges :
    preFixReads demoPool tReadReset 1 = []
      ∧ (consumeForFiring demoPool tReadReset).2 1 = [7] := by
  constructor <;> rfl

/-! ## (c) Duplicate input arcs on one place -/

/-- Two `one()` input arcs on place 0. -/
def tDup : Transition :=
  { name := "t"
    inputs := [{ place := 0, card := .one, guard := none },
               { place := 0, card := .one, guard := none }]
    inhibitors := []
    reads := []
    resets := [] }

/-- `can_enable` passes (each spec's requirement is checked individually
against the same single token), yet after the first `CONSUME_ONE` the head
slot is `None` — exactly the value the second op's
`ring_remove_first().unwrap()` (pre-fix `precompiled_backend.rs:307`)
panicked on. Post-fix this net is rejected at compile time: it violates
`DistinctInputPlaces` (CORE-030 AC3), the hypothesis every consumption
theorem in this development carries. -/
theorem canEnable_insufficient_for_totality :
    canEnable demoPool tDup = true
      ∧ (execOpsFrom ⟨demoPool, emptyBag, emptyBag⟩ [.one 0]).pool.first 0 = none
      ∧ ¬ DistinctInputPlaces tDup := by
  refine ⟨by decide, by rfl, ?_⟩
  intro h
  unfold DistinctInputPlaces tDup at h
  simp [List.pairwise_cons] at h

/-! ## (d) Unknown-place token drop -/

/-- Pre-fix `produce_token` (commit `1bdf586`,
`precompiled_backend.rs:1039-1046`): `if let Some(pid) = place_id(place)`
with **no else branch** — for a place the program does not know, nothing
happens. -/
def preFixProduce (s : Pool) (p : PlaceId) (c : Colour) : Pool :=
  if p < s.nplaces then s.addLast p c else s

/-- Producing to an unknown place was the *identity*: the token is gone
without trace, violating `token_conservation`'s balance the moment the
executor's `TokenAdded` event (emitted regardless) is counted. The reference
kept the token in its `Marking`; post-fix the precompiled backend retains it
in the `extra_marking` side-map merged into `materialize_marking`
(CORE-072 AC3). -/
theorem unknown_place_drop :
    preFixProduce demoPool 9 42 = demoPool := rfl

end Libpetri
