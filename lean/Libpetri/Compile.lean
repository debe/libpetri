/-
# The compiled consume program of `PrecompiledNet`

Models `rust/libpetri-runtime/src/precompiled_net.rs` `compile_consume_ops`
(all input specs in declaration order, then all reset arcs in declaration
order — the `reset_ops_start` boundary is where read arcs peek, per
EXEC-012/EXEC-013) and the untimed, non-ν fragment of
`precompiled_backend.rs` `can_enable` (bitmap presence phase +
`CompiledNet::cardinality_check`).

FR4 (opcode-stream well-formedness) is *structural* here: `ConsumeOp` is the
decoded instruction, `compileConsumeOps` is its only producer, and the
inputs-before-resets shape is the definition. The `u32` encoding and the `pc`
walk are cited but not modelled — decode is language-local and every
differential test exercises it.
-/
import Libpetri.Basic
import Libpetri.Ring

namespace Libpetri

/-- One decoded consume opcode (`precompiled_net.rs:14-18`, spec CONC-021):
`CONSUME_ONE`, `CONSUME_N`, `CONSUME_ALL`, `CONSUME_ATLEAST`, `RESET`.
The `atLeast` minimum operand is carried by the encoding but *skipped* at run
time (`precompiled_backend.rs` — `if opcode == CONSUME_ATLEAST { pc += 1 }`);
it participates only in enablement. -/
inductive ConsumeOp where
  | one (p : PlaceId)
  | n (p : PlaceId) (k : Nat)
  | all (p : PlaceId)
  | atLeast (p : PlaceId) (min : Nat)
  | reset (p : PlaceId)
  deriving DecidableEq, Repr

/-- The input-spec half of `compile_consume_ops` (`precompiled_net.rs:357-379`). -/
def opOfSpec (sp : InSpec) : ConsumeOp :=
  match sp.card with
  | .one => .one sp.place
  | .exactly k => .n sp.place k
  | .all => .all sp.place
  | .atLeast m => .atLeast sp.place m

/-- `compile_consume_ops` (`precompiled_net.rs:354-389`): all input specs in
declaration order, then all reset arcs in declaration order. The boundary
between the two halves is the shipped `reset_ops_start`. -/
def compileConsumeOps (t : Transition) : List ConsumeOp :=
  t.inputs.map opOfSpec ++ t.resets.map .reset

/-- IO-007's `consumptionCount(available)` column, as the opcode interpreter
realises it (the `to_consume` match of `consume_for_firing`): `One`/`Exactly`
consume their required count, `All`/`AtLeast` drain everything available. -/
def consumeCountAt (avail : Nat) : Card → Nat
  | .one => 1
  | .exactly k => k
  | .all => avail
  | .atLeast _ => avail

/-- `consumeCountAt` agrees with the `consumesAll`/`required` formulation
(`Basic.lean`'s guard-free `consumeCount`). -/
theorem consumeCountAt_eq (avail : Nat) (c : Card) :
    consumeCountAt avail c = if c.consumesAll then avail else c.required := by
  cases c <;> rfl

/-- Untimed, non-ν enablement over the pool: the sparse-mask presence phase
(`precompiled_net.rs` `can_enable_bitmap` — every input and read place
occupied, every inhibitor place empty; reset places gate nothing, CORE-034)
plus `CompiledNet::cardinality_check` (`compiled_net.rs` — each spec's
`required_count` individually against `token_counts`). Models
`precompiled_backend.rs` `can_enable`, minus timing and the ν-match clause
(deferred to the ν phase). -/
def canEnable (s : Pool) (t : Transition) : Bool :=
  t.inputs.all (fun sp =>
    decide (0 < s.cnt sp.place) && decide (sp.card.required ≤ s.cnt sp.place))
    && t.reads.all (fun p => decide (0 < s.cnt p))
    && t.inhibitors.all (fun p => s.cnt p == 0)

/-- Fix (c)'s compile-time guarantee (`compiled_net.rs` duplicate-input-place
rejection, CORE-030 AC3): a compilable transition satisfies
`InputsDistinctPlaces`, and additionally every input place is distinct as a
raw list — the form the consume-program induction consumes. -/
def DistinctInputPlaces (t : Transition) : Prop :=
  (t.inputs.map (·.place)).Pairwise (· ≠ ·)

/-- Every place a transition references is a real (compiled) place id. In the
shipped code this holds by construction — `CompiledNet::compile` interns every
referenced place name into `place_index` — so it is a standing hypothesis
here, not a proof obligation. -/
structure PlacesInBounds (t : Transition) (n : Nat) : Prop where
  inputs : ∀ sp ∈ t.inputs, sp.place < n
  reads : ∀ p ∈ t.reads, p < n
  inhibitors : ∀ p ∈ t.inhibitors, p < n
  resets : ∀ p ∈ t.resets, p < n

end Libpetri
