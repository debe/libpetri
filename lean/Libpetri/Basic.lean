/-
# Core model: concrete CTPN semantics and the verifier's untimed abstraction

Scope is the untimed fragment (see `lean/README.md`). Every definition below names
the exact shipped function it models; if that function changes, this file is wrong
and the fidelity note is the thing to check first.

Reference for the intended mathematics:
`theory/verification-preserving-neural-substitution.typ`, Definition 1 and
Proposition 1. That file is read-only here — nothing in `theory/` is edited by
this development.
-/

namespace Libpetri

/-- Place identity. The shipped code keys places by name (`Arc<str>`); the
flattener sorts and dedups those names into a dense index
(`net_flattener.rs:31-40`), which is what `PlaceId` models. -/
abbrev PlaceId := Nat

/-- A token's colour payload. `libpetri-core/src/token.rs` carries an arbitrary
`Arc<T>`; only guard-observable equality matters here, so `Nat` suffices. -/
abbrev Colour := Nat

/-- Concrete marking: a FIFO queue of coloured tokens per place.
Models `libpetri-runtime/src/marking.rs` (`HashMap<Arc<str>, VecDeque<ErasedToken>>`). -/
abbrev CMarking := PlaceId → List Colour

/-- Abstract marking: one token *count* per place. Models the `m_i` integer
variables of the CHC encoding (`encode`, `smt_encoder.rs:65-66`). -/
abbrev AMarking := PlaceId → Nat

/-- The colour-erasure abstraction `α(M)[p] = |M(p)|`
(`theory/verification-preserving-neural-substitution.typ`, "colour erasure"). -/
def alpha (m : CMarking) : AMarking := fun p => (m p).length

/-- A unary input-arc guard. Models `libpetri-core/src/input.rs`
`GuardFn = Arc<dyn Fn(&dyn Any) -> bool>`. -/
abbrev Guard := Colour → Bool

/-- Input cardinality. Models `libpetri-core/src/input.rs` `enum In`. -/
inductive Card where
  | one
  | exactly (n : Nat)
  | all
  | atLeast (n : Nat)
  deriving DecidableEq, Repr

/-- Models `libpetri-core/src/input.rs:83` `required_count`. -/
def Card.required : Card → Nat
  | .one => 1
  | .exactly n => n
  | .all => 1
  | .atLeast n => n

/-- The `matches!(spec, In::All { .. } | In::AtLeast { .. })` test that drives
`consume_all` in `net_flattener.rs:53`. -/
def Card.consumesAll : Card → Bool
  | .all => true
  | .atLeast _ => true
  | _ => false

/-- One input arc. -/
structure InSpec where
  place : PlaceId
  card  : Card
  guard : Option Guard

/-- A transition, already reduced to the untimed structural core: actions,
timing, priority-ordering and ν-correlation are out of scope for this file
(`priority` is used only in `Libpetri/Priority.lean`). -/
structure Transition where
  name       : String
  inputs     : List InSpec
  inhibitors : List PlaceId
  reads      : List PlaceId
  resets     : List PlaceId
  priority   : Int := 0

/-!
## Per-place projections

`net_flattener.rs:49-56` *sums* `required_count` over every input spec landing on
the same place. This development models **at most one input spec per place**,
which is the case every shipped fixture exercises; `specAt` is the projection
that assumption buys us. A net with two input arcs on one place is outside the
model — stated as `InputsDistinctPlaces` where it is needed.
-/

/-- The input spec on `p`, if any. -/
def specAt (t : Transition) (p : PlaceId) : Option InSpec :=
  t.inputs.find? (fun s => s.place == p)

/-- `pre[p]` of the flat transition (`net_flattener.rs:51-52`). -/
def pre (t : Transition) (p : PlaceId) : Nat :=
  match specAt t p with
  | none => 0
  | some s => s.card.required

/-- Whether `p` is in `consume_all` (`net_flattener.rs:53-55`). -/
def consumeAllAt (t : Transition) (p : PlaceId) : Bool :=
  match specAt t p with
  | none => false
  | some s => s.card.consumesAll

/-- `post[p]` for one flattened XOR branch: `net_flattener.rs:85-88` walks
`output::all_places` (a `HashSet`) and does `post[pid] += 1`, so every place in
the branch contributes exactly **one** token. -/
def post (br : List PlaceId) (p : PlaceId) : Nat :=
  if br.contains p then 1 else 0

/-!
## Concrete semantics

Models `bitmap_backend.rs:327 can_enable` (enablement) and
`bitmap_backend.rs:664 consume_for_firing` + `:815 produce_token` (effect).
-/

/-- Tokens at `s.place` satisfying `s`'s guard. Models the guard-matching
tally a draining arc computes inside `consume_for_firing`
(`bitmap_backend.rs:723-729`). That arm called `Marking::count_matching`
(`marking.rs`), which counts over the *whole* queue, until the EXEC-003 AC5
work replaced it with the same count bounded to the drainable prefix; the
bound is the scope note on `consumeCount` below. -/
def matchCount (m : CMarking) (s : InSpec) : Nat :=
  match s.guard with
  | none => (m s.place).length
  | some g => ((m s.place).filter g).length

/-- Tokens actually removed from `s.place` by one firing.

`consume_for_firing` (`bitmap_backend.rs:714-731`): `One => 1`,
`Exactly{n} => n`, and
`All`/`AtLeast` => the guard-matching count, i.e. **all guard-matching
tokens** — tokens failing the guard are left behind by `remove_matching`.

Written as a single branch on `consumesAll` rather than a four-way match: for
`One`/`Exactly` the consumed count coincides with `required_count`, so the two
forms agree pointwise.

**EXEC-003 AC5 scope.** The shipped draining arms count and remove within
`drainable(place, live)` — `live` minus the tokens a same-pass synchronous
action deposited — not within the whole queue. `drainable = live` on every
firing with no deposit outstanding at that place, which is the case this
definition models; `Conservation.lean`'s header states the exclusion once for
the whole consume model, and `Refinement.lean` records why the cycle-level
theorem is nevertheless untouched. `One`/`Exactly` are unaffected: they take a
fixed count off the FIFO head, which the AC4 gate already confined to the
pre-deposit prefix. -/
def consumeCount (m : CMarking) (s : InSpec) : Nat :=
  if s.card.consumesAll then matchCount m s else s.card.required

/-- Tokens removed from `p` by one firing. -/
def consumedAt (m : CMarking) (t : Transition) (p : PlaceId) : Nat :=
  match specAt t p with
  | none => 0
  | some s => consumeCount m s

/-- Concrete enablement (`can_enable`, `bitmap_backend.rs:327`, minus timing
and ν): every input arc has enough *matching* tokens, every inhibited place is
empty, every read place is non-empty. Reset arcs deliberately do not gate
(CORE-034).

This is the `pre_deposit = false` call — the one `update_enablement` makes.
The intra-pass `recheck_can_fire` passes `true`, which additionally discounts
the pass's `deposit_delta` from the counting checks (EXEC-003 AC4); that path
is idealized in `Refinement.lean`, not modelled here. -/
def enabledC (m : CMarking) (t : Transition) : Bool :=
  t.inputs.all (fun s => s.card.required ≤ matchCount m s)
    && t.inhibitors.all (fun p => (m p).length == 0)
    && t.reads.all (fun p => 1 ≤ (m p).length)

/-- The α-image of the concrete successor marking.

Stated at token-count granularity, which is all `α` observes: `remove_matching`
removes exactly `consumedAt` tokens, a reset arc drains the place
(`bitmap_backend.rs` reset handling), and the action's writes add `prod p`
tokens via `produce_token`.

`prod` is deliberately an arbitrary function: `executor_core/output.rs:37`
`validate_out_spec` checks only *which places* the action wrote to, never how
many tokens it wrote to each. Constraining it is `UnitOutput` below — and that
constraint turns out to be load-bearing. -/
def alphaFireC (m : CMarking) (t : Transition) (prod : PlaceId → Nat) : AMarking :=
  fun p =>
    if t.resets.contains p then prod p
    else (m p).length - consumedAt m t p + prod p

/-!
## Abstract semantics — the CHC encoding

Models `firing_conditions` (`smt_encoder.rs:151-209`) exactly.
-/

/-- Abstract enablement: `m_i >= pre[i]` (`firing_conditions`,
`smt_encoder.rs:160-165`), `m_i = 0` for inhibitors (`:167-170`), `m_i >= 1`
for reads (`:172-175`). -/
def enabledA (m : AMarking) (t : Transition) : Bool :=
  t.inputs.all (fun s => s.card.required ≤ m s.place)
    && t.inhibitors.all (fun p => m p == 0)
    && t.reads.all (fun p => 1 ≤ m p)

/-- The abstract fire relation (`firing_conditions`,
`smt_encoder.rs:177-201`):

* reset place      → `m'_i = post[i]`
* `consume_all` place → `m'_i = post[i]`
* otherwise        → `m'_i = m_i - pre[i] + post[i]`
-/
def fireA (m : AMarking) (t : Transition) (br : List PlaceId) : AMarking :=
  fun p =>
    if t.resets.contains p then post br p
    else if consumeAllAt t p then post br p
    else m p - pre t p + post br p

/-!
## Well-formedness hypotheses

Each of these is a side condition Proposition 1 needs and the shipped encoder
does not check. `Soundness.lean` proves the theorem under them and exhibits a
concrete counterexample for each, i.e. none is decorative.
-/

/-- No input spec carries two arcs into one place — see `specAt`. -/
def InputsDistinctPlaces (t : Transition) : Prop :=
  ∀ s ∈ t.inputs, specAt t s.place = some s

/-- **A consume-all arc must be unguarded.**

`net_flattener.rs` never inspects `In`'s guard, so the encoder emits
`m'_i = post[i]` (place emptied) for every `All`/`AtLeast` place. The executor
consumes only guard-*matching* tokens, so guard-failing tokens survive the
firing. Without this hypothesis the abstraction under-approximates. -/
def GuardFreeConsumeAll (t : Transition) : Prop :=
  ∀ s ∈ t.inputs, s.card.consumesAll = true → s.guard = none

/-- **An action writes at most one token per output place.**

`validate_out_spec` is a set-membership check, so an action may write any number
of tokens to a place the spec permits, while `post` fixes the abstract gain at
1 per branch place. Neither paper states this condition; Assumption W1
("observationally pure with respect to the marking") does not imply it. -/
def UnitOutput (prod : PlaceId → Nat) (br : List PlaceId) : Prop :=
  ∀ p, prod p = post br p

end Libpetri
