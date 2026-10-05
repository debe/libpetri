import Libpetri.Novel.LinearBound
import Mathlib.Data.Finset.Card

/-!
# Route A — the name-coloured encoding for colour-slot bound `k > 0` (model)

The ν-net Route A ([NU-050], [NU-051], [NU-053], [NU-054]) encodes a correlation name as one
of `k` **colours**: every coloured place becomes `k` per-colour counters, a mint takes a
*globally fresh* colour (one no coloured place holds), a matched join consumes one token of
the **same** colour from every key, a coloured consumer threads the colour it consumes.
`Semiflow.lean` (`vacuous_colour_layer`) covers `k = 0` under the old semiflow bound, and
`RouteA/SlotBound.lean` (`vacuous_colour_layer_lp`) under the LP bound. This file and its
siblings cover every `k`.

This module is the **model**. It states, in the vocabulary of `Basic.lean`,
`Novel/ForwardDeposit.lean` and `Novel/LinearBound.lean`:

* the plan `build_plan` returns (`name_coloured_encoder.rs`): the coloured places `C`
  (`ColouredPlan.coloured`), the slot count `k`, and one class per flat row
  (`Class::{Untouched, Mint, Join, Consume}`) — `Cls`, `CRow`, and the shape a class
  promises about the row's incidence on `C` — `ClassOK`;
* the CHC relation `encode_coloured` emits — `EState` (one column per uncoloured place,
  `k` columns per coloured place), the rule bodies built by `encode_rule`
  (`uGuard`, `uFire`, `sMint`, `sJoin`, `sConsume`, the lifted invariants), the seed, and
  `ReachE`, the least fixpoint;
* the colour-aware quiescence predicate `encode_coloured_quiescent` / `uncoloured_disable`
  / `coloured_disabled_term` — `uDisabled`, `colDisabled`, `DeadE`, in its strict form (every
  row counted; what the Rust emits under `assume_no_reaping` or on a net with no reapable
  transition). The shipped form skips reapable rows; it is `RouteA/Reaping.lean`'s `DeadERs`;
* the **ν semantics** the encoding must over-approximate — `NuStep`, `ReachNu`: a concrete
  marking whose coloured tokens carry their correlation name.

## The ν semantics, and what it assumes about the runtime

A coloured token's payload is modelled **as its projected name** ([NU-001]: identity is a
projection of the payload; equality of projected names is the only observation a match
makes, [NU-021]). Uncoloured tokens keep an arbitrary payload, unobserved. A ν step of a row
`r` is (`NuStep`):

* the count-level step of `Novel/ForwardDeposit.lean` (`StepCR`): the row is enabled
  (`enabledC`, `can_enable`) and the successor holds `alphaFireC` tokens, the row's deposit
  counts as its post vector (P4 below);
* a name-level effect on the coloured places, per class (`NameEffect`):
  * `untouched` — no coloured place changes;
  * `mint outs` — **one fresh name** `v`, held by no coloured place, is appended to every
    coloured output (P1);
  * `join ins rel` — some name `v` present in every key is consumed once from each key
    (FIFO within a name: `List.erase` removes the first `v`), and appended once to each relay
    target (P2);
  * `consume inp outs` — some token `v` of `inp` is consumed and appended to each coloured
    output (P3; the runtime takes the FIFO head, one of the tokens this allows).

Premises about the shipped runtime, none of them proved about Rust. They come in two kinds.

**Built into the ν semantics.** P1–P4 and P6 are part of the definitions of `NuStep`,
`NameEffect` and `ReachNu`, not hypotheses of the theorems. If one of them is false of the
executor, no theorem becomes inapplicable: the theorems stay true, but of a relation that is
not the executor's, and a `Proven` then says nothing about the executor. `Retrodict.lean`
exhibits exactly that for P1.

* **P1 (NU-010)** a row `build_plan` classifies `Mint` writes one name that no coloured place
  holds into all of its coloured outputs. **Declared, not checked at run time.** Before the fix
  `build_plan` checked only incidence (no coloured input, ≥ 1 budget token consumed), so a
  timeout `forward` that re-emits the consumed token, name included ([IO-014]), a `fork()`, or
  an action payload that carries a live name were all classified `Mint` (`Retrodict.lean`,
  `forward_mint_false_proven`). The flat row cannot tell these apart, so the shipped
  `build_plan` reads the source transition: a `Mint` row must belong to a declared mint
  (`mints`: `SmtVerifier::mint_transitions`, or consuming a declared budget place) whose
  timeout writes no coloured place (`timeout_writes`; `Plan.shipped_mint`). What a declared
  mint's action writes is the contract the report names.
* **P2 (NU-020, NU-021, NU-054)** a matched join's correlated inputs are consumed at count
  one each by one name present in all of them; its relay targets receive that name. The
  runtime checks the relay targets (`relay_violation`, [NU-054]).
* **P3 (NU-051)** a coloured consumer (EXTENDED `Class::Consume`) threads the name it consumes
  into its coloured outputs (relay) or drops it (drain); it never mints. **Unchecked for the
  action**, like P1: `relay_violation` covers only a ν-join's NU-054 relay targets, not a
  consumer's outputs. Its timeout writes are checked: each coloured one must forward the
  consumed input (`Plan.shipped_consume`).
* **P4** the count effect of a firing is `StepCR` over the flat rows (`Soundness.lean`,
  `Novel/ForwardDeposit.lean`; the executor ↔ `StepC` link is gap 30 of the analysis, as for
  every route).
* **P6 (VER-004)** the untimed, priority-free interleaving over-approximates the **markings**
  the executor visits. It does: a timed firing is an untimed one and reaping never changes the
  marking (`Novel/ReapingVsUntimed.lean`, `timed_markings_reachable`). It does **not** over-
  approximate where the executor comes to **rest**: a reaped transition (timing `Deadline` or
  `Window`, `reaping::is_reapable`; `Exact` is never reaped, [TIME-006]) leaves the executor
  quiescent at a marking where the untimed net still enables it. So `routeA_quiescence_sound`
  (`Simulate.lean`), which reads the strict `DeadE`, gives **no guarantee for timed executions
  of a net with a reapable transition**. The shipped `encode_coloured_quiescent` skips the rows
  of reapable transitions (`ft.reapable`) unless the caller sets `assume_no_reaping`.
  `RouteA/Reaping.lean` models that predicate (`DeadERs`, equal to the reaping-aware `DeadER`),
  proves it sound for the executor's rest markings (`routeA_quiescence_sound_reaping`,
  `routeA_reap_aware_sound`), and gives the witness on which the strict query is wrong
  (`ReapW.reaping_breaks_routeA_quiescence`).

**Hypotheses of the theorems.** P5, `ConsumeNoSelfLoop` and the fields of `Premises`
(`Simulate.lean`) are hypotheses: where one fails, the theorem does not apply.

* **P5 (IO-006)** input arcs carry no guard: `GuardFreeConsumeAll` for the simulation,
  `Unguarded` for the quiescence transfer.
* **`ConsumeNoSelfLoop`** a coloured consumer does not relay into its own input. `build_plan`
  does not check it; the shipped encoder no longer needs it (see below).

## What is modelled of the encoder, and how

`EState` columns are `Nat`. The Rust columns are `Int` with a non-negativity guard on every
changed column (`encode_rule`); unchanged columns are copied and the seed is non-negative, so
on the reachable set the two coincide, and every guard below makes the `Nat` subtraction
exact. Places are `PlaceId`s below `n = place_count`; a row's arcs lie below `n`
(`flatten`'s dense index).

`sConsume` models the **update order** the `Class::Consume` rule had before the self-loop fix: the input
column's decrement is pushed first and each coloured output's increment after it, and
`encode_rule` keeps the **last** write per column (`changed[col] = Some(expr)`). On a
self-loop consumer (`inp ∈ outs`) the rule therefore writes `m_inp_c + 1` where the executor
leaves the place unchanged. `Class::Join` handles the same shape explicitly (a key that is
also a relay target nets to zero); `Class::Consume` does not. With a validated law covering
`inp` conjoined, the rule is then **unsatisfiable**, the row never fires in the encoding, and
everything it would have produced is lost: a wrong `Proven` (`Retrodict.lean`,
`self_loop_consume_false_proven`). The simulation theorem carries `ConsumeNoSelfLoop` as a
premise `build_plan` does not check. The shipped arm nets the self-loop (guard only, no update
of the input column), which is the join rule on the one input; `Shipped.lean` reads each
consumer row as that join and drops the premise (`premises_shipped`).
-/

namespace Libpetri.Novel.RouteA

open Libpetri
open Libpetri.Novel.ForwardDeposit
open Libpetri.Novel.LinearBound

/-- A correlation name ([NU-001]). Only equality is observed. -/
abbrev Name := Nat

/-! ## The plan -/

/-- The class `build_plan` assigns a flat row (`enum Class`, `name_coloured_encoder.rs`),
with the coloured places it reads off the row's own incidence. -/
inductive Cls where
  /-- `Class::Untouched`: no coloured incidence. -/
  | untouched
  /-- `Class::Mint { coloured_out }`. -/
  | mint (outs : List PlaceId)
  /-- `Class::Join { coloured_in, relay_out }`. -/
  | join (ins relays : List PlaceId)
  /-- `Class::Consume { input_col, coloured_out }` (EXTENDED, [NU-051]). -/
  | consume (inp : PlaceId) (outs : List PlaceId)
  deriving DecidableEq, Repr

/-- A classified flat row: the transition (for `pre`, arcs), its deposit (`post[p] =
d.count p`, `Novel/ForwardDeposit.lean`), and its class. -/
structure CRow where
  t : Transition
  d : Deposit
  cls : Cls

/-- The flat row the flat routes see. -/
def CRow.flat (r : CRow) : Transition × Deposit := (r.t, r.d)

/-- No reset, consume-all, inhibitor or read arc touches a coloured place — the
`touches_coloured` refusal of `build_plan`. -/
def NoTestArcs (C : List PlaceId) (t : Transition) : Prop :=
  ∀ p ∈ C, t.resets.contains p = false ∧ consumeAllAt t p = false ∧
    p ∉ t.inhibitors ∧ p ∉ t.reads

/-- The incidence a class promises on the coloured places: what the classification branch of
`build_plan` checks (`coloured_in` = coloured places with `pre > 0`, `coloured_out` = those
with `post > 0`, every count exactly one). -/
def ClassShape (C : List PlaceId) (r : CRow) : Prop :=
  match r.cls with
  | .untouched => ∀ p ∈ C, pre r.t p = 0 ∧ r.d.count p = 0
  | .mint outs => outs ≠ [] ∧ (∀ o ∈ outs, o ∈ C) ∧
      ∀ p ∈ C, pre r.t p = 0 ∧ r.d.count p = (if p ∈ outs then 1 else 0)
  | .join ins rel => ins ≠ [] ∧ (∀ p ∈ ins, p ∈ C) ∧ (∀ p ∈ rel, p ∈ C) ∧
      ∀ p ∈ C, pre r.t p = (if p ∈ ins then 1 else 0) ∧
        r.d.count p = (if p ∈ rel then 1 else 0)
  | .consume inp outs => inp ∈ C ∧ (∀ o ∈ outs, o ∈ C) ∧
      ∀ p ∈ C, pre r.t p = (if p = inp then 1 else 0) ∧
        r.d.count p = (if p ∈ outs then 1 else 0)

/-- A row `build_plan` accepted. -/
structure ClassOK (C : List PlaceId) (r : CRow) : Prop where
  arcs : NoTestArcs C r.t
  shape : ClassShape C r

/-- The premise the shipped `build_plan` does **not** check: a coloured consumer does not
relay into its own input. -/
def ConsumeNoSelfLoop : Cls → Prop
  | .consume inp outs => inp ∉ outs
  | _ => True

/-! ## The encoding `encode_coloured` emits -/

/-- One valuation of the `Reachable` columns (`Layout`): `u p` for an uncoloured place,
`s p c` for colour `c < k` of a coloured place. Entries outside the layout are unused. -/
structure EState where
  u : AMarking
  s : PlaceId → Nat → Nat

/-- `Layout::aggregate`: the uncoloured column, or the sum of a coloured place's `k` colour
columns (`"0"` at `k = 0`). The lifted invariants and every property arm read this. -/
def agg (C : List PlaceId) (k : Nat) (e : EState) : AMarking :=
  fun p => if p ∈ C then ∑ c ∈ Finset.range k, e.s p c else e.u p

/-- The uncoloured guards `uncoloured_incidence` pushes: `m_i ≥ pre[i]` for every uncoloured
`i`, `m_i = 0` for an inhibitor, `m_i ≥ 1` for a read (never on a coloured place). -/
def uGuard (C : List PlaceId) (e : EState) (t : Transition) : Prop :=
  (∀ p, p ∉ C → pre t p ≤ e.u p) ∧ (∀ p ∈ t.inhibitors, e.u p = 0) ∧
    (∀ p ∈ t.reads, 1 ≤ e.u p)

/-- The uncoloured updates `uncoloured_incidence` pushes: `post[i]` on a reset or consume-all
place, `m_i - pre[i] + post[i]` otherwise — `fireAD` on the uncoloured columns. -/
def uFire (C : List PlaceId) (e : EState) (t : Transition) (d : Deposit) : AMarking :=
  fun p => if p ∈ C then e.u p else fireAD e.u t d p

/-- The `Class::Mint` rule for colour `c`: `+1` on colour `c` of each coloured output. -/
def sMint (outs : List PlaceId) (c : Nat) (s : PlaceId → Nat → Nat) : PlaceId → Nat → Nat :=
  fun p c' => if c' = c ∧ p ∈ outs then s p c' + 1 else s p c'

/-- The `Class::Join` rule for colour `c`: `-1` on each key that is not a relay target, `+1`
on each relay target that is not a key; a key that is also a relay target is carried over
([NU-054]). -/
def sJoin (ins rel : List PlaceId) (c : Nat) (s : PlaceId → Nat → Nat) : PlaceId → Nat → Nat :=
  fun p c' =>
    if c' = c then
      (if p ∈ ins ∧ p ∉ rel then s p c' - 1
       else if p ∈ rel ∧ p ∉ ins then s p c' + 1 else s p c')
    else s p c'

/-- The `Class::Consume` rule for colour `c`, **with the shipped write order**: the input's
decrement is pushed before the outputs' increments and `encode_rule` keeps the last write per
column, so an output wins over the input. -/
def sConsume (inp : PlaceId) (outs : List PlaceId) (c : Nat) (s : PlaceId → Nat → Nat) :
    PlaceId → Nat → Nat :=
  fun p c' =>
    if c' = c then
      (if p ∈ outs then s p c' + 1 else if p = inp then s p c' - 1 else s p c')
    else s p c'

/-- The colour part of one rule of the class, for some colour `c < k` (one rule per colour),
with its colour guard: a globally fresh colour for a mint, colour `c` on every key for a
join, colour `c` on the input for a consumer. -/
def ColourStep (C : List PlaceId) (k : Nat) :
    Cls → (PlaceId → Nat → Nat) → (PlaceId → Nat → Nat) → Prop
  | .untouched, s, s' => s' = s
  | .mint outs, s, s' => ∃ c, c < k ∧ (∀ q ∈ C, s q c = 0) ∧ s' = sMint outs c s
  | .join ins rel, s, s' => ∃ c, c < k ∧ (∀ p ∈ ins, 1 ≤ s p c) ∧ s' = sJoin ins rel c s
  | .consume inp outs, s, s' => ∃ c, c < k ∧ 1 ≤ s inp c ∧ s' = sConsume inp outs c s

/-- What one `encode_coloured` call is built from. -/
structure Enc where
  /-- `plan.coloured` (sorted, deduplicated flat indices). -/
  C : List PlaceId
  /-- `plan.k`, the checked colour-slot bound (`checked`, `slot_bound_lp.rs`;
  `RouteA/SlotBound.lean`). -/
  k : Nat
  /-- `flat.place_count`. -/
  n : Nat
  /-- The flat rows with their classes (`plan.classes` zipped with `flat.transitions`). -/
  rows : List CRow
  /-- The weight vectors of the `invariants` argument (conjoined by `lifted_invariant`). -/
  invs : List Weight
  /-- The seed of the uncoloured columns (`initial.count`), and `y·M₀` of each invariant. -/
  a0 : AMarking

/-- One rule of `encode_coloured`: the uncoloured guards and updates, the class's colour
guard and update for one colour, and every lifted invariant on the successor's aggregates
(`y·agg(M') = y·M₀`; `inv.constant` is `y·M₀` after `validate_invariants_exact`). -/
structure EStep (E : Enc) (r : CRow) (e e' : EState) : Prop where
  guard : uGuard E.C e r.t
  u : e'.u = uFire E.C e r.t r.d
  s : ColourStep E.C E.k r.cls e.s e'.s
  inv : ∀ y ∈ E.invs, dot y (agg E.C E.k e') E.n = dot y E.a0 E.n

/-- The seed `(assert (Reachable …))`: uncoloured places at their initial count, every colour
column at `0`. -/
def e0 (E : Enc) : EState :=
  ⟨fun p => if p ∈ E.C then 0 else E.a0 p, fun _ _ => 0⟩

/-- One transition of the CHC system: some row's rule fires. -/
def StepE (E : Enc) (e e' : EState) : Prop := ∃ r ∈ E.rows, EStep E r e e'

/-- `Reachable`, the least fixpoint of the seed and the transition rules. -/
def ReachE (E : Enc) : EState → Prop := Relation.ReflTransGen (StepE E) (e0 E)

/-! ## The colour-aware quiescence predicate -/

/-- The uncoloured disable reasons of a row (`uncoloured_disable`, env-free): an uncoloured
input below its demand, a marked inhibitor, an empty read place. -/
def uDisabled (C : List PlaceId) (e : EState) (t : Transition) : Prop :=
  (∃ p, p ∉ C ∧ e.u p < pre t p) ∨ (∃ p ∈ t.inhibitors, 0 < e.u p) ∨
    (∃ p ∈ t.reads, e.u p < 1)

/-- `coloured_disabled_term`: no colour enables the class — no free colour for a mint, no
colour on every key for a join, no colour at the input for a consumer. At `k = 0` every
coloured class is disabled outright (`"true"`), which is what the empty quantifier gives. -/
def colDisabled (C : List PlaceId) (k : Nat) : Cls → (PlaceId → Nat → Nat) → Prop
  | .untouched, _ => False
  | .mint _, s => ∀ c, c < k → ∃ q ∈ C, 1 ≤ s q c
  | .join ins _, s => ∀ c, c < k → ∃ p ∈ ins, s p c = 0
  | .consume inp _, s => ∀ c, c < k → s inp c = 0

/-- `encode_coloured_quiescent` with no row marked reapable (`assume_no_reaping`, or a net with
no `Deadline` / `Window` transition): every row is disabled for an uncoloured reason or for
every colour. (A row with no reason at all makes the Rust return `None`, "never quiescent"; the
empty disjunction is `False`, the same answer.) The shipped predicate skips the reapable rows
first: `RouteA/Reaping.lean`, `DeadERs`, `deadERs_nil`. -/
def DeadE (E : Enc) (e : EState) : Prop :=
  ∀ r ∈ E.rows, uDisabled E.C e r.t ∨ colDisabled E.C E.k r.cls e.s

/-! ## The ν semantics -/

/-- The live names: every name some coloured place holds. -/
def live (C : List PlaceId) (m : CMarking) : List Name := C.flatMap m

/-- The name-level effect of one firing on the coloured places (P1–P3). This **is** the ν
semantics' reading of the action contract, not a check of it: P1 and P3 are unenforced by the
runtime, and an executor step that breaks them is not a `NameEffect` (see the module header). -/
def NameEffect (C : List PlaceId) : Cls → CMarking → CMarking → Prop
  | .untouched, m, m' => ∀ p ∈ C, m' p = m p
  | .mint outs, m, m' => ∃ v, (∀ q ∈ C, v ∉ m q) ∧
      ∀ p ∈ C, m' p = if p ∈ outs then m p ++ [v] else m p
  | .join ins rel, m, m' => ∃ v, (∀ p ∈ ins, v ∈ m p) ∧
      ∀ p ∈ C, m' p = (if p ∈ ins then (m p).erase v else m p) ++
        (if p ∈ rel then [v] else [])
  | .consume inp outs, m, m' => ∃ v, v ∈ m inp ∧
      ∀ p ∈ C, m' p = (if p = inp then (m p).erase v else m p) ++
        (if p ∈ outs then [v] else [])

/-- One ν firing of a row: the count-level step (`StepCR`'s shape) and the name-level effect. -/
structure NuStep (C : List PlaceId) (r : CRow) (m m' : CMarking) : Prop where
  enabled : enabledC m r.t = true
  counts : alpha m' = alphaFireC m r.t (fun p => r.d.count p)
  names : NameEffect C r.cls m m'

/-- ν reachability over the rows of a plan, closed net (no injection: `coloured_attempt`
declines under injection, [VER-006] AC7). -/
def ReachNu (C : List PlaceId) (rows : List CRow) (m0 : CMarking) : CMarking → Prop :=
  Relation.ReflTransGen (fun m m' => ∃ r ∈ rows, NuStep C r m m') m0

/-- A row is enabled in the ν semantics ([NU-020] for a join: the counts **and** one name
present in every key). A mint is enabled whenever its counts are: the runtime always has a
fresh name. -/
def NuEnabled (m : CMarking) (r : CRow) : Prop :=
  enabledC m r.t = true ∧
    match r.cls with
    | .join ins _ => ∃ v, ∀ p ∈ ins, v ∈ m p
    | _ => True

/-- ν quiescence: no row is enabled. -/
def NuDead (rows : List CRow) (m : CMarking) : Prop := ∀ r ∈ rows, ¬ NuEnabled m r

/-- P5 for the quiescence transfer: no input arc carries a guard ([IO-006]). -/
def Unguarded (t : Transition) : Prop := ∀ s ∈ t.inputs, s.guard = none

/-! ## The simulation relation -/

/-- Tokens of colour `c` in a list of names, under the colour assignment `σ`. -/
def cnt (σ : Name → Nat) (c : Nat) (l : List Name) : Nat := l.countP (fun x => decide (σ x = c))

/-- A ν marking `m` is represented by the encoding state `e` under the colour assignment `σ`:
uncoloured columns hold the counts, each colour column counts the names of that colour, and
`σ` is injective on the live names with every live colour below `k`. -/
structure Sim (C : List PlaceId) (k : Nat) (m : CMarking) (e : EState) (σ : Name → Nat) :
    Prop where
  unc : ∀ p, p ∉ C → e.u p = (m p).length
  col : ∀ p ∈ C, ∀ c, e.s p c = cnt σ c (m p)
  inj : ∀ x ∈ live C m, ∀ x' ∈ live C m, σ x = σ x' → x = x'
  lt : ∀ x ∈ live C m, σ x < k

end Libpetri.Novel.RouteA
