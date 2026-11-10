import Libpetri.Reference.Semantics
import Libpetri.Reference.Queue
import Libpetri.Spec.Registry

set_option linter.missingDocs true

/-!
# Glossary: firing semantics

The terms of `spec/glossary.md`, as Lean definitions over the reference semantics
(`Libpetri/Reference/Semantics.lean`). Nothing here redefines firing: every term is a name for,
or a reading of, a definition the reference semantics already has (`Seam.enabledNA`,
`Seam.nconsumed`, `Seam.fireNC`, `Reference.deposit`, `Reference.Fires`). Each docstring quotes
its glossary entry; the bridge lemmas at the end show that the readable forms agree with the
reference definitions.

A requirement statement is a predicate over an abstract firing relation `F : FireRel N`, so that
it can be checked against the reference semantics (`Reference.Fires`) and against a mutant.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

variable {N : Type}

/-! ## Places, token counts, markings -/

/-- **Glossary: Place.** "A named container that holds tokens [CORE-001]. Two places are the
same place exactly when they have the same identity [CORE-002]."

The firing semantics identifies a place with its name, of a type `N` with decidable equality;
the identity of [CORE-002] is equality on `N`. -/
abbrev PlaceName (N : Type) := N

/-- **Glossary: Marking.** "The distribution of tokens across all places at one instant
[CORE-070]. A place no arc touches keeps its tokens and is inert [CORE-072]."

At the granularity of the firing semantics a marking is its token counts, by place name. -/
abbrev CountMarking (N : Type) := N → Nat

/-- **Glossary: Token count.** "The number of tokens a place holds in a marking, written `m(p)`.
Enablement and firing read token counts only: no input arc tests a token's value [IO-006]." -/
abbrev TokenCount (m : CountMarking N) (p : N) : Nat := m p

/-- **Glossary: Marked.** "A place is marked when its token count is not zero." -/
def Marked (m : CountMarking N) (p : N) : Prop := m p ≠ 0

instance (m : CountMarking N) (p : N) : Decidable (Marked m p) :=
  inferInstanceAs (Decidable (m p ≠ 0))

/-! ## Arcs -/

/-- **Glossary: Input arc.** "An arc from a place to a transition that the transition consumes
from when it fires, according to the arc's cardinality `One`, `Exactly(n)`, `All` or
`AtLeast(m)` [CORE-030], [IO-001]–[IO-004]. A transition declares at most one input arc per
place [CORE-030]."

`InputArc t p c`: the input arc of `t` on `p` has cardinality `c`. It reads the arc the way the
reference semantics does (`Seam.nspecAt`, the first input arc on `p`), so it names the one arc
that enablement and consumption use. A malformed transition with two input arcs on `p` (which
[CORE-030] rejects at build) has `InputArc t p c` for the first one only. -/
def InputArc [DecidableEq N] (t : Trans N) (p : N) (c : Card) : Prop :=
  ∃ s, nspecAt t.core p = some s ∧ s.card = c

/-- **Glossary: Inhibitor arc.** "An arc from a place to a transition that disables the
transition while the place is marked [CORE-031]. It never consumes." -/
abbrev InhibitorArc (t : Trans N) (p : N) : Prop := p ∈ t.core.inhibitors

/-- `t` with every inhibitor arc on `p` removed, and nothing else changed: the transition a
marking-independent inhibitor on `p` would leave behind. -/
def withoutInhibitor [DecidableEq N] (t : Trans N) (p : N) : Trans N :=
  { t with core := { t.core with inhibitors := t.core.inhibitors.filter (· ≠ p) } }

/-- **Glossary: Read arc.** "An arc from a place to a transition that requires the place to be
marked for the transition to be enabled [CORE-032]. It never consumes." -/
abbrev ReadArc (t : Trans N) (p : N) : Prop := p ∈ t.core.reads

/-- **Glossary: Reset arc.** "An arc from a place to a transition that removes every token from
the place when the transition fires [CORE-034]. It never affects enablement." -/
abbrev ResetArc (t : Trans N) (p : N) : Prop := p ∈ t.core.resets

/-- Every place an output spec names, `allPlaces` of [IO-017]: a `ForwardInput` contributes its
`to`. -/
def outPlaces : Out N → List N
  | .place p => [p]
  | .forward _ dst => [dst]
  | .and l r => outPlaces l ++ outPlaces r
  | .xor l r => outPlaces l ++ outPlaces r
  | .timeout c => outPlaces c

/-- **Glossary: Output arc.** "An arc from a transition to a place: a place that the
transition's output spec names [CORE-035], [IO-017]." -/
def OutputArc (t : Trans N) (p : N) : Prop :=
  ∃ o, t.out = some o ∧ p ∈ outPlaces o

/-! ## Cardinality -/

/-- **Glossary: Required count.** "`requiredCount()`: the fewest tokens an input place must hold
for the transition to be enabled. It is 1 for `One` and `All`, `n` for `Exactly(n)` and `m` for
`AtLeast(m)` [IO-007]." This is `Card.required`. -/
abbrev requiredCount (c : Card) : Nat := c.required

/-- **Glossary: Consumption count.** "`consumptionCount(available)`: the tokens a firing removes
from an input place that holds `available` tokens. It is 1 for `One`, `n` for `Exactly(n)` and
`available` for `All` and `AtLeast(m)` [IO-007]." -/
def consumptionCount (c : Card) (available : Nat) : Nat :=
  if c.consumesAll then available else c.required

/-! ## Enablement and firing -/

/-- **Glossary: Enabled.** "A transition is enabled in a marking when every input place holds
at least its required count, every read place is marked and no inhibitor place is marked
[CORE-022], [IO-005]. Reset arcs and output arcs play no part." This is `Seam.enabledNA`;
`enabled_iff` is the readable form. -/
def Enabled (t : Trans N) (m : CountMarking N) : Prop := enabledNA m t.core = true

instance (t : Trans N) (m : CountMarking N) : Decidable (Enabled t m) :=
  inferInstanceAs (Decidable (enabledNA m t.core = true))

/-- **Glossary: Consume.** "To remove tokens from an input place when the transition fires: as
many as the consumption count, oldest first [CORE-030], [IO-007]. Read arcs and inhibitor arcs
never consume [CORE-031], [CORE-032]."

`Consumes t m p` is the number of tokens a firing of `t` from `m` consumes from `p`
(`Seam.nconsumed`; 0 for a place with no input arc). Token order is below the count
granularity. -/
abbrev Consumes [DecidableEq N] (t : Trans N) (m : CountMarking N) (p : N) : Nat :=
  nconsumed m t.core p

/-- **Glossary: Deposit.** "The tokens a firing adds to the marking, counted per place: how many
tokens each place receives. It may be written as a list of places with repetition, a place
receiving one token per occurrence, but only the count per place is normative: two deposits that
put the same number of tokens in every place are the same deposit, whatever their order
[CORE-036]. A reset place ends a firing holding exactly what the firing deposited there
[CORE-034]."

`Deposits d p` is the number of tokens the deposit `d` puts in `p` (`Seam.depProd`). -/
abbrev Deposits [DecidableEq N] (d : List N) (p : N) : Nat := depProd d p

/-- **Glossary: Deposit**, "two deposits that put the same number of tokens in every place are
the same deposit, whatever their order [CORE-036]": `SamePerPlace d d'`. -/
def SamePerPlace [DecidableEq N] (d d' : List N) : Prop := ∀ p, Deposits d p = Deposits d' p

/-- **Glossary: Produced set.** "The places that received at least one token from a firing
[IO-015]." -/
abbrev Produced (d : List N) (p : N) : Prop := p ∈ d

/-- The produced set of `d` is exactly the places of `b`: one or more tokens in each place of
`b`, none anywhere else (glossary: Output branch, "the branch fixes which places receive tokens,
not how many"). -/
def OnPlacesOf (d b : List N) : Prop := ∀ p, Produced d p ↔ p ∈ b

/-- **Glossary: Fire.** "To fire is to perform one firing. One firing of an enabled transition
consumes from its input places, empties its reset places and deposits the tokens of one outcome
[CORE-030], [CORE-034], [CORE-035]. Read as one step from a marking `m` to a marking `m'`, a
firing ignores timing and priority."

A firing relation: `F t m d m'` says that `t` fires from `m`, deposits `d`, and leaves `m'`.
Requirements are predicates over an arbitrary `F`; `Reference.Fires` is the reference one. -/
abbrev FireRel (N : Type) := Trans N → (N → Nat) → List N → (N → Nat) → Prop

/-- **Glossary: Fire**, with the deposit hidden: `Fire F t m m'` says that some firing of `t`
under `F` leads from `m` to `m'`. -/
def Fire (F : FireRel N) (t : Trans N) : (N → Nat) → (N → Nat) → Prop :=
  fun m m' => ∃ d, F t m d m'

/-- The reference firing relation (`Reference.Fires`), as a `FireRel`. -/
abbrev RefFire [DecidableEq N] : FireRel N := Reference.Fires

/- The reference firing relation is the witness model: a `holds` theorem checks a requirement
against it. -/
#spec_witness RefFire

/-! ## Outcomes -/

/-- **Glossary: Output spec.** "The tree of `Place`, `And`, `Xor`, `Timeout` and `ForwardInput`
nodes that says where a transition's action may write [IO-010]–[IO-014]. A transition with no
output spec deposits nothing." The output spec of `t` is `t.out`, an `Option (Out N)`. -/
abbrev OutputSpec (t : Trans N) : Option (Out N) := t.out

/-- **Glossary: Output branch.** "One way the action can satisfy the output spec: a set of
places, taking one child at every `Xor` and the union at every `And` [IO-015], [IO-016]. With
output validation enabled [CONC-026], a firing that ends with its action deposits one or more
tokens in each place of one output branch and none in any other place: the branch fixes which
places receive tokens, not how many [IO-015], [CORE-036]. The output branches of a spec that
builds are pairwise distinct sets [IO-012]. The analyses that enumerate them model one token per
place [IO-016]."

`OutputBranch t b`: `b` is one of the branches of `t`'s output spec (`Out.branches`); a
transition with no output spec has the one empty branch. A `Timeout` node offers its child's
branches ("Timeout — claims its child's claim", [IO-015]). The timeout outcome is not an output
branch: what it deposits is `TimeoutOutcome` [IO-013]. -/
def OutputBranch (t : Trans N) (b : List N) : Prop :=
  match t.out with
  | none => b = []
  | some o => b ∈ o.branches

/-- **Glossary: Forward.** "`ForwardInput(from, to)`, allowed only inside the child of a
`Timeout` node: on the timeout outcome, one token in `to` for each token the firing consumed from
`from`, in consumption order, each keeping the consumed token's value and `created_at` [IO-014].
In an output branch it claims `to` [IO-015]." Values and `created_at` are below the count
granularity of the firing semantics.

`forwardDeposit consumed src dst` is the deposit of `ForwardInput(src, dst)` on the timeout
outcome of a firing that consumed `consumed p` tokens from each `p`. -/
def forwardDeposit (consumed : N → Nat) (src dst : N) : List N :=
  List.replicate (consumed src) dst

/-- **Glossary: Timeout outcome.** "The way a firing ends when the executor's own budget timer
on the `Timeout` node fires before the action completes [IO-013]. An output spec holds at most
one `Timeout` node, so a transition has at most one timeout outcome [IO-013]. The `Timeout` child
holds no `Xor` node, so that outcome deposits in one fixed set of places [IO-013]. The marking
then receives the `Timeout` child's tokens and nothing else: one minted token in each place the
child names through `Place`, and for each `ForwardInput(from, to)` the tokens the firing consumed
from `from`, each keeping its value and `created_at` [IO-014]. It is compared with other deposits
per place [CORE-036], [IO-012]. An exception the action raises is not a timeout outcome."

`TimeoutOutcome t consumed d`: `d` is a deposit of the timeout outcome of `t`, for a firing
that consumed `consumed p` tokens from each `p`. The reference reads the first `Timeout` node in
pre-order, which on a transition that builds (`Builds`) is its only one, and whose child then
holds no `Xor` node, so `d` is unique (`timeoutOutcome_unique`). -/
def TimeoutOutcome (t : Trans N) (consumed : N → Nat) (d : List N) : Prop :=
  ∃ o c, t.out = some o ∧ o.findTimeout = some c ∧ d ∈ c.timeoutDeposits consumed

/-- **Glossary: Exact on the output spec** ([IO-011], [IO-012]): on every place the output spec
`o` names, the produced set of `d` and the branch `b` agree. -/
def ExactOn (o : Out N) (d : List N) (b : List N) : Prop :=
  ∀ q ∈ outPlaces o, (Produced d q ↔ q ∈ b)

/-! ## Building a transition: the build-time checks

**Glossary: Build-time checks.** "The checks building a transition runs: the input-arc check of
[CORE-030], the input-count checks of [IO-002] and [IO-004], the input-and-read check of
[EXEC-012], the timing check of [TIME-001], then, on its output spec and in this order, a place
named twice in one output branch
[IO-011], more than one `Timeout` node [IO-013], an `Xor` node inside the child of the `Timeout`
node [IO-013], a `ForwardInput` outside the child of a `Timeout` node [IO-014], a `ForwardInput`
whose `from` is not an input place [IO-014], and two output branches that claim the same set of
places [IO-012]. The first check that fails names the error. No executor option skips them
[CONC-026]."

`WellFormedOut` is the output-spec part, `PreOutputChecks` the checks that run before it
([CORE-030], the [IO-002]/[IO-004] input counts, and [EXEC-012]'s input-and-read check), `Builds`
the whole. The timing check of [TIME-001] is outside this model, because `Trans` carries no
timing; `Reference/Load.lean` and the runtimes run it in the stated place. The spec orders [EXEC-012] after both, and orders neither of [CORE-030] and the
count checks before the other; `refBuild` is the reference builder, which names the first failing
check with its message, byte for byte. -/

/-- The input places of `t`, in declaration order. -/
def inPlaces (t : Trans N) : List N := t.core.inputs.map (·.place)

/-- The input places of `t` are distinct: [CORE-030]'s build check. -/
def InputsDistinct (t : Trans N) : Prop := (inPlaces t).Nodup

instance [DecidableEq N] (t : Trans N) : Decidable (InputsDistinct t) :=
  inferInstanceAs (Decidable (inPlaces t).Nodup)

/-- **The input-count checks pass** ([IO-002] AC1, [IO-004] AC1): every input arc requires at
least one token, so no `Exactly(0)` and no `AtLeast(0)`. -/
def InputCountsPositive (t : Trans N) : Prop := ∀ s ∈ t.core.inputs, 1 ≤ requiredCount s.card

instance (t : Trans N) : Decidable (InputCountsPositive t) := by
  unfold InputCountsPositive; infer_instance

/-- The stand-in message of the [IO-002] and [IO-004] count checks (`Exactly(n)` or
`AtLeast(n)` with `n < 1`). The spec gives the checks no message of their own here, so the
reference builder uses a stand-in, as it does for [CORE-030]. -/
def msgCount : String := "IO-002/IO-004"

/-- **[EXEC-012]'s build error** (ruling D15), for the transition `t` and the place `p`, byte
for byte the message of the spec with `<t>` the name of `t` and `<p>` the place. -/
def msgInputRead [ToString N] (t : Trans N) (p : N) : String :=
  "Transition '" ++ t.core.name ++ "' declares an input arc and a read arc on place '" ++
    toString p ++ "'. A read of a place the same firing consumes from has no coherent " ++
    "semantics and is rejected (EXEC-012). Remove the read arc: the input arc already hands " ++
    "the consumed tokens to the action."

/-- The place the [EXEC-012] build check names: the place of the first read arc, in declaration
order, whose place is an input place of `t`; `none` when there is none. -/
def firstInputRead [DecidableEq N] (t : Trans N) : Option N :=
  t.core.reads.find? (fun p => decide (p ∈ inPlaces t))

/-- The check finds nothing exactly when `t` has no input arc and read arc on one place. -/
theorem firstInputRead_eq_none_iff [DecidableEq N] (t : Trans N) :
    firstInputRead t = none ↔ NoInputRead t := by
  unfold firstInputRead NoInputRead
  rw [List.find?_eq_none]
  constructor
  · intro h s hs hr
    have := h s.place hr
    simp only [decide_eq_true_eq] at this
    exact this (List.mem_map.mpr ⟨s, hs, rfl⟩)
  · intro h p hp hin
    simp only [decide_eq_true_eq] at hin
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hin
    exact h s hs hp

/-- **The checks before the output-spec checks pass**: the input places are distinct
([CORE-030]), every input arc requires at least one token ([IO-002], [IO-004]), and no place
carries both an input arc and a read arc ([EXEC-012], ruling D15). -/
def PreOutputChecks [DecidableEq N] (t : Trans N) : Prop :=
  InputsDistinct t ∧ InputCountsPositive t ∧ NoInputRead t

instance [DecidableEq N] (t : Trans N) : Decidable (PreOutputChecks t) := by
  unfold PreOutputChecks; infer_instance

/-- Some output branch of `o` names a place twice: [IO-011]'s build check, the first of the
output-spec checks. -/
def DupBranch (o : Out N) : Prop := ∃ b ∈ o.branches, ¬ b.Nodup

instance [DecidableEq N] (o : Out N) : Decidable (DupBranch o) :=
  inferInstanceAs (Decidable (∃ b ∈ o.branches, ¬ b.Nodup))

/-- **Duplicate in one branch**: some output branch of `o` names the place `p` twice. `DupBranch o`
holds exactly when this holds for some `p` (`dupBranch_iff`). -/
def BranchDuplicate [DecidableEq N] (o : Out N) (p : N) : Prop :=
  ∃ b ∈ o.branches, 2 ≤ b.count p

/-- A branch that names a place twice is not `Nodup`, and one that is not `Nodup` names some place
twice. -/
theorem dupBranch_iff [DecidableEq N] (o : Out N) : DupBranch o ↔ ∃ p, BranchDuplicate o p := by
  constructor
  · rintro ⟨b, hb, hn⟩
    rw [List.nodup_iff_count_le_one] at hn
    simp only [not_forall, Nat.not_le] at hn
    obtain ⟨p, hp⟩ := hn
    exact ⟨p, b, hb, hp⟩
  · rintro ⟨p, b, hb, hc⟩
    refine ⟨b, hb, fun hn => ?_⟩
    have := List.nodup_iff_count_le_one.mp hn p
    omega

/-- Every place of an output branch is named by the output spec. -/
theorem outPlaces_of_branch :
    ∀ (o : Out N) (b : List N), b ∈ o.branches → ∀ p ∈ b, p ∈ outPlaces o
  | .place q, b, hb, p, hp => by
    simp only [Out.branches, List.mem_singleton] at hb
    subst hb
    simpa [outPlaces] using hp
  | .forward _ dst, b, hb, p, hp => by
    simp only [Out.branches, List.mem_singleton] at hb
    subst hb
    simpa [outPlaces] using hp
  | .and l r, b, hb, p, hp => by
    simp only [Out.branches, cross, List.mem_flatMap, List.mem_map] at hb
    obtain ⟨x, hx, y, hy, rfl⟩ := hb
    simp only [outPlaces, List.mem_append]
    rcases List.mem_append.1 hp with h | h
    · exact .inl (outPlaces_of_branch l x hx p h)
    · exact .inr (outPlaces_of_branch r y hy p h)
  | .xor l r, b, hb, p, hp => by
    simp only [Out.branches, List.mem_append] at hb
    simp only [outPlaces, List.mem_append]
    rcases hb with h | h
    · exact .inl (outPlaces_of_branch l b h p hp)
    · exact .inr (outPlaces_of_branch r b h p hp)
  | .timeout c, b, hb, p, hp => outPlaces_of_branch c b hb p hp

/-- Every place the output spec names lies in some output branch. -/
theorem branch_of_outPlaces :
    ∀ (o : Out N), ∀ q ∈ outPlaces o, ∃ b ∈ o.branches, q ∈ b
  | .place p, q, hq => ⟨[p], by simp [Out.branches], by simpa [outPlaces] using hq⟩
  | .forward _ p, q, hq => ⟨[p], by simp [Out.branches], by simpa [outPlaces] using hq⟩
  | .and l r, q, hq => by
    simp only [outPlaces, List.mem_append] at hq
    obtain ⟨x0, hx0⟩ := List.exists_mem_of_ne_nil _ (branches_ne_nil l)
    obtain ⟨y0, hy0⟩ := List.exists_mem_of_ne_nil _ (branches_ne_nil r)
    rcases hq with hq | hq
    · obtain ⟨x, hx, hqx⟩ := branch_of_outPlaces l q hq
      exact ⟨x ++ y0, by simp only [Out.branches, cross, List.mem_flatMap, List.mem_map]; exact
        ⟨x, hx, y0, hy0, rfl⟩, List.mem_append_left _ hqx⟩
    · obtain ⟨y, hy, hqy⟩ := branch_of_outPlaces r q hq
      exact ⟨x0 ++ y, by simp only [Out.branches, cross, List.mem_flatMap, List.mem_map]; exact
        ⟨x0, hx0, y, hy, rfl⟩, List.mem_append_right _ hqy⟩
  | .xor l r, q, hq => by
    simp only [outPlaces, List.mem_append] at hq
    rcases hq with hq | hq
    · obtain ⟨b, hb, hqb⟩ := branch_of_outPlaces l q hq
      exact ⟨b, by simp [Out.branches, hb], hqb⟩
    · obtain ⟨b, hb, hqb⟩ := branch_of_outPlaces r q hq
      exact ⟨b, by simp [Out.branches, hb], hqb⟩
  | .timeout c, q, hq => branch_of_outPlaces c q hq

/-! ### [IO-011]'s walk: which place the message names

**IO-011, "Which place the message names."** "1. A `Place(P)` node and a `ForwardInput(from, P)`
node name `P`. 2. A `Timeout` node walks its child and names the places its child names. 3. An
`Xor` node walks its children left to right. *If* a child reports a place, *then* the `Xor`
*shall* report that place. Otherwise the `Xor` names the places its children name, each once, in
the order the walk first meets them. 4. An `And` node walks its children left to right. *If* a
child reports a place, *then* the `And` *shall* report that place. Otherwise, *if* a place the
child names, taken in the order the walk first met them, is already named by an earlier child,
*then* the `And` *shall* report the first such place. Otherwise the `And` names the places its
children name, each once, in the order the walk first meets them."

A walk result is `.inl p` (the walk reports `p`) or `.inr ps` (it reports nothing and names the
places `ps`, each once, in the order it met them). The reference's binary `.and` reads an n-ary
`And` as right-nested binary nodes, so a `.and` met as a child of an `.and` continues its parent's
walk: the children of `And(c₁, …, cₙ)` are walked as the n-ary node's children (`andChildren`
order). Every builder walks the n-ary node it holds; the two agree on every spec in which no
`And` is written as a direct child of an `And`, the specs the binary `Out` tells apart. -/

/-- Step 4 at one child of an `And`: the child's own result `own`, checked against `pool`, the
places the `And`'s earlier children name. A place the child reports stays reported; otherwise the
first place the child names, in the order the walk met them, that `pool` holds is reported;
otherwise the child's places join `pool`. -/
def andStep [DecidableEq N] (pool : List N) : N ⊕ List N → N ⊕ List N
  | .inl p => .inl p
  | .inr cs =>
    match cs.find? (fun q => decide (q ∈ pool)) with
    | some p => .inl p
    | none => .inr (pool ++ cs)

/-- Step 3 on the results of an `Xor`'s two children: the first reported place, or the places
both name, each once, in first-seen order. -/
def xorJoin [DecidableEq N] : N ⊕ List N → N ⊕ List N → N ⊕ List N
  | .inl p, _ => .inl p
  | .inr _, .inl p => .inl p
  | .inr ls, .inr rs => .inr (ls ++ rs.filter (fun q => decide (q ∉ ls)))

/-- **[IO-011]'s walk** of `o` as a child of an `And` whose earlier children name `pool` (`[]`:
not below an `And`, or its first child). Steps 1 and 2 are the `place`, `forward` and `timeout`
clauses, step 3 the `xor` clause through `xorJoin`, step 4 the `and` clause (its children in
turn, each through `andStep`). A `Timeout` child and the children of an `Xor` start a walk of
their own (`pool = []`). -/
def dupScan [DecidableEq N] : List N → Out N → N ⊕ List N
  | pool, .place p => andStep pool (.inr [p])
  | pool, .forward _ d => andStep pool (.inr [d])
  | pool, .timeout c => andStep pool (dupScan [] c)
  | pool, .xor l r => andStep pool (xorJoin (dupScan [] l) (dupScan [] r))
  | pool, .and l r =>
    match dupScan pool l with
    | .inl p => .inl p
    | .inr pool' => dupScan pool' r

/-- **The place [IO-011]'s message names**: the place the walk of `o` reports, `none` when it
reports none. -/
def firstDup [DecidableEq N] (o : Out N) : Option N :=
  match dupScan [] o with
  | .inl p => some p
  | .inr _ => none

/-- What a walk result says about the node `o` walked against `pool`: a reported place is named
twice in one output branch of `o`, or is named by `o` and by `pool`; when nothing is reported, no
output branch of `o` names a place twice, `o` names no place of `pool`, and the result holds the
places of `pool` and of `o`. -/
def DupScanSpec [DecidableEq N] (o : Out N) (pool : List N) : N ⊕ List N → Prop
  | .inl p => BranchDuplicate o p ∨ (p ∈ outPlaces o ∧ p ∈ pool)
  | .inr ps => ¬ DupBranch o ∧ (∀ q ∈ outPlaces o, q ∉ pool) ∧ ∀ q, q ∈ ps ↔ q ∈ pool ∨ q ∈ outPlaces o

/-- `andStep` turns a walk of `o` on its own into a walk of `o` against `pool`. -/
theorem andStep_spec [DecidableEq N] {o : Out N} {own : N ⊕ List N} (pool : List N)
    (h : DupScanSpec o [] own) : DupScanSpec o pool (andStep pool own) := by
  cases own with
  | inl p =>
    simp only [DupScanSpec, List.not_mem_nil, and_false, or_false] at h
    exact .inl h
  | inr cs =>
    obtain ⟨hd, -, hm⟩ := h
    simp only [List.not_mem_nil, false_or] at hm
    simp only [andStep]
    cases hf : cs.find? (fun q => decide (q ∈ pool)) with
    | some p =>
      have hp : p ∈ pool := by simpa using List.find?_some hf
      exact .inr ⟨(hm p).1 (List.mem_of_find?_eq_some hf), hp⟩
    | none =>
      rw [List.find?_eq_none] at hf
      refine ⟨hd, fun q hq hqp => ?_, fun q => ?_⟩
      · exact absurd (by simpa using hqp) (hf q ((hm q).2 hq))
      · rw [List.mem_append, hm q]

/-- The walk is sound: its result satisfies `DupScanSpec`. -/
theorem dupScan_spec [DecidableEq N] : ∀ (o : Out N) (pool : List N),
    DupScanSpec o pool (dupScan pool o)
  | .place p, pool => andStep_spec pool (by
      refine ⟨fun ⟨b, hb, hn⟩ => hn ?_, by simp, fun q => ?_⟩
      · simp only [Out.branches, List.mem_singleton] at hb; subst hb; simp
      · simp [outPlaces])
  | .forward _ d, pool => andStep_spec pool (by
      refine ⟨fun ⟨b, hb, hn⟩ => hn ?_, by simp, fun q => ?_⟩
      · simp only [Out.branches, List.mem_singleton] at hb; subst hb; simp
      · simp [outPlaces])
  | .timeout c, pool => andStep_spec pool (dupScan_spec c [])
  | .xor l r, pool => andStep_spec pool (by
      have hl := dupScan_spec l []
      have hr := dupScan_spec r []
      cases hsl : dupScan [] l with
      | inl p =>
        rw [hsl] at hl
        simp only [DupScanSpec, List.not_mem_nil, and_false, or_false] at hl
        obtain ⟨b, hb, hc⟩ := hl
        exact .inl ⟨b, by simp [Out.branches, hb], hc⟩
      | inr ls =>
        rw [hsl] at hl
        obtain ⟨hdl, -, hml⟩ := hl
        cases hsr : dupScan [] r with
        | inl p =>
          rw [hsr] at hr
          simp only [DupScanSpec, List.not_mem_nil, and_false, or_false] at hr
          obtain ⟨b, hb, hc⟩ := hr
          exact .inl ⟨b, by simp [Out.branches, hb], hc⟩
        | inr rs =>
          rw [hsr] at hr
          obtain ⟨hdr, -, hmr⟩ := hr
          refine ⟨fun ⟨b, hb, hn⟩ => ?_, by simp, fun q => ?_⟩
          · simp only [Out.branches, List.mem_append] at hb
            rcases hb with hb | hb
            · exact hdl ⟨b, hb, hn⟩
            · exact hdr ⟨b, hb, hn⟩
          · simp only [List.mem_append, List.mem_filter, decide_eq_true_eq, hml, hmr,
              List.not_mem_nil, false_or, outPlaces]
            tauto)
  | .and l r, pool => by
    have hl := dupScan_spec l pool
    simp only [dupScan]
    cases hsl : dupScan pool l with
    | inl p =>
      rw [hsl] at hl
      dsimp only [DupScanSpec]
      rcases hl with ⟨x, hx, hc⟩ | ⟨hp, hpp⟩
      · obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ (branches_ne_nil r)
        refine .inl ⟨x ++ y, ?_, by rw [List.count_append]; omega⟩
        simp only [Out.branches, cross, List.mem_flatMap, List.mem_map]
        exact ⟨x, hx, y, hy, rfl⟩
      · exact .inr ⟨by simp [outPlaces, hp], hpp⟩
    | inr pool' =>
      rw [hsl] at hl
      dsimp only
      obtain ⟨hdl, hpl, hml⟩ := hl
      have hr := dupScan_spec r pool'
      cases hsr : dupScan pool' r with
      | inl p =>
        rw [hsr] at hr
        dsimp only [DupScanSpec]
        rcases hr with ⟨y, hy, hc⟩ | ⟨hp, hpp⟩
        · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (branches_ne_nil l)
          refine .inl ⟨x ++ y, ?_, by rw [List.count_append]; omega⟩
          simp only [Out.branches, cross, List.mem_flatMap, List.mem_map]
          exact ⟨x, hx, y, hy, rfl⟩
        · rcases (hml p).1 hpp with hpp | hpl'
          · exact .inr ⟨by simp [outPlaces, hp], hpp⟩
          · obtain ⟨x, hx, hpx⟩ := branch_of_outPlaces l p hpl'
            obtain ⟨y, hy, hpy⟩ := branch_of_outPlaces r p hp
            refine .inl ⟨x ++ y, ?_, ?_⟩
            · simp only [Out.branches, cross, List.mem_flatMap, List.mem_map]
              exact ⟨x, hx, y, hy, rfl⟩
            · rw [List.count_append]
              have := List.count_pos_iff.mpr hpx
              have := List.count_pos_iff.mpr hpy
              omega
      | inr ps =>
        rw [hsr] at hr
        dsimp only [DupScanSpec]
        obtain ⟨hdr, hpr, hmr⟩ := hr
        refine ⟨fun ⟨b, hb, hn⟩ => ?_, fun q hq hqp => ?_, fun q => ?_⟩
        · simp only [Out.branches, cross, List.mem_flatMap, List.mem_map] at hb
          obtain ⟨x, hx, y, hy, rfl⟩ := hb
          have hnx : x.Nodup := by by_contra h; exact hdl ⟨x, hx, h⟩
          have hny : y.Nodup := by by_contra h; exact hdr ⟨y, hy, h⟩
          refine hn (List.nodup_append.2 ⟨hnx, hny, fun a ha b hb hab => ?_⟩)
          subst hab
          exact hpr a (outPlaces_of_branch r y hy a hb)
            ((hml a).2 (.inr (outPlaces_of_branch l x hx a ha)))
        · simp only [outPlaces, List.mem_append] at hq
          rcases hq with hq | hq
          · exact hpl q hq hqp
          · exact hpr q hq ((hml q).2 (.inl hqp))
        · rw [hmr q, hml q]
          simp only [outPlaces, List.mem_append]
          tauto

/-- The place the walk reports is named twice in one output branch. -/
theorem firstDup_some [DecidableEq N] {o : Out N} {p : N} (h : firstDup o = some p) :
    BranchDuplicate o p := by
  have hs := dupScan_spec o []
  unfold firstDup at h
  cases hd : dupScan [] o with
  | inl q =>
    rw [hd] at h hs
    simp only [Option.some.injEq] at h
    subst h
    simpa [DupScanSpec] using hs
  | inr _ => rw [hd] at h; simp at h

/-- **The walk reports a place exactly when some output branch names a place twice** ([IO-011],
"Which place the message names"). -/
theorem firstDup_eq_none_iff [DecidableEq N] (o : Out N) : firstDup o = none ↔ ¬ DupBranch o := by
  constructor
  · intro h
    have hs := dupScan_spec o []
    unfold firstDup at h
    cases hd : dupScan [] o with
    | inl q => rw [hd] at h; simp at h
    | inr ps => rw [hd] at hs; exact hs.1
  · intro h
    cases hf : firstDup o with
    | none => rfl
    | some p => exact absurd ((dupBranch_iff o).2 ⟨p, firstDup_some hf⟩) h

/-- The number of `Timeout` nodes of an output spec, nested and sibling ones alike: the `<n>` of
[IO-013]'s build error, which a spec with 2 or more fails. -/
def timeoutCount : Out N → Nat
  | .timeout c => 1 + timeoutCount c
  | .and l r => timeoutCount l + timeoutCount r
  | .xor l r => timeoutCount l + timeoutCount r
  | _ => 0

/-- **The first `ForwardInput` outside the child of a `Timeout` node**, as its `(from, to)`
([IO-014]): the walk is pre-order, children left to right, and does not enter a `Timeout` node,
below which a forward is allowed. `none`: every `ForwardInput` of `o` is inside the child of a
`Timeout` node. The right-nested binary `And` / `Xor` of the reference visit the leaves in the
order the n-ary spec is written. -/
def forwardOutside : Out N → Option (N × N)
  | .forward s d => some (s, d)
  | .and l r => (forwardOutside l).or (forwardOutside r)
  | .xor l r => (forwardOutside l).or (forwardOutside r)
  | .timeout _ => none
  | .place _ => none

/-- The `from` places of every `ForwardInput` node of `o`, in pre-order ([IO-014] AC3). -/
def forwardSources : Out N → List N
  | .forward s _ => [s]
  | .and l r => forwardSources l ++ forwardSources r
  | .xor l r => forwardSources l ++ forwardSources r
  | .timeout c => forwardSources c
  | .place _ => []

/-- `o` holds an `Xor` node, at any depth. -/
def hasXor : Out N → Bool
  | .xor _ _ => true
  | .and l r => hasXor l || hasXor r
  | .timeout c => hasXor c
  | _ => false

/-- **Some `Timeout` node of `o` holds an `Xor` node in its child**, at any depth: [IO-013]'s
second build check ("One fixed timeout deposit"). It runs after the `Timeout` count check, so on
the specs it decides there is at most one `Timeout` node to search. -/
def xorInTimeout : Out N → Bool
  | .timeout c => hasXor c
  | .and l r => xorInTimeout l || xorInTimeout r
  | .xor l r => xorInTimeout l || xorInTimeout r
  | _ => false

/-- **Glossary: Same set of places.** "Two lists of places name the same set of places when every
place of each is a place of the other, whatever the order or repetition. Places are the same
under the implementation's own `Place` equality [CORE-002], [MOD-024]. Output branches are
compared this way [IO-012], [IO-015]." Place identity is equality on `N`. -/
def SameSet (a b : List N) : Prop := ∀ q, q ∈ a ↔ q ∈ b

/-- `SameSet`, as a `Bool`. -/
def sameSetB [DecidableEq N] (a b : List N) : Bool :=
  a.all (fun q => decide (q ∈ b)) && b.all (fun q => decide (q ∈ a))

/-- `sameSetB` decides `SameSet`. -/
theorem sameSetB_iff [DecidableEq N] (a b : List N) : sameSetB a b = true ↔ SameSet a b := by
  simp only [sameSetB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, SameSet]
  constructor
  · rintro ⟨h1, h2⟩ q; exact ⟨h1 q, h2 q⟩
  · intro h; exact ⟨fun q hq => (h q).1 hq, fun q hq => (h q).2 hq⟩

instance [DecidableEq N] (a b : List N) : Decidable (SameSet a b) :=
  decidable_of_iff _ (sameSetB_iff a b)

/-- **[IO-012]'s check on the branch list**: the first index `j` whose set equals the set of an
earlier entry, with the smallest such earlier index `i`, as `(i, j)`; `none` when the entries are
pairwise distinct sets. -/
def firstClash [DecidableEq N] (bs : List (List N)) : Option (Nat × Nat) :=
  (List.range bs.length).findSome? fun j =>
    ((List.range j).find? fun i => sameSetB (bs.getD i []) (bs.getD j [])).map (·, j)

/-- `firstClash` finds nothing exactly when the entries are pairwise distinct sets. -/
theorem firstClash_eq_none_iff [DecidableEq N] (bs : List (List N)) :
    firstClash bs = none ↔ bs.Pairwise (fun a b => ¬ SameSet a b) := by
  rw [List.pairwise_iff_getElem, firstClash, List.findSome?_eq_none_iff]
  constructor
  · intro h i j hi hj hij hs
    have h1 := h j (List.mem_range.2 hj)
    rw [Option.map_eq_none_iff, List.find?_eq_none] at h1
    have h2 := h1 i (List.mem_range.2 hij)
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem hj, Option.getD_some] at h2
    exact h2 ((sameSetB_iff _ _).2 hs)
  · intro h j hj
    rw [Option.map_eq_none_iff, List.find?_eq_none]
    intro i hi
    have hj' := List.mem_range.1 hj
    have hi' := List.mem_range.1 hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (Nat.lt_trans hi' hj'),
      List.getElem?_eq_getElem hj', Option.getD_some]
    intro hs
    exact h i j (Nat.lt_trans hi' hj') hj' hi' ((sameSetB_iff _ _).1 hs)

/-- **[IO-011]'s build error**, for the place `p`. -/
def msgDup [ToString N] (t : Trans N) (p : N) : String :=
  s!"output spec of transition '{t.core.name}' names place '{p}' twice in one AND branch; outputs are sets (IO-015) — a weighted output is not supported, add a second place or a follow-up transition"

/-- **[IO-013]'s build error**, for `n` `Timeout` nodes. -/
def msgTimeouts (t : Trans N) (n : Nat) : String :=
  s!"output spec of transition '{t.core.name}' has {n} Timeout nodes; an output spec has at most one, nested or not (IO-013)"

/-- **[IO-013]'s second build error**: an `Xor` node inside the child of the `Timeout` node. -/
def msgXorInTimeout (t : Trans N) : String :=
  s!"output spec of transition '{t.core.name}' has a Xor node inside the child of its Timeout node; the timeout outcome deposits one fixed set of places (IO-013)"

/-- **[IO-014]'s placement error**, for the node `ForwardInput(src, dst)`. -/
def msgForward [ToString N] (t : Trans N) (src dst : N) : String :=
  s!"output spec of transition '{t.core.name}' uses ForwardInput('{src}', '{dst}') outside the child of a Timeout node; a forward deposits only on the timeout outcome (IO-014)"

/-- **[IO-014] AC3's build error**, for a forward from the non-input place `src`. -/
def msgNonInput [ToString N] (t : Trans N) (src : N) : String :=
  s!"Transition '{t.core.name}': ForwardInput references non-input place '{src}'"

/-- **[IO-012]'s build error**, for the output branches `i` and `j`, both claiming the places
`ps`. -/
def msgAmbiguous [ToString N] (t : Trans N) (i j : Nat) (ps : List N) : String :=
  "output spec of transition '" ++ t.core.name ++ "' is ambiguous: output branches " ++
    toString i ++ " and " ++ toString j ++ " both claim {" ++
    ", ".intercalate (ps.map toString) ++ "}; no write can tell them apart (IO-012)"

/-- **The output spec `o` passes the build-time checks**, for a transition whose input places are
`inputs`, in the preamble's order: no output branch names a place twice ([IO-011]); at most one
`Timeout` node ([IO-013]); no `Xor` node inside the child of the `Timeout` node ([IO-013]); no
`ForwardInput` outside the child of a `Timeout` ([IO-014]); every `ForwardInput`'s `from` an
input place ([IO-014] AC3); no two output branches at different indices of the [IO-016]
enumeration, that is no two distinct assignments, claiming the same set of places ([IO-012]). -/
def WellFormedOut [DecidableEq N] (inputs : List N) (o : Out N) : Prop :=
  ¬ DupBranch o ∧ timeoutCount o ≤ 1 ∧ xorInTimeout o = false ∧ forwardOutside o = none ∧
    (∀ s ∈ forwardSources o, s ∈ inputs) ∧ o.branches.Pairwise (fun a b => ¬ SameSet a b)

instance [DecidableEq N] (inputs : List N) (o : Out N) : Decidable (WellFormedOut inputs o) := by
  unfold WellFormedOut; infer_instance

/-- **Glossary: Builds.** "A transition builds when it passes every build-time check. A
definition that fails one is not a transition of any net: no executor holds it, so it is never
enabled and never fires [CORE-022]."

`Builds t`: the checks before the output-spec checks pass (`PreOutputChecks`: distinct input
places [CORE-030], positive input counts [IO-002]/[IO-004], no input arc and read arc on one
place [EXEC-012]) and its output spec, if it has one, passes the build-time checks
(`WellFormedOut`) against its input places. -/
def Builds [DecidableEq N] (t : Trans N) : Prop :=
  PreOutputChecks t ∧ ∀ o, OutputSpec t = some o → WellFormedOut (inPlaces t) o

instance [DecidableEq N] (t : Trans N) : Decidable (Builds t) :=
  match h : t.out with
  | none => decidable_of_iff (PreOutputChecks t) (by
      simp only [Builds, OutputSpec, h, reduceCtorEq, false_implies, implies_true, and_true])
  | some o => decidable_of_iff (PreOutputChecks t ∧ WellFormedOut (inPlaces t) o) (by
      simp only [Builds, OutputSpec, h, Option.some.injEq, forall_eq'])

/-- The output-spec checks of the reference builder, in the order of the Output Composition
preamble, given the input places `ins` the [IO-014] AC3 check reads; the first that fails names
the error. The [IO-011] check is the walk itself: it reports a place exactly when some output
branch names a place twice (`firstDup_eq_none_iff`). -/
def checkOut [DecidableEq N] [ToString N] (t : Trans N) (ins : List N) (o : Out N) :
    Option String :=
  match firstDup o with
  | some p => some (msgDup t p)
  | none =>
  if 2 ≤ timeoutCount o then some (msgTimeouts t (timeoutCount o))
  else if xorInTimeout o then some (msgXorInTimeout t)
  else match forwardOutside o with
    | some (s, d) => some (msgForward t s d)
    | none =>
      match (forwardSources o).find? (fun s => decide (s ∉ ins)) with
      | some s => some (msgNonInput t s)
      | none =>
        match firstClash o.branches with
        | some (i, j) => some (msgAmbiguous t i j (o.branches.getD i []))
        | none => none

/-- **The reference builder**: [CORE-030]'s input-arc check (its message is a stand-in, the spec
gives none), the [IO-002]/[IO-004] count checks (stand-in `msgCount`), [EXEC-012]'s
input-and-read check (`msgInputRead`, ruling D15), then the output-spec checks of `checkOut`.
Running [CORE-030] before the count checks is this builder's choice, not the spec's: the spec
orders neither before the other, and the runtimes interleave the two per input arc. No
requirement block depends on that order; [EXEC-012] after both is the spec's.
`refBuild t = none`: `t` builds; `refBuild t = some msg`: building `t` fails with `msg`. -/
def refBuild [DecidableEq N] [ToString N] (t : Trans N) : Option String :=
  if ¬ InputsDistinct t then some "CORE-030"
  else if ¬ InputCountsPositive t then some msgCount
  else match firstInputRead t with
    | some p => some (msgInputRead t p)
    | none =>
      match t.out with
      | none => none
      | some o => checkOut t (inPlaces t) o

/- The reference builder is a witness model of the blocks that constrain building. -/
#spec_witness refBuild

/-- The output-spec checks of the reference builder pass exactly on a well-formed output spec. -/
theorem checkOut_eq_none_iff [DecidableEq N] [ToString N] (t : Trans N) (o : Out N) :
    checkOut t (inPlaces t) o = none ↔ WellFormedOut (inPlaces t) o := by
  unfold checkOut WellFormedOut
  rw [← firstClash_eq_none_iff]
  cases hd : firstDup o with
  | some p =>
    exact iff_of_false (by simp)
      (fun h => h.1 ((dupBranch_iff o).2 ⟨p, firstDup_some hd⟩))
  | none =>
  have hd := (firstDup_eq_none_iff o).1 hd
  simp only
  by_cases hc : 2 ≤ timeoutCount o
  · rw [if_pos hc]; exact iff_of_false (by simp) (fun h => by have := h.2.1; omega)
  rw [if_neg hc]
  cases hxt : xorInTimeout o with
  | true => exact iff_of_false (by simp) (fun h => by have := h.2.2.1; simp at this)
  | false =>
  simp only [Bool.false_eq_true, if_false]
  cases hf : forwardOutside o with
  | some x =>
    exact iff_of_false (by simp) (fun h => by have := h.2.2.2.1; simp at this)
  | none =>
    cases hs : (forwardSources o).find? (fun s => decide (s ∉ inPlaces t)) with
    | some s =>
      have hn : s ∉ inPlaces t := by simpa using List.find?_some hs
      exact iff_of_false (by simp)
        (fun h => hn (h.2.2.2.2.1 s (List.mem_of_find?_eq_some hs)))
    | none =>
      rw [List.find?_eq_none] at hs
      have hs' : ∀ s ∈ forwardSources o, s ∈ inPlaces t := fun s hm => by
        simpa using hs s hm
      cases hx : firstClash o.branches with
      | some x =>
        exact iff_of_false (by simp)
          (fun h => by have := h.2.2.2.2.2; simp at this)
      | none => exact iff_of_true rfl ⟨hd, by omega, trivial, rfl, hs', rfl⟩

/-- On a transition that passes the checks before the output-spec checks, the reference builder
is its output-spec checks. -/
theorem refBuild_of_pre [DecidableEq N] [ToString N] {t : Trans N} (h : PreOutputChecks t) :
    refBuild t = match t.out with
      | none => none
      | some o => checkOut t (inPlaces t) o := by
  unfold refBuild
  rw [if_neg (not_not.mpr h.1), if_neg (not_not.mpr h.2.1),
    (firstInputRead_eq_none_iff t).2 h.2.2]

/-- The reference builder accepts exactly the transitions that build. -/
theorem refBuild_eq_none_iff [DecidableEq N] [ToString N] (t : Trans N) :
    refBuild t = none ↔ Builds t := by
  by_cases hp : PreOutputChecks t
  · rw [refBuild_of_pre hp]
    cases ho : t.out with
    | none => simp [Builds, hp, OutputSpec, ho]
    | some o =>
      simp only [Builds, hp, OutputSpec, ho, Option.some.injEq, forall_eq', true_and]
      exact checkOut_eq_none_iff t o
  · refine iff_of_false ?_ (fun h => hp h.1)
    unfold refBuild
    by_cases hi : InputsDistinct t
    · by_cases hc : InputCountsPositive t
      · have hw : ¬ NoInputRead t := fun hw => hp ⟨hi, hc, hw⟩
        rw [if_neg (not_not.mpr hi), if_neg (not_not.mpr hc)]
        cases hf : firstInputRead t with
        | some p => simp
        | none => exact absurd ((firstInputRead_eq_none_iff t).1 hf) hw
      · rw [if_neg (not_not.mpr hi), if_pos hc]; simp
    · rw [if_pos hi]; simp

/-! ## Bridge lemmas: the readable forms agree with the reference definitions -/

/-- The [CORE-022] reading of `Enabled`: every input arc satisfied, every read place marked, no
inhibitor place marked. -/
theorem enabled_iff (t : Trans N) (m : CountMarking N) :
    Enabled t m ↔
      (∀ s ∈ t.core.inputs, requiredCount s.card ≤ m s.place) ∧
      (∀ p ∈ t.core.inhibitors, ¬ Marked m p) ∧
      (∀ p ∈ t.core.reads, Marked m p) := by
  simp only [Enabled, enabledNA, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    beq_iff_eq, Marked, ne_eq, Decidable.not_not, requiredCount]
  constructor
  · rintro ⟨⟨hi, hh⟩, hr⟩
    exact ⟨hi, hh, fun p hp => by have := hr p hp; omega⟩
  · rintro ⟨hi, hh, hr⟩
    exact ⟨⟨hi, hh⟩, fun p hp => by have := hr p hp; omega⟩

/-- `Consumes` is the [IO-007] consumption count of the input arc on the place, and 0 where
there is none. -/
theorem consumes_eq [DecidableEq N] (t : Trans N) (m : CountMarking N) (p : N) :
    Consumes t m p =
      match nspecAt t.core p with
      | none => 0
      | some s => consumptionCount s.card (m p) := by
  simp only [Consumes, nconsumed, consumptionCount]
  cases nspecAt t.core p <;> rfl

/-- The input arc `InputArc t p c` names is one of `t`'s input arcs, on `p`. -/
theorem inputArc_mem [DecidableEq N] {t : Trans N} {p : N} {c : Card}
    (h : InputArc t p c) : ∃ s ∈ t.core.inputs, s.place = p ∧ s.card = c := by
  obtain ⟨s, hs, hc⟩ := h
  have hp : s.place = p := by simpa using List.find?_some hs
  exact ⟨s, List.mem_of_find?_eq_some hs, hp, hc⟩

/-- A forward's timeout deposit is `forwardDeposit`. -/
theorem timeoutDeposits_forward (consumed : N → Nat) (src dst : N) :
    (Out.forward src dst).timeoutDeposits consumed = [forwardDeposit consumed src dst] := rfl

/-- `forwardDeposit` puts one token in `to` per token consumed from `from` ([IO-014] AC2). -/
theorem forwardDeposit_count [DecidableEq N] (consumed : N → Nat) (src dst : N) :
    Deposits (forwardDeposit consumed src dst) dst = consumed src := by
  simp [Deposits, depProd, forwardDeposit]

/-- A reference firing is: enabled, a deposit offered by the output spec, and the effect
`Seam.fireNC`. -/
theorem refFire_iff [DecidableEq N] (t : Trans N) (m : CountMarking N) (d : List N)
    (m' : CountMarking N) :
    RefFire t m d m' ↔
      Enabled t m ∧
        (∃ ch, deposit (Consumes t m) (OutputSpec t) ch = some d) ∧
        m' = fireNC m t.core (depProd d) := Iff.rfl

/-- The effect of a reference firing, place by place: a reset place holds exactly what was
deposited there; every other place loses what was consumed and gains what was deposited. -/
theorem refFire_apply [DecidableEq N] {t : Trans N} {m m' : CountMarking N} {d : List N}
    (h : RefFire t m d m') (p : N) :
    m' p = if ResetArc t p then Deposits d p else m p - Consumes t m p + Deposits d p := by
  obtain ⟨-, -, rfl⟩ := h
  rfl


/-- Every place a timeout deposit of a node puts a token in is named by that node. -/
theorem outPlaces_of_timeoutDeposit (consumed : N → Nat) :
    ∀ (o : Out N) (b : List N), b ∈ o.timeoutDeposits consumed → ∀ p ∈ b, p ∈ outPlaces o
  | .place q, b, hb, p, hp => by
    simp only [Out.timeoutDeposits, List.mem_singleton] at hb
    subst hb
    simpa [outPlaces] using hp
  | .forward _ dst, b, hb, p, hp => by
    simp only [Out.timeoutDeposits, List.mem_singleton] at hb
    subst hb
    simp [outPlaces, List.eq_of_mem_replicate hp]
  | .and l r, b, hb, p, hp => by
    simp only [Out.timeoutDeposits, cross, List.mem_flatMap, List.mem_map] at hb
    obtain ⟨x, hx, y, hy, rfl⟩ := hb
    simp only [outPlaces, List.mem_append]
    rcases List.mem_append.1 hp with h | h
    · exact .inl (outPlaces_of_timeoutDeposit consumed l x hx p h)
    · exact .inr (outPlaces_of_timeoutDeposit consumed r y hy p h)
  | .xor l r, b, hb, p, hp => by
    simp only [Out.timeoutDeposits, List.mem_append] at hb
    simp only [outPlaces, List.mem_append]
    rcases hb with h | h
    · exact .inl (outPlaces_of_timeoutDeposit consumed l b h p hp)
    · exact .inr (outPlaces_of_timeoutDeposit consumed r b h p hp)
  | .timeout c, b, hb, p, hp => outPlaces_of_timeoutDeposit consumed c b hb p hp

/-- The node `findTimeout` returns names only places its tree names. -/
theorem outPlaces_of_findTimeout :
    ∀ (o c : Out N), o.findTimeout = some c → ∀ p ∈ outPlaces c, p ∈ outPlaces o
  | .place _, c, h, _, _ => by simp [Out.findTimeout] at h
  | .forward _ _, c, h, _, _ => by simp [Out.findTimeout] at h
  | .timeout c', c, h, p, hp => by
    simp only [Out.findTimeout, Option.some.injEq] at h
    subst h
    exact hp
  | .and l r, c, h, p, hp => by
    simp only [Out.findTimeout] at h
    simp only [outPlaces, List.mem_append]
    cases hl : l.findTimeout with
    | some c' =>
      rw [hl, Option.some_or, Option.some.injEq] at h
      subst h
      exact .inl (outPlaces_of_findTimeout l c' hl p hp)
    | none =>
      rw [hl, Option.none_or] at h
      exact .inr (outPlaces_of_findTimeout r c h p hp)
  | .xor l r, c, h, p, hp => by
    simp only [Out.findTimeout] at h
    simp only [outPlaces, List.mem_append]
    cases hl : l.findTimeout with
    | some c' =>
      rw [hl, Option.some_or, Option.some.injEq] at h
      subst h
      exact .inl (outPlaces_of_findTimeout l c' hl p hp)
    | none =>
      rw [hl, Option.none_or] at h
      exact .inr (outPlaces_of_findTimeout r c h p hp)

/-- A node that holds no `Xor` node has exactly one timeout deposit. -/
theorem timeoutDeposits_singleton (consumed : N → Nat) :
    ∀ (c : Out N), hasXor c = false → ∃ d, c.timeoutDeposits consumed = [d]
  | .place p, _ => ⟨[p], rfl⟩
  | .forward _ _, _ => ⟨_, rfl⟩
  | .xor _ _, h => by simp [hasXor] at h
  | .timeout c, h => timeoutDeposits_singleton consumed c h
  | .and l r, h => by
    simp only [hasXor, Bool.or_eq_false_iff] at h
    obtain ⟨x, hx⟩ := timeoutDeposits_singleton consumed l h.1
    obtain ⟨y, hy⟩ := timeoutDeposits_singleton consumed r h.2
    exact ⟨x ++ y, by simp [Out.timeoutDeposits, hx, hy, cross]⟩

/-- On a spec with no `Xor` node inside a `Timeout` child, the `Timeout` child `findTimeout`
returns holds no `Xor` node. -/
theorem hasXor_findTimeout :
    ∀ (o c : Out N), xorInTimeout o = false → o.findTimeout = some c → hasXor c = false
  | .place _, _, _, h => by simp [Out.findTimeout] at h
  | .forward _ _, _, _, h => by simp [Out.findTimeout] at h
  | .timeout _, c, hx, h => by
    simp only [Out.findTimeout, Option.some.injEq] at h
    subst h
    exact hx
  | .and l r, c, hx, h => by
    simp only [xorInTimeout, Bool.or_eq_false_iff] at hx
    simp only [Out.findTimeout] at h
    cases hl : l.findTimeout with
    | some c' =>
      rw [hl, Option.some_or, Option.some.injEq] at h
      subst h
      exact hasXor_findTimeout l c' hx.1 hl
    | none =>
      rw [hl, Option.none_or] at h
      exact hasXor_findTimeout r c hx.2 h
  | .xor l r, c, hx, h => by
    simp only [xorInTimeout, Bool.or_eq_false_iff] at hx
    simp only [Out.findTimeout] at h
    cases hl : l.findTimeout with
    | some c' =>
      rw [hl, Option.some_or, Option.some.injEq] at h
      subst h
      exact hasXor_findTimeout l c' hx.1 hl
    | none =>
      rw [hl, Option.none_or] at h
      exact hasXor_findTimeout r c hx.2 h

/-- **One fixed timeout deposit** ([IO-013]): the timeout outcome of a transition that builds is
one deposit, every place the `Timeout` child names receiving its tokens. -/
theorem timeoutOutcome_unique [DecidableEq N] {t : Trans N} (hb : Builds t) {consumed : N → Nat}
    {d d' : List N} (h : TimeoutOutcome t consumed d) (h' : TimeoutOutcome t consumed d') :
    d = d' := by
  obtain ⟨o, c, ho, hc, hd⟩ := h
  obtain ⟨o', c', ho', hc', hd'⟩ := h'
  rw [ho, Option.some.injEq] at ho'
  subst ho'
  rw [hc, Option.some.injEq] at hc'
  subst hc'
  obtain ⟨e, he⟩ := timeoutDeposits_singleton consumed c
    (hasXor_findTimeout o c (hb.2 o ho).2.2.1 hc)
  rw [he, List.mem_singleton] at hd hd'
  rw [hd, hd']

/-- Every place a reference firing deposits in is an output place of the transition: an action
branch and a timeout deposit put tokens only in places the output spec names, and a transition
with no output spec deposits nothing. -/
theorem refFire_outputs [DecidableEq N] {t : Trans N} {m m' : N → Nat}
    {d : List N} (h : RefFire t m d m') : ∀ p, Produced d p → OutputArc t p := by
  obtain ⟨-, ⟨ch, hd⟩, -⟩ := h
  intro p hp
  cases ho : t.out with
  | none =>
    rw [ho] at hd
    cases ch with
    | action i =>
      cases i with
      | zero =>
        simp only [deposit, Option.some.injEq] at hd
        subst hd
        exact absurd hp (by simp [Produced])
      | succ _ => simp [deposit] at hd
    | timedOut _ => simp [deposit] at hd
  | some o =>
    rw [ho] at hd
    refine ⟨o, ho, ?_⟩
    cases ch with
    | action i =>
      exact outPlaces_of_branch o d (List.mem_of_getElem? hd) p hp
    | timedOut j =>
      simp only [deposit, Option.bind_eq_some_iff] at hd
      obtain ⟨c, hc, hj⟩ := hd
      exact outPlaces_of_findTimeout o c hc p
        (outPlaces_of_timeoutDeposit _ c d (List.mem_of_getElem? hj) p hp)

end Libpetri.Spec
