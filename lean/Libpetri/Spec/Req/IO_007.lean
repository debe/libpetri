import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.Glossary

set_option linter.missingDocs true

/-!
# IO-007: requiredCount and consumptionCount contract (`spec/02-input-output-specs.md`)

IO-007 is a pure-function requirement (kind F): it fixes the two functions every input
cardinality exposes, `requiredCount()` and `consumptionCount(available)`, and says that the second
fails below the first. The statement is a predicate over a *cardinality contract*: a pair of
functions of that shape, with a failing call read as `none`. The witness is the reference
contract, built from the glossary's `requiredCount` and `consumptionCount` (the functions the
reference firing semantics enables and consumes with), guarded by the precondition.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## The model: a cardinality contract -/

/-- A cardinality contract: the two functions of [IO-007] for every input cardinality.
`consume c a = none` reads as "calling `consumptionCount(a)` on `c` is an error". -/
structure CardContract where
  /-- `requiredCount()` of each cardinality. -/
  required : Card → Nat
  /-- `consumptionCount(available)` of each cardinality: `some k` returns `k`, `none` fails. -/
  consume : Card → Nat → Option Nat

/-- The reference contract: the glossary's `requiredCount` (`Card.required`, which the
reference enablement `Seam.enabledNA` reads) and `consumptionCount` (which the reference
consumption `Seam.nconsumed` computes), the latter failing below the required count. -/
def ioRefContract : CardContract where
  required := requiredCount
  consume c a := if requiredCount c ≤ a then some (consumptionCount c a) else none

/- The reference contract is the witness model of IO-007's `holds` theorem. -/
#spec_witness ioRefContract

/-! ## IO-007: requiredCount and consumptionCount Contract -/

requirement IO_007
  id "IO-007"
  title "requiredCount and consumptionCount Contract"
  kind F
  scope "all input cardinalities"
  source verbatim "spec/02-input-output-specs.md"
  quote "The required count *shall* be 1 for `One` and `All`, `n` for `Exactly(n)` and `m` for `AtLeast(m)`."
        "*While* `available` is at least the required count, `consumptionCount(available)` *shall* return 1 for `One`, `n` for `Exactly(n)` and `available` for `All` and `AtLeast(m)`."
        "*If* `consumptionCount(available)` is called with `available` less than the required count, *then* the call *shall* fail with an error."
  reading "requiredCount() is 1 for One, n for Exactly(n), 1 for All and m for AtLeast(m);"
          "for every cardinality c and every available ≥ requiredCount(c), consumptionCount(available) returns 1 for One, n for Exactly(n), available for All and available for AtLeast(m);"
          "for every cardinality c and every available < requiredCount(c), consumptionCount(available) fails (none)."
  assumes "A contract is the pair of functions of one implementation; a call that raises (an exception, a panic, an assertion failure) is read as `none`, a call that returns `k` as `some k`. Which error is raised, and its message, are not part of the statement."
          "AC1 (each variant returns the values of the table) is the first two lines: the first line is the requiredCount column, the second the consumptionCount column on every call the third line allows."
          "AC2 (calling consumptionCount with insufficient tokens is an error) is the third line."
          "The counts n and m range over all naturals. That Exactly(n) and AtLeast(m) are built only with n, m ≥ 1 is IO-002 AC1 and IO-004 AC1, not this block's subject; the table holds for 0 too."
          "'(matching) tokens' in the definition of requiredCount() is read at the granularity of a token count: which tokens of a place count as matching (the ν correlation of NU-020) is decided before the count reaches these functions, so `available` is already the matching count."
          "That an executor calls consumptionCount only on an enabled transition, where every input place holds its required count, is enablement (CORE-022, IO-005), not this block's subject; that a firing removes exactly consumptionCount(available) tokens is CORE-030's subject (glossary: Consume, bridge lemma `consumes_eq`)."
  signoff "2026-11-13 1860eb65b8a890ff ai"
  statement : CardContract → Prop :=
    fun K =>
      (∀ c, K.required c =
        match c with
        | .one => 1
        | .exactly n => n
        | .all => 1
        | .atLeast m => m) ∧
      (∀ c a, K.required c ≤ a → K.consume c a = some
        (match c with
         | .one => 1
         | .exactly n => n
         | .all => a
         | .atLeast _ => a)) ∧
      (∀ c a, a < K.required c → K.consume c a = none)

/- The pinned readable form of IO-007: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.IO_007 : CardContract → Prop :=
fun K =>
  (∀ (c : Card),
      K.required c =
        match c with
        | Card.one => 1
        | Card.exactly n => n
        | Card.all => 1
        | Card.atLeast m => m) ∧
    (∀ (c : Card) (a : ℕ),
        K.required c ≤ a →
          K.consume c a =
            some
              (match c with
              | Card.one => 1
              | Card.exactly n => n
              | Card.all => a
              | Card.atLeast n => a)) ∧
      ∀ (c : Card), ∀ a < K.required c, K.consume c a = none
-/
#guard_msgs in #print IO_007

/-- The reference contract satisfies IO-007: `Card.required` is the requiredCount column,
`consumptionCount` (`available` where `Card.consumesAll`, else `Card.required`) is the
consumptionCount column, and the guard makes every call below the required count fail. -/
@[evidence holds IO_007]
theorem IO_007_reference : IO_007 ioRefContract := by
  refine ⟨fun c => ?_, fun c a h => ?_, fun c a h => ?_⟩
  · cases c <;> rfl
  · show (if requiredCount c ≤ a then _ else _) = _
    have h' : requiredCount c ≤ a := h
    rw [if_pos h']
    cases c <;> rfl
  · show (if requiredCount c ≤ a then _ else _) = _
    have h' : a < requiredCount c := h
    rw [if_neg (Nat.not_le.2 h')]

/-! ### Examples: wrong contracts -/

/-- A contract in which `All` needs no token: its requiredCount is 0, and its consumption count
is the reference one from 0 tokens up. -/
def io007_allNeedsNothing : CardContract where
  required c := match c with
    | .all => 0
    | c => requiredCount c
  consume c a := match c with
    | .all => some a
    | c => ioRefContract.consume c a

/-- ✗ An `All` that needs no token violates IO-007 (first line): its requiredCount is 0, not 1;
with it, firing an `All` arc from an empty place would be enabled. -/
@[evidence forbids IO_007]
theorem IO_007_forbids_allNeedsNothing : ¬ IO_007 io007_allNeedsNothing := by
  intro h
  exact absurd (h.1 .all) (by decide)

/-- Mutant reading of IO-007 that drops the first line: whatever the required count, the
consumption count is the table's on every call it allows, and every other call fails. -/
def IO_007_mutant_dropRequired (K : CardContract) : Prop :=
  (∀ c a, K.required c ≤ a → K.consume c a = some
    (match c with
     | .one => 1
     | .exactly n => n
     | .all => a
     | .atLeast _ => a)) ∧
  (∀ c a, a < K.required c → K.consume c a = none)

/-- A contract that requires nothing of any cardinality and never fails: every call returns the
table's consumption count. -/
def io007_requiresNothing : CardContract where
  required _ := 0
  consume c a := some (match c with
    | .one => 1
    | .exactly n => n
    | .all => a
    | .atLeast _ => a)

/-- The contract that requires nothing kills the first mutant: it meets the mutant (the
consumption column is right and no call is below a required count of 0) but not IO-007 (`One`
requires 0 tokens, not 1). -/
@[evidence mutant IO_007]
theorem IO_007_mutant_dropRequired_killed :
    IO_007_mutant_dropRequired io007_requiresNothing ∧ ¬ IO_007 io007_requiresNothing := by
  refine ⟨⟨fun c a _ => rfl, fun c a h => absurd h (Nat.not_lt_zero a)⟩, fun h => ?_⟩
  exact absurd (h.1 .one) (by decide)

/-- Mutant reading of IO-007 that drops the second line: the required counts are the table's and
calls below them fail, but a call that is allowed may return anything. -/
def IO_007_mutant_dropConsumption (K : CardContract) : Prop :=
  (∀ c, K.required c =
    match c with
    | .one => 1
    | .exactly n => n
    | .all => 1
    | .atLeast m => m) ∧
  (∀ c a, a < K.required c → K.consume c a = none)

/-- A contract in which `AtLeast(m)` consumes only `m`, its required count, instead of draining
the place: the plausible misreading of "at least". -/
def io007_atLeastTakesMinimum : CardContract where
  required := requiredCount
  consume c a := if requiredCount c ≤ a then some (requiredCount c) else none

/-- The minimum-taking `AtLeast` kills the second mutant: it meets the mutant (required counts
and failures as the table says) but not IO-007 (`AtLeast(1)` with 2 available returns 1, not
2). -/
@[evidence mutant IO_007]
theorem IO_007_mutant_dropConsumption_killed :
    IO_007_mutant_dropConsumption io007_atLeastTakesMinimum ∧
      ¬ IO_007 io007_atLeastTakesMinimum := by
  refine ⟨⟨fun c => ?_, fun c a h => ?_⟩, fun h => ?_⟩
  · cases c <;> rfl
  · simp only [io007_atLeastTakesMinimum] at h ⊢
    rw [if_neg (by omega)]
  · have := h.2.1 (.atLeast 1) 2 (by decide)
    exact absurd this (by decide)

/-- Mutant reading of IO-007 that drops the third line: the table is right on every call it
allows, but a call below the required count need not fail. -/
def IO_007_mutant_dropError (K : CardContract) : Prop :=
  (∀ c, K.required c =
    match c with
    | .one => 1
    | .exactly n => n
    | .all => 1
    | .atLeast m => m) ∧
  (∀ c a, K.required c ≤ a → K.consume c a = some
    (match c with
     | .one => 1
     | .exactly n => n
     | .all => a
     | .atLeast _ => a))

/-- A contract that never fails: the reference counts, with `consumptionCount` returning its
value even below the required count (the unguarded glossary function). -/
def io007_neverFails : CardContract where
  required := requiredCount
  consume c a := some (consumptionCount c a)

/-- The contract that never fails kills the third mutant: it meets the mutant (both columns are
right) but not IO-007 (`One` with 0 available returns 1 instead of failing). -/
@[evidence mutant IO_007]
theorem IO_007_mutant_dropError_killed :
    IO_007_mutant_dropError io007_neverFails ∧ ¬ IO_007 io007_neverFails := by
  refine ⟨⟨fun c => ?_, fun c a _ => ?_⟩, fun h => ?_⟩
  · cases c <;> rfl
  · cases c <;> rfl
  · have := h.2.2 .one 0 (by decide)
    exact absurd this (by decide)

/-! ### Non-vacuity: the reference contract and a reference firing -/

/-- The transition of the example: one `AtLeast(2)` input arc on place `0`, nothing else. -/
def io007_t : Trans Nat :=
  { core :=
      { name := "t", inputs := [{ place := 0, card := .atLeast 2 }], inhibitors := [], reads := [],
        resets := [] },
    out := none }

/-- The marking of the example: three tokens in every place. -/
def io007_m : Nat → Nat := fun _ => 3

/-- The marking after the example's firing: place `0` drained, the rest untouched. -/
def io007_m' : Nat → Nat := fun n => if n = 0 then 0 else 3

/-- Every line of IO-007 is exercised by the reference contract, and the contract is the one the
reference firing uses: `AtLeast(2)` requires 2, returns `available` (3) with 3 available and
fails with 1; `Exactly(2)` returns 2 with 3 available; and a reference firing of an `AtLeast(2)`
arc from a place holding 3 consumes `consumptionCount(3) = 3`, draining it. -/
@[evidence nonvacuous IO_007]
theorem IO_007_nonvacuous :
    ioRefContract.required (.atLeast 2) = 2 ∧
      ioRefContract.consume (.atLeast 2) 3 = some 3 ∧
      ioRefContract.consume (.exactly 2) 3 = some 2 ∧
      ioRefContract.consume (.atLeast 2) 1 = none ∧
      Consumes io007_t io007_m 0 = consumptionCount (.atLeast 2) 3 ∧
      Fire RefFire io007_t io007_m io007_m' := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, [], by decide, ⟨.action 0, rfl⟩, ?_⟩
  funext n
  by_cases h : n = 0
  · subst h; rfl
  · simp [io007_m', h, Ne.symm h, fireNC, depProd, nconsumed, nspecAt, io007_t, io007_m]

end Libpetri.Spec
