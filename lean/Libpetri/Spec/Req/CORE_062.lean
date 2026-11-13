import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryContext

set_option linter.missingDocs true

/-!
# CORE-062: Context output access (`spec/01-core-model.md`)

CORE-062 is a pure-function requirement (kind F) over a transition context `C : Ctx N T V`
(`Spec/GlossaryContext.lean`) and a value projection `value : T → V`, which the output lines do not
use: it is there so that CORE-060 to CORE-063 share one signature. The output accessor takes the transition, the buffer the action has
declared so far (places and values, in the order declared), a place and the values of one call,
and returns `none` when the call reports an error, `some` of the buffer after the call otherwise.
The single form `output(place, value)` is the call with the one value `[value]`.

The two lines: on an output place of the transition, the call appends one entry per value, in the
order of the values, after everything declared before, so a call with no values leaves the buffer
as it was and succeeds (line 1); on a place that is not an output place, the call reports an error
for every list of values, the empty one included (line 2). Derived: the single form is the bulk
form with one value (`core062_single`); the bulk form is the single form repeated once per value
on an output place (`core062_bulk_repeated`), and differs from it only by the empty call on an
undeclared place (`core062_empty_undeclared`), which is what "validates the place exactly once"
adds; a call that reports an error leaves no entry on its place in any buffer the action goes on
to build (`core062_error_declares_nothing`, "declare no token" and AC3's "no partial output", which
the type of the output accessor carries); and every buffer built by successful calls names output
places only, so an action that
writes through the context deposits only in the output places of its transition
(`core062_deposits_outputs`, the bridge to [CORE-035] line 1 and [CONC-026] line 2).

The witness is the reference context `refCtx`. One wrong context per load-bearing clause is
killed: bulk values in reverse order, new entries put ahead of the earlier ones, repeated values
collapsed, an empty bulk call refused on an output place, a check made per value (so an empty call
on an undeclared place succeeds), and an undeclared place answered by silently producing nothing.
A context with one allowed set for the input and the output places is forbidden.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## CORE-062: Context Output Access -/

requirement CORE_062
  id "CORE-062"
  title "Context Output Access"
  kind F
  scope "the transition context of every implementation, except output calls made after the firing has ended with the timeout outcome"
  source verbatim "spec/01-core-model.md"
  quote "*When* an action calls `output(place, value)` on an output place of its transition, the call *shall* declare one token carrying `value` on that place, after every token the action declared before."
        "*When* an action calls the bulk form with a sequence of values on an output place of its transition, the call *shall* declare one token per value on that place, in the order of the sequence, after every token the action declared before."
        "*When* an action calls the bulk form with no values on an output place of its transition, the call *shall* declare no token and return successfully."
        "*If* an action calls `output(place, value)` or the bulk form on a place that does not resolve to an output place of its transition ([MOD-031]), *then* the call *shall* report an error and declare no token, also when it passes no values ([CORE-063])."
        "These four sentences do not govern an output call made after the firing has ended with the timeout outcome ([IO-013]); such a call declares no token that the firing deposits."
  reading "For every value projection value, every context C, every transition t, every buffer e (the places and values the action declared before the call, in order), every place p and every list of values vs:"
          "if p is an output place of t, the output call on t, e, p and vs succeeds and returns e followed by one entry (p, v) for each v in vs, in the order of vs;"
          "if p is not an output place of t, the output call on t, e, p and vs reports an error, whatever vs is, the empty list included."
  assumes "The model is the pair (value, C), as in CORE-060, so that the context blocks CORE-060 to CORE-063 share one signature; the value projection value plays no part in the output lines. C is a transition context (Ctx, Spec/GlossaryContext.lean). Its output accessor takes the transition, the buffer of places and values the action has declared so far in the firing, a place and the values of one call, and returns none when the call reports an error and some of the new buffer otherwise. The single form output(place, value) is the call with the one value [value]; every language shape of the bulk form (Java varargs and Iterable, TypeScript rest parameters, Rust and Python output_many) is the call with the values in iteration order. A value list is finite and fully known: a value source that fails part way (a Python iterable that raises, a Rust iterator that panics) is outside the block. The witness is the reference context refCtx."
          "Java API shape: the single form is the overload a call resolves to. Java declares output(Place<T>, T), the varargs output(Place<T>, T...) and output(Place<T>, Iterable<? extends T>) (the output overloads of TransitionContext in java/src/main/java/org/libpetri/core/TransitionContext.java). On a place whose token type is a supertype of a collection type, such as Place<Object>, a call output(place, value) whose value has a static type that is an Iterable resolves to the Iterable overload (JLS 15.12.2: the first phase, without varargs, already matches it with T = Object), so it declares one token per element, not one token carrying the collection. The block reads such a call as the bulk call it resolves to, with the elements in iteration order; a caller that wants one token holding the collection casts the value to the place's type. The built-in transform and fork pass a value of static type Object and so take the single form (java/src/main/java/org/libpetri/core/TransitionAction.java:104-107). This is the shape of the Java API (kind N), not a runtime defect, and no line is weakened for it."
          "An output place is a place the transition's output spec names (OutputArc: the glossary's Output arc, IO-017's allPlaces), so the targets of ForwardInput nodes and the places of a Timeout child are output places. Every runtime checks the place against that set: Rust require_output (rust/libpetri-core/src/context.rs:462-473), Java requireOutput (TransitionContext.requireOutput in java/src/main/java/org/libpetri/core/TransitionContext.java, called by every output overload), TypeScript requireOutput (typescript/src/core/transition-context.ts:196-198 and :227-233), Python require_output (rust/libpetri-py/src/action.rs, called by output and output_many). The place an action names is the place the call resolves to, as the fourth quoted sentence says (MOD-031): after instancing or port binding, Java, TypeScript and the Python binding adapter map a declared place the action names to the composed place first (MOD-031, W8)."
          "Declaring a token is appending it to the firing's emission buffer. When the buffer enters the marking (at completion, or earlier through a flush) is EXEC-020's and ruling D17's, and that a firing that ends with the completion of its action deposits exactly that emission is CORE-050's. core062_deposits_outputs joins the two: for an action that writes through a context satisfying CORE-062 (ThroughCtx), every place a reference action firing deposits in is an output place of the transition."
          "The block does not govern an output call made after the firing has ended with the timeout outcome (IO-013), as the fifth quoted sentence says; the markdown lists IO-013 and IO-017 (the output places) among the dependencies. After it, Java and TypeScript detach the action's collector, and an output call on an output place still returns normally but its token is counted and dropped (TransitionContext.detachForTimeout in java/src/main/java/org/libpetri/core/TransitionContext.java and typescript/src/core/transition-context.ts); line 1 does not describe those calls, and IO-013 says that no output of such an action is deposited."
          "Line 1 compares lists: the new entries come after the old buffer, one per value with its repetitions, in the order of the values. A context that writes the values of one call in reverse order meets the reading 'one token per value, as a multiset' and violates line 1 (CORE_062_mutant_bulkAnyOrder_killed). A context that puts the new entries ahead of the earlier ones meets the reading 'the buffer holds the earlier and the new tokens' and violates line 1 (CORE_062_mutant_bufferAnyOrder_killed). A context that collapses repeated values meets the reading 'every value gets a token' and violates line 1 (CORE_062_mutant_eachValue_killed)."
          "Line 2 reads 'results in an error' as 'the call reports an error and declares nothing' (ruling D63 (a)): Rust returns an error, Java and TypeScript throw, Python raises. Whether the firing then fails depends on whether the action lets the error out (EXEC-030), which is not this block's. A context that answers an undeclared place by silently producing nothing meets the reading 'producing to an undeclared place yields no token' and violates line 2 (CORE_062_mutant_silentDrop_killed). A context with one allowed set for the input and the output places is forbidden (CORE_062_forbids_arcPlaces)."
          "A call that reports an error returns none and so leaves the buffer as it was: the type of the output accessor has no room for a failed call that changed the buffer, so the clause 'declare no token' of the fourth sentence and the 'no partial output' of AC3 are carried by the type, not by a line, and no wrong context of this type can append a prefix and then report an error. Their observable content is core062_error_declares_nothing: a buffer built by successful calls, so also by an action that catches the error and goes on, holds no entry on a place that is not an output place. A bulk call names one place, so a check made per value fails on the first value before anything is appended, and the only case in which checking once up front (AC3) and checking per value differ is the call with no values on an undeclared place. Every runtime checks before it iterates (the four locations above), so that call is an error: line 2 says so for the empty list too. A context that checks per value meets the reading 'every token produced to an undeclared place is an error' and violates line 2 (CORE_062_mutant_perValue_killed); core062_empty_undeclared shows that this call is the one difference between the bulk form and the single form repeated."
          "The stamp of a declared token is not this block's: V holds values, and the buffer carries no creation timestamp. That an output token carries the current reading of the epoch clock is CORE-035 AC2 (with TIME-015 and CORE-011, whose executor line is the W11 block), and both runtime shapes meet it: Rust's output_many reads the clock once for the whole call (rust/libpetri-core/src/context.rs:448), Java and TypeScript read it for each value as it is added; either way the stamps of one call are current readings and do not decrease. No block relies on one stamp per value. A value source that fails part way leaves open whether the tokens it yielded before failing stay in the buffer: AC3's 'no partial output' is about the undeclared-place error only, and the markdown is silent on such a source. Producing a ready-made token (Java's output(Place, Token), TypeScript's outputToken) is not in the spec and not part of the block. The method names and signatures per language are API shape (kind N), recorded in AC2 and not in the formula."
          "AC1 (output(place, value) declares a single token on the given output place) is line 1 with one value: core062_single."
          "AC2 (a bulk form produces one token per value in iteration order; the language shapes) is line 1: core062_bulk_repeated shows that on an output place the bulk call is the single call repeated once per value, in order. The language shapes are API shape (kind N), recorded in the AC and not in the formula."
          "AC3 (the bulk form validates the place exactly once and reports an error before appending any token if the place is not declared) is line 2 for every list of values, with the reading of none above: no partial output (core062_error_declares_nothing), and an error also for the empty call. 'Exactly once' is the cost of the check (quality), not encoded beyond that."
          "AC4 (an empty bulk call is a no-op and returns successfully) is line 1 with the empty list, on a declared output place: core062_empty_declared. On an undeclared place the empty call is an error (line 2, AC3); the spec edit CORE-062-ac4 says so in the AC."
          "AC5 (producing to an undeclared output place results in an error) is line 2."
          "The test derivation is CORE_062_nonvacuous: an action that calls output(place, value) through the reference context builds the buffer [(2, 5)], and the reference action firing deposits the token in place 2; the bulk call with the three values 5, 6 and 7 appends three entries in that order, and on a transition whose only output branch names place 2 three times the reference firing deposits the three tokens in place 2 in that order; the bulk call on a foreign place reports an error, so nothing is appended."
  signoff "2026-11-13 fe09b40624b5af42 ai"
  statement : ∀ {N T V : Type} [DecidableEq N], (T → V) → Ctx N T V → Prop :=
    fun _value C =>
      (∀ t e p vs, OutputArc t p → C.output t e p vs = some (e ++ vs.map fun v => (p, v))) ∧
      (∀ t e p vs, ¬ OutputArc t p → C.output t e p vs = none)

/- The pinned readable form of CORE-062: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CORE_062 : {N T V : Type} → [DecidableEq N] → (T → V) → Ctx N T V → Prop :=
fun {N T V} [DecidableEq N] _value C =>
  (∀ (t : Reference.Trans N) (e : List (N × V)) (p : N) (vs : List V),
      OutputArc t p → C.output t e p vs = some (e ++ List.map (fun v => (p, v)) vs)) ∧
    ∀ (t : Reference.Trans N) (e : List (N × V)) (p : N) (vs : List V), ¬OutputArc t p → C.output t e p vs = none
-/
#guard_msgs in #print CORE_062

/-! ### The two lines, named (for the mutants) -/

section Lines

variable {N T V : Type} [DecidableEq N]

/-- Line 1 of CORE-062: on an output place the call appends one entry per value, in order. -/
def core062_line1 (_value : T → V) (C : Ctx N T V) : Prop :=
  ∀ t e p vs, OutputArc t p → C.output t e p vs = some (e ++ vs.map fun v => (p, v))

/-- Line 2 of CORE-062: on any other place the call reports an error, for every list of values. -/
def core062_line2 (_value : T → V) (C : Ctx N T V) : Prop :=
  ∀ t e p vs, ¬ OutputArc t p → C.output t e p vs = none

/-- CORE-062 is its two lines. -/
theorem core062_iff (value : T → V) (C : Ctx N T V) :
    CORE_062 value C ↔ core062_line1 value C ∧ core062_line2 value C :=
  Iff.rfl

end Lines

/-! ### The reference -/

/-- ✓ The reference context satisfies CORE-062, whatever the value projection. -/
@[evidence holds CORE_062]
theorem CORE_062_reference {N T V : Type} [DecidableEq N] (value : T → V) :
    CORE_062 value (refCtx (N := N) value) := by
  refine ⟨?_, ?_⟩
  · intro t e p vs hp; simp [refCtx, hp]
  · intro t e p vs hp; simp [refCtx, hp]

/-! ### Consequences: single form, repeated single form, the empty call -/

section Derived

variable {N T V : Type} [DecidableEq N]

/-- **AC1**: the single form on an output place appends one entry after the buffer. -/
theorem core062_single {value : T → V} {C : Ctx N T V} (h : CORE_062 value C) {t : Trans N}
    {p : N} (hp : OutputArc t p) (e : List (N × V)) (v : V) :
    C.output t e p [v] = some (e ++ [(p, v)]) := by
  rw [h.1 t e p [v] hp]; rfl

/-- **AC4**: on an output place, the call with no values succeeds and leaves the buffer as it
was. -/
theorem core062_empty_declared {value : T → V} {C : Ctx N T V} (h : CORE_062 value C)
    {t : Trans N} {p : N} (hp : OutputArc t p) (e : List (N × V)) : C.output t e p [] = some e := by
  rw [h.1 t e p [] hp]; simp

/-- The single form repeated once per value, from the buffer `e`: the result of the last call,
or the first error. -/
def core062_repeat (C : Ctx N T V) (t : Trans N) (p : N) : List (N × V) → List V →
    Option (List (N × V))
  | e, [] => some e
  | e, v :: vs => (C.output t e p [v]).bind fun e' => core062_repeat C t p e' vs

/-- **AC2**: on an output place, the bulk call is the single call repeated once per value, in
order. -/
theorem core062_bulk_repeated {value : T → V} {C : Ctx N T V} (h : CORE_062 value C)
    {t : Trans N} {p : N} (hp : OutputArc t p) (e : List (N × V)) (vs : List V) :
    C.output t e p vs = core062_repeat C t p e vs := by
  induction vs generalizing e with
  | nil => rw [core062_empty_declared h hp]; rfl
  | cons v vs ih =>
    rw [h.1 t e p (v :: vs) hp, core062_repeat, core062_single h hp, Option.bind_some, ← ih,
      h.1 t _ p vs hp]
    simp

/-- **AC3**: on an undeclared place the bulk call and the repeated single call agree whenever
there is a value, and differ on the empty call: the bulk call reports an error, the repetition of
zero calls reports nothing. This is the one observable content of "validates the place exactly
once" for a call that names one place. -/
theorem core062_empty_undeclared {value : T → V} {C : Ctx N T V} (h : CORE_062 value C)
    {t : Trans N} {p : N} (hp : ¬ OutputArc t p) (e : List (N × V)) :
    (∀ vs, vs ≠ [] → C.output t e p vs = core062_repeat C t p e vs) ∧
      C.output t e p [] = none ∧ core062_repeat C t p e [] = some e := by
  refine ⟨fun vs hne => ?_, h.2 t e p [] hp, rfl⟩
  cases vs with
  | nil => exact absurd rfl hne
  | cons v vs => rw [h.2 t e p _ hp, core062_repeat, h.2 t e p [v] hp]; rfl

/-- A context that satisfies CORE-062 appends only on output places. -/
theorem core062_outputsOnlyDeclared {value : T → V} {C : Ctx N T V} (h : CORE_062 value C) :
    OutputsOnlyDeclared C := by
  intro t e p vs e' hc
  by_cases hp : OutputArc t p
  · rw [h.1 t e p vs hp, Option.some.injEq] at hc
    subst hc
    refine ⟨_, rfl, fun x hx => ?_⟩
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
    exact hp
  · rw [h.2 t e p vs hp] at hc; cases hc

/-- **Sentence 4, "declare no token"; AC3, "no partial output"**: under CORE-062, a buffer built
by successful output calls on `t` holds no entry on a place that is not an output place of `t`.
An action that calls on such a place, catches the error and goes on, therefore never has a token
of that call in its emission. -/
theorem core062_error_declares_nothing {value : T → V} {C : Ctx N T V} (h : CORE_062 value C)
    {t : Trans N} {p : N} (hp : ¬ OutputArc t p) {e : List (N × V)} (hb : Built C t e) :
    ∀ x ∈ e, x.1 ≠ p := by
  intro x hx heq
  exact hp (heq ▸ built_outputs (core062_outputsOnlyDeclared h) hb x hx)

/-- **Bridge to [CORE-035] line 1 and [CONC-026] line 2**: an action that writes through a
context satisfying CORE-062 deposits, in a reference action firing, only in output places of its
transition. -/
theorem core062_deposits_outputs {value : T → V} {C : Ctx N T V} {val : T → V}
    {a : ActionRel N T} (h : CORE_062 value C) (ha : ThroughCtx C val a) {t : Trans N}
    {M M' : QueueMarking N T} {δ : Delivered N T} {e : List (N × T)}
    (hf : refActionFire a t M δ e M') :
    ∀ p ∈ e.map Prod.fst, OutputArc t p :=
  ctx_deposits_outputs (core062_outputsOnlyDeclared h) ha hf

end Derived

/-! ### Examples

Tokens are pairs `(value, timestamp)` and the value projection is `Prod.fst`. -/

/-- `t`: an input arc on place 0 that takes one token, output `Place 2`. -/
def core062_t : Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 2) }

/-- `t3`: an input arc on place 0 that takes one token, and one output branch that names
place 2 three times. -/
def core062_t3 : Trans Nat :=
  { core := { name := "t3", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.and (.place 2) (.and (.place 2) (.place 2))) }

/-- Place 0 holds the value 1 (stamped 0); every other place is empty. -/
def core062_M : QueueMarking Nat (Nat × Nat) := fun p => if p = 0 then [(1, 0)] else []

/-- The reference context with the value projection `Prod.fst`. -/
abbrev core062_ref : Ctx Nat (Nat × Nat) Nat := refCtx Prod.fst

/-- The action of the test derivation: it completes with the token `(5, 0)` in place 2. -/
def core062_act : ActionFn Nat (Nat × Nat) := fun _ _ => .ok [(2, (5, 0))]

/-- ✓ CORE-062 is not vacuous. The test derivation: the action calls `output(2, 5)` through the
reference context, which builds the buffer `[(2, 5)]` from the empty buffer, and the reference
action firing of `t` deposits the token `(5, 0)` in place 2. The bulk call with 5, 6, 7 appends
three entries in that order, and the reference firing of `t3`, whose branch names place 2 three
times, deposits the three tokens in place 2 in that order. The bulk call on the foreign place 5,
and on the input place 0, reports an error, so nothing is appended. -/
@[evidence nonvacuous CORE_062]
theorem CORE_062_nonvacuous :
    Built core062_ref core062_t [(2, 5)] ∧
    refActionFire core062_act.rel core062_t core062_M (qDelivered core062_M core062_t)
      [(2, (5, 0))] (qFire core062_M core062_t [(2, (5, 0))]) ∧
    qFire core062_M core062_t [(2, (5, 0))] 2 = [(5, 0)] ∧
    core062_ref.output core062_t [] 2 [5, 6, 7] = some [(2, 5), (2, 6), (2, 7)] ∧
    RefQFire core062_t3 core062_M (qDelivered core062_M core062_t3)
      [(2, (5, 0)), (2, (6, 0)), (2, (7, 0))]
      (qFire core062_M core062_t3 [(2, (5, 0)), (2, (6, 0)), (2, (7, 0))]) ∧
    qFire core062_M core062_t3 [(2, (5, 0)), (2, (6, 0)), (2, (7, 0))] 2 =
      [(5, 0), (6, 0), (7, 0)] ∧
    core062_ref.output core062_t [(2, 5)] 5 [5, 6, 7] = none ∧
    core062_ref.output core062_t [(2, 5)] 0 [5, 6, 7] = none := by
  refine ⟨.call [] [(2, 5)] 2 [5] .nil (by decide),
    ⟨⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩, by unfold OutputBranch core062_t; decide, rfl⟩,
    by decide, by decide,
    ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩, by decide, by decide, by decide⟩

/-! ### Wrong context: one allowed set for every arc -/

/-- A context with one allowed set for the input and the output places of the transition: an
output call on an input place appends as on an output place. -/
def core062_arcPlacesCtx {N T V : Type} [DecidableEq N] (value : T → V) : Ctx N T V :=
  { refCtx value with
    output := fun t e p vs =>
      if OutputArc t p ∨ p ∈ inPlaces t then some (e ++ vs.map fun v => (p, v)) else none }

/-- ✗ It violates line 2: on `t`, the input place 0 is no output place, and the call appends the
value 5 there instead of reporting an error. -/
@[evidence forbids CORE_062]
theorem CORE_062_forbids_arcPlaces :
    ¬ CORE_062 Prod.fst (core062_arcPlacesCtx (N := Nat) (T := Nat × Nat) (V := Nat)
        Prod.fst) := by
  intro h
  have := h.2 core062_t [] 0 [5] (by decide)
  exact absurd this (by decide)

/-! ### Mutant: the values of one call in any order -/

section MutantBulk

variable {N T V : Type} [DecidableEq N]

/-- Mutant reading of line 1 ("one token per value" read as a multiset): the call appends after
the buffer the entries of the values in some order. Line 2 is as in CORE-062. -/
def CORE_062_mutant_bulkAnyOrder (value : T → V) (C : Ctx N T V) : Prop :=
  (∀ t e p vs, OutputArc t p →
      ∃ l, C.output t e p vs = some (e ++ l) ∧ l.Perm (vs.map fun v => (p, v))) ∧
    core062_line2 value C

/-- A context that appends the values of one call in reverse order. -/
def core062_revCtx (value : T → V) : Ctx N T V :=
  { refCtx value with
    output := fun t e p vs =>
      if OutputArc t p then some (e ++ (vs.map fun v => (p, v)).reverse) else none }

end MutantBulk

/-- ✗ The reversing context kills the mutant: it meets the multiset reading, but the bulk call
with 5, 6, 7 on place 2 appends 7, 6, 5 (line 1). -/
@[evidence mutant CORE_062]
theorem CORE_062_mutant_bulkAnyOrder_killed :
    CORE_062_mutant_bulkAnyOrder Prod.fst (core062_revCtx (N := Nat) (T := Nat × Nat) (V := Nat)
        Prod.fst) ∧
      ¬ CORE_062 Prod.fst (core062_revCtx (N := Nat) (T := Nat × Nat) (V := Nat)
        Prod.fst) := by
  refine ⟨⟨fun t e p vs hp => ⟨_, by simp [core062_revCtx, hp], List.reverse_perm _⟩,
    fun t e p vs hp => by simp [core062_revCtx, hp]⟩, fun h => ?_⟩
  have := h.1 core062_t [] 2 [5, 6, 7] (by decide)
  exact absurd this (by decide)

/-! ### Mutant: the new entries anywhere in the buffer -/

section MutantBuffer

variable {N T V : Type} [DecidableEq N]

/-- Mutant reading of line 1 ("declares a token" read as "the buffer then holds the earlier and
the new tokens"): the buffer after the call is some ordering of the earlier entries and the new
ones. Line 2 is as in CORE-062. -/
def CORE_062_mutant_bufferAnyOrder (value : T → V) (C : Ctx N T V) : Prop :=
  (∀ t e p vs, OutputArc t p →
      ∃ l, C.output t e p vs = some l ∧ l.Perm (e ++ vs.map fun v => (p, v))) ∧
    core062_line2 value C

/-- A context that puts the entries of a call ahead of the earlier ones. -/
def core062_prependCtx (value : T → V) : Ctx N T V :=
  { refCtx value with
    output := fun t e p vs =>
      if OutputArc t p then some ((vs.map fun v => (p, v)) ++ e) else none }

end MutantBuffer

/-- ✗ The prepending context kills the mutant: it meets the reading, but after the buffer
`[(2, 1)]` the call with 5 on place 2 gives `[(2, 5), (2, 1)]` (line 1). -/
@[evidence mutant CORE_062]
theorem CORE_062_mutant_bufferAnyOrder_killed :
    CORE_062_mutant_bufferAnyOrder Prod.fst
        (core062_prependCtx (N := Nat) (T := Nat × Nat) (V := Nat)
        Prod.fst) ∧
      ¬ CORE_062 Prod.fst (core062_prependCtx (N := Nat) (T := Nat × Nat) (V := Nat)
        Prod.fst) := by
  refine ⟨⟨fun t e p vs hp => ⟨_, by simp [core062_prependCtx, hp], List.perm_append_comm⟩,
    fun t e p vs hp => by simp [core062_prependCtx, hp]⟩, fun h => ?_⟩
  have := h.1 core062_t [(2, 1)] 2 [5] (by decide)
  exact absurd this (by decide)

/-! ### Mutant: a token for each distinct value -/

/-- Mutant reading of line 1 ("one token per value" read as "every value gets a token"): the
call appends entries on the place whose values are exactly those of the call, repetitions not
counted. Line 2 is as in CORE-062. -/
def CORE_062_mutant_eachValue {N T V : Type} [DecidableEq N] (value : T → V) (C : Ctx N T V) :
    Prop :=
  (∀ t e p vs, OutputArc t p →
      ∃ l, C.output t e p vs = some (e ++ l) ∧ ∀ x, x ∈ l ↔ x ∈ vs.map fun v => (p, v)) ∧
    core062_line2 value C

/-- A context that keeps only the first occurrence of each value of a call. -/
def core062_dedupCtx : Ctx Nat (Nat × Nat) Nat :=
  { refCtx Prod.fst with
    output := fun t e p vs =>
      if OutputArc t p then some (e ++ vs.eraseDups.map fun v => (p, v)) else none }

/-- ✗ The collapsing context kills the mutant: it meets the reading, but the call with 5, 5 on
place 2 appends one entry, not two (line 1). -/
@[evidence mutant CORE_062]
theorem CORE_062_mutant_eachValue_killed :
    CORE_062_mutant_eachValue Prod.fst core062_dedupCtx ∧ ¬ CORE_062 Prod.fst core062_dedupCtx := by
  refine ⟨⟨fun t e p vs hp => ⟨vs.eraseDups.map fun v => (p, v), by simp [core062_dedupCtx, hp],
      fun x => ?_⟩,
    fun t e p vs hp => by simp [core062_dedupCtx, hp]⟩, fun h => ?_⟩
  · simp only [List.mem_map]
    constructor
    · rintro ⟨v, hv, rfl⟩; exact ⟨v, List.mem_eraseDups.mp hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩; exact ⟨v, List.mem_eraseDups.mpr hv, rfl⟩
  · have := h.1 core062_t [] 2 [5, 5] (by decide)
    exact absurd this (by decide)

/-! ### Mutant: the empty bulk call left open -/

section MutantEmpty

variable {N T V : Type} [DecidableEq N]

/-- Mutant reading of line 1 (a bulk call needs at least one value): line 1 only for a non-empty
list of values. Line 2 is as in CORE-062. -/
def CORE_062_mutant_nonEmpty (value : T → V) (C : Ctx N T V) : Prop :=
  (∀ t e p vs, OutputArc t p → vs ≠ [] →
      C.output t e p vs = some (e ++ vs.map fun v => (p, v))) ∧
    core062_line2 value C

/-- A context that refuses a bulk call with no values. -/
def core062_nonEmptyCtx (value : T → V) : Ctx N T V :=
  { refCtx value with
    output := fun t e p vs =>
      if OutputArc t p ∧ vs ≠ [] then some (e ++ vs.map fun v => (p, v)) else none }

end MutantEmpty

/-- ✗ The refusing context kills the mutant: it meets the reading, but the empty call on the
output place 2 reports an error instead of succeeding (line 1, AC4). -/
@[evidence mutant CORE_062]
theorem CORE_062_mutant_nonEmpty_killed :
    CORE_062_mutant_nonEmpty Prod.fst
        (core062_nonEmptyCtx (N := Nat) (T := Nat × Nat) (V := Nat)
        Prod.fst) ∧
      ¬ CORE_062 Prod.fst (core062_nonEmptyCtx (N := Nat) (T := Nat × Nat) (V := Nat)
        Prod.fst) := by
  refine ⟨⟨fun t e p vs hp hne => by simp [core062_nonEmptyCtx, hp, hne],
    fun t e p vs hp => by simp [core062_nonEmptyCtx, hp]⟩, fun h => ?_⟩
  have := h.1 core062_t [] 2 [] (by decide)
  exact absurd this (by decide)

/-! ### Mutant: the place checked per value -/

section MutantPerValue

variable {N T V : Type} [DecidableEq N]

/-- Mutant reading of line 2 ("producing to an undeclared output place results in an error"
read as "every token produced there is an error"): line 2 only for a non-empty list of values.
Line 1 is as in CORE-062. -/
def CORE_062_mutant_perValue (value : T → V) (C : Ctx N T V) : Prop :=
  core062_line1 value C ∧ (∀ t e p vs, ¬ OutputArc t p → vs ≠ [] → C.output t e p vs = none)

/-- A context that checks the place once per value: a call with no values checks nothing and
succeeds on any place. -/
def core062_perValueCtx (value : T → V) : Ctx N T V :=
  { refCtx value with
    output := fun t e p vs =>
      if OutputArc t p then some (e ++ vs.map fun v => (p, v))
      else if vs = [] then some e else none }

end MutantPerValue

/-- ✗ The per-value context kills the mutant: it meets the reading, but the empty call on the
foreign place 5 succeeds instead of reporting an error (line 2, AC3). -/
@[evidence mutant CORE_062]
theorem CORE_062_mutant_perValue_killed :
    CORE_062_mutant_perValue Prod.fst
        (core062_perValueCtx (N := Nat) (T := Nat × Nat) (V := Nat)
        Prod.fst) ∧
      ¬ CORE_062 Prod.fst (core062_perValueCtx (N := Nat) (T := Nat × Nat) (V := Nat)
        Prod.fst) := by
  refine ⟨⟨fun t e p vs hp => by simp [core062_perValueCtx, hp],
    fun t e p vs hp hne => by simp [core062_perValueCtx, hp, hne]⟩, fun h => ?_⟩
  have := h.2 core062_t [] 5 [] (by decide)
  exact absurd this (by decide)

/-! ### Mutant: an undeclared place silently produces nothing -/

section MutantDrop

variable {N T V : Type} [DecidableEq N]

/-- Mutant reading of line 2 ("results in an error" read as "yields no token"): on an undeclared
place the call reports an error or succeeds with the buffer unchanged. Line 1 is as in
CORE-062. -/
def CORE_062_mutant_silentDrop (value : T → V) (C : Ctx N T V) : Prop :=
  core062_line1 value C ∧
    (∀ t e p vs, ¬ OutputArc t p → C.output t e p vs = none ∨ C.output t e p vs = some e)

/-- A context that drops a call on an undeclared place and returns normally. -/
def core062_dropCtx (value : T → V) : Ctx N T V :=
  { refCtx value with
    output := fun t e p vs => if OutputArc t p then some (e ++ vs.map fun v => (p, v)) else some e }

end MutantDrop

/-- ✗ The dropping context kills the mutant: it meets the reading, but the call with 5 on the
foreign place 5 returns normally instead of reporting an error (line 2). -/
@[evidence mutant CORE_062]
theorem CORE_062_mutant_silentDrop_killed :
    CORE_062_mutant_silentDrop Prod.fst (core062_dropCtx (N := Nat) (T := Nat × Nat) (V := Nat)
        Prod.fst) ∧
      ¬ CORE_062 Prod.fst (core062_dropCtx (N := Nat) (T := Nat × Nat) (V := Nat)
        Prod.fst) := by
  refine ⟨⟨fun t e p vs hp => by simp [core062_dropCtx, hp],
    fun t e p vs hp => .inr (by simp [core062_dropCtx, hp])⟩, fun h => ?_⟩
  have := h.2 core062_t [] 5 [5] (by decide)
  exact absurd this (by decide)

end Libpetri.Spec
