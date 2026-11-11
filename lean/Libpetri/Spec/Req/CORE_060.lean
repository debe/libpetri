import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryContext
import Libpetri.Spec.Req.EXEC_010

set_option linter.missingDocs true

/-!
# CORE-060: Context input access (`spec/01-core-model.md`)

CORE-060 is a pure-function requirement (kind F) over a transition context `C : Ctx N T V`
(`Spec/GlossaryContext.lean`) and a value projection `value : T → V`. A context is a record of
accessor functions over the transition and what the firing delivered to its action (`Delivered`);
a result `none` is a call that reports an error. `T` is the type of tokens, each with its creation
timestamp, and `V` the type of their values.

The four lines: on an input place from which the delivery holds tokens, `inputs` returns their
values in the order delivered (line 1); when exactly one token was delivered from the place,
`input` returns its value (line 2) and `inputToken` the token itself (line 3); on a place that is
not an input place and from which the delivery holds no token, all three report an error (line 4).
The premises of lines 1 and 4 hold at every firing (each input arc consumes at least one token,
and a firing consumes through its input arcs only), so they only set aside deliveries no firing
makes; they accept the Rust and Python check, which is key presence in the delivered map
(`CORE_060_allows_keyed`). Lines 2 and 3 say nothing when the firing consumed more than one token
(ruling D50 (a)): the runtimes differ there, and `CORE_060_batch_undecided` shows two contexts
that both satisfy the block and differ.

The witness is the reference context `refCtx`. The link to the firing is `core060_inputs_oldest`:
together with EXEC-010 over the same queue firing relation, `inputs` returns the values of the
oldest tokens of the place, in queue order, for an input that is not a correlated input of a ν-net
match specification. One wrong context per line is killed: one that returns the values in reverse
order, one whose `input` always reports an error, one whose `inputToken` re-mints the token with
another timestamp, and one that answers an undeclared place with the empty list instead of an
error. Three runtime-shaped slips are forbidden: one store for consumed and read tokens served
through `inputs` (line 4), the same store served through an unguarded `inputToken` (line 4), and a
pooled context not cleared between firings (lines 1 to 3).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## CORE-060: Context Input Access -/

requirement CORE_060
  id "CORE-060"
  title "Context Input Access"
  kind F
  scope "the transition context of every implementation; line 3 and the inputToken part of line 4 only where the context gives access to tokens: Java and TypeScript"
  source verbatim "spec/01-core-model.md"
  quote "*When* an action calls `inputs(place)` on an input place of its transition, the call *shall* return the values of the tokens the firing consumed from that place, in the order the firing consumed them ([EXEC-010])."
        "*When* an action calls `input(place)` on an input place from which the firing consumed exactly one token, the call *shall* return the value of that token."
        "*Where* the transition context gives access to tokens (Java, TypeScript), *when* an action calls `inputToken(place)` on an input place from which the firing consumed exactly one token, the call *shall* return that token, with its creation timestamp."
        "*If* an action calls `inputs(place)`, `input(place)` or `inputToken(place)` (where it exists) on a place that does not resolve to an input place of its transition ([MOD-031]), *then* the call *shall* report an error ([CORE-063])."
        "What `input(place)` and `inputToken(place)` return when the firing consumed more than one token from the place is not specified; an action reads a batch with `inputs(place)`."
  reading "For every value projection value and every context C, every transition t, every delivery δ (the tokens the firing consumed from each input place and the tokens its read arcs read) and every place p:"
          "if p is an input place of t and δ delivered at least one token from p, inputs on t, δ and p returns the values of the tokens δ delivered from p, in the order δ delivered them;"
          "if p is an input place of t and δ delivered exactly one token x from p, input on t, δ and p returns the value of x;"
          "if p is an input place of t and δ delivered exactly one token x from p, inputToken on t, δ and p returns x itself;"
          "if p is not an input place of t and δ delivered no token from p, inputs, input and inputToken on t, δ and p each report an error."
  assumes "The model is the pair (value, C). C is a transition context (Ctx, Spec/GlossaryContext.lean): its accessors inputs, input and inputToken take the transition, the delivery and a place, and return none when the call reports an error. A delivery (Delivered, Spec/GlossaryQueue.lean) is what the firing hands its action: the tokens it consumed from each input place, in the order consumed, and the tokens its read arcs read. Tokens are the queue model's token identities T, each carrying its value and its creation timestamp; value : T → V reads a token's value, so input (a value) and inputToken (the token, with its timestamp) are told apart. The witness is the reference context refCtx."
          "The block is a function of the delivery, not of the marking: line 1 keeps the order in which the firing delivered the tokens, and which tokens the firing consumes, and in which order, is not CORE-060's. For an input that is not a correlated input of a ν-net match specification it is EXEC-010's: the oldest tokens of the place, in queue order. core060_inputs_oldest derives that for any context that satisfies CORE-060 and any queue firing relation that satisfies EXEC-010, and core060_input_oldest gives the value of the oldest token for input on an arc that consumes one token. A correlated input (NU-020) takes the matched tokens of the chosen name, oldest first among them, and can pass over an older token of another name, so for it the delivered tokens are not the oldest of the place. The block holds for whatever delivery that firing makes; the two joint theorems do not reach it, because the queue firing relation of EXEC-010 carries no match specification (ruling D16)."
          "Lines 1 and 4 range over the deliveries a firing makes at the place: line 1 takes an input place from which the delivery holds at least one token, line 4 a place that is not an input place and from which the delivery holds none. Every firing meets both premises: each input arc requires and consumes at least one token (IO-002, IO-004 AC1), and a firing consumes through its input arcs only. A delivery that breaks them is made by no firing, and the block makes no claim on it."
          "The premises accept the Rust and Python check, which is key presence in the map of delivered tokens, not membership in the input places: Rust's input and inputs answer from self.inputs.get(place_name) (rust/libpetri-core/src/context.rs:278-302), the backends insert a key only when they push a token (rust/libpetri-runtime/src/bitmap_backend.rs:785-808), and Python copies those keys (rust/libpetri-py/src/action.rs:329-365). That context, core060_keyedCtx, satisfies CORE-060 (CORE_060_allows_keyed), and on every delivery that holds tokens from exactly the input places it answers as refCtx at every place (core060_keyed_agrees)."
          "Line 1 compares lists: the values in the order delivered, with their repetitions. A context that returns them in reverse order meets the reading 'inputs returns all consumed values' as a multiset and violates line 1 (CORE_060_mutant_anyOrder_killed)."
          "Lines 2 and 3 carry the premise that exactly one token was delivered from the place (ruling D50 (a), clash core-c#1). With more than one, the runtimes differ: input reports an error in Rust (rust/libpetri-core/src/context.rs:278-287), TypeScript (typescript/src/core/transition-context.ts:114-123) and Python (rust/libpetri-py/src/action.rs:207-217), and Java returns the value of the oldest token (java/src/main/java/org/libpetri/core/TransitionContext.java:164-168, against its own javadoc at :162, a recorded defect, RD-09 in spec/runtime-defects.md); inputToken returns the oldest token in Java (:190-194) and TypeScript (typescript/src/core/transition-context.ts:133-138). The block leaves the case open: CORE_060_batch_undecided shows two contexts that both satisfy it and differ there, on input and on inputToken. A firing never consumes zero tokens from an input place (IO-002 and IO-004 AC1: every input arc requires at least one token), so 'other than one' is 'more than one' at a firing. No line claims anything on an input place with an empty delivery, which no firing makes: lines 2 and 3 need exactly one token, line 1 at least one."
          "A context whose input always reports an error, so that an action must use inputs, meets the reading 'input returns a consumed value when it returns one' and violates line 2 (CORE_060_mutant_soundOnly_killed). A context whose inputToken re-mints the token with the same value and another timestamp meets the reading 'inputToken returns a token with the consumed value' and violates line 3 (CORE_060_mutant_valueOnly_killed): the metadata the token carries is the consumed token's own."
          "A context is a function of the transition, the delivery and the place, so a context that keeps state across firings is modelled as a different context at each firing. Java's precompiled executor reuses one context per transition and clears its token store before each firing (java/src/main/java/org/libpetri/runtime/PrecompiledNetExecutor.java:2320-2324); a context that kept the tokens of the previous firing ahead of its own violates lines 1 to 3 (CORE_060_forbids_staleStore)."
          "Line 3, and the inputToken part of line 4, are scoped to the implementations whose context gives access to tokens (ruling D50 (a), clash core-c#2): Java's and TypeScript's inputToken. The Rust and Python contexts expose values only (rust/libpetri-core/src/context.rs:278-327, python/libpetri/_libpetri.pyi), so line 3 has no accessor there; Rust's take_inputs empties the context and serves the executor, not an action. The Lean line is the same under every scope."
          "Line 4 reads 'results in an error' as 'the call reports an error' (none): Rust returns an error, Java and TypeScript throw, Python raises. A place that is not an input place includes a read place (no place is both, ruling D15), an output place and a place of no arc of the transition. A context that answers such a place with the empty list meets the reading 'an undeclared place has no consumed values' and violates line 4 (CORE_060_mutant_emptyList_killed). So does one that keeps the consumed and the read tokens in one store and serves a read place through inputs (CORE_060_forbids_sharedStore), or through an inputToken that lost its input-place guard (CORE_060_forbids_unguardedToken): TypeScript's context and Java's precompiled executor keep one such store (typescript/src/core/transition-context.ts:114-160, java/src/main/java/org/libpetri/runtime/PrecompiledNetExecutor.java:2341-2347), so each accessor depends on its own guard. The read accessor is CORE-061's, the output accessor CORE-062's, and the three error lines together are CORE-063's."
          "The error sentence names the place the call resolves to (MOD-031), and the block reads every place that way: after instancing or port binding, Java and TypeScript map a declared place the action names to the composed place first (MOD-031, W8). A type mismatch between the place and the value (Rust's downcast error) is API shape and not modelled: V is one type of values. Further accessors (Java's inputTokens, Rust's input_raw and input_tokens_raw) are not part of the block."
          "AC1 (input(place) returns the single consumed value) is line 2, under the exactly-one premise of ruling D50 (a)."
          "AC2 (inputs(place) returns all consumed values, for multi-token cardinality) is line 1."
          "AC3 (inputToken(place) returns the token with metadata, including its timestamp) is line 3, scoped to Java and TypeScript."
          "AC4 (accessing an undeclared input place results in an error) is line 4."
          "The test derivation (fire a transition consuming 3 tokens, verify inputs() returns 3 values) is CORE_060_nonvacuous: the reference firing of a transition whose input arc takes exactly 3 tokens delivers the 3 oldest, and the reference context returns their 3 values, in queue order."
  signoff "pending"
  statement : ∀ {N T V : Type} [DecidableEq N], (T → V) → Ctx N T V → Prop :=
    fun value C =>
      (∀ t δ p, p ∈ inPlaces t → δ.inputs p ≠ [] →
        C.inputs t δ p = some ((δ.inputs p).map value)) ∧
      (∀ t δ p x, p ∈ inPlaces t → δ.inputs p = [x] → C.input t δ p = some (value x)) ∧
      (∀ t δ p x, p ∈ inPlaces t → δ.inputs p = [x] → C.inputToken t δ p = some x) ∧
      (∀ t δ p, p ∉ inPlaces t → δ.inputs p = [] →
        C.inputs t δ p = none ∧ C.input t δ p = none ∧ C.inputToken t δ p = none)

/- The pinned readable form of CORE-060: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CORE_060 : {N T V : Type} → [DecidableEq N] → (T → V) → Ctx N T V → Prop :=
fun {N T V} [DecidableEq N] value C =>
  (∀ (t : Reference.Trans N) (δ : Delivered N T),
      ∀ p ∈ inPlaces t, δ.inputs p ≠ [] → C.inputs t δ p = some (List.map value (δ.inputs p))) ∧
    (∀ (t : Reference.Trans N) (δ : Delivered N T) (p : N) (x : T),
        p ∈ inPlaces t → δ.inputs p = [x] → C.input t δ p = some (value x)) ∧
      (∀ (t : Reference.Trans N) (δ : Delivered N T) (p : N) (x : T),
          p ∈ inPlaces t → δ.inputs p = [x] → C.inputToken t δ p = some x) ∧
        ∀ (t : Reference.Trans N) (δ : Delivered N T),
          ∀ p ∉ inPlaces t, δ.inputs p = [] → C.inputs t δ p = none ∧ C.input t δ p = none ∧ C.inputToken t δ p = none
-/
#guard_msgs in #print CORE_060

/-! ### The four lines, named (for the mutants) -/

section Lines

variable {N T V : Type} [DecidableEq N]

/-- Line 1 of CORE-060: `inputs` on an input place from which the delivery holds tokens returns
their values, in order. -/
def core060_line1 (value : T → V) (C : Ctx N T V) : Prop :=
  ∀ t δ p, p ∈ inPlaces t → δ.inputs p ≠ [] → C.inputs t δ p = some ((δ.inputs p).map value)

/-- Line 2 of CORE-060: `input` returns the value of the single delivered token. -/
def core060_line2 (value : T → V) (C : Ctx N T V) : Prop :=
  ∀ t δ p x, p ∈ inPlaces t → δ.inputs p = [x] → C.input t δ p = some (value x)

/-- Line 3 of CORE-060: `inputToken` returns the single delivered token itself. -/
def core060_line3 (_value : T → V) (C : Ctx N T V) : Prop :=
  ∀ t δ p x, p ∈ inPlaces t → δ.inputs p = [x] → C.inputToken t δ p = some x

/-- Line 4 of CORE-060: the three input accessors report an error off the input places. -/
def core060_line4 (_value : T → V) (C : Ctx N T V) : Prop :=
  ∀ t δ p, p ∉ inPlaces t → δ.inputs p = [] →
    C.inputs t δ p = none ∧ C.input t δ p = none ∧ C.inputToken t δ p = none

/-- CORE-060 is its four lines. -/
theorem core060_iff (value : T → V) (C : Ctx N T V) :
    CORE_060 value C ↔
      core060_line1 value C ∧ core060_line2 value C ∧ core060_line3 value C ∧
        core060_line4 value C :=
  Iff.rfl

end Lines

/-! ### The reference -/

/-- ✓ The reference context satisfies CORE-060, whatever the value projection. -/
@[evidence holds CORE_060]
theorem CORE_060_reference {N T V : Type} [DecidableEq N] (value : T → V) :
    CORE_060 value (refCtx (N := N) value) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t δ p hp _; simp [refCtx, hp]
  · intro t δ p x hp hx; simp [refCtx, hp, hx]
  · intro t δ p x hp hx; simp [refCtx, hp, hx]
  · intro t δ p hp _; simp [refCtx, hp]

/-! ### Consequences in the joint model (with EXEC-010) -/

section Joint

variable {N T V : Type} [DecidableEq N]

/-- **Joint with EXEC-010**: on a firing of a queue firing relation that satisfies EXEC-010, a
context that satisfies CORE-060 returns from `inputs` the values of the oldest `Consumes` tokens
of the input place, in queue order. The premise `hne` holds at every firing (each input arc
consumes at least one token, IO-002). The queue model has no match specification, so this is the
reading for an input that is not a correlated input (NU-020). -/
theorem core060_inputs_oldest {value : T → V} {C : Ctx N T V} {Q : QFireRel N T}
    (hC : CORE_060 value C) (hQ : EXEC_010 Q) {t : Trans N} {M M' : QueueMarking N T}
    {δ : Delivered N T} {e : List (N × T)} (hf : Q t M δ e M') {p : N} (hp : p ∈ inPlaces t)
    (hne : δ.inputs p ≠ []) :
    C.inputs t δ p = some ((OldestFirst M p (Consumes t (Counts M) p)).map value) := by
  rw [hC.1 t δ p hp hne, hQ.2.1 t δ e p hp M M' hf]

/-- **Joint with EXEC-010**: on an input place from which the firing consumes one token, `input`
returns the value of the oldest token of the place and `inputToken` that token. -/
theorem core060_input_oldest {value : T → V} {C : Ctx N T V} {Q : QFireRel N T}
    (hC : CORE_060 value C) (hQ : EXEC_010 Q) {t : Trans N} {M M' : QueueMarking N T}
    {δ : Delivered N T} {e : List (N × T)} (hf : Q t M δ e M') {p : N} (hp : p ∈ inPlaces t)
    (h1 : Consumes t (Counts M) p = 1) {x : T} (hx : Head M p = some x) :
    C.input t δ p = some (value x) ∧ C.inputToken t δ p = some x := by
  have hd : δ.inputs p = [x] := by
    rw [hQ.2.1 t δ e p hp M M' hf, h1]
    unfold OldestFirst
    unfold Head at hx
    cases hM : M p with
    | nil => rw [hM] at hx; cases hx
    | cons y ys => rw [hM] at hx; cases hx; rfl
  exact ⟨hC.2.1 t δ p x hp hd, hC.2.2.1 t δ p x hp hd⟩

end Joint

/-! ### Examples

Tokens are pairs `(value, timestamp)` and the value projection is `Prod.fst`. -/

/-- `t3`: an input arc on place 0 that takes exactly 3 tokens, a read arc on place 1, output
`Place 2`. -/
def core060_t3 : Trans Nat :=
  { core := { name := "t3", inputs := [⟨0, .exactly 3⟩], inhibitors := [], reads := [1],
              resets := [] },
    out := some (.place 2) }

/-- `u`: an input arc on place 0 that takes one token, a read arc on place 1, output `Place 2`. -/
def core060_u : Trans Nat :=
  { core := { name := "u", inputs := [⟨0, .one⟩], inhibitors := [], reads := [1], resets := [] },
    out := some (.place 2) }

/-- Place 0 holds the values 10, 11, 12 (stamped 1, 2, 3), oldest first, place 1 the value 7;
every other place is empty. -/
def core060_M : QueueMarking Nat (Nat × Nat) := fun p =>
  if p = 0 then [(10, 1), (11, 2), (12, 3)] else if p = 1 then [(7, 0)] else []

/-- The reference context with the value projection `Prod.fst`. -/
abbrev core060_ref : Ctx Nat (Nat × Nat) Nat := refCtx Prod.fst

/-- ✓ CORE-060 is not vacuous. The test derivation: `t3` fires from `core060_M` (a reference
queue firing), consuming the 3 oldest tokens of place 0, and the reference context returns their
3 values in queue order. On `u`, which consumes one token, `input` returns the value 10 of the
oldest token and `inputToken` the token `(10, 1)` with its timestamp. On the read place 1, which
is no input place, the three accessors report an error. -/
@[evidence nonvacuous CORE_060]
theorem CORE_060_nonvacuous :
    RefQFire core060_t3 core060_M (qDelivered core060_M core060_t3) [(2, (0, 9))]
      (qFire core060_M core060_t3 [(2, (0, 9))]) ∧
    core060_ref.inputs core060_t3 (qDelivered core060_M core060_t3) 0 = some [10, 11, 12] ∧
    core060_ref.input core060_u (qDelivered core060_M core060_u) 0 = some 10 ∧
    core060_ref.inputToken core060_u (qDelivered core060_M core060_u) 0 = some (10, 1) ∧
    core060_ref.inputs core060_t3 (qDelivered core060_M core060_t3) 1 = none ∧
    core060_ref.input core060_t3 (qDelivered core060_M core060_t3) 1 = none ∧
    core060_ref.inputToken core060_t3 (qDelivered core060_M core060_t3) 1 = none := by
  refine ⟨⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ### The batch case: undecided (ruling D50 (a)) -/

section Batch

variable {N T V : Type} [DecidableEq N]

/-- Java's reading of the batch case: `input` returns the value of the oldest delivered token,
whatever the count. -/
def core060_oldestCtx (value : T → V) : Ctx N T V :=
  { refCtx value with
    input := fun t δ p => if p ∈ inPlaces t then ((δ.inputs p).head?).map value else none }

/-- A strict reading of the batch case: `inputToken` reports an error unless exactly one token
was delivered, as `input` does in Rust, TypeScript and Python. -/
def core060_strictCtx (value : T → V) : Ctx N T V :=
  { refCtx value with
    inputToken := fun t δ p =>
      if p ∈ inPlaces t then (match δ.inputs p with | [x] => some x | _ => none) else none }

/-- Java's reading satisfies CORE-060. -/
theorem core060_oldestCtx_ok (value : T → V) : CORE_060 value (core060_oldestCtx (N := N) value) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t δ p hp _; simp [core060_oldestCtx, refCtx, hp]
  · intro t δ p x hp hx; simp [core060_oldestCtx, hp, hx]
  · intro t δ p x hp hx; simp [core060_oldestCtx, refCtx, hp, hx]
  · intro t δ p hp _; simp [core060_oldestCtx, refCtx, hp]

/-- The strict reading satisfies CORE-060. -/
theorem core060_strictCtx_ok (value : T → V) : CORE_060 value (core060_strictCtx (N := N) value) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t δ p hp _; simp [core060_strictCtx, refCtx, hp]
  · intro t δ p x hp hx; simp [core060_strictCtx, refCtx, hp, hx]
  · intro t δ p x hp hx; simp [core060_strictCtx, hp, hx]
  · intro t δ p hp _; simp [core060_strictCtx, refCtx, hp]

end Batch

/-- ? The batch case is open. On the firing of `t3`, which consumes 3 tokens from place 0, the
reference context and Java's reading both satisfy CORE-060 and differ on `input` (an error
against the value 10 of the oldest token), and the reference context and the strict reading both
satisfy it and differ on `inputToken` (the oldest token `(10, 1)` against an error). -/
@[evidence undecided CORE_060]
theorem CORE_060_batch_undecided :
    CORE_060 Prod.fst core060_ref ∧
    CORE_060 Prod.fst (core060_oldestCtx (N := Nat) (T := Nat × Nat) Prod.fst) ∧
    CORE_060 Prod.fst (core060_strictCtx (N := Nat) (T := Nat × Nat) Prod.fst) ∧
    core060_ref.input core060_t3 (qDelivered core060_M core060_t3) 0 = none ∧
    (core060_oldestCtx Prod.fst).input core060_t3 (qDelivered core060_M core060_t3) 0 = some 10 ∧
    core060_ref.inputToken core060_t3 (qDelivered core060_M core060_t3) 0 = some (10, 1) ∧
    (core060_strictCtx Prod.fst).inputToken core060_t3 (qDelivered core060_M core060_t3) 0 =
      none := by
  refine ⟨CORE_060_reference _, core060_oldestCtx_ok _, core060_strictCtx_ok _, ?_, ?_, ?_, ?_⟩
    <;> decide

/-! ### The Rust and Python shape: the declared check is key presence -/

section Keyed

variable {N T V : Type} [DecidableEq N]

/-- The Rust and Python context: an input accessor answers a place exactly when the map of
delivered tokens has a key for it, and the executor inserts a key only when it pushes a token
(rust/libpetri-core/src/context.rs:278-302, rust/libpetri-runtime/src/bitmap_backend.rs:785-808,
rust/libpetri-py/src/action.rs:329-365). Rust and Python have no `inputToken`; the field answers
the oldest delivered token, so that it is defined. -/
def core060_keyedCtx (value : T → V) : Ctx N T V :=
  { refCtx value with
    inputs := fun _ δ p => if δ.inputs p ≠ [] then some ((δ.inputs p).map value) else none
    input := fun _ δ p => match δ.inputs p with | [x] => some (value x) | _ => none
    inputToken := fun _ δ p => (δ.inputs p).head? }

/-- A delivery a firing of `t` makes: it holds tokens from exactly the input places of `t`. -/
def core060_FromInputs (t : Trans N) (δ : Delivered N T) : Prop :=
  ∀ p, δ.inputs p ≠ [] ↔ p ∈ inPlaces t

/-- On every delivery that holds tokens from exactly the input places, the keyed context answers
as the reference context, on all three input accessors and at every place. -/
theorem core060_keyed_agrees (value : T → V) (t : Trans N) (δ : Delivered N T)
    (h : core060_FromInputs t δ) (p : N) :
    (core060_keyedCtx value).inputs t δ p = (refCtx value).inputs t δ p ∧
    (core060_keyedCtx value).input t δ p = (refCtx value).input t δ p ∧
    (core060_keyedCtx value).inputToken t δ p = (refCtx value).inputToken t δ p := by
  by_cases hp : p ∈ inPlaces t
  · have hne := (h p).2 hp
    simp [core060_keyedCtx, refCtx, hp, hne]
    rfl
  · have he : δ.inputs p = [] := by
      by_contra hne; exact hp ((h p).1 hne)
    simp [core060_keyedCtx, refCtx, hp, he]

end Keyed

/-- ✓ The keyed context satisfies CORE-060: the premises of lines 1 and 4 (tokens delivered from
an input place, none from any other place) are what every firing gives, and they are exactly what
the key-presence check relies on. -/
@[evidence allows CORE_060]
theorem CORE_060_allows_keyed {N T V : Type} [DecidableEq N] (value : T → V) :
    CORE_060 value (core060_keyedCtx (N := N) value) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t δ p _ hne; simp [core060_keyedCtx, hne]
  · intro t δ p x _ hx; simp [core060_keyedCtx, hx]
  · intro t δ p x _ hx; simp [core060_keyedCtx, hx]
  · intro t δ p _ he; simp [core060_keyedCtx, he]

/-! ### Wrong contexts: one shared store, a lost guard, a stale pooled store -/

/-- A context that keeps the consumed and the read tokens in one store and serves both through
the input accessors: on a read place `inputs`, `input` and `inputToken` answer from the read
tokens. -/
def core060_sharedCtx {N T V : Type} [DecidableEq N] (value : T → V) : Ctx N T V :=
  { refCtx value with
    inputs := fun t δ p =>
      if p ∈ inPlaces t then some ((δ.inputs p).map value)
      else if ReadArc t p then some ((δ.reads p).map value) else none }

/-- ✗ It violates line 4: on `t3`, the read place 1 is no input place and the firing consumes no
token from it, and its `inputs` answers with the value 7 read there instead of an error. -/
@[evidence forbids CORE_060]
theorem CORE_060_forbids_sharedStore :
    ¬ CORE_060 Prod.fst (core060_sharedCtx (N := Nat) (T := Nat × Nat) Prod.fst) := by
  intro h
  have := (h.2.2.2 core060_t3 (qDelivered core060_M core060_t3) 1 (by decide) (by decide)).1
  exact absurd this (by decide)

/-- The same shared store, with every accessor guarded except `inputToken`, which answers the
first token the store holds for the place, consumed or read (TypeScript's
`return this.rawInput.get(actual)` without its `requireInput` call). -/
def core060_unguardedTokenCtx {N T V : Type} [DecidableEq N] (value : T → V) : Ctx N T V :=
  { refCtx value with
    inputToken := fun _ δ p => (δ.inputs p ++ δ.reads p).head? }

/-- ✗ It violates line 4: on the reference firing of `t3`, `inputToken` on the read place 1
answers the read token `(7, 0)` instead of an error. Its `inputs` and `input` are guarded, so
`CORE_060_forbids_sharedStore` does not cover it. -/
@[evidence forbids CORE_060]
theorem CORE_060_forbids_unguardedToken :
    ¬ CORE_060 Prod.fst (core060_unguardedTokenCtx (N := Nat) (T := Nat × Nat) Prod.fst) := by
  intro h
  have := (h.2.2.2 core060_t3 (qDelivered core060_M core060_t3) 1 (by decide) (by decide)).2.2
  exact absurd this (by decide)

/-- A pooled context that was not cleared between firings: `prev` is what the earlier firing of
the transition left in it, and the accessors answer from `prev` ahead of the current delivery
(Java's `TokenInput.get` returns the head of the list). -/
def core060_staleCtx {N T V : Type} [DecidableEq N] (prev : Delivered N T) (value : T → V) :
    Ctx N T V :=
  { refCtx value with
    inputs := fun t δ p =>
      if p ∈ inPlaces t then some ((prev.inputs p ++ δ.inputs p).map value) else none
    input := fun t δ p =>
      if p ∈ inPlaces t then ((prev.inputs p ++ δ.inputs p).head?).map value else none
    inputToken := fun t δ p =>
      if p ∈ inPlaces t then (prev.inputs p ++ δ.inputs p).head? else none }

/-- ✗ After the first firing of `u` from `core060_M`, which consumed `(10, 1)`, the uncleared
context serves the second firing, which consumes `(11, 2)`, with `(10, 1)`: line 3 fails. -/
@[evidence forbids CORE_060]
theorem CORE_060_forbids_staleStore :
    ¬ CORE_060 Prod.fst
      (core060_staleCtx (N := Nat) (T := Nat × Nat) (qDelivered core060_M core060_u) Prod.fst) := by
  intro h
  have := h.2.2.1 core060_u (qDelivered (qFire core060_M core060_u []) core060_u) 0 (11, 2)
    (by decide) (by decide)
  exact absurd this (by decide)

/-! ### Mutant: line 1 as a multiset -/

section MutantOrder

variable {N T V : Type} [DecidableEq N]

/-- Mutant reading of line 1 ("returns all consumed values" read without their order): `inputs`
returns the delivered values in some order. Lines 2 to 4 are as in CORE-060. -/
def CORE_060_mutant_anyOrder (value : T → V) (C : Ctx N T V) : Prop :=
  (∀ t δ p, p ∈ inPlaces t → δ.inputs p ≠ [] →
      ∃ l, C.inputs t δ p = some l ∧ l.Perm ((δ.inputs p).map value)) ∧
    core060_line2 value C ∧ core060_line3 value C ∧ core060_line4 value C

/-- A context that returns the delivered values newest first, and is the reference otherwise. -/
def core060_revCtx (value : T → V) : Ctx N T V :=
  { refCtx value with
    inputs := fun t δ p => if p ∈ inPlaces t then some ((δ.inputs p).map value).reverse else none }

end MutantOrder

/-- ✗ The reversing context kills the mutant: it meets the multiset reading, but on `t3` it
returns 12, 11, 10 for the tokens consumed as 10, 11, 12 (line 1). -/
@[evidence mutant CORE_060]
theorem CORE_060_mutant_anyOrder_killed :
    CORE_060_mutant_anyOrder Prod.fst (core060_revCtx (N := Nat) (T := Nat × Nat) Prod.fst) ∧
      ¬ CORE_060 Prod.fst (core060_revCtx (N := Nat) (T := Nat × Nat) Prod.fst) := by
  have hr := CORE_060_reference (N := Nat) (T := Nat × Nat) (Prod.fst : Nat × Nat → Nat)
  refine ⟨⟨fun t δ p hp _ => ?_, hr.2.1, hr.2.2.1, fun t δ p hp _ => ?_⟩, fun h => ?_⟩
  · exact ⟨_, by simp [core060_revCtx, hp], List.reverse_perm _⟩
  · simp [core060_revCtx, refCtx, hp]
  · have := h.1 core060_t3 (qDelivered core060_M core060_t3) 0 (by decide) (by decide)
    exact absurd this (by decide)

/-! ### Mutant: line 2 as soundness only -/

section MutantSound

variable {N T V : Type} [DecidableEq N]

/-- Mutant reading of line 2 ("returns the single consumed value" read as "a value `input`
returns is a consumed one"): `input` may always report an error. Lines 1, 3 and 4 are as in
CORE-060. -/
def CORE_060_mutant_soundOnly (value : T → V) (C : Ctx N T V) : Prop :=
  core060_line1 value C ∧
    (∀ t δ p v, p ∈ inPlaces t → C.input t δ p = some v → ∃ x ∈ δ.inputs p, v = value x) ∧
    core060_line3 value C ∧ core060_line4 value C

/-- A context whose `input` always reports an error, so an action must use `inputs`. -/
def core060_noInputCtx (value : T → V) : Ctx N T V :=
  { refCtx value with input := fun _ _ _ => none }

end MutantSound

/-- ✗ The context without `input` kills the mutant: it meets the soundness reading, but on `u`,
which consumes the one token `(10, 1)`, its `input` reports an error (line 2). -/
@[evidence mutant CORE_060]
theorem CORE_060_mutant_soundOnly_killed :
    CORE_060_mutant_soundOnly Prod.fst (core060_noInputCtx (N := Nat) (T := Nat × Nat) Prod.fst) ∧
      ¬ CORE_060 Prod.fst (core060_noInputCtx (N := Nat) (T := Nat × Nat) Prod.fst) := by
  have hr := CORE_060_reference (N := Nat) (T := Nat × Nat) (Prod.fst : Nat × Nat → Nat)
  refine ⟨⟨hr.1, fun _ _ _ _ _ h => (by cases h), hr.2.2.1, fun t δ p hp he => ?_⟩, fun h => ?_⟩
  · exact ⟨(hr.2.2.2 t δ p hp he).1, rfl, (hr.2.2.2 t δ p hp he).2.2⟩
  · have := h.2.1 core060_u (qDelivered core060_M core060_u) 0 (10, 1) (by decide) (by decide)
    cases this

/-! ### Mutant: line 3 with the value only -/

/-- Mutant reading of line 3 ("returns the token with metadata" read as "returns a token with
the consumed value"): `inputToken` may re-mint the token. Lines 1, 2 and 4 are as in CORE-060. -/
def CORE_060_mutant_valueOnly {N T V : Type} [DecidableEq N] (value : T → V) (C : Ctx N T V) :
    Prop :=
  core060_line1 value C ∧ core060_line2 value C ∧
    (∀ t δ p x, p ∈ inPlaces t → δ.inputs p = [x] →
      ∃ y, C.inputToken t δ p = some y ∧ value y = value x) ∧
    core060_line4 value C

/-- A context whose `inputToken` re-mints the oldest consumed token with the timestamp 0. -/
def core060_restampCtx : Ctx Nat (Nat × Nat) Nat :=
  { refCtx Prod.fst with
    inputToken := fun t δ p =>
      if p ∈ inPlaces t then ((δ.inputs p).head?).map fun x => (x.1, 0) else none }

/-- ✗ The re-minting context kills the mutant: it meets the value reading, but on `u`, which
consumes the token `(10, 1)`, its `inputToken` returns `(10, 0)` (line 3). -/
@[evidence mutant CORE_060]
theorem CORE_060_mutant_valueOnly_killed :
    CORE_060_mutant_valueOnly Prod.fst core060_restampCtx ∧
      ¬ CORE_060 Prod.fst core060_restampCtx := by
  have hr := CORE_060_reference (N := Nat) (T := Nat × Nat) (Prod.fst : Nat × Nat → Nat)
  refine ⟨⟨hr.1, hr.2.1, fun t δ p x hp hx => ?_, fun t δ p hp _ => ?_⟩, fun h => ?_⟩
  · exact ⟨(x.1, 0), by simp [core060_restampCtx, hp, hx], rfl⟩
  · simp [core060_restampCtx, refCtx, hp]
  · have := h.2.2.1 core060_u (qDelivered core060_M core060_u) 0 (10, 1) (by decide) (by decide)
    exact absurd this (by decide)

/-! ### Mutant: line 4 as "no consumed values" -/

section MutantEmpty

variable {N T V : Type} [DecidableEq N]

/-- Mutant reading of line 4 ("accessing an undeclared input place results in an error" read as
"an undeclared place has no consumed values"): off the input places `inputs` reports an error or
returns the empty list. Lines 1 to 3 are as in CORE-060. -/
def CORE_060_mutant_emptyList (value : T → V) (C : Ctx N T V) : Prop :=
  core060_line1 value C ∧ core060_line2 value C ∧ core060_line3 value C ∧
    (∀ t δ p, p ∉ inPlaces t → δ.inputs p = [] →
      (C.inputs t δ p = none ∨ C.inputs t δ p = some []) ∧
        C.input t δ p = none ∧ C.inputToken t δ p = none)

/-- A context that answers `inputs` on an undeclared place with the empty list. -/
def core060_emptyCtx (value : T → V) : Ctx N T V :=
  { refCtx value with
    inputs := fun t δ p => if p ∈ inPlaces t then some ((δ.inputs p).map value) else some [] }

end MutantEmpty

/-- ✗ The empty-list context kills the mutant: it meets the "no consumed values" reading, but on
`t3` its `inputs` answers the read place 1 with the empty list instead of an error (line 4). -/
@[evidence mutant CORE_060]
theorem CORE_060_mutant_emptyList_killed :
    CORE_060_mutant_emptyList Prod.fst (core060_emptyCtx (N := Nat) (T := Nat × Nat) Prod.fst) ∧
      ¬ CORE_060 Prod.fst (core060_emptyCtx (N := Nat) (T := Nat × Nat) Prod.fst) := by
  have hr := CORE_060_reference (N := Nat) (T := Nat × Nat) (Prod.fst : Nat × Nat → Nat)
  refine ⟨⟨fun t δ p hp _ => ?_, hr.2.1, hr.2.2.1, fun t δ p hp he => ?_⟩, fun h => ?_⟩
  · simp [core060_emptyCtx, hp]
  · exact ⟨.inr (by simp [core060_emptyCtx, hp]), (hr.2.2.2 t δ p hp he).2⟩
  · have := (h.2.2.2 core060_t3 (qDelivered core060_M core060_t3) 1 (by decide) (by decide)).1
    exact absurd this (by decide)

end Libpetri.Spec
