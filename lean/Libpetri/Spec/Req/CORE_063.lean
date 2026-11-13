import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryContext
import Libpetri.Spec.Req.CORE_060
import Libpetri.Spec.Req.CORE_061
import Libpetri.Spec.Req.CORE_062
import Libpetri.Spec.Text.CORE_063

set_option linter.missingDocs true

/-!
# CORE-063: Context structure enforcement (`spec/01-core-model.md`)

CORE-063 is a pure-function requirement (kind F) over a transition context `C : Ctx N T V`
(`Spec/GlossaryContext.lean`) and a value projection `value : T → V`, the same model as CORE-060
to CORE-062. A context is a record of accessor functions over the transition and what the firing
delivered to its action (`Delivered`); a result `none` is a call that reports an error. The value
projection is not used by the statement; it is a parameter so that the block is stated over the
same model as CORE-060 and the reference `refCtx value` is a model of both.

The three lines: on a place that is not an input place and from which the delivery holds no
token, the input accessors `inputs`, `input` and `inputToken` report an error (line 1, CORE-060
line 4); on a place that is not a read place and from which the delivery holds no read token,
`read` reports an error, also on an input place (line 2); on a place that is not an output place,
an output call reports an error, whatever its values, the empty list included, so it leaves no
entry behind (line 3). Line 1 is CORE-060 line 4, line 2 is CORE-061 line 2 and line 3 is
CORE-062 line 2, each by `Iff.rfl`, so the block is the conjunction of the three error lines and
follows from the three blocks (`CORE_063_of_060_061_062`). The delivery premises of lines 1 and 2
hold at every reference firing (`qDelivered_inputs_off`, `qDelivered_reads_off`), so on a firing's
delivery the lines need no premise (`core063_on_firing`).

Ruling D63 (a): the block is a rule on calls made through the context. A token that bypasses the
context (Java's and TypeScript's internal `rawOutput()`) is CORE-072 AC3's defensive clause and
is not witnessed. The bridge to the firing is `core063_deposits_outputs`: an action that writes
through a context that satisfies CORE-063, and whose successful output calls append at the named
place, deposits in a reference action firing only in output places of its transition, which is
CORE-035 line 1 and CONC-026 line 2.

The witness is the reference context `refCtx`. One wrong context per line is killed: one that
guards every accessor by "the transition has some arc on the place" (line 1), one that guards
`read` by "an input or a read place" and serves both from one store (line 2), and one that drops an
output call on an undeclared place without an error (line 3). A context that accepts an output on
any arc place of the transition, TypeScript's `read` without its guard, and a one-store context
that leaves only `input` or only `inputToken` unguarded are forbidden, so each conjunct of line 1
is load-bearing; the Rust and Python context, which checks key presence in the delivered maps, is
allowed.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## CORE-063: Context Structure Enforcement -/

requirement CORE_063
  id "CORE-063"
  title "Context Structure Enforcement"
  kind F
  scope "the transition context of every implementation; the inputToken part of line 1 only where the context gives access to tokens: Java and TypeScript"
  source verbatim "spec/01-core-model.md"
  covers CORE_063.s1, CORE_063.s2, CORE_063.s3, CORE_063.s4, CORE_063.s5, CORE_063.s6
  reading "For every value projection value and every context C, every transition t, every delivery δ (the tokens the firing consumed from each input place and the tokens its read arcs read), every output buffer e, every place p and every list of values vs:"
          "if p is not an input place of t and δ delivered no token from p, inputs, input and inputToken on t, δ and p each report an error;"
          "if p is not a read place of t and δ delivered no read token from p, read on t, δ and p reports an error;"
          "if p is not an output place of t, the output call on t, e, p and vs reports an error (it returns no buffer)."
  assumes "The model is the pair (value, C), the model of CORE-060 to CORE-062. C is a transition context (Ctx, Spec/GlossaryContext.lean): inputs, input, inputToken and read take the transition, the delivery and a place and return none when the call reports an error; output takes the transition, the buffer written so far, a place and the values of one call and returns none when the call reports an error, some of the new buffer otherwise. The value projection value : T → V is not used by the three lines; it keeps the block on the same model as CORE-060. The witness is the reference context refCtx."
          "'Declared in the transition's structure' is read per accessor: an input accessor needs an input arc (inPlaces), read needs a read arc (ReadArc), an output call needs a place the output specification names (OutputArc, glossary: Output arc; CORE-035, IO-017). It is not 'some arc of the transition names the place': a context that guards every accessor by that union answers inputs on an output place with the empty list and violates line 1 (CORE_063_mutant_anyArc_killed), and one that accepts an output on any arc place of the transition (a net-membership check) violates line 3 (CORE_063_forbids_anyArcOutput). Each conjunct of line 1 is load-bearing on its own: a context that keeps the consumed and the read tokens in one store (TypeScript's rawInput, Java's precompiled executor) and drops only the guard of input, or only that of inputToken, answers the read token of a read place and violates line 1 (CORE_063_forbids_unguardedInput, CORE_063_forbids_unguardedToken)."
          "Lines 1 and 2 range over the deliveries a firing makes at the place: line 1 takes a place from which the delivery holds no consumed token, line 2 a place from which it holds no read token. Every reference firing meets both premises (qDelivered_inputs_off, qDelivered_reads_off), and every runtime builds its delivery that way, as the fourth quoted sentence records: EXEC-010's line 3 and EXEC-012's line 7 require it of every executor, which CORE-061 records as core061_ByArcs (core061_byArcs_of). core063_on_firing gives the three lines on the delivery of any reference firing with no premise left, which is the reading of the three EARS sentences. On a delivery that breaks the premises, which no runtime makes, the block makes no claim. The premises accept the Rust and Python check, which is key presence in the maps of delivered tokens: Rust's input accessors answer from self.inputs.get(place_name) and read from self.reads.get(place_name) (TransitionContext::input, inputs and read in rust/libpetri-core/src/context.rs), the backends insert a key only when they push a token (consume_for_firing in rust/libpetri-runtime/src/bitmap_backend.rs), and Python copies those keys (rust/libpetri-py/src/action.rs from_transition_context). That context, core063_keyedCtx, satisfies CORE-063 (CORE_063_allows_keyed). Line 3 has no delivery premise: every runtime checks the output call against the output places of the transition (Rust require_output over allowed_outputs in context.rs; Java requireOutput over allowedOutputs, which the constructor sets to transition.outputPlaces() (TransitionContext.requireOutput in java/src/main/java/org/libpetri/core/TransitionContext.java); TypeScript requireOutput in typescript/src/core/transition-context.ts; Python require_output in rust/libpetri-py/src/action.rs)."
          "Line 1 is CORE-060 line 4, word for word in Lean (core063_line1_of_core060), and the inputToken part of it is scoped as CORE-060's is: Java and TypeScript have inputToken, the Rust and Python contexts expose values only. Line 2 is CORE-061 line 2 (core063_line2_iff_core061) and line 3 is CORE-062 line 2 (core063_line3_iff_core062), both by Iff.rfl, so a change to one formula breaks the build here; CORE_063_of_lines records that the block is the conjunction of the three error lines, and CORE_063_of_060_061_062 that a context that meets CORE-060, CORE-061 and CORE-062 meets CORE-063, which is the Depends on line. The EARS sentences of lines 2 and 3 restate CORE-061's and CORE-062's error sentences in other words on purpose: CORE-063 is the requirement that collects the three error rules, and the Iff.rfl theorems keep the restatement from drifting in Lean."
          "The fifth quoted sentence leaves the plural accessors out: Ctx has no field for them, as in CORE-061. Every implementation guards each with the check of the singular accessor of the same kind: Java reads and inputTokens call requireRead and requireInput (TransitionContext.inputTokens and TransitionContext.reads in java/src/main/java/org/libpetri/core/TransitionContext.java), TypeScript reads calls requireRead (TransitionContext.reads in typescript/src/core/transition-context.ts), Rust reads, read_tokens_raw and input_tokens_raw look the place up in the same map as read and inputs (rust/libpetri-core/src/context.rs), and Python reads uses the lookup of read (rust/libpetri-py/src/action.rs, resolve_lookup_key). That second half of the sentence is a description of the code, not a line of the block."
          "Line 2 says 'also on an input place': no place is both an input and a read place of one transition (ruling D15, NoInputRead), so an input place is a place that is not a read place. A context that keeps the consumed and the read tokens in one store and guards read by 'an input or a read place' meets the reading 'read reports an error on a place that is neither an input nor a read place' and violates line 2 (CORE_063_mutant_sharedSet_killed). TypeScript's context keeps one such store (TransitionContext.read answers from rawInput.value, typescript/src/core/transition-context.ts), so read depends on its own guard requireRead: without it, read answers the consumed token of an input place (CORE_063_forbids_unguardedRead)."
          "'Results in an error' is read as 'the call reports an error' (none): Rust returns an Err, Java throws IllegalArgumentException, TypeScript throws, Python raises. Whether the firing then fails is not CORE-063's: it fails only if the action lets the error out (EXEC-030), and a produce action passes it on (CORE-054 lines 3 and 4). An output call that silently drops the values meets the reading 'producing to an undeclared output declares no token' and violates line 3 (CORE_063_mutant_silentDrop_killed). Line 3 holds for every list of values, the empty one included, as the third quoted sentence says ('also when it passes no values'): every runtime checks the place before it iterates (CORE-062 AC3), so an empty bulk call on an undeclared place is an error too, and the call leaves no partial output."
          "Ruling D63 (a): the block is a rule on the calls an action makes through its context, and the last quoted sentence says so. Java and TypeScript expose the context's raw output collector (TransitionContext.rawOutput in java/src/main/java/org/libpetri/core/TransitionContext.java and typescript/src/core/transition-context.ts), documented internal and used by the executors; a token written there bypasses the check, and CORE-072 AC3 retains it as a token on an unknown place. That seam is not witnessed by any model of the joint consistency theorem, because CORE-035 line 1 and CONC-026 line 2 say that no firing deposits outside its output places. The firing-level statement is derived: core063_deposits_outputs shows that an action that writes through a context that satisfies CORE-063, whose successful output calls append only entries at the named place (core063_AppendsAt, CORE-062 line 1 gives it), deposits in a reference action firing only in output places of its transition."
          "The error sentences name the place the call resolves to (MOD-031), and the block reads every place that way: after instancing or port binding, Java, TypeScript and the Python binding adapter map a declared place the action names to the composed place first (MOD-031, W8). A type mismatch between the place and the value is API shape and not modelled: V is one type of values. Calls made after a timeout severed the firing's output (IO-013) are out of scope, as for CORE-062."
          "AC1 (accessing an undeclared input gives an error) is line 1."
          "AC2 (accessing an undeclared read gives an error) is line 2."
          "AC3 (producing to an undeclared output gives an error) is line 3."
          "The test derivation (create a context with restricted place sets, attempt out-of-bounds access, verify errors) is CORE_063_nonvacuous: on the reference firing of a transition with input place 0, read place 1 and output place 2, the reference context answers each accessor on its own place and reports an error for inputs, input and inputToken on the read and the output place, for read on the input and the output place, and for output on the input place and, with no values, on the read place."
  signoff "2026-11-13 6f3fb70f7a46effd ai"
  statement : ∀ {N T V : Type} [DecidableEq N], (T → V) → Ctx N T V → Prop :=
    fun _value C =>
      (∀ t δ p, p ∉ inPlaces t → δ.inputs p = [] →
        C.inputs t δ p = none ∧ C.input t δ p = none ∧ C.inputToken t δ p = none) ∧
      (∀ t δ p, ¬ ReadArc t p → δ.reads p = [] → C.read t δ p = none) ∧
      (∀ t e p vs, ¬ OutputArc t p → C.output t e p vs = none)

/- The pinned readable form of CORE-063: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CORE_063 : {N T V : Type} → [DecidableEq N] → (T → V) → Ctx N T V → Prop :=
fun {N T V} [DecidableEq N] _value C =>
  (∀ (t : Reference.Trans N) (δ : Delivered N T),
      ∀ p ∉ inPlaces t, δ.inputs p = [] → C.inputs t δ p = none ∧ C.input t δ p = none ∧ C.inputToken t δ p = none) ∧
    (∀ (t : Reference.Trans N) (δ : Delivered N T) (p : N), ¬ReadArc t p → δ.reads p = [] → C.read t δ p = none) ∧
      ∀ (t : Reference.Trans N) (e : List (N × V)) (p : N) (vs : List V), ¬OutputArc t p → C.output t e p vs = none
-/
#guard_msgs in #print CORE_063

/-! ### The three lines, named (for the mutants) -/

section Lines

variable {N T V : Type} [DecidableEq N]

/-- Line 1 of CORE-063: the input accessors report an error off the input places. -/
def core063_line1 (_value : T → V) (C : Ctx N T V) : Prop :=
  ∀ t δ p, p ∉ inPlaces t → δ.inputs p = [] →
    C.inputs t δ p = none ∧ C.input t δ p = none ∧ C.inputToken t δ p = none

/-- Line 2 of CORE-063: `read` reports an error off the read places. -/
def core063_line2 (_value : T → V) (C : Ctx N T V) : Prop :=
  ∀ t δ p, ¬ ReadArc t p → δ.reads p = [] → C.read t δ p = none

/-- Line 3 of CORE-063: an output call reports an error off the output places. -/
def core063_line3 (_value : T → V) (C : Ctx N T V) : Prop :=
  ∀ (t : Trans N) e p vs, ¬ OutputArc t p → C.output t e p vs = none

/-- CORE-063 is its three lines. -/
theorem core063_iff (value : T → V) (C : Ctx N T V) :
    CORE_063 value C ↔ core063_line1 value C ∧ core063_line2 value C ∧ core063_line3 value C :=
  Iff.rfl

omit [DecidableEq N] in
/-- Line 1 of CORE-063 is line 4 of CORE-060. -/
theorem core063_line1_iff_core060 (value : T → V) (C : Ctx N T V) :
    core063_line1 value C ↔ core060_line4 value C :=
  Iff.rfl

/-- A context that satisfies CORE-060 satisfies line 1 of CORE-063. -/
theorem core063_line1_of_core060 {value : T → V} {C : Ctx N T V} (h : CORE_060 value C) :
    core063_line1 value C :=
  h.2.2.2

/-- **CORE-063 restates three error lines**: CORE-060 line 4 with the read error line (CORE-061)
and the output error line (CORE-062) give CORE-063. -/
theorem CORE_063_of_lines {value : T → V} {C : Ctx N T V} (h60 : core060_line4 value C)
    (h61 : core063_line2 value C) (h62 : core063_line3 value C) : CORE_063 value C :=
  ⟨h60, h61, h62⟩

omit [DecidableEq N] in
/-- Line 2 of CORE-063 is line 2 of CORE-061 (the read error line). -/
theorem core063_line2_iff_core061 (value : T → V) (C : Ctx N T V) :
    core063_line2 value C ↔ core061_line2 value C :=
  Iff.rfl

omit [DecidableEq N] in
/-- Line 3 of CORE-063 is line 2 of CORE-062 (the output error line). -/
theorem core063_line3_iff_core062 (value : T → V) (C : Ctx N T V) :
    core063_line3 value C ↔ core062_line2 value C :=
  Iff.rfl

/-- **Depends on CORE-060, CORE-061 and CORE-062**: a context that meets the three blocks meets
CORE-063, through their error lines. -/
theorem CORE_063_of_060_061_062 {value : T → V} {C : Ctx N T V} (h60 : CORE_060 value C)
    (h61 : CORE_061 value C) (h62 : CORE_062 value C) : CORE_063 value C :=
  CORE_063_of_lines h60.2.2.2 h61.2 h62.2

end Lines

/-! ### The premises of lines 1 and 2 at a firing -/

/-- **CORE-063 on a firing**: on the delivery of a reference firing, a context that satisfies
CORE-063 reports an error from every input accessor on every place that is not an input place and
from `read` on every place that is not a read place, with no premise on the delivery left. -/
theorem core063_on_firing {N T V : Type} [DecidableEq N] {value : T → V} {C : Ctx N T V}
    (h : CORE_063 value C) (M : QueueMarking N T) (t : Trans N) (p : N) :
    (p ∉ inPlaces t → C.inputs t (qDelivered M t) p = none ∧
      C.input t (qDelivered M t) p = none ∧ C.inputToken t (qDelivered M t) p = none) ∧
    (¬ ReadArc t p → C.read t (qDelivered M t) p = none) :=
  ⟨fun hp => h.1 t _ p hp (qDelivered_inputs_off M t hp),
    fun hp => h.2.1 t _ p hp (qDelivered_reads_off M t hp)⟩

/-! ### The reference -/

/-- ✓ The reference context satisfies CORE-063, whatever the value projection. -/
@[evidence holds CORE_063]
theorem CORE_063_reference {N T V : Type} [DecidableEq N] (value : T → V) :
    CORE_063 value (refCtx (N := N) value) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t δ p hp _; simp [refCtx, hp]
  · intro t δ p hp _; simp [refCtx, hp]
  · intro t e p vs hp; simp [refCtx, hp]

/-- The reference context satisfies CORE-060 and CORE-063 together: the two blocks are stated
over one model and share a witness. -/
theorem core063_core060_ref {N T V : Type} [DecidableEq N] (value : T → V) :
    CORE_060 value (refCtx (N := N) value) ∧ CORE_063 value (refCtx (N := N) value) :=
  ⟨CORE_060_reference value, CORE_063_reference value⟩

/-! ### The bridge to the firing (ruling D63 (a)) -/

section Bridge

variable {N T V : Type} [DecidableEq N]

/-- A successful output call on the place `p` keeps the buffer it was given as a prefix and
appends only entries at `p` (CORE-062 line 1 gives it, with the values of the call). -/
def core063_AppendsAt (C : Ctx N T V) : Prop :=
  ∀ t e p vs e', C.output t e p vs = some e' → ∃ l, e' = e ++ l ∧ ∀ x ∈ l, x.1 = p

/-- Under CORE-063 a successful output call names an output place. -/
theorem core063_output_ok {value : T → V} {C : Ctx N T V} (h : CORE_063 value C)
    {t : Trans N} {e e' : List (N × V)} {p : N} {vs : List V}
    (hc : C.output t e p vs = some e') : OutputArc t p := by
  by_contra hp
  rw [h.2.2 t e p vs hp] at hc
  cases hc

/-- CORE-063 with appending at the named place gives the glossary's `OutputsOnlyDeclared`. -/
theorem core063_outputsOnlyDeclared {value : T → V} {C : Ctx N T V} (h : CORE_063 value C)
    (ha : core063_AppendsAt C) : OutputsOnlyDeclared C := by
  intro t e p vs e' hc
  obtain ⟨l, rfl, hl⟩ := ha t e p vs e' hc
  refine ⟨l, rfl, fun x hx => ?_⟩
  rw [hl x hx]
  exact core063_output_ok h hc

/-- **Bridge to [CORE-035] line 1 and [CONC-026] line 2** (ruling D63 (a)): an action that
writes through a context that satisfies CORE-063 and appends at the named place deposits, in a
reference action firing, only in output places of its transition. -/
theorem core063_deposits_outputs {value : T → V} {C : Ctx N T V} {val : T → V}
    {a : ActionRel N T} (h : CORE_063 value C) (ha : core063_AppendsAt C)
    (hT : ThroughCtx C val a) {t : Trans N} {M M' : QueueMarking N T} {δ : Delivered N T}
    {e : List (N × T)} (hf : refActionFire a t M δ e M') :
    ∀ p, Produced (e.map Prod.fst) p → OutputArc t p :=
  ctx_deposits_outputs (core063_outputsOnlyDeclared h ha) hT hf

/-- The reference context appends at the named place. -/
theorem refCtx_appendsAt (value : T → V) : core063_AppendsAt (refCtx (N := N) value) := by
  intro t e p vs e' hc
  by_cases hp : OutputArc t p
  · simp only [refCtx, hp, if_true, Option.some.injEq] at hc
    subst hc
    refine ⟨_, rfl, fun x hx => ?_⟩
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
    rfl
  · simp [refCtx, hp] at hc

end Bridge

/-! ### Examples

The transition `core060_u` of CORE-060: an input arc on place 0 that takes one token, a read arc
on place 1 and output `Place 2`; the marking `core060_M` holds the values 10, 11, 12 on place 0
and 7 on place 1. Tokens are pairs `(value, timestamp)` and the value projection is `Prod.fst`. -/

/-- The delivery of the reference firing of `core060_u` from `core060_M`. -/
abbrev core063_δ : Delivered Nat (Nat × Nat) := qDelivered core060_M core060_u

/-- ✓ CORE-063 is not vacuous. The test derivation: `u` fires from `core060_M` (a reference queue
firing); on its context the reference answers `inputs` on the input place 0, `read` on the read
place 1 and `output` on the output place 2, and reports an error for `inputs`, `input` and
`inputToken` on the read place 1 and on the output place 2, for `read` on the input place 0 and on
the output place 2, and for `output` on the input place 0 and, with no values, on the read place 1.
-/
@[evidence nonvacuous CORE_063]
theorem CORE_063_nonvacuous :
    RefQFire core060_u core060_M core063_δ [(2, (0, 9))]
      (qFire core060_M core060_u [(2, (0, 9))]) ∧
    core060_ref.inputs core060_u core063_δ 0 = some [10] ∧
    core060_ref.read core060_u core063_δ 1 = some 7 ∧
    core060_ref.output core060_u [] 2 [5] = some [(2, 5)] ∧
    core060_ref.inputs core060_u core063_δ 1 = none ∧
    core060_ref.inputs core060_u core063_δ 2 = none ∧
    core060_ref.input core060_u core063_δ 1 = none ∧
    core060_ref.input core060_u core063_δ 2 = none ∧
    core060_ref.inputToken core060_u core063_δ 1 = none ∧
    core060_ref.inputToken core060_u core063_δ 2 = none ∧
    core060_ref.read core060_u core063_δ 0 = none ∧
    core060_ref.read core060_u core063_δ 2 = none ∧
    core060_ref.output core060_u [] 0 [5] = none ∧
    core060_ref.output core060_u [(2, 5)] 1 [] = none := by
  refine ⟨⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩ <;> decide

/-! ### The Rust and Python shape: the declared check is key presence -/

/-- The Rust and Python context: the input accessors are CORE-060's keyed context, and `read`
answers a place exactly when the map of read tokens has a key for it, which the executor inserts
only when it reads a token (`TransitionContext::read` in rust/libpetri-core/src/context.rs,
`consume_for_firing` in rust/libpetri-runtime/src/bitmap_backend.rs). The output call checks the output places,
as the reference does. -/
def core063_keyedCtx {N T V : Type} [DecidableEq N] (value : T → V) : Ctx N T V :=
  { core060_keyedCtx value with read := fun _ δ p => ((δ.reads p).head?).map value }

/-- ✓ The keyed context satisfies CORE-063: the premises of lines 1 and 2 (no consumed token, no
read token from the place) are what every firing gives off the input and the read places, and
they are exactly what the key-presence check relies on. -/
@[evidence allows CORE_063]
theorem CORE_063_allows_keyed {N T V : Type} [DecidableEq N] (value : T → V) :
    CORE_063 value (core063_keyedCtx (N := N) value) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t δ p hp he
    exact (CORE_060_allows_keyed (N := N) value).2.2.2 t δ p hp he
  · intro t δ p _ he; simp [core063_keyedCtx, he]
  · intro t e p vs hp; simp [core063_keyedCtx, core060_keyedCtx, refCtx, hp]

/-! ### Wrong contexts: an output on any arc place, a read without its guard -/

/-- "Declared in the transition's structure" read as "some arc of the transition names the
place": an input, read, inhibitor or reset arc, or the output specification. -/
abbrev core063_ArcPlace {N : Type} [DecidableEq N] (t : Trans N) (p : N) : Prop :=
  p ∈ inPlaces t ∨ ReadArc t p ∨ InhibitorArc t p ∨ ResetArc t p ∨ OutputArc t p

/-- A context whose output call checks only that the transition has some arc on the place (a
net-membership check), and appends there. -/
def core063_anyArcOutputCtx {N T V : Type} [DecidableEq N] (value : T → V) : Ctx N T V :=
  { refCtx value with
    output := fun t e p vs => if core063_ArcPlace t p then some (e ++ vs.map fun v => (p, v))
      else none }

/-- ✗ It violates line 3: on `u`, an output call on the read place 1 appends instead of reporting
an error. -/
@[evidence forbids CORE_063]
theorem CORE_063_forbids_anyArcOutput :
    ¬ CORE_063 Prod.fst (core063_anyArcOutputCtx (N := Nat) (T := Nat × Nat) Prod.fst) := by
  intro h
  have := h.2.2 core060_u [] 1 [5] (by decide)
  exact absurd this (by decide)

/-- TypeScript's `read` without its `requireRead` guard: one store holds the consumed and the
read tokens, and `read` answers the first token the store holds for the place
(`this.rawInput.value(actual)`). -/
def core063_unguardedReadCtx {N T V : Type} [DecidableEq N] (value : T → V) : Ctx N T V :=
  { refCtx value with read := fun _ δ p => ((δ.reads p ++ δ.inputs p).head?).map value }

/-- ✗ It violates line 2: on the reference firing of `u`, `read` on the input place 0 answers the
consumed value 10 instead of an error. -/
@[evidence forbids CORE_063]
theorem CORE_063_forbids_unguardedRead :
    ¬ CORE_063 Prod.fst (core063_unguardedReadCtx (N := Nat) (T := Nat × Nat) Prod.fst) := by
  intro h
  have := h.2.1 core060_u core063_δ 0 (by decide) (by decide)
  exact absurd this (by decide)

/-- TypeScript's `input` without its `requireInput` guard, `inputs` and `inputToken` guarded: the
one store holds the read tokens too, and `input` answers the single token the store holds for the
place. -/
def core063_unguardedInputCtx {N T V : Type} [DecidableEq N] (value : T → V) : Ctx N T V :=
  { refCtx value with
    input := fun _ δ p => match δ.reads p ++ δ.inputs p with | [x] => some (value x) | _ => none }

/-- ✗ It violates line 1 at its `input` conjunct: on the reference firing of `u`, `input` on the
read place 1 answers the read value 7 instead of an error. -/
@[evidence forbids CORE_063]
theorem CORE_063_forbids_unguardedInput :
    ¬ CORE_063 Prod.fst (core063_unguardedInputCtx (N := Nat) (T := Nat × Nat) Prod.fst) := by
  intro h
  have := (h.1 core060_u core063_δ 1 (by decide) (by decide)).2.1
  exact absurd this (by decide)

/-- Java's and TypeScript's `inputToken` without its guard, `inputs` and `input` guarded: it
answers the oldest token the one store holds for the place. -/
def core063_unguardedTokenCtx {N T V : Type} [DecidableEq N] (value : T → V) : Ctx N T V :=
  { refCtx value with inputToken := fun _ δ p => (δ.reads p ++ δ.inputs p).head? }

/-- ✗ It violates line 1 at its `inputToken` conjunct: on the reference firing of `u`,
`inputToken` on the read place 1 answers the read token of value 7 instead of an error. -/
@[evidence forbids CORE_063]
theorem CORE_063_forbids_unguardedToken :
    ¬ CORE_063 Prod.fst (core063_unguardedTokenCtx (N := Nat) (T := Nat × Nat) Prod.fst) := by
  intro h
  have := (h.1 core060_u core063_δ 1 (by decide) (by decide)).2.2
  exact absurd this (by decide)

/-! ### Mutant: line 1 with one allowed set for every accessor -/

section MutantAnyArc

variable {N T V : Type} [DecidableEq N]

/-- Mutant reading of line 1 ("accessing an undeclared input" read as "accessing a place the
transition's structure does not name"): the input accessors report an error only on a place of
no arc of the transition. Lines 2 and 3 are as in CORE-063. -/
def CORE_063_mutant_anyArc (value : T → V) (C : Ctx N T V) : Prop :=
  (∀ t δ p, ¬ core063_ArcPlace t p → δ.inputs p = [] →
      C.inputs t δ p = none ∧ C.input t δ p = none ∧ C.inputToken t δ p = none) ∧
    core063_line2 value C ∧ core063_line3 value C

/-- A context whose input accessors answer every place some arc of the transition names, from
the delivery, and are the reference otherwise. -/
def core063_anyArcCtx (value : T → V) : Ctx N T V :=
  { refCtx value with
    inputs := fun t δ p => if core063_ArcPlace t p then some ((δ.inputs p).map value) else none
    input := fun t δ p =>
      if core063_ArcPlace t p then (match δ.inputs p with | [x] => some (value x) | _ => none)
      else none
    inputToken := fun t δ p => if core063_ArcPlace t p then (δ.inputs p).head? else none }

end MutantAnyArc

/-- ✗ The one-set context kills the mutant: it meets the "no arc at all" reading, but on `u` its
`inputs` answers the output place 2 with the empty list instead of an error (line 1). -/
@[evidence mutant CORE_063]
theorem CORE_063_mutant_anyArc_killed :
    CORE_063_mutant_anyArc Prod.fst (core063_anyArcCtx (N := Nat) (T := Nat × Nat) Prod.fst) ∧
      ¬ CORE_063 Prod.fst (core063_anyArcCtx (N := Nat) (T := Nat × Nat) Prod.fst) := by
  have hr := CORE_063_reference (N := Nat) (T := Nat × Nat) (Prod.fst : Nat × Nat → Nat)
  refine ⟨⟨fun t δ p hp _ => ?_, hr.2.1, hr.2.2⟩, fun h => ?_⟩
  · simp only [core063_anyArcCtx, if_neg hp, and_self]
  · have := (h.1 core060_u core063_δ 2 (by decide) (by decide)).1
    exact absurd this (by decide)

/-! ### Mutant: line 2 with one allowed set for inputs and reads -/

section MutantShared

variable {N T V : Type} [DecidableEq N]

/-- Mutant reading of line 2 ("accessing an undeclared read" read as "accessing a place that is
neither an input nor a read place"): `read` reports an error only off both. Lines 1 and 3 are as
in CORE-063. -/
def CORE_063_mutant_sharedSet (value : T → V) (C : Ctx N T V) : Prop :=
  core063_line1 value C ∧
    (∀ t δ p, ¬ ReadArc t p → p ∉ inPlaces t → δ.reads p = [] → C.read t δ p = none) ∧
    core063_line3 value C

/-- A context that keeps the consumed and the read tokens in one store and guards `read` by "an
input or a read place". -/
def core063_sharedSetCtx (value : T → V) : Ctx N T V :=
  { refCtx value with
    read := fun t δ p =>
      if ReadArc t p ∨ p ∈ inPlaces t then ((δ.reads p ++ δ.inputs p).head?).map value
      else none }

end MutantShared

/-- ✗ The shared-set context kills the mutant: it meets the "neither input nor read" reading, but
on the reference firing of `u` its `read` answers the input place 0 with the consumed value 10
(line 2). -/
@[evidence mutant CORE_063]
theorem CORE_063_mutant_sharedSet_killed :
    CORE_063_mutant_sharedSet Prod.fst
        (core063_sharedSetCtx (N := Nat) (T := Nat × Nat) Prod.fst) ∧
      ¬ CORE_063 Prod.fst (core063_sharedSetCtx (N := Nat) (T := Nat × Nat) Prod.fst) := by
  have hr := CORE_063_reference (N := Nat) (T := Nat × Nat) (Prod.fst : Nat × Nat → Nat)
  refine ⟨⟨hr.1, fun t δ p hr' hi _ => ?_, hr.2.2⟩, fun h => ?_⟩
  · simp [core063_sharedSetCtx, hr', hi]
  · have := h.2.1 core060_u core063_δ 0 (by decide) (by decide)
    exact absurd this (by decide)

/-! ### Mutant: line 3 as "declares no token" -/

section MutantDrop

variable {N T V : Type} [DecidableEq N]

/-- Mutant reading of line 3 ("producing to an undeclared output results in an error" read as
"declares no token there"): off the output places the call reports an error or succeeds with the
buffer unchanged. Lines 1 and 2 are as in CORE-063. -/
def CORE_063_mutant_silentDrop (value : T → V) (C : Ctx N T V) : Prop :=
  core063_line1 value C ∧ core063_line2 value C ∧
    (∀ t e p vs, ¬ OutputArc t p → C.output t e p vs = none ∨ C.output t e p vs = some e)

/-- A context whose output call on a place that is not an output place succeeds and drops the
values. -/
def core063_dropCtx (value : T → V) : Ctx N T V :=
  { refCtx value with
    output := fun t e p vs => if OutputArc t p then some (e ++ vs.map fun v => (p, v)) else some e }

end MutantDrop

/-- ✗ The dropping context kills the mutant: it meets the "declares no token" reading, but on `u`
an output call on the read place 1 succeeds instead of reporting an error (line 3). -/
@[evidence mutant CORE_063]
theorem CORE_063_mutant_silentDrop_killed :
    CORE_063_mutant_silentDrop Prod.fst (core063_dropCtx (N := Nat) (T := Nat × Nat) Prod.fst) ∧
      ¬ CORE_063 Prod.fst (core063_dropCtx (N := Nat) (T := Nat × Nat) Prod.fst) := by
  have hr := CORE_063_reference (N := Nat) (T := Nat × Nat) (Prod.fst : Nat × Nat → Nat)
  refine ⟨⟨hr.1, hr.2.1, fun t e p vs hp => .inr ?_⟩, fun h => ?_⟩
  · simp [core063_dropCtx, hp]
  · have := h.2.2 core060_u [] 1 [5] (by decide)
    exact absurd this (by decide)

end Libpetri.Spec
