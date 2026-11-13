import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryContext
import Libpetri.Spec.Req.EXEC_010
import Libpetri.Spec.Req.EXEC_012
import Libpetri.Spec.Text.CORE_061

set_option linter.missingDocs true

/-!
# CORE-061: Context read access (`spec/01-core-model.md`)

CORE-061 is a pure-function requirement (kind F) over a transition context `C : Ctx N T V`
(`Spec/GlossaryContext.lean`) and a value projection `value : T → V`. A context is a record of
accessor functions over the transition and what the firing delivered to its action (`Delivered`);
a result `none` is a call that reports an error.

The two lines: on a read place of the transition from which the delivery holds no consumed token
and holds a read token, `read` returns the value of the first such read token (line 1); on a place
that is not a read place and from which the delivery holds no read token, `read` reports an error,
an input place included (line 2). The two delivery premises are a property of the firing, not of
the context: a firing delivers read tokens only at read places and consumed tokens only at input
places (`core061_ByArcs`). The reference firing has it (`core061_refQFire_byArcs`), and so does
every queue firing relation that meets EXEC-010 and EXEC-012 (`core061_byArcs_of`: EXEC-010's
line 3 and EXEC-012's line 7), so the joint theorems take those requirements, not the property,
as hypotheses. The premises accept the two runtime shapes: the Rust and Python check, which is key
presence in the map of read tokens (`CORE_061_allows_keyed`), and the Java and TypeScript context,
which keeps consumed and read tokens in one store behind a read-place guard
(`CORE_061_allows_guardedShared`).

The witness is the reference context `refCtx`. The link to the firing is `core061_read_head` and
`core061_read_off`: together with EXEC-010 and EXEC-012 over a queue firing relation,
`read` returns the value of the oldest token of the read place, the firing leaves that token in
the place (when the place is not also a reset place), and `read` off the read places reports an
error. One wrong context per line is killed: one whose `read` always reports an error, and one that
serves `read` on an input place from the consumed tokens. One runtime-shaped slip is forbidden: a
single store for consumed and read tokens served through a `read` that lost its read-place guard.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## CORE-061: Context Read Access -/

requirement CORE_061
  id "CORE-061"
  title "Context Read Access"
  kind F
  scope "the transition context of every implementation"
  source verbatim "spec/01-core-model.md"
  covers CORE_061.s1, CORE_061.s2, CORE_061.s3
  reading "For every value projection value and every context C, every transition t, every delivery δ (the tokens the firing consumed from each input place and the tokens its read arcs read) and every place p:"
          "if p is a read place of t, δ consumed no token from p and the first token δ read at p is x, read on t, δ and p returns the value of x;"
          "if p is not a read place of t and δ read no token at p, read on t, δ and p reports an error, whether or not p is an input place of t."
  assumes "The model is the pair (value, C). C is a transition context (Ctx, Spec/GlossaryContext.lean): its accessor read takes the transition, the delivery and a place, and returns none when the call reports an error. A delivery (Delivered, Spec/GlossaryQueue.lean) is what the firing hands its action: the tokens it consumed from each input place and the tokens its read arcs read, per place. Tokens are the queue model's token identities T; value : T → V reads a token's value. The witness is the reference context refCtx."
          "The block is a function of the delivery, not of the marking. Which token a read arc reads is not CORE-061's but EXEC-012's: the head of the read place, after input consumption and before reset draining. core061_read_head derives, for any context that satisfies CORE-061, any pair (Build, Q) that satisfies EXEC-012 and whose Q satisfies EXEC-010, that on a firing of a transition with no input arc and read arc on one place read returns the value of the oldest token of the read place, and that the firing leaves the queue of a read place that is not a reset place as it was, followed by the tokens it deposits there (identity and order). That is the clause 'the oldest token the place holds' of the first quoted sentence. The second quoted sentence states EXEC-012 line 2 as a consequence for the action and is not a line of this block: it is the 'without consuming it' of AC1 and the 'token still in place' of the test derivation, and its exception names EXEC-013, under which a reset arc drains the place. The context itself is a function and consumes nothing."
          "The premises 'δ consumed no token from p' (line 1) and 'δ read no token at p' (line 2) are a property of the firing, not of the context: a firing delivers read tokens only at the read places of its transition and consumed tokens only at its input places (core061_ByArcs). The reference queue firing has it (core061_refQFire_byArcs, from qDelivered_reads_off and qDelivered_inputs_off), and every runtime builds its delivery that way. EXEC-010's line 3 (no consumed token from a place that is not an input place) and EXEC-012's line 7 (no read token from a place that is not a read place) state it for every executor, so every queue firing relation that meets both delivers by arcs (core061_byArcs_of). Under them the third quoted sentence holds at every firing (core061_read_off, from EXEC-012 alone), and the first does through core061_read_head."
          "Line 1 takes the first token read at the read place, from a delivery that holds no consumed token there. At a firing of a transition that builds both premises are what the firing gives: every token a firing delivers at a read place is the head of its queue (EXEC-012 line 1), so the first is the only value there is, and a transition with two read arcs on one place gets the head twice; and no read place is an input place (ruling D15), so under core061_ByArcs the firing consumed no token from it. On a delivery no firing makes, with two different read tokens at one place, line 1 still asks for the first: that is a deliberate choice, and every runtime takes the first entry (Rust tokens[0] in read, rust/libpetri-core/src/context.rs; Java's and TypeScript's TokenInput, TokenInput.get in java/src/main/java/org/libpetri/core/TokenInput.java). A context that answers the last read token agrees with refCtx at every firing and is rejected only on such a delivery. The premise that the delivery holds a read token at the read place holds at every firing, because a transition fires only while its read places are marked (CORE-032). On a read place from which the delivery holds no token, which no firing makes, the block makes no claim; refCtx and every runtime report an error there (Rust 'No tokens for read place', Python 'read place ... is empty', Java and TypeScript TokenInput.get)."
          "Java and TypeScript keep the consumed and the read tokens in one store (rawInput), filled with the consumed tokens first and the read tokens after them (fireTransition of BitmapNetExecutor and of PrecompiledNetExecutor in java/src/main/java/org/libpetri/runtime, and fireTransition in typescript/src/runtime/bitmap-net-executor.ts and typescript/src/runtime/precompiled-net-executor.ts, the latter with fireTransitionMatched for a join, each running its input loop before the read-arc peek), and read checks its guard requireRead and then answers the first entry of that store at the place (TransitionContext.read in java/src/main/java/org/libpetri/core/TransitionContext.java and typescript/src/core/transition-context.ts). That context, core061_guardedSharedCtx, satisfies CORE-061 (CORE_061_allows_guardedShared), because line 1 takes a delivery with no consumed token at the read place, and at every firing of a transition that builds, under core061_ByArcs, it answers read as refCtx at every place (core061_guarded_agrees). Without the premise, line 1 would reject it on a delivery no firing makes (core061_strict_rejects_guarded). The same store served through a read without its guard is forbidden (CORE_061_forbids_sharedStore)."
          "A context whose read always reports an error meets the reading 'read returns a read value when it returns one' and violates line 1 (CORE_061_mutant_soundOnly_killed)."
          "Line 2 reads 'results in an error' as 'the call reports an error' (none): Rust returns an error, Java and TypeScript throw, Python raises. 'An undeclared read place' is any place that is not a read place of the transition: an input place, an output place, or a place of no arc of the transition. A context with one allowed set for inputs and reads, which answers read on an input place with the value of a consumed token, meets the reading 'read reports an error on a place the transition does not declare at all' and violates line 2 (CORE_061_mutant_anyDeclared_killed). No place is both an input place and a read place of a transition that builds (ruling D15, EXEC-012), so the two lines never meet on one place at a firing."
          "Line 2 accepts the Rust and Python check, which is key presence in the map of read tokens, not membership in the read places: Rust's read answers from self.reads.get(place_name) (rust/libpetri-core/src/context.rs), the backends insert a key only when they push a read token (consume_for_firing in rust/libpetri-runtime/src/bitmap_backend.rs, peek_reads in rust/libpetri-runtime/src/precompiled_backend.rs), and Python copies those keys (rust/libpetri-py/src/action.rs from_transition_context). That context, core061_keyedCtx, satisfies CORE-061 (CORE_061_allows_keyed), and on every delivery that holds read tokens at exactly the read places it answers read as refCtx at every place (core061_keyed_agrees). It is correct only under core061_ByArcs, which is why that property is named above."
          "The third quoted sentence is word for word the second quoted sentence of CORE-063, and line 2 is the same formula as CORE-063's line 2. CORE-061 is the requirement that states the rule, as its AC2; CORE-063 depends on CORE-061 and collects the error lines of CORE-060 to CORE-062, so the citation runs from CORE-063 to CORE-061 and not back."
          "The error sentence names the place the call resolves to (MOD-031), and the block reads every place that way: after instancing or port binding, Java, TypeScript and the Python binding adapter map a declared place the action names to the composed place first (MOD-031, W8). A type mismatch between the place and the value (Rust's downcast error) is API shape and not modelled: V is one type of values. Further accessors (reads(place) in Java, TypeScript, Rust and Python, Rust's read_tokens_raw) are not part of the block."
          "AC1 (read(place) returns the read value without consuming it) is line 1, with 'without consuming it' from EXEC-012 line 2 through core061_read_head."
          "AC2 (accessing an undeclared read place results in an error) is line 2, and at a firing core061_read_off."
          "The test derivation (fire a transition with a read arc, verify read() returns the value, verify the token is still in place) is CORE_061_nonvacuous: a reference firing of a transition with an input arc on place 0 and a read arc on place 1, which holds 7 then 8, delivers the token of value 7 at place 1, the reference context returns 7, the firing leaves 7 and 8 in place 1, and read on the input place 0 and on the output place 2 reports an error. CORE_061_joint_example derives the same answers through core061_read_head and core061_read_off from EXEC-012's reference pair."
  signoff "2026-11-13 6f385fd4cc9dc684 ai"
  statement : ∀ {N T V : Type} [DecidableEq N], (T → V) → Ctx N T V → Prop :=
    fun value C =>
      (∀ t δ p x, ReadArc t p → δ.inputs p = [] → (δ.reads p).head? = some x →
        C.read t δ p = some (value x)) ∧
      (∀ t δ p, ¬ ReadArc t p → δ.reads p = [] → C.read t δ p = none)

/- The pinned readable form of CORE-061: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CORE_061 : {N T V : Type} → [DecidableEq N] → (T → V) → Ctx N T V → Prop :=
fun {N T V} [DecidableEq N] value C =>
  (∀ (t : Reference.Trans N) (δ : Delivered N T) (p : N) (x : T),
      ReadArc t p → δ.inputs p = [] → (δ.reads p).head? = some x → C.read t δ p = some (value x)) ∧
    ∀ (t : Reference.Trans N) (δ : Delivered N T) (p : N), ¬ReadArc t p → δ.reads p = [] → C.read t δ p = none
-/
#guard_msgs in #print CORE_061

/-! ### The two lines, named (for the mutants) -/

section Lines

variable {N T V : Type} [DecidableEq N]

/-- Line 1 of CORE-061: `read` on a read place, from which the delivery holds no consumed token,
returns the value of the first token read there. -/
def core061_line1 (value : T → V) (C : Ctx N T V) : Prop :=
  ∀ t δ p x, ReadArc t p → δ.inputs p = [] → (δ.reads p).head? = some x →
    C.read t δ p = some (value x)

/-- Line 2 of CORE-061: `read` reports an error off the read places, input places included. -/
def core061_line2 (_value : T → V) (C : Ctx N T V) : Prop :=
  ∀ t δ p, ¬ ReadArc t p → δ.reads p = [] → C.read t δ p = none

/-- CORE-061 is its two lines. -/
theorem core061_iff (value : T → V) (C : Ctx N T V) :
    CORE_061 value C ↔ core061_line1 value C ∧ core061_line2 value C :=
  Iff.rfl

end Lines

/-! ### The reference -/

/-- ✓ The reference context satisfies CORE-061, whatever the value projection. -/
@[evidence holds CORE_061]
theorem CORE_061_reference {N T V : Type} [DecidableEq N] (value : T → V) :
    CORE_061 value (refCtx (N := N) value) := by
  refine ⟨?_, ?_⟩
  · intro t δ p x hp _ hx; simp [refCtx, hp, hx]
  · intro t δ p hp _; simp [refCtx, hp]

/-! ### The delivery premises at a firing

A firing delivers read tokens only at the read places of its transition and consumed tokens only
at its input places. The reference firing has this property, and EXEC-010's line 3 and EXEC-012's
line 7 state it for every queue firing relation that meets them (`core061_byArcs_of`). -/

section Delivery

variable {N T : Type} [DecidableEq N]

/-- **Delivers by arcs**: every firing of `Q` delivers read tokens only at read places of its
transition and consumed tokens only at its input places. -/
def core061_ByArcs (Q : QFireRel N T) : Prop :=
  ∀ t M δ e M', Q t M δ e M' → ∀ p,
    (¬ ReadArc t p → δ.reads p = []) ∧ (p ∉ inPlaces t → δ.inputs p = [])

/-- ✓ The reference queue firing delivers by arcs. -/
theorem core061_refQFire_byArcs : core061_ByArcs (N := N) (T := T) RefQFire := by
  intro t M δ e M' h p
  obtain ⟨_, _, rfl, _⟩ := h
  exact ⟨qDelivered_reads_off M t, qDelivered_inputs_off M t⟩

/-- A queue firing relation that meets EXEC-010 and EXEC-012 delivers by arcs: EXEC-010's line 3
and EXEC-012's line 7. -/
theorem core061_byArcs_of [ToString N] {Build : Trans N → Option String} {Q : QFireRel N T}
    (h10 : EXEC_010 Q) (h12 : EXEC_012 Build Q) : core061_ByArcs Q :=
  fun t M δ e M' hf p =>
    ⟨fun hp => h12.2.2.2 t p δ e hp M M' hf, fun hp => h10.2.2 t δ e p hp M M' hf⟩

omit [DecidableEq N] in
/-- Under ruling D15 a read place is no input place. -/
theorem core061_notIn_of_read {t : Trans N} (hw : NoInputRead t) {p : N} (hp : ReadArc t p) :
    p ∉ inPlaces t := by
  intro hi
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hi
  exact hw s hs hp

end Delivery

/-! ### Consequences in the joint model (with EXEC-012) -/

/-- **The third quoted sentence at a firing**: on a firing of a queue firing relation that meets
EXEC-012 (its line 7: no read token off the read places), a context that satisfies CORE-061
reports an error for `read` on every place that is not a read place of the transition, an input
place included. -/
theorem core061_read_off {N T V : Type} [DecidableEq N] [ToString N] {value : T → V}
    {C : Ctx N T V} {Build : Trans N → Option String} {Q : QFireRel N T}
    (hC : CORE_061 value C) (hQ : EXEC_012 Build Q) {t : Trans N}
    {M M' : QueueMarking N T} {δ : Delivered N T} {e : List (N × T)} (hf : Q t M δ e M')
    {p : N} (hp : ¬ ReadArc t p) : C.read t δ p = none :=
  hC.2 t δ p hp (hQ.2.2.2 t p δ e hp M M' hf)

section Joint

variable {N T V : Type} [DecidableEq N] [ToString N]

/-- **Joint with EXEC-010 and EXEC-012**: on a firing of a queue firing relation that satisfies
both, of a transition with no input arc and read arc on one place (every transition
that builds, ruling D15), a context that satisfies CORE-061 returns from `read` the value of the
oldest token of the read place; and when the place is not also a reset place, the firing leaves
its queue as it was, followed by the tokens it deposits there: the read consumes nothing. -/
theorem core061_read_head {value : T → V} {C : Ctx N T V} {Build : Trans N → Option String}
    {Q : QFireRel N T} (hC : CORE_061 value C) (hQ : EXEC_012 Build Q) (h10 : EXEC_010 Q)
    {t : Trans N} {M M' : QueueMarking N T} {δ : Delivered N T} {e : List (N × T)}
    (hf : Q t M δ e M') (hw : NoInputRead t) {p : N} (hp : ReadArc t p) {x : T}
    (hx : Head M p = some x) :
    C.read t δ p = some (value x) ∧ (¬ ResetArc t p → AppendedAtTail M M' e p) :=
  ⟨hC.1 t δ p x hp (h10.2.2 t δ e p (core061_notIn_of_read hw hp) M M' hf)
      (((hQ.1 t p δ e hw hp) M M' hf).1.trans hx),
    fun hr => (hQ.2.1 t p δ e hw hp hr) M M' hf⟩

end Joint

/-! ### Examples

Tokens are pairs `(value, timestamp)` and the value projection is `Prod.fst`. -/

/-- `r`: an input arc on place 0 that takes one token, a read arc on place 1, output `Place 2`. -/
def core061_r : Trans Nat :=
  { core := { name := "r", inputs := [⟨0, .one⟩], inhibitors := [], reads := [1], resets := [] },
    out := some (.place 2) }

/-- Place 0 holds the value 10 (stamped 1), place 1 the values 7 then 8 (stamped 0 and 5);
every other place is empty. -/
def core061_M : QueueMarking Nat (Nat × Nat) := fun p =>
  if p = 0 then [(10, 1)] else if p = 1 then [(7, 0), (8, 5)] else []

/-- The emission of the examples: one token of value 0 to the output place 2. -/
def core061_e : List (Nat × (Nat × Nat)) := [(2, (0, 9))]

/-- The reference context with the value projection `Prod.fst`. -/
abbrev core061_ref : Ctx Nat (Nat × Nat) Nat := refCtx Prod.fst

/-- ✓ CORE-061 is not vacuous. The test derivation: `r` fires from `core061_M` (a reference
queue firing), the read arc reads the oldest token `(7, 0)` of place 1, the reference context
returns its value 7, and the firing leaves `(7, 0)` and `(8, 5)` in place 1. On the input place 0
and on the output place 2, `read` reports an error. -/
@[evidence nonvacuous CORE_061]
theorem CORE_061_nonvacuous :
    RefQFire core061_r core061_M (qDelivered core061_M core061_r) core061_e
      (qFire core061_M core061_r core061_e) ∧
    core061_ref.read core061_r (qDelivered core061_M core061_r) 1 = some 7 ∧
    qFire core061_M core061_r core061_e 1 = [(7, 0), (8, 5)] ∧
    core061_ref.read core061_r (qDelivered core061_M core061_r) 0 = none ∧
    core061_ref.read core061_r (qDelivered core061_M core061_r) 2 = none := by
  refine ⟨⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The reference firing of `r` from `core061_M`. -/
theorem core061_fire_r :
    RefQFire core061_r core061_M (qDelivered core061_M core061_r) core061_e
      (qFire core061_M core061_r core061_e) :=
  ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩

/-- ✓ The same answers through the joint theorems: from EXEC-012's reference pair (`refBuild`,
`RefQFire`), EXEC-010's reference firing and the reference context,
`core061_read_head` gives on the firing of `r` the value 7 of the head of place 1 and a place 1
left as it was, and `core061_read_off` gives an error for `read` on the input place 0. -/
@[evidence nonvacuous CORE_061]
theorem CORE_061_joint_example :
    (refCtx (N := Nat) (T := Nat × Nat) Prod.fst).read core061_r (qDelivered core061_M core061_r) 1 = some 7 ∧
      AppendedAtTail core061_M (qFire core061_M core061_r core061_e) core061_e 1 ∧
      (refCtx (N := Nat) (T := Nat × Nat) Prod.fst).read core061_r (qDelivered core061_M core061_r) 0 = none :=
  have h := core061_read_head (CORE_061_reference Prod.fst) EXEC_012_reference
    EXEC_010_reference core061_fire_r (by decide) (p := 1) (by decide) (x := (7, 0))
    (by decide)
  ⟨h.1, h.2 (by decide),
    core061_read_off (CORE_061_reference Prod.fst) EXEC_012_reference core061_fire_r
      (p := 0) (by decide)⟩

/-! ### The Rust and Python shape: the declared check is key presence -/

section Keyed

variable {N T V : Type} [DecidableEq N]

/-- The Rust and Python context: `read` answers a place exactly when the map of read tokens has
a key for it, and the executor inserts a key only when it pushes a read token
(`read` in rust/libpetri-core/src/context.rs, `consume_for_firing` in
rust/libpetri-runtime/src/bitmap_backend.rs,
rust/libpetri-py/src/action.rs `from_transition_context`). An empty list under a key is an error too. -/
def core061_keyedCtx (value : T → V) : Ctx N T V :=
  { refCtx value with read := fun _ δ p => ((δ.reads p).head?).map value }

/-- A delivery a firing of `t` makes: it holds read tokens at exactly the read places of `t`. -/
def core061_FromReads (t : Trans N) (δ : Delivered N T) : Prop :=
  ∀ p, δ.reads p ≠ [] ↔ ReadArc t p

/-- On every delivery that holds read tokens at exactly the read places, the keyed context
answers `read` as the reference context, at every place. -/
theorem core061_keyed_agrees (value : T → V) (t : Trans N) (δ : Delivered N T)
    (h : core061_FromReads t δ) (p : N) :
    (core061_keyedCtx value).read t δ p = (refCtx value).read t δ p := by
  by_cases hp : ReadArc t p
  · simp [core061_keyedCtx, refCtx, hp]
  · have he : δ.reads p = [] := by
      by_contra hne; exact hp ((h p).1 hne)
    simp [core061_keyedCtx, refCtx, hp, he]

end Keyed

/-- ✓ The keyed context satisfies CORE-061: the premise of line 2 (no read token at a place that
is not a read place) is what a firing that delivers by arcs gives, and it is exactly what the
key-presence check relies on. -/
@[evidence allows CORE_061]
theorem CORE_061_allows_keyed {N T V : Type} [DecidableEq N] (value : T → V) :
    CORE_061 value (core061_keyedCtx (N := N) value) := by
  refine ⟨?_, ?_⟩
  · intro t δ p x _ _ hx; simp [core061_keyedCtx, hx]
  · intro t δ p _ he; simp [core061_keyedCtx, he]

/-! ### The Java and TypeScript shape: one store behind a read-place guard -/

section Guarded

variable {N T V : Type} [DecidableEq N]

/-- The Java and TypeScript context: consumed and read tokens in one store (`rawInput`), the
consumed tokens first; `read` checks the read-place guard (`requireRead`) and answers the first
entry of the store at the place (`read` in java/src/main/java/org/libpetri/core/TransitionContext.java and in
typescript/src/core/transition-context.ts). -/
def core061_guardedSharedCtx (value : T → V) : Ctx N T V :=
  { refCtx value with
    read := fun t δ p => if ReadArc t p then ((δ.inputs p ++ δ.reads p).head?).map value else none }

/-- At every firing of a transition that builds (ruling D15), of a queue firing relation that
delivers by arcs, the guarded shared store answers `read` as the reference context, at every
place. -/
theorem core061_guarded_agrees (value : T → V) {Q : QFireRel N T} (hD : core061_ByArcs Q)
    {t : Trans N} {M M' : QueueMarking N T} {δ : Delivered N T} {e : List (N × T)}
    (hf : Q t M δ e M') (hw : NoInputRead t) (p : N) :
    (core061_guardedSharedCtx value).read t δ p = (refCtx value).read t δ p := by
  by_cases hp : ReadArc t p
  · have hi := (hD t M δ e M' hf p).2 (core061_notIn_of_read hw hp)
    simp [core061_guardedSharedCtx, refCtx, hp, hi]
  · simp [core061_guardedSharedCtx, refCtx, hp]

/-- Line 1 without the premise that the delivery holds no consumed token at the read place. -/
def core061_line1_strict (value : T → V) (C : Ctx N T V) : Prop :=
  ∀ t δ p x, ReadArc t p → (δ.reads p).head? = some x → C.read t δ p = some (value x)

end Guarded

/-- ✓ The guarded shared store satisfies CORE-061: line 1 takes a delivery with no consumed token
at the read place, and line 2 is the guard. -/
@[evidence allows CORE_061]
theorem CORE_061_allows_guardedShared {N T V : Type} [DecidableEq N] (value : T → V) :
    CORE_061 value (core061_guardedSharedCtx (N := N) value) := by
  refine ⟨?_, ?_⟩
  · intro t δ p x hp hi hx; simp [core061_guardedSharedCtx, hp, hi, hx]
  · intro t δ p hp _; simp [core061_guardedSharedCtx, hp]

/-- A delivery for `r` that no firing makes: a consumed token `(99, 0)` at the read place 1, ahead
of the read token `(7, 0)`. -/
def core061_offδ : Delivered Nat (Nat × Nat) :=
  ⟨fun p => if p = 1 then [(99, 0)] else [], fun p => if p = 1 then [(7, 0)] else []⟩

/-- Why line 1 carries its consumed-token premise: without it, line 1 rejects the shipped Java and
TypeScript context on `core061_offδ`, a delivery no firing makes, where the store answers 99
ahead of the read value 7. -/
theorem core061_strict_rejects_guarded :
    ¬ core061_line1_strict Prod.fst
      (core061_guardedSharedCtx (N := Nat) (T := Nat × Nat) Prod.fst) := by
  intro h
  have := h core061_r core061_offδ 1 (7, 0) (by decide) (by decide)
  exact absurd this (by decide)

/-! ### Wrong context: one shared store without the read guard -/

/-- A context that keeps the consumed and the read tokens in one store and serves `read` from it
on any place, without the read-place guard (TypeScript's `return this.rawInput.value(actual)`
without its `requireRead` call). -/
def core061_sharedCtx {N T V : Type} [DecidableEq N] (value : T → V) : Ctx N T V :=
  { refCtx value with read := fun _ δ p => ((δ.inputs p ++ δ.reads p).head?).map value }

/-- ✗ It violates line 2: on the reference firing of `r`, place 0 is an input place and no read
place, the firing reads no token there, and `read` answers the value 10 of the consumed token
instead of an error. -/
@[evidence forbids CORE_061]
theorem CORE_061_forbids_sharedStore :
    ¬ CORE_061 Prod.fst (core061_sharedCtx (N := Nat) (T := Nat × Nat) Prod.fst) := by
  intro h
  have := h.2 core061_r (qDelivered core061_M core061_r) 0 (by decide) (by decide)
  exact absurd this (by decide)

/-! ### Mutant: line 1 as soundness only -/

section MutantSound

variable {N T V : Type} [DecidableEq N]

/-- Mutant reading of line 1 ("returns the read value" read as "a value `read` returns is a read
one"): `read` may always report an error. Line 2 is as in CORE-061. -/
def CORE_061_mutant_soundOnly (value : T → V) (C : Ctx N T V) : Prop :=
  (∀ t δ p v, ReadArc t p → C.read t δ p = some v → ∃ x ∈ δ.reads p, v = value x) ∧
    core061_line2 value C

/-- A context whose `read` always reports an error. -/
def core061_noReadCtx (value : T → V) : Ctx N T V :=
  { refCtx value with read := fun _ _ _ => none }

end MutantSound

/-- ✗ The context without `read` kills the mutant: it meets the soundness reading, but on the
firing of `r`, which reads the token `(7, 0)` at place 1 and consumes nothing there, its `read`
reports an error (line 1). -/
@[evidence mutant CORE_061]
theorem CORE_061_mutant_soundOnly_killed :
    CORE_061_mutant_soundOnly Prod.fst (core061_noReadCtx (N := Nat) (T := Nat × Nat) Prod.fst) ∧
      ¬ CORE_061 Prod.fst (core061_noReadCtx (N := Nat) (T := Nat × Nat) Prod.fst) := by
  refine ⟨⟨fun _ _ _ _ _ h => (by cases h), fun _ _ _ _ _ => rfl⟩, fun h => ?_⟩
  have := h.1 core061_r (qDelivered core061_M core061_r) 1 (7, 0) (by decide) (by decide)
    (by decide)
  cases this

/-! ### Mutant: line 2 as "a place the transition does not declare at all" -/

section MutantDeclared

variable {N T V : Type} [DecidableEq N]

/-- Mutant reading of line 2 ("an undeclared read place" read as "a place the transition
declares neither as a read place nor as an input place", one allowed set for inputs and reads):
`read` reports an error only off both. Line 1 is as in CORE-061. -/
def CORE_061_mutant_anyDeclared (value : T → V) (C : Ctx N T V) : Prop :=
  core061_line1 value C ∧
    (∀ t δ p, ¬ ReadArc t p → p ∉ inPlaces t → δ.reads p = [] → C.read t δ p = none)

/-- A context with one allowed set for inputs and reads: `read` on a read place answers the first
read token, on an input place the first consumed token. -/
def core061_unionCtx (value : T → V) : Ctx N T V :=
  { refCtx value with
    read := fun t δ p =>
      if ReadArc t p then ((δ.reads p).head?).map value
      else if p ∈ inPlaces t then ((δ.inputs p).head?).map value else none }

end MutantDeclared

/-- ✗ The one-allowed-set context kills the mutant: it meets the "not declared at all" reading,
but on the firing of `r` its `read` answers the input place 0 with the value 10 of the consumed
token instead of an error (line 2). -/
@[evidence mutant CORE_061]
theorem CORE_061_mutant_anyDeclared_killed :
    CORE_061_mutant_anyDeclared Prod.fst (core061_unionCtx (N := Nat) (T := Nat × Nat) Prod.fst) ∧
      ¬ CORE_061 Prod.fst (core061_unionCtx (N := Nat) (T := Nat × Nat) Prod.fst) := by
  refine ⟨⟨fun t δ p x hp _ hx => ?_, fun t δ p hp hi _ => ?_⟩, fun h => ?_⟩
  · simp [core061_unionCtx, hp, hx]
  · simp [core061_unionCtx, hp, hi]
  · have := h.2 core061_r (qDelivered core061_M core061_r) 0 (by decide) (by decide)
    exact absurd this (by decide)

end Libpetri.Spec
