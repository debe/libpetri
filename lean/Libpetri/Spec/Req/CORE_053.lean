import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryContext
import Libpetri.Spec.Req.CORE_050

set_option linter.missingDocs true

/-!
# CORE-053: Transform action (`spec/01-core-model.md`)

CORE-053 is a pure-function requirement (kind F) over the transform combinator
`X : TransformFn N T V → ActionRel N T`: it takes the host's function `f` and gives the action
the transition runs. The host's function is a relation (`TransformFn`): handed the transition and
what the firing delivered (`Delivered`, the transition context of [CORE-050]), one call of it may
return a value `v`, having written the tokens `w` through the context first, or may fail. A
relation, not a function, because the function may read the world: one delivery may give more
than one value, and that is what tells "one call" from "one call per output place". Tokens are
compared on their values through the value projection `val : T → V`, never on their identity or
stamp.

The three lines: every completion of the transform comes from one call of `f` on the delivery the
action was handed, and is, place by place, what that call wrote followed by one token carrying the
returned value in every place the output specification names (`TransformCopies`); every call of
`f` that returns gives such a completion; and the transform fails only when a call of `f` on that
delivery fails. The witness is `refTransform val`, which appends one token carrying the value to
the call's writes, once per place of the output specification, and fails when the call fails.

Wrong transforms are killed: one per line (a transform that calls `f` once per output place, one
that never ends, and one that may fail after `f` returned), one that writes only the first output
place, one that hands `f` an empty context, one that drops what `f` wrote, one that puts the copy
before what `f` wrote, and one that walks the output places with their repeats.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## Vocabulary of the block -/

/-- **The host's transform function** ([CORE-053]): `f t δ (.ok (w, v))` says that one call of
`f`, handed the transition `t` and what the firing delivered `δ` (its transition context), may
return the value `v` after writing the tokens `w` (places and tokens, in the order written)
through the context; `f t δ (.error m)` says that one call may fail with the message `m`. A
relation, because the function may read the world. -/
abbrev TransformFn (N T V : Type) :=
  Trans N → Delivered N T → Except String (List (N × T) × V) → Prop

section Vocab

variable {N T V : Type} [DecidableEq N]

/-- **The transform's output, place by place**: the emission `e` holds, in every place the output
specification of `t` names, the tokens `w` sent there followed by exactly one token carrying the
value `v`, and in every other place exactly the tokens `w` sent there. -/
def TransformCopies (val : T → V) (t : Trans N) (w : List (N × T)) (v : V)
    (e : List (N × T)) : Prop :=
  ∀ p, (OutputArc t p → ∃ x, val x = v ∧ EmittedTo e p = EmittedTo w p ++ [x]) ∧
    (¬ OutputArc t p → EmittedTo e p = EmittedTo w p)

/-- **The reference transform**: one call of `f` on the delivery returns `v` after writing `w`,
and the action completes with `w`, followed by one token `x` carrying `v` in each place of the
output specification; or one call fails, and the action fails with its message. Which token
carries `v` (its stamp) is the host's, so the reference leaves it open. -/
def refTransform (val : T → V) : TransformFn N T V → ActionRel N T := fun f t δ r =>
  (∃ w v x, f t δ (.ok (w, v)) ∧ val x = v ∧ r = .ok (w ++ (outPlaceSet t).map (·, x))) ∨
    (∃ m, f t δ (.error m) ∧ r = .error m)

/- The reference transform is the witness model of CORE-053. -/
#spec_witness refTransform

end Vocab

/-! ## CORE-053: Transform Action -/

requirement CORE_053
  id "CORE-053"
  title "Transform Action"
  kind F
  scope "implementations that provide transform()"
  source verbatim "spec/01-core-model.md"
  quote "*When* a transition fires under the transform action, the action *shall* call its function with the transition context of that firing, and *shall* complete or fail with the outcome of one such call."
        "*When* the function returns a value, the transform action *shall* complete with the output tokens the function wrote through the context, followed in every place the output spec names by one token carrying that value."
  reading "Let X be the transform: X f is the action built from the host's function f; f t δ (ok (w, v)) says that one call of f, handed the transition t and the delivery δ, may return v after writing w through the context, and f t δ (error m) that one call may fail; val reads the value a token carries."
          "For every function f, transition t, delivery δ and emission e: if the action X f, handed t and δ, completes with e, then some single call of f on that same t and δ wrote w and returned v, and in every place the output specification of t names e holds the tokens w sent there followed by exactly one token carrying v, and in every other place exactly the tokens w sent there."
          "For every function f, transition t, delivery δ, writes w and value v that some token carries: if one call of f, handed t and δ, may write w and return v, then X f, handed t and δ, may complete with an emission of that shape for w and v."
          "For every function f, transition t, delivery δ and message m: if the action X f, handed t and δ, fails with m, then some call of f on that same t and δ fails."
  assumes "The model is the pair (val, X). X is the transform combinator: from the host's function f (TransformFn: a relation from the transition and what the firing delivered to the outcome of one call, either the tokens the function wrote through the context and the value it returned, or a failure) it gives the action X f (ActionRel, Spec/GlossaryAction.lean; glossary: Action). val : T → V reads the value a token carries, so tokens are compared on their values, never on their identity or creation stamp: the stamp of a copied token is the host's (CORE-011), and Rust stamps each copy at its own output call (rust/libpetri-core/src/context.rs output_raw). The witness is refTransform val."
          "The function is a relation, not a function, because it may read the world: one delivery may give more than one value, or a value on one call and a failure on another. That is what makes 'one such call' a line: a transform that calls the function once per output place may copy a different value to each place (CORE_053_mutant_perPlace_killed), and a transform whose emission is the writes of two calls is no single call's writes."
          "How many times the function is called beyond the call that accounts for the outcome is not observable in a relational model, and a transform that makes an extra call and discards its result is not excluded: the first sentence says which call the outcome comes from, not how many calls are made."
          "Line 1 reads both sentences from the completion's side: the function is called on the transition context of the firing (the transition and the delivery the action was handed; CORE-050 line 1 makes that the firing's delivery), and the completion is one call's writes followed by the copies. Its accessors (input, inputs, inputToken, read, output) are CORE-060 to CORE-063's. A transform that hands the function an empty context (CORE_053_forbids_blind), that drops what the function wrote (CORE_053_forbids_dropWrites), that puts the copy before what the function wrote (CORE_053_forbids_copiesFirst), that writes only the first output place (CORE_053_forbids_firstOnly) or that copies once per occurrence of a place the output specification names twice (CORE_053_forbids_rawList) violates it."
          "Line 1 is stated per place (EmittedTo): the order of the copies across places is not stated. Rust iterates a hash set of the output places, Java and TypeScript iterate the transition's output place set; each place receives exactly one copy, after what the function wrote there, which is what the marking sees (EXEC-020 appends per place in emission order)."
          "Line 2 reads the second sentence's 'shall complete' from the side of the call: a call of the function that returns a value gives a completion. A transform that never ends, with neither a completion nor a failure, holds of lines 1 and 3 alone (CORE_053_mutant_soundOnly_killed). The premise that some token carries v holds in every runtime (any value can be put in a token) and keeps the line true at every model type."
          "Line 3 reads 'complete or fail with the outcome of one such call' and the second sentence's 'shall complete' from the side of a failure: the transform fails only when a call of its function on the same transition and delivery fails, so a transform that may fail after its function returned, such as a copy loop whose output call can fail, violates it (CORE_053_mutant_noFailLine_killed). The failure's message is not compared. Rust's function returns a value and has no failure channel, and its copy loop names only declared output places, so its output call does not fail there and the Rust transform never fails; Java and TypeScript catch the function's exception and fail the action, as the reference does with the call's message."
          "Whether a failing call must make the transform fail, and how a failure is handled, are EXEC-030's. The function's own writes are output calls through the context, so which places they may name is CORE-062 and CORE-063's: when every write list the function returns is built by output calls of a context that meets CORE-062 line 1, the transform writes through that context (refTransform_throughCtx), and an action that writes through a context whose output calls append only on output places deposits only in output places (ctx_deposits_outputs, core053_deposits_outputs). The execution context of CORE-064 is not modelled."
          "The place set is the glossary's output arc (OutputArc: every place the output specification names, all branches of an XOR, the child of a Timeout, the destination of a ForwardInput), the same set every runtime hands the context (rust/libpetri-core/src/output.rs all_places; Java Transition.outputPlaces; TypeScript TransitionContext.outputPlaces). On a specification with more than one output branch the copies fill every branch, so the completion fills no single branch and the firing ends with no completion of the action (IO-015, EXEC-021; core053_xor_never_fires). The markdown's note under CORE-053 says so for the reader."
          "In the joint model a firing that ends with the completion of the transform deposits that completion (CORE-050 line 2), so it deposits one call's writes followed by one copy per output place (core053_firing_copies)."
          "AC1 (the function receives the transition context) is line 1: the call that accounts for the completion is a call on the transition and the delivery the action was handed (CORE_053_forbids_blind)."
          "AC2 (the return value is produced to all output places) is lines 1 and 2: every completion carries one token with the returned value in every place the output specification names, and every returned value gives such a completion (CORE_053_forbids_firstOnly). transform(place, fn), transformFrom and transformAsync are API shape, not encoded."
          "The test derivation (a transform that doubles an integer input; all outputs receive the doubled value) is CORE_053_nonvacuous: the doubling function on a delivery of 7, under AND(Place 1, Place 2), completes with 14 in place 1 and 14 in place 2, and the reference action firing deposits both; besides, a function that fails makes the reference transform fail, so the premise of line 3 is met."
  signoff "pending"
  statement : ∀ {N T V : Type} [DecidableEq N], (T → V) → (TransformFn N T V → ActionRel N T) → Prop :=
    fun val X =>
      (∀ f t δ e, X f t δ (.ok e) → ∃ w v, f t δ (.ok (w, v)) ∧ TransformCopies val t w v e) ∧
      (∀ f t δ w v, f t δ (.ok (w, v)) → (∃ x, val x = v) →
        ∃ e, X f t δ (.ok e) ∧ TransformCopies val t w v e) ∧
      (∀ f t δ m, X f t δ (.error m) → ∃ m', f t δ (.error m'))

/- The pinned readable form of CORE-053: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CORE_053 : {N T V : Type} → [DecidableEq N] → (T → V) → (TransformFn N T V → ActionRel N T) → Prop :=
fun {N T V} [DecidableEq N] val X =>
  (∀ (f : TransformFn N T V) (t : Reference.Trans N) (δ : Delivered N T) (e : List (N × T)),
      X f t δ (Except.ok e) → ∃ w v, f t δ (Except.ok (w, v)) ∧ TransformCopies val t w v e) ∧
    (∀ (f : TransformFn N T V) (t : Reference.Trans N) (δ : Delivered N T) (w : List (N × T)) (v : V),
        f t δ (Except.ok (w, v)) → (∃ x, val x = v) → ∃ e, X f t δ (Except.ok e) ∧ TransformCopies val t w v e) ∧
      ∀ (f : TransformFn N T V) (t : Reference.Trans N) (δ : Delivered N T) (m : String),
        X f t δ (Except.error m) → ∃ m', f t δ (Except.error m')
-/
#guard_msgs in #print CORE_053

/-! ### The three lines, named (for the mutants) -/

section Lines

variable {N T V : Type} [DecidableEq N]

/-- Line 1 of CORE-053: every completion is one call's writes followed by one copy of its value
in every output place. -/
def core053_line1 (val : T → V) (X : TransformFn N T V → ActionRel N T) : Prop :=
  ∀ f t δ e, X f t δ (.ok e) → ∃ w v, f t δ (.ok (w, v)) ∧ TransformCopies val t w v e

/-- Line 2 of CORE-053: every call that returns gives a completion of that shape. -/
def core053_line2 (val : T → V) (X : TransformFn N T V → ActionRel N T) : Prop :=
  ∀ f t δ w v, f t δ (.ok (w, v)) → (∃ x, val x = v) →
    ∃ e, X f t δ (.ok e) ∧ TransformCopies val t w v e

/-- Line 3 of CORE-053: the transform fails only when a call of its function fails. -/
def core053_line3 (X : TransformFn N T V → ActionRel N T) : Prop :=
  ∀ f t δ m, X f t δ (.error m) → ∃ m', f t δ (.error m')

/-- CORE-053 is its three lines. -/
theorem core053_iff (val : T → V) (X : TransformFn N T V → ActionRel N T) :
    CORE_053 val X ↔ core053_line1 val X ∧ core053_line2 val X ∧ core053_line3 X :=
  Iff.rfl

end Lines

/-! ### Lemmas on emissions -/

section Emit

variable {N T : Type} [DecidableEq N]

/-- The writes followed by one token `x` per output place have the transform's shape for every
value `x` carries. -/
theorem transformCopies_append {V : Type} (val : T → V) (t : Trans N) (w : List (N × T)) (x : T) :
    TransformCopies val t w (val x) (w ++ (outPlaceSet t).map (·, x)) := by
  intro p
  rw [emittedTo_append, emittedTo_outPlaceSet]
  refine ⟨fun hp => ⟨x, rfl, ?_⟩, fun hp => ?_⟩
  · rw [if_pos hp]
  · rw [if_neg hp, List.append_nil]

end Emit

/-! ### The reference -/

/-- ✓ The reference transform satisfies CORE-053: its completions are one call's writes followed
by one copy per output place, every call that returns gives one, and it fails only with a call
that fails. -/
@[evidence holds CORE_053]
theorem CORE_053_reference {N T V : Type} [DecidableEq N] (val : T → V) :
    CORE_053 (N := N) val (refTransform val) := by
  refine ⟨fun f t δ e h => ?_, fun f t δ w v hf ⟨x, hx⟩ => ?_, fun f t δ m h => ?_⟩
  · rcases h with ⟨w, v, x, hf, hx, he⟩ | ⟨m, -, he⟩
    · cases he
      subst hx
      exact ⟨w, val x, hf, transformCopies_append val t w x⟩
    · cases he
  · subst hx
    exact ⟨_, .inl ⟨w, val x, x, hf, rfl, rfl⟩, transformCopies_append val t w x⟩
  · rcases h with ⟨w, v, x, -, -, he⟩ | ⟨m', hf, -⟩
    · cases he
    · exact ⟨m', hf⟩

/-! ### Consequences in the joint model -/

section Joint

variable {N T V : Type} [DecidableEq N]

/-- **With CORE-050**: a firing that ends with the completion of a transform deposits one call's
writes followed by one copy of the returned value in every output place. -/
theorem core053_firing_copies {Q : QFireRel N T} {AF : ActFireRel N T} (h50 : CORE_050 Q AF)
    {val : T → V} {X : TransformFn N T V → ActionRel N T} (h53 : CORE_053 val X)
    {f : TransformFn N T V} {t : Trans N} {M M' : QueueMarking N T} {δ : Delivered N T}
    {e : List (N × T)} (hf : AF (X f) t M δ e M') :
    ∃ w v, f t δ (.ok (w, v)) ∧ TransformCopies val t w v e :=
  h53.1 f t δ e (h50.2.1 _ t δ e M M' hf)

/-- **The reference transform writes through the context**: under a context whose output call on
an output place appends one entry per value (CORE-062 line 1), if every write list the function
returns is built by successful output calls of that context, then every emission the reference
transform completes with is too: the function's writes followed by one single output call per
output place. -/
theorem refTransform_throughCtx {C : Ctx N T V} (val : T → V)
    (hC : ∀ t e p vs, OutputArc t p → C.output t e p vs = some (e ++ vs.map fun v => (p, v)))
    {f : TransformFn N T V}
    (hw : ∀ t δ w v, f t δ (.ok (w, v)) → Built C t (w.map fun x => (x.1, val x.2))) :
    ThroughCtx C val (refTransform val f) := by
  intro t δ e h
  rcases h with ⟨w, v, x, hf, -, he⟩ | ⟨m, -, he⟩
  · cases he
    have hb := built_append_copies hC (hw t δ w v hf) (outPlaceSet t)
      (fun p hp => (mem_outPlaceSet t p).1 hp) (val x)
    simpa [List.map_map, Function.comp_def] using hb
  · cases he

/-- **Bridge to [CORE-035] line 1 at the transform**: with a context as in
`refTransform_throughCtx` whose output calls append only on output places, a reference action
firing under the reference transform deposits only in output places of its transition. -/
theorem core053_deposits_outputs {C : Ctx N T V} {val : T → V}
    (hC : ∀ t e p vs, OutputArc t p → C.output t e p vs = some (e ++ vs.map fun v => (p, v)))
    (hO : OutputsOnlyDeclared C) {f : TransformFn N T V}
    (hw : ∀ t δ w v, f t δ (.ok (w, v)) → Built C t (w.map fun x => (x.1, val x.2)))
    {t : Trans N} {M M' : QueueMarking N T} {δ : Delivered N T} {e : List (N × T)}
    (hf : refActionFire (refTransform val f) t M δ e M') : ∀ p ∈ e.map Prod.fst, OutputArc t p :=
  ctx_deposits_outputs hO (refTransform_throughCtx val hC hw) hf

end Joint

/-! ### Examples -/

/-- `tAnd`: one input arc on place 0, output `AND(Place 1, Place 2)`. -/
def core053_tAnd : Trans Nat :=
  { core :=
      { name := "double", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.and (.place 1) (.place 2)) }

/-- `tXor`: one input arc on place 0, output `XOR(Place 1, Place 2)`. -/
def core053_tXor : Trans Nat :=
  { core :=
      { name := "choose", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.xor (.place 1) (.place 2)) }

/-- `tDup`: one input arc on place 0, output `AND(Place 1, Place 1)`, naming place 1 twice. -/
def core053_tDup : Trans Nat :=
  { core := { name := "dup", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.and (.place 1) (.place 1)) }

/-- Place 0 holds 7; every other place is empty. -/
def core053_M : QueueMarking Nat Nat := fun p => if p = 0 then [7] else []

/-- The empty delivery. -/
def core053_δ0 : Delivered Nat Nat := ⟨fun _ => [], fun _ => []⟩

/-- The test derivation's function: it writes nothing and returns twice the oldest token
delivered from place 0; it never fails. -/
def core053_double : TransformFn Nat Nat Nat := fun _ δ r =>
  r = .ok ([], 2 * (δ.inputs 0).headD 0)

/-- A function that reads the world: it writes nothing and returns 1 or 2. -/
def core053_oneOrTwo : TransformFn Nat Nat Nat := fun _ _ r => r = .ok ([], 1) ∨ r = .ok ([], 2)

/-- A function that writes a token 5 in place 3 and returns 0. -/
def core053_writes : TransformFn Nat Nat Nat := fun _ _ r => r = .ok ([(3, 5)], 0)

/-- A function that writes a token 5 in output place 1 and returns 0. -/
def core053_writes1 : TransformFn Nat Nat Nat := fun _ _ r => r = .ok ([(1, 5)], 0)

/-- A function that writes nothing and returns 0. -/
def core053_zero : TransformFn Nat Nat Nat := fun _ _ r => r = .ok ([], 0)

/-- A function that always fails. -/
def core053_throws : TransformFn Nat Nat Nat := fun _ _ r => r = .error "boom"

/-- The reference context of the test derivation: the delivery of `tAnd` from place 0 holding 7
is 7. -/
theorem core053_delivery : (qDelivered core053_M core053_tAnd).inputs 0 = [7] := by decide

/-- On the test derivation's delivery, the one outcome of the doubling function is 14, with no
writes. -/
theorem core053_double_iff {r : Except String (List (Nat × Nat) × Nat)} :
    core053_double core053_tAnd (qDelivered core053_M core053_tAnd) r ↔ r = .ok ([], 14) := by
  show r = .ok ([], 2 * ((qDelivered core053_M core053_tAnd).inputs 0).headD 0) ↔ _
  rw [core053_delivery]; rfl

/-- `outPlaceSet tAnd` is places 1 and 2. -/
theorem core053_outSet_and : outPlaceSet core053_tAnd = [1, 2] := by decide

/-- ✓ CORE-053 is not vacuous. The test derivation: the doubling transform on `AND(Place 1,
Place 2)`, handed the delivery of 7, completes with 14 in place 1 and 14 in place 2, and the
reference action firing (CORE-050) deposits both, leaving place 0 empty. Besides, a function that
fails makes the reference transform fail (the premise of line 3). -/
@[evidence nonvacuous CORE_053]
theorem CORE_053_nonvacuous :
    refTransform id core053_double core053_tAnd (qDelivered core053_M core053_tAnd)
      (.ok [(1, 14), (2, 14)]) ∧
    refActionFire (refTransform id core053_double) core053_tAnd core053_M
      (qDelivered core053_M core053_tAnd) [(1, 14), (2, 14)]
      (qFire core053_M core053_tAnd [(1, 14), (2, 14)]) ∧
    qFire core053_M core053_tAnd [(1, 14), (2, 14)] 1 = [14] ∧
    qFire core053_M core053_tAnd [(1, 14), (2, 14)] 2 = [14] ∧
    qFire core053_M core053_tAnd [(1, 14), (2, 14)] 0 = [] ∧
    refTransform id core053_throws core053_tAnd (qDelivered core053_M core053_tAnd)
      (.error "boom") := by
  have hT : refTransform id core053_double core053_tAnd (qDelivered core053_M core053_tAnd)
      (.ok [(1, 14), (2, 14)]) := by
    refine .inl ⟨[], 14, 14, core053_double_iff.2 rfl, rfl, ?_⟩
    rw [core053_outSet_and]; rfl
  refine ⟨hT, ⟨⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩, ?_, hT⟩, by decide, by decide, by decide,
    .inr ⟨"boom", rfl, rfl⟩⟩
  show ([1, 2] : List Nat) ∈ [[1, 2]]
  exact List.mem_singleton.2 rfl

/-- **IO-015 consequence**: on `XOR(Place 1, Place 2)` no transform that meets line 1 ends a
reference action firing with a function that writes nothing, since the copies fill both branches
and the completion fills no single one. -/
theorem core053_xor_never_fires {X : TransformFn Nat Nat Nat → ActionRel Nat Nat}
    (h : core053_line1 id X) {f : TransformFn Nat Nat Nat}
    (hw : ∀ t δ w v, f t δ (.ok (w, v)) → w = []) {M M' : QueueMarking Nat Nat}
    {δ : Delivered Nat Nat} {e : List (Nat × Nat)} :
    ¬ refActionFire (X f) core053_tXor M δ e M' := by
  rintro ⟨-, hb, ha⟩
  obtain ⟨w, v, hf, hc⟩ := h f _ δ e ha
  have hw0 := hw _ _ _ _ hf
  subst hw0
  have h1 : OutputArc core053_tXor 1 := by decide
  have h2 : OutputArc core053_tXor 2 := by decide
  obtain ⟨x1, -, hx1⟩ := (hc 1).1 h1
  obtain ⟨x2, -, hx2⟩ := (hc 2).1 h2
  have hb' : e.map Prod.fst = [1] ∨ e.map Prod.fst = [2] := by
    have : e.map Prod.fst ∈ [[1], [2]] := hb
    simpa using this
  rcases hb' with hb' | hb'
  · match e, hb' with
    | [(1, y)], _ => exact absurd hx2 (by simp [EmittedTo, qEmittedTo])
  · match e, hb' with
    | [(2, y)], _ => exact absurd hx1 (by simp [EmittedTo, qEmittedTo])

/-! ### Wrong transforms -/

section Wrong

variable {N T V : Type} [DecidableEq N]

/-- A transform that writes the copy only in the first place of the output specification. -/
def core053_firstOnly (val : T → V) : TransformFn N T V → ActionRel N T := fun f t δ r =>
  ∃ w v x, f t δ (.ok (w, v)) ∧ val x = v ∧ r = .ok (w ++ ((outPlaceSet t).take 1).map (·, x))

/-- A transform that hands its function an empty context: no token delivered. -/
def core053_blind (val : T → V) : TransformFn N T V → ActionRel N T := fun f t _ r =>
  ∃ w v x, f t ⟨fun _ => [], fun _ => []⟩ (.ok (w, v)) ∧ val x = v ∧
    r = .ok (w ++ (outPlaceSet t).map (·, x))

/-- A transform that drops what its function wrote through the context. -/
def core053_dropWrites (val : T → V) : TransformFn N T V → ActionRel N T := fun f t δ r =>
  ∃ w v x, f t δ (.ok (w, v)) ∧ val x = v ∧ r = .ok ((outPlaceSet t).map (·, x))

/-- A transform that buffers what its function wrote and flushes it after the copy loop (the
Java and TypeScript slip of a write target swapped for the call), so in a place the function
also writes the copy comes first. -/
def core053_copiesFirst (val : T → V) : TransformFn N T V → ActionRel N T := fun f t δ r =>
  ∃ w v x, f t δ (.ok (w, v)) ∧ val x = v ∧ r = .ok ((outPlaceSet t).map (·, x) ++ w)

/-- A transform whose copy loop walks the output specification's place list with its repeats
(`outPlaces`) instead of the set of places it names. -/
def core053_rawList (val : T → V) : TransformFn N T V → ActionRel N T := fun f t δ r =>
  ∃ w v x, f t δ (.ok (w, v)) ∧ val x = v ∧
    r = .ok (w ++ (match t.out with | some o => outPlaces o | none => []).map (·, x))

/-- A transform that calls its function once per output place: one call for the writes, then
one call per place for the value copied there. -/
def core053_perPlace (val : T → V) : TransformFn N T V → ActionRel N T := fun f t δ r =>
  ∃ w v, f t δ (.ok (w, v)) ∧ ∃ e, r = .ok e ∧
    ∀ p, (OutputArc t p →
        ∃ x w', f t δ (.ok (w', val x)) ∧ EmittedTo e p = EmittedTo w p ++ [x]) ∧
      (¬ OutputArc t p → EmittedTo e p = EmittedTo w p)

/-- A transform that never ends: no completion and no failure. -/
def core053_never (_val : T → V) : TransformFn N T V → ActionRel N T := fun _ _ _ _ => False

/-- The reference transform, which may also fail after a call of its function returned (a copy
loop whose output call can fail). -/
def core053_mayFail (val : T → V) : TransformFn N T V → ActionRel N T := fun f t δ r =>
  refTransform val f t δ r ∨ (∃ w v, f t δ (.ok (w, v)) ∧ r = .error "output")

end Wrong

/-- ✗ A transform that writes only the first output place violates line 2: the doubling function
returns 14 on `AND(Place 1, Place 2)`, and no completion puts 14 in place 2. -/
@[evidence forbids CORE_053]
theorem CORE_053_forbids_firstOnly :
    ¬ CORE_053 (N := Nat) (id : Nat → Nat) (core053_firstOnly id) := by
  intro h
  obtain ⟨e, ⟨w, v, x, hfw, -, he⟩, hc⟩ := h.2.1 _ _ _ _ _ (core053_double_iff.2 rfl) ⟨14, rfl⟩
  have hw := core053_double_iff.1 hfw
  cases hw
  cases he
  obtain ⟨y, -, hy⟩ := (hc 2).1 (by decide)
  rw [core053_outSet_and] at hy
  have : EmittedTo ([] ++ ([1, 2].take 1).map (·, x)) 2 = [] := by
    simp [EmittedTo, qEmittedTo]
  rw [this] at hy
  have := congrArg List.length hy
  simp at this

/-- ✗ A transform that hands its function an empty context violates line 1: on the delivery of 7
it completes with 0 in both places, which no call of the doubling function on that delivery
returns. -/
@[evidence forbids CORE_053]
theorem CORE_053_forbids_blind :
    ¬ CORE_053 (N := Nat) (id : Nat → Nat) (core053_blind id) := by
  intro h
  have hb : core053_blind id core053_double core053_tAnd (qDelivered core053_M core053_tAnd)
      (.ok [(1, 0), (2, 0)]) :=
    ⟨[], 0, 0, rfl, rfl, by rw [core053_outSet_and]; rfl⟩
  obtain ⟨w, v, hf, hc⟩ := h.1 _ _ _ _ hb
  have hf' := core053_double_iff.1 hf
  cases hf'
  obtain ⟨y, hy, hx⟩ := (hc 1).1 (by decide)
  simp [EmittedTo, qEmittedTo] at hx
  subst hx
  simp at hy

/-- ✗ A transform that drops what its function wrote violates line 1: the function writes a token
5 in place 3, and the completion leaves place 3 empty. -/
@[evidence forbids CORE_053]
theorem CORE_053_forbids_dropWrites :
    ¬ CORE_053 (N := Nat) (id : Nat → Nat) (core053_dropWrites id) := by
  intro h
  have hd : core053_dropWrites id core053_writes core053_tAnd
      (qDelivered core053_M core053_tAnd) (.ok [(1, 0), (2, 0)]) :=
    ⟨[(3, 5)], 0, 0, rfl, rfl, by rw [core053_outSet_and]; rfl⟩
  obtain ⟨w, v, hf, hc⟩ := h.1 _ _ _ _ hd
  cases hf
  have h3 : ¬ OutputArc core053_tAnd 3 := by decide
  have := (hc 3).2 h3
  simp [EmittedTo, qEmittedTo] at this

/-- ✗ A transform that puts the copy before what its function wrote violates line 1: the function
writes 5 in output place 1 and returns 0, and the completion holds 0 then 5 in place 1, where the
written 5 must come first. -/
@[evidence forbids CORE_053]
theorem CORE_053_forbids_copiesFirst :
    ¬ CORE_053 (N := Nat) (id : Nat → Nat) (core053_copiesFirst id) := by
  intro h
  have hm : core053_copiesFirst id core053_writes1 core053_tAnd
      (qDelivered core053_M core053_tAnd) (.ok [(1, 0), (2, 0), (1, 5)]) :=
    ⟨[(1, 5)], 0, 0, rfl, rfl, by rw [core053_outSet_and]; rfl⟩
  obtain ⟨w, v, hf, hc⟩ := h.1 _ _ _ _ hm
  cases hf
  obtain ⟨y, -, hy⟩ := (hc 1).1 (by decide)
  simp [EmittedTo, qEmittedTo] at hy

/-- ✗ A transform whose copy loop walks the output places with their repeats violates line 1: on
`AND(Place 1, Place 1)` it puts two copies of the value in place 1. -/
@[evidence forbids CORE_053]
theorem CORE_053_forbids_rawList :
    ¬ CORE_053 (N := Nat) (id : Nat → Nat) (core053_rawList id) := by
  intro h
  have hm : core053_rawList id core053_zero core053_tDup core053_δ0
      (.ok [(1, 0), (1, 0)]) := ⟨[], 0, 0, rfl, rfl, rfl⟩
  obtain ⟨w, v, hf, hc⟩ := h.1 _ _ _ _ hm
  cases hf
  obtain ⟨y, -, hy⟩ := (hc 1).1 (by decide)
  have := congrArg List.length hy
  simp [EmittedTo, qEmittedTo] at this

/-! ### Mutant: line 1 with the function called once per output place -/

/-- Mutant reading of line 1 ("copies the result to all output places" read without "one such
call"): every copy carries a value some call of the function returns, not one call's value.
Lines 2 and 3 are as in CORE-053. -/
def CORE_053_mutant_perPlace {N T V : Type} [DecidableEq N] (val : T → V)
    (X : TransformFn N T V → ActionRel N T) : Prop :=
  (∀ f t δ e, X f t δ (.ok e) → ∃ w v, f t δ (.ok (w, v)) ∧
    ∀ p, (OutputArc t p →
        ∃ x w', f t δ (.ok (w', val x)) ∧ EmittedTo e p = EmittedTo w p ++ [x]) ∧
      (¬ OutputArc t p → EmittedTo e p = EmittedTo w p)) ∧
  core053_line2 val X ∧ core053_line3 X

/-- ✗ The per-place transform kills the mutant: it meets the wrong reading, but with a function
that returns 1 or 2 it completes on `AND(Place 1, Place 2)` with 1 in place 1 and 2 in place 2,
which no single call returns (line 1). -/
@[evidence mutant CORE_053]
theorem CORE_053_mutant_perPlace_killed :
    CORE_053_mutant_perPlace (N := Nat) (id : Nat → Nat) (core053_perPlace id) ∧
      ¬ CORE_053 (N := Nat) (id : Nat → Nat) (core053_perPlace id) := by
  refine ⟨⟨fun f t δ e h => ?_, fun f t δ w v hf ⟨x, hx⟩ => ?_, fun f t δ m h => ?_⟩, fun h => ?_⟩
  · obtain ⟨w, v, hf, e', he, hc⟩ := h
    cases he
    exact ⟨w, v, hf, hc⟩
  · subst hx
    have hc := transformCopies_append (id : Nat → Nat) t w x
    refine ⟨_, ⟨w, x, hf, _, rfl, fun p => ⟨fun hp => ?_, (hc p).2⟩⟩, hc⟩
    obtain ⟨y, hy, he⟩ := (hc p).1 hp
    exact ⟨y, w, by rw [show (id y : Nat) = x from hy]; exact hf, he⟩
  · obtain ⟨_, _, _, _, he, _⟩ := h
    cases he
  · have hp : core053_perPlace id core053_oneOrTwo core053_tAnd
        (qDelivered core053_M core053_tAnd) (.ok [(1, 1), (2, 2)]) := by
      refine ⟨[], 1, .inl rfl, _, rfl, fun p => ⟨fun hp => ?_, fun hp => ?_⟩⟩
      · have hp' : p = 1 ∨ p = 2 := by
          have : p ∈ outPlaceSet core053_tAnd := (mem_outPlaceSet _ _).2 hp
          rw [core053_outSet_and] at this
          simpa using this
        rcases hp' with rfl | rfl
        · exact ⟨1, [], .inl rfl, by decide⟩
        · exact ⟨2, [], .inr rfl, by decide⟩
      · have h1 : p ≠ 1 := fun h => hp (h ▸ by decide)
        have h2 : p ≠ 2 := fun h => hp (h ▸ by decide)
        simp [EmittedTo, qEmittedTo, Ne.symm h1, Ne.symm h2]
    obtain ⟨w, v, hf, hc⟩ := h.1 _ _ _ _ hp
    obtain ⟨y1, hy1, he1⟩ := (hc 1).1 (by decide)
    obtain ⟨y2, hy2, he2⟩ := (hc 2).1 (by decide)
    have hw : w = [] := by
      rcases hf with hf | hf <;> cases hf <;> rfl
    subst hw
    simp [EmittedTo, qEmittedTo] at he1 he2
    subst he1 he2
    simp at hy1 hy2
    omega

/-! ### Mutant: no completion line -/

/-- Mutant reading: lines 1 and 3 alone, without the second sentence's "shall complete" read from
the side of the call. It holds of the transform that never ends. -/
def CORE_053_mutant_soundOnly {N T V : Type} [DecidableEq N] (val : T → V)
    (X : TransformFn N T V → ActionRel N T) : Prop :=
  core053_line1 val X ∧ core053_line3 X

/-- ✗ The transform that never ends kills the mutant: it meets lines 1 and 3 (it neither
completes nor fails), but the doubling function returns 14 and the transform gives no completion
(line 2). -/
@[evidence mutant CORE_053]
theorem CORE_053_mutant_soundOnly_killed :
    CORE_053_mutant_soundOnly (N := Nat) (id : Nat → Nat) (core053_never id) ∧
      ¬ CORE_053 (N := Nat) (id : Nat → Nat) (core053_never id) := by
  refine ⟨⟨fun _ _ _ _ h => h.elim, fun _ _ _ _ h => h.elim⟩, fun h => ?_⟩
  obtain ⟨e, he, -⟩ := h.2.1 _ _ _ _ _ (core053_double_iff.2 rfl) ⟨14, rfl⟩
  exact he

/-! ### Mutant: no failure line -/

/-- Mutant reading: lines 1 and 2 alone, without "complete or fail with the outcome of one such
call" read from the side of a failure. It holds of a transform that may fail after its function
returned. -/
def CORE_053_mutant_noFailLine {N T V : Type} [DecidableEq N] (val : T → V)
    (X : TransformFn N T V → ActionRel N T) : Prop :=
  core053_line1 val X ∧ core053_line2 val X

/-- ✗ The transform that may fail after its function returned kills the mutant: it meets lines 1
and 2 (its completions are the reference's), but on the test derivation's delivery, where the
doubling function only ever returns 14, it may fail, and no call of the function fails there
(line 3). -/
@[evidence mutant CORE_053]
theorem CORE_053_mutant_noFailLine_killed :
    CORE_053_mutant_noFailLine (N := Nat) (id : Nat → Nat) (core053_mayFail id) ∧
      ¬ CORE_053 (N := Nat) (id : Nat → Nat) (core053_mayFail id) := by
  have href := CORE_053_reference (N := Nat) (id : Nat → Nat)
  refine ⟨⟨fun f t δ e h => ?_, fun f t δ w v hf hx => ?_⟩, fun h => ?_⟩
  · rcases h with h | ⟨_, _, _, h⟩
    · exact href.1 f t δ e h
    · cases h
  · obtain ⟨e, he, hc⟩ := href.2.1 f t δ w v hf hx
    exact ⟨e, .inl he, hc⟩
  · obtain ⟨m', hf⟩ := h.2.2 core053_double core053_tAnd (qDelivered core053_M core053_tAnd)
      "output" (.inr ⟨[], 14, core053_double_iff.2 rfl, rfl⟩)
    cases core053_double_iff.1 hf

end Libpetri.Spec
