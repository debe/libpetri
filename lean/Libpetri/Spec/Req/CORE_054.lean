import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryContext
import Libpetri.Spec.Req.CORE_050

set_option linter.missingDocs true

/-!
# CORE-054: Produce action (`spec/01-core-model.md`)

CORE-054 is a pure-function requirement (kind F) over a value projection `value : T → V` and a
produce action family `produce : N → V → ActionRel N T`: `produce p v` is the built-in action
that produces the fixed value `v` to the place `p` (`ActionRel`, `Spec/GlossaryAction.lean`).
`T` is the type of tokens, each with its creation timestamp, and `V` the type of their values.
The block states the value, not the token: the token's creation timestamp is out of scope here
(CORE-035 AC2 and CORE-011's executor line state it).

The four lines. On a transition whose output specification names `p`: the action ends (line 1,
when some token carries `v`), and every way it ends is a completion with exactly one output
token, which carries `v` and goes to `p`, and no token in any other place (line 2). On a
transition whose output specification does not name `p`: the action ends (line 3), and every way
it ends is a failure (line 4). Lines 3 and 4 are CORE-063's error at the produce action: the
action passes the output call's error on and does not swallow it.

The witness is `refProduce value`: the action that makes the single output call
`output(p, v)` on the reference context `refCtx` (`Spec/GlossaryContext.lean`) and completes
with any tokens whose values are the buffer, or fails when the call reports an error. The link to
the firing is `core054_fires` and `core054_emits`: with CORE-050 in the joint model, a firing of a
transition whose output specification is `Place p` ends with the completion of the produce action
and deposits exactly one token of value `v` in `p`. One wrong action per line is killed: one that
never ends on a declared place (line 1), one that writes `v` to every output place (line 2, which
the literal reading of AC1 lets through), one that never ends on an undeclared place (line 3) and
one that completes with no token on an undeclared place on some runs (line 4). One that writes two
tokens, one that writes the consumed input, one that fails on a declared place and one that
swallows the error on an undeclared place are forbidden.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## The reference produce action -/

section Ref

variable {N T V : Type} [DecidableEq N]

/-- **Produce through a context**: the action makes the single output call `output(p, v)` on
the context `C`, from the empty buffer. When the call succeeds, the action completes with any
tokens whose places and values, read through `value`, are the buffer after the call (the context
stamps the tokens); when the call reports an error, the action fails. -/
def core054_ctxProduce (C : Ctx N T V) (value : T → V) (p : N) (v : V) : ActionRel N T :=
  fun t _ r =>
    match C.output t [] p [v] with
    | some b => ∃ e, r = .ok e ∧ e.map (fun x => (x.1, value x.2)) = b
    | none => ∃ m, r = .error m

/-- **The reference produce action** ([CORE-054]): produce through the reference context
`refCtx value`. -/
def refProduce (value : T → V) (p : N) (v : V) : ActionRel N T :=
  core054_ctxProduce (refCtx value) value p v

end Ref

/- The reference produce action is the witness model of CORE-054. -/
#spec_witness refProduce

/-! ## CORE-054: Produce Action -/

requirement CORE_054
  id "CORE-054"
  title "Produce Action"
  kind F
  scope "the built-in produce action of Java, TypeScript and Rust (the Python binding exposes no produce built-in)"
  source verbatim "spec/01-core-model.md"
  quote "*When* the built-in produce action of a place and a value runs on a transition whose output spec names that place, the action *shall* complete with exactly one output token, which carries that value and goes to that place, and with no output token in any other place."
        "*If* the built-in produce action of a place and a value runs on a transition whose output spec does not name that place, *then* the action *shall* fail."
  reading "For every value projection value and every produce action family produce (produce p v is the built-in action that produces the value v to the place p), every place p, value v, transition t and delivery δ:"
          "if the output specification of t names p and some token carries v, produce p v ends on t and δ in some way;"
          "if the output specification of t names p, every way produce p v ends on t and δ is a completion with the emission [(p, x)] for a token x whose value is v: exactly one output token, in p, and no token in any other place;"
          "if the output specification of t does not name p, produce p v ends on t and δ in some way;"
          "if the output specification of t does not name p, every way produce p v ends on t and δ is a failure."
  assumes "The model is the pair (value, produce). value : T → V reads a token's value; T is the queue model's token identities, each carrying its value and its creation timestamp. produce p v is an action (ActionRel, Spec/GlossaryAction.lean): a relation from a transition and the delivery to how the action ends, completing with an emission (places and tokens, in emission order) or failing with a message. The value is fixed: on every transition whose output spec names p, whatever the delivery, every completion of produce p v carries v (line 2), so every such firing produces the same value. The witness is refProduce value, the single output call output(p, v) on the reference context refCtx (core054_ctxProduce), which mirrors the three runtimes (rust/libpetri-core/src/action.rs:165-168, java/src/main/java/org/libpetri/core/TransitionAction.java:179-184, typescript/src/core/transition-action.ts:89-93: one ctx.output call, then completion)."
          "ActionRel records the ways an action ends, not whether every run ends: an action that ends on some runs and not on others is the relation of its endings, so a run that does not end is outside this block, and lines 1 and 3 rule out only an action that has no way to end at all. The three runtimes end after the one output call (Rust run_sync returns, Java returns a completed future, the TypeScript async function returns or throws)."
          "The block states the value, not the token: line 2 fixes the place and the value of the one token, and the token's creation timestamp is out of scope for this block. That an output token carries the epoch clock reading at its output call is CORE-035 AC2 and CORE-011, whose executor line is the W11 block; a produce action that builds its token once and hands that same token to every firing (the Java metadata overload ctx.output(Place, Token), java/src/main/java/org/libpetri/core/TransitionContext.java:295) meets this block and is for that line to reject. The runtimes stamp at the output call (rust/libpetri-core/src/context.rs:401-416, created_at from the epoch clock). The premise of line 1 that some token carries v holds of every runtime's token type, which carries any value of its type; it is there because the block is stated over an abstract token type."
          "'A transition whose output spec names that place' is OutputArc t p (glossary: Output arc; CORE-035, IO-017). On a place the output specification does not name, the output call reports an error and leaves no entry behind (CORE-062 AC5, CORE-063 AC3), and lines 3 and 4 say the produce action passes that error on: it fails, and it never completes, so it cannot complete with no token (refProduce_undeclared). Every runtime does so: Rust returns the error with ?, Java throws IllegalArgumentException from the output call and the TypeScript output call throws inside the async action. A transition with no output specification names no place, so the produce action of any place fails on it. Whether the one-token emission is a deposit the output specification offers is the firing's question (IO-015, CORE-050 line 3): on Place p it is (core054_fires), on And(Place p, Place q) it is not and validation fails the firing (EXEC-021)."
          "Line 1 says that the action ends on a declared place, so an action that never ends there violates it (CORE_054_mutant_noComplete_killed: lines 2 to 4 hold of it). Line 2 says what every way of ending on a declared place is, so an action that fails there violates it (CORE_054_forbids_fails), and so do one that writes two tokens (CORE_054_forbids_twoTokens) and one that writes the token it consumed instead of the value (CORE_054_forbids_echo). 'Exactly one output token in that place and none in any other' is stronger than AC1's 'the place receives a token with the value': an action that writes the value to every output place meets the AC1 reading and violates line 2 (CORE_054_mutant_ac1_killed). Line 3 says that the action ends on an undeclared place (CORE_054_mutant_noEndUndeclared_killed: an action that never ends there meets lines 1, 2 and 4). Line 4 says that every way it ends there is a failure (CORE_054_mutant_swallowSometimes_killed: an action that fails on some runs and completes with no token on others meets lines 1 to 3), and an action that always swallows the error and completes with no token violates it (CORE_054_forbids_swallow)."
          "The produce action writes through the context: every emission it completes with is a buffer built by successful output calls (refProduce_throughCtx), so CORE-062's and CORE-063's context lines and ctx_deposits_outputs apply to it."
          "AC1 (the specified place receives a token with the fixed value) is lines 1 and 2 at the action, and at the firing through CORE-050: on a transition whose output specification is Place p, an enabled firing ends with the completion of produce p v (core054_fires), and every firing that ends with it deposits exactly one token of value v in p and nothing elsewhere (core054_emits). Lines 3 and 4 have no acceptance criterion of CORE-054; they are CORE-062 AC5 and CORE-063 AC3 at the produce action."
          "The test derivation (produce action with value \"hello\" to place P; P receives \"hello\") is CORE_054_nonvacuous: on a transition consuming one token from place 0 and producing to Place 1, the reference action firing under refProduce for the value \"hello\" deposits one token carrying \"hello\" in place 1, and on place 2, which the transition does not name, the reference action fails."
  signoff "pending"
  statement : ∀ {N T V : Type} [DecidableEq N], (T → V) → (N → V → ActionRel N T) → Prop :=
    fun value produce =>
      (∀ p v t δ, OutputArc t p → (∃ x, value x = v) → ∃ r, produce p v t δ r) ∧
      (∀ p v t δ r, OutputArc t p → produce p v t δ r → ∃ x, r = .ok [(p, x)] ∧ value x = v) ∧
      (∀ p v t δ, ¬ OutputArc t p → ∃ r, produce p v t δ r) ∧
      (∀ p v t δ r, ¬ OutputArc t p → produce p v t δ r → ∃ m, r = .error m)

/- The pinned readable form of CORE-054: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CORE_054 : {N T V : Type} → [DecidableEq N] → (T → V) → (N → V → ActionRel N T) → Prop :=
fun {N T V} [DecidableEq N] value produce =>
  (∀ (p : N) (v : V) (t : Reference.Trans N) (δ : Delivered N T),
      OutputArc t p → (∃ x, value x = v) → ∃ r, produce p v t δ r) ∧
    (∀ (p : N) (v : V) (t : Reference.Trans N) (δ : Delivered N T) (r : Except String (List (N × T))),
        OutputArc t p → produce p v t δ r → ∃ x, r = Except.ok [(p, x)] ∧ value x = v) ∧
      (∀ (p : N) (v : V) (t : Reference.Trans N) (δ : Delivered N T), ¬OutputArc t p → ∃ r, produce p v t δ r) ∧
        ∀ (p : N) (v : V) (t : Reference.Trans N) (δ : Delivered N T) (r : Except String (List (N × T))),
          ¬OutputArc t p → produce p v t δ r → ∃ m, r = Except.error m
-/
#guard_msgs in #print CORE_054

/-! ### The four lines, named (for the mutants) -/

section Lines

variable {N T V : Type} [DecidableEq N]

/-- Line 1 of CORE-054: on a transition whose output specification names `p`, the produce
action ends, when some token carries the value. -/
def core054_line1 (value : T → V) (produce : N → V → ActionRel N T) : Prop :=
  ∀ p v t δ, OutputArc t p → (∃ x, value x = v) → ∃ r, produce p v t δ r

/-- Line 2 of CORE-054: on a transition whose output specification names `p`, every way the
produce action ends is a completion with exactly one token, in `p`, carrying `v`. -/
def core054_line2 (value : T → V) (produce : N → V → ActionRel N T) : Prop :=
  ∀ p v t δ r, OutputArc t p → produce p v t δ r → ∃ x, r = .ok [(p, x)] ∧ value x = v

/-- Line 3 of CORE-054: on a transition whose output specification does not name `p`, the
produce action ends. -/
def core054_line3 (produce : N → V → ActionRel N T) : Prop :=
  ∀ p v t δ, ¬ OutputArc t p → ∃ r, produce p v t δ r

/-- Line 4 of CORE-054: on a transition whose output specification does not name `p`, every way
the produce action ends is a failure. -/
def core054_line4 (produce : N → V → ActionRel N T) : Prop :=
  ∀ p v t δ r, ¬ OutputArc t p → produce p v t δ r → ∃ m, r = .error m

/-- CORE-054 is its four lines. -/
theorem core054_iff (value : T → V) (produce : N → V → ActionRel N T) :
    CORE_054 value produce ↔ core054_line1 value produce ∧ core054_line2 value produce ∧
      core054_line3 produce ∧ core054_line4 produce :=
  Iff.rfl

end Lines

/-! ### The reference -/

section RefFacts

variable {N T V : Type} [DecidableEq N]

/-- On a place the output specification names, the reference context's output call of one
value from the empty buffer gives the one entry `(p, v)`. -/
theorem core054_refCtx_output_single {value : T → V} {t : Trans N} {p : N} (hp : OutputArc t p)
    (v : V) : (refCtx value).output t [] p [v] = some [(p, v)] := by
  simp [refCtx, hp]

/-- On a place the output specification names, the reference produce action ends exactly by
completing with one token in `p` whose value is `v`. -/
theorem refProduce_declared {value : T → V} {t : Trans N} {p : N} (hp : OutputArc t p) (v : V)
    (δ : Delivered N T) (r : Except String (List (N × T))) :
    refProduce value p v t δ r ↔ ∃ x, r = .ok [(p, x)] ∧ value x = v := by
  unfold refProduce core054_ctxProduce
  rw [core054_refCtx_output_single hp v]
  constructor
  · rintro ⟨e, rfl, he⟩
    match e, he with
    | [(q, x)], he =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq, and_true] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨x, rfl, rfl⟩
  · rintro ⟨x, rfl, rfl⟩
    exact ⟨[(p, x)], rfl, rfl⟩

/-- **CORE-063 at the produce action**: on a place the output specification does not name, the
output call reports an error, so the reference produce action fails, and only fails. -/
theorem refProduce_undeclared {value : T → V} {t : Trans N} {p : N} (hp : ¬ OutputArc t p)
    (v : V) (δ : Delivered N T) (r : Except String (List (N × T))) :
    refProduce value p v t δ r ↔ ∃ m, r = .error m := by
  unfold refProduce core054_ctxProduce
  have h : (refCtx value).output t [] p [v] = none := by simp [refCtx, hp]
  rw [h]

omit [DecidableEq N] in
/-- **The produce action writes through the context**: every emission a produce action through
the context `C` completes with is a buffer built by one successful output call of `C`. -/
theorem core054_ctxProduce_throughCtx (C : Ctx N T V) (value : T → V) (p : N) (v : V) :
    ThroughCtx C value (core054_ctxProduce C value p v) := by
  intro t δ e h
  unfold core054_ctxProduce at h
  split at h
  · rename_i b hb
    obtain ⟨e', he', hm⟩ := h
    cases he'
    rw [hm]
    exact Built.call [] b p [v] Built.nil hb
  · obtain ⟨m, hm⟩ := h
    cases hm

/-- The reference produce action writes through the reference context. -/
theorem refProduce_throughCtx (value : T → V) (p : N) (v : V) :
    ThroughCtx (refCtx value) value (refProduce value p v) :=
  core054_ctxProduce_throughCtx _ value p v

end RefFacts

/-- ✓ The reference produce action satisfies CORE-054, for every value projection: on a place
the output specification names, it completes with one token carrying the value in that place,
and only so; on a place it does not name, it fails, and only fails. -/
@[evidence holds CORE_054]
theorem CORE_054_reference {N T V : Type} [DecidableEq N] (value : T → V) :
    CORE_054 value (refProduce (N := N) value) := by
  refine ⟨fun p v t δ hp ⟨x, hx⟩ => ⟨.ok [(p, x)], (refProduce_declared hp v δ _).2 ⟨x, rfl, hx⟩⟩,
    fun p v t δ r hp h => (refProduce_declared hp v δ r).1 h,
    fun p v t δ hp => ⟨.error "undeclared output place", (refProduce_undeclared hp v δ _).2 ⟨_, rfl⟩⟩,
    fun p v t δ r hp h => (refProduce_undeclared hp v δ r).1 h⟩

/-! ### Consequences at the firing (with CORE-050) -/

section Joint

variable {N T V : Type} [DecidableEq N]

omit [DecidableEq N] in
/-- The output specification `Place p` has the one branch `[p]`. -/
theorem core054_outputBranch_place {t : Trans N} {p : N} (ho : t.out = some (.place p)) :
    OutputBranch t [p] := by
  unfold OutputBranch
  rw [ho]
  exact List.mem_singleton.2 rfl

omit [DecidableEq N] in
/-- `Place p` names `p`. -/
theorem core054_outputArc_place {t : Trans N} {p : N} (ho : t.out = some (.place p)) : OutputArc t p :=
  ⟨.place p, ho, List.mem_singleton.2 rfl⟩

/-- **AC1 at the firing, deposit**: with CORE-050, every firing that ends with the completion of
the produce action of `p` and `v`, on a transition whose output specification names `p`, emits
exactly one token, in `p`, carrying `v`, and nothing elsewhere. -/
theorem core054_emits {Q : QFireRel N T} {AF : ActFireRel N T} {value : T → V}
    {produce : N → V → ActionRel N T} (h50 : CORE_050 Q AF) (h : CORE_054 value produce)
    {p : N} {v : V} {t : Trans N} (hp : OutputArc t p) {M M' : QueueMarking N T}
    {δ : Delivered N T} {e : List (N × T)} (hf : AF (produce p v) t M δ e M') :
    ∃ x, e = [(p, x)] ∧ value x = v := by
  obtain ⟨x, hx, hv⟩ := h.2.1 p v t δ _ hp (h50.2.1 _ t δ e M M' hf)
  exact ⟨x, Except.ok.inj hx, hv⟩

/-- **Lines 3 and 4 at the firing**: with CORE-050, no firing of a transition whose output
specification does not name `p` ends with the completion of the produce action of `p`. -/
theorem core054_undeclared_noFiring {Q : QFireRel N T} {AF : ActFireRel N T} {value : T → V}
    {produce : N → V → ActionRel N T} (h50 : CORE_050 Q AF) (h : CORE_054 value produce)
    {p : N} {v : V} {t : Trans N} (hp : ¬ OutputArc t p) {M M' : QueueMarking N T}
    {δ : Delivered N T} {e : List (N × T)} : ¬ AF (produce p v) t M δ e M' := by
  intro hf
  obtain ⟨m, hm⟩ := h.2.2.2 p v t δ _ hp (h50.2.1 _ t δ e M M' hf)
  cases hm

/-- **AC1 at the firing, occurrence**: in the joint model (CORE-050, `Q` covering every reference
firing and delivering the reference delivery), an enabled transition whose output specification
is `Place p` has a firing that ends with the completion of the produce action of `p` and `v`,
depositing one token of value `v` in `p`, when some token carries `v`. -/
theorem core054_fires {Q : QFireRel N T} {AF : ActFireRel N T} {value : T → V}
    {produce : N → V → ActionRel N T} (h50 : CORE_050 Q AF) (h : CORE_054 value produce)
    (hc : QCovers Q RefFire) (hδ : ∀ t M δ e M', Q t M δ e M' → δ = qDelivered M t)
    {p : N} {v : V} {t : Trans N} (ho : t.out = some (.place p)) {M : QueueMarking N T}
    (hen : Enabled t (Counts M)) (hv : ∃ x, value x = v) :
    ∃ x M', value x = v ∧ AF (produce p v) t M (qDelivered M t) [(p, x)] M' := by
  obtain ⟨r, hr⟩ := h.1 p v t (qDelivered M t) (core054_outputArc_place ho) hv
  obtain ⟨x, rfl, hx⟩ := h.2.1 p v t _ r (core054_outputArc_place ho) hr
  obtain ⟨M', hf⟩ := core050_fires (e := [(p, x)]) h50 hc hδ hen (core054_outputBranch_place ho) hr
  exact ⟨x, M', hx, hf⟩

/-- On the reference, a produce firing on `Place p` is a reference queue firing (`RefQFire`)
that ends with the completion of the reference produce action. -/
theorem core054_ref_fires {value : T → V} {p : N} {v : V} {t : Trans N}
    (ho : t.out = some (.place p)) {M : QueueMarking N T} (hen : Enabled t (Counts M)) {x : T}
    (hx : value x = v) :
    refActionFire (refProduce value p v) t M (qDelivered M t) [(p, x)] (qFire M t [(p, x)]) := by
  have hb := core054_outputBranch_place ho
  obtain ⟨i, hi⟩ := (outputBranch_iff_action t (Consumes t (Counts M)) _).1 hb
  exact ⟨⟨hen, ⟨.action i, hi⟩, rfl, rfl⟩, hb,
    (refProduce_declared (core054_outputArc_place ho) v _ _).2 ⟨x, rfl, hx⟩⟩

end Joint

/-! ### Examples -/

/-- Tokens of the examples: a value and a creation timestamp. -/
abbrev Core054Tok := String × Nat

/-- `w`: one input arc on place 0, output `And(Place 1, Place 2)`. -/
def core054_w : Trans Nat :=
  { core := { name := "w", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.and (.place 1) (.place 2)) }

/-- Place 0 holds the token `("in", 1)`; every other place is empty. -/
def core054_M : QueueMarking Nat Core054Tok := fun p => if p = 0 then [("in", 1)] else []

/-- `u` (CORE-050's `core050_u`: one input arc on place 0, output `Place 1`) does not name
place 2. -/
theorem core054_u_not2 : ¬ OutputArc core050_u 2 := by decide

/-- ✓ CORE-054 is not vacuous. The test derivation: on `u` from a place 0 holding one token, the
reference action firing under the produce action of place 1 and the value "hello" deposits one
token carrying "hello" in place 1 (stamped 3 here) and empties place 0. On place 2, which `u`
does not name, the reference produce action fails (lines 3 and 4). -/
@[evidence nonvacuous CORE_054]
theorem CORE_054_nonvacuous :
    refActionFire (refProduce Prod.fst 1 "hello") core050_u core054_M
      (qDelivered core054_M core050_u) [(1, ("hello", 3))]
      (qFire core054_M core050_u [(1, ("hello", 3))]) ∧
    qFire core054_M core050_u [(1, ("hello", 3))] 1 = [("hello", 3)] ∧
    qFire core054_M core050_u [(1, ("hello", 3))] 0 = [] ∧
    refProduce (N := Nat) (T := Core054Tok) Prod.fst 2 "hello" core050_u
      (qDelivered core054_M core050_u) (.error "undeclared output place") := by
  refine ⟨core054_ref_fires rfl (by decide) rfl, by decide, by decide, ?_⟩
  exact (refProduce_undeclared core054_u_not2 _ _ _).2 ⟨_, rfl⟩

/-! ### Actions that differ from the reference on one side -/

section Patch

variable {N T V : Type} [DecidableEq N]

/-- The action that behaves as `D` on a declared place and as the reference on an undeclared one. -/
def core054_onDeclared (value : T → V) (D : N → V → ActionRel N T) : N → V → ActionRel N T :=
  fun p v t δ r => (OutputArc t p ∧ D p v t δ r) ∨ (¬ OutputArc t p ∧ refProduce value p v t δ r)

/-- The action that behaves as the reference on a declared place and as `X` on an undeclared one. -/
def core054_onUndeclared (value : T → V) (X : N → V → ActionRel N T) : N → V → ActionRel N T :=
  fun p v t δ r => (OutputArc t p ∧ refProduce value p v t δ r) ∨ (¬ OutputArc t p ∧ X p v t δ r)

/-- An action that is the reference on an undeclared place meets line 3. -/
theorem core054_onDeclared_line3 (value : T → V) (D : N → V → ActionRel N T) :
    core054_line3 (core054_onDeclared value D) := fun _ v _ δ hp =>
  ⟨.error "undeclared output place", Or.inr ⟨hp, (refProduce_undeclared hp v δ _).2 ⟨_, rfl⟩⟩⟩

/-- An action that is the reference on an undeclared place meets line 4. -/
theorem core054_onDeclared_line4 (value : T → V) (D : N → V → ActionRel N T) :
    core054_line4 (core054_onDeclared value D) := by
  intro p v t δ r hp h
  rcases h with ⟨hp', -⟩ | ⟨-, h⟩
  · exact absurd hp' hp
  · exact (refProduce_undeclared hp v δ r).1 h

/-- An action that is the reference on a declared place meets line 1. -/
theorem core054_onUndeclared_line1 (value : T → V) (X : N → V → ActionRel N T) :
    core054_line1 value (core054_onUndeclared value X) := fun p v _ δ hp ⟨x, hx⟩ =>
  ⟨.ok [(p, x)], Or.inl ⟨hp, (refProduce_declared hp v δ _).2 ⟨x, rfl, hx⟩⟩⟩

/-- An action that is the reference on a declared place meets line 2. -/
theorem core054_onUndeclared_line2 (value : T → V) (X : N → V → ActionRel N T) :
    core054_line2 value (core054_onUndeclared value X) := by
  intro p v t δ r hp h
  rcases h with ⟨-, h⟩ | ⟨hp', -⟩
  · exact (refProduce_declared hp v δ r).1 h
  · exact absurd hp hp'

end Patch

/-! ### Mutant: without line 1 (an action that never ends on a declared place) -/

/-- Mutant reading: lines 2 to 4, without line 1. It holds of an action that never ends on a
declared place. -/
def CORE_054_mutant_noComplete {N T V : Type} [DecidableEq N] (value : T → V)
    (produce : N → V → ActionRel N T) : Prop :=
  core054_line2 value produce ∧ core054_line3 produce ∧ core054_line4 produce

/-- A produce action that never ends on a declared place and is the reference elsewhere. -/
def core054_never {N T V : Type} [DecidableEq N] (value : T → V) : N → V → ActionRel N T :=
  core054_onDeclared value fun _ _ _ _ _ => False

/-- ✗ The action that never ends on a declared place kills the mutant: it meets line 2 vacuously
and lines 3 and 4 as the reference, but on `u` the produce action of place 1 and the value "a"
does not end, although a token carries "a" (line 1). -/
@[evidence mutant CORE_054]
theorem CORE_054_mutant_noComplete_killed :
    CORE_054_mutant_noComplete (N := Nat) (Prod.fst : Core054Tok → String)
        (core054_never Prod.fst) ∧
      ¬ CORE_054 (N := Nat) (Prod.fst : Core054Tok → String) (core054_never Prod.fst) := by
  refine ⟨⟨?_, core054_onDeclared_line3 _ _, core054_onDeclared_line4 _ _⟩, fun h => ?_⟩
  · intro p v t δ r hp h
    rcases h with ⟨-, h⟩ | ⟨hp', -⟩
    · exact h.elim
    · exact absurd hp hp'
  · obtain ⟨r, hr⟩ := h.1 1 "a" core050_u ⟨fun _ => [], fun _ => []⟩
      (core054_outputArc_place rfl) ⟨("a", 0), rfl⟩
    rcases hr with ⟨-, h⟩ | ⟨hp', -⟩
    · exact h
    · exact hp' (core054_outputArc_place rfl)

/-! ### Mutant: AC1 read literally (an action that writes the value everywhere) -/

section MutantAC1

variable {N T V : Type} [DecidableEq N]

/-- Mutant reading of line 2, AC1 read literally ("the specified place receives a token with
the fixed value"): every way the action ends on a declared place is a completion in which some
token carrying `v` goes to `p`. Lines 1, 3 and 4 are as in CORE-054. -/
def CORE_054_mutant_ac1 (value : T → V) (produce : N → V → ActionRel N T) : Prop :=
  core054_line1 value produce ∧
    (∀ p v t δ r, OutputArc t p → produce p v t δ r →
      ∃ e, r = .ok e ∧ ∃ x, (p, x) ∈ e ∧ value x = v) ∧
    core054_line3 produce ∧ core054_line4 produce

/-- The places an output specification names, or none without one. -/
def core054_allOut (t : Trans N) : List N := (t.out.map outPlaces).getD []

/-- A produce action that, on a declared place, writes one token carrying `v` to every output
place of the transition (a transform with a constant result, CORE-053), not only to `p`; on an
undeclared place it is the reference. -/
def core054_everywhere (value : T → V) : N → V → ActionRel N T :=
  core054_onDeclared value fun _ v t _ r =>
    ∃ x, value x = v ∧ r = .ok ((core054_allOut t).map fun q => (q, x))

/-- The everywhere action meets the mutant reading. -/
theorem core054_everywhere_ac1 (value : T → V) :
    CORE_054_mutant_ac1 value (core054_everywhere (N := N) value) := by
  refine ⟨fun p v t δ hp ⟨x, hx⟩ => ⟨_, Or.inl ⟨hp, x, hx, rfl⟩⟩, fun p v t δ r hp h => ?_,
    core054_onDeclared_line3 _ _, core054_onDeclared_line4 _ _⟩
  rcases h with ⟨-, x, hx, rfl⟩ | ⟨hp', -⟩
  · obtain ⟨o, ho, hpo⟩ := hp
    refine ⟨_, rfl, x, ?_, hx⟩
    simp only [core054_allOut, ho, Option.map_some, Option.getD_some]
    exact List.mem_map.2 ⟨p, hpo, rfl⟩
  · exact absurd hp hp'

end MutantAC1

/-- ✗ The everywhere action kills the mutant: it meets the AC1 reading, but on `w`, whose output
specification is `And(Place 1, Place 2)`, the produce action of place 1 writes a token to
place 2 as well (line 2). -/
@[evidence mutant CORE_054]
theorem CORE_054_mutant_ac1_killed :
    CORE_054_mutant_ac1 (N := Nat) (Prod.fst : Core054Tok → String)
        (core054_everywhere Prod.fst) ∧
      ¬ CORE_054 (N := Nat) (Prod.fst : Core054Tok → String) (core054_everywhere Prod.fst) := by
  refine ⟨core054_everywhere_ac1 _, fun h => ?_⟩
  have hp : OutputArc core054_w 1 := ⟨_, rfl, by decide⟩
  obtain ⟨x, hx, -⟩ := h.2.1 1 "a" core054_w ⟨fun _ => [], fun _ => []⟩ _ hp
    (Or.inl ⟨hp, ("a", 0), rfl, rfl⟩)
  have := Except.ok.inj hx
  simp [core054_allOut, core054_w, outPlaces] at this

/-! ### Mutant: without line 3 (an action that never ends on an undeclared place) -/

/-- Mutant reading: lines 1, 2 and 4, without line 3. It holds of an action that never ends on
an undeclared place. -/
def CORE_054_mutant_noEndUndeclared {N T V : Type} [DecidableEq N] (value : T → V)
    (produce : N → V → ActionRel N T) : Prop :=
  core054_line1 value produce ∧ core054_line2 value produce ∧ core054_line4 produce

/-- A produce action that is the reference on a declared place and never ends on an undeclared
one. -/
def core054_hangUndeclared {N T V : Type} [DecidableEq N] (value : T → V) :
    N → V → ActionRel N T :=
  core054_onUndeclared value fun _ _ _ _ _ => False

/-- ✗ The action that never ends on an undeclared place kills the mutant: it meets lines 1 and 2
as the reference and line 4 vacuously, but on `u` the produce action of place 2, which `u` does
not name, does not end (line 3). -/
@[evidence mutant CORE_054]
theorem CORE_054_mutant_noEndUndeclared_killed :
    CORE_054_mutant_noEndUndeclared (N := Nat) (Prod.fst : Core054Tok → String)
        (core054_hangUndeclared Prod.fst) ∧
      ¬ CORE_054 (N := Nat) (Prod.fst : Core054Tok → String) (core054_hangUndeclared Prod.fst) := by
  refine ⟨⟨core054_onUndeclared_line1 _ _, core054_onUndeclared_line2 _ _, ?_⟩, fun h => ?_⟩
  · intro p v t δ r hp h
    rcases h with ⟨hp', -⟩ | ⟨-, h⟩
    · exact absurd hp' hp
    · exact h.elim
  · obtain ⟨r, hr⟩ := h.2.2.1 2 "a" core050_u ⟨fun _ => [], fun _ => []⟩ core054_u_not2
    rcases hr with ⟨hp', -⟩ | ⟨-, h⟩
    · exact core054_u_not2 hp'
    · exact h

/-! ### Mutant: without line 4 (an action that sometimes swallows the error) -/

/-- Mutant reading: lines 1 to 3, without line 4. It holds of an action that, on an undeclared
place, fails on some runs and completes with no token on others. -/
def CORE_054_mutant_swallowSometimes {N T V : Type} [DecidableEq N] (value : T → V)
    (produce : N → V → ActionRel N T) : Prop :=
  core054_line1 value produce ∧ core054_line2 value produce ∧ core054_line3 produce

/-- A produce action that is the reference on a declared place and, on an undeclared one, either
fails or drops the output call's error and completes with no token. -/
def core054_swallowSometimes {N T V : Type} [DecidableEq N] (value : T → V) :
    N → V → ActionRel N T :=
  core054_onUndeclared value fun _ _ _ _ r => r = .ok [] ∨ ∃ m, r = .error m

/-- ✗ The sometimes-swallowing action kills the mutant: it meets lines 1 and 2 as the reference
and line 3 by failing, but on `u` the produce action of place 2, which `u` does not name, may
complete with no token (line 4). -/
@[evidence mutant CORE_054]
theorem CORE_054_mutant_swallowSometimes_killed :
    CORE_054_mutant_swallowSometimes (N := Nat) (Prod.fst : Core054Tok → String)
        (core054_swallowSometimes Prod.fst) ∧
      ¬ CORE_054 (N := Nat) (Prod.fst : Core054Tok → String)
        (core054_swallowSometimes Prod.fst) := by
  refine ⟨⟨core054_onUndeclared_line1 _ _, core054_onUndeclared_line2 _ _,
    fun p v t δ hp => ⟨.error "undeclared output place", Or.inr ⟨hp, Or.inr ⟨_, rfl⟩⟩⟩⟩,
    fun h => ?_⟩
  obtain ⟨m, hm⟩ := h.2.2.2 2 "a" core050_u ⟨fun _ => [], fun _ => []⟩ (.ok []) core054_u_not2
    (Or.inr ⟨core054_u_not2, Or.inl rfl⟩)
  cases hm

/-! ### Wrong actions forbidden -/

/-- A produce action that writes two tokens carrying `v` to `p`. -/
def core054_twoTokens {N T V : Type} (value : T → V) : N → V → ActionRel N T := fun p v _ _ r =>
  ∃ x, value x = v ∧ r = .ok [(p, x), (p, x)]

/-- ✗ Writing two tokens violates line 2: on `u` the produce action of place 1 completes with
two tokens. -/
@[evidence forbids CORE_054]
theorem CORE_054_forbids_twoTokens :
    ¬ CORE_054 (N := Nat) (Prod.fst : Core054Tok → String) (core054_twoTokens Prod.fst) := by
  intro h
  obtain ⟨x, hx, -⟩ := h.2.1 1 "a" core050_u ⟨fun _ => [], fun _ => []⟩ _
    (core054_outputArc_place rfl) ⟨("a", 0), rfl, rfl⟩
  have := Except.ok.inj hx
  simp at this

/-- A produce action that writes a token the firing consumed, instead of a token carrying `v`. -/
def core054_echo {N T V : Type} : N → V → ActionRel N T := fun p _ _ δ r =>
  ∃ q x, x ∈ δ.inputs q ∧ r = .ok [(p, x)]

/-- ✗ Writing the consumed input violates line 2: on `u` with the token `("in", 1)` delivered from
place 0, the produce action of place 1 and the value "hello" writes a token carrying "in". -/
@[evidence forbids CORE_054]
theorem CORE_054_forbids_echo :
    ¬ CORE_054 (N := Nat) (Prod.fst : Core054Tok → String) core054_echo := by
  intro h
  obtain ⟨x, hx, hv⟩ := h.2.1 1 "hello" core050_u (qDelivered core054_M core050_u) _
    (core054_outputArc_place rfl) ⟨0, ("in", 1), by decide, rfl⟩
  have := Except.ok.inj hx
  simp only [List.cons.injEq, Prod.mk.injEq, true_and, and_true] at this
  subst this
  exact absurd hv (by decide)

/-- A produce action that fails on every transition, a declared place included. -/
def core054_fails {N T V : Type} : N → V → ActionRel N T := fun _ _ _ _ r =>
  ∃ m, r = .error m

/-- ✗ Failing on a declared place violates line 2: on `u` the produce action of place 1 fails. -/
@[evidence forbids CORE_054]
theorem CORE_054_forbids_fails :
    ¬ CORE_054 (N := Nat) (Prod.fst : Core054Tok → String) core054_fails := by
  intro h
  obtain ⟨x, hx, -⟩ := h.2.1 1 "a" core050_u ⟨fun _ => [], fun _ => []⟩ _
    (core054_outputArc_place rfl) ⟨"fail", rfl⟩
  cases hx

/-- A produce action that is the reference on a declared place and, on an undeclared one, drops
the output call's error and completes with no token: the Rust slip
`let _ = ctx.output_raw(..); Ok(())` or the TypeScript slip `try { ctx.output(..) } catch {}`. -/
def core054_swallow {N T V : Type} [DecidableEq N] (value : T → V) : N → V → ActionRel N T :=
  core054_onUndeclared value fun _ _ _ _ r => r = .ok []

/-- ✗ Swallowing the error violates line 4: on `u` the produce action of place 2, which `u` does
not name, completes with no token. At the firing, on a sink transition it would consume the
input and deposit nothing, where every runtime fails the firing. -/
@[evidence forbids CORE_054]
theorem CORE_054_forbids_swallow :
    ¬ CORE_054 (N := Nat) (Prod.fst : Core054Tok → String) (core054_swallow Prod.fst) := by
  intro h
  obtain ⟨m, hm⟩ := h.2.2.2 2 "a" core050_u ⟨fun _ => [], fun _ => []⟩ (.ok []) core054_u_not2
    (Or.inr ⟨core054_u_not2, rfl⟩)
  cases hm

end Libpetri.Spec
