import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryContext

set_option linter.missingDocs true

/-!
# CORE-052: Fork action (`spec/01-core-model.md`)

CORE-052 is a pure-function requirement (kind F) over the built-in fork action, read as an action
function `Fork : ActionFn N T` (`Spec/GlossaryAction.lean`): given a transition and what the
firing delivered, it completes with an emission (places and tokens) or fails. The value a token
carries is the projection `val : T → V`, a parameter of the statement as in CORE-003: every
runtime deposits a new token with a fresh `created_at` that carries the consumed value, so the
block compares values, not tokens.

The three lines: on a transition with exactly one input place whose firing consumed exactly one
token `x` from it, fork completes, and every place gets, by value, `[val x]` if the output spec
names it and nothing otherwise (line 1); on a transition without exactly one input place, zero
included, fork fails (line 2); on a batch of two or more consumed tokens `x :: y :: ys` from the
sole input place, fork either fails or completes as in line 1 with the oldest token `x` (line 3).
Which of the two a batch gets is not settled (ruling D50 (a)): Java, Rust and Python copy the
oldest token (`refFork`), TypeScript fails (`refForkStrict`); both satisfy the block and they
differ on a batch (`CORE_052_batch_undecided`).

Wrong forks are killed: one that writes only the first output place, one that writes two copies,
one that also writes back to its input place, one that emits another value, one that accepts two
input places, one that completes on a transition with no input place, one that copies every token
of a batch, and one that copies the newest token of a batch. A fork that emits a new token with
the same value is allowed, and so is Rust's way of counting input places (the places that
delivered). One consequence joins the block with CORE-050 and IO-015: on an output spec
`Xor(a, b)` with two different places, no firing ends with the fork action
(`core052_xor_never_fires`).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## Vocabulary -/

/-- `i` is the sole input place of `t`: the input places of `t`, as a set, are exactly `{i}`. -/
def core052_soleInput {N : Type} (t : Trans N) (i : N) : Prop := ∀ p, p ∈ inPlaces t ↔ p = i

/-! ## CORE-052: Fork Action -/

requirement CORE_052
  id "CORE-052"
  title "Fork Action"
  kind F
  scope "all implementations (the built-in fork action; Python rides on the Rust action)"
  source verbatim "spec/01-core-model.md"
  quote "A built-in fork action that copies a single input token value to all declared output places."
        "*When* the fork action runs for a transition with exactly one input place and the firing consumed exactly one token from that place, the action *shall* complete with one token carrying that token's value in every place the output spec names and with no token in any other place."
        "*If* the transition does not have exactly one input place, *then* the fork action *shall* fail."
        "*When* the firing consumed two or more tokens from the single input place, the fork action *shall* either fail or complete with one token carrying the oldest consumed token's value in every place the output spec names and with no token in any other place."
        "**Divergence:** when the firing consumed two or more tokens from the single input place, the fork action copies the oldest consumed token to every output place in Java, Rust and Python and fails in TypeScript."
        "**Note:** The fork action writes every place the output spec names, so on an output spec `Xor(a, b)` with two different places it writes both, and an executor with output validation enabled rejects its completion ([IO-015], [EXEC-021])."
  reading "For every value projection val and every fork action function Fork, for every transition t and every delivery δ:"
          "for every place i and token x, if i is the sole input place of t (the input places of t, as a set, are {i}) and δ delivers exactly [x] from i, then Fork t δ completes with an emission e such that, for every place p, the values of the tokens e sends to p are [val x] if t's output spec names p and [] otherwise;"
          "if t has no sole input place (it has none, or two or more) and every input place of t delivered at least one token in δ, then Fork t δ fails with some message;"
          "for every place i and tokens x, y, ys, if i is the sole input place of t and δ delivers x :: y :: ys from i (x the oldest), then Fork t δ either fails with some message or completes with an emission e such that, for every place p, the values of the tokens e sends to p are [val x] if t's output spec names p and [] otherwise."
  assumes "The fork action is read as an action function (ActionFn, Spec/GlossaryAction.lean): from the transition and the delivery δ (the consumed tokens per input place in consumption order, oldest first, and the read tokens per read place) to a completion with an emission (places and tokens, in emission order) or a failure. It reads nothing else, so a function, not a relation. Where the tokens it completes with go is CORE-050's line 2 (the firing deposits exactly them, AF := refActionFire with the action ActionFn.rel Fork)."
          "Values, not tokens: val x is the value a token carries (CORE-003's projection; none for a unit token when V is an Option). Every runtime deposits a new token with a fresh created_at carrying the consumed value (Rust epoch_now in the output path, Java and TypeScript ctx.output), so lines 1 and 3 compare (EmittedTo e p).map val with [val x]. A fork that emits the consumed token itself (refFork) and one that emits a new token with the same value (CORE_052_allows_freshStamp) both satisfy them; a fork that emits another value violates them (CORE_052_forbids_otherValue)."
          "'Exactly one input place' is a set condition (core052_soleInput): the input places are the places of t's input arcs, read and reset arcs excluded. Java and TypeScript count the declared input places (ctx.inputPlaces()); Rust counts input_place_names, the keys of the consumed-input map, which are the input places that delivered a token. The two counts agree on every delivery in which each input place delivered at least one token, and every firing is such a delivery (IO-002, IO-004 AC1: every input arc requires at least one token). Line 2 is stated for those deliveries only, so a fork that counts as Rust does satisfies the block (CORE_052_allows_rustCount). Lines 1 and 3 need no such premise: the sole input place delivered there. A transition with two input arcs on one place is rejected when it is built (CORE-030) and is covered by the set reading either way."
          "'Every place the output spec names' is OutputArc (glossary: Output arc; IO-017's set): every place of the spec, Xor alternatives, the Timeout child and ForwardInput targets included (Rust output_place_names over allowed_outputs, Java Transition.outputPlaces, TypeScript ctx.outputPlaces()). A transition without an output spec names no place, so fork completes with no token there. Lines 1 and 3 compare per place, not as a list: Rust iterates a HashSet of output places, so the emission order is not fixed and the block does not fix it."
          "Line 1 has three parts, each with a wrong fork that meets a plausible weaker reading: every output place gets a copy (the fork that writes only the first output place meets 'tokens only in output places, carrying the value', CORE_052_mutant_onlyOutputs_killed); exactly one copy (a fork that writes two copies meets the old AC2, 'produces the input value to all output places', CORE_052_mutant_ac2Literal_killed_double); and nothing elsewhere (a fork that also writes back to its input place meets the same reading, CORE_052_mutant_ac2Literal_killed_echo). AC2 is reworded to state the three parts."
          "Line 2 includes zero input places: AC1 says 'requires exactly one input place', and all three runtimes fail on any count other than one (rust/libpetri-core/src/action.rs Fork::run_sync, java TransitionAction.fork, typescript transition-action.ts fork), with the message 'Fork requires exactly 1 input place, found n'. AC3 said 'more than one input place' and is reworded to 'not exactly one' under ruling D20 (R-CB6). A fork that completes with no token on a transition without input places meets AC3's old wording and violates line 2 (CORE_052_mutant_ac3Literal_killed); a fork that accepts two input places and copies the first violates it too (CORE_052_forbids_acceptTwo). The message text is not stated."
          "Ruling D50 (a): line 1 is stated for a firing that consumed exactly one token from the sole input place, and the batch case (two or more, from an Exactly(n), All or AtLeast input) is left undecided between the runtimes' two behaviours: Java and Rust copy the oldest consumed token (Java ctx.input returns the first token of the batch, Rust's fork reads input_raw, which takes the first token), Python rides on Rust, and TypeScript fails (ctx.input throws on a count other than one). Both satisfy the block (CORE_052_reference, CORE_052_reference_strict) and differ on a batch (CORE_052_batch_undecided); the spec records which runtime does which in its Divergence note. Line 3 changes no runtime and picks neither: it only excludes what neither runtime does and what the headline 'copies a single input token value' excludes, a fork that copies every token of the batch and one that copies the newest (CORE_052_mutant_noBatch_killed_all, CORE_052_mutant_noBatch_killed_newest). AC4 states line 3."
          "The same option (exactly-one premise, batch undecided) is taken for input() in CORE-060. The runtimes' batch behaviour differs between the two in Rust and Python, where fork reads input_raw (the oldest token) and input() reports an error, so the two Divergence notes put Rust on different sides. A delivery of no token from the sole input place does not arise from a firing (IO-002, IO-004 AC1); both readings fail on it and the block says nothing of it."
          "Consequence with CORE-050 and IO-015 (core052_xor_never_fires), the Note: fork writes every place of the spec, so on Xor(a, b) with a ≠ b its emission fills no output branch and no reference action firing ends with the fork action; the executor's output validation rejects the completion (EXEC-021). Under the validation skip of CONC-026 the completion is not checked, which is CONC-026's. The block does not restate this; it follows from line 1 and refActionFire."
          "That every output place must accept the input value's type (Java's javadoc) is CORE-003's compatibility, owed by the net's author; a null value is propagated as a value like any other. That fork is a built-in with a constructor (fork() in each language, BuiltinAction in Python) is API shape. Whether it runs synchronously (Rust is_sync) is CONC-011's."
          "AC1 (requires exactly one input place) is line 2 with line 1's premise. AC2 (exactly one token carrying the input value in each output place and none elsewhere) is line 1. AC3 (throws or errors if the transition does not declare exactly one input place) is line 2. AC4 (on two or more consumed tokens, fails or copies the oldest as in AC2) is line 3. The test derivation (fork with one input and three outputs; all three receive the same value) is CORE_052_nonvacuous: on And(Place 1, And(Place 2, Place 3)) the reference fork completes with 7 in places 1, 2 and 3, and the reference action firing deposits them."
  signoff "pending"
  statement : ∀ {N T V : Type} [DecidableEq N], (T → V) → ActionFn N T → Prop :=
    fun val Fork => ∀ t δ,
      (∀ i x, core052_soleInput t i → δ.inputs i = [x] →
        ∃ e, Fork t δ = .ok e ∧
          ∀ p, (EmittedTo e p).map val = if OutputArc t p then [val x] else []) ∧
      ((¬ ∃ i, core052_soleInput t i) → (∀ p ∈ inPlaces t, δ.inputs p ≠ []) →
        ∃ msg, Fork t δ = .error msg) ∧
      (∀ i x y ys, core052_soleInput t i → δ.inputs i = x :: y :: ys →
        (∃ msg, Fork t δ = .error msg) ∨
        ∃ e, Fork t δ = .ok e ∧
          ∀ p, (EmittedTo e p).map val = if OutputArc t p then [val x] else [])

/- The pinned readable form of CORE-052: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CORE_052 : {N T V : Type} → [DecidableEq N] → (T → V) → ActionFn N T → Prop :=
fun {N T V} [DecidableEq N] val Fork =>
  ∀ (t : Reference.Trans N) (δ : Delivered N T),
    (∀ (i : N) (x : T),
        core052_soleInput t i →
          δ.inputs i = [x] →
            ∃ e,
              Fork t δ = Except.ok e ∧
                ∀ (p : N), List.map val (EmittedTo e p) = if OutputArc t p then [val x] else []) ∧
      ((¬∃ i, core052_soleInput t i) → (∀ p ∈ inPlaces t, δ.inputs p ≠ []) → ∃ msg, Fork t δ = Except.error msg) ∧
        ∀ (i : N) (x y : T) (ys : List T),
          core052_soleInput t i →
            δ.inputs i = x :: y :: ys →
              (∃ msg, Fork t δ = Except.error msg) ∨
                ∃ e,
                  Fork t δ = Except.ok e ∧
                    ∀ (p : N), List.map val (EmittedTo e p) = if OutputArc t p then [val x] else []
-/
#guard_msgs in #print CORE_052

/-! ### The three lines, named (for the mutants) -/

section Lines

variable {N T V : Type} [DecidableEq N]

/-- Line 1 of CORE-052: one sole input place, one consumed token: one copy of its value in every
output place and nothing elsewhere. -/
def core052_line1 (val : T → V) (Fork : ActionFn N T) : Prop :=
  ∀ t δ i x, core052_soleInput t i → δ.inputs i = [x] →
    ∃ e, Fork t δ = .ok e ∧
      ∀ p, (EmittedTo e p).map val = if OutputArc t p then [val x] else []

/-- Line 2 of CORE-052: no sole input place, and every input place delivered: fork fails. -/
def core052_line2 (Fork : ActionFn N T) : Prop :=
  ∀ t (δ : Delivered N T), (¬ ∃ i, core052_soleInput t i) → (∀ p ∈ inPlaces t, δ.inputs p ≠ []) →
    ∃ msg, Fork t δ = .error msg

/-- Line 3 of CORE-052: a batch from the sole input place: fork fails, or copies the oldest
consumed value once to every output place and nothing elsewhere. -/
def core052_line3 (val : T → V) (Fork : ActionFn N T) : Prop :=
  ∀ t δ i x y ys, core052_soleInput t i → δ.inputs i = x :: y :: ys →
    (∃ msg, Fork t δ = .error msg) ∨
    ∃ e, Fork t δ = .ok e ∧
      ∀ p, (EmittedTo e p).map val = if OutputArc t p then [val x] else []

/-- CORE-052 is its three lines. -/
theorem core052_iff (val : T → V) (Fork : ActionFn N T) :
    CORE_052 val Fork ↔ core052_line1 val Fork ∧ core052_line2 Fork ∧ core052_line3 val Fork :=
  ⟨fun h => ⟨fun t δ => (h t δ).1, fun t δ => (h t δ).2.1, fun t δ => (h t δ).2.2⟩,
    fun ⟨h1, h2, h3⟩ t δ => ⟨h1 t δ, h2 t δ, h3 t δ⟩⟩

end Lines

/-! ## The reference forks -/

section Reference

variable {N T : Type} [DecidableEq N]

/-- **The reference fork** (Java, Rust, Python): with one input place, copy the oldest consumed
token to every output place; with any other number of input places, fail with the runtimes'
message. -/
def refFork : ActionFn N T := fun t δ =>
  match (inPlaces t).eraseDups with
  | [i] => match δ.inputs i with
    | x :: _ => .ok ((outPlaceSet t).map (·, x))
    | [] => .error "No tokens for the input place"
  | l => .error s!"Fork requires exactly 1 input place, found {l.length}"

/- The reference fork is a witness model of CORE-052. -/
#spec_witness refFork

/-- **The strict reading** (TypeScript): as `refFork`, but fail unless the firing consumed
exactly one token from the input place. -/
def refForkStrict : ActionFn N T := fun t δ =>
  match (inPlaces t).eraseDups with
  | [i] => match δ.inputs i with
    | [x] => .ok ((outPlaceSet t).map (·, x))
    | l => .error s!"Place consumed {l.length} tokens, use inputs() for batched access"
  | l => .error s!"Fork requires exactly 1 input place, found {l.length}"

/- The strict reading is a witness model of CORE-052 too. -/
#spec_witness refForkStrict

end Reference

/-! ### Lemmas -/

section Lemmas

variable {N T V : Type} [DecidableEq N]

omit [DecidableEq N] in
/-- A list without repetition whose members are exactly `i` is `[i]`. -/
theorem core052_nodup_eq_singleton {l : List N} {i : N} (hl : l.Nodup)
    (hm : ∀ p, p ∈ l ↔ p = i) : l = [i] := by
  cases l with
  | nil => exact absurd ((hm i).2 rfl) (List.not_mem_nil)
  | cons a as =>
    have ha : a = i := (hm a).1 (List.mem_cons_self ..)
    subst ha
    cases as with
    | nil => rfl
    | cons b bs =>
      have hb : b = a := (hm b).1 (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      subst hb
      exact absurd (List.mem_cons_self ..) (List.nodup_cons.1 hl).1

/-- The sole input place, as the reference computes it. -/
theorem core052_soleInput_iff (t : Trans N) (i : N) :
    core052_soleInput t i ↔ (inPlaces t).eraseDups = [i] := by
  constructor
  · intro h
    exact core052_nodup_eq_singleton (eraseDups_nodup _)
      fun p => List.mem_eraseDups.trans (h p)
  · intro h p
    rw [← List.mem_eraseDups, h, List.mem_singleton]

/-- A copy of `x` in every output place, as values. -/
theorem core052_copies (val : T → V) (t : Trans N) (x : T) (p : N) :
    (EmittedTo ((outPlaceSet t).map (·, x)) p).map val =
      if OutputArc t p then [val x] else [] := by
  rw [emittedTo_outPlaceSet]
  split <;> rfl

/-- A place an emission does not name receives nothing from it. -/
theorem core052_emittedTo_nil {e : List (N × T)} {p : N} (h : p ∉ e.map Prod.fst) :
    EmittedTo e p = [] := by
  simp only [EmittedTo, qEmittedTo, List.map_eq_nil_iff, List.filter_eq_nil_iff,
    decide_eq_true_eq]
  intro a ha hap
  exact h (List.mem_map.2 ⟨a, ha, hap⟩)

/-- The strict reading fails on a batch from the sole input place. -/
theorem core052_strict_batch {t : Trans N} {δ : Delivered N T} {i : N} {x y : T} {ys : List T}
    (hi : core052_soleInput t i) (hx : δ.inputs i = x :: y :: ys) :
    ∃ msg, refForkStrict t δ = .error msg := by
  unfold refForkStrict
  rw [(core052_soleInput_iff t i).1 hi]
  simp only [hx]
  exact ⟨_, rfl⟩

omit [DecidableEq N] in
/-- Every input place of `t` delivered, when the sole input place delivered. -/
theorem core052_delivered_of_sole {t : Trans N} {δ : Delivered N T} {i : N}
    (hi : core052_soleInput t i) (hx : δ.inputs i ≠ []) : ∀ p ∈ inPlaces t, δ.inputs p ≠ [] := by
  intro p hp
  rw [(hi p).1 hp]
  exact hx

end Lemmas

/-! ## The reference -/

/-- ✓ The reference fork (Java, Rust, Python: the oldest token of a batch) satisfies CORE-052, at
every type and every value projection. -/
@[evidence holds CORE_052]
theorem CORE_052_reference {N T V : Type} [DecidableEq N] (val : T → V) :
    CORE_052 val (refFork (N := N) (T := T)) := by
  intro t δ
  refine ⟨fun i x hi hx => ?_, fun hn _ => ?_, fun i x y ys hi hx => .inr ?_⟩
  · refine ⟨(outPlaceSet t).map (·, x), ?_, core052_copies val t x⟩
    simp [refFork, (core052_soleInput_iff t i).1 hi, hx]
  · unfold refFork
    split
    · next i h => exact absurd ⟨i, (core052_soleInput_iff t i).2 h⟩ hn
    · exact ⟨_, rfl⟩
  · refine ⟨(outPlaceSet t).map (·, x), ?_, core052_copies val t x⟩
    simp [refFork, (core052_soleInput_iff t i).1 hi, hx]

/-- ✓ The strict reading (TypeScript: a batch fails) satisfies CORE-052 too. -/
@[evidence holds CORE_052]
theorem CORE_052_reference_strict {N T V : Type} [DecidableEq N] (val : T → V) :
    CORE_052 val (refForkStrict (N := N) (T := T)) := by
  intro t δ
  refine ⟨fun i x hi hx => ?_, fun hn _ => ?_, fun i x y ys hi hx => .inl ?_⟩
  · refine ⟨(outPlaceSet t).map (·, x), ?_, core052_copies val t x⟩
    simp [refForkStrict, (core052_soleInput_iff t i).1 hi, hx]
  · unfold refForkStrict
    split
    · next i h => exact absurd ⟨i, (core052_soleInput_iff t i).2 h⟩ hn
    · exact ⟨_, rfl⟩
  · exact core052_strict_batch hi hx

/-! ## The fork writes through the context -/

/-- **The reference fork writes through the context**: under a context whose output call on an
output place appends one entry per value (CORE-062 line 1), every emission the reference fork
completes with is a buffer built by one single output call per output place, so
`ctx_deposits_outputs` applies to fork firings. -/
theorem refFork_throughCtx {N T V : Type} [DecidableEq N] {C : Ctx N T V} (val : T → V)
    (hC : ∀ t e p vs, OutputArc t p → C.output t e p vs = some (e ++ vs.map fun v => (p, v))) :
    ThroughCtx C val (ActionFn.rel (refFork (N := N) (T := T))) := by
  intro t δ e h
  unfold ActionFn.rel refFork at h
  split at h
  · split at h
    · rename_i x _ _
      cases h
      have hb := built_append_copies hC Built.nil (outPlaceSet t)
        (fun p hp => (mem_outPlaceSet t p).1 hp) (val x)
      simpa [List.map_map, Function.comp_def] using hb
    · cases h
  · cases h

/-! ## Examples -/

/-- `f3`: one input arc on place 0, output `And(Place 1, And(Place 2, Place 3))` (the test
derivation: one input, three outputs). -/
def core052_f3 : Trans Nat :=
  { core := { name := "f3", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.and (.place 1) (.and (.place 2) (.place 3))) }

/-- `f2`: one input arc on place 0, output `And(Place 1, Place 2)`. -/
def core052_f2 : Trans Nat :=
  { core := { name := "f2", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.and (.place 1) (.place 2)) }

/-- `fAll`: one `All` input arc on place 0, output `And(Place 1, Place 2)`. -/
def core052_fAll : Trans Nat :=
  { core := { name := "fAll", inputs := [⟨0, .all⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.and (.place 1) (.place 2)) }

/-- `two`: input arcs on places 0 and 4, output `Place 1`. -/
def core052_two : Trans Nat :=
  { core :=
      { name := "two", inputs := [⟨0, .one⟩, ⟨4, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 1) }

/-- `none`: no input arc, output `Place 1`. -/
def core052_noIn : Trans Nat :=
  { core := { name := "noIn", inputs := [], inhibitors := [], reads := [], resets := [] },
    out := some (.place 1) }

/-- `xor`: one input arc on place 0, output `Xor(Place 1, Place 2)`. -/
def core052_xorT : Trans Nat :=
  { core := { name := "xor", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.xor (.place 1) (.place 2)) }

/-- Place 0 holds 7; every other place is empty. -/
def core052_M : QueueMarking Nat Nat := fun p => if p = 0 then [7] else []

/-- Place 0 holds 7, then 8; every other place is empty. -/
def core052_M2 : QueueMarking Nat Nat := fun p => if p = 0 then [7, 8] else []

/-- A delivery of the one token 7 from place 0 and of 9 from place 4. -/
def core052_δ : Delivered Nat Nat := ⟨fun p => if p = 0 then [7] else if p = 4 then [9] else [],
  fun _ => []⟩

/-- A delivery of the one token 7 from place 0 and nothing from place 4: no firing of `two`
delivers this (both of its input arcs require a token). -/
def core052_δ0 : Delivered Nat Nat := ⟨fun p => if p = 0 then [7] else [], fun _ => []⟩

/-- The emission of the reference fork on `f3`. -/
def core052_e3 : List (Nat × Nat) := [(1, 7), (2, 7), (3, 7)]

/-- On `two`, `core052_δ` delivers from both input places. -/
theorem core052_two_delivered : ∀ p ∈ inPlaces core052_two, core052_δ.inputs p ≠ [] := by
  intro p hp
  simp [core052_two, inPlaces] at hp
  rcases hp with rfl | rfl <;> decide

/-- `two` has no sole input place. -/
theorem core052_two_noSole : ¬ ∃ i, core052_soleInput core052_two i := by
  rintro ⟨i, hi⟩
  have h0 := (hi 0).1 (by decide)
  have h4 := (hi 4).1 (by decide)
  omega

/-- `f2` has the sole input place 0. -/
theorem core052_f2_sole : core052_soleInput core052_f2 0 :=
  (core052_soleInput_iff _ _).2 (by decide)

/-- `fAll` has the sole input place 0. -/
theorem core052_fAll_sole : core052_soleInput core052_fAll 0 :=
  (core052_soleInput_iff _ _).2 (by decide)

/-- ✓ CORE-052 is not vacuous. The test derivation: on `f3` (one input, three outputs) fired from
a place 0 holding 7, the reference fork completes with 7 in places 1, 2 and 3, the reference
action firing under it deposits them, and places 1, 2 and 3 then hold 7; on `two` (two input
places) and on `noIn` (none) it fails; on `fAll` fired from a place 0 holding 7 then 8 (a batch)
it completes with the oldest, 7, in places 1 and 2. -/
@[evidence nonvacuous CORE_052]
theorem CORE_052_nonvacuous :
    refFork core052_f3 (qDelivered core052_M core052_f3) = .ok core052_e3 ∧
    refActionFire (ActionFn.rel refFork) core052_f3 core052_M (qDelivered core052_M core052_f3)
      core052_e3 (qFire core052_M core052_f3 core052_e3) ∧
    [1, 2, 3].map (qFire core052_M core052_f3 core052_e3) = [[7], [7], [7]] ∧
    qFire core052_M core052_f3 core052_e3 0 = [] ∧
    (∃ msg, refFork core052_two core052_δ = .error msg) ∧
    (∃ msg, refFork core052_noIn core052_δ = .error msg) ∧
    refFork core052_fAll (qDelivered core052_M2 core052_fAll) = .ok [(1, 7), (2, 7)] := by
  refine ⟨by decide, ⟨⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩,
    show ([1, 2, 3] : List Nat) ∈ [[1, 2, 3]] from List.mem_singleton.2 rfl,
    (by decide : refFork core052_f3 (qDelivered core052_M core052_f3) = .ok core052_e3)⟩,
    by decide, by decide, ⟨_, rfl⟩, ⟨_, rfl⟩, by decide⟩

/-! ## The batch case: undecided between the two readings -/

/-- ? Ruling D50 (a). Both readings satisfy CORE-052, and they differ on a batch: on `fAll` fired
from a place 0 holding 7 then 8, the firing delivers both tokens; the reference fork (Java, Rust,
Python) copies the oldest, 7, to places 1 and 2, and the strict reading (TypeScript) fails. Which
one an implementation follows is not settled by the block; line 3 allows exactly these two. -/
@[evidence undecided CORE_052]
theorem CORE_052_batch_undecided :
    CORE_052 (id : Nat → Nat) (refFork (N := Nat)) ∧
    CORE_052 (id : Nat → Nat) (refForkStrict (N := Nat)) ∧
    (qDelivered core052_M2 core052_fAll).inputs 0 = [7, 8] ∧
    refFork core052_fAll (qDelivered core052_M2 core052_fAll) = .ok [(1, 7), (2, 7)] ∧
    (∃ msg, refForkStrict core052_fAll (qDelivered core052_M2 core052_fAll) = .error msg) :=
  ⟨CORE_052_reference id, CORE_052_reference_strict id, by decide, by decide, ⟨_, rfl⟩⟩

/-! ## Allowed: a new token with the same value -/

/-- A fork on stamped tokens `(value, created_at)` that emits a NEW token, with the consumed
value and the stamp 0, as every runtime does (a fresh `created_at`). -/
def core052_stampFork : ActionFn Nat (Nat × Nat) := fun t δ =>
  match refFork t δ with
  | .ok e => .ok (e.map fun pe => (pe.1, (pe.2.1, 0)))
  | .error m => .error m

/-- Restamping keeps the values an emission sends to every place. -/
theorem core052_restamp_values (e : List (Nat × (Nat × Nat))) (p : Nat) :
    (EmittedTo (e.map fun pe => (pe.1, (pe.2.1, 0))) p).map Prod.fst =
      (EmittedTo e p).map Prod.fst := by
  simp only [EmittedTo, qEmittedTo, List.filter_map, List.map_map]
  rfl

/-- ✓ A fork that emits a new token carrying the consumed value satisfies CORE-052 on values,
while its tokens are not the consumed one: on `f2` with the stamped token `(7, 100)` delivered,
place 1 receives `(7, 0)`. -/
@[evidence allows CORE_052]
theorem CORE_052_allows_freshStamp :
    CORE_052 Prod.fst core052_stampFork ∧
    core052_stampFork core052_f2 ⟨fun p => if p = 0 then [(7, 100)] else [], fun _ => []⟩ =
      .ok [(1, (7, 0)), (2, (7, 0))] := by
  refine ⟨fun t δ => ⟨fun i x hi hx => ?_, fun hn hd => ?_, fun i x y ys hi hx => ?_⟩, by decide⟩
  · obtain ⟨e, he, hp⟩ := (CORE_052_reference (N := Nat) (T := Nat × Nat) Prod.fst t δ).1 i x hi hx
    refine ⟨e.map fun pe => (pe.1, (pe.2.1, 0)), by simp [core052_stampFork, he], fun p => ?_⟩
    rw [← hp p, core052_restamp_values]
  · obtain ⟨m, hm⟩ := (CORE_052_reference (N := Nat) (T := Nat × Nat) Prod.fst t δ).2.1 hn hd
    exact ⟨m, by simp [core052_stampFork, hm]⟩
  · rcases (CORE_052_reference (N := Nat) (T := Nat × Nat) Prod.fst t δ).2.2 i x y ys hi hx with
      ⟨m, hm⟩ | ⟨e, he, hp⟩
    · exact .inl ⟨m, by simp [core052_stampFork, hm]⟩
    · refine .inr ⟨e.map fun pe => (pe.1, (pe.2.1, 0)), by simp [core052_stampFork, he],
        fun p => ?_⟩
      rw [← hp p, core052_restamp_values]

/-! ## Allowed: Rust's count of input places -/

/-- Rust's fork (rust/libpetri-core/src/action.rs `Fork::run_sync`): it counts the input places
by `input_place_names`, the keys of the consumed-input map, which holds a place only when a token
was taken from it. So its input places are the declared ones that delivered a token. -/
def core052_rustCount {N T : Type} [DecidableEq N] : ActionFn N T := fun t δ =>
  match ((inPlaces t).eraseDups.filter fun p => !(δ.inputs p).isEmpty) with
  | [i] => match δ.inputs i with
    | x :: _ => .ok ((outPlaceSet t).map (·, x))
    | [] => .error "No tokens for the input place"
  | l => .error s!"Fork requires exactly 1 input place, found {l.length}"

/-- On every delivery in which each input place delivered at least one token (every firing),
Rust's count is the reference fork. -/
theorem core052_rustCount_agrees {N T : Type} [DecidableEq N] (t : Trans N) (δ : Delivered N T)
    (h : ∀ p ∈ inPlaces t, δ.inputs p ≠ []) : core052_rustCount t δ = refFork t δ := by
  have hf : ((inPlaces t).eraseDups.filter fun p => !(δ.inputs p).isEmpty) =
      (inPlaces t).eraseDups := by
    apply List.filter_eq_self.2
    intro p hp
    have := h p (List.mem_eraseDups.1 hp)
    cases hq : δ.inputs p with
    | nil => exact absurd hq this
    | cons _ _ => rfl
  unfold core052_rustCount refFork
  rw [hf]

/-- ✓ A fork that counts input places as Rust does satisfies CORE-052: it agrees with the
reference fork on every delivery a firing produces, and differs only on one no firing produces,
`two` with a token from place 0 and none from place 4, where it completes. Line 2 is stated for
deliveries in which every input place delivered, so it does not reach that one. -/
@[evidence allows CORE_052]
theorem CORE_052_allows_rustCount {V : Type} (val : Nat → V) :
    CORE_052 val (core052_rustCount (N := Nat) (T := Nat)) ∧
    core052_rustCount core052_two core052_δ0 = .ok [(1, 7)] := by
  refine ⟨fun t δ => ⟨fun i x hi hx => ?_, fun hn hd => ?_, fun i x y ys hi hx => ?_⟩, by decide⟩
  · rw [core052_rustCount_agrees t δ (core052_delivered_of_sole hi (by simp [hx]))]
    exact (CORE_052_reference val t δ).1 i x hi hx
  · rw [core052_rustCount_agrees t δ hd]
    exact (CORE_052_reference val t δ).2.1 hn hd
  · rw [core052_rustCount_agrees t δ (core052_delivered_of_sole hi (by simp [hx]))]
    exact (CORE_052_reference val t δ).2.2 i x y ys hi hx

/-! ## Wrong forks -/

/-- A fork that emits another value: the consumed value plus one. -/
def core052_otherValue : ActionFn Nat Nat := fun t δ =>
  match refFork t δ with
  | .ok e => .ok (e.map fun pe => (pe.1, pe.2 + 1))
  | .error m => .error m

/-- ✗ It violates line 1: on `f2` with 7 delivered, place 1 receives 8. -/
@[evidence forbids CORE_052]
theorem CORE_052_forbids_otherValue : ¬ CORE_052 (id : Nat → Nat) core052_otherValue := by
  intro h
  obtain ⟨e, he, hp⟩ := (h core052_f2 (qDelivered core052_M core052_f2)).1 0 7
    core052_f2_sole (by decide)
  have : core052_otherValue core052_f2 (qDelivered core052_M core052_f2) = .ok [(1, 8), (2, 8)] :=
    by decide
  rw [this] at he; cases he
  exact absurd (hp 1) (by decide)

/-- A fork that accepts two input places and copies the oldest token of the first. -/
def core052_acceptTwo : ActionFn Nat Nat := fun t δ =>
  match (inPlaces t).eraseDups with
  | i :: _ => match δ.inputs i with
    | x :: _ => .ok ((outPlaceSet t).map (·, x))
    | [] => .error "no token"
  | [] => .error "Fork requires exactly 1 input place, found 0"

/-- ✗ It violates line 2: on `two` (input places 0 and 4, both delivering) it completes. -/
@[evidence forbids CORE_052]
theorem CORE_052_forbids_acceptTwo : ¬ CORE_052 (id : Nat → Nat) core052_acceptTwo := by
  intro h
  obtain ⟨m, hm⟩ := (h core052_two core052_δ).2.1 core052_two_noSole core052_two_delivered
  have : core052_acceptTwo core052_two core052_δ = .ok [(1, 7)] := by decide
  rw [this] at hm; cases hm

/-! ### Mutant: line 1 without "every output place" -/

section MutantOnly

variable {N T V : Type} [DecidableEq N]

/-- Mutant reading of line 1 ("copies to output places" without "all"): fork completes, and
every token it emits goes to an output place and carries the consumed value. Lines 2 and 3 are as
in CORE-052. -/
def CORE_052_mutant_onlyOutputs (val : T → V) (Fork : ActionFn N T) : Prop :=
  (∀ t δ i x, core052_soleInput t i → δ.inputs i = [x] →
    ∃ e, Fork t δ = .ok e ∧ ∀ pe ∈ e, OutputArc t pe.1 ∧ val pe.2 = val x) ∧
    core052_line2 Fork ∧ core052_line3 val Fork

/-- A fork that writes only the first output place, and fails on a batch. -/
def core052_firstOnly : ActionFn N T := fun t δ =>
  match (inPlaces t).eraseDups with
  | [i] => match δ.inputs i with
    | [x] => .ok (((outPlaceSet t).take 1).map (·, x))
    | _ => .error "not one token"
  | l => .error s!"Fork requires exactly 1 input place, found {l.length}"

end MutantOnly

/-- ✗ The first-output fork kills the mutant: it emits only tokens with the consumed value to
output places, but on `f2` place 2 receives nothing (line 1). -/
@[evidence mutant CORE_052]
theorem CORE_052_mutant_onlyOutputs_killed :
    CORE_052_mutant_onlyOutputs (id : Nat → Nat) (core052_firstOnly (N := Nat)) ∧
      ¬ CORE_052 (id : Nat → Nat) (core052_firstOnly (N := Nat)) := by
  refine ⟨⟨fun t δ i x hi hx => ?_, fun t δ hn _ => ?_, fun t δ i x y ys hi hx => .inl ?_⟩,
    fun h => ?_⟩
  · refine ⟨((outPlaceSet t).take 1).map (·, x), ?_, fun pe hpe => ?_⟩
    · simp [core052_firstOnly, (core052_soleInput_iff t i).1 hi, hx]
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hpe
      exact ⟨(mem_outPlaceSet t p).1 (List.mem_of_mem_take hp), rfl⟩
  · unfold core052_firstOnly
    split
    · next i h => exact absurd ⟨i, (core052_soleInput_iff t i).2 h⟩ hn
    · exact ⟨_, rfl⟩
  · unfold core052_firstOnly
    rw [(core052_soleInput_iff t i).1 hi]
    simp only [hx]
    exact ⟨_, rfl⟩
  · obtain ⟨e, he, hp⟩ := (h core052_f2 (qDelivered core052_M core052_f2)).1 0 7
      core052_f2_sole (by decide)
    have : core052_firstOnly core052_f2 (qDelivered core052_M core052_f2) = .ok [(1, 7)] :=
      by decide
    rw [this] at he; cases he
    exact absurd (hp 2) (by decide)

/-! ### Mutant: AC2 read literally (every output place receives the value) -/

section MutantAc2

variable {N T V : Type} [DecidableEq N]

/-- Mutant reading of line 1 (the old AC2 literally, "produces the input value to all output
places"): fork completes, and every output place receives a token carrying the consumed value;
how many, and what other places receive, is left open. Lines 2 and 3 are as in CORE-052. -/
def CORE_052_mutant_ac2Literal (val : T → V) (Fork : ActionFn N T) : Prop :=
  (∀ t δ i x, core052_soleInput t i → δ.inputs i = [x] →
    ∃ e, Fork t δ = .ok e ∧ ∀ p, OutputArc t p → val x ∈ (EmittedTo e p).map val) ∧
    core052_line2 Fork ∧ core052_line3 val Fork

/-- A fork that writes two copies to every output place (and fails on a batch, as the strict
reading does). -/
def core052_double : ActionFn N T := fun t δ =>
  match refForkStrict t δ with
  | .ok e => .ok (e ++ e)
  | .error m => .error m

/-- A fork that also writes the token back to its input place when that is no output place, and
fails on a batch. -/
def core052_echo : ActionFn N T := fun t δ =>
  match (inPlaces t).eraseDups with
  | [i] => match δ.inputs i with
    | [x] => .ok ((outPlaceSet t).map (·, x) ++
        if OutputArc t i then [] else [(i, x)])
    | _ => .error "not one token"
  | l => .error s!"Fork requires exactly 1 input place, found {l.length}"

/-- Every output place receives the value from the reference emission. -/
theorem core052_ref_mem (val : T → V) (t : Trans N) (x : T) (p : N) (hp : OutputArc t p) :
    val x ∈ (EmittedTo ((outPlaceSet t).map (·, x)) p).map val := by
  rw [core052_copies val t x p, if_pos hp]
  exact List.mem_singleton_self _

end MutantAc2

/-- ✗ The doubling fork kills the mutant: every output place receives the value, but on `f2`
place 1 receives two tokens (line 1, exactly one). -/
@[evidence mutant CORE_052]
theorem CORE_052_mutant_ac2Literal_killed_double :
    CORE_052_mutant_ac2Literal (id : Nat → Nat) (core052_double (N := Nat)) ∧
      ¬ CORE_052 (id : Nat → Nat) (core052_double (N := Nat)) := by
  refine ⟨⟨fun t δ i x hi hx => ?_, fun t δ hn hd => ?_, fun t δ i x y ys hi hx => .inl ?_⟩,
    fun h => ?_⟩
  · refine ⟨(outPlaceSet t).map (·, x) ++ (outPlaceSet t).map (·, x), ?_, fun p hp => ?_⟩
    · simp [core052_double, refForkStrict, (core052_soleInput_iff t i).1 hi, hx]
    · simp only [EmittedTo, qEmittedTo, List.filter_append, List.map_append, List.mem_append]
      exact .inl (core052_ref_mem id t x p hp)
  · obtain ⟨m, hm⟩ := (CORE_052_reference_strict (V := Unit) (fun _ => ()) t δ).2.1 hn hd
    exact ⟨m, by simp [core052_double, hm]⟩
  · obtain ⟨m, hm⟩ := core052_strict_batch (T := Nat) hi hx
    exact ⟨m, by simp [core052_double, hm]⟩
  · obtain ⟨e, he, hp⟩ := (h core052_f2 (qDelivered core052_M core052_f2)).1 0 7
      core052_f2_sole (by decide)
    have : core052_double core052_f2 (qDelivered core052_M core052_f2) =
        .ok [(1, 7), (2, 7), (1, 7), (2, 7)] := by decide
    rw [this] at he; cases he
    exact absurd (hp 1) (by decide)

/-- ✗ The echoing fork kills the mutant: every output place receives the value, but on `f2` the
input place 0 receives a copy too (line 1, nothing elsewhere). -/
@[evidence mutant CORE_052]
theorem CORE_052_mutant_ac2Literal_killed_echo :
    CORE_052_mutant_ac2Literal (id : Nat → Nat) (core052_echo (N := Nat)) ∧
      ¬ CORE_052 (id : Nat → Nat) (core052_echo (N := Nat)) := by
  refine ⟨⟨fun t δ i x hi hx => ?_, fun t δ hn _ => ?_, fun t δ i x y ys hi hx => .inl ?_⟩,
    fun h => ?_⟩
  · refine ⟨(outPlaceSet t).map (·, x) ++ (if OutputArc t i then [] else [(i, x)]), ?_,
      fun p hp => ?_⟩
    · simp [core052_echo, (core052_soleInput_iff t i).1 hi, hx]
    · simp only [EmittedTo, qEmittedTo, List.filter_append, List.map_append, List.mem_append]
      exact .inl (core052_ref_mem id t x p hp)
  · unfold core052_echo
    split
    · next i h => exact absurd ⟨i, (core052_soleInput_iff t i).2 h⟩ hn
    · exact ⟨_, rfl⟩
  · unfold core052_echo
    rw [(core052_soleInput_iff t i).1 hi]
    simp only [hx]
    exact ⟨_, rfl⟩
  · obtain ⟨e, he, hp⟩ := (h core052_f2 (qDelivered core052_M core052_f2)).1 0 7
      core052_f2_sole (by decide)
    have : core052_echo core052_f2 (qDelivered core052_M core052_f2) =
        .ok [(1, 7), (2, 7), (0, 7)] := by decide
    rw [this] at he; cases he
    exact absurd (hp 0) (by decide)

/-! ### Mutant: AC3's old wording (fail only on more than one input place) -/

section MutantAc3

variable {N T V : Type} [DecidableEq N]

/-- Mutant reading of line 2 (AC3 before the D20 rewording, "throws if more than one input place
is declared"): fork fails on two or more input places; zero is left open. Lines 1 and 3 are as
in CORE-052. -/
def CORE_052_mutant_ac3Literal (val : T → V) (Fork : ActionFn N T) : Prop :=
  core052_line1 val Fork ∧
    (∀ t (δ : Delivered N T), 2 ≤ (inPlaces t).eraseDups.length →
      (∀ p ∈ inPlaces t, δ.inputs p ≠ []) → ∃ msg, Fork t δ = .error msg) ∧
    core052_line3 val Fork

/-- A fork that completes with no token on a transition without input places. -/
def core052_zeroOk : ActionFn N T := fun t δ =>
  match (inPlaces t).eraseDups with
  | [] => .ok []
  | _ => refFork t δ

end MutantAc3

/-- ✗ The zero-tolerant fork kills the mutant: it meets lines 1 and 3 and fails on two or more
input places, but on `noIn` (no input place) it completes (line 2). -/
@[evidence mutant CORE_052]
theorem CORE_052_mutant_ac3Literal_killed :
    CORE_052_mutant_ac3Literal (id : Nat → Nat) (core052_zeroOk (N := Nat)) ∧
      ¬ CORE_052 (id : Nat → Nat) (core052_zeroOk (N := Nat)) := by
  refine ⟨⟨fun t δ i x hi hx => ?_, fun t δ h2 hd => ?_, fun t δ i x y ys hi hx => ?_⟩,
    fun h => ?_⟩
  · have hs := (core052_soleInput_iff t i).1 hi
    have := (CORE_052_reference (N := Nat) (T := Nat) id t δ).1 i x hi hx
    simpa [core052_zeroOk, hs] using this
  · have hn : ¬ ∃ i, core052_soleInput t i := by
      rintro ⟨i, hi⟩
      rw [(core052_soleInput_iff t i).1 hi] at h2
      simp at h2
    obtain ⟨m, hm⟩ := (CORE_052_reference (N := Nat) (T := Nat) id t δ).2.1 hn hd
    refine ⟨m, ?_⟩
    unfold core052_zeroOk
    split
    · next h0 => rw [h0] at h2; simp at h2
    · exact hm
  · have hs := (core052_soleInput_iff t i).1 hi
    have := (CORE_052_reference (N := Nat) (T := Nat) id t δ).2.2 i x y ys hi hx
    simpa [core052_zeroOk, hs] using this
  · obtain ⟨m, hm⟩ := (h core052_noIn core052_δ).2.1 (by
      rintro ⟨i, hi⟩
      exact absurd ((hi i).2 rfl) (by simp [core052_noIn, inPlaces]))
      (by simp [core052_noIn, inPlaces])
    have : core052_zeroOk core052_noIn core052_δ = .ok [] := by decide
    rw [this] at hm; cases hm

/-! ### Mutant: the batch left open (no line 3) -/

section MutantNoBatch

variable {N T V : Type} [DecidableEq N]

/-- Mutant reading: ruling D50 (a)'s exactly-one premise with nothing said of a batch, that is
lines 1 and 2 of CORE-052 without line 3. -/
def CORE_052_mutant_noBatch (val : T → V) (Fork : ActionFn N T) : Prop :=
  core052_line1 val Fork ∧ core052_line2 Fork

/-- A fork that iterates the batch (Rust `input_tokens_raw`, Java `ctx.inputs(place)`, instead of
`input_raw` / `ctx.input`): every consumed token of the sole input place goes to every output
place. -/
def core052_allTokens : ActionFn N T := fun t δ =>
  match (inPlaces t).eraseDups with
  | [i] => match δ.inputs i with
    | [] => .error "No tokens for the input place"
    | xs => .ok (xs.flatMap fun x => (outPlaceSet t).map (·, x))
  | l => .error s!"Fork requires exactly 1 input place, found {l.length}"

/-- A fork that copies the newest consumed token of the batch (`last` instead of the FIFO head). -/
def core052_newest : ActionFn N T := fun t δ =>
  match (inPlaces t).eraseDups with
  | [i] => match (δ.inputs i).getLast? with
    | some x => .ok ((outPlaceSet t).map (·, x))
    | none => .error "No tokens for the input place"
  | l => .error s!"Fork requires exactly 1 input place, found {l.length}"

end MutantNoBatch

/-- ✗ The batch-iterating fork kills the mutant: it meets lines 1 and 2, but on `fAll` fired from
a place 0 holding 7 then 8 it sends 7 and 8 to place 1 (line 3: fail, or one copy of the
oldest). -/
@[evidence mutant CORE_052]
theorem CORE_052_mutant_noBatch_killed_all :
    CORE_052_mutant_noBatch (id : Nat → Nat) (core052_allTokens (N := Nat)) ∧
      ¬ CORE_052 (id : Nat → Nat) (core052_allTokens (N := Nat)) := by
  refine ⟨⟨fun t δ i x hi hx => ?_, fun t δ hn _ => ?_⟩, fun h => ?_⟩
  · refine ⟨(outPlaceSet t).map (·, x), ?_, core052_copies id t x⟩
    simp [core052_allTokens, (core052_soleInput_iff t i).1 hi, hx]
  · unfold core052_allTokens
    split
    · next i h => exact absurd ⟨i, (core052_soleInput_iff t i).2 h⟩ hn
    · exact ⟨_, rfl⟩
  · have hm2 : core052_allTokens core052_fAll (qDelivered core052_M2 core052_fAll) =
        .ok [(1, 7), (2, 7), (1, 8), (2, 8)] := by decide
    rcases (h core052_fAll (qDelivered core052_M2 core052_fAll)).2.2 0 7 8 []
        core052_fAll_sole (by decide) with ⟨m, hm⟩ | ⟨e, he, hp⟩
    · rw [hm2] at hm; cases hm
    · rw [hm2] at he; cases he
      exact absurd (hp 1) (by decide)

/-- ✗ The newest-token fork kills the mutant: it meets lines 1 and 2, but on `fAll` fired from a
place 0 holding 7 then 8 it sends 8 to places 1 and 2 (line 3: fail, or a copy of the oldest,
7). -/
@[evidence mutant CORE_052]
theorem CORE_052_mutant_noBatch_killed_newest :
    CORE_052_mutant_noBatch (id : Nat → Nat) (core052_newest (N := Nat)) ∧
      ¬ CORE_052 (id : Nat → Nat) (core052_newest (N := Nat)) := by
  refine ⟨⟨fun t δ i x hi hx => ?_, fun t δ hn _ => ?_⟩, fun h => ?_⟩
  · refine ⟨(outPlaceSet t).map (·, x), ?_, core052_copies id t x⟩
    simp [core052_newest, (core052_soleInput_iff t i).1 hi, hx]
  · unfold core052_newest
    split
    · next i h => exact absurd ⟨i, (core052_soleInput_iff t i).2 h⟩ hn
    · exact ⟨_, rfl⟩
  · have hm3 : core052_newest core052_fAll (qDelivered core052_M2 core052_fAll) =
        .ok [(1, 8), (2, 8)] := by decide
    rcases (h core052_fAll (qDelivered core052_M2 core052_fAll)).2.2 0 7 8 []
        core052_fAll_sole (by decide) with ⟨m, hm⟩ | ⟨e, he, hp⟩
    · rw [hm3] at hm; cases hm
    · rw [hm3] at he; cases he
      exact absurd (hp 1) (by decide)

/-! ## Consequence with CORE-050 and IO-015 (the Note) -/

/-- **Fork on a choice never ends a firing.** For every fork satisfying CORE-052 and every
transition with a sole input place `i` and the output spec `Xor(Place a, Place b)`, `a ≠ b`: with
one token delivered from `i`, the fork writes both `a` and `b`, so its emission fills no output
branch and no reference action firing ends with the fork action. -/
theorem core052_xor_never_fires {N T V : Type} [DecidableEq N] {val : T → V}
    {Fork : ActionFn N T} (h : CORE_052 val Fork) {t : Trans N} {i a b : N}
    (hi : core052_soleInput t i) (ho : t.out = some (.xor (.place a) (.place b))) (hab : a ≠ b)
    {M M' : QueueMarking N T} {δ : Delivered N T} {x : T} {e : List (N × T)}
    (hx : δ.inputs i = [x]) :
    ¬ refActionFire (ActionFn.rel Fork) t M δ e M' := by
  rintro ⟨-, hb, ha⟩
  obtain ⟨e0, he0, hp⟩ := (h t δ).1 i x hi hx
  have he : e = e0 := Except.ok.inj (ha.symm.trans he0)
  subst he
  have hoa : OutputArc t a := ⟨_, ho, by simp [outPlaces]⟩
  have hob : OutputArc t b := ⟨_, ho, by simp [outPlaces]⟩
  have h1 := hp a
  have h2 := hp b
  rw [if_pos hoa] at h1
  rw [if_pos hob] at h2
  have hne : ∀ q, (EmittedTo e q).map val = [val x] → q ∈ e.map Prod.fst := by
    intro q hq
    by_contra hn
    rw [core052_emittedTo_nil hn] at hq
    cases hq
  have m1 := hne a h1
  have m2 := hne b h2
  have hb' : e.map Prod.fst ∈ (Out.xor (.place a) (.place b)).branches := by
    unfold OutputBranch at hb
    rw [ho] at hb
    exact hb
  simp only [Out.branches, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hb'
  rcases hb' with hb' | hb' <;> rw [hb'] at m1 m2 <;> simp at m1 m2
  · exact hab m2.symm
  · exact hab m1

/-- The reference fork on `xor` from a place 0 holding 7: it completes, writing both places, and
no reference action firing ends with it. -/
example : refFork core052_xorT (qDelivered core052_M core052_xorT) = .ok [(1, 7), (2, 7)] ∧
    ∀ e M', ¬ refActionFire (ActionFn.rel refFork) core052_xorT core052_M
      (qDelivered core052_M core052_xorT) e M' :=
  ⟨by decide, fun _ _ => core052_xor_never_fires (i := 0) (x := 7) (CORE_052_reference (id : Nat → Nat))
    ((core052_soleInput_iff _ _).2 (by decide)) rfl (by decide) (by decide)⟩

end Libpetri.Spec
