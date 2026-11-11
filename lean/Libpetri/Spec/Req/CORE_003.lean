import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryQueue
import Libpetri.Spec.Req.CORE_010

set_option linter.missingDocs true

/-!
# CORE-003: Place type safety (`spec/01-core-model.md`)

Ruling D36 (a): CORE-003 is an assumption (kind A), not a run-time check of the engine. No
runtime checks the type of a token an action emits (Python checks nothing, Rust writes by place
name with a value of any type, TypeScript types the place handle only, Java checks only the
initial marking), and every runtime deposits a unit token into a place of any type on the
timeout outcome. What the engine guarantees is an invariant and an acceptance: if every token of
a marking is compatible with its place and every token a firing deposits is compatible with the
place it is deposited to, every token of the marking after the firing is compatible with its
place, every token the action receives from an input or read place is compatible with that
place, and no firing is refused because the tokens it deposits carry compatible values.

The requirement is a predicate over a net's declared typing and an abstract queue firing
relation `Q : QFireRel N T` (glossary `GlossaryQueue.lean`). The typing is three parameters: the
declared type `ty p` of each place, a value projection `val : T → Option V` and the relation
`HasType : Ty → V → Prop` (a value is of a type). A token is compatible with `p`
(`TokenCompatible`) when every value it carries is of `p`'s declared type, so a token without a
value (the unit token, CORE-012) is compatible with every place. The typing is a parameter, not
quantified inside the statement: a universal typing includes one that gives every place its own
type, which turns the lines into token provenance (CORE-010's subject) and rejects an engine that
moves a token between two places of one type (`CORE_003_everyTyping_rejects_sameTypeMove`).

The evidence: lines 1 to 3 are a corollary of CORE-010 (`core003_lines123_of_CORE_010`) and
line 4 holds of the reference because its deposit check reads only the places, so the reference
queue firing satisfies the block at every typing; three firing relations that deliver or deposit
a token in a place of another type break lines 1 to 3, one each; an engine with a run-time type
table that refuses a compatible deposit breaks line 4; a move between two places of one type is
allowed; the reference itself breaks the reading of line 1 without the deposit premise
(`CORE_003_engine_unchecked`), which is the text's "the engine does not check".
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## Compatibility -/

/-- **Compatible** (CORE-003): token `x` is compatible with place `p` when every value it
carries is of `p`'s declared type `ty p`, `HasType (ty p) v`. A token whose projection is `none`
carries no value (the unit token, CORE-012) and is compatible with every place
(`CORE_003_unit_compatible`). -/
def TokenCompatible {N T Ty V : Type} (ty : N → Ty) (val : T → Option V)
    (HasType : Ty → V → Prop) (p : N) (x : T) : Prop :=
  ∀ v, val x = some v → HasType (ty p) v

/-- Every token of every place of the queue marking `M` is compatible with its place. -/
def CompatibleMarking {N T Ty V : Type} (ty : N → Ty) (val : T → Option V)
    (HasType : Ty → V → Prop) (M : QueueMarking N T) : Prop :=
  ∀ p, ∀ x ∈ M p, TokenCompatible ty val HasType p x

/-- Every token of the deposit `e` is compatible with the place it is deposited to. -/
def CompatibleDeposit {N T Ty V : Type} (ty : N → Ty) (val : T → Option V)
    (HasType : Ty → V → Prop) (e : List (N × T)) : Prop :=
  ∀ y ∈ e, TokenCompatible ty val HasType y.1 y.2

/-! ## CORE-003: Place Type Safety -/

requirement CORE_003
  id "CORE-003"
  title "Place Type Safety"
  kind A
  scope "all executors"
  source verbatim "spec/01-core-model.md"
  quote "A place has a declared token type, and a token is compatible with a place when its value is of that type."
        "A token without a value, the unit token ([CORE-012]), is compatible with every place."
        "The engine does not check the type of a token it deposits or a host adds: the net's author and the host keep an action's outputs, a forwarded token ([IO-014]) and an injected token compatible with their places."
        "*When* a transition fires from a marking in which every token is compatible with its place, nothing else changes the marking between the firing's consumption and its deposit, and every token the firing deposits is compatible with the place it is deposited to, every token a place holds after the firing *shall* be compatible with that place."
        "*When* a transition fires from a marking in which every token is compatible with its place, every token its action receives from one of its input places or read places *shall* be compatible with that place."
        "*When* a transition can fire from a marking and deposit tokens to a list of places, it *shall* also be able to fire from that marking, delivering the same tokens to its action, and deposit to the same places, in the same order, any tokens compatible with them."
        "A firing whose action outputs a token with a compatible value to a place succeeds."
  reading "For a net whose places have the declared types ty (a token is compatible with place p when every value val gives it is of type ty p by HasType; a token without a value is compatible with every place), every transition t with no input arc and read arc on one place (ruling D15), and every firing of t from M that delivers δ, deposits e and leaves M':"
          "if every token of M is compatible with its place and every token of e is compatible with the place it is deposited to, every token of M' is compatible with its place;"
          "if every token of M is compatible with its place, every token δ delivers as consumed from an input place p is compatible with p;"
          "if every token of M is compatible with its place, every token δ delivers as read from a read place p is compatible with p;"
          "for every deposit e' to the same places as e, in the same order, whose every token is compatible with its place, t also fires from M, delivering δ and depositing e'."
  assumes "A firing is one step Q t M δ e M' (glossary: QFireRel): t fires from the queue marking M, delivers δ to its action (the consumed tokens per input place and the read tokens per read place), deposits e (places and tokens, in deposit order; the glossary calls e what the action emits) and leaves M'. T is the token. The net's declared typing is three parameters of the statement, fixed for the net and not quantified inside it: ty p is the declared type of place p, val x the value of token x (none for a token without a value) and HasType τ v says that v is a value of type τ. The reference satisfies the block at every typing (CORE_003_reference)."
          "The typing is a parameter so that the block states type safety and not provenance. Read with every typing quantified inside the statement, the lines would also apply to a typing that gives every place its own type, and would then reject an engine that moves a deposited token between two places of one declared type; the prose allows that engine, and the block does too (CORE_003_allows_sameTypeMove), while the quantified reading rejects it (CORE_003_everyTyping_rejects_sameTypeMove). Provenance is CORE-010's subject."
          "Ruling D36 (a). The first three quoted sentences define compatibility and say who keeps it; they are assumptions on the net's author and the host (kind A), not engine behaviour, and are encoded as TokenCompatible (sentences 1 and 2) and as the deposit premise of line 1 (sentence 3). Sentence 2 is the definition's none case (CORE_003_unit_compatible): a token whose projection is none carries no value to check and meets the deposit premise at any place. It is a definitional sentence; which tokens of T are unit tokens is fixed by val, and no theorem here ties the executor's unit token to it. Whether the deposit of the timeout outcome (IO-013) is a step of Q is the queue model's question (CORE-010's assumes: a timed-out completion is not); where it is, its unit tokens meet the premise of line 1 at every place. Java's Place.accepts reads a null value the same way."
          "Sentence 3 is checked against the reference: the reference deposits whatever the firing deposits, an incompatible token included, so the reading of line 1 without its deposit premise is false of it (CORE_003_engine_unchecked, cited for the sentence). That premise is what the deposit's author owes: an action's emitted outputs (Rust's ctx.output takes a place name and a value of any type; TypeScript and Java type the handle only at compile time; Python checks nothing), a ForwardInput whose from and to places have different types (TypeScript and Rust accept such a pair), and a token a host injects or restores (a host step, not a step of Q). Who supplies such a token is outside the firing relation; the block does not show a ForwardInput separately, since in RefQFire a forwarded token is an entry of e like any output."
          "The first EARS sentence is line 1. It is scoped, as CORE-010's first two sentences are, to a firing with nothing else changing the marking between its consumption and its deposit: an asynchronous action's outputs are deposited when its completion is processed, in a later cycle, and a host may inject a token in between. Each part keeps the invariant on its own (consumption removes tokens, a deposit of compatible tokens adds compatible ones), but the interleaved form is a property of the executor model (RefExec, W5), not of one step of Q; no block cited here covers it yet."
          "The second EARS sentence is lines 2 and 3, split by arc kind so that δ.inputs is consulted only at input places and δ.reads only at read places. It is why an action's typed read of its input succeeds when the marking is compatible (Rust's input::<T> downcast, CORE-060). A correlated input of a match specification (NU-020) delivers tokens of its own place too, so the sentence needs no exception; Reference.Trans carries no match specification (ruling D30). What δ holds under a place that is neither an input nor a read place of t is not constrained, as in CORE-010's lines 4 and 5: the sentence speaks only of tokens received from input and read places, and an action asking for an undeclared input place is CORE-060 AC4's error case (RefCtx, W3)."
          "The third EARS sentence is line 4, and AC1 (a firing whose action outputs a token with a compatible value to a place succeeds) is line 4 with line 1: whatever tokens a firing deposits, the same firing with compatible tokens to the same places is a step too, and it keeps a compatible marking compatible. Line 4 kills an engine with a run-time type table that refuses a compatible deposit (CORE_003_forbids_refuseCompatible); lines 1 to 3 accept that engine, since it is a sub-relation of the reference (CORE_003_mutant_noLine4_killed_refuseCompatible). Line 4 asks nothing of an incompatible deposit: whether an engine may refuse one is not CORE-003's, and an engine that checks types at run time satisfies it."
          "Every line is stated for transitions satisfying NoInputRead (ruling D15), as CORE-010's lines are: lines 1 to 3 are a corollary of CORE-010 (core003_lines123_of_CORE_010), line 1 from CORE-010 line 1 (every token after the firing was held by the place or deposited there) and lines 2 and 3 from CORE-010 lines 4 and 5 (every delivered token was held by its place). A transition with an input arc and a read arc on one place is rejected when it is built (EXEC-012) and never fires, so the EARS sentences, which carry no such premise, say nothing more than the lines about a transition that can fire."
          "Each of lines 1 to 3 has a firing relation that breaks it from a compatible marking with a compatible deposit: an engine that puts a deposited token in a place of another type than the one it is deposited to (CORE_003_forbids_misroute, line 1), and an action handed an input token (CORE_003_forbids_inputElsewhere, line 2) or a read token (CORE_003_forbids_readElsewhere, line 3) taken from a place of another type. The deposit premise of line 1 is load-bearing in the other direction: the reading without it is stronger and false of the reference (CORE_003_engine_unchecked), so no relation separates it from line 1 as a mutant would."
          "Like most on … shall lines, lines 1 to 3 hold of the relation that takes no step; line 4 does too, since it only extends steps Q takes. The coverage conjunct QCovers Q F of the queue consistency theorem rules out the empty relation, as for CORE-010."
          "The fourth and fifth sentences of the description and AC2 are not encoded. The fourth (an implementation that keeps a run-time token type for each place rejects an initial marking that puts a token with an incompatible value in a place) and AC2 are Java's Marking.from check, run when either Java executor is built. The initial marking is CORE-072's Init, over token counts, so no step relation here sees the token's value: the check is tested, not encoded (kind Q), and it is not part of the block's scope. Java does not check later deposits (Marking.addToken, ctx.output) at run time. The fifth (a compiler rejects a token of another type where an API call takes a typed place handle) is API shape: compile-time typing is not claimed (ruling D36 (a)), and whether the typed API surfaces bind the Python binding is open ruling D99 and is not relied on."
          "The test derivation (a transition outputs an integer token to an Integer place and succeeds; in Java an initial marking with a string token is rejected) is AC1 and AC2; CORE_003_nonvacuous fires the reference with the compatible deposit of 30 to place 2."
  signoff "pending"
  statement : ∀ {N T Ty V : Type} [DecidableEq N], (N → Ty) → (T → Option V) →
      (Ty → V → Prop) → QFireRel N T → Prop :=
    fun ty val HasType Q => ∀ t, NoInputRead t →
      (∀ δ e, on (fun M M' => Q t M δ e M'), shall (fun M M' =>
        CompatibleMarking ty val HasType M → CompatibleDeposit ty val HasType e →
          CompatibleMarking ty val HasType M')) ∧
      (∀ δ e, on (fun M M' => Q t M δ e M'), shall (fun M _ =>
        CompatibleMarking ty val HasType M →
          ∀ p ∈ inPlaces t, ∀ x ∈ δ.inputs p, TokenCompatible ty val HasType p x)) ∧
      (∀ δ e, on (fun M M' => Q t M δ e M'), shall (fun M _ =>
        CompatibleMarking ty val HasType M →
          ∀ p, ReadArc t p → ∀ x ∈ δ.reads p, TokenCompatible ty val HasType p x)) ∧
      (∀ δ e e', on (fun M M' => Q t M δ e M'), shall (fun M _ =>
        e'.map Prod.fst = e.map Prod.fst → CompatibleDeposit ty val HasType e' →
          ∃ M'', Q t M δ e' M''))

/- The pinned readable form of CORE-003: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CORE_003 : {N T Ty V : Type} →
  [DecidableEq N] → (N → Ty) → (T → Option V) → (Ty → V → Prop) → QFireRel N T → Prop :=
fun {N T Ty V} [DecidableEq N] ty val HasType Q =>
  ∀ (t : Reference.Trans N),
    NoInputRead t →
      (∀ (δ : Delivered N T) (e : List (N × T)),
          on fun M M' => Q t M δ e M', shall fun M M' =>
            CompatibleMarking ty val HasType M →
              CompatibleDeposit ty val HasType e → CompatibleMarking ty val HasType M') ∧
        (∀ (δ : Delivered N T) (e : List (N × T)),
            on fun M M' => Q t M δ e M', shall fun M x =>
              CompatibleMarking ty val HasType M →
                ∀ p ∈ inPlaces t, ∀ x ∈ δ.inputs p, TokenCompatible ty val HasType p x) ∧
          (∀ (δ : Delivered N T) (e : List (N × T)),
              on fun M M' => Q t M δ e M', shall fun M x =>
                CompatibleMarking ty val HasType M →
                  ∀ (p : N), ReadArc t p → ∀ x ∈ δ.reads p, TokenCompatible ty val HasType p x) ∧
            ∀ (δ : Delivered N T) (e e' : List (N × T)),
              on fun M M' => Q t M δ e M', shall fun M x =>
                List.map Prod.fst e' = List.map Prod.fst e → CompatibleDeposit ty val HasType e' → ∃ M'', Q t M δ e' M''
-/
#guard_msgs in #print CORE_003

/-- Lines 1 to 3 of CORE-003 alone, without line 4 (the acceptance of a compatible deposit): the
mutant reading `CORE_003_mutant_noLine4_killed_refuseCompatible` is checked against. -/
def CORE_003_lines123 {N T Ty V : Type} [DecidableEq N] (ty : N → Ty) (val : T → Option V)
    (HasType : Ty → V → Prop) (Q : QFireRel N T) : Prop :=
  ∀ t, NoInputRead t →
    (∀ δ e, on (fun M M' => Q t M δ e M'), shall (fun M M' =>
      CompatibleMarking ty val HasType M → CompatibleDeposit ty val HasType e →
        CompatibleMarking ty val HasType M')) ∧
    (∀ δ e, on (fun M M' => Q t M δ e M'), shall (fun M _ =>
      CompatibleMarking ty val HasType M →
        ∀ p ∈ inPlaces t, ∀ x ∈ δ.inputs p, TokenCompatible ty val HasType p x)) ∧
    (∀ δ e, on (fun M M' => Q t M δ e M'), shall (fun M _ =>
      CompatibleMarking ty val HasType M →
        ∀ p, ReadArc t p → ∀ x ∈ δ.reads p, TokenCompatible ty val HasType p x))

/-! ### The unit clause -/

/-- A token without a value (the unit token, CORE-012) is compatible with every place, whatever
the place's declared type: it carries nothing to check. -/
@[evidence cites "CORE-003" "A token without a value, the unit token ([CORE-012]), is compatible with every place."]
theorem CORE_003_unit_compatible {N T Ty V : Type} (ty : N → Ty) (val : T → Option V)
    (HasType : Ty → V → Prop) (p : N) (x : T) (h : val x = none) :
    TokenCompatible ty val HasType p x := by
  intro v hv
  rw [h] at hv
  exact absurd hv (by simp)

/-! ### Membership in a queue marking after a firing -/

/-- A token the firing deposits at `p` is an entry `(p, x)` of the deposit list. -/
theorem core003_mem_emittedTo {N T : Type} [DecidableEq N] {e : List (N × T)} {p : N} {x : T}
    (h : x ∈ EmittedTo e p) : (p, x) ∈ e := by
  simp only [EmittedTo, qEmittedTo, List.mem_map, List.mem_filter, decide_eq_true_eq] at h
  obtain ⟨y, ⟨hy, rfl⟩, rfl⟩ := h
  exact hy

/-- A token of `p` after appending the deposit `es` to `B` was a token of `p` in `B` or an
entry `(p, x)` of `es`. -/
theorem core003_mem_qAppend {N T : Type} [DecidableEq N] {B : QueueMarking N T}
    {es : List (N × T)} {p : N} {x : T} (h : x ∈ qAppend B es p) : x ∈ B p ∨ (p, x) ∈ es := by
  induction es generalizing B with
  | nil => exact Or.inl h
  | cons y es ih =>
    rcases ih (B := qAppendOne B y.1 y.2) h with hb | hb
    · simp only [qAppendOne] at hb
      split at hb
      · rename_i hp
        rcases List.mem_append.1 hb with hb | hb
        · exact Or.inl hb
        · rw [List.mem_singleton] at hb
          subst hb hp
          exact Or.inr List.mem_cons_self
      · exact Or.inl hb
    · exact Or.inr (List.mem_cons_of_mem _ hb)

/-- A token of `p` after the consume of a firing of `t` was a token of `p` before it. -/
theorem core003_mem_qConsume {N T : Type} [DecidableEq N] {M : QueueMarking N T} {t : Trans N}
    {p : N} {x : T} (h : x ∈ qConsume M t p) : x ∈ M p := by
  simp only [qConsume, qPostInput] at h
  split at h
  · simp at h
  · exact List.mem_of_mem_drop h

/-! ### Derived from CORE-010, and the reference -/

/-- Derived: every queue firing relation satisfying CORE-010 satisfies lines 1 to 3 of CORE-003
at every typing. Line 1 is CORE-010 line 1 (every token a place holds after the firing was held
by the place or deposited there); lines 2 and 3 are CORE-010 lines 4 and 5 (every delivered
token was held by its place). Type safety needs no check of its own: the engine moves tokens only
within a place or from the deposit. -/
@[evidence cites "CORE-003" "the first two EARS sentences, under ruling D15: every queue firing relation that satisfies CORE-010 keeps a compatible marking compatible under compatible deposits and delivers only compatible tokens, at every declared typing"]
theorem core003_lines123_of_CORE_010 {N T Ty V : Type} [DecidableEq N] {Q : QFireRel N T}
    (h : CORE_010 Q) (ty : N → Ty) (val : T → Option V) (HasType : Ty → V → Prop) :
    CORE_003_lines123 ty val HasType Q := by
  intro t hw
  refine ⟨fun δ e M M' hq hM he p x hx => ?_, fun δ e M M' hq hM p hp x hx => ?_,
    fun δ e M M' hq hM p hp x hx => ?_⟩
  · have hmem := ((h t hw).1 δ e M M' hq p).subset hx
    rcases List.mem_append.1 hmem with hm | hm
    · exact hM p x hm
    · exact he (p, x) (core003_mem_emittedTo hm)
  · exact hM p x (((h t hw).2.2.2.1 δ e M M' hq p hp).subset hx)
  · exact hM p x ((h t hw).2.2.2.2 δ e M M' hq p hp x hx)

/-- Lines 1 to 3 and line 4 make CORE-003. -/
theorem core003_of_lines {N T Ty V : Type} [DecidableEq N] {ty : N → Ty} {val : T → Option V}
    {HasType : Ty → V → Prop} {Q : QFireRel N T} (h : CORE_003_lines123 ty val HasType Q)
    (h4 : ∀ t δ e e' M M', Q t M δ e M' → e'.map Prod.fst = e.map Prod.fst →
      CompatibleDeposit ty val HasType e' → ∃ M'', Q t M δ e' M'') :
    CORE_003 ty val HasType Q := by
  intro t hw
  obtain ⟨h1, h2, h3⟩ := h t hw
  exact ⟨h1, h2, h3, fun δ e e' M M' hq => h4 t δ e e' M M' hq⟩

/-- The reference queue firing satisfies CORE-003 at every declared typing: lines 1 to 3 as the
corollary of its CORE-010 evidence (`CORE_010_reference`), and line 4 because its deposit check
reads only the places of the deposit, so any deposit to the same places, compatible or not, is a
firing too. -/
@[evidence holds CORE_003]
theorem CORE_003_reference {N T Ty V : Type} [DecidableEq N] (ty : N → Ty) (val : T → Option V)
    (HasType : Ty → V → Prop) : CORE_003 ty val HasType (RefQFire (N := N) (T := T)) :=
  core003_of_lines (core003_lines123_of_CORE_010 CORE_010_reference ty val HasType)
    fun t _ _ e' M _ ⟨h1, ⟨ch, h2⟩, h3, _⟩ heq _ =>
      ⟨qFire M t e', h1, ⟨ch, by rw [heq]; exact h2⟩, h3, rfl⟩

/-! ### The engine does not check -/

/-- The reading of line 1 without the deposit premise: every firing from a compatible marking
leaves a compatible marking, whatever it deposits. -/
def CORE_003_bare {N T Ty V : Type} [DecidableEq N] (ty : N → Ty) (val : T → Option V)
    (HasType : Ty → V → Prop) (Q : QFireRel N T) : Prop :=
  ∀ t δ e M M', Q t M δ e M' →
    CompatibleMarking ty val HasType M → CompatibleMarking ty val HasType M'

/-! ### Examples

Tokens are `Option Nat`, the projection is the identity (`none` is the unit token), a place's
declared type is its own number (`ty = id`) and type `p` takes the values `v` with
`v / 10 = p + 1`: place `0` takes 10 to 19, place `1` 20 to 29, place `2` 30 to 39, and so on.
The transition is `qexT .one`: an input on `0`, a read and a reset on `1`, output place `2`. -/

/-- The value-of-type relation of the examples: type `p` takes the values `10 * (p + 1)` to
`10 * (p + 1) + 9`. -/
def core003_has (p v : Nat) : Prop := v / 10 = p + 1

instance (p v : Nat) : Decidable (core003_has p v) := inferInstanceAs (Decidable (v / 10 = p + 1))

/-- Compatibility of the examples as a test: no value, or a value of the place's type. -/
def core003_compatB (p : Nat) : Option Nat → Bool
  | none => true
  | some w => w / 10 == p + 1

/-- With the identity typing and projection, compatibility is the test `core003_compatB`. -/
theorem core003_compat_iff (p : Nat) (x : Option Nat) :
    TokenCompatible (id : Nat → Nat) (id : Option Nat → Option Nat) core003_has p x ↔
      core003_compatB p x = true := by
  cases x with
  | none => simp [TokenCompatible, core003_compatB]
  | some w => simp [TokenCompatible, core003_compatB, core003_has]

instance (p : Nat) (x : Option Nat) :
    Decidable (TokenCompatible (id : Nat → Nat) (id : Option Nat → Option Nat) core003_has p x) :=
  decidable_of_iff _ (core003_compat_iff p x).symm

/-- The marking of the examples: place `0` holds `10`, a unit token and `12`; place `1` holds
`20` and `21`; every other place is empty. Every token is compatible with its place. -/
def core003_M : QueueMarking Nat (Option Nat) := fun p =>
  if p = 0 then [some 10, none, some 12] else if p = 1 then [some 20, some 21] else []

/-- The deposit of the examples: the token `30` to the output place `2`, compatible with it. -/
def core003_e : List (Nat × Option Nat) := [(2, some 30)]

/-- The example marking is compatible. -/
theorem core003_M_compatible : CompatibleMarking id id core003_has core003_M := by
  intro p
  by_cases h0 : p = 0
  · subst h0; decide
  by_cases h1 : p = 1
  · subst h1; decide
  · simp [core003_M, h0, h1]

/-- The example deposit is compatible. -/
theorem core003_e_compatible : CompatibleDeposit id id core003_has core003_e := by
  unfold CompatibleDeposit
  decide

/-! ### Violation: a deposit in a place of another type -/

/-- A queue firing that is the reference except that every deposited token `(p, x)` lands in
place `f p` instead of `p`, as an engine that resolves a place name to the wrong slot would. -/
def core003_moveQ {N T : Type} [DecidableEq N] (f : N → N) : QFireRel N T := fun t M δ e M' =>
  Enabled t (Counts M) ∧
    (∃ ch, deposit (Consumes t (Counts M)) (OutputSpec t) ch = some (e.map Prod.fst)) ∧
    δ = qDelivered M t ∧ M' = qAppend (qConsume M t) (e.map fun y => (f y.1, y.2))

/-- The misroute of the examples: every deposited token lands in the place after the one it is
deposited to (`p + 1`), whose declared type is another one. -/
def core003_misrouteQ : QFireRel Nat (Option Nat) := core003_moveQ (· + 1)

/-- ✗ Depositing a token in a place of another type than the one it is deposited to violates
CORE-003 (line 1): from the compatible `core003_M`, the compatible deposit of `30` to place `2`
lands in place `3`, which takes 40 to 49. -/
@[evidence forbids CORE_003]
theorem CORE_003_forbids_misroute : ¬ CORE_003 id id core003_has core003_misrouteQ := by
  intro h
  have hq : core003_misrouteQ (qexT .one) core003_M (qDelivered core003_M (qexT .one)) core003_e
      (qAppend (qConsume core003_M (qexT .one)) (core003_e.map fun y => (y.1 + 1, y.2))) :=
    ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩
  have := (h (qexT .one) (by decide)).1 _ _ _ _ hq core003_M_compatible
    core003_e_compatible 3
  revert this
  decide

/-! ### Allowed: a move between two places of one type -/

/-- The move of the examples: a token deposited to place `2` lands in place `3`; every other
deposit lands where it is deposited. -/
def core003_mv (p : Nat) : Nat := if p = 2 then 3 else p

/-- A move that keeps every place's declared type keeps a firing relation type safe: under a
typing with `ty (f p) = ty p` for every `p`, `core003_moveQ f` satisfies CORE-003. -/
theorem core003_moveQ_typeSafe {N T Ty V : Type} [DecidableEq N] (f : N → N) (ty : N → Ty)
    (val : T → Option V) (HasType : Ty → V → Prop) (hf : ∀ p, ty (f p) = ty p) :
    CORE_003 ty val HasType (core003_moveQ (T := T) f) := by
  have href := CORE_003_reference (N := N) (T := T) ty val HasType
  intro t hw
  obtain ⟨_, r2, r3, _⟩ := href t hw
  refine ⟨fun δ e M M' hq hM he p x hx => ?_, fun δ e M M' hq => ?_, fun δ e M M' hq => ?_,
    fun δ e e' M M' hq heq _ => ?_⟩
  · obtain ⟨_, _, _, rfl⟩ := hq
    rcases core003_mem_qAppend hx with hm | hm
    · exact hM p x (core003_mem_qConsume hm)
    · obtain ⟨y, hy, hyx⟩ := List.mem_map.1 hm
      simp only [Prod.mk.injEq] at hyx
      obtain ⟨rfl, rfl⟩ := hyx
      intro v hv
      rw [hf]
      exact he y hy v hv
  · obtain ⟨h1, h2, h3, _⟩ := hq
    exact r2 δ e M (qFire M t e) ⟨h1, h2, h3, rfl⟩
  · obtain ⟨h1, h2, h3, _⟩ := hq
    exact r3 δ e M (qFire M t e) ⟨h1, h2, h3, rfl⟩
  · obtain ⟨h1, ⟨ch, h2⟩, h3, _⟩ := hq
    exact ⟨_, h1, ⟨ch, by rw [heq]; exact h2⟩, h3, rfl⟩

/-- ✓ An engine that moves every token deposited to place `2` into place `3` satisfies CORE-003
when places `2` and `3` have one declared type (`ty p = p / 2`), whatever the projection and the
value-of-type relation: the prose asks type safety, not provenance (CORE-010's subject). -/
@[evidence allows CORE_003]
theorem CORE_003_allows_sameTypeMove {T V : Type} (val : T → Option V)
    (HasType : Nat → V → Prop) :
    CORE_003 (fun p : Nat => p / 2) val HasType (core003_moveQ (T := T) core003_mv) :=
  core003_moveQ_typeSafe _ _ _ _ fun p => by unfold core003_mv; split <;> simp_all

/-- The reading with the typing quantified inside the statement: CORE-003 at every typing. -/
def CORE_003_everyTyping {N T : Type} [DecidableEq N] (Q : QFireRel N T) : Prop :=
  ∀ (Ty V : Type) (ty : N → Ty) (val : T → Option V) (HasType : Ty → V → Prop),
    CORE_003 ty val HasType Q

/-- The reading with every typing quantified inside the statement is provenance, not type
safety: it rejects the move between two places of one type that `CORE_003_allows_sameTypeMove`
lets through, by taking the typing that gives every place its own type and lets place `3` take
no value. -/
theorem CORE_003_everyTyping_rejects_sameTypeMove :
    ¬ CORE_003_everyTyping (core003_moveQ (N := Nat) (T := Option Nat) core003_mv) := by
  intro h
  have hq : core003_moveQ (T := Option Nat) core003_mv (qexT .one) core003_M
      (qDelivered core003_M (qexT .one)) core003_e
      (qAppend (qConsume core003_M (qexT .one)) (core003_e.map fun y => (core003_mv y.1, y.2))) :=
    ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩
  have hM : CompatibleMarking (id : Nat → Nat) (id : Option Nat → Option Nat)
      (fun p (_ : Nat) => p ≠ 3) core003_M := by
    intro p x hx v _
    by_cases h3 : p = 3
    · subst h3; simp [core003_M] at hx
    · exact h3
  have he : CompatibleDeposit (id : Nat → Nat) (id : Option Nat → Option Nat)
      (fun p (_ : Nat) => p ≠ 3) core003_e := by
    intro y hy v _
    simp [core003_e] at hy
    subst hy
    decide
  have hmem : some 30 ∈
      qAppend (qConsume core003_M (qexT .one)) (core003_e.map fun y => (core003_mv y.1, y.2)) 3 := by
    decide
  exact (h Nat Nat id id (fun p _ => p ≠ 3) (qexT .one) (by decide)).1 _ _ _ _ hq hM he 3 _
    hmem 30 rfl rfl

/-! ### Violation: an input token from another place -/

/-- A queue firing that is the reference except that the action receives, from each input place
`p`, as many tokens as the reference consumes but taken from the head of place `p + 1`. -/
def core003_inputElsewhereQ : QFireRel Nat (Option Nat) := fun t M δ e M' =>
  Enabled t (Counts M) ∧
    (∃ ch, deposit (Consumes t (Counts M)) (OutputSpec t) ch = some (e.map Prod.fst)) ∧
    δ = ⟨fun p => (M (p + 1)).take (qInputs M t p).length, qReads M t⟩ ∧ M' = qFire M t e

/-- ✗ Handing the action an input token taken from a place of another type violates CORE-003
(line 2): from the compatible `core003_M`, the action receives `20` as the token consumed from
place `0`, which takes 10 to 19. -/
@[evidence forbids CORE_003]
theorem CORE_003_forbids_inputElsewhere : ¬ CORE_003 id id core003_has core003_inputElsewhereQ := by
  intro h
  have hq : core003_inputElsewhereQ (qexT .one) core003_M
      ⟨fun p => (core003_M (p + 1)).take (qInputs core003_M (qexT .one) p).length,
        qReads core003_M (qexT .one)⟩
      core003_e (qFire core003_M (qexT .one) core003_e) :=
    ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩
  have := (h (qexT .one) (by decide)).2.1 _ _ _ _ hq core003_M_compatible 0 (by decide)
  revert this
  decide

/-! ### Violation: a read token from another place -/

/-- A queue firing that is the reference except that the action receives, for each read place
`p`, as many tokens as the reference reads but taken from the head of place `p - 1`. -/
def core003_readElsewhereQ : QFireRel Nat (Option Nat) := fun t M δ e M' =>
  Enabled t (Counts M) ∧
    (∃ ch, deposit (Consumes t (Counts M)) (OutputSpec t) ch = some (e.map Prod.fst)) ∧
    δ = ⟨qInputs M t, fun p => (M (p - 1)).take (qReads M t p).length⟩ ∧ M' = qFire M t e

/-- ✗ Handing the action a read token taken from a place of another type violates CORE-003
(line 3): from the compatible `core003_M`, the action receives `10` as the token read from
place `1`, which takes 20 to 29. -/
@[evidence forbids CORE_003]
theorem CORE_003_forbids_readElsewhere : ¬ CORE_003 id id core003_has core003_readElsewhereQ := by
  intro h
  have hq : core003_readElsewhereQ (qexT .one) core003_M
      ⟨qInputs core003_M (qexT .one),
        fun p => (core003_M (p - 1)).take (qReads core003_M (qexT .one) p).length⟩
      core003_e (qFire core003_M (qexT .one) core003_e) :=
    ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩
  have := (h (qexT .one) (by decide)).2.2.1 _ _ _ _ hq core003_M_compatible 1 (by decide)
  revert this
  decide

/-! ### Violation: a compatible deposit refused

An engine that keeps a run-time token type per place, like Java's `Place.accepts`, but whose
place-to-type table is off by one: it maps place `p` to the values `10 * p` to `10 * p + 9`
instead of `10 * (p + 1)` to `10 * (p + 1) + 9`, and refuses every firing whose deposit carries
a value its table rejects. Otherwise it is the reference. -/

/-- The off-by-one run-time check: place `p` accepts the unit token and the values with
`w / 10 = p`. -/
def core003_tableAccepts (p : Nat) : Option Nat → Bool
  | none => true
  | some w => w / 10 == p

/-- The reference, restricted to deposits the off-by-one check accepts. -/
def core003_refuseCompatibleQ : QFireRel Nat (Option Nat) := fun t M δ e M' =>
  RefQFire t M δ e M' ∧ ∀ y ∈ e, core003_tableAccepts y.1 y.2 = true

/-- ✗ Refusing a compatible deposit violates CORE-003 (line 4): from `core003_M` the engine fires
`qexT .one` depositing `20` to place `2` (its table accepts it), but has no firing with the
compatible deposit of `30` to place `2`. This is AC1: a firing whose action outputs a token with
a compatible value to a place succeeds. -/
@[evidence forbids CORE_003]
theorem CORE_003_forbids_refuseCompatible :
    ¬ CORE_003 id id core003_has core003_refuseCompatibleQ := by
  intro h
  have hq : core003_refuseCompatibleQ (qexT .one) core003_M (qDelivered core003_M (qexT .one))
      [(2, some 20)] (qFire core003_M (qexT .one) [(2, some 20)]) :=
    ⟨⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩, by decide⟩
  obtain ⟨_, _, hacc⟩ := (h (qexT .one) (by decide)).2.2.2 _ _ core003_e _ _ hq rfl
    core003_e_compatible
  have := hacc (2, some 30) (by simp [core003_e])
  revert this
  decide

/-- ✗ Lines 1 to 3 alone accept the engine that refuses a compatible deposit, since it is a
sub-relation of the reference; line 4 kills it. -/
@[evidence mutant CORE_003]
theorem CORE_003_mutant_noLine4_killed_refuseCompatible :
    CORE_003_lines123 id id core003_has core003_refuseCompatibleQ ∧
      ¬ CORE_003 id id core003_has core003_refuseCompatibleQ := by
  refine ⟨fun t hw => ?_, CORE_003_forbids_refuseCompatible⟩
  obtain ⟨h1, h2, h3, _⟩ := CORE_003_reference (N := Nat) (T := Option Nat) id id core003_has t hw
  exact ⟨fun δ e M M' hq => h1 δ e M M' hq.1, fun δ e M M' hq => h2 δ e M M' hq.1,
    fun δ e M M' hq => h3 δ e M M' hq.1⟩

/-! ### The deposit premise is needed: the engine does not check -/

/-- The reference deposits an incompatible token as readily as a compatible one: from the
compatible `core003_M`, depositing `99` to place `2` (which takes 30 to 39) leaves `99` there.
So the reading of line 1 without its deposit premise (`CORE_003_bare`) is false of the reference
firing: type safety of the marking rests on the deposit's author, not on an engine check. -/
@[evidence cites "CORE-003" "The engine does not check the type of a token it deposits or a host adds: the net's author and the host keep an action's outputs, a forwarded token ([IO-014]) and an injected token compatible with their places."]
theorem CORE_003_engine_unchecked :
    ¬ CORE_003_bare id id core003_has (RefQFire (N := Nat) (T := Option Nat)) := by
  intro h
  have hq : RefQFire (qexT .one) core003_M (qDelivered core003_M (qexT .one)) [(2, some 99)]
      (qFire core003_M (qexT .one) [(2, some 99)]) := ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩
  have := h _ _ _ _ _ hq core003_M_compatible 2
  revert this
  decide

/-! ### Every line exercised -/

/-- Every line of CORE-003 is exercised by the reference, firing `qexT .one` from the compatible
`core003_M` with the compatible deposit of `30` to place `2` (AC1): the action receives `10` from
the input place `0` (line 2) and `20` from the read place `1` (line 3), each compatible with its
place, and the marking after the firing is compatible (line 1): place `0` keeps the unit token
(compatible with place `0` though it carries no value, `CORE_003_unit_compatible`) and `12`,
place `2` holds `30`. The same firing deposits the unit token to place `2` as well (line 4: a
deposit to the same place, swapped for the compatible `30`). -/
@[evidence nonvacuous CORE_003]
theorem CORE_003_nonvacuous :
    RefQFire (qexT .one) core003_M (qDelivered core003_M (qexT .one)) core003_e
        (qFire core003_M (qexT .one) core003_e) ∧
      RefQFire (qexT .one) core003_M (qDelivered core003_M (qexT .one)) [(2, none)]
        (qFire core003_M (qexT .one) [(2, none)]) ∧
      NoInputRead (qexT .one) ∧
      CompatibleMarking id id core003_has core003_M ∧
      CompatibleDeposit id id core003_has core003_e ∧
      (qDelivered core003_M (qexT .one)).inputs 0 = [some 10] ∧
      (qDelivered core003_M (qexT .one)).reads 1 = [some 20] ∧
      qFire core003_M (qexT .one) core003_e 0 = [none, some 12] ∧
      qFire core003_M (qexT .one) core003_e 2 = [some 30] ∧
      CompatibleMarking id id core003_has (qFire core003_M (qexT .one) core003_e) :=
  ⟨⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩, ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩, by decide,
    core003_M_compatible, core003_e_compatible, by decide, by decide, by decide, by decide,
    (CORE_003_reference (N := Nat) (T := Option Nat) id id core003_has (qexT .one)
      (by decide)).1 _ _ _ _ ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩ core003_M_compatible
      core003_e_compatible⟩

end Libpetri.Spec
