import Libpetri.Spec.GlossaryAction

set_option linter.missingDocs true

/-!
# Glossary: the transition context

The terms the context requirements use ([CORE-060]–[CORE-063]): what an action can ask its
transition context, and what a call that names a place the transition does not declare returns.
Nothing here defines firing again. A context is a record of accessor functions over what the
firing delivered (`Delivered`, [EXEC-010], [EXEC-012]); the firing, its delivery and its deposit
stay `RefQFire`'s and `refActionFire`'s (`Spec/GlossaryAction.lean`):

* `inputs`, `input`, `inputToken` and `read` take the transition, the delivery and a place, and
  return `none` when the call reports an error, `some` of the answer otherwise;
* `output` takes the transition, the output buffer the action has written so far, a place and
  the values of one call, and returns `none` when the call reports an error, `some` of the new
  buffer otherwise. The single form `output(place, value)` is the call with one value;
* tokens are the queue model's token identities `T`, and their values are read through a value
  projection `value : T → V`, so `inputToken` (the token itself, with its creation timestamp) and
  `input` (its value) are told apart.

The reference context `refCtx value` answers exactly on the places the transition declares, from
the delivery, and appends output calls on output places to the buffer. `Built C t e` says that the
buffer `e` is reachable from the empty buffer by successful output calls; `ThroughCtx C val a`
says that every emission the action `a` completes with is such a buffer, read through `val`.
`ctx_deposits_outputs` is the bridge to [CORE-035] line 1 and [CONC-026] line 2: under a context
whose successful output calls append only entries on output places (`OutputsOnlyDeclared`), an
action that writes through the context deposits only in output places of its transition.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## Contexts -/

/-- **A transition context** ([CORE-060]–[CORE-063]): the accessors an action calls, each a
function of the transition and of what the firing delivered (`Delivered`). `T` is the type of
tokens (with their creation timestamps), `V` the type of values. A result `none` is a call that
reports an error; a result `some x` is a call that answers `x`. -/
structure Ctx (N T V : Type) where
  /-- `inputs(place)`: the values of the tokens the firing consumed from the place. -/
  inputs : Trans N → Delivered N T → N → Option (List V)
  /-- `input(place)`: the value of the single token the firing consumed from the place. -/
  input : Trans N → Delivered N T → N → Option V
  /-- `inputToken(place)`: the token the firing consumed from the place, with its metadata. -/
  inputToken : Trans N → Delivered N T → N → Option T
  /-- `read(place)`: the value of the token a read arc read from the place. -/
  read : Trans N → Delivered N T → N → Option V
  /-- An output call `output(place, values…)`: from the buffer the action has written so far,
  the place and the values of the call, the buffer after the call (places and values, in the
  order written), or `none` when the call reports an error. -/
  output : Trans N → List (N × V) → N → List V → Option (List (N × V))

variable {N T V : Type} [DecidableEq N]

/-- **The reference context.** It answers `inputs`, `input` and `inputToken` on an input place
of the transition only, from the tokens the firing delivered from it: all their values, the value
of the single token when exactly one was delivered (an error otherwise), and the oldest token.
It answers `read` on a read place only, with the value of the first token read there. An output
call on an output place appends one entry per value, in order; on any other place it reports an
error and leaves no entry behind. -/
def refCtx (value : T → V) : Ctx N T V where
  inputs t δ p := if p ∈ inPlaces t then some ((δ.inputs p).map value) else none
  input t δ p :=
    if p ∈ inPlaces t then (match δ.inputs p with | [x] => some (value x) | _ => none) else none
  inputToken t δ p := if p ∈ inPlaces t then (δ.inputs p).head? else none
  read t δ p := if ReadArc t p then ((δ.reads p).head?).map value else none
  output t e p vs := if OutputArc t p then some (e ++ vs.map fun v => (p, v)) else none

/- The reference context is the witness model of the context blocks. -/
#spec_witness refCtx

/-! ## Output through the context -/

/-- **Built through the context**: the buffer `e` is reachable from the empty buffer by output
calls of `C` on the transition `t` that all succeed. -/
inductive Built (C : Ctx N T V) (t : Trans N) : List (N × V) → Prop
  /-- The empty buffer: the action has written nothing yet. -/
  | nil : Built C t []
  /-- One more output call that succeeds. -/
  | call (e e' : List (N × V)) (p : N) (vs : List V) :
      Built C t e → C.output t e p vs = some e' → Built C t e'

/-- **The action writes through the context**: every emission the action `a` completes with is,
read through the value projection `val`, a buffer built by successful output calls of `C`. -/
def ThroughCtx (C : Ctx N T V) (val : T → V) (a : ActionRel N T) : Prop :=
  ∀ t δ e, a t δ (.ok e) → Built C t (e.map fun x => (x.1, val x.2))

/-- **Output calls append only on output places**: a successful output call on `t` keeps the
buffer it was given as a prefix and appends only entries whose place is an output place of `t`
([CORE-062], [CORE-063]). -/
def OutputsOnlyDeclared (C : Ctx N T V) : Prop :=
  ∀ t e p vs e', C.output t e p vs = some e' →
    ∃ l, e' = e ++ l ∧ ∀ x ∈ l, OutputArc t x.1

/-- The reference context's output calls append only on output places. -/
theorem refCtx_outputsOnlyDeclared (value : T → V) :
    OutputsOnlyDeclared (refCtx (N := N) value) := by
  intro t e p vs e' h
  by_cases hp : OutputArc t p
  · simp only [refCtx, hp, if_true, Option.some.injEq] at h
    subst h
    refine ⟨_, rfl, fun x hx => ?_⟩
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
    exact hp
  · simp [refCtx, hp] at h

omit [DecidableEq N] in
/-- A buffer built through a context whose output calls append only on output places names only
output places of the transition. -/
theorem built_outputs {C : Ctx N T V} (h : OutputsOnlyDeclared C) {t : Trans N}
    {e : List (N × V)} (hb : Built C t e) : ∀ x ∈ e, OutputArc t x.1 := by
  induction hb with
  | nil => intro x hx; cases hx
  | call e e' p vs _ hc ih =>
    obtain ⟨l, rfl, hl⟩ := h t e p vs e' hc
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ih x hx
    · exact hl x hx

omit [DecidableEq N] in
/-- **Copies through the context**: under a context whose output call on an output place appends
one entry per value (CORE-062 line 1), a built buffer followed by one entry `(p, v)` for each place
`p` of a list of output places is built too, by one single output call per place. -/
theorem built_append_copies {C : Ctx N T V}
    (hC : ∀ t e p vs, OutputArc t p → C.output t e p vs = some (e ++ vs.map fun v => (p, v)))
    {t : Trans N} {e : List (N × V)} (he : Built C t e) (l : List N)
    (hl : ∀ p ∈ l, OutputArc t p) (v : V) : Built C t (e ++ l.map fun p => (p, v)) := by
  induction l generalizing e with
  | nil => simpa using he
  | cons p ps ih =>
    have h1 : Built C t (e ++ [(p, v)]) :=
      Built.call e _ p [v] he (hC t e p [v] (hl p (List.mem_cons_self ..)))
    have h2 := ih h1 (fun q hq => hl q (List.mem_cons_of_mem _ hq))
    simpa [List.append_assoc] using h2

/-- **Bridge to [CORE-035] line 1 and [CONC-026] line 2**: an action that writes through a
context whose output calls append only on output places deposits, in a reference action firing,
only in output places of its transition. -/
theorem ctx_deposits_outputs {C : Ctx N T V} {val : T → V} {a : ActionRel N T}
    (hC : OutputsOnlyDeclared C) (ha : ThroughCtx C val a) {t : Trans N}
    {M M' : QueueMarking N T} {δ : Delivered N T} {e : List (N × T)}
    (hf : refActionFire a t M δ e M') : ∀ p ∈ e.map Prod.fst, OutputArc t p := by
  intro p hp
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
  exact built_outputs hC (ha t δ e hf.2.2) (x.1, val x.2)
    (List.mem_map.mpr ⟨x, hx, rfl⟩)

end Libpetri.Spec
