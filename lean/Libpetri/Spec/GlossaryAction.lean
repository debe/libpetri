import Libpetri.Reference.Build
import Libpetri.Spec.GlossaryQueue
import Libpetri.Spec.Req.IO_013

set_option linter.missingDocs true

/-!
# Glossary: actions

The terms the action requirements use ([CORE-050]–[CORE-054]): what an action is, what it means
for a firing to end with the completion of its action, and how the identity tag of a built
transition (`Act`, `Reference/Build.lean`) names an action. Nothing here defines firing again:

* an action is a relation `ActionRel` from a transition and what the firing delivers to it
  (`Delivered`, [EXEC-010], [EXEC-012]) to how it ends: completing with an emission (places and
  tokens, in emission order) or failing with a message;
* an action firing relation `AF : ActFireRel N T` gives, for every action `a`, the queue firings
  (`QFireRel`) that end with the completion of `a`. A plain `QFireRel` cannot carry this: it does
  not record how a firing ended, and a timed-out firing deposits tokens no action produced
  ([IO-013]);
* the reference `refActionFire a` is the reference queue firing `RefQFire` restricted to the
  firings whose emission fills one output branch and that `a` completes with on the delivery. It
  is a restriction of `RefQFire`, not a second firing rule.

The link to the existing witnesses: `refActionFire_refQFire` (an action firing is a queue
firing), `refActionFire_refFire` (counted, it is a reference firing), `refActionFire_iff_choice`
(the reference action firings are exactly the reference queue firings by an `action` choice whose
emission the action completes with), and `refQFire_iff_action_or_timeout` (every reference queue
firing ends with the completion of an action or with the timeout outcome of IO-013's
`refTimeoutOutcomeFire`, and both are queue firings).

The tag `Act` of a built transition is read through `Act.interp I`: the built-in passthrough tag
is the action that completes with no token (`refPassthrough`, [CORE-051]); another tag `other x`
is the action `I x`. `passthrough_never_offered` is the firing-level consequence [CORE-043] rests
on: a transition with an output specification never ends a reference action firing under
passthrough. `outPlaceSet t` is the set of output places, each once, that the fork and transform
actions write to ([CORE-052], [CORE-053]).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

variable {N T A : Type}

/-! ## Actions -/

/-- Glossary: *Action* (spec/glossary.md).

`a t δ r`: the action `a` of transition `t`, handed the delivery `δ`, may end with `r`:
`.ok e` (it completes with the emission `e`, places and tokens in emission order) or `.error msg`
(it fails, [EXEC-030]). A relation, not a function, because an action may read the world: one
delivery may complete in more than one way. -/
abbrev ActionRel (N T : Type) := Trans N → Delivered N T → Except String (List (N × T)) → Prop

/-- An action that reads nothing but what the firing delivers: one way to end per delivery. -/
abbrev ActionFn (N T : Type) := Trans N → Delivered N T → Except String (List (N × T))

/-- An action function as an action relation: it ends only the way the function says. -/
def ActionFn.rel (f : ActionFn N T) : ActionRel N T := fun t δ r => f t δ = r

/-- **The built-in passthrough action** ([CORE-051]): it completes, with no token. -/
def refPassthrough : ActionFn N T := fun _ _ => .ok []

/-- The action an identity tag names: the passthrough tag names `refPassthrough`, and the tag
`other x` names `I x`. `I` is the host's table of its own actions. -/
def _root_.Libpetri.Reference.Act.interp (I : A → ActionRel N T) : Act A → ActionRel N T
  | .passthrough => refPassthrough.rel
  | .other x => I x

/-- The passthrough tag names the action that completes with no token and never fails, whatever
the table of other actions. -/
theorem interp_passthrough (I : A → ActionRel N T) (t : Trans N) (δ : Delivered N T)
    (r : Except String (List (N × T))) :
    Act.interp I .passthrough t δ r ↔ r = .ok [] :=
  ⟨fun h => h.symm, fun h => h.symm⟩

/-- **Is passthrough** ([CORE-051], [CORE-043]): the tag is the built-in passthrough action.
Identity on the tag, not behaviour: a hand-written action that completes with no token is not
passthrough. -/
def IsPassthrough (x : Act A) : Prop := x = .passthrough

instance [DecidableEq A] (x : Act A) : Decidable (IsPassthrough x) :=
  inferInstanceAs (Decidable (x = .passthrough))

/-- **Unit token** ([CORE-012], [CORE-003]): a token without a value, read through the value
projection `val` (the `val` of CORE-003's block). -/
def IsUnitToken {V : Type} (val : T → Option V) (x : T) : Prop := val x = none

/-! ## Firings that end with the action -/

/-- An action firing relation: `AF a t M δ e M'` says that `t` fires from the queue marking `M`
under the action `a`, delivers `δ` to it, and ends with the completion of `a`, which emitted `e`;
the firing leaves `M'`. `AF a` holds a tuple only if `a` completes with its emission on its
delivery (CORE-050 line 2), so the firing of an action that only fails ([EXEC-030]) or never
completes is in no `AF a`. A tuple does not record how the firing ended: the child of a Timeout
node is also an action branch, so the tuple of a firing that ended with the timeout outcome
([IO-013]) is in `AF a` whenever `a` can complete with the same emission
(`core050_timeout_overlap`). -/
abbrev ActFireRel (N T : Type) := ActionRel N T → QFireRel N T

/-- **The reference action firing**: a reference queue firing (`RefQFire`) whose emission fills
one output branch (glossary: Output branch) and that the action completes with on what the firing
delivered. -/
def refActionFire [DecidableEq N] : ActFireRel N T := fun a t M δ e M' =>
  RefQFire t M δ e M' ∧ OutputBranch t (e.map Prod.fst) ∧ a t δ (.ok e)

/- The reference action firing is the witness model of the action blocks. -/
#spec_witness refActionFire

/-- **Ends with its action or its timeout outcome** ([CORE-050], [IO-013]): every queue firing
of `Q` is a firing of `AF` under some action, or, counted, a firing of `TO`, the firings that end
with the timeout outcome. A cover, not a partition: a tuple can be both (see `ActFireRel`). -/
def EndsByActionOrTimeout [DecidableEq N] (Q : QFireRel N T) (AF : ActFireRel N T)
    (TO : FireRel N) : Prop :=
  ∀ t M δ e M', Q t M δ e M' →
    (∃ a, AF a t M δ e M') ∨ TO t (Counts M) (e.map Prod.fst) (Counts M')

/-- **Tag firing**: the firings of the definition `d` of a built transition that end with the
completion of the action its tag names, under the table `I`. -/
def TagFire (AF : ActFireRel N T) (I : A → ActionRel N T) (d : TransDef N A) :
    QueueMarking N T → Delivered N T → List (N × T) → QueueMarking N T → Prop :=
  AF (Act.interp I d.action) d.toTrans

/-! ## Bridge lemmas -/

/-- An output branch is exactly a deposit the output specification offers by an `action`
choice, whatever the firing consumed. -/
theorem outputBranch_iff_action (t : Trans N) (c : N → Nat) (d : List N) :
    OutputBranch t d ↔ ∃ i, deposit c (OutputSpec t) (.action i) = some d := by
  unfold OutputBranch OutputSpec
  cases t.out with
  | none =>
    constructor
    · rintro rfl; exact ⟨0, rfl⟩
    · rintro ⟨i, hi⟩
      cases i with
      | zero => exact (Option.some.inj hi).symm
      | succ n => simp [deposit] at hi
  | some o =>
    simp only [deposit]
    exact List.mem_iff_getElem?

/-- Every output branch of an output specification names at least one place. -/
theorem outBranches_ne_nil : ∀ (o : Out N), ∀ b ∈ o.branches, b ≠ []
  | .place _, b, h => by
    simp only [Out.branches, List.mem_singleton] at h
    subst h; simp
  | .forward _ _, b, h => by
    simp only [Out.branches, List.mem_singleton] at h
    subst h; simp
  | .and l r, b, h => by
    simp only [Out.branches, cross, List.mem_flatMap, List.mem_map] at h
    obtain ⟨x, hx, y, -, rfl⟩ := h
    simp [outBranches_ne_nil l x hx]
  | .xor l r, b, h => by
    simp only [Out.branches, List.mem_append] at h
    rcases h with h | h
    · exact outBranches_ne_nil l b h
    · exact outBranches_ne_nil r b h
  | .timeout c, b, h => outBranches_ne_nil c b h

section Bridge

variable [DecidableEq N]

/-- **Link to `RefQFire`**: every reference action firing is a reference queue firing. -/
theorem refActionFire_refQFire {a : ActionRel N T} {t : Trans N} {M M' : QueueMarking N T}
    {δ : Delivered N T} {e : List (N × T)} (h : refActionFire a t M δ e M') :
    RefQFire t M δ e M' :=
  h.1

/-- Counted, every reference action firing is a reference firing whose deposit is the places
of the emission. -/
theorem refActionFire_refFire {a : ActionRel N T} {t : Trans N} {M M' : QueueMarking N T}
    {δ : Delivered N T} {e : List (N × T)} (h : refActionFire a t M δ e M') :
    RefFire t (Counts M) (e.map Prod.fst) (Counts M') :=
  h.1.fires

/-- The reference action firings, in the form of `RefQFire` itself: enabled, an `action` choice
whose deposit is the places of the emission, the reference delivery, the reference result, and
the action completing with the emission on that delivery. -/
theorem refActionFire_iff_choice (a : ActionRel N T) (t : Trans N) (M : QueueMarking N T)
    (δ : Delivered N T) (e : List (N × T)) (M' : QueueMarking N T) :
    refActionFire a t M δ e M' ↔
      Enabled t (Counts M) ∧
        (∃ i, deposit (Consumes t (Counts M)) (OutputSpec t) (.action i) = some (e.map Prod.fst)) ∧
        δ = qDelivered M t ∧ M' = qFire M t e ∧ a t δ (.ok e) := by
  constructor
  · rintro ⟨⟨hen, -, hδ, hM⟩, hb, ha⟩
    exact ⟨hen, (outputBranch_iff_action t _ _).1 hb, hδ, hM, ha⟩
  · rintro ⟨hen, ⟨i, hi⟩, hδ, hM, ha⟩
    exact ⟨⟨hen, ⟨.action i, hi⟩, hδ, hM⟩, (outputBranch_iff_action t _ _).2 ⟨i, hi⟩, ha⟩

/-- **Link to `RefQFire` and IO-013**: a reference queue firing is exactly a reference action
firing under some action, or a firing that, counted, ends with the timeout outcome (IO-013's
`refTimeoutOutcomeFire`) and delivers and leaves what the reference queue firing does. The action
of the first case can be taken as the one that completes with the emission. -/
theorem refQFire_iff_action_or_timeout (t : Trans N) (M : QueueMarking N T) (δ : Delivered N T)
    (e : List (N × T)) (M' : QueueMarking N T) :
    RefQFire t M δ e M' ↔
      (∃ a, refActionFire a t M δ e M') ∨
        (refTimeoutOutcomeFire t (Counts M) (e.map Prod.fst) (Counts M') ∧
          δ = qDelivered M t ∧ M' = qFire M t e) := by
  constructor
  · intro h
    obtain ⟨hen, ⟨ch, hch⟩, hδ, hM⟩ := h
    cases ch with
    | action i =>
      exact .inl ⟨fun _ _ r => r = .ok e, ⟨hen, ⟨.action i, hch⟩, hδ, hM⟩,
        (outputBranch_iff_action t _ _).2 ⟨i, hch⟩, rfl⟩
    | timedOut j =>
      have hf : RefQFire t M δ e M' := ⟨hen, ⟨.timedOut j, hch⟩, hδ, hM⟩
      exact .inr ⟨⟨hen, ⟨j, hch⟩, hf.fires.2.2⟩, hδ, hM⟩
  · rintro (⟨a, h⟩ | ⟨⟨hen, ⟨j, hj⟩, -⟩, hδ, hM⟩)
    · exact h.1
    · exact ⟨hen, ⟨.timedOut j, hj⟩, hδ, hM⟩

/-- The reference queue firing ends with the completion of its action or with its timeout
outcome. -/
theorem refQFire_endsBy :
    EndsByActionOrTimeout (RefQFire (N := N) (T := T)) refActionFire refTimeoutOutcomeFire :=
  fun t M δ e M' h => ((refQFire_iff_action_or_timeout t M δ e M').1 h).imp id (·.1)

/-- **Passthrough is never offered** ([CORE-043], [CORE-051]): a transition with an output
specification never ends a reference action firing under the passthrough tag, since passthrough
completes with no token and every output branch names a place. -/
theorem passthrough_never_offered (I : A → ActionRel N T) {t : Trans N} {o : Out N}
    (ho : OutputSpec t = some o) {M M' : QueueMarking N T} {δ : Delivered N T}
    {e : List (N × T)} : ¬ refActionFire (Act.interp I .passthrough) t M δ e M' := by
  rintro ⟨-, hb, ha⟩
  have he : e = [] := by
    have := (interp_passthrough I t δ _).1 ha
    exact (Except.ok.inj this)
  subst he
  unfold OutputBranch at hb
  rw [show t.out = some o from ho] at hb
  exact outBranches_ne_nil o [] hb rfl

end Bridge

/-! ## The output places, each once

The built-in actions that write to every output place (fork, [CORE-052]; transform, [CORE-053])
walk the set of places the output specification names, each once (Rust's `allowed_outputs`, the
`outputPlaces()` set of Java and TypeScript). -/

section OutSet

variable [DecidableEq N]

/-- The places the output specification of `t` names, each once, in first-occurrence order. -/
def outPlaceSet (t : Trans N) : List N :=
  match t.out with
  | some o => (outPlaces o).eraseDups
  | none => []

/-- `eraseDups` leaves no repetition. -/
theorem eraseDups_nodup (l : List N) : l.eraseDups.Nodup := by
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
    cases l with
    | nil => simp
    | cons a as =>
      rw [List.eraseDups_cons]
      refine List.nodup_cons.2 ⟨?_, ih _ ?_ _ rfl⟩
      · intro hm
        have := List.mem_eraseDups.1 hm
        simp at this
      · subst h
        exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- A place is in `outPlaceSet t` exactly when it is an output place of `t`. -/
theorem mem_outPlaceSet (t : Trans N) (p : N) : p ∈ outPlaceSet t ↔ OutputArc t p := by
  unfold outPlaceSet OutputArc
  cases t.out with
  | none => simp
  | some o => simp [List.mem_eraseDups]

/-- `outPlaceSet t` names each place once. -/
theorem outPlaceSet_nodup (t : Trans N) : (outPlaceSet t).Nodup := by
  unfold outPlaceSet
  cases t.out with
  | none => exact List.nodup_nil
  | some o => exact eraseDups_nodup _

/-- What a concatenation sends to a place is what each part sends there, in order. -/
theorem emittedTo_append (a b : List (N × T)) (p : N) :
    EmittedTo (a ++ b) p = EmittedTo a p ++ EmittedTo b p := by
  simp [EmittedTo, qEmittedTo, List.filter_append]

/-- One token `x` per place of a duplicate-free list: a place of the list receives `x` once, any
other place nothing. -/
theorem emittedTo_map_nodup (l : List N) (hl : l.Nodup) (x : T) (p : N) :
    EmittedTo (l.map (·, x)) p = if p ∈ l then [x] else [] := by
  induction l with
  | nil => simp [EmittedTo, qEmittedTo]
  | cons a as ih =>
    have hnd := List.nodup_cons.1 hl
    have ih' := ih hnd.2
    simp only [EmittedTo, qEmittedTo] at ih' ⊢
    by_cases hap : a = p
    · subst hap
      simp only [List.map_cons, List.filter_cons, decide_true, ↓reduceIte, List.mem_cons, true_or]
      rw [ih']; simp [hnd.1]
    · have hpa : ¬ p = a := fun h => hap h.symm
      simp only [List.map_cons, List.filter_cons, hap, decide_false, List.mem_cons, hpa, false_or]
      exact ih'

/-- One token `x` in every output place of `t`: an output place receives `x` once, any other
place nothing. -/
theorem emittedTo_outPlaceSet (t : Trans N) (x : T) (p : N) :
    EmittedTo ((outPlaceSet t).map (·, x)) p = if OutputArc t p then [x] else [] := by
  rw [emittedTo_map_nodup _ (outPlaceSet_nodup t)]
  by_cases hp : OutputArc t p
  · rw [if_pos ((mem_outPlaceSet t p).2 hp), if_pos hp]
  · rw [if_neg (fun h => hp ((mem_outPlaceSet t p).1 h)), if_neg hp]

end OutSet

end Libpetri.Spec
