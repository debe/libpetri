import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryQueue
import Libpetri.Spec.Text.EXEC_020

set_option linter.missingDocs true

/-!
# EXEC-020: Output token deposition (`spec/04-execution-model.md`)

The requirement is a predicate over an abstract queue firing relation `Q : QFireRel N T`
(glossary `GlossaryQueue.lean`). It says where a firing's deposit goes and in which order: every
place's queue after the firing is some queue the firing left (`base`), followed by the tokens
the action emitted to that place, in emission order; on a place the firing neither consumes
from nor resets, that queue is the one the place held before, unchanged; and on an input place
that is not reset, it is tokens the place held before, in the order it held them. The evidence
theorems check it against the reference queue firing (`RefQFire`), against an executor that
writes several tokens into one claimed place (acceptance criterion 2), and against three mutant
executors: one that deposits at the head of the queue, one that deposits in reverse emission
order, one that reorders the tokens left on an input place it also deposits to, and one whose
deposit replaces the queue of the place it emits to, with one mutant reading per mutant.

Phase 1 has no completion and no admission: a reference queue firing is atomic, its emission is
an offered deposit of the output spec, and so every firing stands for an admitted completion
whose produced tokens pass validation. The sentence on a completion that is not admitted or
fails validation, and acceptance criteria 3 and 4, belong to the executor model of Phase 2
(`RefExec`); the block's assumptions say so.

Like most `on … shall` lines, the block holds of the relation that takes no step at all.
`EXEC_020_joint` shows that the reference satisfies the block together with the two count
guards `QProjectsTo Q RefFire` and `QCovers Q RefFire`, and `exec020_empty_not_covers` that the
relation without steps fails `QCovers`; the joint model of the queue blocks is
`spec_consistent_queue` (`ConsistencyQueue.lean`).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## EXEC-020: Output token deposition -/

requirement EXEC_020
  id "EXEC-020"
  title "Output Token Deposition"
  kind B
  scope "all executors"
  source verbatim "spec/04-execution-model.md"
  covers EXEC_020.s1, EXEC_020.s3
  reading "For every queue firing of Q, of a transition t from the queue marking M, delivering δ, emitting e and leaving M', there is a queue marking base (the queues the firing leaves before its deposit) such that:"
          "every place p holds after the firing the queue base holds at p, followed by the tokens e emits to p, in emission order (AppendedAtTail base M' e p);"
          "on every place p that is neither an input place nor a reset place of t, base holds the queue M held at p;"
          "on every input place p of t that is not a reset place, base holds at p tokens M held at p, in the order M held them (a sublist of M's queue at p)."
  assumes "A queue firing relates a transition, the queue marking it fires from, what it delivers to its action, the tokens the action emits (places and tokens, in the order the action produced them) and the queue marking it leaves (glossary: QFireRel, Queue order). The firing is atomic: the step that starts it deposits its emission."
          "Phase 1 has no completion and no admission. Every firing of the reference queue relation (RefQFire) deposits an emission whose places are an offered deposit of the output spec, so it stands for an admitted completion whose produced tokens pass output validation, which is the trigger of the quoted 'shall' sentence. Which completions the executor admits (not one whose firing ended with its timeout outcome, [EXEC-022] and [IO-013]; not one a stop on a terminal place abandoned, [EXEC-042]; not one an immediate termination abandoned, [ENV-015]; every in-flight one a close waits for, [ENV-013]) is the executor model of Phase 2 (RefExec) and is deferred to it, as is the moment of admission ([EXEC-001] step 1, or the firing pass for a synchronous action)."
          "The sentence 'If the completion of an action is not admitted, or output validation rejects the produced tokens, then the executor shall not deposit any token the action produced at completion.' is deferred to Phase 2: it speaks of completions that are not admitted and of a validation that fails, neither of which is a firing of the atomic Phase 1 relation. The joint model's QProjectsTo Q RefFire excludes every step whose emitted places are not an offered deposit, so at Phase 1 grain no step deposits an emission validation would reject; it is not a line of this block. It does not model the rejected completion itself: a firing that consumes, fails validation and deposits nothing (TransitionFailed, [EXEC-021], [EVT-008]) is not a step of the atomic relation, and neither is a firing of an executor with the validation skip of [CONC-026], which deposits a write that is not an offered deposit. Both are Phase 2 (RefExec)."
          "Tokens an action published before it completed ([IO-015]) are not modelled: the Phase 1 action emits only at the end of the firing. That they are not deposited again and survive a failed or abandoned completion is deferred to Phase 2."
          "Line 1 is the quoted sentences: the emitted tokens are the tail of each queue, in emission order. Lines 2 and 3 say what 'its place's queue' is, the queue the deposit goes after: on a place the firing does not consume from or reset, the tokens already there (line 2); on an input place that is not reset, tokens the place held, kept in queue order (line 3, glossary Queue order: 'The tokens of a place are kept in the order they were added'). Line 3 does not say which tokens the firing consumes: oldest first is [EXEC-010], and a correlated input of a ν-net match ([NU-020], ruling D16) may take other tokens, which also leaves a sublist; the exact queue left is [EXEC-010] and [EXEC-013]. On a reset place base is unconstrained here; [EXEC-013], [CORE-034] and the count guard QProjectsTo Q RefFire make it empty. Without line 3 an executor that reorders the tokens left on an input place it also deposits to would satisfy the block (EXEC_020_mutant_restOrder_killed). Without line 2 an executor whose deposit replaces the queue of a place it emits to, instead of appending after the tokens already there, would satisfy the block with an empty base there (EXEC_020_forbids_overwrite, EXEC_020_mutant_overwrite_killed)."
          "AC1 (an action produces V to P; V appears at the end of P's queue) is line 1 with line 2: the nonvacuous example EXEC_020_nonvacuous deposits 30 to a place already holding 40 and leaves 40 then 30; an executor that leaves only 30 there violates line 2 (EXEC_020_forbids_overwrite)."
          "AC2 (multiple tokens to the same place are added in order) is line 1 for an emission with several tokens to one place. The reference queue firing deposits one token per claimed place on an action outcome (Reference.deposit, as every branch-enumerating analysis, [IO-016]), and the count guard QProjectsTo Q RefFire imposes the same on every Q, so the joint model has no step with two tokens to one place until the projection compares places as a set, as [IO-015] does. AC2 is therefore witnessed outside the joint model, by executors that accept several tokens into one claimed place under that set comparison: the in-order one satisfies EXEC-020 and leaves 40, 30, 31 when 30 then 31 go to a place holding 40 (EXEC_020_allows_several), and the reverse-order one violates it (EXEC_020_forbids_reversed)."
          "AC3 (a completion that is not admitted deposits none of the action's tokens) and AC4 (a completion whose produced tokens fail validation deposits none of them) are the deferred sentence above, Phase 2."
  signoff "2026-11-13 b671259740fe73af ai"
  statement : ∀ {N T : Type} [DecidableEq N], QFireRel N T → Prop :=
    fun Q => ∀ t M δ e M', Q t M δ e M' →
      ∃ base : QueueMarking _ _,
        (∀ p, AppendedAtTail base M' e p) ∧
        (∀ p, p ∉ inPlaces t → ¬ ResetArc t p → base p = M p) ∧
        (∀ p, p ∈ inPlaces t → ¬ ResetArc t p → (base p).Sublist (M p))

/- The pinned readable form of EXEC-020: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EXEC_020 : {N T : Type} → [DecidableEq N] → QFireRel N T → Prop :=
fun {N T} [DecidableEq N] Q =>
  ∀ (t : Reference.Trans N) (M : QueueMarking N T) (δ : Delivered N T) (e : List (N × T)) (M' : QueueMarking N T),
    Q t M δ e M' →
      ∃ base,
        (∀ (p : N), AppendedAtTail base M' e p) ∧
          (∀ p ∉ inPlaces t, ¬ResetArc t p → base p = M p) ∧ ∀ p ∈ inPlaces t, ¬ResetArc t p → (base p).Sublist (M p)
-/
#guard_msgs in #print EXEC_020

/-! ### Lemmas about the reference semantics -/

/-- The reference consume leaves a place the transition neither consumes from nor resets as it
was. -/
theorem exec020_qConsume_untouched {N T : Type} [DecidableEq N] (M : QueueMarking N T)
    {t : Trans N} {p : N} (hi : p ∉ inPlaces t) (hr : ¬ ResetArc t p) : qConsume M t p = M p := by
  have hn : nspecAt t.core p = none := by
    unfold nspecAt
    rw [List.find?_eq_none]
    intro s hs he
    have : s.place = p := by simpa using he
    exact hi (List.mem_map.mpr ⟨s, hs, this⟩)
  have hr' : p ∉ t.core.resets := hr
  simp [qConsume, hr', qPostInput, qTake, nconsumed, hn]

/-- The reference consume leaves on an input place that is not reset the queue without its
consumed prefix, which is a sublist of the queue. -/
theorem exec020_qConsume_sublist {N T : Type} [DecidableEq N] (M : QueueMarking N T)
    (t : Trans N) {p : N} (hr : ¬ ResetArc t p) : (qConsume M t p).Sublist (M p) := by
  have hr' : p ∉ t.core.resets := hr
  simp only [qConsume, hr', if_false, qPostInput]
  exact List.drop_sublist _ _

/-- The reference satisfies EXEC-020: its result is the reference consume (`qConsume`) with the
emission appended one token at a time at the tail (`qAppend_apply`), and the consume leaves a
place without input or reset arc as it was and an input place without reset arc a sublist. -/
@[evidence holds EXEC_020]
theorem EXEC_020_reference {N T : Type} [DecidableEq N] : EXEC_020 (RefQFire (N := N) (T := T)) := by
  intro t M δ e M' h
  refine ⟨qConsume M t, fun p => ?_, fun p hi hr => exec020_qConsume_untouched M hi hr,
    fun p _ hr => exec020_qConsume_sublist M t hr⟩
  rw [AppendedAtTail, h.2.2.2, qFire, qAppend_apply]

/-- The reference satisfies EXEC-020 together with the two count guards of the joint model
(glossary `GlossaryQueue.lean`), which rule out the relation that takes no step. The joint
model of all blocks, `spec_consistent_queue`, conjoins the same three. -/
theorem EXEC_020_joint {N T : Type} [DecidableEq N] :
    EXEC_020 (RefQFire (N := N) (T := T)) ∧ QProjectsTo (RefQFire (N := N) (T := T)) RefFire ∧
      QCovers (RefQFire (N := N) (T := T)) RefFire :=
  ⟨EXEC_020_reference, refQFire_projectsTo, refQFire_covers⟩

/-- The relation that takes no step satisfies EXEC-020 but not the count guard `QCovers`: the
reference fires `qexT .one` from `qexM`. -/
theorem exec020_empty_not_covers :
    EXEC_020 (fun (_ : Trans Nat) (_ : QueueMarking Nat Nat) _ _ _ => False) ∧
      ¬ QCovers (fun (_ : Trans Nat) (_ : QueueMarking Nat Nat) _ _ _ => False) RefFire := by
  refine ⟨fun _ _ _ _ _ h => h.elim, fun h => ?_⟩
  obtain ⟨_, _, h, -⟩ := h _ _ _ _ qex_refQFire.fires
  exact h

/-! ### Examples -/

/-- `qexM` (`Reference/Queue.lean`) with the output place 2 already holding the token 40. -/
def exec020M : QueueMarking Nat Nat :=
  fun p => if p = 0 then [10, 11, 12] else if p = 1 then [20, 21] else if p = 2 then [40] else []

/-- The reference result of `qexT .one` (input `One` on 0, read and reset on 1, output place 2)
fired from `exec020M`, its action emitting `30` to place 2. -/
def exec020_after : QueueMarking Nat Nat := qFire exec020M (qexT .one) [(2, 30)]

/-- A queue firing relation that consumes as the reference does and then builds the result from
the consumed queues and the emission with `f`; its emissions are those `ok` allows. The
reference is `f = qAppend` with `ok` the reference's offered deposits. -/
def exec020_resultFire {N T : Type} [DecidableEq N] (ok : Trans N → QueueMarking N T → List N → Prop)
    (f : QueueMarking N T → List (N × T) → QueueMarking N T) : QFireRel N T :=
  fun t M δ e M' => Enabled t (Counts M) ∧ ok t M (e.map Prod.fst) ∧ δ = qDelivered M t ∧
    M' = f (qConsume M t) e

/-- The reference's offered deposits: an emission whose places are a deposit of the output
spec. -/
def exec020_offered {N T : Type} [DecidableEq N] (t : Trans N) (M : QueueMarking N T)
    (d : List N) : Prop :=
  ∃ ch, deposit (Consumes t (Counts M)) (OutputSpec t) ch = some d

/-- [IO-015]'s set comparison: an emission whose places, as a set, are an offered deposit; an
action may write several tokens into one claimed place. -/
def exec020_offeredAsSet {N T : Type} [DecidableEq N] (t : Trans N) (M : QueueMarking N T)
    (d : List N) : Prop :=
  ∃ ch d', deposit (Consumes t (Counts M)) (OutputSpec t) ch = some d' ∧ ∀ p, p ∈ d ↔ p ∈ d'

/-- **Mutant executor: deposit at the head.** Every emitted token is put in front of the queue,
the emission's tokens in emission order ahead of the tokens already there. Its emissions are the
reference's. -/
def exec020_prependFire {N T : Type} [DecidableEq N] : QFireRel N T :=
  exec020_resultFire exec020_offered fun B e p => EmittedTo e p ++ B p

/-- **Mutant executor: reverse emission order.** The emission goes to the tail, but the tokens
to one place in the reverse of the order the action produced them. Its emissions are those of
[IO-015]'s set comparison, so an action can write two tokens into one claimed place. -/
def exec020_reversedFire {N T : Type} [DecidableEq N] : QFireRel N T :=
  exec020_resultFire exec020_offeredAsSet fun B e p => B p ++ (EmittedTo e p).reverse

/-- Depositing at the head goes unnoticed by the count semantics: every firing of the mutant,
counted, is a reference firing. Only the queue order tells it apart. -/
theorem exec020_prepend_projectsTo {N T : Type} [DecidableEq N] :
    QProjectsTo (exec020_prependFire (N := N) (T := T)) RefFire := by
  rintro t M δ e M' ⟨hen, hok, hδ, rfl⟩
  have href : RefQFire t M δ e (qFire M t e) := ⟨hen, hok, hδ, rfl⟩
  have hc : Counts (fun p => EmittedTo e p ++ qConsume M t p) = Counts (qFire M t e) := by
    funext p
    simp only [Counts, EmittedTo, qCount, qFire, qAppend_apply, List.length_append]
    omega
  rw [hc]
  exact href.fires

/-- No queue `b ++ [30]` is `[30, 40]`. -/
theorem exec020_ne_prepended (b : List Nat) : [30, 40] ≠ b ++ [30] := by
  intro h
  have := congrArg List.getLast? h
  simp at this

/-- No queue `b ++ [30, 31]` is `[40, 31, 30]`. -/
theorem exec020_ne_reversed (b : List Nat) : [40, 31, 30] ≠ b ++ [30, 31] := by
  intro h
  have := congrArg List.getLast? h
  simp at this

/-- ✗ Depositing at the head violates EXEC-020: firing `qexT .one` from `exec020M` with `30`
emitted to place 2 leaves `[30, 40]` there, which no queue followed by `[30]` is. -/
@[evidence forbids EXEC_020]
theorem EXEC_020_forbids_prepend : ¬ EXEC_020 (exec020_prependFire (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨base, hb, -⟩ := h (qexT .one) exec020M _ [(2, 30)] _
    ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩
  have h2 := hb 2
  simp only [AppendedAtTail] at h2
  have hl : EmittedTo [((2 : Nat), (30 : Nat))] 2 ++ qConsume exec020M (qexT .one) 2 = [30, 40] := by
    decide
  have he : EmittedTo [((2 : Nat), (30 : Nat))] 2 = [30] := by decide
  rw [hl, he] at h2
  exact exec020_ne_prepended _ h2

/-- ✗ Depositing in reverse emission order violates EXEC-020: firing `qexT .one` from
`exec020M` with `30` then `31` emitted to place 2 (one claimed place, two tokens, [IO-015])
leaves `[40, 31, 30]` there, which no queue followed by `[30, 31]` is (AC2). -/
@[evidence forbids EXEC_020]
theorem EXEC_020_forbids_reversed : ¬ EXEC_020 (exec020_reversedFire (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨base, hb, -⟩ := h (qexT .one) exec020M _ [(2, 30), (2, 31)] _
    ⟨by decide, ⟨.action 0, [2], rfl, by intro p; simp⟩, rfl, rfl⟩
  have h2 := hb 2
  simp only [AppendedAtTail] at h2
  have hl : qConsume exec020M (qexT .one) 2 ++
      (EmittedTo [((2 : Nat), (30 : Nat)), (2, 31)] 2).reverse = [40, 31, 30] := by
    decide
  have he : EmittedTo [((2 : Nat), (30 : Nat)), (2, 31)] 2 = [30, 31] := by decide
  rw [hl, he] at h2
  exact exec020_ne_reversed _ h2

/-- Mutant reading of EXEC-020: produced tokens go to the head of the queue, ahead of the tokens
already there, in emission order. -/
def EXEC_020_mutant_prepend {N T : Type} [DecidableEq N] (Q : QFireRel N T) : Prop :=
  ∀ t M δ e M', Q t M δ e M' →
    ∃ base : QueueMarking N T,
      (∀ p, M' p = EmittedTo e p ++ base p) ∧
      (∀ p, p ∉ inPlaces t → ¬ ResetArc t p → base p = M p) ∧
      (∀ p, p ∈ inPlaces t → ¬ ResetArc t p → (base p).Sublist (M p))

/-- The head-depositing executor kills the first mutant: it satisfies the mutant reading (with
the reference consume as `base`) but not EXEC-020. -/
@[evidence mutant EXEC_020]
theorem EXEC_020_mutant_prepend_killed :
    EXEC_020_mutant_prepend (exec020_prependFire (N := Nat) (T := Nat)) ∧
      ¬ EXEC_020 (exec020_prependFire (N := Nat) (T := Nat)) := by
  refine ⟨?_, EXEC_020_forbids_prepend⟩
  rintro t M δ e M' ⟨-, -, -, rfl⟩
  exact ⟨qConsume M t, fun _ => rfl, fun p hi hr => exec020_qConsume_untouched M hi hr,
    fun p _ hr => exec020_qConsume_sublist M t hr⟩

/-- Mutant reading of EXEC-020: produced tokens go to the tail of the queue, but the tokens to
one place in the reverse of the order the action produced them. -/
def EXEC_020_mutant_reversed {N T : Type} [DecidableEq N] (Q : QFireRel N T) : Prop :=
  ∀ t M δ e M', Q t M δ e M' →
    ∃ base : QueueMarking N T,
      (∀ p, M' p = base p ++ (EmittedTo e p).reverse) ∧
      (∀ p, p ∉ inPlaces t → ¬ ResetArc t p → base p = M p) ∧
      (∀ p, p ∈ inPlaces t → ¬ ResetArc t p → (base p).Sublist (M p))

/-- The reverse-order executor kills the second mutant: it satisfies the mutant reading (with
the reference consume as `base`) but not EXEC-020. -/
@[evidence mutant EXEC_020]
theorem EXEC_020_mutant_reversed_killed :
    EXEC_020_mutant_reversed (exec020_reversedFire (N := Nat) (T := Nat)) ∧
      ¬ EXEC_020 (exec020_reversedFire (N := Nat) (T := Nat)) := by
  refine ⟨?_, EXEC_020_forbids_reversed⟩
  rintro t M δ e M' ⟨-, -, -, rfl⟩
  exact ⟨qConsume M t, fun _ => rfl, fun p hi hr => exec020_qConsume_untouched M hi hr,
    fun p _ hr => exec020_qConsume_sublist M t hr⟩

/-! ### Acceptance criterion 2: several tokens to one place -/

/-- **In-order executor under [IO-015]'s set comparison.** It consumes as the reference does and
appends the emission at the tail in emission order, as the reference does, but admits every
emission whose places, as a set, are an offered deposit, so an action can write several tokens
into one claimed place. -/
def exec020_severalFire {N T : Type} [DecidableEq N] : QFireRel N T :=
  exec020_resultFire exec020_offeredAsSet qAppend

/-- ✓ Acceptance criterion 2 outside the joint model: the executor that writes several tokens
into one claimed place, in emission order, satisfies EXEC-020; firing `qexT .one` from
`exec020M` with `30` then `31` emitted to place 2, which holds `40`, it leaves `40, 30, 31`
there. -/
@[evidence allows EXEC_020]
theorem EXEC_020_allows_several :
    EXEC_020 (exec020_severalFire (N := Nat) (T := Nat)) ∧
      exec020_severalFire (qexT .one) exec020M (qDelivered exec020M (qexT .one))
        [(2, 30), (2, 31)] (qAppend (qConsume exec020M (qexT .one)) [(2, 30), (2, 31)]) ∧
      qAppend (qConsume exec020M (qexT .one)) [((2 : Nat), (30 : Nat)), (2, 31)] 2 = [40, 30, 31] := by
  refine ⟨?_, ⟨by decide, ⟨.action 0, [2], rfl, by intro p; simp⟩, rfl, rfl⟩, by decide⟩
  rintro t M δ e M' ⟨-, -, -, rfl⟩
  exact ⟨qConsume M t, fun p => by rw [AppendedAtTail, qAppend_apply],
    fun p hi hr => exec020_qConsume_untouched M hi hr, fun p _ hr => exec020_qConsume_sublist M t hr⟩

/-! ### Mutant: the tokens left on an input place lose their order -/

/-- The queue a firing of the third mutant leaves before its deposit: the reference consume,
reversed on an input place the firing also deposits to. -/
def exec020_restReversed {N T : Type} [DecidableEq N] (M : QueueMarking N T) (t : Trans N)
    (e : List (N × T)) : QueueMarking N T :=
  fun p => if p ∈ inPlaces t ∧ EmittedTo e p ≠ [] then (qConsume M t p).reverse else qConsume M t p

/-- **Mutant executor: reorder the tokens left on a self-loop.** It fires exactly when the
reference does, delivers what it delivers and appends the emission at the tail in emission
order, but on an input place it also deposits to it reverses the tokens the consumption left.
Counted, every firing is a reference firing. -/
def exec020_restReversedFire {N T : Type} [DecidableEq N] : QFireRel N T :=
  fun t M δ e M' => RefQFire t M δ e (qFire M t e) ∧
    M' = fun p => exec020_restReversed M t e p ++ EmittedTo e p

/-- A self-loop: input `One` on place 0, output place 0. -/
def exec020_selfT : Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] }
    out := some (.place 0) }

/-- Place 0 holds `1, 2, 3`; every other place is empty. -/
def exec020_selfM : QueueMarking Nat Nat := fun p => if p = 0 then [1, 2, 3] else []

/-- No queue `b ++ [4]` with `b` a sublist of `[1, 2, 3]` is `[3, 2, 4]`. -/
theorem exec020_ne_restReversed (b : List Nat) (hb : b.Sublist [1, 2, 3]) :
    [3, 2, 4] ≠ b ++ [4] := by
  intro h
  have hb' : b = [3, 2] := by
    have := congrArg List.dropLast h
    simpa using this.symm
  subst hb'
  revert hb
  decide

/-- Mutant reading of EXEC-020: lines 1 and 2 only. The tokens a firing leaves on an input
place are unconstrained; the deposit only has to follow them. -/
def EXEC_020_mutant_restOrder {N T : Type} [DecidableEq N] (Q : QFireRel N T) : Prop :=
  ∀ t M δ e M', Q t M δ e M' →
    ∃ base : QueueMarking N T,
      (∀ p, AppendedAtTail base M' e p) ∧
      (∀ p, p ∉ inPlaces t → ¬ ResetArc t p → base p = M p)

/-- The self-loop reordering executor kills the third mutant: it satisfies the mutant reading
(lines 1 and 2) but not EXEC-020. Firing `exec020_selfT` from `exec020_selfM` with `4` emitted
to place 0, it leaves `3, 2, 4` there, where the reference leaves `2, 3, 4`; no sublist of
`1, 2, 3` followed by `4` is `3, 2, 4`. -/
@[evidence mutant EXEC_020]
theorem EXEC_020_mutant_restOrder_killed :
    EXEC_020_mutant_restOrder (exec020_restReversedFire (N := Nat) (T := Nat)) ∧
      ¬ EXEC_020 (exec020_restReversedFire (N := Nat) (T := Nat)) := by
  refine ⟨?_, fun h => ?_⟩
  · rintro t M δ e M' ⟨-, rfl⟩
    refine ⟨exec020_restReversed M t e, fun p => rfl, fun p hi hr => ?_⟩
    simp [exec020_restReversed, hi, exec020_qConsume_untouched M hi hr]
  · obtain ⟨base, hb, -, hs⟩ := h exec020_selfT exec020_selfM _ [(0, 4)] _
      ⟨⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩, rfl⟩
    have h0 := hb 0
    simp only [AppendedAtTail] at h0
    have hl : exec020_restReversed exec020_selfM exec020_selfT [((0 : Nat), (4 : Nat))] 0 ++
        EmittedTo [((0 : Nat), (4 : Nat))] 0 = [3, 2, 4] := by decide
    have he : EmittedTo [((0 : Nat), (4 : Nat))] 0 = [4] := by decide
    have hm : exec020_selfM 0 = [1, 2, 3] := by decide
    rw [hl, he] at h0
    have hs0 := hs 0 (by decide) (by decide)
    rw [hm] at hs0
    exact exec020_ne_restReversed _ hs0 h0

/-! ### Mutant: the deposit replaces the target queue -/

/-- **Mutant executor: overwrite.** It consumes as the reference does, but a place the action
emits to ends holding only the emitted tokens, in emission order, as if the deposit were a put
instead of an append; every other place keeps the consumed queue. Its emissions are the
reference's. -/
def exec020_overwriteFire {N T : Type} [DecidableEq N] : QFireRel N T :=
  exec020_resultFire exec020_offered fun B e p => if EmittedTo e p = [] then B p else EmittedTo e p

/-- ✗ Overwriting the target queue violates EXEC-020 (line 2, AC1): firing `qexT .one` from
`exec020M` with `30` emitted to place 2, which holds `40` and is neither an input nor a reset
place, leaves `[30]` there; line 2 makes the queue before the deposit `[40]`, and `[40]`
followed by `[30]` is not `[30]`. -/
@[evidence forbids EXEC_020]
theorem EXEC_020_forbids_overwrite : ¬ EXEC_020 (exec020_overwriteFire (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨base, hb, h2, -⟩ := h (qexT .one) exec020M _ [(2, 30)] _
    ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩
  have hp := hb 2
  simp only [AppendedAtTail] at hp
  rw [h2 2 (by decide) (by decide)] at hp
  revert hp
  decide

/-- Mutant reading of EXEC-020: lines 1 and 3 only. The queue the deposit goes after is
unconstrained on a place the firing neither consumes from nor resets. -/
def EXEC_020_mutant_overwrite {N T : Type} [DecidableEq N] (Q : QFireRel N T) : Prop :=
  ∀ t M δ e M', Q t M δ e M' →
    ∃ base : QueueMarking N T,
      (∀ p, AppendedAtTail base M' e p) ∧
      (∀ p, p ∈ inPlaces t → ¬ ResetArc t p → (base p).Sublist (M p))

/-- The overwriting executor kills the fourth mutant: it satisfies the mutant reading (with an
empty `base` on the places it emits to and the reference consume elsewhere) but not EXEC-020. -/
@[evidence mutant EXEC_020]
theorem EXEC_020_mutant_overwrite_killed :
    EXEC_020_mutant_overwrite (exec020_overwriteFire (N := Nat) (T := Nat)) ∧
      ¬ EXEC_020 (exec020_overwriteFire (N := Nat) (T := Nat)) := by
  refine ⟨?_, EXEC_020_forbids_overwrite⟩
  rintro t M δ e M' ⟨-, -, -, rfl⟩
  refine ⟨fun p => if EmittedTo e p = [] then qConsume M t p else [], fun p => ?_, fun p _ hr => ?_⟩
  · simp only [AppendedAtTail]
    by_cases h : EmittedTo e p = [] <;> simp [h]
  · by_cases h : EmittedTo e p = []
    · simp only [h, if_true]; exact exec020_qConsume_sublist M t hr
    · simp [h]

/-- The reference leaves `2, 3, 4` in place 0 of the self-loop example. -/
example : qFire exec020_selfM exec020_selfT [(0, 4)] 0 = [2, 3, 4] := by decide

/-- EXEC-020 is exercised by the reference (AC1): `qexT .one` fires from `exec020M`, where its
output place 2 already holds `40`, its action emitting `30` there; the firing leaves `40` then
`30` in place 2, where depositing at the head would leave `30` then `40`. -/
@[evidence nonvacuous EXEC_020]
theorem EXEC_020_nonvacuous :
    RefQFire (qexT .one) exec020M (qDelivered exec020M (qexT .one)) [(2, 30)] exec020_after ∧
      exec020M 2 = [40] ∧ exec020_after 2 = [40, 30] ∧
      exec020_after 2 ≠ EmittedTo [((2 : Nat), (30 : Nat))] 2 ++ exec020M 2 := by
  refine ⟨⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩, by decide, by decide, by decide⟩

end Libpetri.Spec
