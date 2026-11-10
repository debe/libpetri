import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryQueue
import Libpetri.Spec.Req.EXEC_010
import Libpetri.Spec.Req.EXEC_012
import Libpetri.Spec.Req.EXEC_013
import Libpetri.Spec.Req.EXEC_020

set_option linter.missingDocs true

/-!
# CORE-010: Token immutability (`spec/01-core-model.md`)

The engine never rewrites a token. Every token a place holds after a firing is a token it held
before or a token the action emitted there, with no extra copies; every token a place held and
the firing neither consumed nor cleared is still there; every token the action receives from an
input place or a read place is a token that place held, and no consumed token is received twice.
The requirement is a predicate over an abstract queue firing relation `Q : QFireRel N T`
(glossary `GlossaryQueue.lean`), where `T` is the token itself (its value and its creation
timestamp), so that a changed value or a changed timestamp is a different element of `T`.

Tokens are compared as multisets (`List.Subperm`), not only by membership: a membership-only
reading accepts a firing that re-stamps a kept token onto a timestamp another held token already
has (unit tokens), that re-stamps a place's tokens and reports the new copies as emitted, or that
hands the action the head token twice. The conservation lines (2 and 3) close the gap left by
the emission `e` being a parameter of the step: whatever `e` lists, the tokens a place held and
the firing did not consume or clear must still be there, unchanged.

The evidence checks the statement against the reference queue firing (`RefQFire`), against
seven firing relations that change a token and one that copies a kept token, and against three
mutant readings (only the value immutable; membership instead of multiplicity, which accepts
four of the seven; line 1 alone by membership, which accepts the copy that lines 2 and 3 let
through). Under ruling D15 the block
is a corollary of EXEC-010, EXEC-012, EXEC-013 and EXEC-020 (`CORE_010_of_EXEC`).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## CORE-010: Token immutability -/

requirement CORE_010
  id "CORE-010"
  title "Token Immutability"
  kind B
  scope "all executors"
  source verbatim "spec/01-core-model.md"
  quote "A token is an immutable value object consisting of a typed payload value and a creation timestamp."
        "Once created, neither the value nor the timestamp can be modified."
        "*When* a transition fires and nothing else changes the marking between the firing's consumption and its deposit, every token a place holds after the firing *shall* be a token the place held before the firing, with the same value and creation timestamp, or a token the action emitted to that place, and the firing *shall* not duplicate any of these tokens."
        "*When* a transition fires and nothing else changes the marking between the firing's consumption and its deposit, every token that a place without a reset arc of the transition held before the firing *shall* still be in that place after the firing, with the same value and creation timestamp, unless the action received it from that place as a consumed input."
        "*When* a transition fires, every token its action receives from one of its input places or read places *shall* be a token that place held before the firing, with the same value and creation timestamp, and the action *shall* not receive a consumed token more often than its input place held it."
  reading "For every transition t with no input arc and read arc on one place (ruling D15), every firing of t from M that delivers δ, emits e and leaves M':"
          "every place p ends holding a sub-multiset of its tokens in M followed by the tokens e sends to p;"
          "every place p that is neither an input place nor a reset place of t still holds every token it held in M, with multiplicity;"
          "every input place p of t that is not a reset place holds every token it held in M, with multiplicity, apart from the tokens δ delivers as consumed from p;"
          "the tokens δ delivers as consumed from an input place p are a sub-multiset of the tokens p held in M;"
          "every token δ delivers as read from a read place p is a token p held in M."
  assumes "A firing is one step Q t M δ e M' (glossary: QFireRel): t fires from the queue marking M, delivers δ to its action (the consumed tokens per input place and the read tokens per read place), the action emits e (places and tokens, in emission order) and the firing leaves M'. T is the token itself, its value and its creation timestamp together, so 'the same value and creation timestamp' is equality in T, 'a token the place held' is membership in the place's queue and 'duplicate' or 'more often' compares occurrence counts (List.Subperm: every token occurs at most as often on the left as on the right)."
          "The firing is atomic, as one step of Q is: the first two EARS sentences are scoped to a firing with nothing else changing the marking between its consumption and its deposit. In all three runtimes an asynchronous action's outputs are deposited when its completion is processed, in a later cycle than the consumption (Java BitmapNetExecutor fireTransition and its completion handler; Rust and TypeScript alike), and other firings and injected tokens can change the marking in between, so after such a firing a place need not hold the tokens it held when the firing consumed. The third EARS sentence is local to the consumption and needs no scope. The same property for interleaved firings (each firing takes the head of its input places when it starts and appends at the tail when it completes) is stated locally by EXEC-010 and EXEC-020; over the executor cycle it is the companion of the executor model (RefExec, W5)."
          "The first quoted sentence is the definition the statement is read against: a token is its value and its creation timestamp, compared by content (a value object), which is equality in T. The 'typed payload' (a value of the place's token type) is CORE-001's and IO-006's subject and is not encoded; T is one abstract type for every place."
          "The second quoted sentence is read at the engine seam, as the three EARS sentences restate it: the engine never rewrites, drops or copies a token it holds or moves. The same property at other seams belongs to their IDs: a Forward keeps the consumed token's value and timestamp (IO-014 AC5, below RefQFire), a restore keeps both (CORE-073 AC1), and tokens an action publishes before it completes (IO-015) are deposited outside a single firing (RefExec, Phase 2). An action or user code mutating a token object, deep immutability of the payload (a Java record holding a mutable object, a Rust Arc<T> with interior mutability) and runtime freezing in TypeScript are API shape (AC3), not claimed here."
          "e is the emission of a completion the executor processed and output validation accepted ([EXEC-020], [EXEC-021], ruling D17); a discarded, timed-out, stopped or failed completion is not a step of Q. The tokens of e are new tokens the action created, so the block says nothing about their values or timestamps (CORE-011's subject). Because e is a parameter of the step, line 1 alone accepts a relation that re-stamps a place's tokens and lists the new copies in e; lines 2 and 3 kill it whatever e lists, since the original tokens must still be there (CORE_010_forbids_launder)."
          "Every line is stated for transitions satisfying NoInputRead (ruling D15): a transition with an input arc and a read arc on one place is rejected when it is built (EXEC-012) and never fires, so the EARS sentences, which carry no such premise, say nothing more than the lines about any transition that can fire. The reference meets the lines without that premise too; the premise is there so that the block is exactly a corollary of the signed EXEC blocks, which carry it."
          "Derived: under D15, the lines follow from EXEC-020 (every place keeps a base followed by its emitted tokens; a place without an input arc and a reset arc keeps its queue as base, an input place that is not a reset place a sublist of it), EXEC-013 line 1 (a reset place holds exactly its emitted tokens), EXEC-010 line 1 (an input place that is not a reset place ends as a permutation of its queue after the consumed prefix followed by its emitted tokens), EXEC-010 line 2 (the delivered inputs are the FIFO prefix) and EXEC-012 line 1 (every read token is the head of the place), by CORE_010_of_EXEC. Every relation the forbids theorems here reject is therefore also rejected by one of those blocks; the block adds the link from the CORE-010 prose, not a new constraint."
          "Line 1 is the first EARS sentence. A firing that re-stamps the tokens a place keeps onto pairs the place did not hold is killed by it (CORE_010_forbids_restamp; lines 2 and 3 kill it too). A firing that keeps every token and adds one more copy of a kept token is killed by line 1 alone (CORE_010_forbids_dup): lines 2 and 3 ask only that the held tokens stay, so its 'shall not duplicate' half is line 1's, and a reading of line 1 by membership accepts the copy (CORE_010_mutant_line1Membership_killed_dup). Order is not compared: that the kept tokens are the queue after the consumed prefix, in order, is EXEC-010's and EXEC-020's."
          "Lines 2 and 3 are the second EARS sentence, split by whether the place is an input place, so that δ.inputs is consulted only where t has an input arc. They catch a rewrite that line 1 cannot see because the new token equals another held or emitted token: unit tokens (CORE-012) whose value ring and timestamp ring run out of step (CORE_010_forbids_desync, line 3), a place that stamps every token with its last arrival so that a held token becomes a copy of the emitted one (CORE_010_forbids_lastArrival, line 2), and the laundering relation above (CORE_010_forbids_launder, line 2)."
          "Lines 4 and 5 are the third EARS sentence, split by arc kind: line 4 for input places, line 5 for read places. An altered copy handed over as an input (CORE_010_forbids_alteredInput) or as a read (CORE_010_forbids_alteredRead) is killed, and so is an action that receives the head token k times for an exactly(k) input (CORE_010_forbids_headTwice, line 4). Line 5 is membership only: a read arc delivers the head once per arc, so a place read by two arcs legitimately hands over one token twice (qReadsBag); the read multiplicity is EXEC-012's. Both lines are restricted to the input places and the read places of t: what an action receives from a place that is neither is not constrained here, as in EXEC-010 and EXEC-013, because the spec has no shall sentence on it."
          "'neither the value nor the timestamp': a reading under which only the value is immutable accepts a firing that keeps every value and re-stamps the kept tokens; CORE-010 kills it (CORE_010_mutant_valueOnly_killed). A reading by membership instead of multiplicity accepts the laundering, desync, last-arrival and head-twice relations; CORE-010 kills each (CORE_010_mutant_membership_killed_*)."
          "Like most on … shall lines, the lines hold of the relation that takes no step; the coverage conjunct QCovers Q F of the queue consistency theorem rules that out (exec020_empty_not_covers)."
          "AC1 (token value accessible after creation and matching the original) is read at the engine seam as lines 1 to 5: a token the action receives, or a place keeps, is the token as created, value included (CORE_010_nonvacuous: the action receives (10, 0) and (20, 3), place 0 keeps (11, 1) and (12, 2), place 2 keeps (40, 5)). The accessor itself is API shape, checked by tests, not encoded."
          "AC2 (token timestamp accessible after creation) is API shape: an accessor exists in every language with a token object. It is checked by tests and not encoded; that the timestamp a kept or delivered token carries is its original one is lines 1 to 5."
          "AC3 (no API to mutate token fields after creation) is API shape (kind Q in the plan): checked by tests and by each language's type system, not encoded. Whether the API-shape criteria bind the Python binding, which has no token object, is open ruling D99 and is not relied on."
          "The test derivation (create a token with value 42, its value is 42 and its timestamp is set) is AC1 and AC2 and is not encoded."
  signoff "pending"
  statement : ∀ {N T : Type} [DecidableEq N], QFireRel N T → Prop :=
    fun Q => ∀ t, NoInputRead t →
      (∀ δ e, on (fun M M' => Q t M δ e M'), shall (fun M M' =>
        ∀ p, (M' p).Subperm (M p ++ EmittedTo e p))) ∧
      (∀ δ e, on (fun M M' => Q t M δ e M'), shall (fun M M' =>
        ∀ p, p ∉ inPlaces t → ¬ ResetArc t p → (M p).Subperm (M' p))) ∧
      (∀ δ e, on (fun M M' => Q t M δ e M'), shall (fun M M' =>
        ∀ p ∈ inPlaces t, ¬ ResetArc t p → (M p).Subperm (δ.inputs p ++ M' p))) ∧
      (∀ δ e, on (fun M M' => Q t M δ e M'), shall (fun M _ =>
        ∀ p ∈ inPlaces t, (δ.inputs p).Subperm (M p))) ∧
      (∀ δ e, on (fun M M' => Q t M δ e M'), shall (fun M _ =>
        ∀ p, ReadArc t p → ∀ x ∈ δ.reads p, x ∈ M p))

/- The pinned readable form of CORE-010: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CORE_010 : {N T : Type} → [DecidableEq N] → QFireRel N T → Prop :=
fun {N T} [DecidableEq N] Q =>
  ∀ (t : Reference.Trans N),
    NoInputRead t →
      (∀ (δ : Delivered N T) (e : List (N × T)),
          on fun M M' => Q t M δ e M', shall fun M M' => ∀ (p : N), (M' p).Subperm (M p ++ EmittedTo e p)) ∧
        (∀ (δ : Delivered N T) (e : List (N × T)),
            on fun M M' => Q t M δ e M', shall fun M M' => ∀ p ∉ inPlaces t, ¬ResetArc t p → (M p).Subperm (M' p)) ∧
          (∀ (δ : Delivered N T) (e : List (N × T)),
              on fun M M' => Q t M δ e M', shall fun M M' =>
                ∀ p ∈ inPlaces t, ¬ResetArc t p → (M p).Subperm (δ.inputs p ++ M' p)) ∧
            (∀ (δ : Delivered N T) (e : List (N × T)),
                on fun M M' => Q t M δ e M', shall fun M x => ∀ p ∈ inPlaces t, (δ.inputs p).Subperm (M p)) ∧
              ∀ (δ : Delivered N T) (e : List (N × T)),
                on fun M M' => Q t M δ e M', shall fun M x => ∀ (p : N), ReadArc t p → ∀ x ∈ δ.reads p, x ∈ M p
-/
#guard_msgs in #print CORE_010

/-! ### Lemmas about the reference operations -/

section Lemmas

variable {N T : Type} [DecidableEq N]

/-- A delivered input token is a token of the place: the FIFO prefix is part of the queue. -/
theorem core010_qInputs_mem {M : QueueMarking N T} {t : Trans N} {p : N} {x : T}
    (h : x ∈ qInputs M t p) : x ∈ M p :=
  List.mem_of_mem_take h

/-- The consume step leaves a sublist of every queue: a reset place is empty, any other place
keeps a suffix of its queue. -/
theorem core010_qConsume_sublist (M : QueueMarking N T) (t : Trans N) (p : N) :
    (qConsume M t p).Sublist (M p) := by
  unfold qConsume
  split
  · exact List.nil_sublist _
  · exact List.drop_sublist _ _

/-- A token the consume step leaves in a place is a token of the place. -/
theorem core010_qConsume_mem {M : QueueMarking N T} {t : Trans N} {p : N} {x : T}
    (h : x ∈ qConsume M t p) : x ∈ M p :=
  (core010_qConsume_sublist M t p).subset h

/-- A read token is a token of the place, with or without ruling D15: the read bag holds heads
of the queue after input consumption, a suffix of the place's queue. -/
theorem core010_qReads_mem {M : QueueMarking N T} {t : Trans N} {p : N} {x : T}
    (h : x ∈ qReads M t p) : x ∈ M p := by
  unfold qReads at h
  rw [qReadsBag_apply] at h
  simp only [List.mem_flatten, List.mem_replicate] at h
  obtain ⟨l, ⟨-, rfl⟩, hl⟩ := h
  exact List.mem_of_mem_drop (List.mem_of_mem_head? (Option.mem_toList.1 hl))

/-- At a place that is not a reset place, the consume step leaves the queue after the delivered
FIFO prefix. -/
theorem core010_qConsume_of_not_reset (M : QueueMarking N T) {t : Trans N} {p : N}
    (hr : ¬ ResetArc t p) : qConsume M t p = qPostInput M t p := by
  have hr' : p ∉ t.core.resets := hr
  simp [qConsume, hr']

end Lemmas

/-! ### Derived from the EXEC blocks, and the reference -/

/-- Derived: under ruling D15 CORE-010 follows from EXEC-010 (line 1: an input place that is not
a reset place ends as a permutation of its queue after the consumed prefix followed by its
emitted tokens; line 2: the delivered inputs are the FIFO prefix), EXEC-012 line 1 (every read
token is the head of the place), EXEC-013 line 1 (a reset place holds exactly its emitted tokens)
and EXEC-020 (every other place keeps its queue, or a sublist of it, followed by its emitted
tokens). Every relation meeting the four signed blocks meets CORE-010. -/
@[evidence cites "CORE-010" "lines 1 to 5, under ruling D15: every queue firing relation that satisfies EXEC-010, EXEC-012, EXEC-013 and EXEC-020 keeps every token it neither consumed nor cleared, keeps, delivers and reads only tokens the place held, without extra copies, or deposits emitted ones"]
theorem CORE_010_of_EXEC {N T : Type} [DecidableEq N] [ToString N]
    {Build : Trans N → Option String} {Q : QFireRel N T}
    (h10 : EXEC_010 Q) (h12 : EXEC_012 Build Q) (h13 : EXEC_013 Q) (h20 : EXEC_020 Q) :
    CORE_010 Q := by
  intro t hw
  refine ⟨fun δ e M M' h p => ?_, fun δ e M M' h p hi hr => ?_,
    fun δ e M M' h p hi hr => ?_, fun δ e M M' h p hi => ?_, fun δ e M M' h p hp x hx => ?_⟩
  · by_cases hr : ResetArc t p
    · rw [(h13 t hw).1 δ e M M' h p hr]
      exact (List.sublist_append_right _ _).subperm
    · obtain ⟨base, hb, hout, hin⟩ := h20 t M δ e M' h
      have hb' : M' p = base p ++ EmittedTo e p := hb p
      rw [hb']
      by_cases hi : p ∈ inPlaces t
      · exact ((hin p hi hr).append_right _).subperm
      · rw [hout p hi hr]
  · obtain ⟨base, hb, hout, -⟩ := h20 t M δ e M' h
    have hb' : M' p = base p ++ EmittedTo e p := hb p
    rw [hb', hout p hi hr]
    exact (List.sublist_append_left _ _).subperm
  · have hperm := (h10.1 t δ e p hi hr M M' h).2
    have hin : δ.inputs p = OldestFirst M p (Consumes t (Counts M) p) := h10.2 t δ e p hi M M' h
    rw [hin, OldestFirst]
    have : List.Perm ((M p).take (Consumes t (Counts M) p) ++ M' p)
        ((M p).take (Consumes t (Counts M) p) ++
          ((M p).drop (Consumes t (Counts M) p) ++ EmittedTo e p)) :=
      hperm.append_left _
    rw [← List.append_assoc, List.take_append_drop] at this
    exact (List.sublist_append_left _ _).subperm.trans this.symm.subperm
  · rw [h10.2 t δ e p hi M M' h, OldestFirst]
    exact (List.take_sublist _ _).subperm
  · have := (h12.1 t p δ e hw hp M M' h).2.1 x hx
    exact List.mem_of_mem_head? this

/-- The reference queue firing satisfies CORE-010, as the corollary of the reference's EXEC-010,
EXEC-012, EXEC-013 and EXEC-020 evidence (`CORE_010_of_EXEC`): a place ends holding its queue
after the consume step (empty for a reset place, the queue after the delivered FIFO prefix
otherwise) followed by the tokens emitted to it, and the read bag holds heads of the queue.
The `ToString` instance only names the build check of EXEC-012 and does not occur in CORE-010. -/
@[evidence holds CORE_010]
theorem CORE_010_reference {N T : Type} [DecidableEq N] :
    CORE_010 (RefQFire (N := N) (T := T)) :=
  letI : ToString N := ⟨fun _ => ""⟩
  CORE_010_of_EXEC EXEC_010_reference EXEC_012_reference EXEC_013_reference EXEC_020_reference

/-! ### Examples

The tokens of the examples are pairs `(value, creation timestamp)`, so that a changed value and
a changed timestamp are both visible. The transition is `qexT`: an input on `0`, a read and a
reset on `1`, output place `2`. -/

/-- The queue marking of the examples: place `0` holds `(10, 0), (11, 1), (12, 2)`, place `1`
holds `(20, 3), (21, 4)`, the output place `2` holds `(40, 5)`, every other place is empty. -/
def core010_M : QueueMarking Nat (Nat × Nat) := fun p =>
  if p = 0 then [(10, 0), (11, 1), (12, 2)] else if p = 1 then [(20, 3), (21, 4)]
  else if p = 2 then [(40, 5)] else []

/-- The emission of the examples: one new token `(30, 6)` to the output place `2`. -/
def core010_e : List (Nat × (Nat × Nat)) := [(2, (30, 6))]

/-- Re-stamp a token: the same value, a later creation timestamp. -/
def core010_restamp (x : Nat × Nat) : Nat × Nat := (x.1, x.2 + 1)

/-- Alter a token's value, keeping its creation timestamp. -/
def core010_revalue (x : Nat × Nat) : Nat × Nat := (x.1 + 1, x.2)

/-- Re-stamping keeps every value. -/
theorem core010_restamp_values (l : List (Nat × Nat)) :
    (l.map core010_restamp).map Prod.fst = l.map Prod.fst := by
  simp [List.map_map, Function.comp_def, core010_restamp]

/-! ### Violation: the kept tokens re-stamped -/

/-- A queue firing that is the reference except that every token a place keeps through the
consume step is re-stamped: same value, timestamp one later. -/
def core010_restampQ : QFireRel Nat (Nat × Nat) := fun t M δ e M' =>
  Enabled t (Counts M) ∧
    (∃ ch, deposit (Consumes t (Counts M)) (OutputSpec t) ch = some (e.map Prod.fst)) ∧
    δ = qDelivered M t ∧ M' = qAppend (fun p => (qConsume M t p).map core010_restamp) e

/-- The re-stamping firing of `qexT .one` from `core010_M`. -/
theorem core010_restampQ_fires :
    core010_restampQ (qexT .one) core010_M (qDelivered core010_M (qexT .one)) core010_e
      (qAppend (fun p => (qConsume core010_M (qexT .one) p).map core010_restamp) core010_e) :=
  ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩

/-- ✗ Re-stamping the tokens a place keeps violates CORE-010 (line 1, "with the same value and
creation timestamp"): firing `qexT .one` from `core010_M` leaves `(11, 2), (12, 3)` in place
`0`, which held `(11, 1), (12, 2)`; `(12, 3)` was neither held there nor emitted. -/
@[evidence forbids CORE_010]
theorem CORE_010_forbids_restamp : ¬ CORE_010 core010_restampQ := by
  intro h
  have := (h (qexT .one) (by decide)).1 _ _ _ _ core010_restampQ_fires 0
  revert this
  decide

/-! ### Violation: an altered copy handed over as an input -/

/-- A queue firing that is the reference except that the action receives, for every consumed
token, a copy with its value changed. -/
def core010_alteredInputQ : QFireRel Nat (Nat × Nat) := fun t M δ e M' =>
  Enabled t (Counts M) ∧
    (∃ ch, deposit (Consumes t (Counts M)) (OutputSpec t) ch = some (e.map Prod.fst)) ∧
    δ = ⟨fun p => (qInputs M t p).map core010_revalue, qReads M t⟩ ∧ M' = qFire M t e

/-- ✗ Handing the action an altered copy of a consumed token violates CORE-010 (line 4): firing
`qexT .one` from `core010_M` hands over `(11, 0)` from place `0`, which held `(10, 0)`. -/
@[evidence forbids CORE_010]
theorem CORE_010_forbids_alteredInput : ¬ CORE_010 core010_alteredInputQ := by
  intro h
  have hq : core010_alteredInputQ (qexT .one) core010_M
      ⟨fun p => (qInputs core010_M (qexT .one) p).map core010_revalue, qReads core010_M (qexT .one)⟩
      core010_e (qFire core010_M (qexT .one) core010_e) :=
    ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩
  have := (h (qexT .one) (by decide)).2.2.2.1 _ _ _ _ hq 0 (by decide)
  revert this
  decide

/-! ### Violation: an altered copy handed over as a read -/

/-- A queue firing that is the reference except that the action receives, for every read token,
a re-stamped copy. -/
def core010_alteredReadQ : QFireRel Nat (Nat × Nat) := fun t M δ e M' =>
  Enabled t (Counts M) ∧
    (∃ ch, deposit (Consumes t (Counts M)) (OutputSpec t) ch = some (e.map Prod.fst)) ∧
    δ = ⟨qInputs M t, fun p => (qReads M t p).map core010_restamp⟩ ∧ M' = qFire M t e

/-- ✗ Handing the action a re-stamped copy of a read token violates CORE-010 (line 5): firing
`qexT .one` from `core010_M` hands over `(20, 4)` from the read place `1`, which held
`(20, 3)`. -/
@[evidence forbids CORE_010]
theorem CORE_010_forbids_alteredRead : ¬ CORE_010 core010_alteredReadQ := by
  intro h
  have hq : core010_alteredReadQ (qexT .one) core010_M
      ⟨qInputs core010_M (qexT .one), fun p => (qReads core010_M (qexT .one) p).map core010_restamp⟩
      core010_e (qFire core010_M (qexT .one) core010_e) :=
    ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩
  have := (h (qexT .one) (by decide)).2.2.2.2 _ _ _ _ hq 1 (by decide)
  revert this
  decide

/-! ### Violation: re-stamped copies reported as emitted -/

/-- A queue firing that delivers as the reference, then re-stamps every token the consume step
leaves and lists every re-stamped token in `e` as if the action had emitted it to the place it
sits in. Line 1 alone accepts it: every token of `M'` is "emitted". -/
def core010_launderQ : QFireRel Nat (Nat × Nat) := fun t M δ e M' =>
  Enabled t (Counts M) ∧ δ = qDelivered M t ∧
    M' = (fun p => (qConsume M t p).map core010_restamp) ∧ ∀ p, ∀ x ∈ M' p, x ∈ EmittedTo e p

/-- The laundering emission from `core010_M` under `qexT .one`: the re-stamped `(11, 2)`,
`(12, 3)` at `0` and `(40, 6)` at `2`. -/
def core010_launderE : List (Nat × (Nat × Nat)) := [(0, (11, 2)), (0, (12, 3)), (2, (40, 6))]

/-- The laundering firing of `qexT .one` from `core010_M`. -/
theorem core010_launderQ_fires :
    core010_launderQ (qexT .one) core010_M (qDelivered core010_M (qexT .one)) core010_launderE
      (fun p => (qConsume core010_M (qexT .one) p).map core010_restamp) := by
  refine ⟨by decide, rfl, rfl, fun p x hx => ?_⟩
  by_cases h0 : p = 0
  · subst h0; revert x; decide
  by_cases h1 : p = 1
  · subst h1; revert x; decide
  by_cases h2 : p = 2
  · subst h2; revert x; decide
  · have h1' : p ∉ (qexT .one).core.resets := by simp [qexT, h1]
    simp [qConsume, qPostInput, h1', core010_M, h0, h1, h2] at hx

/-- ✗ Re-stamping the tokens a place keeps and reporting the copies as emitted violates CORE-010
(line 2): the output place `2`, neither an input nor a reset place of `qexT .one`, held
`(40, 5)` and after the firing holds only `(40, 6)`. -/
@[evidence forbids CORE_010]
theorem CORE_010_forbids_launder : ¬ CORE_010 core010_launderQ := by
  intro h
  have := (h (qexT .one) (by decide)).2.1 _ _ _ _ core010_launderQ_fires 2 (by decide)
    (by decide)
  revert this
  decide

/-! ### Violation: the action receives the head token k times -/

/-- The inputs a runtime delivers when it peeks the head `k` times before removing `k` tokens:
`k` copies of the oldest token. -/
def core010_headTwiceInputs (M : QueueMarking Nat (Nat × Nat)) (t : Trans Nat) (p : Nat) :
    List (Nat × Nat) :=
  (qInputs M t p).flatMap (fun _ => (M p).head?.toList)

/-- A queue firing that is the reference except that the action receives the head token once
per consumed token. The place itself is consumed correctly. -/
def core010_headTwiceQ : QFireRel Nat (Nat × Nat) := fun t M δ e M' =>
  Enabled t (Counts M) ∧
    (∃ ch, deposit (Consumes t (Counts M)) (OutputSpec t) ch = some (e.map Prod.fst)) ∧
    δ = ⟨core010_headTwiceInputs M t, qReads M t⟩ ∧ M' = qFire M t e

/-- The head-twice firing of `qexT (.exactly 2)` from `core010_M`. -/
theorem core010_headTwiceQ_fires :
    core010_headTwiceQ (qexT (.exactly 2)) core010_M
      ⟨core010_headTwiceInputs core010_M (qexT (.exactly 2)), qReads core010_M (qexT (.exactly 2))⟩
      core010_e (qFire core010_M (qexT (.exactly 2)) core010_e) :=
  ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩

/-- ✗ Handing the action the head token twice for an `exactly(2)` input violates CORE-010
(line 4): it receives `(10, 0), (10, 0)` where place `0` held `(10, 0)` once; the second consumed
token, created as `(11, 1)`, reaches the action as `(10, 0)`. -/
@[evidence forbids CORE_010]
theorem CORE_010_forbids_headTwice : ¬ CORE_010 core010_headTwiceQ := by
  intro h
  have := (h (qexT (.exactly 2)) (by decide)).2.2.2.1 _ _ _ _ core010_headTwiceQ_fires 0
    (by decide)
  revert this
  decide

/-! ### Violations with unit tokens

With `(Unit, timestamp)` tokens (CORE-012's unit tokens, which most control flow uses) a
re-stamped token can equal another token the place holds or receives, so a membership test
cannot see it. -/

/-- A unit token: no value, a creation timestamp. -/
abbrev Core010U := Unit × Nat

/-- The kept queue of a runtime whose value ring and timestamp ring run out of step: values
after the consumed prefix, paired with timestamps from the old head. -/
def core010_desyncKeep (l : List Core010U) (k : Nat) : List Core010U :=
  List.zip ((l.map Prod.fst).drop k) ((l.map Prod.snd).take (l.length - k))

/-- A queue firing that is the reference except that the consume step advances the value ring
but not the timestamp ring, so every kept token takes an older token's timestamp. -/
def core010_desyncQ : QFireRel Nat Core010U := fun t M δ e M' =>
  Enabled t (Counts M) ∧
    (∃ ch, deposit (Consumes t (Counts M)) (OutputSpec t) ch = some (e.map Prod.fst)) ∧
    δ = qDelivered M t ∧
    M' = qAppend (fun p => if p ∈ t.core.resets then []
      else core010_desyncKeep (M p) (qInputs M t p).length) e

/-- Unit tokens: place `0` holds tokens created at 0, 1, 2; place `1` one created at 3; the
output place `2` one created at 4. -/
def core010_UM : QueueMarking Nat Core010U := fun p =>
  if p = 0 then [((), 0), ((), 1), ((), 2)] else if p = 1 then [((), 3)]
  else if p = 2 then [((), 4)] else []

/-- The unit-token emission: one new token created at 5 to the output place `2`. -/
def core010_Ue : List (Nat × Core010U) := [(2, ((), 5))]

/-- The desync firing of `qexT .one` from `core010_UM`. -/
theorem core010_desyncQ_fires :
    core010_desyncQ (qexT .one) core010_UM (qDelivered core010_UM (qexT .one)) core010_Ue
      (qAppend (fun p => if p ∈ (qexT .one).core.resets then []
        else core010_desyncKeep (core010_UM p) (qInputs core010_UM (qexT .one) p).length)
        core010_Ue) :=
  ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩

/-- ✗ Out-of-step value and timestamp rings violate CORE-010 (line 3): place `0` held tokens
created at 0, 1, 2; the action receives the one created at 0, and the place keeps tokens stamped
0 and 1 where it should keep those created at 1 and 2. The token created at 2 is gone, though
every kept token equals one the place held. -/
@[evidence forbids CORE_010]
theorem CORE_010_forbids_desync : ¬ CORE_010 core010_desyncQ := by
  intro h
  have := (h (qexT .one) (by decide)).2.2.1 _ _ _ _ core010_desyncQ_fires 0 (by decide)
    (by decide)
  revert this
  decide

/-- The queue a place ends with when it stamps every token with its last arrival: kept tokens
then emitted ones, all re-stamped with the last emitted token's timestamp when anything was
emitted to the place. -/
def core010_lastArrivalStamp (base em : List Core010U) : List Core010U :=
  match em.getLast? with
  | none => base
  | some z => (base ++ em).map (fun x => (x.1, z.2))

/-- A queue firing that is the reference except that a place reports the time of its last
deposit as the creation timestamp of every token it holds. -/
def core010_lastArrivalQ : QFireRel Nat Core010U := fun t M δ e M' =>
  Enabled t (Counts M) ∧
    (∃ ch, deposit (Consumes t (Counts M)) (OutputSpec t) ch = some (e.map Prod.fst)) ∧
    δ = qDelivered M t ∧ M' = fun p => core010_lastArrivalStamp (qConsume M t p) (EmittedTo e p)

/-- The last-arrival firing of `qexT .one` from `core010_UM`. -/
theorem core010_lastArrivalQ_fires :
    core010_lastArrivalQ (qexT .one) core010_UM (qDelivered core010_UM (qexT .one)) core010_Ue
      (fun p => core010_lastArrivalStamp (qConsume core010_UM (qexT .one) p)
        (EmittedTo core010_Ue p)) :=
  ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩

/-- ✗ Stamping a place's tokens with its last arrival violates CORE-010 (line 2): the output
place `2`, neither an input nor a reset place, held the token created at 4 and after the firing
holds two tokens stamped 5, each equal to the emitted one. -/
@[evidence forbids CORE_010]
theorem CORE_010_forbids_lastArrival : ¬ CORE_010 core010_lastArrivalQ := by
  intro h
  have := (h (qexT .one) (by decide)).2.1 _ _ _ _ core010_lastArrivalQ_fires 2 (by decide)
    (by decide)
  revert this
  decide

/-! ### Violation: a kept token copied -/

/-- The extra tokens of the copying relation: at place `2`, one more copy of the token at the
head of the place before the firing; nothing elsewhere. -/
def core010_dupExtra (M : QueueMarking Nat (Nat × Nat)) (p : Nat) : List (Nat × Nat) :=
  if p = 2 then (M p).take 1 else []

/-- A queue firing that is the reference except that place `2` gets one more copy of its old
head after the tokens it keeps. Every token the reference keeps is still there, so lines 2 and 3
hold; only line 1's "shall not duplicate" sees the copy. -/
def core010_dupQ : QFireRel Nat (Nat × Nat) := fun t M δ e M' =>
  Enabled t (Counts M) ∧
    (∃ ch, deposit (Consumes t (Counts M)) (OutputSpec t) ch = some (e.map Prod.fst)) ∧
    δ = qDelivered M t ∧ M' = qAppend (fun p => qConsume M t p ++ core010_dupExtra M p) e

/-- A firing of the copying relation is a reference firing with the same delivery, and every
place ends holding at least the reference's queue, as a sublist. -/
theorem core010_dupQ_ref {t : Trans Nat} {M M' : QueueMarking Nat (Nat × Nat)}
    {δ : Delivered Nat (Nat × Nat)} {e : List (Nat × (Nat × Nat))} (h : core010_dupQ t M δ e M') :
    RefQFire t M δ e (qFire M t e) ∧ ∀ p, (qFire M t e p).Sublist (M' p) := by
  obtain ⟨hen, hdep, hδ, rfl⟩ := h
  refine ⟨⟨hen, hdep, hδ, rfl⟩, fun p => ?_⟩
  rw [qFire, qAppend_apply, qAppend_apply, List.append_assoc]
  exact (List.sublist_append_right _ _).append_left _

/-- The copying firing of `qexT .one` from `core010_M`. -/
theorem core010_dupQ_fires :
    core010_dupQ (qexT .one) core010_M (qDelivered core010_M (qexT .one)) core010_e
      (qAppend (fun p => qConsume core010_M (qexT .one) p ++ core010_dupExtra core010_M p)
        core010_e) :=
  ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩

/-- ✗ Copying a kept token violates CORE-010 (line 1, "the firing *shall* not duplicate any of
these tokens"): firing `qexT .one` from `core010_M` leaves `(40, 5), (40, 5), (30, 6)` in the
output place `2`, which held `(40, 5)` once and received `(30, 6)`. Lines 2 and 3 accept the
firing (`CORE_010_mutant_line1Membership_killed_dup`). -/
@[evidence forbids CORE_010]
theorem CORE_010_forbids_dup : ¬ CORE_010 core010_dupQ := by
  intro h
  have := (h (qexT .one) (by decide)).1 _ _ _ _ core010_dupQ_fires 2
  revert this
  decide

/-! ### Mutant: only the value is immutable -/

/-- Mutant reading of CORE-010 under which only the value is immutable: lines 1 to 3 compare
values only, so a kept token may carry a new timestamp. Lines 4 and 5 are as in CORE-010. -/
def CORE_010_mutant_valueOnly {N V S : Type} [DecidableEq N] (Q : QFireRel N (V × S)) :
    Prop :=
  ∀ t, NoInputRead t →
    (∀ δ e, on (fun M M' => Q t M δ e M'), shall (fun M M' =>
      ∀ p, ((M' p).map Prod.fst).Subperm ((M p ++ EmittedTo e p).map Prod.fst))) ∧
    (∀ δ e, on (fun M M' => Q t M δ e M'), shall (fun M M' =>
      ∀ p, p ∉ inPlaces t → ¬ ResetArc t p → ((M p).map Prod.fst).Subperm ((M' p).map Prod.fst))) ∧
    (∀ δ e, on (fun M M' => Q t M δ e M'), shall (fun M M' =>
      ∀ p ∈ inPlaces t, ¬ ResetArc t p →
        ((M p).map Prod.fst).Subperm ((δ.inputs p ++ M' p).map Prod.fst))) ∧
    (∀ δ e, on (fun M M' => Q t M δ e M'), shall (fun M _ =>
      ∀ p ∈ inPlaces t, (δ.inputs p).Subperm (M p))) ∧
    (∀ δ e, on (fun M M' => Q t M δ e M'), shall (fun M _ =>
      ∀ p, ReadArc t p → ∀ x ∈ δ.reads p, x ∈ M p))

/-- The re-stamping firing kills the value-only mutant: it keeps every value, so it satisfies
the mutant reading at every transition and marking, but not CORE-010, whose "neither the value
nor the timestamp" rejects the re-stamped `(12, 3)` (`CORE_010_forbids_restamp`). -/
@[evidence mutant CORE_010]
theorem CORE_010_mutant_valueOnly_killed :
    CORE_010_mutant_valueOnly core010_restampQ ∧ ¬ CORE_010 core010_restampQ := by
  refine ⟨fun t _ => ⟨fun δ e M M' h p => ?_, fun δ e M M' h p hi hr => ?_,
      fun δ e M M' h p hi hr => ?_, fun δ e M M' h p _ => ?_, fun δ e M M' h p _ x hx => ?_⟩,
    CORE_010_forbids_restamp⟩
  · obtain ⟨-, -, -, rfl⟩ := h
    rw [qAppend_apply, List.map_append, List.map_append, core010_restamp_values]
    exact (((core010_qConsume_sublist M t p).map _).append_right _).subperm
  · obtain ⟨-, -, -, rfl⟩ := h
    rw [qAppend_apply, List.map_append, core010_restamp_values,
      exec020_qConsume_untouched M hi hr]
    exact (List.sublist_append_left _ _).subperm
  · obtain ⟨-, -, rfl, rfl⟩ := h
    rw [qAppend_apply, core010_qConsume_of_not_reset M hr]
    simp only [qDelivered, List.map_append, core010_restamp_values]
    rw [← List.append_assoc, ← List.map_append, qInputs_append_qPostInput, ← List.map_append]
    exact ((List.sublist_append_left _ _).map _).subperm
  · obtain ⟨-, -, rfl, -⟩ := h
    exact (List.take_sublist _ _).subperm
  · obtain ⟨-, -, rfl, -⟩ := h
    exact core010_qReads_mem hx

/-! ### Mutant: membership instead of multiplicity -/

/-- Mutant reading of CORE-010 that compares by membership only and has no conservation lines:
every token a place ends with is a token it held or one emitted to it, and every delivered input
or read token is a token of its place. -/
def CORE_010_mutant_membership {N T : Type} [DecidableEq N] (Q : QFireRel N T) : Prop :=
  ∀ t, NoInputRead t →
    (∀ δ e, on (fun M M' => Q t M δ e M'), shall (fun M M' =>
      ∀ p, ∀ x ∈ M' p, x ∈ M p ∨ x ∈ EmittedTo e p)) ∧
    (∀ δ e, on (fun M M' => Q t M δ e M'), shall (fun M _ =>
      ∀ p ∈ inPlaces t, ∀ x ∈ δ.inputs p, x ∈ M p)) ∧
    (∀ δ e, on (fun M M' => Q t M δ e M'), shall (fun M _ =>
      ∀ p, ReadArc t p → ∀ x ∈ δ.reads p, x ∈ M p))

/-- The laundering relation kills the membership mutant: every token it leaves is listed as
emitted, so it satisfies the mutant reading at every transition and marking, but not CORE-010,
whose line 2 sees that the held `(40, 5)` is gone (`CORE_010_forbids_launder`). -/
@[evidence mutant CORE_010]
theorem CORE_010_mutant_membership_killed_launder :
    CORE_010_mutant_membership core010_launderQ ∧ ¬ CORE_010 core010_launderQ := by
  refine ⟨fun t _ => ⟨fun δ e M M' h p x hx => .inr (h.2.2.2 p x hx),
      fun δ e M M' h p _ x hx => ?_, fun δ e M M' h p _ x hx => ?_⟩, CORE_010_forbids_launder⟩
  · obtain ⟨-, rfl, -⟩ := h
    exact core010_qInputs_mem hx
  · obtain ⟨-, rfl, -⟩ := h
    exact core010_qReads_mem hx

/-- The head-twice relation kills the membership mutant: the duplicated head is a token the
place held, so it satisfies the mutant reading at every transition and marking, but not
CORE-010, whose line 4 counts it (`CORE_010_forbids_headTwice`). -/
@[evidence mutant CORE_010]
theorem CORE_010_mutant_membership_killed_headTwice :
    CORE_010_mutant_membership core010_headTwiceQ ∧ ¬ CORE_010 core010_headTwiceQ := by
  refine ⟨fun t _ => ⟨fun δ e M M' h p x hx => ?_, fun δ e M M' h p _ x hx => ?_,
      fun δ e M M' h p _ x hx => ?_⟩, CORE_010_forbids_headTwice⟩
  · obtain ⟨-, -, -, rfl⟩ := h
    rw [qFire, qAppend_apply] at hx
    rcases List.mem_append.1 hx with hx | hx
    · exact .inl (core010_qConsume_mem hx)
    · exact .inr hx
  · obtain ⟨-, -, rfl, -⟩ := h
    simp only [core010_headTwiceInputs, List.mem_flatMap] at hx
    obtain ⟨_, -, hx⟩ := hx
    exact List.mem_of_mem_head? (Option.mem_toList.1 hx)
  · obtain ⟨-, -, rfl, -⟩ := h
    exact core010_qReads_mem hx

/-- A kept token of the desync relation is a token the place held: with unit values, a pair of
a value and an old timestamp is the old token. -/
theorem core010_desyncKeep_mem {l : List Core010U} {k : Nat} {x : Core010U}
    (h : x ∈ core010_desyncKeep l k) : x ∈ l := by
  have h2 := (List.of_mem_zip h).2
  obtain ⟨y, hy, hxy⟩ := List.mem_map.1 (List.mem_of_mem_take h2)
  have : y = x := Prod.ext (Subsingleton.elim _ _) hxy
  exact this ▸ hy

/-- The desync relation kills the membership mutant: every re-stamped unit token equals a token
the place held, so it satisfies the mutant reading at every transition and marking, but not
CORE-010, whose line 3 sees that the token created at 2 is gone (`CORE_010_forbids_desync`). -/
@[evidence mutant CORE_010]
theorem CORE_010_mutant_membership_killed_desync :
    CORE_010_mutant_membership core010_desyncQ ∧ ¬ CORE_010 core010_desyncQ := by
  refine ⟨fun t _ => ⟨fun δ e M M' h p x hx => ?_, fun δ e M M' h p _ x hx => ?_,
      fun δ e M M' h p _ x hx => ?_⟩, CORE_010_forbids_desync⟩
  · obtain ⟨-, -, -, rfl⟩ := h
    rw [qAppend_apply] at hx
    rcases List.mem_append.1 hx with hx | hx
    · left
      split at hx
      · simp at hx
      · exact core010_desyncKeep_mem hx
    · exact .inr hx
  · obtain ⟨-, -, rfl, -⟩ := h
    exact core010_qInputs_mem hx
  · obtain ⟨-, -, rfl, -⟩ := h
    exact core010_qReads_mem hx

/-- A token of a last-arrival place is a token the place kept or one emitted to it: with unit
values, a token re-stamped to the last arrival's timestamp is the last arrival. -/
theorem core010_lastArrivalStamp_mem {base em : List Core010U} {x : Core010U}
    (h : x ∈ core010_lastArrivalStamp base em) : x ∈ base ∨ x ∈ em := by
  unfold core010_lastArrivalStamp at h
  split at h
  · exact .inl h
  · rename_i z hz
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 h
    have : ((y.1, z.2) : Core010U) = z := Prod.ext (Subsingleton.elim _ _) rfl
    rw [this]
    exact .inr (List.mem_of_getLast? hz)

/-- The last-arrival relation kills the membership mutant: every re-stamped unit token equals
the emitted one, so it satisfies the mutant reading at every transition and marking, but not
CORE-010, whose line 2 sees that the held token created at 4 is gone
(`CORE_010_forbids_lastArrival`). -/
@[evidence mutant CORE_010]
theorem CORE_010_mutant_membership_killed_lastArrival :
    CORE_010_mutant_membership core010_lastArrivalQ ∧ ¬ CORE_010 core010_lastArrivalQ := by
  refine ⟨fun t _ => ⟨fun δ e M M' h p x hx => ?_, fun δ e M M' h p _ x hx => ?_,
      fun δ e M M' h p _ x hx => ?_⟩, CORE_010_forbids_lastArrival⟩
  · obtain ⟨-, -, -, rfl⟩ := h
    rcases core010_lastArrivalStamp_mem hx with hx | hx
    · exact .inl (core010_qConsume_mem hx)
    · exact .inr hx
  · obtain ⟨-, -, rfl, -⟩ := h
    exact core010_qInputs_mem hx
  · obtain ⟨-, -, rfl, -⟩ := h
    exact core010_qReads_mem hx

/-! ### Mutant: line 1 by membership, lines 2 to 5 kept -/

/-- Mutant reading of CORE-010 whose line 1 compares by membership only: every token a place
ends with is a token it held or one emitted to it, with no bound on copies. Lines 2 to 5 are as
in CORE-010, so the conservation lines stay. -/
def CORE_010_mutant_line1Membership {N T : Type} [DecidableEq N] (Q : QFireRel N T) : Prop :=
  ∀ t, NoInputRead t →
    (∀ δ e, on (fun M M' => Q t M δ e M'), shall (fun M M' =>
      ∀ p, ∀ x ∈ M' p, x ∈ M p ∨ x ∈ EmittedTo e p)) ∧
    (∀ δ e, on (fun M M' => Q t M δ e M'), shall (fun M M' =>
      ∀ p, p ∉ inPlaces t → ¬ ResetArc t p → (M p).Subperm (M' p))) ∧
    (∀ δ e, on (fun M M' => Q t M δ e M'), shall (fun M M' =>
      ∀ p ∈ inPlaces t, ¬ ResetArc t p → (M p).Subperm (δ.inputs p ++ M' p))) ∧
    (∀ δ e, on (fun M M' => Q t M δ e M'), shall (fun M _ =>
      ∀ p ∈ inPlaces t, (δ.inputs p).Subperm (M p))) ∧
    (∀ δ e, on (fun M M' => Q t M δ e M'), shall (fun M _ =>
      ∀ p, ReadArc t p → ∀ x ∈ δ.reads p, x ∈ M p))

/-- The copying relation kills the line-1 membership mutant: the copy is a token the place held
and every kept token is still there, so it satisfies the mutant reading at every transition and
marking (lines 2 to 5 through the reference, `core010_dupQ_ref`), but not CORE-010, whose line 1
counts the copy (`CORE_010_forbids_dup`). This is the case only line 1 decides: lines 2 and 3 of
CORE-010 accept it. -/
@[evidence mutant CORE_010]
theorem CORE_010_mutant_line1Membership_killed_dup :
    CORE_010_mutant_line1Membership core010_dupQ ∧ ¬ CORE_010 core010_dupQ := by
  refine ⟨fun t hw => ⟨fun δ e M M' h p x hx => ?_, fun δ e M M' h p hi hr => ?_,
      fun δ e M M' h p hi hr => ?_, fun δ e M M' h p hi => ?_, fun δ e M M' h p hp x hx => ?_⟩,
    CORE_010_forbids_dup⟩
  · obtain ⟨-, -, -, rfl⟩ := h
    rw [qAppend_apply] at hx
    rcases List.mem_append.1 hx with hx | hx
    · rcases List.mem_append.1 hx with hx | hx
      · exact .inl (core010_qConsume_mem hx)
      · left
        unfold core010_dupExtra at hx
        split at hx
        · exact List.mem_of_mem_take hx
        · simp at hx
    · exact .inr hx
  · obtain ⟨href, hsub⟩ := core010_dupQ_ref h
    exact ((CORE_010_reference t hw).2.1 δ e M _ href p hi hr).trans
      (hsub p).subperm
  · obtain ⟨href, hsub⟩ := core010_dupQ_ref h
    exact ((CORE_010_reference t hw).2.2.1 δ e M _ href p hi hr).trans
      ((hsub p).append_left _).subperm
  · obtain ⟨href, -⟩ := core010_dupQ_ref h
    exact (CORE_010_reference t hw).2.2.2.1 δ e M _ href p hi
  · obtain ⟨href, -⟩ := core010_dupQ_ref h
    exact (CORE_010_reference t hw).2.2.2.2 δ e M _ href p hp x hx

/-! ### Every line exercised -/

/-- Every line of CORE-010 is exercised by the reference, firing `qexT .one` (a `one()` input on
`0`, a read and a reset on `1`, output place `2`; no input arc and read arc on one place) from
`core010_M`, the action emitting the new token `(30, 6)` to `2`: the action receives `(10, 0)`
from the input place `0` (line 4, AC1) and `(20, 3)` from the read place `1` (line 5), each with
its value and timestamp; place `0` keeps `(11, 1)` and `(12, 2)` unchanged (lines 1 and 3) and
place `2` keeps `(40, 5)` and then holds the emitted `(30, 6)` (lines 1 and 2). -/
@[evidence nonvacuous CORE_010]
theorem CORE_010_nonvacuous :
    RefQFire (qexT .one) core010_M (qDelivered core010_M (qexT .one)) core010_e
        (qFire core010_M (qexT .one) core010_e) ∧
      NoInputRead (qexT .one) ∧
      (qDelivered core010_M (qexT .one)).inputs 0 = [(10, 0)] ∧
      (qDelivered core010_M (qexT .one)).reads 1 = [(20, 3)] ∧
      qFire core010_M (qexT .one) core010_e 0 = [(11, 1), (12, 2)] ∧
      qFire core010_M (qexT .one) core010_e 2 = [(40, 5), (30, 6)] :=
  ⟨⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩, by decide, by decide, by decide, by decide,
    by decide⟩

end Libpetri.Spec
