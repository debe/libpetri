import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryQueue

set_option linter.missingDocs true

/-!
# CORE-070: Marking state (`spec/01-core-model.md`)

CORE-070 is a pure-function requirement (kind F): it fixes the operations of a marking, an
empty marking, adding a token to a place, removing the first token of a place and the token
count of a place, against queue order (glossary: Queue order). The statement is a predicate over
an abstract store `Ops : MarkingOps N T` (glossary `GlossaryQueue.lean`), the one store interface
CORE-070 and CONC-022 share. `Ops.view` reads the queue each place holds, oldest token first, so
every operation is stated against the queue it changes. `Ops.ok s p` says that the state `s`
holds a queue for `p`: every set of places (the places of a net) has an empty marking that holds
all of them, and every operation keeps every place the marking held. So the operation lines
chain, and a sequence of operations from the empty marking of a net is constrained at every step
(`CORE_070_reach`, `CORE_070_adds`, `CORE_070_fifo`, `CORE_070_derivation`).

The witness is `refQOps`, the queue marking that the reference queue firing `RefQFire` steps
(`view` is the identity, `add` is `qAppendOne`). The flat ring pool of the precompiled backend
satisfies the block too, with its removal guarded by the count as every caller of
`ring_remove_first` does (`CORE_070_ringStore`), which is the evidence that "internally, each
place maps to a FIFO queue" holds of that storage. The wrong models are a stack (add at the
head), an add that also writes another place, a last-in first-out removal, a removal from an
unmarked place that clears another place, a count of marked places instead of tokens, an empty
marking that holds a token, a store that holds no place, a store whose states each hold one
place, a fixed-capacity ring that drops a token added to a full ring, and a map store that drops
the entry of a place its removal empties.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## CORE-070: Marking State -/

requirement CORE_070
  id "CORE-070"
  title "Marking State"
  kind F
  scope "all executors"
  source verbatim "spec/01-core-model.md"
  quote "A marking represents the current distribution of tokens across all places."
        "Internally, each place maps to a FIFO queue of tokens."
        "A marking *shall* hold a queue of tokens for each place of its net, oldest token first, and the token count of a place *shall* be the length of its queue."
        "An empty marking *shall* hold no token in any place."
        "*When* a token is added to a place, the marking *shall* append it at the tail of that place's queue and leave the queue of every other place unchanged."
        "*When* the first token of a marked place is removed, the marking *shall* return the head of that place's queue and keep the rest of that queue in order, leaving the queue of every other place unchanged."
        "*If* the first token of a place that is not marked is removed, *then* the marking *shall* return no token and change no queue."
        "*When* a token is added to or removed from a marking, the resulting marking *shall* still hold a queue for each place of its net."
  reading "Let Ops be a store of markings: view s p is the queue place p holds in state s, oldest token first; ok s p says that s holds a queue for p; empty, add, removeFirst and count are the operations."
          "For every list of places P there is a state that holds every place of P, and in which every place holds the empty queue and has token count 0."
          "In the designated empty marking every place holds the empty queue and has token count 0."
          "For every state s holding p: add s p x holds at p the queue of s followed by x, and its count at p is one more; every place q that s holds is still held, and if q is not p it keeps its queue and its count."
          "For every state s holding p, with p marked: removeFirst s p returns the head of p's queue, leaves p holding the rest of its queue in order, and its count at p is one less; every place q that s holds is still held, and if q is not p it keeps its queue and its count."
          "For every state s holding p, with p not marked: removeFirst s p returns no token, and every place q that s holds is still held and keeps its queue and its count."
          "For every state s holding p, the token count of p is the length of p's queue."
  assumes "The model is a store Ops : MarkingOps N T (glossary GlossaryQueue.lean), the one interface CORE-070 and CONC-022 are stated over. N is the place identity (glossary: Place; identity by name, CORE-002) and T the token, kept abstract: a token's value and created_at are not constrained here, only which token sits where in a queue. view reads each place's queue, so 'FIFO queue' and 'queue order' are the glossary term Queue order; Marked is the glossary term on the count view (count s p not zero)."
          "ok s p is 'the store s holds a queue for p'. The queue marking of the reference (refQOps) holds one for every place in every state (ok is True); a store compiled for one net (the precompiled ring pool, CONC-022) holds one for each place of that net, and only while it is well formed. 'The places of its net' is read as a finite list of places P, so the first line says that every net has an empty marking that holds all of its places (for the ring pool, a pool with one ring per place id up to the largest one, CORE_070_ringStore). The three closure clauses (a place the marking held is still held after add, after a marked removal and after an unmarked removal) are the last quoted sentence, which is the third applied to the marking an operation leaves. Together with the first line they make the third quoted sentence hold of every marking reached from the empty marking of a net by the operations (CORE_070_reach), which is how 'a marking holds a queue for each place of its net' is read: a state the store never reaches from such an empty marking is not a marking of that net, and nothing is claimed of it. Without the closure clauses the operation lines constrain one step from a held state only (CORE_070_mutant_noClosure_ring and CORE_070_mutant_noClosure_map); without the first line's 'every place of P at once' a store whose states each hold one place passes (CORE_070_mutant_somePlace_killed)."
          "The operation lines protect the places q that the state holds (ok s q), which by the reading above are the places of its net; 'every other place' in the add and removal sentences is read as every other place of the net, the places the marking holds a queue for. A place outside the net is not part of the marking and is not constrained. The precompiled ring pool shows why the premise is needed: a place id beyond the pool's place count has no ring, and the pool says nothing about what reading it would show."
          "The designated empty marking Ops.empty is read at the view only (the second line): it holds no token in any place. It is not required to hold a place. The glossary store refRingStore takes as Ops.empty the pool over no place (emptyPool), which holds no place (core070_ringEmpty_holds_none), because a ring pool is sized when the net is compiled; the empty marking of a net is the state the first line provides. A consequence: a store whose designated empty state holds no place and whose add from that state loses the token is accepted, since adding to a place a marking does not hold is not an operation the spec describes. Tying Ops.empty to the places of a net needs an empty marking indexed by the place list in the glossary interface (MarkingOps, shared with CONC-022), which is outside this block."
          "The first two quoted sentences are prose that the EARS sentences after them restate: 'the current distribution of tokens across all places' is the first line together with the count line and the closure clauses, and 'Internally, each place maps to a FIFO queue' is the view of each place and the add and removal lines. Across a sequence of operations the queue is first in, first out: from the empty marking of a net, a sequence of adds leaves at each place exactly the tokens added there, in the order added (CORE_070_adds), and a removal then returns the first of them (CORE_070_fifo). 'Internally' does not single out one storage: both the queue marking (CORE_070_reference) and the precompiled ring pool (CORE_070_ringStore) satisfy the block."
          "The removal lines are read at the view and at ok: removing from a place that is not marked changes no queue and no count and keeps every place held, which is what an observer of the marking can see. Whether the store's internal state is untouched is not claimed. The precompiled ring pool's own removal (ring_remove_first in precompiled_backend.rs) is a private operation with the precondition 'the place is marked': on an unmarked place it would panic on its unwrap, and its callers check the count first. Its Lean model Pool.removeFirst advances the head index there, which leaves a pool that is no longer well formed (core070_ringRaw_unmarked_breaks). The block is therefore checked against the ring pool with the removal its callers perform, guarded by the count (core070_ringMarking), which is the marking interface (Marking.remove_first in Rust, removeFirst in Java and TypeScript, all returning no token on an unmarked place)."
          "The operations are one step each; a sequence of operations is their composition (CORE_070_reach). Which operations a firing performs, and in which order, is EXEC-010, EXEC-012, EXEC-013 and EXEC-020: a firing's deposit is one add per emitted token, in emission order (refQFire_deposit_adds). Removal of a matching token (the correlated ν input, NU-020) and removal of every token (the reset drain, CORE-034, EXEC-013) are other operations, not stated here; so is peek (EXEC-012, CONC-022), which CORE-070 does not mention."
          "Who may call the operations (only the orchestrator; actions never touch the live marking) is CORE-071, and the snapshot form of a marking is CORE-073; neither is encoded here."
          "AC1 (an empty marking has zero tokens in all places) is the first line (the empty marking of a net) and the second line (the designated empty marking)."
          "AC2 (tokens can be added and removed from specific places) is the first line (every place of a net is held by its empty marking) together with the add line and the two removal lines, each of which changes only the place it names and keeps every place held, so any sequence of adds and removals on the places of a net is constrained at every step (CORE_070_reach)."
          "AC3 (the token count per place is queryable) is the count line: count is the length of the place's queue, and the add and removal lines say how it moves."
          "The test derivation (empty marking, three tokens added to P, count 3, one removed, count 2) is a consequence of the statement for every store, from the empty marking of any net containing P (CORE_070_derivation), which also gives that the token removed is the first one added; CORE_070_nonvacuous runs it on the reference."
  signoff "2026-11-13 1cc7b90b478876c1 ai"
  statement : ∀ {N T : Type}, MarkingOps N T → Prop :=
    fun Ops =>
      (∀ P : List _, ∃ s, (∀ p ∈ P, Ops.ok s p) ∧
        ∀ q, Ops.view s q = [] ∧ Ops.count s q = 0) ∧
      (∀ p, Ops.view Ops.empty p = [] ∧ Ops.count Ops.empty p = 0) ∧
      (∀ s p x, Ops.ok s p →
        Ops.view (Ops.add s p x) p = Ops.view s p ++ [x] ∧
        Ops.count (Ops.add s p x) p = Ops.count s p + 1 ∧
        ∀ q, Ops.ok s q →
          Ops.ok (Ops.add s p x) q ∧
          (q ≠ p → Ops.view (Ops.add s p x) q = Ops.view s q ∧
            Ops.count (Ops.add s p x) q = Ops.count s q)) ∧
      (∀ s p, Ops.ok s p → Marked (Ops.count s) p →
        (Ops.removeFirst s p).1 = (Ops.view s p).head? ∧
        Ops.view (Ops.removeFirst s p).2 p = (Ops.view s p).tail ∧
        Ops.count (Ops.removeFirst s p).2 p = Ops.count s p - 1 ∧
        ∀ q, Ops.ok s q →
          Ops.ok (Ops.removeFirst s p).2 q ∧
          (q ≠ p → Ops.view (Ops.removeFirst s p).2 q = Ops.view s q ∧
            Ops.count (Ops.removeFirst s p).2 q = Ops.count s q)) ∧
      (∀ s p, Ops.ok s p → ¬ Marked (Ops.count s) p →
        (Ops.removeFirst s p).1 = none ∧
        ∀ q, Ops.ok s q →
          Ops.ok (Ops.removeFirst s p).2 q ∧
          Ops.view (Ops.removeFirst s p).2 q = Ops.view s q ∧
          Ops.count (Ops.removeFirst s p).2 q = Ops.count s q) ∧
      (∀ s p, Ops.ok s p → Ops.count s p = (Ops.view s p).length)

/- The pinned readable form of CORE-070: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CORE_070 : {N T : Type} → MarkingOps N T → Prop :=
fun {N T} Ops =>
  (∀ (P : List N), ∃ s, (∀ p ∈ P, Ops.ok s p) ∧ ∀ (q : N), Ops.view s q = [] ∧ Ops.count s q = 0) ∧
    (∀ (p : N), Ops.view Ops.empty p = [] ∧ Ops.count Ops.empty p = 0) ∧
      (∀ (s : Ops.σ) (p : N) (x : T),
          Ops.ok s p →
            Ops.view (Ops.add s p x) p = Ops.view s p ++ [x] ∧
              Ops.count (Ops.add s p x) p = Ops.count s p + 1 ∧
                ∀ (q : N),
                  Ops.ok s q →
                    Ops.ok (Ops.add s p x) q ∧
                      (q ≠ p →
                        Ops.view (Ops.add s p x) q = Ops.view s q ∧ Ops.count (Ops.add s p x) q = Ops.count s q)) ∧
        (∀ (s : Ops.σ) (p : N),
            Ops.ok s p →
              Marked (Ops.count s) p →
                (Ops.removeFirst s p).1 = (Ops.view s p).head? ∧
                  Ops.view (Ops.removeFirst s p).2 p = (Ops.view s p).tail ∧
                    Ops.count (Ops.removeFirst s p).2 p = Ops.count s p - 1 ∧
                      ∀ (q : N),
                        Ops.ok s q →
                          Ops.ok (Ops.removeFirst s p).2 q ∧
                            (q ≠ p →
                              Ops.view (Ops.removeFirst s p).2 q = Ops.view s q ∧
                                Ops.count (Ops.removeFirst s p).2 q = Ops.count s q)) ∧
          (∀ (s : Ops.σ) (p : N),
              Ops.ok s p →
                ¬Marked (Ops.count s) p →
                  (Ops.removeFirst s p).1 = none ∧
                    ∀ (q : N),
                      Ops.ok s q →
                        Ops.ok (Ops.removeFirst s p).2 q ∧
                          Ops.view (Ops.removeFirst s p).2 q = Ops.view s q ∧
                            Ops.count (Ops.removeFirst s p).2 q = Ops.count s q) ∧
            ∀ (s : Ops.σ) (p : N), Ops.ok s p → Ops.count s p = (Ops.view s p).length
-/
#guard_msgs in #print CORE_070

/-! ## The reference satisfies CORE-070 -/

/-- The queue marking of the reference satisfies CORE-070: it holds every place in every state,
`qEmpty` holds the empty queue everywhere, `qAppendOne` appends at the tail of one place,
`removeFirst` returns the head of one place and leaves its tail (`removeFirst_fst`,
`removeFirst_self`, `removeFirst_other`), and the count is the length of the queue (`Counts`). -/
@[evidence holds CORE_070]
theorem CORE_070_reference {N T : Type} [DecidableEq N] : CORE_070 (refQOps (N := N) (T := T)) := by
  refine ⟨fun _ => ⟨qEmpty, fun _ _ => trivial, fun _ => ⟨rfl, rfl⟩⟩, fun _ => ⟨rfl, rfl⟩,
    ?_, ?_, ?_, fun _ _ _ => rfl⟩
  · intro s p x _
    refine ⟨by simp [refQOps, qAppendOne], by simp [refQOps, qAppendOne, Counts, qCount], ?_⟩
    intro q _
    exact ⟨trivial, fun hq =>
      ⟨by simp [refQOps, qAppendOne, hq], by simp [refQOps, qAppendOne, Counts, qCount, hq]⟩⟩
  · intro s p _ _
    refine ⟨rfl, removeFirst_self s p, removeFirst_count s p, ?_⟩
    intro q _
    exact ⟨trivial, fun hq => ⟨removeFirst_other s hq, by
      show ((removeFirst s p).2 q).length = (s q).length
      rw [removeFirst_other s hq]⟩⟩
  · intro s p _ hm
    have h0 : s p = [] := by
      have : (s p).length = 0 := by
        by_contra h
        exact hm h
      exact List.eq_nil_of_length_eq_zero this
    refine ⟨by simp [refQOps, removeFirst, Head, h0], fun q _ => ⟨trivial, ?_⟩⟩
    by_cases hq : q = p
    · subst hq
      have h1 : (removeFirst s q).2 q = s q := by rw [removeFirst_self, h0]; rfl
      exact ⟨h1, by
        show ((removeFirst s q).2 q).length = (s q).length
        rw [h1]⟩
    · exact ⟨removeFirst_other s hq, by
        show ((removeFirst s p).2 q).length = (s q).length
        rw [removeFirst_other s hq]⟩

/-- A firing's deposit is CORE-070's `add`, one token at a time, in emission order: the queue
marking a reference queue firing leaves is the consumed marking with every emitted token added
by `refQOps.add`. So the marking operations of this block are the ones the firing relation of
EXEC-010 to EXEC-020 steps with. -/
theorem refQFire_deposit_adds {N T : Type} [DecidableEq N] {t : Trans N}
    {M M' : QueueMarking N T} {δ : Delivered N T} {e : List (N × T)}
    (h : RefQFire t M δ e M') :
    M' = e.foldl (fun M x => (refQOps (N := N) (T := T)).add M x.1 x.2) (qConsume M t) := by
  rw [h.2.2.2]
  rfl

/-! ## Consequences: sequences of operations

The closure clauses make the operation lines chain. These theorems hold of every store that
satisfies CORE-070, not only of the reference. -/

/-- A sequence of marking operations: `inl (p, x)` adds `x` to `p`, `inr p` removes the first
token of `p`. -/
def core070_run {N T : Type} (Ops : MarkingOps N T) (s : Ops.σ) (os : List ((N × T) ⊕ N)) :
    Ops.σ :=
  os.foldl (fun s o => match o with
    | .inl (p, x) => Ops.add s p x
    | .inr p => (Ops.removeFirst s p).2) s

/-- The place an operation names. -/
def core070_target {N T : Type} : (N × T) ⊕ N → N
  | .inl (p, _) => p
  | .inr p => p

/-- Every marking reached from a marking that holds the places `P`, by adds and removals on
places of `P`, still holds every place of `P`: with the first line, every marking reached from
the empty marking of a net holds a queue for each place of the net (the third quoted sentence,
read on reachable markings). -/
theorem CORE_070_reach {N T : Type} {Ops : MarkingOps N T} (h : CORE_070 Ops) (P : List N) :
    ∀ (os : List ((N × T) ⊕ N)) (s : Ops.σ), (∀ p ∈ P, Ops.ok s p) →
      (∀ o ∈ os, core070_target o ∈ P) → ∀ p ∈ P, Ops.ok (core070_run Ops s os) p
  | [], _, hs, _ => hs
  | o :: os, s, hs, ho => by
    have ht : core070_target o ∈ P := ho o (List.mem_cons_self ..)
    have hs1 : ∀ p ∈ P, Ops.ok (core070_run Ops s [o]) p := by
      intro q hq
      match o, ht with
      | .inl (p, x), ht => exact ((h.2.2.1 s p x (hs p ht)).2.2 q (hs q hq)).1
      | .inr p, ht =>
        by_cases hm : Marked (Ops.count s) p
        · exact ((h.2.2.2.1 s p (hs p ht) hm).2.2.2 q (hs q hq)).1
        · exact ((h.2.2.2.2.1 s p (hs p ht) hm).2 q (hs q hq)).1
    exact CORE_070_reach h P os (core070_run Ops s [o]) hs1
      (fun o' ho' => ho o' (List.mem_cons_of_mem _ ho'))

/-- From a marking that holds the places `P`, a sequence of adds to places of `P` keeps every
place of `P` held and leaves at each place of `P` its queue followed by the tokens added there,
in the order added. -/
theorem CORE_070_adds {N T : Type} [DecidableEq N] {Ops : MarkingOps N T} (h : CORE_070 Ops)
    (P : List N) : ∀ (e : List (N × T)) (s : Ops.σ), (∀ p ∈ P, Ops.ok s p) →
      (∀ x ∈ e, x.1 ∈ P) →
      (∀ p ∈ P, Ops.ok (e.foldl (fun s x => Ops.add s x.1 x.2) s) p) ∧
      ∀ p ∈ P, Ops.view (e.foldl (fun s x => Ops.add s x.1 x.2) s) p =
        Ops.view s p ++ EmittedTo e p
  | [], _, hs, _ => ⟨hs, fun p _ => by simp [EmittedTo, qEmittedTo]⟩
  | (a, x) :: t, s, hs, he => by
    have ha : a ∈ P := he (a, x) (List.mem_cons_self ..)
    have hadd := h.2.2.1 s a x (hs a ha)
    have hs1 : ∀ p ∈ P, Ops.ok (Ops.add s a x) p := fun p hp => (hadd.2.2 p (hs p hp)).1
    have ih := CORE_070_adds h P t (Ops.add s a x) hs1
      (fun y hy => he y (List.mem_cons_of_mem _ hy))
    refine ⟨ih.1, fun p hp => ?_⟩
    rw [List.foldl_cons, ih.2 p hp]
    by_cases hpa : p = a
    · subst hpa
      rw [hadd.1]
      simp [EmittedTo, qEmittedTo]
    · have hap : ¬ a = p := fun h => hpa h.symm
      rw [((hadd.2.2 p (hs p hp)).2 hpa).1]
      simp [EmittedTo, qEmittedTo, hap]

/-- First in, first out across a sequence of operations: from an empty marking that holds the
places `P`, after a sequence of adds to places of `P`, removing the first token of a place
returns the first token added there, leaves the others in the order added, and keeps every
place of `P` held. -/
theorem CORE_070_fifo {N T : Type} [DecidableEq N] {Ops : MarkingOps N T} (h : CORE_070 Ops)
    (P : List N) (e : List (N × T)) {s : Ops.σ} (hs : ∀ p ∈ P, Ops.ok s p)
    (hz : ∀ q, Ops.view s q = []) (he : ∀ x ∈ e, x.1 ∈ P) {p : N} (hp : p ∈ P) {y : T}
    {ys : List T} (hy : EmittedTo e p = y :: ys) :
    (Ops.removeFirst (e.foldl (fun s x => Ops.add s x.1 x.2) s) p).1 = some y ∧
      Ops.view (Ops.removeFirst (e.foldl (fun s x => Ops.add s x.1 x.2) s) p).2 p = ys ∧
      ∀ q ∈ P, Ops.ok (Ops.removeFirst (e.foldl (fun s x => Ops.add s x.1 x.2) s) p).2 q := by
  obtain ⟨hok, hv⟩ := CORE_070_adds h P e s hs he
  have hvp : Ops.view (e.foldl (fun s x => Ops.add s x.1 x.2) s) p = y :: ys := by
    simp [hv p hp, hz, hy]
  have hc := h.2.2.2.2.2 _ p (hok p hp)
  have hm : Marked (Ops.count (e.foldl (fun s x => Ops.add s x.1 x.2) s)) p := by
    unfold Marked
    rw [hc, hvp]
    simp
  have hr := h.2.2.2.1 _ p (hok p hp) hm
  refine ⟨?_, ?_, fun q hq => (hr.2.2.2 q (hok q hq)).1⟩
  · rw [hr.1, hvp]
    rfl
  · rw [hr.2.1, hvp]
    rfl

/-- The test derivation, for every store that satisfies CORE-070: from an empty marking that
holds `p` (the empty marking of a net containing `p`, which the first line provides), three
tokens added to `p` give count 3, and removing one returns the first token added and leaves
count 2. -/
@[evidence cites "CORE-070" "the test derivation (create an empty marking, add 3 tokens to place P, the count is 3, remove one, the count is 2) follows from the statement for every store, from the empty marking of any net containing P, and the token removed is the first one added"]
theorem CORE_070_derivation {N T : Type} [DecidableEq N] {Ops : MarkingOps N T}
    (h : CORE_070 Ops) {s : Ops.σ} {p : N} (hs : Ops.ok s p) (hz : ∀ q, Ops.view s q = [])
    (a b c : T) :
    Ops.count (Ops.add (Ops.add (Ops.add s p a) p b) p c) p = 3 ∧
      (Ops.removeFirst (Ops.add (Ops.add (Ops.add s p a) p b) p c) p).1 = some a ∧
      Ops.count (Ops.removeFirst (Ops.add (Ops.add (Ops.add s p a) p b) p c) p).2 p = 2 := by
  obtain ⟨hok, hv⟩ := CORE_070_adds h [p] [(p, a), (p, b), (p, c)] s (by simpa using hs)
    (by simp)
  have hv3 : Ops.view (Ops.add (Ops.add (Ops.add s p a) p b) p c) p = [a, b, c] := by
    have := hv p (List.mem_singleton_self p)
    simpa [hz, EmittedTo, qEmittedTo] using this
  have hok3 : Ops.ok (Ops.add (Ops.add (Ops.add s p a) p b) p c) p :=
    hok p (List.mem_singleton_self p)
  have hc3 := h.2.2.2.2.2 _ p hok3
  rw [hv3] at hc3
  have hm : Marked (Ops.count (Ops.add (Ops.add (Ops.add s p a) p b) p c)) p := by
    unfold Marked
    rw [hc3]
    simp
  have hr := h.2.2.2.1 _ p hok3 hm
  refine ⟨hc3, ?_, ?_⟩
  · rw [hr.1, hv3]
    rfl
  · rw [hr.2.2.1, hc3]
    simp

/-! ## The precompiled ring pool satisfies CORE-070 -/

/-- A well-formed ring pool over the places `0 … p`: one free slot per place, at offset `q`. -/
def core070_onePerPlace (p : PlaceId) : Pool where
  pool _ := none
  len := p + 1
  offset q := q
  head _ := 0
  tail _ := 0
  cnt _ := 0
  cap _ := 1
  nplaces := p + 1

theorem core070_onePerPlace_wf (p : PlaceId) : Pool.WF (core070_onePerPlace p) := by
  constructor
  · intro q _; simp [core070_onePerPlace]
  · intro q _; simp [core070_onePerPlace]
  · intro q _; simp [core070_onePerPlace]
  · intro q _; simp [core070_onePerPlace, ringPos]
  · intro q hq; simp [core070_onePerPlace] at hq ⊢; omega
  · intro q _ i hi; simp [core070_onePerPlace] at hi
  · intro q _ i _ _; simp [core070_onePerPlace]
  · intro q r hq hr hne; simp [core070_onePerPlace]; omega

/-- Every place of a list is at most the largest one. -/
theorem core070_le_max : ∀ (P : List PlaceId) (p : PlaceId), p ∈ P → p ≤ P.foldr max 0
  | [], _, h => absurd h List.not_mem_nil
  | a :: t, p, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (core070_le_max t p h) (Nat.le_max_right _ _)

/-- On a well-formed pool, a place with count 0 projects to the empty queue. -/
theorem core070_proj_of_cnt_zero {s : Pool} {p : PlaceId} (h : s.cnt p = 0) : s.proj p = [] := by
  unfold Pool.proj
  rw [h]
  rfl

/-- The ring pool as a marking: `refRingStore` (CONC-022's store) with its removal guarded by
the count, as every caller of `ring_remove_first` is: on an unmarked place it returns no token
and leaves the pool as it is. -/
def core070_ringMarking : MarkingOps PlaceId Colour :=
  { refRingStore with
    removeFirst := fun s p => if s.cnt p = 0 then (none, s) else refRingStore.removeFirst s p }

/-- The precompiled backend's flat ring pool satisfies CORE-070, with the removal its callers
perform (`core070_ringMarking`): the empty marking of a net is a pool with one ring per place
id, `Pool.addLast` appends at the tail through the grow path (`addLast_proj_self`) and keeps the
pool well formed (`addLast_wf`), `Pool.removeFirst` on a marked place drops the head
(`removeFirst_proj_self`), returns it (`peekFirst_eq_head`) and keeps the pool well formed
(`removeFirst_wf`), both leave every other place of the pool as it is, and the stored count is
the length of the projected queue (`proj_length`). So the ring buffer per place is a FIFO queue
per place. -/
@[evidence cites "CORE-070" "the second quoted sentence ('Internally, each place maps to a FIFO queue of tokens') for the precompiled backend's flat ring pool (Libpetri.Pool, refRingStore), the store CONC-022 states the same interface over: its Lean model, with the removal guarded by the count as every caller of ring_remove_first does, satisfies the whole block"]
theorem CORE_070_ringStore : CORE_070 core070_ringMarking := by
  refine ⟨fun P => ⟨core070_onePerPlace (P.foldr max 0), fun p hp =>
      ⟨core070_onePerPlace_wf _, by
        show p < P.foldr max 0 + 1
        exact Nat.lt_succ_of_le (core070_le_max P p hp)⟩,
      fun _ => ⟨core070_proj_of_cnt_zero rfl, rfl⟩⟩,
    fun p => ⟨core070_proj_of_cnt_zero rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · rintro s p x ⟨hwf, hp⟩
    have hwf' := Pool.addLast_wf hwf hp x
    have hn : (s.addLast p x).nplaces = s.nplaces := by
      unfold Pool.addLast; split <;> simp
    refine ⟨Pool.addLast_proj_self hwf hp x, ?_, ?_⟩
    · show (s.addLast p x).cnt p = s.cnt p + 1
      have h1 := Pool.proj_length hwf' (p := p) (by rw [hn]; exact hp)
      have h2 := Pool.proj_length hwf hp
      rw [Pool.addLast_proj_self hwf hp x] at h1
      simp at h1
      omega
    · rintro q ⟨-, hqn⟩
      refine ⟨⟨hwf', by show q < (s.addLast p x).nplaces; rw [hn]; exact hqn⟩, fun hq => ?_⟩
      refine ⟨Pool.addLast_proj_other hwf hp hqn hq x, ?_⟩
      show (s.addLast p x).cnt q = s.cnt q
      have h1 := Pool.proj_length hwf' (p := q) (by rw [hn]; exact hqn)
      have h2 := Pool.proj_length hwf hqn
      rw [Pool.addLast_proj_other hwf hp hqn hq x] at h1
      omega
  · rintro s p ⟨hwf, hp⟩ hm
    have hc : 0 < s.cnt p := Nat.pos_of_ne_zero hm
    have hm' : s.cnt p ≠ 0 := hm
    have he : core070_ringMarking.removeFirst s p = (s.peekFirst p, s.removeFirst p) := by
      simp [core070_ringMarking, refRingStore, hm']
    rw [he]
    refine ⟨Pool.peekFirst_eq_head hwf hp, Pool.removeFirst_proj_self hwf hp hc,
      Pool.removeFirst_cnt_self s p, ?_⟩
    rintro q ⟨-, hqn⟩
    exact ⟨⟨Pool.removeFirst_wf hwf hp hc, by
        show q < (s.removeFirst p).nplaces
        rw [Pool.removeFirst_nplaces]
        exact hqn⟩,
      fun hq => ⟨Pool.removeFirst_proj_other hwf hp hqn hq, Pool.removeFirst_cnt_other s hq⟩⟩
  · rintro s p ⟨hwf, hp⟩ hm
    have h0 : s.cnt p = 0 := by
      by_contra h
      exact hm h
    have he : core070_ringMarking.removeFirst s p = (none, s) := by
      simp [core070_ringMarking, h0]
    rw [he]
    exact ⟨rfl, fun q hq => ⟨hq, rfl, rfl⟩⟩
  · rintro s p ⟨hwf, hp⟩
    exact (Pool.proj_length hwf hp).symm

/-- The glossary ring store's designated empty marking, the pool over no place, holds no place:
the empty marking of a net is the pool sized to it, which the first line provides. -/
theorem core070_ringEmpty_holds_none (p : PlaceId) :
    ¬ refRingStore.ok refRingStore.empty p :=
  fun h => Nat.not_lt_zero p h.2

/-- A well-formed pool over place `0` with an empty ring of two slots. -/
def core070_twoSlot : Pool where
  pool _ := none
  len := 2
  offset _ := 0
  head _ := 0
  tail _ := 0
  cnt _ := 0
  cap _ := 2
  nplaces := 1

theorem core070_twoSlot_wf : Pool.WF core070_twoSlot := by
  constructor
  · intro q _; simp [core070_twoSlot]
  · intro q _; simp [core070_twoSlot]
  · intro q _; simp [core070_twoSlot]
  · intro q _; simp [core070_twoSlot, ringPos]
  · intro q _; simp [core070_twoSlot]
  · intro q _ i hi; simp [core070_twoSlot] at hi
  · intro q _ i _ _; simp [core070_twoSlot]
  · intro q r hq hr hne; simp [core070_twoSlot] at hq hr; omega

/-- The unguarded model of `ring_remove_first` on an unmarked place advances the head index and
leaves a pool that is no longer well formed (its cached tail no longer follows the head). The
Rust operation is never called there (it would panic), which is why `CORE_070_ringStore` checks
the guarded removal its callers perform. -/
theorem core070_ringRaw_unmarked_breaks :
    refRingStore.ok core070_twoSlot 0 ∧ ¬ Marked (refRingStore.count core070_twoSlot) 0 ∧
      ¬ refRingStore.ok (refRingStore.removeFirst core070_twoSlot 0).2 0 := by
  refine ⟨⟨core070_twoSlot_wf, by decide⟩, by decide, fun h => ?_⟩
  have := h.1.tail_eq 0 (by decide)
  exact absurd this (by decide)

/-! ## Wrong stores -/

/-- A stack: `add` puts the token at the head of the place. -/
def core070_stackOps : MarkingOps Nat Nat :=
  { refQOps with add := fun M p x q => if q = p then x :: M q else M q }

/-- ✗ A stack violates CORE-070 (the add line): adding `1` to a place holding `[0]` gives
`[1, 0]`, not `[0, 1]`. -/
@[evidence forbids CORE_070]
theorem CORE_070_forbids_stack : ¬ CORE_070 core070_stackOps := by
  intro h
  have := (h.2.2.1 (fun _ => [0]) 0 1 trivial).1
  exact absurd this (by decide)

/-- An add that also writes the next place. -/
def core070_leakyOps : MarkingOps Nat Nat :=
  { refQOps with add := fun M p x q => if q = p ∨ q = p + 1 then M q ++ [x] else M q }

/-- ✗ An add that writes another place violates CORE-070 (the add line, other places): adding
to place `0` changes place `1`. -/
@[evidence forbids CORE_070]
theorem CORE_070_forbids_leaky : ¬ CORE_070 core070_leakyOps := by
  intro h
  have := (((h.2.2.1 (fun _ => []) 0 7 trivial).2.2 1 trivial).2 (by decide)).1
  exact absurd this (by decide)

/-- Last in, first out: `removeFirst` returns and drops the newest token. -/
def core070_lifoOps : MarkingOps Nat Nat :=
  { refQOps with
    removeFirst := fun M p => ((M p).getLast?, fun q => if q = p then (M q).dropLast else M q) }

/-- ✗ A last-in first-out removal violates CORE-070 (the removal line): from `[0, 1]` it returns
`1`, not the head `0`. -/
@[evidence forbids CORE_070]
theorem CORE_070_forbids_lifo : ¬ CORE_070 core070_lifoOps := by
  intro h
  have := (h.2.2.2.1 (fun _ => [0, 1]) 0 trivial (by decide)).1
  exact absurd this (by decide)

/-- Removing from an unmarked place empties the whole marking. -/
def core070_clearOps : MarkingOps Nat Nat :=
  { refQOps with
    removeFirst := fun M p => if M p = [] then (none, qEmpty) else removeFirst M p }

/-- ✗ A removal from an unmarked place that changes another place violates CORE-070 (the
unmarked removal line): place `1` loses its token. -/
@[evidence forbids CORE_070]
theorem CORE_070_forbids_clear : ¬ CORE_070 core070_clearOps := by
  intro h
  have := ((h.2.2.2.2.1 (fun q => if q = 0 then [] else [5]) 0 trivial (by decide)).2 1
    trivial).2.1
  exact absurd this (by decide)

/-- A count of marked places: `1` for a marked place, `0` otherwise. -/
def core070_placesOps : MarkingOps Nat Nat :=
  { refQOps with count := fun M p => if M p = [] then 0 else 1 }

/-- ✗ Counting marked places instead of tokens violates CORE-070 (the count line): a place
holding two tokens has count `1`. -/
@[evidence forbids CORE_070]
theorem CORE_070_forbids_places : ¬ CORE_070 core070_placesOps := by
  intro h
  have := h.2.2.2.2.2 (fun _ => [0, 1]) 0 trivial
  exact absurd this (by decide)

/-- An empty marking that holds one token in every place. -/
def core070_seededOps : MarkingOps Nat Nat :=
  { refQOps with empty := fun _ => [0] }

/-- ✗ An empty marking with a token violates CORE-070 (the empty line). -/
@[evidence forbids CORE_070]
theorem CORE_070_forbids_seeded : ¬ CORE_070 core070_seededOps := by
  intro h
  exact absurd (h.2.1 0).1 (by decide)

/-- A store that holds no place. -/
def core070_noPlaceOps : MarkingOps Nat Nat :=
  { refQOps with ok := fun _ _ => False }

/-- ✗ A store that holds no place violates CORE-070 (the first line). -/
@[evidence forbids CORE_070]
theorem CORE_070_forbids_noPlace : ¬ CORE_070 core070_noPlaceOps := by
  intro h
  obtain ⟨_, hs, _⟩ := h.1 [0]
  exact hs 0 (List.mem_singleton_self 0)

/-- A store whose every state holds exactly one place, the one it is tagged with: each place is
held by some state, but no state holds two places. -/
def core070_onePlaceOps : MarkingOps Nat Nat where
  σ := QueueMarking Nat Nat × Nat
  ok s p := s.2 = p
  view s := s.1
  empty := (qEmpty, 0)
  add s p x := (qAppendOne s.1 p x, s.2)
  removeFirst s p := ((removeFirst s.1 p).1, ((removeFirst s.1 p).2, s.2))
  peek s p := Head s.1 p
  count s := Counts s.1

/-- ✗ A store whose states each hold one place violates CORE-070 (the first line): no marking
holds both places of a net with places `0` and `1`. -/
@[evidence forbids CORE_070]
theorem CORE_070_forbids_onePlace : ¬ CORE_070 core070_onePlaceOps := by
  intro h
  obtain ⟨s, hs, _⟩ := h.1 [0, 1]
  have h0 : s.2 = 0 := hs 0 (by simp)
  have h1 : s.2 = 1 := hs 1 (by simp)
  omega

/-- A fixed-capacity ring per place, four slots and no grow path: an add to a full ring drops
the token, and the store holds a place only while its ring has a free slot. -/
def core070_fixedRingOps : MarkingOps Nat Nat :=
  { refQOps with
    ok := fun M p => (M p).length < 4
    add := fun M p x => if (M p).length < 4 then qAppendOne M p x else M }

/-- ✗ A fixed-capacity ring violates CORE-070 (the add line's closure clause): adding a fourth
token to place `0` leaves a marking that no longer holds place `0`, so the fifth would be lost. -/
@[evidence forbids CORE_070]
theorem CORE_070_forbids_fixedRing : ¬ CORE_070 core070_fixedRingOps := by
  intro h
  have hok : core070_fixedRingOps.ok (fun _ => [1, 2, 3]) 0 := by
    show ([1, 2, 3] : List Nat).length < 4
    decide
  have := ((h.2.2.1 (fun _ => [1, 2, 3]) 0 4 hok).2.2 0 hok).1
  exact absurd this (by
    show ¬ (core070_fixedRingOps.add (fun _ => [1, 2, 3]) 0 4 0).length < 4
    decide)

/-- A map store that keeps an entry only for a marked place and holds a place only while its
queue is not empty; its removal from a place with no entry resets the whole map. -/
def core070_mapDropOps : MarkingOps Nat Nat :=
  { refQOps with
    ok := fun M p => M p ≠ []
    removeFirst := fun M p => if M p = [] then (none, qEmpty) else removeFirst M p }

/-- ✗ A map store that drops a place's entry when its removal empties it violates CORE-070 (the
marked removal line's closure clause): removing the only token of place `0` leaves a marking
that no longer holds place `0`. -/
@[evidence forbids CORE_070]
theorem CORE_070_forbids_mapDrop : ¬ CORE_070 core070_mapDropOps := by
  intro h
  have hok : core070_mapDropOps.ok (fun _ => [5]) 0 := List.cons_ne_nil 5 []
  have := ((h.2.2.2.1 (fun _ => [5]) 0 hok (by decide)).2.2.2 0 hok).1
  exact this (by decide)

/-! ## Mutant readings -/

/-- Mutant reading of CORE-070 without the first line: the operation lines for the places a
state holds, with no place required to be held. -/
def CORE_070_mutant_dropPlaces {N T : Type} (Ops : MarkingOps N T) : Prop :=
  (∀ p, Ops.view Ops.empty p = [] ∧ Ops.count Ops.empty p = 0) ∧
  (∀ s p x, Ops.ok s p →
    Ops.view (Ops.add s p x) p = Ops.view s p ++ [x] ∧
    Ops.count (Ops.add s p x) p = Ops.count s p + 1 ∧
    ∀ q, Ops.ok s q →
      Ops.ok (Ops.add s p x) q ∧
      (q ≠ p → Ops.view (Ops.add s p x) q = Ops.view s q ∧
        Ops.count (Ops.add s p x) q = Ops.count s q)) ∧
  (∀ s p, Ops.ok s p → Marked (Ops.count s) p →
    (Ops.removeFirst s p).1 = (Ops.view s p).head? ∧
    Ops.view (Ops.removeFirst s p).2 p = (Ops.view s p).tail ∧
    Ops.count (Ops.removeFirst s p).2 p = Ops.count s p - 1 ∧
    ∀ q, Ops.ok s q →
      Ops.ok (Ops.removeFirst s p).2 q ∧
      (q ≠ p → Ops.view (Ops.removeFirst s p).2 q = Ops.view s q ∧
        Ops.count (Ops.removeFirst s p).2 q = Ops.count s q)) ∧
  (∀ s p, Ops.ok s p → ¬ Marked (Ops.count s) p →
    (Ops.removeFirst s p).1 = none ∧
    ∀ q, Ops.ok s q →
      Ops.ok (Ops.removeFirst s p).2 q ∧
      Ops.view (Ops.removeFirst s p).2 q = Ops.view s q ∧
      Ops.count (Ops.removeFirst s p).2 q = Ops.count s q) ∧
  (∀ s p, Ops.ok s p → Ops.count s p = (Ops.view s p).length)

/-- The store that holds no place kills the first mutant: every operation line is vacuous for
it and its empty marking is the reference one, so it satisfies the mutant, but not CORE-070. -/
@[evidence mutant CORE_070]
theorem CORE_070_mutant_dropPlaces_killed :
    CORE_070_mutant_dropPlaces core070_noPlaceOps ∧ ¬ CORE_070 core070_noPlaceOps :=
  ⟨⟨fun _ => ⟨rfl, rfl⟩, fun _ _ _ h => h.elim, fun _ _ h => h.elim, fun _ _ h => h.elim,
    fun _ _ h => h.elim⟩, CORE_070_forbids_noPlace⟩

/-- Mutant reading of CORE-070 whose first line asks only that each place be held by some
empty state, not that one empty state hold all the places of a net. -/
def CORE_070_mutant_somePlace {N T : Type} (Ops : MarkingOps N T) : Prop :=
  (∀ p, ∃ s, Ops.ok s p ∧ ∀ q, Ops.view s q = [] ∧ Ops.count s q = 0) ∧
  CORE_070_mutant_dropPlaces Ops

/-- The store whose states each hold one place kills the second mutant: every place is held by
an empty state tagged with it and every operation keeps the tag, so it satisfies the mutant, but
no state holds two places, so it violates CORE-070. -/
@[evidence mutant CORE_070]
theorem CORE_070_mutant_somePlace_killed :
    CORE_070_mutant_somePlace core070_onePlaceOps ∧ ¬ CORE_070 core070_onePlaceOps := by
  refine ⟨⟨fun p => ⟨(qEmpty, p), rfl, fun _ => ⟨rfl, rfl⟩⟩, fun _ => ⟨rfl, rfl⟩, ?_, ?_, ?_,
    fun _ _ _ => rfl⟩, CORE_070_forbids_onePlace⟩
  · rintro ⟨M, t⟩ p x _
    refine ⟨by simp [core070_onePlaceOps, qAppendOne],
      by simp [core070_onePlaceOps, qAppendOne, Counts, qCount], fun q hq => ⟨hq, fun hqp => ?_⟩⟩
    exact ⟨by simp [core070_onePlaceOps, qAppendOne, hqp],
      by simp [core070_onePlaceOps, qAppendOne, Counts, qCount, hqp]⟩
  · rintro ⟨M, t⟩ p _ _
    refine ⟨rfl, removeFirst_self M p, removeFirst_count M p, fun q hq => ⟨hq, fun hqp => ?_⟩⟩
    exact ⟨removeFirst_other M hqp, by
      show ((removeFirst M p).2 q).length = (M q).length
      rw [removeFirst_other M hqp]⟩
  · rintro ⟨M, t⟩ p _ hm
    have h0 : M p = [] := by
      have : (M p).length = 0 := by
        by_contra h
        exact hm h
      exact List.eq_nil_of_length_eq_zero this
    refine ⟨by simp [core070_onePlaceOps, removeFirst, Head, h0], fun q hq => ⟨hq, ?_⟩⟩
    by_cases hqp : q = p
    · subst hqp
      have h1 : (removeFirst M q).2 q = M q := by rw [removeFirst_self, h0]; rfl
      exact ⟨h1, by
        show ((removeFirst M q).2 q).length = (M q).length
        rw [h1]⟩
    · exact ⟨removeFirst_other M hqp, by
        show ((removeFirst M p).2 q).length = (M q).length
        rw [removeFirst_other M hqp]⟩

/-- Mutant reading of CORE-070 without the closure clauses (the block's earlier form): each
place is held by some state, and the operation lines constrain one step from a state that holds
the place, without asking that the resulting state still hold it. -/
def CORE_070_mutant_noClosure {N T : Type} (Ops : MarkingOps N T) : Prop :=
  (∀ p, ∃ s, Ops.ok s p) ∧
  (∀ p, Ops.view Ops.empty p = [] ∧ Ops.count Ops.empty p = 0) ∧
  (∀ s p x, Ops.ok s p →
    Ops.view (Ops.add s p x) p = Ops.view s p ++ [x] ∧
    Ops.count (Ops.add s p x) p = Ops.count s p + 1 ∧
    ∀ q, q ≠ p → Ops.ok s q →
      Ops.view (Ops.add s p x) q = Ops.view s q ∧
      Ops.count (Ops.add s p x) q = Ops.count s q) ∧
  (∀ s p, Ops.ok s p → Marked (Ops.count s) p →
    (Ops.removeFirst s p).1 = (Ops.view s p).head? ∧
    Ops.view (Ops.removeFirst s p).2 p = (Ops.view s p).tail ∧
    Ops.count (Ops.removeFirst s p).2 p = Ops.count s p - 1 ∧
    ∀ q, q ≠ p → Ops.ok s q →
      Ops.view (Ops.removeFirst s p).2 q = Ops.view s q ∧
      Ops.count (Ops.removeFirst s p).2 q = Ops.count s q) ∧
  (∀ s p, Ops.ok s p → ¬ Marked (Ops.count s) p →
    (Ops.removeFirst s p).1 = none ∧
    ∀ q, Ops.ok s q →
      Ops.view (Ops.removeFirst s p).2 q = Ops.view s q ∧
      Ops.count (Ops.removeFirst s p).2 q = Ops.count s q) ∧
  (∀ s p, Ops.ok s p → Ops.count s p = (Ops.view s p).length)

/-- The fixed-capacity ring kills the third mutant: each add from a ring with a free slot
appends at the tail, so it satisfies the mutant, but the fourth add leaves a ring the store no
longer holds, so it violates CORE-070. Without the closure clause the precompiled ring with no
grow path (CONC-022) would pass. -/
@[evidence mutant CORE_070]
theorem CORE_070_mutant_noClosure_ring :
    CORE_070_mutant_noClosure core070_fixedRingOps ∧ ¬ CORE_070 core070_fixedRingOps := by
  refine ⟨⟨fun _ => ⟨(qEmpty : QueueMarking Nat Nat), Nat.zero_lt_succ _⟩, fun _ => ⟨rfl, rfl⟩,
    ?_, ?_, ?_, fun _ _ _ => rfl⟩, CORE_070_forbids_fixedRing⟩
  · intro s p x (hp : (s p).length < 4)
    refine ⟨by simp [core070_fixedRingOps, refQOps, qAppendOne, hp],
      by simp [core070_fixedRingOps, refQOps, qAppendOne, Counts, qCount, hp], ?_⟩
    intro q hq _
    exact ⟨by simp [core070_fixedRingOps, refQOps, qAppendOne, hq, hp],
      by simp [core070_fixedRingOps, refQOps, qAppendOne, Counts, qCount, hq, hp]⟩
  · intro s p _ _
    refine ⟨rfl, removeFirst_self s p, removeFirst_count s p, ?_⟩
    intro q hq _
    exact ⟨removeFirst_other s hq, by
      show ((removeFirst s p).2 q).length = (s q).length
      rw [removeFirst_other s hq]⟩
  · intro s p _ hm
    have h0 : s p = [] := by
      have : (s p).length = 0 := by
        by_contra h
        exact hm h
      exact List.eq_nil_of_length_eq_zero this
    refine ⟨by simp [core070_fixedRingOps, refQOps, removeFirst, Head, h0], fun q _ => ?_⟩
    by_cases hq : q = p
    · subst hq
      have h1 : (removeFirst s q).2 q = s q := by rw [removeFirst_self, h0]; rfl
      exact ⟨h1, by
        show ((removeFirst s q).2 q).length = (s q).length
        rw [h1]⟩
    · exact ⟨removeFirst_other s hq, by
        show ((removeFirst s p).2 q).length = (s q).length
        rw [removeFirst_other s hq]⟩

/-- The map store that drops an emptied entry also kills the third mutant: it holds a place
only while the place is marked, so the unmarked removal line never applies and its reset of the
whole map passes the mutant; the closure clause of the marked removal line rules it out. -/
@[evidence mutant CORE_070]
theorem CORE_070_mutant_noClosure_map :
    CORE_070_mutant_noClosure core070_mapDropOps ∧ ¬ CORE_070 core070_mapDropOps := by
  refine ⟨⟨fun _ => ⟨(fun _ => [0] : QueueMarking Nat Nat), List.cons_ne_nil _ _⟩,
    fun _ => ⟨rfl, rfl⟩, ?_, ?_, ?_, fun _ _ _ => rfl⟩, CORE_070_forbids_mapDrop⟩
  · intro s p x _
    refine ⟨by simp [core070_mapDropOps, refQOps, qAppendOne],
      by simp [core070_mapDropOps, refQOps, qAppendOne, Counts, qCount], ?_⟩
    intro q hq _
    exact ⟨by simp [core070_mapDropOps, refQOps, qAppendOne, hq],
      by simp [core070_mapDropOps, refQOps, qAppendOne, Counts, qCount, hq]⟩
  · intro s p (hp : s p ≠ []) _
    have e : core070_mapDropOps.removeFirst s p = removeFirst s p := by
      simp [core070_mapDropOps, hp]
    rw [e]
    refine ⟨rfl, removeFirst_self s p, removeFirst_count s p, ?_⟩
    intro q hq _
    exact ⟨removeFirst_other s hq, by
      show ((removeFirst s p).2 q).length = (s q).length
      rw [removeFirst_other s hq]⟩
  · intro s p (hp : s p ≠ []) hm
    exact absurd (show (s p).length ≠ 0 from fun h => hp (List.eq_nil_of_length_eq_zero h)) hm

/-- Mutant reading of CORE-070 that keeps only the counts of the add line: adding raises the
count of the place by one and leaves every other place as it is, but where the token goes in the
queue is free. -/
def CORE_070_mutant_addCountOnly {N T : Type} (Ops : MarkingOps N T) : Prop :=
  ∀ s p x, Ops.ok s p →
    Ops.count (Ops.add s p x) p = Ops.count s p + 1 ∧
    ∀ q, q ≠ p → Ops.ok s q →
      Ops.view (Ops.add s p x) q = Ops.view s q ∧
      Ops.count (Ops.add s p x) q = Ops.count s q

/-- The stack kills the fourth mutant: it adds one token to the place and touches no other, so
it satisfies the mutant, but it adds at the head, so it violates CORE-070. -/
@[evidence mutant CORE_070]
theorem CORE_070_mutant_addCountOnly_killed :
    CORE_070_mutant_addCountOnly core070_stackOps ∧ ¬ CORE_070 core070_stackOps := by
  refine ⟨fun s p x _ => ⟨?_, fun q hq _ => ?_⟩, CORE_070_forbids_stack⟩
  · simp [core070_stackOps, refQOps, Counts, qCount]
  · simp [core070_stackOps, refQOps, Counts, qCount, hq]

/-- Mutant reading of CORE-070 that keeps only the counts of the marked removal line: removing
lowers the count of the place by one and leaves every other place as it is, but which token is
returned, and which tokens stay, is free. -/
def CORE_070_mutant_removeCountOnly {N T : Type} (Ops : MarkingOps N T) : Prop :=
  ∀ s p, Ops.ok s p → Marked (Ops.count s) p →
    Ops.count (Ops.removeFirst s p).2 p = Ops.count s p - 1 ∧
    ∀ q, q ≠ p → Ops.ok s q →
      Ops.view (Ops.removeFirst s p).2 q = Ops.view s q ∧
      Ops.count (Ops.removeFirst s p).2 q = Ops.count s q

/-- The last-in first-out store kills the fifth mutant: it removes one token from the place and
touches no other, so it satisfies the mutant, but it removes the newest token, so it violates
CORE-070. -/
@[evidence mutant CORE_070]
theorem CORE_070_mutant_removeCountOnly_killed :
    CORE_070_mutant_removeCountOnly core070_lifoOps ∧ ¬ CORE_070 core070_lifoOps := by
  refine ⟨fun s p _ _ => ⟨?_, fun q hq _ => ?_⟩, CORE_070_forbids_lifo⟩
  · simp [core070_lifoOps, refQOps, Counts, qCount]
  · simp [core070_lifoOps, refQOps, Counts, qCount, hq]

/-! ## Nonvacuity: the test derivation on the reference -/

/-- The reference marking after the test derivation's three adds: tokens `1`, `2`, `3` added to
place `0` of the empty marking, in that order. -/
def core070_three : QueueMarking Nat Nat :=
  qAppendOne (qAppendOne (qAppendOne qEmpty 0 1) 0 2) 0 3

/-- CORE-070 bites on the reference, along the test derivation: every place is held, the empty
marking counts 0 at place `0`, three adds give count 3 and the queue `[1, 2, 3]`, the removal
returns the first token added (`1`) and leaves count 2 and the queue `[2, 3]`, and place `1` is
untouched throughout. The lines' premises (`ok`, a marked place, an unmarked place) are all met
on the reference. -/
@[evidence nonvacuous CORE_070]
theorem CORE_070_nonvacuous :
    (∀ s p, (refQOps (N := Nat) (T := Nat)).ok s p) ∧
      refQOps.count (refQOps (N := Nat) (T := Nat)).empty 0 = 0 ∧
      refQOps.count core070_three 0 = 3 ∧ refQOps.view core070_three 0 = [1, 2, 3] ∧
      Marked (refQOps.count core070_three) 0 ∧ ¬ Marked (refQOps.count core070_three) 1 ∧
      (refQOps.removeFirst core070_three 0).1 = some 1 ∧
      refQOps.count (refQOps.removeFirst core070_three 0).2 0 = 2 ∧
      refQOps.view (refQOps.removeFirst core070_three 0).2 0 = [2, 3] ∧
      refQOps.view (refQOps.removeFirst core070_three 0).2 1 = [] := by
  refine ⟨fun _ _ => trivial, ?_⟩
  decide

end Libpetri.Spec
