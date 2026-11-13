import Libpetri.Reference.Queue
import Libpetri.Ring.Grow
import Libpetri.Spec.Glossary

set_option linter.missingDocs true

/-!
# Queue terms: token order within a firing

The terms the token-order requirements use ([EXEC-010], [EXEC-012], [EXEC-013], [EXEC-020]),
as Lean definitions over the reference queue firing (`Libpetri/Reference/Queue.lean`).
`QueueMarking` refers to the glossary entry *Queue order* (section "Execution" of
`spec/glossary.md`); the other terms have no glossary entry and quote the requirement sentence
they read. The glossary's "Admitted completion" is not here: a single firing has no completion
to accept, and it belongs to the executor model (`RefExec`). As in `Glossary.lean`, nothing here
redefines the firing. Each term is a
readable name for a definition the reference already has (`qCount`, `qInputs`, `qReads`,
`qEmittedTo`, `qFire`), and the bridge lemmas at the end show that the two agree.

A queue requirement is a predicate over an abstract queue firing relation `Q : QFireRel N T`,
so that it can be checked against the reference (`RefQFire`) and against a mutant. Two
conditions tie such a relation to the count semantics, so that it cannot hold of a relation
that does nothing: `QProjectsTo Q RefFire` (every queue firing, counted, is a reference firing)
and `QCovers Q RefFire` (every reference firing lifts to a queue firing from every queue marking
with those counts, whatever the emitted token values). The reference has both
(`refQFire_projectsTo`, `refQFire_covers`); together they are `count_QFire`.

Ruling D15: a transition with an input arc and a read arc on the same place is rejected when it
is built (`NoInputRead`), so EXEC-012's firing lines and EXEC-013 assume `NoInputRead t`, and
the read terms need not say whether a read sees the queue before or after input consumption.
EXEC-010 and EXEC-020 hold without it.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

variable {N T : Type}

/-! ## Queue markings -/

/-- Glossary: *Queue order* (spec/glossary.md).

A queue marking holds every place's tokens in queue order, the head first; `T` is the type of
token identities. Correlated ν inputs are not modelled (`RefQFire` consumes oldest first from
every input place). -/
abbrev QueueMarking (N T : Type) := QMarking N T

/-- The token counts of a queue marking (glossary: Token count): the length of each queue. -/
abbrev Counts (M : QueueMarking N T) : CountMarking N := qCount M

/-- **Head** (glossary: Queue order, "The oldest token is the head of the place"): the oldest
token of `p`'s queue, `none` when `p` is not marked. -/
def Head (M : QueueMarking N T) (p : N) : Option T := (M p).head?

/-- **Oldest first** ([EXEC-010]): the `k` oldest tokens of `p`'s queue, in FIFO order: the
FIFO prefix of length `k`. -/
def OldestFirst (M : QueueMarking N T) (p : N) (k : Nat) : List T := (M p).take k

/-- **Delivered** ([EXEC-010], [EXEC-012]): what a firing hands its action: the tokens it
consumed from each input place (`inputs`) and the tokens its read arcs peeked (`reads`). -/
abbrev Delivered (N T : Type) := QDelivered N T

/-- **Emitted to** ([EXEC-020]): "Multiple tokens to same place are added in order." The tokens
an emission list `e` (places and tokens, in emission order) sends to `p`, in emission order. -/
abbrev EmittedTo [DecidableEq N] (e : List (N × T)) (p : N) : List T := qEmittedTo e p

/-- **Appended at the tail** ([EXEC-020]): "Each token is added to the end of the target place's
FIFO queue." `M'` holds at `p` the queue `base` held there, followed by the tokens emitted to
`p`, in emission order. -/
def AppendedAtTail [DecidableEq N] (base M' : QueueMarking N T) (e : List (N × T)) (p : N) :
    Prop :=
  M' p = base p ++ EmittedTo e p

/-! ## Marking operations

The operations of a marking that [CORE-070] names (an empty marking, adding a token, removing
one, the count of a place) and that the precompiled token store of [CONC-022] offers by place
id. `MarkingOps` is the one interface both requirements are stated over, so that "add at the
tail, remove the head" has one normative form. It has two registered witnesses: `refQOps`, the
queue marking of `RefQFire` itself, and `refRingStore`, the flat ring pool of `Libpetri.Pool`
(`Ring/Core.lean`, `Ring/Grow.lean`). -/

/-- **Remove first** (glossary: Queue order, "The oldest token is the head of the place";
[CORE-070]): take the head of `p`'s queue. The result is the token removed, `none` when `p` is
not marked, and the queue marking without it; every other place keeps its queue. -/
def removeFirst [DecidableEq N] (M : QueueMarking N T) (p : N) : Option T × QueueMarking N T :=
  (Head M p, fun q => if q = p then (M q).tail else M q)

/-- **Marking operations** ([CORE-070], [CONC-022]): a token store with the operations of a
marking. `σ` is the store's state type and `view` reads the queue each place holds, oldest
first, so that every operation can be stated against queue order (glossary: Queue order).

`ok s p` says that `s` is a well-formed store that holds a queue for `p`. A store whose places
are fixed when the net is compiled (the ring pool, sized per place id) holds queues for those
places only; the queue marking holds one for every place. -/
structure MarkingOps (N T : Type) where
  /-- The state type of the store. -/
  σ : Type
  /-- `s` is a well-formed store and holds a queue for the place. -/
  ok : σ → N → Prop
  /-- The queue each place holds, oldest token first. -/
  view : σ → QueueMarking N T
  /-- The empty store. -/
  empty : σ
  /-- Add a token to a place. -/
  add : σ → N → T → σ
  /-- Remove the first token of a place: the token removed, if any, and the store without it. -/
  removeFirst : σ → N → Option T × σ
  /-- The first token of a place, without removing it. -/
  peek : σ → N → Option T
  /-- The token count of a place. -/
  count : σ → N → Nat

/-- The queue marking as a store ([CORE-070]): the state is the queue marking `RefQFire`
steps, `view` is the identity, `add` is `qAppendOne` (the deposit of one token, [EXEC-020]),
`removeFirst` is `removeFirst`, `peek` is `Head` and `count` is `Counts`. Every place has a
queue. -/
def refQOps [DecidableEq N] : MarkingOps N T where
  σ := QueueMarking N T
  ok _ _ := True
  view M := M
  empty := qEmpty
  add := qAppendOne
  removeFirst M p := removeFirst M p
  peek := Head
  count M := Counts M

#spec_witness refQOps

/-- The empty ring pool: no place, no slot. The precompiled executor sizes one ring per place
id when it compiles the net, so a pool over no place is the only store that holds no token and
needs no net. -/
def emptyPool : Pool where
  pool _ := none
  len := 0
  offset _ := 0
  head _ := 0
  tail _ := 0
  cnt _ := 0
  cap _ := 0
  nplaces := 0

/-- The flat ring pool as a store ([CONC-022]): `Libpetri.Pool`, the field-for-field model of
the precompiled backend's token pool. A place has a queue when the pool is well formed
(`Pool.WF`) and the place id is below `nplaces`; `view` is the refinement map `Pool.proj`; `add`
is `Pool.addLast`, which grows the ring when it is full; `removeFirst` returns `Pool.peekFirst`
and `Pool.removeFirst`; `count` is the stored count `Pool.cnt`. -/
def refRingStore : MarkingOps PlaceId Colour where
  σ := Pool
  ok s p := Pool.WF s ∧ p < s.nplaces
  view := Pool.proj
  empty := emptyPool
  add := Pool.addLast
  removeFirst s p := (s.peekFirst p, s.removeFirst p)
  peek := Pool.peekFirst
  count := Pool.cnt

#spec_witness refRingStore

/-! ## Queue firing relations -/

/-- A queue firing relation: `Q t M δ e M'` says that `t` fires from the queue marking `M`,
delivers `δ` to its action, the action emits `e`, and the firing leaves `M'`. -/
abbrev QFireRel (N T : Type) :=
  Trans N → QueueMarking N T → Delivered N T → List (N × T) → QueueMarking N T → Prop

/-- Every firing of `Q`, counted, is a firing of `F` whose deposit is the emitted places. -/
def QProjectsTo (Q : QFireRel N T) (F : FireRel N) : Prop :=
  ∀ t M δ e M', Q t M δ e M' → F t (Counts M) (e.map Prod.fst) (Counts M')

/-- Every firing of `F` lifts to `Q` from every queue marking with its counts, with every
emission (any token values) whose places are its deposit. -/
def QCovers (Q : QFireRel N T) (F : FireRel N) : Prop :=
  ∀ t M e m', F t (Counts M) (e.map Prod.fst) m' → ∃ δ M', Q t M δ e M' ∧ Counts M' = m'

/-- The reference queue firing (`Reference.RefQFire`), as a `QFireRel`. It is registered as a
witness model in `Reference/Queue.lean`. -/
abbrev RefQFireRel [DecidableEq N] : QFireRel N T := RefQFire

/-! ## Bridge lemmas: the readable forms agree with the reference definitions -/

theorem refQFire_projectsTo [DecidableEq N] : QProjectsTo (RefQFire (N := N) (T := T)) RefFire :=
  fun _ _ _ _ _ h => h.fires

theorem refQFire_covers [DecidableEq N] : QCovers (RefQFire (N := N) (T := T)) RefFire :=
  fun t M e m' h => (count_QFire t M e m').mpr h

/-- A reference queue firing is: enabled on the counts, an offered deposit, the reference
delivery, and the reference result. -/
theorem refQFire_iff [DecidableEq N] (t : Trans N) (M : QueueMarking N T) (δ : Delivered N T)
    (e : List (N × T)) (M' : QueueMarking N T) :
    RefQFire t M δ e M' ↔
      Enabled t (Counts M) ∧
        (∃ ch, deposit (Consumes t (Counts M)) (OutputSpec t) ch = some (e.map Prod.fst)) ∧
        δ = qDelivered M t ∧ M' = qFire M t e := Iff.rfl

/-- The reference delivers, from each place, its `Consumes` oldest tokens ([EXEC-010]). -/
theorem refQFire_inputs [DecidableEq N] {t : Trans N} {M M' : QueueMarking N T}
    {δ : Delivered N T} {e : List (N × T)} (h : RefQFire t M δ e M') (p : N) :
    δ.inputs p = OldestFirst M p (Consumes t (Counts M) p) := by
  rw [h.2.2.1]
  rfl

/-- Under D15 the reference read bag holds the head of the pre-firing queue, once per read arc
on the place ([EXEC-012]). -/
theorem refQFire_reads [DecidableEq N] {t : Trans N} (hw : NoInputRead t)
    {M M' : QueueMarking N T} {δ : Delivered N T} {e : List (N × T)}
    (h : RefQFire t M δ e M') (p : N) :
    δ.reads p = (List.replicate (t.core.reads.count p) (Head M p).toList).flatten := by
  rw [h.2.2.1]
  exact qReads_noInputRead hw M p

/-- The reference result, place by place: a reset place holds exactly what was emitted to it;
every other place keeps its queue without the consumed oldest tokens, then the emitted tokens in
emission order ([EXEC-010], [EXEC-013], [EXEC-020], [CORE-034]). -/
theorem refQFire_apply [DecidableEq N] {t : Trans N} {M M' : QueueMarking N T}
    {δ : Delivered N T} {e : List (N × T)} (h : RefQFire t M δ e M') (p : N) :
    M' p = (if ResetArc t p then [] else (M p).drop (Consumes t (Counts M) p)) ++ EmittedTo e p := by
  rw [h.2.2.2, qFire_apply]
  rfl

/-- On a place with no input arc and no reset arc the reference appends at the tail
([EXEC-020]): the queue is kept, identity and order, and the emitted tokens follow. -/
theorem refQFire_appendedAtTail [DecidableEq N] {t : Trans N} {M M' : QueueMarking N T}
    {δ : Delivered N T} {e : List (N × T)} (h : RefQFire t M δ e M') {p : N}
    (hi : p ∉ inPlaces t) (hr : ¬ ResetArc t p) : AppendedAtTail M M' e p := by
  have hn : nspecAt t.core p = none := by
    unfold nspecAt
    rw [List.find?_eq_none]
    intro s hs he
    have : s.place = p := by simpa using he
    exact hi (List.mem_map.mpr ⟨s, hs, this⟩)
  rw [AppendedAtTail, refQFire_apply h, if_neg hr]
  simp [Consumes, nconsumed, hn]

/-- Under D15 a read place that is not a reset place keeps its queue, identity and order, and
the emitted tokens follow ([EXEC-012]). -/
theorem refQFire_read_kept [DecidableEq N] {t : Trans N} (hw : NoInputRead t)
    {M M' : QueueMarking N T} {δ : Delivered N T} {e : List (N × T)} (h : RefQFire t M δ e M')
    {p : N} (hp : ReadArc t p) (hr : ¬ ResetArc t p) : AppendedAtTail M M' e p := by
  refine refQFire_appendedAtTail h (fun hi => ?_) hr
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hi
  exact hw s hs hp

/-! ## Bridge lemmas: removing the first token -/

/-- `removeFirst` returns the head of the place. -/
theorem removeFirst_fst [DecidableEq N] (M : QueueMarking N T) (p : N) :
    (removeFirst M p).1 = Head M p := rfl

/-- `removeFirst` leaves the place its queue without the head. -/
theorem removeFirst_self [DecidableEq N] (M : QueueMarking N T) (p : N) :
    (removeFirst M p).2 p = (M p).tail := by
  simp [removeFirst]

/-- `removeFirst` leaves every other place as it is. -/
theorem removeFirst_other [DecidableEq N] (M : QueueMarking N T) {p q : N} (h : q ≠ p) :
    (removeFirst M p).2 q = M q := by
  simp [removeFirst, h]

/-- The token removed, followed by the queue left, is the queue before: `removeFirst` keeps the
rest of the place in order. -/
theorem removeFirst_order [DecidableEq N] (M : QueueMarking N T) (p : N) :
    (removeFirst M p).1.toList ++ (removeFirst M p).2 p = M p := by
  rw [removeFirst_fst, removeFirst_self, Head]
  cases M p <;> rfl

/-- `removeFirst` lowers the count of the place by one (none on an unmarked place). -/
theorem removeFirst_count [DecidableEq N] (M : QueueMarking N T) (p : N) :
    Counts (removeFirst M p).2 p = Counts M p - 1 := by
  simp [Counts, qCount, removeFirst_self]

/-! ## The reference delivery off the arcs ([EXEC-010], [EXEC-012]) -/

/-- A firing reads through its read arcs only: the reference delivery holds no read token at a
place that is not a read place of the transition. -/
theorem qDelivered_reads_off [DecidableEq N] (M : QueueMarking N T) (t : Trans N)
    {p : N} (hp : ¬ ReadArc t p) : (qDelivered M t).reads p = [] := by
  show qReads M t p = []
  unfold qReads
  rw [qReadsBag_apply, List.count_eq_zero.mpr hp]
  rfl

/-- A firing consumes through its input arcs only: the reference delivery holds no consumed token
at a place that is not an input place of the transition. -/
theorem qDelivered_inputs_off [DecidableEq N] (M : QueueMarking N T) (t : Trans N)
    {p : N} (hi : p ∉ inPlaces t) : (qDelivered M t).inputs p = [] := by
  have hn : nspecAt t.core p = none := by
    simp only [nspecAt, List.find?_eq_none, decide_eq_true_eq]
    intro s hs hp
    exact hi (List.mem_map.2 ⟨s, hs, hp⟩)
  show qInputs M t p = []
  simp [qInputs, qTake, nconsumed, hn]

end Libpetri.Spec
