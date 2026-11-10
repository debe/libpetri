import Libpetri.Reference.Queue
import Libpetri.Spec.Glossary

set_option linter.missingDocs true

/-!
# Queue terms: token order within a firing

The terms the token-order requirements use ([EXEC-010], [EXEC-012], [EXEC-013], [EXEC-020]),
as Lean definitions over the reference queue firing (`Libpetri/Reference/Queue.lean`).
`QueueMarking` quotes the glossary entry "Queue order" (section "Execution" of
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

/-- **Glossary: Queue order.** "The tokens of a place are kept in the order they were added. The
oldest token is the head of the place; a firing consumes from the head, except on a correlated
input of a ν-net match [EXEC-010], [NU-020], and reads the head [EXEC-012], and a deposit adds
at the tail [EXEC-020]."

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

end Libpetri.Spec
