import Libpetri.Reference.Semantics
import Libpetri.Refinement.Model
import Libpetri.Spec.Registry

set_option linter.missingDocs true

/-!
# The reference semantics on queue markings: one firing, token by token

`Semantics.lean` fires on **count markings** (`N → Nat`). The token-order requirements
([EXEC-010] oldest-first consumption, [EXEC-012] read peek, [EXEC-013] in-firing order,
[EXEC-020] tail deposit) speak about *which* tokens move, so they need a marking that keeps
every place's FIFO queue: a **queue marking** `QMarking N T := N → List T`, the head of each
list being the oldest token. `T` is an abstract token type (token identities); the examples use
`Nat`.

**One firing** (`RefQFire t M e M'`) of `t` from the queue marking `M`, the action emitting `e`
(a list of `(place, token)` pairs in emission order):

* **Enabled, outcome**: exactly as `Reference.Fires` on the counts `qCount M`: `t` is enabled
  there, and the places of `e` (`e.map Prod.fst`) are a deposit the output spec offers. Token
  values are the action's choice and are not constrained (a forward's kept value, [IO-014] AC5,
  is below this witness).
* **Inputs** ([EXEC-010], [IO-007]): from each input place the firing takes the FIFO prefix of
  length `consumptionCount(available)` (`qInputs`, delivered to the action), leaving the rest
  (`qPostInput`).
* **Reads** ([EXEC-012], [EXEC-013] AC4): each read arc delivers the head of its place **after
  input consumption and before reset draining** (`qReads`). Under ruling D15 a transition never
  has an input arc and a read arc on one place (`NoInputRead`, rejected when the transition is
  built), so on every transition that builds this is the head of the pre-firing queue
  (`qReads_noInputRead`).
* **Resets** ([CORE-034], [EXEC-013]): a reset place is drained after the reads (`qConsume`).
* **Outputs** ([EXEC-020]): each emitted token is appended at the **tail** of its place, in
  emission order (`qAppend`, one `qAppendOne` per emission).

The operations reuse the reference executor's shapes from `Refinement/Model.lean`:
`qPostInput` is `bbPostInput`, `qInputs` is `bbInputsBag`, `qReadsBag` is `bbReadsBag`,
`qConsume` is `bbConsumeMarking` and `qAppend` is `bbProduceMany`'s marking, each by name; the
bridge theorems at the end (`pullC_qPostInput`, `pullC_qInputs`, `pullC_qReadsBag`,
`pullC_qConsume`, `pullC_qAppend`) prove the correspondence through a place index.

**Count projection** (`count_QFire`): the counts of the queue firings are exactly the reference
count firings: `(∃ M', RefQFire t M e M' ∧ qCount M' = m') ↔ Fires t (qCount M) (e.map
Prod.fst) m'`. So every count-level requirement proved of `RefFire` transfers, and the queue
witness adds only token order.

Not modelled here: the ν-correlated inputs of [NU-020] (name-matched, not FIFO; ruling D16
excludes them from [EXEC-010]), same-pass deposits ([EXEC-003]), and whether a completion is
admitted ([EXEC-020] under ruling D17, Phase 2 `RefExec`): `RefQFire` is one atomic firing.
-/

namespace Libpetri.Reference

open Libpetri Libpetri.Novel.Seam

variable {N T : Type}

/-- A queue marking: every place's tokens in FIFO order, oldest first ([EXEC-010]). -/
abbrev QMarking (N T : Type) := N → List T

/-- The count marking a queue marking projects to: the length of every queue. -/
def qCount (M : QMarking N T) : N → Nat := fun p => (M p).length

/-- The empty queue marking. -/
def qEmpty : QMarking N T := fun _ => []

variable [DecidableEq N]

/-- The tokens emitted to `p`, in emission order. -/
def qEmittedTo (e : List (N × T)) (p : N) : List T :=
  (e.filter (fun x => decide (x.1 = p))).map Prod.snd

/-- How many tokens a firing of `t` takes from `p`: `consumptionCount(available)` of its input
arc on `p`, 0 without one (`Seam.nconsumed` on the counts). -/
def qTake (M : QMarking N T) (t : Trans N) (p : N) : Nat := nconsumed (qCount M) t.core p

/-- The tokens the firing delivers to the action from each input place: the FIFO prefix of
length `qTake` ([EXEC-010]). `bbInputsBag` by name. -/
def qInputs (M : QMarking N T) (t : Trans N) : N → List T := fun p => (M p).take (qTake M t p)

/-- The queue marking after input consumption: every input place without its FIFO prefix.
`bbPostInput` by name. -/
def qPostInput (M : QMarking N T) (t : Trans N) : QMarking N T :=
  fun p => (M p).drop (qTake M t p)

/-- Append `l` to the bag at `p` (`Conservation.Pop.addBag` by name). -/
def qAddBag (b : N → List T) (p : N) (l : List T) : N → List T :=
  fun q => if q = p then b q ++ l else b q

/-- The read bag from marking `M`: per read arc, the head of its place, in arc order.
`bbReadsBag` by name. -/
def qReadsBag (M : QMarking N T) (reads : List N) : N → List T :=
  reads.foldl (fun b p => qAddBag b p (M p).head?.toList) (fun _ => [])

/-- The tokens the read arcs deliver: the heads **after input consumption, before reset
draining** ([EXEC-012], [EXEC-013] AC4). -/
def qReads (M : QMarking N T) (t : Trans N) : N → List T := qReadsBag (qPostInput M t) t.core.reads

/-- The queue marking after the whole consume: inputs, then resets drained ([CORE-034]).
`bbConsumeMarking` by name. -/
def qConsume (M : QMarking N T) (t : Trans N) : QMarking N T :=
  fun p => if p ∈ t.core.resets then [] else qPostInput M t p

/-- Append one token at the tail of `p` ([EXEC-020]). `bbProduceOne`'s marking by name. -/
def qAppendOne (M : QMarking N T) (p : N) (x : T) : QMarking N T :=
  fun q => if q = p then M q ++ [x] else M q

/-- Append the emissions `e` one at a time, in emission order ([EXEC-020]).
`bbProduceMany`'s marking by name. -/
def qAppend (M : QMarking N T) (e : List (N × T)) : QMarking N T :=
  e.foldl (fun M x => qAppendOne M x.1 x.2) M

/-- The queue marking a firing of `t` that emitted `e` leaves. -/
def qFire (M : QMarking N T) (t : Trans N) (e : List (N × T)) : QMarking N T :=
  qAppend (qConsume M t) e

/-- **No input arc and read arc on one place** (ruling D15): building a transition that has an
input arc and a read arc on the same place fails, in every language. Every transition that
builds satisfies this; the queue requirements assume it. -/
def NoInputRead (t : Trans N) : Prop := ∀ s ∈ t.core.inputs, s.place ∉ t.core.reads

instance (t : Trans N) : Decidable (NoInputRead t) :=
  inferInstanceAs (Decidable (∀ s ∈ t.core.inputs, s.place ∉ t.core.reads))

/-- What a firing delivers to its action: the consumed input tokens and the read tokens, each a
bag by place. -/
structure QDelivered (N T : Type) where
  /-- The consumed tokens, per input place, in FIFO order ([EXEC-010]). -/
  inputs : N → List T
  /-- The read tokens, per read place, one head per read arc ([EXEC-012]). -/
  reads  : N → List T

/-- What the reference delivers to the action of `t` fired from `M`. -/
def qDelivered (M : QMarking N T) (t : Trans N) : QDelivered N T := ⟨qInputs M t, qReads M t⟩

/-- **The reference queue firing**: `t` fires from the queue marking `M`, delivers `δ` to its
action, the action emits `e` (places and tokens, in emission order), and the firing leaves `M'`.
Enablement and the offered deposits are `Reference.Fires`'s, on the counts; `δ` and `M'` are
determined by `M`, `t` and `e`. -/
def RefQFire (t : Trans N) (M : QMarking N T) (δ : QDelivered N T) (e : List (N × T))
    (M' : QMarking N T) : Prop :=
  enabledNA (qCount M) t.core = true ∧
    (∃ ch, deposit (nconsumed (qCount M) t.core) t.out ch = some (e.map Prod.fst)) ∧
    δ = qDelivered M t ∧ M' = qFire M t e

#spec_witness RefQFire

/-! ## Closed forms -/

theorem qAppend_apply (e : List (N × T)) (M : QMarking N T) (p : N) :
    qAppend M e p = M p ++ qEmittedTo e p := by
  induction e generalizing M with
  | nil => simp [qAppend, qEmittedTo]
  | cons x xs ih =>
    simp only [qAppend, List.foldl_cons] at ih ⊢
    rw [ih]
    unfold qAppendOne qEmittedTo
    by_cases h : p = x.1
    · subst h; simp
    · simp [h, Ne.symm h]

theorem qEmittedTo_length (e : List (N × T)) (p : N) :
    (qEmittedTo e p).length = (e.map Prod.fst).count p := by
  induction e with
  | nil => rfl
  | cons x xs ih =>
    simp only [qEmittedTo, List.filter_cons, List.map_cons, List.count_cons] at ih ⊢
    by_cases h : x.1 = p
    · simp [h, ih]
    · simp [h, ih]

theorem qFire_apply (M : QMarking N T) (t : Trans N) (e : List (N × T)) (p : N) :
    qFire M t e p =
      (if p ∈ t.core.resets then [] else (M p).drop (qTake M t p)) ++ qEmittedTo e p := by
  simp [qFire, qAppend_apply, qConsume, qPostInput]

/-- Input consumption splits each queue into the delivered FIFO prefix and the rest. -/
theorem qInputs_append_qPostInput (M : QMarking N T) (t : Trans N) (p : N) :
    qInputs M t p ++ qPostInput M t p = M p := List.take_append_drop _ _

/-- A place without an input arc is untouched by input consumption. -/
theorem qPostInput_of_none {M : QMarking N T} {t : Trans N} {p : N}
    (h : nspecAt t.core p = none) : qPostInput M t p = M p := by
  simp [qPostInput, qTake, nconsumed, h]

theorem qReadsBag_apply (M : QMarking N T) (reads : List N) (p : N) :
    qReadsBag M reads p = (List.replicate (reads.count p) (M p).head?.toList).flatten := by
  suffices ∀ b : N → List T, reads.foldl (fun b q => qAddBag b q (M q).head?.toList) b p
      = b p ++ (List.replicate (reads.count p) (M p).head?.toList).flatten by
    unfold qReadsBag
    simpa using this (fun _ => [])
  induction reads with
  | nil => intro b; simp
  | cons q qs ih =>
    intro b
    rw [List.foldl_cons, ih]
    unfold qAddBag
    by_cases h : p = q
    · subst h; simp [List.replicate_succ]
    · simp [h, Ne.symm h]

/-- **Reads under D15**: on a transition with no input arc and read arc on one place, the read
bag holds the head of the pre-firing queue, once per read arc on the place. -/
theorem qReads_noInputRead {t : Trans N} (h : NoInputRead t) (M : QMarking N T) (p : N) :
    qReads M t p = (List.replicate (t.core.reads.count p) (M p).head?.toList).flatten := by
  unfold qReads
  rw [qReadsBag_apply]
  by_cases hp : p ∈ t.core.reads
  · have hn : nspecAt t.core p = none := by
      unfold nspecAt
      rw [List.find?_eq_none]
      intro s hs he
      have : s.place = p := by simpa using he
      exact h s hs (this ▸ hp)
    rw [qPostInput_of_none hn]
  · simp [List.count_eq_zero_of_not_mem hp]

/-! ## Count projection -/

/-- The counts of a queue firing's result are the reference count successor. -/
theorem qCount_qFire (M : QMarking N T) (t : Trans N) (e : List (N × T)) :
    qCount (qFire M t e) = fireNC (qCount M) t.core (depProd (e.map Prod.fst)) := by
  funext p
  simp only [qCount, qFire_apply, List.length_append, qEmittedTo_length, fireNC, depProd]
  by_cases hr : p ∈ t.core.resets
  · simp [hr]
  · simp [hr, qTake]

/-- **Count projection**: the queue firings, counted, are exactly the reference count firings.
For every emission `e`, some queue firing of `t` from `M` leaves a marking counting `m'` iff the
reference fires `t` from the counts of `M` with deposit `e.map Prod.fst` to `m'`. -/
theorem count_QFire (t : Trans N) (M : QMarking N T) (e : List (N × T)) (m' : N → Nat) :
    (∃ δ M', RefQFire t M δ e M' ∧ qCount M' = m') ↔ Fires t (qCount M) (e.map Prod.fst) m' := by
  constructor
  · rintro ⟨δ, M', ⟨hen, hd, -, rfl⟩, rfl⟩
    exact ⟨hen, hd, qCount_qFire M t e⟩
  · rintro ⟨hen, hd, rfl⟩
    exact ⟨qDelivered M t, qFire M t e, ⟨hen, hd, rfl, rfl⟩, qCount_qFire M t e⟩

/-- A queue firing's counts are a reference firing. -/
theorem RefQFire.fires {t : Trans N} {M M' : QMarking N T} {δ : QDelivered N T}
    {e : List (N × T)} (h : RefQFire t M δ e M') :
    Fires t (qCount M) (e.map Prod.fst) (qCount M') :=
  (count_QFire t M e _).mp ⟨δ, M', h, rfl⟩

/-- The queue firing is deterministic once the emission is fixed: the delivered bags and the
result are functions of `t`, `M` and `e`. -/
theorem RefQFire.det {t : Trans N} {M M₁ M₂ : QMarking N T} {δ₁ δ₂ : QDelivered N T}
    {e : List (N × T)} (h₁ : RefQFire t M δ₁ e M₁) (h₂ : RefQFire t M δ₂ e M₂) :
    δ₁ = δ₂ ∧ M₁ = M₂ :=
  ⟨h₁.2.2.1.trans h₂.2.2.1.symm, h₁.2.2.2.trans h₂.2.2.2.symm⟩

/-- Every enabled transition fires on queue markings, with any emission whose places are an
offered deposit. -/
theorem refQFire_of_fires {t : Trans N} {M : QMarking N T} {e : List (N × T)} {m' : N → Nat}
    (h : Fires t (qCount M) (e.map Prod.fst) m') :
    RefQFire t M (qDelivered M t) e (qFire M t e) ∧ qCount (qFire M t e) = m' := by
  obtain ⟨hen, hd, rfl⟩ := h
  exact ⟨⟨hen, hd, rfl, rfl⟩, qCount_qFire M t e⟩

/-! ## Bridges to the reference executor (`Refinement/Model.lean`), through a place index

With tokens `Colour` and places resolved through a `PlaceIndex`, each queue operation is the
reference executor's operation on `pullC ix M`, the flat view of the named marking. -/

section Bridge

variable (ix : PlaceIndex N)

theorem pullC_qPostInput (M : QMarking N Colour) {t : Trans N}
    (hin : ∀ s ∈ t.core.inputs, s.place ∈ ix.names) :
    pullC ix (qPostInput M t) = bbPostInput (pullC ix M) (toFlatT ix t.core) := by
  funext i
  unfold bbPostInput
  cases hi : ix.name? i with
  | none => simp [pullC, hi, specAt_none ix hin hi]
  | some n =>
    rw [specAt_some ix hin hi]
    cases hs : nspecAt t.core n with
    | none => simp [pullC, hi, qPostInput, qTake, nconsumed, hs]
    | some s =>
      simp [pullC, hi, qPostInput, qTake, nconsumed, hs, flatSpec, consumeCountAt_eq, qCount]

theorem pullC_qInputs (M : QMarking N Colour) {t : Trans N}
    (hin : ∀ s ∈ t.core.inputs, s.place ∈ ix.names) :
    pullC ix (qInputs M t) = bbInputsBag (pullC ix M) (toFlatT ix t.core) := by
  funext i
  unfold bbInputsBag
  cases hi : ix.name? i with
  | none => simp [pullC, hi, specAt_none ix hin hi]
  | some n =>
    rw [specAt_some ix hin hi]
    cases hs : nspecAt t.core n with
    | none => simp [pullC, hi, qInputs, qTake, nconsumed, hs]
    | some s =>
      simp [pullC, hi, qInputs, qTake, nconsumed, hs, flatSpec, consumeCountAt_eq, qCount]

theorem pullC_qAddBag (b : N → List Colour) {n : N} (hn : n ∈ ix.names) (l : List Colour) :
    pullC ix (qAddBag b n l) = addBag (pullC ix b) (ix.idx n) l := by
  funext i
  unfold addBag qAddBag pullC
  cases hi : ix.name? i with
  | none =>
    have hsz := ix.name?_eq_none_iff.mp hi
    have := ix.idx_lt hn
    have hne : i ≠ ix.idx n := fun he => by rw [he] at hsz; omega
    simp [hne]
  | some n' =>
    have hidx := ix.idx_of_name? hi
    have hiff : (i = ix.idx n) ↔ (n' = n) := by
      rw [← hidx, eq_comm, ix.idx_inj hn, eq_comm]
    by_cases h : n' = n
    · simp [h, hiff.mpr h]
    · have : i ≠ ix.idx n := fun e => h (hiff.mp e)
      simp [h, this]

theorem pullC_qReadsBag (M : QMarking N Colour) {reads : List N}
    (hr : ∀ n ∈ reads, n ∈ ix.names) :
    pullC ix (qReadsBag M reads) = bbReadsBag (pullC ix M) (reads.map ix.idx) := by
  unfold qReadsBag bbReadsBag
  suffices ∀ (b : N → List Colour) (b' : TokenBag), pullC ix b = b' →
      pullC ix (reads.foldl (fun b p => qAddBag b p (M p).head?.toList) b)
        = (reads.map ix.idx).foldl (fun b p => addBag b p (pullC ix M p).head?.toList) b' by
    apply this
    funext i
    simp only [pullC, emptyBag]
    cases ix.name? i <;> rfl
  induction reads with
  | nil => intro b b' h; simpa using h
  | cons q qs ih =>
    intro b b' h
    have hq : q ∈ ix.names := hr q List.mem_cons_self
    simp only [List.foldl_cons, List.map_cons]
    apply ih (fun n hn => hr n (List.mem_cons_of_mem q hn))
    rw [pullC_qAddBag ix b hq, h]
    congr 2
    simp [pullC, ix.name?_idx hq]

theorem pullC_qConsume (M : QMarking N Colour) {t : Trans N}
    (hin : ∀ s ∈ t.core.inputs, s.place ∈ ix.names) (hres : ∀ n ∈ t.core.resets, n ∈ ix.names) :
    pullC ix (qConsume M t) = bbConsumeMarking (pullC ix M) (toFlatT ix t.core) := by
  have hp := pullC_qPostInput ix M hin
  funext i
  unfold bbConsumeMarking
  rw [← hp]
  cases hi : ix.name? i with
  | none =>
    have := contains_idx_none ix hres hi
    have hni : i ∉ (toFlatT ix t.core).resets := by
      simpa [toFlatT, List.contains_iff_mem] using this
    simp [pullC, hi, hni]
  | some n =>
    have := contains_idx_some ix t.core.resets hi
    have hiff : i ∈ (toFlatT ix t.core).resets ↔ n ∈ t.core.resets := by
      simpa [toFlatT, List.contains_iff_mem] using this
    by_cases h : n ∈ t.core.resets
    · simp [pullC, hi, qConsume, h, hiff.mpr h]
    · simp [pullC, hi, qConsume, h, mt hiff.mp h]

theorem pullC_qAppendOne (M : QMarking N Colour) {n : N} (hn : n ∈ ix.names) (x : Colour) :
    pullC ix (qAppendOne M n x) = addBag (pullC ix M) (ix.idx n) [x] :=
  pullC_qAddBag ix M hn [x]

/-- Appending the emissions by name is `bbProduceMany`'s marking on the flat view, the emissions
resolved through the index. -/
theorem pullC_qAppend (net : _root_.Libpetri.Net) (M : QMarking N Colour) (e : List (N × Colour))
    (he : ∀ x ∈ e, x.1 ∈ ix.names) (bb : BBState) (hbb : bb.marking = pullC ix M) :
    (bbProduceMany net bb (e.map fun x => (ix.idx x.1, x.2))).marking = pullC ix (qAppend M e) := by
  induction e generalizing M bb with
  | nil => simpa [bbProduceMany, qAppend] using hbb
  | cons x xs ih =>
    have hx : x.1 ∈ ix.names := he x List.mem_cons_self
    simp only [List.map_cons, bbProduceMany, qAppend, List.foldl_cons]
    apply ih (qAppendOne M x.1 x.2) (fun y hy => he y (List.mem_cons_of_mem x hy))
    rw [pullC_qAppendOne ix M hx, ← hbb]
    funext q
    simp [bbProduceOne, addBag]

end Bridge

/-! ## Examples (decidable) -/

/-- A three-token queue on place 0 (tokens 10, 11, 12 added in that order). -/
def qexM : QMarking Nat Nat := fun p => if p = 0 then [10, 11, 12] else if p = 1 then [20, 21] else []

/-- `t` with input `card` on 0, a read and a reset on 1, output place 2. -/
def qexT (card : Card) : Trans Nat :=
  { core := { name := "t", inputs := [⟨0, card⟩], inhibitors := [], reads := [1], resets := [1] }
    out := some (.place 2) }

example : qInputs qexM (qexT .one) 0 = [10] := by decide
example : qInputs qexM (qexT (.exactly 2)) 0 = [10, 11] := by decide
example : qInputs qexM (qexT .all) 0 = [10, 11, 12] := by decide
example : qReads qexM (qexT .one) 1 = [20] := by decide
example : NoInputRead (qexT .one) := by decide
example : qFire qexM (qexT .one) [(2, 30)] 1 = [] := by decide
example : qFire qexM (qexT .one) [(2, 30)] 0 = [11, 12] := by decide
example : qAppend qexM [(0, 13), (0, 14)] 0 = [10, 11, 12, 13, 14] := by decide

/-- The reference queue firing of `qexT .one` from `qexM`: it delivers `[10]` and `[20]`, and
leaves `[11, 12]` in 0, nothing in the reset place 1, and the emitted `30` in 2. -/
theorem qex_refQFire :
    RefQFire (qexT .one) qexM ⟨fun p => if p = 0 then [10] else [], fun p => if p = 1 then [20] else []⟩
      [(2, 30)] (fun p => if p = 0 then [11, 12] else if p = 2 then [30] else []) := by
  refine ⟨by decide, ⟨.action 0, rfl⟩, ?_, ?_⟩
  · simp only [qDelivered, QDelivered.mk.injEq]
    constructor <;> funext p
    · match p with
      | 0 => decide
      | p + 1 => simp [qInputs, qTake, nconsumed, nspecAt, qexT]
    · rw [qReads_noInputRead (by decide)]
      match p with
      | 0 => decide
      | 1 => decide
      | p + 2 => simp [qexT]
  · funext p
    rw [qFire_apply]
    match p with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | p + 3 => simp [qexT, qexM, qEmittedTo]

end Libpetri.Reference
