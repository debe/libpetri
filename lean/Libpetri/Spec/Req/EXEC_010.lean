import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryQueue
import Libpetri.Spec.Text.EXEC_010

set_option linter.missingDocs true

/-!
# EXEC-010: FIFO token consumption (`spec/04-execution-model.md`)

The requirement is a predicate over an abstract queue firing relation `Q : QFireRel N T`
(glossary `GlossaryQueue.lean`): `Q t M δ e M'` says that `t` fires from the queue marking `M`,
delivers `δ` to its action, the action emits `e`, and the firing leaves `M'`. The evidence
theorems check it against the reference queue firing (`RefQFire`), against two relations that
take the right number of tokens in the wrong way (`exec010_revSel`, delivered newest first, and
`exec010_dropNewestSel`, the newest tokens removed), against a relation that removes the newest
tokens only from a self-loop place (`exec010_selfLoopNewestQ`), and against three mutant
readings: the kept tokens only a subsequence of the queue after the firing (killed by a self-loop
place with a repeated token value), LIFO consumption, and any subset of the right size.

Every relation here other than the reference and the two self-loop relations is an instance of
`exec010_by sel`: enablement,
the offered deposits, the reads and the tail append are the reference's, and only the split of
each queue into the delivered tokens and the tokens it keeps is `sel`'s.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## EXEC-010: FIFO token consumption -/

requirement EXEC_010
  id "EXEC-010"
  title "FIFO Token Consumption"
  kind B
  scope "all executors"
  source verbatim "spec/04-execution-model.md"
  covers EXEC_010.s1, EXEC_010.s2, EXEC_010.s3, EXEC_010.s4, EXEC_010.s5, EXEC_010.s6, EXEC_010.s7
  reading "For every queue firing relation Q:"
          "for every firing of a transition t and every input place p of t that is not a reset place of t: the queue p holds after the firing begins with the tokens of p's queue before the firing after its oldest Consumes tokens, in their queue order, and it holds exactly those tokens and the tokens the action emits to p, in some order;"
          "for every firing of a transition t and every input place p of t: the tokens delivered to the action from p are the oldest Consumes tokens of p's queue before the firing, in queue order;"
          "for every firing of a transition t and every place p that is not an input place of t: no consumed token is delivered to the action from p."
  assumes "A firing relates a queue marking before it to the queue marking after it, with what it delivered to the action and the emissions of the action (glossary: Queue order, QueueMarking, Delivered, QFireRel). Consumes t (Counts M) p is the consumption count of t's input arc on p at the token counts of M (glossary: Consumption count, Consume), so 'as many as the consumption count of the input arc' is the length of the prefix both lines name, and the paragraph 'The number of tokens consumed is determined by the input cardinality's consumptionCount(available)' is the same count."
          "Correlated inputs (ruling D16): the transitions of the model (Reference.Trans) carry no ν-net match specification, so every input place is an input that is not a correlated input of a match specification, and the lines quantify over every input place. The exception paragraph is therefore not a line of the formula: how a correlated input consumes (the matched tokens of the chosen name, oldest first among them) is NU-020's, not encoded here; this block makes no claim about a correlated input, and a mutant that consumed a correlated input oldest first would not be killed by it."
          "Line 1 is the first 'shall' sentence. It is stated at every input place that is not a reset place, including a place the action also emits to (a self-loop): the place keeps its tokens after the oldest Consumes ones, in queue order and ahead of every token emitted to it, and gains exactly the tokens emitted to it, so the tokens that left it are the oldest. Keeping the kept tokens ahead (a prefix, not only a subsequence) is what makes the consumed tokens the oldest when token values repeat: a place holding 10, 11, 10 whose action emits 10 back would otherwise pass with 10, 11, 10, the newest 10 consumed, which no count or value check can tell from the oldest 10 consumed and the emission put at the head (killed by EXEC_010_mutant_sublist_killed). That the emitted tokens follow the kept ones agrees with EXEC-020's tail append; the order among the emitted tokens is EXEC-020's, so line 1 fixes them only up to order. A reset place is left to line 2: it ends the firing holding exactly what was deposited there (CORE-034). With nothing emitted to the place, line 1 says the queue before the firing is its oldest Consumes tokens followed by the queue after it (exec010_line1_noEmission). The line is exercised by EXEC_010_nonvacuous; a relation that removes the newest tokens from a self-loop place is killed by EXEC_010_forbids_selfLoopNewest."
          "Line 2 is the second 'shall' sentence: the action receives, from each input place, the consumed tokens in queue order, the oldest first (OldestFirst, the FIFO prefix). On an input place that is also a reset place line 2 is the only line: the consumed prefix is still the oldest, the rest is drained. Line 3 is the third shall sentence, the counterpart of line 2 at every other place: the action receives no consumed token from a place that is not an input place, a read, reset, inhibitor or output place included. CORE-063 cites it for its sentence that an executor hands an action consumed tokens only from the input places of its transition, and CORE-061's delivery by arcs follows from it with EXEC-012's line 7 (core061_byArcs_of). All runtimes meet it: Rust's consume_for_firing walks the transition's input specs only and keys the consumed tokens by input place (rust/libpetri-runtime/src/bitmap_backend.rs and precompiled_backend.rs), Java and TypeScript fill the consumed tokens from inputSpecs only in fireTransition (java/src/main/java/org/libpetri/runtime/BitmapNetExecutor.java, typescript/src/runtime/bitmap-net-executor.ts, and the precompiled executors' input opcodes), and drained reset tokens never reach the action. Java and TypeScript keep the consumed and the read tokens in one store (rawInput) and separate them by the context's input gate (CORE-060); an executor that hands the read tokens over as consumed ones too breaks line 3 (EXEC_010_forbids_mergedInputs)."
          "The firing is the atomic firing of the reference: the counts the consumption count reads are the counts at the start of the firing. Same-pass deposits (EXEC-003 AC5: a draining arc ships the pass-start count, not the live one) need the cycle relation of Phase 2 (RefExec) and are deferred to it; consume_faithful (Conservation.lean) states the same FIFO prefix for one firing on the compiled consume program, under the module's assumption that no same-pass deposit is outstanding."
          "A transition with two input arcs on one place is rejected when it is built (CORE-030); the model reads the first arc (nspecAt), as Consumes does."
          "AC1 (tokens A, B, C added in that order; One consumes A), AC2 (Exactly(2) consumes A, B) and AC3 (All consumes A, B, C) are EXEC_010_nonvacuous, with tokens 10, 11, 12 for A, B, C: the reference delivers [10], [10, 11] and [10, 11, 12] and leaves [11, 12], [12] and []."
          "The test derivation (identifiable token values, fire, check the consumed tokens are in FIFO order) is the same check as AC1 to AC3."
  signoff "2026-11-13 528559a13871b25d ai"
  statement : ∀ {N T : Type} [DecidableEq N], QFireRel N T → Prop :=
    fun Q =>
      (∀ t δ e p, p ∈ inPlaces t → ¬ ResetArc t p →
        on (fun M M' => Q t M δ e M'), shall (fun M M' =>
          (M p).drop (Consumes t (Counts M) p) <+: M' p ∧
            List.Perm (M' p) ((M p).drop (Consumes t (Counts M) p) ++ EmittedTo e p))) ∧
      (∀ t δ e p, p ∈ inPlaces t →
        on (fun M M' => Q t M δ e M'), shall (fun M _ =>
          δ.inputs p = OldestFirst M p (Consumes t (Counts M) p))) ∧
      (∀ t δ e p, p ∉ inPlaces t →
        on (fun M M' => Q t M δ e M'), shall (fun _ _ => δ.inputs p = []))

/- The pinned readable form of EXEC-010: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EXEC_010 : {N T : Type} → [DecidableEq N] → QFireRel N T → Prop :=
fun {N T} [DecidableEq N] Q =>
  (∀ (t : Reference.Trans N) (δ : Delivered N T) (e : List (N × T)),
      ∀ p ∈ inPlaces t,
        ¬ResetArc t p →
          on fun M M' => Q t M δ e M', shall fun M M' =>
            List.drop (Consumes t (Counts M) p) (M p) <+: M' p ∧
              (M' p).Perm (List.drop (Consumes t (Counts M) p) (M p) ++ EmittedTo e p)) ∧
    (∀ (t : Reference.Trans N) (δ : Delivered N T) (e : List (N × T)),
        ∀ p ∈ inPlaces t,
          on fun M M' => Q t M δ e M', shall fun M x => δ.inputs p = OldestFirst M p (Consumes t (Counts M) p)) ∧
      ∀ (t : Reference.Trans N) (δ : Delivered N T) (e : List (N × T)),
        ∀ p ∉ inPlaces t, on fun M M' => Q t M δ e M', shall fun x x_1 => δ.inputs p = []
-/
#guard_msgs in #print EXEC_010

/-! ### Lemmas -/

section Lemmas

variable {N T : Type} [DecidableEq N]

/-- An enabled transition consumes from no place more tokens than the place holds. -/
theorem exec010_consumes_le {t : Trans N} {m : CountMarking N} (h : Enabled t m) (p : N) :
    Consumes t m p ≤ m p := by
  rw [consumes_eq]
  cases hs : nspecAt t.core p with
  | none => exact Nat.zero_le _
  | some s =>
    simp only [consumptionCount]
    split
    · exact Nat.le_refl _
    · have hmem := List.mem_of_find?_eq_some hs
      have hpl : s.place = p := by simpa using List.find?_some hs
      exact hpl ▸ ((enabled_iff t m).1 h).1 s hmem

/-- The tokens a firing that splits every queue with `sel` delivers: the first part of the
split of each place, and the reference reads. -/
def exec010_delivered (sel : List T → Nat → List T × List T) (M : QueueMarking N T)
    (t : Trans N) : Delivered N T :=
  ⟨fun p => (sel (M p) (Consumes t (Counts M) p)).1, qReads M t⟩

/-- The queue marking a firing that splits every queue with `sel` leaves: a reset place is
drained, every other place keeps the second part of its split, and the emissions are appended
at the tail. -/
def exec010_after (sel : List T → Nat → List T × List T) (M : QueueMarking N T) (t : Trans N)
    (e : List (N × T)) : QueueMarking N T :=
  qAppend (fun p => if p ∈ t.core.resets then [] else (sel (M p) (Consumes t (Counts M) p)).2) e

/-- The queue firing that splits each queue `l` from which it consumes `k` tokens into
`(sel l k).1`, delivered, and `(sel l k).2`, kept. Enablement, the offered deposits, the reads,
the reset drain and the tail append are the reference's. -/
def exec010_by (sel : List T → Nat → List T × List T) : QFireRel N T :=
  fun t M δ e M' => Enabled t (Counts M) ∧
    (∃ ch, deposit (Consumes t (Counts M)) (OutputSpec t) ch = some (e.map Prod.fst)) ∧
    δ = exec010_delivered sel M t ∧ M' = exec010_after sel M t e

theorem exec010_by_inputs {sel : List T → Nat → List T × List T} {t : Trans N}
    {M M' : QueueMarking N T} {δ : Delivered N T} {e : List (N × T)}
    (h : exec010_by sel t M δ e M') (p : N) :
    δ.inputs p = (sel (M p) (Consumes t (Counts M) p)).1 := by
  rw [h.2.2.1]; rfl

theorem exec010_by_kept {sel : List T → Nat → List T × List T} {t : Trans N}
    {M M' : QueueMarking N T} {δ : Delivered N T} {e : List (N × T)}
    (h : exec010_by sel t M δ e M') {p : N} (hr : ¬ ResetArc t p) (he : EmittedTo e p = []) :
    M' p = (sel (M p) (Consumes t (Counts M) p)).2 := by
  have he' : qEmittedTo e p = [] := he
  have hr' : p ∉ t.core.resets := hr
  rw [h.2.2.2, exec010_after, qAppend_apply, he', List.append_nil, if_neg hr']

/-- The consumption count of a firing of `exec010_by sel` is at most the length of the queue. -/
theorem exec010_by_le {sel : List T → Nat → List T × List T} {t : Trans N}
    {M M' : QueueMarking N T} {δ : Delivered N T} {e : List (N × T)}
    (h : exec010_by sel t M δ e M') (p : N) : Consumes t (Counts M) p ≤ (M p).length :=
  exec010_consumes_le h.1 p

end Lemmas

/-! ### The reference -/

/-- The reference queue firing satisfies EXEC-010: from each place it delivers the FIFO prefix
of length `Consumes` (`refQFire_inputs`, line 2), and a place that is not a reset place keeps
the rest of its queue followed by the tokens emitted to it (`refQFire_apply`, line 1); from a
place that is not an input place it delivers no consumed token (`qDelivered_inputs_off`,
line 3). -/
@[evidence holds EXEC_010]
theorem EXEC_010_reference {N T : Type} [DecidableEq N] :
    EXEC_010 (RefQFire (N := N) (T := T)) := by
  refine ⟨fun t δ e p _ hr M M' h => ?_, fun t δ e p _ M M' h => refQFire_inputs h p,
    fun t δ e p hp M M' h => ?_⟩
  rotate_left
  · obtain ⟨-, -, rfl, -⟩ := h
    exact qDelivered_inputs_off M t hp
  beta_reduce at h ⊢
  rw [refQFire_apply h p, if_neg hr]
  exact ⟨List.prefix_append _ _, List.Perm.refl _⟩

/-- With nothing emitted to the place, line 1 of EXEC-010 is the plain FIFO split: the queue
before the firing is its oldest `Consumes` tokens followed by the queue after it. -/
theorem exec010_line1_noEmission {T : Type} (l l' em : List T) (k : Nat) (he : em = [])
    (h : l.drop k <+: l' ∧ List.Perm l' (l.drop k ++ em)) :
    l = l.take k ++ l' := by
  subst he
  rw [List.append_nil] at h
  rw [← h.1.sublist.eq_of_length h.2.length_eq.symm, List.take_append_drop]

/-! ### Examples (AC1 to AC3) -/

/-- The emission of the examples: one token `30` to the output place `2`. -/
def exec010_e : List (Nat × Nat) := [(2, 30)]

/-- Every line of EXEC-010 is exercised by the reference. The examples fire `qexT c` (input
`c` on place `0`, a read and a reset on `1`, output place `2`) from `qexM` (tokens `10, 11, 12`
on `0`, added in that order), the action emitting `30` to `2`: place `0` is an input place that
is not a reset place and receives no emission, so both lines apply. AC1: `One` delivers `[10]`
and leaves `[11, 12]`; AC2: `Exactly(2)` delivers `[10, 11]` and leaves `[12]`; AC3: `All`
delivers `[10, 11, 12]` and leaves `[]`. -/
@[evidence nonvacuous EXEC_010]
theorem EXEC_010_nonvacuous :
    (0 ∈ inPlaces (qexT .one) ∧ ¬ ResetArc (qexT .one) 0 ∧ EmittedTo exec010_e 0 = []) ∧
    (∃ δ M', RefQFire (qexT .one) qexM δ exec010_e M' ∧
      δ.inputs 0 = [10] ∧ M' 0 = [11, 12]) ∧
    (∃ δ M', RefQFire (qexT (.exactly 2)) qexM δ exec010_e M' ∧
      δ.inputs 0 = [10, 11] ∧ M' 0 = [12]) ∧
    (∃ δ M', RefQFire (qexT .all) qexM δ exec010_e M' ∧
      δ.inputs 0 = [10, 11, 12] ∧ M' 0 = []) := by
  refine ⟨by decide, ?_, ?_, ?_⟩ <;>
    exact ⟨qDelivered qexM _, qFire qexM _ exec010_e,
      ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩, by decide, by decide⟩

/-- A relation of the form `exec010_by sel` fires `qexT c` from `qexM` whenever `c` is enabled
there. -/
theorem exec010_by_fires (sel : List Nat → Nat → List Nat × List Nat) (c : Card)
    (hen : Enabled (qexT c) (Counts qexM)) :
    exec010_by sel (qexT c) qexM (exec010_delivered sel qexM (qexT c)) exec010_e
      (exec010_after sel qexM (qexT c) exec010_e) :=
  ⟨hen, ⟨.action 0, rfl⟩, rfl, rfl⟩

/-! ### Relations that take the right number of tokens the wrong way -/

/-- The oldest tokens consumed but delivered newest first. -/
def exec010_revSel {T : Type} (l : List T) (k : Nat) : List T × List T :=
  ((l.take k).reverse, l.drop k)

/-- ✗ Delivering the consumed tokens newest first violates EXEC-010 (line 2, "in queue order,
the oldest first"): `Exactly(2)` from `[10, 11, 12]` delivers `[11, 10]`. -/
@[evidence forbids EXEC_010]
theorem EXEC_010_forbids_reversed : ¬ EXEC_010 (exec010_by (N := Nat) (T := Nat) exec010_revSel) := by
  intro h
  have := h.2.1 (qexT (.exactly 2)) _ exec010_e 0 (by decide) _ _
    (exec010_by_fires exec010_revSel (.exactly 2) (by decide))
  exact absurd this (by decide)

/-- The oldest tokens delivered, but the newest ones removed from the place. -/
def exec010_dropNewestSel {T : Type} (l : List T) (k : Nat) : List T × List T :=
  (l.take k, l.take (l.length - k))

/-- ✗ Removing the newest tokens violates EXEC-010 (line 1), even though the action receives
the oldest ones: `One` from `[10, 11, 12]` leaves `[10, 11]`. -/
@[evidence forbids EXEC_010]
theorem EXEC_010_forbids_dropNewest :
    ¬ EXEC_010 (exec010_by (N := Nat) (T := Nat) exec010_dropNewestSel) := by
  intro h
  have := h.1 (qexT .one) _ exec010_e 0 (by decide) (by decide) _ _
    (exec010_by_fires exec010_dropNewestSel .one (by decide))
  exact absurd this (by decide)

/-- A self-loop: one token from place `0`, output to place `0`, no read arc. -/
def exec010_selfT : Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 0) }

/-- The self-loop has no input arc and read arc on one place: ruling D15 admits it. -/
theorem exec010_selfT_noInputRead : NoInputRead exec010_selfT := by decide

/-- The reference everywhere, except that an input place that is not a reset place and receives
an emission loses its newest `Consumes` tokens instead of its oldest. It delivers the oldest
ones, so line 2 holds; only line 1 sees the self-loop. -/
def exec010_selfLoopNewestQ : QFireRel Nat Nat := fun t M δ e M' =>
  ∃ M0, RefQFire t M δ e M0 ∧
    M' = fun p => if p ∈ inPlaces t ∧ p ∉ t.core.resets ∧ EmittedTo e p ≠ [] then
      (M p).take ((M p).length - Consumes t (Counts M) p) ++ EmittedTo e p else M0 p

/-- ✗ Removing the newest tokens from a self-loop place violates EXEC-010 (line 1), even though
the action receives the oldest ones: `exec010_selfT` from `[10, 11, 12]`, the action emitting
`30` back to `0`, delivers `[10]` and leaves `[10, 11, 30]` instead of `[11, 12, 30]`. The
transition has no read arc (`exec010_selfT_noInputRead`), so ruling D15 does not exclude it. -/
@[evidence forbids EXEC_010]
theorem EXEC_010_forbids_selfLoopNewest : ¬ EXEC_010 exec010_selfLoopNewestQ := by
  intro h
  have := h.1 exec010_selfT (qDelivered qexM exec010_selfT) [(0, 30)] 0 (by decide) (by decide)
    qexM _ ⟨_, ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩, rfl⟩
  exact absurd this (by decide)

/-! ### Mutant: the kept tokens a subsequence, not a prefix -/

/-- A self-loop place holding `10, 11, 10`, oldest first; every other place is empty. -/
def exec010_dupM : QueueMarking Nat Nat := fun p => if p = 0 then [10, 11, 10] else []

/-- The reference everywhere, plus one firing of the self-loop `exec010_selfT` from
`exec010_dupM`, the action emitting `10` back to `0`, that consumes the newest `10` instead of
the oldest and leaves `10, 11, 10`. The reference leaves `11, 10, 10`. -/
def exec010_dupNewestQ : QFireRel Nat Nat := fun t M δ e M' =>
  RefQFire t M δ e M' ∨
    (t = exec010_selfT ∧ M = exec010_dupM ∧ δ = qDelivered exec010_dupM exec010_selfT ∧
      e = [(0, 10)] ∧ M' = exec010_dupM)

/-- Mutant reading of EXEC-010 whose line 1 asks only that the kept tokens appear in the queue
after the firing in their order (a subsequence), not that they lead it. -/
def EXEC_010_mutant_sublist {N T : Type} [DecidableEq N] (Q : QFireRel N T) : Prop :=
  (∀ t δ e p, p ∈ inPlaces t → ¬ ResetArc t p →
    on (fun M M' => Q t M δ e M'), shall (fun M M' =>
      List.Sublist ((M p).drop (Consumes t (Counts M) p)) (M' p) ∧
        List.Perm (M' p) ((M p).drop (Consumes t (Counts M) p) ++ EmittedTo e p))) ∧
  (∀ t δ e p, p ∈ inPlaces t →
    on (fun M M' => Q t M δ e M'), shall (fun M _ =>
      δ.inputs p = OldestFirst M p (Consumes t (Counts M) p)))

/-- The subsequence reading cannot tell the newest `10` consumed from the oldest `10` consumed
with the emission put at the head: `exec010_dupNewestQ` satisfies it. EXEC-010 kills it, since
the queue `10, 11, 10` does not begin with `11, 10`, so the next `One` firing would receive
`10` where the spec requires `11`. -/
@[evidence mutant EXEC_010]
theorem EXEC_010_mutant_sublist_killed :
    EXEC_010_mutant_sublist exec010_dupNewestQ ∧ ¬ EXEC_010 exec010_dupNewestQ := by
  refine ⟨⟨fun t δ e p hp hr M M' h => ?_, fun t δ e p hp M M' h => ?_⟩, fun h => ?_⟩
  · rcases h with h | ⟨rfl, rfl, rfl, rfl, rfl⟩
    · have := EXEC_010_reference.1 t δ e p hp hr M M' h
      exact ⟨this.1.sublist, this.2⟩
    · have : p = 0 := by simpa [inPlaces, exec010_selfT] using hp
      subst this; decide
  · rcases h with h | ⟨rfl, rfl, rfl, rfl, rfl⟩
    · exact EXEC_010_reference.2.1 t δ e p hp M M' h
    · exact refQFire_inputs (M' := qFire exec010_dupM exec010_selfT [(0, 10)])
        ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩ p
  · have := h.1 exec010_selfT _ [(0, 10)] 0 (by decide) (by decide) exec010_dupM exec010_dupM
      (.inr ⟨rfl, rfl, rfl, rfl, rfl⟩)
    exact absurd this (by decide)

/-! ### Mutant: LIFO consumption -/

/-- LIFO: the newest `k` tokens are consumed and delivered, the oldest ones kept. -/
def exec010_lifoSel {T : Type} (l : List T) (k : Nat) : List T × List T :=
  (l.drop (l.length - k), l.take (l.length - k))

/-- Mutant reading of EXEC-010 that consumes from the newest end of the queue (LIFO): the
place keeps its oldest tokens and the action receives the newest `Consumes` tokens. -/
def EXEC_010_mutant_lifo {N T : Type} [DecidableEq N] (Q : QFireRel N T) : Prop :=
  (∀ t δ e p, p ∈ inPlaces t → ¬ ResetArc t p → EmittedTo e p = [] →
    on (fun M M' => Q t M δ e M'), shall (fun M M' =>
      M p = M' p ++ (M p).drop ((M p).length - Consumes t (Counts M) p))) ∧
  (∀ t δ e p, p ∈ inPlaces t →
    on (fun M M' => Q t M δ e M'), shall (fun M _ =>
      δ.inputs p = (M p).drop ((M p).length - Consumes t (Counts M) p)))

/-- The LIFO firing satisfies the LIFO reading, at every type. -/
theorem exec010_lifo_mutant {N T : Type} [DecidableEq N] :
    EXEC_010_mutant_lifo (exec010_by (N := N) (T := T) exec010_lifoSel) := by
  refine ⟨fun t δ e p _ hr he M M' h => ?_, fun t δ e p _ M M' h => exec010_by_inputs h p⟩
  beta_reduce at h ⊢
  rw [exec010_by_kept h hr he, exec010_lifoSel, List.take_append_drop]

/-- The LIFO firing kills the LIFO mutant: it satisfies the mutant reading, but not EXEC-010,
since `One` from `[10, 11, 12]` delivers `[12]` instead of `[10]`. -/
@[evidence mutant EXEC_010]
theorem EXEC_010_mutant_lifo_killed :
    EXEC_010_mutant_lifo (exec010_by (N := Nat) (T := Nat) exec010_lifoSel) ∧
      ¬ EXEC_010 (exec010_by (N := Nat) (T := Nat) exec010_lifoSel) := by
  refine ⟨exec010_lifo_mutant, fun h => ?_⟩
  have := h.2.1 (qexT .one) _ exec010_e 0 (by decide) _ _
    (exec010_by_fires exec010_lifoSel .one (by decide))
  exact absurd this (by decide)

/-! ### Mutant: any subset of the right size -/

/-- Skip the head: when tokens remain, consume the `k` tokens after the oldest one and keep the
oldest one with the rest; when every token is consumed, consume them all. Queue order is kept on
both sides. -/
def exec010_skipHeadSel {T : Type} : List T → Nat → List T × List T
  | [], _ => ([], [])
  | x :: xs, k => if k ≤ xs.length then (xs.take k, x :: xs.drop k) else (x :: xs, [])

/-- Mutant reading of EXEC-010 that asks only for the right number of tokens: the place keeps
some `length - Consumes` of its tokens, in queue order, and the action receives some `Consumes`
of them, in queue order. -/
def EXEC_010_mutant_subset {N T : Type} [DecidableEq N] (Q : QFireRel N T) : Prop :=
  (∀ t δ e p, p ∈ inPlaces t → ¬ ResetArc t p → EmittedTo e p = [] →
    on (fun M M' => Q t M δ e M'), shall (fun M M' =>
      List.Sublist (M' p) (M p) ∧ (M' p).length = (M p).length - Consumes t (Counts M) p)) ∧
  (∀ t δ e p, p ∈ inPlaces t →
    on (fun M M' => Q t M δ e M'), shall (fun M _ =>
      List.Sublist (δ.inputs p) (M p) ∧ (δ.inputs p).length = Consumes t (Counts M) p))

theorem exec010_skipHead_spec {T : Type} (l : List T) (k : Nat) (hk : k ≤ l.length) :
    List.Sublist (exec010_skipHeadSel l k).1 l ∧ (exec010_skipHeadSel l k).1.length = k ∧
      List.Sublist (exec010_skipHeadSel l k).2 l ∧
        (exec010_skipHeadSel l k).2.length = l.length - k := by
  cases l with
  | nil =>
    simp only [List.length_nil, Nat.le_zero] at hk
    subst hk
    simp [exec010_skipHeadSel]
  | cons x xs =>
    simp only [List.length_cons] at hk
    by_cases h : k ≤ xs.length
    · simp only [exec010_skipHeadSel, if_pos h, List.length_take, List.length_cons,
        List.length_drop]
      refine ⟨(List.take_sublist k xs).cons x, by omega, (List.drop_sublist k xs).cons_cons x, by omega⟩
    · simp only [exec010_skipHeadSel, if_neg h, List.length_cons, List.length_nil]
      exact ⟨List.Sublist.refl _, by omega, List.nil_sublist _, by omega⟩

/-- The skip-the-head firing satisfies the subset reading, at every type. -/
theorem exec010_skipHead_mutant {N T : Type} [DecidableEq N] :
    EXEC_010_mutant_subset (exec010_by (N := N) (T := T) exec010_skipHeadSel) := by
  refine ⟨fun t δ e p _ hr he M M' h => ?_, fun t δ e p _ M M' h => ?_⟩
  · obtain ⟨-, -, h3, h4⟩ := exec010_skipHead_spec (M p) _ (exec010_by_le h p)
    rw [exec010_by_kept h hr he]
    exact ⟨h3, h4⟩
  · obtain ⟨h1, h2, -, -⟩ := exec010_skipHead_spec (M p) _ (exec010_by_le h p)
    rw [exec010_by_inputs h p]
    exact ⟨h1, h2⟩

/-- The skip-the-head firing kills the subset mutant: it satisfies the subset reading and keeps
queue order on both sides, but not EXEC-010, since `One` from `[10, 11, 12]` delivers `[11]`
and leaves `[10, 12]`. -/
@[evidence mutant EXEC_010]
theorem EXEC_010_mutant_subset_killed :
    EXEC_010_mutant_subset (exec010_by (N := Nat) (T := Nat) exec010_skipHeadSel) ∧
      ¬ EXEC_010 (exec010_by (N := Nat) (T := Nat) exec010_skipHeadSel) := by
  refine ⟨exec010_skipHead_mutant, fun h => ?_⟩
  have := h.2.1 (qexT .one) _ exec010_e 0 (by decide) _ _
    (exec010_by_fires exec010_skipHeadSel .one (by decide))
  exact absurd this (by decide)

/-! ### Line 3: consumed tokens only from input places -/

/-- A transition with an input arc on place `0`, a read arc on place `1` and output place `2`. -/
def exec010_rt : Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .one⟩], inhibitors := [], reads := [1], resets := [] },
    out := some (.place 2) }

/-- Place `0` holds `10`, the read place `1` holds `20`. -/
def exec010_rM : QueueMarking Nat Nat := fun p => if p = 0 then [10] else if p = 1 then [20] else []

/-- An executor that keeps the consumed and the read tokens in one store and hands the whole
store over as consumed tokens: the reference firing, with the read tokens added to the consumed
ones at every place (Java's and TypeScript's shared `rawInput` without the input gate). -/
def exec010_mergedInputs : QFireRel Nat Nat := fun t M δ e M' =>
  ∃ δ₀, RefQFire t M δ₀ e M' ∧ δ = ⟨fun p => δ₀.inputs p ++ δ₀.reads p, δ₀.reads⟩

/-- ✗ Handing the read tokens over as consumed tokens violates EXEC-010 (line 3): firing
`exec010_rt` from `exec010_rM` delivers `20` as a consumed token from the read place `1`, which is
not an input place. -/
@[evidence forbids EXEC_010]
theorem EXEC_010_forbids_mergedInputs : ¬ EXEC_010 exec010_mergedInputs := by
  intro h
  have := h.2.2 exec010_rt _ exec010_e 1 (by decide) exec010_rM (qFire exec010_rM exec010_rt exec010_e)
    ⟨_, ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩, rfl⟩
  revert this
  decide

/-- Line 3 on the reference: firing `exec010_rt` from `exec010_rM` delivers `10` consumed from the
input place `0`, and no consumed token from the read place `1` or the output place `2`, while the
read token `20` is delivered as a read. -/
@[evidence nonvacuous EXEC_010]
theorem EXEC_010_nonvacuous_offInputs :
    (∃ δ M', RefQFire exec010_rt exec010_rM δ exec010_e M' ∧ 1 ∉ inPlaces exec010_rt ∧
      δ.inputs 0 = [10] ∧ δ.inputs 1 = [] ∧ δ.inputs 2 = [] ∧ δ.reads 1 = [20]) :=
  ⟨qDelivered exec010_rM exec010_rt, qFire exec010_rM exec010_rt exec010_e,
    ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩, by decide, by decide, by decide, by decide, by decide⟩

end Libpetri.Spec
