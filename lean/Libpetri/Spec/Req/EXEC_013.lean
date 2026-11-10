import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryQueue

set_option linter.missingDocs true

/-!
# EXEC-013: Reset arc execution (`spec/04-execution-model.md`)

The order of the parts of one firing: input consumption, then read peeks, then reset draining,
all before the action, whose outputs land last. The requirement is a predicate over an abstract
queue firing relation `Q : QFireRel N T` (glossary `GlossaryQueue.lean`), so that it can be
checked against the reference queue firing (`RefQFire`), against a firing that does not drain,
and against three mutant readings: reset draining before the read peek, reset draining before
input consumption, and the action's outputs deposited before the drain.

Token counts are CORE-034's subject (AC1 and AC2 on counts); the clock restart of AC3 is
TIME-012's. Which tokens an input consumes is EXEC-010's, where the queue left on an input place
that is not reset and the tail append are EXEC-020's. This block states what only a queue model
can see of the order: that the action's inputs and reads are taken before the drain, and that
its outputs land after it.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## EXEC-013: Reset arc execution -/

requirement EXEC_013
  id "EXEC-013"
  title "Reset Arc Execution"
  kind B
  scope "all executors"
  source verbatim "spec/04-execution-model.md"
  quote "When a transition fires, all tokens are removed from each reset place."
        "This happens during the firing step, before the action executes."
        "*When* a transition fires, it *shall* drain each of its reset places ([CORE-034]) before its action starts."
        "*When* a transition fires, it *shall* consume from its input places first, then peek its read places, then drain its reset places."
        "*When* a transition with a read arc and a reset arc on the same place fires, its action *shall* receive as the read token the oldest token the place held before the drain."
        "*If* a reset place of a firing transition is unmarked, *then* the drain *shall* remove nothing and the firing *shall* proceed."
  reading "For every transition t with no input arc and read arc on one place (ruling D15):"
          "every firing of t that emits e leaves each reset place of t holding exactly the tokens e sends there, in emission order;"
          "every firing of t from M that delivers δ hands the action, from each input place of t that is also a reset place, as many tokens as the input arc consumes, taken from the place's queue in M and kept in queue order;"
          "every firing of t from M that delivers δ hands the action, for each place that is both a read place and a reset place of t, a nonempty read bag whose every token is the head of the place's queue in M;"
          "from every queue marking M at which t is enabled and one of its reset places is unmarked, every emission e whose places are a deposit t offers is the emission of some firing of t from M."
  assumes "A firing is one step Q t M δ e M' (glossary: QFireRel): t fires from the queue marking M, delivers δ to its action (the consumed tokens per input place and the read tokens per read place), the action emits e (places and tokens, in emission order) and the firing leaves M'. Queue order, Head, Emitted to and Appended at the tail are the glossary terms of GlossaryQueue.lean. Timing, priority and events play no part. Correlated ν inputs are not modelled (NU-020); ruling D16 excludes them from EXEC-010's oldest-first consumption, and line 2 does not say which tokens an input consumes, only that they are taken from the queue before the drain, so it makes no claim that D16 would contradict."
          "e is the emission of a completion the executor admitted and output validation accepted ([EXEC-020], [EXEC-021], ruling D17); a discarded, timed-out, stopped or failed completion is not a step of Q. Tokens an action published before it completed ([IO-015]) are not modelled: they land after the drain and survive it, also when the completion then fails validation (ruling D17). Both are Phase 2 (RefExec)."
          "Every line is stated for transitions satisfying NoInputRead (ruling D15): a transition with an input arc and a read arc on one place is rejected when it is built (EXEC-012) and never fires. Under D15 no place is both an input place and a read place, so the 'input consumption, then read peeks' half of the fourth quoted sentence is not observable in a single firing: a read place is untouched by input consumption, and the read sees its pre-firing head whichever comes first. That half is therefore not a line; the halves 'input consumption, then reset draining' and 'read peeks, then reset draining' are lines 2 and 3."
          "Line 1 is the first quoted sentence and the single-firing consequence of the second and third: the drain comes before the action's outputs land, so every token the action emits to a reset place survives it, and the place ends with exactly those tokens, in emission order. A drain after the action's outputs would leave the place empty (exec013_outputsFirst violates it). The other half of 'before its action starts', that the drained marking is the intermediate marking other transitions see while the action runs (the unquoted body sentence 'Like input consumption, the drain lands in the intermediate marking, so it restarts the clocks of transitions it disables there'), is TIME-012's and the Phase 2 executor model's (RefExec), not a line here. On token counts line 1 is CORE-034's first line."
          "Line 2 is the fourth quoted sentence's 'input consumption, then reset draining': an input place that is also a reset place hands the action as many tokens as the input arc's consumption count (IO-007) on the pre-firing counts, taken from its pre-firing queue in queue order; a drain first would hand it nothing (exec013_drainFirst violates it). Which tokens they are (the oldest, except for a correlated ν input) is EXEC-010's subject; the queue an input place that is not a reset place keeps, and the tail append of the emitted tokens, are EXEC-010's and EXEC-020's. What is delivered from a place that is not an input place (for instance the drained tokens of a reset place that is not an input place) is not constrained by this block, nor by any other requirement block: the spec has no shall sentence on it, so that the action receives nothing from such a place is not encoded."
          "Line 3 is the fifth quoted sentence, which is the 'read peeks, then reset draining' half of the fourth: the read token of a place that is both a read place and a reset place is the head of its queue before the drain. The read bag is nonempty and every token in it is that head; how many copies a transition with several read arcs on one place receives is CORE-032's and EXEC-012's subject and is not fixed here."
          "Line 4 is the sixth quoted sentence's 'the firing shall proceed': an unmarked reset place blocks no firing, so every firing the counts allow (enabled, an offered deposit, glossary Enabled, Consumes and OutputSpec) is a firing of Q. Its 'the drain shall remove nothing' is line 1 at an unmarked reset place: the place ends with exactly the emitted tokens, which is the empty queue followed by them (EXEC_013_unmarked_removes_nothing)."
          "The body sentence 'A token a synchronous action deposited earlier in the same firing pass survives the drain ([EXEC-003] AC5).' is about a firing pass of several firings; a single queue firing has no earlier firing, so it is EXEC-003's subject and the Phase 2 cycle relation's, not encoded."
          "AC1 (reset place with 5 tokens, all removed) is line 1 at a reset place that is not an output place: it ends empty (EXEC_013_nonvacuous, the five-token place 3). On token counts it is CORE-034's first line (cited on CORE_034_reference)."
          "AC2 (reset place empty, no error) is line 4 and line 1 at an unmarked reset place (EXEC_013_nonvacuous). On token counts it is CORE-034's second line: a reset arc does not affect whether its transition can fire (cited on CORE_034_reference)."
          "AC3 (the reset place is also an input or read place of another enabled transition, whose clock restarts) is read in TIME-012's form and is not encoded here: the queue firing has no clocks. TIME-012 says the other transition loses its clock in the intermediate marking and is newly armed with a fresh clock when it is enabled again; AC3's bare 'restarts' is read as that, not as a restart of a transition that the drain leaves disabled. The evidence is TIME-012's AC3 example TIME_012_ac3 (cited there)."
          "AC4 (reset draining after read peeking; a read arc and a reset arc on one place observe the pre-reset front token; the overall order is input consumption, read peeks, reset draining) is lines 2 and 3; the mutants exec013_resetFirst (draining before the peek) and exec013_drainFirst (draining before input consumption) are killed by lines 3 and 2."
          "The test derivation's clock-restart check is AC3's and is TIME-012's subject."
  signoff "pending"
  statement : ∀ {N T : Type} [DecidableEq N], QFireRel N T → Prop :=
    fun Q => ∀ t, NoInputRead t →
      (∀ δ e, on (fun M M' => Q t M δ e M'), shall (fun _ M' =>
        ∀ p, ResetArc t p → M' p = EmittedTo e p)) ∧
      (∀ δ e, on (fun M M' => Q t M δ e M'), shall (fun M _ => ∀ p, p ∈ inPlaces t →
        ResetArc t p →
          (δ.inputs p).length = Consumes t (Counts M) p ∧ List.Sublist (δ.inputs p) (M p))) ∧
      (∀ δ e, on (fun M M' => Q t M δ e M'), shall (fun M _ => ∀ p, ReadArc t p → ResetArc t p →
        δ.reads p ≠ [] ∧ ∀ tok ∈ δ.reads p, Head M p = some tok)) ∧
      (∀ M e, (∃ p, ResetArc t p ∧ M p = []) → Enabled t (Counts M) →
        (∃ ch, deposit (Consumes t (Counts M)) (OutputSpec t) ch = some (e.map Prod.fst)) →
        ∃ δ M', Q t M δ e M')

/- The pinned readable form of EXEC-013: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EXEC_013 : {N T : Type} → [DecidableEq N] → QFireRel N T → Prop :=
fun {N T} [DecidableEq N] Q =>
  ∀ (t : Reference.Trans N),
    NoInputRead t →
      (∀ (δ : Delivered N T) (e : List (N × T)),
          on fun M M' => Q t M δ e M', shall fun x M' => ∀ (p : N), ResetArc t p → M' p = EmittedTo e p) ∧
        (∀ (δ : Delivered N T) (e : List (N × T)),
            on fun M M' => Q t M δ e M', shall fun M x =>
              ∀ p ∈ inPlaces t,
                ResetArc t p → (δ.inputs p).length = Consumes t (Counts M) p ∧ (δ.inputs p).Sublist (M p)) ∧
          (∀ (δ : Delivered N T) (e : List (N × T)),
              on fun M M' => Q t M δ e M', shall fun M x =>
                ∀ (p : N), ReadArc t p → ResetArc t p → δ.reads p ≠ [] ∧ ∀ tok ∈ δ.reads p, Head M p = some tok) ∧
            ∀ (M : QueueMarking N T) (e : List (N × T)),
              (∃ p, ResetArc t p ∧ M p = []) →
                Enabled t (Counts M) →
                  (∃ ch, deposit (Consumes t (Counts M)) (OutputSpec t) ch = some (List.map Prod.fst e)) →
                    ∃ δ M', Q t M δ e M'
-/
#guard_msgs in #print EXEC_013

/-! ### The reference -/

section Reference

variable {N T : Type} [DecidableEq N]

/-- An enabled transition consumes from no place more tokens than the place holds. -/
theorem exec013_consumes_le {t : Trans N} {m : CountMarking N} (h : Enabled t m) (p : N) :
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

/-- The reference delivery from an enabled firing takes from each place as many tokens as the
input arc consumes, from the pre-firing queue, in queue order. -/
theorem exec013_qInputs {t : Trans N} {M : QueueMarking N T} (h : Enabled t (Counts M)) (p : N) :
    (qInputs M t p).length = Consumes t (Counts M) p ∧ List.Sublist (qInputs M t p) (M p) :=
  ⟨by rw [qInputs, List.length_take]; exact Nat.min_eq_left (exec013_consumes_le h p),
    List.take_sublist _ _⟩

/-- Under D15 the reference read bag of an enabled firing at a read place holds the head of the
place's queue, at least once and nothing else. -/
theorem exec013_ref_reads {t : Trans N} (hw : NoInputRead t) {M M' : QueueMarking N T}
    {δ : Delivered N T} {e : List (N × T)} (h : RefQFire t M δ e M') {p : N} (hp : ReadArc t p) :
    δ.reads p ≠ [] ∧ ∀ tok ∈ δ.reads p, Head M p = some tok := by
  have hm : Marked (Counts M) p := ((enabled_iff t (Counts M)).1 h.1).2.2 p hp
  obtain ⟨x, xs, hx⟩ : ∃ x xs, M p = x :: xs := by
    cases hM : M p with
    | nil => exact absurd (by simp [Counts, qCount, hM]) hm
    | cons x xs => exact ⟨x, xs, rfl⟩
  have hc : 0 < t.core.reads.count p := List.count_pos_iff.2 hp
  rw [refQFire_reads hw h p, Head, hx]
  refine ⟨?_, fun tok htok => ?_⟩
  · obtain ⟨n, hn⟩ : ∃ n, t.core.reads.count p = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hc).symm⟩
    simp [hn, List.replicate_succ]
  · simp only [List.mem_flatten, List.mem_replicate] at htok
    obtain ⟨l, ⟨-, rfl⟩, hl⟩ := htok
    simp at hl
    simp [hl]

end Reference

/-- The reference queue firing satisfies EXEC-013: `qFire` drains the reset places after the
input step and before it appends the emitted tokens (`refQFire_apply`), the delivered inputs
are a prefix of the pre-firing queue of the consumed length (`exec013_qInputs`), the read bag is
taken before the drain (`qReads` reads `qPostInput`, not `qConsume`), and `RefQFire` asks only
for enablement and an offered deposit on the counts, which a reset arc does not affect. -/
@[evidence holds EXEC_013]
theorem EXEC_013_reference {N T : Type} [DecidableEq N] :
    EXEC_013 (RefQFire (N := N) (T := T)) := by
  intro t hw
  refine ⟨fun δ e M M' h p hp => ?_, fun δ e M M' h p _ _ => ?_,
      fun δ e M M' h p hp _ => exec013_ref_reads hw h hp,
      fun M e _ hen hd => ⟨_, _, hen, hd, rfl, rfl⟩⟩
  · rw [refQFire_apply h, if_pos hp, List.nil_append]
  · rw [h.2.2.1]
    exact exec013_qInputs h.1 p

/-- The sixth quoted sentence's 'the drain shall remove nothing', from line 1: an unmarked
reset place ends with its (empty) queue followed by the emitted tokens. -/
theorem EXEC_013_unmarked_removes_nothing {N T : Type} [DecidableEq N] {Q : QFireRel N T}
    (h : EXEC_013 Q) {t : Trans N} (hw : NoInputRead t) {M M' : QueueMarking N T}
    {δ : Delivered N T} {e : List (N × T)} (hq : Q t M δ e M') {p : N} (hp : ResetArc t p)
    (he : M p = []) : AppendedAtTail M M' e p := by
  rw [AppendedAtTail, (h t hw).1 δ e M M' hq p hp, he, List.nil_append]

/-! ### Examples -/

/-- The queue marking of the examples: place `0` holds `10, 11, 12`, place `1` holds `20, 21`,
place `3` holds the five tokens `30` to `34`, every other place is empty. -/
def exec013_M : QueueMarking Nat Nat := fun p =>
  if p = 0 then [10, 11, 12] else if p = 1 then [20, 21] else if p = 3 then [30, 31, 32, 33, 34]
  else []

/-- The transition of the examples: a `one()` input on `0`, a read arc on `1`, reset arcs on
`0`, `1`, `3` and `4`, and output spec `Place 0`. Place `0` is an input and a reset place,
place `1` a read and a reset place, place `3` a reset place with five tokens (AC1), place `4`
an unmarked reset place (AC2). -/
def exec013_t : Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .one⟩], inhibitors := [], reads := [1],
              resets := [0, 1, 3, 4] },
    out := some (.place 0) }

/-- The emission of the examples: one token `99` to place `0`. -/
def exec013_e : List (Nat × Nat) := [(0, 99)]

/-- The reference firing of `exec013_t` from `exec013_M` with emission `exec013_e`. -/
theorem exec013_t_fires :
    RefQFire exec013_t exec013_M (qDelivered exec013_M exec013_t) exec013_e
      (qFire exec013_M exec013_t exec013_e) :=
  ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩

/-! ### Violation: a firing that does not drain -/

/-- A queue firing that consumes its inputs and appends its outputs but never drains a reset
place. -/
def exec013_noDrain {N T : Type} [DecidableEq N] : QFireRel N T := fun t M δ e M' =>
  Enabled t (Counts M) ∧
    (∃ ch, deposit (Consumes t (Counts M)) (OutputSpec t) ch = some (e.map Prod.fst)) ∧
    δ = qDelivered M t ∧ M' = qAppend (qPostInput M t) e

/-- ✗ A firing that does not drain violates EXEC-013 (line 1): firing `exec013_t` leaves the
five tokens of the reset place `3` in place. -/
@[evidence forbids EXEC_013]
theorem EXEC_013_forbids_noDrain : ¬ EXEC_013 (exec013_noDrain (N := Nat) (T := Nat)) := by
  intro h
  have hq : exec013_noDrain exec013_t exec013_M (qDelivered exec013_M exec013_t) exec013_e
      (qAppend (qPostInput exec013_M exec013_t) exec013_e) :=
    ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩
  have := (h exec013_t (by decide)).1 _ _ _ _ hq 3 (by decide)
  revert this
  decide

/-! ### Mutant: reset draining before the read peek -/

/-- A queue firing that drains the reset places before it peeks the read places: the read bag
is taken from the marking after the whole consume step (`qConsume`). -/
def exec013_resetFirst {N T : Type} [DecidableEq N] : QFireRel N T := fun t M δ e M' =>
  Enabled t (Counts M) ∧
    (∃ ch, deposit (Consumes t (Counts M)) (OutputSpec t) ch = some (e.map Prod.fst)) ∧
    δ = ⟨qInputs M t, qReadsBag (qConsume M t) t.core.reads⟩ ∧ M' = qFire M t e

/-- Mutant reading of EXEC-013 in which the drain comes before the read peek: line 3 says a
place that is both a read place and a reset place hands the action nothing (its drained queue
has no head). The other lines are as in EXEC-013. -/
def EXEC_013_mutant_resetFirst {N T : Type} [DecidableEq N] (Q : QFireRel N T) : Prop :=
  ∀ t, NoInputRead t →
    (∀ δ e, on (fun M M' => Q t M δ e M'), shall (fun _ M' =>
      ∀ p, ResetArc t p → M' p = EmittedTo e p)) ∧
    (∀ δ e, on (fun M M' => Q t M δ e M'), shall (fun M _ => ∀ p, p ∈ inPlaces t →
      ResetArc t p →
        (δ.inputs p).length = Consumes t (Counts M) p ∧ List.Sublist (δ.inputs p) (M p))) ∧
    (∀ δ e, on (fun M M' => Q t M δ e M'), shall (fun _ _ => ∀ p, ReadArc t p → ResetArc t p →
      δ.reads p = [])) ∧
    (∀ M e, (∃ p, ResetArc t p ∧ M p = []) → Enabled t (Counts M) →
      (∃ ch, deposit (Consumes t (Counts M)) (OutputSpec t) ch = some (e.map Prod.fst)) →
      ∃ δ M', Q t M δ e M')

/-- The firing that drains before it peeks kills the mutant: it satisfies the mutant reading,
but not EXEC-013. Firing `exec013_t` hands the action no read token from place `1`, which held
`20` before the drain (AC4). -/
@[evidence mutant EXEC_013]
theorem EXEC_013_mutant_resetFirst_killed :
    EXEC_013_mutant_resetFirst (exec013_resetFirst (N := Nat) (T := Nat)) ∧
      ¬ EXEC_013 (exec013_resetFirst (N := Nat) (T := Nat)) := by
  refine ⟨fun t hw => ⟨fun δ e M M' h p hp => ?_, fun δ e M M' h p _ _ => ?_,
      fun δ e M M' h p _ hp => ?_,
      fun M e _ hen hd => ⟨_, _, hen, hd, rfl, rfl⟩⟩, fun h => ?_⟩
  · obtain ⟨-, -, -, rfl⟩ := h
    rw [qFire_apply, if_pos hp, List.nil_append]
  · obtain ⟨hen, -, rfl, -⟩ := h
    exact exec013_qInputs hen p
  · obtain ⟨-, -, rfl, -⟩ := h
    show qReadsBag (qConsume M t) t.core.reads p = []
    rw [qReadsBag_apply]
    simp [qConsume, show p ∈ t.core.resets from hp]
  · have hq : exec013_resetFirst exec013_t exec013_M
        ⟨qInputs exec013_M exec013_t, qReadsBag (qConsume exec013_M exec013_t) exec013_t.core.reads⟩
        exec013_e (qFire exec013_M exec013_t exec013_e) :=
      ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩
    have := ((h exec013_t (by decide)).2.2.1 _ _ _ _ hq 1 (by decide) (by decide)).1
    revert this
    decide

/-! ### Mutant: reset draining before input consumption -/

/-- A queue firing that drains the reset places before it takes its inputs: the delivered
inputs are taken from the drained marking (`qConsume`), the read bag and the result are the
reference's. -/
def exec013_drainFirst {N T : Type} [DecidableEq N] : QFireRel N T := fun t M δ e M' =>
  Enabled t (Counts M) ∧
    (∃ ch, deposit (Consumes t (Counts M)) (OutputSpec t) ch = some (e.map Prod.fst)) ∧
    δ = ⟨fun p => (qConsume M t p).take (qTake M t p), qReads M t⟩ ∧ M' = qFire M t e

/-- Mutant reading of EXEC-013 in which the drain comes before input consumption: line 2 says
an input place that is also a reset place hands the action nothing. The other lines are as in
EXEC-013. -/
def EXEC_013_mutant_drainFirst {N T : Type} [DecidableEq N] (Q : QFireRel N T) : Prop :=
  ∀ t, NoInputRead t →
    (∀ δ e, on (fun M M' => Q t M δ e M'), shall (fun _ M' =>
      ∀ p, ResetArc t p → M' p = EmittedTo e p)) ∧
    (∀ δ e, on (fun M M' => Q t M δ e M'), shall (fun _ _ => ∀ p, p ∈ inPlaces t →
      ResetArc t p → δ.inputs p = [])) ∧
    (∀ δ e, on (fun M M' => Q t M δ e M'), shall (fun M _ => ∀ p, ReadArc t p → ResetArc t p →
      δ.reads p ≠ [] ∧ ∀ tok ∈ δ.reads p, Head M p = some tok)) ∧
    (∀ M e, (∃ p, ResetArc t p ∧ M p = []) → Enabled t (Counts M) →
      (∃ ch, deposit (Consumes t (Counts M)) (OutputSpec t) ch = some (e.map Prod.fst)) →
      ∃ δ M', Q t M δ e M')

/-- The firing that drains before it consumes kills the mutant: it satisfies the mutant reading,
but not EXEC-013. Firing `exec013_t` hands the action no token from the input and reset place
`0`, whose `one()` input arc consumes one (AC4, 'input consumption first'). -/
@[evidence mutant EXEC_013]
theorem EXEC_013_mutant_drainFirst_killed :
    EXEC_013_mutant_drainFirst (exec013_drainFirst (N := Nat) (T := Nat)) ∧
      ¬ EXEC_013 (exec013_drainFirst (N := Nat) (T := Nat)) := by
  refine ⟨fun t hw => ⟨fun δ e M M' h p hp => ?_, fun δ e M M' h p _ hp => ?_,
      fun δ e M M' h p hp _ => ?_,
      fun M e _ hen hd => ⟨_, _, hen, hd, rfl, rfl⟩⟩, fun h => ?_⟩
  · obtain ⟨-, -, -, rfl⟩ := h
    rw [qFire_apply, if_pos hp, List.nil_append]
  · obtain ⟨-, -, rfl, -⟩ := h
    show (qConsume M t p).take (qTake M t p) = []
    simp [qConsume, show p ∈ t.core.resets from hp]
  · obtain ⟨h1, h2, rfl, -⟩ := h
    exact exec013_ref_reads hw (δ := qDelivered M t) (M' := qFire M t e) ⟨h1, h2, rfl, rfl⟩ hp
  · have hq : exec013_drainFirst exec013_t exec013_M
        ⟨fun p => (qConsume exec013_M exec013_t p).take (qTake exec013_M exec013_t p),
          qReads exec013_M exec013_t⟩
        exec013_e (qFire exec013_M exec013_t exec013_e) :=
      ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩
    have := ((h exec013_t (by decide)).2.1 _ _ _ _ hq 0 (by decide) (by decide)).1
    revert this
    decide

/-! ### Mutant: the action's outputs before the drain -/

/-- A queue firing that deposits the emitted tokens first and then runs the consume step on the
result: inputs and the drain see the action's outputs. -/
def exec013_outputsFirst {N T : Type} [DecidableEq N] : QFireRel N T := fun t M δ e M' =>
  Enabled t (Counts M) ∧
    (∃ ch, deposit (Consumes t (Counts M)) (OutputSpec t) ch = some (e.map Prod.fst)) ∧
    δ = qDelivered M t ∧ M' = qConsume (qAppend M e) t

/-- Mutant reading of EXEC-013 in which the action's outputs are deposited before the drain:
line 1 says a reset place ends empty. The other lines are as in EXEC-013. -/
def EXEC_013_mutant_outputsFirst {N T : Type} [DecidableEq N] (Q : QFireRel N T) : Prop :=
  ∀ t, NoInputRead t →
    (∀ δ e, on (fun M M' => Q t M δ e M'), shall (fun _ M' => ∀ p, ResetArc t p → M' p = [])) ∧
    (∀ δ e, on (fun M M' => Q t M δ e M'), shall (fun M _ => ∀ p, p ∈ inPlaces t →
      ResetArc t p →
        (δ.inputs p).length = Consumes t (Counts M) p ∧ List.Sublist (δ.inputs p) (M p))) ∧
    (∀ δ e, on (fun M M' => Q t M δ e M'), shall (fun M _ => ∀ p, ReadArc t p → ResetArc t p →
      δ.reads p ≠ [] ∧ ∀ tok ∈ δ.reads p, Head M p = some tok)) ∧
    (∀ M e, (∃ p, ResetArc t p ∧ M p = []) → Enabled t (Counts M) →
      (∃ ch, deposit (Consumes t (Counts M)) (OutputSpec t) ch = some (e.map Prod.fst)) →
      ∃ δ M', Q t M δ e M')

/-- The firing that deposits first kills the mutant: it satisfies the mutant reading, but not
EXEC-013. Firing `exec013_t` emits `99` to the reset place `0`, and the drain that follows
removes it, so place `0` ends empty instead of holding `99`. -/
@[evidence mutant EXEC_013]
theorem EXEC_013_mutant_outputsFirst_killed :
    EXEC_013_mutant_outputsFirst (exec013_outputsFirst (N := Nat) (T := Nat)) ∧
      ¬ EXEC_013 (exec013_outputsFirst (N := Nat) (T := Nat)) := by
  refine ⟨fun t hw => ⟨fun δ e M M' h p hp => ?_, fun δ e M M' h p _ _ => ?_,
      fun δ e M M' h p hp _ => ?_,
      fun M e _ hen hd => ⟨_, _, hen, hd, rfl, rfl⟩⟩, fun h => ?_⟩
  · obtain ⟨-, -, -, rfl⟩ := h
    simp [qConsume, show p ∈ t.core.resets from hp]
  · obtain ⟨hen, -, rfl, -⟩ := h
    exact exec013_qInputs hen p
  · exact exec013_ref_reads hw ⟨h.1, h.2.1, h.2.2.1, rfl⟩ hp
  · have hq : exec013_outputsFirst exec013_t exec013_M (qDelivered exec013_M exec013_t)
        exec013_e (qConsume (qAppend exec013_M exec013_e) exec013_t) :=
      ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩
    have := (h exec013_t (by decide)).1 _ _ _ _ hq 0 (by decide)
    revert this
    decide

/-! ### Every line exercised -/

/-- Every line of EXEC-013 is exercised by the reference, firing `exec013_t` (a `one()` input
on `0`; a read on `1`; resets on `0`, `1`, `3`, `4`) from `exec013_M` with emission `99` to
place `0`: the action receives the token `10` from the queue `10, 11, 12` of the input and
reset place `0` (line 2, input before drain) and the pre-drain head `20` of the read and reset
place `1` (line 3, AC4); place `0` ends with the emitted `99` only (line 1, outputs after the
drain), place `1` and the five-token place `3` end empty (line 1, AC1), the unmarked reset place
`4` ends empty, the drain removing nothing (line 1, AC2), and the firing exists although `4` is
unmarked (line 4, AC2). -/
@[evidence nonvacuous EXEC_013]
theorem EXEC_013_nonvacuous :
    RefQFire exec013_t exec013_M (qDelivered exec013_M exec013_t) exec013_e
        (qFire exec013_M exec013_t exec013_e) ∧
      (qDelivered exec013_M exec013_t).inputs 0 = [10] ∧
      (qDelivered exec013_M exec013_t).reads 1 = [20] ∧
      qFire exec013_M exec013_t exec013_e 0 = [99] ∧
      qFire exec013_M exec013_t exec013_e 1 = [] ∧
      exec013_M 3 = [30, 31, 32, 33, 34] ∧ qFire exec013_M exec013_t exec013_e 3 = [] ∧
      exec013_M 4 = [] ∧ qFire exec013_M exec013_t exec013_e 4 = [] ∧
      NoInputRead exec013_t :=
  ⟨exec013_t_fires, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

end Libpetri.Spec
