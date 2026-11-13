import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.Glossary

set_option linter.missingDocs true

/-!
# IO-003: Input All (`spec/02-input-output-specs.md`)

A predicate over an abstract firing relation `F : FireRel N`, checked against the reference
semantics (`RefFire`), against concrete firing relations that break it, and against one mutant
reading per clause.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## Local terms -/

/-- **All input arc** (local term, read from the glossary's *Input arc*): the input arc of `t`
on `p` has cardinality `All`. Like `InputArc`, it names the arc enablement and consumption use
(the first input arc on `p`). -/
abbrev AllArc {N : Type} [DecidableEq N] (t : Trans N) (p : N) : Prop := InputArc t p .all

/-- `t` with every `All` input arc on `p` removed and nothing else changed: the transition the
`All` arc on `p` would leave behind if it played no part in enablement. -/
def withoutAll {N : Type} [DecidableEq N] (t : Trans N) (p : N) : Trans N :=
  { t with core := { t.core with
      inputs := t.core.inputs.filter (fun s => !(decide (s.place = p) && decide (s.card = .all))) } }

/-! ## IO-003: Input All -/

requirement IO_003
  id "IO-003"
  title "Input All"
  kind B
  scope "all executors"
  source verbatim "spec/02-input-output-specs.md"
  quote "*While* the place of an `All` input arc of a transition is unmarked, the transition *shall not* fire."
        "*While* the place of an `All` input arc of a transition is marked and is not a correlated input of the transition's match specification ([NU-020]), the `All` input arc *shall not* affect whether the transition can fire."
        "*When* a transition fires, it *shall* consume every token from the place of each of its `All` input arcs that is not a correlated input of its match specification ([NU-020])."
        "*When* a transition fires, the place of each of its `All` input arcs that is neither an output place of the transition nor a correlated input of its match specification *shall* end the firing empty."
  reading "For every transition t and every place p on which t has an `All` input arc:"
          "t does not fire from a marking in which p is unmarked;"
          "from a marking in which p is marked, t can fire exactly when t without its `All` input arcs on p can fire;"
          "every firing of t that deposits d leaves p holding exactly the tokens d puts there;"
          "if p is not an output place of t, every firing of t leaves p empty, whatever deposit the firing reports."
  assumes "A firing is read as one step from a marking to a marking (glossary: Fire); timing and priority play no part. 'Can fire' is read as 'some firing to some marking exists'."
          "Correlated inputs (ruling D30, extending D16): the second, third and fourth quoted shall sentences exclude a correlated input of a ν-net match specification (NU-020), where an `All` arc consumes the tokens of the chosen name only and leaves the others, as the section's last sentence says. The transitions of the model (Reference.Trans) carry no match specification, so every input place is one that is not a correlated input, and the second to fourth lines quantify over every `All` input arc. How a correlated input counts and consumes is NU-020's, not encoded here."
          "The first two lines together say that the `All` arc requires exactly one token: `requiredCount()` returns 1 (the first bullet; `Card.required .all = 1`)."
          "'Consume every token' is read through the place's count after the firing: p ends holding only what this firing deposited in p, so it kept none of its own tokens. This is the second bullet, `consumptionCount(available)` returns `available`. A firing that also deposits into p (p is an output place of t) leaves those tokens in p."
          "AC1 (enables when the place has >= 1 token) is the second line: with p marked the `All` arc removes no firing. AC3 (0 tokens, not enabled) is the first line. AC2 (all tokens consumed, place empty after) is the third line, with 'empty' read as 'empty apart from this firing's own deposit into p', and the fourth line, where p is not an output place and 'empty' is literal."
          "The fourth line is the guard IO-001 also carries: it does not trust the deposit a firing reports. On a place that t's output spec does not name (glossary: Output arc) no firing can deposit (CORE-035, CORE-063), so there the drain shows in the marking alone, as an empty place. Without it, a firing that keeps p's tokens and reports them as its own deposit into p would pass the third line. The fourth line stands alone: it needs neither the third line nor CORE-035."
          "A reset arc on p does not weaken the fourth line: the spec sentence has no reset exclusion, and a reset place that is not an output place ends holding what the firing deposited there (CORE-034), which is nothing."
          "Deposits are compared per place (CORE-036): the lines read the count `Deposits d p` and the marking's count at p, never the order of d."
          "Which token is consumed first, and that the consumed tokens reach the action, are below the count granularity of a firing relation; they are not encoded."
          "A firing is one step at the count granularity: EXEC-003 AC5 (an `All` or `AtLeast` arc that fires later in a firing pass drains only the tokens the firing may drain, and leaves in place the tokens a synchronous action deposited earlier in the same pass) is below this granularity; that refinement is EXEC-003's subject and the reference executor's (RefExec, wave W5), not this block's."
          "A transition with two input arcs on p is rejected at build by CORE-030. On such a transition the formula reads the first arc on p, as the reference does (`InputArc`); `withoutAll` removes only the `All` arcs on p."
  signoff "2026-11-13 f3ab08fa5c1929cf ai"
  statement : ∀ {N : Type} [DecidableEq N], FireRel N → Prop :=
    fun F => ∀ t p, AllArc t p →
      (while (fun m => ¬ Marked m p), never Fire F t) ∧
      (∀ m, Marked m p → ((∃ m', Fire F t m m') ↔ (∃ m', Fire F (withoutAll t p) m m'))) ∧
      (∀ d, on (fun m m' => F t m d m'), shall (fun _ m' => m' p = Deposits d p)) ∧
      (¬ OutputArc t p → ∀ d, on (fun m m' => F t m d m'), shall (fun _ m' => m' p = 0))

/- The pinned readable form of IO-003: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.IO_003 : {N : Type} → [DecidableEq N] → FireRel N → Prop :=
fun {N} [DecidableEq N] F =>
  ∀ (t : Reference.Trans N) (p : N),
    AllArc t p →
      (while fun m => ¬Marked m p, never Fire F t) ∧
        (∀ (m : CountMarking N), Marked m p → ((∃ m', Fire F t m m') ↔ ∃ m', Fire F (withoutAll t p) m m')) ∧
          (∀ (d : List N), on fun m m' => F t m d m', shall fun x m' => m' p = Deposits d p) ∧
            (¬OutputArc t p → ∀ (d : List N), on fun m m' => F t m d m', shall fun x m' => m' p = 0)
-/
#guard_msgs in #print IO_003

/-! ## Lemmas over the reference semantics -/

/-- `cross` of two non-empty alternative lists is non-empty. -/
theorem io003_cross_ne_nil {N : Type} {xs ys : List (List N)} (hx : xs ≠ []) (hy : ys ≠ []) :
    cross xs ys ≠ [] := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hx
  obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hy
  simp [cross]

/-- Every output spec offers at least one output branch. -/
theorem io003_branches_ne_nil {N : Type} : ∀ o : Out N, o.branches ≠ []
  | .place _ => by simp [Out.branches]
  | .forward _ _ => by simp [Out.branches]
  | .and l r => io003_cross_ne_nil (io003_branches_ne_nil l) (io003_branches_ne_nil r)
  | .xor l _ => by simp [Out.branches, io003_branches_ne_nil l]
  | .timeout c => io003_branches_ne_nil c

/-- Under the reference semantics a transition can fire exactly when it is enabled: its output
spec always offers a way to end (the first output branch, or the empty deposit). -/
theorem io003_canFire_ref_iff {N : Type} [DecidableEq N] (t : Trans N) (m : N → Nat) :
    (∃ m', Fire RefFire t m m') ↔ Enabled t m := by
  constructor
  · rintro ⟨m', d, hen, -⟩
    exact hen
  · intro hen
    have : ∃ d, deposit (nconsumed m t.core) t.out (.action 0) = some d := by
      cases h : t.out with
      | none => exact ⟨[], rfl⟩
      | some o =>
        obtain ⟨b, bs, hb⟩ := List.exists_cons_of_ne_nil (io003_branches_ne_nil o)
        exact ⟨b, by simp [deposit, hb]⟩
    obtain ⟨d, hd⟩ := this
    exact ⟨_, d, hen, ⟨.action 0, hd⟩, rfl⟩

/-- An `All` arc on `p` lies among the transition's input arcs, on `p`. -/
theorem io003_allArc_mem {N : Type} [DecidableEq N] {t : Trans N} {p : N} (h : AllArc t p) :
    ∃ s ∈ t.core.inputs, s.place = p ∧ s.card = .all := by
  obtain ⟨s, hs, hc⟩ := h
  refine ⟨s, List.mem_of_find?_eq_some hs, ?_, hc⟩
  simpa using List.find?_some hs

/-- An enabled transition has its `All` place marked: the arc asks for one token. -/
theorem io003_enabled_marked {N : Type} [DecidableEq N] {t : Trans N} {p : N}
    {m : N → Nat} (hp : AllArc t p) (hen : Enabled t m) : Marked m p := by
  obtain ⟨s, hs, hsp, hsc⟩ := io003_allArc_mem hp
  have := ((enabled_iff t m).1 hen).1 s hs
  rw [hsp, hsc] at this
  exact Nat.pos_iff_ne_zero.mp this

/-- With `p` marked, removing the `All` arcs on `p` does not change enablement: each of them
asks for one token, which `p` has. -/
theorem io003_enabled_withoutAll {N : Type} [DecidableEq N] (t : Trans N) (p : N)
    (m : N → Nat) (hp : Marked m p) :
    Enabled (withoutAll t p) m ↔ Enabled t m := by
  have h1 : 1 ≤ m p := Nat.pos_of_ne_zero hp
  simp only [Enabled, enabledNA, withoutAll, Bool.and_eq_true, List.all_eq_true,
    List.mem_filter, decide_eq_true_eq, and_imp]
  constructor
  · rintro ⟨⟨hi, hh⟩, hr⟩
    refine ⟨⟨fun s hs => ?_, hh⟩, hr⟩
    by_cases e : s.place = p ∧ s.card = .all
    · obtain ⟨e1, e2⟩ := e
      simp [e1, e2, Card.required, h1]
    · exact hi s hs (by simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]; exact not_and_or.mp e)
  · rintro ⟨⟨hi, hh⟩, hr⟩
    exact ⟨⟨fun s hs _ => hi s hs, hh⟩, hr⟩

/-- A reference firing leaves the place of an `All` arc holding exactly what it deposited there. -/
theorem io003_ref_drain {N : Type} [DecidableEq N] {t : Trans N} {p : N} (hp : AllArc t p)
    {m m' : N → Nat} {d : List N} (hf : RefFire t m d m') : m' p = Deposits d p := by
  rw [refFire_apply hf p]
  split
  · rfl
  · obtain ⟨s, hs, hc⟩ := hp
    rw [consumes_eq, hs]
    simp [consumptionCount, hc, Card.consumesAll]

/-! ## Evidence -/

/-- The reference semantics satisfies IO-003: `Seam.enabledNA` asks `Card.required .all = 1`
token of an `All` place, so the transition does not fire while it is unmarked and the arc asks
nothing more while it is marked; `Seam.nconsumed` takes every token of an `All` place, so the
place ends with only what the firing deposited there (`refFire_apply`); and a reference firing
deposits only in output places, so an `All` place that is not one ends empty. -/
@[evidence holds IO_003]
theorem IO_003_reference {N : Type} [DecidableEq N] : IO_003 (RefFire (N := N)) := by
  intro t p hp
  refine ⟨?_, fun m hm => ?_, fun d m m' hf => io003_ref_drain hp hf,
    fun ho d m m' hf => ?_⟩
  · rintro m m' ⟨d, hen, -, -⟩ hm
    exact hm (io003_enabled_marked hp hen)
  · rw [io003_canFire_ref_iff, io003_canFire_ref_iff, io003_enabled_withoutAll t p m hm]
  · show m' p = 0
    rw [io003_ref_drain hp hf]
    exact List.count_eq_zero_of_not_mem (fun h => ho (refFire_outputs hf p h))

/-! ### Examples over a one-place net -/

/-- The transition of the examples: one `All` input arc on place `0`, nothing else, no output
spec. -/
def io003_t : Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .all⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- `io003_t` has no output place. -/
theorem io003_t_noOut (p : Nat) : ¬ OutputArc io003_t p := by
  rintro ⟨o, h, -⟩; simp [io003_t] at h

/-- The marking of the examples in which every place holds five tokens (the test derivation's
five tokens). -/
def io003_five : Nat → Nat := fun _ => 5

/-- The marking of the examples in which place `0` holds four tokens and every other place
five: what a firing that consumes one token of `0` leaves behind. -/
def io003_four : Nat → Nat := fun n => if n = 0 then 4 else 5

/-- The marking of the examples in which place `0` is empty and every other place holds five
tokens: what a firing that drains place `0` leaves behind. -/
def io003_drained : Nat → Nat := fun n => if n = 0 then 0 else 5

/-- The marking of the examples in which every place is empty. -/
def io003_empty : Nat → Nat := fun _ => 0

/-- An input arc with cardinality `All` read as cardinality `c`; any other arc unchanged. -/
def io003_allAs (c : Card) (s : NInSpec Nat) : NInSpec Nat :=
  if s.card = .all then ⟨s.place, c⟩ else s

/-- `t` with each `All` input arc read as `One`. -/
def io003_allAsOne (t : Trans Nat) : Trans Nat :=
  { t with core := { t.core with inputs := t.core.inputs.map (io003_allAs .one) } }

/-- A firing relation that reads `All` as `One`: a reference firing of the transition with each
`All` arc replaced by `One`. -/
def io003_allAsOneFire : FireRel Nat := fun t => RefFire (io003_allAsOne t)

/-- The firing of `io003_t` from five tokens under `io003_allAsOneFire`: one token of place `0`
taken, nothing deposited. -/
theorem io003_allAsOne_step : io003_allAsOneFire io003_t io003_five [] io003_four :=
  ⟨by decide, ⟨.action 0, rfl⟩, by
    funext n
    rcases n with _ | n <;>
      simp [fireNC, depProd, nconsumed, nspecAt, io003_allAsOne, io003_allAs, io003_t,
        io003_five, io003_four, Card.consumesAll, Card.required]⟩

/-- ✗ Reading `All` as `One` violates IO-003 (third clause): from five tokens `io003_t`
consumes one and leaves four, although it deposits nothing in place `0`. -/
@[evidence forbids IO_003]
theorem IO_003_forbids_allAsOne : ¬ IO_003 io003_allAsOneFire := by
  intro h
  have := (h io003_t 0 ⟨_, rfl, rfl⟩).2.2.1 [] io003_five io003_four io003_allAsOne_step
  exact absurd this (by decide)

/-- `t` with each `All` input arc read as `AtLeast(0)`: it still drains its place, but asks for
no token. -/
def io003_allAsAtLeast0 (t : Trans Nat) : Trans Nat :=
  { t with core := { t.core with inputs := t.core.inputs.map (io003_allAs (.atLeast 0)) } }

/-- A firing relation in which an `All` arc asks for no token: a reference firing of the
transition with each `All` arc replaced by `AtLeast(0)`. -/
def io003_requiresNothingFire : FireRel Nat := fun t => RefFire (io003_allAsAtLeast0 t)

/-- ✗ An `All` arc that asks for no token violates IO-003 (first clause): `io003_t` fires from
the empty marking. -/
@[evidence forbids IO_003]
theorem IO_003_forbids_requiresNothing : ¬ IO_003 io003_requiresNothingFire := by
  intro h
  have hf : Fire io003_requiresNothingFire io003_t io003_empty io003_empty :=
    ⟨[], by decide, ⟨.action 0, rfl⟩, by
      funext n
      simp [fireNC, depProd, nconsumed, nspecAt, io003_allAsAtLeast0, io003_allAs, io003_t, io003_empty,
        Card.consumesAll]⟩
  exact (h io003_t 0 ⟨_, rfl, rfl⟩).1 _ _ hf (by decide)

/-- The marking that holds one token in place `0` and none elsewhere: `Deposits [0]` read as a
marking. -/
def io003_phantom : Nat → Nat := fun n => Deposits [0] n

/-- A firing relation that keeps no input token in the marking but reports a deposit it never
made: an enabled transition fires, reports one token deposited in place `0`, and leaves exactly
that one token in place `0` and nothing elsewhere, whether or not its output spec names `0`. -/
def io003_phantomFire : FireRel Nat :=
  fun t m d m' => Enabled t m ∧ d = [0] ∧ m' = io003_phantom

/-- ✗ A reported deposit in a place the output spec does not name violates IO-003 (fourth
clause): `io003_t` has no output place, yet its firing from five tokens leaves one token in its
`All` place `0`. The third clause alone accepts it, because the firing reports that token as its
own deposit. -/
@[evidence forbids IO_003]
theorem IO_003_forbids_phantomDeposit : ¬ IO_003 io003_phantomFire := by
  intro h
  have := (h io003_t 0 ⟨_, rfl, rfl⟩).2.2.2 (io003_t_noOut 0) [0] io003_five io003_phantom
    ⟨by decide, rfl, rfl⟩
  exact absurd this (by decide)

/-! ### Mutants: one per clause -/

/-- Mutant reading of IO-003 that drops the first clause: the `All` arc need not stop the
transition while its place is unmarked. -/
def IO_003_mutant_dropUnmarked {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t p, AllArc t p →
    (∀ m, Marked m p → ((∃ m', Fire F t m m') ↔ (∃ m', Fire F (withoutAll t p) m m'))) ∧
    (∀ d, on (fun m m' => F t m d m'), shall (fun _ m' => m' p = Deposits d p)) ∧
    (¬ OutputArc t p → ∀ d, on (fun m m' => F t m d m'), shall (fun _ m' => m' p = 0))

/-- The firing that empties the net: every transition fires from every marking, deposits
nothing and leaves every place empty. -/
def io003_wipeFire : FireRel Nat := fun _ _ d m' => d = [] ∧ m' = io003_empty

/-- The wiping firing kills the first mutant: whether a transition fires does not depend on its
arcs, and every place ends empty (second, third and fourth clauses hold), but `io003_t` fires
from the empty marking (the first clause fails). -/
@[evidence mutant IO_003]
theorem IO_003_mutant_dropUnmarked_killed :
    IO_003_mutant_dropUnmarked io003_wipeFire ∧ ¬ IO_003 io003_wipeFire := by
  refine ⟨fun t p _ => ⟨fun m _ => ?_, ?_, fun _ => ?_⟩, fun h => ?_⟩
  · exact ⟨fun _ => ⟨_, [], rfl, rfl⟩, fun _ => ⟨_, [], rfl, rfl⟩⟩
  · rintro d m m' ⟨rfl, rfl⟩
    rfl
  · rintro d m m' ⟨rfl, rfl⟩
    rfl
  · exact (h io003_t 0 ⟨_, rfl, rfl⟩).1 io003_empty io003_empty ⟨[], rfl, rfl⟩ (by decide)

/-- Mutant reading of IO-003 that drops the second clause: with its place marked, the `All` arc
may still stop the transition. -/
def IO_003_mutant_dropMarked {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t p, AllArc t p →
    (while (fun m => ¬ Marked m p), never Fire F t) ∧
    (∀ d, on (fun m m' => F t m d m'), shall (fun _ m' => m' p = Deposits d p)) ∧
    (¬ OutputArc t p → ∀ d, on (fun m m' => F t m d m'), shall (fun _ m' => m' p = 0))

/-- A firing relation in which an `All` arc blocks its transition whatever the marking: a
transition with no `All` arc fires from every marking, emptying the net; one with an `All` arc
never fires. -/
def io003_allBlocksFire : FireRel Nat :=
  fun t _ d m' => (∀ s ∈ t.core.inputs, s.card ≠ .all) ∧ d = [] ∧ m' = io003_empty

/-- The always-blocking firing kills the second mutant: a transition with an `All` arc never
fires, so the first, third and fourth clauses hold vacuously; but from five tokens `io003_t`
does not fire although without its `All` arc it does (the second clause fails). -/
@[evidence mutant IO_003]
theorem IO_003_mutant_dropMarked_killed :
    IO_003_mutant_dropMarked io003_allBlocksFire ∧ ¬ IO_003 io003_allBlocksFire := by
  refine ⟨fun t p hp => ?_, fun h => ?_⟩
  · obtain ⟨s, hs, -, hc⟩ := io003_allArc_mem hp
    refine ⟨?_, ?_, fun _ => ?_⟩
    · rintro m m' ⟨d, hno, -⟩ -
      exact hno s hs hc
    · rintro d m m' ⟨hno, -⟩
      exact absurd hc (hno s hs)
    · rintro d m m' ⟨hno, -⟩
      exact absurd hc (hno s hs)
  · have hw : ∃ m', Fire io003_allBlocksFire (withoutAll io003_t 0) io003_five m' :=
      ⟨_, [], by decide, rfl, rfl⟩
    obtain ⟨m', d, hno, -⟩ :=
      ((h io003_t 0 ⟨_, rfl, rfl⟩).2.1 io003_five (by decide)).2 hw
    exact hno _ (List.mem_singleton_self _) rfl

/-- A firing relation that fires an enabled transition, reports any deposit and leaves every
place empty: enablement as the reference has it, the marking afterwards blind to the deposit. -/
def io003_drainAllFire : FireRel Nat := fun t m _ m' => Enabled t m ∧ m' = io003_empty

/-- Under a firing relation that fires exactly the enabled transitions, an `All` arc gates as
the first two clauses say. -/
theorem io003_gate_of_enabled (F : FireRel Nat)
    (hF : ∀ t m, (∃ m', Fire F t m m') ↔ Enabled t m)
    (hE : ∀ t m d m', F t m d m' → Enabled t m) (t : Trans Nat) (p : Nat) (hp : AllArc t p) :
    (while (fun m => ¬ Marked m p), never Fire F t) ∧
    (∀ m, Marked m p → ((∃ m', Fire F t m m') ↔ (∃ m', Fire F (withoutAll t p) m m'))) := by
  refine ⟨?_, fun m hm => ?_⟩
  · rintro m m' ⟨d, hf⟩ hm
    exact hm (io003_enabled_marked hp (hE _ _ _ _ hf))
  · rw [hF, hF, io003_enabled_withoutAll t p m hm]

/-- Mutant reading of IO-003 that drops the third clause: the `All` arc gates the transition
and drains a place that is not an output place, but a firing need not leave an output place
holding what it deposited there. -/
def IO_003_mutant_dropDrain {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t p, AllArc t p →
    (while (fun m => ¬ Marked m p), never Fire F t) ∧
    (∀ m, Marked m p → ((∃ m', Fire F t m m') ↔ (∃ m', Fire F (withoutAll t p) m m'))) ∧
    (¬ OutputArc t p → ∀ d, on (fun m m' => F t m d m'), shall (fun _ m' => m' p = 0))

/-- The net-emptying firing of enabled transitions kills the third mutant: it fires exactly the
enabled transitions (first and second clauses) and leaves every place empty (fourth clause),
but when it reports a deposit of one token in place `0`, place `0` does not hold it (the third
clause fails). -/
@[evidence mutant IO_003]
theorem IO_003_mutant_dropDrain_killed :
    IO_003_mutant_dropDrain io003_drainAllFire ∧ ¬ IO_003 io003_drainAllFire := by
  have hF : ∀ t m, (∃ m', Fire io003_drainAllFire t m m') ↔ Enabled t m :=
    fun t m => ⟨fun ⟨_, _, he, _⟩ => he, fun he => ⟨_, [], he, rfl⟩⟩
  refine ⟨fun t p hp => ?_, fun h => ?_⟩
  · obtain ⟨h1, h2⟩ := io003_gate_of_enabled _ hF (fun _ _ _ _ hf => hf.1) t p hp
    refine ⟨h1, h2, fun _ d m m' hf => ?_⟩
    rw [hf.2]
    rfl
  · have := (h io003_t 0 ⟨_, rfl, rfl⟩).2.2.1 [0] io003_five io003_empty ⟨by decide, rfl⟩
    exact absurd this (by decide)

/-- Mutant reading of IO-003 that drops the fourth clause: the reading before the guard, which
trusts the deposit a firing reports. -/
def IO_003_mutant_dropEmpty {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t p, AllArc t p →
    (while (fun m => ¬ Marked m p), never Fire F t) ∧
    (∀ m, Marked m p → ((∃ m', Fire F t m m') ↔ (∃ m', Fire F (withoutAll t p) m m'))) ∧
    (∀ d, on (fun m m' => F t m d m'), shall (fun _ m' => m' p = Deposits d p))

/-- The phantom-deposit firing kills the fourth mutant: it fires exactly the enabled transitions
(first and second clauses) and every place holds what the reported deposit puts there (third
clause), but `io003_t`, which has no output place, leaves a token in its `All` place (the fourth
clause fails). -/
@[evidence mutant IO_003]
theorem IO_003_mutant_dropEmpty_killed :
    IO_003_mutant_dropEmpty io003_phantomFire ∧ ¬ IO_003 io003_phantomFire := by
  have hF : ∀ t m, (∃ m', Fire io003_phantomFire t m m') ↔ Enabled t m :=
    fun t m => ⟨fun ⟨_, _, he, _⟩ => he, fun he => ⟨_, [0], he, rfl, rfl⟩⟩
  refine ⟨fun t p hp => ?_, IO_003_forbids_phantomDeposit⟩
  obtain ⟨h1, h2⟩ := io003_gate_of_enabled _ hF (fun _ _ _ _ hf => hf.1) t p hp
  refine ⟨h1, h2, ?_⟩
  rintro d m m' ⟨-, rfl, rfl⟩
  rfl

/-- All four clauses of IO-003 are exercised by the reference semantics: `io003_t` has an
`All` arc on place `0`, which is not an output place; it does not fire from the empty marking
(first clause); from five tokens it fires, as it does without its `All` arc (second clause);
and that firing deposits nothing and leaves place `0` empty while the other places keep their
tokens (third and fourth clauses, the test derivation's five tokens drained). -/
@[evidence nonvacuous IO_003]
theorem IO_003_nonvacuous :
    AllArc io003_t 0 ∧ ¬ OutputArc io003_t 0 ∧
      ¬ Fire RefFire io003_t io003_empty io003_empty ∧
      RefFire io003_t io003_five [] io003_drained ∧
      Fire RefFire (withoutAll io003_t 0) io003_five io003_five := by
  refine ⟨⟨_, rfl, rfl⟩, io003_t_noOut 0, ?_, ⟨by decide, ⟨.action 0, rfl⟩, ?_⟩,
    ⟨[], by decide, ⟨.action 0, rfl⟩, ?_⟩⟩
  · rintro ⟨d, hen, -⟩
    exact absurd hen (by decide)
  · funext n
    rcases n with _ | n <;>
      simp [fireNC, depProd, nconsumed, nspecAt, io003_t, io003_five, io003_drained,
        Card.consumesAll]
  · funext n
    simp [fireNC, depProd, nconsumed, nspecAt, withoutAll, io003_t, io003_five]

end Libpetri.Spec
