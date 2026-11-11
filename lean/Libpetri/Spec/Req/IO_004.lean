import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.Glossary

set_option linter.missingDocs true

/-!
# IO-004: Input AtLeast (`spec/02-input-output-specs.md`)

The requirement is a predicate over an abstract firing relation `F : FireRel N`. The evidence
theorems check it against the reference semantics (`Reference.Fires`, as `RefFire`), against
concrete firing relations that break it, and against one mutant reading per clause.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-- `t` with its input arc on `p` removed, and nothing else changed: the transition an
`AtLeast` arc that plays no part in enablement would leave behind. Only the first input arc on
`p` is removed, the one `InputArc` names (a malformed transition with two input arcs on `p`,
which [CORE-030] rejects at build, keeps the second). Local to IO-004; not a glossary term. -/
def withoutInputArc [DecidableEq N] (t : Trans N) (p : N) : Trans N :=
  { t with core := { t.core with inputs := t.core.inputs.eraseP (fun s => decide (s.place = p)) } }

/-! ## IO-004: Input AtLeast -/

requirement IO_004
  id "IO-004"
  title "Input AtLeast"
  kind B
  scope "all executors"
  source verbatim "spec/02-input-output-specs.md"
  quote "*While* the input place of an `AtLeast(place, minimum)` input arc holds fewer than `minimum` tokens, the transition *shall not* fire."
        "*While* the input place of an `AtLeast(place, minimum)` input arc holds at least `minimum` tokens and is not a correlated input of the transition's match specification ([NU-020]), the input arc *shall not* affect whether the transition can fire."
        "*When* a transition with an `AtLeast(place, minimum)` input arc fires, it *shall* consume every token the input place holds, unless the input place is a correlated input of its match specification ([NU-020])."
        "*When* a transition with an `AtLeast(place, minimum)` input arc fires, and the input place is neither an output place nor a correlated input of the match specification of the transition, the input place *shall* end the firing empty."
  reading "For every transition t, place p and number n such that the input arc of t on p is AtLeast(p, n):"
          "t does not fire from a marking in which p holds fewer than n tokens;"
          "from a marking m in which p holds at least n tokens, t can fire from m exactly when t without its input arc on p can fire from m;"
          "every firing of t, with whatever deposit d, leaves p holding exactly the tokens d deposited there (every token p held was consumed);"
          "if p is not an output place of t, every firing of t leaves p empty, whatever deposit the firing reports."
  assumes "A firing is read as one step from a marking to a marking (glossary: Fire); timing and priority play no part. 'Can fire' is read as 'some firing from m exists', whatever marking it leads to: removing the arc changes what the firing consumes from p, so only whether t fires is compared, not where it leads."
          "Correlated inputs (ruling D30, extending D16): the second, third and fourth quoted shall sentences exclude a correlated input of a ν-net match specification (NU-020), where an `AtLeast` arc requires and consumes the tokens of the chosen name only, as the section's last sentence says. The transitions of the model (Reference.Trans) carry no match specification, so every input place is one that is not a correlated input, and the second to fourth lines quantify over every `AtLeast` input arc. How a correlated input counts and consumes is NU-020's, not encoded here."
          "'The input arc on p' is the first input arc on p, as the glossary term Input arc reads it; `withoutInputArc` removes that one arc. [CORE-030] allows at most one input arc per place, so on a well-formed transition it is the only one."
          "AC1 (construction with minimum < 1 is rejected): not encoded. It is a build-time check on the net definition, outside the firing relation. The statement quantifies over every n, n = 0 included; the reference semantics satisfies it there too (AtLeast(p, 0) never blocks and drains p)."
          "AC2 (transition enables when the place has >= minimum tokens) is the second line: with p holding at least n tokens the arc does not stop t from firing. Read with [IO-005], the other arcs of t still decide."
          "AC3 (all tokens consumed on firing, not just minimum) is the third line, stated on the marking the firing leaves: p ends holding what was deposited there and nothing it held before. A reset arc on p ([CORE-034]) gives the same end count, so neither the third nor the fourth line needs a reset guard."
          "The fourth line is the guard IO-001 carries, so the block stands alone: the deposit a firing reports is not trusted for the count. On a place the output spec of t does not name, no firing of t can deposit ([CORE-035]), so the drain shows in the marking alone, as an empty place. Without it a firing that consumes nothing but reports a deposit in p equal to what p held would pass the third line."
          "AC4 (place with minimum - 1 tokens, transition not enabled) is the first line, at the count minimum - 1."
          "A firing is one step at the count granularity: EXEC-003 AC5 (an `All` or `AtLeast` arc that fires later in a firing pass drains only the tokens the firing may drain, and leaves in place the tokens a synchronous action deposited earlier in the same pass) is below this granularity; that refinement is EXEC-003's subject and the reference executor's (RefExec, wave W5), not this block's."
          "The two bullets (`requiredCount()` returns `minimum`, `consumptionCount(available)` returns `available`) are the pure-function contract of [IO-007] and the glossary terms Required count and Consumption count; this block encodes their effect on firing (lines 1 to 4), not the functions themselves."
          "The output-spec build checks ([IO-011] to [IO-014]) and the output validation skip ([CONC-026]) do not touch input consumption; the block holds of every firing relation over every transition, built or not."
  signoff "pending"
  statement : ∀ {N : Type} [DecidableEq N], FireRel N → Prop :=
    fun F => ∀ t p n, InputArc t p (.atLeast n) →
      (while (fun m => TokenCount m p < n), never Fire F t) ∧
      (∀ m, n ≤ TokenCount m p →
        ((∃ m', Fire F t m m') ↔ ∃ m', Fire F (withoutInputArc t p) m m')) ∧
      (∀ d, on (fun m m' => F t m d m'), shall (fun _ m' => TokenCount m' p = Deposits d p)) ∧
      (¬ OutputArc t p →
        ∀ d, on (fun m m' => F t m d m'), shall (fun _ m' => TokenCount m' p = 0))

/- The pinned readable form of IO-004: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.IO_004 : {N : Type} → [DecidableEq N] → FireRel N → Prop :=
fun {N} [DecidableEq N] F =>
  ∀ (t : Reference.Trans N) (p : N) (n : ℕ),
    InputArc t p (Card.atLeast n) →
      (while fun m => TokenCount m p < n, never Fire F t) ∧
        (∀ (m : CountMarking N),
            n ≤ TokenCount m p → ((∃ m', Fire F t m m') ↔ ∃ m', Fire F (withoutInputArc t p) m m')) ∧
          (∀ (d : List N), on fun m m' => F t m d m', shall fun x m' => TokenCount m' p = Deposits d p) ∧
            (¬OutputArc t p → ∀ (d : List N), on fun m m' => F t m d m', shall fun x m' => TokenCount m' p = 0)
-/
#guard_msgs in #print IO_004

/-! ### Lemmas for the reference semantics -/

/-- Removing the first element that satisfies `q` does not change `List.all f` when that element
satisfies `f`. -/
theorem all_eraseP_of_find? {α : Type} (l : List α) (q : α → Bool) (f : α → Bool) (s : α)
    (h : l.find? q = some s) (hf : f s = true) : (l.eraseP q).all f = l.all f := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    by_cases hq : q a = true
    · have : a = s := by simpa [List.find?, hq] using h
      subst this
      simp [List.eraseP_cons_of_pos hq, hf]
    · have h' : l.find? q = some s := by simpa [List.find?, hq] using h
      simp [List.eraseP_cons_of_neg hq, ih h']

/-- With `p` holding at least `n` tokens, `t` and `t` without its `AtLeast(p, n)` input arc are
enabled at the same markings. -/
theorem enabledNA_withoutInputArc {N : Type} [DecidableEq N] (t : Trans N) (p : N) (n : Nat)
    (m : N → Nat) (h : InputArc t p (.atLeast n)) (hm : n ≤ m p) :
    enabledNA m (withoutInputArc t p).core = enabledNA m t.core := by
  obtain ⟨s, hs, hc⟩ := h
  have hp : s.place = p := by simpa using List.find?_some hs
  have := all_eraseP_of_find? t.core.inputs (fun s => decide (s.place = p))
    (fun s => decide (s.card.required ≤ m s.place)) s hs
    (by simp [hc, hp, Card.required, hm])
  simp only [enabledNA, withoutInputArc, this]

/-- The number of timeout deposits a spec offers does not depend on what the firing consumed. -/
theorem timeoutDeposits_length {N : Type} (o : Out N) (c₁ c₂ : N → Nat) :
    (o.timeoutDeposits c₁).length = (o.timeoutDeposits c₂).length := by
  induction o with
  | place p => rfl
  | forward src dst => rfl
  | and l r ihl ihr => simp [Out.timeoutDeposits, cross, List.length_flatMap, ihl, ihr]
  | xor l r ihl ihr => simp [Out.timeoutDeposits, ihl, ihr]
  | timeout c ih => simpa [Out.timeoutDeposits] using ih

/-- Whether an output spec offers a way of ending does not depend on what the firing consumed. -/
theorem deposit_isSome {N : Type} (c₁ c₂ : N → Nat) (o : Option (Out N))
    (ch : Novel.ForwardDeposit.Choice) :
    (deposit c₁ o ch).isSome = (deposit c₂ o ch).isSome := by
  rcases o with _ | o <;> rcases ch with ⟨_ | i⟩ | j <;> simp only [deposit]
  cases o.findTimeout with
  | none => rfl
  | some c =>
    rw [Bool.eq_iff_iff]
    simp only [Option.bind_some, Option.isSome_iff_ne_none, ne_eq, List.getElem?_eq_none_iff,
      timeoutDeposits_length c c₁ c₂]

/-- Some reference firing of `t` from `m` exists exactly when `t` is enabled at `m` and its
output spec offers some way of ending, whatever the firing consumes. -/
theorem refFire_exists_iff {N : Type} [DecidableEq N] (t : Trans N) (m : N → Nat) :
    (∃ m', Fire RefFire t m m') ↔
      enabledNA m t.core = true ∧ ∃ ch, (deposit (fun _ => 0) t.out ch).isSome := by
  constructor
  · rintro ⟨m', d, hen, ⟨ch, hd⟩, -⟩
    exact ⟨hen, ch, by rw [deposit_isSome _ (nconsumed m t.core), hd]; rfl⟩
  · rintro ⟨hen, ch, hs⟩
    rw [deposit_isSome _ (nconsumed m t.core)] at hs
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 hs
    exact ⟨_, d, hen, ⟨ch, hd⟩, rfl⟩

/-- The reference semantics satisfies IO-004: `Seam.enabledNA` requires `requiredCount` =
`n` tokens in `p` (first line); with `p` holding that many, the arc's test passes, so removing
it leaves enablement unchanged, and whether the output spec offers an outcome does not depend on
consumption (second line); `Seam.nconsumed` takes every token of an `AtLeast` place, so `p` ends
with its deposit (third line); and a reference firing deposits only in places the output spec
names, so outside them that deposit is empty and `p` ends empty (fourth line). -/
@[evidence holds IO_004]
theorem IO_004_reference {N : Type} [DecidableEq N] : IO_004 (RefFire (N := N)) := by
  intro t p n h
  obtain ⟨s, hsmem, hsp, hsc⟩ := inputArc_mem h
  have hdrain : ∀ d m m', RefFire t m d m' → m' p = Deposits d p := by
    intro d m m' hf
    have hc : Consumes t m p = m p := by
      obtain ⟨s', hs', hc'⟩ := h
      simp [Consumes, nconsumed, hs', hc', Card.consumesAll]
    rw [refFire_apply hf p, hc]
    split <;> omega
  refine ⟨?_, fun m hm => ?_, fun d m m' hf => hdrain d m m' hf, fun ho d m m' hf => ?_⟩
  · rintro m m' ⟨d, hen, -, -⟩ hlt
    have := ((enabled_iff t m).1 hen).1 s hsmem
    simp [hsp, hsc, requiredCount, Card.required, TokenCount] at this hlt
    omega
  · rw [refFire_exists_iff, refFire_exists_iff, enabledNA_withoutInputArc t p n m h hm]
    rfl
  · show m' p = 0
    rw [hdrain d m m' hf]
    exact List.count_eq_zero_of_not_mem (fun hp => ho (refFire_outputs hf p hp))

/-! ### Examples over a one-place net -/

/-- The transition of the examples: one input arc `AtLeast(0, 3)`, no other arcs, no output
spec. -/
def io004_t : Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .atLeast 3⟩], inhibitors := [], reads := [],
              resets := [] },
    out := none }

/-- The marking of the examples in which every place holds 7 tokens. -/
def io004_seven : Nat → Nat := fun _ => 7

/-- The marking of the examples in which every place holds 2 tokens (one fewer than the
minimum, AC4). -/
def io004_two : Nat → Nat := fun _ => 2

/-- The marking `io004_t` leaves from `io004_seven`: place `0` drained, the others untouched. -/
def io004_drained : Nat → Nat := fun q => if q = 0 then 0 else 7

/-- The marking left from `io004_seven` when only the minimum, 3 tokens, is taken from place `0`. -/
def io004_four : Nat → Nat := fun q => if q = 0 then 4 else 7

/-- Every `AtLeast` input arc turned into `All`: the minimum is ignored and one token suffices. -/
def io004_allify (t : Trans Nat) : Trans Nat :=
  { t with core := { t.core with inputs := t.core.inputs.map fun s =>
      match s.card with
      | .atLeast _ => { s with card := .all }
      | _ => s } }

/-- A firing relation that ignores the minimum of `AtLeast`: a reference firing of the
transition with every `AtLeast` arc read as `All`. -/
def io004_ignoresMinimumFire : FireRel Nat := fun t => RefFire (io004_allify t)

/-- ✗ Ignoring the minimum violates IO-004 (first line): `io004_t` fires while place `0` holds 2
of its 3 required tokens. -/
@[evidence forbids IO_004]
theorem IO_004_forbids_ignoresMinimum : ¬ IO_004 io004_ignoresMinimumFire := by
  intro h
  have hfire : Fire io004_ignoresMinimumFire io004_t io004_two (fun q => if q = 0 then 0 else 2) :=
    ⟨[], by decide, ⟨.action 0, rfl⟩, by
      funext q; by_cases hq : q = 0 <;>
        simp [hq, eq_comm (a := 0), fireNC, depProd, nconsumed, nspecAt, io004_allify, io004_t,
          io004_two, Card.consumesAll]⟩
  exact (h io004_t 0 3 ⟨_, rfl, rfl⟩).1 _ _ hfire (by decide)

/-- Every `AtLeast(p, n)` input arc turned into `Exactly(p, n)`: only the minimum is taken. -/
def io004_exactlify (t : Trans Nat) : Trans Nat :=
  { t with core := { t.core with inputs := t.core.inputs.map fun s =>
      match s.card with
      | .atLeast n => { s with card := .exactly n }
      | _ => s } }

/-- A firing relation that takes only the minimum: a reference firing of the transition with
every `AtLeast` arc read as `Exactly`. -/
def io004_takesMinimumFire : FireRel Nat := fun t => RefFire (io004_exactlify t)

/-- ✗ Taking only the minimum violates IO-004 (third line), the test derivation's case:
`io004_t` fires from 7 tokens in place `0`, takes 3 and leaves 4. -/
@[evidence forbids IO_004]
theorem IO_004_forbids_takesMinimum : ¬ IO_004 io004_takesMinimumFire := by
  intro h
  have hfire : io004_takesMinimumFire io004_t io004_seven [] io004_four :=
    ⟨by decide, ⟨.action 0, rfl⟩, by
      funext q; by_cases hq : q = 0 <;>
        simp [hq, eq_comm (a := 0), fireNC, depProd, nconsumed, nspecAt, io004_exactlify, io004_t,
          io004_seven, io004_four, Card.consumesAll, Card.required]⟩
  have := (h io004_t 0 3 ⟨_, rfl, rfl⟩).2.2.1 [] _ _ hfire
  simp [TokenCount, Deposits, depProd, io004_four] at this

/-- `io004_t` has no output place: it has no output spec. -/
theorem io004_t_noOut (p : Nat) : ¬ OutputArc io004_t p := by
  rintro ⟨o, h, -⟩; simp [io004_t] at h

/-- A ghost-deposit firing relation: an enabled transition fires, reports a deposit of one token
in each of its input places, whether or not its output spec names them, and leaves every place
holding exactly what it reports as deposited there. -/
def io004_ghostFire : FireRel Nat :=
  fun t m d m' => Enabled t m ∧ d = t.core.inputs.map NInSpec.place ∧ m' = fun q => Deposits d q

/-- ✗ A firing that reports a deposit in an input place its output spec does not name violates
IO-004 (fourth line): `io004_t` has no output place, fires from 7 tokens in place `0` and leaves
1 token there, the one it claims to have deposited. -/
@[evidence forbids IO_004]
theorem IO_004_forbids_ghost : ¬ IO_004 io004_ghostFire := by
  intro h
  have := (h io004_t 0 3 ⟨_, rfl, rfl⟩).2.2.2 (io004_t_noOut 0) [0] io004_seven
    (fun q => Deposits [0] q) ⟨by decide, rfl, rfl⟩
  exact absurd this (by decide)

/-! ### Mutants: one per line -/

/-- Mutant reading of IO-004 that drops the first line: no minimum to wait for. -/
def IO_004_mutant_dropMinimum {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t p n, InputArc t p (.atLeast n) →
    (∀ m, n ≤ TokenCount m p →
      ((∃ m', Fire F t m m') ↔ ∃ m', Fire F (withoutInputArc t p) m m')) ∧
    (∀ d, on (fun m m' => F t m d m'), shall (fun _ m' => TokenCount m' p = Deposits d p)) ∧
    (¬ OutputArc t p →
      ∀ d, on (fun m m' => F t m d m'), shall (fun _ m' => TokenCount m' p = 0))

/-- A firing relation in which every transition may fire from every marking, depositing nothing
and emptying every place. -/
def io004_drainEverythingFire : FireRel Nat := fun _ _ d m' => d = [] ∧ m' = fun _ => 0

/-- The drain-everything firing kills the first mutant: it satisfies the mutant (every
transition fires, and every place ends empty with nothing deposited) but not IO-004 (`io004_t`
fires while place `0` holds 2 tokens). -/
@[evidence mutant IO_004]
theorem IO_004_mutant_dropMinimum_killed :
    IO_004_mutant_dropMinimum io004_drainEverythingFire ∧ ¬ IO_004 io004_drainEverythingFire := by
  refine ⟨fun t p n _ => ⟨fun m _ => ?_, fun d m m' hf => ?_, fun _ d m m' hf => ?_⟩, fun h => ?_⟩
  · exact ⟨fun _ => ⟨_, [], rfl, rfl⟩, fun _ => ⟨_, [], rfl, rfl⟩⟩
  · obtain ⟨rfl, rfl⟩ := hf
    rfl
  · obtain ⟨rfl, rfl⟩ := hf
    rfl
  · exact (h io004_t 0 3 ⟨_, rfl, rfl⟩).1 io004_two _ ⟨[], rfl, rfl⟩ (by decide)

/-- Mutant reading of IO-004 that drops the second line: the arc may block its transition even
when the minimum is there. -/
def IO_004_mutant_dropEnables {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t p n, InputArc t p (.atLeast n) →
    (while (fun m => TokenCount m p < n), never Fire F t) ∧
    (∀ d, on (fun m m' => F t m d m'), shall (fun _ m' => TokenCount m' p = Deposits d p)) ∧
    (¬ OutputArc t p →
      ∀ d, on (fun m m' => F t m d m'), shall (fun _ m' => TokenCount m' p = 0))

/-- A firing relation in which only a transition with no input arcs fires, changing nothing. -/
def io004_inputFreeFire : FireRel Nat := fun t m d m' => t.core.inputs = [] ∧ d = [] ∧ m' = m

/-- The input-free firing kills the second mutant: it satisfies the mutant (a transition with an
`AtLeast` arc never fires) but not IO-004 (`io004_t` does not fire from 7 tokens, although it
fires there without its input arc). -/
@[evidence mutant IO_004]
theorem IO_004_mutant_dropEnables_killed :
    IO_004_mutant_dropEnables io004_inputFreeFire ∧ ¬ IO_004 io004_inputFreeFire := by
  refine ⟨fun t p n h => ?_, fun h => ?_⟩
  · obtain ⟨s, hs, -⟩ := inputArc_mem h
    have hne : t.core.inputs ≠ [] := List.ne_nil_of_mem hs
    exact ⟨fun _ _ ⟨_, hf, _⟩ _ => hne hf, fun _ _ _ hf => absurd hf.1 hne,
      fun _ _ _ _ hf => absurd hf.1 hne⟩
  · obtain ⟨_, _, hne, _⟩ := ((h io004_t 0 3 ⟨_, rfl, rfl⟩).2.1 io004_seven (by decide)).2
      ⟨io004_seven, [], rfl, rfl, rfl⟩
    exact absurd hne (by decide)

/-- Mutant reading of IO-004 that drops the third line: on an output place the arc may consume
fewer than every token. -/
def IO_004_mutant_dropDrain {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t p n, InputArc t p (.atLeast n) →
    (while (fun m => TokenCount m p < n), never Fire F t) ∧
    (∀ m, n ≤ TokenCount m p →
      ((∃ m', Fire F t m m') ↔ ∃ m', Fire F (withoutInputArc t p) m m')) ∧
    (¬ OutputArc t p →
      ∀ d, on (fun m m' => F t m d m'), shall (fun _ m' => TokenCount m' p = 0))

/-- Whether the output spec of `t` names `q`: `OutputArc` as a `Bool`. -/
def io004_isOut (t : Trans Nat) (q : Nat) : Bool :=
  match t.out with
  | some o => decide (q ∈ outPlaces o)
  | none => false

/-- `io004_isOut` decides `OutputArc`. -/
theorem io004_isOut_iff (t : Trans Nat) (q : Nat) : io004_isOut t q = true ↔ OutputArc t q := by
  obtain ⟨c, o, r⟩ := t
  cases o <;> simp [io004_isOut, OutputArc]

/-- A firing relation that drains only the input places its output spec does not name: an
enabled transition fires, deposits nothing, empties each of those input places and leaves every
other place, its input places that are also output places included, as it is. -/
def io004_keepOutputFire : FireRel Nat :=
  fun t m d m' => Enabled t m ∧ d = [] ∧
    m' = fun q => if q ∈ t.core.inputs.map NInSpec.place ∧ io004_isOut t q = false then 0 else m q

/-- The second transition of the examples: `io004_t` with the output spec `Place(0)`, so its
`AtLeast` input place is also an output place. -/
def io004_t2 : Trans Nat :=
  { core := { name := "t2", inputs := [⟨0, .atLeast 3⟩], inhibitors := [], reads := [],
              resets := [] },
    out := some (.place 0) }

/-- The keep-output firing kills the third mutant: it satisfies the mutant (it fires exactly
when the reference enablement says so, and empties an `AtLeast` place that is not an output
place) but not IO-004 (`io004_t2` fires from 7 tokens, deposits nothing and leaves all 7 in
place `0`, its output place). -/
@[evidence mutant IO_004]
theorem IO_004_mutant_dropDrain_killed :
    IO_004_mutant_dropDrain io004_keepOutputFire ∧ ¬ IO_004 io004_keepOutputFire := by
  refine ⟨fun t p n h => ⟨?_, fun m hm => ?_, fun ho d m m' hf => ?_⟩, fun h => ?_⟩
  · rintro m m' ⟨d, hen, -, -⟩ hlt
    obtain ⟨s, hs, hsp, hsc⟩ := inputArc_mem h
    have := ((enabled_iff t m).1 hen).1 s hs
    simp [hsp, hsc, requiredCount, Card.required, TokenCount] at this hlt
    omega
  · have he := enabledNA_withoutInputArc t p n m h hm
    constructor
    · rintro ⟨m', d, hen, -, -⟩
      exact ⟨_, [], (show enabledNA m _ = true from he.trans hen), rfl, rfl⟩
    · rintro ⟨m', d, hen, -, -⟩
      exact ⟨_, [], (show enabledNA m _ = true from he.symm.trans hen), rfl, rfl⟩
  · obtain ⟨-, -, rfl⟩ := hf
    obtain ⟨s, hs, hsp, -⟩ := inputArc_mem h
    have hin : p ∈ t.core.inputs.map NInSpec.place := List.mem_map.2 ⟨s, hs, hsp⟩
    have hno : io004_isOut t p = false := by
      cases hb : io004_isOut t p
      · rfl
      · exact absurd ((io004_isOut_iff t p).1 hb) ho
    show (if p ∈ t.core.inputs.map NInSpec.place ∧ io004_isOut t p = false then 0 else m p) = 0
    rw [if_pos ⟨hin, hno⟩]
  · have := (h io004_t2 0 3 ⟨_, rfl, rfl⟩).2.2.1 [] io004_seven _ ⟨by decide, rfl, rfl⟩
    simp [TokenCount, Deposits, depProd, io004_seven, io004_isOut, io004_t2, outPlaces] at this

/-- Mutant reading of IO-004 that drops the fourth line: a firing may report a deposit in an
input place its output spec does not name, and keep that many tokens there. -/
def IO_004_mutant_dropEmpty {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t p n, InputArc t p (.atLeast n) →
    (while (fun m => TokenCount m p < n), never Fire F t) ∧
    (∀ m, n ≤ TokenCount m p →
      ((∃ m', Fire F t m m') ↔ ∃ m', Fire F (withoutInputArc t p) m m')) ∧
    (∀ d, on (fun m m' => F t m d m'), shall (fun _ m' => TokenCount m' p = Deposits d p))

/-- The ghost-deposit firing kills the fourth mutant: it satisfies the mutant (it fires exactly
when the reference enablement says so, and every place ends with what the firing reports as
deposited there) but not IO-004 (`IO_004_forbids_ghost`). -/
@[evidence mutant IO_004]
theorem IO_004_mutant_dropEmpty_killed :
    IO_004_mutant_dropEmpty io004_ghostFire ∧ ¬ IO_004 io004_ghostFire := by
  refine ⟨fun t p n h => ⟨?_, fun m hm => ?_, fun d m m' hf => ?_⟩, IO_004_forbids_ghost⟩
  · rintro m m' ⟨d, hen, -, -⟩ hlt
    obtain ⟨s, hs, hsp, hsc⟩ := inputArc_mem h
    have := ((enabled_iff t m).1 hen).1 s hs
    simp [hsp, hsc, requiredCount, Card.required, TokenCount] at this hlt
    omega
  · have he := enabledNA_withoutInputArc t p n m h hm
    constructor
    · rintro ⟨m', d, hen, -, -⟩
      exact ⟨_, _, (show enabledNA m _ = true from he.trans hen), rfl, rfl⟩
    · rintro ⟨m', d, hen, -, -⟩
      exact ⟨_, _, (show enabledNA m _ = true from he.symm.trans hen), rfl, rfl⟩
  · obtain ⟨-, -, rfl⟩ := hf
    rfl

/-- The marking `io004_t2` leaves from `io004_seven`: place `0` drained and given back the one
token the output spec deposits there, the others untouched. -/
def io004_refilled : Nat → Nat := fun q => if q = 0 then 1 else 7

/-- All four lines of IO-004 are exercised by the reference semantics: `io004_t` has the input
arc `AtLeast(0, 3)`; it does not fire from 2 tokens in place `0` (first line); it fires from 7
tokens, as it does there without its input arc (second line); that firing drains all 7, not
just the minimum 3, and place `0`, which is not an output place, ends empty (third and fourth
lines); and `io004_t2`, whose `AtLeast` place `0` is also its output place, fires from 7 tokens
and leaves exactly the 1 token it deposits there (third line, with the fourth not applying). -/
@[evidence nonvacuous IO_004]
theorem IO_004_nonvacuous :
    InputArc io004_t 0 (.atLeast 3) ∧
      ¬ (∃ m', Fire RefFire io004_t io004_two m') ∧
      Fire RefFire io004_t io004_seven io004_drained ∧
      Fire RefFire (withoutInputArc io004_t 0) io004_seven io004_seven ∧
      ¬ OutputArc io004_t 0 ∧ io004_drained 0 = 0 ∧
      InputArc io004_t2 0 (.atLeast 3) ∧ OutputArc io004_t2 0 ∧
      RefFire io004_t2 io004_seven [0] io004_refilled ∧ io004_refilled 0 = Deposits [0] 0 := by
  refine ⟨⟨_, rfl, rfl⟩, ?_, ⟨[], by decide, ⟨.action 0, rfl⟩, ?_⟩,
    ⟨[], by decide, ⟨.action 0, rfl⟩, ?_⟩, io004_t_noOut 0, rfl, ⟨_, rfl, rfl⟩,
    ⟨_, rfl, by simp [outPlaces]⟩, ⟨by decide, ⟨.action 0, rfl⟩, ?_⟩, by decide⟩
  · rintro ⟨m', d, hen, -⟩
    exact absurd hen (by decide)
  · funext q; by_cases hq : q = 0 <;>
      simp [hq, eq_comm (a := 0), fireNC, depProd, nconsumed, nspecAt, io004_t, io004_seven,
        io004_drained, Card.consumesAll]
  · funext q
    simp [fireNC, depProd, nconsumed, nspecAt, withoutInputArc, io004_t, io004_seven]
  · funext q; by_cases hq : q = 0 <;>
      simp [hq, eq_comm (a := 0), fireNC, depProd, nconsumed, nspecAt, io004_t2, io004_seven,
        io004_refilled, Card.consumesAll]

end Libpetri.Spec
