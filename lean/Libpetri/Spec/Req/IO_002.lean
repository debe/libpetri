import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.Glossary

set_option linter.missingDocs true

/-!
# IO-002: Input Exactly (`spec/02-input-output-specs.md`)

The requirement is a predicate over an abstract firing relation `F : FireRel N`. The evidence
theorems check it against the reference semantics (`Reference.Fires`, as `RefFire`), against
concrete firing relations that read `Exactly(n)` as `One` or as `AtLeast(n)` or that report a
deposit they do not make, and against one mutant reading per clause and part.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## IO-002: Input Exactly -/

requirement IO_002
  id "IO-002"
  title "Input Exactly"
  kind B
  scope "all executors"
  source verbatim "spec/02-input-output-specs.md"
  quote "`Exactly(place, n)` is an input arc whose required count and consumption count are both N, where N >= 1."
        "*While* the input place of an `Exactly(n)` input arc holds fewer than N tokens, the transition *shall not* fire."
        "*When* a transition with an `Exactly(n)` input arc fires, it *shall* consume exactly N tokens from the input place."
        "*When* a transition with an `Exactly(n)` input arc fires, and the input place is neither a reset place nor an output place of the transition, the input place *shall* end the firing holding exactly N fewer tokens than it held before the firing."
  reading "For every transition t, place p and count N such that the input arc of t on p is Exactly(N):"
          "t does not fire from a marking in which p holds fewer than N tokens;"
          "unless p is also a reset place of t, every firing of t from m that deposits d and leaves m' has m'(p) + N = m(p) + d(p): p loses exactly N tokens, besides what the firing deposits there; and if p is not an output place of t either, m'(p) + N = m(p): p loses exactly N tokens, whatever deposit the firing reports."
  assumes "A firing is read as one step from a marking to a marking with its deposit (glossary: Fire); timing and priority play no part. 'Enables' is read as 'some firing exists'."
          "The first quoted sentence (required count N, consumption count N; the bullets `requiredCount()` returns N and `consumptionCount(available)` returns N) is IO-007's contract for `Exactly(n)`. Here it is observed through firing: the required count is the second line, the consumption count the third. The bullets' qualifier 'when available >= N' is implied: by the second line no firing starts with fewer."
          "AC1 (construction with N < 1 rejected, also when the transition is built from a spec written out without the constructor) is a property of construction, not of firing, so this formula does not encode it: its build half is the block IO_002_build in this file (every transition with an Exactly(0) input arc fails to build), and its constructor half is Q-tested there. The formula here quantifies over every N, N = 0 included; for N = 0 both lines hold of the reference semantics trivially, so the restriction N >= 1 neither weakens nor strengthens what is checked about firing."
          "AC2 (enables only when the place has >= N tokens) and AC4 (N-1 tokens, not enabled) are the second line. The converse ('enables when the place has >= N tokens', given the other arcs allow it) is the AND-join of IO-005 and CORE-022, not this block's subject."
          "AC3 (exactly N consumed on firing, the N oldest, FIFO) is the third line for the count; its second part (the fourth quoted sentence) states it without the deposit for an input place that is neither a reset place nor an output place. Which tokens are consumed (the oldest, FIFO) is below the count granularity of the firing semantics and is the glossary's reading of Consume (CORE-030); it is not encoded here."
          "Consumption is observed through the marking: p loses N and gains what the firing deposits there (p may also be an output place). A place that is both the input place and a reset place of t ends holding what the firing deposited there (CORE-034), so the N tokens consumed are not visible in the marking; the third line excludes that case, as the fourth quoted sentence does."
          "The deposit a firing reports is not trusted for the count: on a place that t's output spec does not name (glossary: Output arc) no firing of t can deposit ([CORE-035]), so there the consumed tokens show in the marking alone, as exactly N tokens fewer (the fourth quoted sentence, IO-001's guard). Without this a firing that consumes nothing but reports a deposit of N in the input place would pass the count, and the block would lean on CORE-035 to stand."
          "Deposits are counts per place (glossary: Deposit, [CORE-036]): `Deposits d p` counts the tokens d puts in p and ignores their order. The build-time output-spec checks of IO-011 to IO-014 (ambiguity, one Timeout, ForwardInput only under a Timeout) and the validation skip of CONC-026 do not touch input consumption, so the formula quantifies over every transition, built or not, and every executor."
          "The input arc of t on p is the first input arc on p (glossary: Input arc); CORE-030 rejects a second one at build."
  signoff "2026-11-13 96c1d96e85a20f1e ai"
  statement : ∀ {N : Type} [DecidableEq N], FireRel N → Prop :=
    fun F => ∀ t p n, InputArc t p (.exactly n) →
      (while (fun m => TokenCount m p < n), never Fire F t) ∧
      (¬ ResetArc t p → ∀ m d m', F t m d m' →
        m' p + n = m p + Deposits d p ∧ (¬ OutputArc t p → m' p + n = m p))

/- The pinned readable form of IO-002: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.IO_002 : {N : Type} → [DecidableEq N] → FireRel N → Prop :=
fun {N} [DecidableEq N] F =>
  ∀ (t : Reference.Trans N) (p : N) (n : ℕ),
    InputArc t p (Card.exactly n) →
      (while fun m => TokenCount m p < n, never Fire F t) ∧
        (¬ResetArc t p →
          ∀ (m : N → ℕ) (d : List N) (m' : N → ℕ),
            F t m d m' → m' p + n = m p + Deposits d p ∧ (¬OutputArc t p → m' p + n = m p))
-/
#guard_msgs in #print IO_002

/-- An `Exactly(n)` input arc on `p` and the input arc on `p` that enablement reads are the
same: an enabled transition finds at least `n` tokens in `p`. -/
theorem io002_le_of_enabled {N : Type} [DecidableEq N] {t : Trans N} {p : N} {n : Nat}
    {m : CountMarking N} (ha : InputArc t p (.exactly n)) (hen : Enabled t m) : n ≤ m p := by
  obtain ⟨s, hs, hc⟩ := ha
  have hmem : s ∈ t.core.inputs := List.mem_of_find?_eq_some hs
  have hp : s.place = p := by simpa using List.find?_some hs
  have := ((enabled_iff t m).1 hen).1 s hmem
  simpa [requiredCount, hc, Card.required, hp] using this

/-- An `Exactly(n)` input arc on `p` consumes `n` tokens from `p`. -/
theorem io002_consumes {N : Type} [DecidableEq N] {t : Trans N} {p : N} {n : Nat}
    (m : CountMarking N) (ha : InputArc t p (.exactly n)) : Consumes t m p = n := by
  obtain ⟨s, hs, hc⟩ := ha
  simp [Consumes, nconsumed, hs, hc, Card.consumesAll, Card.required]

/-- The reference semantics satisfies IO-002: `Seam.enabledNA` requires the input place of an
`Exactly(n)` arc to hold `Card.required (.exactly n) = n` tokens, and `Seam.nconsumed` takes
`n` from it, so a place that is not a reset place loses `n` and gains the deposit, which is empty
outside the output spec's places. -/
@[evidence holds IO_002]
theorem IO_002_reference {N : Type} [DecidableEq N] : IO_002 (RefFire (N := N)) := by
  intro t p n ha
  refine ⟨?_, fun hr m d m' h => ?_⟩
  · rintro m m' ⟨d, hen, -, -⟩ hlt
    have := io002_le_of_enabled ha hen
    simp only [TokenCount] at hlt
    omega
  · have hle := io002_le_of_enabled ha h.1
    have happ := refFire_apply h p
    rw [if_neg hr, io002_consumes m ha] at happ
    refine ⟨by omega, fun ho => ?_⟩
    have h0 : Deposits d p = 0 :=
      List.count_eq_zero_of_not_mem (fun hp => ho (refFire_outputs h p hp))
    omega

/-! ### Examples over a one-place net (the test derivation: `Exactly(5)`, 7 and 4 tokens) -/

/-- The one transition of the examples: one input arc `Exactly(5)` on place `0`, no other arcs,
no output spec. -/
def io002_t : Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .exactly 5⟩], inhibitors := [], reads := [],
              resets := [] },
    out := none }

/-- The input arc of `io002_t` on place `0` is `Exactly(5)`. -/
theorem io002_t_arc : InputArc io002_t 0 (.exactly 5) := ⟨_, rfl, rfl⟩

/-- Place `0` is not a reset place of `io002_t`. -/
theorem io002_t_noReset : ¬ ResetArc io002_t 0 := by decide

/-- `io002_t` has no output place. -/
theorem io002_t_noOut (p : Nat) : ¬ OutputArc io002_t p := by
  rintro ⟨o, h, -⟩; simp [io002_t] at h

/-- A second transition: the input arc `Exactly(5)` on place `0` and an output spec that puts a
token back in place `0`, so place `0` is also an output place. -/
def io002_t2 : Trans Nat :=
  { core := { name := "t2", inputs := [⟨0, .exactly 5⟩], inhibitors := [], reads := [],
              resets := [] },
    out := some (.place 0) }

/-- The input arc of `io002_t2` on place `0` is `Exactly(5)`. -/
theorem io002_t2_arc : InputArc io002_t2 0 (.exactly 5) := ⟨_, rfl, rfl⟩

/-- The marking of the examples in which every place holds 7 tokens. -/
def io002_m7 : CountMarking Nat := fun _ => 7

/-- The marking of the examples in which every place holds 4 tokens (one fewer than 5). -/
def io002_m4 : CountMarking Nat := fun _ => 4

/-- `t` with every `Exactly` input arc rewritten by `f`, and nothing else changed. -/
def io002_recard {N : Type} (f : Nat → Card) (t : Trans N) : Trans N :=
  { t with core := { t.core with inputs := t.core.inputs.map fun s =>
      { s with card := match s.card with | .exactly n => f n | c => c } } }

/-- A firing relation that reads `Exactly(n)` as `One`: a reference firing of the transition
with every `Exactly` input arc replaced by `One`. -/
def io002_asOneFire : FireRel Nat := fun t => RefFire (io002_recard (fun _ => .one) t)

/-- ✗ Reading `Exactly(n)` as `One` violates IO-002 (first clause): `io002_t` fires from the
marking in which place `0` holds 4 tokens, fewer than 5. -/
@[evidence forbids IO_002]
theorem IO_002_forbids_asOne : ¬ IO_002 io002_asOneFire := by
  intro h
  exact (h io002_t 0 5 io002_t_arc).1 io002_m4 _ ⟨[], by decide, ⟨.action 0, rfl⟩, rfl⟩
    (by decide)

/-- A firing relation that reads `Exactly(n)` as `AtLeast(n)`: a reference firing of the
transition with every `Exactly(n)` input arc replaced by `AtLeast(n)`, which drains the place. -/
def io002_asAtLeastFire : FireRel Nat := fun t => RefFire (io002_recard .atLeast t)

/-- ✗ Reading `Exactly(n)` as `AtLeast(n)` violates IO-002 (second clause): `io002_t` fires
from 7 tokens and leaves place `0` empty, consuming 7, not 5. -/
@[evidence forbids IO_002]
theorem IO_002_forbids_asAtLeast : ¬ IO_002 io002_asAtLeastFire := by
  intro h
  have := ((h io002_t 0 5 io002_t_arc).2 io002_t_noReset io002_m7 [] _
    ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩).1
  exact absurd this (by decide)

/-- A ghost-deposit firing relation: `io002_t` fires when enabled, consumes nothing, leaves the
marking as it is and reports a deposit of 5 tokens in its input place `0`, although its output
spec names no place. -/
def io002_ghostFire : FireRel Nat := fun t m d m' =>
  t = io002_t ∧ Enabled t m ∧ d = List.replicate 5 0 ∧ m' = m

/-- ✗ A firing that consumes nothing but reports a deposit in its input place violates IO-002
(second clause, its second part): `io002_t` has no output place, fires from 7 tokens and leaves
all 7 in place `0`. -/
@[evidence forbids IO_002]
theorem IO_002_forbids_ghost : ¬ IO_002 io002_ghostFire := by
  intro h
  have := ((h io002_t 0 5 io002_t_arc).2 io002_t_noReset io002_m7 _ io002_m7
    ⟨rfl, by decide, rfl, rfl⟩).2 (io002_t_noOut 0)
  exact absurd this (by decide)

/-- Mutant reading of IO-002 that drops the first clause: an `Exactly(n)` arc consumes `n`
tokens, but nothing stops its transition from firing with fewer. -/
def IO_002_mutant_dropEnable {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t p n, InputArc t p (.exactly n) →
    ¬ ResetArc t p → ∀ m d m', F t m d m' →
      m' p + n = m p + Deposits d p ∧ (¬ OutputArc t p → m' p + n = m p)

/-- A firing relation in which only `io002_t2` fires, from every marking: it takes 5 tokens
from place `0` and deposits 5 back there (place `0` is one of its output places), leaving the
marking as it is. -/
def io002_returnsFire : FireRel Nat := fun t m d m' =>
  t = io002_t2 ∧ d = List.replicate 5 0 ∧ m' = m

/-- The returning firing kills the first mutant: it satisfies the mutant (place `0` loses 5 and
gains the 5 it deposits, and is an output place of `io002_t2`) but not IO-002 (`io002_t2` fires
from 4 tokens). Without the first clause a place that is also an output place may be short. -/
@[evidence mutant IO_002]
theorem IO_002_mutant_dropEnable_killed :
    IO_002_mutant_dropEnable io002_returnsFire ∧ ¬ IO_002 io002_returnsFire := by
  refine ⟨?_, fun h => ?_⟩
  · rintro t p n ⟨s, hs, hc⟩ - m d m' ⟨rfl, rfl, rfl⟩
    by_cases hp : p = 0
    · subst hp
      simp [io002_t2, nspecAt] at hs
      subst hs
      cases hc
      refine ⟨by simp [Deposits, depProd], fun ho => absurd ⟨_, rfl, by simp [outPlaces]⟩ ho⟩
    · simp [io002_t2, nspecAt, Ne.symm hp] at hs
  · exact (h io002_t2 0 5 io002_t2_arc).1 io002_m4 io002_m4 ⟨_, rfl, rfl, rfl⟩ (by decide)

/-- Mutant reading of IO-002 that drops the second clause: an `Exactly(n)` arc needs `n`
tokens, but a firing may consume any number of them. -/
def IO_002_mutant_dropConsume {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t p n, InputArc t p (.exactly n) → (while (fun m => TokenCount m p < n), never Fire F t)

/-- The firing that consumes nothing: an enabled transition may fire, depositing nothing and
leaving the marking as it is. -/
def io002_idleFire : FireRel Nat := fun t m d m' => Enabled t m ∧ d = [] ∧ m' = m

/-- The idle firing kills the second mutant: it satisfies the mutant (only enabled transitions
fire, so an `Exactly(n)` place holds at least `n`) but not IO-002 (`io002_t` fires from 7
tokens and place `0` keeps all 7). -/
@[evidence mutant IO_002]
theorem IO_002_mutant_dropConsume_killed :
    IO_002_mutant_dropConsume io002_idleFire ∧ ¬ IO_002 io002_idleFire := by
  refine ⟨?_, fun h => ?_⟩
  · rintro t p n ha m m' ⟨d, hen, -, -⟩ hlt
    have := io002_le_of_enabled ha hen
    simp only [TokenCount] at hlt
    omega
  · have := ((h io002_t 0 5 io002_t_arc).2 io002_t_noReset io002_m7 [] io002_m7
      ⟨by decide, rfl, rfl⟩).1
    exact absurd this (by decide)

/-- Mutant reading of IO-002 that drops the second part of the second clause (the fourth quoted
sentence): the count trusts the deposit the firing reports, also in a place outside the output
spec. -/
def IO_002_mutant_trustDeposit {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t p n, InputArc t p (.exactly n) →
    (while (fun m => TokenCount m p < n), never Fire F t) ∧
    (¬ ResetArc t p → ∀ m d m', F t m d m' → m' p + n = m p + Deposits d p)

/-- The ghost-deposit firing kills the third mutant: it fires only when enabled, so the first
clause holds, and the 5 tokens it reports in place `0` make up for the 5 it does not take; but
`io002_t` has no output place, and place `0` keeps its tokens. -/
@[evidence mutant IO_002]
theorem IO_002_mutant_trustDeposit_killed :
    IO_002_mutant_trustDeposit io002_ghostFire ∧ ¬ IO_002 io002_ghostFire := by
  refine ⟨fun t p n ha => ⟨?_, fun _ m d m' ⟨ht, _, hd, hm'⟩ => ?_⟩, IO_002_forbids_ghost⟩
  · rintro m m' ⟨d, -, hen, -⟩ hlt
    have := io002_le_of_enabled ha hen
    simp only [TokenCount] at hlt
    omega
  · subst ht hd hm'
    obtain ⟨s, hs, hc⟩ := ha
    by_cases hp : p = 0
    · subst hp
      simp [io002_t, nspecAt] at hs
      subst hs
      cases hc
      simp [Deposits, depProd]
    · simp [io002_t, nspecAt, Ne.symm hp] at hs

/-- Both clauses of IO-002 are exercised by the reference semantics, as in the test derivation:
`io002_t` has the input arc `Exactly(5)` on place `0`; it does not fire from 4 tokens (first
clause); and it fires from 7 tokens, leaving 2, with place `0` not an output place (second
clause, both parts). -/
@[evidence nonvacuous IO_002]
theorem IO_002_nonvacuous :
    InputArc io002_t 0 (.exactly 5) ∧ ¬ ResetArc io002_t 0 ∧ ¬ OutputArc io002_t 0 ∧
      (∀ m', ¬ Fire RefFire io002_t io002_m4 m') ∧
      Fire RefFire io002_t io002_m7 (fun q => if q = 0 then 2 else 7) := by
  refine ⟨io002_t_arc, io002_t_noReset, io002_t_noOut 0, ?_, ⟨[], by decide, ⟨.action 0, rfl⟩, ?_⟩⟩
  · rintro m' ⟨d, hen, -⟩
    exact absurd hen (by decide)
  · funext q
    by_cases hq : q = 0
    · subst hq; rfl
    · simp [fireNC, nconsumed, nspecAt, depProd, io002_t, io002_m7, hq, Ne.symm hq]

/-! ## IO-002, AC1: the count check at build -/

requirement IO_002_build
  id "IO-002"
  title "Input Exactly"
  kind F
  scope "all transition builders"
  source verbatim "spec/02-input-output-specs.md"
  quote "Construction with N < 1 is rejected (error or panic). Where the language lets the spec be written out without the constructor (a public enum variant, an object literal), building the transition rejects it."
  reading "For the transition builder Build (Build t = none: t builds; Build t = some msg: building t fails with msg):"
          "every transition t one of whose input arcs is Exactly(0) fails to build."
  assumes "Build is the transition builder read as the message it rejects a transition with (none: the transition builds), as in IO-011, IO-013 and EXEC-012; the witness is the reference builder refBuild (glossary: Build-time checks), whose count check (InputCountsPositive, stand-in message msgCount) rejects an input arc that requires fewer than one token. The cardinality of the model (Card) is a value written out directly, so a transition carrying Exactly(0) is the spec written out without the constructor: the second quoted sentence. N ranges over the naturals, so N < 1 is N = 0."
          "The first quoted sentence (the constructor rejects N < 1 with an error or a panic) is not encoded: the model has no constructor, only the value. It is Q-tested: Rust exactly() asserts count >= 1 (rust/libpetri-core/src/input.rs, test exactly_zero_panics), TypeScript exactly() throws (typescript/src/core/in.ts, test 'rejects count < 1' in typescript/tests/core/in.test.ts), Java's Exactly record constructor throws IllegalArgumentException (java/src/main/java/org/libpetri/core/Arc.java), which is also the only way to write the value in Java. Python reaches the Rust constructor."
          "The second quoted sentence is the line. The runtimes whose spec can be written out without the constructor check it when the transition is built: Rust for the public In::Exactly variant (the input-count check in TransitionBuilder::build in rust/libpetri-core/src/transition.rs, tests an_exactly_zero_input_panics and an_at_least_zero_input_panics), TypeScript for an object literal (the input-count check in TransitionBuilder.build in typescript/src/core/transition.ts, test 'build rejects an input that requires no token' in typescript/tests/core/transition.test.ts). A builder without the count check (io002_buildNoCount) builds such a transition and is forbidden (IO_002_build_forbids_noCount)."
          "Only the failure is stated, not its message: the spec gives the check no message, and the reference fails it with the stand-in msgCount. That a transition whose input arcs all require at least one token, and which passes the other build-time checks, does build is CORE-020's line 4 (Builds includes InputCountsPositive), so a builder that rejects every transition meets this line and breaks that one. The order of the count check against CORE-030's input-arc check is not stated (the reference runs CORE-030's first); EXEC-012's line 5 orders its own check after both."
  signoff "2026-11-13 f8246e01110b0659 ai"
  statement : ∀ {N : Type} [DecidableEq N] [ToString N], (Trans N → Option String) → Prop :=
    fun Build => ∀ t : Trans _, ∀ s ∈ t.core.inputs, s.card = .exactly 0 → Build t ≠ none

/- The pinned readable form of the build block: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.IO_002_build : {N : Type} →
  [DecidableEq N] → [ToString N] → (Reference.Trans N → Option String) → Prop :=
fun {N} [DecidableEq N] [ToString N] Build =>
  ∀ (t : Reference.Trans N), ∀ s ∈ t.core.inputs, s.card = Card.exactly 0 → Build t ≠ none
-/
#guard_msgs in #print IO_002_build

/-- ✓ The reference builder satisfies the build block: a transition with an `Exactly(0)` input
arc fails `InputCountsPositive`, so it does not pass `Builds`, and `refBuild` rejects exactly
the transitions that do not (`refBuild_eq_none_iff`). -/
@[evidence holds IO_002_build]
theorem IO_002_build_reference {N : Type} [DecidableEq N] [ToString N] :
    IO_002_build (refBuild (N := N)) := by
  intro t s hs hc h
  have hpos := ((refBuild_eq_none_iff t).1 h).1.2.1 s hs
  simp [requiredCount, hc, Card.required] at hpos

/-- **The reference builder without the count check**: [CORE-030]'s input-arc check, the
[EXEC-012] input-and-read check, then the output-spec checks, as `refBuild` without its
`InputCountsPositive` branch. -/
def io002_buildNoCount {N : Type} [DecidableEq N] [ToString N] (t : Trans N) : Option String :=
  if ¬ InputsDistinct t then some "CORE-030"
  else match firstInputRead t with
    | some p => some (msgInputRead t p)
    | none =>
      match t.out with
      | none => none
      | some o => checkOut t (inPlaces t) o

/-- The transition of the build examples: one input arc `Exactly(0)` on place `0`, written out
without the constructor, no other arcs, no output spec. -/
def io002_t0 : Trans Nat :=
  { core := { name := "t0", inputs := [⟨0, .exactly 0⟩], inhibitors := [], reads := [],
              resets := [] },
    out := none }

/-- ✗ A builder without the count check violates the build block: it builds `io002_t0`, whose
input arc is `Exactly(0)`. -/
@[evidence forbids IO_002_build]
theorem IO_002_build_forbids_noCount : ¬ IO_002_build (io002_buildNoCount (N := Nat)) := by
  intro h
  exact h io002_t0 ⟨0, .exactly 0⟩ (by simp [io002_t0]) rfl (by decide)

/-- The build block is exercised by the reference builder: `io002_t0` has an `Exactly(0)` input
arc, and building it fails with the count check's stand-in message. -/
@[evidence nonvacuous IO_002_build]
theorem IO_002_build_nonvacuous :
    (∃ s ∈ io002_t0.core.inputs, s.card = .exactly 0) ∧ refBuild io002_t0 = some msgCount :=
  ⟨⟨⟨0, .exactly 0⟩, by simp [io002_t0], rfl⟩, by decide⟩

end Libpetri.Spec
