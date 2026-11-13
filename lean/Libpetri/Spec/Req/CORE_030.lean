import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.Glossary
import Libpetri.Spec.Text.CORE_030

set_option linter.missingDocs true

/-!
# CORE-030: Input arc (`spec/01-core-model.md`)

The requirement is a predicate over an abstract firing relation `F : FireRel N`. The evidence
theorems check it against the reference semantics (`Reference.Fires`, as `RefFire`), against two
concrete firing relations that each break one line of the reading, and against three mutant
readings of the text.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-- **Input places distinct.** A transition declares at most one input arc per place ([CORE-030];
glossary: Input arc, "A transition declares at most one input arc per place"): the places of its
input arcs, in declaration order, have no repetition. Place identity is equality on `N`
([CORE-002]). A transition that breaks this never reaches a firing: building it fails. -/
abbrev InputPlacesDistinct {N : Type} (t : Trans N) : Prop :=
  (t.core.inputs.map NInSpec.place).Nodup

/-! ## CORE-030: Input arc -/

requirement CORE_030
  id "CORE-030"
  title "Input arc"
  kind B
  scope "all executors"
  source verbatim "spec/01-core-model.md"
  covers CORE_030.s1, CORE_030.s2
  reading "For every transition t that declares at most one input arc per place, every input place p of t whose input arc has cardinality c, p not a reset place of t, and every deposit d, every firing of t from m to m' depositing d, from a marking in which p holds at least the arc's required count:"
          "leaves m'(p) + consumptionCount(c, m(p)) = m(p) + (the tokens d deposits in p): the firing removes exactly the consumption count from p, besides what it deposits there;"
          "and, if p is not an output place of t either, leaves m'(p) + consumptionCount(c, m(p)) = m(p): p ends holding exactly the consumption count fewer tokens, whatever deposit the firing reports."
  assumes "A firing is read as one step from a marking to a marking with its deposit (glossary: Fire); timing and priority play no part. Markings are token counts (glossary: Marking)."
          "AC1 (a transition with an input arc consumes tokens from the place on firing) is the second line, with the amount the consumption count of the arc's cardinality; the third line is the second quoted sentence."
          "AC2 (consumed tokens follow FIFO order) and 'oldest first' are below the token-count granularity of this firing relation, so no line here states them. They are stated on the queue firing relation by CORE-013's line 2 (the action receives OldestFirst M p k, the first k tokens of p, and a place that is not a reset place keeps List.drop k of its queue, followed by its emissions), which with this block's count gives the oldest consumption-count tokens; CORE_013's assumes cite CORE-030 for it."
          "Inside a firing pass, the marking a transition fires from in the sense of these lines is the pass-visible marking, not the live one (EXEC-003 AC4 and AC5, ruling D75 (a)): m(p) is the pass-visible count of p, so the consumption count of an all() or atLeast(n) arc is taken on it and the tokens removed are the oldest of its pass-visible prefix, while a token a synchronous action deposited into p earlier in the same pass survives the firing and becomes visible at the next pass. EXEC-003's line 2 states this over the executor (a start leaves the pass-visible queue with the consumption and drains applied, followed by the tail deposited inside the pass; EXEC_003_forbids_drainSwallows kills a start that drains the live queue). Rust counts the draining forms on drainable, the live count less the same-pass deposits (deposit_delta; drainable, called from consume_for_firing, in rust/libpetri-runtime/src/bitmap_backend.rs, and drainable in precompiled_backend.rs), and Java drains all() and atLeast(n) to drainable in the same way (BitmapNetExecutor.drainable, called from fireTransition, in java/src/main/java/org/libpetri/runtime/BitmapNetExecutor.java, and PrecompiledNetExecutor.drainable in PrecompiledNetExecutor.java); TypeScript settles every firing in step 1, so its passes have no same-pass deposit. The bridge from a reference start to this one-step firing relation is recorded with the integrator, as for CORE-022 and CORE-031."
          "AC3 and the sentence 'If a transition declares two input arcs on the same place, building the transition shall fail with a descriptive error that names the transition and the place and suggests a single arc with `exactly(n)` / `atLeast(n)` instead.' are the transition builder's, not the firing relation's. The failure half is CORE-020's line 4: a build call succeeds only on arcs that pass Builds (glossary: Builds), whose PreOutputChecks include InputsDistinct, so building a transition with two input arcs on one place fails, and CORE-022 scopes enablement to transitions that build. The message half (the error names the transition and the place and suggests one exactly(n) / atLeast(n) arc) is stated by no block: the reference builder refBuild fails with the stand-in message \"CORE-030\" (Spec/Glossary.lean), which names neither, so a line over Build needs that shared builder and the CORE and IO consistency theorem changed first; that is recorded with the integrator. Until then the message is Q-tested: the three runtimes share one text naming the transition and the first repeated place and suggesting the single arc (Rust duplicate_input_message, rust/libpetri-core/src/transition.rs, tests duplicate_input_places_rejected_at_build and exec012_names_first_offending_read_and_core030_reports_first; Java ArcDiagnostics.duplicateInputMessage, java/src/test/java/org/libpetri/core/TransitionTest.java builder_rejectsTwoInputArcsOnOnePlace; TypeScript duplicateInputArcMessage, typescript/src/core/transition.ts, typescript/tests/core/input-read-same-place.test.ts; Python surfaces Rust's text as StructureError, python/tests/test_backend_divergences.py). AC3's 'the executor compile step keeps the same check, and message, as a backstop' is Q-tested the same way: CompiledNet::compile (rust/libpetri-runtime/src/compiled_net.rs) and the CompiledNet constructors of java/src/main/java/org/libpetri/runtime/CompiledNet.java and typescript/src/runtime/compiled-net.ts call the same message function. The firing lines take the check as a hypothesis: they constrain only transitions whose input places are distinct (InputPlacesDistinct), the only ones AC3 lets any executor, state-class graph or verifier see. Firings of a transition with duplicate input arcs are left unconstrained here, as the spec says their consumption has no coherent semantics."
          "Transitions with a ν match specification (NU-020) are out of scope. The quoted sentence takes the consumption count from IO-007, and on a correlated input of a match specification that count and the oldest-first order apply to the tokens of the chosen name only (glossary: Consume; EXEC-010, NU-020), so an all() or atLeast(n) correlated input removes fewer than every token of the place. The transitions of the model (Reference.Trans) carry no match specification, so both lines are the count-level case of a transition without one (as CORE-022 reads it, rulings D16 and D30); the correlated take is NU-020's and EXEC-010's."
          "The build-time output-spec checks (IO-011 to IO-014) are not a hypothesis here: neither line depends on the output spec beyond which places it names, so both hold of every transition with distinct input places, whether or not its output spec builds."
          "A place that is both an input place and a reset place of t is excluded by both quoted sentences: CORE-034 says such a place ends the firing holding exactly what was deposited there, so it is CORE-034's to constrain (the third hypothesis, ¬ ResetArc t p)."
          "Interpretation: the consumption is read additively, m'(p) + consumed = m(p) + deposited, so a firing that also deposits into its own input place is counted correctly."
          "The deposit a firing reports is not trusted for the count on a place the output spec does not name (glossary: Output arc): no firing of t can deposit there ([CORE-035]), so the consumption shows in the marking alone, as the third line says. Without it a firing that consumes nothing but reports a deposit equal to the consumption count in its input place would pass the second line. This is the guard IO-001 to IO-004 also carry, so each of those blocks stands alone."
          "Interpretation: both lines are required only of firings from a marking in which p holds at least the arc's required count. A firing from a marking where p holds fewer is not enabled (CORE-022, IO-005); whether such a firing may happen at all is those requirements' business, and CORE-030, which speaks only of how much a firing consumes, says nothing about it."
          "'The same place' is equality of place names (TypeScript, Rust, [CORE-002]); Java's name-and-type equality is not modelled."
  signoff "2026-11-13 37a9147db6a0f409 ai"
  statement : ∀ {N : Type} [DecidableEq N], FireRel N → Prop :=
    fun F => ∀ t p c, InputPlacesDistinct t → InputArc t p c → ¬ ResetArc t p → ∀ d,
      (on (fun m m' => F t m d m'), shall
        (fun m m' => requiredCount c ≤ TokenCount m p →
          TokenCount m' p + consumptionCount c (TokenCount m p) = TokenCount m p + Deposits d p ∧
          (¬ OutputArc t p →
            TokenCount m' p + consumptionCount c (TokenCount m p) = TokenCount m p)))

/- The pinned readable form of CORE-030: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CORE_030 : {N : Type} → [DecidableEq N] → FireRel N → Prop :=
fun {N} [DecidableEq N] F =>
  ∀ (t : Reference.Trans N) (p : N) (c : Card),
    InputPlacesDistinct t →
      InputArc t p c →
        ¬ResetArc t p →
          ∀ (d : List N),
            on fun m m' => F t m d m', shall fun m m' =>
              requiredCount c ≤ TokenCount m p →
                TokenCount m' p + consumptionCount c (TokenCount m p) = TokenCount m p + Deposits d p ∧
                  (¬OutputArc t p → TokenCount m' p + consumptionCount c (TokenCount m p) = TokenCount m p)
-/
#guard_msgs in #print CORE_030

/-- The reference semantics satisfies CORE-030: `Seam.fireNC` leaves a non-reset place with
`m p - nconsumed + deposited`, `Seam.nconsumed` is the consumption count of the arc `nspecAt`
finds, and enablement (`Seam.enabledNA`) guarantees the place holds at least the required count,
so the subtraction does not truncate. A reference firing deposits only in places its output spec
names, so outside them the deposit is empty and the place loses exactly the consumption count. -/
@[evidence holds CORE_030]
theorem CORE_030_reference {N : Type} [DecidableEq N] : CORE_030 (RefFire (N := N)) := by
  intro t p c _ hin hr d m m' hf _
  have happ := refFire_apply hf p
  rw [if_neg hr, consumes_eq] at happ
  obtain ⟨s, hmem, hp, hc⟩ := inputArc_mem hin
  have hreq := ((enabled_iff t m).1 hf.1).1 s hmem
  obtain ⟨s', hs', hc'⟩ := hin
  rw [hs'] at happ
  subst hp hc
  have hcard : s'.card = s.card := hc'
  have hle : consumptionCount s.card (m s.place) ≤ m s.place := by
    simp only [consumptionCount]; split <;> omega
  simp only [hcard] at happ
  simp only [TokenCount]
  refine ⟨by omega, fun ho => ?_⟩
  have h0 : Deposits d s.place = 0 :=
    List.count_eq_zero_of_not_mem (fun h => ho (refFire_outputs hf s.place h))
  omega

/-! ### Examples over a one-place net -/

/-- The one transition of the examples: one input arc on place `0` of cardinality `c`, no other
arcs, no output spec. -/
def core030_t (c : Card) : Trans Nat :=
  { core := { name := "t", inputs := [⟨0, c⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- `core030_t c` has no output place. -/
theorem core030_t_noOut (c : Card) (p : Nat) : ¬ OutputArc (core030_t c) p := by
  rintro ⟨o, h, -⟩; simp [core030_t] at h

/-- The marking of the examples in which every place holds `k` tokens. -/
def core030_const (k : Nat) : Nat → Nat := fun _ => k

/-- The firing that changes nothing: every transition may fire from every marking, depositing
nothing and leaving the marking as it is. Its input arcs consume nothing. -/
def core030_idleFire : FireRel Nat := fun _ m d m' => d = [] ∧ m' = m

/-- ✗ A firing that consumes nothing through its input arcs violates CORE-030 (second line):
`core030_t .one` fires from one token in place `0` and leaves that token there. -/
@[evidence forbids CORE_030]
theorem CORE_030_forbids_idle : ¬ CORE_030 core030_idleFire := by
  intro h
  have := (h (core030_t .one) 0 .one (by decide) ⟨⟨0, .one⟩, rfl, rfl⟩ (by decide) []
    (core030_const 1) (core030_const 1) ⟨rfl, rfl⟩ (by decide)).1
  exact absurd this (by decide)

/-- The tokens a ghost firing of `t` from `m` reports in `q`: the consumption count of the input
arc on `q`, none where `t` has no input arc. -/
def core030_ghostCount (t : Trans Nat) (m : Nat → Nat) (q : Nat) : Nat :=
  match nspecAt t.core q with
  | none => 0
  | some s => consumptionCount s.card (m q)

/-- A ghost-deposit firing relation: a transition fires, consumes nothing, leaves the marking as
it is and reports a deposit of as many tokens in each input place as the input arc's consumption
count, whether or not its output spec names the place. -/
def core030_ghostFire : FireRel Nat :=
  fun t m d m' => (∀ q, Deposits d q = core030_ghostCount t m q) ∧ m' = m

/-- ✗ A firing that consumes nothing but reports a deposit in its input place violates CORE-030
(third line): `core030_t .one` has no output place, fires from one token in place `0`, reports a
deposit of one token there, and leaves that token in place `0`. -/
@[evidence forbids CORE_030]
theorem CORE_030_forbids_ghost : ¬ CORE_030 core030_ghostFire := by
  intro h
  have hd : ∀ q, Deposits [0] q = core030_ghostCount (core030_t .one) (core030_const 1) q := by
    intro q
    by_cases hq : q = 0
    · subst hq; decide
    · simp [Deposits, depProd, core030_ghostCount, nspecAt, core030_t, Ne.symm hq]
  have := (h (core030_t .one) 0 .one (by decide) ⟨⟨0, .one⟩, rfl, rfl⟩ (by decide) [0]
    (core030_const 1) (core030_const 1) ⟨hd, rfl⟩ (by decide)).2 (core030_t_noOut .one 0)
  exact absurd this (by decide)

/-! ### Mutants: each changes one line, and a relation tells it apart from CORE-030 -/

/-- Mutant reading of CORE-030 in which an input arc consumes nothing: every firing leaves a
non-reset input place with its tokens plus what was deposited there. -/
def CORE_030_mutant_noConsume {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t p c, InputPlacesDistinct t → InputArc t p c → ¬ ResetArc t p → ∀ d,
    (on (fun m m' => F t m d m'), shall
      (fun m m' => TokenCount m' p = TokenCount m p + Deposits d p))

/-- The idle firing kills the no-consumption mutant: it satisfies it (nothing changes, nothing is
deposited) but not CORE-030. -/
@[evidence mutant CORE_030]
theorem CORE_030_mutant_noConsume_killed :
    CORE_030_mutant_noConsume core030_idleFire ∧ ¬ CORE_030 core030_idleFire := by
  refine ⟨?_, CORE_030_forbids_idle⟩
  rintro t p c - - - d m m' ⟨rfl, rfl⟩
  simp [Deposits, depProd]

/-- Mutant reading of CORE-030 in which every input arc consumes its required count, so that
`All` and `AtLeast(m)` consume their minimum instead of every token in the place. -/
def CORE_030_mutant_required {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t p c, InputPlacesDistinct t → InputArc t p c → ¬ ResetArc t p → ∀ d,
    (on (fun m m' => F t m d m'), shall
      (fun m m' => TokenCount m' p + requiredCount c = TokenCount m p + Deposits d p ∧
        (¬ OutputArc t p → TokenCount m' p + requiredCount c = TokenCount m p)))

/-- A firing relation that consumes the required count from every input place and deposits
nothing: enabled on input arcs, and each input place loses its arc's required count. -/
def core030_requiredFire : FireRel Nat := fun t m d m' =>
  d = [] ∧ (∀ s ∈ t.core.inputs, s.card.required ≤ m s.place) ∧
    m' = fun q => m q - (match nspecAt t.core q with
      | none => 0
      | some s => s.card.required)

/-- The required-count firing kills the second mutant: it satisfies it, but `core030_t .all`
fires from two tokens in place `0` and leaves one, where CORE-030 says `All` consumes both. -/
@[evidence mutant CORE_030]
theorem CORE_030_mutant_required_killed :
    CORE_030_mutant_required core030_requiredFire ∧ ¬ CORE_030 core030_requiredFire := by
  refine ⟨?_, fun h => ?_⟩
  · rintro t p c - hin - d m m' ⟨rfl, hen, rfl⟩
    obtain ⟨s, hmem, hp, hc⟩ := inputArc_mem hin
    have hreq := hen s hmem
    obtain ⟨s', hs', hc'⟩ := hin
    subst hp hc
    have : s'.card = s.card := hc'
    simp only [TokenCount, Deposits, depProd, requiredCount, hs', this]
    simp only [List.count_nil]
    exact ⟨by omega, fun _ => by omega⟩
  · have := (h (core030_t .all) 0 .all (by decide) ⟨⟨0, .all⟩, rfl, rfl⟩ (by decide) []
      (core030_const 2) (fun q => core030_const 2 q - (match nspecAt (core030_t .all).core q with
        | none => 0
        | some s => s.card.required))
      ⟨rfl, by decide, rfl⟩ (by decide)).1
    exact absurd this (by decide)

/-- Mutant reading of CORE-030 that drops the third line: the count trusts the deposit the
firing reports, also in a place outside the output spec. -/
def CORE_030_mutant_trustDeposit {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t p c, InputPlacesDistinct t → InputArc t p c → ¬ ResetArc t p → ∀ d,
    (on (fun m m' => F t m d m'), shall
      (fun m m' => requiredCount c ≤ TokenCount m p →
        TokenCount m' p + consumptionCount c (TokenCount m p) = TokenCount m p + Deposits d p))

/-- The ghost-deposit firing kills the trust-deposit mutant: the deposit it reports in each input
place makes up for the tokens it does not take, so it satisfies the mutant; but
`core030_t .one` has no output place, and its input place keeps its token. -/
@[evidence mutant CORE_030]
theorem CORE_030_mutant_trustDeposit_killed :
    CORE_030_mutant_trustDeposit core030_ghostFire ∧ ¬ CORE_030 core030_ghostFire := by
  refine ⟨?_, CORE_030_forbids_ghost⟩
  rintro t p c - hin - d m m' ⟨hd, rfl⟩ -
  obtain ⟨s', hs', hc'⟩ := hin
  rw [hd p]
  simp only [core030_ghostCount, hs', hc', TokenCount]

/-- Mutant reading of CORE-030 without the enablement guard: both lines are required of every
firing, even one from a marking where the input place holds fewer tokens than the arc requires.
It says more than the requirement, which speaks only of how much a firing consumes, not of which
firings may happen. -/
def CORE_030_mutant_unguarded {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t p c, InputPlacesDistinct t → InputArc t p c → ¬ ResetArc t p → ∀ d,
    (on (fun m m' => F t m d m'), shall
      (fun m m' => TokenCount m' p + consumptionCount c (TokenCount m p) =
          TokenCount m p + Deposits d p ∧
        (¬ OutputArc t p →
          TokenCount m' p + consumptionCount c (TokenCount m p) = TokenCount m p)))

/-- A firing relation that ignores enablement: every transition fires from every marking,
deposits nothing, and takes from each input place its consumption count, as far as the place
holds tokens. -/
def core030_unguardedFire : FireRel Nat := fun t m d m' =>
  d = [] ∧ m' = fun q => m q - (match nspecAt t.core q with
      | none => 0
      | some s => consumptionCount s.card (m q))

/-- CORE-030 allows a firing of a transition that is not enabled, as long as every enabled
firing consumes the consumption count: the unguarded firing relation satisfies CORE-030, and
`core030_t .one` firing from an empty place `0` tells it apart from the unguarded mutant, which
would forbid that firing although CORE-030 says nothing about it. -/
@[evidence allows CORE_030]
theorem CORE_030_allows_unenabled :
    CORE_030 core030_unguardedFire ∧ ¬ CORE_030_mutant_unguarded core030_unguardedFire := by
  refine ⟨?_, fun h => ?_⟩
  · rintro t p c - hin - d m m' ⟨rfl, rfl⟩ hreq
    obtain ⟨s', hs', hc'⟩ := hin
    simp only [TokenCount, Deposits, depProd, hs', hc', List.count_nil, consumptionCount,
      requiredCount] at hreq ⊢
    split <;> exact ⟨by omega, fun _ => by omega⟩
  · have := (h (core030_t .one) 0 .one (by decide) ⟨⟨0, .one⟩, rfl, rfl⟩ (by decide) []
      (core030_const 0) _ ⟨rfl, rfl⟩).1
    exact absurd this (by decide)

/-- The marking of the examples in which place `0` holds `k` tokens and every other place is
empty. -/
def core030_at0 (k : Nat) : Nat → Nat := fun n => if n = 0 then k else 0

/-- Both lines of CORE-030 are exercised by the reference semantics: `core030_t .all` has a
single input arc, of cardinality `All`, on place `0`, which is neither a reset place nor an
output place, and it fires from two tokens in place `0` to none, consuming both. -/
@[evidence nonvacuous CORE_030]
theorem CORE_030_nonvacuous :
    InputPlacesDistinct (core030_t .all) ∧ InputArc (core030_t .all) 0 .all ∧
      ¬ ResetArc (core030_t .all) 0 ∧ ¬ OutputArc (core030_t .all) 0 ∧
      RefFire (core030_t .all) (core030_at0 2) [] (core030_at0 0) := by
  refine ⟨by decide, ⟨⟨0, .all⟩, rfl, rfl⟩, by decide, core030_t_noOut .all 0, by decide,
    ⟨.action 0, rfl⟩, ?_⟩
  funext n
  by_cases h : n = 0
  · subst h; simp [fireNC, depProd, nconsumed, nspecAt, core030_t, core030_at0, Card.consumesAll]
  · simp [fireNC, depProd, nconsumed, nspecAt, core030_t, core030_at0, h, Ne.symm h]

end Libpetri.Spec
