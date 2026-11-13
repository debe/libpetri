import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.Glossary

set_option linter.missingDocs true

/-!
# CORE-036: Arc semantics summary (`spec/01-core-model.md`)

A predicate over an abstract firing relation `F : FireRel N`, checked against the reference
semantics (`RefFire`), against concrete firing relations that break it, and against one mutant
reading per clause.

The eight clauses are the two columns of the table, "Requires token?" (the first four) and
"Consumes?" with "Effect" (the last four). The mutants are all built the same way
(`core036_model`): a firing is a gate on the source marking, a choice of deposit, and the
effect `Seam.fireNC` of some transition core. The reference semantics is the model with the
gate `Enabled`, the deposits of the output spec and the transition's own core; each mutant
changes exactly one of the three, so the clause lemmas below discharge the seven clauses it
keeps.

The eighth clause, the outcome line, compares deposits by places and per place, never as lists
(`OnPlacesOf`, `SamePerPlace`): a write of several tokens into one place of an
output branch, in any order, conforms (`CORE_036_allows_multi`), and closing a firing relation
under per-place equal deposits keeps CORE-036 (`core036_perPlace_closed`). Two further mutants
weaken that line: one accepts a write to part of a branch, one compares a timeout outcome by
places only.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## CORE-036: Arc semantics summary -/

requirement CORE_036
  id "CORE-036"
  title "Arc semantics summary"
  kind B
  scope "all executors; the outcome line with output validation enabled (CONC-026, the default)"
  source verbatim "spec/01-core-model.md"
  quote "*While* an input place of the transition holds fewer tokens than the required count of its input arc, the transition *shall not* fire."
        "*While* a read place of the transition is unmarked, the transition *shall not* fire."
        "*While* an inhibitor place of the transition is marked, the transition *shall not* fire."
        "*While* the transition has no match specification ([NU-020]) and is enabled, it *shall* be able to fire, whatever its output places and reset places hold."
        "*When* the transition fires, each input place that is not a reset place *shall* lose the consumption count of its input arc, and gain what the firing deposits there."
        "*When* the transition fires, each place that is neither an input place nor a reset place *shall* lose no tokens, and gain what the firing deposits there."
        "*When* the transition fires, each reset place *shall* end holding exactly what the firing deposited there."
        "*When* the transition fires and the firing ends with its action, on an executor with output validation enabled ([CONC-026], the default), the places in which it deposits *shall* be exactly the places of one output branch of its output spec, each receiving one or more tokens."
        "*When* the transition fires and the firing ends with the timeout outcome, it *shall* deposit in every place as many tokens as the timeout outcome puts there ([IO-013], [IO-014])."
        "Deposits are compared per place: the order in which a firing deposits its tokens is not normative, and two deposits that put the same number of tokens in every place are the same deposit."
        "As in [CORE-022], the transitions these sentences describe are transitions that build: a definition that building rejects is not a transition of any net and never fires."
  reading "For every transition t:"
          "t does not fire from a marking in which an input place p holds fewer tokens than the required count c of its input arc;"
          "t does not fire from a marking in which a read place p is unmarked;"
          "t does not fire from a marking in which an inhibitor place p is marked;"
          "if t builds (Builds t: it passes every build-time check), then from every marking at which t is enabled some firing of t exists (to some marking);"
          "every firing of t that deposits d leaves an input place p that is not a reset place with what it held, minus the consumption count of its arc, plus what d puts in p;"
          "every firing of t that deposits d leaves a place p that is neither an input place nor a reset place of t with what it held plus what d puts in p;"
          "every firing of t that deposits d leaves a reset place p with exactly what d puts in p;"
          "every firing of t from m that deposits d either puts one or more tokens in each place of some output branch b of t and none in any other place, or puts in every place as many tokens as some timeout outcome d₀ of t for what the firing consumed from m."
  assumes "A firing is read as one step from a marking to a marking (glossary: Fire); timing and priority play no part, so 'produced on complete' (Output) and 'consumed / removed on fire' (Input, Reset) both land in the one step. 'Able to fire' is read as 'some firing exists', to any target marking."
          "Requires token? column. 'Yes' for an input arc is read as 'holds at least the required count' (glossary: Enabled, Required count), which is one token for One and All; 'Yes' for a read arc as 'marked'; 'No (blocks if present)' for an inhibitor arc as 'marked blocks'. The 'No' entries (output, reset, and the inhibitor arc while its place is unmarked) are read together as the fourth line: the table lists every token requirement, so a transition whose input, read and inhibitor arcs are all satisfied can fire whatever its output and reset places hold."
          "Consumes? column. 'Yes' for an input arc is read as the consumption count of IO-007 (glossary: Consumption count). 'No' for output, inhibitor and read arcs is the sixth line: a place that only those arcs touch loses nothing. 'Yes (all)' for a reset arc is the seventh line (glossary: Deposit): a reset place that is also an output place keeps what the firing deposited there, and a reset place that is also an input place ends with the deposit too, so the fifth line excludes reset places."
          "The fifth line uses truncated subtraction, as Seam.fireNC does; under the first line the subtraction never truncates, because a firing only starts when every input place holds at least its required count."
          "Effect column, Output ('Token produced on complete') is the outcome line, the last line of the reading, which reads the eighth, ninth and tenth sentences quoted together. A firing relation does not record how a firing ended. As IO-012 says, a firing ends with its action when it does not end with the timeout outcome, and a firing whose deposit puts in every place as many tokens as some timeout-outcome deposit of the transition from the same marking may have ended with the timeout outcome. So the eighth and ninth sentences are read as one disjunction: the deposit marks exactly the places of an output branch (eighth: the branch fixes which places receive tokens, one or more each, not how many; glossary: Output branch, Produced set), or it equals a timeout outcome per place (ninth: as many tokens in every place). A transition with no output spec has the one empty branch, so it deposits nothing. Read ('Token remains') is the sixth line. Inhibitor ('Disables transition') is the third line."
          "Tenth sentence (deposits are compared per place). Every line of the reading reads the deposit d only through Deposits d (the produced set of d is the set of places p with Deposits d p ≠ 0), so two deposits that put the same number of tokens in every place satisfy it alike and the order of d plays no part: core036_c8_perPlace shows it for the outcome line, and core036_perPlace_closed shows that closing any firing relation under per-place equal deposits keeps CORE-036. Lines 5 to 7 already compare per place."
          "The outcome line is scoped by CONC-026: F is read as the firing relation of an executor with output validation enabled, the default. With the CONC-026 skip enabled a firing that ends with its action deposits what the action wrote, as CONC-026 says, and the outcome line is not claimed of it; lines 1 to 7 hold of every executor."
          "The eleventh sentence (the transitions described are those that build) is read as CORE-022 reads it: 'transitions that build' is the glossary term Builds. It scopes line 4, the one existence claim: a definition that building rejects never fires (CORE-022, CONC-026), so no firing of it is asked, and an executor that holds only transitions that build satisfies CORE-036 (CORE_036_builtOnly). Lines 1 to 3 and 5 to 8 forbid or constrain firings; a transition that does not build has no firing in any executor, so on it they ask nothing of an executor, and they are stated over every Trans because the reference fires every transition and meets them on all of them. TimeoutOutcome reads the first Timeout node in pre-order. A transition that builds holds at most one Timeout node and no ForwardInput outside a Timeout child (IO-013, IO-014), so that node's outcome is the timeout outcome. That at most one output branch matches a deposit (IO-012) is not part of CORE-036: the outcome line asks for some branch."
          "Transitions with a ν match specification (NU-020) are scoped out of the fourth sentence (ruling D30, as in CORE-022): such a transition can be enabled at count level (glossary: Enabled) and still unable to fire, because no single name satisfies every correlated input. The transitions of the model (Reference.Trans) carry no match specification, so line 4 quantifies over every transition that builds. On a correlated input the consumption count of the fifth sentence applies to the tokens of the chosen name (glossary: Correlated input), not to the whole place; line 5 reads it over the whole place, which is the same thing for a transition with no match specification. How the correlation condition decides a firing and what it consumes is NU-020's, not encoded here. Lines 1 to 3 need no exclusion, for the reason CORE-022 gives: a correlated input requires at least its required count of tokens of one name, so at least its required count of tokens."
          "Which runtime firings are steps of F. A firing whose action fails, or whose completion fails output validation (EXEC-030, IO-015 AC2 and AC3), consumes its inputs and clears its reset places but deposits no outcome; it is not a firing in F (glossary: Fire), as in CORE-050, so the outcome line says nothing of it and line 4 asks only that some firing exists. Tokens an action publishes before the firing ends (ctx.flush(), Rust and Python only; IO-015) are not in the one-step model, as in EXEC-020 and CORE-050: the orchestrator deposits each flushed batch as a step of its own (CONC-001), the firing's deposit d is what the executor deposits when the firing ends, and F is read as the firings whose action publishes nothing mid-action. With a flush, IO-015 counts the flushed places towards the eighth sentence's branch, and a firing that ends with the timeout outcome keeps the flushed tokens besides the timeout outcome (glossary: Action), so on Xor(A, Timeout(B)) an action that flushes A and then times out leaves A and B; that is the ninth sentence read over the deposit at the firing's end, and neither case is encoded."
          "What the outcome line loses. A firing relation does not record how a firing ended, so a firing that ended with the timeout outcome but deposits exactly the places of some output branch, with any counts, satisfies the first disjunct. On t: All(2) -> Timeout(ForwardInput(2, 1)), which consumes two tokens from 2, the deposit [1] (forwarding only the first consumed token, which IO-014 forbids) passes, although the timeout outcome is [1, 1] (core036_fwdFirst_accepted): [1] is also the places of the Timeout child read as an output branch. The ninth sentence's full strength, per place for every firing that ends with the timeout outcome, is carried over a relation T of timed-out firings by IO-013's fifth line ('every firing of t in T from m deposits, place by place, exactly the tokens of the timeout outcome') and IO-014's firing line; here the ninth sentence only widens what an action firing may look like."
          "The ninth sentence in the runtimes. Every runtime deposits the timeout outcome without validating it against the output spec and on the places the rewritten output spec names, as given: on And(A, Timeout(d, B)) a timed-out firing deposits B (Java BitmapNetExecutor and PrecompiledNetExecutor processCompletedTransitions, and TypeScript bitmap-net-executor.ts and precompiled-net-executor.ts, skip validation when TransitionContext.isDetachedForTimeout(); Rust, and Python on it, skip it on the timeout path), and Java (TransitionContext outputToHarvest and forwardToHarvest, ExecutorSupport produceTimeoutOutputRecursive) and TypeScript (transition-context.ts outputToHarvest and forwardToHarvest) take the actual places without resolving them through the composition correspondence again. Two wrong executors are recorded in spec/runtime-defects.md as history of Java and TypeScript. RD-01: one that validates the timeout outcome against the whole output spec fails every timed-out firing of And(A, Timeout(d, B)); the statement does not catch it, because a failed firing is not in F and line 4 asks only that some firing exists; IO-013's T-lines do (IO_013_forbids_validateTimeout). RD-31: one that resolves the timeout branch's places through the correspondence a second time deposits, on a port collision (port a bound to b, port b bound to c), the timeout token meant for b on c; when c is an output place the deposit can pass the first disjunct of the outcome line, so the statement does not catch it either; IO-013's fifth line and MOD-031 do (mod031ctx_timeout_resolveTwice in MOD_031.lean)."
          "Read, 'provides value': the value of the read token is not visible at token-count granularity; that the action receives it is CORE-032 AC3, not encoded here."
          "Input token order (FIFO, CORE-030 AC2) and output token timestamps (CORE-035 AC2, IO-014 AC5) are below token-count granularity and not encoded here."
          "AC1 (each arc type behaves exactly as described in the table) is the whole statement: one line per cell of the 'Requires token?' column (lines 1 to 4) and of the 'Consumes?' and 'Effect' columns (lines 5 to 7 and the outcome line), as laid out in the assumptions above."
          "AC2 (an action that writes two tokens into one place of the branch it satisfies fires, and the marking receives all of them) is CORE_036_allows_multi: CORE-036 holds of a firing relation in which t: a → and(b, c) fires with the write b, b, c, and that firing leaves 2 tokens in b and 1 in c. That such a write is deposited at all is IO-015 and IO-016 AC4; CORE-036 only has to allow it."
          "AC3 (two firings that deposit the same number of tokens in every place, in different orders, deposit the same outcome) is core036_c8_perPlace and core036_perPlace_closed, and concretely CORE_036_allows_multi: the write c, b, b of the same transition is allowed alike and leaves the same marking."
          "InputArc names the first input arc on a place (glossary: Input arc); CORE-030 rejects a transition with two input arcs on one place at build, so for every well-formed transition it is the only one."
  signoff "2026-11-13 153aed3781898e2a ai"
  statement : ∀ {N : Type} [DecidableEq N], FireRel N → Prop :=
    fun F => ∀ t,
      (∀ p c, InputArc t p c →
        while (fun m => TokenCount m p < requiredCount c), never Fire F t) ∧
      (∀ p, ReadArc t p → while (fun m => ¬ Marked m p), never Fire F t) ∧
      (∀ p, InhibitorArc t p → while (fun m => Marked m p), never Fire F t) ∧
      (Builds t → ∀ m, Enabled t m → ∃ m', Fire F t m m') ∧
      (∀ d p c, InputArc t p c → ¬ ResetArc t p →
        on (fun m m' => F t m d m'), shall (fun m m' =>
          TokenCount m' p = TokenCount m p - consumptionCount c (TokenCount m p) + Deposits d p)) ∧
      (∀ d p, (∀ c, ¬ InputArc t p c) → ¬ ResetArc t p →
        on (fun m m' => F t m d m'), shall (fun m m' =>
          TokenCount m' p = TokenCount m p + Deposits d p)) ∧
      (∀ d p, ResetArc t p →
        on (fun m m' => F t m d m'), shall (fun _ m' => TokenCount m' p = Deposits d p)) ∧
      (∀ d, on (fun m m' => F t m d m'), shall (fun m _ =>
        (∃ b, OutputBranch t b ∧ OnPlacesOf d b) ∨
        (∃ d₀, TimeoutOutcome t (Consumes t m) d₀ ∧ SamePerPlace d d₀)))

/- The pinned readable form of CORE-036: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CORE_036 : {N : Type} → [DecidableEq N] → FireRel N → Prop :=
fun {N} [DecidableEq N] F =>
  ∀ (t : Reference.Trans N),
    (∀ (p : N) (c : Card), InputArc t p c → while fun m => TokenCount m p < requiredCount c, never Fire F t) ∧
      (∀ (p : N), ReadArc t p → while fun m => ¬Marked m p, never Fire F t) ∧
        (∀ (p : N), InhibitorArc t p → while fun m => Marked m p, never Fire F t) ∧
          (Builds t → ∀ (m : CountMarking N), Enabled t m → ∃ m', Fire F t m m') ∧
            (∀ (d : List N) (p : N) (c : Card),
                InputArc t p c →
                  ¬ResetArc t p →
                    on fun m m' => F t m d m', shall fun m m' =>
                      TokenCount m' p = TokenCount m p - consumptionCount c (TokenCount m p) + Deposits d p) ∧
              (∀ (d : List N) (p : N),
                  (∀ (c : Card), ¬InputArc t p c) →
                    ¬ResetArc t p →
                      on fun m m' => F t m d m', shall fun m m' => TokenCount m' p = TokenCount m p + Deposits d p) ∧
                (∀ (d : List N) (p : N),
                    ResetArc t p → on fun m m' => F t m d m', shall fun x m' => TokenCount m' p = Deposits d p) ∧
                  ∀ (d : List N),
                    on fun m m' => F t m d m', shall fun m x =>
                      (∃ b, OutputBranch t b ∧ OnPlacesOf d b) ∨
                        ∃ d₀, TimeoutOutcome t (Consumes t m) d₀ ∧ SamePerPlace d d₀
-/
#guard_msgs in #print CORE_036

/-! ### The eight clauses, by name

The same formulas as the statement, one definition each, so that a mutant can drop one clause
and the clause lemmas can name the one they prove. `core036_iff` checks that their conjunction
is the statement. -/

section Clauses

variable {N : Type} [DecidableEq N]

/-- Line 1: an input place below its required count blocks the transition. -/
def core036_c1 (F : FireRel N) (t : Trans N) : Prop :=
  ∀ p c, InputArc t p c → while (fun m => TokenCount m p < requiredCount c), never Fire F t

/-- Line 2: an unmarked read place blocks the transition. -/
def core036_c2 (F : FireRel N) (t : Trans N) : Prop :=
  ∀ p, ReadArc t p → while (fun m => ¬ Marked m p), never Fire F t

/-- Line 3: a marked inhibitor place blocks the transition. -/
def core036_c3 (F : FireRel N) (t : Trans N) : Prop :=
  ∀ p, InhibitorArc t p → while (fun m => Marked m p), never Fire F t

/-- Line 4: an enabled transition that builds can fire. -/
def core036_c4 (F : FireRel N) (t : Trans N) : Prop :=
  Builds t → ∀ m, Enabled t m → ∃ m', Fire F t m m'

/-- Line 5: an input place that is not a reset place loses its consumption count. -/
def core036_c5 (F : FireRel N) (t : Trans N) : Prop :=
  ∀ d p c, InputArc t p c → ¬ ResetArc t p →
    on (fun m m' => F t m d m'), shall (fun m m' =>
      TokenCount m' p = TokenCount m p - consumptionCount c (TokenCount m p) + Deposits d p)

/-- Line 6: a place that is neither an input nor a reset place loses nothing. -/
def core036_c6 (F : FireRel N) (t : Trans N) : Prop :=
  ∀ d p, (∀ c, ¬ InputArc t p c) → ¬ ResetArc t p →
    on (fun m m' => F t m d m'), shall (fun m m' =>
      TokenCount m' p = TokenCount m p + Deposits d p)

/-- Line 7: a reset place ends with exactly the deposit. -/
def core036_c7 (F : FireRel N) (t : Trans N) : Prop :=
  ∀ d p, ResetArc t p →
    on (fun m m' => F t m d m'), shall (fun _ m' => TokenCount m' p = Deposits d p)

/-- The outcome line, of one deposit: it marks exactly the places of an output branch, or it
equals a timeout outcome per place. -/
def core036_outcome (t : Trans N) (consumed : N → Nat) (d : List N) : Prop :=
  (∃ b, OutputBranch t b ∧ OnPlacesOf d b) ∨
  (∃ d₀, TimeoutOutcome t consumed d₀ ∧ SamePerPlace d d₀)

/-- Line 8 (the outcome line): the deposit is one outcome of the output spec, compared by
places for an output branch and per place for the timeout outcome. -/
def core036_c8 (F : FireRel N) (t : Trans N) : Prop :=
  ∀ d, on (fun m m' => F t m d m'), shall (fun m _ => core036_outcome t (Consumes t m) d)

/-- CORE-036 is the conjunction of its eight clauses, for every transition. -/
theorem core036_iff (F : FireRel N) :
    CORE_036 F ↔ ∀ t, core036_c1 F t ∧ core036_c2 F t ∧ core036_c3 F t ∧ core036_c4 F t ∧
      core036_c5 F t ∧ core036_c6 F t ∧ core036_c7 F t ∧ core036_c8 F t := Iff.rfl

end Clauses

/-! ### Gated firing models and the clause lemmas -/

section Models

variable {N : Type} [DecidableEq N]

/-- A firing model: `t` fires from `m` when the gate `g t m` holds, deposits a `d` that `dep t m`
allows, and leaves the effect `Seam.fireNC` of the transition core `k t`. -/
def core036_model (g : Trans N → (N → Nat) → Prop) (dep : Trans N → (N → Nat) → List N → Prop)
    (k : Trans N → NTransition N) : FireRel N :=
  fun t m d m' => g t m ∧ dep t m d ∧ m' = fireNC m (k t) (depProd d)

/-- The reference deposits: one outcome of the output spec. -/
def core036_refDep (t : Trans N) (m : N → Nat) (d : List N) : Prop :=
  ∃ ch, deposit (Consumes t m) (OutputSpec t) ch = some d

/-- Every input place holds at least its required count. -/
abbrev core036_inOk (t : Trans N) (m : N → Nat) : Prop :=
  ∀ s ∈ t.core.inputs, requiredCount s.card ≤ m s.place

/-- Every read place is marked. -/
abbrev core036_rdOk (t : Trans N) (m : N → Nat) : Prop := ∀ p ∈ t.core.reads, Marked m p

/-- No inhibitor place is marked. -/
abbrev core036_ihOk (t : Trans N) (m : N → Nat) : Prop := ∀ p ∈ t.core.inhibitors, ¬ Marked m p

/-- The reference firing relation is the gated model with gate `Enabled`, the reference
deposits and the transition's own core. -/
theorem core036_refFire_eq :
    (RefFire (N := N)) = core036_model Enabled core036_refDep (·.core) := rfl

/-- The input arc `InputArc` names is one of the transition's input arcs, on that place. -/
theorem core036_inputArc_mem {t : Trans N} {p : N} {c : Card} (h : InputArc t p c) :
    ∃ s ∈ t.core.inputs, s.place = p ∧ s.card = c := by
  obtain ⟨s, hs, hc⟩ := h
  refine ⟨s, List.mem_of_find?_eq_some hs, ?_, hc⟩
  simpa using List.find?_some hs

/-- A place with no input arc has no arc for `nspecAt` to find. -/
theorem core036_nspecAt_none {t : Trans N} {p : N} (h : ∀ c, ¬ InputArc t p c) :
    nspecAt t.core p = none := by
  cases hs : nspecAt t.core p with
  | none => rfl
  | some s => exact absurd ⟨s, hs, rfl⟩ (h s.card)

/-- Line 1 holds in a model whose gate checks every input place. -/
theorem core036_c1_of {g dep k} (hg : ∀ t m, g t m → core036_inOk t m) (t : Trans N) :
    core036_c1 (core036_model g dep k) t := by
  rintro p c hpc m m' ⟨_, hgm, -, -⟩ hlt
  obtain ⟨s, hs, hp, hc⟩ := core036_inputArc_mem hpc
  have := hg t m hgm s hs
  rw [hp, hc] at this
  exact absurd this (Nat.not_le.mpr hlt)

/-- Line 2 holds in a model whose gate checks every read place. -/
theorem core036_c2_of {g dep k} (hg : ∀ t m, g t m → core036_rdOk t m) (t : Trans N) :
    core036_c2 (core036_model g dep k) t :=
  by
  rintro p hp m _ ⟨_, hgm, -, -⟩ hu
  exact hu (hg t m hgm p hp)

/-- Line 3 holds in a model whose gate checks every inhibitor place. -/
theorem core036_c3_of {g dep k} (hg : ∀ t m, g t m → core036_ihOk t m) (t : Trans N) :
    core036_c3 (core036_model g dep k) t :=
  by
  rintro p hp m _ ⟨_, hgm, -, -⟩ hmk
  exact hg t m hgm p hp hmk

/-- Line 4 holds in a model whose gate admits every enabled transition and that always has a
deposit. -/
theorem core036_c4_of {g dep k} (hg : ∀ t m, Enabled t m → g t m)
    (hd : ∀ t m, ∃ d, dep t m d) (t : Trans N) : core036_c4 (core036_model g dep k) t := by
  intro _ m hen
  obtain ⟨d, hdm⟩ := hd t m
  exact ⟨_, d, hg t m hen, hdm, rfl⟩

/-- Line 5 holds in a model whose effect core consumes the consumption count from every input
place that is not a reset place, and does not reset it. -/
theorem core036_c5_of {g dep k}
    (hk : ∀ (t : Trans N) p c m, InputArc t p c → ¬ ResetArc t p →
      p ∉ (k t).resets ∧ nconsumed m (k t) p = consumptionCount c (m p))
    (t : Trans N) : core036_c5 (core036_model g dep k) t := by
  rintro d p c hpc hr m m' ⟨-, -, hm'⟩
  obtain ⟨h1, h2⟩ := hk t p c m hpc hr
  subst hm'
  simp only [TokenCount, Deposits, fireNC, if_neg h1, h2]

/-- Line 6 holds in a model whose effect core neither consumes from nor resets a place that is
neither an input nor a reset place. -/
theorem core036_c6_of {g dep k}
    (hk : ∀ (t : Trans N) p m, (∀ c, ¬ InputArc t p c) → ¬ ResetArc t p →
      p ∉ (k t).resets ∧ nconsumed m (k t) p = 0)
    (t : Trans N) : core036_c6 (core036_model g dep k) t := by
  rintro d p hpc hr m m' ⟨-, -, hm'⟩
  obtain ⟨h1, h2⟩ := hk t p m hpc hr
  subst hm'
  simp only [TokenCount, Deposits, fireNC, if_neg h1, h2, Nat.sub_zero]

/-- Line 7 holds in a model whose effect core resets every reset place. -/
theorem core036_c7_of {g dep k} (hk : ∀ (t : Trans N) p, ResetArc t p → p ∈ (k t).resets)
    (t : Trans N) : core036_c7 (core036_model g dep k) t := by
  rintro d p hp m m' ⟨-, -, hm'⟩
  subst hm'
  simp only [TokenCount, Deposits, fireNC, if_pos (hk t p hp)]

/-- Line 8 holds in a model whose deposits are outcomes of the output spec. -/
theorem core036_c8_of {g dep k}
    (hd : ∀ (t : Trans N) m d, dep t m d → core036_outcome t (Consumes t m) d)
    (t : Trans N) : core036_c8 (core036_model g dep k) t :=
  by
  rintro d m _ ⟨_, hdm, -⟩
  exact hd t m d hdm

omit [DecidableEq N] in
/-- `Enabled` is the conjunction of the three gate parts. -/
theorem core036_enabled_iff (t : Trans N) (m : N → Nat) :
    Enabled t m ↔ core036_inOk t m ∧ core036_ihOk t m ∧ core036_rdOk t m :=
  enabled_iff t m

/-- The reference consumption at an input place is the consumption count of its arc. -/
theorem core036_ref_c5 (t : Trans N) (p : N) (c : Card) (m : N → Nat) (hpc : InputArc t p c)
    (hr : ¬ ResetArc t p) :
    p ∉ t.core.resets ∧ nconsumed m t.core p = consumptionCount c (m p) := by
  obtain ⟨s, hs, hc⟩ := hpc
  refine ⟨hr, ?_⟩
  simp only [nconsumed, hs, consumptionCount, hc]

/-- The reference consumes nothing from a place with no input arc. -/
theorem core036_ref_c6 (t : Trans N) (p : N) (m : N → Nat) (hpc : ∀ c, ¬ InputArc t p c)
    (hr : ¬ ResetArc t p) : p ∉ t.core.resets ∧ nconsumed m t.core p = 0 := by
  refine ⟨hr, ?_⟩
  simp only [nconsumed, core036_nspecAt_none hpc]

/-- Every reference deposit is an output branch or a timeout outcome, as a list. -/
theorem core036_ref_c8_list (t : Trans N) (m : N → Nat) (d : List N) (h : core036_refDep t m d) :
    OutputBranch t d ∨ TimeoutOutcome t (Consumes t m) d := by
  obtain ⟨ch, hch⟩ := h
  unfold OutputBranch TimeoutOutcome
  simp only [OutputSpec] at hch
  cases ho : t.out with
  | none =>
    rw [ho] at hch
    cases ch with
    | action i =>
      cases i with
      | zero => exact .inl (Option.some.inj hch).symm
      | succ _ => exact absurd hch (by simp [deposit])
    | timedOut _ => exact absurd hch (by simp [deposit])
  | some o =>
    rw [ho] at hch
    cases ch with
    | action i => exact .inl (List.mem_of_getElem? hch)
    | timedOut j =>
      simp only [deposit, Option.bind_eq_some_iff] at hch
      obtain ⟨c, hc, hj⟩ := hch
      exact .inr ⟨o, c, rfl, hc, List.mem_of_getElem? hj⟩

/-- A deposit that is an output branch marks exactly that branch's places, and one that is a
timeout outcome equals itself per place: the list reading implies the outcome line. -/
theorem core036_outcome_of_list {t : Trans N} {c : N → Nat} {d : List N}
    (h : OutputBranch t d ∨ TimeoutOutcome t c d) : core036_outcome t c d :=
  h.elim (fun hb => .inl ⟨d, hb, fun _ => Iff.rfl⟩) (fun ht => .inr ⟨d, ht, fun _ => rfl⟩)

/-- Every reference deposit satisfies the outcome line. -/
theorem core036_ref_c8 (t : Trans N) (m : N → Nat) (d : List N) (h : core036_refDep t m d) :
    core036_outcome t (Consumes t m) d :=
  core036_outcome_of_list (core036_ref_c8_list t m d h)

omit [DecidableEq N] in
/-- A place is in the produced set of a deposit exactly when the deposit puts a token in it. -/
theorem core036_produced_iff [DecidableEq N] (d : List N) (p : N) :
    Produced d p ↔ Deposits d p ≠ 0 := by
  simp [Produced, Deposits, depProd, List.count_eq_zero]

/-- The outcome line reads a deposit only per place: two deposits that put the same number of
tokens in every place satisfy it alike, whatever their order (the tenth sentence, AC3). -/
theorem core036_c8_perPlace {t : Trans N} {c : N → Nat} {d d' : List N}
    (h : SamePerPlace d d') : core036_outcome t c d ↔ core036_outcome t c d' := by
  have hp : ∀ p, Produced d p ↔ Produced d' p := fun p => by
    rw [core036_produced_iff, core036_produced_iff, h p]
  unfold core036_outcome OnPlacesOf SamePerPlace
  constructor
  · rintro (⟨b, hb, hs⟩ | ⟨d₀, ht, he⟩)
    · exact .inl ⟨b, hb, fun p => (hp p).symm.trans (hs p)⟩
    · exact .inr ⟨d₀, ht, fun p => (h p).symm.trans (he p)⟩
  · rintro (⟨b, hb, hs⟩ | ⟨d₀, ht, he⟩)
    · exact .inl ⟨b, hb, fun p => (hp p).trans (hs p)⟩
    · exact .inr ⟨d₀, ht, fun p => (h p).trans (he p)⟩

/-- A firing relation closed under per-place equal deposits: `t` fires from `m` with `d` when it
fires under `F` with some `d'` that puts the same number of tokens in every place. -/
def core036_perPlaceClosure (F : FireRel N) : FireRel N :=
  fun t m d m' => ∃ d', SamePerPlace d d' ∧ F t m d' m'

/-- CORE-036 is blind to the order of a deposit: closing a firing relation that satisfies it
under per-place equal deposits keeps it satisfied (the tenth sentence, AC3). -/
theorem core036_perPlace_closed (F : FireRel N) (h : CORE_036 F) :
    CORE_036 (core036_perPlaceClosure F) := by
  intro t
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h t
  have back : ∀ m m', Fire (core036_perPlaceClosure F) t m m' → Fire F t m m' :=
    fun _ _ ⟨_, d', _, hf⟩ => ⟨d', hf⟩
  refine ⟨fun p c hpc m m' hf => h1 p c hpc m m' (back m m' hf),
    fun p hp m m' hf => h2 p hp m m' (back m m' hf),
    fun p hp m m' hf => h3 p hp m m' (back m m' hf),
    fun hb m hen => ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨m', d, hf⟩ := h4 hb m hen
    exact ⟨m', d, d, fun _ => rfl, hf⟩
  · rintro d p c hpc hr m m' ⟨d', he, hf⟩
    rw [he p]; exact h5 d' p c hpc hr m m' hf
  · rintro d p hpc hr m m' ⟨d', he, hf⟩
    rw [he p]; exact h6 d' p hpc hr m m' hf
  · rintro d p hr m m' ⟨d', he, hf⟩
    rw [he p]; exact h7 d' p hr m m' hf
  · rintro d m m' ⟨d', he, hf⟩
    exact (core036_c8_perPlace he).2 (h8 d' m m' hf)

/-- The reference always has a deposit. -/
theorem core036_ref_dep (t : Trans N) (m : N → Nat) : ∃ d, core036_refDep t m d := by
  obtain ⟨ch, d, h⟩ := exists_deposit (Consumes t m) (OutputSpec t)
  exact ⟨d, ch, h⟩

end Models

/-- The reference semantics satisfies CORE-036: `Seam.enabledNA` is the conjunction of the
three token requirements and nothing else, every enabled transition has a deposit
(`exists_deposit`), `Seam.fireNC` subtracts `Seam.nconsumed` (the consumption count of the input
arc, 0 elsewhere) from a non-reset place and sets a reset place to the deposit, and every
deposit is an output branch or a timeout outcome. -/
@[evidence holds CORE_036]
theorem CORE_036_reference {N : Type} [DecidableEq N] : CORE_036 (RefFire (N := N)) := by
  rw [core036_refFire_eq]
  intro t
  exact ⟨core036_c1_of (fun t m h => ((core036_enabled_iff t m).1 h).1) t,
    core036_c2_of (fun t m h => ((core036_enabled_iff t m).1 h).2.2) t,
    core036_c3_of (fun t m h => ((core036_enabled_iff t m).1 h).2.1) t,
    core036_c4_of (fun _ _ h => h) core036_ref_dep t,
    core036_c5_of core036_ref_c5 t, core036_c6_of core036_ref_c6 t,
    core036_c7_of (fun _ _ h => h) t, core036_c8_of core036_ref_c8 t⟩

/-! ### Examples over one-transition nets on `Nat` -/

/-- A transition with the given arcs and output spec. -/
def core036_t (inputs : List (NInSpec Nat)) (inh rd rs : List Nat) (out : Option (Out Nat)) :
    Trans Nat :=
  { core := { name := "t", inputs := inputs, inhibitors := inh, reads := rd, resets := rs },
    out := out }

/-- One input arc `One` on place `0`. -/
def core036_tIn : Trans Nat := core036_t [⟨0, .one⟩] [] [] [] none

/-- One read arc on place `0`. -/
def core036_tRd : Trans Nat := core036_t [] [] [0] [] none

/-- One inhibitor arc on place `0`. -/
def core036_tIh : Trans Nat := core036_t [] [0] [] [] none

/-- One reset arc on place `0`. -/
def core036_tRs : Trans Nat := core036_t [] [] [] [0] none

/-- No arcs at all, no output spec. -/
def core036_tNone : Trans Nat := core036_t [] [] [] [] none

/-- One output arc to place `0`. -/
def core036_tOut : Trans Nat := core036_t [] [] [] [] (some (.place 0))

/-- The marking in which every place holds `k` tokens. -/
def core036_const (k : Nat) : Nat → Nat := fun _ => k

/-! ### One mutant per clause

Each mutant drops one clause; each killing model changes exactly one ingredient of the
reference model, so it keeps the other seven clauses and breaks the dropped one. -/

/-- The reference model with the gate replaced. -/
def core036_gated (g : Trans Nat → (Nat → Nat) → Prop) : FireRel Nat :=
  core036_model g core036_refDep (·.core)

/-- The reference model with the effect core replaced. -/
def core036_effect (k : Trans Nat → NTransition Nat) : FireRel Nat :=
  core036_model Enabled core036_refDep k

/-- Mutant reading that drops line 1 (input places gate). -/
def CORE_036_mutant_dropInputGate {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t, core036_c2 F t ∧ core036_c3 F t ∧ core036_c4 F t ∧ core036_c5 F t ∧ core036_c6 F t ∧
    core036_c7 F t ∧ core036_c8 F t

/-- Firing that ignores input arcs when deciding whether a transition fires. -/
def core036_ignoresInputsFire : FireRel Nat :=
  core036_gated (fun t m => core036_ihOk t m ∧ core036_rdOk t m)

/-- ✗ Ignoring the input requirement violates CORE-036 (line 1): `core036_tIn` fires from the
empty marking. -/
@[evidence forbids CORE_036]
theorem CORE_036_forbids_ignoresInputs : ¬ CORE_036 core036_ignoresInputsFire := by
  intro h
  refine (h core036_tIn).1 0 .one ⟨⟨0, .one⟩, rfl, rfl⟩ (core036_const 0) _
    ⟨[], ⟨by decide, by decide⟩, ⟨.action 0, rfl⟩, rfl⟩ (by decide)

/-- The input-ignoring firing kills the mutant that drops line 1. -/
@[evidence mutant CORE_036]
theorem CORE_036_mutant_dropInputGate_killed :
    CORE_036_mutant_dropInputGate core036_ignoresInputsFire ∧
      ¬ CORE_036 core036_ignoresInputsFire :=
  ⟨fun t => ⟨core036_c2_of (fun _ _ h => h.2) t, core036_c3_of (fun _ _ h => h.1) t,
    core036_c4_of (fun t m h => ⟨((core036_enabled_iff t m).1 h).2.1,
      ((core036_enabled_iff t m).1 h).2.2⟩) core036_ref_dep t,
    core036_c5_of core036_ref_c5 t, core036_c6_of core036_ref_c6 t,
    core036_c7_of (fun _ _ h => h) t, core036_c8_of core036_ref_c8 t⟩,
   CORE_036_forbids_ignoresInputs⟩

/-- Mutant reading that drops line 2 (read places gate). -/
def CORE_036_mutant_dropReadGate {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t, core036_c1 F t ∧ core036_c3 F t ∧ core036_c4 F t ∧ core036_c5 F t ∧ core036_c6 F t ∧
    core036_c7 F t ∧ core036_c8 F t

/-- Firing that ignores read arcs when deciding whether a transition fires. -/
def core036_ignoresReadsFire : FireRel Nat :=
  core036_gated (fun t m => core036_inOk t m ∧ core036_ihOk t m)

/-- The read-ignoring firing kills the mutant that drops line 2: `core036_tRd` fires from the
empty marking. -/
@[evidence mutant CORE_036]
theorem CORE_036_mutant_dropReadGate_killed :
    CORE_036_mutant_dropReadGate core036_ignoresReadsFire ∧
      ¬ CORE_036 core036_ignoresReadsFire := by
  refine ⟨fun t => ⟨core036_c1_of (fun _ _ h => h.1) t, core036_c3_of (fun _ _ h => h.2) t,
    core036_c4_of (fun t m h => ⟨((core036_enabled_iff t m).1 h).1,
      ((core036_enabled_iff t m).1 h).2.1⟩) core036_ref_dep t,
    core036_c5_of core036_ref_c5 t, core036_c6_of core036_ref_c6 t,
    core036_c7_of (fun _ _ h => h) t, core036_c8_of core036_ref_c8 t⟩, fun h => ?_⟩
  exact (h core036_tRd).2.1 0 (by decide) (core036_const 0) _
    ⟨[], ⟨by decide, by decide⟩, ⟨.action 0, rfl⟩, rfl⟩ (by decide)

/-- Mutant reading that drops line 3 (inhibitor places gate). -/
def CORE_036_mutant_dropInhibitorGate {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t, core036_c1 F t ∧ core036_c2 F t ∧ core036_c4 F t ∧ core036_c5 F t ∧ core036_c6 F t ∧
    core036_c7 F t ∧ core036_c8 F t

/-- Firing that ignores inhibitor arcs when deciding whether a transition fires. -/
def core036_ignoresInhibitorsFire : FireRel Nat :=
  core036_gated (fun t m => core036_inOk t m ∧ core036_rdOk t m)

/-- The inhibitor-ignoring firing kills the mutant that drops line 3: `core036_tIh` fires from
the marking in which every place holds a token. -/
@[evidence mutant CORE_036]
theorem CORE_036_mutant_dropInhibitorGate_killed :
    CORE_036_mutant_dropInhibitorGate core036_ignoresInhibitorsFire ∧
      ¬ CORE_036 core036_ignoresInhibitorsFire := by
  refine ⟨fun t => ⟨core036_c1_of (fun _ _ h => h.1) t, core036_c2_of (fun _ _ h => h.2) t,
    core036_c4_of (fun t m h => ⟨((core036_enabled_iff t m).1 h).1,
      ((core036_enabled_iff t m).1 h).2.2⟩) core036_ref_dep t,
    core036_c5_of core036_ref_c5 t, core036_c6_of core036_ref_c6 t,
    core036_c7_of (fun _ _ h => h) t, core036_c8_of core036_ref_c8 t⟩, fun h => ?_⟩
  exact (h core036_tIh).2.2.1 0 (by decide) (core036_const 1) _
    ⟨[], ⟨by decide, by decide⟩, ⟨.action 0, rfl⟩, rfl⟩ (by decide)

/-- Mutant reading that drops line 4 (an enabled transition can fire). -/
def CORE_036_mutant_dropCanFire {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t, core036_c1 F t ∧ core036_c2 F t ∧ core036_c3 F t ∧ core036_c5 F t ∧ core036_c6 F t ∧
    core036_c7 F t ∧ core036_c8 F t

/-- The firing relation in which nothing ever fires. -/
def core036_neverFire : FireRel Nat := core036_gated (fun _ _ => False)

/-- ✗ A transition that never fires violates CORE-036 (line 4): `core036_tNone` has no arcs, so
it builds and is enabled at every marking. -/
@[evidence forbids CORE_036]
theorem CORE_036_forbids_never : ¬ CORE_036 core036_neverFire := by
  intro h
  obtain ⟨_, _, hf, -⟩ := (h core036_tNone).2.2.2.1 (by decide) (core036_const 0) (by decide)
  exact hf

/-- The never-firing relation kills the mutant that drops line 4: every other clause is a
universal statement over firings, so it holds of the empty relation. -/
@[evidence mutant CORE_036]
theorem CORE_036_mutant_dropCanFire_killed :
    CORE_036_mutant_dropCanFire core036_neverFire ∧ ¬ CORE_036 core036_neverFire :=
  ⟨fun t => ⟨core036_c1_of (fun _ _ h => h.elim) t, core036_c2_of (fun _ _ h => h.elim) t,
    core036_c3_of (fun _ _ h => h.elim) t,
    core036_c5_of core036_ref_c5 t, core036_c6_of core036_ref_c6 t,
    core036_c7_of (fun _ _ h => h) t, core036_c8_of core036_ref_c8 t⟩,
   CORE_036_forbids_never⟩

/-- Mutant reading that drops line 5 (input places consume). -/
def CORE_036_mutant_dropConsume {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t, core036_c1 F t ∧ core036_c2 F t ∧ core036_c3 F t ∧ core036_c4 F t ∧ core036_c6 F t ∧
    core036_c7 F t ∧ core036_c8 F t

/-- The transition core with its input arcs removed. -/
def core036_kNoConsume (t : Trans Nat) : NTransition Nat := { t.core with inputs := [] }

/-- Firing whose effect consumes from no input place. -/
def core036_noConsumeFire : FireRel Nat := core036_effect core036_kNoConsume

/-- ✗ Input arcs that consume nothing violate CORE-036 (line 5): `core036_tIn` fires from the
marking with one token on place `0` and leaves it there. -/
@[evidence forbids CORE_036]
theorem CORE_036_forbids_noConsume : ¬ CORE_036 core036_noConsumeFire := by
  intro h
  have := (h core036_tIn).2.2.2.2.1 [] 0 .one ⟨⟨0, .one⟩, rfl, rfl⟩ (by decide)
    (core036_const 1) _ ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
  exact absurd this (by decide)

/-- The non-consuming firing kills the mutant that drops line 5. -/
@[evidence mutant CORE_036]
theorem CORE_036_mutant_dropConsume_killed :
    CORE_036_mutant_dropConsume core036_noConsumeFire ∧ ¬ CORE_036 core036_noConsumeFire :=
  ⟨fun t => ⟨core036_c1_of (k := core036_kNoConsume) (fun t m h => ((core036_enabled_iff t m).1 h).1) t,
    core036_c2_of (k := core036_kNoConsume) (fun t m h => ((core036_enabled_iff t m).1 h).2.2) t,
    core036_c3_of (k := core036_kNoConsume) (fun t m h => ((core036_enabled_iff t m).1 h).2.1) t,
    core036_c4_of (k := core036_kNoConsume) (fun _ _ h => h) core036_ref_dep t,
    core036_c6_of (k := core036_kNoConsume) (fun _ _ _ _ hr => ⟨hr, rfl⟩) t,
    core036_c7_of (k := core036_kNoConsume) (fun _ _ h => h) t, core036_c8_of core036_ref_c8 t⟩,
   CORE_036_forbids_noConsume⟩

/-- Mutant reading that drops line 6 (no other arc consumes). -/
def CORE_036_mutant_dropNoConsume {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t, core036_c1 F t ∧ core036_c2 F t ∧ core036_c3 F t ∧ core036_c4 F t ∧ core036_c5 F t ∧
    core036_c7 F t ∧ core036_c8 F t

/-- The transition core with a `One` input arc appended for every read arc. -/
def core036_kReadConsumes (t : Trans Nat) : NTransition Nat :=
  { t.core with inputs := t.core.inputs ++ t.core.reads.map (fun p => ⟨p, .one⟩) }

/-- Firing whose effect also consumes one token through every read arc (as an extra `One` input
arc after the real ones). -/
def core036_readConsumesFire : FireRel Nat := core036_effect core036_kReadConsumes

/-- ✗ A read arc that consumes violates CORE-036 (line 6): `core036_tRd` fires from the marking
with one token on place `0` and takes it. -/
@[evidence forbids CORE_036]
theorem CORE_036_forbids_readConsumes : ¬ CORE_036 core036_readConsumesFire := by
  intro h
  have := (h core036_tRd).2.2.2.2.2.1 [] 0 (fun c ⟨_, hs, _⟩ => by simp [nspecAt,
      core036_tRd, core036_t] at hs) (by decide)
    (core036_const 1) _ ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
  exact absurd this (by decide)

/-- The read-consuming firing kills the mutant that drops line 6: the extra arcs come after the
real input arcs, so `nspecAt` still finds the real arc on every input place. -/
@[evidence mutant CORE_036]
theorem CORE_036_mutant_dropNoConsume_killed :
    CORE_036_mutant_dropNoConsume core036_readConsumesFire ∧
      ¬ CORE_036 core036_readConsumesFire := by
  refine ⟨fun t => ⟨core036_c1_of (k := core036_kReadConsumes) (fun t m h => ((core036_enabled_iff t m).1 h).1) t,
    core036_c2_of (k := core036_kReadConsumes) (fun t m h => ((core036_enabled_iff t m).1 h).2.2) t,
    core036_c3_of (k := core036_kReadConsumes) (fun t m h => ((core036_enabled_iff t m).1 h).2.1) t,
    core036_c4_of (k := core036_kReadConsumes) (fun _ _ h => h) core036_ref_dep t,
    core036_c5_of (k := core036_kReadConsumes) (fun t p c m hpc hr => ?_) t,
    core036_c7_of (k := core036_kReadConsumes) (fun _ _ h => h) t, core036_c8_of core036_ref_c8 t⟩,
    CORE_036_forbids_readConsumes⟩
  obtain ⟨s, hs, hc⟩ := hpc
  refine ⟨hr, ?_⟩
  have : nspecAt (core036_kReadConsumes t) p = some s := by
    simp only [nspecAt, core036_kReadConsumes, List.find?_append] at hs ⊢
    rw [hs]; rfl
  simp only [nconsumed, this, consumptionCount, hc]

/-- Mutant reading that drops line 7 (reset places end with the deposit). -/
def CORE_036_mutant_dropReset {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t, core036_c1 F t ∧ core036_c2 F t ∧ core036_c3 F t ∧ core036_c4 F t ∧ core036_c5 F t ∧
    core036_c6 F t ∧ core036_c8 F t

/-- The transition core with its reset arcs removed. -/
def core036_kNoReset (t : Trans Nat) : NTransition Nat := { t.core with resets := [] }

/-- Firing whose effect resets nothing. -/
def core036_noResetFire : FireRel Nat := core036_effect core036_kNoReset

/-- The non-resetting firing kills the mutant that drops line 7: `core036_tRs` fires from the
marking with one token on place `0` and leaves it there. -/
@[evidence mutant CORE_036]
theorem CORE_036_mutant_dropReset_killed :
    CORE_036_mutant_dropReset core036_noResetFire ∧ ¬ CORE_036 core036_noResetFire := by
  refine ⟨fun t => ⟨core036_c1_of (k := core036_kNoReset) (fun t m h => ((core036_enabled_iff t m).1 h).1) t,
    core036_c2_of (k := core036_kNoReset) (fun t m h => ((core036_enabled_iff t m).1 h).2.2) t,
    core036_c3_of (k := core036_kNoReset) (fun t m h => ((core036_enabled_iff t m).1 h).2.1) t,
    core036_c4_of (k := core036_kNoReset) (fun _ _ h => h) core036_ref_dep t,
    core036_c5_of (k := core036_kNoReset) (fun t p c m hpc hr => ⟨List.not_mem_nil, (core036_ref_c5 t p c m hpc hr).2⟩) t,
    core036_c6_of (k := core036_kNoReset) (fun t p m hpc hr => ⟨List.not_mem_nil, (core036_ref_c6 t p m hpc hr).2⟩) t,
    core036_c8_of core036_ref_c8 t⟩, fun h => ?_⟩
  have := (h core036_tRs).2.2.2.2.2.2.1 [] 0 (by decide)
    (core036_const 1) _ ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
  exact absurd this (by decide)

/-- Mutant reading that drops line 8 (the deposit is an outcome of the output spec). -/
def CORE_036_mutant_dropOutcome {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t, core036_c1 F t ∧ core036_c2 F t ∧ core036_c3 F t ∧ core036_c4 F t ∧ core036_c5 F t ∧
    core036_c6 F t ∧ core036_c7 F t

/-- The deposits of a firing that never deposits anything. -/
def core036_depNone (_ : Trans Nat) (_ : Nat → Nat) (d : List Nat) : Prop := d = []

/-- Firing that never deposits anything. -/
def core036_noOutputFire : FireRel Nat := core036_model Enabled core036_depNone (·.core)

/-- ✗ An output arc that produces nothing violates CORE-036 (line 8): `core036_tOut` fires and
deposits nothing, which marks none of the places of its one output branch `[0]`, and it has no
timeout outcome. -/
@[evidence forbids CORE_036]
theorem CORE_036_forbids_noOutput : ¬ CORE_036 core036_noOutputFire := by
  intro h
  have := (h core036_tOut).2.2.2.2.2.2.2 [] (core036_const 0) _ ⟨by decide, rfl, rfl⟩
  rcases this with ⟨b, hb, hs⟩ | ⟨d₀, ⟨o, c, ho, hc, -⟩, -⟩
  · simp only [OutputBranch, core036_tOut, core036_t, Out.branches, List.mem_singleton] at hb
    subst hb
    exact absurd ((hs 0).2 (by simp)) (by simp [Produced])
  · simp only [core036_tOut, core036_t, Option.some.injEq] at ho
    subst ho
    exact absurd hc (by simp [Out.findTimeout])

/-- The non-producing firing kills the mutant that drops line 8. -/
@[evidence mutant CORE_036]
theorem CORE_036_mutant_dropOutcome_killed :
    CORE_036_mutant_dropOutcome core036_noOutputFire ∧ ¬ CORE_036 core036_noOutputFire :=
  ⟨fun t => ⟨core036_c1_of (fun t m h => ((core036_enabled_iff t m).1 h).1) t,
    core036_c2_of (fun t m h => ((core036_enabled_iff t m).1 h).2.2) t,
    core036_c3_of (fun t m h => ((core036_enabled_iff t m).1 h).2.1) t,
    core036_c4_of (dep := core036_depNone) (fun _ _ h => h) (fun _ _ => ⟨[], rfl⟩) t,
    core036_c5_of core036_ref_c5 t, core036_c6_of core036_ref_c6 t,
    core036_c7_of (fun _ _ h => h) t⟩,
   CORE_036_forbids_noOutput⟩

/-! ### Mutant readings of the outcome line

Each weakens one comparison of the outcome line and keeps lines 1 to 7. The killing models are
the reference model with its deposits replaced by everything the weaker reading accepts. -/

/-- The reference model with the deposits replaced keeps lines 1 to 7, as long as it offers
every reference deposit. -/
theorem core036_keeps7 (dep : Trans Nat → (Nat → Nat) → List Nat → Prop)
    (hd : ∀ t m d, core036_refDep t m d → dep t m d) (t : Trans Nat) :
    let F := core036_model Enabled dep (·.core)
    core036_c1 F t ∧ core036_c2 F t ∧ core036_c3 F t ∧ core036_c4 F t ∧ core036_c5 F t ∧
      core036_c6 F t ∧ core036_c7 F t :=
  ⟨core036_c1_of (fun t m h => ((core036_enabled_iff t m).1 h).1) t,
    core036_c2_of (fun t m h => ((core036_enabled_iff t m).1 h).2.2) t,
    core036_c3_of (fun t m h => ((core036_enabled_iff t m).1 h).2.1) t,
    core036_c4_of (fun _ _ h => h) (fun t m => (core036_ref_dep t m).imp (hd t m)) t,
    core036_c5_of core036_ref_c5 t, core036_c6_of core036_ref_c6 t,
    core036_c7_of (fun _ _ h => h) t⟩

/-- The outcome line with "exactly the places of one output branch, each receiving one or more
tokens" weakened to "only places of one output branch": a write to part of a branch passes. -/
def core036_partialOutcome (t : Trans Nat) (consumed : Nat → Nat) (d : List Nat) : Prop :=
  (∃ b, OutputBranch t b ∧ ∀ p, Produced d p → p ∈ b) ∨
  (∃ d₀, TimeoutOutcome t consumed d₀ ∧ SamePerPlace d d₀)

/-- Mutant reading: lines 1 to 7, and the outcome line asking only that the deposited places lie
in one output branch. -/
def CORE_036_mutant_partialBranch (F : FireRel Nat) : Prop :=
  ∀ t, core036_c1 F t ∧ core036_c2 F t ∧ core036_c3 F t ∧ core036_c4 F t ∧ core036_c5 F t ∧
    core036_c6 F t ∧ core036_c7 F t ∧
    ∀ d, on (fun m m' => F t m d m'), shall (fun m _ => core036_partialOutcome t (Consumes t m) d)

/-- Firing that deposits any write the partial reading accepts. -/
def core036_partialFire : FireRel Nat :=
  core036_model Enabled (fun t m d => core036_partialOutcome t (Consumes t m) d) (·.core)

/-- `t: → and(0, 1)`, no input arcs. -/
def core036_tAnd : Trans Nat := core036_t [] [] [] [] (some (.and (.place 0) (.place 1)))

/-- The partial-write firing kills the partial-branch mutant: `core036_tAnd` fires with the
write `[0]`, which lies inside its one output branch `[0, 1]` but does not mark `1`. -/
@[evidence mutant CORE_036]
theorem CORE_036_mutant_partialBranch_killed :
    CORE_036_mutant_partialBranch core036_partialFire ∧ ¬ CORE_036 core036_partialFire := by
  refine ⟨fun t => ?_, fun h => ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
      core036_keeps7 (fun t m d => core036_partialOutcome t (Consumes t m) d)
        (fun t m d hd => (core036_ref_c8 t m d hd).imp
          (fun ⟨b, hb, hs⟩ => ⟨b, hb, fun p hp => (hs p).1 hp⟩) id) t
    exact ⟨h1, h2, h3, h4, h5, h6, h7, fun d m m' ⟨_, hd, _⟩ => hd⟩
  · have hf : core036_partialFire core036_tAnd (core036_const 0) [0] _ :=
      ⟨by decide, .inl ⟨[0, 1], by simp [OutputBranch, core036_tAnd, core036_t, Out.branches,
        cross], fun p hp => by simp_all [Produced]⟩, rfl⟩
    rcases (h core036_tAnd).2.2.2.2.2.2.2 [0] _ _ hf with ⟨b, hb, hs⟩ | ⟨d₀, ⟨o, c, ho, hc, -⟩, -⟩
    · simp only [OutputBranch, core036_tAnd, core036_t, Out.branches, cross] at hb
      simp at hb
      subst hb
      exact absurd ((hs 1).2 (by simp)) (by simp [Produced])
    · simp only [core036_tAnd, core036_t, Option.some.injEq] at ho
      subst ho
      exact absurd hc (by simp [Out.findTimeout])

/-- The outcome line with the timeout outcome compared by places rather than per place: a
deposit that marks the places of a timeout outcome, with other counts, passes. -/
def core036_timeoutByPlaces (t : Trans Nat) (consumed : Nat → Nat) (d : List Nat) : Prop :=
  (∃ b, OutputBranch t b ∧ OnPlacesOf d b) ∨
  (∃ d₀, TimeoutOutcome t consumed d₀ ∧ ∀ p, Produced d p ↔ Produced d₀ p)

/-- Mutant reading: lines 1 to 7, and the outcome line comparing a timeout outcome by places
only. -/
def CORE_036_mutant_timeoutByPlaces (F : FireRel Nat) : Prop :=
  ∀ t, core036_c1 F t ∧ core036_c2 F t ∧ core036_c3 F t ∧ core036_c4 F t ∧ core036_c5 F t ∧
    core036_c6 F t ∧ core036_c7 F t ∧
    ∀ d, on (fun m m' => F t m d m'), shall (fun m _ => core036_timeoutByPlaces t (Consumes t m) d)

/-- Firing that deposits any write the by-places reading accepts. -/
def core036_timeoutByPlacesFire : FireRel Nat :=
  core036_model Enabled (fun t m d => core036_timeoutByPlaces t (Consumes t m) d) (·.core)

/-- `t: All(2) → and(0, Timeout(ForwardInput(2, 1)))`: its one output branch is `[0, 1]`, and
its timeout outcome forwards every token consumed from `2` into `1`. -/
def core036_tFwd : Trans Nat :=
  core036_t [⟨2, .all⟩] [] [] [] (some (.and (.place 0) (.timeout (.forward 2 1))))

/-- The marking with two tokens in place `2` and none elsewhere. -/
def core036_two : Nat → Nat := fun n => if n = 2 then 2 else 0

/-- The by-places firing kills the timeout-by-places mutant: `core036_tFwd` consumes two tokens
from `2`, so its timeout outcome is `[1, 1]`; the deposit `[1]` marks the same places with one
token fewer, and it is not an output branch either. -/
@[evidence mutant CORE_036]
theorem CORE_036_mutant_timeoutByPlaces_killed :
    CORE_036_mutant_timeoutByPlaces core036_timeoutByPlacesFire ∧
      ¬ CORE_036 core036_timeoutByPlacesFire := by
  refine ⟨fun t => ?_, fun h => ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
      core036_keeps7 (fun t m d => core036_timeoutByPlaces t (Consumes t m) d)
        (fun t m d hd => (core036_ref_c8 t m d hd).imp id
          (fun ⟨d₀, ht, he⟩ => ⟨d₀, ht, fun p => by
            rw [core036_produced_iff, core036_produced_iff, he p]⟩)) t
    exact ⟨h1, h2, h3, h4, h5, h6, h7, fun d m m' ⟨_, hd, _⟩ => hd⟩
  · have hc : Consumes core036_tFwd core036_two 2 = 2 := by decide
    have hto : TimeoutOutcome core036_tFwd (Consumes core036_tFwd core036_two) [1, 1] :=
      ⟨_, _, rfl, rfl, by simp [Out.timeoutDeposits, hc]⟩
    have hf : core036_timeoutByPlacesFire core036_tFwd core036_two [1] _ :=
      ⟨by decide, .inr ⟨[1, 1], hto, fun p => by simp [Produced]⟩, rfl⟩
    rcases (h core036_tFwd).2.2.2.2.2.2.2 [1] _ _ hf with ⟨b, hb, hs⟩ | ⟨d₀, ht, he⟩
    · simp only [OutputBranch, core036_tFwd, core036_t, Out.branches, cross] at hb
      simp at hb
      subst hb
      exact absurd ((hs 0).2 (by simp)) (by simp [Produced])
    · obtain ⟨o, c, ho, hc', hd⟩ := ht
      simp only [core036_tFwd, core036_t, Option.some.injEq] at ho
      subst ho
      simp only [Out.findTimeout, Option.none_or, Option.some.injEq] at hc'
      subst hc'
      simp only [Out.timeoutDeposits, List.mem_singleton, hc] at hd
      subst hd
      exact absurd (he 1) (by decide)

/-! ### What the outcome line allows (AC2, AC3) -/

/-- Firing that deposits every write the outcome line accepts: several tokens into one place of
an output branch included, in any order. It is the executor of IO-015 with output validation
enabled, at token-count granularity. -/
def core036_writeFire : FireRel Nat :=
  core036_model Enabled (fun t m d => core036_outcome t (Consumes t m) d) (·.core)

/-- `t: a → and(b, c)` with `a = 0`, `b = 1`, `c = 2`. -/
def core036_tBC : Trans Nat := core036_t [⟨0, .one⟩] [] [] [] (some (.and (.place 1) (.place 2)))

/-- One token in `a`, none elsewhere. -/
def core036_srcA : Nat → Nat := fun n => if n = 0 then 1 else 0

/-- The marking the write `b, b, c` of `core036_tBC` leaves from `core036_srcA`. -/
def core036_dstBC : Nat → Nat := fireNC core036_srcA core036_tBC.core (depProd [1, 1, 2])

/-- ✓ CORE-036 allows an action to write two tokens into one place of its output branch, in
either order (AC2, AC3): it holds of `core036_writeFire`, under which `t: a → and(b, c)` fires
with the write `b, b, c` and with `c, b, b` to the same marking, 2 tokens in `b` and 1 in `c`,
although neither write is an output branch as a list. -/
@[evidence allows CORE_036]
theorem CORE_036_allows_multi :
    CORE_036 core036_writeFire ∧
      core036_writeFire core036_tBC core036_srcA [1, 1, 2] core036_dstBC ∧
      core036_writeFire core036_tBC core036_srcA [2, 1, 1] core036_dstBC ∧
      core036_dstBC 1 = 2 ∧ core036_dstBC 2 = 1 ∧ core036_dstBC 0 = 0 ∧
      ¬ OutputBranch core036_tBC [1, 1, 2] ∧ ¬ OutputBranch core036_tBC [2, 1, 1] := by
  have hb : OutputBranch core036_tBC [1, 2] := by
    simp [OutputBranch, core036_tBC, core036_t, Out.branches, cross]
  refine ⟨fun t => ?_, ⟨by decide, .inl ⟨[1, 2], hb, fun p => by simp [Produced]⟩, rfl⟩,
    ⟨by decide, .inl ⟨[1, 2], hb, fun p => by simp [Produced]; omega⟩, ?_⟩,
    by decide, by decide, by decide, ?_, ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
      core036_keeps7 (fun t m d => core036_outcome t (Consumes t m) d) core036_ref_c8 t
    exact ⟨h1, h2, h3, h4, h5, h6, h7, fun d m m' ⟨_, hd, _⟩ => hd⟩
  · have hp : depProd [2, 1, 1] = depProd (N := Nat) [1, 1, 2] :=
      funext fun n => List.Perm.count_eq (by decide) n
    simp only [core036_dstBC, hp]
  · simp [OutputBranch, core036_tBC, core036_t, Out.branches, cross]
  · simp [OutputBranch, core036_tBC, core036_t, Out.branches, cross]

/-! ### Non-vacuity -/

/-- The transition of the non-vacuity example: one arc of each kind. Input `One` on place `0`,
read on `1`, inhibitor on `2`, reset on `3`, output to `4`. -/
def core036_tAll : Trans Nat := core036_t [⟨0, .one⟩] [2] [1] [3] (some (.place 4))

/-- The source marking: input, read and reset places hold a token (the reset place two), the
inhibitor and output places none. -/
def core036_src : Nat → Nat := fun n =>
  if n = 0 then 1 else if n = 1 then 1 else if n = 3 then 2 else 0

/-- The marking the reference firing of `core036_tAll` from `core036_src` leaves. -/
def core036_dst : Nat → Nat := fireNC core036_src core036_tAll.core (depProd [4])

/-- Every line of CORE-036 is exercised by the reference semantics: `core036_tAll` has one arc
of each kind and is enabled at `core036_src`; it fires there (line 4), depositing its one output
branch `[4]` (line 8), consuming the input token (line 5), leaving the read token (line 6),
emptying the reset place (line 7) and producing on the output place; and it does not fire once
the input place is emptied (line 1), the read place is emptied (line 2) or the inhibitor place
is marked (line 3). -/
@[evidence nonvacuous CORE_036]
theorem CORE_036_nonvacuous :
    InputArc core036_tAll 0 .one ∧ ReadArc core036_tAll 1 ∧ InhibitorArc core036_tAll 2 ∧
      ResetArc core036_tAll 3 ∧ OutputArc core036_tAll 4 ∧
      Enabled core036_tAll core036_src ∧ RefFire core036_tAll core036_src [4] core036_dst ∧
      OutputBranch core036_tAll [4] ∧
      core036_dst 0 = 0 ∧ core036_dst 1 = 1 ∧ core036_dst 2 = 0 ∧ core036_dst 3 = 0 ∧
      core036_dst 4 = 1 ∧
      (∀ m', ¬ Fire RefFire core036_tAll (fun n => if n = 0 then 0 else core036_src n) m') ∧
      (∀ m', ¬ Fire RefFire core036_tAll (fun n => if n = 1 then 0 else core036_src n) m') ∧
      (∀ m', ¬ Fire RefFire core036_tAll (fun n => if n = 2 then 1 else core036_src n) m') := by
  refine ⟨⟨⟨0, .one⟩, rfl, rfl⟩, by decide, by decide, by decide,
    ⟨.place 4, rfl, by simp [outPlaces]⟩, by decide, ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩,
    by simp [OutputBranch, core036_tAll, core036_t, Out.branches], by decide, by decide,
    by decide, by decide, by decide, ?_, ?_, ?_⟩ <;>
  · rintro m' ⟨d, hen, -⟩
    exact absurd hen (by decide)

/-! ### Transitions that build (the eleventh sentence) -/

/-- **Not the reference semantics.** The reference firings of the transitions that build, and
no firing at all of a definition the build rejects: the runtimes' reading at token-count
granularity, since no executor holds a rejected definition. -/
def core036_refFireBuilt {N : Type} [DecidableEq N] : FireRel N :=
  fun t m d m' => Builds t ∧ RefFire t m d m'

/- The reference restricted to transitions that build is the witness model of CORE-036's
second `holds` theorem. -/
#spec_witness core036_refFireBuilt

/-- ✓ CORE-036 holds of the reference restricted to transitions that build
(`core036_refFireBuilt`): it only removes firings from the reference, so lines 1 to 3 and 5 to 8
are the reference's, and line 4 asks a firing only of a transition that builds, which keeps every
reference firing. Without the `Builds t` premise line 4 would demand a firing of an enabled
definition the build rejects, which the eleventh sentence says never fires, and would reject this
relation. -/
@[evidence holds CORE_036]
theorem CORE_036_builtOnly {N : Type} [DecidableEq N] :
    CORE_036 (core036_refFireBuilt (N := N)) := by
  intro t
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := (CORE_036_reference (N := N)) t
  have back : ∀ m m', Fire core036_refFireBuilt t m m' → Fire RefFire t m m' :=
    fun _ _ ⟨d, hf⟩ => ⟨d, hf.2⟩
  refine ⟨fun p c hp m m' hf => h1 p c hp m m' (back m m' hf),
    fun p hp m m' hf => h2 p hp m m' (back m m' hf),
    fun p hp m m' hf => h3 p hp m m' (back m m' hf), fun hb m hen => ?_,
    fun d p c hp hr m m' hf => h5 d p c hp hr m m' hf.2,
    fun d p hp hr m m' hf => h6 d p hp hr m m' hf.2,
    fun d p hp m m' hf => h7 d p hp m m' hf.2, fun d m m' hf => h8 d m m' hf.2⟩
  obtain ⟨m', d, hf⟩ := h4 hb m hen
  exact ⟨m', d, hb, hf⟩

/-! ### What the outcome line loses -/

/-- `t: All(2) → Timeout(ForwardInput(2, 1))`: its only output branch is the Timeout child's
places `[1]`, and its timeout outcome forwards every token consumed from `2` into `1`. -/
def core036_tFwdOnly : Trans Nat :=
  core036_t [⟨2, .all⟩] [] [] [] (some (.timeout (.forward 2 1)))

/-- The case the assumes names: the outcome line accepts the deposit `[1]` of
`core036_tFwdOnly` after it consumed two tokens from `2` (forwarding only the first consumed
token, which IO-014 forbids), because `[1]` marks exactly the places of the output branch `[1]`;
the timeout outcome is `[1, 1]`. A firing relation does not record that the firing ended with the
timeout outcome, so the ninth sentence's per-place count for it is IO-013's and IO-014's, stated
over the timed-out firings. -/
theorem core036_fwdFirst_accepted :
    core036_outcome core036_tFwdOnly (Consumes core036_tFwdOnly core036_two) [1] ∧
      TimeoutOutcome core036_tFwdOnly (Consumes core036_tFwdOnly core036_two) [1, 1] ∧
      ¬ SamePerPlace [1] [1, 1] := by
  have hc : Consumes core036_tFwdOnly core036_two 2 = 2 := by decide
  refine ⟨.inl ⟨[1], by simp [OutputBranch, core036_tFwdOnly, core036_t, Out.branches],
      fun p => by simp [Produced]⟩,
    ⟨_, _, rfl, rfl, by simp [Out.timeoutDeposits, hc]⟩, fun h => absurd (h 1) (by decide)⟩

end Libpetri.Spec
