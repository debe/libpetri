import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.Glossary
import Libpetri.Spec.Text.IO_013

set_option linter.missingDocs true

/-!
# IO-013: Output timeout (`spec/02-input-output-specs.md`)

IO-013 says how a firing that **ends with the timeout outcome** behaves, that an output spec
holds **at most one `Timeout` node** (a second one, nested in the child of the first or beside
it, is rejected when the transition is built), and that the child of that node holds **no `Xor`
node**, so that the timeout outcome deposits one fixed set of places.

The model is a triple. `Build` is the transition builder, read as the message it rejects a
transition with (`none`: the transition builds). `F` is every firing and `T` the firings that
ended with the timeout outcome. A plain firing relation does not record how a firing ended: on
`Xor(Place 0, Timeout(Place 1))` the timeout deposit `[1]` is also the action branch `{1}`, so a
timed-out firing that wrongly deposits the sibling branch `[0]` looks like an ordinary action
firing. The witness triple is `refBuild`, `RefFire` and `refTimeoutOutcomeFire`.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## The model: the builder, and firings that end with the timeout outcome -/

/-- `t`'s output spec has a `Timeout` node. Local to IO-013: not a glossary term. -/
def HasTimeout {N : Type} (t : Trans N) : Prop :=
  ∃ o c, OutputSpec t = some o ∧ o.findTimeout = some c

/-- Firings of `t` that end with an outcome `dep t m d` allows: enabled, the deposit allowed,
and the reference effect. The reference timed-out firings and the mutant executors below are
instances. -/
def timedOutBy {N : Type} [DecidableEq N] (dep : Trans N → (N → Nat) → List N → Prop) :
    FireRel N :=
  fun t m d m' => Enabled t m ∧ dep t m d ∧ m' = fireNC m t.core (depProd d)

/-- **The reference timed-out firings**: the reference firings (`Reference.Fires`) whose outcome
is a `timedOut` choice, the timeout child's forwards counting what the firing consumed. The same
relation as IO-014's `refTimedOutFire`. -/
def refTimeoutOutcomeFire {N : Type} [DecidableEq N] : FireRel N :=
  timedOutBy fun t m d => ∃ j, deposit (Consumes t m) (OutputSpec t) (.timedOut j) = some d

/- The reference timed-out firings are the third witness model of IO-013's `holds` theorem. -/
#spec_witness refTimeoutOutcomeFire

/-! ## IO-013: Output timeout -/

requirement IO_013
  id "IO-013"
  title "Output timeout"
  kind B
  scope "all executors"
  source verbatim "spec/02-input-output-specs.md"
  covers IO_013.s1, IO_013.s2, IO_013.s3, IO_013.s4, IO_013.s5, IO_013.s6, IO_013.s7, IO_013.s8,
        IO_013.s9, IO_013.s10, IO_013.s11
  reading "Let Build be the builder (Build t = none: t builds; Build t = some msg: building t fails with msg), F the firings and T the firings that end with the timeout outcome."
          "For every transition t whose output spec o holds two or more Timeout nodes, building t fails; and if t passes the checks before the output spec (PreOutputChecks: distinct input places, every input arc requiring at least one token, no input arc and read arc on one place) and no output branch of o names a place twice, it fails with the IO-013 message for t and the number of Timeout nodes in o."
          "Every transition that passes every build check (distinct input places, every input arc requiring at least one token, no input arc and read arc on one place, no place twice in one output branch, at most one Timeout node, no Xor node inside the Timeout child, no ForwardInput outside a Timeout child, every forward from an input place, no two output branches claiming one set of places) builds."
          "For every transition t that builds: every firing of t in T is a firing in F, with the same deposit and target marking."
          "For every transition t that builds: every firing of t in T from m deposits, place by place, exactly the tokens of the timeout outcome of t (for what t consumes at m), and nothing else."
          "For every transition t that builds: from every marking m at which t is enabled, every timeout outcome d of t (for what t consumes at m) is the deposit of some firing in T."
          "For every transition t that builds and whose output spec has a Timeout node, every firing of t in F is in T, or has as its produced set exactly the places of one output branch of t."
          "For every transition t whose output spec o holds at most one Timeout node and an Xor node at any depth of that node's child (xorInTimeout), building t fails; and if t passes the checks before the output spec (PreOutputChecks: distinct input places, every input arc requiring at least one token, no input arc and read arc on one place) and no output branch of o names a place twice, it fails with IO-013's Xor message for t (msgXorInTimeout)."
  assumes "The model is the triple (Build, F, T). Build is the transition builder, read as the message building a transition fails with, none when it builds; the reference builder refBuild runs the checks the model can see in the order of the output composition preamble of spec/02-input-output-specs.md. F is the firing relation and T the firings that end with the timeout outcome (glossary: Timeout outcome), each read as one step from a marking to a marking that deposits the tokens of one outcome (glossary: Fire, Deposit); timing and priority play no part. A plain FireRel cannot carry T: on Xor(Place 0, Timeout(Place 1)) the timeout deposit [1] is also the action branch {1}, so a timed-out firing that deposits the sibling branch [0] would look like an action firing. The witness triple is refBuild, RefFire and refTimeoutOutcomeFire."
          "The build error is msgTimeouts, byte for byte: output spec of transition '<t>' has <n> Timeout nodes; an output spec has at most one, nested or not (IO-013), with <n> the number of Timeout nodes in the spec, nested and sibling ones alike (timeoutCount). The preamble's order puts the IO-011 check (a place twice in one output branch) first, so on such a spec the message is IO-011's and the second line only requires that building fails. The preamble does not place the CORE-030 input-arc check, so on a transition with two input arcs on one place the second line likewise only requires that building fails. The timing check of TIME-001, which runs before the output-spec checks (glossary: Build-time checks), is not in the model either: Trans carries no timing interval, so the message lines (second and eighth) are claimed of transitions whose timing passes that check."
          "'On every construction path' is read as: Build is the one builder every construction path goes through (builders, composition, channel merge, fusion), so a transition that a path yields builds exactly when Build accepts it. Which paths exist is not in the model."
          "The third line is the converse that makes 'builds' checkable (AC7's specs that build): a transition passing the checks before the output spec (CORE-030, the IO-002/IO-004 input counts and EXEC-012's input-and-read check, PreOutputChecks) and every build check of the output composition preamble builds. The checks are the glossary terms Builds and WellFormedOut, the build-time checks of IO-011, IO-012, IO-013 and IO-014; checks the model cannot see (AC1's positive duration, a spec that names no place) are outside it. So are the TIME-001 timing check, the NU-020 and NU-054 checks of a match specification and, in an implementation whose places carry token types, the ForwardInput type check IO-014 allows ('An implementation whose places carry run-time token types (Java) *may* also fail building a transition that has a `ForwardInput(from, to)` whose `to` place's token type cannot hold the tokens of `from`.'; Java runs it in ArcDiagnostics.outputSpecError, 'ForwardInput type mismatch'): Trans carries no timing interval, no match specification and no token types, so the line is read on transitions that pass those checks, AC8's accepted Timeout(d, And(A, ForwardInput(i, B))) with B able to hold the tokens of i."
          "A transition that builds has at most one Timeout node, so its timeout outcome is the one Timeout node's child (Out.findTimeout finds it), and that child holds no Timeout node. The firing lines are stated for transitions that build only: a transition building rejects is not a transition of any net (CORE-022) and never fires."
          "The duration is not in the model, so whether the budget expires is nondeterministic: from every marking at which t is enabled, the action may overrun it. Nor is the action (Trans carries none), and only an action that hands control back to the executor before it completes races its budget: EXEC-022 says 'an action that completes before it hands control back, a synchronous action for example, never times out' (Rust's inline run_sync branch of fire_transition_async, and in Java an action that returns an already-completed stage, which the completeOnTimeout of ExecutorSupport.withActionTimeout cannot end). IO-013's unconditional 'if the action does not complete within duration' is narrowed by EXEC-022 to actions that hand control back, and the sixth line is read over the actions a transition may carry: some such action can overrun the budget. The sixth line therefore reads 'if the action does not complete within duration, the firing shall end with the timeout outcome' as 'the timeout outcome is always one of the ways a firing of t can end'. That overrunning forces the timeout, and that completing in time rules it out, are statements about time that a model of untimed steps cannot express."
          "'It is abandoned' is the action's output being excluded, which the fifth line states for the deposit. Whether the action is stopped is the paragraph after 'One fixed timeout deposit' ('Whether the abandoned action is actually stopped is implementation-defined and MUST NOT be relied upon ...'). It constrains what users may rely on and leaves the abandoned action's side effects to the implementation, so it is not encoded."
          "'The marking receives the tokens of child and nothing else' is read at the deposit (fifth line). Which marking a firing leads to is the effect rule of the glossary term Fire (CORE-030, CORE-034, CORE-035); the fourth line ties every timed-out firing to a firing of F, so that rule applies to it. Output the action published mid-action (EXEC-020, IO-015 AC7) is deposited by its publication, not by the firing's end, and stays in the marking when the budget runs out (EXEC-022: 'Output the action published before the budget ran out stays in the marking'). It is outside this one-step model, so 'it shall not deposit any output of the action' and AC5's 'output the action produced before the budget expired' are read as the output the action had not published. Java and TypeScript have no mid-action publication; Rust's flush does, and Python's on it."
          "'The tokens of child' is the glossary term Timeout outcome, as the reference reads it (Out.timeoutDeposits): one token per Place leaf of child, the product at every And, and one token in to per token consumed from from at every ForwardInput (IO-014), counted per place, so the order of the deposit list does not matter (CORE-036). Token values and created_at (the minted tokens of AC3, forwarded values and their stamps, IO-014 AC5) are below the count granularity."
          "The eighth line is the paragraph 'One fixed timeout deposit'. Its message is msgXorInTimeout, byte for byte. Any Xor at any depth of the Timeout child counts, under an And or a ForwardInput's sibling included (hasXor). It runs after the Timeout count check, as the premise timeoutCount o ≤ 1 states: with two Timeout nodes the message is the first line's. The preamble's order puts the IO-011 check before it, so on a spec that names a place twice in one output branch the eighth line only requires that building fails, and on a transition with two input arcs on one place likewise (CORE-030). 'The executor, not the action, makes the deposit' is the reason the markdown gives and is not a separate constraint."
          "'The timeout outcome of a transition that builds therefore deposits in one fixed set of places' is a consequence, not a clause: on a transition that builds the Timeout child holds no Xor node, so Out.timeoutDeposits of the child has one entry and the fifth and sixth lines name one deposit (theorem IO_013_one_fixed_deposit, from the glossary's timeoutOutcome_unique). Without the check the reference offers one timeout outcome per alternative of an Xor in the child (IO_013_reference_xorChild_two_outcomes)."
          "The seventh line is AC5 for a firing that does not report the timeout outcome: it ended with its action, whose produced set is one output branch (IO-015, exact explanation; how many tokens per place is IO-016's). A deposit that merges a timeout outcome with output the action wrote and reports it as an action firing is neither, unless its places happen to form a whole output branch, in which case it is a legal action firing and no observation of the marking can tell the two apart. The line is a requirement on an executor with output validation enabled, the default (CONC-026); F models such an executor, as RefFire does. With the skip enabled an action firing deposits the action's write and the line is not claimed of it. The skip changes nothing on the timeout outcome (CONC-026), so the timed-out lines (fourth to sixth) do not depend on it; every runtime holds them (below)."
          "The timed-out lines in the runtimes. No runtime validates the timeout outcome against the output spec: Rust, and Python on it, skip validation on the timeout path, and Java (BitmapNetExecutor and PrecompiledNetExecutor processCompletedTransitions) and TypeScript (bitmap-net-executor.ts and precompiled-net-executor.ts) skip it, and the IO-016 multiplicity warning, when TransitionContext.isDetachedForTimeout(), running only the NU-054 relay check; so on And(A, Timeout(d, B)), which builds, a timed-out firing deposits B (ruling D24 (a)). An executor that validates the timeout outcome against the whole output spec fails every such timed-out firing and breaks the sixth line, from every enabled marking every timeout outcome is the deposit of some firing in T (io013_validatingFire and io013_validatedTimedOut, IO_013_forbids_validateTimeout; the behaviour RD-01 in spec/runtime-defects.md recorded of Java and TypeScript)."
          "Every runtime deposits the timeout outcome on the places the rewritten output spec names, as given: Java (TransitionContext outputToHarvest and forwardToHarvest, and ExecutorSupport produceTimeoutOutputRecursive, which reads a ForwardInput's from place with rawInput) and TypeScript (transition-context.ts outputToHarvest and forwardToHarvest) take those places as the actual places and do not resolve them through the composition correspondence again, and Rust deposits on them directly. An executor that resolves them a second time, on a correspondence collision (port a bound to b, port b bound to c), deposits the timeout token meant for b on c and breaks the fifth line, the deposit equals the timeout outcome place by place (the behaviour RD-31 recorded of Java and TypeScript). The correspondence is not in this model, whose transition is the rewritten one, so the statement cannot see the second resolution; that wrong executor is shown in MOD_031.lean (mod031ctx_timeout_resolveTwice), and the runtimes are tested on it (java AbstractNetExecutorEngineTest OutputTimeoutTests outTimeout_portCollision_depositsOnTheBoundPlace_MOD031_IO013; typescript tests/core/compose-action-place-alias.test.ts 'the timeout branch deposits on the bound place under a port-name collision')."
          "The sentence 'A firing of a transition with a match specification whose timeout outcome fails the relay check of [NU-054] does not end with the timeout outcome: it fails ([EVT-008]) and deposits none of the tokens of `child`.' is ruling D24 (a) (clash nu-c#8). It narrows the second quote and the sixth line to firings the relay check accepts. Trans carries no match specification, so a transition with one is outside this block, and on every transition here no relay check applies; the exception is stated by NU_054_check (the check) and NU_054_fail (the failed firing deposits nothing of the timeout outcome)."
          "AC1 (duration must be positive) is a build-time validation of the duration, which the model does not carry; not encoded."
          "AC2 (action completes within duration, normal output validation) is the produced-set disjunct of the seventh line; the validation itself is IO-015's subject."
          "AC3 (action exceeds duration, every place the timeout child names receives tokens: one minted token for a Place, the forwarded tokens for a ForwardInput) is the fifth and sixth lines, read on token counts."
          "AC4 (an ActionTimedOut event is emitted on timeout) is an event obligation (EVT-010, whose lines 1 and 3 state it for both emission variants); the firing relation has no events, so it is not encoded here."
          "AC5 (output produced before the budget expired is discarded, the marking receiving the tokens of the timeout child's one fixed set of places and nothing else; a partial write under an Xor sibling is not a second satisfied branch) is the fifth line for a firing in T and the seventh for a firing outside it; 'one fixed set' is IO_013_one_fixed_deposit."
          "AC6 (a TimeoutException the action raises is an ordinary action failure, not the timeout branch) is about which trigger ends the firing; an action failure deposits no outcome (EXEC-030) and is not a firing in this model, so it is not encoded."
          "AC7 is the second and third lines: its three rejected specs (Timeout(d, Timeout(e, P)), Xor(Timeout(d, A), Timeout(e, B)), And(Timeout(d, A), Xor(B, Timeout(e, C)))) fail with the message for n = 2 and its two accepted specs (Xor(A, Timeout(d, B)), Timeout(d, And(A, B))) build, under the reference builder (IO_013_ac7_rejected, IO_013_ac7_builds)."
          "AC8 is the eighth and third lines: its two rejected specs (Timeout(d, Xor(A, B)), Xor(C, Timeout(d, And(A, Xor(B, D))))) fail with the Xor message, and its two accepted specs (Xor(A, Timeout(d, B)) and, with i an input place, Timeout(d, And(A, ForwardInput(i, B)))) build, under the reference builder (IO_013_ac8_rejected, IO_013_ac8_builds)."
          "The test derivation's build cases are AC7's and AC8's; its timing case (an action sleeping past its budget, the event) is outside the model: the duration and the event store are not in it."
          "Ruling D15: the premise PreOutputChecks t (glossary) is the checks the reference builder runs before the output-spec checks: distinct input places ([CORE-030]), input arcs that each require at least one token ([IO-002], [IO-004]) and no input arc and read arc on one place ([EXEC-012]). A transition that fails one of them fails with that check's message, so on it the build lines only require that building fails, as for CORE-030 before the ruling."
  signoff "2026-11-13 729c134068fcb4bc ai"
  statement : ∀ {N : Type} [DecidableEq N], (Trans N → Option String) → FireRel N → FireRel N → Prop :=
    fun Build F T =>
      (∀ t o, OutputSpec t = some o → 2 ≤ timeoutCount o →
        Build t ≠ none ∧ (PreOutputChecks t → ¬ DupBranch o →
          Build t = some (msgTimeouts t (timeoutCount o)))) ∧
      (∀ t, Builds t → Build t = none) ∧
      (∀ t, Build t = none → ∀ d, on (fun m m' => T t m d m'), shall (fun m m' => F t m d m')) ∧
      (∀ t, Build t = none → ∀ d, on (fun m m' => T t m d m'), shall (fun m _ =>
        ∃ d₀, TimeoutOutcome t (Consumes t m) d₀ ∧ ∀ p, Deposits d p = Deposits d₀ p)) ∧
      (∀ t, Build t = none → ∀ m, Enabled t m → ∀ d, TimeoutOutcome t (Consumes t m) d →
        ∃ m', T t m d m') ∧
      (∀ t, Build t = none → HasTimeout t → ∀ d, on (fun m m' => F t m d m'), shall (fun m m' =>
        T t m d m' ∨ ∃ b, OutputBranch t b ∧ ∀ p, Produced d p ↔ p ∈ b)) ∧
      (∀ t o, OutputSpec t = some o → timeoutCount o ≤ 1 → xorInTimeout o = true →
        Build t ≠ none ∧ (PreOutputChecks t → ¬ DupBranch o →
          Build t = some (msgXorInTimeout t)))

/- The pinned readable form of IO-013: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.IO_013 : {N : Type} →
  [DecidableEq N] → (Reference.Trans N → Option String) → FireRel N → FireRel N → Prop :=
fun {N} [DecidableEq N] Build F T =>
  (∀ (t : Reference.Trans N) (o : Out N),
      OutputSpec t = some o →
        2 ≤ timeoutCount o →
          Build t ≠ none ∧ (PreOutputChecks t → ¬DupBranch o → Build t = some (msgTimeouts t (timeoutCount o)))) ∧
    (∀ (t : Reference.Trans N), Builds t → Build t = none) ∧
      (∀ (t : Reference.Trans N),
          Build t = none → ∀ (d : List N), on fun m m' => T t m d m', shall fun m m' => F t m d m') ∧
        (∀ (t : Reference.Trans N),
            Build t = none →
              ∀ (d : List N),
                on fun m m' => T t m d m', shall fun m x =>
                  ∃ d₀, TimeoutOutcome t (Consumes t m) d₀ ∧ ∀ (p : N), Deposits d p = Deposits d₀ p) ∧
          (∀ (t : Reference.Trans N),
              Build t = none →
                ∀ (m : CountMarking N),
                  Enabled t m → ∀ (d : List N), TimeoutOutcome t (Consumes t m) d → ∃ m', T t m d m') ∧
            (∀ (t : Reference.Trans N),
                Build t = none →
                  HasTimeout t →
                    ∀ (d : List N),
                      on fun m m' => F t m d m', shall fun m m' =>
                        T t m d m' ∨ ∃ b, OutputBranch t b ∧ ∀ (p : N), Produced d p ↔ p ∈ b) ∧
              ∀ (t : Reference.Trans N) (o : Out N),
                OutputSpec t = some o →
                  timeoutCount o ≤ 1 →
                    xorInTimeout o = true →
                      Build t ≠ none ∧ (PreOutputChecks t → ¬DupBranch o → Build t = some (msgXorInTimeout t))
-/
#guard_msgs in #print IO_013

/-! ## The reference satisfies IO-013 -/

/-- The reference builder rejects every output spec with two or more `Timeout` nodes, and with
IO-013's message once the input-arc and IO-011 checks pass. -/
theorem IO_013_refBuild_rejects {N : Type} [DecidableEq N] [ToString N] (t : Trans N)
    (o : Out N) (ho : OutputSpec t = some o) (h2 : 2 ≤ timeoutCount o) :
    refBuild t ≠ none ∧ (PreOutputChecks t → ¬ DupBranch o →
      refBuild t = some (msgTimeouts t (timeoutCount o))) := by
  simp only [OutputSpec] at ho
  refine ⟨fun h => ?_, fun hin hd => ?_⟩
  · have := (((refBuild_eq_none_iff t).1 h).2 o ho).2.1
    omega
  · rw [refBuild_of_pre hin]
    simp [ho, checkOut, (firstDup_eq_none_iff o).2 hd, h2]

/-- The reference builder rejects every output spec with at most one `Timeout` node and an `Xor`
node inside its child, with IO-013's `Xor` message once the input-arc and IO-011 checks pass. -/
theorem IO_013_refBuild_rejectsXor {N : Type} [DecidableEq N] [ToString N] (t : Trans N)
    (o : Out N) (ho : OutputSpec t = some o) (h1 : timeoutCount o ≤ 1)
    (hx : xorInTimeout o = true) :
    refBuild t ≠ none ∧ (PreOutputChecks t → ¬ DupBranch o →
      refBuild t = some (msgXorInTimeout t)) := by
  simp only [OutputSpec] at ho
  refine ⟨fun h => ?_, fun hin hd => ?_⟩
  · have := (((refBuild_eq_none_iff t).1 h).2 o ho).2.2.1
    rw [hx] at this
    exact absurd this (by decide)
  · have h2 : ¬ 2 ≤ timeoutCount o := by omega
    rw [refBuild_of_pre hin]
    simp [ho, checkOut, (firstDup_eq_none_iff o).2 hd, h2, hx]

/-- The reference builder accepts every transition that passes every build check. -/
theorem IO_013_refBuild_wf {N : Type} [DecidableEq N] [ToString N] (t : Trans N)
    (h : Builds t) : refBuild t = none :=
  (refBuild_eq_none_iff t).2 h

/-- Every reference timed-out firing is a reference firing. -/
theorem refTimeoutOutcomeFire_refFire {N : Type} [DecidableEq N] {t : Trans N}
    {m m' : N → Nat} {d : List N} (h : refTimeoutOutcomeFire t m d m') : RefFire t m d m' := by
  obtain ⟨hen, ⟨j, hj⟩, hm'⟩ := h
  exact ⟨hen, ⟨.timedOut j, hj⟩, hm'⟩

/-- A reference timed-out firing deposits a timeout outcome. -/
theorem refTimeoutOutcomeFire_outcome {N : Type} [DecidableEq N] {t : Trans N}
    {m m' : N → Nat} {d : List N} (h : refTimeoutOutcomeFire t m d m') :
    TimeoutOutcome t (Consumes t m) d := by
  obtain ⟨-, ⟨j, hj⟩, -⟩ := h
  have hj' : deposit (Consumes t m) t.out (.timedOut j) = some d := hj
  cases ho : t.out with
  | none => rw [ho] at hj'; simp [deposit] at hj'
  | some o =>
    rw [ho] at hj'
    cases hc : o.findTimeout with
    | none => simp [deposit, hc] at hj'
    | some c =>
      simp only [deposit, hc, Option.bind_some] at hj'
      exact ⟨o, c, ho, hc, List.mem_iff_getElem?.mpr ⟨j, hj'⟩⟩

/-- The reference offers the timeout outcome from every marking at which the transition is
enabled: each timeout deposit has an index `j`, and `.timedOut j` selects it. -/
theorem refTimeoutOutcomeFire_available {N : Type} [DecidableEq N] (t : Trans N)
    (m : N → Nat) (hen : Enabled t m) (d : List N) (hd : TimeoutOutcome t (Consumes t m) d) :
    ∃ m', refTimeoutOutcomeFire t m d m' := by
  obtain ⟨o, c, ho, hc, hdm⟩ := hd
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hdm
  exact ⟨_, hen, ⟨j, by simp [OutputSpec, deposit, ho, hc, hj]⟩, rfl⟩

/-- A reference firing ended with the timeout outcome or with an output branch. -/
theorem refFire_timedOut_or_branch {N : Type} [DecidableEq N] {t : Trans N} {m m' : N → Nat}
    {d : List N} (hf : RefFire t m d m') :
    refTimeoutOutcomeFire t m d m' ∨ ∃ b, OutputBranch t b ∧ ∀ p, Produced d p ↔ p ∈ b := by
  obtain ⟨hen, ⟨ch, hch⟩, hm'⟩ := hf
  cases ch with
  | timedOut j => exact Or.inl ⟨hen, ⟨j, hch⟩, hm'⟩
  | action i =>
    refine Or.inr ⟨d, ?_, fun _ => Iff.rfl⟩
    cases ho : t.out with
    | none =>
      rw [ho] at hch
      cases i with
      | zero => simp only [deposit, Option.some.injEq] at hch; simp [OutputBranch, ho, ← hch]
      | succ i => simp [deposit] at hch
    | some o =>
      rw [ho] at hch
      simp only [OutputBranch, ho]
      exact List.mem_iff_getElem?.mpr ⟨i, hch⟩

/-- The reference satisfies IO-013: the reference builder rejects a spec with two or more
`Timeout` nodes with IO-013's message and accepts every transition that passes every build check;
a timed-out reference firing is a reference firing, deposits the timeout outcome and nothing else
(`.timedOut j`), is available from every enabled marking, and every other reference firing ends
with its action, depositing one output branch (`.action i`). -/
@[evidence holds IO_013]
theorem IO_013_reference {N : Type} [DecidableEq N] [ToString N] :
    IO_013 (refBuild (N := N)) (RefFire (N := N)) (refTimeoutOutcomeFire (N := N)) :=
  ⟨IO_013_refBuild_rejects, IO_013_refBuild_wf,
   fun _ _ _ _ _ h => refTimeoutOutcomeFire_refFire h,
   fun _ _ d _ _ h => ⟨d, refTimeoutOutcomeFire_outcome h, fun _ => rfl⟩,
   fun t _ m hen => refTimeoutOutcomeFire_available t m hen,
   fun _ _ _ _ _ _ h => refFire_timedOut_or_branch h, IO_013_refBuild_rejectsXor⟩

/-- **One fixed timeout deposit**: on a transition the reference builder accepts, the timeout
outcome is one deposit, the same for every timed-out firing that consumed the same tokens. -/
theorem IO_013_one_fixed_deposit {N : Type} [DecidableEq N] [ToString N] {t : Trans N}
    (hb : refBuild t = none) {consumed : N → Nat} {d d' : List N}
    (h : TimeoutOutcome t consumed d) (h' : TimeoutOutcome t consumed d') : d = d' :=
  timeoutOutcome_unique ((refBuild_eq_none_iff t).1 hb) h h'

/-- A timed-out firing of a transition that builds, whose deposit differs, at some place, from
every timeout outcome refutes IO-013 (fourth line), whatever the rest of the model. -/
theorem IO_013_not_of_badTimedOut {N : Type} [DecidableEq N] {B : Trans N → Option String}
    {F T : FireRel N} {t : Trans N} {m m' : N → Nat} {d : List N} (hB : B t = none)
    (hT : T t m d m')
    (hbad : ∀ d₀, TimeoutOutcome t (Consumes t m) d₀ → ∃ p, Deposits d p ≠ Deposits d₀ p) :
    ¬ IO_013 B F T := by
  intro h
  obtain ⟨d₀, ho, hc⟩ := h.2.2.2.1 t hB d m m' hT
  obtain ⟨p, hp⟩ := hbad d₀ ho
  exact hp (hc p)

/-! ### Examples over a small net -/

/-- A transition named `t` with no arcs and output spec `o`. -/
def io013_trans (o : Out Nat) : Trans Nat :=
  { core := { name := "t", inputs := [], inhibitors := [], reads := [], resets := [] },
    out := some o }

/-- A transition with no arcs in whose output spec is `And(Place(0), Timeout(Place(1)))`: its
one output branch is `{0, 1}`, its timeout outcome deposits `[1]` alone. -/
def io013_and : Trans Nat := io013_trans (.and (.place 0) (.timeout (.place 1)))

/-- A transition with no arcs in whose output spec is `Xor(Place(0), Timeout(Place(1)))`, the
AC5 shape: an `Xor` with a `Timeout` sibling. -/
def io013_xor : Trans Nat := io013_trans (.xor (.place 0) (.timeout (.place 1)))

/-- A transition with input arc `(0, One)` whose output spec is `Timeout(ForwardInput(0, 1))`:
on the timeout it forwards the one token it consumed from `0` to `1`. -/
def io013_fwd : Trans Nat :=
  { core :=
      { name := "t", inputs := [{ place := 0, card := .one }], inhibitors := [], reads := [],
        resets := [] },
    out := some (.timeout (.forward 0 1)) }

/-- AC7's first rejected spec, `Timeout(d, Timeout(e, P))`, with `P = 0`. -/
def io013_nested : Trans Nat := io013_trans (.timeout (.timeout (.place 0)))

/-- AC7's second rejected spec, `Xor(Timeout(d, A), Timeout(e, B))`, with `A = 0`, `B = 1`:
two sibling `Timeout` nodes, neither inside the other. -/
def io013_siblings : Trans Nat := io013_trans (.xor (.timeout (.place 0)) (.timeout (.place 1)))

/-- AC7's third rejected spec, `And(Timeout(d, A), Xor(B, Timeout(e, C)))`, with `A = 0`,
`B = 1`, `C = 2`. -/
def io013_spread : Trans Nat :=
  io013_trans (.and (.timeout (.place 0)) (.xor (.place 1) (.timeout (.place 2))))

/-- AC7's second accepted spec, `Timeout(d, And(A, B))`, with `A = 0`, `B = 1`. (Its first,
`Xor(A, Timeout(d, B))`, is `io013_xor`.) -/
def io013_timeoutAnd : Trans Nat := io013_trans (.timeout (.and (.place 0) (.place 1)))

/-- The marking of the examples in which every place is empty. -/
def io013_empty : Nat → Nat := fun _ => 0

/-- The marking with three tokens in every place. -/
def io013_three : Nat → Nat := fun _ => 3

/-- ✓ AC7, rejected: each of AC7's three specs with two `Timeout` nodes fails to build under the
reference builder, with IO-013's message for `n = 2`. -/
theorem IO_013_ac7_rejected :
    refBuild io013_nested = some (msgTimeouts io013_nested 2) ∧
      refBuild io013_siblings = some (msgTimeouts io013_siblings 2) ∧
      refBuild io013_spread = some (msgTimeouts io013_spread 2) :=
  ⟨rfl, rfl, rfl⟩

/-- ✓ AC7, accepted: `Xor(A, Timeout(d, B))` and `Timeout(d, And(A, B))` build under the
reference builder, as do the other examples. -/
theorem IO_013_ac7_builds :
    refBuild io013_xor = none ∧ refBuild io013_timeoutAnd = none ∧
      refBuild io013_and = none ∧ refBuild io013_fwd = none :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The message for the nested spec, spelled out. -/
theorem IO_013_msg_nested :
    msgTimeouts io013_nested 2 =
      "output spec of transition 't' has 2 Timeout nodes; an output spec has at most one, nested or not (IO-013)" := by
  decide

/-- The timeout outcome of `io013_and`: one token in place `1`. -/
theorem io013_timeout_and : TimeoutOutcome io013_and (Consumes io013_and io013_empty) [1] :=
  ⟨_, _, rfl, rfl, List.mem_singleton_self _⟩

/-- The only timeout outcome of `io013_xor`, whatever was consumed, is `[1]`. -/
theorem io013_xor_timeout_eq {k : Nat → Nat} {d₀ : List Nat}
    (h : TimeoutOutcome io013_xor k d₀) : d₀ = [1] := by
  obtain ⟨o, c, ho, hc, hm⟩ := h
  simp only [io013_xor, io013_trans, Option.some.injEq] at ho
  subst ho
  simp only [Out.findTimeout, Option.none_or, Option.some.injEq] at hc
  subst hc
  simpa [Out.timeoutDeposits] using hm

/-- The only timeout outcome of `io013_fwd` forwards what was consumed from `0` to `1`. -/
theorem io013_fwd_timeout_eq {k : Nat → Nat} {d₀ : List Nat}
    (h : TimeoutOutcome io013_fwd k d₀) : d₀ = List.replicate (k 0) 1 := by
  obtain ⟨o, c, ho, hc, hm⟩ := h
  simp only [io013_fwd, Option.some.injEq] at ho
  subst ho
  simp only [Out.findTimeout, Option.some.injEq] at hc
  subst hc
  simpa [Out.timeoutDeposits] using hm

/-- `[1]` is not an output branch of `io013_and`: its only branch is `[0, 1]`. -/
theorem io013_and_not_branch : ¬ OutputBranch io013_and [1] := by
  simp [OutputBranch, io013_and, io013_trans, Out.branches, cross]

/-! ### Forbidden behaviour: the builder -/

/-- A builder that accepts every spec with two or more `Timeout` nodes and is otherwise the
reference builder. -/
def io013_countBlindBuild {N : Type} [DecidableEq N] [ToString N] : Trans N → Option String :=
  fun t =>
    match t.out with
    | some o => if 2 ≤ timeoutCount o then none else refBuild t
    | none => refBuild t

/-- A builder that accepts every spec with one `Timeout` node and an `Xor` node inside its child,
and is otherwise the reference builder: the builders before the check, which threw only when the
timeout fired. -/
def io013_xorBlindBuild {N : Type} [DecidableEq N] [ToString N] : Trans N → Option String :=
  fun t =>
    match t.out with
    | some o => if timeoutCount o ≤ 1 ∧ xorInTimeout o = true then none else refBuild t
    | none => refBuild t

/-- A builder that rejects a `Timeout` nested in the child of another, with IO-013's message,
and accepts sibling `Timeout` nodes: the "nested only" reading of the rule. -/
def io013_nestedOnlyBuild {N : Type} : Trans N → Option String := fun t =>
  match t.out with
  | some o =>
    if IO_013_nestedInside o then some (msgTimeouts t (timeoutCount o)) else none
  | none => none
where
  /-- Some `Timeout` node of the spec holds a `Timeout` node in its child. -/
  IO_013_nestedInside : Out N → Bool
    | .timeout c => 0 < timeoutCount c
    | .and l r => IO_013_nestedInside l || IO_013_nestedInside r
    | .xor l r => IO_013_nestedInside l || IO_013_nestedInside r
    | _ => false

/-- A builder that rejects two or more `Timeout` nodes with the runtime message Java and
TypeScript used to throw at the first timeout, not IO-013's. -/
def io013_oldMessageBuild {N : Type} : Trans N → Option String := fun t =>
  match t.out with
  | some o => if 2 ≤ timeoutCount o then some "Nested Timeout not allowed" else none
  | none => none

/-- A builder that rejects every transition: with the reference builder's message where that
builder rejects it, and otherwise with IO-013's message for no `Timeout` node. -/
def io013_rejectAllBuild {N : Type} [DecidableEq N] [ToString N] : Trans N → Option String :=
  fun t => some ((refBuild t).getD (msgTimeouts t 0))

/-- ✗ A builder that accepts two sibling `Timeout` nodes violates IO-013 (first line, AC7):
`Xor(Timeout(d, A), Timeout(e, B))` builds under the nested-only reading. -/
@[evidence forbids IO_013]
theorem IO_013_forbids_siblingsBuild :
    ¬ IO_013 io013_nestedOnlyBuild (RefFire (N := Nat)) refTimeoutOutcomeFire := by
  intro h
  exact (h.1 io013_siblings _ rfl (by decide)).1 rfl

/-- ✗ A builder that rejects the shape with another message violates IO-013 (first line): on
`Timeout(d, Timeout(e, P))` it reports `Nested Timeout not allowed`. -/
@[evidence forbids IO_013]
theorem IO_013_forbids_oldMessage :
    ¬ IO_013 io013_oldMessageBuild (RefFire (N := Nat)) refTimeoutOutcomeFire := by
  intro h
  have := (h.1 io013_nested _ rfl (by decide)).2 (by decide) (by decide)
  change some "Nested Timeout not allowed" = some (msgTimeouts io013_nested 2) at this
  rw [IO_013_msg_nested] at this
  exact absurd this (by decide)

/-! ### Forbidden behaviour: firings -/

/-- No firing ends with the timeout outcome. -/
def io013_noTimedOut {N : Type} : FireRel N := fun _ _ _ _ => False

/-- A firing relation whose action always completes in time: an enabled transition fires with
one of its output branches, never with the timeout outcome. -/
def io013_neverTimesOutFire : FireRel Nat :=
  fun t m d m' => Enabled t m ∧ OutputBranch t d ∧ m' = fireNC m t.core (depProd d)

/-- ✗ An executor whose action never overruns its budget violates IO-013 (sixth line):
`io013_and` builds and is enabled at the empty marking, but no firing ends with its timeout
outcome. -/
@[evidence forbids IO_013]
theorem IO_013_forbids_neverTimesOut :
    ¬ IO_013 refBuild io013_neverTimesOutFire io013_noTimedOut := by
  intro h
  obtain ⟨_, hf⟩ :=
    h.2.2.2.2.1 io013_and IO_013_ac7_builds.2.2.1 io013_empty (by decide) [1] io013_timeout_and
  exact hf

/-- M1: on the timeout, the executor deposits the first output branch (the action's own output)
instead of the `Timeout` child's tokens. -/
def io013_wrongBranchTimedOut : FireRel Nat :=
  timedOutBy fun t m d => HasTimeout t ∧ deposit (Consumes t m) (OutputSpec t) (.action 0) = some d

/-- ✗ M1, the wrong branch on timeout: on `io013_xor` the timed-out firing deposits the sibling
branch `[0]`, not the child's `[1]`. Each such deposit is also a reference action firing, so
only the timed-out relation shows the fault (fifth line). -/
@[evidence forbids IO_013]
theorem IO_013_forbids_wrongBranch :
    ¬ IO_013 refBuild (RefFire (N := Nat)) io013_wrongBranchTimedOut :=
  IO_013_not_of_badTimedOut (m := io013_empty) (d := [0]) (m' := fireNC io013_empty
      io013_xor.core (depProd [0])) IO_013_ac7_builds.1
    ⟨by decide, ⟨⟨_, _, rfl, rfl⟩, rfl⟩, rfl⟩
    fun _ h => ⟨0, by rw [io013_xor_timeout_eq h]; decide⟩

/-- M2: on the timeout, the executor deposits the timeout outcome twice: a duplicated child
token, or the child's token merged with an action write to the same place. -/
def io013_duplicateTimedOut : FireRel Nat :=
  timedOutBy fun t m d => ∃ d₀, TimeoutOutcome t (Consumes t m) d₀ ∧ d = d₀ ++ d₀

/-- ✗ M2, a duplicated child token: on `io013_xor` the timed-out firing deposits `[1, 1]`,
whose produced set `{1}` is an output branch; the count is wrong (fifth line). -/
@[evidence forbids IO_013]
theorem IO_013_forbids_duplicate :
    ¬ IO_013 refBuild (RefFire (N := Nat)) io013_duplicateTimedOut :=
  IO_013_not_of_badTimedOut (m := io013_empty) (d := [1, 1]) (m' := fireNC io013_empty
      io013_xor.core (depProd [1, 1])) IO_013_ac7_builds.1
    ⟨by decide, ⟨[1], ⟨_, _, rfl, rfl, List.mem_singleton_self _⟩, rfl⟩, rfl⟩
    fun _ h => ⟨1, by rw [io013_xor_timeout_eq h]; decide⟩

/-- M3: on the timeout, every `ForwardInput(from, to)` forwards the whole marking of `from`
instead of what the firing consumed from it. -/
def io013_forwardAllTimedOut : FireRel Nat :=
  timedOutBy fun t m d => ∃ j, deposit m (OutputSpec t) (.timedOut j) = some d

/-- ✗ M3, forwarding the whole source place: `io013_fwd` consumes one of the three tokens in
`0`, but the timed-out firing deposits `[1, 1, 1]` (fifth line). -/
@[evidence forbids IO_013]
theorem IO_013_forbids_forwardAll :
    ¬ IO_013 refBuild (RefFire (N := Nat)) io013_forwardAllTimedOut :=
  IO_013_not_of_badTimedOut (m := io013_three) (d := [1, 1, 1]) (m' := fireNC io013_three
      io013_fwd.core (depProd [1, 1, 1])) IO_013_ac7_builds.2.2.2
    ⟨by decide, ⟨0, rfl⟩, rfl⟩
    fun _ h => ⟨1, by rw [io013_fwd_timeout_eq h]; decide⟩

/-- A firing relation that, besides every reference firing, lets a firing keep what the action
wrote next to the timeout outcome and report it as an action firing: it deposits a timeout
outcome followed by an output branch. -/
def io013_mergeFire : FireRel Nat :=
  fun t m d m' => RefFire t m d m' ∨
    (Enabled t m ∧ ∃ d₀ b, TimeoutOutcome t (Consumes t m) d₀ ∧ OutputBranch t b ∧
      d = d₀ ++ b ∧ m' = fireNC m t.core (depProd d))

/-- ✗ A firing that keeps a partial write of an `Xor` sibling violates IO-013 (seventh line,
AC5): `io013_xor` deposits `[1, 0]`, the timeout outcome `[1]` together with the sibling's place
`0`; it did not end with the timeout outcome, and `{0, 1}` is not an output branch (`{0}` or
`{1}`). -/
@[evidence forbids IO_013]
theorem IO_013_forbids_merge : ¬ IO_013 refBuild io013_mergeFire refTimeoutOutcomeFire := by
  intro h
  have hf : io013_mergeFire io013_xor io013_empty [1, 0]
      (fireNC io013_empty io013_xor.core (depProd [1, 0])) :=
    Or.inr ⟨by decide, [1], [0], ⟨_, _, rfl, rfl, List.mem_singleton_self _⟩,
      by simp [OutputBranch, io013_xor, io013_trans, Out.branches], rfl, rfl⟩
  rcases h.2.2.2.2.2.1 io013_xor IO_013_ac7_builds.1 ⟨_, _, rfl, rfl⟩ [1, 0] _ _ hf with
    hT | ⟨b, hb, hiff⟩
  · have := io013_xor_timeout_eq (refTimeoutOutcomeFire_outcome hT)
    exact absurd this (by decide)
  · simp only [OutputBranch, io013_xor, io013_trans, Out.branches, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact absurd ((hiff 1).1 (by decide)) (by decide)
    · exact absurd ((hiff 0).1 (by decide)) (by decide)

/-- The reference timed-out firings, plus copies that leave the target marking where it was:
the deposit is right but such a firing has no effect, so it is no firing of `F`. -/
def io013_noEffectTimedOut : FireRel Nat :=
  fun t m d m' => refTimeoutOutcomeFire t m d m' ∨
    ((∃ m'', refTimeoutOutcomeFire t m d m'') ∧ m' = m)

/-- ✗ A timed-out firing that is not a firing (fourth line): `io013_and` times out from the
empty marking and deposits `[1]`, but the marking stays empty. -/
@[evidence forbids IO_013]
theorem IO_013_forbids_noEffect :
    ¬ IO_013 refBuild (RefFire (N := Nat)) io013_noEffectTimedOut := by
  intro h
  have hT : io013_noEffectTimedOut io013_and io013_empty [1] io013_empty :=
    Or.inr ⟨⟨_, by decide, ⟨0, rfl⟩, rfl⟩, rfl⟩
  obtain ⟨-, -, hm'⟩ := h.2.2.1 io013_and IO_013_ac7_builds.2.2.1 [1] _ _ hT
  exact absurd (congrFun hm' 1) (by decide)

/-- A wrong executor's timed-out firings (the behaviour RD-01 recorded of Java and TypeScript): a
reference timed-out firing deposits only when its timeout outcome passes output validation against the whole output spec, so only
when its produced set is one output branch. -/
def io013_validatedTimedOut : FireRel Nat :=
  fun t m d m' => refTimeoutOutcomeFire t m d m' ∧
    ∃ b, OutputBranch t b ∧ ∀ p, Produced d p ↔ p ∈ b

/-- A wrong executor's firings (the behaviour RD-01 recorded of Java and TypeScript): the reference
action firings, and the timed-out firings whose timeout outcome passes validation. -/
def io013_validatingFire : FireRel Nat :=
  fun t m d m' => RefFire t m d m' ∧
    (io013_validatedTimedOut t m d m' ∨ ∃ b, OutputBranch t b ∧ ∀ p, Produced d p ↔ p ∈ b)

/-- ✗ Validating the timeout outcome against the whole output spec (sixth line; the behaviour
RD-01 recorded):
`And(Place(0), Timeout(Place(1)))` builds and is enabled at the empty marking, but its timeout
outcome `[1]` is not its output branch `{0, 1}`, so no firing ends with it. -/
@[evidence forbids IO_013]
theorem IO_013_forbids_validateTimeout :
    ¬ IO_013 refBuild io013_validatingFire io013_validatedTimedOut := by
  intro h
  obtain ⟨_, -, b, hb, hp⟩ :=
    h.2.2.2.2.1 io013_and IO_013_ac7_builds.2.2.1 io013_empty (by decide) [1] io013_timeout_and
  have : b = [0, 1] := by
    simpa [OutputBranch, io013_and, io013_trans, Out.branches, cross] using hb
  subst this
  have := (hp 0).2 (by simp)
  simp [Produced] at this

/-! ### Mutant readings: one per line -/

/-- Mutant reading of IO-013 without the first line: a spec with two `Timeout` nodes may build. -/
def IO_013_mutant_dropRejects {N : Type} [DecidableEq N] (Build : Trans N → Option String)
    (F T : FireRel N) : Prop :=
  (∀ t, Builds t → Build t = none) ∧
  (∀ t, Build t = none → ∀ d, on (fun m m' => T t m d m'), shall (fun m m' => F t m d m')) ∧
  (∀ t, Build t = none → ∀ d, on (fun m m' => T t m d m'), shall (fun m _ =>
    ∃ d₀, TimeoutOutcome t (Consumes t m) d₀ ∧ ∀ p, Deposits d p = Deposits d₀ p)) ∧
  (∀ t, Build t = none → ∀ m, Enabled t m → ∀ d, TimeoutOutcome t (Consumes t m) d →
    ∃ m', T t m d m') ∧
  (∀ t, Build t = none → HasTimeout t → ∀ d, on (fun m m' => F t m d m'), shall (fun m m' =>
    T t m d m' ∨ ∃ b, OutputBranch t b ∧ ∀ p, Produced d p ↔ p ∈ b)) ∧
  (∀ t o, OutputSpec t = some o → timeoutCount o ≤ 1 → xorInTimeout o = true →
    Build t ≠ none ∧ (PreOutputChecks t → ¬ DupBranch o → Build t = some (msgXorInTimeout t)))

/-- The count-blind builder kills the first mutant: with the reference firings every other line
holds, but `Timeout(d, Timeout(e, P))` builds. -/
@[evidence mutant IO_013]
theorem IO_013_mutant_dropRejects_killed :
    IO_013_mutant_dropRejects io013_countBlindBuild (RefFire (N := Nat)) refTimeoutOutcomeFire ∧
      ¬ IO_013 io013_countBlindBuild (RefFire (N := Nat)) refTimeoutOutcomeFire := by
  refine ⟨⟨fun t hb => ?_, fun _ _ _ _ _ h => refTimeoutOutcomeFire_refFire h,
    fun _ _ d _ _ h => ⟨d, refTimeoutOutcomeFire_outcome h, fun _ => rfl⟩,
    fun t _ m hen => refTimeoutOutcomeFire_available t m hen,
    fun _ _ _ _ _ _ h => refFire_timedOut_or_branch h, fun t o ho h1 hx => ?_⟩,
    fun h => (h.1 io013_nested _ rfl (by decide)).1 rfl⟩
  · have hr := IO_013_refBuild_wf t hb
    unfold io013_countBlindBuild
    split
    · split
      · rfl
      · exact hr
    · exact hr
  · have ho' : t.out = some o := ho
    have hc : ¬ 2 ≤ timeoutCount o := by omega
    have hb : io013_countBlindBuild t = refBuild t := by simp [io013_countBlindBuild, ho', hc]
    rw [hb]
    exact IO_013_refBuild_rejectsXor t o ho h1 hx

/-- Mutant reading of IO-013 without the second line: nothing need build. -/
def IO_013_mutant_dropBuilds {N : Type} [DecidableEq N] (Build : Trans N → Option String)
    (F T : FireRel N) : Prop :=
  (∀ t o, OutputSpec t = some o → 2 ≤ timeoutCount o →
    Build t ≠ none ∧ (PreOutputChecks t → ¬ DupBranch o →
      Build t = some (msgTimeouts t (timeoutCount o)))) ∧
  (∀ t, Build t = none → ∀ d, on (fun m m' => T t m d m'), shall (fun m m' => F t m d m')) ∧
  (∀ t, Build t = none → ∀ d, on (fun m m' => T t m d m'), shall (fun m _ =>
    ∃ d₀, TimeoutOutcome t (Consumes t m) d₀ ∧ ∀ p, Deposits d p = Deposits d₀ p)) ∧
  (∀ t, Build t = none → ∀ m, Enabled t m → ∀ d, TimeoutOutcome t (Consumes t m) d →
    ∃ m', T t m d m') ∧
  (∀ t, Build t = none → HasTimeout t → ∀ d, on (fun m m' => F t m d m'), shall (fun m m' =>
    T t m d m' ∨ ∃ b, OutputBranch t b ∧ ∀ p, Produced d p ↔ p ∈ b)) ∧
  (∀ t o, OutputSpec t = some o → timeoutCount o ≤ 1 → xorInTimeout o = true →
    Build t ≠ none ∧ (PreOutputChecks t → ¬ DupBranch o → Build t = some (msgXorInTimeout t)))

/-- The reject-everything builder kills the second mutant: it rejects every spec, with the
reference builder's message wherever that builder rejects, so the build lines hold and the firing
lines are vacuous, even with no firing at all; but `Xor(A, Timeout(d, B))` passes every build
check and does not build. -/
@[evidence mutant IO_013]
theorem IO_013_mutant_dropBuilds_killed :
    IO_013_mutant_dropBuilds io013_rejectAllBuild io013_noTimedOut (io013_noTimedOut (N := Nat)) ∧
      ¬ IO_013 io013_rejectAllBuild io013_noTimedOut (io013_noTimedOut (N := Nat)) := by
  refine ⟨⟨fun t o ho h2 => ⟨by simp [io013_rejectAllBuild],
      fun hin hd => by simp [io013_rejectAllBuild, (IO_013_refBuild_rejects t o ho h2).2 hin hd]⟩,
    fun _ h => by simp [io013_rejectAllBuild] at h, fun _ h => by simp [io013_rejectAllBuild] at h,
    fun _ h => by simp [io013_rejectAllBuild] at h,
    fun _ h => by simp [io013_rejectAllBuild] at h,
    fun t o ho h1 hx => ⟨by simp [io013_rejectAllBuild],
      fun hin hd => by
        simp [io013_rejectAllBuild, (IO_013_refBuild_rejectsXor t o ho h1 hx).2 hin hd]⟩⟩,
    fun h => ?_⟩
  have hwf : Builds io013_xor := by decide
  exact absurd (h.2.1 io013_xor hwf) (by simp [io013_rejectAllBuild])

/-- Mutant reading of IO-013 without the fourth line: timed-out firings need not be firings. -/
def IO_013_mutant_dropIsFiring {N : Type} [DecidableEq N] (Build : Trans N → Option String)
    (F T : FireRel N) : Prop :=
  (∀ t o, OutputSpec t = some o → 2 ≤ timeoutCount o →
    Build t ≠ none ∧ (PreOutputChecks t → ¬ DupBranch o →
      Build t = some (msgTimeouts t (timeoutCount o)))) ∧
  (∀ t, Builds t → Build t = none) ∧
  (∀ t, Build t = none → ∀ d, on (fun m m' => T t m d m'), shall (fun m _ =>
    ∃ d₀, TimeoutOutcome t (Consumes t m) d₀ ∧ ∀ p, Deposits d p = Deposits d₀ p)) ∧
  (∀ t, Build t = none → ∀ m, Enabled t m → ∀ d, TimeoutOutcome t (Consumes t m) d →
    ∃ m', T t m d m') ∧
  (∀ t, Build t = none → HasTimeout t → ∀ d, on (fun m m' => F t m d m'), shall (fun m m' =>
    T t m d m' ∨ ∃ b, OutputBranch t b ∧ ∀ p, Produced d p ↔ p ∈ b)) ∧
  (∀ t o, OutputSpec t = some o → timeoutCount o ≤ 1 → xorInTimeout o = true →
    Build t ≠ none ∧ (PreOutputChecks t → ¬ DupBranch o → Build t = some (msgXorInTimeout t)))

/-- The no-effect timed-out firings kill the fourth-line mutant: builder, deposits,
availability and the action firings are the reference's, but a timed-out firing may leave the
marking unchanged. -/
@[evidence mutant IO_013]
theorem IO_013_mutant_dropIsFiring_killed :
    IO_013_mutant_dropIsFiring refBuild (RefFire (N := Nat)) io013_noEffectTimedOut ∧
      ¬ IO_013 refBuild (RefFire (N := Nat)) io013_noEffectTimedOut := by
  refine ⟨⟨IO_013_refBuild_rejects, IO_013_refBuild_wf, ?_, ?_, ?_, IO_013_refBuild_rejectsXor⟩,
    IO_013_forbids_noEffect⟩
  · rintro t - d m m' (h | ⟨⟨_, h⟩, -⟩)
    · exact ⟨d, refTimeoutOutcomeFire_outcome h, fun _ => rfl⟩
    · exact ⟨d, refTimeoutOutcomeFire_outcome h, fun _ => rfl⟩
  · intro t _ m hen d hd
    obtain ⟨m', h⟩ := refTimeoutOutcomeFire_available t m hen d hd
    exact ⟨m', Or.inl h⟩
  · intro t _ _ d m m' hf
    exact (refFire_timedOut_or_branch hf).imp_left Or.inl

/-- Mutant reading of IO-013 without the fifth line: a timed-out firing may deposit anything. -/
def IO_013_mutant_dropOnlyChild {N : Type} [DecidableEq N] (Build : Trans N → Option String)
    (F T : FireRel N) : Prop :=
  (∀ t o, OutputSpec t = some o → 2 ≤ timeoutCount o →
    Build t ≠ none ∧ (PreOutputChecks t → ¬ DupBranch o →
      Build t = some (msgTimeouts t (timeoutCount o)))) ∧
  (∀ t, Builds t → Build t = none) ∧
  (∀ t, Build t = none → ∀ d, on (fun m m' => T t m d m'), shall (fun m m' => F t m d m')) ∧
  (∀ t, Build t = none → ∀ m, Enabled t m → ∀ d, TimeoutOutcome t (Consumes t m) d →
    ∃ m', T t m d m') ∧
  (∀ t, Build t = none → HasTimeout t → ∀ d, on (fun m m' => F t m d m'), shall (fun m m' =>
    T t m d m' ∨ ∃ b, OutputBranch t b ∧ ∀ p, Produced d p ↔ p ∈ b)) ∧
  (∀ t o, OutputSpec t = some o → timeoutCount o ≤ 1 → xorInTimeout o = true →
    Build t ≠ none ∧ (PreOutputChecks t → ¬ DupBranch o → Build t = some (msgXorInTimeout t)))

/-- The reference timed-out firings together with M1's. -/
def io013_refOrWrongBranch : FireRel Nat :=
  fun t m d m' => refTimeoutOutcomeFire t m d m' ∨ io013_wrongBranchTimedOut t m d m'

/-- M1 kills the fifth-line mutant: every M1 timed-out firing is a reference action firing, the
reference timed-out firings stay available, and every firing is the reference's; but on
`io013_xor` a timed-out firing deposits the sibling branch `[0]`. -/
@[evidence mutant IO_013]
theorem IO_013_mutant_dropOnlyChild_killed :
    IO_013_mutant_dropOnlyChild refBuild (RefFire (N := Nat)) io013_refOrWrongBranch ∧
      ¬ IO_013 refBuild (RefFire (N := Nat)) io013_refOrWrongBranch := by
  refine ⟨⟨IO_013_refBuild_rejects, IO_013_refBuild_wf, ?_, ?_, ?_, IO_013_refBuild_rejectsXor⟩, ?_⟩
  · rintro t - d m m' (h | ⟨hen, ⟨-, hd⟩, hm'⟩)
    · exact refTimeoutOutcomeFire_refFire h
    · exact ⟨hen, ⟨.action 0, hd⟩, hm'⟩
  · intro t _ m hen d hd
    obtain ⟨m', h⟩ := refTimeoutOutcomeFire_available t m hen d hd
    exact ⟨m', Or.inl h⟩
  · intro t _ _ d m m' hf
    exact (refFire_timedOut_or_branch hf).imp_left Or.inl
  · exact IO_013_not_of_badTimedOut (m := io013_empty) (d := [0]) (m' := fireNC io013_empty
        io013_xor.core (depProd [0])) IO_013_ac7_builds.1
      (Or.inr ⟨by decide, ⟨⟨_, _, rfl, rfl⟩, rfl⟩, rfl⟩)
      fun _ h => ⟨0, by rw [io013_xor_timeout_eq h]; decide⟩

/-- Mutant reading of IO-013 without the sixth line: the timeout outcome need never happen. -/
def IO_013_mutant_dropAvailable {N : Type} [DecidableEq N] (Build : Trans N → Option String)
    (F T : FireRel N) : Prop :=
  (∀ t o, OutputSpec t = some o → 2 ≤ timeoutCount o →
    Build t ≠ none ∧ (PreOutputChecks t → ¬ DupBranch o →
      Build t = some (msgTimeouts t (timeoutCount o)))) ∧
  (∀ t, Builds t → Build t = none) ∧
  (∀ t, Build t = none → ∀ d, on (fun m m' => T t m d m'), shall (fun m m' => F t m d m')) ∧
  (∀ t, Build t = none → ∀ d, on (fun m m' => T t m d m'), shall (fun m _ =>
    ∃ d₀, TimeoutOutcome t (Consumes t m) d₀ ∧ ∀ p, Deposits d p = Deposits d₀ p)) ∧
  (∀ t, Build t = none → HasTimeout t → ∀ d, on (fun m m' => F t m d m'), shall (fun m m' =>
    T t m d m' ∨ ∃ b, OutputBranch t b ∧ ∀ p, Produced d p ↔ p ∈ b)) ∧
  (∀ t o, OutputSpec t = some o → timeoutCount o ≤ 1 → xorInTimeout o = true →
    Build t ≠ none ∧ (PreOutputChecks t → ¬ DupBranch o → Build t = some (msgXorInTimeout t)))

/-- The never-timing-out executor kills the sixth-line mutant: no firing ends with the timeout
outcome and every firing deposits an output branch, so the mutant holds; but the timeout outcome
of `io013_and` is never a firing. -/
@[evidence mutant IO_013]
theorem IO_013_mutant_dropAvailable_killed :
    IO_013_mutant_dropAvailable refBuild io013_neverTimesOutFire io013_noTimedOut ∧
      ¬ IO_013 refBuild io013_neverTimesOutFire io013_noTimedOut := by
  refine ⟨⟨IO_013_refBuild_rejects, IO_013_refBuild_wf, fun _ _ _ _ _ h => h.elim,
    fun _ _ _ _ _ h => h.elim, ?_, IO_013_refBuild_rejectsXor⟩, IO_013_forbids_neverTimesOut⟩
  rintro t - - d m m' ⟨-, hb, -⟩
  exact Or.inr ⟨d, hb, fun _ => Iff.rfl⟩

/-- Mutant reading of IO-013 without the seventh line: a firing that does not report the
timeout outcome may deposit anything. -/
def IO_013_mutant_dropActionBranch {N : Type} [DecidableEq N] (Build : Trans N → Option String)
    (F T : FireRel N) : Prop :=
  (∀ t o, OutputSpec t = some o → 2 ≤ timeoutCount o →
    Build t ≠ none ∧ (PreOutputChecks t → ¬ DupBranch o →
      Build t = some (msgTimeouts t (timeoutCount o)))) ∧
  (∀ t, Builds t → Build t = none) ∧
  (∀ t, Build t = none → ∀ d, on (fun m m' => T t m d m'), shall (fun m m' => F t m d m')) ∧
  (∀ t, Build t = none → ∀ d, on (fun m m' => T t m d m'), shall (fun m _ =>
    ∃ d₀, TimeoutOutcome t (Consumes t m) d₀ ∧ ∀ p, Deposits d p = Deposits d₀ p)) ∧
  (∀ t, Build t = none → ∀ m, Enabled t m → ∀ d, TimeoutOutcome t (Consumes t m) d →
    ∃ m', T t m d m') ∧
  (∀ t o, OutputSpec t = some o → timeoutCount o ≤ 1 → xorInTimeout o = true →
    Build t ≠ none ∧ (PreOutputChecks t → ¬ DupBranch o → Build t = some (msgXorInTimeout t)))

/-- The merging executor kills the seventh-line mutant: its timed-out firings are the
reference's, so the mutant holds; but it also fires `io013_xor` with `[1, 0]` and reports an
action firing. -/
@[evidence mutant IO_013]
theorem IO_013_mutant_dropActionBranch_killed :
    IO_013_mutant_dropActionBranch refBuild io013_mergeFire refTimeoutOutcomeFire ∧
      ¬ IO_013 refBuild io013_mergeFire refTimeoutOutcomeFire :=
  ⟨⟨IO_013_refBuild_rejects, IO_013_refBuild_wf,
    fun _ _ _ _ _ h => Or.inl (refTimeoutOutcomeFire_refFire h),
    fun _ _ d _ _ h => ⟨d, refTimeoutOutcomeFire_outcome h, fun _ => rfl⟩,
    fun t _ m hen => refTimeoutOutcomeFire_available t m hen, IO_013_refBuild_rejectsXor⟩,
    IO_013_forbids_merge⟩

/-- Every line of IO-013 is exercised by the reference: the reference builder rejects
`Timeout(d, Timeout(e, P))` with IO-013's message for two `Timeout` nodes and builds `io013_and`,
which has a `Timeout` node; `io013_and` times out from the empty marking with its timeout outcome
`[1]`, which is not an output branch, and that timed-out firing is a reference firing; it also
fires with its output branch `[0, 1]`, which is not a timed-out firing. -/
@[evidence nonvacuous IO_013]
theorem IO_013_nonvacuous :
    refBuild io013_nested = some (msgTimeouts io013_nested 2) ∧
      refBuild io013_and = none ∧
      HasTimeout io013_and ∧
      TimeoutOutcome io013_and (Consumes io013_and io013_empty) [1] ∧
      refTimeoutOutcomeFire io013_and io013_empty [1]
        (fireNC io013_empty io013_and.core (depProd [1])) ∧
      RefFire io013_and io013_empty [1] (fireNC io013_empty io013_and.core (depProd [1])) ∧
      ¬ OutputBranch io013_and [1] ∧
      RefFire io013_and io013_empty [0, 1]
        (fireNC io013_empty io013_and.core (depProd [0, 1])) ∧
      ¬ refTimeoutOutcomeFire io013_and io013_empty [0, 1]
        (fireNC io013_empty io013_and.core (depProd [0, 1])) :=
  ⟨IO_013_ac7_rejected.1, IO_013_ac7_builds.2.2.1,
    ⟨_, _, rfl, rfl⟩, io013_timeout_and, ⟨by decide, ⟨0, rfl⟩, rfl⟩,
    ⟨by decide, ⟨.timedOut 0, rfl⟩, rfl⟩, io013_and_not_branch,
    ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩,
    fun h => absurd (refTimeoutOutcomeFire_outcome h) fun ⟨o, c, ho, hc, hm⟩ => by
      simp only [io013_and, io013_trans, Option.some.injEq] at ho
      subst ho
      simp only [Out.findTimeout, Option.none_or, Option.some.injEq] at hc
      subst hc
      simp [Out.timeoutDeposits] at hm⟩

/-! ### One fixed timeout deposit: no `Xor` inside the `Timeout` child (AC8) -/

/-- AC8's first rejected spec, `Timeout(d, Xor(A, B))`, with `A = 0`, `B = 1`. -/
def io013_xorChild : Trans Nat := io013_trans (.timeout (.xor (.place 0) (.place 1)))

/-- AC8's second rejected spec, `Xor(C, Timeout(d, And(A, Xor(B, D))))`, with `A = 0`, `B = 1`,
`C = 2`, `D = 3`: the `Xor` sits under an `And` in the `Timeout` child. -/
def io013_deepXor : Trans Nat :=
  io013_trans (.xor (.place 2) (.timeout (.and (.place 0) (.xor (.place 1) (.place 3)))))

/-- AC8's second accepted spec, `Timeout(d, And(A, ForwardInput(i, B)))`, with `A = 0`, `B = 1`
and the input place `i = 4`. (Its first, `Xor(A, Timeout(d, B))`, is `io013_xor`.) -/
def io013_fwdAnd : Trans Nat :=
  { core :=
      { name := "t", inputs := [{ place := 4, card := .one }], inhibitors := [], reads := [],
        resets := [] },
    out := some (.timeout (.and (.place 0) (.forward 4 1))) }

/-- ✓ AC8, rejected: both specs fail to build under the reference builder, with IO-013's `Xor`
message. -/
theorem IO_013_ac8_rejected :
    refBuild io013_xorChild = some (msgXorInTimeout io013_xorChild) ∧
      refBuild io013_deepXor = some (msgXorInTimeout io013_deepXor) :=
  ⟨rfl, rfl⟩

/-- ✓ AC8, accepted: `Xor(A, Timeout(d, B))` and `Timeout(d, And(A, ForwardInput(i, B)))` build
under the reference builder. -/
theorem IO_013_ac8_builds : refBuild io013_xor = none ∧ refBuild io013_fwdAnd = none :=
  ⟨rfl, rfl⟩

set_option maxRecDepth 8000 in
/-- The `Xor` message for `io013_xorChild`, spelled out. -/
theorem IO_013_msg_xorChild :
    msgXorInTimeout io013_xorChild =
      "output spec of transition 't' has a Xor node inside the child of its Timeout node; the timeout outcome deposits one fixed set of places (IO-013)" := by
  decide

/-- Without the check the reference offers one timeout outcome per alternative: `Timeout(d,
Xor(A, B))` has the two timeout outcomes `[0]` and `[1]`. It does not build, so IO-013's firing
lines do not speak of it. Not tagged as evidence. -/
theorem IO_013_reference_xorChild_two_outcomes (k : Nat → Nat) :
    ¬ Builds io013_xorChild ∧ TimeoutOutcome io013_xorChild k [0] ∧
      TimeoutOutcome io013_xorChild k [1] :=
  ⟨by decide, ⟨_, _, rfl, rfl, by simp [Out.timeoutDeposits]⟩,
    ⟨_, _, rfl, rfl, by simp [Out.timeoutDeposits]⟩⟩

/-- ✗ A builder that accepts an `Xor` inside the `Timeout` child, as the builders did before the
check (they threw only when the timeout fired), violates IO-013 (eighth line, AC8):
`Timeout(d, Xor(A, B))` builds. -/
@[evidence forbids IO_013]
theorem IO_013_forbids_xorChildBuild :
    ¬ IO_013 io013_xorBlindBuild (RefFire (N := Nat)) refTimeoutOutcomeFire :=
  fun h => (h.2.2.2.2.2.2 io013_xorChild _ rfl (by decide) rfl).1 rfl

/-- Mutant reading of IO-013 without the eighth line: an `Xor` may sit inside the `Timeout`
child. -/
def IO_013_mutant_dropXorRejects {N : Type} [DecidableEq N] (Build : Trans N → Option String)
    (F T : FireRel N) : Prop :=
  (∀ t o, OutputSpec t = some o → 2 ≤ timeoutCount o →
    Build t ≠ none ∧ (PreOutputChecks t → ¬ DupBranch o →
      Build t = some (msgTimeouts t (timeoutCount o)))) ∧
  (∀ t, Builds t → Build t = none) ∧
  (∀ t, Build t = none → ∀ d, on (fun m m' => T t m d m'), shall (fun m m' => F t m d m')) ∧
  (∀ t, Build t = none → ∀ d, on (fun m m' => T t m d m'), shall (fun m _ =>
    ∃ d₀, TimeoutOutcome t (Consumes t m) d₀ ∧ ∀ p, Deposits d p = Deposits d₀ p)) ∧
  (∀ t, Build t = none → ∀ m, Enabled t m → ∀ d, TimeoutOutcome t (Consumes t m) d →
    ∃ m', T t m d m') ∧
  (∀ t, Build t = none → HasTimeout t → ∀ d, on (fun m m' => F t m d m'), shall (fun m m' =>
    T t m d m' ∨ ∃ b, OutputBranch t b ∧ ∀ p, Produced d p ↔ p ∈ b))

/-- The `Xor`-blind builder kills the eighth-line mutant: it is the reference builder on every
spec but those with one `Timeout` node and an `Xor` in its child, so every other line holds with
the reference firings; but `Timeout(d, Xor(A, B))` builds. -/
@[evidence mutant IO_013]
theorem IO_013_mutant_dropXorRejects_killed :
    IO_013_mutant_dropXorRejects io013_xorBlindBuild (RefFire (N := Nat)) refTimeoutOutcomeFire ∧
      ¬ IO_013 io013_xorBlindBuild (RefFire (N := Nat)) refTimeoutOutcomeFire := by
  refine ⟨⟨fun t o ho h2 => ?_, fun t hb => ?_, fun _ _ _ _ _ h => refTimeoutOutcomeFire_refFire h,
    fun _ _ d _ _ h => ⟨d, refTimeoutOutcomeFire_outcome h, fun _ => rfl⟩,
    fun t _ m hen => refTimeoutOutcomeFire_available t m hen,
    fun _ _ _ _ _ _ h => refFire_timedOut_or_branch h⟩, IO_013_forbids_xorChildBuild⟩
  · have ho' : t.out = some o := ho
    have hc : ¬ (timeoutCount o ≤ 1 ∧ xorInTimeout o = true) := fun h => by omega
    have hb : io013_xorBlindBuild t = refBuild t := by simp [io013_xorBlindBuild, ho', hc]
    rw [hb]
    exact IO_013_refBuild_rejects t o ho h2
  · have hr := IO_013_refBuild_wf t hb
    unfold io013_xorBlindBuild
    split
    · next o ho =>
      have hx : xorInTimeout o = false := (hb.2 o ho).2.2.1
      simp [hx, hr]
    · exact hr

/-- The eighth line is exercised by the reference: `Timeout(d, Xor(A, B))` has one `Timeout`
node with an `Xor` in its child, names no place twice, and the reference builder rejects it with
the `Xor` message; `Timeout(d, And(A, ForwardInput(i, B)))` builds and its timeout outcome from a
firing that consumed one token from `i` is the one deposit `[0, 1]`. -/
@[evidence nonvacuous IO_013]
theorem IO_013_nonvacuous_xor :
    timeoutCount (Out.timeout (.xor (.place 0) (.place 1)) : Out Nat) ≤ 1 ∧
      xorInTimeout (Out.timeout (.xor (.place 0) (.place 1)) : Out Nat) = true ∧
      PreOutputChecks io013_xorChild ∧
      ¬ DupBranch (Out.timeout (.xor (.place 0) (.place 1)) : Out Nat) ∧
      refBuild io013_xorChild = some (msgXorInTimeout io013_xorChild) ∧
      refBuild io013_fwdAnd = none ∧
      TimeoutOutcome io013_fwdAnd (fun _ => 1) [0, 1] ∧
      ∀ d, TimeoutOutcome io013_fwdAnd (fun _ => 1) d → d = [0, 1] :=
  ⟨by decide, rfl, by decide, by decide, IO_013_ac8_rejected.1, IO_013_ac8_builds.2,
    ⟨_, _, rfl, rfl, by simp [Out.timeoutDeposits, cross]⟩,
    fun d h => IO_013_one_fixed_deposit IO_013_ac8_builds.2 h
      ⟨_, _, rfl, rfl, by simp [Out.timeoutDeposits, cross]⟩⟩

end Libpetri.Spec
