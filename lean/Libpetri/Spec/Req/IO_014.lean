import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.Glossary
import Libpetri.Spec.Text.IO_014

set_option linter.missingDocs true

/-!
# IO-014: Output ForwardInput (`spec/02-input-output-specs.md`)

IO-014 has a build half and a firing half.

* **Build.** A `ForwardInput` outside the child of a `Timeout` node is rejected when the
  transition is built, with a fixed message naming the first such node in pre-order; a forward
  from a place that is not an input place is rejected too (AC1, AC3). The model `Build` is the
  transition builder, read as the message it rejects a transition with (`none`: it builds). The
  witness is `refBuild`, which runs the output-spec checks in the order of the spec's
  output composition preamble.
* **Firing.** What a firing that **ends with the timeout outcome** deposits through a
  `ForwardInput(from, to)` node. A plain firing relation `F : FireRel N` does not say which way a
  firing ended, and on a `Timeout(ForwardInput(from, to))` spec the action branch `[to]` and a
  forward of one token are the same deposit. The firing half is therefore a predicate over the
  relation `T : FireRel N` of the firings that end with the timeout outcome. The witness is
  `refTimedOutFire`: the reference firings (`Reference.Fires`) whose outcome is a `timedOut`
  choice; `refTimedOutFire_refFire` shows each of them is a reference firing.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## The firing model: firings that end with the timeout outcome -/

/-- `ForwardInput(src, dst)` occurs in `o`: as `o` itself, or under an `And`, `Xor` or `Timeout`
node of `o`. -/
def ForwardLeaf {N : Type} : Out N → N → N → Prop
  | .forward s d, src, dst => s = src ∧ d = dst
  | .place _, _, _ => False
  | .and l r, src, dst => ForwardLeaf l src dst ∨ ForwardLeaf r src dst
  | .xor l r, src, dst => ForwardLeaf l src dst ∨ ForwardLeaf r src dst
  | .timeout c, src, dst => ForwardLeaf c src dst

/-- `ForwardInput(src, dst)` occurs in `t`'s `Timeout` child, at any depth. On an output spec
with at most one `Timeout` node, `Out.findTimeout` finds that node's child, the one the reference
timeout outcome reads (glossary: Timeout outcome). -/
def TimeoutForwards {N : Type} (t : Trans N) (src dst : N) : Prop :=
  ∃ o c, OutputSpec t = some o ∧ o.findTimeout = some c ∧ ForwardLeaf c src dst

/-- Firings of `t` that end with the timeout outcome, with the timeout child's forwards counting
`k t m p` tokens for each place `p` instead of the firing's consumption: enabled, a timeout
deposit of the output spec, and the reference effect. -/
def timedOutFireWith {N : Type} [DecidableEq N] (k : Trans N → (N → Nat) → N → Nat) :
    FireRel N :=
  fun t m d m' =>
    Enabled t m ∧ (∃ j, deposit (k t m) (OutputSpec t) (.timedOut j) = some d) ∧
      m' = fireNC m t.core (depProd d)

/-- **The reference timed-out firings**: the reference firings (`Reference.Fires`) that end with
the timeout outcome, a forward counting what the firing consumed (`Consumes`). -/
def refTimedOutFire {N : Type} [DecidableEq N] : FireRel N :=
  timedOutFireWith (fun t m => Consumes t m)

/- The reference timed-out firings are the second witness model of IO-014's `holds` theorem. -/
#spec_witness refTimedOutFire

/-- Every reference timed-out firing is a reference firing: `refTimedOutFire` is the part of
`RefFire` whose outcome is a `timedOut` choice. -/
theorem refTimedOutFire_refFire {N : Type} [DecidableEq N] {t : Trans N} {m m' : N → Nat}
    {d : List N} (h : refTimedOutFire t m d m') : RefFire t m d m' := by
  obtain ⟨hen, ⟨j, hj⟩, hm'⟩ := h
  exact ⟨hen, ⟨.timedOut j, hj⟩, hm'⟩

/-! ## IO-014: Output ForwardInput -/

requirement IO_014
  id "IO-014"
  title "Output ForwardInput"
  kind B
  scope "all executors"
  source verbatim "spec/02-input-output-specs.md"
  covers IO_014.s1, IO_014.s2, IO_014.s3, IO_014.s4, IO_014.s5, IO_014.s6, IO_014.s7, IO_014.s8
  reading "Let Build be the builder (Build t = none: t builds; Build t = some msg: building t fails with msg) and T the firings that end with the timeout outcome."
          "For every transition t whose output spec o has a ForwardInput(from, to) outside the child of a Timeout node, the first in pre-order, building t fails;"
          "and if t's input places are distinct, no output branch of o names a place twice, o has at most one Timeout node and no Xor node inside its Timeout child, building t fails with the IO-014 message naming t, from and to."
          "For every transition t whose output spec has a ForwardInput from a place that is not one of t's input places, building t fails."
          "Every transition that passes every build check (distinct input places, no place twice in one output branch, at most one Timeout node, no Xor node inside the Timeout child, no ForwardInput outside a Timeout child, every forward from an input place, no two output branches claiming one set of places) builds."
          "For every transition t whose output spec has at most one Timeout node and a ForwardInput(from, to) anywhere in that node's child (also under And or Xor), every deposit d and every firing of t from m in T that deposits d, there is one timeout deposit e of the Timeout child, built with every ForwardInput(a, b) of the child putting in b one token per token the firing consumes from a, such that e puts no more tokens than d in any place (no consumed token is lost, at any forward of the child) and d puts no more tokens than e in any place (one token per consumed token, none extra)."
  assumes "The model is the pair (Build, T). Build is the transition builder, read as the message building a transition fails with, none when it builds; the reference builder refBuild runs the CORE-030 input-arc check and then the output-spec checks in the order of the output composition preamble of spec/02-input-output-specs.md (IO-011, IO-013's Timeout count, IO-013's Xor inside the Timeout child, IO-014, IO-014 AC3, IO-012), with each message byte for byte except CORE-030's, which the spec does not give. Place names are rendered with the place type's ToString."
          "T is the relation of firings that end with the timeout outcome (glossary: Timeout outcome), read as one step from a marking to a marking that deposits the Timeout child's tokens (glossary: Fire, Deposit); timing and priority play no part. A plain FireRel cannot be used: on Timeout(ForwardInput(from, to)) the action branch [to] and a forward of one token are the same deposit. The witness refTimedOutFire is the part of RefFire whose outcome is a timedOut choice (refTimedOutFire_refFire). That the resulting marking receives d is the effect rule (CORE-030, CORE-034, CORE-035) on the plain firing relation, not restated here."
          "The build error is msgForward, byte for byte: output spec of transition '<t>' uses ForwardInput('<from>', '<to>') outside the child of a Timeout node; a forward deposits only on the timeout outcome (IO-014). 'Not inside the child of a Timeout node' and 'the first such node' are forwardOutside: the pre-order walk, children left to right, that does not enter a Timeout node. The preamble's order runs the IO-011 check (a place twice in one output branch) and the IO-013 checks (more than one Timeout node, an Xor node inside the Timeout child) first, so on such a spec the message is theirs, and the second line only requires that building fails; CORE-030's input-arc check is not placed by the preamble and is treated the same way."
          "'On every construction path' is read as: Build is the one builder every construction path goes through (builders, composition, channel merge, fusion), so a transition that a path yields builds exactly when Build accepts it. Which paths exist is not in the model. No executor option reaches Build (CONC-026)."
          "The fifth line is the converse that makes 'builds' checkable (AC7's specs that build): a transition passing the checks before the output spec (CORE-030, the IO-002/IO-004 input counts and EXEC-012's input-and-read check, PreOutputChecks) and every build check of the output composition preamble builds. The checks are the glossary terms Builds and WellFormedOut, the same checks IO-013 reads."
          "The firing line is stated for every transition whose output spec has at most one Timeout node, not only for transitions that build: a transition with two or more Timeout nodes is rejected (IO-013) and has no single Timeout child, so no reading of 'the Timeout child' is claimed there, while a transition with a forward from a non-input place, rejected by the fourth line, is still covered, which is what keeps the fourth quote (no input consumed, nothing forwarded) checkable. A transition with one Timeout node has one Timeout child, the one Out.findTimeout finds."
          "'The `ForwardInput(from, to)` node of an output spec that, on the timeout outcome, deposits in `to` the tokens a firing consumed' (first quote) is the firing line, which says how many."
          "'Every ForwardInput(from, to) in the Timeout child' includes a ForwardInput nested under And or Xor. On a transition that builds the child holds no Xor node (IO-013), so it has one timeout deposit (glossary: timeoutOutcome_unique); the line is also stated for transitions that do not build, where an Xor child has several timeout deposits and which one a firing chose is visible only in the whole deposit, so the statement compares d place by place with one timeout deposit e of the child (glossary: Timeout outcome, TimeoutOutcome); deposits are compared per place, so the order of the deposit list does not matter (CORE-036). This also fixes the tokens the child's Place leaves put in, which is IO-013's subject (AC5); it is restated here only because it is what identifies the chosen alternative. Comparing only the place `to` would let a forward-first firing pass whenever another alternative of the child happens to put the same count in `to`."
          "'The count' (sixth quote) is the firing's consumption from `from`, the glossary term Consume (Consumes t m from), which is IO-007's consumption count of the input arc on `from` (bridge lemma consumes_eq) and 0 for a place with no input arc. The two bounds of the firing line together say d equals e place by place, with one existential e for both; they are split so that losing tokens and inventing tokens are refuted separately."
          "The seventh quote (no forward of fewer tokens, not only the first) is the first bound. The eighth quote (no input consumed, nothing forwarded) is the second bound, e having no forwarded token where Consumes t m from = 0."
          "The sentence '*When* a `ForwardInput` forwards a consumed token, the token it deposits in `to` *shall* carry the consumed token's `created_at` as well as its value.' is token metadata (a value and a creation stamp) below the count granularity of the firing semantics, which has no token values or stamps; it is not encoded, and neither is the paragraph around it (the TIME-015 exception, the NU-022 tie-break)."
          "AC1 (from must be a declared input place, validated at build time) and AC3 (an invalid from reference is a build error) are the fourth line. Which forward AC3's existing message names when several are invalid is not said by the text; the reference builder names the first in pre-order, and the statement does not constrain the message."
          "AC2 (one token per consumed token, preserving values and consumption order) is the firing line for its count; values and consumption order are below the count granularity and are not encoded."
          "AC4 (All or Exactly(n) with N tokens consumed puts exactly N in `to`) is the two bounds together, with Consumes giving N for Exactly(n) and the whole place for All."
          "AC5 (a forwarded token's created_at equals the original's and is not re-stamped from the epoch clock, while a minted recovery token is, in every implementation) is token metadata below the count granularity and is not encoded."
          "AC6 (every analysis deposits what the executor deposits) is about the verifier's branch expansion (IO-016, VER-001), not about firings or building; Novel/ForwardDeposit.lean proves it for the flattened rows."
          "AC7 is the second, third and fifth lines: its three rejected specs (ForwardInput(a, b), Xor(c, ForwardInput(a, b)), And(c, Xor(e, ForwardInput(a, b)))) fail with the message naming a and b, and its two accepted specs (Timeout(d, ForwardInput(a, b)), Xor(c, Timeout(d, And(e, ForwardInput(a, b))))) build, under the reference builder with a an input place (IO_014_ac7_rejected, IO_014_ac7_builds)."
          "Ruling D15: the premise PreOutputChecks t (glossary) is the checks the reference builder runs before the output-spec checks: distinct input places ([CORE-030]), input arcs that each require at least one token ([IO-002], [IO-004]) and no input arc and read arc on one place ([EXEC-012]). A transition that fails one of them fails with that check's message, so on it the build lines only require that building fails, as for CORE-030 before the ruling."
          "Every runtime forwards on the timeout outcome between the places the rewritten output spec names, as given: Java (ExecutorSupport produceTimeoutOutputRecursive reads the from place with rawInput, and TransitionContext.forwardToHarvest deposits in to) and TypeScript (executor-support.ts produceTimeoutOutput and transition-context.ts forwardToHarvest) take those places as the actual places and do not resolve them through the composition correspondence again, and Rust forwards between them directly. An executor that resolves them a second time, on a correspondence collision (port a bound to b, port b bound to c), forwards the token meant for b to c, or reads from the wrong input, so the deposit differs place by place from every timeout deposit of the child and the firing line fails (the behaviour RD-31 in spec/runtime-defects.md recorded of Java and TypeScript, on both the to and the from side). The correspondence is not in this model, whose transition is the rewritten one, so the statement cannot see the second resolution; that wrong executor is shown in MOD_031.lean (mod031ctx_timeout_resolveTwice), and the runtimes are tested on it (java AbstractNetExecutorEngineTest OutputTimeoutTests outTimeout_forwardInput_portCollision_forwardsFromTheBoundPlace_MOD031_IO014; typescript tests/core/compose-action-place-alias.test.ts 'a timeout ForwardInput reads and deposits on the actual places under a collision')."
  signoff "2026-11-13 73d8a8afcc5b3c0d ai"
  statement : ∀ {N : Type} [DecidableEq N] [ToString N], (Trans N → Option String) → FireRel N → Prop :=
    fun Build T =>
      (∀ t o src dst, OutputSpec t = some o → forwardOutside o = some (src, dst) →
        Build t ≠ none) ∧
      (∀ t o src dst, OutputSpec t = some o → forwardOutside o = some (src, dst) →
        PreOutputChecks t → ¬ DupBranch o → timeoutCount o ≤ 1 → xorInTimeout o = false →
        Build t = some (msgForward t src dst)) ∧
      (∀ t o src, OutputSpec t = some o → src ∈ forwardSources o →
        src ∉ inPlaces t → Build t ≠ none) ∧
      (∀ t, Builds t → Build t = none) ∧
      (∀ t src dst, (∀ o, OutputSpec t = some o → timeoutCount o ≤ 1) →
        TimeoutForwards t src dst → ∀ d,
        on (fun m m' => T t m d m'), shall (fun m _ => ∃ e, TimeoutOutcome t (Consumes t m) e ∧
          (∀ p, Deposits e p ≤ Deposits d p) ∧ (∀ p, Deposits d p ≤ Deposits e p)))

/- The pinned readable form of IO-014: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.IO_014 : {N : Type} →
  [DecidableEq N] → [ToString N] → (Reference.Trans N → Option String) → FireRel N → Prop :=
fun {N} [DecidableEq N] [ToString N] Build T =>
  (∀ (t : Reference.Trans N) (o : Out N) (src dst : N),
      OutputSpec t = some o → forwardOutside o = some (src, dst) → Build t ≠ none) ∧
    (∀ (t : Reference.Trans N) (o : Out N) (src dst : N),
        OutputSpec t = some o →
          forwardOutside o = some (src, dst) →
            PreOutputChecks t →
              ¬DupBranch o → timeoutCount o ≤ 1 → xorInTimeout o = false → Build t = some (msgForward t src dst)) ∧
      (∀ (t : Reference.Trans N) (o : Out N) (src : N),
          OutputSpec t = some o → src ∈ forwardSources o → src ∉ inPlaces t → Build t ≠ none) ∧
        (∀ (t : Reference.Trans N), Builds t → Build t = none) ∧
          ∀ (t : Reference.Trans N) (src dst : N),
            (∀ (o : Out N), OutputSpec t = some o → timeoutCount o ≤ 1) →
              TimeoutForwards t src dst →
                ∀ (d : List N),
                  on fun m m' => T t m d m', shall fun m x =>
                    ∃ e,
                      TimeoutOutcome t (Consumes t m) e ∧
                        (∀ (p : N), Deposits e p ≤ Deposits d p) ∧ ∀ (p : N), Deposits d p ≤ Deposits e p
-/
#guard_msgs in #print IO_014

/-! ## The clauses, one by one (for the mutants) -/

/-- First line: a `ForwardInput` outside a `Timeout` child makes building fail. -/
def IO_014_bareRejected {N : Type} (Build : Trans N → Option String) : Prop :=
  ∀ t o src dst, OutputSpec t = some o → forwardOutside o = some (src, dst) →
    Build t ≠ none

/-- Second line: with the earlier checks passing, the failure is IO-014's message. -/
def IO_014_bareMessage {N : Type} [DecidableEq N] [ToString N]
    (Build : Trans N → Option String) : Prop :=
  ∀ t o src dst, OutputSpec t = some o → forwardOutside o = some (src, dst) →
    PreOutputChecks t → ¬ DupBranch o → timeoutCount o ≤ 1 → xorInTimeout o = false →
    Build t = some (msgForward t src dst)

/-- Third line (AC1, AC3): a forward from a non-input place makes building fail. -/
def IO_014_nonInputRejected {N : Type} [DecidableEq N] (Build : Trans N → Option String) :
    Prop :=
  ∀ t o src, OutputSpec t = some o → src ∈ forwardSources o →
    src ∉ inPlaces t → Build t ≠ none

/-- Fourth line: a transition passing every build check builds. -/
def IO_014_wfBuilds {N : Type} [DecidableEq N] (Build : Trans N → Option String) : Prop :=
  ∀ t, Builds t → Build t = none

/-- Fifth line: a timed-out firing deposits, place by place, one timeout deposit of the child. -/
def IO_014_forwardCounts {N : Type} [DecidableEq N] (T : FireRel N) : Prop :=
  ∀ t src dst, (∀ o, OutputSpec t = some o → timeoutCount o ≤ 1) →
    TimeoutForwards t src dst → ∀ d,
    on (fun m m' => T t m d m'), shall (fun m _ => ∃ e, TimeoutOutcome t (Consumes t m) e ∧
      (∀ p, Deposits e p ≤ Deposits d p) ∧ (∀ p, Deposits d p ≤ Deposits e p))

/-- IO-014 is the conjunction of its five clauses. -/
theorem IO_014_iff {N : Type} [DecidableEq N] [ToString N] (Build : Trans N → Option String)
    (T : FireRel N) :
    IO_014 Build T ↔ IO_014_bareRejected Build ∧ IO_014_bareMessage Build ∧
      IO_014_nonInputRejected Build ∧ IO_014_wfBuilds Build ∧ IO_014_forwardCounts T :=
  Iff.rfl

/-! ## The reference satisfies IO-014 -/

/-- A timeout deposit of the reference outcome rule is a `TimeoutOutcome`. -/
theorem deposit_timedOut_outcome {N : Type} {k : N → Nat} {t : Trans N} {j : Nat} {d : List N}
    (hd : deposit k (OutputSpec t) (.timedOut j) = some d) : TimeoutOutcome t k d := by
  cases ho : t.out with
  | none => simp [OutputSpec, ho, deposit] at hd
  | some o =>
    rw [OutputSpec, ho] at hd
    cases hc : o.findTimeout with
    | none => simp [deposit, hc] at hd
    | some c =>
      simp only [deposit, hc, Option.bind_some] at hd
      exact ⟨o, c, ho, hc, List.mem_of_getElem? hd⟩

/-- A branch without a repeated place has no place counted twice. -/
theorem IO_014_find_dup_none {N : Type} [DecidableEq N] {b : List N} (h : b.Nodup) :
    b.find? (fun p => decide (2 ≤ b.count p)) = none := by
  rw [List.find?_eq_none]
  intro p hp
  rw [List.count_eq_one_of_mem h hp]
  decide

/-- The output-spec checks reject a spec with a forward outside a `Timeout` child, whatever
input places they read. -/
theorem IO_014_checkOut_bare {N : Type} [DecidableEq N] [ToString N] {t : Trans N}
    {ins : List N} {o : Out N} {src dst : N} (h : forwardOutside o = some (src, dst)) :
    checkOut t ins o ≠ none ∧
      (¬ DupBranch o → timeoutCount o ≤ 1 → xorInTimeout o = false →
        checkOut t ins o = some (msgForward t src dst)) := by
  unfold checkOut
  refine ⟨?_, fun hd hc hx => ?_⟩
  · split
    · simp
    · split
      · simp
      · split
        · simp
        · simp [h]
  · simp [(firstDup_eq_none_iff o).2 hd, show ¬ 2 ≤ timeoutCount o by omega, hx, h]

/-- The reference builder satisfies the first two lines. -/
theorem IO_014_refBuild_bare {N : Type} [DecidableEq N] [ToString N] {t : Trans N}
    {o : Out N} {src dst : N} (ho : OutputSpec t = some o)
    (h : forwardOutside o = some (src, dst)) :
    refBuild t ≠ none ∧
      (PreOutputChecks t → ¬ DupBranch o → timeoutCount o ≤ 1 → xorInTimeout o = false →
        refBuild t = some (msgForward t src dst)) := by
  have ho' : t.out = some o := ho
  refine ⟨fun hb => (IO_014_checkOut_bare h).1
    ((checkOut_eq_none_iff t o).2 (((refBuild_eq_none_iff t).1 hb).2 o ho)), fun hi hd hc hx => ?_⟩
  rw [refBuild_of_pre hi, ho']; exact (IO_014_checkOut_bare h).2 hd hc hx

/-- The output-spec checks reject a forward from a place outside `ins`. -/
theorem IO_014_checkOut_nonInput {N : Type} [DecidableEq N] [ToString N] {t : Trans N}
    {ins : List N} {o : Out N} {src : N} (hs : src ∈ forwardSources o)
    (hn : src ∉ ins) : checkOut t ins o ≠ none := by
  unfold checkOut
  split
  · simp
  · split
    · simp
    · split
      · simp
      · split
        · simp
        · split
          · simp
          · rename_i hf
            rw [List.find?_eq_none] at hf
            exact absurd (hf src hs) (by simpa using hn)

/-- The reference builder satisfies the third line. -/
theorem IO_014_refBuild_nonInput {N : Type} [DecidableEq N] [ToString N] {t : Trans N}
    {o : Out N} {src : N} (ho : OutputSpec t = some o) (hs : src ∈ forwardSources o)
    (hn : src ∉ inPlaces t) : refBuild t ≠ none := fun hb =>
  IO_014_checkOut_nonInput hs hn
    ((checkOut_eq_none_iff t o).2 (((refBuild_eq_none_iff t).1 hb).2 o ho))

/-- The reference builder satisfies the fourth line. -/
theorem IO_014_refBuild_wf {N : Type} [DecidableEq N] [ToString N] {t : Trans N}
    (h : Builds t) : refBuild t = none :=
  (refBuild_eq_none_iff t).2 h

/-- The reference timed-out firings satisfy the fifth line: a timed-out reference firing
deposits one of the `Timeout` child's timeout deposits (`Out.timeoutDeposits`), each forward
counting what the firing consumed, so `e := d` matches it place by place. -/
theorem IO_014_refFire_counts {N : Type} [DecidableEq N] :
    IO_014_forwardCounts (refTimedOutFire (N := N)) := by
  intro t src dst _ _ d m _ hf
  obtain ⟨-, ⟨j, hj⟩, -⟩ := hf
  exact ⟨d, deposit_timedOut_outcome hj, fun _ => le_refl _, fun _ => le_refl _⟩

/-- The reference satisfies IO-014: the reference builder and the reference timed-out firings. -/
@[evidence holds IO_014]
theorem IO_014_reference {N : Type} [DecidableEq N] [ToString N] :
    IO_014 (refBuild (N := N)) refTimedOutFire :=
  ⟨fun _ _ _ _ ho h => (IO_014_refBuild_bare ho h).1,
    fun _ _ _ _ ho h => (IO_014_refBuild_bare ho h).2,
    fun _ _ _ ho hs hn => IO_014_refBuild_nonInput ho hs hn,
    fun _ h => IO_014_refBuild_wf h,
    IO_014_refFire_counts⟩

/-! ### AC7 under the reference builder -/

/-- A transition named `t` with the one input place `a` and the output spec `o`. -/
def io014_build (o : Out String) : Trans String :=
  { core := { name := "t", inputs := [{ place := "a", card := .one }], inhibitors := [],
              reads := [], resets := [] },
    out := some o }

set_option maxRecDepth 8000 in
/-- AC7's rejected specs fail with the IO-014 message naming `a` and `b`: `ForwardInput(a, b)`,
`Xor(c, ForwardInput(a, b))` and `And(c, Xor(e, ForwardInput(a, b)))`. -/
theorem IO_014_ac7_rejected :
    refBuild (io014_build (.forward "a" "b")) =
        some "output spec of transition 't' uses ForwardInput('a', 'b') outside the child of a Timeout node; a forward deposits only on the timeout outcome (IO-014)" ∧
      refBuild (io014_build (.xor (.place "c") (.forward "a" "b"))) =
        some "output spec of transition 't' uses ForwardInput('a', 'b') outside the child of a Timeout node; a forward deposits only on the timeout outcome (IO-014)" ∧
      refBuild (io014_build (.and (.place "c") (.xor (.place "e") (.forward "a" "b")))) =
        some "output spec of transition 't' uses ForwardInput('a', 'b') outside the child of a Timeout node; a forward deposits only on the timeout outcome (IO-014)" := by
  decide

/-- AC7's accepted specs build: `Timeout(d, ForwardInput(a, b))` and
`Xor(c, Timeout(d, And(e, ForwardInput(a, b))))`. -/
theorem IO_014_ac7_builds :
    refBuild (io014_build (.timeout (.forward "a" "b"))) = none ∧
      refBuild (io014_build
        (.xor (.place "c") (.timeout (.and (.place "e") (.forward "a" "b"))))) = none := by
  decide

/-- The first-failing check wins: `Xor(ForwardInput(a, b), And(Timeout(c), Timeout(e)))` has a
forward outside a `Timeout` child, but the [IO-013] check runs first. -/
theorem IO_014_order_timeoutFirst :
    refBuild (io014_build
        (.xor (.forward "a" "b") (.and (.timeout (.place "c")) (.timeout (.place "e"))))) =
      some "output spec of transition 't' has 2 Timeout nodes; an output spec has at most one, nested or not (IO-013)" := by
  decide

/-- A forward from the non-input place `x` inside a `Timeout` child fails with AC3's message. -/
theorem IO_014_ac3_rejected :
    refBuild (io014_build (.timeout (.forward "x" "b"))) =
      some "Transition 't': ForwardInput references non-input place 'x'" := by
  decide

/-! ### Firing examples -/

/-- The first transition of the firing examples: one `Exactly(2)` input arc on place `0`,
output spec `Timeout(ForwardInput(0, 1))`. -/
def io014_t : Trans Nat :=
  { core :=
      { name := "t", inputs := [{ place := 0, card := .exactly 2 }], inhibitors := [], reads := [],
        resets := [] },
    out := some (.timeout (.forward 0 1)) }

/-- The second transition of the firing examples: one `Exactly(2)` input arc on place `0`,
output spec `Timeout(And(ForwardInput(0, 1), Place(2)))`, a forward nested in the `Timeout`
child. -/
def io014_nested : Trans Nat :=
  { core :=
      { name := "u", inputs := [{ place := 0, card := .exactly 2 }], inhibitors := [], reads := [],
        resets := [] },
    out := some (.timeout (.and (.forward 0 1) (.place 2))) }

/-- The marking of the examples: two tokens in every place. -/
def io014_m : Nat → Nat := fun _ => 2

/-- The marking after a correct timed-out firing of `io014_t`: place `0` drained by 2, place `1`
up by 2. -/
def io014_m' : Nat → Nat := fun n => if n = 0 then 0 else if n = 1 then 4 else 2

/-- `io014_t`'s `Timeout` child is `ForwardInput(0, 1)`. -/
theorem io014_t_forwards : TimeoutForwards io014_t 0 1 := ⟨_, _, rfl, rfl, rfl, rfl⟩

/-- `io014_nested`'s `Timeout` child has `ForwardInput(0, 1)` under its `And`. -/
theorem io014_nested_forwards : TimeoutForwards io014_nested 0 1 :=
  ⟨_, _, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- `io014_t` has one `Timeout` node. -/
theorem io014_t_one : ∀ o, OutputSpec io014_t = some o → timeoutCount o ≤ 1 := by
  intro o ho; cases ho; decide

/-- `io014_nested` has one `Timeout` node. -/
theorem io014_nested_one :
    ∀ o, OutputSpec io014_nested = some o → timeoutCount o ≤ 1 := by
  intro o ho; cases ho; decide

/-- `io014_t` passes every build check. -/
theorem io014_t_wf : Builds io014_t := by
  refine ⟨by decide, fun o ho => ?_⟩
  cases ho
  decide

/-- The only timeout deposit of `io014_t` forwards `k 0` tokens to place `1`. -/
theorem io014_t_outcome {k : Nat → Nat} {e : List Nat} :
    TimeoutOutcome io014_t k e ↔ e = List.replicate (k 0) 1 := by
  constructor
  · rintro ⟨o, c, ho, hc, he⟩
    cases ho
    cases hc
    simpa [Out.timeoutDeposits] using he
  · rintro rfl
    exact ⟨_, _, rfl, rfl, by simp [Out.timeoutDeposits]⟩

/-- The only timeout deposit of `io014_nested` forwards `k 0` tokens to place `1` and puts one
token in place `2`. -/
theorem io014_nested_outcome {k : Nat → Nat} {e : List Nat} :
    TimeoutOutcome io014_nested k e ↔ e = List.replicate (k 0) 1 ++ [2] := by
  constructor
  · rintro ⟨o, c, ho, hc, he⟩
    cases ho
    cases hc
    simpa [Out.timeoutDeposits, cross] using he
  · rintro rfl
    exact ⟨_, _, rfl, rfl, by simp [Out.timeoutDeposits, cross]⟩

/-- A timed-out firing of `io014_t` that forwards only the first consumed token. -/
def io014_forwardFirstFire : FireRel Nat := fun t m d m' =>
  t = io014_t ∧ timedOutFireWith (fun t m p => min 1 (Consumes t m p)) t m d m'

/-- A timed-out firing of `io014_t` that forwards every consumed token twice. -/
def io014_forwardTwiceFire : FireRel Nat := fun t m d m' =>
  t = io014_t ∧ timedOutFireWith (fun t m p => 2 * Consumes t m p) t m d m'

/-- An executor that is right for a forward at the top of the `Timeout` child but forwards only
the first consumed token when the forward is nested in it: the reference everywhere except on
`io014_nested`, where its forward counts `min 1` of the consumption. -/
def io014_nestedFirstFire : FireRel Nat := fun t m d m' =>
  (t ≠ io014_nested ∧ refTimedOutFire t m d m') ∨
    (t = io014_nested ∧ timedOutFireWith (fun t m p => min 1 (Consumes t m p)) t m d m')

/-- The forward-first firing of `io014_t` from `io014_m`: one token in place `1`. -/
theorem io014_forwardFirst_fires :
    io014_forwardFirstFire io014_t io014_m [1] (fireNC io014_m io014_t.core (depProd [1])) :=
  ⟨rfl, by decide, ⟨0, rfl⟩, rfl⟩

/-- The forward-twice firing of `io014_t` from `io014_m`: four tokens in place `1`. -/
theorem io014_forwardTwice_fires :
    io014_forwardTwiceFire io014_t io014_m [1, 1, 1, 1]
      (fireNC io014_m io014_t.core (depProd [1, 1, 1, 1])) :=
  ⟨rfl, by decide, ⟨0, rfl⟩, rfl⟩

/-- The nested forward-first firing of `io014_nested` from `io014_m`: one token in place `1`
and one in place `2`, where the reference puts two in place `1`. -/
theorem io014_nestedFirst_fires :
    io014_nestedFirstFire io014_nested io014_m [1, 2]
      (fireNC io014_m io014_nested.core (depProd [1, 2])) :=
  Or.inr ⟨rfl, by decide, ⟨0, rfl⟩, rfl⟩

/-! ### Forbidden models -/

/-- ✗ Forwarding only the first consumed token violates IO-014 (fifth line, first bound):
`io014_t` consumes 2 tokens from place `0`, its only timeout deposit puts 2 in place `1`, and the
firing puts 1. -/
@[evidence forbids IO_014]
theorem IO_014_forbids_forwardFirst : ¬ IO_014 refBuild io014_forwardFirstFire := by
  intro h
  obtain ⟨e, he, hle, -⟩ :=
    h.2.2.2.2 io014_t 0 1 io014_t_one io014_t_forwards [1] _ _ io014_forwardFirst_fires
  rw [io014_t_outcome] at he
  subst he
  exact absurd (hle 1) (by decide)

/-- ✗ Forwarding every consumed token twice violates IO-014 (fifth line, second bound):
`io014_t` consumes 2 tokens from place `0`, its only timeout deposit puts 2 in place `1`, and the
firing puts 4. -/
@[evidence forbids IO_014]
theorem IO_014_forbids_forwardTwice : ¬ IO_014 refBuild io014_forwardTwiceFire := by
  intro h
  obtain ⟨e, he, -, hle⟩ :=
    h.2.2.2.2 io014_t 0 1 io014_t_one io014_t_forwards [1, 1, 1, 1] _ _ io014_forwardTwice_fires
  rw [io014_t_outcome] at he
  subst he
  exact absurd (hle 1) (by decide)

/-- ✗ Forwarding only the first consumed token at a forward nested in the `Timeout` child
violates IO-014 (fifth line): `Timeout(And(ForwardInput(0, 1), Place(2)))` has the single
timeout deposit `[1, 1, 2]`, and the firing deposits `[1, 2]`. -/
@[evidence forbids IO_014]
theorem IO_014_forbids_nestedFirst : ¬ IO_014 refBuild io014_nestedFirstFire := by
  intro h
  obtain ⟨e, he, hle, -⟩ := h.2.2.2.2 io014_nested 0 1 io014_nested_one io014_nested_forwards
    [1, 2] _ _ io014_nestedFirst_fires
  rw [io014_nested_outcome] at he
  subst he
  exact absurd (hle 1) (by decide)

/-- The spec of the bare-forward builder's counterexample: a forward outside a `Timeout` child
next to two `Timeout` nodes, every forward from the input place `a`. -/
def io014_bareMulti : Trans String :=
  io014_build (.xor (.forward "a" "b") (.and (.timeout (.place "c")) (.timeout (.place "e"))))

/-- A builder that accepts a spec with two or more `Timeout` nodes whose forwards all come from
input places, a bare forward included, and is the reference builder elsewhere. -/
def IO_014_buildSkipsMulti {N : Type} [DecidableEq N] [ToString N] (t : Trans N) :
    Option String :=
  match t.out with
  | some o =>
    if 2 ≤ timeoutCount o ∧ ∀ s ∈ forwardSources o, s ∈ inPlaces t then
      none
    else refBuild t
  | none => refBuild t

/-- ✗ A builder that accepts a forward outside a `Timeout` child violates IO-014 (first line):
`IO_014_buildSkipsMulti` builds `io014_bareMulti`. -/
@[evidence forbids IO_014]
theorem IO_014_forbids_buildSkipsMulti :
    ¬ IO_014 IO_014_buildSkipsMulti (refTimedOutFire (N := String)) := by
  intro h
  exact h.1 io014_bareMulti _ "a" "b" rfl rfl (by decide)

/-- A builder that rejects whatever the reference rejects, with one vague message. -/
def IO_014_buildVague {N : Type} [DecidableEq N] [ToString N] (t : Trans N) : Option String :=
  (refBuild t).map fun _ => "rejected"

/-- ✗ A builder that rejects a bare forward with another message violates IO-014 (second
line): `ForwardInput(a, b)` is rejected with `rejected`. -/
@[evidence forbids IO_014]
theorem IO_014_forbids_buildVague :
    ¬ IO_014 IO_014_buildVague (refTimedOutFire (N := String)) := by
  intro h
  have := h.2.1 (io014_build (.forward "a" "b")) _ "a" "b" rfl rfl (by decide) (by decide)
    (by decide) rfl
  revert this
  decide

/-- A builder that does not run AC3's check: the reference builder reading every place as an
input place. -/
def IO_014_buildNoInputCheck {N : Type} [DecidableEq N] [ToString N] (t : Trans N) :
    Option String :=
  if ¬ InputsDistinct t then some "CORE-030"
  else match t.out with
    | none => none
    | some o => checkOut t (forwardSources o) o

/-- ✗ A builder that accepts a forward from a non-input place violates IO-014 (third line):
`Timeout(ForwardInput(x, b))` builds although `x` is not an input place. -/
@[evidence forbids IO_014]
theorem IO_014_forbids_buildNoInputCheck :
    ¬ IO_014 IO_014_buildNoInputCheck (refTimedOutFire (N := String)) := by
  intro h
  exact h.2.2.1 (io014_build (.timeout (.forward "x" "b"))) _ "x" rfl (by decide) (by decide)
    (by decide)

/-- A builder that rejects every transition, with the reference message where the reference
rejects. -/
def IO_014_buildNone {N : Type} [DecidableEq N] [ToString N] (t : Trans N) : Option String :=
  some ((refBuild t).getD "rejected")

/-- ✗ A builder that rejects a well-formed transition violates IO-014 (fourth line): it rejects
`io014_t`. -/
@[evidence forbids IO_014]
theorem IO_014_forbids_buildNone : ¬ IO_014 IO_014_buildNone (refTimedOutFire (N := Nat)) := by
  intro h
  exact absurd (h.2.2.2.1 io014_t io014_t_wf) (by simp [IO_014_buildNone])

/-! ### Mutants: one per clause -/

/-- Mutant reading of IO-014 without the first line: a bare forward is constrained only when the
earlier checks pass. -/
def IO_014_mutant_dropBareRejected {N : Type} [DecidableEq N] [ToString N]
    (Build : Trans N → Option String) (T : FireRel N) : Prop :=
  IO_014_bareMessage Build ∧ IO_014_nonInputRejected Build ∧ IO_014_wfBuilds Build ∧
    IO_014_forwardCounts T

/-- `IO_014_buildSkipsMulti` agrees with the reference builder on a spec with at most one
`Timeout` node. -/
theorem IO_014_buildSkipsMulti_eq {N : Type} [DecidableEq N] [ToString N] {t : Trans N}
    {o : Out N} (ho : OutputSpec t = some o) (hc : timeoutCount o ≤ 1) :
    IO_014_buildSkipsMulti t = refBuild t := by
  have ho' : t.out = some o := ho
  simp only [IO_014_buildSkipsMulti, ho']
  rw [if_neg (by omega)]

/-- The bare-forward builder kills the first mutant: it passes every other line, but builds
`io014_bareMulti`. -/
@[evidence mutant IO_014]
theorem IO_014_mutant_dropBareRejected_killed :
    IO_014_mutant_dropBareRejected IO_014_buildSkipsMulti (refTimedOutFire (N := String)) ∧
      ¬ IO_014 IO_014_buildSkipsMulti (refTimedOutFire (N := String)) := by
  refine ⟨⟨fun t o src dst ho h hi hd hc hx => ?_, fun t o src ho hs hn => ?_, fun t hw => ?_,
    IO_014_refFire_counts⟩, IO_014_forbids_buildSkipsMulti⟩
  · rw [IO_014_buildSkipsMulti_eq ho hc]
    exact (IO_014_refBuild_bare ho h).2 hi hd hc hx
  · have ho' : t.out = some o := ho
    simp only [IO_014_buildSkipsMulti, ho']
    rw [if_neg (fun hh => hn (hh.2 src hs))]
    exact IO_014_refBuild_nonInput ho hs hn
  · have hr := IO_014_refBuild_wf hw
    cases ho : t.out with
    | none => simp only [IO_014_buildSkipsMulti, ho]; exact hr
    | some o =>
      rw [IO_014_buildSkipsMulti_eq ho (hw.2 o ho).2.1]
      exact hr

/-- Mutant reading of IO-014 without the second line: a bare forward must be rejected, with any
message. -/
def IO_014_mutant_dropBareMessage {N : Type} [DecidableEq N] [ToString N]
    (Build : Trans N → Option String) (T : FireRel N) : Prop :=
  IO_014_bareRejected Build ∧ IO_014_nonInputRejected Build ∧ IO_014_wfBuilds Build ∧
    IO_014_forwardCounts T

/-- The vague builder kills the second mutant: it rejects whatever the reference rejects and
builds whatever it builds, but not with IO-014's message. -/
@[evidence mutant IO_014]
theorem IO_014_mutant_dropBareMessage_killed :
    IO_014_mutant_dropBareMessage IO_014_buildVague (refTimedOutFire (N := String)) ∧
      ¬ IO_014 IO_014_buildVague (refTimedOutFire (N := String)) := by
  refine ⟨⟨fun t o src dst ho h => ?_, fun t o src ho hs hn => ?_, fun t hw => ?_,
    IO_014_refFire_counts⟩, IO_014_forbids_buildVague⟩
  · have := (IO_014_refBuild_bare ho h).1
    simpa [IO_014_buildVague] using this
  · have := IO_014_refBuild_nonInput ho hs hn
    simpa [IO_014_buildVague] using this
  · simp [IO_014_buildVague, IO_014_refBuild_wf hw]

/-- Mutant reading of IO-014 without the third line: a forward from a non-input place may build. -/
def IO_014_mutant_dropNonInput {N : Type} [DecidableEq N] [ToString N]
    (Build : Trans N → Option String) (T : FireRel N) : Prop :=
  IO_014_bareRejected Build ∧ IO_014_bareMessage Build ∧ IO_014_wfBuilds Build ∧
    IO_014_forwardCounts T

/-- The builder without AC3's check kills the third mutant. -/
@[evidence mutant IO_014]
theorem IO_014_mutant_dropNonInput_killed :
    IO_014_mutant_dropNonInput IO_014_buildNoInputCheck (refTimedOutFire (N := String)) ∧
      ¬ IO_014 IO_014_buildNoInputCheck (refTimedOutFire (N := String)) := by
  refine ⟨⟨fun t o src dst ho h => ?_, fun t o src dst ho h hi hd hc hx => ?_, fun t hw => ?_,
    IO_014_refFire_counts⟩, IO_014_forbids_buildNoInputCheck⟩
  · have ho' : t.out = some o := ho
    unfold IO_014_buildNoInputCheck
    split
    · simp
    · rw [ho']; exact (IO_014_checkOut_bare h).1
  · have ho' : t.out = some o := ho
    unfold IO_014_buildNoInputCheck
    rw [if_neg (not_not.mpr hi.1), ho']
    exact (IO_014_checkOut_bare h).2 hd hc hx
  · have hr := IO_014_refBuild_wf hw
    unfold IO_014_buildNoInputCheck
    rw [refBuild_of_pre hw.1] at hr
    rw [if_neg (not_not.mpr hw.1.1)]
    cases ho : t.out with
    | none => rfl
    | some o =>
      rw [ho] at hr
      obtain ⟨hd, hc, hxt, hf, -, hx⟩ := hw.2 o ho
      rw [← firstClash_eq_none_iff] at hx
      have hfind : (forwardSources o).find?
          (fun s => decide (s ∉ forwardSources o)) = none := by
        rw [List.find?_eq_none]
        intro s hm
        simpa using hm
      simp only [checkOut, (firstDup_eq_none_iff o).2 hd,
        if_neg (show ¬ 2 ≤ timeoutCount o by omega), hxt, Bool.false_eq_true, if_false, hf,
        hfind, hx]

/-- Mutant reading of IO-014 without the fourth line: building may fail on a well-formed
transition. -/
def IO_014_mutant_dropWfBuilds {N : Type} [DecidableEq N] [ToString N]
    (Build : Trans N → Option String) (T : FireRel N) : Prop :=
  IO_014_bareRejected Build ∧ IO_014_bareMessage Build ∧ IO_014_nonInputRejected Build ∧
    IO_014_forwardCounts T

/-- The reject-everything builder kills the fourth mutant: it rejects every bare forward with the
reference message and every non-input forward, but also `io014_t`. -/
@[evidence mutant IO_014]
theorem IO_014_mutant_dropWfBuilds_killed :
    IO_014_mutant_dropWfBuilds IO_014_buildNone (refTimedOutFire (N := Nat)) ∧
      ¬ IO_014 IO_014_buildNone (refTimedOutFire (N := Nat)) := by
  refine ⟨⟨fun _ _ _ _ _ _ => by simp [IO_014_buildNone],
    fun t o src dst ho h hi hd hc hx => ?_, fun _ _ _ _ _ _ => by simp [IO_014_buildNone],
    IO_014_refFire_counts⟩, IO_014_forbids_buildNone⟩
  simp [IO_014_buildNone, (IO_014_refBuild_bare ho h).2 hi hd hc hx]

/-- On `io014_t`, a timed-out firing under `timedOutFireWith k` deposits `k io014_t m 0` tokens
in place `1` and nothing else. -/
theorem io014_t_fire_deposit {k : Trans Nat → (Nat → Nat) → Nat → Nat} {m m' : Nat → Nat}
    {d : List Nat} (hf : timedOutFireWith k io014_t m d m') :
    d = List.replicate (k io014_t m 0) 1 := by
  obtain ⟨-, ⟨j, hj⟩, -⟩ := hf
  exact io014_t_outcome.mp (deposit_timedOut_outcome hj)

/-- The build lines hold of the reference builder. -/
theorem IO_014_refBuild_lines {N : Type} [DecidableEq N] [ToString N] :
    IO_014_bareRejected (refBuild (N := N)) ∧ IO_014_bareMessage (refBuild (N := N)) ∧
      IO_014_nonInputRejected (refBuild (N := N)) ∧
      IO_014_wfBuilds (refBuild (N := N)) :=
  let h := IO_014_reference (N := N); ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- Mutant reading of IO-014 that drops the fifth line's first bound: the deposit puts no more
tokens anywhere than a timeout deposit of the child, but consumed tokens may be lost. -/
def IO_014_mutant_dropNoLoss {N : Type} [DecidableEq N] [ToString N]
    (Build : Trans N → Option String) (T : FireRel N) : Prop :=
  IO_014_bareRejected Build ∧ IO_014_bareMessage Build ∧ IO_014_nonInputRejected Build ∧
    IO_014_wfBuilds Build ∧
    ∀ t src dst, (∀ o, OutputSpec t = some o → timeoutCount o ≤ 1) →
      TimeoutForwards t src dst → ∀ d,
      on (fun m m' => T t m d m'), shall (fun m _ => ∃ e, TimeoutOutcome t (Consumes t m) e ∧
        (∀ p, Deposits d p ≤ Deposits e p))

/-- The forward-first firing kills the first firing mutant: it never deposits more than the
child's timeout deposit (it forwards `min 1` of the consumption), but it loses the second token
`io014_t` consumes. -/
@[evidence mutant IO_014]
theorem IO_014_mutant_dropNoLoss_killed :
    IO_014_mutant_dropNoLoss refBuild io014_forwardFirstFire ∧
      ¬ IO_014 refBuild io014_forwardFirstFire := by
  refine ⟨⟨IO_014_refBuild_lines.1, IO_014_refBuild_lines.2.1, IO_014_refBuild_lines.2.2.1,
    IO_014_refBuild_lines.2.2.2, fun t src dst _ _ d m m' hf => ?_⟩, IO_014_forbids_forwardFirst⟩
  obtain ⟨rfl, hf⟩ := hf
  refine ⟨_, io014_t_outcome.mpr rfl, fun p => ?_⟩
  rw [io014_t_fire_deposit hf]
  simp only [Deposits, depProd, List.count_replicate]
  split <;> omega

/-- Mutant reading of IO-014 that drops the fifth line's second bound: the deposit puts at least
the child's timeout deposit everywhere, but a forward may deposit more tokens than were
consumed. -/
def IO_014_mutant_dropNoExtra {N : Type} [DecidableEq N] [ToString N]
    (Build : Trans N → Option String) (T : FireRel N) : Prop :=
  IO_014_bareRejected Build ∧ IO_014_bareMessage Build ∧ IO_014_nonInputRejected Build ∧
    IO_014_wfBuilds Build ∧
    ∀ t src dst, (∀ o, OutputSpec t = some o → timeoutCount o ≤ 1) →
      TimeoutForwards t src dst → ∀ d,
      on (fun m m' => T t m d m'), shall (fun m _ => ∃ e, TimeoutOutcome t (Consumes t m) e ∧
        (∀ p, Deposits e p ≤ Deposits d p))

/-- The forward-twice firing kills the second firing mutant: it never loses a consumed token (it
forwards twice as many), but it invents 2 tokens on `io014_t`. -/
@[evidence mutant IO_014]
theorem IO_014_mutant_dropNoExtra_killed :
    IO_014_mutant_dropNoExtra refBuild io014_forwardTwiceFire ∧
      ¬ IO_014 refBuild io014_forwardTwiceFire := by
  refine ⟨⟨IO_014_refBuild_lines.1, IO_014_refBuild_lines.2.1, IO_014_refBuild_lines.2.2.1,
    IO_014_refBuild_lines.2.2.2, fun t src dst _ _ d m m' hf => ?_⟩, IO_014_forbids_forwardTwice⟩
  obtain ⟨rfl, hf⟩ := hf
  refine ⟨_, io014_t_outcome.mpr rfl, fun p => ?_⟩
  rw [io014_t_fire_deposit hf]
  simp only [Deposits, depProd, List.count_replicate]
  split <;> omega

/-- Mutant reading of IO-014 whose fifth line covers only a `Timeout` child that is exactly
`ForwardInput(src, dst)` and counts only the tokens in `dst`. -/
def IO_014_mutant_topLevelOnly {N : Type} [DecidableEq N] [ToString N]
    (Build : Trans N → Option String) (T : FireRel N) : Prop :=
  IO_014_bareRejected Build ∧ IO_014_bareMessage Build ∧ IO_014_nonInputRejected Build ∧
    IO_014_wfBuilds Build ∧
    ∀ t src dst, (∃ o, OutputSpec t = some o ∧ o.findTimeout = some (.forward src dst)) → ∀ d,
      (on (fun m m' => T t m d m'), shall (fun m _ => Consumes t m src ≤ Deposits d dst)) ∧
      (on (fun m m' => T t m d m'), shall (fun m _ => Deposits d dst ≤ Consumes t m src))

/-- The nested forward-first executor kills the top-level-only mutant: it is the reference on
every transition whose `Timeout` child is exactly a forward, and loses a token only at the
forward nested in `io014_nested`'s `And`. -/
@[evidence mutant IO_014]
theorem IO_014_mutant_topLevelOnly_killed :
    IO_014_mutant_topLevelOnly refBuild io014_nestedFirstFire ∧
      ¬ IO_014 refBuild io014_nestedFirstFire := by
  refine ⟨⟨IO_014_refBuild_lines.1, IO_014_refBuild_lines.2.1, IO_014_refBuild_lines.2.2.1,
    IO_014_refBuild_lines.2.2.2, fun t src dst h d => ?_⟩, IO_014_forbids_nestedFirst⟩
  have hdep : ∀ m m', io014_nestedFirstFire t m d m' → Deposits d dst = Consumes t m src := by
    intro m m' hf
    rcases hf with ⟨-, -, ⟨j, hj⟩, -⟩ | ⟨rfl, -⟩
    · obtain ⟨o, ho, hc⟩ := h
      obtain ⟨o', c, ho', hc', he⟩ := deposit_timedOut_outcome hj
      rw [show OutputSpec t = t.out from rfl, ho'] at ho
      cases ho
      rw [hc] at hc'
      cases hc'
      simp only [Out.timeoutDeposits, List.mem_singleton] at he
      subst he
      exact forwardDeposit_count _ _ _
    · obtain ⟨o, ho, hc⟩ := h
      cases ho
      cases hc
  exact ⟨fun m m' hf => (hdep m m' hf).ge, fun m m' hf => (hdep m m' hf).le⟩

/-- IO-014 is exercised by the reference: the reference builder rejects a bare forward with
IO-014's message and builds `io014_t`; from `io014_m` both firing examples consume 2 tokens from
place `0`, and the timed-out reference firing of `io014_t` deposits `[1, 1]` and that of
`io014_nested` deposits `[1, 1, 2]`, both reference firings. -/
@[evidence nonvacuous IO_014]
theorem IO_014_nonvacuous :
    refBuild (io014_build (.forward "a" "b")) =
        some (msgForward (io014_build (.forward "a" "b")) "a" "b") ∧
      refBuild io014_t = none ∧
      TimeoutForwards io014_t 0 1 ∧ TimeoutForwards io014_nested 0 1 ∧
      Consumes io014_t io014_m 0 = 2 ∧ Consumes io014_nested io014_m 0 = 2 ∧
      refTimedOutFire io014_t io014_m [1, 1] io014_m' ∧
      RefFire io014_t io014_m [1, 1] io014_m' ∧
      refTimedOutFire io014_nested io014_m [1, 1, 2]
        (fireNC io014_m io014_nested.core (depProd [1, 1, 2])) ∧
      RefFire io014_nested io014_m [1, 1, 2]
        (fireNC io014_m io014_nested.core (depProd [1, 1, 2])) := by
  have hf : refTimedOutFire io014_t io014_m [1, 1] io014_m' := by
    refine ⟨by decide, ⟨0, rfl⟩, ?_⟩
    funext n
    by_cases h0 : n = 0
    · subst h0; rfl
    · by_cases h1 : n = 1
      · subst h1; rfl
      · simp [io014_m', h0, h1, fireNC, depProd, nconsumed, nspecAt, io014_t, io014_m,
          Ne.symm h0, Ne.symm h1]
  have hn : refTimedOutFire io014_nested io014_m [1, 1, 2]
      (fireNC io014_m io014_nested.core (depProd [1, 1, 2])) := ⟨by decide, ⟨0, rfl⟩, rfl⟩
  exact ⟨(IO_014_refBuild_bare rfl rfl).2 (by decide) (by decide) (by decide) rfl,
    IO_014_refBuild_wf io014_t_wf, io014_t_forwards,
    io014_nested_forwards, rfl, rfl, hf, refTimedOutFire_refFire hf, hn,
    refTimedOutFire_refFire hn⟩

end Libpetri.Spec
