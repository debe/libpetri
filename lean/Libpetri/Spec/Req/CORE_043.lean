import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryBuild
import Libpetri.Spec.Req.IO_015

set_option linter.missingDocs true

/-!
# CORE-043: Output-declaring transitions must produce (`spec/01-core-model.md`)

CORE-043 is a pure-function requirement (kind F) over a pair of checks on a built net
(`BuiltNet`, `Reference/Build.lean`): the compile check `C` and the verification entry check `V`,
each `BuiltNet N A → Option String`, where `none` means the check passes and `some n` means it
fails naming the transition `n`. A transition carries its action as an identity tag (`Act`): the
built-in passthrough action ([CORE-051]) or another action named by an opaque id, so a hand-written
action that produces nothing is never taken for the built-in.

The witnesses are `refCompile` (the first transition, in declaration order, that declares an
output specification and carries passthrough, by name) and `refVerifyEntry` (the same check: the verifier
pipeline model, `Verifier/Pipeline.lean`, does not model an entry check).

Wrong checks are killed: a compile step that never refuses (the check made at bind time only, so
the builder default slips through), a check that exempts a `Timeout`-only spec, an extensional check
that also refuses a hand-written action producing nothing, a check that names the last offender or
the offender with the least name, a check that skips source transitions, and a verification entry
point that never refuses, refuses more nets, or names another transition.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## CORE-043: Output-Declaring Transitions Must Produce -/

requirement CORE_043
  id "CORE-043"
  title "Output-Declaring Transitions Must Produce"
  kind F
  scope "every compile step and every verification entry point (state-class graph and SMT), under every property and option setting the entry point accepts"
  source verbatim "spec/01-core-model.md"
  quote "*If* a net holds a transition that declares an output spec, a `Timeout`-only spec included, and carries the built-in passthrough action ([CORE-051]), whether bound explicitly, carried because a `bindActions` mapping omitted it ([CORE-042]), or left in place as the builder default, *then* compiling the net *shall* fail with an error that names the first such transition in declaration order."
        "*If* no transition of a net both declares an output spec and carries the built-in passthrough action, *then* compiling the net *shall not* fail under this requirement."
        "*If* a transition declares no output spec, or carries an action other than the built-in passthrough, a `fork()` action ([CORE-052]) or a hand-written action that produces nothing included, *then* compiling the net *shall not* fail under this requirement naming that transition."
        "*When* a net is submitted to a verification entry point (state-class graph or SMT), under any property and option the entry point accepts, the entry point *shall* fail under this requirement exactly when compiling the submitted net does, with an error that names the same transition."
  reading "For every compile check C and every verification entry check V, each a function from a built net to none (the check passes) or some name (the check fails naming that transition):"
          "if the transitions of net b, in declaration order, are l1, then d, then l2, d declares an output specification and carries the built-in passthrough, and no transition of l1 does both, then C b fails naming d;"
          "if no transition of net b both declares an output specification and carries the built-in passthrough, then C b passes;"
          "for every net b, V b is C b: the verification entry point fails on exactly the nets compiling fails on, naming the same transition."
  assumes "A compile check (C) is the CORE-043 check of one implementation's compile step, read as a function of the built net: none when the check passes, some n when it fails (a panic or an exception) with an error naming transition n. A verification entry check (V) is the same check at one verification entry point of that implementation under one property and one option setting the entry point accepts: the state-class-graph entry point and the SMT entry point are each their own V, each setting gives its own V, and the block holds for every such V (CORE_043 C V once per entry point and setting). Other reasons a compile step or a verifier may refuse a net are not this block's subject. The message bytes are not stated: they differ by one word across the runtimes (rust/libpetri-core/src/petri_net.rs:792-799 and typescript/src/core/internal/output-action-check.ts:13-19 against java/src/main/java/org/libpetri/core/internal/OutputActionCheck.java:32-36); only that the error names the transition is stated, read as the returned name."
          "An action is read as its identity tag (Act): the built-in passthrough or another action named by an opaque id. That the built-in is one stable instance and that the identity predicate accepts it and rejects every other action is CORE-051's (line 3 of its AC list); this block reads 'carries the built-in passthrough' as action = passthrough. The third quoted sentence is lines 1 and 2 together, under the shared unique-names assumption (ruling D23): a transition that declares no output specification, or carries fork(), a hand-written action that produces nothing or any other action than the built-in, is no offender, so either the net has no offender and line 2 passes it, or line 1 names the first offender, which is another transition with another name (core043_nonOffender_unnamed, through core043_pin: the three lines determine both checks). Without unique names a non-offender that shares the first offender's name gets the same returned name, which no check over names can tell apart; the lines themselves need no unique-names premise. CORE_043_nonvacuous checks a sink, a fork()-bound and a no-op transition together, alone and next to an offender; CORE_043_forbids_extensional kills the check that also refuses the hand-written one."
          "'Declares an output spec' is read as 'has an output specification' (out is not none): an empty And or Xor cannot be built (rust/libpetri-core/src/output.rs:47, java/src/main/java/org/libpetri/core/Arc.java:274-275, typescript/src/core/out.ts:68-69), so 'non-empty output spec' (AC1) and 'output spec' name the same transitions. A Timeout-only spec, Timeout(d, ForwardInput(P, Q)), is an output specification like any other: the ForwardInput branch is deposited by the executor on the timeout outcome (IO-014), which passthrough never reaches, and line 1 does not exempt it (CORE_043_mutant_timeoutExempt_killed)."
          "'The first such transition in declaration order' is the order of the built net's transitions, the order in which they were added (CORE-040, ruling D32). All three runtimes walk the net's transitions and throw on the first offender (rust/libpetri-runtime/src/compiled_net.rs:66, java/src/main/java/org/libpetri/runtime/CompiledNet.java:101, typescript/src/runtime/compiled-net.ts:80). A check that names another offender violates line 1: the last one (CORE_043_mutant_someOffender_killed), or the one with the least name, as a walk over the transitions sorted by name would (CORE_043_forbids_nameSorted); core043_netTwo declares its offenders b then a, so both are told apart from the first. Every transition is checked, a source with no input arc included: a check placed inside the walk over input arcs skips sources and violates line 1 (CORE_043_forbids_skipSource). Transitions are identified by name (ruling D10, with the shared unique-names assumption of ruling D23)."
          "The lines range over every built net, including one no builder produced; the check reads only each transition's name, output specification and action, so a net a host can submit (one that holds only builder outputs, BuiltNet.FromBuilder) is one case of them. How a transition came to carry passthrough plays no part: the check reads the net handed to the compile step, after the builder default (CORE-051), either bindActions form (CORE-042: refBind with a resolver; mapKeep, where an omitted transition keeps its prior action, which is passthrough when it was never bound; mapClobber, where an omitted transition gets passthrough), binding on a subnet definition (MOD-051), per-instance binding (MOD-030) and channel merge (MOD-021). The first quoted sentence's 'carried because a bindActions mapping omitted it' covers both map forms. The theorems core043_builderDefault and core043_mapOmitted show the builder default and the mapClobber substitution reaching the reference check; subnet binding, per-instance binding and channel merge are the composition model's (W8), which rebuilds through the builder, so the lines already range over the nets it builds and their evidence is W8's."
          "The verification entry point is checked against the net submitted to it, under every property and option setting it accepts. A net the verifier derives from it, such as the in-flight split of VER-004 and NU-052 under PrioritySemantics CONFLICT (whose start half keeps a sink's name and action and gains an output place), is not the submitted net and is not checked under this requirement. Every runtime checks the submitted net once, before any rewrite: Rust's SMT entry point checks the net it is given (rust/libpetri-verification/src/smt_verifier.rs SmtVerifier::for_net), and the TypeScript and Java SMT entry points check the caller's net before prepare() rewrites it (typescript/src/verification/smt-verifier.ts verify and encodeScripts, requireOutputProducingActions(this.callerNet); java/src/main/java/org/libpetri/smt/SmtVerifier.java pipeline and encodeScripts, requireOutputProducingActions(callerNet)). The in-flight split gives the start half of a sink on the built-in passthrough a placeholder action that is never run (rust/libpetri-verification/src/in_flight.rs halves and placeholder_action; java/src/main/java/org/libpetri/analysis/InFlight.java START_ACTION; typescript/src/verification/in-flight.ts NEVER_RUN_ACTION), and keeps every other action, so the checks the state-class graph builders make on the derived net (rust/libpetri-verification/src/nu_scg_verifier.rs verify_name_scg and state_class_graph.rs StateClassGraph::build_core, java/src/main/java/org/libpetri/analysis/StateClassGraph.java initial class) pass on it exactly when compiling the submitted net does; the Python binding rides on Rust. A verifier that runs the check on the derived split net, whose start half keeps a sink's passthrough and gains an output place, refuses under CONFLICT a net that compiles and violates line 3 (the behaviour RD-08 in spec/runtime-defects.md recorded of all three runtimes and Python); so does a reused verifier that checks the net its previous call left rewritten instead of the one submitted (the behaviour RD-47 recorded of Java's SmtVerifier). The tests: rust smt_verifier.rs core043_conflict_split_of_a_passthrough_sink_is_not_refused; java SplitDemandTest CORE043_aConflictSplitOfAPassthroughSinkIsNotRefused and CORE043_aReusedVerifierChecksTheCallersNet; typescript tests/verification/smt-verifier-core043.test.ts; python tests/test_smoke.py test_core_043_conflict_split_of_a_passthrough_sink_is_not_refused. The environment transitions of a VER-022 contract are not transitions of the submitted net and are not checked (VER-022: 'Their actions never run, so one that declares outputs gets a placeholder action instead of a [CORE-043] refusal'). The verifier pipeline model (Verifier/Pipeline.lean, the block VER_003) does not model the entry check: its decider starts from the property-place refusal, so the reference entry check is refVerifyEntry = refCompile (refVerifyEntry_eq) and line 3's holds evidence is true by definition. That every verifier entry point runs the check is test evidence (kind Q), the runtime sites named above."
          "The body's 'compiling or verifying such a net MUST fail' is lines 1 and 3; 'one check there covers the builder default, either bindActions form, binding on a subnet definition, per-instance binding and channel merge alike' is the reading above that the check reads the net, not the binding. 'Such a transition can never fire usefully' is a consequence: an output specification never offers an empty deposit to an action outcome (core043_no_empty_action_deposit, every branch names a place: branches_ne_nil_mem), so under IO-015 the empty output of passthrough fails validation on every firing (IO_015_ac6); on a net that passes the check, a transition carrying passthrough has no output specification and its empty deposit is the one its spec offers (core043_passthrough_sink). 'Verification does not compensate' and 'the rule is unconditional' (it does not depend on the CONC-026 validation opt-out) are why the check exists, not further lines: the check reads no executor option."
          "AC1 (compiling errors when a transition with a non-empty output spec carries passthrough, bound explicitly, substituted by a bindActions mapping or left as the builder default, a Timeout-only spec included) is line 1, with the readings above; a compile step that never refuses (a check made at bind time only, which misses the builder default) violates it (CORE_043_forbids_bindTimeOnly), and so does one that exempts a Timeout-only spec (CORE_043_mutant_timeoutExempt_killed) or skips a source transition (CORE_043_forbids_skipSource). CORE_043_nonvacuous computes the four cases of the test derivation on the reference, and a source transition."
          "AC2 (the error names the offending transition, the first one in declaration order when there are several) is line 1's 'fails naming d'."
          "AC3 (submitting the same net to a verification entry point fails the same way) is line 3, once per entry point and option setting; a verification entry point that never refuses violates it (CORE_043_forbids_verifyNever), and so do the readings 'refuses at least the nets compiling refuses' (CORE_043_mutant_verifyCovers_killed) and 'refuses the same nets, naming any transition' (CORE_043_mutant_sameNets_killed)."
          "AC4 (a sink may carry passthrough; CORE-042 is untouched) is line 2 on a net whose transitions carrying passthrough have no output specification, and the third quoted sentence on a net that also holds an offender. That binding stays lazy and total is CORE-042's line, not restated here."
          "AC5 (the built-in is recognised by identity, so a hand-written action that produces nothing is not claimed) is line 2 and the third quoted sentence read over the identity tag; the extensional reading of the whole check (an output-declaring transition is refused when its action produces nothing) is CORE_043_mutant_extensional, killed by the extensional check. That such an action fails at run time is IO-015's."
  signoff "2026-11-13 fcb226a000337de7 ai"
  statement : ∀ {N A : Type}, (BuiltNet N A → Option String) → (BuiltNet N A → Option String) → Prop :=
    fun C V =>
      (∀ b l₁ d l₂, b.trans = l₁ ++ d :: l₂ → d.out ≠ none → d.action = .passthrough →
        (∀ e ∈ l₁, e.out ≠ none → e.action ≠ .passthrough) → C b = some d.core.name) ∧
      (∀ b, (∀ d ∈ b.trans, d.out ≠ none → d.action ≠ .passthrough) → C b = none) ∧
      (∀ b, V b = C b)

/- The pinned readable form of CORE-043: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CORE_043 : {N A : Type} → (BuiltNet N A → Option String) → (BuiltNet N A → Option String) → Prop :=
fun {N A} C V =>
  (∀ (b : BuiltNet N A) (l₁ : List (TransDef N A)) (d : TransDef N A) (l₂ : List (TransDef N A)),
      b.trans = l₁ ++ d :: l₂ →
        d.out ≠ none →
          d.action = Act.passthrough → (∀ e ∈ l₁, e.out ≠ none → e.action ≠ Act.passthrough) → C b = some d.core.name) ∧
    (∀ (b : BuiltNet N A), (∀ d ∈ b.trans, d.out ≠ none → d.action ≠ Act.passthrough) → C b = none) ∧
      ∀ (b : BuiltNet N A), V b = C b
-/
#guard_msgs in #print CORE_043

/-! ### The three lines over an offender predicate (for the mutants) -/

section Lines

variable {N A : Type}

/-- The pairing CORE-043 rejects: an output specification and the built-in passthrough. -/
def core043_offPT (d : TransDef N A) : Prop := d.out ≠ none ∧ d.action = .passthrough

/-- The three lines of CORE-043 with the offending transitions given by `off`: the first offender
in declaration order is named, a net without one passes, and the entry check is the compile
check. -/
def core043_with (off : TransDef N A → Prop) (C V : BuiltNet N A → Option String) : Prop :=
  (∀ b l₁ d l₂, b.trans = l₁ ++ d :: l₂ → off d → (∀ e ∈ l₁, ¬ off e) → C b = some d.core.name) ∧
  (∀ b, (∀ d ∈ b.trans, ¬ off d) → C b = none) ∧
  (∀ b, V b = C b)

/-- CORE-043 is its three lines with the offender predicate `core043_offPT`. -/
theorem core043_iff_with (C V : BuiltNet N A → Option String) :
    CORE_043 C V ↔ core043_with core043_offPT C V := by
  unfold CORE_043 core043_with core043_offPT
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun b l₁ d l₂ he hd hl => h1 b l₁ d l₂ he hd.1 hd.2 fun e he' ho hp => hl e he' ⟨ho, hp⟩,
      fun b hn => h2 b fun d hd ho hp => hn d hd ⟨ho, hp⟩, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun b l₁ d l₂ he ho hp hl => h1 b l₁ d l₂ he ⟨ho, hp⟩ fun e he' hc => hl e he' hc.1 hc.2,
      fun b hn => h2 b fun d hd hc => hn d hd hc.1 hc.2, h3⟩

/-- The check that names the first transition, in declaration order, satisfying `p`. -/
def core043_firstWith (p : TransDef N A → Bool) (b : BuiltNet N A) : Option String :=
  (b.trans.find? p).map (·.core.name)

/-- The first-offender check meets the three lines for its own offender predicate. -/
theorem core043_firstWith_lines (p : TransDef N A → Bool) :
    core043_with (fun d => p d = true) (core043_firstWith p) (core043_firstWith p) := by
  refine ⟨fun b l₁ d l₂ he hd hl => ?_, fun b hn => ?_, fun _ => rfl⟩
  · have h0 : l₁.find? p = none := List.find?_eq_none.2 fun e he' => by simpa using hl e he'
    have hd' : p d = true := hd
    simp only [core043_firstWith, he, List.find?_append, h0, Option.none_or,
      List.find?_cons_of_pos hd', Option.map_some]
  · have h0 : b.trans.find? p = none := List.find?_eq_none.2 fun e he' => by simpa using hn e he'
    simp only [core043_firstWith, h0, Option.map_none]

/-- The reference compile check is the first-offender check for the passthrough pairing. -/
theorem refCompile_eq_firstWith :
    (refCompile : BuiltNet N A → Option String) = core043_firstWith TransDef.outputPassthrough :=
  rfl

end Lines

/-! ### The reference -/

/-- ✓ The reference checks satisfy CORE-043: `refCompile` names the first transition in
declaration order that declares an output specification and carries passthrough, passes a net
without one, and `refVerifyEntry` is `refCompile`. -/
@[evidence holds CORE_043]
theorem CORE_043_reference {N A : Type} :
    CORE_043 (refCompile (N := N) (A := A)) refVerifyEntry := by
  refine ⟨fun b l₁ d l₂ he ho hp hl => ?_, fun b hn => refCompile_eq_none_iff.2 hn, fun _ => rfl⟩
  exact refCompile_eq_some_iff.2 ⟨l₁, d, l₂, he, ho, hp, rfl, fun e he' hc => hl e he' hc.1 hc.2⟩

/-- The three lines determine both checks: lines 1 and 2 cover every net (it has a first offender
or none), so a compile check meeting them is `refCompile`, and line 3 makes the entry check equal to
it. A wrong check that differs from the reference on one built net is rejected. -/
theorem core043_pin {N A : Type} (C V : BuiltNet N A → Option String) (h : CORE_043 C V) :
    C = refCompile ∧ V = refCompile := by
  obtain ⟨h1, h2, h3⟩ := h
  have hC : C = refCompile := by
    funext b
    cases hc : refCompile b with
    | none => exact h2 b (refCompile_eq_none_iff.1 hc)
    | some n =>
      obtain ⟨l₁, d, l₂, he, ho, hp, rfl, hl⟩ := refCompile_eq_some_iff.1 hc
      exact h1 b l₁ d l₂ he ho hp fun e he' ho' hp' => hl e he' ⟨ho', hp'⟩
  exact ⟨hC, funext fun b => (h3 b).trans (congrFun hC b)⟩

/-- The third quoted sentence, from lines 1 and 2: on a net whose transition names are unique
(ruling D23), a transition that declares no output specification or carries an action other than
the built-in passthrough is never the one a check meeting CORE-043 names. -/
theorem core043_nonOffender_unnamed {N A : Type} {C V : BuiltNet N A → Option String}
    (h : CORE_043 C V) {b : BuiltNet N A} (hu : (b.trans.map (·.core.name)).Nodup)
    {d : TransDef N A} (hd : d ∈ b.trans) (hn : ¬ (d.out ≠ none ∧ d.action = .passthrough)) :
    C b ≠ some d.core.name := by
  rw [(core043_pin C V h).1]
  intro hc
  obtain ⟨e, he, ho, hp, hname⟩ := refCompile_some_mem hc
  have : e = d := List.inj_on_of_nodup_map hu he hd hname
  exact hn (this ▸ ⟨ho, hp⟩)

/-! ### How passthrough reaches the check (AC1) -/

/-- The builder default reaches the check (AC1): a transition built by the reference builder
without an action and with an output specification makes the reference compile check fail on every
net the reference net builder builds from it. -/
theorem core043_builderDefault {N A : Type} [DecidableEq N] [ToString N] {k : Nat}
    {i : TransIn N A} {x : (refTransBuild (N := N) (A := A)).I}
    (hx : (refTransBuild (N := N) (A := A)).build k i = .ok x) (ho : i.out ≠ none)
    (ha : i.action = none) {inp : NetIn (refTransBuild (N := N) (A := A))} {b : BuiltNet N A}
    (hb : refNetBuild inp = .ok b) (hmem : x ∈ inp.trans) : (refCompile b).isSome := by
  have hd : (refTransBuild (N := N) (A := A)).defOf x = i.resolve := by
    show x.1.2 = i.resolve
    rw [refTransBuild_def hx]
  refine refCompile_isSome (d := i.resolve) ?_ ho (resolve_action_none ha)
  rw [refNetBuild_trans hb, ← hd]
  exact List.mem_map_of_mem hmem

/-- The map form's substitution reaches the check (AC1): binding with a map that omits an
output-declaring transition, as Java and TypeScript read the map form (`mapClobber`), makes the
reference compile check fail. -/
theorem core043_mapOmitted {N A : Type} {b : BuiltNet N A} {d : TransDef N A}
    {m : String → Option (Act A)} (hd : d ∈ b.trans) (ho : d.out ≠ none)
    (hm : m d.core.name = none) : (refCompile (refBind b (mapClobber m))).isSome := by
  refine refCompile_isSome (d := d.bindWith (mapClobber m)) ?_ ho ?_
  · exact List.mem_map_of_mem hd
  · simp [TransDef.bindWith, mapClobber, hm]

/-! ### Why the pairing is rejected, and what passing the check gives -/

/-- An output specification never offers an empty deposit to an action outcome: every branch
names at least one place (`branches_ne_nil_mem`). So passthrough, which emits nothing, has no
action firing on a transition with an output specification, and fails IO-015's validation on
every completion (`IO_015_ac6`). -/
theorem core043_no_empty_action_deposit {N : Type} (o : Out N) (c : N → Nat) (i : Nat) :
    deposit c (some o) (.action i) ≠ some [] := by
  intro h
  exact branches_ne_nil_mem o [] (List.mem_of_getElem? h) rfl

/-- On a net that passes the reference compile check, a transition carrying passthrough has no
output specification, and the empty deposit is the one its spec offers to the action outcome. -/
theorem core043_passthrough_sink {N A : Type} {b : BuiltNet N A} (h : refCompile b = none)
    {d : TransDef N A} (hd : d ∈ b.trans) (hp : d.action = .passthrough) :
    d.toTrans.out = none ∧ ∀ c, deposit c d.toTrans.out (.action 0) = some [] := by
  have ho : d.out = none := Classical.byContradiction fun ho => refCompile_eq_none_iff.1 h d hd ho hp
  exact ⟨ho, fun c => by simp [TransDef.toTrans, ho, deposit]⟩

/-! ### Examples (places and action ids are strings) -/

/-- A transition `n` with one input arc on `p`, output specification `out` and action `act` (absent
= the builder default), as the reference builder resolves it. -/
def core043_def (n : String) (out : Option (Out String)) (act : Option (Act String)) :
    TransDef String String :=
  ({ core := ⟨n, [⟨"p", .one⟩], [], [], []⟩, out := out, action := act } : TransIn String String).resolve

/-- A net of the given transitions on places `p` and `q`. -/
def core043_net (ts : List (TransDef String String)) : BuiltNet String String := ⟨["p", "q"], ts, []⟩

/-- `t` declares `Place(q)` and carries the builder default. -/
def core043_netDefault : BuiltNet String String := core043_net [core043_def "t" (some (.place "q")) none]

/-- `t` declares `Place(q)` and is bound to the action `fork`. -/
def core043_netFork : BuiltNet String String :=
  core043_net [core043_def "t" (some (.place "q")) (some (.other "fork"))]

/-- `t` declares `Timeout(ForwardInput(p, q))` (the duration is not modelled) and carries the
builder default. -/
def core043_netTimeout : BuiltNet String String :=
  core043_net [core043_def "t" (some (.timeout (.forward "p" "q"))) none]

/-- A sink `s` carrying passthrough, `f` declaring `Place(q)` bound to `fork`, and `h` declaring
`Place(q)` bound to a hand-written action `noop` that produces nothing. -/
def core043_netPass : BuiltNet String String :=
  core043_net [core043_def "s" none none, core043_def "f" (some (.place "q")) (some (.other "fork")),
    core043_def "h" (some (.place "q")) (some (.other "noop"))]

/-- A sink `s`, the `fork`-bound `f` and the no-op `h`, then two offenders declared `b` then `a`
(against name order, so the first offender is neither the last nor the least by name). -/
def core043_netTwo : BuiltNet String String :=
  core043_net [core043_def "s" none none, core043_def "f" (some (.place "q")) (some (.other "fork")),
    core043_def "h" (some (.place "q")) (some (.other "noop")),
    core043_def "b" (some (.place "q")) none, core043_def "a" (some (.place "q")) none]

/-- A source `src`, with no input arc, declaring `Place(q)` and carrying the builder default. -/
def core043_src : TransDef String String :=
  ({ core := ⟨"src", [], [], [], []⟩, out := some (.place "q"), action := none } :
    TransIn String String).resolve

/-- The net of the source `src` alone. -/
def core043_netSource : BuiltNet String String := core043_net [core043_src]

/-- ✓ Every line of CORE-043 is exercised by the reference, on the test derivation's nets: the
builder default, passthrough bound explicitly, passthrough substituted because a map omitted the
transition (`mapClobber`, Java and TypeScript), and a `Timeout`-only spec each make compiling fail
naming `t` (line 1, AC1, AC2); a source with no input arc is checked (line 1); of two offenders
declared `b` then `a` the first, `b`, is named, not the sink, the `fork`-bound or the no-op
transition before it (line 1, third quoted sentence); a sink with passthrough, a `fork`-bound
transition and a hand-written no-op pass (line 2, AC4, AC5); the verification entry check gives the
same answers (line 3, AC3). -/
@[evidence nonvacuous CORE_043]
theorem CORE_043_nonvacuous :
    refCompile core043_netDefault = some "t" ∧
    refCompile (refBind core043_netFork fun n => if n = "t" then some .passthrough else none) =
      some "t" ∧
    refCompile (refBind core043_netFork (mapClobber fun n => if n = "u" then some (.other "fork") else none)) =
      some "t" ∧
    refCompile core043_netTimeout = some "t" ∧
    refCompile core043_netSource = some "src" ∧
    refCompile core043_netTwo = some "b" ∧
    refCompile core043_netPass = none ∧
    refVerifyEntry core043_netDefault = some "t" ∧
    refVerifyEntry core043_netTimeout = some "t" ∧
    refVerifyEntry core043_netTwo = some "b" ∧
    refVerifyEntry core043_netPass = none := by
  decide

/-! ### Wrong checks -/

/-- A compile step that never refuses: the check made at bind time only, which never sees the
builder default. -/
def core043_never {N A : Type} : BuiltNet N A → Option String := fun _ => none

/-- `noop` produces nothing: the action ids a static analysis of the action could flag. -/
def core043_isNoop (a : String) : Bool := a == "noop"

/-- The extensional offender: an output specification and an action that produces nothing, the
built-in or one whose id `noop` flags. -/
def core043_extPred {N A : Type} (noop : A → Bool) (d : TransDef N A) : Bool :=
  d.out.isSome && match d.action with
    | .passthrough => true
    | .other a => noop a

/-- The extensional check: refuses an output-declaring transition whose action produces nothing,
the built-in or a hand-written one (`noop` decides which ids produce nothing). -/
def core043_extCompile {N A : Type} (noop : A → Bool) : BuiltNet N A → Option String :=
  core043_firstWith (core043_extPred noop)

/-- The output specification is a `Timeout` node at the root. -/
def core043_timeoutRoot {N : Type} : Option (Out N) → Bool
  | some (.timeout _) => true
  | _ => false

/-- The check that exempts a `Timeout`-only spec. -/
def core043_timeoutExempt {N A : Type} : BuiltNet N A → Option String :=
  core043_firstWith fun d => d.outputPassthrough && !core043_timeoutRoot d.out

/-- The check that names the last offender. -/
def core043_lastCompile {N A : Type} (b : BuiltNet N A) : Option String :=
  (b.trans.reverse.find? TransDef.outputPassthrough).map (·.core.name)

/-- Insert by name: one step of a stable insertion sort. -/
def core043_insertByName (d : TransDef String String) :
    List (TransDef String String) → List (TransDef String String)
  | [] => [d]
  | e :: es => if d.core.name ≤ e.core.name then d :: e :: es else e :: core043_insertByName d es

/-- The check that walks the transitions sorted by name, as a compile step that sorts its
transitions the way it sorts place names would: it names the offender with the least name. -/
def core043_nameSorted (b : BuiltNet String String) : Option String :=
  ((b.trans.foldr core043_insertByName []).find? TransDef.outputPassthrough).map (·.core.name)

/-- The check made inside the walk over input arcs: a source transition, with no input arc, is
never checked. -/
def core043_skipSource {N A : Type} : BuiltNet N A → Option String :=
  core043_firstWith fun d => d.outputPassthrough && !d.core.inputs.isEmpty

/-- A verification entry point that refuses every net. -/
def core043_always {N A : Type} : BuiltNet N A → Option String := fun _ => some "refused"

/-- ✗ A compile step that never refuses (the check at bind time only) violates CORE-043 (line 1,
AC1): the net whose transition carries the builder default compiles. -/
@[evidence forbids CORE_043]
theorem CORE_043_forbids_bindTimeOnly :
    ¬ CORE_043 (core043_never (N := String) (A := String)) core043_never := by
  intro h
  have := h.1 core043_netDefault [] (core043_def "t" (some (.place "q")) none) [] rfl
    (by simp [core043_def, TransIn.resolve]) (by simp [core043_def, TransIn.resolve]) (by simp)
  exact absurd this (by simp [core043_never])

/-- ✗ A verification entry point that never refuses violates CORE-043 (line 3, AC3): it
green-lights the net the compile check refuses. -/
@[evidence forbids CORE_043]
theorem CORE_043_forbids_verifyNever :
    ¬ CORE_043 (refCompile (N := String) (A := String)) core043_never := by
  intro h
  have := h.2.2 core043_netDefault
  exact absurd this (by decide)

/-- ✗ The extensional check violates CORE-043 (line 2, AC5): it refuses the net whose
output-declaring transitions carry `fork` and a hand-written no-op. -/
@[evidence forbids CORE_043]
theorem CORE_043_forbids_extensional :
    ¬ CORE_043 (core043_extCompile (N := String) core043_isNoop)
      (core043_extCompile core043_isNoop) := by
  intro h
  have := h.2.1 core043_netPass (by decide)
  exact absurd this (by decide)

/-- ✗ The name-sorted check violates CORE-043 (line 1, AC2): of the offenders declared `b` then
`a` it names `a`, the least name, not the first. -/
@[evidence forbids CORE_043]
theorem CORE_043_forbids_nameSorted : ¬ CORE_043 core043_nameSorted core043_nameSorted := by
  intro h
  have := h.1 core043_netTwo [core043_def "s" none none,
      core043_def "f" (some (.place "q")) (some (.other "fork")),
      core043_def "h" (some (.place "q")) (some (.other "noop"))]
    (core043_def "b" (some (.place "q")) none) [core043_def "a" (some (.place "q")) none] rfl
    (by simp [core043_def, TransIn.resolve]) (by simp [core043_def, TransIn.resolve])
    (by simp [core043_def, TransIn.resolve])
  exact absurd this (by decide)

/-- ✗ The check that skips source transitions violates CORE-043 (line 1, AC1): the net of the
source `src`, which declares `Place(q)` and carries the builder default, compiles. -/
@[evidence forbids CORE_043]
theorem CORE_043_forbids_skipSource :
    ¬ CORE_043 (core043_skipSource (N := String) (A := String)) core043_skipSource := by
  intro h
  have := h.1 core043_netSource [] core043_src [] rfl (by simp [core043_src, TransIn.resolve])
    (by simp [core043_src, TransIn.resolve]) (by simp)
  exact absurd this (by decide)

/-! ### Mutants, one per load-bearing reading -/

section Mutants

variable {N A : Type}

/-- Mutant reading of line 1 (AC1): a `Timeout`-only spec is exempt; lines 2 and 3 read with the
same exemption. -/
def CORE_043_mutant_timeoutExempt (C V : BuiltNet N A → Option String) : Prop :=
  core043_with (fun d => core043_offPT d ∧ core043_timeoutRoot d.out = false) C V

/-- Mutant reading of lines 1 and 2 (AC5): the extensional check, refusing an output-declaring
transition whose action produces nothing (`noop`), the built-in or a hand-written one. -/
def CORE_043_mutant_extensional (noop : A → Bool) (C V : BuiltNet N A → Option String) : Prop :=
  core043_with (fun d => d.out ≠ none ∧
    (d.action = .passthrough ∨ ∃ a, d.action = .other a ∧ noop a = true)) C V

/-- Mutant reading of line 1 (AC2 without "first"): when some transition is an offender, the
check fails naming some offender. Lines 2 and 3 are as in CORE-043. -/
def CORE_043_mutant_someOffender (C V : BuiltNet N A → Option String) : Prop :=
  (∀ b, ∀ d ∈ b.trans, d.out ≠ none → d.action = .passthrough →
    ∃ e ∈ b.trans, e.out ≠ none ∧ e.action = .passthrough ∧ C b = some e.core.name) ∧
  (∀ b, (∀ d ∈ b.trans, d.out ≠ none → d.action ≠ .passthrough) → C b = none) ∧
  (∀ b, V b = C b)

/-- Mutant reading of line 3 (AC3 as "verification cannot green-light a net that will not
compile"): the entry check refuses at least the nets the compile check refuses. Lines 1 and 2 are
as in CORE-043. -/
def CORE_043_mutant_verifyCovers (C V : BuiltNet N A → Option String) : Prop :=
  (∀ b l₁ d l₂, b.trans = l₁ ++ d :: l₂ → d.out ≠ none → d.action = .passthrough →
    (∀ e ∈ l₁, e.out ≠ none → e.action ≠ .passthrough) → C b = some d.core.name) ∧
  (∀ b, (∀ d ∈ b.trans, d.out ≠ none → d.action ≠ .passthrough) → C b = none) ∧
  (∀ b, (C b).isSome → (V b).isSome)

/-- Mutant reading of line 3 ("fails the same way" as "refuses the same nets"): the entry check
refuses exactly the nets the compile check refuses, naming any transition. Lines 1 and 2 are as in
CORE-043. -/
def CORE_043_mutant_sameNets (C V : BuiltNet N A → Option String) : Prop :=
  (∀ b l₁ d l₂, b.trans = l₁ ++ d :: l₂ → d.out ≠ none → d.action = .passthrough →
    (∀ e ∈ l₁, e.out ≠ none → e.action ≠ .passthrough) → C b = some d.core.name) ∧
  (∀ b, (∀ d ∈ b.trans, d.out ≠ none → d.action ≠ .passthrough) → C b = none) ∧
  (∀ b, (V b).isSome = (C b).isSome)

end Mutants

/-- The timeout-exempting check kills the mutant: it meets the exempting reading, but compiles the
net whose `Timeout`-only transition carries the builder default (line 1). -/
@[evidence mutant CORE_043]
theorem CORE_043_mutant_timeoutExempt_killed :
    CORE_043_mutant_timeoutExempt (core043_timeoutExempt (N := String) (A := String))
      core043_timeoutExempt ∧
    ¬ CORE_043 (core043_timeoutExempt (N := String) (A := String)) core043_timeoutExempt := by
  refine ⟨?_, fun h => ?_⟩
  · have := core043_firstWith_lines (N := String) (A := String)
      fun d => d.outputPassthrough && !core043_timeoutRoot d.out
    refine ⟨fun b l₁ d l₂ he hd hl => this.1 b l₁ d l₂ he ?_ fun e he' hc => hl e he' ?_,
      fun b hn => this.2.1 b fun d hd hc => hn d hd ?_, this.2.2⟩
    · simp only [Bool.and_eq_true, Bool.not_eq_true', TransDef.outputPassthrough_iff]
      exact ⟨⟨hd.1.1, hd.1.2⟩, hd.2⟩
    · simp only [Bool.and_eq_true, Bool.not_eq_true', TransDef.outputPassthrough_iff] at hc
      exact ⟨⟨hc.1.1, hc.1.2⟩, hc.2⟩
    · simp only [Bool.and_eq_true, Bool.not_eq_true', TransDef.outputPassthrough_iff] at hc
      exact ⟨⟨hc.1.1, hc.1.2⟩, hc.2⟩
  · have := h.1 core043_netTimeout [] (core043_def "t" (some (.timeout (.forward "p" "q"))) none) []
      rfl (by simp [core043_def, TransIn.resolve]) (by simp [core043_def, TransIn.resolve]) (by simp)
    exact absurd this (by decide)

/-- The extensional check kills the mutant: it meets the extensional reading, but refuses the net
whose output-declaring transitions carry `fork` and a hand-written no-op (line 2). -/
@[evidence mutant CORE_043]
theorem CORE_043_mutant_extensional_killed :
    CORE_043_mutant_extensional core043_isNoop
      (core043_extCompile (N := String) core043_isNoop) (core043_extCompile core043_isNoop) ∧
    ¬ CORE_043 (core043_extCompile (N := String) core043_isNoop) (core043_extCompile core043_isNoop) := by
  refine ⟨?_, CORE_043_forbids_extensional⟩
  have key : ∀ d : TransDef String String, core043_extPred core043_isNoop d = true ↔
      (d.out ≠ none ∧ (d.action = .passthrough ∨ ∃ a, d.action = .other a ∧ core043_isNoop a = true)) := by
    intro d
    rcases d with ⟨c, o, tm, pr, act⟩
    cases act <;> simp [core043_extPred, Option.isSome_iff_ne_none]
  have := core043_firstWith_lines (N := String) (A := String) (core043_extPred core043_isNoop)
  refine ⟨fun b l₁ d l₂ he hd hl => this.1 b l₁ d l₂ he ((key d).2 hd)
      fun e he' hc => hl e he' ((key e).1 hc),
    fun b hn => this.2.1 b fun d hd hc => hn d hd ((key d).1 hc), this.2.2⟩

/-- The last-offender check kills the mutant: it names an offender whenever there is one, but of
the two offenders declared `b` then `a` it names `a`, not the first (line 1). -/
@[evidence mutant CORE_043]
theorem CORE_043_mutant_someOffender_killed :
    CORE_043_mutant_someOffender (core043_lastCompile (N := String) (A := String))
      core043_lastCompile ∧
    ¬ CORE_043 (core043_lastCompile (N := String) (A := String)) core043_lastCompile := by
  refine ⟨⟨fun b d hd ho hp => ?_, fun b hn => ?_, fun _ => rfl⟩, fun h => ?_⟩
  · cases hf : b.trans.reverse.find? TransDef.outputPassthrough with
    | none =>
      have := List.find?_eq_none.1 hf d (List.mem_reverse.2 hd)
      rw [Bool.not_eq_true, ← Bool.not_eq_true, TransDef.outputPassthrough_iff] at this
      exact absurd ⟨ho, hp⟩ this
    | some e =>
      have he := List.mem_reverse.1 (List.mem_of_find?_eq_some hf)
      have hpe := TransDef.outputPassthrough_iff.1 (List.find?_some hf)
      exact ⟨e, he, hpe.1, hpe.2, by simp [core043_lastCompile, hf]⟩
  · have : b.trans.reverse.find? TransDef.outputPassthrough = none :=
      List.find?_eq_none.2 fun e he hc =>
        hn e (List.mem_reverse.1 he) (TransDef.outputPassthrough_iff.1 hc).1
          (TransDef.outputPassthrough_iff.1 hc).2
    simp [core043_lastCompile, this]
  · have := h.1 core043_netTwo [core043_def "s" none none,
        core043_def "f" (some (.place "q")) (some (.other "fork")),
        core043_def "h" (some (.place "q")) (some (.other "noop"))]
      (core043_def "b" (some (.place "q")) none) [core043_def "a" (some (.place "q")) none] rfl
      (by simp [core043_def, TransIn.resolve]) (by simp [core043_def, TransIn.resolve])
      (by simp [core043_def, TransIn.resolve])
    exact absurd this (by decide)

/-- The always-refusing entry point kills the mutant: it refuses every net the compile check
refuses, but also the net the compile check passes (line 3). -/
@[evidence mutant CORE_043]
theorem CORE_043_mutant_verifyCovers_killed :
    CORE_043_mutant_verifyCovers (refCompile (N := String) (A := String)) core043_always ∧
    ¬ CORE_043 (refCompile (N := String) (A := String)) core043_always := by
  obtain ⟨h1, h2, -⟩ := CORE_043_reference (N := String) (A := String)
  refine ⟨⟨h1, h2, fun _ _ => rfl⟩, fun h => ?_⟩
  have := h.2.2 core043_netPass
  exact absurd this (by decide)

/-- The last-offender entry point kills the mutant: it refuses exactly the nets the compile check
refuses, but on the net with offenders declared `b` then `a` it names `a` where compiling names `b`
(line 3). -/
@[evidence mutant CORE_043]
theorem CORE_043_mutant_sameNets_killed :
    CORE_043_mutant_sameNets (refCompile (N := String) (A := String)) core043_lastCompile ∧
    ¬ CORE_043 (refCompile (N := String) (A := String)) core043_lastCompile := by
  obtain ⟨h1, h2, -⟩ := CORE_043_reference (N := String) (A := String)
  obtain ⟨⟨hs, -, -⟩, -⟩ := CORE_043_mutant_someOffender_killed
  refine ⟨⟨h1, h2, fun b => ?_⟩, fun h => ?_⟩
  · cases hc : refCompile b with
    | none =>
      have hn := refCompile_eq_none_iff.1 hc
      have : core043_lastCompile b = none := by
        have : b.trans.reverse.find? TransDef.outputPassthrough = none :=
          List.find?_eq_none.2 fun e he hc' =>
            hn e (List.mem_reverse.1 he) (TransDef.outputPassthrough_iff.1 hc').1
              (TransDef.outputPassthrough_iff.1 hc').2
        simp [core043_lastCompile, this]
      rw [this]
    | some n =>
      obtain ⟨d, hd, ho, hp, -⟩ := refCompile_some_mem hc
      obtain ⟨e, -, -, -, he⟩ := hs b d hd ho hp
      rw [he]; rfl
  · have := h.2.2 core043_netTwo
    exact absurd this (by decide)

end Libpetri.Spec
