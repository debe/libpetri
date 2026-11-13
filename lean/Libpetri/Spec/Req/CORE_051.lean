import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.Req.CORE_050
import Libpetri.Spec.Req.CORE_020
import Libpetri.Spec.Req.CORE_052

set_option linter.missingDocs true

/-!
# CORE-051: Passthrough action (`spec/01-core-model.md`)

CORE-051 is a pure-function requirement (kind F) over four parts of one implementation:

* `interp : Act A → ActionRel N T`, the action an identity tag names (`Act`,
  `Reference/Build.lean`: the built-in passthrough or another action named by an id);
* `isPT : Act A → Bool`, the identity predicate (`is_passthrough` in Rust, `isPassthrough` in
  Java and TypeScript);
* `B : TBuilder N A`, the transition builder of CORE-020;
* `pt : Nat → Act A`, the `k`-th retrieval of the built-in (`passthrough()`).

The four lines: passthrough completes with no token and never fails; the identity predicate holds
of the built-in tag and of nothing else; a transition built without an action carries the
built-in; every retrieval yields the same instance, which the predicate accepts. The witness is
`Act.interp I` (for every table `I` of other actions), `Act.isPassthrough` (the predicate the
CORE-043 compile check reads), `refTransBuild` and `refRetrievePassthrough`.

One wrong implementation per line is killed: a passthrough that copies its input to the output
places (it is `fork()`, and agrees with passthrough on a sink), an extensional predicate that also
claims a hand-written no-op, a builder whose default is a hand-written no-op, and a retrieval that
returns a fresh action after the first call.

Two consequences tie the block to its neighbours: the tag of any action satisfying CORE-052 is
not the passthrough tag, so the identity predicate rejects `fork()` (`core051_fork_ne`); and with
CORE-020's line 4 a transition built without an action exists and carries the built-in
(`core051_default_builds`), which is what kills a builder that requires an action
(`core051_requiredAction_joint`).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## The reference retrieval -/

/-- **The reference retrieval of the built-in** ([CORE-051]): every call returns the one
passthrough tag (a stable singleton: `rust/libpetri-core/src/action.rs:67-70`,
`java/src/main/java/org/libpetri/core/TransitionAction.java:55-57`,
`typescript/src/core/transition-action.ts:19-24`). -/
def refRetrievePassthrough {A : Type} : Nat → Act A := fun _ => .passthrough

/- The witness models of CORE-051: the reference retrieval, the tag reading of GlossaryAction and
the identity predicate of the reference compile check. -/
/-- The table of other actions about which nothing is known: each may end in any way. The
reference of CORE-051 holds under every table (`core051_reference_table`); this one is the table
the tagged witness uses. -/
def refAnyAction {N T A : Type} : A → ActionRel N T := fun _ _ _ _ => True

#spec_witness refRetrievePassthrough
#spec_witness refAnyAction
#spec_witness Libpetri.Reference.Act.interp
#spec_witness Libpetri.Reference.Act.isPassthrough

/-! ## CORE-051: Passthrough Action -/

requirement CORE_051
  id "CORE-051"
  title "Passthrough Action"
  kind F
  scope "all implementations"
  source verbatim "spec/01-core-model.md"
  quote "*When* a transition fires under the built-in passthrough action, the action *shall* complete with no output token and *shall not* fail."
        "The identity predicate *shall* accept the built-in passthrough action and reject every other action, including `fork()` ([CORE-052]) and a hand-written action that produces no token."
        "*When* a transition is built without an action, the built transition *shall* carry the built-in passthrough action."
        "Every retrieval of the built-in passthrough action *shall* yield the same instance, which the identity predicate accepts."
  reading "Let interp be the action each identity tag names, isPT the identity predicate, B the transition builder and pt k the k-th retrieval of the built-in."
          "For every transition t, delivery δ and outcome r: the passthrough tag ends with r on t and δ exactly when r is completion with no token."
          "For every tag x: isPT x holds exactly when x is the passthrough tag."
          "For every call k on an input i that gives no action: if the call returns an instance x, the definition of x carries the passthrough tag."
          "For all retrievals k and j: pt k equals pt j, and isPT holds of pt k."
  assumes "The model is the tuple (interp, isPT, B, pt). An action is read as its identity tag (Act, Reference/Build.lean): the built-in passthrough or another action named by an opaque id; this is the tag CORE-020, CORE-042 and CORE-043 carry on a built transition (TransDef). interp tag is the action relation (ActionRel, Spec/GlossaryAction.lean) the tag names; the reference is Act.interp I, the passthrough tag naming refPassthrough and other x naming I x, for every table I of other actions. isPT is the identity predicate on tags; the reference is Act.isPassthrough, the predicate the CORE-043 compile check reads (refCompile). B is CORE-020's transition builder (TBuilder); the reference is refTransBuild. pt k is the tag the k-th retrieval of the built-in returns (Rust passthrough(), Java TransitionAction.passthrough(), TypeScript passthrough(), Python libpetri.passthrough); the reference is refRetrievePassthrough."
          "Two actions are the same instance exactly when their tags are equal. A runtime action is an object compared by reference (Rust Arc::ptr_eq, rust/libpetri-core/src/action.rs:75-77; Java ==, java/src/main/java/org/libpetri/core/TransitionAction.java:65-67; TypeScript ===, typescript/src/core/transition-action.ts:32-34); a fresh closure per retrieval is a fresh tag (CORE_051_forbids_freshPerRetrieval). Python's built-in is the enum member BuiltinAction.Passthrough, mapped to Rust's singleton (PyBuiltinAction::to_rust in rust/libpetri-py/src/model.rs), so Python carries the tag itself; a Python callable that produces nothing is another action. Python exposes no identity predicate; line 2 is read there through the Rust one the compile check calls."
          "An explicitly bound null or undefined is not an action and is outside the model: the model's only absent action is TransIn.action = none, Rust cannot express a null action, and Python's builder raises TypeError on one (resolve_py_action in rust/libpetri-py/src/model.rs). Java's Transition.Builder.action(null) throws (Objects.requireNonNull in Transition.Builder.action, java/src/main/java/org/libpetri/core/Transition.java) and TypeScript's action(null) or action(undefined) throws a TypeError (TransitionBuilder.action in typescript/src/core/transition.ts), so in every runtime a transition is built either with an action or without one, and leaving the call out gives the passthrough default (line 3). A setter that stored null would build a transition the identity predicate rejects, so CORE-043's check would pass it and every firing would then fail (the behaviour RD-06 in spec/runtime-defects.md recorded of Java and TypeScript); it is not read as 'built without an action', and line 3 is not weakened for it. The rejection is test evidence (java TransitionTest core051_builder_rejectsNullAction, typescript tests/core/transition.test.ts 'rejects a null or undefined action (CORE-051)'), as the model has no null."
          "Line 1 reads the first sentence at the level of the action: on every transition and delivery the passthrough tag completes, with no token, and has no other outcome, so it never fails (rust/libpetri-core/src/action.rs:86-88 returns Ok(()), java/src/main/java/org/libpetri/core/TransitionAction.java:80-81 returns a completed future, typescript/src/core/transition-action.ts:24 is async () => {}; Python runs Rust's Passthrough, PyBuiltinAction::to_rust in rust/libpetri-py/src/model.rs). A passthrough that copies its input token to every output place is fork() (CORE-052): it agrees with passthrough on a sink and violates line 1 on a transition with an output place (CORE_051_mutant_sinkOnly_killed); a passthrough that fails violates it on every delivery (CORE_051_forbids_failing). That a firing under the passthrough tag deposits nothing is line 1 with CORE-050's line 2 (core051_fire_nil), and that a transition built without an action deposits nothing when a firing ends with its action is line 3 on top (core051_default_fire_nil)."
          "The body's 'consumes input tokens' describes the firing, not the action: what a firing consumes is CORE-030's and EXEC-010's, whatever its action. 'Completes immediately' (AC1) is line 1 for 'completes'. 'Immediately' (no task dispatch, the action runs inline on the orchestrator thread) is a claim about thread placement, kind Q: the Lean model has no threads, so no Lean block states it, and it is checked by tests (CONC-011 AC1, 'Passthrough actions execute inline without task dispatch')."
          "Line 2 reads 'recognisable by identity' as an exact characterisation over tags: the predicate accepts the built-in and rejects every other tag, whatever that action does. An extensional predicate that also accepts a hand-written action producing no token violates it (CORE_051_mutant_acceptsBuiltin_killed). fork() is rejected because its tag is not the passthrough tag: on a one-place self-loop that delivers one token, an action satisfying CORE-052 emits a copy of it, while line 1 allows the passthrough tag no token there, so the tag of every fork satisfying CORE-052 differs from the passthrough tag and line 2 rejects it (core051_fork_ne); at the example table, other fork names the reference fork refFork (core051_reference_fork). Every predicate satisfying line 2 is Act.isPassthrough (core051_isPT_eq), so CORE-043's check, stated over action = passthrough, reads the same nets under any such predicate."
          "Line 3 reads the body's 'This is the default action for transitions without explicitly bound actions' at build time: a transition built without an action carries the built-in (rust/libpetri-core/src/transition.rs:256, java/src/main/java/org/libpetri/core/Transition.java:247, typescript/src/core/transition.ts TransitionBuilder's _action field, and Python's builder, PyTransitionBuilder build in rust/libpetri-py/src/model.rs, None => passthrough()). Line 3 is conditional on a successful build; that a transition given no action builds at all is CORE-020's line 4, and with it such a transition exists and carries the built-in (core051_default_builds). A builder that requires an action fails every build without one, satisfies line 3 vacuously, and is rejected by CORE-020's line 4 (core051_requiredAction_joint). Binding later (bindActions) is CORE-042's, which keeps the tag of an unbound transition. A builder whose default is a hand-written no-op behaves the same at every firing and violates the line (CORE_051_mutant_behaviouralDefault_killed): CORE-043's check would then miss an output-declaring transition left at the default."
          "Line 4 reads 'a stable singleton rather than a fresh closure per call' and the first half of AC3: every retrieval yields one instance and the predicate accepts it. A retrieval whose first call returns the built-in and whose later calls return fresh actions violates it (CORE_051_mutant_firstRetrieval_killed), and so does one that returns a fresh action on every call (CORE_051_forbids_freshPerRetrieval). By line 2, line 4 says every retrieval is the passthrough tag (core051_pt_eq). Python's retrieval is the module constant libpetri.passthrough (python/libpetri/model.py:23, the enum member BuiltinAction.Passthrough), so every access yields the same instance and line 4 holds there by construction."
          "AC1 (passthrough action completes immediately) is line 1 for 'completes'; 'immediately' is left to tests (CONC-011 AC1) as above."
          "AC2 (no output tokens are produced) is line 1: the only outcome is completion with no token."
          "AC3 (repeated retrieval yields the same instance, and an identity predicate accepts the built-in and rejects every other action, including fork()) is lines 4 and 2, with core051_fork_ne for fork()."
          "The test derivation (fire a sink transition with passthrough and see no output token; retrieve the built-in twice and see identity) is CORE_051_nonvacuous: the reference action firing of a sink under the passthrough tag deposits nothing, two retrievals are equal and accepted, and the predicate rejects fork() and a hand-written no-op."
  signoff "2026-11-13 752d59ef4603d8d6 ai"
  statement : ∀ {N T A : Type}, (Act A → ActionRel N T) → (Act A → Bool) → TBuilder N A →
      (Nat → Act A) → Prop :=
    fun interp isPT B pt =>
      (∀ t δ r, interp .passthrough t δ r ↔ r = .ok []) ∧
      (∀ x, isPT x = true ↔ x = .passthrough) ∧
      (∀ k i x, B.build k i = .ok x → i.action = none → (B.defOf x).action = .passthrough) ∧
      (∀ k j, pt k = pt j ∧ isPT (pt k) = true)

/- The pinned readable form of CORE-051: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CORE_051 : {N T A : Type} →
  (Act A → ActionRel N T) → (Act A → Bool) → TBuilder N A → (ℕ → Act A) → Prop :=
fun {N T A} interp isPT B pt =>
  (∀ (t : Reference.Trans N) (δ : Delivered N T) (r : Except String (List (N × T))),
      interp Act.passthrough t δ r ↔ r = Except.ok []) ∧
    (∀ (x : Act A), isPT x = true ↔ x = Act.passthrough) ∧
      (∀ (k : ℕ) (i : TransIn N A) (x : B.I),
          B.build k i = Except.ok x → i.action = none → (B.defOf x).action = Act.passthrough) ∧
        ∀ (k j : ℕ), pt k = pt j ∧ isPT (pt k) = true
-/
#guard_msgs in #print CORE_051

/-! ### The four lines, named (for the mutants) -/

section Lines

variable {N T A : Type}

/-- Line 1 of CORE-051: passthrough completes with no token and has no other outcome. -/
def core051_line1 (interp : Act A → ActionRel N T) : Prop :=
  ∀ t δ r, interp .passthrough t δ r ↔ r = .ok []

/-- Line 2 of CORE-051: the identity predicate holds of the passthrough tag and nothing else. -/
def core051_line2 (isPT : Act A → Bool) : Prop :=
  ∀ x, isPT x = true ↔ x = .passthrough

/-- Line 3 of CORE-051: a transition built without an action carries the passthrough tag. -/
def core051_line3 (B : TBuilder N A) : Prop :=
  ∀ k i x, B.build k i = .ok x → i.action = none → (B.defOf x).action = .passthrough

/-- Line 4 of CORE-051: every retrieval yields one instance, which the predicate accepts. -/
def core051_line4 (isPT : Act A → Bool) (pt : Nat → Act A) : Prop :=
  ∀ k j, pt k = pt j ∧ isPT (pt k) = true

/-- CORE-051 is its four lines. -/
theorem core051_iff (interp : Act A → ActionRel N T) (isPT : Act A → Bool) (B : TBuilder N A)
    (pt : Nat → Act A) :
    CORE_051 interp isPT B pt ↔
      core051_line1 interp ∧ core051_line2 isPT ∧ core051_line3 B ∧ core051_line4 isPT pt :=
  Iff.rfl

end Lines

/-! ### The reference -/

/-- The reference satisfies CORE-051 under every table `I` of other actions: the passthrough tag
names `refPassthrough`, `Act.isPassthrough` is the tag test, the reference builder resolves an
absent action to passthrough, and every reference retrieval is the passthrough tag. -/
theorem core051_reference_table {N T A : Type} [DecidableEq N] [ToString N]
    (I : A → ActionRel N T) :
    CORE_051 (Act.interp I) Act.isPassthrough (refTransBuild (N := N) (A := A))
      refRetrievePassthrough := by
  refine ⟨fun t δ r => interp_passthrough I t δ r, fun _ => Act.isPassthrough_iff,
    fun k i x h hn => ?_, fun _ _ => ⟨rfl, rfl⟩⟩
  show x.1.2.action = _
  rw [refTransBuild_def h]
  exact resolve_action_none hn

/-- ✓ The reference satisfies CORE-051 (`core051_reference_table` at the table that knows
nothing about the other actions). -/
@[evidence holds CORE_051]
theorem CORE_051_reference {N T A : Type} [DecidableEq N] [ToString N] :
    CORE_051 (Act.interp (refAnyAction (N := N) (T := T) (A := A))) Act.isPassthrough
      (refTransBuild (N := N) (A := A)) refRetrievePassthrough :=
  core051_reference_table _

/-! ### Consequences -/

section Consequences

variable {N T A : Type}

/-- Every predicate satisfying line 2 is the reference tag test `Act.isPassthrough`: the
predicate CORE-043's check reads is fixed by CORE-051. -/
theorem core051_isPT_eq {interp : Act A → ActionRel N T} {isPT : Act A → Bool}
    {B : TBuilder N A} {pt : Nat → Act A} (h : CORE_051 interp isPT B pt) :
    isPT = Act.isPassthrough := by
  funext x
  apply Bool.eq_iff_iff.2
  rw [h.2.1 x, Act.isPassthrough_iff]

/-- By line 2, line 4 says every retrieval is the passthrough tag. -/
theorem core051_pt_eq {interp : Act A → ActionRel N T} {isPT : Act A → Bool}
    {B : TBuilder N A} {pt : Nat → Act A} (h : CORE_051 interp isPT B pt) (k : Nat) :
    pt k = .passthrough :=
  (h.2.1 _).1 (h.2.2.2 k k).2

/-- Passthrough never fails: no failure is an outcome of the passthrough tag. -/
theorem core051_never_fails {interp : Act A → ActionRel N T} {isPT : Act A → Bool}
    {B : TBuilder N A} {pt : Nat → Act A} (h : CORE_051 interp isPT B pt) (t : Trans N)
    (δ : Delivered N T) (m : String) : ¬ interp .passthrough t δ (.error m) := by
  intro he
  cases (h.1 t δ _).1 he

variable [DecidableEq N]

/-- **With CORE-050**: a firing that ends with the completion of the passthrough tag deposits
nothing, for every `interp` satisfying line 1 (CORE-050's line 2 makes the emission one the action
completes with). -/
theorem core051_fire_nil {Q : QFireRel N T} {AF : ActFireRel N T} (h50 : CORE_050 Q AF)
    {interp : Act A → ActionRel N T} {isPT : Act A → Bool} {B : TBuilder N A}
    {pt : Nat → Act A} (h : CORE_051 interp isPT B pt) {t : Trans N} {M M' : QueueMarking N T}
    {δ : Delivered N T} {e : List (N × T)} (hf : AF (interp .passthrough) t M δ e M') : e = [] :=
  (Except.ok.inj ((h.1 t δ _).1 (h50.2.1 _ t δ e M M' hf))).symm ▸ rfl

/-- **With CORE-050 and CORE-020's builder**: a transition built without an action deposits
nothing when a firing ends with the completion of its action. -/
theorem core051_default_fire_nil {Q : QFireRel N T} {AF : ActFireRel N T} (h50 : CORE_050 Q AF)
    {interp : Act A → ActionRel N T} {isPT : Act A → Bool} {B : TBuilder N A}
    {pt : Nat → Act A} (h : CORE_051 interp isPT B pt) {k : Nat} {i : TransIn N A} {x : B.I}
    (hb : B.build k i = .ok x) (hn : i.action = none) {M M' : QueueMarking N T}
    {δ : Delivered N T} {e : List (N × T)}
    (hf : AF (interp (B.defOf x).action) (B.defOf x).toTrans M δ e M') : e = [] := by
  rw [h.2.2.1 k i x hb hn] at hf
  exact core051_fire_nil h50 h hf

/-- **With CORE-020**: a transition given no action whose arcs and output specification build and
whose timing is valid builds (CORE-020's line 4), and carries the built-in (line 3). -/
theorem core051_default_builds {interp : Act A → ActionRel N T} {isPT : Act A → Bool}
    {B : TBuilder N A} {pt : Nat → Act A} (h20 : CORE_020 B) (h : CORE_051 interp isPT B pt)
    (k : Nat) {i : TransIn N A} (hn : i.action = none) (hb : Builds i.toTrans)
    (ht : ∀ tm, i.timing = some tm → tm.Valid) :
    ∃ x, B.build k i = .ok x ∧ (B.defOf x).action = .passthrough := by
  obtain ⟨x, hx⟩ := (h20.2.2.2 k i).2 ⟨hb, ht⟩
  exact ⟨x, hx, h.2.2.1 k i x hx hn⟩

/-- A one-place self-loop: one input arc on `n`, output `Place n`. -/
def core051_loop (n : N) : Trans N :=
  { core := { name := "fork", inputs := [⟨n, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place n) }

/-- The delivery of the one token `x` from `n`. -/
def core051_δx (n : N) (x : T) : Delivered N T :=
  ⟨fun p => if p = n then [x] else [], fun _ => []⟩

/-- **With CORE-052**: the tag of a fork is not the passthrough tag, and the identity predicate
rejects it. On the self-loop on `n` delivering `x`, a fork satisfying CORE-052 completes with a
copy of `x` in `n`, while line 1 allows the passthrough tag no token there. -/
theorem core051_fork_ne {V : Type} {val : T → V} {Fork : ActionFn N T} (h52 : CORE_052 val Fork)
    {interp : Act A → ActionRel N T} {isPT : Act A → Bool} {B : TBuilder N A} {pt : Nat → Act A}
    (h : CORE_051 interp isPT B pt) {fk : Act A} (hfk : interp fk = Fork.rel) (n : N) (x : T) :
    fk ≠ .passthrough ∧ isPT fk = false := by
  have hne : fk ≠ .passthrough := by
    rintro rfl
    obtain ⟨e, he, hp⟩ := (h52 (core051_loop n) (core051_δx n x)).1 n x
      (fun p => by simp [inPlaces, core051_loop]) (by simp [core051_δx])
    have hr : interp .passthrough (core051_loop n) (core051_δx n x) (.ok e) := by
      rw [hfk]; exact he
    have he0 : e = [] := Except.ok.inj ((h.1 _ _ _).1 hr)
    have := hp n
    rw [if_pos ⟨_, rfl, by simp [outPlaces]⟩, he0] at this
    simp [qEmittedTo] at this
  refine ⟨hne, ?_⟩
  cases hx : isPT fk
  · rfl
  · exact absurd ((h.2.1 fk).1 hx) hne

end Consequences

/-! ### Examples -/

/-- The action ids of the examples: `"fork"` names `fork()` (CORE-052) and `"noop"` a
hand-written action that completes with no token. -/
def core051_I : String → ActionRel Nat Nat
  | "noop" => refPassthrough.rel
  | "fork" => (refFork (N := Nat) (T := Nat)).rel
  | _ => fun _ _ _ => False

/-- At the example table, `other "fork"` names the reference fork, which satisfies CORE-052, and
the identity predicate rejects it, as `core051_fork_ne` requires of every predicate satisfying
CORE-051. -/
theorem core051_reference_fork :
    CORE_052 id (refFork (N := Nat) (T := Nat)) ∧
      Act.interp core051_I (.other "fork") = (refFork (N := Nat) (T := Nat)).rel ∧
      ((Act.other "fork" : Act String) ≠ .passthrough ∧
        Act.isPassthrough (Act.other "fork") = false) :=
  ⟨CORE_052_reference id, rfl,
    core051_fork_ne (CORE_052_reference id)
      (core051_reference_table (N := Nat) (T := Nat) (A := String) core051_I) rfl 0 7⟩

/-- A delivery of the token 7 from place 0 and nothing else. -/
def core051_δ : Delivered Nat Nat := ⟨fun p => if p = 0 then [7] else [], fun _ => []⟩

/-- A sink input without an action: one input arc on place 0, no output specification. -/
def core051_sinkIn : TransIn Nat String :=
  { core := { name := "s", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- The sink input builds under the reference builder at every call number. -/
theorem core051_sinkIn_builds (k : Nat) :
    (refTransBuild (N := Nat) (A := String)).build k core051_sinkIn =
      .ok ⟨(k, core051_sinkIn.resolve), k, core051_sinkIn,
        refTransBuildRaw_ok.2 ⟨(refBuild_eq_none_iff _).1 (by decide), nofun, rfl⟩⟩ :=
  refTransBuild_ok.2 (refTransBuildRaw_ok.2 ⟨(refBuild_eq_none_iff _).1 (by decide), nofun, rfl⟩)

/-- ✓ CORE-051 is not vacuous. The test derivation: the reference action firing of the sink `s`
under the passthrough tag, from a place 0 holding 7 then 8, deposits nothing (line 1 with
CORE-050); two retrievals of the built-in are equal and accepted by the identity predicate, which
rejects `fork()` and a hand-written no-op (lines 2 and 4); the sink built without an action
carries the passthrough tag (line 3). -/
@[evidence nonvacuous CORE_051]
theorem CORE_051_nonvacuous :
    refActionFire (Act.interp core051_I .passthrough) core050_s core050_M
      (qDelivered core050_M core050_s) [] (qFire core050_M core050_s []) ∧
    qFire core050_M core050_s [] 0 = [8] ∧
    (∀ m, ¬ Act.interp core051_I .passthrough core050_s (qDelivered core050_M core050_s)
      (.error m)) ∧
    refRetrievePassthrough (A := String) 0 = refRetrievePassthrough 1 ∧
    Act.isPassthrough (refRetrievePassthrough (A := String) 1) = true ∧
    Act.isPassthrough (Act.other "fork") = false ∧
    Act.isPassthrough (Act.other "noop") = false ∧
    (∃ x, (refTransBuild (N := Nat) (A := String)).build 0 core051_sinkIn = .ok x ∧
      ((refTransBuild (N := Nat) (A := String)).defOf x).action = .passthrough) := by
  refine ⟨?_, by decide, fun m h => ?_, rfl, rfl, rfl, rfl, ⟨_, core051_sinkIn_builds 0, rfl⟩⟩
  · exact ⟨⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩, rfl, rfl⟩
  · cases h

/-! ### Wrong implementations -/

/-- A passthrough that never completes: it fails on every delivery. -/
def core051_failInterp : Act String → ActionRel Nat Nat
  | .passthrough => fun _ _ r => r = .error "passthrough failed"
  | .other a => core051_I a

/-- ✗ A passthrough that fails violates CORE-051 (line 1): on the sink delivery it does not
complete with no token. -/
@[evidence forbids CORE_051]
theorem CORE_051_forbids_failing :
    ¬ CORE_051 core051_failInterp Act.isPassthrough (refTransBuild (N := Nat) (A := String))
      refRetrievePassthrough := by
  intro h
  have := (h.1 core050_s core051_δ (.ok [])).2 rfl
  cases this

/-- A retrieval that returns a fresh action on every call (a fresh closure per call). -/
def core051_freshPT : Nat → Act String := fun k => .other s!"closure{k}"

/-- ✗ A fresh action per retrieval violates CORE-051 (line 4): the first retrieval is not the
second, and the identity predicate rejects both. -/
@[evidence forbids CORE_051]
theorem CORE_051_forbids_freshPerRetrieval :
    ¬ CORE_051 (Act.interp core051_I) Act.isPassthrough (refTransBuild (N := Nat) (A := String))
      core051_freshPT := by
  intro h
  have := (h.2.2.2 0 1).2
  cases this

/-! ### Mutant: line 1 checked on sinks only (passthrough is fork) -/

/-- Every output place of `t`, each receiving every token delivered from the input places: the
emission of `fork()` (CORE-052) on a delivery. -/
def core051_copyEmit (t : Trans Nat) (δ : Delivered Nat Nat) : List (Nat × Nat) :=
  ((t.out.map outPlaces).getD []).flatMap fun p => ((inPlaces t).flatMap δ.inputs).map (p, ·)

/-- A passthrough that copies its input to every output place (it is `fork()`). -/
def core051_forkInterp : Act String → ActionRel Nat Nat
  | .passthrough => fun t δ r => r = .ok (core051_copyEmit t δ)
  | .other a => core051_I a

/-- Mutant reading of line 1 (the test derivation's sink taken as the whole line): on a transition
with no output specification, passthrough completes with no token and has no other outcome. -/
def CORE_051_mutant_sinkOnly {N T A : Type} (interp : Act A → ActionRel N T)
    (isPT : Act A → Bool) (B : TBuilder N A) (pt : Nat → Act A) : Prop :=
  (∀ t δ r, t.out = none → (interp .passthrough t δ r ↔ r = .ok [])) ∧
    core051_line2 isPT ∧ core051_line3 B ∧ core051_line4 isPT pt

/-- ✗ The copying passthrough kills the mutant: on a sink it emits nothing, but on `u` (input
place 0, output `Place 1`) it emits the delivered 7 in place 1 (line 1). -/
@[evidence mutant CORE_051]
theorem CORE_051_mutant_sinkOnly_killed :
    CORE_051_mutant_sinkOnly core051_forkInterp Act.isPassthrough
        (refTransBuild (N := Nat) (A := String)) refRetrievePassthrough ∧
      ¬ CORE_051 core051_forkInterp Act.isPassthrough (refTransBuild (N := Nat) (A := String))
        refRetrievePassthrough := by
  obtain ⟨-, h2, h3, h4⟩ := core051_reference_table (N := Nat) (T := Nat) (A := String) core051_I
  refine ⟨⟨fun t δ r ht => ?_, h2, h3, h4⟩, fun h => ?_⟩
  · show r = .ok (core051_copyEmit t δ) ↔ r = .ok []
    simp [core051_copyEmit, ht]
  · have h1 : (Except.ok [] : Except String (List (Nat × Nat))) =
        .ok (core051_copyEmit core050_u core051_δ) := (h.1 core050_u core051_δ (.ok [])).2 rfl
    exact absurd (Except.ok.inj h1) (by decide)

/-! ### Mutant: line 2 as "accepts the built-in" (an extensional predicate) -/

/-- A predicate that accepts every action that completes with no token: the built-in and the
hand-written no-op. -/
def core051_extIsPT : Act String → Bool
  | .passthrough => true
  | .other a => a == "noop"

/-- Mutant reading of line 2 ("an identity predicate over it accepts the built-in" without "and
rejects every other action"). -/
def CORE_051_mutant_acceptsBuiltin {N T A : Type} (interp : Act A → ActionRel N T)
    (isPT : Act A → Bool) (B : TBuilder N A) (pt : Nat → Act A) : Prop :=
  core051_line1 interp ∧ isPT .passthrough = true ∧ core051_line3 B ∧ core051_line4 isPT pt

/-- ✗ The extensional predicate kills the mutant: it accepts the built-in, but it also accepts the
hand-written no-op, which is not the built-in (line 2). -/
@[evidence mutant CORE_051]
theorem CORE_051_mutant_acceptsBuiltin_killed :
    CORE_051_mutant_acceptsBuiltin (Act.interp core051_I) core051_extIsPT
        (refTransBuild (N := Nat) (A := String)) refRetrievePassthrough ∧
      ¬ CORE_051 (Act.interp core051_I) core051_extIsPT (refTransBuild (N := Nat) (A := String))
        refRetrievePassthrough := by
  obtain ⟨h1, -, h3, -⟩ := core051_reference_table (N := Nat) (T := Nat) (A := String) core051_I
  refine ⟨⟨h1, rfl, h3, fun _ _ => ⟨rfl, rfl⟩⟩, fun h => ?_⟩
  have := (h.2.1 (.other "noop")).1 rfl
  cases this

/-! ### Mutant: line 3 as a behavioural default (a hand-written no-op default) -/

/-- A builder that checks arcs and output specification as the reference does and resolves an
absent action to the hand-written no-op `other "noop"` instead of the built-in. -/
def core051_noopDefaultBuild : TBuilder Nat String where
  I := Nat × TransDef Nat String
  build k i :=
    match refBuild i.toTrans with
    | some e => .error e
    | none => .ok (k, { i.resolve with action := i.action.getD (.other "noop") })
  defOf := Prod.snd
  same x y := x.1 = y.1

/-- A successful call of the no-op-default builder resolves the input with the no-op default. -/
theorem core051_noop_def {k : Nat} {i : TransIn Nat String} {x : Nat × TransDef Nat String}
    (hb : core051_noopDefaultBuild.build k i = .ok x) :
    x.2 = { i.resolve with action := i.action.getD (.other "noop") } := by
  simp only [core051_noopDefaultBuild] at hb
  split at hb
  · cases hb
  · cases hb; rfl

/-- Mutant reading of line 3 ("the default action" read by behaviour): a transition built without
an action carries an action that completes with no token and has no other outcome. -/
def CORE_051_mutant_behaviouralDefault {N T A : Type} (interp : Act A → ActionRel N T)
    (isPT : Act A → Bool) (B : TBuilder N A) (pt : Nat → Act A) : Prop :=
  core051_line1 interp ∧ core051_line2 isPT ∧
    (∀ k i x, B.build k i = .ok x → i.action = none →
      ∀ t δ r, interp (B.defOf x).action t δ r ↔ r = .ok []) ∧
    core051_line4 isPT pt

/-- ✗ The no-op default kills the mutant: the default behaves as passthrough on every delivery,
but the sink built without an action carries `other "noop"`, not the built-in (line 3), so the
CORE-043 check would not see it. -/
@[evidence mutant CORE_051]
theorem CORE_051_mutant_behaviouralDefault_killed :
    CORE_051_mutant_behaviouralDefault (Act.interp core051_I) Act.isPassthrough
        core051_noopDefaultBuild refRetrievePassthrough ∧
      ¬ CORE_051 (Act.interp core051_I) Act.isPassthrough core051_noopDefaultBuild
        refRetrievePassthrough := by
  obtain ⟨h1, h2, -, h4⟩ := core051_reference_table (N := Nat) (T := Nat) (A := String) core051_I
  refine ⟨⟨h1, h2, fun k i x hb hn t δ r => ?_, h4⟩, fun h => ?_⟩
  · have hx : (core051_noopDefaultBuild.defOf x).action = .other "noop" := by
      rw [show (core051_noopDefaultBuild.defOf x) = x.2 from rfl, core051_noop_def hb, hn]; rfl
    rw [hx]
    exact ⟨fun e => e.symm, fun e => e.symm⟩
  · have hr : refBuild core051_sinkIn.toTrans = none := by decide
    have hb : core051_noopDefaultBuild.build 0 core051_sinkIn =
        .ok (0, { core051_sinkIn.resolve with action := .other "noop" }) := by
      simp only [core051_noopDefaultBuild, hr]; rfl
    have := h.2.2.1 0 core051_sinkIn _ hb rfl
    cases this

/-! ### A builder that requires an action (killed with CORE-020) -/

/-- A builder that moves the default into a required field: it fails every input without an
action (as `Objects.requireNonNull(action)` at build in Java, or `.expect("action")` in Rust, would;
the Java setter's check on an explicit null leaves the default in place) and builds every
other input as the reference does. -/
def core051_requiredBuild : TBuilder Nat String where
  I := (refTransBuild (N := Nat) (A := String)).I
  build k i := match i.action with
    | none => .error "action required"
    | some _ => (refTransBuild (N := Nat) (A := String)).build k i
  defOf := (refTransBuild (N := Nat) (A := String)).defOf
  same := (refTransBuild (N := Nat) (A := String)).same

/-- The required-action builder satisfies CORE-051 (line 3 never fires, since no input without an
action builds) and is rejected by CORE-020's line 4: the sink `s` has buildable arcs and no
timing, yet does not build. CORE-051's line 3 relies on CORE-020 for the transitions it speaks of
to exist (`core051_default_builds`). -/
theorem core051_requiredAction_joint :
    CORE_051 (Act.interp core051_I) Act.isPassthrough core051_requiredBuild
        refRetrievePassthrough ∧
      ¬ CORE_020 core051_requiredBuild := by
  obtain ⟨h1, h2, -, h4⟩ := core051_reference_table (N := Nat) (T := Nat) (A := String) core051_I
  refine ⟨⟨h1, h2, fun k i x hb hn => ?_, h4⟩, fun h => ?_⟩
  · simp only [core051_requiredBuild, hn] at hb; cases hb
  · obtain ⟨x, hx⟩ :=
      (h.2.2.2 0 core051_sinkIn).2 ⟨(refBuild_eq_none_iff _).1 (by decide), nofun⟩
    cases hx

/-! ### Mutant: line 4 as "the first retrieval is the built-in" -/

/-- A retrieval whose first call returns the built-in and whose later calls return fresh
actions. -/
def core051_firstPT : Nat → Act String
  | 0 => .passthrough
  | k + 1 => .other s!"closure{k}"

/-- Mutant reading of line 4 (one retrieval checked, not repeated retrieval): the first retrieval
is accepted by the identity predicate. -/
def CORE_051_mutant_firstRetrieval {N T A : Type} (interp : Act A → ActionRel N T)
    (isPT : Act A → Bool) (B : TBuilder N A) (pt : Nat → Act A) : Prop :=
  core051_line1 interp ∧ core051_line2 isPT ∧ core051_line3 B ∧ isPT (pt 0) = true

/-- ✗ The first-call singleton kills the mutant: the first retrieval is the built-in, but the
second is a fresh action, not the same instance (line 4). -/
@[evidence mutant CORE_051]
theorem CORE_051_mutant_firstRetrieval_killed :
    CORE_051_mutant_firstRetrieval (Act.interp core051_I) Act.isPassthrough
        (refTransBuild (N := Nat) (A := String)) core051_firstPT ∧
      ¬ CORE_051 (Act.interp core051_I) Act.isPassthrough (refTransBuild (N := Nat) (A := String))
        core051_firstPT := by
  obtain ⟨h1, h2, h3, -⟩ := core051_reference_table (N := Nat) (T := Nat) (A := String) core051_I
  refine ⟨⟨h1, h2, h3, rfl⟩, fun h => ?_⟩
  have := (h.2.2.2 0 1).1
  cases this

end Libpetri.Spec
