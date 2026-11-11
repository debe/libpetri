import Libpetri.Reference.Timed
import Libpetri.Spec.Glossary
import Libpetri.Spec.Req.TIME_001

set_option linter.missingDocs true

/-!
# RefNetBuild: transition definitions, the transition builder and the net builder

The structure model of [CORE-020], [CORE-021] and [CORE-040]–[CORE-043]: what a host hands the
transition builder (`TransIn`), what a built transition carries (`TransDef`), the transition
builder as an interface (`TBuilder`) with its reference `refTransBuild`, and the net builder
`refNetBuild` from declared places and built transitions to a built net (`BuiltNet`).

Nothing here defines firing, enablement or a build check a second time:

* the firing view of a definition is `TransDef.toTrans`, a `Reference.Trans`, whose `reapable`
  bit is computed from the timing, so a built net meets the coherence assumption of `TimedNet`
  by construction;
* the arc and output-spec checks of the transition builder are `refBuild` (`Spec/Glossary.lean`),
  the witness every IO and EXEC-012 build line is stated over, and its timing check is TIME-001's
  reference factory `refTimingFactory` ([TIME-001] AC5: a timing written out without a factory is
  checked again when the transition is built);
* a built net runs as `BuiltNet.toNet` (untimed) or `BuiltNet.toTimed` (timed).

Three design points shared with the composition and ν-net models are fixed here:

* **One `TransDef`.** The composition model's `CDef` extends `TransDef` (adding the MOD-031
  correspondence), and the ν-net model's `NuDef` extends it (adding the match specification of
  [NU-020]); neither adds a field to `TransDef` or to `Reference.Trans`.
* **Places are the abstract `N`.** Every model is over the place type `N` of the glossary
  (`PlaceName N := N`, identity = equality on `N`). How a host place object maps to `N` (by name,
  or by name and token type in Java) is [CORE-002]'s, and the composition model's prefix renaming
  acts on the same `N`.
* **A net is built from built transitions.** `NetIn B` holds instances of the transition builder
  `B` (`B.I`), not bare definitions. The reference builder's instances are exactly what one of its
  build calls returned (`refTransBuild_inst`), so every transition of a built net builds and has
  a valid timing (`refNetBuild_trans_ok`).
-/

namespace Libpetri.Reference

open Libpetri Libpetri.Novel.Seam Libpetri.Spec
open Libpetri.Novel.TimedScg (Timing)

/-! ## The action identity tag -/

/-- The action a transition carries, as far as structure can see it: the built-in passthrough
action, recognised by identity ([CORE-051]), or another action named by an opaque id `a`. What an
action does is the action model's (`Spec/GlossaryAction.lean`, W3). -/
inductive Act (A : Type) where
  /-- The built-in passthrough action ([CORE-051]). -/
  | passthrough
  /-- Another action, named by its id. -/
  | other (a : A)
  deriving DecidableEq, Repr

/-! ## Transition definitions -/

/-- What a host hands the transition builder ([CORE-020]): the name and arcs (`core`, each arc
kind a list, in the order given and with its repetitions), the output specification if any, and
optionally a timing, a priority and an action (absent = the builder's default). -/
structure TransIn (N A : Type) where
  /-- The name and the input, inhibitor, read and reset arcs. -/
  core     : NTransition N
  /-- The output specification ([IO-010]); `none` = no output specification. -/
  out      : Option (Out N)
  /-- The timing, if one is given ([TIME-001]). -/
  timing   : Option Timing := none
  /-- The priority, if one is given ([EXEC-002]). -/
  priority : Option Int := none
  /-- The action, if one is given. -/
  action   : Option (Act A) := none

/-- A transition definition as a built transition carries it: every field resolved. The
composition model's `CDef` and the ν-net model's `NuDef` extend this record; no other record
carries these fields. -/
structure TransDef (N A : Type) where
  /-- The name and the input, inhibitor, read and reset arcs. -/
  core     : NTransition N
  /-- The output specification; `none` = no output specification. -/
  out      : Option (Out N)
  /-- The timing. -/
  timing   : Timing
  /-- The priority (higher fires first, [EXEC-002]). -/
  priority : Int
  /-- The action. -/
  action   : Act A

variable {N A : Type}

/-- The firing view of a definition: a `Reference.Trans` whose `reapable` bit is the timing's,
so a net of built transitions meets `TimedNet`'s coherence assumption by construction. -/
def TransDef.toTrans (d : TransDef N A) : Trans N := ⟨d.core, d.out, d.timing.reapable⟩

/-- The build-check view of an input: arcs and output specification (`refBuild` reads nothing
else). -/
def TransIn.toTrans (i : TransIn N A) : Trans N := ⟨i.core, i.out, false⟩

/-- The definition the reference builder resolves from an input: the given fields kept, the
absent ones defaulted (timing `Immediate`, [TIME-001] AC1; priority 0, [CORE-020]; action
passthrough, [CORE-051]). -/
def TransIn.resolve (i : TransIn N A) : TransDef N A :=
  ⟨i.core, i.out, i.timing.getD .immediate, i.priority.getD 0, i.action.getD .passthrough⟩

/-- Every place a definition names: its input, inhibitor, read and reset places and every place
of its output specification ([IO-017]). -/
def TransDef.namedPlaces (d : TransDef N A) : List N :=
  d.core.inputs.map (·.place) ++ d.core.inhibitors ++ d.core.reads ++ d.core.resets ++
    (d.out.map outPlaces).getD []

/-- `Builds` reads only the arcs and the output specification, never the `reapable` bit. -/
theorem builds_reapable [DecidableEq N] (c : NTransition N) (o : Option (Out N)) (r r' : Bool) :
    Builds (⟨c, o, r⟩ : Trans N) ↔ Builds (⟨c, o, r'⟩ : Trans N) := Iff.rfl

/-! ## The transition builder -/

/-- A transition builder ([CORE-020], [CORE-021]): the `k`-th build call on input `i` either
fails with a message or returns an instance; an instance has a definition (`defOf`) and an
identity (`same`). -/
structure TBuilder (N A : Type) where
  /-- The instances the builder returns. -/
  I     : Type
  /-- The `k`-th build call on an input: `.ok x` returns the instance `x`, `.error msg` fails. -/
  build : Nat → TransIn N A → Except String I
  /-- The definition an instance carries. -/
  defOf : I → TransDef N A
  /-- Instance identity ([CORE-021]). -/
  same  : I → I → Prop

section Ref

variable [DecidableEq N] [ToString N]

/-- The reference build function: `refBuild`'s arc and output-spec checks, then, for a timing
written out without a factory, TIME-001's reference factory again ([TIME-001] AC5). Rust runs the
timing check after the input checks and before the output-spec checks (`transition.rs:381-470`);
only success is stated anywhere, so the order matters for the message alone. A successful call
returns its call number and the resolved definition. -/
def refTransBuildRaw (k : Nat) (i : TransIn N A) : Except String (Nat × TransDef N A) :=
  match refBuild i.toTrans with
  | some e => .error e
  | none =>
    match i.timing with
    | none => .ok (k, i.resolve)
    | some tm =>
      match refTimingFactory tm with
      | .error e => .error e
      | .ok _ => .ok (k, i.resolve)

/-- **The reference transition builder.** An instance is a call number and a definition that
some build call returned (so a term of `refTransBuild.I` is never a definition no build call
produced); two instances are the same exactly when they come from the same call ([CORE-021]). -/
def refTransBuild : TBuilder N A where
  I := {x : Nat × TransDef N A // ∃ k i, refTransBuildRaw k i = .ok x}
  build k i :=
    match h : refTransBuildRaw k i with
    | .ok x => .ok ⟨x, k, i, h⟩
    | .error e => .error e
  defOf x := x.1.2
  same x y := x.1.1 = y.1.1

/- The reference transition builder is the witness model of the transition-builder blocks. -/
#spec_witness refTransBuild

/-- TIME-001's reference factory accepts a timing exactly when it is valid, and returns it as
written. -/
theorem refTimingFactory_ok {tm v : Timing} : refTimingFactory tm = .ok v ↔ tm.Valid ∧ v = tm := by
  unfold refTimingFactory
  by_cases h : tm.Valid
  · rw [if_pos h]; exact ⟨fun e => ⟨h, (Except.ok.inj e).symm⟩, fun ⟨_, e⟩ => e ▸ rfl⟩
  · rw [if_neg h]; exact ⟨(fun e => nomatch e), fun ⟨hv, _⟩ => absurd hv h⟩

/-- The reference build function succeeds exactly when the input's arcs and output specification
build and its timing, if one is given, is valid; it then returns the call number and the resolved
definition. -/
theorem refTransBuildRaw_ok {k : Nat} {i : TransIn N A} {y : Nat × TransDef N A} :
    refTransBuildRaw k i = .ok y ↔
      Builds i.toTrans ∧ (∀ tm, i.timing = some tm → tm.Valid) ∧ y = (k, i.resolve) := by
  rw [← refBuild_eq_none_iff]
  unfold refTransBuildRaw
  cases hb : refBuild i.toTrans with
  | some e => simp
  | none =>
    cases ht : i.timing with
    | none =>
      simp only [true_and, reduceCtorEq, false_implies, implies_true]
      exact ⟨fun e => (Except.ok.inj e).symm, fun e => e ▸ rfl⟩
    | some tm =>
      simp only [true_and, Option.some.injEq, forall_eq']
      cases hf : refTimingFactory tm with
      | error e =>
        have hv : ¬ tm.Valid := fun hv => by
          unfold refTimingFactory at hf; rw [if_pos hv] at hf; cases hf
        exact ⟨(fun e => nomatch e), fun ⟨h, _⟩ => absurd h hv⟩
      | ok v =>
        have hv := (refTimingFactory_ok.1 hf).1
        exact ⟨fun e => ⟨hv, (Except.ok.inj e).symm⟩, fun ⟨_, e⟩ => e ▸ rfl⟩

/-- A build call of the reference transition builder returns `x` exactly when the reference
build function returns `x`'s call number and definition. -/
theorem refTransBuild_ok {k : Nat} {i : TransIn N A} {x : (refTransBuild (N := N) (A := A)).I} :
    (refTransBuild (N := N) (A := A)).build k i = .ok x ↔ refTransBuildRaw k i = .ok x.1 := by
  obtain ⟨y, hy⟩ := x
  dsimp only [refTransBuild]
  split
  · rename_i z h
    constructor
    · intro e
      have hz : z = y := congrArg Subtype.val (Except.ok.inj e)
      subst hz; exact h
    · intro e
      have hz : z = y := Except.ok.inj (h.symm.trans e)
      subst hz; rfl
  · rename_i e h
    constructor
    · intro c; cases c
    · intro c; rw [h] at c; cases c

/-- A build call of the reference transition builder succeeds exactly when the input's arcs and
output specification build and its timing, if one is given, is valid. -/
theorem refTransBuild_succeeds {k : Nat} {i : TransIn N A} :
    (∃ x, (refTransBuild (N := N) (A := A)).build k i = .ok x) ↔
      Builds i.toTrans ∧ ∀ tm, i.timing = some tm → tm.Valid := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨hb, ht, -⟩ := refTransBuildRaw_ok.1 (refTransBuild_ok.1 hx)
    exact ⟨hb, ht⟩
  · rintro ⟨hb, ht⟩
    have hr : refTransBuildRaw k i = .ok (k, i.resolve) := refTransBuildRaw_ok.2 ⟨hb, ht, rfl⟩
    exact ⟨⟨(k, i.resolve), k, i, hr⟩, refTransBuild_ok.2 hr⟩

/-- A successful build call of the reference transition builder returns the call number and the
resolved definition. -/
theorem refTransBuild_def {k : Nat} {i : TransIn N A} {x : (refTransBuild (N := N) (A := A)).I}
    (h : (refTransBuild (N := N) (A := A)).build k i = .ok x) :
    x.1 = (k, i.resolve) :=
  (refTransBuildRaw_ok.1 (refTransBuild_ok.1 h)).2.2

/-- Every instance of the reference transition builder is what one of its build calls returned. -/
theorem refTransBuild_inst (x : (refTransBuild (N := N) (A := A)).I) :
    ∃ k i, (refTransBuild (N := N) (A := A)).build k i = .ok x := by
  obtain ⟨k, i, h⟩ := x.2
  exact ⟨k, i, refTransBuild_ok.2 h⟩

/-- The definition of every instance of the reference transition builder builds and has a valid
timing. -/
theorem refTransBuild_inst_ok (x : (refTransBuild (N := N) (A := A)).I) :
    Builds ((refTransBuild (N := N) (A := A)).defOf x).toTrans ∧
      ((refTransBuild (N := N) (A := A)).defOf x).timing.Valid := by
  obtain ⟨k, i, h⟩ := x.2
  obtain ⟨hb, ht, he⟩ := refTransBuildRaw_ok.1 h
  show Builds x.1.2.toTrans ∧ x.1.2.timing.Valid
  rw [he]
  refine ⟨hb, ?_⟩
  show (i.timing.getD .immediate).Valid
  cases hi : i.timing with
  | none => exact trivial
  | some tm => exact ht tm hi

end Ref

/-! ## The net builder -/

/-- What a host hands the net builder: declared places, the instances of transition builder `B`
it added, in the order added, and the declared terminal places of [EXEC-042]. -/
structure NetIn (B : TBuilder N A) where
  /-- The declared places, in the order declared. -/
  places    : List N
  /-- The added transitions, in the order added. -/
  trans     : List B.I
  /-- The declared terminal places ([EXEC-042]). -/
  terminals : List N := []

/-- A built net: its places, its transitions' definitions in declaration order, and its terminal
places. -/
structure BuiltNet (N A : Type) where
  /-- The places of the net. -/
  places    : List N
  /-- The definitions of its transitions, in declaration order. -/
  trans     : List (TransDef N A)
  /-- The terminal places ([EXEC-042]). -/
  terminals : List N

/-- The reference net builder: reject a terminal place some transition consumes from or reads
([EXEC-042] AC5; the message is a stand-in, the spec fixes none); otherwise collect every declared
place, every terminal place and every place an added transition names (duplicates dropped; the
order of places is not normative), keep the transitions in the order added, and keep the terminal
places in declaration order with repeated declarations dropped. All three runtimes add a terminal
place to the net's places and declare it once (the Rust core crate's `PetriNet` builder,
`java/src/main/java/org/libpetri/core/PetriNet.java:362-367`,
`typescript/src/core/petri-net.ts:199-203`). -/
def refNetBuild [DecidableEq N] {B : TBuilder N A} (inp : NetIn B) :
    Except String (BuiltNet N A) :=
  if inp.terminals.any (fun p => (inp.trans.map B.defOf).any fun d =>
      decide (p ∈ d.core.inputs.map (·.place) ∨ p ∈ d.core.reads))
  then .error "EXEC-042"
  else .ok ⟨(inp.places ++ inp.terminals ++
      (inp.trans.map B.defOf).flatMap TransDef.namedPlaces).dedup,
    inp.trans.map B.defOf, inp.terminals.eraseDups⟩

/-- The untimed view of a built net, which every firing block runs on. -/
def BuiltNet.toNet (b : BuiltNet N A) : Net N := ⟨b.places, b.trans.map TransDef.toTrans⟩

/-- The timed view of a built net with deadline tolerance `tol`: a transition's timing is the one
of the definition the net holds under its name (ruling D10), `Immediate` for a name the net does
not hold. -/
def BuiltNet.toTimed (b : BuiltNet N A) (tol : Nat) : TimedNet N :=
  ⟨b.toNet, fun t => ((b.trans.find? (·.core.name == t.core.name)).map (·.timing)).getD .immediate,
    tol⟩

/-- A successful reference net build keeps the added transitions' definitions, in the order
added. -/
theorem refNetBuild_trans [DecidableEq N] {B : TBuilder N A} {inp : NetIn B} {b : BuiltNet N A}
    (h : refNetBuild inp = .ok b) : b.trans = inp.trans.map B.defOf := by
  unfold refNetBuild at h
  split at h
  · cases h
  · cases h; rfl

/-- Every transition of a net built by the reference net builder from instances of the
reference transition builder builds and has a valid timing. -/
theorem refNetBuild_trans_ok [DecidableEq N] [ToString N]
    {inp : NetIn (refTransBuild (N := N) (A := A))} {b : BuiltNet N A}
    (h : refNetBuild inp = .ok b) : ∀ d ∈ b.trans, Builds d.toTrans ∧ d.timing.Valid := by
  intro d hd
  rw [refNetBuild_trans h, List.mem_map] at hd
  obtain ⟨x, -, rfl⟩ := hd
  exact refTransBuild_inst_ok x

end Libpetri.Reference
