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
  a valid timing (`refNetBuild_trans_ok`). A net holds only builder outputs (`FromBuilder`), also
  after binding (`refBind_fromBuilder`); composition rebuilds through the builder.

The fan-out parts, one per block of wave W2:

* **Place identity** ([CORE-002]): `PlaceKeyed`, a place model whose identity is equality of a
  key, with the two runtime readings `refPlacesByName` (TypeScript, Rust, Python) and
  `refPlacesByNameType` (Java) and their divergence (`place_identity_divergence`).
* **Net builder** ([CORE-040]): `refNetBuild` and its characterisation: the transitions in the
  order added, exactly the declared, terminal and arc places, none twice, no rejection of its own
  (`refNetBuild_eq_ok_iff`, `refNetBuild_mem_places`, `refNetBuild_places_nodup`,
  `refNetBuild_of_terminals_nil`).
* **Builder state machine** ([CORE-041]): `BuilderApi`, the reference `copyBuilder` (a handle
  shows the net built from what was added and never changes) and `aliasBuilder`, a wrong
  builder that hands out its own collections, which a later call changes.
* **Binding** ([CORE-042]): `refBind` with a resolver, the map-form readings `mapKeep` (Rust) and
  `mapClobber` (Java, TypeScript); binding changes only action tags.
* **Compile check** ([CORE-043]): `refCompile` and `refVerifyEntry` over the passthrough tag
  (`Act.isPassthrough`), failing on the first output-declaring transition that carries
  passthrough, by name.
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

/-! ## Place identity -/

/-- A place model ([CORE-002]): host place objects `P`, each with a name (of type `Nm`) and a
token type (of type `Ty`), and the key `K` the engine identifies a place by. Two place objects are
the same place exactly when their keys are equal (`PlaceKeyed.Same`); the key takes no state, so
the identity is stable for the lifetime of a net. The key type is the place type `N` of every
other model (the glossary's `PlaceName N := N`, identity = equality on `N`), and composition's
prefix renaming acts on keys. The key type is a field, not a parameter, so that both runtime
readings are models at every choice of `Nm` and `Ty`. -/
structure PlaceKeyed (Nm Ty : Type) where
  /-- The host place objects. -/
  P    : Type
  /-- The key type: the place type `N` of the other models. -/
  K    : Type
  /-- The name of a place object. -/
  name : P → Nm
  /-- The token type of a place object. -/
  ty   : P → Ty
  /-- The key the engine identifies a place object by. -/
  key  : P → K

/-- Two place objects are the same place: their keys are equal ([CORE-002]). -/
def PlaceKeyed.Same {Nm Ty : Type} (M : PlaceKeyed Nm Ty) (p q : M.P) : Prop := M.key p = M.key q

/-- Place identity is an equivalence, by construction. -/
theorem PlaceKeyed.same_equivalence {Nm Ty : Type} (M : PlaceKeyed Nm Ty) : Equivalence M.Same :=
  ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

/-- **Name identity** (TypeScript, Rust, Python): a place object is a name and a token type, and
the key is the name (Rust's `PartialEq` and `Hash` for `Place` in `rust/libpetri-core/src/place.rs`, the
`Place` interface in `typescript/src/core/place.ts`).
The key type is the name type: `N := Nm` (`String` in all three). -/
def refPlacesByName {Nm Ty : Type} : PlaceKeyed Nm Ty where
  P := Nm × Ty
  K := Nm
  name := Prod.fst
  ty := Prod.snd
  key := Prod.fst

/-- **Name-and-type identity** (Java, a record of name and token type,
`Place` in `java/src/main/java/org/libpetri/core/Place.java`): the key is the pair. The key type is
`N := Nm × Ty`. -/
def refPlacesByNameType {Nm Ty : Type} : PlaceKeyed Nm Ty where
  P := Nm × Ty
  K := Nm × Ty
  name := Prod.fst
  ty := Prod.snd
  key := id

/- The two runtime readings are the witness models of the place-identity block. -/
#spec_witness refPlacesByName
#spec_witness refPlacesByNameType

/-- Under name identity the key type is the name type. -/
theorem refPlacesByName_K {Nm Ty : Type} : (refPlacesByName (Nm := Nm) (Ty := Ty)).K = Nm := rfl

/-- Under name-and-type identity the key type is the pair of name and token type. -/
theorem refPlacesByNameType_K {Nm Ty : Type} :
    (refPlacesByNameType (Nm := Nm) (Ty := Ty)).K = (Nm × Ty) := rfl

/-- Under name identity two place objects are the same place exactly when their names are equal. -/
theorem refPlacesByName_same {Nm Ty : Type} {p q : Nm × Ty} :
    (refPlacesByName (Nm := Nm) (Ty := Ty)).Same p q ↔ p.1 = q.1 := Iff.rfl

/-- Under name-and-type identity two place objects are the same place exactly when their names
and token types are equal. -/
theorem refPlacesByNameType_same {Nm Ty : Type} {p q : Nm × Ty} :
    (refPlacesByNameType (Nm := Nm) (Ty := Ty)).Same p q ↔ p.1 = q.1 ∧ p.2 = q.2 := by
  show p = q ↔ _
  exact Prod.ext_iff

/-- **The two readings differ** on two places of one name and different token types: one place
under name identity, two under name-and-type identity ([MOD-024]'s divergence). -/
theorem place_identity_divergence {Nm Ty : Type} (n : Nm) {t₁ t₂ : Ty} (h : t₁ ≠ t₂) :
    (refPlacesByName (Nm := Nm) (Ty := Ty)).Same (n, t₁) (n, t₂) ∧
      ¬ (refPlacesByNameType (Nm := Nm) (Ty := Ty)).Same (n, t₁) (n, t₂) :=
  ⟨rfl, fun e => h (refPlacesByNameType_same.1 e).2⟩

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
timing check after the input checks and before the output-spec checks (`TransitionBuilder::build`, `transition.rs`);
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

/-- A net builder over the instances of transition builder `B` ([CORE-040]): from what the host
added, a built net or a rejection with a message. -/
abbrev NetBuilder (B : TBuilder N A) : Type := NetIn B → Except String (BuiltNet N A)

/-- A definition consumes from or reads place `p`: an input arc or a read arc names `p`. A
terminal place must be neither ([EXEC-042] AC5). -/
def TransDef.ConsumesOrReads (d : TransDef N A) (p : N) : Prop :=
  p ∈ d.core.inputs.map (·.place) ∨ p ∈ d.core.reads

/-- A net input declares a terminal place that one of its added transitions consumes from or
reads ([EXEC-042] AC5): the one case the reference net builder rejects. -/
def NetIn.TerminalClash {B : TBuilder N A} (inp : NetIn B) : Prop :=
  ∃ p ∈ inp.terminals, ∃ x ∈ inp.trans, (B.defOf x).ConsumesOrReads p

/-- The net the reference net builder returns when it accepts: every declared place, every
terminal place and every place an added transition names (duplicates dropped; the order of places
is not normative, ruling D32 orders transitions only), the added transitions' definitions in the
order added, and the terminal places in declaration order with repeated declarations dropped. -/
def NetIn.collect [DecidableEq N] {B : TBuilder N A} (inp : NetIn B) : BuiltNet N A :=
  ⟨(inp.places ++ inp.terminals ++ (inp.trans.map B.defOf).flatMap TransDef.namedPlaces).dedup,
    inp.trans.map B.defOf, inp.terminals.eraseDups⟩

/-- The reference net builder: reject a terminal place some transition consumes from or reads
([EXEC-042] AC5; the message is a stand-in, the spec fixes none); otherwise return `collect`:
every declared place, every terminal place and every place an added transition names, the
transitions in the order added, the terminal places once each. It rejects nothing of its own
([CORE-040]). All three runtimes add a terminal place to the net's places and declare it once (the
Rust core crate's `PetriNetBuilder::terminal`, `PetriNet.Builder.terminal` in
`java/src/main/java/org/libpetri/core/PetriNet.java`, `PetriNetBuilder.terminal` in
`typescript/src/core/petri-net.ts`). Fusion sets, instance composition and retired ports
are not modelled: they rewrite arcs and drop places, and belong to the composition model (W8). -/
def refNetBuild [DecidableEq N] {B : TBuilder N A} (inp : NetIn B) :
    Except String (BuiltNet N A) :=
  if inp.terminals.any (fun p => (inp.trans.map B.defOf).any fun d =>
      decide (p ∈ d.core.inputs.map (·.place) ∨ p ∈ d.core.reads))
  then .error "EXEC-042"
  else .ok inp.collect

/- The reference net builder is the witness model of the net-builder blocks. -/
#spec_witness refNetBuild

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

section NetBuild

variable [DecidableEq N] {B : TBuilder N A}

omit [DecidableEq N] in
/-- The places a definition names, by arc kind: an input, inhibitor, read or reset place, or a
place of its output specification (an output arc, [IO-017]). -/
theorem mem_namedPlaces {d : TransDef N A} {p : N} :
    p ∈ d.namedPlaces ↔
      p ∈ inPlaces d.toTrans ∨ InhibitorArc d.toTrans p ∨ ReadArc d.toTrans p ∨
        ResetArc d.toTrans p ∨ OutputArc d.toTrans p := by
  unfold TransDef.namedPlaces OutputArc inPlaces InhibitorArc ReadArc ResetArc
  cases ho : d.out with
  | none => simp [TransDef.toTrans, ho]
  | some o => simp [TransDef.toTrans, ho]

/-- The boolean test of the reference net builder is `TerminalClash`. -/
theorem terminalClash_iff_any (inp : NetIn B) :
    (inp.terminals.any (fun p => (inp.trans.map B.defOf).any fun d =>
      decide (p ∈ d.core.inputs.map (·.place) ∨ p ∈ d.core.reads))) = true ↔
      inp.TerminalClash := by
  simp only [List.any_eq_true, List.mem_map, decide_eq_true_eq, NetIn.TerminalClash,
    TransDef.ConsumesOrReads]
  constructor
  · rintro ⟨p, hp, _, ⟨x, hx, rfl⟩, h⟩
    exact ⟨p, hp, x, hx, h⟩
  · rintro ⟨p, hp, x, hx, h⟩
    exact ⟨p, hp, B.defOf x, ⟨x, hx, rfl⟩, h⟩

/-- The reference net builder returns `b` exactly when no terminal place clashes and `b` is the
collected net. -/
theorem refNetBuild_eq_ok_iff {inp : NetIn B} {b : BuiltNet N A} :
    refNetBuild inp = .ok b ↔ ¬ inp.TerminalClash ∧ b = inp.collect := by
  unfold refNetBuild
  split
  · rename_i h
    exact ⟨fun c => (nomatch c), fun ⟨hn, _⟩ => absurd ((terminalClash_iff_any inp).1 h) hn⟩
  · rename_i h
    refine ⟨fun c => ⟨fun hc => h ((terminalClash_iff_any inp).2 hc), (Except.ok.inj c).symm⟩,
      fun ⟨_, e⟩ => e ▸ rfl⟩

/-- The reference net builder accepts exactly when no terminal place clashes. -/
theorem refNetBuild_ok_iff {inp : NetIn B} :
    (∃ b, refNetBuild inp = .ok b) ↔ ¬ inp.TerminalClash :=
  ⟨fun ⟨_, h⟩ => (refNetBuild_eq_ok_iff.1 h).1, fun h => ⟨_, refNetBuild_eq_ok_iff.2 ⟨h, rfl⟩⟩⟩

/-- The reference net builder rejects exactly when a terminal place clashes ([EXEC-042] AC5). -/
theorem refNetBuild_error_iff {inp : NetIn B} :
    (∃ e, refNetBuild inp = .error e) ↔ inp.TerminalClash := by
  unfold refNetBuild
  split
  · rename_i h
    exact ⟨fun _ => (terminalClash_iff_any inp).1 h, fun _ => ⟨_, rfl⟩⟩
  · rename_i h
    exact ⟨fun ⟨_, c⟩ => (nomatch c), fun hc => absurd ((terminalClash_iff_any inp).2 hc) h⟩

/-- With no terminal place declared the reference net builder rejects nothing: it has no
rejection of its own ([CORE-040]). -/
theorem refNetBuild_of_terminals_nil {inp : NetIn B} (h : inp.terminals = []) :
    refNetBuild inp = .ok inp.collect :=
  refNetBuild_eq_ok_iff.2 ⟨fun ⟨p, hp, _⟩ => (by rw [h] at hp; cases hp), rfl⟩

/-- The places of the collected net: the declared places, the terminal places and every place an
added transition names. -/
theorem mem_collect_places {inp : NetIn B} {p : N} :
    p ∈ inp.collect.places ↔
      p ∈ inp.places ∨ p ∈ inp.terminals ∨ ∃ x ∈ inp.trans, p ∈ (B.defOf x).namedPlaces := by
  simp only [NetIn.collect, List.mem_dedup, List.mem_append, List.mem_flatMap, List.mem_map,
    or_assoc]
  constructor
  · rintro (h | h | ⟨_, ⟨x, hx, rfl⟩, h⟩)
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr ⟨x, hx, h⟩)
  · rintro (h | h | ⟨x, hx, h⟩)
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr ⟨B.defOf x, ⟨x, hx, rfl⟩, h⟩)

/-- The collected net holds no place twice. -/
theorem collect_places_nodup (inp : NetIn B) : inp.collect.places.Nodup :=
  List.nodup_dedup _

/-- A net built by the reference net builder has as places exactly the declared places, the
terminal places and the places its added transitions name ([CORE-040]). -/
theorem refNetBuild_mem_places {inp : NetIn B} {b : BuiltNet N A} (h : refNetBuild inp = .ok b)
    {p : N} :
    p ∈ b.places ↔
      p ∈ inp.places ∨ p ∈ inp.terminals ∨ ∃ x ∈ inp.trans, p ∈ (B.defOf x).namedPlaces := by
  rw [(refNetBuild_eq_ok_iff.1 h).2]; exact mem_collect_places

/-- A net built by the reference net builder holds no place twice ([CORE-040]). -/
theorem refNetBuild_places_nodup {inp : NetIn B} {b : BuiltNet N A}
    (h : refNetBuild inp = .ok b) : b.places.Nodup := by
  rw [(refNetBuild_eq_ok_iff.1 h).2]; exact collect_places_nodup inp

/-- A net built by the reference net builder keeps the declared terminal places, once each, in
declaration order. -/
theorem refNetBuild_terminals {inp : NetIn B} {b : BuiltNet N A} (h : refNetBuild inp = .ok b) :
    b.terminals = inp.terminals.eraseDups := by
  rw [(refNetBuild_eq_ok_iff.1 h).2]; rfl

/-- Every place a transition of a net built by the reference net builder names is a place of the
net: the arc places of all five kinds are collected ([CORE-040], ruling D32). -/
theorem refNetBuild_arcs_declared {inp : NetIn B} {b : BuiltNet N A}
    (h : refNetBuild inp = .ok b) : ∀ d ∈ b.trans, ∀ p ∈ d.namedPlaces, p ∈ b.places := by
  intro d hd p hp
  rw [refNetBuild_trans h, List.mem_map] at hd
  obtain ⟨x, hx, rfl⟩ := hd
  exact (refNetBuild_mem_places h).2 (.inr (.inr ⟨x, hx, hp⟩))

end NetBuild

/-! ## A net holds only builder outputs -/

/-- Every transition of `b` is the definition of an instance of transition builder `B`: the net
holds only what `B`'s build calls returned. -/
def BuiltNet.FromBuilder (B : TBuilder N A) (b : BuiltNet N A) : Prop :=
  ∀ d ∈ b.trans, ∃ x : B.I, B.defOf x = d

/-- A net built by the reference net builder holds only definitions of the transition builder's
instances. -/
theorem refNetBuild_fromBuilder [DecidableEq N] {B : TBuilder N A} {inp : NetIn B}
    {b : BuiltNet N A} (h : refNetBuild inp = .ok b) : b.FromBuilder B := by
  intro d hd
  rw [refNetBuild_trans h, List.mem_map] at hd
  obtain ⟨x, -, rfl⟩ := hd
  exact ⟨x, rfl⟩

/-- The definition of every instance of the reference transition builder is the resolved
definition of an input some build call accepted. -/
theorem refTransBuild_defOf [DecidableEq N] [ToString N]
    (x : (refTransBuild (N := N) (A := A)).I) :
    ∃ k i, refTransBuildRaw k i = .ok (k, i.resolve) ∧
      (refTransBuild (N := N) (A := A)).defOf x = i.resolve := by
  obtain ⟨k, i, h⟩ := x.2
  have he := (refTransBuildRaw_ok.1 h).2.2
  refine ⟨k, i, he ▸ h, ?_⟩
  show x.1.2 = i.resolve
  rw [he]

/-! ## The builder as a state machine -/

/-- One call on a net builder before `build` ([CORE-040], [EXEC-042]): declare a place, add an
instance of transition builder `B`, or declare a terminal place. -/
inductive BOp (B : TBuilder N A) where
  /-- Declare a place. -/
  | place (p : N)
  /-- Add a transition (an instance `B` returned). -/
  | trans (x : B.I)
  /-- Declare a terminal place ([EXEC-042]). -/
  | terminal (p : N)

/-- The net input before any call. -/
def NetIn.empty {B : TBuilder N A} : NetIn B := ⟨[], [], []⟩

/-- A net input after one more call: the call's place, transition or terminal place appended. -/
def NetIn.addOp {B : TBuilder N A} (inp : NetIn B) : BOp B → NetIn B
  | .place p => { inp with places := inp.places ++ [p] }
  | .trans x => { inp with trans := inp.trans ++ [x] }
  | .terminal p => { inp with terminals := inp.terminals ++ [p] }

/-- The net input a sequence of calls from the empty builder gives: what was added, in the order
added. -/
def NetIn.ofOps {B : TBuilder N A} (ops : List (BOp B)) : NetIn B :=
  ops.foldl NetIn.addOp NetIn.empty

/-- A net builder as a state machine ([CORE-041]): states `S`, the start state, one step per call,
`build` (the next state and a handle on the built net), and `view`, what a handle shows in a
state (a built net, or the rejection `build` reported). The state and handle types are fields,
so a model chooses its own. -/
structure BuilderApi (B : TBuilder N A) where
  /-- The builder's states. -/
  S     : Type
  /-- The handles `build` returns. -/
  H     : Type
  /-- The state of a new builder. -/
  init  : S
  /-- One call before `build`. -/
  step  : S → BOp B → S
  /-- `build`: the state after it and the handle on the built net. -/
  build : S → S × H
  /-- What a handle shows in a state: the built net, or the rejection. -/
  view  : S → H → Except String (BuiltNet N A)

/-- The state after a sequence of calls. -/
def BuilderApi.run {B : TBuilder N A} (BA : BuilderApi B) (s : BA.S) (ops : List (BOp B)) :
    BA.S :=
  ops.foldl BA.step s

section Api

variable [DecidableEq N] {B : TBuilder N A}

/-- **The reference builder state machine**: the state is what was added so far and the nets
built so far; `build` runs the reference net builder on what was added and keeps the result, and
a handle is the index of a result. A later call changes what was added, never a kept result: Java
copies its collections in `build()` (the private `PetriNet` constructor it calls,
`java/src/main/java/org/libpetri/core/PetriNet.java`), TypeScript copies its place and transition
sets in `build()` (`PetriNetBuilder.build`, `typescript/src/core/petri-net.ts`), Rust consumes the
builder (`PetriNetBuilder::build` takes `self`, `rust/libpetri-core/src/petri_net.rs`). -/
def copyBuilder (B : TBuilder N A) : BuilderApi B where
  S := NetIn B × List (Except String (BuiltNet N A))
  H := Nat
  init := (NetIn.empty, [])
  step s op := (s.1.addOp op, s.2)
  build s := ((s.1, s.2 ++ [refNetBuild s.1]), s.2.length)
  view s h := s.2[h]?.getD (.error "no such net")

/- The reference builder state machine is the witness model of the builder-trace blocks. -/
#spec_witness copyBuilder

/-- A wrong builder (ruling D66 (a); the TypeScript behaviour RD-02 recorded, before `build()`
copied its sets): `build` hands out the builder's own collections, so a handle shows the reference
net builder's result on what the builder holds now, including calls made after `build`. -/
def aliasBuilder (B : TBuilder N A) : BuilderApi B where
  S := NetIn B
  H := Unit
  init := NetIn.empty
  step := NetIn.addOp
  build s := (s, ())
  view s _ := refNetBuild s

/-- Running calls on the reference builder state machine appends them to what was added and keeps
the built nets. -/
theorem copyBuilder_run (s : (copyBuilder B).S) (ops : List (BOp B)) :
    (copyBuilder B).run s ops = (ops.foldl NetIn.addOp s.1, s.2) := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact ih ((copyBuilder B).step s op)

/-- A call never changes what a handle of the reference builder state machine shows. -/
theorem copyBuilder_view_step (s : (copyBuilder B).S) (op : BOp B) (h : Nat) :
    (copyBuilder B).view ((copyBuilder B).step s op) h = (copyBuilder B).view s h := rfl

/-- A later `build` never changes what an earlier handle of the reference builder state machine
shows. -/
theorem copyBuilder_view_build (s : (copyBuilder B).S) {h : Nat} (hh : h < s.2.length) :
    (copyBuilder B).view ((copyBuilder B).build s).1 h = (copyBuilder B).view s h := by
  show (s.2 ++ [refNetBuild s.1])[h]?.getD _ = s.2[h]?.getD _
  rw [List.getElem?_append_left hh]

/-- What the handle `build` returns shows right after `build`: the reference net builder's result
on what was added. -/
theorem copyBuilder_view_built (s : (copyBuilder B).S) :
    (copyBuilder B).view ((copyBuilder B).build s).1 ((copyBuilder B).build s).2 =
      refNetBuild s.1 := by
  show (s.2 ++ [refNetBuild s.1])[s.2.length]?.getD _ = _
  simp

/-- **Builder trace.** After any calls from a new builder, the handle `build` returns shows the
reference net builder's result on exactly those calls. -/
theorem copyBuilder_trace (ops : List (BOp B)) :
    let s := (copyBuilder B).run (copyBuilder B).init ops
    (copyBuilder B).view ((copyBuilder B).build s).1 ((copyBuilder B).build s).2 =
      refNetBuild (NetIn.ofOps ops) := by
  show (copyBuilder B).view ((copyBuilder B).build ((copyBuilder B).run (copyBuilder B).init ops)).1
    ((copyBuilder B).build ((copyBuilder B).run (copyBuilder B).init ops)).2 = _
  rw [copyBuilder_view_built, copyBuilder_run]
  rfl

/-- **Stability.** What the handle `build` returns shows does not change under any later calls on
the reference builder state machine. -/
theorem copyBuilder_stable (s : (copyBuilder B).S) (later : List (BOp B)) :
    (copyBuilder B).view ((copyBuilder B).run ((copyBuilder B).build s).1 later)
        ((copyBuilder B).build s).2 =
      (copyBuilder B).view ((copyBuilder B).build s).1 ((copyBuilder B).build s).2 := by
  rw [copyBuilder_run]; rfl

/-- The aliasing builder also shows, right after `build`, the reference net builder's result on
what was added: the trace alone does not separate it from the reference. -/
theorem aliasBuilder_trace (ops : List (BOp B)) :
    let s := (aliasBuilder B).run (aliasBuilder B).init ops
    (aliasBuilder B).view ((aliasBuilder B).build s).1 ((aliasBuilder B).build s).2 =
      refNetBuild (NetIn.ofOps ops) := rfl

/-- Declaring a place keeps an accepted net input accepted and puts the place among the built
net's places. -/
theorem refNetBuild_addPlace {inp : NetIn B} {b : BuiltNet N A} (h : refNetBuild inp = .ok b)
    (p : N) : ∃ b', refNetBuild (inp.addOp (.place p)) = .ok b' ∧ p ∈ b'.places := by
  have hn : ¬ (inp.addOp (.place p)).TerminalClash := (refNetBuild_eq_ok_iff.1 h).1
  exact ⟨_, refNetBuild_eq_ok_iff.2 ⟨hn, rfl⟩,
    mem_collect_places.2 (.inl (List.mem_append_right _ (List.mem_singleton_self p)))⟩

/-- **The aliasing builder is not stable**: after an accepted `build`, declaring a place the
built net does not hold changes what the handle shows. -/
theorem aliasBuilder_unstable {s : (aliasBuilder B).S} {b : BuiltNet N A}
    (h : refNetBuild (B := B) s = .ok b) {p : N} (hp : p ∉ b.places) :
    (aliasBuilder B).view ((aliasBuilder B).run ((aliasBuilder B).build s).1 [.place p])
        ((aliasBuilder B).build s).2 ≠
      (aliasBuilder B).view ((aliasBuilder B).build s).1 ((aliasBuilder B).build s).2 := by
  obtain ⟨b', hb', hpb'⟩ := refNetBuild_addPlace h p
  show refNetBuild (s.addOp (.place p)) ≠ refNetBuild s
  rw [hb', h]
  intro e
  exact hp (Except.ok.inj e ▸ hpb')

/-- The reference net builder builds the empty net from a new builder. -/
theorem refNetBuild_empty : refNetBuild (NetIn.empty (B := B)) = .ok ⟨[], [], []⟩ :=
  refNetBuild_of_terminals_nil rfl

/-- The aliasing builder is unstable at every place type with a place: build a new builder, then
declare a place. -/
theorem aliasBuilder_unstable_empty (p : N) :
    (aliasBuilder B).view
        ((aliasBuilder B).run ((aliasBuilder B).build NetIn.empty).1 [.place p])
        ((aliasBuilder B).build NetIn.empty).2 ≠
      (aliasBuilder B).view ((aliasBuilder B).build NetIn.empty).1
        ((aliasBuilder B).build NetIn.empty).2 :=
  aliasBuilder_unstable refNetBuild_empty List.not_mem_nil

end Api

/-! ## Action binding -/

/-- The definition after binding with resolver `r` ([CORE-042]): a name `r` answers gets that
action, a name it defers (`none`) keeps its action; every other field is kept. -/
def TransDef.bindWith (r : String → Option (Act A)) (d : TransDef N A) : TransDef N A :=
  { d with action := (r d.core.name).getD d.action }

/-- **The reference binding** ([CORE-042], resolver form): every transition bound with the
resolver, by name; places and terminal places kept. It never rejects (it is a function). -/
def refBind (b : BuiltNet N A) (r : String → Option (Act A)) : BuiltNet N A :=
  { b with trans := b.trans.map (TransDef.bindWith r) }

/- The reference binding is the witness model of the binding blocks. -/
#spec_witness refBind

/-- The map form as Rust reads it: a name the map omits is deferred (keeps its action,
`PetriNet::bind_actions` in `rust/libpetri-core/src/petri_net.rs`). -/
def mapKeep (m : String → Option (Act A)) : String → Option (Act A) := m

/-- The map form as Java and TypeScript read it: a name the map omits gets passthrough
(`PetriNet.bindActions(Map)` in `java/src/main/java/org/libpetri/core/PetriNet.java`,
`PetriNet.bindActions` in `typescript/src/core/petri-net.ts`). -/
def mapClobber (m : String → Option (Act A)) : String → Option (Act A) :=
  fun n => some ((m n).getD .passthrough)

/-- Binding keeps the name, the arcs and the output specification. -/
theorem bindWith_core (r : String → Option (Act A)) (d : TransDef N A) :
    (d.bindWith r).core = d.core ∧ (d.bindWith r).out = d.out := ⟨rfl, rfl⟩

/-- Binding keeps the timing and the priority. -/
theorem bindWith_timing_priority (r : String → Option (Act A)) (d : TransDef N A) :
    (d.bindWith r).timing = d.timing ∧ (d.bindWith r).priority = d.priority := ⟨rfl, rfl⟩

/-- Binding changes nothing the firing view reads. -/
theorem bindWith_toTrans (r : String → Option (Act A)) (d : TransDef N A) :
    (d.bindWith r).toTrans = d.toTrans := rfl

/-- A name the resolver answers gets that action. -/
theorem bindWith_answered {r : String → Option (Act A)} {d : TransDef N A} {a : Act A}
    (h : r d.core.name = some a) : (d.bindWith r).action = a := by
  simp [TransDef.bindWith, h]

/-- A name the resolver defers keeps its definition. -/
theorem bindWith_deferred {r : String → Option (Act A)} {d : TransDef N A}
    (h : r d.core.name = none) : d.bindWith r = d := by
  simp [TransDef.bindWith, h]

/-- The reference binding keeps the places and the terminal places. -/
theorem refBind_places (b : BuiltNet N A) (r : String → Option (Act A)) :
    (refBind b r).places = b.places ∧ (refBind b r).terminals = b.terminals := ⟨rfl, rfl⟩

/-- The reference binding binds every transition, in order. -/
theorem refBind_trans (b : BuiltNet N A) (r : String → Option (Act A)) :
    (refBind b r).trans = b.trans.map (TransDef.bindWith r) := rfl

/-- The reference binding changes nothing the untimed view of the net reads. -/
theorem refBind_toNet (b : BuiltNet N A) (r : String → Option (Act A)) :
    (refBind b r).toNet = b.toNet := by
  simp only [BuiltNet.toNet, refBind, List.map_map]
  rfl

/-- The reference binding changes nothing the timed view of the net reads. -/
theorem refBind_toTimed (b : BuiltNet N A) (r : String → Option (Act A)) (tol : Nat) :
    (refBind b r).toTimed tol = b.toTimed tol := by
  unfold BuiltNet.toTimed
  rw [refBind_toNet]
  congr 1
  funext t
  simp only [refBind, List.find?_map, Option.map_map]
  rfl

/-- Both map forms give a mapped name its action. -/
theorem mapForms_mapped {m : String → Option (Act A)} {d : TransDef N A} {a : Act A}
    (h : m d.core.name = some a) :
    (d.bindWith (mapKeep m)).action = a ∧ (d.bindWith (mapClobber m)).action = a :=
  ⟨bindWith_answered h, bindWith_answered (by simp [mapClobber, h])⟩

/-- Both map forms leave an unmapped transition that carries passthrough with passthrough: the
part of the map form all three runtimes share. -/
theorem mapForms_unmapped_passthrough {m : String → Option (Act A)} {d : TransDef N A}
    (h : m d.core.name = none) (hp : d.action = .passthrough) :
    (d.bindWith (mapKeep m)).action = .passthrough ∧
      (d.bindWith (mapClobber m)).action = .passthrough :=
  ⟨by rw [bindWith_deferred (r := mapKeep m) h]; exact hp,
    bindWith_answered (by simp [mapClobber, h])⟩

/-- The two map forms differ on an unmapped transition that carries another action: Rust keeps
it, Java and TypeScript replace it by passthrough (the spec's documented divergence). -/
theorem mapForms_differ {m : String → Option (Act A)} {d : TransDef N A} {a : A}
    (h : m d.core.name = none) (ha : d.action = .other a) :
    (d.bindWith (mapKeep m)).action = .other a ∧
      (d.bindWith (mapClobber m)).action = .passthrough :=
  ⟨by rw [bindWith_deferred (r := mapKeep m) h]; exact ha,
    bindWith_answered (by simp [mapClobber, h])⟩

/-- Binding a net of the reference transition builder's definitions gives a net of its
definitions again: a bound definition is what a build call on the same input with the bound
action returns. A net holds only builder outputs, also after binding. -/
theorem refBind_fromBuilder [ToString N] [DecidableEq N] {b : BuiltNet N A}
    (h : b.FromBuilder (refTransBuild (N := N) (A := A))) (r : String → Option (Act A)) :
    (refBind b r).FromBuilder (refTransBuild (N := N) (A := A)) := by
  intro d' hd'
  rw [refBind_trans, List.mem_map] at hd'
  obtain ⟨d, hd, rfl⟩ := hd'
  obtain ⟨x, rfl⟩ := h d hd
  obtain ⟨k, i, hi, hx⟩ := refTransBuild_defOf x
  rw [hx]
  let i' : TransIn N A := { i with action := some ((r i.resolve.core.name).getD i.resolve.action) }
  obtain ⟨hb, ht, -⟩ := refTransBuildRaw_ok.1 hi
  have hi' : refTransBuildRaw k i' = .ok (k, i'.resolve) := refTransBuildRaw_ok.2 ⟨hb, ht, rfl⟩
  exact ⟨⟨(k, i'.resolve), k, i', hi'⟩, rfl⟩

/-! ## The compile check and the verification entry check -/

/-- The passthrough tag: the action is the built-in passthrough ([CORE-051]; recognised by
identity, so another action that produces nothing is not passthrough). -/
def Act.isPassthrough : Act A → Bool
  | .passthrough => true
  | .other _ => false

/-- The passthrough tag holds exactly of the built-in passthrough. -/
theorem Act.isPassthrough_iff {x : Act A} : x.isPassthrough = true ↔ x = .passthrough := by
  cases x <;> simp [Act.isPassthrough]

/-- A definition declares an output specification and carries the built-in passthrough: the
pairing [CORE-043] rejects. -/
def TransDef.outputPassthrough (d : TransDef N A) : Bool := d.out.isSome && d.action.isPassthrough

/-- `outputPassthrough`, as a proposition. -/
theorem TransDef.outputPassthrough_iff {d : TransDef N A} :
    d.outputPassthrough = true ↔ d.out ≠ none ∧ d.action = .passthrough := by
  simp [TransDef.outputPassthrough, Act.isPassthrough_iff, Option.isSome_iff_ne_none]

/-- **The reference compile check** ([CORE-043]): `none` = this check passes; `some n` = it fails,
naming `n`, the name of the first transition in declaration order that declares an output
specification and carries passthrough (all three runtimes throw on the first offender in
transition order: `require_output_producing_actions`, called first by `CompiledNet::compile` in
`rust/libpetri-runtime/src/compiled_net.rs`, and `requireOutputProducingActions`, called first by
the `CompiledNet` constructor in `java/src/main/java/org/libpetri/runtime/CompiledNet.java` and
`typescript/src/runtime/compiled-net.ts`). -/
def refCompile (b : BuiltNet N A) : Option String :=
  (b.trans.find? TransDef.outputPassthrough).map (·.core.name)

/-- **The reference verification entry check** ([CORE-043] AC3): the same check at the
state-class-graph and SMT entry points. It is `refCompile` until the verifier model (W10) gives
its entry check, which is then identified with this one. -/
def refVerifyEntry (b : BuiltNet N A) : Option String := refCompile b

/- The two reference checks are the witness models of the compile-check blocks. -/
#spec_witness refCompile
#spec_witness refVerifyEntry

/-- The verification entry check refuses exactly the nets the compile check refuses, with the same
name. -/
theorem refVerifyEntry_eq : (refVerifyEntry : BuiltNet N A → Option String) = refCompile := rfl

/-- The compile check passes exactly when no transition that declares an output specification
carries passthrough. -/
theorem refCompile_eq_none_iff {b : BuiltNet N A} :
    refCompile b = none ↔ ∀ d ∈ b.trans, d.out ≠ none → d.action ≠ .passthrough := by
  simp only [refCompile, Option.map_eq_none_iff, List.find?_eq_none,
    TransDef.outputPassthrough_iff, not_and]

/-- The compile check fails naming `n` exactly when the first transition, in declaration order,
that declares an output specification and carries passthrough is named `n`. -/
theorem refCompile_eq_some_iff {b : BuiltNet N A} {n : String} :
    refCompile b = some n ↔
      ∃ l₁ d l₂, b.trans = l₁ ++ d :: l₂ ∧ d.out ≠ none ∧ d.action = .passthrough ∧
        d.core.name = n ∧ ∀ e ∈ l₁, ¬ (e.out ≠ none ∧ e.action = .passthrough) := by
  simp only [refCompile, Option.map_eq_some_iff, List.find?_eq_some_iff_append,
    TransDef.outputPassthrough_iff, Bool.not_eq_true', ne_eq]
  constructor
  · rintro ⟨d, ⟨hd, l₁, l₂, he, hl⟩, rfl⟩
    refine ⟨l₁, d, l₂, he, hd.1, hd.2, rfl, fun e he' hc => ?_⟩
    have := hl e he'
    rw [Bool.eq_false_iff, ne_eq, TransDef.outputPassthrough_iff] at this
    exact this hc
  · rintro ⟨l₁, d, l₂, he, ho, hp, rfl, hl⟩
    refine ⟨d, ⟨⟨ho, hp⟩, l₁, l₂, he, fun e he' => ?_⟩, rfl⟩
    rw [Bool.eq_false_iff, ne_eq, TransDef.outputPassthrough_iff]
    exact hl e he'

/-- When the compile check fails it names a transition of the net that declares an output
specification and carries passthrough. -/
theorem refCompile_some_mem {b : BuiltNet N A} {n : String} (h : refCompile b = some n) :
    ∃ d ∈ b.trans, d.out ≠ none ∧ d.action = .passthrough ∧ d.core.name = n := by
  obtain ⟨l₁, d, l₂, he, ho, hp, hn, -⟩ := refCompile_eq_some_iff.1 h
  exact ⟨d, by rw [he]; exact List.mem_append_right _ (List.mem_cons_self ..), ho, hp, hn⟩

/-- A transition that declares an output specification and carries passthrough makes the compile
check fail. -/
theorem refCompile_isSome {b : BuiltNet N A} {d : TransDef N A} (hd : d ∈ b.trans)
    (ho : d.out ≠ none) (hp : d.action = .passthrough) : (refCompile b).isSome := by
  cases h : refCompile b with
  | some _ => rfl
  | none => exact absurd hp (refCompile_eq_none_iff.1 h d hd ho)

/-- The compile check reads only the transitions: places and terminal places play no part. -/
theorem refCompile_trans {b b' : BuiltNet N A} (h : b.trans = b'.trans) :
    refCompile b = refCompile b' := by
  simp only [refCompile, h]

/-- A transition built without an action carries passthrough (the builder default, [CORE-051]). -/
theorem resolve_action_none {i : TransIn N A} (h : i.action = none) :
    i.resolve.action = .passthrough := by
  simp [TransIn.resolve, h]

end Libpetri.Reference
