import Libpetri.Spec.Registry
import Libpetri.Reference.Build

set_option linter.missingDocs true

/-!
# CORE-002: Place identity (`spec/01-core-model.md`)

CORE-002 is a pure-function requirement (kind F) over an abstract place model
`M : PlaceKeyed Nm Ty` (`Reference/Build.lean`): host place objects, each with a name, a token type
and the key the engine identifies it by. Two place objects are the same place exactly when their
keys are equal (`PlaceKeyed.Same`), so identity is an equivalence and takes no state by
construction. The key type is the place type `N` every other block is stated over (glossary
`PlaceName N := N`, identity = equality on `N`).

The statement fixes the identity to one of the two that exist (ruling D82 (a)): the same place
has one name, two places with the same name and the same token type are the same place, and
either the name alone decides (name identity) or the same place has one token type (name-and-type
identity). Lines 1 and 2 bracket the key between the name and the pair; line 3 rules out every
key strictly between them. The witnesses are the two runtime readings, name identity
`refPlacesByName` (TypeScript, Rust, Python) and name-and-type identity `refPlacesByNameType`
(Java). Wrong models are killed: a model in which every place is one place, reference identity
(each constructed object its own place, which the text before D82 allowed), a builder place set
that keys declared places by reference beside a compiled net that keys places by name (the
behaviour RD-03 recorded of TypeScript's builder), and a key that strips the
composition prefix (the Note). Each line has a mutant (the statement without that line): identity
by token type alone kills the one without line 1, reference identity the one without line 2, and
a key of the name and a coarsening of the token type the one without line 3.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference

/-! ## CORE-002: Place Identity -/

requirement CORE_002
  id "CORE-002"
  title "Place Identity"
  kind F
  scope "all implementations"
  source verbatim "spec/01-core-model.md"
  quote "Two places that are the same place *shall* have the same name."
        "Two places with the same name and the same token type *shall* be the same place."
        "An implementation *shall* identify a place either by its name, so that two places with the same name are the same place, or by its name and its token type, so that two places that are the same place have the same token type."
  reading "For every place model M (place objects with a name, a token type and a key; two objects are the same place when their keys are equal):"
          "for all place objects p and q, if p and q are the same place, p and q have the same name;"
          "for all place objects p and q, if p and q have the same name and the same token type, p and q are the same place;"
          "either for all place objects p and q, if p and q have the same name, p and q are the same place; or for all place objects p and q, if p and q are the same place, p and q have the same token type."
  assumes "A place model (PlaceKeyed, Reference/Build.lean) is the place identity of one implementation: its place objects P, the name and the token type of each, and the key K the engine identifies a place object by. Two place objects are the same place exactly when their keys are equal (PlaceKeyed.Same). K is the place type N of every other block (glossary PlaceName N := N, identity = equality on N): refPlacesByName_K and refPlacesByNameType_K. 'The same way throughout the implementation' is that one implementation is one place model, with one key function; an implementation that mixes two identities is modelled by one key that does both, and line 2 rejects such a mix (CORE_002_forbids_tsBuilderMix, a builder that keys declared places by reference beside a compiled net that keys them by name). An implementation whose equality and hash of place objects disagree is outside the model: their agreement is the host language's contract, and today Rust's PartialEq and Hash both use the name alone (the PartialEq and Hash impls for Place in rust/libpetri-core/src/place.rs)."
          "AC1 (a place is the same place as itself) holds of every place model by construction: the same place is equality of keys, an equivalence (PlaceKeyed.same_equivalence). It is no line of the statement, and no model can break it."
          "AC2 (two independently constructed places with different names are never the same place) is line 1, read backwards: places with different names are never the same place. A model in which every place is one place (CORE_002_forbids_onePlace) violates it, and so does identity by token type alone (CORE_002_mutant_noLine1_killed), which lines 2 and 3 accept."
          "AC3 (place identity is stable across the lifetime of a net) holds by the type of the model: the key of a place object is a function of the object alone, with no state, net or time argument, so no model can change a place's identity during a run."
          "Line 2 is the sentence ruling D82 (a) adds against the text before it, which allowed reference or ID-based equality, under which two place objects constructed separately with the same name and token type are two places; no implementation's engine does that (PartialEq for Place in rust/libpetri-core/src/place.rs compares names, the Place record in java/src/main/java/org/libpetri/core/Place.java is a record of name and token type, the CompiledNet constructor in typescript/src/runtime/compiled-net.ts keys places by name, and the Python binding identifies a place by its name, PyPlace in rust/libpetri-py/src/model.rs). Reference identity (core002_byRef) satisfies lines 1 and 3 (CORE_002_mutant_noLine2, killed by CORE_002_mutant_noLine2_killed) and violates line 2 (CORE_002_forbids_byRef)."
          "Line 3 is the rest of ruling D82 (a): the identity is one of the two that exist, the name or the name and the token type. With lines 1 and 2 it leaves exactly those two: under its first branch the same place is the same name, under its second the same place is the same name and token type. A key between the two, such as the name and a coarsening of the token type (core002_coarseType), meets lines 1 and 2 and fails line 3 (CORE_002_mutant_noLine3_killed). Name identity (TypeScript, Rust, Python; CORE_002_byName) takes the first branch and name-and-type identity (Java; CORE_002_byNameType) the second. They differ on two places of one name and different token types, one place by name and two by name and type (place_identity_divergence, cited by MOD-024)."
          "Which language uses which identity is not a line: the statement is over one abstract model and does not name a language. The body's per-language sentences are carried by the two witness models, whose definitions cite the runtime code (Reference/Build.lean, refPlacesByName and refPlacesByNameType). Java's token type is the run-time class a Java place records (the Place record in Place.java, Class<T> tokenType), so the model's token type for Java is that class: Place<List<String>> and Place<List<Integer>> of one name have one token type and are one place, which is name-and-type identity, not an identity between the two."
          "In TypeScript and Python the host language's own equality of place objects is not the place identity: place(\"A\") in TypeScript returns a new object each time (the place function in typescript/src/core/place.ts), and a Python Place defines no equality, so two objects of one name are unequal objects and one place. The model reads a place object as its name and token type, so host object equality is not modelled. TypeScript keys places by name throughout, as 'the same way throughout the implementation' asks: the net builder keeps the first place object seen for each name (PetriNetBuilder._places, a Map from name to place, typescript/src/core/petri-net.ts), a transition's input, read and output place sets keep one place per name (typescript/src/core/transition.ts placesByName, and allPlaces), the output spec's place sets do the same (typescript/src/core/out.ts allPlaces and enumerateBranches, IO-016 and IO-017), and the compiled net keys places by name (typescript/src/runtime/compiled-net.ts). So CORE_002_byName is the witness of TypeScript's identity in the builder, the built net and the compiled net alike. A builder that keyed declared places by reference beside a compiled net that keys them by name (core002_tsBuilderMix, the behaviour RD-03 in spec/runtime-defects.md recorded of TypeScript's builder) is rejected by line 2 (CORE_002_forbids_tsBuilderMix)."
          "In Java two places of one name and different token types are two places, so a Java net may hold two places with one name. Requirements keyed by place name (snapshot and restore, CORE-073; event and export identifiers) assume one place per name in Java, the place analogue of the unique transition names of ruling D10; CORE-073 already puts such a net outside snapshot and restore. This block states no such assumption itself."
          "The Note (a body place instantiated under two prefixes gives two distinct places) is MOD-010's renaming applied to the key: the two instances have different names, so line 1 makes them different places. A key that strips the prefix (core002_stripPrefix) makes \"a/x\" and \"b/x\" one place and is rejected (CORE_002_forbids_stripPrefix). Renaming itself is the composition model's (wave W8)."
          "The test derivation is lines 1 and 2 with CORE_002_nonvacuous: two places named A and B are different places (line 1); one place referenced twice, and two places constructed separately with one name and one token type, are one place (line 2, the place object (A, 0) the same as an equal one under both identities); and one name with token types 0 and 1 is one place by name (TypeScript, Rust, Python) and two by name and type (Java) (place_identity_divergence). That the engine holds one place of that name in the compiled net is CONC-007's line 1 over the places of the net."
  signoff "2026-11-13 2d1cd1e89380fb5a ai"
  statement : ∀ {Nm Ty : Type}, PlaceKeyed Nm Ty → Prop :=
    fun M =>
      (∀ p q, M.Same p q → M.name p = M.name q) ∧
      (∀ p q, M.name p = M.name q → M.ty p = M.ty q → M.Same p q) ∧
      ((∀ p q, M.name p = M.name q → M.Same p q) ∨ (∀ p q, M.Same p q → M.ty p = M.ty q))

/- The pinned readable form of CORE-002: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CORE_002 : {Nm Ty : Type} → PlaceKeyed Nm Ty → Prop :=
fun {Nm Ty} M =>
  (∀ (p q : M.P), M.Same p q → M.name p = M.name q) ∧
    (∀ (p q : M.P), M.name p = M.name q → M.ty p = M.ty q → M.Same p q) ∧
      ((∀ (p q : M.P), M.name p = M.name q → M.Same p q) ∨ ∀ (p q : M.P), M.Same p q → M.ty p = M.ty q)
-/
#guard_msgs in #print CORE_002

/-! ### The three lines, named (for the mutants) -/

section Lines

variable {Nm Ty : Type}

/-- Line 1 of CORE-002: the same place has one name. -/
def core002_line1 (M : PlaceKeyed Nm Ty) : Prop :=
  ∀ p q, M.Same p q → M.name p = M.name q

/-- Line 2 of CORE-002: the same name and token type give the same place. -/
def core002_line2 (M : PlaceKeyed Nm Ty) : Prop :=
  ∀ p q, M.name p = M.name q → M.ty p = M.ty q → M.Same p q

/-- Line 3 of CORE-002: the name alone decides, or the same place has one token type. -/
def core002_line3 (M : PlaceKeyed Nm Ty) : Prop :=
  (∀ p q, M.name p = M.name q → M.Same p q) ∨ (∀ p q, M.Same p q → M.ty p = M.ty q)

/-- CORE-002 is its three lines. -/
theorem core002_iff (M : PlaceKeyed Nm Ty) :
    CORE_002 M ↔ core002_line1 M ∧ core002_line2 M ∧ core002_line3 M :=
  Iff.rfl

end Lines

/-! ### The references -/

/-- ✓ Name identity (TypeScript, Rust, Python) satisfies CORE-002: the key is the name, and the
name alone decides (line 3, first branch). -/
@[evidence holds CORE_002]
theorem CORE_002_byName {Nm Ty : Type} : CORE_002 (refPlacesByName (Nm := Nm) (Ty := Ty)) :=
  ⟨fun _ _ h => h, fun _ _ h _ => h, Or.inl fun _ _ h => h⟩

/-- ✓ Name-and-type identity (Java) satisfies CORE-002: the key is the pair, so the same place
has one token type (line 3, second branch). -/
@[evidence holds CORE_002]
theorem CORE_002_byNameType {Nm Ty : Type} :
    CORE_002 (refPlacesByNameType (Nm := Nm) (Ty := Ty)) :=
  ⟨fun _ _ h => (refPlacesByNameType_same.1 h).1,
   fun _ _ h g => refPlacesByNameType_same.2 ⟨h, g⟩,
   Or.inr fun _ _ h => (refPlacesByNameType_same.1 h).2⟩

/-- ✓ All three lines of CORE-002 are exercised by the references. Under name identity two place
objects of one name are one place even with different token types (line 3, first branch), and
places named "A" and "B" are different places (line 1); under name-and-type identity a place is
the same place as an equal place object (line 2) and two places of one name and different token
types are two places (line 3, second branch), so the two references differ. -/
@[evidence nonvacuous CORE_002]
theorem CORE_002_nonvacuous :
    (refPlacesByName (Nm := String) (Ty := Nat)).Same ("A", 0) ("A", 1) ∧
    ¬ (refPlacesByName (Nm := String) (Ty := Nat)).Same ("A", 0) ("B", 0) ∧
    (refPlacesByNameType (Nm := String) (Ty := Nat)).Same ("A", 0) ("A", 0) ∧
    ¬ (refPlacesByNameType (Nm := String) (Ty := Nat)).Same ("A", 0) ("A", 1) := by
  refine ⟨rfl, fun h => ?_, rfl, (place_identity_divergence "A" (by decide)).2⟩
  have : ("A" : String) = "B" := refPlacesByName_same.1 h
  exact absurd this (by decide)

/-! ### Wrong models -/

section Wrong

variable {Nm Ty : Type}

/-- A model in which every place object is the same place: one key for all. -/
def core002_onePlace : PlaceKeyed Nm Ty where
  P := Nm × Ty
  K := Unit
  name := Prod.fst
  ty := Prod.snd
  key := fun _ => ()

/-- Reference identity: each constructed place object (numbered by its construction) is its own
place, whatever its name and token type. -/
def core002_byRef : PlaceKeyed Nm Ty where
  P := Nat × Nm × Ty
  K := Nat × Nm × Ty
  name := fun p => p.2.1
  ty := fun p => p.2.2
  key := id

/-- Identity by token type alone: two place objects of one token type are one place. -/
def core002_byType : PlaceKeyed Nm Ty where
  P := Nm × Ty
  K := Ty
  name := Prod.fst
  ty := Prod.snd
  key := Prod.snd

/-- An identity between the two: the key is the name and the parity of the token type, so the
token type is coarsened (as a key of the name and a type with its type arguments dropped would
be, were the model's token type the full generic type). -/
def core002_coarseType : PlaceKeyed Nm Nat where
  P := Nm × Nat
  K := Nm × Nat
  name := Prod.fst
  ty := Prod.snd
  key := fun p => (p.1, p.2 % 2)

/-- A wrong implementation that mixes two identities: a place object declared on the builder
(`some i`, numbered by construction) is identified by reference, a place reached only through
arcs (`none`) by its name, as a builder place set keyed by reference beside a compiled net keyed
by name does (the behaviour RD-03 in `spec/runtime-defects.md` recorded of TypeScript's builder).
One implementation, two identities. -/
def core002_tsBuilderMix : PlaceKeyed String Nat where
  P := Option Nat × String × Nat
  K := Option Nat × String
  name := fun p => p.2.1
  ty := fun p => p.2.2
  key := fun p => (p.1, p.2.1)

/-- The local part of a composed name `prefix/original` ([MOD-010]): the characters after the
last '/'. -/
def core002_local (s : String) : List Char := (s.toList.reverse.takeWhile (· ≠ '/')).reverse

/-- A key that strips the composition prefix: the same body place instantiated under two
prefixes is one place, against the Note and [MOD-012]'s state isolation. -/
def core002_stripPrefix : PlaceKeyed String Nat where
  P := String × Nat
  K := List Char
  name := Prod.fst
  ty := Prod.snd
  key := fun p => core002_local p.1

end Wrong

/-- ✗ A model in which every place is one place violates CORE-002 (line 1, AC2): the places "A"
and "B" are the same place with different names. -/
@[evidence forbids CORE_002]
theorem CORE_002_forbids_onePlace :
    ¬ CORE_002 (core002_onePlace (Nm := String) (Ty := Nat)) := by
  intro h
  have : ("A" : String) = "B" := h.1 ("A", 0) ("B", 0) rfl
  exact absurd this (by decide)

/-- ✗ Reference identity violates CORE-002 (line 2): the place objects constructed first and
second, both named "A" with token type 0, are two places. -/
@[evidence forbids CORE_002]
theorem CORE_002_forbids_byRef :
    ¬ CORE_002 (core002_byRef (Nm := String) (Ty := Nat)) := by
  intro h
  have : ((0, "A", 0) : Nat × String × Nat) = (1, "A", 0) :=
    h.2.1 (0, "A", 0) (1, "A", 0) rfl rfl
  exact absurd this (by decide)

/-- ✗ A builder place set keyed by reference mixed with name keys violates CORE-002 (line 2): a declared
"A" (object 0) and an arc-only "A", both of token type 0, are two places. -/
@[evidence forbids CORE_002]
theorem CORE_002_forbids_tsBuilderMix : ¬ CORE_002 core002_tsBuilderMix := by
  intro h
  have : ((some 0, "A") : Option Nat × String) = (none, "A") :=
    h.2.1 (some 0, "A", 0) (none, "A", 0) rfl rfl
  exact absurd this (by decide)

/-- ✗ A key that strips the composition prefix violates CORE-002 (line 1, the Note): "a/x" and
"b/x" are one place with two names. -/
@[evidence forbids CORE_002]
theorem CORE_002_forbids_stripPrefix : ¬ CORE_002 core002_stripPrefix := by
  intro h
  have : ("a/x" : String) = "b/x" := h.1 ("a/x", 0) ("b/x", 0)
    (show core002_local "a/x" = core002_local "b/x" by decide)
  exact absurd this (by decide)

/-! ### Mutant: without line 1 -/

/-- Mutant reading: lines 2 and 3 only; places of different names may be one place. -/
def CORE_002_mutant_noLine1 {Nm Ty : Type} (M : PlaceKeyed Nm Ty) : Prop :=
  core002_line2 M ∧ core002_line3 M

/-- Identity by token type alone kills the mutant: the same name and token type give the same
token type, so the same place (line 2), and the same place has one token type (line 3), but the
places "A" and "B" of one token type are one place with two names (line 1). -/
@[evidence mutant CORE_002]
theorem CORE_002_mutant_noLine1_killed :
    CORE_002_mutant_noLine1 (core002_byType (Nm := String) (Ty := Nat)) ∧
      ¬ CORE_002 (core002_byType (Nm := String) (Ty := Nat)) := by
  refine ⟨⟨fun _ _ _ g => g, Or.inr fun _ _ h => h⟩, fun h => ?_⟩
  have : ("A" : String) = "B" := h.1 ("A", 0) ("B", 0) rfl
  exact absurd this (by decide)

/-! ### Mutant: without line 2 (the text before ruling D82) -/

/-- Mutant reading: lines 1 and 3 only. Line 1 is what the text before ruling D82 required beyond
an equivalence (AC1, AC2); with line 3 it still accepts reference identity. -/
def CORE_002_mutant_noLine2 {Nm Ty : Type} (M : PlaceKeyed Nm Ty) : Prop :=
  core002_line1 M ∧ core002_line3 M

/-- Reference identity kills the mutant: each object's key is the object, so the same place has
one name (line 1) and one token type (line 3), but two objects constructed separately with one
name and one token type are two places (line 2). -/
@[evidence mutant CORE_002]
theorem CORE_002_mutant_noLine2_killed :
    CORE_002_mutant_noLine2 (core002_byRef (Nm := String) (Ty := Nat)) ∧
      ¬ CORE_002 (core002_byRef (Nm := String) (Ty := Nat)) :=
  ⟨⟨fun _ _ h => congrArg (fun p : Nat × String × Nat => p.2.1) h,
    Or.inr fun _ _ h => congrArg (fun p : Nat × String × Nat => p.2.2) h⟩,
   CORE_002_forbids_byRef⟩

/-! ### Mutant: without line 3 -/

/-- Mutant reading: lines 1 and 2 only, the bracket without the choice of one of the two
identities; a key between the name and the pair passes. -/
def CORE_002_mutant_noLine3 {Nm Ty : Type} (M : PlaceKeyed Nm Ty) : Prop :=
  core002_line1 M ∧ core002_line2 M

/-- The coarsened key kills the mutant: the key carries the name (line 1) and is a function of
the name and token type (line 2), but the places ("A", 0) and ("A", 1) of one name are two
places, so the name alone does not decide, and ("A", 0) and ("A", 2) are one place with two token
types (line 3). -/
@[evidence mutant CORE_002]
theorem CORE_002_mutant_noLine3_killed :
    CORE_002_mutant_noLine3 (core002_coarseType (Nm := String)) ∧
      ¬ CORE_002 (core002_coarseType (Nm := String)) := by
  refine ⟨⟨fun (p q : String × Nat) (h : (p.1, p.2 % 2) = (q.1, q.2 % 2)) =>
      (Prod.mk.inj h).1,
    fun (p q : String × Nat) (h : p.1 = q.1) (g : p.2 = q.2) =>
      show (p.1, p.2 % 2) = (q.1, q.2 % 2) by rw [h, g]⟩, fun h => ?_⟩
  rcases h.2.2 with h3 | h3
  · have : (("A" : String), 0 % 2) = ("A", 1 % 2) := h3 ("A", 0) ("A", 1) rfl
    exact absurd this (by decide)
  · have : (2 : Nat) = 0 :=
      (h3 ("A", 2) ("A", 0) (show (("A" : String), 2 % 2) = ("A", 0 % 2) from rfl))
    exact absurd this (by decide)

end Libpetri.Spec
