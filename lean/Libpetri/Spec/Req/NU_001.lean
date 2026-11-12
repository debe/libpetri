import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.Req.NU_021

set_option linter.missingDocs true

/-!
# NU-001: Name identity (`spec/12-nu-nets.md`)

NU-001 is a pure-function requirement (kind F) on one implementation's names: the name equality
tells two names apart exactly when their underlying string values differ, the name order that the
[NU-020] tie-break reads is a strict total order, and on names of Basic Multilingual Plane (BMP)
characters that order is code-point order. The statement is a predicate over a bundled *name
implementation* `NameImpl`: the carrier of names, the constructor, the implementation's name
equality and the order. The carrier is bundled because the requirement fixes no carrier type; the
reference carrier is `String` itself (a name is its value), and a `holds` theorem may not pass one
type variable as both the value type and the name type.

The name equality is a field, not Lean's equality on the carrier, so that an implementation whose
names compare by object identity (a Java class without `equals`, a JavaScript object compared with
`===`) is a model, and a wrong one (`NU_001_mutant_identityEq`).

Ruling D31 (a) makes the order a parameter: the block accepts any strict total order that is
code-point order on BMP names, so the Rust order (code point, the reference) and the
Java/TypeScript order (UTF-16 code unit) both satisfy it, although they disagree on names with
supplementary-plane characters (`NU_001_allows_utf16`).

Ruling D96 (a) adds a behaviour block, `NU_001_rename` (kind B, at the end of this file): a firing
reads the names its keys project only through equality and, for the tie-break, the name order.
It is stated over the ν firing model and proved from NU-021's equivariance lemma
(`refNuFire_transfer`) with values paired by equality: renaming every name one-to-one changes no
firing, as long as the tie-break still picks the renamed chosen name.

Consistency: the F block has the conjunct `NU_001 I` of `joint_nu_sketch` in
`Spec/ConsistencyNu.lean`, instantiated by `refNameImpl`, and the B block has the conjunct
`NU_001_rename NF` there, instantiated by `RefNuFire`, the firing relation of NU-020's blocks.
-/

namespace Libpetri.Spec

/-! ## The model: one implementation's names -/

/-- A name implementation: the carrier of names, the constructor from the underlying string
value (`NameId::new`, `NameId.of`, `nameId`), the implementation's name equality (`PartialEq`,
`equals`, `===`) and the name order the [NU-020] tie-break reads. -/
structure NameImpl where
  /-- The carrier of names (`NameId`). -/
  Nm : Type
  /-- The constructor: the name of an underlying string value. -/
  ofValue : String → Nm
  /-- The name equality: `eq x y` reads "the implementation treats `x` and `y` as one name". -/
  eq : Nm → Nm → Prop
  /-- The name order: `lt x y` reads "name `x` precedes name `y`". -/
  lt : Nm → Nm → Prop

/-- **The reference names**: a name is its string value, equal when the strings are equal, and
ordered by Lean's `String` order, the lexicographic order on code points. This is Rust's order
(the derived `Ord` on `Arc<str>` compares UTF-8 bytes, which order as code points do), and so
Python's. -/
def refNameImpl : NameImpl where
  Nm := String
  ofValue := id
  eq := (· = ·)
  lt := (· < ·)

/- The reference names are the witness model of NU-001's `holds` theorem. -/
#spec_witness refNameImpl

/-! ## NU-001: Name Identity -/

requirement NU_001
  id "NU-001"
  title "Name Identity"
  kind F
  scope "the names, the name equality and the name order of each implementation"
  source verbatim "spec/12-nu-nets.md"
  quote "The name constructor *shall* return equal names for equal underlying values and different names for different underlying values."
        "Each implementation *shall* order names by one fixed strict total order, the name order: if one name precedes another, the other does not precede it; if a first name precedes a second and the second precedes a third, the first precedes the third; and of two different names, one precedes the other."
        "Of two names whose underlying values hold only Basic Multilingual Plane characters, one *shall* precede the other exactly when its value precedes the other's in the lexicographic order of code points."
  reading "For all values a and b, the implementation's name equality holds between the name constructed from a and the name constructed from b exactly when a = b."
          "For all values a and b, if the name of a precedes the name of b, then the name of b does not precede the name of a (so no name precedes itself)."
          "For all values a, b and c, if the name of a precedes the name of b and the name of b precedes the name of c, then the name of a precedes the name of c."
          "For all different values a and b, the name of a precedes the name of b or the name of b precedes the name of a."
          "For all values a and b whose characters all lie below U+10000, the name of a precedes the name of b exactly when a precedes b in the lexicographic order of code points."
  assumes "The model is one implementation's NameImpl: the carrier of names, the constructor from the underlying value, the name equality and the name order. A name is what the constructor returns; names minted by the executor (NU-010, NU-011) are constructed from their rendered string, so they are names in this sense. The underlying values are strings of Unicode scalar values (Lean's String), which covers every value Rust and Python accept; Java's rejection of a null value and JavaScript or Java strings holding an unpaired surrogate are outside the model."
          "The constructor is a function of the value, so two constructions of one value give one term of the carrier; the name equality is a field, so an implementation whose names compare by object identity, where two constructions of one value are not equal, is a model and breaks the first line (NU_001_mutant_identityEq). Rust derives PartialEq on the string, Java's NameId is a record and TypeScript's NameId is a branded string compared by value: each is the reference equality."
          "The fourth line ranges over different underlying values. By the first line these are exactly the pairs of different names, so it is the quote's 'of two different names'; stating it over values keeps it independent of the first line."
          "'Stable' and 'consistent across a single implementation' (AC2) are read as: the name order is one fixed relation of the implementation, a field of NameImpl, so it cannot differ between two comparisons. Whether it is the same relation in two processes of one implementation is not modelled; every runtime fixes it in code (Rust's derived Ord, Java's String.compareTo, TypeScript's string comparison)."
          "Ruling D31 (a): outside the BMP the order is a parameter. The reference is code-point order (refNameImpl, the order of Rust and of Python, which runs on the Rust runtime); the UTF-16 code-unit order of Java and TypeScript satisfies the block too, agrees with code-point order on BMP names (NU_001_utf16_bmp_agree) and disagrees with it on U+FFFF against U+10000 (NU_001_allows_utf16). The fifth line is what NU-020's 'all languages fire identically' and its note 'byte-identical across implementations for BMP names' rest on for the name half of the tie-break; it rejects a reversed comparator (NU_001_mutant_reversed) and a shortlex order (NU_001_forbids_shortlex). That the oldest-token half of the tie-break agrees across languages is NU-020's and NU-022's, not a line here."
          "Ruling D96 (a): the behaviour sentence of NU-001 (a firing reads the names its keys project only through name equality and, for the tie-break of NU-020, the name order) and its event-driven form are the kind B block NU_001_rename in this file, over the ν firing model; they are not lines of this F block. The sentences 'A name (NameId) is an opaque correlation identity, constructed from an underlying string value.' and 'The name order exists solely for that tie-break and carries no domain meaning.' are design text, traced by NU_001_rename."
          "'Identity is a projection of the token payload, not a field on the token' and 'the token model is unchanged' are design text: a match key reads the token value (NU-020), and no model in this development adds a name field to a token. AC3 (adding ν-matching does not change the token type or the on-the-wire shape of token-bearing events) and the test derivation's third check are API and wire shape (kind Q). No test in any language yet runs a net with and without the ν-net APIs and compares its token events, so AC3 has no traced Q evidence; it is recorded here as open, to be closed by a kind Q test beside the EVT-011 and EVT-012 tests."
          "AC1 (two names constructed from the same underlying value are equal; from different values, unequal) is the first line. AC2 (a stable total order on names, consistent across a single implementation) is the second, third and fourth lines: a strict total order on names, with stability read as above. AC4 (a one-to-one renaming that keeps the chosen name the chosen name changes no firing) is the renaming line NU_001_rename's."
          "The test derivation's first two checks (NameId(\"a\") constructed twice is equal; NameId(\"a\") precedes NameId(\"b\")) follow from the statement for every implementation (NU_001_testDerivation) and are NU_001_nonvacuous on the reference. At runtime the Rust unit tests equality_by_value and total_order_is_lexicographic in rust/libpetri-core/src/name.rs run them."
          "Implementations also hash names (Rust's derived Hash, Java's record hashCode, a JavaScript Map key); a hash consistent with the name equality adds no observation, and is not modelled."
  signoff "pending"
  statement : NameImpl → Prop :=
    fun I =>
      (∀ a b : String, I.eq (I.ofValue a) (I.ofValue b) ↔ a = b) ∧
      (∀ a b : String, I.lt (I.ofValue a) (I.ofValue b) → ¬ I.lt (I.ofValue b) (I.ofValue a)) ∧
      (∀ a b c : String, I.lt (I.ofValue a) (I.ofValue b) → I.lt (I.ofValue b) (I.ofValue c) →
        I.lt (I.ofValue a) (I.ofValue c)) ∧
      (∀ a b : String, a ≠ b → I.lt (I.ofValue a) (I.ofValue b) ∨ I.lt (I.ofValue b) (I.ofValue a)) ∧
      (∀ a b : String, (∀ c ∈ a.toList, c.toNat < 0x10000) → (∀ c ∈ b.toList, c.toNat < 0x10000) →
        (I.lt (I.ofValue a) (I.ofValue b) ↔ a < b))

/- The pinned readable form of NU-001: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.NU_001 : NameImpl → Prop :=
fun I =>
  (∀ (a b : String), I.eq (I.ofValue a) (I.ofValue b) ↔ a = b) ∧
    (∀ (a b : String), I.lt (I.ofValue a) (I.ofValue b) → ¬I.lt (I.ofValue b) (I.ofValue a)) ∧
      (∀ (a b c : String),
          I.lt (I.ofValue a) (I.ofValue b) → I.lt (I.ofValue b) (I.ofValue c) → I.lt (I.ofValue a) (I.ofValue c)) ∧
        (∀ (a b : String), a ≠ b → I.lt (I.ofValue a) (I.ofValue b) ∨ I.lt (I.ofValue b) (I.ofValue a)) ∧
          ∀ (a b : String),
            (∀ c ∈ a.toList, c.toNat < 65536) →
              (∀ c ∈ b.toList, c.toNat < 65536) → (I.lt (I.ofValue a) (I.ofValue b) ↔ a < b)
-/
#guard_msgs in #print NU_001

/-! ## The lines one at a time, for the mutants -/

/-- Line 1 of NU-001: the name equality holds exactly between names of equal values. -/
def NU_001_line1 (I : NameImpl) : Prop := ∀ a b : String, I.eq (I.ofValue a) (I.ofValue b) ↔ a = b

/-- Line 2 of NU-001: the name order is asymmetric. -/
def NU_001_line2 (I : NameImpl) : Prop :=
  ∀ a b : String, I.lt (I.ofValue a) (I.ofValue b) → ¬ I.lt (I.ofValue b) (I.ofValue a)

/-- Line 3 of NU-001: the name order is transitive. -/
def NU_001_line3 (I : NameImpl) : Prop :=
  ∀ a b c : String, I.lt (I.ofValue a) (I.ofValue b) → I.lt (I.ofValue b) (I.ofValue c) → I.lt (I.ofValue a) (I.ofValue c)

/-- Line 4 of NU-001: of the names of two different values, one precedes the other. -/
def NU_001_line4 (I : NameImpl) : Prop :=
  ∀ a b : String, a ≠ b → I.lt (I.ofValue a) (I.ofValue b) ∨ I.lt (I.ofValue b) (I.ofValue a)

/-- Line 5 of NU-001: on names of BMP characters the name order is code-point order. -/
def NU_001_line5 (I : NameImpl) : Prop :=
  ∀ a b : String, (∀ c ∈ a.toList, c.toNat < 0x10000) → (∀ c ∈ b.toList, c.toNat < 0x10000) →
    (I.lt (I.ofValue a) (I.ofValue b) ↔ a < b)

/-- NU-001 is the conjunction of its five lines. -/
theorem NU_001_iff_lines (I : NameImpl) :
    NU_001 I ↔ NU_001_line1 I ∧ NU_001_line2 I ∧ NU_001_line3 I ∧ NU_001_line4 I ∧ NU_001_line5 I :=
  Iff.rfl

/-- Every line of NU-001 except line `k`: what a mutant that breaks line `k` alone keeps. -/
def NU_001_allBut (k : Nat) (I : NameImpl) : Prop :=
  (k ≠ 1 → NU_001_line1 I) ∧ (k ≠ 2 → NU_001_line2 I) ∧ (k ≠ 3 → NU_001_line3 I) ∧
    (k ≠ 4 → NU_001_line4 I) ∧ (k ≠ 5 → NU_001_line5 I)

/-! ## String order facts -/

/-- Lean's `String` order is total on distinct strings. -/
theorem nu001_string_lt_or_gt {a b : String} (h : a ≠ b) : a < b ∨ b < a := by
  by_cases h1 : a < b
  · exact Or.inl h1
  · by_cases h2 : b < a
    · exact Or.inr h2
    · exact absurd (String.le_antisymm (String.not_lt.1 h2) (String.not_lt.1 h1)) h

/-- Lines 2 to 5 hold for names that are their values ordered by Lean's `String` order, whatever
the name equality: they are facts about the order. -/
theorem nu001_string_order_lines (e : String → String → Prop) :
    NU_001_line2 ⟨String, id, e, (· < ·)⟩ ∧ NU_001_line3 ⟨String, id, e, (· < ·)⟩ ∧
      NU_001_line4 ⟨String, id, e, (· < ·)⟩ ∧ NU_001_line5 ⟨String, id, e, (· < ·)⟩ :=
  ⟨fun _ _ h => String.lt_asymm h, fun _ _ _ h h' => String.lt_trans h h',
   fun _ _ h => nu001_string_lt_or_gt h, fun _ _ _ _ => Iff.rfl⟩

/-! ## The reference satisfies NU-001 -/

/-- The reference satisfies NU-001: the constructor is the identity, the name equality is string
equality, and Lean's `String` order is a strict total order, code-point order everywhere. -/
@[evidence holds NU_001]
theorem NU_001_reference : NU_001 refNameImpl :=
  ⟨fun _ _ => Iff.rfl, nu001_string_order_lines (· = ·)⟩

/-- The test derivation's first two checks follow from NU-001 for every implementation: `NameId("a")`
is equal to itself, `NameId("a")` and `NameId("b")` are different names, and `NameId("a")` precedes
`NameId("b")` (line 5, since both are ASCII). -/
theorem NU_001_testDerivation (I : NameImpl) (h : NU_001 I) :
    I.eq (I.ofValue "a") (I.ofValue "a") ∧ ¬ I.eq (I.ofValue "a") (I.ofValue "b") ∧
      I.lt (I.ofValue "a") (I.ofValue "b") := by
  refine ⟨(h.1 "a" "a").2 rfl, fun e => absurd ((h.1 "a" "b").1 e) (by decide), ?_⟩
  exact (h.2.2.2.2 "a" "b" (by decide) (by decide)).2 (by decide)

/-- The test derivation on the reference: `NameId("a")` constructed twice gives one name,
`NameId("a")` and `NameId("b")` are different names, and `NameId("a")` precedes `NameId("b")`. -/
@[evidence nonvacuous NU_001]
theorem NU_001_nonvacuous :
    refNameImpl.eq (refNameImpl.ofValue "a") (refNameImpl.ofValue "a") ∧
      ¬ refNameImpl.eq (refNameImpl.ofValue "a") (refNameImpl.ofValue "b") ∧
      refNameImpl.lt (refNameImpl.ofValue "a") (refNameImpl.ofValue "b") :=
  NU_001_testDerivation refNameImpl NU_001_reference

/-! ## Ruling D31 (a): the UTF-16 order of Java and TypeScript satisfies NU-001 too -/

/-- The UTF-16 code units of one character: the code point itself in the Basic Multilingual
Plane, a surrogate pair above it. -/
def nu001Utf16Units (c : Char) : List Nat :=
  if c.val.toNat < 0x10000 then [c.val.toNat]
  else [0xD800 + (c.val.toNat - 0x10000) / 0x400, 0xDC00 + (c.val.toNat - 0x10000) % 0x400]

/-- The UTF-16 code units of a string, as Java's `String` and a JavaScript string hold it. -/
def nu001Utf16 (s : String) : List Nat := s.toList.flatMap nu001Utf16Units

/-- **The Java/TypeScript names**: a name is its string value, equal when the strings are equal,
and ordered by the lexicographic order of UTF-16 code units (Java's `String.compareTo`,
JavaScript's `<` on strings). -/
def utf16NameImpl : NameImpl where
  Nm := String
  ofValue := id
  eq := (· = ·)
  lt a b := nu001Utf16 a < nu001Utf16 b

/-- The UTF-16 units of a character decide the character, and where they end: a code point in
the Basic Multilingual Plane is never a surrogate, so the first unit tells one unit from a pair. -/
theorem nu001Utf16Units_append_inj {c c' : Char} {r r' : List Nat}
    (h : nu001Utf16Units c ++ r = nu001Utf16Units c' ++ r') : c = c' ∧ r = r' := by
  have hv : c.val.toNat.isValidChar := c.valid
  have hv' : c'.val.toNat.isValidChar := c'.valid
  simp only [Nat.isValidChar] at hv hv'
  have ext : c.val.toNat = c'.val.toNat → c = c' := fun e =>
    Char.ext (UInt32.toNat_inj.mp e)
  unfold nu001Utf16Units at h
  split at h <;> split at h <;>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
  · exact ⟨ext h.1, h.2⟩
  · omega
  · omega
  · exact ⟨ext (by omega), h.2.2⟩

/-- A character has at least one UTF-16 unit. -/
theorem nu001Utf16Units_ne_nil (c : Char) : nu001Utf16Units c ≠ [] := by
  unfold nu001Utf16Units
  split <;> simp

/-- The UTF-16 encoding of a character list is injective. -/
theorem nu001Utf16_flatMap_inj :
    ∀ {l l' : List Char}, l.flatMap nu001Utf16Units = l'.flatMap nu001Utf16Units → l = l'
  | [], [], _ => rfl
  | [], c :: _, h => by
      simp only [List.flatMap_nil, List.flatMap_cons] at h
      exact absurd (List.append_eq_nil_iff.1 h.symm).1 (nu001Utf16Units_ne_nil c)
  | c :: _, [], h => by
      simp only [List.flatMap_nil, List.flatMap_cons] at h
      exact absurd (List.append_eq_nil_iff.1 h).1 (nu001Utf16Units_ne_nil c)
  | c :: l, c' :: l', h => by
      simp only [List.flatMap_cons] at h
      obtain ⟨hc, hr⟩ := nu001Utf16Units_append_inj h
      rw [hc, nu001Utf16_flatMap_inj hr]

/-- The UTF-16 encoding of a string is injective. -/
theorem nu001Utf16_inj {a b : String} (h : nu001Utf16 a = nu001Utf16 b) : a = b :=
  String.ext (nu001Utf16_flatMap_inj h)

/-- On a list of BMP characters the UTF-16 units are the code points, one unit per character. -/
theorem nu001Utf16_bmp : ∀ (l : List Char), (∀ c ∈ l, c.toNat < 0x10000) →
    l.flatMap nu001Utf16Units = l.map Char.toNat
  | [], _ => rfl
  | c :: l, h => by
      have hc : c.val.toNat < 0x10000 := h c (List.mem_cons_self ..)
      have hl := nu001Utf16_bmp l (fun d hd => h d (List.mem_cons_of_mem _ hd))
      simp only [List.flatMap_cons, List.map_cons, hl, nu001Utf16Units, if_pos hc]
      rfl

/-- Comparing the code points of two character lists lexicographically is comparing the
characters: `Char.toNat` is injective and strictly monotone. -/
theorem nu001_lex_toNat : ∀ (l l' : List Char),
    List.Lex (· < ·) (l.map Char.toNat) (l'.map Char.toNat) ↔ List.Lex (· < ·) l l'
  | [], [] => by simp
  | [], _ :: _ => by simp
  | _ :: _, [] => by simp [List.not_lex_nil]
  | c :: l, c' :: l' => by
      simp only [List.map_cons, List.cons_lex_cons_iff, nu001_lex_toNat l l']
      have e : c.toNat = c'.toNat ↔ c = c' :=
        ⟨fun h => Char.ext (UInt32.toNat_inj.mp h), fun h => h ▸ rfl⟩
      have r : c.toNat < c'.toNat ↔ c < c' := by
        show c.val.toNat < c'.val.toNat ↔ c.val < c'.val
        exact UInt32.lt_iff_toNat_lt.symm
      rw [e, r]

/-- On BMP names the UTF-16 code-unit order of Java and TypeScript is code-point order: the
fifth line holds for `utf16NameImpl`. -/
theorem NU_001_utf16_bmp_agree : NU_001_line5 utf16NameImpl := by
  intro a b ha hb
  show nu001Utf16 a < nu001Utf16 b ↔ a.toList < b.toList
  unfold nu001Utf16
  rw [nu001Utf16_bmp _ ha, nu001Utf16_bmp _ hb]
  exact nu001_lex_toNat _ _

/-- Ruling D31 (a): NU-001 does not fix the name order outside the BMP. The Java/TypeScript
UTF-16 code-unit order satisfies NU-001, as the reference code-point order does, and the two
disagree on U+FFFF against U+10000: by code point U+FFFF precedes U+10000, by UTF-16 code unit
U+10000 (the surrogate pair D800 DC00) precedes U+FFFF. -/
@[evidence allows NU_001]
theorem NU_001_allows_utf16 :
    NU_001 utf16NameImpl ∧ refNameImpl.lt "￿" "𐀀" ∧ utf16NameImpl.lt "𐀀" "￿" := by
  refine ⟨⟨fun _ _ => Iff.rfl, fun _ _ h => List.lt_asymm h,
    fun _ _ _ h h' => List.lt_trans h h', fun a b h => ?_, NU_001_utf16_bmp_agree⟩, ?_, ?_⟩
  · have hne : nu001Utf16 a ≠ nu001Utf16 b := fun e => h (nu001Utf16_inj e)
    by_cases h1 : nu001Utf16 a < nu001Utf16 b
    · exact Or.inl h1
    · by_cases h2 : nu001Utf16 b < nu001Utf16 a
      · exact Or.inr h2
      · exact absurd (List.le_antisymm (List.not_lt.1 h2) (List.not_lt.1 h1)) hne
  · show ("￿" : String) < "𐀀"
    decide
  · show nu001Utf16 "𐀀" < nu001Utf16 "￿"
    decide

/-! ## Wrong name implementations NU-001 rejects -/

/-- Names compared by object identity: a Java `final class NameId` without `equals`, or a
JavaScript `{ value }` object compared with `===`. Two constructions of one value are two objects,
so the implementation never treats them as one name. The order is Lean's `String` order. -/
def nu001IdentityEq : NameImpl where
  Nm := String
  ofValue := id
  eq _ _ := False
  lt := (· < ·)

/-- ✗ Line 1 is load-bearing (equal names for equal values): names compared by object identity
keep every other line (the order is still code-point order) and are rejected, since two
constructions of `"a"` are not one name, and a fork's siblings would never join. -/
@[evidence mutant NU_001]
theorem NU_001_mutant_identityEq :
    NU_001_allBut 1 nu001IdentityEq ∧ ¬ NU_001 nu001IdentityEq := by
  have hl := nu001_string_order_lines (fun _ _ => False)
  exact ⟨⟨fun h => absurd rfl h, fun _ => hl.1, fun _ => hl.2.1, fun _ => hl.2.2.1,
    fun _ => hl.2.2.2⟩, fun h => (h.1 "a" "a").2 rfl⟩

/-- A case-insensitive name equality (`equalsIgnoreCase`, or a `Map` keyed by the lower-case
value) beside a case-sensitive order: `"A"` and `"a"` are one name. -/
def nu001IgnoreCase : NameImpl where
  Nm := String
  ofValue := id
  eq x y := String.ofList (x.toList.map Char.toLower) = String.ofList (y.toList.map Char.toLower)
  lt := (· < ·)

/-- ✗ Line 1 is load-bearing (different names for different values): a case-insensitive name
equality keeps every other line and is rejected, since `"A"` and `"a"` are different values with
one name. -/
@[evidence mutant NU_001]
theorem NU_001_mutant_ignoreCase :
    NU_001_allBut 1 nu001IgnoreCase ∧ ¬ NU_001 nu001IgnoreCase := by
  have hl := nu001_string_order_lines nu001IgnoreCase.eq
  refine ⟨⟨fun h => absurd rfl h, fun _ => hl.1, fun _ => hl.2.1, fun _ => hl.2.2.1,
    fun _ => hl.2.2.2⟩, fun h => ?_⟩
  have hfold : nu001IgnoreCase.eq (nu001IgnoreCase.ofValue "A") (nu001IgnoreCase.ofValue "a") := by
    show String.ofList ("A".toList.map Char.toLower) = String.ofList ("a".toList.map Char.toLower)
    exact congrArg String.ofList (by decide)
  exact absurd ((h.1 "A" "a").1 hfold) (by decide)

/-- A name whose underlying value holds only Basic Multilingual Plane characters. Line 5 fixes
the order on these names, so a mutant of lines 2 to 4 that keeps line 5 must differ from the
reference only on names outside the BMP. -/
def nu001Bmp (s : String) : Prop := ∀ c ∈ s.toList, c.toNat < 0x10000

instance (s : String) : Decidable (nu001Bmp s) := by unfold nu001Bmp; infer_instance

/-- A non-strict order outside the BMP: the comparator answers "precedes" also for a name and
itself when the name holds a supplementary-plane character (an `≤` left in the branch that
handles surrogate pairs), and is code-point order otherwise. -/
def nu001NonStrict : NameImpl where
  Nm := String
  ofValue := id
  eq := (· = ·)
  lt a b := a < b ∨ (a = b ∧ ¬ nu001Bmp a)

/-- ✗ Line 2 is load-bearing: the non-strict order keeps every other line (it is transitive,
total on different names and code-point order on BMP names) and is rejected, since the name
`"𐀀"` (U+10000) precedes itself. -/
@[evidence mutant NU_001]
theorem NU_001_mutant_nonStrict :
    NU_001_allBut 2 nu001NonStrict ∧ ¬ NU_001 nu001NonStrict := by
  refine ⟨⟨fun _ _ _ => Iff.rfl, fun h => absurd rfl h, fun _ a b c h h' => ?_,
    fun _ a b hne => (nu001_string_lt_or_gt hne).imp Or.inl Or.inl, fun _ a b ha _ => ?_⟩,
    fun h => ?_⟩
  · rcases h with h | ⟨rfl, hn⟩ <;> rcases h' with h' | ⟨rfl, hn'⟩
    · exact Or.inl (String.lt_trans h h')
    · exact Or.inl h
    · exact Or.inl h'
    · exact Or.inr ⟨rfl, hn⟩
  · exact ⟨fun h => h.elim id (fun h' => absurd ha h'.2), Or.inl⟩
  · have hx : nu001NonStrict.lt (nu001NonStrict.ofValue "𐀀") (nu001NonStrict.ofValue "𐀀") :=
      Or.inr ⟨rfl, by decide⟩
    exact h.2.1 "𐀀" "𐀀" hx hx

/-- The three names of a cyclic comparator, all outside the BMP (U+10000, U+10001, U+10002). -/
def nu001Cyc3 (s : String) : Prop := s = "𐀀" ∨ s = "𐀁" ∨ s = "𐀂"

instance (s : String) : Decidable (nu001Cyc3 s) := by unfold nu001Cyc3; infer_instance

/-- A cyclic comparator: on three supplementary-plane names `"𐀀"`, `"𐀁"` and `"𐀂"` it answers
rock, paper, scissors (each precedes the next, and the last precedes the first); on every other
pair it is Lean's `String` order. Such a comparator has no least name among the three. -/
def nu001Cyclic : NameImpl where
  Nm := String
  ofValue := id
  eq := (· = ·)
  lt a b := if nu001Cyc3 a ∧ nu001Cyc3 b then
      (a = "𐀀" ∧ b = "𐀁") ∨ (a = "𐀁" ∧ b = "𐀂") ∨ (a = "𐀂" ∧ b = "𐀀")
    else a < b

/-- ✗ Line 3 is load-bearing: the cyclic comparator keeps every other line (it is asymmetric, of
two different names one precedes the other, and it is code-point order on BMP names) and is
rejected, since `"𐀀"` precedes `"𐀁"`, `"𐀁"` precedes `"𐀂"` and `"𐀀"` does not precede
`"𐀂"`. -/
@[evidence mutant NU_001]
theorem NU_001_mutant_cyclic :
    NU_001_allBut 3 nu001Cyclic ∧ ¬ NU_001 nu001Cyclic := by
  refine ⟨⟨fun _ _ _ => Iff.rfl, fun _ a b h => ?_, fun h => absurd rfl h, fun _ a b hne => ?_,
    fun _ a b ha _ => ?_⟩, fun h => ?_⟩
  · show ¬ (if nu001Cyc3 b ∧ nu001Cyc3 a then
      (b = "𐀀" ∧ a = "𐀁") ∨ (b = "𐀁" ∧ a = "𐀂") ∨ (b = "𐀂" ∧ a = "𐀀") else b < a)
    change (if nu001Cyc3 a ∧ nu001Cyc3 b then
      (a = "𐀀" ∧ b = "𐀁") ∨ (a = "𐀁" ∧ b = "𐀂") ∨ (a = "𐀂" ∧ b = "𐀀") else a < b) at h
    by_cases hc : nu001Cyc3 a ∧ nu001Cyc3 b
    · have hc' : nu001Cyc3 b ∧ nu001Cyc3 a := ⟨hc.2, hc.1⟩
      rw [if_pos hc] at h
      rw [if_pos hc']
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    · have hc' : ¬ (nu001Cyc3 b ∧ nu001Cyc3 a) := fun h' => hc ⟨h'.2, h'.1⟩
      rw [if_neg hc] at h
      rw [if_neg hc']
      exact String.lt_asymm h
  · show (if nu001Cyc3 a ∧ nu001Cyc3 b then
        (a = "𐀀" ∧ b = "𐀁") ∨ (a = "𐀁" ∧ b = "𐀂") ∨ (a = "𐀂" ∧ b = "𐀀") else a < b) ∨
      (if nu001Cyc3 b ∧ nu001Cyc3 a then
        (b = "𐀀" ∧ a = "𐀁") ∨ (b = "𐀁" ∧ a = "𐀂") ∨ (b = "𐀂" ∧ a = "𐀀") else b < a)
    by_cases hc : nu001Cyc3 a ∧ nu001Cyc3 b
    · have hc' : nu001Cyc3 b ∧ nu001Cyc3 a := ⟨hc.2, hc.1⟩
      rw [if_pos hc, if_pos hc']
      obtain ⟨ha | ha | ha, hb | hb | hb⟩ := hc <;> subst ha <;> subst hb <;>
        first | exact absurd rfl hne | decide
    · have hc' : ¬ (nu001Cyc3 b ∧ nu001Cyc3 a) := fun h' => hc ⟨h'.2, h'.1⟩
      rw [if_neg hc, if_neg hc']
      exact nu001_string_lt_or_gt hne
  · have hc : ¬ (nu001Cyc3 a ∧ nu001Cyc3 b) := fun ⟨hc, _⟩ => by
      rcases hc with rfl | rfl | rfl <;> exact absurd ha (by decide)
    show (if nu001Cyc3 a ∧ nu001Cyc3 b then
        (a = "𐀀" ∧ b = "𐀁") ∨ (a = "𐀁" ∧ b = "𐀂") ∨ (a = "𐀂" ∧ b = "𐀀") else a < b) ↔ a < b
    rw [if_neg hc]
  · have hab : nu001Cyclic.lt (nu001Cyclic.ofValue "𐀀") (nu001Cyclic.ofValue "𐀁") := by
      dsimp only [nu001Cyclic]; decide
    have hbc : nu001Cyclic.lt (nu001Cyclic.ofValue "𐀁") (nu001Cyclic.ofValue "𐀂") := by
      dsimp only [nu001Cyclic]; decide
    have hac : ¬ nu001Cyclic.lt (nu001Cyclic.ofValue "𐀀") (nu001Cyclic.ofValue "𐀂") := by
      dsimp only [nu001Cyclic]; decide
    exact hac (h.2.2.1 "𐀀" "𐀁" "𐀂" hab hbc)

/-- A comparator that gives up outside the BMP: BMP names by code point, every other name after
them, and "neither precedes" for two names outside the BMP (a comparator that returns 0 for the
names it does not handle). -/
def nu001AstralTie : NameImpl where
  Nm := String
  ofValue := id
  eq := (· = ·)
  lt a b := (nu001Bmp a ∧ nu001Bmp b ∧ a < b) ∨ (nu001Bmp a ∧ ¬ nu001Bmp b)

/-- ✗ Line 4 is load-bearing: the comparator that gives up outside the BMP keeps every other line
(it is asymmetric, transitive and code-point order on BMP names) and is rejected, since neither of
the different names `"𐀀"` and `"𐀁"` precedes the other, so the tie-break between them is
undefined. -/
@[evidence mutant NU_001]
theorem NU_001_mutant_astralTie :
    NU_001_allBut 4 nu001AstralTie ∧ ¬ NU_001 nu001AstralTie := by
  refine ⟨⟨fun _ _ _ => Iff.rfl, fun _ a b h h' => ?_, fun _ a b c h h' => ?_,
    fun h => absurd rfl h, fun _ a b ha hb => ?_⟩, fun h => ?_⟩
  · rcases h with ⟨_, _, h⟩ | ⟨ha, hb⟩ <;> rcases h' with ⟨_, _, h'⟩ | ⟨hb', ha'⟩
    · exact String.lt_asymm h h'
    · exact ha' (by assumption)
    · exact hb (by assumption)
    · exact ha' ha
  · rcases h with ⟨ha, hb, h⟩ | ⟨ha, hb⟩ <;> rcases h' with ⟨hb', hc, h'⟩ | ⟨hb', hc⟩
    · exact Or.inl ⟨ha, hc, String.lt_trans h h'⟩
    · exact Or.inr ⟨ha, hc⟩
    · exact absurd hb' hb
    · exact absurd hb' hb
  · exact ⟨fun h => h.elim (fun h' => h'.2.2) (fun h' => absurd hb h'.2),
      fun h => Or.inl ⟨ha, hb, h⟩⟩
  · rcases h.2.2.2.1 "𐀀" "𐀁" (by decide) with (⟨ha, _⟩ | ⟨ha, _⟩) | (⟨ha, _⟩ | ⟨ha, _⟩) <;>
      exact absurd ha (by decide)

/-- A reversed comparator: the arguments of the comparison swapped (`other.compareTo(this)`), so
`"b"` precedes `"a"`. It is still a strict total order. -/
def nu001Reversed : NameImpl where
  Nm := String
  ofValue := id
  eq := (· = ·)
  lt a b := b < a

/-- ✗ Line 5 is load-bearing: a reversed comparator keeps every other line (it is a strict total
order) and is rejected, since on the ASCII names `"a"` and `"b"` it reverses code-point order, so
the [NU-020] tie-break would pick the other name in every language that orders correctly. -/
@[evidence mutant NU_001]
theorem NU_001_mutant_reversed :
    NU_001_allBut 5 nu001Reversed ∧ ¬ NU_001 nu001Reversed := by
  refine ⟨⟨fun _ => fun _ _ => Iff.rfl, fun _ _ _ h => String.lt_asymm h,
    fun _ _ _ _ h h' => String.lt_trans h' h, fun _ a b hne => ?_, fun h => absurd rfl h⟩,
    fun h => ?_⟩
  · rcases nu001_string_lt_or_gt hne with h | h
    · exact Or.inr h
    · exact Or.inl h
  · have hab : ("a" : String) < "b" := by decide
    have hba := (h.2.2.2.2 "a" "b" (by decide) (by decide)).2 hab
    exact absurd hba (by show ¬ ("b" : String) < "a"; decide)

/-- A shortlex order: shorter names first, names of one length by code point. It is what one
writes so that the minted name `t#s:9` sorts before `t#s:10`. -/
def nu001Shortlex : NameImpl where
  Nm := String
  ofValue := id
  eq := (· = ·)
  lt a b := a.length < b.length ∨ (a.length = b.length ∧ a < b)

/-- ✗ A shortlex order is rejected by line 5: on the ASCII names `"aa"` and `"b"` it puts `"b"`
first, while code-point order puts `"aa"` first. -/
@[evidence forbids NU_001]
theorem NU_001_forbids_shortlex : ¬ NU_001 nu001Shortlex := by
  intro h
  have hlt : ("aa" : String) < "b" := by decide
  have h' := (h.2.2.2.2 "aa" "b" (by decide) (by decide)).2 hlt
  exact absurd h' (by
    show ¬ (("aa" : String).length < ("b" : String).length ∨
      (("aa" : String).length = ("b" : String).length ∧ ("aa" : String) < "b"))
    decide)

/-! ## The behaviour line (ruling D96 (a)): names are read only through equality and the tie-break -/

open Libpetri Libpetri.Reference

section Rename

variable {N V Nm : Type}

/-- A key projection with every name it gives renamed by `σ`. -/
def nuRenameKey (σ : Nm → Nm) (f : KeyFn V Nm) : KeyFn V Nm := fun v => (f v).map σ

/-- A match specification with every key and relay projection renamed by `σ`: the same keyed
places and relay targets, in the same order. -/
def nuRenameMs (σ : Nm → Nm) (ms : MatchSpec N (KeyFn V Nm)) : MatchSpec N (KeyFn V Nm) :=
  { keys := ms.keys.map fun k => (k.1, nuRenameKey σ k.2),
    relays := ms.relays.map fun k => (k.1, nuRenameKey σ k.2) }

/-- **The transition with its names renamed**: `t` with every name its keys and relay targets
project renamed by `σ`. Its arcs, output spec and every token value stay as they are. -/
def nuRenameNames (σ : Nm → Nm) (t : NuTrans N (KeyFn V Nm)) : NuTrans N (KeyFn V Nm) :=
  { base := t.base, mspec := t.mspec.map (nuRenameMs σ) }

end Rename

/-! ## NU-001: Name Identity (the renaming line) -/

requirement NU_001_rename
  id "NU-001"
  title "Name Identity (renaming)"
  kind B
  scope "every executor; one firing of a transition with a match specification"
  source verbatim "spec/12-nu-nets.md"
  quote "Whether a matched transition is enabled, and which tokens its firing consumes, *shall* depend on the names its keys project only through name **equality** and, for the tie-break of [NU-020], the name order."
        "*When* a matched transition fires with a chosen name, and a one-to-one renaming of names makes the renamed chosen name the chosen name ([NU-020], [NU-022]) of the same transition with every name its keys and relay targets project renamed, at the same marking, that renamed transition *shall* fire from that marking with the renamed chosen name, for the same emission, delivering the same tokens and leaving the same marking."
  reading "For every transition t with match specification ms, every injective renaming σ of names, and every firing of t in R from M with chosen name n, delivery δ and emission e, leaving M': if σ n is the chosen name of nuRenameNames σ t at M (t with every name its keys and relay targets give renamed by σ; Selected over the selection input of t at M with every name renamed by σ, which is the renamed transition's own selection input), then R has a firing of nuRenameNames σ t from M with chosen name σ n, delivery δ and emission e, leaving M'."
  assumes "The model is a ν firing relation R over queue markings of stamped tokens (NuFireRel), as for NU_020_enable and NU_021: R t M c δ e M' says that t fires from M with chosen name c, delivers δ, the action emits e, and the firing leaves M'. A renaming of names is a function σ from names to names applied to what every key and relay target projects (nuRenameNames); the places, arcs, output spec, token values, markings and emissions are untouched, so 'the same transition with every name its keys and relay targets project renamed' is nuRenameNames σ t and token payloads are not renamed. It is injective because a renaming that merges two names changes name equality, which the sentence lets a firing read: a matcher whose name index folds names that differ, such as a case-folding NameId, is rejected (NU_001_rename_forbids_folded). 'Is enabled' and 'which tokens its firing consumes' are read as: the firing exists, with the same delivery and the same result."
          "The name order enters only through the premise: σ n must be the chosen name of the renamed transition at M (Selected over the renamed selection input, which is the renamed transition's own selection input at M, nu001_matchIn_rename). The premise speaks of the renamed side only; that n is the chosen name of t at M is not assumed, and for a relation that meets NU_020_enable it holds anyway. A renaming that keeps the name order keeps the pick of every firing NU_020_enable allows, so with NU_020_enable the line gives 'a firing commutes with every strictly monotone renaming' (nu001_rename_strictMono). A renaming that does not keep the name order is what rules out reading the order anywhere but the tie-break: a matcher that fires only when the chosen name is the least name held in its correlated inputs meets every firing line of NU-020 and is rejected here (NU_001_rename_mutant_leastHeld), and so is a matcher that treats the name 0 as no name, a test on the content of a name (NU_001_rename_forbids_zeroAsNone, the case NU-021's assumes defers to this line)."
          "When the renaming changes which name the tie-break picks (possible only when two eligible names share their earliest createdAt), the line says nothing of the renamed transition's firing under the new pick. That it fires is the conjunct NuCovers of the ν consistency theorem: a transition enabled on its counts fires under its Selected name with every offered, relay-checked emission, and being enabled on the counts and eligibility read names only through equality (NU_020_enable's first two lines). So 'whether a matched transition is enabled' is this line together with NuCovers; enabledness is an existence clause and is not a line here. For a renaming that can be undone (a permutation of names) the line runs both ways when the pick is kept on both sides (nu001_rename_iff); a one-to-one renaming that is not onto has no one-to-one inverse, and for it the way back is again NuCovers with NU_020_enable's eligibility line."
          "A firing whose chosen name is not eligible meets the premise under no renaming, since a one-to-one renaming keeps a name that is not eligible not eligible (nu021_eligible), so this line says nothing of it: a matcher that lets a reserved name such as the empty string join any name when no name is eligible meets this line and is rejected by the eligibility line of NU_020_enable (nu001_wildcard_left_to_NU_020). Rust, Java and TypeScript have no such fallback."
          "The reference RefNuFire meets the line by NU-021's equivariance lemma refNuFire_transfer at the pairing 'equal values' (NU_001_rename_reference). The verifier's name symmetry is the same property one layer down: Route B's join enabling and steps are invariant under renamings (Novel.RouteB.joinEnab_inv, joinStep_sym, mintStep_sym) and its canonical key under permutations of name symbols (Novel.CanonicalKey.canonicalKey_comp)."
          "AC4 (a one-to-one renaming of the names a join's keys project, which makes the renamed chosen name the chosen name of the renamed join, does not change which tokens the join consumes or the marking it leaves) is this line, and the test derivation's renaming check is NU_001_rename_nonvacuous on the reference. No test in any language yet runs a join with its keys composed with a swap of names, so AC4 has no runtime test; it is recorded here as open. AC1 to AC3 are accounted for by the F block NU_001."
          "The sentences 'A name (NameId) is an opaque correlation identity, constructed from an underlying string value.' and 'The name order exists solely for that tie-break and carries no domain meaning.' are this line's design text. Transitions without a match project no name, so the line speaks of matched transitions only; timing, priority and the firing pass are not in the model, as for NU-020."
  signoff "pending"
  statement : ∀ {N V Nm : Type} [DecidableEq N] [LinearOrder Nm], NuFireRel N V Nm → Prop :=
    fun R =>
      ∀ t ms, t.mspec = some ms → ∀ σ, Function.Injective σ → ∀ n δ e,
        on (fun M M' => R t M (some n) δ e M'), shall (fun M M' =>
          Selected (nuMapIn σ (matchIn ms t M)) (σ n) →
            R (nuRenameNames σ t) M (some (σ n)) δ e M')

/- The pinned readable form of NU_001_rename: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.NU_001_rename : {N V Nm : Type} → [DecidableEq N] → [LinearOrder Nm] → NuFireRel N V Nm → Prop :=
fun {N V Nm} [DecidableEq N] [LinearOrder Nm] R =>
  ∀ (t : NuTrans N (KeyFn V Nm)) (ms : MatchSpec N (KeyFn V Nm)),
    t.mspec = some ms →
      ∀ (σ : Nm → Nm),
        Function.Injective σ →
          ∀ (n : Nm) (δ : QDelivered N (Stamped V)) (e : List (N × Stamped V)),
            on fun M M' => R t M (some n) δ e M', shall fun M M' =>
              Selected (nuMapIn σ (matchIn ms t M)) (σ n) → R (nuRenameNames σ t) M (some (σ n)) δ e M'
-/
#guard_msgs in #print NU_001_rename

/-! ## The reference meets the renaming line -/

section RenameFacts
variable {N V Nm : Type} [DecidableEq N] [LinearOrder Nm]

omit [DecidableEq N] [LinearOrder Nm] in
/-- A marking corresponds to itself when values are paired by equality. -/
theorem nu001_qRel_refl (M : QMarking N (Stamped V)) : NuQRel (fun _ => (· = ·)) M M :=
  fun _ => List.forall₂_same.2 fun _ _ => ⟨rfl, rfl⟩

omit [DecidableEq N] [LinearOrder Nm] in
/-- An emission corresponds to itself when values are paired by equality. -/
theorem nu001_emRel_refl (e : List (N × Stamped V)) : NuEmRel (fun _ => (· = ·)) e e :=
  List.forall₂_same.2 fun _ _ => ⟨rfl, rfl, rfl⟩

omit [DecidableEq N] [LinearOrder Nm] in
/-- Markings that correspond with values paired by equality are equal. -/
theorem nu001_qRel_eq {A B : QMarking N (Stamped V)} (h : NuQRel (fun _ => (· = ·)) A B) :
    A = B := funext fun p => by
  have h' : List.Forall₂ (· = ·) (A p) (B p) := (h p).imp fun x y hxy => by
    cases x; cases y; obtain ⟨h1, h2⟩ := hxy; simp only at h1 h2; subst h1 h2; rfl
  rwa [List.forall₂_eq_eq_eq] at h'

omit [DecidableEq N] [LinearOrder Nm] in
/-- The keys (or relay targets) of a match correspond to their renaming, with values paired by
equality. -/
theorem nu001_keysRel (σ : Nm → Nm) (ks : List (N × KeyFn V Nm)) :
    List.Forall₂ (NuKeyRel (fun _ => (· = ·)) σ) ks (ks.map fun k => (k.1, nuRenameKey σ k.2)) := by
  induction ks with
  | nil => exact .nil
  | cons k ks ih => exact .cons ⟨rfl, fun v w hvw => by subst hvw; rfl⟩ ih

omit [LinearOrder Nm] in
/-- The renamed match's selection input is the selection input with every name renamed: the
premise of the line is the renamed transition's own tie-break at `M`. -/
theorem nu001_matchIn_rename (σ : Nm → Nm) (ms : MatchSpec N (KeyFn V Nm))
    (t : NuTrans N (KeyFn V Nm)) (M : QMarking N (Stamped V)) :
    matchIn (nuRenameMs σ ms) (nuRenameNames σ t) M = nuMapIn σ (matchIn ms t M) :=
  nu021_matchIn (t₁ := t) rfl (nu001_keysRel σ ms.keys) (nu001_qRel_refl M)

/-- ✓ RefNuFire satisfies the renaming line: by NU-021's equivariance lemma with values paired
by equality, the renamed transition takes the same tokens for the renamed chosen name, accepts
the same emission and leaves the same marking; and the tie-break picks the renamed chosen name,
which is the premise. -/
@[evidence holds NU_001_rename]
theorem NU_001_rename_reference : NU_001_rename (RefNuFire (N := N) (V := V) (Nm := Nm)) := by
  intro t ms hm σ hσ n δ e M M' hf hsel
  obtain ⟨n', hn, -, hen, ⟨ch, hdep⟩, hrok, rfl, rfl⟩ := (refNuFire_matched hm M _ _ _ _).1 hf
  cases hn
  have hm₂ : (nuRenameNames σ t).mspec = some (nuRenameMs σ ms) := by
    simp [nuRenameNames, hm]
  have hb : t.base = (nuRenameNames σ t).base := rfl
  have hk : List.Forall₂ (NuKeyRel (fun _ => (· = ·)) σ) ms.keys (nuRenameMs σ ms).keys :=
    nu001_keysRel σ ms.keys
  have hr : List.Forall₂ (NuKeyRel (fun _ => (· = ·)) σ) ms.relays (nuRenameMs σ ms).relays :=
    nu001_keysRel σ ms.relays
  have hM := nu001_qRel_refl M
  obtain ⟨hin, hpost⟩ := nu021_nuInputs_nuPost hσ hb hk hM n
  have hc := nu021_corrTake hσ hb hk hM n
  have hinEq := nu001_qRel_eq hin
  have hpostEq := nu001_qRel_eq hpost
  refine (refNuFire_matched hm₂ M _ _ _ _).2 ⟨σ n, rfl, ?_, hen, ⟨ch, ?_⟩, ?_, ?_, ?_⟩
  · rw [nu001_matchIn_rename]; exact refSelect_eq_some_iff.2 hsel
  · rw [hc]; exact hdep
  · exact nu021_relayOk hr (nu001_emRel_refl e) hrok
  · unfold nuDelivered; rw [hinEq, hpostEq]; rfl
  · unfold nuConsume; rw [hpostEq]; rfl

/-- With NU-020's tie-break line, the renaming line gives the commuting form: every firing commutes
with every strictly monotone renaming of names (such a renaming keeps the tie-break's pick). -/
theorem nu001_rename_strictMono {R : NuFireRel N V Nm} (h1 : NU_001_rename R)
    (h2 : NU_020_enable R) {t : NuTrans N (KeyFn V Nm)} {ms : MatchSpec N (KeyFn V Nm)}
    (hm : t.mspec = some ms) {σ : Nm → Nm} (hσ : StrictMono σ) {M : QMarking N (Stamped V)}
    {n δ e M'} (hf : R t M (some n) δ e M') : R (nuRenameNames σ t) M (some (σ n)) δ e M' := by
  refine h1 t ms hm σ hσ.injective n δ e M M' hf ⟨?_, fun m hm' => ?_⟩
  · obtain ⟨n', hn', hel⟩ := h2.2.1 t ms hm _ δ e M M' hf
    cases hn'
    rw [nu021_eligible hσ.injective]; exact hel
  · obtain ⟨m', rfl⟩ := nu021_eligible_image _ hm'
    rw [nu021_eligible hσ.injective] at hm'
    exact (nu021_selKey hσ _ n m').2 (h2.2.2 t ms hm n δ e M M' hf m' hm')

omit [DecidableEq N] [LinearOrder Nm] in
/-- Renaming the keys and relay targets by `σ` and then by a left inverse `τ` of `σ` gives back
the keys and relay targets. -/
theorem nu001_keys_rename_rename {σ τ : Nm → Nm} (h : ∀ x, τ (σ x) = x)
    (ks : List (N × KeyFn V Nm)) :
    ((ks.map fun k => (k.1, nuRenameKey σ k.2)).map fun k => (k.1, nuRenameKey τ k.2)) = ks := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.map_cons, ih, List.cons.injEq, and_true]
    refine Prod.ext rfl (funext fun v => ?_)
    simp only [nuRenameKey, Option.map_map]
    cases k.2 v <;> simp [h]

omit [DecidableEq N] [LinearOrder Nm] in
/-- Renaming a transition's names by `σ` and then by a left inverse `τ` of `σ` gives back the
transition. -/
theorem nu001_rename_rename {σ τ : Nm → Nm} (h : ∀ x, τ (σ x) = x) (t : NuTrans N (KeyFn V Nm)) :
    nuRenameNames τ (nuRenameNames σ t) = t := by
  obtain ⟨b, ms⟩ := t
  cases ms with
  | none => rfl
  | some ms =>
    simp only [nuRenameNames, Option.map_some, nuRenameMs, nu001_keys_rename_rename h]

omit [DecidableEq N] [LinearOrder Nm] in
/-- Renaming a selection input's names by `σ` and then by a left inverse `τ` of `σ` gives back
the selection input. -/
theorem nu001_mapIn_mapIn {σ τ : Nm → Nm} (h : ∀ x, τ (σ x) = x) (I : MatchIn Nm) :
    nuMapIn τ (nuMapIn σ I) = I := by
  obtain ⟨ks⟩ := I
  simp [nuMapIn, Function.comp_def, h]

/-- For a renaming that can be undone, the renaming line runs both ways: when the chosen name
`n` of `t` and its renamed name `σ n` of the renamed transition are both the tie-break's pick at
`M`, then `t` fires with `n` exactly when the renamed transition fires with `σ n`, with the same
delivery, emission and result. The way back is the line applied to the inverse renaming. -/
theorem nu001_rename_iff {R : NuFireRel N V Nm} (h1 : NU_001_rename R)
    {t : NuTrans N (KeyFn V Nm)} {ms : MatchSpec N (KeyFn V Nm)} (hm : t.mspec = some ms)
    {σ τ : Nm → Nm} (hστ : ∀ x, τ (σ x) = x) (hτσ : ∀ y, σ (τ y) = y)
    {M : QMarking N (Stamped V)} {n δ e M'} (hsel : Selected (matchIn ms t M) n)
    (hsel' : Selected (nuMapIn σ (matchIn ms t M)) (σ n)) :
    R t M (some n) δ e M' ↔ R (nuRenameNames σ t) M (some (σ n)) δ e M' := by
  have hσ : Function.Injective σ := fun x y hxy => by rw [← hστ x, hxy, hστ y]
  have hτ : Function.Injective τ := fun x y hxy => by rw [← hτσ x, hxy, hτσ y]
  have hm₂ : (nuRenameNames σ t).mspec = some (nuRenameMs σ ms) := by
    simp [nuRenameNames, hm]
  refine ⟨fun hf => h1 t ms hm σ hσ n δ e M M' hf hsel', fun hf => ?_⟩
  have hback := h1 _ _ hm₂ τ hτ (σ n) δ e M M' hf (by
    rw [nu001_matchIn_rename, nu001_mapIn_mapIn hστ, hστ]; exact hsel)
  rwa [nu001_rename_rename hστ, hστ] at hback

end RenameFacts

/-! ## Examples: a join of places 0 and 1 whose key reads the name off the value -/

/-- The renaming that swaps the names `a` and `b` and keeps every other name. -/
def nu001_swap (a b : Nat) : Nat → Nat := fun x => if x = a then b else if x = b then a else x

/-- A swap is one-to-one. -/
theorem nu001_swap_inj (a b : Nat) : Function.Injective (nu001_swap a b) := by
  intro x y h
  unfold nu001_swap at h
  split_ifs at h <;> omega

/-- Place 0 holds 1@0, 2@1; place 1 holds 2@2, 1@3. Both names are eligible; name 1 has the
earlier token (createdAt 0 against 1), so the tie-break picks 1. -/
def nu001_M : QMarking Nat (Stamped Nat) := fun p =>
  if p = 0 then [nu020_tok 1 0, nu020_tok 2 1]
  else if p = 1 then [nu020_tok 2 2, nu020_tok 1 3] else []

/-- The reference join fires on `nu001_M` with name 1, taking 1@0 and 1@3. -/
theorem nu001_fires :
    RefNuFire (nu020_join .one .one) nu001_M (some 1)
      (nuDelivered nu020_ms (nu020_join .one .one) nu001_M 1) []
      (qAppend (nuConsume nu020_ms (nu020_join .one .one) nu001_M 1) []) :=
  ⟨1, rfl, by decide, by decide, ⟨.action 0, rfl⟩, fun r hr => by simp [nu020_ms] at hr, rfl, rfl⟩

/-- ✓ Worked example. Place 0 holds 1@0, 2@1 and place 1 holds 2@2, 1@3, and the join fires with
name 1, the name with the earlier token. Now swap the names 1 and 2, which reverses their order:
name 2 now has the earlier token, so the tie-break picks it, and the renamed join fires with name 2,
taking the same two tokens 1@0 and 1@3 and leaving the same marking. -/
@[evidence nonvacuous NU_001_rename]
theorem NU_001_rename_nonvacuous :
    RefNuFire (nu020_join .one .one) nu001_M (some 1)
        (nuDelivered nu020_ms (nu020_join .one .one) nu001_M 1) []
        (qAppend (nuConsume nu020_ms (nu020_join .one .one) nu001_M 1) []) ∧
      Selected (nuMapIn (nu001_swap 1 2) (matchIn nu020_ms (nu020_join .one .one) nu001_M)) 2 ∧
      RefNuFire (nuRenameNames (nu001_swap 1 2) (nu020_join .one .one)) nu001_M (some 2)
        (nuDelivered nu020_ms (nu020_join .one .one) nu001_M 1) []
        (qAppend (nuConsume nu020_ms (nu020_join .one .one) nu001_M 1) []) ∧
      nuInputs nu020_ms (nu020_join .one .one) nu001_M 1 0 = [nu020_tok 1 0] ∧
      nuInputs nu020_ms (nu020_join .one .one) nu001_M 1 1 = [nu020_tok 1 3] := by
  have hs : Selected (nuMapIn (nu001_swap 1 2) (matchIn nu020_ms (nu020_join .one .one) nu001_M))
      (nu001_swap 1 2 1) := refSelect_eq_some_iff.1 (by decide)
  exact ⟨nu001_fires, hs, NU_001_rename_reference _ nu020_ms rfl _ (nu001_swap_inj 1 2) 1 _ _ _ _
    nu001_fires hs, by decide, by decide⟩

/-! ## Wrong firings the renaming line rejects -/

/-- The reference firing with an extra condition `G` on the transition, the marking and the
chosen name. -/
def nu001_gated (G : NuTrans Nat (KeyFn Nat Nat) → QMarking Nat (Stamped Nat) → Option Nat → Prop) :
    NuFireRel Nat Nat Nat := fun t M c δ e M' => RefNuFire t M c δ e M' ∧ G t M c

/-- The lines of NU-020 that speak of a firing (the tie-break, the correlated take, the frame). -/
def nu001_nu020Lines {N V Nm : Type} [DecidableEq N] [LinearOrder Nm] (R : NuFireRel N V Nm) :
    Prop :=
  NU_020_enable R ∧ NU_020_take R ∧ NU_020_frame R

/-- A gated reference firing meets every line of NU-020: each line constrains only the firings
that happen, and the gate only removes firings. -/
theorem nu001_gated_meets_NU_020 (G) : nu001_nu020Lines (nu001_gated G) := by
  obtain ⟨e1, e2, e3⟩ := NU_020_enable_reference (N := Nat) (V := Nat) (Nm := Nat)
  obtain ⟨t1, t2⟩ := NU_020_take_reference (N := Nat) (V := Nat) (Nm := Nat)
  obtain ⟨f1, f2, f3, f4, f5⟩ := NU_020_frame_reference (N := Nat) (V := Nat) (Nm := Nat)
  exact ⟨⟨fun t ms hm c δ e M M' hf => e1 t ms hm c δ e M M' hf.1,
      fun t ms hm c δ e M M' hf => e2 t ms hm c δ e M M' hf.1,
      fun t ms hm n δ e M M' hf => e3 t ms hm n δ e M M' hf.1⟩,
    ⟨fun t ms hm n δ e M M' hf => t1 t ms hm n δ e M M' hf.1,
      fun t ms hm n δ e M M' hf => t2 t ms hm n δ e M M' hf.1⟩,
    ⟨fun t ms hm n δ e M M' hf => f1 t ms hm n δ e M M' hf.1,
      fun t ms hm n δ e M M' hf => f2 t ms hm n δ e M M' hf.1,
      fun t ms hm n δ e M M' hf => f3 t ms hm n δ e M M' hf.1,
      fun t ms hm n δ e M M' hf => f4 t ms hm n δ e M M' hf.1,
      fun t ms hm n δ e M M' hf => f5 t ms hm n δ e M M' hf.1⟩⟩

/-- The gate "the chosen name is the least name held in the correlated inputs": every name a
correlated input's key gives to one of its tokens, eligible or not, is at least the chosen name. -/
def nu001_leastHeldGate (t : NuTrans Nat (KeyFn Nat Nat)) (M : QMarking Nat (Stamped Nat))
    (c : Option Nat) : Prop :=
  ∀ ms, t.mspec = some ms → ∀ n, c = some n → ∀ k ∈ (matchIn ms t M).keys, ∀ x ∈ k.1, n ≤ x.1

/-- The matcher that fires only when the chosen name is the least name held in its correlated
inputs: it reads the name order outside the tie-break. -/
def nu001_leastHeld : NuFireRel Nat Nat Nat := nu001_gated nu001_leastHeldGate

/-- Place 0 holds 1@0, 2@1; place 1 holds 1@2. Only name 1 is eligible (place 1 holds no 2), and
1 is also the least name held. -/
def nu001_M1 : QMarking Nat (Stamped Nat) := fun p =>
  if p = 0 then [nu020_tok 1 0, nu020_tok 2 1] else if p = 1 then [nu020_tok 1 2] else []

/-- ✗ Worked example. Place 0 holds 1@0, 2@1 and place 1 holds 1@2; only name 1 can join, and it
is the least name held, so this matcher fires with 1. Swap the names 1 and 2: the only name that
can join is now 2, so the tie-break picks it, but 2 is no longer the least name held (place 0 also
holds a token named 1), and this matcher does not fire. It meets every firing line of NU-020, so only the
renaming line rules out reading the name order outside the tie-break. -/
@[evidence mutant NU_001_rename]
theorem NU_001_rename_mutant_leastHeld :
    nu001_nu020Lines nu001_leastHeld ∧ ¬ NU_001_rename nu001_leastHeld := by
  refine ⟨nu001_gated_meets_NU_020 _, fun h => ?_⟩
  have hf : nu001_leastHeld (nu020_join .one .one) nu001_M1 (some 1)
      (nuDelivered nu020_ms (nu020_join .one .one) nu001_M1 1) []
      (qAppend (nuConsume nu020_ms (nu020_join .one .one) nu001_M1 1) []) := by
    refine ⟨⟨1, rfl, by decide, by decide, ⟨.action 0, rfl⟩,
      fun r hr => by simp [nu020_ms] at hr, rfl, rfl⟩, ?_⟩
    intro ms hms n hn
    simp only [nu020_join, Option.some.injEq] at hms hn
    subst hms hn
    decide
  have hs : Selected (nuMapIn (nu001_swap 1 2) (matchIn nu020_ms (nu020_join .one .one) nu001_M1))
      (nu001_swap 1 2 1) := refSelect_eq_some_iff.1 (by decide)
  have h2 := (h _ nu020_ms rfl _ (nu001_swap_inj 1 2) 1 _ _ _ _ hf hs).2 _ rfl _ rfl
  revert h2
  decide

/-- The gate "the name 0 is no name": the matcher refuses to join on the name 0, a test on the
content of a name. -/
def nu001_zeroAsNoneGate (_t : NuTrans Nat (KeyFn Nat Nat)) (_M : QMarking Nat (Stamped Nat))
    (c : Option Nat) : Prop :=
  c ≠ some 0

/-- ✗ Worked example. Place 0 holds 11@0 and place 1 holds 11@1 (the marking of NU-021's
examples, here with the key that reads the name off the value), and a matcher that treats the name
0 as no name fires with name 11. Swap the names 11 and 0: the only name that can join is now 0, the
tie-break picks it, and the matcher refuses to fire, so the renaming line fails. -/
@[evidence forbids NU_001_rename]
theorem NU_001_rename_forbids_zeroAsNone : ¬ NU_001_rename (nu001_gated nu001_zeroAsNoneGate) := by
  intro h
  have hf : nu001_gated nu001_zeroAsNoneGate (nu020_join .one .one) nu021_M₁ (some 11)
      (nuDelivered nu020_ms (nu020_join .one .one) nu021_M₁ 11) []
      (qAppend (nuConsume nu020_ms (nu020_join .one .one) nu021_M₁ 11) []) :=
    ⟨⟨11, rfl, by decide, by decide, ⟨.action 0, rfl⟩,
      fun r hr => by simp [nu020_ms] at hr, rfl, rfl⟩, by show (some 11 : Option Nat) ≠ some 0; decide⟩
  have hs : Selected (nuMapIn (nu001_swap 0 11) (matchIn nu020_ms (nu020_join .one .one) nu021_M₁))
      (nu001_swap 0 11 11) := refSelect_eq_some_iff.1 (by decide)
  exact (h _ nu020_ms rfl _ (nu001_swap_inj 0 11) 11 _ _ _ _ hf hs).2 (by decide)

/-- Folding a name to its last digit, standing in for a name equality that normalises (a `NameId`
whose `equals` and `hashCode` fold case, used as the key of the per-input name index). -/
def nu001_fold (x : Nat) : Nat := x % 10

/-- The matcher whose name index is keyed by the folded name: the reference firing of `t` with
every name its keys give folded, so different names that fold alike share one bucket. -/
def nu001_folded : NuFireRel Nat Nat Nat := fun t => RefNuFire (nuRenameNames nu001_fold t)

/-- Place 0 holds 1@0; place 1 holds 11@1, 1@2. -/
def nu001_M2 : QMarking Nat (Stamped Nat) := fun p =>
  if p = 0 then [nu020_tok 1 0] else if p = 1 then [nu020_tok 11 1, nu020_tok 1 2] else []

/-- ✗ Worked example. Place 0 holds 1@0 and place 1 holds 11@1, 1@2. A matcher that folds names
to their last digit treats 11 as 1, joins on name 1 and takes 11@1 from place 1, the first token
of its bucket. Swap the names 11 and 12: the tie-break still picks 1, but 12 folds to 2, so the
matcher now takes 1@2 from place 1. The renaming line asks for the same tokens, so it rejects a
name equality that is coarser than equality of names. -/
@[evidence forbids NU_001_rename]
theorem NU_001_rename_forbids_folded : ¬ NU_001_rename nu001_folded := by
  intro h
  have hf : nu001_folded (nu020_join .one .one) nu001_M2 (some 1)
      (nuDelivered (nuRenameMs nu001_fold nu020_ms) (nuRenameNames nu001_fold (nu020_join .one .one))
        nu001_M2 1) []
      (qAppend (nuConsume (nuRenameMs nu001_fold nu020_ms)
        (nuRenameNames nu001_fold (nu020_join .one .one)) nu001_M2 1) []) :=
    (refNuFire_matched (ms := nuRenameMs nu001_fold nu020_ms) rfl _ _ _ _ _).2
      ⟨1, rfl, by decide, by decide, ⟨.action 0, rfl⟩,
        fun r hr => by simp [nuRenameMs, nu020_ms] at hr, rfl, rfl⟩
  have hs : Selected (nuMapIn (nu001_swap 11 12) (matchIn nu020_ms (nu020_join .one .one) nu001_M2))
      (nu001_swap 11 12 1) := refSelect_eq_some_iff.1 (by decide)
  have h2 := h _ nu020_ms rfl _ (nu001_swap_inj 11 12) 1 _ _ _ _ hf hs
  obtain ⟨n, hc, -, -, -, -, hδ, -⟩ :=
    (refNuFire_matched (ms := nuRenameMs nu001_fold (nuRenameMs (nu001_swap 11 12) nu020_ms)) rfl
      _ _ _ _ _).1 h2
  have hn : n = 1 := by simp [nu001_swap] at hc; omega
  subst hn
  have := congrArg (fun d => d.inputs 1) hδ
  revert this
  decide

/-- Reading the name 0 as the name `n`. -/
def nu001_wild (n : Nat) : Nat → Nat := fun x => if x = 0 then n else x

/-- A matcher with a reserved wildcard name used as a fallback: it fires as the reference does,
and when no name can join it lets a token whose key gives the name 0 (the empty string in a
runtime) stand in for any name `n` and fires with `n`. -/
def nu001_wildcard : NuFireRel Nat Nat Nat := fun t M c δ e M' =>
  RefNuFire t M c δ e M' ∨
    ∃ ms n, t.mspec = some ms ∧ (∀ m, eligible (matchIn ms t M) m = false) ∧ c = some n ∧
      RefNuFire (nuRenameNames (nu001_wild n) t) M (some n) δ e M'

/-- Place 0 holds 1@0; place 1 holds the wildcard 0@1. No name is in both places. -/
def nu001_M3 : QMarking Nat (Stamped Nat) := fun p =>
  if p = 0 then [nu020_tok 1 0] else if p = 1 then [nu020_tok 0 1] else []

/-- Worked example of what the renaming line leaves to NU-020. Place 0 holds 1@0 and place 1
holds 0@1, so no name is in both places and the join cannot fire. A matcher that reads the name 0
as "joins anything" fires anyway with name 1. The renaming line accepts this matcher: its extra
firings use a chosen name that cannot join, and no one-to-one renaming makes such a name the
tie-break's pick, so the line never applies to them. NU-020's line "the chosen name can join"
rejects it. -/
theorem nu001_wildcard_left_to_NU_020 :
    NU_001_rename nu001_wildcard ∧ ¬ NU_020_enable nu001_wildcard := by
  refine ⟨fun t ms hm σ hσ n δ e M M' hf hsel => ?_, fun h => ?_⟩
  · rcases hf with hf | ⟨ms', n', hm', hnone, hc, -⟩
    · exact Or.inl (NU_001_rename_reference t ms hm σ hσ n δ e M M' hf hsel)
    · rw [hm] at hm'; cases hm'; cases hc
      have h1 := hsel.1
      rw [nu021_eligible hσ, hnone n] at h1
      exact absurd h1 Bool.false_ne_true
  · have hnone : ∀ m, eligible (matchIn nu020_ms (nu020_join .one .one) nu001_M3) m = false := by
      intro m
      by_cases h0 : m = 0
      · subst h0; decide
      · by_cases h1 : m = 1
        · subst h1; decide
        · simp [eligible, matchIn, nu020_ms, nu020_key, nu001_M3, stamps, nu020_tok, Ne.symm h0,
            Ne.symm h1]
    have hf : nu001_wildcard (nu020_join .one .one) nu001_M3 (some 1)
        (nuDelivered (nuRenameMs (nu001_wild 1) nu020_ms)
          (nuRenameNames (nu001_wild 1) (nu020_join .one .one)) nu001_M3 1) []
        (qAppend (nuConsume (nuRenameMs (nu001_wild 1) nu020_ms)
          (nuRenameNames (nu001_wild 1) (nu020_join .one .one)) nu001_M3 1) []) :=
      Or.inr ⟨nu020_ms, 1, rfl, hnone, rfl,
        (refNuFire_matched (ms := nuRenameMs (nu001_wild 1) nu020_ms) rfl _ _ _ _ _).2
          ⟨1, rfl, by decide, by decide, ⟨.action 0, rfl⟩,
            fun r hr => by simp [nuRenameMs, nu020_ms] at hr, rfl, rfl⟩⟩
    obtain ⟨n, hn, hel⟩ := h.2.1 (nu020_join .one .one) nu020_ms rfl _ _ _ nu001_M3 _ hf
    cases hn
    rw [hnone] at hel
    exact absurd hel Bool.false_ne_true

end Libpetri.Spec
