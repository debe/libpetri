import Libpetri.Spec.Registry

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
supplementary-plane characters (`NU_001_allows_utf16`). Ruling D96 (a) adds a behaviour line (a
firing depends on names only through equality and, for the tie-break, the name order); it is stated
in wave W9 over the ν firing model, together with NU-021's value-blindness, and is an assumes item
here.

Consistency: this block has no conjunct in a `Consistency*` module yet. Its conjunct
(`∃ I : NameImpl, NU_001 I`, instantiated by `refNameImpl`) joins `Spec/ConsistencyNu.lean`, the
ν sketch of wave W9, where the name type it fixes is shared with the ν firing model.
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
          "Ruling D96 (a): the sentence 'Whether a matched transition is enabled, and which tokens its firing consumes, shall depend on the names its keys project only through name equality and, for the tie-break of [NU-020], the name order.' is a behaviour line over the ν firing model and is stated in wave W9 together with NU-021, not in this block. It needs two clauses there: (i) under every injective renaming of projected names, whether a matched transition is enabled is unchanged and the names the tie-break chooses among are renamed, with the consumed tokens following the chosen name, so the order cannot decide enabledness or consumption outside the tie-break (a rule 'enabled only if the matched name is the least name in the marking' breaks it); (ii) a firing commutes with every injective renaming that also preserves the name order. Equivariance under order-preserving renamings alone is weaker than the sentence and does not discharge it. The sentences 'A name (NameId) is an opaque correlation identity, constructed from an underlying string value.' and 'The name order exists solely for that tie-break and carries no domain meaning.' are this line's design text and are traced by it. The verifier's name symmetry (Novel.RouteB.joinEnab_inv, joinStep_sym, mintStep_sym, CanonicalKey.canonicalKey_comp) is cited there."
          "'Identity is a projection of the token payload, not a field on the token' and 'the token model is unchanged' are design text: a match key reads the token value (NU-020), and no model in this development adds a name field to a token. AC3 (adding ν-matching does not change the token type or the on-the-wire shape of token-bearing events) and the test derivation's third check are API and wire shape (kind Q). No test in any language yet runs a net with and without the ν-net APIs and compares its token events, so AC3 has no traced Q evidence; it is recorded here as open, to be closed by a kind Q test beside the EVT-011 and EVT-012 tests."
          "AC1 (two names constructed from the same underlying value are equal; from different values, unequal) is the first line. AC2 (a stable total order on names, consistent across a single implementation) is the second, third and fourth lines: a strict total order on names, with stability read as above."
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
            (∀ (c : Char), c ∈ a.toList → c.toNat < 65536) →
              (∀ (c : Char), c ∈ b.toList → c.toNat < 65536) → (I.lt (I.ofValue a) (I.ofValue b) ↔ a < b)
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

end Libpetri.Spec
