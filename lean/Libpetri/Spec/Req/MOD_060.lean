import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryCompose
import Libpetri.Reference.Fuse
import Libpetri.Reference.ComposeBuild
import Libpetri.Spec.Req.MOD_061

set_option linter.missingDocs true

/-!
# MOD-060: Fusion set declaration (`spec/11-modular-composition.md`)

MOD-060 is a pure-function requirement (kind F) over an abstract declaration check
`D : DeclFn N`: declaring a fusion set either returns the set or fails with a message. The
token type of a place is read through a model parameter `tyOf`; an implementation that keeps no
run-time token type (TypeScript) is the case `tyOf := fun _ => ()`, where every set agrees on
its type.

Three lines: a set with no member is rejected; a set with at least one member whose members
agree on the token type is accepted and returned as declared, one member included (ruling D54
(a)); a set whose members disagree on the token type is rejected. The witness is the reference
check `refDeclFusion tyOf` of `Reference/Fuse.lean`, the check the build script runs on every
`fuse` call (`scriptStep`), so the declaration MOD-060 states is the one whose sets MOD-061
fuses (`MOD_060_joint`). Which member is canonical, and that the canonical member keeps its own
name, is MOD-061's: its substitution sends every member to `FusionSet.canonical`, the first
declared member.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## MOD-060: Fusion Set Declaration (orthogonal to composition) -/

requirement MOD_060
  id "MOD-060"
  title "Fusion Set Declaration (orthogonal to composition)"
  kind F
  scope "every fusion-set declaration check"
  source verbatim "spec/11-modular-composition.md"
  quote "*If* a fusion set is declared with no member, *then* declaring it *shall* fail."
        "*When* a fusion set is declared with at least one member and no two of its members have different run-time token types, declaring it *shall* succeed and *shall* return the set with its name and with its members in the order they were declared."
        "*Where* an implementation keeps a run-time token type for places (Java and Rust), *if* two members of a fusion set have different token types, *then* declaring the set *shall* fail."
  reading "For every token-type reading tyOf of places and every fusion-set declaration check D:"
          "for every name n, D rejects the set named n with no member;"
          "for every set s with at least one member whose members all have the same token type under tyOf, D returns s itself: its name and its members in declaration order;"
          "for every set s two of whose members have different token types under tyOf, D rejects s."
  assumes "The model is an abstract declaration check D : DeclFn N (Reference/Fuse.lean): a set (FusionSet, glossary GlossaryCompose.lean: a name and the member places in declaration order) is accepted, returning a set, or rejected with a message. The token type is a model parameter tyOf: Java reads Place.tokenType (java/src/main/java/org/libpetri/core/FusionSet.java Builder.build) and Rust the run-time TypeId of each member (rust/libpetri-core/src/fusion.rs FusionSetBuilder.member, which rejects a member of another type as it is added); TypeScript (typescript/src/core/fusion-set.ts FusionSetBuilder.build) keeps no run-time token type and is the case tyOf := fun _ => (), under which line 3 never applies. The Python binding (rust/libpetri-py) exposes no fusion-set declaration, so no line reaches it. The witness is refDeclFusion tyOf, which is what every runtime does: an empty member list is rejected with 'must have at least one member (MOD-060)', a member whose type differs from the first member's is rejected, and otherwise the set is kept as declared."
          "Line 1 is the first quoted sentence and AC4's malformed case: a check that accepts an empty set is killed (MOD_060_mutant_acceptEmpty_killed). Line 2 is the second quoted sentence, AC1 and the body's item 2: a set with one member is accepted (ruling D54 (a): every runtime accepts it, and it fuses nothing, since its canonical member maps to itself); a check that rejects a one-member set as malformed, the earlier SHOULD of AC4, is killed (MOD_060_mutant_rejectSingleton_killed). 'Returns the set as declared' fixes the member order, so the canonical member, the first declared (FusionSet.canonical, which MOD-061's substitution reads), is the one the caller wrote first; a check that reorders the members breaks line 2 (MOD_060_forbids_reorder)."
          "Line 3 is the third quoted sentence and AC3, under ruling D36 (a): the token-type check is stated where an implementation keeps a run-time token type. A check that compares no token type is killed (MOD_060_mutant_noTypeCheck_killed). Compatibility per CORE-003 is equality of the run-time token type in Java and Rust; a compile-time check (TypeScript's generic FusionSet.of, Rust's typed member) is typing, not modelled."
          "AC2 (fusion is independent of port bindings; the canonical fused place is the substitution target of every arc that referenced a port-substituted place or a non-canonical member) and the paragraph on the order of operations are MOD-061's: fusion runs at build(), after every compose call (Reference/ComposeBuild.lean finish and fuseStage), and its substitution sends every member to the first declared member (MOD-061 lines 1, 3 and 4 through SubstSpec). The name of a fusion set is used in diagnostics only (MOD-061 step 1); Rust and TypeScript also reject an empty name when the builder is created and Java accepts it, which no sentence states. The test derivation (three members of one type accepted; one member accepted and fusing nothing; no member rejected; mixed types rejected in Java and Rust; the compose-then-fuse case) is MOD_060_nonvacuous for the declarations and MOD-061 for the build."
  signoff "pending"
  statement : ∀ {N T : Type}, (N → T) → DeclFn N → Prop :=
    fun {N _T} tyOf D =>
      (∀ n : String, ∃ m, D ⟨n, []⟩ = .error m) ∧
      (∀ s : FusionSet N, s.members ≠ [] → TypesAgree tyOf s → D s = .ok s) ∧
      (∀ s : FusionSet N, ¬ TypesAgree tyOf s → ∃ m, D s = .error m)

/- The pinned readable form of MOD-060: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.MOD_060 : {N T : Type} → (N → T) → DeclFn N → Prop :=
fun {N _T} tyOf D =>
  (∀ (n : String), ∃ m, D { name := n, members := [] } = Except.error m) ∧
    (∀ (s : FusionSet N), s.members ≠ [] → TypesAgree tyOf s → D s = Except.ok s) ∧
      ∀ (s : FusionSet N), ¬TypesAgree tyOf s → ∃ m, D s = Except.error m
-/
#guard_msgs in #print MOD_060

/-! ### The three lines, named (for the mutants) -/

section Lines

variable {N T : Type}

/-- Line 1 of MOD-060: a set with no member is rejected. -/
def mod060_line1 (D : DeclFn N) : Prop := ∀ n : String, ∃ m, D ⟨n, []⟩ = .error m

/-- Line 2 of MOD-060: a non-empty set whose members agree on the token type is returned as
declared. -/
def mod060_line2 (tyOf : N → T) (D : DeclFn N) : Prop :=
  ∀ s : FusionSet N, s.members ≠ [] → TypesAgree tyOf s → D s = .ok s

/-- Line 3 of MOD-060: a set whose members disagree on the token type is rejected. -/
def mod060_line3 (tyOf : N → T) (D : DeclFn N) : Prop :=
  ∀ s : FusionSet N, ¬ TypesAgree tyOf s → ∃ m, D s = .error m

/-- MOD-060 is its three lines. -/
theorem mod060_iff (tyOf : N → T) (D : DeclFn N) :
    MOD_060 tyOf D ↔ mod060_line1 D ∧ mod060_line2 tyOf D ∧ mod060_line3 tyOf D :=
  Iff.rfl

/-- A set with no member agrees on every token type. -/
theorem typesAgree_nil (tyOf : N → T) (n : String) : TypesAgree tyOf (⟨n, []⟩ : FusionSet N) :=
  fun _ h => absurd h List.not_mem_nil

/-- Every set agrees on a token type that tells no place apart. -/
theorem typesAgree_unit (s : FusionSet N) : TypesAgree (fun _ : N => ()) s :=
  fun _ _ _ _ => rfl

end Lines

/-! ### The reference -/

section Ref

variable {N T : Type} [ToString N] [DecidableEq T]

/-- The three lines of the reference declaration check, for every token-type reading. -/
theorem refDeclFusion_lines (tyOf : N → T) :
    mod060_line1 (refDeclFusion tyOf) ∧ mod060_line2 tyOf (refDeclFusion tyOf) ∧
      mod060_line3 tyOf (refDeclFusion tyOf) :=
  ⟨refDeclFusion_empty tyOf,
    fun s hne hty => (refDeclFusion_ok_iff tyOf s s).2 ⟨hne, hty, rfl⟩,
    fun s hty => except_error_of_not_ok fun s' h =>
      hty ((refDeclFusion_ok_iff tyOf s s').1 h).2.1⟩

end Ref

/-- ✓ The reference declaration check satisfies MOD-060 for every token-type reading: it rejects
a set with no member, rejects a set two of whose members have different token types, and
otherwise returns the set exactly as it was declared, a set with one member included. -/
@[evidence holds MOD_060]
theorem MOD_060_reference {N T : Type} [ToString N] [DecidableEq T] (tyOf : N → T) :
    MOD_060 tyOf (refDeclFusion tyOf) :=
  refDeclFusion_lines tyOf

/-! ### Example -/

/-- The example token type: the parity of a place number, so places 0, 2 and 4 share a type and
place 1 has another. -/
def mod060_ty (n : Nat) : Nat := n % 2

/-- ✓ Every line of MOD-060 is exercised by the reference. With places numbered and typed by
parity: the set `permits` with members 0, 2 and 4 (one type) is accepted as declared; the set
`one` with the single member 3 is accepted too and fuses nothing; the set `empty` with no member
is rejected; the set `mixed` with members 0 and 1 (two types) is rejected. The same check
without run-time token types, as in TypeScript, accepts `mixed`. -/
@[evidence nonvacuous MOD_060]
theorem MOD_060_nonvacuous :
    refDeclFusion mod060_ty ⟨"permits", [0, 2, 4]⟩ = .ok ⟨"permits", [0, 2, 4]⟩ ∧
      refDeclFusion mod060_ty ⟨"one", [3]⟩ = .ok ⟨"one", [3]⟩ ∧
      (∃ m, refDeclFusion mod060_ty (⟨"empty", []⟩ : FusionSet Nat) = .error m) ∧
      (∃ m, refDeclFusion mod060_ty ⟨"mixed", [0, 1]⟩ = .error m) ∧
      refDeclFusion (fun _ : Nat => ()) ⟨"mixed", [0, 1]⟩ = .ok ⟨"mixed", [0, 1]⟩ :=
  ⟨rfl, rfl, ⟨_, rfl⟩, ⟨_, rfl⟩, rfl⟩

/-! ### Mutants, one per line -/

section Mutants

variable {N T : Type}

/-- Mutant reading: MOD-060 without line 1 (a set with no member may be accepted). -/
def MOD_060_mutant_acceptEmpty (tyOf : N → T) (D : DeclFn N) : Prop :=
  mod060_line2 tyOf D ∧ mod060_line3 tyOf D

/-- Mutant reading: MOD-060 without line 2 (a well-typed set may be rejected or changed). -/
def MOD_060_mutant_rejectSingleton (tyOf : N → T) (D : DeclFn N) : Prop :=
  mod060_line1 D ∧ mod060_line3 tyOf D

/-- Mutant reading: MOD-060 without line 3 (members of two token types may be accepted). -/
def MOD_060_mutant_noTypeCheck (tyOf : N → T) (D : DeclFn N) : Prop :=
  mod060_line1 D ∧ mod060_line2 tyOf D

end Mutants

/-- A declaration check that accepts a set with no member and is the reference otherwise. -/
def acceptEmptyDecl : DeclFn Nat := fun s =>
  if s.members.isEmpty then .ok s else refDeclFusion mod060_ty s

/-- A declaration check that rejects a set with fewer than two members as malformed and is the
reference otherwise. -/
def rejectSingletonDecl : DeclFn Nat := fun s =>
  if s.members.length < 2 then .error "a fusion set needs at least two members"
  else refDeclFusion mod060_ty s

/-- A declaration check that keeps the members in reverse order. -/
def reorderDecl : DeclFn Nat := fun s =>
  (refDeclFusion mod060_ty s).map fun s' => { s' with members := s'.members.reverse }

/-- The mutant without line 1 is killed by the check that accepts an empty set: it meets the
other two lines, since a set with a member goes to the reference and a set with no member has
one token type, but it accepts the set `empty` with no member. -/
@[evidence mutant MOD_060]
theorem MOD_060_mutant_acceptEmpty_killed :
    MOD_060_mutant_acceptEmpty mod060_ty acceptEmptyDecl ∧
      ¬ MOD_060 mod060_ty acceptEmptyDecl := by
  have R := refDeclFusion_lines mod060_ty
  refine ⟨⟨fun s hne hty => ?_, fun s hty => ?_⟩, fun h => ?_⟩
  · have : s.members.isEmpty = false := by
      cases hs : s.members with
      | nil => exact absurd hs hne
      | cons _ _ => rfl
    simp only [acceptEmptyDecl, this]
    exact R.2.1 s hne hty
  · obtain ⟨n, ms⟩ := s
    cases ms with
    | nil => exact absurd (typesAgree_nil mod060_ty n) hty
    | cons a l => exact R.2.2 _ hty
  · obtain ⟨m, hm⟩ := h.1 "empty"
    cases hm

/-- The mutant without line 2 is killed by the check that rejects a set with fewer than two
members, the earlier SHOULD of AC4: it meets the other two lines, but rejects the set `one`
with the single member 3, which every runtime accepts. -/
@[evidence mutant MOD_060]
theorem MOD_060_mutant_rejectSingleton_killed :
    MOD_060_mutant_rejectSingleton mod060_ty rejectSingletonDecl ∧
      ¬ MOD_060 mod060_ty rejectSingletonDecl := by
  have R := refDeclFusion_lines mod060_ty
  refine ⟨⟨fun n => ⟨_, rfl⟩, fun s hty => ?_⟩, fun h => ?_⟩
  · unfold rejectSingletonDecl
    split
    · exact ⟨_, rfl⟩
    · exact R.2.2 s hty
  · have := h.2.1 ⟨"one", [3]⟩ (by simp) (by intro a ha b hb; simp at ha hb; simp [ha, hb])
    cases this

/-- The mutant without line 3 is killed by the check that compares no token type: it meets the
other two lines, but accepts the set `mixed` whose members 0 and 1 have two token types. -/
@[evidence mutant MOD_060]
theorem MOD_060_mutant_noTypeCheck_killed :
    MOD_060_mutant_noTypeCheck mod060_ty (refDeclFusion (fun _ : Nat => ())) ∧
      ¬ MOD_060 mod060_ty (refDeclFusion (fun _ : Nat => ())) := by
  have R := refDeclFusion_lines (N := Nat) (fun _ : Nat => ())
  refine ⟨⟨R.1, fun s hne _ => R.2.1 s hne (typesAgree_unit s)⟩, fun h => ?_⟩
  obtain ⟨m, hm⟩ := h.2.2 ⟨"mixed", [0, 1]⟩ (fun hty => by
    have := hty 0 (by simp) 1 (by simp)
    simp [mod060_ty] at this)
  cases hm

/-- ✗ A check that returns the members in another order violates MOD-060 (line 2): for the set
`permits` declared with members 0, 2 and 4 it returns 4, 2, 0, so the canonical member, the first
declared, would be 4 instead of 0. -/
@[evidence forbids MOD_060]
theorem MOD_060_forbids_reorder : ¬ MOD_060 mod060_ty reorderDecl := by
  intro h
  have := h.2.1 ⟨"permits", [0, 2, 4]⟩ (by simp)
    (by intro a ha b hb; simp at ha hb; rcases ha with rfl | rfl | rfl <;>
          rcases hb with rfl | rfl | rfl <;> rfl)
  cases this

/-! ### Joint with MOD-061: the declared sets are the ones fusion reads -/

/-- ✓ **The declaration and the fusion of a set fit together.** For every naming, token-type
reading and channel merge, there is one declaration check that meets MOD-060 and one fusion that
meets MOD-061, and the reference build script records a fusion set through that very check:
declaring `fuse s` adds `s` to the builder's fusion sets exactly when the check accepts it, and
fails with the check's message otherwise. So a set `{P, Q}` declared on the builder is fused at
`build()` as it was declared, `P` first. -/
@[evidence consistent MOD_060 MOD_061]
theorem MOD_060_joint {N A T : Type} [DecidableEq N] [ToString N] [DecidableEq T] [ToString T]
    (Nm : Naming N) (tyOf : N → T) (Mg : MergeFn N A) :
    ∃ (Dc : DeclFn N) (Fz : FuseFn N A),
      MOD_060 tyOf Dc ∧ MOD_061 refBuild Fz ∧
      ∀ (b : Bld N A) (s : FusionSet N),
        scriptStep Nm tyOf refBuild Mg b (.fuse s) =
          (Dc s).map fun s' => { b with fusions := b.fusions ++ [s'] } :=
  ⟨refDeclFusion tyOf, refFuse refBuild, MOD_060_reference tyOf, MOD_061_reference refBuild,
    fun _ _ => rfl⟩

end Libpetri.Spec
