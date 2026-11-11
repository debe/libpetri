import Libpetri.Spec.Registry
import Libpetri.Basic

set_option linter.missingDocs true

/-!
# EXP-006: Cardinality labels (`spec/09-export.md`)

The cardinality label an export gives an input arc. The requirement is a predicate over an
abstract cardinality labeller `L : Card → Option String` (`none`: no cardinality label), on the
existing `Libpetri.Card`. The witness `refCardLabel` sits beside the block, as `refReadyOrder`
does in EXEC-002: it is the function every runtime mapper computes (`input_label` in
the Rust crate `libpetri-export`, module `mapper`, the `card` switch in `PetriNetGraphMapper.java` and in
`petri-net-mapper.ts`).

Ruling D41 (a) pins the forms every runtime draws: `×n` for `Exactly(n)`, `*` for `All`, `≥m`
for `AtLeast(m)` and no cardinality label for `One`. The spec's earlier second forms (bare `n` and
`all`) are mutants of the block (`EXP_006_mutant_eitherForm_killed`). Drawing the label on the
edge of the arc is a separate sentence of the spec; it needs the export model and is EXP-018's
label lines, not this block's.
-/

namespace Libpetri.Spec

open Libpetri

/-! ## The witness: the label every runtime draws -/

/-- **The reference cardinality labeller** (witness model): no label for `One`, `×n` for
`Exactly(n)`, `*` for `All`, `≥m` for `AtLeast(m)`, the numbers in decimal. Rust `input_label`
(crate `libpetri-export`, module `mapper`), Java and TypeScript compute the same function. -/
def refCardLabel : Card → Option String
  | .one => none
  | .exactly n => some ("×" ++ toString n)
  | .all => some "*"
  | .atLeast m => some ("≥" ++ toString m)

#spec_witness refCardLabel

/-! ## EXP-006: Cardinality labels -/

requirement EXP_006
  id "EXP-006"
  title "Cardinality Labels"
  kind F
  scope "every exporter, on the input arcs of a net (the only arcs with a cardinality)"
  source verbatim "spec/09-export.md"
  quote "Multi-token arcs (Exactly(n), All, AtLeast(m)) display count notation on the arc label:"
        "Exactly(n): label shows \"×n\""
        "All: label shows \"*\""
        "AtLeast(m): label shows \"≥m\""
        "The export *shall* give an input arc with cardinality `One` no cardinality label."
        "The export *shall* give an input arc with cardinality `Exactly(n)` the cardinality label `×n`."
        "The export *shall* give an input arc with cardinality `All` the cardinality label `*`."
        "The export *shall* give an input arc with cardinality `AtLeast(m)` the cardinality label `≥m`."
  reading "For the cardinality labeller L of an export (none: no cardinality label):"
          "One has no cardinality label;"
          "for every count n of at least 1, Exactly(n) is labelled ×n;"
          "All is labelled *;"
          "for every minimum m, AtLeast(m) is labelled ≥m."
  assumes "The model is the cardinality labeller L : Card → Option String of an export: the cardinality label it gives an input arc, from the arc's cardinality alone, none for no cardinality label. Only input arcs have a cardinality (glossary: Input arc; the output specs of IO-011 to IO-014 carry none), so the opening sentence 'Multi-token arcs (Exactly(n), All, AtLeast(m)) display count notation on the arc label:', which names no arc kind, is read as input arcs, and the four shall sentences name input arcs to say so. Output, inhibitor, read and reset arcs are out of scope. Correlation (EXP-018, NU-020) plays no part in L: the ⟨n⟩ prefix is not a cardinality label."
          "Where the label is drawn is not encoded here. The sentence 'The export shall draw the cardinality label of an input arc on the edge of the arc.' needs the export model RefExport and is carried by EXP-018's label lines: the label of an uncorrelated input edge of an arc with cardinality c is refCardLabel c, and the label of a correlated one is ⟨n⟩, followed by a space and refCardLabel c when that is a label. The glossary agreement ExportAgrees ties the exporter's input labels to the labeller L of this block in the export consistency theorem. This block alone does not rule out an export that draws no label, or a label other than L's, on an input edge, nor a mapper that writes ⟨n⟩ alone on a correlated Exactly(2) edge (its uncorrelated labeller is the correct one); EXP-018 rejects both (EXP_018_forbids_replace)."
          "'×n' is read as the character × (U+00D7) followed by n in decimal, 'n' as n in decimal alone, '≥m' as ≥ (U+2265) followed by m in decimal, as every runtime writes them (Lean toString on Nat); an ASCII lookalike such as x3 or >=5 is a different label (EXP_006_forbids_ascii). 'No cardinality label' is none: some \"\" is a label, although DOT draws label=\"\" like no label; no runtime writes it (EXP_006_forbids_emptyOne)."
          "Line 2 ranges over counts of at least 1, since IO-002 defines Exactly(n) only for N >= 1 and its AC1 rejects N < 1, so no export labels Exactly(0). Line 4 has no such guard: IO-004 states no lower bound on the minimum (only the runtimes reject a minimum below 1), so the bullet 'AtLeast(m): label shows ≥m' is taken for every m, AtLeast(0) included; the reference labeller meets it, and a labeller that drops the label of AtLeast(0) violates the block (EXP_006_mutant_atLeastGuard_killed)."
          "Lines 2 and 3 are the forms ruling D41 (a) pins, the ones all three runtimes write (×n, *, ≥m). The spec once allowed a second form for each (bare n for Exactly(n), all for All); that reading is the mutant EXP_006_mutant_eitherForm, and a labeller with the bare forms meets it and violates the block (EXP_006_mutant_eitherForm_killed). A labeller that mixes the forms per value (bare 1 for Exactly(1), ×n for larger counts, all for All) violates line 2 at n = 1 (EXP_006_forbids_mixed)."
          "The opening sentence names Exactly(n) as a multi-token arc for every n; Exactly(1) moves one token and is still labelled, by AC1 ('Non-One cardinality is displayed on the arc') and by every runtime (×1). Line 2 therefore holds at n = 1, and the reading that labels only arcs moving more than one token is a mutant (EXP_006_mutant_multiOnly_killed)."
          "AC1 (non-One cardinality is displayed on the arc) is encoded in its label half by lines 2, 3 and 4: every buildable non-One cardinality has a cardinality label (EXP_006_labels_nonOne). Its 'on the arc' half is EXP-018's label lines (see above)."
          "AC2 (One cardinality has no cardinality label, by default) is line 1. The edge label is not modelled here, so this block does not rule out a One input edge drawn with some other label (for example 1); EXP-018's line 3 does, under which an uncorrelated One edge carries no label. EXP-018 labels a correlated One input edge ⟨n⟩, which is not a cardinality label, so it does not contradict AC2 (ruling D41 (a), clash exp-a#6, clashExport_corrOne). The word 'default' is read as 'the label of an uncorrelated One input edge'; no configuration option of EXP-007 changes the cardinality label in any runtime."
          "The test derivation (a net with Exactly(3) and AtLeast(5) inputs, labels show the counts) is EXP_006_nonvacuous on the reference labeller: ×3 and ≥5."
  signoff "pending"
  statement : (Card → Option String) → Prop :=
    fun L =>
      L .one = none ∧
      (∀ n, 0 < n → L (.exactly n) = some ("×" ++ toString n)) ∧
      L .all = some "*" ∧
      (∀ m, L (.atLeast m) = some ("≥" ++ toString m))

/- The pinned readable form of EXP-006: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EXP_006 : (Card → Option String) → Prop :=
fun L =>
  L Card.one = none ∧
    (∀ (n : Nat), 0 < n → L (Card.exactly n) = some ("×" ++ toString n)) ∧
      L Card.all = some "*" ∧ ∀ (m : Nat), L (Card.atLeast m) = some ("≥" ++ toString m)
-/
#guard_msgs in #print EXP_006

/-! ### The reference -/

/-- The reference labeller satisfies EXP-006. -/
@[evidence holds EXP_006]
theorem EXP_006_reference : EXP_006 refCardLabel :=
  ⟨rfl, fun _ _ => rfl, rfl, fun _ => rfl⟩

/-- AC1, label half, follows from the block: a labeller that satisfies it gives every buildable
non-One cardinality a label. -/
theorem EXP_006_labels_nonOne {L : Card → Option String} (h : EXP_006 L) :
    (∀ n, 0 < n → L (.exactly n) ≠ none) ∧ L .all ≠ none ∧ (∀ m, L (.atLeast m) ≠ none) := by
  obtain ⟨-, h2, h3, h4⟩ := h
  refine ⟨fun n hn => ?_, ?_, fun m => ?_⟩
  · simp [h2 n hn]
  · simp [h3]
  · simp [h4 m]

/-! ### Examples: wrong labellers, one per line -/

/-- A labeller that reads `One` as `Exactly(1)` and labels it `×1`. -/
def exp006_oneAsExactly : Card → Option String
  | .one => some "×1"
  | c => refCardLabel c

/-- ✗ Labelling `One` violates EXP-006 (line 1). -/
@[evidence forbids EXP_006]
theorem EXP_006_forbids_oneAsExactly : ¬ EXP_006 exp006_oneAsExactly := by
  intro h
  exact absurd h.1 (by decide)

/-- A labeller that writes the empty string for `One`: a label, although DOT draws it like
none. -/
def exp006_emptyOne : Card → Option String
  | .one => some ""
  | c => refCardLabel c

/-- ✗ An empty label on `One` violates EXP-006 (line 1): "no cardinality label" is `none`. -/
@[evidence forbids EXP_006]
theorem EXP_006_forbids_emptyOne : ¬ EXP_006 exp006_emptyOne := by
  intro h
  exact absurd h.1 (by decide)

/-- A labeller that labels only arcs moving more than one token: `Exactly(1)` gets no label. -/
def exp006_multiOnly : Card → Option String
  | .exactly 1 => none
  | c => refCardLabel c

/-- ✗ Leaving `Exactly(1)` unlabelled violates EXP-006 (line 2 at n = 1). -/
@[evidence forbids EXP_006]
theorem EXP_006_forbids_multiOnly : ¬ EXP_006 exp006_multiOnly := by
  intro h
  exact absurd (h.2.1 1 (by decide)) (by decide)

/-- Mutant reading of EXP-006 that takes "multi-token arcs" literally: line 2 only for counts
of at least 2. -/
def EXP_006_mutant_multiOnly (L : Card → Option String) : Prop :=
  L .one = none ∧
  (∀ n, 1 < n → L (.exactly n) = some ("×" ++ toString n)) ∧
  L .all = some "*" ∧
  (∀ m, L (.atLeast m) = some ("≥" ++ toString m))

/-- The multi-token-only labeller kills the mutant: it meets the literal reading but not
EXP-006, whose AC1 labels every non-One cardinality. -/
@[evidence mutant EXP_006]
theorem EXP_006_mutant_multiOnly_killed :
    EXP_006_mutant_multiOnly exp006_multiOnly ∧ ¬ EXP_006 exp006_multiOnly := by
  refine ⟨⟨rfl, fun n hn => ?_, rfl, fun _ => rfl⟩, EXP_006_forbids_multiOnly⟩
  have : n ≠ 1 := by omega
  match n, this with
  | 0, _ => omega
  | k + 2, _ => rfl

/-- A labeller written without Unicode: `x` for `×` and `>=` for `≥`. -/
def exp006_ascii : Card → Option String
  | .exactly n => some ("x" ++ toString n)
  | .atLeast m => some (">=" ++ toString m)
  | c => refCardLabel c

/-- ✗ ASCII lookalikes violate EXP-006 (line 2 at n = 3 and line 4 at m = 5). -/
@[evidence forbids EXP_006]
theorem EXP_006_forbids_ascii : ¬ EXP_006 exp006_ascii := by
  intro h
  exact absurd (h.2.1 3 (by decide)) (by decide)

/-- A labeller that draws `All` as `AtLeast(1)`, since both need one token and take them all. -/
def exp006_allAsAtLeast : Card → Option String
  | .all => some "≥1"
  | c => refCardLabel c

/-- ✗ Labelling `All` as `≥1` violates EXP-006 (line 3). -/
@[evidence forbids EXP_006]
theorem EXP_006_forbids_allAsAtLeast : ¬ EXP_006 exp006_allAsAtLeast := by
  intro h
  exact absurd h.2.2.1 (by decide)

/-- A labeller that writes the minimum of `AtLeast(m)` like an exact count, `×m`. -/
def exp006_atLeastAsExactly : Card → Option String
  | .atLeast m => some ("×" ++ toString m)
  | c => refCardLabel c

/-- ✗ Labelling `AtLeast(5)` as `×5` violates EXP-006 (line 4). -/
@[evidence forbids EXP_006]
theorem EXP_006_forbids_atLeastAsExactly : ¬ EXP_006 exp006_atLeastAsExactly := by
  intro h
  exact absurd (h.2.2.2 5) (by decide)

/-- A labeller that adds a unit to the count: `×3 tokens`, `≥5 tokens`. -/
def exp006_suffix : Card → Option String
  | .exactly n => some ("×" ++ toString n ++ " tokens")
  | .atLeast m => some ("≥" ++ toString m ++ " tokens")
  | c => refCardLabel c

/-- ✗ A unit after the count violates EXP-006 (line 4 at m = 5). -/
@[evidence forbids EXP_006]
theorem EXP_006_forbids_suffix : ¬ EXP_006 exp006_suffix := by
  intro h
  exact absurd (h.2.2.2 5) (by decide)

/-- A labeller that leaves `AtLeast(0)` unlabelled, as if no minimum below 1 existed. -/
def exp006_atLeastZeroBlank : Card → Option String
  | .atLeast 0 => none
  | c => refCardLabel c

/-- Mutant of EXP-006 with a guard the spec does not state: line 4 only for minimums of at
least 1. -/
def EXP_006_mutant_atLeastGuard (L : Card → Option String) : Prop :=
  L .one = none ∧
  (∀ n, 0 < n → L (.exactly n) = some ("×" ++ toString n)) ∧
  L .all = some "*" ∧
  (∀ m, 0 < m → L (.atLeast m) = some ("≥" ++ toString m))

/-- The labeller that drops `AtLeast(0)` meets the guarded mutant but not EXP-006, whose line 4
covers every minimum, as the bullet and IO-004 do. -/
@[evidence mutant EXP_006]
theorem EXP_006_mutant_atLeastGuard_killed :
    EXP_006_mutant_atLeastGuard exp006_atLeastZeroBlank ∧ ¬ EXP_006 exp006_atLeastZeroBlank := by
  refine ⟨⟨rfl, fun _ _ => rfl, rfl, fun m hm => ?_⟩, fun h => ?_⟩
  · match m, hm with
    | k + 1, _ => rfl
  · exact absurd (h.2.2.2 0) (by decide)

/-! ### The second forms of the earlier spec (ruling D41 (a)) -/

/-- A labeller with the second forms the spec allowed before ruling D41 (a): bare `n` for
`Exactly(n)` and `all` for `All`. -/
def exp006_bare : Card → Option String
  | .exactly n => some (toString n)
  | .all => some "all"
  | c => refCardLabel c

/-- ✗ The bare forms violate EXP-006 (line 2 at n = 2: `2` is not `×2`). -/
@[evidence forbids EXP_006]
theorem EXP_006_forbids_bare : ¬ EXP_006 exp006_bare := by
  intro h
  exact absurd (h.2.1 2 (by decide)) (by decide)

/-- Mutant of EXP-006 with the disjunctions of the earlier spec: `×n` or `n` for `Exactly(n)`,
`*` or `all` for `All`. -/
def EXP_006_mutant_eitherForm (L : Card → Option String) : Prop :=
  L .one = none ∧
  (∀ n, 0 < n →
    L (.exactly n) = some ("×" ++ toString n) ∨ L (.exactly n) = some (toString n)) ∧
  (L .all = some "*" ∨ L .all = some "all") ∧
  (∀ m, L (.atLeast m) = some ("≥" ++ toString m))

/-- The bare labeller kills the mutant: it meets the either-form reading but not EXP-006, whose
lines 2 and 3 are the pinned forms of ruling D41 (a). -/
@[evidence mutant EXP_006]
theorem EXP_006_mutant_eitherForm_killed :
    EXP_006_mutant_eitherForm exp006_bare ∧ ¬ EXP_006 exp006_bare :=
  ⟨⟨rfl, fun _ _ => Or.inr rfl, Or.inr rfl, fun _ => rfl⟩, EXP_006_forbids_bare⟩

/-- A labeller that mixes the forms: bare `1` for `Exactly(1)`, `×n` for larger counts, and
`all` for `All` next to `×n`. -/
def exp006_mixed : Card → Option String
  | .exactly 1 => some "1"
  | .all => some "all"
  | c => refCardLabel c

/-- ✗ Mixed forms violate EXP-006 (line 2 at n = 1, and line 3). -/
@[evidence forbids EXP_006]
theorem EXP_006_forbids_mixed : ¬ EXP_006 exp006_mixed := by
  intro h
  exact absurd (h.2.1 1 (by decide)) (by decide)

/-- A labeller that writes `all` for `All` and the pinned forms otherwise. -/
def exp006_allWord : Card → Option String
  | .all => some "all"
  | c => refCardLabel c

/-- ✗ `all` for `All` violates EXP-006 (line 3), although every other form is the pinned one. -/
@[evidence forbids EXP_006]
theorem EXP_006_forbids_allWord : ¬ EXP_006 exp006_allWord := by
  intro h
  exact absurd h.2.2.1 (by decide)

/-! ### Non-vacuity -/

/-- The test derivation on the reference labeller: `Exactly(3)` shows `×3`, `AtLeast(5)` shows
`≥5`, `All` shows `*` and `One` shows nothing; and the forms differ, so each line bites. -/
@[evidence nonvacuous EXP_006]
theorem EXP_006_nonvacuous :
    refCardLabel (.exactly 3) = some "×3" ∧ refCardLabel (.atLeast 5) = some "≥5" ∧
      refCardLabel .all = some "*" ∧ refCardLabel .one = none ∧
      refCardLabel (.exactly 1) = some "×1" := by
  decide

end Libpetri.Spec
