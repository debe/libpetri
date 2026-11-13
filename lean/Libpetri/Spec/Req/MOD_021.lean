import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryCompose
import Libpetri.Reference.ComposeMerge
import Libpetri.Spec.Text.MOD_021

set_option linter.missingDocs true

/-!
# MOD-021: Channel composition (`spec/11-modular-composition.md`)

MOD-021 has two blocks.

* `MOD_021_table` (kind F): the canonical input-arc merge table, over an abstract
  table `mg : Card → Card → Option Card` (two input-arc cardinalities on one place give the
  merged cardinality, or `none` for a rejection). The table is shared by channel composition
  (this ID) and fusion ([MOD-061]); [CORE-030] refers to it.
* `MOD_021` (kind B): the channel merge, over an abstract merge function `Mg : MergeFn N A` (the
  caller-side definition and the instance-side channel definition give the merged definition or
  a rejection message), the transition builder's check `Build`, the composition `sq` of two
  actions, the correspondence merge `cm` of [MOD-031] and the implementation's rendering `tstr`
  of a timing. Eleven lines: name and priority, input arcs merged by the table, inhibitor, read
  and reset arcs united, the output `And(caller, instance)`, the runtimes' timing rule (ruling
  D77 (a)), the caller's action first, the builder check, the timing rejection (naming the
  caller and both timings), the arc-type rejection (rule (d), set reading, naming an offending
  place and both sets), the rule (c) diagnostic, and acceptance.

The witness of the table block is the glossary's `mergeCard` (`Spec/GlossaryCompose.lean`), the
table every runtime implements. The block pins the table completely: every model of it is
`mergeCard` (`mod021_table_unique`), so the table is symmetric (`mod021_table_symm`, the
sentence "The table is symmetric") and a merged arc requires the sum of the two sides' counts,
or for two `atLeast` arcs the larger minimum, or for two `all` arcs is `all`
(`mod021_table_required`). Wrong tables are killed: one that
rejects everything, one that keeps the first side's arc, and one per line that meets a plausible
wrong reading of that line (rule (a) read literally, so `one` with `one` collapses to `one`; no
`all` row; `atLeast` minimums summed; an off-table pair merged instead of rejected).

The witness of the merge block is the reference merge `refMerge` (`Reference/ComposeMerge.lean`),
for every `Build`, `sq` and `cm`, with the reference's timing rendering `timingStr`. Its proof
goes through `mod021_mergeG`, the reference with the timing merge, the timing message, the
arc-type check and the seam name left open; the wrong merges that kill lines 8 to 10 change one
of those parts, and the wrong merges that kill lines 1 to 6 rewrite one field of
every success (`mod021_post`). Three consequences hold for every model: a success has the merged
shape (`mod021_ok_shaped`), a merge the builder cannot accept fails (`mod021_buildFails`), and a
sole off-table pair is the one the diagnostic names (`mod021_offTable_sole`).
-/

namespace Libpetri.Spec

open Libpetri

/-! ## The table's vocabulary -/

/-- The fixed number of tokens an input arc draws: `one` draws 1, `exactly n` draws `n`; `all`
and `atLeast` have no fixed draw. The summing rows of the merge table are the pairs where both
sides have one. -/
def mod021_draw : Card → Option Nat
  | .one => some 1
  | .exactly n => some n
  | _ => none

/-- The pairs the canonical input-arc merge table lists: both sides `one` or `exactly`, both
`all`, or both `atLeast`. Every other pair is "anything else" (rule (c)). -/
def mod021_listed : Card → Card → Bool
  | .one, .one | .one, .exactly _ | .exactly _, .one | .exactly _, .exactly _ => true
  | .all, .all => true
  | .atLeast _, .atLeast _ => true
  | _, _ => false

/-! ## MOD-021, the input-arc merge table -/

requirement MOD_021_table
  id "MOD-021"
  title "Channel Composition, the input-arc merge table"
  kind F
  scope "the input-arc merge table of every implementation, used by channel composition and by fusion (MOD-061)"
  source verbatim "spec/11-modular-composition.md"
  covers MOD_021.s8, MOD_021.s9, MOD_021.s10, MOD_021.s11
  reading "For every merge table mg (two input-arc cardinalities on one place give the merged cardinality, or none for a rejection):"
          "if each side draws a fixed count (one draws 1, exactly n draws n), mg merges them to exactly of the sum: one with one gives exactly 2, one with exactly n (either order) gives exactly (n + 1), exactly n with exactly m gives exactly (n + m);"
          "mg merges all with all to all;"
          "mg merges atLeast n with atLeast m to atLeast (max n m);"
          "mg rejects (none) every pair the table does not list (mod021_listed: not both one or exactly, not both all, not both atLeast), for example one with all, exactly 2 with atLeast 2, all with atLeast 1."
  assumes "A merge table is read as a function on the cardinalities of two input arcs that meet on one place (Card, Basic.lean: one, exactly n, all, atLeast n), giving the merged cardinality or a rejection. Only the cardinality is stated; the place of the merged arc, its slot among the transition's arcs, a guard on either side and the case of more than two arcs on one place (the runtimes fold the arcs left to right, first-seen slot) are the merge block's (MOD_021, kind B) and MOD-061's. All three runtimes implement exactly this table: Rust merge_in_pair (rust/libpetri-core/src/rewriter.rs), Java mergeInPair (java/src/main/java/org/libpetri/core/internal/SubnetRewriter.java), TypeScript mergeInPair with summableCount (typescript/src/core/internal/subnet-rewriter.ts); Python uses the Rust code. The witness mergeCard (Spec/GlossaryCompose.lean) is that table."
          "Counts are unbounded naturals. A sum past a machine integer (Java int, Rust usize) is out of scope, and so is a count the arc builder rejects (exactly 0, atLeast 0): the merged arc is rebuilt through the transition builder, whose checks are CORE-030's and IO-002's, and that rebuild is the merge block's line."
          "The table is complete: every model of the block is mergeCard (mod021_table_unique). So 'The table is symmetric' holds of every model (mod021_table_symm) and needs no line of its own, and the explanatory sentence on why one and exactly sum while atLeast keeps the stricter minimum is mod021_table_required: a merged arc requires the sum of the two sides' required counts, or for two atLeast arcs the larger one, or for two all arcs is all."
          "Rule (a) as first written ('Same arc type with same cardinality/weight: collapse to a single arc') would merge one with one to one, against the table, AC6 and every runtime (clash mod-b#3). Under ruling D20 (MB-6) rule (a) is reworded to cover read, inhibitor and reset arcs only, leaving input arcs to the table. The literal reading is the mutant MOD_021_table_mutant_ruleA, killed by mod021_collapse (equal cardinalities collapse, the table otherwise)."
          "Line 1 kills mod021_firstWins (keeps the first side's arc) and MOD_021_table_mutant_ruleA; line 2 kills MOD_021_table_mutant_noAllRow (two all arcs read as a conflict); line 3 kills MOD_021_table_mutant_atLeastSummed (atLeast minimums summed, AC6's 'not AtLeast(4)'); line 4 kills MOD_021_table_mutant_rowsOnly (an off-table pair merged to atLeast of the summed requirements instead of rejected). A table that rejects everything violates line 1 (MOD_021_table_forbids_rejectAll)."
          "AC6 (One with One gives a single Exactly(2) arc, All with All gives All, AtLeast(1) with AtLeast(3) gives AtLeast(3), not AtLeast(4)) is lines 1 to 3 on those rows (MOD_021_table_nonvacuous, by decide); that the merged transition carries a single input arc on the place is the merge block's line. AC8 (One with All rejected) is line 4 on that pair (MOD_021_table_nonvacuous); the shape of the rejection message (seam, both cardinalities, place) is the merge block's line for channel composition and MOD-061's for fusion, each with a sole-offender premise (composition design, skeptic correction S3)."
          "AC1 (arc union), AC2 (disjoint timings rejected), AC3 (overlapping timings), AC4 (the action order), AC5 (one firing per fire) and AC7 (different arc types rejected) are the merge block's (MOD_021, kind B, composition wave W8, over refMerge). AC9 (token timestamp and FIFO order of tokens produced by merged firings) is CONC-003 and EXEC-020 under ruling D48 (a), which rewords AC9 to cite them; its one TokenAdded event per produced token is EVT-011's."
  signoff "2026-11-13 f528a237be1afc84 ai"
  statement : (Card → Card → Option Card) → Prop :=
    fun mg =>
      (∀ a b n m, mod021_draw a = some n → mod021_draw b = some m →
        mg a b = some (.exactly (n + m))) ∧
      mg .all .all = some .all ∧
      (∀ n m, mg (.atLeast n) (.atLeast m) = some (.atLeast (max n m))) ∧
      (∀ a b, mod021_listed a b = false → mg a b = none)

/- The pinned readable form of the MOD-021 table block: a change to the formula shows up as a
diff here. -/
/--
info: def Libpetri.Spec.MOD_021_table : (Card → Card → Option Card) → Prop :=
fun mg =>
  (∀ (a b : Card) (n m : ℕ), mod021_draw a = some n → mod021_draw b = some m → mg a b = some (Card.exactly (n + m))) ∧
    mg Card.all Card.all = some Card.all ∧
      (∀ (n m : ℕ), mg (Card.atLeast n) (Card.atLeast m) = some (Card.atLeast (max n m))) ∧
        ∀ (a b : Card), mod021_listed a b = false → mg a b = none
-/
#guard_msgs in #print MOD_021_table

/-! ### The four lines, named (for the mutants) -/

section Lines

/-- Line 1 of the table block: two fixed draws merge to `exactly` of their sum. -/
def mod021_line1 (mg : Card → Card → Option Card) : Prop :=
  ∀ a b n m, mod021_draw a = some n → mod021_draw b = some m → mg a b = some (.exactly (n + m))

/-- Line 2 of the table block: `all` with `all` merges to `all`. -/
def mod021_line2 (mg : Card → Card → Option Card) : Prop :=
  mg .all .all = some .all

/-- Line 3 of the table block: `atLeast` with `atLeast` keeps the larger minimum. -/
def mod021_line3 (mg : Card → Card → Option Card) : Prop :=
  ∀ n m, mg (.atLeast n) (.atLeast m) = some (.atLeast (max n m))

/-- Line 4 of the table block: every pair the table does not list is rejected. -/
def mod021_line4 (mg : Card → Card → Option Card) : Prop :=
  ∀ a b, mod021_listed a b = false → mg a b = none

/-- The table block is its four lines. -/
theorem mod021_table_iff (mg : Card → Card → Option Card) :
    MOD_021_table mg ↔ mod021_line1 mg ∧ mod021_line2 mg ∧ mod021_line3 mg ∧ mod021_line4 mg :=
  Iff.rfl

end Lines

/-! ### The reference -/

#spec_witness mergeCard

/-- ✓ The glossary's merge table satisfies the block: `one` with `one` gives `exactly(2)`,
`one` with `exactly(3)` gives `exactly(4)`, `exactly(2)` with `exactly(3)` gives `exactly(5)`,
`all` with `all` gives `all`, `atLeast(1)` with `atLeast(3)` gives `atLeast(3)`, and every other
pair, such as `one` with `all`, is rejected. -/
@[evidence holds MOD_021_table]
theorem MOD_021_table_reference : MOD_021_table mergeCard := by
  refine ⟨fun a b n m ha hb => ?_, rfl, fun n m => rfl, fun a b h => ?_⟩
  · cases a <;> cases b <;> simp [mod021_draw] at ha hb <;> subst ha hb <;>
      simp [mergeCard, Nat.add_comm]
  · cases a <;> cases b <;> simp [mod021_listed] at h <;> rfl

/-! ### Consequences for every model of the block -/

section Consequences

/-- **The table is complete.** Every model of the block is the glossary's `mergeCard`: the four
lines fix the merged cardinality, or the rejection, of every pair of input arcs. -/
theorem mod021_table_unique {mg : Card → Card → Option Card} (h : MOD_021_table mg) :
    mg = mergeCard := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  funext a b
  cases a <;> cases b <;>
    first
    | exact (h1 _ _ _ _ rfl rfl).trans (by simp [mergeCard, Nat.add_comm])
    | exact h2
    | exact h3 _ _
    | exact (h4 _ _ rfl).trans rfl

/-- **"The table is symmetric."** In every model of the block, merging `a` with `b` gives what
merging `b` with `a` gives: `one` with `exactly(3)` and `exactly(3)` with `one` both give
`exactly(4)`. -/
theorem mod021_table_symm {mg : Card → Card → Option Card} (h : MOD_021_table mg)
    (a b : Card) : mg a b = mg b a := by
  rw [mod021_table_unique h]
  exact mergeCard_comm a b

/-- **Why the rows are what they are.** In every model of the block, a merged arc requires the
sum of the two sides' required counts, or, for two `atLeast` arcs, the larger of the two, or, for
two `all` arcs, is `all` again: `one` with `exactly(2)` requires 3 tokens, `atLeast(1)` with
`atLeast(3)` requires 3, and `all` with `all` gives `all`. -/
theorem mod021_table_required {mg : Card → Card → Option Card} (h : MOD_021_table mg)
    {a b c : Card} (hc : mg a b = some c) :
    c.required = a.required + b.required ∨
      (∃ n m, a = .atLeast n ∧ b = .atLeast m ∧ c.required = max n m) ∨
      (a = .all ∧ b = .all ∧ c = .all) := by
  rw [mod021_table_unique h] at hc
  cases a <;> cases b <;> simp [mergeCard] at hc <;> subst hc <;> simp [Card.required, Nat.add_comm]

end Consequences

/-! ### Examples -/

/-- ✓ The rows the acceptance criteria name, on the reference table: `one` with `one` gives
`exactly(2)` (AC6), `all` with `all` gives `all` (AC6), `atLeast(1)` with `atLeast(3)` gives
`atLeast(3)` and not `atLeast(4)` (AC6), `one` with `exactly(3)` gives `exactly(4)` in either
order, and `one` with `all` is rejected (AC8). -/
@[evidence nonvacuous MOD_021_table]
theorem MOD_021_table_nonvacuous :
    mergeCard .one .one = some (.exactly 2) ∧
    mergeCard .all .all = some .all ∧
    mergeCard (.atLeast 1) (.atLeast 3) = some (.atLeast 3) ∧
    mergeCard (.atLeast 1) (.atLeast 3) ≠ some (.atLeast 4) ∧
    mergeCard .one (.exactly 3) = some (.exactly 4) ∧
    mergeCard (.exactly 3) .one = some (.exactly 4) ∧
    mergeCard .one .all = none := by
  decide

/-! ### Wrong tables -/

/-- A table that rejects every pair. -/
def mod021_rejectAll : Card → Card → Option Card := fun _ _ => none

/-- A table that keeps the first side's arc, as a union of arcs deduplicated by place would. -/
def mod021_firstWins : Card → Card → Option Card := fun a _ => some a

/-- ✗ A table that rejects every pair violates the block (line 1): `one` with `one` must merge to
`exactly(2)`, and it is rejected. -/
@[evidence forbids MOD_021_table]
theorem MOD_021_table_forbids_rejectAll : ¬ MOD_021_table mod021_rejectAll := by
  intro h
  have := h.1 .one .one 1 1 rfl rfl
  simp [mod021_rejectAll] at this

/-- ✗ A table that keeps the first side's arc violates the block (line 1): `one` with `one`
gives `one`, where the table gives `exactly(2)`. -/
@[evidence forbids MOD_021_table]
theorem MOD_021_table_forbids_firstWins : ¬ MOD_021_table mod021_firstWins := by
  intro h
  have := h.1 .one .one 1 1 rfl rfl
  simp [mod021_firstWins] at this

/-! ### Mutants, one per line -/

/-- Rule (a) read literally: two arcs with the same cardinality collapse to that cardinality, and
the table decides the rest. -/
def mod021_collapse (a b : Card) : Option Card := if a = b then some a else mergeCard a b

/-- **Mutant of line 1:** rule (a) read literally (equal cardinalities collapse) in place of line
1, lines 2 to 4 kept. -/
def MOD_021_table_mutant_ruleA (mg : Card → Card → Option Card) : Prop :=
  (∀ c, mg c c = some c) ∧ mod021_line2 mg ∧ mod021_line3 mg ∧ mod021_line4 mg

/-- ✗ The literal rule (a) collapses `one` with `one` to `one`: it meets the mutant (equal
cardinalities collapse, `all`, `atLeast` and the rejections as the table says) and violates line
1, which gives `exactly(2)`. -/
@[evidence mutant MOD_021_table]
theorem MOD_021_table_mutant_ruleA_killed :
    MOD_021_table_mutant_ruleA mod021_collapse ∧ ¬ MOD_021_table mod021_collapse := by
  refine ⟨⟨fun c => by simp [mod021_collapse], rfl, fun n m => ?_, fun a b h => ?_⟩, fun h => ?_⟩
  · by_cases hnm : n = m
    · subst hnm; simp [mod021_collapse]
    · simp [mod021_collapse, hnm, mergeCard]
  · have hne : a ≠ b := by
      rintro rfl; cases a <;> simp [mod021_listed] at h
    simp only [mod021_collapse, hne, if_false]
    exact MOD_021_table_reference.2.2.2 a b h
  · have := h.1 .one .one 1 1 rfl rfl
    simp [mod021_collapse] at this

/-- A table without the `all` row: two `all` arcs are read as a conflict (each drains the place),
the table otherwise. -/
def mod021_noAllRow : Card → Card → Option Card
  | .all, .all => none
  | a, b => mergeCard a b

/-- **Mutant of line 2:** the `all` row dropped and `all` with `all` rejected, lines 1, 3 and 4
kept. -/
def MOD_021_table_mutant_noAllRow (mg : Card → Card → Option Card) : Prop :=
  mod021_line1 mg ∧ mg .all .all = none ∧ mod021_line3 mg ∧ mod021_line4 mg

/-- ✗ A table that rejects `all` with `all` meets the mutant and violates line 2, which merges
the two to `all` (AC6). -/
@[evidence mutant MOD_021_table]
theorem MOD_021_table_mutant_noAllRow_killed :
    MOD_021_table_mutant_noAllRow mod021_noAllRow ∧ ¬ MOD_021_table mod021_noAllRow := by
  refine ⟨⟨fun a b n m ha hb => ?_, rfl, fun n m => rfl, fun a b h => ?_⟩, fun h => ?_⟩
  · cases a <;> cases b <;> simp [mod021_draw] at ha hb <;> subst ha hb <;>
      simp [mod021_noAllRow, mergeCard, Nat.add_comm]
  · cases a <;> cases b <;> simp [mod021_listed] at h <;> rfl
  · exact absurd h.2.1 (by simp [mod021_noAllRow])

/-- A table that sums `atLeast` minimums, as it sums `exactly` counts. -/
def mod021_atLeastSummed : Card → Card → Option Card
  | .atLeast n, .atLeast m => some (.atLeast (n + m))
  | a, b => mergeCard a b

/-- **Mutant of line 3:** `atLeast` minimums summed in place of the larger one, lines 1, 2 and 4
kept. -/
def MOD_021_table_mutant_atLeastSummed (mg : Card → Card → Option Card) : Prop :=
  mod021_line1 mg ∧ mod021_line2 mg ∧
    (∀ n m, mg (.atLeast n) (.atLeast m) = some (.atLeast (n + m))) ∧ mod021_line4 mg

/-- ✗ A table that sums `atLeast` minimums merges `atLeast(1)` with `atLeast(3)` to `atLeast(4)`:
it meets the mutant and violates line 3, which gives `atLeast(3)` (AC6, "not `AtLeast(4)`"). -/
@[evidence mutant MOD_021_table]
theorem MOD_021_table_mutant_atLeastSummed_killed :
    MOD_021_table_mutant_atLeastSummed mod021_atLeastSummed ∧
      ¬ MOD_021_table mod021_atLeastSummed := by
  refine ⟨⟨fun a b n m ha hb => ?_, rfl, fun n m => rfl, fun a b h => ?_⟩, fun h => ?_⟩
  · cases a <;> cases b <;> simp [mod021_draw] at ha hb <;> subst ha hb <;>
      simp [mod021_atLeastSummed, mergeCard, Nat.add_comm]
  · cases a <;> cases b <;> simp [mod021_listed] at h <;> rfl
  · have := h.2.2.1 1 3
    simp [mod021_atLeastSummed] at this

/-- A table that merges every off-table pair instead of rejecting it, to `atLeast` of the two
sides' summed requirements (both sides draw, so at least their sum). -/
def mod021_mergeAll (a b : Card) : Option Card :=
  match mergeCard a b with
  | some c => some c
  | none => some (.atLeast (a.required + b.required))

/-- **Mutant of line 4:** the rows of the table only, with nothing said of the other pairs. -/
def MOD_021_table_mutant_rowsOnly (mg : Card → Card → Option Card) : Prop :=
  mod021_line1 mg ∧ mod021_line2 mg ∧ mod021_line3 mg

/-- ✗ A table that merges `one` with `all` to `atLeast(2)` meets every row and violates line 4,
which rejects the pair (AC8). -/
@[evidence mutant MOD_021_table]
theorem MOD_021_table_mutant_rowsOnly_killed :
    MOD_021_table_mutant_rowsOnly mod021_mergeAll ∧ ¬ MOD_021_table mod021_mergeAll := by
  refine ⟨⟨fun a b n m ha hb => ?_, rfl, fun n m => rfl⟩, fun h => ?_⟩
  · cases a <;> cases b <;> simp [mod021_draw] at ha hb <;> subst ha hb <;>
      simp [mod021_mergeAll, mergeCard, Nat.add_comm]
  · have := h.2.2.2 .one .all rfl
    simp [mod021_mergeAll, mergeCard] at this

/-! ## MOD-021, the channel merge (kind B) -/

section MergeVocab

open Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Novel.TimedScg (Timing)

variable {N A : Type}

/-- Neither ... nor: the definition `d` has at most one input arc on each place (every built
transition, [CORE-030]). -/
def mod021_inOnce (d : CDef N A) : Prop := (d.core.inputs.map (·.place)).Nodup

/-- A character Java's `Character.isWhitespace` accepts: tab to carriage return, the four
information separators U+001C to U+001F, the space, and the Unicode space, line and paragraph
separators other than the no-break spaces U+00A0, U+2007 and U+202F. -/
def mod021_javaSpace (ch : Char) : Bool :=
  let n := ch.toNat
  (0x09 ≤ n && n ≤ 0x0D) || (0x1C ≤ n && n ≤ 0x20) || n == 0x1680 ||
    (0x2000 ≤ n && n ≤ 0x200A && n != 0x2007) || n == 0x2028 || n == 0x2029 || n == 0x205F ||
    n == 0x3000

/-- **A named caller**: the name of `c` has a character that is not white space. Rust and
TypeScript refuse to merge under an empty name, Java under a blank one
(`String.isBlank`, which is `Character.isWhitespace` on every character). -/
def mod021_named (c : CDef N A) : Prop := ∃ ch ∈ c.core.name.toList, mod021_javaSpace ch = false

/-- The seam of a channel-merge diagnostic: `Channel composition '<name>'`. -/
def mod021_seam (name : String) : String := "Channel composition '" ++ name ++ "'"

/-- A cardinality as Rust and Python spell it in a diagnostic: `at_least(n)` for `atLeast`. -/
def mod021_cardSnake : Card → String
  | .one => "one()"
  | .exactly n => s!"exactly({n})"
  | .all => "all()"
  | .atLeast n => s!"at_least({n})"

variable [ToString N]

/-- The [MOD-021] rule (c) diagnostic of a channel merge, as Java and TypeScript spell it
(`atLeast(n)`): the seam with the caller-side name, both cardinalities and the place. -/
def mod021_offTableMsg (name : String) (col : Collision N) : String :=
  s!"{mod021_seam name}: input arcs {cardStr col.left} and {cardStr col.right} collide on place '{col.place}' and have no additive merge (MOD-021 rule (c)). Use a single arc with exactly(n) / atLeast(n)."

/-- The same diagnostic as Rust and Python spell it (`at_least(n)`, `merge_transitions` in `rewriter.rs`). -/
def mod021_offTableMsgSnake (name : String) (col : Collision N) : String :=
  s!"{mod021_seam name}: input arcs {mod021_cardSnake col.left} and {mod021_cardSnake col.right} collide on place '{col.place}' and have no additive merge (MOD-021 rule (c)). Use a single arc with exactly(n) / at_least(n)."

variable [DecidableEq N]

/-- **The input arcs merged by the table**: `d` has at most one input arc per place, and on each
place the one side's arc where only one side has one, the table's merge where both have one. -/
def mod021_inputsMerged (c i d : CDef N A) : Prop :=
  mod021_inOnce d ∧
    ∀ p, cardAt d.core.inputs p = mergeAt (cardAt c.core.inputs p) (cardAt i.core.inputs p)

/-- `zs` holds each place of `xs` or `ys` once, and nothing else. -/
def mod021_union (xs ys zs : List N) : Prop := zs.Nodup ∧ ∀ p, p ∈ zs ↔ p ∈ xs ∨ p ∈ ys

/-- **The inhibitor, read and reset arcs united**, type by type (rule (a)). -/
def mod021_arcsUnion (c i d : CDef N A) : Prop :=
  mod021_union c.core.inhibitors i.core.inhibitors d.core.inhibitors ∧
    mod021_union c.core.reads i.core.reads d.core.reads ∧
    mod021_union c.core.resets i.core.resets d.core.resets

/-- **A definition of the merged shape**: what lines 1 to 6 of the merge block allow as the merge
of `c` and `i` (name, priority, input arcs, inhibitor, read and reset arcs, output, timing,
action). -/
def mod021_shaped (sq : Act A → Act A → Act A) (c i d : CDef N A) : Prop :=
  d.core.name = c.core.name ∧ d.priority = c.priority ∧ mod021_inputsMerged c i d ∧
    mod021_arcsUnion c i d ∧ d.out = mergeOut c.out i.out ∧
    rtMergeTiming c.timing i.timing = some d.timing ∧ d.action = sq c.action i.action

end MergeVocab

open Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Novel.TimedScg (Timing)

/- The reference's rendering of a timing in the timing message is the witness for the block's
rendering parameter. -/
#spec_witness timingStr

requirement MOD_021
  id "MOD-021"
  title "Channel Composition, the transition merge"
  kind B
  scope "channel composition in every implementation: the merge of a caller-side transition with the instance-side channel transition it is bound to"
  source verbatim "spec/11-modular-composition.md"
  covers MOD_021.s13, MOD_021.s14, MOD_021.s3, MOD_021.s15, MOD_021.s16, MOD_021.s4, MOD_021.s17,
        MOD_021.s5, MOD_021.s18, MOD_021.s19, MOD_021.s20, MOD_021.s1, MOD_021.s2, MOD_021.s21,
        MOD_021.s22, MOD_021.s7, MOD_021.s23, MOD_021.s24, MOD_021.s6, MOD_021.s12, MOD_021.s25,
        MOD_021.s26
  reading "For every transition-builder check Build, every sequential composition sq of two actions, every correspondence merge cm (MOD-031), every rendering tstr of a timing as a text (the implementation's own in its messages) and every channel merge Mg (the caller-side definition c and the instance-side channel definition i give the merged definition or a rejection message):"
          "line 1: if Mg c i succeeds with d, d has c's name and c's priority;"
          "line 2: if neither c nor i has two input arcs on one place and Mg c i succeeds with d, then d has at most one input arc on each place, and on each place p the cardinality mergeAt gives for c's and i's arcs on p: none where neither has one, the one side's where only one has one, mergeCard of the two (the table block's) where both have one;"
          "line 3: if Mg c i succeeds with d, then for each of the inhibitor, read and reset arcs d has, once each, exactly the places on which c or i has an arc of that type;"
          "line 4: if Mg c i succeeds with d, d's output specification is mergeOut of c's and i's: And(c's, i's) when both have one, the one side's when only one has one, none when neither has one;"
          "line 5: if Mg c i succeeds with d, the timings of c and i merge by rtMergeTiming to d's timing (Immediate yields to the other side, two equal timings collapse);"
          "line 6: if Mg c i succeeds with d, d's action is sq of c's action and i's action, in that order;"
          "line 7: if Mg c i succeeds with d, Build accepts d;"
          "line 8: if c is named (mod021_named: its name has a character that is not white space) and the timings of c and i have no merge (neither is Immediate and they differ), Mg c i fails with a message that contains c's name and, when the two sides' sets of arc types agree on every place both have an input, inhibitor, read or reset arc on (KindsAgree), also tstr of c's timing and tstr of i's timing;"
          "line 9: if c and i have different sets of arc types (input, inhibitor, read, reset) on some place on which both have such an arc (not KindsAgree), Mg c i fails; if moreover c is named, the timings merge and cm c i succeeds, the message contains c's name and, for some such place p, p and c's and i's sets of arc types on p written as sorted lists such as [input] and [read, reset];"
          "line 10: if c is named, neither side has two input arcs on one place, the timings merge, cm c i succeeds, the arc types agree, and some place carries an input arc a of c and an input arc b of i with no merge in the table, then Mg c i fails with the rule (c) diagnostic for some such place p and its pair a, b (caller-side arc first), with seam Channel composition '<c's name>', spelled with atLeast(n) as Java and TypeScript do or with at_least(n) as Rust and Python do;"
          "line 11: if c is named, neither side has two input arcs on one place, the timings merge, cm c i succeeds, the arc types agree, every place where both have an input arc has a merge in the table, and Build accepts every definition of the shape lines 1 to 6 describe (mod021_shaped), Mg c i succeeds."
  assumes "Model scope. A merge function takes the caller-side definition c and the instance-side channel definition i (CDef: name, input, inhibitor, read and reset arcs, output specification, timing, priority, action and the declared-place correspondence of MOD-031) and gives the merged definition or a rejection message, as Rust merge_transitions (rust/libpetri-core/src/rewriter.rs), Java SubnetRewriter.mergeTransitions (java/src/main/java/org/libpetri/core/internal/SubnetRewriter.java) and TypeScript mergeTransitions (typescript/src/core/internal/subnet-rewriter.ts) do; Python uses the Rust code. The witness is refMerge (Reference/ComposeMerge.lean) with the reference's timing rendering timingStr, and the block holds for every Build, sq and cm (MOD_021_reference). Rewriting i through the port bindings before the merge, putting the merged definition into the composed net and not adding the instance-side channel transition separately (clause 5) are MOD-020's (refCompose, Reference/ComposeBind.lean). The merged definition's declared-place correspondence is MOD-031's and no line here constrains it."
          "Ruling D42 (m), clash mod-b#8: the caller-side transition is assumed not to be in the builder already and to have no arc on a port bound in the same compose call; the markdown now scopes the sentences to that case. Java and TypeScript then have nothing to replace and Rust has nothing to rewrite, so the three runtimes merge the same two definitions. Outside that case they differ (Java and TypeScript replace a caller already in the builder, Rust keeps it beside the merged one; Rust rewrites the caller's arcs through the port map, Java and TypeScript do not), and the outcome there is an open item of D42. The caller-side name: every runtime refuses a merge under an empty merged name, which is the caller-side name, before any other check (Rust assert!(!merged_name.is_empty()) in merge_transitions, rust/libpetri-core/src/rewriter.rs, a panic whose message names neither timing; TypeScript mergedName.length === 0 in mergeTransitions, typescript/src/core/internal/subnet-rewriter.ts; Java mergedName.isBlank() in SubnetRewriter.mergeTransitions, java/src/main/java/org/libpetri/core/internal/SubnetRewriter.java, which also refuses a name of white space only), while no transition builder refuses such a name (CORE-020). The markdown therefore scopes the sentences to a caller-side transition whose name is neither empty nor white space only, and lines 8 to 11, whose messages and acceptance that refusal would break, carry the premise mod021_named c (some character of the name is not white space in the sense of Java's Character.isWhitespace, mod021_javaSpace). Lines 1 to 7 speak only of a success and need no premise; the first half of line 9 holds for every name, since the refusal is a failure. A merge under a name of white space only is outside the sentences: Java refuses it and Rust and TypeScript merge it. The example merge with that refusal in front, mod021_emptyGuard, meets the block (mod021_emptyGuard_holds). Where the merged transition sits in declaration order (Rust: the slot of the channel transition; Java and TypeScript: before the surviving instance transitions) is not stated, and neither is the firing order that slot breaks ties in (EXEC-002)."
          "Ruling D77 (a), clashes mod-b#1 and mod-b#2: the merged timing follows the rule all three runtimes share (rtMergeTiming: Immediate yields to the other side, two equal timings collapse, every other pair is rejected; merge_timings in rust/libpetri-core/src/rewriter.rs, SubnetRewriter.mergeTimings in java/src/main/java/org/libpetri/core/internal/SubnetRewriter.java, mergeTimings in typescript/src/core/internal/subnet-rewriter.ts), not the intersection of firing intervals the markdown stated before; clause 2, AC2, AC3 and the test derivation are reworded to it. The interval rule is the wrong model of MOD_021_forbids_intervalTiming: it merges Deadline(100) with Delayed(50) to Window(50, 100), which every runtime rejects. The merged timing is always one of the two sides' timings (rtMergeTiming_side), so it is valid when both are (rtMergeTiming_valid, TIME-001) and it is reaped exactly when one of the sides is (rtMergeTiming_reapable, TIME-006). Java's deprecated Unconstrained timing (Timing.Unconstrained in java/src/main/java/org/libpetri/core/Timing.java) is not Immediate to mergeTimings, so Unconstrained with Delayed(50) is rejected; it is out of scope here as in TIME-001."
          "Actions. sq stands for the runtimes' composed action, which runs the caller-side action and then the instance-side action against one context within one firing (compose_actions and SequentialAction in rust/libpetri-core/src/rewriter.rs, SubnetRewriter.composeActions in java/src/main/java/org/libpetri/core/internal/SubnetRewriter.java, composeActions in typescript/src/core/internal/subnet-rewriter.ts). Line 6 pins the merged action to sq applied to the two sides' actions in that order; at a non-commutative sq such as list append the instance-first order is killed (MOD_021_mutant_instanceActionFirst_killed). That the composed action runs within one firing, as clause 4 and AC4 say, is not a line: one merged definition is one transition, and its firing is EXEC-001's and CORE-021's. The witness sq is seqAct f, which also drops the built-in passthrough on either side, an elision nothing can observe. Priority: no runtime offers an override (pick_priority, pickPriority return the caller's), so clause 3 is reworded to the caller's priority without the former MAY, and line 1 states it."
          "Input arcs. Line 2 and lines 10 and 11 assume that neither side has two input arcs on one place, which every built transition satisfies (CORE-030). On each place the table decides (MOD_021_table, every model of which is mergeCard). The position of a merged arc among the input arcs (the runtimes fold the caller's arcs and then the instance's, keeping the first-seen position: merge_input_arcs in rewriter.rs, SubnetRewriter.mergeInputArcs, normalizeInputArcs in subnet-rewriter.ts) is not normative (ruling D32) and not stated. Line 10's diagnostic names a real offending pair, the caller-side arc first, which is what that fold reports in all three runtimes; with one offending place the pair is fixed (mod021_offTable_sole)."
          "Other arcs and the output. Line 3 compares the inhibitor, read and reset arcs as sets without repetition: the runtimes unite them caller first, keeping the first occurrence (union_arcs in rewriter.rs, SubnetRewriter.unionArcs, unionArcs in subnet-rewriter.ts), and that order is not stated. Rule (a), reworded under ruling D20 (clash mod-b#3), covers these three arc types only. Line 4: the merged output specification is And(caller, instance), caller first, in all three runtimes (merge_outputs in rewriter.rs, SubnetRewriter.mergeOutputs, mergeOutputs in subnet-rewriter.ts). When both sides produce into one place, And(Q, Q) names Q twice in one AND branch and the transition builder rejects the merge (IO-011, mergeEx_buildFails, mod021_buildFails): clause 1's union is read with line 7, so such a channel merge fails in every runtime and is no defect; the markdown says so under rule (b)."
          "Rule (d) is read as all three runtimes read it, by sets of arc types (ruling D20, clash mod-b#4; reject_cross_side_kind_conflicts in rewriter.rs, SubnetRewriter.rejectCrossKindArcConflicts, rejectCrossSideKindConflicts in subnet-rewriter.ts): Read + Reset on one side against Read alone on the other is a conflict, although pairing same-type arcs off first would leave no conflicting pair. That pair-off reading is the wrong model of MOD_021_forbids_pairOff. An output is not counted, as in every runtime: an input arc on one side and an output into the same place on the other is the usual channel wiring, which is why the premises of the markdown sentences speak of places on which both sides have an input, inhibitor, read or reset arc."
          "Messages. Line 10 states the rule (c) diagnostic byte for byte as the three runtimes write it; Java and TypeScript spell atLeast(n), Rust and Python at_least(n) in the cardinality and in the closing hint (merge_transitions and describe_in in rewriter.rs), and the line accepts both. The timing and arc-type messages are stated by what they name. Line 8: every runtime passes the caller-side name as the channel name and names it in the timing message and in the arc-type message. The two timings are named in each runtime's own rendering (Rust Debug in merge_timings, rewriter.rs; Java the record's toString in SubnetRewriter.mergeTimings; TypeScript describeTiming in mergeTimings, subnet-rewriter.ts), so line 8 states them through the parameter tstr; the witness is the reference's timingStr, and MOD_021_mutant_timingNameOnly_killed kills a message that names the caller only. Line 9: the caller-side name, an offending place and both sides' sets of arc types on it in the sorted rendering [inhibitor, input, read, reset] that the three runtimes share (describe_kinds in rewriter.rs, the TreeSet toString in SubnetRewriter.rejectCrossKindArcConflicts, describeKinds in subnet-rewriter.ts); rule (d) of the markdown now states that rendering."
          "Order of the checks, composition design skeptic correction S3. Rust and TypeScript check the timing, the ν-net match, the correspondence, the arc types, the input arcs and then the builder; Java checks the arc types first, then the timing, the match and the correspondence (merge_transitions in rewriter.rs, SubnetRewriter.mergeTransitions, mergeTransitions in subnet-rewriter.ts). Line 8 therefore claims the two timings only when the arc types agree (Java's arc-type message names the caller but not the timings; clause 2 lets an implementation report the rule (d) error instead), and lines 9 and 10 claim a message only when the earlier checks of every order pass. Line 9 claims that some offending place is named, not which one: Rust takes the first in its sorted map of the instance's places, TypeScript the first in the instance's arc order and Java the first its HashMap yields."
          "The declared-place correspondence merge cm is MOD-031's: its content and its rejection are that block's, and this block reads it only in the premises of lines 9 to 11. The ν-net match a transition may carry (NU-060) is not modelled here: CDef has no match field. The markdown sentences carry the premise that at most one side carries a match, since Rust and TypeScript reject two matches before the arc types and the input arcs (merge_match_specs in rewriter.rs); lines 9 to 11 hold over CDef, where no side carries one. NU-060 (wave W9) adds the field, its check and that premise to the Lean lines."
          "AC1 is MOD_021_nonvacuous on the reference: caller T with input P and output Q merged with channel transition C with input R and output S gives one transition T with inputs P and R, output And(Q, S) and Immediate timing. AC2 is line 8: Delayed(100) against Deadline(50) is rejected with the timing message naming T, Delayed(100) and Deadline(50) (MOD_021_nonvacuous). AC3, reworded under ruling D77 (a), is lines 5 and 8 on its three cases (MOD_021_nonvacuous). AC4's order is line 6; that both actions run within one firing and that token movement is atomic is EXEC-001's and CORE-021's, since one merged definition is one transition. AC5 (one invocation per fire) follows for the same reason and is EXEC-001's. AC6 is line 2 with the table block on its rows (MOD_021_nonvacuous). AC7, reworded to the set reading, is line 9: input against reset on P is rejected naming T, P, [input] and [reset] (MOD_021_nonvacuous). AC8 is line 10: one() against all() on P gives the exact diagnostic (MOD_021_nonvacuous). AC9 is reworded under ruling D48 (a) to cite CORE-011, CONC-003 and EXEC-020, which own the stamp of a produced token and the order of deposited tokens; its one TokenAdded event per produced token is EVT-011's. The Depends on line now lists the requirements the reworded text cites."
          "Mutants: line 1 kills MOD_021_mutant_instanceName and MOD_021_mutant_instancePriority, line 2 MOD_021_mutant_concatInputs, line 3 MOD_021_mutant_appendReads, line 4 MOD_021_mutant_callerOutput, line 5 MOD_021_mutant_callerTiming, line 6 MOD_021_mutant_instanceActionFirst, line 7 MOD_021_mutant_skipBuild, line 8 MOD_021_mutant_acceptTimingConflict and MOD_021_mutant_timingNameOnly, line 9 MOD_021_mutant_noKindCheck, line 10 MOD_021_mutant_instanceSeam, line 11 MOD_021_mutant_conservative. A merge that rejects everything violates line 11 (MOD_021_forbids_rejectAll)."
  signoff "2026-11-13 758692c07568f5cc ai"
  statement : ∀ {N A : Type} [DecidableEq N] [ToString N], (Trans N → Option String) →
      (Act A → Act A → Act A) → CorrMergeFn N A → (Timing → String) → MergeFn N A → Prop :=
    fun Build sq cm tstr Mg =>
      (∀ c i d, Mg c i = .ok d → d.core.name = c.core.name ∧ d.priority = c.priority) ∧
      (∀ c i d, mod021_inOnce c → mod021_inOnce i → Mg c i = .ok d →
        mod021_inputsMerged c i d) ∧
      (∀ c i d, Mg c i = .ok d → mod021_arcsUnion c i d) ∧
      (∀ c i d, Mg c i = .ok d → d.out = mergeOut c.out i.out) ∧
      (∀ c i d, Mg c i = .ok d → rtMergeTiming c.timing i.timing = some d.timing) ∧
      (∀ c i d, Mg c i = .ok d → d.action = sq c.action i.action) ∧
      (∀ c i d, Mg c i = .ok d → Build d.toTrans = none) ∧
      (∀ c i, mod021_named c → rtMergeTiming c.timing i.timing = none →
        ∃ m, Mg c i = .error m ∧ MsgNames m c.core.name ∧
          (KindsAgree c.toTransDef i.toTransDef →
            MsgNames m (tstr c.timing) ∧ MsgNames m (tstr i.timing))) ∧
      ((∀ c i, ¬ KindsAgree c.toTransDef i.toTransDef → ∃ m, Mg c i = .error m) ∧
        ∀ c i tm corr, mod021_named c → rtMergeTiming c.timing i.timing = some tm →
          cm c i = .ok corr →
          ¬ KindsAgree c.toTransDef i.toTransDef →
          ∃ m p, Mg c i = .error m ∧ p ∈ kindPlaces c.toTransDef ∧ p ∈ kindPlaces i.toTransDef ∧
            arcKinds c.toTransDef p ≠ arcKinds i.toTransDef p ∧
            MsgNames m c.core.name ∧ MsgNames m (toString p) ∧
            MsgNames m (arcKinds c.toTransDef p).str ∧
            MsgNames m (arcKinds i.toTransDef p).str) ∧
      (∀ c i tm corr, mod021_named c → mod021_inOnce c → mod021_inOnce i →
        rtMergeTiming c.timing i.timing = some tm → cm c i = .ok corr →
        KindsAgree c.toTransDef i.toTransDef →
        (∃ p a b, cardAt c.core.inputs p = some a ∧ cardAt i.core.inputs p = some b ∧
          mergeCard a b = none) →
        ∃ p a b, cardAt c.core.inputs p = some a ∧ cardAt i.core.inputs p = some b ∧
          mergeCard a b = none ∧
          (Mg c i = .error (mod021_offTableMsg c.core.name ⟨p, a, b⟩) ∨
            Mg c i = .error (mod021_offTableMsgSnake c.core.name ⟨p, a, b⟩))) ∧
      (∀ c i tm corr, mod021_named c → mod021_inOnce c → mod021_inOnce i →
        rtMergeTiming c.timing i.timing = some tm → cm c i = .ok corr →
        KindsAgree c.toTransDef i.toTransDef →
        (∀ p a b, cardAt c.core.inputs p = some a → cardAt i.core.inputs p = some b →
          mergeCard a b ≠ none) →
        (∀ d, mod021_shaped sq c i d → Build d.toTrans = none) →
        ∃ d, Mg c i = .ok d)

/- The pinned readable form of the MOD-021 merge block: a change to the formula shows up as a
diff here. -/
/--
info: def Libpetri.Spec.MOD_021 : {N A : Type} →
  [DecidableEq N] →
    [ToString N] →
      (Reference.Trans N → Option String) →
        (Act A → Act A → Act A) → CorrMergeFn N A → (Timing → String) → MergeFn N A → Prop :=
fun {N A} [DecidableEq N] [ToString N] Build sq cm tstr Mg =>
  (∀ (c i d : CDef N A), Mg c i = Except.ok d → d.core.name = c.core.name ∧ d.priority = c.priority) ∧
    (∀ (c i d : CDef N A), mod021_inOnce c → mod021_inOnce i → Mg c i = Except.ok d → mod021_inputsMerged c i d) ∧
      (∀ (c i d : CDef N A), Mg c i = Except.ok d → mod021_arcsUnion c i d) ∧
        (∀ (c i d : CDef N A), Mg c i = Except.ok d → d.out = mergeOut c.out i.out) ∧
          (∀ (c i d : CDef N A), Mg c i = Except.ok d → rtMergeTiming c.timing i.timing = some d.timing) ∧
            (∀ (c i d : CDef N A), Mg c i = Except.ok d → d.action = sq c.action i.action) ∧
              (∀ (c i d : CDef N A), Mg c i = Except.ok d → Build d.toTrans = none) ∧
                (∀ (c i : CDef N A),
                    mod021_named c →
                      rtMergeTiming c.timing i.timing = none →
                        ∃ m,
                          Mg c i = Except.error m ∧
                            MsgNames m c.core.name ∧
                              (KindsAgree c.toTransDef i.toTransDef →
                                MsgNames m (tstr c.timing) ∧ MsgNames m (tstr i.timing))) ∧
                  ((∀ (c i : CDef N A), ¬KindsAgree c.toTransDef i.toTransDef → ∃ m, Mg c i = Except.error m) ∧
                      ∀ (c i : CDef N A) (tm : Timing) (corr : Option (List (N × N))),
                        mod021_named c →
                          rtMergeTiming c.timing i.timing = some tm →
                            cm c i = Except.ok corr →
                              ¬KindsAgree c.toTransDef i.toTransDef →
                                ∃ m p,
                                  Mg c i = Except.error m ∧
                                    p ∈ kindPlaces c.toTransDef ∧
                                      p ∈ kindPlaces i.toTransDef ∧
                                        arcKinds c.toTransDef p ≠ arcKinds i.toTransDef p ∧
                                          MsgNames m c.core.name ∧
                                            MsgNames m (toString p) ∧
                                              MsgNames m (arcKinds c.toTransDef p).str ∧
                                                MsgNames m (arcKinds i.toTransDef p).str) ∧
                    (∀ (c i : CDef N A) (tm : Timing) (corr : Option (List (N × N))),
                        mod021_named c →
                          mod021_inOnce c →
                            mod021_inOnce i →
                              rtMergeTiming c.timing i.timing = some tm →
                                cm c i = Except.ok corr →
                                  KindsAgree c.toTransDef i.toTransDef →
                                    (∃ p a b,
                                        cardAt c.core.inputs p = some a ∧
                                          cardAt i.core.inputs p = some b ∧ mergeCard a b = none) →
                                      ∃ p a b,
                                        cardAt c.core.inputs p = some a ∧
                                          cardAt i.core.inputs p = some b ∧
                                            mergeCard a b = none ∧
                                              (Mg c i =
                                                  Except.error
                                                    (mod021_offTableMsg c.core.name
                                                      { place := p, left := a, right := b }) ∨
                                                Mg c i =
                                                  Except.error
                                                    (mod021_offTableMsgSnake c.core.name
                                                      { place := p, left := a, right := b }))) ∧
                      ∀ (c i : CDef N A) (tm : Timing) (corr : Option (List (N × N))),
                        mod021_named c →
                          mod021_inOnce c →
                            mod021_inOnce i →
                              rtMergeTiming c.timing i.timing = some tm →
                                cm c i = Except.ok corr →
                                  KindsAgree c.toTransDef i.toTransDef →
                                    (∀ (p : N) (a b : Card),
                                        cardAt c.core.inputs p = some a →
                                          cardAt i.core.inputs p = some b → mergeCard a b ≠ none) →
                                      (∀ (d : CDef N A), mod021_shaped sq c i d → Build d.toTrans = none) →
                                        ∃ d, Mg c i = Except.ok d
-/
#guard_msgs in #print MOD_021

/-! ### The eleven lines, named (for the mutants) -/

section BLines

variable {N A : Type} [DecidableEq N] [ToString N]

/-- Line 1: the caller's name and priority. -/
def mod021b_line1 (Mg : MergeFn N A) : Prop :=
  ∀ c i d, Mg c i = .ok d → d.core.name = c.core.name ∧ d.priority = c.priority

/-- Line 2: the input arcs merged by the table. -/
def mod021b_line2 (Mg : MergeFn N A) : Prop :=
  ∀ c i d, mod021_inOnce c → mod021_inOnce i → Mg c i = .ok d → mod021_inputsMerged c i d

/-- Line 3: the inhibitor, read and reset arcs united. -/
def mod021b_line3 (Mg : MergeFn N A) : Prop :=
  ∀ c i d, Mg c i = .ok d → mod021_arcsUnion c i d

/-- Line 4: the output specifications combined. -/
def mod021b_line4 (Mg : MergeFn N A) : Prop :=
  ∀ c i d, Mg c i = .ok d → d.out = mergeOut c.out i.out

/-- Line 5: the timings merged by the runtimes' rule. -/
def mod021b_line5 (Mg : MergeFn N A) : Prop :=
  ∀ c i d, Mg c i = .ok d → rtMergeTiming c.timing i.timing = some d.timing

/-- Line 6: the caller's action, then the instance's. -/
def mod021b_line6 (sq : Act A → Act A → Act A) (Mg : MergeFn N A) : Prop :=
  ∀ c i d, Mg c i = .ok d → d.action = sq c.action i.action

/-- Line 7: the merged transition builds. -/
def mod021b_line7 (Build : Trans N → Option String) (Mg : MergeFn N A) : Prop :=
  ∀ c i d, Mg c i = .ok d → Build d.toTrans = none

/-- Line 8: timings with no merge reject, naming the caller, and both timings (rendered by
`tstr`) when the arc types agree. -/
def mod021b_line8 (tstr : Timing → String) (Mg : MergeFn N A) : Prop :=
  ∀ c i, mod021_named c → rtMergeTiming c.timing i.timing = none →
    ∃ m, Mg c i = .error m ∧ MsgNames m c.core.name ∧
      (KindsAgree c.toTransDef i.toTransDef →
        MsgNames m (tstr c.timing) ∧ MsgNames m (tstr i.timing))

/-- Line 8 without the timings: timings with no merge reject, naming the caller. -/
def mod021b_line8Name (Mg : MergeFn N A) : Prop :=
  ∀ c i, mod021_named c → rtMergeTiming c.timing i.timing = none →
    ∃ m, Mg c i = .error m ∧ MsgNames m c.core.name

/-- Line 9: different arc types on one place reject; once the timings and the correspondences
merge, the message names an offending place and both sides' sets of arc types on it. -/
def mod021b_line9 (cm : CorrMergeFn N A) (Mg : MergeFn N A) : Prop :=
  (∀ c i, ¬ KindsAgree c.toTransDef i.toTransDef → ∃ m, Mg c i = .error m) ∧
    ∀ c i tm corr, mod021_named c → rtMergeTiming c.timing i.timing = some tm →
      cm c i = .ok corr → ¬ KindsAgree c.toTransDef i.toTransDef →
      ∃ m p, Mg c i = .error m ∧ p ∈ kindPlaces c.toTransDef ∧ p ∈ kindPlaces i.toTransDef ∧
        arcKinds c.toTransDef p ≠ arcKinds i.toTransDef p ∧
        MsgNames m c.core.name ∧ MsgNames m (toString p) ∧
        MsgNames m (arcKinds c.toTransDef p).str ∧
        MsgNames m (arcKinds i.toTransDef p).str

/-- The conclusion of line 10 with the seam named after `name`. -/
def mod021_offTableNamed (Mg : MergeFn N A) (c i : CDef N A) (name : String) : Prop :=
  ∃ p a b, cardAt c.core.inputs p = some a ∧ cardAt i.core.inputs p = some b ∧
    mergeCard a b = none ∧
    (Mg c i = .error (mod021_offTableMsg name ⟨p, a, b⟩) ∨
      Mg c i = .error (mod021_offTableMsgSnake name ⟨p, a, b⟩))

/-- Line 10, with the seam named by `seam` (the block takes the caller's name). -/
def mod021b_line10At (seam : CDef N A → CDef N A → String) (cm : CorrMergeFn N A)
    (Mg : MergeFn N A) : Prop :=
  ∀ c i tm corr, mod021_named c → mod021_inOnce c → mod021_inOnce i →
    rtMergeTiming c.timing i.timing = some tm → cm c i = .ok corr →
    KindsAgree c.toTransDef i.toTransDef →
    (∃ p a b, cardAt c.core.inputs p = some a ∧ cardAt i.core.inputs p = some b ∧
      mergeCard a b = none) →
    mod021_offTableNamed Mg c i (seam c i)

/-- Line 10: an off-table pair rejects with the rule (c) diagnostic, seam after the caller. -/
def mod021b_line10 (cm : CorrMergeFn N A) (Mg : MergeFn N A) : Prop :=
  mod021b_line10At (fun c _ => c.core.name) cm Mg

/-- Line 11: acceptance. -/
def mod021b_line11 (Build : Trans N → Option String) (sq : Act A → Act A → Act A)
    (cm : CorrMergeFn N A) (Mg : MergeFn N A) : Prop :=
  ∀ c i tm corr, mod021_named c → mod021_inOnce c → mod021_inOnce i →
    rtMergeTiming c.timing i.timing = some tm → cm c i = .ok corr →
    KindsAgree c.toTransDef i.toTransDef →
    (∀ p a b, cardAt c.core.inputs p = some a → cardAt i.core.inputs p = some b →
      mergeCard a b ≠ none) →
    (∀ d, mod021_shaped sq c i d → Build d.toTrans = none) →
    ∃ d, Mg c i = .ok d

/-- The merge block is its eleven lines. -/
theorem mod021b_iff (Build : Trans N → Option String) (sq : Act A → Act A → Act A)
    (cm : CorrMergeFn N A) (tstr : Timing → String) (Mg : MergeFn N A) :
    MOD_021 Build sq cm tstr Mg ↔
      mod021b_line1 Mg ∧ mod021b_line2 Mg ∧ mod021b_line3 Mg ∧ mod021b_line4 Mg ∧ mod021b_line5 Mg ∧
      mod021b_line6 sq Mg ∧ mod021b_line7 Build Mg ∧ mod021b_line8 tstr Mg ∧ mod021b_line9 cm Mg ∧
      mod021b_line10 cm Mg ∧ mod021b_line11 Build sq cm Mg :=
  Iff.rfl

end BLines

/-! ### A merge with its parts as parameters

`mod021_mergeG` is the reference merge with four of its parts left open: the timing merge, the
timing message, the arc-type check and the name in the seam of the rule (c) diagnostic. The
reference is the instance with the runtimes' parts (`mod021_refMerge_eq`); the wrong merges that
kill lines 8, 9 and 10 change one part. -/

section General

variable {N A : Type} [DecidableEq N] [ToString N]

/-- The reference merge with the timing merge `tmf`, the timing message `tmsg`, the arc-type
check `kc` and the seam name `seam` as parameters. -/
def mod021_mergeG (Build : Trans N → Option String) (sq : Act A → Act A → Act A)
    (cm : CorrMergeFn N A) (tmf : Timing → Timing → Option Timing)
    (tmsg : String → Timing → Timing → String)
    (kc : TransDef N A → TransDef N A → Option N) (seam : CDef N A → CDef N A → String) :
    MergeFn N A := fun c i =>
  match tmf c.timing i.timing with
  | none => .error (tmsg c.core.name c.timing i.timing)
  | some tm =>
    match cm c i with
    | .error m => .error m
    | .ok corr =>
      match kc c.toTransDef i.toTransDef with
      | some p => .error (kindMsg c.core.name p (arcKinds c.toTransDef p) (arcKinds i.toTransDef p))
      | none =>
        match mergeInputsE (c.core.inputs ++ i.core.inputs) with
        | .error col => .error (fuseMsg (chanSeam (seam c i)) col)
        | .ok ins =>
          match Build (mergedDef sq c i tm ins corr).toTrans with
          | some m => .error m
          | none => .ok (mergedDef sq c i tm ins corr)

/-- The reference merge is the general one with the runtimes' parts. -/
theorem mod021_refMerge_eq (Build : Trans N → Option String) (sq : Act A → Act A → Act A)
    (cm : CorrMergeFn N A) :
    refMerge Build sq cm =
      mod021_mergeG Build sq cm rtMergeTiming timingMsg kindConflict (fun c _ => c.core.name) :=
  rfl

omit [DecidableEq N] in
/-- The channel diagnostic of the reference is `mod021_offTableMsg`. -/
theorem mod021_fuseMsg_eq (name : String) (col : Collision N) :
    fuseMsg (chanSeam name) col = mod021_offTableMsg name col := rfl

omit [ToString N] in
/-- `eraseDups` leaves no repetition. -/
theorem mod021_eraseDups_nodup (l : List N) : l.eraseDups.Nodup := by
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
    cases l with
    | nil => simp
    | cons a as =>
      rw [List.eraseDups_cons]
      refine List.nodup_cons.2 ⟨?_, ih _ ?_ _ rfl⟩
      · intro hm
        have := List.mem_eraseDups.1 hm
        simp at this
      · subst h
        exact Nat.lt_succ_of_le (List.length_filter_le _ _)

omit [ToString N] in
/-- The union of two arc lists holds each of their places once. -/
theorem mod021_union_unionArcs (xs ys : List N) : mod021_union xs ys (unionArcs xs ys) :=
  ⟨mod021_eraseDups_nodup _, fun _ => mem_unionArcs⟩

/-- A message of the form `a ++ toString s` names `s`. -/
theorem mod021_msgNames_endS (a s : String) : MsgNames (a ++ toString s) s :=
  msgNames_end a s

/-- The timing rejection names the channel. -/
theorem mod021_timingMsg_names (name : String) (c i : Timing) :
    MsgNames (timingMsg name c i) name := by
  unfold timingMsg
  repeat (first | (with_reducible exact msgNames_end _ _) |
    (with_reducible exact mod021_msgNames_endS _ _) | (with_reducible apply msgNames_app))

/-- The timing rejection names both timings as the reference renders them. -/
theorem mod021_timingMsg_timings (name : String) (c i : Timing) :
    MsgNames (timingMsg name c i) (timingStr c) ∧
      MsgNames (timingMsg name c i) (timingStr i) := by
  unfold timingMsg
  refine ⟨?_, ?_⟩ <;>
    repeat (first | (with_reducible exact msgNames_end _ _) |
      (with_reducible exact mod021_msgNames_endS _ _) | (with_reducible apply msgNames_app))

omit [DecidableEq N] in
/-- The arc-type rejection names the channel, the place and both sets of arc types. -/
theorem mod021_kindMsg_names (name : String) (p : N) (a b : ArcKinds) :
    MsgNames (kindMsg name p a b) name ∧ MsgNames (kindMsg name p a b) (toString p) ∧
      MsgNames (kindMsg name p a b) a.str ∧ MsgNames (kindMsg name p a b) b.str := by
  unfold kindMsg
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    repeat (first | (with_reducible exact msgNames_end _ _) |
      (with_reducible exact mod021_msgNames_endS _ _) | (with_reducible apply msgNames_app))

variable {Build : Trans N → Option String} {sq : Act A → Act A → Act A} {cm : CorrMergeFn N A}
  {tmf : Timing → Timing → Option Timing} {tmsg : String → Timing → Timing → String}
  {kc : TransDef N A → TransDef N A → Option N} {seam : CDef N A → CDef N A → String}

/-- What a success of the general merge is made of. -/
theorem mod021_G_ok {c i d : CDef N A} (h : mod021_mergeG Build sq cm tmf tmsg kc seam c i = .ok d) :
    ∃ tm corr ins, tmf c.timing i.timing = some tm ∧ cm c i = .ok corr ∧
      kc c.toTransDef i.toTransDef = none ∧
      mergeInputsE (c.core.inputs ++ i.core.inputs) = .ok ins ∧
      d = mergedDef sq c i tm ins corr ∧ Build d.toTrans = none := by
  unfold mod021_mergeG at h
  cases htm : tmf c.timing i.timing with
  | none => simp [htm] at h
  | some tm =>
    cases hc : cm c i with
    | error m => simp [htm, hc] at h
    | ok corr =>
      cases hk : kc c.toTransDef i.toTransDef with
      | some p => simp [htm, hc, hk] at h
      | none =>
        cases hi : mergeInputsE (c.core.inputs ++ i.core.inputs) with
        | error col => simp [htm, hc, hk, hi] at h
        | ok ins =>
          cases hb : Build (mergedDef sq c i tm ins corr).toTrans with
          | some m => simp [htm, hc, hk, hi, hb] at h
          | none =>
            simp only [htm, hc, hk, hi, hb, Except.ok.injEq] at h
            subst h
            exact ⟨tm, corr, ins, rfl, rfl, rfl, rfl, rfl, hb⟩

/-- Timings with no merge reject with the timing message. -/
theorem mod021_G_timing {c i : CDef N A} (h : tmf c.timing i.timing = none) :
    mod021_mergeG Build sq cm tmf tmsg kc seam c i = .error (tmsg c.core.name c.timing i.timing) := by
  simp only [mod021_mergeG, h]

/-- An arc-type conflict found rejects with the arc-type message. -/
theorem mod021_G_kinds {c i : CDef N A} {tm : Timing} {corr : Option (List (N × N))} {p : N}
    (ht : tmf c.timing i.timing = some tm) (hc : cm c i = .ok corr)
    (hk : kc c.toTransDef i.toTransDef = some p) :
    mod021_mergeG Build sq cm tmf tmsg kc seam c i =
      .error (kindMsg c.core.name p (arcKinds c.toTransDef p) (arcKinds i.toTransDef p)) := by
  simp only [mod021_mergeG, ht, hc, hk]

/-- An off-table pair rejects with the rule (c) diagnostic. -/
theorem mod021_G_offTable {c i : CDef N A} {tm : Timing} {corr : Option (List (N × N))}
    {col : Collision N} (ht : tmf c.timing i.timing = some tm) (hc : cm c i = .ok corr)
    (hk : kc c.toTransDef i.toTransDef = none)
    (hi : mergeInputsE (c.core.inputs ++ i.core.inputs) = .error col) :
    mod021_mergeG Build sq cm tmf tmsg kc seam c i = .error (mod021_offTableMsg (seam c i) col) := by
  simp only [mod021_mergeG, ht, hc, hk, hi]
  rfl

/-- Every check passing, the general merge succeeds with the merged definition. -/
theorem mod021_G_accepts {c i : CDef N A} {tm : Timing} {corr : Option (List (N × N))}
    {ins : List (NInSpec N)} (ht : tmf c.timing i.timing = some tm) (hc : cm c i = .ok corr)
    (hk : kc c.toTransDef i.toTransDef = none)
    (hi : mergeInputsE (c.core.inputs ++ i.core.inputs) = .ok ins)
    (hb : Build (mergedDef sq c i tm ins corr).toTrans = none) :
    mod021_mergeG Build sq cm tmf tmsg kc seam c i = .ok (mergedDef sq c i tm ins corr) := by
  simp only [mod021_mergeG, ht, hc, hk, hi, hb]

omit [ToString N] in
/-- The merged definition has the merged shape. -/
theorem mod021_mergedDef_shaped {c i : CDef N A} {tm : Timing} {corr : Option (List (N × N))}
    {ins : List (NInSpec N)} (hx : mod021_inOnce c) (hy : mod021_inOnce i)
    (ht : rtMergeTiming c.timing i.timing = some tm)
    (hi : mergeInputsE (c.core.inputs ++ i.core.inputs) = .ok ins) :
    mod021_shaped sq c i (mergedDef sq c i tm ins corr) :=
  ⟨rfl, rfl, mergeInputsE_cardAt hx hy hi,
    ⟨mod021_union_unionArcs _ _, mod021_union_unionArcs _ _, mod021_union_unionArcs _ _⟩, rfl, ht, rfl⟩

theorem mod021_G_line1 : mod021b_line1 (mod021_mergeG Build sq cm tmf tmsg kc seam) := by
  intro c i d h
  obtain ⟨_, _, _, -, -, -, -, rfl, -⟩ := mod021_G_ok h
  exact ⟨rfl, rfl⟩

theorem mod021_G_line2 : mod021b_line2 (mod021_mergeG Build sq cm tmf tmsg kc seam) := by
  intro c i d hx hy h
  obtain ⟨_, _, _, -, -, -, hi, rfl, -⟩ := mod021_G_ok h
  exact mergeInputsE_cardAt hx hy hi

theorem mod021_G_line3 : mod021b_line3 (mod021_mergeG Build sq cm tmf tmsg kc seam) := by
  intro c i d h
  obtain ⟨_, _, _, -, -, -, -, rfl, -⟩ := mod021_G_ok h
  exact ⟨mod021_union_unionArcs _ _, mod021_union_unionArcs _ _, mod021_union_unionArcs _ _⟩

theorem mod021_G_line4 : mod021b_line4 (mod021_mergeG Build sq cm tmf tmsg kc seam) := by
  intro c i d h
  obtain ⟨_, _, _, -, -, -, -, rfl, -⟩ := mod021_G_ok h
  rfl

theorem mod021_G_line5 (htm : ∀ a b t, tmf a b = some t → rtMergeTiming a b = some t) :
    mod021b_line5 (mod021_mergeG Build sq cm tmf tmsg kc seam) := by
  intro c i d h
  obtain ⟨_, _, _, ht, -, -, -, rfl, -⟩ := mod021_G_ok h
  exact htm _ _ _ ht

theorem mod021_G_line6 : mod021b_line6 sq (mod021_mergeG Build sq cm tmf tmsg kc seam) := by
  intro c i d h
  obtain ⟨_, _, _, -, -, -, -, rfl, -⟩ := mod021_G_ok h
  rfl

theorem mod021_G_line7 : mod021b_line7 Build (mod021_mergeG Build sq cm tmf tmsg kc seam) := by
  intro c i d h
  obtain ⟨_, _, _, -, -, -, -, -, hb⟩ := mod021_G_ok h
  exact hb

theorem mod021_G_line8Name (htm : ∀ a b, rtMergeTiming a b = none → tmf a b = none)
    (hn : ∀ n a b, MsgNames (tmsg n a b) n) :
    mod021b_line8Name (mod021_mergeG Build sq cm tmf tmsg kc seam) := fun _ _ _ h =>
  ⟨_, mod021_G_timing (htm _ _ h), hn _ _ _⟩

theorem mod021_G_line8 {tstr : Timing → String}
    (htm : ∀ a b, rtMergeTiming a b = none → tmf a b = none)
    (hn : ∀ n a b, MsgNames (tmsg n a b) n)
    (hts : ∀ n a b, MsgNames (tmsg n a b) (tstr a) ∧ MsgNames (tmsg n a b) (tstr b)) :
    mod021b_line8 tstr (mod021_mergeG Build sq cm tmf tmsg kc seam) := fun _ _ _ h =>
  ⟨_, mod021_G_timing (htm _ _ h), hn _ _ _, fun _ => hts _ _ _⟩

theorem mod021_G_line9 (hrt : ∀ a b t, rtMergeTiming a b = some t → tmf a b = some t)
    (hk1 : ∀ c i : TransDef N A, kc c i = none → KindsAgree c i)
    (hks : ∀ (c i : TransDef N A) p, kc c i = some p →
      p ∈ kindPlaces c ∧ p ∈ kindPlaces i ∧ arcKinds c p ≠ arcKinds i p) :
    mod021b_line9 cm (mod021_mergeG Build sq cm tmf tmsg kc seam) := by
  refine ⟨fun c i hk => except_error_of_not_ok fun d h => ?_,
    fun c i tm corr _ ht hc hK => ?_⟩
  · obtain ⟨_, _, _, -, -, hkn, -⟩ := mod021_G_ok h
    exact hk (hk1 _ _ hkn)
  · cases hk : kc c.toTransDef i.toTransDef with
    | none => exact absurd (hk1 _ _ hk) hK
    | some p =>
      obtain ⟨hpc, hpi, hne⟩ := hks _ _ _ hk
      obtain ⟨n1, n2, n3, n4⟩ := mod021_kindMsg_names c.core.name p
        (arcKinds c.toTransDef p) (arcKinds i.toTransDef p)
      exact ⟨_, p, mod021_G_kinds (hrt _ _ _ ht) hc hk, hpc, hpi, hne, n1, n2, n3, n4⟩

theorem mod021_G_line10 (hrt : ∀ a b t, rtMergeTiming a b = some t → tmf a b = some t)
    (hk0 : ∀ c i : TransDef N A, KindsAgree c i → kc c i = none) :
    mod021b_line10At seam cm (mod021_mergeG Build sq cm tmf tmsg kc seam) := by
  intro c i tm corr _ hx hy ht hc hK ⟨p, a, b, ha, hb, hab⟩
  cases hi : mergeInputsE (c.core.inputs ++ i.core.inputs) with
  | ok ins => exact absurd hab ((mergeInputsE_ok_iff hx hy).1 ⟨ins, hi⟩ p a b ha hb)
  | error col =>
    obtain ⟨h1, h2, h3⟩ := mergeInputsE_error hx hy hi
    exact ⟨col.place, col.left, col.right, h1, h2, h3,
      Or.inl (mod021_G_offTable (hrt _ _ _ ht) hc (hk0 _ _ hK) hi)⟩

theorem mod021_G_line11 (hrt : ∀ a b t, rtMergeTiming a b = some t → tmf a b = some t)
    (hk0 : ∀ c i : TransDef N A, KindsAgree c i → kc c i = none) :
    mod021b_line11 Build sq cm (mod021_mergeG Build sq cm tmf tmsg kc seam) := by
  intro c i tm corr _ hx hy ht hc hK hall hB
  obtain ⟨ins, hi⟩ := (mergeInputsE_ok_iff hx hy).2 hall
  exact ⟨_, mod021_G_accepts (hrt _ _ _ ht) hc (hk0 _ _ hK) hi
    (hB _ (mod021_mergedDef_shaped hx hy ht hi))⟩

end General

/-! ### The reference -/

/-- ✓ The reference channel merge satisfies the block for every transition-builder check, every
way of composing two actions and every correspondence merge, with timings written as the
reference writes them (`Delayed(100)`). For example, caller `T` (input `P`, output `Q`) merged
with channel transition `C` (input `R`, output `S`) gives one transition `T` with inputs `P` and
`R` and output `And(Q, S)`; two `one()` arcs on `P` become one `exactly(2)`; `Delayed(100)`
against `Deadline(50)` is rejected with a message naming `T`, `Delayed(100)` and
`Deadline(50)`. -/
@[evidence holds MOD_021]
theorem MOD_021_reference {N A : Type} [DecidableEq N] [ToString N]
    (Build : Trans N → Option String) (sq : Act A → Act A → Act A) (cm : CorrMergeFn N A) :
    MOD_021 Build sq cm timingStr (refMerge Build sq cm) := by
  rw [mod021_refMerge_eq]
  have hrt : ∀ a b t, rtMergeTiming a b = some t → rtMergeTiming a b = some t := fun _ _ _ h => h
  have hk0 : ∀ c i : TransDef N A, KindsAgree c i → kindConflict c i = none :=
    fun _ _ h => kindConflict_eq_none_iff.2 h
  exact ⟨mod021_G_line1, mod021_G_line2, mod021_G_line3, mod021_G_line4, mod021_G_line5 hrt,
    mod021_G_line6, mod021_G_line7,
    mod021_G_line8 (fun _ _ h => h) mod021_timingMsg_names mod021_timingMsg_timings,
    mod021_G_line9 hrt (fun _ _ h => kindConflict_eq_none_iff.1 h) (fun _ _ _ h => kindConflict_some h),
    mod021_G_line10 hrt hk0, mod021_G_line11 hrt hk0⟩

/-! ### Consequences for every model of the block -/

section BConsequences

variable {N A : Type} [DecidableEq N] [ToString N] {Build : Trans N → Option String}
  {sq : Act A → Act A → Act A} {cm : CorrMergeFn N A} {tstr : Timing → String} {Mg : MergeFn N A}

/-- **A success has the merged shape.** In every model of the block, a successful merge of two
definitions with at most one input arc per place is a definition of the shape lines 1 to 6
describe. -/
theorem mod021_ok_shaped (h : MOD_021 Build sq cm tstr Mg) {c i d : CDef N A} (hx : mod021_inOnce c)
    (hy : mod021_inOnce i) (hd : Mg c i = .ok d) : mod021_shaped sq c i d := by
  obtain ⟨l1, l2, l3, l4, l5, l6, -⟩ := h
  exact ⟨(l1 c i d hd).1, (l1 c i d hd).2, l2 c i d hx hy hd, l3 c i d hd, l4 c i d hd,
    l5 c i d hd, l6 c i d hd⟩

/-- **A merge the builder cannot accept fails.** In every model of the block, when the transition
builder rejects every definition of the merged shape, the merge fails: caller and channel
transition both putting a token into `Q` give the output `And(Q, Q)`, which the builder rejects
([IO-011]), so the merge is rejected. -/
theorem mod021_buildFails (h : MOD_021 Build sq cm tstr Mg) {c i : CDef N A} (hx : mod021_inOnce c)
    (hy : mod021_inOnce i) (hB : ∀ d, mod021_shaped sq c i d → Build d.toTrans ≠ none) :
    ∃ m, Mg c i = .error m :=
  except_error_of_not_ok fun d hd => hB d (mod021_ok_shaped h hx hy hd) (h.2.2.2.2.2.2.1 c i d hd)

/-- **The sole off-table pair is named.** In every model of the block, when the earlier checks
pass and `P` is the only place where the caller's input arc `a` and the instance's `b` have no
merge, the merge fails with the rule (c) diagnostic for `P`, `a` and `b`: `one()` against `all()`
on `P` from caller `T` gives `Channel composition 'T': input arcs one() and all() collide on place
'P' ...`. -/
theorem mod021_offTable_sole (h : MOD_021 Build sq cm tstr Mg) {c i : CDef N A} {tm : Timing}
    {corr : Option (List (N × N))} {p : N} {a b : Card} (hn : mod021_named c) (hx : mod021_inOnce c)
    (hy : mod021_inOnce i) (ht : rtMergeTiming c.timing i.timing = some tm)
    (hc : cm c i = .ok corr) (hK : KindsAgree c.toTransDef i.toTransDef)
    (ha : cardAt c.core.inputs p = some a) (hb : cardAt i.core.inputs p = some b)
    (hab : mergeCard a b = none)
    (hsole : ∀ q a' b', cardAt c.core.inputs q = some a' → cardAt i.core.inputs q = some b' →
      mergeCard a' b' = none → q = p) :
    Mg c i = .error (mod021_offTableMsg c.core.name ⟨p, a, b⟩) ∨
      Mg c i = .error (mod021_offTableMsgSnake c.core.name ⟨p, a, b⟩) := by
  obtain ⟨q, a', b', ha', hb', hab', hm⟩ :=
    h.2.2.2.2.2.2.2.2.2.1 c i tm corr hn hx hy ht hc hK ⟨p, a, b, ha, hb, hab⟩
  obtain rfl := hsole q a' b' ha' hb' hab'
  rw [ha] at ha'
  rw [hb] at hb'
  cases ha'
  cases hb'
  exact hm

end BConsequences

/-! ### Examples -/

/-- A transition-builder check that accepts every transition. -/
def mod021_buildAll {N : Type} : Trans N → Option String := fun _ => none

/-- The example composition of two actions: list append, caller first (not commutative). -/
def mod021_sqEx : Act (List String) → Act (List String) → Act (List String) := seqAct (· ++ ·)

/-- The example correspondence merge: it records none. -/
def mod021_cmNone : CorrMergeFn String (List String) := fun _ _ => .ok none

/-- An example caller named `T` is a named caller. -/
theorem mod021_named_T (ins : List (NInSpec String)) (o : Option (Out String))
    (inh reads resets : List String) (tm : Timing) (prio : Int) (act : Act (List String)) :
    mod021_named (mergeExDef "T" ins o inh reads resets tm prio act) :=
  ⟨'T', by simp [mergeExDef], by decide⟩

/-- A success, read off a decided view of the merge. -/
theorem mod021_ok_of_view {N A β : Type} {Mg : MergeFn N A} {c i : CDef N A}
    {f : CDef N A → β} {v : β} (h : (Mg c i).toOption.map f = some v) :
    ∃ d, Mg c i = .ok d ∧ f d = v := by
  cases hm : Mg c i with
  | error e => simp [hm, Except.toOption] at h
  | ok d => simp [hm, Except.toOption] at h; exact ⟨d, rfl, h⟩

set_option maxRecDepth 20000 in
/-- ✓ The acceptance criteria on the reference merge (the reference builder, actions as lists
joined caller first, no correspondence). AC1: caller `T` (input `P`, output `Q`) and channel
transition `C` (input `R`, output `S`) merge to one transition `T` taking from `P` and `R`,
putting into `Q` and `S`, `Immediate`. AC6: two `one()` arcs on `P` give one `exactly(2)`. AC8:
`one()` against `all()` on `P` gives `Channel composition 'T': input arcs one() and all() collide
on place 'P' ...`. AC7: input against reset on `P` is rejected naming `P`, `[input]` and
`[reset]`. AC2: `Delayed(100)` against `Deadline(50)` is rejected with a message naming `T`,
`Delayed(100)` and `Deadline(50)`. AC3: `Immediate` against
`Delayed(100)` gives `Delayed(100)`, `Window(10, 100)` twice gives `Window(10, 100)`, and
`Deadline(100)` against `Delayed(50)` is rejected. Caller priority 3 beats instance priority 7,
and caller action `c` then instance action `i` gives `c, i`. -/
@[evidence nonvacuous MOD_021]
theorem MOD_021_nonvacuous :
    (refMerge refBuild mod021_sqEx mod021_cmNone (mergeExDef "T" [⟨"P", .one⟩] (some (.place "Q")))
        (mergeExDef "C" [⟨"R", .one⟩] (some (.place "S")))).toOption.map mergeExView =
      some ("T", [("P", .one), ("R", .one)], some ["Q", "S"], .immediate) ∧
    (refMerge refBuild mod021_sqEx mod021_cmNone (mergeExDef "T" [⟨"P", .one⟩] none)
        (mergeExDef "C" [⟨"P", .one⟩] none)).toOption.map
        (fun d => d.core.inputs.map fun s => (s.place, s.card)) = some [("P", .exactly 2)] ∧
    mergeExMsg (refMerge refBuild mod021_sqEx mod021_cmNone (mergeExDef "T" [⟨"P", .one⟩] none)
        (mergeExDef "C" [⟨"P", .all⟩] none)) =
      some (mod021_offTableMsg "T" (⟨"P", .one, .all⟩ : Collision String)) ∧
    mergeExMsg (refMerge refBuild mod021_sqEx mod021_cmNone (mergeExDef "T" [⟨"P", .one⟩] none)
        (mergeExDef "C" [] none [] [] ["P"])) =
      some (kindMsg "T" "P" ⟨true, false, false, false⟩ ⟨false, false, false, true⟩) ∧
    mergeExMsg (refMerge refBuild mod021_sqEx mod021_cmNone (mergeExDef "T" [] none (tm := .delayed 100))
        (mergeExDef "C" [] none (tm := .deadline 50))) =
      some (timingMsg "T" (.delayed 100) (.deadline 50)) ∧
    (refMerge refBuild mod021_sqEx mod021_cmNone (mergeExDef "T" [] none)
        (mergeExDef "C" [] none (tm := .delayed 100))).toOption.map (·.timing) =
      some (.delayed 100) ∧
    (refMerge refBuild mod021_sqEx mod021_cmNone (mergeExDef "T" [] none (tm := .window 10 100))
        (mergeExDef "C" [] none (tm := .window 10 100))).toOption.map (·.timing) =
      some (.window 10 100) ∧
    (refMerge refBuild mod021_sqEx mod021_cmNone (mergeExDef "T" [] none (tm := .deadline 100))
        (mergeExDef "C" [] none (tm := .delayed 50))).toOption.isNone = true ∧
    (refMerge refBuild mod021_sqEx mod021_cmNone
        (mergeExDef "T" [] none (prio := 3) (act := .other ["c"]))
        (mergeExDef "C" [] none (prio := 7) (act := .other ["i"]))).toOption.map
        (fun d => (d.priority, d.action)) = some (3, .other ["c", "i"]) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ### Wrong merges -/

section Wrong

/-- The example reference merge with a builder that accepts everything. -/
def mod021_base : MergeFn String (List String) := refMerge mod021_buildAll mod021_sqEx mod021_cmNone

/-- The reference lines of the example base merge. -/
theorem mod021_base_holds : MOD_021 mod021_buildAll mod021_sqEx mod021_cmNone timingStr mod021_base :=
  MOD_021_reference _ _ _

/-- The example merge with the runtimes' first check: it refuses an empty caller-side name before
anything else, as Rust (`merge_transitions` in `rewriter.rs`), Java (`SubnetRewriter.mergeTransitions`) and
TypeScript (`mergeTransitions` in `subnet-rewriter.ts`) do. -/
def mod021_emptyGuard : MergeFn String (List String) := fun c i =>
  if c.core.name = "" then .error "mergeTransitions: mergedName must be a non-empty string"
  else mod021_base c i

/-- The merge that refuses an empty caller-side name meets the block: lines 8 to 11 claim nothing
of a caller whose name is empty, so the runtimes' refusal is no violation. -/
theorem mod021_emptyGuard_holds :
    MOD_021 mod021_buildAll mod021_sqEx mod021_cmNone timingStr mod021_emptyGuard := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11⟩ := mod021_base_holds
  have hok : ∀ c i d, mod021_emptyGuard c i = .ok d → mod021_base c i = .ok d := by
    intro c i d h
    unfold mod021_emptyGuard at h
    split at h
    · cases h
    · exact h
  have heq : ∀ c i, mod021_named c → mod021_emptyGuard c i = mod021_base c i := by
    intro c i ⟨ch, hm, _⟩
    unfold mod021_emptyGuard
    rw [if_neg]
    intro he
    rw [he] at hm
    simp at hm
  refine ⟨fun c i d h => l1 c i d (hok _ _ _ h), fun c i d hx hy h => l2 c i d hx hy (hok _ _ _ h),
    fun c i d h => l3 c i d (hok _ _ _ h), fun c i d h => l4 c i d (hok _ _ _ h),
    fun c i d h => l5 c i d (hok _ _ _ h), fun c i d h => l6 c i d (hok _ _ _ h),
    fun c i d h => l7 c i d (hok _ _ _ h), fun c i hn ht => heq c i hn ▸ l8 c i hn ht,
    ⟨fun c i hk => ?_, fun c i tm corr hn ht hc hK => heq c i hn ▸ l9.2 c i tm corr hn ht hc hK⟩,
    fun c i tm corr hn hx hy ht hc hK hoff => heq c i hn ▸ l10 c i tm corr hn hx hy ht hc hK hoff,
    fun c i tm corr hn hx hy ht hc hK hall hB => heq c i hn ▸ l11 c i tm corr hn hx hy ht hc hK hall hB⟩
  unfold mod021_emptyGuard
  split
  · exact ⟨_, rfl⟩
  · exact l9.1 c i hk

/-- A merge that rejects every pair. -/
def mod021_rejectAllMerge : MergeFn String (List String) := fun _ _ => .error ""

/-- ✗ A merge that rejects everything violates the block (line 11): two definitions without arcs,
both `Immediate`, must merge, and it rejects them. -/
@[evidence forbids MOD_021]
theorem MOD_021_forbids_rejectAll :
    ¬ MOD_021 mod021_buildAll mod021_sqEx mod021_cmNone timingStr mod021_rejectAllMerge := by
  intro h
  obtain ⟨d, hd⟩ := h.2.2.2.2.2.2.2.2.2.2 (mergeExDef "T" [] none) (mergeExDef "C" [] none)
    .immediate none (mod021_named_T ..) (by simp [mod021_inOnce, mergeExDef]) (by simp [mod021_inOnce, mergeExDef])
    rfl rfl (fun p hp => by simp [kindPlaces, mergeExDef] at hp)
    (fun p a b ha => by simp [cardAt, mergeExDef] at ha) (fun _ _ => rfl)
  cases hd

/-! #### Merges that change one field of every success

`mod021_post g Mg` is `Mg` with every success `d` of `c` and `i` replaced by `g c i d`: its
rejections are `Mg`'s, so every rejection line and the acceptance line carry over, and a success
line carries over when `g` keeps the field it reads. -/

section Post

variable {N A : Type} [DecidableEq N] [ToString N]

/-- `Mg` with every success rewritten by `g`. -/
def mod021_post (g : CDef N A → CDef N A → CDef N A → CDef N A) (Mg : MergeFn N A) :
    MergeFn N A := fun c i => (Mg c i).map (g c i)

variable {g : CDef N A → CDef N A → CDef N A → CDef N A} {Mg : MergeFn N A}

omit [DecidableEq N] [ToString N] in
/-- A success of the rewritten merge is a rewritten success. -/
theorem mod021_post_ok {c i d : CDef N A} (h : mod021_post g Mg c i = .ok d) :
    ∃ d0, Mg c i = .ok d0 ∧ g c i d0 = d :=
  except_map_ok_iff.1 h

omit [DecidableEq N] [ToString N] in
/-- The rewritten merge rejects exactly as `Mg` does. -/
theorem mod021_post_err {c i : CDef N A} {m : String} :
    mod021_post g Mg c i = .error m ↔ Mg c i = .error m := by
  unfold mod021_post
  cases Mg c i <;> simp [Except.map]

omit [DecidableEq N] [ToString N] in
/-- Line 1 carries over when `g` keeps name and priority. -/
theorem mod021_post_line1 (hg : ∀ c i d, (g c i d).core.name = d.core.name ∧ (g c i d).priority = d.priority)
    (h : mod021b_line1 Mg) : mod021b_line1 (mod021_post g Mg) := by
  intro c i d hd
  obtain ⟨d0, h0, rfl⟩ := mod021_post_ok hd
  exact ⟨(hg c i d0).1.trans (h c i d0 h0).1, (hg c i d0).2.trans (h c i d0 h0).2⟩

omit [ToString N] in
/-- Line 2 carries over when `g` keeps the input arcs. -/
theorem mod021_post_line2 (hg : ∀ c i d, (g c i d).core.inputs = d.core.inputs)
    (h : mod021b_line2 Mg) : mod021b_line2 (mod021_post g Mg) := by
  intro c i d hx hy hd
  obtain ⟨d0, h0, rfl⟩ := mod021_post_ok hd
  have := h c i d0 hx hy h0
  unfold mod021_inputsMerged mod021_inOnce at *
  rw [hg]
  exact this

omit [DecidableEq N] [ToString N] in
/-- Line 3 carries over when `g` keeps the inhibitor, read and reset arcs. -/
theorem mod021_post_line3
    (hg : ∀ c i d, (g c i d).core.inhibitors = d.core.inhibitors ∧ (g c i d).core.reads = d.core.reads ∧
      (g c i d).core.resets = d.core.resets)
    (h : mod021b_line3 Mg) : mod021b_line3 (mod021_post g Mg) := by
  intro c i d hd
  obtain ⟨d0, h0, rfl⟩ := mod021_post_ok hd
  have := h c i d0 h0
  unfold mod021_arcsUnion at *
  rw [(hg c i d0).1, (hg c i d0).2.1, (hg c i d0).2.2]
  exact this

omit [DecidableEq N] [ToString N] in
/-- Line 4 carries over when `g` keeps the output specification. -/
theorem mod021_post_line4 (hg : ∀ c i d, (g c i d).out = d.out) (h : mod021b_line4 Mg) :
    mod021b_line4 (mod021_post g Mg) := by
  intro c i d hd
  obtain ⟨d0, h0, rfl⟩ := mod021_post_ok hd
  rw [hg]; exact h c i d0 h0

omit [DecidableEq N] [ToString N] in
/-- Line 5 carries over when `g` keeps the timing. -/
theorem mod021_post_line5 (hg : ∀ c i d, (g c i d).timing = d.timing) (h : mod021b_line5 Mg) :
    mod021b_line5 (mod021_post g Mg) := by
  intro c i d hd
  obtain ⟨d0, h0, rfl⟩ := mod021_post_ok hd
  rw [hg]; exact h c i d0 h0

omit [DecidableEq N] [ToString N] in
/-- Line 6 carries over when `g` keeps the action. -/
theorem mod021_post_line6 {sq : Act A → Act A → Act A} (hg : ∀ c i d, (g c i d).action = d.action)
    (h : mod021b_line6 sq Mg) : mod021b_line6 sq (mod021_post g Mg) := by
  intro c i d hd
  obtain ⟨d0, h0, rfl⟩ := mod021_post_ok hd
  rw [hg]; exact h c i d0 h0

omit [DecidableEq N] [ToString N] in
/-- Line 7 holds of every merge for the builder that accepts everything. -/
theorem mod021_line7_buildAll (Mg : MergeFn N A) : mod021b_line7 mod021_buildAll Mg :=
  fun _ _ _ _ => rfl

omit [ToString N] in
/-- Line 8 carries over. -/
theorem mod021_post_line8 {tstr : Timing → String} (h : mod021b_line8 tstr Mg) :
    mod021b_line8 tstr (mod021_post g Mg) := by
  intro c i hn0 ht
  obtain ⟨m, hm, hn⟩ := h c i hn0 ht
  exact ⟨m, mod021_post_err.2 hm, hn⟩

/-- Line 9 carries over. -/
theorem mod021_post_line9 {cm : CorrMergeFn N A} (h : mod021b_line9 cm Mg) :
    mod021b_line9 cm (mod021_post g Mg) := by
  refine ⟨fun c i hk => ?_, fun c i tm corr hn0 ht hc hK => ?_⟩
  · obtain ⟨m, hm⟩ := h.1 c i hk
    exact ⟨m, mod021_post_err.2 hm⟩
  · obtain ⟨m, p, hm, hn⟩ := h.2 c i tm corr hn0 ht hc hK
    exact ⟨m, p, mod021_post_err.2 hm, hn⟩

/-- Line 10 carries over. -/
theorem mod021_post_line10 {cm : CorrMergeFn N A} {seam : CDef N A → CDef N A → String}
    (h : mod021b_line10At seam cm Mg) : mod021b_line10At seam cm (mod021_post g Mg) := by
  intro c i tm corr hn hx hy ht hc hK hoff
  obtain ⟨p, a, b, ha, hb, hab, hor⟩ := h c i tm corr hn hx hy ht hc hK hoff
  exact ⟨p, a, b, ha, hb, hab, hor.imp mod021_post_err.2 mod021_post_err.2⟩

omit [ToString N] in
/-- Line 11 carries over. -/
theorem mod021_post_line11 {Build : Trans N → Option String} {sq : Act A → Act A → Act A}
    {cm : CorrMergeFn N A} (h : mod021b_line11 Build sq cm Mg) :
    mod021b_line11 Build sq cm (mod021_post g Mg) := by
  intro c i tm corr hn hx hy ht hc hK hall hB
  obtain ⟨d, hd⟩ := h c i tm corr hn hx hy ht hc hK hall hB
  exact ⟨g c i d, by simp [mod021_post, hd, Except.map]⟩

/-- Lines 8 to 11 of a merge carry over to every rewrite of its successes. -/
theorem mod021_post_rejections {Build : Trans N → Option String} {sq : Act A → Act A → Act A}
    {cm : CorrMergeFn N A} {tstr : Timing → String} (h : MOD_021 Build sq cm tstr Mg) :
    mod021b_line8 tstr (mod021_post g Mg) ∧ mod021b_line9 cm (mod021_post g Mg) ∧
      mod021b_line10 cm (mod021_post g Mg) ∧ mod021b_line11 Build sq cm (mod021_post g Mg) :=
  ⟨mod021_post_line8 h.2.2.2.2.2.2.2.1, mod021_post_line9 h.2.2.2.2.2.2.2.2.1,
    mod021_post_line10 h.2.2.2.2.2.2.2.2.2.1, mod021_post_line11 h.2.2.2.2.2.2.2.2.2.2⟩

end Post

/-- No definition in the example has two input arcs on one place. -/
theorem mod021_inOnce_ex (nm : String) (ins : List (NInSpec String)) (o : Option (Out String))
    (inh reads resets : List String) (tm : Timing) (prio : Int) (act : Act (List String))
    (h : (ins.map (·.place)).Nodup) :
    mod021_inOnce (mergeExDef nm ins o inh reads resets tm prio act) := h

/-! #### Line 1 -/

/-- The example base merge with the instance-side name on every success. -/
def mod021_instanceNameMerge : MergeFn String (List String) :=
  mod021_post (fun _ i d => { d with core := { d.core with name := i.core.name } }) mod021_base

/-- **Mutant of line 1:** the merged transition takes the instance-side name, lines 2 to 11 kept. -/
def MOD_021_mutant_instanceName {N A : Type} [DecidableEq N] [ToString N]
    (Build : Trans N → Option String) (sq : Act A → Act A → Act A) (cm : CorrMergeFn N A)
    (tstr : Timing → String) (Mg : MergeFn N A) : Prop :=
  (∀ c i d, Mg c i = .ok d → d.core.name = i.core.name ∧ d.priority = c.priority) ∧
    mod021b_line2 Mg ∧ mod021b_line3 Mg ∧ mod021b_line4 Mg ∧ mod021b_line5 Mg ∧
    mod021b_line6 sq Mg ∧ mod021b_line7 Build Mg ∧ mod021b_line8 tstr Mg ∧ mod021b_line9 cm Mg ∧
    mod021b_line10 cm Mg ∧ mod021b_line11 Build sq cm Mg

/-- ✗ A merge that names the merged transition after the channel transition: caller `T` and
channel transition `C` merge to a transition named `C`. It meets the mutant and violates line 1,
which keeps the caller's name `T`. -/
@[evidence mutant MOD_021]
theorem MOD_021_mutant_instanceName_killed :
    MOD_021_mutant_instanceName mod021_buildAll mod021_sqEx mod021_cmNone timingStr mod021_instanceNameMerge ∧
      ¬ MOD_021 mod021_buildAll mod021_sqEx mod021_cmNone timingStr mod021_instanceNameMerge := by
  obtain ⟨l1, l2, l3, l4, l5, l6, -, -, -, -, -⟩ := mod021_base_holds
  obtain ⟨r8, r9, r10, r11⟩ := mod021_post_rejections (g := fun _ i d =>
    { d with core := { d.core with name := i.core.name } }) mod021_base_holds
  refine ⟨⟨fun c i d hd => ?_, mod021_post_line2 (fun _ _ _ => rfl) l2,
    mod021_post_line3 (fun _ _ _ => ⟨rfl, rfl, rfl⟩) l3, mod021_post_line4 (fun _ _ _ => rfl) l4,
    mod021_post_line5 (fun _ _ _ => rfl) l5, mod021_post_line6 (fun _ _ _ => rfl) l6,
    mod021_line7_buildAll _, r8, r9, r10, r11⟩, fun h => ?_⟩
  · obtain ⟨d0, h0, rfl⟩ := mod021_post_ok hd
    exact ⟨rfl, (l1 c i d0 h0).2⟩
  · obtain ⟨d, hd, hv⟩ := mod021_ok_of_view (Mg := mod021_instanceNameMerge)
      (c := mergeExDef "T" [] none) (i := mergeExDef "C" [] none) (f := (·.core.name))
      (v := "C") (by decide)
    have := (h.1 _ _ d hd).1
    rw [this] at hv
    exact absurd hv (by decide)

/-- The example base merge with the instance-side priority on every success. -/
def mod021_instancePriorityMerge : MergeFn String (List String) :=
  mod021_post (fun _ i d => { d with priority := i.priority }) mod021_base

/-- **Mutant of line 1:** the instance-side priority wins, lines 2 to 11 kept. -/
def MOD_021_mutant_instancePriority {N A : Type} [DecidableEq N] [ToString N]
    (Build : Trans N → Option String) (sq : Act A → Act A → Act A) (cm : CorrMergeFn N A)
    (tstr : Timing → String) (Mg : MergeFn N A) : Prop :=
  (∀ c i d, Mg c i = .ok d → d.core.name = c.core.name ∧ d.priority = i.priority) ∧
    mod021b_line2 Mg ∧ mod021b_line3 Mg ∧ mod021b_line4 Mg ∧ mod021b_line5 Mg ∧
    mod021b_line6 sq Mg ∧ mod021b_line7 Build Mg ∧ mod021b_line8 tstr Mg ∧ mod021b_line9 cm Mg ∧
    mod021b_line10 cm Mg ∧ mod021b_line11 Build sq cm Mg

/-- ✗ A merge in which the instance side's priority wins: caller priority 3 against channel
transition priority 7 gives 7. It meets the mutant and violates line 1, which gives the caller's
3 (clause 3). -/
@[evidence mutant MOD_021]
theorem MOD_021_mutant_instancePriority_killed :
    MOD_021_mutant_instancePriority mod021_buildAll mod021_sqEx mod021_cmNone timingStr
        mod021_instancePriorityMerge ∧
      ¬ MOD_021 mod021_buildAll mod021_sqEx mod021_cmNone timingStr mod021_instancePriorityMerge := by
  obtain ⟨l1, l2, l3, l4, l5, l6, -, -, -, -, -⟩ := mod021_base_holds
  obtain ⟨r8, r9, r10, r11⟩ := mod021_post_rejections
    (g := fun _ i d => { d with priority := i.priority }) mod021_base_holds
  refine ⟨⟨fun c i d hd => ?_, mod021_post_line2 (fun _ _ _ => rfl) l2,
    mod021_post_line3 (fun _ _ _ => ⟨rfl, rfl, rfl⟩) l3, mod021_post_line4 (fun _ _ _ => rfl) l4,
    mod021_post_line5 (fun _ _ _ => rfl) l5, mod021_post_line6 (fun _ _ _ => rfl) l6,
    mod021_line7_buildAll _, r8, r9, r10, r11⟩, fun h => ?_⟩
  · obtain ⟨d0, h0, rfl⟩ := mod021_post_ok hd
    exact ⟨(l1 c i d0 h0).1, rfl⟩
  · obtain ⟨d, hd, hv⟩ := mod021_ok_of_view (Mg := mod021_instancePriorityMerge)
      (c := mergeExDef "T" [] none (prio := 3)) (i := mergeExDef "C" [] none (prio := 7))
      (f := (·.priority)) (v := 7) (by decide)
    have := (h.1 _ _ d hd).2
    rw [this] at hv
    exact absurd hv (by decide)

/-! #### Line 2 -/

/-- The example base merge that keeps both sides' input arcs side by side, unmerged. -/
def mod021_concatInputsMerge : MergeFn String (List String) :=
  mod021_post (fun c i d => { d with core := { d.core with inputs := c.core.inputs ++ i.core.inputs } })
    mod021_base

/-- **Mutant of line 2:** the input arcs are the caller's followed by the instance's, unmerged;
lines 1 and 3 to 11 kept. -/
def MOD_021_mutant_concatInputs {N A : Type} [DecidableEq N] [ToString N]
    (Build : Trans N → Option String) (sq : Act A → Act A → Act A) (cm : CorrMergeFn N A)
    (tstr : Timing → String) (Mg : MergeFn N A) : Prop :=
  mod021b_line1 Mg ∧ (∀ c i d, Mg c i = .ok d → d.core.inputs = c.core.inputs ++ i.core.inputs) ∧
    mod021b_line3 Mg ∧ mod021b_line4 Mg ∧ mod021b_line5 Mg ∧
    mod021b_line6 sq Mg ∧ mod021b_line7 Build Mg ∧ mod021b_line8 tstr Mg ∧ mod021b_line9 cm Mg ∧
    mod021b_line10 cm Mg ∧ mod021b_line11 Build sq cm Mg

/-- ✗ A merge that keeps both sides' input arcs unmerged: `one()` on `P` from each side gives two
`one()` arcs on `P`. It meets the mutant and violates line 2, which gives a single `exactly(2)`
(AC6). -/
@[evidence mutant MOD_021]
theorem MOD_021_mutant_concatInputs_killed :
    MOD_021_mutant_concatInputs mod021_buildAll mod021_sqEx mod021_cmNone timingStr mod021_concatInputsMerge ∧
      ¬ MOD_021 mod021_buildAll mod021_sqEx mod021_cmNone timingStr mod021_concatInputsMerge := by
  obtain ⟨l1, -, l3, l4, l5, l6, -, -, -, -, -⟩ := mod021_base_holds
  obtain ⟨r8, r9, r10, r11⟩ := mod021_post_rejections
    (g := fun c i d => { d with core := { d.core with inputs := c.core.inputs ++ i.core.inputs } }) mod021_base_holds
  refine ⟨⟨mod021_post_line1 (fun _ _ _ => ⟨rfl, rfl⟩) l1, fun c i d hd => ?_,
    mod021_post_line3 (fun _ _ _ => ⟨rfl, rfl, rfl⟩) l3, mod021_post_line4 (fun _ _ _ => rfl) l4,
    mod021_post_line5 (fun _ _ _ => rfl) l5, mod021_post_line6 (fun _ _ _ => rfl) l6,
    mod021_line7_buildAll _, r8, r9, r10, r11⟩, fun h => ?_⟩
  · obtain ⟨d0, -, rfl⟩ := mod021_post_ok hd
    rfl
  · obtain ⟨d, hd, hv⟩ := mod021_ok_of_view (Mg := mod021_concatInputsMerge)
      (c := mergeExDef "T" [⟨"P", .one⟩] none) (i := mergeExDef "C" [⟨"P", .one⟩] none)
      (f := fun d => cardAt d.core.inputs "P") (v := some .one) (by decide)
    have := (h.2.1 _ _ d (mod021_inOnce_ex _ _ _ _ _ _ _ _ _ (by decide))
      (mod021_inOnce_ex _ _ _ _ _ _ _ _ _ (by decide)) hd).2 "P"
    rw [this] at hv
    exact absurd hv (by decide)

/-! #### Line 3 -/

/-- The example base merge that appends the instance's read arcs to the caller's, repeats
included. -/
def mod021_appendReadsMerge : MergeFn String (List String) :=
  mod021_post (fun c i d => { d with core := { d.core with reads := c.core.reads ++ i.core.reads } })
    mod021_base

/-- **Mutant of line 3:** read arcs appended, repeats kept; lines 1, 2 and 4 to 11 kept. -/
def MOD_021_mutant_appendReads {N A : Type} [DecidableEq N] [ToString N]
    (Build : Trans N → Option String) (sq : Act A → Act A → Act A) (cm : CorrMergeFn N A)
    (tstr : Timing → String) (Mg : MergeFn N A) : Prop :=
  mod021b_line1 Mg ∧ mod021b_line2 Mg ∧
    (∀ c i d, Mg c i = .ok d →
      mod021_union c.core.inhibitors i.core.inhibitors d.core.inhibitors ∧
      d.core.reads = c.core.reads ++ i.core.reads ∧
      mod021_union c.core.resets i.core.resets d.core.resets) ∧
    mod021b_line4 Mg ∧ mod021b_line5 Mg ∧
    mod021b_line6 sq Mg ∧ mod021b_line7 Build Mg ∧ mod021b_line8 tstr Mg ∧ mod021b_line9 cm Mg ∧
    mod021b_line10 cm Mg ∧ mod021b_line11 Build sq cm Mg

/-- ✗ A merge that appends read arcs without collapsing them: both sides read `P`, the merged
transition reads `P` twice. It meets the mutant and violates line 3, which keeps one read arc on
`P` (rule (a)). -/
@[evidence mutant MOD_021]
theorem MOD_021_mutant_appendReads_killed :
    MOD_021_mutant_appendReads mod021_buildAll mod021_sqEx mod021_cmNone timingStr mod021_appendReadsMerge ∧
      ¬ MOD_021 mod021_buildAll mod021_sqEx mod021_cmNone timingStr mod021_appendReadsMerge := by
  obtain ⟨l1, l2, l3, l4, l5, l6, -, -, -, -, -⟩ := mod021_base_holds
  obtain ⟨r8, r9, r10, r11⟩ := mod021_post_rejections
    (g := fun c i d => { d with core := { d.core with reads := c.core.reads ++ i.core.reads } }) mod021_base_holds
  refine ⟨⟨mod021_post_line1 (fun _ _ _ => ⟨rfl, rfl⟩) l1, mod021_post_line2 (fun _ _ _ => rfl) l2,
    fun c i d hd => ?_, mod021_post_line4 (fun _ _ _ => rfl) l4,
    mod021_post_line5 (fun _ _ _ => rfl) l5, mod021_post_line6 (fun _ _ _ => rfl) l6,
    mod021_line7_buildAll _, r8, r9, r10, r11⟩, fun h => ?_⟩
  · obtain ⟨d0, h0, rfl⟩ := mod021_post_ok hd
    exact ⟨(l3 c i d0 h0).1, rfl, (l3 c i d0 h0).2.2⟩
  · obtain ⟨d, hd, hv⟩ := mod021_ok_of_view (Mg := mod021_appendReadsMerge)
      (c := mergeExDef "T" [] none [] ["P"]) (i := mergeExDef "C" [] none [] ["P"])
      (f := (·.core.reads)) (v := ["P", "P"]) (by decide)
    have := (h.2.2.1 _ _ d hd).2.1.1
    rw [hv] at this
    exact absurd this (by decide)

/-! #### Line 4 -/

/-- The example base merge that keeps only the caller's output specification. -/
def mod021_callerOutputMerge : MergeFn String (List String) :=
  mod021_post (fun c _ d => { d with out := c.out }) mod021_base

/-- **Mutant of line 4:** the caller's output specification only; lines 1 to 3 and 5 to 11
kept. -/
def MOD_021_mutant_callerOutput {N A : Type} [DecidableEq N] [ToString N]
    (Build : Trans N → Option String) (sq : Act A → Act A → Act A) (cm : CorrMergeFn N A)
    (tstr : Timing → String) (Mg : MergeFn N A) : Prop :=
  mod021b_line1 Mg ∧ mod021b_line2 Mg ∧ mod021b_line3 Mg ∧
    (∀ c i d, Mg c i = .ok d → d.out = c.out) ∧ mod021b_line5 Mg ∧
    mod021b_line6 sq Mg ∧ mod021b_line7 Build Mg ∧ mod021b_line8 tstr Mg ∧ mod021b_line9 cm Mg ∧
    mod021b_line10 cm Mg ∧ mod021b_line11 Build sq cm Mg

/-- ✗ A merge that keeps only the caller's output: caller `T` puts into `Q`, channel transition
`C` into `S`, and the merged transition puts into `Q` only. It meets the mutant and violates line
4, which gives `And(Q, S)` (AC1). -/
@[evidence mutant MOD_021]
theorem MOD_021_mutant_callerOutput_killed :
    MOD_021_mutant_callerOutput mod021_buildAll mod021_sqEx mod021_cmNone timingStr mod021_callerOutputMerge ∧
      ¬ MOD_021 mod021_buildAll mod021_sqEx mod021_cmNone timingStr mod021_callerOutputMerge := by
  obtain ⟨l1, l2, l3, -, l5, l6, -, -, -, -, -⟩ := mod021_base_holds
  obtain ⟨r8, r9, r10, r11⟩ := mod021_post_rejections (g := fun c _ d => { d with out := c.out }) mod021_base_holds
  refine ⟨⟨mod021_post_line1 (fun _ _ _ => ⟨rfl, rfl⟩) l1, mod021_post_line2 (fun _ _ _ => rfl) l2,
    mod021_post_line3 (fun _ _ _ => ⟨rfl, rfl, rfl⟩) l3, fun c i d hd => ?_,
    mod021_post_line5 (fun _ _ _ => rfl) l5, mod021_post_line6 (fun _ _ _ => rfl) l6,
    mod021_line7_buildAll _, r8, r9, r10, r11⟩, fun h => ?_⟩
  · obtain ⟨d0, -, rfl⟩ := mod021_post_ok hd
    rfl
  · obtain ⟨d, hd, hv⟩ := mod021_ok_of_view (Mg := mod021_callerOutputMerge)
      (c := mergeExDef "T" [] (some (.place "Q"))) (i := mergeExDef "C" [] (some (.place "S")))
      (f := fun d => d.out.map outPlaces) (v := some ["Q"]) (by decide)
    have := h.2.2.2.1 _ _ d hd
    rw [this] at hv
    exact absurd hv (by decide)

/-! #### Line 5 -/

/-- The example base merge that keeps the caller's timing. -/
def mod021_callerTimingMerge : MergeFn String (List String) :=
  mod021_post (fun c _ d => { d with timing := c.timing }) mod021_base

/-- **Mutant of line 5:** the caller's timing always wins; lines 1 to 4 and 6 to 11 kept. -/
def MOD_021_mutant_callerTiming {N A : Type} [DecidableEq N] [ToString N]
    (Build : Trans N → Option String) (sq : Act A → Act A → Act A) (cm : CorrMergeFn N A)
    (tstr : Timing → String) (Mg : MergeFn N A) : Prop :=
  mod021b_line1 Mg ∧ mod021b_line2 Mg ∧ mod021b_line3 Mg ∧ mod021b_line4 Mg ∧
    (∀ c i d, Mg c i = .ok d → d.timing = c.timing) ∧
    mod021b_line6 sq Mg ∧ mod021b_line7 Build Mg ∧ mod021b_line8 tstr Mg ∧ mod021b_line9 cm Mg ∧
    mod021b_line10 cm Mg ∧ mod021b_line11 Build sq cm Mg

/-- ✗ A merge in which the caller's timing always wins, as its priority does: an `Immediate`
caller merged with a `Deadline(5)` channel transition stays `Immediate`. It meets the mutant and
violates line 5, which gives `Deadline(5)` (`Immediate` yields to the other side, AC3). -/
@[evidence mutant MOD_021]
theorem MOD_021_mutant_callerTiming_killed :
    MOD_021_mutant_callerTiming mod021_buildAll mod021_sqEx mod021_cmNone timingStr mod021_callerTimingMerge ∧
      ¬ MOD_021 mod021_buildAll mod021_sqEx mod021_cmNone timingStr mod021_callerTimingMerge := by
  obtain ⟨l1, l2, l3, l4, -, l6, -, -, -, -, -⟩ := mod021_base_holds
  obtain ⟨r8, r9, r10, r11⟩ := mod021_post_rejections
    (g := fun c _ d => { d with timing := c.timing }) mod021_base_holds
  refine ⟨⟨mod021_post_line1 (fun _ _ _ => ⟨rfl, rfl⟩) l1, mod021_post_line2 (fun _ _ _ => rfl) l2,
    mod021_post_line3 (fun _ _ _ => ⟨rfl, rfl, rfl⟩) l3, mod021_post_line4 (fun _ _ _ => rfl) l4,
    fun c i d hd => ?_, mod021_post_line6 (fun _ _ _ => rfl) l6,
    mod021_line7_buildAll _, r8, r9, r10, r11⟩, fun h => ?_⟩
  · obtain ⟨d0, -, rfl⟩ := mod021_post_ok hd
    rfl
  · obtain ⟨d, hd, hv⟩ := mod021_ok_of_view (Mg := mod021_callerTimingMerge)
      (c := mergeExDef "T" [] none) (i := mergeExDef "C" [] none (tm := .deadline 5))
      (f := (·.timing)) (v := .immediate) (by decide)
    have := h.2.2.2.2.1 _ _ d hd
    rw [hv] at this
    exact absurd this (by decide)

/-! #### Line 6 -/

/-- The example base merge that runs the instance's action first. -/
def mod021_instanceFirstMerge : MergeFn String (List String) :=
  mod021_post (fun c i d => { d with action := mod021_sqEx i.action c.action }) mod021_base

/-- **Mutant of line 6:** the instance-side action first; lines 1 to 5 and 7 to 11 kept. -/
def MOD_021_mutant_instanceActionFirst {N A : Type} [DecidableEq N] [ToString N]
    (Build : Trans N → Option String) (sq : Act A → Act A → Act A) (cm : CorrMergeFn N A)
    (tstr : Timing → String) (Mg : MergeFn N A) : Prop :=
  mod021b_line1 Mg ∧ mod021b_line2 Mg ∧ mod021b_line3 Mg ∧ mod021b_line4 Mg ∧ mod021b_line5 Mg ∧
    (∀ c i d, Mg c i = .ok d → d.action = sq i.action c.action) ∧
    mod021b_line7 Build Mg ∧ mod021b_line8 tstr Mg ∧ mod021b_line9 cm Mg ∧
    mod021b_line10 cm Mg ∧ mod021b_line11 Build sq cm Mg

/-- ✗ A merge that runs the channel transition's action before the caller's: caller action `c`
and instance action `i` give `i, c`. It meets the mutant and violates line 6, which gives `c, i`
(clause 4, AC4). -/
@[evidence mutant MOD_021]
theorem MOD_021_mutant_instanceActionFirst_killed :
    MOD_021_mutant_instanceActionFirst mod021_buildAll mod021_sqEx mod021_cmNone timingStr
        mod021_instanceFirstMerge ∧
      ¬ MOD_021 mod021_buildAll mod021_sqEx mod021_cmNone timingStr mod021_instanceFirstMerge := by
  obtain ⟨l1, l2, l3, l4, l5, -, -, -, -, -, -⟩ := mod021_base_holds
  obtain ⟨r8, r9, r10, r11⟩ := mod021_post_rejections
    (g := fun c i d => { d with action := mod021_sqEx i.action c.action }) mod021_base_holds
  refine ⟨⟨mod021_post_line1 (fun _ _ _ => ⟨rfl, rfl⟩) l1, mod021_post_line2 (fun _ _ _ => rfl) l2,
    mod021_post_line3 (fun _ _ _ => ⟨rfl, rfl, rfl⟩) l3, mod021_post_line4 (fun _ _ _ => rfl) l4,
    mod021_post_line5 (fun _ _ _ => rfl) l5, fun c i d hd => ?_,
    mod021_line7_buildAll _, r8, r9, r10, r11⟩, fun h => ?_⟩
  · obtain ⟨d0, -, rfl⟩ := mod021_post_ok hd
    rfl
  · obtain ⟨d, hd, hv⟩ := mod021_ok_of_view (Mg := mod021_instanceFirstMerge)
      (c := mergeExDef "T" [] none (act := .other ["c"]))
      (i := mergeExDef "C" [] none (act := .other ["i"]))
      (f := (·.action)) (v := .other ["i", "c"]) (by decide)
    have := h.2.2.2.2.2.1 _ _ d hd
    rw [hv] at this
    exact absurd this (by decide)

/-! #### Line 7 -/

/-- **Mutant of line 7:** the transition-builder check dropped; every other line kept. -/
def MOD_021_mutant_skipBuild {N A : Type} [DecidableEq N] [ToString N]
    (Build : Trans N → Option String) (sq : Act A → Act A → Act A) (cm : CorrMergeFn N A)
    (tstr : Timing → String) (Mg : MergeFn N A) : Prop :=
  mod021b_line1 Mg ∧ mod021b_line2 Mg ∧ mod021b_line3 Mg ∧ mod021b_line4 Mg ∧ mod021b_line5 Mg ∧
    mod021b_line6 sq Mg ∧ mod021b_line8 tstr Mg ∧ mod021b_line9 cm Mg ∧
    mod021b_line10 cm Mg ∧ mod021b_line11 Build sq cm Mg

/-- ✗ A merge that never asks the transition builder: caller `T` and channel transition `C` both
put a token into `Q`, and the merged output `And(Q, Q)`, which names `Q` twice in one AND branch,
is accepted. It meets the mutant and violates line 7, since the reference builder rejects that
transition ([IO-011]). -/
@[evidence mutant MOD_021]
theorem MOD_021_mutant_skipBuild_killed :
    MOD_021_mutant_skipBuild refBuild mod021_sqEx mod021_cmNone timingStr mod021_base ∧
      ¬ MOD_021 refBuild mod021_sqEx mod021_cmNone timingStr mod021_base := by
  obtain ⟨l1, l2, l3, l4, l5, l6, -, l8, l9, l10, l11⟩ := mod021_base_holds
  refine ⟨⟨l1, l2, l3, l4, l5, l6, l8, l9, l10,
    fun c i tm corr hn hx hy ht hc hK hall _ => l11 c i tm corr hn hx hy ht hc hK hall fun _ _ => rfl⟩,
    fun h => ?_⟩
  obtain ⟨d, hd, hv⟩ := mod021_ok_of_view (Mg := mod021_base)
    (c := mergeExDef "T" [] (some (.place "Q"))) (i := mergeExDef "C" [] (some (.place "Q")))
    (f := fun d => (refBuild d.toTrans).isSome) (v := true) (by decide)
  have := h.2.2.2.2.2.2.1 _ _ d hd
  rw [this] at hv
  exact absurd hv (by decide)

/-! #### Lines 8, 9 and 10: one part of the merge changed -/

/-- The example merge that, where two timings have no merge, keeps the caller's. -/
def mod021_acceptTimingMerge : MergeFn String (List String) :=
  mod021_mergeG mod021_buildAll mod021_sqEx mod021_cmNone
    (fun a b => some ((rtMergeTiming a b).getD a)) timingMsg kindConflict (fun c _ => c.core.name)

/-- **Mutant of line 8:** two timings with no merge are not rejected, the caller's timing is
kept; line 5 weakened to the timings that merge, the other lines kept. -/
def MOD_021_mutant_acceptTimingConflict {N A : Type} [DecidableEq N] [ToString N]
    (Build : Trans N → Option String) (sq : Act A → Act A → Act A) (cm : CorrMergeFn N A)
    (_tstr : Timing → String) (Mg : MergeFn N A) : Prop :=
  mod021b_line1 Mg ∧ mod021b_line2 Mg ∧ mod021b_line3 Mg ∧ mod021b_line4 Mg ∧
    (∀ c i d, Mg c i = .ok d → d.timing = (rtMergeTiming c.timing i.timing).getD c.timing) ∧
    mod021b_line6 sq Mg ∧ mod021b_line7 Build Mg ∧ mod021b_line9 cm Mg ∧
    mod021b_line10 cm Mg ∧ mod021b_line11 Build sq cm Mg

/-- ✗ A merge that settles a timing conflict for the caller: `Deadline(100)` against
`Delayed(50)` merges, keeping `Deadline(100)`. It meets the mutant and violates line 8, which
rejects the pair (AC3). -/
@[evidence mutant MOD_021]
theorem MOD_021_mutant_acceptTimingConflict_killed :
    MOD_021_mutant_acceptTimingConflict mod021_buildAll mod021_sqEx mod021_cmNone timingStr
        mod021_acceptTimingMerge ∧
      ¬ MOD_021 mod021_buildAll mod021_sqEx mod021_cmNone timingStr mod021_acceptTimingMerge := by
  have hrt : ∀ a b t, rtMergeTiming a b = some t →
      (fun a b => some ((rtMergeTiming a b).getD a)) a b = some t := fun a b t h => by simp [h]
  have hk0 : ∀ c i : TransDef String (List String), KindsAgree c i → kindConflict c i = none :=
    fun _ _ h => kindConflict_eq_none_iff.2 h
  refine ⟨⟨mod021_G_line1, mod021_G_line2, mod021_G_line3, mod021_G_line4, fun c i d hd => ?_,
    mod021_G_line6, mod021_G_line7,
    mod021_G_line9 hrt (fun _ _ h => kindConflict_eq_none_iff.1 h)
      (fun _ _ _ h => kindConflict_some h),
    mod021_G_line10 hrt hk0, mod021_G_line11 hrt hk0⟩, fun h => ?_⟩
  · obtain ⟨_, _, _, ht, -, -, -, rfl, -⟩ := mod021_G_ok hd
    exact (Option.some.inj ht).symm
  · obtain ⟨m, hm, -⟩ := h.2.2.2.2.2.2.2.1 (mergeExDef "T" [] none (tm := .deadline 100))
      (mergeExDef "C" [] none (tm := .delayed 50)) (mod021_named_T ..) (by decide)
    have hv : (mod021_acceptTimingMerge (mergeExDef "T" [] none (tm := .deadline 100))
        (mergeExDef "C" [] none (tm := .delayed 50))).toOption.isSome = true := by decide
    rw [hm] at hv
    cases hv

/-- The example merge whose timing message names the caller-side transition only. -/
def mod021_timingNameOnlyMerge : MergeFn String (List String) :=
  mod021_mergeG mod021_buildAll mod021_sqEx mod021_cmNone rtMergeTiming
    (fun n _ _ => mod021_seam n) kindConflict (fun c _ => c.core.name)

/-- **Mutant of line 8:** the timing rejection names the caller-side transition but not the two
timings; the other lines kept. -/
def MOD_021_mutant_timingNameOnly {N A : Type} [DecidableEq N] [ToString N]
    (Build : Trans N → Option String) (sq : Act A → Act A → Act A) (cm : CorrMergeFn N A)
    (_tstr : Timing → String) (Mg : MergeFn N A) : Prop :=
  mod021b_line1 Mg ∧ mod021b_line2 Mg ∧ mod021b_line3 Mg ∧ mod021b_line4 Mg ∧ mod021b_line5 Mg ∧
    mod021b_line6 sq Mg ∧ mod021b_line7 Build Mg ∧ mod021b_line8Name Mg ∧ mod021b_line9 cm Mg ∧
    mod021b_line10 cm Mg ∧ mod021b_line11 Build sq cm Mg

set_option maxRecDepth 20000 in
/-- ✗ A merge whose timing rejection names only the caller: caller `T` with `Deadline(100)`
against channel transition `C` with `Delayed(50)`, neither with an arc, is rejected with the bare
message `Channel composition 'T'`. It meets the mutant and violates line 8, whose message names
`Deadline(100)` and `Delayed(50)` as well (clause 2, AC2). -/
@[evidence mutant MOD_021]
theorem MOD_021_mutant_timingNameOnly_killed :
    MOD_021_mutant_timingNameOnly mod021_buildAll mod021_sqEx mod021_cmNone timingStr
        mod021_timingNameOnlyMerge ∧
      ¬ MOD_021 mod021_buildAll mod021_sqEx mod021_cmNone timingStr mod021_timingNameOnlyMerge := by
  have hrt : ∀ a b t, rtMergeTiming a b = some t → rtMergeTiming a b = some t := fun _ _ _ h => h
  have hk0 : ∀ c i : TransDef String (List String), KindsAgree c i → kindConflict c i = none :=
    fun _ _ h => kindConflict_eq_none_iff.2 h
  refine ⟨⟨mod021_G_line1, mod021_G_line2, mod021_G_line3, mod021_G_line4, mod021_G_line5 hrt,
    mod021_G_line6, mod021_G_line7,
    mod021_G_line8Name (fun _ _ h => h) (fun _ _ _ => msgNames_app _ (msgNames_end _ _)),
    mod021_G_line9 hrt (fun _ _ h => kindConflict_eq_none_iff.1 h) (fun _ _ _ h => kindConflict_some h),
    mod021_G_line10 hrt hk0, mod021_G_line11 hrt hk0⟩, fun h => ?_⟩
  have hK : KindsAgree (mergeExDef "T" [] none (tm := .deadline 100)).toTransDef
      (mergeExDef "C" [] none (tm := .delayed 50)).toTransDef :=
    fun p hp => by simp [kindPlaces, mergeExDef] at hp
  obtain ⟨m, hm, -, hts⟩ := h.2.2.2.2.2.2.2.1 (mergeExDef "T" [] none (tm := .deadline 100))
    (mergeExDef "C" [] none (tm := .delayed 50)) (mod021_named_T ..) (by decide)
  have hmsg : mergeExMsg (mod021_timingNameOnlyMerge (mergeExDef "T" [] none (tm := .deadline 100))
      (mergeExDef "C" [] none (tm := .delayed 50))) = some "Channel composition 'T'" := by decide
  rw [hm] at hmsg
  simp only [mergeExMsg, Option.some.injEq] at hmsg
  subst hmsg
  have hn := (hts hK).1
  unfold MsgNames at hn
  exact absurd hn (by decide)

/-- The example merge without the arc-type check. -/
def mod021_noKindsMerge : MergeFn String (List String) :=
  mod021_mergeG mod021_buildAll mod021_sqEx mod021_cmNone rtMergeTiming timingMsg (fun _ _ => none)
    (fun c _ => c.core.name)

/-- **Mutant of line 9:** different arc types on one place are not rejected; the other lines
kept. -/
def MOD_021_mutant_noKindCheck {N A : Type} [DecidableEq N] [ToString N]
    (Build : Trans N → Option String) (sq : Act A → Act A → Act A) (cm : CorrMergeFn N A)
    (tstr : Timing → String) (Mg : MergeFn N A) : Prop :=
  mod021b_line1 Mg ∧ mod021b_line2 Mg ∧ mod021b_line3 Mg ∧ mod021b_line4 Mg ∧ mod021b_line5 Mg ∧
    mod021b_line6 sq Mg ∧ mod021b_line7 Build Mg ∧ mod021b_line8 tstr Mg ∧
    mod021b_line10 cm Mg ∧ mod021b_line11 Build sq cm Mg

/-- ✗ A merge without the arc-type check: the caller consumes from `P` and the channel transition
resets `P`, and the merge succeeds. It meets the mutant and violates line 9, which rejects the
pair (rule (d), AC7). -/
@[evidence mutant MOD_021]
theorem MOD_021_mutant_noKindCheck_killed :
    MOD_021_mutant_noKindCheck mod021_buildAll mod021_sqEx mod021_cmNone timingStr mod021_noKindsMerge ∧
      ¬ MOD_021 mod021_buildAll mod021_sqEx mod021_cmNone timingStr mod021_noKindsMerge := by
  have hrt : ∀ a b t, rtMergeTiming a b = some t → rtMergeTiming a b = some t := fun _ _ _ h => h
  have hk0 : ∀ c i : TransDef String (List String), KindsAgree c i →
      (fun _ _ => none : TransDef String (List String) → TransDef String (List String) → Option String) c i = none :=
    fun _ _ _ => rfl
  refine ⟨⟨mod021_G_line1, mod021_G_line2, mod021_G_line3, mod021_G_line4, mod021_G_line5 hrt,
    mod021_G_line6, mod021_G_line7, mod021_G_line8 (fun _ _ h => h) mod021_timingMsg_names mod021_timingMsg_timings,
    mod021_G_line10 hrt hk0, mod021_G_line11 hrt hk0⟩, fun h => ?_⟩
  have hkc : kindConflict (mergeExDef "T" [⟨"P", .one⟩] none).toTransDef
      (mergeExDef "C" [] none [] [] ["P"]).toTransDef = some "P" := by decide
  have hK : ¬ KindsAgree (mergeExDef "T" [⟨"P", .one⟩] none).toTransDef
      (mergeExDef "C" [] none [] [] ["P"]).toTransDef := fun hK => by
    rw [kindConflict_eq_none_iff.2 hK] at hkc
    cases hkc
  obtain ⟨m, hm⟩ := h.2.2.2.2.2.2.2.2.1.1 _ _ hK
  have hv : (mod021_noKindsMerge (mergeExDef "T" [⟨"P", .one⟩] none)
      (mergeExDef "C" [] none [] [] ["P"])).toOption.isSome = true := by decide
  rw [hm] at hv
  cases hv

/-- The example merge whose rule (c) diagnostic takes the channel transition's name as seam. -/
def mod021_instanceSeamMerge : MergeFn String (List String) :=
  mod021_mergeG mod021_buildAll mod021_sqEx mod021_cmNone rtMergeTiming timingMsg kindConflict
    (fun _ i => i.core.name)

/-- **Mutant of line 10:** the seam of the rule (c) diagnostic names the instance-side transition;
the other lines kept. -/
def MOD_021_mutant_instanceSeam {N A : Type} [DecidableEq N] [ToString N]
    (Build : Trans N → Option String) (sq : Act A → Act A → Act A) (cm : CorrMergeFn N A)
    (tstr : Timing → String) (Mg : MergeFn N A) : Prop :=
  mod021b_line1 Mg ∧ mod021b_line2 Mg ∧ mod021b_line3 Mg ∧ mod021b_line4 Mg ∧ mod021b_line5 Mg ∧
    mod021b_line6 sq Mg ∧ mod021b_line7 Build Mg ∧ mod021b_line8 tstr Mg ∧ mod021b_line9 cm Mg ∧
    mod021b_line10At (fun _ i => i.core.name) cm Mg ∧ mod021b_line11 Build sq cm Mg

set_option maxRecDepth 20000 in
/-- ✗ A merge whose diagnostic names the channel transition: caller `T` takes `one()` from `P`,
channel transition `C` takes `all()`, and the rejection reads `Channel composition 'C': ...`. It
meets the mutant and violates line 10, whose seam is the caller's name `T` (the markdown's
`Channel composition '<name>'` pinned to the caller side). -/
@[evidence mutant MOD_021]
theorem MOD_021_mutant_instanceSeam_killed :
    MOD_021_mutant_instanceSeam mod021_buildAll mod021_sqEx mod021_cmNone timingStr mod021_instanceSeamMerge ∧
      ¬ MOD_021 mod021_buildAll mod021_sqEx mod021_cmNone timingStr mod021_instanceSeamMerge := by
  have hrt : ∀ a b t, rtMergeTiming a b = some t → rtMergeTiming a b = some t := fun _ _ _ h => h
  have hk0 : ∀ c i : TransDef String (List String), KindsAgree c i → kindConflict c i = none :=
    fun _ _ h => kindConflict_eq_none_iff.2 h
  refine ⟨⟨mod021_G_line1, mod021_G_line2, mod021_G_line3, mod021_G_line4, mod021_G_line5 hrt,
    mod021_G_line6, mod021_G_line7, mod021_G_line8 (fun _ _ h => h) mod021_timingMsg_names mod021_timingMsg_timings,
    mod021_G_line9 hrt (fun _ _ h => kindConflict_eq_none_iff.1 h)
      (fun _ _ _ h => kindConflict_some h),
    mod021_G_line10 hrt hk0, mod021_G_line11 hrt hk0⟩, fun h => ?_⟩
  have hkc : kindConflict (mergeExDef "T" [⟨"P", .one⟩] none).toTransDef
      (mergeExDef "C" [⟨"P", .all⟩] none).toTransDef = none := by decide
  obtain ⟨p, a, b, ha, hb, -, hor⟩ := h.2.2.2.2.2.2.2.2.2.1 (mergeExDef "T" [⟨"P", .one⟩] none)
    (mergeExDef "C" [⟨"P", .all⟩] none) .immediate none (mod021_named_T ..)
    (mod021_inOnce_ex _ _ _ _ _ _ _ _ _ (by decide)) (mod021_inOnce_ex _ _ _ _ _ _ _ _ _ (by decide))
    rfl rfl (kindConflict_eq_none_iff.1 hkc) ⟨"P", .one, .all, by decide, by decide, by decide⟩
  have hp : p = "P" := by
    by_contra hne
    simp [cardAt, mergeExDef, List.find?, Ne.symm hne] at ha
  subst hp
  have ha' : a = .one := by simpa [cardAt, mergeExDef] using ha.symm
  have hb' : b = .all := by simpa [cardAt, mergeExDef] using hb.symm
  subst ha' hb'
  have hmsg : mergeExMsg (mod021_instanceSeamMerge (mergeExDef "T" [⟨"P", .one⟩] none)
      (mergeExDef "C" [⟨"P", .all⟩] none)) =
      some (mod021_offTableMsg "C" (⟨"P", .one, .all⟩ : Collision String)) := by decide
  rcases hor with hm | hm <;> rw [hm] at hmsg <;> simp only [mergeExMsg, Option.some.injEq] at hmsg <;>
    exact absurd hmsg (by decide)

/-! #### Line 11 -/

/-- `Mg`, except that a merge where both sides have an output specification is rejected. -/
def mod021_conservative {N A : Type} (Mg : MergeFn N A) : MergeFn N A := fun c i =>
  (Mg c i).bind fun d => if (c.out.isSome && i.out.isSome) = true then .error "both sides produce"
    else .ok d

/-- A success of the conservative merge is one of `Mg`. -/
theorem mod021_conservative_ok {N A : Type} {Mg : MergeFn N A} {c i d : CDef N A}
    (h : mod021_conservative Mg c i = .ok d) : Mg c i = .ok d := by
  unfold mod021_conservative at h
  cases hm : Mg c i with
  | error e => rw [hm] at h; cases h
  | ok d0 =>
    rw [hm] at h
    by_cases hb : (c.out.isSome && i.out.isSome) = true
    · simp [hb, Except.bind] at h
    · simp [hb, Except.bind] at h
      rw [h]

/-- A rejection of `Mg` is one of the conservative merge. -/
theorem mod021_conservative_err {N A : Type} {Mg : MergeFn N A} {c i : CDef N A} {m : String}
    (h : Mg c i = .error m) : mod021_conservative Mg c i = .error m := by
  unfold mod021_conservative
  rw [h]
  rfl

/-- **Mutant of line 11:** lines 1 to 10, without acceptance. -/
def MOD_021_mutant_conservative {N A : Type} [DecidableEq N] [ToString N]
    (Build : Trans N → Option String) (sq : Act A → Act A → Act A) (cm : CorrMergeFn N A)
    (tstr : Timing → String) (Mg : MergeFn N A) : Prop :=
  mod021b_line1 Mg ∧ mod021b_line2 Mg ∧ mod021b_line3 Mg ∧ mod021b_line4 Mg ∧ mod021b_line5 Mg ∧
    mod021b_line6 sq Mg ∧ mod021b_line7 Build Mg ∧ mod021b_line8 tstr Mg ∧ mod021b_line9 cm Mg ∧
    mod021b_line10 cm Mg

/-- ✗ A merge that refuses whenever both sides have an output: caller `T` puts into `Q`, channel
transition `C` into `S`, nothing conflicts, and the merge is rejected. It meets the mutant (every
success and every rejection it gives is the reference's) and violates line 11, under which this
merge succeeds (AC1). -/
@[evidence mutant MOD_021]
theorem MOD_021_mutant_conservative_killed :
    MOD_021_mutant_conservative mod021_buildAll mod021_sqEx mod021_cmNone timingStr
        (mod021_conservative mod021_base) ∧
      ¬ MOD_021 mod021_buildAll mod021_sqEx mod021_cmNone timingStr (mod021_conservative mod021_base) := by
  obtain ⟨l1, l2, l3, l4, l5, l6, -, l8, l9, l10, -⟩ := mod021_base_holds
  refine ⟨⟨fun c i d hd => l1 c i d (mod021_conservative_ok hd),
    fun c i d hx hy hd => l2 c i d hx hy (mod021_conservative_ok hd),
    fun c i d hd => l3 c i d (mod021_conservative_ok hd),
    fun c i d hd => l4 c i d (mod021_conservative_ok hd),
    fun c i d hd => l5 c i d (mod021_conservative_ok hd),
    fun c i d hd => l6 c i d (mod021_conservative_ok hd), mod021_line7_buildAll _,
    fun c i hn0 ht => ?_, ⟨fun c i hk => ?_, fun c i tm corr hn0 ht hc hK => ?_⟩,
    fun c i tm corr hn0 hx hy ht hc hK hoff => ?_⟩, fun h => ?_⟩
  · obtain ⟨m, hm, hn⟩ := l8 c i hn0 ht
    exact ⟨m, mod021_conservative_err hm, hn⟩
  · obtain ⟨m, hm⟩ := l9.1 c i hk
    exact ⟨m, mod021_conservative_err hm⟩
  · obtain ⟨m, p, hm, hn⟩ := l9.2 c i tm corr hn0 ht hc hK
    exact ⟨m, p, mod021_conservative_err hm, hn⟩
  · obtain ⟨p, a, b, ha, hb, hab, hor⟩ := l10 c i tm corr hn0 hx hy ht hc hK hoff
    exact ⟨p, a, b, ha, hb, hab, hor.imp mod021_conservative_err mod021_conservative_err⟩
  · obtain ⟨d, hd⟩ := h.2.2.2.2.2.2.2.2.2.2 (mergeExDef "T" [] (some (.place "Q")))
      (mergeExDef "C" [] (some (.place "S"))) .immediate none (mod021_named_T ..)
      (mod021_inOnce_ex _ _ _ _ _ _ _ _ _ (by decide)) (mod021_inOnce_ex _ _ _ _ _ _ _ _ _ (by decide))
      rfl rfl (fun p hp => by simp [kindPlaces, mergeExDef] at hp)
      (fun p a b ha => by simp [cardAt, mergeExDef] at ha) (fun _ _ => rfl)
    have hv : (mod021_conservative mod021_base (mergeExDef "T" [] (some (.place "Q")))
        (mergeExDef "C" [] (some (.place "S")))).toOption.isSome = false := by decide
    rw [hd] at hv
    cases hv

/-! #### Wrong readings of the markdown -/

/-- The kinds of arc `a` has and `b` has not. -/
def mod021_kindsDiff (a b : ArcKinds) : ArcKinds :=
  ⟨a.input && !b.input, a.inhibitor && !b.inhibitor, a.read && !b.read, a.reset && !b.reset⟩

/-- Rule (d) read by pairing same-type arcs off first: a place is a conflict only when each side
keeps an arc type the other side has not. -/
def mod021_pairOffConflict {N A : Type} [DecidableEq N] (c i : TransDef N A) : Option N :=
  (kindPlaces i).find? fun p => (arcKinds c p).any && (mod021_kindsDiff (arcKinds c p) (arcKinds i p)).any &&
    (mod021_kindsDiff (arcKinds i p) (arcKinds c p)).any

/-- The example merge with the pair-off reading of rule (d). -/
def mod021_pairOffMerge : MergeFn String (List String) :=
  mod021_mergeG mod021_buildAll mod021_sqEx mod021_cmNone rtMergeTiming timingMsg mod021_pairOffConflict
    (fun c _ => c.core.name)

/-- ✗ Rule (d) read by pairing same-type arcs off: the caller reads and resets `P`, the channel
transition only reads `P`; after the two reads pair up the reset has no partner, so this reading
finds no conflict and merges. The block violates it (line 9): the two sides' sets of arc types on
`P`, `[read, reset]` and `[read]`, differ, and every runtime rejects. -/
@[evidence forbids MOD_021]
theorem MOD_021_forbids_pairOff :
    ¬ MOD_021 mod021_buildAll mod021_sqEx mod021_cmNone timingStr mod021_pairOffMerge := by
  intro h
  have hkc : kindConflict (mergeExDef "T" [] none [] ["P"] ["P"]).toTransDef
      (mergeExDef "C" [] none [] ["P"]).toTransDef = some "P" := by decide
  have hK : ¬ KindsAgree (mergeExDef "T" [] none [] ["P"] ["P"]).toTransDef
      (mergeExDef "C" [] none [] ["P"]).toTransDef := fun hK => by
    rw [kindConflict_eq_none_iff.2 hK] at hkc
    cases hkc
  obtain ⟨m, hm⟩ := h.2.2.2.2.2.2.2.2.1.1 _ _ hK
  have hv : (mod021_pairOffMerge (mergeExDef "T" [] none [] ["P"] ["P"])
      (mergeExDef "C" [] none [] ["P"])).toOption.isSome = true := by decide
  rw [hm] at hv
  cases hv

/-- The upper end of a timing's firing interval (`none`: unbounded). -/
def mod021_latest : Timing → Option Nat
  | .immediate => some 0
  | .deadline b => some b
  | .delayed _ => none
  | .window _ l => some l
  | .exact a => some a

/-- The merged timing as the markdown stated it before ruling D77: equal timings collapse;
otherwise the intersection of the two firing intervals, mapped back by shape, and no merge when
it is empty. -/
def mod021_intervalTiming (c i : Timing) : Option Timing :=
  if c = i then some c else
    let lo := max c.earliest i.earliest
    match mod021_latest c, mod021_latest i with
    | none, none => some (.delayed lo)
    | some h, none | none, some h =>
      if h < lo then none else if lo = h then some (if h = 0 then .immediate else .exact h)
      else if lo = 0 then some (.deadline h) else some (.window lo h)
    | some a, some b =>
      let h := min a b
      if h < lo then none else if lo = h then some (if h = 0 then .immediate else .exact h)
      else if lo = 0 then some (.deadline h) else some (.window lo h)

/-- The example merge with the interval rule for timings. -/
def mod021_intervalMerge : MergeFn String (List String) :=
  mod021_mergeG mod021_buildAll mod021_sqEx mod021_cmNone mod021_intervalTiming timingMsg kindConflict
    (fun c _ => c.core.name)

/-- ✗ The interval rule the markdown stated before ruling D77: `Deadline(100)` against
`Delayed(50)` meets in `[50, 100]` and merges to `Window(50, 100)`. The block violates it (line
5): the runtimes' rule has no merge for two different non-`Immediate` timings, and every runtime
rejects the pair. -/
@[evidence forbids MOD_021]
theorem MOD_021_forbids_intervalTiming :
    ¬ MOD_021 mod021_buildAll mod021_sqEx mod021_cmNone timingStr mod021_intervalMerge := by
  intro h
  obtain ⟨d, hd, -⟩ := mod021_ok_of_view (Mg := mod021_intervalMerge)
    (c := mergeExDef "T" [] none (tm := .deadline 100)) (i := mergeExDef "C" [] none (tm := .delayed 50))
    (f := (·.timing)) (v := .window 50 100) (by decide)
  have := h.2.2.2.2.1 _ _ d hd
  have h0 : rtMergeTiming (mergeExDef "T" [] none (tm := .deadline 100)).timing
      (mergeExDef "C" [] none (tm := .delayed 50)).timing = none := by decide
  rw [h0] at this
  cases this

end Wrong

/-! ### Wave W9 compatibility -/

/-- NU-060's block (wave W9, `Spec/Req/NU_060.lean`) still writes `mod021_names`. It is the
shared `MsgNames` (`mod021_names_eq`); it goes when NU-060 switches to `MsgNames`. -/
def mod021_names (msg s : String) : Prop := s.toList <:+: msg.toList

/-- `mod021_names` is `MsgNames`. -/
theorem mod021_names_eq : mod021_names = MsgNames := rfl

/-- `msgNames_end` under NU-060's name. -/
theorem mod021_names_end (a s : String) : mod021_names (a ++ s) s := msgNames_end a s

/-- `msgNames_app` under NU-060's name. -/
theorem mod021_names_app {m s : String} (t : String) (h : mod021_names m s) :
    mod021_names (m ++ t) s := msgNames_app t h

end Libpetri.Spec
