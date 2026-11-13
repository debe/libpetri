import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryNu
import Libpetri.Spec.Text.NU_022

set_option linter.missingDocs true

/-!
# NU-022: Deterministic match selection (`spec/12-nu-nets.md`)

NU-022 is a pure-function requirement (kind F) on the selection a matched transition joins by:
given what the selection reads (`MatchIn`: per correlated input, the `(name, createdAt)` of every
named token in queue order, and the input's required count), it returns the eligible name that is
least by (earliest `createdAt` among the name's tokens in the correlated inputs, then name order),
and it returns a name whenever one is eligible. The statement is over an abstract selection
function `S : MatchSelect Nm`; the witness is the reference selection `refSelect`
(`Spec/GlossaryNu.lean`), the `argmin` the runtimes' `select_match_name` computes.

Ruling D31 (a): the stamp is the minimum over every token of the name in the correlated inputs,
consumed by the firing or not, and the name order is a parameter (`[LinearOrder Nm]`), so the
block holds of Rust's code-point order and of Java's and TypeScript's UTF-16 order alike.

The block has exactly one model for each name order (`NU_022_unique`), which is AC1.

Consistency: `Spec/ConsistencyNu.lean` joins this block to the ν firing through `NuSelectsBy`:
the chosen name of every matched firing is the selection's answer on the marking.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference

/-! ## NU-022: Deterministic Match Selection -/

requirement NU_022
  id "NU-022"
  title "Deterministic Match Selection"
  kind F
  scope "the match selection of every executor: select_match_name / selectMatchName and every incremental matcher"
  source verbatim "spec/12-nu-nets.md"
  covers NU_022.s1, NU_022.s2
  reading "For every selection input I and name n: if S returns n on I, then n is eligible on I (the match has a key, and every correlated input holds at least one token of n and at least its required count of them), and for every eligible name m, (oldest stamp of n, n) is at most (oldest stamp of m, m) in the lexicographic order, the oldest stamp being the earliest createdAt over every token of the name in every correlated input."
          "For every selection input I: if some name is eligible on I, then S returns a name on I."
  assumes "The model is one selection function S from the selection input to an optional name, for one name order. The selection input (MatchIn) is what select_match_name reads: per correlated input, in key order, the name and createdAt of every token whose key yields a name, in queue order, and the input's required count (Exactly n: n, AtLeast m: m, One and All: 1). A token whose key yields no name is not in it (ruling D37 (a)). Reading the input off a marking is matchIn (GlossaryNu), and that the firing's chosen name is the selection's answer is the conjunct NuSelectsBy of the consistency theorem; neither is a line here."
          "Ruling D31 (a): the oldest correlated-token timestamp of a name is the earliest createdAt over every token of the name in every correlated input, consumed by the firing or not (oldest in GlossaryNu), as all three runtimes compute it in their name index (select_match_name in rust/libpetri-runtime/src/match_engine.rs, MatchEngine.selectMatchName in java/src/main/java/org/libpetri/runtime/MatchEngine.java, selectMatchName in typescript/src/runtime/match-engine.ts). The reading 'among the tokens the firing consumes' is a forbidden model (NU_022_forbids_consumedOnly): it differs when a forwarded token keeps an old stamp behind a newer one (IO-014). createdAt is an integer, negative before the epoch (CORE-011)."
          "Ruling D31 (a): the name order is a parameter, any linear order on names. The sentences 'The selection is a pure function of the current marking and MUST be identical across all conforming implementations on names whose values hold only Basic Multilingual Plane characters ([NU-001])' and AC3 are carried by NU-001's fifth line (on BMP names every implementation's order is code-point order) together with this block's uniqueness: the block fixes the answer once the order is fixed. That the implementations' orders agree outside the BMP is not claimed (AC3: they may differ)."
          "AC1 (given the same eligible name-to-timestamps state, every implementation selects the same NameId) is the consequence NU_022_unique: two selection functions that both satisfy the block are equal."
          "AC2 (an incremental matcher returns the same NameId as the reference select_match_name for any sequence of add and consume operations) is about a matcher's internal state, the heap and per-name queues of the incremental matcher. Its contents half is proved for the Lean match cache by MatchCache.match_cache_lockstep, fire_muts_lockstep and sync_matchedRemove_step (the cache equals the from-scratch recompute after every eligible mutation); the heap order is kind Q, tested by the randomised differential tests of the test derivation. Not a line here."
          "AC3 (NameId ordering byte-identical for ASCII and BMP names; supplementary-plane code points may order differently per NU-001) is NU-001's, see above; not a line here."
          "A match without keys selects nothing: eligible is false for every name when the match has no key, as in every runtime (per_place.is_empty() returns None). A match builder rejects fewer than two keys (NU-020); the raw construction paths do not, and the block covers them too."
  signoff "2026-11-13 10b4f766fd485813 ai"
  statement : ∀ {Nm : Type} [LinearOrder Nm], MatchSelect Nm → Prop :=
    fun S =>
      (∀ I n, S I = some n → Selected I n) ∧
      (∀ I, (∃ n, eligible I n = true) → (S I).isSome = true)

/- The pinned readable form of NU-022: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.NU_022 : {Nm : Type} → [LinearOrder Nm] → MatchSelect Nm → Prop :=
fun {Nm} [LinearOrder Nm] S =>
  (∀ (I : MatchIn Nm) (n : Nm), S I = some n → Selected I n) ∧
    ∀ (I : MatchIn Nm), (∃ n, eligible I n = true) → (S I).isSome = true
-/
#guard_msgs in #print NU_022

/-! ## Holds and uniqueness -/

/-- ✓ The reference selection satisfies NU-022: it returns the eligible name least by (earliest
stamp, name), and it returns a name whenever one is eligible. -/
@[evidence holds NU_022]
theorem NU_022_reference {Nm : Type} [LinearOrder Nm] : NU_022 (refSelect (Nm := Nm)) :=
  ⟨fun I => (refSelect_spec I).1, fun I => (refSelect_spec I).2⟩

/-- AC1: the selection is unique. Two selection functions that both satisfy NU-022 return the
same name on every input, so every implementation that meets the block selects the same name. -/
theorem NU_022_unique {Nm : Type} [LinearOrder Nm] {S₁ S₂ : MatchSelect Nm} (h₁ : NU_022 S₁)
    (h₂ : NU_022 S₂) : S₁ = S₂ := by
  funext I
  cases e₁ : S₁ I with
  | none =>
    cases e₂ : S₂ I with
    | none => rfl
    | some m =>
      have := h₁.2 I ⟨m, (h₂.1 I m e₂).1⟩
      simp [e₁] at this
  | some n =>
    cases e₂ : S₂ I with
    | none =>
      have := h₂.2 I ⟨n, (h₁.1 I n e₁).1⟩
      simp [e₂] at this
    | some m => rw [selected_unique (h₁.1 I n e₁) (h₂.1 I m e₂)]

/-- NU-022 has exactly one model for each name order: the reference selection. -/
theorem NU_022_iff_ref {Nm : Type} [LinearOrder Nm] (S : MatchSelect Nm) :
    NU_022 S ↔ S = refSelect :=
  ⟨fun h => NU_022_unique h NU_022_reference, fun h => h ▸ NU_022_reference⟩

/-! ## Examples over names and stamps in `Nat` and `Int` -/

/-- Two correlated inputs, one token each required. Name 1 has tokens stamped 5 and 1, name 2
has tokens stamped 3 and 7, name 3 is only in the first input. -/
def nu022_two : MatchIn Nat := ⟨[([(1, 5), (2, 3), (3, 0)], 1), ([(2, 7), (1, 1)], 1)]⟩

/-- Names 1 and 2 both have earliest stamp 4: the name order decides. -/
def nu022_tie : MatchIn Nat := ⟨[([(2, 4), (1, 4)], 1), ([(1, 9), (2, 8)], 1)]⟩

/-- ✓ Worked example. On `nu022_two`, names 1 and 2 are both in both inputs, and name 3 is not in
the second, so 3 is not eligible. Name 1's earliest token (stamp 1, in the second input) is
earlier than name 2's (stamp 3), so the reference selection picks 1, which is the `Selected`
name. On `nu022_tie` both names start at stamp 4, and the name order picks 1. -/
@[evidence nonvacuous NU_022]
theorem NU_022_nonvacuous :
    eligible nu022_two 1 = true ∧ eligible nu022_two 2 = true ∧ eligible nu022_two 3 = false ∧
      refSelect nu022_two = some 1 ∧ Selected nu022_two 1 ∧
      eligible nu022_tie 2 = true ∧ refSelect nu022_tie = some 1 :=
  ⟨by decide, by decide, by decide, by decide,
    refSelect_eq_some_iff.1 (by decide), by decide, by decide⟩

/-! ## Forbidden models, one per load-bearing part of a line -/

/-- 'Oldest' read as the oldest of the tokens the firing consumes: per input, only the first
`required` tokens of the name count. -/
def oldestConsumed (I : MatchIn Nat) (n : Nat) : WithTop Int :=
  (I.keys.flatMap fun k => (stamps k.1 n).take k.2).minimum

/-- The selection that orders names by `oldestConsumed`. -/
def nu022_consumedOnly : MatchSelect Nat := fun I =>
  (cands I).argmin fun n => (toLex (oldestConsumed I n, n) : Lex (WithTop Int × Nat))

/-- Name 1 holds stamps 5 then 3 (a forwarded token keeps its stamp, IO-014), name 2 holds 4;
one token is required. -/
def nu022_nonMono : MatchIn Nat := ⟨[([(1, 5), (1, 3), (2, 4)], 1)]⟩

/-- ✗ Ruling D31 (a), worked example: one input holds name 1 stamped 5, name 1 stamped 3 (a token
forwarded with its old stamp) and name 2 stamped 4, and one token is required. Counting only the
token the firing would consume, name 1's stamp is 5 and name 2 wins; counting every token of the
name, name 1's stamp is 3 and name 1 is the selected name. So the consumed-only reading breaks the
first line. -/
@[evidence forbids NU_022]
theorem NU_022_forbids_consumedOnly : ¬ NU_022 nu022_consumedOnly := by
  intro h
  have h2 : nu022_consumedOnly nu022_nonMono = some 2 := by decide
  obtain ⟨-, hmin⟩ := h.1 _ _ h2
  exact absurd (hmin 1 (by decide)) (by decide)

/-- The selection that orders by name first, stamp second. -/
def nu022_nameFirst : MatchSelect Nat := fun I => (cands I).argmin id

/-- ✗ Worked example: on `nu022_two` the name order alone picks name 1 too, so take two names
where it does not: name 2 stamped 1 and name 1 stamped 6, in both inputs. Ordering by name first
picks 1, but name 2's token is older, so the first line fails. -/
@[evidence forbids NU_022]
theorem NU_022_forbids_nameFirst : ¬ NU_022 nu022_nameFirst := by
  intro h
  let I : MatchIn Nat := ⟨[([(2, 1), (1, 6)], 1), ([(1, 6), (2, 2)], 1)]⟩
  have h1 : nu022_nameFirst I = some 1 := by decide
  obtain ⟨-, hmin⟩ := h.1 _ _ h1
  exact absurd (hmin 2 (by decide)) (by decide)

/-- The selection that returns the name of the first token of the first input, eligible or not:
FIFO arrival with no join. -/
def nu022_firstToken : MatchSelect Nat := fun I =>
  I.keys.head?.bind fun k => k.1.head?.map Prod.fst

/-- ✗ Worked example: the first input's first token has name 3, which the second input does not
hold. Returning it breaks the first line's 'that name shall be eligible'. -/
@[evidence forbids NU_022]
theorem NU_022_forbids_firstToken : ¬ NU_022 nu022_firstToken := by
  intro h
  let I : MatchIn Nat := ⟨[([(3, 0), (1, 5)], 1), ([(1, 1)], 1)]⟩
  have h1 : nu022_firstToken I = some 3 := by decide
  exact absurd (h.1 _ _ h1).1 (by decide)

/-- ✗ The selection that never returns a name breaks the second line: on `nu022_two` names 1 and 2
are eligible, and it returns nothing. -/
@[evidence forbids NU_022]
theorem NU_022_forbids_never : ¬ NU_022 (fun _ => (none : Option Nat)) := by
  intro h
  exact absurd (h.2 nu022_two ⟨1, by decide⟩) (by decide)

/-- The selection that prefers the newest token: the eligible name whose latest stamp is
greatest. -/
def nu022_newest : MatchSelect Nat := fun I =>
  (cands I).argmax fun n => (I.keys.flatMap fun k => stamps k.1 n).maximum

/-- ✗ Worked example: on `nu022_two` name 2 has the latest token (stamp 7), so newest-first picks
2, while name 1's earliest token (stamp 1) is older than name 2's (stamp 3). The first line
fails. -/
@[evidence forbids NU_022]
theorem NU_022_forbids_newest : ¬ NU_022 nu022_newest := by
  intro h
  have h2 : nu022_newest nu022_two = some 2 := by decide
  obtain ⟨-, hmin⟩ := h.1 _ _ h2
  exact absurd (hmin 1 (by decide)) (by decide)

/-! ## A mutant: the block without its second line -/

/-- NU-022 without its second line: a selection may return nothing although a name is
eligible. -/
def NU_022_mutant_mayRefuse {Nm : Type} [LinearOrder Nm] (S : MatchSelect Nm) : Prop :=
  ∀ I n, S I = some n → Selected I n

/-- ✗ Worked example: the selection that never answers meets the first line (it never returns a
name, so it never returns a wrong one) but not NU-022: on `nu022_two` names 1 and 2 are eligible
and a firing would never join. The second line is load-bearing. -/
@[evidence mutant NU_022]
theorem NU_022_mutant_mayRefuse_killed :
    NU_022_mutant_mayRefuse (fun _ => (none : Option Nat)) ∧
      ¬ NU_022 (fun _ => (none : Option Nat)) :=
  ⟨fun _ _ h => absurd h (by simp), NU_022_forbids_never⟩

end Libpetri.Spec
