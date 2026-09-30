import Mathlib.Data.List.Basic

/-!
# Pairwise mutual exclusion ([VER-002])

`MutualExclusion` over a list of places is **pairwise**: violated iff some two entries of the
list, at different positions, are marked at once. The Rust verifier enumerates the pairs with
`property.rs` `mutex_pairs` (positions `i < j < n`, lexicographic), writes the SMT term with
`smt_encoder.rs` `pairwise_marked` (`false` below two entries, `(and a b)` for two, the
disjunction of every pair's conjunction beyond) and evaluates it on a marking with
`property.rs` `two_marked` (the graph routes and the abstract replay). A linear route proves the
list pair by pair (`SmtProperty::linear_parts`).

This module states the one list fact all of them rest on: the disjunction over `pairsOf l` of
"both marked" holds iff at least two entries of `l` are marked (`any_pairsOf_iff`). It is
generic in the marking predicate, so the flat encoder (`Seam/Bad.lean` `pairMarkedBad`) and the
linear bound (`LinearBound.lean` `pairwise_linear_bound_sound`) instantiate it.
-/

namespace Libpetri.Novel.Pairwise

variable {α : Type}

/-- The position pairs `(l[i], l[j])`, `i < j`, in lexicographic order: `mutex_pairs`
(`property.rs`) mapped through the list. -/
def pairsOf : List α → List (α × α)
  | [] => []
  | x :: xs => xs.map (fun y => (x, y)) ++ pairsOf xs

/-- Two entries marked: `two_marked` (`property.rs`). -/
def twoMarked (f : α → Bool) (l : List α) : Bool := decide (2 ≤ (l.filter f).length)

theorem any_eq_true_iff_filter_pos (f : α → Bool) (l : List α) :
    l.any f = true ↔ 0 < (l.filter f).length := by
  rw [List.length_pos_iff_exists_mem]
  simp [List.any_eq_true, List.mem_filter]

/-- **The pairwise disjunction is "two marked".** Some pair of positions `i < j` has both
entries satisfying `f` iff at least two entries satisfy `f`. -/
theorem any_pairsOf_iff (f : α → Bool) (l : List α) :
    (pairsOf l).any (fun p => f p.1 && f p.2) = true ↔ 2 ≤ (l.filter f).length := by
  induction l with
  | nil => simp [pairsOf]
  | cons x xs ih =>
    rw [pairsOf, List.any_append, Bool.or_eq_true, ih, List.any_map]
    have hx : (xs.any ((fun p : α × α => f p.1 && f p.2) ∘ fun y => (x, y))) = (f x && xs.any f) := by
      cases hf : f x <;> simp [Function.comp_def, hf]
    rw [hx]
    cases hf : f x
    · simp [hf]
    · simp only [Bool.true_and, List.filter_cons, hf, if_true, List.length_cons]
      rw [any_eq_true_iff_filter_pos]
      omega

/-- `twoMarked` is the pairwise disjunction. -/
theorem twoMarked_eq_any (f : α → Bool) (l : List α) :
    twoMarked f l = (pairsOf l).any (fun p => f p.1 && f p.2) := by
  apply Bool.eq_iff_iff.mpr
  rw [any_pairsOf_iff, twoMarked, decide_eq_true_eq]

/-- Two entries: the one pair. `MutualExclusion(p, q)` is "both marked". -/
theorem pairsOf_two (p q : α) : pairsOf [p, q] = [(p, q)] := by
  simp [pairsOf]

/-- Fewer than two entries: no pair, never violated. -/
theorem pairsOf_short {l : List α} (h : l.length < 2) : pairsOf l = [] := by
  match l, h with
  | [], _ => rfl
  | [_], _ => rfl

/-- The pairs of a mapped list are the mapped pairs. -/
theorem pairsOf_map {β : Type} (g : α → β) (l : List α) :
    pairsOf (l.map g) = (pairsOf l).map (fun p => (g p.1, g p.2)) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [pairsOf, ih, List.map_map, Function.comp]

/-- Every pair is drawn from the list. -/
theorem mem_pairsOf {l : List α} {p : α × α} (h : p ∈ pairsOf l) : p.1 ∈ l ∧ p.2 ∈ l := by
  induction l with
  | nil => simp [pairsOf] at h
  | cons x xs ih =>
    rw [pairsOf, List.mem_append, List.mem_map] at h
    rcases h with ⟨y, hy, rfl⟩ | h
    · exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ hy⟩
    · exact ⟨List.mem_cons_of_mem _ (ih h).1, List.mem_cons_of_mem _ (ih h).2⟩

end Libpetri.Novel.Pairwise
