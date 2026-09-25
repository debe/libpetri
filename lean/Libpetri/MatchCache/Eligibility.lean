/-
# Match cache: the fast-path eligibility predicate

`FastPathEligible` and its static-analysis lemmas over the consumer/reset
maps, split out of `MatchCache.lean`.
-/
import Libpetri.MatchCache.Plumbing

namespace Libpetri

/-! ## The eligibility predicate, exactly as `init_match_caches` states it -/

/-- The `required` match of `init_match_caches`
(`precompiled_backend.rs:321-330`): `Some(In::One) => 1`,
`Some(In::Exactly{count}) => count`, everything else — `All`, `AtLeast`, or
no input spec at all — is ineligible (`_ => { eligible = false }`). -/
def fixedRequired : Card → Option Nat
  | .one => some 1
  | .exactly k => some k
  | .all => none
  | .atLeast _ => none

/-- Conjunct 1 for one correlated input: the spec lookup
(`t.input_specs().iter().find(...)`, `precompiled_backend.rs:317-320` —
`specAt` in `Basic.lean`) composed with `fixedRequired`. `some k` means the
input consumes a fixed `k` tokens per firing. -/
def requiredOf (t : Transition) (p : PlaceId) : Option Nat :=
  (specAt t p).bind fun sp => fixedRequired sp.card

/-- Conjunct 2's artifact: the `reset_target` boolean array of
`init_match_caches` (`precompiled_backend.rs:286-298`) — is `p` a reset
target of *any* transition (the owner included)? -/
def resetTarget (ts : List Transition) (p : PlaceId) : Bool :=
  ts.any fun u => u.resets.any fun r => r == p

/-- The Rust inner loop `for spec in t.input_specs() { if pid { push(tid) } }`
(`precompiled_backend.rs:289-293`): one entry per input spec of the
transition at index `i` that lands on `p`. -/
def specTids (i : Nat) (p : PlaceId) : List InSpec → List Nat
  | [] => []
  | sp :: rest =>
    if sp.place == p then i :: specTids i p rest else specTids i p rest

/-- Conjunct 3's artifact: the `input_consumers[pid]` vector
(`precompiled_backend.rs:285-293`) — every transition index that consumes
`p` through an input arc, in index order, with multiplicity. -/
def consumerTids : List Transition → Nat → PlaceId → List Nat
  | [], _, _ => []
  | u :: rest, i, p => specTids i p u.inputs ++ consumerTids rest (i + 1) p

def inputConsumers (ts : List Transition) (p : PlaceId) : List Nat :=
  consumerTids ts 0 p

/-- **The fast-path eligibility predicate of `init_match_caches`**
(`precompiled_backend.rs:312-336`), for the correlated input `p` of the
matched transition at index `tid`:

* `fixed_count` — the input spec on `p` is `One`/`Exactly` with consume
  count `k` (`:311-320`);
* `no_reset` — `!reset_target[pid]` (`:321`);
* `sole_consumer` — `input_consumers[pid] == [tid]` (`:321`): exactly one
  input arc in the whole net lands on `p`, and it is `tid`'s.

The code additionally requires `p` to be a compiled place id (`:303-306`);
the model's `PlaceId`s are dense, so that conjunct is absorbed (tokens for
unknown places never enter the pool or the caches — CORE-072). A matched
transition is fast-path eligible when every one of its key places satisfies
this predicate; the lockstep theorems are stated per key place. -/
structure FastPathEligible (ts : List Transition) (tid : Nat)
    (t : Transition) (p : PlaceId) (k : Nat) : Prop where
  owner : ts[tid]? = some t
  fixed_count : requiredOf t p = some k
  no_reset : resetTarget ts p = false
  sole_consumer : inputConsumers ts p = [tid]

/-! ### Static-analysis lemmas over the consumer/reset maps -/

theorem specTids_mem {i : Nat} {p : PlaceId} {l : List InSpec} :
    ∀ {x : Nat}, x ∈ specTids i p l → x = i := by
  induction l with
  | nil => intro x hx; cases hx
  | cons sp rest ih =>
    intro x hx
    simp only [specTids] at hx
    cases hpl : (sp.place == p) with
    | true =>
      rw [if_pos hpl] at hx
      cases hx with
      | head => rfl
      | tail _ h => exact ih h
    | false =>
      rw [if_neg (by simp [hpl])] at hx
      exact ih hx

theorem specTids_length {i : Nat} {p : PlaceId} :
    ∀ (l : List InSpec),
      (specTids i p l).length = l.countP fun sp => sp.place == p := by
  intro l
  induction l with
  | nil => rfl
  | cons sp rest ih =>
    simp only [specTids, List.countP_cons]
    cases hpl : (sp.place == p) with
    | true => simp [ih]
    | false => simp [ih]

theorem consumerTids_ge {p : PlaceId} {ts : List Transition} :
    ∀ {i x : Nat}, x ∈ consumerTids ts i p → i ≤ x := by
  induction ts with
  | nil => intro i x hx; cases hx
  | cons u rest ih =>
    intro i x hx
    simp only [consumerTids] at hx
    rcases List.mem_append.mp hx with h | h
    · have := specTids_mem h; omega
    · have := ih h; omega

theorem consumerTids_nil {p : PlaceId} {ts : List Transition} :
    ∀ {i : Nat}, consumerTids ts i p = [] →
      ∀ (j : Nat) (u : Transition), ts[j]? = some u →
        u.inputs.countP (fun sp => sp.place == p) = 0 := by
  induction ts with
  | nil => intro i _ j u hj; nomatch hj
  | cons u₀ rest ih =>
    intro i h j u hj
    simp only [consumerTids] at h
    obtain ⟨h1, h2⟩ := append_eq_nil' h
    cases j with
    | zero =>
      have hu : u₀ = u := Option.some.inj hj
      subst hu
      rw [← specTids_length (i := i) u₀.inputs, h1]
      rfl
    | succ j' => exact ih h2 j' u hj

/-- The load-bearing consequence of `input_consumers[pid] == [tid]`: the
transition at index `tid` has **exactly one** input spec on `p`, and every
other transition has **none**. -/
theorem consumerTids_single {p : PlaceId} {ts : List Transition} :
    ∀ {i tid : Nat}, consumerTids ts i p = [tid] →
      ∀ (j : Nat) (u : Transition), ts[j]? = some u →
        u.inputs.countP (fun sp => sp.place == p)
          = if i + j = tid then 1 else 0 := by
  induction ts with
  | nil => intro i tid _ j u hj; nomatch hj
  | cons u₀ rest ih =>
    intro i tid h j u hj
    simp only [consumerTids] at h
    cases hfm : specTids i p u₀.inputs with
    | nil =>
      rw [hfm, List.nil_append] at h
      have htid : i + 1 ≤ tid :=
        consumerTids_ge (show tid ∈ consumerTids rest (i + 1) p by
          rw [h]; exact List.Mem.head _)
      cases j with
      | zero =>
        have hu : u₀ = u := Option.some.inj hj
        subst hu
        rw [if_neg (by omega), ← specTids_length (i := i) u₀.inputs, hfm]
        rfl
      | succ j' =>
        rw [ih h j' u hj]
        by_cases hc : i + 1 + j' = tid
        · rw [if_pos hc, if_pos (by omega)]
        · rw [if_neg hc, if_neg (by omega)]
    | cons x xs =>
      rw [hfm, List.cons_append] at h
      injection h with hx htail
      obtain ⟨hxs, hrec⟩ := append_eq_nil' htail
      have hxi : x = i := specTids_mem (show x ∈ specTids i p u₀.inputs by
        rw [hfm]; exact List.Mem.head _)
      cases j with
      | zero =>
        have hu : u₀ = u := Option.some.inj hj
        subst hu
        rw [if_pos (by omega), ← specTids_length (i := i) u₀.inputs, hfm, hxs]
        rfl
      | succ j' =>
        rw [if_neg (by omega)]
        exact consumerTids_nil hrec j' u hj

theorem resetTarget_false {ts : List Transition} {p : PlaceId}
    (h : resetTarget ts p = false) :
    ∀ u ∈ ts, (u.resets.any fun r => r == p) = false := by
  induction ts with
  | nil => intro u hu; cases hu
  | cons u₀ rest ih =>
    rw [resetTarget, List.any_cons] at h
    intro u hu
    cases hx : (u₀.resets.any fun r => r == p) with
    | true => rw [hx, Bool.true_or] at h; cases h
    | false =>
      rw [hx, Bool.false_or] at h
      cases hu with
      | head => exact hx
      | tail _ hm => exact ih h u hm

end Libpetri
