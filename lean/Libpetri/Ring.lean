/-
# The flat token pool of `PrecompiledBackend`, at full fidelity

Models the ring-buffer token storage of
`rust/libpetri-runtime/src/precompiled_backend.rs`: one flat pool
(`token_pool: Vec<Option<ErasedToken>>`) holding every place's ring as a block
at `place_offset[pid]`, with per-place `ring_head` / `ring_tail` /
`ring_capacity` / `token_counts`. The *i*-th oldest token of place `p` lives at

    token_pool[place_offset[p] + (ring_head[p] + i) % ring_capacity[p]]

Colours stand in for `ErasedToken` (as everywhere in this development — only
guard-observable equality matters), and the pool is a total function
`Nat → Option Colour` (a flat array *is* its index function; `len` carries the
`Vec` length for the bounds invariant RB1).

The invariant bundle `Pool.WF` is RB1–RB3 of the plan; `Pool.proj` is the
refinement map RB4 onto `CMarking` (`Basic.lean`), and the operation lemmas
are RB5 (`addLast`/grow preserve FIFO) and the frame/effect specs each later
file builds on. `ring_remove_matching` (RB6) lives here too, with both
compaction directions.
-/
import Libpetri.Ring.Match

namespace Libpetri

namespace Pool

/-! ### The composed operation -/

def removeMatching (s : Pool) (p : PlaceId) (pred : Colour → Bool) :
    Option Colour × Pool :=
  match s.findMatch p pred with
  | none => (none, s)
  | some i =>
    (s.pool (s.slot p i),
     if i ≤ s.cnt p - 1 - i then s.headSlideAt p i else s.tailSlideAt p i)

/-- RB6, no-match half: nothing satisfies `pred`, nothing changes. -/
theorem removeMatching_none {s : Pool} (_hwf : WF s) {p : PlaceId}
    (_hp : p < s.nplaces) {pred : Colour → Bool}
    (h : (s.removeMatching p pred).1 = none) :
    (s.removeMatching p pred).2 = s ∧ ∀ c ∈ s.proj p, pred c = false := by
  unfold removeMatching at h ⊢
  cases hf : s.findMatch p pred with
  | some i =>
    rw [hf] at h
    change s.pool (s.slot p i) = none at h
    obtain ⟨_, h2, h3, _⟩ := findMatchFrom_some hf
    obtain ⟨c, hc, _⟩ := matchesAt_true h3
    rw [hc] at h
    cases h
  | none =>
    refine ⟨rfl, fun c hc => ?_⟩
    obtain ⟨j, hj, hjc⟩ := mem_projFrom hc
    have := findMatchFrom_none hf j (by omega) (by omega)
    unfold matchesAt at this
    rw [Nat.zero_add] at hjc
    rw [hjc] at this
    exact this

/-- **RB6**, match half: `ring_remove_matching` removes *exactly the first*
token satisfying `pred` — the projection splits as `pre ++ c :: post` with
every `pre` element failing the predicate, and the survivor list is
`pre ++ post` in order. Both compaction directions land on the same list, and
the result is well-formed. Other places are untouched. -/
theorem removeMatching_some {s : Pool} (hwf : WF s) {p : PlaceId}
    (hp : p < s.nplaces) {pred : Colour → Bool} {c : Colour}
    (h : (s.removeMatching p pred).1 = some c) :
    pred c = true ∧
    ∃ pre post,
      s.proj p = pre ++ c :: post ∧
      (∀ c' ∈ pre, pred c' = false) ∧
      (s.removeMatching p pred).2.proj p = pre ++ post ∧
      (∀ q, q < s.nplaces → q ≠ p → (s.removeMatching p pred).2.proj q = s.proj q) ∧
      WF (s.removeMatching p pred).2 := by
  unfold removeMatching at h ⊢
  cases hf : s.findMatch p pred with
  | none =>
    rw [hf] at h
    change (none : Option Colour) = some c at h
    cases h
  | some i =>
    rw [hf] at h
    change s.pool (s.slot p i) = some c at h
    obtain ⟨_, hlt, hm, hearlier⟩ := findMatchFrom_some hf
    rw [Nat.zero_add] at hlt
    obtain ⟨c', hc', hpred⟩ := matchesAt_true hm
    have hcc : c' = c := by
      rw [hc'] at h
      exact Option.some.inj h
    subst hcc
    refine ⟨hpred, s.projFrom p 0 i, s.projFrom p (i + 1) (s.cnt p - 1 - i),
      proj_split hwf hp hlt hc', ?_, ?_, ?_, ?_⟩
    · intro c'' hc''
      obtain ⟨j, hj, hjc⟩ := mem_projFrom hc''
      have := hearlier j (by omega) (by omega)
      unfold matchesAt at this
      rw [Nat.zero_add] at hjc
      rw [hjc] at this
      exact this
    · show (if i ≤ s.cnt p - 1 - i then s.headSlideAt p i else s.tailSlideAt p i).proj p
          = s.projFrom p 0 i ++ s.projFrom p (i + 1) (s.cnt p - 1 - i)
      by_cases hside : i ≤ s.cnt p - 1 - i
      · rw [if_pos hside]
        exact headSlideAt_proj_self hwf hp hlt
      · rw [if_neg hside]
        exact tailSlideAt_proj_self hwf hp hlt
    · intro q hq hne
      show (if i ≤ s.cnt p - 1 - i then s.headSlideAt p i else s.tailSlideAt p i).proj q
          = s.proj q
      by_cases hside : i ≤ s.cnt p - 1 - i
      · rw [if_pos hside]
        exact headSlideAt_proj_other hwf hp hq hne i
      · rw [if_neg hside]
        exact tailSlideAt_proj_other hwf hp hq hne i
    · show WF (if i ≤ s.cnt p - 1 - i then s.headSlideAt p i else s.tailSlideAt p i)
      by_cases hside : i ≤ s.cnt p - 1 - i
      · rw [if_pos hside]
        exact headSlideAt_wf hwf hp hlt
      · rw [if_neg hside]
        exact tailSlideAt_wf hwf hp hlt

end Pool

end Libpetri
