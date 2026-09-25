/-
# Token bags and the per-opcode token loop

`TokenBag` and `popN` (iterated `ring_remove_first`), split out of
`Conservation.lean`, which builds the opcode interpreter on them.
-/
import Libpetri.Compile

namespace Libpetri

/-- Per-place token lists accumulated during a firing — the Lean image of the
executor's pooled `inputs: HashMap<Arc<str>, Vec<ErasedToken>>` and of the
`emit_removed` stream restricted to RESET removals. -/
abbrev TokenBag := PlaceId → List Colour

def emptyBag : TokenBag := fun _ => []

def addBag (b : TokenBag) (p : PlaceId) (l : List Colour) : TokenBag :=
  fun q => if q = p then b q ++ l else b q

@[simp] theorem addBag_self (b : TokenBag) (p : PlaceId) (l : List Colour) :
    addBag b p l p = b p ++ l := by simp [addBag]
theorem addBag_other (b : TokenBag) {p q : PlaceId} (l : List Colour)
    (hne : q ≠ p) : addBag b p l q = b q := by simp [addBag, hne]

/-! ## `ring_remove_first` iterated: the per-opcode token loop -/

/-- `k` iterations of `ring_remove_first` at one place, collecting the
removed tokens in removal (= FIFO) order. This is the body of every consume
opcode's `for _ in 0..count` loop. -/
def popN (s : Pool) (p : PlaceId) : Nat → Pool × List Colour
  | 0 => (s, [])
  | k + 1 =>
    let c := s.first p
    let rest := popN (s.removeFirst p) p k
    (rest.1, c.toList ++ rest.2)

/-- A non-empty ring projects as a cons, headed by `first`. -/
theorem proj_cons {s : Pool} (hwf : Pool.WF s) {p : PlaceId}
    (hp : p < s.nplaces) (hcnt : 0 < s.cnt p) :
    ∃ c rest, s.first p = some c ∧ s.proj p = c :: rest := by
  obtain ⟨c, hc, _⟩ := Pool.toList_of_isSome (Pool.first_isSome hwf hp hcnt)
  have hhead := Pool.first_eq_head hwf hp hcnt
  rw [hc] at hhead
  cases hproj : s.proj p with
  | nil => rw [hproj] at hhead; cases hhead
  | cons a rest =>
    rw [hproj] at hhead
    have hca : c = a := Option.some.inj hhead
    exact ⟨c, rest, hc, by rw [hca]⟩

/-- The full spec of `popN`: totality (WF out), FIFO faithfulness (the
collected tokens are `take k`, the survivors `drop k`), the frame on other
places, and the count bookkeeping. -/
theorem popN_spec {s : Pool} (hwf : Pool.WF s) {p : PlaceId}
    (hp : p < s.nplaces) {k : Nat} (hk : k ≤ s.cnt p) :
    Pool.WF (popN s p k).1 ∧
    (popN s p k).1.nplaces = s.nplaces ∧
    (popN s p k).2 = (s.proj p).take k ∧
    (popN s p k).1.proj p = (s.proj p).drop k ∧
    (∀ q, q < s.nplaces → q ≠ p → (popN s p k).1.proj q = s.proj q) ∧
    (∀ q, (popN s p k).1.cnt q = if q = p then s.cnt q - k else s.cnt q) := by
  induction k generalizing s with
  | zero =>
    refine ⟨hwf, rfl, rfl, rfl, fun q _ _ => rfl, fun q => ?_⟩
    by_cases hq : q = p <;> simp [popN, hq]
  | succ k ih =>
    have hcnt : 0 < s.cnt p := by omega
    obtain ⟨c, rest, hc, hproj⟩ := proj_cons hwf hp hcnt
    have hwf' := Pool.removeFirst_wf hwf hp hcnt
    obtain ⟨ih1, ih2, ih3, ih4, ih5, ih6⟩ :=
      ih hwf' (by rw [Pool.removeFirst_nplaces]; exact hp)
        (by rw [Pool.removeFirst_cnt_self]; omega)
    have hproj' : (s.removeFirst p).proj p = rest := by
      rw [Pool.removeFirst_proj_self hwf hp hcnt, hproj, List.tail_cons]
    have hstep1 : (popN s p (k + 1)).1 = (popN (s.removeFirst p) p k).1 := rfl
    have hstep2 : (popN s p (k + 1)).2
        = (s.first p).toList ++ (popN (s.removeFirst p) p k).2 := rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hstep1]; exact ih1
    · rw [hstep1, ih2, Pool.removeFirst_nplaces]
    · rw [hstep2, hc, ih3, hproj', hproj]
      rfl
    · rw [hstep1, ih4, hproj', hproj]
      rfl
    · intro q hq hne
      rw [hstep1, ih5 q (by rw [Pool.removeFirst_nplaces]; exact hq) hne,
        Pool.removeFirst_proj_other hwf hp hq hne]
    · intro q
      rw [hstep1, ih6 q]
      by_cases hqp : q = p
      · subst hqp
        rw [if_pos rfl, if_pos rfl, Pool.removeFirst_cnt_self]
        omega
      · rw [if_neg hqp, if_neg hqp, Pool.removeFirst_cnt_other s hqp]

end Libpetri
