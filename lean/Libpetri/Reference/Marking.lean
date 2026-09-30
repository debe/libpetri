import Mathlib.Data.String.Basic

/-!
# Canonical markings: sorted association lists without zero entries

The reference keys a marking by place name. A marking is a list of `(place, count)` entries;
`get m p` is the count of `p`, `0` for a name without an entry. The **canonical** form
(`Canon`) keeps the entries strictly sorted by name and drops every zero count, so two
canonical lists are equal exactly when they hold the same counts (`ext`). That is what lets the
explorer deduplicate markings by list equality and hashing.

`set m p v` writes one count and keeps the form canonical (`get_set`, `canon_set`).
-/

namespace Libpetri.Reference

variable {K : Type} [LinearOrder K]

/-- A marking: `(place, count)` entries. -/
abbrev Marking (K : Type) := List (K × Nat)

/-- The count of `q`: the first entry for `q`, or `0`. -/
def get : Marking K → K → Nat
  | [], _ => 0
  | (k, v) :: rest, q => if k = q then v else get rest q

/-- Strictly sorted by name, no zero count. -/
def Canon (m : Marking K) : Prop :=
  (m.map Prod.fst).Pairwise (· < ·) ∧ ∀ e ∈ m, e.2 ≠ 0

/-- Write count `v` for `k`: insert, replace, or (for `v = 0`) remove the entry. -/
def set : Marking K → K → Nat → Marking K
  | [], k, v => if v = 0 then [] else [(k, v)]
  | (k', v') :: rest, k, v =>
    if k < k' then (if v = 0 then (k', v') :: rest else (k, v) :: (k', v') :: rest)
    else if k = k' then (if v = 0 then rest else (k, v) :: rest)
    else (k', v') :: set rest k v

/-- The canonical marking holding the given counts (later entries win). -/
def ofList (l : List (K × Nat)) : Marking K :=
  l.foldl (fun m e => set m e.1 e.2) []

/-! ## Lemmas -/

theorem canon_nil : Canon ([] : Marking K) := ⟨List.Pairwise.nil, fun _ h => absurd h List.not_mem_nil⟩

theorem canon_cons {k : K} {v : Nat} {rest : Marking K} :
    Canon ((k, v) :: rest) ↔ (∀ e ∈ rest, k < e.1) ∧ v ≠ 0 ∧ Canon rest := by
  unfold Canon
  simp only [List.map_cons, List.pairwise_cons, List.mem_map, List.mem_cons, forall_eq_or_imp]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨fun e he => h1 _ ⟨e, he, rfl⟩, h3, h2, h4⟩
  · rintro ⟨h1, h3, h2, h4⟩
    exact ⟨⟨fun a ⟨e, he, hea⟩ => hea ▸ h1 e he, h2⟩, h3, h4⟩

theorem get_eq_zero_of_forall_ne {m : Marking K} {q : K} (h : ∀ e ∈ m, e.1 ≠ q) :
    get m q = 0 := by
  induction m with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨k, v⟩ := e
    simp only [get]
    rw [if_neg (h (k, v) List.mem_cons_self)]
    exact ih (fun e he => h e (List.mem_cons_of_mem _ he))

/-- Below the head's name, the tail holds nothing. -/
theorem get_tail_of_le {k q : K} {v : Nat} {rest : Marking K} (hc : Canon ((k, v) :: rest))
    (hq : q ≤ k) : get rest q = 0 :=
  get_eq_zero_of_forall_ne fun e he heq =>
    absurd (heq ▸ (canon_cons.mp hc).1 e he) (not_lt.mpr hq)

theorem mem_set {m : Marking K} {k : K} {v : Nat} {e : K × Nat} (h : e ∈ set m k v) :
    (e = (k, v) ∧ v ≠ 0) ∨ e ∈ m := by
  induction m with
  | nil =>
    simp only [set] at h
    split at h
    · exact absurd h List.not_mem_nil
    · rename_i hv
      exact Or.inl ⟨List.mem_singleton.mp h, hv⟩
  | cons x rest ih =>
    obtain ⟨k', v'⟩ := x
    simp only [set] at h
    split at h
    · split at h
      · exact Or.inr h
      · rename_i hv
        rcases List.mem_cons.mp h with h | h
        · exact Or.inl ⟨h, hv⟩
        · exact Or.inr h
    · split at h
      · split at h
        · exact Or.inr (List.mem_cons_of_mem _ h)
        · rename_i hv
          rcases List.mem_cons.mp h with h | h
          · exact Or.inl ⟨h, hv⟩
          · exact Or.inr (List.mem_cons_of_mem _ h)
      · rcases List.mem_cons.mp h with h | h
        · exact Or.inr (h ▸ List.mem_cons_self)
        · rcases ih h with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem _ h)

theorem canon_set : ∀ {m : Marking K}, Canon m → ∀ (k : K) (v : Nat), Canon (set m k v)
  | [], _, k, v => by
    simp only [set]
    split
    · exact canon_nil
    · rename_i hv
      exact canon_cons.mpr ⟨fun _ h => absurd h List.not_mem_nil, hv, canon_nil⟩
  | (k', v') :: rest, hc, k, v => by
    obtain ⟨hlt, hv', hrest⟩ := canon_cons.mp hc
    simp only [set]
    split
    · rename_i hkk
      split
      · exact hc
      · rename_i hv
        refine canon_cons.mpr ⟨fun e he => ?_, hv, hc⟩
        rcases List.mem_cons.mp he with rfl | he
        · exact hkk
        · exact lt_trans hkk (hlt e he)
    · split
      · rename_i hkk
        split
        · exact hrest
        · rename_i hv
          exact canon_cons.mpr ⟨fun e he => hkk ▸ hlt e he, hv, hrest⟩
      · rename_i hkk1 hkk2
        have hgt : k' < k := lt_of_le_of_ne (not_lt.mp hkk1) (Ne.symm hkk2)
        refine canon_cons.mpr ⟨fun e he => ?_, hv', canon_set hrest k v⟩
        rcases mem_set he with ⟨rfl, _⟩ | he
        · exact hgt
        · exact hlt e he

/-- **Reading after a write.** -/
theorem get_set : ∀ {m : Marking K}, Canon m → ∀ (k : K) (v : Nat) (q : K),
    get (set m k v) q = if q = k then v else get m q
  | [], _, k, v, q => by
    simp only [set]
    split
    · rename_i hv
      subst hv
      split <;> rfl
    · simp only [get]
      by_cases hq : q = k
      · subst hq; simp
      · simp [hq, Ne.symm hq]
  | (k', v') :: rest, hc, k, v, q => by
    have hrest := (canon_cons.mp hc).2.2
    simp only [set]
    split
    · rename_i hkk
      split
      · rename_i hv
        subst hv
        by_cases hq : q = k
        · subst hq
          rw [if_pos rfl]
          simp only [get]
          rw [if_neg (ne_of_gt hkk), get_tail_of_le hc (le_of_lt hkk)]
        · rw [if_neg hq]
      · simp only [get]
        by_cases hq : q = k
        · subst hq; simp
        · simp [hq, Ne.symm hq]
    · split
      · rename_i hkk
        subst hkk
        split
        · rename_i hv
          subst hv
          by_cases hq : q = k
          · subst hq
            simp only [get, if_true]
            exact get_tail_of_le hc le_rfl
          · simp only [get]
            rw [if_neg hq, if_neg (Ne.symm hq)]
        · simp only [get]
          by_cases hq : q = k
          · subst hq; simp
          · simp [hq, Ne.symm hq]
      · rename_i hkk1 hkk2
        simp only [get]
        rw [get_set hrest k v q]
        by_cases hq : k' = q
        · subst hq
          rw [if_pos rfl, if_pos rfl, if_neg (Ne.symm hkk2)]
        · rw [if_neg hq, if_neg hq]

/-- An entry of a canonical marking is its count. -/
theorem get_of_mem : ∀ {m : Marking K}, Canon m → ∀ {q : K} {v : Nat}, (q, v) ∈ m → get m q = v
  | [], _, _, _, h => absurd h List.not_mem_nil
  | (k', v') :: rest, hc, q, v, h => by
    obtain ⟨hlt, _, hrest⟩ := canon_cons.mp hc
    simp only [get]
    rcases List.mem_cons.mp h with h | h
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp
    · rw [if_neg (ne_of_lt (hlt _ h)), get_of_mem hrest h]

/-- A nonzero count comes from an entry. -/
theorem mem_of_get_ne_zero : ∀ {m : Marking K} {q : K}, get m q ≠ 0 → (q, get m q) ∈ m
  | [], _, h => absurd rfl h
  | (k', v') :: rest, q, h => by
    simp only [get] at h ⊢
    by_cases hq : k' = q
    · subst hq
      simp
    · rw [if_neg hq] at h ⊢
      exact List.mem_cons_of_mem _ (mem_of_get_ne_zero h)

/-- The marked names of a canonical marking are its entries. -/
theorem get_ne_zero_iff {m : Marking K} (hc : Canon m) {q : K} :
    get m q ≠ 0 ↔ q ∈ m.map Prod.fst := by
  constructor
  · intro h
    exact List.mem_map.mpr ⟨_, mem_of_get_ne_zero h, rfl⟩
  · intro h
    obtain ⟨⟨q', v⟩, hm, rfl⟩ := List.mem_map.mp h
    rw [get_of_mem hc hm]
    exact hc.2 _ hm

/-- **Canonical markings are equal iff they hold the same counts.** -/
theorem ext : ∀ {a b : Marking K}, Canon a → Canon b → (∀ q, get a q = get b q) → a = b
  | [], [], _, _, _ => rfl
  | [], (k, v) :: _, _, hb, h => by
    have := h k
    simp only [get, if_true] at this
    exact absurd this.symm (canon_cons.mp hb).2.1
  | (k, v) :: _, [], ha, _, h => by
    have := h k
    simp only [get, if_true] at this
    exact absurd this (canon_cons.mp ha).2.1
  | (k1, v1) :: r1, (k2, v2) :: r2, ha, hb, h => by
    obtain ⟨_, hv1, hr1⟩ := canon_cons.mp ha
    obtain ⟨_, hv2, hr2⟩ := canon_cons.mp hb
    rcases lt_trichotomy k1 k2 with hlt | heq | hgt
    · have := h k1
      simp only [get, if_true] at this
      rw [if_neg (ne_of_gt hlt), get_tail_of_le hb (le_of_lt hlt)] at this
      exact absurd this hv1
    · subst heq
      have hv := h k1
      simp only [get, if_true] at hv
      subst hv
      have hr : ∀ q, get r1 q = get r2 q := fun q => by
        by_cases hq : q = k1
        · subst hq
          rw [get_tail_of_le ha le_rfl, get_tail_of_le hb le_rfl]
        · have := h q
          simp only [get] at this
          rwa [if_neg (Ne.symm hq), if_neg (Ne.symm hq)] at this
      rw [ext hr1 hr2 hr]
    · have := h k2
      simp only [get, if_true] at this
      rw [if_neg (ne_of_gt hgt), get_tail_of_le ha (le_of_lt hgt)] at this
      exact absurd this.symm hv2

/-- Writing a list of places, each to `F p`, from a canonical start. -/
theorem foldl_set : ∀ (L : List K) (F : K → Nat) {acc : Marking K}, Canon acc →
    Canon (L.foldl (fun a p => set a p (F p)) acc) ∧
      ∀ q, get (L.foldl (fun a p => set a p (F p)) acc) q = if q ∈ L then F q else get acc q
  | [], _, acc, hc => ⟨hc, fun q => by simp⟩
  | p :: ps, F, acc, hc => by
    obtain ⟨hc', hg⟩ := foldl_set ps F (canon_set hc p (F p))
    refine ⟨hc', fun q => ?_⟩
    simp only [List.foldl_cons]
    rw [hg q, get_set hc]
    by_cases hq : q ∈ ps
    · simp [hq]
    · by_cases hqp : q = p
      · subst hqp; simp
      · simp [hq, hqp]

theorem canon_ofList (l : List (K × Nat)) : Canon (ofList l) := by
  unfold ofList
  suffices ∀ (l : List (K × Nat)) (acc : Marking K), Canon acc →
      Canon (l.foldl (fun m e => set m e.1 e.2) acc) from this l [] canon_nil
  intro l
  induction l with
  | nil => exact fun _ h => h
  | cons e es ih => exact fun acc h => ih _ (canon_set h e.1 e.2)

end Libpetri.Reference
