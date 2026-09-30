import Libpetri.Novel.Seam.Index

/-!
# Where a token may rest: `stranding_excuses` ([VER-002], [VER-014])

`rest_set.rs` `stranding_excuses` computes, per flat place, how a token resting there is excused:
`None` when it never counts as stranded (a declared sink, or a marker), otherwise the flat
indices of the markers whose presence excuses it. It is an imperative loop over a vector, with
two subtleties: names that do not resolve in the flat net are skipped (an unresolved sink
excuses nothing, an unresolved marker excuses nothing), and `None` is absorbing — a place that
becomes a marker later loses the markers it collected earlier.

`strandingExcuses` is that loop, statement for statement, over `Nat → Option (List Nat)` for the
vector. The final `sort_unstable` of each list is omitted: the encoder reads the list only
through membership (`(= marker 0)` per entry), so order is invisible. `strandingExcuses_spec`
characterises the result by name.
-/

namespace Libpetri.Novel.Seam

variable {N : Type} [DecidableEq N]

/-- `rest_set.rs` `ConditionalSinks`: places where a token may rest while `marker` is marked. -/
structure CondSinks (N : Type) where
  marker : N
  places : List N

/-- The `excuses` vector, by flat index. -/
abbrev Excuses := Nat → Option (List Nat)

/-- `excuses[i] = v`. -/
def setAt (e : Excuses) (i : Nat) (v : Option (List Nat)) : Excuses :=
  fun j => if j = i then v else e j

/-- The sink loop body: `if let Some(&pid) = flat.place_index.get(sink) { excuses[pid] = None }`. -/
def sinkStep (ix : PlaceIndex N) (e : Excuses) (sink : N) : Excuses :=
  match ix.lookup sink with
  | some pid => setAt e pid none
  | none => e

/-- The inner loop body: push `mid` onto a still-`Some` entry of a resolving place. -/
def placeStep (ix : PlaceIndex N) (mid : Nat) (e : Excuses) (p : N) : Excuses :=
  match ix.lookup p with
  | none => e
  | some pid =>
    match e pid with
    | some l => setAt e pid (some (if mid ∈ l then l else l ++ [mid]))
    | none => e

/-- The outer loop body: skip an unresolved marker, else clear the marker's entry and walk the
places. -/
def entryStep (ix : PlaceIndex N) (e : Excuses) (c : CondSinks N) : Excuses :=
  match ix.lookup c.marker with
  | none => e
  | some mid => c.places.foldl (placeStep ix mid) (setAt e mid none)

/-- `rest_set.rs` `stranding_excuses` (up to the final per-list sort). -/
def strandingExcuses (ix : PlaceIndex N) (sinks : List N) (cond : List (CondSinks N)) : Excuses :=
  cond.foldl (entryStep ix) (sinks.foldl (sinkStep ix) (fun _ => some []))

/-- `n` is the marker of some conditional declaration. -/
def IsMarker (cond : List (CondSinks N)) (n : N) : Prop := ∃ c ∈ cond, c.marker = n

/-- A token on `n` is excused by the marker at flat index `k`. -/
def ExcusedBy (ix : PlaceIndex N) (cond : List (CondSinks N)) (n : N) (k : Nat) : Prop :=
  ∃ c ∈ cond, c.marker ∈ ix.names ∧ ix.idx c.marker = k ∧ n ∈ c.places

/-- What the vector means, by name, for every indexed place. -/
structure ExcuseSpec (ix : PlaceIndex N) (sinks : List N) (cond : List (CondSinks N))
    (e : Excuses) : Prop where
  none_iff : ∀ i n, ix.name? i = some n → (e i = none ↔ n ∈ sinks ∨ IsMarker cond n)
  mem_iff : ∀ i n l, ix.name? i = some n → e i = some l → ∀ k, (k ∈ l ↔ ExcusedBy ix cond n k)

section Proofs

variable (ix : PlaceIndex N)

theorem name_eq_of_idx {i : Nat} {n n' : N} (hi : ix.name? i = some n) (hn' : n' ∈ ix.names)
    (he : ix.idx n' = i) : n' = n := by
  rw [← ix.idx_of_name? hi] at he
  exact (ix.idx_inj hn').mp he

theorem idx_ne_of_ne {i : Nat} {n n' : N} (hi : ix.name? i = some n) (hne : n' ≠ n) :
    ix.idx n' ≠ i := by
  intro he
  have hmem : n' ∈ ix.names := by
    by_contra hn
    have hsz := List.idxOf_eq_length_iff.mpr hn
    have hlt := ix.idx_lt (ix.mem_of_name? hi)
    rw [ix.idx_of_name? hi] at hlt
    unfold PlaceIndex.idx at he
    unfold PlaceIndex.size at hlt
    omega
  exact hne (name_eq_of_idx ix hi hmem he)

theorem sinkStep_spec {pre : List N} {e : Excuses} (h : ExcuseSpec ix pre [] e) (s : N) :
    ExcuseSpec ix (pre ++ [s]) [] (sinkStep ix e s) := by
  cases hl : ix.lookup s with
  | none =>
    have hstep : sinkStep ix e s = e := by simp [sinkStep, hl]
    rw [hstep]
    have hs := ix.lookup_eq_none.mp hl
    refine ⟨fun i n hi => ?_, fun i n l hi he k => h.mem_iff i n l hi he k⟩
    have hne : n ≠ s := fun he => hs (he ▸ ix.mem_of_name? hi)
    rw [h.none_iff i n hi]
    simp [hne]
  | some pid =>
    have hstep : sinkStep ix e s = setAt e pid none := by simp [sinkStep, hl]
    rw [hstep]
    obtain ⟨hs, hpid⟩ := ix.lookup_eq_some.mp hl
    refine ⟨fun i n hi => ?_, fun i n l hi he k => ?_⟩
    · unfold setAt
      by_cases hip : i = pid
      · subst hip
        have : s = n := name_eq_of_idx ix hi hs hpid
        simp [this]
      · have hne : n ≠ s := fun he => hip (by rw [← hpid, ← he, ix.idx_of_name? hi])
        rw [if_neg hip, h.none_iff i n hi]
        simp [hne]
    · unfold setAt at he
      by_cases hip : i = pid
      · rw [if_pos hip] at he; exact absurd he (by simp)
      · rw [if_neg hip] at he
        exact h.mem_iff i n l hi he k

theorem sinks_spec : ∀ (S pre : List N) (e : Excuses), ExcuseSpec ix pre [] e →
    ExcuseSpec ix (pre ++ S) [] (S.foldl (sinkStep ix) e)
  | [], pre, e, h => by simpa using h
  | s :: S, pre, e, h => by
    have := sinks_spec S (pre ++ [s]) _ (sinkStep_spec ix h s)
    simpa using this

theorem placeStep_spec (mid : Nat) (e : Excuses) (p : N) (i : Nat) :
    (placeStep ix mid e p i = none ↔ e i = none) ∧
    ∀ l', placeStep ix mid e p i = some l' → ∃ l, e i = some l ∧
      ∀ k, (k ∈ l' ↔ k ∈ l ∨ (k = mid ∧ ix.lookup p = some i)) := by
  cases hl : ix.lookup p with
  | none =>
    have hstep : placeStep ix mid e p = e := by simp [placeStep, hl]
    rw [hstep]
    refine ⟨Iff.rfl, fun l' he => ⟨l', he, fun k => ?_⟩⟩
    simp
  | some pid =>
    cases hep : e pid with
    | none =>
      have hstep : placeStep ix mid e p = e := by simp [placeStep, hl, hep]
      rw [hstep]
      refine ⟨Iff.rfl, fun l' he => ⟨l', he, fun k => ?_⟩⟩
      constructor
      · exact Or.inl
      · rintro (hk | ⟨-, hpi⟩)
        · exact hk
        · have : pid = i := Option.some.inj hpi
          subst this
          rw [hep] at he; exact absurd he (by simp)
    | some l0 =>
      have hstep : placeStep ix mid e p = setAt e pid (some (if mid ∈ l0 then l0 else l0 ++ [mid])) := by
        simp [placeStep, hl, hep]
      rw [hstep]
      unfold setAt
      by_cases hip : i = pid
      · subst hip
        refine ⟨by simp [hep], fun l' he => ⟨l0, hep, fun k => ?_⟩⟩
        simp only [if_true, Option.some.injEq] at he
        subst he
        by_cases hm : mid ∈ l0
        · simp only [hm, if_true]
          constructor
          · exact Or.inl
          · rintro (hk | ⟨rfl, -⟩)
            · exact hk
            · exact hm
        · simp only [hm, if_false, List.mem_append, List.mem_singleton]
          simp
      · rw [if_neg hip]
        refine ⟨Iff.rfl, fun l' he => ⟨l', he, fun k => ?_⟩⟩
        constructor
        · exact Or.inl
        · rintro (hk | ⟨-, hpi⟩)
          · exact hk
          · exact absurd (Option.some.inj hpi).symm hip

theorem places_spec (mid : Nat) : ∀ (P : List N) (e : Excuses) (i : Nat),
    ((P.foldl (placeStep ix mid) e) i = none ↔ e i = none) ∧
    ∀ l', (P.foldl (placeStep ix mid) e) i = some l' → ∃ l, e i = some l ∧
      ∀ k, (k ∈ l' ↔ k ∈ l ∨ (k = mid ∧ ∃ p ∈ P, ix.lookup p = some i))
  | [], e, i => ⟨Iff.rfl, fun l' he => ⟨l', he, fun k => by simp⟩⟩
  | p :: P, e, i => by
    obtain ⟨h1, h2⟩ := places_spec mid P (placeStep ix mid e p) i
    obtain ⟨g1, g2⟩ := placeStep_spec ix mid e p i
    refine ⟨h1.trans g1, fun l'' he => ?_⟩
    obtain ⟨l', he', hk'⟩ := h2 l'' he
    obtain ⟨l, hel, hk⟩ := g2 l' he'
    refine ⟨l, hel, fun k => ?_⟩
    rw [hk', hk]
    simp only [List.mem_cons, exists_eq_or_imp]
    tauto

theorem entryStep_spec {sinks : List N} {pre : List (CondSinks N)} {e : Excuses}
    (h : ExcuseSpec ix sinks pre e) (c : CondSinks N) :
    ExcuseSpec ix sinks (pre ++ [c]) (entryStep ix e c) := by
  cases hl : ix.lookup c.marker with
  | none =>
    have hstep : entryStep ix e c = e := by simp [entryStep, hl]
    rw [hstep]
    have hc := ix.lookup_eq_none.mp hl
    refine ⟨fun i n hi => ?_, fun i n l hi he k => ?_⟩
    · have hne : c.marker ≠ n := fun he => hc (he ▸ ix.mem_of_name? hi)
      rw [h.none_iff i n hi]
      simp [IsMarker, hne]
    · rw [h.mem_iff i n l hi he k]
      simp [ExcusedBy, hc]
  | some mid =>
    have hstep : entryStep ix e c = c.places.foldl (placeStep ix mid) (setAt e mid none) := by
      simp [entryStep, hl]
    rw [hstep]
    obtain ⟨hc, hmid⟩ := ix.lookup_eq_some.mp hl
    refine ⟨fun i n hi => ?_, fun i n l hi he k => ?_⟩
    · rw [(places_spec ix mid c.places _ i).1]
      unfold setAt
      by_cases hip : i = mid
      · subst hip
        have : c.marker = n := name_eq_of_idx ix hi hc hmid
        simp [IsMarker, this]
      · have hne : c.marker ≠ n := fun he => hip (by rw [← hmid, he, ix.idx_of_name? hi])
        rw [if_neg hip, h.none_iff i n hi]
        simp [IsMarker, hne]
    · obtain ⟨l1, he1, hk⟩ := (places_spec ix mid c.places _ i).2 l he
      unfold setAt at he1
      by_cases hip : i = mid
      · rw [if_pos hip] at he1; exact absurd he1 (by simp)
      · rw [if_neg hip] at he1
        rw [hk, h.mem_iff i n l1 hi he1 k]
        have hlook : (∃ p ∈ c.places, ix.lookup p = some i) ↔ n ∈ c.places := by
          constructor
          · rintro ⟨p, hp, hpl⟩
            obtain ⟨hpm, hpi⟩ := ix.lookup_eq_some.mp hpl
            exact (name_eq_of_idx ix hi hpm hpi) ▸ hp
          · intro hn
            exact ⟨n, hn, ix.lookup_eq_some.mpr ⟨ix.mem_of_name? hi, ix.idx_of_name? hi⟩⟩
        rw [hlook]
        simp only [ExcusedBy, List.mem_append, List.mem_singleton]
        constructor
        · rintro (⟨c', hc', h1, h2, h3⟩ | ⟨rfl, hn⟩)
          · exact ⟨c', Or.inl hc', h1, h2, h3⟩
          · exact ⟨c, Or.inr rfl, hc, hmid, hn⟩
        · rintro ⟨c', (hc' | rfl), h1, h2, h3⟩
          · exact Or.inl ⟨c', hc', h1, h2, h3⟩
          · exact Or.inr ⟨by rw [← h2, hmid], h3⟩

theorem conds_spec {sinks : List N} : ∀ (C pre : List (CondSinks N)) (e : Excuses),
    ExcuseSpec ix sinks pre e → ExcuseSpec ix sinks (pre ++ C) (C.foldl (entryStep ix) e)
  | [], pre, e, h => by simpa using h
  | c :: C, pre, e, h => by
    have := conds_spec C (pre ++ [c]) _ (entryStep_spec ix h c)
    simpa using this

/-- **`stranding_excuses` by name.** For every indexed place `n`: its entry is `None` iff `n` is a
declared sink or a marker, and otherwise holds exactly the indices of the resolving markers
whose declarations name `n`. -/
theorem strandingExcuses_spec (sinks : List N) (cond : List (CondSinks N)) :
    ExcuseSpec ix sinks cond (strandingExcuses ix sinks cond) := by
  have h0 : ExcuseSpec ix [] [] (fun _ => some []) :=
    ⟨fun _ _ _ => by simp [IsMarker], fun _ _ l _ he k => by
      cases he; simp [ExcusedBy]⟩
  have hs := sinks_spec ix sinks [] _ h0
  simp only [List.nil_append] at hs
  have := conds_spec ix cond [] _ hs
  simpa [strandingExcuses] using this

end Proofs

end Libpetri.Novel.Seam
