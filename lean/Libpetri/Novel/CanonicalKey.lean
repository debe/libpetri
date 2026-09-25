import Mathlib.Data.List.Lex
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Finite.Basic
import Mathlib.GroupTheory.Perm.Basic

/-!
# `canonical_key` is a complete invariant of the symbol-renaming orbit

Model of `NameMarking::canonical_key` (`rust/libpetri-verification/src/name_marking.rs`), the
ν-net symmetry reduction ([NU-001]).

* Symbols are `Sym` with a linear order (the raw `Sym` ids), the coloured places are `Fin k`
  in `coloured_order`, and a name marking is `M : Sym → Fin k → ℕ` (token count of symbol `s`
  in place `p`). `live M` are the symbols with a nonzero count somewhere (`live_symbols`); it is
  a `Finset` when that set is finite, which every Rust marking is.
* `sig M s` is the signature, the count vector of `s` over `coloured_order` (`signature`).
* `ranked M` sorts the live `(signature, raw id)` pairs lexicographically (`ranked.sort()`),
  `rank M s` is the position of `s` in it (`rank_of`).
* `entries M p` is the sorted list of `(rank, count)` pairs of the symbols in place `p`
  (`entries.sort()`), and `canonicalKey M` lists them per place in `coloured_order`.

The Rust function renders this list of lists as a string `p:{rxc,…}#…`. The place names are
fixed by `coloured_order` and the rendering is injective, so key-string equality is equality of
`canonicalKey`; the string layer is not modelled.

Results:
* `canonicalKey_eq_iff`: two keys are equal iff the multisets of live signatures are equal;
* `canonicalKey_comp` (invariance): `canonicalKey (M ∘ σ) = canonicalKey M` for every
  `σ : Equiv.Perm Sym`;
* `canonicalKey_complete` (completeness): for finite live supports, equal keys imply
  `N = M ∘ σ` for some permutation `σ` — equality as functions, not only on live symbols;
* `canonicalKey_eq_iff_exists_perm`: the two combined.
-/

namespace Libpetri.Novel.CanonicalKey

variable {Sym : Type*} [LinearOrder Sym] {k : ℕ}

/-- The symbols with a token somewhere (`live_symbols`). -/
def liveSet (M : Sym → Fin k → ℕ) : Set Sym := {s | ∃ p, M s p ≠ 0}

open Classical in
/-- `liveSet` as a `Finset` (empty on an infinite support, which no Rust marking has). -/
noncomputable def live (M : Sym → Fin k → ℕ) : Finset Sym :=
  if h : (liveSet M).Finite then h.toFinset else ∅

/-- The signature of `s`: its count vector over `coloured_order`. -/
def sig (M : Sym → Fin k → ℕ) (s : Sym) : List ℕ := List.ofFn (M s)

/-- `ranked`: the live `(signature, raw id)` pairs, sorted lexicographically. -/
noncomputable def ranked (M : Sym → Fin k → ℕ) : List (List ℕ ×ₗ Sym) :=
  ((live M).val.map fun s => toLex (sig M s, s)).sort

/-- The live symbols in rank order. -/
noncomputable def syms (M : Sym → Fin k → ℕ) : List Sym := (ranked M).map fun x => (ofLex x).2

/-- `rank_of[s]`: the position of `s` in `ranked`. -/
noncomputable def rank (M : Sym → Fin k → ℕ) (s : Sym) : ℕ := (syms M).idxOf s

/-- The sorted `(rank, count)` pairs of the symbols holding tokens in place `p`. -/
noncomputable def entries (M : Sym → Fin k → ℕ) (p : Fin k) : List (ℕ ×ₗ ℕ) :=
  (((live M).filter fun s => M s p ≠ 0).val.map fun s => toLex (rank M s, M s p)).sort

/-- `canonical_key`: the per-place `entries`, in `coloured_order`. -/
noncomputable def canonicalKey (M : Sym → Fin k → ℕ) : List (List (ℕ ×ₗ ℕ)) :=
  List.ofFn (entries M)

/-- The signatures in rank order. -/
noncomputable def sigs (M : Sym → Fin k → ℕ) : List (List ℕ) := (syms M).map (sig M)

/-- Count of the rank-`r` signature in place `p` (`0` past the end). -/
def cnt (L : List (List ℕ)) (r : ℕ) (p : Fin k) : ℕ := (L.getD r []).getD p 0

/-! ### Live symbols and ranks -/

omit [LinearOrder Sym] in
theorem mem_live_of_finite {M : Sym → Fin k → ℕ} (h : (liveSet M).Finite) {s : Sym} :
    s ∈ live M ↔ ∃ p, M s p ≠ 0 := by
  simp only [live, dif_pos h, Set.Finite.mem_toFinset]
  rfl

omit [LinearOrder Sym] in
theorem exists_ne_of_mem_live {M : Sym → Fin k → ℕ} {s : Sym} (hs : s ∈ live M) :
    ∃ p, M s p ≠ 0 := by
  unfold live at hs
  split_ifs at hs with h
  · exact (h.mem_toFinset).1 hs
  · simp at hs

theorem syms_coe (M : Sym → Fin k → ℕ) : ((syms M : List Sym) : Multiset Sym) = (live M).val := by
  rw [syms, ← Multiset.map_coe, ranked, Multiset.sort_eq, Multiset.map_map]
  simp

theorem syms_nodup (M : Sym → Fin k → ℕ) : (syms M).Nodup := by
  rw [← Multiset.coe_nodup, syms_coe]
  exact (live M).nodup

theorem mem_syms {M : Sym → Fin k → ℕ} {s : Sym} : s ∈ syms M ↔ s ∈ live M := by
  rw [← Multiset.mem_coe, syms_coe, Finset.mem_val]

theorem ranked_eq (M : Sym → Fin k → ℕ) :
    ranked M = (syms M).map fun s => toLex (sig M s, s) := by
  rw [syms, List.map_map]
  conv_lhs => rw [← List.map_id (ranked M)]
  refine List.map_congr_left fun x hx => ?_
  rw [ranked, Multiset.mem_sort, Multiset.mem_map] at hx
  obtain ⟨s, -, rfl⟩ := hx
  rfl

theorem rank_lt {M : Sym → Fin k → ℕ} {s : Sym} (hs : s ∈ live M) :
    rank M s < (syms M).length :=
  List.idxOf_lt_length_iff.2 (mem_syms.2 hs)

theorem getElem?_rank {M : Sym → Fin k → ℕ} {s : Sym} (hs : s ∈ live M) :
    (syms M)[rank M s]? = some s := by
  rw [List.getElem?_eq_getElem (rank_lt hs)]
  exact congrArg some (List.getElem_idxOf _)

theorem rank_getElem {M : Sym → Fin k → ℕ} {r : ℕ} (hr : r < (syms M).length) :
    rank M (syms M)[r] = r :=
  (syms_nodup M).idxOf_getElem r hr

theorem rank_injOn {M : Sym → Fin k → ℕ} {s t : Sym} (hs : s ∈ live M) (ht : t ∈ live M)
    (h : rank M s = rank M t) : s = t := by
  have e := getElem?_rank hs
  rw [h, getElem?_rank ht] at e
  exact (Option.some_injective _ e).symm

/-! ### Signatures in rank order -/

theorem length_sigs (M : Sym → Fin k → ℕ) : (sigs M).length = (syms M).length :=
  List.length_map _

theorem sigs_sorted (M : Sym → Fin k → ℕ) : (sigs M).Pairwise (· ≤ ·) := by
  have h : (ranked M).Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
  rw [ranked_eq, List.pairwise_map] at h
  rw [sigs, List.pairwise_map]
  exact h.imp fun hab => Prod.Lex.monotone_fst_ofLex hab

theorem sigs_coe (M : Sym → Fin k → ℕ) :
    ((sigs M : List (List ℕ)) : Multiset (List ℕ)) = (live M).val.map (sig M) := by
  rw [sigs, ← Multiset.map_coe, syms_coe]

/-- The signatures in rank order are the sorted multiset of live signatures. -/
theorem sigs_eq_sort (M : Sym → Fin k → ℕ) : sigs M = ((live M).val.map (sig M)).sort := by
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (sigs_sorted M) (Multiset.pairwise_sort _ _)
  rw [← Multiset.coe_eq_coe, Multiset.sort_eq, sigs_coe]

theorem sigs_eq_iff {M N : Sym → Fin k → ℕ} :
    sigs M = sigs N ↔ (live M).val.map (sig M) = (live N).val.map (sig N) := by
  constructor
  · intro h
    rw [← sigs_coe, ← sigs_coe, h]
  · intro h
    rw [sigs_eq_sort, sigs_eq_sort, h]

theorem cnt_sigs {M : Sym → Fin k → ℕ} {r : ℕ} (hr : r < (syms M).length) (p : Fin k) :
    cnt (sigs M) r p = M (syms M)[r] p := by
  simp [cnt, sigs, sig, hr]

theorem cnt_eq_zero {L : List (List ℕ)} {r : ℕ} (hr : L.length ≤ r) (p : Fin k) :
    cnt L r p = 0 := by
  simp [cnt, List.getElem?_eq_none hr]

theorem getElem_sigs {M : Sym → Fin k → ℕ} {r : ℕ} (hr : r < (sigs M).length) :
    (sigs M)[r] = List.ofFn (fun p : Fin k => cnt (sigs M) r p) := by
  have hr' : r < (syms M).length := by rwa [← length_sigs]
  simp only [cnt_sigs hr']
  simp [sigs, sig]

/-- Every rank belongs to a live symbol, so its row has a nonzero count. -/
theorem exists_cnt_ne {M : Sym → Fin k → ℕ} {r : ℕ} (hr : r < (sigs M).length) :
    ∃ p : Fin k, cnt (sigs M) r p ≠ 0 := by
  have hr' : r < (syms M).length := by rwa [← length_sigs]
  obtain ⟨p, hp⟩ := exists_ne_of_mem_live (mem_syms.1 (List.getElem_mem hr'))
  exact ⟨p, by rwa [cnt_sigs hr']⟩

/-! ### The per-place entries depend only on the signatures in rank order -/

theorem mem_entries {M : Sym → Fin k → ℕ} {p : Fin k} {x : ℕ ×ₗ ℕ} :
    x ∈ entries M p ↔
      ∃ r < (sigs M).length, cnt (sigs M) r p ≠ 0 ∧ x = toLex (r, cnt (sigs M) r p) := by
  simp only [entries, Multiset.mem_sort, Multiset.mem_map, Finset.mem_val, Finset.mem_filter]
  constructor
  · rintro ⟨s, ⟨hs, hp⟩, rfl⟩
    have h1 := rank_lt hs
    have e : (syms M)[rank M s] = s :=
      Option.some_injective _ ((List.getElem?_eq_getElem h1).symm.trans (getElem?_rank hs))
    refine ⟨rank M s, by rwa [length_sigs], ?_⟩
    rw [cnt_sigs h1, e]
    exact ⟨hp, rfl⟩
  · rintro ⟨r, hr, hp, rfl⟩
    have hr' : r < (syms M).length := by rwa [← length_sigs]
    rw [cnt_sigs hr'] at hp ⊢
    refine ⟨(syms M)[r], ⟨mem_syms.1 (List.getElem_mem hr'), hp⟩, ?_⟩
    rw [rank_getElem hr']

theorem toLex_mem_entries {M : Sym → Fin k → ℕ} {p : Fin k} {r c : ℕ} :
    toLex (r, c) ∈ entries M p ↔ cnt (sigs M) r p ≠ 0 ∧ c = cnt (sigs M) r p := by
  rw [mem_entries]
  constructor
  · rintro ⟨r', -, h0, he⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (toLex.injective he)
    exact ⟨h0, rfl⟩
  · rintro ⟨h0, rfl⟩
    refine ⟨r, ?_, h0, rfl⟩
    by_contra hr
    exact h0 (cnt_eq_zero (not_lt.1 hr) p)

theorem entries_pairwise_lt (M : Sym → Fin k → ℕ) (p : Fin k) :
    (entries M p).Pairwise (· < ·) := by
  have hnd : (entries M p).Nodup := by
    rw [← Multiset.coe_nodup, entries, Multiset.sort_eq]
    refine Multiset.Nodup.map_on ?_ (Finset.nodup _)
    intro s hs t ht hst
    simp only [Finset.mem_val, Finset.mem_filter] at hs ht
    exact rank_injOn hs.1 ht.1 (congrArg (fun x => (ofLex x).1) hst)
  exact ((Multiset.pairwise_sort _ _).and hnd).imp fun h => lt_of_le_of_ne h.1 h.2

theorem canonicalKey_eq_of_sigs {M N : Sym → Fin k → ℕ} (h : sigs M = sigs N) :
    canonicalKey M = canonicalKey N := by
  unfold canonicalKey
  congr 1
  funext p
  refine (entries_pairwise_lt M p).eq_of_mem_iff (entries_pairwise_lt N p) fun x => ?_
  rw [mem_entries, mem_entries, h]

theorem sigs_eq_of_canonicalKey {M N : Sym → Fin k → ℕ} (h : canonicalKey M = canonicalKey N) :
    sigs M = sigs N := by
  have hp : ∀ p r c, toLex (r, c) ∈ entries M p ↔ toLex (r, c) ∈ entries N p := by
    intro p r c
    rw [congrFun (List.ofFn_injective h) p]
  have hcnt : ∀ r (p : Fin k), cnt (sigs M) r p = cnt (sigs N) r p := by
    intro r p
    by_cases hM : cnt (sigs M) r p = 0
    · by_cases hN : cnt (sigs N) r p = 0
      · rw [hM, hN]
      · exact (toLex_mem_entries.1 ((hp p r _).2 (toLex_mem_entries.2 ⟨hN, rfl⟩))).2.symm
    · exact (toLex_mem_entries.1 ((hp p r _).1 (toLex_mem_entries.2 ⟨hM, rfl⟩))).2
  have hlen : (sigs M).length = (sigs N).length := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · obtain ⟨p, hp⟩ := exists_cnt_ne hlt
      exact hp (by rw [← hcnt]; exact cnt_eq_zero le_rfl p)
    · obtain ⟨p, hp⟩ := exists_cnt_ne hlt
      exact hp (by rw [hcnt]; exact cnt_eq_zero le_rfl p)
  refine List.ext_getElem hlen fun r h1 h2 => ?_
  rw [getElem_sigs h1, getElem_sigs h2]
  simp only [hcnt]

/-- Equal keys ↔ equal signatures in rank order ↔ equal multisets of live signatures. -/
theorem canonicalKey_eq_iff {M N : Sym → Fin k → ℕ} :
    canonicalKey M = canonicalKey N ↔ (live M).val.map (sig M) = (live N).val.map (sig N) :=
  ⟨fun h => sigs_eq_iff.1 (sigs_eq_of_canonicalKey h),
    fun h => canonicalKey_eq_of_sigs (sigs_eq_iff.2 h)⟩

/-! ### Invariance -/

omit [LinearOrder Sym] in
theorem live_comp (M : Sym → Fin k → ℕ) (σ : Equiv.Perm Sym) :
    live (M ∘ σ) = (live M).map σ.symm.toEmbedding := by
  by_cases h : (liveSet M).Finite
  · have h' : (liveSet (M ∘ σ)).Finite :=
      show (σ ⁻¹' liveSet M).Finite from Set.Finite.preimage σ.injective.injOn h
    ext s
    rw [mem_live_of_finite h', Finset.mem_map_equiv, mem_live_of_finite h]
    simp
  · have h' : ¬ (liveSet (M ∘ σ)).Finite := fun h' => h (by
      have := h'.image σ
      rwa [show liveSet (M ∘ σ) = σ ⁻¹' liveSet M from rfl,
        Set.image_preimage_eq _ σ.surjective] at this)
    simp [live, h, h']

/-- **Invariance.** Renaming symbols by any permutation leaves the key unchanged. -/
theorem canonicalKey_comp (M : Sym → Fin k → ℕ) (σ : Equiv.Perm Sym) :
    canonicalKey (M ∘ σ) = canonicalKey M := by
  rw [canonicalKey_eq_iff, live_comp, Finset.map_val, Multiset.map_map]
  congr 1
  funext s
  simp [sig]

/-! ### Completeness -/

/-- Two duplicate-free lists of equal length are related by a permutation of `Sym`. -/
theorem exists_perm_map_eq : ∀ {a b : List Sym}, a.Nodup → b.Nodup → a.length = b.length →
    ∃ σ : Equiv.Perm Sym, b.map σ = a
  | [], [], _, _, _ => ⟨1, rfl⟩
  | [], _ :: _, _, _, hl => by simp at hl
  | _ :: _, [], _, _, hl => by simp at hl
  | a0 :: a, b0 :: b, ha, hb, hl => by
    rw [List.nodup_cons] at ha hb
    obtain ⟨τ, hτ⟩ := exists_perm_map_eq ha.2 hb.2 (by simpa using hl)
    have hb0 : τ b0 ∉ a := by
      rw [← hτ, List.mem_map]
      rintro ⟨x, hx, hxe⟩
      exact hb.1 (τ.injective hxe ▸ hx)
    refine ⟨Equiv.swap (τ b0) a0 * τ, ?_⟩
    rw [List.map_cons, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_left,
      ← List.map_map, hτ]
    congr 1
    conv_rhs => rw [← List.map_id a]
    refine List.map_congr_left fun x hx => ?_
    exact Equiv.swap_apply_of_ne_of_ne (fun h => hb0 (h ▸ hx)) (fun h => ha.1 (h ▸ hx))

/-- **Completeness.** Markings with finite live support and equal keys lie in one orbit of the
symbol-renaming action. -/
theorem canonicalKey_complete {M N : Sym → Fin k → ℕ} (hM : (liveSet M).Finite)
    (hN : (liveSet N).Finite) (h : canonicalKey M = canonicalKey N) :
    ∃ σ : Equiv.Perm Sym, N = M ∘ σ := by
  have hs := sigs_eq_of_canonicalKey h
  have hlen : (syms M).length = (syms N).length := by
    rw [← length_sigs, ← length_sigs, hs]
  obtain ⟨σ, hσ⟩ := exists_perm_map_eq (syms_nodup M) (syms_nodup N) hlen
  refine ⟨σ, funext fun s => ?_⟩
  by_cases hsN : s ∈ syms N
  · obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hsN
    have hrM : r < (syms M).length := hlen ▸ hr
    have hσr : σ (syms N)[r] = (syms M)[r] :=
      ((List.getElem_of_eq hσ.symm hrM).trans (List.getElem_map _)).symm
    have e : (sigs M)[r]'(by rwa [length_sigs]) = (sigs N)[r]'(by rwa [length_sigs]) :=
      List.getElem_of_eq hs _
    simp only [sigs, List.getElem_map, sig] at e
    rw [Function.comp_apply, hσr, List.ofFn_injective e]
  · have hσs : σ s ∉ syms M := by
      rw [← hσ, List.mem_map]
      rintro ⟨x, hx, hxs⟩
      exact hsN (σ.injective hxs ▸ hx)
    funext p
    have h1 : N s p = 0 := by
      by_contra hne
      exact hsN (mem_syms.2 ((mem_live_of_finite hN).2 ⟨p, hne⟩))
    have h2 : M (σ s) p = 0 := by
      by_contra hne
      exact hσs (mem_syms.2 ((mem_live_of_finite hM).2 ⟨p, hne⟩))
    rw [h1, Function.comp_apply, h2]

/-- Orbit characterisation: on finite live supports, equal keys ↔ one symbol-renaming orbit. -/
theorem canonicalKey_eq_iff_exists_perm {M N : Sym → Fin k → ℕ} (hM : (liveSet M).Finite)
    (hN : (liveSet N).Finite) :
    canonicalKey M = canonicalKey N ↔ ∃ σ : Equiv.Perm Sym, N = M ∘ σ :=
  ⟨canonicalKey_complete hM hN, fun ⟨σ, hσ⟩ => hσ ▸ (canonicalKey_comp M σ).symm⟩

end Libpetri.Novel.CanonicalKey
