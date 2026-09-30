import Libpetri.Novel.CanonicalKey
import Libpetri.Basic

/-!
# Route B, the name layer: `NameMarking`, the role steps and the orbit dedup ([NU-050], [VER-012])

Model of `rust/libpetri-verification/src/name_marking.rs` (`NameMarking`: `add`, `remove`,
`count_of`, `symbols_in`, `canonical_key`) and of the symbol-level half of `name_successors`
(`name_state_class_graph.rs`): `enabling_symbols`, `distinct_signatures`, and the per-symbol
update each role applies.

* A name marking is `M : ℕ → Fin co.length → ℕ`: `M s i` tokens of symbol `s` at the `i`-th place
  of `coloured_order` (`co`). The Rust map is keyed by place name; `idx co p` is the position of
  `p` in `coloured_order`, `none` for an uncoloured place. Every `add` / `remove` the successor
  step issues targets a coloured place (a coloured output, a key, the consumed input, a relay
  target — relay targets are unioned into the coloured set under EXTENDED), so an operation on an
  uncoloured place is modelled as a no-op; the Rust would create a map entry there, which
  `canonical_key` would then read through `live_symbols`. That branch is unreachable from
  `name_successors`, which is the premise the no-op encodes.
* `removeAt` is `NameMarking::remove`: when fewer than `c` tokens are present it leaves the
  marking unchanged (the Rust returns `false` and every caller ignores it).
* `dsig` is `distinct_signatures`, literally: the first symbol of each signature in the given
  order, with the `len < 2` shortcut.

Results:
* `SymStep` — the renaming law `F (σ⁻¹ s) (M ∘ σ) = F s M ∘ σ`. `addAt`, `removeAt` and every
  `foldl` of them satisfy it, so `joinStep` (relay included, [NU-054]), `consumeStep` and
  `mintStep` do (`joinStep_sym`, `consumeStep_sym`, `mintStep_sym`).
* `key_rename` / `key_swap`: for a `SymStep`, the successor's `canonicalKey` is unchanged by a
  renaming of the source, and two symbols with one signature give successors with equal keys.
* `transversal_perm`: any two lists that pick one symbol per signature of an enabling set give
  the same successor keys up to order. `dsig_transversal` shows `distinct_signatures` is such a
  list, and `dedup_perm` combines them across a renaming: the orbit dedup of [VER-012] makes the
  keyed successor list a function of the source key.
* `mint_key`: minting any fresh symbol into two markings with one key gives one key.
-/

namespace Libpetri.Novel.RouteB

open Libpetri
open Libpetri.Novel.CanonicalKey

section NameLayer

variable (co : List PlaceId)

/-- A name marking (`NameMarking`): `M s i` tokens of symbol `s` at the `i`-th coloured place. -/
abbrev NM := ℕ → Fin co.length → ℕ

/-- The position of `p` in `coloured_order`, `none` for an uncoloured place. -/
def idx (p : PlaceId) : Option (Fin co.length) :=
  (List.finRange co.length).find? fun i => co[i.1] == p

/-- `NameMarking::count_of`. -/
def cnt (M : NM co) (s : ℕ) (p : PlaceId) : ℕ :=
  match idx co p with
  | some i => M s i
  | none => 0

/-- `NameMarking::add(p, s, c)`. -/
def addAt (p : PlaceId) (s c : ℕ) (M : NM co) : NM co :=
  match idx co p with
  | some i => fun u j => if u = s ∧ j = i then M u j + c else M u j
  | none => M

/-- `NameMarking::remove(p, s, c)`: unchanged when fewer than `c` are present. -/
def removeAt (p : PlaceId) (s c : ℕ) (M : NM co) : NM co :=
  match idx co p with
  | some i => if c ≤ M s i then (fun u j => if u = s ∧ j = i then M u j - c else M u j) else M
  | none => M

/-- The renaming law of a per-symbol step. -/
def SymStep (F : ℕ → NM co → NM co) : Prop :=
  ∀ (σ : Equiv.Perm ℕ) (s : ℕ) (M : NM co), F (σ.symm s) (M ∘ σ) = F s M ∘ σ

/-- A per-symbol step touches only its symbol's row. -/
def Local (F : ℕ → NM co → NM co) : Prop :=
  ∀ s M u, u ≠ s → F s M u = M u

variable {co}

theorem cnt_comp (M : NM co) (σ : Equiv.Perm ℕ) (s : ℕ) (p : PlaceId) :
    cnt co (M ∘ σ) s p = cnt co M (σ s) p := by
  unfold cnt
  cases idx co p <;> rfl

theorem addAt_sym (p : PlaceId) (c : ℕ) : SymStep co (fun s M => addAt co p s c M) := by
  intro σ s M
  unfold addAt
  cases idx co p with
  | none => rfl
  | some i =>
    funext u j
    simp only [Function.comp]
    have : (u = σ.symm s) ↔ σ u = s := by
      constructor
      · rintro rfl; simp
      · rintro rfl; simp
    by_cases h : σ u = s
    · simp [this.mpr h]
    · have h' : u ≠ σ.symm s := fun e => h (this.mp e)
      simp [h, h']

theorem removeAt_sym (p : PlaceId) (c : ℕ) : SymStep co (fun s M => removeAt co p s c M) := by
  intro σ s M
  unfold removeAt
  cases idx co p with
  | none => rfl
  | some i =>
    have hc : (M ∘ σ) (σ.symm s) i = M s i := by simp
    simp only [hc]
    split
    · funext u j
      simp only [Function.comp]
      by_cases h : σ u = s
      · have h' : u = σ.symm s := by rw [← h]; simp
        simp [h']
      · have h' : u ≠ σ.symm s := fun e => h (by rw [e]; simp)
        simp [h, h']
    · rfl

theorem addAt_local (p : PlaceId) (c : ℕ) : Local co (fun s M => addAt co p s c M) := by
  intro s M u hu
  unfold addAt
  cases idx co p with
  | none => rfl
  | some i => funext j; simp [hu]

theorem removeAt_local (p : PlaceId) (c : ℕ) : Local co (fun s M => removeAt co p s c M) := by
  intro s M u hu
  unfold removeAt
  cases idx co p with
  | none => rfl
  | some i =>
    by_cases hc : c ≤ M s i
    · simp only [if_pos hc]; funext j; simp [hu]
    · simp only [if_neg hc]

theorem foldl_sym {α : Type} (ops : List α) (op : α → ℕ → NM co → NM co)
    (h : ∀ a, SymStep co (op a)) :
    SymStep co (fun s M => ops.foldl (fun M a => op a s M) M) := by
  intro σ s M
  induction ops generalizing M with
  | nil => rfl
  | cons a ops ih =>
    simp only [List.foldl_cons]
    rw [h a σ s M]
    exact ih _

theorem foldl_local {α : Type} (ops : List α) (op : α → ℕ → NM co → NM co)
    (h : ∀ a, Local co (op a)) :
    Local co (fun s M => ops.foldl (fun M a => op a s M) M) := by
  intro s M u hu
  induction ops generalizing M with
  | nil => rfl
  | cons a ops ih =>
    simp only [List.foldl_cons]
    have := ih (op a s M)
    simp only at this
    rw [this, h a s M u hu]

theorem comp_sym {F G : ℕ → NM co → NM co} (hF : SymStep co F) (hG : SymStep co G) :
    SymStep co (fun s M => G s (F s M)) := by
  intro σ s M
  simp only
  rw [hF, hG]

theorem comp_local {F G : ℕ → NM co → NM co} (hF : Local co F) (hG : Local co G) :
    Local co (fun s M => G s (F s M)) := by
  intro s M u hu
  simp only
  rw [hG s _ u hu, hF s M u hu]

variable (co)

/-- The join step on symbol `s` (`name_successors`, `Role::Join`): `remove(p, s, req)` for every
`(p, req)` of `coloured_in`, in order, then `add(p, s, 1)` for every relay target of the fired
branch ([NU-054]). -/
def joinStep (cin : List (PlaceId × ℕ)) (rel : List PlaceId) (s : ℕ) (M : NM co) : NM co :=
  rel.foldl (fun M p => addAt co p s 1 M) (cin.foldl (fun M pr => removeAt co pr.1 s pr.2 M) M)

/-- The consumer step on symbol `s` (`Role::Consume`, [NU-051]): `remove(inp, s, 1)`, then
`add(p, s, 1)` for every coloured output of the fired branch (relay; none = drain). -/
def consumeStep (inp : PlaceId) (outs : List PlaceId) (s : ℕ) (M : NM co) : NM co :=
  outs.foldl (fun M p => addAt co p s 1 M) (removeAt co inp s 1 M)

/-- The mint step (`Role::Mint`): `add(p, fresh, 1)` for every coloured output of the branch. -/
def mintStep (outs : List PlaceId) (c : ℕ) (M : NM co) : NM co :=
  outs.foldl (fun M p => addAt co p c 1 M) M

variable {co}

theorem joinStep_sym (cin : List (PlaceId × ℕ)) (rel : List PlaceId) :
    SymStep co (joinStep co cin rel) :=
  comp_sym (F := fun s M => cin.foldl (fun M (pr : PlaceId × ℕ) => removeAt co pr.1 s pr.2 M) M)
    (G := fun s M => rel.foldl (fun M p => addAt co p s 1 M) M)
    (foldl_sym cin (fun (pr : PlaceId × ℕ) s M => removeAt co pr.1 s pr.2 M) fun pr => removeAt_sym pr.1 pr.2)
    (foldl_sym rel (fun p s M => addAt co p s 1 M) fun p => addAt_sym p 1)

theorem joinStep_local (cin : List (PlaceId × ℕ)) (rel : List PlaceId) :
    Local co (joinStep co cin rel) :=
  comp_local (F := fun s M => cin.foldl (fun M (pr : PlaceId × ℕ) => removeAt co pr.1 s pr.2 M) M)
    (G := fun s M => rel.foldl (fun M p => addAt co p s 1 M) M)
    (foldl_local cin (fun (pr : PlaceId × ℕ) s M => removeAt co pr.1 s pr.2 M) fun pr => removeAt_local pr.1 pr.2)
    (foldl_local rel (fun p s M => addAt co p s 1 M) fun p => addAt_local p 1)

theorem consumeStep_sym (inp : PlaceId) (outs : List PlaceId) :
    SymStep co (consumeStep co inp outs) :=
  comp_sym (F := fun s M => removeAt co inp s 1 M)
    (G := fun s M => outs.foldl (fun M p => addAt co p s 1 M) M)
    (removeAt_sym inp 1) (foldl_sym outs (fun p s M => addAt co p s 1 M) fun p => addAt_sym p 1)

theorem consumeStep_local (inp : PlaceId) (outs : List PlaceId) :
    Local co (consumeStep co inp outs) :=
  comp_local (F := fun s M => removeAt co inp s 1 M)
    (G := fun s M => outs.foldl (fun M p => addAt co p s 1 M) M)
    (removeAt_local inp 1) (foldl_local outs (fun p s M => addAt co p s 1 M) fun p => addAt_local p 1)

theorem mintStep_sym (outs : List PlaceId) : SymStep co (mintStep co outs) :=
  foldl_sym outs (fun p s M => addAt co p s 1 M) fun p => addAt_sym p 1

theorem mintStep_local (outs : List PlaceId) : Local co (mintStep co outs) :=
  foldl_local outs (fun p s M => addAt co p s 1 M) fun p => addAt_local p 1

/-! ## Keys of per-symbol steps -/

/-- **Renaming.** A renamed source gives the renamed successor, hence the same key. -/
theorem key_rename {F : ℕ → NM co → NM co} (hF : SymStep co F) (σ : Equiv.Perm ℕ) (s : ℕ)
    (M : NM co) : canonicalKey (F (σ.symm s) (M ∘ σ)) = canonicalKey (F s M) := by
  rw [hF]
  exact canonicalKey_comp _ _

/-- **Swap.** Two symbols with equal rows give successors with equal keys: the transposition
of the two fixes the source and maps one successor onto the other. -/
theorem key_swap {F : ℕ → NM co → NM co} (hF : SymStep co F) {M : NM co} {s s' : ℕ}
    (h : M s = M s') : canonicalKey (F s M) = canonicalKey (F s' M) := by
  have hfix : M ∘ (Equiv.swap s s') = M := by
    funext u
    simp only [Function.comp]
    by_cases h1 : u = s
    · subst h1; rw [Equiv.swap_apply_left, h]
    · by_cases h2 : u = s'
      · subst h2; rw [Equiv.swap_apply_right, h]
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
  have hs : (Equiv.swap s s').symm s = s' := by
    rw [Equiv.symm_swap, Equiv.swap_apply_left]
  have := key_rename hF (Equiv.swap s s') s M
  rw [hs, hfix] at this
  exact this.symm

theorem sig_eq_iff {M : NM co} {s t : ℕ} : sig M s = sig M t ↔ M s = M t :=
  ⟨fun h => List.ofFn_injective h, fun h => by unfold sig; rw [h]⟩

theorem sig_comp (M : NM co) (σ : Equiv.Perm ℕ) (t : ℕ) : sig (M ∘ σ) t = sig M (σ t) := rfl

/-! ## Transversals: one symbol per signature -/

/-- `U` picks one symbol per signature of the symbols satisfying `E`. -/
structure Transversal (M : NM co) (E : ℕ → Prop) (U : List ℕ) : Prop where
  sub : ∀ u ∈ U, E u
  nodup : (U.map (sig M)).Nodup
  cover : ∀ s, E s → ∃ u ∈ U, sig M u = sig M s

/-- **Any two transversals give the same keyed successors**, up to order, for any `g` that only
reads a symbol's signature. -/
theorem transversal_perm {β : Type} {M : NM co} {E : ℕ → Prop} {g : ℕ → β}
    (hg : ∀ s t, sig M s = sig M t → g s = g t) {U V : List ℕ}
    (hU : Transversal M E U) (hV : Transversal M E V) : (U.map g).Perm (V.map g) := by
  classical
  let h : List ℕ → β := fun v => g (Classical.epsilon fun s => sig M s = v)
  have hgh : ∀ s, g s = h (sig M s) := fun s =>
    hg _ _ (Classical.epsilon_spec (p := fun t => sig M t = sig M s) ⟨s, rfl⟩).symm
  have hUg : U.map g = (U.map (sig M)).map h := by rw [List.map_map]; exact List.map_congr_left fun s _ => hgh s
  have hVg : V.map g = (V.map (sig M)).map h := by rw [List.map_map]; exact List.map_congr_left fun s _ => hgh s
  rw [hUg, hVg]
  refine List.Perm.map h ((List.perm_ext_iff_of_nodup hU.nodup hV.nodup).mpr fun v => ?_)
  simp only [List.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨w, hw, he⟩ := hV.cover u (hU.sub u hu)
    exact ⟨w, hw, he⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨u, hu, he⟩ := hU.cover w (hV.sub w hw)
    exact ⟨u, hu, he⟩

/-! ## `distinct_signatures` -/

variable (co)

/-- The loop of `distinct_signatures`: keep a symbol iff its signature is not yet `seen`. -/
def dsigAux (M : NM co) : List (List ℕ) → List ℕ → List ℕ
  | _, [] => []
  | seen, s :: ss =>
    if sig M s ∈ seen then dsigAux M seen ss else s :: dsigAux M (sig M s :: seen) ss

/-- `distinct_signatures`, with its `len < 2` shortcut. -/
def dsig (M : NM co) (l : List ℕ) : List ℕ :=
  if l.length < 2 then l else dsigAux co M [] l

variable {co}

theorem dsig_eq (M : NM co) (l : List ℕ) : dsig co M l = dsigAux co M [] l := by
  unfold dsig
  split
  · rename_i h
    match l, h with
    | [], _ => rfl
    | [a], _ => simp [dsigAux]
  · rfl

theorem dsigAux_spec (M : NM co) : ∀ (l : List ℕ) (seen : List (List ℕ)),
    (∀ r ∈ dsigAux co M seen l, r ∈ l) ∧
    ((dsigAux co M seen l).map (sig M)).Nodup ∧
    (∀ r ∈ dsigAux co M seen l, sig M r ∉ seen) ∧
    (∀ s ∈ l, sig M s ∈ seen ∨ ∃ r ∈ dsigAux co M seen l, sig M r = sig M s)
  | [], seen => by simp [dsigAux]
  | s :: ss, seen => by
    obtain ⟨h1, h2, h3, h4⟩ := dsigAux_spec M ss seen
    obtain ⟨g1, g2, g3, g4⟩ := dsigAux_spec M ss (sig M s :: seen)
    by_cases hs : sig M s ∈ seen
    · simp only [dsigAux, if_pos hs]
      refine ⟨fun r hr => List.mem_cons_of_mem _ (h1 r hr), h2, h3, fun t ht => ?_⟩
      rcases List.mem_cons.mp ht with rfl | ht
      · exact Or.inl hs
      · exact h4 t ht
    · simp only [dsigAux, if_neg hs]
      refine ⟨fun r hr => ?_, ?_, fun r hr => ?_, fun t ht => ?_⟩
      · rcases List.mem_cons.mp hr with rfl | hr
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (g1 r hr)
      · rw [List.map_cons, List.nodup_cons]
        refine ⟨fun hm => ?_, g2⟩
        obtain ⟨r, hr, he⟩ := List.mem_map.mp hm
        exact g3 r hr (he ▸ List.mem_cons_self)
      · rcases List.mem_cons.mp hr with rfl | hr
        · exact hs
        · exact fun h => g3 r hr (List.mem_cons_of_mem _ h)
      · rcases List.mem_cons.mp ht with rfl | ht
        · exact Or.inr ⟨t, List.mem_cons_self, rfl⟩
        · rcases g4 t ht with h | ⟨r, hr, he⟩
          · rcases List.mem_cons.mp h with h | h
            · exact Or.inr ⟨s, List.mem_cons_self, h.symm⟩
            · exact Or.inl h
          · exact Or.inr ⟨r, List.mem_cons_of_mem _ hr, he⟩

/-- `distinct_signatures` of the enabling symbols below a support bound is a transversal of the
enabling set. -/
theorem dsig_transversal {M : NM co} {E : ℕ → Bool} {B : ℕ} (hB : ∀ s, E s = true → s < B) :
    Transversal M (fun s => E s = true) (dsig co M ((List.range B).filter E)) := by
  rw [dsig_eq]
  obtain ⟨h1, h2, -, h4⟩ := dsigAux_spec M ((List.range B).filter E) []
  refine ⟨fun u hu => ?_, h2, fun s hs => ?_⟩
  · exact (List.mem_filter.mp (h1 u hu)).2
  · have hm : s ∈ (List.range B).filter E := List.mem_filter.mpr ⟨List.mem_range.mpr (hB s hs), hs⟩
    rcases h4 s hm with h | h
    · exact absurd h List.not_mem_nil
    · exact h

/-! ## Across a renaming -/

/-- A symbol predicate that commutes with renaming (`enabling_symbols`, `symbols_in`). -/
def RenamingInvariant (E : NM co → ℕ → Bool) : Prop :=
  ∀ (M : NM co) (σ : Equiv.Perm ℕ) (s : ℕ), E (M ∘ σ) s = E M (σ s)

/-- A symbol predicate that only holds of live symbols. -/
def LiveOnly (E : NM co → ℕ → Bool) : Prop :=
  ∀ (M : NM co) (s : ℕ), E M s = true → ∃ i, M s i ≠ 0

/-- Support below `B`: every symbol at or above `B` is dead. -/
def Supp (M : NM co) (B : ℕ) : Prop := ∀ s, B ≤ s → ∀ i, M s i = 0

theorem lt_of_live {M : NM co} {B s : ℕ} (hB : Supp M B) (h : ∃ i, M s i ≠ 0) : s < B := by
  by_contra hs
  obtain ⟨i, hi⟩ := h
  exact hi (hB s (Nat.le_of_not_lt hs) i)

/-- **The orbit dedup is key-equivariant.** Two markings in one renaming orbit, each with a
support bound, give the same keyed successor lists up to order when each fires once per distinct
signature among its enabling symbols (`dsig` of the filtered symbols below its bound). -/
theorem dedup_perm {E : NM co → ℕ → Bool} (hE : RenamingInvariant E) (hL : LiveOnly E)
    {F : ℕ → NM co → NM co} (hF : SymStep co F) {M N : NM co} {σ : Equiv.Perm ℕ}
    (hN : N = M ∘ σ) {B B' : ℕ} (hM : Supp M B) (hN' : Supp N B') :
    ((dsig co M ((List.range B).filter (E M))).map fun s => canonicalKey (F s M)).Perm
      ((dsig co N ((List.range B').filter (E N))).map fun s => canonicalKey (F s N)) := by
  subst hN
  set U := dsig co M ((List.range B).filter (E M))
  set V := dsig co (M ∘ σ) ((List.range B').filter (E (M ∘ σ)))
  have hU : Transversal M (fun s => E M s = true) U :=
    dsig_transversal fun s hs => lt_of_live hM (hL M s hs)
  have hV : Transversal (M ∘ σ) (fun s => E (M ∘ σ) s = true) V :=
    dsig_transversal fun s hs => lt_of_live hN' (hL _ s hs)
  -- Rewrite `V`'s keys through `σ`.
  have hVk : (V.map fun t => canonicalKey (F t (M ∘ σ))) =
      (V.map σ).map fun s => canonicalKey (F s M) := by
    rw [List.map_map]
    refine List.map_congr_left fun t _ => ?_
    have := key_rename hF σ (σ t) M
    simp only [Equiv.symm_apply_apply] at this
    exact this
  rw [hVk]
  have hV' : Transversal M (fun s => E M s = true) (V.map σ) := by
    refine ⟨fun u hu => ?_, ?_, fun s hs => ?_⟩
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hu
      have := hV.sub t ht
      rwa [hE] at this
    · rw [List.map_map]
      exact hV.nodup
    · have hs' : E (M ∘ σ) (σ.symm s) = true := by rw [hE]; simpa using hs
      obtain ⟨t, ht, he⟩ := hV.cover _ hs'
      refine ⟨σ t, List.mem_map.mpr ⟨t, ht, rfl⟩, ?_⟩
      rw [sig_comp, sig_comp] at he
      simpa using he
  exact transversal_perm (fun s t h => key_swap hF (sig_eq_iff.mp h)) hU hV'

/-- **Minting a fresh symbol is key-equivariant**: whichever fresh symbol each side mints, two
markings in one orbit give successors with one key. -/
theorem mint_key (outs : List PlaceId) {M N : NM co} {σ : Equiv.Perm ℕ} (hN : N = M ∘ σ)
    {c c' : ℕ} (hc : ∀ i, M c i = 0) (hc' : ∀ i, N c' i = 0) :
    canonicalKey (mintStep co outs c M) = canonicalKey (mintStep co outs c' N) := by
  subst hN
  have h1 := key_rename (mintStep_sym (co := co) outs) σ (σ c') M
  simp only [Equiv.symm_apply_apply] at h1
  rw [h1]
  apply key_swap (mintStep_sym outs)
  funext i
  rw [hc i]
  exact (hc' i).symm

/-! ## Enabling predicates -/

variable (co)

/-- `enabling_symbols`: present in the first correlated input, at the required multiplicity in
every one. No correlated input, no enabling symbol. -/
def joinEnab (cin : List (PlaceId × ℕ)) (M : NM co) (s : ℕ) : Bool :=
  match cin with
  | [] => false
  | (p0, _) :: _ => cnt co M s p0 != 0 && cin.all fun pr => decide (pr.2 ≤ cnt co M s pr.1)

/-- `symbols_in(inp)`: the symbols holding a token in `inp`. -/
def resident (inp : PlaceId) (M : NM co) (s : ℕ) : Bool := cnt co M s inp != 0

variable {co}

theorem joinEnab_inv (cin : List (PlaceId × ℕ)) : RenamingInvariant (joinEnab co cin) := by
  intro M σ s
  unfold joinEnab
  cases cin with
  | nil => rfl
  | cons pr rest => simp only [cnt_comp]

theorem resident_inv (inp : PlaceId) : RenamingInvariant (resident co inp) := by
  intro M σ s
  unfold resident
  rw [cnt_comp]

theorem cnt_ne_live {M : NM co} {s : ℕ} {p : PlaceId} (h : cnt co M s p ≠ 0) : ∃ i, M s i ≠ 0 := by
  unfold cnt at h
  split at h
  · exact ⟨_, h⟩
  · exact absurd rfl h

theorem joinEnab_live (cin : List (PlaceId × ℕ)) : LiveOnly (joinEnab co cin) := by
  intro M s h
  unfold joinEnab at h
  cases cin with
  | nil => simp at h
  | cons pr rest =>
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    exact cnt_ne_live h.1

theorem resident_live (inp : PlaceId) : LiveOnly (resident co inp) := by
  intro M s h
  unfold resident at h
  simp only [bne_iff_ne, ne_eq] at h
  exact cnt_ne_live h

end NameLayer

end Libpetri.Novel.RouteB
