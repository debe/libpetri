import Libpetri.Novel.RouteB.Name
import Libpetri.Interning
import Libpetri.Novel.ForwardDeposit

/-!
# Route B, the successor step: `name_successors`, the [NU-052] prune, and `Equivariant` discharged

Model of one expansion of `NameStateClassGraph::build_until` (`name_state_class_graph.rs`):
for every base-enabled transition of the class, skip it under `PrioritySemantics::Conflict` when
`priority_dominated` holds, else for every branch outcome (`expand_transition`) compute the base
successor (`compute_successor`, dropped when empty) and the name successors (`name_successors`),
one class per name successor, labelled with the transition's name.

* The base layer is abstract (`BaseLayer β`): a class's base is whatever `intern_base` keys:
  marking, zone and `ready_earliest` — and the step reads it only through `enabled`, `fire`,
  `readyLe` (the `ready_earliest` comparison of [NU-052]), `compete` (`shares_consumed_input`)
  and `idle` (the [VER-004] in-flight guard, a count on the base marking).
  The key of a class is `(base, canonicalKey names)`: the pair of intern ids the Rust dedups by,
  with the base intern key taken to be injective on what the step reads. That premise is exactly
  `equivariance_is_necessary` (`Interning.lean`); `intern_base` meets it by keying all three
  components (the zone key lists the clock names in canonical order, so the clock order
  `ready_earliest` is indexed by is keyed too). `Exec.lean` instantiates the base with `AMarking`
  and `ForwardDeposit.fireAD` (`untimedBase`).
* **Name-gated clocks (shipped, not in `BaseLayer`).** The model computes the base successor
  once per branch outcome, independent of the name layer. The shipped `build_until` computes it
  once per name step (`name_successors` returns `NameStep { intermediate, after }`: the layer
  with the fired symbol taken out, `None` for `Ordinary` / `Mint`, and the layer after the
  deposit, the latter being exactly what the model's `nameSuccs` lists), through
  `compute_successor_gated` with `name_enabled` on the intermediate and the new layer as the
  gates, so a ν-join whose inputs share no name holds no clock. On the untimed instance
  `untimedBase` there are no clocks, so the gate changes nothing there and every end-to-end
  theorem stands. For the timed class the successor now depends on the name step, but only
  through `name_enabled`, which is invariant under renaming (`nameEnabled_comp`), so the
  key-equivariance argument below carries over; restating `BaseLayer.fire` with the two gates
  as arguments is the formal version, not done here.
* `NState` carries the name layer with a support bound (`bound`, one above every live symbol), so
  the mint counter hypothesis `bound ≤ c` of `Interning.lean` says the minted symbol is fresh.
  Rust mints `next_sym`, `next_sym + 1`, … across one expansion; the model mints `c` in every
  successor of the expansion. Each successor holds one fresh symbol, and `mint_key` shows the
  key does not depend on which fresh symbol it is.
* The successor of a join / consume on symbol `s` gets bound `max bound (c + 1)` (any bound above
  the live symbols serves; the key never reads it).
* A branch outcome is a `Row`: fixed-count deposits plus drained forwards
  (`Deposit::Drained`), which `fire` resolves against the class's base, as `compute_successor`
  does through `produce_marking`. The name step reads the outcome's `places`
  (`Outcome::places`, drained targets included), as `name_successors` reads `output_places`.

This file models the per-class expansion of `build_until` (the `priority_dominated` call, the
`expand_transition` loop, the empty-successor skip, one edge per name successor); the queue,
budget and stop logic of the same function are in `Decide.lean`.

Results:
* `nameSuccs_perm`: two name layers in one orbit give the same successor keys up to order, per
  role: `Ordinary` trivially, `Mint` by `mint_key`, `Join` (relay included) and `Consume` by
  `dedup_perm`.
* `willFire_comp`, `dominated_eq`: `will_fire` and the prune read only whether an enabling symbol
  exists, which a renaming preserves.
* **`routeB_equivariant`: `Explorer.Equivariant (routeB …)`** — the hypothesis `Interning.lean`
  assumed, discharged for the shipped step.
* `routeB_interned_keys_eq`, `routeB_interned_edges_eq`: the hash-consed graph is the plain
  quotient graph, keys and labelled edges alike, with no premise left but the base-key one.
-/

namespace Libpetri.Novel.RouteB

open Libpetri
open Libpetri.Novel.CanonicalKey
open Libpetri.Novel.ForwardDeposit (Deposit)

/-- One branch outcome (`branch_outcomes::Outcome`) as the successor step reads it. `fixed` holds
the fixed-count deposits (`Deposit::Tokens(n)`: the place `n` times); `drains` the drained
forwards (`Deposit::Drained(from)` into `to`, stored as `(to, from)`): a timeout
`ForwardInput` from an `All` / `AtLeast` input, whose count depends on the marking the firing
drains and which the base layer resolves (`produce_marking` through `Outcome::resolved`). -/
structure Row where
  fixed  : Deposit
  drains : List (PlaceId × PlaceId) := []
  deriving DecidableEq

/-- `Outcome::places`: every place the outcome deposits into, drained targets included. This
is the `output_places` set `name_successors` reads. -/
def Row.places (r : Row) : Deposit := r.fixed ++ r.drains.map Prod.fst

/-- `Outcome::resolved` with `drained(from) = k from`, as a deposit list. -/
def Row.resolve (k : PlaceId → ℕ) (r : Row) : Deposit :=
  r.fixed ++ r.drains.flatMap fun x => List.replicate (k x.2) x.1

/-- A transition as Route B reads it: the structural core, the branch outcomes
(`expand_transition`, each a `Row`), the match keys (`match_spec().keys()`, `none` = no match
spec) and the declared relay targets ([NU-054]). -/
structure NuTrans where
  base   : Transition
  rows   : List Row
  keys   : Option (List PlaceId)
  relays : List PlaceId

/-- `name_fragment.rs` `Role`. Places are named by `PlaceId`, as in the Rust (by name). -/
inductive Role where
  | ordinary
  | mint
  | join (cin : List (PlaceId × ℕ)) (relay : List PlaceId)
  | consume (inp : PlaceId)
  deriving DecidableEq, Repr

/-- What the successor step reads of a class's base (`StateClass` + `ready_earliest`).
`idle b H`: no earlier firing of `H` is in flight, `marking.count(inflight:<H>) == 0` on the
class's base marking ([VER-004]); always true on a net the in-flight split left atomic, which
has no such place. -/
structure BaseLayer (β : Type) where
  enabled : β → Transition → Bool
  fire    : β → Transition → Row → Option β
  readyLe : β → Transition → Transition → Bool
  compete : β → Transition → Transition → Bool
  idle    : β → Transition → Bool

section Graph

variable (co : List PlaceId)

/-- `coloured_outputs`: the coloured places of the fired branch's `places` set. -/
def colOut (d : Deposit) : List PlaceId := d.dedup.filter fun p => (idx co p).isSome

/-- The relay targets of the fired branch: `output_places.filter(relay_to.contains)`. -/
def relOut (d : Deposit) (rel : List PlaceId) : List PlaceId := d.dedup.filter fun p => p ∈ rel

/-- `name_successors`: the name layers one firing of a role on branch `d` yields, from a layer
with support below `B`, minting `c`. -/
def nameSuccs (role : Role) (M : NM co) (d : Deposit) (B c : ℕ) : List (NM co) :=
  match role with
  | .ordinary => [M]
  | .mint => [mintStep co (colOut co d) c M]
  | .join cin rel => (dsig co M ((List.range B).filter (joinEnab co cin M))).map
      fun s => joinStep co cin (relOut d rel) s M
  | .consume inp => (dsig co M ((List.range B).filter (resident co inp M))).map
      fun s => consumeStep co inp (colOut co d) s M

/-- `will_fire`: a join needs an enabling symbol, a consumer a resident one. -/
def willFire (role : Role) (M : NM co) (B : ℕ) : Bool :=
  match role with
  | .join cin _ => (List.range B).any (joinEnab co cin M)
  | .consume inp => (List.range B).any (resident co inp M)
  | .ordinary => true
  | .mint => true

/-- A class of the name-aware graph: base, name layer, and a support bound for the layer. -/
structure NState (β : Type) where
  b : β
  m : NM co
  bound : ℕ
  supp : Supp m bound

variable {co}

theorem Supp.mono {M : NM co} {B B' : ℕ} (h : Supp M B) (hle : B ≤ B') : Supp M B' :=
  fun s hs i => h s (Nat.le_trans hle hs) i

theorem mem_dsig_range {M : NM co} {E : ℕ → Bool} {B s : ℕ}
    (h : s ∈ dsig co M ((List.range B).filter E)) : s < B ∧ E s = true := by
  rw [dsig_eq] at h
  have := (dsigAux_spec M ((List.range B).filter E) []).1 s h
  rw [List.mem_filter, List.mem_range] at this
  exact this

theorem supp_of_local {F : ℕ → NM co → NM co} (hF : Local co F) {M : NM co} {B s B' : ℕ}
    (hM : Supp M B) (hs : s < B') (hB : B ≤ B') : Supp (F s M) B' := by
  intro u hu i
  have hne : u ≠ s := by omega
  rw [hF s M u hne]
  exact hM u (Nat.le_trans hB hu) i

/-- Every name successor has support below `max B (c + 1)`. -/
theorem nameSuccs_supp {role : Role} {M : NM co} {d : Deposit} {B c : ℕ} (hM : Supp M B) :
    ∀ M' ∈ nameSuccs co role M d B c, Supp M' (max B (c + 1)) := by
  intro M' hM'
  cases role with
  | ordinary =>
    rw [nameSuccs, List.mem_singleton] at hM'
    subst hM'
    exact hM.mono (Nat.le_max_left _ _)
  | mint =>
    rw [nameSuccs, List.mem_singleton] at hM'
    subst hM'
    exact supp_of_local (mintStep_local _) hM (by omega) (Nat.le_max_left _ _)
  | join cin rel =>
    rw [nameSuccs, List.mem_map] at hM'
    obtain ⟨s, hs, rfl⟩ := hM'
    have := (mem_dsig_range hs).1
    exact supp_of_local (joinStep_local _ _) hM (by omega) (Nat.le_max_left _ _)
  | consume inp =>
    rw [nameSuccs, List.mem_map] at hM'
    obtain ⟨s, hs, rfl⟩ := hM'
    have := (mem_dsig_range hs).1
    exact supp_of_local (consumeStep_local _ _) hM (by omega) (Nat.le_max_left _ _)

/-! ## Name successors across a renaming -/

/-- **Per-role key-equivariance of `name_successors`.** -/
theorem nameSuccs_perm (role : Role) (d : Deposit) {M N : NM co} {σ : Equiv.Perm ℕ}
    (hN : N = M ∘ σ) {B B' c c' : ℕ} (hM : Supp M B) (hN' : Supp N B') (hc : B ≤ c)
    (hc' : B' ≤ c') :
    ((nameSuccs co role M d B c).map canonicalKey).Perm
      ((nameSuccs co role N d B' c').map canonicalKey) := by
  cases role with
  | ordinary =>
    simp only [nameSuccs, List.map_cons, List.map_nil]
    rw [hN, canonicalKey_comp]
  | mint =>
    simp only [nameSuccs, List.map_cons, List.map_nil]
    rw [mint_key (colOut co d) hN (fun i => hM c hc i) (fun i => hN' c' hc' i)]
  | join cin rel =>
    simp only [nameSuccs, List.map_map]
    exact dedup_perm (joinEnab_inv cin) (joinEnab_live cin) (joinStep_sym cin (relOut d rel))
      hN hM hN'
  | consume inp =>
    simp only [nameSuccs, List.map_map]
    exact dedup_perm (resident_inv inp) (resident_live inp)
      (consumeStep_sym inp (colOut co d)) hN hM hN'

theorem any_range_iff {E : NM co → ℕ → Bool} (hL : LiveOnly E) {M : NM co} {B : ℕ}
    (hM : Supp M B) : (List.range B).any (E M) = true ↔ ∃ s, E M s = true := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨s, -, hs⟩
    exact ⟨s, hs⟩
  · rintro ⟨s, hs⟩
    exact ⟨s, List.mem_range.mpr (lt_of_live hM (hL M s hs)), hs⟩

theorem exists_comp_iff {E : NM co → ℕ → Bool} (hE : RenamingInvariant E) (M : NM co)
    (σ : Equiv.Perm ℕ) : (∃ s, E (M ∘ σ) s = true) ↔ ∃ s, E M s = true := by
  constructor
  · rintro ⟨s, hs⟩
    rw [hE] at hs
    exact ⟨σ s, hs⟩
  · rintro ⟨s, hs⟩
    refine ⟨σ.symm s, ?_⟩
    rw [hE]
    simpa using hs

theorem any_range_comp {E : NM co → ℕ → Bool} (hE : RenamingInvariant E) (hL : LiveOnly E)
    {M N : NM co} {σ : Equiv.Perm ℕ} (hN : N = M ∘ σ) {B B' : ℕ} (hM : Supp M B)
    (hN' : Supp N B') : (List.range B').any (E N) = (List.range B).any (E M) := by
  apply Bool.eq_iff_iff.mpr
  rw [any_range_iff hL hM, any_range_iff hL hN', hN]
  exact exists_comp_iff hE M σ

/-- `will_fire` is renaming-invariant. -/
theorem willFire_comp (role : Role) {M N : NM co} {σ : Equiv.Perm ℕ} (hN : N = M ∘ σ)
    {B B' : ℕ} (hM : Supp M B) (hN' : Supp N B') :
    willFire co role N B' = willFire co role M B := by
  cases role with
  | ordinary => rfl
  | mint => rfl
  | join cin rel => exact any_range_comp (joinEnab_inv cin) (joinEnab_live cin) hN hM hN'
  | consume inp => exact any_range_comp (resident_inv inp) (resident_live inp) hN hM hN'

/-- `name_enabled`: the gate `build_until` hands `compute_successor_gated`. A join needs an
enabling symbol ([NU-020]); every other role is enabled by its counts. -/
def nameEnabled (role : Role) (M : NM co) (B : ℕ) : Bool :=
  match role with
  | .join _ _ => willFire co role M B
  | _ => true

/-- **The clock gate is invariant under renaming**: `name_enabled` reads only whether an
enabling symbol exists. So a base successor that depends on the name step through this gate
(the name-gated clocks of the shipped Route B) depends on it only up to key. -/
theorem nameEnabled_comp (role : Role) {M N : NM co} {σ : Equiv.Perm ℕ} (hN : N = M ∘ σ)
    {B B' : ℕ} (hM : Supp M B) (hN' : Supp N B') :
    nameEnabled role N B' = nameEnabled role M B := by
  cases role with
  | join cin rel => exact willFire_comp (.join cin rel) hN hM hN'
  | ordinary => rfl
  | mint => rfl
  | consume _ => rfl

/-! ## One expansion -/

variable {β : Type} (base : BaseLayer β) (net : List NuTrans) (role : NuTrans → Role)
  (conflict : Bool)

/-- `priority_dominated` ([NU-052]): some other base-enabled `H` of strictly higher priority,
ready no later, with no earlier firing in flight, that will fire and genuinely competes for a
consumed input. -/
def dominated (S : NState co β) (L : NuTrans) : Bool :=
  (net.filter fun H => base.enabled S.b H.base).any fun H =>
    (H.base.name != L.base.name) && decide (L.base.priority < H.base.priority)
      && base.readyLe S.b H.base L.base && base.idle S.b H.base
      && willFire co (role H) S.m S.bound && base.compete S.b H.base L.base

/-- One expansion of a class with mint counter `c`: the labelled successors, in the Rust's loop
order (enabled transitions, then branch outcomes, then name successors). `conflict` selects
`PrioritySemantics::Conflict`. -/
def succ (c : ℕ) (S : NState co β) : List (String × NState co β) :=
  (net.filter fun T => base.enabled S.b T.base).flatMap fun T =>
    if conflict && dominated base net role S T then [] else
      T.rows.flatMap fun d =>
        match base.fire S.b T.base d with
        | none => []
        | some b' => (nameSuccs co (role T) S.m d.places S.bound c).attach.map fun M' =>
            (T.base.name, ⟨b', M'.1, max S.bound (c + 1), nameSuccs_supp S.supp M'.1 M'.2⟩)

/-- The key of a class: the pair the Rust interns and dedups by. -/
noncomputable def keyOf (S : NState co β) : β × List (List (ℕ ×ₗ ℕ)) := (S.b, canonicalKey S.m)

/-- The Route B worklist step as an `Interning.lean` explorer. -/
noncomputable def routeB : Explorer (NState co β) (β × List (List (ℕ ×ₗ ℕ))) String where
  key := keyOf
  bound S := S.bound
  succ := succ base net role conflict

/-- The successors seen through the key. -/
noncomputable def succKeyed (c : ℕ) (S : NState co β) : List (String × (β × List (List (ℕ ×ₗ ℕ)))) :=
  (net.filter fun T => base.enabled S.b T.base).flatMap fun T =>
    if conflict && dominated base net role S T then [] else
      T.rows.flatMap fun d =>
        match base.fire S.b T.base d with
        | none => []
        | some b' => ((nameSuccs co (role T) S.m d.places S.bound c).map canonicalKey).map
            fun k => (T.base.name, (b', k))

theorem succ_keyed (c : ℕ) (S : NState co β) :
    (succ base net role conflict c S).map (routeB base net role conflict).keyed =
      succKeyed base net role conflict c S := by
  unfold succ succKeyed
  rw [List.map_flatMap]
  refine List.flatMap_congr fun T _ => ?_
  split
  · rfl
  · rw [List.map_flatMap]
    refine List.flatMap_congr fun d _ => ?_
    split
    · rfl
    · rw [List.map_map, List.map_map]
      conv_rhs => rw [← List.attach_map_subtype_val (nameSuccs co (role T) S.m d.places S.bound c),
        List.map_map]
      rfl

variable {base net role conflict}

theorem liveSet_finite {M : NM co} {B : ℕ} (hM : Supp M B) : (liveSet M).Finite := by
  refine (Set.finite_lt_nat B).subset fun s hs => ?_
  obtain ⟨i, hi⟩ := hs
  exact lt_of_live hM ⟨i, hi⟩

theorem dominated_eq {S S' : NState co β} (hb : S.b = S'.b) {σ : Equiv.Perm ℕ}
    (hm : S'.m = S.m ∘ σ) (L : NuTrans) :
    dominated base net role S L = dominated base net role S' L := by
  unfold dominated
  rw [hb]
  congr 1
  funext H
  rw [willFire_comp (role H) hm S.supp S'.supp]

/-- **`Equivariant` holds for the shipped Route B step.** Two classes with one key have the same
`(label, key)` successors up to order, under any counters fresh for each: the hypothesis of
`Interning.lean`'s `interned_keys_eq` / `interned_edges_eq`, discharged. -/
theorem routeB_equivariant : (routeB (co := co) base net role conflict).Equivariant := by
  constructor
  intro a b c c' hkey hca hcb
  have hk : keyOf a = keyOf b := hkey
  simp only [keyOf, Prod.mk.injEq] at hk
  obtain ⟨hb, hm⟩ := hk
  obtain ⟨σ, hσ⟩ := canonicalKey_complete (liveSet_finite a.supp) (liveSet_finite b.supp) hm
  change (succ base net role conflict c a).map _ |>.Perm ((succ base net role conflict c' b).map _)
  rw [succ_keyed, succ_keyed]
  unfold succKeyed
  rw [hb]
  refine List.Perm.flatMap_left _ fun T _ => ?_
  rw [dominated_eq (S := a) (S' := b) hb hσ T]
  split
  · exact List.Perm.refl _
  · refine List.Perm.flatMap_left _ fun d _ => ?_
    split
    · exact List.Perm.refl _
    · exact List.Perm.map _ (nameSuccs_perm (role T) d.places hσ a.supp b.supp hca hcb)

/-- **Interning is sound for Route B**: the hash-consed exploration reaches exactly the keys of
the plain one ([VER-012]), with `Equivariant` discharged rather than assumed. -/
theorem routeB_interned_keys_eq (rep : NState co β → NState co β)
    (hrep : ∀ s, keyOf (rep s) = keyOf s) (a0 : NState co β) :
    ∀ k, (∃ s, Explorer.Reach (routeB base net role conflict) a0 s ∧ keyOf s = k) ↔
      (∃ s, Explorer.ReachI (routeB base net role conflict) rep a0 s ∧ keyOf s = k) :=
  Explorer.interned_keys_eq routeB_equivariant rep hrep a0

/-- The labelled edges agree too. -/
theorem routeB_interned_edges_eq (rep : NState co β → NState co β)
    (hrep : ∀ s, keyOf (rep s) = keyOf s) (a0 : NState co β) :
    ∀ k l k', Explorer.Edge (routeB base net role conflict) a0 k l k' ↔
      Explorer.EdgeI (routeB base net role conflict) rep a0 k l k' :=
  Explorer.interned_edges_eq routeB_equivariant rep hrep a0

end Graph

end Libpetri.Novel.RouteB
