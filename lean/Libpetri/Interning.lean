/-
# Interning in the ν state-class graph: when sharing a representative is free

`NameStateClassGraph.build` (Java `analysis/NameStateClassGraph.java`; Rust
`name_state_class_graph.rs`, the interning itself in `intern_base` /
`intern_names`; TypeScript `name-state-class-graph.ts`) explores
the [VER-012] quotient by a worklist: pop a class, compute its labelled
successors (`name_successors`, one name layer per enabling symbol, minting a
fresh symbol from a monotone counter), dedup each by its canonical key, push
the new ones. A class costs kilobytes — `NameMarking` (`name_marking.rs`) is a
map of maps, `StateClass` (`state_class.rs`) a marking plus a DBM — and a
medium ν-net has millions of them. The memory change hash-conses the two
layers: a successor whose base (marking + zone + earliest-ready times) or whose
name layer (canonical key) has been seen before is **stored as the earlier
representative**, and later exploration proceeds from that representative
rather than from the freshly computed object.

The representative is a *different value* — a renaming of the symbols — so this
is a semantic claim, not a memory one: the graph explored from representatives
must be the same quotient graph. This file proves it, generically, and shows
the single hypothesis it rests on.

* `Explorer` — the abstract worklist step: a key, a freshness bound, and the
  labelled successors under a counter.
* `Equivariant` — **the load-bearing hypothesis**: states with equal keys have
  successors with equal `(label, key)` multisets, under any fresh-enough
  counters. It is exactly what the shipped code provides and what the
  representative must preserve:
  - `name_successors` is equivariant under symbol renaming role by role
    (`Ordinary` copies; `Mint` stamps a symbol the counter guarantees fresh;
    `Join` fires once per enabling symbol, a rank property; `Consume` once per
    resident symbol), and `will_fire` / `priority_dominated` read only whether
    `enabling_symbols` / `symbols_in` is empty;
  - `canonical_key` (`name_marking.rs`) is a complete invariant of the
    renaming orbit, so equal keys *are* renamings;
  - for the base layer the representative is not a renaming but an equal
    value — provided the intern key carries **everything the successor step
    reads**. `StateClass` equality (`state_class.rs`) is marking + zone, yet
    `priority_dominated` also reads `ready_earliest`, which two arrivals at one
    zone may disagree on; that is why the shipped intern key includes it.
* `interned_keys_eq` / `interned_edges_eq` — under `Equivariant`, exploring
  from any key-preserving representative map reaches exactly the same keys and
  the same `(key, label, key)` edges as exploring from the states themselves.
  Class *indices* are not claimed: successors are enumerated by raw symbol id,
  which a renaming permutes.
* `equivariance_is_necessary` — an explorer whose step reads what the key
  hides: interning then loses a reachable key. The hypothesis is not
  bureaucracy.

The counter is threaded as a hypothesis `bound ≤ c` on each step rather than
as state: the shipped `next_sym` only ever increases, so every stored class
has `bound ≤ next_sym` at the time it is explored, and the theorem holds for
whichever fresh counter that turns out to be.
-/
import Libpetri.Basic

namespace Libpetri

/-- The abstract worklist step of `NameStateClassGraph.build`: `key` is the
dedup key (`canonical_key`), `bound` the least symbol id fresh for a state
(one above its live symbols), `succ c s` the labelled successors of `s` when
the mint counter is `c` — `name_successors` per enabled transition, with the
[NU-052] prune folded in. -/
structure Explorer (S K L : Type) where
  key   : S → K
  bound : S → Nat
  succ  : Nat → S → List (L × S)

namespace Explorer

variable {S K L : Type}

/-- A labelled successor seen through the key. -/
def keyed (E : Explorer S K L) (ls : L × S) : L × K := (ls.1, E.key ls.2)

/-- **Key-equivariance of the step.** Two states with the same key have the
same `(label, key)` successors up to order, under any counters fresh for each.
This is the one property interning needs; the header lists the shipped facts
that establish it. -/
structure Equivariant (E : Explorer S K L) : Prop where
  key_succ : ∀ a b c c', E.key a = E.key b → E.bound a ≤ c → E.bound b ≤ c' →
    List.Perm ((E.succ c a).map E.keyed) ((E.succ c' b).map E.keyed)

/-- Plain exploration: the closure of `a0` under successors, each step taken
with some counter fresh for its source (the shipped counter is monotone, so
this is the counter the build actually has). -/
inductive Reach (E : Explorer S K L) (a0 : S) : S → Prop
  | init : Reach E a0 a0
  | step {a : S} {c : Nat} {l : L} {s : S} :
      Reach E a0 a → E.bound a ≤ c → (l, s) ∈ E.succ c a → Reach E a0 s

/-- Interned exploration: every successor is stored — and later explored — as
`rep s` instead of `s`. The shipped interner is `rep = first-seen state with
this key`; the theorem holds for any key-preserving `rep`. -/
inductive ReachI (E : Explorer S K L) (rep : S → S) (a0 : S) : S → Prop
  | init : ReachI E rep a0 a0
  | step {a : S} {c : Nat} {l : L} {s : S} :
      ReachI E rep a0 a → E.bound a ≤ c → (l, s) ∈ E.succ c a → ReachI E rep a0 (rep s)

/-- An edge of the plain graph, seen through the key. -/
inductive Edge (E : Explorer S K L) (a0 : S) : K → L → K → Prop
  | mk {a : S} {c : Nat} {l : L} {s : S} :
      Reach E a0 a → E.bound a ≤ c → (l, s) ∈ E.succ c a → Edge E a0 (E.key a) l (E.key s)

/-- An edge of the interned graph, seen through the key. -/
inductive EdgeI (E : Explorer S K L) (rep : S → S) (a0 : S) : K → L → K → Prop
  | mk {a : S} {c : Nat} {l : L} {s : S} :
      ReachI E rep a0 a → E.bound a ≤ c → (l, s) ∈ E.succ c a →
      EdgeI E rep a0 (E.key a) l (E.key s)

/-- From a `(label, key)` present in the keyed successor list of `b`, recover a
concrete successor of `b` with that key. -/
theorem exists_succ_of_keyed {E : Explorer S K L} {b : S} {c : Nat} {l : L} {k : K}
    (h : (l, k) ∈ (E.succ c b).map E.keyed) : ∃ s, (l, s) ∈ E.succ c b ∧ E.key s = k := by
  rw [List.mem_map] at h
  obtain ⟨⟨l', s⟩, hmem, hk⟩ := h
  simp only [keyed, Prod.mk.injEq] at hk
  obtain ⟨rfl, rfl⟩ := hk
  exact ⟨s, hmem, rfl⟩

/-- Every plainly reachable state has an interned twin with the same key. -/
theorem reach_to_interned {E : Explorer S K L} (hE : E.Equivariant) (rep : S → S)
    (hrep : ∀ s, E.key (rep s) = E.key s) {a0 : S} :
    ∀ {s}, Reach E a0 s → ∃ s', ReachI E rep a0 s' ∧ E.key s' = E.key s := by
  intro s h
  induction h with
  | init => exact ⟨a0, ReachI.init, rfl⟩
  | @step a c l s hr hb hmem ih =>
    obtain ⟨a', hr', hk⟩ := ih
    have hperm := hE.key_succ a a' c (E.bound a') hk.symm hb (Nat.le_refl _)
    have hin : (l, E.key s) ∈ (E.succ (E.bound a') a').map E.keyed :=
      hperm.mem_iff.mp (List.mem_map.mpr ⟨(l, s), hmem, rfl⟩)
    obtain ⟨s', hmem', hk'⟩ := exists_succ_of_keyed hin
    exact ⟨rep s', ReachI.step hr' (Nat.le_refl _) hmem', (hrep s').trans hk'⟩

/-- Every interned-reachable state has a plainly reachable twin with the same key. -/
theorem interned_to_reach {E : Explorer S K L} (hE : E.Equivariant) (rep : S → S)
    (hrep : ∀ s, E.key (rep s) = E.key s) {a0 : S} :
    ∀ {s}, ReachI E rep a0 s → ∃ s', Reach E a0 s' ∧ E.key s' = E.key s := by
  intro s h
  induction h with
  | init => exact ⟨a0, Reach.init, rfl⟩
  | @step a c l s hr hb hmem ih =>
    obtain ⟨a', hr', hk⟩ := ih
    have hperm := hE.key_succ a' a (E.bound a') c hk (Nat.le_refl _) hb
    have hin : (l, E.key s) ∈ (E.succ (E.bound a') a').map E.keyed :=
      hperm.mem_iff.mpr (List.mem_map.mpr ⟨(l, s), hmem, rfl⟩)
    obtain ⟨s', hmem', hk'⟩ := exists_succ_of_keyed hin
    exact ⟨s', Reach.step hr' (Nat.le_refl _) hmem', hk'.trans (hrep s).symm⟩

/-- **Interning preserves the reachable quotient.** For any key-preserving
representative map, the set of keys reached by the interned exploration is the
set of keys reached by the plain one — the state classes of the [VER-012]
graph, hence the verdict, are unchanged by hash-consing. -/
theorem interned_keys_eq {E : Explorer S K L} (hE : E.Equivariant) (rep : S → S)
    (hrep : ∀ s, E.key (rep s) = E.key s) (a0 : S) :
    ∀ k, (∃ s, Reach E a0 s ∧ E.key s = k) ↔ (∃ s, ReachI E rep a0 s ∧ E.key s = k) := by
  intro k
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨s', hs', hk⟩ := reach_to_interned hE rep hrep hs
    exact ⟨s', hs', hk⟩
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨s', hs', hk⟩ := interned_to_reach hE rep hrep hs
    exact ⟨s', hs', hk⟩

/-- The `(key, label, key)` edges agree as well: the interned graph is the
plain quotient graph, not merely the same vertex set. -/
theorem interned_edges_eq {E : Explorer S K L} (hE : E.Equivariant) (rep : S → S)
    (hrep : ∀ s, E.key (rep s) = E.key s) (a0 : S) :
    ∀ k l k', Edge E a0 k l k' ↔ EdgeI E rep a0 k l k' := by
  intro k l k'
  constructor
  · rintro ⟨hr, hb, hmem⟩
    rename_i a c s
    obtain ⟨a', hr', hk⟩ := reach_to_interned hE rep hrep hr
    have hperm := hE.key_succ a a' c (E.bound a') hk.symm hb (Nat.le_refl _)
    have hin : (l, E.key s) ∈ (E.succ (E.bound a') a').map E.keyed :=
      hperm.mem_iff.mp (List.mem_map.mpr ⟨(l, s), hmem, rfl⟩)
    obtain ⟨s', hmem', hk'⟩ := exists_succ_of_keyed hin
    rw [← hk, ← hk']
    exact EdgeI.mk hr' (Nat.le_refl _) hmem'
  · rintro ⟨hr, hb, hmem⟩
    rename_i a c s
    obtain ⟨a', hr', hk⟩ := interned_to_reach hE rep hrep hr
    have hperm := hE.key_succ a' a (E.bound a') c hk (Nat.le_refl _) hb
    have hin : (l, E.key s) ∈ (E.succ (E.bound a') a').map E.keyed :=
      hperm.mem_iff.mpr (List.mem_map.mpr ⟨(l, s), hmem, rfl⟩)
    obtain ⟨s', hmem', hk'⟩ := exists_succ_of_keyed hin
    rw [← hk, ← hk']
    exact Edge.mk hr' (Nat.le_refl _) hmem'

end Explorer

/-!
## Necessity: the step must not read what the key hides

A two-field state `(k, r)` whose key is `k` alone, and whose step reads `r`:
from `r = 0` it moves to `r = 1` under the same key, from `r = 1` it advances
the key. Plain exploration climbs through every key; an interner that folds
`(0, 1)` back onto the first-seen `(0, 0)` — a perfectly key-preserving
representative — never leaves key `0`. The successor step read `r`, a datum
the key does not determine: the exact shape of the `ready_earliest` hole the
base intern key had to close.
-/

/-- The toy explorer: key = first component, step reads the second. -/
def toy : Explorer (Nat × Nat) Nat Unit where
  key := fun s => s.1
  bound := fun _ => 0
  succ := fun _ s => if s.2 = 0 then [((), (s.1, 1))] else [((), (s.1 + 1, 0))]

/-- The first-seen representative of key `0` is `(0, 0)`; `(0, 1)` folds onto it. -/
def toyRep : Nat × Nat → Nat × Nat := fun s => if s = (0, 1) then (0, 0) else s

theorem toyRep_key : ∀ s, toy.key (toyRep s) = toy.key s := by
  intro s
  unfold toyRep
  split
  · rename_i h
    subst h
    rfl
  · rfl

/-- The toy step is **not** key-equivariant: `(0, 0)` and `(0, 1)` share key `0`
but their keyed successors are `[((), 0)]` and `[((), 1)]`. -/
theorem toy_not_equivariant : ¬ toy.Equivariant := by
  intro hE
  have h := hE.key_succ (0, 0) (0, 1) 0 0 rfl (Nat.le_refl _) (Nat.le_refl _)
  simp [toy, Explorer.keyed] at h

/-- Plain exploration reaches key `1`: `(0,0) → (0,1) → (1,0)`. -/
theorem toy_reaches_one : ∃ s, Explorer.Reach toy (0, 0) s ∧ toy.key s = 1 := by
  refine ⟨(1, 0), ?_, rfl⟩
  have h1 : Explorer.Reach toy (0, 0) (0, 1) :=
    Explorer.Reach.step (c := 0) (l := ()) Explorer.Reach.init (Nat.le_refl _) (by simp [toy])
  exact Explorer.Reach.step (c := 0) (l := ()) h1 (Nat.le_refl _) (by simp [toy])

/-- Interned exploration is stuck at `(0, 0)`. -/
theorem toy_interned_stuck : ∀ s, Explorer.ReachI toy toyRep (0, 0) s → s = (0, 0) := by
  intro s h
  induction h with
  | init => rfl
  | @step a c l s' _hr _hb hmem ih =>
    subst ih
    have hs : s' = (0, 1) := by simpa [toy] using hmem
    subst hs
    decide

/-- **Key-equivariance is load-bearing.** With a key-preserving representative
but a step that reads past the key, plain exploration reaches key `1` while the
interned exploration never leaves key `0`: a class of the quotient graph lost —
on a verifier, a false `Proven`. -/
theorem equivariance_is_necessary :
    (∀ s, toy.key (toyRep s) = toy.key s)
    ∧ ¬ toy.Equivariant
    ∧ (∃ s, Explorer.Reach toy (0, 0) s ∧ toy.key s = 1)
    ∧ (∀ s, Explorer.ReachI toy toyRep (0, 0) s → toy.key s = 0) :=
  ⟨toyRep_key, toy_not_equivariant, toy_reaches_one,
    fun s h => by rw [toy_interned_stuck s h]; rfl⟩

end Libpetri
