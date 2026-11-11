import Libpetri.Reference.Marking
import Libpetri.Reference.Queue
import Libpetri.Spec.GlossaryTime
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Dedup
import Libpetri.Spec.Registry

set_option linter.missingDocs true

/-!
# RefSnapshot: the snapshot form of a queue marking, restore, and seeding a resume

The witness model of [CORE-073] (and of the snapshot carried by [EVT-014] and [ENV-014], which
import it and never redefine it). It is the token-level generalisation of
`Reference/Marking.lean`: where a count marking is a sorted list of `(place, count)` entries
without a zero count, a **snapshot** (`QSnap K T`) is a list of `(place, queue)` entries, the
queue being the place's tokens in FIFO order (head = oldest, as in `QMarking`). The token type
`T` is abstract: a token is the implementation's own token, value and `created_at` together, so
"the tokens are unchanged" covers both fields at once.

* **Canonical** (`QCanon`): names strictly ascending, no empty queue. With `K := String` the order
  is `String.lt`, the code-point order the spec requires (a UTF-16 order differs above U+FFFF).
* **Snapshot** (`refSnapshot`): a queue marking is a function, so it is snapshotted together with
  a finite list `supp` covering its marked places (`FinQ`). The snapshot lists exactly the marked
  places (`mem_snapshot_keys`), sorted and deduplicated, each with its whole queue. It is
  canonical (`snapshot_canon`) and **extensional**: it depends only on the marking, never on the
  support list that came with it (`snapshot_extensional`, `snapshot_eq_iff`), so a drained place
  and a place that never held a token snapshot identically.
* **Restore** (`refRestore`): the queue of the first entry for a name, or empty. It retains every
  name, declared or not (the restore knows no net). Restore after snapshot is the marking, token
  for token and in order (`restore_snapshot`). On a snapshot with pairwise distinct names (a
  mapping, `QKeysNodup`) the restore ignores entry order (`restore_perm`) and an empty entry
  restores like an absent one (`restore_dropEmpty`). Snapshot after restore is the canonical form
  (`snapshot_restore`).
* **Counts** (`snapCounts`): the count projection of a snapshot is a `Reference.Marking`; the
  snapshot's projection is canonical and holds `qCount` of the marking (`count_snapshot`), so it is
  the count marking the conformance corpus and the verifiers already use.
* **Resume** (`refResume`): seeding a timed executor from a snapshot is `TSt.init` on the counts of
  the restored marking at the resuming clock reading. It arms exactly the transitions enabled in
  the restored marking, each stamped with that reading (`resume_initArms`), so every clock starts
  fresh. The state depends on the snapshot only through its counts (`resume_counts_only`): no token
  value and no `created_at` advances or shortcuts a timing decision (`resume_map_tokens`).
* **Seeding with an explicit initial marking** (`refSeed`, ruling D84 (a)): a restore together
  with an explicit initial marking that holds a token is rejected; an explicit marking without a
  token is accepted.

`insertionSort` and not `mergeSort`: `mergeSort` is defined by well-founded recursion, so the
kernel does not reduce it and `decide` examples would get stuck.

Not modelled here: codecs, JSON, archives and the debug protocol ([EVT-014], [EVT-025]); Java's
resolution of names against the receiving net and its rejection of two same-named places
([MOD-024]); the executor seeding the restored tokens unchanged (AC9, RefExec).
-/

namespace Libpetri.Reference

open Libpetri.Spec (Armed Enabled InNet ClockReading Elapsed InitArms initArms_init)

variable {K T : Type}

/-! ## The form -/

/-- The snapshot form ([CORE-073]): `(place name, queue)` entries, each queue in FIFO order. -/
abbrev QSnap (K T : Type) := List (K × List T)

/-- A snapshot is a **mapping**: its place names are pairwise distinct. -/
def QKeysNodup (s : QSnap K T) : Prop := (s.map Prod.fst).Nodup

/-- **Canonical**: names strictly ascending, no empty queue. -/
def QCanon [LinearOrder K] (s : QSnap K T) : Prop :=
  (s.map Prod.fst).Pairwise (· < ·) ∧ ∀ e ∈ s, e.2 ≠ []

instance [DecidableEq K] (s : QSnap K T) : Decidable (QKeysNodup s) :=
  inferInstanceAs (Decidable (List.Nodup _))

instance [LinearOrder K] (s : QSnap K T) : Decidable (QCanon s) :=
  decidable_of_iff ((s.map Prod.fst).Pairwise (· < ·) ∧ ∀ e ∈ s, e.2.isEmpty = false)
    (by simp only [QCanon, List.isEmpty_eq_false_iff, ne_eq])

/-- A queue marking together with a finite list covering its marked places. The list may name a
place twice or name an unmarked place; the snapshot does not depend on it. -/
structure FinQ (K T : Type) where
  /-- The queue marking. -/
  M : QMarking K T
  /-- A finite list of names covering the marked places. -/
  supp : List K
  /-- Every marked place is in `supp`. -/
  hsupp : ∀ k, M k ≠ [] → k ∈ supp

/-! ## Snapshot and restore -/

/-- The names a snapshot lists: the marked places of the support, ascending, each once. -/
def snapKeys [LinearOrder K] (F : FinQ K T) : List K :=
  ((F.supp.insertionSort (· ≤ ·)).dedup).filter fun k => !(F.M k).isEmpty

/-- **The reference snapshot**: each marked place with its whole queue, ascending by name. -/
def refSnapshot [LinearOrder K] (F : FinQ K T) : QSnap K T :=
  (snapKeys F).map fun k => (k, F.M k)

/-- **The reference restore**: the queue of the first entry for a name, or empty. -/
def refRestore [DecidableEq K] : QSnap K T → QMarking K T
  | [], _ => []
  | (k, q) :: rest, p => if k = p then q else refRestore rest p

section Restore

variable [DecidableEq K]

@[simp] theorem refRestore_nil (p : K) : refRestore ([] : QSnap K T) p = [] := rfl

theorem refRestore_cons (k : K) (q : List T) (rest : QSnap K T) (p : K) :
    refRestore ((k, q) :: rest) p = if k = p then q else refRestore rest p := rfl

/-- A name without an entry restores to the empty queue. -/
theorem restore_eq_nil_of_not_mem {s : QSnap K T} {p : K} (h : p ∉ s.map Prod.fst) :
    refRestore s p = [] := by
  induction s with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨k, q⟩ := e
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [refRestore_cons, if_neg (Ne.symm h.1), ih h.2]

/-- A name restoring to a non-empty queue has an entry. -/
theorem mem_keys_of_restore_ne_nil {s : QSnap K T} {p : K} (h : refRestore s p ≠ []) :
    p ∈ s.map Prod.fst := by
  by_contra hn
  exact h (restore_eq_nil_of_not_mem hn)

/-- On a mapping, an entry is what its name restores to. -/
theorem restore_of_mem {s : QSnap K T} (hnd : QKeysNodup s) {k : K} {q : List T}
    (h : (k, q) ∈ s) : refRestore s k = q := by
  induction s with
  | nil => exact absurd h List.not_mem_nil
  | cons e rest ih =>
    obtain ⟨k', q'⟩ := e
    have hnd' : k' ∉ rest.map Prod.fst ∧ QKeysNodup rest :=
      List.nodup_cons.mp (show (k' :: rest.map Prod.fst).Nodup from hnd)
    rw [refRestore_cons]
    rcases List.mem_cons.mp h with h | h
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp
    · have hk : k' ≠ k := fun hk => hnd'.1 (hk ▸ List.mem_map.mpr ⟨_, h, rfl⟩)
      rw [if_neg hk, ih hnd'.2 h]

/-- The restore of a snapshot, packed with its names as the support. -/
def restoreFin (s : QSnap K T) : FinQ K T where
  M := refRestore s
  supp := s.map Prod.fst
  hsupp := fun _ h => mem_keys_of_restore_ne_nil h

/-- On a mapping, restore ignores entry order. -/
theorem restore_perm {s s' : QSnap K T} (hnd : QKeysNodup s) (hp : s.Perm s') :
    refRestore s = refRestore s' := by
  have hnd' : QKeysNodup s' := (hp.map Prod.fst).nodup_iff.mp hnd
  funext p
  by_cases hk : p ∈ s.map Prod.fst
  · obtain ⟨⟨k, q⟩, hm, rfl⟩ := List.mem_map.mp hk
    rw [restore_of_mem hnd hm, restore_of_mem hnd' (hp.mem_iff.mp hm)]
  · have hk' : p ∉ s'.map Prod.fst := fun h => hk ((hp.map Prod.fst).mem_iff.mpr h)
    rw [restore_eq_nil_of_not_mem hk, restore_eq_nil_of_not_mem hk']

/-- On a mapping, an entry with an empty queue restores like an absent one. -/
theorem restore_dropEmpty {s : QSnap K T} (hnd : QKeysNodup s) :
    refRestore (s.filter fun e => !e.2.isEmpty) = refRestore s := by
  funext p
  induction s with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨k, q⟩ := e
    have hnd' : k ∉ rest.map Prod.fst ∧ QKeysNodup rest :=
      List.nodup_cons.mp (show (k :: rest.map Prod.fst).Nodup from hnd)
    rw [refRestore_cons]
    cases q with
    | nil =>
      simp only [List.filter_cons, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true,
        if_false]
      rw [ih hnd'.2]
      by_cases hkp : k = p
      · subst hkp; rw [if_pos rfl, restore_eq_nil_of_not_mem hnd'.1]
      · rw [if_neg hkp]
    | cons x xs =>
      simp only [List.filter_cons, List.isEmpty_cons, Bool.not_false, if_true]
      rw [refRestore_cons, ih hnd'.2]

/-- Restoring a snapshot whose queues are mapped token by token maps each restored queue. -/
theorem restore_map_tokens (f : T → T) (s : QSnap K T) (p : K) :
    refRestore (s.map fun e => (e.1, e.2.map f)) p = (refRestore s p).map f := by
  induction s with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨k, q⟩ := e
    simp only [List.map_cons, refRestore_cons]
    split <;> simp [ih]

end Restore

/-! ## Canonical form -/

section Canon

variable [LinearOrder K]

theorem qCanon_cons {k : K} {q : List T} {rest : QSnap K T} :
    QCanon ((k, q) :: rest) ↔ (∀ e ∈ rest, k < e.1) ∧ q ≠ [] ∧ QCanon rest := by
  unfold QCanon
  simp only [List.map_cons, List.pairwise_cons, List.mem_map, List.mem_cons, forall_eq_or_imp]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨fun e he => h1 _ ⟨e, he, rfl⟩, h3, h2, h4⟩
  · rintro ⟨h1, h3, h2, h4⟩
    exact ⟨⟨fun a ⟨e, he, hea⟩ => hea ▸ h1 e he, h2⟩, h3, h4⟩

/-- A canonical snapshot is a mapping. -/
theorem QCanon.keysNodup {s : QSnap K T} (h : QCanon s) : QKeysNodup s :=
  h.1.imp fun hlt => ne_of_lt hlt

/-- Below the head's name, the tail of a canonical snapshot holds nothing. -/
theorem restore_tail_of_le {k p : K} {q : List T} {rest : QSnap K T}
    (hc : QCanon ((k, q) :: rest)) (hp : p ≤ k) : refRestore rest p = [] :=
  restore_eq_nil_of_not_mem fun hm => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
    exact absurd ((qCanon_cons.mp hc).1 e he) (not_lt.mpr hp)

/-- **Canonical snapshots are equal iff they restore to the same marking** (the token analogue
of `Reference.ext`). -/
theorem canon_ext : ∀ {a b : QSnap K T}, QCanon a → QCanon b →
    (∀ p, refRestore a p = refRestore b p) → a = b
  | [], [], _, _, _ => rfl
  | [], (k, q) :: _, _, hb, h => by
    have := h k
    simp only [refRestore_nil, refRestore_cons, if_true] at this
    exact absurd this.symm (qCanon_cons.mp hb).2.1
  | (k, q) :: _, [], ha, _, h => by
    have := h k
    simp only [refRestore_nil, refRestore_cons, if_true] at this
    exact absurd this (qCanon_cons.mp ha).2.1
  | (k1, q1) :: r1, (k2, q2) :: r2, ha, hb, h => by
    obtain ⟨_, hq1, hr1⟩ := qCanon_cons.mp ha
    obtain ⟨_, hq2, hr2⟩ := qCanon_cons.mp hb
    rcases lt_trichotomy k1 k2 with hlt | heq | hgt
    · have := h k1
      rw [refRestore_cons, refRestore_cons, if_pos rfl, if_neg (ne_of_gt hlt),
        restore_tail_of_le hb (le_of_lt hlt)] at this
      exact absurd this hq1
    · subst heq
      have hq := h k1
      rw [refRestore_cons, refRestore_cons, if_pos rfl, if_pos rfl] at hq
      subst hq
      have hr : ∀ p, refRestore r1 p = refRestore r2 p := fun p => by
        by_cases hp : p = k1
        · subst hp
          rw [restore_tail_of_le ha le_rfl, restore_tail_of_le hb le_rfl]
        · have := h p
          rwa [refRestore_cons, refRestore_cons, if_neg (Ne.symm hp), if_neg (Ne.symm hp)] at this
      rw [canon_ext hr1 hr2 hr]
    · have := h k2
      rw [refRestore_cons, refRestore_cons, if_pos rfl, if_neg (ne_of_gt hgt),
        restore_tail_of_le ha (le_of_lt hgt)] at this
      exact absurd this.symm hq2

/-! ## The reference snapshot: keys, canonical, round trip, extensional -/

/-- The snapshot lists exactly the marked places. -/
theorem mem_snapKeys (F : FinQ K T) (k : K) : k ∈ snapKeys F ↔ F.M k ≠ [] := by
  unfold snapKeys
  simp only [List.mem_filter, List.mem_dedup, (List.perm_insertionSort _ _).mem_iff,
    Bool.not_eq_true', List.isEmpty_eq_false_iff]
  exact ⟨fun h => h.2, fun h => ⟨F.hsupp k h, h⟩⟩

/-- The snapshot's names are strictly ascending. -/
theorem snapKeys_lt (F : FinQ K T) : (snapKeys F).Pairwise (· < ·) := by
  unfold snapKeys
  apply List.Pairwise.filter
  have hs : ((F.supp.insertionSort (· ≤ ·)).dedup).Pairwise (· ≤ ·) :=
    (List.pairwise_insertionSort (· ≤ ·) F.supp).sublist (List.dedup_sublist _)
  exact (hs.and (List.nodup_dedup _)).imp fun h => lt_of_le_of_ne h.1 h.2

/-- The names of the snapshot are `snapKeys`. -/
theorem snapshot_keys (F : FinQ K T) : (refSnapshot F).map Prod.fst = snapKeys F := by
  simp [refSnapshot, Function.comp_def]

/-- **Keyed by marked places**: a name has an entry exactly when its place holds a token. -/
theorem mem_snapshot_keys (F : FinQ K T) (k : K) :
    k ∈ (refSnapshot F).map Prod.fst ↔ F.M k ≠ [] := by
  rw [snapshot_keys, mem_snapKeys]

/-- Every entry of the snapshot is its place with its whole queue. -/
theorem mem_snapshot (F : FinQ K T) {k : K} {q : List T} :
    (k, q) ∈ refSnapshot F ↔ F.M k ≠ [] ∧ q = F.M k := by
  unfold refSnapshot
  simp only [List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨k', hk', rfl, rfl⟩
    exact ⟨(mem_snapKeys F k').mp hk', rfl⟩
  · rintro ⟨h, rfl⟩
    exact ⟨k, (mem_snapKeys F k).mpr h, rfl, rfl⟩

/-- **The snapshot is canonical.** -/
theorem snapshot_canon (F : FinQ K T) : QCanon (refSnapshot F) := by
  refine ⟨(snapshot_keys F) ▸ snapKeys_lt F, fun e he => ?_⟩
  obtain ⟨k, q⟩ := e
  obtain ⟨h, rfl⟩ := (mem_snapshot F).mp he
  exact h

/-- **Restore after snapshot is the marking**: every place gets its queue back, every token
unchanged and in FIFO order. -/
theorem restore_snapshot (F : FinQ K T) : refRestore (refSnapshot F) = F.M := by
  funext k
  by_cases hk : F.M k = []
  · rw [hk]
    exact restore_eq_nil_of_not_mem fun hm => ((mem_snapshot_keys F k).mp hm) hk
  · exact restore_of_mem (snapshot_canon F).keysNodup ((mem_snapshot F).mpr ⟨hk, rfl⟩)

/-- **Extensional**: the snapshot depends only on the marking, not on the support list. -/
theorem snapshot_extensional {F G : FinQ K T} (h : F.M = G.M) : refSnapshot F = refSnapshot G :=
  canon_ext (snapshot_canon F) (snapshot_canon G) fun p => by
    rw [restore_snapshot, restore_snapshot, h]

/-- Two snapshots are equal exactly when the markings are. -/
theorem snapshot_eq_iff {F G : FinQ K T} : refSnapshot F = refSnapshot G ↔ F.M = G.M :=
  ⟨fun h => by rw [← restore_snapshot F, ← restore_snapshot G, h], snapshot_extensional⟩

/-- Snapshot after restore is the canonical form: a canonical snapshot comes back unchanged. -/
theorem snapshot_restore {s : QSnap K T} (hc : QCanon s) : refSnapshot (restoreFin s) = s :=
  canon_ext (snapshot_canon _) hc fun p => by rw [restore_snapshot]; rfl

/-- A canonical snapshot is the reference snapshot of the marking it restores to. -/
theorem canon_iff_snapshot {s : QSnap K T} : QCanon s ↔ ∃ F : FinQ K T, refSnapshot F = s :=
  ⟨fun hc => ⟨restoreFin s, snapshot_restore hc⟩, fun ⟨F, h⟩ => h ▸ snapshot_canon F⟩

/-! ## The count projection -/

/-- The count marking of a snapshot: each entry's queue length. -/
def snapCounts (s : QSnap K T) : Marking K := s.map fun e => (e.1, e.2.length)

/-- The count of a name in `snapCounts` is the length of its restored queue. -/
theorem get_snapCounts (s : QSnap K T) (p : K) :
    get (snapCounts s) p = (refRestore s p).length := by
  induction s with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨k, q⟩ := e
    simp only [snapCounts, List.map_cons, get, refRestore_cons] at ih ⊢
    split <;> simp [ih]

/-- The count projection of a canonical snapshot is a canonical count marking. -/
theorem canon_snapCounts {s : QSnap K T} (hc : QCanon s) : Canon (snapCounts s) := by
  refine ⟨?_, fun e he => ?_⟩
  · simpa [snapCounts, Function.comp_def] using hc.1
  · obtain ⟨⟨k, q⟩, hm, rfl⟩ := List.mem_map.mp he
    simpa using hc.2 _ hm

/-- **Count link**: the snapshot's count projection is the canonical count marking holding
`qCount` of the marking (`Reference.Marking`, as the conformance corpus uses it). -/
theorem count_snapshot (F : FinQ K T) :
    Canon (snapCounts (refSnapshot F)) ∧ ∀ k, get (snapCounts (refSnapshot F)) k = qCount F.M k :=
  ⟨canon_snapCounts (snapshot_canon F), fun k => by rw [get_snapCounts, restore_snapshot]; rfl⟩

end Canon

/-! ## Seeding: an explicit initial marking, and arming at the resuming reading -/

section Seed

variable [DecidableEq K]

/-- An explicit initial marking (in the same entry shape) holds a token. -/
def HoldsToken (E : QSnap K T) : Prop := E.any (fun e => !e.2.isEmpty) = true

instance (E : QSnap K T) : Decidable (HoldsToken E) := inferInstanceAs (Decidable (_ = true))

omit [DecidableEq K] in
theorem holdsToken_iff (E : QSnap K T) : HoldsToken E ↔ ∃ e ∈ E, e.2 ≠ [] := by
  simp [HoldsToken, List.isEmpty_eq_false_iff]

/-- **The reference seeding** of an executor ([CORE-072], [CORE-073] AC11 under ruling D84 (a)):
without a restore, the explicit initial marking; with a restore, the restored marking, and an
error when the explicit initial marking also holds a token. An explicit marking without a token
is accepted together with a restore. -/
def refSeed (restore : Option (QSnap K T)) (explicit : QSnap K T) : Except String (QMarking K T) :=
  match restore with
  | none => .ok (refRestore explicit)
  | some s =>
    if HoldsToken explicit then
      .error "a restored marking and a non-empty explicit initial marking both describe the initial marking"
    else .ok (refRestore s)

theorem refSeed_none (E : QSnap K T) : refSeed none E = .ok (refRestore E) := rfl

/-- A restore with an explicit marking that holds no token seeds the restored marking. -/
theorem refSeed_restore {s E : QSnap K T} (h : ¬ HoldsToken E) :
    refSeed (some s) E = .ok (refRestore s) := by
  simp [refSeed, h]

/-- A restore together with an explicit marking holding a token is rejected, never merged and
never resolved in favour of either. -/
theorem refSeed_both {s E : QSnap K T} (h : HoldsToken E) : ∀ M, refSeed (some s) E ≠ .ok M := by
  intro M
  simp [refSeed, h]

/-- **The resume**: a timed executor seeded from a snapshot at the resuming clock reading `now0`
is the reference initialiser on the counts of the restored marking. -/
def refResume (X : TimedNet K) (s : QSnap K T) (now0 : Nat) : TSt K :=
  TSt.init X (qCount (refRestore s)) now0

theorem resume_eq_init (X : TimedNet K) (s : QSnap K T) (now0 : Nat) :
    refResume X s now0 = TSt.init X (qCount (refRestore s)) now0 := rfl

/-- The resume holds the restored marking's counts on every place, declared or not. -/
theorem resume_marking (X : TimedNet K) (s : QSnap K T) (now0 : Nat) :
    (refResume X s now0).m = qCount (refRestore s) := rfl

/-- The resume starts the firing clock at the resuming reading. -/
theorem resume_clock (X : TimedNet K) (s : QSnap K T) (now0 : Nat) :
    ClockReading (refResume X s now0) = now0 := rfl

/-- **Seeding a restore arms at the resuming reading**: a transition of the net is armed exactly
when it is enabled in the restored marking, with the resuming reading as its stamp. -/
theorem resume_initArms (X : TimedNet K) (s : QSnap K T) (now0 : Nat) {u : Trans K}
    (hu : InNet X u) :
    (Armed (refResume X s now0) u ↔ Enabled u (qCount (refRestore s))) ∧
      (Enabled u (qCount (refRestore s)) → (refResume X s now0).stamp u.core.name = some now0) :=
  initArms_init X (qCount (refRestore s)) now0 u hu

/-- Every transition of the net enabled by the restored marking starts with elapsed time 0. -/
theorem resume_elapsed (X : TimedNet K) (s : QSnap K T) (now0 : Nat) {u : Trans K}
    (hu : InNet X u) (he : Enabled u (qCount (refRestore s))) :
    Elapsed (refResume X s now0) u = 0 :=
  Spec.initArms_elapsed initArms_init hu he

/-- The resume depends on the snapshot only through the restored counts. -/
theorem resume_counts_only (X : TimedNet K) {s s' : QSnap K T} (now0 : Nat)
    (h : qCount (refRestore s) = qCount (refRestore s')) :
    refResume X s now0 = refResume X s' now0 := by
  simp only [refResume, h]

/-- **No token shortcuts a clock**: changing every token (its value, its `created_at`) leaves the
resumed state unchanged. -/
theorem resume_map_tokens (X : TimedNet K) (f : T → T) (s : QSnap K T) (now0 : Nat) :
    refResume X (s.map fun e => (e.1, e.2.map f)) now0 = refResume X s now0 :=
  resume_counts_only X now0 (funext fun p => by simp [qCount, restore_map_tokens])

end Seed

/-- A restored snapshot of a marking seeds exactly as that marking would ([CORE-073] AC2). -/
theorem resume_snapshot [LinearOrder K] (X : TimedNet K) (F : FinQ K T) (now0 : Nat) :
    refResume X (refSnapshot F) now0 = TSt.init X (qCount F.M) now0 := by
  rw [resume_eq_init, restore_snapshot]

/-! ## Witness models

Registered so that a block's `holds` theorem may apply its requirement to them. -/

#spec_witness refSnapshot
#spec_witness refRestore
#spec_witness refResume
#spec_witness refSeed

/-! ## Examples -/

/-- A three-place queue marking; place "b" holds nothing. -/
def snapExM : QMarking String Nat := fun k => if k = "c" then [7, 8] else if k = "a" then [1] else []

/-- `snapExM` with a support naming "a" twice and the unmarked "b". -/
def snapExF : FinQ String Nat where
  M := snapExM
  supp := ["c", "a", "b", "a"]
  hsupp := fun k h => by
    unfold snapExM at h
    by_cases hc : k = "c"
    · simp [hc]
    · by_cases ha : k = "a"
      · simp [ha]
      · simp [hc, ha] at h

example : refSnapshot snapExF = [("a", [1]), ("c", [7, 8])] := by decide
example : refRestore [("c", [7, 8]), ("a", [1])] "c" = [7, 8] := by decide
example : refRestore [("c", [7, 8]), ("b", []), ("a", [1])] "b" = [] := by decide

/-- The name U+E000 (Basic Multilingual Plane, private use). -/
def snapNameBmp : String := String.singleton (Char.ofNat 0xE000)
/-- The name U+10000 (above U+FFFF; UTF-16 surrogate D800 DC00). -/
def snapNameAstral : String := String.singleton (Char.ofNat 0x10000)

/-- Names order by code point: the name U+E000 sorts before the name U+10000 (a UTF-16
code-unit order would put U+10000, surrogate D800, first). -/
def snapExCP : FinQ String Nat where
  M := fun k => if k = snapNameAstral then [1] else if k = snapNameBmp then [2] else []
  supp := [snapNameAstral, snapNameBmp]
  hsupp := fun k h => by
    by_cases h1 : k = snapNameAstral
    · simp [h1]
    · by_cases h2 : k = snapNameBmp
      · simp [h2]
      · simp [h1, h2] at h

example : (refSnapshot snapExCP).map Prod.fst = [snapNameBmp, snapNameAstral] := by decide

example : refSeed (some [("a", [1])]) ([] : QSnap String Nat) = .ok (refRestore [("a", [1])]) :=
  rfl
example : (refSeed (some [("a", [1])]) [("b", [])] : Except String (QMarking String Nat)).toBool
    = true := by decide
example : (refSeed (some [("a", [1])]) [("b", [2])] : Except String (QMarking String Nat)).toBool
    = false := by decide

end Libpetri.Reference
