import Libpetri.Novel.RouteB.Decide
import Libpetri.Reference.Decide
import Libpetri.Spec.Registry

set_option linter.missingDocs true
set_option autoImplicit false

/-!
# The graph layer of the verifier (RefVerifier L2)

Every graph route of the verifier is one build loop at a different explorer: the enumeration
route ([VER-017]) and its stubborn-set reduction ([VER-024]) at the identity explorer of a
successor function, Route B ([VER-012]) at the name explorer, the timed class graph ([VER-010],
[VER-023]) at a class-key explorer. The loop is `Novel.RouteB.Decide.build`: breadth-first, the
class budget tested when a class is taken from the worklist, the total budget as a stop oracle,
an optional early stop at the first violating class, and the verdict `Decide.verdict` (a
`Proven` only from a closed graph that was not stopped, a violation read off any prefix). This
file adds what the routes report beside the verdict, and the state-space cache.

* **Computable build** (`buildD`, `buildD_eq`): the same loop with a decidable key test, so
  concrete graphs can be evaluated by `decide` in examples and mutants.
* **Edges** (`edges`): the labelled edges `(i, l, j)` of the built graph, read from each class
  whose successors were looked at (`opened`: the expanded classes, plus the parent of an
  early-stopped class), each pointing at the stored class with the successor's key.
* **Shortest witness** (`shortest`, `trace`): a breadth-first search over the edges, layer by
  layer. `trace_spec`: the witness of a stored class is a path of the built graph, no longer
  than any other path there (`shortest in the BUILT graph`), and `trace_erun` lifts it to a real
  run of the explorer ending in a state with the class's key.
* **Closed and truncated** (`build_complete_lt`, `build_truncated_ge`, `build_budget_eq`,
  `build_budget_le`): a build that was neither stopped nor stopped early closed exactly when it
  has fewer classes than the budget; a graph that closed with `C` classes is the build at every
  budget above `C`, and every budget of `C` or less truncates.
* **Taken labels** (`taken`, `taken_sound`, `taken_complete`): a label on an edge is one some
  reachable state fires; on a closed graph, every label a reachable state fires is on an edge.
* **The cache** (`Slot`, `Use`, `cacheLookup`, `useVerdict`, `CacheKey`, `cacheQuery`): the
  state machine of one entry and of a keyed cache, without concurrency.
* **The enumeration instance** (`enumE`): the identity explorer of `Reference.succ`; stored
  classes are reachable markings, the witness is a `Reference.Run`, and a closed graph stores
  every reachable marking.
* **The graph route** (`GraphRoute`, `refGraphRoute`): the build, the verdict and the witness as
  one abstract object, the witness registered for the blocks.
-/

namespace Libpetri.Spec.Verifier.Graph

open Libpetri Libpetri.Novel.RouteB

/-! ## The identity explorer and the computable build -/

section Build

variable {S K L : Type}

/-- The identity explorer of a successor function: a class is a state and its key is the state
itself. The enumeration route of [VER-017] is the build at this explorer. -/
def idExplorer (succ : S → List (L × S)) : Explorer S S L where
  key := id
  bound := fun _ => 0
  succ := fun _ => succ

/-- The identity explorer is key-equivariant: equal keys are equal states, and the successor
list does not read the counter. -/
theorem idExplorer_equivariant (succ : S → List (L × S)) : (idExplorer succ).Equivariant := by
  refine ⟨fun a b c c' h _ _ => ?_⟩
  change a = b at h
  subst h
  exact List.Perm.refl _

variable (E : Explorer S K L) [DecidableEq K]

/-- `Decide.expandB` with the decidable key test. -/
def expandD (bad : S → Bool) (stopAt : Bool) : List S → List (L × S) → List S × Bool
  | cls, [] => (cls, false)
  | cls, (_, y) :: ys =>
    if cls.any (fun z => decide (E.key z = E.key y)) then expandD bad stopAt cls ys
    else if stopAt && bad y then (cls ++ [y], true)
    else expandD bad stopAt (cls ++ [y]) ys

theorem expandD_eq (bad : S → Bool) (stopAt : Bool) :
    ∀ (cls : List S) (ys : List (L × S)),
      expandD E bad stopAt cls ys = Decide.expandB E bad stopAt cls ys
  | cls, [] => by simp [expandD, Decide.expandB]
  | cls, (l, y) :: ys => by
    classical
    simp only [expandD, Decide.expandB]
    by_cases hk : ∃ z ∈ cls, E.key z = E.key y
    · have hany : cls.any (fun z => decide (E.key z = E.key y)) = true := by
        simpa [List.any_eq_true] using hk
      rw [if_pos hany, if_pos hk]
      exact expandD_eq bad stopAt cls ys
    · have hany : ¬ cls.any (fun z => decide (E.key z = E.key y)) = true := by
        simpa [List.any_eq_true] using hk
      rw [if_neg hany, if_neg hk]
      split
      · rfl
      · exact expandD_eq bad stopAt (cls ++ [y]) ys

/-- `Decide.loop` with the decidable key test. -/
def loopD (maxClasses : ℕ) (cut : ℕ → Bool) (bad : S → Bool) (stopAt : Bool) :
    ℕ → List S → ℕ → ℕ → Decide.Out S
  | 0, cls, exp, _ => ⟨cls, exp, false, true, false⟩
  | fuel + 1, cls, exp, c =>
    match cls[exp]? with
    | none => ⟨cls, exp, true, false, false⟩
    | some x =>
      if maxClasses ≤ cls.length then ⟨cls, exp, false, false, false⟩
      else if cut fuel then ⟨cls, exp, false, true, false⟩
      else
        match expandD E bad stopAt cls (E.succ c x) with
        | (cls', true) => ⟨cls', exp, false, false, true⟩
        | (cls', false) =>
          loopD maxClasses cut bad stopAt fuel cls' (exp + 1) (Decide.nextC E c (E.succ c x))

theorem loopD_eq (maxClasses : ℕ) (cut : ℕ → Bool) (bad : S → Bool) (stopAt : Bool) :
    ∀ fuel cls exp c, loopD E maxClasses cut bad stopAt fuel cls exp c =
      Decide.loop E maxClasses cut bad stopAt fuel cls exp c
  | 0, cls, exp, c => rfl
  | fuel + 1, cls, exp, c => by
    simp only [loopD, Decide.loop, expandD_eq]
    rcases cls[exp]? with _ | x
    · rfl
    · simp only
      split_ifs
      · rfl
      · rfl
      · rcases Decide.expandB E bad stopAt cls (E.succ c x) with ⟨cls', _ | _⟩
        · exact loopD_eq maxClasses cut bad stopAt fuel _ _ _
        · rfl

/-- **The computable build**: `Decide.build` with the decidable key test (`buildD_eq`). -/
def buildD (maxClasses : ℕ) (cut : ℕ → Bool) (bad : S → Bool) (stopAt : Bool) (fuel : ℕ)
    (x0 : S) : Decide.Out S :=
  if stopAt && bad x0 then ⟨[x0], 0, false, false, true⟩
  else loopD E maxClasses cut bad stopAt fuel [x0] 0 (E.bound x0)

/-- The computable build is the build of `Novel.RouteB.Decide`. -/
theorem buildD_eq (maxClasses : ℕ) (cut : ℕ → Bool) (bad : S → Bool) (stopAt : Bool) (fuel : ℕ)
    (x0 : S) : buildD E maxClasses cut bad stopAt fuel x0 =
      Decide.build E maxClasses cut bad stopAt fuel x0 := by
  simp only [buildD, Decide.build, loopD_eq]

end Build

/-! ## Paths and breadth-first search over a labelled edge list -/

section Bfs

variable {L : Type}

/-- A path of an edge list from node `a`, built at its end: the labels in order and the last
node. -/
inductive Walk (es : List (ℕ × L × ℕ)) (a : ℕ) : List L → ℕ → Prop
  /-- The empty path stays at `a`. -/
  | nil : Walk es a [] a
  /-- A path to `b` followed by an edge `(b, l, c)` is a path to `c`. -/
  | snoc {tr : List L} {b c : ℕ} {l : L} : Walk es a tr b → (b, l, c) ∈ es →
      Walk es a (tr ++ [l]) c

/-- Append the candidates whose node is new, in order; the first candidate of a node wins. -/
def addNew : List (ℕ × List L) → List (ℕ × List L) → List (ℕ × List L)
  | acc, [] => acc
  | acc, (j, t) :: cs =>
    if acc.any (fun e => e.1 == j) then addNew acc cs else addNew (acc ++ [(j, t)]) cs

/-- One edge further from every visited node: the target and the path extended by the label. -/
def cands (es : List (ℕ × L × ℕ)) (vis : List (ℕ × List L)) : List (ℕ × List L) :=
  vis.flatMap fun v => (es.filter fun e => e.1 == v.1).map fun e => (e.2.2, v.2 ++ [e.2.1])

/-- The breadth-first layers from `a`: after `k` rounds, every node within `k` edges of `a`, each
with the first path found to it. -/
def bfs (es : List (ℕ × L × ℕ)) (a : ℕ) : ℕ → List (ℕ × List L)
  | 0 => [(a, [])]
  | k + 1 => addNew (bfs es a k) (cands es (bfs es a k))

/-- The path the search recorded for node `j` after `fuel` rounds, if it reached `j`. -/
def shortest (es : List (ℕ × L × ℕ)) (a fuel j : ℕ) : Option (List L) :=
  ((bfs es a fuel).find? (fun e => e.1 == j)).map Prod.snd

theorem addNew_prefix : ∀ (acc cs : List (ℕ × List L)), ∃ t, addNew acc cs = acc ++ t
  | acc, [] => ⟨[], by simp [addNew]⟩
  | acc, (j, t) :: cs => by
    simp only [addNew]
    split
    · exact addNew_prefix acc cs
    · obtain ⟨u, hu⟩ := addNew_prefix (acc ++ [(j, t)]) cs
      exact ⟨(j, t) :: u, by rw [hu]; simp⟩

theorem mem_addNew : ∀ (acc cs : List (ℕ × List L)) (e : ℕ × List L),
    e ∈ addNew acc cs → e ∈ acc ∨ e ∈ cs
  | acc, [], e, h => Or.inl h
  | acc, (j, t) :: cs, e, h => by
    simp only [addNew] at h
    split at h
    · rcases mem_addNew acc cs e h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · rcases mem_addNew _ cs e h with h | h
      · rcases List.mem_append.mp h with h | h
        · exact Or.inl h
        · rw [List.mem_singleton.mp h]; exact Or.inr List.mem_cons_self
      · exact Or.inr (List.mem_cons_of_mem _ h)

theorem addNew_cover : ∀ (acc cs : List (ℕ × List L)) (j : ℕ),
    (j ∈ acc.map Prod.fst ∨ j ∈ cs.map Prod.fst) → j ∈ (addNew acc cs).map Prod.fst
  | acc, [], j, h => by
    rcases h with h | h
    · exact h
    · simp at h
  | acc, (j', t) :: cs, j, h => by
    simp only [addNew]
    split
    · rename_i hany
      apply addNew_cover acc cs j
      rcases h with h | h
      · exact Or.inl h
      · rcases List.mem_cons.mp h with h | h
        · left
          obtain ⟨e, he, hej⟩ := List.any_eq_true.mp hany
          simp only [beq_iff_eq] at hej
          exact List.mem_map.mpr ⟨e, he, by simp at h; rw [h, hej]⟩
        · exact Or.inr h
    · apply addNew_cover _ cs j
      rcases h with h | h
      · left; simp only [List.map_append, List.mem_append]; exact Or.inl h
      · rcases List.mem_cons.mp h with h | h
        · left; simp only [List.map_append, List.mem_append]; right; simp at h; simp [h]
        · exact Or.inr h

theorem addNew_nodup : ∀ (acc cs : List (ℕ × List L)), (acc.map Prod.fst).Nodup →
    ((addNew acc cs).map Prod.fst).Nodup
  | acc, [], h => h
  | acc, (j, t) :: cs, h => by
    simp only [addNew]
    split
    · exact addNew_nodup acc cs h
    · rename_i hany
      apply addNew_nodup _ cs
      rw [List.map_append, List.nodup_append]
      refine ⟨h, List.nodup_singleton _, fun a ha b hb => ?_⟩
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
      subst hb
      intro hab
      subst hab
      apply hany
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
      exact List.any_eq_true.mpr ⟨e, he, by simp⟩

theorem bfs_prefix (es : List (ℕ × L × ℕ)) (a : ℕ) :
    ∀ k k', k ≤ k' → ∃ t, bfs es a k' = bfs es a k ++ t := by
  intro k k' h
  induction h with
  | refl => exact ⟨[], by simp⟩
  | step _ ih =>
    obtain ⟨t, ht⟩ := ih
    obtain ⟨u, hu⟩ := addNew_prefix (bfs es a _) (cands es (bfs es a _))
    exact ⟨t ++ u, by simp only [bfs]; rw [hu, ht, List.append_assoc]⟩

theorem bfs_nodup (es : List (ℕ × L × ℕ)) (a : ℕ) : ∀ k, ((bfs es a k).map Prod.fst).Nodup
  | 0 => by simp [bfs]
  | k + 1 => addNew_nodup _ _ (bfs_nodup es a k)

/-- Every recorded path is a path of the edge list, no longer than the number of rounds. -/
theorem bfs_sound (es : List (ℕ × L × ℕ)) (a : ℕ) :
    ∀ k (j : ℕ) (t : List L), (j, t) ∈ bfs es a k → Walk es a t j ∧ t.length ≤ k
  | 0, j, t, h => by
    simp only [bfs, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨.nil, by simp⟩
  | k + 1, j, t, h => by
    simp only [bfs] at h
    rcases mem_addNew _ _ _ h with h | h
    · obtain ⟨hw, hl⟩ := bfs_sound es a k j t h
      exact ⟨hw, by omega⟩
    · obtain ⟨v, hv, he⟩ := List.mem_flatMap.mp h
      obtain ⟨e, hef, hee⟩ := List.mem_map.mp he
      obtain ⟨hes, heq⟩ := List.mem_filter.mp hef
      simp only [beq_iff_eq] at heq
      simp only [Prod.mk.injEq] at hee
      obtain ⟨rfl, rfl⟩ := hee
      obtain ⟨hw, hl⟩ := bfs_sound es a k v.1 v.2 hv
      refine ⟨.snoc hw ?_, by simp; omega⟩
      rw [← heq]
      exact hes

/-- Every node a path of at most `k` edges reaches is recorded after `k` rounds. -/
theorem bfs_complete (es : List (ℕ × L × ℕ)) (a : ℕ) {t : List L} {j : ℕ}
    (hw : Walk es a t j) : ∀ k, t.length ≤ k → j ∈ (bfs es a k).map Prod.fst := by
  induction hw with
  | nil =>
    intro k _
    obtain ⟨u, hu⟩ := bfs_prefix es a 0 k (Nat.zero_le _)
    rw [hu]; simp [bfs]
  | @snoc tr b c l _ he ih =>
    intro k hk
    simp only [List.length_append, List.length_singleton] at hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hb := ih k' (by omega)
    obtain ⟨v, hv, hvb⟩ := List.mem_map.mp hb
    simp only [bfs]
    apply addNew_cover
    right
    refine List.mem_map.mpr ⟨(c, v.2 ++ [l]), ?_, rfl⟩
    refine List.mem_flatMap.mpr ⟨v, hv, List.mem_map.mpr ⟨(b, l, c), ?_, rfl⟩⟩
    exact List.mem_filter.mpr ⟨he, by simp [hvb]⟩

theorem find_of_nodup {xs : List (ℕ × List L)} (hnd : (xs.map Prod.fst).Nodup) {j : ℕ}
    {t : List L} (h : (j, t) ∈ xs) : (xs.find? (fun e => e.1 == j)).map Prod.snd = some t := by
  induction xs with
  | nil => simp at h
  | cons e xs ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp h with h | h
    · subst h; simp
    · have hne : e.1 ≠ j := fun he => hnd.1 (he ▸ List.mem_map.mpr ⟨(j, t), h, rfl⟩)
      have hb : (e.1 == j) = false := by simpa using hne
      rw [List.find?_cons, hb]
      exact ih hnd.2 h

theorem find_mem {xs : List (ℕ × List L)} {j : ℕ} {t : List L}
    (h : (xs.find? (fun e => e.1 == j)).map Prod.snd = some t) : (j, t) ∈ xs := by
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
  have hj := List.find?_some he
  simp only [beq_iff_eq] at hj
  have := List.mem_of_find?_eq_some he
  rw [← hj]
  exact this

/-- The recorded path is a path of the edge list. -/
theorem shortest_sound {es : List (ℕ × L × ℕ)} {a n j : ℕ} {t : List L}
    (h : shortest es a n j = some t) : Walk es a t j :=
  (bfs_sound es a n j t (find_mem h)).1

/-- **The recorded path is a shortest one**: no longer than any path of at most `n` edges. -/
theorem shortest_min {es : List (ℕ × L × ℕ)} {a n j : ℕ} {t' : List L}
    (hw : Walk es a t' j) (hn : t'.length ≤ n) :
    ∃ t, shortest es a n j = some t ∧ t.length ≤ t'.length := by
  have hj := bfs_complete es a hw t'.length le_rfl
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hj
  obtain ⟨u, hu⟩ := bfs_prefix es a t'.length n hn
  refine ⟨v.2, ?_, (bfs_sound es a _ v.1 v.2 hv).2⟩
  apply find_of_nodup (bfs_nodup es a n)
  rw [hu]
  exact List.mem_append_left _ hv

/-- Once some path of at most `n` edges reaches `j`, the recorded path is a path no longer than
any path at all. -/
theorem shortest_spec {es : List (ℕ × L × ℕ)} {a n j : ℕ} {t0 : List L}
    (hw0 : Walk es a t0 j) (hn0 : t0.length ≤ n) :
    ∃ t, shortest es a n j = some t ∧ Walk es a t j ∧
      ∀ t', Walk es a t' j → t.length ≤ t'.length := by
  obtain ⟨t, ht, hlen⟩ := shortest_min hw0 hn0
  refine ⟨t, ht, shortest_sound ht, fun t' hw' => ?_⟩
  rcases Nat.lt_or_ge n t'.length with h | h
  · omega
  · obtain ⟨t'', ht'', hl''⟩ := shortest_min hw' h
    rw [ht] at ht''
    cases ht''
    exact hl''

end Bfs

/-! ## The edges of a built graph -/

section Edges

variable {S K L : Type} (E : Explorer S K L) [DecidableEq K]

/-- The index of the stored class with the key of `y` (the first one; a build stores each key
once, `build_par`). -/
def keyIdx (cls : List S) (y : S) : Option ℕ := cls.findIdx? (fun z => decide (E.key z = E.key y))

/-- How many classes had their successors looked at: the expanded ones, and after an early stop
also the parent of the class that stopped the build. -/
def opened (o : Decide.Out S) : ℕ := if o.early then o.exp + 1 else o.exp

/-- The edges out of class `i`: one per successor, to the stored class with the successor's key.
A successor with no stored key-twin (cut off by an early stop) has no edge. -/
def succEdges (o : Decide.Out S) (i : ℕ) : List (ℕ × L × ℕ) :=
  match o.cls[i]? with
  | some x => (E.succ (E.bound x) x).filterMap fun ly =>
      (keyIdx E o.cls ly.2).map fun j => (i, ly.1, j)
  | none => []

/-- **The labelled edges of a built graph**: `(i, l, j)` when class `i` was opened and one of its
successors, by a step labelled `l`, has the key of class `j`. -/
def edges (o : Decide.Out S) : List (ℕ × L × ℕ) := (List.range (opened o)).flatMap (succEdges E o)

/-- The labels on the edges of a built graph: what the graph saw fire. -/
def taken (o : Decide.Out S) : List L := (edges E o).map fun e => e.2.1

/-- What an edge is. -/
theorem mem_edges {o : Decide.Out S} {i j : ℕ} {l : L} :
    (i, l, j) ∈ edges E o ↔ i < opened o ∧ ∃ x y, o.cls[i]? = some x ∧
      (l, y) ∈ E.succ (E.bound x) x ∧ keyIdx E o.cls y = some j := by
  simp only [edges, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨i', hi', he⟩
    unfold succEdges at he
    split at he
    · rename_i x hx
      obtain ⟨ly, hly, hm⟩ := List.mem_filterMap.mp he
      obtain ⟨j', hj', hje⟩ := Option.map_eq_some_iff.mp hm
      simp only [Prod.mk.injEq] at hje
      obtain ⟨rfl, rfl, rfl⟩ := hje
      exact ⟨hi', x, ly.2, hx, hly, hj'⟩
    · simp at he
  · rintro ⟨hi, x, y, hx, hy, hj⟩
    refine ⟨i, hi, ?_⟩
    unfold succEdges
    rw [hx]
    exact List.mem_filterMap.mpr ⟨(l, y), hy, by simp [hj]⟩

/-- No two stored classes share a key. -/
def KeysInj (cls : List S) : Prop :=
  ∀ (i j : ℕ) (zi zj : S), cls[i]? = some zi → cls[j]? = some zj → E.key zi = E.key zj → i = j

variable {E}

theorem keyIdx_some {cls : List S} {y : S} {j : ℕ} (h : keyIdx E cls y = some j) :
    ∃ z, cls[j]? = some z ∧ E.key z = E.key y := by
  obtain ⟨hlt, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp h
  exact ⟨cls[j], List.getElem?_eq_getElem hlt, by simpa using hp⟩

theorem keyIdx_of {cls : List S} (hinj : KeysInj E cls) {y z : S} {j : ℕ} (hz : cls[j]? = some z)
    (hk : E.key z = E.key y) : keyIdx E cls y = some j := by
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hz
  refine List.findIdx?_eq_some_iff_getElem.mpr ⟨hlt, by simpa using hk, fun j' hj' hp => ?_⟩
  have hk' : E.key cls[j'] = E.key cls[j] := by simp at hp; rw [hp, hk]
  have := hinj j' j _ _ (List.getElem?_eq_getElem (by omega)) (List.getElem?_eq_getElem hlt) hk'
  omega

theorem keyIdx_isSome {cls : List S} {y z : S} (hz : z ∈ cls) (hk : E.key z = E.key y) :
    ∃ j, keyIdx E cls y = some j := by
  cases h : keyIdx E cls y with
  | some j => exact ⟨j, rfl⟩
  | none =>
    have := List.findIdx?_eq_none_iff.mp h z hz
    simp [hk] at this

theorem getElem?_snoc_cases {cls : List S} {y z : S} {i : ℕ} (h : (cls ++ [y])[i]? = some z) :
    (i < cls.length ∧ cls[i]? = some z) ∨ (i = cls.length ∧ z = y) := by
  rcases Nat.lt_or_ge i cls.length with hi | hi
  · rw [List.getElem?_append_left hi] at h; exact Or.inl ⟨hi, h⟩
  · rw [List.getElem?_append_right hi] at h
    rcases Nat.lt_or_ge (i - cls.length) 1 with h1 | h1
    · have : i = cls.length := by omega
      subst this
      simp at h
      exact Or.inr ⟨rfl, h.symm⟩
    · rw [List.getElem?_eq_none (by simpa using h1)] at h; cases h

omit [DecidableEq K] in
theorem keysInj_snoc {cls : List S} {y : S} (hinj : KeysInj E cls)
    (hnew : ¬ ∃ z ∈ cls, E.key z = E.key y) : KeysInj E (cls ++ [y]) := by
  intro i j zi zj hi hj hk
  rcases getElem?_snoc_cases hi with ⟨hil, hi'⟩ | ⟨rfl, rfl⟩ <;>
    rcases getElem?_snoc_cases hj with ⟨hjl, hj'⟩ | ⟨rfl, rfl⟩
  · exact hinj i j zi zj hi' hj' hk
  · exact absurd ⟨zi, List.mem_of_getElem? hi', hk⟩ hnew
  · exact absurd ⟨zj, List.mem_of_getElem? hj', hk.symm⟩ hnew
  · rfl

theorem expandB_inj (bad : S → Bool) (stopAt : Bool) :
    ∀ (ys : List (L × S)) (cls : List S), KeysInj E cls →
      KeysInj E (Decide.expandB E bad stopAt cls ys).1
  | [], cls, h => by simpa [Decide.expandB] using h
  | (l, y) :: ys, cls, h => by
    classical
    unfold Decide.expandB
    by_cases hk : ∃ z ∈ cls, E.key z = E.key y
    · rw [if_pos hk]; exact expandB_inj bad stopAt ys cls h
    · rw [if_neg hk]
      split
      · exact keysInj_snoc h hk
      · exact expandB_inj bad stopAt ys _ (keysInj_snoc h hk)

/-- The loop invariant of the parent argument: the initial class first, keys stored once,
bounds below the counter, and every later class a successor of an expanded class before it. -/
structure PInv (x0 : S) (cls : List S) (exp c : ℕ) : Prop where
  /-- The initial class is class `0`. -/
  head : cls[0]? = some x0
  /-- No key is stored twice. -/
  inj : KeysInj E cls
  /-- The counter is fresh for every stored class. -/
  bound : ∀ z ∈ cls, E.bound z ≤ c
  /-- At most every stored class is expanded. -/
  exp_le : exp ≤ cls.length
  /-- Every class after the first has an expanded parent before it. -/
  par : ∀ j y, cls[j]? = some y → 0 < j → ∃ i x c', i < j ∧ i < exp ∧ cls[i]? = some x ∧
    E.bound x ≤ c' ∧ ∃ l, (l, y) ∈ E.succ c' x

/-- What the parent argument gives on a build's result: the initial class first, keys stored
once, every later class a successor of an opened class before it. -/
def ParOut (x0 : S) (o : Decide.Out S) : Prop :=
  o.cls[0]? = some x0 ∧ KeysInj E o.cls ∧
    ∀ j y, o.cls[j]? = some y → 0 < j → ∃ i x c', i < j ∧ i < opened o ∧ o.cls[i]? = some x ∧
      E.bound x ≤ c' ∧ ∃ l, (l, y) ∈ E.succ c' x

omit [DecidableEq K] in
/-- The parent property after one expansion of class `exp`. -/
theorem par_step {x0 x : S} {cls t : List S} {exp c : ℕ} (hinv : PInv (E := E) x0 cls exp c)
    (hx : cls[exp]? = some x) (htm : ∀ z ∈ t, ∃ l, (l, z) ∈ E.succ c x) :
    ∀ j y, (cls ++ t)[j]? = some y → 0 < j → ∃ i x' c', i < j ∧ i < exp + 1 ∧
      (cls ++ t)[i]? = some x' ∧ E.bound x' ≤ c' ∧ ∃ l, (l, y) ∈ E.succ c' x' := by
  have hxlt : exp < cls.length := by
    rcases Nat.lt_or_ge exp cls.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hx; cases hx
  intro j y hj hj0
  rcases Nat.lt_or_ge j cls.length with hjl | hjl
  · rw [List.getElem?_append_left hjl] at hj
    obtain ⟨i, x', c', hij, hie, hix, hb, l, hl⟩ := hinv.par j y hj hj0
    exact ⟨i, x', c', hij, by omega, by rw [List.getElem?_append_left (by omega)]; exact hix,
      hb, l, hl⟩
  · rw [List.getElem?_append_right hjl] at hj
    obtain ⟨l, hl⟩ := htm y (List.mem_of_getElem? hj)
    exact ⟨exp, x, c, by omega, by omega, by rw [List.getElem?_append_left hxlt]; exact hx,
      hinv.bound x (List.mem_of_getElem? hx), l, hl⟩

theorem loop_par (maxClasses : ℕ) (cut : ℕ → Bool) (bad : S → Bool) (stopAt : Bool) (x0 : S) :
    ∀ fuel cls exp c, PInv (E := E) x0 cls exp c →
      ParOut (E := E) x0 (Decide.loop E maxClasses cut bad stopAt fuel cls exp c)
  | 0, cls, exp, c, hinv => by
    simp only [Decide.loop]
    exact ⟨hinv.head, hinv.inj, fun j y hj hj0 => by
      simpa [opened] using hinv.par j y hj hj0⟩
  | fuel + 1, cls, exp, c, hinv => by
    have hpar0 : ∀ e, ParOut (E := E) x0 ⟨cls, exp, false, e, false⟩ := fun e =>
      ⟨hinv.head, hinv.inj, fun j y hj hj0 => by simpa [opened] using hinv.par j y hj hj0⟩
    simp only [Decide.loop]
    split
    · exact ⟨hinv.head, hinv.inj, fun j y hj hj0 => by simpa [opened] using hinv.par j y hj hj0⟩
    · rename_i x hx
      have hxlt : exp < cls.length := by
        rcases Nat.lt_or_ge exp cls.length with h | h
        · exact h
        · rw [List.getElem?_eq_none h] at hx; cases hx
      have h0 : 0 < cls.length := by omega
      obtain ⟨⟨t, ht, htm⟩, -⟩ := Decide.expandB_spec E bad stopAt (E.succ c x) cls
      have hinj := expandB_inj (E := E) bad stopAt (E.succ c x) cls hinv.inj
      split
      · exact hpar0 false
      · split
        · exact hpar0 true
        · split
          · rename_i cls' heq
            rw [heq] at ht hinj
            simp only at ht hinj
            subst ht
            refine ⟨by rw [List.getElem?_append_left h0]; exact hinv.head, hinj, ?_⟩
            intro j y hj hj0
            obtain ⟨i, x', c', h1, h2, h3⟩ := par_step hinv hx htm j y hj hj0
            exact ⟨i, x', c', h1, by simpa [opened] using h2, h3⟩
          · rename_i cls' heq
            rw [heq] at ht hinj
            simp only at ht hinj
            subst ht
            apply loop_par maxClasses cut bad stopAt x0 fuel
            refine ⟨by rw [List.getElem?_append_left h0]; exact hinv.head, hinj, ?_, ?_,
              par_step hinv hx htm⟩
            · intro z hz
              rcases List.mem_append.mp hz with hz | hz
              · exact Nat.le_trans (hinv.bound z hz) (Decide.le_nextC_start E c _)
              · obtain ⟨l, hl⟩ := htm z hz
                exact Decide.le_nextC E c _ (l, z) hl
            · simp only [List.length_append]; omega

/-- **The parent property of a build**: the initial class is class `0`, every key is stored once,
and every later class is a successor of an opened class before it. -/
theorem build_par (maxClasses : ℕ) (cut : ℕ → Bool) (bad : S → Bool) (stopAt : Bool) (fuel : ℕ)
    (x0 : S) : ParOut (E := E) x0 (Decide.build E maxClasses cut bad stopAt fuel x0) := by
  simp only [Decide.build]
  split
  · refine ⟨rfl, fun i j zi zj hi hj _ => ?_, fun j y hj hj0 => ?_⟩
    · rcases getElem?_snoc_cases (cls := []) (by simpa using hi) with ⟨h, _⟩ | ⟨rfl, -⟩
      · simp at h
      · rcases getElem?_snoc_cases (cls := []) (by simpa using hj) with ⟨h, _⟩ | ⟨rfl, -⟩
        · simp at h
        · rfl
    · rcases getElem?_snoc_cases (cls := []) (by simpa using hj) with ⟨h, _⟩ | ⟨rfl, -⟩
      · simp at h
      · simp at hj0
  · apply loop_par
    refine ⟨rfl, fun i j zi zj hi hj _ => ?_, fun z hz => ?_, by simp, fun j y hj hj0 => ?_⟩
    · rcases getElem?_snoc_cases (cls := []) (by simpa using hi) with ⟨h, _⟩ | ⟨rfl, -⟩
      · simp at h
      · rcases getElem?_snoc_cases (cls := []) (by simpa using hj) with ⟨h, _⟩ | ⟨rfl, -⟩
        · simp at h
        · rfl
    · rw [List.mem_singleton.mp hz]
    · rcases getElem?_snoc_cases (cls := []) (by simpa using hj) with ⟨h, _⟩ | ⟨rfl, -⟩
      · simp at h
      · simp at hj0

/-- **Every stored class is reached along the edges** from class `0`, by a path of at most its
index many edges (the build is breadth-first, so a parent's index is smaller). -/
theorem build_walk (hE : E.Equivariant) {maxClasses : ℕ} {cut : ℕ → Bool} {bad : S → Bool}
    {stopAt : Bool} {fuel : ℕ} {x0 : S} :
    ∀ j, j < (Decide.build E maxClasses cut bad stopAt fuel x0).cls.length →
      ∃ t, Walk (edges E (Decide.build E maxClasses cut bad stopAt fuel x0)) 0 t j ∧
        t.length ≤ j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact ⟨[], .nil, le_rfl⟩
    · obtain ⟨-, hinj, hpar⟩ := build_par (E := E) maxClasses cut bad stopAt fuel x0
      have hy := List.getElem?_eq_getElem hj
      obtain ⟨i, x, c', hij, hio, hx, hb, l, hl⟩ := hpar j _ hy hj0
      have hperm := hE.key_succ x x c' (E.bound x) rfl hb le_rfl
      have hin : (l, E.key (Decide.build E maxClasses cut bad stopAt fuel x0).cls[j]) ∈
          (E.succ (E.bound x) x).map E.keyed :=
        hperm.mem_iff.mp (List.mem_map.mpr ⟨_, hl, rfl⟩)
      obtain ⟨y', hy', hky'⟩ := Explorer.exists_succ_of_keyed hin
      have hidx := keyIdx_of hinj hy hky'.symm
      have hilen : i < (Decide.build E maxClasses cut bad stopAt fuel x0).cls.length := by
        omega
      obtain ⟨t, ht, htl⟩ := ih i hij hilen
      refine ⟨t ++ [l], .snoc ht ((mem_edges E).mpr ⟨hio, x, y', hx, hy', hidx⟩), ?_⟩
      simp only [List.length_append, List.length_singleton]
      omega

end Edges

/-! ## Runs of an explorer and the witness of a stored class -/

section Witness

variable {S K L : Type} (E : Explorer S K L)

/-- A labelled run of an explorer, built at its end, each step taken with a counter fresh for its
source. -/
inductive ERun (a : S) : List L → S → Prop
  /-- The empty run stays at `a`. -/
  | nil : ERun a [] a
  /-- A run to `b` followed by a successor of `b` is a run to that successor. -/
  | snoc {tr : List L} {b s : S} {c : ℕ} {l : L} : ERun a tr b → E.bound b ≤ c →
      (l, s) ∈ E.succ c b → ERun a (tr ++ [l]) s

variable {E}

/-- A run reaches its end. -/
theorem erun_reach {a s : S} {tr : List L} (h : ERun E a tr s) : Explorer.Reach E a s := by
  induction h with
  | nil => exact Explorer.Reach.init
  | snoc _ hb hl ih => exact Explorer.Reach.step ih hb hl

variable [DecidableEq K]

/-- **A path of a built graph is a real run**: it lifts to a run of the explorer from the initial
class, ending in a state with the key of the path's last class. -/
theorem walk_erun (hE : E.Equivariant) {o : Decide.Out S} {x0 : S} (h0 : o.cls[0]? = some x0)
    {t : List L} {j : ℕ} (hw : Walk (edges E o) 0 t j) :
    ∀ y, o.cls[j]? = some y → ∃ s, ERun E x0 t s ∧ E.key s = E.key y := by
  induction hw with
  | nil =>
    intro y hy
    rw [h0] at hy
    cases hy
    exact ⟨x0, .nil, rfl⟩
  | @snoc tr b c l _ he ih =>
    intro y hy
    obtain ⟨-, x, y', hx, hy', hidx⟩ := (mem_edges E).mp he
    obtain ⟨z, hz, hkz⟩ := keyIdx_some hidx
    rw [hy] at hz
    cases hz
    obtain ⟨s, hs, hks⟩ := ih x hx
    have hperm := hE.key_succ x s (E.bound x) (E.bound s) hks.symm le_rfl le_rfl
    have hin : (l, E.key y') ∈ (E.succ (E.bound s) s).map E.keyed :=
      hperm.mem_iff.mp (List.mem_map.mpr ⟨_, hy', rfl⟩)
    obtain ⟨s', hs', hks'⟩ := Explorer.exists_succ_of_keyed hin
    exact ⟨s', .snoc hs le_rfl hs', hks'.trans hkz.symm⟩

variable (E)

/-- **The witness of class `i`**: the path the breadth-first search over the edges records for
it, empty when there is none. -/
def trace (o : Decide.Out S) (i : ℕ) : List L := (shortest (edges E o) 0 o.cls.length i).getD []

variable {E}

/-- **The witness is a shortest path of the built graph**: a path from class `0` to class `i`,
of at most `i` edges, and no longer than any other path of the built graph to class `i`. -/
theorem trace_spec (hE : E.Equivariant) {maxClasses : ℕ} {cut : ℕ → Bool} {bad : S → Bool}
    {stopAt : Bool} {fuel : ℕ} {x0 : S} {i : ℕ}
    (hi : i < (Decide.build E maxClasses cut bad stopAt fuel x0).cls.length) :
    Walk (edges E (Decide.build E maxClasses cut bad stopAt fuel x0)) 0
        (trace E (Decide.build E maxClasses cut bad stopAt fuel x0) i) i ∧
      (trace E (Decide.build E maxClasses cut bad stopAt fuel x0) i).length ≤ i ∧
      ∀ t', Walk (edges E (Decide.build E maxClasses cut bad stopAt fuel x0)) 0 t' i →
        (trace E (Decide.build E maxClasses cut bad stopAt fuel x0) i).length ≤ t'.length := by
  obtain ⟨t0, hw0, hl0⟩ := build_walk hE i hi
  obtain ⟨t, ht, hw, hmin⟩ :=
    shortest_spec (n := (Decide.build E maxClasses cut bad stopAt fuel x0).cls.length) hw0
      (by omega)
  have htr : trace E (Decide.build E maxClasses cut bad stopAt fuel x0) i = t := by
    simp [trace, ht]
  rw [htr]
  exact ⟨hw, Nat.le_trans (hmin t0 hw0) hl0, hmin⟩

/-- **The witness is a real run** from the initial state to a state with the class's key. -/
theorem trace_erun (hE : E.Equivariant) {maxClasses : ℕ} {cut : ℕ → Bool} {bad : S → Bool}
    {stopAt : Bool} {fuel : ℕ} {x0 y : S} {i : ℕ}
    (hy : (Decide.build E maxClasses cut bad stopAt fuel x0).cls[i]? = some y) :
    ∃ s, ERun E x0 (trace E (Decide.build E maxClasses cut bad stopAt fuel x0) i) s ∧
      E.key s = E.key y := by
  have hi : i < (Decide.build E maxClasses cut bad stopAt fuel x0).cls.length := by
    rcases Nat.lt_or_ge i (Decide.build E maxClasses cut bad stopAt fuel x0).cls.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hy; cases hy
  exact walk_erun hE (build_par maxClasses cut bad stopAt fuel x0).1 (trace_spec hE hi).1 y hy

end Witness

/-! ## Closed, truncated and the class budget -/

section Budget

variable {S K L : Type} (E : Explorer S K L)

/-- The loop only appends classes. -/
theorem loop_prefix (maxClasses : ℕ) (cut : ℕ → Bool) (bad : S → Bool) (stopAt : Bool) :
    ∀ fuel cls exp c, ∃ t, (Decide.loop E maxClasses cut bad stopAt fuel cls exp c).cls = cls ++ t
  | 0, cls, exp, c => ⟨[], by simp [Decide.loop]⟩
  | fuel + 1, cls, exp, c => by
    simp only [Decide.loop]
    split
    · exact ⟨[], by simp⟩
    · rename_i x hx
      obtain ⟨⟨t, ht, -⟩, -⟩ := Decide.expandB_spec E bad stopAt (E.succ c x) cls
      split
      · exact ⟨[], by simp⟩
      · split
        · exact ⟨[], by simp⟩
        · split
          · rename_i cls' heq
            rw [heq] at ht
            exact ⟨t, ht⟩
          · rename_i cls' heq
            rw [heq] at ht
            simp only at ht
            obtain ⟨u, hu⟩ := loop_prefix maxClasses cut bad stopAt fuel cls' (exp + 1)
              (Decide.nextC E c (E.succ c x))
            exact ⟨t ++ u, by rw [hu, ht, List.append_assoc]⟩

/-- A closed loop result was neither stopped nor stopped early. -/
theorem loop_flags (maxClasses : ℕ) (cut : ℕ → Bool) (bad : S → Bool) (stopAt : Bool) :
    ∀ fuel cls exp c, (Decide.loop E maxClasses cut bad stopAt fuel cls exp c).complete = true →
      (Decide.loop E maxClasses cut bad stopAt fuel cls exp c).stopped = false ∧
      (Decide.loop E maxClasses cut bad stopAt fuel cls exp c).early = false
  | 0, cls, exp, c => by simp [Decide.loop]
  | fuel + 1, cls, exp, c => by
    simp only [Decide.loop]
    split
    · simp
    · split
      · simp
      · split
        · simp
        · split
          · simp
          · exact loop_flags maxClasses cut bad stopAt fuel _ _ _

/-- A closed build was neither stopped nor stopped early. -/
theorem build_flags {maxClasses : ℕ} {cut : ℕ → Bool} {bad : S → Bool} {stopAt : Bool}
    {fuel : ℕ} {x0 : S} (h : (Decide.build E maxClasses cut bad stopAt fuel x0).complete = true) :
    (Decide.build E maxClasses cut bad stopAt fuel x0).stopped = false ∧
      (Decide.build E maxClasses cut bad stopAt fuel x0).early = false := by
  simp only [Decide.build] at h ⊢
  split at h
  · cases h
  · rename_i hb
    rw [if_neg hb]
    exact loop_flags E maxClasses cut bad stopAt fuel _ _ _ h

theorem loop_complete_lt (maxClasses : ℕ) (cut : ℕ → Bool) (bad : S → Bool) (stopAt : Bool) :
    ∀ fuel cls exp c, exp ≤ cls.length → (exp = cls.length → cls.length < maxClasses) →
      (Decide.loop E maxClasses cut bad stopAt fuel cls exp c).complete = true →
      (Decide.loop E maxClasses cut bad stopAt fuel cls exp c).cls.length < maxClasses
  | 0, cls, exp, c, _, _, h => by simp [Decide.loop] at h
  | fuel + 1, cls, exp, c, hle, hq, h => by
    simp only [Decide.loop] at h ⊢
    split at h
    · rename_i hnone
      have : cls.length ≤ exp := by
        by_contra hc
        rw [List.getElem?_eq_getElem (by omega)] at hnone
        cases hnone
      exact hq (by omega)
    · rename_i x hx
      have hxlt : exp < cls.length := by
        rcases Nat.lt_or_ge exp cls.length with h' | h'
        · exact h'
        · rw [List.getElem?_eq_none h'] at hx; cases hx
      split at h
      · cases h
      · rename_i hn
        rw [if_neg hn]
        split at h
        · cases h
        · rename_i hcut
          rw [if_neg hcut]
          obtain ⟨⟨t, ht, -⟩, -⟩ := Decide.expandB_spec E bad stopAt (E.succ c x) cls
          split at h
          · cases h
          · rename_i cls' heq
            rw [heq] at ht
            simp only at ht
            apply loop_complete_lt maxClasses cut bad stopAt fuel cls' (exp + 1) _ _ _ h
            · rw [ht, List.length_append]; omega
            · intro he
              rw [ht, List.length_append] at he ⊢
              omega

/-- **A closed graph has fewer classes than the budget.** -/
theorem build_complete_lt {maxClasses : ℕ} {cut : ℕ → Bool} {bad : S → Bool} {stopAt : Bool}
    {fuel : ℕ} {x0 : S} (h : (Decide.build E maxClasses cut bad stopAt fuel x0).complete = true) :
    (Decide.build E maxClasses cut bad stopAt fuel x0).cls.length < maxClasses := by
  simp only [Decide.build] at h ⊢
  split at h
  · cases h
  · rename_i hb
    rw [if_neg hb]
    exact loop_complete_lt E maxClasses cut bad stopAt fuel [x0] 0 _ (by simp)
      (by simp) h

theorem loop_truncated_ge (maxClasses : ℕ) (cut : ℕ → Bool) (bad : S → Bool) (stopAt : Bool) :
    ∀ fuel cls exp c,
      (Decide.loop E maxClasses cut bad stopAt fuel cls exp c).complete = false →
      (Decide.loop E maxClasses cut bad stopAt fuel cls exp c).stopped = false →
      (Decide.loop E maxClasses cut bad stopAt fuel cls exp c).early = false →
      maxClasses ≤ (Decide.loop E maxClasses cut bad stopAt fuel cls exp c).cls.length
  | 0, cls, exp, c => by simp [Decide.loop]
  | fuel + 1, cls, exp, c => by
    simp only [Decide.loop]
    split
    · simp
    · split
      · rename_i hn; intro _ _ _; exact hn
      · split
        · simp
        · split
          · simp
          · exact loop_truncated_ge maxClasses cut bad stopAt fuel _ _ _

/-- **A graph cut off at the class budget holds at least the budget's number of classes**: a
build that did not close, was not stopped and did not stop early was truncated, and that
happens only when the class count reached the budget. -/
theorem build_truncated_ge {maxClasses : ℕ} {cut : ℕ → Bool} {bad : S → Bool} {stopAt : Bool}
    {fuel : ℕ} {x0 : S}
    (hc : (Decide.build E maxClasses cut bad stopAt fuel x0).complete = false)
    (hs : (Decide.build E maxClasses cut bad stopAt fuel x0).stopped = false)
    (he : (Decide.build E maxClasses cut bad stopAt fuel x0).early = false) :
    maxClasses ≤ (Decide.build E maxClasses cut bad stopAt fuel x0).cls.length := by
  simp only [Decide.build] at hc hs he ⊢
  split at he
  · cases he
  · rename_i hb
    rw [if_neg hb] at hc hs ⊢
    exact loop_truncated_ge E maxClasses cut bad stopAt fuel _ _ _ hc hs he

/-- **Closed iff fewer classes than the budget**, for a build that was not stopped and did not
stop early. -/
theorem build_closed_iff {maxClasses : ℕ} {cut : ℕ → Bool} {bad : S → Bool} {stopAt : Bool}
    {fuel : ℕ} {x0 : S}
    (hs : (Decide.build E maxClasses cut bad stopAt fuel x0).stopped = false)
    (he : (Decide.build E maxClasses cut bad stopAt fuel x0).early = false) :
    (Decide.build E maxClasses cut bad stopAt fuel x0).complete = true ↔
      (Decide.build E maxClasses cut bad stopAt fuel x0).cls.length < maxClasses := by
  refine ⟨build_complete_lt E, fun hlt => ?_⟩
  cases hc : (Decide.build E maxClasses cut bad stopAt fuel x0).complete
  · have := build_truncated_ge E hc hs he; omega
  · rfl

theorem loop_budget_eq (n n' : ℕ) (cut : ℕ → Bool) (bad : S → Bool) (stopAt : Bool) :
    ∀ fuel cls exp c, (Decide.loop E n cut bad stopAt fuel cls exp c).complete = true →
      (Decide.loop E n cut bad stopAt fuel cls exp c).cls.length < n' →
      Decide.loop E n' cut bad stopAt fuel cls exp c = Decide.loop E n cut bad stopAt fuel cls exp c
  | 0, cls, exp, c, _, _ => rfl
  | fuel + 1, cls, exp, c, h1, h2 => by
    have hlen : cls.length < n' := by
      obtain ⟨t, ht⟩ := loop_prefix E n cut bad stopAt (fuel + 1) cls exp c
      have := congrArg List.length ht
      simp only [List.length_append] at this
      omega
    simp only [Decide.loop] at h1 ⊢
    cases hx : cls[exp]? with
    | none => rfl
    | some x =>
      simp only [hx] at h1 ⊢
      have hn' : ¬ n' ≤ cls.length := by omega
      rw [if_neg hn']
      by_cases hn : n ≤ cls.length
      · rw [if_pos hn] at h1; cases h1
      · rw [if_neg hn] at h1 ⊢
        by_cases hcut : cut fuel = true
        · rw [if_pos hcut] at h1; cases h1
        · rw [if_neg hcut] at h1
          rw [if_neg hcut, if_neg hcut]
          have h2' : (Decide.loop E n cut bad stopAt (fuel + 1) cls exp c).cls.length < n' := h2
          simp only [Decide.loop, hx, if_neg hn, if_neg hcut] at h2'
          generalize Decide.expandB E bad stopAt cls (E.succ c x) = r at h1 h2' ⊢
          obtain ⟨cls', f⟩ := r
          cases f
          · simp only at h1 h2' ⊢
            exact loop_budget_eq n n' cut bad stopAt fuel cls' (exp + 1) _ h1 h2'
          · simp at h1

/-- **A closed graph is the build at every larger budget**: a graph that closed with `C`
classes is what the build returns at any budget above `C` (same stop oracle and fuel). -/
theorem build_budget_eq {n n' : ℕ} {cut : ℕ → Bool} {bad : S → Bool} {stopAt : Bool}
    {fuel : ℕ} {x0 : S} (h : (Decide.build E n cut bad stopAt fuel x0).complete = true)
    (hn' : (Decide.build E n cut bad stopAt fuel x0).cls.length < n') :
    Decide.build E n' cut bad stopAt fuel x0 = Decide.build E n cut bad stopAt fuel x0 := by
  simp only [Decide.build] at h hn' ⊢
  split at h
  · cases h
  · rename_i hb
    rw [if_neg hb] at hn'
    rw [if_neg hb, if_neg hb]
    exact loop_budget_eq E n n' cut bad stopAt fuel _ _ _ h hn'

/-- **Every budget of `C` or less truncates** a graph that closes with `C` classes. -/
theorem build_budget_le {n n' : ℕ} {cut : ℕ → Bool} {bad : S → Bool} {stopAt : Bool}
    {fuel : ℕ} {x0 : S} (h : (Decide.build E n cut bad stopAt fuel x0).complete = true)
    (hn' : n' ≤ (Decide.build E n cut bad stopAt fuel x0).cls.length) :
    (Decide.build E n' cut bad stopAt fuel x0).complete = false := by
  cases h' : (Decide.build E n' cut bad stopAt fuel x0).complete
  · rfl
  · have hlt' := build_complete_lt E h'
    have hlt := build_complete_lt E h
    have heq := build_budget_eq E (n' := n) h' (by omega)
    rw [heq] at hn'
    omega

end Budget

/-! ## What a built graph saw fire -/

section Taken

variable {S K L : Type} {E : Explorer S K L} [DecidableEq K]

/-- **A taken label is a real step**: every label on an edge of any build (closed, truncated,
stopped or stopped early) is fired by some reachable state. -/
theorem taken_sound {maxClasses : ℕ} {cut : ℕ → Bool} {bad : S → Bool} {stopAt : Bool}
    {fuel : ℕ} {x0 : S} {l : L}
    (h : l ∈ taken E (Decide.build E maxClasses cut bad stopAt fuel x0)) :
    ∃ y c s, Explorer.Reach E x0 y ∧ E.bound y ≤ c ∧ (l, s) ∈ E.succ c y := by
  obtain ⟨⟨i, l', j⟩, he, rfl⟩ := List.mem_map.mp h
  obtain ⟨-, x, y, hx, hy, -⟩ := (mem_edges E).mp he
  exact ⟨x, E.bound x, y, Decide.build_reach E (List.mem_of_getElem? hx), le_rfl, hy⟩

/-- **On a closed graph every step of a reachable state is an edge**: the edge leaves the class
with the state's key and enters the class with the successor's key. -/
theorem edges_complete (hE : E.Equivariant) {maxClasses : ℕ} {cut : ℕ → Bool}
    {bad : S → Bool} {stopAt : Bool} {fuel : ℕ} {x0 : S}
    (hc : (Decide.build E maxClasses cut bad stopAt fuel x0).complete = true)
    {y s : S} {c : ℕ} {l : L} (hy : Explorer.Reach E x0 y) (hb : E.bound y ≤ c)
    (hl : (l, s) ∈ E.succ c y) :
    ∃ i j z w, (i, l, j) ∈ edges E (Decide.build E maxClasses cut bad stopAt fuel x0) ∧
      (Decide.build E maxClasses cut bad stopAt fuel x0).cls[i]? = some z ∧
      E.key z = E.key y ∧
      (Decide.build E maxClasses cut bad stopAt fuel x0).cls[j]? = some w ∧
      E.key w = E.key s := by
  obtain ⟨-, hclosed, -, hall⟩ := Decide.build_spec E maxClasses cut bad stopAt fuel x0
  have hx0 := Decide.x0_mem_build (E := E) maxClasses cut bad stopAt fuel x0
  obtain ⟨z, hz, hkz⟩ := Decide.complete_twin hE hx0 hclosed (hall hc) y hy
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hz
  have hilt : i < (Decide.build E maxClasses cut bad stopAt fuel x0).cls.length := by
    rcases Nat.lt_or_ge i (Decide.build E maxClasses cut bad stopAt fuel x0).cls.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hi; cases hi
  have hearly := (build_flags E hc).2
  have hperm := hE.key_succ y z c (E.bound z) hkz.symm hb le_rfl
  have hin : (l, E.key s) ∈ (E.succ (E.bound z) z).map E.keyed :=
    hperm.mem_iff.mp (List.mem_map.mpr ⟨_, hl, rfl⟩)
  obtain ⟨s', hs', hks'⟩ := Explorer.exists_succ_of_keyed hin
  obtain ⟨w, hw, hkw⟩ := Decide.complete_twin hE hx0 hclosed (hall hc) s (Explorer.Reach.step hy hb hl)
  obtain ⟨j, hj⟩ := keyIdx_isSome (E := E) hw (hkw.trans hks'.symm)
  obtain ⟨w', hw', hkw'⟩ := keyIdx_some hj
  refine ⟨i, j, z, w', (mem_edges E).mpr ⟨?_, z, s', hi, hs', hj⟩, hi, hkz, hw', hkw'.trans hks'⟩
  simp only [opened, hearly, Bool.false_eq_true, if_false]
  rw [hall hc]
  exact hilt

/-- **On a closed graph the taken labels are exactly the fired ones**: a label is on an edge iff
some reachable state fires it. -/
theorem taken_complete (hE : E.Equivariant) {maxClasses : ℕ} {cut : ℕ → Bool}
    {bad : S → Bool} {stopAt : Bool} {fuel : ℕ} {x0 : S}
    (hc : (Decide.build E maxClasses cut bad stopAt fuel x0).complete = true) (l : L) :
    l ∈ taken E (Decide.build E maxClasses cut bad stopAt fuel x0) ↔
      ∃ y c s, Explorer.Reach E x0 y ∧ E.bound y ≤ c ∧ (l, s) ∈ E.succ c y := by
  refine ⟨taken_sound, fun ⟨y, c, s, hy, hb, hl⟩ => ?_⟩
  obtain ⟨i, j, -, -, he, -⟩ := edges_complete hE hc hy hb hl
  exact List.mem_map.mpr ⟨(i, l, j), he, rfl⟩

end Taken

/-! ## The state-space cache ([VER-017], [VER-024])

One entry is a slot: empty, a closed graph, or a truncation remembered with its budget and its
explored prefix. A query at a budget is answered without building when the slot already knows
the answer: a closed graph of `C` classes is reused for a budget above `C` and read as a prefix
(declined) for a budget of `C` or less; a truncation at `B` declines every budget of `B` or less.
Otherwise the query builds; a closed result is stored as closed, a truncated one with the
query's budget, and a stopped one (total budget or cancellation, [VER-013]) leaves the slot as
it was. A build that fails (`none`) leaves the slot as it was too. Concurrency (one build per
entry, waiting) is not modelled. -/

section Cache

variable {S K L : Type}

/-- One cache entry. -/
inductive Slot (S : Type) where
  /-- Nothing known: never built, or the build that owned the slot failed. -/
  | empty
  /-- A graph that closed. -/
  | closed (o : Decide.Out S)
  /-- A graph cut off at the class budget `budget`, kept with its explored prefix. -/
  | truncated (budget : ℕ) (o : Decide.Out S)

/-- How a query was answered. -/
inductive Use (S : Type) where
  /-- Built at the query's budget; read as without a cache. -/
  | built (o : Decide.Out S)
  /-- A cached closed graph, smaller than the budget; read as closed. -/
  | reused (o : Decide.Out S)
  /-- A cached graph the budget would truncate; read as an explored prefix, nothing built. -/
  | declined (o : Decide.Out S)

/-- The graph a query reads. -/
def Use.graph : Use S → Decide.Out S
  | .built o => o
  | .reused o => o
  | .declined o => o

/-- What a build leaves in the slot: closed as closed, truncated with the budget, stopped not at
all. -/
def store (slot : Slot S) (budget : ℕ) (o : Decide.Out S) : Slot S :=
  if o.complete then .closed o else if o.stopped then slot else .truncated budget o

/-- Build into the slot, or leave it as it was when the build failed. -/
def buildInto (slot : Slot S) (budget : ℕ) : Option (Decide.Out S) → Option (Use S) × Slot S
  | none => (none, slot)
  | some o => (some (.built o), store slot budget o)

/-- **One query on one entry**: `build` is what a build at `budget` would return (`none`: it
failed); it is read only when the slot does not answer. -/
def cacheLookup (slot : Slot S) (budget : ℕ) (build : Option (Decide.Out S)) :
    Option (Use S) × Slot S :=
  match slot with
  | .closed o => (some (if o.cls.length < budget then .reused o else .declined o), slot)
  | .truncated B o => if budget ≤ B then (some (.declined o), slot) else buildInto slot budget build
  | .empty => buildInto slot budget build

/-- The verdict a query reads off its answer: a declined graph never closes. -/
def useVerdict (E : Explorer S K L) (u : Use S) (p : Decide.Prop' S L) : Decide.Verdict :=
  match u with
  | .built o => Decide.verdict E o p
  | .reused o => Decide.verdict E o p
  | .declined o => Decide.verdict E { o with complete := false } p

/-- The key of an entry: the net, the transitions the in-flight split of [VER-004] rewrote, the
initial marking, and whether the graph is reduced by stubborn sets ([VER-024]). -/
structure CacheKey (N M : Type) where
  /-- The caller's net (or its structural fingerprint). -/
  net : N
  /-- The transitions the in-flight split rewrote. -/
  split : List String
  /-- The initial marking. -/
  m0 : M
  /-- Whether the graph is the stubborn-set reduced one. -/
  reduced : Bool
  deriving DecidableEq

/-- A keyed cache: one slot per key. -/
abbrev Cache (κ S : Type) := κ → Slot S

/-- **One query on a keyed cache**: only the entry of its key is read or written. -/
def cacheQuery {κ : Type} [DecidableEq κ] (c : Cache κ S) (k : κ) (budget : ℕ)
    (build : Option (Decide.Out S)) : Option (Use S) × Cache κ S :=
  ((cacheLookup (c k) budget build).1, Function.update c k (cacheLookup (c k) budget build).2)

/-- A query never touches another key's entry. -/
theorem cacheQuery_frame {κ : Type} [DecidableEq κ] (c : Cache κ S) {k k' : κ} (h : k' ≠ k)
    (budget : ℕ) (build : Option (Decide.Out S)) : (cacheQuery c k budget build).2 k' = c k' := by
  simp [cacheQuery, Function.update, h]

/-- A query's own entry is what `cacheLookup` leaves. -/
theorem cacheQuery_self {κ : Type} [DecidableEq κ] (c : Cache κ S) (k : κ) (budget : ℕ)
    (build : Option (Decide.Out S)) :
    (cacheQuery c k budget build).2 k = (cacheLookup (c k) budget build).2 := by
  simp [cacheQuery]

/-- **A failed build leaves the entry as it found it.** -/
theorem cacheLookup_fail (slot : Slot S) (budget : ℕ) : (cacheLookup slot budget none).2 = slot := by
  cases slot with
  | empty => rfl
  | closed o => rfl
  | truncated B o =>
    simp only [cacheLookup]
    split <;> rfl

/-- **A cached closed graph answers without building**: reused above its class count, declined at
or below it. -/
theorem cacheLookup_closed (o : Decide.Out S) (budget : ℕ) (build : Option (Decide.Out S)) :
    cacheLookup (.closed o) budget build =
      (some (if o.cls.length < budget then .reused o else .declined o), .closed o) := rfl

/-- **A remembered truncation at `B` declines every budget of `B` or less without building.** -/
theorem cacheLookup_truncated_le {B budget : ℕ} (o : Decide.Out S) (h : budget ≤ B)
    (build : Option (Decide.Out S)) :
    cacheLookup (.truncated B o) budget build = (some (.declined o), .truncated B o) := by
  simp [cacheLookup, h]

/-- **A larger budget builds again and replaces the truncation** (unless the build is stopped or
fails, which leave it). -/
theorem cacheLookup_truncated_gt {B budget : ℕ} (o o' : Decide.Out S) (h : B < budget) :
    cacheLookup (.truncated B o) budget (some o') =
      (some (.built o'), store (.truncated B o) budget o') := by
  simp [cacheLookup, buildInto, Nat.not_le.mpr h]

/-- Reading a graph as a prefix does not change which classes violate. -/
theorem violatesAt_declined (E : Explorer S K L) (o : Decide.Out S) (p : Decide.Prop' S L) :
    Decide.violatesAt E { o with complete := false } p = Decide.violatesAt E o p := rfl

/-- The verdict of a graph read as a prefix. -/
theorem verdict_declined (E : Explorer S K L) (o : Decide.Out S) (p : Decide.Prop' S L) :
    Decide.verdict E { o with complete := false } p =
      if o.stopped then .unknown else
        match (List.range o.cls.length).find? (Decide.violatesAt E o p) with
        | some i => .violated i
        | none => .unknown := by
  simp only [Decide.verdict, violatesAt_declined]
  split
  · rfl
  · split
    · rename_i hi; rw [hi]
    · rename_i hn; rw [hn]; rfl

/-- **A graph read as a prefix never proves.** -/
theorem verdict_declined_ne_proven (E : Explorer S K L) (o : Decide.Out S) (p : Decide.Prop' S L) :
    Decide.verdict E { o with complete := false } p ≠ .proven := by
  rw [verdict_declined]
  split
  · simp
  · split <;> simp

/-- A violation read off a graph as a prefix is the violation read off the graph. -/
theorem verdict_declined_violated {E : Explorer S K L} {o : Decide.Out S} {p : Decide.Prop' S L}
    {i : ℕ} (h : Decide.verdict E { o with complete := false } p = .violated i) :
    Decide.verdict E o p = .violated i := by
  rw [verdict_declined] at h
  simp only [Decide.verdict]
  split at h
  · cases h
  · rename_i hs
    rw [if_neg hs]
    split at h
    · rename_i j hj
      rw [hj]
      exact h
    · cases h

/-- The verdict a query reads is the verdict of its graph, unless the graph was declined. -/
theorem useVerdict_violated {E : Explorer S K L} {u : Use S} {p : Decide.Prop' S L} {i : ℕ}
    (h : useVerdict E u p = .violated i) : Decide.verdict E u.graph p = .violated i := by
  cases u with
  | built o => exact h
  | reused o => exact h
  | declined o => exact verdict_declined_violated h

/-- A graph some build returned, for some budget, stop oracle, early-stop predicate and fuel. -/
def Built (E : Explorer S K L) (x0 : S) (o : Decide.Out S) : Prop :=
  ∃ n cut bad stopAt fuel, o = Decide.build E n cut bad stopAt fuel x0

/-- What an entry may hold: nothing, a closed graph some build returned, or a truncation at `B`
that the build at `B` returned (not closed, not stopped). -/
def SlotOK (E : Explorer S K L) (x0 : S) : Slot S → Prop
  | .empty => True
  | .closed o => Built E x0 o ∧ o.complete = true
  | .truncated B o => (∃ cut bad stopAt fuel, o = Decide.build E B cut bad stopAt fuel x0) ∧
      o.complete = false ∧ o.stopped = false

/-- **The cache keeps what it may hold**, and every answer reads a graph some build returned,
when the query's build is the build at its own budget. -/
theorem cacheLookup_ok {E : Explorer S K L} {x0 : S} {slot : Slot S} (hslot : SlotOK E x0 slot)
    {budget : ℕ} {build : Option (Decide.Out S)}
    (hb : ∀ o, build = some o → ∃ cut bad stopAt fuel, o = Decide.build E budget cut bad stopAt fuel x0) :
    SlotOK E x0 (cacheLookup slot budget build).2 ∧
      ∀ u, (cacheLookup slot budget build).1 = some u → Built E x0 u.graph := by
  have hbuild : SlotOK E x0 (buildInto slot budget build).2 ∧
      ∀ u, (buildInto slot budget build).1 = some u → Built E x0 u.graph := by
    cases build with
    | none => exact ⟨hslot, fun u h => by cases h⟩
    | some o =>
      obtain ⟨cut, bad, stopAt, fuel, rfl⟩ := hb _ rfl
      refine ⟨?_, fun u h => ?_⟩
      · simp only [buildInto, store]
        split
        · exact ⟨⟨budget, cut, bad, stopAt, fuel, rfl⟩, by assumption⟩
        · split
          · exact hslot
          · rename_i hc hs
            exact ⟨⟨cut, bad, stopAt, fuel, rfl⟩, by simpa using hc, by simpa using hs⟩
      · simp only [buildInto, Option.some.injEq] at h
        subst h
        exact ⟨budget, cut, bad, stopAt, fuel, rfl⟩
  cases slot with
  | empty => exact hbuild
  | closed o =>
    refine ⟨hslot, fun u h => ?_⟩
    simp only [cacheLookup, Option.some.injEq] at h
    subst h
    split <;> exact hslot.1
  | truncated B o =>
    simp only [cacheLookup]
    split
    · refine ⟨hslot, fun u h => ?_⟩
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨cut, bad, stopAt, fuel, h⟩ := hslot.1
      exact ⟨B, cut, bad, stopAt, fuel, h⟩
    · exact hbuild

/-- **A cached answer proves only from a closed graph smaller than the query's budget**. -/
theorem cache_proven {E : Explorer S K L} {x0 : S} {slot : Slot S} (hslot : SlotOK E x0 slot)
    {budget : ℕ} {build : Option (Decide.Out S)}
    (hb : ∀ o, build = some o → ∃ cut bad stopAt fuel, o = Decide.build E budget cut bad stopAt fuel x0)
    {u : Use S} (hu : (cacheLookup slot budget build).1 = some u) {p : Decide.Prop' S L}
    (hp : useVerdict E u p = .proven) :
    u.graph.complete = true ∧ u.graph.stopped = false ∧ u.graph.cls.length < budget := by
  have hbuilt : ∀ o, (buildInto slot budget build).1 = some u → u = .built o →
      o.cls.length < budget ∨ o.complete = false := by
    intro o h hu'
    cases build with
    | none => cases h
    | some o' =>
      simp only [buildInto, Option.some.injEq] at h
      subst h
      cases hu'
      obtain ⟨cut, bad, stopAt, fuel, rfl⟩ := hb _ rfl
      cases hc : (Decide.build E budget cut bad stopAt fuel x0).complete
      · exact Or.inr rfl
      · exact Or.inl (build_complete_lt E hc)
  cases u with
  | declined o => exact absurd hp (verdict_declined_ne_proven E o p)
  | built o =>
    obtain ⟨hc, hs⟩ := Decide.truncated_never_proven E o p hp
    refine ⟨hc, hs, ?_⟩
    have hbi : (buildInto slot budget build).1 = some (.built o) := by
      cases slot with
      | empty => exact hu
      | closed o' =>
        simp only [cacheLookup, Option.some.injEq] at hu
        split at hu <;> cases hu
      | truncated B o' =>
        simp only [cacheLookup] at hu
        split at hu
        · cases hu
        · exact hu
    rcases hbuilt o hbi rfl with h | h
    · exact h
    · simp [h] at hc
  | reused o =>
    obtain ⟨hc, hs⟩ := Decide.truncated_never_proven E o p hp
    refine ⟨hc, hs, ?_⟩
    cases slot with
    | empty =>
      cases build with
      | none => cases hu
      | some o' => simp [cacheLookup, buildInto] at hu
    | closed o' =>
      simp only [cacheLookup, Option.some.injEq] at hu
      split at hu
      · cases hu; assumption
      · cases hu
    | truncated B o' =>
      simp only [cacheLookup] at hu
      split at hu
      · cases hu
      · cases build with
        | none => cases hu
        | some o'' => simp [buildInto] at hu

/-- **A cached safety violation stands**: the class it names is stored, reachable and bad,
whatever answered the query. -/
theorem cache_violated_safety {E : Explorer S K L} {x0 : S} {u : Use S} (hu : Built E x0 u.graph)
    {bad : S → Bool} {i : ℕ} (h : useVerdict E u (.safety bad) = .violated i) :
    ∃ x, u.graph.cls[i]? = some x ∧ Explorer.Reach E x0 x ∧ bad x = true := by
  obtain ⟨n, cut, sb, stopAt, fuel, he⟩ := hu
  have h' := useVerdict_violated h
  rw [he] at h' ⊢
  exact Decide.prefix_safety_sound h'

/-- **A cached quiescence violation stands**: the class it names is stored, reachable, expanded,
bad, and fires only reapable transitions. -/
theorem cache_violated_quiescence {E : Explorer S K L} (hE : E.Equivariant) {x0 : S} {u : Use S}
    (hu : Built E x0 u.graph) {bad : S → Bool} {reap : L → Bool} {i : ℕ}
    (h : useVerdict E u (.quiescence bad reap) = .violated i) :
    ∃ x, u.graph.cls[i]? = some x ∧ i < u.graph.exp ∧ Explorer.Reach E x0 x ∧ bad x = true ∧
      ∀ c, E.bound x ≤ c → ∀ ly ∈ E.succ c x, reap ly.1 = true := by
  obtain ⟨n, cut, sb, stopAt, fuel, he⟩ := hu
  have h' := useVerdict_violated h
  rw [he] at h' ⊢
  exact Decide.prefix_quiescence_sound hE h'

/-- **Reusing a closed graph is answering without the cache**: a graph that closed is reused for
a budget above its class count, and it is exactly what the build at that budget returns (with
the same stop oracle and fuel), so verdict and witness are the uncached ones. -/
theorem cache_reused_eq (E : Explorer S K L) {n budget : ℕ} {cut : ℕ → Bool} {bad : S → Bool}
    {stopAt : Bool} {fuel : ℕ} {x0 : S}
    (hc : (Decide.build E n cut bad stopAt fuel x0).complete = true)
    (hb : (Decide.build E n cut bad stopAt fuel x0).cls.length < budget)
    (build : Option (Decide.Out S)) :
    (cacheLookup (.closed (Decide.build E n cut bad stopAt fuel x0)) budget build).1 =
        some (.reused (Decide.build E budget cut bad stopAt fuel x0)) ∧
      Decide.build E budget cut bad stopAt fuel x0 = Decide.build E n cut bad stopAt fuel x0 := by
  have heq := build_budget_eq E hc hb
  refine ⟨?_, heq⟩
  simp [cacheLookup, hb, heq]

/-- **A budget at or below a closed graph's class count is declined**, and the build at that
budget would not have closed either: the answer is a prefix reading on both sides. -/
theorem cache_closed_small (E : Explorer S K L) {n budget : ℕ} {cut : ℕ → Bool} {bad : S → Bool}
    {stopAt : Bool} {fuel : ℕ} {x0 : S}
    (hc : (Decide.build E n cut bad stopAt fuel x0).complete = true)
    (hb : budget ≤ (Decide.build E n cut bad stopAt fuel x0).cls.length)
    (build : Option (Decide.Out S)) :
    (cacheLookup (.closed (Decide.build E n cut bad stopAt fuel x0)) budget build).1 =
        some (.declined (Decide.build E n cut bad stopAt fuel x0)) ∧
      (Decide.build E budget cut bad stopAt fuel x0).complete = false := by
  refine ⟨?_, build_budget_le E hc hb⟩
  simp [cacheLookup, Nat.not_lt.mpr hb]

end Cache

/-! ## The enumeration instance: the identity explorer of the reference successor function -/

section Enum

variable {K : Type} [LinearOrder K]

open Reference in
/-- The explorer of the enumeration route ([VER-017]) on a reference net: a class is a canonical
marking, its successors are `Reference.succ` (every enabled transition, every way its firing can
end). -/
def enumE (net : Reference.Net K) :
    Explorer (Reference.Marking K) (Reference.Marking K) String :=
  idExplorer (Reference.succ net)

/-- The enumeration explorer is key-equivariant. -/
theorem enumE_equivariant (net : Reference.Net K) : (enumE net).Equivariant :=
  idExplorer_equivariant _

/-- A firing sequence extended by one step. -/
theorem run_snoc {net : Reference.Net K} {tr : List String} {a b c : K → ℕ} {l : String}
    (h : Reference.Run net tr a b) (hs : Reference.LStep net l b c) :
    Reference.Run net (tr ++ [l]) a c := by
  induction h with
  | nil m => exact .cons hs (.nil c)
  | cons h1 _ ih => exact .cons h1 (ih hs)

/-- **A run of the enumeration explorer is a firing sequence** of the net, between canonical
markings. -/
theorem enum_erun {net : Reference.Net K} {m0 m : Reference.Marking K} {tr : List String}
    (h : ERun (enumE net) m0 tr m) (hc : Reference.Canon m0) :
    Reference.Canon m ∧ Reference.Run net tr (Reference.get m0) (Reference.get m) := by
  induction h with
  | nil => exact ⟨hc, .nil _⟩
  | snoc _ _ hl ih =>
    obtain ⟨hc', hst⟩ := Reference.mem_succ ih.1 hl
    exact ⟨hc', run_snoc ih.2 hst⟩

/-- **Every class the enumeration reaches is a reachable marking.** -/
theorem enum_reach {net : Reference.Net K} {m0 m : Reference.Marking K}
    (h : Explorer.Reach (enumE net) m0 m) (hc : Reference.Canon m0) :
    Reference.Canon m ∧ Reference.Reach net (Reference.get m0) (Reference.get m) := by
  unfold Explorer.Reach at h
  induction h with
  | refl => exact ⟨hc, Relation.ReflTransGen.refl⟩
  | tail _ hs ih =>
    obtain ⟨c, l, -, hl⟩ := hs
    obtain ⟨hc', hst⟩ := Reference.mem_succ ih.1 hl
    exact ⟨hc', Relation.ReflTransGen.tail ih.2 ⟨l, hst⟩⟩

/-- **Every stored class of an enumeration build is a reachable marking**, closed graph or not. -/
theorem enum_stored {net : Reference.Net K} {n : ℕ} {cut : ℕ → Bool}
    {bad : Reference.Marking K → Bool} {stopAt : Bool} {fuel : ℕ} {m0 z : Reference.Marking K}
    (hz : z ∈ (Decide.build (enumE net) n cut bad stopAt fuel m0).cls) (hc : Reference.Canon m0) :
    Reference.Canon z ∧ Reference.Reach net (Reference.get m0) (Reference.get z) :=
  enum_reach (Decide.build_reach (enumE net) hz) hc

/-- **The witness of an enumeration build is a firing sequence** from the initial marking to the
class it names, and a shortest path of the built graph (`trace_spec`). -/
theorem enum_trace_run {net : Reference.Net K} {n : ℕ} {cut : ℕ → Bool}
    {bad : Reference.Marking K → Bool} {stopAt : Bool} {fuel : ℕ} {m0 y : Reference.Marking K}
    {i : ℕ} (hy : (Decide.build (enumE net) n cut bad stopAt fuel m0).cls[i]? = some y)
    (hc : Reference.Canon m0) :
    Reference.Run net (trace (enumE net) (Decide.build (enumE net) n cut bad stopAt fuel m0) i)
      (Reference.get m0) (Reference.get y) := by
  obtain ⟨s, hs, hks⟩ := trace_erun (enumE_equivariant net) hy
  change s = y at hks
  subst hks
  exact (enum_erun hs hc).2

/-- Reachability along the reference successor list is reachability of the enumeration
explorer. -/
theorem search_reach_enum {net : Reference.Net K} {m0 y : Reference.Marking K}
    (h : Reference.Search.Reach (Reference.succ net) m0 y) : Explorer.Reach (enumE net) m0 y := by
  unfold Explorer.Reach
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih =>
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hs
    exact Relation.ReflTransGen.tail ih ⟨0, e.1, le_rfl, he⟩

/-- **A closed enumeration graph stores every reachable marking.** -/
theorem enum_complete_stored {net : Reference.Net K} {n : ℕ} {cut : ℕ → Bool}
    {bad : Reference.Marking K → Bool} {stopAt : Bool} {fuel : ℕ} {m0 : Reference.Marking K}
    (hcomp : (Decide.build (enumE net) n cut bad stopAt fuel m0).complete = true)
    (hc : Reference.Canon m0) {f : K → ℕ} (hf : Reference.Reach net (Reference.get m0) f) :
    ∃ z ∈ (Decide.build (enumE net) n cut bad stopAt fuel m0).cls,
      Reference.Canon z ∧ Reference.get z = f := by
  obtain ⟨y, hcy, hgy, hry⟩ := Reference.search_reach_complete hc hf
  have hry' : Explorer.Reach (enumE net) m0 y := search_reach_enum hry
  obtain ⟨-, hclosed, -, hall⟩ := Decide.build_spec (enumE net) n cut bad stopAt fuel m0
  obtain ⟨z, hz, hkz⟩ := Decide.complete_twin (enumE_equivariant net)
    (Decide.x0_mem_build (E := enumE net) n cut bad stopAt fuel m0) hclosed (hall hcomp) y hry'
  change z = y at hkz
  subst hkz
  exact ⟨z, hz, hcy, hgy⟩

end Enum

/-! ## The graph route -/

/-- **A graph route**, abstractly: the build at an explorer (class budget, stop oracle, early-stop
predicate and switch, fuel, initial class), the verdict read off a built graph, and the witness
of a class. -/
structure GraphRoute (S K L : Type) where
  /-- The build. -/
  build : Explorer S K L → ℕ → (ℕ → Bool) → (S → Bool) → Bool → ℕ → S → Decide.Out S
  /-- The verdict read off a built graph. -/
  verdict : Explorer S K L → Decide.Out S → Decide.Prop' S L → Decide.Verdict
  /-- The witness of a class: the labels of a path from the initial class. -/
  trace : Explorer S K L → Decide.Out S → ℕ → List L

/-- **The reference graph route**: the build loop of `Novel.RouteB.Decide` (computable form), its
verdict, and the shortest path of the built graph as the witness. -/
def refGraphRoute {S K L : Type} [DecidableEq K] : GraphRoute S K L where
  build E := buildD E
  verdict E := Decide.verdict E
  trace E := trace E

#spec_witness refGraphRoute
#spec_witness cacheLookup
#spec_witness cacheQuery
#spec_witness useVerdict
#spec_witness taken
#spec_witness edges

/-- The reference route builds with `Novel.RouteB.Decide.build`. -/
theorem refGraphRoute_build {S K L : Type} [DecidableEq K] (E : Explorer S K L) (n : ℕ)
    (cut : ℕ → Bool) (bad : S → Bool) (stopAt : Bool) (fuel : ℕ) (x0 : S) :
    (refGraphRoute (S := S) (K := K) (L := L)).build E n cut bad stopAt fuel x0 =
      Decide.build E n cut bad stopAt fuel x0 :=
  buildD_eq E n cut bad stopAt fuel x0

/-! ## Worked examples -/

section Examples

/-- An unbounded producer `gen : G → G, A`, seen through the tokens on `A`: from `n` tokens,
`gen` gives `n + 1`. -/
def genSucc : ℕ → List (String × ℕ) := fun n => [("gen", n + 1)]

/-- The producer's graph at a class budget of 6: never closes. -/
def genGraph : Decide.Out ℕ :=
  buildD (idExplorer genSucc) 6 (fun _ => false) (fun _ => false) false 20 0

/-- The producer's graph is cut off at the budget: 6 classes stored, 5 expanded, not stopped. -/
theorem genGraph_truncated :
    genGraph.complete = false ∧ genGraph.stopped = false ∧ genGraph.cls.length = 6 ∧
      genGraph.exp = 5 := by decide

/-- On the truncated producer graph, "at most 2 tokens on `A`" is violated by class 3 (three
tokens), and the witness is `gen, gen, gen`, the shortest path to it in the built graph. -/
theorem genGraph_bound_violated :
    Decide.verdict (idExplorer genSucc) genGraph (.safety fun n => decide (2 < n)) =
        .violated 3 ∧
      trace (idExplorer genSucc) genGraph 3 = ["gen", "gen", "gen"] := by
  refine ⟨by decide, rfl⟩

/-- On the same truncated graph, deadlock freedom is not decided: no expanded class is without a
successor, the frontier class does not count, and nothing is proven from a prefix. -/
theorem genGraph_deadlock_declines :
    Decide.verdict (idExplorer genSucc) genGraph (.quiescence (fun _ => true) fun _ => false) =
      .unknown := by decide

/-- A fork: from `0`, `toB` gives `1` and `toA` gives `2`; from `1`, `toC` gives `3`; `2` and
`3` are dead. -/
def forkSucc : ℕ → List (String × ℕ)
  | 0 => [("toB", 1), ("toA", 2)]
  | 1 => [("toC", 3)]
  | _ => []

/-- The fork at budget 3 stops after expanding `0`: classes `0, 1, 2` stored, only `0` expanded.
The dead class `2` sits on the frontier, so deadlock freedom is not violated there: the route
declines. -/
theorem fork_frontier_declines :
    (buildD (idExplorer forkSucc) 3 (fun _ => false) (fun _ => false) false 20 0).exp = 1 ∧
      Decide.verdict (idExplorer forkSucc)
        (buildD (idExplorer forkSucc) 3 (fun _ => false) (fun _ => false) false 20 0)
        (.quiescence (fun _ => true) fun _ => false) = .unknown := by decide

/-- At budget 5 the fork closes with 4 classes, and deadlock freedom is violated at class `2`,
reached by `toA`. -/
theorem fork_closed_violated :
    (buildD (idExplorer forkSucc) 5 (fun _ => false) (fun _ => false) false 20 0).complete =
        true ∧
      Decide.verdict (idExplorer forkSucc)
        (buildD (idExplorer forkSucc) 5 (fun _ => false) (fun _ => false) false 20 0)
        (.quiescence (fun _ => true) fun _ => false) = .violated 2 ∧
      trace (idExplorer forkSucc)
        (buildD (idExplorer forkSucc) 5 (fun _ => false) (fun _ => false) false 20 0) 2 =
        ["toA"] := by
  refine ⟨by decide, by decide, rfl⟩

/-- A chain `0 → 1 → 2` by `t`: three classes. -/
def chainSucc : ℕ → List (String × ℕ) := fun n => if n < 2 then [("t", n + 1)] else []

/-- The chain's graph at a budget. -/
def chainGraph (n : ℕ) : Decide.Out ℕ :=
  buildD (idExplorer chainSucc) n (fun _ => false) (fun _ => false) false 20 0

/-- The budget boundary: the three-class chain closes at budget 4 and is truncated at budget 3,
so a graph closes exactly when it has fewer classes than the budget. -/
theorem chain_budget_boundary :
    (chainGraph 4).complete = true ∧ (chainGraph 4).cls.length = 3 ∧
      (chainGraph 3).complete = false ∧ (chainGraph 3).stopped = false := by decide

/-- The cache on the chain. A first query at budget 4 builds a closed graph and stores it. A
second query at budget 10 reuses it without building (its build argument is `none`). A query at
budget 2 is declined from the same entry. A truncation at budget 2 declines budget 1 without
building, and a failed build at budget 5 leaves it in place. -/
theorem chain_cache :
    (cacheLookup .empty 4 (some (chainGraph 4))).1 = some (.built (chainGraph 4)) ∧
      (cacheLookup .empty 4 (some (chainGraph 4))).2 = .closed (chainGraph 4) ∧
      (cacheLookup (.closed (chainGraph 4)) 10 none).1 = some (.reused (chainGraph 4)) ∧
      (cacheLookup (.closed (chainGraph 4)) 2 none).1 = some (.declined (chainGraph 4)) ∧
      (cacheLookup .empty 2 (some (chainGraph 2))).2 = .truncated 2 (chainGraph 2) ∧
      (cacheLookup (.truncated 2 (chainGraph 2)) 1 none).1 = some (.declined (chainGraph 2)) ∧
      (cacheLookup (.truncated 2 (chainGraph 2)) 5 none).2 = .truncated 2 (chainGraph 2) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · simp only [cacheLookup, buildInto, store]
    rw [if_pos (by decide)]
  · simp only [cacheLookup]
    rw [if_pos (by decide)]
  · simp only [cacheLookup]
    rw [if_neg (by decide)]
  · simp only [cacheLookup, buildInto, store]
    rw [if_neg (by decide), if_neg (by decide)]

/-- A chain `0 → 1 → 2` whose second step is `u`. At budget 2 the graph is cut off before class
`1` is expanded, so `u` is on no edge although it fires: a truncated graph cannot call it
unreachable. At budget 4 the graph closes and both labels are taken. -/
def twoStepSucc : ℕ → List (String × ℕ)
  | 0 => [("t", 1)]
  | 1 => [("u", 2)]
  | _ => []

/-- The truncated graph takes only `t`; the closed one takes `t` and `u`. -/
theorem twoStep_taken :
    taken (idExplorer twoStepSucc)
        (buildD (idExplorer twoStepSucc) 2 (fun _ => false) (fun _ => false) false 20 0) =
        ["t"] ∧
      taken (idExplorer twoStepSucc)
        (buildD (idExplorer twoStepSucc) 4 (fun _ => false) (fun _ => false) false 20 0) =
        ["t", "u"] := ⟨rfl, rfl⟩

end Examples

end Libpetri.Spec.Verifier.Graph
