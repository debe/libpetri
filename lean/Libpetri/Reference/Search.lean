import Std.Data.HashMap.Lemmas
import Mathlib.Logic.Relation

/-!
# Breadth-first exploration with a class cap

A generic breadth-first search over a labelled successor function. Discovered states live in a
hash map (`Seen`) that also records each state's BFS depth and the edge it was discovered by,
from which a shortest firing sequence is read back (`traceTo`). The frontier is processed level
by level: `frontier` is the current level, `next` collects the following one (newest first).

The search stops **incomplete** when a new state would exceed `cap` states, or when `fuel`
runs out; it is **complete** when both queues run dry. `2 * cap + 2` fuel always suffices
(each pop removes a distinct discovered state, each level swap needs a state discovered since
the last one), but nothing below depends on it: running out of fuel is reported as
incompleteness, never as a verdict.

Results (the invariant is `Enumeration.lean`'s, carried over to the hash map):
* `explore_reach`: every discovered state is reachable, complete or not;
* **`explore_complete_iff`**: when the search completes, a state is discovered iff it is
  reachable.
-/

namespace Libpetri.Reference.Search

variable {σ : Type} [BEq σ] [Hashable σ]

/-- Reachability along the successor function, labels forgotten. -/
def Reach (succ : σ → List (String × σ)) (x0 : σ) : σ → Prop :=
  Relation.ReflTransGen (fun a b => b ∈ (succ a).map Prod.snd) x0

/-- What is recorded per discovered state: BFS depth and the discovering edge. -/
structure Info (σ : Type) where
  depth  : Nat
  parent : Option (σ × String)

abbrev Seen (σ : Type) [BEq σ] [Hashable σ] := Std.HashMap σ (Info σ)

/-- The recorded depth of `x`. -/
def depthOf (seen : Seen σ) (x : σ) : Nat := (seen[x]?.map Info.depth).getD 0

/-- Expand `x`: every successor not yet seen is recorded (depth `dx + 1`, parent `x`) and
queued. The flag is `false` when a new state would make more than `cap`; the map is returned
either way, so it is never shared and every insertion is in place. -/
def expand (cap : Nat) (x : σ) (dx : Nat) :
    List (String × σ) → Seen σ → List σ → Seen σ × List σ × Bool
  | [], seen, next => (seen, next, true)
  | (l, y) :: ys, seen, next =>
    if seen.contains y then expand cap x dx ys seen next
    else if cap ≤ seen.size then (seen, next, false)
    else expand cap x dx ys (seen.insert y ⟨dx + 1, some (x, l)⟩) (y :: next)

/-- The level-by-level loop. Returns the discovered states and `complete`. -/
def loop (succ : σ → List (String × σ)) (cap : Nat) :
    Nat → Seen σ → List σ → List σ → Seen σ × Bool
  | 0, seen, _, _ => (seen, false)
  | _ + 1, seen, [], [] => (seen, true)
  | fuel + 1, seen, [], next@(_ :: _) => loop succ cap fuel seen next.reverse []
  | fuel + 1, seen, x :: xs, next =>
    let r := expand cap x (depthOf seen x) (succ x) seen next
    if r.2.2 then loop succ cap fuel r.1 xs r.2.1 else (r.1, false)

/-- **The exploration** from `x0`, at most `cap` states. -/
def explore (succ : σ → List (String × σ)) (cap : Nat) (x0 : σ) : Seen σ × Bool :=
  loop succ cap (2 * cap + 2) ((∅ : Seen σ).insert x0 ⟨0, none⟩) [x0] []

/-- The labels of the recorded path from the root to `z` (parent pointers, at most `fuel`). -/
def traceTo (seen : Seen σ) : Nat → σ → List String → List String
  | 0, _, acc => acc
  | fuel + 1, z, acc =>
    match seen[z]? with
    | some ⟨_, some (p, l)⟩ => traceTo seen fuel p (l :: acc)
    | _ => acc

/-! ## The invariant -/

variable [LawfulBEq σ]

/-- Every discovered state is reachable, the queue holds discovered states, and a discovered
state not waiting in the queue has every successor discovered. -/
structure Inv (succ : σ → List (String × σ)) (x0 : σ) (seen : Seen σ) (q : List σ) : Prop where
  root   : x0 ∈ seen
  reach  : ∀ z, z ∈ seen → Reach succ x0 z
  queue  : ∀ z ∈ q, z ∈ seen
  closed : ∀ z, z ∈ seen → z ∈ q ∨ ∀ y ∈ (succ z).map Prod.snd, y ∈ seen

theorem mem_insert_iff {seen : Seen σ} {y z : σ} {v : Info σ} :
    z ∈ seen.insert y v ↔ z = y ∨ z ∈ seen := by
  rw [Std.HashMap.mem_insert, beq_iff_eq]
  exact or_congr_left eq_comm

theorem expand_spec (succ : σ → List (String × σ)) (cap : Nat) (x0 x : σ) (dx : Nat)
    (hx : Reach succ x0 x) :
    ∀ (ys : List (String × σ)) (seen : Seen σ) (next : List σ),
      (∀ e ∈ ys, e.2 ∈ (succ x).map Prod.snd) → (∀ z, z ∈ seen → Reach succ x0 z) →
      let r := expand cap x dx ys seen next
      (∀ z, z ∈ seen → z ∈ r.1) ∧ (∀ z ∈ next, z ∈ r.2.1) ∧
      (r.2.2 = true → ∀ e ∈ ys, e.2 ∈ r.1) ∧
      (∀ z, z ∈ r.1 → Reach succ x0 z) ∧ (∀ z, z ∈ r.1 → z ∈ seen ∨ z ∈ r.2.1) ∧
      (∀ z ∈ r.2.1, z ∈ next ∨ z ∈ r.1)
  | [], seen, next, _, hr => by
    simp only [expand]
    exact ⟨fun _ h => h, fun _ h => h, fun _ e h => absurd h List.not_mem_nil, hr,
      fun _ h => Or.inl h, fun _ h => Or.inl h⟩
  | (l, y) :: ys, seen, next, hys, hr => by
    have hys' : ∀ e ∈ ys, e.2 ∈ (succ x).map Prod.snd := fun e he => hys e (List.mem_cons_of_mem _ he)
    have hy : y ∈ (succ x).map Prod.snd := hys (l, y) List.mem_cons_self
    simp only [expand]
    split
    · rename_i hc
      have hmem : y ∈ seen := Std.HashMap.mem_iff_contains.mpr hc
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := expand_spec succ cap x0 x dx hx ys seen next hys' hr
      refine ⟨h1, h2, fun hok e he => ?_, h4, h5, h6⟩
      rcases List.mem_cons.mp he with rfl | he
      · exact h1 _ hmem
      · exact h3 hok e he
    · rename_i hc
      split
      · exact ⟨fun _ h => h, fun _ h => h, fun h => absurd h Bool.false_ne_true, hr,
          fun _ h => Or.inl h, fun _ h => Or.inl h⟩
      · have hr' : ∀ z, z ∈ seen.insert y ⟨dx + 1, some (x, l)⟩ → Reach succ x0 z := by
          intro z hz
          rcases mem_insert_iff.mp hz with rfl | hz
          · exact Relation.ReflTransGen.tail hx hy
          · exact hr z hz
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := expand_spec succ cap x0 x dx hx ys _ _ hys' hr'
        refine ⟨fun z hz => h1 z (mem_insert_iff.mpr (Or.inr hz)),
          fun z hz => h2 z (List.mem_cons_of_mem _ hz), fun hok e he => ?_, h4, fun z hz => ?_,
          fun z hz => ?_⟩
        · rcases List.mem_cons.mp he with rfl | he
          · exact h1 _ (mem_insert_iff.mpr (Or.inl rfl))
          · exact h3 hok e he
        · rcases h5 z hz with hz' | hz'
          · rcases mem_insert_iff.mp hz' with rfl | hz'
            · exact Or.inr (h2 _ List.mem_cons_self)
            · exact Or.inl hz'
          · exact Or.inr hz'
        · rcases h6 z hz with hz' | hz'
          · rcases List.mem_cons.mp hz' with rfl | hz'
            · exact Or.inr (h1 _ (mem_insert_iff.mpr (Or.inl rfl)))
            · exact Or.inl hz'
          · exact Or.inr hz'

theorem inv_expand {succ : σ → List (String × σ)} {cap : Nat} {x0 x : σ} {dx : Nat}
    {seen : Seen σ} {xs next : List σ}
    (hinv : Inv succ x0 seen (x :: xs ++ next)) :
    (∀ z, z ∈ (expand cap x dx (succ x) seen next).1 → Reach succ x0 z) ∧
    ((expand cap x dx (succ x) seen next).2.2 = true →
      Inv succ x0 (expand cap x dx (succ x) seen next).1
        (xs ++ (expand cap x dx (succ x) seen next).2.1)) := by
  have hx : Reach succ x0 x := hinv.reach x (hinv.queue x List.mem_cons_self)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
    expand_spec succ cap x0 x dx hx (succ x) seen next
      (fun e he => List.mem_map.mpr ⟨e, he, rfl⟩) hinv.reach
  refine ⟨h4, fun hok => ⟨h1 _ hinv.root, h4, fun z hz => ?_, fun z hz => ?_⟩⟩
  · rcases List.mem_append.mp hz with hz | hz
    · exact h1 z (hinv.queue z (List.mem_cons_of_mem _ (List.mem_append_left _ hz)))
    · rcases h6 z hz with hz' | hz'
      · exact h1 z (hinv.queue z (List.mem_append_right _ hz'))
      · exact hz'
  · rcases h5 z hz with hz' | hz'
    · rcases hinv.closed z hz' with hq | hs
      · rcases List.mem_cons.mp hq with rfl | hq
        · right
          intro y hy
          obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
          exact h3 hok e he
        · rcases List.mem_append.mp hq with hq | hq
          · exact Or.inl (List.mem_append_left _ hq)
          · exact Or.inl (List.mem_append_right _ (h2 z hq))
      · exact Or.inr fun y hy => h1 y (hs y hy)
    · exact Or.inl (List.mem_append_right _ hz')

theorem loop_spec (succ : σ → List (String × σ)) (cap : Nat) (x0 : σ) :
    ∀ fuel (seen : Seen σ) (fr next : List σ), Inv succ x0 seen (fr ++ next) →
      (∀ z, z ∈ (loop succ cap fuel seen fr next).1 → Reach succ x0 z) ∧
      ((loop succ cap fuel seen fr next).2 = true →
        x0 ∈ (loop succ cap fuel seen fr next).1 ∧
        ∀ z, z ∈ (loop succ cap fuel seen fr next).1 →
          ∀ y ∈ (succ z).map Prod.snd, y ∈ (loop succ cap fuel seen fr next).1)
  | 0, seen, fr, next, hinv => by
    simp only [loop]
    exact ⟨hinv.reach, fun h => absurd h Bool.false_ne_true⟩
  | _ + 1, seen, [], [], hinv => by
    simp only [loop]
    refine ⟨hinv.reach, fun _ => ⟨hinv.root, fun z hz y hy => ?_⟩⟩
    rcases hinv.closed z hz with h | h
    · exact absurd h List.not_mem_nil
    · exact h y hy
  | fuel + 1, seen, [], n :: ns, hinv => by
    simp only [loop]
    apply loop_spec succ cap x0 fuel
    refine ⟨hinv.root, hinv.reach, fun z hz => hinv.queue z ?_, fun z hz => ?_⟩
    · simp only [List.nil_append, List.append_nil, List.mem_reverse] at hz ⊢
      exact hz
    · rcases hinv.closed z hz with h | h
      · left
        simp only [List.nil_append, List.append_nil, List.mem_reverse] at h ⊢
        exact h
      · exact Or.inr h
  | fuel + 1, seen, x :: xs, next, hinv => by
    simp only [loop]
    obtain ⟨hr, hi⟩ := inv_expand (cap := cap) (dx := depthOf seen x) hinv
    split
    · rename_i hok
      exact loop_spec succ cap x0 fuel _ xs _ (hi hok)
    · exact ⟨hr, fun h => absurd h Bool.false_ne_true⟩

theorem inv_init (succ : σ → List (String × σ)) (x0 : σ) :
    Inv succ x0 ((∅ : Seen σ).insert x0 ⟨0, none⟩) ([x0] ++ []) := by
  have hm : ∀ z, z ∈ (∅ : Seen σ).insert x0 ⟨0, none⟩ ↔ z = x0 := fun z => by
    rw [mem_insert_iff]
    simp
  refine ⟨(hm x0).mpr rfl, fun z hz => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · rw [(hm z).mp hz]; exact Relation.ReflTransGen.refl
  · simp only [List.append_nil, List.mem_singleton] at hz
    exact (hm z).mpr hz
  · left; simpa using (hm z).mp hz

/-- Every discovered state is reachable, whether or not the search completed. -/
theorem explore_reach {succ : σ → List (String × σ)} {cap : Nat} {x0 : σ} {z : σ}
    (hz : z ∈ (explore succ cap x0).1) : Reach succ x0 z :=
  (loop_spec succ cap x0 _ _ _ _ (inv_init succ x0)).1 z hz

/-- **A completed search discovers exactly the reachable states.** -/
theorem explore_complete_iff {succ : σ → List (String × σ)} {cap : Nat} {x0 : σ}
    (h : (explore succ cap x0).2 = true) (z : σ) :
    z ∈ (explore succ cap x0).1 ↔ Reach succ x0 z := by
  obtain ⟨hr, hc⟩ := loop_spec succ cap x0 _ _ _ _ (inv_init succ x0)
  obtain ⟨hroot, hcl⟩ := hc h
  refine ⟨hr z, fun hz => ?_⟩
  induction hz with
  | refl => exact hroot
  | tail _ hs ih => exact hcl _ ih _ hs

end Libpetri.Reference.Search
