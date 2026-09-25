import Libpetri.Soundness
import Mathlib.Logic.Relation

/-!
# The bounded enumeration route decides exactly ([VER-017])

Model of the enumeration route: `StateClassGraph::build_with_options`
(`rust/libpetri-verification/src/state_class_graph.rs:102`), which the route reaches through
`StateClassGraph::build` with no environment places, and the verdict that
`decide_over_state_space` (`rust/libpetri-verification/src/scg_verifier.rs:114`) reads off the
built graph. `verify_via_state_class_graph` (`scg_verifier.rs:94`) is the two in sequence; with
a `StateSpaceCache` attached, `verify_net` calls `decide_over_state_space` directly on a graph
the cache built or already held.

The exploration is a breadth-first worklist (`state_class_graph.rs:128-194`):
* pop the front class, and stop with `complete = false` if the budget is reached
  (`classes.len() >= max_classes`, `state_class_graph.rs:129-132`);
* otherwise, for every successor in order, look its key up. A new successor is appended to
  both the class list and the queue (`state_class_graph.rs:164-174`); a known one only gets an
  edge.
* The graph is complete when the queue runs dry.
`run` is that loop with the class list and queue as lists and dedup by equality (the key).
Lean needs termination, so there is a `fuel` argument, and running out of fuel counts as
truncation. `decide_over_state_space` reports `Truncated` unless the graph is complete.
Otherwise the verdict is `Violated` iff some discovered class satisfies the property's bad
predicate (`decide_over_classes`, the first class where it holds), where a class is quiescent
iff it has no successor (`is_quiescent`, `scg_verifier.rs:84-86`).

Results:
* `run_complete_iff_reach` (the core): if the loop reports `complete`, a state is among the
  discovered classes **iff** it is reachable from the initial one. The loop invariant: every
  class is reachable, and every class not waiting in the queue has all its successors
  discovered.
* `decided_exact`: a complete run's `Proven` (no discovered class is bad) holds **iff** no
  reachable state is bad, and a `Violated` class is really reachable. For the abstract loop the
  verdict is sound and complete for the predicate it reads, as the spec's "What the verdict
  means" demands.
* `succNet_iff_step`, `quiescent_iff_dead`, `net_enumeration_exact`: instantiated with the
  flat net's successor function over abstract markings, the discovered classes are exactly the
  `ReachA`-reachable markings (the encoders' untimed reachable set), and a quiescent class is
  exactly a dead marking. So deadlock freedom read off a closed graph is deadlock freedom of
  `ReachA`.

The step from these results to the shipped route rests on two premises that are assumed, not
proven:
* **Successors.** On an untimed net a class is modelled by its marking and its successors by
  the CHC fire relation `fireA`, one per enabled flat transition (XOR branch). The Rust
  `compute_successor` (`state_class_graph.rs:429`) works on state classes with (trivial) firing
  domains, iterates the class's enabled transitions in canonical clock order rather than net
  order, and drops a successor whose domain is empty (`state_class_graph.rs:158-160`). That it
  yields exactly the `fireA` successors, as a set, on an immediate-only net is the premise of
  VER-017 condition 3. Order does not matter: every result above is about membership.
* **Class identity.** The Rust dedups classes by `StateClass::canonical_key`, the marking key
  joined with the DBM's `zone_key`. The model takes it to be equality of markings, which holds
  when the zone of an untimed class is determined by its marking.

Also not modelled:
* Environment injection. The Rust build threads `env_set` into `compute_successor`
  (`state_class_graph.rs:112`, `state_class_graph.rs:153`), but the Lean successor step
  `succNet` covers only net transitions. The route itself runs only when no environment places
  are registered (VER-017 condition 2, checked in `verify_net`).
* The state-space cache: that a graph reused under an equal net and marking fingerprint is the
  graph a fresh build would return.
* The counterexample path reconstruction (`counterexample_path`); only reachability of the
  violating class is proven.
* That the route closes on every small enough state space (budget and fuel large enough). Only
  what a closed run decides is proven.
-/

namespace Libpetri.Novel.Enumeration

open Libpetri

variable {σ : Type} [DecidableEq σ]

/-- Reachability along a successor function. -/
def Reach (succ : σ → List σ) (x0 : σ) : σ → Prop :=
  Relation.ReflTransGen (fun a b => b ∈ succ a) x0

/-- Expand one class: every successor not yet discovered is appended to the class list and
to the queue, in successor order (`state_class_graph.rs:136-193`). -/
def expand (cls q : List σ) : List σ → List σ × List σ
  | [] => (cls, q)
  | y :: ys => if y ∈ cls then expand cls q ys else expand (cls ++ [y]) (q ++ [y]) ys

/-- The worklist loop. Returns the class list and `complete`. -/
def run (succ : σ → List σ) (maxClasses : Nat) : Nat → List σ → List σ → List σ × Bool
  | 0, cls, _ => (cls, false)
  | _ + 1, cls, [] => (cls, true)
  | fuel + 1, cls, x :: q =>
    if maxClasses ≤ cls.length then (cls, false)
    else
      let r := expand cls q (succ x)
      run succ maxClasses fuel r.1 r.2

/-- `build`: start from the initial class alone. -/
def build (succ : σ → List σ) (maxClasses fuel : Nat) (x0 : σ) : List σ × Bool :=
  run succ maxClasses fuel [x0] [x0]

/-! ## The loop invariant -/

/-- Every class is reachable, the queue is made of classes, and every class not waiting in
the queue has all its successors discovered. -/
structure Inv (succ : σ → List σ) (x0 : σ) (cls q : List σ) : Prop where
  reach : ∀ z ∈ cls, Reach succ x0 z
  queue_sub : ∀ z ∈ q, z ∈ cls
  closed : ∀ z ∈ cls, z ∈ q ∨ ∀ y ∈ succ z, y ∈ cls

theorem expand_spec (succ : σ → List σ) (x0 x : σ) (hx : Reach succ x0 x) :
    ∀ (ys : List σ) (cls q : List σ), (∀ y ∈ ys, y ∈ succ x) →
      (∀ z ∈ cls, Reach succ x0 z) →
      (∀ z ∈ cls, z ∈ (expand cls q ys).1) ∧
      (∀ z ∈ q, z ∈ (expand cls q ys).2) ∧
      (∀ y ∈ ys, y ∈ (expand cls q ys).1) ∧
      (∀ z ∈ (expand cls q ys).1, Reach succ x0 z) ∧
      (∀ z ∈ (expand cls q ys).1, z ∈ cls ∨ z ∈ (expand cls q ys).2) ∧
      (∀ z ∈ (expand cls q ys).2, z ∈ q ∨ z ∈ (expand cls q ys).1)
  | [], cls, q, _, hr => by
    refine ⟨fun z h => h, fun z h => h, fun y h => absurd h List.not_mem_nil, hr,
      fun z h => Or.inl h, fun z h => Or.inl h⟩
  | y :: ys, cls, q, hys, hr => by
    have hys' : ∀ y' ∈ ys, y' ∈ succ x := fun y' h => hys y' (List.mem_cons_of_mem y h)
    have hy : y ∈ succ x := hys y List.mem_cons_self
    by_cases hmem : y ∈ cls
    · simp only [expand, if_pos hmem]
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := expand_spec succ x0 x hx ys cls q hys' hr
      refine ⟨h1, h2, fun y' h => ?_, h4, h5, h6⟩
      rcases List.mem_cons.mp h with rfl | h
      · exact h1 _ hmem
      · exact h3 y' h
    · simp only [expand, if_neg hmem]
      have hr' : ∀ z ∈ cls ++ [y], Reach succ x0 z := fun z h => by
        rcases List.mem_append.mp h with h | h
        · exact hr z h
        · rw [List.mem_singleton.mp h]
          exact Relation.ReflTransGen.tail hx hy
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
        expand_spec succ x0 x hx ys (cls ++ [y]) (q ++ [y]) hys' hr'
      refine ⟨fun z h => h1 z (List.mem_append_left _ h),
        fun z h => h2 z (List.mem_append_left _ h), fun y' h => ?_, h4, fun z h => ?_,
        fun z h => ?_⟩
      · rcases List.mem_cons.mp h with rfl | h
        · exact h1 _ (List.mem_append_right _ (List.mem_singleton_self _))
        · exact h3 y' h
      · rcases h5 z h with h' | h'
        · rcases List.mem_append.mp h' with h'' | h''
          · exact Or.inl h''
          · rw [List.mem_singleton.mp h'']
            exact Or.inr (h2 _ (List.mem_append_right _ (List.mem_singleton_self _)))
        · exact Or.inr h'
      · rcases h6 z h with h' | h'
        · rcases List.mem_append.mp h' with h'' | h''
          · exact Or.inl h''
          · rw [List.mem_singleton.mp h'']
            exact Or.inr (h1 _ (List.mem_append_right _ (List.mem_singleton_self _)))
        · exact Or.inr h'

theorem inv_expand {succ : σ → List σ} {x0 x : σ} {cls q : List σ}
    (hinv : Inv succ x0 cls (x :: q)) :
    Inv succ x0 (expand cls q (succ x)).1 (expand cls q (succ x)).2 := by
  have hx : Reach succ x0 x := hinv.reach x (hinv.queue_sub x List.mem_cons_self)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
    expand_spec succ x0 x hx (succ x) cls q (fun _ h => h) hinv.reach
  refine ⟨h4, fun z h => ?_, fun z h => ?_⟩
  · rcases h6 z h with h' | h'
    · exact h1 z (hinv.queue_sub z (List.mem_cons_of_mem x h'))
    · exact h'
  · rcases h5 z h with h' | h'
    · rcases hinv.closed z h' with hq | hs
      · rcases List.mem_cons.mp hq with rfl | hq
        · exact Or.inr h3
        · exact Or.inl (h2 z hq)
      · exact Or.inr fun y hy => h1 y (hs y hy)
    · exact Or.inl h'

theorem run_inv (succ : σ → List σ) (maxClasses : Nat) (x0 : σ) :
    ∀ fuel (cls q : List σ), Inv succ x0 cls q → (run succ maxClasses fuel cls q).2 = true →
      (∀ z ∈ (run succ maxClasses fuel cls q).1, Reach succ x0 z) ∧
      (∀ z ∈ cls, z ∈ (run succ maxClasses fuel cls q).1) ∧
      ∀ z ∈ (run succ maxClasses fuel cls q).1, ∀ y ∈ succ z,
        y ∈ (run succ maxClasses fuel cls q).1
  | 0, _, _, _, h => by simp [run] at h
  | _ + 1, cls, [], hinv, _ => by
    refine ⟨hinv.reach, fun z h => h, fun z hz y hy => ?_⟩
    rcases hinv.closed z hz with h | h
    · exact absurd h List.not_mem_nil
    · exact h y hy
  | fuel + 1, cls, x :: q, hinv, h => by
    simp only [run] at h ⊢
    split at h
    · simp at h
    · rename_i hlt
      rw [if_neg hlt]
      obtain ⟨hr, hsub, hcl⟩ := run_inv succ maxClasses x0 fuel _ _ (inv_expand hinv) h
      have hx : Reach succ x0 x := hinv.reach x (hinv.queue_sub x List.mem_cons_self)
      have h1 := (expand_spec succ x0 x hx (succ x) cls q (fun _ h => h) hinv.reach).1
      exact ⟨hr, fun z hz => hsub z (h1 z hz), hcl⟩

/-- **A closed exploration discovers exactly the reachable set.** -/
theorem run_complete_iff_reach {succ : σ → List σ} {maxClasses fuel : Nat} {x0 : σ}
    (h : (build succ maxClasses fuel x0).2 = true) (y : σ) :
    y ∈ (build succ maxClasses fuel x0).1 ↔ Reach succ x0 y := by
  have hinv : Inv succ x0 [x0] [x0] :=
    ⟨fun z hz => by rw [List.mem_singleton.mp hz]; exact Relation.ReflTransGen.refl,
      fun z hz => hz, fun z hz => Or.inl hz⟩
  obtain ⟨hr, hsub, hcl⟩ := run_inv succ maxClasses x0 fuel [x0] [x0] hinv h
  refine ⟨hr y, fun hy => ?_⟩
  induction hy with
  | refl => exact hsub x0 (List.mem_singleton_self _)
  | tail _ hs ih => exact hcl _ ih _ hs

/-! ## The verdict -/

/-- The route's verdict on a closed graph: `true` = `Proven` (no discovered class is bad). -/
def proven (bad : σ → Bool) (cls : List σ) : Bool :=
  cls.all fun x => !bad x

/-- **The decided verdict is exact.** On a closed graph, `Proven` holds iff no reachable state
is bad, and every class the route reports as violating is reachable. -/
theorem decided_exact {succ : σ → List σ} {maxClasses fuel : Nat} {x0 : σ} (bad : σ → Bool)
    (h : (build succ maxClasses fuel x0).2 = true) :
    (proven bad (build succ maxClasses fuel x0).1 = true ↔
      ∀ y, Reach succ x0 y → bad y = false) ∧
    ∀ x ∈ (build succ maxClasses fuel x0).1, bad x = true → Reach succ x0 x := by
  refine ⟨?_, fun x hx _ => (run_complete_iff_reach h x).mp hx⟩
  unfold proven
  rw [List.all_eq_true]
  constructor
  · intro hall y hy
    have := hall y ((run_complete_iff_reach h y).mpr hy)
    simpa using this
  · intro hall x hx
    have := hall x ((run_complete_iff_reach h x).mp hx)
    simp [this]

/-! ## Instantiated with a flat net -/

/-- The successors of an abstract marking: one per enabled flat transition, in net order. -/
def succNet (net : FlatNet) (a : AMarking) : List AMarking :=
  net.filterMap fun ft => if enabledA a ft.1 = true then some (fireA a ft.1 ft.2) else none

theorem succNet_iff_step (net : FlatNet) (a b : AMarking) :
    b ∈ succNet net a ↔ StepARel net a b := by
  unfold succNet StepARel
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨ft, hmem, hft⟩
    split at hft
    · rename_i hen
      exact ⟨ft, hmem, hen, (Option.some.inj hft).symm⟩
    · exact absurd hft (by simp)
  · rintro ⟨ft, hmem, hen, rfl⟩
    exact ⟨ft, hmem, by rw [if_pos hen]⟩

theorem reach_succNet_iff (net : FlatNet) (a0 a : AMarking) :
    Reach (succNet net) a0 a ↔ ReachA net a0 a := by
  unfold Reach ReachA
  have : (fun x y => y ∈ succNet net x) = StepARel net := by
    funext x y
    exact propext (succNet_iff_step net x y)
  rw [this]

/-- A class is quiescent (no successor) iff its marking is dead. -/
theorem quiescent_iff_dead (net : FlatNet) (a : AMarking) :
    succNet net a = [] ↔ ∀ ft ∈ net, enabledA a ft.1 = false := by
  unfold succNet
  rw [List.filterMap_eq_nil_iff]
  constructor
  · intro h ft hmem
    have := h ft hmem
    cases hen : enabledA a ft.1 with
    | false => rfl
    | true => simp [hen] at this
  · intro h ft hmem
    simp [h ft hmem]

/-- **[VER-017] on a flat net.** If the enumeration of an untimed flat net closes, its classes
are exactly the `ReachA`-reachable markings. Reading a bad predicate off them decides it exactly
for `ReachA`, and in particular the graph has a quiescent class iff some reachable marking is
dead. -/
theorem net_enumeration_exact {net : FlatNet} {maxClasses fuel : Nat} {a0 : AMarking}
    [DecidableEq AMarking]
    (h : (build (succNet net) maxClasses fuel a0).2 = true) (bad : AMarking → Bool) :
    (∀ a, a ∈ (build (succNet net) maxClasses fuel a0).1 ↔ ReachA net a0 a) ∧
    (proven bad (build (succNet net) maxClasses fuel a0).1 = true ↔
      ∀ a, ReachA net a0 a → bad a = false) ∧
    ((∃ a ∈ (build (succNet net) maxClasses fuel a0).1, succNet net a = []) ↔
      ∃ a, ReachA net a0 a ∧ ∀ ft ∈ net, enabledA a ft.1 = false) := by
  have hmem : ∀ a, a ∈ (build (succNet net) maxClasses fuel a0).1 ↔ ReachA net a0 a :=
    fun a => (run_complete_iff_reach h a).trans (reach_succNet_iff net a0 a)
  refine ⟨hmem, ?_, ?_⟩
  · rw [(decided_exact bad h).1]
    exact forall_congr' fun a => by rw [reach_succNet_iff]
  · constructor
    · rintro ⟨a, ha, hq⟩
      exact ⟨a, (hmem a).mp ha, (quiescent_iff_dead net a).mp hq⟩
    · rintro ⟨a, ha, hd⟩
      exact ⟨a, (hmem a).mpr ha, (quiescent_iff_dead net a).mpr hd⟩

end Libpetri.Novel.Enumeration
