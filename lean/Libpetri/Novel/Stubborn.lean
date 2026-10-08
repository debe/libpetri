import Libpetri.Novel.Enumeration
import Mathlib.Data.Finset.Card

/-!
# Stubborn-set reduction of the enumeration route ([VER-024])

Model of the deadlock-preserving partial-order reduction of [VER-024]
(`spec/07-verification.md`), which the enumeration route of [VER-017] applies to quiescence
properties: at each class it expands only the enabled rows of a **stubborn set**. The Rust is
`stubborn_sets.rs::StubbornSets` (footprints in `new`, the seed choice in `select`, D1 / D2 in
`closure` and `scapegoat`), applied by `state_class_graph.rs::build_core` through
`build_stubborn`; Java `org.libpetri.analysis.StubbornSets` and TypeScript
`verification/analysis/stubborn-sets` mirror it.

The model works on **rows** (`Transition × Deposit`, one outcome of one transition, the rows of
`Enumeration.succRows`). The implementation works on transitions, taking every outcome of a
transition together and adding all rows of a transition at once; a transition-level stubborn
set is a row-level one (row footprints are contained in the transition's, and enabledness is per
transition), so the row-level conditions here cover it.

* Footprints (`tests`, `writes`, `overwrites`, `increases`, `decreases`) and the dependency
  relation (`dependent`, `Dependent`, `dependent_iff`) as the spec's "Footprints" section.
* `indep_diamond`, `indep_preserves_enabled`: independent rows enabled together stay enabled
  after either fires and commute. On a place both write, independence rules out that it is an
  input or a reset of either, so both only add and truncated subtraction never bites.
* `IsStubborn`: the key row, (D1) and (D2). `outside_cannot_enable` (D2),
  `outside_cannot_disable` (D1), `commute_to_front`.
* `stubborn_preserves_dead`: for any `StubbornFamily` (a stubborn set per marking with an enabled
  row), every `ReachAD`-reachable dead marking is reachable by reduced steps (`StepRed`).
  `reduced_reach_sound`: every reduced-reachable marking is `ReachAD`-reachable.
  `reducedQuiescent_iff_dead`: no reduced successor iff dead.
* `reduced_enumeration_exact_quiescence`: the [VER-017] frame (`Enumeration.build`) run over
  `succReduced`; when it closes, its quiescent classes are exactly the reachable dead markings,
  so a predicate read off quiescent classes is decided exactly. `reduced_full_same_quiescent`:
  the reduced and the full closed graphs have the same quiescent classes.
  `reduced_prefix_quiescent_sound`: a quiescent class of a truncated reduced graph is a
  reachable dead marking (the [VER-017] prefix rule).
* The closure the route computes (`closure`, `req`, `Blocker`, `firstBlocker`): from an enabled
  seed, add the dependents of enabled members (D1) and the increasers or decreasers of the
  blocker of disabled members (D2) until nothing is added. `closure_closed`: `rows.length + 1`
  rounds reach a fixpoint. `closed_stubborn`: a fixpoint is stubborn. `closure_family`,
  `closure_enumeration_exact_quiescence`: any seed choice (the route's fewest-enabled-rows choice
  included) gives an exact reduced enumeration.

No well-formedness premise is needed: not `InputsDistinctPlaces` (the proofs only use that a
place outside a row's `writes` keeps its count, and that a place a row neither deposits into
nor consumes from cannot go down or up respectively), nor `GuardFreeConsumeAll` (that is a
premise of the concrete-to-abstract step, `ForwardDeposit.rows_reachability_simulated`, not of
anything here).

Out of scope, as in `Enumeration.lean`: class identity, timing, environment places, ν-joins and
drained forwards (the spec's conditions for the reduction to apply), and the counterexample path
(a reduced violation is a real path since reduced steps are steps, `stepRed_stepAD`).
-/

namespace Libpetri.Novel.Stubborn

open Libpetri ForwardDeposit Enumeration

/-- One row of the flat net: a transition with one of its outcomes. -/
abbrev Row := Transition × Deposit

/-! ## Footprints -/

/-- The places of `t`'s input specs. -/
def inPlaces (t : Transition) : List PlaceId := t.inputs.map (·.place)

/-- `tests(r)`: input, read and inhibitor places. -/
def tests (r : Row) : List PlaceId := inPlaces r.1 ++ r.1.reads ++ r.1.inhibitors

/-- `writes(r)`: input and reset places and every place the outcome deposits into. -/
def writes (r : Row) : List PlaceId := inPlaces r.1 ++ r.1.resets ++ r.2

/-- `overwrites(r)`: reset places and consume-all inputs. -/
def overwrites (r : Row) : List PlaceId :=
  r.1.resets ++ (inPlaces r.1).filter (fun p => consumeAllAt r.1 p)

/-- Two place lists share a place. -/
def meets (xs ys : List PlaceId) : Bool := xs.any (fun p => ys.contains p)

theorem meets_iff {xs ys : List PlaceId} : meets xs ys = true ↔ ∃ p, p ∈ xs ∧ p ∈ ys := by
  simp [meets]

/-- The dependency relation, as a decision procedure. -/
def dependent (r u : Row) : Bool :=
  meets (writes r) (tests u) || meets (writes u) (tests r) ||
    meets (overwrites r) (writes u) || meets (overwrites u) (writes r)

/-- `r` and `u` are dependent. -/
def Dependent (r u : Row) : Prop := dependent r u = true

theorem dependent_iff {r u : Row} : Dependent r u ↔
    (∃ p, p ∈ writes r ∧ p ∈ tests u) ∨ (∃ p, p ∈ writes u ∧ p ∈ tests r) ∨
    (∃ p, p ∈ overwrites r ∧ p ∈ writes u) ∨ (∃ p, p ∈ overwrites u ∧ p ∈ writes r) := by
  simp only [Dependent, dependent, Bool.or_eq_true, meets_iff, or_assoc]

/-- `u` can increase `p`: its outcome deposits into `p`. -/
def increases (u : Row) (p : PlaceId) : Bool := u.2.contains p

/-- `u` can decrease `p`: `p` is one of its input or reset places. -/
def decreases (u : Row) (p : PlaceId) : Bool := (inPlaces u.1).contains p || u.1.resets.contains p

/-! ## Firing outside a footprint -/

theorem specAt_none {t : Transition} {p : PlaceId} (h : p ∉ inPlaces t) : specAt t p = none := by
  unfold specAt
  rw [List.find?_eq_none]
  intro s hs hsp
  apply h
  simp only [beq_iff_eq] at hsp
  exact List.mem_map.mpr ⟨s, hs, hsp⟩

/-- A place outside `writes r` keeps its count. -/
theorem fire_unwritten {r : Row} {p : PlaceId} (h : p ∉ writes r) (a : AMarking) :
    fireAD a r.1 r.2 p = a p := by
  simp only [writes, List.mem_append, not_or] at h
  obtain ⟨⟨hin, hres⟩, hdep⟩ := h
  have hs := specAt_none hin
  simp [fireAD, consumeAllAt, pre, hs, hres, List.count_eq_zero_of_not_mem hdep]

/-- A place neither input nor reset of `r.1` only gains the deposit. -/
theorem fire_additive {r : Row} {p : PlaceId} (hin : p ∉ inPlaces r.1) (hres : p ∉ r.1.resets)
    (a : AMarking) : fireAD a r.1 r.2 p = a p + r.2.count p := by
  have hs := specAt_none hin
  simp [fireAD, consumeAllAt, pre, hs, hres]

/-- The count after firing at `p` depends only on the count before at `p`. -/
theorem fire_congr {x y : AMarking} {p : PlaceId} (h : x p = y p) (t : Transition) (d : Deposit) :
    fireAD x t d p = fireAD y t d p := by
  simp only [fireAD, h]

theorem all_congr_mem {α : Type} {l : List α} {f g : α → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons, h x List.mem_cons_self,
      ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

/-- Enablement reads only the tested places. -/
theorem enabled_congr {x y : AMarking} {r : Row} (h : ∀ p ∈ tests r, x p = y p) :
    enabledA x r.1 = enabledA y r.1 := by
  have hi : ∀ s ∈ r.1.inputs, x s.place = y s.place := fun s hs =>
    h _ (by simp only [tests, inPlaces, List.mem_append, List.mem_map]; exact Or.inl (Or.inl ⟨s, hs, rfl⟩))
  have hr : ∀ p ∈ r.1.reads, x p = y p := fun p hp =>
    h p (by simp only [tests, List.mem_append]; exact Or.inl (Or.inr hp))
  have hn : ∀ p ∈ r.1.inhibitors, x p = y p := fun p hp =>
    h p (by simp only [tests, List.mem_append]; exact Or.inr hp)
  unfold enabledA
  have e1 : (r.1.inputs.all fun s => decide (s.card.required ≤ x s.place)) =
      (r.1.inputs.all fun s => decide (s.card.required ≤ y s.place)) :=
    all_congr_mem (fun s hs => by rw [hi s hs])
  have e2 : (r.1.inhibitors.all fun p => x p == 0) = (r.1.inhibitors.all fun p => y p == 0) :=
    all_congr_mem (fun p hp => by rw [hn p hp])
  have e3 : (r.1.reads.all fun p => decide (1 ≤ x p)) = (r.1.reads.all fun p => decide (1 ≤ y p)) :=
    all_congr_mem (fun p hp => by rw [hr p hp])
  rw [e1, e2, e3]

/-! ## Independence: the diamond -/

theorem mem_tests_of_in {r : Row} {p : PlaceId} (h : p ∈ inPlaces r.1) : p ∈ tests r := by
  simp [tests, h]

theorem mem_overwrites_of_reset {r : Row} {p : PlaceId} (h : p ∈ r.1.resets) :
    p ∈ overwrites r := by
  simp [overwrites, h]

theorem dependent_symm {r u : Row} : Dependent r u ↔ Dependent u r := by
  rw [dependent_iff, dependent_iff]
  constructor <;> rintro (h | h | h | h)
  all_goals first
    | exact Or.inl h | exact Or.inr (Or.inl h)
    | exact Or.inr (Or.inr (Or.inl h)) | exact Or.inr (Or.inr (Or.inr h))

theorem indep_writes_tests {r u : Row} (h : ¬ Dependent r u) {p : PlaceId}
    (hw : p ∈ writes r) : p ∉ tests u := fun ht =>
  h (dependent_iff.mpr (Or.inl ⟨p, hw, ht⟩))

theorem indep_overwrites_writes {r u : Row} (h : ¬ Dependent r u) {p : PlaceId}
    (ho : p ∈ overwrites r) : p ∉ writes u := fun hw =>
  h (dependent_iff.mpr (Or.inr (Or.inr (Or.inl ⟨p, ho, hw⟩))))

/-- **Independence keeps enablement** ([VER-024] "Independent transitions enabled together stay
enabled after either fires"). Only `writes u ∩ tests r = ∅` is used, so `u` need not be
enabled: firing `u` leaves every place `r` tests untouched. -/
theorem indep_preserves_enabled {r u : Row} (hind : ¬ Dependent r u) {a : AMarking}
    (hr : enabledA a r.1 = true) : enabledA (fireAD a u.1 u.2) r.1 = true := by
  have hind' : ¬ Dependent u r := fun h => hind (dependent_symm.mp h)
  rw [enabled_congr (fun p hp => fire_unwritten (fun hw => indep_writes_tests hind' hw hp) a)]
  exact hr

/-- **The diamond.** Two independent rows enabled at `a` stay enabled after each other, and
firing them in either order reaches the same marking. On a place both write, independence rules
out that it is an input or a reset of either (`writes ∩ tests = ∅` and
`overwrites ∩ writes = ∅`), so both only add their deposits and truncated subtraction never
bites. -/
theorem indep_diamond {r u : Row} (hind : ¬ Dependent r u) {a : AMarking}
    (hr : enabledA a r.1 = true) (hu : enabledA a u.1 = true) :
    enabledA (fireAD a r.1 r.2) u.1 = true ∧ enabledA (fireAD a u.1 u.2) r.1 = true ∧
      fireAD (fireAD a r.1 r.2) u.1 u.2 = fireAD (fireAD a u.1 u.2) r.1 r.2 := by
  have hind' : ¬ Dependent u r := fun h => hind (dependent_symm.mp h)
  refine ⟨indep_preserves_enabled hind' hu, indep_preserves_enabled hind hr, ?_⟩
  funext p
  by_cases hwr : p ∈ writes r
  · by_cases hwu : p ∈ writes u
    · have hinr : p ∉ inPlaces r.1 := fun h => indep_writes_tests hind' hwu (mem_tests_of_in h)
      have hinu : p ∉ inPlaces u.1 := fun h => indep_writes_tests hind hwr (mem_tests_of_in h)
      have hresr : p ∉ r.1.resets := fun h =>
        indep_overwrites_writes hind (mem_overwrites_of_reset h) hwu
      have hresu : p ∉ u.1.resets := fun h =>
        indep_overwrites_writes hind' (mem_overwrites_of_reset h) hwr
      simp only [fire_additive hinu hresu, fire_additive hinr hresr]
      omega
    · rw [fire_unwritten hwu, fire_congr (fire_unwritten hwu a)]
  · rw [fire_unwritten hwr, fire_congr (fire_unwritten hwr a)]

/-! ## Firing sequences -/

/-- `PathAD rows σ a b`: firing the rows of `σ` in order, each in `rows` and enabled when it
fires, leads from `a` to `b`. -/
inductive PathAD (rows : List Row) : List Row → AMarking → AMarking → Prop where
  | nil (a : AMarking) : PathAD rows [] a a
  | cons {r : Row} {σ : List Row} {a b : AMarking} (hmem : r ∈ rows)
      (hen : enabledA a r.1 = true) (hrest : PathAD rows σ (fireAD a r.1 r.2) b) :
      PathAD rows (r :: σ) a b

theorem PathAD.append {rows : List Row} :
    ∀ {σ τ : List Row} {a b c : AMarking}, PathAD rows σ a b → PathAD rows τ b c →
      PathAD rows (σ ++ τ) a c
  | _, _, _, _, _, .nil _, h => h
  | _, _, _, _, _, .cons hm he hr, h => .cons hm he (PathAD.append hr h)

theorem PathAD.split {rows : List Row} :
    ∀ {σ τ : List Row} {a c : AMarking}, PathAD rows (σ ++ τ) a c →
      ∃ b, PathAD rows σ a b ∧ PathAD rows τ b c
  | [], _, a, _, h => ⟨a, .nil a, h⟩
  | _ :: _, _, _, _, .cons hm he hr =>
    let ⟨b, h1, h2⟩ := PathAD.split hr
    ⟨b, .cons hm he h1, h2⟩

theorem PathAD.reach {rows : List Row} {σ : List Row} {a b : AMarking}
    (h : PathAD rows σ a b) : ReachAD rows a b := by
  induction h with
  | nil => exact Relation.ReflTransGen.refl
  | cons hm he _ ih => exact Relation.ReflTransGen.head ⟨_, hm, he, rfl⟩ ih

theorem reachAD_path {rows : List Row} {a b : AMarking} (h : ReachAD rows a b) :
    ∃ σ, PathAD rows σ a b := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], .nil b⟩
  | head hs _ ih =>
    obtain ⟨σ, hσ⟩ := ih
    obtain ⟨r, hm, he, rfl⟩ := hs
    exact ⟨r :: σ, .cons hm he hσ⟩

/-- A row independent of every row of a firing sequence stays enabled along it. -/
theorem indep_path_preserves_enabled {rows : List Row} {r : Row} :
    ∀ {σ : List Row} {a b : AMarking}, PathAD rows σ a b → (∀ u ∈ σ, ¬ Dependent r u) →
      enabledA a r.1 = true → enabledA b r.1 = true
  | _, _, _, .nil _, _, h => h
  | _, _, _, .cons _ _ hrest, hind, h =>
    indep_path_preserves_enabled hrest (fun u hu => hind u (List.mem_cons_of_mem _ hu))
      (indep_preserves_enabled (hind _ List.mem_cons_self) h)

/-- **Commuting an independent row to the front of a sequence.** If `r` is enabled at `a` and
independent of every row of `σ`, then `r` then `σ` is a firing sequence from `a` to the marking
`σ` then `r` reaches. -/
theorem indep_path_commute {rows : List Row} {r : Row} :
    ∀ {σ : List Row} {a b : AMarking}, PathAD rows σ a b → (∀ u ∈ σ, ¬ Dependent r u) →
      enabledA a r.1 = true → PathAD rows σ (fireAD a r.1 r.2) (fireAD b r.1 r.2)
  | _, _, _, .nil _, _, _ => .nil _
  | _, a, _, .cons (r := u) hm he hrest, hind, h => by
    obtain ⟨hu', _, hcomm⟩ := indep_diamond (hind u List.mem_cons_self) h he
    refine .cons hm hu' ?_
    rw [hcomm]
    exact indep_path_commute hrest (fun v hv => hind v (List.mem_cons_of_mem _ hv))
      (indep_preserves_enabled (hind u List.mem_cons_self) h)

/-! ## Stubborn sets -/

/-- The (D2) reason a disabled row `r` gives at `a`: an input or read place with too few tokens
whose every increaser is in `S`, or a marked inhibitor place whose every decreaser is in `S`.
It implies `r` is disabled (`Witness.disabled`). -/
def Witness (rows S : List Row) (a : AMarking) (r : Row) : Prop :=
  (∃ s ∈ r.1.inputs, a s.place < s.card.required ∧
      ∀ u ∈ rows, increases u s.place = true → u ∈ S) ∨
  (∃ p ∈ r.1.reads, a p = 0 ∧ ∀ u ∈ rows, increases u p = true → u ∈ S) ∨
  (∃ p ∈ r.1.inhibitors, 0 < a p ∧ ∀ u ∈ rows, decreases u p = true → u ∈ S)

/-- **`S` is stubborn at `a`** with respect to `rows` ([VER-024] "The stubborn set at a class"):
a key row of `S` is enabled, every enabled row of `S` has all its dependents in `S` (D1), and
every disabled row of `S` has a (D2) witness. -/
structure IsStubborn (rows S : List Row) (a : AMarking) : Prop where
  key : ∃ r ∈ S, enabledA a r.1 = true
  d1 : ∀ r ∈ S, enabledA a r.1 = true → ∀ u ∈ rows, Dependent r u → u ∈ S
  d2 : ∀ r ∈ S, enabledA a r.1 = false → Witness rows S a r

theorem Witness.disabled {rows S : List Row} {a : AMarking} {r : Row}
    (h : Witness rows S a r) : enabledA a r.1 = false := by
  rw [Bool.eq_false_iff]
  intro hen
  simp only [enabledA, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at hen
  obtain ⟨⟨hin, hinh⟩, hrd⟩ := hen
  rcases h with ⟨s, hs, hlt, _⟩ | ⟨p, hp, h0, _⟩ | ⟨p, hp, hpos, _⟩
  · exact absurd (hin s hs) (Nat.not_le.mpr hlt)
  · have := hrd p hp
    omega
  · have := hinh p hp
    omega

/-- A row outside `S` keeps a (D2) witness: it cannot increase the place an input or read
witness waits on, nor decrease the place an inhibitor witness is blocked by. -/
theorem Witness.step {rows S : List Row} {a : AMarking} {r u : Row}
    (h : Witness rows S a r) (hu : u ∈ rows) (hout : u ∉ S) :
    Witness rows S (fireAD a u.1 u.2) r := by
  have noinc : ∀ p, (∀ v ∈ rows, increases v p = true → v ∈ S) → fireAD a u.1 u.2 p ≤ a p := by
    intro p hp
    have hc : u.2.count p = 0 :=
      List.count_eq_zero_of_not_mem fun hm => hout (hp u hu (by simp [increases, hm]))
    simp only [fireAD, hc]
    split <;> [omega; split <;> omega]
  rcases h with ⟨s, hs, hlt, hS⟩ | ⟨p, hp, h0, hS⟩ | ⟨p, hp, hpos, hS⟩
  · exact Or.inl ⟨s, hs, Nat.lt_of_le_of_lt (noinc _ hS) hlt, hS⟩
  · exact Or.inr (Or.inl ⟨p, hp, Nat.le_zero.mp (h0 ▸ noinc p hS), hS⟩)
  · refine Or.inr (Or.inr ⟨p, hp, ?_, hS⟩)
    have hnd : decreases u p = false := by
      rw [Bool.eq_false_iff]
      exact fun hd => hout (hS u hu hd)
    simp only [decreases, Bool.or_eq_false_iff] at hnd
    obtain ⟨hin, hres⟩ := hnd
    have hin' : p ∉ inPlaces u.1 := by simpa using hin
    have hres' : p ∉ u.1.resets := by simpa using hres
    rw [fire_additive hin' hres']
    omega

/-- **Rows outside a stubborn set cannot enable a disabled member** (from D2). -/
theorem outside_cannot_enable {rows S : List Row} {a : AMarking} (hS : IsStubborn rows S a)
    {r : Row} (hr : r ∈ S) (hdis : enabledA a r.1 = false) {σ : List Row} {b : AMarking}
    (hpath : PathAD rows σ a b) (hout : ∀ u ∈ σ, u ∉ S) : enabledA b r.1 = false := by
  have key : ∀ {σ : List Row} {a b : AMarking}, PathAD rows σ a b → (∀ u ∈ σ, u ∉ S) →
      Witness rows S a r → Witness rows S b r := by
    intro σ a b hp
    induction hp with
    | nil => exact fun _ h => h
    | cons hm _ _ ih =>
      exact fun ho hw => ih (fun u hu => ho u (List.mem_cons_of_mem _ hu))
        (hw.step hm (ho _ List.mem_cons_self))
  exact (key hpath hout (hS.d2 r hr hdis)).disabled

/-- **Rows outside a stubborn set cannot disable an enabled member** (from D1: each of them is
independent of it). -/
theorem outside_cannot_disable {rows S : List Row} {a : AMarking} (hS : IsStubborn rows S a)
    {r : Row} (hr : r ∈ S) (hen : enabledA a r.1 = true) {σ : List Row} {b : AMarking}
    (hpath : PathAD rows σ a b) (hσ : ∀ u ∈ σ, u ∈ rows) (hout : ∀ u ∈ σ, u ∉ S) :
    enabledA b r.1 = true :=
  indep_path_preserves_enabled hpath
    (fun u hu hd => hout u hu (hS.d1 r hr hen u (hσ u hu) hd)) hen

theorem PathAD.mem {rows : List Row} {σ : List Row} {a b : AMarking}
    (h : PathAD rows σ a b) : ∀ u ∈ σ, u ∈ rows := by
  induction h with
  | nil => exact fun _ h => absurd h List.not_mem_nil
  | cons hm _ _ ih =>
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact hm
    · exact ih u hu

/-- **The first stubborn row commutes to the front.** If `σ` avoids `S` and a member `r` of `S`
fires right after it, then `r` was already enabled at `a`, and `r` then `σ` reaches the same
marking. -/
theorem commute_to_front {rows S : List Row} {a : AMarking} (hS : IsStubborn rows S a)
    {r : Row} (hr : r ∈ S) {σ : List Row} {b : AMarking}
    (hpath : PathAD rows σ a b) (hout : ∀ u ∈ σ, u ∉ S) (henb : enabledA b r.1 = true) :
    enabledA a r.1 = true ∧ PathAD rows σ (fireAD a r.1 r.2) (fireAD b r.1 r.2) := by
  have hena : enabledA a r.1 = true := by
    cases h : enabledA a r.1 with
    | true => rfl
    | false => rw [outside_cannot_enable hS hr h hpath hout] at henb; exact absurd henb (by simp)
  exact ⟨hena, indep_path_commute hpath
    (fun u hu hd => hout u hu (hS.d1 r hr hena u (hpath.mem u hu) hd)) hena⟩

theorem PathAD.cons_inv {rows : List Row} {r : Row} {σ : List Row} {a b : AMarking}
    (h : PathAD rows (r :: σ) a b) :
    r ∈ rows ∧ enabledA a r.1 = true ∧ PathAD rows σ (fireAD a r.1 r.2) b := by
  cases h with
  | cons hm he hr => exact ⟨hm, he, hr⟩

/-! ## The reduced graph preserves every reachable dead marking -/

/-- A list either avoids `P` or splits at its first element satisfying `P`. -/
theorem first_split {α : Type} (P : α → Prop) :
    ∀ σ : List α, (∀ x ∈ σ, ¬ P x) ∨
      ∃ σ1 r σ2, σ = σ1 ++ r :: σ2 ∧ (∀ x ∈ σ1, ¬ P x) ∧ P r
  | [] => Or.inl fun _ h => absurd h List.not_mem_nil
  | x :: xs => by
    by_cases hx : P x
    · exact Or.inr ⟨[], x, xs, rfl, fun _ h => absurd h List.not_mem_nil, hx⟩
    · rcases first_split P xs with h | ⟨σ1, r, σ2, rfl, h1, hr⟩
      · exact Or.inl fun y hy => by
          rcases List.mem_cons.mp hy with rfl | hy
          · exact hx
          · exact h y hy
      · refine Or.inr ⟨x :: σ1, r, σ2, rfl, fun y hy => ?_, hr⟩
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hx
        · exact h1 y hy

/-- A marking where no row is enabled. -/
def Dead (rows : List Row) (a : AMarking) : Prop := ∀ r ∈ rows, enabledA a r.1 = false

/-- A choice of stubborn set per marking: always a subset of the rows, and stubborn at every
marking where some row is enabled. What it is at a dead marking does not matter. -/
structure StubbornFamily (rows : List Row) (stub : AMarking → List Row) : Prop where
  sub : ∀ a, ∀ r ∈ stub a, r ∈ rows
  stubborn : ∀ a, (∃ r ∈ rows, enabledA a r.1 = true) → IsStubborn rows (stub a) a

/-- The reduced step: fire an enabled row of the stubborn set chosen at the marking. -/
def StepRed (stub : AMarking → List Row) (a a' : AMarking) : Prop := StepAD (stub a) a a'

/-- **[VER-024]: every reachable dead marking is reachable in the reduced graph.** By strong
induction on the length of a firing sequence to the dead marking `d`: the sequence must fire a
row of the stubborn set (its key row would otherwise stay enabled, `outside_cannot_disable`),
and the first such row commutes to the front (`commute_to_front`), leaving a shorter sequence. -/
theorem stubborn_preserves_dead {rows : List Row} {stub : AMarking → List Row}
    (hF : StubbornFamily rows stub) {a0 d : AMarking} (hreach : ReachAD rows a0 d)
    (hd : Dead rows d) : Relation.ReflTransGen (StepRed stub) a0 d := by
  obtain ⟨σ, hσ⟩ := reachAD_path hreach
  suffices h : ∀ n (σ : List Row) a, σ.length = n → PathAD rows σ a d →
      Relation.ReflTransGen (StepRed stub) a d from h _ σ a0 rfl hσ
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro σ a hlen hp
    cases σ with
    | nil =>
      cases hp
      exact Relation.ReflTransGen.refl
    | cons r0 σ0 =>
      obtain ⟨hm0, he0, -⟩ := hp.cons_inv
      have hS := hF.stubborn a ⟨r0, hm0, he0⟩
      rcases first_split (· ∈ stub a) (r0 :: σ0) with hno | ⟨σ1, r, σ2, heq, hout, hr⟩
      · obtain ⟨k, hk, hken⟩ := hS.key
        have hkd := outside_cannot_disable hS hk hken hp hp.mem hno
        rw [hd k (hF.sub a k hk)] at hkd
        exact absurd hkd (by simp)
      · rw [heq] at hp hlen
        obtain ⟨b, h1, h2⟩ := hp.split
        obtain ⟨-, hrb, h3⟩ := h2.cons_inv
        obtain ⟨hra, hcomm⟩ := commute_to_front hS hr h1 hout hrb
        have hlt : (σ1 ++ σ2).length < n := by
          rw [← hlen]
          simp
        exact Relation.ReflTransGen.head ⟨r, hr, hra, rfl⟩
          (ih _ hlt (σ1 ++ σ2) _ rfl (hcomm.append h3))

/-- A reduced step is a step of the full net. -/
theorem stepRed_stepAD {rows : List Row} {stub : AMarking → List Row}
    (hF : StubbornFamily rows stub) {a b : AMarking} (h : StepRed stub a b) : StepAD rows a b := by
  obtain ⟨r, hr, he, rfl⟩ := h
  exact ⟨r, hF.sub a r hr, he, rfl⟩

/-- **Every marking the reduced graph reaches is reachable in the full net.** -/
theorem reduced_reach_sound {rows : List Row} {stub : AMarking → List Row}
    (hF : StubbornFamily rows stub) {a0 a : AMarking}
    (h : Relation.ReflTransGen (StepRed stub) a0 a) : ReachAD rows a0 a :=
  Relation.ReflTransGen.lift id (fun _ _ hs => stepRed_stepAD hF hs) a0 a h

/-- **A marking has no reduced successor iff it is dead** (the key row of the stubborn set is
an enabled row whenever any row is). -/
theorem reducedQuiescent_iff_dead {rows : List Row} {stub : AMarking → List Row}
    (hF : StubbornFamily rows stub) (a : AMarking) :
    (∀ b, ¬ StepRed stub a b) ↔ Dead rows a := by
  constructor
  · intro h r hr
    cases hen : enabledA a r.1 with
    | false => rfl
    | true =>
      obtain ⟨k, hk, hken⟩ := (hF.stubborn a ⟨r, hr, hen⟩).key
      exact absurd ⟨k, hk, hken, rfl⟩ (h _)
  · rintro hd b ⟨r, hr, he, -⟩
    rw [hd r (hF.sub a r hr)] at he
    exact absurd he (by simp)

/-! ## The reduced enumeration -/

/-- The reduced successors: one per enabled row of the stubborn set chosen at `a`, in its order.
It is `succRows` over that set. -/
def succReduced (stub : AMarking → List Row) (a : AMarking) : List AMarking :=
  succRows (stub a) a

theorem succReduced_iff_step (stub : AMarking → List Row) (a b : AMarking) :
    b ∈ succReduced stub a ↔ StepRed stub a b :=
  succRows_iff_step (stub a) a b

theorem reach_succReduced_iff (stub : AMarking → List Row) (a0 a : AMarking) :
    Reach (succReduced stub) a0 a ↔ Relation.ReflTransGen (StepRed stub) a0 a := by
  unfold Reach
  have : (fun x y => y ∈ succReduced stub x) = StepRed stub := by
    funext x y
    exact propext (succReduced_iff_step stub x y)
  rw [this]

/-- A reduced class is quiescent iff its marking is dead. -/
theorem succReduced_nil_iff_dead {rows : List Row} {stub : AMarking → List Row}
    (hF : StubbornFamily rows stub) (a : AMarking) : succReduced stub a = [] ↔ Dead rows a := by
  rw [← reducedQuiescent_iff_dead hF a]
  constructor
  · intro h b hb
    rw [← succReduced_iff_step, h] at hb
    exact absurd hb List.not_mem_nil
  · intro h
    rw [List.eq_nil_iff_forall_not_mem]
    exact fun b hb => h b ((succReduced_iff_step stub a b).mp hb)

/-- **Every class of a reduced run is reachable in the full net, closed or not**: the prefix
rule of [VER-017] carries over to the reduced graph. -/
theorem reduced_build_reach {rows : List Row} {stub : AMarking → List Row}
    (hF : StubbornFamily rows stub) [DecidableEq AMarking] {maxClasses fuel : Nat}
    {a0 a : AMarking} (h : a ∈ (build (succReduced stub) maxClasses fuel a0).1) :
    ReachAD rows a0 a :=
  reduced_reach_sound hF ((reach_succReduced_iff stub a0 a).mp (build_reach a h))

/-- **[VER-024] The reduced enumeration decides quiescence exactly.** If the reduced
exploration closes: every discovered class is reachable in the full net; its quiescent classes
are exactly the `ReachAD`-reachable dead markings; and so any predicate `bad` read off the
quiescent classes only (`deadlockFree` is `bad := true`) is `Proven` iff no reachable dead
marking is bad. -/
theorem reduced_enumeration_exact_quiescence {rows : List Row} {stub : AMarking → List Row}
    (hF : StubbornFamily rows stub) [DecidableEq AMarking] {maxClasses fuel : Nat}
    {a0 : AMarking} (h : (build (succReduced stub) maxClasses fuel a0).2 = true)
    (bad : AMarking → Bool) :
    (∀ a ∈ (build (succReduced stub) maxClasses fuel a0).1, ReachAD rows a0 a) ∧
    (∀ a, (a ∈ (build (succReduced stub) maxClasses fuel a0).1 ∧ succReduced stub a = []) ↔
      (ReachAD rows a0 a ∧ Dead rows a)) ∧
    (proven (fun a => (succReduced stub a).isEmpty && bad a)
        (build (succReduced stub) maxClasses fuel a0).1 = true ↔
      ∀ a, ReachAD rows a0 a → Dead rows a → bad a = false) := by
  have hsound : ∀ a ∈ (build (succReduced stub) maxClasses fuel a0).1, ReachAD rows a0 a :=
    fun a ha => reduced_build_reach hF ha
  have hq : ∀ a, (a ∈ (build (succReduced stub) maxClasses fuel a0).1 ∧ succReduced stub a = [])
      ↔ (ReachAD rows a0 a ∧ Dead rows a) := by
    intro a
    rw [succReduced_nil_iff_dead hF]
    constructor
    · exact fun ⟨ha, hd⟩ => ⟨hsound a ha, hd⟩
    · intro ⟨hr, hd⟩
      exact ⟨(run_complete_iff_reach h a).mpr
        ((reach_succReduced_iff stub a0 a).mpr (stubborn_preserves_dead hF hr hd)), hd⟩
  refine ⟨hsound, hq, ?_⟩
  unfold proven
  rw [List.all_eq_true]
  constructor
  · intro hall a hr hd
    have hmem := ((hq a).mpr ⟨hr, hd⟩)
    have := hall a hmem.1
    simpa [hmem.2] using this
  · intro hall a ha
    cases hn : succReduced stub a with
    | nil =>
      have hd := ((hq a).mp ⟨ha, hn⟩)
      simp [hall a hd.1 hd.2]
    | cons _ _ => simp [hn]

/-- **A quiescent class of any reduced run, closed or truncated, is a reachable dead marking.**
The prefix reading of [VER-017] stays sound for quiescence on the reduced graph, for a class the
build expanded. -/
theorem reduced_prefix_quiescent_sound {rows : List Row} {stub : AMarking → List Row}
    (hF : StubbornFamily rows stub) [DecidableEq AMarking] {maxClasses fuel : Nat}
    {a0 a : AMarking} (h : a ∈ (build (succReduced stub) maxClasses fuel a0).1)
    (hq : succReduced stub a = []) : ReachAD rows a0 a ∧ Dead rows a :=
  ⟨reduced_build_reach hF h, (succReduced_nil_iff_dead hF a).mp hq⟩

/-- **The reduced and the full graph agree on quiescent classes.** When both explorations close,
a marking is a quiescent class of the reduced graph iff it is a quiescent class of the full graph
of [VER-017], so every quiescence property gets the same verdict. -/
theorem reduced_full_same_quiescent {rows : List Row} {stub : AMarking → List Row}
    (hF : StubbornFamily rows stub) [DecidableEq AMarking] {maxR fuelR maxF fuelF : Nat}
    {a0 : AMarking} (hR : (build (succReduced stub) maxR fuelR a0).2 = true)
    (hFull : (build (succRows rows) maxF fuelF a0).2 = true) (a : AMarking) :
    (a ∈ (build (succReduced stub) maxR fuelR a0).1 ∧ succReduced stub a = []) ↔
      (a ∈ (build (succRows rows) maxF fuelF a0).1 ∧ succRows rows a = []) := by
  rw [(reduced_enumeration_exact_quiescence hF hR (fun _ => true)).2.1 a,
    (rows_enumeration_exact hFull (fun _ => true)).1 a, quiescentRows_iff_dead]
  rfl

/-! ## The closure the implementation computes -/

/-- The indices of the rows satisfying `f`, in row order. -/
def rowsWhere (rows : List Row) (f : Row → Bool) : List Nat :=
  (List.range rows.length).filter fun j => (rows[j]?.map f).getD false

theorem mem_rowsWhere {rows : List Row} {f : Row → Bool} {j : Nat} :
    j ∈ rowsWhere rows f ↔ ∃ u, rows[j]? = some u ∧ f u = true := by
  simp only [rowsWhere, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hj, h⟩
    refine ⟨rows[j], List.getElem?_eq_getElem hj, ?_⟩
    rw [List.getElem?_eq_getElem hj] at h
    simpa using h
  · rintro ⟨u, hu, hf⟩
    obtain ⟨hj, -⟩ := List.getElem?_eq_some_iff.mp hu
    exact ⟨hj, by rw [hu]; simpa using hf⟩

theorem lt_of_mem_rowsWhere {rows : List Row} {f : Row → Bool} {j : Nat}
    (h : j ∈ rowsWhere rows f) : j < rows.length := by
  obtain ⟨u, hu, -⟩ := mem_rowsWhere.mp h
  exact (List.getElem?_eq_some_iff.mp hu).1

/-- A blocker picks, for a disabled transition, one unsatisfied condition: `(true, p)` for an
input or read place `p` with too few tokens, `(false, p)` for a marked inhibitor place `p`. -/
abbrev Blocker := AMarking → Transition → Option (Bool × PlaceId)

/-- The blocker names an unsatisfied condition of every disabled transition. Any such choice
gives a stubborn set; the order the spec fixes (code-point order of place name, inputs and reads
before inhibitors) only makes the choice, and so the reduced graph, the same in every
implementation. -/
def BlockerSound (blk : Blocker) : Prop :=
  ∀ a t, enabledA a t = false → ∃ b p, blk a t = some (b, p) ∧
    (b = true → (∃ s ∈ t.inputs, s.place = p ∧ a p < s.card.required) ∨
      (p ∈ t.reads ∧ a p = 0)) ∧
    (b = false → p ∈ t.inhibitors ∧ 0 < a p)

/-- The first unsatisfied condition in list order: inputs, then reads, then inhibitors. With the
input and read places sorted by name beforehand this is the spec's order. -/
def firstBlocker : Blocker := fun a t =>
  match t.inputs.find? (fun s => decide (a s.place < s.card.required)) with
  | some s => some (true, s.place)
  | none =>
    match t.reads.find? (fun p => a p == 0) with
    | some p => some (true, p)
    | none => (t.inhibitors.find? (fun p => decide (0 < a p))).map fun p => (false, p)

theorem firstBlocker_sound : BlockerSound firstBlocker := by
  intro a t hdis
  unfold firstBlocker
  cases hi : t.inputs.find? (fun s => decide (a s.place < s.card.required)) with
  | some s =>
    have hlt := List.find?_some hi
    simp only [decide_eq_true_eq] at hlt
    exact ⟨true, s.place, rfl, fun _ => Or.inl ⟨s, List.mem_of_find?_eq_some hi, rfl, hlt⟩,
      fun h => absurd h (by simp)⟩
  | none =>
    cases hr : t.reads.find? (fun p => a p == 0) with
    | some p =>
      have h0 := List.find?_some hr
      simp only [beq_iff_eq] at h0
      exact ⟨true, p, rfl, fun _ => Or.inr ⟨List.mem_of_find?_eq_some hr, h0⟩,
        fun h => absurd h (by simp)⟩
    | none =>
      cases hn : t.inhibitors.find? (fun p => decide (0 < a p)) with
      | some p =>
        have hpos := List.find?_some hn
        simp only [decide_eq_true_eq] at hpos
        exact ⟨false, p, rfl, fun h => absurd h (by simp),
          fun _ => ⟨List.mem_of_find?_eq_some hn, hpos⟩⟩
      | none =>
        exfalso
        rw [List.find?_eq_none] at hi hr hn
        have : enabledA a t = true := by
          simp only [enabledA, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
            beq_iff_eq]
          refine ⟨⟨fun s hs => ?_, fun p hp => ?_⟩, fun p hp => ?_⟩
          · have := hi s hs
            simp only [decide_eq_true_eq] at this
            omega
          · have := hn p hp
            simp only [decide_eq_true_eq] at this
            omega
          · have := hr p hp
            simp only [beq_iff_eq] at this
            omega
        rw [this] at hdis
        exact absurd hdis (by simp)

section Closure

variable (rows : List Row) (blk : Blocker) (a : AMarking)

/-- What member `i` requires: (D1) every row dependent with it when it is enabled, (D2) every
row that can increase (or decrease) the place of its blocker when it is disabled. -/
def req (i : Nat) : List Nat :=
  match rows[i]? with
  | none => []
  | some r =>
    if enabledA a r.1 = true then rowsWhere rows (dependent r)
    else
      match blk a r.1 with
      | some (true, p) => rowsWhere rows fun u => increases u p
      | some (false, p) => rowsWhere rows fun u => decreases u p
      | none => []

/-- One round: add every required row not yet present. -/
def grow (idx : List Nat) : List Nat :=
  idx ++ (idx.flatMap (req rows blk a)).filter fun j => decide (j ∉ idx)

/-- Iterate rounds until nothing new is required, or the fuel runs out. -/
def closureIter : Nat → List Nat → List Nat
  | 0, idx => idx
  | n + 1, idx =>
    if (idx.flatMap (req rows blk a)).all (fun j => decide (j ∈ idx)) then idx
    else closureIter n (grow rows blk a idx)

/-- The closure `S(seed)` of [VER-024], as row indices. -/
def closure (seed fuel : Nat) : List Nat := closureIter rows blk a fuel [seed]

/-- A set of indices requiring nothing outside itself. -/
def Closed (idx : List Nat) : Prop := ∀ i ∈ idx, ∀ j ∈ req rows blk a i, j ∈ idx

/-- The rows an index set names. -/
def members (idx : List Nat) : List Row := idx.filterMap fun i => rows[i]?

end Closure

theorem mem_members {rows : List Row} {idx : List Nat} {u : Row} :
    u ∈ members rows idx ↔ ∃ i ∈ idx, rows[i]? = some u := by
  simp [members, List.mem_filterMap]

theorem lt_of_mem_req {rows : List Row} {blk : Blocker} {a : AMarking} {i j : Nat}
    (h : j ∈ req rows blk a i) : j < rows.length := by
  unfold req at h
  split at h
  · exact absurd h List.not_mem_nil
  · split at h
    · exact lt_of_mem_rowsWhere h
    · split at h
      · exact lt_of_mem_rowsWhere h
      · exact lt_of_mem_rowsWhere h
      · exact absurd h List.not_mem_nil

theorem closureIter_sup {rows : List Row} {blk : Blocker} {a : AMarking} :
    ∀ (n : Nat) (idx : List Nat), ∀ i ∈ idx, i ∈ closureIter rows blk a n idx
  | 0, _, _, h => h
  | n + 1, idx, i, h => by
    simp only [closureIter]
    split
    · exact h
    · exact closureIter_sup n _ i (List.mem_append_left _ h)

/-- Each round that is not a fixpoint adds a new index below `rows.length`, so the number of
missing indices is a measure: with more fuel than missing indices, the iteration stops at a
closed set. -/
theorem closureIter_closed {rows : List Row} {blk : Blocker} {a : AMarking} :
    ∀ (n : Nat) (idx : List Nat), (∀ i ∈ idx, i < rows.length) →
      (Finset.range rows.length \ idx.toFinset).card < n →
      Closed rows blk a (closureIter rows blk a n idx)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, idx, hlt, hcard => by
    simp only [closureIter]
    split
    · rename_i hall
      rw [List.all_eq_true] at hall
      intro i hi j hj
      have := hall j (List.mem_flatMap.mpr ⟨i, hi, hj⟩)
      simpa using this
    · rename_i hall
      simp only [List.all_eq_true, not_forall, decide_eq_true_eq] at hall
      obtain ⟨j, hj, hjn⟩ := hall
      obtain ⟨i, hi, hji⟩ := List.mem_flatMap.mp hj
      have hgrow_sup : ∀ x ∈ idx, x ∈ grow rows blk a idx := fun x hx => List.mem_append_left _ hx
      have hj_grow : j ∈ grow rows blk a idx :=
        List.mem_append_right _ (List.mem_filter.mpr ⟨hj, by simpa using hjn⟩)
      have hlt' : ∀ x ∈ grow rows blk a idx, x < rows.length := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hlt x hx
        · obtain ⟨k, -, hk⟩ := List.mem_flatMap.mp (List.mem_filter.mp hx).1
          exact lt_of_mem_req hk
      apply closureIter_closed n _ hlt'
      have hsub : Finset.range rows.length \ (grow rows blk a idx).toFinset ⊆
          Finset.range rows.length \ idx.toFinset := by
        intro x hx
        simp only [Finset.mem_sdiff, List.mem_toFinset] at hx ⊢
        exact ⟨hx.1, fun h => hx.2 (hgrow_sup x h)⟩
      have hss : Finset.range rows.length \ (grow rows blk a idx).toFinset ⊂
          Finset.range rows.length \ idx.toFinset := by
        rw [Finset.ssubset_iff_of_subset hsub]
        refine ⟨j, ?_, ?_⟩
        · simp only [Finset.mem_sdiff, List.mem_toFinset, Finset.mem_range]
          exact ⟨lt_of_mem_req hji, hjn⟩
        · simp only [Finset.mem_sdiff, List.mem_toFinset, not_and, not_not]
          exact fun _ => hj_grow
      have := Finset.card_lt_card hss
      omega

/-- **`rows.length + 1` rounds suffice**: from a valid seed, the closure with at least that much
fuel is closed. -/
theorem closure_closed {rows : List Row} {blk : Blocker} {a : AMarking} {seed fuel : Nat}
    (hseed : seed < rows.length) (hfuel : rows.length + 1 ≤ fuel) :
    Closed rows blk a (closure rows blk a seed fuel) := by
  apply closureIter_closed fuel [seed] (fun i hi => by rw [List.mem_singleton.mp hi]; exact hseed)
  have := Finset.card_le_card (Finset.sdiff_subset (s := Finset.range rows.length)
    (t := [seed].toFinset))
  rw [Finset.card_range] at this
  omega

/-- **A closed set containing an enabled seed is stubborn** ([VER-024]): the seed is the key
row, and the closure's two rules are (D1) and (D2). -/
theorem closed_stubborn {rows : List Row} {blk : Blocker} (hblk : BlockerSound blk)
    {a : AMarking} {idx : List Nat} (hcl : Closed rows blk a idx) {seed : Nat} {r0 : Row}
    (hseed : seed ∈ idx) (hr0 : rows[seed]? = some r0) (hen0 : enabledA a r0.1 = true) :
    IsStubborn rows (members rows idx) a := by
  refine ⟨⟨r0, mem_members.mpr ⟨seed, hseed, hr0⟩, hen0⟩, ?_, ?_⟩
  · intro r hr hen u hu hdep
    obtain ⟨i, hi, hri⟩ := mem_members.mp hr
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hu
    refine mem_members.mpr ⟨j, hcl i hi j ?_, hj⟩
    simp only [req, hri, hen, if_true]
    exact mem_rowsWhere.mpr ⟨u, hj, hdep⟩
  · intro r hr hdis
    obtain ⟨i, hi, hri⟩ := mem_members.mp hr
    obtain ⟨b, p, hb, h1, h2⟩ := hblk a r.1 hdis
    have hreq : ∀ u ∈ rows, (if b = true then increases u p else decreases u p) = true →
        u ∈ members rows idx := by
      intro u hu hf
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hu
      refine mem_members.mpr ⟨j, hcl i hi j ?_, hj⟩
      cases b with
      | true =>
        simp only [req, hri, hdis, hb]
        exact mem_rowsWhere.mpr ⟨u, hj, by simpa using hf⟩
      | false =>
        simp only [req, hri, hdis, hb]
        exact mem_rowsWhere.mpr ⟨u, hj, by simpa using hf⟩
    cases b with
    | true =>
      rcases h1 rfl with ⟨s, hs, hsp, hlt⟩ | ⟨hp, h0⟩
      · subst hsp
        exact Or.inl ⟨s, hs, hlt, fun u hu hinc => hreq u hu (by simpa using hinc)⟩
      · exact Or.inr (Or.inl ⟨p, hp, h0, fun u hu hinc => hreq u hu (by simpa using hinc)⟩)
    | false =>
      obtain ⟨hp, hpos⟩ := h2 rfl
      exact Or.inr (Or.inr ⟨p, hp, hpos, fun u hu hdec => hreq u hu (by simpa using hdec)⟩)

/-- The stubborn set the route expands at `a`: the closure of the seed `seedOf a` picks.
The implementation picks the enabled seed whose closure has the fewest enabled rows; any
choice of an enabled seed is covered. -/
def closureStub (rows : List Row) (blk : Blocker) (seedOf : AMarking → Nat) (fuel : Nat)
    (a : AMarking) : List Row :=
  members rows (closure rows blk a (seedOf a) fuel)

/-- **The implementation's choice is a stubborn family**: with a sound blocker, a seed that is
an enabled row whenever some row is enabled, and at least `rows.length + 1` rounds of fuel. -/
theorem closure_family {rows : List Row} {blk : Blocker} (hblk : BlockerSound blk)
    {seedOf : AMarking → Nat} {fuel : Nat}
    (hseed : ∀ a, (∃ r ∈ rows, enabledA a r.1 = true) →
      ∃ r, rows[seedOf a]? = some r ∧ enabledA a r.1 = true)
    (hfuel : rows.length + 1 ≤ fuel) : StubbornFamily rows (closureStub rows blk seedOf fuel) := by
  refine ⟨fun a u hu => ?_, fun a hex => ?_⟩
  · obtain ⟨i, -, hi⟩ := mem_members.mp hu
    exact List.mem_of_getElem? hi
  · obtain ⟨r0, hr0, hen0⟩ := hseed a hex
    have hlt : seedOf a < rows.length := (List.getElem?_eq_some_iff.mp hr0).1
    exact closed_stubborn hblk (closure_closed hlt hfuel)
      (closureIter_sup fuel [seedOf a] (seedOf a) (List.mem_singleton_self _)) hr0 hen0

/-- **[VER-024] end to end**: the enumeration that expands, at each class, the enabled rows of
the closure of an enabled seed (any seed choice, `firstBlocker` or any sound blocker) decides
every quiescence predicate exactly when it closes. -/
theorem closure_enumeration_exact_quiescence {rows : List Row} {blk : Blocker}
    (hblk : BlockerSound blk) {seedOf : AMarking → Nat} {fuel : Nat}
    (hseed : ∀ a, (∃ r ∈ rows, enabledA a r.1 = true) →
      ∃ r, rows[seedOf a]? = some r ∧ enabledA a r.1 = true)
    (hfuel : rows.length + 1 ≤ fuel) [DecidableEq AMarking] {maxClasses bfuel : Nat}
    {a0 : AMarking}
    (h : (build (succReduced (closureStub rows blk seedOf fuel)) maxClasses bfuel a0).2 = true)
    (bad : AMarking → Bool) :
    proven (fun a => (succReduced (closureStub rows blk seedOf fuel) a).isEmpty && bad a)
        (build (succReduced (closureStub rows blk seedOf fuel)) maxClasses bfuel a0).1 = true ↔
      ∀ a, ReachAD rows a0 a → Dead rows a → bad a = false :=
  (reduced_enumeration_exact_quiescence (closure_family hblk hseed hfuel) h bad).2.2

end Libpetri.Novel.Stubborn
