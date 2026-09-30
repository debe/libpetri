import Libpetri.Novel.EnvSemantics.Supplied
import Libpetri.Novel.Enumeration

/-!
# `Arrivals(min, max)` is exactly its closure ([VER-006], [VER-022])

`EnvironmentAnalysisMode::Arrivals { max }` / `ArrivalsBetween { min, max }` is a net rewrite,
not an encoding: `SmtVerifier::with_arrivals` hands the net, its marking and the registered
environment places (registration order, deduplicated) to `open_net::close_arrivals_between`,
which builds the [VER-022] closure (`close_open_net`) with one arrival group `(min, max)` per
environment place, and every route then verifies the closed net as an ordinary closed net. For
the environment place `P = envs[i]`:

* a **mandatory** source `env:arrivals[i]` holding `min`, with `env:arrive[i]:P`: `one(source) →
  P`; left out when `min = 0`;
* an **optional** source `env:optional[i]` holding `max − min`, with `env:arrive?[i]:P` and
  `env:decline[i]` (`one(source)`, no output, one empty outcome row); left out when
  `max = min`.

Here the flat index gives the sources the fresh places `base + 2i` and `base + 2i + 1` above
every place of the net (`RowsBelow`, `EnvsBelow`: the closure's name-freshness check), the rows
are `closureRows` (the net's rows, then each group's in order, as `flatten` reads the closed
net's transitions in that order) and the seed `closureM0`.

**The open semantics it claims to decide** ([VER-006]): between `min` and `max` tokens are
injected into each environment place over the whole run, and a run may rest only once every
mandatory arrival has happened. That is `StepArr`: a row step, or an arrival into `p ∈ envs`
while fewer than `max` have arrived there, with the per-place arrival count carried along.

* `arrivals_closure_reach` (**`arrivals_closure_exact`, safety**): a marking of the net is
  reachable in the closed net (any source contents) iff the open system reaches it with some
  arrival counts.
* `arrivals_closure_quiescent` (**`arrivals_closure_exact`, quiescence**): it is reachable as a
  **dead** closed marking iff the open system reaches it with **every** count `≥ min`, and no row
  of the net is enabled there. A closed dead marking has empty sources: the environment has
  delivered what it must and delivered or declined the rest.
* `proposition_one_arrivals`: the executor's runs under such an environment are runs of the
  open system; `arrivals_enumeration_sound` composes this with the closure and
  `Enumeration.rows_enumeration_exact`: a closed enumeration's `Proven` of a property of the
  net's places holds for every executor run under the environment.

Premises: `min ≤ max` (checked by `arrivals_between` / `with_arrivals`), environment places
distinct (`environment_places` inserts each once), the net's arcs, deposits, environment places
and seed below `base`. Not modelled: the inert-place and [EXEC-042] terminal rewrites that run
after this one, and names.
-/

namespace Libpetri.Novel.EnvSemantics

/-- `omega` after unfolding `PlaceId`: a comparison elaborated at type `PlaceId` is invisible to
`omega`, which matches `Nat` syntactically. -/
local macro "pomega" : tactic => `(tactic| ((try simp only [PlaceId] at *) <;> omega))

open Libpetri Libpetri.Novel.ForwardDeposit Libpetri.Novel.Seam

/-! ## The closure -/

/-- The mandatory source of group `i`. -/
def mandP (base i : Nat) : PlaceId := base + 2 * i
/-- The optional source of group `i`. -/
def optP (base i : Nat) : PlaceId := base + 2 * i + 1

/-- `arrival_transition` / the decline: one token from `src`, nothing else. -/
def srcT (name : String) (src : PlaceId) : Transition :=
  { name, inputs := [{ place := src, card := .one, guard := none }]
  , inhibitors := [], reads := [], resets := [] }

/-- Group `i`'s rows, as `close_open_net` adds its transitions. -/
def groupRows (base lo hi i : Nat) (p : PlaceId) : Rows :=
  (if 0 < lo then [(srcT s!"env:arrive[{i}]:{p}" (mandP base i), [p])] else [])
    ++ (if lo < hi then
          [(srcT s!"env:arrive?[{i}]:{p}" (optP base i), [p]),
           (srcT s!"env:decline[{i}]" (optP base i), [])]
        else [])

/-- Every group's rows, in registration order. -/
def envRows (base lo hi : Nat) (envs : List PlaceId) : Rows :=
  (List.range envs.length).flatMap fun i => groupRows base lo hi i (envs.getD i 0)

/-- The closed net's rows. -/
def closureRows (rows : Rows) (envs : List PlaceId) (base lo hi : Nat) : Rows :=
  rows ++ envRows base lo hi envs

/-- The closed net's seed: the net's marking below `base`, `min` on each mandatory source and
`max − min` on each optional one. -/
def closureM0 (a0 : AMarking) (envs : List PlaceId) (base lo hi : Nat) : AMarking := fun q =>
  if q < base then a0 q
  else if q - base < 2 * envs.length then (if (q - base) % 2 = 0 then lo else hi - lo)
  else 0

/-! ## The open semantics -/

/-- One more arrival counted at `p`. -/
def bumpC (c : PlaceId → Nat) (p : PlaceId) : PlaceId → Nat :=
  fun q => if q == p then c q + 1 else c q

/-- **One step of the open system under `Arrivals(·, hi)`**: a row fires, or one token arrives on
an environment place that has seen fewer than `hi`. -/
def StepArr (rows : Rows) (envs : List PlaceId) (hi : Nat)
    (s s' : AMarking × (PlaceId → Nat)) : Prop :=
  (StepAD rows s.1 s'.1 ∧ s'.2 = s.2) ∨
    ∃ p ∈ envs, s.2 p < hi ∧ s'.1 = injA s.1 p ∧ s'.2 = bumpC s.2 p

def ReachArr (rows : Rows) (envs : List PlaceId) (hi : Nat) (s0 : AMarking × (PlaceId → Nat)) :
    AMarking × (PlaceId → Nat) → Prop :=
  Relation.ReflTransGen (StepArr rows envs hi) s0

/-! ## Premises -/

/-- Every arc, reset and deposit of the net lies below `base`. -/
def RowsBelow (base : Nat) (rows : Rows) : Prop :=
  ∀ tr ∈ rows, (∀ s ∈ tr.1.inputs, s.place < base) ∧ (∀ q ∈ tr.1.inhibitors, q < base) ∧
    (∀ q ∈ tr.1.reads, q < base) ∧ (∀ q ∈ tr.1.resets, q < base) ∧ (∀ q ∈ tr.2, q < base)

def ZeroAbove (base : Nat) (a : AMarking) : Prop := ∀ q, base ≤ q → a q = 0

def AgreeBelow (base : Nat) (x a : AMarking) : Prop := ∀ q, q < base → x q = a q

/-! ## Row facts -/

theorem enabledA_agree {base : Nat} {rows : Rows} (hR : RowsBelow base rows) {tr}
    (htr : tr ∈ rows) {x a : AMarking} (h : AgreeBelow base x a) :
    enabledA x tr.1 = enabledA a tr.1 := by
  obtain ⟨hI, hH, hD, -, -⟩ := hR tr htr
  have e1 : tr.1.inputs.all (fun s => decide (s.card.required ≤ x s.place)) =
      tr.1.inputs.all (fun s => decide (s.card.required ≤ a s.place)) :=
    all_congr_mem fun s hs => by rw [h _ (hI s hs)]
  have e2 : tr.1.inhibitors.all (fun q => x q == 0) = tr.1.inhibitors.all (fun q => a q == 0) :=
    all_congr_mem fun q hq => by rw [h _ (hH q hq)]
  have e3 : tr.1.reads.all (fun q => decide (1 ≤ x q)) = tr.1.reads.all (fun q => decide (1 ≤ a q)) :=
    all_congr_mem fun q hq => by rw [h _ (hD q hq)]
  unfold enabledA
  rw [e1, e2, e3]

theorem fireAD_above {base : Nat} {rows : Rows} (hR : RowsBelow base rows) {tr}
    (htr : tr ∈ rows) (x : AMarking) {q : PlaceId} (hq : base ≤ q) :
    fireAD x tr.1 tr.2 q = x q := by
  obtain ⟨hI, -, -, hS, hP⟩ := hR tr htr
  have hsp : specAt tr.1 q = none := by
    unfold specAt
    rw [List.find?_eq_none]
    intro s hs
    have := hI s hs
    have hne : s.place ≠ q := by pomega
    simpa using hne
  have hres : q ∉ tr.1.resets := fun hm => by have := hS q hm; pomega
  have hcnt : tr.2.count q = 0 := by
    rw [List.count_eq_zero]
    intro hm; have := hP q hm; pomega
  simp [fireAD, hres, consumeAllAt, pre, hsp, hcnt]

theorem agree_fire {base : Nat} {x a : AMarking} (h : AgreeBelow base x a) (t : Transition)
    (d : Deposit) : AgreeBelow base (fireAD x t d) (fireAD a t d) :=
  fun q hq => fireAD_congr (h q hq) t d

theorem zeroAbove_step {base : Nat} {rows : Rows} (hR : RowsBelow base rows) {a a' : AMarking}
    (ha : ZeroAbove base a) (h : StepAD rows a a') : ZeroAbove base a' := by
  obtain ⟨tr, htr, _, rfl⟩ := h
  intro q hq
  rw [fireAD_above hR htr a hq, ha q hq]

theorem zeroAbove_inj {base : Nat} {a : AMarking} {p : PlaceId} (hp : p < base)
    (ha : ZeroAbove base a) : ZeroAbove base (injA a p) := by
  intro q hq
  have : q ≠ p := by pomega
  simp [injA, this, ha q hq]

/-! ## Source-transition facts -/

theorem enabledA_srcT (x : AMarking) (nm : String) (src : PlaceId) :
    enabledA x (srcT nm src) = decide (1 ≤ x src) := by
  simp [enabledA, srcT, Card.required]

theorem fireAD_srcT (x : AMarking) (nm : String) (src : PlaceId) (d : Deposit) (q : PlaceId) :
    fireAD x (srcT nm src) d q = x q - (if q = src then 1 else 0) + d.count q := by
  by_cases h : q = src
  · subst h; simp [fireAD, srcT, consumeAllAt, pre, specAt, Card.consumesAll, Card.required]
  · have hne : (src == q) = false := by simp; pomega
    simp [fireAD, srcT, consumeAllAt, pre, specAt, h, hne]

theorem mem_groupRows {base lo hi i : Nat} {p : PlaceId} {tr : Transition × Deposit}
    (h : tr ∈ groupRows base lo hi i p) :
    (0 < lo ∧ ∃ nm, tr = (srcT nm (mandP base i), [p])) ∨
    (lo < hi ∧ ∃ nm, tr = (srcT nm (optP base i), [p])) ∨
    (lo < hi ∧ ∃ nm, tr = (srcT nm (optP base i), [])) := by
  unfold groupRows at h
  rw [List.mem_append] at h
  rcases h with h | h
  · split at h
    · rename_i hlo; simp only [List.mem_singleton] at h; exact Or.inl ⟨hlo, _, h⟩
    · simp at h
  · split at h
    · rename_i hlh
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h
      · exact Or.inr (Or.inl ⟨hlh, _, h⟩)
      · exact Or.inr (Or.inr ⟨hlh, _, h⟩)
    · simp at h

theorem mem_envRows {base lo hi : Nat} {envs : List PlaceId} {tr : Transition × Deposit}
    (h : tr ∈ envRows base lo hi envs) :
    ∃ i < envs.length, tr ∈ groupRows base lo hi i (envs.getD i 0) := by
  unfold envRows at h
  obtain ⟨i, hi, htr⟩ := List.mem_flatMap.mp h
  exact ⟨i, List.mem_range.mp hi, htr⟩

theorem arrive_mem {rows : Rows} {envs : List PlaceId} {base lo hi i : Nat}
    (hi' : i < envs.length) (hlo : 0 < lo) :
    ∃ nm, (srcT nm (mandP base i), [envs.getD i 0]) ∈ closureRows rows envs base lo hi :=
  ⟨s!"env:arrive[{i}]:{envs.getD i 0}", List.mem_append_right _ (List.mem_flatMap.mpr
    ⟨i, List.mem_range.mpr hi', by unfold groupRows; rw [if_pos hlo]; simp⟩)⟩

theorem arriveOpt_mem {rows : Rows} {envs : List PlaceId} {base lo hi i : Nat}
    (hi' : i < envs.length) (hlh : lo < hi) :
    ∃ nm, (srcT nm (optP base i), [envs.getD i 0]) ∈ closureRows rows envs base lo hi :=
  ⟨s!"env:arrive?[{i}]:{envs.getD i 0}", List.mem_append_right _ (List.mem_flatMap.mpr
    ⟨i, List.mem_range.mpr hi', by unfold groupRows; rw [if_pos hlh]; simp⟩)⟩

theorem decline_mem {rows : Rows} {envs : List PlaceId} {base lo hi i : Nat}
    (hi' : i < envs.length) (hlh : lo < hi) :
    ∃ nm, (srcT nm (optP base i), ([] : Deposit)) ∈ closureRows rows envs base lo hi :=
  ⟨s!"env:decline[{i}]", List.mem_append_right _ (List.mem_flatMap.mpr
    ⟨i, List.mem_range.mpr hi', by unfold groupRows; rw [if_pos hlh]; simp⟩)⟩

theorem getD_eq {envs : List PlaceId} {i : Nat} (h : i < envs.length) :
    envs.getD i 0 = envs[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem getD_mem {envs : List PlaceId} {i : Nat} (h : i < envs.length) : envs.getD i 0 ∈ envs := by
  rw [getD_eq h]; exact List.getElem_mem h

theorem getD_inj {envs : List PlaceId} (hN : envs.Nodup) {i j : Nat} (hi : i < envs.length)
    (hj : j < envs.length) (h : envs.getD i 0 = envs.getD j 0) : i = j := by
  rw [getD_eq hi, getD_eq hj] at h
  exact (List.Nodup.getElem_inj_iff hN).mp h

theorem exists_index {envs : List PlaceId} {p : PlaceId} (h : p ∈ envs) :
    ∃ i < envs.length, envs.getD i 0 = p := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  exact ⟨i, hi, getD_eq hi⟩

/-! ## Invariants -/

/-- Closed → open: the sources account for the arrivals so far, declines included. -/
def InvI (base lo hi : Nat) (envs : List PlaceId) (x : AMarking) (c : PlaceId → Nat) : Prop :=
  ∀ i < envs.length, x (mandP base i) ≤ lo ∧ x (optP base i) ≤ hi - lo ∧
    x (mandP base i) + x (optP base i) + c (envs.getD i 0) ≤ hi ∧
    lo ≤ x (mandP base i) + c (envs.getD i 0)

/-- Open → closed: no decline yet, and mandatory arrivals first. -/
def InvJ (base lo hi : Nat) (envs : List PlaceId) (x : AMarking) (c : PlaceId → Nat) : Prop :=
  ∀ i < envs.length, x (mandP base i) = lo - min (c (envs.getD i 0)) lo ∧
    x (mandP base i) + x (optP base i) + c (envs.getD i 0) = hi

theorem closureM0_mand (a0 : AMarking) (envs : List PlaceId) (base lo hi : Nat) {i : Nat}
    (hi' : i < envs.length) : closureM0 a0 envs base lo hi (mandP base i) = lo := by
  unfold closureM0 mandP
  have h1 : ¬ base + 2 * i < base := by pomega
  have h2 : base + 2 * i - base < 2 * envs.length := by pomega
  have h3 : (base + 2 * i - base) % 2 = 0 := by pomega
  rw [if_neg h1, if_pos h2, if_pos h3]

theorem closureM0_opt (a0 : AMarking) (envs : List PlaceId) (base lo hi : Nat) {i : Nat}
    (hi' : i < envs.length) : closureM0 a0 envs base lo hi (optP base i) = hi - lo := by
  unfold closureM0 optP
  have h1 : ¬ base + 2 * i + 1 < base := by pomega
  have h2 : base + 2 * i + 1 - base < 2 * envs.length := by pomega
  have h3 : ¬ (base + 2 * i + 1 - base) % 2 = 0 := by pomega
  rw [if_neg h1, if_pos h2, if_neg h3]

theorem closureM0_agree (a0 : AMarking) (envs : List PlaceId) (base lo hi : Nat) :
    AgreeBelow base (closureM0 a0 envs base lo hi) a0 := by
  intro q hq; simp [closureM0, hq]

theorem arrive_at_src {base : Nat} {x : AMarking} {nm : String} {src p : PlaceId}
    (hp : p < base) (hs : base ≤ src) : fireAD x (srcT nm src) [p] src = x src - 1 := by
  rw [fireAD_srcT]
  have : p ≠ src := by pomega
  simp [this]

theorem arrive_at_p {base : Nat} {x : AMarking} {nm : String} {src p : PlaceId}
    (hp : p < base) (hs : base ≤ src) : fireAD x (srcT nm src) [p] p = x p + 1 := by
  rw [fireAD_srcT]
  have : p ≠ src := by pomega
  simp [this]

theorem arrive_at_other {x : AMarking} {nm : String} {src p q : PlaceId} (h1 : q ≠ src)
    (h2 : q ≠ p) : fireAD x (srcT nm src) [p] q = x q := by
  rw [fireAD_srcT]
  simp [h1, Ne.symm h2]

theorem decline_at_src {x : AMarking} {nm : String} {src : PlaceId} :
    fireAD x (srcT nm src) [] src = x src - 1 := by
  rw [fireAD_srcT]; simp

theorem decline_at_other {x : AMarking} {nm : String} {src q : PlaceId} (h : q ≠ src) :
    fireAD x (srcT nm src) [] q = x q := by
  rw [fireAD_srcT]; simp [h]

theorem decline_effect (x : AMarking) (nm : String) (src : PlaceId) (q : PlaceId) :
    fireAD x (srcT nm src) [] q = if q = src then x q - 1 else x q := by
  rw [fireAD_srcT]
  by_cases h : q = src <;> simp [h]

theorem bumpC_same (c : PlaceId → Nat) (p : PlaceId) : bumpC c p p = c p + 1 := by
  simp [bumpC]

theorem bumpC_other {c : PlaceId → Nat} {p q : PlaceId} (h : q ≠ p) : bumpC c p q = c q := by
  simp [bumpC, h]

/-- The coordinates of two groups are distinct places. -/
theorem src_ne {base i j : Nat} (h : j ≠ i) :
    mandP base j ≠ mandP base i ∧ mandP base j ≠ optP base i ∧ optP base j ≠ mandP base i ∧
      optP base j ≠ optP base i := by
  unfold mandP optP; refine ⟨?_, ?_, ?_, ?_⟩ <;> pomega

theorem mand_ne_opt (base i : Nat) : mandP base i ≠ optP base i := by unfold mandP optP; pomega

theorem src_ne_below {base i : Nat} {p : PlaceId} (hp : p < base) :
    mandP base i ≠ p ∧ optP base i ≠ p := by
  unfold mandP optP; constructor <;> pomega

theorem src_above (base i : Nat) : base ≤ mandP base i ∧ base ≤ optP base i := by
  unfold mandP optP; constructor <;> pomega

/-! ## Closed → open -/

theorem closed_to_open {rows : Rows} {envs : List PlaceId} {base lo hi : Nat} {a0 : AMarking}
    (hR : RowsBelow base rows) (hE : ∀ p ∈ envs, p < base) (hN : envs.Nodup) (hlh : lo ≤ hi)
    (hA0 : ZeroAbove base a0) {x : AMarking}
    (h : ReachAD (closureRows rows envs base lo hi) (closureM0 a0 envs base lo hi) x) :
    ∃ a c, ReachArr rows envs hi (a0, fun _ => 0) (a, c) ∧ AgreeBelow base x a ∧
      ZeroAbove base a ∧ InvI base lo hi envs x c := by
  induction h with
  | refl =>
    refine ⟨a0, fun _ => 0, Relation.ReflTransGen.refl, closureM0_agree _ _ _ _ _, hA0, ?_⟩
    intro i hi'
    rw [closureM0_mand _ _ _ _ _ hi', closureM0_opt _ _ _ _ _ hi']
    pomega
  | @tail x1 x2 _ hs ih =>
    obtain ⟨a, c, hr, hag, hz, hI⟩ := ih
    obtain ⟨tr, hmem, hen, rfl⟩ := hs
    rcases List.mem_append.mp hmem with hrow | henv
    · -- a row of the net: the open system fires it; the sources do not move
      have hen' : enabledA a tr.1 = true := by rw [← enabledA_agree hR hrow hag]; exact hen
      refine ⟨fireAD a tr.1 tr.2, c, hr.tail (Or.inl ⟨⟨tr, hrow, hen', rfl⟩, rfl⟩),
        agree_fire hag _ _, zeroAbove_step hR hz ⟨tr, hrow, hen', rfl⟩, ?_⟩
      intro i hi'
      rw [fireAD_above hR hrow x1 (src_above base i).1,
        fireAD_above hR hrow x1 (src_above base i).2]
      exact hI i hi'
    · obtain ⟨i, hi', hg⟩ := mem_envRows henv
      generalize hpdef : envs.getD i 0 = p at hg
      have hpE : p ∈ envs := hpdef ▸ getD_mem hi'
      have hpB : p < base := hE p hpE
      have hIi := hI i hi'
      rw [hpdef] at hIi
      have hjp : ∀ j < envs.length, j ≠ i → envs.getD j 0 ≠ p :=
        fun j hj hji he => hji (getD_inj hN hj hi' (he.trans hpdef.symm))
      have hmp := src_ne_below (i := i) hpB
      rcases mem_groupRows hg with ⟨_, nm, rfl⟩ | ⟨_, nm, rfl⟩ | ⟨_, nm, rfl⟩
      · -- mandatory arrival
        rw [enabledA_srcT] at hen
        simp only [decide_eq_true_eq] at hen
        refine ⟨injA a p, bumpC c p, hr.tail (Or.inr ⟨p, hpE, by pomega, rfl, rfl⟩), ?_,
          zeroAbove_inj hpB hz, ?_⟩
        · intro q hq
          have hqs : q ≠ mandP base i := by have := (src_above base i).1; pomega
          by_cases hqp : q = p
          · rw [hqp, arrive_at_p hpB (src_above base i).1, ← hqp, hag q hq]; simp [injA, hqp]
          · rw [arrive_at_other hqs hqp, hag q hq]; simp [injA, hqp]
        · intro j hj
          by_cases hji : j = i
          · rw [hji, hpdef, arrive_at_src hpB (src_above base i).1,
              arrive_at_other (mand_ne_opt base i).symm hmp.2, bumpC_same]
            pomega
          · obtain ⟨g1, -, g3, -⟩ := src_ne (base := base) hji
            have hmj := src_ne_below (i := j) hpB
            rw [arrive_at_other g1 hmj.1, arrive_at_other g3 hmj.2, bumpC_other (hjp j hj hji)]
            exact hI j hj
      · -- optional arrival
        rw [enabledA_srcT] at hen
        simp only [decide_eq_true_eq] at hen
        refine ⟨injA a p, bumpC c p, hr.tail (Or.inr ⟨p, hpE, by pomega, rfl, rfl⟩), ?_,
          zeroAbove_inj hpB hz, ?_⟩
        · intro q hq
          have hqs : q ≠ optP base i := by have := (src_above base i).2; pomega
          by_cases hqp : q = p
          · rw [hqp, arrive_at_p hpB (src_above base i).2, ← hqp, hag q hq]; simp [injA, hqp]
          · rw [arrive_at_other hqs hqp, hag q hq]; simp [injA, hqp]
        · intro j hj
          by_cases hji : j = i
          · rw [hji, hpdef, arrive_at_src hpB (src_above base i).2,
              arrive_at_other (mand_ne_opt base i) hmp.1, bumpC_same]
            pomega
          · obtain ⟨-, g2, -, g4⟩ := src_ne (base := base) hji
            have hmj := src_ne_below (i := j) hpB
            rw [arrive_at_other g2 hmj.1, arrive_at_other g4 hmj.2, bumpC_other (hjp j hj hji)]
            exact hI j hj
      · -- decline: the open system does nothing
        rw [enabledA_srcT] at hen
        simp only [decide_eq_true_eq] at hen
        refine ⟨a, c, hr, ?_, hz, ?_⟩
        · intro q hq
          have hqs : q ≠ optP base i := by have := (src_above base i).2; pomega
          rw [decline_at_other hqs, hag q hq]
        · intro j hj
          by_cases hji : j = i
          · rw [hji, hpdef, decline_at_src, decline_at_other (mand_ne_opt base i)]
            pomega
          · obtain ⟨-, g2, -, g4⟩ := src_ne (base := base) hji
            rw [decline_at_other g2, decline_at_other g4]
            exact hI j hj

/-! ## Open → closed -/

theorem open_to_closed {rows : Rows} {envs : List PlaceId} {base lo hi : Nat} {a0 : AMarking}
    (hR : RowsBelow base rows) (hE : ∀ p ∈ envs, p < base) (hN : envs.Nodup) (hlh : lo ≤ hi)
    {a : AMarking} {c : PlaceId → Nat}
    (h : ReachArr rows envs hi (a0, fun _ => 0) (a, c)) :
    ∃ x, ReachAD (closureRows rows envs base lo hi) (closureM0 a0 envs base lo hi) x ∧
      AgreeBelow base x a ∧ InvJ base lo hi envs x c := by
  suffices H : ∀ s, ReachArr rows envs hi (a0, fun _ => 0) s →
      ∃ x, ReachAD (closureRows rows envs base lo hi) (closureM0 a0 envs base lo hi) x ∧
        AgreeBelow base x s.1 ∧ InvJ base lo hi envs x s.2 from H _ h
  intro s hs
  induction hs with
  | refl =>
    refine ⟨_, Relation.ReflTransGen.refl, closureM0_agree _ _ _ _ _, ?_⟩
    intro i hi'
    rw [closureM0_mand _ _ _ _ _ hi', closureM0_opt _ _ _ _ _ hi']
    refine ⟨by simp, ?_⟩
    simp only
    pomega
  | @tail s1 s2 _ hst ih =>
    obtain ⟨x, hx, hag, hJ⟩ := ih
    rcases hst with ⟨⟨tr, hrow, hen, h1⟩, h2⟩ | ⟨p, hpE, hlt, h1, h2⟩
    · refine ⟨fireAD x tr.1 tr.2, hx.tail ⟨tr, List.mem_append_left _ hrow, ?_, rfl⟩, ?_, ?_⟩
      · rw [enabledA_agree hR hrow hag]; exact hen
      · rw [h1]; exact agree_fire hag _ _
      · intro i hi'
        rw [fireAD_above hR hrow x (src_above base i).1,
          fireAD_above hR hrow x (src_above base i).2, h2]
        exact hJ i hi'
    · obtain ⟨i, hi', hpi⟩ := exists_index hpE
      have hpB : p < base := hE p hpE
      have hJi := hJ i hi'
      rw [hpi] at hJi
      have hjp : ∀ j < envs.length, j ≠ i → envs.getD j 0 ≠ p :=
        fun j hj hji he => hji (getD_inj hN hj hi' (he.trans hpi.symm))
      have hmp := src_ne_below (i := i) hpB
      have hag' : ∀ (src : PlaceId) (nm : String), base ≤ src →
          AgreeBelow base (fireAD x (srcT nm src) [p]) s2.1 := by
        intro src nm hsrc q hq
        rw [h1]
        have hqs : q ≠ src := by pomega
        by_cases hqp : q = p
        · rw [hqp, arrive_at_p hpB hsrc, ← hqp, hag q hq]; simp [injA, hqp]
        · rw [arrive_at_other hqs hqp, hag q hq]; simp [injA, hqp]
      by_cases hM : 1 ≤ x (mandP base i)
      · -- the mandatory source first
        have hlo : 0 < lo := by pomega
        obtain ⟨nm, hmem⟩ := arrive_mem (rows := rows) (base := base) (hi := hi) hi' hlo
        rw [hpi] at hmem
        refine ⟨_, hx.tail ⟨_, hmem, by rw [enabledA_srcT]; simpa using hM, rfl⟩,
          hag' _ nm (src_above base i).1, ?_⟩
        intro j hj
        rw [h2]
        by_cases hji : j = i
        · rw [hji, hpi, arrive_at_src hpB (src_above base i).1,
            arrive_at_other (mand_ne_opt base i).symm hmp.2, bumpC_same]
          pomega
        · obtain ⟨g1, -, g3, -⟩ := src_ne (base := base) hji
          have hmj := src_ne_below (i := j) hpB
          rw [arrive_at_other g1 hmj.1, arrive_at_other g3 hmj.2, bumpC_other (hjp j hj hji)]
          exact hJ j hj
      · -- then the optional one
        have hO : 1 ≤ x (optP base i) := by pomega
        have hlh' : lo < hi := by pomega
        obtain ⟨nm, hmem⟩ := arriveOpt_mem (rows := rows) (base := base) hi' hlh'
        rw [hpi] at hmem
        refine ⟨_, hx.tail ⟨_, hmem, by rw [enabledA_srcT]; simpa using hO, rfl⟩,
          hag' _ nm (src_above base i).2, ?_⟩
        intro j hj
        rw [h2]
        by_cases hji : j = i
        · rw [hji, hpi, arrive_at_src hpB (src_above base i).2,
            arrive_at_other (mand_ne_opt base i) hmp.1, bumpC_same]
          pomega
        · obtain ⟨-, g2, -, g4⟩ := src_ne (base := base) hji
          have hmj := src_ne_below (i := j) hpB
          rw [arrive_at_other g2 hmj.1, arrive_at_other g4 hmj.2, bumpC_other (hjp j hj hji)]
          exact hJ j hj

/-! ## Exactness -/

theorem reachArr_zeroAbove {rows : Rows} {envs : List PlaceId} {base hi : Nat}
    (hR : RowsBelow base rows) (hE : ∀ p ∈ envs, p < base) {s0 s : AMarking × (PlaceId → Nat)}
    (h0 : ZeroAbove base s0.1) (h : ReachArr rows envs hi s0 s) : ZeroAbove base s.1 := by
  induction h with
  | refl => exact h0
  | tail _ hs ih =>
    rcases hs with ⟨hst, _⟩ | ⟨p, hp, _, h1, _⟩
    · exact zeroAbove_step hR ih hst
    · rw [h1]; exact zeroAbove_inj (hE p hp) ih

/-- **`arrivals_closure_exact`, safety.** A marking of the net (zero on the fresh places) is
reachable in the closed net iff the open system with at most `hi` arrivals per environment place
reaches it. So every safety property of the net's places means the same on both. -/
theorem arrivals_closure_reach {rows : Rows} {envs : List PlaceId} {base lo hi : Nat}
    {a0 : AMarking} (hR : RowsBelow base rows) (hE : ∀ p ∈ envs, p < base) (hN : envs.Nodup)
    (hlh : lo ≤ hi) (hA0 : ZeroAbove base a0) {a : AMarking} (ha : ZeroAbove base a) :
    (∃ x, ReachAD (closureRows rows envs base lo hi) (closureM0 a0 envs base lo hi) x ∧
        AgreeBelow base x a) ↔
      ∃ c, ReachArr rows envs hi (a0, fun _ => 0) (a, c) := by
  constructor
  · rintro ⟨x, hx, hag⟩
    obtain ⟨a', c, hr, hag', hz, -⟩ := closed_to_open hR hE hN hlh hA0 hx
    have : a' = a := by
      funext q
      by_cases hq : q < base
      · rw [← hag' q hq, hag q hq]
      · rw [hz q (by pomega), ha q (by pomega)]
    exact ⟨c, this ▸ hr⟩
  · rintro ⟨c, hr⟩
    obtain ⟨x, hx, hag, -⟩ := open_to_closed hR hE hN hlh hr
    exact ⟨x, hx, hag⟩

/-- Clear the optional source of groups `0 … n-1`. -/
def clearOpt (base : Nat) (x : AMarking) : Nat → AMarking
  | 0 => x
  | n + 1 => fun q => if q = optP base n then 0 else clearOpt base x n q

theorem clearOpt_ne {base : Nat} {x : AMarking} {q : PlaceId} :
    ∀ n, (∀ i < n, q ≠ optP base i) → clearOpt base x n q = x q
  | 0, _ => rfl
  | n + 1, h => by
    simp only [clearOpt]
    rw [if_neg (h n (by pomega)), clearOpt_ne n (fun i hi => h i (by pomega))]

theorem clearOpt_opt {base : Nat} {x : AMarking} {i : Nat} :
    ∀ n, i < n → clearOpt base x n (optP base i) = 0
  | 0, h => absurd h (by pomega)
  | n + 1, h => by
    simp only [clearOpt]
    by_cases hin : i = n
    · subst hin; simp
    · rw [if_neg (by unfold optP; pomega)]; exact clearOpt_opt n (by pomega)

/-- Declining `n` optional tokens of group `i` empties its optional source. -/
theorem decline_reach {rows : Rows} {envs : List PlaceId} {base lo hi i : Nat}
    (hi' : i < envs.length) (hlh : lo < hi) :
    ∀ n (y : AMarking), y (optP base i) = n →
      Relation.ReflTransGen (StepAD (closureRows rows envs base lo hi)) y
        (fun q => if q = optP base i then 0 else y q)
  | 0, y, hy => by
    have : (fun q => if q = optP base i then 0 else y q) = y := by
      funext q; by_cases h : q = optP base i <;> simp [h, hy]
    rw [this]
  | n + 1, y, hy => by
    obtain ⟨nm, hmem⟩ := decline_mem (rows := rows) (base := base) hi' hlh
    have hstep : StepAD (closureRows rows envs base lo hi) y (fireAD y (srcT nm (optP base i)) []) :=
      ⟨_, hmem, by rw [enabledA_srcT, hy]; simp, rfl⟩
    have ih := decline_reach (rows := rows) hi' hlh n (fireAD y (srcT nm (optP base i)) [])
      (by rw [decline_at_src, hy]; pomega)
    have e : (fun q => if q = optP base i then 0
        else fireAD y (srcT nm (optP base i)) [] q) = fun q => if q = optP base i then 0 else y q := by
      funext q; by_cases h : q = optP base i <;> simp [h, decline_effect]
    rw [e] at ih
    exact Relation.ReflTransGen.head hstep ih

theorem clearOpt_reach {rows : Rows} {envs : List PlaceId} {base lo hi : Nat} {x : AMarking}
    (hopt : ∀ i < envs.length, lo < hi ∨ x (optP base i) = 0) :
    ∀ n, n ≤ envs.length →
      Relation.ReflTransGen (StepAD (closureRows rows envs base lo hi)) x (clearOpt base x n)
  | 0, _ => Relation.ReflTransGen.refl
  | n + 1, hn => by
    have ih := clearOpt_reach (rows := rows) hopt n (by pomega)
    have hcur : clearOpt base x n (optP base n) = x (optP base n) :=
      clearOpt_ne n (fun i hi => by unfold optP; pomega)
    rcases hopt n (by pomega) with hlh | hz
    · have := decline_reach (rows := rows) (envs := envs) (base := base) (i := n) (by pomega) hlh _
        (clearOpt base x n) rfl
      exact ih.trans this
    · have : clearOpt base x (n + 1) = clearOpt base x n := by
        funext q
        simp only [clearOpt]
        by_cases h : q = optP base n
        · subst h; rw [if_pos rfl, hcur, hz]
        · rw [if_neg h]
      rw [this]; exact ih

/-- **`arrivals_closure_exact`, quiescence.** A marking of the net is a dead marking of the
closed net iff the open system reaches it with **at least `lo`** arrivals on every environment
place and no row of the net enabled: a closed run rests only once every mandatory arrival has
happened (and every optional one arrived or was declined). -/
theorem arrivals_closure_quiescent {rows : Rows} {envs : List PlaceId} {base lo hi : Nat}
    {a0 : AMarking} (hR : RowsBelow base rows) (hE : ∀ p ∈ envs, p < base) (hN : envs.Nodup)
    (hlh : lo ≤ hi) (hA0 : ZeroAbove base a0) {a : AMarking} (ha : ZeroAbove base a) :
    (∃ x, ReachAD (closureRows rows envs base lo hi) (closureM0 a0 envs base lo hi) x ∧
        Dead (closureRows rows envs base lo hi) x ∧ AgreeBelow base x a) ↔
      ∃ c, ReachArr rows envs hi (a0, fun _ => 0) (a, c) ∧ (∀ p ∈ envs, lo ≤ c p) ∧
        Dead rows a := by
  constructor
  · rintro ⟨x, hx, hd, hag⟩
    obtain ⟨a', c, hr, hag', hz, hI⟩ := closed_to_open hR hE hN hlh hA0 hx
    have ha' : a' = a := by
      funext q
      by_cases hq : q < base
      · rw [← hag' q hq, hag q hq]
      · rw [hz q (by pomega), ha q (by pomega)]
    subst ha'
    refine ⟨c, hr, ?_, ?_⟩
    · intro p hp
      obtain ⟨i, hi', rfl⟩ := exists_index hp
      obtain ⟨hMlo, hOlo, _, hlc⟩ := hI i hi'
      have hM0 : x (mandP base i) = 0 := by
        by_cases hlo : 0 < lo
        · obtain ⟨nm, hmem⟩ := arrive_mem (rows := rows) (base := base) (hi := hi) hi' hlo
          have := hd _ hmem
          rw [enabledA_srcT] at this
          simpa using this
        · pomega
      pomega
    · intro tr htr
      rw [← enabledA_agree hR htr hag']
      exact hd tr (List.mem_append_left _ htr)
  · rintro ⟨c, hr, hlo, hd⟩
    obtain ⟨x, hx, hag, hJ⟩ := open_to_closed hR hE hN hlh hr
    have hM : ∀ i < envs.length, x (mandP base i) = 0 := by
      intro i hi'
      have := (hJ i hi').1
      have := hlo _ (getD_mem hi')
      rw [Nat.min_eq_right (by pomega)] at *
      pomega
    have hopt : ∀ i < envs.length, lo < hi ∨ x (optP base i) = 0 := by
      intro i hi'
      have h1 := (hJ i hi').2
      have h2 := hlo _ (getD_mem hi')
      have h3 := hM i hi'
      pomega
    refine ⟨clearOpt base x envs.length, hx.trans (clearOpt_reach hopt _ le_rfl), ?_, ?_⟩
    · have hag2 : AgreeBelow base (clearOpt base x envs.length) a := by
        intro q hq
        rw [clearOpt_ne _ (fun i _ => by unfold optP; pomega), hag q hq]
      intro tr htr
      rcases List.mem_append.mp htr with hrow | henv
      · rw [enabledA_agree hR hrow hag2]; exact hd tr hrow
      · obtain ⟨i, hi', hg⟩ := mem_envRows henv
        rcases mem_groupRows hg with ⟨_, nm, rfl⟩ | ⟨_, nm, rfl⟩ | ⟨_, nm, rfl⟩
        · rw [enabledA_srcT, clearOpt_ne _ (fun j _ => by unfold optP mandP; pomega), hM i hi']
          rfl
        · rw [enabledA_srcT, clearOpt_opt _ hi']; rfl
        · rw [enabledA_srcT, clearOpt_opt _ hi']; rfl
    · intro q hq
      rw [clearOpt_ne _ (fun i _ => by unfold optP; pomega), hag q hq]

/-! ## The executor under an arrivals environment -/

/-- **One concrete step under `Arrivals(·, hi)`**: the executor fires a row, or the environment
injects one token into an environment place that has seen fewer than `hi`. -/
def StepCArr (rows : Rows) (envs : List PlaceId) (hi : Nat)
    (s s' : CMarking × (PlaceId → Nat)) : Prop :=
  (StepCR rows s.1 s'.1 ∧ s'.2 = s.2) ∨
    ∃ p ∈ envs, s.2 p < hi ∧ (∃ col, s'.1 = injC s.1 p col) ∧ s'.2 = bumpC s.2 p

/-- **Proposition 1 under arrivals.** -/
theorem proposition_one_arrivals {rows : Rows} {envs : List PlaceId} {hi : Nat}
    (hG : ∀ tr ∈ rows, GuardFreeConsumeAll tr.1) {s0 s : CMarking × (PlaceId → Nat)}
    (h : Relation.ReflTransGen (StepCArr rows envs hi) s0 s) :
    ReachArr rows envs hi (alpha s0.1, s0.2) (alpha s.1, s.2) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih =>
    rcases hs with ⟨hst, h2⟩ | ⟨p, hp, hlt, ⟨col, h1⟩, h2⟩
    · exact ih.tail (Or.inl ⟨stepCR_simulated hG hst, h2⟩)
    · exact ih.tail (Or.inr ⟨p, hp, hlt, by rw [h1, alpha_injC], h2⟩)

/-- **The closed enumeration's `Proven` holds for the executor under `Arrivals(lo, hi)`.** If the
state-space enumeration of the closed rows closes and proves `bad` false, and `bad` reads only
the net's places, no executor run under an environment delivering at most `hi` tokens per
environment place reaches a bad marking. -/
theorem arrivals_enumeration_sound {rows : Rows} {envs : List PlaceId} {base lo hi : Nat}
    [DecidableEq AMarking] {maxClasses fuel : Nat} {m0 : CMarking}
    (hR : RowsBelow base rows) (hE : ∀ p ∈ envs, p < base) (hN : envs.Nodup) (hlh : lo ≤ hi)
    (hG : ∀ tr ∈ rows, GuardFreeConsumeAll tr.1) (hM0 : ZeroAbove base (alpha m0))
    (hB : (Enumeration.build (Enumeration.succRows (closureRows rows envs base lo hi))
      maxClasses fuel (closureM0 (alpha m0) envs base lo hi)).2 = true)
    (bad : AMarking → Bool) (hbad : ∀ x y, AgreeBelow base x y → bad x = bad y)
    (hp : Enumeration.proven bad (Enumeration.build
      (Enumeration.succRows (closureRows rows envs base lo hi)) maxClasses fuel
      (closureM0 (alpha m0) envs base lo hi)).1 = true)
    {s : CMarking × (PlaceId → Nat)}
    (hr : Relation.ReflTransGen (StepCArr rows envs hi) (m0, fun _ => 0) s) :
    bad (alpha s.1) = false := by
  have hA := proposition_one_arrivals hG hr
  have hz := reachArr_zeroAbove (s0 := (alpha m0, fun _ => 0)) hR hE hM0 hA
  obtain ⟨x, hx, hag⟩ := (arrivals_closure_reach hR hE hN hlh hM0 hz).mpr ⟨_, hA⟩
  have := ((Enumeration.rows_enumeration_exact hB bad).2.1.mp hp) x hx
  rw [← hbad x _ hag]; exact this

end Libpetri.Novel.EnvSemantics
