/-
# The scheduling layer: priority partition and enablement-time FIFO

The general (timed / multi-priority) ready path — `collect_ready_general`
(`rust/libpetri-runtime/src/precompiled_backend.rs`, post-fix (a)) against
the reference's stable sort (`bitmap_backend.rs`: `(priority DESC,
enabled_at ASC)` over an ascending-tid buffer).

Clocks are abstract naturals (`enabled_at_ms` under any order-embedding of
the reals the executor actually compares — only `≤`/`<` comparisons occur;
`NEG_INFINITY` never reaches the ready path because only *enabled*
transitions are scanned, EN4). Readiness is `earliest ≤ now - clock`
(TIME-010 lower bound).

The heart of fix (a): the canonical ready order is the *unique* permutation
of the ready set sorted by the strict lexicographic key
`(priority DESC, clock ASC, tid ASC)` — unique because the tid component
makes keys distinct, which is exactly why the shipped fix may use
`sort_unstable`. Both implementations are then provably equal to it:

* `bbOrder_eq_canonical` — the reference's stable sort output: sorted by
  `(priority DESC, clock ASC)` with ascending-tid tiebreak (stability over
  an ascending-tid input buffer).
* `pcOrder_eq_canonical` — the post-fix precompiled output: per-priority
  levels drained in descending order, each level's slice sorted by
  `(clock, tid)` (the in-place `sort_unstable_by` of fix (a)).
* `collect_ready_general_refines` — therefore the two outputs are equal.

Formally, each implementation's output is characterised by the premises
(a permutation of the ready set with the respective sortedness shape) rather
than by re-implementing the sort algorithms; the shapes are the documented
postconditions of `sort_by`/`sort_unstable_by` plus the queue structure.
RQ1–RQ4 of the plan are the `levelPartition_sorted` premise components.

Both backends' `collect_ready_general` ends by calling `begin_firing_pass`
(refresh the fire-pass presence snapshot from live, reset the pass's
`deposit_delta` — EXEC-003 AC3/AC4). That writes state only
`recheck_can_fire` reads; it neither adds to nor removes from the ready set
and does not touch its order, so it is outside this module's fragment.
-/
import Libpetri.Basic

namespace Libpetri

/-- The scheduling view of one transition: its priority, its enablement
timestamp (`enabled_at_ms`, abstract Nat), and its id. -/
structure SchedKey where
  prio  : Nat → Int
  clock : Nat → Nat

namespace SchedKey

variable (K : SchedKey)

/-- The strict canonical order: priority descending, then enablement time
ascending, then tid ascending (EXEC-002 AC1–AC3). -/
def lt (a b : Nat) : Prop :=
  K.prio b < K.prio a
    ∨ (K.prio a = K.prio b
        ∧ (K.clock a < K.clock b ∨ (K.clock a = K.clock b ∧ (a : Nat) < b)))

theorem lt_asymm {a b : Nat} (h1 : K.lt a b) (h2 : K.lt b a) : False := by
  unfold lt at h1 h2
  rcases h1 with h1 | ⟨e1, h1 | ⟨c1, h1⟩⟩ <;>
    rcases h2 with h2 | ⟨e2, h2 | ⟨c2, h2⟩⟩ <;> omega

theorem lt_trans {a b c : Nat} (h1 : K.lt a b) (h2 : K.lt b c) : K.lt a c := by
  unfold lt at h1 h2 ⊢
  rcases h1 with h1 | ⟨e1, h1 | ⟨c1, h1⟩⟩ <;>
    rcases h2 with h2 | ⟨e2, h2 | ⟨c2, h2⟩⟩ <;>
    first
      | exact Or.inl (by omega)
      | exact Or.inr ⟨by omega, Or.inl (by omega)⟩
      | exact Or.inr ⟨by omega, Or.inr ⟨by omega, by omega⟩⟩

/-- Totality on distinct tids: the tid component decides ties. -/
theorem lt_connex {a b : Nat} (hne : a ≠ b) : K.lt a b ∨ K.lt b a := by
  unfold lt
  rcases Int.lt_trichotomy (K.prio a) (K.prio b) with h | h | h
  · right; left; omega
  · rcases Nat.lt_trichotomy (K.clock a) (K.clock b) with h' | h' | h'
    · left; right; exact ⟨h, Or.inl h'⟩
    · rcases Nat.lt_trichotomy a b with h'' | h'' | h''
      · left; right; exact ⟨h, Or.inr ⟨h', h''⟩⟩
      · exact absurd h'' hne
      · right; right; exact ⟨h.symm, Or.inr ⟨h'.symm, h''⟩⟩
    · right; right; exact ⟨h.symm, Or.inl h'⟩
  · left; left; omega

end SchedKey

/-- **The uniqueness backbone**: two lists strictly sorted by the same
asymmetric transitive order and containing the same elements are equal. This
is why fix (a)'s `sort_unstable_by` with the `(enabled_at, tid)` key is
deterministic and stability-free. -/
theorem eq_of_perm_of_sorted (K : SchedKey) :
    ∀ {l₁ l₂ : List Nat}, l₁.Pairwise K.lt → l₂.Pairwise K.lt →
      l₁.Perm l₂ → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ _ _ hperm
    exact (List.Perm.nil_eq hperm).symm |>.symm ▸ rfl
  | cons a t₁ ih =>
    intro l₂ hs₁ hs₂ hperm
    cases l₂ with
    | nil => exact absurd hperm.symm (by simp)
    | cons b t₂ =>
      rw [List.pairwise_cons] at hs₁ hs₂
      have hab : a = b := by
        by_cases h : a = b
        · exact h
        · exfalso
          have ha2 : a ∈ b :: t₂ := hperm.mem_iff.mp List.mem_cons_self
          have hb1 : b ∈ a :: t₁ := hperm.mem_iff.mpr List.mem_cons_self
          rcases List.mem_cons.mp ha2 with h1 | h1
          · exact h h1
          · rcases List.mem_cons.mp hb1 with h2 | h2
            · exact h h2.symm
            · exact K.lt_asymm (hs₁.1 b h2) (hs₂.1 a h1)
      subst hab
      rw [ih hs₁.2 hs₂.2 (hperm.cons_inv)]

/-! ## The ready set (general path, Nat clocks) -/

/-- The ready predicate of `collect_ready_general`: enabled, and the TIME-010
lower bound has elapsed (`earliest_ms[tid] <= now_ms - enabled_at_ms[tid]`). -/
def isReady (enabled : Nat → Bool) (K : SchedKey) (earliest : Nat → Nat)
    (now : Nat) (tid : Nat) : Bool :=
  enabled tid && decide (earliest tid ≤ now - K.clock tid)

/-- The ready tids in ascending tid order — both backends' scan order
(the enabled-bitmap walk / the reference's buffer build). -/
def readyScan (T : Nat) (enabled : Nat → Bool) (K : SchedKey)
    (earliest : Nat → Nat) (now : Nat) : List Nat :=
  (List.range T).filter (isReady enabled K earliest now)

/-! ## The shapes the two implementations produce -/

/-- RQ1–RQ4: the post-fix precompiled output shape. `blocks` are the
per-priority-level queue contents at drain time: one block per non-empty
level in strictly descending priority (RQ2/RQ3, `priority_levels` is sorted
descending and drained in order), each block's members carrying exactly that
level's priority (RQ1, `transition_to_priority_index` routing), and each
block sorted by `(clock, tid)` (RQ4 — fix (a)'s in-place
`sort_unstable_by` on the occupied slice). -/
structure LevelBlocks (K : SchedKey) (blocks : List (Int × List Nat)) : Prop where
  desc : (blocks.map (·.1)).Pairwise (· > ·)
  homo : ∀ b ∈ blocks, ∀ tid ∈ b.2, K.prio tid = b.1
  sorted : ∀ b ∈ blocks, b.2.Pairwise (fun a c =>
    K.clock a < K.clock c ∨ (K.clock a = K.clock c ∧ (a : Nat) < c))

private theorem pairwise_imp_mem {α : Type} {R S : α → α → Prop} :
    ∀ {l : List α}, (∀ a ∈ l, ∀ b ∈ l, R a b → S a b) → l.Pairwise R →
      l.Pairwise S := by
  intro l
  induction l with
  | nil => intro _ _; exact List.Pairwise.nil
  | cons x t ih =>
    intro h hp
    rw [List.pairwise_cons] at hp ⊢
    exact ⟨fun b hb =>
        h x List.mem_cons_self b (List.mem_cons_of_mem _ hb) (hp.1 b hb),
      ih (fun a ha b hb =>
        h a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)) hp.2⟩

/-- Draining the blocks in order is strictly sorted by the canonical key. -/
theorem levelBlocks_sorted {K : SchedKey} :
    ∀ {blocks : List (Int × List Nat)}, LevelBlocks K blocks →
      (blocks.flatMap (·.2)).Pairwise K.lt := by
  intro blocks
  induction blocks with
  | nil => intro _; exact List.Pairwise.nil
  | cons b rest ih =>
    intro hlb
    rw [List.flatMap_cons, List.pairwise_append]
    obtain ⟨hdesc, hhomo, hsorted⟩ := hlb
    rw [List.map_cons, List.pairwise_cons] at hdesc
    refine ⟨?_, ?_, ?_⟩
    · -- within the head block: same priority, (clock, tid)-sorted
      exact pairwise_imp_mem
        (fun a ha c hc hac => Or.inr ⟨by
          rw [hhomo b List.mem_cons_self a ha,
            hhomo b List.mem_cons_self c hc], hac⟩)
        (hsorted b List.mem_cons_self)
    · exact ih ⟨hdesc.2, fun b' hm => hhomo b' (List.mem_cons_of_mem _ hm),
        fun b' hm => hsorted b' (List.mem_cons_of_mem _ hm)⟩
    · -- across blocks: strictly descending priorities
      intro a ha c hc
      left
      obtain ⟨b', hb', hcb'⟩ := List.mem_flatMap.mp hc
      rw [hhomo b List.mem_cons_self a ha,
        hhomo b' (List.mem_cons_of_mem _ hb') c hcb']
      exact hdesc.1 b'.1 (List.mem_map.mpr ⟨b', hb', rfl⟩)

/-- **`collect_ready_general` refines the reference (fix (a) correct).**

If the post-fix precompiled backend drains priority-level blocks of the
ready set (`LevelBlocks` — RQ1–RQ4), and the reference produces any
canonically sorted ordering of the same ready set (its stable
`(priority DESC, enabled_at ASC)` sort over the ascending-tid buffer — with
stability supplying the ascending-tid tiebreak), then the two outputs are
*equal*: same transitions, fired in the same order (EXEC-002 AC1–AC4,
CONC-023 AC4). -/
theorem collect_ready_general_refines {K : SchedKey}
    {blocks : List (Int × List Nat)} {bbOut ready : List Nat}
    (hlb : LevelBlocks K blocks)
    (hpcperm : (blocks.flatMap (·.2)).Perm ready)
    (hbbsorted : bbOut.Pairwise K.lt) (hbbperm : bbOut.Perm ready) :
    blocks.flatMap (·.2) = bbOut :=
  eq_of_perm_of_sorted K (levelBlocks_sorted hlb) hbbsorted
    (hpcperm.trans hbbperm.symm)

end Libpetri
