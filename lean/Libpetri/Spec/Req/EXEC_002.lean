import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryTime
import Libpetri.RetrodictExec
import Libpetri.Spec.Text.EXEC_002

set_option linter.missingDocs true

/-!
# EXEC-002: Priority-based firing order (`spec/04-execution-model.md`)

EXEC-002 is a pure function of one pass's inputs: which transitions are ready, their
priorities, their timings and their stamps decide the order in which the pass offers
them for firing. The requirement is a predicate over an abstract ordering function
`O : ReadyIn → List Nat` (the ready order of every backend, as declaration indices). The
evidence theorems check it against the reference order `refReadyOrder`, against the
declaration-order scan, and against mutant orders: the pre-fix per-level drain in declaration
order (`tid_order_diverges`), a tie broken by descending declaration order, a LIFO order, orders
that misbehave only on the all-immediate fast path, and the general sort used on every input.

On the all-immediate fast path (one priority, every transition `Immediate`) the order is the
ready transitions in ascending declaration order, whatever their stamps, as the section states
and ruling D14 (a) accepts (`EXEC_002_mutant_fastOpen_killed`).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Novel.TimedScg (Timing)

/-! ## The interface: the inputs of one pass's ready order -/

/-- The inputs of one pass's ready order. The net's transitions are numbered `0 … n-1` in
declaration order; a transition is named by its number. -/
structure ReadyIn where
  /-- The number of transitions of the net. -/
  n      : Nat
  /-- The priority of each transition. -/
  prio   : Nat → Int
  /-- The timing of each transition ([TIME-001]). -/
  timing : Nat → Timing
  /-- The stamp of each transition: the firing-clock reading taken by the enablement update
  that most recently newly armed it (glossary: Armed, [TIME-010]). `ReadyIn.ofTSt` reads it off
  a timed state. -/
  clock  : Nat → Nat
  /-- The transition is ready (glossary: Ready): armed, past its earliest bound, not expired.
  `ReadyIn.ofTSt` reads it off a timed state. -/
  ready  : Nat → Bool

/-- An ordering function: the ready order a backend computes from a pass's inputs. -/
abbrev ReadyOrder := ReadyIn → List Nat

namespace ReadyIn

/-- The ready transitions, in declaration order. -/
def readyList (I : ReadyIn) : List Nat := (List.range I.n).filter I.ready

/-- The canonical key of the pass: priority descending, then stamp ascending, then
declaration order ascending (`SchedKey.lt`, `Sched.lean`). -/
def key (I : ReadyIn) : SchedKey := { prio := I.prio, clock := I.clock }

/-- The tie order of AC3: two transitions of equal priority and equal stamp come in
ascending declaration order (no constraint on any other pair). -/
def tieLt (I : ReadyIn) (a b : Nat) : Prop :=
  I.prio a = I.prio b → I.clock a = I.clock b → a < b

/-- The condition of the all-immediate fast path: every transition of the net is `Immediate`
and all priorities are equal. -/
def FastPath (I : ReadyIn) : Prop :=
  ∀ a, a < I.n → ∀ b, b < I.n → I.timing a = .immediate ∧ I.prio a = I.prio b

instance (I : ReadyIn) : Decidable I.FastPath := by
  unfold FastPath; infer_instance

theorem readyList_nodup (I : ReadyIn) : I.readyList.Nodup :=
  (List.nodup_range).filter _

theorem mem_readyList (I : ReadyIn) (a : Nat) : a ∈ I.readyList ↔ a < I.n ∧ I.ready a = true := by
  simp [readyList]

/-- The ready list is in ascending declaration order. -/
theorem readyList_sorted (I : ReadyIn) : I.readyList.Pairwise (· < ·) :=
  List.Pairwise.filter _ List.pairwise_lt_range

/-- A net with a transition that is not `Immediate` does not take the fast path. -/
theorem not_fastPath_of_timing {I : ReadyIn} {a : Nat} (ha : a < I.n)
    (h : I.timing a ≠ .immediate) : ¬ I.FastPath :=
  fun hf => h (hf a ha a ha).1

/-- **The bridge to the timed state.** The inputs of a pass taken from a timed state `s` of the
net `X`: the transitions `ts` in declaration order, their priorities `prio` (the timed reference
step has none), their timings, their stamps, and the glossary term Ready as
the ready bit. Indices past the list are not ready. -/
def ofTSt {N : Type} [DecidableEq N] (X : TimedNet N) (prio : Trans N → Int) (s : TSt N)
    (ts : List (Trans N)) : ReadyIn where
  n := ts.length
  prio i := (ts[i]?.map prio).getD 0
  timing i := (ts[i]?.map (TimingOf X)).getD .immediate
  clock i := (ts[i]?.bind fun t => s.stamp t.core.name).getD 0
  ready i := (ts[i]?.map fun t => decide (Ready X s t)).getD false

/-- On a bridged input, a transition of the list is ready exactly when it is Ready in the timed
state (glossary). -/
theorem ofTSt_ready {N : Type} [DecidableEq N] (X : TimedNet N) (prio : Trans N → Int)
    (s : TSt N) (ts : List (Trans N)) (i : Nat) (hi : i < ts.length) :
    (ofTSt X prio s ts).ready i = true ↔ Ready X s ts[i] := by
  simp [ofTSt, List.getElem?_eq_getElem hi]

/-- On a bridged input, a transition of the list that is armed and has not yet reached its
earliest bound is not in the ready list (TIME-010 line 4's gate, seen by the ready order). -/
theorem ofTSt_not_ready_early {N : Type} [DecidableEq N] (X : TimedNet N) (prio : Trans N → Int)
    (s : TSt N) (ts : List (Trans N)) (i : Nat) (hi : i < ts.length)
    (he : Elapsed s ts[i] < (TimingOf X ts[i]).earliest) :
    i ∉ (ofTSt X prio s ts).readyList := by
  rw [mem_readyList]
  rintro ⟨-, h⟩
  rw [ofTSt_ready X prio s ts i hi] at h
  exact absurd h.2.1 (by omega)

end ReadyIn

/-! ## The reference order: a sort by the canonical key -/

/-- A strict order on declaration indices that is total on distinct indices. -/
structure StrictTotal (lt : Nat → Nat → Prop) : Prop where
  /-- Asymmetric. -/
  asymm : ∀ a b, lt a b → ¬ lt b a
  /-- Transitive. -/
  trans : ∀ a b c, lt a b → lt b c → lt a c
  /-- Total on distinct indices. -/
  connex : ∀ a b, a ≠ b → lt a b ∨ lt b a

/-- Sort a list by a strict order (`List.mergeSort` with the reflexive closure). -/
def sortBy (lt : Nat → Nat → Prop) [DecidableRel lt] (l : List Nat) : List Nat :=
  l.mergeSort (fun a b => !decide (lt b a))

theorem sortBy_perm (lt : Nat → Nat → Prop) [DecidableRel lt] (l : List Nat) :
    (sortBy lt l).Perm l :=
  List.mergeSort_perm _ _

/-- Sorting a list without duplicates by a strict total order sorts it strictly. -/
theorem sortBy_pairwise {lt : Nat → Nat → Prop} [DecidableRel lt] (h : StrictTotal lt)
    {l : List Nat} (hnd : l.Nodup) : (sortBy lt l).Pairwise lt := by
  have hle : (sortBy lt l).Pairwise (fun a b => (!decide (lt b a)) = true) := by
    refine List.pairwise_mergeSort (fun a b c hab hbc => ?_) (fun a b => ?_) l
    · simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hab hbc ⊢
      intro hca
      by_cases e : a = b
      · subst e; exact hbc hca
      · rcases h.connex a b e with hab' | hba
        · exact hbc (h.trans _ _ _ hca hab')
        · exact hab hba
    · by_cases hba : lt b a
      · have : ¬ lt a b := h.asymm _ _ hba
        simp [this]
      · simp [hba]
  have hnd' : (sortBy lt l).Nodup := (sortBy_perm lt l).nodup_iff.2 hnd
  refine (hle.and hnd').imp fun ⟨hab, hne⟩ => ?_
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hab
  rcases h.connex _ _ hne with h1 | h1
  · exact h1
  · exact absurd h1 hab

/-- The canonical key is a strict total order. -/
theorem schedKey_strictTotal (K : SchedKey) : StrictTotal K.lt :=
  ⟨fun _ _ h1 h2 => K.lt_asymm h1 h2, fun _ _ _ => K.lt_trans, fun _ _ => K.lt_connex⟩

/-- Strictly sorted by the canonical key implies sorted by the tie order of AC3. -/
theorem tieLt_of_key_lt (I : ReadyIn) {a b : Nat} (h : I.key.lt a b) : I.tieLt a b := by
  intro hp hc
  unfold SchedKey.lt ReadyIn.key at h
  simp only at h
  omega

/-- The general-path order: the ready transitions sorted by the canonical key, priority
descending, then stamp ascending, then declaration order ascending. -/
def exec002_sortOrder : ReadyOrder := fun I => sortBy I.key.lt I.readyList

/-- **The reference ready order** (witness model). Off the fast path, the ready transitions
sorted by the canonical key. On the fast path, the ready transitions in declaration order, as the
section says every backend does (ruling D14 (a)). -/
def refReadyOrder : ReadyOrder := fun I =>
  if I.FastPath then I.readyList else exec002_sortOrder I

#spec_witness refReadyOrder

/-! ## EXEC-002: Priority-based firing order -/

requirement EXEC_002
  id "EXEC-002"
  title "Priority-Based Firing Order"
  kind F
  scope "every executor backend, the all-immediate fast path included (ruling D14 (a))"
  source verbatim "spec/04-execution-model.md"
  covers EXEC_002.s1, EXEC_002.s2, EXEC_002.s3, EXEC_002.s4, EXEC_002.s5, EXEC_002.s6, EXEC_002.s7,
        EXEC_002.s8, EXEC_002.s12, EXEC_002.s13, EXEC_002.s11
  reading "For every input of a pass, fast path included:"
          "the order holds every ready transition exactly once and nothing else;"
          "two transitions of equal priority and equal stamp come in ascending declaration order;"
          "off the all-immediate fast path, the order is strictly sorted by priority descending, then stamp ascending, then declaration order ascending;"
          "and on the all-immediate fast path, the order is the ready transitions in ascending declaration order, whatever their stamps."
  assumes "The model is an ordering function O from the inputs of one pass (ReadyIn: the net's transitions numbered in declaration order, their priorities, their timings, their stamps and which are ready) to the list of ready transitions in the order the pass offers them for firing. Ready is the glossary term (armed, past the earliest bound, not expired); the stamp is the firing-clock reading taken by the enablement update that most recently newly armed the transition (glossary: Armed, [TIME-010]); the field ReadyIn.clock holds it. In the block these are free inputs; ReadyIn.ofTSt reads them off a timed state of the reference step (the state's stamp, glossary Ready as the ready bit), and ClashesTime shows a bridged input reached by the timed reference step. Which reading becomes a stamp is TIME-010's, not this block's. Which of the offered transitions fires is EXEC-003, not this block."
          "The four 'shall' sentences are the first three lines of the formula. The first is line 1. The fourth, on every input, is line 2. The second and third, off the fast path, are line 3 together with lines 1 and 2: since the order holds every ready transition exactly once, being strictly sorted by the key (priority descending, stamp ascending, declaration order ascending) is the same as offering, of every two ready transitions, the one of higher priority first, of equal priority the one with the earlier stamp first, and of equal priority and stamp the earlier-declared one first (EXEC_002_iff_sentences). The three items of the sort list are the same key, item by item."
          "The all-immediate fast path is accepted as stated (ruling D14 (a)). The quoted fast-path sentence is line 4: on ReadyIn.FastPath (every transition of the net Immediate, all priorities equal) the order is ReadyIn.readyList, the ready transitions in ascending declaration order, and the stamps are not read, so two ready transitions with different stamps still come in declaration order. 'Fire straight from the enablement bitmap' is read as the offer order of the ready transitions; which transitions are ready (a transition whose firing is in flight in a net that is not re-entrant included) is a free input here. Lines 1 and 2 hold on the fast path as well and there follow from line 4. Every runtime scans in ascending declaration index on the fast path: rust/libpetri-runtime/src/precompiled_backend.rs and bitmap_backend.rs (collect_ready_immediate), java/src/main/java/org/libpetri/runtime/PrecompiledNetExecutor.java (fireReadyImmediate), typescript/src/runtime/precompiled-net-executor.ts (fireReadyImmediate). A backend without the fast path that sorts by stamp on every input breaks line 4 (EXEC_002_mutant_fastOpen_killed: on exec002_Ifs, all Immediate and one priority, transition 1 armed before 0, the sort offers [1, 0] where line 4 asks [0, 1]). 'This is deliberate, and every backend takes the path under the same condition.' is the one fixed condition ReadyIn.FastPath of lines 3 and 4, which the block uses for every backend. The note of ruling D14 (a) that composition does not preserve the fast path is MOD-012's, not this block's."
          "AC1 (priority 10 before priority 5) and AC2 (equal priority on the general path, the one armed first, with the earlier stamp, fires first) are the third line; AC3 (equal priority and equal stamp, ascending declaration order) is the second line, on every input. That transitions newly armed by the enablement update of one cycle share one stamp is TIME-010's stamp rule at the grain of a cycle, deferred to Phase 2 (RefExec); in the block the stamps are free inputs, so AC3 is checked on every pair with equal stamps. EXEC_002_nonvacuous checks the test derivation (priorities 5, 10, 5, all Immediate, armed together), AC2 and AC3 on the reference order, and the fast path."
          "AC4 (every backend produces the identical ready order) follows: two ordering functions that satisfy the block agree on every input (EXEC_002_unique), off the fast path because the key is total on distinct transitions, on it by line 4. 'Stamp order is the general-path order' is line 3, and 'on the all-immediate single-priority fast path every backend fires in declaration order instead' is line 4. That the shipped backends compute the general-path order is Q evidence, cited from Sched.lean (collect_ready_general_refines) and Refinement.lean (precompiled_refines_bitmap_immediate, the immediate fragment). AC4's 'Backends MUST NOT differ in which order they use, nor in the condition that selects it.' is the one fixed condition ReadyIn.FastPath, which the block uses for every backend: a backend whose own fast-path condition is narrower or wider breaks line 3 or line 4 on every input where the two orders then differ (a narrower condition that checks only the ready transitions is killed, EXEC_002_forbids_readyFast; one that never takes the fast path, EXEC_002_mutant_fastOpen_killed)."
          "'Fires first' is read as 'is offered first in the pass's order'; with tokens to compete for, the earlier transition takes them (EXEC-003). That a pass starts its firings in this order is a Phase 2 behaviour line over the executor, not this block."
  signoff "2026-11-13 70c357c823f6665b ai"
  statement : ReadyOrder → Prop :=
    fun O => ∀ I : ReadyIn,
      (O I).Perm I.readyList ∧
      (O I).Pairwise I.tieLt ∧
      (¬ I.FastPath → (O I).Pairwise I.key.lt) ∧
      (I.FastPath → O I = I.readyList)

/- The pinned readable form of EXEC-002: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EXEC_002 : ReadyOrder → Prop :=
fun O =>
  ∀ (I : ReadyIn),
    (O I).Perm I.readyList ∧
      List.Pairwise I.tieLt (O I) ∧ (¬I.FastPath → List.Pairwise I.key.lt (O I)) ∧ (I.FastPath → O I = I.readyList)
-/
#guard_msgs in #print EXEC_002

/-! ### The order is unique off the fast path, and the reference computes it -/

/-- Any ordering function that is a permutation of the ready list strictly sorted by a strict
total order satisfies the corresponding reading. Used by the reference and the mutants. -/
theorem sortBy_spec (lt : ReadyIn → Nat → Nat → Prop) [∀ I, DecidableRel (lt I)]
    (h : ∀ I, StrictTotal (lt I)) (I : ReadyIn) :
    (sortBy (lt I) I.readyList).Perm I.readyList ∧
      (sortBy (lt I) I.readyList).Pairwise (lt I) :=
  ⟨sortBy_perm _ _, sortBy_pairwise (h I) I.readyList_nodup⟩

/-- The general sort meets all three lines on every input. -/
theorem exec002_sortOrder_spec (I : ReadyIn) :
    (exec002_sortOrder I).Perm I.readyList ∧ (exec002_sortOrder I).Pairwise I.tieLt ∧
      (exec002_sortOrder I).Pairwise I.key.lt := by
  obtain ⟨hp, hs⟩ := sortBy_spec (fun I => I.key.lt) (fun I => schedKey_strictTotal I.key) I
  exact ⟨hp, hs.imp (tieLt_of_key_lt I), hs⟩

/-- The declaration order meets the first two lines on every input. -/
theorem exec002_readyList_spec (I : ReadyIn) :
    I.readyList.Perm I.readyList ∧ I.readyList.Pairwise I.tieLt :=
  ⟨List.Perm.refl _, I.readyList_sorted.imp fun h _ _ => h⟩

/-- ✓ The reference ready order satisfies EXEC-002. -/
@[evidence holds EXEC_002]
theorem EXEC_002_reference : EXEC_002 refReadyOrder := fun I => by
  by_cases h : I.FastPath
  · rw [show refReadyOrder I = I.readyList from if_pos h]
    exact ⟨(exec002_readyList_spec I).1, (exec002_readyList_spec I).2, fun hn => absurd h hn,
      fun _ => rfl⟩
  · rw [show refReadyOrder I = exec002_sortOrder I from if_neg h]
    obtain ⟨h1, h2, h3⟩ := exec002_sortOrder_spec I
    exact ⟨h1, h2, fun _ => h3, fun hf => absurd hf h⟩

/-- AC4: two ordering functions that satisfy EXEC-002 compute the same order on every input,
off the fast path by the canonical sort, on it by declaration order. -/
@[evidence cites "EXEC-002" "AC4: two ready orders that satisfy the block are equal on every input: off the all-immediate fast path both are the ready set strictly sorted by priority DESC, stamp ASC, declaration order ASC, on it both are the ready set in declaration order (ruling D14 (a))"]
theorem EXEC_002_unique {O₁ O₂ : ReadyOrder} (h₁ : EXEC_002 O₁) (h₂ : EXEC_002 O₂)
    (I : ReadyIn) : O₁ I = O₂ I := by
  by_cases hI : I.FastPath
  · rw [(h₁ I).2.2.2 hI, (h₂ I).2.2.2 hI]
  · exact eq_of_perm_of_sorted I.key ((h₁ I).2.2.1 hI) ((h₂ I).2.2.1 hI)
      ((h₁ I).1.trans (h₂ I).1.symm)

/-- An ordering function that satisfies EXEC-002 is the reference order. -/
theorem EXEC_002_eq_ref {O : ReadyOrder} (h : EXEC_002 O) (I : ReadyIn) :
    O I = refReadyOrder I :=
  EXEC_002_unique h EXEC_002_reference I

/-- A list that is a permutation of the ready list and strictly sorted by the key is the order
every ordering function satisfying EXEC-002 computes off the fast path. -/
theorem EXEC_002_forced {O : ReadyOrder} (h : EXEC_002 O) {I : ReadyIn} (hI : ¬ I.FastPath)
    {l : List Nat} (hp : l.Perm I.readyList) (hs : l.Pairwise I.key.lt) : O I = l :=
  eq_of_perm_of_sorted I.key ((h I).2.2.1 hI) hs ((h I).1.trans hp.symm)

/-! ### The four 'shall' sentences, pair by pair, and the fast path -/

/-- In a strictly sorted list, `a` comes before `b` when `a` is below `b`. -/
theorem sublist_pair_of_pairwise {lt : Nat → Nat → Prop} (hasym : ∀ a b, lt a b → ¬ lt b a)
    {a b : Nat} : ∀ {l : List Nat}, l.Pairwise lt → a ∈ l → b ∈ l → lt a b → [a, b].Sublist l
  | [], _, ha, _, _ => absurd ha List.not_mem_nil
  | x :: t, hp, ha, hb, hab => by
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.1 ha with rfl | ha'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd hab (hasym _ _ hab)
      · exact List.Sublist.cons_cons _ (List.singleton_sublist.2 hb')
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd (hp.1 a ha') (hasym _ _ hab)
      · exact List.Sublist.cons _ (sublist_pair_of_pairwise hasym hp.2 ha' hb' hab)

/-- In a list sorted by `r`, two distinct members `a`, `b` with `¬ r b a` come as `a` before
`b`. -/
theorem sublist_pair_of_pairwise_not {r : Nat → Nat → Prop} {a b : Nat} (hne : a ≠ b)
    (hba : ¬ r b a) : ∀ {l : List Nat}, l.Pairwise r → a ∈ l → b ∈ l → [a, b].Sublist l
  | [], _, ha, _ => absurd ha List.not_mem_nil
  | x :: t, hp, ha, hb => by
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.1 ha with rfl | ha'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd rfl hne
      · exact List.Sublist.cons_cons _ (List.singleton_sublist.2 hb')
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd (hp.1 a ha') hba
      · exact List.Sublist.cons _ (sublist_pair_of_pairwise_not hne hba hp.2 ha' hb')

/-- In a list without duplicates, two members do not come in both orders. -/
theorem not_both_pairs {x y : Nat} : ∀ {l : List Nat}, l.Nodup →
    [x, y].Sublist l → [y, x].Sublist l → False
  | [], _, h, _ => by simp at h
  | z :: t, hnd, h1, h2 => by
    rw [List.nodup_cons] at hnd
    rw [List.sublist_cons_iff] at h1 h2
    rcases h1 with h1 | ⟨r, e1, h1⟩ <;> rcases h2 with h2 | ⟨r', e2, h2⟩
    · exact not_both_pairs hnd.2 h1 h2
    · cases e2
      exact hnd.1 (h1.subset (by simp))
    · cases e1
      exact hnd.1 (h2.subset (by simp))
    · cases e1; cases e2
      exact hnd.1 (h1.subset (by simp))

/-- The four 'shall' sentences of EXEC-002, each as a statement about pairs of ready
transitions, and the fast-path sentence: the order holds every ready transition exactly once and
nothing else; off the fast path, of two ready transitions the one of higher priority comes
first; off the fast path, of two ready transitions of equal priority the one with the earlier
stamp comes first; of two ready transitions of equal priority and equal stamp the
earlier-declared one comes first; and on the fast path the order is the declaration order. -/
def EXEC_002_sentences (O : ReadyOrder) : Prop :=
  ∀ I : ReadyIn,
    (O I).Perm I.readyList ∧
    (¬ I.FastPath → ∀ a ∈ I.readyList, ∀ b ∈ I.readyList,
      I.prio b < I.prio a → [a, b].Sublist (O I)) ∧
    (¬ I.FastPath → ∀ a ∈ I.readyList, ∀ b ∈ I.readyList,
      I.prio a = I.prio b → I.clock a < I.clock b → [a, b].Sublist (O I)) ∧
    (∀ a ∈ I.readyList, ∀ b ∈ I.readyList,
      I.prio a = I.prio b → I.clock a = I.clock b → a < b → [a, b].Sublist (O I)) ∧
    (I.FastPath → O I = I.readyList)

/-- The block is the four 'shall' sentences and the fast-path sentence: an ordering function
satisfies EXEC-002 exactly when it satisfies each sentence read pair by pair. The block's
sortedness by the key is the second and third sentences together with the fourth, because the
order holds every ready transition exactly once. -/
theorem EXEC_002_iff_sentences (O : ReadyOrder) : EXEC_002 O ↔ EXEC_002_sentences O := by
  constructor
  · intro h I
    obtain ⟨hp, ht, hk, hf⟩ := h I
    have mem : ∀ {a}, a ∈ I.readyList → a ∈ O I := fun ha => hp.mem_iff.2 ha
    have asymm : ∀ a b, I.key.lt a b → ¬ I.key.lt b a := fun _ _ h1 h2 => I.key.lt_asymm h1 h2
    refine ⟨hp, fun hI a ha b hb hlt => ?_, fun hI a ha b hb he hc => ?_,
      fun a ha b hb he hc hab => ?_, hf⟩
    · exact sublist_pair_of_pairwise asymm (hk hI) (mem ha) (mem hb) (Or.inl hlt)
    · exact sublist_pair_of_pairwise asymm (hk hI) (mem ha) (mem hb) (Or.inr ⟨he, Or.inl hc⟩)
    · exact sublist_pair_of_pairwise_not (Nat.ne_of_lt hab)
        (fun h' => absurd (h' he.symm hc.symm) (Nat.lt_asymm hab)) ht (mem ha) (mem hb)
  · intro h I
    obtain ⟨hp, h2, h3, h4, hf⟩ := h I
    have hnd : (O I).Nodup := hp.nodup_iff.2 I.readyList_nodup
    have mem : ∀ {a}, a ∈ O I → a ∈ I.readyList := fun ha => hp.mem_iff.1 ha
    have ends : ∀ {x y}, [x, y].Sublist (O I) → x ∈ I.readyList ∧ y ∈ I.readyList ∧ x ≠ y :=
      fun hs => ⟨mem (hs.subset (by simp)), mem (hs.subset (by simp)),
        fun e => by subst e; exact List.nodup_iff_sublist.1 hnd _ hs⟩
    refine ⟨hp, List.pairwise_iff_forall_sublist.2 fun {x y} hs => ?_,
      fun hI => List.pairwise_iff_forall_sublist.2 fun {x y} hs => ?_, hf⟩
    · obtain ⟨hx, hy, hne⟩ := ends hs
      intro he hc
      rcases Nat.lt_or_gt_of_ne hne with hxy | hyx
      · exact hxy
      · exact (not_both_pairs hnd hs (h4 y hy x hx he.symm hc.symm hyx)).elim
    · obtain ⟨hx, hy, hne⟩ := ends hs
      rcases I.key.lt_connex hne with hxy | hyx
      · exact hxy
      · exfalso
        refine not_both_pairs hnd hs ?_
        unfold SchedKey.lt ReadyIn.key at hyx
        simp only at hyx
        rcases hyx with hlt | ⟨he, hlt | ⟨hc, hlt⟩⟩
        · exact h2 hI y hy x hx hlt
        · exact h3 hI y hy x hx he hlt
        · exact h4 y hy x hx he hc hlt

/-- ✓ The reference ready order satisfies the four 'shall' sentences. -/
theorem EXEC_002_sentences_reference : EXEC_002_sentences refReadyOrder :=
  (EXEC_002_iff_sentences _).1 EXEC_002_reference

/-! ### Examples -/

/-- AC2 and the AC4 test derivation: two transitions of priority `0`, both `Delayed` (so the net
takes the general path), both ready; transition `1` was armed at `3`, transition `0` later at
`5`, so declaration order is opposite to arming order (`Ka` of `RetrodictExec.lean`). -/
def exec002_Ia : ReadyIn :=
  { n := 2, prio := Ka.prio, timing := fun _ => .delayed 1, clock := Ka.clock,
    ready := fun _ => true }

/-- The test derivation: priorities 5, 10, 5, all `Immediate`, all armed at `0` (AC1 and
AC3). Two priority levels put the net on the general path. -/
def exec002_I3 : ReadyIn :=
  { n := 3, prio := fun t => if t = 1 then 10 else 5, timing := fun _ => .immediate,
    clock := fun _ => 0, ready := fun _ => true }

/-- A fast-path input: three `Immediate` transitions of priority `0`, all armed at `0`;
transition `1` is not ready. -/
def exec002_Ifp : ReadyIn :=
  { n := 3, prio := fun _ => 0, timing := fun _ => .immediate, clock := fun _ => 0,
    ready := fun t => t != 1 }

theorem exec002_Ia_general : ¬ exec002_Ia.FastPath := by decide

theorem exec002_I3_general : ¬ exec002_I3.FastPath := by decide

theorem exec002_Ifp_fast : exec002_Ifp.FastPath := by decide

/-- A fast-path input whose stamps differ: two `Immediate` transitions of priority `0`, both
ready; transition `1` was armed at `0` and transition `0` later at `3` (it was held across cycles
while in flight), so declaration order is opposite to arming order. -/
def exec002_Ifs : ReadyIn :=
  { n := 2, prio := fun _ => 0, timing := fun _ => .immediate,
    clock := fun t => if t = 0 then 3 else 0, ready := fun _ => true }

theorem exec002_Ifs_fast : exec002_Ifs.FastPath := by decide

/-- The order EXEC-002 forces on `exec002_Ia`: transition `1`, armed first, then `0`. -/
theorem exec002_Ia_forced {O : ReadyOrder} (h : EXEC_002 O) : O exec002_Ia = [1, 0] :=
  EXEC_002_forced h exec002_Ia_general (by decide) tid_order_diverges.2

/-- The order EXEC-002 forces on `exec002_I3`: P10 first, then the two P5 transitions in
declaration order (equal stamp, AC3). -/
theorem exec002_I3_forced {O : ReadyOrder} (h : EXEC_002 O) : O exec002_I3 = [1, 0, 2] :=
  EXEC_002_forced h exec002_I3_general (by decide) (by decide)

/-- The order EXEC-002 forces on the fast-path input `exec002_Ifp`: the two ready transitions
`0` and `2`, tied on priority and stamp, in ascending declaration order (already by the first
two lines). -/
theorem exec002_Ifp_forced {O : ReadyOrder} (h : EXEC_002 O) : O exec002_Ifp = [0, 2] := by
  obtain ⟨hp, ht, -⟩ := h exec002_Ifp
  have hp' : (O exec002_Ifp).Perm [0, 2] := hp.trans (by decide)
  have hlen : (O exec002_Ifp).length = 2 := by rw [hp'.length_eq]; rfl
  match e : O exec002_Ifp, hlen with
  | [x, y], _ =>
    rw [e] at hp' ht
    have hx : x = 0 ∨ x = 2 := by
      have := hp'.mem_iff.1 (List.mem_cons_self ..); simpa using this
    have hy : y = 0 ∨ y = 2 := by
      have := hp'.mem_iff.1 (List.mem_cons_of_mem _ (List.mem_cons_self ..)); simpa using this
    have hxy : x < y := by
      have := List.rel_of_pairwise_cons ht (List.mem_cons_self ..)
      exact this rfl rfl
    have hnd := hp'.nodup_iff.2 (by decide)
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> first | rfl | omega

/-- The order EXEC-002 forces on the fast-path input `exec002_Ifs` (line 4): declaration order
`[0, 1]`, though `1` was armed first. -/
theorem exec002_Ifs_forced {O : ReadyOrder} (h : EXEC_002 O) : O exec002_Ifs = [0, 1] :=
  ((h exec002_Ifs).2.2.2 exec002_Ifs_fast).trans (by decide)

/-- The general sort on `exec002_Ifs` offers `1`, armed first, before `0`. -/
theorem exec002_Ifs_sort : exec002_sortOrder exec002_Ifs = [1, 0] :=
  eq_of_perm_of_sorted exec002_Ifs.key
    (sortBy_pairwise (schedKey_strictTotal _) exec002_Ifs.readyList_nodup)
    (by decide) ((sortBy_perm _ _).trans (by decide))

/-! ### A backend that ignores priority -/

/-- The ready transitions in declaration order: the bitmap scan, without the sort. -/
def exec002_scanOrder : ReadyOrder := fun I => I.readyList

/-- ✗ The declaration-order scan violates EXEC-002 (AC1): in the test derivation the priority-5
transition `0` comes before the priority-10 transition `1`. -/
@[evidence forbids EXEC_002]
theorem EXEC_002_forbids_scan : ¬ EXEC_002 exec002_scanOrder := by
  intro h
  have := exec002_I3_forced h
  revert this
  decide

/-! ### Mutant: unconstrained on the fast path -/

/-- The fast-path order reversed: the reference off the fast path, descending declaration order
on it. -/
def exec002_revFast : ReadyOrder := fun I =>
  if I.FastPath then I.readyList.reverse else exec002_sortOrder I

/-- Mutant reading of EXEC-002 that leaves the fast path wholly unconstrained (the general path
only, the first form of this block). -/
def EXEC_002_mutant_generalOnly (O : ReadyOrder) : Prop :=
  ∀ I : ReadyIn, ¬ I.FastPath → (O I).Perm I.readyList ∧ (O I).Pairwise I.key.lt

/-- The reversed fast path kills the mutant: it satisfies the general-path-only reading, but on
the fast-path input `exec002_Ifp` it offers `2` before `0`, though that tie of priority and
stamp breaks by ascending declaration order (AC3, line 2). -/
@[evidence mutant EXEC_002]
theorem EXEC_002_mutant_generalOnly_killed :
    EXEC_002_mutant_generalOnly exec002_revFast ∧ ¬ EXEC_002 exec002_revFast := by
  refine ⟨fun I hI => ?_, fun h => ?_⟩
  · simp only [exec002_revFast, if_neg hI]
    exact ⟨(exec002_sortOrder_spec I).1, (exec002_sortOrder_spec I).2.2⟩
  · have := exec002_Ifp_forced h
    simp only [exec002_revFast, if_pos exec002_Ifp_fast] at this
    revert this; decide

/-- On the fast path, every transition of the net, ready or not. -/
def exec002_allFast : ReadyOrder := fun I =>
  if I.FastPath then List.range I.n else exec002_sortOrder I

/-- ✗ An order that offers a transition that is not ready on the fast path violates EXEC-002:
on `exec002_Ifp` it offers transition `1`. -/
@[evidence forbids EXEC_002]
theorem EXEC_002_forbids_allFast : ¬ EXEC_002 exec002_allFast := by
  intro h
  have := exec002_Ifp_forced h
  simp only [exec002_allFast, if_pos exec002_Ifp_fast] at this
  revert this; decide

/-- A fast-path condition that looks only at the ready transitions (all of them `Immediate` and
of one priority), not at every transition of the net: declaration order then, else the sort. -/
def exec002_readyFast : ReadyOrder := fun I =>
  if ∀ a ∈ I.readyList, ∀ b ∈ I.readyList, I.timing a = .immediate ∧ I.prio a = I.prio b
  then I.readyList else exec002_sortOrder I

/-- ✗ The narrower condition violates EXEC-002 (AC4, the condition that selects the order): on a
net with a `Delayed` transition that is not ready, the two ready `Immediate` transitions of one
priority come in declaration order, though `1` was armed first and the net is on the general
path. -/
@[evidence forbids EXEC_002]
theorem EXEC_002_forbids_readyFast : ¬ EXEC_002 exec002_readyFast := by
  intro h
  let I : ReadyIn :=
    { n := 3, prio := fun _ => 0, timing := fun t => if t = 2 then .delayed 5 else .immediate,
      clock := fun t => if t = 0 then 5 else 3, ready := fun t => t != 2 }
  have hI : ¬ I.FastPath := by decide
  have e2 : exec002_readyFast I = [1, 0] := EXEC_002_forced h hI (by decide) (by decide)
  have e1 : exec002_readyFast I = [0, 1] := by
    simp only [exec002_readyFast]; decide
  rw [e1] at e2; exact absurd e2 (by decide)

/-! ### Mutant: the fast path open beyond the first two lines -/

/-- Mutant reading of EXEC-002 without line 4: on the fast path only the first two lines hold,
so the order of two ready transitions with different stamps is left open (the form of this
block before ruling D14 (a)). -/
def EXEC_002_mutant_fastOpen (O : ReadyOrder) : Prop :=
  ∀ I : ReadyIn,
    (O I).Perm I.readyList ∧
    (O I).Pairwise I.tieLt ∧
    (¬ I.FastPath → (O I).Pairwise I.key.lt)

/-- The general sort on every input (a backend without the fast path) kills the mutant: it
satisfies the mutant reading, but not EXEC-002. On the fast-path input `exec002_Ifs` it offers
`[1, 0]` by stamp, where the section ('do not read the enablement timestamp at all') asks the
declaration order `[0, 1]`. -/
@[evidence mutant EXEC_002]
theorem EXEC_002_mutant_fastOpen_killed :
    EXEC_002_mutant_fastOpen exec002_sortOrder ∧ ¬ EXEC_002 exec002_sortOrder := by
  refine ⟨fun I => ⟨(exec002_sortOrder_spec I).1, (exec002_sortOrder_spec I).2.1,
    fun _ => (exec002_sortOrder_spec I).2.2⟩, fun h => ?_⟩
  have := exec002_Ifs_forced h
  rw [exec002_Ifs_sort] at this
  exact absurd this (by decide)

/-! ### Mutant: the pre-fix drain in declaration order within a priority level -/

/-- The key of the pre-fix per-level drain: priority descending, then declaration order
ascending; the stamp is not read. -/
def exec002_tidKey (I : ReadyIn) : SchedKey := { prio := I.prio, clock := fun _ => 0 }

/-- The pre-fix order (`tid_order_diverges`): each priority level drained in declaration order. -/
def exec002_tidOrder : ReadyOrder := fun I => sortBy (exec002_tidKey I).lt I.readyList

/-- Mutant reading of EXEC-002 that orders equal priorities by declaration order, not by
stamp (AC2 dropped). -/
def EXEC_002_mutant_tid (O : ReadyOrder) : Prop :=
  ∀ I : ReadyIn, ¬ I.FastPath →
    (O I).Perm I.readyList ∧ (O I).Pairwise (exec002_tidKey I).lt

/-- The pre-fix drain kills the mutant: it satisfies the mutant reading, but not EXEC-002. On
`exec002_Ia` it offers `0` before `1`, though `1` was armed first. -/
@[evidence mutant EXEC_002]
theorem EXEC_002_mutant_tid_killed :
    EXEC_002_mutant_tid exec002_tidOrder ∧ ¬ EXEC_002 exec002_tidOrder := by
  refine ⟨fun I _ => sortBy_spec (fun I => (exec002_tidKey I).lt)
    (fun I => schedKey_strictTotal _) I, fun h => ?_⟩
  have e : exec002_tidOrder exec002_Ia = [0, 1] :=
    eq_of_perm_of_sorted (exec002_tidKey exec002_Ia)
      (sortBy_pairwise (schedKey_strictTotal _) exec002_Ia.readyList_nodup)
      (by decide) ((sortBy_perm _ _).trans (by decide))
  have := exec002_Ia_forced h
  rw [e] at this
  exact absurd this (by decide)

/-! ### Mutant: ties broken by descending declaration order -/

/-- The key that breaks a tie of priority and stamp by descending declaration order. -/
def exec002_descLt (I : ReadyIn) (a b : Nat) : Prop :=
  I.prio b < I.prio a ∨
    (I.prio a = I.prio b ∧ (I.clock a < I.clock b ∨ (I.clock a = I.clock b ∧ b < a)))

instance (I : ReadyIn) : DecidableRel (exec002_descLt I) := fun a b => by
  unfold exec002_descLt; infer_instance

theorem exec002_descLt_strictTotal (I : ReadyIn) : StrictTotal (exec002_descLt I) := by
  refine ⟨fun a b h1 h2 => ?_, fun a b c h1 h2 => ?_, fun a b hne => ?_⟩ <;>
    unfold exec002_descLt at *
  · rcases h1 with h1 | ⟨e1, h1 | ⟨c1, h1⟩⟩ <;>
      rcases h2 with h2 | ⟨e2, h2 | ⟨c2, h2⟩⟩ <;> omega
  · rcases h1 with h1 | ⟨e1, h1 | ⟨c1, h1⟩⟩ <;>
      rcases h2 with h2 | ⟨e2, h2 | ⟨c2, h2⟩⟩ <;>
      first
        | exact Or.inl (by omega)
        | exact Or.inr ⟨by omega, Or.inl (by omega)⟩
        | exact Or.inr ⟨by omega, Or.inr ⟨by omega, by omega⟩⟩
  · rcases Int.lt_trichotomy (I.prio a) (I.prio b) with h | h | h
    · right; left; omega
    · rcases Nat.lt_trichotomy (I.clock a) (I.clock b) with h' | h' | h'
      · left; right; exact ⟨h, Or.inl h'⟩
      · rcases Nat.lt_trichotomy a b with h'' | h'' | h''
        · right; right; exact ⟨h.symm, Or.inr ⟨h'.symm, h''⟩⟩
        · exact absurd h'' hne
        · left; right; exact ⟨h, Or.inr ⟨h', h''⟩⟩
      · right; right; exact ⟨h.symm, Or.inl h'⟩
    · left; left; omega

/-- The order that breaks ties by descending declaration order. -/
def exec002_descOrder : ReadyOrder := fun I => sortBy (exec002_descLt I) I.readyList

/-- Mutant reading of EXEC-002 with the tie of AC3 broken by descending declaration order. -/
def EXEC_002_mutant_tieDesc (O : ReadyOrder) : Prop :=
  ∀ I : ReadyIn, ¬ I.FastPath → (O I).Perm I.readyList ∧ (O I).Pairwise (exec002_descLt I)

/-- The descending tie-break kills the mutant: it satisfies the mutant reading, but not
EXEC-002. In the test derivation the two priority-5 transitions, armed at the same reading,
come out as `2` before `0`. -/
@[evidence mutant EXEC_002]
theorem EXEC_002_mutant_tieDesc_killed :
    EXEC_002_mutant_tieDesc exec002_descOrder ∧ ¬ EXEC_002 exec002_descOrder := by
  refine ⟨fun I _ => sortBy_spec exec002_descLt exec002_descLt_strictTotal I, fun h => ?_⟩
  have e : exec002_descOrder exec002_I3 = [1, 2, 0] :=
    List.Perm.eq_of_pairwise
      (fun a b _ _ hab hba => ((exec002_descLt_strictTotal exec002_I3).asymm a b hab hba).elim)
      (sortBy_pairwise (exec002_descLt_strictTotal _) exec002_I3.readyList_nodup)
      (by decide) ((sortBy_perm _ _).trans (by decide))
  have := exec002_I3_forced h
  rw [e] at this
  exact absurd this (by decide)

/-! ### A LIFO order -/

/-- Enablement time descending within a priority level (LIFO): the plausible AC2 bug. -/
def exec002_lifoKey (I : ReadyIn) : SchedKey :=
  { prio := I.prio, clock := fun t => 1000 - I.clock t }

/-- The LIFO order. -/
def exec002_lifoOrder : ReadyOrder := fun I => sortBy (exec002_lifoKey I).lt I.readyList

/-- ✗ The LIFO order violates EXEC-002 (AC2): on `exec002_Ia` it offers `0`, armed last,
before `1`, armed first. -/
@[evidence forbids EXEC_002]
theorem EXEC_002_forbids_lifo : ¬ EXEC_002 exec002_lifoOrder := by
  intro h
  have e : exec002_lifoOrder exec002_Ia = [0, 1] :=
    eq_of_perm_of_sorted (exec002_lifoKey exec002_Ia)
      (sortBy_pairwise (schedKey_strictTotal _) exec002_Ia.readyList_nodup)
      (by decide) ((sortBy_perm _ _).trans (by decide))
  have := exec002_Ia_forced h
  rw [e] at this
  exact absurd this (by decide)

/-! ### Every line exercised -/

/-- Every line of EXEC-002 is exercised by the reference order. AC2 and the AC4 test
derivation: two equal-priority transitions armed in the order opposite to their declaration
come out as `[1, 0]` (third line). The test derivation of AC1 and AC3: priorities 5, 10, 5, all
`Immediate`, armed together, come out as P10, then the two P5 in declaration order,
`[1, 0, 2]` (second and third lines). A transition that is not ready is left out (first line),
off the fast path and on it; on the fast path the two ready transitions, tied, come out in
declaration order (first and second lines), and two ready transitions whose stamps differ come
out in declaration order too, the later-armed `0` first (fourth line). -/
@[evidence nonvacuous EXEC_002]
theorem EXEC_002_nonvacuous :
    ¬ exec002_Ia.FastPath ∧ refReadyOrder exec002_Ia = [1, 0] ∧
      ¬ exec002_I3.FastPath ∧ refReadyOrder exec002_I3 = [1, 0, 2] ∧
      ¬ ({ exec002_I3 with ready := fun t => t != 1 } : ReadyIn).FastPath ∧
      refReadyOrder { exec002_I3 with ready := fun t => t != 1 } = [0, 2] ∧
      exec002_Ifp.FastPath ∧ exec002_Ifp.ready 1 = false ∧
      refReadyOrder exec002_Ifp = [0, 2] ∧
      exec002_Ifs.FastPath ∧ exec002_Ifs.clock 1 < exec002_Ifs.clock 0 ∧
      refReadyOrder exec002_Ifs = [0, 1] := by
  refine ⟨exec002_Ia_general, exec002_Ia_forced EXEC_002_reference, exec002_I3_general,
    exec002_I3_forced EXEC_002_reference, by decide,
    EXEC_002_forced EXEC_002_reference (by decide) (by decide) (by decide),
    exec002_Ifp_fast, rfl, exec002_Ifp_forced EXEC_002_reference, exec002_Ifs_fast, by decide,
    exec002_Ifs_forced EXEC_002_reference⟩

end Libpetri.Spec
