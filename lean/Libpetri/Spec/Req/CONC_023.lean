import Libpetri.Spec.Req.EXEC_002

set_option linter.missingDocs true

/-!
# CONC-023: Priority-partitioned ready queues (`spec/05-concurrency.md`)

The precompiled executor keeps one ready queue per priority level and drains the levels from the
highest priority to the lowest. What a pass can observe of that structure is the order in which
the ready transitions are offered: grouped by priority level, the groups in descending order of
priority, and within one level by stamp, then by declaration order (AC4). The requirement is a
predicate over the abstract ordering function `O : ReadyOrder` of [EXEC-002] (`ReadyIn` to the
list of ready transitions, as declaration indices), so that it can be checked against the
reference order `refReadyOrder`, against an order that offers the highest level only, against
fast-path orders that drop, add or reorder transitions, and against two mutant readings: each
level drained in declaration order (the pre-fix backend that AC4 calls "NOT sufficient") and the
levels drained from the lowest priority up.

The fast path is exempt from the queues (AC4), not from the order: on it the block asks what
both outcomes of the open ruling D14 share, every ready transition exactly once and ties of
priority and stamp in declaration order (`CONC_023_D14_neutral`). The block is then equivalent
to [EXEC-002] (`CONC_023_iff_EXEC_002`): the per-level drain is the canonical sort. It adds no
constraint on the order; it states the queue structure a reader of CONC-023 expects, ties the
two formulas together so that neither can drift alone, and links them to the backend refinement
theorem `collect_ready_general_refines` (`Sched.lean`), which already cites CONC-023.
-/

namespace Libpetri.Spec

open Libpetri

/-! ## CONC-023: Priority-partitioned ready queues -/

requirement CONC_023
  id "CONC-023"
  title "Priority-Partitioned Ready Queues"
  kind F
  scope "the ready order of the precompiled executor, and by AC4 of every backend; on the all-immediate fast path only what both outcomes of ruling D14 share"
  source verbatim "spec/05-concurrency.md"
  quote "*Where* the net does not take the all-immediate fast path, the ready order *shall* be the ready transitions grouped by priority level, at most one group per priority level, with the groups in descending order of priority."
        "*Where* the net does not take the all-immediate fast path, the ready order *shall* offer the ready transitions of one priority level in ascending order of stamp."
        "The ready order *shall* hold every ready transition exactly once and no other transition, on the all-immediate fast path as well."
        "The ready order *shall* offer ready transitions of one priority level with equal stamps in ascending declaration order, also when they were armed in different cycles and on the all-immediate fast path."
        "Within the same priority, FIFO ordering by enablement time is preserved."
        "Feeding a level's queue in declaration order is NOT sufficient: transitions enabled in different cycles must drain in enablement order even when it disagrees with declaration order, and equal enablement timestamps break by ascending declaration order — the identical order [EXEC-002] AC3/AC4 requires of every backend."
  reading "For every input of a pass, fast path included:"
          "the order holds every ready transition exactly once and no other transition;"
          "two transitions of equal priority and equal stamp come in ascending declaration order;"
          "and off the all-immediate fast path there are groups (a priority and a list of transitions each) such that the order is the groups drained one after the other, the groups' priorities are strictly descending, so each priority level has at most one group, and every transition of a group has the group's priority;"
          "and within each group a transition with an earlier stamp comes first, and of two with equal stamps the earlier-declared one comes first."
  assumes "The model is EXEC-002's ordering function O from the inputs of one pass (ReadyIn: the transitions numbered in declaration order, their priorities, timings and stamps, and which are ready) to the list of ready transitions in the order the pass offers them for firing. A group of the formula is the content of one priority level's ready queue when the pass drains it; the formula does not model the queues, only the order they produce. Ready and stamp are the glossary terms (Armed, Ready, [TIME-010]); which transitions are ready and which reading becomes a stamp are EXEC-002's and TIME-010's inputs, free here."
          "The first quoted sentence is line 3 ('the ready transitions grouped by priority level' together with line 1: each ready transition in exactly one group, nothing else; 'at most one group per priority level, with the groups in descending order of priority' is the strictly descending group priorities). Levels that hold no ready transition need no group. It restates the body sentence 'Transition selection scans priority levels in descending order and picks the first non-empty queue, giving O(L) selection where L is the number of distinct priority levels (typically 1–3).' as far as the order of one pass shows it: 'picks the first non-empty queue' is read as the selection of the next transition, repeated until every queue is drained, not as a pass that offers the highest level only (conc023_topOnly is forbidden by line 1). Re-selection after a firing of the same pass has changed which transitions are ready is the executor's pass model (EXEC-001, EXEC-003), a Phase 2 behaviour line over RefExec, not this block; the test derivation's 'fire in correct priority order' is likewise checked as offer order. The selection cost O(L) is not encoded."
          "The second quoted sentence is line 4, which states it inside one group together with line 2 (equal priority holds inside a group), so that the groups are Sched.lean's LevelBlocks. The third quoted sentence is line 1 and the fourth is line 2, both on every input. 'Also when they were armed in different cycles': the interface has no cycle, the stamp is all a pass reads of the arming, and the firing clock's readings 'never decrease and may repeat' (glossary Firing clock, GlossaryTime ClockReading), so two transitions armed in different cycles can share a stamp, and line 2 then gives declaration order (conc023_Irep_forced)."
          "AC4's first two sentences (quoted) are line 4 with line 2: within a level, stamp ascending, then declaration order ascending. 'Enablement time' and 'enablement timestamp' are the stamp, and 'enablement order' is stamp order. 'Transitions enabled in different cycles must drain in enablement order even when it disagrees with declaration order' is line 4 on two stamps that differ; on two stamps that are equal although the cycles differ, the clause 'equal enablement timestamps break by ascending declaration order' governs, as the fourth quoted sentence says. Rewording AC4's 'transitions enabled in different cycles' to 'transitions with different stamps' is an editorial edit that waits for the open ruling D20. 'Feeding a level's queue in declaration order is NOT sufficient' is the mutant exec002_tidOrder (each level in declaration order), killed by line 4 (CONC_023_mutant_tid_killed). 'The identical order [EXEC-002] AC3/AC4 requires of every backend' is CONC_023_iff_EXEC_002: the block holds exactly when EXEC-002 holds."
          "AC4's third sentence, 'The all-immediate single-priority fast path is exempt: it bypasses the ready queues and fires in declaration order, which [EXEC-002] AC4 requires of every backend alike.', is encoded by the premise 'not the all-immediate fast path' on lines 3 and 4 (ReadyIn.FastPath, EXEC-002's condition, which is the condition all three runtimes test), and by lines 1 and 2 on the fast path. Which order the fast path uses when stamps differ is EXEC-002's subject and the open ruling D14's: both outcomes, declaration order and the general sort, satisfy lines 1 and 2 (CONC_023_D14_neutral), and a fast path that offers only the first ready transition, offers transitions that are not ready, or reverses a tie is killed (CONC_023_mutant_generalOnly_killed, CONC_023_forbids_allFast, CONC_023_forbids_revFast)."
          "AC1 (distinct priority levels precomputed and sorted descending) is a property of the precompiled program's data (the priority-level array built at compile time), kind Q, inspected in the runtimes; its observable consequence is line 3, whose strictly descending group priorities are the sorted distinct levels that hold a ready transition. The body sentence 'Distinct priority values are sorted descending at compile time.' is the same as AC1. 'Each transition maps to a priority index for O(1) ready-queue insertion.' is data layout and cost, kind Q, not encoded."
          "AC2 (each priority level has a separate FIFO queue) and AC3 (selection is O(L) in the number of distinct priority levels), and the body sentence 'Each priority level has its own FIFO queue.', are structure and cost, not encoded. As written they disagree with AC4 and with the runtimes (clash conc-b#6): a FIFO queue fed from the enablement bitmap gives declaration order, which AC4 calls not sufficient, so Rust and Java sort each level's queue by stamp and declaration order on every pass and TypeScript sorts one buffer. Their rewording waits for the open ruling D20 and is out of this block; lines 2 and 4 state the order the queues must deliver whatever their structure, so until D20 the quoted sentences are the binding ones."
          "The test derivation (three priority levels; priority order across levels, FIFO within each level) is checked by CONC_023_nonvacuous on conc023_I5: priorities 3, 2 and 1, with two transitions of the lowest level armed in the order opposite to their declaration and two with equal stamps."
          "Form: the quoted sentences use 'shall' inside a SHOULD requirement, as IO-016 and TIME-015 do. The SHOULD is the queue structure; the order the sentences state is required of every backend by EXEC-002 (MUST), so 'shall' is true whether or not a backend keeps per-level queues."
          "Equivalence: line 1 to line 4 together are the same as EXEC-002's three lines (CONC_023_iff_EXEC_002; off the fast path, the order is a permutation of the ready transitions strictly sorted by EXEC-002's canonical key, the hard direction being conc023_blocks_of_sorted). That the precompiled backends compute the drain is Q evidence: collect_ready_general_refines (Sched.lean) shows that a drain of level blocks of the ready set equals the reference's sort, and precompiled_refines_bitmap_immediate (Refinement.lean) covers the immediate fragment."
  signoff "pending"
  statement : ReadyOrder → Prop :=
    fun O => ∀ I : ReadyIn,
      ((O I).Perm I.readyList ∧
        (O I).Pairwise (fun a c => I.prio a = I.prio c → I.clock a = I.clock c → a < c)) ∧
      (¬ I.FastPath → ∃ blocks : List (Int × List Nat),
        O I = blocks.flatMap (·.2) ∧
        ((blocks.map (·.1)).Pairwise (· > ·) ∧ ∀ b ∈ blocks, ∀ a ∈ b.2, I.prio a = b.1) ∧
        (∀ b ∈ blocks, b.2.Pairwise (fun a c =>
          I.clock a < I.clock c ∨ (I.clock a = I.clock c ∧ a < c))))

/- The pinned readable form of CONC-023: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CONC_023 : ReadyOrder → Prop :=
fun O =>
  ∀ (I : ReadyIn),
    ((O I).Perm I.readyList ∧ List.Pairwise (fun a c => I.prio a = I.prio c → I.clock a = I.clock c → a < c) (O I)) ∧
      (¬I.FastPath →
        ∃ blocks,
          O I = List.flatMap (fun x => x.2) blocks ∧
            (List.Pairwise (fun x1 x2 => x1 > x2) (List.map (fun x => x.1) blocks) ∧
                ∀ b ∈ blocks, ∀ a ∈ b.2, I.prio a = b.1) ∧
              ∀ b ∈ blocks, List.Pairwise (fun a c => I.clock a < I.clock c ∨ I.clock a = I.clock c ∧ a < c) b.2)
-/
#guard_msgs in #print CONC_023

/-! ### The block is the level-block shape of `Sched.lean` -/

/-- The conditions of lines 3 and 4 on the groups are `LevelBlocks` of the pass's canonical
key. -/
theorem conc023_levelBlocks_iff (I : ReadyIn) (blocks : List (Int × List Nat)) :
    LevelBlocks I.key blocks ↔
      ((blocks.map (·.1)).Pairwise (· > ·) ∧ ∀ b ∈ blocks, ∀ a ∈ b.2, I.prio a = b.1) ∧
      (∀ b ∈ blocks, b.2.Pairwise (fun a c =>
        I.clock a < I.clock c ∨ (I.clock a = I.clock c ∧ a < c))) :=
  ⟨fun h => ⟨⟨h.desc, h.homo⟩, h.sorted⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩

/-- A list strictly sorted by a canonical key is the drain of level blocks, each nonempty (the
converse of `levelBlocks_sorted`). -/
theorem conc023_blocks_of_sorted (K : SchedKey) : ∀ (l : List Nat), l.Pairwise K.lt →
    ∃ blocks : List (Int × List Nat), LevelBlocks K blocks ∧ blocks.flatMap (·.2) = l ∧
      ∀ b ∈ blocks, b.2 ≠ []
  | [], _ => ⟨[], ⟨List.Pairwise.nil, by simp, by simp⟩, rfl, by simp⟩
  | x :: t, h => by
    rw [List.pairwise_cons] at h
    obtain ⟨blocks, hlb, hfl, hne⟩ := conc023_blocks_of_sorted K t h.2
    have hx : ∀ b ∈ blocks, ∀ y ∈ b.2, K.lt x y := fun b hb y hy =>
      h.1 y (hfl ▸ List.mem_flatMap.2 ⟨b, hb, hy⟩)
    match blocks, hlb, hfl, hne, hx with
    | [], _, hfl, _, _ =>
      refine ⟨[(K.prio x, [x])], ⟨by simp, by simp, by simp⟩, ?_, by simp⟩
      simpa using hfl
    | (pr, b) :: rest, hlb, hfl, hne, hx =>
      have hbne : b ≠ [] := hne (pr, b) (by simp)
      obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil b hbne
      have hpy : K.prio y = pr := hlb.homo (pr, b) (by simp) y hy
      by_cases hp : K.prio x = pr
      · refine ⟨(pr, x :: b) :: rest, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
        · simpa using hlb.desc
        · intro b' hb' tid htid
          rcases List.mem_cons.1 hb' with rfl | hb'
          · rcases List.mem_cons.1 htid with rfl | htid
            · exact hp
            · exact hlb.homo (pr, b) (by simp) tid htid
          · exact hlb.homo b' (List.mem_cons_of_mem _ hb') tid htid
        · intro b' hb'
          rcases List.mem_cons.1 hb' with rfl | hb'
          · rw [List.pairwise_cons]
            refine ⟨fun z hz => ?_, hlb.sorted (pr, b) (by simp)⟩
            have hlt := hx (pr, b) (by simp) z hz
            have hpz : K.prio z = pr := hlb.homo (pr, b) (by simp) z hz
            unfold SchedKey.lt at hlt
            rcases hlt with hlt | ⟨_, hlt⟩
            · omega
            · exact hlt
          · exact hlb.sorted b' (List.mem_cons_of_mem _ hb')
        · simpa using hfl
        · intro b' hb'
          rcases List.mem_cons.1 hb' with rfl | hb'
          · simp
          · exact hne b' (List.mem_cons_of_mem _ hb')
      · refine ⟨(K.prio x, [x]) :: (pr, b) :: rest, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
        · have hd := hlb.desc
          simp only [List.map_cons, List.pairwise_cons] at hd ⊢
          have hgt : K.prio x > pr := by
            have hlt := hx (pr, b) (by simp) y hy
            unfold SchedKey.lt at hlt
            rcases hlt with hlt | ⟨he, _⟩
            · omega
            · exact absurd (he.trans hpy) hp
          refine ⟨fun a ha => ?_, hd⟩
          rcases List.mem_cons.1 ha with rfl | ha
          · exact hgt
          · have := hd.1 a ha
            omega
        · intro b' hb' tid htid
          rcases List.mem_cons.1 hb' with rfl | hb'
          · have : tid = x := by simpa using htid
            subst this; rfl
          · exact hlb.homo b' hb' tid htid
        · intro b' hb'
          rcases List.mem_cons.1 hb' with rfl | hb'
          · simp
          · exact hlb.sorted b' hb'
        · simpa using hfl
        · intro b' hb'
          rcases List.mem_cons.1 hb' with rfl | hb'
          · simp
          · exact hne b' hb'

/-- **The block is EXEC-002.** An ordering function satisfies CONC-023 exactly when it satisfies
EXEC-002: on every input the order holds every ready transition exactly once and breaks ties of
priority and stamp by declaration order, and off the fast path the drain of the level groups is
the canonical sort (priority descending, stamp ascending, declaration order ascending). -/
theorem CONC_023_iff_EXEC_002 (O : ReadyOrder) : CONC_023 O ↔ EXEC_002 O := by
  constructor
  · intro h I
    obtain ⟨⟨hp, ht⟩, hg⟩ := h I
    refine ⟨hp, ht, fun hI => ?_⟩
    obtain ⟨blocks, hfl, hl⟩ := hg hI
    rw [hfl]
    exact levelBlocks_sorted ((conc023_levelBlocks_iff I blocks).2 hl)
  · intro h I
    obtain ⟨hp, ht, hs⟩ := h I
    refine ⟨⟨hp, ht⟩, fun hI => ?_⟩
    obtain ⟨blocks, hlb, hfl, -⟩ := conc023_blocks_of_sorted I.key _ (hs hI)
    exact ⟨blocks, hfl.symm, (conc023_levelBlocks_iff I blocks).1 hlb⟩

/-- Every ordering function that satisfies EXEC-002 satisfies CONC-023. -/
theorem CONC_023_of_EXEC_002 {O : ReadyOrder} (h : EXEC_002 O) : CONC_023 O :=
  (CONC_023_iff_EXEC_002 O).2 h

/-- Off the fast path, a permutation of the ready list strictly sorted by the canonical key is the
order every ordering function satisfying CONC-023 computes. -/
theorem CONC_023_forced {O : ReadyOrder} (h : CONC_023 O) {I : ReadyIn} (hI : ¬ I.FastPath)
    {l : List Nat} (hp : l.Perm I.readyList) (hs : l.Pairwise I.key.lt) : O I = l :=
  EXEC_002_forced ((CONC_023_iff_EXEC_002 O).1 h) hI hp hs

/-! ### The reference -/

/-- ✓ The reference ready order satisfies CONC-023: off the fast path it is the canonical sort of
the ready transitions (EXEC-002), which is the drain of its level groups; on the fast path it is
the ready transitions in declaration order. -/
@[evidence holds CONC_023]
theorem CONC_023_reference : CONC_023 refReadyOrder :=
  CONC_023_of_EXEC_002 EXEC_002_reference

/-- The block does not decide D14: the reference (declaration order on the fast path) and the
general sort on every input (the other outcome) both satisfy it. -/
theorem CONC_023_D14_neutral : CONC_023 refReadyOrder ∧ CONC_023 exec002_sortOrder :=
  ⟨CONC_023_reference, CONC_023_of_EXEC_002 EXEC_002_D14_neutral.2⟩

/-! ### Examples -/

/-- The test derivation with three priority levels: five transitions, all `Delayed` (so the net
takes the general path) and all ready. Transition `1` has priority 3, transition `2` priority 2,
transitions `0`, `3` and `4` priority 1. In the lowest level, `3` and `4` were armed at `2` and
`0` later at `5`, so declaration order disagrees with arming order, and `3` and `4` share a
stamp. -/
def conc023_I5 : ReadyIn :=
  { n := 5, prio := fun t => if t = 1 then 3 else if t = 2 then 2 else 1,
    timing := fun _ => .delayed 1,
    clock := fun t => if t = 0 then 5 else if t = 1 ∨ t = 2 then 0 else 2,
    ready := fun _ => true }

theorem conc023_I5_general : ¬ conc023_I5.FastPath := by decide

/-- The level groups of `conc023_I5`: priority 3 holds `1`, priority 2 holds `2`, priority 1
holds `3`, `4` (equal stamps, declaration order) and then `0` (later stamp). -/
def conc023_blocks5 : List (Int × List Nat) := [(3, [1]), (2, [2]), (1, [3, 4, 0])]

/-- The order CONC-023 forces on `conc023_I5`. -/
theorem conc023_I5_forced {O : ReadyOrder} (h : CONC_023 O) : O conc023_I5 = [1, 2, 3, 4, 0] :=
  CONC_023_forced h conc023_I5_general (by decide) (by decide)

/-- The order CONC-023 forces on EXEC-002's `exec002_Ia` (two equal-priority transitions, `1`
armed before `0`): `1` first. -/
theorem conc023_Ia_forced {O : ReadyOrder} (h : CONC_023 O) : O exec002_Ia = [1, 0] :=
  CONC_023_forced h exec002_Ia_general (by decide) Libpetri.tid_order_diverges.2

/-- The order CONC-023 forces on EXEC-002's test derivation `exec002_I3` (priorities 5, 10, 5,
armed together). -/
theorem conc023_I3_forced {O : ReadyOrder} (h : CONC_023 O) : O exec002_I3 = [1, 0, 2] :=
  CONC_023_forced h exec002_I3_general (by decide) (by decide)

/-- Two transitions armed in different cycles at one repeated clock reading: both of priority `0`,
both `Delayed` (so the net takes the general path) and ready. Transition `1` was armed by the
enablement update of one cycle and transition `0` by that of a later cycle, but the firing clock
did not advance between the two updates (its readings may repeat), so both carry the stamp `4`.
The pass reads only the stamp, so the order is the declaration order, not the order of the
cycles. -/
def conc023_Irep : ReadyIn :=
  { n := 2, prio := fun _ => 0, timing := fun _ => .delayed 1, clock := fun _ => 4,
    ready := fun _ => true }

theorem conc023_Irep_general : ¬ conc023_Irep.FastPath := by decide

/-- The order CONC-023 forces on `conc023_Irep` (line 2, the fourth quoted sentence): `0` before
`1`, though `1` was armed in the earlier cycle. -/
theorem conc023_Irep_forced {O : ReadyOrder} (h : CONC_023 O) : O conc023_Irep = [0, 1] :=
  CONC_023_forced h conc023_Irep_general (by decide) (by decide)

/-- The order CONC-023 forces on EXEC-002's fast-path input `exec002_Ifp` (transition `1` not
ready), under either outcome of D14: the ready transitions `0` and `2`, tied on priority and
stamp, in declaration order (lines 1 and 2). -/
theorem conc023_Ifp_forced {O : ReadyOrder} (h : CONC_023 O) : O exec002_Ifp = [0, 2] :=
  exec002_Ifp_forced ((CONC_023_iff_EXEC_002 O).1 h)

/-! ### Violation: a pass that offers the highest level only -/

/-- "Picks the first non-empty queue" read as a pass that offers only the highest priority level
holding a ready transition: the reference order restricted to the transitions of the highest
priority among the ready ones. -/
def conc023_topOnly : ReadyOrder := fun I =>
  (refReadyOrder I).filter fun a => decide (∀ b ∈ refReadyOrder I, I.prio b ≤ I.prio a)

/-- ✗ A pass that offers the highest level only violates CONC-023 (line 1): on the test
derivation `exec002_I3` it offers `1` alone, leaving out the two ready priority-5 transitions. -/
@[evidence forbids CONC_023]
theorem CONC_023_forbids_topOnly : ¬ CONC_023 conc023_topOnly := by
  intro h
  have e := conc023_I3_forced h
  have e' : conc023_topOnly exec002_I3 = [1] := by
    simp only [conc023_topOnly, exec002_I3_forced EXEC_002_reference]
    decide
  rw [e'] at e
  exact absurd e (by decide)

/-! ### Mutant: the fast path left unconstrained -/

/-- Mutant reading of CONC-023 that leaves the fast path wholly unconstrained (the first form of
this block): lines 1 to 4 off the fast path only. -/
def CONC_023_mutant_generalOnly (O : ReadyOrder) : Prop :=
  ∀ I : ReadyIn, ¬ I.FastPath → ∃ blocks : List (Int × List Nat),
    (O I = blocks.flatMap (·.2) ∧ (O I).Perm I.readyList) ∧
    ((blocks.map (·.1)).Pairwise (· > ·) ∧ ∀ b ∈ blocks, ∀ a ∈ b.2, I.prio a = b.1) ∧
    (∀ b ∈ blocks, b.2.Pairwise (fun a c =>
      I.clock a < I.clock c ∨ (I.clock a = I.clock c ∧ a < c)))

/-- A fast path that offers only the first ready transition of the bitmap scan per pass (a
`break` left in the scan loop), so that every other ready transition waits for a later pass;
the general sort off the fast path. -/
def conc023_firstOnly : ReadyOrder := fun I =>
  if I.FastPath then I.readyList.take 1 else exec002_sortOrder I

/-- Off the fast path, the general sort satisfies the general-path-only reading. -/
theorem conc023_generalOnly_of_sort {O : ReadyOrder}
    (hO : ∀ I : ReadyIn, ¬ I.FastPath → O I = exec002_sortOrder I) :
    CONC_023_mutant_generalOnly O := fun I hI => by
  rw [hO I hI]
  obtain ⟨blocks, hlb, hfl, -⟩ :=
    conc023_blocks_of_sorted I.key _ (exec002_sortOrder_spec I).2.2
  exact ⟨blocks, ⟨hfl.symm, (exec002_sortOrder_spec I).1⟩,
    (conc023_levelBlocks_iff I blocks).1 hlb⟩

/-- The first-only fast path kills the mutant: it satisfies the general-path-only reading, but on
the fast-path input `exec002_Ifp` it offers `[0]` and drops the ready transition `2`, which both
outcomes of D14 offer (line 1; AC4, 'it bypasses the ready queues and fires'). -/
@[evidence mutant CONC_023]
theorem CONC_023_mutant_generalOnly_killed :
    CONC_023_mutant_generalOnly conc023_firstOnly ∧ ¬ CONC_023 conc023_firstOnly := by
  refine ⟨conc023_generalOnly_of_sort fun I hI => by simp only [conc023_firstOnly, if_neg hI],
    fun h => ?_⟩
  have := conc023_Ifp_forced h
  simp only [conc023_firstOnly, if_pos exec002_Ifp_fast] at this
  revert this; decide

/-- ✗ A fast path that offers every transition of the net, ready or not (`exec002_allFast`),
violates CONC-023 (line 1): on `exec002_Ifp` it offers transition `1`, which is not ready. -/
@[evidence forbids CONC_023]
theorem CONC_023_forbids_allFast : ¬ CONC_023 exec002_allFast := by
  intro h
  have := conc023_Ifp_forced h
  simp only [exec002_allFast, if_pos exec002_Ifp_fast] at this
  revert this; decide

/-- ✗ A fast path in descending declaration order (`exec002_revFast`) violates CONC-023 (line 2):
on `exec002_Ifp` it offers `2` before `0`, though the two are tied on priority and stamp. -/
@[evidence forbids CONC_023]
theorem CONC_023_forbids_revFast : ¬ CONC_023 exec002_revFast := by
  intro h
  have := conc023_Ifp_forced h
  simp only [exec002_revFast, if_pos exec002_Ifp_fast] at this
  revert this; decide

/-! ### Mutant: each level drained in declaration order ("NOT sufficient") -/

/-- Mutant reading of CONC-023 in which a level's queue is fed and drained in declaration order:
line 4 orders a group by declaration order only, not by stamp. Lines 1 to 3 are as in
CONC-023. -/
def CONC_023_mutant_tid (O : ReadyOrder) : Prop :=
  ∀ I : ReadyIn,
    ((O I).Perm I.readyList ∧
      (O I).Pairwise (fun a c => I.prio a = I.prio c → I.clock a = I.clock c → a < c)) ∧
    (¬ I.FastPath → ∃ blocks : List (Int × List Nat),
      O I = blocks.flatMap (·.2) ∧
      ((blocks.map (·.1)).Pairwise (· > ·) ∧ ∀ b ∈ blocks, ∀ a ∈ b.2, I.prio a = b.1) ∧
      (∀ b ∈ blocks, b.2.Pairwise (· < ·)))

/-- The pre-fix per-level drain in declaration order (`exec002_tidOrder`) kills the mutant: it
satisfies the mutant reading, but not CONC-023. On `exec002_Ia` it offers `0` before `1`, though
`1` was armed first (AC4, 'Feeding a level's queue in declaration order is NOT sufficient'). -/
@[evidence mutant CONC_023]
theorem CONC_023_mutant_tid_killed :
    CONC_023_mutant_tid exec002_tidOrder ∧ ¬ CONC_023 exec002_tidOrder := by
  refine ⟨fun I => ?_, fun h => ?_⟩
  · have hs := sortBy_pairwise (schedKey_strictTotal (exec002_tidKey I)) I.readyList_nodup
    refine ⟨⟨sortBy_perm _ _, hs.imp fun {a c} hac _ _ => ?_⟩, fun _ => ?_⟩
    · unfold SchedKey.lt at hac
      simp only [exec002_tidKey] at hac
      omega
    · obtain ⟨blocks, hlb, hfl, -⟩ := conc023_blocks_of_sorted (exec002_tidKey I) _ hs
      refine ⟨blocks, hfl.symm, ⟨hlb.desc, hlb.homo⟩,
        fun b hb => (hlb.sorted b hb).imp fun hac => ?_⟩
      simp only [exec002_tidKey] at hac
      omega
  · have e : exec002_tidOrder exec002_Ia = [0, 1] :=
      eq_of_perm_of_sorted (exec002_tidKey exec002_Ia)
        (sortBy_pairwise (schedKey_strictTotal _) exec002_Ia.readyList_nodup)
        (by decide) ((sortBy_perm _ _).trans (by decide))
    have := conc023_Ia_forced h
    rw [e] at this
    exact absurd this (by decide)

/-! ### Mutant: the levels drained from the lowest priority up -/

/-- The key that drains the levels from the lowest priority up: the priority negated, the stamp
and declaration order as in the canonical key. -/
def conc023_ascKey (I : ReadyIn) : SchedKey := { prio := fun t => - I.prio t, clock := I.clock }

/-- The order that drains the levels in ascending priority, each by stamp, then declaration
order. -/
def conc023_ascOrder : ReadyOrder := fun I => sortBy (conc023_ascKey I).lt I.readyList

/-- Mutant reading of CONC-023 in which the scan of the priority levels runs from the lowest
priority up: line 3 asks for strictly ascending group priorities. Lines 1, 2 and 4 are as in
CONC-023. -/
def CONC_023_mutant_asc (O : ReadyOrder) : Prop :=
  ∀ I : ReadyIn,
    ((O I).Perm I.readyList ∧
      (O I).Pairwise (fun a c => I.prio a = I.prio c → I.clock a = I.clock c → a < c)) ∧
    (¬ I.FastPath → ∃ blocks : List (Int × List Nat),
      O I = blocks.flatMap (·.2) ∧
      ((blocks.map (·.1)).Pairwise (· < ·) ∧ ∀ b ∈ blocks, ∀ a ∈ b.2, I.prio a = b.1) ∧
      (∀ b ∈ blocks, b.2.Pairwise (fun a c =>
        I.clock a < I.clock c ∨ (I.clock a = I.clock c ∧ a < c))))

/-- The ascending drain kills the mutant: it satisfies the mutant reading, but not CONC-023. On
the test derivation `exec002_I3` it offers the two priority-5 transitions before the
priority-10 one. -/
@[evidence mutant CONC_023]
theorem CONC_023_mutant_asc_killed :
    CONC_023_mutant_asc conc023_ascOrder ∧ ¬ CONC_023 conc023_ascOrder := by
  refine ⟨fun I => ?_, fun h => ?_⟩
  · have hs := sortBy_pairwise (schedKey_strictTotal (conc023_ascKey I)) I.readyList_nodup
    refine ⟨⟨sortBy_perm _ _, hs.imp fun {a c} hac _ _ => ?_⟩, fun _ => ?_⟩
    · unfold SchedKey.lt at hac
      simp only [conc023_ascKey] at hac
      omega
    · obtain ⟨blocks, hlb, hfl, -⟩ := conc023_blocks_of_sorted (conc023_ascKey I) _ hs
      refine ⟨blocks.map fun b => (- b.1, b.2), ?_, ⟨?_, ?_⟩, ?_⟩
      · simpa [conc023_ascOrder, List.flatMap_map, Function.comp_def] using hfl.symm
      · have hd := hlb.desc
        rw [List.map_map]
        exact (List.pairwise_map.1 hd |>.imp fun h => by simp; omega) |> List.pairwise_map.2
      · intro b hb a ha
        obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
        have := hlb.homo b' hb' a ha
        simp only [conc023_ascKey] at this
        simp only
        omega
      · intro b hb
        obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
        exact hlb.sorted b' hb'
  · have e : conc023_ascOrder exec002_I3 = [0, 2, 1] :=
      eq_of_perm_of_sorted (conc023_ascKey exec002_I3)
        (sortBy_pairwise (schedKey_strictTotal _) exec002_I3.readyList_nodup)
        (by decide) ((sortBy_perm _ _).trans (by decide))
    have := conc023_I3_forced h
    rw [e] at this
    exact absurd this (by decide)

/-! ### Every line exercised -/

/-- Every line of CONC-023 is exercised by the reference order. On the test derivation with three
priority levels `conc023_I5`, the order `[1, 2, 3, 4, 0]` holds every ready transition once
(line 1) and is the drain of the groups `(3, [1])`, `(2, [2])`, `(1, [3, 4, 0])`, whose
priorities 3, 2, 1 descend, each group holding only its level (line 3); in the lowest level `3`
and `4`, armed at `2`, come before `0`, armed at `5` though declared first, and `3` comes before
`4`, equal stamp, by declaration order (lines 2 and 4, AC4). On `exec002_Ia` the two
equal-priority transitions come in arming order `[1, 0]`, not declaration order (AC4); on
`conc023_Irep`, armed in different cycles at one repeated reading, in declaration order
`[0, 1]` (line 2). On the fast-path input `exec002_Ifp` the order leaves out the transition that
is not ready (line 1) and offers the tied `0` before `2` (line 2). -/
@[evidence nonvacuous CONC_023]
theorem CONC_023_nonvacuous :
    ¬ conc023_I5.FastPath ∧ refReadyOrder conc023_I5 = [1, 2, 3, 4, 0] ∧
      refReadyOrder conc023_I5 = conc023_blocks5.flatMap (·.2) ∧
      LevelBlocks conc023_I5.key conc023_blocks5 ∧
      conc023_I5.clock 3 = conc023_I5.clock 4 ∧ conc023_I5.clock 3 < conc023_I5.clock 0 ∧
      ¬ exec002_Ia.FastPath ∧ refReadyOrder exec002_Ia = [1, 0] ∧
      ¬ conc023_Irep.FastPath ∧ refReadyOrder conc023_Irep = [0, 1] ∧
      exec002_Ifp.FastPath ∧ exec002_Ifp.readyList = [0, 2] ∧
      refReadyOrder exec002_Ifp = [0, 2] := by
  refine ⟨conc023_I5_general, conc023_I5_forced CONC_023_reference, ?_,
    ⟨by decide, by decide, by decide⟩, by decide, by decide, exec002_Ia_general,
    conc023_Ia_forced CONC_023_reference, conc023_Irep_general,
    conc023_Irep_forced CONC_023_reference, exec002_Ifp_fast, by decide,
    conc023_Ifp_forced CONC_023_reference⟩
  rw [conc023_I5_forced CONC_023_reference]
  decide

end Libpetri.Spec
