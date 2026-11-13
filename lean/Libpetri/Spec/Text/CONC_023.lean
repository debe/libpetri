import Libpetri.Spec.Text

requirement_text CONC_023
  id "CONC-023"
  title "Priority-Partitioned Ready Queues"
  priority SHOULD
  kind F
  body r#"Distinct priority values are sorted descending at compile time. Each priority level has its own FIFO queue. Transition selection scans priority levels in descending order and picks the first non-empty queue, giving O(L) selection where L is the number of distinct priority levels (typically 1–3).

⟦s1|*Where* the net does not take the all-immediate fast path, the ready order *shall* be the ready transitions grouped by priority level, at most one group per priority level, with the groups in descending order of priority.⟧

⟦s2|*Where* the net does not take the all-immediate fast path, the ready order *shall* offer the ready transitions of one priority level in ascending order of stamp.⟧

⟦s3|The ready order *shall* hold every ready transition exactly once and no other transition, on the all-immediate fast path as well.⟧

⟦s4|The ready order *shall* offer ready transitions of one priority level with equal stamps in ascending declaration order, also when they were armed in different cycles and on the all-immediate fast path.⟧

Each transition maps to a priority index for O(1) ready-queue insertion.

**Acceptance Criteria:**
1. Distinct priority levels are precomputed and sorted descending.
2. Each priority level has a separate FIFO queue.
3. Transition selection is O(L) where L = distinct priority levels.
4. ⟦s5|Within the same priority, FIFO ordering by enablement time is preserved.⟧
   ⟦s6|Feeding a level's queue in declaration order is NOT sufficient: transitions
   enabled in different cycles must drain in enablement order even when it
   disagrees with declaration order, and equal enablement timestamps break by
   ascending declaration order — the identical order [EXEC-002] AC3/AC4
   requires of every backend.⟧ ⟦s7|The all-immediate single-priority fast path is
   exempt: it bypasses the ready queues and fires in declaration order, which
   [EXEC-002] AC4 requires of every backend alike.⟧

**Depends on:** [EXEC-002]
**Test derivation:** Net with 3 priority levels; verify transitions fire in correct priority order with FIFO within each level."#
