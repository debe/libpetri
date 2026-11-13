import Libpetri.Spec.Text

requirement_text EXEC_002
  id "EXEC-002"
  title "Priority-Based Firing Order"
  priority MUST
  kind F
  body r#"⟦s1|When multiple transitions are ready to fire (armed, past their earliest bound and not expired; see the glossary), they are sorted by:⟧
1. ⟦s2|**Priority**, descending: a higher priority fires first.⟧
2. ⟦s3|**Stamp**, ascending (FIFO): among equal priority, the transition armed first fires first ([TIME-010]).⟧
3. ⟦s4|**Declaration order**, ascending: among equal priority and equal stamp, the transition declared first fires first.⟧

⟦s5|The ready order of a firing pass *shall* hold every ready transition exactly once and no other transition.⟧

⟦s6|*Where* the net does not take the all-immediate fast path, the ready order *shall* offer a ready transition of higher priority before a ready transition of lower priority.⟧

⟦s7|*Where* the net does not take the all-immediate fast path, the ready order *shall* offer, among ready transitions of equal priority, the one with the earlier stamp first.⟧

⟦s8|The ready order *shall* offer, among ready transitions of equal priority and equal stamp, the earlier-declared one first.⟧

⟦s9|*When* a firing pass starts transitions, the executor *shall* start only transitions of the ready order of that pass, in the order in which that order offers them.⟧

⟦s10|*When* an enablement update newly arms several transitions, a restarted transition included ([TIME-012]), it *shall* give all of them one and the same stamp.⟧

**All-immediate fast path.** ⟦s11|When every transition is `Immediate` and all priorities are equal, backends fire straight from the enablement bitmap in ascending declaration order and do not read the enablement timestamp at all — including when two ready transitions carry different timestamps because one was held across cycles while in flight.⟧ This is deliberate, and every backend takes the path under the same condition. ⟦s12|The sort above describes the general path.⟧

**Acceptance Criteria:**
1. Transition with priority 10 fires before transition with priority 5.
2. Two transitions with equal priority on the general path: the one armed first (the earlier
   stamp) fires first.
3. ⟦s13|Equal priority **and** equal stamp (transitions newly armed by the enablement update of
   the same orchestrator cycle share one stamp, [TIME-010]): the tie breaks by ascending
   declaration order, so the order is fully deterministic.⟧
4. Every executor backend produces the **identical** ready order for the same net
   and marking. Stamp order is the general-path order; on the
   all-immediate single-priority fast path every backend fires in declaration
   order instead. Backends MUST NOT differ in which order they use, nor in the
   condition that selects it.

**Depends on:** [TIME-010]
**Test derivation:** Three transitions with priorities 5, 10, 5; enable all simultaneously; verify firing order: P10, then P5 (first enabled), then P5 (second enabled). For AC4, on a net that takes the general path (two priority levels, or one non-`Immediate` transition), enable two equal-priority transitions in different cycles with declaration order opposite to enablement order and verify every backend follows enablement order; on an all-immediate single-priority net, verify every backend fires in declaration order."#
