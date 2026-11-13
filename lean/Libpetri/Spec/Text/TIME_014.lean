import Libpetri.Spec.Text

requirement_text TIME_014
  id "TIME-014"
  title "Competitive Scheduling with Timing"
  priority MUST
  kind T
  body r#"⟦s1|When multiple transitions compete for the same tokens, timing interacts with priority:⟧
- ⟦s2|Higher priority transitions are preferred.⟧
- Before its earliest bound a Delayed transition is not ready, so a ready Immediate transition competing for the same tokens takes them first whatever their priorities; once both are ready, the order of [EXEC-002] applies (among equal priority, the one armed first comes first).
- A Delayed transition with low priority can serve as a fallback: while it stays armed, it fires in the first cycle at or after its earliest bound in which the high-priority Immediate transition is not ready to take the tokens.

⟦s3|*While* several ready transitions compete for the same tokens, the executor *shall* fire them in the order of [EXEC-002], so the transition with the highest priority takes the tokens first ([EXEC-003]).⟧

⟦s4|*While* a `Delayed` transition is armed and its elapsed time is less than its earliest bound, it *shall not* fire, so a ready transition competing for the same tokens takes them first whatever their priorities ([TIME-004]).⟧

**Acceptance Criteria:**
1. Two transitions on same input: T1 (P=10, Immediate) and T2 (P=-10, Delayed(3s)); T1 also needs an event token in a second input place, which holds one; T1 fires first.
2. If T1's event place stays empty for 3s, T1 is not enabled: T2 is armed at once, becomes ready when its elapsed time reaches 3s, and fires.

**Depends on:** [EXEC-002], [EXEC-003]
**Test derivation:** Event-driven workflow pattern: PrimaryAction (P=10, immediate) vs FallbackAction (P=-10, 3s delay)."#
