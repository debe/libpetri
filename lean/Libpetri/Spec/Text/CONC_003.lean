import Libpetri.Spec.Text

requirement_text CONC_003
  id "CONC-003"
  title "Happens-Before Guarantee"
  priority MUST
  kind B
  body r#"⟦s1|All writes performed by an action (output tokens, side effects) are visible to the orchestrator after the action's future/promise completes.⟧ ⟦s2|The completion mechanism provides a happens-before edge.⟧

⟦s3|*When* the executor deposits the produced tokens of an admitted completion ([EXEC-020]), it *shall* deposit exactly the tokens the action wrote after its last publication, if any ([IO-015]), and before it returned, each at the tail of its place, in the order the action wrote them.⟧

⟦s4|*When* the executor deposits a batch an action published before it completed ([IO-015]), it *shall* deposit the earliest publication of that action it has not yet deposited, as exactly the tokens the action wrote before that publication and after the one before it, each at the tail of its place, in the order the action wrote them.⟧

⟦s5|The executor *shall* keep the batches an action published queued, in the order the action published them, until it deposits each one, unless a terminal place or an immediate termination stops the run ([EXEC-042], [ENV-015]).⟧

**Acceptance Criteria:**
1. Action writes to output context; orchestrator reads output after completion; values are visible.
2. No stale reads possible.

**Test derivation:** Action stores complex object in output; verify orchestrator sees complete object."#
