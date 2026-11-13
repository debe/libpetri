import Libpetri.Spec.Text

requirement_text EXEC_021
  id "EXEC-021"
  title "Output Spec Validation"
  priority MUST
  kind B
  body r#"⟦s1|Before depositing tokens, the executor validates that the produced tokens satisfy the declared output specification (see [IO-015]).⟧ ⟦s2|An executor with the validation skip of [CONC-026] enabled does not validate.⟧

⟦s3|*When* an executor with output validation enabled admits the completion of an action, it *shall* validate the produced tokens against the transition's output spec ([IO-015]) before it deposits any of them.⟧

⟦s4|*If* the produced tokens of an admitted completion fail output validation, *then* the executor *shall* deposit none of them and *shall* emit a TransitionFailed event ([EVT-008]).⟧

⟦s5|*If* the produced tokens of an admitted completion fail output validation, *then* the executor *shall not* restore the tokens the firing consumed and *shall not* remove the tokens the action published before it completed ([IO-015]).⟧

⟦s6|*When* an executor with output validation enabled validates the produced tokens of an admitted completion, it *shall* count the places of every batch the action published before it completed ([IO-015]) as produced, together with the places of the produced tokens.⟧

⟦s7|*If* the produced tokens of an admitted completion pass output validation, *then* the executor *shall not* fail the firing.⟧

⟦s8|The timeout outcome is not a completion of the action: [EXEC-022] and [IO-013] govern its deposit.⟧

⟦s9|*When* a firing ends with its timeout outcome, the executor *shall not* validate the timeout outcome against the transition's output spec; the join-relay check of [NU-054] still runs on it.⟧

**Acceptance Criteria:**
1. And: all children received tokens → valid.
2. Xor: exactly one child is selected; overlapping branches resolve without a tie-break, because [IO-015] requires the selected assignment's claim to *equal* the produced set, not merely be satisfied by it.
3. Violation → failure event emitted.
4. Validation is applied by every executor backend a language ships, not only the reference one.
5. Violation → the event is TransitionFailed, no produced token is deposited, the consumed tokens are not restored ([EXEC-030]), and tokens the action published mid-action stay in the marking.

**Depends on:** [IO-011], [IO-012], [IO-015], [EVT-008], [EXEC-030], [NU-054]
**Test derivation:** Xor output with tokens to 2 branches → violation event; verify neither branch place received a token."#
