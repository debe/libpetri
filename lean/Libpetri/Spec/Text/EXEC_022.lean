import Libpetri.Spec.Text

requirement_text EXEC_022
  id "EXEC-022"
  title "Action Timeout Handling"
  priority MUST
  kind T
  body r#"⟦s1|When a transition's output specification includes a Timeout node, the executor races the action against the timeout duration:⟧
- ⟦s2|Action completes first → normal output validation.⟧
- ⟦s3|Timeout fires first → the firing is abandoned (the action is stopped where the runtime can; see [IO-013]); the timeout child output receives tokens; ActionTimedOut event emitted.⟧

⟦s4|The budget is host time: it elapses in real time, not on the firing clock ([TIME-015]).⟧ ⟦s5|Only an action that hands control back to the executor before it completes races its budget; an action that completes before it hands control back, a synchronous action for example, never times out.⟧ ⟦s6|When the action completes at the instant the budget runs out, either side may win.⟧

⟦s7|*If* the output spec of a firing's transition has no `Timeout` node, or the action of the firing completed before it handed control back to the executor, *then* the executor *shall not* end the firing with its timeout outcome.⟧ ⟦s8|*While* the budget of a firing has not elapsed, the executor *shall not* end the firing with its timeout outcome.⟧ ⟦s9|*If* the action of a firing completes before the firing ends with its timeout outcome, *then* the executor *shall not* end the firing with its timeout outcome.⟧ ⟦s10|*If* a firing has already ended, by the return of its action or by its budget running out, *then* the executor *shall not* change how it ended.⟧

⟦s11|*When* the budget of a firing runs out before its action completes, the executor *shall* take as the timeout outcome the tokens of the `Timeout` child ([IO-013], [IO-014]): one minted token for each `Place` node, and for each `ForwardInput(from, to)` every token the firing consumed from `from`, in consumption order, each keeping its value and `created_at`.⟧ ⟦s12|*When* the executor deposits the timeout outcome of a firing, it *shall* add exactly the tokens of that outcome, each at the tail of its place, and *shall not* deposit an outcome of that firing again or fail it afterwards.⟧

⟦s13|*If* the budget of a firing runs out before its action completes, *then* the executor *shall not* deposit the completion of the action, and *shall not* deposit or publish any other output the action had not published before the budget ran out.⟧ ⟦s14|Output the action published before the budget ran out stays in the marking ([EXEC-020], [IO-015]).⟧ ⟦s15|The timeout outcome is not validated against the output spec, and the join-relay check of [NU-054] still runs on it ([EXEC-021]).⟧

**Acceptance Criteria:**
1. Action completes in 50ms with 100ms timeout → normal completion.
2. An action that hands control back to the executor and takes 200ms, with a 100ms timeout → timeout branch activated; ActionTimedOut event.
3. ForwardInput in timeout child → **every** token consumed from the `from` place is forwarded to the `to` place, one output token per consumed token, in consumption order, each keeping its original `created_at` ([IO-014]).
4. Output the action wrote and had not published before the budget expired is discarded, not merged with the timeout branch ([IO-013] AC5); output it published before stays in the marking ([EXEC-020]).

**Depends on:** [IO-013], [IO-014], [EVT-010], [TIME-015], [EXEC-021], [NU-054]
**Test derivation:** Slow action with timeout; verify timeout branch tokens and event."#
