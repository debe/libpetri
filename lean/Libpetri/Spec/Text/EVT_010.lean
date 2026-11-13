import Libpetri.Spec.Text

requirement_text EVT_010
  id "EVT-010"
  title "ActionTimedOut Event"
  priority MUST
  kind B
  body r#"Emitted when a firing ends with its timeout outcome ([EXEC-022]): the budget of the `Out.Timeout` node of its output spec runs out before its action completes. It is distinct from TransitionTimedOut, which reports a transition reaped at its timing deadline ([EVT-009]). Contains:
- Timestamp
- Transition name
- Timeout duration

⟦s1|The executor *shall* emit an ActionTimedOut event only when the budget of a firing runs out or when it settles a firing that ended with its timeout outcome, and the event *shall* name that firing's transition.⟧

⟦s2|*When* the executor emits the ActionTimedOut event of a firing as it deposits the firing's timeout outcome, it *shall* emit that event before the TokenAdded events of the outcome.⟧

⟦s3|The executor *shall* emit at most one ActionTimedOut event for each firing, and, for a firing that ended with its timeout outcome, *shall* emit one no later than when it settles that outcome, whether it deposits the outcome or fails the firing because the join-relay check of [NU-054] rejects it.⟧

⟦s4|Each ActionTimedOut event *shall* carry the duration of the `Timeout` node of the firing's output spec.⟧

**Acceptance Criteria:**
1. Emitted for a firing that ends with its timeout outcome (its action's Out.Timeout budget runs out before the action completes, [EXEC-022]), and never for a transition reaped at its timing deadline.
2. The TokenAdded events of the timeout branch come after this event.

**Depends on:** [IO-013], [EXEC-022], [EVT-009], [NU-054]
**Test derivation:** Action sleeps 500ms; Out.Timeout at 100ms; verify ActionTimedOut event."#
