import Libpetri.Spec.Text

requirement_text EVT_007
  id "EVT-007"
  title "TransitionCompleted Event"
  priority MUST
  kind B
  body r#"Emitted when the executor deposits the outcome of a firing whose action completed successfully: the tokens the action produced at completion (an admitted completion, [EXEC-021]). Contains:
- Timestamp
- Transition name
- List of produced tokens (Java and TypeScript; defensive copy)
- Duration of action execution (Java and TypeScript)

⟦s1|*When* the executor deposits an admitted completion ([EXEC-021]), it *shall* emit the TokenAdded events of the deposited tokens followed by exactly one TransitionCompleted event naming the firing's transition, and no other event in that deposit except log messages ([EVT-013]).⟧

⟦s2|The executor *shall* emit TransitionCompleted events only when it deposits an admitted completion or a timeout outcome ([EXEC-022]).⟧

⟦s3|*If* the executor emits a TransitionCompleted event when it deposits a timeout outcome, *then* that event *shall* name the firing's transition and be the only TransitionCompleted event of the deposit and its last event other than log messages.⟧

⟦s4|*Where* the TransitionCompleted event carries the produced tokens (Java and TypeScript), the TokenAdded events of the deposit of an admitted completion *shall* carry the tokens the action produced at completion in emission order ([EXEC-020]), and the TransitionCompleted event *shall* list the same tokens in the same order.⟧

⟦s5|*Where* the TransitionCompleted event carries the produced tokens (Java and TypeScript), a TransitionCompleted event emitted when the executor deposits a timeout outcome *shall* list the tokens of that timeout outcome.⟧

⟦s6|*Where* the TransitionCompleted event carries the duration of the action (Java and TypeScript), the duration *shall* be at most the firing-clock time from the start of the firing to the moment the executor deposits its outcome ([TIME-015]).⟧

**Acceptance Criteria:**
1. Emitted after successful action completion and after the TokenAdded events of the tokens the action produced at completion. Tokens the action published before it completed ([IO-015]) may be deposited and reported after the event ([EXEC-020]).
2. (Java and TypeScript) The duration is at most the firing-clock time between the start of the firing and the deposit of its outcome; zero is allowed.

**Depends on:** [EVT-011], [EXEC-020], [EXEC-021], [EXEC-022]
**Test derivation:** Fire a transition whose action produces a token after the clock advanced; verify the TokenAdded event, then TransitionCompleted naming the transition, which in Java and TypeScript lists the produced token with a duration no larger than the clock advance."#
