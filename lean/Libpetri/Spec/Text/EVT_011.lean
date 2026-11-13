import Libpetri.Spec.Text

requirement_text EVT_011
  id "EVT-011"
  title "TokenAdded Event"
  priority MUST
  kind B
  body r#"⟦s1|Emitted when the executor adds a token to a place: from an action's output, a timeout outcome, a mid-action publication (where the implementation offers one, [IO-015]) or an external injection.⟧ ⟦s2|The tokens of the initial marking are not added by the executor and get no TokenAdded event; where the executor emits a MarkingSnapshot at the start of a run, that snapshot reports them ([EVT-014]).⟧ Contains:
- Timestamp
- Place name
- The token (Java and TypeScript; Rust and Python when the event store captures tokens)

⟦s3|*When* the executor deposits tokens into a place, by settling a completion or a timeout outcome, by depositing a mid-action publication (where the implementation offers one, [IO-015]) or by injecting an environment token, it *shall* emit one TokenAdded event naming that place for each token it deposits there.⟧

⟦s4|The executor *shall* emit TokenAdded events only when it deposits tokens, and *shall not* emit a TokenAdded event for a token of the initial marking.⟧

⟦s5|*Where* the TokenAdded event carries the token (Java and TypeScript; Rust and Python when the event store captures tokens), the TokenAdded events of a deposit *shall* carry, for each place, the tokens deposited there in the order they are appended, so that the place's queue before the deposit followed by these tokens is its queue after the deposit.⟧

**Acceptance Criteria:**
1. Emitted for every token the executor deposits during a run, and at no other time: not for the tokens of the initial marking, not when a transition starts and not when an injection is requested.
2. Place name identifies the target place.
3. Where the event carries the token, the tokens reported for a place in one deposit are the deposited tokens, in the order they are appended.

**Test derivation:** Add token to place; verify TokenAdded event with correct place name."#
