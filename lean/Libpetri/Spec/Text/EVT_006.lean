import Libpetri.Spec.Text

requirement_text EVT_006
  id "EVT-006"
  title "TransitionStarted Event"
  priority MUST
  kind B
  body r#"⟦s1|Emitted when a transition begins firing (tokens consumed, action dispatched).⟧ Contains:
- Timestamp
- Transition name
- List of removed tokens, consumed by input arcs and drained by reset arcs (Java and TypeScript only; defensive copy)

⟦s2|*When* a transition starts, the executor *shall* emit exactly one TransitionStarted event naming that transition as the last event of the start, and no event before it in that start other than TokenRemoved events ([EVT-012]).⟧

⟦s3|The executor *shall* emit TransitionStarted events only when a transition starts.⟧

⟦s4|*Where* the TransitionStarted event carries the removed tokens (Java and TypeScript), it *shall* list the tokens of the TokenRemoved events of the same start, in the same order.⟧

⟦s5|*Where* the TransitionStarted event carries the removed tokens (Java and TypeScript), the list *shall* hold every token the firing rule removes from the marking visible to the pass ([EXEC-003], [EXEC-013]): the tokens the input arcs consume, then the tokens the reset arcs drain, each group in declaration order and each place's tokens oldest first.⟧

**Acceptance Criteria:**
1. Emitted after token consumption, before action execution.
2. (Java and TypeScript) The list of removed tokens matches the tokens the start actually removes, consumed and drained.

**Test derivation:** Fire a transition that consumes 2 tokens through an input arc and drains 1 through a reset arc; verify its 3 TokenRemoved events, then TransitionStarted as the last event of the start, which in Java and TypeScript lists the same 3 tokens in the same order."#
