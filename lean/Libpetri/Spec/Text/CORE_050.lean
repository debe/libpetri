import Libpetri.Spec.Text

requirement_text CORE_050
  id "CORE-050"
  title "Transition Action"
  priority MUST
  kind B
  body r#"A transition action is an asynchronous function that receives a transition context and produces output tokens. The action signature returns a future/promise that resolves when the action completes.

⟦s1|*When* a transition fires, its action *shall* receive a transition context holding the tokens the firing consumed from each input place and the tokens its read arcs read ([EXEC-010], [EXEC-012]).⟧

⟦s2|*When* a firing ends with the completion of its action, the firing *shall* deposit exactly the output tokens the action completed with, whether the action wrote them through the context or returned them.⟧

⟦s3|*If* the executor admits the completion of a firing's action ([EXEC-020]), the transition has no match specification ([NU-020]) and the output tokens fill one output branch ([IO-015]), *then* the firing *shall* end with that completion.⟧

**Acceptance Criteria:**
1. Action receives a context with consumed input tokens and read token values.
2. Action produces output tokens via the context or a return value.
3. Action is asynchronous (returns future/promise/completion stage).

**Test derivation:** Create action that reads input, transforms it, and produces output; verify output tokens."#
