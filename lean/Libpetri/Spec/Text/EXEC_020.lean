import Libpetri.Spec.Text

requirement_text EXEC_020
  id "EXEC-020"
  title "Output Token Deposition"
  priority MUST
  kind B
  body r#"After an action completes and the executor admits the completion, the executor deposits produced tokens into the marking according to the output specification, unless output validation rejects them ([EXEC-021]). ⟦s1|Each token is added to the end of the target place's FIFO queue, in the order the action produced it.⟧

A completion is an action that returned normally; an action that throws or returns an error fails instead ([EXEC-030]). The executor **admits** a completion when it processes it: in step 1 of a cycle, or inside the firing pass for a synchronous action ([EXEC-001]). ⟦s2|It never admits the completion of a firing that ended with its timeout outcome ([EXEC-022], [IO-013]), that a stop on a terminal place abandoned ([EXEC-042]) or that an immediate termination abandoned ([ENV-015]).⟧ A close ([ENV-013]) waits for in-flight actions and admits their completions.

⟦s3|*When* the executor admits the completion of an action and output validation does not reject the produced tokens ([EXEC-021], [CONC-026]), the executor *shall* add each produced token at the tail of its place's queue, in the order the action produced the tokens.⟧

⟦s4|*If* the completion of an action is not admitted, or output validation rejects the produced tokens, *then* the executor *shall not* deposit any token the action produced at completion.⟧

Tokens an action published before it completed ([IO-015], mid-action publication) are deposited when the executor processes the publication, which can be after the completion's own tokens. They are not deposited again, and once deposited they stay in the marking, whatever happens to the completion. ⟦s5|A publication still queued when a terminal place stops the run ([EXEC-042]) is discarded.⟧

⟦s6|*When* the executor deposits the tokens an action produced at completion, it *shall* do so only in the step that admits that completion, while the run is under way and no terminal place is marked, and *shall* add them at the tails of their places' queues in the order the action produced them.⟧

⟦s7|The executor *shall* change the marking only when it starts a transition, deposits the tokens of an admitted completion, deposits a timeout outcome ([EXEC-022]), deposits a mid-action publication ([IO-015]) or injects an external event ([ENV-003]).⟧

⟦s8|*When* a run has finished ([EXEC-041]), the executor *shall not* change the marking, so a completion, a timeout outcome or a publication that is still in flight or queued deposits nothing.⟧

⟦s9|*When* the executor deposits the timeout outcome of a firing ([EXEC-022], [IO-013]), it *shall* do so only in a step in which a completion of that firing would be admitted, while the run is under way and no terminal place is marked, and *shall* add exactly the tokens of that outcome at the tails of their places' queues, in the order of the outcome.⟧

**Acceptance Criteria:**
1. Action produces token with value V to place P; V appears at end of P's queue.
2. Multiple tokens to same place are added in order.
3. A completion that is not admitted (the firing ended with its timeout outcome, or a terminal place stopped the run while the action was in flight) deposits none of the action's tokens.
4. A completion whose produced tokens fail output validation deposits none of them ([EXEC-021]).

**Depends on:** [EXEC-021], [EXEC-022], [EXEC-042], [IO-015]
**Test derivation:** Action produces 3 tokens to P; verify all 3 appear in order. Action with a timeout budget that writes to P and then outlives the budget; verify P receives nothing from the action. Action that writes to a place outside its chosen output branch; verify nothing is deposited."#
