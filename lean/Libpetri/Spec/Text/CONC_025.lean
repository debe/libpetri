import Libpetri.Spec.Text

requirement_text CONC_025
  id "CONC-025"
  title "Lazy Marking Synchronization"
  priority SHOULD
  kind B
  body r#"The executor maintains token state internally in ring buffers [CONC-022] and materializes a Marking object lazily — only when needed for events [EVT-014], debug inspection, or the execution result [EXEC-041]. During normal execution cycles, no Marking object is created or updated.

⟦s1|*When* the executor materializes a Marking, it *shall* give each place the token storage holds a queue for exactly the tokens of that queue at that moment, in queue order.⟧

**Acceptance Criteria:**
1. Normal execution cycles do not create or update a Marking object.
2. Marking is materialized on demand for event emission, debug, or result.
3. ⟦s2|The materialized Marking accurately reflects the current ring buffer state.⟧

**Test derivation:** Execute a net with noop event store; verify no Marking object is created until result is requested."#
