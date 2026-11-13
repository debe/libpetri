import Libpetri.Spec.Text

requirement_text CORE_060
  id "CORE-060"
  title "Context Input Access"
  priority MUST
  kind F
  body r#"The transition context provides access to consumed input token values. Actions can retrieve single values or lists of values from declared input places.

⟦s1|*When* an action calls `inputs(place)` on an input place of its transition, the call *shall* return the values of the tokens the firing consumed from that place, in the order the firing consumed them ([EXEC-010]).⟧

⟦s2|*When* an action calls `input(place)` on an input place from which the firing consumed exactly one token, the call *shall* return the value of that token.⟧

⟦s3|*Where* the transition context gives access to tokens (Java, TypeScript), *when* an action calls `inputToken(place)` on an input place from which the firing consumed exactly one token, the call *shall* return that token, with its creation timestamp.⟧

⟦s4|*If* an action calls `inputs(place)`, `input(place)` or `inputToken(place)` (where it exists) on a place that does not resolve to an input place of its transition ([MOD-031]), *then* the call *shall* report an error ([CORE-063]).⟧

⟦s5|What `input(place)` and `inputToken(place)` return when the firing consumed more than one token from the place is not specified; an action reads a batch with `inputs(place)`.⟧

**Acceptance Criteria:**
1. `input(place)` returns the single consumed value.
2. `inputs(place)` returns all consumed values (for multi-token cardinality).
3. `inputToken(place)` returns the token with metadata (including timestamp).
4. Accessing an undeclared input place results in an error.

**Depends on:** [CORE-050], [EXEC-010]
**Test derivation:** Fire transition consuming 3 tokens; verify `inputs()` returns 3 values."#
