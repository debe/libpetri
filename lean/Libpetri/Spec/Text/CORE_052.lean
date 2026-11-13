import Libpetri.Spec.Text

requirement_text CORE_052
  id "CORE-052"
  title "Fork Action"
  priority SHOULD
  kind F
  body r#"⟦s1|A built-in fork action that copies a single input token value to all declared output places.⟧

⟦s2|*When* the fork action runs for a transition with exactly one input place and the firing consumed exactly one token from that place, the action *shall* complete with one token carrying that token's value in every place the output spec names and with no token in any other place.⟧

⟦s3|*If* the transition does not have exactly one input place, *then* the fork action *shall* fail.⟧

⟦s4|*When* the firing consumed two or more tokens from the single input place, the fork action *shall* either fail or complete with one token carrying the oldest consumed token's value in every place the output spec names and with no token in any other place.⟧

⟦s5|**Divergence:** when the firing consumed two or more tokens from the single input place, the fork action copies the oldest consumed token to every output place in Java, Rust and Python and fails in TypeScript.⟧

⟦s6|**Note:** The fork action writes every place the output spec names, so on an output spec `Xor(a, b)` with two different places it writes both, and an executor with output validation enabled rejects its completion ([IO-015], [EXEC-021]).⟧

**Acceptance Criteria:**
1. Requires exactly one input place.
2. Produces exactly one token carrying the input value in each output place, and no token in any other place.
3. Throws/errors if the transition does not declare exactly one input place (none, or more than one).
4. When the firing consumed two or more tokens from the single input place, either fails or produces the oldest consumed token's value as in criterion 2.

**Test derivation:** Fork action with 1 input and 3 outputs; verify all 3 receive the same value."#
