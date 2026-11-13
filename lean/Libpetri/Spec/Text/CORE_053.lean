import Libpetri.Spec.Text

requirement_text CORE_053
  id "CORE-053"
  title "Transform Action"
  priority SHOULD
  kind F
  body r#"A built-in transform action that applies a user-provided function to the context, then copies the result to all output places.

⟦s1|*When* a transition fires under the transform action, the action *shall* call its function with the transition context of that firing, and *shall* complete or fail with the outcome of one such call.⟧

⟦s2|*When* the function returns a value, the transform action *shall* complete with the output tokens the function wrote through the context, followed in every place the output spec names by one token carrying that value.⟧

**Note:** The places the output spec names include every branch of an `Xor` and the child of a `Timeout`, and the transform action puts one copy in each. On an output spec with an `Xor`, that completion fills more than one branch, so output validation ([IO-015]) rejects it.

**Acceptance Criteria:**
1. Function receives the transition context.
2. Return value is produced to all output places.

**Test derivation:** Transform action doubles an integer input; verify all outputs receive the doubled value."#
