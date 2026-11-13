import Libpetri.Spec.Text

requirement_text CORE_035
  id "CORE-035"
  title "Output Arc"
  priority MUST
  kind B
  body r#"An output arc connects a transition to a place.

⟦s1|*When* a transition fires, it *shall* deposit tokens only in its output places, according to its output spec (see [IO-010]–[IO-015]).⟧

⟦s2|*When* a transition fires, the marking the firing leaves *shall* hold every token the firing deposited.⟧

⟦s3|*When* a transition fires, every place that is neither an input place nor a reset place of the transition *shall* change by exactly the tokens the firing deposited there.⟧

**Acceptance Criteria:**
1. After transition fires, produced tokens appear in the output place.
2. Output tokens are created with the current timestamp of the epoch clock ([TIME-015]); a
   token a `ForwardInput` forwards keeps its original `created_at` ([IO-014]).

**Test derivation:** Fire transition with output; verify token appears in output place."#
