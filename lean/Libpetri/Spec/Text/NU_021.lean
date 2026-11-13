import Libpetri.Spec.Text

requirement_text NU_021
  id "NU-021"
  title "Match as the Sole Per-Token Filter"
  priority MUST
  kind B
  body r#"Name correlation ([NU-020]) is the **only** per-token filter the enablement check
applies. There is no unary value predicate on an input: guards were removed in
[IO-006] and no implementation carries one, so token selection is determined by
position ([EXEC-010], [IO-007]) and, on correlated inputs, by name equality, with the
chosen name picked by the tie-break of [NU-020], which reads names and `createdAt` only.
Nothing else about a token's value is read.

A pairing of values says, for each place, which pairs of values may stand in for each other
there. A transition's keys and relay targets cannot tell a pairing apart when every key on a
place, and every relay target at a place, projects the two values of each pair on that place to
the same name or to no name. On a place that no key and no relay target reads, a pairing may
pair any two values, and a transition without a match specification has no keys, so for it any
pairing qualifies. Two markings differ by a pairing when every place holds as many tokens in
both and the tokens at the same queue position of a place have the same `createdAt` and values
the pairing pairs on that place. Two emissions, or two deliveries, differ by a pairing when they
hold such tokens on the same places in the same order.

⟦s1|*When* a transition fires, it *shall* also fire with the same chosen name from every marking that differs from its marking only by a pairing its keys and relay targets cannot tell apart, for every emission that differs from its emission by the same pairing, delivering tokens and leaving a marking that differ from its own by the same pairing.⟧

⟦s2|*When* a transition with a match specification fires, every token it delivers from a correlated input *shall* project to the chosen name under that input's key.⟧

⟦s3|*When* a transition with a match specification fires, each correlated input that is not one of its reset places *shall* end the firing holding, of the tokens that do not project to the chosen name, exactly the ones it held before, in their order, followed by the ones the firing deposited there, in the order deposited.⟧

*Note (non-normative).* Should a future revision reintroduce a unary input filter, the
intended composition order is: the filter applies **first** and the name correlation runs
over the survivors, so a token must pass the filter *and* project to the chosen name to be
consumed. No implementation has such a filter today.

**Acceptance Criteria:**
1. No input specification variant exposes a value predicate; the enablement check
   evaluates no per-token predicate other than name equality on correlated inputs.
2. A correlated input consumes only tokens carrying the chosen name; a same-place
   token of a different name is left behind regardless of its value.

**Depends on:** [NU-020], [EXEC-010], [IO-007]
**Test derivation:** A ν-join over a place holding tokens of two different names;
verify only the tokens of the selected name are consumed and the others remain."#
