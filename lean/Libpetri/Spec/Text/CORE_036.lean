import Libpetri.Spec.Text

requirement_text CORE_036
  id "CORE-036"
  title "Arc Semantics Summary"
  priority MUST
  kind B
  body r#"The five arc types have the following semantics:

| Arc Type  | Requires Token? | Consumes? | Effect                      |
|-----------|-----------------|-----------|------------------------------|
| Input     | Yes             | Yes       | Token consumed on fire       |
| Output    | No              | No        | Token produced on complete   |
| Inhibitor | No (blocks if present) | No | Disables transition          |
| Read      | Yes             | No        | Token remains; provides value|
| Reset     | No              | Yes (all) | All tokens removed on fire   |

In EARS form, for every transition:

⟦s1|*While* an input place of the transition holds fewer tokens than the required count of its input arc, the transition *shall not* fire.⟧

⟦s2|*While* a read place of the transition is unmarked, the transition *shall not* fire.⟧

⟦s3|*While* an inhibitor place of the transition is marked, the transition *shall not* fire.⟧

⟦s4|*While* the transition has no match specification ([NU-020]) and is enabled, it *shall* be able to fire, whatever its output places and reset places hold.⟧

⟦s5|*When* the transition fires, each input place that is not a reset place *shall* lose the consumption count of its input arc, and gain what the firing deposits there.⟧

⟦s6|*When* the transition fires, each place that is neither an input place nor a reset place *shall* lose no tokens, and gain what the firing deposits there.⟧

⟦s7|*When* the transition fires, each reset place *shall* end holding exactly what the firing deposited there.⟧

⟦s8|*When* the transition fires and the firing ends with its action, on an executor with output validation enabled ([CONC-026], the default), the places in which it deposits *shall* be exactly the places of one output branch of its output spec, each receiving one or more tokens.⟧

⟦s9|*When* the transition fires and the firing ends with the timeout outcome, it *shall* deposit in every place as many tokens as the timeout outcome puts there ([IO-013], [IO-014]).⟧

⟦s10|Deposits are compared per place: the order in which a firing deposits its tokens is not normative, and two deposits that put the same number of tokens in every place are the same deposit.⟧

⟦s11|As in [CORE-022], the transitions these sentences describe are transitions that build: a definition that building rejects is not a transition of any net and never fires.⟧

**Acceptance Criteria:**
1. Each arc type behaves exactly as described in the table.
2. An action that writes two tokens into one place of the output branch it satisfies, and one
   token into each other place of that branch, fires; the marking receives all of them
   ([IO-015], [IO-016] AC4).
3. Two firings that deposit the same number of tokens in every place, in different orders,
   deposit the same outcome.

**Test derivation:** One test per arc type verifying semantics. `t: a → and(b, c)` whose action writes `b`, `b`, `c`: verify the firing succeeds and leaves 2 tokens in `b` and 1 in `c`. The same action writing `c`, `b`, `b`: verify the same marking."#
