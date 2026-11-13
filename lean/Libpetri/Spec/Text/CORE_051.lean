import Libpetri.Spec.Text

requirement_text CORE_051
  id "CORE-051"
  title "Passthrough Action"
  priority MUST
  kind F
  body r#"A built-in passthrough action that consumes input tokens and produces no output tokens. This is the default action for transitions without explicitly bound actions.

The built-in MUST be recognisable by identity, a stable singleton rather than a fresh closure per
call, so that [CORE-043] can reject a net pairing it with a declared output spec without claiming
a user-supplied action that happens to produce nothing.

⟦s1|*When* a transition fires under the built-in passthrough action, the action *shall* complete with no output token and *shall not* fail.⟧

⟦s2|The identity predicate *shall* accept the built-in passthrough action and reject every other action, including `fork()` ([CORE-052]) and a hand-written action that produces no token.⟧

⟦s3|*When* a transition is built without an action, the built transition *shall* carry the built-in passthrough action.⟧

⟦s4|Every retrieval of the built-in passthrough action *shall* yield the same instance, which the identity predicate accepts.⟧

**Acceptance Criteria:**
1. Passthrough action completes immediately.
2. No output tokens are produced.
3. Repeated retrieval of the built-in yields the same instance, and an identity predicate over it accepts the built-in and rejects every other action, including `fork()` ([CORE-052]).

**Test derivation:** Fire a sink transition with passthrough; verify no output tokens. Retrieve the built-in twice; verify identity."#
