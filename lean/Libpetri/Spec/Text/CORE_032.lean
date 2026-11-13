import Libpetri.Spec.Text

requirement_text CORE_032
  id "CORE-032"
  title "Read Arc"
  priority MUST
  kind B
  body r#"A read arc (test arc) connects a place to a transition as a **positive precondition**.

⟦s1|*While* a read place of a transition is unmarked, the transition *shall not* fire.⟧

⟦s2|*While* a read place of a transition is marked, the read arc *shall not* affect whether the transition can fire or the marking its firing leaves.⟧

⟦s3|*When* a transition fires, each of its read places on which it has neither an input arc nor a reset arc *shall* end the firing with its token count before the firing plus the tokens the firing deposits there.⟧

The read arc does not consume tokens; the value of a read token is available to the action via the transition context.

A transition has no read arc on a place it has an input arc on: building such a transition fails ([EXEC-012]).

**Acceptance Criteria:**
1. Read place must have tokens for transition to be enabled.
2. Token remains in place after transition fires.
3. Action receives the read token value.

**Test derivation:** Create transition with read arc; fire transition; verify token still in place after firing."#
