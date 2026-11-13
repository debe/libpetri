import Libpetri.Spec.Text

requirement_text CORE_041
  id "CORE-041"
  title "Net Immutability"
  priority MUST
  kind B
  body r#"⟦s1|After construction, a Petri net definition is immutable.⟧ ⟦s2|The set of places, transitions, and their connections cannot be modified.⟧

⟦s3|*When* the build call of a net builder used as [CORE-040] describes is made, the call *shall* give the net that [CORE-040] describes, or report the rejection that [EXEC-042] describes, for all the places, transitions and terminal places added to that builder before the call, including those added before an earlier build call.⟧

⟦s4|*When* a net builder used as [CORE-040] describes has built a net and is used again, to add places, transitions or terminal places or to build again, the net it built *shall* keep the places, transitions and terminal places it had when it was built.⟧

**Acceptance Criteria:**
1. No mutation methods exist on the constructed net.
2. Collections returned by the net are unmodifiable or copies.

**Depends on:** [CORE-040], [EXEC-042]
**Test derivation:** Build a net; verify no mutation API exists."#
