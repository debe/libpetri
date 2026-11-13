import Libpetri.Spec.Text

requirement_text CORE_020
  id "CORE-020"
  title "Transition Definition"
  priority MUST
  kind F
  body r#"A transition is a named element that consumes tokens from input places, executes an action, and produces tokens to output places. Each transition has:
- A name (identifies the transition, see [TIME-010])
- Input specifications with cardinality (see [IO-001])
- An output specification with routing structure (see [IO-010])
- Zero or more inhibitor arcs
- Zero or more read arcs
- Zero or more reset arcs
- A timing specification (see [TIME-001])
- A priority value (integer, higher = fires first)
- An action to execute

⟦s1|*When* a transition is built, the built transition *shall* carry the name and the output specification it was given, if any, and each of its input, inhibitor, read and reset arc lists exactly as given, in the order given and with its repetitions.⟧

⟦s2|*When* a transition is built with a timing, a priority or an action, the built transition *shall* carry that timing, priority or action.⟧

⟦s3|*When* a transition is built without a priority, the built transition *shall* have priority 0.⟧

⟦s4|Building a transition that has no match specification ([NU-020]) *shall* succeed exactly when its arcs and output specification pass the build-time checks and the timing it is given, if any, is valid ([TIME-001]).⟧

**Acceptance Criteria:**
1. A transition can be constructed with all the above fields via a builder pattern.
2. All fields are accessible after construction.

**Test derivation:** Build a transition with inputs, outputs, inhibitors, reads, resets, timing, priority, and action; verify all fields match."#
