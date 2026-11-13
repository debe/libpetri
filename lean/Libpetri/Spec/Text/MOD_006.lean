import Libpetri.Spec.Text

requirement_text MOD_006
  id "MOD-006"
  title "Subnet Validation at Build"
  priority MUST
  kind B
  body r#"Construction of a subnet definition MUST validate the interface against the body before producing an immutable result. The body is the net that the net builder builds, and the places and transitions of the body are those of that net ([CORE-040]). Validation MUST reject:
1. A port whose underlying place is not present in the body.
2. A channel whose underlying transition is not present in the body.
3. Duplicate port names within the interface.
4. Duplicate channel names within the interface.
5. A body that the net builder rejects ([CORE-040], [EXEC-042]).

Each failure MUST produce an error identifying the offending element by name.

Duplicate names (cases 3 and 4) do not depend on the body and may be checked before the body is built. Port names and channel names are two namespaces: a port and a channel may have the same name. This settles for subnet definitions the choice that [MOD-005] leaves to the implementation.

A channel whose transition has the name of no body transition is rejected in every implementation (case 2), and a channel over a transition of the body is accepted in every implementation. Whether a channel over a second transition object that has the name of a body transition is accepted is implementation-defined: Java and TypeScript compare transition objects and reject it, Rust and Python compare names and accept it. As in [TIME-010], the transitions of one body are assumed to have pairwise distinct names; no builder checks this.

A terminal place that the body declares ([EXEC-042]) and that no body transition consumes from or reads is not by itself a reason to reject at subnet build; `instantiate` and composition refuse such a body ([EXEC-042], [MOD-010]).

⟦s1|*If* a port of the interface exposes a place that is not a place of the built body, *then* building the subnet definition *shall* fail.⟧

⟦s2|*If* a channel of the interface exposes a transition whose name is not the name of a transition of the built body, *then* building the subnet definition *shall* fail.⟧

⟦s3|*If* two ports of the interface have the same name, *then* building the subnet definition *shall* fail.⟧

⟦s4|*If* two channels of the interface have the same name, *then* building the subnet definition *shall* fail.⟧

⟦s5|*If* the net builder rejects the body, *then* building the subnet definition *shall* fail.⟧

⟦s6|*When* the net builder builds the body, every port exposes a place of the built body, every channel exposes a transition of the built body, and no two ports and no two channels have the same name, building the subnet definition *shall* succeed.⟧

⟦s7|*When* building the subnet definition fails, the error message *shall* contain the message with which the net builder rejected the body, or the name of a port or channel that meets one of the rejection cases 1 to 4.⟧

**Acceptance Criteria:**
1. Each rejection case above produces an error at subnet build, not later at instantiation or composition.
2. Error messages name the offending port, channel, place, or transition.
3. A valid subnet definition is immutable after build.

**Depends on:** [CORE-040], [CORE-041]
**Test derivation:** Construct invalid subnets covering rejection cases 1 to 4; verify each fails at build with a message naming the offending element. Case 5 has no test: the subnet-definition builder takes only places, transitions, ports and channels, the net builder rejects none of these on its own, and `fromNet` ([MOD-014]) takes a net that is already built."#
