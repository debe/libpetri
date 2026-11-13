import Libpetri.Spec.Text

requirement_text MOD_001
  id "MOD-001"
  title "SubnetDef Definition (open net + interface)"
  priority MUST
  kind F
  body r#"A **subnet definition** is an open Petri net fragment paired with a declared **interface**. The fragment is a structurally complete net definition (places, transitions, arcs, timing, priority, optional actions) per [CORE-040]; the interface enumerates which of its places are exposed as **ports** and which of its transitions are exposed as **synchronous channels**.

A subnet definition MAY be parameterised by a typed `Params` value supplied at instantiation time (see [MOD-010]). When unparameterised, the parameter type is the implementation's unit/void type.

Building a subnet definition fails in the cases of [MOD-006]; this requirement says what a successful build returns. The body is the net that the net builder builds from the declared places, transitions and terminal places ([CORE-040]), so its places include every place an arc of a body transition names. The order in which the interface lists its ports and channels is not specified. As in [TIME-010], the transitions of one body are assumed to have pairwise distinct names.

⟦s1|*When* building the subnet definition succeeds, its interface *shall* hold exactly the declared ports, each with the name, direction and place it was declared with.⟧

⟦s2|*When* building the subnet definition succeeds, its interface *shall* hold exactly the declared channels, each with the name and transition it was declared with.⟧

⟦s3|*When* building the subnet definition succeeds, its body *shall* hold the places and terminal places of the net that the net builder builds from the declaration, and the declared transitions in the order they were added, none of them renamed.⟧

⟦s4|*When* building the subnet definition succeeds, the subnet definition *shall* keep the name it was declared with.⟧

⟦s5|*When* the net builder builds the body and the interface declares no port and no channel, building the subnet definition *shall* succeed.⟧

**Acceptance Criteria:**
1. A subnet definition can be constructed with a body net and an interface.
2. The body net follows all CORE construction rules and is itself immutable per [CORE-041].
3. The interface enumerates a (possibly empty) set of ports and a (possibly empty) set of channels.
4. The subnet definition exposes both `body()` (the unrenamed body) and `iface()` (the interface) for inspection.
5. A subnet definition is immutable after construction.

**Test derivation:** Build a subnet definition with two places and one transition, exposing one place as a port; verify body, interface, port set, and channel set are accessible and unmodifiable."#
