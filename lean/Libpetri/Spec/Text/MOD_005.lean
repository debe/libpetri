import Libpetri.Spec.Text

requirement_text MOD_005
  id "MOD-005"
  title "Channel Declaration (interface transitions for synchronous fusion)"
  priority MUST
  kind B
  body r#"An **interface transition** (synchronous channel) declares:
1. A **name** unique within the interface (sharing namespace with port names is implementation-defined; collisions MUST be rejected if they share a namespace).
2. The underlying `Transition` from the body net it exposes.

A channel MAY be bound at composition time to a caller-side transition, producing a single merged transition in the composed net (see [MOD-021]). Channels are the synchronization primitive for cross-instance and host-instance coupling at the transition level; ports synchronize at the place level.

As in [MOD-006], a channel whose transition has the name of no body transition is rejected, a channel over a transition of the body is accepted, and a channel over a second transition object that has the name of a body transition is implementation-defined. For subnet definitions [MOD-006] settles the namespace choice of item 1: port names and channel names are two namespaces.

⟦s1|*If* two channels of the interface have the same name, *then* building the subnet definition *shall* fail.⟧

⟦s2|*If* a channel of the interface exposes a transition whose name is not the name of a transition of the built body, *then* building the subnet definition *shall* fail.⟧

⟦s3|*When* the net builder builds the body, the subnet definition builds without its channels, every channel exposes a transition of the built body, no two channels have the same name, and no channel has the name of a port, building the subnet definition with its channels *shall* succeed.⟧

**Acceptance Criteria:**
1. A channel can be declared with a name and a body transition.
2. The channel name is unique within its namespace.
3. The exposed transition's identity is preserved through the channel handle (see [MOD-011]).
4. A channel whose underlying transition is not present in the body net is rejected at build (see [MOD-006]).

**Test derivation:** Build an interface with one channel exposing a transition `attempt`; verify the channel handle resolves to the same transition identity in the renamed body. Attempt to declare two channels with the same name; verify rejection."#
