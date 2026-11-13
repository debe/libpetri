import Libpetri.Spec.Text

requirement_text MOD_014
  id "MOD-014"
  title "SubnetDef.fromNet retrofit utility"
  priority MUST
  kind B
  body r#"Implementations MUST provide a utility `fromNet(net, iface)` that constructs a subnet definition from an existing closed `PetriNet` plus an interface declaration whose ports and channels expose places and transitions of that net. This allows pre-existing nets to be wrapped as reusable subnet fragments without rebuilding them. It is also how a subnet definition whose body holds a composed instance is built, which nested instantiation needs ([MOD-013]).

The retrofit utility MUST validate the interface against the supplied net per [MOD-006] (port places exist, channel transitions exist, names unique). The net is already built, so the body rejection of [MOD-006] (case 5) does not arise. A net that declares terminal places ([EXEC-042]) is accepted by `fromNet` and refused when the definition is instantiated ([MOD-010]).

As in [MOD-006], a channel over a transition of the net is accepted and a channel whose transition has the name of no transition of the net is rejected. Whether a channel over a second transition object that has the name of a net transition is accepted is implementation-defined: Java and TypeScript compare transition objects and reject it, Rust and Python compare names and accept it. After a composition the net holds rewritten transitions, so a channel exposes the transition taken from the net.

An interface holds at most one port and at most one channel of each name in every implementation, because the interface builder rejects a second declaration of a name; `fromNet` checks the names again. Port names and channel names are two namespaces, as in [MOD-006].

⟦s1|*If* a port of the interface exposes a place that is not a place of the net, *then* `fromNet` *shall* fail.⟧

⟦s2|*If* a channel of the interface exposes a transition whose name is not the name of a transition of the net, *then* `fromNet` *shall* fail.⟧

⟦s3|*If* two ports of the interface have the same name, *then* `fromNet` *shall* fail.⟧

⟦s4|*If* two channels of the interface have the same name, *then* `fromNet` *shall* fail.⟧

⟦s5|*When* every port of the interface exposes a place of the net, every channel exposes a transition of the net, and no two ports and no two channels have the same name, `fromNet` *shall* succeed.⟧

⟦s6|*When* `fromNet` succeeds, the subnet definition *shall* have the net's name, the net's places, transitions and terminal places as its body, with the transitions in the net's order, and the given ports and channels as its interface.⟧

⟦s7|*When* `fromNet` fails, the error message *shall* contain the name of a port or channel that meets one of the four rejection cases above.⟧

**Acceptance Criteria:**
1. `fromNet(net, iface)` produces a subnet definition whose body equals the supplied net (modulo immutability semantics).
2. The interface validation rules of [MOD-006] apply.
3. The resulting subnet definition is unparameterised (its parameter type is the implementation unit/void type).

**Test derivation:** Build a `PetriNet` with places `a`, `b`; call `fromNet(net, iface{port: in -> a})`; verify the resulting subnet exposes port `in` over place `a`."#
