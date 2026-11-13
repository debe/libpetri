import Libpetri.Spec.Text

requirement_text MOD_003
  id "MOD-003"
  title "Port Declaration (name + direction + place)"
  priority MUST
  kind B
  body r#"An **interface place** (port) declares:
1. A **name** unique within the interface.
2. A **direction**: `Input`, `Output`, or `InOut`.
3. The underlying `Place<T>` from the body net it exposes.

The exposed place MUST be a place of the subnet's body. Two distinct ports MAY expose the same body place, whatever their directions. When two ports expose one body place, a caller binds both to one caller place; which binding a composition keeps when they are bound to two different caller places is not defined ([MOD-020]).

⟦s1|*If* two ports of one interface have the same name, *then* building the subnet definition *shall* fail.⟧

⟦s2|*If* the net builder builds the body and a port exposes a place that is not a place of the built body, *then* building the subnet definition *shall* fail.⟧

⟦s3|*When* building a subnet definition succeeds, building it with one more port, whose name no port of the interface has and which exposes the place of one of its ports, *shall* also succeed, whatever the directions of the two ports.⟧

**Acceptance Criteria:**
1. A port can be declared with name, direction, and a body place.
2. The port name is unique within an interface (duplicate names rejected at build).
3. The exposed place's token type is preserved in the port's typed handle (see [MOD-011]).
4. A port whose underlying place is not present in the body net is rejected at build (see [MOD-006]).
5. Two ports with different names over one body place build, whatever their directions.

**Test derivation:** Build an interface with ports `in: Input<String>` and `out: Output<String>`; verify both names and directions retrievable. Attempt to declare two ports with the same name; verify rejection. Attempt to declare a port over a place not in the body; verify rejection. Declare a second port with another name over the place of `in`, once as `Input` and once as `Output`; verify that both subnets build."#
