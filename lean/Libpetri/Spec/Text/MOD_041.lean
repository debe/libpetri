import Libpetri.Spec.Text

requirement_text MOD_041
  id "MOD-041"
  title "Debug Protocol Subnet Instances"
  priority SHOULD
  kind F
  body r#"The debug protocol's `Subscribed` response (live net inspection) SHOULD carry, in addition to the existing place and transition descriptors, an enumeration of **subnet instance descriptors**. The descriptors are computed from the names of the flat net alone. The **instance prefix** of a node name is the part of the name before its last `/`; a name without `/`, or whose only `/` is its first character, has none. The **listed places** of a net are the places that some arc or output specification of its transitions names: the debug protocol describes exactly these with a `PlaceInfo`, and a place that the builder holds but no arc or output names is not listed. Each descriptor describes one distinct instance prefix that some transition or listed place name carries, which is usually one top-level or nested instance of the composed net, and includes:

1. The instance prefix string (e.g., `b1` or `outer/inner`).
2. The originating subnet definition's name, where available.
3. The parameter value supplied at instantiation, where available.
4. The set of transitions whose instance prefix is the descriptor's prefix (full prefixed names).
5. The set of listed places whose instance prefix is the descriptor's prefix (full prefixed names, reported as the exposed places). After composition these are the instance's own internal places (not those of instances nested in it) and its unbound ports: a bound port takes the name of the caller place it is bound to.
6. An optional parent-prefix field: the instance prefix of the descriptor's own prefix, which names the enclosing instance of a nested one.

Current runtimes keep neither the definition name nor the parameter value after composition, so items 2 and 3 are absent.

An outer instance all of whose nodes sit in a nested instance has no descriptor of its own; the nested descriptor names it as its parent. A subnet that uses `/` in its own names (the place `s1/obs/TURN` of [MOD-040]) also yields a descriptor, here `s1/obs`, that is no instance. A hand-written net with a `/` in a name gets descriptors too. A session over an imported archive carries no net topology; its subnet instance list is not specified here.

In addition, individual `PlaceInfo` and `TransitionInfo` entries in the debug protocol SHOULD carry an optional `instancePrefix` field derived from the name's prefix portion, so clients that do not parse names themselves can group nodes.

⟦s1|*When* a debug session subscribed to a live net answers `Subscribed`, its subnet instance list *shall* hold exactly one descriptor for each distinct instance prefix that the name of some transition or listed place of the net carries, and no other descriptor.⟧

⟦s2|*When* a debug session subscribed to a live net answers `Subscribed`, each subnet instance descriptor *shall* list as its transitions exactly the transitions of the net whose instance prefix is the descriptor's prefix, and as its places exactly the listed places of the net whose instance prefix is the descriptor's prefix.⟧

⟦s3|*When* a debug session subscribed to a live net answers `Subscribed`, each subnet instance descriptor *shall* carry as its parent prefix the instance prefix of its own prefix, and no parent prefix when its own prefix has none.⟧

⟦s4|*When* a debug session subscribed to a live net answers `Subscribed`, the `instancePrefix` field of the `PlaceInfo` or `TransitionInfo` of every node *shall* be the instance prefix of the node's name, and *shall* be absent when the name has none.⟧

This requirement is observability-only; it does not change net behavior.

**Acceptance Criteria:**
1. A debug session subscribed to a live composed net receives a list of subnet instance descriptors with one entry per distinct instance prefix that some transition or listed place name carries.
2. Each descriptor's transition and exposed-place sets enumerate exactly the transitions and listed places whose instance prefix is the descriptor's prefix.
3. Each `PlaceInfo` and `TransitionInfo` whose node name has an instance prefix carries that prefix as `instancePrefix`, and one whose name has none carries no `instancePrefix`.
4. Nested instances are reported with their parent prefix.
5. A debug session subscribed to a live net with no `/` in any name returns an empty subnet-instance list and no `instancePrefix` fields.

**Depends on:** [MOD-010], [MOD-013]
**Test derivation:** Subscribe to a debug session for a two-instance pipeline; assert the response carries two instance descriptors with the correct prefix, transitions, and exposed places."#
