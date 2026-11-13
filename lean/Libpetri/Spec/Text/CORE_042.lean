import Libpetri.Spec.Text

requirement_text CORE_042
  id "CORE-042"
  title "Action Binding Separation"
  priority MUST
  kind F
  body r#"⟦s1|The net's static structure (places, transitions, arcs, timing, priority) MUST be separable from the runtime behavior (actions).⟧ ⟦s2|A `bindActions()` operation takes a structure and a mapping of transition names to actions, producing a new net with actions bound.⟧

⟦s3|*When* actions are bound to a net, in either form, the new net *shall* have the name, the places and the terminal places of the original net and, for each transition of the original net, in the same order, a transition with the same name, arcs, output specification, timing and priority.⟧

⟦s4|*When* actions are bound with a resolver that returns an action for a transition's name, the transition *shall* carry that action in the new net.⟧

⟦s5|*When* actions are bound with a resolver that returns no action (`null`/`None`) for a transition's name, the transition *shall* carry in the new net the action it carried before.⟧

⟦s6|*When* actions are bound with a mapping that maps a transition's name to an action, the transition *shall* carry that action in the new net.⟧

⟦s7|*When* actions are bound with a mapping whose values are actions and that does not map a transition's name, the transition *shall* carry in the new net either the passthrough action or the action it carried before, and an implementation makes the same one of these two choices for every transition, every net and every mapping, so a transition that carried passthrough still carries passthrough.⟧

⟦s8|*When* actions are bound to a net, in either form, a transition that has a match specification ([NU-020]) *shall* have the same match specification in the new net.⟧

⟦s9|Binding actions to a net *shall* return a new net for every net and every resolver or mapping, and *shall* leave the original net unchanged.⟧

**Acceptance Criteria:**
1. A net can be created with no actions (all transitions use passthrough).
2. `bindActions(mapping)` produces a new net with actions bound by transition name.
3. The original net is not modified.
4. Unbound transitions retain the passthrough action.

⟦s10|Binding is lazy and total: it never rejects, so a partially bound net is a legitimate intermediate
value and an action MAY be bound after instantiation ([MOD-031] AC7); the declared structure is
reconciled against the bound behaviour at compile time ([CORE-043]).⟧ ⟦s11|**Divergence:** the map form
substitutes passthrough for every transition the map omits in Java and TypeScript (so a second call
clobbers the first's bindings) but leaves them untouched in Rust; only the resolver form, where a
`null`/`None` result defers a transition, binds in stages identically across implementations.⟧
⟦s12|In Java a mapping may hold a name with a `null` value, and the map form then defers that transition
as the resolver form does; TypeScript substitutes passthrough for a `null` or `undefined` value.⟧

The same operation exists on a subnet definition ([MOD-051]): `SubnetDef.bindActions` takes the
same argument forms, keyed by the definition's unprefixed transition names, treats unnamed
transitions exactly as the net-level form does in the same language, and returns a new definition.

**Test derivation:** Create a net with 3 transitions; bind actions for 2; verify the third still has passthrough."#
