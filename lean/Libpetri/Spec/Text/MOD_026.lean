import Libpetri.Spec.Text

requirement_text MOD_026
  id "MOD-026"
  title "Subnet-Membership Metadata for Direct Composition"
  priority SHOULD
  kind B
  body r#"Direct composition per [MOD-025] erases the `prefix/` name segments that
[MOD-040] and [EXP-016] rely on to reconstruct subnet clusters. To keep
cluster-aware export available for directly-composed nets, the builder SHOULD
record **subnet-membership metadata** on the net it builds: a mapping from node
name (place or transition) to the name of the owning subnet.

The mapping is resolved from the per-`compose(SubnetDef)` contributions:

1. Every body place and every body transition of a `compose(SubnetDef)` call is
   recorded, by name, as contributed by that subnet (its definition name per
   [MOD-001]), also when the builder already held a place of that name. Subnets
   are told apart by their recorded names. A call that fails records nothing.
2. A node contributed by **exactly one** subnet maps to that subnet.
3. A place contributed by **two or more** subnets is a shared rendezvous place
   with no single owner and MUST be **absent** from the mapping (it renders
   outside any cluster). A transition cannot be multiply-contributed: the
   transition-name-collision rejection of [MOD-025] forbids it.
4. A node of a net not built via direct composition is absent from the mapping.
   Instance composition per [MOD-020] and [MOD-024] records no membership: those nodes carry
   their `prefix/` names and cluster via [MOD-040]'s name-based detection. A
   caller that wants one answer for both kinds of composition asks the net's
   `subnetOf(name)` accessor ([MOD-040]), which reads this mapping first and
   falls back to the instance prefix; the mapping itself stays empty for
   instance-composed nodes.

A subnet definition name containing the `/` separator MUST be sanitized (each
`/` replaced by `_`) before it is recorded, so a membership value never triggers the
nested-cluster splitting that [MOD-040] applies to `/`-bearing prefixes.

The mapping is immutable, carried on the built net, and observability-only: it
does NOT affect execution, marking, or any property of [MOD-023] (the net is
still flat). Action binding per [CORE-042] rebuilds transitions but preserves
their names, so the mapping survives a re-bind unchanged. Fusion per [MOD-061]
removes the non-canonical places it merges away; their membership entries MUST
be dropped so the mapping names only nodes that still exist.

⟦s1|*When* a `compose(SubnetDef)` call succeeds, the builder *shall* record each body place and each body transition of the subnet definition, by name, as contributed by that subnet under the definition's name with each `/` replaced by `_`.⟧

⟦s2|The builder *shall* record contributions only in `compose(SubnetDef)` calls.⟧

⟦s3|*When* a node name is recorded as contributed by exactly one subnet, the resolution of the recorded contributions *shall* map that node name to that subnet.⟧

⟦s4|*If* a node name is recorded as contributed by two or more different subnets, *then* the resolution *shall* have no entry for that node name.⟧

⟦s5|*If* a node name is recorded as contributed by no subnet, *then* the resolution *shall* have no entry for that node name.⟧

⟦s6|*When* a build succeeds, the membership mapping of the built net *shall* be the resolution of the contributions the build recorded, except for the names of the places that fusion ([MOD-061]) removed.⟧

⟦s7|*If* fusion removes a member place other than the first member of its fusion set, *then* the membership mapping of the built net *shall* have no entry for that member's name.⟧

⟦s8|*When* a build succeeds, a build that differs from it only in the names of the subnet definitions it composes directly *shall* also succeed and give the same places, transitions, terminal places and transition correspondences ([MOD-031]).⟧

⟦s9|*When* actions are bound to a built net ([CORE-042]), the net that binding returns *shall* carry the same membership mapping.⟧

**Acceptance Criteria:**
1. Direct-composing two subnets `A` and `B` records each private node under its
   subnet: a place or transition contributed only by `A` maps to `A`.
2. A place named identically in two directly-composed subnets whose recorded
   names differ is absent from the mapping.
3. A net not built via direct composition (flat, or instance-composed) has an
   empty membership mapping.
4. Direct-composing the same subnets in opposite orders yields equal mappings.
5. Fusing away a non-canonical place removes its membership entry; the
   surviving canonical place keeps its own.
6. A subnet definition name containing `/` is recorded with `/` replaced.

**Depends on:** [MOD-025], [MOD-023], [MOD-001]
**Test derivation:** Direct-compose a producer subnet and a consumer subnet
sharing a place `pipe`; assert each subnet's private place/transition maps to
its subnet name and `pipe` is absent. Build a flat net; assert an empty
mapping. Direct-compose then fuse two places; assert the non-canonical place's
entry is gone."#
