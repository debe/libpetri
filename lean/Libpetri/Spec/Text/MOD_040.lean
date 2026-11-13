import Libpetri.Spec.Text

requirement_text MOD_040
  id "MOD-040"
  title "Export Grouping (subgraph cluster_* per instance prefix)"
  priority SHOULD
  kind F
  body r#"⟦s1|DOT export per [EXP-001] of a composed net SHOULD emit a `subgraph cluster_<sanitizedKey>` block grouping the nodes of each subnet.⟧ The exporter determines a node's cluster key from one of two sources:

- **Subnet-membership metadata** ([MOD-026]), when the net carries any. A node mapped to subnet `S` is grouped under `cluster_<sanitize(S)>`; a node with no entry (a shared rendezvous place, or a node from instance composition) is not grouped by metadata.
- **Instance-prefix detection**, the fallback. A node whose name begins with `<prefix>/` is grouped under `cluster_<sanitize(prefix)>`; nested instance prefixes (per [MOD-013]) produce nested cluster subgraphs.

When the net carries membership metadata, the exporter SHOULD prefer it, and SHOULD fall back to instance-prefix detection for any node without a metadata entry, so a builder that mixes direct and instance composition keeps both cluster kinds. The cluster source MAY be made caller-selectable (e.g. an explicit metadata-only, prefix-only, or no-clustering override); the default SHOULD be the metadata-when-present behaviour above.

**The rule as an accessor.** Membership metadata answers "which subnet does this node belong to" only for direct composition, and the prefix answers it only for instance composition ([MOD-026] rule 4). The net SHOULD expose the combined answer as `subnetOf(name)`, which follows the default (`AUTO`) cluster rule above without its nesting, except that the prefix it falls back to is one some transition lives under:

1. `name` is not a place or transition of the net → absent;
2. else the membership entry for `name`, when there is one;
3. else the longest `/`-prefix of `name` that some transition of the net lives under: of the prefixes of `name` ending before one of its `/` characters, taken from longest to shortest (`a/b/c/x` gives `a/b/c`, then `a/b`, then `a`), the first non-empty `P` such that at least one transition of the net has a name beginning with `P/`;
4. else absent.

Step 3 walks up because a subnet may use `/` inside its own namespace: an instance `s1` whose body has a place `obs/TURN` contributes `s1/obs/TURN`, and the part before the last `/`, `s1/obs`, is no instance and carries no transition. Reading it as a subnet made encapsulation checks report a place of `s1` as belonging to a subnet of its own. For a transition name step 3 returns its own instance prefix (the transition itself begins with it), so transitions are attributed as by the part before the last `/`. The set of prefixes that head a transition SHOULD be computed once per net, lazily, so `subnetOf` costs O(depth of the name).

`subnetOf` therefore differs from the DOT `AUTO` cluster rule for a name with `/` inside a subnet's own namespace: the exporter still clusters `s1/obs/TURN` under `s1/obs`. The exporter's instance-prefix helper and its clustering are unchanged by this rule. `subnetOf` is additive: no export output, membership mapping or event changes.

⟦s2|For `subnetOf` and the instance-prefix helper, the SHOULD priority is whether an implementation offers them at all; an implementation that offers them answers as the next six sentences say.⟧

⟦s3|In the four sentences on `subnetOf` that follow, a `/`-prefix of a name is a non-empty beginning of the name that is immediately followed by a `/`, and a `/`-prefix `P` heads a transition of the net when the name of some transition of the net begins with `P/`.⟧

⟦s4|*If* `name` is neither a place nor a transition of the net, *then* `subnetOf(name)` *shall* be absent.⟧

⟦s5|*When* `name` is a place or a transition of the net and the net's membership mapping ([MOD-026]) has an entry for `name`, `subnetOf(name)` *shall* return that entry.⟧

⟦s6|*When* `name` is a place or a transition of the net with no membership entry and some `/`-prefix of `name` heads a transition of the net, `subnetOf(name)` *shall* return the longest such `/`-prefix.⟧

⟦s7|*When* `name` is a place or a transition of the net with no membership entry and no `/`-prefix of `name` heads a transition of the net, `subnetOf(name)` *shall* be absent.⟧

⟦s8|The instance-prefix helper (`instancePrefixOf`) *shall* return the part of a name before its last `/` when that part is not empty, and be absent otherwise.⟧

⟦s9|The sanitization function applied to the key MUST match the existing DOT ID sanitization per [EXP-014] (non-`[A-Za-z0-9_]` characters, including `/`, replaced by `_`).⟧

The cluster label SHOULD be the original (un-sanitized) key string (the prefix, or the subnet name) for human readability.

⟦s10|This requirement does NOT change the styling, junction, or arc-rendering rules of EXP-002..EXP-015; it only adds grouping structure.⟧

⟦s11|For the export half of this requirement (the sentences on DOT export: the opening sentence and its two bullets, the preference and cluster-source sentences, the sanitization and label sentences and the sentence on EXP-002..EXP-015), the SHOULD priority is whether an exporter draws cluster subgraphs at all; an exporter that draws them reads every MAY, SHOULD and MUST sentence of the export half as *shall*, lets the caller select the metadata-only, prefix-only and no-clustering sources, uses the default source when the caller selects none, takes the cluster key of a node and the covered nets as [EXP-016] defines them, and follows the next three sentences, which restate shall sentences of [EXP-016].⟧

⟦s12|The exporter *shall* make each node that has a cluster key a direct member of the cluster of that key and of no other cluster, make a node without a cluster key a member of no cluster, and list as a member of a cluster only a node it draws.⟧

⟦s13|The exporter *shall* draw exactly one cluster for each cluster key of a drawn node and for each `/`-prefix of such a key and no other cluster, nest each cluster directly in the cluster whose key is the part of its own key before the last `/` and draw a cluster whose key has no `/` at the top level, and give the cluster of key K the ID `cluster_` followed by K sanitized per [EXP-014] and the label K.⟧

⟦s14|The exporter *shall* draw, in any order, the same nodes, and the same edges other than the ghost edges of [EXP-017], as it draws for the same net and configuration under no clustering.⟧

**Acceptance Criteria:**
1. Compose two instances with prefixes `b1` and `b2`; export DOT; verify the output contains `subgraph cluster_b1 { ... }` and `subgraph cluster_b2 { ... }` blocks.
2. Each cluster block contains, directly or through the cluster blocks nested in it, exactly the places and transitions whose cluster key is the cluster's key or begins with it followed by `/`, and the junction nodes of those transitions.
3. Nested instance prefixes produce nested cluster subgraphs.
4. A net with no composed instances and no membership metadata (no `/` in any name) produces no cluster subgraphs.
5. Cluster IDs match the regex `cluster_[A-Za-z0-9_]+` (sanitized per [EXP-014]).
6. A net carrying [MOD-026] membership metadata emits a `subgraph cluster_<subnetName>` block per subnet; each subnet's private nodes appear inside its block and a shared (multi-subnet) place whose name has no instance prefix appears at the top level.
7. With both membership metadata and `prefix/`-named instance nodes in one net, metadata-mapped nodes cluster by subnet name and prefix-named nodes cluster by prefix.
8. `subnetOf` on a directly composed node returns its subnet name; on an instance-composed node `b1/inner/p` of a net with a transition `b1/inner/t` it returns `b1/inner`; on a shared rendezvous place without `/`, a flat node without `/`, and a name the net does not declare, it is absent.
9. `subnetOf` walks up to a prefix some transition lives under: with a transition `s1/t`, the place `s1/obs/TURN` gives `s1`; a place `x/y` with no transition under `x/` is absent; with a nested transition `outer/inner/t`, the place `outer/inner/p` gives `outer/inner`; a membership entry wins over all of these. The DOT export of the same nets is byte-identical to before.

**Implementation notes:**
- Java: `PetriNet.subnetOf(String)` returns `Optional<String>`; the prefix helper is
  `org.libpetri.export.SubnetPrefixes.instancePrefixOf`.
- TypeScript: `PetriNet.subnetOf(name)` returns `string | undefined`; `instancePrefixOf` is
  exported from `libpetri/export`.
- Rust: `PetriNet::subnet_of(&self, name)` returns an `Option`; the prefix helper is
  `libpetri_core::subnet_prefixes::instance_prefix_of`, re-exported from
  `libpetri_export::subnet_prefixes`.
- Python: `Net.subnet_of(name) -> str | None`, and `Net.subnet_membership`, the [MOD-026]
  mapping as a `dict`.

**Depends on:** [MOD-010], [MOD-013], [MOD-026], [EXP-001], [EXP-014], [EXP-016]
**Test derivation:** Build a composed net with two top-level instances; export; assert cluster blocks present with correct membership and IDs. Build a directly-composed net of two subnets; export; assert one `subgraph cluster_<subnetName>` per subnet with the shared place, named without `/`, at top level."#
