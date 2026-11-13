import Libpetri.Spec.Text

requirement_text EXP_016
  id "EXP-016"
  title "Subnet Instance Cluster Subgraphs"
  priority SHOULD
  kind F
  body r#"⟦s1|DOT export of a net produced by modular composition (per [MOD-020]) SHOULD emit a `subgraph cluster_<sanitizedKey>` block grouping each subnet's nodes.⟧ The cluster key is drawn from one of two sources, per [MOD-040]:

- ⟦s2|**Subnet-membership metadata** ([MOD-026]) carried by a directly-composed net — a node mapped to subnet `S` clusters under `cluster_<sanitize(S)>`; a shared (multi-subnet) place has no entry and is not grouped by metadata.⟧
- ⟦s3|**Instance-prefix detection** — a node whose name begins with `<prefix>/` (the separator established by [MOD-010]) clusters under `cluster_<sanitize(prefix)>`. Nested instance prefixes (per [MOD-013]) MUST produce nested cluster subgraphs.⟧

⟦s4|When the net carries membership metadata the exporter SHOULD prefer it and fall back to instance-prefix detection for any node without an entry, so direct and instance composition coexist.⟧ ⟦s5|The cluster source MAY be caller-selectable (metadata-only, prefix-only, or no clustering); the default SHOULD be metadata-when-present.⟧

⟦s6|The sanitization function applied to the key MUST match the existing DOT ID sanitization per [EXP-014] (non-`[A-Za-z0-9_]` characters, including `/`, replaced by `_`). The cluster `label` attribute SHOULD carry the original (un-sanitized) key string for human readability.⟧

⟦s7|This requirement does NOT alter the styling, junction, or arc rendering rules of EXP-002..EXP-015; it adds grouping structure only. A net with neither composed instances nor membership metadata (no `/` in any node name) MUST produce no cluster subgraphs.⟧

⟦s8|The SHOULD priority is whether an exporter draws cluster subgraphs at all. For an exporter that draws them, every MAY, SHOULD and MUST sentence of this requirement reads as *shall*: it lets the caller select each cluster source named above, takes the default source when the caller selects none, and follows the sentences below.⟧

⟦s9|Under the default cluster source the cluster key of a place or a transition is its membership entry when it has one and otherwise its instance prefix; under the metadata-only source it is the membership entry alone, under the prefix-only source the instance prefix alone, and under no clustering there is none. The instance prefix of a name is the part before its last `/`; a name without `/`, or whose only `/` is its first character, has none. A junction node has the cluster key of its transition. A node without a cluster key is a top-level node. A `/`-prefix of a key is the non-empty beginning of the key up to, and not including, one of its `/` characters.⟧

⟦s10|These sentences cover nets whose place names and transition names are ASCII, in which no two place names and no two transition names become equal under the sanitization of [EXP-014], and in which every cluster key of a place or transition name is ASCII, non-empty and has no empty `/`-segment: it neither starts nor ends with `/` and holds no `//`. On other nets the clustering, and whether it changes the nodes and edges drawn, is implementation-defined.⟧

Known limit: the Java, TypeScript and Rust mappers look a node's cluster key up by its DOT ID, so two names that sanitize to one ID, such as `b1/x` and `b1_x`, become one node in one cluster. The name assumption above keeps such nets out of these sentences.

⟦s11|The mapper *shall* make each node that has a cluster key a direct member of the cluster of that key and of no other cluster, and a top-level node a member of no cluster.⟧

⟦s12|The mapper *shall* list as a member of a cluster only a node it draws, and, on a net whose transition names are pairwise distinct, list each such node at most once.⟧

⟦s13|The mapper *shall* draw exactly one cluster for each cluster key of a drawn node and for each `/`-prefix of such a key, and no other cluster.⟧

⟦s14|The mapper *shall* nest each cluster directly in the cluster whose key is the part of its own key before the last `/`, and draw a cluster whose key has no `/` at the top level.⟧

⟦s15|The mapper *shall* give the cluster of key K the ID `cluster_` followed by K with each character outside `[A-Za-z0-9_]` replaced by `_`, and the label K.⟧

⟦s16|The mapper *shall* draw, in any order, the same nodes, and the same edges other than the ghost edges of [EXP-017], as it draws for the same net and configuration under no clustering.⟧

**Acceptance Criteria:**
1. A net composed from two top-level instances with prefixes `b1` and `b2` exports DOT containing `subgraph cluster_b1 { ... }` and `subgraph cluster_b2 { ... }` blocks.
2. Each cluster block contains, directly or through the cluster blocks nested in it, exactly the places and transitions whose cluster key is the cluster's key or begins with it followed by `/`, and the junction nodes of those transitions.
3. Nested instances produce nested cluster subgraphs (e.g., `cluster_outer` containing `cluster_outer_inner`).
4. A net with no `/` in any node name and no membership metadata produces no cluster subgraphs.
5. Cluster IDs match the regex `cluster_[A-Za-z0-9_]+` and are deterministic across repeated exports.
6. Java, TypeScript, and Rust mappers produce byte-identical cluster blocks (subject to MOD support in each language) for the same composed input.
7. A directly-composed net carrying [MOD-026] metadata exports one `subgraph cluster_<subnetName>` block per subnet, with each subnet's private nodes inside and shared places whose names carry no instance prefix at the top level.

**Depends on:** [EXP-001], [EXP-014], [MOD-010], [MOD-026], [MOD-040]
**Test derivation:** Compose two instances with prefixes `b1` and `b2`; export DOT; assert cluster blocks present, members correct, IDs sanitized. Compose nested instances; assert nested cluster subgraphs. Direct-compose two subnets; assert one `cluster_<subnetName>` block per subnet."#
