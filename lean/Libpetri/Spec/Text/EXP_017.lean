import Libpetri.Spec.Text

requirement_text EXP_017
  id "EXP-017"
  title "Compound Cluster Layout Hints"
  priority SHOULD
  kind F
  body r#"⟦s1|DOT export SHOULD set `compound=true` at the digraph level unconditionally so Graphviz honours `lhead` and `ltail` attributes on edges that cross cluster boundaries.⟧ This is a no-op for flat (uncomposed) nets but keeps the digraph header uniform across all exports.

⟦s2|In this requirement the cluster key of a node is its key under [EXP-016], so a node with a key lies in the deepest cluster of that key, and an orphan is a node with no key, which is drawn at the top level.⟧ ⟦s3|An edge is an edge of the exported graph other than a ghost edge, of any arc type, in the direction it is drawn, and either end of it may be a junction node ([EXP-012]).⟧ ⟦s4|A bridge for an ordered pair of distinct keys (X, Y) is an orphan `o` together with an edge `a → o` from a node `a` with key X and an edge `o → b` to a node `b` with key Y, so one orphan with several such pairs of edges gives several bridges.⟧ ⟦s5|A cluster and a cluster nested in it, such as `outer` and `outer/inner`, have two distinct keys, so an orphan between them bridges them.⟧

⟦s6|For every ordered pair of distinct cluster keys (X, Y) that at least one bridge connects, the exporter MUST emit exactly one invisible ghost edge with:⟧

- `style = invis` (no visible artifact; pure layout constraint)
- `arrowhead = none`
- ⟦s7|`ltail = "cluster_" + sanitize(X)` (matches the cluster id defined by [EXP-016])⟧
- ⟦s8|`lhead = "cluster_" + sanitize(Y)`⟧

⟦s9|The ghost edge's source and target node ids MUST be the `a` and the `b` of the first bridge for (X, Y) in this scan order: the nodes in the order they are drawn, for each orphan the edges into it in the order they are drawn, and for each of those the edges out of it in the order they are drawn.⟧ Graphviz then has a real cluster-to-cluster connection to constrain layout, while the visible flow still passes through the orphan via the original real edges.

⟦s10|Because every drawn edge counts, a reset edge into an orphan place and a read edge out of it bridge two clusters although no token moves between them.⟧ ⟦s11|An orphan transition whose output spec has a junction bridges nothing through that junction, since the junction is itself an orphan.⟧

⟦s12|Multiple orphans bridging the same ordered cluster pair `(X, Y)` collapse to one ghost edge (dedup by ordered pair).⟧ ⟦s13|The reverse direction `(Y, X)` is a separate ghost edge when its own 1-hop path exists.⟧ ⟦s14|Orphan paths that fall entirely inside a single cluster (`X == Y`) or that only touch one clustered neighbour MUST NOT produce a ghost edge.⟧

⟦s15|This requirement does NOT change [EXP-016] cluster membership, the visible edge set, or styling rules.⟧ It only adds the `compound=true` graph attribute and the synthesized ghost edges.

⟦s16|Apart from the `compound` attribute, these sentences cover the nets that the sentences of [EXP-016] cover; on other nets the ghost edges, and whether clustering changes the other edges drawn, are implementation-defined.⟧

⟦s17|The exporter *shall* set the graph attribute `compound` to true in every export.⟧

⟦s18|*Where* a bridge connects an ordered pair of distinct cluster keys (X, Y), an exporter that clusters *shall* draw a ghost edge from the `a` to the `b` of the first bridge for (X, Y), with `ltail` the cluster ID of X and `lhead` the cluster ID of Y.⟧

⟦s19|Each ghost edge that an exporter that clusters draws *shall* run from the `a` to the `b` of the first bridge for some ordered pair of distinct cluster keys (X, Y), with `ltail` the cluster ID of X and `lhead` the cluster ID of Y.⟧

⟦s20|An exporter that clusters *shall* draw at most one ghost edge for each ordered pair of cluster keys.⟧

⟦s21|The exporter *shall* draw the same edges other than ghost edges as it draws for the same net with no clustering.⟧

**Acceptance Criteria:**
1. Every DOT export contains `compound="true"` as a top-level graph attribute.
2. A net where `cluster_left` and `cluster_right` are bridged by a single orphan transition produces exactly one ghost edge with `style=invis`, `arrowhead=none`, `ltail="cluster_left"`, `lhead="cluster_right"`.
3. Three orphans bridging the same `(left, right)` pair still produce exactly one ghost edge (dedup by ordered pair).
4. Bidirectional bridging (`left → o1 → right` and `right → o2 → left`) produces two ghost edges, one per direction.
5. An orphan with `X → o → X` (same cluster on both sides) produces no ghost edge.
6. An orphan with only one clustered neighbour produces no ghost edge.
7. A flat net (no instance prefixes) produces no ghost edges but still emits `compound="true"`.
8. Anchor node selection is deterministic and matches across Java, TypeScript, and Rust exporters byte-for-byte for the same composed input.

**Depends on:** [EXP-012], [EXP-014], [EXP-016]
**Test derivation:** Build a composed net with two instances and an orphan transition between them; export DOT in each language; assert one `style="invis"` edge with matching `ltail`/`lhead`. Add bidirectional and multi-orphan variants. Verify `compound="true"` on a flat net."#
