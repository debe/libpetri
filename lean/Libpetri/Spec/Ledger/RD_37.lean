import Libpetri.Spec.Ledger
import Libpetri.Spec.Req.EXP_017
import Libpetri.Spec.Text.EXP_017

runtime_defect RD_37
  title "Java and TypeScript dedup ghost edges by a NUL-joined string"
  requirements r#"EXP-017 (line 2: a ghost edge for every bridged ordered pair of cluster keys;
'dedup by ordered pair')."#
  runtimes r#"Java, TypeScript."#
  defect r#"`synthesizeGhostEdges` keys the dedup map by the string `x + "\0" + y`, not by the
ordered pair. A cluster key may hold the NUL character (it is ASCII, inside EXP-016's name
assumption, and no builder checks place names), so the distinct pairs (`a\0b`, `c`) and
(`a`, `b\0c`) share the key `a\0b\0c` and the second pair gets no ghost edge.
`java/src/main/java/org/libpetri/export/ClusterBuilder.java`,
`typescript/src/export/cluster-builder.ts`. Rust keys the dedup map by the
`(String, String)` pair (`rust/libpetri-export/src/cluster_builder.rs`, ghost synthesis). The
fix is a key that cannot collide, such as a nested map or a length-prefixed key."#
  evidence r#"⟪EXP_017_forbids_nulDedup⟫ and ⟪exp017_nulNet_counts⟫ (EXP_017.lean): on
⟪exp017NulNet⟫ the reference draws two ghost edges and the NUL-joined dedup draws one."#
  fix r#"Java dedups by the ordered pair `List.of(x, y)` and TypeScript by the length-prefixed key
`${x.length}:${x}${y}`; neither can collide. Java
`ClusterBuilderTest.ghostEdgesDedupByOrderedPair_nulInKeyDoesNotMerge_EXP017`; TypeScript
`cluster-builder.test.ts`, "EXP-017: ghost edges dedup by ordered pair"."#
  status "fixed, unreleased"
