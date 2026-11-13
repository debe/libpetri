import Libpetri.Spec.Ledger
import Libpetri.Reference.ExportCluster
import Libpetri.Spec.Req.EXP_016
import Libpetri.Spec.Text.EXP_016
import Libpetri.Spec.Text.EXP_017
import Libpetri.Spec.Text.MOD_040

runtime_defect RD_12
  title "An empty `/` segment in a cluster key fails the export"
  requirements r#"EXP-016, EXP-017, MOD-040 (ruling D46 (a))."#
  runtimes r#"Rust (panics), Java and TypeScript (throw), and Python through Rust."#
  defect r#"on a key such as `a//x` or `http://host/x`, `register_prefix_chain` skips the empty
segment and never registers the key itself; the builder then fails at the node's key.
`rust/libpetri-export/src/cluster_builder.rs` (`register_prefix_chain`). Python's
`dot_export` and archive writer reach that exporter and raise `PanicException`. Java fails on
fewer keys: `String.split` keeps inner empty segments, so the keys `a//x` and `http://host`
draw, and only a key with a leading or trailing `/`, such as `/a` (the key of `/a/x`) or `a/`
(the key of `a//x`), throws a `NullPointerException`
(`java/src/main/java/org/libpetri/export/ClusterBuilder.java`, `registerPrefixChain`).
TypeScript throws a `TypeError` on a key with a leading `/` and on the empty key
(`typescript/src/export/cluster-builder.ts`)."#
  evidence r#"⟪registerChain⟫ (Reference/ExportCluster.lean); EXP-016's name assumption
(⟪ExportNet.ClusterKeysWellFormed⟫) keeps such nets out of the block."#
  fix r#"the three exporters register the glossary key chain (every non-empty prefix that ends
before a `/`, then the key itself, the empty key included) and take the deepest common prefix as
the longest element of one chain that is in the other; keys without an empty segment draw as
before. Rust `cluster_builder.rs` `exp_016_key_with_empty_segment_registers_its_key_chain` and
`dot_exporter.rs` `exp_016_empty_segment_names_export_without_panic`; Java
`ClusterBuilderTest.partitionRegistersTheKeyChainOfAKeyWithAnEmptySegment_EXP016` and
`SubnetDotExportTest.dotExport_emptySegmentNames_doNotThrow_EXP016`; TypeScript
`cluster-builder.test.ts`, "EXP-016: a key with an empty /-segment (a/, a//x, /a) draws its key
chain and does not throw"; Python
`test_dot_export.py::test_exp_016_empty_segment_cluster_key_exports_without_panic` and
`::test_exp_016_empty_segment_cluster_key_archives_without_panic`."#
  status "fixed, unreleased"
