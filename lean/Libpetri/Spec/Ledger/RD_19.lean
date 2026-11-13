import Libpetri.Spec.Ledger
import Libpetri.Spec.Req.EVT_025
import Libpetri.Spec.Text.EVT_025

runtime_defect RD_19
  title "Python writes archive version 3 only"
  requirements r#"EVT-025 (a writer for each of the header versions 1, 2 and 3; AC1)."#
  runtimes r#"Python."#
  defect r#"the binding offers `write_from_store`, which always writes version 3, and no
`writeV1` or `writeV2`. `rust/libpetri-py/src/archive.rs`."#
  evidence r#"⟪EVT_025_forbids_v3Only⟫ (EVT_025.lean)."#
  fix r#"`SessionArchiveWriter` offers `write_v1` and `write_v2` beside `write_from_store`, which
writes version 3; `write_v1` takes no tags, since the version 1 header has none. Python
`test_archive.py::test_evt_025_ac1_writes_header_versions_1_2_and_3`."#
  status "fixed, unreleased"
