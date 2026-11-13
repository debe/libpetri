import Libpetri.Spec.Ledger
import Libpetri.Spec.Req.EVT_025
import Libpetri.Spec.Text.EVT_025

runtime_defect RD_18
  title "Python archives at most 10,000 events"
  requirements r#"EVT-025 (one record for each event of the store's snapshot)."#
  runtimes r#"Python."#
  defect r#"`write_from_store` copies the store into a debug store of the default capacity of
10,000 events before writing, so a larger store is archived without its oldest events.
`rust/libpetri-py/src/archive.rs` (`DebugEventStore::new` in `write_from_store`)."#
  evidence r#"⟪EVT_025_forbids_copyThroughBounded⟫ (EVT_025.lean)."#
  fix r#"the copy is a debug store sized to the snapshot, so no event is evicted before the write.
Python `test_archive.py::test_evt_025_archive_keeps_every_event_of_a_store_over_10000`."#
  status "fixed, unreleased"
