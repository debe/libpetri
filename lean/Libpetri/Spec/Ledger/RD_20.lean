import Libpetri.Spec.Ledger
import Libpetri.Spec.Text.EVT_025

runtime_defect RD_20
  title "Python stamps an empty archive with the wall clock"
  requirements r#"EVT-025 (two archives of identical run data are identical)."#
  runtimes r#"Python."#
  defect r#"for an empty store `write_from_store` takes the start and end times from
`SystemTime::now`, so two archives of the same empty session differ.
`rust/libpetri-py/src/archive.rs`."#
  evidence r#"none; the EVT_025 assumes record it."#
  fix r#"the start time is the first event's timestamp, or 0 for an empty store, and the end time
the last event's, or none for an empty store; the wall clock is not read. Python
`test_archive.py::test_evt_025_two_archives_of_one_empty_session_are_identical`."#
  status "fixed, unreleased"
