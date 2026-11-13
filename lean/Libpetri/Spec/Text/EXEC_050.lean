import Libpetri.Spec.Text

requirement_text EXEC_050
  id "EXEC-050"
  title "~~Timestamp-Based Stale Detection~~ (Removed)"
  status Removed
  body r#"Stale detection is a usage pattern built from read arcs ([CORE-032]), token timestamps ([CORE-010]) and XOR outputs ([IO-012]); it has no executor behaviour of its own. The pattern is kept as advice in [Usage guidance (non-normative)](00-index.md#usage-guidance-non-normative).

Retained as a tombstone for traceability; excluded from the active requirement count."#
