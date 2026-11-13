import Libpetri.Spec.Text

requirement_text CONC_012
  id "CONC-012"
  title "~~Concurrent Action Limit~~ (Removed)"
  status Removed
  body r#"No implementation offers an executor-level limit on in-flight actions, and a permit place bounds concurrency inside the net, where verification can see it. The former text and the permit-place pattern are kept as advice in [Usage guidance (non-normative)](00-index.md#usage-guidance-non-normative).

Retained as a tombstone for traceability; excluded from the active requirement count."#
