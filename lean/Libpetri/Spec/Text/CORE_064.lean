import Libpetri.Spec.Text

requirement_text CORE_064
  id "CORE-064"
  title "~~Execution Context Injection~~ (Removed)"
  status Removed
  body r#"Host objects in the transition context (a tracing span, configuration) are a convenience of the language bindings, not part of the firing contract: not every implementation has them, and no requirement depends on them. The former text is kept as advice in [Usage guidance (non-normative)](00-index.md#usage-guidance-non-normative).

Retained as a tombstone for traceability; excluded from the active requirement count."#
