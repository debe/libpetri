import Libpetri.Spec.Text

requirement_text PERF_040
  id "PERF-040"
  title "Flat-Array Memory Layout"
  priority SHOULD
  kind Q
  body r#"The precompiled executor SHOULD use a flat-array memory layout with no hash map lookups on the hot path. Per-transition data is stored in parallel arrays of length T (transition count) indexed by transition ID. Token storage uses ring buffers indexed by place ID. In-flight transition tracking uses arrays indexed by transition ID.

**Acceptance Criteria:**
1. No hash map lookups occur during the execution loop (consume, fire, complete, enable).
2. Per-transition timing, priority, masks, and opcodes are in parallel arrays.
3. Token access is by integer place ID, not by place object lookup.
4. In-flight tracking is by integer transition ID, not by transition object lookup.

**Depends on:** [CONC-020]
**Test derivation:** Profile execution of a 100-transition net; verify no hash map operations on the hot path."#
