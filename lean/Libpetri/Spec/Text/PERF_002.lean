import Libpetri.Spec.Text

requirement_text PERF_002
  id "PERF-002"
  title "Enablement Check O(W)"
  priority MUST
  kind Q
  body r#"Individual transition enablement checks are O(W) where W = ceil(numPlaces / word_size). Word size is implementation-defined (32-bit or 64-bit). For nets with fewer than 64 places, this is O(1).

**Acceptance Criteria:**
1. Enablement check for a single transition does not iterate over arcs.
2. Check is constant-time for nets with < 64 places.
3. Check scales with word count for larger nets.

**Depends on:** [CONC-004]
**Test derivation:** Benchmark enablement check on nets of varying sizes; verify constant-time for small nets."#
