import Libpetri.Spec.Text

requirement_text CONC_020
  id "CONC-020"
  title "Precompiled Net Representation"
  priority SHOULD
  kind Q
  body r#"The precompiled net extends the compiled net [CONC-007] by further compiling the net topology into flat arrays and operation sequences that eliminate virtual dispatch and hash map lookups from the hot path. The precompiled representation includes:
- Flat arrays of length T (transition count) for per-transition data: timing, priorities, enablement masks, operation sequences
- Opcode-based consume operation sequences per transition [CONC-021]
- Ring buffer token storage indexed by place ID [CONC-022]
- Priority-partitioned ready queues [CONC-023]
- Precomputed timing arrays [CONC-024]
- Sparse enablement masks [PERF-042]

The precompiled net is immutable after construction.

**Acceptance Criteria:**
1. Precompiled net is constructed from a compiled net or directly from a symbolic net.
2. All per-transition data is stored in parallel arrays indexed by transition ID.
3. No hash map lookups occur during execution.
4. The precompiled net is immutable — no mutation after compile().

**Depends on:** [CONC-007]
**Test derivation:** Compile a net; verify all arrays are correctly populated and match the symbolic net."#
