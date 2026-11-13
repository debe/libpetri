import Libpetri.Spec.Ledger
import Libpetri.Spec.Text.CORE_043

runtime_defect RD_08
  title "The CORE-043 check runs on the derived split net under CONFLICT"
  requirements r#"CORE-043 (line 3: a verification entry point fails exactly when compiling the
submitted net does)."#
  runtimes r#"Rust, Java, TypeScript, and Python through Rust."#
  defect r#"under `PrioritySemantics` CONFLICT the verifier splits a sink into a start half,
which keeps the sink's name and action and gains an output place, and then runs the CORE-043
check on that derived net. A net that compiles is refused, and the Rust error says the sink
declares an output spec when it declares none.
Rust: `with_in_flight` (`rust/libpetri-verification/src/smt_verifier.rs`), `halves`
(`in_flight.rs`), `verify_name_scg` (`nu_scg_verifier.rs`), `StateClassGraph::build_core`
(`state_class_graph.rs`).
Java: the state-space lookup in `SmtVerifier.pipeline`
(`java/src/main/java/org/libpetri/smt/SmtVerifier.java`), `StateClassGraph.initialStateClass`
(`java/src/main/java/org/libpetri/analysis/StateClassGraph.java`).
TypeScript: `SmtVerifier.verify` (`typescript/src/verification/smt-verifier.ts`, after `prepare()`).
Rust's SMT entry already checks the submitted net; its refusals come from the graph builders it
calls on the split net, which are CORE-043 entry points with checks of their own, so a check
run once before any rewrite does not end the defect on its own. Java also checks a field that
a previous call left rewritten, so a reused verifier can fail its second call (RD-47)."#
  evidence r#"none; the CORE_043 assumes record it."#
  fix r#"the start half of a split passthrough sink gets a placeholder action instead of the
passthrough in all three runtimes, so the split net passes CORE-043 exactly when the submitted net
does; Java and TypeScript also run the entry check on the caller's net before `prepare()`. The
public graph builders keep their own checks. Rust `smt_verifier.rs`
`core043_conflict_split_of_a_passthrough_sink_is_not_refused`; Java
`SplitDemandTest.CORE043_aConflictSplitOfAPassthroughSinkIsNotRefused`; TypeScript
`smt-verifier-core043.test.ts`, "a conflict split of a passthrough sink is not refused
(CORE-043)"; Python
`test_smoke.py::test_core_043_conflict_split_of_a_passthrough_sink_is_not_refused`."#
  status "fixed, unreleased"
