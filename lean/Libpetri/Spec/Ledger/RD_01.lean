import Libpetri.Spec.Ledger
import Libpetri.Spec.ClashesExec
import Libpetri.Spec.Req.EXEC_021
import Libpetri.Spec.Req.IO_013
import Libpetri.Spec.Text.CORE_036
import Libpetri.Spec.Text.EXEC_021
import Libpetri.Spec.Text.EXEC_022
import Libpetri.Spec.Text.IO_013

runtime_defect RD_01
  title "The timeout outcome is validated against the output spec"
  requirements r#"EXEC-021, EXEC-022, IO-013 (ruling D24 (a)), CORE-036 (the ninth sentence: a
firing that ends with the timeout outcome deposits in every place as many tokens as the timeout
outcome puts there)."#
  runtimes r#"Java, TypeScript."#
  defect r#"both validate the timeout outcome against the whole output spec, so a spec such as
`And(A, Timeout(d, B))` fails the firing on every timeout instead of depositing `B`. Rust skips
validation on the timeout path and still runs the join-relay check.
`java/src/main/java/org/libpetri/runtime/BitmapNetExecutor.java`
(`processCompletedTransitions`), `typescript/src/runtime/bitmap-net-executor.ts`
(`validateOutSpec` in `processCompletedTransitions`, on the completion path that also settles a
timed-out firing). The production
executors have the same check: `PrecompiledNetExecutor.processCompletedTransitions` in Java and
the general branch of `typescript/src/runtime/precompiled-net-executor.ts`."#
  evidence r#"⟪clashExec_timeoutValidated_conflict⟫ (ClashesExec.lean),
⟪EXEC_021_forbids_validateTimeout⟫ (EXEC_021.lean), ⟪IO_013_forbids_validateTimeout⟫
(IO_013.lean)."#
  fix r#"both executors of each runtime skip the output-spec validation and the IO-016
multiplicity warning for a firing that ended with the timeout outcome and run only the join-relay
check (NU-054), so `And(A, Timeout(d, B))` deposits `B`. Java
`AbstractNetExecutorEngineTest.OutputTimeoutTests.outTimeout_andSibling_depositsTheTimeoutChildUnvalidated_EXEC021`
and `outTimeout_andSibling_forwardsEveryTokenWithoutMultiplicityWarning_EXEC021`; TypeScript
`executor-shared-semantics.test.ts`, "the timeout outcome is not validated (EXEC-021, EXEC-022,
IO-013)", on both executors."#
  status "fixed, unreleased"
