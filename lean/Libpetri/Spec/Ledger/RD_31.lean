import Libpetri.Spec.Ledger
import Libpetri.Spec.Req.MOD_031
import Libpetri.Spec.Text.CORE_036
import Libpetri.Spec.Text.EXEC_022
import Libpetri.Spec.Text.IO_013
import Libpetri.Spec.Text.IO_014
import Libpetri.Spec.Text.MOD_031

runtime_defect RD_31
  title "Java and TypeScript resolve the timeout branch's places a second time"
  requirements r#"MOD-031 (the correspondence is applied once, to a declared place), IO-013 (the
timeout outcome deposits the tokens of its child on the child's places), IO-014 (a forward
deposits in `to` the tokens consumed from `from`: `forwardToHarvest` resolves `to` again, so
with port `a` bound to `b` and port `b` bound to `c` the forward meant for `b` lands on `c`),
CORE-036 (the ninth sentence and the outcome line: the timeout token meant for `b` is
deposited on `c`), EXEC-022 (line 1: the timeout outcome is the token-level outcome of the
`Timeout` child)."#
  runtimes r#"Java, TypeScript."#
  defect r#"the executor deposits the timeout branch through `outputToHarvest` and
`forwardToHarvest` with the places the rewritten output specification names, which are already
the actual places (`java/src/main/java/org/libpetri/runtime/ExecutorSupport.java`,
`produceTimeoutOutputRecursive`; `typescript/src/runtime/executor-support.ts`,
`produceTimeoutOutput`). Both methods resolve the place through the correspondence again
(`java/src/main/java/org/libpetri/core/TransitionContext.java`;
`typescript/src/core/transition-context.ts`). On a collision (port `a` bound to the
caller place `b`, port `b` bound to `c`) the timeout token meant for `b` lands on `c`. The
`from` side of a `ForwardInput` is resolved twice as well (Java reads it through
`TransitionContext.inputTokens`, TypeScript in `forwardToHarvest`), so a timeout can forward a
token taken from the wrong input, or fail the firing when the twice-resolved place fails the
declared-place check before `action-timed-out` is emitted. Rust deposits the timeout branch on
the places as given."#
  evidence r#"⟪mod031ctx_timeout_resolveTwice⟫ in `MOD_031.lean`."#
  fix r#"`outputToHarvest` and `forwardToHarvest` take the actual places of the rewritten output
spec as given, and Java reads the `from` tokens from the raw input. Java
`AbstractNetExecutorEngineTest.OutputTimeoutTests.outTimeout_portCollision_depositsOnTheBoundPlace_MOD031_IO013`
and `outTimeout_forwardInput_portCollision_forwardsFromTheBoundPlace_MOD031_IO014`; TypeScript
`compose-action-place-alias.test.ts`, "the timeout branch deposits on the bound place under a
port-name collision" and "a timeout ForwardInput reads and deposits on the actual places under a
collision", on both executors."#
  status "fixed, unreleased"
