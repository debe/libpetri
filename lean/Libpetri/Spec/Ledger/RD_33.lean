import Libpetri.Spec.Ledger
import Libpetri.Spec.Req.CONC_003
import Libpetri.Spec.Text.CONC_003
import Libpetri.Spec.Text.EXEC_020

runtime_defect RD_33
  title "Java and TypeScript read the output collector at admission, not at completion"
  requirements r#"CONC-003 (line 1: a commit deposits exactly the tokens the action wrote
before it returned), EXEC-020 (the produced tokens of an admitted completion are what the
action wrote)."#
  runtimes r#"Java and TypeScript (both executors)."#
  defect r#"neither runtime detaches the output collector when an action completes normally;
only the timeout path detaches it (`detachForTimeout`,
`java/src/main/java/org/libpetri/core/TransitionContext.java`,
`typescript/src/core/transition-context.ts`). The output is read when the orchestrator
later admits the completion, in `processCompletedTransitions` of
`java/src/main/java/org/libpetri/runtime/BitmapNetExecutor.java`
(`flight.context().rawOutput()`; the completion is queued in `fireTransition`),
`PrecompiledNetExecutor.java`, `typescript/src/runtime/bitmap-net-executor.ts` (the
`.then` in `fireTransition` detaches nothing) and `precompiled-net-executor.ts`. So a token an
action writes after its future or promise completed, from a thread or a timer it started, and
before the completion is admitted, is deposited at the commit. Rust moves the outputs into the
completion message when the action returns. Java's synchronous paths (`processSyncOutput`) read
the output without detaching it too, and `PrecompiledNetExecutor` reused a pooled context per
transition, so a write that arrived after admission landed in the next firing of the same
transition. The fix is to detach the collector at completion, as the timeout path already does."#
  evidence r#"⟪CONC_003_forbids_lateWrite⟫ (CONC_003.lean)."#
  fix r#"both runtimes detach the write target when the action completes (`detachAtCompletion`)
and keep what was written as the harvest, so a later write is dropped. Java detaches in the
completion callback and on the synchronous path, and its precompiled executor gives every firing a
fresh context; TypeScript detaches in the first reaction to the action's promise, also with an
action timeout armed. Java
`AbstractNetExecutorEngineTest.OutputAtCompletionTests.aWriteAfterCompletionIsNotDeposited_CONC003`
and `aLateWriteDoesNotReachTheNextFiring_CONC003`; TypeScript `executor-shared-semantics.test.ts`,
"a token written after the action's promise settled is not deposited (CONC-003)", with and without
an action timeout, on both executors."#
  status "fixed, unreleased"
