import Libpetri.Spec.Ledger
import Libpetri.Spec.Req.ENV_016_l1
import Libpetri.Spec.Text.ENV_016

runtime_defect RD_34
  title "Java's awaitTermination waits out its timeout on a loop that never ran or that died at boot"
  requirements r#"ENV-016 (second block, `ENV_016_await`: line 1 and the sentence that a call
on an executor whose loop was never started answers true at once, without waiting for the
timeout; AC1, true once the loop has stopped; the sentence that `awaitTermination` is not
defeated by a failure such as a throwing event store)."#
  runtimes r#"Java (both executors)."#
  defect r#"two paths leave `started` true and `terminatedFuture` never completed, so
`awaitTermination` gets past `if (!started) return true`, waits out its whole timeout and
answers false, on every later call too.
(a) A rejected submit. `run(Duration, RunTimeoutPolicy)` sets `started = true` before
`CompletableFuture.supplyAsync(this::executeLoop, executor)`
(`java/src/main/java/org/libpetri/runtime/BitmapNetExecutor.java`,
`PrecompiledNetExecutor.java`). When the executor rejects the task, the call throws
`RejectedExecutionException` and the loop never runs. A `close()` before the run does this on
an executor that owns its pool, since `close()` shuts the pool down (`BitmapNetExecutor.close`);
a caller-supplied executor that rejects the task does it without a close.
(b) A store that throws at boot. `executeLoop` emits `ExecutionStarted` and the first marking
snapshot before its `try`/`finally` (`BitmapNetExecutor.java`,
`PrecompiledNetExecutor.java`), and `emitEvent` does not catch
(`BitmapNetExecutor.java`, `PrecompiledNetExecutor.java`). A store that
throws on these appends makes `run()` throw before the `finally` that completes
`terminatedFuture`; the loop is gone and `running` stays true. The termination bookkeeping of
the `finally` already survives a throwing store; the boot does not.
Reproduced against `java/target/classes`: after a rejected `run(Duration)`, and after a
`run()` that threw `IllegalStateException` from a store that throws on every append, both
executors answer `awaitTermination(300 ms)` with false after 300 ms. TypeScript, Rust and
Python provide no `awaitTermination`."#
  evidence r#"none of its own. Case (a) is an answer false on a loop that never started,
which line 1 of ⟪ENV_016_await⟫ forbids (⟪ENV_016_await_mutant_blocksUnstarted⟫ is that
answer). Case (b) has no image in the model, which has no step for a loop that dies before its
run: read as a loop that stays running, it meets every line, so the defect shows only against
AC1 and the quoted throwing-store sentence. The fix is to set `started` only once the submit
is accepted, or to complete `terminatedFuture` when the submit fails, and to move the boot
emissions inside the `try`."#
  fix r#"`run(Duration, policy)` restores `started` and rethrows when the submit throws, and
`executeLoop` emits its boot events inside the `try`, so a store that throws at boot still reaches
the `finally` that completes `terminatedFuture`, with the termination reason `STOPPED`. Java
`AbstractNetExecutorEnvironmentTest.LifecycleTests.awaitTermination_trueAtOnceAfterARejectedRun_ENV016`
and `awaitTermination_trueAfterABootThatThrew_ENV016_AC1`, on both executors."#
  status "fixed, unreleased"
