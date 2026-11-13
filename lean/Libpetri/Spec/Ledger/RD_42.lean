import Libpetri.Spec.Ledger
import Libpetri.Spec.Req.VER_013
import Libpetri.Spec.Text.VER_013

runtime_defect RD_42
  title "Java and TypeScript treat the last millisecond of the total budget differently from the clamp"
  requirements r#"VER-013 (the total budget sentence, `VER_013_args` line 6: with no whole
millisecond remaining no process starts, and AC9 'no z3 process starts once the budget is
spent'; the stop sentences, `VER_013_stop` line 4: a solver call is refused only by a poll
that finds the stop, and line 6: the `Unknown` then gets the reason `total verification budget
of <N> ms exhausted during <phase>`)."#
  runtimes r#"Java, TypeScript."#
  defect r#"both runtimes poll the deadline on a finer clock than the clamp reads it, so when
less than one millisecond of the total budget is left the two disagree. Java:
`Z3Solver.run` (`java/src/main/java/org/libpetri/smt/z3/Z3Solver.java`) calls
`deadline.check()`, which throws only once the nanosecond deadline has passed
(`VerificationDeadline.expired`, `java/src/main/java/org/libpetri/core/internal/VerificationDeadline.java`),
and then sets `left = Math.max(1, deadline.remainingMs())` with `remainingMs` the remaining
nanoseconds divided down to whole milliseconds. With 0 < remaining < 1 ms the whole
milliseconds left are 0, yet Java starts a `z3` process with `-t:1`, `-T:2` and a 2001 ms
watchdog. TypeScript: `runZ3Text` (`typescript/src/verification/z3/z3-process.ts`)
refuses when `Math.floor(deadline.remainingMs()) <= 0` but records no stop, while every poll
(`Deadline.check` through `passed()`, `remainingMs() <= 0`,
`typescript/src/verification/total-budget.ts`; `enter`, and the `unknown` case of the IC3/PDR
query and the certificate check in `runPipeline`, `smt-verifier.ts`) still sees
time left. In that window the IC3/PDR query is refused, `runZ3Spacer` turns the rejection into
`unknown` with the reason `total verification budget of <N> ms exhausted; z3 not started`
(`z3/spacer-runner.ts`), the `check()` of the `unknown` case does not throw, and
`verify()` returns that reason without `during IC3/PDR query`. A step that steps aside after a
refused call (the state-equation phase, for example) is followed by `enter()` of the next
step, which passes, so a step is entered after the refusal. Rust and Python use one
whole-millisecond `remaining()` for the entry poll, the polls inside a step and the clamp
(`total_budget.rs` `expired_now`, `step`, `cut`, `clamp`), so the clamp refuses exactly when a
poll records `Stop::Budget`. The fix is one clock for both:
Java should start no process when `remainingMs()` is 0 and record the budget stop there (or
poll and clamp on whole milliseconds, as Rust does); TypeScript should record the stop when
the clamp refuses, or poll on `Math.floor(remainingMs()) <= 0`."#
  evidence r#"⟪VER_013_args_forbids_javaSubMs⟫ (`VER_013.lean`): the clamp that raises a
remainder of 0 whole milliseconds to 1 ms breaks ⟪VER_013_args⟫ line 6 while lines 4 and 5
hold for it. ⟪VER_013_stop_forbids_refuseUnrecorded⟫ (`VER_013.lean`): a runner whose refused
call records no stop breaks ⟪VER_013_stop⟫ line 4, and its `Unknown` keeps the refusal's own
reason. The two clocks themselves are not modelled; the model has one stop per poll."#
  fix r#"both runtimes poll on the whole-millisecond clock the clamp reads: Java's `expired()` is
`remainingMs() <= 0` and `Z3Solver.run` starts no process with no whole millisecond left, and
TypeScript's `passed()` tests `Math.floor(remainingMs()) <= 0`. Java
`TotalBudgetTest.subMillisecondRemainderStopsAsTheClampDoes_VER013_AC9` and
`StubZ3Test.totalBudget_noProcessStartsWithoutAWholeMillisecondLeft_VER013_AC9`; TypeScript
`total-budget.test.ts`, "VER-013 AC9: with less than one whole millisecond left the poll stops as
the clamp refuses"."#
  status "fixed, unreleased"
