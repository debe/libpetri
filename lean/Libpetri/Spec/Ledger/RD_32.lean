import Libpetri.Spec.Ledger
import Libpetri.Spec.GlossaryExec
import Libpetri.Spec.Req.CONC_010
import Libpetri.Spec.Req.TIME_cycle
import Libpetri.Spec.Text.CONC_010
import Libpetri.Spec.Text.TIME_010

runtime_defect RD_32
  title "TypeScript blocks without a timer when a boundary falls due during the wait's setup"
  requirements r#"CONC-010 (line 4 and AC3: a block taken while an armed transition has a
timing boundary ahead at the reading of the cycle's deadline step sets a timer no longer than
the wait to the nearest such boundary, plus the timer resolution), TIME-010 (the decision to
wait of a cycle judges elapsed time at the reading of its deadline step, and no other step of
the cycle takes a new reading for these judgements)."#
  runtimes r#"TypeScript (both executors)."#
  defect r#"`awaitWork` computes its timer from a fresh clock reading taken inside
`millisUntilNextTimedTransition` (`typescript/src/runtime/bitmap-net-executor.ts`,
`precompiled-net-executor.ts`), later than the cycle reading `cycleNowMs` (taken in
`executeLoop`) and after the
`await Promise.resolve()` yield. When a boundary has passed by that later reading, the method
returns 0. The wait returns early only when no action is in flight
(`if (timerMs === 0 && promises.length === 0) return;`); with an action in
flight it skips the timer (`if (timerMs > 0)`) and blocks in `Promise.race`
over the in-flight completions and the wake-up only. Example: a `Delayed(10)` transition `t`
armed at reading 0, an action `u` in flight for an hour, a cycle reading of 9.9 (so `t` is not
Ready and nothing fires) and a wait reading of 10.05: the loop blocks with no timer and `t`
waits for `u` to return. Rust takes its timer from `cycle_now`
(`run_async`, `rust/libpetri-runtime/src/executor_core/executor.rs`), and Java leaves its poll as soon
as `nanosUntilNextTimedTransition() <= 0` (`BitmapNetExecutor.java`,
`PrecompiledNetExecutor.java`); Python rides on Rust. This is the TypeScript half of RD-16's
decision to wait."#
  evidence r#"⟪CONC_010_forbids_untimedPark⟫ in `CONC_010.lean`: a park with no timer while
⟪nextBoundary⟫ at the cycle reading is set breaks line 4. At the later reading `t` is Ready, so
line 2 would forbid the block as well. ⟪TIME_010_cycle_forbids_rereadAtPark⟫ in
`TIME_cycle.lean`: a decision to wait that takes a new reading breaks the TIME-010 companion's
line 5."#
  fix r#"`awaitWork(cycleNowMs)` hands the cycle reading to `millisUntilNextTimedTransition`,
which takes no reading of its own, in both executors; the same change fixes the TypeScript half of
RD-16. TypeScript `injectable-clock.test.ts`, "CONC-010 AC3 / TIME-010: a boundary that falls due
during the wait setup still gets a timer", on both executors."#
  status "fixed, unreleased"
