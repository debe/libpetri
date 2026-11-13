import Libpetri.Spec.Ledger
import Libpetri.Spec.Req.TIME_014
import Libpetri.Spec.Req.TIME_cycle
import Libpetri.Spec.Text.EXEC_001
import Libpetri.Spec.Text.EXEC_002
import Libpetri.Spec.Text.TIME_003
import Libpetri.Spec.Text.TIME_005
import Libpetri.Spec.Text.TIME_010
import Libpetri.Spec.Text.TIME_013
import Libpetri.Spec.Text.TIME_014

runtime_defect RD_16
  title "Java's firing pass and decision to wait judge at readings of their own"
  requirements r#"TIME-014 (line 3), TIME-010 (the firing pass and the decision to wait judge
at the deadline step's reading, and no other step of the cycle takes a new reading for these
judgements), EXEC-001 (ruling D61 (c)), EXEC-002 (the executor companion `EXEC_002_cycle`, line 1:
a pass starts only transitions of the ready order at the deadline step's reading), TIME-003
(line 2), TIME-005 (line 3), TIME-013 (line 2: no firing of a reapable transition whose elapsed
time is greater than its latest bound plus the tolerance)."#
  runtimes r#"Java (both executors) and TypeScript (its decision to wait; see RD-32)."#
  defect r#"a Java cycle takes four readings of the firing clock: the enablement update, the
deadline step, the firing pass and the decision to wait each read the clock (`clockNanos()`).
The pass judges readiness at its own reading instead of the deadline step's, and the decision
to wait judges the next timing boundary at a fourth reading (`nanosUntilNextTimedTransition`,
called from `awaitCompletionOrEvent`, its poll loop and `awaitExternalEvent`). Rust takes one
reading per cycle and conforms. TypeScript's deadline step and pass share one reading, which
conforms, but its decision to wait takes another (RD-32). The pass checks only the earliest
bound at its reading and never checks expiry again, so a `Deadline` or `Window` transition
whose elapsed time passes its latest bound plus the tolerance between the deadline step's reading and the pass's is neither reaped nor refused:
it fires. Example: `Deadline(100)`, tolerance 5, armed at 0; the deadline step reads 105.9 ms
(elapsed 105, not past 105, so no reap), the pass reads 106.0 ms (elapsed 106) and fires it.
The reading at the decision to wait is later than the deadline step's, so it only shortens the
wait, which CONC-010 accepts; it is still a new reading that TIME-010 rules out.
`updateDirtyTransitions`, `enforceDeadlines`, `fireReadyGeneral` and
`nanosUntilNextTimedTransition` (used in `awaitCompletionOrEvent`, its poll loop
`awaitCompletionPolling` and `awaitExternalEvent`), in
`java/src/main/java/org/libpetri/runtime/BitmapNetExecutor.java` and
`java/src/main/java/org/libpetri/runtime/PrecompiledNetExecutor.java`."#
  evidence r#"⟪TIME_014_forbids_passReread⟫ (TIME_014.lean),
⟪TIME_010_cycle_forbids_rereadAtBegin⟫ and ⟪TIME_010_cycle_forbids_rereadAtPark⟫
(TIME_cycle.lean)."#
  fix r#"Java takes one firing-clock reading per cycle, before the enablement update, and hands it
to the deadline step, the firing pass and the decision to wait in both executors; the poll loop
only counts the timer down. TypeScript's decision to wait takes the cycle reading through the
RD-32 change. Java `AbstractInjectableClockTest`:
`firingPassJudgesReadinessAtTheDeadlineStepsReading_TIME014_TIME010`,
`firingPassNeverStartsAReapableTransitionPastItsLatestBound_TIME013_TIME010` and
`decisionToWaitJudgesTheNextBoundaryAtTheCycleReading_TIME010_CONC010`; TypeScript
`injectable-clock.test.ts`, "CONC-010 AC3 / TIME-010: a boundary that falls due during the wait
setup still gets a timer"."#
  status "fixed, unreleased"
