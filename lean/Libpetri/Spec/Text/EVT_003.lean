import Libpetri.Spec.Text

requirement_text EVT_003
  id "EVT-003"
  title "ExecutionCompleted Event"
  priority MUST
  kind B
  body r#"Emitted when a run ends: the executor's loop finishes the run, whatever the termination reason ([EXEC-041]). Contains:
- Timestamp
- Net name
- Execution ID (Java and TypeScript, [EVT-002])
- Total duration (Java and TypeScript)

⟦s1|*When* the executor finishes a run ([EXEC-041]), it *shall* emit exactly one ExecutionCompleted event, whatever the termination reason.⟧

⟦s2|The executor *shall* emit ExecutionCompleted events only when it finishes a run.⟧

⟦s3|*If* the executor has emitted the ExecutionCompleted event of a run, *then* it *shall not* emit another event of that run other than a log message ([EVT-013]) or an ActionTimedOut event ([EVT-010]).⟧

⟦s4|*When* the executor finishes a run with the termination reason `quiescent` ([EXEC-040]), it *shall* have no firing in flight, so every firing of the run has ended before its ExecutionCompleted event.⟧

The event marks the end of the run, not its outcome. A run that a terminal stop ([EXEC-042]) or an immediate termination ([ENV-015]) ends can leave firings in flight: both abandon them, and the timer of an abandoned action can still emit its ActionTimedOut after the end. The event carries no termination reason: a consumer reads the reason as [EXEC-041] says, never the event alone as proof that the net quiesced. A loop that a caller's run budget leaves running has not finished, so it emits the event when it finishes, not when the caller's wait ends.

⟦s5|*Where* the ExecutionCompleted event carries a total duration (Java and TypeScript), the total duration *shall* be at least the time the run took on the executor's firing clock ([TIME-015]), from the reading at its ExecutionStarted event to the reading at its ExecutionCompleted event.⟧

Java and TypeScript measure the total duration from the construction of the executor, so for a later run of the same executor it also counts the earlier runs and the time between them.

**Acceptance Criteria:**
1. Emitted exactly once per run that finishes, whatever the termination reason, and followed by no event of the run other than a log message or an ActionTimedOut.
2. At a quiescent finish no firing is in flight; a terminal stop or an immediate termination may leave firings in flight.
3. Where the event carries a total duration (Java and TypeScript), it is at least the time the run took on the executor's firing clock.

**Test derivation:** Run a net to quiescence; verify the last event is ExecutionCompleted, emitted once; with a firing clock that advances during the run, verify the duration is at least the time between the run's ExecutionStarted and ExecutionCompleted."#
