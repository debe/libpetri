import Libpetri.Spec.Text

requirement_text EVT_002
  id "EVT-002"
  title "ExecutionStarted Event"
  priority MUST
  kind B
  body r#"Emitted when the executor begins running. Contains:
- Timestamp
- Net name
- Execution ID (Java and TypeScript): the ID of the executor that runs, drawn when it is constructed

⟦s1|*When* a run starts, the executor *shall* emit an ExecutionStarted event before its first cycle ([EXEC-001]) and before any event of the run other than a log message ([EVT-013]).⟧

⟦s2|The executor *shall* emit at most one ExecutionStarted event per run.⟧

A run's events reach the event store only while the store is enabled ([EVT-020]).

⟦s3|Two executors constructed in one process from the same copy of the library *shall* carry different execution IDs, whatever the clock reads when each is constructed ([TIME-015] AC14).⟧

⟦s4|*Where* the lifecycle events carry the execution ID (Java and TypeScript), the ExecutionStarted and ExecutionCompleted events of every run *shall* carry the ID of the executor that runs it.⟧

An executor keeps its execution ID for all its runs, so the runs of one executor share it. [EVT-003] says when an ExecutionCompleted event is emitted.

**Acceptance Criteria:**
1. Emitted exactly once per execution run, before any transitions fire.
2. Two executors constructed in one process from the same copy of the library carry different execution IDs, even at the same clock reading.

**Test derivation:** Run net; verify the first event other than a log message is ExecutionStarted with correct net name."#
