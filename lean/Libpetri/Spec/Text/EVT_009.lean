import Libpetri.Spec.Text

requirement_text EVT_009
  id "EVT-009"
  title "TransitionTimedOut Event"
  priority MUST
  kind B
  body r#"Reports a reap of a transition ([TIME-013]). Contains:
- Timestamp
- Transition name
- Deadline duration (Java and TypeScript)
- Elapsed time when reaped (Java and TypeScript): the time since the transition was last newly armed ([TIME-010])

⟦s1|*When* the executor reaps a transition ([TIME-013]), it *shall* emit exactly one TransitionTimedOut event naming that transition.⟧

⟦s2|The executor *shall* emit a TransitionTimedOut event only when it reaps a transition, and the event *shall* name the transition it reaps.⟧

⟦s3|*Where* the TransitionTimedOut event carries the deadline and the elapsed time (Java and TypeScript), the deadline *shall* be the latest bound of the transition, without the deadline tolerance, and the elapsed time *shall* be the transition's elapsed time ([TIME-010]) at the reading of the deadline step that reaps it.⟧

⟦s4|Transition names are taken to be pairwise distinct, as in the timing requirements ([TIME-010]).⟧

**Acceptance Criteria:**
1. Emitted in the deadline step of a cycle at whose reading a reapable, armed transition's
   elapsed time is strictly greater than its latest bound plus the deadline tolerance; never for
   an `Exact` transition ([TIME-006]).
2. After this event the transition is reaped: it stays enabled but is not armed, and does not
   fire until one of its arc places is written ([TIME-013]).

**Depends on:** [TIME-013]
**Test derivation:** Transition with Deadline(100ms); delay firing 200ms; verify TransitionTimedOut event."#
