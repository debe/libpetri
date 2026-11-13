import Libpetri.Spec.Text

requirement_text EVT_013
  id "EVT-013"
  title "LogMessage Event"
  priority SHOULD
  kind B
  body r#"Emitted when a transition action produces log output. The engine captures log statements from within actions and wraps them as events. Contains:
- Timestamp
- Transition name, empty or absent when no transition is responsible for the message (see below)
- Logger name (Java and TypeScript)
- Log level
- Message
- Error/throwable details (optional; Java and TypeScript)

⟦s1|*Where* the implementation captures the log statements of actions (Java and TypeScript), the executor *shall* report each log statement it captures from the action of a firing as one LogMessage event that carries the firing's transition name, the statement's level and its message.⟧

**The engine may also emit diagnostics of its own** through this event rather than adding an event
type per diagnostic: a dead arc ([CORE-037]), an unknown place ([CORE-072]), a repeated output
place ([IO-016]), and similar. A diagnostic that a transition is responsible for carries that
transition's name: the transition that declares the dead arc, or the transition whose firing
deposited the tokens. A diagnostic that no transition is responsible for, at the initial-marking
and injection seams, carries an empty or absent transition name.
Consumers MUST therefore treat the transition name as optional and MUST NOT key, filter or group on
it without handling its absence.

⟦s2|*When* the executor emits an engine diagnostic before the first step of a run, the diagnostic *shall* carry an empty or absent transition name, unless it reports a dead arc ([CORE-037]), in which case it *shall* carry the name of the transition that declares the arc.⟧

⟦s3|*When* the executor emits an engine diagnostic as it injects a token into an environment place, the diagnostic *shall* carry an empty or absent transition name.⟧

⟦s4|*When* the executor emits an engine diagnostic as it deposits the outcome of a firing or a batch that the firing published ([IO-015]), the diagnostic *shall* carry the name of that firing's transition.⟧

An engine diagnostic SHOULD be emitted only where it reports something the caller did not ask for
and would otherwise not learn. A diagnostic on a path the caller explicitly requested, such as a
`close()` it called itself ([ENV-013]), is a false positive: it fires on every run of a net whose
normal ending is a shutdown ([ENV-012]), and a warning that always fires trains its reader to
ignore the level. Where a queryable result already carries the information ([EXEC-041] AC3), the
event is an addition to it and MUST NOT be the only signal.

⟦s5|*When* the caller drains, closes or stops the executor ([ENV-011], [ENV-013], [ENV-015]), the executor *shall not* emit an engine diagnostic for the request or for the queued external events it discards because of it.⟧

⟦s6|*When* the executor refuses an injection request because it is draining, closed or stopped, or because the run has finished ([ENV-006]), it *shall not* emit an engine diagnostic for the refusal.⟧

⟦s7|*When* a run ends because it is quiescent, a terminal place is marked, or the caller closed or stopped it ([EXEC-041]), the executor *shall not* emit an engine diagnostic for that end.⟧

**Acceptance Criteria:**
1. Log statements within actions are captured as LogMessage events.
2. Log level (INFO, WARN, ERROR, etc.) is preserved.
3. Exception details are included when present.
4. An engine diagnostic that no transition is responsible for carries an empty or absent
   transition name, one that a transition is responsible for carries that transition's name, and
   every consumer of the event tolerates an absent name.
5. No engine diagnostic is emitted on a caller-requested termination path (a drain, a close or a
   stop), nor when a run ends as quiescent, terminal, closed or stopped, nor when an injection
   request is refused.

**Depends on:** [CORE-072], [ENV-012], [ENV-013], [EXEC-041]
**Implementation notes:**
- Java: Captures SLF4J output via LogCaptureScope
- TypeScript: Captures via context.log() method
- Rust: Emits the engine diagnostics as LogMessage events, but does not capture the log statements of actions (the transition context's log function is never installed); Python, which runs on Rust, captures none either.

**Test derivation:** Action logs a warning; verify LogMessage event with correct level and message."#
