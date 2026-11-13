import Libpetri.Spec.Text

requirement_text ENV_006
  id "ENV-006"
  title "inject() Rejection on Closed or Draining Executor"
  priority MUST
  kind B
  body r#"⟦s1|If the executor has been closed, is draining, or execution has completed, inject() returns an error or false rather than silently dropping the token.⟧

⟦s2|*If* `inject()` is called while the executor is draining, closed or stopped ([ENV-011], [ENV-013], [ENV-015]), or after the run has finished, *then* it *shall* return an error or `false`.⟧

⟦s3|*If* `inject()` is called while the executor is draining, closed or stopped, or after the run has finished, *then* the executor *shall* change nothing: the token *shall not* reach the marking, and no event *shall* be queued for injection.⟧

⟦s4|Each accepted injection *shall* stay an event of its own until it is injected, discarded or dropped: the executor *shall not* merge two accepted injections into one.⟧

⟦s5|*Where* `inject()` returns an admission signal ([ENV-004]), *when* a run that accepted an injection finishes, the executor *shall* have completed the signal of that injection, with the value [ENV-004] gives: by injecting the token, by discarding the event on a close ([ENV-013]), by dropping it on an immediate termination ([ENV-015]), or by dropping it at the finish of the run while it is still queued.⟧

A run whose terminal place ([EXEC-042]) is marked has not finished until the executor ends it: an injection accepted in between is dropped when the run ends, and its admission signal, where one exists, completes with `false`. TypeScript refuses such a call at once, which gives the caller the same `false`.

In Java, in TypeScript and in Python, which has one handle per executor, every injector shares the executor's lifecycle, so every injector is refused from the moment of the drain or the close. In Rust the drained flag belongs to the `ExecutorHandle`: a handle refuses once it has itself drained or closed the executor, and every handle refuses once the run has finished. An event that another sender injects after that drain or close is answered `true`, and the executor drops it on receipt without a report. The first two sentences above therefore hold in Rust for one injector per executor, and for every sender the token still never reaches the marking.

Rust and Python return no admission signal ([ENV-004]): their `inject()` reports acceptance only, so an accepted event that a stop on a terminal place ([EXEC-042]) drops is not reported. Their executor still injects, discards or drops every event it accepted by the time the run finishes; only the report to the caller is missing. A form of `inject()` without a result (TypeScript's `injectNoAwait`, Java's `injectAsync`) is outside this requirement: it reports nothing, and on a draining, closed or finished executor it drops the token without an answer.

**Acceptance Criteria:**
1. After executor closes, inject() returns error/false.
2. After drain(), inject() returns error/false.
3. Where an admission signal exists ([ENV-004]), every accepted injection completes it by the time the run finishes.

**Depends on:** [ENV-002], [ENV-004], [ENV-011], [ENV-013], [ENV-015], [EXEC-042]
**Test derivation:** Run executor to completion; call inject(); verify error returned. Call drain(); inject(); verify error returned."#
