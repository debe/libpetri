import Libpetri.Spec.Text

requirement_text CONC_002
  id "CONC-002"
  title "Non-Blocking Action Dispatch"
  priority MUST
  kind B
  body r#"⟦s1|An action returns a future/promise/task; the orchestrator does not *await* its completion inline before continuing.⟧ Concurrency is provided by whatever drives that returned handle — a virtual-thread pool, tokio tasks, or promise microtasks. Where the action *body* is invoked is implementation-defined: an implementation MAY invoke it inline on the orchestrator thread (delegating the dispatch decision to the action, which supplies its own executor for any work it wants to run off-thread), or MAY submit it to a task pool itself. In an inline-invoking implementation an action that blocks before returning its handle blocks the whole net; concurrency there comes from the action returning a handle backed by its own thread/pool.

⟦s2|*When* the executor starts a transition, it *shall not* deposit any token; the outputs of the firing are deposited in a later step ([CONC-003]).⟧

⟦s3|*When* the executor starts a transition, it *shall* add a firing of that transition, its action not yet completed, to the firings in flight, and *shall* leave every other firing in flight as it was.⟧

⟦s4|From its termination test ([EXEC-040]) the executor *shall* either begin a firing pass or finish the run; it *shall not* wait at the test for a firing in flight to complete.⟧

⟦s5|The executor *shall* pass over a transition of the ready order without starting it only when the transition holds no clock or is not enabled on the marking the firing pass judges ([EXEC-003]), whatever firings are in flight.⟧

⟦s6|*When* the executor updates enablement ([TIME-010]), it *shall* leave every enabled transition that is not reaped ([TIME-013]) holding a clock, whatever firings are in flight, unless the executor is not re-entrant and a firing of that transition is in flight.⟧

⟦s7|*Where* the executor is not re-entrant (Java, TypeScript), it *shall not* arm ([TIME-010]) or start a transition while a firing of that transition is in flight.⟧

**Acceptance Criteria:**
1. The orchestrator does not await an action's completion inline; it continues once the action returns its handle.
2. Multiple actions whose handles are backed by concurrent work execute concurrently.
3. The orchestrator continues processing other transitions while such actions run.

⟦s8|While an action runs its inputs are consumed and its outputs not yet deposited, and other
transitions fire.⟧ Verification models that for every transition it splits in two ([VER-004]):
one whose output another transition tests with an inhibitor, reset or drain, one that marks a
terminal place, and the extra transitions a lower-bound `QuiescentCount` beside a terminal
place and conflict priority ([NU-052]) require. ⟦s9|Whether an executor starts a transition again
while an earlier firing of it is in flight is not specified: a re-entrant executor does (Rust,
Python), one that is not re-entrant does not (Java, TypeScript).⟧ The verification model allows it, which is sound for every
implementation. When a counterexample
starts a transition again while its earlier firing is in flight, the report says so, since on
Java and TypeScript that trace may be a false alarm. Conflict priority does not rely on the
restart: a pruner pre-empts nothing while its own action is in flight.

**Test derivation:** Two transitions fire; both actions return handles backed by a 100ms async sleep; verify total time ~100ms, not ~200ms."#
