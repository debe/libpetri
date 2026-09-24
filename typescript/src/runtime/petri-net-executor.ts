import type { Marking, MarkingSnapshotForm } from './marking.js';
import type { EnvironmentPlace } from '../core/place.js';
import type { Token } from '../core/token.js';

/**
 * What to do with the orchestrator loop when `run(timeoutMs)` hits its timeout.
 *
 * Mirrors Java's `PetriNetExecutor.RunTimeoutPolicy`.
 *
 * - `'abandon'` — reject the returned promise and leave the loop running. The net
 *   keeps firing transitions and mutating its marking after the caller has given up.
 *   This is what `run(timeoutMs)` has always done, and it stays the default only for
 *   compatibility — it is rarely what you want.
 * - `'close'` — reject the returned promise and `close()` the executor. Queued external
 *   events are discarded and in-flight actions are allowed to complete, per [ENV-013].
 */
export type RunTimeoutPolicy = 'abandon' | 'close';

/**
 * Why an executor's run ended ([EXEC-041], [EXEC-042]), or `'running'` while no run has ended.
 *
 * - `'quiescent'` — nothing enabled and nothing in flight ([EXEC-040]); the marking is final.
 * - `'terminal'` — a deposit marked a terminal place the net declares ([EXEC-042]). The marking
 *   is the designed end; in-flight actions were abandoned and queued external events refused.
 * - `'closed'` — {@link PetriNetExecutor.close} stopped the run ([ENV-013]).
 * - `'stopped'` — a run budget (`run(timeoutMs)`) expired. The returned promise still rejects,
 *   as it always has; this is what the executor reports afterwards.
 *
 * `'quiescent'` and `'terminal'` are the **completed** reasons ({@link isComplete}); the others
 * are truncations, whose marking the net was not designed to end in.
 */
export type TerminationReason = 'running' | 'quiescent' | 'terminal' | 'closed' | 'stopped';

/**
 * Whether `reason` is a **completed** termination ([EXEC-041]): `'quiescent'` or `'terminal'`,
 * the two whose marking the net was designed to end in. `false` for a truncation and while the
 * run is still going.
 */
export function isComplete(reason: TerminationReason): boolean {
  return reason === 'quiescent' || reason === 'terminal';
}

/**
 * A marking captured from a **running** executor, per **ENV-014**.
 *
 * Carries the in-flight condition *with* the marking rather than exposing it separately: a
 * separately-queryable count would be read at a different instant than the capture, and a
 * caller comparing the two would be racing the orchestrator (AC#5).
 */
export interface SnapshotResult {
  /** The marking at the instant of capture, in CORE-073's form. An owned copy (AC#3). */
  readonly marking: MarkingSnapshotForm;
  /**
   * Whether any **work was in flight** at the instant this snapshot was taken: an action, or an
   * accepted but un-injected external event.
   *
   * A boolean observation about that moment — not a count, and not a live reading. Deliberately
   * singular: a plural name on a boolean invites the reader to expect a quantity, and a quantity
   * is what ENV-014 AC#5 rejects, because it would be read at a different instant than the
   * capture and so be racy.
   *
   * `true` means the snapshot is **not a valid restore point**, because some token is in no
   * place (AC#6):
   *
   * - a firing has consumed its inputs and its outputs have not all landed. That holds from the
   *   moment of consumption — so it covers the action's synchronous prefix and every
   *   `EventStore.append` called during the firing, not only the awaited part of the action —
   *   until the last output is deposited (`transition-completed` is emitted from a settled
   *   marking);
   * - or an external event was accepted by `inject` / `injectValue` / `injectNoAwait` and has
   *   not yet been deposited into its environment place. Resuming from such a capture would
   *   lose an event the host was told was accepted.
   *
   * It remains a perfectly valid *observation* of the running net — which is why this reports
   * the fact rather than refusing. The name predates the second case and is kept so the field
   * reads the same in all four languages (`action_in_flight` in Rust and Python).
   */
  readonly actionInFlight: boolean;
}

/**
 * Whether `result` may be persisted and later handed back as `restore` without losing tokens
 * (**ENV-014** AC#5–AC#8): exactly `!result.actionInFlight`.
 *
 * Named for the question a checkpointing caller is actually asking. {@link SnapshotResult} is a
 * plain interface here, so this is a free function where Java has the accessor
 * `SnapshotResult.isRestorePoint()` and Rust and Python have `is_restore_point` — the same
 * derivation in all four, with no state of its own. The field stays the fact the engine saw; a
 * field named `restorable` would describe one caller's intent instead.
 *
 * `false` is never an error: the snapshot is still a valid observation of the running net, and
 * a saver that gets `false` retries later — `transition-completed` is emitted from a settled
 * marking, so it is the natural moment to ask again.
 *
 * ```ts
 * const result = executor.snapshot();
 * if (isRestorePoint(result)) await save(JSON.stringify([...result.marking]));
 * ```
 *
 * @returns `true` when no work was in flight at the instant of capture — no action between
 *   consumption and its last deposit, and no accepted external event still un-injected
 */
export function isRestorePoint(result: SnapshotResult): boolean {
  return !result.actionInFlight;
}

/**
 * Interface for Petri net executors.
 */
export interface PetriNetExecutor {
  /**
   * Run the net until quiescence or timeout.
   *
   * @param timeoutMs reject after this many milliseconds; omit to run to quiescence
   * @param onTimeout what happens to the loop when the timeout fires (default `'abandon'`)
   */
  run(timeoutMs?: number, onTimeout?: RunTimeoutPolicy): Promise<Marking>;

  /**
   * Inject an external token. Returns true if accepted.
   *
   * The promise reports **admission**, which the orchestrator grants. Never `await` it from
   * inside a host clock's wait ([TIME-015]) — there the orchestrator is the caller, so
   * awaiting admission suspends the only thing that can grant it. Use {@link injectNoAwait}.
   */
  inject<T>(place: EnvironmentPlace<T>, token: Token<T>): Promise<boolean>;

  /**
   * Enqueue an external token with **no admission signal to await** ([TIME-015]).
   *
   * The form to call from inside a host clock's `sleep`. The token is admitted in the
   * executor's external-events phase on a following cycle exactly as {@link inject}'s is;
   * only the acknowledgement is dropped, which is what makes it impossible to deadlock on.
   */
  injectNoAwait<T>(place: EnvironmentPlace<T>, value: T): void;

  /**
   * Captures the running net's marking ([ENV-014]).
   *
   * Serviced without stopping the net: the executor keeps running afterwards, and the returned
   * marking is an owned copy independent of subsequent state (AC#2, AC#3). Callable from
   * anywhere, including from inside an action or an `EventStore.append`; there the capture can
   * land mid-firing, which {@link SnapshotResult.actionInFlight} then reports.
   *
   * @throws once the executor has been drained or closed (AC#4)
   */
  snapshot(): SnapshotResult;

  /**
   * Why the run ended ([EXEC-041] AC3), or `'running'` until it has. Distinguishes a run that
   * completed (`'quiescent'`, `'terminal'`) from one that was truncated (`'closed'`,
   * `'stopped'`); see {@link isComplete}.
   */
  terminationReason(): TerminationReason;

  /** Graceful shutdown: reject new inject() calls, process queued events, terminate at quiescence. */
  drain(): void;

  /** Immediate shutdown: discard queued events, wait for in-flight, terminate. */
  close(): void;
}
