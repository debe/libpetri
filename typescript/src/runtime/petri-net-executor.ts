import type { Marking } from './marking.js';
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

  /** Inject an external token. Returns true if accepted. */
  inject<T>(place: EnvironmentPlace<T>, token: Token<T>): Promise<boolean>;

  /** Graceful shutdown: reject new inject() calls, process queued events, terminate at quiescence. */
  drain(): void;

  /** Immediate shutdown: discard queued events, wait for in-flight, terminate. */
  close(): void;
}
