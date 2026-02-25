import type { Marking } from './marking.js';
import type { EnvironmentPlace } from '../core/place.js';
import type { Token } from '../core/token.js';

/**
 * Interface for Petri net executors.
 */
export interface PetriNetExecutor {
  /** Run the net until quiescence or timeout. */
  run(timeoutMs?: number): Promise<Marking>;

  /** Inject an external token. Returns true if accepted. */
  inject<T>(place: EnvironmentPlace<T>, token: Token<T>): Promise<boolean>;

  /** Shut down the executor. */
  close(): void;
}
