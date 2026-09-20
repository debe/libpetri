import type { Place } from './place.js';
import type { Token } from './token.js';
import { tokenOf, tokenAt } from './token.js';

/**
 * An output entry: place + token pair.
 */
export interface OutputEntry {
  readonly place: Place<any>;
  readonly token: Token<any>;
}

/**
 * Collects output tokens produced by a transition action.
 */
export class TokenOutput {
  private readonly _entries: OutputEntry[] = [];

  /**
   * Epoch-clock reader for the tokens this collector mints, or `undefined` for the wall
   * clock ([TIME-015]).
   *
   * A token written as `ctx.output(place, value)` is **executor-produced**: the action
   * supplies a *value* and libpetri chooses the `createdAt`. The line is drawn by who
   * chooses the timestamp, not who supplies the value — so under an injected clock these
   * follow it, as do the recovery outputs the executor synthesises on an action timeout
   * (which reach the marking through this same collector). Reading the boundary the other
   * way would leave the bulk of a run's tokens on wall time under a virtual clock:
   * defeating the requirement while appearing to satisfy it.
   *
   * `undefined` rather than a defaulted `Date.now` so the no-clock path stays exactly
   * {@link tokenOf}, allocating and dispatching nothing extra.
   */
  private readonly epochNowMs: (() => number) | undefined;

  constructor(epochNowMs?: () => number) {
    this.epochNowMs = epochNowMs;
  }

  /**
   * Once true, further writes are dropped instead of appended. Set by the executor
   * (via {@link import('./transition-context.js').TransitionContext.detachForTimeout})
   * when a firing times out, so the action it has stopped waiting for can no longer
   * reach the marking. Irreversible.
   */
  private detached = false;

  /**
   * Add a value to an output place (creates token with the current timestamp).
   *
   * The timestamp comes from the executor's epoch clock when one was injected, and from
   * the wall clock otherwise — see {@link epochNowMs}.
   */
  add<T>(place: Place<T>, value: T): this {
    if (this.detached) return this;
    const epoch = this.epochNowMs;
    const token = epoch === undefined ? tokenOf(value) : tokenAt(value, epoch());
    this._entries.push({ place, token });
    return this;
  }

  /** Add a pre-existing token to an output place. */
  addToken<T>(place: Place<T>, token: Token<T>): this {
    if (this.detached) return this;
    this._entries.push({ place, token });
    return this;
  }

  /**
   * @internal Severs this collector: subsequent {@link add}/{@link addToken} calls are
   * dropped. Executor machinery invoked when a firing times out — never call from an action.
   */
  detach(): void {
    this.detached = true;
  }

  /** Returns all collected outputs. */
  entries(): readonly OutputEntry[] {
    return this._entries;
  }

  /** Check if any outputs were produced. */
  isEmpty(): boolean {
    return this._entries.length === 0;
  }

  /** Returns the set of place names that received tokens. */
  placesWithTokens(): Set<string> {
    const result = new Set<string>();
    for (const entry of this._entries) {
      result.add(entry.place.name);
    }
    return result;
  }
}
