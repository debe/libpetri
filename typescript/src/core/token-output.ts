import type { Place } from './place.js';
import type { Token } from './token.js';
import { tokenOf } from './token.js';

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
   * Once true, further writes are dropped instead of appended. Set by the executor
   * (via {@link import('./transition-context.js').TransitionContext.detachForTimeout})
   * when a firing times out, so the action it has stopped waiting for can no longer
   * reach the marking. Irreversible.
   */
  private detached = false;

  /** Add a value to an output place (creates token with current timestamp). */
  add<T>(place: Place<T>, value: T): this {
    if (this.detached) return this;
    this._entries.push({ place, token: tokenOf(value) });
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
