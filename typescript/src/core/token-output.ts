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

  /** Add a value to an output place (creates token with current timestamp). */
  add<T>(place: Place<T>, value: T): this {
    this._entries.push({ place, token: tokenOf(value) });
    return this;
  }

  /** Add a pre-existing token to an output place. */
  addToken<T>(place: Place<T>, token: Token<T>): this {
    this._entries.push({ place, token });
    return this;
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
