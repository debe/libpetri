import type { Place } from './place.js';
import type { Token } from './token.js';

/**
 * Consumed input tokens bound to their source places.
 *
 * Passed to TransitionAction as the `input` parameter, providing
 * type-safe read access to tokens consumed from input places.
 */
export class TokenInput {
  private readonly tokens = new Map<string, Token<any>[]>();

  /** Add a token (used by executor when firing transition). */
  add<T>(place: Place<T>, token: Token<T>): this {
    const existing = this.tokens.get(place.name);
    if (existing) {
      existing.push(token);
    } else {
      this.tokens.set(place.name, [token]);
    }
    return this;
  }

  /** Get all tokens for a place. */
  getAll<T>(place: Place<T>): readonly Token<T>[] {
    return (this.tokens.get(place.name) ?? []) as Token<T>[];
  }

  /** Get the first token for a place. Throws if no tokens. */
  get<T>(place: Place<T>): Token<T> {
    const list = this.tokens.get(place.name);
    if (!list || list.length === 0) {
      throw new Error(`No token for place: ${place.name}`);
    }
    return list[0] as Token<T>;
  }

  /** Get the first token's value for a place. Throws if no tokens. */
  value<T>(place: Place<T>): T {
    return this.get(place).value;
  }

  /** Get all token values for a place. */
  values<T>(place: Place<T>): readonly T[] {
    return this.getAll(place).map(t => t.value);
  }

  /** Get token count for a place. */
  count(place: Place<any>): number {
    return this.getAll(place).length;
  }

  /** Check if any tokens exist for a place. */
  has(place: Place<any>): boolean {
    return this.count(place) > 0;
  }
}
