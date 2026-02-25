/**
 * @module marking
 *
 * Mutable token state (marking) of a running Petri net.
 *
 * Tokens per place are stored in FIFO arrays (push to end, shift from front).
 * Not thread-safe — all mutation occurs from the single-threaded orchestrator.
 *
 * For typical nets (≤10 tokens per place), Array.shift() is faster than a deque
 * due to cache locality. Only optimize if profiling shows a bottleneck.
 */
import type { Place } from '../core/place.js';
import type { Token } from '../core/token.js';

const EMPTY_TOKENS: readonly Token<any>[] = Object.freeze([]);

/** Anything that carries a place reference and an optional guard predicate. */
export interface GuardSpec<T = any> {
  readonly place: Place<T>;
  readonly guard?: (value: T) => boolean;
}

/**
 * Mutable marking (token state) of a Petri Net during execution.
 *
 * Tokens in each place are maintained in FIFO order (array: push to end, shift from front).
 * Not thread-safe — all access must be from the orchestrator.
 */
export class Marking {
  /** Place name -> FIFO queue of tokens. */
  private readonly tokens = new Map<string, Token<any>[]>();
  /** Place name -> Place reference (for inspection). */
  private readonly placeRefs = new Map<string, Place<any>>();

  static empty(): Marking {
    return new Marking();
  }

  static from(initial: Map<Place<any>, Token<any>[]>): Marking {
    const m = new Marking();
    for (const [place, tokens] of initial) {
      m.placeRefs.set(place.name, place);
      m.tokens.set(place.name, [...tokens]);
    }
    return m;
  }

  // ======================== Token Addition ========================

  addToken<T>(place: Place<T>, token: Token<T>): void {
    this.placeRefs.set(place.name, place);
    const queue = this.tokens.get(place.name);
    if (queue) {
      queue.push(token);
    } else {
      this.tokens.set(place.name, [token]);
    }
  }

  // ======================== Token Removal ========================

  /** Removes and returns the oldest token. Returns null if empty. */
  removeFirst<T>(place: Place<T>): Token<T> | null {
    const queue = this.tokens.get(place.name);
    if (!queue || queue.length === 0) return null;
    return queue.shift() as Token<T>;
  }

  /** Removes and returns all tokens from a place. */
  removeAll<T>(place: Place<T>): Token<T>[] {
    const queue = this.tokens.get(place.name);
    if (!queue || queue.length === 0) return [];
    const result = [...queue] as Token<T>[];
    queue.length = 0;
    return result;
  }

  /**
   * Removes and returns the first token whose value satisfies the guard predicate.
   *
   * Performs a linear scan of the place's FIFO queue. If no guard is provided,
   * behaves like `removeFirst()`. If a guard is provided, skips non-matching
   * tokens and splices the first match out of the queue (O(n) worst case).
   */
  removeFirstMatching(spec: GuardSpec): Token<any> | null {
    const queue = this.tokens.get(spec.place.name);
    if (!queue || queue.length === 0) return null;
    if (!spec.guard) {
      return queue.shift()!;
    }
    for (let i = 0; i < queue.length; i++) {
      const token = queue[i]!;
      if (spec.guard(token.value)) {
        queue.splice(i, 1);
        return token;
      }
    }
    return null;
  }

  // ======================== Token Inspection ========================

  /** Check if any token matches a guard predicate. */
  hasMatchingToken(spec: GuardSpec): boolean {
    const queue = this.tokens.get(spec.place.name);
    if (!queue || queue.length === 0) return false;
    if (!spec.guard) return true;
    return queue.some(t => spec.guard!(t.value));
  }

  /**
   * Counts tokens in a place whose values satisfy the guard predicate.
   *
   * If no guard is provided, returns the total token count (O(1)).
   * With a guard, performs a linear scan over all tokens (O(n)).
   * Used by the executor for enablement checks on guarded `all`/`at-least` inputs.
   */
  countMatching(spec: GuardSpec): number {
    const queue = this.tokens.get(spec.place.name);
    if (!queue || queue.length === 0) return 0;
    if (!spec.guard) return queue.length;
    let count = 0;
    for (const t of queue) {
      if (spec.guard(t.value)) count++;
    }
    return count;
  }

  /**
   * Returns tokens in a place. **Returns a live reference** to the internal
   * array — callers must not mutate it. Copy with `[...peekTokens(p)]` if
   * mutation or snapshot semantics are needed.
   */
  peekTokens<T>(place: Place<T>): readonly Token<T>[] {
    return (this.tokens.get(place.name) ?? EMPTY_TOKENS) as readonly Token<T>[];
  }

  /** Returns the oldest token without removing it. */
  peekFirst<T>(place: Place<T>): Token<T> | null {
    const queue = this.tokens.get(place.name);
    return queue && queue.length > 0 ? queue[0] as Token<T> : null;
  }

  /** Checks if a place has any tokens. */
  hasTokens(place: Place<any>): boolean {
    const queue = this.tokens.get(place.name);
    return queue !== undefined && queue.length > 0;
  }

  /** Returns the number of tokens in a place. */
  tokenCount(place: Place<any>): number {
    const queue = this.tokens.get(place.name);
    return queue ? queue.length : 0;
  }

  // ======================== Debugging ========================

  toString(): string {
    const parts: string[] = [];
    for (const [name, queue] of this.tokens) {
      if (queue.length > 0) {
        parts.push(`${name}: ${queue.length}`);
      }
    }
    return `Marking{${parts.join(', ')}}`;
  }
}
