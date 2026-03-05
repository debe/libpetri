import type { Place } from '../core/place.js';

/** @internal Symbol key restricting construction to the builder and factory methods. */
const MARKING_STATE_KEY = Symbol('MarkingState.internal');

/**
 * Immutable snapshot of a Petri net marking for state space analysis.
 *
 * Maps places (by name) to integer token counts. Only stores places with count > 0.
 * Used for invariant computation and structural verification, not runtime execution.
 */
export class MarkingState {
  private readonly tokenCounts: ReadonlyMap<string, number>;
  private readonly placesByName: ReadonlyMap<string, Place<any>>;

  /** @internal Use {@link MarkingState.builder} or {@link MarkingState.empty} to create instances. */
  constructor(key: symbol, tokenCounts: Map<string, number>, placesByName: Map<string, Place<any>>) {
    if (key !== MARKING_STATE_KEY) throw new Error('Use MarkingState.builder() to create instances');
    this.tokenCounts = tokenCounts;
    this.placesByName = placesByName;
  }

  /** Returns the token count for a place (0 if absent). */
  tokens(place: Place<any>): number {
    return this.tokenCounts.get(place.name) ?? 0;
  }

  /** Checks if a place has at least one token. */
  hasTokens(place: Place<any>): boolean {
    return this.tokens(place) > 0;
  }

  /** Checks if any of the given places has tokens. */
  hasTokensInAny(places: Iterable<Place<any>>): boolean {
    for (const p of places) {
      if (this.hasTokens(p)) return true;
    }
    return false;
  }

  /** Returns all places with tokens > 0. */
  placesWithTokens(): Place<any>[] {
    return [...this.placesByName.values()];
  }

  /** Returns the total number of tokens. */
  totalTokens(): number {
    let sum = 0;
    for (const count of this.tokenCounts.values()) sum += count;
    return sum;
  }

  /** Checks if no tokens exist anywhere. */
  isEmpty(): boolean {
    return this.tokenCounts.size === 0;
  }

  toString(): string {
    if (this.tokenCounts.size === 0) return '{}';
    const entries = [...this.tokenCounts.entries()]
      .sort(([a], [b]) => a.localeCompare(b))
      .map(([name, count]) => `${name}:${count}`);
    return `{${entries.join(', ')}}`;
  }

  static empty(): MarkingState {
    return new MarkingState(MARKING_STATE_KEY, new Map(), new Map());
  }

  static builder(): MarkingStateBuilder {
    return new MarkingStateBuilder();
  }
}

export class MarkingStateBuilder {
  private readonly tokenCounts = new Map<string, number>();
  private readonly placesByName = new Map<string, Place<any>>();

  /** Sets the token count for a place. */
  tokens(place: Place<any>, count: number): this {
    if (count < 0) throw new Error(`Token count cannot be negative: ${count}`);
    if (count > 0) {
      this.tokenCounts.set(place.name, count);
      this.placesByName.set(place.name, place);
    } else {
      this.tokenCounts.delete(place.name);
      this.placesByName.delete(place.name);
    }
    return this;
  }

  /** Adds tokens to a place. */
  addTokens(place: Place<any>, count: number): this {
    if (count < 0) throw new Error(`Token count cannot be negative: ${count}`);
    if (count > 0) {
      const current = this.tokenCounts.get(place.name) ?? 0;
      this.tokenCounts.set(place.name, current + count);
      this.placesByName.set(place.name, place);
    }
    return this;
  }

  /** Removes tokens from a place. Throws if insufficient. */
  removeTokens(place: Place<any>, count: number): this {
    const current = this.tokenCounts.get(place.name) ?? 0;
    const newCount = current - count;
    if (newCount < 0) {
      throw new Error(
        `Cannot remove ${count} tokens from ${place.name} (has ${current})`,
      );
    }
    if (newCount === 0) {
      this.tokenCounts.delete(place.name);
      this.placesByName.delete(place.name);
    } else {
      this.tokenCounts.set(place.name, newCount);
    }
    return this;
  }

  /** Copies all token counts from another marking state. */
  copyFrom(other: MarkingState): this {
    for (const p of other.placesWithTokens()) {
      this.tokenCounts.set(p.name, other.tokens(p));
      this.placesByName.set(p.name, p);
    }
    return this;
  }

  build(): MarkingState {
    return new MarkingState(MARKING_STATE_KEY, new Map(this.tokenCounts), new Map(this.placesByName));
  }
}
