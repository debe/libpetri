import type { Place } from './place.js';

/**
 * Input specification with cardinality and optional guard predicate.
 * CPN-compliant: cardinality determines how many tokens to consume,
 * guard filters which tokens are eligible.
 *
 * Inputs are always AND-joined (all must be satisfied to enable transition).
 * XOR on inputs is modeled via multiple transitions (conflict).
 */
export type In = InOne | InExactly | InAll | InAtLeast;

export interface InOne<T = any> {
  readonly type: 'one';
  readonly place: Place<T>;
  readonly guard?: (value: T) => boolean;
}

export interface InExactly<T = any> {
  readonly type: 'exactly';
  readonly place: Place<T>;
  readonly count: number;
  readonly guard?: (value: T) => boolean;
}

export interface InAll<T = any> {
  readonly type: 'all';
  readonly place: Place<T>;
  readonly guard?: (value: T) => boolean;
}

export interface InAtLeast<T = any> {
  readonly type: 'at-least';
  readonly place: Place<T>;
  readonly minimum: number;
  readonly guard?: (value: T) => boolean;
}

// ==================== Factory Functions ====================

/** Consume exactly 1 token (standard CPN semantics). Optional guard filters eligible tokens. */
export function one<T>(place: Place<T>, guard?: (value: T) => boolean): InOne<T> {
  return guard !== undefined ? { type: 'one', place, guard } : { type: 'one', place };
}

/** Consume exactly N tokens (batching). Optional guard filters eligible tokens. */
export function exactly<T>(count: number, place: Place<T>, guard?: (value: T) => boolean): InExactly<T> {
  if (count < 1) {
    throw new Error(`count must be >= 1, got: ${count}`);
  }
  return guard !== undefined ? { type: 'exactly', place, count, guard } : { type: 'exactly', place, count };
}

/** Consume all available tokens (must be 1+). Optional guard filters eligible tokens. */
export function all<T>(place: Place<T>, guard?: (value: T) => boolean): InAll<T> {
  return guard !== undefined ? { type: 'all', place, guard } : { type: 'all', place };
}

/** Wait for N+ tokens, consume all when enabled. Optional guard filters eligible tokens. */
export function atLeast<T>(minimum: number, place: Place<T>, guard?: (value: T) => boolean): InAtLeast<T> {
  if (minimum < 1) {
    throw new Error(`minimum must be >= 1, got: ${minimum}`);
  }
  return guard !== undefined
    ? { type: 'at-least', place, minimum, guard }
    : { type: 'at-least', place, minimum };
}

// ==================== Helper Functions ====================

/** Returns the minimum number of tokens required to enable. */
export function requiredCount(spec: In): number {
  switch (spec.type) {
    case 'one': return 1;
    case 'exactly': return spec.count;
    case 'all': return 1;
    case 'at-least': return spec.minimum;
  }
}

/**
 * Returns the actual number of tokens to consume given the available count.
 * - One: always consumes 1
 * - Exactly: always consumes exactly count
 * - All: consumes all available
 * - AtLeast: consumes all available (when enabled, i.e., >= minimum)
 */
export function consumptionCount(spec: In, available: number): number {
  if (available < requiredCount(spec)) {
    throw new Error(
      `Cannot consume from '${spec.place.name}': available=${available}, required=${requiredCount(spec)}`
    );
  }
  switch (spec.type) {
    case 'one': return 1;
    case 'exactly': return spec.count;
    case 'all': return available;
    case 'at-least': return available;
  }
}
