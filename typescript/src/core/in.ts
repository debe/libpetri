import type { Place } from './place.js';

/**
 * Input specification with cardinality. Purely structural (IO-006): cardinality
 * determines how many tokens to consume; there is no per-token predicate.
 *
 * Conditional token selection is modeled with multiple conflicting transitions
 * and XOR-on-input semantics rather than a predicate coupled to the enablement
 * check.
 *
 * Inputs are always AND-joined (all must be satisfied to enable transition).
 * XOR on inputs is modeled via multiple transitions (conflict).
 */
export type In = InOne | InExactly | InAll | InAtLeast;

export interface InOne<T = any> {
  readonly type: 'one';
  readonly place: Place<T>;
}

export interface InExactly<T = any> {
  readonly type: 'exactly';
  readonly place: Place<T>;
  readonly count: number;
}

export interface InAll<T = any> {
  readonly type: 'all';
  readonly place: Place<T>;
}

export interface InAtLeast<T = any> {
  readonly type: 'at-least';
  readonly place: Place<T>;
  readonly minimum: number;
}

// ==================== Factory Functions ====================

/** Consume exactly 1 token (standard CPN semantics). */
export function one<T>(place: Place<T>): InOne<T> {
  return { type: 'one', place };
}

/** Consume exactly N tokens (batching). */
export function exactly<T>(count: number, place: Place<T>): InExactly<T> {
  if (count < 1) {
    throw new Error(`count must be >= 1, got: ${count}`);
  }
  return { type: 'exactly', place, count };
}

/** Consume all available tokens (must be 1+). */
export function all<T>(place: Place<T>): InAll<T> {
  return { type: 'all', place };
}

/** Wait for N+ tokens, consume all when enabled. */
export function atLeast<T>(minimum: number, place: Place<T>): InAtLeast<T> {
  if (minimum < 1) {
    throw new Error(`minimum must be >= 1, got: ${minimum}`);
  }
  return { type: 'at-least', place, minimum };
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
