import type { Place } from '../core/place.js';

/**
 * Safety properties that can be verified via IC3/PDR.
 *
 * Each property is encoded as an error condition: if a reachable state
 * violates the property, Spacer finds a counterexample. If no violation
 * is reachable, the property is proven.
 */
export type SmtProperty = DeadlockFree | MutualExclusion | PlaceBound | Unreachable;

/** Deadlock-freedom: no reachable marking has all transitions disabled. */
export interface DeadlockFree {
  readonly type: 'deadlock-free';
}

/** Mutual exclusion: two places never have tokens simultaneously. */
export interface MutualExclusion {
  readonly type: 'mutual-exclusion';
  readonly p1: Place<any>;
  readonly p2: Place<any>;
}

/** Place bound: a place never exceeds a given token count. */
export interface PlaceBound {
  readonly type: 'place-bound';
  readonly place: Place<any>;
  readonly bound: number;
}

/** Unreachability: the given places never all have tokens simultaneously. */
export interface Unreachable {
  readonly type: 'unreachable';
  readonly places: ReadonlySet<Place<any>>;
}

// Factory functions

export function deadlockFree(): DeadlockFree {
  return { type: 'deadlock-free' };
}

export function mutualExclusion(p1: Place<any>, p2: Place<any>): MutualExclusion {
  return { type: 'mutual-exclusion', p1, p2 };
}

export function placeBound(place: Place<any>, bound: number): PlaceBound {
  return { type: 'place-bound', place, bound };
}

export function unreachable(places: ReadonlySet<Place<any>>): Unreachable {
  return { type: 'unreachable', places: new Set(places) };
}

/** Human-readable description of a property. */
export function propertyDescription(prop: SmtProperty): string {
  switch (prop.type) {
    case 'deadlock-free':
      return 'Deadlock-freedom';
    case 'mutual-exclusion':
      return `Mutual exclusion of ${prop.p1.name} and ${prop.p2.name}`;
    case 'place-bound':
      return `Place ${prop.place.name} bounded by ${prop.bound}`;
    case 'unreachable':
      return `Unreachability of marking with tokens in {${[...prop.places].map(p => p.name).join(', ')}}`;
  }
}
