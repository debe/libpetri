import type { Place } from '../../core/place.js';
import type { FlatTransition } from './flat-transition.js';

/**
 * A flattened Petri net with indexed places and XOR-expanded transitions.
 *
 * Intermediate representation between the high-level PetriNet and Z3 CHC encoding.
 */
export interface FlatNet {
  /** Ordered list of places (index = position). */
  readonly places: readonly Place<any>[];
  /** Reverse lookup: place name -> index. */
  readonly placeIndex: ReadonlyMap<string, number>;
  /** XOR-expanded flat transitions. */
  readonly transitions: readonly FlatTransition[];
  /** For bounded environment places: place name -> max tokens. */
  readonly environmentBounds: ReadonlyMap<string, number>;
}

export function flatNetPlaceCount(net: FlatNet): number {
  return net.places.length;
}

export function flatNetTransitionCount(net: FlatNet): number {
  return net.transitions.length;
}

export function flatNetIndexOf(net: FlatNet, place: Place<any>): number {
  return net.placeIndex.get(place.name) ?? -1;
}
