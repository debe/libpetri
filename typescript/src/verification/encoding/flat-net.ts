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
  /**
   * Environment places whose tokens the analysis MODELS as externally injected
   * (VER-006). Maps env place name -> injection bound: a number caps injection
   * (`Bounded(k)`), `null` means unbounded (`AlwaysAvailable`). Absent entries
   * (incl. `Ignore` mode) are not injected. The encoder emits one injection CHC
   * rule per entry and the incidence matrix gains one injector column per entry
   * so closed-net P-invariants over these places are correctly discarded.
   */
  readonly environmentInjection: ReadonlyMap<string, number | null>;
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
