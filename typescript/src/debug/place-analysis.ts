/**
 * Analyze places for start/end/environment classification.
 * TypeScript port of Java's PlaceAnalysis.
 */

import type { PetriNet } from '../core/petri-net.js';
import type { Place } from '../core/place.js';

export interface PlaceAnalysisInfo {
  readonly tokenType: string;
  readonly hasIncoming: boolean;
  readonly hasOutgoing: boolean;
}

export class PlaceAnalysis {
  private readonly _data: ReadonlyMap<string, PlaceAnalysisInfo>;

  constructor(data: ReadonlyMap<string, PlaceAnalysisInfo>) {
    this._data = data;
  }

  get data(): ReadonlyMap<string, PlaceAnalysisInfo> {
    return this._data;
  }

  isStart(placeName: string): boolean {
    const info = this._data.get(placeName);
    return info != null && !info.hasIncoming;
  }

  isEnd(placeName: string): boolean {
    const info = this._data.get(placeName);
    return info != null && !info.hasOutgoing;
  }

  /** Build place analysis from a PetriNet. */
  static from(net: PetriNet): PlaceAnalysis {
    const data = new Map<string, { tokenType: string; hasIncoming: boolean; hasOutgoing: boolean }>();

    function ensure(place: Place<unknown>): { tokenType: string; hasIncoming: boolean; hasOutgoing: boolean } {
      let info = data.get(place.name);
      if (!info) {
        info = { tokenType: 'unknown', hasIncoming: false, hasOutgoing: false };
        data.set(place.name, info);
      }
      return info;
    }

    for (const transition of net.transitions) {
      // Input arcs: place → transition (place has outgoing)
      for (const input of transition.inputSpecs) {
        const info = ensure((input as { place: Place<unknown> }).place);
        info.hasOutgoing = true;
      }

      // Output arcs: transition → place (place has incoming)
      if (transition.outputSpec) {
        const outputPlaces = collectOutputPlaces(transition.outputSpec);
        for (const place of outputPlaces) {
          const info = ensure(place);
          info.hasIncoming = true;
        }
      }

      // Inhibitor arcs: just ensure place exists
      for (const inh of transition.inhibitors) {
        ensure((inh as { place: Place<unknown> }).place);
      }

      // Read arcs: place has outgoing (read = test without consuming)
      for (const read of transition.reads) {
        const info = ensure((read as { place: Place<unknown> }).place);
        info.hasOutgoing = true;
      }

      // Reset arcs: just ensure place exists
      for (const reset of transition.resets) {
        ensure((reset as { place: Place<unknown> }).place);
      }
    }

    return new PlaceAnalysis(data as ReadonlyMap<string, PlaceAnalysisInfo>);
  }
}

/** Recursively collect all output places from an Out spec. */
function collectOutputPlaces(out: unknown): Place<unknown>[] {
  const spec = out as { type: string; place?: Place<unknown>; children?: unknown[]; child?: unknown; from?: Place<unknown>; to?: Place<unknown> };
  switch (spec.type) {
    case 'place':
      return spec.place ? [spec.place] : [];
    case 'and':
    case 'xor':
      return (spec.children ?? []).flatMap(c => collectOutputPlaces(c));
    case 'timeout':
      return spec.child ? collectOutputPlaces(spec.child) : [];
    case 'forward-input':
      return spec.to ? [spec.to] : [];
    default:
      return [];
  }
}
