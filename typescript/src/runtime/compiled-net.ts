/**
 * @module compiled-net
 *
 * Integer-indexed, precomputed representation of a PetriNet for bitmap-based execution.
 *
 * **Precomputation strategy**: At compile time, all places and transitions are assigned
 * stable integer IDs. Input/inhibitor arcs are converted to Uint32Array bitmasks (one per
 * transition), enabling O(W) enablement checks via bitwise AND where W = ceil(numPlaces/32).
 *
 * **Why bitmaps**: JS bitwise operators work natively on 32-bit integers. Using Uint32Array
 * with 32-bit words (WORD_SHIFT=5) avoids BigInt overhead while keeping enablement checks
 * branch-free and cache-friendly. For a typical 50-place net, W=2 words per mask.
 *
 * **Reverse index**: A place-to-transitions mapping enables the dirty set pattern —
 * when a place's marking changes, only affected transitions are re-evaluated.
 */
import type { PetriNet } from '../core/petri-net.js';
import type { Place } from '../core/place.js';
import type { Transition } from '../core/transition.js';
import { requiredCount } from '../core/in.js';
import { allPlaces } from '../core/out.js';

/** 32-bit words for JS bitwise ops. */
export const WORD_SHIFT = 5;
export const BIT_MASK = 31;

export interface CardinalityCheck {
  readonly placeIds: readonly number[];
  readonly requiredCounts: readonly number[];
}

/**
 * Integer-indexed, precomputed representation of a PetriNet for bitmap-based execution.
 *
 * Uses Uint32Array masks with 32-bit words (JS bitwise ops work on 32-bit ints natively).
 */
export class CompiledNet {
  readonly net: PetriNet;
  readonly placeCount: number;
  readonly transitionCount: number;
  readonly wordCount: number;

  // ID mappings
  private readonly _placesById: Place<any>[];
  private readonly _transitionsById: Transition[];
  private readonly _placeIndex: Map<string, number>;
  private readonly _transitionIndex: Map<Transition, number>;

  // Precomputed masks per transition
  private readonly _needsMask: Uint32Array[];
  private readonly _inhibitorMask: Uint32Array[];

  // Reverse index: place -> affected transition IDs
  private readonly _placeToTransitions: number[][];

  // Consumption place IDs per transition (input + reset places)
  private readonly _consumptionPlaceIds: number[][];

  // Cardinality and guard flags
  private readonly _cardinalityChecks: (CardinalityCheck | null)[];
  private readonly _hasGuards: boolean[];

  private constructor(net: PetriNet) {
    this.net = net;

    // Collect all places
    const allPlacesSet = new Map<string, Place<any>>();
    for (const t of net.transitions) {
      for (const spec of t.inputSpecs) allPlacesSet.set(spec.place.name, spec.place);
      for (const r of t.reads) allPlacesSet.set(r.place.name, r.place);
      for (const inh of t.inhibitors) allPlacesSet.set(inh.place.name, inh.place);
      for (const rst of t.resets) allPlacesSet.set(rst.place.name, rst.place);
      if (t.outputSpec !== null) {
        for (const p of allPlaces(t.outputSpec)) allPlacesSet.set(p.name, p);
      }
    }
    for (const p of net.places) allPlacesSet.set(p.name, p);

    this.placeCount = allPlacesSet.size;
    this.wordCount = (this.placeCount + BIT_MASK) >>> WORD_SHIFT;

    // Assign place IDs
    this._placesById = [...allPlacesSet.values()];
    this._placeIndex = new Map();
    for (let i = 0; i < this._placesById.length; i++) {
      this._placeIndex.set(this._placesById[i]!.name, i);
    }

    // Assign transition IDs
    this._transitionsById = [...net.transitions];
    this.transitionCount = this._transitionsById.length;
    this._transitionIndex = new Map();
    for (let i = 0; i < this._transitionsById.length; i++) {
      this._transitionIndex.set(this._transitionsById[i]!, i);
    }

    // Precompute masks
    this._needsMask = new Array(this.transitionCount);
    this._inhibitorMask = new Array(this.transitionCount);
    this._consumptionPlaceIds = new Array(this.transitionCount);
    this._cardinalityChecks = new Array(this.transitionCount).fill(null);
    this._hasGuards = new Array(this.transitionCount).fill(false);

    const placeToTransitionsList: number[][] = new Array(this.placeCount);
    for (let i = 0; i < this.placeCount; i++) {
      placeToTransitionsList[i] = [];
    }

    for (let tid = 0; tid < this.transitionCount; tid++) {
      const t = this._transitionsById[tid]!;
      const needs = new Uint32Array(this.wordCount);
      const inhibitors = new Uint32Array(this.wordCount);

      let needsCardinality = false;

      // Input specs
      for (const inSpec of t.inputSpecs) {
        const pid = this._placeIndex.get(inSpec.place.name)!;
        setBit(needs, pid);
        placeToTransitionsList[pid]!.push(tid);

        if (inSpec.type !== 'one') {
          needsCardinality = true;
        }
        if (inSpec.guard) {
          this._hasGuards[tid] = true;
        }
      }

      // Build cardinality check if needed
      if (needsCardinality) {
        const pids: number[] = [];
        const reqs: number[] = [];
        for (const inSpec of t.inputSpecs) {
          pids.push(this._placeIndex.get(inSpec.place.name)!);
          reqs.push(requiredCount(inSpec));
        }
        this._cardinalityChecks[tid] = { placeIds: pids, requiredCounts: reqs };
      }

      // Read arcs
      for (const arc of t.reads) {
        const pid = this._placeIndex.get(arc.place.name)!;
        setBit(needs, pid);
        placeToTransitionsList[pid]!.push(tid);
      }

      // Inhibitor arcs
      for (const arc of t.inhibitors) {
        const pid = this._placeIndex.get(arc.place.name)!;
        setBit(inhibitors, pid);
        placeToTransitionsList[pid]!.push(tid);
      }

      // Reset arcs (add to affected transitions)
      for (const arc of t.resets) {
        const pid = this._placeIndex.get(arc.place.name)!;
        placeToTransitionsList[pid]!.push(tid);
      }

      // Consumption place IDs (input + reset, deduplicated)
      const consumptionSet = new Set<number>();
      for (const spec of t.inputSpecs) consumptionSet.add(this._placeIndex.get(spec.place.name)!);
      for (const arc of t.resets) consumptionSet.add(this._placeIndex.get(arc.place.name)!);
      this._consumptionPlaceIds[tid] = [...consumptionSet];

      this._needsMask[tid] = needs;
      this._inhibitorMask[tid] = inhibitors;
    }

    // Build reverse index: deduplicate transition IDs per place
    this._placeToTransitions = new Array(this.placeCount);
    for (let pid = 0; pid < this.placeCount; pid++) {
      this._placeToTransitions[pid] = [...new Set(placeToTransitionsList[pid]!)];
    }
  }

  static compile(net: PetriNet): CompiledNet {
    return new CompiledNet(net);
  }

  // ==================== Accessors ====================

  place(pid: number): Place<any> { return this._placesById[pid]!; }
  transition(tid: number): Transition { return this._transitionsById[tid]!; }

  placeId(place: Place<any>): number {
    const id = this._placeIndex.get(place.name);
    if (id === undefined) throw new Error(`Unknown place: ${place.name}`);
    return id;
  }

  transitionId(t: Transition): number {
    const id = this._transitionIndex.get(t);
    if (id === undefined) throw new Error(`Unknown transition: ${t.name}`);
    return id;
  }

  affectedTransitions(pid: number): readonly number[] {
    return this._placeToTransitions[pid]!;
  }

  consumptionPlaceIds(tid: number): readonly number[] {
    return this._consumptionPlaceIds[tid]!;
  }

  cardinalityCheck(tid: number): CardinalityCheck | null {
    return this._cardinalityChecks[tid]!;
  }

  hasGuards(tid: number): boolean {
    return this._hasGuards[tid]!;
  }

  // ==================== Enablement Check ====================

  /**
   * Two-phase bitmap enablement check for a transition:
   * 1. **Presence check**: verifies all required places (inputs + reads) have tokens
   *    via `containsAll(snapshot, needsMask)`.
   * 2. **Inhibitor check**: verifies no inhibitor places have tokens
   *    via `!intersects(snapshot, inhibitorMask)`.
   *
   * This is a necessary but not sufficient condition — cardinality and guard checks
   * are performed separately by the executor for transitions that pass this fast path.
   */
  canEnableBitmap(tid: number, markingSnapshot: Uint32Array): boolean {
    // All needed places present?
    if (!containsAll(markingSnapshot, this._needsMask[tid]!)) return false;
    // No inhibitors active?
    if (intersects(markingSnapshot, this._inhibitorMask[tid]!)) return false;
    return true;
  }
}

// ==================== Bitmap Helpers ====================

export function setBit(arr: Uint32Array, bit: number): void {
  arr[bit >>> WORD_SHIFT]! |= (1 << (bit & BIT_MASK));
}

export function clearBit(arr: Uint32Array, bit: number): void {
  arr[bit >>> WORD_SHIFT]! &= ~(1 << (bit & BIT_MASK));
}

export function testBit(arr: Uint32Array, bit: number): boolean {
  return (arr[bit >>> WORD_SHIFT]! & (1 << (bit & BIT_MASK))) !== 0;
}

/** Checks if all bits in mask are set in snapshot. */
export function containsAll(snapshot: Uint32Array, mask: Uint32Array): boolean {
  for (let i = 0; i < mask.length; i++) {
    const m = mask[i]!;
    if (m === 0) continue;
    const s = i < snapshot.length ? snapshot[i]! : 0;
    // Use >>> 0 to coerce the bitwise AND result to unsigned. Without this,
    // when bit 31 (the sign bit) is set, (s & m) returns a negative signed
    // int32 while m (from Uint32Array) is unsigned, causing a false mismatch.
    if (((s & m) >>> 0) !== m) return false;
  }
  return true;
}

/** Checks if any bit in mask is set in snapshot. */
export function intersects(snapshot: Uint32Array, mask: Uint32Array): boolean {
  for (let i = 0; i < mask.length; i++) {
    const m = mask[i]!;
    if (m === 0) continue;
    if (i < snapshot.length && (snapshot[i]! & m) !== 0) return true;
  }
  return false;
}

