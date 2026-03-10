/**
 * @module precompiled-net
 *
 * Flat-array precompiled representation of a PetriNet for high-performance execution.
 *
 * **Design**: Compiles from a `CompiledNet`, converting all per-transition data into
 * flat typed arrays indexed by transition ID (tid) or place ID (pid). Eliminates Map
 * lookups and object traversals from the hot path.
 *
 * **Sparse enablement**: Each transition's needs/inhibitor masks are classified as
 * empty (-2), single-word (>=0), or multi-word (-1). Single-word masks avoid inner
 * loops entirely; multi-word uses precomputed sparse indices to skip zero words.
 *
 * **Opcode programs**: Input consumption is compiled to compact opcode sequences
 * (CONSUME_ONE, CONSUME_N, CONSUME_ALL, CONSUME_ATLEAST, RESET) that the executor
 * dispatches without inspecting In spec objects.
 *
 * @see CompiledNet for the base bitmap representation
 * @see PrecompiledNetExecutor for the executor that uses this representation
 */
import type { PetriNet } from '../core/petri-net.js';
import type { Place } from '../core/place.js';
import type { Transition } from '../core/transition.js';
import type { Out } from '../core/out.js';
import { CompiledNet, WORD_SHIFT, BIT_MASK } from './compiled-net.js';
import type { CardinalityCheck } from './compiled-net.js';
import { earliest as timingEarliest, latest as timingLatest, hasDeadline as timingHasDeadline } from '../core/timing.js';

// ==================== Opcodes ====================

/** Consume exactly 1 token from place. Next word: pid. */
export const CONSUME_ONE = 0;
/** Consume exactly N tokens. Next words: pid, count. */
export const CONSUME_N = 1;
/** Consume all tokens. Next word: pid. */
export const CONSUME_ALL = 2;
/** Consume at-least N tokens (consumes all). Next words: pid, minimum. */
export const CONSUME_ATLEAST = 3;
/** Reset (clear all tokens). Next word: pid. */
export const RESET = 4;

/** Sparse mask classification: no bits set. */
const SPARSE_EMPTY = -2;
/** Sparse mask classification: bits span multiple words. */
const SPARSE_MULTI = -1;

/**
 * Immutable precompiled representation of a Petri net.
 *
 * All data is stored in flat typed arrays indexed by tid/pid for cache-friendly,
 * branch-free access on the hot path. Compiled once, reused across executions.
 */
export class PrecompiledNet {
  // ==================== Identity ====================
  readonly compiled: CompiledNet;
  readonly placeCount: number;
  readonly transitionCount: number;
  readonly wordCount: number;

  // ==================== Place Cache ====================
  /** Places indexed by pid — avoids compiled.place(pid) indirection on hot path. */
  readonly places: readonly Place<any>[];

  // ==================== Opcode Programs ====================
  /** Per-transition consume opcode sequences. */
  readonly consumeOps: readonly (readonly number[])[];
  /** Per-transition read-arc place IDs. */
  readonly readOps: readonly (readonly number[])[];

  // ==================== Enablement Masks ====================
  readonly needsMask: readonly Uint32Array[];
  readonly inhibitorMask: readonly Uint32Array[];

  // ==================== Sparse Enablement (PERF-042) ====================
  readonly needsSingleWordIndex: Int8Array;
  readonly needsSingleWordMask: Uint32Array;
  readonly needsSparseIndices: readonly (readonly number[])[];
  readonly needsSparseMasks: readonly (readonly number[])[];

  readonly inhibitorSingleWordIndex: Int8Array;
  readonly inhibitorSingleWordMask: Uint32Array;
  readonly inhibitorSparseIndices: readonly (readonly number[])[];
  readonly inhibitorSparseMasks: readonly (readonly number[])[];

  // ==================== Timing (CONC-024) ====================
  readonly earliestMs: Float64Array;
  readonly latestMs: Float64Array;
  readonly hasDeadline: Uint8Array;

  // ==================== Priority (CONC-023) ====================
  readonly priorities: Int32Array;
  readonly transitionToPriorityIndex: Uint32Array;
  readonly priorityLevels: readonly number[];
  readonly distinctPriorityCount: number;

  // ==================== Output Fast Path ====================
  /** -2=no spec, -1=complex, >=0=single output place ID. */
  readonly simpleOutputPlaceId: Int32Array;

  // ==================== Input Precomputation ====================
  readonly inputPlaceCount: Uint32Array;
  readonly inputPlaceMaskWords: readonly Uint32Array[];

  // ==================== Reverse Index ====================
  readonly placeToTransitions: readonly (readonly number[])[];
  readonly consumptionPlaceIds: readonly (readonly number[])[];

  // ==================== Cardinality & Guards ====================
  readonly cardinalityChecks: readonly (CardinalityCheck | null)[];
  readonly hasGuards: readonly boolean[];

  // ==================== Global Flags ====================
  readonly allImmediate: boolean;
  readonly allSamePriority: boolean;
  readonly anyDeadlines: boolean;

  private constructor(compiled: CompiledNet) {
    this.compiled = compiled;
    this.placeCount = compiled.placeCount;
    this.transitionCount = compiled.transitionCount;
    this.wordCount = compiled.wordCount;

    const tc = compiled.transitionCount;
    const wc = compiled.wordCount;

    // Cache place references
    const places: Place<any>[] = new Array(this.placeCount);
    for (let pid = 0; pid < this.placeCount; pid++) {
      places[pid] = compiled.place(pid);
    }
    this.places = places;

    // Copy masks from CompiledNet
    const needsMask: Uint32Array[] = new Array(tc);
    const inhibitorMask: Uint32Array[] = new Array(tc);
    for (let tid = 0; tid < tc; tid++) {
      // Access via canEnableBitmap internals — copy the mask arrays
      // We need to extract them; use the CompiledNet's accessor pattern
      needsMask[tid] = new Uint32Array(wc);
      inhibitorMask[tid] = new Uint32Array(wc);
    }

    // Build needs/inhibitor masks by probing CompiledNet
    // We reconstruct from transition arc specs since CompiledNet doesn't expose raw masks
    for (let tid = 0; tid < tc; tid++) {
      const t = compiled.transition(tid);
      const needs = needsMask[tid]!;
      const inhibitors = inhibitorMask[tid]!;

      for (const inSpec of t.inputSpecs) {
        const pid = compiled.placeId(inSpec.place);
        needs[pid >>> WORD_SHIFT]! |= (1 << (pid & BIT_MASK));
      }
      for (const arc of t.reads) {
        const pid = compiled.placeId(arc.place);
        needs[pid >>> WORD_SHIFT]! |= (1 << (pid & BIT_MASK));
      }
      for (const arc of t.inhibitors) {
        const pid = compiled.placeId(arc.place);
        inhibitors[pid >>> WORD_SHIFT]! |= (1 << (pid & BIT_MASK));
      }
    }
    this.needsMask = needsMask;
    this.inhibitorMask = inhibitorMask;

    // ==================== Sparse Enablement ====================
    this.needsSingleWordIndex = new Int8Array(tc);
    this.needsSingleWordMask = new Uint32Array(tc);
    const needsSparseIndices: number[][] = new Array(tc);
    const needsSparseMasks: number[][] = new Array(tc);

    this.inhibitorSingleWordIndex = new Int8Array(tc);
    this.inhibitorSingleWordMask = new Uint32Array(tc);
    const inhibitorSparseIndices: number[][] = new Array(tc);
    const inhibitorSparseMasks: number[][] = new Array(tc);

    for (let tid = 0; tid < tc; tid++) {
      compileSparse(needsMask[tid]!, wc,
        this.needsSingleWordIndex, this.needsSingleWordMask,
        needsSparseIndices, needsSparseMasks, tid);
      compileSparse(inhibitorMask[tid]!, wc,
        this.inhibitorSingleWordIndex, this.inhibitorSingleWordMask,
        inhibitorSparseIndices, inhibitorSparseMasks, tid);
    }
    this.needsSparseIndices = needsSparseIndices;
    this.needsSparseMasks = needsSparseMasks;
    this.inhibitorSparseIndices = inhibitorSparseIndices;
    this.inhibitorSparseMasks = inhibitorSparseMasks;

    // ==================== Opcode Programs ====================
    const consumeOps: number[][] = new Array(tc);
    const readOps: number[][] = new Array(tc);
    for (let tid = 0; tid < tc; tid++) {
      const t = compiled.transition(tid);
      consumeOps[tid] = compileConsumeProgram(t, compiled);
      readOps[tid] = compileReadProgram(t, compiled);
    }
    this.consumeOps = consumeOps;
    this.readOps = readOps;

    // ==================== Reverse Index & Consumption ====================
    const placeToTransitions: number[][] = new Array(this.placeCount);
    const consumptionPlaceIds: number[][] = new Array(tc);
    for (let pid = 0; pid < this.placeCount; pid++) {
      placeToTransitions[pid] = [...compiled.affectedTransitions(pid)];
    }
    for (let tid = 0; tid < tc; tid++) {
      consumptionPlaceIds[tid] = [...compiled.consumptionPlaceIds(tid)];
    }
    this.placeToTransitions = placeToTransitions;
    this.consumptionPlaceIds = consumptionPlaceIds;

    // ==================== Cardinality & Guards ====================
    const cardinalityChecks: (CardinalityCheck | null)[] = new Array(tc);
    const hasGuards: boolean[] = new Array(tc);
    for (let tid = 0; tid < tc; tid++) {
      cardinalityChecks[tid] = compiled.cardinalityCheck(tid);
      hasGuards[tid] = compiled.hasGuards(tid);
    }
    this.cardinalityChecks = cardinalityChecks;
    this.hasGuards = hasGuards;

    // ==================== Timing ====================
    this.earliestMs = new Float64Array(tc);
    this.latestMs = new Float64Array(tc);
    this.hasDeadline = new Uint8Array(tc);
    let anyDeadlines = false;
    let allImm = true;

    for (let tid = 0; tid < tc; tid++) {
      const t = compiled.transition(tid);
      this.earliestMs[tid] = timingEarliest(t.timing);
      this.latestMs[tid] = timingLatest(t.timing);
      if (timingHasDeadline(t.timing)) {
        this.hasDeadline[tid] = 1;
        anyDeadlines = true;
      }
      if (t.timing.type !== 'immediate') allImm = false;
    }
    this.anyDeadlines = anyDeadlines;
    this.allImmediate = allImm;

    // ==================== Priority ====================
    this.priorities = new Int32Array(tc);
    const prioritySet = new Set<number>();
    const firstPriority = tc > 0 ? compiled.transition(0).priority : 0;
    let samePrio = true;

    for (let tid = 0; tid < tc; tid++) {
      const p = compiled.transition(tid).priority;
      this.priorities[tid] = p;
      prioritySet.add(p);
      if (p !== firstPriority) samePrio = false;
    }
    this.allSamePriority = samePrio;

    // Sort priorities descending
    const levels = [...prioritySet].sort((a, b) => b - a);
    this.priorityLevels = levels;
    this.distinctPriorityCount = levels.length;

    // Map tid -> priority queue index
    this.transitionToPriorityIndex = new Uint32Array(tc);
    const levelIndex = new Map<number, number>();
    for (let i = 0; i < levels.length; i++) {
      levelIndex.set(levels[i]!, i);
    }
    for (let tid = 0; tid < tc; tid++) {
      this.transitionToPriorityIndex[tid] = levelIndex.get(this.priorities[tid]!)!;
    }

    // ==================== Output Fast Path ====================
    this.simpleOutputPlaceId = new Int32Array(tc);
    for (let tid = 0; tid < tc; tid++) {
      const t = compiled.transition(tid);
      if (t.outputSpec === null) {
        this.simpleOutputPlaceId[tid] = -2; // no spec
      } else {
        const simplePid = simpleOutputPlace(t.outputSpec, compiled);
        this.simpleOutputPlaceId[tid] = simplePid;
      }
    }

    // ==================== Input Precomputation ====================
    this.inputPlaceCount = new Uint32Array(tc);
    const inputPlaceMaskWords: Uint32Array[] = new Array(tc);
    for (let tid = 0; tid < tc; tid++) {
      const t = compiled.transition(tid);
      this.inputPlaceCount[tid] = t.inputSpecs.length + t.reads.length;
      const mask = new Uint32Array(wc);
      for (const spec of t.inputSpecs) {
        const pid = compiled.placeId(spec.place);
        mask[pid >>> WORD_SHIFT]! |= (1 << (pid & BIT_MASK));
      }
      inputPlaceMaskWords[tid] = mask;
    }
    this.inputPlaceMaskWords = inputPlaceMaskWords;
  }

  // ==================== Factory Methods ====================

  static compile(net: PetriNet): PrecompiledNet {
    return new PrecompiledNet(CompiledNet.compile(net));
  }

  static compileFrom(compiled: CompiledNet): PrecompiledNet {
    return new PrecompiledNet(compiled);
  }

  // ==================== Sparse Enablement Check ====================

  /**
   * Three-case sparse enablement check:
   * 1. Empty mask (needsSingleWordIndex == -2): always passes
   * 2. Single-word mask (>=0): one comparison
   * 3. Multi-word mask (-1): iterate precomputed sparse indices
   */
  canEnableSparse(tid: number, snapshot: Uint32Array): boolean {
    // Check needs mask
    const needsIdx = this.needsSingleWordIndex[tid]!;
    if (needsIdx === SPARSE_EMPTY) {
      // No needs — passes
    } else if (needsIdx >= 0) {
      // Single word
      const m = this.needsSingleWordMask[tid]!;
      if ((snapshot[needsIdx]! & m) !== m) return false;
    } else {
      // Multi-word sparse
      const indices = this.needsSparseIndices[tid]!;
      const masks = this.needsSparseMasks[tid]!;
      for (let i = 0; i < indices.length; i++) {
        const m = masks[i]!;
        if ((snapshot[indices[i]!]! & m) !== m) return false;
      }
    }

    // Check inhibitor mask
    const inhIdx = this.inhibitorSingleWordIndex[tid]!;
    if (inhIdx === SPARSE_EMPTY) {
      return true; // No inhibitors
    } else if (inhIdx >= 0) {
      return (snapshot[inhIdx]! & this.inhibitorSingleWordMask[tid]!) === 0;
    } else {
      const indices = this.inhibitorSparseIndices[tid]!;
      const masks = this.inhibitorSparseMasks[tid]!;
      for (let i = 0; i < indices.length; i++) {
        if ((snapshot[indices[i]!]! & masks[i]!) !== 0) return false;
      }
      return true;
    }
  }
}

// ==================== Compilation Helpers ====================

function compileSparse(
  mask: Uint32Array,
  wordCount: number,
  singleWordIndex: Int8Array,
  singleWordMask: Uint32Array,
  sparseIndices: number[][],
  sparseMasks: number[][],
  tid: number,
): void {
  let nonZeroCount = 0;
  let lastNonZeroWord = -1;

  for (let w = 0; w < wordCount; w++) {
    if (mask[w] !== 0) {
      nonZeroCount++;
      lastNonZeroWord = w;
    }
  }

  if (nonZeroCount === 0) {
    singleWordIndex[tid] = SPARSE_EMPTY;
    singleWordMask[tid] = 0;
    sparseIndices[tid] = [];
    sparseMasks[tid] = [];
  } else if (nonZeroCount === 1) {
    singleWordIndex[tid] = lastNonZeroWord;
    singleWordMask[tid] = mask[lastNonZeroWord]!;
    sparseIndices[tid] = [];
    sparseMasks[tid] = [];
  } else {
    singleWordIndex[tid] = SPARSE_MULTI;
    singleWordMask[tid] = 0;
    const idx: number[] = [];
    const msk: number[] = [];
    for (let w = 0; w < wordCount; w++) {
      if (mask[w] !== 0) {
        idx.push(w);
        msk.push(mask[w]!);
      }
    }
    sparseIndices[tid] = idx;
    sparseMasks[tid] = msk;
  }
}

function compileConsumeProgram(t: Transition, compiled: CompiledNet): number[] {
  const ops: number[] = [];

  for (const spec of t.inputSpecs) {
    const pid = compiled.placeId(spec.place);
    switch (spec.type) {
      case 'one':
        ops.push(CONSUME_ONE, pid);
        break;
      case 'exactly':
        ops.push(CONSUME_N, pid, spec.count);
        break;
      case 'all':
        ops.push(CONSUME_ALL, pid);
        break;
      case 'at-least':
        ops.push(CONSUME_ATLEAST, pid, spec.minimum);
        break;
    }
  }

  for (const arc of t.resets) {
    const pid = compiled.placeId(arc.place);
    ops.push(RESET, pid);
  }

  return ops;
}

function compileReadProgram(t: Transition, compiled: CompiledNet): number[] {
  const pids: number[] = [];
  for (const arc of t.reads) {
    pids.push(compiled.placeId(arc.place));
  }
  return pids;
}

function simpleOutputPlace(spec: Out, compiled: CompiledNet): number {
  if (spec.type === 'place') {
    return compiled.placeId(spec.place);
  }
  return -1; // complex
}
