import type { Place } from './place.js';

/**
 * Output specification with explicit split semantics.
 * Supports composite structures (XOR of ANDs, AND of XORs, etc.)
 *
 * - And: ALL children must receive tokens
 * - Xor: EXACTLY ONE child receives token
 * - One: Leaf node — produce 1 token to a single output place (mirrors `In.One`)
 * - Exactly: Leaf node — produce N tokens to a single output place (mirrors `In.Exactly`,
 *   verification-only metadata; runtime production is determined by the action)
 * - Timeout: Timeout branch that activates if action exceeds duration
 * - ForwardInput: Forward consumed input to output on timeout
 */
export type Out = OutAnd | OutXor | OutOne | OutExactly | OutTimeout | OutForwardInput;

export interface OutAnd {
  readonly type: 'and';
  readonly children: readonly Out[];
}

export interface OutXor {
  readonly type: 'xor';
  readonly children: readonly Out[];
}

export interface OutOne {
  readonly type: 'one';
  readonly place: Place<any>;
}

export interface OutExactly {
  readonly type: 'exactly';
  readonly place: Place<any>;
  /** Number of tokens >= 1, used by formal analyzers (SCG, SMT). */
  readonly count: number;
}

export interface OutTimeout {
  readonly type: 'timeout';
  /** Timeout duration in milliseconds. */
  readonly afterMs: number;
  readonly child: Out;
}

export interface OutForwardInput {
  readonly type: 'forward-input';
  readonly from: Place<any>;
  readonly to: Place<any>;
}

// ==================== Factory Functions ====================

/**
 * AND-split: all children must receive tokens.
 *
 * @example
 * ```ts
 * // AND of XOR branches: one of (A,B) AND one of (C,D)
 * and(xorPlaces(placeA, placeB), xorPlaces(placeC, placeD))
 *
 * // AND with a fixed place + XOR branch
 * and(one(always), xorPlaces(left, right))
 * ```
 */
export function and(...children: Out[]): OutAnd {
  if (children.length === 0) {
    throw new Error('AND requires at least 1 child');
  }
  return { type: 'and', children };
}

/** AND-split from places: all places must receive tokens. */
export function andPlaces(...places: Place<any>[]): OutAnd {
  return and(...places.map(outOne));
}

/** XOR-split: exactly one child receives token. */
export function xor(...children: Out[]): OutXor {
  if (children.length < 2) {
    throw new Error('XOR requires at least 2 children');
  }
  return { type: 'xor', children };
}

/** XOR-split from places: exactly one place receives token. */
export function xorPlaces(...places: Place<any>[]): OutXor {
  return xor(...places.map(outOne));
}

/**
 * Leaf output spec for a single place — produce 1 token. Mirrors `In.one`.
 * Prefixed with `out` to disambiguate from the `In.one` factory.
 */
export function outOne(p: Place<any>): OutOne {
  if (p == null) {
    throw new Error('One place cannot be null');
  }
  return { type: 'one', place: p };
}

/**
 * Leaf output spec for a single place producing exactly N tokens.
 * Mirrors `In.exactly`. Multiplicity is verification-only metadata; the runtime
 * validator treats `Exactly(p, n)` identically to `One(p)`.
 */
export function outExactly(count: number, p: Place<any>): OutExactly {
  if (p == null) {
    throw new Error('Exactly place cannot be null');
  }
  if (!Number.isInteger(count) || count < 1) {
    throw new Error(`count must be an integer >= 1, got: ${count}`);
  }
  return { type: 'exactly', place: p, count };
}

/** Timeout output: activates if action exceeds duration. */
export function timeout(afterMs: number, child: Out): OutTimeout {
  if (afterMs <= 0) {
    throw new Error(`Timeout must be positive: ${afterMs}`);
  }
  return { type: 'timeout', afterMs, child };
}

/** Timeout output pointing to a single place. */
export function timeoutPlace(afterMs: number, p: Place<any>): OutTimeout {
  return timeout(afterMs, outOne(p));
}

/** Forward consumed input value to output place on timeout. */
export function forwardInput(from: Place<any>, to: Place<any>): OutForwardInput {
  return { type: 'forward-input', from, to };
}

// ==================== Helper Functions ====================

/** Collects all leaf places from this output spec (flattened, no multiplicity). */
export function allPlaces(out: Out): Set<Place<any>> {
  const result = new Set<Place<any>>();
  collectPlaces(out, result);
  return result;
}

function collectPlaces(out: Out, result: Set<Place<any>>): void {
  switch (out.type) {
    case 'one':
      result.add(out.place);
      break;
    case 'exactly':
      result.add(out.place);
      break;
    case 'forward-input':
      result.add(out.to);
      break;
    case 'and':
    case 'xor':
      for (const child of out.children) {
        collectPlaces(child, result);
      }
      break;
    case 'timeout':
      collectPlaces(out.child, result);
      break;
  }
}

/**
 * Enumerates all possible output branches for structural analysis.
 *
 * Each branch is a multiset (place → integer count):
 * - One(P) contributes {P → 1}
 * - Exactly(P, N) contributes {P → N}
 * - ForwardInput(_, to) contributes {to → 1}
 * - AND = Cartesian product of children's branches; on key collision, counts SUM
 * - XOR = list-concatenation of children's branches (one per alternative)
 * - Timeout = delegates to child
 */
export function enumerateBranches(out: Out): ReadonlyArray<ReadonlyMap<Place<any>, number>> {
  switch (out.type) {
    case 'one':
      return [new Map([[out.place, 1]])];

    case 'exactly':
      return [new Map([[out.place, out.count]])];

    case 'forward-input':
      return [new Map<Place<any>, number>([[out.to, 1]])];

    case 'and': {
      let result: Map<Place<any>, number>[] = [new Map()];
      for (const child of out.children) {
        result = crossProduct(result, enumerateBranches(child));
      }
      return result;
    }

    case 'xor': {
      const result: Map<Place<any>, number>[] = [];
      for (const child of out.children) {
        for (const branch of enumerateBranches(child)) {
          // Copy to a mutable Map (callers may mutate; ReadonlyMap forbids).
          result.push(new Map(branch));
        }
      }
      return result;
    }

    case 'timeout':
      return enumerateBranches(out.child);
  }
}

function crossProduct(
  a: Map<Place<any>, number>[],
  b: ReadonlyArray<ReadonlyMap<Place<any>, number>>,
): Map<Place<any>, number>[] {
  const result: Map<Place<any>, number>[] = [];
  for (const mapA of a) {
    for (const mapB of b) {
      const merged = new Map<Place<any>, number>(mapA);
      for (const [place, count] of mapB) {
        merged.set(place, (merged.get(place) ?? 0) + count);
      }
      result.push(merged);
    }
  }
  return result;
}
