import type { Place } from './place.js';

/**
 * Output specification with explicit split semantics.
 * Supports composite structures (XOR of ANDs, AND of XORs, etc.)
 *
 * - And: ALL children must receive tokens
 * - Xor: EXACTLY ONE child receives token
 * - Place: Leaf node representing a single output place
 * - Timeout: Timeout branch that activates if action exceeds duration
 * - ForwardInput: Forward consumed input to output on timeout
 *
 * A spec names **places, not counts**. Validation ([IO-015]) compares the SET of
 * places an action wrote against the branches' claims, so an action that deposits
 * several tokens into one named place is accepted — and every analysis that
 * enumerates branches ({@link enumerateBranches}: the state-class graph, the SMT
 * encoding, the ν fragment check) models exactly one token per named place. Such a
 * firing therefore does more than the analyses explore, in the direction that can
 * make a `proven` false. The executors report it once per transition as a `WARN`
 * log-message ([IO-016]); a net meant to be verified should produce one token per
 * named place and express multiplicity in its topology.
 */
export type Out = OutAnd | OutXor | OutPlace | OutTimeout | OutForwardInput;

export interface OutAnd {
  readonly type: 'and';
  readonly children: readonly Out[];
}

export interface OutXor {
  readonly type: 'xor';
  readonly children: readonly Out[];
}

export interface OutPlace {
  readonly type: 'place';
  readonly place: Place<any>;
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
 * and(outPlace(always), xorPlaces(left, right))
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
  return and(...places.map(outPlace));
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
  return xor(...places.map(outPlace));
}

/** Leaf output spec for a single place. */
export function outPlace(p: Place<any>): OutPlace {
  return { type: 'place', place: p };
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
  return timeout(afterMs, outPlace(p));
}

/** Forward consumed input value to output place on timeout. */
export function forwardInput(from: Place<any>, to: Place<any>): OutForwardInput {
  return { type: 'forward-input', from, to };
}

// ==================== Helper Functions ====================

/** Collects all leaf places from this output spec (flattened). */
export function allPlaces(out: Out): Set<Place<any>> {
  const result = new Set<Place<any>>();
  collectPlaces(out, result);
  return result;
}

function collectPlaces(out: Out, result: Set<Place<any>>): void {
  switch (out.type) {
    case 'place':
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
 * Enumerates all possible output branches for structural analysis ([IO-016]).
 *
 * - AND = single branch containing all child places (Cartesian product)
 * - XOR = one branch per alternative child
 * - Nested = Cartesian product for AND, union for XOR
 *
 * A branch is a **set** of places: it says which places receive a token, not how
 * many tokens each receives. Analyses built on it (the state-class graph's virtual
 * transitions, the flattener's post vectors, the ν fragment check) deposit one token
 * per place of the chosen branch. An action that writes `n > 1` tokens to a place
 * its branch names once is accepted by [IO-015] but is outside what those analyses
 * explore — a sound under-approximation for safety only when it never happens, which
 * is why the executors warn about it ([IO-016] AC4).
 */
export function enumerateBranches(out: Out): ReadonlyArray<ReadonlySet<Place<any>>> {
  switch (out.type) {
    case 'place':
      return [new Set([out.place])];

    case 'forward-input':
      return [new Set<Place<any>>([out.to])];

    case 'and': {
      let result: Set<Place<any>>[] = [new Set()];
      for (const child of out.children) {
        result = crossProduct(result, enumerateBranches(child) as Set<Place<any>>[]);
      }
      return result;
    }

    case 'xor': {
      const result: Set<Place<any>>[] = [];
      for (const child of out.children) {
        result.push(...(enumerateBranches(child) as Set<Place<any>>[]));
      }
      return result;
    }

    case 'timeout':
      return enumerateBranches(out.child);
  }
}

function crossProduct(
  a: Set<Place<any>>[],
  b: ReadonlyArray<ReadonlySet<Place<any>>>,
): Set<Place<any>>[] {
  const result: Set<Place<any>>[] = [];
  for (const setA of a) {
    for (const setB of b) {
      const merged = new Set<Place<any>>(setA);
      for (const p of setB) merged.add(p);
      result.push(merged);
    }
  }
  return result;
}
