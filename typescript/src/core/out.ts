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

/** The message of the `And` arity check (IO-011 AC1). */
const AND_ARITY = 'AND requires at least 1 child';

/** The message of the `Xor` arity check (IO-012 AC1). */
const XOR_ARITY = 'XOR requires at least 2 children';

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
    throw new Error(AND_ARITY);
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
    throw new Error(XOR_ARITY);
  }
  return { type: 'xor', children };
}

/**
 * The factory message for the first node of `out`, in pre-order with children left to right,
 * that {@link and} or {@link xor} would reject: an `And` without children (IO-011 AC1) or an
 * `Xor` with fewer than two (IO-012 AC1). A spec written as an object literal skips the
 * factories, so the transition build runs this again. `null` when every node passes.
 */
export function arityViolation(out: Out): string | null {
  switch (out.type) {
    case 'and':
      return out.children.length === 0 ? AND_ARITY : firstArityViolation(out.children);
    case 'xor':
      return out.children.length < 2 ? XOR_ARITY : firstArityViolation(out.children);
    case 'timeout':
      return arityViolation(out.child);
    case 'place':
    case 'forward-input':
      return null;
  }
}

function firstArityViolation(children: readonly Out[]): string | null {
  for (const child of children) {
    const found = arityViolation(child);
    if (found !== null) return found;
  }
  return null;
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

/**
 * Collects all leaf places from this output spec (flattened), one per name: places are
 * identified by name (CORE-002), so two `place('A')` objects are one place and the first
 * one met is kept.
 */
export function allPlaces(out: Out): Set<Place<any>> {
  const result = new Map<string, Place<any>>();
  collectPlaces(out, result);
  return new Set(result.values());
}

function collectPlaces(out: Out, result: Map<string, Place<any>>): void {
  switch (out.type) {
    case 'place':
      if (!result.has(out.place.name)) result.set(out.place.name, out.place);
      break;
    case 'forward-input':
      if (!result.has(out.to.name)) result.set(out.to.name, out.to);
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

/** Two leaves of one output branch that name the same place, as {@link duplicateInBranch} finds them. */
export interface BranchDuplicate {
  /** The place name, after `nameOf`. */
  readonly name: string;
  /** The two leaf places, as the spec names them (before `nameOf`). */
  readonly first: Place<any>;
  readonly second: Place<any>;
}

/**
 * The place the walk of [IO-011] ("Which place the message names") reports: a place some output
 * branch names twice, or `null` when no branch does. `And(Xor(A, B), Xor(B, A))` reports `B`.
 * `nameOf` maps a leaf place to the place it stands for
 * (identity by default; composition passes its port-to-host binding).
 *
 * Linear in the spec: an AND's children combine by cross product, so a place any branch of
 * one child names and any branch of a sibling names is named twice by some branch.
 */
export function duplicateInBranch(
  out: Out,
  nameOf: (p: Place<any>) => string = p => p.name,
): BranchDuplicate | null {
  return findDuplicate(out, nameOf).dup;
}

function findDuplicate(
  out: Out,
  nameOf: (p: Place<any>) => string,
): { dup: BranchDuplicate | null; leaves: Map<string, Place<any>> } {
  switch (out.type) {
    case 'place':
      return { dup: null, leaves: new Map([[nameOf(out.place), out.place]]) };
    case 'forward-input':
      return { dup: null, leaves: new Map([[nameOf(out.to), out.to]]) };
    case 'timeout':
      return findDuplicate(out.child, nameOf);
    case 'xor':
    case 'and': {
      const leaves = new Map<string, Place<any>>();
      for (const child of out.children) {
        const found = findDuplicate(child, nameOf);
        if (found.dup !== null) return found;
        for (const [name, p] of found.leaves) {
          const prior = leaves.get(name);
          if (prior !== undefined && out.type === 'and') return { dup: { name, first: prior, second: p }, leaves };
          if (prior === undefined) leaves.set(name, p);
        }
      }
      return { dup: null, leaves };
    }
  }
}

/** The [IO-011] rejection of a place named twice in one AND branch. */
export function duplicateOutputPlaceMessage(transitionName: string, placeName: string): string {
  return `output spec of transition '${transitionName}' names place '${placeName}' twice in one AND branch; ` +
    'outputs are sets (IO-015) — a weighted output is not supported, add a second place or a follow-up transition';
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
      // One place per name in a branch (CORE-002): the first object met is kept.
      const names = new Set<string>();
      for (const p of setA) names.add(p.name);
      const merged = new Set<Place<any>>(setA);
      for (const p of setB) {
        if (!names.has(p.name)) {
          names.add(p.name);
          merged.add(p);
        }
      }
      result.push(merged);
    }
  }
  return result;
}

/** The number of `Timeout` nodes in the spec, nested ones and siblings alike ([IO-013]). */
export function countTimeouts(out: Out): number {
  switch (out.type) {
    case 'place':
    case 'forward-input':
      return 0;
    case 'timeout':
      return 1 + countTimeouts(out.child);
    case 'and':
    case 'xor': {
      let n = 0;
      for (const child of out.children) n += countTimeouts(child);
      return n;
    }
  }
}

/** The [IO-013] rejection of an output spec with more than one `Timeout` node. */
export function timeoutCountMessage(transitionName: string, count: number): string {
  return `output spec of transition '${transitionName}' has ${count} Timeout nodes; ` +
    'an output spec has at most one, nested or not (IO-013)';
}

/**
 * Whether the child of a `Timeout` node in the spec holds an `Xor` node at any depth ([IO-013]).
 * The executor, not the action, makes the timeout deposit, so nothing could choose an alternative.
 */
export function hasXorInTimeoutChild(out: Out): boolean {
  switch (out.type) {
    case 'place':
    case 'forward-input':
      return false;
    case 'timeout':
      return containsXor(out.child);
    case 'and':
    case 'xor':
      return out.children.some(hasXorInTimeoutChild);
  }
}

function containsXor(out: Out): boolean {
  switch (out.type) {
    case 'place':
    case 'forward-input':
      return false;
    case 'xor':
      return true;
    case 'timeout':
      return containsXor(out.child);
    case 'and':
      return out.children.some(containsXor);
  }
}

/** The [IO-013] rejection of an `Xor` node inside the child of the `Timeout` node. */
export function xorInTimeoutMessage(transitionName: string): string {
  return `output spec of transition '${transitionName}' has a Xor node inside the child of its Timeout node; ` +
    'the timeout outcome deposits one fixed set of places (IO-013)';
}

/**
 * The first `ForwardInput` in pre-order (children left to right) that is not inside the child
 * of a `Timeout` node, or `null` ([IO-014]). A `Timeout`'s subtree is not searched: every
 * forward there deposits on the timeout outcome.
 */
export function bareForwardInput(out: Out): OutForwardInput | null {
  switch (out.type) {
    case 'forward-input':
      return out;
    case 'place':
    case 'timeout':
      return null;
    case 'and':
    case 'xor':
      for (const child of out.children) {
        const found = bareForwardInput(child);
        if (found !== null) return found;
      }
      return null;
  }
}

/** The [IO-014] rejection of a `ForwardInput` outside the child of a `Timeout` node. */
export function bareForwardInputMessage(transitionName: string, fi: OutForwardInput): string {
  return `output spec of transition '${transitionName}' uses ForwardInput('${fi.from.name}', '${fi.to.name}') ` +
    'outside the child of a Timeout node; a forward deposits only on the timeout outcome (IO-014)';
}

/** Two output branches that claim the same set of places, as {@link ambiguousBranches} finds them. */
export interface AmbiguousBranches {
  /** The earlier branch index ([IO-016] numbering). */
  readonly i: bigint;
  /** The first branch index whose set an earlier branch already claims. */
  readonly j: bigint;
  /** The place names of branch `i`, in the order the spec names them (leaves left to right). */
  readonly places: readonly string[];
}

/**
 * The [IO-012] ambiguity check: the first branch `j` (in [IO-016] enumeration order) whose set
 * of places equals the set of an earlier branch, the smallest such earlier branch `i`, and the
 * places of `i`, or `null` when every branch claims a different set.
 *
 * Reports what enumerating the branches and comparing them in index order would report, without
 * enumerating them: an `And` of 64 two-way `Xor`s has 2^64 branches. It relies on the [IO-011]
 * check having passed, so the children of an `And` name disjoint places and two branches of an
 * `And` claim the same set exactly when they claim the same set in every child.
 *
 * - An `And` collides first in its LAST child that collides at all, with every other child on its
 *   branch 0: a tuple whose first nonzero component sits at an earlier child is larger, and before
 *   that child's first collision every branch of it is the first of its set.
 * - An `Xor` collides first in its first child holding a branch that either collides inside the
 *   child or claims a set an earlier child claims. Only the latter needs a search, which runs over
 *   the child's branches whose places all lie in the earlier children's places, and stops at the
 *   child's own first collision.
 *
 * An `And` of `Xor`s is therefore checked in time linear in its size. The `Xor` search is
 * exponential only when two alternatives have exponentially many branches inside each other's
 * places without ever claiming the same set.
 *
 * Indices are `bigint` because the branch count is a product.
 */
export function ambiguousBranches(out: Out): AmbiguousBranches | null {
  const a = new BranchAnalysis();
  const j = a.firstCollision(out);
  if (j === null) return null;
  const set = new Set(a.decode(out, j));
  const i = a.firstIndexOf(out, set)!;
  return { i, j, places: a.decode(out, i) };
}

/** The [IO-012] rejection of two output branches that claim the same set of places. */
export function ambiguousOutputMessage(transitionName: string, amb: AmbiguousBranches): string {
  return `output spec of transition '${transitionName}' is ambiguous: output branches ${amb.i} and ${amb.j} ` +
    `both claim {${amb.places.join(', ')}}; no write can tell them apart (IO-012)`;
}

/** Memoised structural facts about output-spec nodes, keyed by node object. */
class BranchAnalysis {
  private readonly counts = new Map<Out, bigint>();
  private readonly universes = new Map<Out, Set<string>>();
  private readonly collisions = new Map<Out, bigint | null>();

  /** The number of branches of `out` ([IO-016]). */
  count(out: Out): bigint {
    let n = this.counts.get(out);
    if (n !== undefined) return n;
    switch (out.type) {
      case 'place':
      case 'forward-input': n = 1n; break;
      case 'timeout': n = this.count(out.child); break;
      case 'xor': n = 0n; for (const c of out.children) n += this.count(c); break;
      case 'and': n = 1n; for (const c of out.children) n *= this.count(c); break;
    }
    this.counts.set(out, n);
    return n;
  }

  /** Every place name any branch of `out` claims. */
  universe(out: Out): Set<string> {
    let u = this.universes.get(out);
    if (u !== undefined) return u;
    switch (out.type) {
      case 'place': u = new Set([out.place.name]); break;
      case 'forward-input': u = new Set([out.to.name]); break;
      case 'timeout': u = this.universe(out.child); break;
      case 'xor':
      case 'and':
        u = new Set();
        for (const c of out.children) for (const p of this.universe(c)) u.add(p);
        break;
    }
    this.universes.set(out, u);
    return u;
  }

  /** The place names of branch `index` of `out`, leaves left to right. */
  decode(out: Out, index: bigint): string[] {
    switch (out.type) {
      case 'place': return [out.place.name];
      case 'forward-input': return [out.to.name];
      case 'timeout': return this.decode(out.child, index);
      case 'xor': {
        let rest = index;
        for (const c of out.children) {
          const n = this.count(c);
          if (rest < n) return this.decode(c, rest);
          rest -= n;
        }
        throw new Error('branch index out of range');
      }
      case 'and': {
        const parts: string[][] = [];
        let rest = index;
        for (let k = out.children.length - 1; k >= 0; k--) {
          const c = out.children[k]!;
          const n = this.count(c);
          parts.push(this.decode(c, rest % n));
          rest /= n;
        }
        return parts.reverse().flat();
      }
    }
  }

  /** The smallest index of a branch of `out` whose set is `set`, or `null` when none is. */
  firstIndexOf(out: Out, set: ReadonlySet<string>): bigint | null {
    switch (out.type) {
      case 'place': return set.size === 1 && set.has(out.place.name) ? 0n : null;
      case 'forward-input': return set.size === 1 && set.has(out.to.name) ? 0n : null;
      case 'timeout': return this.firstIndexOf(out.child, set);
      case 'xor': {
        let offset = 0n;
        for (const c of out.children) {
          const idx = this.firstIndexOf(c, set);
          if (idx !== null) return offset + idx;
          offset += this.count(c);
        }
        return null;
      }
      case 'and': {
        // The children name disjoint places, so the set splits into one part per child.
        const parts = out.children.map(() => new Set<string>());
        for (const p of set) {
          const k = out.children.findIndex(c => this.universe(c).has(p));
          if (k < 0) return null;
          parts[k]!.add(p);
        }
        let index = 0n;
        for (let k = 0; k < out.children.length; k++) {
          const c = out.children[k]!;
          const idx = this.firstIndexOf(c, parts[k]!);
          if (idx === null) return null;
          index = index * this.count(c) + idx;
        }
        return index;
      }
    }
  }

  /** The first branch of `out` whose set an earlier branch of `out` also claims, or `null`. */
  firstCollision(out: Out): bigint | null {
    if (this.collisions.has(out)) return this.collisions.get(out)!;
    let j: bigint | null = null;
    switch (out.type) {
      case 'place':
      case 'forward-input':
        break;
      case 'timeout':
        j = this.firstCollision(out.child);
        break;
      case 'and': {
        let stride = 1n;
        for (let k = out.children.length - 1; k >= 0; k--) {
          const c = out.children[k]!;
          const jc = this.firstCollision(c);
          if (jc !== null) { j = jc * stride; break; }
          stride *= this.count(c);
        }
        break;
      }
      case 'xor': {
        let offset = 0n;
        for (let k = 0; k < out.children.length && j === null; k++) {
          const c = out.children[k]!;
          const own = this.firstCollision(c);
          const cross = this.firstClaimedEarlier(out.children.slice(0, k), c, own);
          const local = cross !== null && (own === null || cross <= own) ? cross : own;
          if (local !== null) j = offset + local;
          offset += this.count(c);
        }
        break;
      }
    }
    this.collisions.set(out, j);
    return j;
  }

  /**
   * The smallest index, at most `bound` when one is given, of a branch of `child` whose set some
   * node of `earlier` also claims, or `null`.
   */
  private firstClaimedEarlier(earlier: readonly Out[], child: Out, bound: bigint | null): bigint | null {
    const mine = this.universe(child);
    // An empty `And` claims no place, so two alternatives that can both claim nothing are rivals
    // even when they name no common place.
    const empty = this.canBeEmpty(child);
    const rivals = earlier.filter(e =>
      [...this.universe(e)].some(p => mine.has(p)) || (empty && this.canBeEmpty(e)));
    if (rivals.length === 0) return null;
    const within = new Set<string>();
    for (const r of rivals) for (const p of this.universe(r)) within.add(p);
    for (const [index, places] of this.branchesWithin(child, within)) {
      if (bound !== null && index > bound) return null;
      const set = new Set(places);
      if (rivals.some(r => this.firstIndexOf(r, set) !== null)) return index;
    }
    return null;
  }

  /** The branches of `out` in index order whose places all lie in `within`, with their indices. */
  private *branchesWithin(out: Out, within: ReadonlySet<string>): Generator<[bigint, string[]]> {
    switch (out.type) {
      case 'place':
        if (within.has(out.place.name)) yield [0n, [out.place.name]];
        return;
      case 'forward-input':
        if (within.has(out.to.name)) yield [0n, [out.to.name]];
        return;
      case 'timeout':
        yield* this.branchesWithin(out.child, within);
        return;
      case 'xor': {
        let offset = 0n;
        for (const c of out.children) {
          for (const [idx, places] of this.branchesWithin(c, within)) yield [offset + idx, places];
          offset += this.count(c);
        }
        return;
      }
      case 'and': {
        if (!out.children.every(c => this.canStayWithin(c, within))) return;
        yield* this.productWithin(out.children, 0, within);
        return;
      }
    }
  }

  private *productWithin(children: readonly Out[], k: number, within: ReadonlySet<string>): Generator<[bigint, string[]]> {
    if (k === children.length) {
      yield [0n, []];
      return;
    }
    let stride = 1n;
    for (let l = k + 1; l < children.length; l++) stride *= this.count(children[l]!);
    for (const [a, head] of this.branchesWithin(children[k]!, within)) {
      for (const [b, tail] of this.productWithin(children, k + 1, within)) {
        yield [a * stride + b, head.concat(tail)];
      }
    }
  }

  /** Whether some branch of `out` claims no place (an `And` with no children). */
  private canBeEmpty(out: Out): boolean {
    switch (out.type) {
      case 'place':
      case 'forward-input': return false;
      case 'timeout': return this.canBeEmpty(out.child);
      case 'xor': return out.children.some(c => this.canBeEmpty(c));
      case 'and': return out.children.every(c => this.canBeEmpty(c));
    }
  }

  /** Whether some branch of `out` names only places in `within`. */
  private canStayWithin(out: Out, within: ReadonlySet<string>): boolean {
    switch (out.type) {
      case 'place': return within.has(out.place.name);
      case 'forward-input': return within.has(out.to.name);
      case 'timeout': return this.canStayWithin(out.child, within);
      case 'xor': return out.children.some(c => this.canStayWithin(c, within));
      case 'and': return out.children.every(c => this.canStayWithin(c, within));
    }
  }
}
