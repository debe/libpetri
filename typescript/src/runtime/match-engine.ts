/**
 * @module match-engine
 *
 * ν-net binding selection — the canonical name-correlation algorithm shared by
 * both executor backends (spec NU-020).
 *
 * A transition carrying a {@link import('../core/match-spec.js').MatchSpec} is
 * enabled only when there is a single name present in every correlated input
 * with its required token count. The two executors differ only in how they read
 * tokens (`Marking` FIFO queues vs the precompiled per-place arrays); the
 * *selection* — which name satisfies the join, and the deterministic tie-break —
 * lives here so it is identical across backends and matches the Rust/Java ports.
 */
import type { Token } from '../core/token.js';
import type { Place } from '../core/place.js';
import type { Transition } from '../core/transition.js';
import type { NameId } from '../core/name.js';
import type { KeyFn } from '../core/match-spec.js';

/** Per-correlated-input statistic for one name: count + oldest timestamp (ms). */
export interface NameStat {
  count: number;
  minCreatedAt: number;
}

/**
 * Selects the satisfying correlation name across all correlated inputs, or
 * `null` when no single name is present in every input with at least its
 * required count.
 *
 * Determinism (NU-020): among satisfying names, pick the one whose oldest
 * matched token (minimum `createdAt` across the correlated inputs) is earliest;
 * break remaining ties by {@link NameId} order. Byte-identical to the Rust
 * `select_match_name` and the Java `selectMatchName`.
 *
 * The `NameId` tie-break uses JS string `<` (UTF-16 code-unit order). This is
 * byte-identical to the Java (`String.compareTo`) and Rust (UTF-8 code-point)
 * ports for ASCII/BMP names — which covers every executor-minted name
 * (`"{transition}#{n}"`). For supplementary-plane code points in user-supplied
 * correlation keys, Rust's UTF-8 order can differ from this UTF-16 order; NU-001
 * requires only per-implementation consistency, which holds.
 */
export function selectMatchName(
  perPlace: ReadonlyArray<Map<NameId, NameStat>>,
  requireds: readonly number[],
): NameId | null {
  if (perPlace.length === 0) return null;
  // Seed candidate names from the smallest index; result is seed-independent.
  let seed = 0;
  for (let i = 1; i < perPlace.length; i++) {
    if (perPlace[i]!.size < perPlace[seed]!.size) seed = i;
  }

  let bestName: NameId | null = null;
  let bestTs = 0;
  for (const [name, stat] of perPlace[seed]!) {
    if (stat.count < requireds[seed]!) continue;
    let repTs = Number.MAX_SAFE_INTEGER;
    let satisfied = true;
    for (let j = 0; j < perPlace.length; j++) {
      const s = perPlace[j]!.get(name);
      if (s === undefined || s.count < requireds[j]!) {
        satisfied = false;
        break;
      }
      repTs = Math.min(repTs, s.minCreatedAt);
    }
    if (!satisfied) continue;
    const take = bestName === null || repTs < bestTs || (repTs === bestTs && name < bestName);
    if (take) {
      bestName = name;
      bestTs = repTs;
    }
  }
  return bestName;
}

/**
 * Builds a `name → {count, minCreatedAt}` index over the given tokens. When a
 * `guard` (the correlated input's unary filter) is given, tokens failing it are
 * excluded BEFORE indexing — the filter applies first and name correlation runs
 * only over the survivors, so a token failing the filter is never selected even
 * if its name matches (NU-021). Matches the Rust/Java ports, which guard-filter
 * before building the name index.
 */
export function buildNameIndex(
  tokens: readonly Token<any>[],
  key: KeyFn,
  guard?: (value: any) => boolean,
): Map<NameId, NameStat> {
  const index = new Map<NameId, NameStat>();
  for (const token of tokens) {
    if (guard && !guard(token.value)) continue;
    const name = key(token.value);
    if (name === undefined || name === null) continue;
    const ts = token.createdAt;
    const prev = index.get(name);
    if (prev) {
      prev.count++;
      if (ts < prev.minCreatedAt) prev.minCreatedAt = ts;
    } else {
      index.set(name, { count: 1, minCreatedAt: ts });
    }
  }
  return index;
}

/**
 * Required token count for `placeName` from the transition's input spec
 * (1 for one/all, n for exactly(n), m for at-least(m)).
 */
export function requiredFor(t: Transition, placeName: string): number {
  for (const inSpec of t.inputSpecs) {
    if (inSpec.place.name === placeName) {
      if (inSpec.type === 'exactly') return inSpec.count;
      if (inSpec.type === 'at-least') return inSpec.minimum;
      return 1;
    }
  }
  return 1;
}

/**
 * Finds the correlation name satisfying `t`'s `MatchSpec`, or `null` if the join
 * is not enabled (NU-020). `getTokens` abstracts the token source so both
 * executors share this code (Marking queues vs precompiled per-place arrays).
 */
export function findBinding(
  t: Transition,
  getTokens: (place: Place<any>) => readonly Token<any>[],
): NameId | null {
  const ms = t.matchSpec;
  if (!ms) return null;
  const perPlace: Map<NameId, NameStat>[] = [];
  const requireds: number[] = [];
  for (const k of ms.keys) {
    // NU-021: apply the input's guard before indexing names, so a token failing
    // the filter is excluded from both the count and the name-presence/tie-break.
    perPlace.push(buildNameIndex(getTokens(k.place), k.key, guardFor(t, k.place.name)));
    requireds.push(requiredFor(t, k.place.name));
  }
  return selectMatchName(perPlace, requireds);
}

/** The unary guard on `t`'s input arc for `placeName`, if any (NU-021). */
function guardFor(t: Transition, placeName: string): ((value: any) => boolean) | undefined {
  for (const inSpec of t.inputSpecs) {
    if (inSpec.place.name === placeName) return inSpec.guard;
  }
  return undefined;
}

// ==================== Incremental matcher (NU-020 performance) ====================
//
// `selectMatchName` rebuilds a full name index over every token on each call, so
// draining N ready correlation groups costs O(N²). `IncrementalMatcher` maintains
// the per-input name index (a FIFO min-queue of timestamps per name) plus a
// lazy-deletion min-heap of ready names ordered by the same `(oldest_ts, name)`
// key, so `add`/`consume` are O(log n) and `best()` is an O(1) read. Used only
// for `one`/`exactly` correlated inputs that are consumed by no other transition
// (so the cache can't desync); otherwise the executor falls back to
// `selectMatchName`. Ported byte-identically from the Rust `IncrementalMatcher`.

/**
 * FIFO queue of timestamps with O(1)-amortized min-query (two-stack method).
 * Mirrors the executor's FIFO-within-name removal (`popFront` drops the
 * earliest-inserted token) while answering "oldest remaining timestamp". A plain
 * min-heap would diverge from FIFO order when timestamps are not insertion-ordered.
 */
class MinQueue {
  private readonly inStack: number[] = [];
  private readonly inMin: number[] = [];
  private readonly outStack: number[] = [];
  private readonly outMin: number[] = [];

  get size(): number {
    return this.inStack.length + this.outStack.length;
  }

  pushBack(v: number): void {
    this.inStack.push(v);
    const top = this.inMin.length;
    this.inMin.push(top ? Math.min(this.inMin[top - 1]!, v) : v);
  }

  popFront(): void {
    if (this.outStack.length === 0) {
      while (this.inStack.length) {
        const v = this.inStack.pop()!;
        this.inMin.pop();
        this.outStack.push(v);
        const top = this.outMin.length;
        this.outMin.push(top ? Math.min(this.outMin[top - 1]!, v) : v);
      }
    }
    this.outStack.pop();
    this.outMin.pop();
  }

  min(): number {
    const a = this.inMin.length ? this.inMin[this.inMin.length - 1]! : Infinity;
    const b = this.outMin.length ? this.outMin[this.outMin.length - 1]! : Infinity;
    return a < b ? a : b;
  }
}

interface ReadyEntry {
  ts: number;
  name: NameId;
}

/** Binary min-heap of ready names keyed by `(ts, name)` — the `select_match_name` order. */
class ReadyHeap {
  private readonly a: ReadyEntry[] = [];

  get size(): number {
    return this.a.length;
  }

  peek(): ReadyEntry | undefined {
    return this.a[0];
  }

  private less(x: ReadyEntry, y: ReadyEntry): boolean {
    return x.ts < y.ts || (x.ts === y.ts && x.name < y.name);
  }

  push(e: ReadyEntry): void {
    const a = this.a;
    a.push(e);
    let i = a.length - 1;
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (this.less(a[i]!, a[p]!)) {
        const tmp = a[i]!;
        a[i] = a[p]!;
        a[p] = tmp;
        i = p;
      } else break;
    }
  }

  pop(): void {
    const a = this.a;
    const last = a.pop()!;
    if (a.length === 0) return;
    a[0] = last;
    let i = 0;
    const n = a.length;
    for (;;) {
      const l = 2 * i + 1;
      const r = 2 * i + 2;
      let m = i;
      if (l < n && this.less(a[l]!, a[m]!)) m = l;
      if (r < n && this.less(a[r]!, a[m]!)) m = r;
      if (m === i) break;
      const tmp = a[i]!;
      a[i] = a[m]!;
      a[m] = tmp;
      i = m;
    }
  }
}

/**
 * Incremental equivalent of {@link selectMatchName} for `one`/`exactly`
 * correlated inputs (fixed consume count). {@link best} is an O(1) read and, for
 * any sequence of `add`/`consume`, returns exactly the name `selectMatchName`
 * would — verified by `incremental-matcher.test.ts`.
 *
 * While ready names are pushed in non-decreasing `(rep_ts, name)` order — the
 * canonical fork/join (siblings carry the fork's monotonic timestamp) or any
 * time-ordered seed — a plain FIFO (index-based deque, never `shift()`) is a
 * valid min-PQ, so `add`/`consume` are amortized O(1). The first out-of-order
 * push migrates the deque into the lazy-deletion {@link ReadyHeap} (`heaped`),
 * thereafter O(log n) — the proven fallback. The fast path is re-entered whenever
 * the structure fully empties.
 */
export class IncrementalMatcher {
  private readonly ts: Array<Map<NameId, MinQueue>>;
  /** Monotonic fast path: ascending `(rep_ts, name)`; `fifo[fifoHead]` (after
   * `cleanTop`) is the min. Active while `!heaped`. Advance `fifoHead` instead of
   * `shift()` (O(1)); reset when the head catches the length. */
  private readonly fifo: ReadyEntry[] = [];
  private fifoHead = 0;
  /** Largest entry appended to `fifo` in the current monotonic run. */
  private maxPushed: ReadyEntry | null = null;
  /** Once an out-of-order push migrates `fifo` into `heap`. */
  private heaped = false;
  private readonly heap = new ReadyHeap();
  private readonly ready = new Map<NameId, number>();

  constructor(private readonly requireds: readonly number[]) {
    this.ts = requireds.map(() => new Map<NameId, MinQueue>());
  }

  /** Add one (already guard-passing) token carrying `name` at `createdAt` to input `i`. */
  add(i: number, name: NameId, createdAt: number): void {
    let q = this.ts[i]!.get(name);
    if (!q) {
      q = new MinQueue();
      this.ts[i]!.set(name, q);
    }
    q.pushBack(createdAt);
    this.refresh(name);
    this.cleanTop();
  }

  /** Remove the `required` earliest-inserted tokens of `name` from every input (NU-020). */
  consume(name: NameId): void {
    for (let i = 0; i < this.requireds.length; i++) {
      const q = this.ts[i]!.get(name);
      if (q) {
        for (let r = 0; r < this.requireds[i]!; r++) q.popFront();
        if (q.size === 0) this.ts[i]!.delete(name);
      }
    }
    this.refresh(name);
    this.cleanTop();
  }

  /** The name `selectMatchName` would pick, or `null`. O(1) read. */
  best(): NameId | null {
    if (this.heaped) {
      const top = this.heap.peek();
      return top ? top.name : null;
    }
    return this.fifoHead < this.fifo.length ? this.fifo[this.fifoHead]!.name : null;
  }

  /**
   * Route a ready name's `(rep, name)` to the active structure: append to the
   * FIFO in O(1) while pushes stay non-decreasing; on the first inversion,
   * migrate the FIFO into the heap and stay heap-backed.
   */
  private pushReady(rep: number, name: NameId): void {
    const entry: ReadyEntry = { ts: rep, name };
    if (this.heaped) {
      this.heap.push(entry);
      return;
    }
    const max = this.maxPushed;
    const monotonic = max === null || rep > max.ts || (rep === max.ts && name >= max.name);
    if (monotonic) {
      this.maxPushed = entry;
      this.fifo.push(entry);
    } else {
      this.heaped = true;
      for (let i = this.fifoHead; i < this.fifo.length; i++) this.heap.push(this.fifo[i]!);
      this.fifo.length = 0;
      this.fifoHead = 0;
      this.heap.push(entry);
    }
  }

  private repTs(name: NameId): number | null {
    let rep = Infinity;
    for (let i = 0; i < this.requireds.length; i++) {
      const q = this.ts[i]!.get(name);
      if (!q || q.size < this.requireds[i]!) return null;
      const m = q.min();
      if (m < rep) rep = m;
    }
    return rep;
  }

  private refresh(name: NameId): void {
    const rep = this.repTs(name);
    if (rep !== null) {
      if (this.ready.get(name) !== rep) {
        this.ready.set(name, rep);
        this.pushReady(rep, name);
      }
    } else {
      this.ready.delete(name);
    }
  }

  private cleanTop(): void {
    if (this.heaped) {
      for (;;) {
        const top = this.heap.peek();
        if (top && this.ready.get(top.name) !== top.ts) this.heap.pop();
        else break;
      }
      if (this.heap.size === 0) {
        this.heaped = false;
        this.maxPushed = null;
      }
    } else {
      while (this.fifoHead < this.fifo.length) {
        const top = this.fifo[this.fifoHead]!;
        if (this.ready.get(top.name) !== top.ts) this.fifoHead++;
        else break;
      }
      if (this.fifoHead >= this.fifo.length) {
        // fully drained: reset the backing array + start a fresh monotonic run
        this.fifo.length = 0;
        this.fifoHead = 0;
        this.maxPushed = null;
      }
    }
  }

  /** Test-only: has the matcher fallen back from the FIFO fast path to the heap? */
  isHeaped(): boolean {
    return this.heaped;
  }
}
