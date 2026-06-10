import { describe, it, expect } from 'vitest';
import { selectMatchName, IncrementalMatcher } from '../../src/runtime/match-engine.js';
import type { NameStat } from '../../src/runtime/match-engine.js';
import { nameId } from '../../src/core/name.js';
import type { NameId } from '../../src/core/name.js';

/** Tiny deterministic 32-bit LCG (no Math.random — keeps the test reproducible). */
class Lcg {
  constructor(private s: number) {}
  next(): number {
    this.s = (Math.imul(this.s, 1664525) + 1013904223) >>> 0;
    return this.s;
  }
}

/** Reference pick: build the per-input index from the ground truth, defer to selectMatchName. */
function referenceSelect(truth: ReadonlyArray<ReadonlyArray<[NameId, number]>>, requireds: number[]): NameId | null {
  const perPlace = truth.map((toks) => {
    const idx = new Map<NameId, NameStat>();
    for (const [n, ts] of toks) {
      const prev = idx.get(n);
      if (prev) {
        prev.count++;
        if (ts < prev.minCreatedAt) prev.minCreatedAt = ts;
      } else {
        idx.set(n, { count: 1, minCreatedAt: ts });
      }
    }
    return idx;
  });
  return selectMatchName(perPlace, requireds);
}

describe('IncrementalMatcher', () => {
  // Differential test: for random add/consume sequences (2-3 inputs, required
  // 1-2, multiple tokens per name → partial consume + rep_ts advance + ties),
  // best() must equal selectMatchName at every step. Timestamps are random and
  // non-monotonic; the ground truth removes in INSERTION order (FIFO-within-name,
  // like the executor) — exercising the FIFO-vs-oldest distinction a plain
  // min-heap would get wrong.
  it('matches selectMatchName byte-for-byte over random add/consume sequences', () => {
    const names = [nameId('A'), nameId('B'), nameId('C'), nameId('D')];
    for (let seed = 0; seed < 400; seed++) {
      const rng = new Lcg(((seed * 2654435761) ^ 0xdeadbeef) >>> 0);
      const k = 2 + (rng.next() % 2);
      const requireds = Array.from({ length: k }, () => 1 + (rng.next() % 2));
      const m = new IncrementalMatcher(requireds);
      const truth: Array<Array<[NameId, number]>> = Array.from({ length: k }, () => []);

      for (let step = 0; step < 80; step++) {
        if (rng.next() % 3 < 2) {
          const i = rng.next() % k;
          const name = names[rng.next() % names.length]!;
          const ts = rng.next() % 40; // collisions + out-of-order on purpose
          m.add(i, name, ts);
          truth[i]!.push([name, ts]);
        } else {
          const pick = referenceSelect(truth, requireds);
          if (pick !== null) {
            expect(m.best(), `before consume (seed=${seed})`).toBe(pick);
            m.consume(pick);
            for (let i = 0; i < k; i++) {
              let removed = 0;
              truth[i] = truth[i]!.filter(([n]) => {
                if (removed < requireds[i]! && n === pick) {
                  removed++;
                  return false;
                }
                return true;
              });
            }
          }
        }
        expect(m.best(), `after op (seed=${seed})`).toBe(referenceSelect(truth, requireds));
      }
    }
  });
});
