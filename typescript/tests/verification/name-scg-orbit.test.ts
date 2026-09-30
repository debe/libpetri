import { describe, it, expect } from 'vitest';
import { NameStateClassGraph } from '../../src/verification/analysis/name-state-class-graph.js';
import { classify, type FragmentMode } from '../../src/verification/analysis/name-fragment.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { FIG_11B_ROWS, FIG_11C_ROWS, FIG_12A_ROWS, FIG_13B_ROWS, pnidNet } from '../fixtures/pnid-nets.js';
import { allMints } from '../fixtures/all-mints.js';

/**
 * [VER-012] implementation note: a join (or coloured consume) emits one successor per distinct
 * symbol signature, not one per enabling symbol. Symbols with equal signatures are swapped by a
 * transposition that fixes the name marking, so the class set and every class's (label, target)
 * set are unchanged — only parallel identical edges disappear. Emitting per symbol cost a copy and
 * a canonical key per live name per class: ~O(N² log N) on an unbounded-mint net.
 */

interface Case {
  readonly rows: Parameters<typeof pnidNet>[1];
  readonly marking: ReadonlyArray<readonly [string, number]>;
  readonly mode: FragmentMode;
  readonly carriers: readonly string[];
  readonly cap: number;
  /** Measured with per-symbol emission (before orbit dedup): classes and distinct edges. */
  readonly classes: number;
  readonly distinctEdges: number;
  readonly complete: boolean;
}

const CASES: Record<string, Case> = {
  'Fig. 11(b), truncated': {
    rows: FIG_11B_ROWS, marking: [['clerk', 2]], mode: 'base', carriers: [], cap: 3000,
    classes: 3000, distinctEdges: 5836, complete: false,
  },
  'Fig. 11(c)': {
    rows: FIG_11C_ROWS, marking: [['clerk', 3]], mode: 'base', carriers: [], cap: 100_000,
    classes: 4, distinctEdges: 6, complete: true,
  },
  'Fig. 13(b) EXTENDED, truncated': {
    rows: FIG_13B_ROWS, marking: [['R', 2]], mode: 'extended', carriers: ['P1'], cap: 3000,
    classes: 3000, distinctEdges: 5841, complete: false,
  },
  'Fig. 13(b) BASE': {
    rows: FIG_13B_ROWS, marking: [['R', 2]], mode: 'base', carriers: [], cap: 3000,
    classes: 6, distinctEdges: 6, complete: true,
  },
  'Fig. 12(a) EXTENDED': {
    rows: FIG_12A_ROWS, marking: [['SUPPLY', 3]], mode: 'extended', carriers: ['P1', 'B1', 'B2'], cap: 100_000,
    classes: 84, distinctEdges: 196, complete: true,
  },
};

function build(c: Case): NameStateClassGraph {
  const { net, places } = pnidNet('orbit', c.rows);
  const m = MarkingState.builder();
  for (const [n, k] of c.marking) m.tokens(places.get(n)!, k);
  const fragment = classify(net, c.mode, new Set(c.carriers), allMints(net));
  expect(fragment).not.toBeNull();
  return NameStateClassGraph.build(net, m.build(), fragment!, c.cap);
}

describe('Route B orbit dedup of join/consume successors (VER-012)', () => {
  for (const [name, c] of Object.entries(CASES)) {
    it(`${name}: same classes, same distinct edges, no parallel duplicates`, () => {
      const g = build(c);
      expect(g.isComplete()).toBe(c.complete);
      expect(g.classCount()).toBe(c.classes);
      const distinct = new Set(g.edges.map(e => `${e.from}>${e.to}:${e.transitionName}`));
      expect(distinct.size).toBe(c.distinctEdges);
      expect(g.edges.length).toBe(distinct.size);
    });
  }

  it('an 8 000-class Fig. 11(b) graph builds well within a generous bound', () => {
    // Per-symbol emission took ~14.5 s here (quadratic); with orbit dedup ~0.5 s.
    const t0 = performance.now();
    const g = build({ ...CASES['Fig. 11(b), truncated']!, cap: 8000 });
    const elapsed = performance.now() - t0;
    expect(g.classCount()).toBe(8000);
    expect(elapsed).toBeLessThan(6000);
  }, 60_000);
});
