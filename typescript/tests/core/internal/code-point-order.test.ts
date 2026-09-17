import { describe, it, expect } from 'vitest';
import { compareCodePoints } from '../../../src/core/internal/code-point-order.js';

/**
 * The cross-language acceptance vector for name order ([VER-013], [VER-022]), already in
 * code-point order. The Rust and Java suites assert the same sequence.
 */
const CANONICAL: readonly string[] = [
  '',
  'Z',
  'a',
  'ab',
  '\u00C4', // Ä
  '\u4E2D', // 中
  '\uE000', // private use, the lowest unit above the surrogates
  '\uFF21', // fullwidth Ａ
  '\u{1D400}', // mathematical bold A, a surrogate pair
  '\u{1F600}', // grinning face, a surrogate pair
];

/** Lexicographic order on the code point sequences: the definition, not the fast path. */
function reference(a: string, b: string): number {
  const x = Array.from(a, c => c.codePointAt(0)!);
  const y = Array.from(b, c => c.codePointAt(0)!);
  for (let i = 0; i < Math.min(x.length, y.length); i++) {
    if (x[i] !== y[i]) return x[i]! - y[i]!;
  }
  return x.length - y.length;
}

describe('compareCodePoints', () => {
  it('sorts the cross-language vector into code-point order from any starting order', () => {
    const starts = [
      [...CANONICAL].reverse(),
      [...CANONICAL].sort(), // code-unit order
      [CANONICAL[8]!, CANONICAL[3]!, CANONICAL[6]!, CANONICAL[0]!, CANONICAL[9]!,
        CANONICAL[5]!, CANONICAL[1]!, CANONICAL[7]!, CANONICAL[2]!, CANONICAL[4]!],
    ];
    for (const start of starts) {
      expect(start.sort(compareCodePoints)).toEqual(CANONICAL);
    }
  });

  it('differs from the code-unit order of < and the default sort', () => {
    // As units the supplementary characters' lead surrogates (0xD835, 0xD83D) sit below
    // 0xE000; as code points they sit above U+FFFF. A comparator that forgot the fix-up
    // would pass the ASCII half of the vector and fail here.
    const units = [...CANONICAL].sort();
    expect(units.indexOf('\u{1D400}')).toBeLessThan(units.indexOf('\uE000'));
    expect(compareCodePoints('\u{1D400}', '\uE000')).toBeGreaterThan(0);
    expect(compareCodePoints('\u{1F600}', '\uFF21')).toBeGreaterThan(0);
    expect(compareCodePoints('\uFFFF', '\u{10000}')).toBeLessThan(0);
  });

  it('ignores the host locale', () => {
    expect(compareCodePoints('Zeit', 'apfel')).toBeLessThan(0);
    expect(compareCodePoints('Ia', 'ia')).toBeLessThan(0);
    expect(compareCodePoints('aa', 'b')).toBeLessThan(0);
    expect(compareCodePoints('z', '\u00C4rger')).toBeLessThan(0);
    // Canonically equivalent but different code points: never equal.
    expect(compareCodePoints('\u00C4', 'A\u0308')).toBeGreaterThan(0);
  });

  it('sorts a prefix first and is zero only on equal strings', () => {
    expect(compareCodePoints('', '')).toBe(0);
    expect(compareCodePoints('ab', 'ab')).toBe(0);
    expect(compareCodePoints('a', 'ab')).toBeLessThan(0);
    expect(compareCodePoints('ab', 'a')).toBeGreaterThan(0);
    expect(compareCodePoints('\u{1F600}', '\u{1F600}x')).toBeLessThan(0);
  });

  it('agrees in sign with the code-point definition on every pair of mixed-plane names', () => {
    // The prefixes send the same pairs down both paths: unless both strings hold a unit at
    // 0xD800 or above the engine's comparison decides, and the shared U+1F600 sends every
    // pair to the unit loop. The long prefix puts the deciding pair far from the start.
    const pieces = ['', 'a', 'Z', '\u00C4', '\uD7FF', '\uE000', '\uFFFF', '\u{10000}', '\u{1D400}', '\u{10FFFF}'];
    for (const prefix of ['', 'orderService.fulfilment.', '\u{1F600}.shared.']) {
      const names: string[] = [];
      for (const x of pieces) for (const y of pieces) names.push(prefix + x + y);
      for (const a of names) {
        for (const b of names) {
          expect(Math.sign(compareCodePoints(a, b)), `${JSON.stringify(a)} vs ${JSON.stringify(b)}`)
            .toBe(Math.sign(reference(a, b)));
        }
      }
    }
  });
});
