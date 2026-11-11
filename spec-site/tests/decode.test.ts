import { describe, expect, it } from 'vitest';
import { arr, decode, DecodeError, int, lit, nullable, obj, str, tagged } from '../src/decode.js';
import { outputSpec, replayStep, siteData } from '../src/decode-site.js';
import { buildSiteData } from '../src/gen/site.js';

describe('decoders', () => {
  const point = obj({ x: int, label: nullable(str) });

  it('accepts exact objects', () => {
    expect(decode(point, { x: 1, label: null })).toEqual({ x: 1, label: null });
  });

  it('rejects missing and unknown keys with the JSON path', () => {
    expect(() => decode(arr(point), [{ x: 1 }])).toThrow(/\$\[0\]\.label: missing key/);
    expect(() => decode(point, { x: 1, label: 'a', extra: 1 })).toThrow(/\$\.extra: unknown key/);
    expect(() => decode(point, { x: 1.5, label: null })).toThrow(DecodeError);
  });

  it('dispatches tagged unions and rejects unknown tags', () => {
    const shape = tagged('kind', {
      a: obj({ kind: lit('a'), n: int }),
      b: obj({ kind: lit('b') }),
    });
    expect(decode(shape, { kind: 'b' })).toEqual({ kind: 'b' });
    expect(() => decode(shape, { kind: 'c' })).toThrow(/unknown tag/);
  });

  it('decodes recursive output specs and replay steps', () => {
    const spec = { type: 'xor', children: [{ type: 'place', place: 'a' }, { type: 'timeout', afterMs: 5, child: { type: 'forward', from: 'x', to: 'y' } }] };
    expect(decode(outputSpec, spec)).toEqual(spec);
    const blocked = {
      kind: 'blocked',
      index: 3,
      fire: 'take',
      branch: 0,
      timeout: false,
      reason: { kind: 'inhibitorMarked', place: 'lock', count: 1 },
      requirement: 'CORE-031',
      message: "'take' is not enabled: inhibitor place 'lock' holds 1 token",
    };
    expect(decode(replayStep, blocked)).toEqual(blocked);
  });

  it('round-trips assembled SiteData', () => {
    const data = buildSiteData({
      spec: { files: [], blocks: [] },
      glossary: [],
      lean: { blocks: [], citations: [] },
      coverage: {},
      defects: [],
      situations: [],
      diagrams: new Set(),
    });
    expect(decode(siteData, JSON.parse(JSON.stringify(data)))).toEqual(data);
  });
});
