/**
 * Unit tests of the conformance harness on inline nets: the loader builds every schema shape,
 * the reference firing rule yields the README's outcomes (clarification 5), and the conformance
 * check goes red on a wrong verdict or a trace that does not replay. No solver, never skipped.
 */
import { describe, expect, it } from 'vitest';
import { mkdtempSync, mkdirSync, readFileSync, readdirSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { place } from '../../../src/core/place.js';
import { buildNet, loadNet, parseNet, SchemaNotExpressible } from './loader.js';
import { readCorpus, runCorpus } from './corpus.js';
import { checkConformance, checkDefaultPassConformance, renderFinding, replay } from './reference.js';

/** Every input kind, inhibitor / read / reset arcs, xor / and / timeout / forward, no output. */
const KINDS = {
  id: 'kinds',
  places: ['a', 'b', 'c', 'd', 'e', 'g', 'r'],
  marking: { a: 2, b: 3, r: 1 },
  transitions: [
    {
      name: 't_ex',
      inputs: [{ place: 'a', kind: 'exactly', n: 2 }],
      reads: ['r'],
      output: { type: 'xor', children: [
        { type: 'place', place: 'c' },
        { type: 'timeout', afterMs: 50, child: { type: 'forward', from: 'a', to: 'd' } },
      ] },
      priority: 1,
    },
    {
      name: 't_all',
      inputs: [{ place: 'b', kind: 'all' }],
      inhibitors: ['c'],
      output: { type: 'and', children: [{ type: 'place', place: 'e' }, { type: 'place', place: 'g' }] },
    },
    { name: 't_al', inputs: [{ place: 'e', kind: 'atLeast', n: 1 }], resets: ['g'], output: null },
  ],
  properties: [
    { id: 'k0', type: 'place-bound', place: 'd', bound: 1 },
    { id: 'k1', type: 'place-bound', place: 'd', bound: 2 },
    { id: 'k7', type: 'terminates-at-sink', sinks: ['c'] },
  ],
};

/** A declared arc-less place `q`, an undeclared marked place `z`, all six property types. */
const SEQ = {
  id: 'seq',
  places: ['a', 'b', 'c', 'q'],
  marking: { a: 1, z: 1 },
  transitions: [
    { name: 't1', inputs: [{ place: 'a', kind: 'one' }], inhibitors: [], reads: [], resets: [],
      output: { type: 'place', place: 'b' }, priority: 0 },
    { name: 't2', inputs: [{ place: 'b', kind: 'one' }], output: { type: 'place', place: 'c' } },
  ],
  properties: [
    { id: 'p0', type: 'deadlock-free', sinks: ['c'] },
    { id: 'p1', type: 'deadlock-free', sinks: ['c', 'z'] },
    { id: 'p2', type: 'terminates-at-sink', sinks: ['c'] },
    { id: 'p4', type: 'place-bound', place: 'b', bound: 1 },
    { id: 'p6', type: 'mutual-exclusion', places: ['a', 'b'] },
    { id: 'p7', type: 'unreachable', places: ['c', 'z'] },
    { id: 'p10', type: 'quiescent-count', places: ['c'], min: 2 },
  ],
};

describe('conformance loader', () => {
  it('loads every input kind, arc kind and the output tree', () => {
    const loaded = loadNet(KINDS);
    const byName = new Map([...loaded.net.transitions].map(t => [t.name, t]));
    expect([...byName.keys()].sort()).toEqual(['t_al', 't_all', 't_ex']);
    expect(byName.get('t_ex')!.inputSpecs.map(i => i.type)).toEqual(['exactly']);
    expect(byName.get('t_all')!.inputSpecs.map(i => i.type)).toEqual(['all']);
    expect(byName.get('t_al')!.inputSpecs.map(i => i.type)).toEqual(['at-least']);
    expect(byName.get('t_ex')!.reads.map(a => a.place.name)).toEqual(['r']);
    expect(byName.get('t_ex')!.priority).toBe(1);
    expect(byName.get('t_all')!.inhibitors.map(a => a.place.name)).toEqual(['c']);
    expect(byName.get('t_al')!.resets.map(a => a.place.name)).toEqual(['g']);
    expect(byName.get('t_al')!.outputSpec).toBeNull();
    expect(byName.get('t_ex')!.outputSpec?.type).toBe('xor');
  });

  it('keeps an undeclared marked place in the marking only, and declares arc-less places', () => {
    const loaded = loadNet(SEQ);
    expect(loaded.initialMarking.tokens(place('z'))).toBe(1);
    const names = [...loaded.net.places].map(p => p.name);
    expect(names).toContain('q');
    expect(names).not.toContain('z');
    expect(new Set(loaded.properties.map(p => p.spec.type))).toEqual(new Set([
      'deadlock-free', 'terminates-at-sink', 'place-bound', 'mutual-exclusion', 'unreachable', 'quiescent-count',
    ]));
    const qc = loaded.properties.find(p => p.spec.id === 'p10')!.property;
    expect(qc.type === 'quiescent-count' && qc.max).toBe(Infinity);
    expect(loaded.properties.find(p => p.spec.id === 'p0')!.sinks.map(p => p.name)).toEqual(['c']);
  });

  it('rejects what the schema does not allow or TypeScript cannot express', () => {
    expect(() => parseNet({ ...SEQ, transitions: [{ name: 't', inputs: [{ place: 'a', kind: 'some' }] }] }))
      .toThrow(/unknown input kind/);
    expect(() => parseNet({ ...SEQ, transitions: [{ name: 't', output: { type: 'or' } }] }))
      .toThrow(/unknown output type/);
    expect(() => parseNet({ ...SEQ, properties: [{ id: 'x', type: 'liveness' }] })).toThrow(/unknown property type/);
    const two = parseNet({ ...SEQ, properties: [{ id: 'x', type: 'mutual-exclusion', places: ['a'] }] });
    expect(() => buildNet(two)).toThrow(SchemaNotExpressible);
  });

  it('skips a mutual exclusion over three places, which the two-place API cannot state (clarification 1)', () => {
    const three = buildNet(parseNet({
      ...SEQ,
      properties: [
        { id: 'x', type: 'mutual-exclusion', places: ['a', 'b', 'c'] },
        { id: 'y', type: 'mutual-exclusion', places: ['a', 'b'] },
      ],
    }));
    expect(three.skipped.map(p => p.id)).toEqual(['x']);
    expect(three.properties.map(p => p.spec.id)).toEqual(['y']);
  });
});

describe('reference outcomes (README clarification 5)', () => {
  const kinds = parseNet(KINDS);
  const [k0, k1] = kinds.properties;

  it('a timeout forward of an exactly(2) input deposits two tokens (IO-014)', () => {
    expect(replay(kinds, k0!, ['t_ex'])).toBeNull();
    expect(replay(kinds, k0!, ['t_ex_b2'])).toBeNull();
    expect(replay(kinds, k1!, ['t_ex'])).toMatch(/do not violate/);
  });

  it('a completing action writes a forward target with one token (IO-015, IO-016)', () => {
    const net = parseNet({
      id: 'completion-forward',
      places: ['p0', 'p1'],
      marking: { p1: 3, s0: 1 },
      transitions: [{
        name: 't2',
        inputs: [{ place: 'p1', kind: 'exactly', n: 3 }],
        inhibitors: ['p0'],
        output: { type: 'timeout', afterMs: 50, child: { type: 'forward', from: 'p1', to: 'p1' } },
      }],
      properties: [{ id: 'd', type: 'deadlock-free', sinks: ['p0', 's0'] }],
    });
    // Completion leaves {p1:1, s0:1}: quiescent (p1 < 3) with p1 stranded. The timeout outcome
    // {p1:3, s0:1} is not quiescent.
    expect(replay(net, net.properties[0]!, ['t2'])).toBeNull();
  });

  it('an empty trace replays iff the initial marking violates', () => {
    const seq = parseNet(SEQ);
    const p7 = seq.properties.find(p => p.id === 'p7')!;
    const p4 = seq.properties.find(p => p.id === 'p4')!;
    expect(replay(seq, p7, ['t1', 't2'])).toBeNull();
    expect(replay(seq, p7, [])).toMatch(/do not violate/);
    expect(replay(seq, { ...p4, id: 'z0', type: 'place-bound', place: 'z', bound: 0 }, [])).toBeNull();
  });
});

describe('the conformance check goes red', () => {
  const kinds = parseNet(KINDS);
  const [k0, k1] = kinds.properties;

  it('flags a proven verdict the reference violates', () => {
    const f = checkConformance(kinds, k0!, 'fake', { verdict: 'proven', trace: [], traced: false },
      { property: 'k0', verdict: 'violated', trace: ['t_ex'] });
    expect(f.map(x => x.kind)).toEqual(['WRONG PROVEN']);
  });

  it('flags a violated trace that does not replay', () => {
    const f = checkConformance(kinds, k0!, 'fake', { verdict: 'violated', trace: ['t_al'], traced: true }, undefined);
    expect(f.map(x => x.kind)).toEqual(['REPLAY FAILS']);
    expect(renderFinding(f[0]!)).toMatch(/not enabled/);
  });

  it('flags a violated verdict the reference proves, and says when the trace falsifies it', () => {
    const wrong = checkConformance(kinds, k1!, 'fake', { verdict: 'violated', trace: ['t_ex'], traced: true },
      { property: 'k1', verdict: 'proven' });
    expect(wrong.map(x => x.kind)).toEqual(['WRONG VIOLATED']);
    const falsifies = checkConformance(kinds, k0!, 'fake', { verdict: 'violated', trace: ['t_ex'], traced: true },
      { property: 'k0', verdict: 'proven' });
    expect(falsifies.map(x => x.kind)).toEqual(['FALSIFIES REFERENCE']);
    expect(renderFinding(falsifies[0]!)).toMatch(/falsifies the reference/);
  });

  it('fails an untraced violation (rule 3, clarification 6), and against a proof (rule 2)', () => {
    const untraced = { verdict: 'violated', trace: [], traced: false } as const;
    expect(checkConformance(kinds, k0!, 'fake', untraced, { property: 'k0', verdict: 'violated' }).map(x => x.kind))
      .toEqual(['UNTRACED VIOLATED']);
    expect(checkConformance(kinds, k0!, 'fake', untraced, undefined).map(x => x.kind))
      .toEqual(['UNTRACED VIOLATED']);
    expect(checkConformance(kinds, k1!, 'fake', untraced, { property: 'k1', verdict: 'proven' }).map(x => x.kind))
      .toEqual(['WRONG VIOLATED']);
  });

  it('allows unknown against any reference verdict', () => {
    for (const verdict of ['proven', 'violated', 'unknown'] as const) {
      expect(checkConformance(kinds, k0!, 'fake', { verdict: 'unknown', trace: [], traced: false, reason: 'x' },
        { property: 'k0', verdict })).toEqual([]);
    }
  });
});

describe('the corpus runner', () => {
  it('skips cleanly on a missing corpus', () => {
    expect(readCorpus(join(tmpdir(), 'libpetri-conformance-does-not-exist')).skipReason).toMatch(/no corpus nets/);
    expect(readCorpus(null).skipReason).toMatch(/not found/);
  });

  it('reports stale expected files and dumps traced violations flat, enumeration only', async () => {
    const dir = mkdtempSync(join(tmpdir(), 'libpetri-conformance-'));
    try {
      mkdirSync(join(dir, 'nets'));
      mkdirSync(join(dir, 'expected'));
      writeFileSync(join(dir, 'nets', 'kinds.json'), JSON.stringify(KINDS));
      writeFileSync(join(dir, 'nets', 'seq.json'), JSON.stringify(SEQ));
      writeFileSync(join(dir, 'expected', 'kinds.json'), JSON.stringify({
        id: 'kinds', reference: 'inline', classes: 9, complete: true,
        results: [
          { property: 'k0', verdict: 'violated', trace: ['t_ex'] },
          { property: 'k1', verdict: 'proven' },
          { property: 'k7', verdict: 'violated', trace: ['t_ex', 't_all', 't_al'] },
        ],
      }));
      const corpus = readCorpus(dir);
      expect(corpus.entries.map(e => e.id)).toEqual(['kinds']);
      expect(corpus.missingExpected).toEqual(['seq']);
      const dump = join(dir, 'dump');
      const report = await runCorpus(corpus, { z3: false, dumpDir: dump });
      expect(report.skippedConfigs).toEqual(['smt+lb', 'smt-lb', 'ic3', 'smt+lb/split', 'smt-lb/split', 'ic3/split']);
      expect(report.findings.map(renderFinding)).toEqual([]);
      expect(report.stats.get('enum')).toMatchObject({ proven: 1, violated: 2, unknown: 0, untraced: 0 });
      // The default pass runs the same setup with the split on.
      expect(report.stats.has('enum/split')).toBe(true);
      expect(readdirSync(dump)).toEqual(['kinds.traces.json']);
      expect(JSON.parse(readFileSync(join(dump, 'kinds.traces.json'), 'utf8')).map((d: { property: string }) => d.property))
        .toEqual(['k0', 'k7']);
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  }, 60_000);
});

describe('the default pass (VER-004 split on) keeps rules 1, 3 and 4', () => {
  const kinds = parseNet(KINDS);
  const [k0, k1] = kinds.properties;

  it('still flags a proven verdict the reference violates (rule 1)', () => {
    const f = checkDefaultPassConformance(kinds, k0!, 'fake/split', { verdict: 'proven', trace: [], traced: false },
      { property: 'k0', verdict: 'violated', trace: ['t_ex'] });
    expect(f.map(x => x.kind)).toEqual(['WRONG PROVEN']);
  });

  it('allows a violated verdict the reference proves (rule 2 skipped)', () => {
    const f = checkDefaultPassConformance(kinds, k0!, 'fake/split', { verdict: 'violated', trace: ['t_ex'], traced: true },
      { property: 'k0', verdict: 'proven' });
    expect(f).toEqual([]);
  });

  it('still fails an untraced violation, and replays a trace of an unsplit net (rules 3, 4)', () => {
    const untraced = { verdict: 'violated', trace: [], traced: false } as const;
    expect(checkDefaultPassConformance(kinds, k1!, 'fake/split', untraced, { property: 'k1', verdict: 'proven' })
      .map(x => x.kind)).toEqual(['UNTRACED VIOLATED']);
    expect(checkDefaultPassConformance(kinds, k0!, 'fake/split', { verdict: 'violated', trace: ['t_al'], traced: true },
      undefined).map(x => x.kind)).toEqual(['REPLAY FAILS']);
  });

  it('does not replay a trace of a split net, whose completion steps the reference lacks', () => {
    const f = checkDefaultPassConformance(kinds, k0!, 'fake/split',
      { verdict: 'violated', trace: ['t_ex', 'complete:t_ex'], traced: true, split: true }, undefined);
    expect(f).toEqual([]);
  });
});
