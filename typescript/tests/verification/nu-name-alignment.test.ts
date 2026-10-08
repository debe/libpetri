import { describe, it, expect } from 'vitest';
import { readFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import type { SmtVerificationResult } from '../../src/verification/smt-verification-result.js';
import {
  deadlockFree, nameAligned, propertyDescription, quiescentCount, quiescentNameAligned, type SmtProperty,
} from '../../src/verification/smt-property.js';
import type { FragmentMode } from '../../src/verification/analysis/name-fragment.js';
import { classify, declaredMints } from '../../src/verification/analysis/name-fragment.js';
import { NameMarking } from '../../src/verification/analysis/name-marking.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { flatten } from '../../src/verification/encoding/net-flattener.js';
import { encodeNet } from '../../src/verification/z3/smt-encoder.js';
import { buildColouredPlan, encodeColoured } from '../../src/verification/z3/name-coloured-encoder.js';
import { solveSlotBound } from '../../src/verification/z3/slot-bound-lp.js';
import { encodeLinearBound, violationDemand } from '../../src/verification/z3/linear-bound.js';
import { encodeStateEquationQuery } from '../../src/verification/z3/state-equation-query.js';
import { runStateEquationPhase } from '../../src/verification/z3/state-equation-phase.js';
import { runFiringBoundPhase } from '../../src/verification/z3/bounded-run.js';
import { satisfiesBad, vectorize } from '../../src/verification/z3/abstract-replayer.js';
import { verifyViaStateClassGraph } from '../../src/verification/scg-verifier.js';
import { decideOverClasses, safetyViolation } from '../../src/verification/graph-decision.js';
import { alwaysAvailable, arrivals, bounded } from '../../src/verification/analysis/environment-analysis-mode.js';
import { BitmapNetExecutor } from '../../src/runtime/bitmap-net-executor.js';
import { PrecompiledNetExecutor } from '../../src/runtime/precompiled-net-executor.js';
import type { Marking } from '../../src/runtime/marking.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import type { TransitionContext } from '../../src/core/transition-context.js';
import { place, type Place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { andPlaces, outPlace } from '../../src/core/out.js';
import { matchKey, matchSpec, relayKey } from '../../src/core/match-spec.js';
import { nameId } from '../../src/core/name.js';
import { tokenOf, type Token } from '../../src/core/token.js';
import { deadline } from '../../src/core/timing.js';
import { pnidNet } from '../fixtures/pnid-nets.js';

/**
 * [NU-055] name alignment: the fixtures of spec/verification-fixtures/nu-aligned-fixtures.json
 * (AC1, AC2, AC3, AC6, AC7, AC8), the routes that must not decide it (AC4), the predicate's
 * invariance under name permutation and reordering and a run with a pinned minting scope (AC5),
 * and the construction rules and descriptions of the list `S` (AC7).
 */

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../../../spec/verification-fixtures');

/** A row of `nu-aligned-fixtures.json`: transition, inputs, outputs, match keys, relay targets. */
type AlignedRow = readonly [string, string[], string[], string[], string[]];

interface AlignedFixture {
  readonly id: string;
  readonly net: string;
  readonly route: 'B';
  readonly rows: readonly AlignedRow[];
  readonly marking: Readonly<Record<string, number>>;
  readonly property: {
    readonly type: 'name-aligned' | 'quiescent-name-aligned' | 'quiescent-count';
    readonly places: readonly string[];
    readonly min?: number;
    readonly max?: number;
  };
  readonly mintTransitions: readonly string[];
  readonly carrierPlaces: readonly string[];
  readonly fragmentMode: FragmentMode;
  readonly budgetPlaces?: readonly string[];
  readonly environmentPlaces?: readonly string[];
  readonly environmentMode?: 'always-available';
  readonly expected: 'proven' | 'violated' | 'unknown';
  readonly witnessLength?: number;
  readonly reasonContains?: string;
}

const fixtures: readonly AlignedFixture[] =
  JSON.parse(readFileSync(join(root, 'nu-aligned-fixtures.json'), 'utf8')).fixtures;

function fixtureById(id: string): AlignedFixture {
  const f = fixtures.find(x => x.id === id);
  if (f === undefined) throw new Error(`no fixture ${id}`);
  return f;
}

/** The fixture's net, its places by name, and a configured verifier. */
function fixtureVerifier(f: AlignedFixture): { verifier: SmtVerifier; p: (n: string) => Place<unknown>; net: PetriNet } {
  const rows = f.rows.map(([t, ins, outs, match, relay]) =>
    match.length > 0 ? [t, ins, outs, { match, relay }] as const : [t, ins, outs] as const);
  const { net, places } = pnidNet(f.net, rows);
  const p = (n: string) => {
    const x = places.get(n);
    if (x === undefined) throw new Error(`fixture ${f.id} references unknown place '${n}'`);
    return x;
  };
  const prop = f.property;
  const named = prop.places.map(p) as [Place<unknown>, ...Place<unknown>[]];
  const property: SmtProperty =
    prop.type === 'name-aligned' ? nameAligned(...named)
      : prop.type === 'quiescent-name-aligned' ? quiescentNameAligned(...named)
        : quiescentCount(named, prop.min!, prop.max!);
  const verifier = SmtVerifier.forNet(net)
    .initialMarking(m => { for (const [n, k] of Object.entries(f.marking)) m.tokens(p(n), k); })
    .property(property)
    .mintTransitions(...f.mintTransitions)
    .carrierPlaces(...f.carrierPlaces.map(p))
    .fragmentMode(f.fragmentMode)
    .timeout(30_000);
  if (f.budgetPlaces?.length) verifier.budgetPlaces(...f.budgetPlaces.map(p));
  if (f.environmentPlaces?.length) {
    verifier.environmentPlaces(...f.environmentPlaces.map(n => ({ place: p(n) })));
    if (f.environmentMode === 'always-available') verifier.environmentMode(alwaysAvailable());
  }
  return { verifier, p, net };
}

describe('NU-055 name-alignment fixtures (nu-aligned-fixtures.json)', () => {
  it('runs every fixture of the file, and every unknown one names what its reason must contain', () => {
    // One test per fixture below: the ids are distinct, so none shadows another.
    expect(fixtures.length).toBeGreaterThan(0);
    expect(new Set(fixtures.map(f => f.id)).size).toBe(fixtures.length);
    for (const f of fixtures) {
      if (f.expected === 'unknown') expect(f.reasonContains, f.id).toBeTruthy();
    }
  });

  for (const f of fixtures) {
    it(f.id, async () => {
      const result = await fixtureVerifier(f).verifier.verify();
      // Route attribution first: every fixture is decided (or refused) by Route B.
      expect(f.route).toBe('B');
      expect(result.route).toBe('nu-scg');
      expect(result.report).toContain('Route B');
      expect(result.verdict.type).toBe(f.expected);
      if (result.verdict.type === 'unknown') {
        // The refusal order of NU-055 picks what the reason names when several refusals apply.
        expect(result.verdict.reason).toContain(f.reasonContains!);
      }
      if (f.witnessLength !== undefined) {
        expect(result.counterexampleTransitions).toHaveLength(f.witnessLength);
        // NU-055 "Violated": a path of the graph, not of the flat abstract semantics.
        expect(result.counterexampleConfirmed).toBeNull();
      }
    });
  }
});

describe('NU-055 description and refusals', () => {
  const fixed = fixtureById('nu-aligned-search-quiescent-proven');

  it('describes both properties byte for byte, for one, two and three places', async () => {
    const box = place('box');
    const list = place('list');
    const staged = place('staged');
    expect(propertyDescription(nameAligned(box))).toBe('Name alignment of box');
    expect(propertyDescription(nameAligned(box, list))).toBe('Name alignment of box and list');
    expect(propertyDescription(nameAligned(box, staged, list))).toBe('Name alignment of box, staged and list');
    expect(propertyDescription(quiescentNameAligned(box))).toBe('Quiescent name alignment of box');
    expect(propertyDescription(quiescentNameAligned(box, list))).toBe('Quiescent name alignment of box and list');
    expect(propertyDescription(quiescentNameAligned(box, staged, list)))
      .toBe('Quiescent name alignment of box, staged and list');
    const result = await fixtureVerifier(fixed).verifier.verify();
    expect(result.report).toContain('Property: Quiescent name alignment of box and list');
  });

  it('AC2: a place absent from the net is unknown naming the place, never proven', async () => {
    const { verifier, p } = fixtureVerifier(fixed);
    const result = await verifier.property(quiescentNameAligned(p('box'), place('ghost'))).verify();
    expect(result.verdict.type).toBe('unknown');
    expect(result.verdict.type === 'unknown' && result.verdict.reason).toContain("'ghost'");
  });

  it('AC2: NameAligned on an uncoloured place is unknown naming the place', async () => {
    const { verifier, p } = fixtureVerifier(fixed);
    const result = await verifier.property(nameAligned(p('ready'), p('list'))).verify();
    expect(result.route).toBe('nu-scg');
    expect(result.verdict.type === 'unknown' && result.verdict.reason).toContain("'ready'");
  });

  it('AC3: under BASE a carrier is uncoloured and the reason names EXTENDED', async () => {
    // BASE colours the match keys alone; on a net inside the BASE fragment a carrier is
    // uncoloured, which the reason names together with the mode that colours it.
    const box = place<string>('box');
    const reply = place<string>('reply');
    const done = place<string>('done');
    const go = place<string>('go');
    const fn = (v: string) => nameId(v);
    const send = Transition.builder('send').inputs(one(go)).outputs(andPlaces(box, reply)).action(async () => {}).build();
    const join = Transition.builder('join')
      .inputs(one(box), one(reply))
      .match(matchSpec(matchKey(box, fn), matchKey(reply, fn)))
      .outputs(outPlace(done))
      .action(async () => {})
      .build();
    const net = PetriNet.builder('baseCarrier').transitions(send, join).build();
    const result = await SmtVerifier.forNet(net)
      .initialMarking(m => m.tokens(go, 1))
      .mintTransitions('send')
      .carrierPlaces(done)
      .property(nameAligned(box, done))
      .verify();
    expect(result.route).toBe('nu-scg');
    expect(result.verdict.type === 'unknown' && result.verdict.reason).toContain("'done'");
    expect(result.verdict.type === 'unknown' && result.verdict.reason).toContain('EXTENDED');
  });

  it('AC3: the BASE run names the ignored relay declarations in the report', async () => {
    const result = await fixtureVerifier(fixtureById('nu-aligned-search-base-unknown')).verifier.verify();
    expect(result.report).toContain("ν relay declarations ignored under BASE fragment mode (NU-054): 'apply' -> 'box', 'apply' -> 'staged'");
  });

  it('NU-051: outside the EXTENDED fragment the verdict is unknown and no other route is named', async () => {
    // A read arc on the coloured `box` puts the net outside every fragment.
    const f = fixed;
    const rows: Parameters<typeof pnidNet>[1] = [
      ...f.rows.map(([t, ins, outs, match, relay]) =>
        match.length > 0 ? [t, ins, outs, { match, relay }] as const : [t, ins, outs] as const),
      ['peek', ['idle'], ['idle'], { read: ['box'] }],
    ];
    const { net, places } = pnidNet('outside', rows);
    const p = (n: string) => places.get(n)!;
    const result = await SmtVerifier.forNet(net)
      .initialMarking(m => { for (const [n, k] of Object.entries(f.marking)) m.tokens(p(n), k); })
      .property(quiescentNameAligned(p('box'), p('list')))
      .mintTransitions(...f.mintTransitions)
      .carrierPlaces(...f.carrierPlaces.map(p))
      .fragmentMode('extended')
      .verify();
    expect(result.route).toBe('nu-scg');
    expect(result.verdict.type).toBe('unknown');
    const reason = result.verdict.type === 'unknown' ? result.verdict.reason : '';
    expect(reason).toContain('EXTENDED');
    expect(reason).not.toContain('over-approximation');
    expect(result.report).not.toContain('verified via sound over-approximation');
  });

  it('AC6: the bug variant with the coloured initial token is unknown naming the place', async () => {
    const f = fixtureById('nu-aligned-search-bug-quiescent-violated');
    const { verifier, p } = fixtureVerifier(f);
    const result = await verifier.initialMarking(m => {
      for (const [n, k] of Object.entries(f.marking)) m.tokens(p(n), k);
      m.tokens(p('reply'), 1);
    }).verify();
    expect(result.verdict.type === 'unknown' && result.verdict.reason).toContain("'reply'");
  });

  it('QuiescentNameAligned carries no sink clause: declared sinks do not weaken it', async () => {
    const f = fixtureById('nu-aligned-search-bug-quiescent-violated');
    const { verifier, p } = fixtureVerifier(f);
    const result = await verifier.sinkPlaces(p('box'), p('list')).verify();
    expect(result.route).toBe('nu-scg');
    expect(result.verdict.type).toBe('violated');
    expect(result.counterexampleTransitions).toHaveLength(12);
  });

  it('QuiescentNameAligned reads the reap-aware quiescence of VER-002 (TIME-013)', async () => {
    // `sendA` and `sendB` mint two names into `box` and `list`; `drop`, a deadline drain of
    // `list`, is all that realigns them. A late executor reaps it and rests misaligned.
    const a = place<string>('a');
    const b = place<string>('b');
    const box = place<string>('box');
    const list = place<string>('list');
    const done = place<string>('done');
    const mint = (name: string, from: Place<string>, to: Place<string>) =>
      Transition.builder(name).inputs(one(from)).outputs(outPlace(to)).action(async () => {}).build();
    const drop = Transition.builder('drop').inputs(one(list)).outputs(outPlace(done)).timing(deadline(10))
      .action(async () => {}).build();
    const net = PetriNet.builder('reapedAlignment').transitions(mint('sendA', a, box), mint('sendB', b, list), drop).build();
    const verifier = (noReaping: boolean) => SmtVerifier.forNet(net)
      .initialMarking(m => m.tokens(a, 1).tokens(b, 1))
      .mintTransitions('sendA', 'sendB')
      .carrierPlaces(box, list)
      .fragmentMode('extended')
      .assumeNoReaping(noReaping)
      .property(quiescentNameAligned(box, list));
    const late = await verifier(false).verify();
    expect(late.route).toBe('nu-scg');
    expect(late.verdict.type, late.report).toBe('violated');
    expect(late.counterexampleTransitions).toEqual(['sendA', 'sendB']);
    const onTime = await verifier(true).verify();
    expect(onTime.route).toBe('nu-scg');
    expect(onTime.verdict.type, onTime.report).toBe('proven');
  });

  it('Modelled injection: under arrivals(2) the keystrokes are closed into the net and Route B decides it', async () => {
    for (const [id, expected] of [
      ['nu-aligned-search-env-quiescent-unknown', 'proven'],
      ['nu-aligned-search-bug-env-quiescent-unknown', 'violated'],
    ] as const) {
      const result = await fixtureVerifier(fixtureById(id)).verifier.environmentMode(arrivals(2, 2)).verify();
      expect(result.route, id).toBe('nu-scg');
      expect(result.verdict.type, result.report).toBe(expected);
    }
  });

  it('AC6: QuiescentNameAligned under bounded(k) with an environment place names it and points to arrivals', async () => {
    const f = fixtureById('nu-aligned-search-env-quiescent-unknown');
    const result = await fixtureVerifier(f).verifier.environmentMode(bounded(2)).verify();
    expect(result.route).toBe('nu-scg');
    const reason = result.verdict.type === 'unknown' ? result.verdict.reason : '';
    expect(reason).toContain("'typed'");
    expect(reason).toContain('arrivals(k)');
  });

  it('AC8: an arrival into a coloured place is refused before a marked coloured place', async () => {
    // `e` is a carrier fed by arrivals(1) and `box` starts marked: step 3 of the refusal order
    // names `e`, ahead of step 7, which would name `box`.
    const e = place<string>('e');
    const box = place<string>('box');
    const fwd = Transition.builder('fwd').inputs(one(e)).outputs(outPlace(box)).action(async () => {}).build();
    const net = PetriNet.builder('arrivalBeforeMarked').transitions(fwd).build();
    const result = await SmtVerifier.forNet(net)
      .initialMarking(m => m.tokens(box, 1))
      .environmentPlaces({ place: e })
      .environmentMode(arrivals(1, 1))
      .carrierPlaces(e, box)
      .fragmentMode('extended')
      .property(quiescentNameAligned(box))
      .verify();
    expect(result.route).toBe('nu-scg');
    const reason = result.verdict.type === 'unknown' ? result.verdict.reason : '';
    expect(reason, result.report).toContain("environment place 'e'");
    expect(reason).toContain('arrivals(k)');
  });
});

describe('NU-055 AC7: S is a non-empty list of places', () => {
  const box = place('box');
  const list = place('list');

  it('a repeated place counts once, at its first occurrence, compared by name', () => {
    const again = place('box'); // another Place object with the same name
    for (const prop of [nameAligned(box, list, again, list), quiescentNameAligned(box, list, again, list)]) {
      expect(prop.places.map(p => p.name)).toEqual(['box', 'list']);
      expect(prop.places[0]).toBe(box);
    }
    expect(propertyDescription(nameAligned(list, box, list))).toBe('Name alignment of list and box');
    expect(propertyDescription(nameAligned(box, box))).toBe('Name alignment of box');
  });

  it('an empty S is rejected at construction', () => {
    // The type takes at least one place; a caller that gets past it (an empty spread) still throws.
    const none: Place<unknown>[] = [];
    expect(() => nameAligned(...(none as [Place<unknown>]))).toThrow('nameAligned needs at least one place');
    expect(() => quiescentNameAligned(...(none as [Place<unknown>])))
      .toThrow('quiescentNameAligned needs at least one place');
  });

  it('an empty S written as an object, past the factories, is rejected by the verifier', () => {
    const verifier = SmtVerifier.forNet(searchAsYouType(false).net);
    expect(() => verifier.property({ type: 'name-aligned', places: [] }))
      .toThrow('name-aligned needs at least one place');
    expect(() => verifier.property({ type: 'quiescent-name-aligned', places: [] }))
      .toThrow('quiescent-name-aligned needs at least one place');
  });

  it('the singleton says its place never holds two names', () => {
    const nm = new NameMarking();
    nm.add('reply', 0, 2);
    expect(nm.aligned(['reply'])).toBe(true);
    nm.add('reply', 1, 1);
    expect(nm.aligned(['reply'])).toBe(false);
  });

  it('one name across all: a place holding two names violates S whatever the others hold', () => {
    // The pairwise reading of two places (every name in p equals every name in q) accepts this
    // marking, since `list` is empty; the list reading counts self pairs and does not.
    const nm = new NameMarking();
    nm.add('box', 0, 1);
    nm.add('box', 1, 1);
    expect(nm.aligned(['box', 'list'])).toBe(false);
    expect(nm.aligned(['list'])).toBe(true);
    // Each place holding one name, but not the same one.
    const split = new NameMarking();
    split.add('box', 0, 1);
    split.add('staged', 0, 1);
    split.add('list', 1, 1);
    expect(split.aligned(['box', 'staged'])).toBe(true);
    expect(split.aligned(['box', 'staged', 'list'])).toBe(false);
  });

  it('the fixture that separates the list reading from the pairwise one is violated', async () => {
    // Three keystrokes: the net rests with two stale replies in `reply` and `staged` empty.
    const f = fixtureById('nu-aligned-search-three-keystrokes-quiescent-violated');
    const result = await fixtureVerifier(f).verifier.verify();
    expect(result.route).toBe('nu-scg');
    expect(result.verdict.type).toBe('violated');
    expect(result.counterexampleTransitions).toHaveLength(12);
    const rest = result.counterexampleTrace[result.counterexampleTrace.length - 1]!;
    expect([...rest.placesWithTokens()].map(p => p.name)).not.toContain('staged');
  });

  it('reordering S changes no verdict and no witness length', async () => {
    const f = fixtureById('nu-aligned-search-three-quiescent-violated');
    const { verifier, p } = fixtureVerifier(f);
    for (const order of [['box', 'list', 'reply'], ['reply', 'box', 'list'], ['list', 'reply', 'box']]) {
      const result = await verifier.property(quiescentNameAligned(...(order.map(p) as [Place<unknown>]))).verify();
      expect(result.verdict.type, order.join(',')).toBe('violated');
      expect(result.counterexampleTransitions, order.join(',')).toHaveLength(f.witnessLength!);
    }
  });
});

describe('NU-055 AC4: no other route decides name alignment', () => {
  const fixed = fixtureById('nu-aligned-search-quiescent-proven');
  const { verifier, p, net } = fixtureVerifier(fixed);
  const initial = MarkingState.builder();
  for (const [n, k] of Object.entries(fixed.marking)) initial.tokens(p(n), k);
  const m0 = initial.build();
  const flat = flatten(net);
  const props: readonly SmtProperty[] = [nameAligned(p('box'), p('list')), quiescentNameAligned(p('box'), p('list'))];
  const ONLY_B = 'decided only by the name-partition state-class graph (NU-055, Route B)';

  for (const prop of props) {
    describe(prop.type, () => {
      it('encodeScripts returns no script', () => {
        expect(() => verifier.property(prop).encodeScripts()).toThrow(ONLY_B);
      });

      it('Route A (NU-050, NU-053) gives no encoding', () => {
        // With the budget fixture's declaration the net is in Route A's fragment: a plan exists,
        // but a colour slot is not a name, so it encodes no name-alignment query.
        const mints = declaredMints(net, new Set(['slot']), new Set(fixed.mintTransitions));
        const plan = buildColouredPlan(
          net, flat, m0, mints, 'extended', new Set(fixed.carrierPlaces), c => solveSlotBound(flat, m0, c),
        );
        expect(plan).not.toBeNull();
        expect(encodeColoured(plan!, flat, m0, prop, [], new Set())).toBeNull();
      });

      it('the flat HORN encoder (VER-001) gives no script', () => {
        expect(() => encodeNet(flat, m0, prop, [])).toThrow(ONLY_B);
      });

      it('the linear bound (VER-015) has no demand', () => {
        expect(violationDemand(flat, prop)).toBeNull();
        expect(encodeLinearBound(flat, m0, prop)).toBeNull();
      });

      it('the state-equation phase (VER-018) is inconclusive', async () => {
        expect(() => encodeStateEquationQuery(flat, m0, prop, new Set(), [], [])).toThrow(ONLY_B);
        const outcome = await runStateEquationPhase(flat, m0, prop, new Set(), [], async () => {
          throw new Error('no solver call expected');
        });
        expect(outcome.kind).toBe('inconclusive');
        expect(outcome.kind === 'inconclusive' && outcome.reason).toContain(ONLY_B);
      });

      it('the firing-bound phase (VER-019) is inconclusive', async () => {
        const outcome = await runFiringBoundPhase(flat, m0, prop, new Set(), [], async () => {
          throw new Error('no solver call expected');
        });
        expect(outcome.kind).toBe('inconclusive');
        expect(outcome.kind === 'inconclusive' && outcome.reason).toContain(ONLY_B);
      });

      it('the bounded enumeration (VER-017) is unknown', () => {
        const outcome = verifyViaStateClassGraph(net, m0, prop, new Set(), 10_000);
        expect(outcome.kind).toBe('decided');
        expect(outcome.kind === 'decided' && outcome.verdict.type).toBe('unknown');
        expect(outcome.kind === 'decided' && outcome.verdict.type === 'unknown' && outcome.verdict.reason)
          .toContain(ONLY_B);
      });

      it('a graph without a name layer refuses to decide it', () => {
        // With or without a resting class: no class may be read as aligned for want of names.
        for (const quiescent of [true, false]) {
          const view = { count: 1, markingOf: () => m0, isQuiescent: () => quiescent };
          expect(() => decideOverClasses(view, prop, new Set())).toThrow(ONLY_B);
        }
      });

      it('the abstract replayer reads no names', () => {
        expect(() => satisfiesBad(vectorize(m0, flat), flat, prop, new Set())).toThrow(ONLY_B);
      });
    });
  }

  it('a declared budget place still sends NameAligned to Route B', async () => {
    const result = await fixtureVerifier(fixtureById('nu-aligned-search-budget-transient-violated')).verifier.verify();
    expect(result.route).toBe('nu-scg');
    expect(result.report).not.toContain('Route A');
  });

  it('a Route B truncation stays unknown, with no deferral to Route A', async () => {
    const { verifier: v, p: q } = fixtureVerifier(fixed);
    const result = await v.budgetPlaces(q('slot')).nuMaxClasses(5).verify();
    expect(result.route).toBe('nu-scg');
    expect(result.verdict.type).toBe('unknown');
    expect(result.report).not.toContain('deferring to Route A');
  });

  it('the prefix rule: a truncated NameAligned graph is violated by a stored class, else unknown', async () => {
    // The fixed net's graph closes at 31 classes and its first misaligned class is the 24th.
    const f = fixtureById('nu-aligned-search-transient-violated');
    // A reachability-safety property: the build stops at its first violating class (VER-012).
    const full = await fixtureVerifier(f).verifier.verify();
    expect(full.report).toContain('Route B stopped at the first violating class');
    const cut = await fixtureVerifier(f).verifier.nuMaxClasses(20).verify();
    expect(cut.route).toBe('nu-scg');
    expect(cut.verdict.type).toBe('unknown');
    const prefix = await fixtureVerifier(f).verifier.nuMaxClasses(25).verify();
    expect(prefix.verdict.type).toBe('violated');
    expect(prefix.counterexampleTransitions).toHaveLength(8);
  });

  it('the prefix rule: a truncated QuiescentNameAligned graph is violated by an expanded class at rest', async () => {
    // `gen` grows `junk` without bound, so the graph never closes; `stop` ends the generator,
    // and after `sendA` and `sendB` minted two names into `box` and `list` the net rests misaligned.
    const a = place<string>('a');
    const b = place<string>('b');
    const g = place<string>('g');
    const box = place<string>('box');
    const list = place<string>('list');
    const junk = place<string>('junk');
    const done = place<string>('done');
    const step = (name: string, from: Place<string>, ...to: Place<string>[]) =>
      Transition.builder(name).inputs(one(from)).outputs(to.length === 1 ? outPlace(to[0]!) : andPlaces(...to))
        .action(async () => {}).build();
    const net = PetriNet.builder('unboundedRest')
      .transitions(step('sendA', a, box), step('sendB', b, list), step('gen', g, g, junk), step('stop', g, done))
      .build();
    const result = await SmtVerifier.forNet(net)
      .initialMarking(m => m.tokens(a, 1).tokens(b, 1).tokens(g, 1))
      .mintTransitions('sendA', 'sendB')
      .carrierPlaces(box, list)
      .fragmentMode('extended')
      .nuMaxClasses(50)
      .property(quiescentNameAligned(box, list))
      .verify();
    expect(result.route).toBe('nu-scg');
    expect(result.verdict.type, result.report).toBe('violated');
    expect(result.counterexampleTransitions).toHaveLength(3);
    expect(result.report).toContain('was truncated at 50 classes; the violation was found in the explored prefix');
  });

  it('existing properties on the matchless bug variant keep their route', async () => {
    // The has-match gate is lifted for name alignment only: a quiescentCount on a net without a
    // matched transition is still decided by the plain enumeration (VER-017).
    const { verifier: v, p: q } = fixtureVerifier(fixtureById('nu-aligned-search-bug-quiescent-violated'));
    const result = await v.property(quiescentCount([q('list')], 1, 1)).verify();
    expect(result.route).toBe('enumeration');
    const dl = await v.property(deadlockFree()).verify();
    expect(dl.route).not.toBe('nu-scg');
  });
});

describe('NU-055 AC5: invariance under name permutation', () => {
  it('the predicate gives the same answer on a class and on its permutation', () => {
    const marking = (perm: (s: number) => number): NameMarking => {
      const nm = new NameMarking();
      nm.add('box', perm(0), 1);
      nm.add('list', perm(1), 1);
      nm.add('reply', perm(0), 1);
      nm.add('reply', perm(2), 1);
      nm.add('staged', perm(2), 1);
      return nm;
    };
    const identity = marking(s => s);
    const swapped = marking(s => [7, 3, 5][s]!);
    const order = ['box', 'list', 'reply', 'staged'];
    expect(swapped.canonicalKey(order)).toBe(identity.canonicalKey(order));
    const lists = [...order.map(p => [p]), ...order.flatMap(p => order.filter(q => q !== p).map(q => [p, q])), order];
    for (const s of lists) {
      expect(swapped.aligned(s)).toBe(identity.aligned(s));
      // Only membership counts: S reversed, or with a place repeated, reads the same.
      expect(identity.aligned([...s].reverse())).toBe(identity.aligned(s));
      expect(identity.aligned([...s, s[0]!])).toBe(identity.aligned(s));
    }
    expect(identity.aligned(['box', 'list'])).toBe(false);
    expect(identity.aligned(['box', 'reply'])).toBe(false);
    expect(identity.aligned(['reply', 'staged'])).toBe(false);
    expect(identity.aligned(['staged'])).toBe(true);
    expect(identity.aligned(['reply'])).toBe(false);
    expect(identity.aligned(['box', 'inflightA'])).toBe(true); // an empty place imposes nothing
  });

  it('safetyViolation reads the name layer for NameAligned only', () => {
    const box = place('box');
    const list = place('list');
    const nm = new NameMarking();
    nm.add('box', 0, 1);
    nm.add('list', 1, 1);
    expect(safetyViolation(nameAligned(box, list))!(MarkingState.empty(), nm)).toBe(true);
    expect(safetyViolation(quiescentNameAligned(box, list))).toBeNull();
  });

  it('the fixed net classifies with box and list coloured, the bug variant without a matched transition', () => {
    const f = fixtureById('nu-aligned-search-bug-quiescent-violated');
    const { net } = fixtureVerifier(f);
    expect([...net.transitions].some(t => t.matchSpec !== null)).toBe(false);
    const carriers = new Set(f.carrierPlaces);
    const mints = new Set(f.mintTransitions);
    // Without a matched transition the default classifier sees no ν-net; a name-alignment query lifts that.
    expect(classify(net, 'extended', carriers, mints)).toBeNull();
    const fragment = classify(net, 'extended', carriers, mints, /* admitMatchless */ true);
    expect(fragment?.colouredOrder).toEqual([...carriers].sort());
  });

  describe('a run with a pinned minting scope (NU-010, NU-011)', () => {
    const backends = [
      { name: 'BitmapNetExecutor', make: (net: PetriNet, t: Map<Place<any>, Token<any>[]>, scope?: string) =>
        new BitmapNetExecutor(net, t, { executionScope: scope }) },
      { name: 'PrecompiledNetExecutor', make: (net: PetriNet, t: Map<Place<any>, Token<any>[]>, scope?: string) =>
        new PrecompiledNetExecutor(net, t, { executionScope: scope }) },
    ];

    for (const backend of backends) {
      for (const scope of [undefined, 'nu055-scope']) {
        for (const bug of [false, true]) {
          it(`${backend.name}, ${scope ?? 'default'} scope, ${bug ? 'bug variant' : 'fixed net'}`, async () => {
            const { net, places } = searchAsYouType(bug);
            const marking = await backend.make(net, initialTokens(places), scope).run(5000);
            const box = names(marking, places.get('box')!);
            const list = names(marking, places.get('list')!);
            expect(box).toHaveLength(1);
            expect(list).toHaveLength(1);
            if (scope !== undefined) expect(box[0]).toContain(`#${scope}:`);
            // The fixed net rests aligned (QuiescentNameAligned proven); the bug variant, with the
            // first reply answered last, rests on the old results (violated with 12 firings).
            if (bug) expect(list[0]).not.toBe(box[0]);
            else expect(list[0]).toBe(box[0]);
          });
        }
      }
    }

    it('the verdicts on the executable nets match the fixtures', async () => {
      for (const bug of [false, true]) {
        const { net, places } = searchAsYouType(bug);
        const p = (n: string) => places.get(n)!;
        const carriers = bug ? ['box', 'inflightA', 'inflightB', 'reply', 'staged', 'list'] : ['inflightA', 'inflightB', 'list'];
        const result: SmtVerificationResult = await SmtVerifier.forNet(net)
          .initialMarking(m => { for (const [n, k] of INITIAL) m.tokens(p(n), k); })
          .property(quiescentNameAligned(p('box'), p('list')))
          .mintTransitions('sendA', 'sendB')
          .carrierPlaces(...carriers.map(p))
          .fragmentMode('extended')
          .verify();
        expect(result.route).toBe('nu-scg');
        expect(result.verdict.type).toBe(bug ? 'violated' : 'proven');
      }
    });
  });
});

const INITIAL: ReadonlyArray<readonly [string, number]> = [['typed', 2], ['idle', 1], ['listEmpty', 1], ['slot', 1]];

function initialTokens(places: ReadonlyMap<string, Place<string>>): Map<Place<any>, Token<any>[]> {
  return new Map(INITIAL.map(([n, k]) => [places.get(n)!, Array.from({ length: k }, () => tokenOf('unit'))]));
}

function names(marking: Marking, p: Place<string>): string[] {
  return marking.peekTokens(p).map(t => t.value);
}

/**
 * The search-as-you-type net of NU-055 with executable actions: each token of a coloured place
 * is its name. `fetchA` answers only once `show` has shown a result, so the reply to the first
 * keystroke lands after the reply to the second, deterministically: the run the bug variant's
 * counterexample describes.
 */
function searchAsYouType(bug: boolean): { net: PetriNet; places: Map<string, Place<string>> } {
  const places = new Map<string, Place<string>>();
  const p = (n: string): Place<string> => {
    let x = places.get(n);
    if (x === undefined) {
      x = place<string>(n);
      places.set(n, x);
    }
    return x;
  };
  let releaseA: () => void = () => {};
  const firstShown = new Promise<void>(r => { releaseA = r; });
  const key = (v: string) => nameId(v);
  const unit = (out: string) => async (ctx: TransitionContext) => { ctx.output(p(out), 'unit'); };
  const relay = (from: string, to: string) => async (ctx: TransitionContext) => { ctx.output(p(to), ctx.input(p(from))); };
  const mint = (inflight: string) => async (ctx: TransitionContext) => {
    const n = ctx.freshName();
    ctx.output(p('box'), n);
    ctx.output(p(inflight), n);
  };
  const ts = [
    Transition.builder('first').inputs(one(p('idle')), one(p('typed'))).outputs(outPlace(p('armedA'))).action(unit('armedA')),
    Transition.builder('retire').inputs(one(p('box')), one(p('typed'))).outputs(outPlace(p('armedB'))).action(unit('armedB')),
    Transition.builder('sendA').inputs(one(p('armedA'))).outputs(andPlaces(p('box'), p('inflightA'))).action(mint('inflightA')),
    Transition.builder('sendB').inputs(one(p('armedB'))).outputs(andPlaces(p('box'), p('inflightB'))).action(mint('inflightB')),
    Transition.builder('fetchA').inputs(one(p('inflightA'))).outputs(outPlace(p('reply'))).action(async (ctx: TransitionContext) => {
      const n = ctx.input(p('inflightA'));
      await firstShown;
      ctx.output(p('reply'), n);
    }),
    Transition.builder('fetchB').inputs(one(p('inflightB'))).outputs(outPlace(p('reply'))).action(relay('inflightB', 'reply')),
    bug
      ? Transition.builder('apply_bug').inputs(one(p('reply')), one(p('slot'))).outputs(andPlaces(p('staged'), p('clr')))
        .action(async (ctx: TransitionContext) => {
          ctx.output(p('staged'), ctx.input(p('reply')));
          ctx.output(p('clr'), 'unit');
        })
      : Transition.builder('apply').inputs(one(p('reply')), one(p('box')), one(p('slot')))
        .match(matchSpec(matchKey(p('reply'), key), matchKey(p('box'), key), relayKey(p('box'), key), relayKey(p('staged'), key)))
        .outputs(andPlaces(p('box'), p('staged'), p('clr')))
        .action(async (ctx: TransitionContext) => {
          const n = ctx.input(p('reply'));
          ctx.output(p('box'), n);
          ctx.output(p('staged'), n);
          ctx.output(p('clr'), 'unit');
        }),
    Transition.builder('clearNone').inputs(one(p('listEmpty')), one(p('clr'))).outputs(outPlace(p('ready'))).action(unit('ready')),
    Transition.builder('clear').inputs(one(p('list')), one(p('clr'))).outputs(outPlace(p('ready'))).action(unit('ready')),
    Transition.builder('show').inputs(one(p('staged')), one(p('ready'))).outputs(andPlaces(p('list'), p('slot')))
      .action(async (ctx: TransitionContext) => {
        ctx.output(p('list'), ctx.input(p('staged')));
        ctx.output(p('slot'), 'unit');
        releaseA();
      }),
  ];
  const net = PetriNet.builder(bug ? 'searchAsYouTypeBug' : 'searchAsYouType').transitions(...ts.map(t => t.build())).build();
  return { net, places };
}

