import { describe, it, expect } from 'vitest';
import { place } from '../../../src/core/place.js';
import type { Place } from '../../../src/core/place.js';
import { Transition } from '../../../src/core/transition.js';
import { PetriNet } from '../../../src/core/petri-net.js';
import {
  one,
  exactly,
  all,
  atLeast,
  type In,
} from '../../../src/core/in.js';
import {
  outPlace,
  and,
  xor,
  timeout,
  forwardInput,
  type Out,
} from '../../../src/core/out.js';
import {
  renamePlace,
  renameNet,
  rewriteTransition,
  substitutePlaces,
  rewriteIn,
  rewriteOut,
  rewriteInhibitor,
  rewriteRead,
  rewriteReset,
} from '../../../src/core/internal/subnet-rewriter.js';

/**
 * Unit tests for the package-internal subnet rewriter. The rewriter is the
 * structural rewrite primitive used by `SubnetDef.instantiate` and (later)
 * `PetriNetBuilder.compose(...)`. These tests pin the per-arc-variant
 * rewrite contract and the `renameNet` end-to-end rename pass.
 */
describe('SubnetRewriter', () => {
  // ============================================================
  //  renamePlace — basic shape
  // ============================================================

  describe('renamePlace', () => {
    it('prefixes the name with prefix + "/"', () => {
      const orig = place<string>('p');
      const renamed = renamePlace(orig, 'pre');
      expect(renamed.name).toBe('pre/p');
    });

    it('returns a fresh Place reference (does not mutate input)', () => {
      const orig = place<string>('p');
      const renamed = renamePlace(orig, 'pre');
      expect(renamed).not.toBe(orig);
      expect(orig.name).toBe('p');
    });
  });

  // ============================================================
  //  resolve / partial-remap behavior — places not in remap are kept
  // ============================================================

  describe('partial-remap (places not in remap pass through)', () => {
    it('rewriteIn with empty remap returns identical-shaped In with same place', () => {
      const p = place<number>('p');
      const remap = new Map<string, Place<unknown>>();
      const rewritten = rewriteIn(one(p), remap) as { type: 'one'; place: Place<unknown> };
      expect(rewritten.type).toBe('one');
      expect(rewritten.place).toBe(p);
    });

    it('rewriteOut with empty remap on a Place leaf preserves the place', () => {
      const p = place<string>('out');
      const remap = new Map<string, Place<unknown>>();
      const rewritten = rewriteOut(outPlace(p), remap) as { type: 'place'; place: Place<unknown> };
      expect(rewritten.type).toBe('place');
      expect(rewritten.place).toBe(p);
    });

    it('rewriteInhibitor with partial remap substitutes only known places', () => {
      const p = place<string>('p');
      const q = place<string>('q');
      const renamedP = place<string>('pre/p');
      const remap = new Map<string, Place<unknown>>([['p', renamedP as Place<unknown>]]);

      // p is in remap, q is not.
      const rewrittenP = rewriteInhibitor({ type: 'inhibitor', place: p }, remap);
      const rewrittenQ = rewriteInhibitor({ type: 'inhibitor', place: q }, remap);

      expect(rewrittenP.place).toBe(renamedP);
      expect(rewrittenQ.place).toBe(q);
    });
  });

  // ============================================================
  //  rewriteIn — exhaustive over In discriminator
  // ============================================================

  describe('rewriteIn — all variants', () => {
    function makeRemap(orig: Place<unknown>, prefix: string): Map<string, Place<unknown>> {
      return new Map([[orig.name, place<unknown>(prefix + '/' + orig.name)]]);
    }

    it('one: substitutes place, preserves type discriminator', () => {
      const p = place<number>('p');
      const remap = makeRemap(p as Place<unknown>, 'pre');
      const rewritten = rewriteIn(one(p), remap);
      expect(rewritten.type).toBe('one');
      expect(rewritten.place.name).toBe('pre/p');
    });

    it('exactly: preserves count and substitutes place', () => {
      const p = place<number>('p');
      const remap = makeRemap(p as Place<unknown>, 'pre');
      const rewritten = rewriteIn(exactly(3, p), remap) as Extract<In, { type: 'exactly' }>;
      expect(rewritten.type).toBe('exactly');
      expect(rewritten.count).toBe(3);
      expect(rewritten.place.name).toBe('pre/p');
    });

    it('all: substitutes place', () => {
      const p = place<number>('p');
      const remap = makeRemap(p as Place<unknown>, 'pre');
      const rewritten = rewriteIn(all(p), remap) as Extract<In, { type: 'all' }>;
      expect(rewritten.type).toBe('all');
      expect(rewritten.place.name).toBe('pre/p');
    });

    it('at-least: preserves minimum and substitutes place', () => {
      const p = place<number>('p');
      const remap = makeRemap(p as Place<unknown>, 'pre');
      const rewritten = rewriteIn(atLeast(2, p), remap) as Extract<In, { type: 'at-least' }>;
      expect(rewritten.type).toBe('at-least');
      expect(rewritten.minimum).toBe(2);
      expect(rewritten.place.name).toBe('pre/p');
    });
  });

  // ============================================================
  //  rewriteOut — exhaustive over Out discriminator + recursion
  // ============================================================

  describe('rewriteOut — all variants', () => {
    function makeRemap(prefix: string, ...originals: Place<unknown>[]): Map<string, Place<unknown>> {
      const m = new Map<string, Place<unknown>>();
      for (const p of originals) m.set(p.name, place<unknown>(prefix + '/' + p.name));
      return m;
    }

    it('place: substitutes place', () => {
      const p = place<string>('p');
      const remap = makeRemap('pre', p as Place<unknown>);
      const rewritten = rewriteOut(outPlace(p), remap) as Extract<Out, { type: 'place' }>;
      expect(rewritten.type).toBe('place');
      expect(rewritten.place.name).toBe('pre/p');
    });

    it('forward-input: substitutes both from and to', () => {
      const from = place<string>('from');
      const to = place<string>('to');
      const remap = makeRemap('pre', from as Place<unknown>, to as Place<unknown>);
      const rewritten = rewriteOut(forwardInput(from, to), remap) as Extract<Out, { type: 'forward-input' }>;
      expect(rewritten.type).toBe('forward-input');
      expect(rewritten.from.name).toBe('pre/from');
      expect(rewritten.to.name).toBe('pre/to');
    });

    it('and: substitutes children in order', () => {
      const a = place<string>('a');
      const b = place<string>('b');
      const remap = makeRemap('pre', a as Place<unknown>, b as Place<unknown>);
      const original = and(outPlace(a), outPlace(b));
      const rewritten = rewriteOut(original, remap) as Extract<Out, { type: 'and' }>;
      expect(rewritten.type).toBe('and');
      expect(rewritten.children).toHaveLength(2);
      expect((rewritten.children[0] as Extract<Out, { type: 'place' }>).place.name).toBe('pre/a');
      expect((rewritten.children[1] as Extract<Out, { type: 'place' }>).place.name).toBe('pre/b');
    });

    it('xor: substitutes children in order', () => {
      const a = place<string>('a');
      const b = place<string>('b');
      const remap = makeRemap('pre', a as Place<unknown>, b as Place<unknown>);
      const original = xor(outPlace(a), outPlace(b));
      const rewritten = rewriteOut(original, remap) as Extract<Out, { type: 'xor' }>;
      expect(rewritten.type).toBe('xor');
      expect(rewritten.children).toHaveLength(2);
      expect((rewritten.children[0] as Extract<Out, { type: 'place' }>).place.name).toBe('pre/a');
      expect((rewritten.children[1] as Extract<Out, { type: 'place' }>).place.name).toBe('pre/b');
    });

    it('timeout: preserves afterMs, recurses into child', () => {
      const p = place<string>('p');
      const remap = makeRemap('pre', p as Place<unknown>);
      const rewritten = rewriteOut(timeout(150, outPlace(p)), remap) as Extract<Out, { type: 'timeout' }>;
      expect(rewritten.type).toBe('timeout');
      expect(rewritten.afterMs).toBe(150);
      expect((rewritten.child as Extract<Out, { type: 'place' }>).place.name).toBe('pre/p');
    });

    it('and(xor(...), and(...)): nested recursion through both branches', () => {
      const a = place<string>('a');
      const b = place<string>('b');
      const c = place<string>('c');
      const d = place<string>('d');
      const remap = makeRemap(
        'pre',
        a as Place<unknown>,
        b as Place<unknown>,
        c as Place<unknown>,
        d as Place<unknown>,
      );

      const nested = and(xor(outPlace(a), outPlace(b)), and(outPlace(c), outPlace(d)));
      const rewritten = rewriteOut(nested, remap) as Extract<Out, { type: 'and' }>;

      expect(rewritten.type).toBe('and');
      const xorBranch = rewritten.children[0] as Extract<Out, { type: 'xor' }>;
      expect(xorBranch.type).toBe('xor');
      expect((xorBranch.children[0] as Extract<Out, { type: 'place' }>).place.name).toBe('pre/a');
      expect((xorBranch.children[1] as Extract<Out, { type: 'place' }>).place.name).toBe('pre/b');

      const andBranch = rewritten.children[1] as Extract<Out, { type: 'and' }>;
      expect(andBranch.type).toBe('and');
      expect((andBranch.children[0] as Extract<Out, { type: 'place' }>).place.name).toBe('pre/c');
      expect((andBranch.children[1] as Extract<Out, { type: 'place' }>).place.name).toBe('pre/d');
    });

    it('timeout(and(forward-input)): triple-nested recursion', () => {
      const from = place<string>('from');
      const to = place<string>('to');
      const remap = new Map<string, Place<unknown>>([
        ['from', place<unknown>('pre/from')],
        ['to', place<unknown>('pre/to')],
      ]);

      const out: Out = timeout(50, and(forwardInput(from, to)));
      const rewritten = rewriteOut(out, remap) as Extract<Out, { type: 'timeout' }>;
      expect(rewritten.type).toBe('timeout');
      expect(rewritten.afterMs).toBe(50);
      const andChild = rewritten.child as Extract<Out, { type: 'and' }>;
      expect(andChild.type).toBe('and');
      const fwd = andChild.children[0] as Extract<Out, { type: 'forward-input' }>;
      expect(fwd.type).toBe('forward-input');
      expect(fwd.from.name).toBe('pre/from');
      expect(fwd.to.name).toBe('pre/to');
    });
  });

  // ============================================================
  //  rewriteInhibitor / rewriteRead / rewriteReset
  // ============================================================

  describe('rewriteInhibitor / rewriteRead / rewriteReset', () => {
    it('inhibitor: substitutes place', () => {
      const p = place<string>('p');
      const renamed = place<unknown>('pre/p');
      const remap = new Map<string, Place<unknown>>([['p', renamed]]);
      const rewritten = rewriteInhibitor({ type: 'inhibitor', place: p }, remap);
      expect(rewritten.type).toBe('inhibitor');
      expect(rewritten.place).toBe(renamed);
    });

    it('read: substitutes place', () => {
      const p = place<string>('p');
      const renamed = place<unknown>('pre/p');
      const remap = new Map<string, Place<unknown>>([['p', renamed]]);
      const rewritten = rewriteRead({ type: 'read', place: p }, remap);
      expect(rewritten.type).toBe('read');
      expect(rewritten.place).toBe(renamed);
    });

    it('reset: substitutes place', () => {
      const p = place<string>('p');
      const renamed = place<unknown>('pre/p');
      const remap = new Map<string, Place<unknown>>([['p', renamed]]);
      const rewritten = rewriteReset({ type: 'reset', place: p }, remap);
      expect(rewritten.type).toBe('reset');
      expect(rewritten.place).toBe(renamed);
    });
  });

  // ============================================================
  //  rewriteTransition — name prefix + arc rewrite + action by-ref
  // ============================================================

  describe('rewriteTransition', () => {
    it('prefixes name and rewrites arcs; preserves action by reference', () => {
      const p = place<string>('p');
      const q = place<string>('q');
      const action = async () => {};
      const t = Transition.builder('t')
        .inputs(one(p))
        .outputs(outPlace(q))
        .priority(2)
        .action(action)
        .build();

      const remap = new Map<string, Place<unknown>>([
        ['p', place<unknown>('pre/p')],
        ['q', place<unknown>('pre/q')],
      ]);
      const renamed = rewriteTransition(t, 'pre', remap);

      expect(renamed.name).toBe('pre/t');
      expect(renamed.priority).toBe(2);
      expect(renamed.action).toBe(action);
      expect(renamed.inputSpecs).toHaveLength(1);
      expect((renamed.inputSpecs[0] as Extract<In, { type: 'one' }>).place.name).toBe('pre/p');
      expect(renamed.outputSpec).not.toBeNull();
      expect((renamed.outputSpec as Extract<Out, { type: 'place' }>).place.name).toBe('pre/q');
    });

    it('preserves inhibitor / read / reset arcs', () => {
      const p = place<string>('p');
      const inh = place<string>('inh');
      const rd = place<string>('rd');
      const rs = place<string>('rs');

      const t = Transition.builder('t')
        .read(p)
        .inhibitor(inh)
        .read(rd)
        .reset(rs)
        .build();

      const remap = new Map<string, Place<unknown>>([
        ['p', place<unknown>('pre/p')],
        ['inh', place<unknown>('pre/inh')],
        ['rd', place<unknown>('pre/rd')],
        ['rs', place<unknown>('pre/rs')],
      ]);
      const renamed = rewriteTransition(t, 'pre', remap);

      expect(renamed.inhibitors).toHaveLength(1);
      expect(renamed.inhibitors[0]!.place.name).toBe('pre/inh');
      expect(renamed.reads).toHaveLength(2);
      expect(renamed.reads.map((r) => r.place.name).sort()).toEqual(['pre/p', 'pre/rd']);
      expect(renamed.resets).toHaveLength(1);
      expect(renamed.resets[0]!.place.name).toBe('pre/rs');
    });
  });

  // ============================================================
  //  substitutePlaces — same name, place substitution only
  // ============================================================

  describe('substitutePlaces', () => {
    it('keeps the original name; substitutes places only', () => {
      const p = place<string>('p');
      const t = Transition.builder('keep_my_name').inputs(one(p)).build();
      const remap = new Map<string, Place<unknown>>([
        ['p', place<unknown>('caller/p')],
      ]);

      const rewritten = substitutePlaces(t, remap);
      expect(rewritten.name).toBe('keep_my_name');
      expect((rewritten.inputSpecs[0] as Extract<In, { type: 'one' }>).place.name).toBe('caller/p');
    });

    it('partial remap: places not in remap pass through unchanged', () => {
      const p = place<string>('p');
      const q = place<string>('q');
      const t = Transition.builder('t').inputs(one(p), one(q)).build();
      const remap = new Map<string, Place<unknown>>([
        ['p', place<unknown>('caller/p')],
      ]);

      const rewritten = substitutePlaces(t, remap);
      expect(rewritten.inputSpecs).toHaveLength(2);
      const placeNames = rewritten.inputSpecs.map(
        (s) => (s as Extract<In, { type: 'one' }>).place.name,
      );
      expect(placeNames).toContain('caller/p');
      expect(placeNames).toContain('q');
    });
  });

  // ============================================================
  //  renameNet — end-to-end rename pass + remap-side-effect contract
  // ============================================================

  describe('renameNet', () => {
    it('renames every place and transition; fills both remaps; preserves stranded places', () => {
      const a = place<string>('a');
      const b = place<string>('b');
      const stranded = place<string>('stranded');
      const t = Transition.builder('t').inputs(one(a)).outputs(outPlace(b)).build();
      const body = PetriNet.builder('body').place(stranded).transition(t).build();

      const placeRemap = new Map<string, Place<unknown>>();
      const transitionRemap = new Map<string, Transition>();
      const renamed = renameNet(body, 'pre', placeRemap, transitionRemap);

      // Net name is prefixed.
      expect(renamed.name).toBe('pre/body');

      // All places renamed AND stranded place is preserved.
      const renamedPlaceNames = [...renamed.places].map((p) => p.name).sort();
      expect(renamedPlaceNames).toEqual(['pre/a', 'pre/b', 'pre/stranded']);

      // Transition renamed.
      expect(renamed.transitions.size).toBe(1);
      const [renamedT] = [...renamed.transitions];
      expect(renamedT!.name).toBe('pre/t');

      // Remaps populated.
      expect(placeRemap.get('a')?.name).toBe('pre/a');
      expect(placeRemap.get('b')?.name).toBe('pre/b');
      expect(placeRemap.get('stranded')?.name).toBe('pre/stranded');
      expect(transitionRemap.get('t')).toBe(renamedT);
    });

    it('clears caller-supplied maps before populating', () => {
      const p = place<string>('p');
      const t = Transition.builder('t').read(p).build();
      const body = PetriNet.builder('body').transition(t).build();

      const placeRemap = new Map<string, Place<unknown>>([
        ['stale', place<unknown>('stale_value')],
      ]);
      const transitionRemap = new Map<string, Transition>([
        ['stale_t', t],
      ]);

      renameNet(body, 'pre', placeRemap, transitionRemap);

      expect(placeRemap.has('stale')).toBe(false);
      expect(transitionRemap.has('stale_t')).toBe(false);
      expect(placeRemap.get('p')?.name).toBe('pre/p');
    });
  });
});
