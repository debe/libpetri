import { describe, it, expect } from 'vitest';
import { Instance, __createInstance } from '../../src/core/instance.js';
import { SubnetDef } from '../../src/core/subnet-def.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import type { Place } from '../../src/core/place.js';

/**
 * Trivial accessor tests for the {@link Instance} scaffolding.
 *
 * Real instance tests — the rename pass, port handle wiring, channel handle
 * wiring, and `bindActions(...)` — land with task #11. These tests exercise
 * the Symbol-guarded constructor via the package-internal factory
 * {@link __createInstance} so the API shape is pinned today.
 */
describe('Instance (scaffolding)', () => {
  function buildDef() {
    const p = place<string>('p');
    const t = Transition.builder('t').read(p).build();
    return { def: SubnetDef.builder('S').transition(t).build(), p, t };
  }

  it('rejects direct construction without the internal Symbol key', () => {
    const { def, p, t } = buildDef();
    expect(() =>
      new Instance(
        Symbol('imposter'),
        'pre',
        def,
        def.body,
        new Map<string, Place<unknown>>([['port', p]]),
        new Map([['ch', t]]),
        undefined as void,
      ),
    ).toThrow(/Use SubnetDef\.instantiate/);
  });

  it('accessors return the values supplied to the internal factory', () => {
    const { def, p, t } = buildDef();
    const portHandles = new Map<string, Place<unknown>>([['port', p]]);
    const channelHandles = new Map<string, Transition>([['ch', t]]);

    const inst = __createInstance<void>(
      'pre',
      def,
      def.body,
      portHandles,
      channelHandles,
      undefined as void,
    );

    expect(inst.prefix).toBe('pre');
    expect(inst.def).toBe(def);
    expect(inst.renamedBody).toBe(def.body);
    expect(inst.params).toBeUndefined();
    expect(inst.port<string>('port')).toBe(p);
    expect(inst.channel('ch')).toBe(t);
  });

  it('port throws on missing name', () => {
    const { def } = buildDef();
    const inst = __createInstance<void>(
      'pre',
      def,
      def.body,
      new Map<string, Place<unknown>>(),
      new Map(),
      undefined as void,
    );
    expect(() => inst.port<string>('nope')).toThrow(/No port named 'nope'/);
  });

  it('channel throws on missing name', () => {
    const { def } = buildDef();
    const inst = __createInstance<void>(
      'pre',
      def,
      def.body,
      new Map<string, Place<unknown>>(),
      new Map(),
      undefined as void,
    );
    expect(() => inst.channel('nope')).toThrow(/No channel named 'nope'/);
  });

  it('descriptor exposes prefix, defName, transitions, exposedPlaces, params', () => {
    const { def, p, t } = buildDef();
    const portHandles = new Map<string, Place<unknown>>([['port', p]]);
    const channelHandles = new Map<string, Transition>([['ch', t]]);

    const inst = __createInstance<void>(
      'pre',
      def,
      def.body,
      portHandles,
      channelHandles,
      undefined as void,
    );

    const desc = inst.descriptor();
    expect(desc.prefix).toBe('pre');
    expect(desc.defName).toBe('S');
    expect(desc.transitions).toContain('t');
    expect(desc.exposedPlaces).toContain('p');
    expect(desc.params).toBeUndefined();
    expect(desc.parentPrefix).toBeNull();
  });

});
