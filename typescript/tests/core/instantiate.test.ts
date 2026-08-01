import { describe, it, expect } from 'vitest';
import { place } from '../../src/core/place.js';
import { Transition } from '../../src/core/transition.js';
import { SubnetDef } from '../../src/core/subnet-def.js';
import { one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import type { TransitionAction } from '../../src/core/transition-action.js';

interface Item {
  readonly tag: string;
}

interface MyParams {
  readonly bufferSize: number;
  readonly label: string;
}

/**
 * Integration tests for `SubnetDef.instantiate(prefix, params)` and
 * `Instance.bindActions(...)`. Specs: MOD-010 (creation), MOD-011 (handle map),
 * MOD-012 (per-instance state isolation), MOD-013 (nested instantiation
 * partial — full nesting lands with `compose`), MOD-030 (action binding).
 */
describe('SubnetDef.instantiate', () => {
  function buildSimpleDef() {
    const input = place<Item>('input');
    const output = place<Item>('output');
    const t = Transition.builder('forward')
      .inputs(one(input))
      .outputs(outPlace(output))
      .build();
    const def = SubnetDef.builder('Forwarder')
      .transition(t)
      .inputPort('input', input)
      .outputPort('output', output)
      .channel('forward', t)
      .build();
    return { def, input, output, t };
  }

  // ============================================================
  //  MOD-010: rename pass produces prefix-namespaced body
  // ============================================================

  it('returns a renamed body where every place starts with prefix + "/"', () => {
    const { def } = buildSimpleDef();
    const inst = def.instantiate('buf1');

    for (const p of inst.renamedBody.places) {
      expect(p.name.startsWith('buf1/')).toBe(true);
    }
    for (const t of inst.renamedBody.transitions) {
      expect(t.name.startsWith('buf1/')).toBe(true);
    }
    expect(inst.renamedBody.name).toBe('buf1/Forwarder');
  });

  // ============================================================
  //  MOD-011: handle map exposes typed renamed places/transitions
  // ============================================================

  it('port handle returns the renamed Place<T> by ORIGINAL name', () => {
    const { def } = buildSimpleDef();
    const inst = def.instantiate('buf1');

    const inputPort = inst.port<Item>('input');
    expect(inputPort.name).toBe('buf1/input');

    const outputPort = inst.port<Item>('output');
    expect(outputPort.name).toBe('buf1/output');
  });

  it('channel handle returns the renamed Transition by ORIGINAL name', () => {
    const { def } = buildSimpleDef();
    const inst = def.instantiate('buf1');

    const forwardChannel = inst.channel('forward');
    expect(forwardChannel.name).toBe('buf1/forward');
  });

  it('renamed port place matches the place object inside renamedBody.places', () => {
    const { def } = buildSimpleDef();
    const inst = def.instantiate('buf1');
    const inputPort = inst.port<Item>('input');

    // The port handle must point to the SAME Place reference that lives in
    // the renamed body (not a fresh allocation), so compose(...) can rewire
    // arcs by reference equality.
    const renamedInput = [...inst.renamedBody.places].find((p) => p.name === 'buf1/input');
    expect(inputPort).toBe(renamedInput);
  });

  // ============================================================
  //  MOD-012: per-instance state isolation
  // ============================================================

  it('two instances with different prefixes have disjoint place sets', () => {
    const { def } = buildSimpleDef();
    const a = def.instantiate('a');
    const b = def.instantiate('b');

    const aPlaceNames = new Set([...a.renamedBody.places].map((p) => p.name));
    const bPlaceNames = new Set([...b.renamedBody.places].map((p) => p.name));

    for (const name of aPlaceNames) {
      expect(bPlaceNames.has(name)).toBe(false);
    }
    expect(aPlaceNames.size).toBeGreaterThan(0);
    expect(bPlaceNames.size).toBe(aPlaceNames.size);
  });

  it('two instances with different prefixes have disjoint transition sets', () => {
    const { def } = buildSimpleDef();
    const a = def.instantiate('a');
    const b = def.instantiate('b');

    const aTNames = new Set([...a.renamedBody.transitions].map((t) => t.name));
    const bTNames = new Set([...b.renamedBody.transitions].map((t) => t.name));

    for (const name of aTNames) {
      expect(bTNames.has(name)).toBe(false);
    }
  });

  // ============================================================
  //  MOD-030: actions are shared by reference across instances
  // ============================================================

  it('two instances of the same def share each transition\'s action by reference', () => {
    // Build a def whose transition has a non-passthrough action so we can
    // test "shared by reference". (passthrough() returns a singleton, so it
    // would compare equal by identity no matter how the rewriter treated it,
    // proving nothing — hence a distinct captured closure here.)
    const input = place<Item>('input');
    const output = place<Item>('output');
    const sharedAction: TransitionAction = async () => {};
    const t = Transition.builder('forward')
      .inputs(one(input))
      .outputs(outPlace(output))
      .action(sharedAction)
      .build();
    const def = SubnetDef.builder('Forwarder')
      .transition(t)
      .inputPort('input', input)
      .outputPort('output', output)
      .build();

    const a = def.instantiate('a');
    const b = def.instantiate('b');

    const [aT] = [...a.renamedBody.transitions];
    const [bT] = [...b.renamedBody.transitions];

    expect(aT!.action).toBe(sharedAction);
    expect(bT!.action).toBe(sharedAction);
    expect(aT!.action).toBe(bT!.action);
  });

  // ============================================================
  //  MOD-010: prefix validation
  // ============================================================

  it('throws on empty prefix', () => {
    const { def } = buildSimpleDef();
    expect(() => def.instantiate('')).toThrow(/non-empty/);
  });

  it('throws when prefix contains "/"', () => {
    const { def } = buildSimpleDef();
    expect(() => def.instantiate('outer/inner')).toThrow(/'\/'/);
  });

  // ============================================================
  //  Params plumbing
  // ============================================================

  it('params are reachable via instance.params for parameterised subnets', () => {
    // Build a param-typed subnet def.
    const input = place<Item>('input');
    const t = Transition.builder('t').read(input).build();
    const def = SubnetDef.builder<MyParams>('Buffer')
      .transition(t)
      .inputPort('input', input)
      .build();

    const params: MyParams = { bufferSize: 16, label: 'audio' };
    const inst = def.instantiate('aud', params);

    expect(inst.params).toBe(params);
    expect(inst.params.bufferSize).toBe(16);
    expect(inst.params.label).toBe('audio');
  });

  it('params default to undefined when omitted (SubnetDef<void>)', () => {
    const { def } = buildSimpleDef();
    const inst = def.instantiate('pre');
    expect(inst.params).toBeUndefined();
  });
});

// ============================================================
//  Instance.bindActions — MOD-030
// ============================================================

describe('Instance.bindActions', () => {
  function buildDef() {
    const input = place<Item>('input');
    const output = place<Item>('output');
    const t = Transition.builder('forward')
      .inputs(one(input))
      .outputs(outPlace(output))
      .build();
    return SubnetDef.builder('Forwarder')
      .transition(t)
      .inputPort('input', input)
      .outputPort('output', output)
      .channel('forward', t)
      .build();
  }

  it('rebinds the action on the named transition (MOD-030)', () => {
    const def = buildDef();
    const inst = def.instantiate('inst1');

    const newAction: TransitionAction = async () => {};
    const rebound = inst.bindActions({ forward: newAction });

    const [reboundT] = [...rebound.renamedBody.transitions];
    expect(reboundT!.action).toBe(newAction);
  });

  it('keeps the same prefix, def, params, and port handles after rebind', () => {
    const def = buildDef();
    const inst = def.instantiate('inst1');

    const newAction: TransitionAction = async () => {};
    const rebound = inst.bindActions({ forward: newAction });

    expect(rebound.prefix).toBe(inst.prefix);
    expect(rebound.def).toBe(inst.def);
    expect(rebound.params).toBe(inst.params);
    // Port handles point to the renamed places — these are stable across
    // bindActions because places are not rebuilt (only transitions are).
    expect(rebound.port<Item>('input')).toBe(inst.port<Item>('input'));
    expect(rebound.port<Item>('output')).toBe(inst.port<Item>('output'));
  });

  it('refreshes channel handles to point at the rebound transition', () => {
    const def = buildDef();
    const inst = def.instantiate('inst1');
    const newAction: TransitionAction = async () => {};
    const rebound = inst.bindActions({ forward: newAction });

    // The channel handle on the rebound instance should point at the
    // post-bind transition (carrying newAction), not the pre-bind one.
    const reboundChannel = rebound.channel('forward');
    expect(reboundChannel.action).toBe(newAction);
  });

  it('does not mutate the original instance (MOD-030: per-instance scope)', () => {
    const def = buildDef();
    const inst1 = def.instantiate('inst1');
    const inst2 = def.instantiate('inst2');

    const originalAction = [...inst2.renamedBody.transitions][0]!.action;

    const newAction: TransitionAction = async () => {};
    inst1.bindActions({ forward: newAction });

    // inst1's renamedBody is also untouched (bindActions returns a NEW instance).
    const inst1Action = [...inst1.renamedBody.transitions][0]!.action;
    expect(inst1Action).not.toBe(newAction);

    // inst2 — a sibling instance — is completely unaffected.
    const inst2Action = [...inst2.renamedBody.transitions][0]!.action;
    expect(inst2Action).toBe(originalAction);
  });

  it('throws when an unknown original transition name is supplied (typo guard)', () => {
    const def = buildDef();
    const inst = def.instantiate('pre');

    const newAction: TransitionAction = async () => {};
    expect(() => inst.bindActions({ nonexistent: newAction })).toThrow(/nonexistent/);
  });
});
