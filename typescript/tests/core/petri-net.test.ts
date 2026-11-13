import { describe, it, expect } from 'vitest';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace, andPlaces } from '../../src/core/out.js';
import { matchSpec, matchKey } from '../../src/core/match-spec.js';
import { nameId } from '../../src/core/name.js';
import type { TransitionAction } from '../../src/core/transition-action.js';
import { fork, isPassthrough } from '../../src/core/transition-action.js';
import { CompiledNet } from '../../src/runtime/compiled-net.js';
import { FusionSet } from '../../src/core/fusion-set.js';
import { retryPolicy } from '../fixtures/subnet-fixtures.js';

describe('PetriNet', () => {
  const p1 = place<string>('P1');
  const p2 = place<number>('P2');
  const p3 = place<string>('P3');

  it('creates net with builder', () => {
    const t = Transition.builder('T')
      .inputs(one(p1))
      .outputs(outPlace(p2))
      .build();

    const net = PetriNet.builder('TestNet')
      .transition(t)
      .build();

    expect(net.name).toBe('TestNet');
    expect(net.transitions.size).toBe(1);
    // Places auto-collected from transitions
    expect(net.places.size).toBe(2);
  });

  it('auto-collects places from transitions', () => {
    const t = Transition.builder('T')
      .inputs(one(p1))
      .outputs(andPlaces(p2, p3))
      .inhibitor(p3)
      .build();

    const net = PetriNet.builder('Net')
      .transition(t)
      .build();

    const placeNames = [...net.places].map(p => p.name).sort();
    expect(placeNames).toContain('P1');
    expect(placeNames).toContain('P2');
    expect(placeNames).toContain('P3');
  });

  it('allows explicit places', () => {
    const orphan = place('Orphan');
    const net = PetriNet.builder('Net')
      .place(orphan)
      .build();

    expect(net.places.has(orphan)).toBe(true);
  });

  it('bindActions replaces action by transition name', () => {
    const t = Transition.builder('T')
      .inputs(one(p1))
      .outputs(outPlace(p2))
      .build();

    const net = PetriNet.builder('Net')
      .transition(t)
      .build();

    const action: TransitionAction = async () => {};

    const bound = net.bindActions({ T: action });

    // Original net unchanged
    const origT = [...net.transitions][0]!;
    expect(origT.action).not.toBe(action);

    // Bound net has new action
    const boundT = [...bound.transitions][0]!;
    expect(boundT.action).toBe(action);
    expect(boundT.name).toBe('T');
    // Structure preserved
    expect(boundT.inputSpecs).toHaveLength(1);
  });

  it('bindActions with Map', () => {
    const t = Transition.builder('T')
      .inputs(one(p1))
      .outputs(outPlace(p2))
      .build();

    const net = PetriNet.builder('Net').transition(t).build();

    const action: TransitionAction = async () => {};
    const bound = net.bindActions(new Map([['T', action]]));
    const boundT = [...bound.transitions][0]!;
    expect(boundT.action).toBe(action);
  });

  it('bindActions preserves unbound transitions', () => {
    const t1 = Transition.builder('T1').build();
    const t2 = Transition.builder('T2').build();

    const net = PetriNet.builder('Net')
      .transitions(t1, t2)
      .build();

    const action: TransitionAction = async () => {};
    const bound = net.bindActions({ T1: action });

    const boundTransitions = [...bound.transitions];
    const boundT1 = boundTransitions.find(t => t.name === 'T1')!;
    const boundT2 = boundTransitions.find(t => t.name === 'T2')!;

    expect(boundT1.action).toBe(action);
    // T2 should get passthrough (default for unbound)
    expect(boundT2).toBeDefined();
  });

  it('bindActions preserves all arc specs', () => {
    const inh = place('INH');
    const rd = place('RD');
    const rst = place('RST');

    const t = Transition.builder('T')
      .inputs(one(p1))
      .outputs(outPlace(p2))
      .inhibitor(inh)
      .read(rd)
      .reset(rst)
      .priority(5)
      .build();

    const net = PetriNet.builder('Net').transition(t).build();

    const action: TransitionAction = async () => {};
    const bound = net.bindActions({ T: action });
    const boundT = [...bound.transitions][0]!;

    expect(boundT.inhibitors).toHaveLength(1);
    expect(boundT.reads).toHaveLength(1);
    expect(boundT.resets).toHaveLength(1);
    expect(boundT.priority).toBe(5);
    expect(boundT.inputSpecs).toHaveLength(1);
    expect(boundT.outputSpec).not.toBeNull();
  });

  it('bindActions preserves matchSpec', () => {
    // NU-030 regression: bindActions rebuilds each transition to attach its
    // action (rebuildWithAction). It must carry a ν-net join's matchSpec
    // forward — dropping it silently reverts a correlated join-by-id to a
    // plain FIFO AND join at runtime.
    interface Msg { cid: string; }
    const a = place<Msg>('branchA');
    const b = place<Msg>('branchB');
    const merged = place<string>('merged');

    const join = Transition.builder('join')
      .inputs(one(a), one(b))
      .match(matchSpec(
        matchKey(a, (m: Msg) => nameId(m.cid)),
        matchKey(b, (m: Msg) => nameId(m.cid)),
      ))
      .outputs(outPlace(merged))
      .build();

    const net = PetriNet.builder('matchBind').transition(join).build();
    expect([...net.transitions][0]!.matchSpec).not.toBeNull(); // precondition

    const action: TransitionAction = async () => {};
    const bound = net.bindActions({ join: action });
    const boundJoin = [...bound.transitions][0]!;

    expect(boundJoin.matchSpec,
      'bindActions must preserve the ν-net matchSpec (regression: rebuildWithAction dropped it)')
      .not.toBeNull();
    expect(boundJoin.matchSpec!.keys).toHaveLength(2);
  });

  it('bindActionsWithResolver binds via resolver function', () => {
    const t1 = Transition.builder('T1')
      .inputs(one(p1))
      .outputs(outPlace(p2))
      .build();
    const t2 = Transition.builder('T2')
      .inputs(one(p2))
      .outputs(outPlace(p3))
      .build();

    const net = PetriNet.builder('Net').transitions(t1, t2).build();

    const actions: Record<string, TransitionAction> = {};
    const action1: TransitionAction = async () => {};
    const action2: TransitionAction = async () => {};
    actions['T1'] = action1;
    actions['T2'] = action2;

    const bound = net.bindActionsWithResolver((name) => actions[name]!);

    const boundTransitions = [...bound.transitions];
    const boundT1 = boundTransitions.find(t => t.name === 'T1')!;
    const boundT2 = boundTransitions.find(t => t.name === 'T2')!;

    expect(boundT1.action).toBe(action1);
    expect(boundT2.action).toBe(action2);
    // Structure preserved
    expect(boundT1.inputSpecs).toHaveLength(1);
    expect(boundT2.outputSpec).not.toBeNull();
  });

  // ============================================================
  //  CORE-043: output-declaring transitions must produce
  // ============================================================
  //
  // The rejection itself lives at compile time — see
  // tests/runtime/compiled-net-core043.test.ts. What this block pins down is the other half
  // of the contract: that CORE-042 and MOD-031 AC7 survive it. Binding stays lazy and
  // total, so a net may still be built with no actions and bound in stages; only handing
  // one to an executor demands that the declared structure and the bound behaviour agree.

  it('bindActions leaves an output-declaring transition on passthrough (CORE-042 AC4)', () => {
    // Binding must NOT reject here, because a bind is not necessarily the last one — see the
    // staged-binding test below. Rejecting at bind time would make MOD-031 AC7's staged
    // binding unusable.
    const t = Transition.builder('T')
      .inputs(one(p1))
      .outputs(outPlace(p2))
      .build();
    const net = PetriNet.builder('Net').transition(t).build();

    const bound = net.bindActions({});

    expect(isPassthrough([...bound.transitions][0]!.action),
      'binding is lazy; the reconciliation happens at compile time (CORE-043)').toBe(true);
  });

  it('bindActionsWithResolver binds each transition in turn across two stages (MOD-031 AC7)', () => {
    // A resolver that returns null defers a transition to a later bind; the first stage must
    // not fail merely because the second has not happened yet.
    const inp = place<string>('In');
    const mid = place<string>('Mid');
    const out = place<string>('Out');

    const net = PetriNet.builder('Net').transitions(
      Transition.builder('first').inputs(one(inp)).outputs(outPlace(mid)).build(),
      Transition.builder('second').inputs(one(mid)).outputs(outPlace(out)).build(),
    ).build();

    const staged = net
      .bindActionsWithResolver((n) => (n === 'first' ? fork() : null))
      .bindActionsWithResolver((n) => (n === 'second' ? fork() : null));

    for (const t of staged.transitions) {
      expect(isPassthrough(t.action), `${t.name} must carry its bound action after both stages`)
        .toBe(false);
    }
    expect(() => CompiledNet.compile(staged), 'the fully bound net must compile').not.toThrow();
  });

  it('bindActions allows passthrough on a sink transition', () => {
    // A transition that declares no output is a legitimate sink and may retain passthrough —
    // at bind time and at compile time alike.
    const net = PetriNet.builder('Net')
      .transition(Transition.builder('sink').inputs(one(p1)).build())
      .build();

    const bound = net.bindActions({});

    expect(isPassthrough([...bound.transitions][0]!.action),
      'the unbound sink must still carry passthrough (CORE-042 AC4)').toBe(true);
    expect(() => CompiledNet.compile(bound)).not.toThrow();
  });

  it('multiple transitions', () => {
    const t1 = Transition.builder('T1')
      .inputs(one(p1))
      .outputs(outPlace(p2))
      .build();
    const t2 = Transition.builder('T2')
      .inputs(one(p2))
      .outputs(outPlace(p3))
      .build();

    const net = PetriNet.builder('Pipeline')
      .transitions(t1, t2)
      .build();

    expect(net.transitions.size).toBe(2);
    expect(net.places.size).toBe(3);
  });
  // ============================================================
  //  CORE-041: a built net does not see later builder calls
  // ============================================================

  it('a built net keeps its places and transitions when the builder is used again (CORE-041)', () => {
    const t1 = Transition.builder('T1').inputs(one(p1)).outputs(outPlace(p2)).build();
    const t2 = Transition.builder('T2').inputs(one(p2)).outputs(outPlace(p3)).build();
    const end = place<string>('End');

    const builder = PetriNet.builder('Net').transition(t1);
    const n1 = builder.build();
    builder.transition(t2).terminal(end).place(place('Extra'));
    const n2 = builder.build();

    expect([...n1.transitions]).toEqual([t1]);
    expect([...n1.places].map(p => p.name).sort()).toEqual(['P1', 'P2']);
    expect([...n2.transitions]).toEqual([t1, t2]);
    expect([...n2.places].map(p => p.name).sort()).toEqual(['End', 'Extra', 'P1', 'P2', 'P3']);
  });

  it('a channel compose after build leaves the built net intact (CORE-041)', () => {
    const callerT = Transition.builder('callerSide').build();
    const builder = PetriNet.builder('host').transition(callerT);
    const n1 = builder.build();

    builder.compose(retryPolicy().instantiate('rp1'), (b) => b.bindChannel('attempt', callerT));

    expect([...n1.transitions]).toEqual([callerT]);
  });

  // ============================================================
  //  CORE-002 / CORE-040: one place per name
  // ============================================================

  it('holds one place for two place objects with one name (CORE-002, CORE-040)', () => {
    const a1 = place<string>('A');
    const a2 = place<string>('A');
    const a3 = place<string>('A');
    const t1 = Transition.builder('T1').inputs(one(p1)).outputs(outPlace(a2)).build();
    const t2 = Transition.builder('T2').inputs(one(a3)).build();

    const net = PetriNet.builder('Net').place(a1).transitions(t1, t2).places(place('A')).build();

    const named = [...net.places].filter(p => p.name === 'A');
    expect(named).toHaveLength(1);
    expect(named[0], 'the first object added is kept').toBe(a1);
    expect(net.places.size).toBe(2);
  });

  it('holds one place for two place objects with one name after fusion (CORE-002, CORE-040)', () => {
    const a = place<string>('A');
    const b = place<string>('B');
    const c1 = place<string>('C');
    const c2 = place<string>('C');
    const t1 = Transition.builder('T1').inputs(one(a)).outputs(outPlace(c1)).build();
    const t2 = Transition.builder('T2').inputs(one(c2)).outputs(outPlace(b)).build();

    const net = PetriNet.builder('Net').transitions(t1, t2).fuse(FusionSet.of('ab', a, b)).build();

    expect([...net.places].map(p => p.name).sort()).toEqual(['A', 'C']);
  });

  // ============================================================
  //  CORE-042: a resolver that returns no action defers
  // ============================================================

  it('bindActionsWithResolver defers a transition when the resolver returns undefined (CORE-042)', () => {
    const a: TransitionAction = async () => {};
    const t = Transition.builder('T').inputs(one(p1)).outputs(outPlace(p2)).action(a).build();
    const net = PetriNet.builder('Net').transition(t).build();
    const table: Record<string, TransitionAction> = {};

    const bound = net.bindActionsWithResolver((name) => table[name]);

    const [boundT] = [...bound.transitions];
    expect(boundT).toBe(t);
    expect(boundT!.action).toBe(a);
  });
});
