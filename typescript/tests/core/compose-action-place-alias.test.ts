import { describe, it, expect } from 'vitest';
import { place } from '../../src/core/place.js';
import type { Place } from '../../src/core/place.js';
import { Transition } from '../../src/core/transition.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { SubnetDef } from '../../src/core/subnet-def.js';
import { Interface } from '../../src/core/interface.js';
import { one } from '../../src/core/in.js';
import { outPlace, xorPlaces } from '../../src/core/out.js';
import { BitmapNetExecutor } from '../../src/runtime/bitmap-net-executor.js';
import { tokenOf } from '../../src/core/token.js';
import type { Token } from '../../src/core/token.js';
import type { TransitionAction } from '../../src/core/transition-action.js';

/**
 * Integration tests for **MOD-031** (Action Place Resolution under Composition),
 * per `spec/11-modular-composition.md`. The actions here hardcode their
 * **declared** place constants (NOT port-agnostic `ctx.inputPlaces()` discovery)
 * and must still fire after instancing + port binding rewrites their arcs.
 */
describe('MOD-031 — action place resolution under composition', () => {
  function seed(p: Place<string>, value: string): Map<Place<any>, Token<any>[]> {
    const initial = new Map<Place<unknown>, Token<unknown>[]>();
    initial.set(p as Place<unknown>, [tokenOf(value)] as Token<unknown>[]);
    return initial as Map<Place<any>, Token<any>[]>;
  }

  it('hardcoded-declared-place action fires under bindPort (AC#1, AC#5)', async () => {
    const reqDecl = place<string>('reqDecl');
    const respDecl = place<string>('respDecl');

    // Action hardcodes the DECLARED places — not port-agnostic discovery.
    const call: TransitionAction = async (ctx) => {
      ctx.output(respDecl, ctx.input(reqDecl) + '!');
    };
    const step = Transition.builder('call')
      .inputs(one(reqDecl))
      .outputs(outPlace(respDecl))
      .action(call)
      .build();
    const def = SubnetDef.builder('Step')
      .transition(step)
      .inputPort('in', reqDecl)
      .outputPort('out', respDecl)
      .build();

    const REQ = place<string>('REQ');
    const RESP = place<string>('RESP');

    const net = PetriNet.builder('h')
      .place(REQ)
      .place(RESP)
      .compose(def.instantiate('probe'), (b) => b.bindPort('in', REQ).bindPort('out', RESP))
      .build();

    // AC#5: place-set discovery returns the ACTUAL composed places, never the
    // declared constants — port-agnostic actions stay valid.
    const composed = [...net.transitions].find((t) => t.name === 'probe/call')!;
    const inNames = new Set([...composed.inputPlaces()].map((p) => p.name));
    const outNames = new Set([...composed.outputPlaces()].map((p) => p.name));
    expect(inNames.has('REQ')).toBe(true);
    expect(outNames.has('RESP')).toBe(true);
    expect(inNames.has('reqDecl')).toBe(false);
    expect(outNames.has('respDecl')).toBe(false);

    const executor = new BitmapNetExecutor(net, seed(REQ, 'x'));
    const marking = await executor.run(2000);

    expect(marking.hasTokens(RESP)).toBe(true);
    expect(marking.peekFirst(RESP)?.value).toBe('x!');
  });

  it('hardcoded-declared-place action bound via Instance.bindActions fires (MOD-031 ∩ CORE-042)', async () => {
    // The action is NOT baked into the def. It is bound AFTER instantiate via
    // Instance.bindActions (the stateless-structure + late-binding idiom). The
    // instantiate-time declared→actual correspondence must survive the action
    // swap, or the hardcoded declared place throws.
    const reqDecl = place<string>('reqDecl');
    const respDecl = place<string>('respDecl');

    const call: TransitionAction = async (ctx) => {
      ctx.output(respDecl, ctx.input(reqDecl) + '!');
    };

    // Structure-only def — action bound later, not at definition time.
    const def = SubnetDef.builder('Step')
      .transition(Transition.builder('call').inputs(one(reqDecl)).outputs(outPlace(respDecl)).build())
      .inputPort('in', reqDecl)
      .outputPort('out', respDecl)
      .build();

    const REQ = place<string>('REQ');
    const RESP = place<string>('RESP');

    const net = PetriNet.builder('h')
      .place(REQ)
      .place(RESP)
      .compose(def.instantiate('probe').bindActions({ call }), (b) =>
        b.bindPort('in', REQ).bindPort('out', RESP),
      )
      .build();

    // The bound transition still reports the ACTUAL composed places — the alias
    // is preserved without leaking declared places into the structure.
    const composed = [...net.transitions].find((t) => t.name === 'probe/call')!;
    const inNames = new Set([...composed.inputPlaces()].map((p) => p.name));
    const outNames = new Set([...composed.outputPlaces()].map((p) => p.name));
    expect(inNames.has('REQ')).toBe(true);
    expect(outNames.has('RESP')).toBe(true);
    expect(inNames.has('reqDecl')).toBe(false);
    expect(outNames.has('respDecl')).toBe(false);

    const executor = new BitmapNetExecutor(net, seed(REQ, 'x'));
    const marking = await executor.run(2000);

    expect(marking.hasTokens(RESP)).toBe(true);
    expect(marking.peekFirst(RESP)?.value).toBe('x!');
  });

  it('XOR branch selection by declared constant (AC#2)', async () => {
    const inDecl = place<string>('inDecl');
    const aDecl = place<string>('aDecl');
    const bDecl = place<string>('bDecl');

    const branch: TransitionAction = async (ctx) => {
      ctx.output(aDecl, 'via-a:' + ctx.input(inDecl));
    };
    const route = Transition.builder('route')
      .inputs(one(inDecl))
      .outputs(xorPlaces(aDecl, bDecl))
      .action(branch)
      .build();
    const def = SubnetDef.builder('Router')
      .transition(route)
      .inputPort('in', inDecl)
      .outputPort('a', aDecl)
      .outputPort('b', bDecl)
      .build();

    const REQ = place<string>('REQ');
    const A = place<string>('A');
    const B = place<string>('B');

    const net = PetriNet.builder('h')
      .place(REQ)
      .place(A)
      .place(B)
      .compose(def.instantiate('r'), (b) => b.bindPort('in', REQ).bindPort('a', A).bindPort('b', B))
      .build();

    const executor = new BitmapNetExecutor(net, seed(REQ, 'go'));
    const marking = await executor.run(2000);

    expect(marking.tokenCount(A)).toBe(1);
    expect(marking.tokenCount(B)).toBe(0);
    expect(marking.peekFirst(A)?.value).toBe('via-a:go');
  });

  it('nested instance resolves doubly-prefixed place (AC#3, MOD-013)', async () => {
    const reqDecl = place<string>('reqDecl');
    const xDecl = place<string>('xDecl');

    const emit: TransitionAction = async (ctx) => {
      ctx.output(xDecl, ctx.input(reqDecl));
    };
    const tEmit = Transition.builder('emit')
      .inputs(one(reqDecl))
      .outputs(outPlace(xDecl))
      .action(emit)
      .build();
    const innerDef = SubnetDef.builder('Inner')
      .place(xDecl)
      .transition(tEmit)
      .inputPort('in', reqDecl)
      .build();

    // Compose inner (prefix "inner") into a body net exposing sIn as the bound input.
    const sIn = place<string>('sIn');
    const sBody = PetriNet.builder('Sbody')
      .place(sIn)
      .compose(innerDef.instantiate('inner'), (b) => b.bindPort('in', sIn))
      .build();

    // Retrofit the composed body as a subnet S, re-exposing sIn as port "sin".
    const sDef = SubnetDef.fromNet(sBody, Interface.builder().inputPort('sin', sIn).build());

    // Instantiate S as "outer" and compose into the host, binding sin -> hostReq.
    const hostReq = place<string>('hostReq');
    const host = PetriNet.builder('host')
      .place(hostReq)
      .compose(sDef.instantiate('outer'), (b) => b.bindPort('sin', hostReq))
      .build();

    const doublyPrefixed = [...host.places].find((p) => p.name === 'outer/inner/xDecl') as
      | Place<string>
      | undefined;
    expect(doublyPrefixed).not.toBeUndefined();

    const executor = new BitmapNetExecutor(host, seed(hostReq, 'deep'));
    const marking = await executor.run(2000);

    expect(marking.hasTokens(doublyPrefixed!)).toBe(true);
    expect(marking.peekFirst(doublyPrefixed!)?.value).toBe('deep');
  });

  it('hand-written and flat-net transitions carry identity (empty) alias (AC#4, MOD-025)', () => {
    const a = place<string>('a');
    const b = place<string>('b');
    const t = Transition.builder('t').inputs(one(a)).outputs(outPlace(b)).build();
    expect(t.placeAlias.size).toBe(0);

    const net = PetriNet.builder('flat').transition(t).build();
    for (const tr of net.transitions) {
      expect(tr.placeAlias.size).toBe(0);
    }
  });

  it('composed net is structurally equal to the hand-written flat net; alias is off-structure (AC#6, MOD-023)', () => {
    const reqDecl = place<string>('reqDecl');
    const respDecl = place<string>('respDecl');

    const call: TransitionAction = async (ctx) => {
      ctx.output(respDecl, ctx.input(reqDecl) + '!');
    };
    const step = Transition.builder('call')
      .inputs(one(reqDecl))
      .outputs(outPlace(respDecl))
      .action(call)
      .build();
    const def = SubnetDef.builder('Step')
      .transition(step)
      .inputPort('in', reqDecl)
      .outputPort('out', respDecl)
      .build();

    const REQ = place<string>('REQ');
    const RESP = place<string>('RESP');

    const composed = PetriNet.builder('h')
      .place(REQ)
      .place(RESP)
      .compose(def.instantiate('probe'), (b) => b.bindPort('in', REQ).bindPort('out', RESP))
      .build();

    // Equivalent hand-written flat net: same places, same 'probe/call' transition,
    // same REQ -> RESP arc topology, no action.
    const handWritten = PetriNet.builder('h')
      .place(REQ)
      .place(RESP)
      .transition(Transition.builder('probe/call').inputs(one(REQ)).outputs(outPlace(RESP)).build())
      .build();

    // Structural equivalence per MOD-023: place names, transition names, arc topology.
    const placeNames = (n: PetriNet): Set<string> => new Set([...n.places].map((p) => p.name));
    const tNames = (n: PetriNet): Set<string> => new Set([...n.transitions].map((t) => t.name));
    expect(placeNames(composed)).toEqual(placeNames(handWritten));
    expect(tNames(composed)).toEqual(tNames(handWritten));

    const composedT = [...composed.transitions].find((t) => t.name === 'probe/call')!;
    const handT = [...handWritten.transitions].find((t) => t.name === 'probe/call')!;
    const inNames = (t: Transition): Set<string> => new Set([...t.inputPlaces()].map((p) => p.name));
    const outNames = (t: Transition): Set<string> =>
      new Set([...t.outputPlaces()].map((p) => p.name));
    expect(inNames(composedT)).toEqual(inNames(handT));
    expect(outNames(composedT)).toEqual(outNames(handT));

    // ...yet the correspondence is OFF-structure: composed carries exactly the
    // name-keyed declared->actual alias, the hand-written one is empty.
    expect(composedT.placeAlias).toEqual(
      new Map([
        ['reqDecl', REQ],
        ['respDecl', RESP],
      ]),
    );
    expect(handT.placeAlias.size).toBe(0);
  });
});
