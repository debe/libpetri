import { describe, it, expect } from 'vitest';
import { place } from '../../src/core/place.js';
import type { Place } from '../../src/core/place.js';
import { Transition } from '../../src/core/transition.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { SubnetDef } from '../../src/core/subnet-def.js';
import { Interface } from '../../src/core/interface.js';
import { FusionSet } from '../../src/core/fusion-set.js';
import { one } from '../../src/core/in.js';
import { forwardInput, outPlace, timeout, timeoutPlace, xor, xorPlaces } from '../../src/core/out.js';
import { BitmapNetExecutor } from '../../src/runtime/bitmap-net-executor.js';
import { PrecompiledNetExecutor } from '../../src/runtime/precompiled-net-executor.js';
import { InMemoryEventStore, eventsOfType } from '../../src/event/event-store.js';
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
  it('multi-pass rewrite keeps a declared place whose name round-trips unchanged (MOD-031 regression)', async () => {
    // The chained path never walks arcs — it can only carry forward what the
    // previous pass recorded. So a declared place that happens to map to its own
    // name on pass 1 must still get an entry, or pass 2 has nothing to rename
    // and the action's hardcoded constant resolves to a place that no longer
    // exists in the composed net.
    const aDecl = place<string>('aDecl'); // exposed as an input port
    const bDecl = place<string>('bDecl'); // internal — always gets prefixed
    const outDecl = place<string>('outDecl'); // internal — always gets prefixed

    const join: TransitionAction = async (ctx) => {
      ctx.output(outDecl, ctx.input(aDecl) + '+' + ctx.input(bDecl));
    };
    const t = Transition.builder('join')
      .inputs(one(aDecl), one(bDecl))
      .outputs(outPlace(outDecl))
      .action(join)
      .build();
    const innerDef = SubnetDef.builder('Inner')
      .place(bDecl)
      .place(outDecl)
      .transition(t)
      .inputPort('a', aDecl)
      .build();

    // Pass 1 — bind port 'a' to a host place named EXACTLY like the declared
    // place. 'aDecl' round-trips to itself here; 'bDecl'/'outDecl' do not, so
    // the alias is mixed and survives the all-identity wholesale drop.
    const hostA = place<string>('aDecl');
    const mid = PetriNet.builder('mid')
      .place(hostA)
      .compose(innerDef.instantiate('inst'), (b) => b.bindPort('a', hostA))
      .build();

    // Pass 2 — retrofit that composed body as a subnet, re-expose hostA, and
    // bind it to a differently-named host place.
    const midDef = SubnetDef.fromNet(mid, Interface.builder().inputPort('a2', hostA).build());
    const hostReq = place<string>('hostReq');
    const host = PetriNet.builder('host')
      .place(hostReq)
      .compose(midDef.instantiate('outer'), (b) => b.bindPort('a2', hostReq))
      .build();

    const finalB = [...host.places].find((p) => p.name === 'outer/inst/bDecl') as
      | Place<string>
      | undefined;
    const finalOut = [...host.places].find((p) => p.name === 'outer/inst/outDecl') as
      | Place<string>
      | undefined;
    expect(finalB).not.toBeUndefined();
    expect(finalOut).not.toBeUndefined();

    const initial = new Map<Place<unknown>, Token<unknown>[]>();
    initial.set(hostReq as Place<unknown>, [tokenOf('A')] as Token<unknown>[]);
    initial.set(finalB! as Place<unknown>, [tokenOf('B')] as Token<unknown>[]);

    const executor = new BitmapNetExecutor(host, initial as Map<Place<any>, Token<any>[]>);
    const marking = await executor.run(2000);

    // Before the fix: the transition enabled, started, consumed both inputs,
    // then threw `Place 'aDecl' not in declared inputs`. Under EXEC-031 (no
    // rollback) the tokens were simply gone — silent loss, not a build error.
    expect(marking.hasTokens(finalOut!)).toBe(true);
    expect(marking.peekFirst(finalOut!)?.value).toBe('A+B');
    expect(marking.tokenCount(hostReq)).toBe(0);
  });

  it('channel merge then fusion: caller action resolves its declared place (MOD-031 key-set completeness)', async () => {
    // RD-23: the caller `call` carries no correspondence; the instance's channel transition
    // carries one. The merge must still give every place the caller names a key, or the later
    // fusion pass (h -> f) leaves `h` unresolved and the action throws after consuming inputs.
    const x = place<string>('x');
    const done = place<string>('done');
    const serve = Transition.builder('serve')
      .inputs(one(x))
      .outputs(outPlace(done))
      .build();
    const def = SubnetDef.builder('Svc')
      .place(done)
      .transition(serve)
      .inputPort('x', x)
      .channel('serve', serve)
      .build();
    const inst = def.instantiate('s').bindActions({
      serve: async (ctx) => {
        ctx.output(done, ctx.input(x));
      },
    });

    const h = place<string>('h');
    const f = place<string>('f');
    const hx = place<string>('hx');
    const out = place<string>('out');
    const call = Transition.builder('call')
      .inputs(one(h))
      .outputs(outPlace(out))
      .action(async (ctx) => {
        ctx.output(out, ctx.input(h) + '!');
      })
      .build();

    const net = PetriNet.builder('host')
      .place(f)
      .place(h)
      .place(hx)
      .place(out)
      .compose(inst, (b) => b.bindPort('x', hx).bindChannel('serve', call))
      .fuse(FusionSet.of('F', f, h))
      .build();

    const merged = [...net.transitions].find((t) => t.name === 'call')!;
    expect(merged.placeAlias.get('h')?.name).toBe('f');
    expect(merged.placeAlias.get('x')?.name).toBe('hx');

    const initial = new Map<Place<unknown>, Token<unknown>[]>();
    initial.set(f as Place<unknown>, [tokenOf('F')] as Token<unknown>[]);
    initial.set(hx as Place<unknown>, [tokenOf('X')] as Token<unknown>[]);
    const store = new InMemoryEventStore();
    const marking = await new BitmapNetExecutor(net, initial as Map<Place<any>, Token<any>[]>, {
      eventStore: store,
    }).run(2000);

    expect(eventsOfType(store, 'transition-failed')).toHaveLength(0);
    expect(marking.peekFirst(out)?.value).toBe('F!');
    const sDone = [...net.places].find((p) => p.name === 's/done') as Place<string>;
    expect(marking.peekFirst(sDone)?.value).toBe('X');
  });

  // The timeout outcome is deposited on the places of the rewritten output spec, which are
  // already the actual places: the correspondence is applied once, to a declared place, and
  // never again in firing (MOD-031, IO-013, IO-014, CORE-036). Under a port-name collision
  // (declared `a` bound to the caller's `b`, declared `b` bound to `c`) a second resolution
  // would move the timeout token meant for `b` onto `c`.
  for (const backend of ['BitmapNetExecutor', 'PrecompiledNetExecutor'] as const) {
    const run = async (net: PetriNet, initial: Map<Place<any>, Token<any>[]>, store: InMemoryEventStore) =>
      (backend === 'BitmapNetExecutor'
        ? new BitmapNetExecutor(net, initial, { eventStore: store })
        : new PrecompiledNetExecutor(net, initial, { eventStore: store })
      ).run(2000);
    const never: TransitionAction = () => new Promise<void>(() => {});

    it(`the timeout branch deposits on the bound place under a port-name collision (MOD-031, IO-013, ${backend})`, async () => {
      const job = place<string>('job');
      const a = place<string>('a');
      const b = place<string>('b');
      const work = Transition.builder('work')
        .inputs(one(job))
        .outputs(xor(outPlace(b), timeoutPlace(30, a)))
        .action(never)
        .build();
      const def = SubnetDef.builder('Work')
        .transition(work)
        .inputPort('job', job)
        .outputPort('a', a)
        .outputPort('b', b)
        .build();

      const hostJob = place<string>('hostJob');
      const hostB = place<string>('b');
      const hostC = place<string>('c');
      const net = PetriNet.builder('h')
        .place(hostJob).place(hostB).place(hostC)
        .compose(def.instantiate('w'), (bb) =>
          bb.bindPort('job', hostJob).bindPort('a', hostB).bindPort('b', hostC))
        .build();

      const store = new InMemoryEventStore();
      const marking = await run(net, seed(hostJob, 'j'), store);

      expect(eventsOfType(store, 'action-timed-out')).toHaveLength(1);
      expect(eventsOfType(store, 'transition-failed')).toHaveLength(0);
      expect(marking.tokenCount(hostB)).toBe(1);
      expect(marking.tokenCount(hostC)).toBe(0);
    });

    it(`a timeout ForwardInput reads and deposits on the actual places under a collision (MOD-031, IO-014, ${backend})`, async () => {
      // Declared `job` is bound to the caller's `a`, declared `a` to `b`, declared `b` to `c`:
      // resolving the rewritten `from` (actual `a`) again names `b`, which is no input.
      const job = place<string>('job');
      const a = place<string>('a');
      const b = place<string>('b');
      const work = Transition.builder('work')
        .inputs(one(job))
        .outputs(xor(outPlace(b), timeout(30, forwardInput(job, a))))
        .action(never)
        .build();
      const def = SubnetDef.builder('Work')
        .transition(work)
        .inputPort('job', job)
        .outputPort('a', a)
        .outputPort('b', b)
        .build();

      const hostA = place<string>('a');
      const hostB = place<string>('b');
      const hostC = place<string>('c');
      const net = PetriNet.builder('h')
        .place(hostA).place(hostB).place(hostC)
        .compose(def.instantiate('w'), (bb) =>
          bb.bindPort('job', hostA).bindPort('a', hostB).bindPort('b', hostC))
        .build();

      const store = new InMemoryEventStore();
      const marking = await run(net, seed(hostA, 'j'), store);

      expect(eventsOfType(store, 'action-timed-out')).toHaveLength(1);
      expect(eventsOfType(store, 'transition-failed')).toHaveLength(0);
      expect(marking.tokenCount(hostA)).toBe(0);
      expect(marking.peekTokens(hostB).map((tok) => tok.value)).toEqual(['j']);
      expect(marking.tokenCount(hostC)).toBe(0);
    });
  }
});
