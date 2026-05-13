import { describe, it, expect } from 'vitest';
import { place } from '../../src/core/place.js';
import type { Place } from '../../src/core/place.js';
import { Transition } from '../../src/core/transition.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { SubnetDef } from '../../src/core/subnet-def.js';
import { ComposeBindings } from '../../src/core/compose-bindings.js';
import { one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import type { In } from '../../src/core/in.js';
import { BitmapNetExecutor } from '../../src/runtime/bitmap-net-executor.js';
import { tokenOf } from '../../src/core/token.js';
import type { Token } from '../../src/core/token.js';
import { producer, boundedBuffer, consumer, retryPolicy } from '../fixtures/subnet-fixtures.js';
import { fork, transform } from '../../src/core/transition-action.js';

/**
 * Integration tests for {@link PetriNetBuilder.compose}, per
 * `spec/11-modular-composition.md` requirements **MOD-020** (composition
 * operation), **MOD-022** (type compatibility), and **MOD-023** (composition
 * produces a flat net).
 *
 * Channel composition (MOD-021) end-to-end behaviour lives in
 * `channel-composition.test.ts`; this file covers a single smoke test that
 * `compose(...)` accepts and applies a channel binding.
 */

interface Item {
  readonly tag: string;
}

function tokensOf(...values: string[]): Token<string>[] {
  return values.map(tokenOf);
}

describe('PetriNetBuilder.compose — port composition (MOD-020, MOD-022, MOD-023)', () => {

  // ============================================================
  //  MOD-020: single port -> caller place merge by structural rewrite
  // ============================================================

  it('compose_singlePort_mergesPlace: arc references the caller place by reference', () => {
    const def = producer();
    const inst = def.instantiate('p1');

    const buffer = place<string>('buffer');
    const built = PetriNet.builder('host')
      .compose(inst, { output: buffer as Place<unknown> })
      .build();

    // Find the rewritten 'p1/produce' transition; its output arc must point
    // at the caller's `buffer` place by reference, not at 'p1/output'.
    let foundProduce: Transition | null = null;
    for (const t of built.transitions) {
      if (t.name === 'p1/produce') {
        foundProduce = t;
        break;
      }
    }
    expect(foundProduce).not.toBeNull();
    expect(foundProduce!.outputSpec).not.toBeNull();
    expect(foundProduce!.outputSpec!.type).toBe('place');
    const outPlaceSpec = foundProduce!.outputSpec! as { type: 'place'; place: Place<unknown> };
    // Reference equality: the rewritten arc points at caller's buffer.
    expect(outPlaceSpec.place).toBe(buffer);

    // The instance-side renamed `p1/output` place is gone from the host net
    // because the only arc that referenced it has been rewritten — but
    // wait: the renamed body declared `p1/output` as a structural place
    // (renameNet preserves stranded places). The rewriter only touches arc
    // place references; the host builder collects places from arcs. Since
    // we never explicitly added 'p1/output', and the only arc that mentioned
    // it has been rewritten, 'p1/output' must NOT be in the built net.
    const placeNames = new Set([...built.places].map((p) => p.name));
    expect(placeNames.has('p1/output')).toBe(false);
    expect(placeNames.has('buffer')).toBe(true);
    // Internal place 'p1/nextItem' flows through unchanged.
    expect(placeNames.has('p1/nextItem')).toBe(true);
  });

  // ============================================================
  //  MOD-022: type compatibility — TS compile-time only enforcement
  // ============================================================

  it('compose_typeMismatch_compileTimeOnly: typed bindPort signature rejects wrong types at compile time', () => {
    // TypeScript erases generics at runtime, so MOD-022 enforcement in TS
    // is a compile-time-only contract per spec note: "In languages without
    // runtime generic reification (TypeScript), enforcement is compile-time
    // only via the static type system; runtime per-token-type tagging is
    // not required."
    //
    // The following lines exercise the typed `bindPort<T>` signature. The
    // first line compiles (correct types). The second line is annotated
    // with `// @ts-expect-error` to verify TypeScript rejects it.
    const def = producer();
    const inst = def.instantiate('p1');

    const correctBuffer = place<string>('buffer');
    const wrongBuffer = place<number>('wrongBuffer');

    // Sanity check: typed bindings accept correctly typed places.
    PetriNet.builder('ok')
      .compose(inst, (b) => b.bindPort<string>('output', correctBuffer))
      .build();

    // The cast escape-hatch path: at runtime, mismatched types are NOT
    // detected (per MOD-022 ¶2). This is documented behaviour — callers who
    // bypass the typed signature via `as` casts assume responsibility.
    expect(() => {
      PetriNet.builder('runtime-cast')
        .compose(inst, (b) =>
          b.bindPort<string>('output', wrongBuffer as unknown as Place<string>),
        )
        .build();
    }).not.toThrow();

    // Compile-time-only contract: the following triggers a tsc error
    // exactly because TS narrows the second argument to `Place<string>`.
    PetriNet.builder('compile-time-check')
      // @ts-expect-error — Place<number> is not assignable to Place<string>
      .compose(inst, (b) => b.bindPort<string>('output', wrongBuffer))
      .build();
  });

  // ============================================================
  //  Validation: unknown port name throws
  // ============================================================

  it('compose_unknownPortName_throws: helpful error names the bad port and lists known ports', () => {
    const def = producer();
    const inst = def.instantiate('p1');
    const someplace = place<string>('someplace');

    expect(() =>
      PetriNet.builder('host').compose(inst, {
        nonexistent: someplace as Place<unknown>,
      }),
    ).toThrow(/no port named 'nonexistent'/);

    expect(() =>
      PetriNet.builder('host').compose(inst, {
        nonexistent: someplace as Place<unknown>,
      }),
    ).toThrow(/Producer/);
  });

  // ============================================================
  //  MOD-012 / MOD-020: per-instance state isolation
  // ============================================================

  it('compose_internalPlacesGetTheirOwnSlot: two instances of same subnet have disjoint internal places', () => {
    const def = producer();
    const a = def.instantiate('a');
    const b = def.instantiate('b');

    const buffer = place<string>('buffer');
    const built = PetriNet.builder('host')
      .compose(a, { output: buffer as Place<unknown> })
      .compose(b, { output: buffer as Place<unknown> })
      .build();

    const placeNames = new Set([...built.places].map((p) => p.name));
    // Both internal places get distinct prefixed slots.
    expect(placeNames.has('a/nextItem')).toBe(true);
    expect(placeNames.has('b/nextItem')).toBe(true);
    // The shared port maps to one caller place.
    expect(placeNames.has('buffer')).toBe(true);
    // Renamed port places are gone.
    expect(placeNames.has('a/output')).toBe(false);
    expect(placeNames.has('b/output')).toBe(false);

    // Both 'a/produce' and 'b/produce' transitions exist and are distinct.
    const tNames = new Set([...built.transitions].map((t) => t.name));
    expect(tNames.has('a/produce')).toBe(true);
    expect(tNames.has('b/produce')).toBe(true);
  });

  // ============================================================
  //  Channel binding smoke test (MOD-021 — full coverage in
  //  channel-composition.test.ts)
  // ============================================================

  it('compose_channelBinding_mergesIntoCallerTransition: caller-named transition survives, renamed channel transition merges away', () => {
    const def = retryPolicy();
    const inst = def.instantiate('rp1');

    const callerT = Transition.builder('callerSide').build();

    const built = PetriNet.builder('host')
      .compose(inst, (b) => b.bindChannel('attempt', callerT))
      .build();

    const tNames = new Set([...built.transitions].map((t) => t.name));
    expect(tNames.has('callerSide')).toBe(true);
    expect(tNames.has('rp1/attempt')).toBe(false);
  });

  it('compose_unknownChannel_throws: helpful error names the bad channel and lists known channels', () => {
    const def = retryPolicy();
    const inst = def.instantiate('rp1');
    const callerT = Transition.builder('callerSide').build();

    expect(() =>
      PetriNet.builder('host').compose(inst, (b) => b.bindChannel('nonexistent', callerT)),
    ).toThrow(/no channel named 'nonexistent'/);

    expect(() =>
      PetriNet.builder('host').compose(inst, (b) => b.bindChannel('nonexistent', callerT)),
    ).toThrow(/RetryPolicy/);
  });

  // ============================================================
  //  Typed callback overload — multiple bindings, fluent
  // ============================================================

  it('compose_typedBindingsForm: multiple typed port bindings via the callback overload', () => {
    // A subnet with two typed ports of different types; ensure both bind
    // through the typed `bindPort<T>` API.
    const inputP = place<string>('in');
    const outputP = place<number>('out');
    const t = Transition.builder('forward')
      .inputs(one(inputP))
      .outputs(outPlace(outputP))
      .build();
    const def = SubnetDef.builder('TwoPort')
      .transition(t)
      .inputPort('in', inputP)
      .outputPort('out', outputP)
      .build();
    const inst = def.instantiate('tp1');

    const callerIn = place<string>('callerIn');
    const callerOut = place<number>('callerOut');

    const built = PetriNet.builder('host')
      .compose(inst, (b) =>
        b
          .bindPort<string>('in', callerIn)
          .bindPort<number>('out', callerOut),
      )
      .build();

    // Find the rewritten transition; both arcs should refer to caller-side
    // places by reference.
    let forward: Transition | null = null;
    for (const tr of built.transitions) {
      if (tr.name === 'tp1/forward') {
        forward = tr;
        break;
      }
    }
    expect(forward).not.toBeNull();
    expect((forward!.inputSpecs[0] as Extract<In, { type: 'one' }>).place).toBe(callerIn);
    const outSpec = forward!.outputSpec! as { type: 'place'; place: Place<unknown> };
    expect(outSpec.place).toBe(callerOut);
  });

  // ============================================================
  //  ComposeBindings construction is symbol-guarded
  // ============================================================

  it('ComposeBindings is not directly constructible without the internal symbol', () => {
    expect(() => new ComposeBindings(Symbol('wrong'))).toThrow(/PetriNetBuilder.compose/);
  });

  // ============================================================
  //  MOD-023: end-to-end through the executor
  // ============================================================

  it('compose_producerBufferConsumer_endToEnd: tokens flow producer -> buffer -> consumer', async () => {
    const prodDef = producer();
    const bufDef = boundedBuffer(2);
    const consDef = consumer();

    // Bind actions: action-less control-flow fixtures need a TS transition
    // action that copies the consumed input token to every declared output
    // place (the TS executor does not auto-forward — it strictly validates
    // against the declared `outputs(...)` spec). For the dequeue transition
    // (which has an AND output split: get + slots), we copy the consumed
    // item's value to both output places.
    const prod = prodDef.instantiate('prod').bindActions({ produce: fork() });
    const buf = bufDef
      .instantiate('buf')
      .bindActions({
        // enqueue consumes (put, slots) and emits to internal `items`. We
        // emit the value of the put-side token; the `slots` token is just
        // capacity bookkeeping.
        enqueue: transform((ctx) => {
          const putPlace = [...ctx.inputPlaces()].find((p) => p.name.endsWith('/put'))
            ?? [...ctx.inputPlaces()].find((p) => !p.name.endsWith('/slots'))!;
          return ctx.input(putPlace);
        }),
        // dequeue consumes from items and emits to both `get` and `slots`.
        // The transform action copies the same value to every output place,
        // which is fine here because the `slots` token's value doesn't
        // matter for capacity tracking.
        dequeue: transform((ctx) => {
          const itemsPlace = [...ctx.inputPlaces()].find((p) => p.name.endsWith('/items'))!;
          return ctx.input(itemsPlace);
        }),
      });
    const cons = consDef.instantiate('cons').bindActions({ consume: fork() });

    // Wiring places: producer output -> buffer.put; buffer.get -> consumer input.
    const producerToBuffer = place<string>('producerToBuffer');
    const bufferToConsumer = place<string>('bufferToConsumer');

    const net = PetriNet.builder('pipeline')
      .compose(prod, (b) => b.bindPort<string>('output', producerToBuffer))
      .compose(buf, (b) =>
        b
          .bindPort<string>('put', producerToBuffer)
          .bindPort<string>('get', bufferToConsumer),
      )
      .compose(cons, (b) => b.bindPort<string>('input', bufferToConsumer))
      .build();

    // Initial marking: seed producer's nextItem with one token, buffer's
    // slots with capacity tokens. The producer transitions consume from
    // 'prod/nextItem' (renamed) and emit through producerToBuffer.
    const prodNextItem = [...net.places].find((p) => p.name === 'prod/nextItem')!;
    const bufSlots = [...net.places].find((p) => p.name === 'buf/slots')!;
    const consConsumed = [...net.places].find((p) => p.name === 'cons/consumed')!;

    const initial = new Map<Place<unknown>, Token<unknown>[]>();
    initial.set(prodNextItem, tokensOf('payload') as Token<unknown>[]);
    initial.set(bufSlots, tokensOf('slot1', 'slot2') as Token<unknown>[]);

    const executor = new BitmapNetExecutor(net, initial as Map<Place<any>, Token<any>[]>);
    const finalMarking = await executor.run(2000);

    // The single producer token has flowed all the way to consumer's sink.
    expect(finalMarking.tokenCount(consConsumed)).toBe(1);
    expect(finalMarking.peekFirst(consConsumed)!.value).toBe('payload');

    // Producer's nextItem has been drained.
    expect(finalMarking.tokenCount(prodNextItem)).toBe(0);
  });

  it('compose_twoProducerInstances_perInstanceState: two producers feed the same buffer', async () => {
    const prodDef = producer();
    const bufDef = boundedBuffer(2);
    const consDef = consumer();

    const p1 = prodDef.instantiate('p1').bindActions({ produce: fork() });
    const p2 = prodDef.instantiate('p2').bindActions({ produce: fork() });
    const buf = bufDef
      .instantiate('buf')
      .bindActions({
        enqueue: transform((ctx) => {
          const putPlace = [...ctx.inputPlaces()].find((p) => !p.name.endsWith('/slots'))!;
          return ctx.input(putPlace);
        }),
        dequeue: transform((ctx) => {
          const itemsPlace = [...ctx.inputPlaces()].find((p) => p.name.endsWith('/items'))!;
          return ctx.input(itemsPlace);
        }),
      });
    const cons = consDef.instantiate('cons').bindActions({ consume: fork() });

    const producerToBuffer = place<string>('producerToBuffer');
    const bufferToConsumer = place<string>('bufferToConsumer');

    const net = PetriNet.builder('pipeline')
      .compose(p1, (b) => b.bindPort<string>('output', producerToBuffer))
      .compose(p2, (b) => b.bindPort<string>('output', producerToBuffer))
      .compose(buf, (b) =>
        b
          .bindPort<string>('put', producerToBuffer)
          .bindPort<string>('get', bufferToConsumer),
      )
      .compose(cons, (b) => b.bindPort<string>('input', bufferToConsumer))
      .build();

    // Seed each producer with a distinct token to verify per-instance state.
    const p1NextItem = [...net.places].find((p) => p.name === 'p1/nextItem')!;
    const p2NextItem = [...net.places].find((p) => p.name === 'p2/nextItem')!;
    const bufSlots = [...net.places].find((p) => p.name === 'buf/slots')!;
    const consConsumed = [...net.places].find((p) => p.name === 'cons/consumed')!;

    // Sanity: both producers have distinct internal places.
    expect(p1NextItem).not.toBe(p2NextItem);

    const initial = new Map<Place<unknown>, Token<unknown>[]>();
    initial.set(p1NextItem, tokensOf('one') as Token<unknown>[]);
    initial.set(p2NextItem, tokensOf('two') as Token<unknown>[]);
    initial.set(bufSlots, tokensOf('slot1', 'slot2') as Token<unknown>[]);

    const executor = new BitmapNetExecutor(net, initial as Map<Place<any>, Token<any>[]>);
    const finalMarking = await executor.run(2000);

    // Both tokens reached the consumer (FIFO order in the consumer's sink).
    expect(finalMarking.tokenCount(consConsumed)).toBe(2);
    const observedValues = new Set<string>();
    // Drain by removing one at a time (peekFirst doesn't expose all values).
    // We inspect via the consumed place's tokens through removeAll.
    const drained = finalMarking.removeAll<string>(consConsumed);
    for (const t of drained) observedValues.add(t.value);
    expect(observedValues).toEqual(new Set(['one', 'two']));

    // Both producers have drained; both internal places are empty.
    expect(finalMarking.tokenCount(p1NextItem)).toBe(0);
    expect(finalMarking.tokenCount(p2NextItem)).toBe(0);
  });

  // ============================================================
  //  Map vs Record overloads — both work
  // ============================================================

  it('Map overload accepts a runtime Map<string, Place<unknown>>', () => {
    const def = producer();
    const inst = def.instantiate('p1');
    const buffer = place<string>('buffer');

    const portMap = new Map<string, Place<unknown>>([
      ['output', buffer as Place<unknown>],
    ]);
    const built = PetriNet.builder('host').compose(inst, portMap).build();

    const placeNames = new Set([...built.places].map((p) => p.name));
    expect(placeNames.has('buffer')).toBe(true);
    expect(placeNames.has('p1/output')).toBe(false);
  });
});
