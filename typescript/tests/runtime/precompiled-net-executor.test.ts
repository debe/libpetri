import { describe, it, expect } from 'vitest';
import { PrecompiledNetExecutor } from '../../src/runtime/precompiled-net-executor.js';
import { Marking } from '../../src/runtime/marking.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place, environmentPlace } from '../../src/core/place.js';
import type { Place, EnvironmentPlace } from '../../src/core/place.js';
import { one, exactly, all, atLeast } from '../../src/core/in.js';
import { outPlace, andPlaces, xor, xorPlaces, timeout, timeoutPlace, forwardInput, and } from '../../src/core/out.js';
import { immediate, delayed, exact, window, deadline } from '../../src/core/timing.js';
import { tokenOf, unitToken } from '../../src/core/token.js';
import type { Token } from '../../src/core/token.js';
import type { TransitionAction } from '../../src/core/transition-action.js';
import { InMemoryEventStore, noopEventStore, eventsOfType, failures } from '../../src/event/event-store.js';
import type { TransitionFailed, TransitionTimedOut, MarkingSnapshot } from '../../src/event/net-event.js';

// ======================== Test Helpers ========================

function initialTokens(...entries: [Place<any>, Token<any>[]][]): Map<Place<any>, Token<any>[]> {
  return new Map(entries);
}

async function runNet(
  net: PetriNet,
  tokens: Map<Place<any>, Token<any>[]>,
  options?: { eventStore?: InMemoryEventStore; environmentPlaces?: Set<EnvironmentPlace<any>> },
): Promise<{ marking: Marking; executor: PrecompiledNetExecutor }> {
  const executor = new PrecompiledNetExecutor(net, tokens, options);
  const marking = await executor.run(5000);
  return { marking, executor };
}

function sleep(ms: number): Promise<void> {
  return new Promise(resolve => setTimeout(resolve, ms));
}

// ======================== INPUT ARC TESTS ========================

describe('Input Arc Tests', () => {
  it('basic input arc consumes token when transition fires', async () => {
    const input = place<string>('IN');
    const output = place<string>('OUT');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .action(async (ctx) => {
        ctx.output(output, ctx.input(input));
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const { marking } = await runNet(net, initialTokens([input, [tokenOf('hello')]]));

    expect(marking.hasTokens(input)).toBe(false);
    expect(marking.hasTokens(output)).toBe(true);
    expect(marking.peekFirst(output)!.value).toBe('hello');
  });

  it('input arc requires token to enable', async () => {
    const input = place<string>('IN');
    const output = place<string>('OUT');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .action(async (ctx) => { ctx.output(output, 'result'); })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const { marking } = await runNet(net, initialTokens());

    expect(marking.hasTokens(output)).toBe(false);
  });

  it('multiple input arcs require all tokens', async () => {
    const pA = place<number>('A');
    const pB = place<number>('B');
    const output = place<number>('OUT');
    const t = Transition.builder('T')
      .inputs(one(pA), one(pB))
      .outputs(outPlace(output))
      .action(async (ctx) => {
        ctx.output(output, ctx.input(pA) + ctx.input(pB));
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();

    // Only A → should not fire
    const { marking: m1 } = await runNet(net, initialTokens([pA, [tokenOf(10)]]));
    expect(m1.hasTokens(output)).toBe(false);

    // Both A and B → fires
    const { marking: m2 } = await runNet(net, initialTokens([pA, [tokenOf(10)]], [pB, [tokenOf(20)]]));
    expect(m2.hasTokens(output)).toBe(true);
    expect(m2.peekFirst(output)!.value).toBe(30);
  });

  it('input arc FIFO ordering', async () => {
    const input = place<number>('IN');
    const output = place<number>('OUT');
    const consumed: number[] = [];
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .action(async (ctx) => {
        const v = ctx.input(input);
        consumed.push(v);
        ctx.output(output, v);
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    await runNet(net, initialTokens([input, [tokenOf(1), tokenOf(2), tokenOf(3)]]));

    expect(consumed).toEqual([1, 2, 3]);
  });
});

// ======================== OUTPUT ARC TESTS ========================

describe('Output Arc Tests', () => {
  it('basic output arc produces token', async () => {
    const input = place<string>('IN');
    const output = place<string>('OUT');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .action(async (ctx) => { ctx.output(output, 'produced'); })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const { marking } = await runNet(net, initialTokens([input, [tokenOf('trigger')]]));

    expect(marking.peekFirst(output)!.value).toBe('produced');
  });

  it('multiple output arcs produce to all places', async () => {
    const input = place<string>('IN');
    const outA = place<string>('A');
    const outB = place<string>('B');
    const outC = place<string>('C');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(andPlaces(outA, outB, outC))
      .action(async (ctx) => {
        ctx.output(outA, 'a');
        ctx.output(outB, 'b');
        ctx.output(outC, 'c');
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const { marking } = await runNet(net, initialTokens([input, [tokenOf('trigger')]]));

    expect(marking.hasTokens(outA)).toBe(true);
    expect(marking.hasTokens(outB)).toBe(true);
    expect(marking.hasTokens(outC)).toBe(true);
  });

  it('multiple tokens to same place', async () => {
    const input = place<string>('IN');
    const output = place<number>('OUT');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .action(async (ctx) => {
        ctx.output(output, 1);
        ctx.output(output, 2);
        ctx.output(output, 3);
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const { marking } = await runNet(net, initialTokens([input, [tokenOf('trigger')]]));

    expect(marking.tokenCount(output)).toBe(3);
    expect(marking.peekTokens(output).map(t => t.value)).toEqual([1, 2, 3]);
  });
});

// ======================== INHIBITOR ARC TESTS ========================

describe('Inhibitor Arc Tests', () => {
  it('inhibitor arc blocks when place has tokens', async () => {
    const input = place<string>('IN');
    const output = place<string>('OUT');
    const blocker = place<string>('BLOCKER');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .inhibitor(blocker)
      .action(async (ctx) => { ctx.output(output, 'done'); })
      .build();
    const net = PetriNet.builder('N').transition(t).build();

    // With blocker: blocked
    const { marking: m1 } = await runNet(net, initialTokens(
      [input, [tokenOf('go')]],
      [blocker, [tokenOf('block')]],
    ));
    expect(m1.hasTokens(output)).toBe(false);
    expect(m1.hasTokens(input)).toBe(true);

    // Without blocker: fires
    const { marking: m2 } = await runNet(net, initialTokens([input, [tokenOf('go')]]));
    expect(m2.hasTokens(output)).toBe(true);
  });

  it('multiple inhibitors all must be empty', async () => {
    const input = place<string>('IN');
    const output = place<string>('OUT');
    const b1 = place<string>('B1');
    const b2 = place<string>('B2');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .inhibitors(b1, b2)
      .action(async (ctx) => { ctx.output(output, 'done'); })
      .build();
    const net = PetriNet.builder('N').transition(t).build();

    // Both blockers present
    const { marking: m1 } = await runNet(net, initialTokens(
      [input, [tokenOf('go')]],
      [b1, [tokenOf('x')]],
      [b2, [tokenOf('y')]],
    ));
    expect(m1.hasTokens(output)).toBe(false);

    // Only one blocker
    const { marking: m2 } = await runNet(net, initialTokens(
      [input, [tokenOf('go')]],
      [b1, [tokenOf('x')]],
    ));
    expect(m2.hasTokens(output)).toBe(false);

    // No blockers
    const { marking: m3 } = await runNet(net, initialTokens([input, [tokenOf('go')]]));
    expect(m3.hasTokens(output)).toBe(true);
  });

  it('inhibitor becomes unblocked when token removed', async () => {
    const input = place<string>('IN');
    const output = place<string>('OUT');
    const blocker = place<string>('BLOCKER');
    const cleared = place<string>('CLEARED');

    // clearBlocker has higher priority, consumes the blocker
    const clearBlocker = Transition.builder('ClearBlocker')
      .inputs(one(blocker))
      .outputs(outPlace(cleared))
      .priority(10)
      .action(async (ctx) => { ctx.output(cleared, 'ok'); })
      .build();

    const main = Transition.builder('Main')
      .inputs(one(input))
      .outputs(outPlace(output))
      .inhibitor(blocker)
      .action(async (ctx) => { ctx.output(output, 'done'); })
      .build();

    const net = PetriNet.builder('N').transitions(clearBlocker, main).build();
    const { marking } = await runNet(net, initialTokens(
      [input, [tokenOf('go')]],
      [blocker, [tokenOf('block')]],
    ));

    expect(marking.hasTokens(cleared)).toBe(true);
    expect(marking.hasTokens(output)).toBe(true);
  });
});

// ======================== READ ARC TESTS ========================

describe('Read Arc Tests', () => {
  it('read arc requires token but does not consume', async () => {
    const input = place<number>('IN');
    const output = place<number>('OUT');
    const config = place<number>('CONFIG');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .read(config)
      .action(async (ctx) => {
        ctx.output(output, ctx.input(input) + ctx.read(config));
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();

    // Without config: doesn't fire
    const { marking: m1 } = await runNet(net, initialTokens([input, [tokenOf(10)]]));
    expect(m1.hasTokens(output)).toBe(false);

    // With config: fires, config remains
    const { marking: m2 } = await runNet(net, initialTokens(
      [input, [tokenOf(10)]],
      [config, [tokenOf(5)]],
    ));
    expect(m2.hasTokens(output)).toBe(true);
    expect(m2.peekFirst(output)!.value).toBe(15);
    expect(m2.hasTokens(config)).toBe(true);
  });

  it('multiple transitions can read same place', async () => {
    const shared = place<string>('SHARED');
    const in1 = place<string>('IN1');
    const in2 = place<string>('IN2');
    const out1 = place<string>('OUT1');
    const out2 = place<string>('OUT2');

    const t1 = Transition.builder('T1')
      .inputs(one(in1)).outputs(outPlace(out1)).read(shared)
      .action(async (ctx) => { ctx.output(out1, ctx.read(shared)); })
      .build();
    const t2 = Transition.builder('T2')
      .inputs(one(in2)).outputs(outPlace(out2)).read(shared)
      .action(async (ctx) => { ctx.output(out2, ctx.read(shared)); })
      .build();

    const net = PetriNet.builder('N').transitions(t1, t2).build();
    const { marking } = await runNet(net, initialTokens(
      [in1, [tokenOf('a')]],
      [in2, [tokenOf('b')]],
      [shared, [tokenOf('config')]],
    ));

    expect(marking.hasTokens(out1)).toBe(true);
    expect(marking.hasTokens(out2)).toBe(true);
    expect(marking.hasTokens(shared)).toBe(true);
  });

  it('multiple read arcs all required', async () => {
    const input = place<number>('IN');
    const output = place<number>('OUT');
    const rd1 = place<number>('RD1');
    const rd2 = place<number>('RD2');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .reads(rd1, rd2)
      .action(async (ctx) => {
        ctx.output(output, ctx.read(rd1) + ctx.read(rd2));
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();

    // Only one read present
    const { marking: m1 } = await runNet(net, initialTokens(
      [input, [tokenOf(1)]],
      [rd1, [tokenOf(10)]],
    ));
    expect(m1.hasTokens(output)).toBe(false);

    // Both present
    const { marking: m2 } = await runNet(net, initialTokens(
      [input, [tokenOf(1)]],
      [rd1, [tokenOf(10)]],
      [rd2, [tokenOf(20)]],
    ));
    expect(m2.hasTokens(output)).toBe(true);
    expect(m2.peekFirst(output)!.value).toBe(30);
    expect(m2.hasTokens(rd1)).toBe(true);
    expect(m2.hasTokens(rd2)).toBe(true);
  });
});

// ======================== RESET ARC TESTS ========================

describe('Reset Arc Tests', () => {
  it('reset arc removes all tokens from place', async () => {
    const input = place<string>('IN');
    const output = place<string>('OUT');
    const resetPlace = place<number>('RST');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .reset(resetPlace)
      .action(async (ctx) => { ctx.output(output, 'done'); })
      .build();
    const net = PetriNet.builder('N').transition(t).build();

    const { marking } = await runNet(net, initialTokens(
      [input, [tokenOf('go')]],
      [resetPlace, [tokenOf(1), tokenOf(2), tokenOf(3)]],
    ));
    expect(marking.tokenCount(resetPlace)).toBe(0);
    expect(marking.hasTokens(output)).toBe(true);
  });

  it('reset arc fires even if place is empty', async () => {
    const input = place<string>('IN');
    const output = place<string>('OUT');
    const resetPlace = place<number>('RST');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .reset(resetPlace)
      .action(async (ctx) => { ctx.output(output, 'done'); })
      .build();
    const net = PetriNet.builder('N').transition(t).build();

    const { marking } = await runNet(net, initialTokens([input, [tokenOf('go')]]));
    expect(marking.hasTokens(output)).toBe(true);
  });

  it('multiple reset arcs clear all places', async () => {
    const input = place<string>('IN');
    const output = place<string>('OUT');
    const rst1 = place<number>('RST1');
    const rst2 = place<number>('RST2');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .resets(rst1, rst2)
      .action(async (ctx) => { ctx.output(output, 'done'); })
      .build();
    const net = PetriNet.builder('N').transition(t).build();

    const { marking } = await runNet(net, initialTokens(
      [input, [tokenOf('go')]],
      [rst1, [tokenOf(1), tokenOf(2)]],
      [rst2, [tokenOf(3), tokenOf(4), tokenOf(5)]],
    ));
    expect(marking.tokenCount(rst1)).toBe(0);
    expect(marking.tokenCount(rst2)).toBe(0);
    expect(marking.hasTokens(output)).toBe(true);
  });

  it('difference between reset and input: input consumes one, reset removes all', async () => {
    const trigger = place<string>('TRIGGER');
    const inputPlace = place<number>('INPUT');
    const resetPlace = place<number>('RESET');
    const output = place<string>('OUT');

    // Single transition: consumes ONE from inputPlace (input arc), removes ALL from resetPlace (reset arc)
    const t = Transition.builder('T')
      .inputs(one(trigger), one(inputPlace))
      .outputs(outPlace(output))
      .reset(resetPlace)
      .action(async (ctx) => { ctx.output(output, 'done'); })
      .build();

    const net = PetriNet.builder('N').transition(t).build();
    const { marking } = await runNet(net, initialTokens(
      [trigger, [tokenOf('go')]],
      [inputPlace, [tokenOf(1), tokenOf(2), tokenOf(3)]],
      [resetPlace, [tokenOf(10), tokenOf(20), tokenOf(30)]],
    ));

    // Input: consumed one (trigger consumed too), 2 remain
    expect(marking.tokenCount(inputPlace)).toBe(2);
    // Reset: all removed
    expect(marking.tokenCount(resetPlace)).toBe(0);
    expect(marking.hasTokens(output)).toBe(true);
  });
});

// ======================== COMBINED ARC TESTS ========================

describe('Combined Arc Tests', () => {
  it('input + inhibitor combined', async () => {
    const input = place<string>('IN');
    const output = place<string>('OUT');
    const blocker = place<string>('BLOCKER');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .inhibitor(blocker)
      .action(async (ctx) => { ctx.output(output, 'done'); })
      .build();
    const net = PetriNet.builder('N').transition(t).build();

    // Blocked
    const { marking: m1 } = await runNet(net, initialTokens(
      [input, [tokenOf('go')]],
      [blocker, [tokenOf('x')]],
    ));
    expect(m1.hasTokens(output)).toBe(false);
    expect(m1.hasTokens(input)).toBe(true);

    // Not blocked
    const { marking: m2 } = await runNet(net, initialTokens([input, [tokenOf('go')]]));
    expect(m2.hasTokens(output)).toBe(true);
  });

  it('input + read combined', async () => {
    const input = place<number>('IN');
    const config = place<number>('CONFIG');
    const output = place<number>('OUT');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .read(config)
      .action(async (ctx) => {
        ctx.output(output, ctx.input(input) * ctx.read(config));
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const { marking } = await runNet(net, initialTokens(
      [input, [tokenOf(7)]],
      [config, [tokenOf(3)]],
    ));

    expect(marking.hasTokens(input)).toBe(false);
    expect(marking.hasTokens(config)).toBe(true);
    expect(marking.peekFirst(output)!.value).toBe(21);
  });

  it('input + reset combined', async () => {
    const input = place<string>('IN');
    const output = place<string>('OUT');
    const resetPlace = place<number>('RST');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .reset(resetPlace)
      .action(async (ctx) => { ctx.output(output, 'done'); })
      .build();
    const net = PetriNet.builder('N').transition(t).build();

    const { marking } = await runNet(net, initialTokens(
      [input, [tokenOf('go')]],
      [resetPlace, [tokenOf(1), tokenOf(2), tokenOf(3)]],
    ));
    expect(marking.tokenCount(resetPlace)).toBe(0);
    expect(marking.hasTokens(output)).toBe(true);
  });

  it('input + read + reset fires when all satisfied', async () => {
    const input = place<string>('IN');
    const output = place<string>('OUT');
    const readPlace = place<number>('RD');
    const resetPlace = place<number>('RST');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .read(readPlace)
      .reset(resetPlace)
      .action(async (ctx) => { ctx.output(output, 'done'); })
      .build();
    const net = PetriNet.builder('N').transition(t).build();

    const { marking } = await runNet(net, initialTokens(
      [input, [tokenOf('go')]],
      [readPlace, [tokenOf(10)]],
      [resetPlace, [tokenOf(1), tokenOf(2)]],
    ));

    expect(marking.hasTokens(input)).toBe(false);
    expect(marking.hasTokens(readPlace)).toBe(true);
    expect(marking.tokenCount(resetPlace)).toBe(0);
    expect(marking.hasTokens(output)).toBe(true);
  });

  it('input + read + reset blocked when read absent', async () => {
    const input = place<string>('IN');
    const output = place<string>('OUT');
    const readPlace = place<number>('RD');
    const resetPlace = place<number>('RST');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .read(readPlace)
      .reset(resetPlace)
      .action(async (ctx) => { ctx.output(output, 'done'); })
      .build();
    const net = PetriNet.builder('N').transition(t).build();

    const { marking } = await runNet(net, initialTokens(
      [input, [tokenOf('go')]],
      [resetPlace, [tokenOf(1)]],
    ));

    expect(marking.hasTokens(input)).toBe(true);
    expect(marking.tokenCount(resetPlace)).toBe(1); // NOT reset
    expect(marking.hasTokens(output)).toBe(false);
  });

  it('all arc types combined fires when all satisfied', async () => {
    const input = place<string>('IN');
    const output = place<string>('OUT');
    const inhibitor = place<string>('INH');
    const readPlace = place<number>('RD');
    const resetPlace = place<number>('RST');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .inhibitor(inhibitor)
      .read(readPlace)
      .reset(resetPlace)
      .action(async (ctx) => { ctx.output(output, 'done'); })
      .build();
    const net = PetriNet.builder('N').transition(t).build();

    const { marking } = await runNet(net, initialTokens(
      [input, [tokenOf('go')]],
      [readPlace, [tokenOf(10)]],
      [resetPlace, [tokenOf(1), tokenOf(2)]],
    ));

    expect(marking.hasTokens(input)).toBe(false);
    expect(marking.hasTokens(readPlace)).toBe(true);
    expect(marking.tokenCount(resetPlace)).toBe(0);
    expect(marking.hasTokens(output)).toBe(true);
  });

  it('all arc types blocked by inhibitor', async () => {
    const input = place<string>('IN');
    const output = place<string>('OUT');
    const inhibitor = place<string>('INH');
    const readPlace = place<number>('RD');
    const resetPlace = place<number>('RST');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .inhibitor(inhibitor)
      .read(readPlace)
      .reset(resetPlace)
      .action(async (ctx) => { ctx.output(output, 'done'); })
      .build();
    const net = PetriNet.builder('N').transition(t).build();

    const { marking } = await runNet(net, initialTokens(
      [input, [tokenOf('go')]],
      [inhibitor, [tokenOf('block')]],
      [readPlace, [tokenOf(10)]],
      [resetPlace, [tokenOf(1)]],
    ));

    expect(marking.hasTokens(input)).toBe(true);
    expect(marking.tokenCount(resetPlace)).toBe(1); // NOT reset
    expect(marking.hasTokens(output)).toBe(false);
  });

  it('all arc types blocked by missing read', async () => {
    const input = place<string>('IN');
    const output = place<string>('OUT');
    const inhibitor = place<string>('INH');
    const readPlace = place<number>('RD');
    const resetPlace = place<number>('RST');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .inhibitor(inhibitor)
      .read(readPlace)
      .reset(resetPlace)
      .action(async (ctx) => { ctx.output(output, 'done'); })
      .build();
    const net = PetriNet.builder('N').transition(t).build();

    const { marking } = await runNet(net, initialTokens(
      [input, [tokenOf('go')]],
      [resetPlace, [tokenOf(1)]],
    ));

    expect(marking.hasTokens(input)).toBe(true);
    expect(marking.tokenCount(resetPlace)).toBe(1);
    expect(marking.hasTokens(output)).toBe(false);
  });

  it('two transitions: inhibitor cleared by first enables second', async () => {
    const blocker = place<string>('BLOCKER');
    const input = place<string>('IN');
    const outClear = place<string>('CLEARED');
    const output = place<string>('OUT');

    const clearT = Transition.builder('Clear')
      .inputs(one(blocker))
      .outputs(outPlace(outClear))
      .priority(50)
      .action(async (ctx) => { ctx.output(outClear, 'cleared'); })
      .build();

    const mainT = Transition.builder('Main')
      .inputs(one(input))
      .outputs(outPlace(output))
      .inhibitor(blocker)
      .action(async (ctx) => { ctx.output(output, 'done'); })
      .build();

    const net = PetriNet.builder('N').transitions(clearT, mainT).build();
    const { marking } = await runNet(net, initialTokens(
      [blocker, [tokenOf('block')]],
      [input, [tokenOf('go')]],
    ));

    expect(marking.hasTokens(outClear)).toBe(true);
    expect(marking.hasTokens(output)).toBe(true);
  });
});

// ======================== CARDINALITY TESTS ========================

describe('Cardinality Tests', () => {
  it('exactly(3) consumes exactly 3 of 5 tokens', async () => {
    const input = place<number>('IN');
    const output = place<number>('OUT');
    const t = Transition.builder('T')
      .inputs(exactly(3, input))
      .outputs(outPlace(output))
      .action(async (ctx) => {
        const vals = ctx.inputs(input);
        ctx.output(output, vals.reduce((a, b) => a + b, 0));
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const { marking } = await runNet(net, initialTokens(
      [input, [tokenOf(1), tokenOf(2), tokenOf(3), tokenOf(4), tokenOf(5)]],
    ));

    expect(marking.tokenCount(input)).toBe(2);
    expect(marking.hasTokens(output)).toBe(true);
  });

  it('all() consumes all tokens', async () => {
    const input = place<number>('IN');
    const output = place<number>('OUT');
    const readPlace = place<string>('RD');
    const resetPlace = place<string>('RST');
    const t = Transition.builder('T')
      .inputs(all(input))
      .outputs(outPlace(output))
      .read(readPlace)
      .reset(resetPlace)
      .action(async (ctx) => {
        const vals = ctx.inputs(input);
        ctx.output(output, vals.reduce((a, b) => a + b, 0));
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const { marking } = await runNet(net, initialTokens(
      [input, [tokenOf(1), tokenOf(2), tokenOf(3), tokenOf(4)]],
      [readPlace, [tokenOf('config')]],
      [resetPlace, [tokenOf('x')]],
    ));

    expect(marking.tokenCount(input)).toBe(0);
    expect(marking.hasTokens(output)).toBe(true);
    expect(marking.peekFirst(output)!.value).toBe(10);
    expect(marking.hasTokens(readPlace)).toBe(true);
    expect(marking.tokenCount(resetPlace)).toBe(0);
  });

  it('atLeast(3) blocks with only 2 tokens', async () => {
    const input = place<number>('IN');
    const output = place<number>('OUT');
    const t = Transition.builder('T')
      .inputs(atLeast(3, input))
      .outputs(outPlace(output))
      .action(async (ctx) => {
        ctx.output(output, ctx.inputs(input).length);
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const { marking } = await runNet(net, initialTokens(
      [input, [tokenOf(1), tokenOf(2)]],
    ));

    expect(marking.hasTokens(output)).toBe(false);
    expect(marking.tokenCount(input)).toBe(2);
  });

  it('atLeast(3) fires with 5 tokens and consumes all', async () => {
    const input = place<number>('IN');
    const output = place<number>('OUT');
    const t = Transition.builder('T')
      .inputs(atLeast(3, input))
      .outputs(outPlace(output))
      .action(async (ctx) => {
        ctx.output(output, ctx.inputs(input).length);
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const { marking } = await runNet(net, initialTokens(
      [input, [tokenOf(1), tokenOf(2), tokenOf(3), tokenOf(4), tokenOf(5)]],
    ));

    expect(marking.hasTokens(output)).toBe(true);
    expect(marking.peekFirst(output)!.value).toBe(5);
    expect(marking.tokenCount(input)).toBe(0);
  });
});

// ======================== OUTPUT SPEC TESTS ========================

describe('Output Spec Tests', () => {
  it('XOR output produces to correct branch', async () => {
    const input = place<string>('IN');
    const success = place<string>('SUCCESS');
    const failure = place<string>('FAILURE');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(xorPlaces(success, failure))
      .action(async (ctx) => { ctx.output(success, 'ok'); })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const { marking } = await runNet(net, initialTokens([input, [tokenOf('go')]]));

    expect(marking.hasTokens(success)).toBe(true);
    expect(marking.hasTokens(failure)).toBe(false);
  });

  it('AND output requires all places produced', async () => {
    const input = place<string>('IN');
    const outA = place<string>('A');
    const outB = place<string>('B');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(andPlaces(outA, outB))
      .action(async (ctx) => {
        ctx.output(outA, 'a');
        ctx.output(outB, 'b');
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const { marking } = await runNet(net, initialTokens([input, [tokenOf('go')]]));

    expect(marking.hasTokens(outA)).toBe(true);
    expect(marking.hasTokens(outB)).toBe(true);
  });

  it('XOR violation: multiple branches emits failure', async () => {
    const input = place<string>('IN');
    const branchA = place<string>('A');
    const branchB = place<string>('B');
    const eventStore = new InMemoryEventStore();
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(xorPlaces(branchA, branchB))
      .action(async (ctx) => {
        ctx.output(branchA, 'a');
        ctx.output(branchB, 'b'); // violation: both branches!
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    await runNet(net, initialTokens([input, [tokenOf('go')]]), { eventStore });

    const fails = failures(eventStore);
    expect(fails.length).toBeGreaterThan(0);
    const failEvent = fails[0] as TransitionFailed;
    expect(failEvent.errorMessage).toContain('XOR violation');
    expect(failEvent.errorMessage).toContain('multiple branches');
  });

  it('XOR violation: no branch emits failure', async () => {
    const input = place<string>('IN');
    const branchA = place<string>('A');
    const branchB = place<string>('B');
    const eventStore = new InMemoryEventStore();
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(xorPlaces(branchA, branchB))
      .action(async (ctx) => {
        // No output produced → XOR violation
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    await runNet(net, initialTokens([input, [tokenOf('go')]]), { eventStore });

    const fails = failures(eventStore);
    expect(fails.length).toBeGreaterThan(0);
    const failEvent = fails[0] as TransitionFailed;
    expect(failEvent.errorMessage).toContain('XOR violation');
    expect(failEvent.errorMessage).toContain('no branch');
  });

  it('missing required output emits failure', async () => {
    const input = place<string>('IN');
    const output = place<string>('OUT');
    const eventStore = new InMemoryEventStore();
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .action(async (ctx) => {
        // No output produced
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    await runNet(net, initialTokens([input, [tokenOf('go')]]), { eventStore });

    const fails = failures(eventStore);
    expect(fails.length).toBeGreaterThan(0);
    const failEvent = fails[0] as TransitionFailed;
    expect(failEvent.errorMessage).toContain('does not satisfy');
  });
});

// ======================== TIMING TESTS ========================

describe('Timing Tests', () => {
  it('delayed timing delays execution', async () => {
    const input = place<string>('IN');
    const output = place<string>('OUT');
    let fireTimeMs = 0;
    const startMs = performance.now();

    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .timing(delayed(150))
      .action(async (ctx) => {
        fireTimeMs = performance.now();
        ctx.output(output, 'done');
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    await runNet(net, initialTokens([input, [tokenOf('go')]]));

    expect(marking => marking.hasTokens(output));
    expect(fireTimeMs - startMs).toBeGreaterThanOrEqual(100); // Allow tolerance
  });

  it('exact timing fires at specified time', async () => {
    const input = place<string>('IN');
    const output = place<string>('OUT');
    let fireTimeMs = 0;
    const startMs = performance.now();

    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .timing(exact(150))
      .action(async (ctx) => {
        fireTimeMs = performance.now();
        ctx.output(output, 'done');
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    await runNet(net, initialTokens([input, [tokenOf('go')]]));

    expect(fireTimeMs - startMs).toBeGreaterThanOrEqual(100);
  });

  it('immediate timing fires quickly', async () => {
    const input = place<string>('IN');
    const output = place<string>('OUT');
    let fireTimeMs = 0;
    const startMs = performance.now();

    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .timing(immediate())
      .action(async (ctx) => {
        fireTimeMs = performance.now();
        ctx.output(output, 'done');
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    await runNet(net, initialTokens([input, [tokenOf('go')]]));

    expect(fireTimeMs - startMs).toBeLessThan(100);
  });
});

// ======================== OUTPUT TIMEOUT TESTS ========================

describe('Output Timeout Tests', () => {
  it('timeout produces timeout token when action slow', async () => {
    const input = place<string>('IN');
    const success = place<string>('SUCCESS');
    const timeoutOut = place<string>('TIMEOUT');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(xor(outPlace(success), timeoutPlace(50, timeoutOut)))
      .action(async (ctx) => {
        await sleep(200);
        ctx.output(success, 'ok');
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const { marking } = await runNet(net, initialTokens([input, [tokenOf('go')]]));

    expect(marking.hasTokens(timeoutOut)).toBe(true);
    expect(marking.hasTokens(success)).toBe(false);
  });

  it('timeout produces normal output when action fast', async () => {
    const input = place<string>('IN');
    const success = place<string>('SUCCESS');
    const timeoutOut = place<string>('TIMEOUT');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(xor(outPlace(success), timeoutPlace(500, timeoutOut)))
      .action(async (ctx) => {
        ctx.output(success, 'ok');
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const { marking } = await runNet(net, initialTokens([input, [tokenOf('go')]]));

    expect(marking.hasTokens(success)).toBe(true);
    expect(marking.hasTokens(timeoutOut)).toBe(false);
  });

  it('timeout forward-input forwards consumed value', async () => {
    const input = place<string>('IN');
    const success = place<string>('SUCCESS');
    const retry = place<string>('RETRY');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(xor(outPlace(success), timeout(50, forwardInput(input, retry))))
      .action(async (ctx) => {
        await sleep(200);
        ctx.output(success, 'ok');
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const { marking } = await runNet(net, initialTokens([input, [tokenOf('original-value')]]));

    expect(marking.hasTokens(retry)).toBe(true);
    expect(marking.peekFirst(retry)!.value).toBe('original-value');
    expect(marking.hasTokens(success)).toBe(false);
  });

  it('timeout AND child produces to multiple places', async () => {
    const input = place<string>('IN');
    const success = place<string>('SUCCESS');
    const fallbackA = place<string>('FA');
    const fallbackB = place<string>('FB');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(xor(outPlace(success), timeout(50, andPlaces(fallbackA, fallbackB))))
      .action(async (ctx) => {
        await sleep(200);
        ctx.output(success, 'ok');
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const { marking } = await runNet(net, initialTokens([input, [tokenOf('go')]]));

    expect(marking.hasTokens(fallbackA)).toBe(true);
    expect(marking.hasTokens(fallbackB)).toBe(true);
    expect(marking.hasTokens(success)).toBe(false);
  });
});

// ======================== PRIORITY TESTS ========================

describe('Priority Tests', () => {
  it('higher priority fires first', async () => {
    const input = place<string>('IN');
    const outHigh = place<string>('HIGH');
    const outLow = place<string>('LOW');
    const order: string[] = [];

    const tHigh = Transition.builder('High')
      .inputs(one(input))
      .outputs(outPlace(outHigh))
      .priority(10)
      .action(async (ctx) => { order.push('high'); ctx.output(outHigh, 'hi'); })
      .build();

    const tLow = Transition.builder('Low')
      .inputs(one(input))
      .outputs(outPlace(outLow))
      .priority(1)
      .action(async (ctx) => { order.push('low'); ctx.output(outLow, 'lo'); })
      .build();

    const net = PetriNet.builder('N').transitions(tHigh, tLow).build();
    const { marking } = await runNet(net, initialTokens([input, [tokenOf('go')]]));

    // High priority fires, consumes token, low cannot fire
    expect(marking.hasTokens(outHigh)).toBe(true);
    expect(order[0]).toBe('high');
  });
});

// ======================== ASYNC ACTION TESTS ========================

describe('Async Action Tests', () => {
  it('async action completes successfully', async () => {
    const input = place<string>('IN');
    const output = place<string>('OUT');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .action(async (ctx) => {
        await sleep(10);
        ctx.output(output, 'async-result');
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const { marking } = await runNet(net, initialTokens([input, [tokenOf('go')]]));

    expect(marking.peekFirst(output)!.value).toBe('async-result');
  });

  it('async action handles exception', async () => {
    const input = place<string>('IN');
    const output = place<string>('OUT');
    const eventStore = new InMemoryEventStore();
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .action(async () => {
        throw new Error('boom');
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    await runNet(net, initialTokens([input, [tokenOf('go')]]), { eventStore });

    const fails = eventsOfType(eventStore, 'transition-failed');
    expect(fails.length).toBeGreaterThan(0);
    expect(fails[0]!.errorMessage).toBe('boom');
  });

  it('parallel transitions execute in parallel', async () => {
    const fork = place<string>('FORK');
    const w1In = place<string>('W1');
    const w2In = place<string>('W2');
    const w3In = place<string>('W3');
    const w1Out = place<string>('W1_OUT');
    const w2Out = place<string>('W2_OUT');
    const w3Out = place<string>('W3_OUT');

    const forkT = Transition.builder('Fork')
      .inputs(one(fork))
      .outputs(andPlaces(w1In, w2In, w3In))
      .action(async (ctx) => {
        ctx.output(w1In, 'go');
        ctx.output(w2In, 'go');
        ctx.output(w3In, 'go');
      })
      .build();

    const makeWorker = (name: string, inP: Place<string>, outP: Place<string>) =>
      Transition.builder(name)
        .inputs(one(inP))
        .outputs(outPlace(outP))
        .action(async (ctx) => {
          await sleep(100);
          ctx.output(outP, 'done');
        })
        .build();

    const net = PetriNet.builder('N')
      .transitions(forkT, makeWorker('W1', w1In, w1Out), makeWorker('W2', w2In, w2Out), makeWorker('W3', w3In, w3Out))
      .build();

    const startMs = performance.now();
    const { marking } = await runNet(net, initialTokens([fork, [tokenOf('start')]]));
    const durationMs = performance.now() - startMs;

    expect(marking.hasTokens(w1Out)).toBe(true);
    expect(marking.hasTokens(w2Out)).toBe(true);
    expect(marking.hasTokens(w3Out)).toBe(true);
    // ~100ms if parallel, ~300ms if sequential
    expect(durationMs).toBeLessThan(250);
  });

  it('passthrough action produces no output', async () => {
    const input = place<string>('IN');
    const t = Transition.builder('T')
      .inputs(one(input))
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const { marking } = await runNet(net, initialTokens([input, [tokenOf('go')]]));

    expect(marking.hasTokens(input)).toBe(false);
  });

  it('transform synchronous transformation', async () => {
    const input = place<number>('IN');
    const output = place<number>('OUT');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .action(async (ctx) => {
        ctx.output(output, ctx.input(input) * 2);
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const { marking } = await runNet(net, initialTokens([input, [tokenOf(21)]]));

    expect(marking.peekFirst(output)!.value).toBe(42);
  });
});

// ======================== WORKFLOW PATTERN TESTS ========================

describe('Workflow Pattern Tests', () => {
  it('sequential chain executes in order', async () => {
    const p1 = place<number>('P1');
    const p2 = place<number>('P2');
    const p3 = place<number>('P3');
    const p4 = place<number>('P4');
    const seq: number[] = [];

    const t1 = Transition.builder('T1')
      .inputs(one(p1)).outputs(outPlace(p2))
      .action(async (ctx) => { seq.push(1); ctx.output(p2, ctx.input(p1)); })
      .build();
    const t2 = Transition.builder('T2')
      .inputs(one(p2)).outputs(outPlace(p3))
      .action(async (ctx) => { seq.push(2); ctx.output(p3, ctx.input(p2)); })
      .build();
    const t3 = Transition.builder('T3')
      .inputs(one(p3)).outputs(outPlace(p4))
      .action(async (ctx) => { seq.push(3); ctx.output(p4, ctx.input(p3)); })
      .build();

    const net = PetriNet.builder('N').transitions(t1, t2, t3).build();
    const { marking } = await runNet(net, initialTokens([p1, [tokenOf(0)]]));

    expect(seq).toEqual([1, 2, 3]);
    expect(marking.hasTokens(p4)).toBe(true);
  });

  it('fork-join parallel branches merge', async () => {
    const start = place<string>('START');
    const left = place<string>('LEFT');
    const right = place<string>('RIGHT');
    const leftDone = place<string>('LEFT_DONE');
    const rightDone = place<string>('RIGHT_DONE');
    const end = place<string>('END');

    const forkT = Transition.builder('Fork')
      .inputs(one(start)).outputs(andPlaces(left, right))
      .action(async (ctx) => { ctx.output(left, 'l'); ctx.output(right, 'r'); })
      .build();
    const leftT = Transition.builder('Left')
      .inputs(one(left)).outputs(outPlace(leftDone))
      .action(async (ctx) => { ctx.output(leftDone, 'ld'); })
      .build();
    const rightT = Transition.builder('Right')
      .inputs(one(right)).outputs(outPlace(rightDone))
      .action(async (ctx) => { ctx.output(rightDone, 'rd'); })
      .build();
    const joinT = Transition.builder('Join')
      .inputs(one(leftDone), one(rightDone)).outputs(outPlace(end))
      .action(async (ctx) => { ctx.output(end, 'done'); })
      .build();

    const net = PetriNet.builder('N').transitions(forkT, leftT, rightT, joinT).build();
    const { marking } = await runNet(net, initialTokens([start, [tokenOf('go')]]));

    expect(marking.hasTokens(left)).toBe(false);
    expect(marking.hasTokens(right)).toBe(false);
    expect(marking.hasTokens(end)).toBe(true);
  });

  it('conditional branching exclusive choice', async () => {
    const input = place<string>('IN');
    const leftOut = place<string>('LEFT');
    const rightOut = place<string>('RIGHT');

    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(xorPlaces(leftOut, rightOut))
      .action(async (ctx) => {
        const val = ctx.input(input);
        if (val === 'GoLeft') ctx.output(leftOut, 'left');
        else ctx.output(rightOut, 'right');
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();

    // GoLeft
    const { marking: m1 } = await runNet(net, initialTokens([input, [tokenOf('GoLeft')]]));
    expect(m1.hasTokens(leftOut)).toBe(true);
    expect(m1.hasTokens(rightOut)).toBe(false);

    // GoRight
    const { marking: m2 } = await runNet(net, initialTokens([input, [tokenOf('GoRight')]]));
    expect(m2.hasTokens(rightOut)).toBe(true);
    expect(m2.hasTokens(leftOut)).toBe(false);
  });

  it('loop repeats until condition', async () => {
    const loop = place<number>('LOOP');
    const done = place<number>('DONE');
    let iterations = 0;

    const t = Transition.builder('T')
      .inputs(one(loop))
      .outputs(xorPlaces(loop, done))
      .action(async (ctx) => {
        const v = ctx.input(loop);
        iterations++;
        if (v >= 3) ctx.output(done, v);
        else ctx.output(loop, v + 1);
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const { marking } = await runNet(net, initialTokens([loop, [tokenOf(0)]]));

    expect(iterations).toBe(4); // 0→1→2→3→done
    expect(marking.hasTokens(done)).toBe(true);
    expect(marking.peekFirst(done)!.value).toBe(3);
  });

  it('mutex mutual exclusion', async () => {
    const mutex = place<string>('MUTEX');
    const req1 = place<string>('REQ1');
    const req2 = place<string>('REQ2');
    const done1 = place<string>('DONE1');
    const done2 = place<string>('DONE2');
    const sequence: string[] = [];

    const makeWorker = (name: string, req: Place<string>, out: Place<string>) =>
      Transition.builder(name)
        .inputs(one(req), one(mutex))
        .outputs(andPlaces(out, mutex))
        .action(async (ctx) => {
          sequence.push(`${name}-start`);
          await sleep(20);
          sequence.push(`${name}-end`);
          ctx.output(out, 'done');
          ctx.output(mutex, 'free');
        })
        .build();

    const net = PetriNet.builder('N')
      .transitions(makeWorker('W1', req1, done1), makeWorker('W2', req2, done2))
      .build();
    const { marking } = await runNet(net, initialTokens(
      [mutex, [tokenOf('free')]],
      [req1, [tokenOf('go')]],
      [req2, [tokenOf('go')]],
    ));

    expect(marking.hasTokens(done1)).toBe(true);
    expect(marking.hasTokens(done2)).toBe(true);
    // Mutual exclusion: one must finish before the other starts
    const firstEnd = sequence.indexOf('W1-end') < sequence.indexOf('W2-end') ? 'W1' : 'W2';
    const secondStart = firstEnd === 'W1' ? 'W2-start' : 'W1-start';
    const firstEndIdx = sequence.indexOf(`${firstEnd}-end`);
    const secondStartIdx = sequence.indexOf(secondStart);
    // The second worker starts after the first completes (or equal — both times are OK for mutual exclusion)
    expect(secondStartIdx).toBeGreaterThanOrEqual(firstEndIdx);
  });
});

// ======================== EDGE CASES AND ERROR HANDLING ========================

describe('Edge Cases and Error Handling', () => {
  it('empty net completes immediately', async () => {
    const net = PetriNet.builder('Empty').build();
    const { marking } = await runNet(net, initialTokens());
    expect(marking).toBeDefined();
  });

  it('no initial tokens nothing fires', async () => {
    const input = place<string>('IN');
    const output = place<string>('OUT');
    const t = Transition.builder('T')
      .inputs(one(input)).outputs(outPlace(output))
      .action(async (ctx) => { ctx.output(output, 'x'); })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const { marking } = await runNet(net, initialTokens());
    expect(marking.hasTokens(output)).toBe(false);
  });

  it('single transition fires once', async () => {
    let fireCount = 0;
    const input = place<string>('IN');
    const output = place<string>('OUT');
    const t = Transition.builder('T')
      .inputs(one(input)).outputs(outPlace(output))
      .action(async (ctx) => { fireCount++; ctx.output(output, 'x'); })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    await runNet(net, initialTokens([input, [tokenOf('go')]]));
    expect(fireCount).toBe(1);
  });

  it('many tokens all processed', async () => {
    const input = place<number>('IN');
    const output = place<number>('OUT');
    const t = Transition.builder('T')
      .inputs(one(input)).outputs(outPlace(output))
      .action(async (ctx) => { ctx.output(output, ctx.input(input)); })
      .build();
    const net = PetriNet.builder('N').transition(t).build();

    const tokens = Array.from({ length: 100 }, (_, i) => tokenOf(i));
    const { marking } = await runNet(net, initialTokens([input, tokens]));

    expect(marking.tokenCount(input)).toBe(0);
    expect(marking.tokenCount(output)).toBe(100);
  });
});

// ======================== EVENT STORE TESTS ========================

describe('Event Store Tests', () => {
  it('event store records all events', async () => {
    const eventStore = new InMemoryEventStore();
    const input = place<string>('IN');
    const output = place<string>('OUT');
    const t = Transition.builder('T')
      .inputs(one(input)).outputs(outPlace(output))
      .action(async (ctx) => { ctx.output(output, 'done'); })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    await runNet(net, initialTokens([input, [tokenOf('go')]]), { eventStore });

    const types = eventStore.events().map(e => e.type);
    expect(types).toContain('execution-started');
    expect(types).toContain('transition-enabled');
    expect(types).toContain('transition-started');
    expect(types).toContain('transition-completed');
    expect(types).toContain('execution-completed');
  });

  it('noop event store has no allocations', async () => {
    const noop = noopEventStore();
    const input = place<string>('IN');
    const output = place<string>('OUT');
    const t = Transition.builder('T')
      .inputs(one(input)).outputs(outPlace(output))
      .action(async (ctx) => { ctx.output(output, 'done'); })
      .build();
    const net = PetriNet.builder('N').transition(t).build();

    const executor = new PrecompiledNetExecutor(net, initialTokens([input, [tokenOf('go')]]), { eventStore: noop });
    await executor.run(5000);
    expect(noop.events()).toHaveLength(0);
  });
});

// ======================== EXECUTOR CLOSE TESTS ========================

describe('Executor Close Tests', () => {
  it('close stops execution', async () => {
    const input = place<string>('IN');
    const output = place<string>('OUT');
    const envP = environmentPlace<string>('ENV');

    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .action(async (ctx) => { ctx.output(output, 'done'); })
      .build();
    const net = PetriNet.builder('N').transition(t).build();

    const executor = new PrecompiledNetExecutor(net, initialTokens(), {
      environmentPlaces: new Set([envP]),
    });

    const promise = executor.run(5000);
    // Drain after a short delay
    setTimeout(() => executor.drain(), 50);
    const marking = await promise;
    expect(marking).toBeDefined();
  });
});

// ======================== ENVIRONMENT PLACE TESTS ========================

describe('Environment Place Tests', () => {
  it('executor with env places wakes on environment injection', async () => {
    const envP = environmentPlace<string>('ENV');
    const input = envP.place;
    const output = place<string>('OUT');

    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .action(async (ctx) => { ctx.output(output, ctx.input(input)); })
      .build();
    const net = PetriNet.builder('N').transition(t).build();

    const executor = new PrecompiledNetExecutor(net, initialTokens(), {
      environmentPlaces: new Set([envP]),
    });

    const promise = executor.run(5000);

    // Inject after a brief delay
    await sleep(30);
    const accepted = await executor.inject(envP, tokenOf('injected'));
    expect(accepted).toBe(true);

    // Drain and collect
    await sleep(50);
    executor.drain();
    const marking = await promise;

    expect(marking.hasTokens(output)).toBe(true);
    expect(marking.peekFirst(output)!.value).toBe('injected');
  });

  it('inject into non-environment place fails', async () => {
    const envP = environmentPlace<string>('ENV');
    const nonEnvP = environmentPlace<string>('NON_ENV');
    const input = envP.place;
    const t = Transition.builder('T').inputs(one(input)).build();
    const net = PetriNet.builder('N').transition(t).build();

    const executor = new PrecompiledNetExecutor(net, initialTokens(), {
      environmentPlaces: new Set([envP]),
    });

    const promise = executor.run(5000);

    await expect(executor.inject(nonEnvP, tokenOf('x'))).rejects.toThrow('not registered');

    executor.drain();
    await promise;
  });

  it('multiple injections all processed', async () => {
    const envP = environmentPlace<number>('ENV');
    const input = envP.place;
    const output = place<number>('OUT');

    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .action(async (ctx) => { ctx.output(output, ctx.input(input)); })
      .build();
    const net = PetriNet.builder('N').transition(t).build();

    const executor = new PrecompiledNetExecutor(net, initialTokens(), {
      environmentPlaces: new Set([envP]),
    });

    const promise = executor.run(5000);

    for (let i = 0; i < 10; i++) {
      await executor.inject(envP, tokenOf(i));
      await sleep(10);
    }

    await sleep(100);
    executor.drain();
    const marking = await promise;

    expect(marking.tokenCount(output)).toBe(10);
  });

  it('inject after close returns false', async () => {
    const envP = environmentPlace<string>('ENV');
    const input = envP.place;
    const t = Transition.builder('T').inputs(one(input)).build();
    const net = PetriNet.builder('N').transition(t).build();

    const executor = new PrecompiledNetExecutor(net, initialTokens(), {
      environmentPlaces: new Set([envP]),
    });

    const promise = executor.run(5000);
    executor.close();
    await promise;

    const result = await executor.inject(envP, tokenOf('too-late'));
    expect(result).toBe(false);
  });

  it('close discards queued external events [ENV-013]', async () => {
    const envP = environmentPlace<string>('ENV');
    const input = envP.place;
    const output = place<string>('OUT');

    // Slow transition to keep executor busy while we queue more events
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .action(async (ctx) => {
        await sleep(500);
        ctx.output(output, ctx.input(input));
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();

    const executor = new PrecompiledNetExecutor(net, initialTokens(), {
      environmentPlaces: new Set([envP]),
    });

    const promise = executor.run(5000);
    await sleep(30);

    // Inject first token to start the slow transition
    await executor.inject(envP, tokenOf('first'));
    await sleep(30);

    // Inject second token while first is in-flight (queued)
    const pendingResult = executor.inject(envP, tokenOf('pending'));

    // Close immediately — should discard the pending event
    executor.close();
    const marking = await promise;

    // The pending inject should complete with false (discarded, not processed)
    expect(await pendingResult).toBe(false);
  });

  it('close waits for in-flight actions before terminating [ENV-013]', async () => {
    const envP = environmentPlace<string>('ENV');
    const input = envP.place;
    const output = place<string>('OUT');

    let actionStarted = false;
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .action(async (ctx) => {
        actionStarted = true;
        await sleep(200);
        ctx.output(output, 'completed');
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();

    const executor = new PrecompiledNetExecutor(net, initialTokens(), {
      environmentPlaces: new Set([envP]),
    });

    const promise = executor.run(5000);
    await sleep(30);

    // Inject token to start the async action
    await executor.inject(envP, tokenOf('go'));
    await sleep(30);
    expect(actionStarted).toBe(true);

    // Close while in-flight — ENV-013 requires in-flight to complete
    executor.close();
    const marking = await promise;

    // The in-flight action should have completed and produced output
    expect(marking.hasTokens(output)).toBe(true);
  });

  it('drain then close escalates to immediate shutdown [ENV-013]', async () => {
    const envP = environmentPlace<string>('ENV');
    const input = envP.place;
    const output = place<string>('OUT');

    let actionStarted = false;
    let actionCanFinish = false;
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .action(async (ctx) => {
        actionStarted = true;
        while (!actionCanFinish) await sleep(10);
        ctx.output(output, 'done');
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();

    const executor = new PrecompiledNetExecutor(net, initialTokens(), {
      environmentPlaces: new Set([envP]),
    });

    const promise = executor.run(5000);
    await sleep(30);

    // Inject token to start slow action
    await executor.inject(envP, tokenOf('go'));
    await sleep(30);
    expect(actionStarted).toBe(true);

    // Queue another injection while first is in-flight
    const pendingResult = executor.inject(envP, tokenOf('queued'));

    // Drain first — rejects new injections
    executor.drain();
    const postDrainResult = await executor.inject(envP, tokenOf('rejected'));
    expect(postDrainResult).toBe(false);

    // Escalate to close — discards queued events
    executor.close();

    // Let the in-flight action complete
    actionCanFinish = true;
    const marking = await promise;

    // In-flight action should complete per ENV-013
    expect(marking.hasTokens(output)).toBe(true);
    // Pending inject should be discarded
    expect(await pendingResult).toBe(false);
  });

  it('delayed transition fires without external event with env places', async () => {
    const envP = environmentPlace<string>('ENV');
    const trigger = place<string>('TRIGGER');
    const output = place<string>('OUT');

    const t = Transition.builder('T')
      .inputs(one(trigger))
      .outputs(outPlace(output))
      .timing(delayed(50))
      .action(async (ctx) => { ctx.output(output, 'timed'); })
      .build();
    const net = PetriNet.builder('N').transition(t).build();

    const executor = new PrecompiledNetExecutor(
      net,
      initialTokens([trigger, [tokenOf('go')]]),
      { environmentPlaces: new Set([envP]) },
    );

    const promise = executor.run(5000);
    await sleep(500);
    executor.drain();
    const marking = await promise;

    expect(marking.hasTokens(output)).toBe(true);
  });

  it('event store records environment token added events', async () => {
    const eventStore = new InMemoryEventStore();
    const envP = environmentPlace<string>('ENV_INPUT');
    const input = envP.place;
    const output = place<string>('OUT');

    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .action(async (ctx) => { ctx.output(output, ctx.input(input)); })
      .build();
    const net = PetriNet.builder('N').transition(t).build();

    const executor = new PrecompiledNetExecutor(net, initialTokens(), {
      environmentPlaces: new Set([envP]),
      eventStore,
    });

    const promise = executor.run(5000);
    await sleep(20);
    await executor.inject(envP, tokenOf('test'));
    await sleep(50);
    executor.drain();
    await promise;

    const tokenAdded = eventsOfType(eventStore, 'token-added');
    const envAdded = tokenAdded.filter(e => e.placeName === 'ENV_INPUT');
    expect(envAdded.length).toBeGreaterThan(0);
  });
});

// ======================== SELF-LOOP AND FIRING ORDER TESTS ========================

describe('Firing Order Tests', () => {
  it('self-loop consumes then produces', async () => {
    const loop = place<number>('LOOP');
    const done = place<number>('DONE');
    const seenValues: number[] = [];

    const t = Transition.builder('T')
      .inputs(one(loop))
      .outputs(xorPlaces(loop, done))
      .action(async (ctx) => {
        const v = ctx.input(loop);
        seenValues.push(v);
        if (v >= 2) ctx.output(done, v + 1);
        else ctx.output(loop, v + 1);
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const { marking } = await runNet(net, initialTokens([loop, [tokenOf(0)]]));

    expect(seenValues).toEqual([0, 1, 2]);
    expect(marking.hasTokens(done)).toBe(true);
    expect(marking.peekFirst(done)!.value).toBe(3);
  });

  it('output deposited after action completes', async () => {
    const input = place<number>('IN');
    const output = place<number>('OUT');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .action(async (ctx) => {
        await sleep(10);
        ctx.output(output, 42);
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const { marking } = await runNet(net, initialTokens([input, [tokenOf(0)]]));

    expect(marking.hasTokens(output)).toBe(true);
    expect(marking.peekFirst(output)!.value).toBe(42);
  });
});

// ======================== RESET ARC TIMER RESTART TESTS ========================

describe('Reset Arc Timer Restart Tests', () => {
  it('reset arc with output to same place restarts timed transition clock', async () => {
    const trigger = place<string>('TRIGGER');
    const timerPlace = place<string>('TIMER');
    const resetDone = place<string>('RESET_DONE');
    const timedOut = place<string>('TIMED_OUT');

    // T1: consumes trigger, resets timerPlace, then re-deposits
    const tReset = Transition.builder('Reset')
      .inputs(one(trigger))
      .outputs(andPlaces(resetDone, timerPlace))
      .reset(timerPlace)
      .priority(10)
      .action(async (ctx) => {
        await sleep(50); // takes 50ms
        ctx.output(resetDone, 'reset-done');
        ctx.output(timerPlace, 'fresh');
      })
      .build();

    // T2: delayed by 200ms, fires off timerPlace
    const tTimeout = Transition.builder('Timeout')
      .inputs(one(timerPlace))
      .outputs(outPlace(timedOut))
      .timing(delayed(200))
      .action(async (ctx) => { ctx.output(timedOut, 'timeout'); })
      .build();

    const net = PetriNet.builder('N').transitions(tReset, tTimeout).build();
    const startMs = performance.now();
    const { marking } = await runNet(net, initialTokens(
      [trigger, [tokenOf('go')]],
      [timerPlace, [tokenOf('initial')]],
    ));
    const elapsed = performance.now() - startMs;

    // Timeout should fire at ~250ms (50ms reset + 200ms delay), not 200ms
    expect(marking.hasTokens(timedOut)).toBe(true);
    expect(elapsed).toBeGreaterThanOrEqual(200);
  });
});

// ======================== GUARDED INPUT ARC TESTS ========================

describe('Guarded Input Arc Tests', () => {
  it('guarded one() only consumes matching token', async () => {
    const input = place<number>('IN');
    const output = place<number>('OUT');
    const t = Transition.builder('T')
      .inputs(one(input, (v: number) => v > 5))
      .outputs(outPlace(output))
      .action(async (ctx) => { ctx.output(output, ctx.input(input)); })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const { marking } = await runNet(net, initialTokens(
      [input, [tokenOf(1), tokenOf(10), tokenOf(2)]],
    ));

    // Only the first matching token (10) should be consumed
    expect(marking.hasTokens(output)).toBe(true);
    expect(marking.peekFirst(output)!.value).toBe(10);
    // Non-matching tokens remain (plus any remaining after re-firing)
  });

  it('guarded one() does not enable when no token matches', async () => {
    const input = place<number>('IN');
    const output = place<number>('OUT');
    const t = Transition.builder('T')
      .inputs(one(input, (v: number) => v > 100))
      .outputs(outPlace(output))
      .action(async (ctx) => { ctx.output(output, ctx.input(input)); })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const { marking } = await runNet(net, initialTokens(
      [input, [tokenOf(1), tokenOf(2), tokenOf(3)]],
    ));

    // No matching token → transition should not fire
    expect(marking.hasTokens(output)).toBe(false);
    expect(marking.tokenCount(input)).toBe(3); // all remain
  });

  it('guarded one() preserves FIFO among matching tokens', async () => {
    const input = place<number>('IN');
    const output = place<number>('OUT');
    const consumed: number[] = [];
    const t = Transition.builder('T')
      .inputs(one(input, (v: number) => v % 2 === 0))
      .outputs(outPlace(output))
      .action(async (ctx) => {
        const v = ctx.input(input);
        consumed.push(v);
        ctx.output(output, v);
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const { marking } = await runNet(net, initialTokens(
      [input, [tokenOf(1), tokenOf(2), tokenOf(3), tokenOf(4), tokenOf(5), tokenOf(6)]],
    ));

    // Should consume even numbers in FIFO order: 2, 4, 6
    expect(consumed).toEqual([2, 4, 6]);
    // Odd numbers remain
    expect(marking.tokenCount(input)).toBe(3);
    expect(marking.peekTokens(input).map(t => t.value)).toEqual([1, 3, 5]);
  });

  it('guarded exactly(2) consumes only matching tokens', async () => {
    const input = place<number>('IN');
    const output = place<number>('OUT');
    const t = Transition.builder('T')
      .inputs(exactly(2, input, (v: number) => v > 5))
      .outputs(outPlace(output))
      .action(async (ctx) => {
        ctx.output(output, ctx.inputs(input).reduce((a, b) => a + b, 0));
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const { marking } = await runNet(net, initialTokens(
      [input, [tokenOf(1), tokenOf(10), tokenOf(2), tokenOf(20), tokenOf(3)]],
    ));

    // Two matching tokens (10, 20) → fires, consumes them
    expect(marking.hasTokens(output)).toBe(true);
    expect(marking.peekFirst(output)!.value).toBe(30);
    // Non-matching tokens remain
    expect(marking.tokenCount(input)).toBe(3);
  });

  it('guarded exactly(3) does not enable with only 2 matching', async () => {
    const input = place<number>('IN');
    const output = place<number>('OUT');
    const t = Transition.builder('T')
      .inputs(exactly(3, input, (v: number) => v > 5))
      .outputs(outPlace(output))
      .action(async (ctx) => {
        ctx.output(output, ctx.inputs(input).reduce((a, b) => a + b, 0));
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const { marking } = await runNet(net, initialTokens(
      [input, [tokenOf(1), tokenOf(10), tokenOf(2), tokenOf(20), tokenOf(3)]],
    ));

    // Only 2 matching tokens, need 3 → should not fire
    expect(marking.hasTokens(output)).toBe(false);
    expect(marking.tokenCount(input)).toBe(5);
  });

  it('guard + inhibitor combined', async () => {
    const input = place<number>('IN');
    const output = place<number>('OUT');
    const blocker = place<string>('BLOCKER');
    const t = Transition.builder('T')
      .inputs(one(input, (v: number) => v > 0))
      .outputs(outPlace(output))
      .inhibitor(blocker)
      .action(async (ctx) => { ctx.output(output, ctx.input(input)); })
      .build();
    const net = PetriNet.builder('N').transition(t).build();

    // Matching token but inhibited
    const { marking: m1 } = await runNet(net, initialTokens(
      [input, [tokenOf(5)]],
      [blocker, [tokenOf('block')]],
    ));
    expect(m1.hasTokens(output)).toBe(false);

    // Matching token, not inhibited → fires
    const { marking: m2 } = await runNet(net, initialTokens(
      [input, [tokenOf(5)]],
    ));
    expect(m2.hasTokens(output)).toBe(true);
    expect(m2.peekFirst(output)!.value).toBe(5);

    // Non-matching token, not inhibited → does not fire
    const { marking: m3 } = await runNet(net, initialTokens(
      [input, [tokenOf(-1)]],
    ));
    expect(m3.hasTokens(output)).toBe(false);
  });

  it('guard with priority: guarded transition only fires on matching tokens', async () => {
    const input = place<number>('IN');
    const matchedOut = place<number>('MATCHED');
    const unmatchedOut = place<number>('UNMATCHED');

    const guarded = Transition.builder('Guarded')
      .inputs(one(input, (v: number) => v > 5))
      .outputs(outPlace(matchedOut))
      .priority(10)
      .action(async (ctx) => { ctx.output(matchedOut, ctx.input(input)); })
      .build();

    const fallback = Transition.builder('Fallback')
      .inputs(one(input))
      .outputs(outPlace(unmatchedOut))
      .priority(1)
      .action(async (ctx) => { ctx.output(unmatchedOut, ctx.input(input)); })
      .build();

    const net = PetriNet.builder('N').transitions(guarded, fallback).build();
    const { marking } = await runNet(net, initialTokens(
      [input, [tokenOf(3), tokenOf(10)]],
    ));

    // Token 10 matches guard → consumed by Guarded
    expect(marking.hasTokens(matchedOut)).toBe(true);
    expect(marking.peekFirst(matchedOut)!.value).toBe(10);
    // Token 3 doesn't match guard → consumed by Fallback
    expect(marking.hasTokens(unmatchedOut)).toBe(true);
    expect(marking.peekFirst(unmatchedOut)!.value).toBe(3);
  });
});

// ======================== DEADLINE ENFORCEMENT TESTS ========================

describe('Deadline Enforcement Tests', () => {
  it('transition with window timing fires within window', async () => {
    const input = place<string>('IN');
    const output = place<string>('OUT');

    const t = Transition.builder('Windowed')
      .inputs(one(input))
      .outputs(outPlace(output))
      .timing(window(50, 200))
      .action(async (ctx) => { ctx.output(output, ctx.input(input)); })
      .build();

    const net = PetriNet.builder('N').transition(t).build();
    const eventStore = new InMemoryEventStore();
    const startMs = performance.now();
    const { marking } = await runNet(net, initialTokens([input, [tokenOf('go')]]), { eventStore });
    const elapsed = performance.now() - startMs;

    // Should have waited at least 50ms (earliest) and fired successfully
    expect(elapsed).toBeGreaterThanOrEqual(45); // small tolerance
    expect(marking.hasTokens(output)).toBe(true);
    expect(marking.peekFirst(output)!.value).toBe('go');

    // No timeout events
    const timedOut = eventsOfType(eventStore, 'transition-timed-out');
    expect(timedOut.length).toBe(0);
  });

  it('deadline enforcement disables transition whose window expires while executor is busy', async () => {
    const input = place<string>('IN');
    const slowInput = place<string>('SLOW');
    const output = place<string>('OUT');
    const slowOut = place<string>('SLOW_OUT');

    // Windowed: enabled immediately (IN has token), window [100, 150].
    // Slow fires first (higher priority, immediate) with a synchronous busy-wait
    // of 200ms that blocks the event loop. The timer for Windowed's earliest (100ms)
    // is queued but can't execute. When the event loop unblocks at ~200ms, the
    // executor cycle runs and enforceDeadlines() detects: elapsed > latest → timed out.
    const windowed = Transition.builder('Windowed')
      .inputs(one(input))
      .outputs(outPlace(output))
      .timing(window(100, 150))
      .action(async (ctx) => { ctx.output(output, ctx.input(input)); })
      .build();

    const slow = Transition.builder('Slow')
      .inputs(one(slowInput))
      .outputs(outPlace(slowOut))
      .priority(100)
      .action(async (ctx) => {
        // Synchronous busy-wait blocks the event loop, preventing timer callbacks
        // from executing. This simulates the executor being unable to process cycles
        // during Windowed's firing window.
        const end = performance.now() + 200;
        while (performance.now() < end) { /* busy-wait */ }
        ctx.output(slowOut, ctx.input(slowInput));
      })
      .build();

    const net = PetriNet.builder('N').transitions(windowed, slow).build();
    const eventStore = new InMemoryEventStore();
    const { marking } = await runNet(net, initialTokens(
      [input, [tokenOf('val')]],
      [slowInput, [tokenOf('go')]],
    ), { eventStore });

    const timedOut = eventsOfType(eventStore, 'transition-timed-out');
    expect(timedOut.length).toBe(1);
    expect(timedOut[0]!.transitionName).toBe('Windowed');
    expect(timedOut[0]!.deadlineMs).toBe(150);
    expect(timedOut[0]!.actualDurationMs).toBeGreaterThan(150);

    // Windowed should NOT have produced output (it timed out)
    expect(marking.hasTokens(output)).toBe(false);
  });
});

// ======================== MARKING SNAPSHOT TESTS ========================

describe('Marking Snapshot Tests', () => {
  it('emits marking snapshots at start and completion', async () => {
    const input = place<string>('IN');
    const output = place<string>('OUT');

    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .action(async (ctx) => { ctx.output(output, ctx.input(input)); })
      .build();

    const net = PetriNet.builder('N').transition(t).build();
    const eventStore = new InMemoryEventStore();
    await runNet(net, initialTokens([input, [tokenOf('hello')]]), { eventStore });

    const snapshots = eventsOfType(eventStore, 'marking-snapshot');
    expect(snapshots.length).toBe(2);

    // First snapshot: initial marking (IN has a token)
    const initial = snapshots[0]!;
    expect(initial.marking.has('IN')).toBe(true);
    expect(initial.marking.get('IN')!.length).toBe(1);
    expect(initial.marking.get('IN')![0]!.value).toBe('hello');
    expect(initial.marking.has('OUT')).toBe(false);

    // Second snapshot: final marking (OUT has a token, IN is empty)
    const final = snapshots[1]!;
    expect(final.marking.has('OUT')).toBe(true);
    expect(final.marking.get('OUT')!.length).toBe(1);
    expect(final.marking.get('OUT')![0]!.value).toBe('hello');
    expect(final.marking.has('IN')).toBe(false);
  });

  it('marking snapshot only includes non-empty places', async () => {
    const a = place<string>('A');
    const b = place<string>('B');
    const c = place<string>('C');

    const t = Transition.builder('T')
      .inputs(one(a))
      .outputs(outPlace(b))
      .action(async (ctx) => { ctx.output(b, ctx.input(a)); })
      .build();

    const net = PetriNet.builder('N').transition(t).build();
    const eventStore = new InMemoryEventStore();
    await runNet(net, initialTokens([a, [tokenOf('val')]]), { eventStore });

    const snapshots = eventsOfType(eventStore, 'marking-snapshot');
    // Initial snapshot should only have A
    expect(snapshots[0]!.marking.size).toBe(1);
    // Final snapshot should only have B
    expect(snapshots[1]!.marking.size).toBe(1);
  });
});
