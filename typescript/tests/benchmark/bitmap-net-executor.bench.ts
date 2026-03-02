/**
 * Vitest benchmarks for BitmapNetExecutor performance scaling.
 *
 * Ports the same network topologies from the Java JMH benchmark suite:
 * - Sync linear chains (Promise.resolve actions, pure engine overhead)
 * - Async linear chains (setTimeout(0) based async actions)
 * - Mixed linear chains (first N async, rest sync)
 * - Parallel fan-out/fan-in
 * - Complex workflow (fork, XOR, read, inhibitor, priority, AND-join)
 */
import { bench, describe } from 'vitest';
import { BitmapNetExecutor } from '../../src/runtime/bitmap-net-executor.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import type { Place } from '../../src/core/place.js';
import { one, exactly } from '../../src/core/in.js';
import { outPlace, andPlaces, xor } from '../../src/core/out.js';
import { tokenOf } from '../../src/core/token.js';
import type { Token } from '../../src/core/token.js';
import { fork } from '../../src/core/transition-action.js';

// ==================== Helpers ====================

/**
 * Uses setImmediate instead of setTimeout(0). setImmediate fires after I/O callbacks
 * but before timers, bypassing the ~1ms minimum timer resolution. This exercises the
 * full macrotask → awaitWork → Promise.race → wake-up path without timer latency
 * dominating measurement. Node.js-specific; benchmarks run in Node via vitest bench.
 */
function yieldAsync(): Promise<void> {
  return new Promise<void>(r => setImmediate(r));
}

function initialTokens(...entries: [Place<any>, Token<any>[]][]): Map<Place<any>, Token<any>[]> {
  return new Map(entries);
}

async function runNet(net: PetriNet, start: Place<string>): Promise<void> {
  const executor = new BitmapNetExecutor(net, initialTokens([start, [tokenOf('start')]]));
  await executor.run(5000);
}

// ==================== Network Builders ====================

interface NetWithStart {
  net: PetriNet;
  start: Place<string>;
}

/**
 * Sync linear chain: start -> t1 -> p1 -> t2 -> ... -> end
 * All actions use Promise.resolve() — isolates pure engine overhead.
 */
function buildSyncLinearChain(transitions: number): NetWithStart {
  const start = place<string>('sync_start');
  const places: Place<string>[] = [start];
  for (let i = 1; i <= transitions; i++) {
    places.push(place<string>(`sync_p${i}`));
  }

  const builder = PetriNet.builder(`SyncLinear${transitions}`);
  for (let i = 0; i < transitions; i++) {
    const to = places[i + 1]!;
    builder.transition(
      Transition.builder(`sync_t${i + 1}`)
        .inputs(one(places[i]!))
        .outputs(outPlace(to))
        .action(async (ctx) => {
          ctx.output(to, 'v');
        })
        .build()
    );
  }

  return { net: builder.build(), start };
}

/**
 * Async linear chain: same topology but actions use setTimeout(0)
 * to exercise the full async completion → wake-up path.
 */
function buildAsyncLinearChain(transitions: number): NetWithStart {
  const start = place<string>('start');
  const places: Place<string>[] = [start];
  for (let i = 1; i <= transitions; i++) {
    places.push(place<string>(`p${i}`));
  }

  const builder = PetriNet.builder(`AsyncLinear${transitions}`);
  for (let i = 0; i < transitions; i++) {
    const to = places[i + 1]!;
    builder.transition(
      Transition.builder(`t${i + 1}`)
        .inputs(one(places[i]!))
        .outputs(outPlace(to))
        .action(async (ctx) => {
          await yieldAsync();
          ctx.output(to, 'v');
        })
        .build()
    );
  }

  return { net: builder.build(), start };
}

/**
 * Mixed linear chain: first `asyncCount` transitions use setTimeout(0),
 * rest use Promise.resolve(). Models I/O at entry boundary + in-memory logic.
 */
function buildMixedLinearChain(total: number, asyncCount: number): NetWithStart {
  const start = place<string>('mix_start');
  const places: Place<string>[] = [start];
  for (let i = 1; i <= total; i++) {
    places.push(place<string>(`mix_p${i}`));
  }

  const builder = PetriNet.builder(`MixedLinear${total}_${asyncCount}async`);
  for (let i = 0; i < total; i++) {
    const to = places[i + 1]!;
    const isAsync = i < asyncCount;
    builder.transition(
      Transition.builder(`mix_t${i + 1}`)
        .inputs(one(places[i]!))
        .outputs(outPlace(to))
        .action(async (ctx) => {
          if (isAsync) await yieldAsync();
          ctx.output(to, 'v');
        })
        .build()
    );
  }

  return { net: builder.build(), start };
}

/**
 * Parallel fan-out/fan-in: start -> fork -> [branch0..N-1] -> [work0..N-1] -> join -> end
 */
function buildParallelFanOut(branches: number): NetWithStart {
  const start = place<string>('pstart');
  const joinPlace = place<string>('pjoin');
  const end = place<string>('pend');

  const branchPlaces: Place<string>[] = [];
  for (let i = 0; i < branches; i++) {
    branchPlaces.push(place<string>(`branch${i}`));
  }

  const forkTrans = Transition.builder('fork')
    .inputs(one(start))
    .outputs(andPlaces(...branchPlaces))
    .action(fork())
    .build();

  const builder = PetriNet.builder(`Parallel${branches}`).transition(forkTrans);

  for (let i = 0; i < branches; i++) {
    const bp = branchPlaces[i]!;
    builder.transition(
      Transition.builder(`work${i}`)
        .inputs(one(bp))
        .outputs(outPlace(joinPlace))
        .action(async (ctx) => {
          await yieldAsync();
          ctx.output(joinPlace, 'v');
        })
        .build()
    );
  }

  const joinTrans = Transition.builder('join')
    .inputs(exactly(branches, joinPlace))
    .outputs(outPlace(end))
    .action(async (ctx) => {
      await yieldAsync();
      ctx.output(end, 'done');
    })
    .build();

  builder.transition(joinTrans);

  return { net: builder.build(), start };
}

/**
 * Complex workflow: 8 transitions, 13 places.
 * Exercises fork, XOR output, read arcs, inhibitor arcs, priority, AND-join.
 */
function buildComplexWorkflow(): NetWithStart {
  const v_input = place<string>('v_input');
  const v_guardIn = place<string>('v_guardIn');
  const v_intentIn = place<string>('v_intentIn');
  const v_searchIn = place<string>('v_searchIn');
  const v_outputGuardIn = place<string>('v_outputGuardIn');
  const v_guardSafe = place<string>('v_guardSafe');
  const v_guardViolation = place<string>('v_guardViolation');
  const v_violated = place<string>('v_violated');
  const v_intentReady = place<string>('v_intentReady');
  const v_topicReady = place<string>('v_topicReady');
  const v_searchReady = place<string>('v_searchReady');
  const v_outputGuardDone = place<string>('v_outputGuardDone');
  const v_response = place<string>('v_response');

  // T1: Fork (1-to-4 fan-out)
  const forkTrans = Transition.builder('Fork')
    .inputs(one(v_input))
    .outputs(andPlaces(v_guardIn, v_intentIn, v_searchIn, v_outputGuardIn))
    .action(fork())
    .build();

  // T2: Guard (XOR output - safe or violation)
  const guardTrans = Transition.builder('Guard')
    .inputs(one(v_guardIn))
    .outputs(xor(outPlace(v_guardSafe), outPlace(v_guardViolation)))
    .action(async (ctx) => {
      await yieldAsync();
      ctx.output(v_guardSafe, 'safe');
    })
    .build();

  // T3: HandleViolation (inhibited by v_guardSafe — won't fire in normal path)
  const handleViolation = Transition.builder('HandleViolation')
    .inputs(one(v_guardViolation))
    .outputs(outPlace(v_violated))
    .inhibitor(v_guardSafe)
    .action(async (ctx) => {
      ctx.output(v_violated, 'violated');
    })
    .build();

  // T4: Intent
  const intentTrans = Transition.builder('Intent')
    .inputs(one(v_intentIn))
    .outputs(outPlace(v_intentReady))
    .action(async (ctx) => {
      await yieldAsync();
      ctx.output(v_intentReady, 'intent');
    })
    .build();

  // T5: TopicKnowledge
  const topicTrans = Transition.builder('TopicKnowledge')
    .inputs(one(v_intentReady))
    .outputs(outPlace(v_topicReady))
    .action(async (ctx) => {
      await yieldAsync();
      ctx.output(v_topicReady, 'topic');
    })
    .build();

  // T6: Search (read intentReady, inhibited by guardViolation, low priority)
  const searchTrans = Transition.builder('Search')
    .inputs(one(v_searchIn))
    .outputs(outPlace(v_searchReady))
    .read(v_intentReady)
    .inhibitor(v_guardViolation)
    .priority(-5)
    .action(async (ctx) => {
      await yieldAsync();
      ctx.output(v_searchReady, 'results');
    })
    .build();

  // T7: OutputGuard (reads guardSafe)
  const outputGuardTrans = Transition.builder('OutputGuard')
    .inputs(one(v_outputGuardIn))
    .outputs(outPlace(v_outputGuardDone))
    .read(v_guardSafe)
    .action(async (ctx) => {
      await yieldAsync();
      ctx.output(v_outputGuardDone, 'checked');
    })
    .build();

  // T8: Compose (AND-join of 3 parallel paths, high priority)
  const composeTrans = Transition.builder('Compose')
    .inputs(one(v_guardSafe), one(v_searchReady), one(v_topicReady))
    .outputs(outPlace(v_response))
    .priority(10)
    .action(async (ctx) => {
      await yieldAsync();
      ctx.output(v_response, 'composed');
    })
    .build();

  const net = PetriNet.builder('ComplexWorkflow')
    .transition(forkTrans)
    .transition(guardTrans)
    .transition(handleViolation)
    .transition(intentTrans)
    .transition(topicTrans)
    .transition(searchTrans)
    .transition(outputGuardTrans)
    .transition(composeTrans)
    .build();

  return { net, start: v_input };
}

// ==================== Pre-built Networks ====================

const syncLinear10 = buildSyncLinearChain(10);
const syncLinear20 = buildSyncLinearChain(20);
const syncLinear50 = buildSyncLinearChain(50);
const syncLinear100 = buildSyncLinearChain(100);
const syncLinear200 = buildSyncLinearChain(200);
const syncLinear500 = buildSyncLinearChain(500);

const asyncLinear5 = buildAsyncLinearChain(5);
const asyncLinear10 = buildAsyncLinearChain(10);
const asyncLinear20 = buildAsyncLinearChain(20);
const asyncLinear50 = buildAsyncLinearChain(50);
const asyncLinear100 = buildAsyncLinearChain(100);
const asyncLinear200 = buildAsyncLinearChain(200);
const asyncLinear500 = buildAsyncLinearChain(500);

const mixedLinear10 = buildMixedLinearChain(10, 2);
const mixedLinear20 = buildMixedLinearChain(20, 2);
const mixedLinear50 = buildMixedLinearChain(50, 2);
const mixedLinear100 = buildMixedLinearChain(100, 2);
const mixedLinear200 = buildMixedLinearChain(200, 2);
const mixedLinear500 = buildMixedLinearChain(500, 2);

const parallel5 = buildParallelFanOut(5);
const parallel10 = buildParallelFanOut(10);
const parallel20 = buildParallelFanOut(20);

const complex = buildComplexWorkflow();

// ==================== Sync Linear Benchmarks ====================

describe('sync linear chain', () => {
  bench('10 transitions', () => runNet(syncLinear10.net, syncLinear10.start));
  bench('20 transitions', () => runNet(syncLinear20.net, syncLinear20.start));
  bench('50 transitions', () => runNet(syncLinear50.net, syncLinear50.start));
  bench('100 transitions', () => runNet(syncLinear100.net, syncLinear100.start));
  bench('200 transitions', () => runNet(syncLinear200.net, syncLinear200.start));
  bench('500 transitions', () => runNet(syncLinear500.net, syncLinear500.start));
});

// ==================== Async Linear Benchmarks ====================

describe('async linear chain', () => {
  bench('5 transitions', () => runNet(asyncLinear5.net, asyncLinear5.start));
  bench('10 transitions', () => runNet(asyncLinear10.net, asyncLinear10.start));
  bench('20 transitions', () => runNet(asyncLinear20.net, asyncLinear20.start));
  bench('50 transitions', () => runNet(asyncLinear50.net, asyncLinear50.start));
  bench('100 transitions', () => runNet(asyncLinear100.net, asyncLinear100.start));
  bench('200 transitions', () => runNet(asyncLinear200.net, asyncLinear200.start));
  bench('500 transitions', () => runNet(asyncLinear500.net, asyncLinear500.start));
});

// ==================== Mixed Linear Benchmarks ====================

describe('mixed linear chain (2 async)', () => {
  bench('10 transitions', () => runNet(mixedLinear10.net, mixedLinear10.start));
  bench('20 transitions', () => runNet(mixedLinear20.net, mixedLinear20.start));
  bench('50 transitions', () => runNet(mixedLinear50.net, mixedLinear50.start));
  bench('100 transitions', () => runNet(mixedLinear100.net, mixedLinear100.start));
  bench('200 transitions', () => runNet(mixedLinear200.net, mixedLinear200.start));
  bench('500 transitions', () => runNet(mixedLinear500.net, mixedLinear500.start));
});

// ==================== Parallel Fan-Out Benchmarks ====================

describe('parallel fan-out', () => {
  bench('5 branches', () => runNet(parallel5.net, parallel5.start));
  bench('10 branches', () => runNet(parallel10.net, parallel10.start));
  bench('20 branches', () => runNet(parallel20.net, parallel20.start));
});

// ==================== Complex Workflow Benchmark ====================

describe('complex workflow', () => {
  bench('8 transitions, 13 places', () => runNet(complex.net, complex.start));
});
