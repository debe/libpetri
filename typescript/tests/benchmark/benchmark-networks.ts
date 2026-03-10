/**
 * Shared network builders for benchmark suites.
 *
 * Extracted so both BitmapNetExecutor and PrecompiledNetExecutor benchmarks
 * use identical network topologies.
 */
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import type { Place } from '../../src/core/place.js';
import { one, exactly } from '../../src/core/in.js';
import { outPlace, andPlaces, xor } from '../../src/core/out.js';
import type { Token } from '../../src/core/token.js';
import { fork } from '../../src/core/transition-action.js';

// ==================== Helpers ====================

/**
 * Uses setImmediate instead of setTimeout(0). setImmediate fires after I/O callbacks
 * but before timers, bypassing the ~1ms minimum timer resolution. This exercises the
 * full macrotask → awaitWork → Promise.race → wake-up path without timer latency
 * dominating measurement. Node.js-specific; benchmarks run in Node via vitest bench.
 */
export function yieldAsync(): Promise<void> {
  return new Promise<void>(r => setImmediate(r));
}

export function initialTokens(...entries: [Place<any>, Token<any>[]][]): Map<Place<any>, Token<any>[]> {
  return new Map(entries);
}

export interface NetWithStart {
  net: PetriNet;
  start: Place<string>;
}

// ==================== Network Builders ====================

/**
 * Sync linear chain: start -> t1 -> p1 -> t2 -> ... -> end
 * All actions use Promise.resolve() — isolates pure engine overhead.
 */
export function buildSyncLinearChain(transitions: number): NetWithStart {
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
export function buildAsyncLinearChain(transitions: number): NetWithStart {
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
export function buildMixedLinearChain(total: number, asyncCount: number): NetWithStart {
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
export function buildParallelFanOut(branches: number): NetWithStart {
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
export function buildComplexWorkflow(): NetWithStart {
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

  const forkTrans = Transition.builder('Fork')
    .inputs(one(v_input))
    .outputs(andPlaces(v_guardIn, v_intentIn, v_searchIn, v_outputGuardIn))
    .action(fork())
    .build();

  const guardTrans = Transition.builder('Guard')
    .inputs(one(v_guardIn))
    .outputs(xor(outPlace(v_guardSafe), outPlace(v_guardViolation)))
    .action(async (ctx) => {
      await yieldAsync();
      ctx.output(v_guardSafe, 'safe');
    })
    .build();

  const handleViolation = Transition.builder('HandleViolation')
    .inputs(one(v_guardViolation))
    .outputs(outPlace(v_violated))
    .inhibitor(v_guardSafe)
    .action(async (ctx) => {
      ctx.output(v_violated, 'violated');
    })
    .build();

  const intentTrans = Transition.builder('Intent')
    .inputs(one(v_intentIn))
    .outputs(outPlace(v_intentReady))
    .action(async (ctx) => {
      await yieldAsync();
      ctx.output(v_intentReady, 'intent');
    })
    .build();

  const topicTrans = Transition.builder('TopicKnowledge')
    .inputs(one(v_intentReady))
    .outputs(outPlace(v_topicReady))
    .action(async (ctx) => {
      await yieldAsync();
      ctx.output(v_topicReady, 'topic');
    })
    .build();

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

  const outputGuardTrans = Transition.builder('OutputGuard')
    .inputs(one(v_outputGuardIn))
    .outputs(outPlace(v_outputGuardDone))
    .read(v_guardSafe)
    .action(async (ctx) => {
      await yieldAsync();
      ctx.output(v_outputGuardDone, 'checked');
    })
    .build();

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

// ==================== Compilation Helpers ====================

export function buildCompilationTransitions(n: number): { places: Place<string>[]; transitions: Transition[] } {
  const places: Place<string>[] = [];
  for (let i = 0; i <= n; i++) {
    places.push(place<string>(`cp${i}`));
  }
  const transitions: Transition[] = [];
  for (let i = 0; i < n; i++) {
    const to = places[i + 1]!;
    transitions.push(
      Transition.builder(`ct${i}`)
        .inputs(one(places[i]!))
        .outputs(outPlace(to))
        .action(fork())
        .build()
    );
  }
  return { places, transitions };
}
