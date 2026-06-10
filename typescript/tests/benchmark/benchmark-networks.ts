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
import { tokenOf, tokenAt } from '../../src/core/token.js';
import { matchSpec, matchKey } from '../../src/core/match-spec.js';
import { nameId } from '../../src/core/name.js';
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
 * Mixed linear chain: ~2% of transitions are synchronous fast-paths
 * (in-memory decisions, guard checks); the rest are async (I/O, network,
 * LLM calls). Models the common real-world workload shape.
 * Formula: `syncCount = floor(total / 50)` — N=50 → 1 sync, N=100 → 2 sync,
 * N=500 → 10 sync; chains of N ≤ 20 are 100% async (formula rounds to zero).
 */
export function buildMixedLinearChain(total: number): NetWithStart {
  const syncCount = Math.floor(total / 50);
  const start = place<string>('mix_start');
  const places: Place<string>[] = [start];
  for (let i = 1; i <= total; i++) {
    places.push(place<string>(`mix_p${i}`));
  }

  const builder = PetriNet.builder(`MixedLinear${total}`);
  for (let i = 0; i < total; i++) {
    const to = places[i + 1]!;
    const isSync = i < syncCount;
    builder.transition(
      Transition.builder(`mix_t${i + 1}`)
        .inputs(one(places[i]!))
        .outputs(outPlace(to))
        .action(async (ctx) => {
          if (!isSync) await yieldAsync();
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

// ==================== ν-net Builders (spec NU-020/021/040) ====================
//
// A transition carrying a MatchSpec is enabled only when a single correlation
// name is present in every correlated input (`findBinding` → `selectMatchName`).
// Unlike the cardinality check, that re-builds a `name → {count, oldest}` index
// over EVERY token in each correlated input on each enablement re-evaluation —
// so draining a deep pool re-indexes the shrinking pool every fire (≈ O(k·depth²)).
// These builders feed benchmarks that quantify that firing-check cost. The
// `hasMatch[tid]` gate means non-ν transitions pay nothing.

export interface NuMsg {
  cid: string;
}

/** A net plus a factory that builds a FRESH pre-seeded marking per invocation. */
export interface NetWithSeed {
  net: PetriNet;
  seed: () => Map<Place<any>, Token<any>[]>;
}

/** Seeds each correlated input with `depth` distinct, mutually-correlating cids. */
function seedDrain(inputs: Place<NuMsg>[], depth: number): () => Map<Place<any>, Token<any>[]> {
  return () => {
    const m = new Map<Place<any>, Token<any>[]>();
    for (const p of inputs) {
      const toks: Token<NuMsg>[] = [];
      for (let j = 0; j < depth; j++) toks.push(tokenAt({ cid: `c${j}` }, j));
      m.set(p, toks);
    }
    return m;
  };
}

/**
 * ν-net join over `branches` correlated inputs, each pre-seeded with `depth`
 * distinct-cid tokens, drained to a sink. The join fires once per correlation
 * name, re-running the name-index build over the shrinking pool each fire.
 * `guarded` adds a unary input filter (NU-021) so the per-token guard-eval cost
 * is included.
 */
export function buildNuJoinDrain(branches: number, depth: number, guarded = false): NetWithSeed {
  const inputs: Place<NuMsg>[] = [];
  for (let i = 0; i < branches; i++) inputs.push(place<NuMsg>(`branch${i}`));
  const merged = place<string>('merged');

  const join = Transition.builder('join')
    .inputs(...inputs.map((p) => (guarded ? one(p, (m: NuMsg) => m.cid !== 'skip') : one(p))))
    .match(matchSpec(...inputs.map((p) => matchKey(p, (m: NuMsg) => nameId(m.cid)))))
    .outputs(outPlace(merged))
    .action(async (ctx) => {
      ctx.output(merged, 'm');
    })
    .build();

  const net = PetriNet.builder('NuJoinDrain').transition(join).build();
  return { net, seed: seedDrain(inputs, depth) };
}

/**
 * Structurally identical to `buildNuJoinDrain(2, depth)` but the join has NO
 * MatchSpec — a plain FIFO 2-way join. Same firing count and token movement,
 * zero name indexing: the gap to `buildNuJoinDrain` is the pure ν firing-check tax.
 */
export function buildPlainJoinDrain(depth: number): NetWithSeed {
  const a = place<NuMsg>('branch0');
  const b = place<NuMsg>('branch1');
  const merged = place<string>('merged');

  const join = Transition.builder('join')
    .inputs(one(a), one(b))
    .outputs(outPlace(merged))
    .action(async (ctx) => {
      ctx.output(merged, 'm');
    })
    .build();

  const net = PetriNet.builder('PlainJoinDrain').transition(join).build();
  return { net, seed: seedDrain([a, b], depth) };
}

/**
 * Realistic end-to-end ν-net: `fork` mints a fresh correlation id (NU-010) and
 * stamps two siblings; the `.match()` join re-merges them (NU-020). When
 * `budgeted`, a `budget` place (k=1) caps live fork groups (NU-040): the fork
 * consumes a budget token and the join returns it, keeping the branch pools
 * shallow and the match check cheap.
 */
export function buildNuScatterGather(groups: number, budgeted = false): NetWithSeed {
  const source = place<number>('source');
  const budget = place<number>('budget');
  const a = place<NuMsg>('branchA');
  const b = place<NuMsg>('branchB');
  const merged = place<string>('merged');

  const fork = Transition.builder('fork')
    .inputs(...(budgeted ? [one(source), one(budget)] : [one(source)]))
    .outputs(andPlaces(a, b))
    .action(async (ctx) => {
      const id = ctx.freshName();
      ctx.output(a, { cid: id });
      ctx.output(b, { cid: id });
    })
    .build();

  const join = Transition.builder('join')
    .inputs(one(a), one(b))
    .match(matchSpec(matchKey(a, (m: NuMsg) => nameId(m.cid)), matchKey(b, (m: NuMsg) => nameId(m.cid))))
    .outputs(budgeted ? andPlaces(merged, budget) : outPlace(merged))
    .action(async (ctx) => {
      ctx.output(merged, ctx.input(a).cid);
      if (budgeted) ctx.output(budget, 0);
    })
    .build();

  const net = PetriNet.builder('NuScatterGather').transitions(fork, join).build();
  const seed = () => {
    const m = new Map<Place<any>, Token<any>[]>();
    const src: Token<number>[] = [];
    for (let j = 0; j < groups; j++) src.push(tokenOf(0));
    m.set(source, src);
    if (budgeted) m.set(budget, [tokenOf(0)]);
    return m;
  };
  return { net, seed };
}
