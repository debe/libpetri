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
import { tokenOf } from '../../src/core/token.js';
import { InMemoryEventStore } from '../../src/event/event-store.js';
import { noopEventStore } from '../../src/event/event-store.js';
import {
  initialTokens,
  buildSyncLinearChain,
  buildAsyncLinearChain,
  buildMixedLinearChain,
  buildParallelFanOut,
  buildComplexWorkflow,
  buildCompilationTransitions,
  buildNuJoinDrain,
  buildPlainJoinDrain,
  buildNuScatterGather,
} from './benchmark-networks.js';
import type { NetWithSeed } from './benchmark-networks.js';

// ==================== Helpers ====================

async function runNet(net: PetriNet, start: import('../../src/core/place.js').Place<string>): Promise<void> {
  const executor = new BitmapNetExecutor(net, initialTokens([start, [tokenOf('start')]]));
  await executor.run(5000);
}

/** Runs a ν-net scenario with a fresh pre-seeded marking each invocation. */
async function runNu(nws: NetWithSeed): Promise<void> {
  const executor = new BitmapNetExecutor(nws.net, nws.seed());
  await executor.run(5000);
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

const mixedLinear10 = buildMixedLinearChain(10);
const mixedLinear20 = buildMixedLinearChain(20);
const mixedLinear50 = buildMixedLinearChain(50);
const mixedLinear100 = buildMixedLinearChain(100);
const mixedLinear200 = buildMixedLinearChain(200);
const mixedLinear500 = buildMixedLinearChain(500);

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

describe('mixed linear chain (~2% sync, rest async)', () => {
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

// ==================== Event Store Overhead ====================

describe('event store overhead', () => {
  bench('noop event store', async () => {
    const executor = new BitmapNetExecutor(complex.net, initialTokens([complex.start, [tokenOf('start')]]), {
      eventStore: noopEventStore(),
    });
    await executor.run(5000);
  });

  bench('inMemory event store', async () => {
    const executor = new BitmapNetExecutor(complex.net, initialTokens([complex.start, [tokenOf('start')]]), {
      eventStore: new InMemoryEventStore(),
    });
    await executor.run(5000);
  });
});

// ==================== Compilation Benchmark ====================

describe('compilation', () => {
  for (const n of [10, 50, 100, 500]) {
    const { transitions } = buildCompilationTransitions(n);

    bench(`${n} transitions`, () => {
      const net = PetriNet.builder(`Compile${n}`).transitions(...transitions).build();
      const _executor = new BitmapNetExecutor(net, new Map());
    });
  }
});

// ==================== ν-net Firing-Check Benchmarks (NU-020/021/040) ====================

const nuDrainDepth = [10, 50, 100, 200, 500].map((d) => ({ d, nws: buildNuJoinDrain(2, d) }));
const nuDrainArity = [4, 8].map((k) => ({ k, nws: buildNuJoinDrain(k, 100) }));
const plainDrainDepth = [10, 50, 100, 200, 500].map((d) => ({ d, nws: buildPlainJoinDrain(d) }));
const nuDrainGuarded = [10, 50, 100, 200, 500].map((d) => ({ d, nws: buildNuJoinDrain(2, d, true) }));
const nuScatter = [10, 50, 100].map((g) => ({ g, nws: buildNuScatterGather(g) }));
const nuScatterBudgeted = [10, 50, 100].map((g) => ({ g, nws: buildNuScatterGather(g, true) }));

// Primary cost curve: re-indexing a draining pool is ~quadratic in pool depth.
describe('ν-net join drain (k=2, by pool depth)', () => {
  for (const { d, nws } of nuDrainDepth) bench(`depth ${d}`, () => runNu(nws));
});

// Baseline: identical topology/marking with NO match — the delta is the ν tax.
describe('plain join drain (k=2, baseline, no match)', () => {
  for (const { d, nws } of plainDrainDepth) bench(`depth ${d}`, () => runNu(nws));
});

// Arity axis: cost is ~linear in the number of correlated inputs (depth=100).
describe('ν-net join drain (depth=100, by arity)', () => {
  for (const { k, nws } of nuDrainArity) bench(`arity ${k}`, () => runNu(nws));
});

// NU-021 guard: per-token guard eval added to the index-building loop.
describe('ν-net join drain guarded (k=2, by pool depth)', () => {
  for (const { d, nws } of nuDrainGuarded) bench(`depth ${d}`, () => runNu(nws));
});

// Realistic fork(freshName)/join end-to-end.
describe('ν-net scatter/gather (by group count)', () => {
  for (const { g, nws } of nuScatter) bench(`${g} groups`, () => runNu(nws));
});

// NU-040 budget bounds live groups → shallow pools → cheap match check.
describe('ν-net scatter/gather budgeted (by group count)', () => {
  for (const { g, nws } of nuScatterBudgeted) bench(`${g} groups`, () => runNu(nws));
});
