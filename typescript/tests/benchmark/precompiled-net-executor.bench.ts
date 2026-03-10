/**
 * Vitest benchmarks for PrecompiledNetExecutor performance scaling.
 *
 * Same network topologies as BitmapNetExecutor benchmarks for direct comparison.
 * Programs are pre-compiled to isolate execution cost from compilation cost.
 */
import { bench, describe } from 'vitest';
import { PrecompiledNet } from '../../src/runtime/precompiled-net.js';
import { PrecompiledNetExecutor } from '../../src/runtime/precompiled-net-executor.js';
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
} from './benchmark-networks.js';

// ==================== Helpers ====================

async function runNet(
  net: PetriNet,
  start: import('../../src/core/place.js').Place<string>,
  program: PrecompiledNet,
): Promise<void> {
  const executor = new PrecompiledNetExecutor(net, initialTokens([start, [tokenOf('start')]]), { program });
  await executor.run(5000);
}

// ==================== Pre-built Networks & Programs ====================

const syncLinear10 = buildSyncLinearChain(10);
const syncLinear20 = buildSyncLinearChain(20);
const syncLinear50 = buildSyncLinearChain(50);
const syncLinear100 = buildSyncLinearChain(100);
const syncLinear200 = buildSyncLinearChain(200);
const syncLinear500 = buildSyncLinearChain(500);

const syncLinear10Prog = PrecompiledNet.compile(syncLinear10.net);
const syncLinear20Prog = PrecompiledNet.compile(syncLinear20.net);
const syncLinear50Prog = PrecompiledNet.compile(syncLinear50.net);
const syncLinear100Prog = PrecompiledNet.compile(syncLinear100.net);
const syncLinear200Prog = PrecompiledNet.compile(syncLinear200.net);
const syncLinear500Prog = PrecompiledNet.compile(syncLinear500.net);

const asyncLinear5 = buildAsyncLinearChain(5);
const asyncLinear10 = buildAsyncLinearChain(10);
const asyncLinear20 = buildAsyncLinearChain(20);
const asyncLinear50 = buildAsyncLinearChain(50);
const asyncLinear100 = buildAsyncLinearChain(100);
const asyncLinear200 = buildAsyncLinearChain(200);
const asyncLinear500 = buildAsyncLinearChain(500);

const asyncLinear5Prog = PrecompiledNet.compile(asyncLinear5.net);
const asyncLinear10Prog = PrecompiledNet.compile(asyncLinear10.net);
const asyncLinear20Prog = PrecompiledNet.compile(asyncLinear20.net);
const asyncLinear50Prog = PrecompiledNet.compile(asyncLinear50.net);
const asyncLinear100Prog = PrecompiledNet.compile(asyncLinear100.net);
const asyncLinear200Prog = PrecompiledNet.compile(asyncLinear200.net);
const asyncLinear500Prog = PrecompiledNet.compile(asyncLinear500.net);

const mixedLinear10 = buildMixedLinearChain(10, 2);
const mixedLinear20 = buildMixedLinearChain(20, 2);
const mixedLinear50 = buildMixedLinearChain(50, 2);
const mixedLinear100 = buildMixedLinearChain(100, 2);
const mixedLinear200 = buildMixedLinearChain(200, 2);
const mixedLinear500 = buildMixedLinearChain(500, 2);

const mixedLinear10Prog = PrecompiledNet.compile(mixedLinear10.net);
const mixedLinear20Prog = PrecompiledNet.compile(mixedLinear20.net);
const mixedLinear50Prog = PrecompiledNet.compile(mixedLinear50.net);
const mixedLinear100Prog = PrecompiledNet.compile(mixedLinear100.net);
const mixedLinear200Prog = PrecompiledNet.compile(mixedLinear200.net);
const mixedLinear500Prog = PrecompiledNet.compile(mixedLinear500.net);

const parallel5 = buildParallelFanOut(5);
const parallel10 = buildParallelFanOut(10);
const parallel20 = buildParallelFanOut(20);

const parallel5Prog = PrecompiledNet.compile(parallel5.net);
const parallel10Prog = PrecompiledNet.compile(parallel10.net);
const parallel20Prog = PrecompiledNet.compile(parallel20.net);

const complex = buildComplexWorkflow();
const complexProg = PrecompiledNet.compile(complex.net);

// ==================== Sync Linear Benchmarks ====================

describe('sync linear chain', () => {
  bench('10 transitions', () => runNet(syncLinear10.net, syncLinear10.start, syncLinear10Prog));
  bench('20 transitions', () => runNet(syncLinear20.net, syncLinear20.start, syncLinear20Prog));
  bench('50 transitions', () => runNet(syncLinear50.net, syncLinear50.start, syncLinear50Prog));
  bench('100 transitions', () => runNet(syncLinear100.net, syncLinear100.start, syncLinear100Prog));
  bench('200 transitions', () => runNet(syncLinear200.net, syncLinear200.start, syncLinear200Prog));
  bench('500 transitions', () => runNet(syncLinear500.net, syncLinear500.start, syncLinear500Prog));
});

// ==================== Async Linear Benchmarks ====================

describe('async linear chain', () => {
  bench('5 transitions', () => runNet(asyncLinear5.net, asyncLinear5.start, asyncLinear5Prog));
  bench('10 transitions', () => runNet(asyncLinear10.net, asyncLinear10.start, asyncLinear10Prog));
  bench('20 transitions', () => runNet(asyncLinear20.net, asyncLinear20.start, asyncLinear20Prog));
  bench('50 transitions', () => runNet(asyncLinear50.net, asyncLinear50.start, asyncLinear50Prog));
  bench('100 transitions', () => runNet(asyncLinear100.net, asyncLinear100.start, asyncLinear100Prog));
  bench('200 transitions', () => runNet(asyncLinear200.net, asyncLinear200.start, asyncLinear200Prog));
  bench('500 transitions', () => runNet(asyncLinear500.net, asyncLinear500.start, asyncLinear500Prog));
});

// ==================== Mixed Linear Benchmarks ====================

describe('mixed linear chain (2 async)', () => {
  bench('10 transitions', () => runNet(mixedLinear10.net, mixedLinear10.start, mixedLinear10Prog));
  bench('20 transitions', () => runNet(mixedLinear20.net, mixedLinear20.start, mixedLinear20Prog));
  bench('50 transitions', () => runNet(mixedLinear50.net, mixedLinear50.start, mixedLinear50Prog));
  bench('100 transitions', () => runNet(mixedLinear100.net, mixedLinear100.start, mixedLinear100Prog));
  bench('200 transitions', () => runNet(mixedLinear200.net, mixedLinear200.start, mixedLinear200Prog));
  bench('500 transitions', () => runNet(mixedLinear500.net, mixedLinear500.start, mixedLinear500Prog));
});

// ==================== Parallel Fan-Out Benchmarks ====================

describe('parallel fan-out', () => {
  bench('5 branches', () => runNet(parallel5.net, parallel5.start, parallel5Prog));
  bench('10 branches', () => runNet(parallel10.net, parallel10.start, parallel10Prog));
  bench('20 branches', () => runNet(parallel20.net, parallel20.start, parallel20Prog));
});

// ==================== Complex Workflow Benchmark ====================

describe('complex workflow', () => {
  bench('8 transitions, 13 places', () => runNet(complex.net, complex.start, complexProg));
});

// ==================== Event Store Overhead ====================

describe('event store overhead', () => {
  bench('noop event store', async () => {
    const executor = new PrecompiledNetExecutor(complex.net, initialTokens([complex.start, [tokenOf('start')]]), {
      eventStore: noopEventStore(),
      program: complexProg,
    });
    await executor.run(5000);
  });

  bench('inMemory event store', async () => {
    const executor = new PrecompiledNetExecutor(complex.net, initialTokens([complex.start, [tokenOf('start')]]), {
      eventStore: new InMemoryEventStore(),
      program: complexProg,
    });
    await executor.run(5000);
  });
});

// ==================== Compilation Benchmark ====================

describe('compilation', () => {
  for (const n of [10, 50, 100, 500]) {
    const { transitions } = buildCompilationTransitions(n);

    bench(`${n} transitions (CompiledNet + PrecompiledNet)`, () => {
      const net = PetriNet.builder(`Compile${n}`).transitions(...transitions).build();
      PrecompiledNet.compile(net);
    });
  }
});
