/**
 * Regression: the sparse enablement index must hold any word index. It was an `Int8Array`,
 * so a transition whose needs- or inhibitor-mask sits in a single word at index 128 or above
 * (place id 4096+) stored a wrapped negative index. Negative reads as SPARSE_MULTI with empty
 * sparse lists, so the needs check passed with the place empty and the inhibitor never blocked;
 * word 254 wrapped to -2 and read as SPARSE_EMPTY. On a 4098-place chain the spuriously enabled
 * last transition failed synchronously on its missing input, re-dirtied itself and spun the
 * orchestrator without yielding, so no `run(timeoutMs)` could fire (PERF-042). Found by
 * mastra-libpetri.
 *
 * The needs cases assert on `canEnableSparse` directly: driving them through the executor
 * would hang the suite on regression rather than fail it. The inhibitor case keeps its input in
 * word 0, so it terminates either way and runs end to end. Place ids are assigned in transition reference order, so filler
 * sink transitions push the places under test to the target word; the ids are asserted.
 */
import { describe, it, expect } from 'vitest';
import {
  PetriNet, Transition, PrecompiledNet, PrecompiledNetExecutor,
  place, one, outPlace, fork, tokenOf,
} from '../../src/index.js';
import type { Place } from '../../src/index.js';

function places(n: number): Place<number>[] {
  return Array.from({ length: n }, (_, i) => place<number>(`p${i}`));
}

/** Sink transitions consuming `ps[0..n)` in order, each claiming the next place id. */
function fillers(ps: Place<number>[], n: number): Transition[] {
  const out: Transition[] = [];
  for (let i = 0; i < n; i++) {
    out.push(Transition.builder(`f${i}`).inputs(one(ps[i]!)).build());
  }
  return out;
}

describe('PrecompiledNet.canEnableSparse with a word index above 127', () => {
  // 127 is the last index an Int8 held; 128 wrapped to -128 (SPARSE_MULTI branch),
  // 254 to -2 (SPARSE_EMPTY) and 255 to -1 (SPARSE_MULTI).
  for (const word of [127, 128, 254, 255]) {
    it(`single-word needs mask in word ${word} tracks its place`, () => {
      const pid = word * 32;
      const ps = places(pid + 2);
      const t = Transition.builder('t')
        .inputs(one(ps[pid]!))
        .outputs(outPlace(ps[pid + 1]!))
        .action(fork())
        .build();
      const net = PetriNet.builder(`word-${word}`)
        .transitions(...fillers(ps, pid), t)
        .build();
      const program = PrecompiledNet.compile(net);
      expect(program.compiled.placeId(ps[pid]!)).toBe(pid);
      const tid = program.compiled.transitionId(t);

      const snapshot = new Uint32Array(program.compiled.wordCount);
      expect(program.canEnableSparse(tid, snapshot)).toBe(false);
      snapshot[word] = 1;
      expect(program.canEnableSparse(tid, snapshot)).toBe(true);
    });
  }

  it('single-word inhibitor mask in word 128 blocks the transition', async () => {
    // `go` must stay in word 0: with its needs mask in a wrapped word too, the regression
    // spins instead of failing. A read on a never-enabled transition pins it to id 1.
    const pin = place<number>('pin');
    const go = place<number>('go');
    const pinGo = Transition.builder('pinGo').inputs(one(pin)).read(go).build();
    const ps = places(128 * 32 - 2);
    const blocker = place<number>('blocker');
    const done = place<number>('done');
    const t = Transition.builder('t')
      .inputs(one(go))
      .inhibitor(blocker)
      .outputs(outPlace(done))
      .action(fork())
      .build();
    const net = PetriNet.builder('word-128-inhibitor')
      .transitions(pinGo, ...fillers(ps, ps.length), t)
      .build();
    const program = PrecompiledNet.compile(net);
    expect(program.compiled.placeId(go)).toBe(1);
    expect(program.compiled.placeId(blocker)).toBe(128 * 32);

    const executor = new PrecompiledNetExecutor(
      net, new Map([[go, [tokenOf(1)]], [blocker, [tokenOf(2)]]]), { program },
    );
    const marking = await executor.run();
    expect(marking.tokenCount(go)).toBe(1);
    expect(marking.tokenCount(done)).toBe(0);
  });
});
