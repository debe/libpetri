/**
 * Regression: the sparse enablement check must treat bit 31 (the int32 sign bit) as an
 * ordinary bit. `(snapshot[w] & m)` is a signed int32 in JavaScript while `m` comes from a
 * Uint32Array, so without `>>> 0` a transition whose needs-mask includes place id 31
 * (or 63, 95, …) compares negative against positive and is never enabled on the
 * production executor. `containsAll` received the same fix in be51666; this pins the
 * sparse path used by `PrecompiledNetExecutor` (CONC-020, PERF-042). Found by n8n-libpetri:
 * every compiled workflow with 32 or more places hit it.
 *
 * Place ids are assigned in transition reference order (inputs, reads, inhibitors, resets,
 * outputs per transition, then declared-only places), so filler sink transitions push the
 * places under test to the sign-bit positions; the ids are asserted, not assumed.
 */
import { describe, it, expect } from 'vitest';
import {
  PetriNet, Transition, PrecompiledNet, PrecompiledNetExecutor,
  place, one, outPlace, fork, transform, tokenOf,
} from '../../src/index.js';
import type { Place } from '../../src/index.js';

function places(n: number): Place<number>[] {
  return Array.from({ length: n }, (_, i) => place<number>(`p${i}`));
}

/** Sink transitions consuming `ps[from..to)` in order, each claiming the next place id. */
function fillers(ps: Place<number>[], from: number, to: number): Transition[] {
  const out: Transition[] = [];
  for (let i = from; i < to; i++) {
    out.push(Transition.builder(`f${i}`).inputs(one(ps[i]!)).build());
  }
  return out;
}

describe('PrecompiledNet.canEnableSparse with the sign bit set', () => {
  it('single-word mask: a transition needing only place 31 is enabled', async () => {
    const ps = places(33);
    const t = Transition.builder('t')
      .inputs(one(ps[31]!))
      .outputs(outPlace(ps[32]!))
      .action(fork())
      .build();
    const net = PetriNet.builder('bit31-single')
      .transitions(...fillers(ps, 0, 31), t)
      .build();
    const program = PrecompiledNet.compile(net);
    expect(program.compiled.placeId(ps[31]!)).toBe(31);
    const tid = program.compiled.transitionId(t);

    const snapshot = new Uint32Array(program.compiled.wordCount);
    snapshot[0] = (1 << 31) >>> 0;
    expect(program.canEnableSparse(tid, snapshot)).toBe(true);

    const executor = new PrecompiledNetExecutor(
      net, new Map([[ps[31]!, [tokenOf(7)]]]), { program },
    );
    const marking = await executor.run();
    expect(marking.tokenCount(ps[31]!)).toBe(0);
    expect(marking.tokenCount(ps[32]!)).toBe(1);
  });

  it('multi-word sparse mask: a transition needing places 31 and 63 is enabled', async () => {
    const ps = places(65);
    // Read arcs claim ids after the inputs of the same transition, so a filler with one
    // input and one read pins p31 to id 31 (and p63 to id 63) without consuming them.
    const pinA = place<number>('pinA');
    const pinB = place<number>('pinB');
    const claimA = Transition.builder('claimA').inputs(one(pinA)).read(ps[31]!).build();
    const claimB = Transition.builder('claimB').inputs(one(pinB)).read(ps[63]!).build();
    const t = Transition.builder('t')
      .inputs(one(ps[31]!), one(ps[63]!))
      .outputs(outPlace(ps[64]!))
      .action(transform(() => 1))
      .build();
    const net = PetriNet.builder('bit31-multi')
      .transitions(...fillers(ps, 0, 30), claimA, ...fillers(ps, 32, 62), claimB, t)
      .build();
    const program = PrecompiledNet.compile(net);
    expect(program.compiled.placeId(ps[31]!)).toBe(31);
    expect(program.compiled.placeId(ps[63]!)).toBe(63);

    const executor = new PrecompiledNetExecutor(
      net, new Map([[ps[31]!, [tokenOf(1)]], [ps[63]!, [tokenOf(2)]]]), { program },
    );
    const marking = await executor.run();
    expect(marking.tokenCount(ps[64]!)).toBe(1);
  });

  it('still rejects when the sign-bit place is empty', () => {
    const ps = places(33);
    const t = Transition.builder('t')
      .inputs(one(ps[31]!))
      .outputs(outPlace(ps[32]!))
      .action(fork())
      .build();
    const net = PetriNet.builder('bit31-empty')
      .transitions(...fillers(ps, 0, 31), t)
      .build();
    const program = PrecompiledNet.compile(net);
    expect(program.compiled.placeId(ps[31]!)).toBe(31);
    const snapshot = new Uint32Array(program.compiled.wordCount);
    snapshot[0] = (1 << 30) >>> 0; // place 30 marked, place 31 empty
    expect(program.canEnableSparse(program.compiled.transitionId(t), snapshot)).toBe(false);
  });
});
