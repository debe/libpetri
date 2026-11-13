import { describe, it, expect } from 'vitest';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { deadlockFree, unreachable } from '../../src/verification/smt-property.js';
import { CompiledNet } from '../../src/runtime/compiled-net.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { andPlaces, outPlace } from '../../src/core/out.js';
import { matchKey, matchSpec } from '../../src/core/match-spec.js';
import { nameId } from '../../src/core/name.js';
import { bindProducers } from '../fixtures/producing-actions.js';

// Its own file rather than a block in smt-verifier.test.ts: vitest isolates test
// files into separate workers, so this gets a fresh z3 WASM heap. Appended to that
// file instead, the extra solver run tipped the shared heap past the 2 GB wasm32
// ceiling and OOM'd an unrelated test alongside it.
const Z3_TIMEOUT = 60_000;

// CORE-043: verification rejects the same nets compilation rejects.
describe('SmtVerifier — CORE-043', () => {
  it('rejects an output-declaring transition still on passthrough', async () => {
    const pA = place('A');
    const pB = place('B');
    const net = PetriNet.builder('inert')
      .transition(Transition.builder('t').inputs(one(pA)).outputs(outPlace(pB)).build())
      .build();

    // Throws before Z3 is reached, so this case costs no solver memory.
    await expect(SmtVerifier.forNet(net).property(deadlockFree()).verify())
      .rejects.toThrow(/Transition 't' declares an output spec/);
  });

  it('accepts the same net once an action is bound', async () => {
    const pA = place('A');
    const pB = place('B');
    const net = PetriNet.builder('live')
      .transition(Transition.builder('t').inputs(one(pA)).outputs(outPlace(pB)).build())
      .build();

    await expect(SmtVerifier.forNet(bindProducers(net)).property(deadlockFree())
      .initialMarking(m => { m.tokens(pA, 1); })
      .sinkPlaces(pB)
      .timeout(30_000)
      .verify()).resolves.toBeDefined();
  }, Z3_TIMEOUT);
});

/**
 * A net that compiles: a ν pair (`MINT` → `X`, `Y`, `JOIN` by name), so Route B reads conflict
 * priority, and a higher-priority **sink** `H: c` on the default passthrough that shares `c`
 * with `L: c → bad`. Conflict priority splits `H`; its start half must not inherit a
 * passthrough next to the in-flight output it gains.
 */
function passthroughSinkPrunerNet(): PetriNet {
  const x = place<string>('X'), y = place<string>('Y'), j = place<string>('J');
  const c = place('c'), bad = place('bad');
  return PetriNet.builder('conflict-sink')
    .transition(Transition.builder('MINT').inputs(one(place('SEED'))).outputs(andPlaces(x, y))
      .action(async ctx => { const n = ctx.freshName(); ctx.output(x, n); ctx.output(y, n); }).build())
    .transition(Transition.builder('JOIN').inputs(one(x), one(y))
      .match(matchSpec(matchKey(x, (v: string) => nameId(v)), matchKey(y, (v: string) => nameId(v))))
      .outputs(outPlace(j)).action(async ctx => { ctx.output(j, ctx.input(x)); }).build())
    .transition(Transition.builder('H').priority(10).inputs(one(c)).build())
    .transition(Transition.builder('L').inputs(one(c)).outputs(outPlace(bad))
      .action(async ctx => { ctx.output(bad, 1); }).build())
    .build();
}

describe('SmtVerifier — CORE-043 under a conflict split (RD-08)', () => {
  const conflictVerifier = () => SmtVerifier.forNet(passthroughSinkPrunerNet())
    .initialMarking(m => { m.tokens(place('SEED'), 1); m.tokens(place('c'), 1); })
    .property(unreachable(new Set([place('bad')])))
    .mintTransitions('MINT')
    .prioritySemantics('conflict');

  it('a conflict split of a passthrough sink is not refused (CORE-043)', () => {
    // The net compiles, so verification must not refuse it.
    expect(() => CompiledNet.compile(passthroughSinkPrunerNet())).not.toThrow();
    expect(() => conflictVerifier().encodeScripts()).not.toThrow();
  });

  it('verify() returns a verdict for a conflict split of a passthrough sink (CORE-043)', async () => {
    const r = await conflictVerifier().timeout(30_000).verify();
    expect(r.report).toContain('In-flight actions (VER-004): H');
    // Route B decides it, so no z3 is needed: H pre-empts L, so `bad` is unreachable.
    expect(r.report).toContain('ν-net Route B');
    expect(r.verdict.type, r.report).toBe('proven');
  });
});
