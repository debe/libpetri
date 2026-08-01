// CORE-043: a transition declaring an output spec must not carry passthrough() in a net
// handed to an executor or to verification.
import { describe, it, expect } from 'vitest';
import { CompiledNet } from '../../src/runtime/compiled-net.js';
import { PrecompiledNet } from '../../src/runtime/precompiled-net.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace, timeout, forwardInput } from '../../src/core/out.js';
import { fork, passthrough } from '../../src/core/transition-action.js';

const IN = place<string>('In');
const OUT = place<string>('Out');

function netOf(...transitions: Transition[]): PetriNet {
  return PetriNet.builder('Test').transitions(...transitions).build();
}

describe('CompiledNet — CORE-043', () => {
  // ---------------------------------------------------------------- rejection paths

  it('builder default: outputs declared, action never bound → rejected', () => {
    const net = netOf(Transition.builder('t')
      .inputs(one(IN))
      .outputs(outPlace(OUT))
      .build());

    expect(() => CompiledNet.compile(net)).toThrow(/Transition 't' declares an output spec/);
  });

  it('explicit bind: passthrough() bound by name → rejected', () => {
    const net = netOf(Transition.builder('t')
      .inputs(one(IN))
      .outputs(outPlace(OUT))
      .action(fork())
      .build())
      .bindActions({ t: passthrough() });

    expect(() => CompiledNet.compile(net)).toThrow(/'t'/);
  });

  it("typo'd key: bindActions substitutes passthrough → rejected", () => {
    const net = netOf(Transition.builder('typoed')
      .inputs(one(IN))
      .outputs(outPlace(OUT))
      .build())
      .bindActions({ typoedd: fork() });

    expect(() => CompiledNet.compile(net)).toThrow(/'typoed'/);
  });

  it('Timeout(ForwardInput) as the whole spec → still rejected', () => {
    // The executor produces the child, but only once the budget expires — a branch
    // passthrough can never reach, since it completes immediately.
    const net = netOf(Transition.builder('t')
      .inputs(one(IN))
      .outputs(timeout(100, forwardInput(IN, OUT)))
      .build());

    expect(() => CompiledNet.compile(net)).toThrow(/'t'/);
  });

  it('the precompiled path is covered too', () => {
    const net = netOf(Transition.builder('t')
      .inputs(one(IN))
      .outputs(outPlace(OUT))
      .build());

    expect(() => PrecompiledNet.compile(net)).toThrow(/'t'/);
  });

  it('the message names the fix', () => {
    const net = netOf(Transition.builder('t')
      .inputs(one(IN))
      .outputs(outPlace(OUT))
      .build());

    expect(() => CompiledNet.compile(net)).toThrow(/IO-015/);
    expect(() => CompiledNet.compile(net)).toThrow(/fork\(\)/);
  });

  // ---------------------------------------------------------------- accepted paths

  it('a sink is still a sink (CORE-042 AC4)', () => {
    const net = netOf(Transition.builder('sink').inputs(one(IN)).build());

    expect(() => CompiledNet.compile(net)).not.toThrow();
  });

  it('fork() satisfies the declared output', () => {
    const net = netOf(Transition.builder('t')
      .inputs(one(IN))
      .outputs(outPlace(OUT))
      .action(fork())
      .build());

    expect(() => CompiledNet.compile(net)).not.toThrow();
  });

  it('a hand-written no-op is not claimed — that stays IO-015\'s job', () => {
    // Identity-based (CORE-051): a hand-written no-op is indistinguishable from one that
    // produces conditionally, so it is left to IO-015 at run time.
    const net = netOf(Transition.builder('t')
      .inputs(one(IN))
      .outputs(outPlace(OUT))
      .action(async () => {})
      .build());

    expect(() => CompiledNet.compile(net),
      'only passthrough() is provably inert; anything else may produce').not.toThrow();
  });
});
