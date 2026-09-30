import { describe, expect, it } from 'vitest';
import { PetriNet, Transition, one, outPlace, place } from 'libpetri';
import { runGates } from '../src/gates.js';
import type { Candidate, Contract } from '../src/types.js';

/** A design that reacts to an environment input it does not generate itself. */
function design(dropOne: boolean): Candidate {
  return {
    name: dropOne ? 'drops' : 'handles',
    rationale: 'test',
    build() {
      const IN = place<unknown>('UTTERANCE'), OUT = place<unknown>('ANSWERED'), BUSY = place<unknown>('BUSY');
      const t = [Transition.builder('take').inputs(one(IN)).outputs(outPlace(BUSY)).build(),
                 Transition.builder('answer').inputs(one(BUSY)).outputs(outPlace(OUT)).build()];
      // the faulty design swallows a waiting utterance whenever it answers one: reset on the input
      if (dropOne) t[1] = Transition.builder('answer').inputs(one(BUSY)).reset(IN).outputs(outPlace(OUT)).build();
      return { net: PetriNet.builder('d').transitions(...t).build(), marking: new Map() };
    },
  };
}

const contract: Contract = {
  name: 'inputs', intent: 'every utterance answered', sources: [], sinks: ['ANSWERED'], scales: [1, 2],
  inputs: [{ place: 'UTTERANCE', tokens: 'k' }],
  properties: [
    { name: 'stranded', spec: { kind: 'deadlockFree' } },
    { name: 'accounting', spec: { kind: 'accounting', outcomes: ['ANSWERED'] } },
  ],
};

describe('environment inputs driven by the harness', () => {
  it('a design that handles every input passes at every scale', async () => {
    const r = await runGates(contract, design(false));
    expect(r.passed).toBe(true);
  });
  it('a design that loses inputs fails accounting at k = 2 only', async () => {
    const r = await runGates(contract, design(true));
    const acc = (k: number) => r.smallScope.find(s => s.k === k)!.results.find(x => x.property === 'accounting')!.verdict;
    expect(acc(1)).toBe('proven');
    expect(acc(2)).toBe('violated');
  });
});
