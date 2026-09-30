import type { PetriNet } from '../../src/core/petri-net.js';

/**
 * Every transition of `net`, as the declared mints (NU-010) of a test that exercises something
 * other than the mint declaration.
 */
export function allMints(net: PetriNet): Set<string> {
  return new Set([...net.transitions].map(t => t.name));
}
