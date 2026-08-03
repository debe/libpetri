import type { PetriNet } from '../../src/core/petri-net.js';
import type { TransitionAction } from '../../src/core/transition-action.js';
import { transform } from '../../src/core/transition-action.js';

/**
 * A token-producing action for structural fixtures.
 *
 * Verification enforces CORE-043 exactly as compilation does, so a net whose shape is all a
 * structural fixture cares about still has to be runnable before it can be analysed.
 */
export function produces(): TransitionAction {
  return transform(() => null);
}

/** {@link produces} on every output-declaring transition; the rest are left untouched. */
export function bindProducers(net: PetriNet): PetriNet {
  const producing = new Set(
    [...net.transitions].filter((t) => t.outputSpec !== null).map((t) => t.name),
  );
  return net.bindActionsWithResolver((name) => (producing.has(name) ? produces() : null));
}
