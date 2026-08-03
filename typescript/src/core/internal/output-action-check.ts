import type { PetriNet } from '../petri-net.js';
import { isPassthrough } from '../transition-action.js';

/**
 * CORE-043: a transition that declares an output spec must not carry the built-in
 * `passthrough()`. It produces no tokens, so output validation (IO-015) rejects every
 * firing and the declared output never arrives. Enforced when a net is compiled for
 * execution and when one is handed to verification, so verification cannot green-light a net that will not compile.
 */
export function requireOutputProducingActions(net: PetriNet): void {
  for (const t of net.transitions) {
    if (t.outputSpec !== null && isPassthrough(t.action)) {
      throw new Error(
        `Transition '${t.name}' declares an output spec but carries passthrough(), which ` +
        `produces no tokens. Every firing would fail output validation (IO-015) and ` +
        `the declared output would never arrive. Bind an action that produces it — ` +
        `fork() moves the input token across — or drop the output spec if the ` +
        `transition is meant to be a sink.`,
      );
    }
  }
}
