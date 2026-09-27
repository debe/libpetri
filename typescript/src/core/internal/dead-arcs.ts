/**
 * @module dead-arcs
 *
 * The dead-arc diagnostic of [CORE-037]: a read, inhibitor or reset arc on a place that no
 * transition produces into or consumes from, that is not an environment place, and that holds
 * no token in the initial marking. Nothing can ever put a token there, so the arc has no effect
 * — a read arc disables its transition for good, an inhibitor never blocks, a reset clears
 * nothing. Usually it names a place the author meant to be another one, such as a port place
 * that instance composition bound away ([MOD-027] rejects the case it can detect).
 *
 * A warning, never a rejection: an arc on a place the host seeds, or an environment place, is
 * legitimate. Both executors and `SmtVerifier` report from this one list.
 */
import type { PetriNet } from '../petri-net.js';

/** One arc [CORE-037] warns about. */
export interface DeadArc {
  readonly kind: 'read' | 'inhibitor' | 'reset';
  readonly transition: string;
  readonly place: string;
}

/**
 * Every dead arc of `net`, in transition order and, within a transition, read, inhibitor then
 * reset arcs in declaration order.
 *
 * @param initiallyMarked whether the initial marking holds a token on the named place
 * @param isEnvironment whether the named place is an environment place of this run
 */
export function findDeadArcs(
  net: PetriNet,
  initiallyMarked: (placeName: string) => boolean,
  isEnvironment: (placeName: string) => boolean,
): DeadArc[] {
  const candidates = unconnectedArcs(net);
  if (candidates.length === 0) return candidates;
  return candidates.filter(arc => !isEnvironment(arc.place) && !initiallyMarked(arc.place));
}

/**
 * The read / inhibitor / reset arcs on places no input arc or output spec touches — the part of
 * the rule that depends on the net alone, computed once per (immutable) net so an executor built
 * per run pays for it once. Empty for almost every net.
 */
const UNCONNECTED = new WeakMap<PetriNet, DeadArc[]>();

function unconnectedArcs(net: PetriNet): DeadArc[] {
  let found = UNCONNECTED.get(net);
  if (found !== undefined) return found;
  const connected = new Set<string>();
  for (const t of net.transitions) {
    for (const spec of t.inputSpecs) connected.add(spec.place.name);
    for (const p of t.outputPlaces()) connected.add(p.name);
  }
  found = [];
  for (const t of net.transitions) {
    for (const arc of t.reads) {
      if (!connected.has(arc.place.name)) found.push({ kind: 'read', transition: t.name, place: arc.place.name });
    }
    for (const arc of t.inhibitors) {
      if (!connected.has(arc.place.name)) found.push({ kind: 'inhibitor', transition: t.name, place: arc.place.name });
    }
    for (const arc of t.resets) {
      if (!connected.has(arc.place.name)) found.push({ kind: 'reset', transition: t.name, place: arc.place.name });
    }
  }
  UNCONNECTED.set(net, found);
  return found;
}

/**
 * The warning text for one dead arc, without a severity prefix, e.g. `reset arc of 'hub_kill' on
 * 'answer/IN': no transition produces into or consumes from it and it starts empty; the arc has
 * no effect.`
 */
export function deadArcMessage(arc: DeadArc): string {
  const effect = arc.kind === 'read'
    ? 'the transition can never be enabled'
    : arc.kind === 'inhibitor'
      ? 'the arc never blocks'
      : 'the arc has no effect';
  return `${arc.kind} arc of '${arc.transition}' on '${arc.place}': no transition produces into ` +
    `or consumes from it and it starts empty; ${effect}.`;
}
