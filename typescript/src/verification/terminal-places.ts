/**
 * @module terminal-places
 *
 * The verification encoding of net-declared terminal places ([EXEC-042], [VER-014]).
 *
 * A terminal place `P` ends the run the moment a deposit marks it. The verifiers see exactly that
 * behaviour in a plain net where `P` inhibits every transition — no transition fires once `P` is
 * marked — with `P` a sink ([VER-002]) and a conditional-sink marker for every place
 * (`sinkPlacesWhen(P, all places)`): a marking with `P` marked is quiescent and excused.
 *
 * The caller restates none of this. A net without terminals is never touched, so its scripts
 * stay byte-identical ([VER-013]).
 */
import { PetriNet } from '../core/petri-net.js';
import type { Place } from '../core/place.js';
import { Transition } from '../core/transition.js';

/**
 * `net` with each of its terminal places inhibiting every transition, or `net` itself — the
 * same instance — when it declares no terminals, so its scripts stay byte-identical.
 *
 * Names, place order and transition order are kept; the added inhibitors follow each
 * transition's own, in terminal declaration order, and one already present is not repeated.
 * The result declares **no** terminals — the inhibitors now carry them — so applying this twice
 * is the same as applying it once. The caller adds the sink half of the encoding (each terminal
 * a sink and a conditional-sink marker for {@link terminalExcusedPlaces}), which a net cannot
 * say by itself. Mirrors Java's `TerminalEncoding.inhibited`.
 */
export function withTerminalInhibitors(net: PetriNet): PetriNet {
  if (net.terminals.size === 0) return net;
  const terminals = [...net.terminals];
  const transitions = [...net.transitions].map(t => {
    const inhibited = new Set(t.inhibitors.map(arc => arc.place.name));
    const missing = terminals.filter(p => !inhibited.has(p.name));
    return missing.length === 0 ? t : withInhibitors(t, missing);
  });
  return PetriNet.builder(net.name)
    .places(...net.places)
    .transitions(...transitions)
    .build();
}

/**
 * The places each terminal excuses while it is marked: every place of `net`, in net order.
 * `sinkPlacesWhen(P, …these)` and the open-net `DesignedTerminal` both take this list.
 */
export function terminalExcusedPlaces(net: PetriNet): Place<any>[] {
  return [...net.places];
}

/** `t` with inhibitor arcs from `places` appended after its own; everything else is carried. */
function withInhibitors(t: Transition, places: readonly Place<any>[]): Transition {
  const b = Transition.builder(t.name)
    .timing(t.timing)
    .priority(t.priority)
    .action(t.action);
  if (t.placeAlias.size > 0) b.placeAlias(t.placeAlias);
  if (t.inputSpecs.length > 0) b.inputs(...t.inputSpecs);
  if (t.outputSpec !== null) b.outputs(t.outputSpec);
  for (const arc of t.inhibitors) b.inhibitor(arc.place);
  for (const p of places) b.inhibitor(p);
  for (const arc of t.reads) b.read(arc.place);
  for (const arc of t.resets) b.reset(arc.place);
  if (t.matchSpec !== null) b.match(t.matchSpec);
  return b.build();
}
