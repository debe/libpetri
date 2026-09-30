/**
 * Correct but badly encapsulated (lab round 12, revisited on libpetri with MOD-027): on a failing
 * verdict one host transition resets the answer subnet's input and its internal ANSWERING place.
 * It passes every gate — unlike the round-12 original, whose reset named `answer/IN`, a port place
 * that composition had bound away, so it cleared nothing and stranded a late draft (libpetri now
 * rejects that at build). What remains is visible only to the sensors: the host reaches into the
 * subnet (encapsulation violation, cross-subnet reset), so the answer subnet cannot be proven on its
 * own, and every change to its internals must be mirrored in the host.
 */
import { PetriNet, SubnetDef, Transition, andPlaces, one, outPlace } from 'libpetri';
import type { Candidate } from '../../src/types.js';
import { guard, hostPlaces, marking, p } from './shared.js';

function answer(): SubnetDef<void> {
  const IN = p('IN'), BUSY = p('ANSWERING'), DRAFT = p('DRAFT');
  return SubnetDef.builder('Answer')
    .place(IN).place(BUSY).place(DRAFT)
    .transition(Transition.builder('start').inputs(one(IN)).outputs(outPlace(BUSY)).build())
    .transition(Transition.builder('finish').inputs(one(BUSY)).outputs(outPlace(DRAFT)).build())
    .inputPort('in', IN).outputPort('draft', DRAFT)
    .build();
}

const candidate: Candidate = {
  name: 'hub',
  rationale:
    'Central kill switch. A failing verdict fires one host transition that resets the answer ' +
    'subnet\'s input and working places and refuses the turn. Fewer transitions and arcs than the ' +
    'cancellation protocol and correct, but the host reaches into the subnet: the sensors, not the ' +
    'gates, are what separate it from `gate`.',
  build(k) {
    const h = hostPlaces();
    const net = PetriNet.builder('guard-hub')
      .transition(Transition.builder('arrive').inputs(one(h.SOURCE)).outputs(outPlace(h.INBOX)).build())
      .transition(Transition.builder('fork').inputs(one(h.INBOX), one(h.TURN_PERMIT)).outputs(andPlaces(h.G_IN, h.A_IN)).build())
      .compose(guard().instantiate('guard'), { in: h.G_IN, ok: h.VERDICT_OK, bad: h.VERDICT_BAD })
      .compose(answer().instantiate('answer'), { in: h.A_IN, draft: h.DRAFT })
      .transition(Transition.builder('send').inputs(one(h.DRAFT), one(h.VERDICT_OK)).outputs(andPlaces(h.SENT, h.TURN_PERMIT)).build())
      .transition(Transition.builder('refuse_drafted').inputs(one(h.VERDICT_BAD), one(h.DRAFT)).outputs(andPlaces(h.REFUSED, h.TURN_PERMIT)).priority(5).build())
      .transition(Transition.builder('kill').inputs(one(h.VERDICT_BAD)).inhibitor(h.DRAFT)
        .reset(h.A_IN).reset(p('answer/ANSWERING'))
        .outputs(andPlaces(h.REFUSED, h.TURN_PERMIT)).build())
      .build();
    return { net, marking: marking(k) };
  },
};

export default candidate;
