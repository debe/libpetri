/**
 * Correct candidate: the answer subnet is cancelled through a CANCEL port and reports CANCELLED.
 * The host never touches the subnet's internal places, so the subnet can be proven on its own.
 */
import { PetriNet, SubnetDef, Transition, andPlaces, one, outPlace } from 'libpetri';
import type { Candidate } from '../../src/types.js';
import { guard, hostPlaces, marking, p } from './shared.js';

/** Drafts an answer; can be cancelled while waiting or while busy. */
function cancellableAnswer(): SubnetDef<void> {
  const IN = p('IN'), BUSY = p('ANSWERING'), DRAFT = p('DRAFT'), CANCEL = p('CANCEL'), CANCELLED = p('CANCELLED');
  return SubnetDef.builder('Answer')
    .place(IN).place(BUSY).place(DRAFT).place(CANCEL).place(CANCELLED)
    .transition(Transition.builder('start').inputs(one(IN)).outputs(outPlace(BUSY)).build())
    .transition(Transition.builder('finish').inputs(one(BUSY)).outputs(outPlace(DRAFT)).build())
    .transition(Transition.builder('cancel_in').inputs(one(CANCEL), one(IN)).outputs(outPlace(CANCELLED)).build())
    .transition(Transition.builder('cancel_busy').inputs(one(CANCEL), one(BUSY)).outputs(outPlace(CANCELLED)).build())
    .inputPort('in', IN).outputPort('draft', DRAFT).inputPort('cancel', CANCEL).outputPort('cancelled', CANCELLED)
    .build();
}

const candidate: Candidate = {
  name: 'gate',
  rationale:
    'Cancellation by consumption only. A failing verdict puts a token on the answer subnet\'s CANCEL ' +
    'port; the subnet withdraws its own work and reports CANCELLED, and the host refuses the turn. ' +
    'A draft that finished first is refused directly. No resets, no arcs into subnet internals.',
  build(k) {
    const h = hostPlaces();
    const CANCEL = p('CANCEL'), CANCELLED = p('CANCELLED');
    const net = PetriNet.builder('guard-gate')
      .transition(Transition.builder('arrive').inputs(one(h.SOURCE)).outputs(outPlace(h.INBOX)).build())
      .transition(Transition.builder('fork').inputs(one(h.INBOX), one(h.TURN_PERMIT)).outputs(andPlaces(h.G_IN, h.A_IN)).build())
      .compose(guard().instantiate('guard'), { in: h.G_IN, ok: h.VERDICT_OK, bad: h.VERDICT_BAD })
      .compose(cancellableAnswer().instantiate('answer'), { in: h.A_IN, draft: h.DRAFT, cancel: CANCEL, cancelled: CANCELLED })
      .transition(Transition.builder('send').inputs(one(h.DRAFT), one(h.VERDICT_OK)).outputs(andPlaces(h.SENT, h.TURN_PERMIT)).build())
      .transition(Transition.builder('refuse_drafted').inputs(one(h.VERDICT_BAD), one(h.DRAFT)).outputs(andPlaces(h.REFUSED, h.TURN_PERMIT)).priority(5).build())
      .transition(Transition.builder('cancel_answer').inputs(one(h.VERDICT_BAD)).inhibitor(h.DRAFT).outputs(outPlace(CANCEL)).build())
      .transition(Transition.builder('refuse_cancelled').inputs(one(CANCELLED)).outputs(andPlaces(h.REFUSED, h.TURN_PERMIT)).build())
      .transition(Transition.builder('refuse_late').inputs(one(CANCEL), one(h.DRAFT)).outputs(andPlaces(h.REFUSED, h.TURN_PERMIT)).build())
      .build();
    return { net, marking: marking(k) };
  },
  subnets: [
    {
      def: guard(),
      inputs: ['in'],
      properties: [{ name: 'alwaysReachesVerdict', spec: { kind: 'deadlockFree' } }],
    },
  ],
};

export default candidate;
