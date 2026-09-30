/**
 * Parallel input guard (lab round 12). An input guard runs in parallel with the answer; a draft is
 * sent only with a passing verdict, and a failing verdict refuses the turn whether the answer is
 * still running or already drafted. One turn at a time.
 */
import type { Contract } from '../../src/types.js';

const contract: Contract = {
  name: 'Guarded turn',
  intent:
    'Each incoming message is checked by an input guard while the answer is drafted in parallel. ' +
    'A draft is sent only after a passing verdict; a failing verdict refuses the turn and nothing of ' +
    'that turn may be left behind. Turns are handled one at a time.',
  properties: [
    { name: 'noStrandedWork', spec: { kind: 'deadlockFree' } },
    { name: 'everyTurnAnswered', spec: { kind: 'accounting', outcomes: ['SENT', 'REFUSED'] } },
    { name: 'oneTurnAtATime', spec: { kind: 'placeBound', place: 'TURN_PERMIT', bound: 1 } },
  ],
  sinks: ['SENT', 'REFUSED', 'TURN_PERMIT'],
  sources: ['SOURCE'],
  scales: [1, 2],
};

export default contract;
