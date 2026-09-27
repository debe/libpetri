import { describe, it, expect } from 'vitest';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { placeBound } from '../../src/verification/smt-property.js';
import { ignore } from '../../src/verification/analysis/environment-analysis-mode.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place, environmentPlace } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';

/**
 * [CORE-037] in the verifier report: one `WARNING:` line per dead read / inhibitor / reset
 * arc, judged against the verification's own initial marking and environment places. The net
 * is untimed, so the enumeration route decides it without a solver.
 */
describe('dead arc warning in the SmtVerifier report (CORE-037)', () => {
  const kill = place<string>('KILL');
  const answerIn = place<string>('answer/IN');
  const flag = place<string>('FLAG');
  const net = PetriNet.builder('lab')
    .transition(Transition.builder('hub_kill').inputs(one(kill)).reset(answerIn).build())
    .transition(Transition.builder('probe').inputs(one(place('P_IN'))).read(flag).inhibitor(flag).build())
    .build();

  const RESET = "WARNING: reset arc of 'hub_kill' on 'answer/IN': no transition produces into or consumes " +
    'from it and it starts empty; the arc has no effect.';
  const READ = "WARNING: read arc of 'probe' on 'FLAG': no transition produces into or consumes from it " +
    'and it starts empty; the transition can never be enabled.';
  const INHIBITOR = "WARNING: inhibitor arc of 'probe' on 'FLAG': no transition produces into or consumes " +
    'from it and it starts empty; the arc never blocks.';

  it('one line per dead arc, in transition order, then read, inhibitor, reset', async () => {
    const result = await SmtVerifier.forNet(net).initialMarking(m => m.tokens(kill, 1)).property(placeBound(kill, 1)).verify();
    expect(result.verdict.type, result.report).toBe('proven');
    const warnings = result.report.split('\n').filter(l => l.startsWith('WARNING: '));
    expect(warnings).toEqual([RESET, READ, INHIBITOR]);
  });

  it('a place the initial marking seeds, or an environment place, is not dead', async () => {
    const seeded = await SmtVerifier.forNet(net)
      .initialMarking(m => m.tokens(kill, 1).tokens(flag, 1))
      .property(placeBound(kill, 1))
      .verify();
    expect(seeded.report.split('\n').filter(l => l.startsWith('WARNING: '))).toEqual([RESET]);

    const env = await SmtVerifier.forNet(net)
      .initialMarking(m => m.tokens(kill, 1))
      .environmentPlaces(environmentPlace<string>('answer/IN'))
      .environmentMode(ignore())
      .property(placeBound(kill, 1))
      .verify();
    expect(env.report.split('\n').filter(l => l.startsWith('WARNING: '))).toEqual([READ, INHIBITOR]);
  });
});
