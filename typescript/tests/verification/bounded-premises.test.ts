import { expect, it } from 'vitest';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { deadlockFree, placeBound, type SmtProperty } from '../../src/verification/smt-property.js';
import { bounded } from '../../src/verification/analysis/environment-analysis-mode.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { environmentPlace, place, type Place } from '../../src/core/place.js';
import { exactly, one, type In } from '../../src/core/in.js';
import { andPlaces, outPlace } from '../../src/core/out.js';
import { matchKey, matchSpec } from '../../src/core/match-spec.js';
import { nameId } from '../../src/core/name.js';
import { produces } from '../fixtures/producing-actions.js';
import { describeZ3 } from '../fixtures/z3.js';

/**
 * [VER-006] AC3: the `bounded(k)` premises. Every route models a bounded environment place as a
 * source holding at most k: the flat encoding caps each successor there at k, the state-class
 * graphs enable an environment input exactly when it demands at most k, and the quiescence
 * clause calls a demand above k permanently disabled. That is the executor only when no
 * transition deposits into an environment place and the initial marking holds at most k on each
 * one. Outside those premises the verifier answers unknown, naming the place, on every route.
 */

const a = place<string>('a');
const b = place<string>('b');
const c = place<string>('c');
const d = place<string>('d');
const ENV_E = environmentPlace<string>('E');
const E = ENV_E.place;
const out = place<string>('out');
const source = place<string>('source');

const arc = (name: string, input: In, to: Place<string>): Transition =>
  Transition.builder(name).inputs(input).outputs(outPlace(to)).action(produces()).build();

/** A same-mint ν-join beside the net, so the query runs on Route B. */
function withJoin(builder: ReturnType<typeof PetriNet.builder>): ReturnType<typeof PetriNet.builder> {
  const branchA = place<string>('branchA');
  const branchB = place<string>('branchB');
  const merged = place<string>('merged');
  const key = (p: Place<string>) => matchKey(p, (v: string) => nameId(v));
  return builder
    .transition(Transition.builder('fork').inputs(one(source)).outputs(andPlaces(branchA, branchB))
      .action(produces()).build())
    .transition(Transition.builder('join').inputs(one(branchA), one(branchB)).outputs(outPlace(merged))
      .match(matchSpec(key(branchA), key(branchB))).action(produces()).build());
}

function net(name: string, join: boolean, ...transitions: Transition[]): PetriNet {
  let builder = PetriNet.builder(name);
  for (const t of transitions) builder = builder.transition(t);
  return (join ? withJoin(builder) : builder).build();
}

async function verify(n: PetriNet, m0: MarkingState, property: SmtProperty, budget: number) {
  let verifier = SmtVerifier.forNet(n)
    .initialMarking(m0)
    .environmentPlaces(ENV_E)
    .environmentMode(bounded(1))
    .property(property)
    .enumerationMaxClasses(budget);
  if ([...n.transitions].some(t => t.name === 'fork')) verifier = verifier.mintTransitions('fork');
  return verifier.verify();
}

function expectRefused(result: Awaited<ReturnType<typeof verify>>, cause: string): void {
  expect(result.verdict.type, result.report).toBe('unknown');
  expect((result.verdict as { reason: string }).reason.startsWith(
    `environment place 'E' is outside the Bounded(1) premises (VER-006 AC3): ${cause}. `,
  ), (result.verdict as { reason: string }).reason).toBe(true);
}

const marking = (counts: [Place<string>, number][]): MarkingState => {
  const builder = MarkingState.builder();
  for (const [p, n] of counts) builder.tokens(p, n);
  return builder.build();
};

describeZ3('bounded(k) premises (VER-006 AC3)', () => {
  it('an initial marking above k is refused: the post-cap froze every transition', async () => {
    const n = net('capA', false,
      arc('t', one(a), b),
      Transition.builder('u').inputs(one(E), one(d)).outputs(outPlace(c)).action(produces()).build());
    for (const budget of [0, 50_000]) {
      expectRefused(await verify(n, marking([[a, 1], [E, 2]]), placeBound(b, 0), budget),
        'the initial marking holds 2 tokens there, more than 1');
    }
  });

  it('a deposit into an environment place is refused: the executor marks E with 2', async () => {
    const n = net('capB', false, arc('t', one(a), E));
    expectRefused(await verify(n, marking([[a, 2]]), placeBound(E, 1), 50_000), "transition 't' deposits into it");
  });

  it('a demand above k met by deposits is refused on every route', async () => {
    for (const join of [true, false]) {
      const n = net('supplied', join, arc('t0', one(a), E), arc('t1', exactly(2, E), out));
      expectRefused(await verify(n, marking([[a, 2], [source, 1]]), placeBound(out, 0), 50_000),
        "transition 't0' deposits into it");
    }
  });

  it('a spurious deadlock from an initial marking above k is refused', async () => {
    for (const join of [true, false]) {
      const n = net('quiescent', join, arc('tQ1', exactly(2, E), out), arc('tQ2', one(out), out));
      expectRefused(await verify(n, marking([[E, 2]]), deadlockFree(), 50_000),
        'the initial marking holds 2 tokens there, more than 1');
    }
  });

  it('within the premises the verdict stands', async () => {
    const n = net('within', false, arc('t', one(a), b), arc('u', one(E), out));
    const m0 = marking([[a, 1], [E, 1]]);
    const violated = await verify(n, m0, placeBound(b, 0), 0);
    expect(violated.verdict.type, violated.report).toBe('violated');
    const proven = await verify(n, m0, placeBound(b, 1), 0);
    expect(proven.verdict.type, proven.report).toBe('proven');
    expect(proven.route).not.toBe('unavailable');
  });
});
