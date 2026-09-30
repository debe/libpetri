import { describe, it, expect } from 'vitest';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { environmentPlace, place, type Place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { andPlaces, outPlace, xorPlaces } from '../../src/core/out.js';
import { fork } from '../../src/core/transition-action.js';
import { matchKey, matchSpec } from '../../src/core/match-spec.js';
import { nameId } from '../../src/core/name.js';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { deadlockFree, placeBound } from '../../src/verification/smt-property.js';
import { bounded } from '../../src/verification/analysis/environment-analysis-mode.js';
import { OpenNetContract, verifyOpenNet } from '../../src/verification/open-net/index.js';
import { TimePetriNetAnalyzer } from '../../src/verification/analysis/time-petri-net-analyzer.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { describeZ3 } from '../fixtures/z3.js';

/**
 * Entry-point fixes of the 2026-09-30 round: a mistyped mint name is rejected alike by
 * `mintTransitions`, `verify`, `encodeScripts` and `verifyOpenNet` ([NU-010]); a Route B decline
 * points at `mintTransitions`; the open-net split refuses a writer into a declared carrier; the
 * Bounded(k) premise names the caller's transition; the analyzer reads a split transition as the
 * caller's. Mirrors `rust/libpetri-verification/tests/mint_declarations.rs`,
 * `env_bounded_premises.rs` and the analyzer unit tests.
 */

const unit = (name: string): Place<unknown> => place<unknown>(name);

/** `fork: source → and(branchA, branchB)` with the stock `fork()` action, `join` matched by name. */
function forkJoin(): PetriNet {
  const a = place<string>('branchA'), b = place<string>('branchB'), merged = place<string>('merged');
  const forkT = Transition.builder('fork').inputs(one(unit('source'))).outputs(andPlaces(a, b)).action(fork()).build();
  const join = Transition.builder('join')
    .inputs(one(a), one(b))
    .match(matchSpec(matchKey(a, (s: string) => nameId(s)), matchKey(b, (s: string) => nameId(s))))
    .outputs(outPlace(merged))
    .action(fork())
    .build();
  return PetriNet.builder('fork-join').transitions(forkT, join).build();
}

const verifier = (net: PetriNet) => SmtVerifier.forNet(net)
  .initialMarking(m => m.tokens(unit('source'), 1))
  .property(deadlockFree())
  .sinkPlaces(place('merged'));

const TYPO = "declared mint transition 'frok' not in the net (NU-010)";

describe('a mint name not in the net (NU-010)', () => {
  it('mintTransitions rejects it with the shared wording, every unknown name once, sorted', () => {
    expect(() => verifier(forkJoin()).mintTransitions('frok')).toThrow(TYPO);
    expect(() => verifier(forkJoin()).mintTransitions('zz', 'frok', 'fork', 'zz')).toThrow(
      "declared mint transitions 'frok', 'zz' not in the net (NU-010)",
    );
  });

  it('verifyOpenNet answers unknown before either route', async () => {
    const contract = OpenNetContract.builder().initialMarking(m => m.tokens(unit('source'), 1)).rest(place('merged')).build();
    const r = await verifyOpenNet(forkJoin(), contract, { configureSmt: v => v.mintTransitions('frok') });
    expect(r.verdict).toEqual({ type: 'unknown', reason: TYPO });
    expect(r.classCount).toBe(0);
    expect(r.report).toContain('skipped (a declared mint transition is not in the net (NU-010))');
  });
});

describeZ3('a Route B decline for an undeclared mint', () => {
  it('points at mintTransitions, in the decline line and in the unknown reason', async () => {
    const pointer = "'fork' writes a coloured place without consuming one and is not declared to mint "
      + '(NU-010); if the action writes a name minted with freshName(), declare it with mintTransitions';
    const r = await verifier(forkJoin()).verify();
    expect(r.report).toContain(`ν-net Route B declined: ${pointer}.`);
    expect(r.verdict.type, r.report).toBe('unknown');
    if (r.verdict.type === 'unknown') expect(r.verdict.reason.endsWith(`; ${pointer}`)).toBe(true);
    const declared = await verifier(forkJoin()).mintTransitions('fork').verify();
    expect(declared.verdict.type, declared.report).toBe('proven');
    expect(declared.report).not.toContain('Route B declined');
  });
});

describe('the open-net split and the carriers its hook declares', () => {
  it('refuses a split transition that writes a declared carrier, as SmtVerifier does', async () => {
    const c = place<string>('c');
    const t = Transition.builder('t').inputs(one(unit('a'))).outputs(andPlaces(c, unit('d'))).action(fork()).build();
    const u = Transition.builder('u').inputs(one(unit('q'))).inhibitor(unit('d')).outputs(outPlace(unit('r'))).action(fork()).build();
    const net = PetriNet.builder('carrier-split').transitions(t, u).build();
    const refusal = "it writes the coloured place 'c', whose tokens carry a ν name";

    const direct = await SmtVerifier.forNet(net)
      .initialMarking(m => m.tokens(unit('a'), 1).tokens(unit('q'), 1))
      .property(placeBound(unit('r'), 1))
      .carrierPlaces(c)
      .verify();
    expect(direct.verdict.type, direct.report).toBe('unknown');
    if (direct.verdict.type === 'unknown') expect(direct.verdict.reason).toContain(refusal);

    const contract = OpenNetContract.builder()
      .initialMarking(m => m.tokens(unit('a'), 1).tokens(unit('q'), 1))
      .rest(c, unit('d'), unit('r'))
      .build();
    const r = await verifyOpenNet(net, contract, { configureSmt: v => v.carrierPlaces(c) });
    expect(r.verdict.type, r.report).toBe('unknown');
    if (r.verdict.type === 'unknown') expect(r.verdict.reason).toContain(refusal);
  });
});

describe('the Bounded(k) premise names the caller\'s transition (VER-006 AC3)', () => {
  it('names t, not its completion step', async () => {
    // `t: a → E`, `u: q + inhibitor(E) → r`: t is split, and its completion step deposits into E.
    const e = unit('E');
    const net = PetriNet.builder('premise-split').transitions(
      Transition.builder('t').inputs(one(unit('a'))).outputs(outPlace(e)).action(fork()).build(),
      Transition.builder('u').inputs(one(unit('q'))).inhibitor(e).outputs(outPlace(unit('r'))).action(fork()).build(),
    ).build();
    const r = await SmtVerifier.forNet(net)
      .initialMarking(m => m.tokens(unit('a'), 1).tokens(unit('q'), 1))
      .environmentPlaces(environmentPlace<unknown>('E'))
      .environmentMode(bounded(1))
      .property(placeBound(e, 1))
      .verify();
    expect(r.verdict.type, r.report).toBe('unknown');
    if (r.verdict.type === 'unknown') {
      expect(r.verdict.reason).toContain("transition 't' deposits into it");
      expect(r.verdict.reason).not.toContain('complete:');
    }
  });
});

describe('the analyzer reads a split transition as the caller\'s (VER-004)', () => {
  // `choice: start → xor(A, B)`, split because `watch` inhibits on A (or because B is terminal).
  const choiceNet = (terminal: boolean): PetriNet => {
    const b = PetriNet.builder('choice').transitions(
      Transition.builder('choice').inputs(one(unit('start'))).outputs(xorPlaces(unit('A'), unit('B'))).action(fork()).build(),
      ...(terminal ? [] : [
        Transition.builder('watch').inputs(one(unit('q'))).inhibitor(unit('A')).outputs(outPlace(unit('r'))).action(fork()).build(),
      ]),
    );
    return terminal ? b.terminal(unit('B')).build() : b.build();
  };

  for (const terminal of [false, true]) {
    it(`XOR branches are read off the completion step (${terminal ? 'terminal' : 'inhibitor'})`, () => {
      const net = choiceNet(terminal);
      const result = TimePetriNetAnalyzer.forNet(net)
        .initialMarking(MarkingState.builder().tokens(unit('start'), 1).tokens(unit('q'), 1).build())
        .goalPlaces(unit('A'), unit('B'))
        .build()
        .analyze();
      expect(result.report).toContain('In-flight actions (VER-004): choice is verified in two steps');
      const choice = [...net.transitions].find(t => t.name === 'choice')!;
      const analysis = TimePetriNetAnalyzer.analyzeXorBranches(result.stateClassGraph, net);
      const info = analysis.transitionBranches.get(choice);
      expect(info?.totalBranches).toBe(2);
      expect([...info!.takenBranches].sort()).toEqual([0, 1]);
      // Without the caller's net the graph's own is read, and the start stands for the choice.
      const own = TimePetriNetAnalyzer.analyzeXorBranches(result.stateClassGraph);
      expect([...own.transitionBranches.keys()].map(t => t.name)).toEqual(['choice']);
      expect(own.isXorComplete()).toBe(true);
    });
  }

  it('L4 names the caller\'s transitions, never a completion step', () => {
    const result = TimePetriNetAnalyzer.forNet(choiceNet(false))
      .initialMarking(MarkingState.builder().tokens(unit('start'), 1).tokens(unit('q'), 1).build())
      .goalPlaces(unit('A'), unit('B'))
      .build()
      .analyze();
    expect(result.report).toContain('Terminal SCC missing transitions: [');
    expect(result.report).not.toMatch(/Terminal SCC missing transitions: \[[^\]]*complete:/);
    for (const line of result.report.split('\n').filter(l => l.includes('Terminal SCC missing transitions'))) {
      expect(line).toMatch(/\[(choice|watch)(, (choice|watch))*\]/);
    }
  });
});
