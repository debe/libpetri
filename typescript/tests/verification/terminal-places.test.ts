/**
 * **EXEC-042 AC7/AC8, [VER-014] "Net-declared terminals"** — every verifier applies a net's
 * terminal places without the caller restating them: each inhibits every transition, is a sink,
 * and excuses every place while marked. A net without terminals is untouched, so its scripts
 * stay byte-identical (the cross-language goldens in `smt-script-parity.test.ts` pin that for
 * every fixture; this file pins the mechanism).
 */
import { describe, it, expect } from 'vitest';
import { describeZ3 } from '../fixtures/z3.js';
import { produces } from '../fixtures/producing-actions.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { and, outPlace } from '../../src/core/out.js';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { deadlockFree } from '../../src/verification/smt-property.js';
import { withTerminalInhibitors } from '../../src/verification/terminal-places.js';
import { OpenNetContract, verifyOpenNet } from '../../src/verification/open-net/index.js';
import { TimePetriNetAnalyzer } from '../../src/verification/analysis/time-petri-net-analyzer.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { dotExport } from '../../src/export/dot-exporter.js';
import { DEFAULT_DOT_CONFIG } from '../../src/export/petri-net-mapper.js';

const START = place<string>('start');
const FAST = place<string>('fast');
const SLOW = place<string>('slow');
const DONE = place<string>('done');
const LATE = place<string>('late');

/**
 * EXEC-042's AC7 net: a fork whose one arm marks the terminal place `done` while the other
 * arm's work is still in flight.
 */
function forkNet(withTerminal: boolean): PetriNet {
  const fork = Transition.builder('fork').inputs(one(START))
    .outputs(and(outPlace(FAST), outPlace(SLOW))).action(produces()).build();
  const finish = Transition.builder('finish').inputs(one(FAST)).outputs(outPlace(DONE)).action(produces()).build();
  const slow = Transition.builder('slowArm').inputs(one(SLOW)).outputs(outPlace(LATE)).action(produces()).build();
  const b = PetriNet.builder('terminalFork').transitions(fork, finish, slow);
  if (withTerminal) b.terminal(DONE);
  return b.build();
}

describe('EXEC-042 AC8 — a net without terminals is untouched', () => {
  it('the rewrite returns the same instance', () => {
    const net = forkNet(false);
    expect(withTerminalInhibitors(net)).toBe(net);
  });

  it('scripts of a terminal-free net are unchanged, and the terminal net differs only by the encoding', () => {
    const plain = SmtVerifier.forNet(forkNet(false)).initialMarking(m => m.tokens(START, 1))
      .property(deadlockFree()).encodeScripts();
    const again = SmtVerifier.forNet(forkNet(false)).initialMarking(m => m.tokens(START, 1))
      .property(deadlockFree()).encodeScripts();
    expect(again).toEqual(plain);
    const terminal = SmtVerifier.forNet(forkNet(true)).initialMarking(m => m.tokens(START, 1))
      .property(deadlockFree()).encodeScripts();
    expect(terminal.horn).not.toBe(plain.horn);
    // Same as restating the encoding by hand on the terminal-free net.
    const inhibited = withTerminalInhibitors(forkNet(true));
    expect(inhibited.terminals.size).toBe(0);
    const byHand = SmtVerifier.forNet(inhibited).initialMarking(m => m.tokens(START, 1))
      .property(deadlockFree()).sinkPlaces(DONE)
      .sinkPlacesWhen(DONE, ...inhibited.places).encodeScripts();
    expect(terminal).toEqual(byHand);
  });

  it('the rewrite adds one inhibitor per terminal to every transition, once', () => {
    const inhibited = withTerminalInhibitors(forkNet(true));
    for (const t of inhibited.transitions) {
      expect(t.inhibitors.map(a => a.place.name)).toEqual(['done']);
    }
    expect([...inhibited.transitions].map(t => t.name)).toEqual(['fork', 'finish', 'slowArm']);
  });
});

describeZ3('EXEC-042 AC7 — the verifier honours terminals without sink options', () => {
  it('DeadlockFree is violated without the declaration', async () => {
    const result = await SmtVerifier.forNet(forkNet(false))
      .initialMarking(m => m.tokens(START, 1)).property(deadlockFree()).timeout(60_000).verify();
    expect(result.verdict.type).toBe('violated');
  });

  it('DeadlockFree is violated even with the terminal as a plain sink (the other arm is stranded)', async () => {
    const result = await SmtVerifier.forNet(forkNet(false))
      .initialMarking(m => m.tokens(START, 1)).property(deadlockFree()).sinkPlaces(DONE)
      .timeout(60_000).verify();
    expect(result.verdict.type).toBe('violated');
  });

  it('DeadlockFree is proven with the declaration, no sink option passed', async () => {
    const result = await SmtVerifier.forNet(forkNet(true))
      .initialMarking(m => m.tokens(START, 1)).property(deadlockFree()).timeout(60_000).verify();
    expect(result.verdict.type).toBe('proven');
  });
});

describe('EXEC-042 — the other verification routes', () => {
  it('the state-class analyzer sees the terminal stop', () => {
    const analyze = (terminal: boolean) => TimePetriNetAnalyzer.forNet(forkNet(terminal))
      .initialMarking(MarkingState.builder().tokens(START, 1).build())
      .goalPlaces(DONE).build().analyze();
    // Without the declaration the only dead end is {done, late}. With it, {done, slow} is one
    // too: once `done` is marked the other arm never fires.
    expect(analyze(false).terminalSCCs).toHaveLength(1);
    expect(analyze(true).terminalSCCs).toHaveLength(2);
  });

  it('verifyOpenNet merges a net terminal as a designed terminal', async () => {
    const inp = place<string>('inp');
    const pending = place<string>('pending');
    const out = place<string>('out');
    const halt = place<string>('halt');
    const tA = Transition.builder('tA').inputs(one(inp)).outputs(and(outPlace(halt), outPlace(pending)))
      .action(produces()).build();
    const tB = Transition.builder('tB').inputs(one(pending)).outputs(outPlace(out)).action(produces()).build();
    const build = (terminal: boolean): PetriNet => {
      const b = PetriNet.builder('opn').transitions(tA, tB);
      if (terminal) b.terminal(halt);
      return b.build();
    };
    const contract = OpenNetContract.builder().arrive(1, inp).build();

    const without = await verifyOpenNet(build(false), contract, { smt: false });
    expect(without.verdict.type).toBe('violated');
    const withTerminal = await verifyOpenNet(build(true), contract, { smt: false });
    expect(withTerminal.verdict.type).toBe('proven');
  });
});

describeZ3('EXEC-042 — open-net SMT route', () => {
  it('verifyOpenNet proves the terminal net on the SMT route too', async () => {
    const inp = place<string>('inp');
    const pending = place<string>('pending');
    const out = place<string>('out');
    const halt = place<string>('halt');
    const tA = Transition.builder('tA').inputs(one(inp)).outputs(and(outPlace(halt), outPlace(pending)))
      .action(produces()).build();
    const tB = Transition.builder('tB').inputs(one(pending)).outputs(outPlace(out)).action(produces()).build();
    const build = (terminal: boolean): PetriNet => {
      const b = PetriNet.builder('opn').transitions(tA, tB);
      if (terminal) b.terminal(halt);
      return b.build();
    };
    const contract = OpenNetContract.builder().arrive(1, inp).build();
    const without = await verifyOpenNet(build(false), contract, { maxClasses: 0 });
    expect(without.verdict.type).toBe('violated');
    const withTerminal = await verifyOpenNet(build(true), contract, { maxClasses: 0 });
    expect(withTerminal.route).toBe('smt');
    expect(withTerminal.verdict.type).toBe('proven');
  });
});

describe('EXEC-042 — export', () => {
  it('terminal takes precedence over environment', () => {
    const inp = place<string>('inp');
    const t = Transition.builder('t').inputs(one(inp)).outputs(outPlace(DONE)).action(produces()).build();
    const net = PetriNet.builder('env').transition(t).terminal(DONE).build();
    const line = dotExport(net, { ...DEFAULT_DOT_CONFIG, environmentPlaces: new Set(['done']) })
      .split('\n').find(l => l.includes('p_done'))!;
    expect(line).toContain('#d6d8db');
    expect(line).not.toContain('dashed');
  });

  it('a terminal place renders in the terminal category, ahead of environment/start/end', () => {
    const net = forkNet(true);
    const dot = dotExport(net);
    const line = dot.split('\n').find(l => l.includes('p_done'))!;
    expect(line).toContain('doublecircle');
    expect(line).toContain('#d6d8db');
    expect(line).toContain('#1b1e21');
    const plain = dotExport(forkNet(false)).split('\n').find(l => l.includes('p_done'))!;
    expect(plain).toContain('#cce5ff'); // `end` without the declaration
  });
});
