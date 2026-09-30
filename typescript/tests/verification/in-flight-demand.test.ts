import { describe, it, expect } from 'vitest';
import { BitmapNetExecutor } from '../../src/runtime/bitmap-net-executor.js';
import { PrecompiledNetExecutor } from '../../src/runtime/precompiled-net-executor.js';
import type { Marking } from '../../src/runtime/marking.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place, type Place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { andPlaces, outPlace } from '../../src/core/out.js';
import { tokenOf, type Token } from '../../src/core/token.js';
import type { TransitionAction } from '../../src/core/transition-action.js';
import { deadline, delayed } from '../../src/core/timing.js';
import { matchKey, matchSpec } from '../../src/core/match-spec.js';
import { nameId } from '../../src/core/name.js';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { placeBound, quiescentCount, unreachable } from '../../src/verification/smt-property.js';
import type { SmtVerificationResult } from '../../src/verification/smt-verification-result.js';
import { describeZ3 } from '../fixtures/z3.js';

/**
 * The fix-round witnesses of 2026-09-30 ([VER-004], [EXEC-042], [NU-052], [TIME-013],
 * [CONC-002]): what the executors do on each net, and what the verifier says of it. Mirrors
 * `rust/libpetri/tests/inflight_atomicity.rs` (the "Witnesses of the fix round" section).
 */

const unit = (name: string): Place<unknown> => place<unknown>(name);

/** Deposits into `into` after `ms`. */
const slowTo = (into: string, ms: number): TransitionAction => async ctx => {
  await new Promise(resolve => setTimeout(resolve, ms));
  ctx.output(unit(into), 1);
};
/** Deposits into `into` at once. */
const inlineTo = (into: string): TransitionAction => async ctx => {
  ctx.output(unit(into), 1);
};

interface Backend {
  readonly name: string;
  make(net: PetriNet, tokens: Map<Place<any>, Token<any>[]>): { run(ms: number): Promise<Marking> };
}
const backends: Backend[] = [
  { name: 'BitmapNetExecutor', make: (net, t) => new BitmapNetExecutor(net, t) },
  { name: 'PrecompiledNetExecutor', make: (net, t) => new PrecompiledNetExecutor(net, t) },
];

function tokens(counts: [string, number][]): Map<Place<any>, Token<any>[]> {
  return new Map(counts.map(([n, k]) => [unit(n), Array.from({ length: k }, () => tokenOf<unknown>(1))]));
}
const count = (m: Marking, name: string) => m.peekTokens(unit(name)).length;

/** F1. `t: a → ok` (100 ms), `f: s → done` (10 ms), `done` terminal. */
function terminalAbandonNet(): PetriNet {
  return PetriNet.builder('terminal-abandon').transitions(
    Transition.builder('t').inputs(one(unit('a'))).outputs(outPlace(unit('ok'))).action(slowTo('ok', 100)).build(),
    Transition.builder('f').inputs(one(unit('s'))).outputs(outPlace(unit('done'))).action(slowTo('done', 10)).build(),
  ).terminal(unit('done')).build();
}

/** The ν pair every conflict witness carries: `MINT: SEED → X, Y` with one fresh name, `JOIN` by name into `J`. */
function nuPair(joinPriority = 0): Transition[] {
  const x = place<string>('X'), y = place<string>('Y'), j = place<string>('J');
  const mint = Transition.builder('MINT')
    .inputs(one(unit('SEED')))
    .outputs(andPlaces(x, y))
    .action(async ctx => {
      const n = ctx.freshName();
      ctx.output(x, n);
      ctx.output(y, n);
    })
    .build();
  const join = Transition.builder('JOIN')
    .priority(joinPriority)
    .inputs(one(x), one(y))
    .match(matchSpec(matchKey(x, (v: string) => nameId(v)), matchKey(y, (v: string) => nameId(v))))
    .outputs(outPlace(j))
    .action(async ctx => { ctx.output(j, ctx.input(x)); })
    .build();
  return [mint, join];
}

/** F2 (a). `t: a → p` (50 ms), `H: p + b → ok` priority 10, `L: b + inhibitor(a) → bad`. */
function conflictFeederNet(): PetriNet {
  return PetriNet.builder('conflict-feeder').transitions(
    Transition.builder('t').inputs(one(unit('a'))).outputs(outPlace(unit('p'))).action(slowTo('p', 50)).build(),
    Transition.builder('H').priority(10).inputs(one(unit('p')), one(unit('b'))).outputs(outPlace(unit('ok'))).action(inlineTo('ok')).build(),
    Transition.builder('L').inputs(one(unit('b'))).inhibitor(unit('a')).outputs(outPlace(unit('bad'))).action(inlineTo('bad')).build(),
    ...nuPair(),
  ).build();
}

/** F2 (b). `H: c → ok` priority 10 (100 ms), `L: c → bad`, `g: s + inhibitor(c) → c`. */
function conflictRestartNet(): PetriNet {
  return PetriNet.builder('conflict-restart').transitions(
    Transition.builder('H').priority(10).inputs(one(unit('c'))).outputs(outPlace(unit('ok'))).action(slowTo('ok', 100)).build(),
    Transition.builder('L').inputs(one(unit('c'))).outputs(outPlace(unit('bad'))).action(inlineTo('bad')).build(),
    Transition.builder('g').inputs(one(unit('s'))).inhibitor(unit('c')).outputs(outPlace(unit('c'))).action(inlineTo('c')).build(),
    ...nuPair(),
  ).build();
}

/** F3. `t: a → p` deadline(20) (150 ms), `h: p + b → ok` deadline(20), `v: b → bad` delayed(60). */
function longActionNet(): PetriNet {
  return PetriNet.builder('long-action').transitions(
    Transition.builder('t').inputs(one(unit('a'))).outputs(outPlace(unit('p'))).timing(deadline(20)).action(slowTo('p', 150)).build(),
    Transition.builder('h').inputs(one(unit('p')), one(unit('b'))).outputs(outPlace(unit('ok'))).timing(deadline(20)).action(inlineTo('ok')).build(),
    Transition.builder('v').inputs(one(unit('b'))).outputs(outPlace(unit('bad'))).timing(delayed(60)).action(inlineTo('bad')).build(),
    ...nuPair(),
  ).build();
}

/** `start: req + inhibitor(busy) → busy` (50 ms). */
function guardNet(): PetriNet {
  return PetriNet.builder('inflight-guard').transitions(
    Transition.builder('start').inputs(one(unit('req'))).inhibitor(unit('busy')).outputs(outPlace(unit('busy'))).action(slowTo('busy', 50)).build(),
  ).build();
}

/** `t: p + go → p` priority 1 (50 ms), `u: q + inhibitor(p) → r`. */
function inhibitorNet(): PetriNet {
  return PetriNet.builder('inflight-inhibitor').transitions(
    Transition.builder('t').priority(1).inputs(one(unit('p')), one(unit('go'))).outputs(outPlace(unit('p'))).action(slowTo('p', 50)).build(),
    Transition.builder('u').inputs(one(unit('q'))).inhibitor(unit('p')).outputs(outPlace(unit('r'))).action(inlineTo('r')).build(),
  ).build();
}

describe('the executors on the fix-round witnesses', () => {
  for (const backend of backends) {
    it(`${backend.name} F1: a terminal stop abandons an action in flight`, async () => {
      const m = await backend.make(terminalAbandonNet(), tokens([['a', 1], ['s', 1]])).run(2000);
      expect([count(m, 'a'), count(m, 'ok'), count(m, 'done')]).toEqual([0, 0, 1]);
    });

    it(`${backend.name} F2 (a): L fires while the feeder of the pruner is in flight`, async () => {
      const m = await backend.make(conflictFeederNet(), tokens([['a', 1], ['b', 1], ['SEED', 1]])).run(2000);
      expect(count(m, 'bad')).toBe(1);
    });

    it(`${backend.name} F2 (b): a pruner in flight is not started again, so L takes the refill`, async () => {
      const m = await backend.make(conflictRestartNet(), tokens([['c', 1], ['s', 1], ['SEED', 1]])).run(2000);
      expect([count(m, 'ok'), count(m, 'bad')]).toEqual([1, 1]);
    });

    it(`${backend.name} F3: a long action lets a delayed transition win`, async () => {
      const m = await backend.make(longActionNet(), tokens([['a', 1], ['b', 1], ['SEED', 1]])).run(2000);
      expect(count(m, 'bad')).toBe(1);
    });
  }
});

const state = (verifier: SmtVerifier, counts: [string, number][]) =>
  verifier.initialMarking(m => { for (const [n, k] of counts) m.tokens(unit(n), k); });

describeZ3('the verifier on the fix-round witnesses', () => {
  it('F1: a quiescent count sees the action a terminal stop abandons', async () => {
    const count = (waived: boolean, classes: number) => state(SmtVerifier.forNet(terminalAbandonNet()), [['a', 1], ['s', 1]])
      .property(quiescentCount([unit('a'), unit('ok')], 1, 1, waived ? [unit('done')] : []))
      .enumerationMaxClasses(classes)
      .timeout(30_000)
      .verify();
    for (const classes of [50_000, 0]) {
      const r = await count(false, classes);
      expect(r.verdict.type, r.report).toBe('violated');
      expect(r.report).toContain(
        'a terminal place stops the net without waiting for an action in flight (EXEC-042) '
        + "and the property's lower bound counts a place one of them deposits into",
      );
    }
    // A lower bound the terminal waives needs no split: the terminal rest is excused.
    const waived = await count(true, 50_000);
    expect(waived.verdict.type, waived.report).toBe('proven');
  });

  const conflict = (net: PetriNet, counts: [string, number][], atomic: boolean) =>
    state(SmtVerifier.forNet(net), [...counts, ['SEED', 1]])
      .property(unreachable(new Set([unit('bad')])))
      .mintTransitions('MINT')
      .prioritySemantics('conflict')
      .assumeAtomicFiring(atomic)
      .timeout(30_000)
      .verify();

  it('F2 (a): conflict priority splits the feeder of a pruner', async () => {
    const r = await conflict(conflictFeederNet(), [['a', 1], ['b', 1]], false);
    expect(r.verdict.type, r.report).toBe('violated');
    expect(r.report).toContain('In-flight actions (VER-004): t, H are verified in two steps');
    expect(r.report).toContain('conflict priority (NU-052) reads whether a pruning transition is enabled');
    // The atomic reading keeps the old answer and names the assumption.
    const atomic = await conflict(conflictFeederNet(), [['a', 1], ['b', 1]], true);
    expect(atomic.verdict.type, atomic.report).toBe('proven');
    expect(atomic.report).toContain('ASSUMPTION: every firing is atomic');
  });

  it('F2 (b): a pruner in flight pre-empts nothing', async () => {
    const r = await conflict(conflictRestartNet(), [['c', 1], ['s', 1]], false);
    expect(r.verdict.type, r.report).toBe('violated');
    expect(r.counterexampleTransitions).toContain('L');
  });

  it('F2 fallback: a ν-join pruner cannot be split, so the pruning is off and the report says why', async () => {
    const x = place<string>('X');
    const drain = Transition.builder('DRAIN').priority(-10).inputs(one(x)).outputs(outPlace(unit('DEAD'))).action(inlineTo('DEAD')).build();
    const net = PetriNet.builder('conflict-join').transitions(...nuPair(10), drain).build();
    const run = (semantics: 'conflict' | 'none') => state(SmtVerifier.forNet(net), [['SEED', 1]])
      .property(unreachable(new Set([unit('DEAD')])))
      .mintTransitions('MINT')
      .fragmentMode('extended')
      .prioritySemantics(semantics)
      .verify();
    const on = await run('conflict');
    const none = await run('none');
    expect(on.report).toContain('Conflict priority (NU-052) is off:');
    expect(on.report).toContain('cannot be split: it');
    expect(on.verdict.type, `${on.report}\n${none.report}`).toBe(none.verdict.type);
  });

  it('F3: Route B under assumeNoReaping names its instant actions', async () => {
    const run = (strict: boolean) => state(SmtVerifier.forNet(longActionNet()), [['a', 1], ['b', 1], ['SEED', 1]])
      .property(unreachable(new Set([unit('bad')])))
      .mintTransitions('MINT')
      .assumeNoReaping(strict)
      .verify();
    const strict = await run(true);
    expect(strict.verdict.type, strict.report).toBe('proven');
    expect(strict.route).toBe('nu-scg');
    expect(strict.report).toContain(
      'ASSUMPTION: no transition is reaped (the assume-no-reaping option), none fires after its '
      + 'latest bound, and an action takes no time, i.e. an on-time executor with atomic firings.',
    );
    expect(strict.report).not.toContain('sound AND complete');
    expect(strict.report).toContain('exact only for an on-time executor whose actions take no time');
    const reapAware = await run(false);
    expect(reapAware.verdict.type, reapAware.report).toBe('violated');
  });

  it('F7: a counterexample that restarts a transition in flight says only Rust does that', async () => {
    const r = await state(SmtVerifier.forNet(guardNet()), [['req', 2]]).property(placeBound(unit('busy'), 1)).verify();
    expect(r.verdict.type, r.report).toBe('violated');
    expect(r.report).toContain(
      "NOTE (CONC-002): the counterexample starts 'start' again while its earlier firing is still in "
      + 'flight (inflight:start marked). The Rust executor starts a transition again while its action '
      + 'runs; the Java and TypeScript executors never do, so on them this counterexample may be a '
      + 'false alarm.\n',
    );
    // TypeScript has no ctx.flush() to report (F5 is Rust and Python only).
    expect(r.report).not.toContain('ctx.flush()');
    // A counterexample without a restart carries no such note.
    const plain: SmtVerificationResult = await state(SmtVerifier.forNet(inhibitorNet()), [['p', 1], ['q', 1], ['go', 1]])
      .property(unreachable(new Set([unit('r')])))
      .verify();
    expect(plain.verdict.type, plain.report).toBe('violated');
    expect(plain.report).not.toContain('NOTE (CONC-002)');
  });
});
