import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import { existsSync, mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { describeZ3 } from '../fixtures/z3.js';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import {
  deadlockFree, mutualExclusion, nameAligned, placeBound, unreachable, type SmtProperty,
} from '../../src/verification/smt-property.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { flatten } from '../../src/verification/encoding/net-flattener.js';
import {
  alwaysAvailable, bounded, ignore, type EnvironmentAnalysisMode,
} from '../../src/verification/analysis/environment-analysis-mode.js';
import { vectorize, violationPredicate } from '../../src/verification/z3/abstract-replayer.js';
import {
  decodeBoundedRun, encodeBoundedRun, replayRun, runWitnessPhase, type FiringBoundSolver,
} from '../../src/verification/z3/bounded-run.js';
import { Z3_ENV } from '../../src/verification/z3/z3-process.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { environmentPlace, place, type Place } from '../../src/core/place.js';
import { exactly, one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import { bindProducers } from '../fixtures/producing-actions.js';
import { allMints } from '../fixtures/all-mints.js';
import { verificationNets } from '../fixtures/verification-nets.js';

/**
 * VER-025, the bounded witness phase: directly before the flat fixpoint query, one bounded run
 * of at most `witnessDepth` steps (default 8), injection steps included, asks for a violation.
 * A run it finds is replayed, trimmed and reported `violated`; everything else falls through.
 *
 * The net of most tests: environment place `e`, `t: one(e) -> p1`, empty initial marking. Flat
 * places are `[e, p1]`, the one transition has selector 0, the injection into `e` selector 1,
 * and 2 idles.
 */
const e = environmentPlace<unknown>('e');
const p1 = place('p1');
const T_FIRE = 0;
const INJECT = 1;
const IDLE = 2;

function pairNet(): PetriNet {
  const t = Transition.builder('t').inputs(one(e.place)).outputs(outPlace(p1)).build();
  return bindProducers(PetriNet.builder('envPair').transitions(t).build());
}

function pairFlat(mode: EnvironmentAnalysisMode = bounded(2)) {
  return flatten(pairNet(), new Set([e]), mode);
}

const HEADER = '  Bounded witness phase (VER-025):';
const status = (line: string): string => `${HEADER}\n    Status: ${line}\n`;

/** A `sat` reply whose model sets the selectors `s0, s1, …` in z3's layout. */
function satReply(...selectors: number[]): string {
  return `sat\n(\n${selectors.map((s, i) => `  (define-fun s${i} () Int\n    ${s})`).join('\n')}\n)`;
}

describe('bounded run with injection steps (VER-025) — building blocks', () => {
  it('encodes the injection selectors after the transitions, the bound as a guard, and idles past them', () => {
    const flat = pairFlat();
    expect(flat.places.map((p) => p.name)).toEqual(['e', 'p1']);
    expect(encodeBoundedRun(flat, [0, 0], placeBound(p1, 1), new Set(), [], 2)).toBe([
      '; Bounded run (VER-019): 2 steps of the exact step relation from M0, idle',
      '; only at the end; sat = a run to a violating marking.',
      '(set-logic QF_LIA)',
      '(declare-const s0 Int)',
      '(declare-const s1 Int)',
      '(declare-const m1_0 Int)',
      '(declare-const m1_1 Int)',
      '(declare-const m2_0 Int)',
      '(declare-const m2_1 Int)',
      '(assert (and (>= s0 0) (<= s0 2)))',
      '(assert (=> (= s0 2) (= s1 2)))',
      '(assert (=> (= s0 0) (>= 0 1)))',
      '(assert (=> (= s0 1) (< 0 2)))',
      '(assert (= m1_0 (ite (= s0 0) (- 0 1) (ite (= s0 1) (+ 0 1) 0))))',
      '(assert (= m1_1 (ite (= s0 0) (+ 0 1) 0)))',
      '(assert (<= m1_0 2))',
      '(assert (and (>= s1 0) (<= s1 2)))',
      '(assert (=> (= s1 0) (>= m1_0 1)))',
      '(assert (=> (= s1 1) (< m1_0 2)))',
      '(assert (= m2_0 (ite (= s1 0) (- m1_0 1) (ite (= s1 1) (+ m1_0 1) m1_0))))',
      '(assert (= m2_1 (ite (= s1 0) (+ m1_1 1) m1_1)))',
      '(assert (<= m2_0 2))',
      '(assert (> m2_1 1))',
      '(check-sat)',
      '(get-model)',
    ].join('\n'));
  });

  it('gives an unbounded injection a selector and an update, and no guard line', () => {
    const script = encodeBoundedRun(pairFlat(alwaysAvailable()), [0, 0], placeBound(p1, 1), new Set(), [], 1);
    expect(script).toContain('(assert (and (>= s0 0) (<= s0 2)))');
    expect(script).toContain('(assert (= m1_0 (ite (= s0 0) (- 0 1) (ite (= s0 1) (+ 0 1) 0))))');
    expect(script).not.toMatch(/\(< /);
  });

  it('keeps the script of a net without injection: T idles and no selector lies past it', () => {
    // `ignore` leaves the environment place an ordinary one: J = 0.
    const script = encodeBoundedRun(pairFlat(ignore()), [1, 0], placeBound(p1, 0), new Set(), [], 2);
    expect(script).toContain('(assert (and (>= s0 0) (<= s0 1)))');
    expect(script).toContain('(assert (=> (= s0 1) (= s1 1)))');
    expect(script).toContain('(assert (= m1_0 (ite (= s0 0) (- 1 1) 1)))');
    expect(script).not.toMatch(/\(< /);
  });

  it('orders injections and post-caps by place index, whatever order the environment places were declared in', () => {
    const a = environmentPlace<unknown>('a');
    const b = environmentPlace<unknown>('b');
    const out = place('out');
    const net = bindProducers(PetriNet.builder('twoEnv').transitions(
      Transition.builder('t').inputs(one(a.place), one(b.place)).outputs(outPlace(out)).build(),
    ).build());
    const encode = (...declared: (typeof a)[]): string => {
      const flat = flatten(net, new Set(declared), bounded(1));
      return encodeBoundedRun(flat, flat.places.map(() => 0), placeBound(out, 0), new Set(), [], 1);
    };
    const script = encode(a, b);
    expect(encode(b, a)).toBe(script);
    const flat = flatten(net, new Set([a, b]), bounded(1));
    const [first, second] = [a, b].map((p) => flat.placeIndex.get(p.place.name)!).sort((x, y) => x - y);
    // Selectors 1 and 2 inject into the lower and the higher index; the caps follow in the same order.
    expect(script).toContain(`(assert (=> (= s0 1) (< 0 1)))\n(assert (=> (= s0 2) (< 0 1)))`);
    expect(script).toContain(`(assert (<= m1_${first} 1))\n(assert (<= m1_${second} 1))`);
    expect(script).toContain(`(assert (= m1_${first} (ite (= s0 0) (- 0 1) (ite (= s0 1) (+ 0 1) 0))))`);
    expect(script).toContain(`(assert (= m1_${second} (ite (= s0 0) (- 0 1) (ite (= s0 2) (+ 0 1) 0))))`);
  });

  it('decodes a selector in [T, T+J) as a step and T+J as idle', () => {
    const reply = satReply(INJECT, T_FIRE, IDLE, INJECT);
    expect(decodeBoundedRun(reply, 2, 4)).toEqual([INJECT, T_FIRE]);
    // Read with the transition count alone, the injection selector would end the run.
    expect(decodeBoundedRun(reply, 1, 4)).toEqual([]);
  });

  it('replays an injection under its bound, names it inject(<place>), and refuses one at the bound', () => {
    const flat = pairFlat();
    const always = (): boolean => true;
    expect(replayRun(flat, [0, 0], [INJECT, INJECT], always)).toEqual({
      states: [[0, 0], [1, 0], [2, 0]],
      steps: ['inject(e)', 'inject(e)'],
    });
    // bounded(2): the guard is M[e] < 2.
    expect(replayRun(flat, [0, 0], [INJECT, INJECT, INJECT], always)).toBeNull();
    expect(replayRun(flat, [2, 0], [INJECT], always)).toBeNull();
    expect(replayRun(flat, [0, 0], [INJECT, T_FIRE, INJECT, T_FIRE], always)?.steps)
      .toEqual(['inject(e)', 't', 'inject(e)', 't']);
  });

  it('replays an unbounded injection at any count', () => {
    const replayed = replayRun(pairFlat(alwaysAvailable()), [0, 0], [INJECT, INJECT, INJECT], () => true);
    expect(replayed?.states.at(-1)).toEqual([3, 0]);
    expect(replayed?.steps).toEqual(['inject(e)', 'inject(e)', 'inject(e)']);
  });
});

describe('runWitnessPhase (VER-025) — one query, stub replies', () => {
  const flat = pairFlat();
  const m0 = MarkingState.builder().build();
  const phase = (
    reply: FiringBoundSolver, property: SmtProperty = placeBound(p1, 1), budgetMs = 60_000, marking = m0,
  ) => runWitnessPhase(flat, marking, property, new Set(), [], reply, { depth: 8, budgetMs });
  const noCall: FiringBoundSolver = async () => {
    throw new Error('no solver call expected');
  };

  it('asks one query, at the depth given, under the dump label witness', async () => {
    const asked: [string, string][] = [];
    const outcome = await runWitnessPhase(flat, m0, placeBound(p1, 1), new Set(), [], async (script, label) => {
      asked.push([script, label]);
      return 'unsat';
    }, { depth: 5, budgetMs: 60_000 });
    expect(outcome).toEqual({ kind: 'none' });
    expect(asked).toEqual([[encodeBoundedRun(flat, [0, 0], placeBound(p1, 1), new Set(), [], 5), 'witness']]);
  });

  it('reads an injection selector as a step of the run, not as idle', async () => {
    const outcome = await phase(async () => satReply(INJECT, T_FIRE, INJECT, T_FIRE, IDLE, IDLE, IDLE, IDLE));
    expect(outcome).toEqual({
      kind: 'violated',
      states: [[0, 0], [1, 0], [0, 1], [1, 1], [0, 2]],
      steps: ['inject(e)', 't', 'inject(e)', 't'],
    });
  });

  it('trims the steps the solver padded the run with, and reports the trimmed run replayed', async () => {
    // p1 <= 0 is violated after inject, t. The model also injects twice more and fires t again.
    const padded = satReply(INJECT, INJECT, T_FIRE, T_FIRE, INJECT, INJECT, IDLE, IDLE);
    const bad = violationPredicate(flat, placeBound(p1, 0), new Set());
    expect(replayRun(flat, [0, 0], decodeBoundedRun(padded, 2, 8)!, bad)?.steps).toHaveLength(6);
    expect(await phase(async () => padded, placeBound(p1, 0))).toEqual({
      kind: 'violated',
      states: [[0, 0], [1, 0], [0, 1]],
      steps: ['inject(e)', 't'],
    });
  });

  describe('the trim ends the run at the first violating marking', () => {
    // q(1), u(1); s1: q -> r; s2: u -> p; s3: r -> q. p and q are marked together after s2
    // from M0, and again after s1, s2, s3; s1 clears the violation and s3 needs s1.
    const [q, u, r, p] = ['q', 'u', 'r', 'p'].map((n) => place(n)) as [Place<any>, Place<any>, Place<any>, Place<any>];
    const net = bindProducers(PetriNet.builder('leaveAndReturn').transitions(
      Transition.builder('s1').inputs(one(q)).outputs(outPlace(r)).build(),
      Transition.builder('s2').inputs(one(u)).outputs(outPlace(p)).build(),
      Transition.builder('s3').inputs(one(r)).outputs(outPlace(q)).build(),
    ).build());
    const closed = flatten(net);
    const start = MarkingState.builder().tokens(q, 1).tokens(u, 1).build();
    const property = mutualExclusion(p, q);
    const s = (name: string): number => closed.transitions.findIndex((ft) => ft.name === name);
    const idle = closed.transitions.length;
    const trimmed = (...selectors: number[]) => runWitnessPhase(
      closed, start, property, new Set(), [],
      async () => satReply(...selectors, ...new Array<number>(8 - selectors.length).fill(idle)),
      { depth: 8, budgetMs: 60_000 },
    );
    const afterS2 = {
      kind: 'violated',
      states: [vectorize(start, closed), vectorize(MarkingState.builder().tokens(q, 1).tokens(p, 1).build(), closed)],
      steps: ['s2'],
    };

    it('a run that passes a violating marking and then continues is cut there', async () => {
      const run = [s('s2'), s('s1'), s('s3')];
      // The whole run replays, and no single step can be removed from it: without s3 it ends
      // off the violation, without s1 s3 is not enabled, without s2 p is never marked.
      const bad = violationPredicate(closed, property, new Set());
      expect(replayRun(closed, vectorize(start, closed), run, bad)?.steps).toEqual(['s2', 's1', 's3']);
      for (const k of [0, 1, 2]) {
        expect(replayRun(closed, vectorize(start, closed), run.filter((_, i) => i !== k), bad)).toBeNull();
      }
      expect(await trimmed(...run)).toEqual(afterS2);
    });

    it('accepts a removal whose prefix violates although its tail is no longer enabled', async () => {
      // s1, s2, s3 violates at its last marking only. Without s1 the run violates after s2,
      // and s3, which needs the token s1 moved, is never taken.
      const run = [s('s1'), s('s2'), s('s3')];
      const bad = violationPredicate(closed, property, new Set());
      expect(replayRun(closed, vectorize(start, closed), run, bad)?.steps).toEqual(['s1', 's2', 's3']);
      expect(replayRun(closed, vectorize(start, closed), [s('s2'), s('s3')], bad)).toBeNull();
      expect(await trimmed(...run)).toEqual(afterS2);
    });

    it('M0 violating is the empty run although the model is a cycle no single step can leave', async () => {
      // a(1) <-> b, a <= 0: M0 violates. The model walks the cycle four times; dropping one
      // step leaves a step that is not enabled or a run that ends in b.
      const [a, b] = [place('a'), place('b')];
      const cycle = flatten(bindProducers(PetriNet.builder('cycle').transitions(
        Transition.builder('t1').inputs(one(a)).outputs(outPlace(b)).build(),
        Transition.builder('t2').inputs(one(b)).outputs(outPlace(a)).build(),
      ).build()));
      const m0 = MarkingState.builder().tokens(a, 1).build();
      const [t1, t2] = ['t1', 't2'].map((n) => cycle.transitions.findIndex((ft) => ft.name === n)) as [number, number];
      const run = [t1, t2, t1, t2, t1, t2, t1, t2];
      const bad = violationPredicate(cycle, placeBound(a, 0), new Set());
      expect(replayRun(cycle, vectorize(m0, cycle), run, bad)?.steps).toHaveLength(8);
      for (let k = 0; k < run.length; k++) {
        expect(replayRun(cycle, vectorize(m0, cycle), run.filter((_, i) => i !== k), bad), `without step ${k}`).toBeNull();
      }
      const outcome = await runWitnessPhase(
        cycle, m0, placeBound(a, 0), new Set(), [], async () => satReply(...run), { depth: 8, budgetMs: 60_000 },
      );
      expect(outcome).toEqual({ kind: 'violated', states: [vectorize(m0, cycle)], steps: [] });
    });
  });

  it('repeats the trim until a pass removes nothing', async () => {
    // sig(1), src(2); drain: sig -> gone; feed: src -> sig; gate: exactly(2, sig) -> done.
    // After drain the gate needs both feeds; without it one feed is enough. A pass goes last to
    // first, so it drops drain (index 0) last, and only the next pass can drop the feed that
    // has become needless.
    const [sig, src, gone, done] = [place('sig'), place('src'), place('gone'), place('done')];
    const gated = flatten(bindProducers(PetriNet.builder('gated').transitions(
      Transition.builder('drain').inputs(one(sig)).outputs(outPlace(gone)).build(),
      Transition.builder('feed').inputs(one(src)).outputs(outPlace(sig)).build(),
      Transition.builder('gate').inputs(exactly(2, sig)).outputs(outPlace(done)).build(),
    ).build()));
    const m0 = MarkingState.builder().tokens(sig, 1).tokens(src, 2).build();
    const property = placeBound(done, 0);
    const [drain, feed, gate] = ['drain', 'feed', 'gate']
      .map((n) => gated.transitions.findIndex((ft) => ft.name === n)) as [number, number, number];
    const idle = gated.transitions.length;
    const initial = vectorize(m0, gated);
    const bad = violationPredicate(gated, property, new Set());
    const run = [drain, feed, feed, gate];
    // The first pass: no removal but that of drain leaves a run to the violation.
    expect(replayRun(gated, initial, run, bad)?.steps).toEqual(['drain', 'feed', 'feed', 'gate']);
    expect(replayRun(gated, initial, [drain, feed, feed], bad)).toBeNull();
    expect(replayRun(gated, initial, [drain, feed, gate], bad)).toBeNull();
    // What one pass leaves, and the removal the second pass finds in it.
    expect(replayRun(gated, initial, [feed, feed, gate], bad)?.steps).toEqual(['feed', 'feed', 'gate']);
    expect(replayRun(gated, initial, [feed, gate], bad)?.steps).toEqual(['feed', 'gate']);
    const outcome = await runWitnessPhase(
      gated, m0, property, new Set(), [],
      async () => satReply(...run, idle, idle, idle, idle), { depth: 8, budgetMs: 60_000 },
    );
    expect(outcome.kind === 'violated' && outcome.steps).toEqual(['feed', 'gate']);
    expect(outcome.kind === 'violated' && outcome.states).toHaveLength(3);
  });

  it('reports M0 violating as the empty run', async () => {
    const marked = MarkingState.builder().tokens(p1, 2).build();
    const outcome = await phase(async () => satReply(...new Array<number>(8).fill(IDLE)), placeBound(p1, 1), 60_000, marked);
    expect(outcome).toEqual({ kind: 'violated', states: [vectorize(marked, flat)], steps: [] });
  });

  describe('the trim polls before each candidate (VER-013)', () => {
    const polled = (poll: () => void, ...selectors: number[]) => runWitnessPhase(
      flat, m0, placeBound(p1, 1), new Set(), [],
      async () => satReply(...selectors, ...new Array<number>(8 - selectors.length).fill(IDLE)),
      { depth: 8, budgetMs: 60_000, poll },
    );

    it('a poll that throws ends the phase with its error, not as inconclusive', async () => {
      const stop = new Error('stop');
      let calls = 0;
      await expect(polled(() => {
        calls++;
        throw stop;
      }, INJECT, T_FIRE, INJECT, T_FIRE)).rejects.toBe(stop);
      expect(calls).toBe(1);
    });

    it('polls once per candidate', async () => {
      // No step of inject, t, inject, t can go: one pass of four candidates, none kept.
      let calls = 0;
      const outcome = await polled(() => { calls++; }, INJECT, T_FIRE, INJECT, T_FIRE);
      expect(outcome.kind === 'violated' && outcome.steps).toHaveLength(4);
      expect(calls).toBe(4);
    });

    it('never polls for a run with no candidate: the empty run', async () => {
      const marked = MarkingState.builder().tokens(p1, 2).build();
      const outcome = await runWitnessPhase(
        flat, marked, placeBound(p1, 1), new Set(), [],
        // The model pads M0 with steps; the prefix cut drops them before any candidate.
        async () => satReply(INJECT, T_FIRE, IDLE, IDLE, IDLE, IDLE, IDLE, IDLE),
        { depth: 8, budgetMs: 60_000, poll: () => { throw new Error('no poll expected'); } },
      );
      expect(outcome).toEqual({ kind: 'violated', states: [vectorize(marked, flat)], steps: [] });
    });
  });

  it('unsat is no run, never a proof', async () => {
    expect(await phase(async () => 'unsat')).toEqual({ kind: 'none' });
  });

  it('unknown is inconclusive', async () => {
    expect(await phase(async () => 'unknown')).toEqual({
      kind: 'inconclusive', reason: 'the bounded run at depth 8 answered unknown',
    });
  });

  it('a transport failure is inconclusive, with its message', async () => {
    expect(await phase(async () => {
      throw new Error('z3 did not exit within 2500 ms and was killed');
    })).toEqual({ kind: 'inconclusive', reason: 'z3 did not exit within 2500 ms and was killed' });
  });

  it('a spent budget is inconclusive, and sends nothing', async () => {
    expect(await phase(noCall, placeBound(p1, 1), 0)).toEqual({
      kind: 'inconclusive', reason: 'time budget of 0 ms exhausted',
    });
  });

  it('a run that does not replay is inconclusive', async () => {
    const reason = 'the bounded run did not replay under the exact semantics';
    // t without a token in e.
    expect(await phase(async () => satReply(T_FIRE, IDLE, IDLE, IDLE, IDLE, IDLE, IDLE, IDLE)))
      .toEqual({ kind: 'inconclusive', reason });
    // A third injection at the bound.
    expect(await phase(async () => satReply(INJECT, INJECT, INJECT, IDLE, IDLE, IDLE, IDLE, IDLE)))
      .toEqual({ kind: 'inconclusive', reason });
    // Every step enabled, the last marking not violating.
    expect(await phase(async () => satReply(INJECT, T_FIRE, IDLE, IDLE, IDLE, IDLE, IDLE, IDLE)))
      .toEqual({ kind: 'inconclusive', reason });
    // No selector in the model.
    expect(await phase(async () => 'sat\n(\n)')).toEqual({ kind: 'inconclusive', reason });
  });

  it('refuses a name-alignment property: a run of counts carries no names (NU-055)', async () => {
    const outcome = await phase(noCall, nameAligned(e.place, p1));
    expect(outcome.kind).toBe('inconclusive');
    expect(outcome.kind === 'inconclusive' && outcome.reason)
      .toContain('decided only by the name-partition state-class graph (NU-055, Route B)');
  });
});

describe.skipIf(process.platform === 'win32')('SmtVerifier bounded witness phase (VER-025) — stub z3', () => {
  let root: string;
  let savedEnv: string | undefined;

  beforeAll(() => {
    root = mkdtempSync(join(tmpdir(), 'libpetri-witness-'));
    savedEnv = process.env[Z3_ENV];
  });

  afterAll(() => {
    if (savedEnv == null) delete process.env[Z3_ENV];
    else process.env[Z3_ENV] = savedEnv;
    rmSync(root, { recursive: true, force: true });
  });

  /**
   * A stub `z3` answering the bounded-run script with `witness` and every other script with
   * `horn` (shell lines). It records the scripts it was asked, in order, the arguments of the
   * bounded-run call and its script.
   */
  function stub(name: string, witness: string, horn: string = "echo 'unknown'") {
    const dir = join(root, name);
    mkdirSync(dir, { recursive: true });
    const script = join(dir, 'z3');
    writeFileSync(script, `#!/bin/sh
if [ "$1" = "--version" ]; then echo 'Z3 version 4.16.0 - 64 bit'; exit 0; fi
script=$(cat)
case "$script" in
  *"; Bounded run (VER-019)"*)
    echo witness >> '${dir}/calls'
    echo "$@" > '${dir}/witness.args'
    printf '%s' "$script" > '${dir}/witness.smt2'
${witness}
    ;;
  *)
    echo horn >> '${dir}/calls'
${horn}
    ;;
esac
`, { mode: 0o755 });
    process.env[Z3_ENV] = script;
    return {
      dir,
      calls: (): string[] =>
        existsSync(join(dir, 'calls')) ? readFileSync(join(dir, 'calls'), 'utf8').trim().split('\n') : [],
      witnessArgs: (): string => readFileSync(join(dir, 'witness.args'), 'utf8').trim(),
      witnessScript: (): string => readFileSync(join(dir, 'witness.smt2'), 'utf8'),
    };
  }

  const sat = (...selectors: number[]): string => `cat <<'EOF'\n${satReply(...selectors)}\nEOF`;
  const STUB_TIMEOUT = 60_000;

  /**
   * The pair net with only the witness and the fixpoint query left to reach the stub. The stub
   * answers at once; the timeout is long so that a loaded machine does not turn a reply into a
   * transport failure (the phase gets an eighth of it).
   */
  function verifier(property: SmtProperty = placeBound(p1, 1)): SmtVerifier {
    return SmtVerifier.forNet(pairNet())
      .enumerationMaxClasses(0)
      .property(property)
      .environmentPlaces(e)
      .environmentMode(bounded(2))
      .linearBound(false)
      .stateEquationPhase(false)
      .firingBound(false)
      .timeout(STUB_TIMEOUT);
  }

  // Each inconclusive or empty outcome: its own report line, then the fixpoint query, whose
  // `unknown` here is the verdict. None of them is ever a proof.
  const fallThrough: [string, string, string][] = [
    ['unsat', "echo 'unsat'", 'no run of at most 8 steps reaches a violation (not a proof)'],
    ['unknown', "echo 'unknown'", 'inconclusive (the bounded run at depth 8 answered unknown)'],
    ['a transport failure', "echo 'garbage'", 'inconclusive (Unexpected Z3 output: garbage)'],
    [
      'a run that does not replay', sat(T_FIRE, IDLE, IDLE, IDLE, IDLE, IDLE, IDLE, IDLE),
      'inconclusive (the bounded run did not replay under the exact semantics)',
    ],
  ];
  for (const [name, reply, line] of fallThrough) {
    it(`${name} falls through to the fixpoint query with its own report line`, async () => {
      const z3 = stub(`fall-${name.replace(/\W+/g, '-')}`, reply);
      const result = await verifier().verify();
      expect(result.report).toContain(status(line));
      expect(z3.calls()).toEqual(['witness', 'horn']);
      expect(result.verdict.type, result.report).toBe('unknown');
      expect(result.report).not.toContain('PROVEN');
    });
  }

  it('unsat followed by a fixpoint proof is the fixpoint proof, certified as without the phase', async () => {
    // The stub proves with the invariant `true` only where the certificate check would accept
    // it, so the check is switched off: what is pinned is that `proven` names IC3/PDR.
    const z3 = stub('unsat-then-proven', "echo 'unsat'", `echo 'sat'
echo '(define-fun Reachable ((x!0 Int) (x!1 Int)) Bool true)'`);
    const result = await verifier().certificateCheck(false).verify();
    expect(z3.calls()).toEqual(['witness', 'horn']);
    expect(result.report).toContain(status('no run of at most 8 steps reaches a violation (not a proof)'));
    expect(result.verdict, result.report).toMatchObject({ type: 'proven', method: 'IC3/PDR' });
  });

  it('a spent phase budget falls through without a query', async () => {
    // timeout 1 ms: the phase budget is max(1, floor(1 / 8)) = 1 ms, gone once the script is encoded.
    const z3 = stub('spent', "echo 'unsat'");
    const result = await verifier().timeout(1).verify();
    expect(result.report).toContain(status('inconclusive (time budget of 1 ms exhausted)'));
    expect(z3.calls()).toEqual(['horn']);
    expect(result.verdict.type, result.report).toBe('unknown');
  });

  it('gives the query an eighth of the timeout', async () => {
    const z3 = stub('eighth', "echo 'unsat'");
    await verifier().timeout(80_000).verify();
    const soft = /-t:(\d+)/.exec(z3.witnessArgs());
    expect(soft, z3.witnessArgs()).not.toBeNull();
    expect(Number(soft![1])).toBeGreaterThan(0);
    expect(Number(soft![1])).toBeLessThanOrEqual(10_000);
  });

  it('a sat run with injection steps is violated, confirmed, in the witness form', async () => {
    const z3 = stub('sat', sat(INJECT, T_FIRE, INJECT, T_FIRE, IDLE, IDLE, IDLE, IDLE));
    const result = await verifier().verify();
    expect(z3.calls(), 'no fixpoint query follows').toEqual(['witness']);
    expect(result.verdict.type, result.report).toBe('violated');
    expect(result.route).toBe('smt');
    expect(result.counterexampleConfirmed).toBe(true);
    expect(result.counterexampleTransitions).toEqual(['inject(e)', 't', 'inject(e)', 't']);
    expect(result.counterexampleTrace.map(String)).toEqual(['{}', '{e:1}', '{p1:1}', '{e:1, p1:1}', '{p1:2}']);
    expect(result.report).toContain([
      HEADER,
      '    Status: a run of 4 steps reaches a violation (replayed; depth 8)',
      '',
      '=== RESULT ===',
      '',
      'VIOLATED: Place p1 bounded by 1',
      '  Counterexample trace (replay order, 5 states):',
      '    0: {}',
      '    1: {e:1}',
      '    2: {p1:1}',
      '    3: {e:1, p1:1}',
      '    4: {p1:2}',
      '  Firing sequence: inject(e) -> t -> inject(e) -> t',
      '',
      '  WARNING: This counterexample is in UNTIMED semantics.',
      '  It may be spurious if timing constraints prevent this sequence.',
    ].join('\n'));
  });

  it('reports the trimmed run and its length', async () => {
    stub('trim', sat(INJECT, INJECT, T_FIRE, T_FIRE, INJECT, INJECT, IDLE, IDLE));
    const result = await verifier(placeBound(p1, 0)).verify();
    expect(result.report).toContain(status('a run of 2 steps reaches a violation (replayed; depth 8)'));
    expect(result.counterexampleTransitions).toEqual(['inject(e)', 't']);
    expect(result.counterexampleTrace).toHaveLength(3);
  });

  it('M0 already violating is the empty firing sequence', async () => {
    stub('m0', sat(...new Array<number>(8).fill(IDLE)));
    const result = await verifier().initialMarking((m) => m.tokens(p1, 2)).verify();
    expect(result.verdict.type, result.report).toBe('violated');
    expect(result.report).toContain(status('a run of 0 steps reaches a violation (replayed; depth 8)'));
    expect(result.report).toContain('  Counterexample trace (replay order, 1 states):\n    0: {p1:2}\n\n  WARNING');
    expect(result.report).not.toContain('Firing sequence:');
    expect(result.counterexampleTrace).toHaveLength(1);
    expect(result.counterexampleTransitions).toEqual([]);
    expect(result.counterexampleConfirmed).toBe(true);
  });

  it('runs with counterexampleReplay(false): that option governs the replay after the fixpoint query', async () => {
    const z3 = stub('replay-off', sat(INJECT, T_FIRE, INJECT, T_FIRE, IDLE, IDLE, IDLE, IDLE));
    const result = await verifier().counterexampleReplay(false).verify();
    expect(z3.calls()).toEqual(['witness']);
    expect(result.verdict.type, result.report).toBe('violated');
    expect(result.counterexampleConfirmed).toBe(true);
    expect(result.counterexampleTransitions).toEqual(['inject(e)', 't', 'inject(e)', 't']);
  });

  it('witnessDepth(0) disables the phase: verdict, route and report are those of the pipeline without it', async () => {
    const on = stub('depth-on', "echo 'unsat'");
    const withPhase = await verifier().verify();
    expect(on.calls()).toEqual(['witness', 'horn']);
    const off = stub('depth-off', "echo 'unsat'");
    const without = await verifier().witnessDepth(0).verify();
    expect(off.calls()).toEqual(['horn']);
    expect(without.report).not.toContain('VER-025');
    const phaseLines = status('no run of at most 8 steps reaches a violation (not a proof)');
    expect(withPhase.report).toContain(phaseLines);
    expect(withPhase.report.replace(phaseLines, '')).toBe(without.report);
    expect(without.verdict).toEqual(withPhase.verdict);
    expect(without.route).toBe(withPhase.route);
    expect(verifier().witnessDepth(0).encodeScripts().witness).toBeNull();
  });

  it('witnessDepth(n) asks one query at depth n, the script encodeScripts() reports', async () => {
    const z3 = stub('depth-3', "echo 'unsat'");
    const result = await verifier().witnessDepth(3).verify();
    expect(z3.calls()).toEqual(['witness', 'horn']);
    expect(result.report).toContain(status('no run of at most 3 steps reaches a violation (not a proof)'));
    const script = z3.witnessScript();
    expect(script.split('\n')[0]).toBe('; Bounded run (VER-019): 3 steps of the exact step relation from M0, idle');
    expect(script).toBe(verifier().witnessDepth(3).encodeScripts().witness);
    expect(verifier().encodeScripts().witness).toBe(
      encodeBoundedRun(pairFlat(), [0, 0], placeBound(p1, 1), new Set(), [], 8),
    );
  });

  it('rejects a negative or fractional depth', () => {
    expect(() => verifier().witnessDepth(-1)).toThrow(new Error('witnessDepth must be non-negative, got -1'));
    expect(() => verifier().witnessDepth(1.5)).toThrow('witnessDepth must be an integer, got 1.5');
    expect(() => verifier().witnessDepth(Number.NaN)).toThrow('witnessDepth must be an integer, got NaN');
  });

  // A stop during the phase (VER-013): the header keeps its one status line, then the stop is
  // the verdict, reported against the step `witness phase`.
  const STOP_REASON = 'verification cancelled during witness phase';
  const stopReport = (line: string): string => `${status(line)}\n=== RESULT ===\n\nUNKNOWN: ${STOP_REASON}`;

  it('is its own step of the total budget: a stop while its query runs is reported against `witness phase`', async () => {
    // The stub records the bounded-run call and never answers. Cancelling once it runs kills
    // it; the status line then carries the stop's reason, not the transport's failure.
    const z3 = stub('step-in-query', 'exec sleep 30');
    const controller = new AbortController();
    const running = verifier().signal(controller.signal).verify();
    while (z3.calls().length === 0) await new Promise((r) => setTimeout(r, 10));
    controller.abort();
    const result = await running;
    expect(z3.calls()).toEqual(['witness']);
    expect(result.verdict, result.report).toEqual({ type: 'unknown', reason: STOP_REASON });
    expect(result.report).toContain(stopReport(`inconclusive (${STOP_REASON})`));
    expect(result.report).not.toContain('z3 killed');
  }, 30_000);

  it('a stop after its query answered keeps the status the answer gave', async () => {
    // The stub records the bounded-run call; the signal reads as aborted from then on, so the
    // stop is seen at the next checkpoint, the one that opens the fixpoint query.
    const z3 = stub('step', "echo 'unsat'");
    const signal = {
      get aborted() { return z3.calls().length > 0; },
      addEventListener() {},
      removeEventListener() {},
    } as unknown as AbortSignal;
    const result = await verifier().signal(signal).verify();
    expect(z3.calls()).toEqual(['witness']);
    expect(result.verdict, result.report).toEqual({ type: 'unknown', reason: STOP_REASON });
    expect(result.report).toContain(stopReport('no run of at most 8 steps reaches a violation (not a proof)'));
  });

  it('polls the deadline in the trim: a stop there is charged to `witness phase` (VER-013)', async () => {
    // The signal reports itself aborted only when read from inside the trim, so no checkpoint
    // and no z3 start sees it. Only the per-candidate poll can turn it into the verdict;
    // without it the run below is reported violated.
    const z3 = stub('trim-stop', sat(INJECT, T_FIRE, INJECT, T_FIRE, IDLE, IDLE, IDLE, IDLE));
    const signal = {
      get aborted() { return (new Error().stack ?? '').includes('trimRun'); },
      addEventListener() {},
      removeEventListener() {},
    } as unknown as AbortSignal;
    const result = await verifier().signal(signal).verify();
    expect(z3.calls()).toEqual(['witness']);
    expect(result.verdict, result.report).toEqual({ type: 'unknown', reason: STOP_REASON });
    expect(result.report).toContain(stopReport(`inconclusive (${STOP_REASON})`));
    expect(result.report).not.toContain('Status: a run of');
  });

  it('never enters on the name-coloured encoding', async () => {
    const built = verificationNets['nuScatterGather']!();
    const budget = built.places.get('budget')!;
    const z3 = stub('coloured', "echo 'unsat'");
    const coloured = (): SmtVerifier => SmtVerifier.forNet(built.net).mintTransitions(...allMints(built.net))
      .enumerationMaxClasses(0)
      .initialMarking(built.initialMarking)
      .property(placeBound(budget, 2))
      .budgetPlaces(budget)
      .linearBound(false)
      .timeout(STUB_TIMEOUT);
    const result = await coloured().verify();
    expect(result.report).toContain('ν-encoding: name-coloured');
    expect(z3.calls()).toEqual(['horn']);
    expect(result.report).not.toContain('VER-025');
    const scripts = coloured().encodeScripts();
    expect(scripts.coloured).toBe(true);
    expect(scripts.witness).toBeNull();
  });

  it('is skipped on a ν-net the ν guard answers unknown: a quiescence property', async () => {
    // A marked coloured place keeps the net off both ν routes, so the flat encoding answers.
    const built = verificationNets['nuScatterGather']!();
    const P = (name: string) => built.places.get(name)!;
    const z3 = stub('nu-quiescence', sat(0, 1, 2, 2, 2, 2, 2, 2));
    const quiescence = (): SmtVerifier => SmtVerifier.forNet(built.net).mintTransitions(...allMints(built.net))
      .enumerationMaxClasses(0)
      .initialMarking((m) => { m.tokens(P('source'), 1); m.tokens(P('budget'), 1); m.tokens(P('branchA'), 1); })
      .property(deadlockFree())
      .budgetPlaces(P('budget'))
      .timeout(STUB_TIMEOUT);
    const result = await quiescence().verify();
    expect(z3.calls(), result.report).toEqual(['horn']);
    expect(result.report).not.toContain('VER-025');
    const scripts = quiescence().encodeScripts();
    expect(scripts.coloured).toBe(false);
    expect(scripts.witness).toBeNull();
  });

  it('is skipped on a ν-net the ν guard answers unknown: no budget place', async () => {
    // An undeclared mint keeps the net off Route B; without a budget Route A does not apply.
    const built = verificationNets['nuScatterGather']!();
    const z3 = stub('nu-unbudgeted', sat(0, 0, 2, 2, 2, 2, 2, 2));
    const unbudgeted = (): SmtVerifier => SmtVerifier.forNet(built.net)
      .enumerationMaxClasses(0)
      .initialMarking(built.initialMarking)
      .property(placeBound(built.places.get('pending')!, 1))
      .linearBound(false)
      .timeout(STUB_TIMEOUT);
    const result = await unbudgeted().verify();
    expect(z3.calls(), result.report).toEqual(['horn']);
    expect(result.report).not.toContain('VER-025');
    const scripts = unbudgeted().encodeScripts();
    expect(scripts.coloured).toBe(false);
    expect(scripts.witness).toBeNull();
  });
});

describeZ3('SmtVerifier bounded witness phase (VER-025) — end to end', () => {
  const pair = verificationNets['envBoundedPair']!;
  // The shared fixtures (`spec/verification-fixtures/fixtures.json`); `verdict-parity.test.ts`
  // asserts their verdicts, this suite which query gave them.
  const fixtures: readonly { id: string; net: string; property: { type: string; place: string; bound: number } }[] =
    JSON.parse(readFileSync(
      resolve(dirname(fileURLToPath(import.meta.url)), '../../../spec/verification-fixtures/fixtures.json'), 'utf8',
    )).fixtures;

  function fixtureVerifier(id: string): SmtVerifier {
    const fixture = fixtures.find((f) => f.id === id)!;
    expect([fixture.net, fixture.property.type]).toEqual(['envBoundedPair', 'place-bound']);
    const built = pair();
    return SmtVerifier.forNet(built.net)
      .enumerationMaxClasses(0)
      .initialMarking(built.initialMarking)
      .property(placeBound(built.places.get(fixture.property.place)!, fixture.property.bound))
      .environmentPlaces(...built.environmentPlaces)
      .environmentMode(built.environmentMode!)
      .timeout(30_000);
  }

  it('env-bounded-witness-violated: a witness with two injections, found at the default depth', async () => {
    const result = await fixtureVerifier('env-bounded-witness-violated').verify();
    expect(result.verdict.type, result.report).toBe('violated');
    expect(result.report).toContain(status('a run of 4 steps reaches a violation (replayed; depth 8)'));
    expect(result.counterexampleTransitions).toEqual(['inject(e)', 't', 'inject(e)', 't']);
    expect(result.counterexampleConfirmed).toBe(true);
    // Decided by the phase: the fixpoint query never ran.
    expect(result.report).not.toContain('Status: SAT (counterexample found)');
  }, 60_000);

  it('env-bounded-deep-witness-violated: no run within the depth, the fixpoint query answers', async () => {
    const result = await fixtureVerifier('env-bounded-deep-witness-violated').verify();
    const phase = status('no run of at most 8 steps reaches a violation (not a proof)');
    expect(result.report).toContain(`${phase}  Status: SAT (counterexample found)`);
    expect(result.verdict.type, result.report).toBe('violated');
    expect(result.counterexampleTransitions).toHaveLength(10);
    expect(result.report).toContain('Counterexample replay: CONFIRMED');
  }, 60_000);

  it('a deeper witnessDepth finds the run the default depth misses', async () => {
    const result = await fixtureVerifier('env-bounded-deep-witness-violated').witnessDepth(10).verify();
    expect(result.verdict.type, result.report).toBe('violated');
    expect(result.report).toContain(status('a run of 10 steps reaches a violation (replayed; depth 10)'));
    expect(result.report).not.toContain('Status: SAT (counterexample found)');
  }, 60_000);

  it('a shallower witnessDepth misses the 4-step run: one query at that depth, not 8 first', async () => {
    const result = await fixtureVerifier('env-bounded-witness-violated').witnessDepth(3).verify();
    const phase = status('no run of at most 3 steps reaches a violation (not a proof)');
    expect(result.report).toContain(`${phase}  Status: SAT (counterexample found)`);
    expect(result.verdict.type, result.report).toBe('violated');
  }, 60_000);

  it('witnessDepth(0) leaves the violation to the fixpoint query and its replay', async () => {
    const result = await fixtureVerifier('env-bounded-witness-violated').witnessDepth(0).verify();
    expect(result.report).not.toContain('VER-025');
    expect(result.verdict.type, result.report).toBe('violated');
    expect(result.report).toContain('Counterexample replay: CONFIRMED');
  }, 60_000);

  it('reports M0 violating as the empty firing sequence', async () => {
    const built = pair();
    const result = await fixtureVerifier('env-bounded-witness-violated')
      .initialMarking((m) => m.tokens(built.places.get('p1')!, 2))
      // The state-equation phase (VER-018) settles its first candidate, M0 itself, the same way.
      .stateEquationPhase(false)
      .verify();
    expect(result.verdict.type, result.report).toBe('violated');
    expect(result.report).toContain(status('a run of 0 steps reaches a violation (replayed; depth 8)'));
    expect(result.counterexampleTrace).toHaveLength(1);
    expect(result.counterexampleTransitions).toEqual([]);
    expect(result.counterexampleConfirmed).toBe(true);
  }, 60_000);

  it('runs under ignore with environment places: a run without injections is real', async () => {
    const built = pair();
    const result = await SmtVerifier.forNet(built.net)
      .enumerationMaxClasses(0)
      .initialMarking((m) => m.tokens(built.places.get('e')!, 1))
      .property(placeBound(built.places.get('p1')!, 0))
      .environmentPlaces(...built.environmentPlaces)
      .environmentMode(ignore())
      .timeout(30_000)
      .verify();
    expect(result.verdict.type, result.report).toBe('violated');
    expect(result.report).toContain(status('a run of 1 steps reaches a violation (replayed; depth 8)'));
    expect(result.counterexampleTransitions).toEqual(['t']);
  }, 60_000);

  it('on a budgeted ν-net the run is name-blind: violated with the may-be-spurious note', async () => {
    // Environment injection keeps the net off the name-coloured encoding (VER-006).
    const built = verificationNets['nuScatterGather']!();
    const P = (name: string) => built.places.get(name)!;
    const result = await SmtVerifier.forNet(built.net).mintTransitions(...allMints(built.net))
      .enumerationMaxClasses(0)
      .initialMarking((m) => m.tokens(P('budget'), 2))
      .environmentPlaces(environmentPlace('source'))
      .environmentMode(bounded(2))
      .property(unreachable(new Set([P('merged')])))
      .budgetPlaces(P('budget'))
      .timeout(30_000)
      .verify();
    expect(result.verdict.type, result.report).toBe('violated');
    expect(result.report).toContain(status('a run of 3 steps reaches a violation (replayed; depth 8)'));
    expect(result.counterexampleTransitions).toEqual(['inject(source)', 'fork', 'join']);
    expect(result.report).toContain("a 'violated' counterexample may be spurious pending the exact ν-analysis (NU-050)");
    expect(result.report).not.toContain('name-colouring over k colour slots');
  }, 60_000);

  it('leaves a proof to the fixpoint query, with the phase line before it', async () => {
    // No marking violates e <= 2 under bounded(2). The bound query (VER-015) and the
    // state-equation phase (VER-018) are off so that the fixpoint query is the one that proves it.
    const built = pair();
    const result = await SmtVerifier.forNet(built.net)
      .enumerationMaxClasses(0)
      .initialMarking(built.initialMarking)
      .property(placeBound(built.places.get('e')!, 2))
      .environmentPlaces(...built.environmentPlaces)
      .environmentMode(built.environmentMode!)
      .linearBound(false)
      .stateEquationPhase(false)
      .timeout(30_000)
      .verify();
    expect(result.report).toContain(status('no run of at most 8 steps reaches a violation (not a proof)'));
    expect(result.verdict, result.report).toMatchObject({ type: 'proven', method: 'IC3/PDR' });
  }, 60_000);
});
