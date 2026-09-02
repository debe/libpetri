/**
 * TS builders for the cross-language verdict-parity fixtures (C4).
 *
 * The normative builder contract is `netDescription` in
 * `spec/verification-fixtures/fixtures.json` — each named net here must match
 * it exactly, per the cross-lang-dot-parity.sh pattern (shared expectations,
 * per-language builders). Never adjust a builder to make a verdict agree: a
 * disagreement with the shared `expected` is a parity FINDING to report.
 */
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place, environmentPlace } from '../../src/core/place.js';
import type { Place, EnvironmentPlace } from '../../src/core/place.js';
import { one, all, atLeast } from '../../src/core/in.js';
import { outPlace, andPlaces } from '../../src/core/out.js';
import { matchSpec, matchKey } from '../../src/core/match-spec.js';
import { nameId } from '../../src/core/name.js';
import type { MarkingStateBuilder } from '../../src/verification/marking-state.js';
import {
  type EnvironmentAnalysisMode,
  alwaysAvailable,
} from '../../src/verification/analysis/environment-analysis-mode.js';
import { bindProducers } from './producing-actions.js';

/** One built parity fixture net, ready for SmtVerifier. */
export interface VerificationFixtureNet {
  /** The net, with producing actions bound (CORE-043). */
  readonly net: PetriNet;
  readonly initialMarking: (m: MarkingStateBuilder) => void;
  /** Fixture place name -> Place, for resolving fixture property specs. */
  readonly places: ReadonlyMap<string, Place<any>>;
  readonly environmentPlaces: readonly EnvironmentPlace<any>[];
  readonly environmentMode: EnvironmentAnalysisMode | null;
}

function fixture(
  net: PetriNet,
  initialMarking: (m: MarkingStateBuilder) => void,
  places: readonly Place<any>[],
  environmentPlaces: readonly EnvironmentPlace<any>[] = [],
  environmentMode: EnvironmentAnalysisMode | null = null,
): VerificationFixtureNet {
  return {
    net: bindProducers(net),
    initialMarking,
    places: new Map(places.map(p => [p.name, p])),
    environmentPlaces,
    environmentMode,
  };
}

/** p0(1),p1,p2; t01: one(p0)->p1; t12: one(p1)->p2; t20: one(p2)->p0. */
function circularChain(): VerificationFixtureNet {
  const p0 = place('p0');
  const p1 = place('p1');
  const p2 = place('p2');
  const t01 = Transition.builder('t01').inputs(one(p0)).outputs(outPlace(p1)).build();
  const t12 = Transition.builder('t12').inputs(one(p1)).outputs(outPlace(p2)).build();
  const t20 = Transition.builder('t20').inputs(one(p2)).outputs(outPlace(p0)).build();
  const net = PetriNet.builder('circularChain').transitions(t01, t12, t20).build();
  return fixture(net, m => m.tokens(p0, 1), [p0, p1, p2]);
}

/** p0(1),p1,p2; t01: one(p0)->p1; t12: one(p1)->p2. p2 is a normal place (no declared sink). */
function deadEndChain(): VerificationFixtureNet {
  const p0 = place('p0');
  const p1 = place('p1');
  const p2 = place('p2');
  const t01 = Transition.builder('t01').inputs(one(p0)).outputs(outPlace(p1)).build();
  const t12 = Transition.builder('t12').inputs(one(p1)).outputs(outPlace(p2)).build();
  const net = PetriNet.builder('deadEndChain').transitions(t01, t12).build();
  return fixture(net, m => m.tokens(p0, 1), [p0, p1, p2]);
}

/** Binary-semaphore mutex: enterN consumes idle_N + lock, exitN returns both. */
function mutexLocked(): VerificationFixtureNet {
  const idle1 = place('idle1');
  const idle2 = place('idle2');
  const lock = place('lock');
  const crit1 = place('crit1');
  const crit2 = place('crit2');
  const enter1 = Transition.builder('enter1').inputs(one(idle1), one(lock)).outputs(outPlace(crit1)).build();
  const exit1 = Transition.builder('exit1').inputs(one(crit1)).outputs(andPlaces(idle1, lock)).build();
  const enter2 = Transition.builder('enter2').inputs(one(idle2), one(lock)).outputs(outPlace(crit2)).build();
  const exit2 = Transition.builder('exit2').inputs(one(crit2)).outputs(andPlaces(idle2, lock)).build();
  const net = PetriNet.builder('mutexLocked').transitions(enter1, exit1, enter2, exit2).build();
  return fixture(
    net,
    m => m.tokens(idle1, 1).tokens(idle2, 1).tokens(lock, 1),
    [idle1, idle2, lock, crit1, crit2],
  );
}

/** Same as mutexLocked but the lock place is omitted entirely. */
function mutexUnlocked(): VerificationFixtureNet {
  const idle1 = place('idle1');
  const idle2 = place('idle2');
  const crit1 = place('crit1');
  const crit2 = place('crit2');
  const enter1 = Transition.builder('enter1').inputs(one(idle1)).outputs(outPlace(crit1)).build();
  const exit1 = Transition.builder('exit1').inputs(one(crit1)).outputs(outPlace(idle1)).build();
  const enter2 = Transition.builder('enter2').inputs(one(idle2)).outputs(outPlace(crit2)).build();
  const exit2 = Transition.builder('exit2').inputs(one(crit2)).outputs(outPlace(idle2)).build();
  const net = PetriNet.builder('mutexUnlocked').transitions(enter1, exit1, enter2, exit2).build();
  return fixture(net, m => m.tokens(idle1, 1).tokens(idle2, 1), [idle1, idle2, crit1, crit2]);
}

/** p0(3),p1; t: one(p0)->p1. Conservation p0+p1=3 (P-invariant strengthening). */
function conservedPair(): VerificationFixtureNet {
  const p0 = place('p0');
  const p1 = place('p1');
  const t = Transition.builder('t').inputs(one(p0)).outputs(outPlace(p1)).build();
  const net = PetriNet.builder('conservedPair').transitions(t).build();
  return fixture(net, m => m.tokens(p0, 3), [p0, p1]);
}

/** Environment place e (always-available injection, VER-006); t: one(e)->p1. */
function envSingleFeed(): VerificationFixtureNet {
  const e = environmentPlace('e');
  const p1 = place('p1');
  const t = Transition.builder('t').inputs(one(e.place)).outputs(outPlace(p1)).build();
  const net = PetriNet.builder('envSingleFeed').transitions(t).build();
  return fixture(net, () => {}, [e.place, p1], [e], alwaysAvailable());
}

/** p0(1),blocker(1),p1; t: one(p0), inhibitor(blocker) -> p1. Blocker never drains. */
function inhibitorFrozen(): VerificationFixtureNet {
  const p0 = place('p0');
  const blocker = place('blocker');
  const p1 = place('p1');
  const t = Transition.builder('t').inputs(one(p0)).inhibitor(blocker).outputs(outPlace(p1)).build();
  const net = PetriNet.builder('inhibitorFrozen').transitions(t).build();
  return fixture(net, m => m.tokens(p0, 1).tokens(blocker, 1), [p0, blocker, p1]);
}

/** The Strengthening.lean H1 witness: t: all(p0)->p1 with p0(2). */
function h1ConsumeAll(): VerificationFixtureNet {
  const p0 = place('p0');
  const p1 = place('p1');
  const t = Transition.builder('t').inputs(all(p0)).outputs(outPlace(p1)).build();
  const net = PetriNet.builder('h1ConsumeAll').transitions(t).build();
  return fixture(net, m => m.tokens(p0, 2), [p0, p1]);
}

/** p0(3),p1; t: atLeast(2)(p0)->p1 producing ONE token — fires at most once from M0. */
function atLeastDrain(): VerificationFixtureNet {
  const p0 = place('p0');
  const p1 = place('p1');
  const t = Transition.builder('t').inputs(atLeast(2, p0)).outputs(outPlace(p1)).build();
  const net = PetriNet.builder('atLeastDrain').transitions(t).build();
  return fixture(net, m => m.tokens(p0, 3), [p0, p1]);
}

/**
 * p0(1),done,stuck; t: one(p0)->AND(done, stuck). The only quiescent marking
 * holds a token in the declared sink `done` AND in the non-sink `stuck`.
 */
function sinkPartialTerminal(): VerificationFixtureNet {
  const p0 = place('p0');
  const done = place('done');
  const stuck = place('stuck');
  const t = Transition.builder('t').inputs(one(p0)).outputs(andPlaces(done, stuck)).build();
  const net = PetriNet.builder('sinkPartialTerminal').transitions(t).build();
  return fixture(net, m => m.tokens(p0, 1), [p0, done, stuck]);
}

/**
 * p0(1) and done (empty); t: one(p0) with NO output spec — a sink transition
 * (CORE-042). `done` touches no arc, so it is declared explicitly on the
 * builder; after t fires the net holds no tokens anywhere.
 */
function sinkDrainedTerminal(): VerificationFixtureNet {
  const p0 = place('p0');
  const done = place('done');
  const t = Transition.builder('t').inputs(one(p0)).build();
  const net = PetriNet.builder('sinkDrainedTerminal').place(done).transitions(t).build();
  return fixture(net, m => m.tokens(p0, 1), [p0, done]);
}

// === Route B fixtures (`"route": "B"` in fixtures.json) ===
//
// ν nets in the BASE mint->matched-join fragment, so the name-aware
// state-class-graph verifier (NU-050 Route B) decides them and the SMT / Route A
// encoders never see them. They pin the two markings on which Route B's deadlock
// predicate — quiescent AND NOT(every marked place is a declared sink) —
// disagrees with VER-002's, which Route A implements verbatim. The disagreement
// is recorded deliberately; see each fixture's netDescription.

/**
 * ν net: fork co-mints ONE fresh name into branchA+branchB; join correlates them
 * by name equality into done+stuck. The only quiescent marking is
 * {done:1, stuck:1} — a token in the declared sink AND one in the non-sink
 * `stuck`. Route B: violated. Route A on the same shape (see
 * `sinkPartialTerminal`): proven. Non-vacuity guard: a failed ν correlation would
 * also quiesce (at {branchA:1, branchB:1}, neither a sink) and also read violated
 * here — `nuDrainedTerminal` below, built on the identical correlation, is what
 * turns violated if that ever happens.
 */
function nuMixedTerminal(): VerificationFixtureNet {
  const source = place<string>('source');
  const branchA = place<string>('branchA');
  const branchB = place<string>('branchB');
  const done = place<string>('done');
  const stuck = place<string>('stuck');
  const fork = Transition.builder('fork')
    .inputs(one(source))
    .outputs(andPlaces(branchA, branchB))
    .build();
  const join = Transition.builder('join')
    .inputs(one(branchA), one(branchB))
    .match(matchSpec(
      matchKey(branchA, (v: string) => nameId(v)),
      matchKey(branchB, (v: string) => nameId(v)),
    ))
    .outputs(andPlaces(done, stuck))
    .build();
  const net = PetriNet.builder('nuMixedTerminal').transitions(fork, join).build();
  return fixture(net, m => m.tokens(source, 1), [source, branchA, branchB, done, stuck]);
}

/**
 * Same mint->join shape, but `join` has NO output spec (a sink transition,
 * CORE-042 / CORE-043 AC4), so the only quiescent marking is the EMPTY one. The
 * declared sink `done` touches no arc and is therefore declared explicitly on the
 * builder, so the declaration resolves against the flattened net (the same
 * requirement its Route A sibling carries). Route B: proven — vacuously as to the
 * predicate (nothing is marked outside the sinks) but NOT as to the net: the empty
 * marking is reachable only because the ν join really correlates the co-minted
 * pair and drains it; a correlation failure would quiesce at
 * {branchA:1, branchB:1} and turn this fixture violated. Route A on the same
 * shape (see `sinkDrainedTerminal`): violated.
 */
function nuDrainedTerminal(): VerificationFixtureNet {
  const source = place<string>('source');
  const branchA = place<string>('branchA');
  const branchB = place<string>('branchB');
  const done = place<string>('done');
  const fork = Transition.builder('fork')
    .inputs(one(source))
    .outputs(andPlaces(branchA, branchB))
    .build();
  const join = Transition.builder('join')
    .inputs(one(branchA), one(branchB))
    .match(matchSpec(
      matchKey(branchA, (v: string) => nameId(v)),
      matchKey(branchB, (v: string) => nameId(v)),
    ))
    .build();
  const net = PetriNet.builder('nuDrainedTerminal').place(done).transitions(fork, join).build();
  return fixture(net, m => m.tokens(source, 1), [source, branchA, branchB, done]);
}

/**
 * ν scatter-gather on Route A's exact name-coloured encoding (NU-053): a declared
 * budget puts the reachability-safety query on the coloured encoder. `fork`
 * consumes source+budget and co-mints one fresh name into branchA+branchB (plus a
 * pending token); `join` correlates the branches and returns the budget token.
 * Conservation budget + pending = 2 bounds budget by 2.
 */
function nuScatterGather(): VerificationFixtureNet {
  const source = place<string>('source');
  const budget = place<string>('budget');
  const pending = place<string>('pending');
  const branchA = place<string>('branchA');
  const branchB = place<string>('branchB');
  const merged = place<string>('merged');
  const fork = Transition.builder('fork')
    .inputs(one(source), one(budget))
    .outputs(andPlaces(branchA, branchB, pending))
    .build();
  const join = Transition.builder('join')
    .inputs(one(branchA), one(branchB), one(pending))
    .match(matchSpec(
      matchKey(branchA, (v: string) => nameId(v)),
      matchKey(branchB, (v: string) => nameId(v)),
    ))
    .outputs(andPlaces(merged, budget))
    .build();
  const net = PetriNet.builder('nuScatterGather').transitions(fork, join).build();
  return fixture(
    net, m => { m.tokens(source, 3); m.tokens(budget, 2); },
    [source, budget, pending, branchA, branchB, merged],
  );
}

/** Registry: fixture `net` name -> builder. */
export const verificationNets: Record<string, () => VerificationFixtureNet> = {
  circularChain,
  deadEndChain,
  mutexLocked,
  mutexUnlocked,
  conservedPair,
  envSingleFeed,
  inhibitorFrozen,
  h1ConsumeAll,
  atLeastDrain,
  sinkPartialTerminal,
  sinkDrainedTerminal,
  nuMixedTerminal,
  nuDrainedTerminal,
  nuScatterGather,
};
