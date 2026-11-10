/**
 * @module bounded-run
 *
 * The firing-bound phase (VER-019). When every firing strictly lowers a weighted
 * token count, every run is short, and a bounded model check to that length decides
 * the property exactly — consume-all and reset clearing, inhibitor and read guards
 * included. A net whose runs are not bounded this way is reported as such and left
 * to the fixpoint query: a bound is both the runtime cap and the width of the claim.
 *
 * **Ranking.** Weights `r ≥ 0` with `r·C_t ≤ −1` for every flat transition `t` that
 * can fire. A clearing arc removes at least its weight, so the column `C_t = post −
 * pre` bounds its effect from above. `r·M` then drops by at least one per firing and
 * never goes below zero, so a run from `M0` has at most `K = r·M0` firings. One
 * `QF_LIA` query minimising `r·M0`, re-checked in exact integer arithmetic
 * ({@link checkRankingExact}). When none exists, Farkas gives `y ≥ 0, y ≠ 0` with
 * `C·y ≥ 0`: firing counts the marking equation lets repeat forever
 * ({@link encodeRepeatableVectorQuery}), whose support the report names.
 *
 * **Bounded model check.** One `QF_LIA` script unrolls `d` steps of the exact step
 * relation from `M0` — step `i` fires the transition its selector `s_i` names, or
 * idles, and once idle stays idle — and asks for a violation at the last marking
 * ({@link encodeBoundedRun}). Idling makes "at most `d` firings" one query. `sat` is
 * a run, decoded and replayed firing by firing before it is believed
 * ({@link replayRun}); `unsat` at `d = K` covers every run of the net.
 *
 * **Bounded witness phase (VER-025).** The same script at one fixed depth, with no
 * ranking: on a net with injected environment places ([VER-006]) a step may also be an
 * injection, which takes a selector value after the transitions'. `sat` is a run, replayed
 * and trimmed ({@link runWitnessPhase}); `unsat` is no proof, since the net may run longer.
 */
import type { FlatNet } from '../encoding/flat-net.js';
import type { FlatTransition } from '../encoding/flat-transition.js';
import type { MarkingState } from '../marking-state.js';
import type { SmtProperty } from '../smt-property.js';
import type { ConditionalSinks } from '../rest-set.js';
import type { Place } from '../../core/place.js';
import { rethrowIfProgrammingError } from '../programming-error.js';
import {
  conjoin, encodePropertyViolation, intTerm, resolveEnvInjection, sumTerms,
} from './smt-encoder.js';
import { classifyFirstLine, extractDefineFuns } from './smt-text.js';
import {
  enabledA, environmentCaps, fireA, injectA, stepName, vectorize, violationPredicate, type AbstractState,
} from './abstract-replayer.js';
import { isNameAlignment, routeBOnlyReason } from '../name-alignment.js';

/** A ranking and the firing bound it gives: `weights·C_t ≤ −1` on every transition that can fire. */
export interface FiringBound {
  /** `r`, one entry per flat place, all non-negative. */
  readonly weights: readonly bigint[];
  /** `K = r·M0`: no run from `M0` has more firings. */
  readonly bound: bigint;
}

/** Whether `ft` can ever fire: it does not inhibit a place it needs. */
function canFire(ft: FlatTransition): boolean {
  for (const p of ft.inhibitorPlaces) {
    if (ft.preVector[p]! > 0 || ft.readPlaces.includes(p)) return false;
  }
  return true;
}

/** The `QF_LIA` script asking for the ranking with the least `r·M0`. */
export function encodeRankingQuery(flatNet: FlatNet, initial: readonly number[]): string {
  const P = flatNet.places.length;
  const lines = [
    '; Firing bound (VER-019): weights r >= 0 that every firing lowers by at least one',
    '; (r.C_t <= -1, a clearing arc counted at its weight); every run from M0 then has',
    '; at most r.M0 firings. sat with the least r.M0.',
    '(set-logic QF_LIA)',
  ];
  for (let p = 0; p < P; p++) lines.push(`(declare-const r${p} Int)`);
  for (let p = 0; p < P; p++) lines.push(`(assert (>= r${p} 0))`);
  for (const ft of flatNet.transitions) {
    if (!canFire(ft)) continue;
    const terms: string[] = [];
    for (let p = 0; p < P; p++) {
      const c = ft.postVector[p]! - ft.preVector[p]!;
      if (c !== 0) terms.push(intTerm(c, `r${p}`));
    }
    lines.push(`(assert (<= ${sumTerms(terms)} (- 1)))`);
  }
  const objective: string[] = [];
  for (let p = 0; p < P; p++) if (initial[p]! !== 0) objective.push(intTerm(initial[p]!, `r${p}`));
  lines.push(`(minimize ${sumTerms(objective)})`);
  lines.push('(check-sat)');
  lines.push('(get-model)');
  return lines.join('\n');
}

/** The ranking in a `sat` reply's model; `null` when it defines no weight. */
export function decodeRanking(stdout: string, placeCount: number): bigint[] | null {
  const weights = new Array<bigint>(placeCount).fill(0n);
  let seen = false;
  for (const [name, value] of intDefinitions(stdout)) {
    const m = /^r(\d+)$/.exec(name);
    if (m == null || Number(m[1]) >= placeCount) continue;
    weights[Number(m[1])] = value;
    seen = true;
  }
  return seen ? weights : null;
}

/**
 * Re-checks a ranking in exact integer arithmetic: `r ≥ 0` and `r·C_t ≤ −1` on every
 * flat transition that can fire. Returns the firing bound, or `null` when a check fails.
 */
export function checkRankingExact(
  flatNet: FlatNet,
  initial: readonly number[],
  weights: readonly bigint[],
): FiringBound | null {
  const P = flatNet.places.length;
  if (weights.length !== P || weights.some((w) => w < 0n)) return null;
  for (const ft of flatNet.transitions) {
    if (!canFire(ft)) continue;
    let delta = 0n;
    for (let p = 0; p < P; p++) delta += weights[p]! * BigInt(ft.postVector[p]! - ft.preVector[p]!);
    if (delta > -1n) return null;
  }
  let bound = 0n;
  for (let p = 0; p < P; p++) bound += weights[p]! * BigInt(initial[p]!);
  return { weights, bound };
}

/**
 * The `QF_LIA` script asking for the Farkas alternative of a ranking: firing counts
 * `y ≥ 0`, not all zero, with `C·y ≥ 0` on every place — counts the marking equation
 * lets repeat forever. The fewest firings.
 */
export function encodeRepeatableVectorQuery(flatNet: FlatNet): string {
  const P = flatNet.places.length;
  const live = flatNet.transitions.map((ft, t) => (canFire(ft) ? t : -1)).filter((t) => t >= 0);
  const lines = [
    '; No firing bound (VER-019): firing counts y >= 0, not all zero, with C.y >= 0 on',
    '; every place, so the marking equation lets them repeat forever.',
    '(set-logic QF_LIA)',
  ];
  for (const t of live) lines.push(`(declare-const y${t} Int)`);
  for (const t of live) lines.push(`(assert (>= y${t} 0))`);
  lines.push(`(assert (>= ${sumTerms(live.map((t) => `y${t}`))} 1))`);
  for (let p = 0; p < P; p++) {
    const terms: string[] = [];
    for (const t of live) {
      const ft = flatNet.transitions[t]!;
      const c = ft.postVector[p]! - ft.preVector[p]!;
      if (c !== 0) terms.push(intTerm(c, `y${t}`));
    }
    if (terms.length > 0) lines.push(`(assert (>= ${sumTerms(terms)} 0))`);
  }
  lines.push(`(minimize ${sumTerms(live.map((t) => `y${t}`))})`);
  lines.push('(check-sat)');
  lines.push('(get-model)');
  return lines.join('\n');
}

/** The transitions a repeatable vector fires, in net order; `null` when the model defines none. */
export function decodeRepeatableVector(stdout: string, transitionCount: number): number[] | null {
  const support: number[] = [];
  for (const [name, value] of intDefinitions(stdout)) {
    const m = /^y(\d+)$/.exec(name);
    if (m != null && Number(m[1]) < transitionCount && value > 0n) support.push(Number(m[1]));
  }
  support.sort((a, b) => a - b);
  return support.length === 0 ? null : support;
}

/** Outcome of {@link findFiringBound}. */
export type RankingSearch =
  | { readonly kind: 'bound'; readonly bound: FiringBound }
  /** No ranking; `repeatable` is a repeatable firing vector's support, `null` when none was named. */
  | { readonly kind: 'unbounded'; readonly repeatable: readonly number[] | null }
  /** The ranking query answered `unknown`. */
  | { readonly kind: 'unknown' }
  /** The ranking the model gave failed {@link checkRankingExact}. */
  | { readonly kind: 'rejected' }
  /** `ask` failed with `reason`. */
  | { readonly kind: 'failed'; readonly reason: string };

/**
 * The ranking query, re-checked exactly, and when it is `unsat` the repeatable-vector query.
 * Shared by the VER-019 phase and the open-net termination check of [VER-022]. `ask` resolves
 * with a reply that carries a verdict line, or with the `Error` that stopped it.
 */
export async function findFiringBound(
  flatNet: FlatNet,
  initial: readonly number[],
  ask: (script: string) => Promise<string | Error>,
): Promise<RankingSearch> {
  const ranking = await ask(encodeRankingQuery(flatNet, initial));
  if (ranking instanceof Error) return { kind: 'failed', reason: ranking.message };
  switch (classifyFirstLine(ranking)) {
    case 'sat': {
      const weights = decodeRanking(ranking, flatNet.places.length);
      const bound = weights == null ? null : checkRankingExact(flatNet, initial, weights);
      return bound == null ? { kind: 'rejected' } : { kind: 'bound', bound };
    }
    case 'unsat': {
      const vector = await ask(encodeRepeatableVectorQuery(flatNet));
      const repeatable = vector instanceof Error || classifyFirstLine(vector) !== 'sat'
        ? null
        : decodeRepeatableVector(vector, flatNet.transitions.length);
      return { kind: 'unbounded', repeatable };
    }
    default:
      return { kind: 'unknown' };
  }
}

/**
 * The bounded model check: `depth` steps from `initial`, selector `s_i ∈ [0, T + J]` per
 * step, the exact guard and update of the selected transition, the environment post-caps,
 * and the property's violation at the last marking. `J` counts the injected environment
 * places ({@link resolveEnvInjection}): selector `T + j` injects one token into the `j`-th,
 * under its bound when it has one, and `T + J` idles. Without injection (`J = 0`) the
 * script is the one of [VER-019].
 */
export function encodeBoundedRun(
  flatNet: FlatNet,
  initial: readonly number[],
  property: SmtProperty,
  sinkPlaces: ReadonlySet<Place<any>>,
  conditionalSinks: readonly ConditionalSinks[],
  depth: number,
): string {
  const P = flatNet.places.length;
  const T = flatNet.transitions.length;
  const m = (i: number, p: number): string => (i === 0 ? String(initial[p]!) : `m${i}_${p}`);
  // The encoder's `envBounds(M')` conjunct, in place-index order as there. Vacuous for the
  // firing-bound phase, which refuses a net with declared injection (only the `bounded` mode
  // fills `environmentBounds`, and it injects); live for the witness phase ([VER-025]),
  // which unrolls the injection steps below.
  const caps = environmentCaps(flatNet).sort((a, b) => a[0] - b[0]);
  // Injection steps ([VER-006]) take the selector values after the transitions', in
  // place-index order, exactly the rules the HORN encoding adds; idling moves past them.
  const injections = resolveEnvInjection(flatNet);
  const idle = T + injections.length;
  // Per place, the selectors that change it, last first: the `ite` chain nests inward from the
  // last. An injection into the place comes after its transitions, so it is the innermost.
  const nesting: number[][] = Array.from({ length: P }, () => []);
  injections.forEach((inj, j) => nesting[inj.pid]!.push(T + j));
  for (let t = T - 1; t >= 0; t--) {
    const ft = flatNet.transitions[t]!;
    for (let p = 0; p < P; p++) {
      if (clears(ft, p) || ft.postVector[p]! !== ft.preVector[p]!) nesting[p]!.push(t);
    }
  }
  const lines = [
    `; Bounded run (VER-019): ${depth} steps of the exact step relation from M0, idle`,
    '; only at the end; sat = a run to a violating marking.',
    '(set-logic QF_LIA)',
  ];
  for (let i = 0; i < depth; i++) lines.push(`(declare-const s${i} Int)`);
  for (let i = 1; i <= depth; i++) for (let p = 0; p < P; p++) lines.push(`(declare-const ${m(i, p)} Int)`);
  for (let i = 0; i < depth; i++) {
    lines.push(`(assert (and (>= s${i} 0) (<= s${i} ${idle})))`);
    if (i + 1 < depth) lines.push(`(assert (=> (= s${i} ${idle}) (= s${i + 1} ${idle})))`);
    flatNet.transitions.forEach((ft, t) => {
      const guard = guardConditions(ft, (p) => m(i, p));
      lines.push(`(assert (=> (= s${i} ${t}) ${conjoin(guard)}))`);
    });
    injections.forEach((inj, j) => {
      if (inj.bound != null) lines.push(`(assert (=> (= s${i} ${T + j}) (< ${m(i, inj.pid)} ${inj.bound})))`);
    });
    for (let p = 0; p < P; p++) {
      let value = m(i, p);
      for (const t of nesting[p]!) {
        let next: string;
        if (t >= T) {
          next = shifted(m(i, p), 1);
        } else {
          const ft = flatNet.transitions[t]!;
          next = clears(ft, p) ? String(ft.postVector[p]!) : shifted(m(i, p), ft.postVector[p]! - ft.preVector[p]!);
        }
        value = `(ite (= s${i} ${t}) ${next} ${value})`;
      }
      lines.push(`(assert (= ${m(i + 1, p)} ${value}))`);
    }
    for (const [p, cap] of caps) lines.push(`(assert (<= ${m(i + 1, p)} ${cap}))`);
  }
  const last: string[] = [];
  for (let p = 0; p < P; p++) last.push(m(depth, p));
  lines.push(`(assert ${encodePropertyViolation(flatNet, property, last, sinkPlaces, injections, conditionalSinks)})`);
  lines.push('(check-sat)');
  lines.push('(get-model)');
  return lines.join('\n');
}

/**
 * The steps a `sat` bounded run takes, in order, up to the first idle step; `null` without
 * selectors. `stepCount` is the idle selector: `T` for the firing-bound phase, `T + J` for a
 * run with injection steps, where a selector in `[T, T + J)` is an injection.
 */
export function decodeBoundedRun(stdout: string, stepCount: number, depth: number): number[] | null {
  const selectors = new Array<number>(depth).fill(stepCount);
  let seen = depth === 0;
  for (const [name, value] of intDefinitions(stdout)) {
    const m = /^s(\d+)$/.exec(name);
    if (m == null || Number(m[1]) >= depth) continue;
    selectors[Number(m[1])] = Number(value);
    seen = true;
  }
  if (!seen) return null;
  const firings: number[] = [];
  for (const s of selectors) {
    if (s < 0 || s >= stepCount) break;
    firings.push(s);
  }
  return firings;
}

/**
 * Replays a run from `initial` under the exact abstract semantics and returns its markings
 * and step names when every step is enabled and the last marking violates the property;
 * `null` otherwise. An index below `T` fires that transition, which must also respect the
 * environment post-caps. `T + j` is the `j`-th injection of {@link resolveEnvInjection}, as
 * `successors` takes it: under its bound, one more token, no post-cap (the HORN injection
 * rule carries none), named `inject(<place>)`.
 */
export function replayRun(
  flatNet: FlatNet,
  initial: AbstractState,
  firings: readonly number[],
  isBad: (state: AbstractState) => boolean,
): { states: AbstractState[]; steps: string[] } | null {
  const step = runStepper(flatNet);
  const states: AbstractState[] = [initial];
  const steps: string[] = [];
  let state = initial;
  for (const t of firings) {
    const next = step(state, t);
    if (next == null) return null;
    state = next.state;
    states.push(state);
    steps.push(next.name);
  }
  return isBad(state) ? { states, steps } : null;
}

/**
 * The shortest prefix of `run` that replays to a violating marking, as {@link replayRun}
 * returns a run; `null` when no prefix does. The violation is tested before each step and
 * after the last, so the empty prefix counts (it is `initial`) and the steps after the first
 * violating marking are never taken: they need not be enabled.
 */
function violatingPrefix(
  flatNet: FlatNet,
  initial: AbstractState,
  run: readonly number[],
  isBad: (state: AbstractState) => boolean,
): { states: AbstractState[]; steps: string[] } | null {
  const step = runStepper(flatNet);
  const states: AbstractState[] = [initial];
  const steps: string[] = [];
  let state = initial;
  for (let i = 0; ; i++) {
    if (isBad(state)) return { states, steps };
    if (i === run.length) return null;
    const next = step(state, run[i]!);
    if (next == null) return null;
    state = next.state;
    states.push(state);
    steps.push(next.name);
  }
}

/**
 * One step of a run under the exact abstract semantics, the one {@link replayRun} documents:
 * the marking it leads to and its name, or `null` when the step is not enabled (a firing
 * past a post-cap included).
 */
function runStepper(
  flatNet: FlatNet,
): (state: AbstractState, t: number) => { state: AbstractState; name: string } | null {
  const caps = environmentCaps(flatNet);
  const injections = resolveEnvInjection(flatNet);
  const T = flatNet.transitions.length;
  return (state, t) => {
    if (t >= T) {
      const inj = injections[t - T]!;
      if (inj.bound != null && state[inj.pid]! >= inj.bound) return null;
      return {
        state: injectA(state, inj.pid),
        name: stepName({ kind: 'inject', place: flatNet.places[inj.pid]!.name }),
      };
    }
    const ft = flatNet.transitions[t]!;
    if (!enabledA(state, ft)) return null;
    const next = fireA(state, ft);
    if (caps.some(([idx, cap]) => next[idx]! > cap)) return null;
    return { state: next, name: ft.name };
  };
}

/** `2*budget + q + s` — the ranking as the report prints it. */
export function formatRanking(flatNet: FlatNet, bound: FiringBound): string {
  const parts: string[] = [];
  bound.weights.forEach((w, p) => {
    if (w !== 0n) parts.push(w === 1n ? flatNet.places[p]!.name : `${w}*${flatNet.places[p]!.name}`);
  });
  return parts.length === 0 ? '0' : parts.join(' + ');
}

/** One depth of the bounded model check and what it answered. */
export interface DepthStep {
  readonly depth: number;
  readonly answer: 'sat' | 'unsat';
}

/** Outcome of {@link runFiringBoundPhase}. */
export type FiringBoundOutcome =
  | { readonly kind: 'proven'; readonly bound: FiringBound; readonly depths: readonly DepthStep[] }
  | {
      readonly kind: 'violated';
      readonly bound: FiringBound;
      readonly depths: readonly DepthStep[];
      readonly states: readonly AbstractState[];
      readonly steps: readonly string[];
    }
  /** No ranking exists; `repeatable` names the flat transitions a repeatable firing vector uses. */
  | { readonly kind: 'unbounded'; readonly repeatable: readonly number[] | null }
  | {
      readonly kind: 'inconclusive';
      readonly reason: string;
      readonly bound: FiringBound | null;
      readonly depths: readonly DepthStep[];
    };

/** Runs one script within `timeoutMs`; rejects with the reason when the reply carries no verdict. */
export type FiringBoundSolver = (script: string, phase: 'ranking' | 'bmc' | 'witness', timeoutMs: number) => Promise<string>;

/**
 * Runs the phase: {@link findFiringBound}, then the bounded model check at depths 8, 16,
 * 32, … up to the bound. A violating run is replayed before it is reported; `unsat` at the
 * bound is a proof. Builds its violation predicate from the same arguments as
 * `runStateEquationPhase`, so the two phases cannot disagree on it.
 */
export async function runFiringBoundPhase(
  flatNet: FlatNet,
  initialMarking: MarkingState,
  property: SmtProperty,
  sinkPlaces: ReadonlySet<Place<any>>,
  conditionalSinks: readonly ConditionalSinks[],
  run: FiringBoundSolver,
  options: { readonly budgetMs?: number; readonly maxDepth?: number } = {},
): Promise<FiringBoundOutcome> {
  const budgetMs = options.budgetMs ?? 60_000;
  const maxDepth = options.maxDepth ?? 512;
  const deadline = performance.now() + budgetMs;
  // NU-055: a run of counts carries no names.
  if (isNameAlignment(property)) {
    return { kind: 'inconclusive', reason: routeBOnlyReason(property), bound: null, depths: [] };
  }
  const initial: AbstractState = vectorize(initialMarking, flatNet);
  const isBad = violationPredicate(flatNet, property, sinkPlaces, conditionalSinks);
  const depths: DepthStep[] = [];
  if (flatNet.environmentInjection.size > 0) {
    return { kind: 'inconclusive', reason: 'environment injection has no firing bound', bound: null, depths };
  }
  const ask = async (script: string, phase: 'ranking' | 'bmc'): Promise<string | Error> => {
    const left = Math.floor(deadline - performance.now());
    if (left <= 0) return new Error(`time budget of ${budgetMs} ms exhausted`);
    try {
      return await run(script, phase, left);
    } catch (e: any) {
      rethrowIfProgrammingError(e);
      return new Error(String(e?.message ?? e));
    }
  };

  const ranking = await findFiringBound(flatNet, initial, (script) => ask(script, 'ranking'));
  switch (ranking.kind) {
    case 'failed':
      return { kind: 'inconclusive', reason: ranking.reason, bound: null, depths };
    case 'unbounded':
      return { kind: 'unbounded', repeatable: ranking.repeatable };
    case 'unknown':
      return { kind: 'inconclusive', reason: 'the ranking query answered unknown', bound: null, depths };
    case 'rejected':
      return { kind: 'inconclusive', reason: 'the ranking failed the exact re-check', bound: null, depths };
  }
  const { bound } = ranking;
  if (bound.bound > BigInt(Number.MAX_SAFE_INTEGER)) {
    return { kind: 'inconclusive', reason: `firing bound ${bound.bound} is too large`, bound, depths };
  }
  const K = Number(bound.bound);
  let depth = Math.min(8, K, maxDepth);
  for (;;) {
    const reply = await ask(encodeBoundedRun(flatNet, initial, property, sinkPlaces, conditionalSinks, depth), 'bmc');
    if (reply instanceof Error) return { kind: 'inconclusive', reason: reply.message, bound, depths };
    const answer = classifyFirstLine(reply);
    // Record every answered depth, `sat` or `unsat`.
    if (answer !== 'sat' && answer !== 'unsat') {
      return { kind: 'inconclusive', reason: `the bounded run at depth ${depth} answered unknown`, bound, depths };
    }
    depths.push({ depth, answer });
    if (answer === 'sat') {
      const firings = decodeBoundedRun(reply, flatNet.transitions.length, depth);
      const replayed = firings == null ? null : replayRun(flatNet, initial, firings, isBad);
      if (replayed == null) {
        return { kind: 'inconclusive', reason: 'the bounded run did not replay under the exact semantics', bound, depths };
      }
      return { kind: 'violated', bound, depths, ...replayed };
    }
    if (depth >= K) return { kind: 'proven', bound, depths };
    if (depth >= maxDepth) {
      return { kind: 'inconclusive', reason: `the firing bound ${K} exceeds the depth limit ${maxDepth}`, bound, depths };
    }
    depth = Math.min(2 * depth, K, maxDepth);
  }
}

/** Outcome of {@link runWitnessPhase}. Never a proof: the depth is a search limit, not a bound. */
export type WitnessOutcome =
  /**
   * A run reaches a violation: replayed, then trimmed. It ends at the first violating marking
   * it reaches and no single step of it can be dropped.
   */
  | { readonly kind: 'violated'; readonly states: readonly AbstractState[]; readonly steps: readonly string[] }
  /** The bounded run answered `unsat`: no run of at most `depth` steps reaches a violation. */
  | { readonly kind: 'none' }
  | { readonly kind: 'inconclusive'; readonly reason: string };

/**
 * Runs the bounded witness phase ([VER-025]): one bounded run at `depth`, injection steps
 * included, within `budgetMs` (counted from before the script is encoded). A `sat` run is
 * replayed before it is believed and trimmed ({@link trimRun}) before it is reported. `unsat`
 * is no proof: the net may run longer.
 *
 * The trim is cubic in the run's length and calls `poll` before each candidate ([VER-013]): the
 * verifier passes a deadline poll, which throws once the run must stop, and that error leaves
 * this function as it is. A direct caller passes none.
 */
export async function runWitnessPhase(
  flatNet: FlatNet,
  initialMarking: MarkingState,
  property: SmtProperty,
  sinkPlaces: ReadonlySet<Place<any>>,
  conditionalSinks: readonly ConditionalSinks[],
  run: FiringBoundSolver,
  options: { readonly depth: number; readonly budgetMs: number; readonly poll?: () => void },
): Promise<WitnessOutcome> {
  const { depth, budgetMs } = options;
  const deadline = performance.now() + budgetMs;
  // NU-055: a run of counts carries no names.
  if (isNameAlignment(property)) return { kind: 'inconclusive', reason: routeBOnlyReason(property) };
  const initial: AbstractState = vectorize(initialMarking, flatNet);
  const isBad = violationPredicate(flatNet, property, sinkPlaces, conditionalSinks);
  const script = encodeBoundedRun(flatNet, initial, property, sinkPlaces, conditionalSinks, depth);
  const left = Math.floor(deadline - performance.now());
  if (left <= 0) return { kind: 'inconclusive', reason: `time budget of ${budgetMs} ms exhausted` };
  let reply: string;
  try {
    reply = await run(script, 'witness', left);
  } catch (e: any) {
    rethrowIfProgrammingError(e);
    return { kind: 'inconclusive', reason: String(e?.message ?? e) };
  }
  switch (classifyFirstLine(reply)) {
    case 'unsat':
      return { kind: 'none' };
    case 'sat': {
      const stepCount = flatNet.transitions.length + resolveEnvInjection(flatNet).length;
      const steps = decodeBoundedRun(reply, stepCount, depth);
      const replayed = steps == null ? null : replayRun(flatNet, initial, steps, isBad);
      if (steps == null || replayed == null) {
        return { kind: 'inconclusive', reason: 'the bounded run did not replay under the exact semantics' };
      }
      return { kind: 'violated', ...trimRun(flatNet, initial, steps, isBad, replayed, options.poll) };
    }
    default:
      return { kind: 'inconclusive', reason: `the bounded run at depth ${depth} answered unknown` };
  }
}

/**
 * Drops the steps a replayed run does not need. The run is first cut to its shortest
 * violating prefix ({@link violatingPrefix}); then one step at a time is removed, last first,
 * and the removal kept when the rest still has a violating prefix, which becomes the run,
 * until a pass removes nothing. The solver pads a run to the full depth, so the result ends
 * at the first violating marking it reaches and is irredundant (no single step can be
 * dropped), not claimed minimal. When `initial` violates it is the empty run, whatever the
 * model. Solver-free, and cubic in the run's length: `poll` is called before each candidate,
 * and a poll that throws ends the trim with its error.
 */
function trimRun(
  flatNet: FlatNet,
  initial: AbstractState,
  run: readonly number[],
  isBad: (state: AbstractState) => boolean,
  replayed: { states: AbstractState[]; steps: string[] },
  poll: () => void = () => {},
): { states: AbstractState[]; steps: string[] } {
  const cut = (candidate: readonly number[]): boolean => {
    const prefix = violatingPrefix(flatNet, initial, candidate, isBad);
    if (prefix == null) return false;
    run = candidate.slice(0, prefix.steps.length);
    replayed = prefix;
    return true;
  };
  cut(run);
  for (let removed = true; removed;) {
    removed = false;
    // No proper prefix of the run violates, so a cut after removing step `k` keeps more
    // than `k` steps: every lower index is still in the run.
    for (let k = run.length - 1; k >= 0; k--) {
      poll();
      if (cut(run.filter((_, i) => i !== k))) removed = true;
    }
  }
  return replayed;
}

function clears(ft: FlatTransition, p: number): boolean {
  return ft.consumeAll[p] === true || ft.resetPlaces.includes(p);
}

function guardConditions(ft: FlatTransition, m: (p: number) => string): string[] {
  const out: string[] = [];
  for (let p = 0; p < ft.preVector.length; p++) if (ft.preVector[p]! > 0) out.push(`(>= ${m(p)} ${ft.preVector[p]})`);
  for (const p of ft.inhibitorPlaces) out.push(`(= ${m(p)} 0)`);
  for (const p of ft.readPlaces) out.push(`(>= ${m(p)} 1)`);
  return out;
}

function shifted(v: string, delta: number): string {
  if (delta === 0) return v;
  return delta > 0 ? `(+ ${v} ${delta})` : `(- ${v} ${-delta})`;
}

/** Every `(define-fun <name> () Int <value>)` of a model, as `[name, value]`. */
function intDefinitions(stdout: string): [string, bigint][] {
  const out: [string, bigint][] = [];
  for (const def of extractDefineFuns(stdout)) {
    const m = /^\(define-fun\s+(\S+)\s+\(\)\s+Int\s+(\(-\s*(\d+)\s*\)|(\d+))\s*\)$/s.exec(def.trim());
    if (m != null) out.push([m[1]!, m[3] != null ? -BigInt(m[3]) : BigInt(m[4]!)]);
  }
  return out;
}
