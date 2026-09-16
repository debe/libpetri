/**
 * @module state-equation-phase
 *
 * The refinement loop of the state-equation phase (VER-018).
 *
 * One `QF_LIA` query asks whether a marking the marking equation admits violates the
 * property ({@link encodeStateEquationQuery}). `unsat` proves it. A `sat` model is a
 * candidate, and each round settles it one of three ways, cheapest first:
 *
 * 1. **Witness** — a real run from `M0` within the candidate's firing counts that
 *    reaches a violation ({@link searchWithinCounts}). The property is violated, and
 *    the run is the counterexample.
 * 2. **Trap** — an initially marked trap the candidate leaves empty
 *    ({@link refutingTrap}); `Σ_{q∈Q} m_q ≥ 1` is added and the query asked again.
 * 3. **Inductive inequality** — `a·M ≤ b`, kept by the exact step relation and
 *    excluding the candidate ({@link encodeInductiveInequality}), re-checked in exact
 *    integer arithmetic and added. When there is none, the same question is asked
 *    *relative to the marking equation* ({@link encodeRelativeInequality}), which is
 *    where the spec's `N·out + q ≤ N` shape comes from. A relative inequality is not
 *    inductive on its own, so it cannot be re-checked the same way: the certificate
 *    check over the equation and its refinements is what re-proves it.
 *
 * Every refinement holds in every reachable marking, so an `unsat` after refinement
 * is still a proof, and the refinements it used are its certificate. When none of the
 * three settles a candidate, or the refinement budget or the deadline runs out, the
 * phase is inconclusive and the verifier falls through to the fixpoint query exactly
 * as before; the phase can add verdicts, never remove them.
 */
import type { FlatNet } from '../encoding/flat-net.js';
import type { MarkingState } from '../marking-state.js';
import type { SmtProperty } from '../smt-property.js';
import type { ConditionalSinks } from '../rest-set.js';
import type { Place } from '../../core/place.js';
import { rethrowIfProgrammingError } from '../programming-error.js';
import { classifyFirstLine } from './smt-text.js';
import { vectorize, violationPredicate, type AbstractState } from './abstract-replayer.js';
import {
  decodeCandidate, encodeStateEquationQuery, holdsAt, type Candidate, type MarkingInequality,
} from './state-equation-query.js';
import { refutingTrap } from './trap-refinement.js';
import {
  DEFAULT_WEIGHT_BOUND, checkInductiveExact, decodeInductiveInequality, encodeInductiveInequality,
  encodeRelativeInequality,
} from './invariant-synthesis.js';
import { searchWithinCounts } from './parikh-search.js';

/** The solver phase a script belongs to (`LIBPETRI_SMT_DUMP` file names, VER-013). */
export type StateEquationScriptPhase = 'state-equation' | 'invariant';

/**
 * Runs one script through the solver within `timeoutMs` and resolves with its stdout.
 * Rejects when the transport failed or the reply carries no verdict line, with the
 * reason as the message.
 */
export type StateEquationSolver = (script: string, phase: StateEquationScriptPhase, timeoutMs: number) => Promise<string>;

/** Options of {@link runStateEquationPhase}. */
export interface StateEquationPhaseOptions {
  /** The most refinements the phase adds before it gives up (default 32). */
  readonly maxRefinements?: number;
  /** The magnitude bound on an inductive inequality's weights (default {@link DEFAULT_WEIGHT_BOUND}). */
  readonly weightBound?: number;
  /** The node budget of each witness search (default 100 000). */
  readonly witnessNodes?: number;
  /** Wall-clock budget for the whole phase in milliseconds; each query gets what is left (default 60 000). */
  readonly budgetMs?: number;
}

/** Outcome of {@link runStateEquationPhase}. */
export type StateEquationOutcome =
  | {
      readonly kind: 'proven';
      /** The refinements the final `unsat` used, in the order they were added. */
      readonly refinements: readonly MarkingInequality[];
      /** Solver queries sent, both dump phases counted. */
      readonly queries: number;
    }
  | {
      readonly kind: 'violated';
      readonly states: readonly AbstractState[];
      readonly steps: readonly string[];
      readonly refinements: readonly MarkingInequality[];
      readonly queries: number;
    }
  | {
      readonly kind: 'inconclusive';
      readonly reason: string;
      readonly refinements: readonly MarkingInequality[];
      readonly queries: number;
      /** The candidate the phase stopped on, when it stopped holding one. */
      readonly candidate: Candidate | null;
    };

/**
 * Runs the phase on the flat path. The caller runs the certificate check on a
 * `proven` outcome before reporting it ({@link refinementCertificate}).
 */
export async function runStateEquationPhase(
  flatNet: FlatNet,
  initialMarking: MarkingState,
  property: SmtProperty,
  sinkPlaces: ReadonlySet<Place<any>>,
  conditionalSinks: readonly ConditionalSinks[],
  run: StateEquationSolver,
  options: StateEquationPhaseOptions = {},
): Promise<StateEquationOutcome> {
  const maxRefinements = options.maxRefinements ?? 32;
  const witnessNodes = options.witnessNodes ?? 100_000;
  const budgetMs = options.budgetMs ?? 60_000;
  const deadline = performance.now() + budgetMs;
  const P = flatNet.places.length;
  const T = flatNet.transitions.length;
  const initial: AbstractState = vectorize(initialMarking, flatNet);
  // A bound like `N·out + q ≤ N` weighs a flag by the capacity of the queue it guards,
  // so the default bound grows with the tokens the net starts with.
  const weightBound = options.weightBound ?? Math.max(DEFAULT_WEIGHT_BOUND, initial.reduce((s, v) => s + v, 0));
  const isBad = violationPredicate(flatNet, property, sinkPlaces, conditionalSinks);
  const refinements: MarkingInequality[] = [];
  let queries = 0;
  const inconclusive = (reason: string, candidate: Candidate | null = null): StateEquationOutcome =>
    ({ kind: 'inconclusive', reason, refinements, queries, candidate });

  const ask = async (script: string, phase: StateEquationScriptPhase): Promise<string | Error> => {
    const left = Math.floor(deadline - performance.now());
    if (left <= 0) return new Error(`time budget of ${budgetMs} ms exhausted`);
    queries++;
    try {
      return await run(script, phase, left);
    } catch (e: any) {
      rethrowIfProgrammingError(e);
      return new Error(String(e?.message ?? e));
    }
  };

  /** The inequality a synthesis query found, `null` when it proved there is none, or why it failed. */
  async function synthesize(script: string): Promise<MarkingInequality | null | Error> {
    const reply = await ask(script, 'invariant');
    if (reply instanceof Error) return reply;
    switch (classifyFirstLine(reply)) {
      case 'sat':
        return decodeInductiveInequality(reply, P) ?? new Error('the inductive-inequality model could not be decoded');
      case 'unsat':
        return null;
      default:
        return new Error('the inductive-inequality query answered unknown');
    }
  }

  /**
   * The refinement that excludes `candidate`, cheapest first: a trap, then an inequality
   * inductive on its own, then one inductive only relative to the marking equation. The
   * `Error` is the reason the phase cannot go on, not a failure of the net.
   */
  async function refine(candidate: Candidate): Promise<MarkingInequality | Error> {
    const trap = refutingTrap(flatNet, initial, candidate.marking);
    if (trap != null) return trap;

    // An inequality inductive on its own is cheaper to find and re-checked exactly;
    // one inductive relative to the equation is asked for only when there is none.
    const inductive = await synthesize(encodeInductiveInequality(flatNet, initial, candidate.marking, weightBound));
    if (inductive instanceof Error) return inductive;
    if (inductive != null) {
      if (!checkInductiveExact(flatNet, initial, inductive) || holdsAt(inductive, candidate.marking)) {
        return new Error('an inductive inequality failed the exact re-check');
      }
      return inductive;
    }

    const relative = await synthesize(encodeRelativeInequality(flatNet, initial, candidate.marking, weightBound));
    if (relative instanceof Error) return relative;
    if (relative == null) {
      return new Error(`no trap and no inductive inequality with weights within ±${weightBound} excludes the candidate`);
    }
    if (holdsAt(relative, candidate.marking)) {
      return new Error('an inductive inequality does not exclude its candidate');
    }
    // decodeInductiveInequality labels every model 'inductive'; the report must tell this one apart.
    return { ...relative, origin: 'relative' };
  }

  for (;;) {
    const query = encodeStateEquationQuery(flatNet, initialMarking, property, sinkPlaces, conditionalSinks, refinements);
    const reply = await ask(query, 'state-equation');
    if (reply instanceof Error) return inconclusive(reply.message);
    const answer = classifyFirstLine(reply);
    if (answer === 'unsat') return { kind: 'proven', refinements, queries };
    // `null` cannot reach here: the StateEquationSolver contract rejects a reply with no verdict line.
    if (answer !== 'sat') return inconclusive('the state-equation query answered unknown');
    const candidate = decodeCandidate(reply, P, T);
    if (candidate == null) return inconclusive('the state-equation model could not be decoded');

    const witness = searchWithinCounts(flatNet, initial, candidate.counts, isBad, witnessNodes);
    if (witness.kind === 'found') {
      return { kind: 'violated', states: witness.states, steps: witness.steps, refinements, queries };
    }
    if (refinements.length >= maxRefinements) {
      return inconclusive(`refinement budget exhausted (${maxRefinements} refinements)`, candidate);
    }

    const refinement = await refine(candidate);
    if (refinement instanceof Error) return inconclusive(refinement.message, candidate);
    refinements.push(refinement);
  }
}

/** `a=1, b=1 after t0 x1, t2 x1` — a candidate as the report prints it. */
export function describeCandidate(flatNet: FlatNet, candidate: Candidate): string {
  const marked = candidate.marking
    .map((v, p) => (v === 0 ? null : `${flatNet.places[p]!.name}=${v}`))
    .filter((s): s is string => s != null);
  const fired = candidate.counts
    .map((v, t) => (v === 0 ? null : `${flatNet.transitions[t]!.name} x${v}`))
    .filter((s): s is string => s != null);
  return `${marked.length === 0 ? '{}' : marked.join(', ')} after ${fired.length === 0 ? 'no firing' : fired.join(', ')}`;
}
