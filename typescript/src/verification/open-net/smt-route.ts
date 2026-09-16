/**
 * @module open-net/smt-route
 *
 * The contract asked of the SMT pipeline, for a closed net whose graph does not close
 * ([VER-022]).
 *
 * Each part of the contract is one query on the closed net, and each decides exactly the
 * predicate the graph route reads:
 *
 * - **stranding**: `deadlockFree()` with the clause places, the rest places and the
 *   environment's own places as sinks, and each terminal as a conditional sink ([VER-014]).
 * - **a count clause**: `quiescentCount(places, min, max, markers)` ([VER-002]), with every
 *   terminal marker as a waiver.
 * - **termination**: the firing-bound ranking of [VER-019] on the closed net. Weights that
 *   every firing lowers bound the length of every run by what they give the initial
 *   marking, so no run goes on forever. When there are none, the part is undecided and the
 *   reason names the firings the marking equation lets repeat.
 */
import type { Place } from '../../core/place.js';
import { flatten } from '../encoding/net-flattener.js';
import { tokensAcross } from '../graph-decision.js';
import { rethrowIfProgrammingError } from '../programming-error.js';
import { type ConditionalSinks } from '../rest-set.js';
import {
  countAcross, deadlockFree, propertyDescription, quiescentCount, type SmtProperty,
} from '../smt-property.js';
import type { SmtVerificationResult } from '../smt-verification-result.js';
import { SmtVerifier } from '../smt-verifier.js';
import {
  checkRankingExact, decodeRanking, decodeRepeatableVector, encodeRankingQuery, encodeRepeatableVectorQuery,
  formatRanking,
} from '../z3/bounded-run.js';
import { failureReason, resolveZ3, runZ3Text, timeoutBudget, Z3Unavailable, type Z3Solver } from '../z3/z3-process.js';
import type { ClosedNet } from './closure.js';
import type { OpenNetContract } from './contract.js';
import { restDeclarationOf, strandedNames, waiverMarkers } from './predicate.js';
import { contractViolation, type ContractViolation } from './result.js';

/** What the SMT route found. */
export interface SmtRouteOutcome {
  readonly violations: readonly ContractViolation[];
  /** The parts of the contract no query decided, each with its reason. */
  readonly undecided: readonly string[];
  /** One report line per query. */
  readonly lines: readonly string[];
  /**
   * The inductive invariant each proven query returned, in query order. These are the
   * route's proof evidence: a `proven` open-net verdict is their conjunction, one
   * certificate per part of the contract.
   */
  readonly certificates: readonly SubjectCertificate[];
}

/** One part of the contract and the invariant that proved it. */
export interface SubjectCertificate {
  readonly subject: string;
  readonly invariant: string;
}

interface Query {
  readonly subject: string;
  readonly property: SmtProperty;
  readonly sinks: readonly Place<any>[];
  readonly conditional: readonly ConditionalSinks[];
  /** The violation a `violated` verdict means. */
  readonly onViolated: (result: SmtVerificationResult) => Omit<ContractViolation, 'portTrace'>;
}

/**
 * A part of the contract: a query to run, or a clause no marking can fail.
 *
 * A count clause of `[0, ∞]` is the second kind. `countViolation` reports `upper` only
 * above `max` and `lower` only below `min`, so every marking satisfies it and both routes
 * agree without asking anything — the graph route's `quiescenceFindings` finds nothing for
 * it either. Its places still carry their weight through `restDeclarationOf`, which makes
 * every clause place a sink of the stranding query. Running the query anyway would be
 * strictly worse than skipping it: the answer is `proven` on a solver that has time and
 * `unknown` on one that does not. It gets a report line so that skipping it is visible
 * rather than silent.
 */
type Part =
  | { readonly kind: 'query'; readonly query: Query }
  | { readonly kind: 'vacuous'; readonly subject: string; readonly detail: string };

/** Runs one query per part of the contract, in contract order, then the firing bound. */
export async function decideViaSmt(
  closed: ClosedNet,
  contract: OpenNetContract,
  tracedPlaces: readonly Place<any>[],
  configure: (verifier: SmtVerifier) => SmtVerifier,
  terminationTimeoutMs: number,
): Promise<SmtRouteOutcome> {
  const violations: ContractViolation[] = [];
  const undecided: string[] = [];
  const lines: string[] = [];
  const certificates: SubjectCertificate[] = [];
  for (const part of partsFor(closed, contract)) {
    if (part.kind === 'vacuous') {
      lines.push(`  [${part.subject}] ${part.detail}: proven (no query needed)`);
      continue;
    }
    const q = part.query;
    let verifier = SmtVerifier.forNet(closed.net)
      .initialMarking(closed.initialMarking)
      .property(q.property)
      .sinkPlaces(...q.sinks)
      // The graph route already enumerated as far as its budget allows.
      .enumerationMaxClasses(0);
    for (const c of q.conditional) verifier = verifier.sinkPlacesWhen(c.marker, ...c.places);
    const result = await configure(verifier).verify();
    const verdict = result.verdict;
    lines.push(`  [${q.subject}] ${propertyDescription(q.property)}: ${verdict.type}`
      + (verdict.type === 'unknown' ? ` (${verdict.reason})` : ''));
    if (verdict.type === 'unknown') undecided.push(`${q.subject}: ${verdict.reason}`);
    else if (verdict.type === 'violated') violations.push(contractViolation(closed, tracedPlaces, q.onViolated(result)));
    // A proven part may or may not come with a certificate: the enumeration and bound
    // phases prove without one. Keep the ones that do rather than dropping the evidence.
    else if (verdict.inductiveInvariant !== null) {
      certificates.push({ subject: q.subject, invariant: verdict.inductiveInvariant });
    }
  }
  if (contract.requiresTermination) {
    const termination = await terminationByRanking(closed, terminationTimeoutMs);
    if (termination.proven) {
      lines.push(`  [termination] Firing bound (VER-019): ${termination.detail}`);
    } else {
      lines.push(`  [termination] Firing bound (VER-019): undecided (${termination.reason})`);
      undecided.push(`termination: ${termination.reason}`);
    }
  }
  return { violations, undecided, lines, certificates };
}

function partsFor(closed: ClosedNet, contract: OpenNetContract): Part[] {
  const rest = restDeclarationOf(contract, closed);
  const markers = waiverMarkers(contract);
  // The last marking of a replay-confirmed counterexample is the quiescent one it reached.
  const quiescentMarking = (result: SmtVerificationResult) =>
    result.counterexampleConfirmed === true ? result.counterexampleTrace.at(-1) : undefined;
  const witness = (result: SmtVerificationResult) => ({
    transitions: [...result.counterexampleTransitions],
    markings: [...result.counterexampleTrace],
    cycleStart: null,
    confirmed: result.counterexampleConfirmed === true,
  });

  const stranding: Query = {
    subject: 'stranding',
    property: deadlockFree(),
    sinks: [...rest.sinks],
    conditional: rest.conditional,
    onViolated: result => {
      // The verdict does not depend on the replay — the solver's `sat` is the violation. The
      // attribution does: without a confirmed quiescent marking there is nothing to read the
      // stranded places off, so the finding names the query rather than guessing a place.
      const last = quiescentMarking(result);
      const stranded = last === undefined ? [] : strandedNames(last, rest).map(p => p.name);
      return {
        kind: 'stranded',
        subject: stranded.length === 0 ? 'stranding' : stranded.join(', '),
        detail: stranded.length === 0
          ? 'the solver found a reachable quiescent marking that leaves a token where the contract lets none rest'
          : `${stranded.join(', ')} ${stranded.length === 1 ? 'holds' : 'hold'} a token at quiescence, and nothing in the contract lets one rest there`,
        ...witness(result),
      };
    },
  };

  const parts: Part[] = [{ kind: 'query', query: stranding }];

  for (const clause of contract.clauses) {
    const across = countAcross(clause.min, clause.max, clause.places);
    if (clause.min === 0 && clause.max === Infinity) {
      parts.push({ kind: 'vacuous', subject: clause.name, detail: `${across} at quiescence` });
      continue;
    }
    const query: Query = {
      subject: clause.name,
      property: quiescentCount(clause.places, clause.min, clause.max, markers),
      sinks: [],
      conditional: [],
      onViolated: result => {
        const last = quiescentMarking(result);
        return {
          kind: 'clause',
          subject: clause.name,
          detail: last === undefined
            ? `${across} at quiescence: the solver found a quiescent marking outside it`
            : `${across} at quiescence, found ${tokensAcross(last, clause.places)}`,
          ...witness(result),
        };
      },
    };
    parts.push({ kind: 'query', query });
  }
  return parts;
}

/**
 * Termination by the firing-bound ranking of [VER-019]: weights `r ≥ 0` that every firing
 * of the closed net lowers by at least one, re-checked in exact arithmetic. No run then has
 * more than `r·M0` firings. When there are none, the Farkas alternative names the firings
 * the marking equation lets repeat.
 */
async function terminationByRanking(
  closed: ClosedNet,
  timeoutMs: number,
): Promise<{ readonly proven: true; readonly detail: string } | { readonly proven: false; readonly reason: string }> {
  const flat = flatten(closed.net);
  const initial = flat.places.map(p => closed.initialMarking.tokens(p));
  let solver: Z3Solver;
  try {
    solver = resolveZ3();
  } catch (e) {
    if (e instanceof Z3Unavailable) return { proven: false, reason: e.message };
    throw e;
  }
  const ask = async (script: string): Promise<string | Error> => {
    try {
      const reply = await runZ3Text(solver, script, 'ranking', timeoutMs, []);
      const answer = firstLine(reply.stdout);
      if (answer === 'sat' || answer === 'unsat' || answer === 'unknown') return reply.stdout;
      return new Error(failureReason(reply, timeoutBudget(timeoutMs)));
    } catch (e) {
      rethrowIfProgrammingError(e);
      return new Error(String((e as Error)?.message ?? e));
    }
  };

  const ranking = await ask(encodeRankingQuery(flat, initial));
  if (ranking instanceof Error) return { proven: false, reason: ranking.message };
  const answer = firstLine(ranking);
  if (answer === 'sat') {
    const weights = decodeRanking(ranking, flat.places.length);
    const bound = weights === null ? null : checkRankingExact(flat, initial, weights);
    if (bound === null) return { proven: false, reason: 'the firing-bound ranking failed the exact re-check' };
    return {
      proven: true,
      detail: `every run has at most ${bound.bound} firings (${formatRanking(flat, bound)} drops on every firing)`,
    };
  }
  if (answer === 'unsat') {
    const vector = await ask(encodeRepeatableVectorQuery(flat));
    const repeat = vector instanceof Error || firstLine(vector) !== 'sat'
      ? null
      : decodeRepeatableVector(vector, flat.transitions.length);
    return {
      proven: false,
      reason: repeat === null || repeat.length === 0
        ? 'no firing bound: no weights drop on every firing'
        : `no firing bound: the marking equation lets ${repeat.map(t => flat.transitions[t]!.name).join(', ')} repeat`,
    };
  }
  return { proven: false, reason: 'the firing-bound query answered unknown' };
}

function firstLine(stdout: string): string {
  return stdout.split('\n').find(line => line.trim() !== '')?.trim() ?? '';
}
