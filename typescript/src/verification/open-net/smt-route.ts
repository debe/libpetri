/**
 * @module open-net/smt-route
 *
 * The contract asked of the SMT pipeline when the graph does not close ([VER-022]). Each part
 * is one query on the closed net, deciding exactly the predicate the graph route reads:
 *
 * - **stranding**: `deadlockFree()` with clause, rest and environment places as sinks and each
 *   terminal as a conditional sink ([VER-014]);
 * - **a count clause**: `quiescentCount(places, min, max, markers)` ([VER-002]), every
 *   terminal marker a waiver;
 * - **termination**: the firing-bound ranking of [VER-019]; without one the part is undecided,
 *   naming the firings the marking equation lets repeat.
 */
import { PetriNet } from '../../core/petri-net.js';
import type { Place } from '../../core/place.js';
import { Transition } from '../../core/transition.js';
import { flatten } from '../encoding/net-flattener.js';
import { countAcross, tokensAcross } from '../count-clause.js';
import { rethrowIfProgrammingError } from '../programming-error.js';
import type { ConditionalSinks } from '../rest-set.js';
import { isUntimed } from '../scg-verifier.js';
import {
  deadlockFree, propertyDescription, quiescentCount, type SmtProperty,
} from '../smt-property.js';
import type { SmtVerificationResult } from '../smt-verification-result.js';
import { SmtVerifier } from '../smt-verifier.js';
import { findFiringBound, formatRanking } from '../z3/bounded-run.js';
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
  /** The inductive invariant each proven query returned, in query order; a `proven` verdict is their conjunction. */
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
 * A `[0, ∞]` clause is the second kind: the graph route finds nothing for it either, and its
 * places still count as sinks of the stranding query. Asking would only risk `unknown`, so it
 * is skipped with a report line.
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
  const net = untimed(closed.net);
  for (const part of partsFor(closed, contract)) {
    if (part.kind === 'vacuous') {
      lines.push(`  [${part.subject}] ${part.detail}: proven (no query needed)`);
      continue;
    }
    const q = part.query;
    let verifier = SmtVerifier.forNet(net)
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
    // Some routes prove without a certificate; keep the ones that come with one.
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

/**
 * `net` with every transition `immediate`, so each query decides the untimed claim ([VER-004]).
 * The flat encoders ignore timing, but a ν-net's quiescence query goes to the name-aware graph
 * (NU-050), which keeps it and would prove the weaker timed claim.
 */
function untimed(net: PetriNet): PetriNet {
  if (isUntimed(net)) return net;
  const transitions = [...net.transitions].map(t => {
    if (t.timing.type === 'immediate') return t;
    const b = Transition.builder(t.name).inputs(...t.inputSpecs).priority(t.priority).action(t.action);
    if (t.outputSpec !== null) b.outputs(t.outputSpec);
    for (const arc of t.inhibitors) b.inhibitor(arc.place);
    for (const arc of t.reads) b.read(arc.place);
    for (const arc of t.resets) b.reset(arc.place);
    if (t.matchSpec !== null) b.match(t.matchSpec);
    return b.build();
  });
  return PetriNet.builder(net.name).places(...net.places).transitions(...transitions)
    .terminals(...net.terminals) // EXEC-042
    .build();
}

function partsFor(closed: ClosedNet, contract: OpenNetContract): Part[] {
  const rest = restDeclarationOf(contract, closed);
  const markers = waiverMarkers(contract);
  // A replay-confirmed counterexample ends in the quiescent marking it reached.
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
      // The verdict stands without the replay; naming the stranded places needs its marking.
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

/** Termination by the firing-bound ranking of [VER-019] on the closed net: no run has more than `r·M0` firings. */
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
  // A reply is read only when its first non-blank line is the verdict.
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

  const ranking = await findFiringBound(flat, initial, ask);
  switch (ranking.kind) {
    case 'bound':
      return {
        proven: true,
        detail: `every run has at most ${ranking.bound.bound} firings (${formatRanking(flat, ranking.bound)} drops on every firing)`,
      };
    case 'unbounded':
      return {
        proven: false,
        reason: ranking.repeatable === null
          ? 'no firing bound: no weights drop on every firing'
          : `no firing bound: the marking equation lets ${ranking.repeatable.map(t => flat.transitions[t]!.name).join(', ')} repeat`,
      };
    case 'rejected':
      return { proven: false, reason: 'the firing-bound ranking failed the exact re-check' };
    case 'unknown':
      return { proven: false, reason: 'the firing-bound query answered unknown' };
    case 'failed':
      return { proven: false, reason: ranking.reason };
  }
}

function firstLine(stdout: string): string {
  return stdout.split('\n').find(line => line.trim() !== '')?.trim() ?? '';
}
