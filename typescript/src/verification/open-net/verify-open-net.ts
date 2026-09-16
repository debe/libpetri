/**
 * @module open-net/verify-open-net
 *
 * A subnet verified on its own against a contract, with its ports played by the
 * environment ([VER-022]).
 *
 * The subnet is closed with the environment its contract describes, and the closed net's
 * untimed state-class graph is enumerated. When the graph closes, the verdict is exact.
 * When it does not, a violation found among the explored classes is still real, and the rest
 * of the contract goes to the SMT pipeline, through the properties it already has.
 *
 * A caller that builds its nets from a fixed vocabulary of subnets gets one proof per
 * subnet, and each proof costs what the subnet costs rather than what the interleavings of
 * the whole net cost. Turning those proofs into a claim about the composed net is the
 * caller's own theorem; this entry proves the pieces.
 */
import type { PetriNet } from '../../core/petri-net.js';
import type { SmtVerifier } from '../smt-verifier.js';
import type { Verdict } from '../smt-verification-result.js';
import { closeOpenNet } from './closure.js';
import type { OpenNetContract } from './contract.js';
import { decideOnGraph } from './graph-route.js';
import { renderReport } from './report.js';
import type { ContractViolation, OpenNetResult, OpenNetRoute } from './result.js';
import { decideViaSmt, type SubjectCertificate } from './smt-route.js';

/** Options for {@link verifyOpenNet}. */
export interface OpenNetOptions {
  /** Class budget for the state-class graph (default 50 000, as for [VER-017]). `0` skips the graph. */
  readonly maxClasses?: number;
  /** Whether to ask the SMT pipeline when the graph does not close (default `true`). */
  readonly smt?: boolean;
  /** Configures each `SmtVerifier` the SMT route builds, e.g. `v => v.timeout(120_000).stateEquation(true)`. */
  readonly configureSmt?: (verifier: SmtVerifier) => SmtVerifier;
  /** Time for the firing-bound query that decides termination on the SMT route (default 60 s). */
  readonly terminationTimeoutMs?: number;
}

const DEFAULT_MAX_CLASSES = 50_000;
const METHOD_ENUMERATION = 'open-net contract by state-space enumeration (VER-022)';
const METHOD_SMT = 'open-net contract by the SMT pipeline (VER-022)';

/**
 * Verifies `net` in isolation against `contract` ([VER-022]).
 *
 * `proven` means that, in every run of the environment the contract assumes, every
 * quiescent marking meets the contract, and (unless termination is waived) every run comes
 * to rest. The claim is untimed, priority-blind and value-blind, like every route's
 * ([VER-004]). `violated` lists every broken part with a shortest witness, and
 * `unknown` says why neither route decided.
 *
 * @throws when the net violates CORE-043, as every verifier does, or when the closure's
 *   names collide with the net's
 */
export async function verifyOpenNet(
  net: PetriNet,
  contract: OpenNetContract,
  options: OpenNetOptions = {},
): Promise<OpenNetResult> {
  const start = performance.now();
  const closed = closeOpenNet(net, contract);
  const maxClasses = options.maxClasses ?? DEFAULT_MAX_CLASSES;
  const useSmt = options.smt ?? true;
  // Every place a port trace may mention: the contract's own, plus the closure's. [VER-022]
  // reserves "port" for a place the environment shares with the subnet, which is narrower.
  const tracedPlaces = contract.places();
  // The graph is name-blind: it fires a ν-join on any two tokens, whether or not their names
  // match. For a quiescence contract that is no approximation in either direction — it reaches
  // markings the net cannot (the join's output) and misses ones it does (the inputs a join that
  // cannot match leaves stranded), so neither its `proven` nor its `violated` can stand. The same
  // exclusion as [VER-017] condition 1; the SMT pipeline has exact routes for a ν-net.
  const graphSkipped = [...closed.net.transitions].some(t => t.matchSpec !== null)
    ? 'the closed net declares match (ν-join) transitions, which the graph does not model'
    : maxClasses > 0 ? null : 'class budget 0';
  const graph = graphSkipped === null ? decideOnGraph(closed, contract, maxClasses, tracedPlaces) : null;

  const result = (
    verdict: Verdict,
    route: OpenNetRoute,
    violations: readonly ContractViolation[],
    smtLines: readonly string[] | null,
  ): OpenNetResult => ({
    verdict,
    violations,
    route,
    classCount: graph?.classCount ?? 0,
    graphComplete: graph?.complete ?? false,
    report: renderReport({ net, closed, contract, maxClasses, graph, graphSkipped, smtLines, verdict, violations }),
    closedNet: closed.net,
    closedMarking: closed.initialMarking,
    elapsedMs: performance.now() - start,
  });

  if (graph !== null) {
    if (graph.violations.length > 0) {
      return result({ type: 'violated' }, 'enumeration', graph.violations, null);
    }
    if (graph.complete) {
      // No invariant: the closed graph proves the contract by exhausting its classes, and the
      // classes themselves are the evidence. There is no certificate here to lose.
      return result({ type: 'proven', method: METHOD_ENUMERATION, inductiveInvariant: null }, 'enumeration', [], null);
    }
  }
  const why = graph !== null
    ? `the state-class graph did not close within ${maxClasses} classes`
    : graphSkipped === 'class budget 0'
      ? 'the state-class graph was skipped'
      : `the state-class graph was skipped: ${graphSkipped}`;
  if (!useSmt) {
    return result({ type: 'unknown', reason: `${why}, and the SMT route is disabled` }, 'enumeration', [], null);
  }

  const smt = await decideViaSmt(
    closed, contract, tracedPlaces, options.configureSmt ?? (v => v), options.terminationTimeoutMs ?? 60_000,
  );
  if (smt.violations.length > 0) return result({ type: 'violated' }, 'smt', smt.violations, smt.lines);
  if (smt.undecided.length === 0) {
    return result(
      { type: 'proven', method: METHOD_SMT, inductiveInvariant: combineCertificates(smt.certificates) },
      'smt', [], smt.lines,
    );
  }
  return result(
    { type: 'unknown', reason: `${why}; left undecided by the SMT route: ${smt.undecided.join('; ')}` },
    'smt', [], smt.lines,
  );
}

/**
 * The route's certificates as one invariant, each labelled with the part of the contract it
 * proves. The whole verdict is their conjunction, so keeping them apart keeps them readable.
 *
 * `null` when no query returned one. That is weaker evidence, not a weaker verdict: a part
 * proven by a bound or by enumeration has no invariant to give.
 */
function combineCertificates(certificates: readonly SubjectCertificate[]): string | null {
  if (certificates.length === 0) return null;
  return certificates.map(c => `[${c.subject}] ${c.invariant}`).join('\n');
}
