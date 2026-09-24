/**
 * @module open-net/verify-open-net
 *
 * A subnet verified on its own against a contract, with its ports played by the environment
 * ([VER-022]). The closed net's untimed state-class graph decides exactly when it closes; a
 * violation it finds stands either way, and otherwise the SMT pipeline gets the contract.
 * Composing the per-subnet proofs into a claim about a whole net is the caller's theorem.
 */
import type { PetriNet } from '../../core/petri-net.js';
import type { SmtVerifier } from '../smt-verifier.js';
import type { Verdict } from '../smt-verification-result.js';
import { closeOpenNet } from './closure.js';
import { withDesignedTerminals, type OpenNetContract } from './contract.js';
import { terminalExcusedPlaces, withTerminalInhibitors } from '../terminal-places.js';
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
const SKIPPED_BY_BUDGET = 'class budget 0';
const SKIPPED_BY_MATCH = 'the closed net declares match (ν-join) transitions, which the graph does not model';

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
  let closed = closeOpenNet(net, contract);
  // EXEC-042 / VER-014: the net's own terminal places, applied without the caller restating
  // them. Each inhibits every transition of the closed net (the environment's too: after a
  // terminal stop the runtime admits nothing), and is merged as a designed terminal excusing
  // every place of the closed net.
  if (closed.net.terminals.size > 0) {
    contract = withDesignedTerminals(contract, closed.net.terminals, terminalExcusedPlaces(closed.net));
    closed = { ...closed, net: withTerminalInhibitors(closed.net) };
  }
  const maxClasses = options.maxClasses ?? DEFAULT_MAX_CLASSES;
  const useSmt = options.smt ?? true;
  // The places a port trace reports changes on.
  const tracedPlaces = contract.places();
  // The graph is name-blind: it fires a ν-join on tokens whose names differ and never strands
  // the inputs of a join that cannot match, so for a quiescence contract neither its `proven`
  // nor its `violated` stands ([VER-017] condition 1). The SMT pipeline has exact ν routes.
  const graphSkipped = [...closed.net.transitions].some(t => t.matchSpec !== null)
    ? SKIPPED_BY_MATCH
    : maxClasses > 0 ? null : SKIPPED_BY_BUDGET;
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
      // No invariant: the exhausted graph is the evidence.
      return result({ type: 'proven', method: METHOD_ENUMERATION, inductiveInvariant: null }, 'enumeration', [], null);
    }
  }
  const why = graph !== null
    ? `the state-class graph did not close within ${maxClasses} classes`
    : graphSkipped === SKIPPED_BY_BUDGET
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
 * The route's certificates, each labelled with the contract part it proves, or `null` when no
 * query returned one (a part proven by a bound or by enumeration has none).
 */
function combineCertificates(certificates: readonly SubjectCertificate[]): string | null {
  if (certificates.length === 0) return null;
  return certificates.map(c => `[${c.subject}] ${c.invariant}`).join('\n');
}
