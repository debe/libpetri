/**
 * @module open-net/report
 *
 * The human-readable report of an open-net verification ([VER-022]).
 */
import type { PetriNet } from '../../core/petri-net.js';
import type { Verdict } from '../smt-verification-result.js';
import type { ClosedNet } from './closure.js';
import type { OpenNetContract } from './contract.js';
import type { GraphRouteOutcome } from './graph-route.js';
import type { ContractViolation } from './result.js';

export interface ReportInput {
  readonly net: PetriNet;
  readonly closed: ClosedNet;
  readonly contract: OpenNetContract;
  readonly maxClasses: number;
  readonly graph: GraphRouteOutcome | null;
  /** Why the graph was not built, when {@link graph} is `null`. */
  readonly graphSkipped: string | null;
  readonly smtLines: readonly string[] | null;
  readonly verdict: Verdict;
  readonly violations: readonly ContractViolation[];
}

export function renderReport(input: ReportInput): string {
  const { net, closed, contract, graph, smtLines, verdict, violations } = input;
  const lines: string[] = ['=== OPEN-NET CONTRACT VERIFICATION (VER-022) ===', ''];
  lines.push(`Net: ${net.name}, closed by ${closed.environment.size} environment transitions ` +
    `over ${contract.arrivals.length} arrival groups`);
  lines.push('Contract:', ...contract.describe());
  if (closed.undeclared.length > 0) {
    lines.push(`Not declared by the net: ${closed.undeclared.join(', ')} (no arc touches them; a clause there counts zero)`);
  }
  lines.push('');

  if (graph === null) {
    lines.push(`State-class graph: skipped (${input.graphSkipped ?? 'class budget 0'})`);
  } else {
    lines.push('=== State-class graph (untimed, priority-blind) ===');
    lines.push(graph.complete
      ? `  Classes: ${graph.classCount}, closed`
      : `  Classes: ${graph.classCount}, truncated at the class budget of ${input.maxClasses}`);
  }
  if (smtLines !== null) {
    lines.push('', '=== SMT route ===', ...smtLines);
  }

  lines.push('', '=== RESULT ===');
  switch (verdict.type) {
    case 'proven':
      lines.push(`PROVEN: every quiescent marking meets the contract${contract.requiresTermination ? ' and every run comes to rest' : ''} (${verdict.method})`);
      break;
    case 'unknown':
      lines.push(`UNKNOWN: ${verdict.reason}`);
      break;
    case 'violated':
      lines.push(`VIOLATED: ${violations.length} ${violations.length === 1 ? 'part' : 'parts'} of the contract broken`);
      for (const v of violations) lines.push(...renderViolation(v));
      break;
  }
  return lines.join('\n');
}

function renderViolation(v: ContractViolation): string[] {
  const lines = [`  [${v.subject}] ${v.kind}: ${v.detail}`];
  if (!v.confirmed) lines.push('    (the solver\'s counterexample did not replay as an ordered firing sequence)');
  if (v.portTrace.length > 0) {
    lines.push('    Port trace:');
    for (const s of v.portTrace) {
      if (v.cycleStart !== null && s.step === v.cycleStart + 1) lines.push('      -- the cycle starts here --');
      const env = s.environment === null ? ''
        : s.environment === 'transition' ? ' [environment]' : ` [environment ${s.environment}]`;
      const changes = s.changes.map(c => `${c.place} ${c.delta > 0 ? '+' : ''}${c.delta}`).join(', ');
      lines.push(`      ${s.step}. ${s.transition}${env}${changes.length > 0 ? `  ${changes}` : ''}`);
    }
  }
  if (v.cycleStart !== null) {
    const stem = v.transitions.slice(0, v.cycleStart);
    const cycle = `then repeating ${v.transitions.slice(v.cycleStart).join(', ')}`;
    lines.push(`    Firing sequence: ${stem.length === 0 ? cycle : `${stem.join(', ')}, ${cycle}`}`);
  } else if (v.transitions.length > 0) {
    lines.push(`    Firing sequence: ${v.transitions.join(', ')}`);
  }
  const last = v.markings.at(-1);
  if (last !== undefined) lines.push(`    ${v.kind === 'termination' ? 'Marking on the cycle' : 'Quiescent marking'}: ${last.toString()}`);
  return lines;
}
