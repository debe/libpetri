/**
 * @module open-net/predicate
 *
 * The contract's guarantee at one quiescent marking ([VER-022]): which clauses it breaks and
 * which places it strands. Stranding is the [VER-014] rest set every `DeadlockFree` route
 * reads, so the SMT route can ask for it with `deadlockFree()`.
 */
import type { Place } from '../../core/place.js';
import { compareCodePoints } from '../../core/internal/code-point-order.js';
import type { MarkingState } from '../marking-state.js';
import { tokensAcross, countViolation } from '../graph-decision.js';
import { strandedPlaces, type ConditionalSinks } from '../rest-set.js';
import { countAcross } from '../smt-property.js';
import type { ClosedNet } from './closure.js';
import type { CountClause, OpenNetContract } from './contract.js';

/** One thing a quiescent marking breaks. */
export type Finding =
  | { readonly kind: 'clause'; readonly clause: CountClause; readonly count: number; readonly bound: 'lower' | 'upper' }
  | { readonly kind: 'stranded'; readonly place: string; readonly count: number };

/** The contract's rest set in [VER-014] form. */
export interface RestDeclaration {
  readonly sinks: ReadonlySet<Place<any>>;
  readonly conditional: readonly ConditionalSinks[];
}

/**
 * Clause places, rest places and the environment's own places as sinks; each designed
 * terminal as a conditional sink.
 */
export function restDeclarationOf(contract: OpenNetContract, closed: ClosedNet): RestDeclaration {
  const sinks = new Map<string, Place<any>>();
  for (const c of contract.clauses) for (const p of c.places) if (!sinks.has(p.name)) sinks.set(p.name, p);
  for (const p of contract.rest) if (!sinks.has(p.name)) sinks.set(p.name, p);
  for (const p of closed.environmentPlaces) if (!sinks.has(p.name)) sinks.set(p.name, p);
  return {
    sinks: new Set(sinks.values()),
    conditional: contract.terminals.map(t => ({ marker: t.marker, places: new Set(t.excused) })),
  };
}

/** The clause lower bounds' waivers, for both routes: every designed terminal's marker ([VER-002]). */
export function waiverMarkers(contract: OpenNetContract): Place<any>[] {
  return contract.terminals.map(t => t.marker);
}

/**
 * The places `m` strands, in code-point order of their names ([VER-013]). Both routes
 * attribute a stranding through this: marked **and** unexcused, with the [VER-014]
 * widening, so neither reports a stranding the other proves impossible.
 */
export function strandedNames(m: MarkingState, rest: RestDeclaration): Place<any>[] {
  return strandedPlaces(m, rest.sinks, rest.conditional).sort((a, b) => compareCodePoints(a.name, b.name));
}

/**
 * What the quiescent marking `m` breaks: clauses in contract order, then stranded places by
 * name. Empty when `m` meets the contract.
 */
export function quiescenceFindings(m: MarkingState, contract: OpenNetContract, rest: RestDeclaration): Finding[] {
  const findings: Finding[] = [];
  // Each clause is a QuiescentCount waived by every terminal marker ([VER-002]).
  const markers = waiverMarkers(contract);
  for (const clause of contract.clauses) {
    const bound = countViolation(m, clause.places, clause.min, clause.max, markers);
    if (bound !== null) findings.push({ kind: 'clause', clause, count: tokensAcross(m, clause.places), bound });
  }
  for (const place of strandedNames(m, rest)) {
    findings.push({ kind: 'stranded', place: place.name, count: m.tokens(place) });
  }
  return findings;
}

/** The finding's subject: its clause's name or its place's name. */
export function subjectOf(f: Finding): string {
  return f.kind === 'clause' ? f.clause.name : f.place;
}

/** The finding in words. */
export function describeFinding(f: Finding): string {
  if (f.kind === 'stranded') {
    return `${f.place} holds ${f.count} at quiescence, and nothing in the contract lets a token rest there`;
  }
  const { clause } = f;
  const expected = countAcross(clause.min, clause.max, clause.places);
  return f.bound === 'upper'
    ? `${expected} at quiescence, found ${f.count} (an upper bound holds under a terminal too)`
    : `${expected} at quiescence, found ${f.count}`;
}
