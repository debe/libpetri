/**
 * @module state-equation-query
 *
 * The query of the state-equation phase (VER-018): one `QF_LIA` script asking
 * whether a marking the **marking equation** admits can violate the property.
 *
 * Every marking the untimed net reaches satisfies the rows of
 * {@link stateEquationConditions} for the firing counts `n ≥ 0` of the run that
 * reached it ([VER-016]): `m_p = M0_p + C_p·n` on a place whose column is exact, and
 * `m_p ≤ M0_p + C_p·n` on a place a consume-all or reset arc clears, since every
 * clearing firing removes at least its arc weight. `unsat` therefore proves the
 * property. A `sat` model is a *candidate*: a marking the equation admits, which the
 * net need not reach. The phase refines it away with inequalities every reachable
 * marking satisfies ({@link MarkingInequality}) and asks again.
 *
 * What the phase proves is `SE(M, n) ∧ ⋀ refinements(M)`, an inductive invariant
 * over the places and the firing counters. {@link refinementCertificate} renders it
 * as the `Reachable` interpretation the [VER-016] certificate check takes, which
 * re-proves initiation, consecution and safety against the raw step relation.
 */
import type { FlatNet } from '../encoding/flat-net.js';
import type { MarkingState } from '../marking-state.js';
import type { SmtProperty } from '../smt-property.js';
import type { ConditionalSinks } from '../rest-set.js';
import type { Place } from '../../core/place.js';
import {
  encodePropertyViolation, intTerm, resolveEnvInjection, stateEquationConditions, sumTerms,
} from './smt-encoder.js';
import { extractDefineFuns } from './smt-text.js';

/**
 * A linear inequality `Σ_p weights[p]·m_p ≤ constant` that every reachable marking
 * satisfies: an initially marked trap (`Σ_{q∈Q} m_q ≥ 1`, stored as weights `-1` and
 * constant `-1`), an inductive inequality, or one inductive relative to the marking
 * equation.
 */
export interface MarkingInequality {
  readonly weights: readonly bigint[];
  readonly constant: bigint;
  readonly origin: 'trap' | 'inductive' | 'relative';
}

/** A `sat` model of the query: a marking the equation admits and the firing counts it takes. */
export interface Candidate {
  readonly marking: readonly number[];
  readonly counts: readonly number[];
}

/**
 * The query: `m, n ≥ 0`, the marking equation, the refinements, and the property's
 * violation exactly as the HORN error rule encodes it.
 */
export function encodeStateEquationQuery(
  flatNet: FlatNet,
  initialMarking: MarkingState,
  property: SmtProperty,
  sinkPlaces: ReadonlySet<Place<any>>,
  conditionalSinks: readonly ConditionalSinks[],
  refinements: readonly MarkingInequality[],
): string {
  const mVars = flatNet.places.map((_, i) => `m${i}`);
  const nVars = flatNet.transitions.map((_, k) => `n${k}`);
  const lines = [
    '; State-equation phase (VER-018): every reachable marking satisfies the marking',
    '; equation for the firing counts of its run (an upper bound on a place a',
    '; consume-all or reset arc clears); unsat = no such marking violates the property.',
    '(set-logic QF_LIA)',
  ];
  for (const v of [...mVars, ...nVars]) lines.push(`(declare-const ${v} Int)`);
  for (const v of [...mVars, ...nVars]) lines.push(`(assert (>= ${v} 0))`);
  for (const c of stateEquationConditions(flatNet, initialMarking, nVars, mVars)) lines.push(`(assert ${c})`);
  for (const r of refinements) lines.push(`(assert ${inequalityTerm(r, mVars)})`);
  const bad = encodePropertyViolation(
    flatNet, property, mVars, sinkPlaces, resolveEnvInjection(flatNet), conditionalSinks,
  );
  lines.push(`(assert ${bad})`);
  lines.push('(check-sat)');
  lines.push('(get-model)');
  return lines.join('\n');
}

/** The candidate in a `sat` reply's model; `null` when the model defines no marking or counter. */
export function decodeCandidate(stdout: string, placeCount: number, transitionCount: number): Candidate | null {
  const marking = new Array<number>(placeCount).fill(0);
  const counts = new Array<number>(transitionCount).fill(0);
  let seen = false;
  for (const def of extractDefineFuns(stdout)) {
    const m = /^\(define-fun\s+([mn])(\d+)\s+\(\)\s+Int\s+(\(-\s*(\d+)\s*\)|(\d+))\s*\)$/s.exec(def.trim());
    if (m == null) continue;
    const index = Number(m[2]);
    const value = m[4] != null ? -Number(m[4]) : Number(m[5]);
    if (!Number.isSafeInteger(value)) return null;
    if (m[1] === 'm' && index < placeCount) marking[index] = value;
    else if (m[1] === 'n' && index < transitionCount) counts[index] = value;
    else continue;
    seen = true;
  }
  return seen ? { marking, counts } : null;
}

/** Whether the inequality holds at a marking, in exact integer arithmetic. */
export function holdsAt(inequality: MarkingInequality, marking: readonly number[]): boolean {
  let sum = 0n;
  for (let p = 0; p < inequality.weights.length; p++) {
    const w = inequality.weights[p]!;
    if (w !== 0n) sum += w * BigInt(marking[p] ?? 0);
  }
  return sum <= inequality.constant;
}

/**
 * The inequality as an SMT-LIB term over `vars`: `(<= Σ w·v c)`, or, when no weight
 * is positive, the same bound read the other way round — a trap is `(>= (+ v3 v5) 1)`.
 */
function inequalityTerm(inequality: MarkingInequality, vars: readonly string[]): string {
  const flip = inequality.weights.every((w) => w <= 0n);
  const terms: string[] = [];
  for (let p = 0; p < inequality.weights.length; p++) {
    const w = flip ? -inequality.weights[p]! : inequality.weights[p]!;
    if (w !== 0n) terms.push(intTerm(w, vars[p]!));
  }
  const lhs = sumTerms(terms);
  return flip
    ? `(>= ${lhs} ${literal(-inequality.constant)})`
    : `(<= ${lhs} ${literal(inequality.constant)})`;
}

/**
 * The phase's proof as the `Reachable` interpretation the [VER-016] certificate check
 * takes: `(define-fun Reachable ((x!0 Int) …) Bool …)` over the places and one firing
 * counter per flat transition. The check conjoins the marking equation itself, so the
 * body carries only the refinements, and is `true` when none was needed.
 */
export function refinementCertificate(
  placeCount: number,
  transitionCount: number,
  refinements: readonly MarkingInequality[],
): string {
  const params: string[] = [];
  for (let i = 0; i < placeCount + transitionCount; i++) params.push(`(x!${i} Int)`);
  const vars: string[] = [];
  for (let i = 0; i < placeCount; i++) vars.push(`x!${i}`);
  const terms = refinements.map((r) => inequalityTerm(r, vars));
  const body = terms.length === 0 ? 'true' : terms.length === 1 ? terms[0]! : `(and ${terms.join('\n         ')})`;
  return `(define-fun Reachable (${params.join(' ')}) Bool\n    ${body})`;
}

/** `Merge/hasdata <= Merge/ready_0 + Merge/ready_1`; a trap reads `a + b >= 1`. */
export function formatInequality(flatNet: FlatNet, inequality: MarkingInequality): string {
  const named = (p: number, w: bigint): string =>
    w === 1n ? flatNet.places[p]!.name : `${w}*${flatNet.places[p]!.name}`;
  const left: string[] = [];
  const right: string[] = [];
  inequality.weights.forEach((w, p) => {
    if (w > 0n) left.push(named(p, w));
    else if (w < 0n) right.push(named(p, -w));
  });
  if (left.length === 0) return `${right.length === 0 ? '0' : right.join(' + ')} >= ${-inequality.constant}`;
  // `a <= b` reads better than `a <= 0 + b`, so a zero constant is dropped once the
  // right-hand side has a term of its own.
  const dropZero = inequality.constant === 0n && right.length > 0;
  const rhs = dropZero ? right : [String(inequality.constant), ...right];
  return `${left.join(' + ')} <= ${rhs.join(' + ')}`;
}

function literal(c: bigint): string {
  return c < 0n ? `(- ${-c})` : String(c);
}
