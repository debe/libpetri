/**
 * @module linear-bound
 *
 * The linear state-equation bound (VER-015): a structural proof of a
 * reachability-safety property that needs no fixpoint search.
 *
 * Every reachable marking of the abstract net satisfies `M = M0 + C·σ` for some
 * firing count vector `σ ≥ 0`, so for any weighting `y ≥ 0` with `y·C ≤ 0` on every
 * transition, `y·M ≤ y·M0` holds along every run — a **decreasing** conservation
 * law, where the P-invariants of [VER-005] are the *equalities* `y·C = 0`. The
 * violation of a reachability-safety property is a lower demand on some places
 * (`m_p ≥ 1` for each place of an `unreachable`, `m_p ≥ k+1` for a `placeBound`);
 * if some `y` makes that demand exceed `y·M0`, no reachable marking meets it and the
 * property is proven.
 *
 * Finding `y` is one linear query in `QF_LIA`, answered by the same `z3` transport
 * as everything else ([VER-013]); the answer is then re-checked in exact integer
 * arithmetic (`y ≥ 0`, `y·C ≤ 0` per transition, `y·d ≥ y·M0 + 1`), so the proof
 * rests on the check, not on the solver. It closes exactly the class of proofs IC3
 * misses on pipeline-shaped nets: an ordering argument ("both join slots armed means
 * every upstream stage has run, so no halt is still possible") is a weighted count
 * bound, which Spacer's lemma generalisation does not invent over fifty variables
 * but a linear solver finds in milliseconds.
 *
 * Soundness needs the same guards as the equality laws: zero weight on every
 * consume-all / reset place (H1 — the fire relation is not linear there) and on
 * every injected environment place (H3' — injection breaks conservation).
 */
import type { FlatNet } from '../encoding/flat-net.js';
import type { MarkingState } from '../marking-state.js';
import type { SmtProperty } from '../smt-property.js';
import { nonlinearPlaces } from '../invariant/p-invariant-computer.js';
import { resolveEnvInjection } from './smt-encoder.js';
import { extractDefineFuns } from './smt-text.js';

/** One linear bound `Σ weights[p]·m_p ≤ constant`, with the demand it separates. */
export interface LinearBound {
  /** `y`, one entry per flat place, all non-negative. */
  readonly weights: readonly bigint[];
  /** `y·M0`. */
  readonly constant: bigint;
  /** `y·d`, what the violating markings need at least; strictly above `constant`. */
  readonly demandValue: bigint;
}

/**
 * The violation's demand: flat place index → the least count a violating marking
 * holds there. `null` when the property is not a reachability-safety property, or
 * names no place the net resolves (the verifier refuses those before this runs).
 */
export function violationDemand(flatNet: FlatNet, property: SmtProperty): Map<number, number> | null {
  const demand = new Map<number, number>();
  switch (property.type) {
    case 'unreachable':
      for (const p of property.places) {
        const pid = flatNet.placeIndex.get(p.name);
        if (pid != null) demand.set(pid, 1);
      }
      break;
    case 'mutual-exclusion': {
      for (const p of [property.p1, property.p2]) {
        const pid = flatNet.placeIndex.get(p.name);
        if (pid != null) demand.set(pid, 1);
      }
      break;
    }
    case 'place-bound':
    case 'branch-place-bound': {
      const pid = flatNet.placeIndex.get(property.place.name);
      if (pid != null) demand.set(pid, property.bound + 1);
      break;
    }
    case 'deadlock-free':
    case 'terminates-at-sink':
    case 'joined-or-dead-lettered':
      return null;
  }
  return demand.size === 0 ? null : demand;
}

/** The places whose weight is pinned to zero: H1 (consume-all / reset) and H3' (injected). */
export function zeroWeightPlaces(flatNet: FlatNet): Set<number> {
  const zero = new Set<number>(nonlinearPlaces(flatNet));
  for (const inj of resolveEnvInjection(flatNet)) zero.add(inj.pid);
  return zero;
}

/**
 * The `QF_LIA` script asking for a separating `y`, or `null` when the property has
 * no linear demand. Byte-identical across the four implementations: places in flat
 * index order, one row per flat transition in net order, `(- k)` for a negative
 * literal, a lone term unwrapped.
 */
export function encodeLinearBound(flatNet: FlatNet, initialMarking: MarkingState, property: SmtProperty): string | null {
  const demand = violationDemand(flatNet, property);
  if (demand == null) return null;
  const P = flatNet.places.length;
  const zero = zeroWeightPlaces(flatNet);
  const lines: string[] = [];
  lines.push('; Linear state-equation bound (VER-015): y >= 0 with y.C <= 0 on every');
  lines.push('; transition gives y.M <= y.M0 for every reachable M; sat = the violating');
  lines.push("; markings' demand exceeds that bound, so none is reachable.");
  lines.push('(set-logic QF_LIA)');
  for (let p = 0; p < P; p++) lines.push(`(declare-const y${p} Int)`);
  for (let p = 0; p < P; p++) lines.push(`(assert (>= y${p} 0))`);
  for (const p of [...zero].sort((a, b) => a - b)) lines.push(`(assert (= y${p} 0))`);
  for (const ft of flatNet.transitions) {
    const terms: string[] = [];
    for (let p = 0; p < P; p++) {
      const c = ft.postVector[p]! - ft.preVector[p]!;
      if (c !== 0) terms.push(term(c, `y${p}`));
    }
    if (terms.length > 0) lines.push(`(assert (<= ${sum(terms)} 0))`);
  }
  const demandTerms: string[] = [];
  for (const p of [...demand.keys()].sort((a, b) => a - b)) demandTerms.push(term(demand.get(p)!, `y${p}`));
  const initTerms: string[] = ['1'];
  for (let p = 0; p < P; p++) {
    const m0 = initialMarking.tokens(flatNet.places[p]!);
    if (m0 > 0) initTerms.push(term(m0, `y${p}`));
  }
  lines.push(`(assert (>= ${sum(demandTerms)} ${sum(initTerms)}))`);
  lines.push('(check-sat)');
  lines.push('(get-model)');
  return lines.join('\n');
}

function term(c: number, v: string): string {
  if (c === 1) return v;
  if (c === -1) return `(- ${v})`;
  return c > 0 ? `(* ${c} ${v})` : `(* (- ${-c}) ${v})`;
}

function sum(terms: readonly string[]): string {
  return terms.length === 1 ? terms[0]! : `(+ ${terms.join(' ')})`;
}

/**
 * The weighting in a `sat` reply's model: `y_p` per flat place, zero where the model
 * is silent. `null` when the reply defines no `y`.
 */
export function decodeLinearBound(stdout: string, placeCount: number): bigint[] | null {
  const y = new Array<bigint>(placeCount).fill(0n);
  let seen = false;
  for (const def of extractDefineFuns(stdout)) {
    const m = /^\(define-fun\s+y(\d+)\s+\(\)\s+Int\s+(\(-\s*(\d+)\s*\)|(\d+))\s*\)$/s.exec(def.trim());
    if (m == null) continue;
    const pid = Number(m[1]);
    if (pid >= placeCount) continue;
    y[pid] = m[3] != null ? -BigInt(m[3]) : BigInt(m[4]!);
    seen = true;
  }
  return seen ? y : null;
}

/**
 * Re-proves the bound in exact integer arithmetic: `y ≥ 0`, zero on every H1/H3'
 * place, `y·C ≤ 0` on every flat transition, and `y·d ≥ y·M0 + 1`. Returns the bound
 * when every check passes and `null` otherwise — the verifier then continues to the
 * fixpoint query rather than trust the solver's model.
 */
export function checkLinearBoundExact(
  flatNet: FlatNet,
  initialMarking: MarkingState,
  property: SmtProperty,
  y: readonly bigint[],
): LinearBound | null {
  const demand = violationDemand(flatNet, property);
  if (demand == null) return null;
  const P = flatNet.places.length;
  if (y.length !== P) return null;
  const zero = zeroWeightPlaces(flatNet);
  for (let p = 0; p < P; p++) {
    if (y[p]! < 0n) return null;
    if (zero.has(p) && y[p]! !== 0n) return null;
  }
  for (const ft of flatNet.transitions) {
    let delta = 0n;
    for (let p = 0; p < P; p++) {
      if (y[p]! === 0n) continue;
      delta += y[p]! * BigInt(ft.postVector[p]! - ft.preVector[p]!);
    }
    if (delta > 0n) return null;
  }
  let constant = 0n;
  for (let p = 0; p < P; p++) {
    if (y[p]! !== 0n) constant += y[p]! * BigInt(initialMarking.tokens(flatNet.places[p]!));
  }
  let demandValue = 0n;
  for (const [p, d] of demand) demandValue += y[p]! * BigInt(d);
  if (demandValue < constant + 1n) return null;
  return { weights: y, constant, demandValue };
}

/** `2*a + b <= 2` — the bound as the report prints it. */
export function formatLinearBound(flatNet: FlatNet, bound: LinearBound): string {
  const parts: string[] = [];
  for (let p = 0; p < bound.weights.length; p++) {
    const w = bound.weights[p]!;
    if (w === 0n) continue;
    parts.push(w === 1n ? flatNet.places[p]!.name : `${w}*${flatNet.places[p]!.name}`);
  }
  return `${parts.length === 0 ? '0' : parts.join(' + ')} <= ${bound.constant}`;
}

/** `ready_0 + ready_1 + _halt >= 3` — the violation's weighted demand as the report prints it. */
export function formatLinearDemand(flatNet: FlatNet, property: SmtProperty, bound: LinearBound): string {
  const demand = violationDemand(flatNet, property) ?? new Map<number, number>();
  const parts: string[] = [];
  for (const p of [...demand.keys()].sort((a, b) => a - b)) {
    const w = bound.weights[p]! * BigInt(demand.get(p)!);
    if (w === 0n) continue;
    parts.push(w === 1n ? flatNet.places[p]!.name : `${w}*${flatNet.places[p]!.name}`);
  }
  return `${parts.length === 0 ? '0' : parts.join(' + ')} >= ${bound.demandValue}`;
}
