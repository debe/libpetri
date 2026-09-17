/**
 * @module invariant-synthesis
 *
 * Inductive-inequality refinement for the state-equation phase (VER-018).
 *
 * The marking equation knows how often each transition fired, never in what order,
 * and it ignores the guards that impose the order. The typical spurious candidate on
 * a workflow net is a join that *skipped* — a transition inhibited by `hasdata` —
 * after the data token arrived: every count balances, and only the inhibitor rules
 * the run out. A trap cannot say that either. This refinement looks for one linear
 * inequality `a·M ≤ b` that
 *
 * 1. holds at `M0`,
 * 2. is kept by every step of the **exact** step relation — input weights, read and
 *    inhibitor guards, consume-all and reset clearing included, which is where it
 *    gets its power over the equation — and
 * 3. excludes the candidate: `a·M* ≥ b + 1`.
 *
 * For the join above that is `hasdata ≤ ready_0 + ready_1`: arrivals raise both
 * sides together, `skip` fires only when `hasdata` is empty, and `start` clears it.
 *
 * Condition 2 is the Farkas form of consecution (Colón, Sankaranarayanan and Sipma,
 * "Linear invariant generation using non-linear constraint solving", CAV 2003) with
 * the invariant's own multiplier restricted to `λ_t ∈ {0, 1}` per transition, which
 * keeps the query linear. Write `l_p = max(pre_p, 1 if p is read)` for the guard's
 * lower bound; an inhibited place is exactly `0` before the step.
 *
 * - `λ_t = 1`, the step keeps the bound: `a·M' − a·M ≤ 0` for every enabled `M`. A
 *   place `t` does not clear contributes its column `C_p`; a place it clears
 *   contributes `post_p − M_p ≤ post_p − l_p`, provided `a_p ≥ 0` (on an inhibited
 *   cleared place `M_p = 0`, so `post_p` and no sign condition).
 * - `λ_t = 0`, the guard restores the bound on its own: `a_p ≤ 0` on every place `t`
 *   neither clears nor inhibits, so `a·M'` is largest at `M = l`, and that value is
 *   `≤ b`.
 *
 * An environment injection must keep the bound (`a_p ≤ 0` on an injected place). The
 * query is one `QF_LIA` script with integer weights in `[−bound, bound]`.
 *
 * The weights {@link encodeInductiveInequality} returns are re-checked in exact integer
 * arithmetic ({@link checkInductiveExact}) before they are used. Those of
 * {@link encodeRelativeInequality} are not, and cannot be: that bound holds only relative
 * to the marking equation, so the exact re-check would reject it. It rests on the
 * certificate check, which re-proves the whole refinement against the raw step relation
 * before any verdict rests on it.
 */
import type { FlatNet } from '../encoding/flat-net.js';
import type { FlatTransition } from '../encoding/flat-transition.js';
import { nonlinearPlaces } from '../invariant/p-invariant-computer.js';
import { conjoin, intTerm, resolveEnvInjection, sumTerms } from './smt-encoder.js';
import { extractDefineFuns } from './smt-text.js';
import type { MarkingInequality } from './state-equation-query.js';

/** The default magnitude bound on the weights the query may choose. */
export const DEFAULT_WEIGHT_BOUND = 8;

/** The two ways a transition can keep `a·M ≤ b`, as coefficient rows over the places. */
interface StepShape {
  /** `λ = 1`: `a_p ≥ 0` on these places, and `Σ keep[p]·a_p ≤ 0`. */
  readonly keepNonNegative: readonly number[];
  readonly keep: readonly number[];
  /** `λ = 0`: `a_p ≤ 0` on every place outside `restoreFree`, and `Σ restore[p]·a_p ≤ b`. */
  readonly restoreFree: readonly number[];
  readonly restore: readonly number[];
}

/** The shape of `ft`, or `null` when it can never fire (it inhibits a place it needs). */
function stepShape(ft: FlatTransition, placeCount: number): StepShape | null {
  const inhibited = new Set(ft.inhibitorPlaces);
  const read = new Set(ft.readPlaces);
  const resets = new Set(ft.resetPlaces);
  for (const p of inhibited) if (ft.preVector[p]! > 0 || read.has(p)) return null;
  const keep = new Array<number>(placeCount).fill(0);
  const restore = new Array<number>(placeCount).fill(0);
  const keepNonNegative: number[] = [];
  const restoreFree: number[] = [];
  for (let p = 0; p < placeCount; p++) {
    const pre = ft.preVector[p]!;
    const post = ft.postVector[p]!;
    const lower = Math.max(pre, read.has(p) ? 1 : 0);
    if (resets.has(p) || ft.consumeAll[p]) {
      if (inhibited.has(p)) {
        keep[p] = post;
      } else {
        keep[p] = post - lower;
        keepNonNegative.push(p);
      }
      restore[p] = post;
      restoreFree.push(p);
    } else if (inhibited.has(p)) {
      keep[p] = post - pre;
      restore[p] = post - pre;
      restoreFree.push(p);
    } else {
      keep[p] = post - pre;
      restore[p] = post - pre + lower;
    }
  }
  return { keepNonNegative, keep, restoreFree, restore };
}

/**
 * The `QF_LIA` script asking for weights `a` and bound `b` meeting conditions 1–3 of the
 * module description for `candidate`. `u_p ≥ max(a_p, 0)`, so a transition's `λ = 0` sign
 * condition is the one equation `Σ_p u_p = Σ_{p free} u_p`.
 */
export function encodeInductiveInequality(
  flatNet: FlatNet,
  initial: readonly number[],
  candidate: readonly number[],
  weightBound: number = DEFAULT_WEIGHT_BOUND,
): string {
  const P = flatNet.places.length;
  const a = (p: number): string => `a${p}`;
  const u = (p: number): string => `u${p}`;
  const lines = [
    '; Inductive-inequality refinement (VER-018): a.M <= b holding at M0, kept by every',
    '; step of the exact step relation (guards and clearing included), and excluding',
    '; the candidate marking.',
    '(set-logic QF_LIA)',
  ];
  const w = (p: number): string => `w${p}`;
  for (let p = 0; p < P; p++) lines.push(`(declare-const ${a(p)} Int)`);
  for (let p = 0; p < P; p++) lines.push(`(declare-const ${u(p)} Int)`);
  for (let p = 0; p < P; p++) lines.push(`(declare-const ${w(p)} Int)`);
  lines.push('(declare-const b Int)');
  lines.push('(declare-const upos Int)');
  for (let p = 0; p < P; p++) {
    lines.push(`(assert (and (>= ${a(p)} (- ${weightBound})) (<= ${a(p)} ${weightBound})))`);
    lines.push(`(assert (and (>= ${u(p)} 0) (>= ${u(p)} ${a(p)})))`);
    lines.push(`(assert (and (>= ${w(p)} 0) (>= ${w(p)} (- ${a(p)}))))`);
  }
  lines.push(`(assert (= upos ${sumTerms([...Array(P).keys()].map(u))}))`);
  lines.push(`(assert (<= ${linear(initial, a)} b))`);
  lines.push(`(assert (>= ${linear(candidate, a)} (+ b 1)))`);
  for (const ft of flatNet.transitions) {
    const shape = stepShape(ft, P);
    if (shape == null) continue;
    const keeps = [...shape.keepNonNegative.map((p) => `(>= ${a(p)} 0)`), `(<= ${linear(shape.keep, a)} 0)`];
    const restores = [`(= upos ${sumTerms(shape.restoreFree.map(u))})`, `(<= ${linear(shape.restore, a)} b)`];
    lines.push(`(assert (or ${conjoin(keeps)} ${conjoin(restores)}))`);
  }
  for (const inj of resolveEnvInjection(flatNet)) lines.push(`(assert (<= ${a(inj.pid)} 0))`);
  // The sparsest inequality reads as the structural fact and excludes more candidates.
  lines.push(`(minimize ${sumTerms([...Array(P).keys()].flatMap((p) => [u(p), w(p)]))})`);
  lines.push('(check-sat)');
  lines.push('(get-model)');
  return lines.join('\n');
}

/**
 * The query of {@link encodeInductiveInequality} with the marking equation as a
 * premise of every step: the inequality need only be kept by steps from markings the
 * equation admits. A bound like `q + 3·out ≤ 3` on a queue that is bundled once a
 * signal arrives needs it — `produce` keeps the bound only because `q ≤ 2` whenever
 * `budget ≥ 1`, and that is the equation's `q + budget ≤ 3`.
 *
 * By Farkas, the premise contributes to transition `t`'s consecution one linear
 * consequence of the equation: a weighting `η^t` with `η^t·C_j ≤ 0` on every column
 * `j`, non-negative on a place whose row is an upper bound and absent on an injected
 * place, so that `η^t·M ≤ η^t·M0` holds wherever the equation does. With
 * `κ_t = Σ_{p not cleared} a_p·C_p + Σ_{p cleared} a_p·post_p` the two cases read:
 *
 * - `λ_t = 1`: `η^t_p ≥ 0` on a place `t` neither clears nor inhibits, `a_p + η^t_p ≥ 0`
 *   on a place it clears, and `κ_t ≤ −η^t·M0 + Σ_{p not inhibited} ν_p·l_p`, with
 *   `ν_p = η^t_p` (`a_p + η^t_p` on a cleared place).
 * - `λ_t = 0`: `a_p ≤ η^t_p` on a place `t` neither clears nor inhibits, `η^t_p ≥ 0` on
 *   a place it clears, and `κ_t − b ≤ −η^t·M0 + Σ ν_p·l_p`, with `ν_p = η^t_p − a_p`
 *   (`η^t_p` on a cleared place).
 *
 * With `η^t = 0` these are the conditions of {@link encodeInductiveInequality}. The
 * query carries one weighting per transition, so the phase asks it only when that
 * one found nothing. The weightings are real; the inequality's weights stay integers.
 * The certificate check re-proves the result as part of `SE ∧ refinements`.
 */
export function encodeRelativeInequality(
  flatNet: FlatNet,
  initial: readonly number[],
  candidate: readonly number[],
  weightBound: number = DEFAULT_WEIGHT_BOUND,
): string {
  const P = flatNet.places.length;
  const T = flatNet.transitions.length;
  const upper = nonlinearPlaces(flatNet);
  const injected = new Set(resolveEnvInjection(flatNet).map((inj) => inj.pid));
  const rows = [...Array(P).keys()].filter((p) => !injected.has(p));
  const ra = (p: number): string => `(to_real a${p})`;
  const lines = [
    '; Inductive-inequality refinement relative to the marking equation (VER-018):',
    '; a.M <= b holding at M0, kept by every step from a marking the equation admits',
    '; (one Farkas weighting e<t>_<p> of the equation per transition), and excluding',
    '; the candidate marking.',
    '(set-logic QF_LIRA)',
  ];
  for (let p = 0; p < P; p++) lines.push(`(declare-const a${p} Int)`);
  for (let p = 0; p < P; p++) lines.push(`(declare-const u${p} Int)`);
  for (let p = 0; p < P; p++) lines.push(`(declare-const w${p} Int)`);
  lines.push('(declare-const b Int)');
  for (let p = 0; p < P; p++) {
    lines.push(`(assert (and (>= a${p} (- ${weightBound})) (<= a${p} ${weightBound})))`);
    lines.push(`(assert (and (>= u${p} 0) (>= u${p} a${p})))`);
    lines.push(`(assert (and (>= w${p} 0) (>= w${p} (- a${p}))))`);
  }
  lines.push(`(assert (<= ${linear(initial, (p) => `a${p}`)} b))`);
  lines.push(`(assert (>= ${linear(candidate, (p) => `a${p}`)} (+ b 1)))`);
  for (const p of injected) lines.push(`(assert (<= a${p} 0))`);
  for (let t = 0; t < T; t++) {
    const parts = stepParts(flatNet.transitions[t]!, P);
    if (parts == null) continue;
    const e = (p: number): string => `e${t}_${p}`;
    for (const p of rows) lines.push(`(declare-const ${e(p)} Real)`);
    for (const p of rows) if (upper.has(p)) lines.push(`(assert (>= ${e(p)} 0))`);
    for (const col of flatNet.transitions) {
      const terms: string[] = [];
      for (const p of rows) {
        const c = col.postVector[p]! - col.preVector[p]!;
        if (c !== 0) terms.push(scaled(c, e(p)));
      }
      if (terms.length > 0) lines.push(`(assert (<= ${sumTerms(terms)} 0.0))`);
    }
    // κ_t over the weights, and −η·M0.
    const kappa: string[] = [];
    for (let p = 0; p < P; p++) {
      const c = parts.cleared[p] ? parts.post[p]! : parts.delta[p]!;
      if (c !== 0) kappa.push(scaled(c, ra(p)));
    }
    const etaM0: string[] = [];
    for (const p of rows) if (initial[p]! !== 0) etaM0.push(scaled(-initial[p]!, e(p)));
    const keep: string[] = [];
    const keepRhs = [...etaM0];
    const restore: string[] = [];
    const restoreRhs = [...etaM0];
    for (let p = 0; p < P; p++) {
      if (parts.inhibited[p]) continue;
      const l = parts.lower[p]!;
      const eta = injected.has(p) ? '0.0' : e(p);
      if (parts.cleared[p]) {
        keep.push(`(>= (+ ${ra(p)} ${eta}) 0.0)`);
        restore.push(`(>= ${eta} 0.0)`);
        if (l !== 0) {
          keepRhs.push(scaled(l, `(+ ${ra(p)} ${eta})`));
          restoreRhs.push(scaled(l, eta));
        }
      } else {
        keep.push(`(>= ${eta} 0.0)`);
        restore.push(`(<= ${ra(p)} ${eta})`);
        if (l !== 0) {
          keepRhs.push(scaled(l, eta));
          restoreRhs.push(scaled(l, `(- ${eta} ${ra(p)})`));
        }
      }
    }
    keep.push(`(<= ${sumTerms(kappa, '0.0')} ${sumTerms(keepRhs, '0.0')})`);
    restore.push(`(<= (- ${sumTerms(kappa, '0.0')} (to_real b)) ${sumTerms(restoreRhs, '0.0')})`);
    lines.push(`(assert (or ${conjoin(keep)} ${conjoin(restore)}))`);
  }
  lines.push(`(minimize ${sumTerms([...Array(P).keys()].flatMap((p) => [`u${p}`, `w${p}`]))})`);
  lines.push('(check-sat)');
  lines.push('(get-model)');
  return lines.join('\n');
}

/** The arcs of `ft` per place, or `null` when it can never fire (it inhibits a place it needs). */
function stepParts(
  ft: FlatTransition,
  placeCount: number,
): { cleared: boolean[]; inhibited: boolean[]; lower: number[]; delta: number[]; post: number[] } | null {
  const inhibited = new Array<boolean>(placeCount).fill(false);
  for (const p of ft.inhibitorPlaces) inhibited[p] = true;
  const read = new Set(ft.readPlaces);
  for (let p = 0; p < placeCount; p++) if (inhibited[p] && (ft.preVector[p]! > 0 || read.has(p))) return null;
  const resets = new Set(ft.resetPlaces);
  const cleared: boolean[] = [];
  const lower: number[] = [];
  const delta: number[] = [];
  const post: number[] = [];
  for (let p = 0; p < placeCount; p++) {
    cleared.push(resets.has(p) || ft.consumeAll[p] === true);
    lower.push(Math.max(ft.preVector[p]!, read.has(p) ? 1 : 0));
    delta.push(ft.postVector[p]! - ft.preVector[p]!);
    post.push(ft.postVector[p]!);
  }
  return { cleared, inhibited, lower, delta, post };
}

/** `c·x` for a real-valued `x`, `c` an integer. */
function scaled(c: number, x: string): string {
  if (c === 1) return x;
  if (c === -1) return `(- ${x})`;
  return c > 0 ? `(* ${c}.0 ${x})` : `(* (- ${-c}.0) ${x})`;
}

/** The inequality in a `sat` reply's model; `null` when the model defines no weight or no bound. */
export function decodeInductiveInequality(stdout: string, placeCount: number): MarkingInequality | null {
  const weights = new Array<bigint>(placeCount).fill(0n);
  let constant: bigint | null = null;
  for (const def of extractDefineFuns(stdout)) {
    const m = /^\(define-fun\s+(a(\d+)|b)\s+\(\)\s+Int\s+(\(-\s*(\d+)\s*\)|(\d+))\s*\)$/s.exec(def.trim());
    if (m == null) continue;
    const value = m[4] != null ? -BigInt(m[4]) : BigInt(m[5]!);
    if (m[1] === 'b') constant = value;
    else if (Number(m[2]) < placeCount) weights[Number(m[2])] = value;
  }
  return constant == null ? null : { weights, constant, origin: 'inductive' };
}

/**
 * Re-proves conditions 1 and 2 of the module description in exact integer
 * arithmetic: the inequality holds at `M0`, every injected place has a weight `≤ 0`,
 * and every transition that can fire either keeps the bound (`λ = 1`) or restores it
 * from its guard (`λ = 0`). Condition 3 is not needed for soundness.
 */
export function checkInductiveExact(
  flatNet: FlatNet,
  initial: readonly number[],
  inequality: MarkingInequality,
): boolean {
  const { weights, constant } = inequality;
  const P = flatNet.places.length;
  if (weights.length !== P) return false;
  if (dot(weights, initial) > constant) return false;
  for (const inj of resolveEnvInjection(flatNet)) if (weights[inj.pid]! > 0n) return false;
  for (const ft of flatNet.transitions) {
    const shape = stepShape(ft, P);
    if (shape == null) continue;
    if (shape.keepNonNegative.every((p) => weights[p]! >= 0n) && dot(weights, shape.keep) <= 0n) continue;
    const free = new Set(shape.restoreFree);
    const signs = weights.every((w, p) => w <= 0n || free.has(p));
    if (!signs || dot(weights, shape.restore) > constant) return false;
  }
  return true;
}

function dot(weights: readonly bigint[], values: readonly number[]): bigint {
  let s = 0n;
  for (let p = 0; p < weights.length; p++) {
    if (weights[p] !== 0n && values[p] !== 0) s += weights[p]! * BigInt(values[p]!);
  }
  return s;
}

/** `Σ coeffs[p]·var(p)` over the non-zero coefficients, `0` when there are none. */
function linear(coeffs: readonly number[], v: (p: number) => string): string {
  const terms: string[] = [];
  for (let p = 0; p < coeffs.length; p++) {
    const c = coeffs[p]!;
    if (c === 0) continue;
    terms.push(intTerm(c, v(p)));
  }
  return sumTerms(terms);
}
