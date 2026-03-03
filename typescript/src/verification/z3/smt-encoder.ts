/**
 * @module smt-encoder
 *
 * Encodes a flattened Petri net as Constrained Horn Clauses (CHC) for Z3's Spacer engine.
 *
 * **CHC encoding strategy**: The net's state space is modeled as integer vectors
 * (one variable per place = token count). Three rule types:
 *
 * 1. **Init**: `Reachable(M0)` — the initial marking is reachable
 * 2. **Transition**: `Reachable(M') :- Reachable(M) ∧ enabled(M,t) ∧ fire(M,M',t)` —
 *    one rule per flat transition (XOR branches are separate transitions)
 * 3. **Error**: `Error() :- Reachable(M) ∧ violation(M)` — safety property violation
 *
 * Transition rules include: non-negativity constraints on M', P-invariant strengthening
 * clauses, and environment bounds for bounded analysis.
 *
 * Z3 types are complex and partially untyped; the ctx/fp parameters use `any`.
 */
import type { Arith, Bool, FuncDecl } from 'z3-solver';
import type { FlatNet } from '../encoding/flat-net.js';
import type { FlatTransition } from '../encoding/flat-transition.js';
import type { MarkingState } from '../marking-state.js';
import type { SmtProperty } from '../smt-property.js';
import type { PInvariant } from '../invariant/p-invariant.js';
import type { Place } from '../../core/place.js';
import { flatNetIndexOf } from '../encoding/flat-net.js';

/** Z3 high-level context. Typed as `any` because z3-solver's TS types are incomplete. */
type Z3Context = any;
/** Z3 Fixedpoint solver instance. Typed as `any` because z3-solver's TS types are incomplete. */
type Z3Fixedpoint = any;

/**
 * Result of CHC encoding.
 */
export interface EncodingResult {
  readonly errorExpr: Bool;
  readonly reachableDecl: FuncDecl;
}

/**
 * Encodes a flattened Petri net as Constrained Horn Clauses (CHC) for Z3's Spacer engine.
 *
 * CHC rules:
 * - Reachable(M0) — initial state is reachable
 * - Reachable(M') :- Reachable(M) AND enabled(M,t) AND fire(M,M',t) — transition rules
 * - Error() :- Reachable(M) AND property_violation(M) — safety property
 */
export function encode(
  ctx: Z3Context,
  fp: Z3Fixedpoint,
  flatNet: FlatNet,
  initialMarking: MarkingState,
  property: SmtProperty,
  invariants: readonly PInvariant[],
  sinkPlaces: ReadonlySet<Place<any>> = new Set(),
): EncodingResult {
  const P = flatNet.places.length;
  const Int = ctx.Int;
  const Bool_ = ctx.Bool;

  // Create sorts array for function declaration
  const intSort = Int.sort();
  const boolSort = Bool_.sort();
  const markingSorts: any[] = new Array(P).fill(intSort);

  // Create the Reachable relation: (Int, Int, ...) -> Bool
  const reachable: FuncDecl = ctx.Function.declare('Reachable', ...markingSorts, boolSort);
  fp.registerRelation(reachable);

  // Create the Error relation: () -> Bool
  const error: FuncDecl = ctx.Function.declare('Error', boolSort);
  fp.registerRelation(error);

  // === Rule 1: Initial state ===
  // Reachable(m0_0, m0_1, ..., m0_{P-1})
  const m0Args: Arith[] = [];
  for (let i = 0; i < P; i++) {
    const tokens = initialMarking.tokens(flatNet.places[i]!);
    m0Args.push(Int.val(tokens));
  }
  const initFact = (reachable as any).call(...m0Args) as Bool;
  fp.addRule(initFact, 'init');

  // === Rule 2: Transition rules ===
  for (let t = 0; t < flatNet.transitions.length; t++) {
    const ft = flatNet.transitions[t]!;
    encodeTransitionRule(ctx, fp, reachable, ft, flatNet, invariants, P);
  }

  // === Rule 3: Error rule (property violation) ===
  encodeErrorRule(ctx, fp, reachable, error, flatNet, property, sinkPlaces, P);

  return {
    errorExpr: (error as any).call() as Bool,
    reachableDecl: reachable,
  };
}

function encodeTransitionRule(
  ctx: Z3Context,
  fp: Z3Fixedpoint,
  reachable: FuncDecl,
  ft: FlatTransition,
  flatNet: FlatNet,
  invariants: readonly PInvariant[],
  P: number,
): void {
  const Int = ctx.Int;

  // Create named variables for current and next marking
  const mVars: Arith[] = [];
  const mPrimeVars: Arith[] = [];
  for (let i = 0; i < P; i++) {
    mVars.push(Int.const(`m${i}`));
    mPrimeVars.push(Int.const(`mp${i}`));
  }

  // Body: Reachable(M) AND enabled(M,t) AND fire(M,M',t) AND non-negativity(M') AND invariants(M') AND env bounds(M')
  const reachBody = (reachable as any).call(...mVars) as Bool;
  const enabled = encodeEnabled(ctx, ft, flatNet, mVars, P);
  const fireRelation = encodeFire(ctx, ft, flatNet, mVars, mPrimeVars, P);

  // Non-negativity of M'
  let nonNeg: Bool = ctx.Bool.val(true);
  for (let i = 0; i < P; i++) {
    nonNeg = ctx.And(nonNeg, mPrimeVars[i]!.ge(0));
  }

  // P-invariant constraints on M'
  const invConstraints = encodeInvariantConstraints(ctx, invariants, mPrimeVars, P);

  // Environment bounds on M'
  let envBounds: Bool = ctx.Bool.val(true);
  for (const [name, bound] of flatNet.environmentBounds) {
    const idx = flatNet.placeIndex.get(name);
    if (idx != null) {
      envBounds = ctx.And(envBounds, mPrimeVars[idx]!.le(bound));
    }
  }

  // Body conjunction
  const body = ctx.And(reachBody, enabled, fireRelation, nonNeg, invConstraints, envBounds);

  // Head: Reachable(M')
  const head = (reachable as any).call(...mPrimeVars) as Bool;

  // Rule: forall M, M'. body => head
  const allVars = [...mVars, ...mPrimeVars];
  const rule = ctx.Implies(body, head);
  const qRule = ctx.ForAll(allVars, rule);

  fp.addRule(qRule, `t_${ft.name}`);
}

function encodeEnabled(
  ctx: Z3Context,
  ft: FlatTransition,
  _flatNet: FlatNet,
  mVars: Arith[],
  P: number,
): Bool {
  let result: Bool = ctx.Bool.val(true);

  // Input requirements: M[p] >= pre[p]
  for (let p = 0; p < P; p++) {
    if (ft.preVector[p]! > 0) {
      result = ctx.And(result, mVars[p]!.ge(ft.preVector[p]!));
    }
  }

  // Read arcs: M[p] >= 1
  for (const p of ft.readPlaces) {
    result = ctx.And(result, mVars[p]!.ge(1));
  }

  // Inhibitor arcs: M[p] == 0
  for (const p of ft.inhibitorPlaces) {
    result = ctx.And(result, mVars[p]!.eq(0));
  }

  // Non-negativity of current marking
  for (let p = 0; p < P; p++) {
    result = ctx.And(result, mVars[p]!.ge(0));
  }

  return result;
}

function encodeFire(
  ctx: Z3Context,
  ft: FlatTransition,
  _flatNet: FlatNet,
  mVars: Arith[],
  mPrimeVars: Arith[],
  P: number,
): Bool {
  let result: Bool = ctx.Bool.val(true);

  for (let p = 0; p < P; p++) {
    const isReset = ft.resetPlaces.includes(p);

    if (isReset || ft.consumeAll[p]) {
      // Reset/consumeAll: M'[p] = post[p]
      result = ctx.And(result, mPrimeVars[p]!.eq(ft.postVector[p]!));
    } else {
      // Standard: M'[p] = M[p] - pre[p] + post[p]
      const delta = ft.postVector[p]! - ft.preVector[p]!;
      if (delta === 0) {
        result = ctx.And(result, mPrimeVars[p]!.eq(mVars[p]!));
      } else {
        result = ctx.And(result, mPrimeVars[p]!.eq(mVars[p]!.add(delta)));
      }
    }
  }

  return result;
}

function encodeErrorRule(
  ctx: Z3Context,
  fp: Z3Fixedpoint,
  reachable: FuncDecl,
  error: FuncDecl,
  flatNet: FlatNet,
  property: SmtProperty,
  sinkPlaces: ReadonlySet<Place<any>>,
  P: number,
): void {
  const Int = ctx.Int;

  // Create variables for the error rule
  const mVars: Arith[] = [];
  for (let i = 0; i < P; i++) {
    mVars.push(Int.const(`em${i}`));
  }

  const reachBody = (reachable as any).call(...mVars) as Bool;
  const violation = encodePropertyViolation(ctx, flatNet, property, sinkPlaces, mVars, P);

  const head = (error as any).call() as Bool;
  const body = ctx.And(reachBody, violation);
  const rule = ctx.Implies(body, head);
  const qRule = ctx.ForAll(mVars, rule);

  fp.addRule(qRule, `error_${property.type}`);
}

function encodePropertyViolation(
  ctx: Z3Context,
  flatNet: FlatNet,
  property: SmtProperty,
  sinkPlaces: ReadonlySet<Place<any>>,
  mVars: Arith[],
  P: number,
): Bool {
  switch (property.type) {
    case 'deadlock-free': {
      const deadlock = encodeDeadlock(ctx, flatNet, mVars, P);
      if (sinkPlaces.size > 0) {
        // Deadlock is only a violation if NOT at any expected sink place
        let notAtSink: Bool = ctx.Bool.val(true);
        for (const sink of sinkPlaces) {
          const idx = flatNetIndexOf(flatNet, sink);
          if (idx >= 0) {
            notAtSink = ctx.And(notAtSink, mVars[idx]!.eq(0));
          }
        }
        return ctx.And(deadlock, notAtSink);
      }
      return deadlock;
    }

    case 'mutual-exclusion': {
      const idx1 = flatNetIndexOf(flatNet, property.p1);
      const idx2 = flatNetIndexOf(flatNet, property.p2);
      if (idx1 < 0) throw new Error(`MutualExclusion references unknown place: ${property.p1.name}`);
      if (idx2 < 0) throw new Error(`MutualExclusion references unknown place: ${property.p2.name}`);
      return ctx.And(mVars[idx1]!.ge(1), mVars[idx2]!.ge(1));
    }

    case 'place-bound': {
      const idx = flatNetIndexOf(flatNet, property.place);
      if (idx < 0) throw new Error(`PlaceBound references unknown place: ${property.place.name}`);
      return mVars[idx]!.gt(property.bound);
    }

    case 'unreachable': {
      let allMarked: Bool = ctx.Bool.val(true);
      for (const place of property.places) {
        const idx = flatNetIndexOf(flatNet, place);
        if (idx >= 0) {
          allMarked = ctx.And(allMarked, mVars[idx]!.ge(1));
        }
      }
      return allMarked;
    }
  }
}

/** Encodes the deadlock condition: no transition is enabled. */
function encodeDeadlock(
  ctx: Z3Context,
  flatNet: FlatNet,
  mVars: Arith[],
  P: number,
): Bool {
  let deadlock: Bool = ctx.Bool.val(true);

  for (const ft of flatNet.transitions) {
    const enabled = encodeEnabled(ctx, ft, flatNet, mVars, P);
    deadlock = ctx.And(deadlock, ctx.Not(enabled));
  }

  return deadlock;
}

function encodeInvariantConstraints(
  ctx: Z3Context,
  invariants: readonly PInvariant[],
  mVars: Arith[],
  P: number,
): Bool {
  let result: Bool = ctx.Bool.val(true);

  for (const inv of invariants) {
    // sum(y_i * M[i]) == constant
    let sum: Arith = ctx.Int.val(0);
    for (const idx of inv.support) {
      if (idx < P) {
        sum = sum.add(mVars[idx]!.mul(inv.weights[idx]!));
      }
    }
    result = ctx.And(result, sum.eq(inv.constant));
  }

  return result;
}
