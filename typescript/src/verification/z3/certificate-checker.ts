/**
 * @module certificate-checker
 *
 * Independent re-validation of the inductive invariant Z3 Spacer synthesizes
 * for a `proven` verdict (the IC3 certificate).
 *
 * A "proven" answer from the Fixedpoint engine is only as trustworthy as Z3
 * plus the CHC encoder. This module re-checks the certificate with a plain
 * `ctx.Solver()` in the same Z3 WASM context, against the UNSTRENGTHENED step
 * relation ({@link encodeStepRelation} — no P-invariant conjuncts), so even a
 * wrong-but-validated-looking invariant strengthening can never smuggle a
 * false PROVEN through. Three validity conditions, each expected UNSAT:
 *
 * 1. **VC1 (init)**: `¬I(M₀)` — the initial marking satisfies the invariant
 * 2. **VC2 (consecution)**: `I(M) ∧ M ≥ 0 ∧ T(M,M') ∧ ¬I(M')` — the invariant
 *    is inductive under the unstrengthened step relation
 * 3. **VC3 (safety)**: `I(M) ∧ M ≥ 0 ∧ Bad(M)` — the invariant excludes every
 *    property-violating marking
 *
 * The `M ≥ 0` domain conjunct in VC2/VC3 is sound: the net's state space is
 * ℕ^P (the initial marking is non-negative, transition steps constrain
 * `M' ≥ 0`, and injection steps only increment), so restricting the check to
 * ℕ^P checks exactly the states the system can inhabit — while the invariant
 * itself is only required to over-approximate `Reachable`, which never leaves
 * ℕ^P either.
 *
 * **Answer AST shapes** (`fp.getAnswer()` after an UNSAT query): typically a
 * top-level `and` of one definition per relation, where the `Reachable`
 * definition is `forall vars. Reachable(vars) = φ` (equivalence; `iff` and the
 * over-approximating `Reachable(vars) => φ` are accepted too). A ground
 * (unquantified) `Reachable(args) = φ` definition is handled as well. Inside a
 * `forall` the arguments of the `Reachable` application are de Bruijn
 * variables; argument position `j` names place `j`, and `ctx.substituteVars`
 * maps de Bruijn index `i` to its `to[i]` — the mapping is built from
 * `getVarIndex` per argument, so any bound-variable order is handled.
 *
 * **Candidate certificate**: Spacer synthesizes its invariant against CHC
 * bodies that conjoin the exactly-validated P-invariants, so the plain answer
 * `I` is often inductive only RELATIVE to that strengthening (e.g. `¬(B ≥ 2)`
 * relying on `A + B = 1` — bare consecution fails). The checked candidate is
 * therefore `R' := I ∧ (y·M = y·M₀ for each validated P-invariant)`, with all
 * three VCs proven for `R'` from scratch against the same unstrengthened step
 * relation (the design shared with the Rust and Java checkers). The
 * strengthening is verified, never assumed: a poisoned P-invariant fails VC1
 * (wrong constant) or VC2 (wrong weights) of `R'` and the verdict downgrades,
 * while a genuine strengthening-dependent certificate passes.
 *
 * Outcomes are split the way the caller must treat them: `failed` names the
 * first VC that was not UNSAT (with the solver status and, for SAT, a witness
 * marking), `unavailable` means the check could not run at all (missing or
 * unparseable answer, solver error). Both withhold PROVEN; neither throws.
 */
import type { Arith, Bool, Expr } from 'z3-solver';
import type { FlatNet } from '../encoding/flat-net.js';
import type { MarkingState } from '../marking-state.js';
import type { SmtProperty } from '../smt-property.js';
import type { PInvariant } from '../invariant/p-invariant.js';
import type { Place } from '../../core/place.js';
import { encodeInvariantConstraints, encodePropertyViolation, encodeStepRelation } from './smt-encoder.js';

/** Z3 high-level context. Typed as `any` because z3-solver's TS types are incomplete. */
type Z3Context = any;

/** Label of a validity condition, as it appears in the downgrade reason. */
export type CertificateVc = 'initiation (VC1)' | 'consecution (VC2)' | 'safety (VC3)';

/**
 * Outcome of the certificate check.
 *
 * `passed` — all three validity conditions are UNSAT; the proven verdict is
 * certified independently of the Fixedpoint engine.
 * `failed` — a validity condition was not UNSAT; `detail` carries the solver
 * status and, when the solver produced a model, a witness marking.
 * `unavailable` — the check could not run (missing/unparseable answer, solver
 * error), so no VC is implicated.
 *
 * The caller must withhold PROVEN on `failed` and `unavailable` alike.
 */
export type CertificateCheckOutcome =
  | { readonly type: 'passed'; readonly invariant: string }
  | {
      readonly type: 'failed';
      readonly vc: CertificateVc;
      readonly detail: string;
      readonly invariant: string;
    }
  | { readonly type: 'unavailable'; readonly reason: string; readonly invariant: string | null };

/**
 * Re-validates the IC3 certificate for a proven flat-encoding verdict.
 *
 * @param ctx the Z3 high-level context the answer was produced in
 * @param answer the raw `fp.getAnswer()` AST (null when Z3 produced none)
 * @param flatNet the flat net the CHC query was encoded from
 * @param initialMarking the verified initial marking (VC1)
 * @param property the verified property (VC3)
 * @param invariants the exactly-validated P-invariants the CHC bodies were
 *   strengthened with; conjoined into the CANDIDATE certificate and re-proven
 *   by the three VCs (never conjoined into the step relation)
 * @param sinkPlaces declared sink places (deadlock-freedom VC3)
 * @param timeoutMs per-VC solver timeout in milliseconds
 */
export async function checkCertificate(
  ctx: Z3Context,
  answer: Expr | null,
  flatNet: FlatNet,
  initialMarking: MarkingState,
  property: SmtProperty,
  invariants: readonly PInvariant[],
  sinkPlaces: ReadonlySet<Place<any>>,
  timeoutMs: number,
): Promise<CertificateCheckOutcome> {
  try {
    if (answer == null) {
      return {
        type: 'unavailable',
        reason: 'invariant missing (Z3 produced no inductive-invariant answer)',
        invariant: null,
      };
    }

    const P = flatNet.places.length;
    const Int = ctx.Int;
    const mVars: Arith[] = [];
    const mPrimeVars: Arith[] = [];
    for (let i = 0; i < P; i++) {
      mVars.push(Int.const(`m${i}`));
      mPrimeVars.push(Int.const(`mp${i}`));
    }

    const invariant = extractInvariant(ctx, answer, P, mVars);
    if (invariant == null) {
      return {
        type: 'unavailable',
        reason: 'invariant unparseable (no Reachable definition recognized in the Z3 answer)',
        invariant: String(answer),
      };
    }

    // Candidate R' := I ∧ P-invariant equalities — the strengthening is part of
    // the candidate, never of the step relation, and is re-proven by the three
    // VCs from scratch (see module doc).
    const candidate: Bool = invariants.length > 0
      ? ctx.And(invariant, encodeInvariantConstraints(ctx, invariants, mVars, P))
      : invariant;

    const failure = await validateCandidate(
      ctx, candidate, flatNet, initialMarking, property, sinkPlaces, timeoutMs, mVars, mPrimeVars,
    );
    if (failure == null) {
      return { type: 'passed', invariant: String(candidate) };
    }

    return { type: 'failed', vc: failure.vc, detail: failure.detail, invariant: String(candidate) };
  } catch (e: any) {
    return {
      type: 'unavailable',
      reason: `certificate check error: ${e?.message ?? e}`,
      invariant: null,
    };
  }
}

/** A validity condition that was not UNSAT, with the solver's account of why. */
interface VcFailure {
  readonly vc: CertificateVc;
  /** e.g. `solver returned SATISFIABLE (witness: A=2, B=1)`. */
  readonly detail: string;
}

/**
 * Runs the three validity conditions for one candidate certificate against the
 * unstrengthened step relation. Returns null when all three are UNSAT, else
 * the first failing condition.
 */
async function validateCandidate(
  ctx: Z3Context,
  candidate: Bool,
  flatNet: FlatNet,
  initialMarking: MarkingState,
  property: SmtProperty,
  sinkPlaces: ReadonlySet<Place<any>>,
  timeoutMs: number,
  mVars: Arith[],
  mPrimeVars: Arith[],
): Promise<VcFailure | null> {
  const P = flatNet.places.length;
  const Int = ctx.Int;

  // Domain constraint for VC2/VC3: the system never leaves ℕ^P (see module doc).
  let nonNegM: Bool = ctx.Bool.val(true);
  for (let i = 0; i < P; i++) {
    nonNegM = ctx.And(nonNegM, mVars[i]!.ge(0));
  }

  // === VC1 (init): ¬I(M₀) must be UNSAT ===
  const initPairs: [Expr, Expr][] = mVars.map((v, i) => [
    v as Expr,
    Int.val(initialMarking.tokens(flatNet.places[i]!)) as Expr,
  ]);
  const candidateAtInit = ctx.substitute(candidate, ...initPairs);
  const vc1 = await checkUnsat(ctx, flatNet, mVars, timeoutMs, 'initiation (VC1)', [ctx.Not(candidateAtInit)]);
  if (vc1 != null) return vc1;

  // === VC2 (consecution): I(M) ∧ M ≥ 0 ∧ T(M,M') ∧ ¬I(M') must be UNSAT ===
  const primePairs: [Expr, Expr][] = mVars.map((v, i) => [v as Expr, mPrimeVars[i]! as Expr]);
  const candidatePrime = ctx.substitute(candidate, ...primePairs);
  const step = encodeStepRelation(ctx, flatNet, mVars, mPrimeVars);
  const vc2 = await checkUnsat(ctx, flatNet, mVars, timeoutMs, 'consecution (VC2)',
    [candidate, nonNegM, step, ctx.Not(candidatePrime)]);
  if (vc2 != null) return vc2;

  // === VC3 (safety): I(M) ∧ M ≥ 0 ∧ Bad(M) must be UNSAT ===
  const bad = encodePropertyViolation(ctx, flatNet, property, sinkPlaces, mVars, P);
  const vc3 = await checkUnsat(ctx, flatNet, mVars, timeoutMs, 'safety (VC3)', [candidate, nonNegM, bad]);
  if (vc3 != null) return vc3;

  return null;
}

/**
 * Extracts `I(mVars)` from the Fixedpoint answer: finds the conjunct defining
 * `Reachable` and substitutes its bound (or ground) arguments with the marking
 * constants. Returns null when no recognizable definition is present.
 */
function extractInvariant(ctx: Z3Context, answer: Expr, P: number, mVars: Arith[]): Bool | null {
  for (const conjunct of topLevelConjuncts(ctx, answer)) {
    const invariant = tryExtractDefinition(ctx, conjunct, P, mVars);
    if (invariant != null) return invariant;
  }
  return null;
}

/** Top-level `and` children, or the expression itself when it is not an `and`. */
function topLevelConjuncts(ctx: Z3Context, expr: Expr): Expr[] {
  if (!ctx.isQuantifier(expr) && ctx.isApp(expr) && String((expr as any).decl().name()) === 'and') {
    const out: Expr[] = [];
    const n = (expr as any).numArgs();
    for (let i = 0; i < n; i++) out.push((expr as any).arg(i));
    return out;
  }
  return [expr];
}

/**
 * Attempts to read one conjunct as a `Reachable` definition and returns the
 * defining formula over `mVars`. Handles the `forall`-quantified shape (de
 * Bruijn arguments, any order) and the ground (unquantified) shape.
 */
function tryExtractDefinition(ctx: Z3Context, expr: Expr, P: number, mVars: Arith[]): Bool | null {
  if (ctx.isQuantifier(expr) && (expr as any).is_forall()) {
    const q: any = expr;
    const parts = splitDefinition(ctx, q.body(), P);
    if (parts == null) return null;

    // Argument position j of the Reachable application names place j; its de
    // Bruijn index tells substituteVars which slot to fill with mVars[j].
    const numVars: number = q.num_vars();
    const to: (Expr | undefined)[] = new Array(numVars);
    for (let j = 0; j < P; j++) {
      const arg = parts.app.arg(j);
      if (!ctx.isVar(arg)) return null;
      const idx = ctx.getVarIndex(arg);
      if (idx >= numVars || to[idx] != null) return null;
      to[idx] = mVars[j] as Expr;
    }
    // Bound variables not used as Reachable arguments (none in practice) are
    // kept free under a fresh constant so substituteVars gets a full mapping.
    for (let i = 0; i < numVars; i++) {
      if (to[i] == null) to[i] = ctx.Int.const(`certFree${i}`) as Expr;
    }
    return ctx.substituteVars(parts.phi, ...to);
  }

  // Ground shape: Reachable(args) = φ with unquantified arguments.
  const parts = splitDefinition(ctx, expr, P);
  if (parts == null) return null;
  const pairs: [Expr, Expr][] = [];
  for (let j = 0; j < P; j++) {
    const arg = parts.app.arg(j);
    if (ctx.isVar(arg)) return null;
    pairs.push([arg as Expr, mVars[j]! as Expr]);
  }
  if (pairs.length === 0) return parts.phi as Bool;
  return ctx.substitute(parts.phi, ...pairs);
}

/**
 * Splits a definition node into the `Reachable` application and the defining
 * formula. Accepts `=`/`iff` with `Reachable` on either side and
 * `Reachable(...) => φ` (φ then over-approximates `Reachable`, which is
 * exactly what a certificate must do); rejects `φ => Reachable(...)`, which
 * only under-approximates.
 */
function splitDefinition(ctx: Z3Context, body: Expr, P: number): { app: any; phi: Expr } | null {
  if (ctx.isQuantifier(body) || !ctx.isApp(body)) return null;
  const b: any = body;
  const decl = String(b.decl().name());
  if ((decl === '=' || decl === 'iff') && b.numArgs() === 2) {
    if (isReachableApp(ctx, b.arg(0), P)) return { app: b.arg(0), phi: b.arg(1) };
    if (isReachableApp(ctx, b.arg(1), P)) return { app: b.arg(1), phi: b.arg(0) };
    return null;
  }
  if (decl === '=>' && b.numArgs() === 2 && isReachableApp(ctx, b.arg(0), P)) {
    return { app: b.arg(0), phi: b.arg(1) };
  }
  return null;
}

function isReachableApp(ctx: Z3Context, expr: Expr, P: number): boolean {
  return ctx.isApp(expr)
    && String((expr as any).decl().name()) === 'Reachable'
    && (expr as any).numArgs() === P;
}

/**
 * Runs one validity condition on a fresh plain solver. Returns null when it is
 * UNSAT (the condition holds), else the failure with the solver's status and —
 * for SAT — the marking that witnesses it.
 */
async function checkUnsat(
  ctx: Z3Context,
  flatNet: FlatNet,
  mVars: Arith[],
  timeoutMs: number,
  vc: CertificateVc,
  assertions: readonly Bool[],
): Promise<VcFailure | null> {
  const solver = new ctx.Solver();
  if (timeoutMs > 0) {
    solver.set('timeout', Math.min(timeoutMs, 2147483647));
  }
  for (const assertion of assertions) {
    solver.add(assertion);
  }
  const status = await solver.check();
  if (status === 'unsat') return null;

  if (status === 'sat') {
    const witness = describeWitness(solver, flatNet, mVars);
    return {
      vc,
      detail: `solver returned SATISFIABLE${witness == null ? '' : ` (witness: ${witness})`}`,
    };
  }
  let why: string | null = null;
  try {
    why = String(solver.reasonUnknown());
  } catch {
    // Reason not available; the plain status is enough.
  }
  return { vc, detail: `solver returned UNKNOWN${why == null || why === '' ? '' : ` (${why})`}` };
}

/** Compact `place=count` witness from a SAT model; null when unavailable. */
function describeWitness(solver: any, flatNet: FlatNet, mVars: Arith[]): string | null {
  try {
    const model = solver.model();
    const parts: string[] = [];
    let length = 0;
    for (let i = 0; i < mVars.length; i++) {
      const value = model.eval(mVars[i]!, false);
      // Uninterpreted vars evaluate back to themselves; keep numerals only
      // (Z3 renders a negative one as `(- 5)`).
      const text = value == null ? '' : String(value);
      if (!/^(-?\d+|\(- \d+\))$/.test(text)) continue;
      const part = `${flatNet.places[i]!.name}=${text}`;
      parts.push(part);
      length += part.length + 2;
      if (length > 160) {
        parts.push('...');
        break;
      }
    }
    return parts.length === 0 ? null : parts.join(', ');
  } catch {
    return null;
  }
}
