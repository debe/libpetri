/**
 * @module p-invariant-computer
 *
 * Computes P-invariants of a Petri net via integer Gaussian elimination (Farkas' algorithm).
 *
 * **Algorithm**: A P-invariant is a non-negative integer vector y such that y^T · C = 0
 * (where C is the incidence matrix). This expresses a conservation law: the weighted
 * token sum Σ(y_i · M[i]) is constant across all reachable markings.
 *
 * **Farkas variant**: Constructs the augmented matrix [C^T | I_P] and row-reduces
 * the C^T portion to zero using integer elimination (no floating point). Rows where
 * the C^T part becomes all-zero yield invariant vectors from the identity part.
 * Row normalization by GCD keeps values small during elimination.
 *
 * **Integer Gaussian elimination**: Each elimination step multiplies rows by pivot
 * coefficients (a·row - b·pivotRow) to avoid fractions. This preserves integer
 * arithmetic throughout, critical for exact invariant computation.
 *
 * Invariants are used to strengthen SMT queries (added as constraints on M').
 */
import type { FlatNet } from '../encoding/flat-net.js';
import type { IncidenceMatrix } from '../encoding/incidence-matrix.js';
import type { MarkingState } from '../marking-state.js';
import type { PInvariant } from './p-invariant.js';
import { pInvariant } from './p-invariant.js';

/**
 * Computes P-invariants of a Petri net via integer Gaussian elimination.
 *
 * P-invariants are non-negative integer vectors y where y^T * C = 0.
 * They express conservation laws: the weighted token sum is constant
 * across all reachable markings.
 *
 * Algorithm: compute the null space of C^T using integer row reduction
 * with an augmented identity matrix (Farkas' algorithm variant).
 */
export function computePInvariants(
  matrix: IncidenceMatrix,
  flatNet: FlatNet,
  initialMarking: MarkingState,
): PInvariant[] {
  const P = matrix.numPlaces();
  const T = matrix.numTransitions();

  if (P === 0 || T === 0) return [];

  // We want to find y such that y^T * C = 0, i.e., C^T * y = 0
  // Start with augmented matrix [C^T | I_P]
  // Row-reduce C^T part to zero; the I_P part gives the invariant vectors.
  const ct = matrix.transposedIncidence(); // P × T

  // Augmented matrix: P rows, T + P columns
  // Use regular numbers (safe for nets with < ~50 places/transitions)
  const cols = T + P;
  const augmented: number[][] = [];
  for (let i = 0; i < P; i++) {
    const row = new Array<number>(cols).fill(0);
    for (let j = 0; j < T; j++) {
      row[j] = ct[i]![j]!;
    }
    row[T + i] = 1; // identity part
    augmented.push(row);
  }

  // Integer Gaussian elimination on the C^T part (columns 0..T-1)
  let pivotRow = 0;
  for (let col = 0; col < T && pivotRow < P; col++) {
    // Find pivot (non-zero entry in this column)
    let pivot = -1;
    for (let row = pivotRow; row < P; row++) {
      if (augmented[row]![col] !== 0) {
        pivot = row;
        break;
      }
    }
    if (pivot === -1) continue; // free variable

    // Swap pivot row
    if (pivot !== pivotRow) {
      const tmp = augmented[pivotRow]!;
      augmented[pivotRow] = augmented[pivot]!;
      augmented[pivot] = tmp;
    }

    // Eliminate this column in all other rows
    for (let row = 0; row < P; row++) {
      if (row === pivotRow || augmented[row]![col] === 0) continue;

      const a = augmented[pivotRow]![col]!;
      const b = augmented[row]![col]!;

      // row = a*row - b*pivotRow (keeps integers, eliminates col)
      for (let c = 0; c < cols; c++) {
        augmented[row]![c] = a * augmented[row]![c]! - b * augmented[pivotRow]![c]!;
      }

      // Normalize by GCD to keep values small
      normalizeRow(augmented[row]!, cols);
    }

    pivotRow++;
  }

  // Extract invariants: rows where C^T part is all zeros
  const invariants: PInvariant[] = [];
  for (let row = 0; row < P; row++) {
    let isZero = true;
    for (let col = 0; col < T; col++) {
      if (augmented[row]![col] !== 0) {
        isZero = false;
        break;
      }
    }
    if (!isZero) continue;

    // Extract the weight vector from the identity part
    const weights = new Array<number>(P);
    let allNonNegative = true;
    let hasPositive = false;

    for (let i = 0; i < P; i++) {
      weights[i] = augmented[row]![T + i]!;
      if (weights[i]! < 0) {
        allNonNegative = false;
        break;
      }
      if (weights[i]! > 0) hasPositive = true;
    }

    // We want semi-positive invariants (all weights >= 0, at least one > 0)
    if (!allNonNegative) {
      // Try negating
      let allNonPositive = true;
      for (let i = 0; i < P; i++) {
        if (augmented[row]![T + i]! > 0) {
          allNonPositive = false;
          break;
        }
      }
      if (allNonPositive) {
        for (let i = 0; i < P; i++) {
          weights[i] = -augmented[row]![T + i]!;
        }
        hasPositive = true;
        allNonNegative = true;
      }
    }

    if (!allNonNegative || !hasPositive) continue;

    // Normalize: divide by GCD of weights
    let g = 0;
    for (const w of weights) {
      if (w > 0) g = gcd(g, w);
    }
    if (g > 1) {
      for (let i = 0; i < P; i++) {
        weights[i] = weights[i]! / g;
      }
    }

    // Compute support and constant
    const support = new Set<number>();
    let constant = 0;
    for (let i = 0; i < P; i++) {
      if (weights[i] !== 0) {
        support.add(i);
        const place = flatNet.places[i]!;
        constant += weights[i]! * initialMarking.tokens(place);
      }
    }

    invariants.push(pInvariant(weights, constant, support));
  }

  return invariants;
}

/** An invariant rejected by {@link validateInvariantsExact}, with the reason it failed. */
export interface DroppedInvariant {
  readonly invariant: PInvariant;
  readonly reason: string;
}

/** Result of {@link validateInvariantsExact}: exact-verified invariants plus the rejects. */
export interface InvariantValidationResult {
  readonly valid: readonly PInvariant[];
  readonly dropped: readonly DroppedInvariant[];
}

/**
 * Re-verifies each computed P-invariant **exactly** (BigInt) and drops any that fails.
 *
 * {@link computePInvariants} runs its integer Gaussian elimination in f64 `number`
 * with no overflow guard, and the encoder conjoins each invariant into the CHC
 * transition-rule *body*: a numerically wrong invariant therefore removes reachable
 * successors and can certify a false `Proven`. This pass must run between
 * computation and use, so nothing imprecise ever reaches the encoder — mirroring
 * the defensive style of {@link computePSemiflows}, which drops rows rather than
 * keep imprecise ones.
 *
 * Checks per invariant `y`:
 * - every weight and the constant is a safe integer (`Number.isSafeInteger`),
 * - **H1 linearity** (when `flatNet` is given): `y` is zero on every place with
 *   non-linear consumption — see below,
 * - `y·C = 0` exactly, per transition column of the incidence matrix (BigInt),
 * - when `flatNet` and `initialMarking` are given, the stored constant equals
 *   the exactly recomputed `y·M0`.
 *
 * **H1 linearity guard** (`lean/Libpetri/Strengthening.lean`,
 * `consume_all_hypothesis_is_necessary`): the incidence matrix *linearizes*
 * consumption — its column is `post − pre` with `pre = requiredCount`, so it says
 * nothing about consume-all or reset semantics, where the encoder's fire relation
 * sets `m'_i = post[i]` and erases however many tokens the place actually held.
 * `y·C = 0` is therefore necessary but NOT sufficient: an invariant weighting such
 * a place can pass the exact gate yet be false on the real net, and conjoined into
 * the CHC rule bodies it prunes genuine successors (false PROVEN). Per the Lean
 * theorem's H1 hypothesis, any invariant with a nonzero weight on a place that is,
 * for any flat transition, a consume-all input place (`all` **and** `at-least` —
 * `atLeast(n)` waits for n but then consumes ALL available, see
 * `consumptionCount` in `core/in.ts`; the linear cardinalities are
 * `one`/`exactly(n)`) or a reset place is dropped here. Env-injectable places need
 * no guard of their own: their injector columns ({@link IncidenceMatrix.from})
 * already force `y = 0` there through the `y·C = 0` check — Strengthening.lean's
 * H3′ sufficiency result (`invariant_strengthening_sound_inj`).
 *
 * Dropping a *valid* conservation law only weakens the encoder's strengthening
 * lemmas (sound); keeping an invalid one is what must never happen.
 */
export function validateInvariantsExact(
  matrix: IncidenceMatrix,
  invariants: readonly PInvariant[],
  flatNet?: FlatNet,
  initialMarking?: MarkingState,
): InvariantValidationResult {
  const nonlinear = flatNet == null ? null : nonlinearPlaces(flatNet);
  const valid: PInvariant[] = [];
  const dropped: DroppedInvariant[] = [];
  for (const inv of invariants) {
    const reason = exactCheckFailure(matrix, inv, nonlinear, flatNet, initialMarking);
    if (reason === null) {
      valid.push(inv);
    } else {
      dropped.push({ invariant: inv, reason });
    }
  }
  return { valid, dropped };
}

/**
 * Place indices with non-linear consumption on some flat transition — the
 * reset/consume-all arms of H1. The matrix may carry extra injector columns beyond
 * `flatNet.transitions`; injections are linear (`+e_p`) and need no entry here.
 */
function nonlinearPlaces(flatNet: FlatNet): ReadonlySet<number> {
  const nonlinear = new Set<number>();
  for (const ft of flatNet.transitions) {
    for (let p = 0; p < ft.consumeAll.length; p++) {
      if (ft.consumeAll[p]) nonlinear.add(p);
    }
    for (const p of ft.resetPlaces) nonlinear.add(p);
  }
  return nonlinear;
}

/** Returns why `inv` fails the exact re-check, or null when it passes. */
function exactCheckFailure(
  matrix: IncidenceMatrix,
  inv: PInvariant,
  nonlinear: ReadonlySet<number> | null,
  flatNet?: FlatNet,
  initialMarking?: MarkingState,
): string | null {
  const P = matrix.numPlaces();
  const T = matrix.numTransitions();

  if (inv.weights.length !== P) {
    return `weight vector has ${inv.weights.length} entries, expected ${P}`;
  }
  for (let p = 0; p < P; p++) {
    if (!Number.isSafeInteger(inv.weights[p]!)) {
      return `weight ${inv.weights[p]} for place ${p} is outside the safe-integer range`;
    }
  }
  if (!Number.isSafeInteger(inv.constant)) {
    return `constant ${inv.constant} is outside the safe-integer range`;
  }

  // H1 linearity guard (see the {@link validateInvariantsExact} doc): a nonzero
  // weight on a consume-all or reset place makes the linearized column a lie about
  // the real firing, so the y·C = 0 check below would not certify conservation.
  if (nonlinear !== null) {
    for (let p = 0; p < inv.weights.length; p++) {
      if (inv.weights[p] !== 0 && nonlinear.has(p)) {
        const name = flatNet?.places[p]?.name ?? `#${p}`;
        return (
          `support intersects consume-all/reset place '${name}' ` +
          `(non-linear consumption; see Strengthening.lean H1)`
        );
      }
    }
  }

  // y·C = 0, re-derived in BigInt from the incidence matrix (immune to f64 rounding).
  const y: bigint[] = inv.weights.map((w) => BigInt(w));
  const incidence = matrix.incidence(); // [t][p]
  for (let t = 0; t < T; t++) {
    const row = incidence[t]!;
    let dot = 0n;
    for (let p = 0; p < P; p++) {
      if (y[p] === 0n) continue;
      if (!Number.isSafeInteger(row[p]!)) {
        return `incidence entry ${row[p]} at [t=${t}][p=${p}] is outside the safe-integer range`;
      }
      dot += y[p]! * BigInt(row[p]!);
    }
    if (dot !== 0n) {
      return `y·C is ${dot} (not 0) at transition column ${t}`;
    }
  }

  // Constant = y·M0, recomputed exactly.
  if (flatNet != null && initialMarking != null) {
    let exact = 0n;
    for (let p = 0; p < P; p++) {
      if (y[p] === 0n) continue;
      const tokens = initialMarking.tokens(flatNet.places[p]!);
      if (!Number.isSafeInteger(tokens)) {
        return `initial marking of place ${p} (${tokens}) is outside the safe-integer range`;
      }
      exact += y[p]! * BigInt(tokens);
    }
    if (exact !== BigInt(inv.constant)) {
      return `constant ${inv.constant} does not match the exact y·M0 = ${exact}`;
    }
  }

  return null;
}

/**
 * A P-semiflow generator row during Colom–Silva elimination: the running
 * transition signature `y·C` plus the non-negative place weight `y` that produced
 * it. A row survives an elimination step only when the current column of `y·C` is
 * zero, so after every transition is eliminated the surviving rows have `y·C = 0`.
 */
interface SemiflowRow {
  readonly sig: number[];
  readonly weight: number[];
}

/**
 * Computes minimal **P-semiflows** — non-negative place weightings `y` with
 * `y·C = 0` — via the Colom–Silva / Farkas method. Unlike {@link computePInvariants}
 * (a signed null-space basis), every returned `PInvariant.weights` is non-negative:
 * a genuine P-semiflow, with `constant = y·M0`. A non-negative conservation law
 * soundly **bounds** the token sum over its support: `Σ_{support} M(p) ≤ y·M0`. Used
 * to bound the number of simultaneously-live colours in the name-coloured encoder
 * (see `colourSlotBound`).
 *
 * Mirrors the Rust reference `compute_p_semiflows`.
 */
export function computePSemiflows(
  matrix: IncidenceMatrix,
  flatNet: FlatNet,
  initialMarking: MarkingState,
): PInvariant[] {
  const np = matrix.numPlaces();
  const nt = matrix.numTransitions();
  if (np === 0) return [];

  const incidence = matrix.incidence(); // [t][p]

  // One generator row per place: signature = the place's column of C (over
  // transitions), weight = e_p. Eliminate one transition column at a time using only
  // non-negative combinations, so accumulated weights stay non-negative.
  let rows: SemiflowRow[] = [];
  for (let p = 0; p < np; p++) {
    const sig = new Array<number>(nt);
    for (let t = 0; t < nt; t++) sig[t] = incidence[t]![p]!;
    const weight = new Array<number>(np).fill(0);
    weight[p] = 1;
    rows.push({ sig, weight });
  }

  for (let t = 0; t < nt; t++) {
    const next: SemiflowRow[] = rows.filter((r) => r.sig[t] === 0);
    const pos = rows.filter((r) => r.sig[t]! > 0);
    const neg = rows.filter((r) => r.sig[t]! < 0);
    for (const rp of pos) {
      for (const rn of neg) {
        const cp = -rn.sig[t]!; // > 0
        const cn = rp.sig[t]!; // > 0
        // Checked combination: `number` is f64 and loses integer precision above 2^53,
        // so DROP this generator if any coefficient leaves the safe-integer range rather
        // than keep an imprecise (invalid) row. colourSlotBound then falls back to the
        // sound over-approximation — never an under-approximation.
        const sig = combineRow(cp, rp.sig, cn, rn.sig);
        const weight = combineRow(cp, rp.weight, cn, rn.weight);
        if (sig === null || weight === null) continue;
        reduceGcd(sig, weight);
        next.push({ sig, weight });
      }
    }
    rows = keepSupportMinimal(next);
    if (rows.length > 8192) rows.length = 8192; // safety backstop against blow-up
  }

  const semiflows: PInvariant[] = [];
  for (const { weight } of rows) {
    if (!weight.some((x) => x !== 0)) continue;
    const support = new Set<number>();
    let constant = 0;
    for (let p = 0; p < np; p++) {
      if (weight[p] !== 0) {
        support.add(p);
        constant += weight[p]! * initialMarking.tokens(flatNet.places[p]!);
      }
    }
    // Drop a semiflow whose `Σ weight·M0` left the safe-integer range — fewer covering
    // semiflows just means colourSlotBound falls back soundly.
    if (!Number.isSafeInteger(constant)) continue;
    semiflows.push(pInvariant(weight, constant, support));
  }
  return semiflows;
}

/**
 * Divides a generator row's signature and weight by the GCD of all their absolute
 * values (keeps the P-semiflow minimal and the integers small). Mutates in place.
 */
/**
 * `cp*a + cn*b` componentwise, or null if any result leaves the safe-integer range
 * (`number` is f64 and loses integer precision above 2^53) — the caller then drops the
 * generator and the colour bound falls back soundly rather than using imprecise values.
 */
function combineRow(
  cp: number,
  a: readonly number[],
  cn: number,
  b: readonly number[],
): number[] | null {
  const out = new Array<number>(a.length);
  for (let i = 0; i < a.length; i++) {
    const v = cp * a[i]! + cn * b[i]!;
    if (!Number.isSafeInteger(v)) return null;
    out[i] = v;
  }
  return out;
}

function reduceGcd(sig: number[], weight: number[]): void {
  let g = 0;
  for (const v of sig) g = gcd(g, Math.abs(v));
  for (const v of weight) g = gcd(g, Math.abs(v));
  if (g > 1) {
    for (let i = 0; i < sig.length; i++) sig[i] = sig[i]! / g;
    for (let i = 0; i < weight.length; i++) weight[i] = weight[i]! / g;
  }
}

/**
 * Drops any row whose weight-support is a strict superset of another's — a
 * non-minimal combination only inflates the set (and can cause combinatorial
 * blow-up). Mirrors the Rust reference `keep_support_minimal`.
 */
function keepSupportMinimal(rows: SemiflowRow[]): SemiflowRow[] {
  const supports: number[][] = rows.map((r) => {
    const s: number[] = [];
    for (let i = 0; i < r.weight.length; i++) if (r.weight[i] !== 0) s.push(i);
    return s;
  });
  const keep = new Array<boolean>(rows.length).fill(true);
  for (let i = 0; i < rows.length; i++) {
    if (!keep[i]) continue;
    for (let j = 0; j < rows.length; j++) {
      if (i === j || !keep[j]) continue;
      if (supports[j]!.length < supports[i]!.length && supports[j]!.every((p) => supports[i]!.includes(p))) {
        keep[i] = false;
        break;
      }
    }
  }
  return rows.filter((_, i) => keep[i]);
}

/**
 * Checks if every place is covered by at least one P-invariant.
 * If true, the net is structurally bounded.
 */
export function isCoveredByInvariants(invariants: readonly PInvariant[], numPlaces: number): boolean {
  const covered = new Array<boolean>(numPlaces).fill(false);
  for (const inv of invariants) {
    for (const idx of inv.support) {
      if (idx < numPlaces) covered[idx] = true;
    }
  }
  return covered.every(c => c);
}

function normalizeRow(row: number[], cols: number): void {
  let g = 0;
  for (let c = 0; c < cols; c++) {
    if (row[c] !== 0) {
      g = gcd(g, Math.abs(row[c]!));
    }
  }
  if (g > 1) {
    for (let c = 0; c < cols; c++) {
      row[c] = row[c]! / g;
    }
  }
}

function gcd(a: number, b: number): number {
  while (b !== 0) {
    const t = b;
    b = a % b;
    a = t;
  }
  return a;
}
