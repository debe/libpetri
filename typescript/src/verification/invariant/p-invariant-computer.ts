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
