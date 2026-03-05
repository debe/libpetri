const EPSILON = 1e-9;

/**
 * Difference Bound Matrix (DBM) for Time Petri Net state class analysis.
 *
 * Implements the Berthomieu-Diaz (1991) algorithm for computing firing domains
 * and their successors. Matrix bounds[i][j] = upper bound on (xi - xj).
 * Index 0 is the reference clock; index i+1 is the clock for transition i.
 */
export class DBM {
  private readonly bounds: Float64Array;
  private readonly dim: number;
  readonly clockNames: readonly string[];
  private readonly _empty: boolean;

  private constructor(bounds: Float64Array, dim: number, clockNames: readonly string[], empty: boolean) {
    this.bounds = bounds;
    this.dim = dim;
    this.clockNames = clockNames;
    this._empty = empty;
  }

  /** Creates an initial firing domain for enabled transitions. */
  static create(clockNames: readonly string[], lowerBounds: number[], upperBounds: number[]): DBM {
    const n = clockNames.length;
    const dim = n + 1;
    const bounds = makeMatrix(dim, Infinity);

    for (let i = 0; i < n; i++) {
      bounds[(0) * dim + (i + 1)] = -lowerBounds[i]!;
      bounds[(i + 1) * dim + (0)] = upperBounds[i]!;
    }

    return new DBM(bounds, dim, clockNames, false).canonicalize();
  }

  /** Creates an empty (unsatisfiable) zone. */
  static empty(clockNames: readonly string[]): DBM {
    const b = new Float64Array(1);
    b[0] = 0;
    return new DBM(b, 1, clockNames, true);
  }

  isEmpty(): boolean {
    return this._empty;
  }

  clockCount(): number {
    return this.clockNames.length;
  }

  private get(i: number, j: number): number {
    return this.bounds[i * this.dim + j]!;
  }

  /** Gets the lower bound (earliest firing time) for clock i. */
  getLowerBound(clockIndex: number): number {
    if (this._empty || clockIndex < 0 || clockIndex >= this.clockNames.length) return 0;
    const val = -this.get(0, clockIndex + 1);
    return val === 0 ? 0 : val; // normalize -0 to 0
  }

  /** Gets the upper bound (latest firing time / deadline) for clock i. */
  getUpperBound(clockIndex: number): number {
    if (this._empty || clockIndex < 0 || clockIndex >= this.clockNames.length) return Infinity;
    return this.get(clockIndex + 1, 0);
  }

  /** Checks if transition can fire (lower bound <= 0 after time passage). */
  canFire(clockIndex: number): boolean {
    return !this._empty && this.getLowerBound(clockIndex) <= EPSILON;
  }

  /**
   * Computes the successor firing domain after firing transition t_f.
   * Implements the 5-step Berthomieu-Diaz successor formula.
   */
  fireTransition(
    firedClock: number,
    newClockNames: readonly string[],
    newLowerBounds: number[],
    newUpperBounds: number[],
    persistentClocks: number[],
  ): DBM {
    if (this._empty) return this;

    const n = this.clockNames.length;
    if (firedClock < 0 || firedClock >= n) {
      throw new Error(`Invalid fired clock index: ${firedClock}`);
    }

    // Step 1: Intersect with "t_f fires first" constraint
    const constrained = new Float64Array(this.bounds);
    const dim = this.dim;
    const f = firedClock + 1;

    for (let i = 0; i < n; i++) {
      if (i !== firedClock) {
        const idx = i + 1;
        const pos = f * dim + idx;
        constrained[pos] = Math.min(constrained[pos]!, 0);
      }
    }

    // Step 2: Canonicalize
    if (!canonicalizeInPlace(constrained, dim)) {
      return DBM.empty([]);
    }

    // Steps 3 & 4: Substitution and Elimination
    const newN = persistentClocks.length + newClockNames.length;
    const newDim = newN + 1;
    const newBounds = makeMatrix(newDim, Infinity);

    // Copy persistent clocks with transformed bounds
    for (let pi = 0; pi < persistentClocks.length; pi++) {
      const oldIdx = persistentClocks[pi]! + 1;
      const newIdx = pi + 1;

      const upper = constrained[oldIdx * dim + f]!;
      const lower = Math.max(0, -constrained[f * dim + oldIdx]!);

      newBounds[0 * newDim + newIdx] = -lower;
      newBounds[newIdx * newDim + 0] = upper;

      // Inter-clock constraints between persistent transitions (preserved)
      for (let pj = 0; pj < persistentClocks.length; pj++) {
        const oldJ = persistentClocks[pj]! + 1;
        const newJ = pj + 1;
        newBounds[newIdx * newDim + newJ] = constrained[oldIdx * dim + oldJ]!;
      }
    }

    // Step 5: Add fresh intervals for newly enabled transitions
    const offset = persistentClocks.length;
    for (let k = 0; k < newClockNames.length; k++) {
      const idx = offset + k + 1;
      newBounds[0 * newDim + idx] = -newLowerBounds[k]!;
      newBounds[idx * newDim + 0] = newUpperBounds[k]!;
    }

    // Build new clock names
    const allNames: string[] = [];
    for (const idx of persistentClocks) {
      allNames.push(this.clockNames[idx]!);
    }
    allNames.push(...newClockNames);

    // Step 6: Final canonicalization
    return new DBM(newBounds, newDim, allNames, false).canonicalize();
  }

  /** Lets time pass: set all lower bounds to 0. */
  letTimePass(): DBM {
    if (this._empty) return this;

    const newBounds = new Float64Array(this.bounds);
    for (let i = 1; i < this.dim; i++) {
      newBounds[0 * this.dim + i] = 0;
    }

    return new DBM(newBounds, this.dim, this.clockNames, false).canonicalize();
  }

  private canonicalize(): DBM {
    if (this._empty) return this;

    const canon = new Float64Array(this.bounds);
    if (!canonicalizeInPlace(canon, this.dim)) {
      return DBM.empty(this.clockNames);
    }
    return new DBM(canon, this.dim, this.clockNames, false);
  }

  equals(other: DBM): boolean {
    if (this === other) return true;
    if (this._empty && other._empty) return true;
    if (this._empty || other._empty) return false;
    if (this.clockNames.length !== other.clockNames.length) return false;
    for (let i = 0; i < this.clockNames.length; i++) {
      if (this.clockNames[i] !== other.clockNames[i]) return false;
    }
    if (this.bounds.length !== other.bounds.length) return false;
    for (let i = 0; i < this.bounds.length; i++) {
      if (Math.abs(this.bounds[i]! - other.bounds[i]!) > EPSILON) return false;
    }
    return true;
  }

  toString(): string {
    if (this._empty) return 'DBM[empty]';
    const parts: string[] = [];
    for (let i = 0; i < this.clockNames.length; i++) {
      const lo = formatBound(this.getLowerBound(i));
      const hi = formatBound(this.getUpperBound(i));
      parts.push(`${this.clockNames[i]}:[${lo},${hi}]`);
    }
    return `DBM{${parts.join(', ')}}`;
  }
}

function makeMatrix(dim: number, fill: number): Float64Array {
  const m = new Float64Array(dim * dim).fill(fill);
  for (let i = 0; i < dim; i++) {
    m[i * dim + i] = 0;
  }
  return m;
}

function canonicalizeInPlace(dbm: Float64Array, dim: number): boolean {
  for (let k = 0; k < dim; k++) {
    for (let i = 0; i < dim; i++) {
      for (let j = 0; j < dim; j++) {
        const ik = dbm[i * dim + k]!;
        const kj = dbm[k * dim + j]!;
        if (ik < Infinity && kj < Infinity) {
          const via = ik + kj;
          if (via < dbm[i * dim + j]!) {
            dbm[i * dim + j] = via;
          }
        }
      }
    }
  }
  for (let i = 0; i < dim; i++) {
    if (dbm[i * dim + i]! < -EPSILON) return false;
  }
  return true;
}

function formatBound(b: number): string {
  if (b >= Infinity / 2) return '\u221e';
  if (b === Math.trunc(b)) return String(b);
  return b.toFixed(3);
}
