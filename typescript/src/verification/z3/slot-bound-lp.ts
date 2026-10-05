/**
 * @module slot-bound-lp
 *
 * The colour-slot bound `k` of the name-coloured encoding ([NU-053]), as a linear program
 * solved in exact rational arithmetic, with no solver ([VER-013] AC1).
 *
 * `k` has to bound the number of names live at once. A name is live only while some
 * coloured place holds a token of it, so the live names never outnumber the tokens on the
 * coloured places. For any weighting `y` over the flat places with
 *
 * - `y ≥ 0`,
 * - `y_p ≥ 1` on every coloured place `p`,
 * - `y·N_r ≤ 0` for every flat row `r`, where `N_r = post_r − pre_r` is the row's column of
 *   the incidence matrix (a timeout outcome counts its deposit),
 *
 * every reachable marking has `Σ_{coloured} M ≤ y·M ≤ y·M0`. `k = ⌊opt⌋`, where `opt` is the
 * least `y·M0` over all such weightings. The optimum is unique, so every implementation
 * computes the same `k`. Equivalently (the dual), `opt` is the largest coloured token count
 * the state equation `M = M0 + N·σ ≥ 0`, `σ ≥ 0` admits over the reals. The program is
 * infeasible exactly when that count is unbounded: then nothing bounds the coloured tokens
 * structurally, and the plan is refused.
 *
 * **No H1.** A place a reset or consume-all arc clears keeps a free weight `y_p ≥ 0`. At an
 * enabled firing such a place ends at its deposit, which is at most `m_p − pre_p + post_p`
 * because enablement gives `pre_p ≤ m_p` (Lean `fireAD_le_linear`, `Novel/LinearBound.lean`),
 * and a non-negative weight keeps the inequality. The [VER-015] check `checkLinearBoundExact`
 * still pins such places to weight zero although its proof does not need it
 * (`linear_bound_sound_noH1`); the slot bound follows the proof. The difference is
 * deliberate. Inhibitor and read arcs do not enter the column: they only restrict
 * enablement.
 *
 * **Trust.** {@link solveSlotBound} is untrusted: it is not modelled in Lean, so editing it
 * needs no Lean re-verification. Its answer is a weighting scaled to integers
 * ({@link ScaledCover}). The plan uses `k` only through {@link checkedSlotBound}, which runs
 * {@link checkCover}: an exact re-check of the weighting against every flat row, which
 * computes `k = ⌊Y·M0 / D⌋` itself. Only the checker is modelled (`checkCover`,
 * `colourSlotBoundLP` in `lean/Libpetri/Novel/RouteA/SlotBound.lean`) and proved sufficient
 * for `coloured_simulates` (`buildPlan_premisesS`, `Plan.lean`).
 *
 * **The algorithm** is normative in full, so every implementation performs the same pivots
 * and returns the same weighting:
 *
 * 1. *Presolve.* `U` is the least set of places containing the coloured ones such that a row
 *    producing into `U` (`N_r[q] > 0` for some `q ∈ U`) has every place it consumes from
 *    (`N_r[p] < 0`) in `U`. The kept rows are the rows producing into `U`, in flat order,
 *    restricted to `U`; a kept row equal to an earlier one after the restriction is dropped.
 *    `U` is ordered ascending. The presolve does not change the optimum, and a presolve bug
 *    cannot make `k` unsound because the checker sees every flat row.
 * 2. *The dual, in standard form:* maximise `c·σ` subject to `A·σ + s = b`, `σ, s ≥ 0`, with
 *    one constraint row per place `U[i]` (`A[i][j] = pre − post` of kept row `j` at `U[i]`,
 *    `b_i = M0[U[i]] ≥ 0`) and `c_j` kept row `j`'s net production into the coloured places.
 *    Columns are the kept rows `0..m'` in order, then the slacks `m'..m'+n'` in the order of
 *    `U`. The slacks are the initial basis, feasible because `M0 ≥ 0`: no Phase I, no
 *    artificial variables, no big-M.
 * 3. *Bland's rule.* Entering: the smallest column with a negative objective-row entry.
 *    Leaving: the least ratio `rhs_i / a_ie` over rows with `a_ie > 0`, ties to the row whose
 *    basic column is smallest. No negative entry: optimal. No positive entry in the entering
 *    column: the dual is unbounded, so the program is infeasible.
 * 4. *The weighting.* With `π_i` the objective-row entry of slack column `m' + i`,
 *    `y_p = π_i + [p coloured]` for `p = U[i]` and `y_p = 0` off `U`. `D` is the least common
 *    multiple of the denominators of the `y_p` in lowest terms and `Y = y·D`.
 *
 * Limits, all functions of the presolved program and the pivot sequence, so every
 * implementation refuses the same nets, and together they bound the time of a solve whether
 * or not a total budget is set:
 *
 * - `too-large` past {@link SLOT_LP_MAX_PLACES} places or {@link SLOT_LP_MAX_ROWS} rows after
 *   the presolve, before any pivot.
 * - `work-limit` when the next pivot would take the work past {@link SLOT_LP_WORK_LIMIT}. The
 *   work of a pivot is the length of the pivot row `p`, plus `len(row) + p` for every row it
 *   updates (the other constraint rows with a non-zero entry in the entering column, and the
 *   objective row when it has one there), lengths counted in non-zero entries before the
 *   pivot, slacks included. The work of a solve is the sum over its pivots.
 * - `coefficient-limit` when a pivot leaves an entry of the tableau (a constraint row, its
 *   right-hand side, the objective row or its value) whose numerator or denominator in lowest
 *   terms exceeds `2^63 − 1` in absolute value. The initial tableau is held to the same limit.
 *
 * The solve calls its `stop` poll before every pivot ([VER-013]); the verifier passes a
 * deadline poll, which throws once the run must stop, and `encodeScripts` passes none. Each
 * round of the loop decides in this order: no entering column, optimal; no leaving row,
 * infeasible; the next pivot's work past the limit, work limit; a stop, stopped; otherwise
 * pivot, then the coefficient limit. A solve that ends without needing another pivot is
 * therefore never refused by the work limit.
 *
 * All arithmetic is exact, over `bigint`; no floating point is involved. Mirrors the Rust
 * reference `slot_bound_lp.rs`.
 */
import type { FlatNet } from '../encoding/flat-net.js';
import type { MarkingState } from '../marking-state.js';

/**
 * The largest colour-slot bound a plan may carry: the limit of Java's `int`, applied by every
 * implementation so that all three refuse the same nets (Lean `slotCap`).
 */
export const SLOT_CAP = 2_147_483_647n;

/** The most places the presolved program may have. */
export const SLOT_LP_MAX_PLACES = 4096;

/** The most rows (transitions) the presolved program may have. */
export const SLOT_LP_MAX_ROWS = 16384;

/**
 * The most work a solve may do, in entry updates (see the module documentation). A tenth of a
 * second on a sparse net, a few seconds at worst on a dense weighted one.
 */
export const SLOT_LP_WORK_LIMIT = 4_000_000;

/** The largest magnitude a tableau entry's numerator or denominator may reach: `2^63 − 1`. */
const COEFFICIENT_MAX = 2n ** 63n - 1n;

// ---- exact rationals ----

function gcd(a: bigint, b: bigint): bigint {
  if (a < 0n) a = -a;
  if (b < 0n) b = -b;
  while (b !== 0n) {
    const r = a % b;
    a = b;
    b = r;
  }
  return a;
}

/** An exact rational number in lowest terms with a positive denominator. */
export class Rational {
  private constructor(
    /** The numerator, carrying the sign. */
    readonly num: bigint,
    /** The denominator, always positive. */
    readonly den: bigint,
  ) {}

  static readonly ZERO = new Rational(0n, 1n);
  static readonly ONE = new Rational(1n, 1n);

  /** `num / den` in lowest terms. Throws on a zero denominator. */
  static of(num: bigint, den: bigint = 1n): Rational {
    if (den === 0n) throw new RangeError('Rational with a zero denominator');
    if (den === 1n) return new Rational(num, 1n);
    const g = gcd(num, den);
    if (g !== 1n) {
      num /= g;
      den /= g;
    }
    if (den < 0n) {
      num = -num;
      den = -den;
    }
    return new Rational(num, den);
  }

  isZero(): boolean {
    return this.num === 0n;
  }

  isNegative(): boolean {
    return this.num < 0n;
  }

  isPositive(): boolean {
    return this.num > 0n;
  }

  neg(): Rational {
    return new Rational(-this.num, this.den);
  }

  add(o: Rational): Rational {
    if (this.den === 1n && o.den === 1n) return new Rational(this.num + o.num, 1n);
    return Rational.of(this.num * o.den + o.num * this.den, this.den * o.den);
  }

  sub(o: Rational): Rational {
    if (this.den === 1n && o.den === 1n) return new Rational(this.num - o.num, 1n);
    return Rational.of(this.num * o.den - o.num * this.den, this.den * o.den);
  }

  mul(o: Rational): Rational {
    if (this.den === 1n && o.den === 1n) return new Rational(this.num * o.num, 1n);
    // Cross-reduce first: both factors are in lowest terms, so the product is too. A
    // denominator is at least 1, so neither gcd is zero.
    const g1 = gcd(this.num, o.den);
    const g2 = gcd(o.num, this.den);
    return new Rational((this.num / g1) * (o.num / g2), (this.den / g2) * (o.den / g1));
  }

  div(o: Rational): Rational {
    if (o.num === 0n) throw new RangeError('division by zero');
    const inverse = o.num < 0n ? new Rational(-o.den, -o.num) : new Rational(o.den, o.num);
    return this.mul(inverse);
  }

  /** Negative, zero or positive as `this` is below, equal to or above `o`. */
  cmp(o: Rational): number {
    const l = this.num * o.den;
    const r = o.num * this.den;
    return l < r ? -1 : l > r ? 1 : 0;
  }

  equals(o: Rational): boolean {
    return this.num === o.num && this.den === o.den;
  }

  /** `n` for an integer, else `n/d` (`6`, `14/3`, `-2`). */
  toString(): string {
    return this.den === 1n ? `${this.num}` : `${this.num}/${this.den}`;
  }
}

// ---- the answer types ----

/** A weighting scaled to integers: `y_p = weights[p] / denominator`, one entry per flat place. */
export interface ScaledCover {
  readonly weights: readonly bigint[];
  readonly denominator: bigint;
}

/** What {@link solveSlotBound} answers. `places` and `rows` are the presolved sizes `n'` and `m'`. */
export type LpAnswer =
  /** An optimal weighting, still to be re-checked. */
  | { readonly type: 'optimal'; readonly cover: ScaledCover; readonly places: number; readonly rows: number }
  /** No weighting satisfies the constraints: the coloured tokens are not structurally bounded. */
  | { readonly type: 'infeasible'; readonly places: number; readonly rows: number }
  /** The presolved program exceeds {@link SLOT_LP_MAX_PLACES} or {@link SLOT_LP_MAX_ROWS}. */
  | { readonly type: 'too-large'; readonly places: number; readonly rows: number }
  /** No optimum within {@link SLOT_LP_WORK_LIMIT}; `pivots` were made. */
  | { readonly type: 'work-limit'; readonly pivots: number }
  /** A pivot left a tableau entry outside 63 bits; `pivots` were made, that one included. */
  | { readonly type: 'coefficient-limit'; readonly pivots: number }
  /** The verification was stopped (total budget or cancellation, [VER-013]). */
  | { readonly type: 'stopped' };

/** A weighting {@link checkCover} accepted: `k = ⌊Y·M0 / D⌋` and the value `Y·M0 / D` in lowest terms. */
export interface CheckedCover {
  readonly k: number;
  readonly value: Rational;
}

/** {@link checkCover}'s verdict: the accepted cover, or the first failing clause. */
export type CoverCheck =
  | { readonly ok: true; readonly cover: CheckedCover }
  | { readonly ok: false; readonly reason: string };

/** The colour-slot bound as `buildColouredPlan` receives it: {@link checkedSlotBound} of the simplex's answer. */
export type SlotBound =
  /** A re-checked weighting: the bound `k`, the weighting's value, the presolved sizes. */
  | { readonly type: 'bound'; readonly k: number; readonly value: Rational; readonly places: number; readonly rows: number }
  | { readonly type: 'infeasible'; readonly places: number; readonly rows: number }
  | { readonly type: 'too-large'; readonly places: number; readonly rows: number }
  | { readonly type: 'work-limit'; readonly pivots: number }
  | { readonly type: 'coefficient-limit'; readonly pivots: number }
  /** The simplex's weighting failed the exact re-check (a simplex bug); no bound. */
  | { readonly type: 'check-failed'; readonly reason: string }
  | { readonly type: 'stopped' };

/**
 * The report line, with its two-space indent and no newline. `null` for a stop: the budget
 * machinery reports that.
 */
export function slotBoundReportLine(bound: SlotBound): string | null {
  switch (bound.type) {
    case 'bound':
      return `  Colour-slot bound: LP optimum ${bound.value} over ${bound.places} places and ${bound.rows} ` +
        `transitions, so k=${bound.k} (re-checked in exact arithmetic)`;
    case 'infeasible':
      return `  Colour-slot bound: none (LP infeasible over ${bound.places} places and ${bound.rows} ` +
        'transitions: no weighting bounds the coloured tokens)';
    case 'too-large':
      return `  Colour-slot bound: none (LP over ${bound.places} places and ${bound.rows} transitions ` +
        `exceeds the limit of ${SLOT_LP_MAX_PLACES} places and ${SLOT_LP_MAX_ROWS} transitions)`;
    case 'work-limit':
      return `  Colour-slot bound: none (no LP optimum within the work limit of ${SLOT_LP_WORK_LIMIT} ` +
        `entry updates, after ${bound.pivots} pivots)`;
    case 'coefficient-limit':
      return `  Colour-slot bound: none (an LP coefficient outgrew 63 bits after ${bound.pivots} pivots)`;
    case 'check-failed':
      return `  Colour-slot bound: none (LP weighting failed the exact re-check: ${bound.reason})`;
    case 'stopped':
      return null;
  }
}

/**
 * The bound of whatever the simplex answered (Lean `colourSlotBoundLP`). An optimal answer
 * goes through {@link checkCover}; every other answer passes through as no bound. `k` never
 * comes from an unchecked weighting.
 */
export function checkedSlotBound(
  flat: FlatNet,
  initial: MarkingState,
  coloured: readonly number[],
  answer: LpAnswer,
): SlotBound {
  switch (answer.type) {
    case 'optimal': {
      const check = checkCover(flat, initial, coloured, answer.cover);
      return check.ok
        ? { type: 'bound', k: check.cover.k, value: check.cover.value, places: answer.places, rows: answer.rows }
        : { type: 'check-failed', reason: check.reason };
    }
    case 'infeasible':
      return { type: 'infeasible', places: answer.places, rows: answer.rows };
    case 'too-large':
      return { type: 'too-large', places: answer.places, rows: answer.rows };
    case 'work-limit':
      return { type: 'work-limit', pivots: answer.pivots };
    case 'coefficient-limit':
      return { type: 'coefficient-limit', pivots: answer.pivots };
    case 'stopped':
      return { type: 'stopped' };
  }
}

/** A flat count as an exact integer; a fractional or non-finite count is a caller bug. */
function exactCount(v: number): bigint {
  return BigInt(v);
}

/**
 * The exact re-check of a scaled weighting (Lean `checkCover`). Accepts `(Y, D)` exactly
 * when, in unbounded integer arithmetic,
 *
 * 1. `Y` has one entry per flat place;
 * 2. `D ≥ 1`;
 * 3. `Y_p ≥ 0` for every place, in index order;
 * 4. `Y_p ≥ D` for every coloured place, ascending;
 * 5. `Σ_p Y_p·(post_r[p] − pre_r[p]) ≤ 0` for every flat row `r` of `flat.transitions`, in
 *    flat order: all of them, never the presolved or deduplicated ones;
 * 6. with `V = Σ_p Y_p·M0[p]` and `k = V div D`, `k ≤` {@link SLOT_CAP}.
 *
 * and then returns `k` and `V / D`. The first failing check names the refusal. A coloured
 * index outside the net is refused too; `buildColouredPlan` never passes one.
 *
 * `pre_r[p]` is the summed required count of the inputs on `p`; [CORE-030] AC3 rejects two
 * input specs on one place, so it is the one spec's count Lean `dotIncD` reads.
 */
export function checkCover(
  flat: FlatNet,
  initial: MarkingState,
  coloured: readonly number[],
  cover: ScaledCover,
): CoverCheck {
  const n = flat.places.length;
  const y = cover.weights;
  const d = cover.denominator;
  if (y.length !== n) return { ok: false, reason: `weighting has ${y.length} entries for ${n} places` };
  if (d <= 0n) return { ok: false, reason: `denominator ${d} is not positive` };
  for (let p = 0; p < n; p++) {
    if (y[p]! < 0n) return { ok: false, reason: `place '${flat.places[p]!.name}' has negative weight ${y[p]}` };
  }
  const ascending = [...coloured].sort((a, b) => a - b);
  for (const p of ascending) {
    if (p < 0 || p >= n) return { ok: false, reason: `coloured place index ${p} is out of range for ${n} places` };
    if (y[p]! < d) {
      return {
        ok: false,
        reason: `coloured place '${flat.places[p]!.name}' has weight ${y[p]} below the denominator ${d}`,
      };
    }
  }
  for (const row of flat.transitions) {
    let delta = 0n;
    for (let p = 0; p < n; p++) {
      const post = row.postVector[p] ?? 0;
      const pre = row.preVector[p] ?? 0;
      if (post !== pre) delta += y[p]! * (exactCount(post) - exactCount(pre));
    }
    if (delta > 0n) return { ok: false, reason: `transition '${row.name}' increases the weighted sum by ${delta}` };
  }
  let v = 0n;
  for (let p = 0; p < n; p++) {
    const m0 = initial.tokens(flat.places[p]!);
    if (m0 !== 0) v += y[p]! * exactCount(m0);
  }
  const k = v / d;
  if (k > SLOT_CAP) return { ok: false, reason: `k=${k} exceeds ${SLOT_CAP}` };
  return { ok: true, cover: { k: Number(k), value: Rational.of(v, d) } };
}

/** A stop poll that never stops. */
const NEVER = (): boolean => false;

/**
 * Solves the colour-slot program for the coloured places `coloured` (flat indices).
 * Untrusted: see the module documentation. `stop` is polled before every pivot; returning
 * `true` answers `stopped`, and a poll that throws ends the solve with its error.
 */
export function solveSlotBound(
  flat: FlatNet,
  initial: MarkingState,
  coloured: readonly number[],
  stop: () => boolean = NEVER,
): LpAnswer {
  return solveSlotBoundCounted(flat, initial, coloured, stop).answer;
}

/** What a solve spent: its pivots and its work (see the module documentation). */
export interface SolveCounts {
  readonly pivots: number;
  readonly work: number;
}

/** {@link solveSlotBound}, with what it spent. Exported for the shared fixtures and tests. */
export function solveSlotBoundCounted(
  flat: FlatNet,
  initial: MarkingState,
  coloured: readonly number[],
  stop: () => boolean = NEVER,
): { readonly answer: LpAnswer; readonly counts: SolveCounts } {
  const n = flat.places.length;
  const isColoured = new Array<boolean>(n).fill(false);
  for (const p of coloured) if (p >= 0 && p < n) isColoured[p] = true;
  const program = presolve(flat, isColoured);
  const places = program.places.length;
  const rows = program.rows.length;
  if (places > SLOT_LP_MAX_PLACES || rows > SLOT_LP_MAX_ROWS) {
    return { answer: { type: 'too-large', places, rows }, counts: { pivots: 0, work: 0 } };
  }

  // Constraint row i is place U[i]: `A[i][j] = −N_j[U[i]]` for kept row j, then its slack.
  // Kept rows are visited in order, so every sparse row stays sorted by column.
  const a: SparseRow[] = Array.from({ length: places }, () => []);
  program.rows.forEach((row, j) => {
    for (const [i, v] of row) a[i]!.push([j, Rational.of(-v)]);
  });
  a.forEach((r, i) => r.push([rows + i, Rational.ONE]));
  const b = program.places.map(p => Rational.of(exactCount(initial.tokens(flat.places[p]!))));
  // The objective row starts at −c_j on the structural columns.
  const obj: SparseRow = [];
  program.rows.forEach((row, j) => {
    let c = 0n;
    for (const [i, v] of row) if (isColoured[program.places[i]!]) c += v;
    if (c !== 0n) obj.push([j, Rational.of(-c)]);
  });
  const tableau = new SlotTableau(a, b, obj, Array.from({ length: places }, (_, i) => rows + i));
  const outcome = tableau.run('bland', SLOT_LP_WORK_LIMIT, stop);
  let answer: LpAnswer;
  switch (outcome) {
    case 'optimal': {
      const y = new Array<Rational>(n).fill(Rational.ZERO);
      program.places.forEach((p, i) => {
        const pi = lookup(tableau.obj, rows + i) ?? Rational.ZERO;
        y[p] = isColoured[p] ? pi.add(Rational.ONE) : pi;
      });
      let denominator = 1n;
      for (const v of y) denominator = (denominator / gcd(denominator, v.den)) * v.den;
      const weights = y.map(v => v.num * (denominator / v.den));
      answer = { type: 'optimal', cover: { weights, denominator }, places, rows };
      break;
    }
    case 'unbounded':
      answer = { type: 'infeasible', places, rows };
      break;
    case 'work-limit':
      answer = { type: 'work-limit', pivots: tableau.pivots };
      break;
    case 'coefficient-limit':
      answer = { type: 'coefficient-limit', pivots: tableau.pivots };
      break;
    case 'stopped':
      answer = { type: 'stopped' };
      break;
  }
  return { answer, counts: { pivots: tableau.pivots, work: tableau.work } };
}

/**
 * @internal The presolved program: the places of `U` ascending, and the kept rows, each a
 * sparse vector over positions in `U` of the row's column `post − pre`. Exported for tests.
 */
export interface Presolved {
  readonly places: readonly number[];
  readonly rows: readonly (readonly (readonly [number, bigint])[])[];
}

/** @internal The presolve of step 1. Exported for tests. */
export function presolve(flat: FlatNet, isColoured: readonly boolean[]): Presolved {
  const n = flat.places.length;
  const columns: (readonly [number, bigint])[][] = flat.transitions.map(t => {
    const col: [number, bigint][] = [];
    for (let p = 0; p < n; p++) {
      const post = t.postVector[p] ?? 0;
      const pre = t.preVector[p] ?? 0;
      if (post !== pre) col.push([p, exactCount(post) - exactCount(pre)]);
    }
    return col;
  });
  const producesInto = (col: readonly (readonly [number, bigint])[], inU: readonly boolean[]): boolean =>
    col.some(([q, v]) => v > 0n && inU[q]!);

  // The upstream cone, to a fixpoint. It is a set, so the visiting order is irrelevant.
  const inU = [...isColoured];
  for (;;) {
    let changed = false;
    for (const col of columns) {
      if (!producesInto(col, inU)) continue;
      for (const [p, v] of col) {
        if (v < 0n && !inU[p]) {
          inU[p] = true;
          changed = true;
        }
      }
    }
    if (!changed) break;
  }
  const places: number[] = [];
  for (let p = 0; p < n; p++) if (inU[p]) places.push(p);
  const position = new Array<number>(n).fill(-1);
  places.forEach((p, i) => { position[p] = i; });

  const seen = new Set<string>();
  const rows: (readonly [number, bigint])[][] = [];
  for (const col of columns) {
    if (!producesInto(col, inU)) continue;
    const restricted = col.filter(([p]) => inU[p]).map(([p, v]) => [position[p]!, v] as const);
    const key = restricted.map(([i, v]) => `${i}:${v}`).join(',');
    if (!seen.has(key)) {
      seen.add(key);
      rows.push(restricted);
    }
  }
  return { places, rows };
}

// ---- the simplex core ----

/** A sparse row: `[column, value]` sorted by column, no zero value. */
type SparseRow = (readonly [number, Rational])[];

function lookupIndex(row: SparseRow, col: number): number {
  let lo = 0;
  let hi = row.length - 1;
  while (lo <= hi) {
    const mid = (lo + hi) >>> 1;
    const c = row[mid]![0];
    if (c === col) return mid;
    if (c < col) lo = mid + 1;
    else hi = mid - 1;
  }
  return -1;
}

function lookup(row: SparseRow, col: number): Rational | undefined {
  const i = lookupIndex(row, col);
  return i < 0 ? undefined : row[i]![1];
}

/**
 * Whether a value is within the coefficient limit: numerator and denominator in lowest terms
 * at most `2^63 − 1` in absolute value.
 */
function fits(v: Rational): boolean {
  return (v.num < 0n ? -v.num : v.num) <= COEFFICIENT_MAX && v.den <= COEFFICIENT_MAX;
}

function rowFits(row: SparseRow): boolean {
  return row.every(([, v]) => fits(v));
}

/** `row − f·prow`, both sorted, zeros dropped. */
function subScaled(row: SparseRow, f: Rational, prow: SparseRow): SparseRow {
  const out: SparseRow = [];
  let i = 0;
  let j = 0;
  while (i < row.length || j < prow.length) {
    const ci = i < row.length ? row[i]![0] : Infinity;
    const cj = j < prow.length ? prow[j]![0] : Infinity;
    if (ci < cj) {
      out.push(row[i]!);
      i++;
    } else if (cj < ci) {
      out.push([cj, f.mul(prow[j]![1]).neg()]);
      j++;
    } else {
      const v = row[i]![1].sub(f.mul(prow[j]![1]));
      if (!v.isZero()) out.push([ci, v]);
      i++;
      j++;
    }
  }
  return out;
}

/**
 * @internal The pivot rule. Only `'bland'` is used outside tests. `'largest'` takes the most
 * negative objective entry (smallest column on ties) and the least ratio with ties to the
 * lowest row; it can cycle, which is what the tests show.
 */
export type PivotRule = 'bland' | 'largest';

/** @internal How a run of the tableau ended. */
export type SimplexOutcome = 'optimal' | 'unbounded' | 'work-limit' | 'coefficient-limit' | 'stopped';

/**
 * @internal A maximisation tableau `z + Σ obj_j·x_j = objValue`, `rows·x = rhs`, one basic
 * column per row. Exported for tests.
 */
export class SlotTableau {
  objValue: Rational = Rational.ZERO;
  /** Pivots performed so far. */
  pivots = 0;
  /** Work done so far, in entry updates (see the module documentation). */
  work = 0;

  constructor(
    public rows: SparseRow[],
    public rhs: Rational[],
    public obj: SparseRow,
    public basis: number[],
  ) {}

  /**
   * The standard form `max c·x` subject to `A·x ≤ b`, `x ≥ 0`, with `b ≥ 0` and the slacks
   * as the initial basis (columns `0..c.length` structural, then one slack per row).
   */
  static standard(a: readonly (readonly Rational[])[], b: Rational[], c: readonly Rational[]): SlotTableau {
    const m = c.length;
    const rows = a.map((r, i) => {
      const row: SparseRow = [];
      r.forEach((v, j) => { if (!v.isZero()) row.push([j, v]); });
      row.push([m + i, Rational.ONE]);
      return row;
    });
    const obj: SparseRow = [];
    c.forEach((v, j) => { if (!v.isZero()) obj.push([j, v.neg()]); });
    return new SlotTableau(rows, b, obj, a.map((_, i) => m + i));
  }

  entering(rule: PivotRule): number | null {
    if (rule === 'bland') {
      for (const [c, v] of this.obj) if (v.isNegative()) return c;
      return null;
    }
    let best: readonly [number, Rational] | null = null;
    for (const e of this.obj) {
      if (e[1].isNegative() && (best === null || e[1].cmp(best[1]) < 0)) best = e;
    }
    return best === null ? null : best[0];
  }

  leaving(rule: PivotRule, e: number): number | null {
    let best: { i: number; ratio: Rational } | null = null;
    for (let i = 0; i < this.rows.length; i++) {
      const a = lookup(this.rows[i]!, e);
      if (a === undefined || !a.isPositive()) continue;
      const ratio = this.rhs[i]!.div(a);
      let better: boolean;
      if (best === null) better = true;
      else {
        const c = ratio.cmp(best.ratio);
        better = c < 0 || (c === 0 && rule === 'bland' && this.basis[i]! < this.basis[best.i]!);
      }
      if (better) best = { i, ratio };
    }
    return best === null ? null : best.i;
  }

  /** Whether every entry is within the coefficient limit. */
  fits(): boolean {
    return this.rows.every(rowFits) && this.rhs.every(fits) && rowFits(this.obj) && fits(this.objValue);
  }

  /**
   * The work of pivoting on `(r, e)`: the pivot row's entries, plus, for every row it updates,
   * that row's entries and the pivot row's.
   */
  pivotWork(r: number, e: number): number {
    const p = this.rows[r]!.length;
    const updated = (row: SparseRow): number => (lookupIndex(row, e) < 0 ? 0 : row.length + p);
    let work = p + updated(this.obj);
    for (let i = 0; i < this.rows.length; i++) if (i !== r) work += updated(this.rows[i]!);
    return work;
  }

  /** Pivots on `(r, e)`; whether every entry it wrote is within the coefficient limit. */
  pivot(r: number, e: number): boolean {
    const a = lookup(this.rows[r]!, e);
    if (a === undefined) throw new Error('pivot entry');
    const prow: SparseRow = this.rows[r]!.map(([c, v]) => [c, v.div(a)] as const);
    const prhs = this.rhs[r]!.div(a);
    let within = rowFits(prow) && fits(prhs);
    for (let i = 0; i < this.rows.length; i++) {
      if (i === r) continue;
      const f = lookup(this.rows[i]!, e);
      if (f !== undefined) {
        this.rows[i] = subScaled(this.rows[i]!, f, prow);
        this.rhs[i] = this.rhs[i]!.sub(f.mul(prhs));
        within &&= rowFits(this.rows[i]!) && fits(this.rhs[i]!);
      }
    }
    const f = lookup(this.obj, e);
    if (f !== undefined) {
      this.obj = subScaled(this.obj, f, prow);
      this.objValue = this.objValue.sub(f.mul(prhs));
      within &&= rowFits(this.obj) && fits(this.objValue);
    }
    this.rows[r] = prow;
    this.rhs[r] = prhs;
    this.basis[r] = e;
    return within;
  }

  /**
   * Pivots until optimal or unbounded, within `limit` work in all and the coefficient limit,
   * polling `stop` before every pivot.
   */
  run(rule: PivotRule, limit: number, stop: () => boolean = NEVER): SimplexOutcome {
    if (!this.fits()) return 'coefficient-limit';
    for (;;) {
      const e = this.entering(rule);
      if (e === null) return 'optimal';
      const r = this.leaving(rule, e);
      if (r === null) return 'unbounded';
      const work = this.pivotWork(r, e);
      if (this.work + work > limit) return 'work-limit';
      if (stop()) return 'stopped';
      const within = this.pivot(r, e);
      this.pivots++;
      this.work += work;
      if (!within) return 'coefficient-limit';
    }
  }
}
