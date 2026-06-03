import type { FlatNet } from './flat-net.js';

/**
 * Incidence matrix for a flattened Petri net.
 *
 * The incidence matrix C is defined as C[t][p] = post[t][p] - pre[t][p].
 * It captures the net effect of each transition on each place.
 *
 * P-invariants are solutions to y^T * C = 0, found via null space
 * computation on C^T.
 */
export class IncidenceMatrix {
  private readonly _pre: readonly (readonly number[])[];
  private readonly _post: readonly (readonly number[])[];
  private readonly _incidence: readonly (readonly number[])[];
  private readonly _numTransitions: number;
  private readonly _numPlaces: number;

  private constructor(
    pre: number[][],
    post: number[][],
    incidence: number[][],
    numTransitions: number,
    numPlaces: number,
  ) {
    this._pre = pre;
    this._post = post;
    this._incidence = incidence;
    this._numTransitions = numTransitions;
    this._numPlaces = numPlaces;
  }

  /**
   * Computes the incidence matrix from a FlatNet.
   *
   * Environment-injected places (VER-006) each contribute one extra **injector
   * column** (a virtual transition that produces one token into that place and
   * consumes nothing). This makes P-invariant computation env-aware: a valid
   * invariant `y` must satisfy `y^T·C = 0` for the injector column too, forcing
   * `y[envPlace] = 0` and thereby discarding closed-net conservation laws (e.g.
   * `IN + OUT = const`) that would otherwise vacuously bound an injectable place.
   */
  static from(flatNet: FlatNet): IncidenceMatrix {
    const T = flatNet.transitions.length;
    const P = flatNet.places.length;

    const pre: number[][] = [];
    const post: number[][] = [];
    const incidence: number[][] = [];

    for (let t = 0; t < T; t++) {
      const ft = flatNet.transitions[t]!;
      const preRow = new Array<number>(P);
      const postRow = new Array<number>(P);
      const incRow = new Array<number>(P);

      for (let p = 0; p < P; p++) {
        preRow[p] = ft.preVector[p]!;
        postRow[p] = ft.postVector[p]!;
        incRow[p] = postRow[p]! - preRow[p]!;
      }

      pre.push(preRow);
      post.push(postRow);
      incidence.push(incRow);
    }

    // Injector columns (one per injected environment place): pre = 0, post = e_p.
    let injectorCount = 0;
    for (const name of flatNet.environmentInjection.keys()) {
      const idx = flatNet.placeIndex.get(name);
      if (idx == null) continue;
      const preRow = new Array<number>(P).fill(0);
      const postRow = new Array<number>(P).fill(0);
      const incRow = new Array<number>(P).fill(0);
      postRow[idx] = 1;
      incRow[idx] = 1;
      pre.push(preRow);
      post.push(postRow);
      incidence.push(incRow);
      injectorCount++;
    }

    return new IncidenceMatrix(pre, post, incidence, T + injectorCount, P);
  }

  /**
   * Returns C^T (transpose of incidence matrix), dimensions [P][T].
   * Used for P-invariant computation: null space of C^T gives P-invariants.
   */
  transposedIncidence(): number[][] {
    const ct: number[][] = [];
    for (let p = 0; p < this._numPlaces; p++) {
      const row = new Array<number>(this._numTransitions);
      for (let t = 0; t < this._numTransitions; t++) {
        row[t] = this._incidence[t]![p]!;
      }
      ct.push(row);
    }
    return ct;
  }

  /** Returns the pre-matrix (tokens consumed). T×P. */
  pre(): readonly (readonly number[])[] { return this._pre; }

  /** Returns the post-matrix (tokens produced). T×P. */
  post(): readonly (readonly number[])[] { return this._post; }

  /** Returns the incidence matrix C[t][p] = post - pre. T×P. */
  incidence(): readonly (readonly number[])[] { return this._incidence; }

  numTransitions(): number { return this._numTransitions; }
  numPlaces(): number { return this._numPlaces; }
}
