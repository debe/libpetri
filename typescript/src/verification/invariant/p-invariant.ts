/**
 * A P-invariant (place invariant) of a Petri net.
 *
 * A P-invariant is a vector y such that y^T * C = 0, where C is the
 * incidence matrix. This means that for any reachable marking M:
 * sum(y_i * M_i) = constant, where constant = sum(y_i * M0_i).
 *
 * P-invariants provide structural bounds on places and are used as
 * strengthening lemmas for the IC3/PDR engine.
 */
export interface PInvariant {
  /** Weight vector (one entry per place index). */
  readonly weights: readonly number[];
  /** The invariant value sum(y_i * M0_i). */
  readonly constant: number;
  /** Set of place indices where weight != 0. */
  readonly support: ReadonlySet<number>;
}

export function pInvariant(weights: number[], constant: number, support: Set<number>): PInvariant {
  return { weights, constant, support };
}

export function pInvariantToString(inv: PInvariant): string {
  const parts: string[] = [];
  for (const i of inv.support) {
    if (inv.weights[i] !== 1) {
      parts.push(`${inv.weights[i]}*p${i}`);
    } else {
      parts.push(`p${i}`);
    }
  }
  return `PInvariant[${parts.join(' + ')} = ${inv.constant}]`;
}
