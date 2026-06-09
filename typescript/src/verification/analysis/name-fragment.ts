/**
 * Name-correlation fragment classifier for the ν-aware state class graph
 * (NU-050, Route B). See the Rust/Java equivalents for the full contract.
 *
 * Identifies the coloured places (the correlated inputs of ν-joins) and the role
 * of each transition in the supported mint → matched-join fragment. Returns
 * `null` when the net is not a ν-net or falls outside the fragment (a non-match
 * transition consuming a coloured place, or a join re-minting into one).
 */
import type { PetriNet } from '../../core/petri-net.js';
import type { Transition } from '../../core/transition.js';
import { enumerateBranches } from '../../core/out.js';

export type Role =
  | { readonly type: 'ordinary' }
  | { readonly type: 'mint' }
  | { readonly type: 'join'; readonly colouredIn: ReadonlyArray<readonly [string, number]> };

export interface NameFragment {
  readonly colouredOrder: readonly string[];
  isColoured(place: string): boolean;
  role(transition: string): Role;
}

export function classify(net: PetriNet): NameFragment | null {
  const coloured = new Set<string>();
  let anyMatch = false;
  for (const t of net.transitions) {
    if (t.matchSpec !== null) {
      anyMatch = true;
      for (const key of t.matchSpec.keys) coloured.add(key.place.name);
    }
  }
  if (!anyMatch || coloured.size === 0) return null;

  const roles = new Map<string, Role>();
  for (const t of net.transitions) {
    const consumesColoured = t.inputSpecs.some(s => coloured.has(s.place.name));
    let producesColoured = false;
    if (t.outputSpec !== null) {
      for (const branch of enumerateBranches(t.outputSpec)) {
        for (const p of branch) {
          if (coloured.has(p.name)) producesColoured = true;
        }
      }
    }

    let role: Role;
    if (t.matchSpec !== null) {
      if (producesColoured) return null; // re-mint onto a coloured place — out of fragment
      const colouredIn: Array<readonly [string, number]> = [];
      for (const key of t.matchSpec.keys) {
        const place = key.place.name;
        // One/Exactly consume a fixed count of the matched name (faithfully
        // modelled). All/AtLeast consume ALL matching tokens at runtime — the
        // fixed-count SCG step would under-consume — so drop to the over-approx.
        const required = fixedRequiredCount(t, place);
        if (required === null) return null;
        colouredIn.push([place, required] as const);
      }
      colouredIn.sort((a, b) => (a[0] < b[0] ? -1 : a[0] > b[0] ? 1 : 0));
      role = { type: 'join', colouredIn };
    } else if (producesColoured) {
      if (consumesColoured) return null;
      role = { type: 'mint' };
    } else {
      if (consumesColoured) return null;
      role = { type: 'ordinary' };
    }
    roles.set(t.name, role);
  }

  const colouredOrder = [...coloured].sort();
  return {
    colouredOrder,
    isColoured: (p) => coloured.has(p),
    role: (tn) => roles.get(tn) ?? { type: 'ordinary' },
  };
}

/**
 * The fixed per-firing consumption of the matched name for `t`'s input on
 * `placeName`, or `null` when the cardinality consumes ALL matching tokens
 * (all/at-least) or no such input exists — neither of which the fixed-count SCG
 * step can model faithfully.
 */
function fixedRequiredCount(t: Transition, placeName: string): number | null {
  for (const spec of t.inputSpecs) {
    if (spec.place.name === placeName) {
      switch (spec.type) {
        case 'one': return 1;
        case 'exactly': return spec.count;
        case 'all': return null;
        case 'at-least': return null;
      }
    }
  }
  return null;
}
