/**
 * Name-correlation fragment classifier for the ν-aware state class graph
 * (NU-050, Route B). See the Rust/Java equivalents for the full contract.
 *
 * Identifies the coloured places (the correlated inputs of ν-joins) and the role
 * of each transition in the supported fragment. Returns `null` when the net is
 * not a ν-net or falls outside the admitted fragment (the caller falls back to
 * the SMT / Route A path).
 *
 * {@link FragmentMode.base} (default) admits the shipped mint → matched-join
 * fragment only: a non-match transition consuming a coloured place, or a join
 * re-minting into one, rejects the net. {@link FragmentMode.extended} (opt-in,
 * NU-051) additionally admits the coloured-consumer role ({@link Role} `consume`,
 * drain/relay) and unions user-declared *carrier* places into the coloured set
 * (fork-threaded co-mint). The one deliberate tightening shared by both modes is
 * the reset/read/inhibitor-on-coloured guard below.
 */
import type { PetriNet } from '../../core/petri-net.js';
import type { Transition } from '../../core/transition.js';
import { enumerateBranches } from '../../core/out.js';

/**
 * Selects which coloured-place fragment {@link classify} admits. `base` (default)
 * reproduces the shipped mint → matched-join fragment exactly; `extended`
 * additionally admits the coloured-consumer (drain/relay) role and carrier
 * places (NU-051).
 */
export type FragmentMode = 'base' | 'extended';

export type Role =
  | { readonly type: 'ordinary' }
  | { readonly type: 'mint' }
  | { readonly type: 'join'; readonly colouredIn: ReadonlyArray<readonly [string, number]> }
  /**
   * Coloured consumer (drain/relay), EXTENDED only (NU-051). A non-match
   * transition that consumes **exactly one** coloured place at count **exactly
   * one**. It *relays* the consumed name-symbol into each coloured output of the
   * fired branch (threading `s`), or *drains* it (dead-letters `s`) when the
   * branch produces no coloured output. Because the consumed count is fixed at
   * one, the role carries only the input place name — no count, no list.
   *
   * Documented precondition (NU-051): the action MUST thread the consumed symbol
   * (relay) or drop it (drain); it MUST NOT mint a *fresh* name into a coloured
   * output while consuming a coloured token (a consume-and-remint transition is
   * out of contract — the name layer would thread `s` where the runtime mints
   * afresh).
   */
  | { readonly type: 'consume'; readonly colouredInput: string };

export interface NameFragment {
  readonly colouredOrder: readonly string[];
  isColoured(place: string): boolean;
  role(transition: string): Role;
}

/**
 * Classifies `net` under `mode`. Under {@link FragmentMode.extended} the declared
 * `carrierPlaces` (intermediate places carrying a fresh name from the minting
 * fork onward to a ν-join input) are unioned into the coloured set *before* role
 * assignment, so the existing mint co-mints one fresh name into all of them, and
 * non-match transitions may take the drain/relay `consume` role. Under
 * {@link FragmentMode.base} the `carrierPlaces` are ignored and any non-match
 * transition consuming a coloured place rejects the net (NU-051).
 *
 * Both modes reject a net where any coloured place carries a reset, read, or
 * inhibitor arc: those arcs would be silently misclassified ordinary and the
 * name layer would drift from the base marking (a soundness guard; rejection
 * just falls back to the sound over-approximation).
 */
export function classify(
  net: PetriNet,
  mode: FragmentMode,
  carrierPlaces: ReadonlySet<string>,
): NameFragment | null {
  // 1. Coloured places = union of every match transition's correlated inputs,
  //    plus (EXTENDED only) the declared carrier places.
  const coloured = new Set<string>();
  let anyMatch = false;
  for (const t of net.transitions) {
    if (t.matchSpec !== null) {
      anyMatch = true;
      for (const key of t.matchSpec.keys) coloured.add(key.place.name);
    }
  }
  if (!anyMatch || coloured.size === 0) return null;
  if (mode === 'extended') {
    for (const c of carrierPlaces) coloured.add(c);
  }

  // 1b. Soundness guard (BOTH modes): no coloured place may carry a reset, read,
  //     or inhibitor arc on any transition. Checked after the coloured set is
  //     finalized (a carrier could carry such an arc).
  for (const t of net.transitions) {
    if (
      t.resets.some(r => coloured.has(r.place.name)) ||
      t.reads.some(r => coloured.has(r.place.name)) ||
      t.inhibitors.some(i => coloured.has(i.place.name))
    ) {
      return null;
    }
  }

  const roles = new Map<string, Role>();
  for (const t of net.transitions) {
    const colouredInputs = t.inputSpecs.filter(s => coloured.has(s.place.name));
    const consumesColoured = colouredInputs.length > 0;
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
    } else if (consumesColoured) {
      // A non-match transition consuming a coloured token.
      if (mode === 'base') return null; // BASE: unsupported — the name would be ambiguous.
      // EXTENDED: admitted as a drain/relay ONLY when it consumes exactly ONE
      // coloured place at count EXACTLY ONE (one or exactly{count:1}). More than
      // one coloured input, or any higher / all / at-least count, would over-count
      // the name layer relative to the base marking (which adds exactly one token
      // per output place) — reject to the sound over-approximation.
      if (colouredInputs.length !== 1) return null;
      const spec = colouredInputs[0]!;
      const countOne = spec.type === 'one' || (spec.type === 'exactly' && spec.count === 1);
      if (!countOne) return null;
      role = { type: 'consume', colouredInput: spec.place.name };
    } else if (producesColoured) {
      role = { type: 'mint' };
    } else {
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
