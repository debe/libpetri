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
 * (fork-threaded co-mint), and the declared relay targets of every join (NU-054),
 * onto which a join writes the name it matched. The one deliberate tightening
 * shared by both modes is the reset/read/inhibitor-on-coloured guard below.
 */
import type { PetriNet } from '../../core/petri-net.js';
import type { Transition } from '../../core/transition.js';
import { outcomes, timeoutWrites } from './branch-outcomes.js';
import { compareCodePoints } from '../../core/internal/code-point-order.js';

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
  /**
   * A matched join (NU-020). `relayTo` (EXTENDED only, NU-054) holds the declared relay targets:
   * a firing on symbol `s` removes `s` from the keys, then adds `s` once to each relay target in
   * the fired branch. Empty under BASE and for a join that drains the name.
   */
  | {
      readonly type: 'join';
      readonly colouredIn: ReadonlyArray<readonly [string, number]>;
      readonly relayTo: ReadonlySet<string>;
    }
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
  /** The transitions read as mints, in net order: the analysis trusts the mint contract of NU-010 for them. */
  readonly mints: readonly string[];
  /**
   * The coloured consumers that write a coloured place, in net order: the analysis trusts the
   * relay contract of NU-051 for their action writes.
   */
  readonly relays: readonly string[];
}

/**
 * The transitions of `net` declared to mint (NU-010): each one named in `explicit` (the
 * verifier's `mintTransitions`), plus each one that consumes a declared budget place, since a
 * budget token is what a fork consumes when it mints (NU-040).
 */
export function declaredMints(
  net: PetriNet,
  budgetPlaces: ReadonlySet<string>,
  explicit: ReadonlySet<string>,
): Set<string> {
  const out = new Set(explicit);
  for (const t of net.transitions) {
    if (t.inputSpecs.some(s => budgetPlaces.has(s.place.name))) out.add(t.name);
  }
  return out;
}

/**
 * Why `declared` does not name transitions of `net` (NU-010), or `null` when every name is one:
 * the unknown names, code-point sorted and each once. A typo in a mint declaration would
 * silently leave a real mint undeclared, so every entry point rejects it with this text.
 */
export function unknownMintReason(net: PetriNet, declared: Iterable<string>): string | null {
  const inNet = new Set([...net.transitions].map(t => t.name));
  const unknown = [...new Set([...declared].filter(n => !inNet.has(n)))].sort(compareCodePoints);
  if (unknown.length === 0) return null;
  return `declared mint transition${unknown.length === 1 ? '' : 's'} ` +
    `${unknown.map(n => `'${n}'`).join(', ')} not in the net (NU-010)`;
}

/**
 * The transitions of `net` that write a coloured place of the fragment without consuming one and
 * are not in `mints`, in net order, when declaring them is all that keeps `net` out of the
 * fragment: {@link classify} admits `net` with every transition read as a mint and rejects it
 * with `mints`. Empty otherwise. These are the undeclared mints a Route B decline points at
 * (NU-010).
 */
export function undeclaredMints(
  net: PetriNet,
  mode: FragmentMode,
  carrierPlaces: ReadonlySet<string>,
  mints: ReadonlySet<string>,
): string[] {
  if (classify(net, mode, carrierPlaces, mints) !== null) return [];
  const every = new Set([...net.transitions].map(t => t.name));
  const fragment = classify(net, mode, carrierPlaces, every);
  return fragment === null ? [] : fragment.mints.filter(m => !mints.has(m));
}

/**
 * The sentence a Route B decline adds when {@link undeclaredMints} names transitions: which
 * transitions to declare, and with what.
 */
export function undeclaredMintsPointer(undeclared: readonly string[]): string {
  const one = undeclared.length === 1;
  return `${undeclared.map(t => `'${t}'`).join(', ')} ${one ? 'writes' : 'write'} a coloured place ` +
    `without consuming one and ${one ? 'is' : 'are'} not declared to mint (NU-010); if the action ` +
    `writes a name minted with freshName(), declare ${one ? 'it' : 'them'} with mintTransitions`;
}

/**
 * The report lines naming the ν contracts a verdict rests on (NU-010, NU-051): the transitions
 * read as mints, and the coloured consumers whose action writes are read as relays. Empty when
 * there are none. The analyses cannot check what an action writes, so a verdict holds only
 * while these actions keep the contracts.
 */
export function contractNote(mints: readonly string[], relays: readonly string[]): string {
  let out = '';
  if (mints.length > 0) {
    out += `Mint contract (NU-010) assumed for ${mints.join(', ')}: each writes a freshly minted name into every coloured place it writes.\n`;
  }
  if (relays.length > 0) {
    out += `Relay contract (NU-051) assumed for ${relays.join(', ')}: each writes the name it consumed into every coloured place it writes.\n`;
  }
  return out;
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
 *
 * A transition that writes a coloured place without consuming one is read as a **mint** only
 * when it is named in `mintTransitions`, the declared mints ({@link declaredMints}). The
 * declaration is the net's statement that the action writes a name freshly minted by
 * `freshName()` into each coloured place it writes (NU-010). An action may write any value, a
 * copied correlation id included, so without the declaration the name layer cannot give the
 * deposit a fresh symbol and the net is rejected. A deposit the executor makes on timeout is
 * never a mint, declared or not: a forward copies a consumed value and an `Out.place` writes a
 * unit token with no name (IO-013, IO-014). A join's timeout may write a relay target only by
 * forwarding one of its match keys, the one write that carries the matched name. The executor
 * checks every relay deposit (NU-054) and fails the firing on any other, so no timeout write
 * relies on a contract.
 */
export function classify(
  net: PetriNet,
  mode: FragmentMode,
  carrierPlaces: ReadonlySet<string>,
  mintTransitions: ReadonlySet<string>,
): NameFragment | null {
  // 1. Coloured places = union of every match transition's correlated inputs,
  //    plus (EXTENDED only) the declared carrier places and every join's relay
  //    targets (NU-054). BASE ignores relay declarations, as it ignores carriers.
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
    for (const t of net.transitions) {
      if (t.matchSpec !== null) for (const r of t.matchSpec.relays) coloured.add(r.place.name);
    }
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
  const mints: string[] = [];
  const relays: string[] = [];
  for (const t of net.transitions) {
    const colouredInputs = t.inputSpecs.filter(s => coloured.has(s.place.name));
    const consumesColoured = colouredInputs.length > 0;
    const branches = outcomes(t);
    // The name layer adds one symbol per coloured output place of a firing, as the base
    // marking adds one token per place an action writes. A timeout forward deposits one token
    // per consumed token ([IO-014]); into a coloured place at any count but one, the name
    // layer would lose track of the base marking.
    if (branches.some(o => o.deposits.some(d =>
      coloured.has(d.place.name) && !(d.deposit.type === 'tokens' && d.deposit.count === 1)))) {
      return null;
    }
    let producesColoured = false;
    for (const branch of branches) {
      for (const p of branch.places) {
        if (coloured.has(p.name)) producesColoured = true;
      }
    }
    // What the executor itself writes into a coloured place on timeout: a copy of a consumed
    // value (forward) or a unit token (place). Neither is a fresh name.
    const timeoutColoured = timeoutWrites(t).filter(w => coloured.has(w.to));

    let role: Role;
    if (t.matchSpec !== null) {
      // A join may write a coloured place only as a declared relay target (NU-054, EXTENDED);
      // any other coloured output is a re-mint — out of fragment.
      const relayTo = new Set<string>();
      if (mode === 'extended') for (const r of t.matchSpec.relays) relayTo.add(r.place.name);
      if (producesColoured) {
        for (const branch of branches) {
          for (const p of branch.places) {
            if (coloured.has(p.name) && !relayTo.has(p.name)) return null;
          }
        }
      }
      const keyPlaces = new Set(t.matchSpec.keys.map(k => k.place.name));
      // What the executor writes into a relay target on timeout is checked like an action's
      // write (NU-054). Only a forward of a match key carries the matched name. A unit token has
      // none and a forward of another input carries that input's name, so such a firing fails
      // and deposits nothing, while the name layer would relay the matched name.
      if (timeoutColoured.some(w => w.from === null || !keyPlaces.has(w.from))) return null;
      // A coloured place consumed off-key is taken FIFO, whatever its name; the join
      // step only removes the matched name from the keys, so the name layer would keep
      // a symbol the base marking has lost.
      if (colouredInputs.some(s => !keyPlaces.has(s.place.name))) return null;
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
      // By place name in code-point order, as the Rust port sorts them: the join seeds the
      // symbols it enumerates from its first coloured input, which orders the successors.
      colouredIn.sort((a, b) => compareCodePoints(a[0], b[0]));
      role = { type: 'join', colouredIn, relayTo };
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
      const inputPlace = spec.place.name;
      // A timeout deposit relays the consumed name only when it forwards the coloured input
      // itself. A forward of another input copies a name the relay did not consume, and a unit
      // token has none.
      if (timeoutColoured.some(w => w.from !== inputPlace)) return null;
      if (producesColoured) relays.push(t.name);
      role = { type: 'consume', colouredInput: inputPlace };
    } else if (producesColoured) {
      // Minting fork: produces a coloured token, consumes none. Read as a mint only when
      // declared (NU-010), and never when the executor writes a coloured place on timeout.
      if (!mintTransitions.has(t.name) || timeoutColoured.length > 0) return null;
      mints.push(t.name);
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
    mints,
    relays,
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
