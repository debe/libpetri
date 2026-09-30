/**
 * Structural helpers shared by gates, sensors and the equivalence check. Pure functions over the
 * public libpetri API; no verification here.
 */
import { PetriNet, Transition as T, one, outPlace, place as mkPlace, type Out, type Place, type Transition, type TransitionAction } from 'libpetri';

/** Action bound to every transition of a design candidate: the net is analysed, never executed. */
export const STRUCTURE_ONLY: TransitionAction = () =>
  Promise.reject(new Error('design candidate: analysed, never executed'));

/** Binds the structure-only action to every transition, so output-spec checks accept the net. */
export function bindStructureOnly(net: PetriNet): PetriNet {
  return net.bindActionsWithResolver(() => STRUCTURE_ONLY);
}

/** Every place an output spec can write to (all branches). */
export function outPlaces(out: Out | null): Set<Place<any>> {
  const acc = new Set<Place<any>>();
  const walk = (o: Out): void => {
    switch (o.type) {
      case 'place': acc.add(o.place); break;
      case 'and': case 'xor': o.children.forEach(walk); break;
      case 'timeout': walk(o.child); break;
      case 'forward-input': acc.add(o.to); break;
    }
  };
  if (out) walk(out);
  return acc;
}

/** Places touched by any arc of the transition, with the arc kind. */
export function arcs(t: Transition): Array<{ kind: 'in' | 'out' | 'inhibitor' | 'read' | 'reset'; place: Place<any> }> {
  const l: Array<{ kind: 'in' | 'out' | 'inhibitor' | 'read' | 'reset'; place: Place<any> }> = [];
  for (const i of t.inputSpecs) l.push({ kind: 'in', place: i.place });
  for (const p of outPlaces(t.outputSpec)) l.push({ kind: 'out', place: p });
  for (const a of t.inhibitors) l.push({ kind: 'inhibitor', place: a.place });
  for (const a of t.reads) l.push({ kind: 'read', place: a.place });
  for (const a of t.resets) l.push({ kind: 'reset', place: a.place });
  return l;
}

/** All places the net declares or any arc touches, by name. */
export function allPlaces(net: PetriNet): Map<string, Place<any>> {
  const m = new Map<string, Place<any>>();
  for (const p of net.places) m.set(p.name, p);
  for (const t of net.transitions) for (const a of arcs(t)) m.set(a.place.name, a.place);
  return m;
}

export function placeByName(net: PetriNet, name: string): Place<any> {
  const p = allPlaces(net).get(name);
  if (!p) throw new Error(`place '${name}' does not exist in net '${net.name}'`);
  return p;
}

/** Transitions sorted by name: every module iterates in this order so results are deterministic. */
export function sortedTransitions(net: PetriNet): Transition[] {
  return [...net.transitions].sort((a, b) => (a.name < b.name ? -1 : a.name > b.name ? 1 : 0));
}

/**
 * Subnet membership by node name. Uses `net.subnetOf(name)` (MOD-040 `auto` rule: recorded
 * membership, else the instance prefix before the last `/`, so nested instances resolve to the
 * innermost one) when it answers. A prefix counts as a subnet only if transitions live in it (or in
 * a subnet nested inside it): instances have transitions, while a naming convention for places (an
 * observation interface like `s1/obs/…`) does not, so such a place climbs to the nearest enclosing
 * instance. Without any answer the first-segment transition prefix is the fallback.
 */
export function membership(net: PetriNet): Map<string, string> {
  const m = new Map<string, string>(net.subnetMembership);
  const parent = (s: string) => (s.includes('/') ? s.slice(0, s.lastIndexOf('/')) : undefined);
  const instances = new Set<string>();
  for (const t of net.transitions) {
    for (let s: string | undefined = net.subnetOf(t.name) ?? parent(t.name); s !== undefined; s = parent(s)) instances.add(s);
  }
  const names = [...net.transitions].map(t => t.name).concat([...allPlaces(net).keys()]);
  for (const n of names) {
    if (m.has(n)) continue;
    let s: string | undefined = net.subnetOf(n) ?? parent(n);
    while (s !== undefined && !instances.has(s)) s = parent(s);
    if (s !== undefined) m.set(n, s);
  }
  return m;
}

/** Whether a node of subnet `member` lies inside subnet `subnet` (the same subnet or one nested in it). */
export function insideSubnet(member: string | undefined, subnet: string): boolean {
  return member !== undefined && (member === subnet || member.startsWith(subnet + '/'));
}

/** Sorted arc signature of a transition (arc kind + place name), names of the transition excluded. */
export function signature(t: Transition): string[] {
  return arcs(t).map(a => `${a.kind}:${a.place.name}`).sort();
}

/**
 * Name patterns in contracts: an asterisk matches any run of characters (including the slash), so
 * the pattern `s*` + `/SOURCE` names every session's source. Exact names pass through unchanged even when absent, so
 * missing-place checks still fire; a pattern that matches nothing is also returned as-is.
 */
export function globRegex(pattern: string): RegExp {
  const esc = pattern.split('*').map(s => s.replace(/[.+?^${}()|[\]\\]/g, '\\$&'));
  return new RegExp('^' + esc.join('(.*)') + '$');
}

export function expandNames(patterns: readonly string[], names: Iterable<string>): string[] {
  const all = [...names];
  const out: string[] = [];
  for (const p of patterns) {
    if (!p.includes('*')) { out.push(p); continue; }
    const re = globRegex(p);
    const hits = all.filter(n => re.test(n)).sort();
    if (hits.length === 0) out.push(p); else out.push(...hits);
  }
  return [...new Set(out)];
}

/** Matches of a pattern with their captured `*` segments joined by '|': used to pair per-unit places. */
export function globMatches(pattern: string, names: Iterable<string>): Map<string, string> {
  const re = globRegex(pattern);
  const m = new Map<string, string>();
  for (const n of names) { const r = re.exec(n); if (r) m.set(r.slice(1).join('|'), n); }
  return m;
}


/**
 * Drives the contract's environment inputs: for every matching input place P, adds a supply place
 * `P__supply` holding the scale's token count and an `P__arrive` transition moving one token into P.
 * Returns the wrapped net, the extended marking and the supply place names (the accounting sources).
 *
 * When the design tests P with an inhibitor, reset or drain, libpetri verifies `P__arrive` in two
 * steps like any transition whose output is tested that way (VER-004). That is sound, and costs
 * only the extra states: the in-flight arrival looks to the design like one not yet made. It cannot
 * be avoided here: every gadget that writes P is split for the same reason, and libpetri's own
 * `arrivals(min, max)` mode, whose injections stay atomic, takes one count for all environment
 * places where a contract may give each input its own.
 */
export function withArrivals(
  net: PetriNet,
  marking: ReadonlyMap<string, number>,
  inputs: ReadonlyArray<{ readonly place: string; readonly tokens: 'k' | number }> | undefined,
  k: number,
): { net: PetriNet; marking: ReadonlyMap<string, number>; supplies: string[] } {
  if (!inputs || inputs.length === 0) return { net, marking, supplies: [] };
  const places = allPlaces(net);
  const m = new Map(marking);
  const supplies: string[] = [];
  const b = PetriNet.builder(net.name);
  for (const p of net.places) b.place(p);
  const extra: Transition[] = [];
  for (const inp of inputs) {
    for (const name of expandNames([inp.place], places.keys())) {
      const target = places.get(name);
      if (!target) throw new Error(`contract input '${name}' is not a place of the net`);
      const supply = mkPlace<unknown>(`${name}__supply`);
      extra.push(T.builder(`${name}__arrive`).inputs(one(supply)).outputs(outPlace(target)).action(STRUCTURE_ONLY).build());
      m.set(supply.name, inp.tokens === 'k' ? k : inp.tokens);
      supplies.push(supply.name);
    }
  }
  b.transitions(...net.transitions, ...extra);
  return { net: b.build(), marking: m, supplies };
}
