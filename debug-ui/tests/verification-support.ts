/**
 * Shared by the `*-verification.test.ts` files: the real debug-ui net, and slices of it.
 *
 * The verification tests prove properties of the transitions `buildDebugNet()` returns, not of
 * a hand-copied model, so a change to an arc in definition.ts is a change to what is proven.
 * Actions never run under a verifier; only places, arcs and output specs are read.
 */
import { PetriNet, type Place, type Transition } from 'libpetri';
import { SmtVerifier, alwaysAvailable, type MarkingStateBuilder, type SmtProperty } from 'libpetri/verification';
import { buildDebugNet } from '../src/net/definition.js';
import * as p from '../src/net/places.js';

export const Z3_TIMEOUT = 120_000;

/** The net the UI runs. */
export function debugNet(): PetriNet {
  return buildDebugNet().net;
}

/** The token counts `buildDebugNet()` seeds, read off its `initialTokens`. */
export function seedInitialMarking(m: MarkingStateBuilder): void {
  for (const [place, tokens] of buildDebugNet().initialTokens) m.tokens(place, tokens.length);
}

/** Every place a transition has an arc on, of any kind. */
export function placesOf(t: Transition): Set<string> {
  const names = new Set<string>();
  for (const place of t.inputPlaces()) names.add(place.name);
  for (const place of t.outputPlaces()) names.add(place.name);
  for (const place of t.readPlaces()) names.add(place.name);
  for (const arc of t.inhibitors) names.add(arc.place.name);
  for (const arc of t.resets) names.add(arc.place.name);
  return names;
}

/** The subnet of `net`'s own transitions that have an arc on one of `places`, minus `except`. */
export function sliceTouching(net: PetriNet, name: string, places: readonly Place<unknown>[], except: readonly string[] = []): PetriNet {
  const wanted = new Set(places.map(place => place.name));
  const picked = [...net.transitions].filter(t =>
    !except.includes(t.name) && [...placesOf(t)].some(placeName => wanted.has(placeName)));
  for (const missing of except.filter(n => ![...net.transitions].some(t => t.name === n))) {
    throw new Error(`no transition named ${missing} in ${net.name}`);
  }
  return PetriNet.builder(name).transitions(...picked).build();
}

/** The subnet of `net`'s own transitions with these names. */
export function sliceNamed(net: PetriNet, name: string, ...transitionNames: string[]): PetriNet {
  const byName = new Map([...net.transitions].map(t => [t.name, t]));
  return PetriNet.builder(name).transitions(...transitionNames.map(n => {
    const t = byName.get(n);
    if (!t) throw new Error(`no transition named ${n} in ${net.name}`);
    return t;
  })).build();
}

/** The places of the message router: the permit, one per protocol message, the dead letter. */
export const routerPlaces: readonly Place<unknown>[] = [
  p.routerReady, ...Object.values(p.messageRoutes) as Place<unknown>[], p.deadLetter,
];

/** The environment places `net` has. */
export function environmentOf(net: PetriNet) {
  const names = new Set([...net.places].map(place => place.name));
  return [...p.allEnvironmentPlaces].filter(env => names.has(env.place.name));
}

/** The verdict on `property`, every environment place of `net` injectable at any time (VER-006). */
export async function check(net: PetriNet, marking: (m: MarkingStateBuilder) => void, property: SmtProperty): Promise<string> {
  const result = await SmtVerifier.forNet(net)
    .initialMarking(marking)
    .environmentPlaces(...environmentOf(net))
    .environmentMode(alwaysAvailable())
    .property(property)
    .timeout(60_000)
    .verify();
  return result.verdict.type;
}
