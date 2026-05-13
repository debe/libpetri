import type { PetriNet } from './petri-net.js';
import type { SubnetDef } from './subnet-def.js';

/**
 * Discriminated sum-type abstraction over Petri nets, distinguishing **closed**
 * (runnable) nets from **open** (composable) subnet fragments per
 * `spec/11-modular-composition.md` requirement **MOD-002**.
 *
 * This abstraction is the bridge between the existing flat {@link PetriNet}
 * world and the modular composition extension. Code that wishes to accept
 * "any net" types its parameter as `Subnet`; code that needs a runnable net
 * continues to take {@link PetriNet} (or `Subnet` narrowed to `'closed'`);
 * code that needs an open fragment takes {@link SubnetDef} (or `Subnet`
 * narrowed to `'open'`). Misuse is rejected at compile time wherever
 * TypeScript's structural typing permits.
 *
 * Use the literal `kind` field for exhaustive pattern matching:
 *
 * ```ts
 * function classify(s: Subnet): string {
 *   switch (s.kind) {
 *     case 'closed': return `closed:${s.net.name}`;
 *     case 'open':   return `open:${s.def.name}`;
 *   }
 * }
 * ```
 */
export type Subnet =
  | { readonly kind: 'closed'; readonly net: PetriNet }
  | { readonly kind: 'open'; readonly def: SubnetDef<unknown> };

/** Wraps a {@link PetriNet} as a closed (runnable) {@link Subnet}. */
export function closedSubnet(net: PetriNet): Subnet {
  return { kind: 'closed', net };
}

/** Wraps a {@link SubnetDef} as an open (composable) {@link Subnet}. */
export function openSubnet(def: SubnetDef<unknown>): Subnet {
  return { kind: 'open', def };
}
