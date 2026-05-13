/**
 * Dynamic import-based resolver for `@petrinet` / `@subnet` references.
 *
 * Resolves three kinds of static exports per Java's `PetriNetTaglet` design:
 * 1. `PetriNet` — full body diagram (existing behaviour).
 * 2. `SubnetDef<?>` — body diagram with interface ports highlighted, plus a
 *    subnet header with port/channel badges.
 * 3. `Instance<?>` — renamed body diagram (already prefix-clustered by the
 *    DOT exporter), plus an instance header with prefix, def name, and
 *    params summary.
 *
 * TypeScript cannot use reflection like Java — modules must be importable at
 * doc time (typically from `dist/` after `npm run build`).
 *
 * Tag format:
 * ```
 * @petrinet ./path/to/module#exportName      — access a static export
 * @petrinet ./path/to/module#functionName()  — call a function returning one
 * @petrinet #localExport                     — resolve from same file
 * ```
 *
 * Mirrors: `org.libpetri.doclet.PetriNetTaglet.resolveReference`
 *
 * @module doclet/net-resolver
 */

import { resolve, dirname } from 'node:path';
import { pathToFileURL } from 'node:url';
import type { PetriNet } from '../core/petri-net.js';
import type { SubnetDef } from '../core/subnet-def.js';
import type { Instance } from '../core/instance.js';

/**
 * Discriminated-union result from {@link resolveNet}. Each variant carries
 * the resolved value plus a display title.
 */
export type ResolvedNet =
  | { readonly kind: 'net'; readonly value: PetriNet; readonly title: string }
  | { readonly kind: 'subnet'; readonly value: SubnetDef<unknown>; readonly title: string }
  | { readonly kind: 'instance'; readonly value: Instance<unknown>; readonly title: string };

/**
 * Parses a `@petrinet` / `@subnet` reference and resolves it via dynamic
 * import. Returns `null` when the reference cannot be parsed or imported, or
 * when the resolved value is none of the three supported kinds.
 *
 * @param reference - the tag content, e.g. `./definition#buildDebugNet()`
 * @param sourceFilePath - absolute path to the source file containing the tag
 */
export async function resolveNet(
  reference: string,
  sourceFilePath: string,
): Promise<ResolvedNet | null> {
  const trimmed = reference.trim().split(/\s+/)[0] ?? '';
  if (!trimmed) return null;

  const hashIndex = trimmed.indexOf('#');
  if (hashIndex === -1) return null;

  const modulePath = trimmed.substring(0, hashIndex);
  const exportRef = trimmed.substring(hashIndex + 1);
  if (!exportRef) return null;

  const isCall = exportRef.endsWith('()');
  const exportName = isCall ? exportRef.slice(0, -2) : exportRef;

  // Resolve module path relative to the source file.
  let absolutePath: string;
  if (modulePath) {
    absolutePath = resolve(dirname(sourceFilePath), modulePath);
  } else {
    // `#localExport` — resolve from same file's compiled output.
    absolutePath = sourceFilePath;
  }

  // Try `.js` extension for compiled output, then `.ts` for ts-node scenarios.
  const candidates = [
    absolutePath,
    absolutePath + '.js',
    absolutePath + '.ts',
    absolutePath.replace(/\.ts$/, '.js'),
  ];

  let mod: Record<string, unknown> | undefined;
  for (const candidate of candidates) {
    try {
      mod = await import(pathToFileURL(candidate).href) as Record<string, unknown>;
      break;
    } catch {
      // Try next candidate.
    }
  }

  if (!mod) return null;

  const exported = mod[exportName];
  if (exported == null) return null;

  let value: unknown;
  if (isCall) {
    if (typeof exported !== 'function') return null;
    const result = (exported as (...args: unknown[]) => unknown)();
    // Support functions that return `{ net: PetriNet, ... }` for legacy
    // callers; otherwise pass the result through directly.
    if (
      result !== null && typeof result === 'object' && 'net' in result &&
      isPetriNetLike((result as { net: unknown }).net)
    ) {
      value = (result as { net: unknown }).net;
    } else {
      value = result;
    }
  } else {
    value = exported;
  }

  return classify(value);
}

/**
 * Wraps the resolved value into a {@link ResolvedNet} variant by structural
 * shape — checks {@link Instance} before {@link SubnetDef} before
 * {@link PetriNet} so the most specific match wins (Instance has both `def`
 * and `renamedBody`; SubnetDef has `iface` and `body`; PetriNet has only
 * `transitions` + `name`).
 *
 * Returns `null` when the value matches none of the supported shapes.
 */
function classify(value: unknown): ResolvedNet | null {
  if (value === null || typeof value !== 'object') return null;

  if (isInstanceLike(value)) {
    const inst = value as Instance<unknown>;
    return { kind: 'instance', value: inst, title: `${inst.def.name} :: ${inst.prefix}` };
  }
  if (isSubnetDefLike(value)) {
    const def = value as SubnetDef<unknown>;
    return { kind: 'subnet', value: def, title: def.name };
  }
  if (isPetriNetLike(value)) {
    const net = value as PetriNet;
    return { kind: 'net', value: net, title: net.name };
  }
  return null;
}

/**
 * Structural test for {@link PetriNet}: has a string `name` and a `transitions`
 * Set. Avoids `instanceof` because the imported module may have re-bound the
 * class identity (TypeDoc's bundled output vs `dist/` import path).
 */
function isPetriNetLike(value: unknown): value is PetriNet {
  if (value === null || typeof value !== 'object') return false;
  const candidate = value as { name?: unknown; transitions?: unknown };
  return typeof candidate.name === 'string' && candidate.transitions instanceof Set;
}

/**
 * Structural test for {@link SubnetDef}: has a string `name`, a {@link
 * PetriNet}-shaped `body`, and an `iface` carrying `ports` + `channels` maps.
 */
function isSubnetDefLike(value: unknown): value is SubnetDef<unknown> {
  if (value === null || typeof value !== 'object') return false;
  const candidate = value as { name?: unknown; body?: unknown; iface?: unknown };
  if (typeof candidate.name !== 'string') return false;
  if (!isPetriNetLike(candidate.body)) return false;
  const iface = candidate.iface as { ports?: unknown; channels?: unknown } | undefined;
  return iface !== undefined && iface !== null
    && iface.ports instanceof Map && iface.channels instanceof Map;
}

/**
 * Structural test for {@link Instance}: has a string `prefix`, a {@link
 * SubnetDef}-shaped `def`, and a {@link PetriNet}-shaped `renamedBody`.
 */
function isInstanceLike(value: unknown): value is Instance<unknown> {
  if (value === null || typeof value !== 'object') return false;
  const candidate = value as { prefix?: unknown; def?: unknown; renamedBody?: unknown };
  return typeof candidate.prefix === 'string'
    && isSubnetDefLike(candidate.def)
    && isPetriNetLike(candidate.renamedBody);
}
