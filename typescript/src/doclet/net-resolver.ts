/**
 * Dynamic import-based PetriNet resolver for TypeDoc.
 *
 * TypeScript cannot use reflection like Java — modules must be importable
 * at doc time (from `dist/` after `npm run build`).
 *
 * Tag format:
 * ```
 * @petrinet ./path/to/module#exportName      — access a PetriNet constant
 * @petrinet ./path/to/module#functionName()  — call a function returning PetriNet
 * @petrinet #localExport                     — resolve from same file
 * ```
 *
 * Mirrors: `org.libpetri.doclet.PetriNetTaglet.resolvePetriNet()`
 *
 * @module doclet/net-resolver
 */

import { resolve, dirname } from 'node:path';
import { pathToFileURL } from 'node:url';
import type { PetriNet } from '../core/petri-net.js';

export interface ResolvedNet {
  readonly net: PetriNet;
  readonly title: string;
}

/**
 * Parses a `@petrinet` reference and resolves the PetriNet via dynamic import.
 *
 * @param reference - the tag content, e.g. `./definition#buildDebugNet()`
 * @param sourceFilePath - absolute path to the source file containing the tag
 * @returns the resolved PetriNet with title, or null on failure
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

  // Resolve module path relative to the source file
  let absolutePath: string;
  if (modulePath) {
    absolutePath = resolve(dirname(sourceFilePath), modulePath);
  } else {
    // #localExport — resolve from same file's compiled output
    absolutePath = sourceFilePath;
  }

  // Try .js extension for compiled output, then .ts for ts-node scenarios
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
      // Try next candidate
    }
  }

  if (!mod) return null;

  const exported = mod[exportName];
  if (exported == null) return null;

  let net: PetriNet;
  if (isCall) {
    if (typeof exported !== 'function') return null;
    const result = exported() as PetriNet | { net: PetriNet };
    // Support functions that return { net: PetriNet, ... }
    net = 'net' in result ? result.net : result;
  } else {
    net = exported as PetriNet;
  }

  // Validate it looks like a PetriNet (has name and transitions)
  if (typeof net?.name !== 'string' || !(net?.transitions instanceof Set)) {
    return null;
  }

  return { net, title: net.name };
}
