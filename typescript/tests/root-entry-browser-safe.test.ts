/**
 * The root `libpetri` entry must stay loadable in a browser.
 *
 * `src/index.ts` exports core, runtime and event only, and the package map
 * publishes it without a `node` condition, so bundlers such as Vite hand it to
 * the browser. tsup code-splits the entries into shared `chunk-*.js` files, so
 * one static import from core into `verification/` is enough to put
 * `z3-process.ts` (and its `node:child_process`) into a chunk the root entry
 * loads. That is how debug-ui stopped booting under `vite dev`: the module
 * graph evaluated, touched `child_process.spawn`, and threw before `main.ts`
 * ran.
 *
 * This walks the static-import graph of the BUILT `dist/index.js` and fails if
 * any file reachable from it imports a Node builtin. Dynamic `import()` is
 * ignored on purpose: a lazily loaded verifier is fine, since the browser never
 * evaluates it unless it is called.
 *
 * Needs `npm run build` first (CI builds before `npm test`); skips when
 * `dist/index.js` is missing.
 */

import { describe, expect, it } from 'vitest';
import { existsSync, readFileSync } from 'node:fs';
import { dirname, relative, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const here = dirname(fileURLToPath(import.meta.url));
const distDir = resolve(here, '../dist');
const entry = resolve(distDir, 'index.js');

const NODE_BARE = new Set(['child_process', 'fs', 'path', 'fs/promises', 'os', 'crypto', 'url', 'worker_threads']);

/**
 * Static import/export-from specifiers of an ESM file. Matches
 * `import ... from 'x'`, `import 'x'` and `export ... from 'x'`, but not
 * `import('x')`.
 */
function staticSpecifiers(source: string): string[] {
  const out: string[] = [];
  const re = /(?:^|[;\n}])\s*(?:import|export)\s*(?:[\w*${}\s,]+?\s*from\s*)?(['"])([^'"]+)\1/g;
  for (const m of source.matchAll(re)) out.push(m[2]!);
  return out;
}

function isNodeBuiltin(spec: string): boolean {
  return spec.startsWith('node:') || NODE_BARE.has(spec);
}

describe.skipIf(!existsSync(entry))('root entry (dist/index.js) is browser-safe', () => {
  it('reaches no Node builtin through static imports', () => {
    const offenders: string[] = [];
    const seen = new Set<string>();
    const queue: Array<{ file: string; via: string[] }> = [{ file: entry, via: [] }];

    while (queue.length > 0) {
      const { file, via } = queue.shift()!;
      if (seen.has(file)) continue;
      seen.add(file);
      const chain = [...via, relative(distDir, file)];
      for (const spec of staticSpecifiers(readFileSync(file, 'utf-8'))) {
        if (isNodeBuiltin(spec)) {
          offenders.push(`${chain.join(' -> ')} imports '${spec}'`);
        } else if (spec.startsWith('./') || spec.startsWith('../')) {
          queue.push({ file: resolve(dirname(file), spec), via: chain });
        }
      }
    }

    expect(seen.size).toBeGreaterThan(1); // sanity: the walker followed at least one chunk
    expect(offenders, 'Node builtins reachable from the root entry').toEqual([]);
  });
});

if (!existsSync(entry)) {
  // eslint-disable-next-line no-console
  console.warn('root-entry-browser-safe: dist/index.js missing, run `npm run build` first; skipping.');
}
