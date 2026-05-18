#!/usr/bin/env node
/**
 * Build the self-contained IIFE bundle(s) of the canonical viewer.
 *
 * Outputs:
 *  - typescript/dist/viewer/viewer.iife.js
 *      Full bundle — inlines @viz-js/viz (Graphviz WASM as a base64 blob
 *      inside the JS, no sidecar .wasm needed) and panzoom. ~1.5 MB.
 *      Exposes `window.LibpetriViewer`.
 *  - typescript/dist/viewer/viewer-static.iife.js
 *      Slim bundle — drops @viz-js/viz by aliasing `./render.js` to the
 *      throwing stub `./render-stub.ts`. Intended for pages that ship a
 *      pre-rendered <svg> (Java javadoc taglet running `dot -Tsvg` at
 *      build time). Exposes the SAME `window.LibpetriViewer` global so
 *      the Java init script doesn't need to know which bundle loaded.
 *      Callers must invoke `mount(null, container, opts)`.
 *
 * Also copies the canonical CSS to dist/viewer/viewer.css so consumers
 * can ship it alongside the JS bundle.
 */
import { build } from 'esbuild';
import { copyFileSync, mkdirSync, rmSync, writeFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join, resolve } from 'node:path';

const here = dirname(fileURLToPath(import.meta.url));
const tsRoot = join(here, '..');
const outDir = join(tsRoot, 'dist', 'viewer');
mkdirSync(outDir, { recursive: true });

const banner = `/*! libpetri viewer (IIFE) — generated, do not edit; source: typescript/src/viewer/ */`;

// -- Full bundle --------------------------------------------------------------

const entryShim = join(outDir, '.iife-entry.js');
writeFileSync(
  entryShim,
  `import * as Viewer from '${join(tsRoot, 'src', 'viewer', 'index.ts').replace(/\\/g, '/')}';
globalThis.LibpetriViewer = Viewer;
`,
);

await build({
  entryPoints: [entryShim],
  bundle: true,
  format: 'iife',
  platform: 'browser',
  target: ['es2022'],
  outfile: join(outDir, 'viewer.iife.js'),
  loader: { '.wasm': 'binary' },
  banner: { js: banner },
  minify: true,
  sourcemap: false,
  legalComments: 'none',
  // The viewer module imports @viz-js/viz and panzoom — both must be inlined
  // so the IIFE works offline. No `external:` config; everything in.
  logLevel: 'info',
});

rmSync(entryShim, { force: true });

// -- Slim (static) bundle -----------------------------------------------------

const staticEntryShim = join(outDir, '.iife-entry-static.js');
writeFileSync(
  staticEntryShim,
  `import * as Viewer from '${join(tsRoot, 'src', 'viewer', 'index-static.ts').replace(/\\/g, '/')}';
globalThis.LibpetriViewer = Viewer;
`,
);

// Remap `./render.js` (referenced via dynamic `await import('./render.js')`
// inside `mount()`) to the throwing stub. esbuild's `alias:` config key only
// applies to package specifiers, so we use the documented `onResolve` plugin
// pattern for relative paths. `external: ['@viz-js/viz']` is belt-and-braces:
// if the stub fails to take, esbuild errors out at build time instead of
// silently bundling viz.js.
const renderStubPath = resolve(tsRoot, 'src', 'viewer', 'render-stub.ts');
const renderStubPlugin = {
  name: 'render-stub',
  setup(b) {
    b.onResolve({ filter: /(^|\/)render(\.js)?$/ }, (args) => {
      // Only remap when the import originates inside our viewer directory,
      // so we don't accidentally hijack unrelated `./render` imports from
      // third-party deps. Normalize backslashes so the check works on
      // Windows (where args.importer carries native separators).
      const importerNorm = args.importer.replace(/\\/g, '/');
      if (!importerNorm.includes('src/viewer/')) {
        return null;
      }
      return { path: renderStubPath };
    });
  },
};

await build({
  entryPoints: [staticEntryShim],
  bundle: true,
  format: 'iife',
  platform: 'browser',
  target: ['es2022'],
  outfile: join(outDir, 'viewer-static.iife.js'),
  loader: { '.wasm': 'binary' },
  banner: { js: banner },
  minify: true,
  sourcemap: false,
  legalComments: 'none',
  external: ['@viz-js/viz'],
  plugins: [renderStubPlugin],
  logLevel: 'info',
});

rmSync(staticEntryShim, { force: true });

// -- CSS ----------------------------------------------------------------------

copyFileSync(
  join(tsRoot, 'src', 'viewer', 'resources', 'viewer.css'),
  join(outDir, 'viewer.css'),
);

console.log('Built', join(outDir, 'viewer.iife.js'));
console.log('Built', join(outDir, 'viewer-static.iife.js'));
console.log('Built', join(outDir, 'viewer.css'));
