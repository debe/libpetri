#!/usr/bin/env node
/**
 * Build the self-contained IIFE bundle of the canonical viewer.
 *
 * Output:
 *  - typescript/dist/viewer/viewer.iife.js
 *      Inlines @viz-js/viz (Graphviz WASM as a base64 blob inside the JS,
 *      no sidecar .wasm needed) and panzoom. ~1.5 MB.
 *      Exposes `window.LibpetriViewer`.
 *
 * Also copies the canonical CSS to dist/viewer/viewer.css so consumers
 * can ship it alongside the JS bundle.
 */
import { build } from 'esbuild';
import { copyFileSync, mkdirSync, rmSync, writeFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';

const here = dirname(fileURLToPath(import.meta.url));
const tsRoot = join(here, '..');
const outDir = join(tsRoot, 'dist', 'viewer');
mkdirSync(outDir, { recursive: true });

const banner = `/*! libpetri viewer (IIFE) — generated, do not edit; source: typescript/src/viewer/ */`;

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

copyFileSync(
  join(tsRoot, 'src', 'viewer', 'resources', 'viewer.css'),
  join(outDir, 'viewer.css'),
);

console.log('Built', join(outDir, 'viewer.iife.js'));
console.log('Built', join(outDir, 'viewer.css'));
