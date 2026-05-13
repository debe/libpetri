#!/usr/bin/env node
/**
 * Build the self-contained IIFE bundle of the canonical viewer.
 *
 * Output: typescript/dist/viewer/viewer.iife.js
 *
 * The bundle inlines:
 *  - @viz-js/viz (which itself ships the Graphviz WASM as a base64 blob
 *    inside the JS, so no sidecar .wasm file is required), and
 *  - panzoom (small DOM library).
 *
 * Exposes:
 *   window.LibpetriViewer = { mount, discoverClusters, colorForPrefix,
 *                             DEFAULT_PANZOOM_OPTS, VIEWER_CSS_VARIABLES };
 *
 * This bundle is what the Java/Rust doc-generators embed (as
 * `petrinet-diagrams.js`). It must work offline — no CDN fetches, no
 * external WASM file. Verified by inspecting node_modules/@viz-js/viz/dist:
 * `viz-global.js` is a 1.4MB single file with the WASM payload embedded as
 * a base64 string; esbuild bundles it intact.
 *
 * We also copy the canonical CSS to dist/viewer/viewer.css so consumers
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

// Small adapter so the IIFE bundle exposes the public surface on window.
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

// Remove the throw-away entry shim now that esbuild has consumed it.
rmSync(entryShim, { force: true });

// Copy the canonical CSS next to the IIFE.
copyFileSync(
  join(tsRoot, 'src', 'viewer', 'resources', 'viewer.css'),
  join(outDir, 'viewer.css'),
);

console.log('Built', join(outDir, 'viewer.iife.js'));
console.log('Built', join(outDir, 'viewer.css'));
