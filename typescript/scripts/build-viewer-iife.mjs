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
import { copyFileSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';

const here = dirname(fileURLToPath(import.meta.url));
const tsRoot = join(here, '..');
const outDir = join(tsRoot, 'dist', 'viewer');
const { version } = JSON.parse(
  readFileSync(join(tsRoot, 'package.json'), 'utf-8'),
);
mkdirSync(outDir, { recursive: true });

// Banner is pure ASCII on purpose (see the template-literal note below): the
// whole bundle must survive being inlined into a Markdown doc comment.
const banner = `/*! libpetri viewer (IIFE). Generated, do not edit. Source: typescript/src/viewer/ */`;

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
  // Stamps the package version into the bundle (see src/viewer/version.ts) so
  // `window.LibpetriViewer.VERSION` identifies which viewer a doc page embeds.
  define: { __LIBPETRI_VIEWER_VERSION__: JSON.stringify(version) },
  banner: { js: banner },
  minify: true,
  // @viz-js/viz embeds the Graphviz WASM as a template-literal string whose
  // bytes include raw newlines (0x0A). The doc generators inline this bundle as
  // a `<script>` inside a Markdown doc comment, and rustdoc's Markdown renderer
  // collapses runs of raw newlines — silently dropping WASM bytes and producing
  // a "signature index out of range" CompileError in every browser. Lowering
  // template literals to regular strings makes esbuild escape every 0x0A as
  // `\n`, so no raw newline ever lands *inside* a string literal.
  supported: { 'template-literal': false },
  // `lineLimit` then re-introduces newlines, but only at safe inter-token
  // points (never inside a string). This keeps lines short so rustdoc's
  // Markdown parser doesn't scan multi-megabyte lines for HTML tags (which is
  // pathologically slow); these inter-token newlines are insignificant
  // whitespace, so Markdown collapsing them can't corrupt the bundle.
  lineLimit: 400,
  sourcemap: false,
  legalComments: 'none',
  // The viewer module imports @viz-js/viz and panzoom; both must be inlined so
  // the IIFE works offline. No `external:` config; everything in.
  logLevel: 'info',
});

rmSync(entryShim, { force: true });

copyFileSync(
  join(tsRoot, 'src', 'viewer', 'resources', 'viewer.css'),
  join(outDir, 'viewer.css'),
);

console.log('Built', join(outDir, 'viewer.iife.js'));
console.log('Built', join(outDir, 'viewer.css'));
