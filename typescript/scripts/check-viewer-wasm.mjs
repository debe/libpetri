#!/usr/bin/env node
/**
 * Validate the Graphviz-WASM baked into the built viewer IIFE.
 *
 * The viewer bundle (typescript/dist/viewer/viewer.iife.js) inlines
 * @viz-js/viz, whose Emscripten Graphviz module is embedded as a JS string and
 * decoded at runtime. A corrupt / truncated bake produces a structurally
 * invalid WASM (e.g. "signature index out of range") that fails to instantiate
 * in every browser, but only at first render, so it slips through unit tests
 * that mock @viz-js/viz. This script is the build-time gate that catches it.
 *
 * Three independent checks, all browser-free (Node ships WebAssembly):
 *
 *   1. Functional  — import @viz-js/viz, instantiate it, render a tiny graph.
 *                    Proves the *pinned* viz version actually works end to end.
 *   2. Structural  — load the *built artifact*, capture the exact bytes it hands
 *                    to WebAssembly.instantiate, and assert WebAssembly.validate
 *                    on them. Proves the bundling/minify step didn't corrupt the
 *                    embedded module.
 *   3. Markdown    — the doc generators inline this bundle into a Markdown doc
 *                    comment; rustdoc's renderer can collapse runs of raw
 *                    newlines. Re-run the structural check on a newline-collapsed
 *                    copy and assert the WASM still validates, so no raw newline
 *                    can ever leak into a string literal again.
 *
 * Exit non-zero on any failure so `npm run build:viewer` (and thus
 * scripts/build-viewer.sh) aborts before a bad bundle is distributed.
 */
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';

const here = dirname(fileURLToPath(import.meta.url));
const iifePath = join(here, '..', 'dist', 'viewer', 'viewer.iife.js');
const realWA = globalThis.WebAssembly;

function fail(msg) {
  console.error(`\n[check-viewer-wasm] FAIL: ${msg}\n`);
  process.exit(1);
}

function hexWindow(bytes, center, span = 24) {
  center = Math.min(center, Math.max(0, bytes.length - 1));
  const lo = Math.max(0, center - span);
  const hi = Math.min(bytes.length, center + span);
  let out = '';
  for (let i = lo; i < hi; i++) out += bytes[i].toString(16).padStart(2, '0') + ' ';
  return `bytes [${lo}, ${hi}): ${out.trim()}`;
}

// ---- Check 1: functional render via the pinned @viz-js/viz ----------------
async function functionalCheck() {
  const { instance } = await import('@viz-js/viz');
  const viz = await instance(); // instantiates the WASM (throws if corrupt)
  const svg = viz.renderString('digraph G { a -> b }', { format: 'svg' });
  if (typeof svg !== 'string' || !svg.includes('<svg')) {
    fail(`@viz-js/viz rendered no <svg> (got ${typeof svg}, len ${svg?.length})`);
  }
  console.log('[check-viewer-wasm] @viz-js/viz instantiated + rendered OK');
}

// Load `code` (the built IIFE, or a transformed copy) under a tolerant DOM
// shim, capture the exact bytes it hands to WebAssembly.instantiate, and return
// them. Browser-free: a WebAssembly Proxy grabs the bytes then short-circuits.
async function captureWasm(code) {
  let captured = null;
  const grab = (arg) => {
    let buf = arg;
    if (arg && arg.buffer) buf = arg.buffer; // TypedArray -> ArrayBuffer
    if (buf instanceof ArrayBuffer) captured ??= new Uint8Array(buf.slice(0));
    else if (arg instanceof Uint8Array) captured ??= new Uint8Array(arg);
  };
  // Any property access returns another node (callable + indexable) so the
  // viewer's top-level + mount() reach the WASM instantiation point.
  const node = () =>
    new Proxy(function () {}, {
      get(_t, p) {
        if (p === 'style' || p === 'dataset' || p === 'classList') return node();
        if (p === Symbol.toPrimitive || p === 'toString') return () => '';
        if (p === 'length') return 0;
        if (p === 'nodeType') return 1;
        return node();
      },
      set() { return true; },
      apply() { return node(); },
      construct() { return node(); },
    });
  const setG = (k, v) => {
    try { globalThis[k] = v; }
    catch { Object.defineProperty(globalThis, k, { value: v, configurable: true, writable: true }); }
  };
  setG('WebAssembly', new Proxy(realWA, {
    get(t, p) {
      if (p === 'instantiate' || p === 'compile' || p === 'validate')
        return (a) => { grab(a); throw new Error('__CAPTURED__'); };
      if (p === 'instantiateStreaming' || p === 'compileStreaming')
        return async () => { throw new Error('__streaming_not_used__'); };
      return Reflect.get(t, p);
    },
  }));
  setG('window', globalThis);
  setG('self', globalThis);
  setG('document', node());
  setG('navigator', { userAgent: 'node', platform: 'node' });
  setG('location', { href: 'file:///check' });
  setG('getComputedStyle', () => node());
  setG('requestAnimationFrame', () => 0);
  setG('fetch', async () => { throw new Error('no fetch in check'); });
  setG('LibpetriViewer', undefined);

  // viz's Emscripten runtime logs "Aborted(...)" to console.error when our
  // capture hook short-circuits instantiation — expected noise; silence it.
  const realError = console.error;
  console.error = () => {};
  try {
    try { (0, eval)(code); } catch { /* top-level DOM pokes may throw; fine */ }
    const V = globalThis.LibpetriViewer;
    const trigger = V && (V.renderDotToSvg || V.mount || V.getViz);
    if (typeof trigger === 'function') {
      try { await trigger('digraph G { a -> b }', node(), { chrome: true }); }
      catch { /* instantiate hook throws __CAPTURED__; expected */ }
    }
  } finally {
    console.error = realError;
  }
  setG('WebAssembly', realWA); // restore before validating
  return { captured, exports: globalThis.LibpetriViewer };
}

// ---- Check 2: validate the WASM embedded in the built IIFE -----------------
async function structuralCheck() {
  let code;
  try {
    code = readFileSync(iifePath, 'utf8');
  } catch {
    fail(`built artifact not found: ${iifePath} (run the IIFE build first)`);
  }
  const { captured, exports } = await captureWasm(code);
  if (!captured) {
    const names = exports ? Object.keys(exports).slice(0, 10).join(', ') : '(none)';
    fail(`could not capture the embedded WASM (LibpetriViewer exports: ${names}). Viewer API changed?`);
  }
  if (!realWA.validate(captured)) {
    console.error(`[check-viewer-wasm] embedded WASM is ${captured.length} bytes`);
    console.error(`[check-viewer-wasm] ${hexWindow(captured, 3360)}`);
    fail('WebAssembly.validate() rejected the embedded module (corrupt bake)');
  }
  console.log(`[check-viewer-wasm] embedded WASM validates OK (${captured.length} bytes)`);
  return code;
}

// ---- Check 3: survive Markdown newline-collapse ----------------------------
async function markdownResilienceCheck(code) {
  const collapsed = code
    .replace(/[ \t]+\n/g, '\n') // trim trailing whitespace per line
    .replace(/\n{2,}/g, '\n');  // collapse blank-line runs (the rustdoc failure)
  const { captured } = await captureWasm(collapsed);
  if (!captured || !realWA.validate(captured)) {
    fail(
      'embedded WASM does not survive Markdown newline-collapse — a raw newline ' +
        'leaked into a string literal. Check the esbuild template-literal lowering ' +
        '/ lineLimit settings in build-viewer-iife.mjs.',
    );
  }
  console.log('[check-viewer-wasm] WASM survives Markdown newline-collapse OK');
}

await functionalCheck();
const code = await structuralCheck();
await markdownResilienceCheck(code);
console.log('[check-viewer-wasm] PASS');
