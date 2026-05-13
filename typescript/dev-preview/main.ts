/**
 * Dev-preview entry point.
 *
 * Renders a static DOT file (default: /sample.dot) using the canonical
 * libpetri viewer (`libpetri/viewer`). Same module that ships in debug-ui,
 * the Java doclet, and the Rustdoc embed — so this surface exercises the
 * built-in legend, filter strip, click-to-collapse, and unified panzoom.
 *
 * Iteration loop:
 *   1. Edit spec/styles/mapper/renderer/viewer code
 *   2. (If mapper/styles changed) `npm run regenerate-sample`
 *   3. Reload localhost:5173
 *
 * Override the source via `?dot=/path/to/file.dot`.
 */
import { mount, type ViewerHandle } from '../src/viewer/index.js';
import '../src/viewer/resources/viewer.css';

const status = document.getElementById('status') as HTMLDivElement;
const sourceLabel = document.getElementById('source-label') as HTMLSpanElement;
const container = document.getElementById('diagram-container') as HTMLDivElement;

const params = new URLSearchParams(window.location.search);
const dotPath = params.get('dot') ?? '/sample.dot';
sourceLabel.textContent = dotPath;

let currentHandle: ViewerHandle | null = null;

async function load(): Promise<void> {
  try {
    status.textContent = `fetching ${dotPath}…`;
    const res = await fetch(dotPath);
    if (!res.ok) throw new Error(`${res.status} ${res.statusText}`);
    const dot = await res.text();
    status.textContent = `rendering (${dot.length} bytes)…`;
    const previousHandle = currentHandle;
    currentHandle = null;
    const nextHandle = await mount(dot, container, {
      previousHandle,
      panzoom: { minZoom: 0.02, maxZoom: 1000 },
      chrome: true,
    });
    currentHandle = nextHandle;
    status.textContent = `rendered ${dotPath} (${dot.length} bytes) — scroll to zoom, drag to pan, click a cluster ribbon to collapse`;
    status.classList.remove('error');
  } catch (e) {
    if (currentHandle) {
      currentHandle.dispose();
      currentHandle = null;
    }
    status.textContent = `error: ${e instanceof Error ? e.message : String(e)}`;
    status.classList.add('error');
  }
}

void load();

// Auto-reload on Vite HMR for full-page refresh feel. The viewer's
// `previousHandle` option preserves pan/zoom + cluster state across reloads.
if (import.meta.hot) {
  import.meta.hot.on('vite:beforeUpdate', () => {
    void load();
  });
}
