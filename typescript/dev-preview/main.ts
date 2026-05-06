/**
 * Dev-preview entry point.
 *
 * Renders a static DOT file (default: /sample.dot) using the same viz.js +
 * panzoom pipeline that debug-ui consumes via `libpetri/render-dom`. Lets you
 * iterate on `spec/petri-net-styles.json`, the mapper, the renderer, and
 * panzoom config without booting a libpetri server.
 *
 * Iteration loop:
 *   1. Edit spec/styles/mapper/renderer code
 *   2. (If mapper/styles changed) `npm run regenerate-sample`
 *   3. Reload localhost:5173
 *
 * Override the source via `?dot=/path/to/file.dot`.
 */
import { renderDotToContainer } from '../src/render-dom/index.js';

const status = document.getElementById('status') as HTMLDivElement;
const sourceLabel = document.getElementById('source-label') as HTMLSpanElement;
const container = document.getElementById('diagram-container') as HTMLDivElement;

const params = new URLSearchParams(window.location.search);
const dotPath = params.get('dot') ?? '/sample.dot';
sourceLabel.textContent = dotPath;

async function load(): Promise<void> {
  try {
    status.textContent = `fetching ${dotPath}…`;
    const res = await fetch(dotPath);
    if (!res.ok) throw new Error(`${res.status} ${res.statusText}`);
    const dot = await res.text();
    status.textContent = `rendering (${dot.length} bytes)…`;
    await renderDotToContainer(dot, container);
    status.textContent = `rendered ${dotPath} (${dot.length} bytes) — scroll to zoom, drag to pan`;
    status.classList.remove('error');
  } catch (e) {
    status.textContent = `error: ${e instanceof Error ? e.message : String(e)}`;
    status.classList.add('error');
  }
}

void load();

// Auto-reload on Vite HMR for full-page refresh feel
if (import.meta.hot) {
  import.meta.hot.on('vite:beforeUpdate', () => {
    void load();
  });
}
