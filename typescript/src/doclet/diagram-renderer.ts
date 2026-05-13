/**
 * Shared HTML renderer for Petri Net diagrams in TypeDoc.
 *
 * Generates consistent HTML markup that mounts the canonical
 * {@link https://libpetri.org | libpetri} viewer client-side. The viewer IIFE
 * bundle (Graphviz WASM inlined, offline-safe) is inlined into the generated
 * HTML, making the plugin fully self-contained with no external file
 * dependencies.
 *
 * Each diagram container carries its DOT source as a `data-dot` attribute. An
 * init snippet reads the attribute and calls
 * `window.LibpetriViewer.mount(dot, container, { chrome: true })` to render the
 * SVG and wire pan/zoom + cluster legend/filter chrome.
 *
 * Mirrors: `org.libpetri.doclet.DiagramRenderer`
 *
 * @module doclet/diagram-renderer
 */

import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';

const __dirname = dirname(fileURLToPath(import.meta.url));

function loadResource(filename: string): string {
  return readFileSync(join(__dirname, 'resources', filename), 'utf-8');
}

let inlineCss: string | undefined;
let inlineJs: string | undefined;

function css(): string {
  return (inlineCss ??= loadResource('petrinet-diagrams.css'));
}

function js(): string {
  return (inlineJs ??= loadResource('petrinet-diagrams.js'));
}

/**
 * Escapes HTML special characters for safe embedding as text content.
 */
export function escapeHtml(text: string): string {
  return text
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;');
}

/**
 * Escapes a string for safe inclusion in an HTML attribute value enclosed in
 * double quotes. Identical to {@link escapeHtml} plus single-quote escaping
 * (defence-in-depth even though we always emit double-quoted attributes).
 */
function escapeAttr(text: string): string {
  return text
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#39;');
}

/**
 * Renders a diagram from a DOT source string. The viewer renders the SVG
 * client-side via Graphviz-WASM; no server-side SVG is emitted on the
 * embedded path.
 *
 * Inlines CSS and the viewer IIFE from bundled resources. The IIFE is guarded
 * by an idempotency check (`window._libpetriViewerInit`) so it only executes
 * once per page even when multiple `@petrinet` tags appear.
 *
 * @param title - optional title (null/undefined for no title)
 * @param dotSource - the DOT source code; embedded as `data-dot` and shown in
 *                    the collapsible "View DOT Source" block
 * @returns HTML markup with diagram controls
 */
export function renderSvg(
  title: string | null | undefined,
  dotSource: string,
): string {
  return renderInternal(title ?? null, /* headerHtml */ null, dotSource);
}

/**
 * Renders a subnet- or instance-aware diagram. Identical to {@link renderSvg}
 * apart from an extra {@code headerHtml} block (the port/channel/params
 * badge bar) prepended above the diagram, and the CSS class
 * {@code subnet-diagram} on the wrapper.
 *
 * @param title       diagram title (e.g. "BoundedBuffer :: b1")
 * @param headerHtml  the HTML produced by {@link import('./subnet-header.js')}
 * @param dotSource   the DOT source code
 * @returns HTML markup
 */
export function renderSubnetSvg(
  title: string | null | undefined,
  headerHtml: string,
  dotSource: string,
): string {
  return renderInternal(title ?? null, headerHtml, dotSource);
}

let diagramIdCounter = 0;

function renderInternal(
  title: string | null,
  headerHtml: string | null,
  dotSource: string,
): string {
  const titleHtml = title !== null ? `<h4>${escapeHtml(title)}</h4>\n` : '';
  const summaryText = title !== null ? 'View DOT Source' : 'View Source';
  const diagramClass = headerHtml !== null ? 'petrinet-diagram subnet-diagram' : 'petrinet-diagram';
  const headerBlock = headerHtml !== null ? headerHtml : '';
  const dotAttr = escapeAttr(dotSource);
  const containerId = `libpetri-diagram-${++diagramIdCounter}`;

  return `<style>${css()}</style>
<script>if(!window._libpetriViewerInit){window._libpetriViewerInit=true;
${js()}
}</script>
<div class="${diagramClass}">
${titleHtml}${headerBlock}<div class="diagram-container" id="${containerId}" data-libpetri-diagram="true" data-dot="${dotAttr}"></div>
<details>
<summary>${summaryText}</summary>
<pre><code>${escapeHtml(dotSource)}</code></pre>
</details>
</div>
<script>(function(){function mount(){var el=document.getElementById(${JSON.stringify(containerId)});if(!el)return;if(el.dataset.libpetriMounted)return;if(!window.LibpetriViewer||typeof window.LibpetriViewer.mount!=='function'){return setTimeout(mount,30);}el.dataset.libpetriMounted='1';try{window.LibpetriViewer.mount(el.dataset.dot,el,{chrome:true});}catch(e){console.error('[libpetri] mount failed',e);}}if(document.readyState==='loading'){document.addEventListener('DOMContentLoaded',mount);}else{mount();}})();</script>`;
}
