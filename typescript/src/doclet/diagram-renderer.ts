/**
 * Shared HTML renderer for Petri Net diagrams in TypeDoc.
 *
 * Generates consistent HTML markup with interactive controls for zoom, pan,
 * and fullscreen functionality. Accepts pre-rendered SVG from `@viz-js/viz`.
 *
 * CSS and JS are loaded from bundled resources and inlined into the generated
 * HTML, making the plugin fully self-contained with no external file dependencies.
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
 * Escapes HTML special characters for safe embedding.
 */
export function escapeHtml(text: string): string {
  return text
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;');
}

/**
 * Renders a pre-built SVG diagram with an optional title.
 *
 * Inlines CSS and JS from bundled resources. The JS is guarded by an
 * idempotency check so it only executes once per page, even when multiple
 * `@petrinet` tags appear.
 *
 * @param title - optional title (null/undefined for no title)
 * @param svgContent - the SVG markup
 * @param dotSource - the DOT source code for display in a collapsible block
 * @returns HTML markup with diagram controls
 */
export function renderSvg(
  title: string | null | undefined,
  svgContent: string,
  dotSource: string,
): string {
  const titleHtml = title ? `<h4>${escapeHtml(title)}</h4>\n` : '';
  const summaryText = title ? 'View DOT Source' : 'View Source';

  return `<style>${css()}</style>
<script>if(!window._petriNetDiagramsInit){window._petriNetDiagramsInit=true;
${js()}
}</script>
<div class="petrinet-diagram">
${titleHtml}<div class="diagram-container">
<div class="diagram-controls">
<button class="diagram-btn btn-reset" title="Reset zoom">Reset</button>
<button class="diagram-btn btn-fullscreen" onclick="PetriNetDiagrams.toggleFullscreen(this)">Fullscreen</button>
</div>
${svgContent}
</div>
<details>
<summary>${summaryText}</summary>
<pre><code>${escapeHtml(dotSource)}</code></pre>
</details>
</div>`;
}
