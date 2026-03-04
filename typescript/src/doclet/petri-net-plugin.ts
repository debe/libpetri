/**
 * TypeDoc plugin for `@petrinet` tag — auto-generates interactive SVG diagrams
 * from PetriNet definitions and embeds them in TypeDoc output.
 *
 * Mirrors: `org.libpetri.doclet.PetriNetTaglet`
 *
 * Plugin lifecycle (TypeDoc hooks):
 * 1. `bootstrapEnd` → register `@petrinet` as known block tag
 * 2. `preRenderAsyncJobs` → walk reflections, resolve nets, generate SVGs, cache HTML
 * 3. `comment.beforeTags` → inject cached HTML via JSX.Raw, skip default rendering
 *
 * @module doclet/petri-net-plugin
 */

import {
  type Application,
  type CommentTag,
  type DeclarationReflection,
  type ProjectReflection,
  type Reflection,
  JSX,
} from 'typedoc';
import { resolveNet } from './net-resolver.js';
import { dotToSvg } from './svg-renderer.js';
import { renderSvg, escapeHtml } from './diagram-renderer.js';

// Lazy import to avoid requiring libpetri/export at module level
async function getDotExport(): Promise<typeof import('../export/dot-exporter.js').dotExport> {
  const mod = await import('../export/dot-exporter.js');
  return mod.dotExport;
}

/** Tag name including @ prefix. */
const TAG_NAME = '@petrinet' as `@${string}`;

/** Cache: reflection ID → rendered HTML string */
const htmlCache = new Map<number, string>();

/**
 * Loads the petri-net plugin into the TypeDoc application.
 *
 * @param app - the TypeDoc Application instance
 */
export function load(app: Application): void {
  // 1. Register @petrinet as a known block tag at bootstrap time
  app.on('bootstrapEnd', () => {
    const blockTags = app.options.getValue('blockTags') as string[];
    if (!blockTags.includes(TAG_NAME)) {
      app.options.setValue('blockTags', [...blockTags, TAG_NAME]);
    }
  });

  // 2. Resolve nets and generate SVG during pre-render async phase
  app.renderer.preRenderAsyncJobs.push(async (output) => {
    htmlCache.clear();
    await processProject(app, output.project);
  });

  // 3. Inject cached HTML into comment output, suppress default tag rendering
  app.renderer.hooks.on('comment.beforeTags', (_context, comment, reflection) => {
    const cached = htmlCache.get(reflection.id);
    if (!cached) return JSX.createElement(JSX.Raw, { html: '' });

    // Mark @petrinet tags as skip so TypeDoc doesn't render them as plain text
    for (const tag of comment.blockTags) {
      if (tag.tag === TAG_NAME) {
        tag.skipRendering = true;
      }
    }

    // Inject raw HTML using TypeDoc's JSX
    return JSX.createElement(JSX.Raw, { html: cached });
  });
}

/**
 * Walks all reflections in the project and processes `@petrinet` tags.
 */
async function processProject(app: Application, project: ProjectReflection): Promise<void> {
  const reflections = Object.values(project.reflections);

  for (const reflection of reflections) {
    const comment = reflection.comment;
    if (!comment) continue;

    const petrinetTags = comment.blockTags.filter(
      (tag: CommentTag) => tag.tag === TAG_NAME,
    );
    if (petrinetTags.length === 0) continue;

    for (const tag of petrinetTags) {
      const reference = tagContent(tag);
      try {
        const html = await generateDiagram(reference, reflection, app);
        const existing = htmlCache.get(reflection.id) ?? '';
        htmlCache.set(reflection.id, existing + html);
      } catch (e) {
        const msg = e instanceof Error ? e.message : String(e);
        app.logger.warn(`@petrinet error for ${reflection.getFriendlyFullName()}: ${msg}`);
        const html = errorHtml(`Error generating diagram for '${reference}': ${msg}`);
        const existing = htmlCache.get(reflection.id) ?? '';
        htmlCache.set(reflection.id, existing + html);
      }
    }
  }
}

/**
 * Generates a diagram HTML string for a single `@petrinet` reference.
 */
async function generateDiagram(
  reference: string,
  reflection: Reflection,
  app: Application,
): Promise<string> {
  const trimmed = reference.trim();
  if (!trimmed) {
    return errorHtml(`Empty @petrinet reference on ${reflection.getFriendlyFullName()}`);
  }

  const sourceFile = getSourceFilePath(reflection);
  if (!sourceFile) {
    return errorHtml(`Cannot determine source file for ${reflection.getFriendlyFullName()}`);
  }

  const resolved = await resolveNet(trimmed, sourceFile);
  if (!resolved) {
    return errorHtml(`Cannot resolve PetriNet: ${trimmed}`);
  }

  const dotExport = await getDotExport();
  const dot = dotExport(resolved.net);

  try {
    const svg = await dotToSvg(dot);
    return renderSvg(resolved.title, svg, dot);
  } catch (e) {
    app.logger.warn(`SVG rendering failed, falling back to DOT source: ${e}`);
    return renderSvg(
      resolved.title,
      `<pre><code>${escapeHtml(dot)}</code></pre>`,
      dot,
    );
  }
}

/**
 * Extracts text content from a CommentTag.
 */
function tagContent(tag: CommentTag): string {
  return tag.content
    .map((part) => part.text)
    .join('')
    .trim();
}

/**
 * Gets the source file path from a reflection.
 */
function getSourceFilePath(reflection: Reflection): string | null {
  const decl = reflection as DeclarationReflection;
  if (decl.sources && decl.sources.length > 0) {
    return decl.sources[0]!.fullFileName;
  }
  if (reflection.parent) {
    return getSourceFilePath(reflection.parent);
  }
  return null;
}

/**
 * Renders an error message as styled HTML.
 */
function errorHtml(message: string): string {
  return `<div class="petrinet-error" style="color: #dc3545; border: 1px solid #dc3545; padding: 10px; border-radius: 4px;">
<strong>@petrinet Error:</strong> ${escapeHtml(message)}
</div>`;
}
