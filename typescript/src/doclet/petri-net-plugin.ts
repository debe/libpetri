/**
 * TypeDoc plugin for `@petrinet` and `@subnet` tags — auto-generates
 * interactive SVG diagrams from PetriNet / SubnetDef / Instance definitions
 * and embeds them in TypeDoc output.
 *
 * Mirrors: `org.libpetri.doclet.PetriNetTaglet` + `SubnetTaglet`
 *
 * Plugin lifecycle (TypeDoc hooks):
 * 1. `bootstrapEnd` → register `@petrinet` and `@subnet` as known block tags.
 * 2. `preRenderAsyncJobs` → walk reflections, resolve references, generate
 *    SVGs, cache HTML.
 * 3. `comment.beforeTags` → inject cached HTML via `JSX.Raw`, skip default
 *    rendering for the recognised tags.
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
import { resolveNet, type ResolvedNet } from './net-resolver.js';
import { renderSvg, renderSubnetSvg, escapeHtml } from './diagram-renderer.js';
import { forSubnetDef, forInstance } from './subnet-header.js';
import { fullBody as subnetFullBody, interfaceOnly as subnetInterfaceOnly } from './subnet-dot-export.js';

// Lazy import to avoid requiring libpetri/export at module level.
async function getDotExport(): Promise<typeof import('../export/dot-exporter.js').dotExport> {
  const mod = await import('../export/dot-exporter.js');
  return mod.dotExport;
}

/** Block tag for full body diagrams — resolves PetriNet / SubnetDef / Instance. */
const TAG_PETRINET = '@petrinet' as `@${string}`;
/** Block tag for interface-only subnet diagrams. */
const TAG_SUBNET = '@subnet' as `@${string}`;

/** Cache: reflection ID → rendered HTML string */
const htmlCache = new Map<number, string>();

/**
 * Loads the petri-net plugin into the TypeDoc application.
 *
 * @param app - the TypeDoc Application instance
 */
export function load(app: Application): void {
  // 1. Register both tags as known block tags at bootstrap time.
  app.on('bootstrapEnd', () => {
    const blockTags = app.options.getValue('blockTags') as string[];
    const additions: string[] = [];
    if (!blockTags.includes(TAG_PETRINET)) additions.push(TAG_PETRINET);
    if (!blockTags.includes(TAG_SUBNET)) additions.push(TAG_SUBNET);
    if (additions.length > 0) {
      app.options.setValue('blockTags', [...blockTags, ...additions]);
    }
  });

  // 2. Resolve references and generate SVG during pre-render async phase.
  app.renderer.preRenderAsyncJobs.push(async (output) => {
    htmlCache.clear();
    await processProject(app, output.project);
  });

  // 3. Inject cached HTML into comment output, suppress default tag rendering.
  app.renderer.hooks.on('comment.beforeTags', (_context, comment, reflection) => {
    const cached = htmlCache.get(reflection.id);
    if (!cached) return JSX.createElement(JSX.Raw, { html: '' });

    // Mark our tags as skip so TypeDoc doesn't render them as plain text.
    for (const tag of comment.blockTags) {
      if (tag.tag === TAG_PETRINET || tag.tag === TAG_SUBNET) {
        tag.skipRendering = true;
      }
    }

    return JSX.createElement(JSX.Raw, { html: cached });
  });
}

/**
 * Walks all reflections in the project and processes `@petrinet` / `@subnet`
 * tags. Per-reflection HTML accumulates in {@link htmlCache} so multiple tags
 * on one symbol render in declaration order.
 */
async function processProject(app: Application, project: ProjectReflection): Promise<void> {
  const reflections = Object.values(project.reflections);

  for (const reflection of reflections) {
    const comment = reflection.comment;
    if (!comment) continue;

    for (const tag of comment.blockTags) {
      const isPetrinet = tag.tag === TAG_PETRINET;
      const isSubnet = tag.tag === TAG_SUBNET;
      if (!isPetrinet && !isSubnet) continue;

      const reference = tagContent(tag);
      try {
        const html = isSubnet
          ? await generateInterfaceOnly(reference, reflection)
          : await generateDiagram(reference, reflection);
        const existing = htmlCache.get(reflection.id) ?? '';
        htmlCache.set(reflection.id, existing + html);
      } catch (e) {
        const msg = e instanceof Error ? e.message : String(e);
        const tagName = isSubnet ? '@subnet' : '@petrinet';
        app.logger.warn(`${tagName} error for ${reflection.getFriendlyFullName()}: ${msg}`);
        const html = errorHtml(`Error generating diagram for '${reference}': ${msg}`);
        const existing = htmlCache.get(reflection.id) ?? '';
        htmlCache.set(reflection.id, existing + html);
      }
    }
  }
}

/**
 * Generates a diagram HTML string for a single `@petrinet` reference. Resolves
 * the reference to one of {@link ResolvedNet} variants and dispatches to the
 * matching renderer.
 */
async function generateDiagram(
  reference: string,
  reflection: Reflection,
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
    return errorHtml(`Cannot resolve PetriNet/SubnetDef/Instance: ${trimmed}`);
  }

  return await renderResolved(resolved, /* interfaceOnly */ false);
}

/**
 * Generates an interface-only diagram for a `@subnet` reference. When the
 * resolved reference is not a {@link import('../core/subnet-def.js').SubnetDef},
 * falls back to the regular diagram so the tag still produces useful output.
 */
async function generateInterfaceOnly(
  reference: string,
  reflection: Reflection,
): Promise<string> {
  const trimmed = reference.trim();
  if (!trimmed) {
    return errorHtml(`Empty @subnet reference on ${reflection.getFriendlyFullName()}`);
  }

  const sourceFile = getSourceFilePath(reflection);
  if (!sourceFile) {
    return errorHtml(`Cannot determine source file for ${reflection.getFriendlyFullName()}`);
  }

  const resolved = await resolveNet(trimmed, sourceFile);
  if (!resolved) {
    return errorHtml(`Cannot resolve SubnetDef: ${trimmed}`);
  }

  return await renderResolved(resolved, /* interfaceOnly */ true);
}

/**
 * Dispatches a {@link ResolvedNet} to the matching renderer. The
 * `interfaceOnly` flag is honoured only when the resolved kind is `subnet` —
 * for `net` and `instance` it is ignored (the body is the whole point of
 * those references).
 */
async function renderResolved(
  resolved: ResolvedNet,
  interfaceOnly: boolean,
): Promise<string> {
  switch (resolved.kind) {
    case 'net': {
      const dotExport = await getDotExport();
      const dot = dotExport(resolved.value);
      return renderDiagramHtml(resolved.title, dot, /* header */ null);
    }
    case 'subnet': {
      const dot = interfaceOnly
        ? subnetInterfaceOnly(resolved.value)
        : subnetFullBody(resolved.value);
      const header = forSubnetDef(resolved.value, interfaceOnly);
      const title = resolved.value.name + (interfaceOnly ? ' (interface)' : '');
      return renderDiagramHtml(title, dot, header);
    }
    case 'instance': {
      const dotExport = await getDotExport();
      const dot = dotExport(resolved.value.renamedBody);
      const header = forInstance(resolved.value);
      return renderDiagramHtml(resolved.title, dot, header);
    }
  }
}

/**
 * Emits the diagram HTML. The canonical viewer renders DOT to SVG
 * client-side via Graphviz-WASM, so no server-side SVG rendering happens
 * here. Routes through the subnet-aware renderer when `header` is non-null,
 * the plain renderer otherwise.
 */
function renderDiagramHtml(
  title: string,
  dot: string,
  header: string | null,
): string {
  if (header !== null) {
    return renderSubnetSvg(title, header, dot);
  }
  return renderSvg(title, dot);
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
 * Gets the source file path from a reflection. Walks parents because
 * comment-bearing reflections sometimes lack their own `sources` (e.g.
 * inherited members).
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
