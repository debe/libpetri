/**
 * Small shared components (design 3). Owner: skeleton (core); view-specific components stay in
 * the view's own module. Class names follow the CSS conventions (block__element--modifier);
 * their styles are in style.css.
 */
import type { ReqId } from '../model.js';
import type { AppContext, ViewResult } from './context.js';
import { h } from './dom.js';
import { attachHoverCard } from './hovercard.js';
import { href, R } from './router.js';
import type { StatusMeta } from './status.js';

/** The standard view frame: `<section class="view view--<name>">` with its one `<h1>`. */
export function viewFrame(name: string, title: string, ...children: readonly (Node | null)[]): HTMLElement {
  return h('section', { class: ['view', `view--${name}`], 'aria-labelledby': `view-title-${name}` },
    h('h1', { class: 'view__title', id: `view-title-${name}`, tabindex: -1 }, title),
    ...children,
  );
}

/** A view that is not built yet. Stubs return this until their owner fills them in. */
export function comingSoon(name: string, title: string): ViewResult {
  return {
    title,
    node: viewFrame(name, title, h('p', { class: 'view__note' }, 'Coming soon.')),
  };
}

/** Design 3.8 render error card. */
export function errorPanel(title: string, error: unknown): HTMLElement {
  const message = error instanceof Error ? error.message : String(error);
  return h('section', { class: ['view', 'view--error'], role: 'alert' },
    h('h1', { class: 'view__title', tabindex: -1 }, title),
    h('p', { class: 'view__error' }, `${message}. The self-test at #/selftest lists every failing view.`),
  );
}

/**
 * Design 3.1: a requirement ID as a link to its reader page. Removed IDs are struck through,
 * unknown IDs flagged; a rule preview card is attached through `hovercard.ts`.
 */
export function idLink(ctx: AppContext, id: ReqId): HTMLElement {
  const block = ctx.index.blocks.get(id);
  if (block === undefined) {
    return h('a', { class: ['req-id', 'req-id--unknown'], href: href(R.req(id)), title: 'Unknown requirement' }, id);
  }
  const removed = block.status.state === 'removed';
  const link = h('a', { class: ['req-id', removed && 'req-id--removed'], href: href(R.req(id)), title: block.title }, id);
  attachHoverCard(link, () => h('div', { class: 'rule-preview' },
    h('strong', null, `${id} ${block.title}`),
    removed ? h('p', null, 'Removed. Kept as a tombstone.') : null,
  ));
  return link;
}

/** Design 3.2 status badge: glyph + word on the tone's tint; the explanation as tooltip. */
export function statusBadge(meta: StatusMeta, word: string = meta.word): HTMLElement {
  return h('span', { class: ['badge', `badge--${meta.tone}`], title: meta.explain },
    h('span', { class: 'badge__glyph', 'aria-hidden': 'true' }, meta.glyph),
    ' ',
    word,
  );
}
