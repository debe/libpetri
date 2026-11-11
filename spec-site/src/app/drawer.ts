/**
 * The detail drawer (design 3.7): a right side panel (a bottom sheet under 600px) for a
 * glossary term, a defect, a conformance cell or a theorem. Built on `overlay.ts`.
 *
 * Owner: conf + graph agent (initial version by the skeleton). Other views call `openDrawer`.
 */
import { h } from './dom.js';
import { type OverlayHandle, openOverlay } from './overlay.js';

export interface DrawerOptions {
  readonly title: string;
  readonly content: Node;
  readonly onClose?: () => void;
}

export function openDrawer(options: DrawerOptions): OverlayHandle {
  const close = h('button', { type: 'button', class: 'drawer__close', 'aria-label': 'Close' }, '×');
  const content = h('div', { class: 'drawer__inner' },
    h('header', { class: 'drawer__head' }, h('h2', { class: 'drawer__title' }, options.title), close),
    h('div', { class: 'drawer__body' }, options.content),
  );
  const handle = openOverlay({
    label: options.title,
    block: 'drawer',
    content,
    initialFocus: close,
    ...(options.onClose ? { onClose: options.onClose } : {}),
  });
  close.addEventListener('click', () => handle.close());
  return handle;
}
