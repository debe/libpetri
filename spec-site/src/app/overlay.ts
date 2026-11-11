/**
 * Modal layers: search, keyboard help and drawers. One stack; `Esc` closes the innermost layer;
 * focus moves into a layer when it opens, `Tab` stays inside it, and focus returns to the
 * element that opened it when it closes. Layers never change the route; the shell closes them
 * all on a route change.
 *
 * Owner: skeleton (core).
 */
import { h, listen } from './dom.js';

export interface OverlayOptions {
  /** Accessible name of the dialog. */
  readonly label: string;
  /** BEM block of the panel, e.g. `search` gives `.overlay.overlay--search > .search`. */
  readonly block: string;
  readonly content: Node;
  /** Element to focus on open; the first focusable element otherwise. */
  readonly initialFocus?: HTMLElement;
  readonly onClose?: () => void;
}

export interface OverlayHandle {
  readonly panel: HTMLElement;
  close(): void;
}

const stack: OverlayHandle[] = [];

const FOCUSABLE = 'a[href], button:not([disabled]), input:not([disabled]), select:not([disabled]), textarea:not([disabled]), [tabindex]:not([tabindex="-1"])';

function focusables(root: HTMLElement): HTMLElement[] {
  return Array.from(root.querySelectorAll<HTMLElement>(FOCUSABLE)).filter((el) => !el.hasAttribute('hidden'));
}

export function openOverlay(options: OverlayOptions): OverlayHandle {
  const opener = document.activeElement instanceof HTMLElement ? document.activeElement : null;
  const panel = h('div', { class: options.block, role: 'dialog', 'aria-modal': 'true', 'aria-label': options.label, tabindex: -1 }, options.content);
  const backdrop = h('div', { class: 'overlay__backdrop' });
  const layer = h('div', { class: ['overlay', `overlay--${options.block}`] }, backdrop, panel);

  const stopKeys = listen(layer, 'keydown', (e) => {
    if (e.key === 'Escape') {
      e.preventDefault();
      e.stopPropagation();
      handle.close();
    } else if (e.key === 'Tab') {
      const items = focusables(panel);
      const first = items[0];
      const last = items[items.length - 1];
      if (first === undefined || last === undefined) {
        e.preventDefault();
        return;
      }
      if (e.shiftKey && document.activeElement === first) {
        e.preventDefault();
        last.focus();
      } else if (!e.shiftKey && document.activeElement === last) {
        e.preventDefault();
        first.focus();
      }
    }
  });

  const handle: OverlayHandle = {
    panel,
    close(): void {
      if (!layer.isConnected) return;
      stopKeys();
      layer.remove();
      const i = stack.indexOf(handle);
      if (i >= 0) stack.splice(i, 1);
      if (opener?.isConnected) opener.focus();
      options.onClose?.();
    },
  };
  listen(backdrop, 'click', () => handle.close());

  document.body.append(layer);
  stack.push(handle);
  (options.initialFocus ?? focusables(panel)[0] ?? panel).focus();
  return handle;
}

/** True while any layer is open (page shortcuts stay off). */
export function overlayOpen(): boolean {
  return stack.length > 0;
}

/** Closes every layer, innermost first. */
export function closeAllOverlays(): void {
  for (const layer of [...stack].reverse()) layer.close();
}
