/**
 * Page shortcuts (design 8.2). Single keys are ignored while focus is in a text field or a
 * range input, while a modifier is held (except Ctrl K / Cmd K) and while an overlay is open.
 * View-local keys (`j`/`k`, `[`/`]`, `i`, player keys) are registered by the view with
 * `viewKeys` and removed in its `dispose`.
 *
 * The list shown in the help overlay is `SHORTCUTS` in `shortcuts.ts`; keep the two in step.
 *
 * Owner: skeleton (core).
 */
import type { AppContext } from './context.js';
import { h, isTypingTarget, listen } from './dom.js';
import { openHelp } from './help.js';
import { overlayOpen } from './overlay.js';
import { currentRoute, R, reqGraph, type Route } from './router.js';
import { openSearch } from './search.js';
import { cycleTheme } from './theme.js';

/** Second key after `g` -> target. `g g` opens the graph of the current rule, if any. */
const GOTO: Readonly<Record<string, () => Route>> = {
  s: () => R.situations(),
  r: () => R.req(),
  c: () => R.conf(),
  g: () => {
    const here = currentRoute();
    return here.view === 'req' && here.id !== null ? reqGraph(here.id) : R.graph();
  },
};

/** How long after `g` the second key counts, in milliseconds. */
export const CHORD_MS = 1200;

/** True when a single-key shortcut should not fire for this event. */
export function ignoreKey(e: KeyboardEvent): boolean {
  if (e.defaultPrevented || e.ctrlKey || e.metaKey || e.altKey || overlayOpen()) return true;
  if (e.target instanceof HTMLInputElement && e.target.type === 'range') return true;
  return isTypingTarget(e.target);
}

/**
 * Registers view-local single-key shortcuts (keys as `KeyboardEvent.key`). Returns the function
 * that removes them; call it from the view's `dispose`.
 */
export function viewKeys(handlers: Readonly<Record<string, (event: KeyboardEvent) => void>>): () => void {
  return listen(document, 'keydown', (e) => {
    if (ignoreKey(e)) return;
    const handler = handlers[e.key];
    if (handler) {
      e.preventDefault();
      handler(e);
    }
  });
}

export function installKeyboard(ctx: AppContext, onTheme: () => void): () => void {
  let pendingG = -1;
  const toast = h('div', { class: 'key-toast', role: 'status', hidden: true }, 'g …');
  document.body.append(toast);
  let toastTimer = 0;
  const clearChord = (): void => {
    pendingG = -1;
    toast.hidden = true;
    clearTimeout(toastTimer);
  };

  const stop = listen(document, 'keydown', (e) => {
    if ((e.ctrlKey || e.metaKey) && !e.altKey && e.key.toLowerCase() === 'k' && !overlayOpen()) {
      e.preventDefault();
      openSearch(ctx);
      return;
    }
    if (ignoreKey(e)) return;
    if (pendingG >= 0) {
      const within = e.timeStamp - pendingG <= CHORD_MS;
      clearChord();
      const target = within ? GOTO[e.key] : undefined;
      if (target) {
        e.preventDefault();
        ctx.navigate(target());
        return;
      }
    }
    switch (e.key) {
      case 'g':
        pendingG = e.timeStamp;
        toast.hidden = false;
        toastTimer = window.setTimeout(clearChord, CHORD_MS);
        break;
      case '/':
        e.preventDefault();
        openSearch(ctx);
        break;
      case '?':
        e.preventDefault();
        openHelp(ctx);
        break;
      case 't':
        e.preventDefault();
        cycleTheme();
        onTheme();
        break;
      default:
        return;
    }
  });
  return () => {
    stop();
    clearChord();
    toast.remove();
  };
}
