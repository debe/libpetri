/**
 * Hover cards for glossary terms and requirement links (design 3.6, 10): shown after a short
 * delay on hover and on keyboard focus, hidden on Escape (without moving focus), on blur, and
 * 150 ms after the pointer leaves (the pointer may travel into the card). `aria-describedby`
 * links the card to its target while it shows. One card at a time.
 *
 * Owner: reader + md + search agent.
 */
import { h, listen } from './dom.js';

export interface HoverCardOptions {
  /** Delay before a hover shows the card. Default 300 ms. */
  readonly hoverDelayMs?: number;
  /** Delay before keyboard focus shows the card. Default 300 ms; terms use 0. */
  readonly focusDelayMs?: number;
}

const HIDE_DELAY_MS = 150;
const GAP = 6;
const MARGIN = 8;

interface Active {
  readonly target: HTMLElement;
  readonly card: HTMLElement;
  readonly stop: () => void;
}

let active: Active | null = null;
let serial = 0;

/** Hides the card that shows, if any. */
export function hideHoverCard(): void {
  const a = active;
  if (a === null) return;
  active = null;
  a.stop();
  a.card.remove();
  a.target.removeAttribute('aria-describedby');
}

/**
 * Where a card of `card` size goes for a target at `target` in a viewport of `view` size:
 * below the target, flipped above when it does not fit below and fits above, kept inside the
 * viewport horizontally. Pure.
 */
export function placeCard(
  target: { readonly left: number; readonly top: number; readonly bottom: number },
  card: { readonly width: number; readonly height: number },
  view: { readonly width: number; readonly height: number },
): { readonly left: number; readonly top: number; readonly above: boolean } {
  const below = target.bottom + GAP;
  const aboveTop = target.top - GAP - card.height;
  const above = below + card.height > view.height - MARGIN && aboveTop >= MARGIN;
  const left = Math.max(MARGIN, Math.min(target.left, view.width - card.width - MARGIN));
  return { left, top: above ? aboveTop : below, above };
}

function show(target: HTMLElement, content: () => Node, scheduleHide: () => void, cancelHide: () => void): void {
  if (active?.target === target) return;
  hideHoverCard();
  if (!target.isConnected) return;
  serial += 1;
  const id = `hovercard-${serial}`;
  const card = h('div', { class: 'hovercard', id, role: 'tooltip' }, content());
  document.body.append(card);
  const rect = target.getBoundingClientRect();
  const pos = placeCard(rect, { width: card.offsetWidth, height: card.offsetHeight }, { width: innerWidth, height: innerHeight });
  card.style.left = `${pos.left}px`;
  card.style.top = `${pos.top}px`;
  card.dataset['side'] = pos.above ? 'above' : 'below';
  target.setAttribute('aria-describedby', id);

  const stops = [
    listen(card, 'mouseenter', cancelHide),
    listen(card, 'mouseleave', scheduleHide),
    listen(card, 'focusout', (e) => {
      if (!(e.relatedTarget instanceof Node && (card.contains(e.relatedTarget) || target.contains(e.relatedTarget)))) hideHoverCard();
    }),
    // Capture phase: Esc closes the card before an enclosing drawer or overlay sees it.
    listen(document, 'keydown', (e) => {
      if (e.key !== 'Escape') return;
      e.preventDefault();
      e.stopPropagation();
      hideHoverCard();
    }, { capture: true }),
    listen(window, 'hashchange', hideHoverCard),
    listen(window, 'scroll', hideHoverCard, { capture: true, passive: true }),
    listen(window, 'resize', hideHoverCard),
  ];
  active = { target, card, stop: () => stops.forEach((s) => s()) };
}

/**
 * Attaches a card whose content is built lazily, each time it shows. Returns the function that
 * detaches it (and hides the card if it is this target's).
 */
export function attachHoverCard(target: HTMLElement, content: () => Node, options: HoverCardOptions = {}): () => void {
  const hoverDelay = options.hoverDelayMs ?? 300;
  const focusDelay = options.focusDelayMs ?? 300;
  let showTimer = 0;
  let hideTimer = 0;
  const cancelShow = (): void => clearTimeout(showTimer);
  const cancelHide = (): void => clearTimeout(hideTimer);
  const scheduleHide = (): void => {
    cancelHide();
    hideTimer = window.setTimeout(() => {
      if (active?.target === target) hideHoverCard();
    }, HIDE_DELAY_MS);
  };
  const scheduleShow = (delay: number): void => {
    cancelShow();
    cancelHide();
    const run = (): void => show(target, content, scheduleHide, cancelHide);
    if (delay <= 0) run();
    else showTimer = window.setTimeout(run, delay);
  };
  const stops = [
    listen(target, 'mouseenter', () => scheduleShow(hoverDelay)),
    listen(target, 'mouseleave', () => {
      cancelShow();
      scheduleHide();
    }),
    listen(target, 'focus', () => scheduleShow(focusDelay)),
    listen(target, 'blur', (e) => {
      cancelShow();
      const card = active?.target === target ? active.card : null;
      if (card !== null && e.relatedTarget instanceof Node && card.contains(e.relatedTarget)) return;
      if (active?.target === target) hideHoverCard();
    }),
  ];
  return () => {
    stops.forEach((s) => s());
    cancelShow();
    cancelHide();
    if (active?.target === target) hideHoverCard();
  };
}
