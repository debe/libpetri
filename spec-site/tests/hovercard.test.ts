// @vitest-environment happy-dom
import { describe, expect, it } from 'vitest';
import { attachHoverCard, hideHoverCard, placeCard } from '../src/app/hovercard.js';

describe('placeCard', () => {
  const view = { width: 400, height: 800 };
  it('goes below the target and stays inside the viewport', () => {
    expect(placeCard({ left: 380, top: 100, bottom: 120 }, { width: 200, height: 100 }, view)).toEqual({ left: 192, top: 126, above: false });
  });
  it('flips above when there is no room below', () => {
    expect(placeCard({ left: 10, top: 700, bottom: 720 }, { width: 200, height: 150 }, view)).toEqual({ left: 10, top: 544, above: true });
  });
});

describe('attachHoverCard', () => {
  it('shows on focus, links the card, hides on Escape without moving focus, detaches', () => {
    const target = document.createElement('button');
    document.body.append(target);
    const detach = attachHoverCard(target, () => document.createTextNode('card text'), { focusDelayMs: 0 });
    target.focus();
    target.dispatchEvent(new FocusEvent('focus'));
    const card = document.querySelector('.hovercard');
    expect(card?.textContent).toBe('card text');
    expect(card?.getAttribute('role')).toBe('tooltip');
    expect(target.getAttribute('aria-describedby')).toBe(card?.id);
    document.dispatchEvent(new KeyboardEvent('keydown', { key: 'Escape', bubbles: true }));
    expect(document.querySelector('.hovercard')).toBeNull();
    expect(target.hasAttribute('aria-describedby')).toBe(false);
    target.dispatchEvent(new FocusEvent('focus'));
    expect(document.querySelector('.hovercard')).not.toBeNull();
    detach();
    expect(document.querySelector('.hovercard')).toBeNull();
    hideHoverCard();
    target.remove();
  });
});
