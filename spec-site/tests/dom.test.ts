// @vitest-environment happy-dom
import { describe, expect, it } from 'vitest';
import { h, s } from '../src/app/dom.js';

describe('h', () => {
  it('sets text as text, never as markup', () => {
    const el = h('p', { class: ['a', false, ['b']], 'data-x': 1, hidden: false }, '<b>x</b>', 2);
    expect(el.textContent).toBe('<b>x</b>2');
    expect(el.querySelector('b')).toBeNull();
    expect(el.getAttribute('class')).toBe('a b');
    expect(el.getAttribute('data-x')).toBe('1');
    expect(el.hasAttribute('hidden')).toBe(false);
  });

  it('wires typed listeners', () => {
    let clicks = 0;
    const b = h('button', { type: 'button', on: { click: () => clicks++ } });
    b.click();
    expect(clicks).toBe(1);
  });

  it('creates SVG elements in the SVG namespace', () => {
    expect(s('circle', { r: 3 }).namespaceURI).toBe('http://www.w3.org/2000/svg');
  });
});
