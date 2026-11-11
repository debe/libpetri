/**
 * Typed DOM helpers. Text is always set as text nodes and attributes through `setAttribute`,
 * so data is escaped by construction. There is deliberately no way to pass HTML markup:
 * never use `innerHTML`, `outerHTML`, `insertAdjacentHTML` or `document.write` with data.
 * Pre-rendered SVG diagrams come from `<template>` elements (see `data.ts` `cloneDiagram`).
 *
 * Owner: skeleton (core). Others may add helpers here only through the integrator.
 */

export type AttrValue = string | number | boolean | null | undefined;

/** Class names: falsy entries are dropped, arrays flatten. */
export type ClassValue = string | false | null | undefined | readonly ClassValue[];

/** A child: nodes are appended, strings and numbers become text nodes, falsy entries are dropped. */
export type Child = Node | string | number | false | null | undefined | readonly Child[];

export type Handlers = { readonly [K in keyof HTMLElementEventMap]?: (event: HTMLElementEventMap[K]) => void };

/**
 * Element properties. Values: `true` sets an empty attribute, `false` / `null` / `undefined`
 * leave it off, numbers are stringified. Anything not listed goes in `attrs`.
 */
export interface Props {
  readonly id?: string;
  readonly class?: ClassValue;
  readonly role?: string;
  readonly title?: string;
  readonly href?: string;
  readonly target?: string;
  readonly rel?: string;
  readonly tabindex?: number;
  readonly hidden?: boolean;
  readonly type?: string;
  readonly name?: string;
  readonly value?: string;
  readonly placeholder?: string;
  readonly for?: string;
  readonly lang?: string;
  readonly disabled?: boolean;
  readonly checked?: boolean;
  readonly open?: boolean;
  readonly autocomplete?: string;
  readonly spellcheck?: boolean;
  readonly colspan?: number;
  readonly rowspan?: number;
  readonly scope?: string;
  /** Inline style properties; custom properties (`--x`) work too. */
  readonly style?: Readonly<Record<string, string>>;
  /** Event listeners, typed per event name. */
  readonly on?: Handlers;
  /** Any other attribute. */
  readonly attrs?: Readonly<Record<string, AttrValue>>;
  readonly [data: `data-${string}`]: AttrValue;
  readonly [aria: `aria-${string}`]: AttrValue;
}

const SPECIAL = new Set(['class', 'style', 'on', 'attrs']);

export function classNames(value: ClassValue): string {
  const out: string[] = [];
  const walk = (v: ClassValue): void => {
    if (!v) return;
    if (typeof v === 'string') out.push(v);
    else for (const item of v) walk(item);
  };
  walk(value);
  return out.join(' ');
}

function isAttrValue(value: unknown): value is AttrValue {
  return value === null || value === undefined || typeof value === 'string' || typeof value === 'number' || typeof value === 'boolean';
}

function setAttr(el: Element, name: string, value: AttrValue): void {
  if (value === false || value === null || value === undefined) return;
  // `spellcheck` is enumerated ("true"/"false"), not boolean.
  if (name === 'spellcheck') el.setAttribute(name, value ? 'true' : 'false');
  else el.setAttribute(name, value === true ? '' : String(value));
}

/** Appends children to a parent, flattening arrays and turning text into text nodes. */
export function append(parent: ParentNode, ...children: readonly Child[]): void {
  for (const child of children) {
    if (child === null || child === undefined || child === false) continue;
    if (typeof child === 'string' || typeof child === 'number') parent.append(document.createTextNode(String(child)));
    else if (child instanceof Node) parent.append(child);
    else append(parent, ...child);
  }
}

/** Creates an HTML element. */
export function h<K extends keyof HTMLElementTagNameMap>(tag: K, props?: Props | null, ...children: readonly Child[]): HTMLElementTagNameMap[K] {
  const el = document.createElement(tag);
  if (props) {
    for (const [key, value] of Object.entries(props)) {
      if (SPECIAL.has(key) || !isAttrValue(value)) continue;
      setAttr(el, key, value);
    }
    const cls = classNames(props.class);
    if (cls) el.setAttribute('class', cls);
    if (props.style) for (const [k, v] of Object.entries(props.style)) el.style.setProperty(k, v);
    if (props.attrs) for (const [k, v] of Object.entries(props.attrs)) setAttr(el, k, v);
    if (props.on) {
      for (const [type, handler] of Object.entries(props.on)) {
        if (typeof handler === 'function') el.addEventListener(type, handler as EventListener);
      }
    }
  }
  append(el, ...children);
  return el;
}

export const SVG_NS = 'http://www.w3.org/2000/svg';

/** Creates an SVG element. `class` is an ordinary attribute here; add listeners with `listen`. */
export function s<K extends keyof SVGElementTagNameMap>(
  tag: K,
  attrs?: Readonly<Record<string, AttrValue>> | null,
  ...children: readonly Child[]
): SVGElementTagNameMap[K] {
  const el = document.createElementNS(SVG_NS, tag);
  if (attrs) for (const [k, v] of Object.entries(attrs)) setAttr(el, k, v);
  append(el, ...children);
  return el;
}

/** A document fragment of children. */
export function frag(...children: readonly Child[]): DocumentFragment {
  const f = document.createDocumentFragment();
  append(f, ...children);
  return f;
}

/** Replaces all children of `parent`. */
export function replaceChildren(parent: Element, ...children: readonly Child[]): void {
  parent.replaceChildren();
  append(parent, ...children);
}

/** `querySelector`, typed by tag name when the selector is a bare tag. */
export function $<K extends keyof HTMLElementTagNameMap>(selector: K, root?: ParentNode): HTMLElementTagNameMap[K] | null;
export function $(selector: string, root?: ParentNode): Element | null;
export function $(selector: string, root: ParentNode = document): Element | null {
  return root.querySelector(selector);
}

/** `querySelectorAll` as an array, typed by tag name when the selector is a bare tag. */
export function $all<K extends keyof HTMLElementTagNameMap>(selector: K, root?: ParentNode): HTMLElementTagNameMap[K][];
export function $all(selector: string, root?: ParentNode): Element[];
export function $all(selector: string, root: ParentNode = document): Element[] {
  return Array.from(root.querySelectorAll(selector));
}

/** `querySelector` that checks the element's class, e.g. `$as('#q', HTMLInputElement)`. */
export function $as<T extends Element>(selector: string, ctor: abstract new (...args: never[]) => T, root: ParentNode = document): T | null {
  const el = root.querySelector(selector);
  return el instanceof ctor ? el : null;
}

/** Adds a listener and returns the function that removes it. */
export function listen<K extends keyof DocumentEventMap>(target: Document, type: K, handler: (event: DocumentEventMap[K]) => void, options?: AddEventListenerOptions): () => void;
export function listen<K extends keyof WindowEventMap>(target: Window, type: K, handler: (event: WindowEventMap[K]) => void, options?: AddEventListenerOptions): () => void;
export function listen<K extends keyof HTMLElementEventMap>(target: HTMLElement, type: K, handler: (event: HTMLElementEventMap[K]) => void, options?: AddEventListenerOptions): () => void;
export function listen<K extends keyof SVGElementEventMap>(target: SVGElement, type: K, handler: (event: SVGElementEventMap[K]) => void, options?: AddEventListenerOptions): () => void;
export function listen(target: EventTarget, type: string, handler: (event: Event) => void, options?: AddEventListenerOptions): () => void {
  target.addEventListener(type, handler, options);
  return () => target.removeEventListener(type, handler, options);
}

/** True when the user asked for reduced motion. */
export function prefersReducedMotion(): boolean {
  return typeof matchMedia === 'function' && matchMedia('(prefers-reduced-motion: reduce)').matches;
}

/** True when keyboard input should go to the focused control, not to page shortcuts. */
export function isTypingTarget(target: EventTarget | null): boolean {
  if (!(target instanceof HTMLElement)) return false;
  if (target.isContentEditable) return true;
  return target instanceof HTMLInputElement || target instanceof HTMLTextAreaElement || target instanceof HTMLSelectElement;
}
