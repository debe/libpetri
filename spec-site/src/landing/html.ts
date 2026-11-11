/**
 * A small typed HTML writer for the static landing page (Node side).
 *
 * Text and attribute values are escaped by construction: the only way to get unescaped text into
 * the output is `inlineStyle` / `inlineScript`, which refuse input that could end their element
 * early. Attribute order is the order of the object literal, so the same input gives the same
 * bytes.
 */

/** Module-private key: only this module can wrap a string as `Markup`. */
const CHECKED: unique symbol = Symbol('checked markup');

/** Already-escaped markup. Only this module can make one. */
export class Markup {
  readonly #html: string;

  constructor(key: typeof CHECKED, html: string) {
    if (key !== CHECKED) throw new Error('Markup is made by src/landing/html.ts only');
    this.#html = html;
  }

  toString(): string {
    return this.#html;
  }
}

function checked(html: string): Markup {
  return new Markup(CHECKED, html);
}

export type Child = Markup | string | number | null | undefined | false | readonly Child[];
export type AttrValue = string | number | boolean | null | undefined;
export type Attrs = Readonly<Record<string, AttrValue>>;

/** Elements that never have children or an end tag. */
const VOID_TAGS: ReadonlySet<string> = new Set(['meta', 'link', 'img', 'br', 'hr', 'input']);

const ATTR_NAME = /^[a-z][a-z0-9-]*$/;

export function escapeText(text: string): string {
  return text.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
}

export function escapeAttr(text: string): string {
  return escapeText(text).replace(/"/g, '&quot;');
}

function renderAttrs(attrs: Attrs | null): string {
  if (attrs === null) return '';
  let out = '';
  for (const [name, value] of Object.entries(attrs)) {
    if (!ATTR_NAME.test(name)) throw new Error(`invalid attribute name ${JSON.stringify(name)}`);
    if (value === false || value === null || value === undefined) continue;
    out += value === true ? ` ${name}` : ` ${name}="${escapeAttr(String(value))}"`;
  }
  return out;
}

function renderChild(child: Child): string {
  if (child === null || child === undefined || child === false) return '';
  if (child instanceof Markup) return child.toString();
  if (typeof child === 'string') return escapeText(child);
  if (typeof child === 'number') {
    if (!Number.isFinite(child)) throw new Error(`refusing to write the number ${String(child)}`);
    return String(child);
  }
  return child.map(renderChild).join('');
}

/** `<tag attrs>children</tag>`; a void tag takes no children. */
export function el<K extends keyof HTMLElementTagNameMap>(tag: K, attrs: Attrs | null, ...children: Child[]): Markup {
  const open = `<${tag}${renderAttrs(attrs)}>`;
  if (VOID_TAGS.has(tag)) {
    if (children.length > 0) throw new Error(`<${tag}> cannot have children`);
    return checked(open);
  }
  return checked(`${open}${renderChild(children)}</${tag}>`);
}

/** Joins children into one fragment. */
export function frag(...children: Child[]): Markup {
  return checked(renderChild(children));
}

/** CSS for a `<style>` element. A literal `</style` would end it early, so it is refused. */
export function inlineStyle(css: string): Markup {
  if (/<\/style/i.test(css)) throw new Error('CSS contains </style; refusing to inline it');
  return checked(`<style>${css}</style>`);
}

/** JavaScript for a `<script>` element; `</script` is escaped, `<!--` is refused. */
export function inlineScript(js: string): Markup {
  const safe = js.replace(/<\/script/gi, '<\\/script');
  if (/<!--/.test(safe)) throw new Error('script contains <!--; refusing to inline it');
  return checked(`<script>${safe}</script>`);
}

/** A whole document: doctype, `<html lang="en">`, head and body, with a final newline. */
export function htmlDocument(head: readonly Child[], body: readonly Child[], bodyAttrs: Attrs | null = null): string {
  return `<!doctype html>\n${el('html', { lang: 'en' }, el('head', null, ...head), '\n', el('body', bodyAttrs, ...body))}\n`;
}
