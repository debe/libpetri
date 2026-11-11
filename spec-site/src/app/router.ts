/**
 * Hash routes with typed parameters. Every route is `#/<path>[?<query>]`; a hash that does not
 * start with `#/` (an in-page anchor) is not a route and is ignored.
 *
 *   #/                              situations   (home)
 *   #/situation/<slug>[?step=N]     situation    (one situation with its player)
 *   #/req[?filters]                 req, id null (rules index)
 *   #/req/<ID>[?filters]            req          (rule reader; tombstones too)
 *   #/conf[?f=...]                  conf
 *   #/graph                         graph, node null (picker)
 *   #/graph/<node key>              graph, mode 'node'   (CORE-031, term:<slug>, thm:<name>, RD-07, sit:<slug>)
 *   #/graph/impact/<node key>       graph, mode 'impact'
 *   #/selftest                      selftest
 *   anything else                   notfound
 *
 * Search, keyboard help, drawers and hover cards are overlays: they never change the route.
 * Query keys belong to the view (`step`, `f`, `kind`, `lean`, ...); `formatRoute` writes them
 * sorted and leaves out empty values, so a default filter never shows in the URL.
 *
 * Owner: skeleton (core). Adding a route means editing this file, `views.ts` and the contracts.
 */
import { type GraphNode, nodeKey, parseNodeKey } from '../model.js';

export type QueryParams = Readonly<Record<string, string>>;

export type Route =
  | { readonly view: 'situations'; readonly query: QueryParams }
  | { readonly view: 'situation'; readonly slug: string; readonly query: QueryParams }
  | { readonly view: 'req'; readonly id: string | null; readonly query: QueryParams }
  | { readonly view: 'conf'; readonly query: QueryParams }
  | { readonly view: 'graph'; readonly mode: 'node' | 'impact'; readonly node: GraphNode | null; readonly query: QueryParams }
  | { readonly view: 'selftest'; readonly query: QueryParams }
  | { readonly view: 'notfound'; readonly path: string; readonly query: QueryParams };

export type ViewName = Route['view'];
export type RouteOf<V extends ViewName> = Extract<Route, { readonly view: V }>;

const NO_QUERY: QueryParams = Object.freeze({});

/** Route constructors. */
export const R = {
  situations: (): RouteOf<'situations'> => ({ view: 'situations', query: NO_QUERY }),
  /** `step`: 0 = initial marking, k = after step k; null leaves it out. */
  situation: (slug: string, step: number | null = null): RouteOf<'situation'> => ({
    view: 'situation',
    slug,
    query: step === null ? NO_QUERY : { step: String(step) },
  }),
  req: (id: string | null = null, query: QueryParams = NO_QUERY): RouteOf<'req'> => ({ view: 'req', id, query }),
  conf: (query: QueryParams = NO_QUERY): RouteOf<'conf'> => ({ view: 'conf', query }),
  graph: (node: GraphNode | null = null): RouteOf<'graph'> => ({ view: 'graph', mode: 'node', node, query: NO_QUERY }),
  impact: (node: GraphNode): RouteOf<'graph'> => ({ view: 'graph', mode: 'impact', node, query: NO_QUERY }),
  selftest: (): RouteOf<'selftest'> => ({ view: 'selftest', query: NO_QUERY }),
} as const;

/** Graph route of a requirement, the common case. */
export function reqGraph(id: string, mode: 'node' | 'impact' = 'node'): RouteOf<'graph'> {
  return { view: 'graph', mode, node: { kind: 'req', id }, query: NO_QUERY };
}

function decodeSegment(segment: string): string {
  try {
    return decodeURIComponent(segment);
  } catch {
    return segment;
  }
}

export function parseQuery(text: string): QueryParams {
  const out: Record<string, string> = {};
  for (const pair of text.split('&')) {
    if (pair === '') continue;
    const eq = pair.indexOf('=');
    const key = decodeSegment((eq < 0 ? pair : pair.slice(0, eq)).replace(/\+/g, ' '));
    const value = eq < 0 ? '' : decodeSegment(pair.slice(eq + 1).replace(/\+/g, ' '));
    if (key !== '' && value !== '') out[key] = value;
  }
  return out;
}

/** `?a=1&b=2` with keys sorted and empty values left out; '' when nothing is left. */
export function formatQuery(query: QueryParams): string {
  const keys = Object.keys(query)
    .filter((k) => (query[k] ?? '') !== '')
    .sort();
  if (keys.length === 0) return '';
  return `?${keys.map((k) => `${encodeURIComponent(k)}=${encodeURIComponent(query[k] ?? '').replace(/%2C/g, ',')}`).join('&')}`;
}

/** Comma-separated list value of a query key (`f=defects,untested`), empty when absent. */
export function queryList(query: QueryParams, key: string): readonly string[] {
  const value = query[key];
  return value === undefined ? [] : value.split(',').filter((v) => v !== '');
}

/** True when the hash is a route (`#/...` or empty), false for an in-page anchor. */
export function isRouteHash(hash: string): boolean {
  return hash === '' || hash === '#' || hash.startsWith('#/');
}

export function parseHash(hash: string): Route {
  const raw = hash.startsWith('#') ? hash.slice(1) : hash;
  const q = raw.indexOf('?');
  const pathText = q < 0 ? raw : raw.slice(0, q);
  const query = parseQuery(q < 0 ? '' : raw.slice(q + 1));
  // A theorem key may contain '/': only the first segments are structural, the rest is the key.
  const parts = pathText.split('/').filter((p) => p !== '').map(decodeSegment);
  const [head, a] = parts;
  const n = parts.length;

  if (n === 0) return { view: 'situations', query };
  if (head === 'situation' && n === 2 && a !== undefined) return { view: 'situation', slug: a, query };
  if (head === 'req' && n <= 2) return { view: 'req', id: a ?? null, query };
  if (head === 'conf' && n === 1) return { view: 'conf', query };
  if (head === 'graph') {
    if (n === 1) return { view: 'graph', mode: 'node', node: null, query };
    if (a === 'impact') {
      if (n >= 3) return { view: 'graph', mode: 'impact', node: parseNodeKey(parts.slice(2).join('/')), query };
    } else {
      return { view: 'graph', mode: 'node', node: parseNodeKey(parts.slice(1).join('/')), query };
    }
  }
  if (head === 'selftest' && n === 1) return { view: 'selftest', query };
  return { view: 'notfound', path: `/${parts.join('/')}`, query };
}

const seg = (text: string): string => encodeURIComponent(text).replace(/%3A/gi, ':');

/** The hash for a route, e.g. `#/req/CORE-001`. Use it as an `href`. */
export function formatRoute(route: Route): string {
  const query = formatQuery(route.query);
  switch (route.view) {
    case 'situations':
      return `#/${query}`;
    case 'situation':
      return `#/situation/${seg(route.slug)}${query}`;
    case 'req':
      return `#/req${route.id === null ? '' : `/${seg(route.id)}`}${query}`;
    case 'conf':
      return `#/conf${query}`;
    case 'graph':
      if (route.node === null) return `#/graph${query}`;
      return `#/graph${route.mode === 'impact' ? '/impact' : ''}/${seg(nodeKey(route.node))}${query}`;
    case 'selftest':
      return `#/selftest${query}`;
    case 'notfound':
      return `#${route.path}${query}`;
  }
}

/** Alias of `formatRoute` for `href` attributes. */
export const href = formatRoute;

export function currentRoute(): Route {
  return parseHash(isRouteHash(location.hash) ? location.hash : '');
}

export interface NavigateOptions {
  /** Replace the history entry instead of pushing one. */
  readonly replace?: boolean;
  /**
   * Update the address bar without rendering (no `hashchange` fires). For state the view
   * already shows, such as the player's step or a filter toggle.
   */
  readonly silent?: boolean;
}

export function navigate(route: Route, options: NavigateOptions = {}): void {
  const hash = formatRoute(route);
  if (options.silent) {
    history.replaceState(history.state, '', hash);
    return;
  }
  if (options.replace) {
    history.replaceState(history.state, '', hash);
    dispatchEvent(new HashChangeEvent('hashchange'));
    return;
  }
  if (location.hash === hash) dispatchEvent(new HashChangeEvent('hashchange'));
  else location.hash = hash;
}

/** Calls `handler` on every route change (not on in-page anchors). Returns the unsubscribe. */
export function onRouteChange(handler: (route: Route) => void): () => void {
  const listener = (): void => {
    if (isRouteHash(location.hash)) handler(currentRoute());
  };
  addEventListener('hashchange', listener);
  return () => removeEventListener('hashchange', listener);
}
