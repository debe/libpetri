/**
 * The page frame (design 1, "Global shell"): skip link, sticky header (Home link, wordmark,
 * primary navigation, search button, Lean chip, theme toggle; a menu button under 600px),
 * `<main id="main">`, a polite live region that announces each new view, and the footer.
 * Views render into `main`; the shell marks the current navigation entry with
 * `aria-current="page"`.
 *
 * Owner: skeleton (core); visual polish by the design fixup.
 */
import type { AppContext } from './context.js';
import { h, listen, s } from './dom.js';
import { href, R, type Route } from './router.js';
import { openSearch } from './search.js';
import { cycleTheme, readThemeChoice, themeIcon, themeLabel } from './theme.js';

export type NavKey = 'situations' | 'rules' | 'conf' | 'graph';

export interface Shell {
  readonly root: HTMLElement;
  readonly main: HTMLElement;
  /** Marks the navigation entry of the route and closes the phone menu. */
  setRoute(route: Route): void;
  /** Announces text through the shell's polite live region. */
  announce(text: string): void;
  /** Re-reads the theme choice into the toggle (after the `t` key). */
  syncTheme(): void;
}

export function navKeyOf(route: Route): NavKey | null {
  switch (route.view) {
    case 'situations':
    case 'situation':
      return 'situations';
    case 'req':
      return 'rules';
    case 'conf':
      return 'conf';
    case 'graph':
      return 'graph';
    case 'selftest':
    case 'notfound':
      return null;
  }
}

const NAV: readonly { readonly key: NavKey; readonly label: string; readonly route: Route }[] = [
  { key: 'situations', label: 'Situations', route: R.situations() },
  { key: 'rules', label: 'Rules', route: R.req() },
  { key: 'conf', label: 'Conformance', route: R.conf() },
  { key: 'graph', label: 'Graph', route: R.graph() },
];

function leanChip(ctx: AppContext): HTMLElement {
  const c = ctx.data.counts;
  const part = (text: string, title: string): HTMLElement => h('span', { class: 'lean-chip__part', title }, text);
  const dot = (): HTMLElement => h('span', { class: 'lean-chip__sep', 'aria-hidden': 'true' }, ' · ');
  return h('a', { class: 'lean-chip', href: href(R.conf()) },
    part(`${c.leanBlocks} blocks`, 'Lean requirement blocks'),
    dot(),
    part(`${c.leanIds}/${c.activeIds} IDs`, 'Requirement IDs with at least one Lean block'),
    dot(),
    part(`${c.signedBlocks} signed`, 'Blocks whose statement a reviewer has signed'),
    dot(),
    part(`${c.openDefects} open defects`, 'Open entries of the runtime defect ledger. One entry can name several rules and languages.'),
  );
}

/** A magnifier, drawn as SVG in the text colour (a font glyph would depend on the reader's fonts). */
function searchIcon(): SVGSVGElement {
  return s('svg', { class: 'shell__search-icon', viewBox: '0 0 16 16', width: 16, height: 16, 'aria-hidden': 'true', focusable: 'false' },
    s('circle', { cx: 7, cy: 7, r: 4.5, fill: 'none', stroke: 'currentColor', 'stroke-width': 1.6 }),
    s('path', { d: 'M10.5 10.5 14 14', fill: 'none', stroke: 'currentColor', 'stroke-width': 1.6, 'stroke-linecap': 'round' }),
  );
}

export function createShell(ctx: AppContext): Shell {
  const { links } = ctx.data;
  const main = h('main', { id: 'main', class: 'shell__main', tabindex: -1 });
  const live = h('div', { class: 'sr-only', 'aria-live': 'polite', 'aria-atomic': 'true' });

  const skip = h('a', { class: 'skip-link', href: '#main' }, 'Skip to content');
  listen(skip, 'click', (e) => {
    e.preventDefault();
    main.focus();
  });

  const navLinks = NAV.map((n) => h('a', { class: 'shell__link', href: href(n.route), 'data-nav': n.key }, n.label));
  // On phones the menu sheet also carries what the header has no room for: the way back to the
  // landing page and the Lean summary.
  const menuExtra = h('div', { class: 'shell__menu-extra' },
    h('a', { class: 'shell__link', href: links.home }, 'Home'),
    leanChip(ctx),
  );
  const nav = h('nav', { class: 'shell__nav', id: 'shell-nav', 'aria-label': 'Main' }, navLinks, menuExtra);

  const menuGlyph = h('span', { 'aria-hidden': 'true' }, '≡');
  const menuButton = h('button', { type: 'button', class: 'shell__menu', 'aria-expanded': 'false', 'aria-controls': 'shell-nav', 'aria-label': 'Menu' }, menuGlyph);
  const setMenu = (open: boolean): void => {
    menuButton.setAttribute('aria-expanded', String(open));
    menuGlyph.textContent = open ? '×' : '≡';
    root.classList.toggle('shell--menu-open', open);
  };
  listen(menuButton, 'click', () => setMenu(menuButton.getAttribute('aria-expanded') !== 'true'));

  const searchButton = h('button', { type: 'button', class: 'shell__search', title: 'Search (/)' },
    searchIcon(),
    h('span', { class: 'shell__search-text' }, 'Search rules, terms, theorems'),
    h('kbd', { class: 'shell__search-key', 'aria-hidden': 'true' }, '/'),
  );
  listen(searchButton, 'click', () => openSearch(ctx));

  const themeButton = h('button', { type: 'button', class: 'shell__theme' });
  const syncTheme = (): void => {
    const choice = readThemeChoice();
    themeButton.setAttribute('aria-label', themeLabel(choice));
    themeButton.title = themeLabel(choice);
    themeButton.dataset['choice'] = choice;
    themeButton.replaceChildren(themeIcon(choice));
  };
  listen(themeButton, 'click', () => {
    cycleTheme();
    syncTheme();
  });
  syncTheme();

  const root = h('div', { class: 'shell' },
    skip,
    h('header', { class: 'shell__header' },
      menuButton,
      h('a', { class: 'shell__home', href: links.home }, 'Home'),
      h('a', { class: 'shell__brand', href: href(R.situations()) },
        h('span', { class: 'shell__brand-name' }, 'libpetri'), ' ', h('span', { class: 'shell__brand-sub' }, 'spec'),
      ),
      nav,
      h('div', { class: 'shell__tools' }, searchButton, leanChip(ctx), themeButton),
    ),
    main,
    live,
    h('footer', { class: 'shell__footer' },
      h('span', null, 'Generated from spec/ and lean/report · data ', h('code', null, ctx.data.contentHash)),
      ' · Apache 2.0 · ',
      h('a', { href: links.repo }, 'GitHub'),
      ' · ',
      h('a', { href: links.proofGraph }, 'Proof graph'),
    ),
  );

  return {
    root,
    main,
    setRoute(route: Route): void {
      setMenu(false);
      const key = navKeyOf(route);
      for (const link of navLinks) {
        if (link.dataset['nav'] === key) link.setAttribute('aria-current', 'page');
        else link.removeAttribute('aria-current');
      }
    },
    announce(text: string): void {
      live.textContent = text;
    },
    syncTheme,
  };
}
