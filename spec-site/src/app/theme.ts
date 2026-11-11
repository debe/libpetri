/**
 * Theme choice (design 1, "Theme toggle"): `auto` follows `prefers-color-scheme`; `light` /
 * `dark` set `<html data-theme>`, which the CSS tokens read. The toggle and the `t` key cycle
 * Auto -> Light -> Dark. The choice is a per-viewer convenience kept in localStorage; every
 * access is guarded, so blocked storage just means `auto`.
 *
 * Owner: skeleton (core).
 */

export type ThemeChoice = 'auto' | 'light' | 'dark';
export type Theme = 'light' | 'dark';

export const THEME_STORAGE_KEY = 'libpetri-spec:theme';

const LABEL: Readonly<Record<ThemeChoice, string>> = { auto: 'Auto', light: 'Light', dark: 'Dark' };

export function themeLabel(choice: ThemeChoice): string {
  return `Theme: ${LABEL[choice]}`;
}

/** The choice made in this page view; wins over storage (which may be blocked). */
let chosen: ThemeChoice | null = null;

export function readThemeChoice(): ThemeChoice {
  if (chosen !== null) return chosen;
  try {
    const v = localStorage.getItem(THEME_STORAGE_KEY);
    return v === 'light' || v === 'dark' ? v : 'auto';
  } catch {
    return 'auto';
  }
}

export function storeThemeChoice(choice: ThemeChoice): void {
  chosen = choice;
  try {
    if (choice === 'auto') localStorage.removeItem(THEME_STORAGE_KEY);
    else localStorage.setItem(THEME_STORAGE_KEY, choice);
  } catch {
    // Storage blocked: the choice lasts for this page view only.
  }
}

export function applyThemeChoice(choice: ThemeChoice): void {
  const root = document.documentElement;
  if (choice === 'auto') delete root.dataset['theme'];
  else root.dataset['theme'] = choice;
}

export function nextThemeChoice(choice: ThemeChoice): ThemeChoice {
  return choice === 'auto' ? 'light' : choice === 'light' ? 'dark' : 'auto';
}

/** Moves to the next choice, applies and stores it, and returns it. */
export function cycleTheme(): ThemeChoice {
  const next = nextThemeChoice(readThemeChoice());
  storeThemeChoice(next);
  applyThemeChoice(next);
  return next;
}

export function systemTheme(): Theme {
  return typeof matchMedia === 'function' && matchMedia('(prefers-color-scheme: dark)').matches ? 'dark' : 'light';
}

/** The theme in effect now. */
export function effectiveTheme(): Theme {
  const choice = readThemeChoice();
  return choice === 'auto' ? systemTheme() : choice;
}

/**
 * The theme toggle's icon for a choice, drawn as SVG in the text colour (a half disc, a sun, a
 * moon). Font glyphs such as ◐ ☀ ☾ depend on the reader's fonts and render as slivers where
 * those fonts lack them. Shared by the spec site and the landing page.
 */
export function themeIcon(choice: ThemeChoice, doc: Document = document): SVGSVGElement {
  const NS = 'http://www.w3.org/2000/svg';
  const make = (tag: string, attrs: Readonly<Record<string, string>>): SVGElement => {
    const el = doc.createElementNS(NS, tag);
    for (const [k, v] of Object.entries(attrs)) el.setAttribute(k, v);
    return el;
  };
  const line = { fill: 'none', stroke: 'currentColor', 'stroke-width': '1.5', 'stroke-linecap': 'round', 'stroke-linejoin': 'round' };
  const svg = doc.createElementNS(NS, 'svg');
  for (const [k, v] of Object.entries({ class: 'theme-icon', viewBox: '0 0 16 16', width: '16', height: '16', 'aria-hidden': 'true', focusable: 'false' })) svg.setAttribute(k, v);
  if (choice === 'auto') {
    svg.append(make('circle', { cx: '8', cy: '8', r: '6', ...line }), make('path', { d: 'M8 2a6 6 0 0 1 0 12z', fill: 'currentColor' }));
  } else if (choice === 'light') {
    svg.append(
      make('circle', { cx: '8', cy: '8', r: '3', ...line }),
      make('path', { d: 'M8 1v2M8 13v2M1 8h2M13 8h2M3.05 3.05l1.41 1.41M11.54 11.54l1.41 1.41M3.05 12.95l1.41-1.41M11.54 4.46l1.41-1.41', ...line }),
    );
  } else {
    svg.append(make('path', { d: 'M13.5 9.6A5.75 5.75 0 1 1 6.4 2.5a4.5 4.5 0 0 0 7.1 7.1z', ...line }));
  }
  return svg;
}
