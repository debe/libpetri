/**
 * The landing page template (https://libpetri.org/, written to docs/index.html). Pure: the same
 * counts and assets give the same bytes. Layout and copy follow design.md section 11.
 *
 * The page works without JavaScript. The theme toggle and the copy buttons are progressive
 * enhancements: they ship `hidden` and the client script (src/landing/browser/) reveals them.
 */
import type { SiteCounts } from '../model.js';
import {
  ABOUT,
  EVIDENCE_SVG,
  LEDE,
  LICENSE,
  PACKAGES,
  PAGE_DESCRIPTION,
  PAGE_TITLE,
  PITCH,
  PROOF_GRAPH_HREF,
  REPO_URL,
  SITE_URL,
  SPEC_HREF,
  Z3_NOTE,
} from './content.js';
import type { PackageInfo } from './content.js';
import type { Markup } from './html.js';
import { el, htmlDocument, inlineScript, inlineStyle } from './html.js';
import { LANDING_HOOKS } from './hooks.js';

export interface LandingAssets {
  /** Minified CSS: tokens from src/app/style.css, then src/landing/landing.css. */
  readonly css: string;
  /** Applies the stored theme before first paint (src/app/boot.ts). */
  readonly bootJs: string;
  /** Theme toggle and copy buttons (src/landing/browser/main.ts). */
  readonly clientJs: string;
  /** Intrinsic size of the evidence diagram in CSS pixels, so the image reserves its box. */
  readonly evidence: { readonly width: number; readonly height: number };
}

export interface CountItem {
  readonly value: string;
  readonly label: string;
  /** What the number counts, for the `title` tooltip. */
  readonly title: string;
}

/**
 * The live numbers on the Specification card (design 11: rules, rules with a Lean block,
 * situations, open defects). Every one is read from the site data.
 */
export function specCountItems(c: SiteCounts): readonly CountItem[] {
  return [
    { value: String(c.activeIds), label: c.activeIds === 1 ? 'rule' : 'rules', title: `Active requirements in ${c.specFiles} spec files` },
    {
      value: String(c.leanIds),
      label: 'with a Lean block',
      title: `Requirement IDs that at least one Lean block states (${c.leanBlocks} blocks, companion blocks included)`,
    },
    {
      value: String(c.situations),
      label: c.situations === 1 ? 'situation' : 'situations',
      title: `Small example runs; the Lean reference replays ${c.replayed} of them`,
    },
    {
      value: String(c.openDefects),
      label: c.openDefects === 1 ? 'open defect' : 'open defects',
      title: 'Open entries in the runtime defect ledger',
    },
  ];
}

/** The caption under the evidence diagram, with the live requirement count. */
export function evidenceCaption(c: SiteCounts): string {
  return (
    `One specification with ${c.activeIds} requirements feeds independent Java, TypeScript and Rust implementations; ` +
    'Python binds the Rust one. All three send identical SMT-LIB2 scripts to z3. Lean 4 proofs show that the ' +
    'verifier abstraction covers every run and that the precompiled executor refines the reference.'
  );
}

function header(): Markup {
  return el(
    'header',
    { class: 'top' },
    el(
      'div',
      { class: 'top__inner' },
      el('a', { class: 'top__brand', href: './' }, 'libpetri'),
      el(
        'nav',
        { class: 'top__nav', 'aria-label': 'Main' },
        el('a', { class: 'top__link', href: SPEC_HREF }, 'Spec'),
        el('a', { class: 'top__link', href: PROOF_GRAPH_HREF }, 'Proof graph'),
        el('a', { class: 'top__link', href: REPO_URL }, 'GitHub'),
      ),
      el(
        'button',
        { type: 'button', class: 'top__theme', id: LANDING_HOOKS.themeButton, 'aria-label': 'Theme: Auto', title: 'Theme: Auto', hidden: true },
        '◐',
      ),
    ),
  );
}

function hero(c: SiteCounts, assets: LandingAssets): Markup {
  return el(
    'section',
    { class: 'hero', 'aria-labelledby': 'hero-title' },
    el('h1', { class: 'hero__title', id: 'hero-title' }, PITCH),
    el('p', { class: 'hero__lede' }, LEDE),
    el('p', { class: 'hero__about' }, ABOUT.join(' ')),
    el(
      'div',
      { class: 'hero__actions' },
      el('a', { class: 'button button--primary', href: SPEC_HREF }, 'Read the spec'),
      el('a', { class: 'button', href: REPO_URL }, 'View on GitHub'),
    ),
    el(
      'figure',
      { class: 'evidence' },
      el('img', {
        class: 'evidence__img',
        src: EVIDENCE_SVG,
        width: assets.evidence.width,
        height: assets.evidence.height,
        alt: 'Diagram: one specification, the Java, TypeScript, Rust and Python packages, z3 and the Lean proofs.',
        decoding: 'async',
      }),
      el('figcaption', { class: 'evidence__caption' }, evidenceCaption(c)),
    ),
  );
}

function packageCard(p: PackageInfo): Markup {
  const codeId = `install-${p.key}`;
  return el(
    'article',
    { class: 'pkg', 'aria-labelledby': `pkg-${p.key}` },
    el(
      'div',
      { class: 'pkg__head' },
      el('h3', { class: 'pkg__title', id: `pkg-${p.key}` }, p.version),
      el('span', { class: p.maturity === 'Beta' ? 'tag tag--open' : 'tag' }, p.maturity),
    ),
    el('p', { class: 'pkg__runtime' }, p.runtime, p.note === null ? null : ['. ', p.note]),
    el('p', { class: 'pkg__label' }, p.installLabel),
    el(
      'div',
      { class: 'pkg__install' },
      el('code', { class: 'pkg__cmd', id: codeId }, p.install),
      el(
        'button',
        {
          type: 'button',
          class: 'pkg__copy',
          [LANDING_HOOKS.copyFor]: codeId,
          'aria-label': `Copy install command for ${p.language}`,
          hidden: true,
        },
        el('span', { class: 'pkg__copy-glyph', 'aria-hidden': 'true' }, '⧉'),
        el('span', { class: LANDING_HOOKS.copyText }, 'Copy'),
      ),
    ),
    el(
      'p',
      { class: 'pkg__links' },
      el('a', { href: p.registry.href }, p.registry.name),
      el('span', { 'aria-hidden': 'true' }, ' · '),
      el('a', { href: p.guide }, `${p.language} guide`),
    ),
  );
}

function install(): Markup {
  return el(
    'section',
    { class: 'section', 'aria-labelledby': 'install-title' },
    el('h2', { class: 'section__title', id: 'install-title' }, 'Install'),
    el('p', { class: 'section__lede' }, 'Four packages, one specification. Python binds the Rust runtime.'),
    el('div', { class: 'pkgs' }, PACKAGES.map(packageCard)),
    el('p', { class: 'note' }, Z3_NOTE),
    el('p', { class: 'sr-only', id: LANDING_HOOKS.status, role: 'status', 'aria-live': 'polite' }),
  );
}

interface TeaserSpec {
  readonly href: string;
  readonly title: string;
  readonly text: string;
  /** Extra content under the text, such as the live counts. */
  readonly extra: Markup | null;
}

/**
 * A card that is one link. Its accessible name is its whole text, so it matches what is on
 * screen (WCAG 2.5.3); the arrow is decoration.
 */
function teaser(o: TeaserSpec): Markup {
  return el(
    'a',
    { class: 'teaser', href: o.href },
    el('h3', { class: 'teaser__title' }, o.title, el('span', { class: 'teaser__arrow', 'aria-hidden': 'true' }, ' ›')),
    el('p', { class: 'teaser__text' }, o.text),
    o.extra,
  );
}

function countsList(c: SiteCounts): Markup {
  return el(
    'ul',
    { class: 'counts' },
    specCountItems(c).map((item) =>
      el('li', { class: 'counts__item', title: item.title }, el('strong', { class: 'counts__n' }, item.value), ' ', el('span', { class: 'counts__label' }, item.label)),
    ),
  );
}

function explore(c: SiteCounts): Markup {
  return el(
    'section',
    { class: 'section', 'aria-labelledby': 'explore-title' },
    el('h2', { class: 'section__title', id: 'explore-title' }, 'Look inside'),
    el(
      'div',
      { class: 'teasers' },
      teaser({
        href: SPEC_HREF,
        title: 'Specification',
        text: 'Every requirement with its spec text, its Lean statement and its evidence, plus small example runs that the Lean reference replays.',
        extra: countsList(c),
      }),
      teaser({
        href: PROOF_GRAPH_HREF,
        title: 'Proof graph',
        text: 'Every Lean declaration, and what each proved requirement depends on.',
        extra: null,
      }),
      teaser({
        href: REPO_URL,
        title: 'GitHub',
        text: `Source, issues and releases. ${LICENSE.name}.`,
        extra: null,
      }),
    ),
  );
}

function footer(): Markup {
  return el(
    'footer',
    { class: 'foot' },
    el('a', { href: LICENSE.href }, LICENSE.name),
    el('span', { 'aria-hidden': 'true' }, ' · '),
    el('a', { href: REPO_URL }, 'GitHub'),
    el('span', { 'aria-hidden': 'true' }, ' · '),
    el('span', null, 'libpetri.org'),
  );
}

export function renderLandingPage(counts: SiteCounts, assets: LandingAssets): string {
  const head = [
    el('meta', { charset: 'utf-8' }),
    el('meta', { name: 'viewport', content: 'width=device-width, initial-scale=1' }),
    el('meta', { name: 'color-scheme', content: 'light dark' }),
    el('meta', { name: 'description', content: PAGE_DESCRIPTION }),
    el('link', { rel: 'canonical', href: SITE_URL }),
    el('meta', { property: 'og:title', content: PAGE_TITLE }),
    el('meta', { property: 'og:description', content: PAGE_DESCRIPTION }),
    el('meta', { property: 'og:url', content: SITE_URL }),
    el('meta', { property: 'og:type', content: 'website' }),
    el('title', null, PAGE_TITLE),
    inlineStyle(assets.css),
    inlineScript(assets.bootJs),
  ].flatMap((m) => ['\n', m]);
  const body = [
    el('a', { class: 'skip-link', href: '#main' }, 'Skip to content'),
    header(),
    el('main', { id: 'main', class: 'page', tabindex: -1 }, hero(counts, assets), install(), explore(counts)),
    footer(),
    inlineScript(assets.clientJs),
  ].flatMap((m) => ['\n', m]);
  return htmlDocument([...head, '\n'], [...body, '\n']);
}
