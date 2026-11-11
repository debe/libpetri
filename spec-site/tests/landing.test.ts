import { readFileSync } from 'node:fs';
import { join } from 'node:path';
import { describe, expect, it } from 'vitest';
import { landingPage } from '../src/gen/landing.js';
import { REPO_ROOT, SITE_ROOT } from '../src/gen/paths.js';
import { svgSize, tokenCss, TOKENS_END_MARKER } from '../src/landing/build.js';
import { PACKAGES, PITCH } from '../src/landing/content.js';
import { LANDING_HOOKS } from '../src/landing/hooks.js';
import { el, escapeAttr, escapeText, frag, inlineScript, inlineStyle, Markup } from '../src/landing/html.js';
import type { LandingAssets } from '../src/landing/page.js';
import { evidenceCaption, renderLandingPage, specCountItems } from '../src/landing/page.js';
import type { SiteCounts } from '../src/model.js';

const counts: SiteCounts = {
  specFiles: 13, activeIds: 224, removedIds: 5, proposedIds: 3, leanBlocks: 157, leanIds: 138, signedBlocks: 1,
  citedIds: 81, openDefects: 22, situations: 15, replayed: 9, glossaryTerms: 60, untestedIds: 90,
};

const assets: LandingAssets = {
  css: ':root{--bg:#fff}',
  bootJs: 'void 0',
  clientJs: 'void 1',
  evidence: { width: 809, height: 336 },
};

const all = (text: string, re: RegExp): readonly string[] => [...text.matchAll(re)].map((m) => m[1] ?? '');

describe('landing html writer', () => {
  it('escapes text and attribute values', () => {
    expect(escapeText('a < b & c > d "q"')).toBe('a &lt; b &amp; c &gt; d "q"');
    expect(escapeAttr('"x" & <y>')).toBe('&quot;x&quot; &amp; &lt;y&gt;');
    expect(String(el('a', { href: '?a=1&b="2"', title: '<t>' }, '<b>'))).toBe(
      '<a href="?a=1&amp;b=&quot;2&quot;" title="&lt;t&gt;">&lt;b&gt;</a>',
    );
  });

  it('writes boolean attributes and skips absent ones, in literal order', () => {
    expect(String(el('button', { type: 'button', hidden: true, disabled: false, title: null }))).toBe('<button type="button" hidden></button>');
  });

  it('flattens children and drops empty ones', () => {
    expect(String(frag('a', null, false, undefined, ['b', [1, el('br', null)]]))).toBe('ab1<br>');
  });

  it('refuses children on void elements, bad attribute names and non-finite numbers', () => {
    expect(() => el('img', null, 'x')).toThrow(/cannot have children/);
    expect(() => el('div', { 'on click': 'x' })).toThrow(/invalid attribute name/);
    expect(() => el('p', null, Number.NaN)).toThrow(/refusing/);
  });

  it('guards inline style and script', () => {
    expect(() => inlineStyle('a{}</style><script>')).toThrow(/<\/style/);
    expect(String(inlineScript('x="</script>"'))).toBe('<script>x="<\\/script>"</script>');
    expect(() => inlineScript('x="<!--"')).toThrow(/<!--/);
  });

  it('cannot be bypassed by constructing Markup directly', () => {
    expect(() => Reflect.construct(Markup, [Symbol('checked markup'), '<script>'])).toThrow(/src\/landing\/html\.ts/);
  });
});

describe('landing assets', () => {
  it('cuts the token block out of the spec stylesheet', () => {
    const style = readFileSync(join(SITE_ROOT, 'src/app/style.css'), 'utf8');
    const tokens = tokenCss(style);
    expect(tokens.startsWith(':root {')).toBe(true);
    expect(tokens).toContain('--accent:');
    expect(tokens).toContain(':root[data-theme="dark"]');
    expect(tokens).toContain('prefers-reduced-motion');
    expect(tokens).not.toContain(TOKENS_END_MARKER);
    expect(() => tokenCss('body{}')).toThrow(/design tokens/);
  });

  it('reads the intrinsic SVG size in CSS pixels', () => {
    expect(svgSize('<svg xmlns="x" width="607pt" height="252pt" viewBox="0 0 607 252">')).toEqual({ width: 809, height: 336 });
    expect(svgSize('<svg height="20" width="10px">')).toEqual({ width: 10, height: 20 });
    expect(() => svgSize('<svg viewBox="0 0 1 1">')).toThrow(/width/);
    expect(() => svgSize('<g/>')).toThrow(/root/);
  });
});

describe('landing template', () => {
  const html = renderLandingPage(counts, assets);

  it('is one document with one h1, a canonical URL and the pitch', () => {
    expect(html.startsWith('<!doctype html>\n<html lang="en">')).toBe(true);
    expect(html.endsWith('</html>\n')).toBe(true);
    expect(all(html, /<h1\b[^>]*>([^<]*)</g)).toEqual([PITCH]);
    expect(html).toContain('<link rel="canonical" href="https://libpetri.org/">');
    expect(html).toContain('<main id="main"');
    expect(html).toContain('href="#main"');
  });

  it('lists the four packages with install lines and registry links', () => {
    for (const p of PACKAGES) {
      expect(html).toContain(`<code class="pkg__cmd" id="install-${p.key}">${escapeText(p.install)}</code>`);
      expect(html).toContain(`href="${p.registry.href}"`);
      expect(html).toContain(`href="${p.guide}"`);
    }
    expect(html).toContain('https://central.sonatype.com/artifact/org.libpetri/libpetri');
    expect(html).toContain('https://www.npmjs.com/package/libpetri');
    expect(html).toContain('https://crates.io/crates/libpetri');
    expect(html).toContain('https://pypi.org/project/libpetri/');
  });

  it('links the spec, the proof graph and GitHub', () => {
    expect(html).toContain('href="spec/"');
    expect(html).toContain('href="proof-graph/"');
    expect(html).toContain('href="https://github.com/debe/libpetri"');
  });

  it('shows the live counts', () => {
    const items = specCountItems(counts);
    expect(items.map((i) => `${i.value} ${i.label}`)).toEqual([
      '224 rules', '138 with a Lean block', '15 situations', '22 open defects',
    ]);
    for (const i of items) expect(html).toContain(`<strong class="counts__n">${i.value}</strong>`);
    expect(evidenceCaption(counts)).toContain('224 requirements');
    expect(specCountItems({ ...counts, situations: 1, openDefects: 1 }).map((i) => i.label)).toContain('open defect');
  });

  it('ships the enhancements hidden and every copy button names an existing code element', () => {
    expect(html).toMatch(new RegExp(`<button[^>]*id="${LANDING_HOOKS.themeButton}"[^>]*hidden`));
    const targets = all(html, /data-copy-for="([^"]+)"/g);
    expect(targets).toHaveLength(PACKAGES.length);
    for (const id of targets) expect(html).toContain(`id="${id}"`);
    expect(html).toContain(`id="${LANDING_HOOKS.status}"`);
  });

  it('has unique element ids', () => {
    const ids = all(html, /\sid="([^"]+)"/g);
    expect(new Set(ids).size).toBe(ids.length);
  });

  it('follows the copy rules', () => {
    expect(html).not.toContain('—');
    expect(html).not.toMatch(/claude|anthropic|generated with/i);
  });
});

describe('landing page build', () => {
  it('is deterministic, ignores the old file and embeds real assets', () => {
    const first = landingPage(counts);
    expect(landingPage(counts)).toBe(first);
    expect(first).toContain('--accent:');
    expect(first).toContain('libpetri-spec:theme');
    expect(first).toContain('width="809" height="336"');
    expect(first).not.toContain(REPO_ROOT);
  });
});

describe('404 page', () => {
  it('is a static page that links home', () => {
    const page = readFileSync(join(REPO_ROOT, 'docs/404.html'), 'utf8');
    expect(page).toContain('<a href="/">');
    expect(page).not.toMatch(/<script|http-equiv/i);
    expect(page).not.toContain('—');
  });
});
