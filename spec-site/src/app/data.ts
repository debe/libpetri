/**
 * Reads the embedded data once. `SiteData` is the JSON in
 * `<script type="application/json" id="site-data">`, decoded by `decode-site.ts`; a page whose
 * data does not match the model fails here, at start, with the JSON path of the problem.
 *
 * Owner: skeleton (core).
 */
import { decode } from '../decode.js';
import { siteData } from '../decode-site.js';
import type { SiteData, SituationSlug } from '../model.js';
import { diagramTemplateId, SITE_DATA_ELEMENT_ID } from '../model.js';

export function loadSiteData(doc: Document = document): SiteData {
  const el = doc.getElementById(SITE_DATA_ELEMENT_ID);
  if (el === null) throw new Error(`#${SITE_DATA_ELEMENT_ID} is missing`);
  const raw: unknown = JSON.parse(el.textContent ?? '');
  return decode(siteData, raw);
}

/**
 * A fresh copy of the pre-rendered diagram of a situation, or null when the page has none.
 * Each call returns a new element, so one page can show a diagram several times.
 */
export function cloneDiagram(slug: SituationSlug, doc: Document = document): SVGSVGElement | null {
  const template = doc.getElementById(diagramTemplateId(slug));
  if (!(template instanceof HTMLTemplateElement)) return null;
  const svg = template.content.firstElementChild;
  if (!(svg instanceof SVGSVGElement)) return null;
  const copy = svg.cloneNode(true);
  return copy instanceof SVGSVGElement ? copy : null;
}

/**
 * A decorative thumbnail of a situation's diagram whose labels stay readable: the viewBox is
 * widened (never narrowed) so that, at `widthPx` CSS pixels wide, the smallest label is about
 * `minFontPx` tall; `xMidYMin slice` then shows the top of a tall net instead of shrinking the
 * whole net into a sliver. Null when the page has no diagram for the slug.
 */
export function thumbnailDiagram(slug: SituationSlug, widthPx: number, minFontPx = 9, doc: Document = document): SVGSVGElement | null {
  const svg = cloneDiagram(slug, doc);
  if (svg === null) return null;
  svg.setAttribute('aria-hidden', 'true');
  svg.setAttribute('focusable', 'false');
  svg.removeAttribute('width');
  svg.removeAttribute('height');
  const box = (svg.getAttribute('viewBox') ?? '').trim().split(/[\s,]+/).map(Number);
  const [x, y, w, h] = box;
  if (box.length !== 4 || x === undefined || y === undefined || w === undefined || h === undefined || !box.every(Number.isFinite) || w <= 0) {
    svg.setAttribute('preserveAspectRatio', 'xMidYMid meet');
    return svg;
  }
  const sizes = Array.from(svg.querySelectorAll('text'))
    .map((t) => Number.parseFloat(t.getAttribute('font-size') ?? ''))
    .filter((n) => Number.isFinite(n) && n > 0);
  const font = sizes.length === 0 ? 12 : Math.min(...sizes);
  const width = Math.max(w, widthPx / (minFontPx / font));
  svg.setAttribute('viewBox', `${(x - (width - w) / 2).toFixed(2)} ${y.toFixed(2)} ${width.toFixed(2)} ${h.toFixed(2)}`);
  svg.setAttribute('preserveAspectRatio', 'xMidYMin slice');
  return svg;
}
