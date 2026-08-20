/**
 * Build-stamped viewer version.
 *
 * The bundle carries the version of the `libpetri` package it was built from,
 * so a generated doc page can say which viewer drew it. Doc generators stamp
 * this onto the diagram container as `data-libpetri-viewer`; without it a page
 * rendered by an old bundle (e.g. pre-2.10.5, whose edges are Graphviz-routed
 * diagonals rather than the ELK orthogonal routes) is indistinguishable from a
 * current one except by reading pixels.
 *
 * `__LIBPETRI_VIEWER_VERSION__` is substituted at build time by both bundlers
 * (`tsup.config.ts` for the ESM output, `scripts/build-viewer-iife.mjs` for the
 * IIFE). When the source is loaded directly, as vitest does, the identifier is
 * simply absent and the `typeof` guard falls through to the dev sentinel.
 *
 * @module viewer/version
 */

declare const __LIBPETRI_VIEWER_VERSION__: string | undefined;

/** Version of the `libpetri` package this viewer bundle was built from. */
export const VERSION: string =
  typeof __LIBPETRI_VIEWER_VERSION__ === 'string'
    ? __LIBPETRI_VIEWER_VERSION__
    : '0.0.0-dev';
