/**
 * CSS custom properties exposed by the canonical viewer stylesheet.
 *
 * Each property has a default in `viewer.css`. Consumers can override any of
 * them at any scope (the viewer container, the document root, etc.) to
 * theme the viewer without touching the canonical CSS.
 *
 * Names are listed here as a reference + so the IIFE bundle can expose them
 * on `window.LibpetriViewer.cssVariables`. The list is informational — the
 * stylesheet is still the source of truth.
 *
 * @module viewer/styles
 */

/** CSS custom property names that the canonical stylesheet honours. */
export const VIEWER_CSS_VARIABLES = [
  '--lpv-bg',
  '--lpv-header-bg',
  '--lpv-border',
  '--lpv-text',
  '--lpv-muted',
  '--lpv-cluster-bg',
  '--lpv-cluster-bg-collapsed',
  '--lpv-cluster-stroke-width',
  '--lpv-cluster-stroke-dash',
  '--lpv-cluster-fill-tint',
  '--lpv-dim-opacity',
  '--lpv-active-filter-outline',
  '--lpv-legend-bg',
  '--lpv-chip-bg',
  '--lpv-chip-active-bg',
] as const;

export type ViewerCssVariable = (typeof VIEWER_CSS_VARIABLES)[number];
