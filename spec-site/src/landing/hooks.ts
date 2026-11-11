/**
 * Element ids and attributes shared by the landing template (Node) and its client script
 * (browser). Kept in its own module so the browser bundle does not pull in the template.
 */
export const LANDING_HOOKS = {
  /** The theme toggle button; shipped `hidden`, revealed by the client. */
  themeButton: 'theme-toggle',
  /** Polite live region that announces copy results. */
  status: 'copy-status',
  /** Attribute on a copy button naming the id of the `<code>` it copies. */
  copyFor: 'data-copy-for',
  /** Class of the visible label inside a copy button. */
  copyText: 'pkg__copy-text',
} as const;

/** How long a copy button says "Copied" (design 11). */
export const COPIED_MS = 1500;
