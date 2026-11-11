/** Entry of the landing page's client script (bundled to one IIFE by src/landing/build.ts). */
import { browserClipboard, installCopyButtons, installThemeToggle } from './client.js';

installThemeToggle(document);
installCopyButtons(document, {
  clipboard: browserClipboard(navigator),
  setTimeout: (fn, ms) => window.setTimeout(fn, ms),
  clearTimeout: (handle) => window.clearTimeout(handle),
});
