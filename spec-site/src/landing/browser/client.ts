/**
 * Progressive enhancements of the landing page: the theme toggle and the copy buttons. The page
 * reads fine without them; both controls ship `hidden` and are revealed here.
 *
 * The theme choice uses the spec site's storage key (src/app/theme.ts), so one choice holds on
 * https://libpetri.org/ and https://libpetri.org/spec/.
 */
import { cycleTheme, readThemeChoice, themeIcon, themeLabel } from '../../app/theme.js';
import { COPIED_MS, LANDING_HOOKS } from '../hooks.js';

/** Wires the theme button: shows the current choice and cycles Auto, Light, Dark on click. */
export function installThemeToggle(doc: Document): void {
  const button = doc.getElementById(LANDING_HOOKS.themeButton);
  if (!(button instanceof HTMLButtonElement)) return;
  const sync = (): void => {
    const choice = readThemeChoice();
    const label = themeLabel(choice);
    button.setAttribute('aria-label', label);
    button.title = label;
    button.dataset['choice'] = choice;
    button.replaceChildren(themeIcon(choice, doc));
  };
  button.addEventListener('click', () => {
    cycleTheme();
    sync();
  });
  sync();
  button.hidden = false;
}

/** The part of the Clipboard API the copy buttons use. */
export interface TextClipboard {
  writeText(text: string): Promise<void>;
}

export interface CopyOptions {
  /** Null where the Clipboard API is missing (older browsers, some file:// contexts). */
  readonly clipboard: TextClipboard | null;
  readonly setTimeout: (fn: () => void, ms: number) => number;
  readonly clearTimeout: (handle: number) => void;
}

/** What the live region says after a copy attempt. */
export function copyMessage(outcome: 'copied' | 'selected', text: string): string {
  return outcome === 'copied' ? `Copied: ${text}` : `Selected: ${text}. Copy it with Ctrl C, or Cmd C on a Mac.`;
}

function announce(doc: Document, message: string): void {
  const status = doc.getElementById(LANDING_HOOKS.status);
  if (status === null) return;
  // Clear first so the same message twice in a row is announced twice.
  status.textContent = '';
  status.textContent = message;
}

function selectContents(doc: Document, target: Element): void {
  const selection = doc.getSelection();
  if (selection === null) return;
  const range = doc.createRange();
  range.selectNodeContents(target);
  selection.removeAllRanges();
  selection.addRange(range);
}

/** Wires every `button[data-copy-for]`: copy the named `<code>`'s text, or select it. */
export function installCopyButtons(doc: Document, options: CopyOptions): void {
  for (const button of doc.querySelectorAll<HTMLButtonElement>(`button[${LANDING_HOOKS.copyFor}]`)) {
    const targetId = button.getAttribute(LANDING_HOOKS.copyFor) ?? '';
    const target = doc.getElementById(targetId);
    const label = button.querySelector(`.${LANDING_HOOKS.copyText}`);
    if (target === null || label === null) continue;
    const idleText = label.textContent ?? 'Copy';
    let timer: number | null = null;

    const showCopied = (): void => {
      if (timer !== null) options.clearTimeout(timer);
      label.textContent = 'Copied';
      button.dataset['copied'] = 'true';
      timer = options.setTimeout(() => {
        label.textContent = idleText;
        delete button.dataset['copied'];
        timer = null;
      }, COPIED_MS);
    };
    const fallBack = (text: string): void => {
      selectContents(doc, target);
      announce(doc, copyMessage('selected', text));
    };

    button.addEventListener('click', () => {
      const text = (target.textContent ?? '').trim();
      const clipboard = options.clipboard;
      if (clipboard === null) {
        fallBack(text);
        return;
      }
      clipboard.writeText(text).then(
        () => {
          showCopied();
          announce(doc, copyMessage('copied', text));
        },
        () => fallBack(text),
      );
    });
    button.hidden = false;
  }
}

/** The browser's clipboard, or null where the API is missing. */
export function browserClipboard(nav: { readonly clipboard?: Clipboard | undefined }): TextClipboard | null {
  // `Navigator.clipboard` is typed as always present, but it is undefined outside secure contexts.
  const clipboard = nav.clipboard;
  return clipboard === undefined || typeof clipboard.writeText !== 'function' ? null : clipboard;
}
