// @vitest-environment happy-dom
import { beforeEach, describe, expect, it } from 'vitest';
import { THEME_STORAGE_KEY } from '../src/app/theme.js';
import type { CopyOptions, TextClipboard } from '../src/landing/browser/client.js';
import { browserClipboard, copyMessage, installCopyButtons, installThemeToggle } from '../src/landing/browser/client.js';
import { COPIED_MS, LANDING_HOOKS } from '../src/landing/hooks.js';

function mountCopyMarkup(): void {
  document.body.replaceChildren();
  const code = document.createElement('code');
  code.id = 'install-typescript';
  code.textContent = 'npm install libpetri';
  const button = document.createElement('button');
  button.type = 'button';
  button.hidden = true;
  button.setAttribute(LANDING_HOOKS.copyFor, code.id);
  const label = document.createElement('span');
  label.className = LANDING_HOOKS.copyText;
  label.textContent = 'Copy';
  button.append(label);
  const status = document.createElement('p');
  status.id = LANDING_HOOKS.status;
  document.body.append(code, button, status);
}

interface FakeTimers {
  readonly options: Pick<CopyOptions, 'setTimeout' | 'clearTimeout'>;
  run(): void;
  pending(): number;
}

function fakeTimers(): FakeTimers {
  const queue = new Map<number, { fn: () => void; ms: number }>();
  let next = 1;
  return {
    options: {
      setTimeout: (fn, ms) => {
        queue.set(next, { fn, ms });
        return next++;
      },
      clearTimeout: (handle) => {
        queue.delete(handle);
      },
    },
    run: () => {
      const jobs = [...queue.values()];
      queue.clear();
      for (const job of jobs) job.fn();
    },
    pending: () => queue.size,
  };
}

const flush = (): Promise<void> => new Promise((resolve) => setTimeout(resolve, 0));

const button = (): HTMLButtonElement => {
  const b = document.querySelector('button');
  if (!(b instanceof HTMLButtonElement)) throw new Error('no button');
  return b;
};

describe('theme toggle', () => {
  beforeEach(() => {
    localStorage.clear();
    delete document.documentElement.dataset['theme'];
    document.body.replaceChildren();
    const b = document.createElement('button');
    b.id = LANDING_HOOKS.themeButton;
    b.hidden = true;
    document.body.append(b);
  });

  it('reveals itself and cycles Auto, Light, Dark with the shared storage key', () => {
    installThemeToggle(document);
    const b = button();
    expect(b.hidden).toBe(false);
    expect(b.getAttribute('aria-label')).toBe('Theme: Auto');
    b.click();
    expect(b.getAttribute('aria-label')).toBe('Theme: Light');
    expect(document.documentElement.dataset['theme']).toBe('light');
    expect(localStorage.getItem(THEME_STORAGE_KEY)).toBe('light');
    b.click();
    expect(b.getAttribute('aria-label')).toBe('Theme: Dark');
    b.click();
    expect(b.getAttribute('aria-label')).toBe('Theme: Auto');
    expect(document.documentElement.dataset['theme']).toBeUndefined();
  });
});

describe('copy buttons', () => {
  beforeEach(mountCopyMarkup);

  it('copies the command, says Copied, announces it and resets after the delay', async () => {
    const copied: string[] = [];
    const clipboard: TextClipboard = { writeText: (text) => (copied.push(text), Promise.resolve()) };
    const timers = fakeTimers();
    installCopyButtons(document, { clipboard, ...timers.options });
    const b = button();
    expect(b.hidden).toBe(false);
    b.click();
    await flush();
    expect(copied).toEqual(['npm install libpetri']);
    expect(b.textContent).toBe('Copied');
    expect(b.dataset['copied']).toBe('true');
    expect(document.getElementById(LANDING_HOOKS.status)?.textContent).toBe(copyMessage('copied', 'npm install libpetri'));
    b.click();
    await flush();
    expect(timers.pending()).toBe(1);
    timers.run();
    expect(b.textContent).toBe('Copy');
    expect(b.dataset['copied']).toBeUndefined();
    expect(COPIED_MS).toBe(1500);
  });

  it('selects the command when there is no clipboard', () => {
    installCopyButtons(document, { clipboard: null, ...fakeTimers().options });
    button().click();
    expect(document.getSelection()?.toString()).toBe('npm install libpetri');
    expect(document.getElementById(LANDING_HOOKS.status)?.textContent).toBe(copyMessage('selected', 'npm install libpetri'));
    expect(button().textContent).toBe('Copy');
  });

  it('falls back to selecting when the clipboard refuses', async () => {
    const clipboard: TextClipboard = { writeText: () => Promise.reject(new Error('denied')) };
    installCopyButtons(document, { clipboard, ...fakeTimers().options });
    button().click();
    await flush();
    expect(document.getSelection()?.toString()).toBe('npm install libpetri');
    expect(button().textContent).toBe('Copy');
  });

  it('skips a button whose target is missing', () => {
    document.getElementById('install-typescript')?.remove();
    installCopyButtons(document, { clipboard: null, ...fakeTimers().options });
    expect(button().hidden).toBe(true);
  });
});

describe('browserClipboard', () => {
  it('is null without the Clipboard API', () => {
    expect(browserClipboard({})).toBeNull();
    expect(browserClipboard({ clipboard: undefined })).toBeNull();
  });
});
