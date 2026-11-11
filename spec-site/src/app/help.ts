/**
 * Keyboard help overlay (design 8.3; key `?`). Four sections, each an `h2` with the id
 * `help-<section>`: Keyboard, Reading a rule, How replays work, How to read Lean statements.
 *
 * The keyboard table comes from `SHORTCUTS`; the status legends from `status.ts`, so the help
 * shows exactly the glyphs and words the views use. The two Lean tables (`LEAN_NAMES`,
 * `EARS_NOTATION`) copy the header of `lean/report/requirements.md`; `tests/help.test.ts` parses
 * that generated report and fails when the two drift apart.
 */
import type { ReqKind } from '../model.js';
import type { AppContext } from './context.js';
import { h } from './dom.js';
import { inline } from './md.js';
import { type OverlayHandle, openOverlay } from './overlay.js';
import { SHORTCUTS } from './shortcuts.js';
import { LEAN_META, ROLE_META, ROLE_ORDER, type StatusMeta, TEST_META, TESTED_MEANS } from './status.js';

export type HelpSection = 'keyboard' | 'reading' | 'replays' | 'lean';

export const HELP_SECTIONS: readonly { readonly section: HelpSection; readonly title: string }[] = [
  { section: 'keyboard', title: 'Keyboard' },
  { section: 'reading', title: 'Reading a rule' },
  { section: 'replays', title: 'How replays work' },
  { section: 'lean', title: 'How to read Lean statements' },
];

/** Element id of a section heading. */
export function helpSectionId(section: HelpSection): string {
  return `help-${section}`;
}

/** Kind letters of a requirement (design 3.2), shared with the views' kind badges. */
export const KIND_WORD: { readonly [K in ReqKind]: string } = {
  B: 'Behaviour',
  F: 'Function',
  T: 'Timing',
  Q: 'Quality (tested, not proven)',
  A: 'Assumption',
  N: 'Configuration',
};

/** The order kinds are listed in (design 3.2): KIND_WORD's key order, typed. */
const KIND_ORDER: readonly ReqKind[] = ['B', 'F', 'T', 'Q', 'A', 'N'];

/** One row of a two-column legend table; cells are inline Markdown as the report writes them. */
export interface LegendRow {
  readonly term: string;
  readonly meaning: string;
}

/** "Names in the Lean statements" of `lean/report/requirements.md`, cell for cell. */
export const LEAN_NAMES: readonly LegendRow[] = [
  { term: '`N`', meaning: 'the type of place names; a statement holds for every `N`' },
  {
    term: '`F`',
    meaning:
      'the firing semantics under test (`F : FireRel N`); `F t m d m\'` says that transition `t` fires from marking `m`, deposits `d` and leaves marking `m\'`',
  },
  { term: '`RefFire`', meaning: 'the reference firing semantics (`Reference.Fires`), the registered witness model' },
  { term: '`Trans N`, `Reference.Trans N`', meaning: 'transitions over places named by `N`' },
  { term: '`m`, `m\'`', meaning: 'markings: token counts by place (`N → Nat`)' },
  { term: '`t`, `p`', meaning: 'a transition, a place' },
  { term: '`fun x ↦ e`', meaning: 'the function that maps `x` to `e`' },
];

/** "EARS keywords" of `lean/report/requirements.md`, cell for cell. */
export const EARS_NOTATION: readonly LegendRow[] = [
  { term: '`while P, never R`', meaning: 'no `R` step starts in a state where `P` holds' },
  { term: '`on R, shall Q`', meaning: "every `R` step from `s` to `s'` satisfies `Q s s'`" },
  { term: '`when T, shall R`', meaning: 'in a trace, every `T` is followed (at it or later) by an `R`' },
  { term: '`after T, never B`', meaning: 'in a trace, once a `T` has happened no later event is a `B`' },
  { term: '`until G, never B`', meaning: 'in a trace, no `B` happens before the first `G`' },
  { term: '`at-most-once P`', meaning: 'in a trace, at most one event is a `P`' },
  { term: '`occurs P`', meaning: 'in a trace, some event is a `P`' },
];

/** The EARS words the spec text highlights (design 3.6), in plain words. */
export const EARS_WORDS: readonly LegendRow[] = [
  { term: 'When', meaning: 'the event that triggers the requirement' },
  { term: 'While', meaning: 'a state that must hold for the requirement to apply' },
  { term: 'If … then', meaning: 'an unwanted situation and the response to it' },
  { term: 'Where', meaning: 'a feature or option that must be present' },
  { term: 'shall', meaning: 'what the system must do; "shall not" and "never" say what it must not do' },
];

export const REPLAY_SENTENCES: readonly string[] = [
  'The verified Lean reference fires each step of a situation with its firing rule and records the marking after every step.',
  'The replay uses the untimed rule: priorities and timing play no part, so a replayed step is one that may fire, not one the executor must choose.',
  'Each step says whether it should fire or be blocked, and the build fails when the replay says otherwise.',
  'A step that cannot fire stops the run, and the reference names the reason and the rule behind it, such as an inhibitor place that holds a token.',
  'CI replays every situation again and fails when the result differs from the one this page shows.',
  'Situations with timing, environment places, ν-nets, composition or export are not replayed; their rules still show their Lean evidence.',
];

/**
 * How the keys of one shortcut combine: pressed together (`Ctrl + K`), one after another
 * (`g then s`) or alternatives (`j / k`).
 */
export function keySeparator(keys: readonly string[]): '+' | 'then' | '/' {
  if (keys[0] === 'Ctrl' || keys[0] === 'Cmd') return '+';
  if (keys[0] === 'g' && keys.length === 2) return 'then';
  return '/';
}

function legendTable(ctx: AppContext, caption: string, head: readonly [string, string], rows: readonly LegendRow[], code: boolean): HTMLElement {
  return h('table', { class: 'help__table' },
    h('caption', { class: 'help__caption' }, caption),
    h('thead', null, h('tr', null, h('th', { scope: 'col' }, head[0]), h('th', { scope: 'col' }, head[1]))),
    h('tbody', null, rows.map((r) => h('tr', null,
      h('th', { scope: 'row', class: code ? 'help__code' : 'help__word' }, inline(ctx, r.term, { ears: false })),
      h('td', null, inline(ctx, r.meaning, { ears: false })),
    ))),
  );
}

function glyphLegend(caption: string, metas: readonly StatusMeta[]): HTMLElement {
  return h('div', { class: 'help__legend' },
    h('h3', { class: 'help__subtitle' }, caption),
    h('ul', { class: 'help__glyphs' }, metas.map((m) => h('li', { class: 'help__glyph-row' },
      h('span', { class: ['help__glyph', `help__glyph--${m.tone}`], 'aria-hidden': 'true' }, m.glyph),
      h('span', { class: 'help__glyph-word' }, m.word),
      h('span', { class: 'help__glyph-explain' }, m.explain),
    ))),
  );
}

function section(name: HelpSection, ...children: readonly (Node | null)[]): HTMLElement {
  const title = HELP_SECTIONS.find((s) => s.section === name)?.title ?? name;
  return h('section', { class: 'help__section', 'aria-labelledby': helpSectionId(name) },
    h('h2', { class: 'help__title', id: helpSectionId(name), tabindex: -1 }, title),
    ...children,
  );
}

function jumpTo(root: HTMLElement, name: HelpSection): void {
  const heading = root.querySelector<HTMLElement>(`#${helpSectionId(name)}`);
  if (heading === null) return;
  heading.scrollIntoView({ block: 'start' });
  heading.focus({ preventScroll: true });
}

/**
 * The overlay's content, detached (the self-test renders it). `onClose` adds the Close button
 * that touch users need when the dialog fills the screen.
 */
export function renderHelpPanel(ctx: AppContext, onClose?: () => void): HTMLElement {
  const toc = h('nav', { class: 'help__toc', 'aria-label': 'Help sections' },
    HELP_SECTIONS.map((s) => h('button', {
      type: 'button',
      class: 'help__toc-link',
      on: { click: () => jumpTo(root, s.section) },
    }, s.title)),
  );

  const keyboard = section('keyboard',
    h('p', { class: 'help__note' }, 'Single keys do nothing while you type in a field. Player keys work while focus is inside the player.'),
    h('dl', { class: 'help__keys' },
      SHORTCUTS.map((s) => [
        h('dt', null, s.keys.map((k, i) => [i > 0 ? ` ${keySeparator(s.keys)} ` : null, h('kbd', null, k)])),
        h('dd', null, s.label),
      ]),
    ),
  );

  const reading = section('reading',
    legendTable(ctx, 'EARS words in the spec text', ['Word', 'Meaning'], EARS_WORDS, false),
    h('div', { class: 'help__legend' },
      h('h3', { class: 'help__subtitle' }, 'Kind'),
      h('ul', { class: 'help__glyphs' }, KIND_ORDER.map((k) => h('li', { class: 'help__glyph-row' },
        h('span', { class: 'help__kind', 'aria-hidden': 'true' }, k),
        h('span', { class: 'help__glyph-word' }, KIND_WORD[k]),
      ))),
    ),
    glyphLegend('Evidence: theorems about the rule', ROLE_ORDER.map((r) => ROLE_META[r])),
    glyphLegend('Lean status', [LEAN_META.block, LEAN_META.cited, LEAN_META.mention, LEAN_META.none]),
    glyphLegend('Tests per language', [TEST_META.tested, TEST_META.untested, TEST_META.defect]),
    h('p', { class: 'help__note' }, TESTED_MEANS, ' Python binds the Rust runtime.'),
  );

  const replays = section('replays', h('p', { class: 'help__prose' }, REPLAY_SENTENCES.join(' ')));

  const lean = section('lean',
    h('p', { class: 'help__prose' },
      'A requirement in Lean is a statement checked against a firing semantics, never an axiom. These names and keywords appear in the statements.'),
    legendTable(ctx, 'Names in the Lean statements', ['Name', 'Meaning'], LEAN_NAMES, true),
    legendTable(ctx, 'EARS keywords', ['Notation', 'Reads as'], EARS_NOTATION, true),
  );

  const root: HTMLElement = h('div', { class: 'help__inner' },
    h('div', { class: 'help__head' },
      h('p', { class: 'help__heading' }, 'Help'),
      onClose === undefined ? null : h('button', { type: 'button', class: 'help__close', 'aria-label': 'Close help', on: { click: () => onClose() } }, '×'),
    ),
    toc,
    keyboard,
    reading,
    replays,
    lean,
  );
  return root;
}

export function openHelp(ctx: AppContext, section: HelpSection = 'keyboard'): OverlayHandle {
  let handle: OverlayHandle | null = null;
  const content = renderHelpPanel(ctx, () => handle?.close());
  const heading = content.querySelector<HTMLElement>(`#${helpSectionId(section)}`);
  // The default opening lands on Close; a jump to a section lands on its heading.
  const focus = section === 'keyboard' ? content.querySelector<HTMLElement>('.help__close') : heading;
  handle = openOverlay({
    label: 'Keyboard and reading help',
    block: 'help',
    content,
    ...(focus === null ? {} : { initialFocus: focus }),
  });
  if (section !== 'keyboard') heading?.scrollIntoView({ block: 'start' });
  return handle;
}
