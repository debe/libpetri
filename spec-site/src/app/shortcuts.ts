/** The keyboard map shown in the help overlay (design 8.2). `keyboard.ts` implements it. */

export interface Shortcut {
  /** Keys pressed one after another (`g`, `s`) or, for `Ctrl K`, together. */
  readonly keys: readonly string[];
  readonly label: string;
}

export const SHORTCUTS: readonly Shortcut[] = [
  { keys: ['/'], label: 'Open search' },
  { keys: ['Ctrl', 'K'], label: 'Open search (Cmd K on a Mac)' },
  { keys: ['?'], label: 'Open keyboard help' },
  { keys: ['Esc'], label: 'Close the open card, drawer, overlay or menu' },
  { keys: ['g', 's'], label: 'Go to Situations' },
  { keys: ['g', 'r'], label: 'Go to Rules' },
  { keys: ['g', 'c'], label: 'Go to Conformance' },
  { keys: ['g', 'g'], label: 'Go to Graph (of the current rule, if any)' },
  { keys: ['t'], label: 'Cycle theme: Auto, Light, Dark' },
  { keys: ['j', 'k'], label: 'Rules: next / previous requirement' },
  { keys: ['[', ']'], label: 'Situations: previous / next situation' },
  { keys: ['i'], label: 'Graph: toggle neighbourhood and impact' },
  { keys: ['Space'], label: 'Player: play / pause' },
  { keys: ['←', '→'], label: 'Player: previous / next step' },
  { keys: ['Home', 'End'], label: 'Player: first / last step' },
];
