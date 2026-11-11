/**
 * Copy and facts for the landing page (https://libpetri.org/). Facts come from the repository
 * README: keep them in step when the README's "Get started" table or opening changes.
 *
 * Copy rules (design 12): plain words, sentence case, no em-dashes, no marketing adjectives.
 */

export const SITE_URL = 'https://libpetri.org/';
export const REPO_URL = 'https://github.com/debe/libpetri';
const BLOB = `${REPO_URL}/blob/main/`;

/** Relative so the page works on Pages and from a checkout. */
export const SPEC_HREF = 'spec/';
export const PROOF_GRAPH_HREF = 'proof-graph/';

export const PAGE_TITLE = 'libpetri: Coloured Time Petri Nets you can prove';
export const PAGE_DESCRIPTION =
  'libpetri runs Coloured Time Petri Nets in Java, TypeScript, Rust and Python, and checks them with z3 against one specification backed by Lean proofs.';

export const PITCH = 'Coloured Time Petri Nets you can prove before they run';

export const LEDE = 'Model concurrent, time-aware workflows as Petri nets, run them, and check them before they ship.';

/** What libpetri is, in three sentences (README opening). */
export const ABOUT: readonly [string, string, string] = [
  'libpetri is a Coloured Time Petri Net engine for Java, TypeScript, Rust and Python.',
  'You describe a workflow as places that hold typed tokens and transitions that do the work.',
  'The runtime executes that net, the exporter draws it, and the verifier proves properties of it or returns the run that breaks them.',
];

export type Maturity = 'Production' | 'Beta';

export interface PackageInfo {
  /** Stable key for element ids, e.g. `install-typescript`. */
  readonly key: 'java' | 'typescript' | 'rust' | 'python';
  readonly language: string;
  /** Language and edition as the README table shows it. */
  readonly version: string;
  readonly runtime: string;
  readonly maturity: Maturity;
  /** One sentence under the runtime line; null when the runtime line says enough. */
  readonly note: string | null;
  /** What the copy button copies. */
  readonly install: string;
  /** Label above the install line. */
  readonly installLabel: string;
  readonly registry: { readonly name: string; readonly href: string };
  readonly guide: string;
}

export const PACKAGES: readonly PackageInfo[] = [
  {
    key: 'java',
    language: 'Java',
    version: 'Java 25',
    runtime: 'CompletionStage actions',
    maturity: 'Production',
    note: null,
    install: 'org.libpetri:libpetri',
    installLabel: 'Maven coordinate',
    registry: { name: 'Maven Central', href: 'https://central.sonatype.com/artifact/org.libpetri/libpetri' },
    guide: `${BLOB}java/README.md`,
  },
  {
    key: 'typescript',
    language: 'TypeScript',
    version: 'TypeScript 6',
    runtime: 'Promises and the event loop',
    maturity: 'Production',
    note: null,
    install: 'npm install libpetri',
    installLabel: 'Install',
    registry: { name: 'npm', href: 'https://www.npmjs.com/package/libpetri' },
    guide: `${BLOB}typescript/README.md`,
  },
  {
    key: 'rust',
    language: 'Rust',
    version: 'Rust 2024',
    runtime: 'Tokio',
    maturity: 'Production',
    note: null,
    install: 'cargo add libpetri --features tokio',
    installLabel: 'Install',
    registry: { name: 'crates.io', href: 'https://crates.io/crates/libpetri' },
    guide: `${BLOB}rust/README.md`,
  },
  {
    key: 'python',
    language: 'Python',
    version: 'Python ≥3.11',
    runtime: 'Tokio through PyO3',
    maturity: 'Beta',
    note: 'Binds the Rust runtime.',
    install: 'pip install libpetri',
    installLabel: 'Install',
    registry: { name: 'PyPI', href: 'https://pypi.org/project/libpetri/' },
    guide: `${BLOB}python/README.md`,
  },
];

export const Z3_NOTE = 'Verification runs the z3 executable, version 4.8.0 or newer, found on PATH or through LIBPETRI_Z3.';

export const LICENSE = { name: 'Apache 2.0', href: `${BLOB}LICENSE` } as const;

/** The evidence diagram the README shows, served next to this page. */
export const EVIDENCE_SVG = 'readme/evidence.svg';
