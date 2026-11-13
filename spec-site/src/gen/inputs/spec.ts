/**
 * Input: the requirements and numbered chapters of `lean/report/spec.json` (`spec-json.ts`).
 *
 * Lean reads the generated chapters back and writes every requirement with its body already cut
 * into fields (`lean/Libpetri/Spec/Markdown.lean`): paragraphs (`shall`, `prose`, `code`),
 * acceptance criteria, notes, depends-on, the IDs it mentions otherwise and test derivation.
 * This module maps them onto the site model and adds what only the site needs: the glossary
 * terms each body uses. The checks that the cited IDs exist live in Lean (`#audit_spec`).
 */
import type { GlossaryTerm, SpecBlock, SpecFile } from '../../model.js';
import { readSpecJson, SPEC_JSON_FILE, type SpecJson } from './spec-json.js';
import { inputError, sortedUnique } from './text.js';

export interface SpecInput {
  readonly files: readonly SpecFile[];
  readonly blocks: readonly SpecBlock[];
  /**
   * True when the input was read from disk: `buildSiteData` then runs its cross-input checks
   * (see `checkSiteInputs` in `site.ts`). Hand-built test fixtures leave it out.
   */
  readonly checked?: boolean;
}

// ---------------------------------------------------------------------------------------------
// Glossary terms in block text
// ---------------------------------------------------------------------------------------------

export interface TermMatcher {
  readonly slug: string;
  readonly re: RegExp;
}

/** A case-insensitive whole-word matcher for each term, allowing a plural `s` / `es`. */
export function termMatchers(glossary: readonly GlossaryTerm[]): TermMatcher[] {
  return glossary.map((g) => {
    const words = g.term
      .trim()
      .split(/\s+/)
      .map((w) => w.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'))
      .join('\\s+');
    return { slug: g.slug, re: new RegExp(`(?<![\\p{L}\\p{N}_-])${words}(?:s|es)?(?![\\p{L}\\p{N}_-])`, 'iu') };
  });
}

/** Slugs of the terms that occur in the text, outside code spans, link targets and IDs. Sorted. */
export function termsIn(text: string, matchers: readonly TermMatcher[]): string[] {
  const plain = text
    .replace(/`[^`]*`/g, ' ')
    .replace(/\]\([^)]*\)/g, '] ')
    .replace(/\[[A-Z]+-\d+\]/g, ' ');
  return sortedUnique(matchers.filter((m) => m.re.test(plain)).map((m) => m.slug));
}

// ---------------------------------------------------------------------------------------------
// The requirements
// ---------------------------------------------------------------------------------------------

/** The site model of `spec.json`'s chapters and requirements; `glossary` finds the terms. */
export function specInput(data: SpecJson, glossary: readonly GlossaryTerm[]): SpecInput {
  const matchers = termMatchers(glossary);
  const files = data.chapters.map((c): SpecFile => {
    if (c.title === null) throw inputError(SPEC_JSON_FILE, null, `${c.file} has no "# NN — Title" heading`);
    return { file: c.file, number: c.number, title: c.title, prefixes: c.prefixes, sections: c.sections };
  });
  const blocks = data.requirements.map(
    (r): SpecBlock => ({
      id: r.id,
      title: r.title,
      file: r.file,
      line: r.line,
      section: r.section,
      priority: r.priority,
      kind: r.kind,
      status: { state: r.status },
      body: r.paragraphs,
      acceptance: r.acceptance,
      notes: r.notes,
      dependsOn: r.dependsOn,
      mentions: r.mentions,
      testDerivation: r.testDerivation,
      terms: termsIn(r.paragraphs.filter((p) => p.kind !== 'code').map((p) => p.text).join('\n'), matchers),
    }),
  );
  if (blocks.length === 0) throw inputError(SPEC_JSON_FILE, null, 'no requirements');
  return { files, blocks, checked: true };
}

export function readSpec(root: string, glossary: readonly GlossaryTerm[]): SpecInput {
  return specInput(readSpecJson(root), glossary);
}
