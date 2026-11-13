/**
 * Input: the glossary terms of `lean/report/spec.json` (`spec-json.ts`), each with its group (the
 * `#` or `##` heading it sits under), its text (paragraphs joined with a blank line) and the IDs
 * it cites in order of first mention, as Lean reads them from `spec/glossary.md`.
 *
 * The site adds a slug per term; slugs are unique (a clash fails the build).
 */
import type { GlossaryTerm } from '../../model.js';
import { readSpecJson, SPEC_JSON_FILE, type SpecJson } from './spec-json.js';
import { inputError } from './text.js';

/** Lower-case kebab slug of a term: `Token count` -> `token-count`, `Needs-mask` -> `needs-mask`. */
export function termSlug(term: string): string {
  return term
    .toLowerCase()
    .replace(/[^\p{L}\p{N}]+/gu, '-')
    .replace(/^-+|-+$/g, '');
}

export function glossaryTerms(data: SpecJson): GlossaryTerm[] {
  const slugs = new Map<string, string>();
  const terms = data.glossary.map((t): GlossaryTerm => {
    const slug = termSlug(t.term);
    const clash = slugs.get(slug);
    if (clash !== undefined) throw inputError(SPEC_JSON_FILE, null, `glossary slug "${slug}" of "${t.term}" is also the slug of "${clash}"`);
    slugs.set(slug, t.term);
    return { term: t.term, slug, group: t.group, text: t.text, refs: t.refs };
  });
  if (terms.length === 0) throw inputError(SPEC_JSON_FILE, null, 'no glossary terms');
  return terms;
}

export function readGlossary(root: string): readonly GlossaryTerm[] {
  return glossaryTerms(readSpecJson(root));
}
