/**
 * Input: `spec/glossary.md`, its `### Term` entries under `#` / `##` group headings.
 *
 * A term's text runs from its heading to the next heading; `---` lines are dropped. Paragraphs
 * are joined with a blank line. `refs` are the `[ID]`s of the text in order of first mention.
 * Slugs are unique (a clash fails the build).
 */
import type { GlossaryTerm } from '../../model.js';
import { HEADING_RE, scanLines, splitLines } from './alignment.js';
import { joinMarkdown, toChunks } from './markdown.js';
import { readSource } from './source.js';
import { bracketIds, inputError } from './text.js';

export const GLOSSARY_FILE = 'spec/glossary.md';

/** Lower-case kebab slug of a term: `Token count` -> `token-count`, `Needs-mask` -> `needs-mask`. */
export function termSlug(term: string): string {
  return term
    .toLowerCase()
    .replace(/[^\p{L}\p{N}]+/gu, '-')
    .replace(/^-+|-+$/g, '');
}

export function parseGlossary(text: string, file: string = GLOSSARY_FILE): GlossaryTerm[] {
  const scanned = scanLines(splitLines(text));
  const terms: GlossaryTerm[] = [];
  const slugs = new Map<string, number>();
  let group: string | null = null;
  let open: { term: string; line: number; group: string; start: number } | null = null;

  const close = (end: number): void => {
    if (open === null) return;
    const body = toChunks(scanned.slice(open.start, end), open.start + 1);
    const definition = body.map((c) => joinMarkdown(c.lines)).join('\n\n');
    if (definition === '') throw inputError(file, open.line, `glossary term "${open.term}" has no text`);
    const slug = termSlug(open.term);
    const clash = slugs.get(slug);
    if (clash !== undefined) throw inputError(file, open.line, `glossary slug "${slug}" is also used at line ${clash}`);
    slugs.set(slug, open.line);
    terms.push({ term: open.term, slug, group: open.group, text: definition, refs: bracketIds(definition) });
    open = null;
  };

  scanned.forEach((l, i) => {
    if (l.fence) return;
    const m = HEADING_RE.exec(l.text);
    if (m === null) return;
    close(i);
    const level = m[1]?.length ?? 0;
    const title = l.text.trim().replace(/^#+\s*/, '').replace(/\s+#+\s*$/, '').trim();
    if (level <= 2) group = title;
    else if (level === 3) {
      if (group === null) throw inputError(file, i + 1, `term "${title}" comes before any group heading`);
      open = { term: title, line: i + 1, group, start: i + 1 };
    }
  });
  close(scanned.length);
  if (terms.length === 0) throw inputError(file, null, 'no "### Term" entries');
  return terms;
}

export function readGlossary(root: string): readonly GlossaryTerm[] {
  return parseGlossary(readSource(root, GLOSSARY_FILE));
}
