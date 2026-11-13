/**
 * Input: `lean/report/spec.json`, the spec as data. `#write_spec_json` (`lean/spec-tools/Report.lean`)
 * writes it from the Lean spec text (`lean/Libpetri/Spec/Text/`) and the runtime ledger
 * (`lean/Libpetri/Spec/Ledger/`), and Lean is the one reader of the markdown it renders: every
 * requirement arrives with its body already cut into paragraphs, acceptance criteria, notes,
 * depends-on, mentions and test derivation, so the site parses no markdown.
 *
 * This module only decodes the file: an unknown or missing key, or a value of the wrong type or
 * outside its set (a priority, kind, status, paragraph kind or defect state), fails the build.
 * `spec.ts`, `glossary.ts` and `defects.ts` turn the decoded file into the site's model.
 */
import { arr, type DecodedOf, int, nullable, oneOf, str } from '../../decode.js';
import { PRIORITIES, REQ_KINDS } from '../../model.js';
import { decodeFile, objWith, parseJson } from './json-input.js';
import { readSource } from './source.js';

export const SPEC_JSON_FILE = 'lean/report/spec.json';

const rawSection = objWith({ title: str, ids: arr(str) }, {});
const rawChapter = objWith({ file: str, number: str, title: nullable(str), scope: str, prefixes: arr(str), sections: arr(rawSection) }, {});
const rawLabelled = objWith({ label: str, text: str }, {});
const rawParagraph = objWith({ kind: oneOf(['prose', 'shall', 'code']), text: str }, {});
const rawRequirement = objWith(
  {
    id: str,
    title: str,
    priority: nullable(oneOf(PRIORITIES)),
    kind: nullable(oneOf(REQ_KINDS)),
    status: oneOf(['active', 'proposed', 'removed']),
    file: str,
    line: int,
    section: nullable(str),
    source: str,
    body: str,
    spans: arr(rawLabelled),
    paragraphs: arr(rawParagraph),
    acceptance: arr(str),
    notes: arr(rawLabelled),
    dependsOn: arr(str),
    mentions: arr(str),
    testDerivation: nullable(str),
  },
  {},
);
const rawTerm = objWith({ term: str, group: str, text: str, refs: arr(str) }, {});
const rawDefect = objWith(
  {
    id: str,
    title: str,
    requirements: arr(str),
    runtimes: arr(str),
    text: str,
    evidence: arr(str),
    evidenceText: str,
    fix: nullable(str),
    status: objWith({ state: oneOf(['open', 'fixed']) }, { version: nullable(str) }),
  },
  {},
);
const rawUnbuilt = objWith({ id: str, title: str, requirements: arr(str), runtimes: arr(str), missing: str, status: str }, {});
const rawDivergence = objWith({ aspect: str, spec: str, java: str, typescript: str, rust: str }, {});
const rawSpec = objWith(
  {
    $comment: str,
    chapters: arr(rawChapter),
    requirements: arr(rawRequirement),
    glossary: arr(rawTerm),
    defects: arr(rawDefect),
    unbuilt: arr(rawUnbuilt),
    divergences: arr(rawDivergence),
  },
  {},
);

/** The decoded `spec.json`. */
export type SpecJson = DecodedOf<typeof rawSpec>;

export function parseSpecJson(text: string, file: string = SPEC_JSON_FILE): SpecJson {
  return decodeFile(rawSpec, parseJson(text, file), file);
}

export function readSpecJson(root: string): SpecJson {
  return parseSpecJson(readSource(root, SPEC_JSON_FILE));
}
