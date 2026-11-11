/**
 * Input: `lean/report/requirements.json`, written by `#write_requirements_report`
 * (`lean/spec-tools/Report.lean`): the Lean requirement blocks with their evidence theorems
 * (each with its docstring in `doc`) and the `@[evidence cites]` citations.
 *
 * Blocks stay in file order. `signoff` is `"pending"` or `"<date> <hash>"`. An evidence role
 * outside `EVIDENCE_ROLES`, an unknown kind or key, or a repeated `decl` fails the build. An
 * empty or missing `doc` becomes null. Citations are sorted by id, theorem, fragment.
 */
import { arr, str } from '../../decode.js';
import type { Citation, Evidence, EvidenceRole, LeanBlock, ReqKind, Signoff } from '../../model.js';
import { EVIDENCE_ROLES, REQ_KINDS } from '../../model.js';
import { decodeFile, objWith, parseJson } from './json-input.js';
import { readSource } from './source.js';
import { byString, inputError, REQ_ID_RE } from './text.js';

export const LEAN_REPORT_FILE = 'lean/report/requirements.json';

export interface LeanInput {
  readonly blocks: readonly LeanBlock[];
  readonly citations: readonly Citation[];
}

const rawEvidence = objWith({ theorem: str, role: str, module: str }, { doc: str });
const rawBlock = objWith(
  {
    id: str,
    title: str,
    decl: str,
    module: str,
    kind: str,
    sourceRef: str,
    source: str,
    scope: str,
    quotes: arr(str),
    reading: arr(str),
    assumes: arr(str),
    statement: str,
    signoff: str,
    hash: str,
    evidence: arr(rawEvidence),
  },
  {},
);
const rawCitation = objWith({ theorem: str, role: str, module: str, id: str, fragment: str }, { doc: str });
const rawReport = objWith({ title: str, requirements: arr(rawBlock), citations: arr(rawCitation) }, {});

const SIGNED_RE = /^(\d{4}-\d{2}-\d{2}) ([0-9a-f]{16})$/;
const HASH_RE = /^[0-9a-f]{16}$/;

/** `"pending"` or `"2026-11-10 104625b4eefcf18b"`; anything else is null. */
export function parseSignoff(text: string): Signoff | null {
  if (text === 'pending') return { state: 'pending' };
  const m = SIGNED_RE.exec(text);
  return m === null ? null : { state: 'signed', date: m[1] ?? '', hash: m[2] ?? '' };
}

function evidenceRole(role: string): EvidenceRole | undefined {
  return EVIDENCE_ROLES.find((r) => r === role);
}

function reqKind(kind: string): ReqKind | undefined {
  return REQ_KINDS.find((k) => k === kind);
}

export function parseLeanReport(text: string, file: string = LEAN_REPORT_FILE): LeanInput {
  const report = decodeFile(rawReport, parseJson(text, file), file);
  const decls = new Set<string>();
  const blocks = report.requirements.map((b, i): LeanBlock => {
    const at = (message: string): Error => inputError(file, null, `$.requirements[${i}] (${b.decl}): ${message}`);
    if (!REQ_ID_RE.test(b.id)) throw at(`malformed id "${b.id}"`);
    if (decls.has(b.decl)) throw at('decl appears twice');
    decls.add(b.decl);
    const kind = reqKind(b.kind);
    if (kind === undefined) throw at(`unknown kind "${b.kind}"; add it to REQ_KINDS in src/model.ts`);
    const signoff = parseSignoff(b.signoff);
    if (signoff === null) throw at(`signoff "${b.signoff}" is neither "pending" nor "<date> <16 hex>"`);
    if (!HASH_RE.test(b.hash)) throw at(`hash "${b.hash}" is not 16 hex digits`);
    const evidence = b.evidence.map((e, j): Evidence => {
      const role = evidenceRole(e.role);
      if (role === undefined) throw at(`evidence[${j}] role "${e.role}" is unknown; add it to EVIDENCE_ROLES in src/model.ts`);
      return { theorem: e.theorem, role, module: e.module, doc: e.doc === undefined || e.doc.trim() === '' ? null : e.doc };
    });
    return {
      id: b.id,
      title: b.title,
      decl: b.decl,
      module: b.module,
      kind,
      sourceRef: b.sourceRef,
      source: b.source,
      scope: b.scope,
      quotes: b.quotes,
      reading: b.reading,
      assumes: b.assumes,
      statement: b.statement,
      signoff,
      hash: b.hash,
      evidence,
    };
  });

  const citations = report.citations
    .map((c, i): Citation => {
      if (c.role !== 'cites') throw inputError(file, null, `$.citations[${i}] (${c.theorem}): role "${c.role}" is not "cites"`);
      if (!REQ_ID_RE.test(c.id)) throw inputError(file, null, `$.citations[${i}] (${c.theorem}): malformed id "${c.id}"`);
      return { id: c.id, theorem: c.theorem, module: c.module, fragment: c.fragment };
    })
    .sort((a, b) => byString(a.id, b.id) || byString(a.theorem, b.theorem) || byString(a.fragment, b.fragment));
  return { blocks, citations };
}

export function readLean(root: string): LeanInput {
  return parseLeanReport(readSource(root, LEAN_REPORT_FILE));
}
