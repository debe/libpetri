/**
 * Parity with the CI gate `scripts/spec-lean-alignment.py`: the Python script's own functions run
 * on the real spec and Lean report, and the TypeScript port must find the same active IDs,
 * tombstones, sections, units and present quotes.
 */
import { execFileSync } from 'node:child_process';
import { readdirSync } from 'node:fs';
import { beforeAll, describe, expect, it } from 'vitest';
import { fileSections, quotePresent, splitLines, type SpecUnit } from '../src/gen/inputs/alignment.js';
import { readGlossary } from '../src/gen/inputs/glossary.js';
import { readLean } from '../src/gen/inputs/lean.js';
import { readSource } from '../src/gen/inputs/source.js';
import { parseSpecIndex, readSpec, SPEC_INDEX_FILE } from '../src/gen/inputs/spec.js';
import { REPO_ROOT } from '../src/gen/paths.js';

interface PythonView {
  readonly active: string[];
  readonly tombstones: string[];
  readonly sections: Record<string, { file: string; line: number; units: Array<[string[], number | null]> }>;
  readonly quotesPresent: string[];
  readonly quotesMissing: string[];
}

const PYTHON = String.raw`
import importlib.util, json, sys
from pathlib import Path
repo = Path(sys.argv[1])
spec = importlib.util.spec_from_file_location("align", repo / "scripts" / "spec-lean-alignment.py")
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
active, tombstones = m.active_ids((repo / "spec" / "00-index.md").read_text(encoding="utf-8"))
sections, dups, warns = m.spec_sections(repo / "spec")
blocks, cites = m.load_registry(repo / "lean" / "report" / "requirements.json")
present, missing = [], []
for b in blocks:
    if b.get("source") != "verbatim":
        continue
    sec = sections.get(b["id"])
    for i, q in enumerate(b.get("quotes") or []):
        hit = sec is not None and m.norm(q) != "" and bool(m.match_quote(m.norm(q), sec))
        (present if hit else missing).append(f"{b['decl']}#{i}")
print(json.dumps({
    "active": sorted(active),
    "tombstones": sorted(tombstones),
    "sections": {k: {"file": s.fname, "line": s.line, "units": [[u.sents, u.ac] for u in s.units]} for k, s in sections.items()},
    "quotesPresent": present,
    "quotesMissing": missing,
}))
`;

const sorted = (xs: Iterable<string>): string[] => [...xs].sort();

describe('parity with scripts/spec-lean-alignment.py', () => {
  let py: PythonView;
  beforeAll(() => {
    const out = execFileSync('python3', ['-I', '-c', PYTHON, REPO_ROOT], { encoding: 'utf8', maxBuffer: 64 * 1024 * 1024 });
    py = JSON.parse(out) as PythonView;
  });

  it('reads the same active IDs and tombstones from the index', () => {
    const index = parseSpecIndex(readSource(REPO_ROOT, SPEC_INDEX_FILE));
    expect(sorted(index.active)).toEqual(py.active);
    expect(sorted(index.tombstones)).toEqual(py.tombstones);
    expect(py.active.length).toBeGreaterThan(200);
  });

  it('finds the same blocks: active IDs, tombstones and heading lines', () => {
    const spec = readSpec(REPO_ROOT, readGlossary(REPO_ROOT));
    expect(sorted(spec.blocks.filter((b) => b.status.state !== 'removed').map((b) => b.id))).toEqual(py.active);
    expect(sorted(spec.blocks.filter((b) => b.status.state === 'removed').map((b) => b.id))).toEqual(py.tombstones);
    expect(sorted(spec.blocks.map((b) => b.id))).toEqual(sorted(Object.keys(py.sections)));
    for (const b of spec.blocks) {
      expect({ id: b.id, file: b.file, line: b.line }).toEqual({ id: b.id, file: py.sections[b.id]?.file, line: py.sections[b.id]?.line });
    }
  });

  it('cuts every section of every spec/*.md file into the same units and sentences', () => {
    const files = readdirSync(`${REPO_ROOT}/spec`).filter((f) => f.endsWith('.md')).sort();
    const ts: Record<string, { file: string; line: number; units: Array<[readonly string[], number | null]> }> = {};
    for (const file of files) {
      for (const sec of fileSections(file, splitLines(readSource(REPO_ROOT, `spec/${file}`)))) {
        ts[sec.id] ??= { file, line: sec.line, units: sec.units.map((u: SpecUnit) => [u.sents, u.ac]) };
      }
    }
    expect(ts).toEqual(py.sections);
  });

  it('finds the same Lean quotes present and missing', () => {
    const spec = readSpec(REPO_ROOT, readGlossary(REPO_ROOT));
    const present: string[] = [];
    const missing: string[] = [];
    for (const b of readLean(REPO_ROOT).blocks) {
      if (b.source !== 'verbatim') continue;
      b.quotes.forEach((q, i) => (quotePresent(q, spec.units?.get(b.id) ?? []) ? present : missing).push(`${b.decl}#${i}`));
    }
    expect(present).toEqual(py.quotesPresent);
    expect(missing).toEqual(py.quotesMissing);
    expect(present.length).toBeGreaterThan(100);
  });
});
