/**
 * Input: the defect entries of the runtime ledger in `lean/report/spec.json` (`spec-json.ts`),
 * in ledger order. Lean writes each from its `runtime_defect` declaration
 * (`lean/Libpetri/Spec/Ledger/`): the spec IDs of its Requirements item, its runtimes, the
 * markdown of its Defect, Lean evidence and Fix items, the Lean names its evidence item marks
 * (none when the item starts with "none") and its status.
 *
 * Runtimes map to `Runtime` in `RUNTIMES` order; an unknown one fails the build. The ledger's
 * unbuilt entries and divergence table are not read.
 */
import type { Defect, Runtime } from '../../model.js';
import { RUNTIMES } from '../../model.js';
import { readSpecJson, SPEC_JSON_FILE, type SpecJson } from './spec-json.js';
import { inputError } from './text.js';

export function defectsOf(data: SpecJson): Defect[] {
  return data.defects.map((d): Defect => {
    const names = d.runtimes.map((r) => r.toLowerCase());
    const unknown = names.find((r) => !RUNTIMES.some((x) => x === r));
    if (unknown !== undefined || names.length === 0) throw inputError(SPEC_JSON_FILE, null, `${d.id}: unknown runtime in ${JSON.stringify(d.runtimes)}`);
    const runtimes = RUNTIMES.filter((r: Runtime) => names.includes(r));
    const status = d.status.state === 'open' ? { state: 'open' as const } : { state: 'fixed' as const, version: d.status.version ?? null };
    return { id: d.id, title: d.title, requirements: d.requirements, runtimes, text: d.text, evidence: d.evidence, evidenceText: d.evidenceText, fix: d.fix, status };
  });
}

export function readDefects(root: string): readonly Defect[] {
  return defectsOf(readSpecJson(root));
}
