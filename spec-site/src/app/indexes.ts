/**
 * Lookup tables built once from `SiteData`. Views read these instead of scanning arrays.
 *
 * Owner: skeleton (core). Add a table here when two views need it; otherwise keep it local.
 */
import { edgeEnds, nodeKey } from '../model.js';
import type {
  Citation,
  Defect,
  Edge,
  GlossaryTerm,
  GraphNodeKey,
  LeanBlock,
  ReqId,
  SiteData,
  SituationEntry,
  SituationSlug,
  SpecBlock,
  SpecFile,
} from '../model.js';

export interface SiteIndex {
  /** Every block, tombstones included. */
  readonly blocks: ReadonlyMap<ReqId, SpecBlock>;
  /** Blocks in display order, tombstones excluded. */
  readonly activeBlocks: readonly SpecBlock[];
  readonly files: ReadonlyMap<string, SpecFile>;
  /** Lean blocks of an ID (empty when it has none). */
  readonly lean: (id: ReqId) => readonly LeanBlock[];
  readonly citationsByReq: ReadonlyMap<ReqId, readonly Citation[]>;
  /** Blocks whose Depends on line lists the key. */
  readonly usedBy: ReadonlyMap<ReqId, readonly ReqId[]>;
  readonly defects: ReadonlyMap<string, Defect>;
  readonly defectsByReq: ReadonlyMap<ReqId, readonly Defect[]>;
  readonly situations: ReadonlyMap<SituationSlug, SituationEntry>;
  /** Situations whose `rules` contain the key. */
  readonly situationsByReq: ReadonlyMap<ReqId, readonly SituationEntry[]>;
  /** Glossary terms by slug. */
  readonly terms: ReadonlyMap<string, GlossaryTerm>;
  /** Edges by the `nodeKey` of their source / target node (`CORE-031`, `thm:...`, `term:...`, `sit:...`, `RD-07`). */
  readonly edgesFrom: ReadonlyMap<GraphNodeKey, readonly Edge[]>;
  readonly edgesTo: ReadonlyMap<GraphNodeKey, readonly Edge[]>;
}

function push<K, V>(map: Map<K, V[]>, key: K, value: V): void {
  const list = map.get(key);
  if (list === undefined) map.set(key, [value]);
  else list.push(value);
}

export function buildIndex(data: SiteData): SiteIndex {
  const blocks = new Map(data.blocks.map((b) => [b.id, b] as const));
  const citationsByReq = new Map<ReqId, Citation[]>();
  for (const c of data.citations) push(citationsByReq, c.id, c);
  const usedBy = new Map<ReqId, ReqId[]>();
  for (const b of data.blocks) for (const dep of b.dependsOn) push(usedBy, dep, b.id);
  const defectsByReq = new Map<ReqId, Defect[]>();
  for (const d of data.defects) for (const id of d.requirements) push(defectsByReq, id, d);
  const situationsByReq = new Map<ReqId, SituationEntry[]>();
  for (const s of data.situations) for (const r of s.rules) push(situationsByReq, r.id, s);
  const edgesFrom = new Map<GraphNodeKey, Edge[]>();
  const edgesTo = new Map<GraphNodeKey, Edge[]>();
  for (const e of data.edges) {
    const ends = edgeEnds(e);
    push(edgesFrom, nodeKey(ends.from), e);
    push(edgesTo, nodeKey(ends.to), e);
  }
  const empty: readonly LeanBlock[] = [];
  return {
    blocks,
    activeBlocks: data.blocks.filter((b) => b.status.state !== 'removed'),
    files: new Map(data.files.map((f) => [f.file, f] as const)),
    lean: (id) => data.lean[id] ?? empty,
    citationsByReq,
    usedBy,
    defects: new Map(data.defects.map((d) => [d.id, d] as const)),
    defectsByReq,
    situations: new Map(data.situations.map((s) => [s.slug, s] as const)),
    situationsByReq,
    terms: new Map(data.glossary.map((t) => [t.slug, t] as const)),
    edgesFrom,
    edgesTo,
  };
}
