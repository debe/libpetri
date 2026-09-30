/**
 * Structural equivalence of two libpetri DOT exports: the verified design's and an implementation's.
 *
 * Java, TypeScript, Rust and Python export byte-identical DOT for the same net (EXP-014), so equal
 * text is the fast path. When the texts differ, both are parsed into a structural model and diffed:
 *
 *  - nodes by id and kind: places `p_…`, transitions `t_…`, output junctions `j_<t>__<xor|and>_<n>`;
 *  - arcs by endpoints and kind: input, output, inhibitor, read, reset, reset+output, plus the
 *    semantic qualifiers the exporter writes into edge labels (cardinality `×n` / `*` / `≥n`,
 *    ν correlation `⟨n⟩`, timeout `⏱…ms`) and forward-input outputs;
 *  - cluster membership (nested `subgraph cluster_…` path);
 *  - transition timing interval and priority, which the exporter writes into the label.
 *
 * Presentation is ignored: colours, fonts, sizes, shapes, positions, XOR branch labels, place xlabels,
 * graph name and statement order.
 */
import type { EquivalenceResult } from './types.js';

// ───────────────────────────── DOT parsing ─────────────────────────────

type Tok =
  | { readonly t: 'id'; readonly v: string }
  | { readonly t: 'str'; readonly v: string }
  | { readonly t: 'p'; readonly v: string };

function tokenize(src: string): Tok[] {
  const out: Tok[] = [];
  let i = 0;
  const n = src.length;
  while (i < n) {
    const c = src[i]!;
    if (c === ' ' || c === '\t' || c === '\n' || c === '\r') { i++; continue; }
    if (c === '/' && src[i + 1] === '/') { while (i < n && src[i] !== '\n') i++; continue; }
    if (c === '/' && src[i + 1] === '*') { const e = src.indexOf('*/', i + 2); i = e < 0 ? n : e + 2; continue; }
    if (c === '#' && (i === 0 || src[i - 1] === '\n')) { while (i < n && src[i] !== '\n') i++; continue; }
    if (c === '"') {
      let v = '';
      i++;
      while (i < n && src[i] !== '"') {
        if (src[i] === '\\' && i + 1 < n) {
          const nx = src[i + 1]!;
          // DOT only unescapes \" (and a line continuation); other escapes are kept verbatim.
          if (nx === '"') { v += '"'; i += 2; continue; }
          if (nx === '\n') { i += 2; continue; }
          v += '\\' + nx; i += 2; continue;
        }
        v += src[i]; i++;
      }
      i++;
      out.push({ t: 'str', v });
      continue;
    }
    if (c === '<') {
      // HTML-like label: balanced angle brackets.
      let depth = 0; let v = '';
      while (i < n) {
        const ch = src[i]!;
        if (ch === '<') depth++;
        if (ch === '>') depth--;
        v += ch; i++;
        if (depth === 0) break;
      }
      out.push({ t: 'str', v: v.slice(1, -1) });
      continue;
    }
    if (c === '-' && (src[i + 1] === '>' || src[i + 1] === '-')) { out.push({ t: 'p', v: '-' + src[i + 1] }); i += 2; continue; }
    if ('{}[]=;,:'.includes(c)) { out.push({ t: 'p', v: c }); i++; continue; }
    let v = '';
    while (i < n && !/[\s{}[\]=;,:"<]/.test(src[i]!) && !(src[i] === '-' && (src[i + 1] === '>' || src[i + 1] === '-'))) { v += src[i]; i++; }
    if (v === '') throw new Error(`DOT parse error: unexpected character '${c}' at offset ${i}`);
    out.push({ t: 'id', v });
  }
  return out;
}

interface RawNode { id: string; attrs: Record<string, string>; clusters: string[] }
interface RawEdge { from: string; to: string; attrs: Record<string, string> }
interface RawGraph { nodes: Map<string, RawNode>; edges: RawEdge[] }

function parseDot(src: string): RawGraph {
  const toks = tokenize(src);
  let k = 0;
  const peek = (): Tok | undefined => toks[k];
  const isP = (v: string): boolean => { const t = toks[k]; return t !== undefined && t.t === 'p' && t.v === v; };
  const expectP = (v: string): void => {
    if (!isP(v)) throw new Error(`DOT parse error: expected '${v}' but found '${toks[k]?.v ?? 'end of input'}'`);
    k++;
  };
  const word = (): string => {
    const t = toks[k];
    if (!t || t.t === 'p') throw new Error(`DOT parse error: expected an identifier but found '${t?.v ?? 'end of input'}'`);
    k++;
    return t.v;
  };
  const attrList = (): Record<string, string> => {
    const a: Record<string, string> = {};
    while (isP('[')) {
      k++;
      while (!isP(']')) {
        const key = word();
        let val = 'true';
        if (isP('=')) { k++; val = word(); }
        a[key] = val;
        if (isP(',') || isP(';')) k++;
      }
      k++;
    }
    return a;
  };
  const nodes = new Map<string, RawNode>();
  const edges: RawEdge[] = [];
  const declared = new Set<string>();
  const touch = (id: string, clusters: string[]): void => {
    if (!nodes.has(id)) nodes.set(id, { id, attrs: {}, clusters: [...clusters] });
  };
  const nodeId = (): string => {
    const id = word();
    if (isP(':')) { k++; word(); if (isP(':')) { k++; word(); } } // port suffix, ignored
    return id;
  };

  const body = (clusters: string[]): void => {
    while (!isP('}')) {
      if (peek() === undefined) throw new Error('DOT parse error: unterminated graph body');
      if (isP(';') || isP(',')) { k++; continue; }
      const t = peek()!;
      if (t.t === 'id' && (t.v === 'subgraph' || t.v === '{')) {
        k++;
        let name = '';
        if (!isP('{')) name = word();
        expectP('{');
        const path = name.startsWith('cluster') ? [...clusters, name.replace(/^cluster_?/, '')] : clusters;
        body(path);
        expectP('}');
        continue;
      }
      if (isP('{')) { k++; body(clusters); expectP('}'); continue; }
      const first = word();
      if ((first === 'node' || first === 'edge' || first === 'graph') && isP('[')) { attrList(); continue; }
      if (isP('=')) { k++; word(); continue; } // graph attribute
      // node or edge statement
      if (!first) continue;
      const chain = [first];
      while (isP('->') || isP('--')) { k++; chain.push(nodeId()); }
      const attrs = attrList();
      if (chain.length === 1) {
        // The node statement decides cluster membership (libpetri declares every node in its cluster).
        const existing = nodes.get(first);
        if (existing) { Object.assign(existing.attrs, attrs); if (!declared.has(first)) existing.clusters = [...clusters]; }
        else nodes.set(first, { id: first, attrs, clusters: [...clusters] });
        declared.add(first);
      } else {
        for (const id of chain) touch(id, clusters);
        for (let i = 0; i + 1 < chain.length; i++) edges.push({ from: chain[i]!, to: chain[i + 1]!, attrs });
      }
    }
  };

  // header: [strict] (di)graph [name] {
  while (peek() && !isP('{')) k++;
  expectP('{');
  body([]);
  return { nodes, edges };
}

// ───────────────────────────── structural model ─────────────────────────────

type NodeKind = 'place' | 'transition' | 'junction' | 'node';
type ArcKind = 'input' | 'output' | 'inhibitor' | 'read' | 'reset' | 'reset+output';

interface SNode {
  readonly id: string;
  readonly kind: NodeKind;
  /** Human name: place xlabel / transition name when present, otherwise the id without prefix. */
  readonly name: string;
  readonly cluster: string;
  readonly timing?: string;
  readonly priority?: string;
}

interface SArc {
  from: string;
  to: string;
  readonly kind: ArcKind;
  /** Semantic label content (cardinality, correlation, timeout, forward-input); '' when plain. */
  readonly qual: string;
}

interface Model { readonly nodes: Map<string, SNode>; readonly arcs: SArc[] }

function nodeKind(id: string): NodeKind {
  if (id.startsWith('p_')) return 'place';
  if (id.startsWith('t_')) return 'transition';
  if (id.startsWith('j_')) return 'junction';
  return 'node';
}

function model(dot: string): Model {
  const raw = parseDot(dot);
  const nodes = new Map<string, SNode>();
  for (const r of raw.nodes.values()) {
    const kind = nodeKind(r.id);
    let name = r.id.replace(/^[ptj]_/, '');
    let timing: string | undefined;
    let priority: string | undefined;
    if (kind === 'place' && r.attrs['xlabel']) name = r.attrs['xlabel'];
    if (kind === 'transition' && r.attrs['label'] !== undefined) {
      let label = r.attrs['label'];
      const pm = / prio=(-?\d+)$/.exec(label);
      if (pm) { priority = pm[1]; label = label.slice(0, pm.index); }
      const tm = / \[([^\]]*)\]ms$/.exec(label);
      if (tm) { timing = `[${tm[1]}]ms`; label = label.slice(0, tm.index); }
      if (label) name = label;
    }
    if (kind === 'junction') {
      const jm = /^j_(.+)__(xor|and)_(\d+)$/.exec(r.id);
      if (jm) name = `${jm[1]}:${jm[2]}#${jm[3]}`;
    }
    nodes.set(r.id, { id: r.id, kind, name, cluster: r.clusters.join('/'), timing, priority });
  }
  const arcs: SArc[] = [];
  for (const e of raw.edges) {
    const style = e.attrs['style'] ?? 'solid';
    const head = e.attrs['arrowhead'] ?? 'normal';
    const label = e.attrs['label'] ?? '';
    const intoTransition = nodeKind(e.to) === 'transition';
    let kind: ArcKind;
    const quals: string[] = [];
    if (intoTransition && nodeKind(e.from) !== 'junction') {
      if (head === 'odot') kind = 'inhibitor';
      else if (style.includes('dashed')) kind = 'read';
      else {
        kind = 'input';
        // Cardinality and ν correlation live in the label (EXP-018); nothing else does.
        if (label.includes('⟨n⟩')) quals.push('correlated');
        const card = /(×\d+|≥\d+|\*)/.exec(label);
        if (card) quals.push(card[1]!);
      }
    } else if (style.includes('bold')) {
      kind = label === 'reset+out' ? 'reset+output' : 'reset';
    } else {
      kind = 'output';
      if (style.includes('dashed')) quals.push('forward-input');
      const tm = /⏱\s*(\S+)/.exec(label);
      if (tm) quals.push(`timeout ${tm[1]}`);
    }
    arcs.push({ from: e.from, to: e.to, kind, qual: quals.join(' ') });
  }
  return { nodes, arcs };
}

// ───────────────────────────── diff ─────────────────────────────

const KIND_NOUN: Record<NodeKind, string> = { place: 'place', transition: 'transition', junction: 'output junction', node: 'node' };

function where(cluster: string): string {
  return cluster === '' ? 'top level' : `cluster '${cluster}'`;
}

function arcKey(a: SArc): string { return `${a.from}\u0000${a.to}`; }
function arcDesc(a: SArc): string { return a.qual ? `${a.kind} (${a.qual})` : a.kind; }

/** Neighbourhood signature of `id`, used to recognise renames: arcs with `id` (and its junctions) masked. */
function neighbourhood(m: Model, id: string): string {
  const jPrefix = id.startsWith('t_') ? 'j_' + id.slice(2) + '__' : null;
  const mask = (x: string): string => {
    if (x === id) return '·';
    if (jPrefix && x.startsWith(jPrefix)) return 'j·__' + x.slice(jPrefix.length);
    return x;
  };
  const sig = m.arcs
    .filter(a => mask(a.from) !== a.from || mask(a.to) !== a.to)
    .map(a => `${mask(a.from)}>${mask(a.to)}:${a.kind}:${a.qual}`)
    .sort();
  return sig.length === 0 ? '' : sig.join('|');
}

export function compareDot(designDot: string, implDot: string): EquivalenceResult {
  if (designDot === implDot) return { equal: true, differences: [] };
  let d: Model;
  let im: Model;
  try { d = model(designDot); } catch (e) { return { equal: false, differences: [`design DOT does not parse: ${(e as Error).message}`] }; }
  try { im = model(implDot); } catch (e) { return { equal: false, differences: [`implementation DOT does not parse: ${(e as Error).message}`] }; }

  const diffs: string[] = [];
  const label = (n: SNode): string => `${KIND_NOUN[n.kind]} '${n.name}'`;

  // 1. Nodes present on one side only; pair them up as renames when their arcs are identical.
  const missing = [...d.nodes.values()].filter(n => !im.nodes.has(n.id) && n.kind !== 'junction');
  const extra = [...im.nodes.values()].filter(n => !d.nodes.has(n.id) && n.kind !== 'junction');
  const rename = new Map<string, string>(); // impl id -> design id
  for (const kind of ['place', 'transition', 'node'] as const) {
    const bySig = new Map<string, SNode[]>();
    for (const n of extra.filter(x => x.kind === kind)) {
      const s = neighbourhood(im, n.id);
      if (s) bySig.set(s, [...(bySig.get(s) ?? []), n]);
    }
    const missingSigs = new Map<string, SNode[]>();
    for (const n of missing.filter(x => x.kind === kind)) {
      const s = neighbourhood(d, n.id);
      if (s) missingSigs.set(s, [...(missingSigs.get(s) ?? []), n]);
    }
    for (const [s, ms] of missingSigs) {
      const es = bySig.get(s);
      if (ms.length === 1 && es?.length === 1) rename.set(es[0]!.id, ms[0]!.id);
    }
  }
  for (const [implId, designId] of rename) {
    diffs.push(`${label(d.nodes.get(designId)!)} renamed to '${im.nodes.get(implId)!.name}' (same arcs)`);
  }
  const renamedDesign = new Set(rename.values());
  for (const n of missing) if (!renamedDesign.has(n.id)) diffs.push(`missing ${label(n)}: in the design, not in the implementation`);
  for (const n of extra) if (!rename.has(n.id)) diffs.push(`extra ${label(n)}: in the implementation, not in the design`);

  // Canonicalise implementation ids through the renames (junction ids follow their transition).
  const canon = (id: string): string => {
    const r = rename.get(id);
    if (r) return r;
    const jm = /^j_(.+)(__(?:xor|and)_\d+)$/.exec(id);
    if (jm) { const t = rename.get('t_' + jm[1]); if (t) return 'j_' + t.slice(2) + jm[2]; }
    return id;
  };
  const implNodes = new Map<string, SNode>();
  for (const n of im.nodes.values()) implNodes.set(canon(n.id), n);
  const implArcs = im.arcs.map(a => ({ ...a, from: canon(a.from), to: canon(a.to) }));

  // 2. Per-node attributes that carry semantics: cluster membership, timing, priority.
  for (const dn of d.nodes.values()) {
    const inn = implNodes.get(dn.id);
    if (!inn) continue;
    if (dn.kind === 'junction') continue; // junctions follow their transition
    if (dn.cluster !== inn.cluster) diffs.push(`${label(dn)} moved from ${where(dn.cluster)} to ${where(inn.cluster)}`);
    if (dn.timing !== undefined && inn.timing !== undefined && dn.timing !== inn.timing) {
      diffs.push(`${label(dn)} timing changed: ${dn.timing} in the design, ${inn.timing} in the implementation`);
    }
    if ((dn.priority ?? '0') !== (inn.priority ?? '0') && (dn.timing !== undefined) === (inn.timing !== undefined)) {
      diffs.push(`${label(dn)} priority changed: ${dn.priority ?? '0'} in the design, ${inn.priority ?? '0'} in the implementation`);
    }
  }

  // 3. Arcs, grouped by endpoint pair so a kind change reads as one difference.
  const group = (arcs: readonly SArc[]): Map<string, SArc[]> => {
    const g = new Map<string, SArc[]>();
    for (const a of arcs) g.set(arcKey(a), [...(g.get(arcKey(a)) ?? []), a]);
    return g;
  };
  const dg = group(d.arcs);
  const ig = group(implArcs);
  const name = (id: string, nodes: Map<string, SNode>): string => {
    const n = nodes.get(id);
    if (!n) return id;
    return n.kind === 'junction' ? `${n.name.split(':')[0]} (${n.name.split(':')[1]} junction)` : n.name;
  };
  const pair = (key: string): string => {
    const [from, to] = key.split('\u0000') as [string, string];
    const nodes = d.nodes.has(from) && d.nodes.has(to) ? d.nodes : implNodes;
    return `${name(from, nodes)} → ${name(to, nodes)}`;
  };
  // Arcs of nodes reported as missing/extra are implied by that report; skip them.
  const reportedMissing = new Set(missing.filter(n => !renamedDesign.has(n.id)).map(n => n.id));
  const reportedExtra = new Set(extra.filter(n => !rename.has(n.id)).map(n => canon(n.id)));
  const implied = (key: string, set: Set<string>): boolean => {
    const [from, to] = key.split('\u0000') as [string, string];
    const owner = (x: string): string => { const jm = /^j_(.+)__(?:xor|and)_\d+$/.exec(x); return jm ? 't_' + jm[1] : x; };
    return set.has(owner(from)) || set.has(owner(to));
  };
  for (const key of new Set([...dg.keys(), ...ig.keys()])) {
    const da = (dg.get(key) ?? []).map(arcDesc).sort();
    const ia = (ig.get(key) ?? []).map(arcDesc).sort();
    const onlyD = [...da]; const onlyI: string[] = [];
    for (const x of ia) { const at = onlyD.indexOf(x); if (at >= 0) onlyD.splice(at, 1); else onlyI.push(x); }
    if (onlyD.length === 0 && onlyI.length === 0) continue;
    if (onlyI.length === 0 && implied(key, reportedMissing)) continue;
    if (onlyD.length === 0 && implied(key, reportedExtra)) continue;
    if (onlyD.length === 1 && onlyI.length === 1) {
      diffs.push(`arc kind changed on ${pair(key)}: ${onlyD[0]} in the design, ${onlyI[0]} in the implementation`);
      continue;
    }
    for (const x of onlyD) diffs.push(`missing ${x} arc ${pair(key)}`);
    for (const x of onlyI) diffs.push(`extra ${x} arc ${pair(key)}`);
  }

  if (diffs.length === 0) {
    // Text differs only in presentation (colours, labels, order): structurally equal.
    return { equal: true, differences: [] };
  }
  return { equal: false, differences: diffs };
}
