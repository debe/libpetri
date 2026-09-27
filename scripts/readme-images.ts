/**
 * Generates the README images and the text snippets the README quotes, from real nets.
 *
 * Usage (from repo root; needs `cd typescript && npm install` and a `z3` executable on PATH):
 *
 *   cd typescript && npx tsx ../scripts/readme-images.ts
 *
 * Imports libpetri from `typescript/src`, so the output reflects the working tree, and renders
 * DOT with `@viz-js/viz` (Graphviz WASM) from `typescript/node_modules`.
 *
 * Every claim the README makes about the running example is asserted here; a mismatch throws
 * and nothing is written. Output (docs/readme/), byte-identical across runs:
 *
 *   agent-net.svg             the fixed agent turn loop, with an arc-kind legend
 *   agent-counterexample.svg  the buggy loop with the deadlockFree counterexample drawn on it
 *   agent-subnets.svg         the loop as a subnet, instantiated twice in a session host
 *   tool-fanout.svg           parallel tool calls joined by call id (a ν-net)
 *   evidence.svg              spec, implementations, SMT scripts, z3, Lean
 *   verdicts.txt              verdicts, routes and the counterexample, as the verifier reports them
 *   trace.txt                 event-trace excerpt of one run with a stub model
 *   agent-net.excerpt.ts      the net definition as the README shows it
 *   agent-verify.excerpt.ts   the verifier call as the README shows it
 */

import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';

import {
  BitmapNetExecutor, InMemoryEventStore, Interface, PetriNet, SubnetDef, Transition,
  and, matchKey, matchSpec, one, outPlace, place, tokenOf, unitToken,
} from '../typescript/src/index.js';
import type { NameId, NetEvent, Place } from '../typescript/src/index.js';
import { mapToGraph, renderDot, nodeStyle, edgeStyle, sanitize } from '../typescript/src/export/index.js';
import type { Graph, GraphEdge, GraphNode, Subgraph } from '../typescript/src/export/index.js';
import { SmtVerifier, deadlockFree } from '../typescript/src/verification/index.js';
import type { SmtVerificationResult } from '../typescript/src/verification/index.js';

import {
  agentTurn, buggyAgentTurn, request, thinking, toolCall, toolBudget, answer, failed,
} from './readme/agent-net.js';

const repoRoot = resolve(__dirname, '..');
const outDir = resolve(repoRoot, 'docs', 'readme');
const K = 2; // tool budget

function check(cond: unknown, what: string): asserts cond {
  if (!cond) throw new Error(`readme-images: assertion failed: ${what}`);
}

// ======================== The running example ========================

type Turn = { question: string; notes: string[] };

/** Stub model: asks for one tool, then answers from what it saw. */
const stubModel = async (t: Turn) =>
  t.notes.length === 0 ? { tool: 'search' } : { answer: `answer from ${t.notes.length} notes` };
const stubTool = async (_t: Turn) => 'search result';

// readme:verify:start
function verifyTurn(net: PetriNet) {
  return SmtVerifier.forNet(net)
    .initialMarking(m => m.tokens(request, 1).tokens(toolBudget, 2))
    .property(deadlockFree())
    .sinkPlaces(answer, failed, toolBudget)   // unspent permits may remain
    .verify();
}
// readme:verify:end

/** The same check with the timed counterexample check on ([VER-023]). */
function verifyTurnTimed(net: PetriNet) {
  return SmtVerifier.forNet(net)
    .initialMarking(m => m.tokens(request, 1).tokens(toolBudget, K))
    .property(deadlockFree())
    .sinkPlaces(answer, failed, toolBudget)
    .timedCounterexampleCheck(true)
    .verify();
}

function verdictLine(r: SmtVerificationResult): string {
  const v = r.verdict.type;
  return `verdict: ${v[0]!.toUpperCase()}${v.slice(1)}`;
}

// ======================== Rendering helpers ========================

type Viz = { renderString(dot: string, opts: { format: string; engine: string }): string };

async function loadViz(): Promise<Viz> {
  const vizPath = resolve(repoRoot, 'typescript/node_modules/@viz-js/viz/dist/viz.js');
  const { instance } = await import(pathToFileURL(vizPath).href);
  return instance();
}

interface Svg { body: string; w: number; h: number }

/**
 * Label text in ASCII. The exporter's `⏱`, `⟵` and `⟨n⟩` are missing from Helvetica, and an SVG
 * shown as an `<img>` (GitHub, editor previews) may then draw the whole label, digits included,
 * as boxes. The diamond glyphs `✕` and `✚` stand alone in their label and render fine.
 */
function asciiLabels(dot: string): string {
  return dot
    .replace(/⏱\s*(\d+)ms ⟵(\S+?)(?=")/g, 'timeout $1 ms, forwards $2')
    .replace(/⏱\s*(\d+)ms/g, 'timeout $1 ms')
    .replace(/⟵/g, 'from ')
    .replace(/⟨n⟩/g, 'same id')
    .replace(/→/g, '->');
}

/** Label glyphs allowed outside ASCII: the junction diamonds, each alone in its text element. */
const DIAMOND_GLYPHS = new Set(['✕', '✚']);

/** Renders DOT to an SVG fragment (the `<svg>` element, no prolog/comments) with its size in pt. */
function render(viz: Viz, dot: string): Svg {
  let svg = viz.renderString(asciiLabels(dot), { format: 'svg', engine: 'dot' });
  for (const [, text] of svg.matchAll(/<text[^>]*>([^<]*)<\/text>/g)) {
    check(/^[\x20-\x7e]*$/.test(text!) || DIAMOND_GLYPHS.has(text!), `label text is ASCII: ${JSON.stringify(text)}`);
  }
  svg = svg.substring(svg.indexOf('<svg'));
  svg = svg.replace(/<!--[\s\S]*?-->\n?/g, '');
  const m = /width="([\d.]+)pt" height="([\d.]+)pt"/.exec(svg);
  check(m, 'viz output carries a size in pt');
  // Drop Graphviz's own white page polygon; the card supplies the background.
  svg = svg.replace(/<polygon fill="white" stroke="none" points="[^"]*"\/>\n?/, '');
  return { body: svg, w: Number(m[1]), h: Number(m[2]) };
}

const CARD_PAD = 14;

/** Places fragments on one white rounded card. Layout: rows of columns. */
function card(rows: Svg[][], gap = 18): string {
  const rowSizes = rows.map(r => ({
    w: r.reduce((s, x) => s + x.w, 0) + gap * (r.length - 1),
    h: Math.max(...r.map(x => x.h)),
  }));
  const W = Math.max(...rowSizes.map(r => r.w)) + 2 * CARD_PAD;
  const H = rowSizes.reduce((s, r) => s + r.h, 0) + gap * (rows.length - 1) + 2 * CARD_PAD;
  const parts: string[] = [];
  let y = CARD_PAD;
  rows.forEach((row, i) => {
    let x = CARD_PAD + (W - 2 * CARD_PAD - rowSizes[i]!.w) / 2;
    for (const frag of row) {
      const dy = (rowSizes[i]!.h - frag.h) / 2;
      parts.push(nest(frag, x, y + dy));
      x += frag.w + gap;
    }
    y += rowSizes[i]!.h + gap;
  });
  const f = (n: number) => String(Math.round(n * 100) / 100);
  return [
    `<svg xmlns="http://www.w3.org/2000/svg" xmlns:xlink="http://www.w3.org/1999/xlink" ` +
      `width="${f(W)}pt" height="${f(H)}pt" viewBox="0 0 ${f(W)} ${f(H)}">`,
    `<rect x="0.5" y="0.5" width="${f(W - 1)}" height="${f(H - 1)}" rx="10" ry="10" fill="#ffffff" stroke="#d0d7de"/>`,
    ...parts,
    '</svg>',
    '',
  ].join('\n');
}

function nest(frag: Svg, x: number, y: number): string {
  const f = (n: number) => String(Math.round(n * 100) / 100);
  return frag.body
    .replace(/^<svg[^>]*>/, m => m
      .replace(/width="[\d.]+pt"/, `x="${f(x)}" y="${f(y)}" overflow="visible" width="${f(frag.w)}"`)
      .replace(/height="[\d.]+pt"/, `height="${f(frag.h)}"`)
      .replace(/ xmlns(:xlink)?="[^"]*"/g, ''))
    .trimEnd();
}

/** Deep-maps every node and edge of a Graph, clusters included. */
function restyle(
  g: Graph,
  node: (n: GraphNode) => GraphNode,
  edge: (e: GraphEdge) => GraphEdge,
): Graph {
  const sub = (s: Subgraph): Subgraph => ({
    ...s,
    nodes: s.nodes.map(node),
    edges: s.edges?.map(edge),
    subgraphs: s.subgraphs?.map(sub),
  });
  return { ...g, nodes: g.nodes.map(node), edges: g.edges.map(edge), subgraphs: g.subgraphs.map(sub) };
}

function allEdges(g: Graph): GraphEdge[] {
  const out = [...g.edges];
  const walk = (s: Subgraph) => { out.push(...(s.edges ?? [])); s.subgraphs?.forEach(walk); };
  g.subgraphs.forEach(walk);
  return out;
}

const PLAIN = { direction: 'LR' as const, showTypes: false, showIntervals: false, showPriority: false };

/** Drops XOR branch labels that only repeat the target place's name, which the place already shows. */
function dropEchoLabels(g: Graph): Graph {
  const names = new Map<string, string>();
  const collect = (n: GraphNode) => names.set(n.id, n.semanticId);
  g.nodes.forEach(collect);
  const walk = (s: Subgraph) => { s.nodes.forEach(collect); s.subgraphs?.forEach(walk); };
  g.subgraphs.forEach(walk);
  return restyle(g, n => n, e => (e.from.startsWith('j_') && e.label === names.get(e.to) ? { ...e, label: undefined } : e));
}

/** Inside a cluster the instance prefix is the cluster's label; drop it from node labels. */
function shortInstanceLabels(g: Graph): Graph {
  const strip = (t: string) => t.replace(/^[^/\n]+\//, '');
  return restyle(
    g,
    n => ({
      ...n,
      label: strip(n.label),
      attrs: n.attrs?.['xlabel'] !== undefined ? { ...n.attrs, xlabel: strip(n.attrs['xlabel']) } : n.attrs,
    }),
    e => (e.label !== undefined ? { ...e, label: e.label.replace(/⟵[^/ ]+\//, '⟵') } : e),
  );
}

function withGraphAttrs(g: Graph, attrs: Record<string, string>): Graph {
  return { ...g, graphAttrs: { ...g.graphAttrs, ...attrs } };
}

// ======================== Image 1: the net + legend ========================

function legendDot(chain: readonly number[]): string {
  // One tiny row per arc kind, drawn with the exporter's own node and edge styles.
  const place = nodeStyle('place');
  const tr = nodeStyle('transition');
  const lines: string[] = [];
  const P = (id: string) =>
    `${id} [label="", shape=${place.shape}, style=filled, fillcolor="${place.fill}", color="${place.stroke}", ` +
    `penwidth=${place.penwidth}, width=0.22, fixedsize=true];`;
  const T = (id: string) =>
    `${id} [label="", shape=box, style=filled, fillcolor="${tr.fill}", color="${tr.stroke}", ` +
    `penwidth=${tr.penwidth}, width=0.32, height=0.22, fixedsize=true, group=row];`;
  const J = (id: string, kind: 'xor' | 'and') => {
    const s = nodeStyle(kind === 'xor' ? 'xor-junction' : 'and-junction');
    return `${id} [label="${kind === 'xor' ? '✕' : '✚'}", shape=diamond, style=filled, fillcolor="${s.fill}", ` +
      `color="${s.stroke}", penwidth=${s.penwidth}, width=0.3, height=0.3, fixedsize=true, fontsize=12, group=row];`;
  };
  const E = (a: string, b: string, kind: 'input' | 'output' | 'read' | 'inhibitor' | 'reset', label?: string, dashed = false) => {
    const s = edgeStyle(kind);
    const attrs = [`color="${s.color}"`, `style=${dashed ? 'dashed' : s.style}`, `arrowhead=${s.arrowhead}`];
    if (s.penwidth !== undefined) attrs.push(`penwidth=${s.penwidth}`);
    if (label !== undefined) attrs.push(`label="${label}"`);
    return `${a} -> ${b} [${attrs.join(', ')}];`;
  };
  const K_ = (id: string, text: string) =>
    `${id} [shape=plaintext, style="", label="${text}", fontsize=11, margin="0.02,0", group=row];`;
  const inv = (a: string, b: string) => `${a} -> ${b} [style=invis];`;

  const rows: [string, string[]][] = [
    ['consume', [P('a1'), T('a2'), E('a1', 'a2', 'input')]],
    ['read', [P('b1'), T('b2'), E('b1', 'b2', 'read', 'read')]],
    ['inhibit', [P('c1'), T('c2'), E('c1', 'c2', 'inhibitor')]],
    ['reset', [T('d1'), P('d2'), E('d1', 'd2', 'reset', 'reset')]],
    ['AND fork', [T('e1'), J('e2', 'and'), P('e3'), P('e4'), E('e1', 'e2', 'output'), E('e2', 'e3', 'output'), E('e2', 'e4', 'output')]],
    ['XOR choice', [T('f1'), J('f2', 'xor'), P('f3'), P('f4'), E('f1', 'f2', 'output'), E('f2', 'f3', 'output'), E('f2', 'f4', 'output')]],
    ['timeout', [T('g1'), J('g2', 'xor'), P('g3'), P('g4'), E('g1', 'g2', 'output'), E('g2', 'g3', 'output'), E('g2', 'g4', 'output', '⏱ 10000ms', true)]],
  ];
  lines.push('digraph legend {', '  rankdir=LR; nodesep=0.12; ranksep=0.2; fontname="Helvetica,Arial,sans-serif";');
  lines.push('  node [fontname="Helvetica,Arial,sans-serif", fontsize=10]; edge [fontname="Helvetica,Arial,sans-serif", fontsize=9, arrowsize=0.7];');
  // The items of `chain`, one after another, left to right.
  const chains = [chain];
  const ids = (body: string[]) => body.flatMap(l => { const m = /^(\w+) \[/.exec(l); return m ? [m[1]!] : []; });
  for (const chain of chains) {
    let prev: string | null = null;
    for (const i of chain) {
      const [name, body] = rows[i]!;
      const k = `k${i}`;
      lines.push(`  ${K_(k, name)}`);
      lines.push(...body.map(l => '  ' + l));
      const nodes = ids(body);
      if (prev !== null) lines.push(`  ${prev} -> ${k} [style=invis, minlen=2];`);
      lines.push(`  ${inv(k, nodes[0]!)}`);
      prev = nodes.at(-1)!;
    }
  }
  lines.push('}');
  return lines.join('\n');
}

/** A caption as a DOT fragment, so it renders in the same font as the graphs. */
function captionDot(...lines: string[]): string {
  const text = lines.map(l => l.replace(/"/g, '\\"')).join('\\n');
  return `digraph caption { node [shape=plaintext, fontname="Helvetica,Arial,sans-serif", fontsize=12, fontcolor="#24292f", margin="0.15,0.02"]; c [label="${text}"]; }`;
}

// ======================== Image 2: counterexample overlay ========================

const RED = '#d1242f';

function counterexampleGraph(net: PetriNet, r: SmtVerificationResult): Graph {
  const g = dropEchoLabels(mapToGraph(net, PLAIN));
  const edges = allEdges(g);
  const steps = new Map<GraphEdge, number[]>(); // edge -> firing steps that used it
  const onPath = new Set<string>();             // node ids on the path
  const use = (e: GraphEdge, step: number, numbered: boolean) => {
    if (!steps.has(e)) steps.set(e, []);
    if (numbered) steps.get(e)!.push(step);
    onPath.add(e.from); onPath.add(e.to);
  };
  const byName = new Map([...net.transitions].map(t => [t.name, t]));
  r.counterexampleTransitions.forEach((tName, i) => {
    const step = i + 1;
    const t = byName.get(tName);
    check(t, `counterexample names a transition of the net: ${tName}`);
    const tid = 't_' + sanitize(tName);
    const before = r.counterexampleTrace[i]!, after = r.counterexampleTrace[i + 1]!;
    for (const spec of t.inputSpecs) {
      const e = edges.find(x => x.from === 'p_' + sanitize(spec.place.name) && x.to === tid);
      check(e, `input edge ${spec.place.name} -> ${tName}`);
      use(e, step, spec.place.name !== toolBudget.name);
    }
    // Outputs: every place that gained a token, reached from the transition through its junctions.
    const gained = [...net.places].filter(p => after.tokens(p) > before.tokens(p) - (t.inputSpecs.some(s => s.place.name === p.name) ? 1 : 0));
    const junction = `j_${sanitize(tName)}__`;
    for (const p of gained) {
      const pid = 'p_' + sanitize(p.name);
      const path = findPath(edges, tid, pid, id => id.startsWith(junction));
      check(path, `output path ${tName} -> ${p.name}`);
      path.forEach(e => use(e, step, false));
    }
  });

  const stuck = r.counterexampleTrace.at(-1)!;
  const stuckPlaces = [...net.places].filter(p => stuck.tokens(p) > 0);
  const out = restyle(
    g,
    n => {
      const stuckHere = stuckPlaces.some(p => 'p_' + sanitize(p.name) === n.id);
      if (stuckHere) {
        return { ...n, fill: '#ffd7d5', stroke: RED, penwidth: 3, attrs: { ...n.attrs, xlabel: `${n.semanticId} (stuck)`, fontcolor: RED } };
      }
      if (n.id === 'p_' + sanitize(toolBudget.name)) {
        return { ...n, stroke: RED, penwidth: 2, attrs: { ...n.attrs, xlabel: `${n.semanticId}\n${K} → 0` } };
      }
      if (onPath.has(n.id)) return { ...n, stroke: RED, penwidth: Math.max(2, n.penwidth + 1) };
      return { ...n, fill: '#f6f8fa', stroke: '#b8bec5', attrs: { ...n.attrs, fontcolor: '#8c959f' } };
    },
    e => {
      const s = steps.get(e);
      if (s === undefined) return { ...e, color: '#c4c9ce', attrs: { ...e.attrs, fontcolor: '#8c959f' } };
      const nums = s.length > 0 ? s.join(', ') : undefined;
      const label = [e.label, nums].filter(x => x !== undefined).join('  ');
      return {
        ...e, color: e.arcType === 'inhibitor' ? e.color : RED, penwidth: 2.4,
        label: label === '' ? undefined : label,
        attrs: { ...e.attrs, fontcolor: RED, fontsize: '11' },
      };
    },
  );
  return out;
}

function findPath(edges: GraphEdge[], from: string, to: string, via: (id: string) => boolean): GraphEdge[] | null {
  for (const e of edges.filter(x => x.from === from)) {
    if (e.to === to) return [e];
    if (via(e.to)) {
      const rest = findPath(edges, e.to, to, via);
      if (rest) return [e, ...rest];
    }
  }
  return null;
}

// ======================== Image 3: subnets ========================

function sessionHost() {
  const def = SubnetDef.fromNet(
    agentTurn(stubModel, stubTool),
    Interface.builder()
      .inputPort('request', request)
      .outputPort('answer', answer)
      .outputPort('failed', failed)
      .build(),
  );
  const session = place<string>('session');
  const reqA = place<string>('toAlice'), reqB = place<string>('toBob');
  const ansA = place<string>('fromAlice'), ansB = place<string>('fromBob');
  const failedAny = place<Turn>('escalate');
  const done = place<string>('done');
  const open = Transition.builder('open')
    .inputs(one(session)).outputs(and(outPlace(reqA), outPlace(reqB)))
    .action(async ctx => { const q = ctx.input(session); ctx.output(reqA, q); ctx.output(reqB, q); })
    .build();
  const close = Transition.builder('close')
    .inputs(one(ansA), one(ansB)).outputs(outPlace(done))
    .action(async ctx => { ctx.output(done, `${ctx.input(ansA)} / ${ctx.input(ansB)}`); })
    .build();
  const alice = def.instantiate('alice'), bob = def.instantiate('bob');
  const net = PetriNet.builder('session')
    .transitions(open, close)
    .compose(alice, b => b.bindPort('request', reqA).bindPort('answer', ansA).bindPort('failed', failedAny))
    .compose(bob, b => b.bindPort('request', reqB).bindPort('answer', ansB).bindPort('failed', failedAny))
    .build();
  const budgetA = [...net.places].find(p => p.name === 'alice/toolBudget')!;
  const budgetB = [...net.places].find(p => p.name === 'bob/toolBudget')!;
  check(budgetA && budgetB, 'each instance owns its own toolBudget');
  return {
    net, done, escalate: failedAny, fromAlice: ansA, fromBob: ansB, budgets: [budgetA, budgetB],
    initial: new Map<Place<any>, number>([[session, 1], [budgetA, K], [budgetB, K]]),
  };
}

// ======================== Image 4: ν fan-out ========================

type Call = { id: NameId; turn: string };

function toolFanout() {
  const plan = place<string>('plan');
  const search = place<Call>('search'), fetch = place<Call>('fetch');
  const searched = place<Call>('searched'), fetched = place<Call>('fetched');
  const merged = place<string>('merged');
  const fanOut = Transition.builder('fan-out')
    .inputs(one(plan)).outputs(and(outPlace(search), outPlace(fetch)))
    .action(async ctx => {
      const call = { id: ctx.freshName(), turn: ctx.input(plan) };   // one id per tool round
      ctx.output(search, call); ctx.output(fetch, call);
    })
    .build();
  const runSearch = Transition.builder('run-search')
    .inputs(one(search)).outputs(outPlace(searched))
    .action(async ctx => { ctx.output(searched, ctx.input(search)); })
    .build();
  const runFetch = Transition.builder('run-fetch')
    .inputs(one(fetch)).outputs(outPlace(fetched))
    .action(async ctx => {
      await new Promise(r => setTimeout(r, ctx.input(fetch).turn === 'turn-1' ? 20 : 1)); // finish out of order
      ctx.output(fetched, ctx.input(fetch));
    })
    .build();
  const join = Transition.builder('join')
    .inputs(one(searched), one(fetched))
    .match(matchSpec(matchKey(searched, (c: Call) => c.id), matchKey(fetched, (c: Call) => c.id)))
    .outputs(outPlace(merged))
    .action(async ctx => {
      const a = ctx.input(searched), b = ctx.input(fetched);
      ctx.output(merged, a.turn === b.turn ? a.turn : `CROSSED ${a.turn}/${b.turn}`);
    })
    .build();
  const net = PetriNet.builder('tool-fanout').transitions(fanOut, runSearch, runFetch, join).build();
  return { net, plan, merged, search, fetch };
}

// ======================== Image 5: evidence stack ========================

function specTotal(): number {
  const index = readFileSync(resolve(repoRoot, 'spec/00-index.md'), 'utf-8');
  const m = /^\| \*\*Total\*\* \| \| \| \*\*(\d+)\*\* \|$/m.exec(index);
  check(m, 'spec/00-index.md has a Total row');
  return Number(m[1]);
}

function evidenceDot(total: number): string {
  const font = 'Helvetica,Arial,sans-serif';
  const box = (id: string, label: string, fill: string, stroke: string, extra = '') =>
    `  ${id} [label="${label}", shape=box, style="rounded,filled", fillcolor="${fill}", color="${stroke}"${extra}];`;
  const lean = 'color="#6d28d9", fontcolor="#6d28d9", style=dashed';
  return [
    'digraph evidence {',
    `  rankdir=LR; nodesep=0.25; ranksep=0.55; ordering=out; fontname="${font}";`,
    `  node [fontname="${font}", fontsize=12, margin="0.16,0.07", penwidth=1.3];`,
    `  edge [fontname="${font}", fontsize=10, color="#57606a", arrowsize=0.7];`,
    box('spec', `One specification\\n${total} requirements`, '#eef2ff', '#4f46e5'),
    box('java', 'Java', '#fff3cd', '#856404', ', width=1.1'),
    box('ts', 'TypeScript', '#fff3cd', '#856404', ', width=1.1'),
    box('rust', 'Rust', '#fff3cd', '#856404', ', width=1.1'),
    box('py', 'Python', '#fffaf0', '#b08d2a', ', style="rounded,filled,dashed", width=1.1'),
    box('smt', 'Identical SMT-LIB2\\nscripts', '#f6f8fa', '#57606a'),
    box('z3', 'z3', '#e7f5ec', '#1a7f37'),
    box('lean', 'Lean 4 proofs', '#f3e8ff', '#6d28d9'),
    '  spec -> java; spec -> ts; spec -> rust;',
    '  rust -> py [style=dashed, arrowhead=none, label=" binds"];',
    '  { rank=same; java; ts; rust; py; }',
    '  java -> smt; ts -> smt; rust -> smt;',
    '  smt -> z3;',
    `  lean -> rust [${lean}, label="precompiled executor\\nrefines the reference"];`,
    `  smt -> lean [${lean}, dir=back, label=" verifier abstraction\\n covers every run"];`,
    '  { rank=same; smt -> lean [style=invis, minlen=2]; }',
    '}',
  ].join('\n');
}

// ======================== Main ========================

async function main(): Promise<void> {
  const viz = await loadViz();
  const files = new Map<string, string>();

  // --- Verification of the running example ---
  const buggy = buggyAgentTurn(stubModel, stubTool);
  const fixed = agentTurn(stubModel, stubTool);

  const bug = await verifyTurn(buggy);
  check(bug.verdict.type === 'violated', `buggy net: expected violated, got ${bug.verdict.type}\n${bug.report}`);
  check(bug.counterexampleConfirmed === true, 'buggy net: counterexample is an ordered firing sequence');
  const last = bug.counterexampleTrace.at(-1)!;
  check(last.tokens(toolCall) === 1 && last.tokens(toolBudget) === 0,
    `buggy net: the stuck marking holds toolCall with no budget, got ${last.toString()}`);
  check(bug.counterexampleTransitions.filter(t => t === 'run-tool').length === K,
    'buggy net: the budget is spent by K tool runs');
  const bugTimed = await verifyTurnTimed(buggy);
  check(bugTimed.verdict.type === 'violated', 'buggy net (timed check): still violated');
  const ok = await verifyTurn(fixed);
  check(ok.verdict.type === 'proven', `fixed net: expected proven, got ${ok.verdict.type}\n${ok.report}`);

  // --- One run of the fixed net with the stub model ---
  const events = new InMemoryEventStore();
  const exec = new BitmapNetExecutor(
    fixed,
    new Map<Place<any>, any[]>([[request, [tokenOf('What changed in 7.0?')]], [toolBudget, [unitToken(), unitToken()]]]),
    { eventStore: events },
  );
  const final = await exec.run(5_000);
  const answered = final.peekFirst(answer)?.value;
  check(answered === 'answer from 2 notes', `run reaches answer, got ${String(answered)}`);
  const traceLines = traceExcerpt(events.events());
  check(traceLines.join('|').replace(/ +/g, ' ') ===
    'start request -> thinking|call-model thinking -> toolCall|run-tool toolCall + toolBudget -> toolResult|' +
    'observe toolResult -> thinking|call-model thinking -> answer', `trace excerpt:\n${traceLines.join('\n')}`);

  // --- Composition ---
  const host = sessionHost();
  const hostResult = await SmtVerifier.forNet(host.net)
    .initialMarking(m => { for (const [p, n] of host.initial) m.tokens(p, n); })
    .property(deadlockFree())
    .sinkPlaces(host.done, host.escalate, ...host.budgets)
    .sinkPlacesWhen(host.escalate, host.fromAlice, host.fromBob)   // after an escalation, a finished answer may wait
    .verify();
  check(hostResult.verdict.type === 'proven', `session host: expected proven, got ${hostResult.verdict.type}\n${hostResult.report}`);

  // --- ν fan-out ---
  const fan = toolFanout();
  const fanResult = await SmtVerifier.forNet(fan.net)
    .initialMarking(m => m.tokens(fan.plan, 2))
    .property(deadlockFree())
    .sinkPlaces(fan.merged)
    .fragmentMode('extended')          // run-search / run-fetch relay the id (NU-051)
    .carrierPlaces(fan.search, fan.fetch)
    .verify();
  check(fanResult.verdict.type === 'proven', `tool fan-out: expected proven, got ${fanResult.verdict.type}\n${fanResult.report}`);
  const fanRun = await new BitmapNetExecutor(fan.net, new Map([[fan.plan, [tokenOf('turn-1'), tokenOf('turn-2')]]])).run(5_000);
  const mergedValues = fanRun.peekTokens(fan.merged).map(t => t.value).sort();
  check(JSON.stringify(mergedValues) === '["turn-1","turn-2"]', `fan-out joins by id at runtime, got ${JSON.stringify(mergedValues)}`);

  // --- Text files ---
  const trace = bug.counterexampleTrace;
  const steps = bug.counterexampleTransitions.map((t, i) => {
    const note = t === 'run-tool' && trace[i + 1]!.tokens(thinking) > 0 ? '   (timeout branch)' : '';
    return `  ${String(i + 1).padStart(2)}. ${t.padEnd(11)} -> ${trace[i + 1]!.toString()}${note}`;
  });
  files.set('verdicts.txt', [
    '# Generated by scripts/readme-images.ts. Do not edit.',
    '',
    `[buggy] deadlockFree, sinks answer, failed, toolBudget; initial ${trace[0]!.toString()}`,
    verdictLine(bug),
    `route: ${bug.route}`,
    `counterexampleTiming: ${bug.counterexampleTiming}`,
    `counterexampleTiming with timedCounterexampleCheck(true): ${bugTimed.counterexampleTiming}`,
    'firing sequence:',
    ...steps,
    `stuck marking: ${last.toString()}`,
    '',
    `[fixed] same check, with give-up`,
    verdictLine(ok),
    `route: ${ok.route}`,
    '',
    `[session] two agent-turn instances (alice, bob), deadlockFree, sinks done, escalate, budgets; fromAlice, fromBob may rest once escalate is marked`,
    verdictLine(hostResult),
    `route: ${hostResult.route}`,
    '',
    `[tool-fanout] two plans in flight, join matched on call id, deadlockFree, sink merged, fragmentMode extended, carriers search, fetch`,
    verdictLine(fanResult),
    `route: ${fanResult.route}`,
    '',
  ].join('\n'));
  files.set('trace.txt', [...traceLines, '', `answer: ${JSON.stringify(answered)}`].join('\n') + '\n');

  const netSrc = readFileSync(resolve(repoRoot, 'scripts/readme/agent-net.ts'), 'utf-8');
  files.set('agent-net.excerpt.ts', between(netSrc, 'readme:net')
    .replace("'../../typescript/src/index.js'", "'libpetri'")
    .replace(/^export /gm, ''));
  const selfSrc = readFileSync(__filename, 'utf-8');
  files.set('agent-verify.excerpt.ts',
    "import { SmtVerifier, deadlockFree } from 'libpetri/verification';\n\n" + between(selfSrc, 'readme:verify'));

  // --- Images ---
  const heroGraph = withGraphAttrs(dropEchoLabels(mapToGraph(fixed, PLAIN)), { nodesep: '0.4', ranksep: '0.5' });
  files.set('agent-net.svg', card([[render(viz, renderDot(heroGraph))], [0, 1, 2, 3].map(i => render(viz, legendDot([i]))), [4, 5, 6].map(i => render(viz, legendDot([i])))], 16));

  const cex = withGraphAttrs(counterexampleGraph(buggy, bug), { nodesep: '0.4', ranksep: '0.5' });
  const cexCaption = captionDot(
    `deadlockFree is Violated after ${bug.counterexampleTransitions.length} firings. Arc numbers are the firing steps.`,
    'With the tool budget spent, the token in toolCall has no transition to take it.',
  );
  files.set('agent-counterexample.svg', card([[render(viz, renderDot(cex))], [render(viz, cexCaption)]], 4));

  const hostGraph = withGraphAttrs(
    shortInstanceLabels(dropEchoLabels(mapToGraph(host.net, { ...PLAIN, clusterSource: 'auto' }))),
    { nodesep: '0.35', ranksep: '0.45' },
  );
  const hostGraphLabelled: Graph = {
    ...hostGraph,
    subgraphs: hostGraph.subgraphs.map(sg => ({
      ...sg, label: `${sg.label} (agent-turn instance)`, attrs: { ...sg.attrs, labeljust: 'l', fontsize: '12' },
    })),
  };
  check(hostGraph.subgraphs.length === 2, `session graph has two clusters, got ${hostGraph.subgraphs.length}`);
  files.set('agent-subnets.svg', card([[render(viz, renderDot(hostGraphLabelled))]]));

  const fanGraph = dropEchoLabels(mapToGraph(fan.net, PLAIN));
  files.set('tool-fanout.svg', card([
    [render(viz, renderDot(fanGraph))],
    [render(viz, captionDot(
      'fan-out mints one call id per round and stamps it on both branches.',
      'join fires only for a search and a fetch that carry the same id (teal arcs).',
    ))],
  ], 4));

  files.set('evidence.svg', card([[render(viz, evidenceDot(specTotal()))]]));

  mkdirSync(outDir, { recursive: true });
  for (const [name, content] of [...files].sort(([a], [b]) => a.localeCompare(b))) {
    writeFileSync(resolve(outDir, name), content, 'utf-8');
    console.log(`wrote docs/readme/${name}`);
  }
}

/** The lines strictly between `// <tag>:start` and `// <tag>:end`. */
function between(src: string, tag: string): string {
  const lines = src.split('\n');
  const a = lines.findIndex(l => l.trim() === `// ${tag}:start`);
  const b = lines.findIndex(l => l.trim() === `// ${tag}:end`);
  check(a >= 0 && b > a, `markers ${tag} present`);
  return lines.slice(a + 1, b).join('\n') + '\n';
}

/**
 * One line per firing, read off the event store: the places `token-removed` named before
 * `transition-started`, then the places `token-added` named before `transition-completed`.
 */
function traceExcerpt(events: readonly NetEvent[]): string[] {
  const rows: [string, string, string][] = [];
  let removed: string[] = [], added: string[] = [];
  const consumed = new Map<string, string[]>();
  for (const e of events) {
    switch (e.type) {
      case 'token-removed': removed.push(e.placeName); break;
      case 'token-added': added.push(e.placeName); break;
      case 'transition-started': consumed.set(e.transitionName, removed); removed = []; break;
      case 'transition-completed':
        rows.push([e.transitionName, (consumed.get(e.transitionName) ?? []).join(' + '), added.join(' + ')]);
        added = [];
        break;
      default: break;
    }
  }
  const w0 = Math.max(...rows.map(r => r[0].length)), w1 = Math.max(...rows.map(r => r[1].length));
  return rows.map(([t, from, to]) => `${t.padEnd(w0)}  ${from.padEnd(w1)}  ->  ${to}`);
}

main().catch(e => {
  console.error(e);
  process.exit(1);
});
