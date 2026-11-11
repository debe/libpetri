/**
 * Situation diagrams: corpus net -> libpetri `PetriNet` (TypeScript builder API) -> `mapToGraph`
 * + `renderDot` (exactly what `dotExport` does; styles from `spec/petri-net-styles.json`,
 * EXP-001..018) -> SVG with `@viz-js/viz` in Node.
 *
 * The exporter's output is kept as it is: no colour, shape or geometry changes. The SVG text is
 * only post-processed so the browser can find its parts and one page can show it several times:
 * - the XML prolog, DOCTYPE and comments are dropped, so the string starts with `<svg`;
 * - every node group gets `data-node="<dot id>"` (`p_<place>`, `t_<transition>`, `j_...`,
 *   EXP-014), `data-kind="place|transition|junction"` and `data-name="<net name>"` (the graph
 *   node's `semanticId`, so names that `sanitize` changed map back exactly);
 * - every edge group gets `data-edge="<tail>-><head>"` and `data-arc="<arc type>"`
 *   (`input`, `output`, `inhibitor`, `read`, `reset`, `reset-output`);
 * - every `id` attribute is removed;
 * - the root `<svg>` gets `preserveAspectRatio="xMidYMid meet"`.
 *
 * Graphviz numbers its groups `node<N>` / `edge<N>` in DOT declaration order; `dotOrder`
 * mirrors `renderDot`'s order and every group's `<title>` is checked against it, so a change in
 * the renderer fails the build instead of mislabelling an arc.
 *
 * Owner: DOT/SVG + player agent.
 */
import { instance, type Viz } from '@viz-js/viz';
import {
  PetriNet,
  Transition,
  all,
  and,
  atLeast,
  deadline,
  delayed,
  exact,
  exactly,
  forwardInput,
  immediate,
  one,
  outPlace,
  place,
  timeout,
  window,
  xor,
  type In,
  type Out,
  type Place,
  type Timing as NetTiming,
  type TransitionAction,
} from 'libpetri';
import { DEFAULT_DOT_CONFIG, mapToGraph, renderDot, type Graph, type GraphEdge, type GraphNode, type Subgraph } from 'libpetri/export';
import type { CorpusNet, InputArc, OutputSpec, SituationSlug, Timing } from '../model.js';
import type { SituationInput } from './inputs/situations.js';

export type DiagramMap = ReadonlyMap<SituationSlug, string>;

/** What a node group stands for, from its EXP-014 id prefix. */
export type DiagramNodeKind = 'place' | 'transition' | 'junction';

/** Arc types the `data-arc` attribute carries (the exporter's `arcType`). */
export type DiagramArc = GraphEdge['arcType'];

/**
 * The action of every diagram transition. The diagram reads structure only; the default
 * passthrough is refused on a transition with outputs (CORE-043), and this net never runs.
 */
const STRUCTURE_ONLY: TransitionAction = async () => {
  throw new Error('situation diagram net: structure only, never executed');
};

function toTiming(t: Timing): NetTiming {
  const ms = (value: number | null, key: string): number => {
    if (value === null) throw new Error(`timing '${t.kind}' needs ${key}`);
    return value;
  };
  switch (t.kind) {
    case 'immediate':
    case 'unconstrained':
      return immediate();
    case 'deadline':
      return deadline(ms(t.latestMs, 'latestMs'));
    case 'delayed':
      return delayed(ms(t.earliestMs, 'earliestMs'));
    case 'window':
      return window(ms(t.earliestMs, 'earliestMs'), ms(t.latestMs, 'latestMs'));
    case 'exact':
      return exact(ms(t.earliestMs, 'earliestMs'));
  }
}

/**
 * Builds the libpetri net of a situation with the public builder API, as the conformance
 * loader does (`typescript/tests/verification/conformance/loader.ts`). Throws with the
 * builder's message when the net is not well formed.
 */
export function buildPetriNet(name: string, net: CorpusNet): PetriNet {
  const places = new Map<string, Place<unknown>>();
  const p = (placeName: string): Place<unknown> => {
    let found = places.get(placeName);
    if (found === undefined) {
      found = place<unknown>(placeName);
      places.set(placeName, found);
    }
    return found;
  };
  const toIn = (arc: InputArc): In => {
    switch (arc.kind) {
      case 'one':
        return one(p(arc.place));
      case 'exactly':
        return exactly(arc.n, p(arc.place));
      case 'all':
        return all(p(arc.place));
      case 'atLeast':
        return atLeast(arc.n, p(arc.place));
    }
  };
  const toOut = (spec: OutputSpec): Out => {
    switch (spec.type) {
      case 'place':
        return outPlace(p(spec.place));
      case 'and':
        return and(...spec.children.map(toOut));
      case 'xor':
        return xor(...spec.children.map(toOut));
      case 'timeout':
        return timeout(spec.afterMs, toOut(spec.child));
      case 'forward':
        return forwardInput(p(spec.from), p(spec.to));
    }
  };

  const builder = PetriNet.builder(name);
  for (const t of net.transitions) {
    const tb = Transition.builder(t.name).inputs(...t.inputs.map(toIn));
    for (const name of t.inhibitors) tb.inhibitor(p(name));
    for (const name of t.reads) tb.read(p(name));
    for (const name of t.resets) tb.reset(p(name));
    if (t.output !== null) tb.outputs(toOut(t.output));
    if (t.priority !== 0) tb.priority(t.priority);
    if (t.timing !== null) tb.timing(toTiming(t.timing));
    builder.transition(tb.action(STRUCTURE_ONLY).build());
  }
  for (const name of net.places) builder.place(p(name));
  return builder.build();
}

/** Nodes and edges in the order `renderDot` declares them, which is Graphviz's numbering. */
export function dotOrder(graph: Graph): { readonly nodes: readonly GraphNode[]; readonly edges: readonly GraphEdge[] } {
  const nodes: GraphNode[] = [];
  const edges: GraphEdge[] = [];
  const walk = (sg: Subgraph): void => {
    nodes.push(...sg.nodes);
    for (const nested of sg.subgraphs ?? []) walk(nested);
    edges.push(...(sg.edges ?? []));
  };
  for (const sg of graph.subgraphs) walk(sg);
  nodes.push(...graph.nodes);
  edges.push(...graph.edges);
  return { nodes, edges };
}

/** The node kind of an EXP-014 DOT id. */
export function nodeKindOf(id: string): DiagramNodeKind {
  if (id.startsWith('p_')) return 'place';
  if (id.startsWith('t_')) return 'transition';
  if (id.startsWith('j_')) return 'junction';
  throw new Error(`diagram node '${id}' has no p_, t_ or j_ prefix (EXP-014)`);
}

const ENTITIES: Readonly<Record<string, string>> = { amp: '&', lt: '<', gt: '>', quot: '"', apos: "'" };

/** Decodes the character references Graphviz writes in `<title>` text. */
export function decodeEntities(text: string): string {
  return text.replace(/&(#x[0-9a-fA-F]+|#\d+|[a-zA-Z]+);/g, (whole: string, ref: string) => {
    if (ref.startsWith('#x')) return String.fromCodePoint(Number.parseInt(ref.slice(2), 16));
    if (ref.startsWith('#')) return String.fromCodePoint(Number.parseInt(ref.slice(1), 10));
    return ENTITIES[ref] ?? whole;
  });
}

/** Escapes a value for a double-quoted XML attribute. */
export function escapeAttr(value: string): string {
  return value.replace(/&/g, '&amp;').replace(/"/g, '&quot;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
}

const GROUP = /<g id="(node|edge)(\d+)" class="(node|edge)">(\s*)<title>([^<]*)<\/title>/g;

/**
 * Post-processes Graphviz SVG text (see the module comment). Pure; throws when a group's title
 * does not match the graph, so a mislabelled diagram never ships.
 */
export function annotateSvg(svg: string, graph: Graph): string {
  const order = dotOrder(graph);
  let nodesSeen = 0;
  let edgesSeen = 0;
  let out = svg
    .replace(/<\?xml[\s\S]*?\?>/g, '')
    .replace(/<!DOCTYPE[^>]*>/gi, '')
    .replace(/<!--[\s\S]*?-->/g, '');

  out = out.replace(GROUP, (_whole: string, idKind: string, num: string, cls: string, gap: string, rawTitle: string) => {
    const title = decodeEntities(rawTitle);
    const index = Number.parseInt(num, 10) - 1;
    if (idKind !== cls) throw new Error(`diagram group ${idKind}${num} has class ${cls}`);
    if (cls === 'node') {
      const node = order.nodes[index];
      if (node === undefined || node.id !== title) {
        throw new Error(`diagram node${num} is '${title}', the graph declares '${node?.id ?? 'nothing'}'`);
      }
      nodesSeen += 1;
      return `<g class="node" data-node="${escapeAttr(node.id)}" data-kind="${nodeKindOf(node.id)}" data-name="${escapeAttr(node.semanticId)}">${gap}<title>${rawTitle}</title>`;
    }
    const edge = order.edges[index];
    const expected = edge === undefined ? 'nothing' : `${edge.from}->${edge.to}`;
    if (edge === undefined || expected !== title) {
      throw new Error(`diagram edge${num} is '${title}', the graph declares '${expected}'`);
    }
    edgesSeen += 1;
    return `<g class="edge" data-edge="${escapeAttr(expected)}" data-arc="${edge.arcType}">${gap}<title>${rawTitle}</title>`;
  });

  // Invisible edges (the exporter's cluster ghosts, EXP-016) keep their number but draw nothing.
  const drawnEdges = order.edges.filter((e) => e.style !== 'invis').length;
  if (nodesSeen !== order.nodes.length || edgesSeen !== drawnEdges) {
    throw new Error(
      `diagram has ${nodesSeen} node and ${edgesSeen} edge groups, the graph declares ${order.nodes.length} and ${drawnEdges}`,
    );
  }

  out = out.replace(/\s+id="[^"]*"/g, '');
  // Dropped comments leave blank lines behind.
  out = out.replace(/\n\s*\n/g, '\n').trimStart();
  if (!out.startsWith('<svg')) throw new Error('diagram SVG does not start with <svg');
  // Graphviz writes no preserveAspectRatio; drop one anyway so the attribute is never doubled.
  out = out.replace(/^(<svg[^>]*?)\s+preserveAspectRatio="[^"]*"/, '$1');
  out = out.replace(/^<svg/, '<svg preserveAspectRatio="xMidYMid meet"');
  return `${out.trimEnd()}\n`;
}

let vizPromise: Promise<Viz> | null = null;

function viz(): Promise<Viz> {
  vizPromise ??= instance();
  return vizPromise;
}

/**
 * True when some transition has a real time constraint. Only then do the labels show intervals:
 * in a net about firing or outputs every label would read `[0, ∞]ms`, which is noise. The
 * exporter's own `showIntervals` switch does this, so the drawing still follows EXP-001..018.
 */
export function isTimed(net: CorpusNet): boolean {
  return net.transitions.some((t) => t.timing !== null && t.timing.kind !== 'immediate' && t.timing.kind !== 'unconstrained');
}

/** The DOT text and graph of a situation net (the graph is what `dotExport` renders). */
export function situationGraph(slug: SituationSlug, net: CorpusNet): { readonly graph: Graph; readonly dot: string } {
  const graph = mapToGraph(buildPetriNet(slug, net), { ...DEFAULT_DOT_CONFIG, showIntervals: isTimed(net) });
  return { graph, dot: renderDot(graph) };
}

/** Renders one situation net to annotated SVG text. Same net, same bytes. */
export async function renderDiagram(slug: SituationSlug, net: CorpusNet): Promise<string> {
  const { graph, dot } = situationGraph(slug, net);
  const engine = await viz();
  const result = engine.render(dot, { format: 'svg' });
  if (result.status !== 'success') {
    const messages = result.errors.map((e) => e.message).join('; ');
    throw new Error(`Graphviz failed: ${messages}`);
  }
  return annotateSvg(result.output, graph);
}

/** Every situation's diagram, keyed by slug. A net that does not build fails the build. */
export async function renderDiagrams(situations: readonly SituationInput[]): Promise<DiagramMap> {
  const out = new Map<SituationSlug, string>();
  const sorted = [...situations].sort((a, b) => (a.situation.slug < b.situation.slug ? -1 : a.situation.slug > b.situation.slug ? 1 : 0));
  for (const { situation } of sorted) {
    try {
      out.set(situation.slug, await renderDiagram(situation.slug, situation.net));
    } catch (error) {
      const message = error instanceof Error ? error.message : String(error);
      throw new Error(`spec/situations/${situation.slug}.json: diagram: ${message}`);
    }
  }
  return out;
}
