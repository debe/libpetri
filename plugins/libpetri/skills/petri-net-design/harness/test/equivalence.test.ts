import { describe, expect, it } from 'vitest';
import { PetriNet, SubnetDef, Transition, one, outPlace, place, xorPlaces } from 'libpetri';
import { candidateDot } from '../src/dot.js';
import { compareDot } from '../src/equivalence.js';

const p = (n: string) => place<unknown>(n);

/** Host with one composed subnet; knobs introduce exactly one structural change each. */
function net(o: { draftName?: string; killReads?: boolean } = {}): PetriNet {
  const IN = p('IN'), BUSY = p('BUSY'), DRAFT = p('DRAFT');
  const sub = SubnetDef.builder('Answer').place(IN).place(BUSY).place(DRAFT)
    .transition(Transition.builder('start').inputs(one(IN)).outputs(outPlace(BUSY)).build())
    .transition(Transition.builder('finish').inputs(one(BUSY)).outputs(outPlace(DRAFT)).build());
  const def = sub.inputPort('in', IN).outputPort('draft', DRAFT).build();
  const SRC = p('SRC'), A = p('A_IN'), OK = p('OK'), BAD = p('BAD'), OUT = p(o.draftName ?? 'OUT_DRAFT');
  const kill = Transition.builder('kill').inputs(one(BAD)).outputs(outPlace(p('DONE')));
  if (o.killReads) kill.read(OUT); else kill.inhibitor(OUT);
  return PetriNet.builder('eq')
    .transition(Transition.builder('go').inputs(one(SRC)).outputs(xorPlaces(A, OK, BAD)).build())
    .transition(kill.build())
    .transition(Transition.builder('send').inputs(one(OUT), one(OK)).outputs(outPlace(p('DONE'))).build())
    .compose(def.instantiate('answer'), { in: A, draft: OUT })
    .build();
}

describe('compareDot', () => {
  it('treats identical DOT as equal (fast path)', () => {
    const d = candidateDot(net());
    expect(compareDot(d, d)).toEqual({ equal: true, differences: [] });
  });

  it('ignores presentation: colours, sizes, graph name, place labels, statement order', () => {
    const d = candidateDot(net());
    const lines = d
      .replace('digraph eq {', 'digraph renamed_graph {')
      .replace(/#[0-9A-Fa-f]{6}/g, '#123456')
      .replace(/fontsize=\d+/g, 'fontsize=9')
      .replace(/penwidth=[\d.]+/g, 'penwidth=4')
      .split('\n');
    // Swap the order of the top-level edge statements.
    const edgeIdx = lines.map((l, i) => (/^ {4}\S+ -> /.test(l) ? i : -1)).filter(i => i >= 0);
    const edges = edgeIdx.map(i => lines[i]!).reverse();
    edgeIdx.forEach((i, j) => { lines[i] = edges[j]!; });
    const restyled = lines.join('\n');
    expect(restyled).not.toBe(d);
    expect(compareDot(d, restyled)).toEqual({ equal: true, differences: [] });
  });

  it('detects a renamed place', () => {
    const res = compareDot(candidateDot(net()), candidateDot(net({ draftName: 'DRAFT_OUT' })));
    expect(res.equal).toBe(false);
    expect(res.differences).toContain("place 'OUT_DRAFT' renamed to 'DRAFT_OUT' (same arcs)");
  });

  it('detects a changed arc kind', () => {
    const res = compareDot(candidateDot(net()), candidateDot(net({ killReads: true })));
    expect(res.equal).toBe(false);
    expect(res.differences).toEqual(['arc kind changed on OUT_DRAFT → kill: inhibitor in the design, read in the implementation']);
  });

  it('detects a transition moved out of its cluster', () => {
    const d = candidateDot(net());
    // Lift t_answer_finish out of `subgraph cluster_answer` to the top level.
    const lines = d.split('\n');
    const inCluster = lines.filter(l => l.startsWith('        ') && l.includes('t_answer_finish'));
    expect(inCluster.length).toBeGreaterThan(1); // node statement + intra-cluster arcs
    const rest = lines.filter(l => !inCluster.includes(l));
    rest.splice(rest.length - 2, 0, ...inCluster.map(l => '    ' + l.trim()));
    lines.splice(0, lines.length, ...rest);
    const res = compareDot(d, lines.join('\n'));
    expect(res.equal).toBe(false);
    expect(res.differences).toEqual(["transition 'answer/finish' moved from cluster 'answer' to top level"]);
  });

  it('reports missing and extra places and arcs', () => {
    const a = 'digraph x { p_A [xlabel="A"]; t_T [label="T [0, ∞]ms"]; p_A -> t_T; }';
    const b = 'digraph x { p_B [xlabel="B"]; t_T [label="T [0, ∞]ms prio=3"]; t_T -> p_B; }';
    const res = compareDot(a, b);
    expect(res.differences).toContain("missing place 'A': in the design, not in the implementation");
    expect(res.differences).toContain("extra place 'B': in the implementation, not in the design");
    expect(res.differences).toContain("transition 'T' priority changed: 0 in the design, 3 in the implementation");
  });

  it('reports unparseable input instead of throwing', () => {
    expect(compareDot('digraph x { a -> ', 'digraph y {}').equal).toBe(false);
  });
});
