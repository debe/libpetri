/**
 * Cost curve for open-net contract verification (VER-022).
 *
 * VER-022 proves a subnet once, in isolation, and the claim it makes is meant to be
 * independent of the concurrency budget the composed net runs at. That independence has been
 * observed but never measured. This script measures it, against the knobs a caller turns:
 *
 *   - **Subnet size**, swept as the number of outgoing edges. Each edge contributes a
 *     data/empty place pair, so it moves place count and port count together.
 *   - **Tokens in the budget place**, swept 1..8. Runtime default is 1.
 *   - **Input arity**, which is what the budget competes against — and which comes in two
 *     shapes that behave completely differently.
 *
 * The two input shapes are the point of this script:
 *
 *   - A **join** takes several distinct input indices and requires all of them before it
 *     fires. However large the budget, the node runs once, so a join is budget-blind.
 *   - An **OR** takes several producer edges into one index. Each is an arrival of its own,
 *     each can start an activation, and the budget is what caps them.
 *
 * Measured against 502 real compiled gadgets, every join was budget-blind (464 of 464) and
 * most ORs moved. A harness that builds only one of the two shapes will conclude the wrong
 * law, which is exactly what an earlier version of this file did.
 *
 * Two further structural dimensions:
 *
 *   - `mutex`: an internal 1-safe place (`X/idle`, taken by `start` and returned by `run`).
 *     Worth 6-13% of the class count and nothing structural.
 *   - `independent`: whether the outgoing edges route *together* (one xor choosing data for
 *     all edges or empty for all, as a compiled node gadget does) or *independently*.
 *     Correlated edges add places without adding reachable combinations; independent ones
 *     multiply.
 *
 * Run: cd typescript && npx tsx scripts/bench-open-net.ts [--smt]
 * `--smt` adds the SMT-route sweep (maxClasses 0), which shells out to z3 and is slow.
 */
import { PetriNet } from '../src/core/petri-net.js';
import { Transition } from '../src/core/transition.js';
import { place, type Place } from '../src/core/place.js';
import { one } from '../src/core/in.js';
import { and, andPlaces, outPlace, xor } from '../src/core/out.js';
import { transform } from '../src/core/transition-action.js';
import { OpenNetContract, verifyOpenNet } from '../src/verification/open-net/index.js';
import type { OpenNetResult } from '../src/verification/open-net/index.js';

/** CORE-043 is enforced by verification exactly as by compilation, so a shape still has to run. */
const produces = () => transform(() => null);

interface Shape {
  /** Outgoing edges; each contributes an `e<i>/data` + `e<i>/empty` pair. */
  readonly edges: number;
  /** Tokens in `_budget`. */
  readonly budget: number;
  /**
   * Producer edges into a single input index: the OR shape. Each is an arrival that can
   * start an activation of its own.
   */
  readonly arrivals: number;
  /**
   * Distinct input indices, all required before the node fires: the join shape. Above 1 this
   * builds a join (no skip path), and `arrivals` is one per index by construction.
   */
  readonly join?: number;
  /**
   * Whether the producer edges into the one input index are mutually exclusive — siblings of
   * an upstream XOR split, where only one branch can ever carry data and the rest carry
   * empty. An empty takes the skip path, which spends no budget, so an exclusive OR admits
   * one activation however many edges it has.
   */
  readonly exclusive?: boolean;
  /** Whether `X/idle` serialises activations (the 1-safe internal mutex). */
  readonly mutex: boolean;
  /** Whether each edge routes data/empty for itself, rather than all edges together. */
  readonly independent?: boolean;
}

interface Built {
  readonly net: PetriNet;
  readonly contract: OpenNetContract;
}

/**
 * A node gadget in the shape a compiled workflow produces: input edges carrying data or
 * empty, `edges` outgoing edges, a shared budget and a halt.
 *
 * With `join > 1` the node requires every one of `join` distinct inputs, so it fires once.
 * Otherwise a single index receives `arrivals` producer edges, each of which starts its own
 * activation.
 */
function build(shape: Shape): Built {
  const { edges, budget, arrivals, mutex, independent = false } = shape;
  const joinArity = shape.join ?? 1;
  const isJoin = joinArity > 1;
  const P = {
    in: place('X/in'), inEmpty: place('X/in_empty'), idle: place('X/idle'),
    budget: place('_budget'), halt: place('_halt'), running: place('X/running'),
    routed: place('X/routed'), done: place('X/done'), skipped: place('X/skipped'),
  };
  const data: Place<any>[] = [];
  const empty: Place<any>[] = [];
  for (let i = 0; i < edges; i++) {
    data.push(place(`e${i}/data`));
    empty.push(place(`e${i}/empty`));
  }
  // A join's distinct input indices, each required.
  const joinIns: Place<any>[] = [];
  for (let i = 0; i < joinArity; i++) joinIns.push(place(`X/in_${i}`));

  const startInputs = [
    ...(isJoin ? joinIns.map(p => one(p)) : [one(P.in)]),
    one(P.budget),
    ...(mutex ? [one(P.idle)] : []),
  ];
  const start = Transition.builder('X/start')
    .inputs(...startInputs).inhibitor(P.halt)
    .outputs(outPlace(P.running)).action(produces()).build();

  // Correlated: every edge gets data, or every edge gets empty — one binary choice for the
  // whole node. Independent: each edge chooses for itself, so the branches multiply.
  const routes = independent
    ? and(...data.map((d, i) => xor(outPlace(d), outPlace(empty[i]!))))
    : xor(andPlaces(...data), andPlaces(...empty));
  const success = and(routes, outPlace(P.routed));
  const runOut = mutex
    ? and(xor(success, andPlaces(P.halt, P.budget)), outPlace(P.idle))
    : xor(success, andPlaces(P.halt, P.budget));
  const run = Transition.builder('X/run').inputs(one(P.running))
    .outputs(runOut).action(produces()).build();

  const done = Transition.builder('X/done').inputs(one(P.routed))
    .outputs(andPlaces(P.budget, P.done)).action(produces()).build();

  const transitions = [start, run, done];
  if (!isJoin) {
    // Only the single-index shape has a skip path: a join has no "the input was empty" case
    // short of every arm being empty, which is a different gadget.
    transitions.push(Transition.builder('X/skip').inputs(one(P.inEmpty)).inhibitor(P.halt)
      .outputs(andPlaces(...empty, P.skipped)).action(produces()).build());
  }
  const net = PetriNet.builder('X').transitions(...transitions).build();

  // One activation per arrival on the OR shape; exactly one for a join however wide.
  const activations = isJoin ? 1 : arrivals;
  const builder = OpenNetContract.builder()
    .initialMarking(m => {
      m.tokens(P.budget, budget);
      if (mutex) m.tokens(P.idle, 1);
    });
  if (isJoin) {
    for (const p of joinIns) builder.arrive(1, p);
  } else if (shape.exclusive === true) {
    // Exclusive producers: one branch may carry data or empty, every other branch can only
    // carry empty. Same number of arrivals, but at most one of them can start an activation.
    builder.arrive(1, P.in, P.inEmpty);
    for (let i = 1; i < arrivals; i++) builder.arrive(1, P.inEmpty);
  } else {
    builder.arrive(arrivals, P.in, P.inEmpty);
  }
  builder.arriveAtMost(1, P.halt);
  for (let i = 0; i < edges; i++) builder.expect(`e${i}`, activations, data[i]!, empty[i]!);
  if (mutex) builder.expect('idle', 1, P.idle);
  builder.expect('budget', budget, P.budget);
  builder.expect('history', activations, ...(isJoin ? [P.done] : [P.done, P.skipped]));
  builder.terminal(P.halt, ...(isJoin ? joinIns : [P.in, P.inEmpty]));
  return { net, contract: builder.build() };
}

/** Ports as the contract counts them. */
function portCount(built: Built): number {
  return built.contract.places().length;
}

function row(shape: Shape, built: Built, r: OpenNetResult): string {
  const cols = [
    String(shape.edges).padStart(5),
    String(shape.budget).padStart(6),
    String(shape.arrivals).padStart(4),
    String(shape.join ?? 1).padStart(4),
    (shape.exclusive === true ? 'yes' : 'no').padStart(4),
    (shape.mutex ? 'yes' : 'no').padStart(5),
    (shape.independent === true ? 'yes' : 'no').padStart(5),
    String(built.net.places.size).padStart(6),
    String(portCount(built)).padStart(5),
    String(r.classCount).padStart(8) + (r.graphComplete ? ' ' : '*'),
    r.elapsedMs.toFixed(1).padStart(9),
    r.verdict.type.padEnd(8),
  ];
  return '  ' + cols.join(' ');
}

const HEADER =
  '  edges budget arrv join excl mutex indep places ports  classes   elapsed  verdict  (* = cut)';

async function sweep(title: string, note: string, shapes: Shape[], maxClasses = 200_000): Promise<void> {
  console.log(`\n${title}`);
  console.log(`  ${note}`);
  console.log(HEADER);
  for (const shape of shapes) {
    const built = build(shape);
    const r = await verifyOpenNet(built.net, built.contract, { maxClasses, smt: false });
    console.log(row(shape, built, r));
  }
}

async function main(): Promise<void> {
  const smt = process.argv.includes('--smt');
  console.log('VER-022 open-net verification: cost curve');
  console.log(`node ${process.version}`);

  await sweep(
    'A. Subnet size, correlated edges (budget 1, one arrival, serialised)',
    'Real gadgets: 7-50 places, median 9.',
    [1, 2, 4, 8, 12, 16, 20, 25].map(edges => ({ edges, budget: 1, arrivals: 1, mutex: true })),
  );

  await sweep(
    'B. Budget, single input, serialised (2 edges)',
    'One arrival, so the budget is never the cap.',
    [1, 2, 4, 8].map(budget => ({ edges: 2, budget, arrivals: 1, mutex: true })),
  );

  await sweep(
    'C. Budget, OR shape, two producer edges into one index (no mutex)',
    'Two arrivals, two activations: the budget binds until it stops being the cap.',
    [1, 2, 4, 8].map(budget => ({ edges: 2, budget, arrivals: 2, mutex: false })),
  );

  await sweep(
    'D. Arrivals on the OR shape, budget 2 (no mutex)',
    'The budget only binds once arrivals can outnumber it.',
    [1, 2, 3].map(arrivals => ({ edges: 2, budget: 2, arrivals, mutex: false })),
  );

  await sweep(
    'E. Size with concurrency (OR, no mutex, budget 2, two arrivals)',
    'Size and concurrency together: do they compose or multiply?',
    [1, 2, 4, 8, 12].map(edges => ({ edges, budget: 2, arrivals: 2, mutex: false })),
  );

  await sweep(
    'G. The plateau, OR shape: three arrivals, budget 1..6, no mutex',
    'Classes rise while budget < arrivals, then flat once budget >= 3.',
    [1, 2, 3, 4, 6].map(budget => ({ edges: 2, budget, arrivals: 3, mutex: false })),
  );

  await sweep(
    'H. Size with INDEPENDENT edges (budget 1, one arrival, serialised)',
    'Each edge routes for itself, so the reachable combinations multiply.',
    [1, 2, 3, 4, 5, 6, 8].map(edges => ({ edges, budget: 1, arrivals: 1, mutex: true, independent: true })),
  );

  await sweep(
    'I. The OR shape serialised, two arrivals (2 edges)',
    'The mutex is a constant factor: compare with C, same saturation point.',
    [1, 2, 4, 8].map(budget => ({ edges: 2, budget, arrivals: 2, mutex: true })),
  );

  await sweep(
    'J. The OR shape serialised, three arrivals (2 edges)',
    'Compare with G: lower counts, identical plateau.',
    [1, 2, 3, 4, 8].map(budget => ({ edges: 2, budget, arrivals: 3, mutex: true })),
  );

  // The branch the synthetic family was missing. A join requires every input index, so it
  // runs once at any budget: measured on 502 real gadgets, 464 of 464 joins were budget-blind.
  await sweep(
    'K. JOIN arity at budget 1 (serialised, 2 edges)',
    'Every input index required. Cost against arity, with one activation throughout.',
    [2, 3, 4, 6].map(join => ({ edges: 2, budget: 1, arrivals: 1, join, mutex: true })),
  );

  await sweep(
    'L. JOIN budget-blindness: arity 2 and 3 across budgets 1..8',
    'Prediction: perfectly flat. All inputs required means one activation at any budget.',
    [2, 3].flatMap(join => [1, 2, 4, 8].map(budget => ({ edges: 2, budget, arrivals: 1, join, mutex: true }))),
  );

  // Does an OR's budget-sensitivity come from arrivals, or from arrivals that can become
  // activations? An exclusive OR has the same arrival count and the same clause structure as
  // sweeps C/G, but only one of its branches can carry data.
  await sweep(
    'M. EXCLUSIVE OR: same arrivals, only one branch can carry data',
    'Prediction: flat. The other branches take the skip path, which spends no budget.',
    [2, 3].flatMap(arrivals => [1, 2, 4, 8].map(budget =>
      ({ edges: 2, budget, arrivals, exclusive: true, mutex: false }))),
  );

  if (!smt) {
    console.log('\n(SMT-route sweep skipped; pass --smt to include it.)');
    return;
  }
  console.log('\nF. SMT route (maxClasses 0), budget 1, one arrival, serialised');
  console.log('  The route that survives when the graph will not close.');
  console.log(HEADER);
  for (const edges of [1, 2, 4, 8]) {
    const shape: Shape = { edges, budget: 1, arrivals: 1, mutex: true };
    const built = build(shape);
    const r = await verifyOpenNet(built.net, built.contract, { maxClasses: 0 });
    console.log(row(shape, built, r));
  }
}

main().catch((e: unknown) => {
  console.error(e);
  process.exitCode = 1;
});
