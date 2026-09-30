/**
 * Lab families from research/net-metrics/lab (Families, Subnets, EnvNets, Fixes, TimedNets), rebuilt
 * with the TS builder API as design candidates. Names, arcs, priorities and initial markings follow
 * the Java originals one to one, so the sensors can be checked against results/*.jsonl.
 */
import {
  and,
  andPlaces,
  delayed,
  exactly,
  matchKey,
  matchSpec,
  nameId,
  one,
  outPlace,
  PetriNet,
  place,
  SubnetDef,
  Transition,
  window,
  type Place,
} from 'libpetri';
import type { Candidate, Contract } from '../src/types.js';

export interface Fixture {
  readonly contract: Contract;
  readonly candidate: Candidate;
  /** ν budget places (verifier option in the lab, not structure). */
  readonly budgets?: readonly string[];
  /** ν carrier places (verifier option in the lab: EXTENDED fragment mode). */
  readonly carriers?: readonly string[];
}

type Built = { net: PetriNet; marking: Map<string, number> };
const p = (n: string): Place<unknown> => place(n);
const T = (n: string) => Transition.builder(n);

function fixture(
  name: string, rationale: string, build: (k: number) => Built,
  opts: { sinks?: string[]; sources?: string[]; budgets?: string[]; carriers?: string[] } = {},
): Fixture {
  return {
    contract: { name, intent: rationale, properties: [{ name: 'dlf', spec: { kind: 'deadlockFree' } }], sinks: opts.sinks ?? [], sources: opts.sources ?? [] },
    candidate: { name, rationale, build },
    budgets: opts.budgets,
    carriers: opts.carriers,
  };
}

// ---- Families.cancelReset / cancelDrains ---------------------------------------------------------

export function cancelReset(k: number): Built {
  const start = p('START'), cancel = p('CANCEL'), done = p('DONE'), aborted = p('ABORTED');
  const forks = [...Array(k)].map((_, i) => p(`B_${i}`));
  const joins = [...Array(k)].map((_, i) => p(`C_${i}`));
  const b = PetriNet.builder(`cancel-reset-${k}`);
  b.transition(T('fork').inputs(one(start)).inhibitor(aborted).outputs(andPlaces(...forks)).build());
  for (let i = 0; i < k; i++) b.transition(T(`work_${i}`).inputs(one(forks[i])).outputs(outPlace(joins[i])).build());
  b.transition(T('join').inputs(...joins.map(j => one(j))).outputs(outPlace(done)).build());
  b.transition(T('abort').inputs(one(cancel)).inhibitor(done).outputs(outPlace(aborted)).resets(start, ...forks, ...joins).build());
  return { net: b.build(), marking: new Map([['START', 1], ['CANCEL', 1]]) };
}

export function cancelDrains(k: number): Built {
  const start = p('START'), cancel = p('CANCEL'), cancelling = p('CANCELLING'), done = p('DONE'), aborted = p('ABORTED');
  const forks = [...Array(k)].map((_, i) => p(`B_${i}`));
  const joins = [...Array(k)].map((_, i) => p(`C_${i}`));
  const b = PetriNet.builder(`cancel-drains-${k}`);
  b.transition(T('fork').inputs(one(start)).inhibitors(cancelling, aborted).outputs(andPlaces(...forks)).build());
  for (let i = 0; i < k; i++) b.transition(T(`work_${i}`).inputs(one(forks[i])).inhibitor(cancelling).outputs(outPlace(joins[i])).build());
  b.transition(T('join').inputs(...joins.map(j => one(j))).inhibitor(cancelling).outputs(outPlace(done)).build());
  b.transition(T('begin_cancel').inputs(one(cancel)).inhibitor(done).outputs(outPlace(cancelling)).build());
  const all = [start, ...forks, ...joins];
  for (const q of all) b.transition(T(`drain_${q.name}`).inputs(one(q)).read(cancelling).priority(5).build());
  b.transition(T('finish_cancel').inputs(one(cancelling)).inhibitors(...all).outputs(outPlace(aborted)).build());
  return { net: b.build(), marking: new Map([['START', 1], ['CANCEL', 1]]) };
}

// ---- Subnets.session (local / hub) ---------------------------------------------------------------

function stage(local: boolean): SubnetDef<void> {
  const inP = p('IN'), busy = p('BUSY'), out = p('OUT'), cancelled = p('CANCELLED');
  const start = T('start').inputs(one(inP)).outputs(outPlace(busy));
  const finish = T('finish').inputs(one(busy)).outputs(outPlace(out));
  const b = SubnetDef.builder('Stage').place(inP).place(busy).place(out);
  if (local) {
    start.inhibitor(cancelled); finish.inhibitor(cancelled);
    b.place(cancelled).inputPort('cancelled', cancelled);
    b.transition(T('cleanup').read(cancelled).inputs(one(busy)).build())
      .transition(T('cleanup_in').read(cancelled).inputs(one(inP)).build());
  }
  return b.transition(start.build()).transition(finish.build()).inputPort('in', inP).outputPort('out', out).build();
}

export function session(stages: number, local: boolean): Built {
  const utter = p('UTTER'), turn = p('TURN'), barge = p('BARGE'), aborted = p('ABORTED');
  const cancelled = p('CANCELLED'), spoken = p('SPOKEN');
  const b = PetriNet.builder(`session-${local ? 'local' : 'hub'}-${stages}`);
  b.transition(T('start_turn').inputs(one(utter)).outputs(outPlace(turn)).build());
  let prev: Place<unknown> = turn;
  const internals: Place<unknown>[] = [];
  for (let s = 0; s < stages; s++) {
    const name = `st${s}`;
    const next = s === stages - 1 ? spoken : p(`H${s}`);
    const ports: Record<string, Place<unknown>> = { in: prev, out: next };
    if (local) ports.cancelled = cancelled;
    b.compose(stage(local).instantiate(name), ports);
    internals.push(p(`${name}/BUSY`));
    if (s > 0) internals.push(prev);
    prev = next;
  }
  const bargein = T('barge_in').inputs(one(barge)).inhibitor(spoken);
  if (local) bargein.outputs(andPlaces(aborted, cancelled));
  else bargein.outputs(outPlace(aborted)).resets(turn, ...internals);
  b.transition(bargein.build());
  return { net: b.build(), marking: new Map([['UTTER', 1], ['BARGE', 1]]) };
}

// ---- EnvNets.turns (consume / reset) -------------------------------------------------------------

/**
 * EnvNets.EVENTS defaults to 3 and JOURNAL r6 says "3 events", but the class counts in r6.jsonl /
 * r9.jsonl (9, 11, 12, 15, …) are those of 2 events (3 events gives 16 at s = 1, consume). The
 * recorded runs used -Devents=2, so the default here is 2 to match the data.
 */
export const EVENTS = 2;

export function turns(stages: number, mode: 'consume' | 'reset' | 'resetInbox', events = EVENTS): Built {
  const src = p('SOURCE'), inbox = p('INBOX'), tp = p('TURN_PERMIT'), outcome = p('OUTCOME');
  const st = [...Array(stages)].map((_, j) => p(`S_${j}`));
  const b = PetriNet.builder(`turns-${mode}-${stages}`);
  b.transition(T('arrive').inputs(one(src)).outputs(outPlace(inbox)).build());
  b.transition(T('start').inputs(one(inbox), one(tp)).outputs(outPlace(st[0])).build());
  for (let j = 0; j + 1 < stages; j++) b.transition(T(`step_${j}`).inputs(one(st[j])).outputs(outPlace(st[j + 1])).build());
  b.transition(T('finish').inputs(one(st[stages - 1])).outputs(andPlaces(outcome, tp)).build());
  if (mode === 'consume') {
    for (let j = 0; j < stages; j++)
      b.transition(T(`barge_${j}`).inputs(one(inbox), one(st[j])).outputs(andPlaces(st[0], outcome)).build());
  } else {
    const barge = T('barge').inputs(one(inbox)).inhibitor(tp).outputs(outPlace(st[0])).resets(...st);
    if (mode === 'resetInbox') barge.reset(inbox);
    b.transition(barge.build());
  }
  return { net: b.build(), marking: new Map([['SOURCE', events], ['TURN_PERMIT', 1]]) };
}

// ---- Fixes (§15 human-labelled pairs) ------------------------------------------------------------

export function resetToConsume(k: number, fixed: boolean): Built {
  const idle = p('IDLE'), active = p('ACTIVE'), latch = p('LATCH');
  const b = PetriNet.builder(`resetToConsume-${fixed ? 'after' : 'before'}`);
  b.transition(T('start').inputs(one(idle)).outputs(andPlaces(active, latch)).build());
  const stop = T('stop').inputs(one(active)).outputs(outPlace(idle));
  if (fixed) stop.inputs(one(latch)); else stop.reset(latch);
  b.transition(stop.build());
  return { net: b.build(), marking: new Map([['IDLE', k]]) };
}

export function conflictPair(k: number, fixed: boolean): Built {
  const trig = p('TRIGGER'), latch = p('LATCH'), seen = p('SEEN');
  const b = PetriNet.builder(`conflictPair-${fixed ? 'after' : 'before'}`);
  if (fixed) {
    b.transition(T('set_empty').inputs(one(trig)).inhibitor(latch).outputs(andPlaces(latch, seen)).build());
    b.transition(T('set_occupied').inputs(one(trig), one(latch)).outputs(andPlaces(latch, seen)).build());
  } else {
    b.transition(T('set').inputs(one(trig)).reset(latch).outputs(andPlaces(latch, seen)).build());
  }
  b.transition(T('clear').inputs(exactly(k, seen), one(latch)).build());
  return { net: b.build(), marking: new Map([['TRIGGER', k]]) };
}

export function readCanceller(k: number, fixed: boolean): Built {
  const req = p('REQ'), work = p('WORK'), done = p('DONE'), cancel = p('CANCEL'), cancelled = p('CANCELLED'), closed = p('CLOSED');
  const b = PetriNet.builder(`readCanceller-${fixed ? 'after' : 'before'}`);
  b.transition(T('start').inputs(one(req)).outputs(outPlace(work)).build());
  const finish = T('finish').inputs(one(work)).outputs(outPlace(done));
  if (fixed) {
    finish.inhibitor(cancel);
    b.transition(T('cancel_one').read(cancel).inputs(one(work)).outputs(outPlace(cancelled)).build());
    b.transition(T('close').inputs(one(cancel)).inhibitors(work, req).outputs(outPlace(closed)).build());
    b.transition(T('cancel_req').read(cancel).inputs(one(req)).outputs(outPlace(cancelled)).build());
  } else {
    b.transition(T('cancel_all').inputs(one(cancel)).resets(work, req).outputs(outPlace(closed)).build());
  }
  b.transition(finish.build());
  return { net: b.build(), marking: new Map([['REQ', k], ['CANCEL', 1]]) };
}

export function keptLatch(k: number): Built {
  const idle = p('IDLE'), busy = p('BUSY'), dirty = p('DIRTY');
  const b = PetriNet.builder('keptLatch');
  b.transition(T('work').inputs(one(idle)).inhibitor(dirty).outputs(andPlaces(busy, dirty)).build());
  b.transition(T('done').inputs(one(busy)).reset(dirty).outputs(outPlace(idle)).build());
  return { net: b.build(), marking: new Map([['IDLE', k]]) };
}

// ---- Families.gatherNu / gatherSlots (REQUESTS = 3, BRANCHES = 2 as in results/r3.jsonl) -------

export const REQUESTS = 3;
export const BRANCHES = 2;

export function gatherNu(k: number, n = BRANCHES): Built {
  const src = p('SOURCE'), budget = p('BUDGET'), pending = p('PENDING'), merged = p('MERGED');
  const br = [...Array(n)].map((_, i) => p(`BRANCH_${i}`));
  const dn = [...Array(n)].map((_, i) => p(`DONE_${i}`));
  const b = PetriNet.builder(`gather-nu-${k}`);
  b.transition(T('fork').inputs(one(src), one(budget)).outputs(andPlaces(...br, pending)).build());
  for (let i = 0; i < n; i++) b.transition(T(`work_${i}`).inputs(one(br[i])).outputs(outPlace(dn[i])).build());
  const ms = matchSpec(...dn.map(d => matchKey(d, (o: unknown) => nameId(String(o)))));
  b.transition(T('join').inputs(...dn.map(d => one(d)), one(pending)).match(ms).outputs(andPlaces(merged, budget)).build());
  return { net: b.build(), marking: new Map([['SOURCE', REQUESTS], ['BUDGET', k]]) };
}

export function gatherSlots(k: number, n = BRANCHES): Built {
  const src = p('SOURCE'), merged = p('MERGED');
  const b = PetriNet.builder(`gather-slots-${k}`);
  const marking = new Map([['SOURCE', REQUESTS]]);
  for (let j = 0; j < k; j++) {
    const slot = p(`SLOT_${j}`);
    const br = [...Array(n)].map((_, i) => p(`S${j}_BRANCH_${i}`));
    const dn = [...Array(n)].map((_, i) => p(`S${j}_DONE_${i}`));
    b.transition(T(`fork_${j}`).inputs(one(src), one(slot)).outputs(andPlaces(...br)).build());
    for (let i = 0; i < n; i++) b.transition(T(`work_${j}_${i}`).inputs(one(br[i])).outputs(outPlace(dn[i])).build());
    b.transition(T(`join_${j}`).inputs(...dn.map(d => one(d))).outputs(andPlaces(merged, slot)).build());
    marking.set(`SLOT_${j}`, 1);
  }
  return { net: b.build(), marking };
}

// ---- TimedNets.watchdogs (timing variant) --------------------------------------------------------

export function watchdogs(n: number): Built {
  const b = PetriNet.builder(`watchdog-timing-${n}`);
  const marking = new Map<string, number>();
  for (let i = 0; i < n; i++) {
    const req = p(`REQ_${i}`), calling = p(`CALLING_${i}`), resp = p(`RESP_${i}`), to = p(`TIMEOUT_${i}`);
    b.transition(T(`start_${i}`).inputs(one(req)).outputs(outPlace(calling)).build());
    b.transition(T(`answer_${i}`).timing(window(0, 2)).inputs(one(calling)).outputs(outPlace(resp)).build());
    b.transition(T(`watchdog_${i}`).timing(delayed(5)).inputs(one(calling)).outputs(outPlace(to)).build());
    marking.set(`REQ_${i}`, 1);
  }
  return { net: b.build(), marking };
}

// ---- Candidates ----------------------------------------------------------------------------------

export const FIXTURES = {
  cancelReset: fixture('cancelReset', 'one abort transition resets every in-flight place', cancelReset, { sinks: ['DONE', 'ABORTED', 'CANCEL'] }),
  cancelDrains: fixture('cancelDrains', 'generated drain fan-out behind a CANCELLING marker', cancelDrains, { sinks: ['DONE', 'ABORTED', 'CANCEL'] }),
  sessionLocal: fixture('sessionLocal', 'each stage cleans itself up behind a CANCELLED port', k => session(k, true), { sinks: ['SPOKEN', 'ABORTED', 'CANCELLED', 'BARGE'] }),
  sessionHub: fixture('sessionHub', 'barge-in resets every stage internal place', k => session(k, false), { sinks: ['SPOKEN', 'ABORTED', 'CANCELLED', 'BARGE'] }),
  turnsConsume: fixture('turnsConsume', 'per-stage barge transitions consume the running turn', k => turns(k, 'consume'), { sinks: ['OUTCOME', 'TURN_PERMIT'], sources: ['SOURCE'] }),
  turnsReset: fixture('turnsReset', 'one barge transition resets every stage', k => turns(k, 'reset'), { sinks: ['OUTCOME', 'TURN_PERMIT'], sources: ['SOURCE'] }),
  resetToConsumeBefore: fixture('resetToConsumeBefore', 'stop resets the latch', k => resetToConsume(k, false)),
  resetToConsumeAfter: fixture('resetToConsumeAfter', 'stop consumes the latch', k => resetToConsume(k, true)),
  conflictPairBefore: fixture('conflictPairBefore', 'reset-and-reseed latch', k => conflictPair(k, false)),
  conflictPairAfter: fixture('conflictPairAfter', 'empty-cell / occupied-cell conflict pair', k => conflictPair(k, true)),
  readCancellerBefore: fixture('readCancellerBefore', 'cancel resets in-flight work', k => readCanceller(k, false), { sinks: ['DONE', 'CANCELLED', 'CLOSED'] }),
  readCancellerAfter: fixture('readCancellerAfter', 'read-gated consume-only canceller plus closer', k => readCanceller(k, true), { sinks: ['DONE', 'CANCELLED', 'CLOSED'] }),
  keptLatch: fixture('keptLatch', 'bounded latch that stayed a reset', keptLatch),
  gatherNu: fixture('gatherNu', 'ν join with a budget place', k => gatherNu(k), { sinks: ['MERGED', 'BUDGET'], sources: ['SOURCE'], budgets: ['BUDGET'], carriers: ['BRANCH_0', 'BRANCH_1'] }),
  gatherSlots: fixture('gatherSlots', 'k hand-cloned slots', k => gatherSlots(k), { sinks: ['MERGED', 'SLOT_0', 'SLOT_1'], sources: ['SOURCE'] }),
  watchdogs: fixture('watchdogs', 'n calls each raced by a delayed watchdog', watchdogs, { sinks: [] }),
  envTurnsConsume: fixture('envTurnsConsume', 'env inbox, per-stage consuming barge', k => envTurns(k, 'consume'), { sinks: ['OUTCOME', 'TURN_PERMIT', 'INBOX'], sources: ['INBOX'] }),
  envTurnsReset: fixture('envTurnsReset', 'env inbox, one resetting barge', k => envTurns(k, 'reset'), { sinks: ['OUTCOME', 'TURN_PERMIT', 'INBOX'], sources: ['INBOX'] }),
  envTurnsIdle: fixture('envTurnsIdle', 'env inbox, consume plus idle inhibitor on the inbox', k => envTurns(k, 'idleInhib'), { sinks: ['OUTCOME', 'TURN_PERMIT', 'INBOX', 'IDLE'], sources: ['INBOX'] }),
} as const;

/** EnvNets.envTurns: INBOX is an environment place (no generator, empty initially). */
export function envTurns(stages: number, mode: 'consume' | 'reset' | 'idleInhib'): Built {
  const inbox = p('INBOX'), tp = p('TURN_PERMIT'), outcome = p('OUTCOME'), idle = p('IDLE');
  const st = [...Array(stages)].map((_, j) => p(`S_${j}`));
  const b = PetriNet.builder(`env-turns-${mode}-${stages}`);
  b.transition(T('start').inputs(one(inbox), one(tp)).outputs(outPlace(st[0])).build());
  for (let j = 0; j + 1 < stages; j++) b.transition(T(`step_${j}`).inputs(one(st[j])).outputs(outPlace(st[j + 1])).build());
  b.transition(T('finish').inputs(one(st[stages - 1])).outputs(andPlaces(outcome, tp)).build());
  if (mode === 'reset') {
    b.transition(T('barge').inputs(one(inbox)).inhibitor(tp).outputs(outPlace(st[0])).resets(...st).build());
  } else {
    for (let j = 0; j < stages; j++)
      b.transition(T(`barge_${j}`).inputs(one(inbox), one(st[j])).outputs(and(outPlace(st[0]), outPlace(outcome))).build());
    if (mode === 'idleInhib') {
      b.transition(T('go_idle').inputs(one(tp)).inhibitor(inbox).outputs(outPlace(idle)).build());
      b.transition(T('wake').inputs(one(idle), one(inbox)).outputs(outPlace(st[0])).build());
    }
  }
  return { net: b.build(), marking: new Map([['TURN_PERMIT', 1]]) };
}
