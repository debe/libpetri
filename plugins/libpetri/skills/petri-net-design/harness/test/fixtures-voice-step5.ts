/**
 * Voice-agent step 5 fixture for the units-rule tests: a copy of research/net-metrics/loop/voice-B1
 * step5-minimal (sessionDef of step5-variants with sequential search, one call at a time, no tool
 * loop) and the step-5 contract (loop/contracts/voice/step5.ts). One SubnetDef instance per session
 * (S1, S2, …) sharing only the backend permits IDLE_SEARCH (2) and obs/SEARCH.
 *
 * One change from the research copy: StartSpeaking takes and returns obs/TURN instead of reading
 * it. The copy is violated at k = 1 once firings are not atomic (VER-004): BargeIn fires while
 * StartSpeaking's action runs and the speech it then deposits is stranded.
 */
import {
  PetriNet, SubnetDef, Transition, and, exactly, one, outPlace, place, timeout, xor,
  type In, type Out, type Place,
} from 'libpetri';
import type { Candidate, Contract } from '../src/types.js';

const cache = new Map<string, Place<unknown>>();
const P = (name: string): Place<unknown> => { let p = cache.get(name); if (!p) { p = place<unknown>(name); cache.set(name, p); } return p; };
const O = (n: string): Out => outPlace(P(n));
const AND = (...xs: Array<Out | string>): Out => and(...xs.map(x => (typeof x === 'string' ? O(x) : x)));
const XOR = (...xs: Array<Out | string | string[]>): Out =>
  xor(...xs.map(x => (typeof x === 'string' ? O(x) : Array.isArray(x) ? AND(...x) : x)));
interface TSpec { in?: Array<string | [string, number]>; out?: Out | string | string[]; read?: string[]; inh?: string[] }
function T(name: string, s: TSpec): Transition {
  const b = Transition.builder(name);
  const ins: In[] = (s.in ?? []).map(x => (typeof x === 'string' ? one(P(x)) : exactly(x[1], P(x[0]))));
  if (ins.length) b.inputs(...ins);
  if (s.out !== undefined) b.outputs(typeof s.out === 'string' ? O(s.out) : Array.isArray(s.out) ? AND(...s.out) : s.out);
  for (const r of s.read ?? []) b.read(P(r));
  for (const r of s.inh ?? []) b.inhibitor(P(r));
  return b.build();
}

function sequentialRound(): Transition[] {
  const chain = ['F', 'C', 'X', 'B'];
  const out: Transition[] = [T('StartRound', { in: ['TOPIC'], out: 'Q_F' })];
  chain.forEach((s, i) => {
    const next = chain[i + 1];
    out.push(
      T(`Start_${s}`, { in: [`Q_${s}`, 'IDLE_SEARCH'], out: ['obs/SEARCH', `RUN_${s}`] }),
      T(`Done_${s}`, { in: [`RUN_${s}`, 'obs/SEARCH'], out: XOR(['IDLE_SEARCH', 'RESULTS'], ['IDLE_SEARCH', next ? `Q_${next}` : 'NO_RESULTS']) }),
      T(`Discard_Q_${s}`, { in: [`Q_${s}`, 'ABANDON'], out: 'A_DONE' }),
    );
  });
  return out;
}

function sessionDef() {
  const STAGES = ['INTENT_REQ', 'INTENT', 'TOPIC', 'RESULTS', 'NO_RESULTS', 'PLAN', 'DRAFT'];
  return SubnetDef.builder('session')
    .transitions(
      T('StartTurn', { in: ['UTTERANCE', 'IDLE'], inh: ['obs/CLOSED'], out: ['obs/TURN', 'CHECK_REQ', 'INTENT_REQ'] }),
      T('RefuseClosed', { in: ['UTTERANCE'], read: ['obs/CLOSED'], out: 'REFUSED' }),
      T('SafetyCheck', { in: ['CHECK_REQ'], out: XOR('SAFE', 'UNSAFE', 'SEVERE') }),
      T('DetectIntent', { in: ['INTENT_REQ'], out: 'INTENT' }),
      T('LoadTopic', { in: ['INTENT'], out: 'TOPIC' }),
      ...sequentialRound(),
      T('ComposeAnswer', { in: ['RESULTS'], out: 'PLAN' }),
      T('Plan', { in: ['PLAN'], out: XOR('DRAFT', ['GATHER', 'obs/CALL', 'AWAIT_1']) }),
      T('Await_1', { in: ['AWAIT_1'], out: xor(outPlace(P('GOT_1')), timeout(8000, outPlace(P('GOT_1')))) }),
      T('Collect_1', { in: ['GOT_1', 'obs/CALL'], out: 'S_DONE_1' }),
      T('Gather', { in: ['GATHER', 'S_DONE_1'], out: 'DRAFT' }),
      T('DiscardGather', { in: ['GATHER', 'S_DONE_1', 'ABANDON'], out: 'A_DONE' }),
      T('ComposeNothingFound', { in: ['NO_RESULTS'], out: 'DRAFT' }),
      // Takes obs/TURN and puts it back, where the research copy only read it: while its action is
      // in flight the turn is with it, so BargeIn (which inhibits on obs/SPEAKING, not yet marked)
      // cannot fire in between and strand the speech it deposits (VER-004, EXEC-003).
      T('StartSpeaking', { in: ['DRAFT', 'obs/TURN'], read: ['SAFE'], out: ['obs/SPEAKING', 'obs/TURN'] }),
      T('FinishSpeaking', { in: ['obs/SPEAKING', 'obs/TURN', 'SAFE'], out: ['ANSWERED', 'A_DONE', 'C_DONE'] }),
      T('Refuse', { in: ['obs/TURN', 'UNSAFE'], out: ['REFUSED', 'ABANDON', 'C_DONE'] }),
      T('CloseSession', { in: ['obs/TURN', 'SEVERE'], out: ['REFUSED', 'obs/CLOSED', 'ABANDON', 'C_DONE'] }),
      T('BargeIn', { in: ['obs/TURN'], read: ['UTTERANCE'], inh: ['obs/SPEAKING'], out: ['ABORTED', 'ABANDON', 'ABANDON_CHK'] }),
      T('BargeInSpeaking', { in: ['obs/TURN', 'obs/SPEAKING'], read: ['UTTERANCE'], out: ['ABORTED', 'A_DONE', 'ABANDON_CHK'] }),
      ...STAGES.map(s => T(`Discard_${s}`, { in: [s, 'ABANDON'], out: 'A_DONE' })),
      ...['CHECK_REQ', 'SAFE', 'UNSAFE'].map(s => T(`DiscardCheck_${s}`, { in: [s, 'ABANDON_CHK'], out: 'C_DONE' })),
      T('DiscardCheck_SEVERE', { in: ['SEVERE', 'ABANDON_CHK'], out: ['C_DONE', 'obs/CLOSED'] }),
      T('Release', { in: ['A_DONE', 'C_DONE'], out: 'IDLE' }),
    )
    .inputPort('UTTERANCE', P('UTTERANCE'))
    .inoutPort('BACKEND', P('IDLE_SEARCH'))
    .inoutPort('SEARCHING', P('obs/SEARCH'))
    .build();
}

export const voiceStep5Minimal: Candidate = {
  name: 'step5-minimal',
  rationale: 'voice-B1 step5-minimal: per-session SubnetDef, sequential search, one call at a time, no tool loop.',
  build(k: number) {
    const def = sessionDef();
    const b = PetriNet.builder('voice-step5-minimal');
    const marking = new Map<string, number>([['IDLE_SEARCH', 2]]);
    for (let i = 1; i <= k; i++) {
      b.compose(def.instantiate(`S${i}`), { BACKEND: P('IDLE_SEARCH'), SEARCHING: P('obs/SEARCH') });
      marking.set(`S${i}/IDLE`, 1);
    }
    return { net: b.build(), marking };
  },
};

export const voiceStep5Contract: Contract = {
  name: 'voice-agent/5-sessions',
  intent: 'k concurrent sessions, two utterances each, sharing a search backend of two permits.',
  sources: [],
  inputs: [{ place: '*/UTTERANCE', tokens: 2 }],
  sinks: ['*/ANSWERED', '*/REFUSED', '*/ABORTED', '*/obs/CLOSED', 'IDLE', 'IDLE_*', '*/IDLE', '*/IDLE_*'],
  scales: [1, 2],
  properties: [
    { name: 'R0 nothing is left stranded', spec: { kind: 'deadlockFree' } },
    { name: 'R0 every utterance of every session gets exactly one outcome', spec: { kind: 'accounting', outcomes: ['*/ANSWERED', '*/REFUSED', '*/ABORTED'] } },
    { name: 'R1 one turn at a time per session', spec: { kind: 'placeBound', place: '*/obs/TURN', bound: 1 } },
    { name: 'R17 at most two search requests at a time in total', spec: { kind: 'placeBound', place: 'obs/SEARCH', bound: 2 } },
    { name: 'R11 at most two calls awaiting replies per session', spec: { kind: 'placeBound', place: '*/obs/CALL', bound: 2 } },
    { name: 'R14 never speaking while a call awaits a reply (per session)', spec: { kind: 'mutualExclusion', a: '*/obs/SPEAKING', b: '*/obs/CALL' } },
    { name: 'R18 no turn in a closed session', spec: { kind: 'mutualExclusion', a: '*/obs/CLOSED', b: '*/obs/TURN' } },
  ],
};
