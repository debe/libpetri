/**
 * The net player (design 4.3 to 4.5): the pre-rendered diagram of a situation with tokens drawn
 * on its places, stepped through the Lean replay: first, back, play/pause, next, last and a
 * scrubber; a caption, a blocked callout, the steps list, the marking table and the Lean
 * verdict box.
 *
 * The markings, the blocked reason, its message and its requirement all come from the Lean
 * replay (`entry.result`); the player computes nothing the replay states. The one thing it
 * derives is which transitions are enabled in the shown marking (design 4.3, the green halo),
 * from the net's arcs and the CORE-022 / IO-001..004 rule.
 *
 * The exported SVG is never re-laid out or recoloured: the player only adds two layers inside
 * the Graphviz root group (`g.player__under` behind the nodes, `g.player__tokens` on top) and
 * reads geometry from the exported shapes' attributes, so it works on a detached SVG too.
 *
 * Owner: DOT/SVG + player agent. The pure parts (frames, reducer, captions, layouts) are
 * exported for the unit tests in `tests/player.test.ts`.
 */
import type {
  BlockReason,
  CorpusNet,
  Marking,
  NodeName,
  NotReplayed,
  OutputSpec,
  ReqId,
  SituationEntry,
} from '../model.js';
import type { AppContext } from './context.js';
import { cloneDiagram } from './data.js';
import { h, listen, prefersReducedMotion, replaceChildren, s } from './dom.js';
import { openHelp } from './help.js';
import { inline, plainText } from './md.js';
import { idLink } from './ui.js';

// =============================================================================================
// Public API
// =============================================================================================

export interface PlayerOptions {
  /** Step to show first: 0 = initial marking, k = after step k. Clamped. */
  readonly initialStep?: number;
  /** Called after the shown step changes (the situation view mirrors it in `?step=`). */
  readonly onStep?: (step: number) => void;
}

export interface PlayerHandle {
  readonly node: HTMLElement;
  /** The step shown now. */
  readonly step: () => number;
  /** Number of steps that can be shown after the initial marking. */
  readonly length: number;
  goTo(step: number): void;
  dispose(): void;
}

/**
 * The marking shown at `step`: 0 is the initial marking (the replay's `initial`, or the net's
 * own marking without a replay); k is the marking after step k when step k fired; null when
 * step k is out of range or blocked.
 */
export function markingAt(entry: SituationEntry, step: number): Marking | null {
  if (step === 0) return entry.result?.initial ?? entry.net.marking;
  const s = entry.result?.steps[step - 1];
  return s !== undefined && s.kind === 'fired' ? s.marking : null;
}

// =============================================================================================
// Diagram palette (spec/petri-net-styles.json "animation"; a unit test checks the values).
// The canvas is always paper white, so these stay literal in both themes (design 2.4).
// =============================================================================================

export const ANIMATION_COLOURS = {
  tokenDot: '#007bff',
  enabledGlow: '#28a745',
  inFlightGlow: '#ffc107',
  firingFlash: '#dc3545',
} as const;

/** Ink of the firing outline and the token count (design 4.3), the light `--text`. */
const INK = '#1f2328';
/** Blocked outline and cause rings, the light `--bad`. */
const BLOCKED = '#c4202b';
/** Ring of a place that changed in this step, the light `--accent`. */
const CHANGED = '#4338ca';

/** Autoplay: time per step with motion, and the longer dwell under reduced motion. */
export const AUTOPLAY_MS = 900;
export const AUTOPLAY_REDUCED_MS = 2000;
/** Animation phases of a firing step, in milliseconds (design 4.3; total at most 600). */
const FLASH_END = 160;
const CONSUME = [80, 380] as const;
const PRODUCE = [300, 600] as const;
const ANIMATION_MS = 600;
/** Token dot radius in points (design 4.3). */
const DOT_R = 3;

// =============================================================================================
// Frames: what each player step shows (pure)
// =============================================================================================

/** One place's token count before and after a step. */
export interface PlaceDelta {
  readonly place: NodeName;
  readonly before: number;
  readonly after: number;
}

export interface BlockedInfo {
  readonly reason: BlockReason;
  readonly requirement: ReqId;
  readonly message: string;
}

/** What the player shows at one step. Step 0 is the initial marking. */
export interface Frame {
  readonly step: number;
  readonly kind: 'initial' | 'fired' | 'blocked';
  /** The marking drawn: after the step when it fired, unchanged when it is blocked. */
  readonly marking: Marking;
  /** The marking before the step (equal to `marking` at step 0). */
  readonly before: Marking;
  readonly fire: NodeName | null;
  readonly branch: number;
  readonly timeout: boolean;
  /** The authored caption of the step, or null. */
  readonly text: string | null;
  /** Places whose count changed, in place order. */
  readonly delta: readonly PlaceDelta[];
  readonly blocked: BlockedInfo | null;
}

const count = (m: Marking, place: NodeName): number => m[place] ?? 0;

/**
 * Every place the situation names, in a stable order: declared places first (file order), then
 * places only arcs or markings name, sorted.
 */
export function placeOrder(entry: SituationEntry): readonly NodeName[] {
  const seen = new Set<NodeName>(entry.net.places);
  const extra = new Set<NodeName>();
  const note = (p: NodeName): void => {
    if (!seen.has(p)) extra.add(p);
  };
  const walkOut = (o: OutputSpec): void => {
    switch (o.type) {
      case 'place':
        note(o.place);
        return;
      case 'and':
      case 'xor':
        o.children.forEach(walkOut);
        return;
      case 'timeout':
        walkOut(o.child);
        return;
      case 'forward':
        note(o.from);
        note(o.to);
        return;
    }
  };
  for (const t of entry.net.transitions) {
    t.inputs.forEach((a) => note(a.place));
    t.inhibitors.forEach(note);
    t.reads.forEach(note);
    t.resets.forEach(note);
    if (t.output !== null) walkOut(t.output);
  }
  const markings: Marking[] = [entry.net.marking];
  if (entry.result !== null) {
    markings.push(entry.result.initial);
    for (const step of entry.result.steps) if (step.kind === 'fired') markings.push(step.marking);
  }
  for (const m of markings) Object.keys(m).forEach(note);
  return [...entry.net.places, ...[...extra].sort()];
}

/** Places whose count differs between two markings, in `order`. */
export function markingDelta(before: Marking, after: Marking, order: readonly NodeName[]): readonly PlaceDelta[] {
  const out: PlaceDelta[] = [];
  for (const place of order) {
    const b = count(before, place);
    const a = count(after, place);
    if (a !== b) out.push({ place, before: b, after: a });
  }
  return out;
}

/** The frames of the player: index k is step k; length is 1 + replayed steps. */
export function playerFrames(entry: SituationEntry): readonly Frame[] {
  const order = placeOrder(entry);
  const initial = entry.result?.initial ?? entry.net.marking;
  const frames: Frame[] = [
    { step: 0, kind: 'initial', marking: initial, before: initial, fire: null, branch: 0, timeout: false, text: null, delta: [], blocked: null },
  ];
  if (entry.result === null) return frames;
  let current = initial;
  entry.result.steps.forEach((step, i) => {
    const text = entry.steps[step.index]?.text ?? null;
    if (step.kind === 'fired') {
      frames.push({
        step: i + 1,
        kind: 'fired',
        marking: step.marking,
        before: current,
        fire: step.fire,
        branch: step.branch,
        timeout: step.timeout,
        text,
        delta: markingDelta(current, step.marking, order),
        blocked: null,
      });
      current = step.marking;
    } else {
      frames.push({
        step: i + 1,
        kind: 'blocked',
        marking: current,
        before: current,
        fire: step.fire,
        branch: step.branch,
        timeout: step.timeout,
        text,
        delta: [],
        blocked: { reason: step.reason, requirement: step.requirement, message: step.message },
      });
    }
  });
  return frames;
}

/** Sum of the tokens of a marking. */
export function tokenTotal(m: Marking): number {
  return Object.values(m).reduce((a, b) => a + b, 0);
}

const plural = (n: number, one: string, many: string): string => `${n} ${n === 1 ? one : many}`;

/**
 * Transitions enabled in `marking` (CORE-022): every input place holds the arc's required count
 * (IO-001..004: one 1, exactly n, all 1, atLeast n), no inhibitor place holds a token and every
 * read place does. Net order.
 */
export function enabledTransitions(net: CorpusNet, marking: Marking): readonly NodeName[] {
  return net.transitions
    .filter((t) =>
      t.inputs.every((a) => count(marking, a.place) >= (a.kind === 'exactly' || a.kind === 'atLeast' ? a.n : 1))
      && t.inhibitors.every((p) => count(marking, p) === 0)
      && t.reads.every((p) => count(marking, p) > 0))
    .map((t) => t.name);
}

/** True when the transition's output spec offers a choice of branches (an Xor). */
function hasChoice(o: OutputSpec | null): boolean {
  if (o === null) return false;
  switch (o.type) {
    case 'xor':
      return o.children.length > 1 || o.children.some(hasChoice);
    case 'and':
      return o.children.some(hasChoice);
    case 'timeout':
      return hasChoice(o.child);
    case 'place':
    case 'forward':
      return false;
  }
}

/** "take", "triage, branch 1" or "call, timeout": the transition and the outcome it chose. */
export function firingLabel(net: CorpusNet, frame: Pick<Frame, 'fire' | 'branch' | 'timeout'>): string {
  if (frame.fire === null) return '';
  if (frame.timeout) return `${frame.fire}, timeout`;
  const t = net.transitions.find((x) => x.name === frame.fire);
  return t !== undefined && hasChoice(t.output) ? `${frame.fire}, branch ${frame.branch}` : frame.fire;
}

const MINUS = '−';

/** "job −1 · lock +1" (design 4.3 steps list). */
export function deltaText(delta: readonly PlaceDelta[]): string {
  return delta
    .map((d) => {
      const diff = d.after - d.before;
      return `${d.place} ${diff < 0 ? `${MINUS}${-diff}` : `+${diff}`}`;
    })
    .join(' · ');
}

/** "job 3 · lock 1", or "No tokens". */
export function markingText(m: Marking, order: readonly NodeName[]): string {
  const parts = order.filter((p) => count(m, p) > 0).map((p) => `${p} ${count(m, p)}`);
  return parts.length === 0 ? 'No tokens' : parts.join(' · ');
}

/** Lean's message as a sentence: it ends with a full stop. */
export function sentence(text: string): string {
  const t = text.trim();
  return /[.!?]$/.test(t) ? t : `${t}.`;
}

/** Design 4.3 wording of a blocked reason; the fallback when the replay has no message. */
export function reasonSentence(fire: NodeName, reason: BlockReason): string {
  switch (reason.kind) {
    case 'unknownTransition':
      return `The net has no transition named ${fire}.`;
    case 'inputShort':
      return `${fire} is not enabled: input place ${reason.place} holds ${plural(reason.have, 'token', 'tokens')} and it needs ${reason.need}.`;
    case 'inhibitorMarked':
      return `${fire} is not enabled: inhibitor place ${reason.place} holds a token.`;
    case 'readEmpty':
      return `${fire} is not enabled: read place ${reason.place} is empty.`;
    case 'noSuchBranch':
      return reason.timeout ? `${fire} has no timeout outcome.` : `${fire} has no output branch ${reason.branch}.`;
  }
}

/** The text of a blocked step: Lean's message, else the design template. */
export function blockedText(frame: Frame): string {
  if (frame.blocked === null) return '';
  const message = frame.blocked.message.trim();
  return message === '' ? reasonSentence(frame.fire ?? '', frame.blocked.reason) : sentence(message);
}

/**
 * The visible caption under the controls: a bold lead ("take fires.") and the text (the
 * authored caption, else the marking change). The initial and blocked frames have no lead.
 */
export function captionParts(entry: SituationEntry, frame: Frame, order: readonly NodeName[]): { readonly lead: string | null; readonly text: string } {
  if (frame.kind === 'initial') {
    const tokens = tokenTotal(frame.marking);
    const places = order.filter((p) => count(frame.marking, p) > 0).length;
    return { lead: null, text: `Initial marking. ${plural(tokens, 'token', 'tokens')} in ${plural(places, 'place', 'places')}.` };
  }
  if (frame.kind === 'blocked') return { lead: null, text: blockedText(frame) };
  const delta = deltaText(frame.delta);
  const text = frame.text ?? (delta === '' ? 'The marking does not change.' : `${delta}.`);
  return { lead: `${firingLabel(entry.net, frame)} fires.`, text };
}

/** The caption as one line of plain text (authored captions may hold `code` spans). */
export function captionText(entry: SituationEntry, frame: Frame, order: readonly NodeName[]): string {
  const { lead, text } = captionParts(entry, frame, order);
  return lead === null ? plainText(text) : `${lead} ${plainText(text)}`;
}

/** What the live region says after a step change (design 10). */
export function announcement(entry: SituationEntry, frames: readonly Frame[], step: number): string {
  const frame = frames[step];
  if (frame === undefined) return '';
  const total = frames.length - 1;
  if (frame.kind === 'initial') return 'Back to the initial marking.';
  const head = `Step ${step} of ${total}: `;
  if (frame.kind === 'blocked') {
    const rule = frame.blocked === null ? '' : ` Rule ${frame.blocked.requirement}.`;
    return `${head}${frame.fire ?? ''} is blocked. ${blockedText(frame)}${rule}`;
  }
  const changes = frame.delta.map((d) => `${d.place} ${d.before} to ${d.after}`).join(', ');
  return `${head}${firingLabel(entry.net, frame)} fires.${changes === '' ? ' No marking changes.' : ` ${changes}.`}`;
}

/** The scrubber's `aria-valuetext` (design 4.3). */
export function scrubberText(entry: SituationEntry, frames: readonly Frame[], step: number): string {
  const frame = frames[step];
  const total = frames.length - 1;
  if (frame === undefined || frame.kind === 'initial') return `Step 0 of ${total}: initial marking`;
  const verb = frame.kind === 'blocked' ? 'blocked' : 'fire';
  return `Step ${step} of ${total}: ${verb} ${firingLabel(entry.net, frame)}`;
}

/** The `<desc>` of the SVG: the marking in words, every place with its count. */
export function markingDescription(frame: Frame, order: readonly NodeName[]): string {
  const counts = order.map((p) => `${p} ${count(frame.marking, p)}`).join(', ');
  const head = frame.step === 0 ? 'Initial marking' : frame.kind === 'blocked' ? `Marking at blocked step ${frame.step}` : `Marking after step ${frame.step}`;
  return `${head}: ${counts === '' ? 'no places' : counts}.`;
}

// =============================================================================================
// Lean verdict and not-replayed note (pure)
// =============================================================================================

export type Verdict =
  | { readonly kind: 'not-replayed'; readonly why: NotReplayed | null }
  | { readonly kind: 'expected-other'; readonly at: number }
  | { readonly kind: 'complete'; readonly fired: number }
  | { readonly kind: 'blocked'; readonly fired: number; readonly at: number }
  | { readonly kind: 'disagrees'; readonly at: number };

/**
 * How the Lean replay relates to the authored run. A replay that stops before the authored run
 * ends disagrees (the generator refuses it, so only the self-test sees this state).
 */
export function verdictOf(entry: SituationEntry): Verdict {
  const result = entry.result;
  if (!entry.replay || result === null) return { kind: 'not-replayed', why: entry.notReplayed };
  const blockedAt = result.steps.findIndex((s) => s.kind === 'blocked');
  // A blocked step must be the last replayed one (Lean stops there).
  if (blockedAt >= 0 && blockedAt !== result.steps.length - 1) return { kind: 'disagrees', at: blockedAt + 1 };
  // The replay must cover every authored step: stopping early (at a block) or running past
  // the authored run disagrees at the first step where the two differ.
  if (result.steps.length < entry.steps.length) {
    return { kind: 'disagrees', at: blockedAt >= 0 ? blockedAt + 1 : result.steps.length + 1 };
  }
  if (result.steps.length > entry.steps.length) return { kind: 'disagrees', at: entry.steps.length + 1 };
  // Every step must do what its author says it does (`expect`, default fired).
  const differs = result.steps.findIndex((s, i) => entry.steps[i]?.expect !== s.kind);
  if (differs >= 0) return { kind: 'expected-other', at: differs + 1 };
  if (blockedAt < 0) return { kind: 'complete', fired: result.steps.length };
  return { kind: 'blocked', fired: blockedAt, at: blockedAt + 1 };
}

const NOT_REPLAYED_PHRASE: { readonly [K in NotReplayed]: string } = {
  timed: 'is timed',
  environment: 'uses environment injection',
  'nu-net': 'is a ν-net',
  composition: 'shows composition',
  export: 'shows export',
  verification: 'shows verification',
};

/** Design 4.5 note for a situation Lean does not replay. */
export function notReplayedText(why: NotReplayed | null): string {
  const phrase = why === null ? 'is outside what the replay covers' : NOT_REPLAYED_PHRASE[why];
  return `Lean replays untimed runs only; this situation ${phrase}. Its rules show their Lean evidence below.`;
}

/** "Steps 1 to 5 fire. " / "Step 1 fires. " / "". */
export function firedPrefix(fired: number): string {
  if (fired <= 0) return '';
  return fired === 1 ? 'Step 1 fires. ' : `Steps 1 to ${fired} fire. `;
}

// =============================================================================================
// Step state reducer (pure)
// =============================================================================================

export interface PlayerState {
  /** The shown step, 0..length. */
  readonly step: number;
  /** Steps after the initial marking. */
  readonly length: number;
  readonly playing: boolean;
}

export type PlayerAction =
  | { readonly type: 'first' }
  | { readonly type: 'back' }
  | { readonly type: 'next' }
  | { readonly type: 'last' }
  | { readonly type: 'goto'; readonly step: number }
  | { readonly type: 'play' }
  | { readonly type: 'pause' }
  | { readonly type: 'toggle' }
  /** Autoplay timer: one step forward; stops at the end. */
  | { readonly type: 'tick' };

export function clampStep(step: number, length: number): number {
  if (!Number.isFinite(step)) return 0;
  return Math.max(0, Math.min(length, Math.trunc(step)));
}

export function initialState(length: number, step = 0): PlayerState {
  return { step: clampStep(step, length), length, playing: false };
}

/** True when the player is at its last step (Play becomes Replay). */
export function atEnd(state: PlayerState): boolean {
  return state.step >= state.length;
}

const withState = (state: PlayerState, step: number, playing: boolean): PlayerState =>
  state.step === step && state.playing === playing ? state : { ...state, step, playing };

/**
 * The player's state machine. Every user move stops autoplay; `play` at the end restarts from
 * the initial marking (Replay); `tick` advances while playing and stops at the last step (a
 * blocked step is always the last). Returns the same object when nothing changes.
 */
export function playerReducer(state: PlayerState, action: PlayerAction): PlayerState {
  switch (action.type) {
    case 'first':
      return withState(state, 0, false);
    case 'back':
      return withState(state, clampStep(state.step - 1, state.length), false);
    case 'next':
      return withState(state, clampStep(state.step + 1, state.length), false);
    case 'last':
      return withState(state, state.length, false);
    case 'goto':
      return withState(state, clampStep(action.step, state.length), false);
    case 'play':
      if (state.length === 0) return withState(state, state.step, false);
      return atEnd(state) ? withState(state, 0, true) : withState(state, state.step, true);
    case 'pause':
      return withState(state, state.step, false);
    case 'toggle':
      return playerReducer(state, { type: state.playing ? 'pause' : 'play' });
    case 'tick': {
      if (!state.playing) return state;
      const step = clampStep(state.step + 1, state.length);
      return withState(state, step, step < state.length);
    }
  }
}

// =============================================================================================
// Geometry and token layout (pure)
// =============================================================================================

export interface Box {
  readonly x: number;
  readonly y: number;
  readonly w: number;
  readonly h: number;
}

export interface Circle {
  readonly cx: number;
  readonly cy: number;
  /** Radius of the place circle (the inner one of a double circle). */
  readonly r: number;
  /** Radius of the outermost drawn circle. */
  readonly outer: number;
}

/** The bounding box of an SVG `points` list, or null when it holds no point. */
export function pointsBox(points: string): Box | null {
  const nums = points.trim().split(/[\s,]+/).map(Number);
  let minX = Infinity;
  let minY = Infinity;
  let maxX = -Infinity;
  let maxY = -Infinity;
  for (let i = 0; i + 1 < nums.length; i += 2) {
    const x = nums[i] ?? NaN;
    const y = nums[i + 1] ?? NaN;
    if (!Number.isFinite(x) || !Number.isFinite(y)) continue;
    minX = Math.min(minX, x);
    minY = Math.min(minY, y);
    maxX = Math.max(maxX, x);
    maxY = Math.max(maxY, y);
  }
  if (!Number.isFinite(minX)) return null;
  return { x: minX, y: minY, w: maxX - minX, h: maxY - minY };
}

export interface TokenLayout {
  /** Dot centres relative to the place centre, in points. */
  readonly dots: readonly { readonly dx: number; readonly dy: number }[];
  /** The count printed beside a single dot when there are five or more tokens. */
  readonly label: { readonly dx: number; readonly dy: number; readonly text: string } | null;
}

/** Design 4.3: 1 centre, 2 side by side, 3 triangle, 4 square, 5+ one dot and the count. */
export function tokenLayout(n: number): TokenLayout {
  const d = 4.5;
  switch (n) {
    case 0:
      return { dots: [], label: null };
    case 1:
      return { dots: [{ dx: 0, dy: 0 }], label: null };
    case 2:
      return { dots: [{ dx: -d, dy: 0 }, { dx: d, dy: 0 }], label: null };
    case 3:
      return { dots: [{ dx: 0, dy: -d }, { dx: -d, dy: 3.2 }, { dx: d, dy: 3.2 }], label: null };
    case 4:
      return { dots: [{ dx: -4, dy: -4 }, { dx: 4, dy: -4 }, { dx: -4, dy: 4 }, { dx: 4, dy: 4 }], label: null };
    default:
      return { dots: [{ dx: -5, dy: 0 }], label: { dx: 3.5, dy: 3.5, text: String(n) } };
  }
}

/** Standard easing (design 2.3 `--ease` is close to this ease-out curve). */
export function ease(t: number): number {
  const x = Math.max(0, Math.min(1, t));
  return 1 - (1 - x) ** 3;
}

/** Progress 0..1 of a phase [start, end] at time `t`. */
export function phase(t: number, start: number, end: number): number {
  return Math.max(0, Math.min(1, (t - start) / (end - start)));
}

// =============================================================================================
// SVG access
// =============================================================================================

interface Diagram {
  readonly svg: SVGSVGElement;
  /** Graphviz root group: the coordinate system of every shape. */
  readonly root: SVGGElement;
  readonly under: SVGGElement;
  readonly top: SVGGElement;
  readonly desc: SVGDescElement;
  readonly places: ReadonlyMap<NodeName, Circle>;
  readonly boxes: ReadonlyMap<NodeName, Box>;
}

const num = (el: Element, attr: string): number => Number.parseFloat(el.getAttribute(attr) ?? '');

function nodeGroups(svg: SVGSVGElement, kind: 'place' | 'transition' | 'junction'): Element[] {
  return Array.from(svg.querySelectorAll(`g[data-kind="${kind}"]`));
}

/** Place circles and transition boxes by net name, read from the exported shapes. */
export function readGeometry(svg: SVGSVGElement): { places: Map<NodeName, Circle>; boxes: Map<NodeName, Box> } {
  const places = new Map<NodeName, Circle>();
  for (const g of nodeGroups(svg, 'place')) {
    const name = g.getAttribute('data-name');
    const ellipses = Array.from(g.querySelectorAll('ellipse'));
    const first = ellipses[0];
    if (name === null || first === undefined) continue;
    const r = num(first, 'rx');
    const outer = Math.max(r, ...ellipses.map((e) => num(e, 'rx')).filter(Number.isFinite));
    const circle: Circle = { cx: num(first, 'cx'), cy: num(first, 'cy'), r, outer };
    if (Number.isFinite(circle.cx) && Number.isFinite(circle.cy) && Number.isFinite(r)) places.set(name, circle);
  }
  const boxes = new Map<NodeName, Box>();
  for (const kind of ['transition', 'junction'] as const) {
    for (const g of nodeGroups(svg, kind)) {
      const name = g.getAttribute('data-name');
      const poly = g.querySelector('polygon');
      const box = poly === null ? null : pointsBox(poly.getAttribute('points') ?? '');
      if (name !== null && box !== null) boxes.set(name, box);
    }
  }
  return { places, boxes };
}

function prepareDiagram(svg: SVGSVGElement, title: string): Diagram | null {
  const root = svg.querySelector('g.graph');
  if (!(root instanceof SVGGElement)) return null;
  svg.setAttribute('role', 'img');
  svg.setAttribute('tabindex', '0');
  svg.setAttribute('focusable', 'true');
  svg.classList.add('player__svg');
  const desc = s('desc');
  svg.prepend(s('title', null, title), desc);
  // Natural width in CSS pixels, so "Fit" never blows a small net up past 1.5 times.
  const width = Number.parseFloat(svg.getAttribute('width') ?? '');
  if (Number.isFinite(width)) svg.style.setProperty('--player-natural', `${Math.round(width * (4 / 3))}px`);
  // Natural height too: fitting never shrinks a tall net below its natural size (the canvas scrolls).
  const height = Number.parseFloat(svg.getAttribute('height') ?? '');
  if (Number.isFinite(height)) svg.style.setProperty('--player-natural-h', `${Math.round(height * (4 / 3))}px`);
  const under = s('g', { class: 'player__under', 'aria-hidden': 'true' });
  const firstShape = Array.from(root.children).find((c) => c instanceof SVGGElement);
  root.insertBefore(under, firstShape ?? null);
  const top = s('g', { class: 'player__tokens', 'aria-hidden': 'true' });
  root.append(top);
  const { places, boxes } = readGeometry(svg);
  return { svg, root, under, top, desc, places, boxes };
}

function edgePath(d: Diagram, from: string, to: string, arc?: string): SVGPathElement | null {
  const sel = `g[data-edge="${CSS.escape(`${from}->${to}`)}"]${arc === undefined ? '' : `[data-arc="${CSS.escape(arc)}"]`} path`;
  const el = d.svg.querySelector(sel);
  return el instanceof SVGPathElement ? el : null;
}

function nodeIdOf(d: Diagram, kind: 'place' | 'transition', name: NodeName): string | null {
  const el = d.svg.querySelector(`g[data-kind="${kind}"][data-name="${CSS.escape(name)}"]`);
  return el?.getAttribute('data-node') ?? null;
}

// =============================================================================================
// Painting a frame
// =============================================================================================

interface PaintOptions {
  /** Counts to draw instead of the frame's marking (during an animation). */
  readonly counts?: Marking;
  /** Places whose dots shrink (reset arcs) or pulse (read arcs) during an animation. */
  readonly shrink?: ReadonlySet<NodeName>;
  readonly pulse?: ReadonlySet<NodeName>;
  readonly flash?: boolean;
  readonly reduced: boolean;
}

function ring(c: Circle, colour: string, extra: number, cls: string): SVGCircleElement {
  return s('circle', { class: cls, cx: c.cx, cy: c.cy, r: c.outer + extra, fill: 'none', stroke: colour, 'stroke-width': 2 });
}

function halo(b: Box, colour: string, pad: number, width: number, cls: string, extra: Record<string, string | number> = {}): SVGRectElement {
  return s('rect', {
    class: cls,
    x: b.x - pad,
    y: b.y - pad,
    width: b.w + 2 * pad,
    height: b.h + 2 * pad,
    rx: 2,
    fill: 'none',
    stroke: colour,
    'stroke-width': width,
    ...extra,
  });
}

function drawTokens(parent: SVGGElement, c: Circle, n: number, cls: string): void {
  if (n <= 0) return;
  const layout = tokenLayout(n);
  const g = s('g', { class: cls, 'data-place-tokens': n });
  for (const dot of layout.dots) {
    g.append(s('circle', { cx: c.cx + dot.dx, cy: c.cy + dot.dy, r: DOT_R, fill: ANIMATION_COLOURS.tokenDot, stroke: '#ffffff', 'stroke-width': 0.75 }));
  }
  if (layout.label !== null) {
    g.append(s('text', {
      x: c.cx + layout.label.dx,
      y: c.cy + layout.label.dy,
      'font-family': 'Helvetica,Arial,sans-serif',
      'font-size': 10,
      'font-weight': 700,
      fill: INK,
    }, layout.label.text));
  }
  parent.append(g);
}

function paint(d: Diagram, entry: SituationEntry, frame: Frame, order: readonly NodeName[], o: PaintOptions): void {
  d.under.replaceChildren();
  d.top.replaceChildren();
  d.desc.textContent = markingDescription(frame, order);
  const counts = o.counts ?? frame.marking;

  // Enabled halos (design 4.3) for every enabled transition except the one this step is about.
  if (entry.result !== null) {
    for (const name of enabledTransitions(entry.net, frame.marking)) {
      const b = d.boxes.get(name);
      if (b !== undefined && name !== frame.fire) {
        d.under.append(halo(b, ANIMATION_COLOURS.enabledGlow, 2.5, 3, 'player__enabled', { 'stroke-opacity': 0.6 }));
      }
    }
  }

  const box = frame.fire === null ? undefined : d.boxes.get(frame.fire);
  if (frame.kind === 'fired' && box !== undefined) {
    d.under.append(halo(box, ANIMATION_COLOURS.inFlightGlow, 3, 3, 'player__firing-glow'));
    d.under.append(halo(box, o.flash ? ANIMATION_COLOURS.firingFlash : INK, 1, 2, o.flash ? 'player__firing player__firing--flash' : 'player__firing'));
  }

  if (frame.kind === 'blocked' && frame.blocked !== null) {
    if (box !== undefined) {
      d.under.append(halo(box, BLOCKED, 2.5, 2.5, 'player__blocked', { 'stroke-dasharray': '4 3' }));
    }
    const reason = frame.blocked.reason;
    const causePlace = reason.kind === 'inputShort' || reason.kind === 'inhibitorMarked' || reason.kind === 'readEmpty' ? reason.place : null;
    if (causePlace !== null) {
      const c = d.places.get(causePlace);
      if (c !== undefined) d.top.append(ring(c, BLOCKED, 3, 'player__cause'));
      const pid = nodeIdOf(d, 'place', causePlace);
      const tid = frame.fire === null ? null : nodeIdOf(d, 'transition', frame.fire);
      const arc = reason.kind === 'inhibitorMarked' ? 'inhibitor' : reason.kind === 'readEmpty' ? 'read' : null;
      const path = pid !== null && tid !== null && arc !== null ? edgePath(d, pid, tid, arc) : null;
      if (path !== null) {
        d.top.append(s('path', { class: 'player__cause-arc', d: path.getAttribute('d') ?? '', fill: 'none', stroke: BLOCKED, 'stroke-width': 2.5 }));
      }
    }
  }

  for (const delta of frame.delta) {
    const c = d.places.get(delta.place);
    if (c === undefined) continue;
    d.top.append(ring(c, CHANGED, 3, 'player__changed'));
    if (o.reduced) {
      const diff = delta.after - delta.before;
      d.top.append(s('text', {
        class: 'player__delta',
        x: c.cx + c.outer + 5,
        y: c.cy + 4,
        'font-family': 'Helvetica,Arial,sans-serif',
        'font-size': 10,
        'font-weight': 700,
        fill: CHANGED,
      }, diff < 0 ? `${MINUS}${-diff}` : `+${diff}`));
    }
  }

  for (const [name, c] of d.places) {
    const cls = o.shrink?.has(name) ? 'player__dots player__dots--shrink' : o.pulse?.has(name) ? 'player__dots player__dots--pulse' : 'player__dots';
    drawTokens(d.top, c, count(counts, name), cls);
  }

  // Blocked mark on top: a cross in a red circle at the box's top-right corner.
  if (frame.kind === 'blocked' && box !== undefined) {
    const x = box.x + box.w;
    const y = box.y;
    d.top.append(s('g', { class: 'player__blocked-mark' },
      s('circle', { cx: x, cy: y, r: 7, fill: BLOCKED, stroke: '#ffffff', 'stroke-width': 1 }),
      s('path', { d: `M${x - 3},${y - 3}L${x + 3},${y + 3}M${x + 3},${y - 3}L${x - 3},${y + 3}`, stroke: '#ffffff', 'stroke-width': 1.6, 'stroke-linecap': 'round' }),
    ));
  }
}

// =============================================================================================
// Animation of a firing step (design 4.3)
// =============================================================================================

interface Track {
  readonly paths: readonly SVGPathElement[];
  readonly lengths: readonly number[];
  readonly total: number;
  readonly window: readonly [number, number];
}

function track(paths: readonly SVGPathElement[], window: readonly [number, number]): Track | null {
  if (paths.length === 0) return null;
  try {
    const lengths = paths.map((p) => p.getTotalLength());
    const total = lengths.reduce((a, b) => a + b, 0);
    return total > 0 ? { paths, lengths, total, window } : null;
  } catch {
    return null;
  }
}

function pointOn(t: Track, u: number): DOMPoint | null {
  let distance = u * t.total;
  for (let i = 0; i < t.paths.length; i += 1) {
    const length = t.lengths[i] ?? 0;
    const path = t.paths[i];
    if (path === undefined) continue;
    if (distance <= length || i === t.paths.length - 1) return path.getPointAtLength(Math.min(distance, length));
    distance -= length;
  }
  return null;
}

/** Output edge paths from the transition (through its junctions) to `place`. */
function outputRoute(d: Diagram, tid: string, pid: string): SVGPathElement[] {
  const edges = Array.from(d.svg.querySelectorAll('g[data-arc="output"], g[data-arc="reset-output"]'));
  const step = (from: string, seen: Set<string>): SVGPathElement[] | null => {
    for (const g of edges) {
      const [tail, head] = (g.getAttribute('data-edge') ?? '').split('->');
      if (tail !== from || head === undefined || seen.has(head)) continue;
      const path = g.querySelector('path');
      if (!(path instanceof SVGPathElement)) continue;
      if (head === pid) return [path];
      if (head.startsWith('j_')) {
        const rest = step(head, new Set([...seen, head]));
        if (rest !== null) return [path, ...rest];
      }
    }
    return null;
  };
  return step(tid, new Set([tid])) ?? [];
}

/** Starts the animation of a fired frame; returns a cancel that jumps to the end. */
function animateFiring(d: Diagram, entry: SituationEntry, frame: Frame, order: readonly NodeName[], done: () => void): () => void {
  const finish = (): void => paint(d, entry, frame, order, { reduced: false });
  const transition = entry.net.transitions.find((t) => t.name === frame.fire);
  const tid = frame.fire === null ? null : nodeIdOf(d, 'transition', frame.fire);
  if (transition === undefined || tid === null || typeof requestAnimationFrame !== 'function') {
    finish();
    done();
    return () => {};
  }
  const inputs = new Set(transition.inputs.map((a) => a.place));
  const reads = new Set(transition.reads);
  const resets = new Set(transition.resets);
  const tracks: Track[] = [];
  const pending: Record<NodeName, number> = {};
  for (const delta of frame.delta) {
    const pid = nodeIdOf(d, 'place', delta.place);
    if (pid === null) continue;
    if (delta.after < delta.before && inputs.has(delta.place)) {
      const path = edgePath(d, pid, tid, 'input');
      const t = path === null ? null : track([path], CONSUME);
      if (t !== null) tracks.push(t);
    }
    if (delta.after > delta.before) {
      const t = track(outputRoute(d, tid, pid), PRODUCE);
      if (t !== null) tracks.push(t);
      pending[delta.place] = delta.before;
    }
  }
  // While tokens travel: consumed places already show their new count, produced ones the old.
  const counts: Record<NodeName, number> = { ...frame.marking, ...pending };
  const shrink = new Set([...resets].filter((p) => count(frame.before, p) > 0));
  for (const p of shrink) counts[p] = count(frame.before, p);
  paint(d, entry, frame, order, { counts, shrink, pulse: reads, flash: true, reduced: false });

  const travel = s('g', { class: 'player__travel' });
  const dots = tracks.map(() => s('circle', { r: DOT_R, fill: ANIMATION_COLOURS.tokenDot, stroke: '#ffffff', 'stroke-width': 0.75, opacity: 0 }));
  travel.append(...dots);
  d.top.append(travel);

  let raf = 0;
  let start = -1;
  let flashing = true;
  const tickFrame = (now: number): void => {
    if (start < 0) start = now;
    const t = now - start;
    if (flashing && t >= FLASH_END) {
      flashing = false;
      const outline = d.under.querySelector('.player__firing--flash');
      outline?.setAttribute('stroke', INK);
      outline?.setAttribute('class', 'player__firing');
    }
    tracks.forEach((tr, i) => {
      const dot = dots[i];
      if (dot === undefined) return;
      const u = phase(t, tr.window[0], tr.window[1]);
      const visible = t >= tr.window[0] && t < tr.window[1];
      dot.setAttribute('opacity', visible ? '1' : '0');
      if (!visible) return;
      const p = pointOn(tr, ease(u));
      if (p !== null) {
        dot.setAttribute('cx', String(p.x));
        dot.setAttribute('cy', String(p.y));
      }
    });
    if (t >= ANIMATION_MS) {
      raf = 0;
      finish();
      done();
      return;
    }
    raf = requestAnimationFrame(tickFrame);
  };
  raf = requestAnimationFrame(tickFrame);
  return () => {
    if (raf !== 0) {
      cancelAnimationFrame(raf);
      raf = 0;
      finish();
      done();
    }
  };
}

// =============================================================================================
// The player component
// =============================================================================================

// Step glyphs differ in shape from Play: a single chevron steps, a chevron with a bar jumps.
const GLYPH = { first: '|‹', back: '‹', play: '▶', pause: '❚❚', replay: '↻', next: '›', last: '›|' } as const;

function iconButton(label: string, glyph: string, cls: string, onClick: () => void): HTMLButtonElement {
  return h('button', {
    type: 'button',
    class: ['player__btn', cls],
    'aria-label': label,
    title: label,
    on: { click: onClick },
  }, h('span', { 'aria-hidden': 'true' }, glyph));
}

function setDisabled(button: HTMLButtonElement, disabled: boolean): void {
  if (disabled) button.setAttribute('aria-disabled', 'true');
  else button.removeAttribute('aria-disabled');
}

/** A safe id fragment for a slug (`[a-z0-9-]+` already; anything else becomes `-`). */
const idPart = (slug: string): string => slug.replace(/[^a-zA-Z0-9_-]/g, '-');

function verdictBox(ctx: AppContext, entry: SituationEntry, frames: readonly Frame[]): HTMLElement | null {
  const v = verdictOf(entry);
  if (v.kind === 'not-replayed') return null;
  const footer = h('p', { class: 'player__verdict-foot' }, 'Written by lean/Libpetri/Reference/Situation.lean. Never edited by hand.');
  const howLink = h('button', { type: 'button', class: 'player__link', on: { click: () => { openHelp(ctx, 'replays'); } } }, 'How replays work');
  if (v.kind === 'disagrees' || v.kind === 'expected-other') {
    return h('section', { class: ['player__verdict', 'player__verdict--bad'], 'aria-labelledby': `player-verdict-${idPart(entry.slug)}` },
      h('h2', { class: 'player__verdict-head', id: `player-verdict-${idPart(entry.slug)}` },
        h('span', { 'aria-hidden': 'true' }, '✗ '), `Lean replay disagrees at step ${v.at}`),
      h('p', null, v.kind === 'disagrees'
        ? 'The replay and the authored steps differ. CI fails on this; the self-test reports it.'
        : `The situation says step ${v.at} ${entry.steps[v.at - 1]?.expect === 'blocked' ? 'is blocked' : 'fires'}; the replay says otherwise. CI fails on this; the self-test reports it.`),
      footer,
    );
  }
  const untimed = entry.net.transitions.some((t) => t.priority !== 0)
    ? h('p', { class: 'player__verdict-note' },
        'The replay uses the untimed rule, where priorities play no part: it checks that each step may fire, not that the executor would choose it.')
    : null;
  let body: HTMLElement;
  if (v.kind === 'complete') {
    const all = v.fired === 1 ? 'the one step' : `all ${v.fired} steps`;
    body = h('p', null, `The Lean reference fired ${all} and reached this marking. `, howLink);
  } else {
    const blocked = frames[v.at];
    const info = blocked?.blocked ?? null;
    body = h('p', null,
      `${firedPrefix(v.fired)}Step ${v.at} is blocked, as the situation says: `,
      blocked === undefined ? '' : blockedText(blocked), ' ',
      info === null ? null : idLink(ctx, info.requirement), ' ',
      howLink,
    );
  }
  return h('section', { class: ['player__verdict', 'player__verdict--ok'], 'aria-labelledby': `player-verdict-${idPart(entry.slug)}` },
    h('h2', { class: 'player__verdict-head', id: `player-verdict-${idPart(entry.slug)}` },
      h('span', { 'aria-hidden': 'true' }, '✓ '), 'Lean replay agrees'),
    body,
    untimed,
    footer,
  );
}

function verbBadge(kind: 'initial' | 'fired' | 'blocked' | 'illustration'): HTMLElement {
  switch (kind) {
    case 'initial':
      return h('span', { class: ['badge', 'badge--none', 'player__verb'] }, 'start');
    case 'fired':
      return h('span', { class: ['badge', 'badge--ok', 'player__verb'] }, h('span', { 'aria-hidden': 'true' }, '✓ '), 'fires');
    case 'blocked':
      return h('span', { class: ['badge', 'badge--bad', 'player__verb'] }, h('span', { 'aria-hidden': 'true' }, '✗ '), 'blocked');
    case 'illustration':
      return h('span', { class: ['badge', 'badge--none', 'player__verb'] }, 'illustration');
  }
}

export function mountPlayer(ctx: AppContext, entry: SituationEntry, options: PlayerOptions = {}): PlayerHandle {
  const frames = playerFrames(entry);
  const length = frames.length - 1;
  const order = placeOrder(entry);
  const replayed = entry.result !== null;
  const reduced = prefersReducedMotion();
  const key = idPart(entry.slug);
  let state = initialState(length, options.initialStep ?? 0);
  const cleanups: (() => void)[] = [];
  let cancelAnimation: (() => void) | null = null;
  let timer: ReturnType<typeof setTimeout> | null = null;
  let disposed = false;

  // ---- canvas ----
  const svg = entry.diagram ? cloneDiagram(entry.slug) : null;
  const diagram = svg === null ? null : prepareDiagram(svg, `Net of ${entry.title}`);
  // The button names the action it takes. Phones start at natural size (labels stay
  // readable, the canvas scrolls); wider screens start fitted to the canvas width.
  const fitText = (fit: boolean): string => (fit ? 'Zoom to 100%' : 'Fit to width');
  const startFit = !(typeof matchMedia === 'function' && matchMedia('(max-width: 599px)').matches);
  const fitButton = h('button', { type: 'button', class: 'player__fit' }, fitText(startFit));
  const canvas = h('div', { class: ['player__canvas', diagram === null && 'player__canvas--empty'], 'data-fit': String(startFit) },
    diagram === null ? h('p', { class: 'player__missing' }, 'Diagram not available.') : [diagram.svg, fitButton],
  );
  fitButton.addEventListener('click', () => {
    const fit = canvas.getAttribute('data-fit') !== 'true';
    canvas.setAttribute('data-fit', fit ? 'true' : 'false');
    fitButton.textContent = fitText(fit);
  });

  // ---- controls ----
  const btnFirst = iconButton('First step', GLYPH.first, 'player__btn--first', () => dispatch({ type: 'first' }));
  const btnBack = iconButton('Previous step', GLYPH.back, 'player__btn--back', () => dispatch({ type: 'back' }));
  const btnPlay = iconButton('Play', GLYPH.play, 'player__btn--play', () => dispatch({ type: 'toggle' }));
  const btnNext = iconButton('Next step', GLYPH.next, 'player__btn--next', () => dispatch({ type: 'next' }));
  const btnLast = iconButton('Last step', GLYPH.last, 'player__btn--last', () => dispatch({ type: 'last' }));
  const scrubber = h('input', {
    type: 'range',
    class: 'player__scrubber',
    'aria-label': 'Step',
    attrs: { min: 0, max: length, step: 1 },
    value: String(state.step),
  });
  scrubber.addEventListener('input', () => dispatch({ type: 'goto', step: Number(scrubber.value) }));
  const counter = h('span', { class: 'player__counter', 'aria-hidden': 'true' });
  const controls = replayed
    ? h('div', { class: 'player__controls' },
      h('div', { class: 'player__buttons' }, btnFirst, btnBack, btnPlay, btnNext, btnLast),
      scrubber,
      counter,
    )
    : h('p', { class: 'player__note' }, h('strong', null, 'Not replayed. '), notReplayedText(entry.notReplayed));

  // ---- caption, live region ----
  const captionId = `player-caption-${key}`;
  const caption = h('div', { class: 'player__caption', id: captionId });
  const live = h('div', { class: 'sr-only', 'aria-live': 'polite', 'aria-atomic': 'true' });

  // ---- marking table ----
  const headCells = frames.map((f) => h('th', { scope: 'col', class: 'player__col' },
    f.step === 0 ? 'Start' : f.kind === 'blocked' ? [String(f.step), h('span', { 'aria-hidden': 'true' }, ' ✗'), h('span', { class: 'sr-only' }, ' blocked')] : String(f.step)));
  const bodyRows = order.map((p) => h('tr', null,
    h('th', { scope: 'row', class: 'player__place' }, p),
    frames.map((f) => h('td', { class: 'player__count' }, String(count(f.marking, p)))),
  ));
  const table = h('details', { class: 'player__table' },
    h('summary', null, 'Show marking as a table'),
    h('div', { class: 'player__table-scroll', tabindex: 0, role: 'region', 'aria-label': 'Marking per step' },
      h('table', null,
        h('caption', { class: 'sr-only' }, `Tokens per place at each step of ${entry.title}`),
        h('thead', null, h('tr', null, h('th', { scope: 'col' }, 'Place'), headCells)),
        h('tbody', null, bodyRows),
      ),
    ),
  );

  // ---- steps list ----
  const stepButtons: HTMLButtonElement[] = [];
  const stepItems: HTMLLIElement[] = [];
  const stepsList = h('ol', { class: 'player__steps', 'aria-label': replayed ? 'Steps of the replay' : 'Illustrative steps' });
  if (replayed) {
    frames.forEach((f) => {
      const label = f.kind === 'initial' ? 'Initial marking' : firingLabel(entry.net, f);
      const detail = f.kind === 'initial' ? markingText(f.marking, order) : f.kind === 'fired' ? deltaText(f.delta) : '';
      const button = h('button', { type: 'button', class: 'player__step', on: { click: () => dispatch({ type: 'goto', step: f.step }) } },
        h('span', { class: 'player__num' }, String(f.step)),
        verbBadge(f.kind),
        h('code', { class: 'player__name' }, label),
        detail === '' ? null : h('span', { class: 'player__detail' }, detail),
      );
      stepButtons.push(button);
      const item = h('li', { class: ['player__row', `player__row--${f.kind}`] }, button,
        f.blocked === null ? null : h('span', { class: 'player__rule' }, idLink(ctx, f.blocked.requirement)));
      stepItems.push(item);
      stepsList.append(item);
    });
  } else {
    entry.steps.forEach((st, i) => {
      stepsList.append(h('li', { class: ['player__row', 'player__row--illustration'] },
        h('div', { class: 'player__step', 'aria-disabled': 'true' },
          h('span', { class: 'player__num' }, String(i + 1)),
          verbBadge('illustration'),
          h('code', { class: 'player__name' }, firingLabel(entry.net, { fire: st.fire, branch: st.branch, timeout: st.timeout })),
          st.text === null ? null : h('span', { class: 'player__detail' }, inline(ctx, st.text, { ears: false })),
        ),
      ));
    });
  }
  const stepsHeadId = `player-steps-${key}`;
  const showAll = h('button', { type: 'button', class: ['player__link', 'player__show-all'], 'aria-expanded': 'false' },
    replayed ? `Show all ${length} steps` : 'Show all steps');
  showAll.addEventListener('click', () => {
    const open = side.getAttribute('data-expanded') !== 'true';
    side.setAttribute('data-expanded', open ? 'true' : 'false');
    showAll.setAttribute('aria-expanded', open ? 'true' : 'false');
    showAll.textContent = open ? 'Show the current step only' : replayed ? `Show all ${length} steps` : 'Show all steps';
  });
  const enabledLine = h('p', { class: 'player__enabled-line' });
  const side = h('div', { class: 'player__side', 'data-expanded': 'false' },
    h('h2', { class: 'player__side-title', id: stepsHeadId }, replayed ? 'Steps' : 'Steps (illustration)'),
    stepsList,
    replayed && length > 1 ? showAll : null,
    replayed ? enabledLine : null,
    verdictBox(ctx, entry, frames),
  );

  const stage = h('div', { class: 'player__stage' }, canvas, controls, replayed ? caption : null, table);
  const node = h('div', {
    class: ['player', replayed ? 'player--replay' : 'player--static'],
    role: 'group',
    // A programmatic focus target (no extra tab stop), so a view or test can focus the player
    // and its keys work at once; the SVG is the tab stop inside it.
    tabindex: -1,
    'aria-label': `Net player: ${entry.title}`,
    'aria-describedby': replayed ? captionId : null,
  }, stage, side, live);

  // ---- rendering ----
  const render = (previous: PlayerState | null): void => {
    const frame = frames[state.step];
    if (frame === undefined) return;
    const end = atEnd(state);
    setDisabled(btnFirst, state.step === 0);
    setDisabled(btnBack, state.step === 0);
    setDisabled(btnNext, end);
    setDisabled(btnLast, end);
    setDisabled(btnPlay, length === 0);
    const playLabel = state.playing ? 'Pause' : end && length > 0 ? 'Replay' : 'Play';
    btnPlay.setAttribute('aria-label', playLabel);
    btnPlay.setAttribute('title', playLabel);
    btnPlay.replaceChildren(h('span', { 'aria-hidden': 'true' }, state.playing ? GLYPH.pause : end && length > 0 ? GLYPH.replay : GLYPH.play));
    scrubber.value = String(state.step);
    scrubber.setAttribute('aria-valuetext', scrubberText(entry, frames, state.step));
    counter.textContent = `Step ${state.step} of ${length}`;

    // Caption or blocked callout (design 4.3).
    if (frame.kind === 'blocked' && frame.blocked !== null) {
      caption.className = 'player__caption player__caption--blocked';
      replaceChildren(caption,
        h('span', { class: 'player__blocked-label' }, h('span', { 'aria-hidden': 'true' }, '✗ '), 'Blocked'),
        h('span', { class: 'player__blocked-text' }, blockedText(frame),
          frame.text === null ? null : h('span', { class: 'player__blocked-note' }, inline(ctx, frame.text, { ears: false }))),
        h('span', { class: 'player__blocked-rule' }, idLink(ctx, frame.blocked.requirement)),
      );
    } else {
      const { lead, text } = captionParts(entry, frame, order);
      caption.className = 'player__caption';
      replaceChildren(caption, lead === null ? null : [h('strong', null, lead), ' '], inline(ctx, text, { ears: false }));
    }

    stepButtons.forEach((b, i) => {
      if (i === state.step) b.setAttribute('aria-current', 'step');
      else b.removeAttribute('aria-current');
    });
    stepItems.forEach((item, i) => item.classList.toggle('player__row--current', i === state.step));
    headCells.forEach((c, i) => {
      if (i === state.step) c.setAttribute('aria-current', 'step');
      else c.removeAttribute('aria-current');
    });
    for (const row of bodyRows) {
      Array.from(row.children).forEach((cell, i) => cell.classList.toggle('player__count--current', i === state.step + 1));
    }

    if (replayed) {
      const enabled = enabledTransitions(entry.net, frame.marking);
      replaceChildren(enabledLine,
        enabled.length === 0
          ? 'No transition is enabled in this marking.'
          : ['Enabled in this marking: ', enabled.map((n, i) => [i > 0 ? ' · ' : '', h('span', { class: 'player__enabled-name' }, h('span', { class: 'player__enabled-dot', 'aria-hidden': 'true' }, '● '), n)])],
      );
    }

    if (diagram !== null) {
      cancelAnimation?.();
      cancelAnimation = null;
      const forward = previous !== null && state.step === previous.step + 1 && frame.kind === 'fired';
      if (forward && !reduced && node.isConnected) {
        cancelAnimation = animateFiring(diagram, entry, frame, order, () => { cancelAnimation = null; });
      } else {
        paint(diagram, entry, frame, order, { reduced });
      }
    }

    if (previous !== null && previous.step !== state.step) live.textContent = announcement(entry, frames, state.step);
  };

  const stopTimer = (): void => {
    if (timer !== null) clearTimeout(timer);
    timer = null;
  };
  const schedule = (): void => {
    stopTimer();
    if (!state.playing || disposed) return;
    timer = setTimeout(() => {
      timer = null;
      dispatch({ type: 'tick' });
    }, reduced ? AUTOPLAY_REDUCED_MS : AUTOPLAY_MS);
  };

  function dispatch(action: PlayerAction): void {
    if (disposed) return;
    const before = state;
    // A click on an aria-disabled control does nothing.
    if ((action.type === 'first' || action.type === 'back') && before.step === 0) return;
    if ((action.type === 'next' || action.type === 'last') && atEnd(before)) return;
    let next = playerReducer(before, action);
    // Play starts with a step right away, unless it restarts from the initial marking.
    if ((action.type === 'play' || action.type === 'toggle') && next.playing && !before.playing && next.step === before.step) {
      next = playerReducer(next, { type: 'tick' });
    }
    if (next === before) return;
    state = next;
    render(before);
    schedule();
    if (next.step !== before.step) options.onStep?.(state.step);
  }

  // ---- keys (design 8.2): only while focus is inside the player group ----
  cleanups.push(listen(node, 'keydown', (e) => {
    if (e.defaultPrevented || e.ctrlKey || e.metaKey || e.altKey || !replayed) return;
    const target = e.target;
    // The scrubber handles its own keys; the marking table scrolls with the arrows.
    if (target instanceof HTMLInputElement) return;
    if (target instanceof Element && target.closest('.player__table') !== null) return;
    // Space keeps its native meaning on buttons and links.
    const onButton = target instanceof HTMLButtonElement || target instanceof HTMLAnchorElement;
    const actions: Readonly<Record<string, PlayerAction>> = {
      ArrowLeft: { type: 'back' },
      ArrowRight: { type: 'next' },
      Home: { type: 'first' },
      End: { type: 'last' },
    };
    if (e.key === ' ' && !onButton) {
      e.preventDefault();
      dispatch({ type: 'toggle' });
      return;
    }
    const action = actions[e.key];
    if (action !== undefined) {
      e.preventDefault();
      dispatch(action);
    }
  }));

  // ---- pause when hidden or scrolled away ----
  if (typeof document !== 'undefined') {
    cleanups.push(listen(document, 'visibilitychange', () => {
      if (document.hidden && state.playing) dispatch({ type: 'pause' });
    }));
  }
  if (typeof IntersectionObserver === 'function') {
    const observer = new IntersectionObserver((entries) => {
      if (entries.some((x) => !x.isIntersecting) && state.playing) dispatch({ type: 'pause' });
    });
    observer.observe(node);
    cleanups.push(() => observer.disconnect());
  }

  render(null);

  return {
    node,
    step: () => state.step,
    length,
    goTo(step: number): void {
      dispatch({ type: 'goto', step });
    },
    dispose(): void {
      if (disposed) return;
      stopTimer();
      cancelAnimation?.();
      cancelAnimation = null;
      disposed = true;
      for (const c of cleanups.splice(0)) c();
    },
  };
}
