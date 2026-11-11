// @vitest-environment happy-dom
import { readFileSync } from 'node:fs';
import { join } from 'node:path';
import { afterEach, describe, expect, it } from 'vitest';
import type { AppContext } from '../src/app/context.js';
import { buildIndex } from '../src/app/indexes.js';
import {
  ANIMATION_COLOURS,
  announcement,
  atEnd,
  blockedText,
  captionText,
  clampStep,
  deltaText,
  enabledTransitions,
  firedPrefix,
  firingLabel,
  initialState,
  markingAt,
  markingDelta,
  markingDescription,
  markingText,
  mountPlayer,
  notReplayedText,
  placeOrder,
  playerFrames,
  playerReducer,
  pointsBox,
  reasonSentence,
  readGeometry,
  scrubberText,
  sentence,
  tokenLayout,
  verdictOf,
  type PlayerState,
} from '../src/app/player.js';
import { renderDiagrams } from '../src/gen/diagrams.js';
import { buildSiteData } from '../src/gen/site.js';
import type { CoverageRow, SituationEntry, SpecBlock } from '../src/model.js';
import { diagramTemplateId } from '../src/model.js';
import { loadEntry, loadSituation, REPO } from './player-fixture.js';

// ---------------------------------------------------------------------------------------------
// The step-state reducer
// ---------------------------------------------------------------------------------------------

describe('playerReducer', () => {
  const s0: PlayerState = initialState(4);

  it('starts paused at the clamped initial step', () => {
    expect(initialState(4, 2)).toEqual({ step: 2, length: 4, playing: false });
    expect(initialState(4, 9).step).toBe(4);
    expect(initialState(4, -3).step).toBe(0);
    expect(initialState(4, Number.NaN).step).toBe(0);
    expect(clampStep(2.7, 4)).toBe(2);
  });

  it('moves with first, back, next, last and goto, clamped', () => {
    expect(playerReducer(s0, { type: 'next' }).step).toBe(1);
    expect(playerReducer(s0, { type: 'back' })).toBe(s0); // unchanged: same object
    expect(playerReducer(s0, { type: 'last' }).step).toBe(4);
    expect(playerReducer({ ...s0, step: 4 }, { type: 'next' }).step).toBe(4);
    expect(playerReducer({ ...s0, step: 3 }, { type: 'first' }).step).toBe(0);
    expect(playerReducer(s0, { type: 'goto', step: 3 }).step).toBe(3);
    expect(playerReducer(s0, { type: 'goto', step: 99 }).step).toBe(4);
  });

  it('stops autoplay on every user move', () => {
    const playing: PlayerState = { step: 1, length: 4, playing: true };
    for (const type of ['first', 'back', 'next', 'last', 'pause'] as const) {
      expect(playerReducer(playing, { type }).playing).toBe(false);
    }
    expect(playerReducer(playing, { type: 'goto', step: 2 }).playing).toBe(false);
  });

  it('plays, pauses and toggles', () => {
    const p = playerReducer(s0, { type: 'play' });
    expect(p).toEqual({ step: 0, length: 4, playing: true });
    expect(playerReducer(p, { type: 'toggle' }).playing).toBe(false);
    expect(playerReducer(s0, { type: 'toggle' }).playing).toBe(true);
  });

  it('replays from the initial marking when played at the end', () => {
    const end: PlayerState = { step: 4, length: 4, playing: false };
    expect(atEnd(end)).toBe(true);
    expect(playerReducer(end, { type: 'play' })).toEqual({ step: 0, length: 4, playing: true });
  });

  it('ticks forward only while playing and stops at the last step', () => {
    expect(playerReducer(s0, { type: 'tick' })).toBe(s0);
    let s: PlayerState = { step: 2, length: 4, playing: true };
    s = playerReducer(s, { type: 'tick' });
    expect(s).toEqual({ step: 3, length: 4, playing: true });
    s = playerReducer(s, { type: 'tick' });
    expect(s).toEqual({ step: 4, length: 4, playing: false });
  });

  it('never plays a run without steps', () => {
    const empty = initialState(0);
    expect(playerReducer(empty, { type: 'play' }).playing).toBe(false);
    expect(playerReducer(empty, { type: 'next' })).toBe(empty);
  });
});

// ---------------------------------------------------------------------------------------------
// Frames from the Lean replay
// ---------------------------------------------------------------------------------------------

describe('playerFrames', () => {
  const entry = loadEntry('inhibitor-blocks');
  const frames = playerFrames(entry);
  const order = placeOrder(entry);

  it('has the initial marking plus one frame per replayed step', () => {
    expect(frames.map((f) => f.kind)).toEqual(['initial', 'fired', 'fired', 'fired', 'blocked']);
    expect(frames[0]?.marking).toEqual({ job: 3 });
    expect(frames[1]?.marking).toEqual({ job: 2, lock: 1 });
  });

  it('agrees with markingAt for every fired step', () => {
    frames.forEach((f, k) => {
      const m = markingAt(entry, k);
      if (f.kind === 'blocked') expect(m).toBeNull();
      else expect(m).toEqual(f.marking);
    });
  });

  it('keeps the marking of a blocked step and carries Lean reason, rule and message', () => {
    const blocked = frames[4];
    expect(blocked?.marking).toEqual(frames[3]?.marking);
    expect(blocked?.delta).toEqual([]);
    expect(blocked?.blocked?.requirement).toBe('CORE-031');
    expect(blocked?.blocked?.reason).toEqual({ kind: 'inhibitorMarked', place: 'lock', count: 1 });
    expect(blocked?.text).toBe('A job still waits, but `lock` holds a token.');
  });

  it('computes the change of each step in place order', () => {
    expect(order).toEqual(['job', 'lock', 'done']);
    expect(frames[2]?.delta).toEqual([
      { place: 'lock', before: 1, after: 0 },
      { place: 'done', before: 0, after: 1 },
    ]);
    expect(deltaText(frames[1]?.delta ?? [])).toBe('job −1 · lock +1');
  });

  it('shows only the initial marking without a replay', () => {
    const { situation } = loadSituation('inhibitor-blocks');
    const still: SituationEntry = { ...situation, replay: false, notReplayed: 'timed', result: null, rules: [], diagram: true };
    expect(playerFrames(still)).toHaveLength(1);
    expect(markingAt(still, 0)).toEqual({ job: 3 });
  });

  it('orders places: declared first, then the ones only arcs name, sorted', () => {
    const base = loadEntry('inhibitor-blocks');
    const extra: SituationEntry = { ...base, net: { ...base.net, places: ['done'] } };
    expect(placeOrder(extra)).toEqual(['done', 'job', 'lock']);
  });
});

describe('markingDelta and markingText', () => {
  it('lists changed places only', () => {
    expect(markingDelta({ a: 1, b: 2 }, { b: 3, c: 1 }, ['a', 'b', 'c', 'd'])).toEqual([
      { place: 'a', before: 1, after: 0 },
      { place: 'b', before: 2, after: 3 },
      { place: 'c', before: 0, after: 1 },
    ]);
    expect(markingText({ b: 2, a: 1 }, ['a', 'b'])).toBe('a 1 · b 2');
    expect(markingText({}, ['a'])).toBe('No tokens');
  });
});

describe('enabledTransitions', () => {
  const entry = loadEntry('inhibitor-blocks');

  it('follows inputs, inhibitors and reads (CORE-022)', () => {
    expect(enabledTransitions(entry.net, { job: 3 })).toEqual(['take']);
    expect(enabledTransitions(entry.net, { job: 2, lock: 1 })).toEqual(['release']);
    expect(enabledTransitions(entry.net, {})).toEqual([]);
  });

  it('applies the cardinality of each input arc kind (IO-001..004)', () => {
    const net = {
      places: [],
      marking: {},
      properties: [],
      transitions: [
        { name: 'ex', inputs: [{ kind: 'exactly' as const, place: 'p', n: 2 }], inhibitors: [], reads: ['r'], resets: [], output: null, priority: 0, timing: null },
        { name: 'al', inputs: [{ kind: 'all' as const, place: 'p' }], inhibitors: [], reads: [], resets: [], output: null, priority: 0, timing: null },
        { name: 'ge', inputs: [{ kind: 'atLeast' as const, place: 'p', n: 3 }], inhibitors: [], reads: [], resets: [], output: null, priority: 0, timing: null },
      ],
    };
    expect(enabledTransitions(net, { p: 1 })).toEqual(['al']);
    expect(enabledTransitions(net, { p: 2, r: 1 })).toEqual(['ex', 'al']);
    expect(enabledTransitions(net, { p: 3, r: 1 })).toEqual(['ex', 'al', 'ge']);
  });
});

// ---------------------------------------------------------------------------------------------
// Words
// ---------------------------------------------------------------------------------------------

describe('captions and announcements', () => {
  const entry = loadEntry('inhibitor-blocks');
  const frames = playerFrames(entry);
  const order = placeOrder(entry);

  it('describes the initial marking', () => {
    expect(captionText(entry, frames[0]!, order)).toBe('Initial marking. 3 tokens in 1 place.');
  });

  it('leads a fired step with the transition and uses the authored text', () => {
    // The authored caption's code spans become plain text in the one-line caption.
    expect(captionText(entry, frames[1]!, order)).toBe('take fires. The place lock is empty, so take fires and marks it.');
  });

  it('uses the Lean message for a blocked step, as a sentence', () => {
    expect(blockedText(frames[4]!)).toBe("'take' is not enabled: inhibitor place 'lock' holds 1 token.");
    expect(sentence('Done.')).toBe('Done.');
  });

  it('announces steps for screen readers (design 10)', () => {
    expect(announcement(entry, frames, 0)).toBe('Back to the initial marking.');
    expect(announcement(entry, frames, 1)).toBe('Step 1 of 4: take fires. job 3 to 2, lock 0 to 1.');
    expect(announcement(entry, frames, 4)).toBe(
      "Step 4 of 4: take is blocked. 'take' is not enabled: inhibitor place 'lock' holds 1 token. Rule CORE-031.",
    );
  });

  it('gives the scrubber a value text', () => {
    expect(scrubberText(entry, frames, 0)).toBe('Step 0 of 4: initial marking');
    expect(scrubberText(entry, frames, 2)).toBe('Step 2 of 4: fire release');
    expect(scrubberText(entry, frames, 4)).toBe('Step 4 of 4: blocked take');
  });

  it('describes the marking of every place for the SVG desc', () => {
    expect(markingDescription(frames[1]!, order)).toBe('Marking after step 1: job 2, lock 1, done 0.');
    expect(markingDescription(frames[0]!, order)).toBe('Initial marking: job 3, lock 0, done 0.');
  });

  it('names the branch only where the output offers a choice', () => {
    const xor = loadEntry('xor-branch');
    expect(firingLabel(xor.net, { fire: 'triage', branch: 1, timeout: false })).toBe('triage, branch 1');
    expect(firingLabel(entry.net, { fire: 'take', branch: 0, timeout: false })).toBe('take');
    expect(firingLabel(entry.net, { fire: 'take', branch: 0, timeout: true })).toBe('take, timeout');
  });

  it('has a design 4.3 fallback sentence for every reason', () => {
    expect(reasonSentence('t', { kind: 'inputShort', place: 'p', arc: { kind: 'exactly', n: 2 }, need: 2, have: 1 }))
      .toBe('t is not enabled: input place p holds 1 token and it needs 2.');
    expect(reasonSentence('t', { kind: 'inhibitorMarked', place: 'busy', count: 1 })).toBe('t is not enabled: inhibitor place busy holds a token.');
    expect(reasonSentence('t', { kind: 'readEmpty', place: 'cfg' })).toBe('t is not enabled: read place cfg is empty.');
    expect(reasonSentence('t', { kind: 'noSuchBranch', branch: 2, timeout: false })).toBe('t has no output branch 2.');
    expect(reasonSentence('t', { kind: 'noSuchBranch', branch: 0, timeout: true })).toBe('t has no timeout outcome.');
    expect(reasonSentence('t', { kind: 'unknownTransition' })).toBe('The net has no transition named t.');
  });

  it('names why a situation is not replayed', () => {
    expect(notReplayedText('timed')).toBe('Lean replays untimed runs only; this situation is timed. Its rules show their Lean evidence below.');
    expect(notReplayedText('nu-net')).toContain('is a ν-net');
  });
});

describe('verdictOf', () => {
  it('agrees when every step fires or the run ends at its blocked step', () => {
    expect(verdictOf(loadEntry('inhibitor-blocks'))).toEqual({ kind: 'blocked', fired: 3, at: 4 });
    expect(verdictOf(loadEntry('two-subnets-glued'))).toEqual({ kind: 'complete', fired: 4 });
    expect(firedPrefix(0)).toBe('');
    expect(firedPrefix(1)).toBe('Step 1 fires. ');
    expect(firedPrefix(3)).toBe('Steps 1 to 3 fire. ');
  });

  it('disagrees when the replay stops before the authored run ends', () => {
    const e = loadEntry('inhibitor-blocks');
    const longer: SituationEntry = { ...e, steps: [...e.steps, { fire: 'release', branch: 0, timeout: false, text: null, expect: 'fired' }] };
    expect(verdictOf(longer)).toEqual({ kind: 'disagrees', at: 4 });
  });

  it('disagrees when a step does not do what its author expects', () => {
    const e = loadEntry('inhibitor-blocks');
    const meantToFire: SituationEntry = { ...e, steps: e.steps.map((st) => ({ ...st, expect: 'fired' })) };
    expect(verdictOf(meantToFire)).toEqual({ kind: 'expected-other', at: 4 });
  });

  it('has no verdict without a replay', () => {
    const e = loadEntry('inhibitor-blocks');
    expect(verdictOf({ ...e, replay: false, notReplayed: 'timed', result: null })).toEqual({ kind: 'not-replayed', why: 'timed' });
  });
});

// ---------------------------------------------------------------------------------------------
// Geometry and the palette
// ---------------------------------------------------------------------------------------------

describe('geometry', () => {
  it('reads a polygon box', () => {
    expect(pointsBox('88.64,-296.4 6.66,-296.4 6.66,-267.6 88.64,-267.6 88.64,-296.4')).toEqual({ x: 6.66, y: -296.4, w: 81.98, h: expect.closeTo(28.8, 5) });
    expect(pointsBox('')).toBeNull();
  });

  it('lays out 1 to 4 dots and a count from 5 tokens', () => {
    expect([0, 1, 2, 3, 4].map((n) => tokenLayout(n).dots.length)).toEqual([0, 1, 2, 3, 4]);
    expect(tokenLayout(7)).toEqual({ dots: [{ dx: -5, dy: 0 }], label: { dx: 3.5, dy: 3.5, text: '7' } });
    // Every dot stays inside a 0.35in place circle (radius 12.6pt).
    for (let n = 1; n <= 5; n += 1) {
      for (const d of tokenLayout(n).dots) expect(Math.hypot(d.dx, d.dy) + 3).toBeLessThanOrEqual(12.6);
    }
  });

  it('uses the animation palette of spec/petri-net-styles.json', () => {
    const styles: unknown = JSON.parse(readFileSync(join(REPO, 'spec', 'petri-net-styles.json'), 'utf8'));
    expect(styles).toMatchObject({ animation: ANIMATION_COLOURS });
  });
});

// ---------------------------------------------------------------------------------------------
// The mounted player (happy-dom)
// ---------------------------------------------------------------------------------------------

async function setup(slugs: readonly string[]): Promise<AppContext> {
  const inputs = slugs.map(loadSituation);
  const diagrams = await renderDiagrams(inputs);
  const holder = document.createElement('div');
  holder.id = 'diagrams';
  for (const [slug, svg] of diagrams) {
    const template = document.createElement('template');
    template.id = diagramTemplateId(slug);
    // Test-only: the page embeds the same markup the generator writes.
    template.innerHTML = svg;
    holder.append(template);
  }
  document.body.append(holder);
  // A stub block and coverage row for every rule the situations name, so the inputs agree.
  const ids = [...new Set(inputs.flatMap(({ situation, result }) => [
    ...situation.cites,
    ...(result?.steps ?? []).flatMap((st) => (st.kind === 'blocked' ? [st.requirement] : [])),
  ]))].sort();
  const blocks: SpecBlock[] = ids.map((id, line) => ({
    id, title: `Rule ${id}`, file: '01-core-model.md', line, section: null, priority: 'MUST', kind: 'B',
    status: { state: 'active' }, body: [], acceptance: [], notes: [], dependsOn: [], mentions: [], testDerivation: null, terms: [],
  }));
  const untested = { state: 'untested' } as const;
  const coverage: Record<string, CoverageRow> = Object.fromEntries(ids.map((id) => [id, {
    id, leanProofs: [], leanRef: false, tests: { java: untested, typescript: untested, rust: untested, python: untested },
  }]));
  const data = buildSiteData({
    spec: { files: [], blocks },
    glossary: [],
    lean: { blocks: [], citations: [] },
    coverage,
    defects: [],
    situations: inputs,
    diagrams: new Set(diagrams.keys()),
  });
  return { data, index: buildIndex(data), render: () => { throw new Error('unused'); }, navigate: () => {} };
}

function entryOf(ctx: AppContext, slug: string): SituationEntry {
  const e = ctx.index.situations.get(slug);
  if (e === undefined) throw new Error(`no situation ${slug}`);
  return e;
}

const key = (el: Element, k: string): void => {
  el.dispatchEvent(new KeyboardEvent('keydown', { key: k, bubbles: true, cancelable: true }));
};

describe('mountPlayer', () => {
  afterEach(() => {
    document.body.replaceChildren();
  });

  it('notes the untimed rule on a replay of a net with priorities', async () => {
    const ctx = await setup(['priority-order', 'inhibitor-blocks']);
    const withPriority = mountPlayer(ctx, entryOf(ctx, 'priority-order'));
    expect(withPriority.node.querySelector('.player__verdict-note')?.textContent).toContain('priorities play no part');
    const without = mountPlayer(ctx, entryOf(ctx, 'inhibitor-blocks'));
    expect(without.node.querySelector('.player__verdict-note')).toBeNull();
    withPriority.dispose();
    without.dispose();
  });

  it('draws the initial tokens on the exported places and nothing else changes', async () => {
    const ctx = await setup(['inhibitor-blocks']);
    const player = mountPlayer(ctx, entryOf(ctx, 'inhibitor-blocks'));
    document.body.append(player.node);
    const svg = player.node.querySelector('svg');
    expect(svg?.getAttribute('role')).toBe('img');
    expect(svg?.querySelector('title')?.textContent).toBe('Net of A held lock keeps the gate shut');
    expect(svg?.querySelector('desc')?.textContent).toBe('Initial marking: job 3, lock 0, done 0.');
    const tokens = player.node.querySelectorAll('.player__tokens [data-place-tokens] circle');
    expect(tokens.length).toBe(3); // three dots in job
    // The exported nodes keep their attributes: the player only adds layers.
    expect(svg?.querySelectorAll('g[data-kind="place"]').length).toBe(3);
    expect(player.node.querySelector('.player__caption')?.textContent).toBe('Initial marking. 3 tokens in 1 place.');
    const geo = readGeometry(svg as SVGSVGElement); // querySelector('svg') is an SVGSVGElement
    expect(geo.places.get('job')?.r).toBeCloseTo(12.6, 1);
    expect(geo.boxes.has('take')).toBe(true);
    player.dispose();
  });

  it('steps with the controls, mirrors the step, announces it and marks the list', async () => {
    const ctx = await setup(['inhibitor-blocks']);
    const seen: number[] = [];
    const player = mountPlayer(ctx, entryOf(ctx, 'inhibitor-blocks'), { onStep: (k) => seen.push(k) });
    document.body.append(player.node);
    expect(player.length).toBe(4);
    const next = player.node.querySelector<HTMLButtonElement>('.player__btn--next');
    const first = player.node.querySelector<HTMLButtonElement>('.player__btn--first');
    expect(first?.getAttribute('aria-disabled')).toBe('true');
    next?.click();
    expect(player.step()).toBe(1);
    expect(seen).toEqual([1]);
    expect(player.node.querySelector('[aria-live="polite"]')?.textContent).toBe('Step 1 of 4: take fires. job 3 to 2, lock 0 to 1.');
    expect(player.node.querySelector('.player__step[aria-current="step"] .player__num')?.textContent).toBe('1');
    expect(player.node.querySelector('.player__scrubber')?.getAttribute('aria-valuetext')).toBe('Step 1 of 4: fire take');
    expect(player.node.querySelectorAll('.player__changed').length).toBe(2);
    player.dispose();
  });

  it('shows a blocked step with the Lean message, the cited rule and the cause', async () => {
    const ctx = await setup(['inhibitor-blocks']);
    const player = mountPlayer(ctx, entryOf(ctx, 'inhibitor-blocks'), { initialStep: 4 });
    document.body.append(player.node);
    const callout = player.node.querySelector('.player__caption--blocked');
    expect(callout?.textContent).toContain("'take' is not enabled: inhibitor place 'lock' holds 1 token.");
    expect(callout?.querySelector('a.req-id')?.textContent).toBe('CORE-031');
    expect(player.node.querySelector('.player__blocked')).not.toBeNull();
    expect(player.node.querySelector('.player__cause')).not.toBeNull();
    expect(player.node.querySelector('.player__cause-arc')).not.toBeNull(); // the inhibitor arc
    expect(player.node.querySelector('.player__btn--play')?.getAttribute('aria-label')).toBe('Replay');
    expect(player.node.querySelector('.player__verdict')?.textContent).toContain('Steps 1 to 3 fire. Step 4 is blocked, as the situation says:');
    player.dispose();
  });

  it('answers the player keys only inside its group', async () => {
    const ctx = await setup(['inhibitor-blocks']);
    const player = mountPlayer(ctx, entryOf(ctx, 'inhibitor-blocks'));
    document.body.append(player.node);
    const svg = player.node.querySelector('svg');
    if (svg === null) throw new Error('no svg');
    key(svg, 'ArrowRight');
    key(svg, 'ArrowRight');
    expect(player.step()).toBe(2);
    key(svg, 'End');
    expect(player.step()).toBe(4);
    key(svg, 'ArrowLeft');
    expect(player.step()).toBe(3);
    key(svg, 'Home');
    expect(player.step()).toBe(0);
    key(document.body, 'ArrowRight');
    expect(player.step()).toBe(0);
    key(svg, ' ');
    expect(player.node.querySelector('.player__btn--play')?.getAttribute('aria-label')).toBe('Pause');
    expect(player.step()).toBe(1); // Play steps right away
    key(svg, ' ');
    expect(player.node.querySelector('.player__btn--play')?.getAttribute('aria-label')).toBe('Play');
    player.dispose();
  });

  it('autoplays to the end and stops there', async () => {
    const ctx = await setup(['xor-branch']);
    const player = mountPlayer(ctx, entryOf(ctx, 'xor-branch'));
    document.body.append(player.node);
    player.node.querySelector<HTMLButtonElement>('.player__btn--play')?.click();
    await new Promise((r) => setTimeout(r, 2 * 900 + 200));
    expect(player.step()).toBe(3);
    expect(player.node.querySelector('.player__btn--play')?.getAttribute('aria-label')).toBe('Replay');
    player.dispose();
  });

  it('shows a not-replayed situation as a static net with a note and illustrative steps', async () => {
    const ctx = await setup(['deadline-reaps']);
    const entry = entryOf(ctx, 'deadline-reaps');
    expect(entry.replay).toBe(false);
    const player = mountPlayer(ctx, entry);
    expect(player.length).toBe(0);
    expect(player.node.querySelector('.player__controls')).toBeNull();
    expect(player.node.querySelector('.player__note')?.textContent).toContain('Not replayed.');
    expect(player.node.querySelector('.player__verdict')).toBeNull();
    const rows = player.node.querySelectorAll('.player__row--illustration');
    expect(rows.length).toBe(entry.steps.length);
    player.dispose();
  });

  it('works detached (self-test renders) and without a diagram', async () => {
    const ctx = await setup(['xor-branch']);
    const entry: SituationEntry = { ...entryOf(ctx, 'xor-branch'), diagram: false };
    const player = mountPlayer(ctx, entry, { initialStep: 2 });
    expect(player.node.querySelector('.player__missing')?.textContent).toBe('Diagram not available.');
    expect(player.node.querySelector('.player__caption')?.textContent).toContain('triage, branch 1 fires.');
    player.goTo(3);
    expect(player.node.querySelector('.player__caption--blocked')).not.toBeNull();
    player.dispose();
    player.goTo(0); // after dispose: ignored
    expect(player.step()).toBe(3);
  });
});
