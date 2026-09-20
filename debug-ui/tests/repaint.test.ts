/**
 * The repaint subnet: panels repaint once per animation frame however many state changes the
 * frame covers, and neither dirty flags nor frame ticks pile up.
 *
 * Before, every event left one token on each `*Dirty` place and every repaint took one, and
 * the three panels shared the single `rafTick` of a frame. A burst of n events therefore cost
 * 3n repaints over 3n frames — unless the net had been idle, in which case the ticks nobody
 * had consumed (sixty a second, for as long as the page was open) paid for all of them at once.
 */
import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';
import * as p from '../src/net/places.js';
import { startNet, settle, tokenAdded, SESSION, type RunningNet } from './net-harness.js';
import { updateDiagramHighlighting } from '../src/net/actions/diagram.js';

vi.mock('../src/net/actions/connection.js', async (importOriginal) => {
  const original = await importOriginal<typeof import('../src/net/actions/connection.js')>();
  return { ...original, createWebSocket: vi.fn() };
});

vi.mock('../src/net/actions/diagram.js', async (importOriginal) => {
  const original = await importOriginal<typeof import('../src/net/actions/diagram.js')>();
  return { ...original, renderDotDiagram: vi.fn().mockResolvedValue(undefined), updateDiagramHighlighting: vi.fn() };
});

const REPAINTS = ['t_update_highlighting', 't_update_event_log', 't_update_marking'];

describe('repaint subnet', () => {
  let n: RunningNet;

  beforeEach(() => {
    vi.spyOn(console, 'debug').mockImplementation(() => {});
    vi.mocked(updateDiagramHighlighting).mockClear();
    n = startNet();
  });

  afterEach(() => {
    n.close();
    vi.restoreAllMocks();
  });

  const frame = async () => { await n.executor.injectValue(p.rafTick, undefined); await settle(); };
  const repaints = (from: number) => n.fired(from).filter(name => REPAINTS.includes(name)).sort();
  const resting = () => [p.rafTick.place, p.frameHighlight, p.frameLog, p.frameMarking, p.stateDirty, p.highlightDirty, p.logDirty, p.markingDirty]
    .filter(place => n.tokens(place) > 0).map(place => `${place.name}:${n.tokens(place)}`);

  it('frames with nothing to repaint leave nothing behind', async () => {
    await n.subscribe('live');
    await frame(); // the repaint the subscribe asked for

    const from = n.mark();
    for (let i = 0; i < 25; i++) void n.executor.injectValue(p.rafTick, undefined);
    await settle(80);

    expect(repaints(from)).toEqual([]);
    expect(resting()).toEqual([]);
  });

  it('frames before any session leave nothing behind', async () => {
    await n.connect();
    for (let i = 0; i < 25; i++) void n.executor.injectValue(p.rafTick, undefined);
    await settle(80);
    expect(resting()).toEqual([]);
  });

  it('fifty events and one frame: every panel repaints once, with the latest state', async () => {
    await n.subscribe('live');
    await frame();

    const from = n.mark();
    for (let i = 0; i < 50; i++) void n.inject({ type: 'event', sessionId: SESSION, index: i, event: tokenAdded(`p${i}`, String(i)) });
    await settle(250);
    expect(repaints(from)).toEqual([]); // no frame yet
    vi.mocked(updateDiagramHighlighting).mockClear();

    await frame();
    expect(repaints(from)).toEqual([...REPAINTS].sort());
    expect(vi.mocked(updateDiagramHighlighting).mock.calls[0]![0].eventIndex).toBe(50);
    expect(resting()).toEqual([]);

    await frame();
    expect(repaints(from)).toEqual([...REPAINTS].sort());
  });

  it('all three dirty panels repaint on the same frame', async () => {
    await n.subscribe('live');
    await frame();
    await n.inject({ type: 'event', sessionId: SESSION, index: 0, event: tokenAdded('pA', '1') });
    await settle();

    const from = n.mark();
    await frame();
    expect(repaints(from)).toEqual([...REPAINTS].sort());
  });
});
