import { describe, it, expect } from 'vitest';
import { Marking } from '../../src/runtime/marking.js';
import { place } from '../../src/core/place.js';
import { tokenOf, unitToken } from '../../src/core/token.js';
import type { ArcInput } from '../../src/core/arc.js';

describe('Marking', () => {
  const p1 = place<number>('P1');
  const p2 = place<string>('P2');

  it('empty marking has no tokens', () => {
    const m = Marking.empty();
    expect(m.hasTokens(p1)).toBe(false);
    expect(m.tokenCount(p1)).toBe(0);
    expect(m.peekTokens(p1)).toEqual([]);
  });

  it('from initializes with tokens', () => {
    const t1 = tokenOf(10);
    const t2 = tokenOf(20);
    const m = Marking.from(new Map([[p1, [t1, t2]]]));
    expect(m.hasTokens(p1)).toBe(true);
    expect(m.tokenCount(p1)).toBe(2);
  });

  it('addToken adds to place', () => {
    const m = Marking.empty();
    m.addToken(p1, tokenOf(42));
    expect(m.hasTokens(p1)).toBe(true);
    expect(m.tokenCount(p1)).toBe(1);
    expect(m.peekFirst(p1)!.value).toBe(42);
  });

  it('removeFirst removes oldest (FIFO)', () => {
    const m = Marking.empty();
    m.addToken(p1, tokenOf(1));
    m.addToken(p1, tokenOf(2));
    m.addToken(p1, tokenOf(3));

    const removed = m.removeFirst(p1);
    expect(removed!.value).toBe(1);
    expect(m.tokenCount(p1)).toBe(2);
    expect(m.peekFirst(p1)!.value).toBe(2);
  });

  it('removeFirst returns null on empty place', () => {
    const m = Marking.empty();
    expect(m.removeFirst(p1)).toBeNull();
  });

  it('removeAll removes and returns all tokens', () => {
    const m = Marking.empty();
    m.addToken(p1, tokenOf(1));
    m.addToken(p1, tokenOf(2));
    m.addToken(p1, tokenOf(3));

    const removed = m.removeAll(p1);
    expect(removed).toHaveLength(3);
    expect(removed.map(t => t.value)).toEqual([1, 2, 3]);
    expect(m.hasTokens(p1)).toBe(false);
    expect(m.tokenCount(p1)).toBe(0);
  });

  it('removeAll returns empty array on empty place', () => {
    const m = Marking.empty();
    expect(m.removeAll(p1)).toEqual([]);
  });

  it('removeFirstMatching without guard removes first', () => {
    const m = Marking.empty();
    m.addToken(p1, tokenOf(1));
    m.addToken(p1, tokenOf(2));
    const arc: ArcInput = { type: 'input', place: p1 };
    const removed = m.removeFirstMatching(arc);
    expect(removed!.value).toBe(1);
  });

  it('removeFirstMatching with guard skips non-matching', () => {
    const m = Marking.empty();
    m.addToken(p1, tokenOf(1));
    m.addToken(p1, tokenOf(10));
    m.addToken(p1, tokenOf(2));
    const arc: ArcInput = { type: 'input', place: p1, guard: (v: number) => v > 5 };
    const removed = m.removeFirstMatching(arc);
    expect(removed!.value).toBe(10);
    expect(m.tokenCount(p1)).toBe(2);
  });

  it('removeFirstMatching returns null when no match', () => {
    const m = Marking.empty();
    m.addToken(p1, tokenOf(1));
    const arc: ArcInput = { type: 'input', place: p1, guard: (v: number) => v > 100 };
    expect(m.removeFirstMatching(arc)).toBeNull();
    expect(m.tokenCount(p1)).toBe(1);
  });

  it('hasMatchingToken checks guard', () => {
    const m = Marking.empty();
    m.addToken(p1, tokenOf(1));
    m.addToken(p1, tokenOf(10));
    expect(m.hasMatchingToken({ place: p1, guard: (v: number) => v > 5 })).toBe(true);
    expect(m.hasMatchingToken({ place: p1, guard: (v: number) => v > 100 })).toBe(false);
    expect(m.hasMatchingToken({ place: p1 })).toBe(true);
  });

  it('peekTokens returns reference without removing', () => {
    const m = Marking.empty();
    m.addToken(p1, tokenOf(10));
    m.addToken(p1, tokenOf(20));
    m.addToken(p1, tokenOf(30));

    const tokens = m.peekTokens(p1);
    expect(tokens).toHaveLength(3);
    expect(tokens.map(t => t.value)).toEqual([10, 20, 30]);
    expect(m.tokenCount(p1)).toBe(3);
  });

  it('peekFirst returns null on empty place', () => {
    const m = Marking.empty();
    expect(m.peekFirst(p1)).toBeNull();
  });

  it('toString shows places with counts', () => {
    const m = Marking.empty();
    m.addToken(p1, tokenOf(1));
    m.addToken(p1, tokenOf(2));
    m.addToken(p2, tokenOf('hello'));

    const str = m.toString();
    expect(str).toContain('P1: 2');
    expect(str).toContain('P2: 1');
    expect(str).toMatch(/^Marking\{/);
  });

  it('empty marking toString is Marking{}', () => {
    expect(Marking.empty().toString()).toBe('Marking{}');
  });

  it('multiple places are independent', () => {
    const m = Marking.empty();
    m.addToken(p1, tokenOf(1));
    m.addToken(p2, tokenOf('a'));
    expect(m.hasTokens(p1)).toBe(true);
    expect(m.hasTokens(p2)).toBe(true);
    m.removeFirst(p1);
    expect(m.hasTokens(p1)).toBe(false);
    expect(m.hasTokens(p2)).toBe(true);
  });

  it('unit tokens work correctly', () => {
    const m = Marking.empty();
    m.addToken(p1, unitToken());
    expect(m.hasTokens(p1)).toBe(true);
    const removed = m.removeFirst(p1);
    expect(removed!.value).toBeNull();
  });
});
