import { describe, it, expect } from 'vitest';
import { tokenOf, unitToken, tokenAt, isUnit } from '../../src/core/token.js';

describe('Token', () => {
  it('creates token with value and timestamp', () => {
    const before = Date.now();
    const token = tokenOf('hello');
    const after = Date.now();

    expect(token.value).toBe('hello');
    expect(token.createdAt).toBeGreaterThanOrEqual(before);
    expect(token.createdAt).toBeLessThanOrEqual(after);
  });

  it('creates token with specific timestamp', () => {
    const token = tokenAt(42, 1000);
    expect(token.value).toBe(42);
    expect(token.createdAt).toBe(1000);
  });

  it('unit token is a singleton', () => {
    const u1 = unitToken();
    const u2 = unitToken();
    expect(u1).toBe(u2);
  });

  it('unit token has null value and epoch timestamp', () => {
    const u = unitToken();
    expect(u.value).toBeNull();
    expect(u.createdAt).toBe(0);
  });

  it('isUnit detects unit token', () => {
    expect(isUnit(unitToken())).toBe(true);
    expect(isUnit(tokenOf('hello'))).toBe(false);
    expect(isUnit(tokenOf(null))).toBe(false);
  });

  it('supports various value types', () => {
    expect(tokenOf(42).value).toBe(42);
    expect(tokenOf(true).value).toBe(true);
    expect(tokenOf({ x: 1 }).value).toEqual({ x: 1 });
    expect(tokenOf([1, 2]).value).toEqual([1, 2]);
    expect(tokenOf(null).value).toBeNull();
  });
});
