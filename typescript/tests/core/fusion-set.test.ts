import { describe, it, expect } from 'vitest';
import { place } from '../../src/core/place.js';
import type { Place } from '../../src/core/place.js';
import { FusionSet, FusionSetBuilder } from '../../src/core/fusion-set.js';
import { __FUSION_SET_KEY_FOR_TEST } from '../../src/core/fusion-set.js';

/**
 * Unit tests for {@link FusionSet} per **MOD-060** (fusion set declaration).
 *
 * These tests exercise the construction and validation surface of the carrier
 * object only — the actual fusion-resolution semantics (substitution at
 * `build()` time) are covered by `fusion.test.ts`.
 *
 * Mirrors `java/src/test/java/org/libpetri/core/FusionSetTest.java`. The
 * TypeScript token-type homogeneity check is omitted at runtime (per the
 * TS-specific MOD-022 clause); compile-time `<T>` enforcement on
 * {@link FusionSetBuilder.member} and {@link FusionSet.of} provides the same
 * guarantee at the call site.
 */

describe('FusionSet — construction and validation (MOD-060)', () => {
  // ============================================================
  //  Canonical-member convention
  // ============================================================

  it('firstMemberIsCanonical: first declared member surfaces via .canonical', () => {
    const a = place<string>('A');
    const b = place<string>('B');
    const c = place<string>('C');

    const set = FusionSet.builder('limiter')
      .member(a)
      .member(b)
      .member(c)
      .build();

    expect(set.canonical).toBe(a);
    expect(set.members.length).toBe(3);
    expect(set.members[0]).toBe(a);
    expect(set.members[1]).toBe(b);
    expect(set.members[2]).toBe(c);
    expect(set.name).toBe('limiter');
  });

  // ============================================================
  //  Empty-set rejection (MOD-060)
  // ============================================================

  it('emptySet_throws: building with zero members is rejected', () => {
    expect(() => FusionSet.builder('empty').build()).toThrowError(/empty/);
  });

  // ============================================================
  //  Single-member set: degenerate but allowed (no-op fusion)
  // ============================================================

  it('singleMember_isValid: single-member fusion set is degenerate but accepted', () => {
    const only = place<string>('only');

    const set = FusionSet.builder('solo').member(only).build();

    expect(set.canonical).toBe(only);
    expect(set.members.length).toBe(1);
    expect(set.nonCanonical().length).toBe(0);
  });

  // ============================================================
  //  Static of(...) factory convenience (MOD-060)
  // ============================================================

  it('of_factoryConvenience: of(name, first, ...rest) builds the same shape', () => {
    const a = place<string>('A');
    const b = place<string>('B');
    const c = place<string>('C');

    const set = FusionSet.of('rate', a, b, c);

    expect(set.canonical).toBe(a);
    expect(set.members.length).toBe(3);
    expect(set.nonCanonical().length).toBe(2);
    expect(set.nonCanonical()[0]).toBe(b);
    expect(set.nonCanonical()[1]).toBe(c);
  });

  // ============================================================
  //  nonCanonical() returns all members except the first
  // ============================================================

  it('nonCanonical_returnsAllButFirst: the canonical is excluded, order preserved', () => {
    const a = place<number>('A');
    const b = place<number>('B');
    const c = place<number>('C');
    const d = place<number>('D');

    const set = FusionSet.builder('ints')
      .member(a)
      .member(b)
      .member(c)
      .member(d)
      .build();

    const nc = set.nonCanonical();
    expect(nc.length).toBe(3);
    expect(nc[0]).toBe(b);
    expect(nc[1]).toBe(c);
    expect(nc[2]).toBe(d);
    // canonical not in non-canonical set
    expect(nc.includes(a)).toBe(false);

    // Returned array view is structurally read-only (frozen members + slice).
    // Attempting to mutate `members` directly should fail in strict mode.
    expect(() => {
      (set.members as Place<unknown>[]).push(a);
    }).toThrow();
  });

  // ============================================================
  //  Symbol-guarded constructor
  // ============================================================

  it('constructor_isSymbolGuarded: direct construction with the wrong key is rejected', () => {
    const a = place<string>('A');
    expect(() => new FusionSet(Symbol('not-the-key'), 'x', [a])).toThrowError(
      /Use FusionSet/,
    );
  });

  it('constructor_isSymbolGuarded: construction with the right (internal) key works', () => {
    const a = place<string>('A');
    const set = new FusionSet(__FUSION_SET_KEY_FOR_TEST, 'x', [a]);
    expect(set.canonical).toBe(a);
    expect(set.members.length).toBe(1);
  });

  // ============================================================
  //  Builder validation
  // ============================================================

  it('builder_rejectsEmptyName: empty string name is rejected eagerly', () => {
    expect(() => new FusionSetBuilder('')).toThrowError(/non-empty/);
  });

  it('toString_isReadable: the toString form names canonical and member count', () => {
    const a = place<string>('A');
    const b = place<string>('B');
    const set = FusionSet.of('rate', a, b);
    expect(set.toString()).toContain('rate');
    expect(set.toString()).toContain('A');
    expect(set.toString()).toContain('2');
  });
});
