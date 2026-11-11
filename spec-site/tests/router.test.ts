import { describe, expect, it } from 'vitest';
import { nodeKey, parseNodeKey, type GraphNode } from '../src/model.js';
import { formatRoute, isRouteHash, parseHash, queryList, R, reqGraph, type Route } from '../src/app/router.js';

const ROUND_TRIP: readonly Route[] = [
  R.situations(),
  R.situation('inhibitor-blocks'),
  R.situation('inhibitor-blocks', 3),
  R.req(),
  R.req('CORE-001'),
  R.req('CORE-001', { kind: 'B,F', lean: 'yes' }),
  R.conf({ f: 'defects,untested' }),
  R.graph(),
  reqGraph('EXEC-010'),
  reqGraph('EXEC-010', 'impact'),
  R.graph({ kind: 'term', slug: 'inhibitor-arc' }),
  R.graph({ kind: 'theorem', name: 'Libpetri.Spec.CONC_001_reference' }),
  R.impact({ kind: 'defect', id: 'RD-07' }),
  R.graph({ kind: 'situation', slug: 'xor-branch' }),
  R.selftest(),
];

describe('router', () => {
  it.each(ROUND_TRIP.map((r) => [formatRoute(r), r] as const))('round-trips %s', (hash, route) => {
    expect(parseHash(hash)).toEqual(route);
  });

  it('writes readable hashes with sorted query keys', () => {
    expect(formatRoute(R.req('CORE-001', { z: '1', a: '2' }))).toBe('#/req/CORE-001?a=2&z=1');
    expect(formatRoute(R.conf({ f: 'defects,untested' }))).toBe('#/conf?f=defects,untested');
    expect(formatRoute(R.graph({ kind: 'term', slug: 'inhibitor-arc' }))).toBe('#/graph/term:inhibitor-arc');
    expect(formatRoute(R.situation('xor-branch', 2))).toBe('#/situation/xor-branch?step=2');
  });

  it('drops empty query values so default filters never show', () => {
    expect(formatRoute(R.conf({ f: '' }))).toBe('#/conf');
    expect(queryList(parseHash('#/conf?f=defects,,untested').query, 'f')).toEqual(['defects', 'untested']);
  });

  it('maps unknown paths to notfound', () => {
    expect(parseHash('#/nope/x')).toEqual({ view: 'notfound', path: '/nope/x', query: {} });
    expect(parseHash('#/graph/impact')).toMatchObject({ view: 'notfound' });
    expect(parseHash('#/situation')).toMatchObject({ view: 'notfound' });
  });

  it('treats empty and #/ as home, plain anchors as non-routes', () => {
    expect(parseHash('')).toEqual(R.situations());
    expect(parseHash('#/')).toEqual(R.situations());
    expect(isRouteHash('#main')).toBe(false);
    expect(isRouteHash('#/req')).toBe(true);
  });
});

describe('graph node keys', () => {
  const nodes: readonly GraphNode[] = [
    { kind: 'req', id: 'CORE-031' },
    { kind: 'defect', id: 'RD-07' },
    { kind: 'term', slug: 'token-count' },
    { kind: 'theorem', name: 'Libpetri.Spec.CORE_031_reference' },
    { kind: 'situation', slug: 'xor-branch' },
  ];
  it.each(nodes.map((n) => [nodeKey(n), n] as const))('round-trips %s', (key, node) => {
    expect(parseNodeKey(key)).toEqual(node);
  });
});
