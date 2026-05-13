import { describe, it, expect } from 'vitest';
import { place } from '../../src/core/place.js';
import type { Place } from '../../src/core/place.js';
import { Transition } from '../../src/core/transition.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { FusionSet } from '../../src/core/fusion-set.js';
import { one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import { tokenOf } from '../../src/core/token.js';
import type { Token } from '../../src/core/token.js';
import type { TransitionAction } from '../../src/core/transition-action.js';
import { SubnetDef } from '../../src/core/subnet-def.js';
import { BitmapNetExecutor } from '../../src/runtime/bitmap-net-executor.js';
import { Instance } from '../../src/core/instance.js';
import { leakyBucket } from '../fixtures/subnet-fixtures.js';

/**
 * Tests for {@link FusionSet} resolution at {@link PetriNet.builder}'s
 * `build()` per **MOD-061** (fusion resolution), exercising the structural
 * rewrite that substitutes non-canonical members with the canonical member
 * in every arc of every transition in the builder.
 *
 * Mirrors `java/src/test/java/org/libpetri/core/FusionTest.java`.
 *
 * Coverage:
 * - Single-set substitution: arcs originally referencing non-canonical
 *   members now reference the canonical member; non-canonical members are
 *   absent from the built net's place set.
 * - Independence: places not in any fusion set are untouched.
 * - Overlap detection: a place appearing in two fusion sets is rejected at
 *   `build()`.
 * - Three-way fusion of leaky-bucket `slots` places: shared rate limiter
 *   behavior verified end-to-end via the executor.
 * - Order independence: `fuse(...)` BEFORE `compose(...)` produces the same
 *   result as `fuse(...)` AFTER.
 * - Orthogonality with channel composition: a fusion set + a channel binding
 *   both apply correctly in one builder.
 * - Compose-then-fuse equals fuse-then-compose (structural equivalence).
 */

function findTransition(net: PetriNet, name: string): Transition {
  for (const t of net.transitions) {
    if (t.name === name) return t;
  }
  const available: string[] = [];
  for (const t of net.transitions) available.push(t.name);
  throw new Error(`no transition '${name}' in '${net.name}'. Available: [${available.join(', ')}]`);
}

function placeNames(net: PetriNet): Set<string> {
  const out = new Set<string>();
  for (const p of net.places) out.add(p.name);
  return out;
}

function findRenamedPlace(inst: Instance<unknown>, renamedName: string): Place<unknown> {
  for (const p of inst.renamedBody.places) {
    if (p.name === renamedName) return p;
  }
  const have: string[] = [];
  for (const p of inst.renamedBody.places) have.push(p.name);
  throw new Error(
    `no place '${renamedName}' in instance with prefix '${inst.prefix}'. Places: [${have.join(', ')}]`,
  );
}

function renamedSlots(inst: Instance<unknown>): Place<string> {
  return findRenamedPlace(inst, inst.prefix + '/slots') as Place<string>;
}

/**
 * Returns a map keyed by transition name, valued by a set of "kind:place"
 * strings summarising every arc reference. Lets us compare two nets' arc
 * topologies regardless of transition identity.
 */
function arcSummaryByTransitionName(net: PetriNet): Map<string, Set<string>> {
  const out = new Map<string, Set<string>>();
  for (const t of net.transitions) {
    const refs = new Set<string>();
    for (const spec of t.inputSpecs) refs.add('in:' + spec.place.name);
    for (const p of t.outputPlaces()) refs.add('out:' + p.name);
    for (const inh of t.inhibitors) refs.add('inh:' + inh.place.name);
    for (const r of t.reads) refs.add('read:' + r.place.name);
    for (const r of t.resets) refs.add('reset:' + r.place.name);
    out.set(t.name, refs);
  }
  return out;
}

describe('PetriNetBuilder.fuse — fusion resolution at build (MOD-061)', () => {
  // ============================================================
  //  MOD-061: single fusion set substitutes non-canonical → canonical
  // ============================================================

  it('fuse_substitutesNonCanonicalInArcs', () => {
    const a = place<string>('A'); // canonical
    const b = place<string>('B'); // non-canonical
    const sink = place<string>('sink');

    // T1 reads from B (non-canonical) → after fuse, reads from A.
    const t1 = Transition.builder('readFromB').read(b).build();
    // T2 writes to B (non-canonical) → after fuse, writes to A.
    const t2 = Transition.builder('writeToB')
      .inputs(one(sink))
      .outputs(outPlace(b))
      .build();

    const net = PetriNet.builder('Fused')
      .transitions(t1, t2)
      .fuse(FusionSet.of('ab', a, b))
      .build();

    const names = placeNames(net);
    expect(names.has('A')).toBe(true);
    expect(names.has('sink')).toBe(true);
    expect(names.has('B')).toBe(false);

    const readFromB = findTransition(net, 'readFromB');
    const readNames = new Set([...readFromB.readPlaces()].map((p) => p.name));
    expect(readNames.has('A')).toBe(true);
    expect(readNames.has('B')).toBe(false);

    const writeToB = findTransition(net, 'writeToB');
    const outNames = new Set([...writeToB.outputPlaces()].map((p) => p.name));
    expect(outNames.has('A')).toBe(true);
    expect(outNames.has('B')).toBe(false);
  });

  // ============================================================
  //  Unrelated places are untouched
  // ============================================================

  it('fuse_unrelatedPlaces_unchanged', () => {
    const a = place<string>('A');
    const b = place<string>('B');
    const c = place<string>('C'); // unrelated to {A, B}

    const t1 = Transition.builder('usesC').read(c).build();

    const net = PetriNet.builder('Mixed')
      .transitions(t1)
      .place(c)
      .fuse(FusionSet.of('ab', a, b))
      .build();

    expect(placeNames(net).has('C')).toBe(true);
    const rewritten = findTransition(net, 'usesC');
    const readNames = new Set([...rewritten.readPlaces()].map((p) => p.name));
    expect(readNames.has('C')).toBe(true);
  });

  // ============================================================
  //  Overlap detection: a place in two fusion sets is rejected
  // ============================================================

  it('fuse_overlappingFusionSets_throws', () => {
    const a = place<string>('A');
    const b = place<string>('B');
    const c = place<string>('C');

    const s1 = FusionSet.of('set1', a, b);
    const s2 = FusionSet.of('set2', b, c); // B is in both!

    let caught: Error | undefined;
    try {
      PetriNet.builder('Bad').fuse(s1, s2).build();
    } catch (e) {
      caught = e as Error;
    }
    expect(caught).toBeDefined();
    expect(caught!.message).toContain('B');
    expect(caught!.message).toContain('set1');
    expect(caught!.message).toContain('set2');
  });

  // ============================================================
  //  MOD-061 acceptance: three-bucket shared rate limiter
  // ============================================================

  it('fuse_chained_threeBucketsShareLimiter', async () => {
    // Three instances of leaky-bucket, each with its own internal `slots`
    // place. Compose all three; declare a fusion set across the three slots
    // places. The resulting net has a single canonical `slots`. Bind a
    // forwarding action that consumes input and emits a marker to every
    // declared output place: the default passthrough emits no outputs, so we
    // need explicit forwarding to observe accept/reject markings.
    const forward: TransitionAction = async (ctx) => {
      for (const op of ctx.outputPlaces()) {
        ctx.output(op as Place<string>, 'x');
      }
    };
    const actions: Record<string, TransitionAction> = {
      accept: forward,
      reject: forward,
    };

    const bucketDef = leakyBucket(2);
    const b1 = bucketDef.instantiate('b1', { rate: 2, label: 'b1' }).bindActions(actions);
    const b2 = bucketDef.instantiate('b2', { rate: 2, label: 'b2' }).bindActions(actions);
    const b3 = bucketDef.instantiate('b3', { rate: 2, label: 'b3' }).bindActions(actions);

    // Each instance gets its own external request/accept/reject places.
    const req1 = place<string>('req1');
    const acc1 = place<string>('acc1');
    const rej1 = place<string>('rej1');
    const req2 = place<string>('req2');
    const acc2 = place<string>('acc2');
    const rej2 = place<string>('rej2');
    const req3 = place<string>('req3');
    const acc3 = place<string>('acc3');
    const rej3 = place<string>('rej3');

    // The leakyBucket fixture keeps slots as an INTERNAL place (not a port —
    // that is the whole point of fusion: shared cross-instance state without
    // exposing it as a port on every subnet). Resolve the renamed slots
    // places by name on the renamed body.
    const slotsB1 = renamedSlots(b1);
    const slotsB2 = renamedSlots(b2);
    const slotsB3 = renamedSlots(b3);

    const net = PetriNet.builder('ThreeBuckets')
      .compose(b1, (m) =>
        m.bindPort('request', req1).bindPort('accept', acc1).bindPort('reject', rej1),
      )
      .compose(b2, (m) =>
        m.bindPort('request', req2).bindPort('accept', acc2).bindPort('reject', rej2),
      )
      .compose(b3, (m) =>
        m.bindPort('request', req3).bindPort('accept', acc3).bindPort('reject', rej3),
      )
      .fuse(FusionSet.of('sharedSlots', slotsB1, slotsB2, slotsB3))
      .build();

    // Assertion 1: canonical slotsB1 survives; non-canonical slotsB2/B3 do not.
    const names = placeNames(net);
    expect(names.has('b1/slots')).toBe(true);
    expect(names.has('b2/slots')).toBe(false);
    expect(names.has('b3/slots')).toBe(false);

    // Assertion 2: every accept transition consumes from the canonical slots.
    const b1AcceptT = findTransition(net, 'b1/accept');
    const b1AcceptInputNames = new Set([...b1AcceptT.inputPlaces()].map((p) => p.name));
    expect(b1AcceptInputNames.has('b1/slots')).toBe(true);

    const b2AcceptT = findTransition(net, 'b2/accept');
    const b2AcceptInputNames = new Set([...b2AcceptT.inputPlaces()].map((p) => p.name));
    expect(b2AcceptInputNames.has('b1/slots')).toBe(true);
    expect(b2AcceptInputNames.has('b2/slots')).toBe(false);

    const b3AcceptT = findTransition(net, 'b3/accept');
    const b3AcceptInputNames = new Set([...b3AcceptT.inputPlaces()].map((p) => p.name));
    expect(b3AcceptInputNames.has('b1/slots')).toBe(true);
    expect(b3AcceptInputNames.has('b3/slots')).toBe(false);

    // Assertion 3: dynamic behaviour — only 2 slots total are available
    // across all three buckets. Send three requests; only 2 should accept.
    const initial = new Map<Place<unknown>, Token<unknown>[]>();
    initial.set(req1, [tokenOf('r1')] as Token<unknown>[]);
    initial.set(req2, [tokenOf('r2')] as Token<unknown>[]);
    initial.set(req3, [tokenOf('r3')] as Token<unknown>[]);
    // 2 shared slots — pick the canonical place by name in the built net.
    const canonicalSlots = [...net.places].find((p) => p.name === 'b1/slots')!;
    initial.set(canonicalSlots, [tokenOf('s'), tokenOf('s')] as Token<unknown>[]);

    const executor = new BitmapNetExecutor(net, initial as Map<Place<any>, Token<any>[]>);
    const finalMarking = await executor.run(2000);

    // Look up acc/rej places in the built net by name (the place objects we
    // declared above flow through unchanged because they are the caller-
    // bound port targets).
    const acc1Built = [...net.places].find((p) => p.name === 'acc1')!;
    const acc2Built = [...net.places].find((p) => p.name === 'acc2')!;
    const acc3Built = [...net.places].find((p) => p.name === 'acc3')!;
    const rej1Built = [...net.places].find((p) => p.name === 'rej1')!;
    const rej2Built = [...net.places].find((p) => p.name === 'rej2')!;
    const rej3Built = [...net.places].find((p) => p.name === 'rej3')!;

    const totalAccepts =
      finalMarking.tokenCount(acc1Built) +
      finalMarking.tokenCount(acc2Built) +
      finalMarking.tokenCount(acc3Built);
    const totalRejects =
      finalMarking.tokenCount(rej1Built) +
      finalMarking.tokenCount(rej2Built) +
      finalMarking.tokenCount(rej3Built);

    expect(totalAccepts).toBe(2);
    expect(totalRejects).toBe(1);
  });

  // ============================================================
  //  Order independence: fuse before compose vs after compose
  // ============================================================

  it('fuse_runsAfterCompose: registering fuse before compose still resolves correctly', () => {
    // Declare a fusion set BEFORE the compose call. The fusion set
    // references places that only exist after the renamed body is merged
    // into the host. Builder accumulates fuse sets and applies at build().
    const bucketDef = leakyBucket(1);
    const b1 = bucketDef.instantiate('b1', { rate: 1, label: 'b1' });
    const b2 = bucketDef.instantiate('b2', { rate: 1, label: 'b2' });

    const req1 = place<string>('req1');
    const acc1 = place<string>('acc1');
    const rej1 = place<string>('rej1');
    const req2 = place<string>('req2');
    const acc2 = place<string>('acc2');
    const rej2 = place<string>('rej2');

    const slotsB1 = renamedSlots(b1);
    const slotsB2 = renamedSlots(b2);

    // fuse(...) called BEFORE the compose calls.
    const net = PetriNet.builder('OrderIndependent')
      .fuse(FusionSet.of('shared', slotsB1, slotsB2))
      .compose(b1, (m) =>
        m.bindPort('request', req1).bindPort('accept', acc1).bindPort('reject', rej1),
      )
      .compose(b2, (m) =>
        m.bindPort('request', req2).bindPort('accept', acc2).bindPort('reject', rej2),
      )
      .build();

    const names = placeNames(net);
    expect(names.has('b1/slots')).toBe(true);
    expect(names.has('b2/slots')).toBe(false);

    const b2AcceptT = findTransition(net, 'b2/accept');
    const b2AcceptInputNames = new Set([...b2AcceptT.inputPlaces()].map((p) => p.name));
    expect(b2AcceptInputNames.has('b1/slots')).toBe(true);
  });

  // ============================================================
  //  Orthogonality with channel composition (MOD-021 + MOD-061)
  // ============================================================

  it('fuse_independentOfChannelComposition: a fusion set + a channel binding both apply', () => {
    // Subnet with a channel `fire` and an internal place `shared`.
    const sharedDef = place<string>('shared');
    const tickDef = place<string>('tick');
    const fireT = Transition.builder('fire')
      .read(tickDef)
      .outputs(outPlace(sharedDef))
      .build();
    const def = SubnetDef.builder('HasChannelAndInternal')
      .place(sharedDef)
      .place(tickDef)
      .transition(fireT)
      .channel('fire', fireT)
      .build();

    const inst = def.instantiate('i1');

    // Caller-side place to fuse with the renamed shared place.
    const hostShared = place<string>('hostShared');

    // Caller-side transition for the channel binding.
    const hostTrigger = place<string>('hostTrigger');
    const callerSide = Transition.builder('callerFire').read(hostTrigger).build();

    const renamedShared = findRenamedPlace(inst, 'i1/shared') as Place<string>;

    const net = PetriNet.builder('ChannelPlusFusion')
      .compose(inst, (m) => m.bindChannel('fire', callerSide))
      .fuse(FusionSet.of('share', hostShared, renamedShared))
      .build();

    // Channel composition: the merged caller-side transition exists.
    const merged = findTransition(net, 'callerFire');
    // Fusion: the renamed-instance shared place is gone; hostShared is the
    // canonical and lives in the place set + on the merged transition's
    // output.
    const names = placeNames(net);
    expect(names.has('hostShared')).toBe(true);
    expect(names.has('i1/shared')).toBe(false);

    const mergedOutNames = new Set([...merged.outputPlaces()].map((p) => p.name));
    expect(mergedOutNames.has('hostShared')).toBe(true);
  });

  // ============================================================
  //  fuse + compose orthogonality: structural equivalence
  // ============================================================

  it('fuse_andCompose_orthogonality: compose-then-fuse equals fuse-then-compose', () => {
    // Two equivalent flat nets:
    //   netA: compose-then-fuse (fuse() called after compose())
    //   netB: fuse-then-compose (fuse() called before compose())
    // Both must produce structurally equivalent place + arc sets.
    const bucketDef = leakyBucket(2);

    // ---- netA: compose-then-fuse ----
    const b1A = bucketDef.instantiate('b1', { rate: 2, label: 'b1' });
    const b2A = bucketDef.instantiate('b2', { rate: 2, label: 'b2' });
    const req1A = place<string>('req1');
    const acc1A = place<string>('acc1');
    const rej1A = place<string>('rej1');
    const req2A = place<string>('req2');
    const acc2A = place<string>('acc2');
    const rej2A = place<string>('rej2');
    const slotsB1A = renamedSlots(b1A);
    const slotsB2A = renamedSlots(b2A);

    const netA = PetriNet.builder('ComposeThenFuse')
      .compose(b1A, (m) =>
        m.bindPort('request', req1A).bindPort('accept', acc1A).bindPort('reject', rej1A),
      )
      .compose(b2A, (m) =>
        m.bindPort('request', req2A).bindPort('accept', acc2A).bindPort('reject', rej2A),
      )
      .fuse(FusionSet.of('shared', slotsB1A, slotsB2A))
      .build();

    // ---- netB: fuse-then-compose (same SubnetDef + same prefix → same renamed slots place) ----
    const b1B = bucketDef.instantiate('b1', { rate: 2, label: 'b1' });
    const b2B = bucketDef.instantiate('b2', { rate: 2, label: 'b2' });
    const req1B = place<string>('req1');
    const acc1B = place<string>('acc1');
    const rej1B = place<string>('rej1');
    const req2B = place<string>('req2');
    const acc2B = place<string>('acc2');
    const rej2B = place<string>('rej2');
    const slotsB1B = renamedSlots(b1B);
    const slotsB2B = renamedSlots(b2B);

    const netB = PetriNet.builder('FuseThenCompose')
      .fuse(FusionSet.of('shared', slotsB1B, slotsB2B))
      .compose(b1B, (m) =>
        m.bindPort('request', req1B).bindPort('accept', acc1B).bindPort('reject', rej1B),
      )
      .compose(b2B, (m) =>
        m.bindPort('request', req2B).bindPort('accept', acc2B).bindPort('reject', rej2B),
      )
      .build();

    // Place sets must match by name (TS Place identity is name-based).
    const namesA = placeNames(netA);
    const namesB = placeNames(netB);
    expect([...namesA].sort()).toEqual([...namesB].sort());

    // Transition arc topologies must match by transition name.
    const summaryA = arcSummaryByTransitionName(netA);
    const summaryB = arcSummaryByTransitionName(netB);
    expect(summaryA.size).toBe(summaryB.size);
    for (const [tName, refsA] of summaryA) {
      const refsB = summaryB.get(tName);
      expect(refsB, `transition '${tName}' missing in netB`).toBeDefined();
      expect([...refsA].sort()).toEqual([...refsB!].sort());
    }
  });

  // ============================================================
  //  Sugar overload: fuse(declarer)
  // ============================================================

  it('fuse_sugarOverload_buildsAndApplies: the consumer-style fuse(b => ...) works', () => {
    const a = place<string>('A');
    const b = place<string>('B');

    const t1 = Transition.builder('readFromB').read(b).build();

    const net = PetriNet.builder('Sugar')
      .transition(t1)
      .fuse((fb) => {
        fb.member(a).member(b);
      })
      .build();

    const names = placeNames(net);
    expect(names.has('A')).toBe(true);
    expect(names.has('B')).toBe(false);
  });

  // ============================================================
  //  Multiple disjoint fusion sets: each applies independently
  // ============================================================

  it('fuse_multipleSets_eachAppliesIndependently', () => {
    const a = place<string>('A');
    const b = place<string>('B');
    const c = place<string>('C');
    const d = place<string>('D');

    const t1 = Transition.builder('readsBandD').read(b).read(d).build();

    const net = PetriNet.builder('Multi')
      .transition(t1)
      .fuse(FusionSet.of('ab', a, b), FusionSet.of('cd', c, d))
      .build();

    const names = placeNames(net);
    expect(names.has('A')).toBe(true);
    expect(names.has('C')).toBe(true);
    expect(names.has('B')).toBe(false);
    expect(names.has('D')).toBe(false);

    const rewritten = findTransition(net, 'readsBandD');
    const readNames = new Set([...rewritten.readPlaces()].map((p) => p.name));
    expect(readNames.has('A')).toBe(true);
    expect(readNames.has('C')).toBe(true);
    expect(readNames.has('B')).toBe(false);
    expect(readNames.has('D')).toBe(false);
  });

  // ============================================================
  //  Single-member fusion set is a no-op
  // ============================================================

  it('fuse_singleMemberSet_isNoOp', () => {
    const a = place<string>('A');
    const t1 = Transition.builder('readsA').read(a).build();

    const net = PetriNet.builder('SoloFusion')
      .transition(t1)
      .fuse(FusionSet.builder('solo').member(a).build())
      .build();

    expect(placeNames(net).has('A')).toBe(true);
    const rewritten = findTransition(net, 'readsA');
    const readNames = new Set([...rewritten.readPlaces()].map((p) => p.name));
    expect(readNames.has('A')).toBe(true);
  });
});
