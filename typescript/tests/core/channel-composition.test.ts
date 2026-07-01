import { describe, it, expect } from 'vitest';
import { place } from '../../src/core/place.js';
import type { Place } from '../../src/core/place.js';
import { Transition } from '../../src/core/transition.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import { delayed, immediate, deadline } from '../../src/core/timing.js';
import type { TransitionAction } from '../../src/core/transition-action.js';
import { passthrough } from '../../src/core/transition-action.js';
import { TransitionContext } from '../../src/core/transition-context.js';
import { TokenInput } from '../../src/core/token-input.js';
import { TokenOutput } from '../../src/core/token-output.js';
import { tokenOf, tokenAt } from '../../src/core/token.js';
import type { Token } from '../../src/core/token.js';
import { nameId } from '../../src/core/name.js';
import { matchSpec, matchKey } from '../../src/core/match-spec.js';
import {
  composeActions,
  mergeTransitions,
} from '../../src/core/internal/subnet-rewriter.js';
import { BitmapNetExecutor } from '../../src/runtime/bitmap-net-executor.js';
import { retryPolicy } from '../fixtures/subnet-fixtures.js';

/**
 * Tests for synchronous-channel composition per **MOD-021**: the caller-side
 * transition and the instance-side renamed channel transition fuse into a
 * single merged transition in the composed flat net.
 *
 * Mirrors `java/src/test/java/org/libpetri/core/ChannelCompositionTest.java`.
 *
 * Coverage:
 * - Arc-union semantics across all arc kinds (input, read, output, inhibitor,
 *   reset).
 * - Dedup via structural-key equality on shared places.
 * - Caller-wins identity, name, priority.
 * - Timing resolution: caller-wins on Immediate, instance-wins on
 *   caller-Immediate, equal collapse, conflict throws.
 * - Action composition: sequential caller-then-instance, undefined-safety,
 *   both-passthrough collapses to passthrough.
 * - End-to-end retry-policy fixture: composing into a host net wires the
 *   retry-policy logic into the host's call site, observable via the
 *   executor.
 */

/**
 * Small helper to build a TransitionContext over a transition's declared
 * structure — used by the action-composition unit tests to drive the merged
 * action without spinning up the executor.
 */
function ctxFor(t: Transition): TransitionContext {
  return new TransitionContext(
    t.name,
    new TokenInput(),
    new TokenOutput(),
    t.inputPlaces(),
    t.readPlaces(),
    t.outputPlaces(),
  );
}

describe('SubnetRewriter.mergeTransitions — channel composition (MOD-021)', () => {
  // ============================================================
  //  Arc-union semantics
  // ============================================================

  it('channelMerge_unionsArcsFromBothSides: read arcs from both sides survive', () => {
    const a = place<string>('a');
    const b = place<string>('b');

    const caller = Transition.builder('merged').read(a).build();
    const instance = Transition.builder('instanceSide').read(b).build();

    const merged = mergeTransitions(caller, instance, 'merged');

    expect(merged.name).toBe('merged');
    const readPlaces = new Set([...merged.readPlaces()].map((p) => p.name));
    expect(readPlaces.has('a')).toBe(true);
    expect(readPlaces.has('b')).toBe(true);
    expect(merged.reads.length).toBe(2);
  });

  it('channelMerge_unionsInputArcs: input arcs from both sides survive', () => {
    const a = place<string>('a');
    const b = place<string>('b');

    const caller = Transition.builder('merged').inputs(one(a)).build();
    const instance = Transition.builder('instanceSide').inputs(one(b)).build();

    const merged = mergeTransitions(caller, instance, 'merged');

    expect(merged.inputSpecs.length).toBe(2);
    const inputPlaces = new Set([...merged.inputPlaces()].map((p) => p.name));
    expect(inputPlaces.has('a')).toBe(true);
    expect(inputPlaces.has('b')).toBe(true);
  });

  it('channelMerge_unionsInhibitorReadResetArcs: inhibitor + read + reset arcs from both sides survive', () => {
    const inh1 = place<string>('inh1');
    const inh2 = place<string>('inh2');
    const rd1 = place<string>('rd1');
    const rd2 = place<string>('rd2');
    const rs1 = place<string>('rs1');
    const rs2 = place<string>('rs2');

    const caller = Transition.builder('merged').inhibitor(inh1).read(rd1).reset(rs1).build();
    const instance = Transition.builder('instanceSide').inhibitor(inh2).read(rd2).reset(rs2).build();

    const merged = mergeTransitions(caller, instance, 'merged');

    expect(merged.inhibitors.length).toBe(2);
    expect(merged.reads.length).toBe(2);
    expect(merged.resets.length).toBe(2);
  });

  it('channelMerge_dedupesIdenticalArcs: identical arcs to same place collapse', () => {
    const shared = place<string>('shared');

    const caller = Transition.builder('merged').read(shared).build();
    const instance = Transition.builder('instanceSide').read(shared).build();

    const merged = mergeTransitions(caller, instance, 'merged');

    expect(merged.reads.length).toBe(1);
    const readPlaces = new Set([...merged.readPlaces()].map((p) => p.name));
    expect(readPlaces.has('shared')).toBe(true);
  });

  it('channelMerge_unionsOutputSpecs_intoAnd: both output places present', () => {
    const qCaller = place<string>('qCaller');
    const qInstance = place<string>('qInstance');

    const caller = Transition.builder('merged').outputs(outPlace(qCaller)).build();
    const instance = Transition.builder('instanceSide').outputs(outPlace(qInstance)).build();

    const merged = mergeTransitions(caller, instance, 'merged');

    expect(merged.outputSpec).not.toBeNull();
    // Outer wrap is OutAnd; the merge contract documents this explicitly.
    expect(merged.outputSpec!.type).toBe('and');
    const outNames = new Set([...merged.outputPlaces()].map((p) => p.name));
    expect(outNames.has('qCaller')).toBe(true);
    expect(outNames.has('qInstance')).toBe(true);
  });

  it('channelMerge_outputSpecsOnlyOneSide_thatSideWins', () => {
    const qCaller = place<string>('qCaller');

    const caller = Transition.builder('merged').outputs(outPlace(qCaller)).build();
    const instance = Transition.builder('instanceSide').build();

    const merged = mergeTransitions(caller, instance, 'merged');

    expect(merged.outputSpec).not.toBeNull();
    // Single-sided output flows through unwrapped (no extra OutAnd).
    expect(merged.outputSpec!.type).toBe('place');
    const outNames = new Set([...merged.outputPlaces()].map((p) => p.name));
    expect(outNames.has('qCaller')).toBe(true);
  });

  // ============================================================
  //  Identity, priority, timing
  // ============================================================

  it('channelMerge_callerSidePriorityWins: caller priority survives', () => {
    const caller = Transition.builder('merged').priority(5).build();
    const instance = Transition.builder('instanceSide').priority(10).build();

    const merged = mergeTransitions(caller, instance, 'merged');

    expect(merged.priority).toBe(5);
  });

  it('channelMerge_callerSideTimingWins_whenInstanceImmediate', () => {
    const caller = Transition.builder('merged').timing(delayed(50)).build();
    const instance = Transition.builder('instanceSide').timing(immediate()).build();

    const merged = mergeTransitions(caller, instance, 'merged');

    expect(merged.timing).toEqual(delayed(50));
  });

  it('channelMerge_instanceSideTimingWins_whenCallerImmediate', () => {
    const caller = Transition.builder('merged').timing(immediate()).build();
    const instance = Transition.builder('instanceSide').timing(delayed(75)).build();

    const merged = mergeTransitions(caller, instance, 'merged');

    expect(merged.timing).toEqual(delayed(75));
  });

  it('channelMerge_bothImmediate_resultImmediate', () => {
    const caller = Transition.builder('merged').timing(immediate()).build();
    const instance = Transition.builder('instanceSide').timing(immediate()).build();

    const merged = mergeTransitions(caller, instance, 'merged');

    expect(merged.timing.type).toBe('immediate');
  });

  it('channelMerge_equalNonImmediateTimings_collapse', () => {
    const caller = Transition.builder('merged').timing(delayed(50)).build();
    const instance = Transition.builder('instanceSide').timing(delayed(50)).build();

    const merged = mergeTransitions(caller, instance, 'merged');

    expect(merged.timing).toEqual(delayed(50));
  });

  it('channelMerge_conflictingTimings_throws: error names channel and both timings', () => {
    const caller = Transition.builder('merged').timing(delayed(50)).build();
    const instance = Transition.builder('instanceSide').timing(deadline(100)).build();

    let captured: Error | null = null;
    try {
      mergeTransitions(caller, instance, 'attempt');
    } catch (err) {
      captured = err as Error;
    }

    expect(captured).not.toBeNull();
    const msg = captured!.message;
    expect(msg).toContain('attempt');
    expect(msg).toContain('Delayed');
    expect(msg).toContain('Deadline');
  });

  // ============================================================
  //  Action composition
  // ============================================================

  it('channelMerge_actionsRunSequentially: caller action runs first, then instance action', async () => {
    const calls: string[] = [];

    const callerAction: TransitionAction = async () => {
      calls.push('caller');
    };
    const instanceAction: TransitionAction = async () => {
      calls.push('instance');
    };

    const caller = Transition.builder('merged').action(callerAction).build();
    const instance = Transition.builder('instanceSide').action(instanceAction).build();

    const merged = mergeTransitions(caller, instance, 'merged');

    await merged.action(ctxFor(merged));

    expect(calls).toEqual(['caller', 'instance']);
  });

  it('channelMerge_singleNullAction_noThrow: composeActions returns the non-undefined side by reference', async () => {
    let instanceCalls = 0;
    const instanceAction: TransitionAction = async () => {
      instanceCalls += 1;
    };

    // Drive composeActions directly — Transition.builder always defaults the
    // action to passthrough(), so this is the only way to exercise the
    // undefined branch.
    const composed = composeActions(undefined, instanceAction);
    expect(composed).toBe(instanceAction);

    const t = Transition.builder('t').build();
    await composed!(ctxFor(t));
    expect(instanceCalls).toBe(1);
  });

  it('channelMerge_bothNullAction_resultPassthrough: composeActions returns undefined; mergeTransitions leaves the builder default in place', async () => {
    const composed = composeActions(undefined, undefined);
    expect(composed).toBeUndefined();

    // mergeTransitions on two transitions whose actions are the singleton
    // passthrough should also collapse to passthrough — i.e., the merged
    // transition's `action` IS the passthrough singleton.
    const caller = Transition.builder('merged').build();
    const instance = Transition.builder('instanceSide').build();
    const merged = mergeTransitions(caller, instance, 'merged');
    expect(merged.action).toBe(passthrough());

    // And it must be safely callable end-to-end without throwing.
    await merged.action(ctxFor(merged));
  });

  // ============================================================
  //  End-to-end with the retryPolicy fixture (MOD-021 + EXEC-001)
  // ============================================================

  it('channelMerge_endToEnd_retryPolicy: firing the host transition also runs the retry-policy logic atomically', async () => {
    // The retry-policy subnet exposes one channel "attempt"; binding it to
    // the host's "attemptHttp" transition fuses both sides — firing the host
    // transition also runs the retry-policy logic.
    const retryDef = retryPolicy();

    // Bind an instance-side action that increments a counter when the
    // channel fires — i.e., the per-attempt retry-policy hook.
    let attemptCount = 0;
    const attemptAction: TransitionAction = async (ctx) => {
      attemptCount += 1;
      // The instance-side transition's output spec emits to attemptCount;
      // produce a synthetic value so the merged firing is well-formed.
      for (const op of ctx.outputPlaces()) {
        if (op.name.endsWith('/attemptCount')) {
          ctx.output(op as Place<string>, 'tick');
        }
      }
    };
    const retryInst = retryDef.instantiate('rp').bindActions({ attempt: attemptAction });

    // Host net: a "trigger" place enables an "attemptHttp" transition.
    const trigger = place<string>('trigger');
    const hostResult = place<string>('hostResult');

    let hostCalls = 0;
    const hostAction: TransitionAction = async (ctx) => {
      hostCalls += 1;
      for (const op of ctx.outputPlaces()) {
        if (op.name === 'hostResult') {
          ctx.output(op as Place<string>, 'ok');
        }
      }
    };
    const attemptHttp = Transition.builder('attemptHttp')
      .inputs(one(trigger))
      .outputs(outPlace(hostResult))
      .action(hostAction)
      .build();

    const host = PetriNet.builder('HostWithRetry')
      .compose(retryInst, (b) => b.bindChannel('attempt', attemptHttp))
      .build();

    // After compose, the host net contains the merged "attemptHttp"
    // transition (caller-wins identity) and NOT the renamed "rp/attempt".
    const tNames = new Set([...host.transitions].map((t) => t.name));
    expect(tNames.has('rp/attempt')).toBe(false);
    expect(tNames.has('attemptHttp')).toBe(true);

    // Resolve the renamed instance-side internal place so we can observe
    // the increment via the executor's marking.
    const attemptCountPlace = [...host.places].find((p) => p.name === 'rp/attemptCount');
    expect(attemptCountPlace).not.toBeUndefined();

    const initial = new Map<Place<unknown>, Token<unknown>[]>();
    initial.set(trigger as Place<unknown>, [tokenOf('go')] as Token<unknown>[]);
    const executor = new BitmapNetExecutor(host, initial as Map<Place<any>, Token<any>[]>);
    const finalMarking = await executor.run(2000);

    // The merged transition fires once for the single trigger token — both
    // the host action and the instance-side action increment.
    expect(hostCalls).toBe(1);
    expect(attemptCount).toBe(1);

    // Tokens land in both the host's result place and the retry-policy's
    // attemptCount sink.
    expect(finalMarking.hasTokens(hostResult)).toBe(true);
    expect(finalMarking.hasTokens(attemptCountPlace as Place<string>)).toBe(true);
  });
});

describe('SubnetRewriter.mergeTransitions — ν-net match + declared→actual alias (NU-060 / MOD-031)', () => {
  const cidKey = (a: Place<string>, b: Place<string>) =>
    matchSpec(matchKey(a, (s: string) => nameId(s)), matchKey(b, (s: string) => nameId(s)));

  it('channelMerge_carriesOneSidedMatchSpec: caller-side ν-net match survives the merge', () => {
    const a = place<string>('branchA');
    const b = place<string>('branchB');
    const caller = Transition.builder('join').inputs(one(a), one(b)).match(cidKey(a, b)).build();
    const instance = Transition.builder('instanceSide').build();

    const merged = mergeTransitions(caller, instance, 'join');

    expect(merged.matchSpec).not.toBeNull();
    expect(merged.matchSpec!.keys.map((k) => k.place.name).sort()).toEqual(['branchA', 'branchB']);
  });

  it('channelMerge_carriesInstanceSideMatchSpec: instance-side ν-net match survives the merge', () => {
    const a = place<string>('branchA');
    const b = place<string>('branchB');
    const caller = Transition.builder('join').build();
    const instance = Transition.builder('instanceSide').inputs(one(a), one(b)).match(cidKey(a, b)).build();

    const merged = mergeTransitions(caller, instance, 'join');

    expect(merged.matchSpec).not.toBeNull();
    expect(merged.matchSpec!.keys.map((k) => k.place.name).sort()).toEqual(['branchA', 'branchB']);
  });

  it('channelMerge_bothSidesCarryMatch_throws: NU-060 rejects fusing two correlations', () => {
    const a = place<string>('branchA');
    const b = place<string>('branchB');
    const c = place<string>('branchC');
    const d = place<string>('branchD');
    const caller = Transition.builder('join').inputs(one(a), one(b)).match(cidKey(a, b)).build();
    const instance = Transition.builder('instanceSide').inputs(one(c), one(d)).match(cidKey(c, d)).build();

    expect(() => mergeTransitions(caller, instance, 'attempt')).toThrow('NU-060');
    expect(() => mergeTransitions(caller, instance, 'attempt')).toThrow('attempt');
  });

  it('channelMerge_carriesPlaceAliasFromBothSides: MOD-031 declared→actual alias unioned', () => {
    const actualA = place<string>('host/actualA');
    const actualB = place<string>('host/actualB');
    const caller = Transition.builder('merged')
      .placeAlias(new Map<string, Place<any>>([['declaredA', actualA]]))
      .build();
    const instance = Transition.builder('instanceSide')
      .placeAlias(new Map<string, Place<any>>([['declaredB', actualB]]))
      .build();

    const merged = mergeTransitions(caller, instance, 'merged');

    expect(merged.placeAlias.get('declaredA')?.name).toBe('host/actualA');
    expect(merged.placeAlias.get('declaredB')?.name).toBe('host/actualB');
  });

  it('channelMerge_conflictingPlaceAlias_throws: MOD-031 same-declared different-actual rejected', () => {
    // Same declared local name bound to two different actual places across the
    // two fused sides — an ambiguous MOD-031 correspondence, rejected.
    const actualA = place<string>('host/a');
    const actualB = place<string>('host/b');
    const caller = Transition.builder('merged')
      .placeAlias(new Map<string, Place<any>>([['declaredX', actualA]]))
      .build();
    const instance = Transition.builder('instanceSide')
      .placeAlias(new Map<string, Place<any>>([['declaredX', actualB]]))
      .build();

    expect(() => mergeTransitions(caller, instance, 'attempt')).toThrow('MOD-031');
    expect(() => mergeTransitions(caller, instance, 'attempt')).toThrow('attempt');
  });

  it('channelMerge_mergedMatchJoin_correlatesByName_notFifo: behavioral regression', async () => {
    // The reported production symptom: a matched join fused through the merge
    // path must still pair tokens by name — not by FIFO arrival order.
    const a = place<string>('branchA');
    const b = place<string>('branchB');
    const out = place<string>('merged');

    const caller = Transition.builder('join')
      .inputs(one(a), one(b))
      .match(cidKey(a, b))
      .outputs(outPlace(out))
      .action(async (ctx) => {
        ctx.output(out, `${ctx.input(a)}+${ctx.input(b)}`);
      })
      .build();
    const instance = Transition.builder('instanceSide').build();

    const merged = mergeTransitions(caller, instance, 'join');
    const net = PetriNet.builder('mergedNuJoin').transition(merged).build();

    // Interleaved timestamps: FIFO would cross-pair (X+Y / Y+X); a live match
    // yields the correlated X+X / Y+Y.
    const tokens = new Map<Place<any>, Token<any>[]>([
      [a, [tokenAt('X', 0), tokenAt('Y', 1)]],
      [b, [tokenAt('Y', 0), tokenAt('X', 1)]],
    ]);

    const marking = await new BitmapNetExecutor(net, tokens).run(2000);
    const vals = [...marking.peekTokens(out)].map((t) => t.value as string).sort();
    expect(vals).toEqual(['X+X', 'Y+Y']);
  });
});
