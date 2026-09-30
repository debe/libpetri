/**
 * @module reaping
 *
 * Deadline reaping and late firing in the verifier ([VER-002], [VER-004], [TIME-006],
 * [TIME-013]).
 *
 * A `deadline` / `window` transition still enabled past `latest` plus the executor's
 * tolerance is **reaped**: the executor clears its enabled bit, emits `TransitionTimedOut`
 * and leaves its input tokens where they are. It is not re-enabled until a token on one of
 * its input places changes, so an executor that fell behind can come to rest at a marking
 * the untimed net still enables. Lean: `Libpetri/Novel/ReapingVsUntimed.lean`,
 * `reaping_refutes_ver004_ac3` (the witness `p0 → t → p1`, `t = window(3, 5)`, which rests
 * at `{p0}`).
 *
 * Reaping never changes the marking, so the marking properties keep their untimed verdicts
 * on the untimed routes. What it changes is where a run can rest. A transition is
 * **reapable** iff its timing is `deadline` or `window`; a marking is **reap-quiescent** iff
 * every transition it enables is reapable (plain quiescence, none enabled, is the special
 * case). Every quiescence property reads reap-quiescence on every route.
 *
 * A late executor also fires late: it reaps a deadline / window transition and fires an
 * `exact` one after its bound. So Route B, the timed graph that can return `proven`, is built
 * on `relaxLate`'s net, in which no transition has a latest bound (Lean: `TimedScg/Late.relax`,
 * `late_run_sound`), for every property.
 *
 * `assumeNoReaping` opts out of both and assumes an **on-time executor**: no transition is
 * reaped and none fires after its latest bound. A net timed only with `immediate` and
 * `delayed` verifies identically either way. Mirrors Rust's `reaping.rs` and Java's `Reaping`.
 */
import { PetriNet } from '../core/petri-net.js';
import { Transition } from '../core/transition.js';
import { delayed, earliest, hasDeadline, immediate, type Timing } from '../core/timing.js';
import { compareCodePoints } from '../core/internal/code-point-order.js';

/** Whether a transition with this timing can be reaped: `deadline` and `window` ([TIME-013]). */
export function isReapable(timing: Timing): boolean {
  return timing.type === 'deadline' || timing.type === 'window';
}

/** The names of the net's reapable transitions. */
export function reapableTransitions(net: PetriNet): Set<string> {
  const names = new Set<string>();
  for (const t of net.transitions) if (isReapable(t.timing)) names.add(t.name);
  return names;
}

/** Whether this timing has a finite latest bound: `deadline`, `window` and `exact` ([TIME-006], [TIME-013]). */
export function hasLatestBound(timing: Timing): boolean {
  return hasDeadline(timing);
}

/** The names of the net's transitions with a finite latest bound. */
export function lateTransitions(net: PetriNet): Set<string> {
  const names = new Set<string>();
  for (const t of net.transitions) if (hasLatestBound(t.timing)) names.add(t.name);
  return names;
}

/**
 * `net` with the latest bound of every transition named in `late` dropped, the earliest kept:
 * `deadline(by)` becomes `immediate()`, `window(e, l)` becomes `delayed(e)` and `exact(a)`
 * becomes `delayed(a)` (`immediate()` when the earliest is 0). The same net when nothing
 * changes. Lean: `TimedScg/Late.relax`.
 *
 * A timed graph fires an enabled transition by its latest bound (strong semantics), so it
 * never holds a run that fires something else after that bound while the transition stays
 * enabled. A late executor reaps a deadline / window transition, or fires an exact one after
 * its bound, and does. Dropping the bound puts those runs in the graph; a reaped transition
 * that still fires there only adds runs.
 */
export function relaxLate(net: PetriNet, late: ReadonlySet<string>): PetriNet {
  if (![...net.transitions].some(t => late.has(t.name) && hasLatestBound(t.timing))) return net;
  const transitions = [...net.transitions].map(t => {
    if (!late.has(t.name) || !hasLatestBound(t.timing)) return t;
    const e = earliest(t.timing);
    return withTiming(t, e === 0 ? immediate() : delayed(e));
  });
  return PetriNet.builder(net.name).places(...net.places).transitions(...transitions)
    .terminals(...net.terminals)
    .build();
}

/** `t` with `timing`; every arc, the priority, the action and the alias map carried. */
function withTiming(t: Transition, timing: Timing): Transition {
  const b = Transition.builder(t.name).timing(timing).priority(t.priority).action(t.action);
  if (t.placeAlias.size > 0) b.placeAlias(t.placeAlias);
  if (t.inputSpecs.length > 0) b.inputs(...t.inputSpecs);
  if (t.outputSpec !== null) b.outputs(t.outputSpec);
  for (const arc of t.inhibitors) b.inhibitor(arc.place);
  for (const arc of t.reads) b.read(arc.place);
  for (const arc of t.resets) b.reset(arc.place);
  if (t.matchSpec !== null) b.match(t.matchSpec);
  return b.build();
}

function joined(names: ReadonlySet<string>): string {
  return [...names].sort(compareCodePoints).join(', ');
}

/** The report line of a quiescence verdict on a net with reapable transitions, read reap-aware. */
export function reapAwareNote(reapable: ReadonlySet<string>): string {
  return `Reaping (TIME-013): ${joined(reapable)} can be reaped, so a marking where only `
    + `${reapable.size === 1 ? 'it is' : 'they are'} enabled counts as quiescent (VER-002); `
    + 'the assume-no-reaping option reads it strictly.\n';
}

/**
 * The report line of a verdict reached under `assumeNoReaping` on a net with a transition a late
 * executor treats differently: the on-time executor the verdict rests on. `late` names the
 * reapable transitions and those with a latest bound.
 */
export function noReapingAssumptionNote(late: ReadonlySet<string>): string {
  return 'ASSUMPTION: no transition is reaped (the assume-no-reaping option) and none fires after its '
    + `latest bound, i.e. an on-time executor. A late executor can reap or fire late ${joined(late)} `
    + '(TIME-006, TIME-013); this verdict holds only for runs in which it does neither.\n';
}

/**
 * {@link noReapingAssumptionNote} for a verdict Route B reached ([NU-050]). Route B is the one
 * route that keeps timing, and with the latest bounds kept its graph reads each firing as one
 * instant step: an action that runs while a bound passes lets other transitions fire before its
 * outputs land, which the graph does not hold ([VER-004]).
 */
export function noReapingRouteBNote(late: ReadonlySet<string>): string {
  return 'ASSUMPTION: no transition is reaped (the assume-no-reaping option), none fires after its '
    + 'latest bound, and an action takes no time, i.e. an on-time executor with atomic firings. '
    + `Route B keeps the latest bound of ${joined(late)} and reads each firing as one instant step: a late `
    + 'executor can reap or fire late (TIME-006, TIME-013), and an action that runs while a '
    + 'bound passes lets other transitions fire before its outputs land (VER-004); this verdict '
    + 'holds only for runs in which none of this happens.\n';
}
