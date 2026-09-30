package org.libpetri.smt;

import org.libpetri.core.Arc;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Timing;
import org.libpetri.core.Transition;
import org.libpetri.core.internal.CodePointOrder;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.TreeSet;

/**
 * Deadline reaping and late firing in the verifier ([VER-002], [VER-004], [TIME-006], [TIME-013]).
 *
 * <p>A {@code deadline} / {@code window} transition still enabled past {@code latest} plus the
 * executor's tolerance is <em>reaped</em>: the executor clears its enabled bit, emits
 * {@code TransitionTimedOut} and leaves its input tokens where they are. It is not re-enabled
 * until a token on one of its input places changes, so an executor that fell behind can come to
 * rest at a marking the untimed net still enables. Lean: {@code Libpetri/Novel/ReapingVsUntimed.lean},
 * {@code reaping_refutes_ver004_ac3} (the witness {@code p0 → t → p1}, {@code t = window(3, 5)},
 * which rests at {@code {p0}}).
 *
 * <p>Reaping never changes the marking, so the marking properties keep their untimed verdicts on
 * the untimed routes. What it changes is where a run can rest. A transition is <em>reapable</em>
 * iff its timing is {@code Deadline} or {@code Window}; a marking is <em>reap-quiescent</em> iff
 * every transition it enables is reapable (plain quiescence, none enabled, is the special case).
 * Every quiescence property reads reap-quiescence on every route.
 *
 * <p>A late executor also fires late: it reaps a deadline / window transition and fires an
 * {@code exact} one after its bound. So Route B, the timed graph that can return {@code Proven},
 * is built on {@link #relaxLate}'s net, in which no transition has a latest bound (Lean:
 * {@code TimedScg/Late.relax}, {@code late_run_sound}), for every property.
 *
 * <p>{@link SmtVerifier#assumeNoReaping(boolean)} opts out of both and assumes an <em>on-time
 * executor</em>: no transition is reaped and none fires after its latest bound. A net timed only
 * with {@code immediate} and {@code delayed} verifies identically either way. Mirrors Rust's
 * {@code reaping.rs} and TypeScript's {@code reaping.ts}.
 */
public final class Reaping {

    private Reaping() {}

    /** Whether a transition with this timing can be reaped: {@code Deadline} and {@code Window} ([TIME-013]). */
    public static boolean isReapable(Timing timing) {
        return timing instanceof Timing.Deadline || timing instanceof Timing.Window;
    }

    /** The names of the net's reapable transitions, in net order. */
    public static Set<String> reapableTransitions(PetriNet net) {
        var names = new LinkedHashSet<String>();
        for (var t : net.transitions()) {
            if (isReapable(t.timing())) {
                names.add(t.name());
            }
        }
        return names;
    }

    /** Whether this timing has a finite latest bound: {@code Deadline}, {@code Window} and {@code Exact} ([TIME-006], [TIME-013]). */
    public static boolean hasLatestBound(Timing timing) {
        return timing.hasDeadline();
    }

    /** The names of the net's transitions with a finite latest bound, in net order. */
    public static Set<String> lateTransitions(PetriNet net) {
        var names = new LinkedHashSet<String>();
        for (var t : net.transitions()) {
            if (hasLatestBound(t.timing())) {
                names.add(t.name());
            }
        }
        return names;
    }

    /**
     * {@code net} with the latest bound of every transition named in {@code late} dropped, the
     * earliest kept: {@code deadline(by)} becomes {@code immediate()}, {@code window(e, l)} becomes
     * {@code delayed(e)} and {@code exact(a)} becomes {@code delayed(a)} ({@code immediate()} when
     * the earliest is 0). The same net when nothing changes. Lean: {@code TimedScg/Late.relax}.
     *
     * <p>A timed graph fires an enabled transition by its latest bound (strong semantics), so it
     * never holds a run that fires something else after that bound while the transition stays
     * enabled. A late executor reaps a deadline / window transition, or fires an exact one after its
     * bound, and does. Dropping the bound puts those runs in the graph; a reaped transition that
     * still fires there only adds runs.
     */
    public static PetriNet relaxLate(PetriNet net, Set<String> late) {
        if (net.transitions().stream().noneMatch(t -> late.contains(t.name()) && hasLatestBound(t.timing()))) {
            return net;
        }
        var transitions = new ArrayList<Transition>(net.transitions().size());
        for (var t : net.transitions()) {
            if (!late.contains(t.name()) || !hasLatestBound(t.timing())) {
                transitions.add(t);
                continue;
            }
            var earliest = t.timing().earliest();
            transitions.add(withTiming(t, earliest.isZero() ? Timing.immediate() : Timing.delayed(earliest)));
        }
        var relaxed = PetriNet.builder(net.name())
            .places(net.places().toArray(new Place<?>[0]))
            .transitions(transitions.toArray(new Transition[0]));
        net.terminals().forEach(relaxed::terminal);
        return relaxed.build();
    }

    /** {@code t} with {@code timing}; every arc, the priority, the action and the alias map carried. */
    private static Transition withTiming(Transition t, Timing timing) {
        var b = Transition.builder(t.name())
            .timing(timing)
            .priority(t.priority())
            .action(t.action())
            .placeAlias(t.placeAlias())
            .match(t.matchSpec());
        if (!t.inputSpecs().isEmpty()) {
            b.inputs(t.inputSpecs().toArray(new Arc.In[0]));
        }
        if (t.outputSpec() != null) {
            b.outputs(t.outputSpec());
        }
        t.inhibitors().forEach(b::inhibitorArc);
        t.reads().forEach(b::readArc);
        t.resets().forEach(b::resetArc);
        return b.build();
    }

    private static String joined(Set<String> names) {
        var sorted = new TreeSet<String>(CodePointOrder.COMPARATOR);
        sorted.addAll(names);
        return String.join(", ", sorted);
    }

    /** The report line of a quiescence verdict on a net with reapable transitions, read reap-aware. */
    public static String reapAwareNote(Set<String> reapable) {
        return "Reaping (TIME-013): " + joined(reapable) + " can be reaped, so a marking where only "
            + (reapable.size() == 1 ? "it is" : "they are")
            + " enabled counts as quiescent (VER-002); the assume-no-reaping option reads it strictly.";
    }

    /**
     * The report line of a verdict reached under {@code assumeNoReaping} on a net with a transition
     * a late executor treats differently: the on-time executor the verdict rests on. {@code late}
     * names the reapable transitions and those with a latest bound.
     */
    public static String noReapingAssumptionNote(Set<String> late) {
        return "ASSUMPTION: no transition is reaped (the assume-no-reaping option) and none fires after its "
            + "latest bound, i.e. an on-time executor. A late executor can reap or fire late " + joined(late)
            + " (TIME-006, TIME-013); this verdict holds only for runs in which it does neither.";
    }

    /**
     * {@link #noReapingAssumptionNote} for a verdict Route B reached: Route B keeps the latest
     * bounds and reads each firing as one instant step, so the verdict also assumes that an
     * action takes no time ([VER-004]).
     */
    public static String noReapingRouteBNote(Set<String> late) {
        return "ASSUMPTION: no transition is reaped (the assume-no-reaping option), none fires after its "
            + "latest bound, and an action takes no time, i.e. an on-time executor with atomic firings. "
            + "Route B keeps the latest bound of " + joined(late) + " and reads each firing as one instant "
            + "step: a late executor can reap or fire late (TIME-006, TIME-013), and an action that runs "
            + "while a bound passes lets other transitions fire before its outputs land (VER-004); this "
            + "verdict holds only for runs in which none of this happens.";
    }
}
