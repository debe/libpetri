package org.libpetri.smt.z3;

import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.EnvironmentPlace;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.smt.SmtProperty;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.encoding.NetFlattener;
import org.libpetri.smt.z3.StateEquationQuery.MarkingInequality;
import org.libpetri.smt.z3.StateEquationQuery.Origin;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Predicate;

/**
 * The nets of {@code typescript/tests/verification/state-equation-phase.test.ts} ([VER-018]
 * test derivation), built the same way, so the Java building-block tests assert on the same
 * flat nets the TypeScript and Rust tests do. Public so the verifier-level tests in
 * {@code org.libpetri.smt} run the phases on these nets too. The transitions carry no action:
 * a verifier test binds them ({@code StructureOnly.bind}), as [CORE-043] requires.
 */
public final class StateEquationNets {

    private StateEquationNets() {}

    public static Place<String> place(String name) {
        return Place.of(name, String.class);
    }

    public static FlatNet flatten(PetriNet net) {
        return NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.alwaysAvailable());
    }

    /**
     * The join of a compiled workflow: {@code route} sends data down one arm and an empty
     * marker down the other; a data arm writes {@code hasdata} with its {@code ready}, an empty
     * arm {@code ready} alone; {@code mergeStart} takes both readies with {@code all(hasdata)},
     * {@code mergeSkip} both readies under {@code inhibitor(hasdata)}. The marking equation
     * admits {@code mergeSkip} firing after a data token arrived, stranding {@code hasdata};
     * only the inhibitor rules that out. Flat places: aData, aEmpty, bData, bEmpty, done,
     * hasdata, ready0, ready1, skipped, start.
     */
    public record JoinWithSkip(PetriNet net, MarkingState m0, Place<String> done, Place<String> skipped) {
        public FlatNet flat() {
            return flatten(net);
        }
    }

    public static JoinWithSkip joinWithSkip() {
        var start = place("start");
        var aData = place("aData");
        var aEmpty = place("aEmpty");
        var bData = place("bData");
        var bEmpty = place("bEmpty");
        var hasdata = place("hasdata");
        var ready0 = place("ready0");
        var ready1 = place("ready1");
        var done = place("done");
        var skipped = place("skipped");
        var net = PetriNet.builder("joinWithSkip").transitions(
            Transition.builder("route").inputs(In.one(start))
                .outputs(Out.xor(Out.and(aData, bEmpty), Out.and(aEmpty, bData))).build(),
            Transition.builder("armAData").inputs(In.one(aData)).outputs(Out.and(hasdata, ready0)).build(),
            Transition.builder("armAEmpty").inputs(In.one(aEmpty)).outputs(Out.place(ready0)).build(),
            Transition.builder("armBData").inputs(In.one(bData)).outputs(Out.and(hasdata, ready1)).build(),
            Transition.builder("armBEmpty").inputs(In.one(bEmpty)).outputs(Out.place(ready1)).build(),
            Transition.builder("mergeStart").inputs(In.one(ready0), In.one(ready1), In.all(hasdata))
                .outputs(Out.place(done)).build(),
            Transition.builder("mergeSkip").inputs(In.one(ready0), In.one(ready1)).inhibitors(hasdata)
                .outputs(Out.place(skipped)).build()
        ).build();
        return new JoinWithSkip(net, MarkingState.builder().tokens(start, 1).build(), done, skipped);
    }

    /**
     * The queue-and-bundle net: a producer fires up to {@code n} times into {@code q} until the
     * signal arrives, and the bundler takes {@code all(q)} with the signal ({@code bundleEmpty}
     * takes the signal alone when the queue is empty). Cancellable: the signal may never come.
     * Flat places: budget, (cancelled,) out, q, s, src.
     */
    public record QueueAndBundle(PetriNet net, MarkingState m0, Place<String> q, Place<String> out,
                                 Place<String> budget, Place<String> cancelled) {
        public FlatNet flat() {
            return flatten(net);
        }

        /** The declared sinks: out and budget, and cancelled on the cancellable net. */
        public Set<Place<?>> sinks(boolean cancellable) {
            var sinks = new LinkedHashSet<Place<?>>(List.of(out, budget));
            if (cancellable) {
                sinks.add(cancelled);
            }
            return sinks;
        }
    }

    public static QueueAndBundle queueAndBundle(int n, boolean cancellable) {
        var budget = place("budget");
        var q = place("q");
        var src = place("src");
        var s = place("s");
        var out = place("out");
        var cancelled = place("cancelled");
        var transitions = new ArrayList<Transition>(List.of(
            Transition.builder("produce").inputs(In.one(budget)).inhibitors(s, out).outputs(Out.place(q)).build(),
            Transition.builder("signal").inputs(In.one(src)).outputs(Out.place(s)).build(),
            Transition.builder("bundle").inputs(In.all(q), In.one(s)).outputs(Out.place(out)).build(),
            Transition.builder("bundleEmpty").inputs(In.one(s)).inhibitors(q).outputs(Out.place(out)).build()));
        if (cancellable) {
            transitions.add(Transition.builder("cancel").inputs(In.one(src)).outputs(Out.place(cancelled)).build());
        }
        var net = PetriNet.builder("queue" + n).transitions(transitions.toArray(new Transition[0])).build();
        var m0 = MarkingState.builder().tokens(budget, n).tokens(src, 1).build();
        return new QueueAndBundle(net, m0, q, out, budget, cancelled);
    }

    /**
     * {@code gatedStrand} strands {@code q} behind a gate that never opens. The net is the same
     * either way; only whether {@code sig} is declared an environment place differs, so two
     * searches over it differ in injection and in nothing else. Flat places: done, gateOpen, q,
     * sig, start.
     */
    record GatedStrand(FlatNet flat, int[] initial, Predicate<int[]> bad) {
        /** {@code fill} may fire {@code fill} times, {@code gate} never. */
        long[] counts(long fill) {
            return flat.transitions().stream().mapToLong(ft -> ft.name().equals("fill") ? fill : 0).toArray();
        }
    }

    static GatedStrand gatedStrand(boolean injectable) {
        var start = place("start");
        var q = place("q");
        var gateOpen = place("gateOpen");
        var done = place("done");
        var sig = EnvironmentPlace.of(place("sig"));
        var net = PetriNet.builder("gated").transitions(
            Transition.builder("fill").inputs(In.one(start)).outputs(Out.place(q)).build(),
            Transition.builder("gate").inputs(In.one(sig.place()), In.one(gateOpen)).outputs(Out.place(done)).build()
        ).build();
        var m0 = MarkingState.builder().tokens(start, 1).build();
        var flat = NetFlattener.flatten(net, injectable ? Set.of(sig) : Set.of(),
            EnvironmentAnalysisMode.alwaysAvailable());
        Set<Place<?>> sinks = Set.of(done);
        return new GatedStrand(flat, AbstractReplayer.toVector(flat, m0),
            state -> AbstractReplayer.violates(flat, SmtProperty.deadlockFree(), sinks, state));
    }

    /** The flat index of the place named {@code name}. */
    static int indexOf(FlatNet flat, String name) {
        for (int i = 0; i < flat.placeCount(); i++) {
            if (flat.places().get(i).name().equals(name)) {
                return i;
            }
        }
        throw new IllegalArgumentException("no place " + name);
    }

    /** A marking over the flat places from {@code name, count} pairs, zero elsewhere. */
    static int[] marking(FlatNet flat, Object... nameCounts) {
        int[] m = new int[flat.placeCount()];
        for (int i = 0; i < nameCounts.length; i += 2) {
            m[indexOf(flat, (String) nameCounts[i])] = (Integer) nameCounts[i + 1];
        }
        return m;
    }

    /** {@link #marking} as a candidate marking. */
    static long[] candidate(FlatNet flat, Object... nameCounts) {
        return Arrays.stream(marking(flat, nameCounts)).asLongStream().toArray();
    }

    /** {@code Σ weight·m_name <= constant} from {@code name, weight} pairs, origin inductive. */
    static MarkingInequality inequality(FlatNet flat, int constant, Object... nameWeights) {
        var weights = new BigInteger[flat.placeCount()];
        Arrays.fill(weights, BigInteger.ZERO);
        for (int i = 0; i < nameWeights.length; i += 2) {
            weights[indexOf(flat, (String) nameWeights[i])] = BigInteger.valueOf((Integer) nameWeights[i + 1]);
        }
        return new MarkingInequality(Arrays.asList(weights), BigInteger.valueOf(constant), Origin.INDUCTIVE);
    }
}
