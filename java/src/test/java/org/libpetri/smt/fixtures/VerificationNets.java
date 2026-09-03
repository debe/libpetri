package org.libpetri.smt.fixtures;

import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.EnvironmentPlace;
import org.libpetri.core.MatchSpec;
import org.libpetri.core.NameId;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.fixtures.StructureOnly;

import java.util.Set;

/**
 * Factory for the cross-language verdict-parity nets (C4), one builder per
 * {@code net} name in {@code spec/verification-fixtures/fixtures.json}.
 *
 * <p>Each builder implements that file's {@code netDescription} — the normative
 * builder contract shared by every language — in {@code PaperNetworks} style.
 * All places are {@code String}-typed, so a property place referenced by name in
 * the JSON resolves via {@code Place.of(name, String.class)} (Place is a record;
 * equality is structural on name and token type).
 *
 * <p>The nets are structure-only: they are verified, never executed
 * ({@link StructureOnly}).
 */
public final class VerificationNets {

    private VerificationNets() {}

    /**
     * A named net with everything the verifier needs besides the property.
     *
     * @param net               the structure-only net
     * @param initialMarking    the fixture's initial marking
     * @param environmentPlaces environment places to declare (empty for closed nets)
     * @param environmentMode   the environment analysis mode for those places
     */
    public record NamedNet(
        PetriNet net,
        MarkingState initialMarking,
        Set<EnvironmentPlace<?>> environmentPlaces,
        EnvironmentAnalysisMode environmentMode
    ) {}

    /** Resolves a fixture's {@code net} name to its builder. */
    public static NamedNet build(String name) {
        return switch (name) {
            case "circularChain" -> circularChain();
            case "deadEndChain" -> deadEndChain();
            case "mutexLocked" -> mutexLocked();
            case "mutexUnlocked" -> mutexUnlocked();
            case "conservedPair" -> conservedPair();
            case "envSingleFeed" -> envSingleFeed();
            case "inhibitorFrozen" -> inhibitorFrozen();
            case "h1ConsumeAll" -> h1ConsumeAll();
            case "atLeastDrain" -> atLeastDrain();
            case "sinkPartialTerminal" -> sinkPartialTerminal();
            case "sinkDrainedTerminal" -> sinkDrainedTerminal();
            case "nuMixedTerminal" -> nuMixedTerminal();
            case "nuDrainedTerminal" -> nuDrainedTerminal();
            case "nuScatterGather" -> nuScatterGather();
            default -> throw new IllegalArgumentException("unknown fixture net: " + name);
        };
    }

    private static Place<String> place(String name) {
        return Place.of(name, String.class);
    }

    private static NamedNet closed(PetriNet net, MarkingState initialMarking) {
        return new NamedNet(
            StructureOnly.bind(net), initialMarking, Set.of(), EnvironmentAnalysisMode.ignore());
    }

    /**
     * {@code p0(1),p1,p2; t01: one(p0)->p1; t12: one(p1)->p2; t20: one(p2)->p0}.
     * The token circulates forever — deadlock-free.
     */
    public static NamedNet circularChain() {
        var p0 = place("p0");
        var p1 = place("p1");
        var p2 = place("p2");
        var t01 = Transition.builder("t01").inputs(In.one(p0)).outputs(Out.place(p1)).build();
        var t12 = Transition.builder("t12").inputs(In.one(p1)).outputs(Out.place(p2)).build();
        var t20 = Transition.builder("t20").inputs(In.one(p2)).outputs(Out.place(p0)).build();
        return closed(
            PetriNet.builder("circularChain").transitions(t01, t12, t20).build(),
            MarkingState.builder().tokens(p0, 1).build());
    }

    /**
     * {@code p0(1),p1,p2; t01: one(p0)->p1; t12: one(p1)->p2}. After t12 fires
     * nothing is enabled; p2 is a normal place (not a declared sink), so the
     * quiescent marking is a genuine deadlock.
     */
    public static NamedNet deadEndChain() {
        var p0 = place("p0");
        var p1 = place("p1");
        var p2 = place("p2");
        var t01 = Transition.builder("t01").inputs(In.one(p0)).outputs(Out.place(p1)).build();
        var t12 = Transition.builder("t12").inputs(In.one(p1)).outputs(Out.place(p2)).build();
        return closed(
            PetriNet.builder("deadEndChain").transitions(t01, t12).build(),
            MarkingState.builder().tokens(p0, 1).build());
    }

    /**
     * {@code idle1(1),idle2(1),lock(1),crit1,crit2}; enter consumes idle+lock,
     * exit returns both. The binary semaphore guarantees mutual exclusion.
     */
    public static NamedNet mutexLocked() {
        var idle1 = place("idle1");
        var idle2 = place("idle2");
        var lock = place("lock");
        var crit1 = place("crit1");
        var crit2 = place("crit2");
        var enter1 = Transition.builder("enter1")
            .inputs(In.one(idle1), In.one(lock)).outputs(Out.place(crit1)).build();
        var exit1 = Transition.builder("exit1")
            .inputs(In.one(crit1)).outputs(Out.and(idle1, lock)).build();
        var enter2 = Transition.builder("enter2")
            .inputs(In.one(idle2), In.one(lock)).outputs(Out.place(crit2)).build();
        var exit2 = Transition.builder("exit2")
            .inputs(In.one(crit2)).outputs(Out.and(idle2, lock)).build();
        return closed(
            PetriNet.builder("mutexLocked").transitions(enter1, exit1, enter2, exit2).build(),
            MarkingState.builder().tokens(idle1, 1).tokens(idle2, 1).tokens(lock, 1).build());
    }

    /**
     * Same as {@link #mutexLocked()} but enter1/enter2 do NOT consume lock (the
     * lock place is omitted entirely) — both criticals are reachable together.
     */
    public static NamedNet mutexUnlocked() {
        var idle1 = place("idle1");
        var idle2 = place("idle2");
        var crit1 = place("crit1");
        var crit2 = place("crit2");
        var enter1 = Transition.builder("enter1")
            .inputs(In.one(idle1)).outputs(Out.place(crit1)).build();
        var exit1 = Transition.builder("exit1")
            .inputs(In.one(crit1)).outputs(Out.place(idle1)).build();
        var enter2 = Transition.builder("enter2")
            .inputs(In.one(idle2)).outputs(Out.place(crit2)).build();
        var exit2 = Transition.builder("exit2")
            .inputs(In.one(crit2)).outputs(Out.place(idle2)).build();
        return closed(
            PetriNet.builder("mutexUnlocked").transitions(enter1, exit1, enter2, exit2).build(),
            MarkingState.builder().tokens(idle1, 1).tokens(idle2, 1).build());
    }

    /**
     * {@code p0(3),p1; t: one(p0)->p1}. Conservation {@code p0+p1=3}: the
     * bound-3 proof needs the P-invariant strengthening, exercising the
     * R'-candidate certificate check.
     */
    public static NamedNet conservedPair() {
        var p0 = place("p0");
        var p1 = place("p1");
        var t = Transition.builder("t").inputs(In.one(p0)).outputs(Out.place(p1)).build();
        return closed(
            PetriNet.builder("conservedPair").transitions(t).build(),
            MarkingState.builder().tokens(p0, 3).build());
    }

    /**
     * Environment place {@code e} (always-available injection, VER-006);
     * {@code t: one(e)->p1}. Injection makes p1 exceed any bound.
     */
    public static NamedNet envSingleFeed() {
        var e = place("e");
        var p1 = place("p1");
        var env = EnvironmentPlace.of(e);
        var t = Transition.builder("t").inputs(In.one(e)).outputs(Out.place(p1)).build();
        return new NamedNet(
            StructureOnly.bind(PetriNet.builder("envSingleFeed").transitions(t).build()),
            MarkingState.empty(),
            Set.of(env),
            EnvironmentAnalysisMode.alwaysAvailable());
    }

    /**
     * {@code p0(1),blocker(1),p1; t: one(p0), inhibitor(blocker) -> p1}.
     * Nothing ever drains blocker, so t never fires and p1 stays empty.
     */
    public static NamedNet inhibitorFrozen() {
        var p0 = place("p0");
        var blocker = place("blocker");
        var p1 = place("p1");
        var t = Transition.builder("t")
            .inputs(In.one(p0)).inhibitor(blocker).outputs(Out.place(p1)).build();
        return closed(
            PetriNet.builder("inhibitorFrozen").transitions(t).build(),
            MarkingState.builder().tokens(p0, 1).tokens(blocker, 1).build());
    }

    /**
     * The Strengthening.lean H1 witness: {@code t: all(p0)->p1} with p0(2).
     * The y=(1,1) invariant must be H1-dropped and the bound genuinely
     * violated (p1 reaches 1).
     */
    public static NamedNet h1ConsumeAll() {
        var p0 = place("p0");
        var p1 = place("p1");
        var t = Transition.builder("t").inputs(In.all(p0)).outputs(Out.place(p1)).build();
        return closed(
            PetriNet.builder("h1ConsumeAll").transitions(t).build(),
            MarkingState.builder().tokens(p0, 2).build());
    }

    /**
     * {@code p0(3),p1; t: atLeast(2)(p0)->p1} producing ONE p1 token. AtLeast
     * drains all available, so t fires at most once from M0 and p1 &le; 1; the
     * proof must come from the encoder's consume-all arm alone (the invariant
     * is H1-dropped).
     */
    public static NamedNet atLeastDrain() {
        var p0 = place("p0");
        var p1 = place("p1");
        var t = Transition.builder("t").inputs(In.atLeast(2, p0)).outputs(Out.place(p1)).build();
        return closed(
            PetriNet.builder("atLeastDrain").transitions(t).build(),
            MarkingState.builder().tokens(p0, 3).build());
    }

    /**
     * {@code p0(1),done,stuck; t: one(p0) -> and(done, stuck)}. The only
     * quiescent marking holds a token in the declared sink {@code done} AND one
     * in the non-sink {@code stuck}; per [VER-002] the sink token excuses it.
     * The fixture's {@code sinkPlaces} declares {@code done}.
     */
    public static NamedNet sinkPartialTerminal() {
        var p0 = place("p0");
        var done = place("done");
        var stuck = place("stuck");
        var t = Transition.builder("t")
            .inputs(In.one(p0)).outputs(Out.and(done, stuck)).build();
        return closed(
            PetriNet.builder("sinkPartialTerminal").transitions(t).build(),
            MarkingState.builder().tokens(p0, 1).build());
    }

    /**
     * {@code p0(1),done; t: one(p0)} with NO output spec — a sink transition
     * ([CORE-042], [CORE-043] AC4). {@code done} touches no arc, so it is
     * declared explicitly on the builder; after t fires the net holds no tokens
     * anywhere, so no declared sink has a token and [VER-002]'s error condition
     * holds.
     */
    public static NamedNet sinkDrainedTerminal() {
        var p0 = place("p0");
        var done = place("done");
        var t = Transition.builder("t").inputs(In.one(p0)).build();
        return closed(
            PetriNet.builder("sinkDrainedTerminal").places(done).transitions(t).build(),
            MarkingState.builder().tokens(p0, 1).build());
    }

    // === Route B fixtures ({@code "route": "B"} in fixtures.json) ===
    //
    // &nu; nets in the BASE mint&rarr;matched-join fragment, so the name-aware
    // state-class-graph verifier (NU-050 Route B) decides them and the SMT /
    // Route A encoders never see them. They pin the two markings on which Route
    // B's deadlock predicate — quiescent AND NOT(every marked place is a declared
    // sink) — disagrees with [VER-002]'s, which Route A implements verbatim. The
    // disagreement is recorded deliberately; see each fixture's netDescription.

    /** The ν-join correlation used by both Route B fixtures: name equality on the payload. */
    private static MatchSpec branchMatch(Place<String> branchA, Place<String> branchB) {
        return MatchSpec.builder()
            .key(branchA, NameId::of)
            .key(branchB, NameId::of)
            .build();
    }

    /**
     * &nu; net: {@code fork} co-mints ONE fresh name into {@code branchA}+{@code branchB};
     * {@code join} correlates them by name equality into {@code done}+{@code stuck}. The only
     * quiescent marking is {@code {done:1, stuck:1}} — a token in the declared sink AND one in
     * the non-sink {@code stuck}. Route B: violated. Route A on the same shape (see
     * {@link #sinkPartialTerminal()}): proven. Non-vacuity guard: a failed &nu; correlation
     * would also quiesce (at {@code {branchA:1, branchB:1}}, neither a sink) and also read
     * violated here — {@link #nuDrainedTerminal()}, built on the identical correlation, is what
     * turns violated if that ever happens.
     *
     * @return the named net
     */
    public static NamedNet nuMixedTerminal() {
        var source = place("source");
        var branchA = place("branchA");
        var branchB = place("branchB");
        var done = place("done");
        var stuck = place("stuck");
        var fork = Transition.builder("fork")
            .inputs(In.one(source)).outputs(Out.and(branchA, branchB)).build();
        var join = Transition.builder("join")
            .inputs(In.one(branchA), In.one(branchB))
            .match(branchMatch(branchA, branchB))
            .outputs(Out.and(done, stuck))
            .build();
        return closed(
            PetriNet.builder("nuMixedTerminal").transitions(fork, join).build(),
            MarkingState.builder().tokens(source, 1).build());
    }

    /**
     * Same mint&rarr;join shape, but {@code join} has NO output spec — a sink transition
     * ([CORE-042], [CORE-043] AC4) — so the only quiescent marking is the EMPTY one. The
     * declared sink {@code done} touches no arc and is therefore declared explicitly on the
     * builder, so the declaration resolves against the flattened net (the same requirement its
     * Route A sibling carries). Route B: proven — vacuously as to the predicate (nothing is
     * marked outside the sinks) but NOT as to the net: the empty marking is reachable only
     * because the &nu; join really correlates the co-minted pair and drains it; a correlation
     * failure would quiesce at {@code {branchA:1, branchB:1}} and turn this fixture violated.
     * Route A on the same shape (see {@link #sinkDrainedTerminal()}): violated.
     *
     * @return the named net
     */
    public static NamedNet nuDrainedTerminal() {
        var source = place("source");
        var branchA = place("branchA");
        var branchB = place("branchB");
        var done = place("done");
        var fork = Transition.builder("fork")
            .inputs(In.one(source)).outputs(Out.and(branchA, branchB)).build();
        var join = Transition.builder("join")
            .inputs(In.one(branchA), In.one(branchB))
            .match(branchMatch(branchA, branchB))
            .build();
        return closed(
            PetriNet.builder("nuDrainedTerminal").places(done).transitions(fork, join).build(),
            MarkingState.builder().tokens(source, 1).build());
    }

    /**
     * &nu; scatter-gather on Route A's exact name-coloured encoding ([NU-053]): a declared
     * budget puts the reachability-safety query on the coloured encoder. {@code fork} consumes
     * {@code source}+{@code budget} and co-mints one fresh name into {@code branchA}+{@code
     * branchB} (plus a {@code pending} token); {@code join} correlates the branches and returns
     * the budget token. Conservation {@code budget + pending = 2} bounds {@code budget} by 2.
     *
     * @return the named net
     */
    public static NamedNet nuScatterGather() {
        var source = place("source");
        var budget = place("budget");
        var pending = place("pending");
        var branchA = place("branchA");
        var branchB = place("branchB");
        var merged = place("merged");
        var fork = Transition.builder("fork")
            .inputs(In.one(source), In.one(budget))
            .outputs(Out.and(branchA, branchB, pending))
            .build();
        var join = Transition.builder("join")
            .inputs(In.one(branchA), In.one(branchB), In.one(pending))
            .match(branchMatch(branchA, branchB))
            .outputs(Out.and(merged, budget))
            .build();
        return closed(
            PetriNet.builder("nuScatterGather").transitions(fork, join).build(),
            MarkingState.builder().tokens(source, 3).tokens(budget, 2).build());
    }
}
