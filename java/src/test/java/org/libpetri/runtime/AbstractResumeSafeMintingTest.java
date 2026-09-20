package org.libpetri.runtime;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import org.libpetri.core.*;

import java.time.Instant;
import java.util.List;
import java.util.Map;
import java.util.concurrent.CompletableFuture;

import static org.junit.jupiter.api.Assertions.*;
import static org.libpetri.core.Arc.In.one;
import static org.libpetri.core.Arc.Out.place;

/**
 * <b>NU-011</b> resume-safe ν-name minting, against both executors.
 *
 * <p>NU-011 is the requirement an implementation acquires the moment it gains [CORE-073]
 * restore. The failure it prevents is not an error: a [NU-020] join correlates on name equality
 * alone, so a re-minted name silently merges a restored token with an unrelated fresh one.
 *
 * <p><b>No test here may depend on how many executors the JVM built before it.</b> The first
 * version of these did — two default-scope executors in one JVM minted disjoint names only
 * because a static counter had advanced between them — and so could not see that the first
 * executor of <i>every</i> JVM minted the same names. Names are therefore compared
 * <i>structurally</i>, via {@link Minted}, or under a pinned scope.
 */
@Timeout(60)
abstract class AbstractResumeSafeMintingTest {

    /** Builds an executor; {@code scope == null} leaves the default, {@code restore == null} seeds {@code initial}. */
    protected abstract PetriNetExecutor create(
        PetriNet net, Map<Place<?>, List<Token<?>>> initial,
        Map<String, List<Token<?>>> restore, String scope);

    /** Calls {@code Builder.executionScope(scope)} alone, so validation is observed where it is raised. */
    protected abstract void pinScope(String scope);

    private static final Place<String> IN  = Place.of("in",  String.class);
    private static final Place<String> OUT = Place.of("out", String.class);
    private static final Instant T0 = Instant.parse("2020-01-01T00:00:00Z");

    /**
     * A minted name taken apart the one way NU-011 makes unambiguous: the last {@code ':'}
     * splits off the counter, then the last {@code '#'} before it splits off the scope.
     */
    record Minted(String transition, String scope, long n) {
        static Minted parse(String name) {
            int colon = name.lastIndexOf(':');
            int hash = name.lastIndexOf('#', colon);
            assertTrue(hash >= 0 && colon > hash, "not <transition>#<scope>:<n>: " + name);
            return new Minted(name.substring(0, hash), name.substring(hash + 1, colon),
                Long.parseLong(name.substring(colon + 1)));
        }
    }

    /** Mints a ν-name per firing and writes it out, so the minted names are observable. */
    private static PetriNet mintingNet(String transitionName) {
        return PetriNet.builder("minter").transition(Transition.builder(transitionName)
            .inputs(one(IN)).outputs(place(OUT))
            .action(ctx -> {
                ctx.output(OUT, ctx.freshName().toString());
                return CompletableFuture.completedFuture(null);
            })
            .build()).build();
    }

    private static PetriNet mintingNet() { return mintingNet("fork"); }

    private static Map<Place<?>, List<Token<?>>> seed(int n) {
        return Map.of(IN, List.copyOf(java.util.Collections.nCopies(n, new Token<>("x", T0))));
    }

    private static List<String> mintedBy(PetriNetExecutor executor) {
        return executor.run().peekTokens(OUT).stream().map(t -> (String) t.value()).toList();
    }

    @Test
    void theDefaultScopeIsARandom128BitTokenNotTheExecutionId_AC5() {
        try (var executor = create(mintingNet(), seed(3), null, null)) {
            var minted = mintedBy(executor).stream().map(Minted::parse).toList();

            var scope = minted.get(0).scope();
            assertTrue(scope.matches("[0-9a-f]{32}"),
                "NU-011: the default scope is a process-unique RANDOM token — exactly 32 "
                    + "lowercase hex characters, 128 bits. It used to be the execution id, a "
                    + "process counter from 0, so the first executor of EVERY JVM minted "
                    + "fork#0:0 — and a restore is routinely the first thing a fresh process "
                    + "does. No in-process test could see that. Got scope: '" + scope + "'");
            assertNotEquals(executor.executionId(), scope,
                "the execution id stays the reproducible process counter (TIME-015 AC#14); the "
                    + "two are now different values");
            assertEquals(List.of(0L, 1L, 2L), minted.stream().map(Minted::n).toList(),
                "randomness is confined to the scope: <n> is a plain counter from 0");
            assertEquals(1, minted.stream().map(Minted::scope).distinct().count(),
                "one scope per executor, drawn once");

            try (var another = create(mintingNet(), seed(1), null, null)) {
                assertNotEquals(scope, Minted.parse(mintedBy(another).get(0)).scope(),
                    "NU-011 AC#5: different for every executor");
            }
        }
    }

    @Test
    void aResumedExecutionDoesNotReMintNamesAlreadyInTheMarking_AC1() {
        Map<String, List<Token<?>>> snapshot;
        List<String> original;
        try (var first = create(mintingNet(), seed(3), null, null)) {
            original = mintedBy(first);
            snapshot = first.snapshot().marking();
        }
        assertEquals(3, original.size());

        // Resume: a NEW executor restored from a marking that already holds those names, and
        // given fresh input so it mints again.
        var resumedSnapshot = new java.util.TreeMap<>(snapshot);
        resumedSnapshot.put("in", seed(3).get(IN));
        List<String> all;
        try (var second = create(mintingNet(), Map.of(), resumedSnapshot, null)) {
            all = mintedBy(second);
        }

        assertEquals(6, all.size(), "three restored, three freshly minted");
        assertEquals(6, all.stream().distinct().count(),
            "NU-011 AC#1: an execution seeded from a restored marking MUST NOT re-mint names "
                + "already present. Counting firings from zero collides, and because a NU-020 "
                + "join correlates on name equality alone the collision surfaces as a silent "
                + "mis-correlation rather than an error. Names: " + all);
        var scopes = all.stream().map(n -> Minted.parse(n).scope()).distinct().toList();
        assertEquals(2, scopes.size(),
            "disjoint BY SCOPE, which is what holds across processes; disjoint-by-counter only "
                + "ever held inside one JVM. Scopes: " + scopes);
    }

    /** A forked branch: the ν-name it was minted under, and which run segment forked it. */
    record Branch(String name, String segment) { }

    private static final Place<Branch> LEFT  = Place.of("left",  Branch.class);
    private static final Place<Branch> RIGHT = Place.of("right", Branch.class);

    private static Transition fork() {
        return Transition.builder("fork").inputs(one(IN)).outputs(Arc.Out.and(LEFT, RIGHT))
            .action(ctx -> {
                var branch = new Branch(ctx.freshName().toString(), ctx.input(IN));
                ctx.output(LEFT, branch);
                ctx.output(RIGHT, branch);
                return CompletableFuture.completedFuture(null);
            }).build();
    }

    private static Transition join() {
        return Transition.builder("join").inputs(one(LEFT), one(RIGHT))
            .match(MatchSpec.builder()
                .key(LEFT,  (Branch b) -> NameId.of(b.name()))
                .key(RIGHT, (Branch b) -> NameId.of(b.name()))
                .build())
            .outputs(place(OUT))
            .action(ctx -> {
                ctx.output(OUT, ctx.input(LEFT).segment() + "+" + ctx.input(RIGHT).segment());
                return CompletableFuture.completedFuture(null);
            }).build();
    }

    /** Segment 1 forks once; its LEFT branch is persisted alone, still awaiting its sibling. */
    private Map<String, List<Token<?>>> aLeftBranchAwaitingItsSibling(String scope) {
        var forkOnly = PetriNet.builder("fork-only").transition(fork()).build();
        try (var first = create(forkOnly, Map.of(IN, List.of(new Token<>("seg1", T0))), null, scope)) {
            first.run();
            var snapshot = new java.util.TreeMap<>(first.snapshot().marking());
            snapshot.remove("right"); // the sibling is still out with external work
            snapshot.put("in", List.of(new Token<>("seg2", T0))); // fresh work for segment 2
            return snapshot;
        }
    }

    private List<String> joinedAfterResume(Map<String, List<Token<?>>> snapshot, String scope) {
        var full = PetriNet.builder("fork-join").transition(fork()).transition(join()).build();
        try (var second = create(full, Map.of(), snapshot, scope)) {
            return second.run().peekTokens(OUT).stream().map(t -> (String) t.value()).toList();
        }
    }

    @Test
    void aRestoredBranchIsNotJoinedWithAFreshlyMintedSibling_AC2() {
        assertEquals(List.of("seg2+seg2"), joinedAfterResume(aLeftBranchAwaitingItsSibling(null), null),
            "NU-011 AC#2: segment 2's fork mints a name of its own, so its two branches join "
                + "each other and the restored seg1 branch keeps waiting for ITS sibling. A "
                + "NU-020 join correlates on name equality alone, so a re-minted name pairs "
                + "the restored branch with an unrelated fresh one — silently.");

        // The control: what AC#2 forbids, produced on purpose by reusing one scope for both
        // segments (the misuse Builder.executionScope documents). If this arm ever stops
        // mis-correlating, the assertion above has stopped being able to fail.
        assertEquals(List.of("seg1+seg2"), joinedAfterResume(aLeftBranchAwaitingItsSibling("same"), "same"),
            "with the name re-minted the restored LEFT (older, so first by NU-020's tie-break) "
                + "takes the fresh RIGHT");
    }

    @Test
    void aFixedScopeAndFiringOrderReproduceTheSequence_AC3() {
        List<String> first, second;
        try (var a = create(mintingNet(), seed(3), null, "s1")) {
            first = mintedBy(a);
        }
        try (var b = create(mintingNet(), seed(3), null, "s1")) {
            second = mintedBy(b);
        }
        assertEquals(first, second,
            "NU-011: replay stability is preserved WITHIN a run segment — for a fixed scope and "
                + "firing order the minted sequence must be reproducible. An implementation must "
                + "not satisfy resume-safety with randomness that makes a segment unreproducible.");
        assertEquals(List.of("fork#s1:0", "fork#s1:1", "fork#s1:2"), first,
            "the agreed cross-language format is <transition>#<scope>:<n>");
    }

    @Test
    void twoExecutionsFromTheSameSnapshotMintDisjointNames_AC4() {
        var snapshot = Map.<String, List<Token<?>>>of("in", seed(2).get(IN));
        List<String> a, b;
        try (var x = create(mintingNet(), Map.of(), snapshot, null);
             var y = create(mintingNet(), Map.of(), snapshot, null)) {
            a = mintedBy(x);
            b = mintedBy(y);
        }
        assertTrue(java.util.Collections.disjoint(a, b),
            "NU-011 AC#4: two executions restored from the same snapshot mint disjoint name "
                + "sets. a=" + a + " b=" + b);
        assertNotEquals(Minted.parse(a.get(0)).scope(), Minted.parse(b.get(0)).scope(),
            "and they are disjoint because their scopes differ, not because a counter moved");
    }

    @Test
    void executionScopeRejectsEmptyAndBothSeparators_AC6() {
        var colon = assertThrows(IllegalArgumentException.class, () -> pinScope("a:b"));
        assertTrue(colon.getMessage().contains("NU-011"), "the error cites the requirement");

        var hash = assertThrows(IllegalArgumentException.class, () -> pinScope("a#b"),
            "'#' separates the transition from the scope; a scope holding one makes "
                + "<transition>#<scope>:<n> ambiguous to parse");
        assertTrue(hash.getMessage().contains("NU-011"), "the error cites the requirement");

        assertThrows(IllegalArgumentException.class, () -> pinScope(""), "length 0 is rejected");
        assertThrows(IllegalArgumentException.class, () -> pinScope(null));

        assertDoesNotThrow(() -> pinScope("  "),
            "whitespace is NOT rejected: the rule is identical in all four implementations — "
                + "empty, ':' and '#' — and a blank scope is ugly, not ambiguous");
    }

    @Test
    void aMintedNameParsesUniquelyEvenWhenTheTransitionNameHoldsSeparators_AC6() {
        // A transition name may hold '#' and ':'; the scope may not. That asymmetry is what
        // makes "last ':' then last '#' before it" a total parse.
        try (var executor = create(mintingNet("fork#a:1"), seed(1), null, "seg-2")) {
            var parsed = Minted.parse(mintedBy(executor).get(0));
            assertEquals(new Minted("fork#a:1", "seg-2", 0), parsed);
        }
    }

    @Test
    void theDetachedFallbackMintsTheSameShape_NU011() {
        // A directly-constructed context — a harness or test double — has no executor and so
        // no execution to scope to. It must still mint <transition>#<scope>:<n>: NU-011 is a
        // MUST, so a path minting the old unscoped shape is a latent violation the moment
        // anything reaches it, and this is exactly where someone would meet that shape and
        // take it for the format.
        var t = Transition.builder("fork").inputs(one(IN)).outputs(place(OUT))
            .action(ctx -> CompletableFuture.completedFuture(null)).build();
        var ctx = new TransitionContext(t, new TokenInput(1), new TokenOutput());

        var first = Minted.parse(ctx.freshName().toString());
        var second = Minted.parse(ctx.freshName().toString());

        assertTrue(first.scope().matches("[0-9a-f]{32}"),
            "the same default as the executor path: a random 128-bit scope, so a harness's "
                + "names cannot collide with a persisted marking's either. Got: " + first);
        assertNotEquals(first, second, "still unique within the context");
    }
}
