package org.libpetri.runtime;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import org.libpetri.core.Arc;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Timing;
import org.libpetri.core.Token;
import org.libpetri.core.Transition;

import java.time.Duration;
import java.util.List;
import java.util.Map;
import java.util.concurrent.CompletableFuture;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Configurable deadline-enforcement tolerance (TIME-013), exercised on both Java executors.
 *
 * <p>The tolerance is the grace band beyond a hard deadline ({@code deadline()} / {@code window()})
 * before a transition is force-disabled. It absorbs timer-resolution and scheduling jitter and is
 * configurable per executor via {@code Builder.deadlineTolerance(Duration)} (default {@code 5ms}).
 * It does not gate {@code exact()} transitions, which are enforced softly (TIME-006).
 *
 * <p>The band's behavioural effect (a deadline transition reaped only once elapsed exceeds
 * {@code latest + tolerance}) is driven solely by real executor lateness/jitter, which cannot be
 * reproduced deterministically without a wall-clock race. These tests therefore assert the builder
 * contract and that a configured executor runs correctly; the soft-{@code exact()} behaviour that
 * motivated the change is regression-tested in {@link AbstractNetExecutorEngineTest}.
 */
@Timeout(30)
class DeadlineToleranceTest {

    private static final Place<String> IN = Place.of("In", String.class);
    private static final Place<String> OUT = Place.of("Out", String.class);

    /** A single deadlined transition that fires immediately — used to confirm a configured executor runs. */
    private static PetriNet trivialNet() {
        var t = Transition.builder("t")
            .inputs(Arc.In.one(IN))
            .outputs(Arc.Out.place(OUT))
            .timing(Timing.deadline(Duration.ofSeconds(5)))
            .action(ctx -> {
                ctx.output(OUT, ctx.input(IN));
                return CompletableFuture.completedFuture(null);
            })
            .build();
        return PetriNet.builder("Trivial").transitions(t).build();
    }

    private static Map<Place<?>, List<Token<?>>> initial() {
        return Map.of(IN, List.of(Token.of("go")));
    }

    @Test
    void bitmap_builderAcceptsToleranceAndRuns() throws Exception {
        try (var executor = BitmapNetExecutor.builder(trivialNet(), initial())
                .deadlineTolerance(Duration.ofMillis(50)).build()) {
            var result = executor.run(Duration.ofSeconds(2)).toCompletableFuture().join();
            assertTrue(result.hasTokens(OUT));
        }
    }

    @Test
    void precompiled_builderAcceptsToleranceAndRuns() throws Exception {
        try (var executor = PrecompiledNetExecutor.builder(trivialNet(), initial())
                .deadlineTolerance(Duration.ofMillis(50)).build()) {
            var result = executor.run(Duration.ofSeconds(2)).toCompletableFuture().join();
            assertTrue(result.hasTokens(OUT));
        }
    }

    @Test
    void zeroToleranceIsAccepted() {
        assertDoesNotThrow(() -> BitmapNetExecutor.builder(trivialNet(), initial())
            .deadlineTolerance(Duration.ZERO).build().close());
        assertDoesNotThrow(() -> PrecompiledNetExecutor.builder(trivialNet(), initial())
            .deadlineTolerance(Duration.ZERO).build().close());
    }

    @Test
    void negativeToleranceIsRejected() {
        var neg = Duration.ofMillis(-1);
        assertThrows(IllegalArgumentException.class,
            () -> BitmapNetExecutor.builder(trivialNet(), initial()).deadlineTolerance(neg));
        assertThrows(IllegalArgumentException.class,
            () -> PrecompiledNetExecutor.builder(trivialNet(), initial()).deadlineTolerance(neg));
    }
}
