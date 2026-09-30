package org.libpetri.smt;

import org.libpetri.analysis.AllMints;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.attribute.PosixFilePermissions;
import java.time.Duration;
import java.util.List;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicReference;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import org.junit.jupiter.api.condition.DisabledOnOs;
import org.junit.jupiter.api.condition.OS;
import org.junit.jupiter.api.io.TempDir;
import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.MatchSpec;
import org.libpetri.core.NameId;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.fixtures.StructureOnly;
import org.libpetri.smt.z3.Z3Solver;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * [VER-013] cancellation, Java's idiom: interrupting the thread that runs {@code verify()}. The
 * running z3 process is destroyed at once, no further process starts, the solver-free builds stop
 * at their next poll, the verdict is {@code Unknown} with {@code verification cancelled during
 * <phase>}, and the interrupt flag is still set when {@code verify()} returns (AC11, AC12).
 */
@DisabledOnOs(OS.WINDOWS)
class CancellationTest {

    @TempDir
    static Path root;

    private static final Place<Integer> P0 = Place.of("p0", Integer.class);
    private static final Place<Integer> P1 = Place.of("p1", Integer.class);

    /** A z3 stub that logs each run's pid and then sleeps, ignoring every timeout. */
    private static Z3Solver sleeper(String name) throws IOException {
        Path dir = root.resolve(name);
        Files.createDirectories(dir);
        Path script = dir.resolve("z3");
        Path log = dir.resolve("runs");
        Files.writeString(script,
            "#!/bin/sh\nif [ \"$1\" = \"--version\" ]; then echo 'Z3 version 4.16.0 - 64 bit'; exit 0; fi\n"
                + "echo $$ >> '" + log.toAbsolutePath() + "'\nexec sleep 60\n",
            StandardCharsets.UTF_8);
        Files.setPosixFilePermissions(script, PosixFilePermissions.fromString("rwxr-xr-x"));
        try {
            return Z3Solver.at(script.toString());
        } catch (Z3Solver.Z3Unavailable e) {
            throw new AssertionError(e);
        }
    }

    private static List<String> runs(String name) throws IOException {
        Path log = root.resolve(name).resolve("runs");
        return Files.exists(log) ? Files.readAllLines(log).stream().filter(l -> !l.isBlank()).toList() : List.of();
    }

    private static SmtVerifier chain(Z3Solver solver) {
        var t = Transition.builder("t").inputs(In.one(P0)).outputs(Out.place(P1)).build();
        return SmtVerifier.forNet(StructureOnly.bind(PetriNet.builder("chain").transitions(t).build()))
            .enumerationMaxClasses(0)
            .initialMarking(m -> m.tokens(P0, 1))
            .property(SmtProperty.placeBound(P1, 0))
            .solver(solver)
            .timeout(Duration.ofSeconds(60));
    }

    /** The result of {@code call} on a fresh thread, interrupted once {@code ready} holds, and whether its flag was set after. */
    private record Run(SmtVerificationResult result, boolean flagAfter, long ms) {}

    private static Run runInterrupted(java.util.function.Supplier<SmtVerificationResult> call,
                                      java.util.function.BooleanSupplier ready) throws Exception {
        var result = new AtomicReference<SmtVerificationResult>();
        var flag = new AtomicBoolean();
        var failure = new AtomicReference<Throwable>();
        var worker = new Thread(() -> {
            try {
                result.set(call.get());
                flag.set(Thread.currentThread().isInterrupted());
            } catch (Throwable t) {
                failure.set(t);
            }
        });
        worker.start();
        long deadline = System.nanoTime() + 30_000_000_000L;
        while (!ready.getAsBoolean()) {
            if (System.nanoTime() > deadline) throw new AssertionError("never became ready");
            Thread.sleep(10);
        }
        long t0 = System.nanoTime();
        worker.interrupt();
        worker.join(30_000);
        long ms = (System.nanoTime() - t0) / 1_000_000;
        if (failure.get() != null) throw new AssertionError(failure.get());
        assertFalse(worker.isAlive(), "verify() did not return after the interrupt");
        return new Run(result.get(), flag.get(), ms);
    }

    private static String unknownReason(SmtVerificationResult r) {
        return assertInstanceOf(SmtVerificationResult.Verdict.Unknown.class, r.verdict(), r.report()).reason();
    }

    @Test
    @Timeout(value = 60, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    void interruptingWhileZ3Runs_killsIt_startsNoOther_andKeepsTheFlag() throws Exception {
        var solver = sleeper("sleeper");
        var run = runInterrupted(() -> chain(solver).verify(), () -> {
            try {
                return !runs("sleeper").isEmpty();
            } catch (IOException e) {
                throw new AssertionError(e);
            }
        });

        assertEquals("verification cancelled during linear bound", unknownReason(run.result()));
        assertTrue(run.result().report().endsWith("UNKNOWN: verification cancelled during linear bound\n"),
            run.result().report());
        assertTrue(run.flagAfter(), "the interrupt flag is set when verify() returns");
        assertTrue(run.ms() < 10_000, "returned " + run.ms() + " ms after the interrupt, not at the 60 s timeout");
        var pids = runs("sleeper");
        assertEquals(1, pids.size(), "no further process after the cancellation: " + pids);
        var handle = ProcessHandle.of(Long.parseLong(pids.getFirst().strip()));
        assertTrue(handle.isEmpty() || !handle.get().isAlive(), "the running z3 process was destroyed");
    }

    @Test
    void aThreadInterruptedBeforeTheCall_returnsAtOnceWithoutAProcess() throws Exception {
        var solver = sleeper("pre");
        Thread.currentThread().interrupt();
        SmtVerificationResult r;
        boolean flag;
        try {
            r = chain(solver).verify();
        } finally {
            flag = Thread.interrupted(); // reads and clears, so the flag cannot leak into other tests
        }
        assertEquals("verification cancelled during net preparation", unknownReason(r));
        assertTrue(flag, "the flag is still set");
        assertEquals(List.of(), runs("pre"));
    }

    private static Place<Object> p(String name) {
        return Place.of(name, Object.class);
    }

    /** {@code k} independent toggles: 2^k classes, untimed, so the enumeration route takes it. */
    private static PetriNet toggles(int k) {
        var b = PetriNet.builder("toggles-" + k);
        for (int i = 0; i < k; i++) {
            b.transition(Transition.builder("on_" + i).inputs(In.one(p("a_" + i))).outputs(Out.place(p("b_" + i))).build());
            b.transition(Transition.builder("off_" + i).inputs(In.one(p("b_" + i))).outputs(Out.place(p("a_" + i))).build());
        }
        return StructureOnly.bind(b.build());
    }

    @Test
    @Timeout(value = 60, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    void interruptingAnEnumerationBuild_stopsIt_andLeavesTheCacheAsFound() throws Exception {
        int k = 22;
        var m0 = MarkingState.builder();
        for (int i = 0; i < k; i++) m0.tokens(p("a_" + i), 1);
        var marking = m0.build();
        var net = toggles(k);
        var cache = new StateSpaceCache();
        long start = System.nanoTime();
        var run = runInterrupted(() -> SmtVerifier.forNet(net).initialMarking(marking)
                .property(SmtProperty.placeBound(p("a_0"), 1))
                .enumerationMaxClasses(10_000_000)
                .stateSpaceCache(cache)
                .verify(),
            () -> System.nanoTime() - start > 300_000_000L);
        assertEquals("verification cancelled during state-space enumeration", unknownReason(run.result()));
        assertEquals(SmtVerificationResult.Route.ENUMERATION, run.result().route());
        assertTrue(run.flagAfter());
        assertTrue(run.ms() < 10_000, "returned " + run.ms() + " ms after the interrupt");
        assertEquals(0, cache.size(), "a cancelled build is not a truncation");
    }

    @Test
    @Timeout(value = 60, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    void interruptingARouteBBuild_stopsIt() throws Exception {
        // gen: G -> G, A, B mints a fresh name onto A and B forever; join: A, B matched -> DONE.
        // The live pool is unbounded, so the name-partition graph never closes.
        var g = Place.of("G", String.class);
        var a = Place.of("A", String.class);
        var b = Place.of("B", String.class);
        var done = Place.of("DONE", String.class);
        var match = MatchSpec.builder().key(a, (String v) -> NameId.of(v)).key(b, (String v) -> NameId.of(v)).build();
        var net = StructureOnly.bind(PetriNet.builder("ever-minting").transitions(
            Transition.builder("gen").inputs(In.one(g)).outputs(Out.and(g, a, b)).build(),
            Transition.builder("join").inputs(In.one(a), In.one(b)).match(match).outputs(Out.place(done)).build())
            .build());
        long start = System.nanoTime();
        var run = runInterrupted(() -> SmtVerifier.forNet(net).mintTransitions(AllMints.names(net)).initialMarking(m -> m.tokens(g, 1))
                .property(SmtProperty.deadlockFree())
                .nuMaxClasses(Integer.MAX_VALUE)
                .verify(),
            () -> System.nanoTime() - start > 300_000_000L);
        assertEquals("verification cancelled during Route B (ν name-partition graph)", unknownReason(run.result()));
        assertEquals(SmtVerificationResult.Route.NU_SCG, run.result().route());
        assertTrue(run.flagAfter());
        assertTrue(run.ms() < 10_000, "returned " + run.ms() + " ms after the interrupt");
    }

    @Test
    void outsideVerify_anInterruptedThreadStartsNoProcess() throws Exception {
        var solver = sleeper("outside");
        Thread.currentThread().interrupt();
        Throwable error;
        boolean flag;
        try {
            error = org.junit.jupiter.api.Assertions.assertThrows(
                org.libpetri.smt.z3.Z3Process.Z3ProcessException.class,
                () -> solver.run("(check-sat)", "probe", Duration.ofSeconds(5), List.of()));
        } finally {
            flag = Thread.interrupted();
        }
        assertEquals("verification cancelled; z3 not started", error.getMessage());
        assertTrue(flag);
        assertEquals(List.of(), runs("outside"));
    }

    @Test
    void openNet_anInterruptedThreadStopsBeforeTheGraph_andStartsNoQuery() {
        var net = StructureOnly.bind(PetriNet.builder("chain").transitions(
            Transition.builder("t").inputs(In.one(P0)).outputs(Out.place(P1)).build()).build());
        var contract = org.libpetri.smt.opennet.OpenNetContract.builder().initialTokens(P0, 1).build();
        Thread.currentThread().interrupt();
        org.libpetri.smt.opennet.OpenNetResult r;
        boolean flag;
        try {
            r = org.libpetri.smt.opennet.OpenNetVerifier.verifyOpenNet(net, contract);
        } finally {
            flag = Thread.interrupted();
        }
        var unknown = assertInstanceOf(SmtVerificationResult.Verdict.Unknown.class, r.verdict(), r.report());
        assertEquals("verification cancelled during open-net state-class graph", unknown.reason());
        assertTrue(flag);
    }
}
