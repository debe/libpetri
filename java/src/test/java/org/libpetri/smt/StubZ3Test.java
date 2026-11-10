package org.libpetri.smt;

import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.fixtures.StructureOnly;
import org.libpetri.smt.z3.Z3Solver;
import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledOnOs;
import org.junit.jupiter.api.condition.OS;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.attribute.PosixFilePermissions;
import java.time.Duration;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.*;

/**
 * End-to-end tests against a STUB {@code z3} (V5, V6, C4, and the VER-013 transport
 * contract), the Java mirror of Rust's {@code tests/stub_z3.rs}.
 *
 * <p>The verifier shells out to a {@code z3} executable, so the only way to pin how it
 * reads a solver reply is to control the reply. Each scenario writes a tiny POSIX shell
 * script named {@code z3} and hands it to the verifier through the {@code solver(...)}
 * seam (the JVM cannot change its own environment, so {@code LIBPETRI_Z3} resolution is
 * covered by {@link Z3Solver#resolve(Map)} instead). Every stub answers
 * {@code --version} first, because the transport probes the executable before it runs a
 * script.
 */
@EnabledOnOs({OS.LINUX, OS.MAC})
class StubZ3Test {

    private static final String VERSION_OK = "Z3 version 4.16.0 - 64 bit";
    private static Path root;

    @BeforeAll
    static void scratch() throws IOException {
        root = Path.of("target", "stub-z3", Long.toString(ProcessHandle.current().pid()));
        Files.createDirectories(root);
    }

    @AfterAll
    static void cleanup() throws IOException {
        try (Stream<Path> walk = Files.walk(root)) {
            walk.sorted(Comparator.reverseOrder()).forEach(p -> {
                try {
                    Files.deleteIfExists(p);
                } catch (IOException _) {
                    // best effort
                }
            });
        }
    }

    /** Writes {@code <root>/<name>/z3} answering {@code --version} with {@code version}, else running {@code body}. */
    private static Z3Solver stub(String name, String version, String body) throws IOException {
        Path dir = root.resolve(name);
        Files.createDirectories(dir);
        Path script = dir.resolve("z3");
        Files.writeString(script,
            "#!/bin/sh\nif [ \"$1\" = \"--version\" ]; then echo '" + version + "'; exit 0; fi\n" + body,
            StandardCharsets.UTF_8);
        Files.setPosixFilePermissions(script, PosixFilePermissions.fromString("rwxr-xr-x"));
        try {
            return Z3Solver.at(script.toString());
        } catch (Z3Solver.Z3Unavailable e) {
            throw new AssertionError("stub must resolve: " + e.getMessage(), e);
        }
    }

    private static final Place<Integer> P0 = Place.of("p0", Integer.class);
    private static final Place<Integer> P1 = Place.of("p1", Integer.class);
    private static final Place<Integer> BLOCKER = Place.of("blocker", Integer.class);

    /** p0(1) -> p1: a plain chain the stub's answers are applied to. */
    private static PetriNet chainNet() {
        var t = Transition.builder("t").inputs(In.one(P0)).outputs(Out.place(P1)).build();
        return StructureOnly.bind(PetriNet.builder("stub_chain").transitions(t).build());
    }

    /** Nothing ever drains {@code blocker}, so {@code t} can never fire: p1 is unreachable. */
    private static PetriNet frozenNet() {
        var t = Transition.builder("t").inputs(In.one(P0)).inhibitors(BLOCKER).outputs(Out.place(P1)).build();
        return StructureOnly.bind(PetriNet.builder("stub_frozen").transitions(t).build());
    }

    private static SmtVerificationResult verify(PetriNet net, Z3Solver solver, SmtProperty property,
                                                Duration timeout, Map<Place<?>, Integer> tokens) {
        return SmtVerifier.forNet(net)
            // Explicit opt-out, not an oversight: this suite drives the SOLVER transport
            // through a stub, and [VER-017]'s enumeration route would decide these tiny
            // untimed nets before the stub is ever invoked.
            .enumerationMaxClasses(0)
            .initialMarking(m -> tokens.forEach(m::tokens))
            .property(property)
            .environmentMode(EnvironmentAnalysisMode.ignore())
            // The contract under test is the HORN and certificate scripts' transport. The
            // phases of VER-018/019 run first and would consume the stub's canned replies.
            .stateEquationPhase(false)
            .firingBound(false)
            .solver(solver)
            .timeout(timeout)
            .verify();
    }

    private static SmtVerificationResult verify(Z3Solver solver, SmtProperty property) {
        return verify(chainNet(), solver, property, Duration.ofSeconds(5), Map.of(P0, 1));
    }

    private static String unknownReason(SmtVerificationResult result) {
        var unknown = assertInstanceOf(SmtVerificationResult.Verdict.Unknown.class, result.verdict(),
            "expected Unknown\n" + result.report());
        return unknown.reason();
    }

    /** The V5 reply: a banner, {@code unsat}, the benign model error, a two-state proof. */
    private static final String V5_BODY = """
        cat > /dev/null
        echo 'WARNING: solver configured with a non-default strategy'
        echo 'unsat'
        echo '(error "model is not available")'
        echo '(proof (asserted (Reachable 1 0)) (asserted (Reachable 0 1)))'
        """;

    @Test
    void v5_warningLineBeforeTheVerdictMustNotLoseIt() throws IOException {
        // The HORN script asks for both a proof and a model, so one of the two always
        // answers `(error …)`; a build that prints a banner first must still be read.
        var result = verify(stub("v5", VERSION_OK, V5_BODY), SmtProperty.placeBound(P1, 0));
        assertInstanceOf(SmtVerificationResult.Verdict.Violated.class, result.verdict(), result.report());
        assertEquals(Boolean.TRUE, result.counterexampleConfirmed(), "the decoded chain replays\n" + result.report());
        assertTrue(result.report().contains("  Solver: z3 4.16.0\n"),
            "the report names the probed solver version\n" + result.report());
    }

    @Test
    void c4_genuineNoChainReplayIsTheOneDowngrade() throws IOException {
        // Same stub answer on a net whose only transition is frozen by an inhibitor:
        // the abstract successor space is {M0} and holds no violating state, so the
        // counterexample is spurious and VIOLATED is withheld.
        var solver = stub("c4", VERSION_OK, """
            cat > /dev/null
            echo 'unsat'
            echo '(proof (asserted (Reachable 1 1 0)))'
            """);
        var result = verify(frozenNet(), solver, SmtProperty.unreachable(java.util.Set.of(P1)),
            Duration.ofSeconds(5), Map.of(P0, 1, BLOCKER, 1));
        assertEquals(SmtVerifier.REPLAY_NO_CHAIN_REASON, unknownReason(result), "the C2 reason, verbatim");
        assertEquals(Boolean.FALSE, result.counterexampleConfirmed());
    }

    @Test
    void v6_errorOnStderrMustNeverLeaveAProvenStanding() throws IOException {
        // `sat` with a plausible certificate on the HORN run, then three clean `unsat`
        // lines on stdout while the error that dropped an assert goes to stderr.
        var solver = stub("v6-stderr", VERSION_OK, """
            script=$(cat)
            case "$script" in
              *"set-logic HORN"*)
                echo 'sat'
                echo '(error "proof is not available")'
                echo '(define-fun Reachable ((x!0 Int) (x!1 Int)) Bool (<= x!1 1))'
                ;;
              *)
                echo '(error "line 4: unknown constant Reachable")' >&2
                echo 'unsat'
                echo 'unsat'
                echo 'unsat'
                ;;
            esac
            """);
        var result = verify(solver, SmtProperty.placeBound(P1, 1));
        String reason = unknownReason(result);
        assertTrue(reason.startsWith("certificate check could not run:")
                && reason.contains("stderr")
                && reason.endsWith("PROVEN is withheld without an independently validated certificate"),
            "the C2 could-not-run reason: " + reason);
        assertTrue(result.report().contains("  Certificate check: FAILED"), result.report());
    }

    @Test
    void v6_nonZeroExitWithTruncatedAnswersDoesNotCertify() throws IOException {
        var solver = stub("v6-exit", VERSION_OK, """
            script=$(cat)
            case "$script" in
              *"set-logic HORN"*)
                echo 'sat'
                echo '(define-fun Reachable ((x!0 Int) (x!1 Int)) Bool (<= x!1 1))'
                ;;
              *)
                echo 'unsat'
                exit 1
                ;;
            esac
            """);
        var result = verify(solver, SmtProperty.placeBound(P1, 1));
        assertInstanceOf(SmtVerificationResult.Verdict.Unknown.class, result.verdict(),
            "a truncated certificate run must not certify\n" + result.report());
    }

    @Test
    void v5_errorReplyWithoutVerdictIsUnknownNotAnException() throws IOException {
        var solver = stub("no-verdict", VERSION_OK, """
            cat > /dev/null
            echo '(error "line 1: invalid command")'
            """);
        assertEquals("Z3 error: (error \"line 1: invalid command\")",
            unknownReason(verify(solver, SmtProperty.placeBound(P1, 1))));
    }

    @Test
    void ver013_timeoutLineIsTheBackstopNotAVerdict() throws IOException {
        // With a 5 s budget the backstop is -T:6; the reason names it.
        var solver = stub("timeout", VERSION_OK, "cat > /dev/null\necho 'timeout'\n");
        var result = verify(solver, SmtProperty.placeBound(P1, 1));
        assertEquals("z3 hard timeout after 6s", unknownReason(result));
        assertTrue(result.report().contains("  Status: UNKNOWN (z3 hard timeout after 6s)\n"), result.report());
    }

    @Test
    void ver013_solverIgnoringBothTimeoutsIsKilled() throws IOException {
        // Never reads stdin, never exits: the watchdog at the budget plus twice the grace
        // kills it. No elapsed time is asserted, only the outcome.
        var solver = stub("wedged", VERSION_OK, "exec sleep 30\n");
        var result = verify(chainNet(), solver, SmtProperty.placeBound(P1, 1),
            Duration.ofMillis(200), Map.of(P0, 1));
        assertEquals("z3 did not exit within 2200 ms and was killed", unknownReason(result));
    }

    @Test
    void ver013_replyLargerThanAPipeBufferIsDrained() throws IOException {
        // Two megabytes of banner on BOTH streams before the verdict.
        var solver = stub("banner", VERSION_OK, """
            cat > /dev/null
            yes 'WARNING: a very long banner line' | head -c 2000000
            yes 'WARNING: a very long banner line' | head -c 2000000 >&2
            echo
            echo 'unsat'
            echo '(proof (asserted (Reachable 1 0)) (asserted (Reachable 0 1)))'
            """);
        var result = verify(solver, SmtProperty.placeBound(P1, 0));
        assertInstanceOf(SmtVerificationResult.Verdict.Violated.class, result.verdict(),
            "a 2 MB banner on each stream must not stall or hide the verdict\n" + result.report());
        assertEquals(Boolean.TRUE, result.counterexampleConfirmed());
    }

    @Test
    void ver013_solverBelowTheVersionFloorIsRefused() throws IOException {
        Path dir = root.resolve("too-old");
        Files.createDirectories(dir);
        Path script = dir.resolve("z3");
        Files.writeString(script, "#!/bin/sh\necho 'Z3 version 4.7.1 - 64 bit'\n");
        Files.setPosixFilePermissions(script, PosixFilePermissions.fromString("rwxr-xr-x"));
        var e = assertThrows(Z3Solver.Z3Unavailable.class, () -> Z3Solver.at(script.toString()));
        assertEquals("z3 4.7.1 is older than the minimum 4.8.0", e.getMessage());
    }

    @Test
    void ver013_probeWithoutAVersionIsRefused() throws IOException {
        Path dir = root.resolve("no-version");
        Files.createDirectories(dir);
        Path script = dir.resolve("z3");
        Files.writeString(script, "#!/bin/sh\necho 'not a solver'\n");
        Files.setPosixFilePermissions(script, PosixFilePermissions.fromString("rwxr-xr-x"));
        var e = assertThrows(Z3Solver.Z3Unavailable.class, () -> Z3Solver.at(script.toString()));
        assertEquals("z3 --version did not report a version: not a solver", e.getMessage());
    }

    @Test
    void ver013_missingExecutableNamesTheCommandAndTheEnvVar() {
        var e = assertThrows(Z3Solver.Z3Unavailable.class,
            () -> Z3Solver.resolve(Map.of(Z3Solver.Z3_ENV, "/nonexistent/libpetri-z3")));
        assertEquals("z3 binary not found: /nonexistent/libpetri-z3; install z3 >= 4.8.0 or set LIBPETRI_Z3",
            e.getMessage());
    }

    @Test
    void ver013_unresolvedSolverIsAnUnknownVerdictWithTheSolverLine() {
        // The seam cannot inject an unresolvable solver; drive the verifier's own
        // resolution with a stub that answers no version and see the report.
        var e = assertThrows(Z3Solver.Z3Unavailable.class,
            () -> Z3Solver.resolve(Map.of(Z3Solver.Z3_ENV, "/nonexistent/libpetri-z3")));
        assertTrue(e.getMessage().startsWith("z3 binary not found:"));
    }

    @Test
    void ver013_dumpDirectoryRecordsEveryScriptAndReply() throws IOException {
        Path dump = root.resolve("dump");
        var solver = stub("dump-src", VERSION_OK, V5_BODY).withDumpDir(dump);
        var result = verify(solver, SmtProperty.placeBound(P1, 0));
        assertInstanceOf(SmtVerificationResult.Verdict.Violated.class, result.verdict(), result.report());
        try (Stream<Path> files = Files.list(dump)) {
            // A reachability-safety property runs the linear bound (VER-015) before the
            // bounded witness run (VER-025) and the HORN query; the stub answers `unsat` to all
            // three (no bound separates; no run within the depth; then the
            // violation). The counter is process-wide, so an earlier dump anywhere in this
            // JVM moves it: check the phases in order and that each follows the last, not the
            // absolute numbers.
            var names = files.map(p -> p.getFileName().toString())
                .sorted(Comparator.comparingInt(StubZ3Test::dumpCounter).thenComparing(Comparator.naturalOrder()))
                .toList();
            assertEquals(6, names.size(), "three scripts and three replies: " + names);
            assertEquals(List.of("bound.out", "bound.smt2", "witness.out", "witness.smt2", "horn.out", "horn.smt2"),
                names.stream().map(n -> n.substring(n.indexOf('-') + 1)).toList(), names.toString());
            assertEquals(dumpCounter(names.get(0)) + 1, dumpCounter(names.get(2)),
                "the witness run is dumped straight after the bound: " + names);
            assertEquals(dumpCounter(names.get(2)) + 1, dumpCounter(names.get(4)),
                "the HORN query is dumped straight after the witness run: " + names);
            String bound = Files.readString(dump.resolve(names.get(1)));
            assertTrue(bound.contains("(set-logic QF_LIA)"), "the bound dump is the QF_LIA script:\n" + bound);
            String witness = Files.readString(dump.resolve(names.get(3)));
            assertTrue(witness.startsWith("; Bounded run (VER-019): 8 steps"), "the witness dump is the bounded run:\n" + witness);
            String script = Files.readString(dump.resolve(names.get(5)));
            assertTrue(script.contains("(set-logic HORN)") && script.endsWith("(get-model)"),
                "the dump is the script as sent:\n" + script);
            String reply = Files.readString(dump.resolve(names.get(4)));
            assertTrue(reply.contains("\nunsat\n"), "the dump is the reply as received:\n" + reply);
        }
    }

    /**
     * [VER-013] total budget: a solver that ignores {@code -t} (the stub sleeps for 30 s) is
     * killed by the watchdog derived from the CLAMPED budget, not from the 60 s timeout, and
     * the verdict names the total budget and the phase it cut off.
     */
    @Test
    void totalBudget_clampsEveryProcessToWhatIsLeft() throws IOException {
        var solver = stub("sleeper", VERSION_OK, "exec sleep 30\n");
        long t0 = System.nanoTime();
        var result = SmtVerifier.forNet(chainNet())
            .enumerationMaxClasses(0)
            .initialMarking(m -> m.tokens(P0, 1))
            .property(SmtProperty.placeBound(P1, 0))
            .stateEquationPhase(false)
            .firingBound(false)
            .solver(solver)
            .timeout(Duration.ofSeconds(60))
            .totalBudget(Duration.ofMillis(500))
            .verify();
        long ms = (System.nanoTime() - t0) / 1_000_000;

        var unknown = assertInstanceOf(SmtVerificationResult.Verdict.Unknown.class, result.verdict(), result.report());
        assertEquals("total verification budget of 500 ms exhausted during linear bound",
            unknown.reason());
        // 500 ms plus one watchdog's slack (2 s), with room for a loaded machine: far below the
        // 62 s the unclamped watchdog would wait.
        assertTrue(ms < 15_000, "returned after " + ms + " ms");
    }

    /**
     * [VER-025] is a step of its own under the total budget: with the linear bound off its
     * query is the first one sent, and a solver that never answers is cut off there, by name.
     */
    @Test
    void totalBudget_cutsTheWitnessPhaseOffByName() throws IOException {
        var solver = stub("witness-sleeper", VERSION_OK, "exec sleep 30\n");
        var result = SmtVerifier.forNet(chainNet())
            .enumerationMaxClasses(0)
            .initialMarking(m -> m.tokens(P0, 1))
            .property(SmtProperty.placeBound(P1, 0))
            .linearBound(false)
            .stateEquationPhase(false)
            .firingBound(false)
            .solver(solver)
            .timeout(Duration.ofSeconds(60))
            .totalBudget(Duration.ofMillis(500))
            .verify();
        var unknown = assertInstanceOf(SmtVerificationResult.Verdict.Unknown.class, result.verdict(), result.report());
        assertEquals("total verification budget of 500 ms exhausted during witness phase", unknown.reason());
        // The phase's header keeps its one status line, then the stop is the verdict.
        assertTrue(result.report().contains(
            "  Bounded witness phase (VER-025):\n"
            + "    Status: inconclusive (total verification budget of 500 ms exhausted during witness phase)\n"
            + "\n=== RESULT ===\n\n"
            + "UNKNOWN: total verification budget of 500 ms exhausted during witness phase\n"), result.report());
    }

    /** Answers the bounded run of [VER-025] with {@code witnessReply}, every other script as V5 does. */
    private static String witnessStub(String witnessReply) {
        return "if grep -q '^; Bounded run'; then\n" + witnessReply + "\nelse\n"
            + "echo 'unsat'\necho '(error \"model is not available\")'\n"
            + "echo '(proof (asserted (Reachable 1 0)) (asserted (Reachable 0 1)))'\nfi\n";
    }

    /**
     * [VER-025]: whatever the witness query answers short of a replayed run, the fixpoint query
     * still runs and decides, and the report says why the phase stepped aside.
     */
    @Test
    void ver025_anAnswerWithoutARunFallsThroughWithItsReason() throws IOException {
        record Case(String name, String reply, String status) {}
        for (var c : List.of(
                new Case("unknown", "echo unknown",
                    "    Status: inconclusive (the bounded run at depth 8 answered unknown)\n"),
                new Case("unsat", "echo unsat",
                    "    Status: no run of at most 8 steps reaches a violation (not a proof)\n"),
                // A model that fires nothing: p1 stays empty, so it is not a run to a violation.
                new Case("no-replay", "echo sat\necho '((define-fun s0 () Int 1))'",
                    "    Status: inconclusive (the bounded run did not replay under the exact semantics)\n"),
                new Case("error", "echo '(error \"line 1 column 1: boom\")'\necho sat",
                    "    Status: inconclusive (z3 reported an error: "))) {
            var result = verify(stub("witness-" + c.name(), VERSION_OK, witnessStub(c.reply())),
                SmtProperty.placeBound(P1, 0));
            assertInstanceOf(SmtVerificationResult.Verdict.Violated.class, result.verdict(), c.name() + "\n" + result.report());
            assertTrue(result.report().contains("  Bounded witness phase (VER-025):\n" + c.status()),
                c.name() + "\n" + result.report());
            assertTrue(result.report().contains("Status: SAT (counterexample found)"), c.name() + "\n" + result.report());
        }
    }

    /** A spent budget starts no process: the stub would leave a marker file if it ran. */
    @Test
    void totalBudget_spentStartsNoProcess() throws Exception {
        Path marker = root.resolve("spent").resolve("ran");
        var solver = stub("spent", VERSION_OK, "touch '" + marker.toAbsolutePath() + "'\necho unsat\n");

        var expired = new org.libpetri.core.internal.VerificationDeadline(0);
        assertThrows(org.libpetri.core.internal.VerificationDeadline.Exhausted.class, () ->
            ScopedValue.where(org.libpetri.core.internal.VerificationDeadline.carrier(), expired)
                .call(() -> solver.run("(check-sat)", "probe", Duration.ofSeconds(5), List.of())));
        assertFalse(Files.exists(marker), "the transport started a process on a spent budget");

        var result = SmtVerifier.forNet(chainNet())
            .enumerationMaxClasses(0)
            .initialMarking(m -> m.tokens(P0, 1))
            .property(SmtProperty.placeBound(P1, 0))
            .solver(solver)
            .totalBudget(Duration.ZERO)
            .verify();
        var unknown = assertInstanceOf(SmtVerificationResult.Verdict.Unknown.class, result.verdict(), result.report());
        assertTrue(unknown.reason().startsWith("total verification budget of 0 ms exhausted during "), unknown.reason());
        assertFalse(Files.exists(marker), "verify() started a process on a spent budget");
    }

    /** The zero-padded counter a dump file name starts with ({@code 012-horn.smt2} is 12). */
    private static int dumpCounter(String name) {
        return Integer.parseInt(name.substring(0, name.indexOf('-')));
    }
}
