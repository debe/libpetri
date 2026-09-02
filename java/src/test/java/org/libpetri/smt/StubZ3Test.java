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
            .initialMarking(m -> tokens.forEach(m::tokens))
            .property(property)
            .environmentMode(EnvironmentAnalysisMode.ignore())
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
            var names = files.map(p -> p.getFileName().toString()).sorted().toList();
            assertEquals(2, names.size(), "one script and one reply: " + names);
            assertTrue(names.get(0).endsWith("-horn.out") && names.get(1).endsWith("-horn.smt2"), names.toString());
            String script = Files.readString(dump.resolve(names.get(1)));
            assertTrue(script.contains("(set-logic HORN)") && script.endsWith("(get-model)"),
                "the dump is the script as sent:\n" + script);
            String reply = Files.readString(dump.resolve(names.get(0)));
            assertTrue(reply.contains("\nunsat\n"), "the dump is the reply as received:\n" + reply);
        }
    }
}
