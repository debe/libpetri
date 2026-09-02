package org.libpetri.smt.z3;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.time.Duration;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * A resolved z3 executable: where it is and which version answered the probe
 * (VER-013).
 *
 * <p>The executable is {@code z3} on {@code PATH} unless {@link #Z3_ENV} names another.
 * It is probed once per verification with {@code --version} and refused below
 * {@link #MIN_VERSION}; a missing or too-old binary surfaces as an {@code Unknown}
 * verdict whose reason names the command and the environment variable, never as an
 * exception out of {@code verify()}. Setting {@link #DUMP_ENV} to a directory writes
 * every script and reply there ({@code NNN-<phase>.smt2}, {@code .out}, and
 * {@code .err} when stderr is not empty), which is how a solver reply is reproduced
 * outside the pipeline.
 *
 * @param program the executable as resolved (a path, or a bare name on {@code PATH})
 * @param version the version the probe reported
 * @param dumpDir where scripts and replies are written, or {@code null} for no dump
 */
public record Z3Solver(String program, Z3Version version, Path dumpDir) {

    /** Environment variable naming the z3 executable (default: {@code z3} on {@code PATH}). */
    public static final String Z3_ENV = "LIBPETRI_Z3";

    /** Environment variable naming a directory that receives every script and reply. */
    public static final String DUMP_ENV = "LIBPETRI_SMT_DUMP";

    /**
     * Oldest z3 the transport accepts: {@code -t}/{@code -T}, Spacer as
     * {@code fp.engine}, and the {@code (get-model)} / {@code (get-proof)} printers the
     * decoders read are stable from here.
     */
    public static final Z3Version MIN_VERSION = new Z3Version(4, 8, 0);

    /** No usable z3 resolved; the message is the {@code Unknown} reason the verifier reports. */
    public static final class Z3Unavailable extends Exception {
        Z3Unavailable(String message) {
            super(message);
        }
    }

    public Z3Solver {
        Objects.requireNonNull(program);
        Objects.requireNonNull(version);
    }

    /**
     * Resolves the executable named by {@link #Z3_ENV}, or {@code z3} on {@code PATH},
     * probes its version, and reads {@link #DUMP_ENV}.
     */
    public static Z3Solver resolve() throws Z3Unavailable {
        return resolve(System.getenv());
    }

    /** {@link #resolve()} against an explicit environment (unit-testable). */
    public static Z3Solver resolve(Map<String, String> env) throws Z3Unavailable {
        String program = env.get(Z3_ENV);
        if (program == null || program.isBlank()) {
            program = "z3";
        }
        String dump = env.get(DUMP_ENV);
        Path dumpDir = dump == null || dump.isBlank() ? null : Path.of(dump);
        return at(program).withDumpDir(dumpDir);
    }

    /** Resolves a specific executable (tests point this at a stub). No dump directory. */
    public static Z3Solver at(String program) throws Z3Unavailable {
        Path located = Z3Process.locate(program);
        if (located == null) {
            throw new Z3Unavailable("z3 binary not found: " + program
                + "; install z3 >= " + MIN_VERSION + " or set " + Z3_ENV);
        }
        Z3Process.Reply reply;
        try {
            reply = Z3Process.run(located.toString(), List.of("--version"), "",
                Z3Process.VERSION_PROBE_MS);
        } catch (Z3Process.Z3ProcessException e) {
            throw new Z3Unavailable(e.getMessage());
        }
        if (reply.exit() instanceof Z3Process.Exit.Killed) {
            throw new Z3Unavailable(program + " --version did not answer within "
                + Z3Process.VERSION_PROBE_MS + " ms");
        }
        Z3Version version = Z3Version.parse(reply.stdout());
        if (version == null) {
            String line = (reply.stdout() + "\n" + reply.stderr()).lines()
                .map(String::strip)
                .filter(l -> !l.isEmpty())
                .findFirst()
                .orElse("");
            throw new Z3Unavailable("z3 --version did not report a version: " + line);
        }
        if (version.compareTo(MIN_VERSION) < 0) {
            throw new Z3Unavailable("z3 " + version + " is older than the minimum " + MIN_VERSION);
        }
        return new Z3Solver(located.toString(), version, null);
    }

    /** The same solver writing every script and reply under {@code dir} ({@code null} = off). */
    public Z3Solver withDumpDir(Path dir) {
        return new Z3Solver(program, version, dir);
    }

    /**
     * Runs one script through one z3 process and returns the raw reply. {@code phase}
     * names the dump files; {@code extraArgs} follow the standard argument list
     * ({@link Z3Process#argsFor}). The only exception is a failed spawn or a broken
     * wait: a solver that printed nothing, errored, timed out or was killed still
     * comes back as a reply for the caller to classify
     * ({@link Z3Process#failureReason}).
     */
    public Z3Process.Reply run(String script, String phase, Duration timeout, List<String> extraArgs)
            throws Z3Process.Z3ProcessException {
        long timeoutMs = timeoutMs(timeout);
        Path base = dumpSlot(phase, script);
        var args = new ArrayList<>(Z3Process.argsFor(timeoutMs));
        args.addAll(extraArgs);
        Z3Process.Reply reply = Z3Process.run(program, args, script, Z3Process.watchdogMs(timeoutMs));
        if (base != null) {
            write(base.resolveSibling(base.getFileName() + ".out"), reply.stdout());
            if (!reply.stderr().isBlank()) {
                write(base.resolveSibling(base.getFileName() + ".err"), reply.stderr());
            }
        }
        return reply;
    }

    /** The soft budget in milliseconds: at least one, so {@code -t:0} never means "forever". */
    static long timeoutMs(Duration timeout) {
        if (timeout == null) {
            return 1;
        }
        long ms;
        try {
            ms = timeout.toMillis();
        } catch (ArithmeticException _) {
            ms = Long.MAX_VALUE / 4;
        }
        return Math.max(1, ms);
    }

    private Path dumpSlot(String phase, String script) {
        if (dumpDir == null) {
            return null;
        }
        int n = Z3Process.DUMP_COUNTER.incrementAndGet();
        try {
            Files.createDirectories(dumpDir);
        } catch (IOException _) {
            return null;
        }
        Path base = dumpDir.resolve(String.format("%03d-%s", n, phase));
        write(base.resolveSibling(base.getFileName() + ".smt2"), script);
        return base;
    }

    private static void write(Path file, String text) {
        try {
            Files.writeString(file, text, StandardCharsets.UTF_8);
        } catch (IOException _) {
            // Dump failures are ignored: the dump is a diagnostic, never the pipeline.
        }
    }
}
