package org.libpetri.smt.z3;

import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.FutureTask;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicInteger;

/**
 * The z3 process transport (VER-013).
 *
 * <p>Every SMT query is one {@code z3} process: the SMT-LIB2 script goes to its stdin in
 * a single write, stdin is closed so the solver sees end-of-file, and both output
 * streams are drained concurrently while a wall-clock watchdog waits. The child is
 * destroyed and reaped on every exit path, so a wedged solver can never outlive the
 * query that started it, and no solver state survives between queries, so concurrent
 * verifiers in one JVM are independent.
 *
 * <p>Timeouts are per invocation: {@code -t:<ms>} asks z3 to answer {@code unknown}
 * after the soft budget, {@code -T:<s>} (the budget plus {@link #GRACE_MS}, rounded
 * up) makes z3 print {@code timeout} and exit on its own, and the watchdog at the
 * budget plus twice the grace kills whatever ignored both. The Java, TypeScript and
 * Rust transports pass byte-identical argument lists and classify replies identically
 * ({@link SmtText#classifyFirstLine}, {@link SmtText#timeoutLine},
 * {@link SmtText#errorLine}, {@link #failureReason}).
 */
public final class Z3Process {

    private Z3Process() {}

    /** Slack between the soft budget and the hard backstops, in milliseconds. */
    public static final long GRACE_MS = 1_000;

    /** How long the {@code --version} probe may take before it counts as unavailable. */
    static final long VERSION_PROBE_MS = 5_000;

    /** Process-wide counter for {@link Z3Solver#DUMP_ENV} file names (not solver state). */
    static final AtomicInteger DUMP_COUNTER = new AtomicInteger();

    /** The standard argument list: {@code -smt2 -in -t:<ms> -T:<s>}. */
    public static List<String> argsFor(long timeoutMs) {
        return List.of("-smt2", "-in", "-t:" + timeoutMs, "-T:" + hardTimeoutSecs(timeoutMs));
    }

    /** The {@code -T:} backstop in whole seconds: the soft budget plus the grace, rounded up. */
    public static long hardTimeoutSecs(long timeoutMs) {
        return Math.max(1, Math.ceilDiv(timeoutMs + GRACE_MS, 1000));
    }

    /** When the watchdog kills the process: the soft budget plus twice the grace. */
    public static long watchdogMs(long timeoutMs) {
        return timeoutMs + 2 * GRACE_MS;
    }

    /** How a z3 process ended. */
    public sealed interface Exit {
        /** The process exited by itself with {@code code}. */
        record Exited(int code) implements Exit {}

        /** The watchdog killed it. */
        record Killed() implements Exit {}
    }

    /**
     * The raw reply of one z3 run.
     *
     * @param stdout everything the process wrote to stdout
     * @param stderr everything the process wrote to stderr
     * @param exit   how it ended
     */
    public record Reply(String stdout, String stderr, Exit exit) {
        /** True when the process exited with status 0. */
        public boolean success() {
            return exit instanceof Exit.Exited(int code) && code == 0;
        }
    }

    /** The process could not be started or waited for (a spawn failure, an interrupt). */
    public static final class Z3ProcessException extends Exception {
        Z3ProcessException(String message) {
            super(message);
        }
    }

    /**
     * Why a reply carries no {@code (check-sat)} answer, in the order the transport
     * contract fixes: the {@code -T} backstop, the watchdog, an {@code (error …)} on
     * either stream, anything on stderr, and finally the unexpected stdout itself.
     */
    public static String failureReason(Reply reply, long timeoutMs) {
        if (SmtText.timeoutLine(reply.stdout())) {
            return "z3 hard timeout after " + hardTimeoutSecs(timeoutMs) + "s";
        }
        if (reply.exit() instanceof Exit.Killed) {
            return "z3 did not exit within " + watchdogMs(timeoutMs) + " ms and was killed";
        }
        String err = SmtText.errorLine(reply.stdout());
        if (err == null) {
            err = SmtText.errorLine(reply.stderr());
        }
        if (err != null) {
            return "Z3 error: " + err;
        }
        String stderr = reply.stderr().strip();
        if (!stderr.isEmpty()) {
            return "Z3 error: " + stderr;
        }
        return "Unexpected Z3 output: " + reply.stdout().strip();
    }

    /**
     * Where {@code program} resolves to: the path itself when it names a file, else the
     * first executable of that name on {@code PATH} ({@code .exe} tried on Windows);
     * {@code null} when nothing resolves.
     */
    static Path locate(String program) {
        Path direct = Path.of(program);
        if (direct.getNameCount() > 1 || direct.isAbsolute()) {
            return Files.isRegularFile(direct) ? direct : null;
        }
        String path = System.getenv("PATH");
        if (path == null) {
            return null;
        }
        boolean windows = System.getProperty("os.name", "").toLowerCase().contains("win");
        for (String dir : path.split(java.io.File.pathSeparator)) {
            if (dir.isEmpty()) {
                continue;
            }
            Path candidate = Path.of(dir, program);
            if (Files.isRegularFile(candidate) && Files.isExecutable(candidate)) {
                return candidate;
            }
            if (windows) {
                Path exe = Path.of(dir, program + ".exe");
                if (Files.isRegularFile(exe)) {
                    return exe;
                }
            }
        }
        return null;
    }

    /**
     * Runs {@code program} with {@code args}, feeding {@code script} on stdin, and
     * returns the raw reply. A solver that printed nothing, errored, timed out or was
     * killed still comes back as a reply for the caller to classify; the only
     * exception is a process that could not be started or waited for.
     */
    static Reply run(String program, List<String> args, String script, long watchdogMs)
            throws Z3ProcessException {
        var command = new ArrayList<String>(args.size() + 1);
        command.add(program);
        command.addAll(args);
        Process process;
        try {
            process = new ProcessBuilder(command).redirectErrorStream(false).start();
        } catch (IOException e) {
            throw new Z3ProcessException("failed to spawn " + program + ": " + e.getMessage());
        }
        try {
            // Drains start before anything is written so a reply larger than the pipe
            // buffer cannot stall the solver.
            var stdout = drain(process.getInputStream());
            var stderr = drain(process.getErrorStream());
            // The whole script in one write, then EOF. A solver that exited early
            // (parse error, `-T` expiry) closes the pipe under us; that is not a
            // failure of the transport, the reply says what happened.
            try (var stdin = process.getOutputStream()) {
                stdin.write(script.getBytes(StandardCharsets.UTF_8));
            } catch (IOException _) {
                // see above
            }
            Exit exit;
            try {
                if (process.waitFor(watchdogMs, TimeUnit.MILLISECONDS)) {
                    exit = new Exit.Exited(process.exitValue());
                } else {
                    process.destroyForcibly();
                    process.waitFor();
                    exit = new Exit.Killed();
                }
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
                throw new Z3ProcessException("interrupted while waiting for " + program);
            }
            return new Reply(finish(stdout), finish(stderr), exit);
        } finally {
            if (process.isAlive()) {
                process.destroyForcibly();
            }
        }
    }

    private static FutureTask<String> drain(InputStream stream) {
        var task = new FutureTask<>(() -> new String(stream.readAllBytes(), StandardCharsets.UTF_8));
        Thread.ofVirtual().start(task);
        return task;
    }

    private static String finish(FutureTask<String> drain) {
        try {
            return drain.get();
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            return "";
        } catch (java.util.concurrent.ExecutionException _) {
            return "";
        }
    }
}
