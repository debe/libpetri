//! The z3 process transport ([VER-013]).
//!
//! Every SMT query is one `z3` process: the SMT-LIB2 script goes to its stdin
//! in a single write, stdin is closed so the solver sees EOF, and both output
//! streams are drained concurrently while a wall-clock watchdog waits. The
//! child is killed and reaped on every exit path, so a wedged solver can never
//! outlive the query that started it, and no solver state survives between
//! queries, so concurrent verifiers in one process are independent.
//!
//! The executable is `z3` on `PATH` unless [`Z3_ENV`] names another one. It is
//! probed once per verification with `--version` and refused below
//! [`MIN_Z3_VERSION`]; a missing or too-old binary surfaces as an `Unknown`
//! verdict whose reason names the command and the environment variable, never
//! as a panic. Setting [`DUMP_ENV`] to a directory writes every script and
//! reply there (`NNN-<phase>.smt2`, `.out`, and `.err` when stderr is not
//! empty), which is how a solver reply is reproduced outside the pipeline.
//!
//! Timeouts are per invocation: `-t:<ms>` asks z3 to answer `unknown` after
//! the soft budget, `-T:<s>` (the budget plus [`GRACE_MS`], rounded up) makes
//! z3 print `timeout` and exit on its own, and the watchdog at the budget plus
//! twice the grace kills whatever ignored both. The Java, TypeScript and Rust
//! transports pass byte-identical argument lists and classify replies
//! identically ([`classify_first_line`], [`timeout_line`], [`error_line`],
//! [`failure_reason`]).

use std::ffi::{OsStr, OsString};
use std::fmt;
use std::fs;
use std::io::{Read, Write};
use std::path::PathBuf;
use std::process::{Child, Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

/// Environment variable naming the z3 executable (default: `z3` on `PATH`).
pub const Z3_ENV: &str = "LIBPETRI_Z3";
/// Environment variable naming a directory that receives every script and reply.
pub const DUMP_ENV: &str = "LIBPETRI_SMT_DUMP";
/// Oldest z3 the transport accepts: `-t`/`-T`, Spacer as `fp.engine`, and the
/// `(get-model)` / `(get-proof)` printers the decoders read are stable from here.
pub const MIN_Z3_VERSION: Z3Version = Z3Version(4, 8, 0);
/// Slack between the soft budget and the hard backstops, in milliseconds.
pub const GRACE_MS: u64 = 1_000;
/// How long the `--version` probe may take before it counts as unavailable.
const VERSION_PROBE_MS: u64 = 5_000;
/// Watchdog polling interval.
const POLL: Duration = Duration::from_millis(10);

/// Process-wide counter for [`DUMP_ENV`] file names. Not solver state: it only
/// numbers dump files.
static DUMP_COUNTER: AtomicUsize = AtomicUsize::new(0);

/// A z3 release version, ordered numerically.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Z3Version(pub u32, pub u32, pub u32);

impl fmt::Display for Z3Version {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}.{}", self.0, self.1, self.2)
    }
}

/// Parses the version out of a `z3 --version` reply (`Z3 version 4.16.0 - 64 bit`).
pub fn parse_version(text: &str) -> Option<Z3Version> {
    let start = text.find("Z3 version ")? + "Z3 version ".len();
    let token = text[start..].split_whitespace().next()?;
    let mut parts = token.split('.').map(|p| p.parse::<u32>().ok());
    let major = parts.next()??;
    let minor = parts.next()??;
    let patch = parts.next().flatten().unwrap_or(0);
    Some(Z3Version(major, minor, patch))
}

/// A resolved z3 executable: where it is and which version answered the probe.
#[derive(Debug, Clone)]
pub struct Z3Solver {
    program: OsString,
    version: Z3Version,
}

impl Z3Solver {
    /// Resolves the executable named by [`Z3_ENV`], or `z3` on `PATH`, and
    /// probes its version. The error is the `Unknown` reason the verifier reports.
    pub fn resolve() -> Result<Self, String> {
        let program = std::env::var_os(Z3_ENV)
            .filter(|v| !v.is_empty())
            .unwrap_or_else(|| OsString::from("z3"));
        Self::at(program)
    }

    /// Resolves a specific executable (tests point this at a stub).
    pub fn at(program: impl Into<OsString>) -> Result<Self, String> {
        let program = program.into();
        let version = probe_version(&program)?;
        if version < MIN_Z3_VERSION {
            return Err(format!(
                "z3 {version} is older than the minimum {MIN_Z3_VERSION}"
            ));
        }
        Ok(Self { program, version })
    }

    /// The executable this solver runs.
    pub fn program(&self) -> &OsStr {
        &self.program
    }

    /// The version the probe reported.
    pub fn version(&self) -> Z3Version {
        self.version
    }

    /// Runs one script through one z3 process and returns the raw reply.
    /// `phase` names the dump files; `extra_args` follow the standard argument
    /// list ([`args_for`]). The only error is a failed spawn or a broken wait:
    /// a solver that printed nothing, errored, timed out or was killed still
    /// comes back as a reply for the caller to classify ([`failure_reason`]).
    pub fn run(
        &self,
        script: &str,
        phase: &str,
        timeout_ms: u64,
        extra_args: &[&str],
    ) -> Result<Z3Reply, String> {
        let dump = dump_slot(phase, script);
        let child = Command::new(&self.program)
            .args(args_for(timeout_ms).iter())
            .args(extra_args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|e| format!("failed to spawn {}: {e}", self.program.to_string_lossy()))?;
        let mut guard = ChildGuard(child);
        let drains = Drains::start(&mut guard.0);
        // The whole script in one write, then EOF. A solver that exited early
        // (parse error, `-T` expiry) closes the pipe under us; that is not a
        // failure of the transport, the reply says what happened.
        if let Some(mut stdin) = guard.0.stdin.take() {
            let _ = stdin.write_all(script.as_bytes());
        }
        let exit = wait_with_watchdog(&mut guard, watchdog_ms(timeout_ms))?;
        let (stdout, stderr) = drains.finish();
        if let Some(base) = dump {
            let _ = fs::write(base.with_extension("out"), &stdout);
            if !stderr.trim().is_empty() {
                let _ = fs::write(base.with_extension("err"), &stderr);
            }
        }
        Ok(Z3Reply {
            stdout,
            stderr,
            exit,
        })
    }
}

/// The standard argument list: `-smt2 -in -t:<ms> -T:<s>`.
pub fn args_for(timeout_ms: u64) -> [String; 4] {
    [
        "-smt2".to_string(),
        "-in".to_string(),
        format!("-t:{timeout_ms}"),
        format!("-T:{}", hard_timeout_secs(timeout_ms)),
    ]
}

/// The `-T:` backstop in whole seconds: the soft budget plus the grace, rounded up.
pub fn hard_timeout_secs(timeout_ms: u64) -> u64 {
    (timeout_ms + GRACE_MS).div_ceil(1000).max(1)
}

/// When the watchdog kills the process: the soft budget plus twice the grace.
pub fn watchdog_ms(timeout_ms: u64) -> u64 {
    timeout_ms + 2 * GRACE_MS
}

/// How a z3 process ended.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Z3Exit {
    /// The process exited by itself; `None` when a signal ended it.
    Exited(Option<i32>),
    /// The watchdog killed it.
    Killed,
}

/// The raw reply of one z3 run.
#[derive(Debug, Clone)]
pub struct Z3Reply {
    pub stdout: String,
    pub stderr: String,
    pub exit: Z3Exit,
}

impl Z3Reply {
    /// True when the process exited with status 0.
    pub fn success(&self) -> bool {
        self.exit == Z3Exit::Exited(Some(0))
    }
}

/// The first trimmed stdout line that is a `(check-sat)` answer, if any. The
/// answer is a LINE anywhere in the reply, not the first bytes: a build is free
/// to print a warning first, and a HORN script that asks for both a proof and a
/// model always gets one `(error …)` line back.
pub fn classify_first_line(stdout: &str) -> Option<&str> {
    stdout
        .lines()
        .map(str::trim)
        .find(|l| matches!(*l, "sat" | "unsat" | "unknown"))
}

/// True when z3's `-T` backstop fired: it prints the single line `timeout`.
pub fn timeout_line(stdout: &str) -> bool {
    stdout.lines().map(str::trim).any(|l| l == "timeout")
}

/// The first `(error …)` line in a z3 stream, trimmed.
pub fn error_line(text: &str) -> Option<String> {
    text.lines()
        .map(str::trim)
        .find(|l| l.starts_with("(error"))
        .map(str::to_string)
}

/// Why a reply carries no `(check-sat)` answer, in the order the transport
/// contract fixes: the `-T` backstop, the watchdog, an `(error …)` on either
/// stream, anything on stderr, and finally the unexpected stdout itself.
pub fn failure_reason(reply: &Z3Reply, timeout_ms: u64) -> String {
    if timeout_line(&reply.stdout) {
        return format!("z3 hard timeout after {}s", hard_timeout_secs(timeout_ms));
    }
    if reply.exit == Z3Exit::Killed {
        return format!(
            "z3 did not exit within {} ms and was killed",
            watchdog_ms(timeout_ms)
        );
    }
    if let Some(err) = error_line(&reply.stdout).or_else(|| error_line(&reply.stderr)) {
        return format!("Z3 error: {err}");
    }
    let stderr = reply.stderr.trim();
    if !stderr.is_empty() {
        return format!("Z3 error: {stderr}");
    }
    format!("Unexpected Z3 output: {}", reply.stdout.trim())
}

/// Kills and reaps the child when dropped early (an error return, a panic).
struct ChildGuard(Child);

impl Drop for ChildGuard {
    fn drop(&mut self) {
        // Both calls are no-ops on a child that already exited and was waited.
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

/// Reader threads for stdout and stderr, started before anything is written
/// so a reply larger than the pipe buffer cannot stall the solver.
struct Drains {
    stdout: Option<JoinHandle<String>>,
    stderr: Option<JoinHandle<String>>,
}

impl Drains {
    fn start(child: &mut Child) -> Self {
        Self {
            stdout: child.stdout.take().map(|s| thread::spawn(move || read_all(s))),
            stderr: child.stderr.take().map(|s| thread::spawn(move || read_all(s))),
        }
    }

    fn finish(self) -> (String, String) {
        let join = |h: Option<JoinHandle<String>>| {
            h.and_then(|h| h.join().ok()).unwrap_or_default()
        };
        (join(self.stdout), join(self.stderr))
    }
}

fn read_all(mut reader: impl Read) -> String {
    let mut buf = Vec::new();
    let _ = reader.read_to_end(&mut buf);
    String::from_utf8_lossy(&buf).into_owned()
}

/// Polls the child until it exits or `budget_ms` elapses, then kills it.
fn wait_with_watchdog(guard: &mut ChildGuard, budget_ms: u64) -> Result<Z3Exit, String> {
    let deadline = Instant::now() + Duration::from_millis(budget_ms);
    loop {
        match guard.0.try_wait() {
            Ok(Some(status)) => return Ok(Z3Exit::Exited(status.code())),
            Ok(None) if Instant::now() >= deadline => {
                let _ = guard.0.kill();
                let _ = guard.0.wait();
                return Ok(Z3Exit::Killed);
            }
            Ok(None) => thread::sleep(POLL),
            Err(e) => return Err(format!("z3 process error: {e}")),
        }
    }
}

/// Runs `<program> --version` under its own watchdog and parses the reply.
fn probe_version(program: &OsStr) -> Result<Z3Version, String> {
    let shown = program.to_string_lossy();
    let child = match Command::new(program)
        .arg("--version")
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
    {
        Ok(child) => child,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            return Err(format!(
                "z3 binary not found: {shown}; install z3 >= {MIN_Z3_VERSION} or set {Z3_ENV}"
            ));
        }
        Err(e) => return Err(format!("failed to spawn {shown}: {e}")),
    };
    let mut guard = ChildGuard(child);
    let drains = Drains::start(&mut guard.0);
    let exit = wait_with_watchdog(&mut guard, VERSION_PROBE_MS)?;
    let (stdout, stderr) = drains.finish();
    if exit == Z3Exit::Killed {
        return Err(format!(
            "{shown} --version did not answer within {VERSION_PROBE_MS} ms"
        ));
    }
    match parse_version(&stdout) {
        Some(version) => Ok(version),
        None => {
            let line = stdout
                .lines()
                .chain(stderr.lines())
                .map(str::trim)
                .find(|l| !l.is_empty())
                .unwrap_or("");
            Err(format!("z3 --version did not report a version: {line}"))
        }
    }
}

/// Writes the script to the [`DUMP_ENV`] directory and returns the file base
/// (`<dir>/NNN-<phase>`) for the reply files, or `None` when dumping is off.
fn dump_slot(phase: &str, script: &str) -> Option<PathBuf> {
    let dir = std::env::var_os(DUMP_ENV)
        .filter(|v| !v.is_empty())
        .map(PathBuf::from)?;
    let n = DUMP_COUNTER.fetch_add(1, Ordering::SeqCst) + 1;
    let _ = fs::create_dir_all(&dir);
    let base = dir.join(format!("{n:03}-{phase}"));
    let _ = fs::write(base.with_extension("smt2"), script);
    Some(base)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn standard_argument_list_is_soft_then_hard_timeout() {
        assert_eq!(
            args_for(30_000),
            ["-smt2", "-in", "-t:30000", "-T:31"].map(String::from)
        );
        // Sub-second budgets never round the backstop down to zero.
        assert_eq!(args_for(1)[3], "-T:2");
        assert_eq!(hard_timeout_secs(0), 1);
        assert_eq!(watchdog_ms(200), 2_200);
    }

    #[test]
    fn version_parsing_and_floor() {
        assert_eq!(
            parse_version("Z3 version 4.16.0 - 64 bit"),
            Some(Z3Version(4, 16, 0))
        );
        assert_eq!(
            parse_version("WARNING: something\nZ3 version 4.8.12 - 64 bit\n"),
            Some(Z3Version(4, 8, 12))
        );
        assert_eq!(parse_version("Z3 version 4.8"), Some(Z3Version(4, 8, 0)));
        assert_eq!(parse_version("version 4.8.0"), None);
        assert_eq!(parse_version("Z3 version four"), None);
        assert!(Z3Version(4, 7, 1) < MIN_Z3_VERSION);
        assert!(Z3Version(4, 8, 0) >= MIN_Z3_VERSION);
        assert!(Z3Version(5, 0, 0) > Z3Version(4, 16, 0));
        assert_eq!(Z3Version(4, 16, 0).to_string(), "4.16.0");
    }

    fn reply(stdout: &str, stderr: &str, exit: Z3Exit) -> Z3Reply {
        Z3Reply {
            stdout: stdout.to_string(),
            stderr: stderr.to_string(),
            exit,
        }
    }

    #[test]
    fn reply_classification_table() {
        let ok = Z3Exit::Exited(Some(0));
        assert_eq!(classify_first_line("WARNING: x\nunsat\n(error \"m\")"), Some("unsat"));
        assert_eq!(classify_first_line("  sat  \n(model)"), Some("sat"));
        assert_eq!(classify_first_line("timeout"), None);
        assert!(timeout_line("timeout\n"));
        assert!(!timeout_line("unknown\n(error \"timeout\")"));
        assert_eq!(
            error_line("sat\n(error \"line 3: x\")"),
            Some("(error \"line 3: x\")".to_string())
        );

        assert_eq!(
            failure_reason(&reply("timeout\n", "", ok), 5_000),
            "z3 hard timeout after 6s"
        );
        assert_eq!(
            failure_reason(&reply("", "", Z3Exit::Killed), 200),
            "z3 did not exit within 2200 ms and was killed"
        );
        assert_eq!(
            failure_reason(&reply("(error \"line 1: bad\")", "", ok), 1),
            "Z3 error: (error \"line 1: bad\")"
        );
        assert_eq!(
            failure_reason(&reply("", "(error \"on stderr\")", ok), 1),
            "Z3 error: (error \"on stderr\")"
        );
        assert_eq!(
            failure_reason(&reply("", "segfault\n", Z3Exit::Exited(None)), 1),
            "Z3 error: segfault"
        );
        assert_eq!(
            failure_reason(&reply("garbage\n", "", ok), 1),
            "Unexpected Z3 output: garbage"
        );
        // The backstop wins over the kill: a `timeout` line is z3's own answer.
        assert_eq!(
            failure_reason(&reply("timeout", "", Z3Exit::Killed), 1_000),
            "z3 hard timeout after 2s"
        );
    }

    #[test]
    fn missing_binary_names_the_command_and_the_env_var() {
        let err = Z3Solver::at("/nonexistent/libpetri-z3").unwrap_err();
        assert_eq!(
            err,
            "z3 binary not found: /nonexistent/libpetri-z3; install z3 >= 4.8.0 or set LIBPETRI_Z3"
        );
    }
}
