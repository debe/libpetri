//! Cross-language conformance against the verified Lean reference
//! (`spec/verification-fixtures/conformance/README.md`).
//!
//! Every net of `nets/` is loaded through the schema loader (`common/net_json.rs`)
//! and each of its properties is verified on the four route setups of
//! `route_agreement.rs`:
//!
//! * `enum`   — the default pipeline, bounded enumeration first ([VER-017]);
//! * `smt+lb` — enumeration off (budget 0), linear bound on ([VER-015]), phases on;
//! * `smt-lb` — enumeration off, linear bound off, phases on;
//! * `ic3`    — enumeration off, linear bound and both VER-018/019 phases off.
//!
//! Each verdict is held against `expected/<id>.json`, which only `lake exe
//! reference` writes (`scripts/conformance-corpus.py --update`). The README's
//! conformance rule, per (net, property, route):
//! 1. never `Proven` where the reference says `violated`;
//! 2. never `Violated` where the reference says `proven` (fails loudly either way:
//!    if the dumped trace replays under the reference, the reference is falsified);
//! 3. every `Violated` carries a trace (`[]` when the initial marking violates) and
//!    every trace replays under the reference firing rule — the replay checked by
//!    `scripts/conformance-replay.py`, which runs this test with
//!    `LIBPETRI_CONFORMANCE_DUMP` set and replays each dump with
//!    `lake exe reference --replay`;
//! 4. `Unknown` is always allowed, and counted.
//!
//! The four setups run twice. The **atomic** pass (`assume_atomic_firing(true)`) reads
//! every firing as one step, as the reference does, and is held to all four rules. The
//! **default** pass leaves the in-flight split of [VER-004] on, as a caller gets it, and
//! is held to rules 1, 3 and 4 only: the split adds the executor's runs with an action in
//! flight, which the atomic reference does not have, so a `Violated` where the reference
//! says `proven` is allowed there. A default-pass trace on a net the split left atomic is
//! dumped for the reference replay with the atomic ones; a trace of a split net names
//! `complete:<t>` steps the reference cannot fire, and is counted instead, with whether
//! the verifier's own abstract replay confirmed it.
//!
//! Knobs (all optional):
//! * `LIBPETRI_CONFORMANCE_EXPECTED=<dir>` — read verdicts from `<dir>` instead of
//!   `expected/` (for testing this harness; the corpus's own come from Lean only);
//! * `LIBPETRI_CONFORMANCE_REQUIRE=1` — fail instead of skipping when no expected
//!   verdicts exist (CI's conformance job sets it);
//! * `LIBPETRI_CONFORMANCE_DUMP=<dir>` — write `<dir>/<id>.traces.json`,
//!   `[{"property": id, "trace": [names]}]`, for every net with a `Violated` trace;
//! * `LIBPETRI_CONFORMANCE_FILTER=<substring>` — only nets whose id contains it;
//! * `LIBPETRI_CONFORMANCE_THREADS=<n>` — worker threads (default: available parallelism);
//! * `LIBPETRI_CONFORMANCE_VERBOSE=1` — print every `Unknown` where the reference decided.

#![cfg(feature = "z3")]

#[path = "common/json.rs"]
mod json;
#[path = "common/net_json.rs"]
mod net_json;

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

use json::{Json, parse_json};
use net_json::{CorpusNet, CorpusProperty, load_net};

use libpetri_verification::result::{Verdict, VerificationResult};
use libpetri_verification::smt_verifier::{SmtVerifier, z3_available};

/// Class budget of the enumeration route in the `enum` setup (as route_agreement).
const ENUM_BUDGET: usize = 5_000;

#[derive(Clone, Copy)]
struct Config {
    name: &'static str,
    enum_budget: usize,
    linear_bound: bool,
    phases: bool,
    /// The atomic pass (all four rules) or the default, split pass (rules 1, 3, 4).
    atomic: bool,
}

/// Number of route setups: four, each in the atomic and in the default pass.
const SETUPS: usize = 8;

const CONFIGS: [Config; SETUPS] = [
    Config { name: "enum", enum_budget: ENUM_BUDGET, linear_bound: true, phases: true, atomic: true },
    Config { name: "smt+lb", enum_budget: 0, linear_bound: true, phases: true, atomic: true },
    Config { name: "smt-lb", enum_budget: 0, linear_bound: false, phases: true, atomic: true },
    Config { name: "ic3", enum_budget: 0, linear_bound: false, phases: false, atomic: true },
    Config { name: "enum/split", enum_budget: ENUM_BUDGET, linear_bound: true, phases: true, atomic: false },
    Config { name: "smt+lb/split", enum_budget: 0, linear_bound: true, phases: true, atomic: false },
    Config { name: "smt-lb/split", enum_budget: 0, linear_bound: false, phases: true, atomic: false },
    Config { name: "ic3/split", enum_budget: 0, linear_bound: false, phases: false, atomic: false },
];

fn run_config(net: &CorpusNet, prop: &CorpusProperty, cfg: Config) -> VerificationResult {
    SmtVerifier::for_net(&net.net)
        // The Lean reference fires atomically and does not model the in-flight split of
        // VER-004: the atomic pass compares on that reading, the default pass on the
        // caller's (module docs).
        .assume_atomic_firing(cfg.atomic)
        .initial_marking(net.marking.clone())
        .property(prop.property.clone())
        .sink_places(prop.sinks.iter().cloned())
        .enumeration_max_classes(cfg.enum_budget)
        .linear_bound(cfg.linear_bound)
        .state_equation_phase(cfg.phases)
        .firing_bound(cfg.phases)
        .certificate_check(true)
        .counterexample_replay(true)
        .timeout(4_000)
        .total_budget(12_000)
        .verify()
}

// ======================================================================
// Corpus files
// ======================================================================

fn corpus_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../spec/verification-fixtures/conformance")
}

fn expected_dir() -> PathBuf {
    std::env::var_os("LIBPETRI_CONFORMANCE_EXPECTED")
        .map(PathBuf::from)
        .unwrap_or_else(|| corpus_dir().join("expected"))
}

fn json_files(dir: &Path) -> Vec<PathBuf> {
    let mut files: Vec<PathBuf> = std::fs::read_dir(dir)
        .map(|rd| {
            rd.filter_map(|e| e.ok().map(|e| e.path()))
                .filter(|p| p.extension().is_some_and(|x| x == "json"))
                .collect()
        })
        .unwrap_or_default();
    files.sort();
    files
}

fn read_json(path: &Path) -> Json {
    let text = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    parse_json(&text)
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum RefVerdict {
    Proven,
    Violated,
    Unknown,
}

/// The reference's verdict per property id, from `expected/<id>.json`.
fn expected_verdicts(doc: &Json, net_id: &str) -> Result<BTreeMap<String, RefVerdict>, String> {
    if doc.str_opt("id") != Some(net_id) {
        return Err(format!("expected file names id {:?}, not '{net_id}'", doc.str_opt("id")));
    }
    let mut out = BTreeMap::new();
    for r in doc.arr("results") {
        let v = match r.str("verdict") {
            "proven" => RefVerdict::Proven,
            "violated" => RefVerdict::Violated,
            "unknown" => RefVerdict::Unknown,
            other => return Err(format!("unknown reference verdict '{other}'")),
        };
        out.insert(r.str("property").to_string(), v);
    }
    Ok(out)
}

// ======================================================================
// The check
// ======================================================================

#[derive(Default)]
struct Stats {
    nets: usize,
    queries: usize,
    /// Reference verdicts: proven, violated, unknown.
    reference: [usize; 3],
    /// [config][Proven, Violated, Unknown]
    verdicts: [[usize; 3]; SETUPS],
    /// [config]: `Unknown` although the reference decided (incompleteness).
    incomplete: [usize; SETUPS],
    /// [config]: agreement with a deciding reference.
    agree: [usize; SETUPS],
    /// [config]: a default-pass `Violated` where the reference says `proven`, a run with
    /// an action in flight (allowed there, counted).
    split_only: [usize; SETUPS],
    traces: usize,
    /// Default-pass traces of a split net: not replayable by the atomic reference.
    split_traces: usize,
    /// Of those, the ones the verifier's own abstract replay did not confirm.
    split_unconfirmed: usize,
    /// `Violated` with no firing sequence to replay (markings only, or nothing): a
    /// rule-3 finding.
    untraced: usize,
    unconfirmed: usize,
    incomplete_detail: Vec<String>,
}

impl Stats {
    fn merge(&mut self, o: Stats) {
        self.nets += o.nets;
        self.queries += o.queries;
        for i in 0..3 {
            self.reference[i] += o.reference[i];
        }
        for c in 0..SETUPS {
            for k in 0..3 {
                self.verdicts[c][k] += o.verdicts[c][k];
            }
            self.incomplete[c] += o.incomplete[c];
            self.agree[c] += o.agree[c];
            self.split_only[c] += o.split_only[c];
        }
        self.traces += o.traces;
        self.split_traces += o.split_traces;
        self.split_unconfirmed += o.split_unconfirmed;
        self.untraced += o.untraced;
        self.unconfirmed += o.unconfirmed;
        self.incomplete_detail.extend(o.incomplete_detail);
    }
}

/// One dumped trace: the property and the net's own transition names.
type Trace = (String, Vec<String>);

fn check_net(net: &CorpusNet, expected: &BTreeMap<String, RefVerdict>, stats: &mut Stats) -> (Vec<String>, Vec<Trace>) {
    let mut findings = Vec::new();
    let mut traces: Vec<Trace> = Vec::new();
    stats.nets += 1;
    for prop in &net.properties {
        stats.queries += 1;
        let Some(&rv) = expected.get(&prop.id) else {
            findings.push(format!("{}/{}: no reference verdict (expected/ is stale)", net.id, prop.id));
            continue;
        };
        stats.reference[rv as usize] += 1;
        for (ci, cfg) in CONFIGS.iter().enumerate() {
            let r = run_config(net, prop, *cfg);
            let what = format!("{}/{} [{}] {} via {:?}", net.id, prop.id, cfg.name, prop.property.description(), r.route);
            match &r.verdict {
                Verdict::Proven { method, .. } => {
                    stats.verdicts[ci][0] += 1;
                    match rv {
                        RefVerdict::Violated => findings.push(format!(
                            "WRONG PROVEN (rule 1) {what}: method {method}; the reference reaches a violation"
                        )),
                        RefVerdict::Proven => stats.agree[ci] += 1,
                        RefVerdict::Unknown => {}
                    }
                }
                Verdict::Violated => {
                    stats.verdicts[ci][1] += 1;
                    let names: Vec<String> =
                        r.counterexample_transitions.iter().map(|n| net.transition_name(n)).collect();
                    // A trace of one marking and no step is the initial marking itself.
                    let traced = !names.is_empty() || r.counterexample_trace.len() == 1;
                    let split = !cfg.atomic && r.report.contains("In-flight actions (VER-004):");
                    if traced && split {
                        stats.split_traces += 1;
                        if r.counterexample_confirmed == Some(false) {
                            stats.split_unconfirmed += 1;
                        }
                    } else if traced {
                        stats.traces += 1;
                        if r.counterexample_confirmed == Some(false) {
                            stats.unconfirmed += 1;
                        }
                        let t = (prop.id.clone(), names.clone());
                        if !traces.contains(&t) {
                            traces.push(t);
                        }
                    } else {
                        // Rule 3: a violation must come with a firing sequence the
                        // reference can replay — `[]` when the initial marking violates.
                        stats.untraced += 1;
                        findings.push(format!(
                            "VIOLATED WITHOUT A TRACE (rule 3) {what}: {} marking(s) and no firing \
                             sequence; an initial-marking violation must report the empty trace",
                            r.counterexample_trace.len()
                        ));
                    }
                    match rv {
                        RefVerdict::Proven if !cfg.atomic => stats.split_only[ci] += 1,
                        RefVerdict::Proven => findings.push(format!(
                            "WRONG VIOLATED (rule 2) {what}: the reference's state space is closed and clean; \
                             trace {names:?} (confirmed {:?}). If it replays under `lake exe reference --replay`, \
                             the REFERENCE is falsified",
                            r.counterexample_confirmed
                        )),
                        RefVerdict::Violated => stats.agree[ci] += 1,
                        RefVerdict::Unknown => {}
                    }
                }
                Verdict::Unknown { reason } => {
                    stats.verdicts[ci][2] += 1;
                    if rv != RefVerdict::Unknown {
                        stats.incomplete[ci] += 1;
                        stats.incomplete_detail.push(format!(
                            "{what}: reference {rv:?}, unknown: {}",
                            reason.chars().take(140).collect::<String>()
                        ));
                    }
                }
            }
        }
    }
    (findings, traces)
}

fn json_string(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// `[{"property": id, "trace": [names]}]` — the `lake exe reference --replay` input.
fn traces_json(traces: &[Trace]) -> String {
    let rows: Vec<String> = traces
        .iter()
        .map(|(p, t)| {
            let names: Vec<String> = t.iter().map(|n| json_string(n)).collect();
            format!("  {{\"property\": {}, \"trace\": [{}]}}", json_string(p), names.join(", "))
        })
        .collect();
    format!("[\n{}\n]\n", rows.join(",\n"))
}

fn z3_or_skip(test: &str) -> bool {
    if z3_available() {
        return true;
    }
    assert!(std::env::var("CI").is_err(), "{test} cannot run on this CI runner: no `z3` binary on PATH");
    eprintln!("skipping {test}: z3 binary not on PATH");
    false
}

fn env_flag(name: &str) -> bool {
    std::env::var(name).is_ok_and(|v| v == "1")
}

// ======================================================================
// Tests
// ======================================================================

/// Every corpus net loads under the schema (no z3, no expected verdicts needed).
#[test]
fn every_corpus_net_loads() {
    let files = json_files(&corpus_dir().join("nets"));
    if files.is_empty() {
        eprintln!("skipping every_corpus_net_loads: no nets under {}", corpus_dir().join("nets").display());
        return;
    }
    let mut kinds = BTreeMap::new();
    for f in &files {
        let net = load_net(&read_json(f));
        assert_eq!(
            Some(net.id.as_str()),
            f.file_stem().and_then(|s| s.to_str()),
            "{}: id differs from the file name",
            f.display()
        );
        assert!(!net.properties.is_empty(), "{}: no properties", net.id);
        for p in &net.properties {
            *kinds.entry(p.kind.clone()).or_insert(0usize) += 1;
        }
    }
    eprintln!("[conformance] {} nets load; properties by type {kinds:?}", files.len());
    assert_eq!(kinds.len(), 6, "the corpus must cover all six property types: {kinds:?}");
}

/// The branch suffix of a flattened transition maps back to the net's own name.
#[test]
fn trace_names_map_back_to_the_net() {
    let doc = parse_json(
        r#"{"id": "x", "places": ["a"], "marking": {"a": 1},
            "transitions": [{"name": "t", "inputs": [{"place": "a", "kind": "one"}], "output": null},
                            {"name": "u_b1", "inputs": [], "inhibitors": ["a"], "output": {"type": "place", "place": "a"}}],
            "properties": [{"id": "p", "type": "deadlock-free", "sinks": []}]}"#,
    );
    let net = load_net(&doc);
    assert_eq!(net.transition_name("t_b3"), "t");
    assert_eq!(net.transition_name("t"), "t");
    assert_eq!(net.transition_name("u_b1"), "u_b1");
    assert_eq!(net.transition_name("v_b1"), "v_b1");
    assert_eq!(traces_json(&[("p".into(), vec!["t".into()])]), "[\n  {\"property\": \"p\", \"trace\": [\"t\"]}\n]\n");
}

#[test]
fn conformance_with_the_lean_reference() {
    let exp_dir = expected_dir();
    let nets_dir = corpus_dir().join("nets");
    let expected_files = json_files(&exp_dir);
    if expected_files.is_empty() {
        let msg = format!(
            "no expected verdicts under {} — they are written by the Lean reference only: \
             run scripts/conformance-corpus.py --update",
            exp_dir.display()
        );
        assert!(!env_flag("LIBPETRI_CONFORMANCE_REQUIRE"), "{msg}");
        eprintln!("skipping conformance_with_the_lean_reference: {msg}");
        return;
    }
    if !z3_or_skip("conformance_with_the_lean_reference") {
        return;
    }
    let filter = std::env::var("LIBPETRI_CONFORMANCE_FILTER").unwrap_or_default();
    let net_files: Vec<PathBuf> = json_files(&nets_dir)
        .into_iter()
        .filter(|p| p.file_stem().and_then(|s| s.to_str()).is_some_and(|s| s.contains(&filter)))
        .collect();
    assert!(!net_files.is_empty(), "no corpus nets under {} match filter '{filter}'", nets_dir.display());
    let dump = std::env::var_os("LIBPETRI_CONFORMANCE_DUMP").map(PathBuf::from);
    if let Some(d) = &dump {
        std::fs::create_dir_all(d).unwrap_or_else(|e| panic!("create {}: {e}", d.display()));
    }
    let threads = std::env::var("LIBPETRI_CONFORMANCE_THREADS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or_else(|| std::thread::available_parallelism().map_or(4, |n| n.get()))
        .max(1);

    let start = Instant::now();
    let next = AtomicUsize::new(0);
    let stats = Mutex::new(Stats::default());
    let findings: Mutex<Vec<(usize, String)>> = Mutex::new(Vec::new());
    std::thread::scope(|scope| {
        for _ in 0..threads {
            scope.spawn(|| {
                let mut local = Stats::default();
                loop {
                    let i = next.fetch_add(1, Ordering::Relaxed);
                    let Some(file) = net_files.get(i) else { break };
                    let net = load_net(&read_json(file));
                    let exp_file = exp_dir.join(format!("{}.json", net.id));
                    if !exp_file.exists() {
                        findings.lock().unwrap().push((i, format!("{}: no {} (expected/ is stale)", net.id, exp_file.display())));
                        continue;
                    }
                    let expected = match expected_verdicts(&read_json(&exp_file), &net.id) {
                        Ok(e) => e,
                        Err(why) => {
                            findings.lock().unwrap().push((i, format!("{}: {why}", net.id)));
                            continue;
                        }
                    };
                    // One named thread per net: a verifier panic names the net and is
                    // never caught here (the crate's policy).
                    let id = net.id.clone();
                    let (found, traces, st) = std::thread::Builder::new()
                        .name(format!("conformance {id}"))
                        .spawn(move || {
                            let mut st = Stats::default();
                            let (found, traces) = check_net(&net, &expected, &mut st);
                            (found, traces, st)
                        })
                        .expect("spawn net thread")
                        .join()
                        .unwrap_or_else(|_| panic!("net {id} panicked (message above)"));
                    local.merge(st);
                    if let (Some(d), false) = (&dump, traces.is_empty()) {
                        let path = d.join(format!("{id}.traces.json"));
                        std::fs::write(&path, traces_json(&traces))
                            .unwrap_or_else(|e| panic!("write {}: {e}", path.display()));
                    }
                    findings.lock().unwrap().extend(found.into_iter().map(|f| (i, f)));
                }
                stats.lock().unwrap().merge(local);
            });
        }
    });
    let stats = stats.into_inner().unwrap();
    let mut findings = findings.into_inner().unwrap();
    findings.sort();

    let mut report = format!(
        "[conformance] {} nets, {} queries x {} setups in {:.1}s on {threads} threads against {}\n\
         reference proven/violated/unknown {:?}\n",
        stats.nets,
        stats.queries,
        CONFIGS.len(),
        start.elapsed().as_secs_f64(),
        exp_dir.display(),
        stats.reference
    );
    for (c, cfg) in CONFIGS.iter().enumerate() {
        report.push_str(&format!(
            "  {:12} proven/violated/unknown {:?}  agree {}  unknown-where-reference-decided {}{}\n",
            cfg.name,
            stats.verdicts[c],
            stats.agree[c],
            stats.incomplete[c],
            if cfg.atomic { String::new() } else { format!("  violated-where-reference-proved {}", stats.split_only[c]) }
        ));
    }
    report.push_str(&format!(
        "default-pass traces of split nets {} (unconfirmed by the abstract replay {}), not replayed by the reference\n",
        stats.split_traces, stats.split_unconfirmed
    ));
    report.push_str(&format!(
        "violated traces {} (unconfirmed by the abstract replay {}), violated without a firing sequence {}{}\n",
        stats.traces,
        stats.unconfirmed,
        stats.untraced,
        dump.as_ref().map_or(String::new(), |d| format!("; dumped to {}", d.display()))
    ));
    eprint!("{report}");
    if env_flag("LIBPETRI_CONFORMANCE_VERBOSE") {
        let mut detail = stats.incomplete_detail;
        detail.sort();
        for d in detail {
            eprintln!("  {d}");
        }
    }
    for (_, f) in &findings {
        eprintln!("  {f}");
    }
    assert!(findings.is_empty(), "{} conformance finding(s) against the Lean reference (see stderr)", findings.len());
}
