//! Cross-language verdict-parity fixture runner (C4).
//!
//! Runs every fixture in `spec/verification-fixtures/fixtures.json` — the
//! shared expectations all four language implementations assert against —
//! through the real [`SmtVerifier`] with BOTH independent validation layers
//! on: certificate checking (a `Proven` re-verified as an inductive invariant
//! in a second z3 run) and counterexample replay (a `Violated` re-executed
//! against the abstract semantics). The nets are built with the public core
//! builder API in `tests/common/nets.rs` per each fixture's normative
//! `netDescription`.
//!
//! A verdict disagreeing with a fixture's `expected` is a parity FINDING to
//! investigate and report prominently — never a reason to adjust the fixture.
//! All fixtures run before failing, so one finding does not mask another.

#![cfg(feature = "z3")]

#[path = "common/nets.rs"]
mod nets;

use libpetri_verification::property::SmtProperty;
use libpetri_verification::result::Verdict;
use libpetri_verification::smt_verifier::{SmtVerifier, z3_available};

// === Minimal JSON reader ===
//
// The crate is deliberately dependency-free (no serde), so the fixture file —
// a small, schema-stable document — is read with a tiny recursive-descent
// parser. Test-only code: malformed JSON panics with a position.

#[derive(Debug, Clone, PartialEq)]
enum Json {
    Null,
    Bool(bool),
    Num(f64),
    Str(String),
    Arr(Vec<Json>),
    Obj(Vec<(String, Json)>),
}

impl Json {
    fn get(&self, key: &str) -> Option<&Json> {
        match self {
            Json::Obj(entries) => entries.iter().find(|(k, _)| k == key).map(|(_, v)| v),
            _ => None,
        }
    }

    fn str(&self, key: &str) -> &str {
        match self.get(key) {
            Some(Json::Str(s)) => s,
            other => panic!("expected string at key '{key}', got {other:?}"),
        }
    }

    fn usize(&self, key: &str) -> usize {
        match self.get(key) {
            Some(Json::Num(n)) => *n as usize,
            other => panic!("expected number at key '{key}', got {other:?}"),
        }
    }

    fn arr(&self, key: &str) -> &[Json] {
        match self.get(key) {
            Some(Json::Arr(items)) => items,
            other => panic!("expected array at key '{key}', got {other:?}"),
        }
    }

    /// Optional string (`route`): absent -> `None`.
    fn str_opt(&self, key: &str) -> Option<&str> {
        match self.get(key) {
            None | Some(Json::Null) => None,
            Some(Json::Str(s)) => Some(s),
            other => panic!("expected string at key '{key}', got {other:?}"),
        }
    }

    /// Optional string array (`sinkPlaces`): absent -> empty.
    fn str_arr_opt(&self, key: &str) -> Vec<String> {
        match self.get(key) {
            None | Some(Json::Null) => Vec::new(),
            Some(Json::Arr(items)) => items
                .iter()
                .map(|it| match it {
                    Json::Str(s) => s.clone(),
                    other => panic!("expected string in '{key}', got {other:?}"),
                })
                .collect(),
            other => panic!("expected array at key '{key}', got {other:?}"),
        }
    }
}

fn parse_json(input: &str) -> Json {
    let bytes = input.as_bytes();
    let mut pos = 0usize;
    let value = parse_value(bytes, &mut pos);
    skip_ws(bytes, &mut pos);
    assert!(pos == bytes.len(), "trailing JSON content at byte {pos}");
    value
}

fn skip_ws(bytes: &[u8], pos: &mut usize) {
    while *pos < bytes.len() && bytes[*pos].is_ascii_whitespace() {
        *pos += 1;
    }
}

fn expect(bytes: &[u8], pos: &mut usize, c: u8) {
    assert!(
        *pos < bytes.len() && bytes[*pos] == c,
        "expected '{}' at byte {pos:?}",
        c as char
    );
    *pos += 1;
}

fn parse_value(bytes: &[u8], pos: &mut usize) -> Json {
    skip_ws(bytes, pos);
    match bytes.get(*pos) {
        Some(b'{') => {
            *pos += 1;
            let mut entries = Vec::new();
            skip_ws(bytes, pos);
            if bytes.get(*pos) == Some(&b'}') {
                *pos += 1;
                return Json::Obj(entries);
            }
            loop {
                skip_ws(bytes, pos);
                let key = parse_string(bytes, pos);
                skip_ws(bytes, pos);
                expect(bytes, pos, b':');
                entries.push((key, parse_value(bytes, pos)));
                skip_ws(bytes, pos);
                match bytes.get(*pos) {
                    Some(b',') => *pos += 1,
                    Some(b'}') => {
                        *pos += 1;
                        return Json::Obj(entries);
                    }
                    other => panic!("expected ',' or '}}' at byte {pos:?}, got {other:?}"),
                }
            }
        }
        Some(b'[') => {
            *pos += 1;
            let mut items = Vec::new();
            skip_ws(bytes, pos);
            if bytes.get(*pos) == Some(&b']') {
                *pos += 1;
                return Json::Arr(items);
            }
            loop {
                items.push(parse_value(bytes, pos));
                skip_ws(bytes, pos);
                match bytes.get(*pos) {
                    Some(b',') => *pos += 1,
                    Some(b']') => {
                        *pos += 1;
                        return Json::Arr(items);
                    }
                    other => panic!("expected ',' or ']' at byte {pos:?}, got {other:?}"),
                }
            }
        }
        Some(b'"') => Json::Str(parse_string(bytes, pos)),
        Some(b't') => {
            assert!(bytes[*pos..].starts_with(b"true"), "bad literal at {pos:?}");
            *pos += 4;
            Json::Bool(true)
        }
        Some(b'f') => {
            assert!(bytes[*pos..].starts_with(b"false"), "bad literal at {pos:?}");
            *pos += 5;
            Json::Bool(false)
        }
        Some(b'n') => {
            assert!(bytes[*pos..].starts_with(b"null"), "bad literal at {pos:?}");
            *pos += 4;
            Json::Null
        }
        _ => {
            let start = *pos;
            while *pos < bytes.len()
                && matches!(bytes[*pos], b'0'..=b'9' | b'-' | b'+' | b'.' | b'e' | b'E')
            {
                *pos += 1;
            }
            let text = std::str::from_utf8(&bytes[start..*pos]).unwrap();
            Json::Num(text.parse().unwrap_or_else(|_| panic!("bad number '{text}' at byte {start}")))
        }
    }
}

fn parse_string(bytes: &[u8], pos: &mut usize) -> String {
    expect(bytes, pos, b'"');
    let mut out = String::new();
    loop {
        match bytes.get(*pos) {
            Some(b'"') => {
                *pos += 1;
                return out;
            }
            Some(b'\\') => {
                *pos += 1;
                let escaped = bytes.get(*pos).copied().expect("truncated escape");
                *pos += 1;
                match escaped {
                    b'"' => out.push('"'),
                    b'\\' => out.push('\\'),
                    b'/' => out.push('/'),
                    b'n' => out.push('\n'),
                    b't' => out.push('\t'),
                    b'r' => out.push('\r'),
                    b'u' => {
                        let hex = std::str::from_utf8(&bytes[*pos..*pos + 4]).unwrap();
                        let code = u32::from_str_radix(hex, 16).unwrap();
                        out.push(char::from_u32(code).expect("surrogate escapes unsupported"));
                        *pos += 4;
                    }
                    other => panic!("unsupported escape '\\{}'", other as char),
                }
            }
            Some(_) => {
                // Advance one UTF-8 character.
                let rest = std::str::from_utf8(&bytes[*pos..]).unwrap();
                let c = rest.chars().next().unwrap();
                out.push(c);
                *pos += c.len_utf8();
            }
            None => panic!("unterminated string"),
        }
    }
}

// === Fixture plumbing ===

/// Maps a fixture's `property` object onto [`SmtProperty`]. Note the shared
/// schema's `unreachable` carries a singular `place`.
fn property_of(prop: &Json) -> SmtProperty {
    match prop.str("type") {
        "deadlock-free" => SmtProperty::DeadlockFree,
        "mutual-exclusion" => SmtProperty::mutual_exclusion(
            prop.arr("places")
                .iter()
                .map(|p| match p {
                    Json::Str(s) => s.clone(),
                    other => panic!("expected place name string, got {other:?}"),
                })
                .collect(),
        ),
        "place-bound" => SmtProperty::place_bound(prop.str("place"), prop.usize("bound")),
        "unreachable" => SmtProperty::unreachable(vec![prop.str("place").to_string()]),
        other => panic!("unknown fixture property type '{other}'"),
    }
}

/// The line every implementation prints when the ν name-aware state-class-graph
/// verifier ([NU-050] Route B) — not the SMT / Route A encoders — decided the
/// query. Fixtures marked `"route": "B"` assert it BEFORE their verdict, so a
/// silent fall-back to Route A fails loudly instead of passing vacuously.
const ROUTE_B_MARKER: &str = "ν-net Route B: name-aware state-class graph (NU-050)";

fn verdict_word(verdict: &Verdict) -> &'static str {
    match verdict {
        Verdict::Proven { .. } => "proven",
        Verdict::Violated => "violated",
        Verdict::Unknown { .. } => "unknown",
    }
}

/// Runs every shared fixture and reports ALL disagreements at once.
#[test]
fn verdict_parity_fixtures() {
    if !z3_available() {
        // A skip here used to be a silent green: the whole cross-language
        // fixture contract goes unchecked. `tests/z3_gate.rs` polices this
        // from outside the `z3` cfg; fail loudly here too so the runner that
        // lost its solver names the suite it dropped.
        assert!(
            std::env::var("CI").is_err(),
            "verdict_parity_fixtures cannot run on this CI runner: no `z3` binary on PATH, \
             so the shared cross-language fixture expectations were never checked"
        );
        eprintln!("skipping verdict_parity_fixtures: z3 binary not on PATH");
        return;
    }

    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../spec/verification-fixtures/fixtures.json"
    );
    let raw = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("cannot read shared fixtures at {path}: {e}"));
    let doc = parse_json(&raw);
    let fixtures = doc.arr("fixtures");
    assert!(!fixtures.is_empty(), "fixtures.json lists no fixtures");

    let mut findings: Vec<String> = Vec::new();
    for fixture in fixtures {
        let id = fixture.str("id");
        let expected = fixture.str("expected");
        let built = nets::build(fixture.str("net"));
        let property = property_of(fixture.get("property").expect("fixture without property"));

        let mut verifier = SmtVerifier::for_net(&built.net)
            .initial_marking(built.initial.clone())
            .property(property)
            // Both independent validation layers explicitly ON — the point of
            // the parity suite (they are also the defaults).
            .certificate_check(true)
            .counterexample_replay(true)
            .timeout(30_000);
        if !built.env_places.is_empty() {
            verifier = verifier
                .environment_places(built.env_places.iter().cloned())
                .environment_mode(built.env_mode.clone());
        }
        // Optional shared-schema field: expected terminal places, per [VER-002].
        let sinks = fixture.str_arr_opt("sinkPlaces");
        if !sinks.is_empty() {
            verifier = verifier.sink_places(sinks.iter().cloned());
        }
        let result = verifier.verify();

        let got = verdict_word(&result.verdict);
        let route_b = fixture.str_opt("route") == Some("B");
        eprintln!(
            "[parity] {id}: expected={expected} got={got} route={} replay_confirmed={:?} elapsed={}ms",
            fixture.str_opt("route").unwrap_or("A"),
            result.counterexample_confirmed,
            result.elapsed_ms
        );
        // The route marker is checked FIRST: a `route: "B"` fixture that silently
        // fell back to Route A would pin nothing, so name that failure directly
        // rather than letting it surface as a confusing verdict mismatch.
        if route_b && !result.report.contains(ROUTE_B_MARKER) {
            findings.push(format!(
                "ROUTE FINDING [{id}]: fixture declares route \"B\" but the report does not \
                 name the ν name-aware state-class graph — the query fell back to Route A, so \
                 the Route B deadlock predicate was never exercised\n\
                 --- verifier report ---\n{}",
                result.report
            ));
            continue;
        }
        if got != expected {
            findings.push(format!(
                "PARITY FINDING [{id}]: expected '{expected}', got '{got}'\n\
                 --- verifier report ---\n{}",
                result.report
            ));
            continue;
        }
        if let Some(Json::Str(substring)) = fixture.get("expectReportContains") {
            if !result.report.contains(substring.as_str()) {
                findings.push(format!(
                    "PARITY FINDING [{id}]: verdict '{got}' matches but the report is missing \
                     the required substring {substring:?}\n--- verifier report ---\n{}",
                    result.report
                ));
                continue;
            }
        }
        // Rust-side strengthening beyond the shared contract: on every
        // violated fixture, z3 4.13's refutation proof yields ground
        // `Reachable` states and the abstract replay confirms the chain
        // (observed across all five violated shapes: deadlock, mutex, bound,
        // env injection, H1 consume-all). Losing this is a replay/decoder
        // regression, NOT a fixture mismatch — reported separately.
        // Route B is exempt: its counterexample is a path of the name-partition
        // graph, not of the flat abstract semantics, so it reports
        // `counterexample_confirmed = None` by construction.
        if expected == "violated" && !route_b && result.counterexample_confirmed != Some(true) {
            findings.push(format!(
                "REPLAY REGRESSION [{id}]: verdict is Violated as expected, but the \
                 counterexample no longer replays (confirmed=false)\n\
                 --- verifier report ---\n{}",
                result.report
            ));
        }
    }

    assert!(
        findings.is_empty(),
        "\n{} parity finding(s):\n\n{}",
        findings.len(),
        findings.join("\n\n")
    );
}
