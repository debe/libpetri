//! \[NU-055\] name alignment: the fixtures of
//! `spec/verification-fixtures/nu-aligned-fixtures.json` (AC1, AC2, AC3, AC6), the refusals,
//! and the dispatcher rules of AC4 (Route B whatever the net, never a deferral). The same
//! queries, and the same expected verdicts, as TypeScript's
//! `tests/verification/nu-name-alignment.test.ts`. The other routes are sent the property
//! directly by their own in-module tests, and the AC5 run with a pinned minting scope lives in
//! the umbrella crate's `nu055_name_alignment_run.rs`, which can run the executors.

#![cfg(feature = "z3")]

#[path = "common/json.rs"]
mod json;
#[path = "common/relay_fixtures.rs"]
mod relay_fixtures;
#[path = "common/relay_nets.rs"]
mod relay_nets;

use std::collections::BTreeSet;

use json::Json;
use relay_nets::{Row, j, pnid_net, t};

use libpetri_core::action::fork;
use libpetri_core::input::one;
use libpetri_core::output::out_place;
use libpetri_core::petri_net::PetriNet;
use libpetri_core::place::Place;
use libpetri_core::timing::deadline;
use libpetri_core::transition::Transition;
use libpetri_verification::environment::EnvironmentAnalysisMode;
use libpetri_verification::marking_state::{MarkingState, MarkingStateBuilder};
use libpetri_verification::name_fragment::FragmentMode;
use libpetri_verification::property::SmtProperty;
use libpetri_verification::result::{Verdict, VerificationResult, VerificationRoute};
use libpetri_verification::smt_verifier::SmtVerifier;

const ONLY_B: &str = "decided only by the name-partition state-class graph (NU-055, Route B)";

/// The fixtures of `spec/verification-fixtures/nu-aligned-fixtures.json`.
fn aligned_fixtures() -> Vec<Json> {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../../spec/verification-fixtures/nu-aligned-fixtures.json");
    let raw = std::fs::read_to_string(path).expect("read nu-aligned-fixtures.json");
    json::parse_json(&raw).arr("fixtures").to_vec()
}

fn fixture_by_id(id: &str) -> Json {
    aligned_fixtures()
        .into_iter()
        .find(|f| f.str("id") == id)
        .unwrap_or_else(|| panic!("no fixture {id}"))
}

fn strings(j: &Json) -> Vec<String> {
    match j {
        Json::Arr(items) => items
            .iter()
            .map(|it| match it {
                Json::Str(s) => s.clone(),
                other => panic!("expected a string, got {other:?}"),
            })
            .collect(),
        other => panic!("expected an array, got {other:?}"),
    }
}

fn fixture_property(fixture: &Json) -> SmtProperty {
    let prop = fixture.get("property").unwrap();
    let places = prop.str_arr_opt("places");
    match prop.str("type") {
        "name-aligned" => SmtProperty::name_aligned(&places[0], &places[1]),
        "quiescent-name-aligned" => SmtProperty::quiescent_name_aligned(&places[0], &places[1]),
        "quiescent-count" => SmtProperty::quiescent_count(places, prop.usize("min"), Some(prop.usize("max")), Vec::new()),
        other => panic!("unmapped property '{other}'"),
    }
}

fn fixture_marking(fixture: &Json) -> MarkingState {
    let mut m = MarkingStateBuilder::new();
    for (p, k) in relay_fixtures::fixture_marking(fixture) {
        m = m.tokens(p, k);
    }
    m.build()
}

/// `net` verified with `fixture`'s marking, property and options, after `adjust`.
fn verify_fixture_with<'a>(
    fixture: &Json,
    net: &'a PetriNet,
    adjust: impl FnOnce(SmtVerifier<'a>) -> SmtVerifier<'a>,
) -> VerificationResult {
    let mode = match fixture.str("fragmentMode") {
        "extended" => FragmentMode::Extended,
        "base" => FragmentMode::Base,
        other => panic!("unmapped fragment mode '{other}'"),
    };
    let mut v = SmtVerifier::for_net(net)
        .initial_marking(fixture_marking(fixture))
        .property(fixture_property(fixture))
        .mint_transitions(fixture.str_arr_opt("mintTransitions"))
        .carrier_places(fixture.str_arr_opt("carrierPlaces"))
        .budget_places(fixture.str_arr_opt("budgetPlaces"))
        .fragment_mode(mode)
        .timeout(30_000);
    let env = fixture.str_arr_opt("environmentPlaces");
    if !env.is_empty() {
        assert_eq!(fixture.str("environmentMode"), "always-available");
        v = v.environment_places(env).environment_mode(EnvironmentAnalysisMode::AlwaysAvailable);
    }
    adjust(v).verify()
}

fn verify_fixture(fixture: &Json) -> VerificationResult {
    let net = relay_fixtures::fixture_net(fixture);
    verify_fixture_with(fixture, &net, |v| v)
}

fn verdict(r: &VerificationResult) -> &'static str {
    if r.is_proven() {
        "proven"
    } else if r.is_violated() {
        "violated"
    } else {
        "unknown"
    }
}

fn reason(r: &VerificationResult) -> &str {
    match &r.verdict {
        Verdict::Unknown { reason } => reason,
        other => panic!("expected Unknown, got {other:?}\n{}", r.report),
    }
}

/// What the reason of an `unknown` fixture must name: EXTENDED for a BASE run, else the
/// environment place, else the coloured place the initial marking marks, else the uncoloured
/// property place.
fn named_by_reason(fixture: &Json) -> String {
    if fixture.str("fragmentMode") == "base" {
        return "EXTENDED".into();
    }
    if let Some(env) = fixture.str_arr_opt("environmentPlaces").first() {
        return format!("'{env}'");
    }
    let mut coloured: BTreeSet<String> = fixture.str_arr_opt("carrierPlaces").into_iter().collect();
    for row in fixture.arr("rows") {
        let Json::Arr(cells) = row else { panic!("malformed row {row:?}") };
        coloured.extend(strings(&cells[3]));
        coloured.extend(strings(&cells[4]));
    }
    if let Some((marked, _)) = relay_fixtures::fixture_marking(fixture).into_iter().find(|(p, _)| coloured.contains(p)) {
        return format!("'{marked}'");
    }
    let places = fixture.get("property").unwrap().str_arr_opt("places");
    let uncoloured = places
        .iter()
        .find(|p| !coloured.contains(*p))
        .unwrap_or_else(|| panic!("fixture {}: nothing for the reason to name", fixture.str("id")));
    format!("'{uncoloured}'")
}

// ── the fixtures (AC1, AC2, AC3, AC6) ─────────────────────────────────────────

/// [NU-055] Every fixture of `nu-aligned-fixtures.json`: route B, its verdict and witness
/// length, no confirmation claimed for the graph's trace ([VER-003]), and for an `unknown`
/// a reason naming the place or the declined fragment.
#[test]
fn nu055_aligned_fixtures_get_their_declared_verdicts() {
    let fixtures = aligned_fixtures();
    assert_eq!(fixtures.len(), 10, "the ten NU-055 fixtures");
    for fixture in fixtures {
        let id = fixture.str("id");
        assert_eq!(fixture.str("route"), "B", "{id}");
        let r = verify_fixture(&fixture);
        assert_eq!(r.route, VerificationRoute::NuScg, "{id}\n{}", r.report);
        assert!(r.report.contains("Route B"), "{id}: the report names Route B\n{}", r.report);
        assert_eq!(verdict(&r), fixture.str("expected"), "{id}\n{}", r.report);
        if let Some(Json::Num(n)) = fixture.get("witnessLength") {
            assert_eq!(r.counterexample_transitions.len(), *n as usize, "{id}: {:?}", r.counterexample_transitions);
        }
        assert_eq!(r.counterexample_confirmed, None, "{id}");
        if fixture.str("expected") == "unknown" {
            let why = reason(&r);
            assert!(why.contains(&named_by_reason(&fixture)), "{id}: {why}");
            assert!(!why.contains("verified via"), "{id}: {why}");
        }
    }
}

// ── refusals (AC2, AC3, AC6) ──────────────────────────────────────────────────

/// [NU-055] AC2: a place absent from the net is `Unknown` naming the place, before any route.
#[test]
fn nu055_ac2_an_absent_place_is_unknown_naming_it() {
    let f = fixture_by_id("nu-aligned-search-quiescent-proven");
    let net = relay_fixtures::fixture_net(&f);
    for property in [
        SmtProperty::quiescent_name_aligned("box", "nowhere"),
        SmtProperty::name_aligned("nowhere", "list"),
    ] {
        let r = verify_fixture_with(&f, &net, |v| v.property(property.clone()));
        assert!(reason(&r).contains("'nowhere'"), "{}", r.report);
    }
}

/// [NU-055] AC2: `NameAligned` on an uncoloured place is `Unknown` naming the place.
#[test]
fn nu055_ac2_name_aligned_on_an_uncoloured_place_is_unknown_naming_it() {
    let f = fixture_by_id("nu-aligned-search-uncoloured-unknown");
    let net = relay_fixtures::fixture_net(&f);
    let r = verify_fixture_with(&f, &net, |v| v.property(SmtProperty::name_aligned("ready", "box")));
    assert_eq!(r.route, VerificationRoute::NuScg);
    let why = reason(&r);
    assert!(why.contains("place 'ready' is not a coloured place"), "{why}");
    assert!(r.report.contains(&format!("UNKNOWN: {why}")), "{}", r.report);
}

/// [NU-055] AC3: under BASE a relay target is uncoloured, and the reason names EXTENDED.
#[test]
fn nu055_ac3_under_base_a_relay_target_is_uncoloured_and_the_reason_names_extended() {
    let rows: Vec<Row> = vec![
        t("fork", &["source"], &["A", "B"]),
        j("join", &["A", "B"], &["done"], &["A", "B"], &["done"]),
    ];
    let net = pnid_net("baseRelay", &rows);
    let verify = |mode: FragmentMode| {
        SmtVerifier::for_net(&net)
            .initial_marking(MarkingStateBuilder::new().tokens("source", 1).build())
            .property(SmtProperty::name_aligned("A", "done"))
            .mint_transition("fork")
            .fragment_mode(mode)
            .verify()
    };
    let base = verify(FragmentMode::Base);
    assert_eq!(base.route, VerificationRoute::NuScg);
    let why = reason(&base);
    assert!(why.contains("place 'done' is not a coloured place"), "{why}");
    assert!(why.contains("EXTENDED"), "{why}");
    // Under EXTENDED the relay target is coloured, and the join relays the fork's name.
    let extended = verify(FragmentMode::Extended);
    assert_eq!(extended.route, VerificationRoute::NuScg);
    assert!(extended.is_proven(), "{}", extended.report);
}

/// [NU-055] AC3, [NU-054] AC5: the BASE run names the ignored relay declarations, and its
/// decline says nothing else verified the property.
#[test]
fn nu055_ac3_the_base_run_names_the_ignored_relay_declarations() {
    let r = verify_fixture(&fixture_by_id("nu-aligned-search-base-unknown"));
    assert!(
        r.report.contains("ν relay declarations ignored under BASE fragment mode (NU-054): 'apply' -> 'box', 'apply' -> 'staged'"),
        "{}",
        r.report
    );
    let why = reason(&r);
    assert!(why.contains("net outside the BASE fragment"), "{why}");
    assert!(why.contains(ONLY_B), "{why}");
    assert!(!r.report.contains("verified via"), "{}", r.report);
}

/// [NU-055], [NU-051]: outside the EXTENDED fragment the verdict is `Unknown`, and the note
/// does not say another route verified it.
#[test]
fn nu055_outside_the_extended_fragment_the_verdict_is_unknown_and_no_other_route_is_named() {
    let f = fixture_by_id("nu-aligned-search-quiescent-proven");
    let net = relay_fixtures::fixture_net(&f);
    // A carrier `typed` makes `retire` consume two coloured places.
    let r = verify_fixture_with(&f, &net, |v| {
        v.carrier_places(["inflightA", "inflightB", "list", "typed"].map(String::from))
    });
    assert_eq!(r.route, VerificationRoute::NuScg);
    let why = reason(&r);
    assert!(why.starts_with("ν-net Route B (EXTENDED) declined: net outside coloured-consumer fragment"), "{why}");
    assert!(why.ends_with(&format!("{ONLY_B}, so the verdict is unknown")), "{why}");
    assert!(!r.report.contains("verified via"), "{}", r.report);
}

/// [NU-055], [NU-010]: without the mint declaration the decline names the undeclared mints.
#[test]
fn nu055_undeclared_mints_are_named_by_the_decline() {
    let f = fixture_by_id("nu-aligned-search-quiescent-proven");
    let net = relay_fixtures::fixture_net(&f);
    let r = SmtVerifier::for_net(&net)
        .initial_marking(fixture_marking(&f))
        .property(fixture_property(&f))
        .carrier_places(f.str_arr_opt("carrierPlaces"))
        .fragment_mode(FragmentMode::Extended)
        .verify();
    assert_eq!(r.route, VerificationRoute::NuScg);
    let why = reason(&r);
    assert!(why.contains("'sendA', 'sendB' write a coloured place without consuming one"), "{why}");
    assert!(why.contains(ONLY_B), "{why}");
}

/// [NU-055] AC6: the bug variant with a coloured initial token is `Unknown` naming the place.
#[test]
fn nu055_ac6_the_bug_variant_with_a_coloured_initial_token_is_unknown_naming_it() {
    let f = fixture_by_id("nu-aligned-search-bug-quiescent-violated");
    let net = relay_fixtures::fixture_net(&f);
    let mut m = MarkingStateBuilder::new();
    for (p, k) in relay_fixtures::fixture_marking(&f) {
        m = m.tokens(p, k);
    }
    let r = verify_fixture_with(&f, &net, |v| v.initial_marking(m.tokens("reply", 1).build()));
    assert_eq!(r.route, VerificationRoute::NuScg);
    assert!(reason(&r).contains("coloured place 'reply' holds a token in the initial marking"), "{}", r.report);
}

/// [NU-055] AC6: under `Bounded(k)` too the quiescent form with an environment place is
/// `Unknown` naming it and pointing to arrivals.
#[test]
fn nu055_ac6_quiescent_name_aligned_under_bounded_names_the_environment_place() {
    let f = fixture_by_id("nu-aligned-search-env-quiescent-unknown");
    let net = relay_fixtures::fixture_net(&f);
    let r = verify_fixture_with(&f, &net, |v| v.environment_mode(EnvironmentAnalysisMode::Bounded { max_tokens: 2 }));
    assert_eq!(r.route, VerificationRoute::NuScg);
    let why = reason(&r);
    assert!(why.contains("'typed'"), "{why}");
    assert!(why.contains("arrivals(k)"), "{why}");
}

/// [NU-055] Modelled injection: under `Arrivals` the keystrokes are closed into the net, and
/// Route B decides the quiescent form as on the closed fixtures.
#[test]
fn nu055_under_arrivals_the_keystrokes_are_closed_into_the_net_and_route_b_decides_it() {
    for (id, expected) in [
        ("nu-aligned-search-env-quiescent-unknown", "proven"),
        ("nu-aligned-search-bug-env-quiescent-unknown", "violated"),
    ] {
        let f = fixture_by_id(id);
        let net = relay_fixtures::fixture_net(&f);
        let r = verify_fixture_with(&f, &net, |v| {
            v.environment_mode(EnvironmentAnalysisMode::ArrivalsBetween { min_tokens: 2, max_tokens: 2 })
        });
        assert_eq!(r.route, VerificationRoute::NuScg, "{id}\n{}", r.report);
        assert_eq!(verdict(&r), expected, "{id}\n{}", r.report);
    }
}

/// [NU-055]: `QuiescentNameAligned` carries no sink clause, so declared sinks do not weaken it.
#[test]
fn nu055_quiescent_name_aligned_carries_no_sink_clause() {
    let f = fixture_by_id("nu-aligned-search-bug-quiescent-violated");
    let net = relay_fixtures::fixture_net(&f);
    let r = verify_fixture_with(&f, &net, |v| v.sink_places(["box", "list"].map(String::from)));
    assert_eq!(r.route, VerificationRoute::NuScg);
    assert!(r.is_violated(), "{}", r.report);
    assert_eq!(r.counterexample_transitions.len(), 12);
}

/// [NU-055], [VER-002], [TIME-013]: the quiescent form reads reap-aware quiescence. `sendA`
/// and `sendB` mint two names into `box` and `list`; `drop`, a deadline drain of `list`, is
/// all that realigns them. A late executor reaps it and rests misaligned.
#[test]
fn nu055_quiescent_name_aligned_reads_reap_aware_quiescence() {
    let p = |n: &str| Place::<String>::new(n);
    let step = |name: &str, from: &str, to: &str| {
        Transition::builder(name).input(one(&p(from))).output(out_place(&p(to))).action(fork()).build()
    };
    let drop = Transition::builder("drop")
        .input(one(&p("list")))
        .output(out_place(&p("done")))
        .timing(deadline(10))
        .action(fork())
        .build();
    let net = PetriNet::builder("reapedAlignment")
        .transitions([step("sendA", "a", "box"), step("sendB", "b", "list"), drop])
        .build();
    let verify = |no_reaping: bool| {
        SmtVerifier::for_net(&net)
            .initial_marking(MarkingStateBuilder::new().tokens("a", 1).tokens("b", 1).build())
            .mint_transitions(["sendA", "sendB"].map(String::from))
            .carrier_places(["box", "list"].map(String::from))
            .fragment_mode(FragmentMode::Extended)
            .assume_no_reaping(no_reaping)
            .property(SmtProperty::quiescent_name_aligned("box", "list"))
            .verify()
    };
    let late = verify(false);
    assert_eq!(late.route, VerificationRoute::NuScg);
    assert!(late.is_violated(), "{}", late.report);
    assert_eq!(late.counterexample_transitions, ["sendA", "sendB"]);
    let on_time = verify(true);
    assert_eq!(on_time.route, VerificationRoute::NuScg);
    assert!(on_time.is_proven(), "{}", on_time.report);
}

// ── the dispatcher (AC4) ──────────────────────────────────────────────────────

/// [NU-055] AC4: a declared budget place, which keeps reachability-safety on Route A
/// ([NU-050]), does not apply to `NameAligned`.
#[test]
fn nu055_ac4_a_declared_budget_place_still_sends_name_aligned_to_route_b() {
    let r = verify_fixture(&fixture_by_id("nu-aligned-search-budget-transient-violated"));
    assert_eq!(r.route, VerificationRoute::NuScg);
    assert!(!r.report.contains("Route A"), "{}", r.report);
}

/// [NU-055] AC4: a Route B truncation stays `Unknown`, with no deferral to Route A
/// ([NU-053]) even with a budget place declared.
#[test]
fn nu055_ac4_a_route_b_truncation_stays_unknown_with_no_deferral_to_route_a() {
    let f = fixture_by_id("nu-aligned-search-quiescent-proven");
    let net = relay_fixtures::fixture_net(&f);
    let r = verify_fixture_with(&f, &net, |v| v.budget_place("slot").nu_max_classes(5));
    assert_eq!(r.route, VerificationRoute::NuScg);
    assert!(reason(&r).contains("truncated at 5 classes"), "{}", r.report);
    assert!(!r.report.contains("deferring to"), "{}", r.report);
}

/// [NU-055] AC4, [VER-012] AC3 and AC5: `NameAligned` stops at its first violating class, and
/// a truncated graph is violated by a stored class, else `Unknown`.
#[test]
fn nu055_ac4_prefix_rule_for_name_aligned() {
    let f = fixture_by_id("nu-aligned-search-transient-violated");
    let net = relay_fixtures::fixture_net(&f);
    let full = verify_fixture_with(&f, &net, |v| v);
    assert!(full.report.contains("Route B stopped at the first violating class"), "{}", full.report);
    let cut = verify_fixture_with(&f, &net, |v| v.nu_max_classes(20));
    assert_eq!(cut.route, VerificationRoute::NuScg);
    assert_eq!(verdict(&cut), "unknown", "{}", cut.report);
    let prefix = verify_fixture_with(&f, &net, |v| v.nu_max_classes(25));
    assert!(prefix.is_violated(), "{}", prefix.report);
    assert_eq!(prefix.counterexample_transitions.len(), 8);
}

/// [NU-055] AC4, [VER-012] AC3: a truncated `QuiescentNameAligned` graph is violated by an
/// expanded class at rest. `gen` grows `junk` without bound, so the graph never closes; `stop`
/// ends the generator, and after `sendA` and `sendB` minted two names into `box` and `list`
/// the net rests misaligned. The net has no matched transition at all.
#[test]
fn nu055_ac4_prefix_rule_for_quiescent_name_aligned() {
    let rows: Vec<Row> = vec![
        t("sendA", &["a"], &["box"]),
        t("sendB", &["b"], &["list"]),
        t("gen", &["g"], &["g", "junk"]),
        t("stop", &["g"], &["done"]),
    ];
    let net = pnid_net("unboundedRest", &rows);
    let r = SmtVerifier::for_net(&net)
        .initial_marking(MarkingStateBuilder::new().tokens("a", 1).tokens("b", 1).tokens("g", 1).build())
        .mint_transitions(["sendA", "sendB"].map(String::from))
        .carrier_places(["box", "list"].map(String::from))
        .fragment_mode(FragmentMode::Extended)
        .nu_max_classes(50)
        .property(SmtProperty::quiescent_name_aligned("box", "list"))
        .verify();
    assert_eq!(r.route, VerificationRoute::NuScg);
    assert!(r.is_violated(), "{}", r.report);
    assert_eq!(r.counterexample_transitions.len(), 3);
    assert!(
        r.report.contains("was truncated at 50 classes; the violation was found in the explored prefix"),
        "{}",
        r.report
    );
}

/// [NU-055] AC4: the has-match gate is lifted for name alignment only. On the bug variant,
/// which has no matched transition, a `QuiescentCount` is still decided by the plain
/// enumeration ([VER-017]) and `DeadlockFree` stays off Route B.
#[test]
fn nu055_ac4_existing_properties_on_the_matchless_bug_variant_keep_their_route() {
    let f = fixture_by_id("nu-aligned-search-bug-quiescent-violated");
    let net = relay_fixtures::fixture_net(&f);
    assert!(net.transitions().iter().all(|t| t.match_spec().is_none()));
    let count = verify_fixture_with(&f, &net, |v| {
        v.property(SmtProperty::quiescent_count(vec!["list".into()], 1, Some(1), Vec::new()))
    });
    assert_eq!(count.route, VerificationRoute::Enumeration, "{}", count.report);
    let deadlock = verify_fixture_with(&f, &net, |v| v.property(SmtProperty::DeadlockFree));
    assert_ne!(deadlock.route, VerificationRoute::NuScg, "{}", deadlock.report);
    let aligned = verify_fixture(&f);
    assert_eq!(aligned.route, VerificationRoute::NuScg);
}

/// [NU-055] AC4: `encode_scripts` returns no script for `NameAligned`.
#[test]
#[should_panic(expected = "Name alignment of box and list is decided only by the name-partition state-class graph (NU-055, Route B)")]
fn nu055_ac4_encode_scripts_has_no_script_for_name_aligned() {
    let f = fixture_by_id("nu-aligned-search-quiescent-proven");
    let net = relay_fixtures::fixture_net(&f);
    SmtVerifier::for_net(&net)
        .initial_marking(fixture_marking(&f))
        .property(SmtProperty::name_aligned("box", "list"))
        .encode_scripts();
}

/// [NU-055] AC4: `encode_scripts` returns no script for `QuiescentNameAligned`.
#[test]
#[should_panic(expected = "Quiescent name alignment of box and list is decided only by the name-partition state-class graph (NU-055, Route B)")]
fn nu055_ac4_encode_scripts_has_no_script_for_quiescent_name_aligned() {
    let f = fixture_by_id("nu-aligned-search-quiescent-proven");
    let net = relay_fixtures::fixture_net(&f);
    SmtVerifier::for_net(&net)
        .initial_marking(fixture_marking(&f))
        .property(SmtProperty::quiescent_name_aligned("box", "list"))
        .encode_scripts();
}
