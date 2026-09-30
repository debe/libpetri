//! \[NU-054\] join relay in the analysis: the join chain (AC3), BASE ignoring the
//! declaration (AC5), the PNID fixtures of the spec's test derivation, a
//! correlated self-loop, and Route A against Route B on every fixture both
//! decide (AC6). The same queries, and the same expected verdicts, as
//! TypeScript's `tests/verification/nu-join-relay.test.ts` and Java's
//! `JoinRelayTest`.

#![cfg(feature = "z3")]

#[path = "common/json.rs"]
mod json;
#[path = "common/relay_fixtures.rs"]
mod relay_fixtures;
#[path = "common/relay_nets.rs"]
mod relay_nets;

use libpetri_verification::marking_state::MarkingStateBuilder;
use libpetri_verification::name_fragment::FragmentMode;
use libpetri_verification::property::SmtProperty;
use libpetri_verification::result::{VerificationResult, VerificationRoute};
use libpetri_verification::smt_verifier::{SmtVerifier, z3_available};

use relay_nets::*;

use libpetri_core::action::fork;
use libpetri_core::input::one;
use libpetri_core::match_spec::MatchSpec;
use libpetri_core::name::NameId;
use libpetri_core::output::{Out, and, forward_input, out_place, timeout, xor};
use libpetri_core::petri_net::PetriNet;
use libpetri_core::place::Place;
use libpetri_core::transition::Transition;

#[derive(Clone)]
struct Q {
    rows: Vec<Row>,
    marking: Vec<(&'static str, usize)>,
    property: SmtProperty,
    sinks: Vec<&'static str>,
    budgets: Vec<&'static str>,
    carriers: Vec<&'static str>,
    mode: FragmentMode,
}

impl Q {
    fn new(rows: Vec<Row>, marking: &[(&'static str, usize)], property: SmtProperty) -> Self {
        Self {
            rows,
            marking: marking.to_vec(),
            property,
            sinks: Vec::new(),
            budgets: Vec::new(),
            carriers: Vec::new(),
            mode: FragmentMode::Extended,
        }
    }
    fn sinks(mut self, s: &[&'static str]) -> Self {
        self.sinks = s.to_vec();
        self
    }
    fn budgets(mut self, s: &[&'static str]) -> Self {
        self.budgets = s.to_vec();
        self
    }
    fn carriers(mut self, s: &[&'static str]) -> Self {
        self.carriers = s.to_vec();
        self
    }
    fn mode(mut self, m: FragmentMode) -> Self {
        self.mode = m;
        self
    }
}

/// Verifies `q`; `with_budget` declares its budget places, `nu_max_classes`
/// caps Route B (1 forces a bounded quiescence query past it, onto Route A).
fn verify(q: &Q, with_budget: bool, nu_max_classes: usize, timeout_ms: u64) -> VerificationResult {
    verify_with(q, with_budget, nu_max_classes, timeout_ms, true)
}

/// [`verify`], with the [VER-015] linear bound switched by `linear_bound`: off, a
/// budgeted reachability-safety query reaches the coloured IC3 even when the
/// linear bound would prove it first.
fn verify_with(
    q: &Q,
    with_budget: bool,
    nu_max_classes: usize,
    timeout_ms: u64,
    linear_bound: bool,
) -> VerificationResult {
    let net = pnid_net("relay", &q.rows);
    let mut m = MarkingStateBuilder::new();
    for (p, k) in &q.marking {
        m = m.tokens(*p, *k);
    }
    let mut v = SmtVerifier::for_net(&net)
        .enumeration_max_classes(0)
        .initial_marking(m.build())
        .property(q.property.clone())
        .fragment_mode(q.mode)
        .nu_max_classes(nu_max_classes)
        .timeout(timeout_ms)
        .linear_bound(linear_bound);
    if !q.sinks.is_empty() {
        v = v.sink_places(q.sinks.iter().map(|s| s.to_string()));
    }
    if with_budget && !q.budgets.is_empty() {
        v = v.budget_places(q.budgets.iter().map(|s| s.to_string()));
    } else {
        // Without the budget declaration the mints are declared by name ([NU-010]):
        // the transitions that consume a budget place.
        let mints = net
            .transitions()
            .iter()
            .filter(|t| t.input_specs().iter().any(|s| q.budgets.contains(&s.place_name())))
            .map(|t| t.name().to_string());
        v = v.mint_transitions(mints);
    }
    if !q.carriers.is_empty() {
        v = v.carrier_places(q.carriers.iter().map(|s| s.to_string()));
    }
    v.verify()
}

fn route_b(q: &Q) -> VerificationResult {
    verify(q, true, 100_000, 60_000)
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

fn unreachable(p: &str) -> SmtProperty {
    SmtProperty::unreachable(vec![p.to_string()])
}

// ── AC3: the join chain, through Route B ─────────────────────────────────────

#[test]
fn chain_reaches_done_and_is_deadlock_free_via_route_b() {
    let reach = verify(
        &Q::new(join_chain(), &[("S", 1)], unreachable("done")).budgets(&["S"]),
        false,
        100_000,
        60_000,
    );
    assert_eq!(reach.route, VerificationRoute::NuScg, "{}", reach.report);
    assert!(reach.is_violated(), "{}", reach.report);
    assert_eq!(reach.counterexample_transitions, vec!["fork", "j1", "j2"]);

    let dlf = route_b(&Q::new(join_chain(), &[("S", 1)], SmtProperty::DeadlockFree).sinks(&["done"]).budgets(&["S"]));
    assert_eq!(dlf.route, VerificationRoute::NuScg, "{}", dlf.report);
    assert!(dlf.is_proven(), "{}", dlf.report);
}

#[test]
fn chain_with_an_independent_mint_never_reaches_done() {
    let r = verify(
        &Q::new(join_chain_split(), &[("S", 1), ("S2", 1)], unreachable("done")).budgets(&["S", "S2"]),
        false,
        100_000,
        60_000,
    );
    assert_eq!(r.route, VerificationRoute::NuScg, "{}", r.report);
    assert!(r.is_proven(), "no two different names are equated:\n{}", r.report);
}

#[test]
fn chain_without_the_declaration_falls_back() {
    let r = route_b(
        &Q::new(without_relays(&join_chain()), &[("S", 1)], SmtProperty::DeadlockFree).sinks(&["done"]),
    );
    assert_eq!(verdict(&r), "unknown", "{}", r.report);
    assert!(r.report.contains("EXTENDED) declined"), "{}", r.report);
    assert!(
        r.report.contains("a join writes a coloured place it does not declare as a relay target); \
             verified via sound over-approximation instead."),
        "{}",
        r.report
    );
}

// ── PNID fixtures ─────────────────────────────────────────────────────────────

fn fig12c_deadlock(relay: bool, k: usize, mode: FragmentMode) -> Q {
    let rows = if relay { fig_12c() } else { without_relays(&fig_12c()) };
    Q::new(rows, &[("R", k)], SmtProperty::DeadlockFree)
        .sinks(&["R"])
        .budgets(&["R"])
        .carriers(&FIG_12C_CARRIERS)
        .mode(mode)
}

fn fig12c_bound(k: usize, bound: usize) -> Q {
    Q::new(fig_12c(), &[("R", k)], SmtProperty::place_bound("OR", bound))
        .sinks(&["R"])
        .budgets(&["R"])
        .carriers(&FIG_12C_CARRIERS)
}

#[test]
fn fig12c_with_the_relay_is_deadlock_free_and_bounded_via_route_b() {
    // Paper label (Fig. 12(c)): identifier sound, bounded — both hold.
    for k in [1, 2] {
        let dlf = route_b(&fig12c_deadlock(true, k, FragmentMode::Extended));
        assert_eq!(dlf.route, VerificationRoute::NuScg, "k={k}\n{}", dlf.report);
        assert!(dlf.is_proven(), "k={k}\n{}", dlf.report);
        // No budget declared: the reachability-safety query goes to Route B.
        let bound = verify(&fig12c_bound(k, 2), false, 100_000, 60_000);
        assert_eq!(bound.route, VerificationRoute::NuScg, "k={k}\n{}", bound.report);
        assert!(bound.is_proven(), "k={k}\n{}", bound.report);
    }
}

#[test]
fn fig12c_without_the_relay_extended_declines() {
    let r = route_b(&fig12c_deadlock(false, 1, FragmentMode::Extended));
    assert_eq!(verdict(&r), "unknown", "{}", r.report);
    assert!(r.report.contains("ν-net Route B (EXTENDED) declined"), "{}", r.report);
}

/// AC5: under BASE a relay declaration changes no verdict, and the report names it.
#[test]
fn fig12c_under_base_ignores_the_declaration_and_says_so() {
    let with = route_b(&fig12c_deadlock(true, 1, FragmentMode::Base));
    let without = route_b(&fig12c_deadlock(false, 1, FragmentMode::Base));
    assert_eq!(verdict(&with), verdict(&without), "{}", with.report);
    assert_eq!(with.route, without.route);
    assert!(
        with.report.contains(
            "NOTE: ν relay declarations ignored under BASE fragment mode (NU-054): 'e' -> 'P5'; \
             select fragment_mode(FragmentMode::Extended) to analyse the joins as relays."
        ),
        "{}",
        with.report
    );
    assert!(!without.report.contains("NU-054"), "{}", without.report);
}

fn n1_deadlock(k: usize) -> Q {
    Q::new(n1_corr(), &[("SUPPLY", k)], SmtProperty::DeadlockFree)
        .sinks(&["E_done"])
        .budgets(&["SUPPLY"])
}

#[test]
fn n1_correlated_deadlock_violated_with_trace_a_c() {
    // Spec NU-054 expects Violated with A, C (C moves the case's Y1 token before B
    // joins on it, stranding p). The paper labels N1 identifier sound; reported,
    // not tuned.
    for k in [1, 2] {
        let r = route_b(&n1_deadlock(k));
        assert_eq!(r.route, VerificationRoute::NuScg, "k={k}\n{}", r.report);
        assert!(r.is_violated(), "k={k}\n{}", r.report);
        let expected: Vec<&str> = if k == 1 { vec!["A", "C"] } else { vec!["A", "A", "C", "C"] };
        assert_eq!(r.counterexample_transitions, expected, "k={k}\n{}", r.report);
    }
    let before = route_b(&Q {
        rows: without_relays(&n1_corr()),
        ..n1_deadlock(1)
    });
    assert_eq!(verdict(&before), "unknown", "{}", before.report);
}

fn union_deadlock(relay: bool, k: usize) -> Q {
    let rows = if relay { s_union() } else { without_relays(&s_union()) };
    Q::new(rows, &[("SUPPLY", k)], SmtProperty::DeadlockFree)
        .sinks(&["d_done"])
        .budgets(&["SUPPLY"])
        .carriers(&["q"])
}

#[test]
fn s_union_deadlock_violated_with_trace_a_via_route_b() {
    let before = route_b(&union_deadlock(false, 1));
    assert!(before.report.contains("ν-net Route B (EXTENDED) declined"), "{}", before.report);
    for k in [1, 2] {
        let r = route_b(&union_deadlock(true, k));
        assert_eq!(r.route, VerificationRoute::NuScg, "k={k}\n{}", r.report);
        assert!(r.is_violated(), "k={k}\n{}", r.report);
        if k == 1 {
            assert_eq!(r.counterexample_transitions, vec!["a"], "{}", r.report);
        }
    }
}

// ── correlated self-loop ─────────────────────────────────────────────────────

fn self_loop_deadlock(independent_q: bool, k: usize) -> Q {
    let (marking, budgets): (Vec<(&'static str, usize)>, &[&'static str]) = if independent_q {
        (vec![("S", k), ("T", k)], &["S", "T"])
    } else {
        (vec![("S", k)], &["S"])
    };
    Q::new(self_loop(independent_q), &marking, SmtProperty::DeadlockFree)
        .sinks(&["done"])
        .budgets(budgets)
}

#[test]
fn self_loop_relayed_name_reaches_the_next_join() {
    for k in [1, 2] {
        let ok = route_b(&self_loop_deadlock(false, k));
        assert_eq!(ok.route, VerificationRoute::NuScg, "{}", ok.report);
        assert!(ok.is_proven(), "k={k}\n{}", ok.report);
        let stuck = route_b(&self_loop_deadlock(true, k));
        assert_eq!(stuck.route, VerificationRoute::NuScg, "{}", stuck.report);
        assert!(stuck.is_violated(), "k={k}\n{}", stuck.report);
    }
}

// ── AC6: Route A (coloured IC3) against Route B ──────────────────────────────

fn is_quiescence(p: &SmtProperty) -> bool {
    matches!(p, SmtProperty::DeadlockFree | SmtProperty::JoinedOrDeadLettered { .. })
}

/// Route B and Route A on the same query. Quiescence: Route B by default, Route A
/// by forcing Route B to truncate (budget declared). Reachability-safety: Route A
/// with the budget declared, Route B without it. Spacer does not converge on the
/// proven quiescence queries within the timeout (as in TypeScript and Java): a
/// known solver limit, so there Route A must only never contradict Route B. The
/// [VER-015] linear bound is off for Route A, which would otherwise prove the
/// proven bounds before the coloured query.
fn assert_routes_agree(name: &str, q: &Q, expected: &str) {
    assert_routes(name, q, expected, false);
}

/// As [`assert_routes_agree`], but Route A may answer `unknown` within a short timeout. For
/// the larger instances, where Spacer finds the violation locally but not always on a slower
/// CI machine; Route A must still never contradict Route B.
fn assert_routes_agree_or_unknown(name: &str, q: &Q, expected: &str) {
    assert_routes(name, q, expected, true);
}

fn assert_routes(name: &str, q: &Q, expected: &str, a_may_be_unknown: bool) {
    let (b, a) = if is_quiescence(&q.property) {
        let timeout = if expected == "proven" || a_may_be_unknown { 10_000 } else { 60_000 };
        (verify(q, true, 100_000, 60_000), verify(q, true, 1, timeout))
    } else {
        (verify(q, false, 100_000, 60_000), verify_with(q, true, 100_000, 60_000, false))
    };
    assert_eq!(b.route, VerificationRoute::NuScg, "{name} Route B:\n{}", b.report);
    assert_eq!(verdict(&b), expected, "{name} Route B:\n{}", b.report);
    assert!(a.report.contains("ν-encoding: name-coloured"), "{name}: Route A must decide:\n{}", a.report);
    eprintln!("[NU-054 routes] {name}: Route B {}, Route A {}", verdict(&b), verdict(&a));
    if (is_quiescence(&q.property) && expected == "proven") || a_may_be_unknown {
        assert!(
            verdict(&a) == expected || verdict(&a) == "unknown",
            "{name} Route A contradicts Route B:\n{}",
            a.report
        );
    } else {
        assert_eq!(verdict(&a), expected, "{name} Route A:\n{}", a.report);
    }
}

#[test]
fn routes_agree_on_the_relay_fixtures() {
    if !z3_available() {
        eprintln!("skipping: no usable z3");
        return;
    }
    for k in [1, 2] {
        assert_routes_agree(&format!("Fig. 12(c) placeBound(OR, 2), k={k}"), &fig12c_bound(k, 2), "proven");
        assert_routes_agree(&format!("Fig. 12(c) deadlockFree, k={k}"), &fig12c_deadlock(true, k, FragmentMode::Extended), "proven");
        if k == 1 {
            assert_routes_agree("N1 deadlockFree, k=1", &n1_deadlock(k), "violated");
        } else {
            assert_routes_agree_or_unknown("N1 deadlockFree, k=2", &n1_deadlock(k), "violated");
        }
        assert_routes_agree(&format!("S union deadlockFree, k={k}"), &union_deadlock(true, k), "violated");
        assert_routes_agree(&format!("self-loop deadlockFree, k={k}"), &self_loop_deadlock(false, k), "proven");
    }
    assert_routes_agree("Fig. 12(c) placeBound(OR, 1), k=2", &fig12c_bound(2, 1), "violated");
    let n1 = |p: SmtProperty| Q { property: p, ..n1_deadlock(1) };
    assert_routes_agree("N1 unreachable(E_done), k=1", &n1(unreachable("E_done")), "violated");
    // The self-loop nets to zero on its key: B keeps one token of the case in Y1.
    assert_routes_agree("N1 placeBound(Y1, 1), k=1", &n1(SmtProperty::place_bound("Y1", 1)), "proven");
    assert_routes_agree(
        "join chain unreachable(done)",
        &Q::new(join_chain(), &[("S", 1)], unreachable("done")).budgets(&["S"]),
        "violated",
    );
    assert_routes_agree(
        "join chain deadlockFree, S=2",
        &Q::new(join_chain(), &[("S", 2)], SmtProperty::DeadlockFree).sinks(&["done"]).budgets(&["S"]),
        "proven",
    );
    assert_routes_agree(
        "split chain unreachable(done)",
        &Q::new(join_chain_split(), &[("S", 1), ("S2", 1)], unreachable("done")).budgets(&["S", "S2"]),
        "proven",
    );
    // k = 1 only: at k = 2 the covering semiflow gives six colour slots and Spacer
    // does not find the violation in time (as in Java).
    assert_routes_agree("self-loop independent q deadlockFree, k=1", &self_loop_deadlock(true, 1), "violated");
}

// ── the relay fixtures of the script-parity set ──────────────────────────────

/// Every fixture of `spec/verification-fixtures/nu-relay-fixtures.json` gets its declared
/// verdict from `verify()` with its declared options, so the parity goldens pin
/// the scripts of queries whose answers are known.
#[test]
fn relay_parity_fixtures_get_their_declared_verdicts() {
    if !z3_available() {
        eprintln!("skipping: no usable z3");
        return;
    }
    for fixture in relay_fixtures::relay_fixtures() {
        let id = fixture.str("id");
        let net = relay_fixtures::fixture_net(&fixture);
        let mut m = MarkingStateBuilder::new();
        for (p, k) in relay_fixtures::fixture_marking(&fixture) {
            m = m.tokens(p, k);
        }
        let prop = fixture.get("property").unwrap();
        let property = match prop.str("type") {
            "deadlock-free" => SmtProperty::DeadlockFree,
            "place-bound" => SmtProperty::place_bound(prop.str("place"), prop.usize("bound")),
            "unreachable" => unreachable(prop.str("place")),
            other => panic!("unmapped property '{other}'"),
        };
        assert_eq!(fixture.str("fragmentMode"), "extended", "{id}");
        let r = SmtVerifier::for_net(&net)
            .enumeration_max_classes(0)
            .initial_marking(m.build())
            .property(property)
            .fragment_mode(FragmentMode::Extended)
            .sink_places(fixture.str_arr_opt("sinkPlaces"))
            .budget_places(fixture.str_arr_opt("budgetPlaces"))
            .carrier_places(fixture.str_arr_opt("carrierPlaces"))
            .timeout(60_000)
            .verify();
        assert_eq!(verdict(&r), fixture.str("expected"), "{id}\n{}", r.report);
    }
}

// ── Route A: the fixed update order of a relaying join ───────────────────────

/// The NU-054 update of a relaying join, per colour: `(- x 1)` for each key column
/// that is not a relay target, then `(+ x 1)` for each relay-target column that is
/// not a key; a column that is both (the correlated self-loop's `Y`) keeps its
/// `>= 1` guard and is carried over unchanged. Places flatten in name order:
/// `S` m0, `Y` m1, `done` m2, `p` m3, `q` m4, the coloured ones one column per
/// colour slot.
#[test]
fn a_self_loop_key_is_guarded_and_carried_over_unchanged() {
    let net = pnid_net("selfLoop", &self_loop(false));
    let scripts = SmtVerifier::for_net(&net)
        .initial_marking(MarkingStateBuilder::new().tokens("S", 1).build())
        .property(SmtProperty::DeadlockFree)
        .sink_places(vec!["done".to_string()])
        .budget_places(vec!["S".to_string()])
        .fragment_mode(FragmentMode::Extended)
        .encode_scripts();
    let b_colour_0 = "            (>= m1_0 1)
            (>= m3_0 1)
            (= m0p m0)
            (= m1_0p m1_0)
            (= m1_1p m1_1)
            (= m2p m2)
            (= m3_0p (- m3_0 1))
            (>= m3_0p 0)
            (= m3_1p m3_1)
            (= m4_0p (+ m4_0 1))
            (>= m4_0p 0)
            (= m4_1p m4_1)
";
    assert!(scripts.horn.contains(b_colour_0), "{}", scripts.horn);
}

// ── [VER-015] the linear bound before the name-coloured encoding ─────────────

/// `placeBound(X, 1000)` at budget 2: trivially true, and out of Route A's reach
/// (its colour-slot bound is 2–4× the budget, so Spacer times out). The flat
/// state equation over-approximates the ν semantics, so its structural `Proven`
/// holds for the ν-net too and is returned before the coloured query.
#[test]
fn a_trivial_bound_on_a_budgeted_nu_net_is_proven_by_the_linear_bound() {
    if !z3_available() {
        eprintln!("skipping: no usable z3");
        return;
    }
    let cases = [
        ("N1", Q::new(n1_corr(), &[("SUPPLY", 2)], SmtProperty::place_bound("Y1", 1000)).budgets(&["SUPPLY"])),
        (
            "Fig. 12(c)",
            Q::new(fig_12c(), &[("R", 2)], SmtProperty::place_bound("P1", 1000))
                .sinks(&["R"])
                .budgets(&["R"])
                .carriers(&FIG_12C_CARRIERS),
        ),
        (
            "S union",
            Q::new(s_union(), &[("SUPPLY", 2)], SmtProperty::place_bound("p", 1000))
                .budgets(&["SUPPLY"])
                .carriers(&["q"]),
        ),
    ];
    for (name, q) in cases {
        let r = verify(&q, true, 100_000, 8_000);
        eprintln!("[VER-015 ν] {name}: {} {:?} {}ms", verdict(&r), r.route, r.elapsed_ms);
        assert!(r.is_proven(), "{name}\n{}", r.report);
        assert_eq!(r.route, VerificationRoute::Structural, "{name}\n{}", r.report);
        assert!(r.elapsed_ms < 1_000, "{name}: {}ms\n{}", r.elapsed_ms, r.report);
        assert!(
            r.report.contains("Result: property proven structurally (linear state-equation bound)"),
            "{name}\n{}",
            r.report
        );
        assert!(!r.report.contains("ν-encoding: name-coloured"), "{name}\n{}", r.report);
    }
}

/// A bound the linear bound cannot prove (it is violated) still reaches the
/// name-coloured encoding, with the verdict it had before.
#[test]
fn a_bound_the_linear_bound_cannot_prove_still_reaches_the_coloured_encoding() {
    if !z3_available() {
        eprintln!("skipping: no usable z3");
        return;
    }
    let r = verify(&fig12c_bound(2, 1), true, 100_000, 60_000);
    assert!(r.is_violated(), "{}", r.report);
    assert_eq!(r.route, VerificationRoute::Smt, "{}", r.report);
    assert!(r.report.contains("ν-encoding: name-coloured"), "{}", r.report);
    assert!(!r.report.contains("proven structurally"), "{}", r.report);
}

// ── A join's timeout writes into a relay target ──────────────────────────────

/// The AC3 join chain with `j1`'s relay into `C` written two ways: by the action,
/// or by the executor on timeout (`timeout_child`). `j1` also consumes the
/// uncoloured `Z`, so a forward of a non-key input can be stated.
fn chain_with_timeout(timeout_child: impl Fn(&Place<String>, &Place<String>, &Place<String>) -> Out) -> PetriNet {
    let p = |n: &str| Place::<String>::new(n);
    let key = |s: &String| NameId::new(s.clone());
    let (s, a, b, c, d, z, done) = (p("S"), p("A"), p("B"), p("C"), p("D"), p("Z"), p("done"));
    let fork_t = Transition::builder("fork")
        .input(one(&s))
        .output(and(vec![out_place(&a), out_place(&b), out_place(&d)]))
        .action(fork())
        .build();
    let j1 = Transition::builder("j1")
        .input(one(&a))
        .input(one(&b))
        .input(one(&z))
        .output(xor(vec![out_place(&c), timeout(10, timeout_child(&a, &z, &c))]))
        .match_spec(MatchSpec::builder().key(&a, key).key(&b, key).relay_to(&c, key).build())
        .action(fork())
        .build();
    let j2 = Transition::builder("j2")
        .input(one(&c))
        .input(one(&d))
        .output(out_place(&done))
        .match_spec(MatchSpec::builder().key(&c, key).key(&d, key).build())
        .action(fork())
        .build();
    PetriNet::builder("chain_timeout").transitions([fork_t, j1, j2]).build()
}

fn chain_timeout_deadlock(net: &PetriNet) -> VerificationResult {
    SmtVerifier::for_net(net)
        .enumeration_max_classes(0)
        .initial_marking(MarkingStateBuilder::new().tokens("S", 1).tokens("Z", 1).build())
        .property(SmtProperty::DeadlockFree)
        .sink_places(["done".to_string()])
        .budget_places(["S".to_string()])
        .fragment_mode(FragmentMode::Extended)
        // Out of the fragment, the net falls back to the count abstraction, which
        // cannot decide a quiescence property: nothing to wait for.
        .timeout(2_000)
        .verify()
}

/// The executor checks every token a join deposits in a relay target, timeout
/// branches included ([NU-054]). A unit token (`Out::Place` under `Timeout`) or a
/// forward of a non-key input carries no name or another one, so that firing
/// fails and deposits nothing: `A` and `B` are gone, `D` is stranded and the net
/// deadlocks. The name layer would relay the matched name into `C` instead and
/// let `j2` fire, a wrong `Proven`. Only a forward of a match key relays the
/// matched name, and only that timeout write keeps the join in the fragment.
#[test]
fn a_join_timeout_write_into_a_relay_target_must_forward_a_key() {
    let unit = chain_timeout_deadlock(&chain_with_timeout(|_, _, c| out_place(c)));
    let other = chain_timeout_deadlock(&chain_with_timeout(|_, z, c| forward_input(z, c)));
    for (what, r) in [("a unit token", &unit), ("the non-key Z", &other)] {
        assert!(!r.is_proven(), "timeout writes {what} into C:\n{}", r.report);
        // Both ν routes decline it: Route B, and Route A's coloured encoding.
        assert!(r.report.contains("Route B (EXTENDED) declined"), "{what}:\n{}", r.report);
        assert!(!r.report.contains("ν-encoding: name-coloured"), "{what}:\n{}", r.report);
    }

    let key = chain_timeout_deadlock(&chain_with_timeout(|a, _, c| forward_input(a, c)));
    assert_eq!(key.route, VerificationRoute::NuScg, "{}", key.report);
    assert!(key.is_proven(), "timeout forwards the key A into C:\n{}", key.report);
}
