//! The state-space cache of the enumeration route ([VER-017] AC7-AC10).
//!
//! Every query here is decided or declined by enumeration before any solver is
//! resolved, except where a truncation falls through to the SMT pipeline; those
//! tests assert only on the enumeration part of the report, which is written
//! before the pipeline runs, so they hold with or without `z3` on `PATH`.

#![cfg(feature = "z3")]

use std::sync::Barrier;
use std::thread;

use libpetri_core::action::fork;
use libpetri_core::arc::inhibitor;
use libpetri_core::input::{exactly, one};
use libpetri_core::output::{and_places, out_place};
use libpetri_core::petri_net::PetriNet;
use libpetri_core::place::Place;
use libpetri_core::transition::Transition;
use libpetri_verification::marking_state::{MarkingState, MarkingStateBuilder};
use libpetri_verification::property::SmtProperty;
use libpetri_verification::result::{VerificationResult, VerificationRoute};
use libpetri_verification::smt_verifier::SmtVerifier;
use libpetri_verification::state_space_cache::StateSpaceCache;

const REUSED: &str = "Bounded state-space enumeration: reused cached state space (";
const CACHED_TRUNCATION: &str = "Bounded state-space enumeration: cached truncation at ";

/// How [`pipeline_with`] departs from the plain pipeline, to build nets that differ
/// in exactly one thing the graph reads.
#[derive(Clone, Copy, PartialEq)]
enum Variant {
    Plain,
    /// `t0` consumes two tokens instead of one.
    Cardinality,
    /// `t0` has priority 5.
    Priority,
    /// `t1` is inhibited by `p5`.
    Inhibitor,
    /// `p_n` is a terminal place ([EXEC-042]).
    Terminal,
}

/// `p0 -> t0 -> p1 -> … -> pn`, untimed: `n + 1` classes from one token in `p0`.
fn pipeline_with(n: usize, variant: Variant) -> PetriNet {
    let mut builder = PetriNet::builder(format!("pipeline{n}"));
    for i in 0..n {
        let from = Place::<()>::new(format!("p{i}"));
        let to = Place::<()>::new(format!("p{}", i + 1));
        let input = if i == 0 && variant == Variant::Cardinality {
            exactly(2, &from)
        } else {
            one(&from)
        };
        let mut t = Transition::builder(format!("t{i}"))
            .input(input)
            .output(out_place(&to))
            .action(fork());
        if i == 0 && variant == Variant::Priority {
            t = t.priority(5);
        }
        if i == 1 && variant == Variant::Inhibitor {
            t = t.inhibitor(inhibitor(&Place::<()>::new("p5")));
        }
        builder = builder.transition(t.build());
    }
    if variant == Variant::Terminal {
        builder = builder.terminals([Place::<()>::new(format!("p{n}")).as_ref()]);
    }
    builder.build()
}

fn pipeline(n: usize) -> PetriNet {
    pipeline_with(n, Variant::Plain)
}

fn tokens_in_p0(count: usize) -> MarkingState {
    MarkingStateBuilder::new().tokens("p0", count).build()
}

fn query<'n>(net: &'n PetriNet, m0: &MarkingState, sinks: &[&str]) -> SmtVerifier<'n> {
    SmtVerifier::for_net(net)
        .initial_marking(m0.clone())
        .property(SmtProperty::DeadlockFree)
        .sink_places(sinks.iter().map(|s| s.to_string()))
}

/// The report without the cache's own line and the timing line, which is all a
/// cached answer may add or change.
fn report_body(result: &VerificationResult) -> String {
    result
        .report
        .lines()
        .filter(|l| !l.starts_with(REUSED) && !l.starts_with("Elapsed:"))
        .collect::<Vec<_>>()
        .join("\n")
}

/// Verdict, witness (order of listing included, via `Debug`), confirmation, route
/// and report all agree.
fn assert_same_answer(cached: &VerificationResult, fresh: &VerificationResult) {
    assert_eq!(cached.verdict, fresh.verdict);
    assert_eq!(cached.route, fresh.route);
    assert_eq!(
        format!("{:?}", cached.counterexample_trace),
        format!("{:?}", fresh.counterexample_trace)
    );
    assert_eq!(cached.counterexample_transitions, fresh.counterexample_transitions);
    assert_eq!(cached.counterexample_confirmed, fresh.counterexample_confirmed);
    assert_eq!(report_body(cached), report_body(fresh));
}

/// AC7: the second and later queries build no graph, and answer exactly as a query
/// without the cache does — a proof and a violation with its witness.
#[test]
fn later_queries_reuse_the_graph_and_answer_as_without_it() {
    let net = pipeline(6);
    // Listed out of code-point order, so the witness's first state shows whether
    // it came from the caller's marking.
    let m0 = MarkingStateBuilder::new().tokens("p0", 1).tokens("aside", 1).build();
    let cache = StateSpaceCache::new();

    let first = query(&net, &m0, &["p6"]).state_space_cache(&cache).verify();
    assert_eq!(cache.build_count(), 1);
    // `aside` is not a sink here, so its token is stranded: violated.
    assert!(first.is_violated(), "{}", first.report);
    assert!(!first.report.contains(REUSED), "{}", first.report);

    let proven = query(&net, &m0, &["p6", "aside"]).state_space_cache(&cache).verify();
    let violated = query(&net, &m0, &["p6"]).state_space_cache(&cache).verify();
    let bound = SmtVerifier::for_net(&net)
        .initial_marking(m0.clone())
        .property(SmtProperty::place_bound("p6", 1))
        .state_space_cache(&cache)
        .verify();
    assert_eq!(cache.build_count(), 1, "later queries must not build");
    assert_eq!(cache.len(), 1);

    for result in [&proven, &violated, &bound] {
        assert_eq!(result.route, VerificationRoute::Enumeration, "{}", result.report);
        assert!(
            result
                .report
                .contains("Bounded state-space enumeration: reused cached state space (7 classes) (VER-017).\n=== Bounded state-space enumeration (VER-017) ==="),
            "{}",
            result.report
        );
    }
    assert!(proven.is_proven(), "{}", proven.report);
    assert!(violated.is_violated(), "{}", violated.report);
    assert_eq!(violated.counterexample_transitions.len(), 6);

    assert_same_answer(&proven, &query(&net, &m0, &["p6", "aside"]).verify());
    assert_same_answer(&violated, &query(&net, &m0, &["p6"]).verify());
    assert_same_answer(
        &bound,
        &SmtVerifier::for_net(&net)
            .initial_marking(m0.clone())
            .property(SmtProperty::place_bound("p6", 1))
            .verify(),
    );
}

/// A witness from a cached graph starts at the caller's own listing of the initial
/// marking, not the listing the graph was first built from.
#[test]
fn a_reused_witness_starts_at_the_callers_listing() {
    let net = pipeline(3);
    let ab = MarkingStateBuilder::new().tokens("p0", 1).tokens("aside", 1).build();
    let ba = MarkingStateBuilder::new().tokens("aside", 1).tokens("p0", 1).build();
    let cache = StateSpaceCache::new();
    query(&net, &ab, &["p3"]).state_space_cache(&cache).verify();
    let cached = query(&net, &ba, &["p3"]).state_space_cache(&cache).verify();
    assert_eq!(cache.build_count(), 1, "the same counts listed differently must hit");
    assert!(cached.report.contains(REUSED), "{}", cached.report);
    assert_same_answer(&cached, &query(&net, &ba, &["p3"]).verify());
}

/// AC8: a truncation at `B` declines every budget `<= B` without building; a larger
/// budget builds and replaces it. A closed graph of `C` classes answers a budget
/// `<= C` as truncated.
#[test]
fn a_cached_truncation_declines_smaller_budgets_and_larger_ones_replace_it() {
    let net = pipeline(6); // 7 classes
    let m0 = tokens_in_p0(1);
    let cache = StateSpaceCache::new();
    let at = |budget: usize| {
        query(&net, &m0, &["p6"])
            .enumeration_max_classes(budget)
            .state_space_cache(&cache)
            .verify()
    };
    let truncated = |budget: usize| {
        format!(
            "Bounded state-space enumeration truncated at {budget} classes (VER-017); \
             verifying via the SMT pipeline.\n"
        )
    };
    let cached = |budget: usize| {
        format!(
            "Bounded state-space enumeration: cached truncation at {budget} classes (VER-017); \
             verifying via the SMT pipeline.\n"
        )
    };

    let r = at(3);
    assert_eq!(cache.build_count(), 1);
    assert!(r.report.contains(&truncated(3)) && !r.report.contains(CACHED_TRUNCATION), "{}", r.report);

    for budget in [3, 2, 1] {
        let r = at(budget);
        assert_eq!(cache.build_count(), 1, "budget {budget} must decline without building");
        // The cached line names THIS query's budget and precedes the truncation line.
        assert!(
            r.report.contains(&format!("{}{}", cached(budget), truncated(budget))),
            "{}",
            r.report
        );
    }

    let r = at(5); // larger: builds, truncates again, replaces the entry at 5
    assert_eq!(cache.build_count(), 2);
    assert!(!r.report.contains(CACHED_TRUNCATION), "{}", r.report);
    at(4);
    assert_eq!(cache.build_count(), 2, "the replaced entry declines 4");

    let r = at(1000); // closes, replaces the truncation
    assert_eq!(cache.build_count(), 3);
    assert_eq!(r.route, VerificationRoute::Enumeration, "{}", r.report);
    assert!(!r.report.contains(REUSED), "{}", r.report);
    assert_eq!(cache.len(), 1);

    // Closed at 7: budget 7 would have truncated, and is answered as truncated.
    let r = at(7);
    assert_eq!(cache.build_count(), 3);
    assert!(r.report.contains(&format!("{}{}", cached(7), truncated(7))), "{}", r.report);
    let r = at(8);
    assert_eq!(cache.build_count(), 3);
    assert_eq!(r.route, VerificationRoute::Enumeration, "{}", r.report);
    assert!(r.report.contains(REUSED), "{}", r.report);
}

/// AC9: a different initial marking never hits another entry.
#[test]
fn a_different_initial_marking_misses() {
    let net = pipeline(4);
    let cache = StateSpaceCache::new();
    query(&net, &tokens_in_p0(1), &["p4"]).state_space_cache(&cache).verify();
    let two = query(&net, &tokens_in_p0(2), &["p4"]).state_space_cache(&cache).verify();
    assert_eq!(cache.build_count(), 2);
    assert!(!two.report.contains(REUSED), "{}", two.report);
    assert_same_answer(&two, &query(&net, &tokens_in_p0(2), &["p4"]).verify());
    assert_eq!(cache.len(), 2);
}

/// AC9: a net that differs in one arc cardinality, one priority or one inhibitor
/// never hits another net's entry.
#[test]
fn a_structurally_different_net_misses() {
    let m0 = tokens_in_p0(2);
    let cache = StateSpaceCache::new();
    let variants = [Variant::Plain, Variant::Cardinality, Variant::Priority, Variant::Inhibitor];
    for (i, variant) in variants.into_iter().enumerate() {
        let net = pipeline_with(6, variant);
        let cached = query(&net, &m0, &["p6"]).state_space_cache(&cache).verify();
        assert_eq!(cache.build_count(), i + 1, "variant {i} must not hit");
        assert!(!cached.report.contains(REUSED), "{}", cached.report);
        assert_same_answer(&cached, &query(&net, &m0, &["p6"]).verify());
    }
}

/// Two clones of one net — the Python binding clones on every call — and a second
/// net built the same way hit one entry.
#[test]
fn clones_and_rebuilds_of_one_net_hit() {
    let net = pipeline(5);
    let m0 = tokens_in_p0(1);
    let cache = StateSpaceCache::new();
    let a = net.clone();
    let b = net.clone();
    let rebuilt = pipeline(5);
    query(&a, &m0, &["p5"]).state_space_cache(&cache).verify();
    let from_b = query(&b, &m0, &["p5"]).state_space_cache(&cache).verify();
    let from_rebuilt = query(&rebuilt, &m0, &["p5"]).state_space_cache(&cache).verify();
    assert_eq!(cache.build_count(), 1);
    assert!(from_b.report.contains(REUSED), "{}", from_b.report);
    assert!(from_rebuilt.report.contains(REUSED), "{}", from_rebuilt.report);
}

/// A net whose transition fans out to several fresh places lists them in the order of
/// `Transition::output_places`, a `HashSet` seeded afresh per build, so each rebuild
/// may list `PetriNet::places` differently. The graph never reads that order, so
/// every rebuild must still hit.
#[test]
fn rebuilds_that_list_their_places_in_another_order_hit() {
    fn fan_out() -> PetriNet {
        let p0 = Place::<()>::new("p0");
        let outs: Vec<Place<()>> = (0..6).map(|i| Place::new(format!("q{i}"))).collect();
        let refs: Vec<_> = outs.iter().map(|p| p.as_ref()).collect();
        let refs: Vec<_> = refs.iter().collect();
        PetriNet::builder("fan")
            .transition(
                Transition::builder("t")
                    .input(one(&p0))
                    .output(and_places(&refs))
                    .action(fork())
                    .build(),
            )
            .build()
    }
    let m0 = tokens_in_p0(1);
    let cache = StateSpaceCache::new();
    let mut orders = std::collections::HashSet::new();
    for _ in 0..16 {
        let net = fan_out();
        orders.insert(net.places().iter().map(|p| p.name().to_string()).collect::<Vec<_>>());
        query(&net, &m0, &["q0", "q1", "q2", "q3", "q4", "q5"])
            .state_space_cache(&cache)
            .verify();
    }
    assert!(orders.len() > 1, "the rebuilds must list their places in more than one order");
    assert_eq!(cache.build_count(), 1, "a rebuild listing its places in another order missed");
}

/// A net with terminal places ([EXEC-042]) is rewritten per verification; the entry
/// is keyed on the caller's net, so the second query still hits.
#[test]
fn a_net_with_terminals_hits() {
    let net = pipeline_with(4, Variant::Terminal);
    let m0 = tokens_in_p0(1);
    let cache = StateSpaceCache::new();
    let first = query(&net, &m0, &[]).state_space_cache(&cache).verify();
    let second = query(&net, &m0, &[]).state_space_cache(&cache).verify();
    assert_eq!(cache.build_count(), 1);
    assert!(first.is_proven(), "{}", first.report);
    assert!(second.report.contains(REUSED), "{}", second.report);
    assert_same_answer(&second, &query(&net, &m0, &[]).verify());

    // The terminal declaration is part of the key: the plain net misses.
    query(&pipeline(4), &m0, &[]).state_space_cache(&cache).verify();
    assert_eq!(cache.build_count(), 2);
}

/// AC10: eight threads sharing a cache on one net build its graph once.
#[test]
fn parallel_queries_build_once() {
    // Large enough that the build is still running when the other threads arrive.
    let net = pipeline(3000);
    let m0 = tokens_in_p0(1);
    let cache = StateSpaceCache::new();
    let start = Barrier::new(8);
    let results: Vec<VerificationResult> = thread::scope(|scope| {
        let handles: Vec<_> = (0..8)
            .map(|_| {
                scope.spawn(|| {
                    start.wait();
                    query(&net, &m0, &["p3000"]).state_space_cache(&cache).verify()
                })
            })
            .collect();
        handles.into_iter().map(|h| h.join().expect("query thread")).collect()
    });
    assert_eq!(cache.build_count(), 1);
    assert_eq!(results.iter().filter(|r| !r.report.contains(REUSED)).count(), 1);
    for r in &results {
        assert!(r.is_proven(), "{}", r.report);
        assert_eq!(r.route, VerificationRoute::Enumeration);
    }
}

/// `clear` drops every entry; the next query builds again.
#[test]
fn clear_forgets_every_entry() {
    let net = pipeline(3);
    let m0 = tokens_in_p0(1);
    let cache = StateSpaceCache::new();
    query(&net, &m0, &["p3"]).state_space_cache(&cache).verify();
    cache.clear();
    assert!(cache.is_empty());
    let again = query(&net, &m0, &["p3"]).state_space_cache(&cache).verify();
    assert!(!again.report.contains(REUSED), "{}", again.report);
    assert_eq!(cache.build_count(), 2);
}
