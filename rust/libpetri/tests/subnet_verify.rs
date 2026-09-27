//! End-to-end integration tests for [`SubnetDef::verify`] (via the
//! [`libpetri_verification::harness::SubnetVerifyExt`] extension trait) per
//! `spec/11-modular-composition.md` requirement **MOD-051**.
//!
//! Mirrors `java/src/test/java/org/libpetri/verification/SubnetVerifyTest.java`
//! and `typescript/tests/verification/subnet-verify.test.ts`.
//!
//! Two layers of coverage:
//!
//! 1. **Pure harness-construction tests** (always-on): exercise the
//!    synthetic-net wiring, harness validation, and result aggregation
//!    without invoking Z3. These tests pass regardless of whether the `z3`
//!    feature is enabled.
//! 2. **End-to-end SMT tests** (gated on the `z3` feature + binary
//!    availability): run the verifier on the leaky-bucket fixture and
//!    assert the result is well-formed. Skipped automatically when the Z3
//!    binary is not on PATH (matches Java's `@EnabledIf` skip).
//!
//! Lives in the umbrella `libpetri` crate so it can take a workspace
//! dependency on `libpetri-verification` without creating a cycle through
//! `libpetri-core`.

use std::sync::Arc;

use libpetri::core::action::fork;
use libpetri::core::arc::inhibitor;
use libpetri::core::input::one;
use libpetri::core::output::out_place;
use libpetri::core::place::Place;
use libpetri::core::subnet_def::SubnetDef;
use libpetri::core::token::Token;
use libpetri::core::transition::Transition;
use libpetri::verification::harness::{
    SubnetVerifyExt, TokenSupplier, VerificationHarness, token_supplier,
};
#[cfg(feature = "z3")]
use libpetri::verification::property::SmtProperty;

// ============================================================
//  Fixtures (mirror Java's SubnetFixtures used by SubnetVerifyTest).
// ============================================================

fn leaky_bucket(rate: u32) -> SubnetDef<()> {
    assert!(rate >= 1, "rate must be >= 1, got: {rate}");
    let request = Place::<String>::new("request");
    let accept = Place::<String>::new("accept");
    let reject = Place::<String>::new("reject");
    let slots = Place::<String>::new("slots");

    let accept_t = Transition::builder("accept")
        .input(one(&request))
        .input(one(&slots))
        .output(out_place(&accept))
        .action(fork())
        .build();
    let reject_t = Transition::builder("reject")
        .input(one(&request))
        .inhibitor(inhibitor(&slots))
        .output(out_place(&reject))
        .action(fork())
        .build();

    SubnetDef::<()>::builder(format!("LeakyBucket-{rate}"))
        .place(&slots)
        .transition(accept_t)
        .transition(reject_t)
        .input_port("request", &request)
        .output_port("accept", &accept)
        .output_port("reject", &reject)
        .build()
}

fn producer() -> SubnetDef<()> {
    let next_item = Place::<String>::new("nextItem");
    let output = Place::<String>::new("output");
    let produce = Transition::builder("produce")
        .input(one(&next_item))
        .output(out_place(&output))
        .action(fork())
        .build();
    SubnetDef::<()>::builder("Producer")
        .place(&next_item)
        .transition(produce)
        .output_port("output", &output)
        .build()
}

fn consumer() -> SubnetDef<()> {
    let input = Place::<String>::new("input");
    let consumed = Place::<String>::new("consumed");
    let consume = Transition::builder("consume")
        .input(one(&input))
        .output(out_place(&consumed))
        .action(fork())
        .build();
    SubnetDef::<()>::builder("Consumer")
        .place(&consumed)
        .transition(consume)
        .input_port("input", &input)
        .build()
}

// ============================================================
//  Pure harness-construction tests (no Z3 invocation).
// ============================================================

#[test]
fn verify_output_only_subnet_constructs_synthetic_net() {
    // Producer fixture: only an Output port. An empty harness must succeed
    // structurally — the synthetic enclosing net is built and zero
    // properties run.
    let p = producer();
    let result = p.verify(VerificationHarness::<()>::new());

    assert!(result.per_property.is_empty());
    assert!(result.all_proven(), "vacuously true with zero properties");

    // The synthetic net must contain the harness_out_output observation
    // place and not the renamed sut/output port place.
    let names: Vec<&str> = result
        .synthetic_net
        .places()
        .iter()
        .map(|p| p.name())
        .collect();
    assert!(
        names.contains(&"harness_out_output"),
        "synthetic net must contain harness_out_output; got: {names:?}"
    );
    assert!(
        !names.contains(&"sut/output"),
        "sut/output must be substituted away by compose; got: {names:?}"
    );
}

#[test]
fn verify_synthetic_net_binds_all_ports() {
    // Leaky-bucket: 1 input + 2 output ports. Synthetic enclosing net
    // must contain a synthetic place per port plus the subnet's
    // internal places.
    let bucket = leaky_bucket(2);
    let supplier = token_supplier(|| Token::new(String::from("req")));

    let harness = VerificationHarness::<()>::new().input("request", supplier);
    let result = bucket.verify(harness);

    let names: std::collections::HashSet<&str> = result
        .synthetic_net
        .places()
        .iter()
        .map(|p| p.name())
        .collect();

    assert!(names.contains("harness_in_request"));
    assert!(names.contains("harness_out_accept"));
    assert!(names.contains("harness_out_reject"));
    // Internal place flows through with the prefix.
    assert!(names.contains("sut/slots"));
    // Renamed port places are gone.
    assert!(!names.contains("sut/request"));
    assert!(!names.contains("sut/accept"));
    assert!(!names.contains("sut/reject"));
}

#[test]
#[should_panic(expected = "request")]
fn verify_panics_when_input_generator_missing() {
    // Empty harness on a subnet with an input port must panic naming the
    // missing port.
    let bucket = leaky_bucket(2);
    let _ = bucket.verify(VerificationHarness::<()>::new());
}

#[test]
fn verify_input_generator_invoked_at_construction() {
    // Confirm the supplier is touched at synthetic-net build time so user
    // errors surface eagerly (matches Java/TS).
    let consumer = consumer();
    let count = Arc::new(std::sync::atomic::AtomicUsize::new(0));
    let count_clone = Arc::clone(&count);

    let tracker: TokenSupplier = Arc::new(move || {
        count_clone.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        libpetri::core::token::ErasedToken::from_typed(&Token::new(String::from(
            "tracked",
        )))
    });

    let harness = VerificationHarness::<()>::new().input("input", tracker);
    consumer.verify(harness);

    assert!(count.load(std::sync::atomic::Ordering::SeqCst) >= 1);
}

// ============================================================
//  End-to-end SMT verification (gated on z3 feature + binary).
// ============================================================

/// Probe whether a usable `z3` executable resolves (`PATH` or `LIBPETRI_Z3`,
/// at or above the version floor). Mirrors Java's `z3Available()` guard.
#[cfg(feature = "z3")]
fn z3_binary_available() -> bool {
    libpetri::verification::smt_verifier::z3_available()
}

#[cfg(feature = "z3")]
#[test]
fn verify_leaky_bucket_is_k_bounded() {
    if !z3_binary_available() {
        eprintln!("z3 binary not available — skipping verify_leaky_bucket_is_k_bounded");
        return;
    }

    // Property: with no slots tokens seeded, the synthetic harness_out_accept
    // place is unreachable, so the bound holds at 0 however much the
    // environment injects — [MOD-051]'s test derivation, and it is provable
    // (matches Java's verify_leakyBucket_isKBounded).
    let bucket = leaky_bucket(2);
    let supplier = token_supplier(|| Token::new(String::from("req")));

    // Built through the builder rather than a struct literal: the literal form
    // has to name every field, so it breaks whenever the harness gains one.
    let harness = VerificationHarness::<()>::new()
        .input(Arc::<str>::from("request"), supplier)
        .property(SmtProperty::place_bound("harness_out_accept", 0));

    let result = bucket.verify(harness);

    assert_eq!(result.per_property.len(), 1);
    let (_, verdict) = &result.per_property[0];
    assert!(
        verdict.is_proven(),
        "accept bound must be proven under AlwaysAvailable: {}",
        verdict.report
    );
}

// ============================================================
//  MOD-051 verification options, Arrivals(k), bind_actions.
// ============================================================

#[cfg(feature = "z3")]
mod options {
    use super::*;
    use libpetri::core::match_spec::MatchSpec;
    use libpetri::core::name::NameId;
    use libpetri::core::output::and;
    use libpetri::verification::environment::EnvironmentAnalysisMode;
    use libpetri::verification::harness::SubnetVerifyOptions;
    use libpetri::verification::name_fragment::FragmentMode;
    use libpetri::verification::result::{Verdict, VerificationResult, VerificationRoute};

    /// A subnet forwarding each token of input port `in` to output port `out`.
    fn forwarder() -> SubnetDef<()> {
        let input = Place::<String>::new("in");
        let out = Place::<String>::new("out");
        SubnetDef::<()>::builder("Forward")
            .transition(
                Transition::builder("forward")
                    .input(one(&input))
                    .output(out_place(&out))
                    .action(fork())
                    .build(),
            )
            .input_port("in", &input)
            .output_port("out", &out)
            .build()
    }

    fn harness(properties: Vec<SmtProperty>) -> VerificationHarness<()> {
        let mut h = VerificationHarness::<()>::new()
            .input(Arc::<str>::from("in"), token_supplier(|| Token::new(String::from("x"))));
        for p in properties {
            h = h.property(p);
        }
        h
    }

    fn only(result: &libpetri::verification::harness::SubnetVerificationResult) -> &VerificationResult {
        assert_eq!(result.per_property.len(), 1);
        &result.per_property[0].1
    }

    fn arrivals(k: usize) -> SubnetVerifyOptions {
        SubnetVerifyOptions::default()
            .with_environment_mode(EnvironmentAnalysisMode::Arrivals { max_tokens: k })
    }

    /// AC5: `Arrivals(k)` bounds the total a port receives.
    #[test]
    fn arrivals_bounds_what_a_port_receives() {
        let result = forwarder().verify_with_options(
            harness(vec![SmtProperty::place_bound("harness_out_out", 2)]),
            arrivals(2),
        );
        let r = only(&result);
        assert!(r.is_proven(), "{}", r.report);
        let result = forwarder().verify_with_options(
            harness(vec![SmtProperty::place_bound("harness_out_out", 1)]),
            arrivals(2),
        );
        assert!(only(&result).is_violated());
    }

    /// AC5 contrast: `Bounded(k)` refills the port forever.
    #[test]
    fn bounded_refills_a_port_forever() {
        if !z3_binary_available() {
            eprintln!("z3 binary not available — skipping bounded_refills_a_port_forever");
            return;
        }
        let result = forwarder().verify_with_options(
            harness(vec![SmtProperty::place_bound("harness_out_out", 2)]),
            SubnetVerifyOptions::default()
                .with_environment_mode(EnvironmentAnalysisMode::Bounded { max_tokens: 2 })
                .with_configure(|v, _| v.timeout(30_000)),
        );
        let r = only(&result);
        assert!(r.is_violated(), "{}", r.report);
    }

    /// AC6: the hook runs once per property, after the setup, with the synthetic
    /// net, and what it sets is visible in the result.
    #[test]
    fn configure_reaches_every_per_property_verifier() {
        use std::sync::Mutex;
        let seen: Arc<Mutex<Vec<String>>> = Arc::new(Mutex::new(Vec::new()));
        let log = Arc::clone(&seen);
        let result = forwarder().verify_with_options(
            harness(vec![
                SmtProperty::place_bound("harness_out_out", 2),
                SmtProperty::place_bound("harness_out_out", 3),
            ]),
            arrivals(2).with_configure(move |v, synth| {
                assert!(synth.places().iter().any(|p| p.name() == "harness_out_out"));
                log.lock().unwrap().push(synth.name().to_string());
                v.total_budget(0)
            }),
        );
        assert_eq!(*seen.lock().unwrap(), vec!["verify_Forward", "verify_Forward"]);
        for (_, r) in &result.per_property {
            assert_eq!(
                r.verdict,
                Verdict::Unknown {
                    reason: "total verification budget of 0 ms exhausted during net preparation"
                        .to_string()
                },
                "{}",
                r.report
            );
        }
    }

    /// AC6: a sink place named in the hook changes a quiescence verdict.
    #[test]
    fn a_sink_named_in_the_hook_changes_a_quiescence_verdict() {
        let stranded = forwarder()
            .verify_with_options(harness(vec![SmtProperty::DeadlockFree]), arrivals(1));
        assert!(only(&stranded).is_violated(), "{}", only(&stranded).report);
        let sunk = forwarder().verify_with_options(
            harness(vec![SmtProperty::DeadlockFree]),
            arrivals(1).with_configure(|v, _| v.sink_places(["harness_out_out".to_string()])),
        );
        assert!(only(&sunk).is_proven(), "{}", only(&sunk).report);
    }

    /// PNID Fig. 13(b) as a subnet (`research/net-metrics/validation/pnid/`):
    /// `a: R → P1, OR` mints a case, `b: P1 → B1, B2` relays it, and the joins
    /// `c: B1, OR → R` / `d: B2, OR → R` refund the input port `R`. In BASE the
    /// relay `b` reads as a fresh mint, so the joins never fire, `R` is never
    /// refunded, at most two cases run and `B2` stays within 2: a false `Proven`.
    /// With carrier `P1` in EXTENDED the joins refund `R`, every case strands a
    /// `B2` token, and `B2` passes 2.
    fn fig13b() -> SubnetDef<()> {
        let p = |n: &str| Place::<String>::new(n);
        let (r, p1, or, b1, b2) = (p("R"), p("P1"), p("OR"), p("B1"), p("B2"));
        let key = |q: &Place<String>| (q.clone(), |s: &String| NameId::new(s.clone()));
        let join = |name: &str, branch: &Place<String>| {
            let (k1, f1) = key(branch);
            let (k2, f2) = key(&or);
            Transition::builder(name)
                .input(one(branch))
                .input(one(&or))
                .match_spec(MatchSpec::builder().key(&k1, f1).key(&k2, f2).build())
                .output(out_place(&r))
                .action(fork())
                .build()
        };
        SubnetDef::<()>::builder("Fig13b")
            .transition(
                Transition::builder("a")
                    .input(one(&r))
                    .output(and(vec![out_place(&p1), out_place(&or)]))
                    .action(fork())
                    .build(),
            )
            .transition(
                Transition::builder("b")
                    .input(one(&p1))
                    .output(and(vec![out_place(&b1), out_place(&b2)]))
                    .action(fork())
                    .build(),
            )
            .transition(join("c", &b1))
            .transition(join("d", &b2))
            .input_port("R", &r)
            .build()
    }

    fn nu_harness() -> VerificationHarness<()> {
        VerificationHarness::<()>::new()
            .input(Arc::<str>::from("R"), token_supplier(|| Token::new(String::from("r"))))
            .property(SmtProperty::place_bound("sut/B2", 2))
    }

    /// AC7: without the ν options a ν subnet is verified in BASE, a different
    /// model; the options set through the hook reach the verifier and change it.
    #[test]
    fn nu_options_reach_the_per_property_verifier() {
        let base = fig13b().verify_with_options(nu_harness(), arrivals(2));
        let r = only(&base);
        assert!(r.is_proven(), "BASE reads the relay as a fresh mint\n{}", r.report);

        let extended = fig13b().verify_with_options(
            nu_harness(),
            arrivals(2).with_configure(|v, _| {
                v.fragment_mode(FragmentMode::Extended)
                    .carrier_places(["sut/P1".to_string()])
                    .nu_max_classes(2_000)
            }),
        );
        let r = only(&extended);
        assert!(r.is_violated(), "{}", r.report);
        assert_eq!(r.route, VerificationRoute::NuScg);
    }
}

/// AC8: `bind_actions` on a definition returns a new definition whose instances
/// carry the bound action, keyed by unprefixed names; the receiver's instances
/// keep theirs; ports and channels are unchanged.
#[test]
fn bind_actions_on_a_definition_returns_a_new_definition() {
    use libpetri::core::action::is_passthrough;
    use std::collections::HashMap;

    let input = Place::<String>::new("in");
    let out = Place::<String>::new("out");
    let work = Transition::builder("work")
        .input(one(&input))
        .output(out_place(&out))
        .build();
    let old = SubnetDef::<()>::builder("Bind")
        .transition(work.clone())
        .input_port("in", &input)
        .output_port("out", &out)
        .channel("go", &work)
        .build();
    let bound = old.bind_actions(&HashMap::from([("work".to_string(), fork())]));

    let action_of = |net: &libpetri::core::petri_net::PetriNet, name: &str| {
        net.transitions().iter().find(|t| t.name() == name).unwrap().action().clone()
    };
    assert!(!is_passthrough(&action_of(bound.instantiate_unit("n").renamed_body(), "n/work")));
    assert!(is_passthrough(&action_of(old.instantiate_unit("o").renamed_body(), "o/work")));
    assert!(is_passthrough(&action_of(old.body(), "work")), "the receiver is unchanged");
    let names = |d: &SubnetDef<()>| {
        let mut ports: Vec<String> = d.iface().ports().map(|p| p.name.to_string()).collect();
        ports.sort();
        ports
    };
    assert_eq!(names(&bound), names(&old));
    assert_eq!(bound.iface().port("out").unwrap().place.name(), "out");
    assert_eq!(bound.instantiate_unit("n").channel("go"), "n/work");

    // The resolver form keeps a transition the resolver defers.
    let resolved = old.bind_actions_with_resolver(|_| None);
    assert!(is_passthrough(&action_of(resolved.body(), "work")));
}

/// AC8: the CORE-043 check still applies to a definition bound or not.
#[test]
#[should_panic(expected = "declares an output spec but carries passthrough()")]
fn verify_still_rejects_a_passthrough_that_declares_outputs() {
    let input = Place::<String>::new("in");
    let out = Place::<String>::new("out");
    let def = SubnetDef::<()>::builder("Unbound")
        .transition(Transition::builder("work").input(one(&input)).output(out_place(&out)).build())
        .input_port("in", &input)
        .output_port("out", &out)
        .build()
        .bind_actions(&std::collections::HashMap::new());
    let harness = VerificationHarness::<()>::new()
        .input(Arc::<str>::from("in"), token_supplier(|| Token::new(String::from("x"))));
    def.verify(harness);
}
