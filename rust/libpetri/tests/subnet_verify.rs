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
        .build();
    let reject_t = Transition::builder("reject")
        .input(one(&request))
        .inhibitor(inhibitor(&slots))
        .output(out_place(&reject))
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

/// Probe whether the `z3` binary is on PATH. Mirrors Java's
/// `z3Available()` runtime guard.
#[cfg(feature = "z3")]
fn z3_binary_available() -> bool {
    std::process::Command::new("z3")
        .arg("-version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

#[cfg(feature = "z3")]
#[test]
fn verify_leaky_bucket_is_k_bounded() {
    if !z3_binary_available() {
        eprintln!("z3 binary not available — skipping verify_leaky_bucket_is_k_bounded");
        return;
    }

    // Property: with no slots tokens seeded, the synthetic
    // harness_out_accept place is unreachable (bound 0). The harness
    // doesn't seed initial markings; this checks well-formedness end to
    // end (matches Java's verify_leakyBucket_isKBounded).
    let bucket = leaky_bucket(2);
    let supplier = token_supplier(|| Token::new(String::from("req")));

    let harness = VerificationHarness::<()> {
        params: (),
        port_input_generators: std::collections::HashMap::from([(
            Arc::<str>::from("request"),
            supplier,
        )]),
        properties: vec![SmtProperty::place_bound("harness_out_accept", 0)],
    };

    let result = bucket.verify(harness);

    assert_eq!(result.per_property.len(), 1);
    let (_, verdict) = &result.per_property[0];
    assert!(
        !verdict.report.is_empty(),
        "verifier must produce a non-empty report"
    );
}
