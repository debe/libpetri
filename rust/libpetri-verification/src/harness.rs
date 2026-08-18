//! Local property verification harness for [`SubnetDef`] per
//! `spec/11-modular-composition.md` requirement **MOD-051**.
//!
//! This module wires a [`SubnetDef`] into a synthetic enclosing net suitable
//! for SMT analysis with the existing [`crate::smt_verifier::SmtVerifier`]:
//! - Each declared input (or in-out) port is bound to a synthetic
//!   environment place driven by a caller-supplied [`TokenSupplier`];
//! - Each declared output (or in-out) port is bound to a synthetic
//!   observation place that the caller can reference in an [`SmtProperty`].
//!
//! The harness invokes [`crate::smt_verifier::SmtVerifier`] once per
//! [`SmtProperty`] declared in [`VerificationHarness::properties`] and
//! aggregates the per-property verdicts into a [`SubnetVerificationResult`].
//!
//! # Crate boundary note
//!
//! In Java and TypeScript, `SubnetDef.verify(harness)` lives on the
//! `SubnetDef` class itself (same module). In Rust, the `libpetri-core`
//! crate cannot depend on `libpetri-verification` (which depends on it), so
//! the equivalent ergonomics live on the [`SubnetVerifyExt`] extension trait
//! defined here. Importing this trait lets callers write
//! `def.verify(harness)` exactly as in Java/TS.

use std::collections::HashMap;
use std::sync::Arc;

use libpetri_core::interface::PortDirection;
use libpetri_core::petri_net::{PetriNet, require_output_producing_actions};
use libpetri_core::place::{Place, PlaceRef};
use libpetri_core::subnet_def::SubnetDef;
use libpetri_core::token::{ErasedToken, Token};

use crate::property::SmtProperty;
use crate::result::VerificationResult as SmtVerificationResult;
#[cfg(feature = "z3")]
use crate::smt_verifier::SmtVerifier;

/// Token-source supplier used by the verification harness to seed a synthetic
/// environment place for a given input port, per **MOD-051** AC #3.
///
/// The supplier's presence is what bounds the input behavior in the synthetic
/// harness; it is invoked once at synthetic-net construction time so that
/// supplier-side errors surface eagerly, not at verification time. The
/// concrete token value is not consumed by the verifier itself (which operates
/// on the integer marking projection per [VER-004]); it merely materialises
/// the seed token type and surfaces user errors.
pub type TokenSupplier = Arc<dyn Fn() -> ErasedToken + Send + Sync>;

/// Helper: wrap a typed `Fn() -> Token<T>` into a [`TokenSupplier`].
pub fn token_supplier<T, F>(f: F) -> TokenSupplier
where
    T: Send + Sync + 'static,
    F: Fn() -> Token<T> + Send + Sync + 'static,
{
    Arc::new(move || ErasedToken::from_typed(&f()))
}

/// Harness driving local property verification of a [`SubnetDef`] per
/// **MOD-051**.
///
/// The harness is a value carrier consumed by
/// [`SubnetVerifyExt::verify`]. It supplies the three pieces of information
/// needed to wrap a subnet in a synthetic enclosing net for verification:
///
/// 1. A `params` value of the subnet's parameter type.
/// 2. A `port_input_generators` map from **input port name** (original /
///    pre-prefix) to a [`TokenSupplier`]. The supplier is invoked at
///    synthetic-net construction time when the harness wires up the
///    [`libpetri_core::place::EnvironmentPlace`] associated with the port.
/// 3. A list of `properties` to check (per [VER-002] / [`SmtProperty`]).
///
/// Each entry in `port_input_generators` MUST correspond to an input or
/// in-out port declared on the subnet's interface. Output-only ports never
/// appear in the generator map; instead, the harness wires them to a
/// synthetic observation place visible to the verifier.
pub struct VerificationHarness<P = ()> {
    /// Parameter value supplied to
    /// [`SubnetDef::instantiate`](libpetri_core::subnet_def::SubnetDef::instantiate)
    /// for the system-under-test instance.
    pub params: P,
    /// Map from input-port name to a [`TokenSupplier`] that seeds the
    /// synthetic environment place for that port. Output-only ports MUST NOT
    /// appear; in-out ports MUST appear (mirrors Java/TS).
    pub port_input_generators: HashMap<Arc<str>, TokenSupplier>,
    /// Safety properties to check on the synthetic enclosing net per
    /// [`SmtProperty`]. An empty list is permitted but yields an empty
    /// [`SubnetVerificationResult::per_property`].
    pub properties: Vec<SmtProperty>,
}

impl<P> VerificationHarness<P> {
    /// Convenience constructor for a harness with no input generators and
    /// no properties (useful for pure synthetic-net construction tests).
    pub fn with_params(params: P) -> Self {
        Self {
            params,
            port_input_generators: HashMap::new(),
            properties: Vec::new(),
        }
    }

    /// Register a token supplier for an input or in-out port.
    pub fn input(
        mut self,
        port_name: impl Into<Arc<str>>,
        supplier: TokenSupplier,
    ) -> Self {
        self.port_input_generators.insert(port_name.into(), supplier);
        self
    }

    /// Register an [`SmtProperty`] to check.
    pub fn property(mut self, property: SmtProperty) -> Self {
        self.properties.push(property);
        self
    }
}

impl Default for VerificationHarness<()> {
    fn default() -> Self {
        Self::with_params(())
    }
}

impl VerificationHarness<()> {
    /// Convenience constructor for unparameterised harnesses (`P = ()`).
    pub fn new() -> Self {
        Self::default()
    }
}

/// Aggregated outcome of [`SubnetVerifyExt::verify`] per **MOD-051**.
///
/// The verifier is invoked once per [`SmtProperty`] declared in the harness;
/// each invocation produces an [`SmtVerificationResult`]. This struct carries
/// the per-property results plus the synthetic enclosing net that was
/// constructed for verification (useful for diagnostic output and tooling
/// to render the harness wiring).
///
/// # Naming note
///
/// This type is named `SubnetVerificationResult` (not `VerificationResult`)
/// to avoid colliding with the existing [`crate::result::VerificationResult`]
/// that represents a *per-property* SMT verification verdict. The Java
/// counterpart `org.libpetri.verification.VerificationResult` plays the
/// aggregator role; the Rust crate already used `VerificationResult` for the
/// per-property verdict, so we rename the aggregator here for clarity.
pub struct SubnetVerificationResult {
    /// The synthetic enclosing net assembled by [`SubnetVerifyExt::verify`]:
    /// the renamed body of the subnet under test, with each input port
    /// bound to a synthetic environment place and each output port bound
    /// to a synthetic observation place.
    pub synthetic_net: PetriNet,
    /// Per-property verification results, in the iteration order of the
    /// harness's `properties` list. Stored as a `Vec` of pairs (rather than a
    /// `HashMap`) so iteration order matches the harness exactly (matches
    /// Java/TS semantics) and to avoid requiring `Hash`/`Eq` on
    /// [`SmtProperty`].
    pub per_property: Vec<(SmtProperty, SmtVerificationResult)>,
}

impl SubnetVerificationResult {
    /// Returns true when every property in the harness was proven safe.
    /// An empty harness (no properties) returns `true` vacuously.
    pub fn all_proven(&self) -> bool {
        self.per_property.iter().all(|(_, r)| r.is_proven())
    }

    /// Returns true when at least one property was violated.
    pub fn any_violated(&self) -> bool {
        self.per_property.iter().any(|(_, r)| r.is_violated())
    }
}

/// Extension trait providing [`SubnetVerifyExt::verify`] on
/// [`SubnetDef<P>`], mirroring the Java `SubnetDef.verify(harness)` /
/// TypeScript `subnetDef.verify(harness)` ergonomics.
///
/// Importing this trait lets callers write `def.verify(harness)` directly.
pub trait SubnetVerifyExt<P: 'static> {
    /// Verifies safety properties of this subnet **in isolation** per
    /// **MOD-051**, by wrapping it in a synthetic enclosing net where each
    /// input port is fed by an
    /// [`EnvironmentPlace`](libpetri_core::place::EnvironmentPlace) and each
    /// output port is observed via a synthetic place.
    ///
    /// # Panics
    /// - Panics if any input or in-out port is missing a supplier in
    ///   `harness.port_input_generators`.
    fn verify(&self, harness: VerificationHarness<P>) -> SubnetVerificationResult;
}

impl<P: 'static> SubnetVerifyExt<P> for SubnetDef<P> {
    fn verify(&self, harness: VerificationHarness<P>) -> SubnetVerificationResult {
        verify_subnet(self, harness)
    }
}

/// Free-function form of [`SubnetVerifyExt::verify`]; the trait method
/// delegates here.
pub fn verify_subnet<P: 'static>(
    def: &SubnetDef<P>,
    harness: VerificationHarness<P>,
) -> SubnetVerificationResult {
    let VerificationHarness {
        params,
        port_input_generators: generators,
        properties,
    } = harness;

    // Step 1: instantiate the SubnetDef under the "sut" prefix
    // (system-under-test).
    let sut = def.instantiate("sut", params);

    // Step 2: allocate a synthetic harness place per port. Track the
    // environment-place names (one per input/inout port) so the SmtVerifier
    // can treat them as boundary places rather than ordinary internals.
    let mut env_place_names: Vec<String> = Vec::new();
    let mut port_mappings: HashMap<Arc<str>, PlaceRef> = HashMap::new();

    for port in def.iface().ports() {
        let port_name = &port.name;
        match port.direction {
            PortDirection::Input => {
                let supplier = generators.get(port_name).unwrap_or_else(|| {
                    panic!(
                        "verify: harness is missing an input generator for port '{}' \
                         on subnet '{}' (MOD-051)",
                        port_name,
                        def.name(),
                    )
                });
                // Touch the supplier to surface user errors at construction
                // time rather than at verification time. The returned token
                // is discarded — it serves only to materialise the seed type
                // (matches Java/TS).
                let _seed: ErasedToken = supplier();

                let synth_name: Arc<str> =
                    Arc::from(format!("harness_in_{}", port_name).as_str());
                let synth_ref = synthetic_place_ref(synth_name.clone());
                env_place_names.push(synth_name.to_string());
                port_mappings.insert(Arc::clone(port_name), synth_ref);
            }
            PortDirection::Output => {
                let synth_name: Arc<str> =
                    Arc::from(format!("harness_out_{}", port_name).as_str());
                let synth_ref = synthetic_place_ref(synth_name);
                port_mappings.insert(Arc::clone(port_name), synth_ref);
            }
            PortDirection::InOut => {
                let supplier = generators.get(port_name).unwrap_or_else(|| {
                    panic!(
                        "verify: harness is missing an input generator for in-out port '{}' \
                         on subnet '{}' (MOD-051)",
                        port_name,
                        def.name(),
                    )
                });
                let _seed: ErasedToken = supplier();

                let synth_name: Arc<str> =
                    Arc::from(format!("harness_io_{}", port_name).as_str());
                let synth_ref = synthetic_place_ref(synth_name.clone());
                env_place_names.push(synth_name.to_string());
                port_mappings.insert(Arc::clone(port_name), synth_ref);
            }
        }
    }

    // Step 3: build the synthetic enclosing net. The "verify_" prefix uses
    // an underscore (not "/") so the enclosing-net name does not collide
    // with the prefix separator reserved by [MOD-010] (matches Java/TS).
    let synthetic_net = PetriNet::builder(format!("verify_{}", def.name()))
        .compose(&sut, port_mappings)
        .build();

    // CORE-043: reject here too (not only under the `z3` feature), so a green harness
    // result always implies a subnet that can actually run.
    require_output_producing_actions(&synthetic_net);

    // Step 4: invoke the SmtVerifier once per property and aggregate
    // results. Iteration order matches the harness's property collection
    // for deterministic per-property reporting.
    let per_property = run_per_property(&synthetic_net, &properties, &env_place_names);

    SubnetVerificationResult {
        synthetic_net,
        per_property,
    }
}

/// Dispatch per-property verification. With the `z3` feature enabled we
/// invoke the real [`SmtVerifier`] once per property; without it we surface
/// an `Unknown` verdict per property so callers can still consume the
/// well-shaped [`SubnetVerificationResult`].
#[cfg(feature = "z3")]
fn run_per_property(
    synthetic_net: &PetriNet,
    properties: &[SmtProperty],
    env_place_names: &[String],
) -> Vec<(SmtProperty, SmtVerificationResult)> {
    let mut per_property = Vec::with_capacity(properties.len());
    for property in properties {
        let result = SmtVerifier::for_net(synthetic_net)
            .property(property.clone())
            .environment_places(env_place_names.iter().cloned())
            .verify();
        per_property.push((property.clone(), result));
    }
    per_property
}

#[cfg(not(feature = "z3"))]
fn run_per_property(
    _synthetic_net: &PetriNet,
    properties: &[SmtProperty],
    _env_place_names: &[String],
) -> Vec<(SmtProperty, SmtVerificationResult)> {
    use crate::result::{Verdict, VerificationStatistics};

    properties
        .iter()
        .map(|property| {
            let result = SmtVerificationResult {
                verdict: Verdict::Unknown {
                    reason: "z3 feature not enabled".into(),
                },
                report: format!(
                    "verify (subnet harness): SMT verification disabled — \
                     enable the `z3` feature on libpetri-verification to run \
                     property '{}'",
                    property.description()
                ),
                invariants: Vec::new(),
                discovered_invariants: Vec::new(),
                counterexample_trace: Vec::new(),
                counterexample_confirmed: false,
                counterexample_transitions: Vec::new(),
                elapsed_ms: 0,
                statistics: VerificationStatistics {
                    places: 0,
                    transitions: 0,
                    invariants_found: 0,
                    structural_result: "skipped (no z3 feature)".into(),
                },
            };
            (property.clone(), result)
        })
        .collect()
}

/// Allocate a fresh synthetic place reference. The harness wires only the
/// `PlaceRef` (type-erased) into the host net's compose mapping; the
/// underlying type carried by the original port place is preserved through
/// the rewriter (per [MOD-010]).
fn synthetic_place_ref(name: Arc<str>) -> PlaceRef {
    // Use Place::<()>::new as a uniform constructor — the type parameter is
    // irrelevant once we obtain the type-erased PlaceRef. (We could also
    // construct PlaceRef directly via PlaceRef::new(name), but routing
    // through Place keeps the construction path identical to user code.)
    let place: Place<DummyToken> = Place::new(name);
    place.as_ref()
}

/// Sentinel marker type used solely to satisfy the `Place<T>` constructor in
/// [`synthetic_place_ref`]. Never instantiated; the place's type-erased
/// reference is what flows into the host net.
struct DummyToken;

#[cfg(test)]
mod tests {
    use super::*;
    use libpetri_core::action::fork;
    use libpetri_core::input::one;
    use libpetri_core::output::out_place;
    use libpetri_core::place::Place;
    use libpetri_core::subnet_def::SubnetDef;
    use libpetri_core::token::Token;
    use libpetri_core::transition::Transition;

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
            .inhibitor(libpetri_core::arc::inhibitor(&slots))
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
    #[should_panic(expected = "request")]
    fn verify_missing_input_generator_panics() {
        // leaky_bucket has Input port "request" — supplying an empty harness
        // must panic, naming the missing input port.
        let bucket = leaky_bucket(2);
        let _ = bucket.verify(VerificationHarness::<()>::new());
    }

    #[test]
    fn verify_output_port_only_does_not_require_generator() {
        // producer fixture: only an Output port "output". Empty harness
        // must succeed structurally (synthetic net built, zero properties).
        let p = producer();
        let result = p.verify(VerificationHarness::<()>::new());

        assert!(result.per_property.is_empty(),
            "no properties = empty per-property results");
        assert!(result.all_proven(),
            "vacuously true when no properties are checked");
        assert!(result.synthetic_net.name().starts_with("verify_"),
            "synthetic net name should be 'verify_<def_name>'");
    }

    #[test]
    fn verify_synthetic_net_binds_all_ports() {
        // leaky_bucket: 1 input + 2 output ports. The synthetic enclosing
        // net must contain a synthetic place per port (3 total) plus the
        // subnet's internal places.
        let bucket = leaky_bucket(2);
        let supplier = token_supplier(|| Token::new(String::from("req")));

        let harness = VerificationHarness::<()>::new()
            .input("request", supplier);

        let result = bucket.verify(harness);

        let names: std::collections::HashSet<&str> = result
            .synthetic_net
            .places()
            .iter()
            .map(|p| p.name())
            .collect();

        assert!(names.contains("harness_in_request"),
            "synthetic net must contain the input-port harness place; got: {names:?}");
        assert!(names.contains("harness_out_accept"),
            "synthetic net must contain the accept-output harness place; got: {names:?}");
        assert!(names.contains("harness_out_reject"),
            "synthetic net must contain the reject-output harness place; got: {names:?}");

        // The renamed instance-side port places must be gone (compose
        // substitution rewrote them to the harness places).
        assert!(!names.contains("sut/request"),
            "sut/request should be substituted away");
        assert!(!names.contains("sut/accept"),
            "sut/accept should be substituted away");
        assert!(!names.contains("sut/reject"),
            "sut/reject should be substituted away");
        // Internal place flows through with the prefix.
        assert!(names.contains("sut/slots"),
            "internal sut/slots must remain in the synthetic net");
    }

    #[test]
    fn verify_input_generator_invoked_at_construction() {
        // Per the harness contract: the supplier is touched once at
        // synthetic-net build time so user errors surface early. Confirm
        // the supplier is called at least once when verify() runs.
        let consumer = consumer();
        let count = Arc::new(std::sync::atomic::AtomicUsize::new(0));
        let count_clone = Arc::clone(&count);
        let tracker: TokenSupplier = Arc::new(move || {
            count_clone.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
            ErasedToken::from_typed(&Token::new(String::from("tracked")))
        });

        let harness = VerificationHarness::<()>::new()
            .input("input", tracker);

        consumer.verify(harness);

        assert!(
            count.load(std::sync::atomic::Ordering::SeqCst) >= 1,
            "input generator must be invoked during harness construction"
        );
    }

    #[test]
    fn verify_returns_result_with_all_properties() {
        // Two properties on the consumer fixture. Independent of Z3
        // availability, the harness must invoke the verifier once per
        // property and surface both outcomes in the result vector.
        let consumer = consumer();
        let supplier = token_supplier(|| Token::new(String::from("hello")));

        let props = vec![
            SmtProperty::deadlock_free(),
            SmtProperty::place_bound("harness_in_input", 1),
        ];
        let harness = VerificationHarness::<()> {
            params: (),
            port_input_generators: HashMap::from([
                (Arc::<str>::from("input"), supplier),
            ]),
            properties: props.clone(),
        };

        let result = consumer.verify(harness);

        assert_eq!(result.per_property.len(), props.len(),
            "result must have exactly one entry per harness property");
        // Iteration order preserved.
        for (i, (got, _)) in result.per_property.iter().enumerate() {
            assert_eq!(
                std::mem::discriminant(got),
                std::mem::discriminant(&props[i]),
                "per-property entry order must match harness order"
            );
        }
    }

    #[test]
    fn harness_builder_inserts_generators_and_properties() {
        let supplier = token_supplier(|| Token::new(42i32));
        let h = VerificationHarness::<()>::new()
            .input("p1", supplier)
            .property(SmtProperty::deadlock_free());

        assert_eq!(h.port_input_generators.len(), 1);
        assert!(h.port_input_generators.contains_key(&Arc::<str>::from("p1")));
        assert_eq!(h.properties.len(), 1);
    }

    // ============================================================
    //  End-to-end SMT verification (gated on z3 feature + binary).
    // ============================================================

    /// Probe whether the `z3` binary is on PATH. Mirrors Java's
    /// `z3Available()` runtime guard.
    #[allow(dead_code)]
    fn z3_binary_available() -> bool {
        std::process::Command::new("z3")
            .arg("-version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
    }

    #[cfg(feature = "z3")]
    #[test]
    fn verify_leaky_bucket_returns_well_formed_result() {
        if !z3_binary_available() {
            // No Z3 binary in the sandbox — match Java's @EnabledIf skip.
            return;
        }

        let bucket = leaky_bucket(2);
        let supplier = token_supplier(|| Token::new(String::from("req")));

        // PlaceBound on the synthetic accept place (no slots are seeded so
        // accept is unreachable; the bound holds at 0).
        let harness = VerificationHarness::<()> {
            params: (),
            port_input_generators: HashMap::from([
                (Arc::<str>::from("request"), supplier),
            ]),
            properties: vec![SmtProperty::place_bound("harness_out_accept", 0)],
        };

        let result = bucket.verify(harness);

        assert_eq!(result.per_property.len(), 1,
            "result must have one entry per harness property");
        let (_, verdict) = &result.per_property[0];
        // We do not assert isProven specifically because the outcome
        // depends on environment-analysis mode; the structural assertion
        // is that the verifier ran and produced a non-empty report
        // (matches Java's SubnetVerifyTest.verify_leakyBucket_isKBounded).
        assert!(!verdict.report.is_empty(),
            "verifier must produce a non-empty report");
    }
}
