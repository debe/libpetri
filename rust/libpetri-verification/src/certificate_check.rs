//! Independent certificate check for IC3/PDR proofs.
//!
//! When Z3 Spacer answers `sat` on the CHC encoding ([`crate::smt_encoder`]),
//! the model it produces interprets `Reachable` as an inductive invariant —
//! the proof certificate. This module re-verifies that certificate with plain
//! (non-HORN) SMT queries in a SECOND z3 run, so a `Proven` verdict no longer
//! rests on the empirical HORN sat ⇒ proven mapping alone, nor on the
//! correctness of the P-invariant strengthening: the three verification
//! conditions below are discharged against the UNSTRENGTHENED step relation
//! ([`crate::smt_encoder::encode_step_relation_smt2`]), independent of the
//! exact pre-encoding P-invariant validation.
//!
//! The candidate invariant is `R' := R ∧ Inv`, where `R` is the pasted
//! `Reachable` interpretation and `Inv` the exactly-validated P-invariant
//! equalities the CHC encoding strengthened its rule bodies with: a Spacer
//! model is only guaranteed inductive *relative to* that strengthening, so
//! the conjuncts must ride along in the candidate — but the RELATION stays
//! unstrengthened, which means VC1/VC2 below re-prove each conjunct's
//! initiation and inductiveness from scratch. A wrong P-invariant therefore
//! cannot weaken this check: it fails init or consecution instead. With `T`
//! the step relation and `Bad` the property-violation condition, the VCs —
//! each expected `unsat` — are:
//!
//! 1. **init**: `¬R'(M₀)` — the initial marking is in the invariant;
//! 2. **consecution**: `R'(M) ∧ T(M, M') ∧ ¬R'(M')` — the invariant is closed
//!    under every transition firing and env-injection step;
//! 3. **safety**: `R'(M) ∧ Bad(M)` — the invariant excludes every violating
//!    state.
//!
//! VC2 and VC3 additionally assert `M >= 0`: the encoded system lives in
//! `ℕ^P`, and without that domain constraint the queries range over `ℤ^P`,
//! where a certificate that is genuinely inductive and safe over the markings
//! the net can hold still fails.
//!
//! Polarity cross-check: these are ordinary satisfiability queries with the
//! standard, unambiguous reading (`unsat` = the VC is valid). That a
//! Spacer-produced certificate discharges them independently corroborates the
//! HORN convention the verifier relies on (`sat` ⇒ PROVEN, see
//! [`crate::smt_encoder::encode`]'s query comment).

use crate::marking_state::MarkingState;
use crate::net_flattener::FlatNet;
use crate::p_invariant::PInvariant;
use crate::property::SmtProperty;
use crate::smt_encoder;
use crate::z3_process::{self, Z3Exit, Z3Solver};

/// The three verification conditions, in script order. These labels are quoted
/// verbatim in the verifier's downgrade reason, so all four language
/// implementations name a failing VC identically.
const VC_LABELS: [&str; 3] = ["initiation (VC1)", "consecution (VC2)", "safety (VC3)"];

/// Outcome of the certificate check.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CertificateCheck {
    /// All three VCs discharged (z3 answered `unsat` to each).
    Passed,
    /// One VC came back with something other than `unsat`: the certificate is
    /// not an inductive invariant of the unstrengthened step relation. `vc` is
    /// one of [`VC_LABELS`], `detail` describes the solver's answer.
    Failed {
        /// The failing VC, verbatim from [`VC_LABELS`].
        vc: &'static str,
        /// What the solver answered, e.g.
        /// `solver returned SATISFIABLE (witness: p0=2, p1=1)`.
        detail: String,
    },
    /// The check could not be run to a verdict — a malformed certificate, a
    /// z3 spawn/parse failure, an errored assert. Distinct from `Failed`: it
    /// is an absence of evidence, and the verifier says so.
    Inconclusive {
        /// Why the check could not run.
        reason: String,
    },
}

/// Re-verifies an extracted proof certificate against the unstrengthened step
/// relation. `certificate` is the `(define-fun …)` block extracted verbatim
/// from the Spacer model (auxiliary definitions included, so `Reachable`
/// stays resolvable); `invariants` are the validated P-invariants the CHC
/// encoding was strengthened with — conjoined into the candidate and thereby
/// re-proven by the VCs themselves (see the module docs). Never panics: a
/// malformed net/invariant shape, a missing `Reachable`, a z3 error, an
/// unparseable reply all come back as [`CertificateCheck::Inconclusive`], and
/// a sat/unknown VC as [`CertificateCheck::Failed`].
#[allow(clippy::too_many_arguments)]
pub fn check_certificate(
    certificate: &str,
    flat: &FlatNet,
    initial_marking: &MarkingState,
    property: &SmtProperty,
    invariants: &[PInvariant],
    sink_places: &[String],
    env_bounds: &[(String, usize)],
    env_injection: &[(String, Option<usize>)],
    timeout_ms: u64,
) -> CertificateCheck {
    match Z3Solver::resolve() {
        Ok(solver) => check_certificate_with(
            certificate,
            flat,
            initial_marking,
            property,
            invariants,
            sink_places,
            env_bounds,
            env_injection,
            timeout_ms,
            &solver,
        ),
        Err(reason) => CertificateCheck::Inconclusive { reason },
    }
}

/// The certificate-check script for the given inputs, exactly as
/// [`check_certificate`] sends it ([VER-013] script parity): what the
/// cross-language golden tests diff.
#[allow(clippy::too_many_arguments)]
pub fn vc_script(
    certificate: &str,
    flat: &FlatNet,
    initial_marking: &MarkingState,
    property: &SmtProperty,
    invariants: &[PInvariant],
    sink_places: &[String],
    env_bounds: &[(String, usize)],
    env_injection: &[(String, Option<usize>)],
) -> String {
    VerificationConditions::build(
        certificate,
        flat,
        initial_marking,
        property,
        invariants,
        sink_places,
        env_bounds,
        env_injection,
    )
    .script()
}

/// [`check_certificate`] against an already-resolved solver: what the
/// verifier calls, so one `verify()` probes the executable once.
#[allow(clippy::too_many_arguments)]
pub(crate) fn check_certificate_with(
    certificate: &str,
    flat: &FlatNet,
    initial_marking: &MarkingState,
    property: &SmtProperty,
    invariants: &[PInvariant],
    sink_places: &[String],
    env_bounds: &[(String, usize)],
    env_injection: &[(String, Option<usize>)],
    timeout_ms: u64,
    solver: &Z3Solver,
) -> CertificateCheck {
    // Shape guards for the public entry point: the script builder indexes
    // `flat.places[i]`, `inv.weights[i]` and the marking-variable vectors by
    // place index, so a caller-supplied net or invariant that does not line up
    // must be refused, not panicked on.
    if let Some(reason) = shape_failure(flat, invariants) {
        return CertificateCheck::Inconclusive { reason };
    }
    if !certificate.contains("(define-fun Reachable ")
        && !certificate.contains("(define-fun |Reachable| ")
    {
        return CertificateCheck::Inconclusive {
            reason: "certificate does not define Reachable".to_string(),
        };
    }

    let vcs = VerificationConditions::build(
        certificate,
        flat,
        initial_marking,
        property,
        invariants,
        sink_places,
        env_bounds,
        env_injection,
    );

    // One plain z3 run for all three VCs (no fp.engine — this is not HORN).
    let results = match run_vc_script(&vcs.script(), timeout_ms, solver) {
        Ok(results) => results,
        Err(reason) => return CertificateCheck::Inconclusive { reason },
    };

    for (i, result) in results.iter().enumerate() {
        if result != "unsat" {
            return CertificateCheck::Failed {
                vc: VC_LABELS[i],
                detail: vcs.detail_for(i, result, flat, timeout_ms, solver),
            };
        }
    }
    CertificateCheck::Passed
}

/// Why `flat`/`invariants` cannot be indexed safely, or `None` when they line up.
fn shape_failure(flat: &FlatNet, invariants: &[PInvariant]) -> Option<String> {
    if flat.places.len() != flat.place_count {
        return Some(format!(
            "flat net declares {} places but carries {} names",
            flat.place_count,
            flat.places.len()
        ));
    }
    for inv in invariants {
        if inv.weights.len() != flat.place_count {
            return Some(format!(
                "P-invariant has {} weights for a {}-place net",
                inv.weights.len(),
                flat.place_count
            ));
        }
        if let Some(&pid) = inv.support.iter().find(|&&pid| pid >= flat.place_count) {
            return Some(format!(
                "P-invariant support names place index {pid} in a {}-place net",
                flat.place_count
            ));
        }
    }
    None
}

/// Runs one plain-SMT script and returns the three positional `(check-sat)`
/// answers, or the reason the run could not be trusted.
///
/// Both z3 output channels are inspected: an `(error …)` on EITHER stream
/// means an assert was dropped, which would silently make a VC vacuous; a
/// `timeout` line, a watchdog kill and a non-success exit mean the run did not
/// complete. Only a clean three-answer stdout counts.
fn run_vc_script(
    script: &str,
    timeout_ms: u64,
    solver: &Z3Solver,
) -> Result<Vec<String>, String> {
    let reply = solver.run(script, "certificate", timeout_ms, &[])?;
    if let Some(err) = z3_process::error_line(&reply.stderr) {
        return Err(format!("z3 reported an error on stderr: {err}"));
    }
    if z3_process::timeout_line(&reply.stdout) {
        return Err(format!(
            "z3 hard timeout after {}s while checking the certificate",
            z3_process::hard_timeout_secs(timeout_ms)
        ));
    }
    if reply.exit == Z3Exit::Killed {
        return Err(format!(
            "z3 did not exit within {} ms while checking the certificate and was killed",
            z3_process::watchdog_ms(timeout_ms)
        ));
    }
    let results = parse_vc_results(&reply.stdout)?;
    if !reply.success() {
        let status = match reply.exit {
            Z3Exit::Exited(Some(code)) => format!("exit status: {code}"),
            Z3Exit::Exited(None) => "a signal".to_string(),
            Z3Exit::Killed => "the watchdog kill".to_string(),
        };
        return Err(format!(
            "z3 exited with {status} after answering {results:?}"
        ));
    }
    Ok(results)
}

/// The assembled VC script, kept in parts so one VC can be re-run alone to
/// describe its failure (the model witness / the unknown reason).
struct VerificationConditions {
    prelude: Vec<String>,
    /// The asserts of each VC, in [`VC_LABELS`] order.
    asserts: [Vec<String>; 3],
}

impl VerificationConditions {
    #[allow(clippy::too_many_arguments)]
    fn build(
        certificate: &str,
        flat: &FlatNet,
        initial_marking: &MarkingState,
        property: &SmtProperty,
        invariants: &[PInvariant],
        sink_places: &[String],
        env_bounds: &[(String, usize)],
        env_injection: &[(String, Option<usize>)],
    ) -> Self {
        let p = flat.place_count;
        let m_vars: Vec<String> = (0..p).map(|i| format!("m{i}")).collect();
        let mp_vars: Vec<String> = (0..p).map(|i| format!("m{i}p")).collect();

        let mut prelude = vec![
            "; IC3/PDR certificate check (plain SMT-LIB2, not HORN):".to_string(),
            "; each VC below must be unsat for the certificate to stand.".to_string(),
            certificate.to_string(),
            String::new(),
        ];
        for v in m_vars.iter().chain(mp_vars.iter()) {
            prelude.push(format!("(declare-const {v} Int)"));
        }

        // VC1 (init): the initial marking satisfies the candidate invariant.
        let m0_values: Vec<String> = (0..p)
            .map(|i| initial_marking.count(&flat.places[i]).to_string())
            .collect();
        let vc1 = vec![format!("(assert (not {}))", candidate(&m0_values, invariants))];

        // The system lives in ℕ^P, not ℤ^P: without this the VCs run over
        // negative markings the net can never hold, and a certificate that is
        // inductive/safe over ℕ^P alone fails consecution or safety — a
        // correct `Proven` lost to a state the encoding excludes anyway. The
        // step relation already constrains M' (`m'_i >= 0`); this constrains M.
        let non_negative: Vec<String> = m_vars
            .iter()
            .map(|v| format!("(assert (>= {v} 0))"))
            .collect();

        // VC2 (consecution): the invariant is closed under the unstrengthened
        // step relation (transition firings + env-injection steps, no
        // P-invariant conjuncts).
        let step = smt_encoder::encode_step_relation_smt2(flat, env_bounds, env_injection);
        let mut vc2 = non_negative.clone();
        vc2.push(format!("(assert {})", candidate(&m_vars, invariants)));
        vc2.push(format!("(assert {step})"));
        vc2.push(format!("(assert (not {}))", candidate(&mp_vars, invariants)));

        // VC3 (safety): the invariant excludes every property-violating state —
        // exactly the violation the CHC error rule encodes.
        let env_inject = smt_encoder::resolve_env_injection(flat, env_injection);
        let bad = smt_encoder::encode_property_violation(
            flat,
            property,
            &m_vars,
            sink_places,
            &env_inject,
        );
        let mut vc3 = non_negative;
        vc3.push(format!("(assert {})", candidate(&m_vars, invariants)));
        vc3.push(format!("(assert {bad})"));

        Self {
            prelude,
            asserts: [vc1, vc2, vc3],
        }
    }

    /// The full script: the prelude, then the three VCs under `(push)`/`(pop)`,
    /// each with its own `(check-sat)`.
    fn script(&self) -> String {
        let mut lines = self.prelude.clone();
        for (i, asserts) in self.asserts.iter().enumerate() {
            lines.push(String::new());
            lines.push(format!("; VC{} {}", i + 1, VC_LABELS[i]));
            lines.push("(push)".to_string());
            lines.extend(asserts.iter().cloned());
            lines.push("(check-sat)".to_string());
            lines.push("(pop)".to_string());
        }
        lines.join("\n")
    }

    /// Describes VC `i`'s non-`unsat` answer for the downgrade reason, by
    /// re-running that VC alone with model/reason extraction enabled. The
    /// re-run is best effort: without it the answer is still named.
    fn detail_for(
        &self,
        i: usize,
        answer: &str,
        flat: &FlatNet,
        timeout_ms: u64,
        solver: &Z3Solver,
    ) -> String {
        let mut lines = vec!["(set-option :produce-models true)".to_string()];
        lines.extend(self.prelude.iter().cloned());
        lines.extend(self.asserts[i].iter().cloned());
        lines.push("(check-sat)".to_string());
        lines.push(
            if answer == "sat" { "(get-model)" } else { "(get-info :reason-unknown)" }.to_string(),
        );
        let reply = solver
            .run(&lines.join("\n"), "certificate-detail", timeout_ms, &[])
            .map(|reply| reply.stdout)
            .unwrap_or_default();

        if answer == "sat" {
            match witness(&reply, flat) {
                Some(w) => format!("solver returned SATISFIABLE (witness: {w})"),
                None => "solver returned SATISFIABLE".to_string(),
            }
        } else {
            match reason_unknown(&reply) {
                Some(r) => format!("solver returned UNKNOWN ({r})"),
                None => "solver returned UNKNOWN".to_string(),
            }
        }
    }
}

/// Reads the current-marking assignment out of a `(get-model)` reply as
/// `p0=2, p1=1` (place names, index order). `None` when no `m_i` was defined.
fn witness(model: &str, flat: &FlatNet) -> Option<String> {
    let parts: Vec<String> = (0..flat.place_count)
        .filter_map(|i| {
            let needle = format!("(define-fun m{i} () Int");
            let start = model.find(&needle)? + needle.len();
            let rest = model[start..].trim_start();
            // A negative literal prints as the s-expression `(- 1)`; flatten it
            // back to `-1` so the witness reads like a marking.
            let value = if rest.starts_with('(') {
                let end = crate::smt_verifier::sexpr_end(rest, 0)?;
                rest[1..end - 1].split_whitespace().collect::<Vec<_>>().concat()
            } else {
                rest.split(|c: char| c.is_whitespace() || c == ')')
                    .next()?
                    .to_string()
            };
            Some(format!("{}={}", flat.places[i], value))
        })
        .collect();
    (!parts.is_empty()).then(|| parts.join(", "))
}

/// Reads z3's `(get-info :reason-unknown)` reply, e.g. `timeout`.
fn reason_unknown(reply: &str) -> Option<String> {
    let start = reply.find(":reason-unknown")? + ":reason-unknown".len();
    let rest = reply[start..].trim_start();
    let end = rest.find(')')?;
    let reason = rest[..end].trim().trim_matches('"').trim();
    (!reason.is_empty()).then(|| reason.to_string())
}

/// The candidate invariant applied to a variable (or literal) vector:
/// `R'(vars) = (Reachable vars) ∧ Inv(vars)`. With no P-invariants this is
/// the bare `Reachable` application.
fn candidate(vars: &[String], invariants: &[PInvariant]) -> String {
    let mut conjuncts = vec![format!("(Reachable {})", vars.join(" "))];
    conjuncts.extend(smt_encoder::invariant_conditions(invariants, vars));
    smt_encoder::conjoin(&conjuncts)
}

/// Parses the three positional `(check-sat)` answers from the z3 reply. Any
/// `(error …)` line — a certificate that failed to parse, an arity mismatch —
/// fails the check outright: an errored assert silently vanishes from the
/// query, which could leave a VC vacuous. A `timeout` line is z3's `-T`
/// backstop, not a fourth answer.
fn parse_vc_results(stdout: &str) -> Result<Vec<String>, String> {
    if let Some(err) = z3_process::error_line(stdout) {
        return Err(format!("z3 error while checking the certificate: {err}"));
    }
    if z3_process::timeout_line(stdout) {
        return Err("z3 hard timeout while checking the certificate".to_string());
    }
    let results: Vec<String> = stdout
        .lines()
        .map(str::trim)
        .filter(|l| matches!(*l, "sat" | "unsat" | "unknown"))
        .map(str::to_string)
        .collect();
    if results.len() != 3 {
        return Err(format!(
            "expected 3 VC answers from z3, got {}: {:?}",
            results.len(),
            results
        ));
    }
    Ok(results)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::marking_state::MarkingStateBuilder;
    use crate::net_flattener::flatten;
    use libpetri_core::action::fork;
    use libpetri_core::input::one;
    use libpetri_core::output::out_place;
    use libpetri_core::petri_net::PetriNet;
    use libpetri_core::place::Place;
    use libpetri_core::transition::Transition;

    use crate::smt_verifier::z3_available;
    use crate::z3_process::error_line;

    /// The assembled three-VC script, for the shape assertions below.
    #[allow(clippy::too_many_arguments)]
    fn build_certificate_script(
        certificate: &str,
        flat: &FlatNet,
        initial_marking: &MarkingState,
        property: &SmtProperty,
        invariants: &[PInvariant],
        sink_places: &[String],
        env_bounds: &[(String, usize)],
        env_injection: &[(String, Option<usize>)],
    ) -> String {
        VerificationConditions::build(
            certificate,
            flat,
            initial_marking,
            property,
            invariants,
            sink_places,
            env_bounds,
            env_injection,
        )
        .script()
    }

    /// Chain p1 -> p2 with initial marking p1=1. Sorted place order: p1=0, p2=1.
    fn chain() -> (FlatNet, MarkingState) {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(fork())
            .build();
        let net = PetriNet::builder("chain").transition(t).build();
        let flat = flatten(&net);
        let marking = MarkingStateBuilder::new().tokens("p1", 1).build();
        (flat, marking)
    }

    /// The genuine inductive invariant of the chain net: p1 + p2 = 1, p1 >= 0.
    const GOOD_CERT: &str = "(define-fun Reachable ((x!0 Int) (x!1 Int)) Bool \
                             (and (= (+ x!0 x!1) 1) (>= x!0 0)))";

    #[test]
    fn script_shape_pastes_cert_and_omits_invariants() {
        let (flat, marking) = chain();
        let script = build_certificate_script(
            GOOD_CERT,
            &flat,
            &marking,
            &SmtProperty::place_bound("p2", 1),
            &[],
            &[],
            &[],
            &[],
        );
        assert!(script.contains(GOOD_CERT), "certificate pasted verbatim\n{script}");
        assert!(script.contains("(declare-const m0 Int)"));
        assert!(script.contains("(declare-const m1p Int)"));
        assert!(script.contains("(assert (not (Reachable 1 0)))"), "init VC on M0\n{script}");
        assert!(script.contains("(assert (>= m0 0))"), "VC2/VC3 constrain M to ℕ^P\n{script}");
        assert!(script.contains("(assert (not (Reachable m0p m1p)))"));
        assert_eq!(script.matches("(check-sat)").count(), 3);
        assert_eq!(script.matches("(push)").count(), 3);
        assert!(!script.contains("(set-logic"), "plain SMT, no HORN logic\n{script}");
    }

    #[test]
    fn missing_reachable_definition_fails_cleanly() {
        let (flat, marking) = chain();
        let outcome = check_certificate(
            "(define-fun Other () Bool true)",
            &flat,
            &marking,
            &SmtProperty::place_bound("p2", 1),
            &[],
            &[],
            &[],
            &[],
            5_000,
        );
        match outcome {
            CertificateCheck::Inconclusive { reason } => {
                assert!(reason.contains("does not define Reachable"), "{reason}")
            }
            other => panic!("expected Inconclusive, got {other:?}"),
        }
    }

    #[test]
    fn parse_vc_results_rejects_errors_and_wrong_counts() {
        assert_eq!(
            parse_vc_results("unsat\nunsat\nunsat\n").unwrap(),
            vec!["unsat", "unsat", "unsat"]
        );
        assert!(parse_vc_results("unsat\nunsat\n").is_err(), "two answers");
        let err = parse_vc_results("(error \"line 3: unknown constant\")\nunsat\nsat\nunsat\n")
            .unwrap_err();
        assert!(err.contains("z3 error"), "{err}");
    }

    #[test]
    fn good_certificate_passes_all_three_vcs() {
        if !z3_available() {
            eprintln!("skipping good_certificate_*: z3 binary not on PATH");
            return;
        }
        let (flat, marking) = chain();
        let outcome = check_certificate(
            GOOD_CERT,
            &flat,
            &marking,
            &SmtProperty::place_bound("p2", 1),
            &[],
            &[],
            &[],
            &[],
            5_000,
        );
        assert_eq!(outcome, CertificateCheck::Passed);
    }

    #[test]
    fn trivial_true_certificate_fails_safety_vc() {
        if !z3_available() {
            eprintln!("skipping trivial_true_*: z3 binary not on PATH");
            return;
        }
        // `Reachable := true` passes init and consecution vacuously but cannot
        // exclude the bad states of a net whose bound is genuinely violable
        // (p2 can reach 1 > 0), so the safety VC must catch it.
        let (flat, marking) = chain();
        let outcome = check_certificate(
            "(define-fun Reachable ((x!0 Int) (x!1 Int)) Bool true)",
            &flat,
            &marking,
            &SmtProperty::place_bound("p2", 0),
            &[],
            &[],
            &[],
            &[],
            5_000,
        );
        match outcome {
            CertificateCheck::Failed { vc, detail } => {
                assert_eq!(vc, "safety (VC3)");
                assert!(detail.contains("SATISFIABLE"), "{detail}");
            }
            other => panic!("expected Failed(safety), got {other:?}"),
        }
    }

    #[test]
    fn non_inductive_certificate_fails_consecution_vc() {
        if !z3_available() {
            eprintln!("skipping non_inductive_*: z3 binary not on PATH");
            return;
        }
        // `Reachable := {M0}` contains the initial marking and excludes the bad
        // states, but t1 fires M0 -> (0, 1) which leaves the set: consecution
        // must catch it.
        let (flat, marking) = chain();
        let outcome = check_certificate(
            "(define-fun Reachable ((x!0 Int) (x!1 Int)) Bool (and (= x!0 1) (= x!1 0)))",
            &flat,
            &marking,
            &SmtProperty::place_bound("p2", 1),
            &[],
            &[],
            &[],
            &[],
            5_000,
        );
        match outcome {
            CertificateCheck::Failed { vc, detail } => {
                assert_eq!(vc, "consecution (VC2)");
                // The witness names places, not `m` variables (C2).
                assert!(detail.contains("SATISFIABLE"), "{detail}");
            }
            other => panic!("expected Failed(consecution), got {other:?}"),
        }
    }

    #[test]
    fn empty_certificate_fails_init_vc() {
        if !z3_available() {
            eprintln!("skipping empty_certificate_*: z3 binary not on PATH");
            return;
        }
        // `Reachable := false` does not contain the initial marking.
        let (flat, marking) = chain();
        let outcome = check_certificate(
            "(define-fun Reachable ((x!0 Int) (x!1 Int)) Bool false)",
            &flat,
            &marking,
            &SmtProperty::place_bound("p2", 1),
            &[],
            &[],
            &[],
            &[],
            5_000,
        );
        match outcome {
            CertificateCheck::Failed { vc, .. } => assert_eq!(vc, "initiation (VC1)"),
            other => panic!("expected Failed(initiation), got {other:?}"),
        }
    }

    #[test]
    fn malformed_certificate_fails_via_z3_error() {
        if !z3_available() {
            eprintln!("skipping malformed_certificate_*: z3 binary not on PATH");
            return;
        }
        // Wrong arity: `(Reachable m0 m1)` becomes a z3 error, which must fail
        // the check rather than leave the VCs vacuous.
        let (flat, marking) = chain();
        let outcome = check_certificate(
            "(define-fun Reachable ((x!0 Int)) Bool true)",
            &flat,
            &marking,
            &SmtProperty::place_bound("p2", 1),
            &[],
            &[],
            &[],
            &[],
            5_000,
        );
        match outcome {
            CertificateCheck::Inconclusive { reason } => {
                assert!(reason.contains("z3 error"), "{reason}")
            }
            other => panic!("expected Inconclusive(z3 error), got {other:?}"),
        }
    }

    /// The chain's conservation law p1 + p2 = 1 as a P-invariant.
    fn chain_invariant(constant: i64) -> PInvariant {
        PInvariant {
            weights: vec![1, 1],
            constant,
            support: vec![0, 1],
        }
    }

    #[test]
    fn candidate_conjoins_invariants_but_step_relation_stays_bare() {
        let (flat, marking) = chain();
        let script = build_certificate_script(
            GOOD_CERT,
            &flat,
            &marking,
            &SmtProperty::place_bound("p2", 1),
            &[chain_invariant(1)],
            &[],
            &[],
            &[],
        );
        // The candidate carries the invariant on current, next, and initial
        // markings...
        assert!(
            script.contains("(and (Reachable m0 m1) (= (+ (* 1 m0) (* 1 m1)) 1))"),
            "{script}"
        );
        assert!(
            script.contains("(assert (not (and (Reachable m0p m1p) (= (+ (* 1 m0p) (* 1 m1p)) 1))))"),
            "{script}"
        );
        assert!(
            script.contains("(assert (not (and (Reachable 1 0) (= (+ (* 1 1) (* 1 0)) 1))))"),
            "{script}"
        );
        // ...but the step relation itself stays unstrengthened: the only m'
        // equality mentioning the constant-sum shape comes from the candidate,
        // not from T. T for the chain is a single conjunction of fire/non-neg
        // conjuncts; assert it verbatim to pin that.
        assert!(
            script.contains(
                "(assert (and (>= m0 1) (= m0p (- m0 1)) (= m1p (+ m1 1)) (>= m0p 0) (>= m1p 0)))"
            ),
            "{script}"
        );
    }

    /// Independence from the pre-encoding P-invariant validation (C2): a
    /// poisoned invariant cannot weaken the check — a wrong constant fails
    /// initiation, a non-conserved law fails consecution, and the genuine law
    /// passes. `Reachable := p2 <= 1` needs the conservation law to be
    /// inductive, mirroring how Spacer leans on the strengthening.
    #[test]
    fn strengthening_invariants_are_themselves_reverified() {
        if !z3_available() {
            eprintln!("skipping strengthening_invariants_*: z3 binary not on PATH");
            return;
        }
        let (flat, marking) = chain();
        let cert = "(define-fun Reachable ((x!0 Int) (x!1 Int)) Bool (<= x!1 1))";
        let check = |invariants: &[PInvariant]| {
            check_certificate(
                cert,
                &flat,
                &marking,
                &SmtProperty::place_bound("p2", 1),
                invariants,
                &[],
                &[],
                &[],
                5_000,
            )
        };

        // Genuine law: R' = (p2 <= 1) ∧ (p1 + p2 = 1) is inductive and safe.
        assert_eq!(check(&[chain_invariant(1)]), CertificateCheck::Passed);

        // Wrong constant: p1 + p2 = 2 does not hold at M0 -> init VC fails.
        match check(&[chain_invariant(2)]) {
            CertificateCheck::Failed { vc, .. } => assert_eq!(
                vc, "initiation (VC1)",
                "a wrong constant must fail initiation"
            ),
            other => panic!("expected Failed(initiation), got {other:?}"),
        }

        // Non-conserved law: p1 = 1 is broken by t1 -> consecution VC fails.
        let bogus = PInvariant {
            weights: vec![1, 0],
            constant: 1,
            support: vec![0],
        };
        match check(&[bogus]) {
            CertificateCheck::Failed { vc, .. } => assert_eq!(
                vc, "consecution (VC2)",
                "a non-conserved law must fail consecution"
            ),
            other => panic!("expected Failed(consecution), got {other:?}"),
        }
    }

    /// V2 (the `conservedPair` fixture shape): a certificate that is inductive
    /// and safe over ℕ^P but NOT over ℤ^P must still pass. `p0 + p1 = 3` bounds
    /// `p1` by 3 only when neither place can go negative; without the domain
    /// constraint the safety VC finds `(-1, 4)` and a correct `Proven` is lost.
    #[test]
    fn certificate_inductive_over_naturals_only_still_passes() {
        if !z3_available() {
            eprintln!("skipping certificate_inductive_over_naturals_*: z3 binary not on PATH");
            return;
        }
        let p0 = Place::<i32>::new("p0");
        let p1 = Place::<i32>::new("p1");
        let t = Transition::builder("t")
            .input(one(&p0))
            .output(out_place(&p1))
            .action(fork())
            .build();
        let flat = flatten(&PetriNet::builder("conservedPair").transition(t).build());
        let marking = MarkingStateBuilder::new().tokens("p0", 3).build();
        let outcome = check_certificate(
            "(define-fun Reachable ((x!0 Int) (x!1 Int)) Bool (= (+ x!0 x!1) 3))",
            &flat,
            &marking,
            &SmtProperty::place_bound("p1", 3),
            &[],
            &[],
            &[],
            &[],
            5_000,
        );
        assert_eq!(outcome, CertificateCheck::Passed);
    }

    /// V7: the documented "never panics" contract holds for a caller-supplied
    /// invariant whose shape does not line up with the net.
    #[test]
    fn malformed_invariant_shape_is_inconclusive_not_a_panic() {
        let (flat, marking) = chain();
        let out_of_range = PInvariant {
            weights: vec![1, 1],
            constant: 1,
            support: vec![0, 7],
        };
        match check_certificate(
            GOOD_CERT,
            &flat,
            &marking,
            &SmtProperty::place_bound("p2", 1),
            &[out_of_range],
            &[],
            &[],
            &[],
            5_000,
        ) {
            CertificateCheck::Inconclusive { reason } => {
                assert!(reason.contains("place index 7"), "{reason}")
            }
            other => panic!("expected Inconclusive, got {other:?}"),
        }

        let short = PInvariant {
            weights: vec![1],
            constant: 1,
            support: vec![0],
        };
        assert!(matches!(
            check_certificate(
                GOOD_CERT,
                &flat,
                &marking,
                &SmtProperty::place_bound("p2", 1),
                &[short],
                &[],
                &[],
                &[],
                5_000,
            ),
            CertificateCheck::Inconclusive { .. }
        ));
    }

    /// V6: an `(error …)` routed to stderr must not leave the three stdout
    /// answers looking clean, and a non-success exit is never a pass.
    #[test]
    fn stderr_errors_and_bad_exit_are_caught() {
        assert!(error_line("warning: x\n(error \"line 3: bad\")\n").is_some());
        assert!(error_line("all good\n").is_none());
        // A warning line ahead of the answers is tolerated (V5's shape).
        assert_eq!(
            parse_vc_results("WARNING: blah\nunsat\nunsat\nunsat\n").unwrap(),
            vec!["unsat", "unsat", "unsat"]
        );
    }

    /// The `(get-model)` reply is rendered with PLACE names for the C2 detail.
    #[test]
    fn witness_uses_place_names() {
        let (flat, _) = chain();
        let model = "sat\n(\n  (define-fun m0 () Int 2)\n  (define-fun m1 () Int 1)\n)\n";
        assert_eq!(witness(model, &flat).as_deref(), Some("p1=2, p2=1"));
        // A negative literal prints as `(- 1)`; the witness reads `-1`.
        let negative = "sat\n(\n  (define-fun m0 () Int (- 1))\n  (define-fun m1 () Int 4)\n)\n";
        assert_eq!(witness(negative, &flat).as_deref(), Some("p1=-1, p2=4"));
        assert_eq!(witness("sat\n", &flat), None);
        assert_eq!(
            reason_unknown("unknown\n(:reason-unknown \"timeout\")\n").as_deref(),
            Some("timeout")
        );
    }
}
