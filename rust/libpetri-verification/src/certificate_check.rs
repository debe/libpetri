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
use crate::smt_verifier::run_z3_text;

/// Names of the three verification conditions, in script order.
const VC_NAMES: [&str; 3] = ["init", "consecution", "safety"];

/// Outcome of the certificate check.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CertificateCheck {
    /// All three VCs discharged (z3 answered `unsat` to each).
    Passed,
    /// The certificate did not check out; `reason` names the failing VC or the
    /// z3/parse failure. The verifier downgrades the verdict to `Unknown`.
    Failed { reason: String },
}

/// Re-verifies an extracted proof certificate against the unstrengthened step
/// relation. `certificate` is the `(define-fun …)` block extracted verbatim
/// from the Spacer model (auxiliary definitions included, so `Reachable`
/// stays resolvable); `invariants` are the validated P-invariants the CHC
/// encoding was strengthened with — conjoined into the candidate and thereby
/// re-proven by the VCs themselves (see the module docs). Never panics: every
/// failure mode — missing `Reachable`, a z3 error, an unparseable reply, a
/// sat/unknown VC — comes back as [`CertificateCheck::Failed`].
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
    if !certificate.contains("(define-fun Reachable ")
        && !certificate.contains("(define-fun |Reachable| ")
    {
        return CertificateCheck::Failed {
            reason: "certificate does not define Reachable".to_string(),
        };
    }

    let script = build_certificate_script(
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
    let output = match run_z3_text(&script, timeout_ms, &[]) {
        Ok(output) => output,
        Err(reason) => return CertificateCheck::Failed { reason },
    };
    let stdout = String::from_utf8_lossy(&output.stdout);

    let results = match parse_vc_results(&stdout) {
        Ok(results) => results,
        Err(reason) => return CertificateCheck::Failed { reason },
    };

    for (vc, result) in VC_NAMES.iter().zip(results.iter()) {
        if result != "unsat" {
            return CertificateCheck::Failed {
                reason: format!("{vc} VC not discharged: z3 answered '{result}' (expected unsat)"),
            };
        }
    }
    CertificateCheck::Passed
}

/// Builds the plain SMT-LIB2 script: the pasted certificate, the marking
/// constants (`m0…mN` current, `m0p…mNp` next — the CHC encoding's naming),
/// then the three VCs under `(push)`/`(pop)`, each with its own `(check-sat)`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn build_certificate_script(
    certificate: &str,
    flat: &FlatNet,
    initial_marking: &MarkingState,
    property: &SmtProperty,
    invariants: &[PInvariant],
    sink_places: &[String],
    env_bounds: &[(String, usize)],
    env_injection: &[(String, Option<usize>)],
) -> String {
    let p = flat.place_count;
    let m_vars: Vec<String> = (0..p).map(|i| format!("m{i}")).collect();
    let mp_vars: Vec<String> = (0..p).map(|i| format!("m{i}p")).collect();

    let mut lines = Vec::new();
    lines.push("; IC3/PDR certificate check (plain SMT-LIB2, not HORN):".to_string());
    lines.push("; each VC below must be unsat for the certificate to stand.".to_string());
    lines.push(certificate.to_string());
    lines.push(String::new());
    for v in m_vars.iter().chain(mp_vars.iter()) {
        lines.push(format!("(declare-const {v} Int)"));
    }

    // VC1 (init): the initial marking satisfies the candidate invariant.
    let m0_values: Vec<String> = (0..p)
        .map(|i| initial_marking.count(&flat.places[i]).to_string())
        .collect();
    lines.push(String::new());
    lines.push("; VC1 init".to_string());
    lines.push("(push)".to_string());
    lines.push(format!("(assert (not {}))", candidate(&m0_values, invariants)));
    lines.push("(check-sat)".to_string());
    lines.push("(pop)".to_string());

    // VC2 (consecution): the invariant is closed under the unstrengthened
    // step relation (transition firings + env-injection steps, no P-invariant
    // conjuncts).
    let step = smt_encoder::encode_step_relation_smt2(flat, env_bounds, env_injection);
    lines.push(String::new());
    lines.push("; VC2 consecution".to_string());
    lines.push("(push)".to_string());
    lines.push(format!("(assert {})", candidate(&m_vars, invariants)));
    lines.push(format!("(assert {step})"));
    lines.push(format!("(assert (not {}))", candidate(&mp_vars, invariants)));
    lines.push("(check-sat)".to_string());
    lines.push("(pop)".to_string());

    // VC3 (safety): the invariant excludes every property-violating state —
    // exactly the violation the CHC error rule encodes.
    let env_inject = smt_encoder::resolve_env_injection(flat, env_injection);
    let bad =
        smt_encoder::encode_property_violation(flat, property, &m_vars, sink_places, &env_inject);
    lines.push(String::new());
    lines.push("; VC3 safety".to_string());
    lines.push("(push)".to_string());
    lines.push(format!("(assert {})", candidate(&m_vars, invariants)));
    lines.push(format!("(assert {bad})"));
    lines.push("(check-sat)".to_string());
    lines.push("(pop)".to_string());

    lines.join("\n")
}

/// The candidate invariant applied to a variable (or literal) vector:
/// `R'(vars) = (Reachable vars) ∧ Inv(vars)`. With no P-invariants this is
/// the bare `Reachable` application.
fn candidate(vars: &[String], invariants: &[PInvariant]) -> String {
    let mut conjuncts = vec![format!("(Reachable {})", vars.join(" "))];
    conjuncts.extend(smt_encoder::invariant_conditions(invariants, vars));
    if conjuncts.len() == 1 {
        conjuncts.swap_remove(0)
    } else {
        format!("(and {})", conjuncts.join(" "))
    }
}

/// Parses the three positional `(check-sat)` answers from the z3 reply. Any
/// `(error …)` line — a certificate that failed to parse, an arity mismatch —
/// fails the check outright: an errored assert silently vanishes from the
/// query, which could leave a VC vacuous.
fn parse_vc_results(stdout: &str) -> Result<Vec<String>, String> {
    if let Some(err) = stdout
        .lines()
        .find(|l| l.trim_start().starts_with("(error"))
    {
        return Err(format!("z3 error while checking the certificate: {}", err.trim()));
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

    fn z3_available() -> bool {
        std::process::Command::new("z3")
            .arg("--version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
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
            CertificateCheck::Failed { reason } => {
                assert!(reason.contains("does not define Reachable"), "{reason}")
            }
            other => panic!("expected Failed, got {other:?}"),
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
            CertificateCheck::Failed { reason } => {
                assert!(reason.contains("safety"), "must name the safety VC: {reason}")
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
            CertificateCheck::Failed { reason } => assert!(
                reason.contains("consecution"),
                "must name the consecution VC: {reason}"
            ),
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
            CertificateCheck::Failed { reason } => {
                assert!(reason.contains("init"), "must name the init VC: {reason}")
            }
            other => panic!("expected Failed(init), got {other:?}"),
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
            CertificateCheck::Failed { reason } => {
                assert!(reason.contains("z3 error"), "{reason}")
            }
            other => panic!("expected Failed(z3 error), got {other:?}"),
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
            CertificateCheck::Failed { reason } => {
                assert!(reason.contains("init"), "wrong constant must fail init: {reason}")
            }
            other => panic!("expected Failed(init), got {other:?}"),
        }

        // Non-conserved law: p1 = 1 is broken by t1 -> consecution VC fails.
        let bogus = PInvariant {
            weights: vec![1, 0],
            constant: 1,
            support: vec![0],
        };
        match check(&[bogus]) {
            CertificateCheck::Failed { reason } => assert!(
                reason.contains("consecution"),
                "non-conserved law must fail consecution: {reason}"
            ),
            other => panic!("expected Failed(consecution), got {other:?}"),
        }
    }
}
