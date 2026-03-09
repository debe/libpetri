use std::collections::HashSet;
use std::time::Instant;

use libpetri_core::petri_net::PetriNet;

use crate::counterexample::{self, DecodedTrace};
use crate::environment::EnvironmentAnalysisMode;
use crate::incidence_matrix::IncidenceMatrix;
use crate::marking_state::{MarkingState, MarkingStateBuilder};
use crate::net_flattener::{self, FlatNet};
use crate::p_invariant;
use crate::property::SmtProperty;
use crate::result::{Verdict, VerificationResult, VerificationStatistics};
use crate::smt_encoder;
use crate::structural_check::{self, StructuralCheckResult};

/// Builder for SMT verification of Petri net properties.
///
/// Uses a 5-phase pipeline:
/// 1. Flatten — expand XOR branches into separate transitions
/// 2. Structural pre-check — siphon/trap analysis (may prove deadlock-freedom early)
/// 3. P-invariants — conservation laws for IC3 strengthening
/// 4. SMT encode + query — CHC encoding for Z3 Spacer
/// 5. Result formatting
pub struct SmtVerifier<'a> {
    net: &'a PetriNet,
    initial_marking: MarkingState,
    property: SmtProperty,
    env_places: HashSet<String>,
    env_mode: EnvironmentAnalysisMode,
    sink_places: Vec<String>,
    timeout_ms: u64,
}

impl<'a> SmtVerifier<'a> {
    /// Creates a verifier for the given net.
    pub fn for_net(net: &'a PetriNet) -> Self {
        Self {
            net,
            initial_marking: MarkingStateBuilder::new().build(),
            property: SmtProperty::DeadlockFree,
            env_places: HashSet::new(),
            env_mode: EnvironmentAnalysisMode::Ignore,
            sink_places: Vec::new(),
            timeout_ms: 30_000,
        }
    }

    /// Sets the initial marking.
    pub fn initial_marking(mut self, marking: MarkingState) -> Self {
        self.initial_marking = marking;
        self
    }

    /// Sets the property to verify.
    pub fn property(mut self, property: SmtProperty) -> Self {
        self.property = property;
        self
    }

    /// Adds environment places.
    pub fn environment_places(mut self, places: impl IntoIterator<Item = String>) -> Self {
        self.env_places.extend(places);
        self
    }

    /// Sets the environment analysis mode.
    pub fn environment_mode(mut self, mode: EnvironmentAnalysisMode) -> Self {
        self.env_mode = mode;
        self
    }

    /// Sets sink places (excluded from deadlock detection).
    pub fn sink_places(mut self, places: impl IntoIterator<Item = String>) -> Self {
        self.sink_places.extend(places);
        self
    }

    /// Sets the Z3 timeout in milliseconds.
    pub fn timeout(mut self, ms: u64) -> Self {
        self.timeout_ms = ms;
        self
    }

    /// Runs the verification pipeline.
    ///
    /// Returns a result with verdict, report, and diagnostics.
    ///
    /// This method performs the full 5-phase pipeline:
    /// 1. Flatten the net (XOR expansion)
    /// 2. Structural pre-check (siphon/trap)
    /// 3. Compute P-invariants
    /// 4. Encode as CHC and query Z3 Spacer
    /// 5. Format results
    pub fn verify(self) -> VerificationResult {
        let start = Instant::now();
        let mut report = String::new();

        // Phase 1: Flatten
        report.push_str("=== Phase 1: Net Flattening ===\n");
        let flat = net_flattener::flatten(self.net);
        report.push_str(&format!(
            "Places: {}, Transitions: {} (flat: {})\n\n",
            flat.place_count,
            self.net.transitions().len(),
            flat.transitions.len()
        ));

        // Environment bounds
        let env_bounds: Vec<(String, usize)> = match &self.env_mode {
            EnvironmentAnalysisMode::Bounded { max_tokens } => self
                .env_places
                .iter()
                .map(|name| (name.clone(), *max_tokens))
                .collect(),
            _ => Vec::new(),
        };

        // Phase 2: Structural pre-check
        report.push_str("=== Phase 2: Structural Analysis ===\n");
        let structural_result = structural_check::structural_check(&flat);
        let structural_str = match &structural_result {
            StructuralCheckResult::NoPotentialDeadlock => "no potential deadlock",
            StructuralCheckResult::PotentialDeadlock => "potential deadlock detected",
            StructuralCheckResult::Inconclusive => "inconclusive",
        };
        report.push_str(&format!("Result: {structural_str}\n\n"));

        // If structural analysis proves deadlock-freedom and we're checking that property,
        // we can return early.
        if matches!(self.property, SmtProperty::DeadlockFree)
            && self.sink_places.is_empty()
            && structural_result == StructuralCheckResult::NoPotentialDeadlock
        {
            let elapsed_ms = start.elapsed().as_millis() as u64;
            report.push_str("Deadlock freedom proven structurally (Commoner's theorem).\n");
            return VerificationResult {
                verdict: Verdict::Proven {
                    method: "structural".into(),
                    inductive_invariant: None,
                },
                report,
                invariants: Vec::new(),
                discovered_invariants: Vec::new(),
                counterexample_trace: Vec::new(),
                counterexample_transitions: Vec::new(),
                elapsed_ms,
                statistics: VerificationStatistics {
                    places: flat.place_count,
                    transitions: flat.transitions.len(),
                    invariants_found: 0,
                    structural_result: structural_str.into(),
                },
            };
        }

        // Phase 3: P-invariants
        report.push_str("=== Phase 3: P-Invariants ===\n");
        let matrix = IncidenceMatrix::from_flat_net(&flat);
        let invariants =
            p_invariant::compute_p_invariants(&matrix, &self.initial_marking, &flat.places);
        report.push_str(&format!("Found {} P-invariant(s)\n", invariants.len()));

        for (i, inv) in invariants.iter().enumerate() {
            let terms: Vec<String> = inv
                .support
                .iter()
                .map(|&pid| {
                    if inv.weights[pid] == 1 {
                        flat.places[pid].clone()
                    } else {
                        format!("{}·{}", inv.weights[pid], flat.places[pid])
                    }
                })
                .collect();
            report.push_str(&format!(
                "  I{}: {} = {}\n",
                i,
                terms.join(" + "),
                inv.constant
            ));
        }

        let is_covered = p_invariant::is_covered_by_invariants(&invariants, flat.place_count);
        if is_covered {
            report.push_str("All places covered by invariants (structurally bounded)\n");
        }
        report.push('\n');

        // Phase 4: SMT Encode + Query
        report.push_str("=== Phase 4: SMT Verification ===\n");
        report.push_str(&format!("Property: {}\n", self.property.description()));

        let encoding = smt_encoder::encode(
            &flat,
            &self.initial_marking,
            &self.property,
            &invariants,
            &self.sink_places,
            &env_bounds,
        );

        // Run Z3 Spacer
        let z3_result = run_z3_spacer(&encoding.smt2, self.timeout_ms);

        let (verdict, decoded_trace, discovered_invariants) =
            process_z3_result(&z3_result, &flat, &mut report);

        let elapsed_ms = start.elapsed().as_millis() as u64;

        report.push_str(&format!("\nElapsed: {}ms\n", elapsed_ms));

        VerificationResult {
            verdict,
            report,
            invariants: invariants.clone(),
            discovered_invariants,
            counterexample_trace: decoded_trace.trace,
            counterexample_transitions: decoded_trace.transitions,
            elapsed_ms,
            statistics: VerificationStatistics {
                places: flat.place_count,
                transitions: flat.transitions.len(),
                invariants_found: invariants.len(),
                structural_result: structural_str.into(),
            },
        }
    }
}

/// Result from Z3 Spacer.
enum Z3Result {
    Unsat { invariant_formula: Option<String> },
    Sat { answer: String },
    Unknown { reason: String },
}

/// Runs Z3 Spacer on the given SMT-LIB2 string.
///
/// Invokes `z3` as a subprocess with Spacer engine.
fn run_z3_spacer(smt2: &str, timeout_ms: u64) -> Z3Result {
    use std::io::Write;
    use std::process::{Command, Stdio};

    // Z3 -T flag uses seconds; round up so sub-second timeouts don't become 0
    let timeout_secs = timeout_ms.div_ceil(1000).max(1);

    let mut child = match Command::new("z3")
        .args([
            "-smt2",
            "-in",
            &format!("-T:{timeout_secs}"),
            "fp.engine=spacer",
        ])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
    {
        Ok(child) => child,
        Err(e) => {
            return Z3Result::Unknown {
                reason: format!("Failed to spawn z3: {e}"),
            };
        }
    };

    if let Some(stdin) = child.stdin.as_mut() {
        if let Err(e) = stdin.write_all(smt2.as_bytes()) {
            return Z3Result::Unknown {
                reason: format!("Failed to write to z3 stdin: {e}"),
            };
        }
    }

    let output = match child.wait_with_output() {
        Ok(output) => output,
        Err(e) => {
            return Z3Result::Unknown {
                reason: format!("Z3 process error: {e}"),
            };
        }
    };

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stdout = stdout.trim();

    if stdout.starts_with("unsat") {
        Z3Result::Unsat {
            invariant_formula: extract_invariant_from_output(stdout),
        }
    } else if stdout.starts_with("sat") {
        Z3Result::Sat {
            answer: stdout.to_string(),
        }
    } else {
        let stderr = String::from_utf8_lossy(&output.stderr);
        Z3Result::Unknown {
            reason: if stderr.is_empty() {
                format!("Unexpected Z3 output: {stdout}")
            } else {
                format!("Z3 error: {stderr}")
            },
        }
    }
}

/// Extracts the invariant formula from Z3 output (lines after "unsat").
fn extract_invariant_from_output(output: &str) -> Option<String> {
    let lines: Vec<&str> = output.lines().collect();
    if lines.len() > 1 {
        Some(lines[1..].join("\n"))
    } else {
        None
    }
}

/// Processes the Z3 result into a verdict.
fn process_z3_result(
    result: &Z3Result,
    flat: &FlatNet,
    report: &mut String,
) -> (Verdict, DecodedTrace, Vec<String>) {
    match result {
        Z3Result::Unsat { invariant_formula } => {
            report.push_str("Result: UNSAT (property proven)\n");
            let discovered = if let Some(formula) = invariant_formula {
                report.push_str(&format!("Inductive invariant: {formula}\n"));
                vec![formula.clone()]
            } else {
                Vec::new()
            };
            (
                Verdict::Proven {
                    method: "IC3/PDR".into(),
                    inductive_invariant: invariant_formula.clone(),
                },
                DecodedTrace::empty(),
                discovered,
            )
        }
        Z3Result::Sat { answer } => {
            report.push_str("Result: SAT (property violated)\n");
            let decoded = counterexample::decode(answer, flat);
            if !decoded.trace.is_empty() {
                report.push_str(&format!(
                    "Counterexample trace: {} states, {} transitions\n",
                    decoded.trace.len(),
                    decoded.transitions.len()
                ));
            }
            (Verdict::Violated, decoded, Vec::new())
        }
        Z3Result::Unknown { reason } => {
            report.push_str(&format!("Result: UNKNOWN ({reason})\n"));
            (
                Verdict::Unknown {
                    reason: reason.clone(),
                },
                DecodedTrace::empty(),
                Vec::new(),
            )
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::marking_state::MarkingStateBuilder;
    use libpetri_core::input::one;
    use libpetri_core::output::out_place;
    use libpetri_core::place::Place;
    use libpetri_core::transition::Transition;

    #[test]
    fn verifier_builder_creates_defaults() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let verifier = SmtVerifier::for_net(&net)
            .initial_marking(MarkingStateBuilder::new().tokens("p1", 1).build())
            .property(SmtProperty::DeadlockFree)
            .timeout(5000);

        assert_eq!(verifier.timeout_ms, 5000);
    }

    #[test]
    fn structural_shortcut_for_cycle() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .build();
        let t2 = Transition::builder("t2")
            .input(one(&p2))
            .output(out_place(&p1))
            .build();
        let net = PetriNet::builder("cycle").transitions([t1, t2]).build();

        let result = SmtVerifier::for_net(&net)
            .initial_marking(MarkingStateBuilder::new().tokens("p1", 1).build())
            .property(SmtProperty::DeadlockFree)
            .verify();

        assert!(result.is_proven());
        assert!(result.report.contains("structural"));
    }

    #[test]
    fn verifier_with_env_places() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let verifier = SmtVerifier::for_net(&net)
            .initial_marking(MarkingStateBuilder::new().tokens("p1", 1).build())
            .property(SmtProperty::DeadlockFree)
            .environment_places(vec!["p1".into()])
            .environment_mode(EnvironmentAnalysisMode::Bounded { max_tokens: 5 });

        assert!(verifier.env_places.contains("p1"));
    }

    #[test]
    fn verifier_with_sink_places() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let verifier = SmtVerifier::for_net(&net)
            .initial_marking(MarkingStateBuilder::new().tokens("p1", 1).build())
            .property(SmtProperty::DeadlockFree)
            .sink_places(vec!["p2".into()]);

        assert_eq!(verifier.sink_places, vec!["p2"]);
    }
}
