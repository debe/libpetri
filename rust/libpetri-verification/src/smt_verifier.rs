use std::collections::HashSet;
use std::time::Instant;

use libpetri_core::petri_net::PetriNet;

use crate::counterexample::{self, DecodedTrace};
use crate::environment::EnvironmentAnalysisMode;
use crate::incidence_matrix::IncidenceMatrix;
use crate::marking_state::{MarkingState, MarkingStateBuilder};
use crate::name_coloured_encoder;
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
    /// ν-net budget places ([NU-040]): places whose token count bounds the live
    /// correlation pool (they gate fresh-name minting). Declaring at least one
    /// places the net in the decidable bounded fragment; without it a net that
    /// mints fresh names is treated as unbounded and yields `Unknown` ([NU-050]).
    budget_places: HashSet<String>,
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
            budget_places: HashSet::new(),
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

    /// Declares a ν-net budget place ([NU-040]): a place whose token count bounds
    /// the live correlation pool (it gates fresh-name minting). Declaring at
    /// least one budget place asserts the net lives in the decidable bounded
    /// fragment, so reachability-safety properties over its ν-joins are verified
    /// (over-approximating name equality). Without any budget place, a net that
    /// mints fresh names is treated as unbounded and the verifier returns
    /// `Unknown` ([NU-050]).
    pub fn budget_place(mut self, place: impl Into<String>) -> Self {
        self.budget_places.insert(place.into());
        self
    }

    /// Declares multiple ν-net budget places. See [`SmtVerifier::budget_place`].
    pub fn budget_places(mut self, places: impl IntoIterator<Item = String>) -> Self {
        self.budget_places.extend(places);
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

        // ν-net awareness ([NU-040], [NU-050]). A transition with a match spec
        // joins by name equality; the untimed encoder over-approximates that
        // (name equality assumed satisfiable). The over-approximation is sound
        // for reachability-safety bounds (`Proven` holds — the real net fires
        // strictly fewer joins) but NOT for quiescence-based properties
        // (deadlock / joined-or-dead-lettered), which the name-blind firing
        // distorts. The end-of-pipeline guard turns those cases into `Unknown`.
        let has_match = self.net.transitions().iter().any(|t| t.match_spec().is_some());
        let nu_bounded = !self.budget_places.is_empty();

        // Phase 1: Flatten
        report.push_str("=== Phase 1: Net Flattening ===\n");
        let flat = net_flattener::flatten(self.net);
        report.push_str(&format!(
            "Places: {}, Transitions: {} (flat: {})\n\n",
            flat.place_count,
            self.net.transitions().len(),
            flat.transitions.len()
        ));

        // Environment bounds (legacy post-cap) and the injection map (VER-006).
        // env_injection drives the env-injection CHC rule, the incidence-matrix
        // injector columns, and the relaxed deadlock check. None = unbounded
        // (AlwaysAvailable), Some(k) = Bounded(k); Ignore models no injection.
        let env_bounds: Vec<(String, usize)> = match &self.env_mode {
            EnvironmentAnalysisMode::Bounded { max_tokens } => self
                .env_places
                .iter()
                .map(|name| (name.clone(), *max_tokens))
                .collect(),
            _ => Vec::new(),
        };
        let env_injection: Vec<(String, Option<usize>)> = match &self.env_mode {
            EnvironmentAnalysisMode::AlwaysAvailable => {
                self.env_places.iter().map(|n| (n.clone(), None)).collect()
            }
            EnvironmentAnalysisMode::Bounded { max_tokens } => self
                .env_places
                .iter()
                .map(|n| (n.clone(), Some(*max_tokens)))
                .collect(),
            EnvironmentAnalysisMode::Ignore => Vec::new(),
        };
        // Resolved injector place indices for the incidence matrix.
        let env_inject_indices: Vec<usize> = env_injection
            .iter()
            .filter_map(|(name, _)| flat.place_index.get(name).copied())
            .collect();

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
        // we can return early. Skipped when environment places are registered: the
        // siphon/trap analysis runs on the closed net and is blind to env injection
        // (VER-006), so its early proof could be unsound — fall through to the
        // (injection-aware) SMT encoding instead.
        if matches!(self.property, SmtProperty::DeadlockFree)
            && !has_match
            && self.sink_places.is_empty()
            && self.env_places.is_empty()
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
        let matrix = IncidenceMatrix::from_flat_net(&flat, &env_inject_indices);
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

        // ν-net exact refinement (NU-050 #1, Route A). For a budget-bounded ν-net
        // in the supported mint→matched-join fragment, encode names as a finite
        // colour set (k = the declared budget) with exact same-colour join
        // matching, instead of the name-blind over-approximation — this rules out
        // spurious counterexamples that would equate two distinct names. Only
        // reachability-safety properties are routed here; everything else (and
        // any net outside the fragment) keeps the flat encoding.
        let coloured_plan = if has_match && nu_bounded && is_reachability_safety(&self.property) {
            name_coloured_encoder::build_plan(
                self.net,
                &flat,
                &self.initial_marking,
                &self.budget_places,
            )
        } else {
            None
        };

        let encoding = if let Some(plan) = &coloured_plan {
            report.push_str(&format!(
                "ν-encoding: name-coloured (exact within budget k={}; {} coloured place(s))\n",
                plan.k,
                plan.coloured.len()
            ));
            name_coloured_encoder::encode_coloured(
                plan,
                &flat,
                &self.initial_marking,
                &self.property,
                &invariants,
            )
        } else {
            smt_encoder::encode(
                &flat,
                &self.initial_marking,
                &self.property,
                &invariants,
                &self.sink_places,
                &env_bounds,
                &env_injection,
            )
        };

        // Run Z3 Spacer
        let z3_result = run_z3_spacer(&encoding.smt2, self.timeout_ms);

        let (mut verdict, decoded_trace, discovered_invariants) =
            process_z3_result(&z3_result, &flat, &mut report);

        // Guard against silent vacuous proofs (VER-006): in Ignore mode the encoding
        // does not model env injection, so env-gated transitions never fire and ANY
        // safety bound is trivially "proven". Refuse to certify — downgrade to Unknown.
        if matches!(verdict, Verdict::Proven { .. })
            && !self.env_places.is_empty()
            && self.env_mode == EnvironmentAnalysisMode::Ignore
        {
            let reason = "environment places present but not modeled (mode=Ignore); a proof \
                would be vacuous — use AlwaysAvailable or Bounded(k) to model external injection"
                .to_string();
            report.push_str(&format!("Downgraded to UNKNOWN: {reason}\n"));
            verdict = Verdict::Unknown { reason };
        }

        // ν-net soundness guard ([NU-040], [NU-050]). Applied only when the net
        // contains match (ν-join) transitions, and only to a Proven/Violated
        // verdict (an existing Unknown is left as-is).
        if has_match && !matches!(verdict, Verdict::Unknown { .. }) {
            if !is_reachability_safety(&self.property) {
                // Quiescence-based properties: the name-blind over-approximation
                // over-fires joins, so it sees fewer quiescent states and may
                // miss a real stranded marking. Refuse to certify — exact
                // quiescence reasoning over names is deferred to the SCG
                // name-partition quotient (NU-050 #1).
                let reason = "ν-matching transitions present and the property depends on \
                    quiescence (deadlock / joined-or-dead-lettered); the name-blind \
                    over-approximation cannot decide it soundly — deferred to the exact \
                    ν-analysis (NU-050)"
                    .to_string();
                report.push_str(&format!("Downgraded to UNKNOWN: {reason}\n"));
                verdict = Verdict::Unknown { reason };
            } else if !nu_bounded {
                // Unbounded fresh names: outside the decidable bounded fragment.
                // Reachability/liveness over unbounded fresh names is undecidable
                // (ν-PN reachability); a budget place restores a finite WSTS.
                let reason = "ν-matching transitions present with unbounded fresh names (no \
                    budget place declared via .budget_place(...)); reachability over unbounded \
                    fresh names is undecidable (NU-040) — declare the budget place(s) that gate \
                    minting to verify within the bounded fragment"
                    .to_string();
                report.push_str(&format!("Downgraded to UNKNOWN: {reason}\n"));
                verdict = Verdict::Unknown { reason };
            } else if coloured_plan.is_some() {
                // Exact path (NU-050 #1, Route A): name equality is encoded
                // exactly via bounded name-colouring, so the verdict is sound AND
                // complete within the budget bound — no spurious different-name
                // counterexample. Both `Proven` and `Violated` are trustworthy.
                report.push_str(
                    "Note: ν-join name equality is encoded exactly via bounded name-colouring \
                     (k = budget); the verdict is sound and complete within the budget bound — \
                     no spurious different-name counterexample (NU-050 #1).\n",
                );
            } else {
                // Bounded reachability-safety, but outside the name-coloured
                // fragment: `Proven` is sound. A `Violated` counterexample may be
                // spurious (it could require joining two distinct names), which
                // the exact ν-analysis would rule out.
                report.push_str(
                    "Note: matched (ν-join) transitions are over-approximated (name equality \
                     assumed satisfiable). 'Proven' is sound; a 'Violated' counterexample may \
                     be spurious pending the exact ν-analysis (NU-050).\n",
                );
            }
        }

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

/// Whether a property is a *reachability-safety* property — one whose violation
/// is a reachable bad marking (a "∃ reachable state" check). For these the
/// matched-transition over-approximation is sound for `Proven` (the real net
/// reaches a subset of states). Quiescence-based properties (deadlock,
/// joined-or-dead-lettered) are NOT reachability-safety: their violation
/// involves the *absence* of enabled transitions, which the name-blind
/// over-approximation distorts unsafely ([NU-050]).
fn is_reachability_safety(property: &SmtProperty) -> bool {
    match property {
        SmtProperty::PlaceBound { .. }
        | SmtProperty::BranchPlaceBound { .. }
        | SmtProperty::MutualExclusion { .. }
        | SmtProperty::Unreachable { .. } => true,
        SmtProperty::DeadlockFree | SmtProperty::JoinedOrDeadLettered { .. } => false,
    }
}

/// Outcome of a Z3 Spacer run, in verdict terms.
///
/// Note the HORN/Spacer convention (verified empirically): with the query
/// `(assert (not Error))`, z3 prints `sat` when the property is PROVEN (an
/// inductive invariant excluding all violating states exists) and `unsat` when it
/// is VIOLATED (no such invariant). `run_z3_spacer` performs that translation, so
/// downstream code works in verdict terms.
enum Z3Result {
    /// Property proven (z3 `sat`); the model is the inductive invariant, if printed.
    Proven { invariant_formula: Option<String> },
    /// Property violated (z3 `unsat`); `answer` is the raw solver output.
    Violated { answer: String },
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
        // unsat => no inductive invariant excludes the bad state => VIOLATED.
        Z3Result::Violated {
            answer: stdout.to_string(),
        }
    } else if stdout.starts_with("sat") {
        // sat => an inductive invariant exists => PROVEN.
        Z3Result::Proven {
            invariant_formula: extract_invariant_from_output(stdout),
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
        Z3Result::Proven { invariant_formula } => {
            report.push_str("Result: property proven (Spacer SAT — inductive invariant found)\n");
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
        Z3Result::Violated { answer } => {
            report.push_str("Result: property violated (Spacer UNSAT — no inductive invariant)\n");
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
    use libpetri_core::input::{exactly, one};
    use libpetri_core::output::out_place;
    use libpetri_core::place::Place;
    use libpetri_core::transition::Transition;

    /// True if the `z3` binary is on PATH (the verifier shells out to it). Tests
    /// that exercise Z3 early-return (skip) when it is absent.
    fn z3_available() -> bool {
        std::process::Command::new("z3")
            .arg("--version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
    }

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

    // === VER-006: Environment injection soundness ===
    // Regression for the bug where the SMT verifier vacuously "proved" safety bounds
    // on nets with environment places (env columns could only be consumed, never
    // produced, so the reachable set froze at the initial marking).

    fn env_source_net() -> PetriNet {
        // env IN -> T -> OUT
        let in_p = Place::<i32>::new("IN");
        let out = Place::<i32>::new("OUT");
        let t = Transition::builder("T")
            .input(one(&in_p))
            .output(out_place(&out))
            .build();
        PetriNet::builder("env-source").transition(t).build()
    }

    #[test]
    fn ver006_env_source_always_available_place_bound_violated() {
        if !z3_available() {
            eprintln!("skipping ver006_env_source_*: z3 binary not on PATH");
            return;
        }
        // AlwaysAvailable lets IN be injected without bound, so OUT grows without
        // bound: place_bound(OUT, k) is violated for every finite k.
        for k in [0usize, 1, 5] {
            let result = SmtVerifier::for_net(&env_source_net())
                .environment_places(vec!["IN".into()])
                .environment_mode(EnvironmentAnalysisMode::AlwaysAvailable)
                .property(SmtProperty::place_bound("OUT", k))
                .timeout(15_000)
                .verify();
            assert!(
                result.is_violated(),
                "place_bound(OUT, {k}) must be violated under env injection\n{}",
                result.report
            );
        }
    }

    #[test]
    fn ver006_bounded_gates_by_multiplicity() {
        if !z3_available() {
            eprintln!("skipping ver006_bounded_*: z3 binary not on PATH");
            return;
        }
        // T2 needs EXACTLY 2 tokens from env IN per firing. bounded(1) starves it
        // (OUT stays 0 -> proven), AlwaysAvailable feeds it (OUT unbounded -> violated).
        // Also exercises the env-aware P-invariant: the closed-net law IN + 2*OUT = 0
        // must be discarded so OUT is not vacuously pinned.
        let build = || {
            let in_p = Place::<i32>::new("IN");
            let out = Place::<i32>::new("OUT");
            let t = Transition::builder("T2")
                .input(exactly(2, &in_p))
                .output(out_place(&out))
                .build();
            PetriNet::builder("env-mult").transition(t).build()
        };

        let bounded1 = SmtVerifier::for_net(&build())
            .environment_places(vec!["IN".into()])
            .environment_mode(EnvironmentAnalysisMode::Bounded { max_tokens: 1 })
            .property(SmtProperty::place_bound("OUT", 0))
            .timeout(15_000)
            .verify();
        assert!(
            bounded1.is_proven(),
            "bounded(1) starves a 2-token env input -> OUT stays 0\n{}",
            bounded1.report
        );

        let always = SmtVerifier::for_net(&build())
            .environment_places(vec!["IN".into()])
            .environment_mode(EnvironmentAnalysisMode::AlwaysAvailable)
            .property(SmtProperty::place_bound("OUT", 0))
            .timeout(15_000)
            .verify();
        assert!(
            always.is_violated(),
            "AlwaysAvailable feeds the 2-token env input -> OUT unbounded\n{}",
            always.report
        );
    }

    #[test]
    fn ver006_ignore_mode_with_env_places_downgrades_to_unknown() {
        if !z3_available() {
            eprintln!("skipping ver006_ignore_*: z3 binary not on PATH");
            return;
        }
        // Ignore mode does not model injection; a "proven" here would be vacuous.
        let result = SmtVerifier::for_net(&env_source_net())
            .environment_places(vec!["IN".into()])
            .environment_mode(EnvironmentAnalysisMode::Ignore)
            .property(SmtProperty::place_bound("OUT", 1))
            .timeout(15_000)
            .verify();
        assert!(
            matches!(result.verdict, Verdict::Unknown { .. }),
            "ignore mode with env places must not silently prove, got {:?}\n{}",
            result.verdict,
            result.report
        );
    }

    // === NU-040 / NU-050: ν-net verification (sound carve-out, Stage 6a) ===
    // The untimed encoder over-approximates ν-join name equality. That is sound
    // for reachability-safety bounds (a Proven holds for the real net) — so the
    // bounded-budget decidability lever is checkable today — but not for
    // quiescence properties, and not for unbounded fresh names. These tests pin
    // the resulting verdict discipline on the real Z3 path.

    /// Structural scatter-gather: `fork` consumes a `budget` token and stamps a
    /// `pending` token plus both branches; `join` correlates the branches by
    /// name, consumes `pending`, and returns the `budget` token. The structural
    /// conservation laws `budget + pending = k` and `branchA = branchB = pending`
    /// hold regardless of names, so the over-approximation can prove the bounds.
    fn nu_scatter_gather_net() -> PetriNet {
        use libpetri_core::match_spec::MatchSpec;
        use libpetri_core::name::NameId;
        use libpetri_core::output::and;

        let source = Place::<()>::new("source");
        let budget = Place::<()>::new("budget");
        let pending = Place::<()>::new("pending");
        let a = Place::<String>::new("branchA");
        let b = Place::<String>::new("branchB");
        let merged = Place::<String>::new("merged");

        let fork = Transition::builder("fork")
            .input(one(&source))
            .input(one(&budget)) // minting a name costs one budget token
            .output(and(vec![
                out_place(&a),
                out_place(&b),
                out_place(&pending), // mark a live correlation group
            ]))
            .build();

        let join = Transition::builder("join")
            .input(one(&a))
            .input(one(&b))
            .input(one(&pending))
            .match_spec(
                MatchSpec::builder()
                    .key(&a, |s: &String| NameId::new(s.clone()))
                    .key(&b, |s: &String| NameId::new(s.clone()))
                    .build(),
            )
            .output(and(vec![out_place(&merged), out_place(&budget)])) // return budget
            .build();

        PetriNet::builder("nu_scatter_gather_verify")
            .transitions([fork, join])
            .build()
    }

    fn nu_initial_marking(k: usize) -> MarkingState {
        MarkingStateBuilder::new()
            .tokens("source", 3)
            .tokens("budget", k)
            .build()
    }

    #[test]
    fn nu_branch_budget_bound_proven_with_declared_budget() {
        if !z3_available() {
            eprintln!("skipping nu_branch_budget_bound_*: z3 binary not on PATH");
            return;
        }
        // NU-040 #1: with the budget declared, the live correlation pool is
        // bounded — BranchPlaceBound(budget, k) is proven by conservation.
        let net = nu_scatter_gather_net();
        let result = SmtVerifier::for_net(&net)
            .initial_marking(nu_initial_marking(2))
            .property(SmtProperty::branch_place_bound("budget", 2))
            .budget_place("budget")
            .timeout(15_000)
            .verify();
        assert!(
            result.is_proven(),
            "BranchPlaceBound(budget, 2) must be proven for the bounded scatter-gather\n{}",
            result.report
        );
    }

    #[test]
    fn nu_pending_bound_proven_with_declared_budget() {
        if !z3_available() {
            eprintln!("skipping nu_pending_bound_*: z3 binary not on PATH");
            return;
        }
        // NU-040 #2 (bound half): at most k live groups — Pending is bounded by k.
        let net = nu_scatter_gather_net();
        let result = SmtVerifier::for_net(&net)
            .initial_marking(nu_initial_marking(2))
            .property(SmtProperty::branch_place_bound("pending", 2))
            .budget_place("budget")
            .timeout(15_000)
            .verify();
        assert!(
            result.is_proven(),
            "BranchPlaceBound(pending, 2) must be proven for the bounded scatter-gather\n{}",
            result.report
        );
        // The scatter-gather is in the name-coloured fragment, so the bound is
        // decided exactly (NU-050 #1), not via the name-blind over-approximation.
        assert!(
            result.report.contains("name-coloured"),
            "a bounded ν-net in the supported fragment uses the exact name-coloured encoding\n{}",
            result.report
        );
    }

    #[test]
    fn nu_unbounded_without_declared_budget_is_unknown() {
        if !z3_available() {
            eprintln!("skipping nu_unbounded_*: z3 binary not on PATH");
            return;
        }
        // NU-050 #2: a ν-net that mints fresh names without a declared budget is
        // treated as unbounded — the verifier returns Unknown rather than a
        // (precision-limited) verdict, even for a bound the over-approximation
        // could prove. Declaring the budget place is what asserts the bounded
        // fragment.
        let net = nu_scatter_gather_net();
        let result = SmtVerifier::for_net(&net)
            .initial_marking(nu_initial_marking(2))
            .property(SmtProperty::branch_place_bound("budget", 2))
            .timeout(15_000)
            .verify();
        match &result.verdict {
            Verdict::Unknown { reason } => assert!(
                reason.contains("budget") && reason.contains("unbounded"),
                "Unknown reason should explain the missing budget declaration: {reason}"
            ),
            other => panic!("expected Unknown for an undeclared-budget ν-net, got {other:?}\n{}", result.report),
        }
    }

    #[test]
    fn nu_joined_or_dead_lettered_unknown_on_nu_net() {
        if !z3_available() {
            eprintln!("skipping nu_joined_or_dead_lettered_*: z3 binary not on PATH");
            return;
        }
        // JoinedOrDeadLettered is quiescence-based: the name-blind
        // over-approximation over-fires joins, so it cannot decide it soundly on
        // a ν-net. Even with the budget declared, the verdict is Unknown
        // (deferred to the exact ν-analysis, NU-050 #1).
        let net = nu_scatter_gather_net();
        let result = SmtVerifier::for_net(&net)
            .initial_marking(nu_initial_marking(2))
            .property(SmtProperty::joined_or_dead_lettered("pending"))
            .budget_place("budget")
            .timeout(15_000)
            .verify();
        assert!(
            matches!(result.verdict, Verdict::Unknown { .. }),
            "JoinedOrDeadLettered on a ν-net must be Unknown (quiescence deferred), got {:?}\n{}",
            result.verdict,
            result.report
        );
    }

    #[test]
    fn nu_deadlock_free_unknown_on_nu_net() {
        if !z3_available() {
            eprintln!("skipping nu_deadlock_free_*: z3 binary not on PATH");
            return;
        }
        // DeadlockFree is also quiescence-based — and the structural shortcut is
        // gated off for ν-nets — so it must end as Unknown, not a name-blind
        // (possibly unsound) proof.
        let net = nu_scatter_gather_net();
        let result = SmtVerifier::for_net(&net)
            .initial_marking(nu_initial_marking(2))
            .property(SmtProperty::DeadlockFree)
            .budget_place("budget")
            .timeout(15_000)
            .verify();
        assert!(
            matches!(result.verdict, Verdict::Unknown { .. }),
            "DeadlockFree on a ν-net must be Unknown (quiescence deferred), got {:?}\n{}",
            result.verdict,
            result.report
        );
    }

    #[test]
    fn joined_or_dead_lettered_proven_on_non_nu_net() {
        if !z3_available() {
            eprintln!("skipping joined_or_dead_lettered_proven_*: z3 binary not on PATH");
            return;
        }
        // On a net WITHOUT ν-matching the encoding is exact for quiescence, so
        // the property is soundly decided. Here `pending` always drains before
        // quiescence -> Proven.
        let start = Place::<()>::new("start");
        let pending = Place::<()>::new("pending");
        let done = Place::<()>::new("done");
        let produce = Transition::builder("gen")
            .input(one(&start))
            .output(out_place(&pending))
            .build();
        let fin = Transition::builder("fin")
            .input(one(&pending))
            .output(out_place(&done))
            .build();
        let net = PetriNet::builder("pending_drains")
            .transitions([produce, fin])
            .build();

        let result = SmtVerifier::for_net(&net)
            .initial_marking(MarkingStateBuilder::new().tokens("start", 1).build())
            .property(SmtProperty::joined_or_dead_lettered("pending"))
            .timeout(15_000)
            .verify();
        assert!(
            result.is_proven(),
            "every group joins/dead-letters before quiescence -> Proven\n{}",
            result.report
        );
    }

    #[test]
    fn joined_or_dead_lettered_violated_on_non_nu_net() {
        if !z3_available() {
            eprintln!("skipping joined_or_dead_lettered_violated_*: z3 binary not on PATH");
            return;
        }
        // A stranded `pending` token: `leak` produces into `pending` but nothing
        // consumes it, so the quiescent marking still holds a pending token ->
        // Violated.
        let start = Place::<()>::new("start");
        let pending = Place::<()>::new("pending");
        let leak = Transition::builder("leak")
            .input(one(&start))
            .output(out_place(&pending))
            .build();
        let net = PetriNet::builder("pending_strands").transition(leak).build();

        let result = SmtVerifier::for_net(&net)
            .initial_marking(MarkingStateBuilder::new().tokens("start", 1).build())
            .property(SmtProperty::joined_or_dead_lettered("pending"))
            .timeout(15_000)
            .verify();
        assert!(
            result.is_violated(),
            "a stranded pending token at quiescence -> Violated\n{}",
            result.report
        );
    }

    // === NU-050 #1: name-coloured exact ν-verification (Stage 6b, Route A) ===
    // The flat encoder over-approximates ν-join name equality (name-blind). The
    // bounded name-coloured encoding (k = budget) decides it exactly: a join
    // fires only on same-coloured tokens, so a counterexample requiring two
    // distinct names to be equal is eliminated. These tests pin that on Z3.

    /// Two INDEPENDENT mints feed one join: `forkA` mints a name into `branchA`,
    /// `forkB` mints a *different* name into `branchB`. Their names can never be
    /// equal, so the join can never correlate them and `merged` is unreachable.
    /// The name-blind over-approximation would (wrongly) fire the join — exactly
    /// the spurious "two distinct names are equal" counterexample NU-050 #1 kills.
    fn nu_distinct_mints_net() -> PetriNet {
        use libpetri_core::match_spec::MatchSpec;
        use libpetri_core::name::NameId;

        let source_a = Place::<()>::new("sourceA");
        let source_b = Place::<()>::new("sourceB");
        let budget = Place::<()>::new("budget");
        let a = Place::<String>::new("branchA");
        let b = Place::<String>::new("branchB");
        let merged = Place::<String>::new("merged");

        let fork_a = Transition::builder("forkA")
            .input(one(&source_a))
            .input(one(&budget))
            .output(out_place(&a))
            .build();
        let fork_b = Transition::builder("forkB")
            .input(one(&source_b))
            .input(one(&budget))
            .output(out_place(&b))
            .build();
        let join = Transition::builder("join")
            .input(one(&a))
            .input(one(&b))
            .match_spec(
                MatchSpec::builder()
                    .key(&a, |s: &String| NameId::new(s.clone()))
                    .key(&b, |s: &String| NameId::new(s.clone()))
                    .build(),
            )
            .output(out_place(&merged))
            .build();

        PetriNet::builder("nu_distinct_mints")
            .transitions([fork_a, fork_b, join])
            .build()
    }

    #[test]
    fn nu_distinct_mints_never_join_merged_unreachable() {
        if !z3_available() {
            eprintln!("skipping nu_distinct_mints_*: z3 binary not on PATH");
            return;
        }
        // NU-050 #1: distinct-mint names can never join -> `merged` unreachable.
        // The name-blind over-approximation would report this Violated (spurious);
        // the name-coloured encoding proves it.
        let net = nu_distinct_mints_net();
        let result = SmtVerifier::for_net(&net)
            .initial_marking(
                MarkingStateBuilder::new()
                    .tokens("sourceA", 1)
                    .tokens("sourceB", 1)
                    .tokens("budget", 2)
                    .build(),
            )
            .property(SmtProperty::unreachable(vec!["merged".into()]))
            .budget_place("budget")
            .timeout(15_000)
            .verify();
        assert!(
            result.is_proven(),
            "distinct-mint names can never correlate -> merged unreachable -> Proven\n{}",
            result.report
        );
        assert!(
            result.report.contains("name-coloured"),
            "must use the exact name-coloured encoding\n{}",
            result.report
        );
    }

    #[test]
    fn nu_same_mint_can_join_merged_reachable() {
        if !z3_available() {
            eprintln!("skipping nu_same_mint_*: z3 binary not on PATH");
            return;
        }
        // Companion (non-vacuity): the SAME-mint scatter-gather stamps both
        // branches with one name, so the join CAN fire and `merged` IS reachable.
        // The colouring tracks real reachability — Unreachable(merged) is Violated.
        let net = nu_scatter_gather_net();
        let result = SmtVerifier::for_net(&net)
            .initial_marking(nu_initial_marking(2))
            .property(SmtProperty::unreachable(vec!["merged".into()]))
            .budget_place("budget")
            .timeout(15_000)
            .verify();
        assert!(
            result.is_violated(),
            "same-mint siblings can join -> merged reachable -> Violated\n{}",
            result.report
        );
    }
}
