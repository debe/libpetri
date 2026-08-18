use std::collections::{BTreeSet, HashSet};
use std::time::Instant;

use libpetri_core::petri_net::{PetriNet, require_output_producing_actions};

use crate::abstract_replay::{self, ReplayOutcome};
use crate::certificate_check::{self, CertificateCheck};
use crate::counterexample::{self, DecodedTrace};
use crate::environment::EnvironmentAnalysisMode;
use crate::incidence_matrix::IncidenceMatrix;
use crate::marking_state::{MarkingState, MarkingStateBuilder};
use crate::name_coloured_encoder;
use crate::name_fragment::FragmentMode;
use crate::net_flattener::{self, FlatNet};
use crate::nu_scg_verifier;
use crate::p_invariant::{self, PInvariant};
use crate::priority_semantics::PrioritySemantics;
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
    /// Class-count cap for the ν-aware state-class-graph name-partition analysis
    /// ([NU-050], Route B). When the symbolic name-aware graph would exceed this,
    /// the analysis truncates and the verdict is `Unknown` (the live correlation
    /// pool is not structurally bounded). Default 100_000.
    nu_max_classes: usize,
    /// Which coloured-place fragment the ν-aware SCG admits ([NU-051]). `Base`
    /// (default) reproduces the shipped mint → matched-join behaviour; `Extended`
    /// additionally admits the drain/relay coloured-consumer role and the
    /// declared `carrier_places`.
    fragment_mode: FragmentMode,
    /// EXTENDED-only carrier places ([NU-051]): intermediate places that carry a
    /// fresh name from the minting fork onward to a ν-join input. Ignored under
    /// `FragmentMode::Base`. An unknown name (not in the net) surfaces as
    /// `Unknown` from [`SmtVerifier::verify`], never a silent fall-back.
    carrier_places: HashSet<String>,
    /// How the ν-aware Route B analyzer treats transition priority ([NU-052]).
    /// [`PrioritySemantics::None`] (default) is the priority-blind
    /// over-approximation; [`PrioritySemantics::Conflict`] prunes a lower-priority
    /// firing pre-empted by a conflicting, no-later-ready, strictly-higher-priority
    /// one.
    priority_semantics: PrioritySemantics,
    /// Whether a flat-path `Proven` is re-verified by [`crate::certificate_check`]
    /// (default `true`). See [`SmtVerifier::certificate_phase`].
    certificate_check: bool,
    /// Whether a flat-path `Violated` is re-validated by [`crate::abstract_replay`]
    /// (default `true`). See [`SmtVerifier::replay_phase`].
    counterexample_replay: bool,
    /// Test seam: replaces the extracted certificate fed to the certificate
    /// check, so tests can prove end-to-end that a corrupt certificate
    /// downgrades the verdict.
    #[cfg(test)]
    certificate_override: Option<String>,
    /// Test seam: replaces the state set decoded from the z3 refutation
    /// proof, so tests can prove end-to-end that an unchainable set
    /// downgrades the verdict and an empty decode leaves it
    /// Violated-unconfirmed.
    #[cfg(test)]
    replay_state_set_override: Option<Vec<Vec<i64>>>,
    /// Test seam: shrinks the replay's node budget, so a test can reach the
    /// exhaustion arm on a small net.
    #[cfg(test)]
    replay_node_budget_override: Option<usize>,
}

impl<'a> SmtVerifier<'a> {
    /// Creates a verifier for the given net.
    ///
    /// # Panics
    /// Panics per **CORE-043** if a transition declares an output spec but carries
    /// `passthrough()`, so a proof over this net implies a net that can actually run.
    pub fn for_net(net: &'a PetriNet) -> Self {
        require_output_producing_actions(net);
        Self {
            net,
            initial_marking: MarkingStateBuilder::new().build(),
            property: SmtProperty::DeadlockFree,
            env_places: HashSet::new(),
            env_mode: EnvironmentAnalysisMode::Ignore,
            sink_places: Vec::new(),
            budget_places: HashSet::new(),
            timeout_ms: 30_000,
            nu_max_classes: 100_000,
            fragment_mode: FragmentMode::Base,
            carrier_places: HashSet::new(),
            priority_semantics: PrioritySemantics::None,
            certificate_check: true,
            counterexample_replay: true,
            #[cfg(test)]
            certificate_override: None,
            #[cfg(test)]
            replay_state_set_override: None,
            #[cfg(test)]
            replay_node_budget_override: None,
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

    /// Sets the class-count cap for the ν-aware state-class-graph analysis
    /// ([NU-050], Route B). See [`SmtVerifier`]'s `nu_max_classes` field.
    pub fn nu_max_classes(mut self, max: usize) -> Self {
        self.nu_max_classes = max;
        self
    }

    /// Selects the coloured-place fragment for the ν-aware SCG ([NU-051]).
    /// [`FragmentMode::Base`] (default) admits only mint → matched-join;
    /// [`FragmentMode::Extended`] additionally admits the drain/relay
    /// coloured-consumer role and the declared [`SmtVerifier::carrier_place`]s.
    /// If EXTENDED is requested but the net falls outside the coloured-consumer
    /// fragment, [`SmtVerifier::verify`] appends a short "Route B (EXTENDED)
    /// declined" note and verifies via the sound over-approximation instead.
    pub fn fragment_mode(mut self, mode: FragmentMode) -> Self {
        self.fragment_mode = mode;
        self
    }

    /// Declares a ν-net carrier place ([NU-051]): an intermediate place that
    /// carries a fresh name from the minting fork onward to a ν-join input, so
    /// the fork co-mints one name into it. Effective only under
    /// [`FragmentMode::Extended`]; ignored under `Base`. A name not present in the
    /// net surfaces as an `Unknown` verdict from [`SmtVerifier::verify`] (Rust's
    /// fluent builder is infallible), never a silent fall-back.
    pub fn carrier_place(mut self, place: impl Into<String>) -> Self {
        self.carrier_places.insert(place.into());
        self
    }

    /// Declares multiple ν-net carrier places. See [`SmtVerifier::carrier_place`].
    pub fn carrier_places(mut self, places: impl IntoIterator<Item = String>) -> Self {
        self.carrier_places.extend(places);
        self
    }

    /// Selects how the Route-B name-aware analyzer treats transition priority
    /// ([NU-052]). Defaults to [`PrioritySemantics::None`] (priority-blind
    /// over-approximation). [`PrioritySemantics::Conflict`] models the executor's
    /// conflict-only priority resolution, so a lower-priority transition pre-empted
    /// by a conflicting, no-later-ready, strictly-higher-priority one is not
    /// explored — removing spurious dead-letter-drain stalls the eager,
    /// priority-ordered executor never produces.
    pub fn priority_semantics(mut self, semantics: PrioritySemantics) -> Self {
        self.priority_semantics = semantics;
        self
    }

    /// Enables or disables the independent certificate check on the proven
    /// IC3/PDR path (default: enabled). With it off, `Proven` rests on the
    /// solver's say-so alone. See [`crate::certificate_check`].
    pub fn certificate_check(mut self, enabled: bool) -> Self {
        self.certificate_check = enabled;
        self
    }

    /// Enables or disables abstract counterexample replay on the violated
    /// flat-path verdict (default: enabled). With it off, no counterexample
    /// trace is produced at all. See [`crate::abstract_replay`].
    pub fn counterexample_replay(mut self, enabled: bool) -> Self {
        self.counterexample_replay = enabled;
        self
    }

    /// Test seam: substitute the certificate handed to the certificate check.
    #[cfg(test)]
    fn certificate_override(mut self, certificate: impl Into<String>) -> Self {
        self.certificate_override = Some(certificate.into());
        self
    }

    /// Test seam: substitute the state set handed to the abstract replay.
    #[cfg(test)]
    fn replay_state_set_override(mut self, states: Vec<Vec<i64>>) -> Self {
        self.replay_state_set_override = Some(states);
        self
    }

    /// Test seam: shrink the replay's node budget.
    #[cfg(test)]
    fn replay_node_budget(mut self, budget: usize) -> Self {
        self.replay_node_budget_override = Some(budget);
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

        // ν-net Route B ([NU-050]): the name-aware state-class-graph name-partition
        // quotient decides ν-join correlation EXACTLY — including name×time and
        // quiescence — without a budget. It "fills the gaps" the SMT / Route A path
        // cannot answer exactly: quiescence properties on a ν-net, and unbudgeted
        // reachability-safety. Budgeted, untimed reachability-safety in Route A's
        // fragment stays on Route A below (this trigger is false there). If the net
        // is outside the supported fragment, `verify_via_name_scg` returns None and
        // we fall through to the existing pipeline (which applies the sound Unknown
        // downgrade for these cases).
        if has_match && (!is_reachability_safety(&self.property) || !nu_bounded) {
            let env_refs: Vec<&str> = self.env_places.iter().map(|s| s.as_str()).collect();
            let carrier_set: BTreeSet<String> = self.carrier_places.iter().cloned().collect();
            let scg_outcome = nu_scg_verifier::verify_via_name_scg(
                self.net,
                &self.initial_marking,
                &self.property,
                &self.sink_places,
                &env_refs,
                &self.env_mode,
                self.nu_max_classes,
                self.fragment_mode,
                &carrier_set,
                self.priority_semantics,
            );
            // Route B truncating to Unknown on a bounded quiescence ν-net is not the
            // final word: defer to the scalable Route A coloured IC3/PDR encoder
            // ([NU-053]) below instead of returning Unknown here.
            let defer_to_route_a = scg_outcome.as_ref().is_some_and(|o| {
                matches!(o.verdict, Verdict::Unknown { .. })
                    && !is_reachability_safety(&self.property)
                    && nu_bounded
            });
            if let Some(outcome) = scg_outcome.filter(|_| !defer_to_route_a) {
                let elapsed_ms = start.elapsed().as_millis() as u64;
                report.push_str("=== ν-net Route B: name-aware state-class graph (NU-050) ===\n");
                report.push_str(&format!("Property: {}\n", self.property.description()));
                report.push_str(&format!(
                    "Name-partition state classes: {}\n",
                    outcome.class_count
                ));
                report.push_str(&outcome.note);
                if !outcome.transitions.is_empty() {
                    report.push_str(&format!(
                        "Counterexample trace: {} states, {} transitions\n",
                        outcome.trace.len(),
                        outcome.transitions.len()
                    ));
                }
                report.push_str(&format!("\nElapsed: {elapsed_ms}ms\n"));
                return build_result(
                    outcome.verdict,
                    report,
                    elapsed_ms,
                    VerificationStatistics {
                        places: self.net.places().len(),
                        transitions: self.net.transitions().len(),
                        invariants_found: 0,
                        structural_result: "n/a (ν name-partition SCG)".into(),
                    },
                    Diagnostics {
                        trace: DecodedTrace {
                            trace: outcome.trace,
                            transitions: outcome.transitions,
                        },
                        ..Diagnostics::none()
                    },
                );
            } else if defer_to_route_a {
                report.push_str(
                    "ν-net Route B inconclusive (name-partition truncated); deferring to \
                     Route A coloured IC3/PDR ([NU-053]).\n",
                );
            }
            // EXTENDED was requested but the net is outside the coloured-consumer
            // fragment (classify declined). Surface a short note instead of a
            // silent cliff, then verify via the sound over-approximation below
            // ([NU-051], §5 diagnosability).
            if self.fragment_mode == FragmentMode::Extended && !defer_to_route_a {
                report.push_str(
                    "ν-net Route B (EXTENDED) declined: net outside coloured-consumer fragment \
                     (a coloured place consumed count != 1 or by multiple inputs, carries a \
                     reset/read/inhibitor arc, or a join re-mints a coloured place); verified via \
                     sound over-approximation instead.\n",
                );
            }
        }

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
            report.push_str(&cert_not_applicable("structural proof"));
            return build_result(
                Verdict::Proven {
                    method: "structural".into(),
                    inductive_invariant: None,
                },
                report,
                elapsed_ms,
                flat_statistics(&flat, 0, structural_str),
                Diagnostics::none(),
            );
        }

        // Phase 3: P-invariants
        report.push_str("=== Phase 3: P-Invariants ===\n");
        let matrix = IncidenceMatrix::from_flat_net(&flat, &env_inject_indices);
        // Exact re-validation between computation and use: the encoders conjoin each
        // invariant into the CHC transition-rule BODIES, where a numerically wrong
        // equality (the elimination is unchecked i64) removes reachable successors
        // and could certify a false `Proven`. Only invariants that re-verify exactly
        // (checked i128: y·C = 0 componentwise, constant = y·M0) reach an encoder;
        // the rest are dropped with a report line below.
        let validation = p_invariant::validate_invariants_exact(
            p_invariant::compute_p_invariants(&matrix, &self.initial_marking, &flat.places),
            &matrix,
            &self.initial_marking,
            &flat,
        );
        let invariants = validation.valid;
        // P-semiflows (non-negative conservation laws) bound the simultaneously-live
        // colour count that sets the name-coloured encoder's slot count `k`
        // (see build_plan / colour_slot_bound) — validated the same way before they
        // can set that bound.
        let semiflow_validation = p_invariant::validate_invariants_exact(
            p_invariant::compute_p_semiflows(&matrix, &self.initial_marking, &flat.places),
            &matrix,
            &self.initial_marking,
            &flat,
        );
        let semiflows = semiflow_validation.valid;
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

        append_invariant_drop_report(&mut report, &validation.dropped, "P-invariant");
        append_invariant_drop_report(&mut report, &semiflow_validation.dropped, "P-semiflow");

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
        // spurious counterexamples that would equate two distinct names.
        // Reachability-safety AND quiescence ([NU-053]) properties are both routed
        // here; a net outside the fragment keeps the flat encoding.
        let coloured_plan = if has_match && nu_bounded {
            name_coloured_encoder::build_plan(
                self.net,
                &flat,
                &self.initial_marking,
                &self.budget_places,
                self.fragment_mode,
                &self.carrier_places,
                &semiflows,
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
            let env_inject_idx: Vec<(usize, Option<usize>)> = env_injection
                .iter()
                .filter_map(|(name, b)| flat.place_index.get(name).map(|&pid| (pid, *b)))
                .collect();
            match name_coloured_encoder::encode_coloured(
                plan,
                &flat,
                &self.initial_marking,
                &self.property,
                &invariants,
                &self.sink_places,
                &env_inject_idx,
            ) {
                Some(enc) => enc,
                None => {
                    // The property names a place that does not resolve in the net
                    // (e.g. a typo'd bound/pending place). Emitting the encoding
                    // anyway would certify a vacuous `Proven`; refuse and report
                    // Unknown so a mis-named place never silently certifies.
                    let reason = "property names a place that does not resolve in the net; \
                        refusing to certify (the encoding would be vacuously Proven)"
                        .to_string();
                    report.push_str(&format!("Downgraded to UNKNOWN: {reason}\n"));
                    let elapsed_ms = start.elapsed().as_millis() as u64;
                    return build_result(
                        Verdict::Unknown { reason },
                        report,
                        elapsed_ms,
                        flat_statistics(&flat, invariants.len(), structural_str),
                        Diagnostics {
                            invariants: invariants.clone(),
                            ..Diagnostics::none()
                        },
                    );
                }
            }
        } else {
            smt_encoder::encode(
                &flat,
                &self.initial_marking,
                &self.property,
                &invariants,
                &self.sink_places,
                &env_bounds,
                &env_injection,
                // C3: request the refutation proof the replay decoder reads.
                self.counterexample_replay,
            )
        };

        // Run Z3 Spacer
        let z3_result = run_z3_spacer(&encoding.smt2, self.timeout_ms);

        let (mut verdict, decoded_trace, discovered_invariants) =
            process_z3_result(&z3_result, &mut report);

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
            if coloured_plan.is_some() {
                // Exact path (NU-050 #1 / NU-053, Route A): name equality is encoded
                // exactly via bounded name-colouring, so the verdict is sound AND
                // complete within the budget bound — no spurious different-name
                // counterexample. This holds for reachability-safety AND quiescence
                // (deadlock / joined-or-dead-lettered), so the quiescence downgrade
                // below does NOT apply when an exact coloured plan was used — the
                // colour-aware deadlock encoding does not over-fire joins.
                report.push_str(
                    "Note: ν-join name equality is encoded exactly via bounded name-colouring \
                     (k = budget); the verdict is sound and complete within the budget bound — \
                     no spurious different-name counterexample (NU-050 #1 / NU-053).\n",
                );
            } else if !is_reachability_safety(&self.property) {
                // Quiescence-based properties, name-blind (no coloured plan): the
                // over-approximation over-fires joins, so it sees fewer quiescent
                // states and may miss a real stranded marking. Refuse to certify —
                // exact quiescence reasoning over names is deferred to the SCG
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

        verdict = self.certificate_phase(
            verdict,
            &flat,
            &invariants,
            &env_bounds,
            &env_injection,
            coloured_plan.is_some(),
            &mut report,
        );

        let (verdict, decoded_trace, counterexample_confirmed) = self.replay_phase(
            verdict,
            &z3_result,
            &flat,
            &env_bounds,
            &env_injection,
            coloured_plan.is_some(),
            decoded_trace,
            &mut report,
        );

        let elapsed_ms = start.elapsed().as_millis() as u64;

        report.push_str(&format!("\nElapsed: {}ms\n", elapsed_ms));

        build_result(
            verdict,
            report,
            elapsed_ms,
            flat_statistics(&flat, invariants.len(), structural_str),
            Diagnostics {
                invariants,
                discovered: discovered_invariants,
                trace: decoded_trace,
                confirmed: counterexample_confirmed,
            },
        )
    }

    /// Certificate phase — the second independent layer, after Phase 3's exact
    /// P-invariant re-validation: a flat-path `Proven` must survive
    /// [`crate::certificate_check`] (canonical description there). Any failure
    /// downgrades to `Unknown`; a `Proven` the check did not examine says so in
    /// the report rather than passing silently.
    #[allow(clippy::too_many_arguments)]
    fn certificate_phase(
        &self,
        verdict: Verdict,
        flat: &FlatNet,
        invariants: &[PInvariant],
        env_bounds: &[(String, usize)],
        env_injection: &[(String, Option<usize>)],
        coloured: bool,
        report: &mut String,
    ) -> Verdict {
        if !matches!(verdict, Verdict::Proven { .. }) {
            return verdict;
        }
        // The coloured/ν encoding has its own variable layout, so the flat
        // count-vector VCs do not describe it. Say so rather than stay silent.
        if coloured {
            report.push_str(&cert_not_applicable("name-coloured encoding"));
            return verdict;
        }
        if !self.certificate_check {
            report.push_str(&cert_not_applicable("disabled"));
            return verdict;
        }

        let certificate = {
            let extracted = match &verdict {
                Verdict::Proven { inductive_invariant, .. } => inductive_invariant.clone(),
                _ => None,
            };
            #[cfg(test)]
            let extracted = self.certificate_override.clone().or(extracted);
            extracted
        };
        let Some(cert) = certificate else {
            let reason = certificate_inconclusive_reason(
                "no inductive invariant (define-fun block) could be extracted from the z3 model",
            );
            report.push_str(CERT_FAILED_LINE);
            report.push_str(&format!("Downgraded to UNKNOWN: {reason}\n"));
            return Verdict::Unknown { reason };
        };

        match certificate_check::check_certificate(
            &cert,
            flat,
            &self.initial_marking,
            &self.property,
            invariants,
            &self.sink_places,
            env_bounds,
            env_injection,
            self.timeout_ms,
        ) {
            CertificateCheck::Passed => {
                report.push_str(CERT_PASSED_LINE);
                verdict
            }
            CertificateCheck::Failed { vc, detail } => {
                let reason = certificate_failed_reason(vc, &detail);
                report.push_str(CERT_FAILED_LINE);
                report.push_str(&format!("Downgraded to UNKNOWN: {reason}\n"));
                Verdict::Unknown { reason }
            }
            CertificateCheck::Inconclusive { reason } => {
                let reason = certificate_inconclusive_reason(&reason);
                report.push_str(CERT_FAILED_LINE);
                report.push_str(&format!("Downgraded to UNKNOWN: {reason}\n"));
                Verdict::Unknown { reason }
            }
        }
    }

    /// Counterexample-replay phase: a flat-path `Violated` is re-validated
    /// against the abstract semantics ([`crate::abstract_replay`], canonical
    /// description there).
    ///
    /// Only [`ReplayOutcome::NoChain`] downgrades to `Unknown`. An exhausted
    /// budget, a decoded set without M₀, and an empty decode all leave
    /// `Violated` standing with `Some(false)` and a report note: they are
    /// absences of evidence, not evidence of absence. Flat count encoding only
    /// — the coloured/ν layout is not this abstraction.
    #[allow(clippy::too_many_arguments)]
    fn replay_phase(
        &self,
        verdict: Verdict,
        z3_result: &Z3Result,
        flat: &FlatNet,
        env_bounds: &[(String, usize)],
        env_injection: &[(String, Option<usize>)],
        coloured: bool,
        decoded_trace: DecodedTrace,
        report: &mut String,
    ) -> (Verdict, DecodedTrace, Option<bool>) {
        if !self.counterexample_replay || coloured || !matches!(verdict, Verdict::Violated) {
            return (verdict, decoded_trace, None);
        }
        let Z3Result::Violated { answer } = z3_result else {
            return (verdict, decoded_trace, None);
        };

        let decoded_set = counterexample::decode_state_set(answer, flat);
        #[cfg(test)]
        let decoded_set: BTreeSet<Vec<i64>> = self
            .replay_state_set_override
            .clone()
            .map(|states| states.into_iter().collect())
            .unwrap_or(decoded_set);
        if decoded_set.is_empty() {
            report.push_str(
                "Counterexample replay: no ground Reachable states in the z3 proof — \
                 verdict stays Violated (counterexample unconfirmed)\n",
            );
            return (verdict, decoded_trace, Some(false));
        }

        let m0: Vec<i64> = flat
            .places
            .iter()
            .map(|name| self.initial_marking.count(name) as i64)
            .collect();
        // The chain must anchor at the real initial marking. A decoded set
        // without M₀ carries no chain to search, but that is a property of the
        // proof text, not of the net: unconfirmed, not downgraded.
        if !decoded_set.contains(&m0) {
            report.push_str(
                "Counterexample replay: the decoded state set does not contain M0 — \
                 verdict stays Violated (counterexample unconfirmed)\n",
            );
            return (verdict, decoded_trace, Some(false));
        }

        let env_inject = smt_encoder::resolve_env_injection(flat, env_injection);
        let env_caps: Vec<(usize, usize)> = env_bounds
            .iter()
            .filter_map(|(name, cap)| flat.place_index.get(name).map(|&pid| (pid, *cap)))
            .collect();
        #[cfg(test)]
        let node_budget = self.replay_node_budget_override.unwrap_or(REPLAY_NODE_BUDGET);
        #[cfg(not(test))]
        let node_budget = REPLAY_NODE_BUDGET;

        match abstract_replay::replay(
            flat,
            &m0,
            &decoded_set,
            &self.property,
            &self.sink_places,
            &env_inject,
            &env_caps,
            REPLAY_MAX_SEGMENT_STEPS,
            node_budget,
        ) {
            ReplayOutcome::Confirmed(replayed) => {
                report.push_str(&format!(
                    "Counterexample replay: CONFIRMED — {} decoded state(s), chain of {} step(s) \
                     from M0 to a violating state (re-emitted in replay order):\n",
                    decoded_set.len(),
                    replayed.transitions.len()
                ));
                for (i, state) in replayed.states.iter().enumerate() {
                    report.push_str(&format!("  [{}] {}\n", i, format_abstract_state(flat, state)));
                    if let Some(label) = replayed.transitions.get(i) {
                        report.push_str(&format!("      --{label}-->\n"));
                    }
                }
                let trace = DecodedTrace {
                    trace: replayed
                        .states
                        .iter()
                        .map(|state| abstract_state_to_marking(flat, state))
                        .collect(),
                    transitions: replayed.transitions,
                };
                (verdict, trace, Some(true))
            }
            ReplayOutcome::Exhausted { reason } => {
                report.push_str(&format!(
                    "Counterexample replay: search budget exhausted ({reason}) — \
                     verdict stays Violated (counterexample unconfirmed)\n"
                ));
                (verdict, decoded_trace, Some(false))
            }
            ReplayOutcome::NoChain => {
                report.push_str(&format!("Downgraded to UNKNOWN: {REPLAY_NO_CHAIN_REASON}\n"));
                report.push_str("  decoded state set (no chain M0 ->* Bad):\n");
                append_elided(
                    report,
                    "    ",
                    decoded_set
                        .iter()
                        .map(|state| format_abstract_state(flat, state))
                        .collect::<Vec<_>>()
                        .join("\n")
                        .as_str(),
                );
                report.push_str("  raw z3 answer:\n");
                append_elided(report, "    ", answer);
                (
                    Verdict::Unknown {
                        reason: REPLAY_NO_CHAIN_REASON.to_string(),
                    },
                    DecodedTrace::empty(),
                    Some(false),
                )
            }
        }
    }
}

/// Everything a [`VerificationResult`] carries beyond its verdict, report and
/// statistics. [`Diagnostics::none`] is the shape of an early exit.
struct Diagnostics {
    invariants: Vec<PInvariant>,
    discovered: Vec<String>,
    trace: DecodedTrace,
    confirmed: Option<bool>,
}

impl Diagnostics {
    fn none() -> Self {
        Self {
            invariants: Vec::new(),
            discovered: Vec::new(),
            trace: DecodedTrace::empty(),
            confirmed: None,
        }
    }
}

/// The single construction site of [`VerificationResult`] (which is
/// `#[non_exhaustive]`): every `verify()` exit — Route B, structural,
/// early-Unknown, full pipeline — routes through here, so a new field gets one
/// default rather than four.
fn build_result(
    verdict: Verdict,
    report: String,
    elapsed_ms: u64,
    statistics: VerificationStatistics,
    diagnostics: Diagnostics,
) -> VerificationResult {
    VerificationResult {
        verdict,
        report,
        invariants: diagnostics.invariants,
        discovered_invariants: diagnostics.discovered,
        counterexample_trace: diagnostics.trace.trace,
        counterexample_transitions: diagnostics.trace.transitions,
        counterexample_confirmed: diagnostics.confirmed,
        elapsed_ms,
        statistics,
    }
}

/// Statistics keyed off the flattened net — the shape every post-flattening
/// exit reports.
fn flat_statistics(
    flat: &FlatNet,
    invariants_found: usize,
    structural_result: &str,
) -> VerificationStatistics {
    VerificationStatistics {
        places: flat.place_count,
        transitions: flat.transitions.len(),
        invariants_found,
        structural_result: structural_result.into(),
    }
}

/// Certificate-check report lines (C2) — one canonical wording per outcome,
/// byte-identical across the four implementations.
const CERT_PASSED_LINE: &str = "  Certificate check: PASSED (init, consecution, safety)\n";
const CERT_FAILED_LINE: &str = "  Certificate check: FAILED\n";

/// `  Certificate check: not applicable (<why>)` — emitted on a `Proven`
/// verdict the check did not examine (`structural proof`, `name-coloured
/// encoding`, `disabled`).
fn cert_not_applicable(why: &str) -> String {
    format!("  Certificate check: not applicable ({why})\n")
}

/// Downgrade reason when a VC came back other than `unsat`.
fn certificate_failed_reason(vc: &str, detail: &str) -> String {
    format!(
        "certificate check failed: {vc} was not UNSAT - {detail}; the IC3 certificate could \
         not be independently re-validated against the unstrengthened step relation, so \
         PROVEN is withheld"
    )
}

/// Downgrade reason when the check could not be run to a verdict at all.
fn certificate_inconclusive_reason(reason: &str) -> String {
    format!(
        "certificate check could not run: {reason}; PROVEN is withheld without an \
         independently validated certificate"
    )
}

/// The one replay outcome that withdraws a `Violated` verdict (C2).
const REPLAY_NO_CHAIN_REASON: &str = "counterexample replay found no firing chain to the \
     violation under the abstract semantics, so VIOLATED is withheld";

/// Appends `text` to the report at `indent`, keeping only the first and last
/// [`REPORT_ELISION_HEAD`]/[`REPORT_ELISION_TAIL`] lines. A Spacer refutation
/// proof for a real net runs to megabytes; the report is meant to be read.
fn append_elided(report: &mut String, indent: &str, text: &str) {
    let lines: Vec<&str> = text.lines().collect();
    let keep = REPORT_ELISION_HEAD + REPORT_ELISION_TAIL;
    if lines.len() <= keep {
        for line in lines {
            report.push_str(&format!("{indent}{line}\n"));
        }
        return;
    }
    for line in &lines[..REPORT_ELISION_HEAD] {
        report.push_str(&format!("{indent}{line}\n"));
    }
    report.push_str(&format!(
        "{indent}… {} line(s) elided …\n",
        lines.len() - keep
    ));
    for line in &lines[lines.len() - REPORT_ELISION_TAIL..] {
        report.push_str(&format!("{indent}{line}\n"));
    }
}

/// Lines kept at the head / tail of an elided report block.
const REPORT_ELISION_HEAD: usize = 20;
const REPORT_ELISION_TAIL: usize = 5;

/// Appends the Phase-3 report lines for invariants dropped by the exact
/// re-validation pass ([`p_invariant::validate_invariants_exact`]): one line per
/// drop plus a closing count line. `kind` is "P-invariant" or "P-semiflow".
///
/// The per-drop line is canonical across the four implementations and is
/// diffed byte-for-byte: `  Dropped invariant: <desc> - <reason>` (`Dropped
/// semiflow:` for the semiflow pass), with an ASCII hyphen-minus separator.
/// `validate_invariants_exact` supplies `<desc> - <reason>`.
fn append_invariant_drop_report(report: &mut String, dropped: &[String], kind: &str) {
    if dropped.is_empty() {
        return;
    }
    let noun = if kind == "P-semiflow" { "semiflow" } else { "invariant" };
    for reason in dropped {
        report.push_str(&format!("  Dropped {noun}: {reason}\n"));
    }
    report.push_str(&format!(
        "Dropped {} {kind}(s) that failed exact re-validation (excluded from the encoding)\n",
        dropped.len()
    ));
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

/// Spawns the `z3` binary (`-smt2 -in -T:<secs>` plus `extra_args`), feeding
/// `smt2` on stdin. Returns the raw process output — stdout may well contain
/// `(error …)` lines, which callers interpret — or a spawn/pipe failure
/// description. Shared by the Spacer run and the certificate check
/// ([`crate::certificate_check`]).
pub(crate) fn run_z3_text(
    smt2: &str,
    timeout_ms: u64,
    extra_args: &[&str],
) -> Result<std::process::Output, String> {
    use std::io::Write;
    use std::process::{Command, Stdio};

    // Z3 -T flag uses seconds; round up so sub-second timeouts don't become 0
    let timeout_secs = timeout_ms.div_ceil(1000).max(1);

    let mut child = match Command::new("z3")
        .args(["-smt2", "-in", &format!("-T:{timeout_secs}")])
        .args(extra_args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
    {
        Ok(child) => child,
        Err(e) => return Err(format!("Failed to spawn z3: {e}")),
    };

    if let Some(stdin) = child.stdin.as_mut() {
        if let Err(e) = stdin.write_all(smt2.as_bytes()) {
            return Err(format!("Failed to write to z3 stdin: {e}"));
        }
    }

    match child.wait_with_output() {
        Ok(output) => Ok(output),
        Err(e) => Err(format!("Z3 process error: {e}")),
    }
}

/// Runs Z3 Spacer on the given SMT-LIB2 string.
///
/// Invokes `z3` as a subprocess with Spacer engine.
fn run_z3_spacer(smt2: &str, timeout_ms: u64) -> Z3Result {
    let output = match run_z3_text(smt2, timeout_ms, &["fp.engine=spacer"]) {
        Ok(output) => output,
        Err(reason) => return Z3Result::Unknown { reason },
    };

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stdout = stdout.trim();

    // Scan for the verdict LINE rather than the first bytes of the reply. The
    // script deliberately emits both (get-proof) and (get-model), one of which
    // answers `(error …)` on either branch, and a z3 build is free to print a
    // warning first or route those lines differently — anchoring on
    // `starts_with` turned every such build's flat-path verdict into Unknown.
    match stdout
        .lines()
        .map(str::trim)
        .find(|l| matches!(*l, "sat" | "unsat" | "unknown"))
    {
        // unsat => no inductive invariant excludes the bad state => VIOLATED.
        Some("unsat") => Z3Result::Violated {
            answer: stdout.to_string(),
        },
        // sat => an inductive invariant exists => PROVEN.
        Some("sat") => Z3Result::Proven {
            invariant_formula: extract_invariant_from_output(stdout),
        },
        Some(_) => Z3Result::Unknown {
            reason: "Z3 answered unknown".to_string(),
        },
        None => {
            // No verdict at all: an `(error …)` on either stream is the
            // likeliest cause and the most useful thing to report.
            let stderr = String::from_utf8_lossy(&output.stderr);
            let error = stdout
                .lines()
                .chain(stderr.lines())
                .map(str::trim)
                .find(|l| l.starts_with("(error"));
            Z3Result::Unknown {
                reason: match error {
                    Some(err) => format!("Z3 error: {err}"),
                    None if !stderr.trim().is_empty() => {
                        format!("Z3 error: {}", stderr.trim())
                    }
                    None => format!("Unexpected Z3 output: {stdout}"),
                },
            }
        }
    }
}

/// Extracts the inductive invariant from Z3's `sat` output: every
/// `(define-fun …)` in the `(get-model)` block, joined verbatim. Keeping the
/// auxiliary definitions alongside `Reachable` means the block stays
/// self-contained — the certificate check can paste it into a fresh script
/// with every name resolvable. Returns `None` when no model was printed (the
/// unsat path's `(error "model is not available")` has no define-funs).
fn extract_invariant_from_output(output: &str) -> Option<String> {
    let defs = extract_define_funs(output);
    if defs.is_empty() {
        None
    } else {
        Some(defs.join("\n"))
    }
}

/// Balanced-paren scanner: returns each complete `(define-fun …)`
/// s-expression in `output`, in order. Paren counting skips string literals
/// (`"…"`, with `""` escapes) and quoted symbols (`|…|`) — Spacer model
/// output has neither today, but the scanner does not rely on that. A
/// truncated (unbalanced) definition is dropped rather than half-captured.
fn extract_define_funs(output: &str) -> Vec<String> {
    let mut defs = Vec::new();
    let mut from = 0;
    while let Some(pos) = output[from..].find("(define-fun") {
        let start = from + pos;
        match sexpr_end(output, start) {
            Some(end) => {
                defs.push(output[start..end].to_string());
                from = end;
            }
            None => break,
        }
    }
    defs
}

/// Returns the byte index one past the `)` matching the `(` at `start`.
/// Shared with the proof-state decoder ([`crate::counterexample::decode_state_set`]).
pub(crate) fn sexpr_end(s: &str, start: usize) -> Option<usize> {
    let mut depth = 0usize;
    let mut in_string = false;
    let mut in_symbol = false;
    for (off, c) in s[start..].char_indices() {
        if in_string {
            // SMT-LIB escapes a quote as `""` — reading it as close-then-reopen
            // keeps the paren count right.
            if c == '"' {
                in_string = false;
            }
        } else if in_symbol {
            if c == '|' {
                in_symbol = false;
            }
        } else {
            match c {
                '"' => in_string = true,
                '|' => in_symbol = true,
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        return Some(start + off + c.len_utf8());
                    }
                }
                _ => {}
            }
        }
    }
    None
}

/// True if the `z3` binary this crate shells out to is on `PATH`. Without it
/// every SMT path returns `Unknown`; the test suites use this to skip loudly
/// rather than fail.
pub fn z3_available() -> bool {
    std::process::Command::new("z3")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

/// Replay search bounds (C3): at most this many abstract steps between
/// consecutive decoded proof states (and after the last one) …
const REPLAY_MAX_SEGMENT_STEPS: usize = 3;
/// … and this many search nodes ADMITTED in total before the search gives up
/// (which leaves the verdict alone — exhaustion is not a no-chain finding).
/// "Admitted" is the counting rule the sibling implementations conform to:
/// non-dominated nodes only, anchor included, tripped on `>=` — see
/// [`abstract_replay::replay`].
const REPLAY_NODE_BUDGET: usize = 10_000;

/// Renders an abstract count vector with place names for the report,
/// omitting zero counts (`"p1:2, p2:1"`, or `"(empty)"`).
fn format_abstract_state(flat: &FlatNet, state: &[i64]) -> String {
    let parts: Vec<String> = flat
        .places
        .iter()
        .zip(state)
        .filter(|&(_, &count)| count != 0)
        .map(|(name, count)| format!("{name}:{count}"))
        .collect();
    if parts.is_empty() {
        "(empty)".to_string()
    } else {
        parts.join(", ")
    }
}

/// Converts an abstract count vector into the result's `MarkingState` form.
fn abstract_state_to_marking(flat: &FlatNet, state: &[i64]) -> MarkingState {
    let mut builder = MarkingStateBuilder::new();
    for (name, &count) in flat.places.iter().zip(state) {
        if count > 0 {
            builder = builder.tokens(name, count as usize);
        }
    }
    builder.build()
}

/// Processes the Z3 result into a verdict.
fn process_z3_result(
    result: &Z3Result,
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
        Z3Result::Violated { .. } => {
            report.push_str("Result: property violated (Spacer UNSAT — no inductive invariant)\n");
            // No trace yet: the refutation proof is a SET of ground `Reachable`
            // facts in an order the proof printer chose, so the only ordered
            // trace this crate emits is the one the abstract replay
            // reconstructs by search (see `replay_phase`).
            (Verdict::Violated, DecodedTrace::empty(), Vec::new())
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
    use libpetri_core::action::fork;
    use libpetri_core::input::{all, exactly, one};
    use libpetri_core::output::out_place;
    use libpetri_core::place::Place;
    use libpetri_core::transition::Transition;

    /// CORE-043: verification rejects the same nets compilation rejects.
    #[test]
    #[should_panic(expected = "Transition 't1' declares an output spec but carries passthrough()")]
    fn for_net_rejects_output_declaring_passthrough() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        SmtVerifier::for_net(&net);
    }

    #[test]
    fn verifier_builder_creates_defaults() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(fork())
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
            .action(fork())
            .build();
        let t2 = Transition::builder("t2")
            .input(one(&p2))
            .output(out_place(&p1))
            .action(fork())
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
            .action(fork())
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
            .action(fork())
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let verifier = SmtVerifier::for_net(&net)
            .initial_marking(MarkingStateBuilder::new().tokens("p1", 1).build())
            .property(SmtProperty::DeadlockFree)
            .sink_places(vec!["p2".into()]);

        assert_eq!(verifier.sink_places, vec!["p2"]);
    }

    /// The Phase-3 drop report: one line per dropped invariant plus a count line,
    /// exactly what the invariant phase pushes when exact re-validation rejects a
    /// poisoned invariant. Pure string plumbing — no z3 needed.
    #[test]
    fn invariant_drop_report_lines() {
        let mut report = String::new();
        append_invariant_drop_report(&mut report, &[], "P-invariant");
        assert!(report.is_empty(), "no drops must add no lines");

        // `<desc> - <reason>` as `validate_invariants_exact` renders it: the
        // separator is an ASCII hyphen-minus, never an em dash (the four
        // implementations diff these lines byte-for-byte).
        let dropped = vec![
            "p1 = 1 - y*C is -1 (not 0) at transition 't'".to_string(),
            "3*p2 = 9 - constant 9 does not match exact y*M0 = 3".to_string(),
        ];
        append_invariant_drop_report(&mut report, &dropped, "P-invariant");
        assert!(report.contains("  Dropped invariant: p1 = 1 - y*C is -1 (not 0) at transition 't'\n"));
        assert!(report.contains("  Dropped invariant: 3*p2 = 9 - constant 9 does not match exact y*M0 = 3\n"));
        assert!(
            !report.contains('—'),
            "the canonical drop line uses ' - ', never an em dash:\n{report}"
        );
        assert!(report.contains("Dropped 2 P-invariant(s) that failed exact re-validation"));
    }

    // === Certificate check (independent IC3/PDR proof re-verification) ===

    /// Balanced-paren define-fun extraction: nested parens, multiple
    /// definitions, and robustness against parens inside string literals and
    /// quoted symbols. Pure string plumbing — no z3 needed.
    #[test]
    fn extract_define_funs_nested_and_multiple() {
        let output = "sat\n(\n  (define-fun Error () Bool\n    (exists ((x!1 Int))\n  (! (and (not (>= x!1 2))) :weight 0)))\n  (define-fun Reachable ((x!0 Int) (x!1 Int)) Bool\n    (and (or (not (>= x!0 1)) (not (>= x!1 1)))\n         (not (>= x!1 2))))\n)";
        let defs = extract_define_funs(output);
        assert_eq!(defs.len(), 2);
        assert!(defs[0].starts_with("(define-fun Error"));
        assert!(defs[0].ends_with(":weight 0)))"), "nested close captured: {}", defs[0]);
        assert!(defs[1].starts_with("(define-fun Reachable"));
        assert!(defs[1].ends_with("(not (>= x!1 2))))"), "{}", defs[1]);

        // Parens inside a string literal or a |quoted symbol| must not count.
        let tricky = "(define-fun |odd )name| () String \"un(balanced\") (define-fun f () Int 1)";
        let defs = extract_define_funs(tricky);
        assert_eq!(defs.len(), 2);
        assert_eq!(defs[0], "(define-fun |odd )name| () String \"un(balanced\")");
        assert_eq!(defs[1], "(define-fun f () Int 1)");

        // A truncated definition is dropped, not half-captured.
        assert!(extract_define_funs("(define-fun f ((x Int)) Bool (and (= x 1)").is_empty());
    }

    /// The unsat path prints `(error "model is not available")` after the
    /// verdict line — no define-funs, so extraction yields a clean None.
    #[test]
    fn extract_invariant_none_when_model_unavailable() {
        assert_eq!(
            extract_invariant_from_output("unsat\n(error \"line 42 column 10: model is not available\")"),
            None
        );
        assert_eq!(extract_invariant_from_output("sat"), None);
        let some = extract_invariant_from_output(
            "sat\n(\n  (define-fun Reachable ((x!0 Int)) Bool (>= x!0 0))\n)",
        );
        assert_eq!(
            some.as_deref(),
            Some("(define-fun Reachable ((x!0 Int)) Bool (>= x!0 0))")
        );
    }

    /// Proven-path fixture for the certificate check: the 2-place cycle with
    /// PlaceBound goes through the flat IC3/PDR path (no structural shortcut,
    /// no ν, no colouring).
    fn cert_cycle_net() -> PetriNet {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(fork())
            .build();
        let t2 = Transition::builder("t2")
            .input(one(&p2))
            .output(out_place(&p1))
            .action(fork())
            .build();
        PetriNet::builder("cert_cycle").transitions([t1, t2]).build()
    }

    /// Default-on happy path: a flat-path proof extracts the Spacer model and
    /// the certificate check discharges all three VCs. Incidentally this also
    /// cross-checks the HORN polarity convention: the three VC answers are
    /// ordinary sat/unsat queries with the standard unambiguous reading, and
    /// they only all come back unsat because the `sat`-side model of the CHC
    /// system really is an inductive invariant — independent corroboration of
    /// the empirical sat ⇒ proven mapping in [`run_z3_spacer`].
    #[test]
    fn certificate_check_passes_on_proven_flat_path() {
        if !z3_available() {
            eprintln!("skipping certificate_check_passes_*: z3 binary not on PATH");
            return;
        }
        let net = cert_cycle_net();
        let result = SmtVerifier::for_net(&net)
            .initial_marking(MarkingStateBuilder::new().tokens("p1", 3).build())
            .property(SmtProperty::place_bound("p2", 3))
            .timeout(15_000)
            .verify();
        assert!(result.is_proven(), "{}", result.report);
        assert!(
            result.report.contains("  Certificate check: PASSED (init, consecution, safety)"),
            "proven flat path must carry the PASSED line\n{}",
            result.report
        );
        match &result.verdict {
            Verdict::Proven { inductive_invariant: Some(inv), .. } => assert!(
                inv.contains("(define-fun Reachable"),
                "the extracted certificate is the model's Reachable block: {inv}"
            ),
            other => panic!("expected Proven with an extracted invariant, got {other:?}"),
        }
        assert_eq!(result.discovered_invariants.len(), 1);
    }

    /// End-to-end H1 witness (`Strengthening.lean`,
    /// `consume_all_hypothesis_is_necessary`): `t: all(p0) → p1` with M0 = (2, 0).
    /// Without the linearity guard, the C2 gate accepts y = (1, 1) (the linearized
    /// column is (−1, +1)), the conjoined `p0 + p1 = 2` prunes the genuine successor
    /// (the real firing drains both tokens, y·M drops 2 → 1), and
    /// `PlaceBound(p1, 0)` comes out falsely Proven. With the guard the invariant is
    /// dropped and the verdict must be Violated — p1 genuinely reaches 1.
    #[test]
    fn h1_witness_place_bound_is_violated_not_proven() {
        if !z3_available() {
            eprintln!("skipping h1_witness_place_bound_*: z3 binary not on PATH");
            return;
        }
        let p0 = Place::<i32>::new("p0");
        let p1 = Place::<i32>::new("p1");
        let t = Transition::builder("t")
            .input(all(&p0))
            .output(out_place(&p1))
            .action(fork())
            .build();
        let net = PetriNet::builder("h1_witness").transition(t).build();

        let result = SmtVerifier::for_net(&net)
            .initial_marking(MarkingStateBuilder::new().tokens("p0", 2).build())
            .property(SmtProperty::place_bound("p1", 0))
            .timeout(15_000)
            .verify();
        assert!(
            matches!(result.verdict, Verdict::Violated),
            "PlaceBound(p1, 0) must be VIOLATED on the witness net, got {:?}\n{}",
            result.verdict,
            result.report
        );
        assert!(
            result.report.contains("non-linear consumption")
                && result.report.contains("Strengthening.lean H1"),
            "the report must carry the H1 drop line\n{}",
            result.report
        );
    }

    /// The check also runs (and passes) on the env-injection flat path, where
    /// the step relation includes injection disjuncts and env bounds.
    #[test]
    fn certificate_check_passes_with_env_injection() {
        if !z3_available() {
            eprintln!("skipping certificate_check_passes_with_env_*: z3 binary not on PATH");
            return;
        }
        let in_p = Place::<i32>::new("IN");
        let out = Place::<i32>::new("OUT");
        let t = Transition::builder("T2")
            .input(exactly(2, &in_p))
            .output(out_place(&out))
            .action(fork())
            .build();
        let net = PetriNet::builder("env-mult").transition(t).build();
        let result = SmtVerifier::for_net(&net)
            .environment_places(vec!["IN".into()])
            .environment_mode(EnvironmentAnalysisMode::Bounded { max_tokens: 1 })
            .property(SmtProperty::place_bound("OUT", 0))
            .timeout(15_000)
            .verify();
        assert!(result.is_proven(), "{}", result.report);
        assert!(
            result.report.contains("Certificate check: PASSED"),
            "env-injection proven path must also re-verify\n{}",
            result.report
        );
    }

    /// End-to-end seam: a corrupt certificate must downgrade the flat-path
    /// proof to Unknown with a reason naming the failing VC — never certify,
    /// never panic.
    ///
    /// The net is the env-injection one deliberately: it has no P-invariants
    /// (the injector column forces `y = 0` on IN, which then forces `y = 0` on
    /// OUT), so `Reachable := true` really is the whole candidate. On a
    /// conserving net the validated invariant rides along in `R'` and rescues
    /// the safety VC by itself — a pass, correctly.
    #[test]
    fn corrupt_certificate_downgrades_proven_to_unknown() {
        if !z3_available() {
            eprintln!("skipping corrupt_certificate_*: z3 binary not on PATH");
            return;
        }
        let in_p = Place::<i32>::new("IN");
        let out = Place::<i32>::new("OUT");
        let t = Transition::builder("T2")
            .input(exactly(2, &in_p))
            .output(out_place(&out))
            .action(fork())
            .build();
        let net = PetriNet::builder("env-mult").transition(t).build();
        let result = SmtVerifier::for_net(&net)
            .environment_places(vec!["IN".into()])
            .environment_mode(EnvironmentAnalysisMode::Bounded { max_tokens: 1 })
            .property(SmtProperty::place_bound("OUT", 0))
            .certificate_override("(define-fun Reachable ((x!0 Int) (x!1 Int)) Bool true)")
            .timeout(15_000)
            .verify();
        match &result.verdict {
            Verdict::Unknown { reason } => {
                assert!(
                    reason.contains("certificate check failed: safety (VC3) was not UNSAT")
                        && reason.contains("PROVEN is withheld"),
                    "reason must name the failing VC (C2): {reason}"
                );
            }
            other => panic!("expected Unknown after corrupt certificate, got {other:?}\n{}", result.report),
        }
        assert!(
            result.report.contains("  Certificate check: FAILED"),
            "{}",
            result.report
        );
        assert!(!result.report.contains("Certificate check: PASSED"), "{}", result.report);
    }

    /// Opt-out: `.certificate_check(false)` skips the second z3 run — no
    /// PASSED line, verdict unchanged.
    #[test]
    fn certificate_check_opt_out_skips_the_check() {
        if !z3_available() {
            eprintln!("skipping certificate_check_opt_out_*: z3 binary not on PATH");
            return;
        }
        let net = cert_cycle_net();
        let result = SmtVerifier::for_net(&net)
            .initial_marking(MarkingStateBuilder::new().tokens("p1", 3).build())
            .property(SmtProperty::place_bound("p2", 3))
            .certificate_check(false)
            .timeout(15_000)
            .verify();
        assert!(result.is_proven(), "{}", result.report);
        assert!(
            result
                .report
                .contains("  Certificate check: not applicable (disabled)"),
            "opt-out must say why no check ran\n{}",
            result.report
        );
        // Even a corrupt certificate is ignored when the check is off.
        let result = SmtVerifier::for_net(&net)
            .initial_marking(MarkingStateBuilder::new().tokens("p1", 3).build())
            .property(SmtProperty::place_bound("p2", 3))
            .certificate_check(false)
            .certificate_override("(define-fun Reachable ((x!0 Int) (x!1 Int)) Bool true)")
            .timeout(15_000)
            .verify();
        assert!(result.is_proven(), "{}", result.report);
    }

    /// End-to-end through verify(): on a well-behaved net every computed invariant
    /// re-verifies exactly, so Phase 3 reports them and drops nothing. Runs without
    /// z3 — the phase-3 report is built before the solver is spawned, and the
    /// assertions hold whether the verdict is Proven or Unknown(no z3).
    #[test]
    fn invariant_phase_validates_without_dropping_on_sound_net() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(fork())
            .build();
        let t2 = Transition::builder("t2")
            .input(one(&p2))
            .output(out_place(&p1))
            .action(fork())
            .build();
        let net = PetriNet::builder("cycle").transitions([t1, t2]).build();

        let result = SmtVerifier::for_net(&net)
            .initial_marking(MarkingStateBuilder::new().tokens("p1", 3).build())
            .property(SmtProperty::place_bound("p2", 3))
            .verify();

        assert!(
            result.report.contains("Found 1 P-invariant(s)"),
            "the validated invariant must reach the report\n{}",
            result.report
        );
        assert_eq!(result.invariants.len(), 1);
        assert_eq!(result.invariants[0].constant, 3);
        assert!(
            !result.report.contains("Dropped invariant:"),
            "a sound net must not lose invariants to validation\n{}",
            result.report
        );
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
            .action(fork())
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
                .action(fork())
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

        let t_fork = Transition::builder("fork")
            .input(one(&source))
            .input(one(&budget)) // minting a name costs one budget token
            .output(and(vec![
                out_place(&a),
                out_place(&b),
                out_place(&pending), // mark a live correlation group
            ]))
            .action(fork())
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
            .action(fork())
            .build();

        PetriNet::builder("nu_scatter_gather_verify")
            .transitions([t_fork, join])
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

    // === NU-053: Route A coloured quiescence (EXTENDED + deadlock encoding) ===

    /// A single-turn co-mint→join net: `fork` consumes `source` + `budget` and
    /// co-mints one fresh name into join inputs `a` and `b`; `join` correlates them
    /// into `merged` and refunds `budget`. The only quiescent marking holds just the
    /// sinks {merged, budget}, so it is deadlock-free.
    fn nu053_no_stall_net() -> PetriNet {
        use libpetri_core::match_spec::MatchSpec;
        use libpetri_core::name::NameId;
        use libpetri_core::output::and;

        let source = Place::<()>::new("source");
        let budget = Place::<()>::new("budget");
        let a = Place::<String>::new("a");
        let b = Place::<String>::new("b");
        let merged = Place::<String>::new("merged");

        let t_fork = Transition::builder("fork")
            .input(one(&source))
            .input(one(&budget))
            .output(and(vec![out_place(&a), out_place(&b)]))
            .action(fork())
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
            .output(and(vec![out_place(&merged), out_place(&budget)]))
            .action(fork())
            .build();
        PetriNet::builder("nu053_no_stall")
            .transitions([t_fork, join])
            .build()
    }

    /// The no-stall net plus an EXTENDED drain that steals `a` into a dead-letter,
    /// stranding `b`: an unprioritised schedule can reach a quiescent marking where
    /// the non-sink `b` still holds a token, so it is NOT deadlock-free.
    fn nu053_steal_net() -> PetriNet {
        use libpetri_core::match_spec::MatchSpec;
        use libpetri_core::name::NameId;
        use libpetri_core::output::and;

        let source = Place::<()>::new("source");
        let budget = Place::<()>::new("budget");
        let a = Place::<String>::new("a");
        let b = Place::<String>::new("b");
        let merged = Place::<String>::new("merged");
        let deadletter = Place::<String>::new("deadletter");

        let t_fork = Transition::builder("fork")
            .input(one(&source))
            .input(one(&budget))
            .output(and(vec![out_place(&a), out_place(&b)]))
            .action(fork())
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
            .output(and(vec![out_place(&merged), out_place(&budget)]))
            .action(fork())
            .build();
        let drain = Transition::builder("drain")
            .input(one(&a))
            .output(out_place(&deadletter))
            .action(fork())
            .build();
        PetriNet::builder("nu053_steal")
            .transitions([t_fork, join, drain])
            .build()
    }

    fn nu053_seed() -> MarkingState {
        MarkingStateBuilder::new()
            .tokens("source", 1)
            .tokens("budget", 1)
            .build()
    }

    #[test]
    fn nu053_route_a_proves_deadlock_free_when_route_b_truncates() {
        if !z3_available() {
            eprintln!("skipping nu053_route_a_proves_*: z3 binary not on PATH");
            return;
        }
        // nu_max_classes = 1 forces Route B to truncate, so the bounded quiescence
        // proof defers to the Route A coloured IC3/PDR encoder ([NU-053]).
        let net = nu053_no_stall_net();
        let result = SmtVerifier::for_net(&net)
            .initial_marking(nu053_seed())
            .property(SmtProperty::DeadlockFree)
            .sink_places(["merged".to_string(), "budget".to_string()])
            .budget_place("budget")
            .nu_max_classes(1)
            .timeout(15_000)
            .verify();
        assert!(
            result.report.contains("Route A"),
            "expected the proof to defer to Route A\n{}",
            result.report
        );
        assert!(
            result.is_proven(),
            "Route A must prove the co-mint→join net deadlock-free\n{}",
            result.report
        );
    }

    #[test]
    fn nu053_route_a_detects_stranding_deadlock() {
        if !z3_available() {
            eprintln!("skipping nu053_route_a_detects_*: z3 binary not on PATH");
            return;
        }
        // The EXTENDED drain can steal `a` and strand `b` under an unprioritised
        // schedule — a genuine reachable deadlock the coloured encoding must catch.
        // Sinks are {merged, budget} only: under [VER-002] a quiescent marking is
        // excused as soon as ANY declared sink holds a token, so declaring
        // `deadletter` a sink would excuse the stranded-`b` marking (which also
        // holds the dead-lettered token) and hide the stall.
        let net = nu053_steal_net();
        let result = SmtVerifier::for_net(&net)
            .initial_marking(nu053_seed())
            .property(SmtProperty::DeadlockFree)
            .sink_places(["merged".to_string(), "budget".to_string()])
            .budget_place("budget")
            .fragment_mode(FragmentMode::Extended)
            .nu_max_classes(1)
            .timeout(15_000)
            .verify();
        assert!(
            result.is_violated(),
            "Route A must detect the drain-steal stranding as a deadlock\n{}",
            result.report
        );
    }

    #[test]
    fn nu053_route_a_agrees_with_route_b_on_no_stall() {
        if !z3_available() {
            eprintln!("skipping nu053_route_a_agrees_*: z3 binary not on PATH");
            return;
        }
        // Differential: Route B (exact SCG, default class bound) and Route A (forced
        // via a tiny class bound) must agree that the net is deadlock-free.
        let net = nu053_no_stall_net();
        let build = |max_classes: usize| {
            SmtVerifier::for_net(&net)
                .initial_marking(nu053_seed())
                .property(SmtProperty::DeadlockFree)
                .sink_places(["merged".to_string(), "budget".to_string()])
                .budget_place("budget")
                .nu_max_classes(max_classes)
                .timeout(15_000)
                .verify()
        };
        let route_b = build(100_000);
        let route_a = build(1);
        assert!(route_b.is_proven(), "Route B must prove no-stall\n{}", route_b.report);
        assert!(route_a.is_proven(), "Route A must prove no-stall\n{}", route_a.report);
    }

    #[test]
    fn nu_structurally_bounded_without_declared_budget_decided_by_route_b() {
        // NU-050 Route B: without a DECLARED budget place, Route A returns Unknown.
        // Route B's name-partition quotient discovers the structural bound (the
        // budget token caps live groups) and proves BranchPlaceBound(budget, 2)
        // exactly — the beyond-bounded win. Pure SCG, so no Z3 binary is needed.
        let net = nu_scatter_gather_net();
        let result = SmtVerifier::for_net(&net)
            .initial_marking(nu_initial_marking(2))
            .property(SmtProperty::branch_place_bound("budget", 2))
            .verify();
        assert!(
            result.is_proven(),
            "Route B decides a structurally-bounded ν-net without a declared budget\n{}",
            result.report
        );
        assert!(
            result.report.contains("Route B"),
            "expected the Route B note\n{}",
            result.report
        );
    }

    #[test]
    fn nu_joined_or_dead_lettered_proven_by_route_b() {
        // NU-050 Route B: quiescence on a ν-net is now decided exactly by the
        // name-aware SCG (the SMT path deferred it to Unknown). Same-mint siblings
        // always join, so no quiescent state strands `pending` → PROVEN. No Z3.
        let net = nu_scatter_gather_net();
        let result = SmtVerifier::for_net(&net)
            .initial_marking(nu_initial_marking(2))
            .property(SmtProperty::joined_or_dead_lettered("pending"))
            .verify();
        assert!(
            result.is_proven(),
            "every same-mint group joins → no stranded pending → Proven\n{}",
            result.report
        );
        assert!(
            result.report.contains("Route B"),
            "expected the Route B note\n{}",
            result.report
        );
    }

    #[test]
    fn nu_deadlock_free_violated_by_route_b() {
        // NU-050 Route B: DeadlockFree is now exact. The scatter-gather quiesces
        // when `source` is exhausted (budget returned, no group in flight) — a
        // genuine deadlock with no declared sinks → VIOLATED (was Unknown). No Z3.
        let net = nu_scatter_gather_net();
        let result = SmtVerifier::for_net(&net)
            .initial_marking(nu_initial_marking(2))
            .property(SmtProperty::DeadlockFree)
            .verify();
        assert!(
            result.is_violated(),
            "the net quiesces when source is exhausted → DeadlockFree violated\n{}",
            result.report
        );
        assert!(
            result.report.contains("Route B"),
            "expected the Route B note\n{}",
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
            .action(fork())
            .build();
        let fin = Transition::builder("fin")
            .input(one(&pending))
            .output(out_place(&done))
            .action(fork())
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
            .action(fork())
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
            .action(fork())
            .build();
        let fork_b = Transition::builder("forkB")
            .input(one(&source_b))
            .input(one(&budget))
            .output(out_place(&b))
            .action(fork())
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
            .action(fork())
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

    // === NU-051: EXTENDED coloured-consumer fragment (drain/relay + carrier co-mint) ===
    // The name-aware SCG decides DeadlockFree exactly, so these route through
    // Route B without ever touching the z3 binary.

    /// A `fork` co-mints one fresh name into `branchA`, `branchB`, and the
    /// declared carrier `stray`; the `join` correlates the branches into `merged`
    /// (a sink), leaving `stray`; the optional `drain` dead-letters the leftover
    /// `stray` into `deadletter` (a sink). Without the drain, `stray` is stranded
    /// at quiescence — a genuine stall.
    fn comint_carrier_drain_net(with_drain: bool) -> PetriNet {
        use libpetri_core::match_spec::MatchSpec;
        use libpetri_core::name::NameId;
        use libpetri_core::output::and;

        let source = Place::<()>::new("source");
        let a = Place::<String>::new("branchA");
        let b = Place::<String>::new("branchB");
        let stray = Place::<String>::new("stray");
        let merged = Place::<String>::new("merged");
        let dl = Place::<()>::new("deadletter");

        let t_fork = Transition::builder("fork")
            .input(one(&source))
            .output(and(vec![out_place(&a), out_place(&b), out_place(&stray)]))
            .action(fork())
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
            .action(fork())
            .build();

        let mut builder = PetriNet::builder("comint_carrier_drain").transitions([t_fork, join]);
        if with_drain {
            let drain = Transition::builder("drain")
                .input(one(&stray))
                .output(out_place(&dl))
                .action(fork())
                .build();
            builder = builder.transition(drain);
        }
        builder.build()
    }

    #[test]
    fn extended_deadlock_free_proven_with_drain_via_route_b() {
        // With the drain, the only quiescent marking is {merged, deadletter}, both
        // declared sinks → no stall → PROVEN. Decided by Route B EXTENDED (no z3).
        let net = comint_carrier_drain_net(true);
        let result = SmtVerifier::for_net(&net)
            .initial_marking(MarkingStateBuilder::new().tokens("source", 1).build())
            .property(SmtProperty::DeadlockFree)
            .sink_places(vec!["merged".into(), "deadletter".into()])
            .fragment_mode(FragmentMode::Extended)
            .carrier_place("stray")
            .verify();
        assert!(
            result.is_proven(),
            "the drain dead-letters the leftover carrier token → no stall → Proven\n{}",
            result.report
        );
        assert!(
            result.report.contains("Route B"),
            "the verdict must come from Route B (name-partition quotient), not the SMT path\n{}",
            result.report
        );
    }

    #[test]
    fn extended_deadlock_free_violated_without_drain_via_route_b() {
        // Remove the drain: after the join, `stray` is stranded at quiescence
        // ({merged, stray}, and `stray` is not a sink) → a genuine stall → VIOLATED.
        let net = comint_carrier_drain_net(false);
        let result = SmtVerifier::for_net(&net)
            .initial_marking(MarkingStateBuilder::new().tokens("source", 1).build())
            .property(SmtProperty::DeadlockFree)
            .sink_places(vec!["merged".into(), "deadletter".into()])
            .fragment_mode(FragmentMode::Extended)
            .carrier_place("stray")
            .verify();
        assert!(
            result.is_violated(),
            "without the drain the carrier token strands at quiescence → Violated\n{}",
            result.report
        );
        assert!(
            result.report.contains("Route B"),
            "the verdict must come from Route B\n{}",
            result.report
        );
    }

    #[test]
    fn extended_unknown_on_unknown_carrier_place() {
        // A mistyped carrier name must surface as Unknown naming the place — never
        // a silent fall-back to a confident (possibly false) verdict.
        let net = comint_carrier_drain_net(true);
        let result = SmtVerifier::for_net(&net)
            .initial_marking(MarkingStateBuilder::new().tokens("source", 1).build())
            .property(SmtProperty::DeadlockFree)
            .sink_places(vec!["merged".into(), "deadletter".into()])
            .fragment_mode(FragmentMode::Extended)
            .carrier_place("nonExistent")
            .verify();
        match &result.verdict {
            Verdict::Unknown { reason } => assert!(
                reason.contains("nonExistent"),
                "reason must name the offending carrier: {reason}\n{}",
                result.report
            ),
            other => panic!("expected Unknown on unknown carrier, got {other:?}\n{}", result.report),
        }
    }

    // === C3: abstract counterexample replay ===

    /// Default-on happy path: a genuinely violated flat-path fixture decodes
    /// ground `Reachable` states from the z3 refutation proof and the
    /// abstract replay confirms the chain — verdict stays Violated,
    /// `counterexample_confirmed` set, trace re-emitted in replay order
    /// (M0 first, violating state last).
    #[test]
    fn violated_counterexample_confirmed_by_replay() {
        if !z3_available() {
            eprintln!("skipping violated_counterexample_confirmed_*: z3 binary not on PATH");
            return;
        }
        let net = cert_cycle_net();
        let result = SmtVerifier::for_net(&net)
            .initial_marking(MarkingStateBuilder::new().tokens("p1", 3).build())
            .property(SmtProperty::place_bound("p2", 2))
            .timeout(15_000)
            .verify();
        assert!(result.is_violated(), "{}", result.report);
        assert_eq!(
            result.counterexample_confirmed,
            Some(true),
            "the genuine CEX must replay\n{}",
            result.report
        );
        assert!(
            result.report.contains("Counterexample replay: CONFIRMED"),
            "{}",
            result.report
        );
        let trace = &result.counterexample_trace;
        assert!(!trace.is_empty(), "replay must re-emit the trace");
        assert_eq!(trace[0].count("p1"), 3, "trace starts at M0\n{}", result.report);
        assert!(
            trace.last().unwrap().count("p2") > 2,
            "trace ends in a violating state\n{}",
            result.report
        );
        assert_eq!(
            result.counterexample_transitions.len(),
            trace.len() - 1,
            "one step label between consecutive states"
        );
    }

    /// C4: an exhausted SEGMENT budget (test seam: M0 alone, Bad six steps
    /// away — twice the budget) is an absence of evidence. The Violated
    /// verdict stands, unconfirmed, with the exhaustion named in the report.
    #[test]
    fn segment_budget_exhaustion_keeps_violated_unconfirmed() {
        if !z3_available() {
            eprintln!("skipping segment_budget_exhaustion_*: z3 binary not on PATH");
            return;
        }
        let net = cert_cycle_net();
        let result = SmtVerifier::for_net(&net)
            .initial_marking(MarkingStateBuilder::new().tokens("p1", 6).build())
            .property(SmtProperty::place_bound("p2", 5))
            // flat place order is sorted: [p1, p2] — this is M0 and nothing else.
            .replay_state_set_override(vec![vec![6, 0]])
            .timeout(15_000)
            .verify();
        assert!(result.is_violated(), "{}", result.report);
        assert_eq!(result.counterexample_confirmed, Some(false));
        assert!(
            result.report.contains("search budget exhausted (segment budget"),
            "the report must name the exhausted budget\n{}",
            result.report
        );
    }

    /// V4: an exhausted NODE budget likewise leaves the verdict alone. The
    /// seam shrinks the budget to 1, so the search dies at the anchor node.
    #[test]
    fn node_budget_exhaustion_keeps_violated_unconfirmed() {
        if !z3_available() {
            eprintln!("skipping node_budget_exhaustion_*: z3 binary not on PATH");
            return;
        }
        let net = cert_cycle_net();
        let result = SmtVerifier::for_net(&net)
            .initial_marking(MarkingStateBuilder::new().tokens("p1", 3).build())
            .property(SmtProperty::place_bound("p2", 2))
            .replay_node_budget(1)
            .timeout(15_000)
            .verify();
        assert!(result.is_violated(), "{}", result.report);
        assert_eq!(result.counterexample_confirmed, Some(false));
        assert!(
            result
                .report
                .contains("search budget exhausted (search node budget of 1 exhausted)"),
            "the report must name the exhausted budget\n{}",
            result.report
        );
    }

    /// C4: a decoded set without M0 cannot anchor a search, so no search runs
    /// — that says nothing about the net, and the verdict must survive it.
    #[test]
    fn state_set_missing_initial_marking_keeps_violated() {
        if !z3_available() {
            eprintln!("skipping state_set_missing_initial_*: z3 binary not on PATH");
            return;
        }
        let net = cert_cycle_net();
        let result = SmtVerifier::for_net(&net)
            .initial_marking(MarkingStateBuilder::new().tokens("p1", 3).build())
            .property(SmtProperty::place_bound("p2", 2))
            .replay_state_set_override(vec![vec![2, 1], vec![0, 3]])
            .timeout(15_000)
            .verify();
        assert!(result.is_violated(), "{}", result.report);
        assert_eq!(result.counterexample_confirmed, Some(false));
        assert!(
            result
                .report
                .contains("the decoded state set does not contain M0"),
            "{}",
            result.report
        );
    }

    /// Decode-nothing is NOT a downgrade (mass-downgrading real verdicts
    /// would regress the suite): Violated stands, unconfirmed, with a note.
    #[test]
    fn empty_decode_keeps_violated_unconfirmed() {
        if !z3_available() {
            eprintln!("skipping empty_decode_keeps_*: z3 binary not on PATH");
            return;
        }
        let net = cert_cycle_net();
        let result = SmtVerifier::for_net(&net)
            .initial_marking(MarkingStateBuilder::new().tokens("p1", 3).build())
            .property(SmtProperty::place_bound("p2", 2))
            .replay_state_set_override(Vec::new())
            .timeout(15_000)
            .verify();
        assert!(result.is_violated(), "{}", result.report);
        assert_eq!(result.counterexample_confirmed, Some(false));
        assert!(
            result
                .report
                .contains("no ground Reachable states in the z3 proof"),
            "{}",
            result.report
        );
    }

    /// Opt-out: `.counterexample_replay(false)` skips proof emission and
    /// replay entirely — verdict untouched, no replay lines.
    #[test]
    fn counterexample_replay_opt_out() {
        if !z3_available() {
            eprintln!("skipping counterexample_replay_opt_out_*: z3 binary not on PATH");
            return;
        }
        let net = cert_cycle_net();
        let result = SmtVerifier::for_net(&net)
            .initial_marking(MarkingStateBuilder::new().tokens("p1", 3).build())
            .property(SmtProperty::place_bound("p2", 2))
            .counterexample_replay(false)
            .timeout(15_000)
            .verify();
        assert!(result.is_violated(), "{}", result.report);
        assert_eq!(
            result.counterexample_confirmed, None,
            "the replay did not apply (C1)"
        );
        assert!(
            !result.report.contains("Counterexample replay"),
            "opt-out must not run or mention the replay\n{}",
            result.report
        );
    }

    /// Replay across an env-injection step (VER-006): the confirmed chain
    /// includes an `inject(...)` label.
    #[test]
    fn replay_confirms_env_injection_counterexample() {
        if !z3_available() {
            eprintln!("skipping replay_confirms_env_*: z3 binary not on PATH");
            return;
        }
        let result = SmtVerifier::for_net(&env_source_net())
            .environment_places(vec!["IN".into()])
            .environment_mode(EnvironmentAnalysisMode::AlwaysAvailable)
            .property(SmtProperty::place_bound("OUT", 0))
            .timeout(15_000)
            .verify();
        assert!(result.is_violated(), "{}", result.report);
        assert_eq!(
            result.counterexample_confirmed,
            Some(true),
            "the injection CEX must replay\n{}",
            result.report
        );
        assert!(
            result
                .counterexample_transitions
                .iter()
                .any(|label| label == "inject(IN)"),
            "the chain must step through env injection: {:?}\n{}",
            result.counterexample_transitions,
            result.report
        );
    }

    /// The report must stay readable: a Spacer refutation proof runs to
    /// megabytes, so a raw block is kept head-and-tail with an elision marker.
    #[test]
    fn long_report_blocks_are_elided() {
        let mut report = String::new();
        let text: String = (0..200).map(|i| format!("line{i}\n")).collect();
        append_elided(&mut report, "    ", &text);
        assert!(report.contains("    line0\n") && report.contains("    line19\n"));
        assert!(!report.contains("    line20\n"), "{report}");
        assert!(report.contains("    … 175 line(s) elided …\n"), "{report}");
        assert!(report.contains("    line199\n"), "{report}");
        assert_eq!(report.lines().count(), 26);

        // Short blocks pass through untouched.
        let mut short = String::new();
        append_elided(&mut short, "  ", "a\nb\n");
        assert_eq!(short, "  a\n  b\n");
    }

    /// A coloured/ν `Proven` gets no certificate check (different variable
    /// layout) — the report says so rather than staying silent (C2).
    #[test]
    fn coloured_path_reports_certificate_not_applicable() {
        if !z3_available() {
            eprintln!("skipping coloured_path_reports_*: z3 binary not on PATH");
            return;
        }
        let net = nu_scatter_gather_net();
        let result = SmtVerifier::for_net(&net)
            .initial_marking(nu_initial_marking(2))
            .property(SmtProperty::branch_place_bound("budget", 2))
            .budget_place("budget")
            .timeout(15_000)
            .verify();
        assert!(result.is_proven(), "{}", result.report);
        assert!(
            result
                .report
                .contains("  Certificate check: not applicable (name-coloured encoding)"),
            "{}",
            result.report
        );
        assert_eq!(result.counterexample_confirmed, None);
    }

    /// A structural proof returns before any solver runs; it must say so too.
    #[test]
    fn structural_proof_reports_certificate_not_applicable() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(fork())
            .build();
        let t2 = Transition::builder("t2")
            .input(one(&p2))
            .output(out_place(&p1))
            .action(fork())
            .build();
        let net = PetriNet::builder("cycle").transitions([t1, t2]).build();
        let result = SmtVerifier::for_net(&net)
            .initial_marking(MarkingStateBuilder::new().tokens("p1", 1).build())
            .property(SmtProperty::DeadlockFree)
            .verify();
        assert!(result.is_proven(), "{}", result.report);
        assert!(
            result
                .report
                .contains("  Certificate check: not applicable (structural proof)"),
            "{}",
            result.report
        );
        assert_eq!(result.counterexample_confirmed, None);
    }
}
