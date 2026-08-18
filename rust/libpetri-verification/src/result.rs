use crate::marking_state::MarkingState;
use crate::p_invariant::PInvariant;

/// Verdict of a verification query.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Verdict {
    /// Property holds for all reachable states.
    Proven {
        /// The method that proved the property (e.g., "IC3/PDR" or "structural").
        method: String,
        /// Inductive invariant discovered by the solver, if available.
        inductive_invariant: Option<String>,
    },
    /// Property is violated with a counterexample trace.
    Violated,
    /// Solver could not determine the result.
    Unknown {
        /// Reason for the unknown result.
        reason: String,
    },
}

impl Verdict {
    pub fn is_proven(&self) -> bool {
        matches!(self, Self::Proven { .. })
    }

    pub fn is_violated(&self) -> bool {
        matches!(self, Self::Violated)
    }
}

/// Statistics from the verification run.
///
/// `#[non_exhaustive]`: the verifier gains diagnostics over time, so callers
/// construct this only through [`SmtVerifier::verify`](crate::smt_verifier::SmtVerifier::verify).
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct VerificationStatistics {
    pub places: usize,
    pub transitions: usize,
    pub invariants_found: usize,
    pub structural_result: String,
}

/// Result of an SMT verification query.
///
/// `#[non_exhaustive]`: new diagnostic fields land here as the independent
/// validation layers grow, so callers read fields rather than destructure.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct VerificationResult {
    pub verdict: Verdict,
    pub report: String,
    pub invariants: Vec<PInvariant>,
    pub discovered_invariants: Vec<String>,
    pub counterexample_trace: Vec<MarkingState>,
    pub counterexample_transitions: Vec<String>,
    /// Outcome of the abstract counterexample replay ([`crate::abstract_replay`]),
    /// as a TRI-STATE. **This is the canonical definition**: the PyO3 getter,
    /// the Python docstring and the sibling implementations restate it and
    /// point back here.
    ///
    /// * `None` — the replay did not apply: replay disabled, a non-violated
    ///   verdict, or a verdict from the name-coloured / Route B / structural
    ///   path;
    /// * `Some(false)` — the replay applied and did NOT confirm the
    ///   counterexample. Two shapes, both reported the same way:
    ///   * it could not conclude (nothing decodable in the proof, M₀ absent
    ///     from the decoded set, or a budget exhausted) — the `Violated`
    ///     verdict stands unconfirmed, see the report note;
    ///   * it refuted the trace outright
    ///     ([`ReplayOutcome::NoChain`](crate::abstract_replay::ReplayOutcome::NoChain):
    ///     no firing chain reaches the violation) — the verdict is downgraded
    ///     to `Unknown`. A refutation is strictly more informative than "did
    ///     not apply", so it reports `Some(false)`, never `None`;
    /// * `Some(true)` — the replay chained M₀ to a violating state.
    pub counterexample_confirmed: Option<bool>,
    pub elapsed_ms: u64,
    pub statistics: VerificationStatistics,
}

impl VerificationResult {
    pub fn is_proven(&self) -> bool {
        self.verdict.is_proven()
    }

    pub fn is_violated(&self) -> bool {
        self.verdict.is_violated()
    }
}
