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
#[derive(Debug, Clone)]
pub struct VerificationStatistics {
    pub places: usize,
    pub transitions: usize,
    pub invariants_found: usize,
    pub structural_result: String,
}

/// Result of an SMT verification query.
#[derive(Debug, Clone)]
pub struct VerificationResult {
    pub verdict: Verdict,
    pub report: String,
    pub invariants: Vec<PInvariant>,
    pub discovered_invariants: Vec<String>,
    pub counterexample_trace: Vec<MarkingState>,
    pub counterexample_transitions: Vec<String>,
    /// Whether a `Violated` verdict's counterexample was confirmed by the
    /// abstract replay (C3, [`crate::abstract_replay`]): the state set decoded
    /// from the z3 refutation proof chained from the initial marking to a
    /// state satisfying the property violation under the abstract (untimed,
    /// value-blind) semantics. `false` on every non-violated verdict, when
    /// replay is disabled or not applicable (name-coloured / Route B /
    /// structural paths), and when the proof yielded no decodable states
    /// (common — not a downgrade; see the report note).
    pub counterexample_confirmed: bool,
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
